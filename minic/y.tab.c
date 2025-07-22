

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum
{
    NString = 32,
    NGlo     = 256,
    NVar     = 512,
    NStr     = 256,
};

enum
{
    NIL,
    INT,
    FLOAT,
    LNG,
    PTR,
    FUN,
};

#define IDIR(x) (((x) << 3) + PTR)
#define FUNC(x) (((x) << 3) + FUN)
#define DREF(x) ((x) >> 3)
#define KIND(x) ((x) & 7)

#define SIZE(x)                                 \
    (x == NIL ? (die("void has no size"), 0) :     \
     x == INT ? 4 :                             \
     x == FLOAT ? 4 : 8 )

typedef struct Node Node;
typedef struct Symb Symb;
typedef struct Stmt Stmt;

struct Symb
{
    enum
    {
        Con,
        Tmp,
        Var,
        Glo,
    } t;
    
    union 
    {
        int n;
        char v[NString];
    } u;

    unsigned long ctyp;
};

struct Node
{
    char op;
    union
    {
        int n;
        char v[NString];
        Symb s;
    } u;
    
    Node *l, *r;
};

struct Stmt
{
    enum
    {
        If,
        While,
        Seq,
        Expr,
        Break,
        Ret,
    } t;
    
    void *p1, *p2, *p3;
};

int yylex(void), yyerror(char *);
Symb expr(Node *), lval(Node *);
void branch(Node *, int, int);

FILE *of;
int line;
int lbl, tmp, nglo;
char *ini[NGlo];

struct
{
    char v[NString];
    unsigned ctyp;
    int glo;
} varh[NVar];

void die(char *s)
{
    fprintf(stderr, "error:%d: %s\n", line, s);
    exit(1);
}

void* alloc(size_t s)
{
    void *p;

    p = malloc(s);
    if (!p)
        die("out of memory");
    return p;
}

unsigned hash(char *s)
{
    unsigned h;

    h = 42;
    while (*s)
        h += 11 * h + *s++;
    return h % NVar;
}

void varclr()
{
    unsigned h;

    for (h=0; h<NVar; h++)
        if (!varh[h].glo)
            varh[h].v[0] = 0;
}

void varadd(char *v, int glo, unsigned ctyp)
{
    unsigned h0, h;

    h0  = hash(v);
    h   = h0;
    
    do 
    {
        if (varh[h].v[0] == 0)
        {
            strcpy(varh[h].v, v);
            varh[h].glo = glo;
            varh[h].ctyp = ctyp;
            return;
        }

        if (strcmp(varh[h].v, v) == 0)
            die("double definition");
        
        h = (h+1) % NVar;
    } while(h != h0);
    
    die("too many variables");
}

Symb* varget(char *v)
{
    static Symb s;
    unsigned h0, h;

    h0     = hash(v);
    h     = h0;
    
    do 
    {
        if (strcmp(varh[h].v, v) == 0)
        {
            if (!varh[h].glo)
            {
                s.t = Var;
                strcpy(s.u.v, v);
            } 
            else
            {
                s.t = Glo;
                s.u.n = varh[h].glo;
            }
            
            s.ctyp = varh[h].ctyp;
            return &s;
        }
        
        h = (h+1) % NVar;
    } while (h != h0 && varh[h].v[0] != 0);
    
    return 0;
}

char irtyp(unsigned ctyp)
{
    return SIZE(ctyp) == 8 ? 'l' : 'w';
}

void psymb(Symb s)
{
    switch (s.t) 
    {
    case Tmp:
        
        fprintf(of, "%%t%d", s.u.n);
        break;

    case Var:
        
        fprintf(of, "%%%s", s.u.v);
        break;

    case Glo:
        
        fprintf(of, "$glo%d", s.u.n);
        break;

    case Con:
        
        fprintf(of, "%d", s.u.n);
        break;
    }
}

void sext(Symb *s)
{
    fprintf(of, "\t%%t%d =l extsw ", tmp);
    psymb(*s);
    fprintf(of, "\n");
    s->t = Tmp;
    s->ctyp = LNG;
    s->u.n = tmp++;
}

unsigned prom(int op, Symb *l, Symb *r)
{
    Symb *t;
    int sz;

    if (l->ctyp == r->ctyp && KIND(l->ctyp) != PTR)
        return l->ctyp;

    if (l->ctyp == LNG && r->ctyp == INT)
    {
        sext(r);
        return LNG;
    }
    
    if (l->ctyp == INT && r->ctyp == LNG)
    {
        sext(l);
        return LNG;
    }

    if (l->ctyp == FLOAT && r->ctyp == INT)
        return FLOAT;

    if (l->ctyp == INT && r->ctyp == FLOAT)
        return FLOAT;

    if (l->ctyp == FLOAT && r->ctyp == LNG)
        return FLOAT;

    if (l->ctyp == LNG && r->ctyp == FLOAT)
        return FLOAT;

    if (op == '+')
    {
        if (KIND(r->ctyp) == PTR)
        {
            t = l;
            l = r;
            r = t;
        }
        
        if (KIND(r->ctyp) == PTR)
            die("pointers added");
        
        goto Scale;
    }

    if (op == '-')
    {
        if (KIND(l->ctyp) != PTR)
            die("pointer substracted from integer");
        
        if (KIND(r->ctyp) != PTR)
            goto Scale;
        
        if (l->ctyp != r->ctyp)
            die("non-homogeneous pointers in substraction");
        
        return LNG;
    }

Scale:

    sz = SIZE(DREF(l->ctyp));
    
    if (r->t == Con)
        r->u.n *= sz;
    
    else
    {
        if (irtyp(r->ctyp) != 'l')
            sext(r);
        fprintf(of, "\t%%t%d =l mul %d, ", tmp, sz);
        psymb(*r);
        fprintf(of, "\n");
        r->u.n = tmp++;
    }

    return l->ctyp;
}

void load(Symb d, Symb s)
{
    char t;

    fprintf(of, "\t");
    psymb(d);
    t = irtyp(d.ctyp);
    fprintf(of, " =%c load%c ", t, t);
    psymb(s);
    fprintf(of, "\n");
}

void call(Node *n, Symb *sr)
{
    Node *a;
    char *f;
    unsigned ft;

    f = n->l->u.v;
    
    if (varget(f))
    {
        ft = varget(f)->ctyp;
        if (KIND(ft) != FUN)
            die("invalid call");
    }
    else
        ft = FUNC(INT);
    
    sr->ctyp = DREF(ft);
    
    for (a=n->r; a; a=a->r)
        a->u.s = expr(a->l);
    
    fprintf(of, "\t");
    psymb(*sr);
    fprintf(of, " =%c call $%s(", irtyp(sr->ctyp), f);
    
    for (a=n->r; a; a=a->r)
    {
        fprintf(of, "%c ", irtyp(a->u.s.ctyp));
        psymb(a->u.s);
        fprintf(of, ", ");
    }
    
    fprintf(of, "...)\n");
}

Symb expr(Node *n)
{
    static char *otoa[] =
    {
        ['+'] = "add",
        ['-'] = "sub",
        ['*'] = "mul",
        ['/'] = "div",
        ['%'] = "rem",
        ['&'] = "and",
        ['<'] = "cslt",  /* meeeeh, wrong for pointers! */
        ['l'] = "csle",
        ['e'] = "ceq",
        ['n'] = "cne",
    };
    
    Symb sr, s0, s1, sl;
    int o, l;
    char ty[2];
 
    sr.t     = Tmp;
    sr.u.n     = tmp++;

    switch (n->op) 
    {
        case 0:
            abort();

        // and/or

        case 'o':

        // assign

        case 'a':

            l = lbl;
            lbl += 3;
            branch(n, l, l+1);
            fprintf(of, "@l%d\n", l);
            fprintf(of, "\tjmp @l%d\n", l+2);
            fprintf(of, "@l%d\n", l+1);
            fprintf(of, "\tjmp @l%d\n", l+2);
            fprintf(of, "@l%d\n", l+2);
            fprintf(of, "\t");
            sr.ctyp = INT;
            psymb(sr);
            fprintf(of, " =w phi @l%d 1, @l%d 0\n", l, l+1);
            break;

        // load value

        case 'V':

            s0         = lval(n);
            sr.ctyp = s0.ctyp;
            load(sr, s0);
            break;

        // constant

        case 'N':

            sr.t   	= Con;
            sr.u.n  = n->u.n;
            
            if (n->u.s.ctyp == INT)
                sr.ctyp = INT;
            break;

        // Symbol reference

        case 'S':

            sr.t 	= Glo;
            sr.u.n  = n->u.n;
            sr.ctyp = IDIR(INT);
            break;

        case 'C':

            call(n, &sr);
            break;

        case '@':

            s0 = expr(n->l);
            if (KIND(s0.ctyp) != PTR)
                die("dereference of a non-pointer");
            sr.ctyp = DREF(s0.ctyp);
            load(sr, s0);
            break;

        case 'A':

            sr = lval(n->l);
            sr.ctyp = IDIR(sr.ctyp);
            break;

        case '=':

            s0 = expr(n->r);
            s1 = lval(n->l);
            sr = s0;
            
            if (s1.ctyp == LNG &&  s0.ctyp == INT)
                sext(&s0);
            
            if (s0.ctyp != IDIR(NIL) || KIND(s1.ctyp) != PTR)
                if (s1.ctyp != IDIR(NIL) || KIND(s0.ctyp) != PTR)
                if (s1.ctyp != s0.ctyp)
                    die("invalid assignment");
            
                fprintf(of, "\tstore%c ", irtyp(s1.ctyp));
            goto Args;

        case 'P':
        case 'M':
            o = n->op == 'P' ? '+' : '-';
            sl = lval(n->l);
            s0.t = Tmp;
            s0.u.n = tmp++;
            s0.ctyp = sl.ctyp;
            load(s0, sl);
            s1.t = Con;
            s1.u.n = 1;
            s1.ctyp = INT;
            goto Binop;

        default:
            s0 = expr(n->l);
            s1 = expr(n->r);
            o = n->op;
        Binop:
            sr.ctyp = prom(o, &s0, &s1);
            if (strchr("ne<l", n->op)) {
                sprintf(ty, "%c", irtyp(sr.ctyp));
                sr.ctyp = INT;
            } else
                strcpy(ty, "");
            fprintf(of, "\t");
            psymb(sr);
            fprintf(of, " =%c", irtyp(sr.ctyp));
            fprintf(of, " %s%s ", otoa[o], ty);
        Args:
            psymb(s0);
            fprintf(of, ", ");
            psymb(s1);
            fprintf(of, "\n");
            break;

    }

    if (n->op == '-' &&  KIND(s0.ctyp) == PTR &&  KIND(s1.ctyp) == PTR) 
    {
        fprintf(of, "\t%%t%d =l div ", tmp);
        psymb(sr);
        fprintf(of, ", %d\n", SIZE(DREF(s0.ctyp)));
        sr.u.n = tmp++;
    }

    if (n->op == 'P' || n->op == 'M') 
    {
        fprintf(of, "\tstore%c ", irtyp(sl.ctyp));
        psymb(sr);
        fprintf(of, ", ");
        psymb(sl);
        fprintf(of, "\n");
        sr = s0;
    }
    
    return sr;
}

Symb
lval(Node *n)
{
    Symb sr;

    switch (n->op) {
    default:
        die("invalid lvalue");
    case 'V':
        if (!varget(n->u.v))
            die("undefined variable");
        sr = *varget(n->u.v);
        break;
    case '@':
        sr = expr(n->l);
        if (KIND(sr.ctyp) != PTR)
            die("dereference of a non-pointer");
        sr.ctyp = DREF(sr.ctyp);
        break;
    }
    return sr;
}

void
branch(Node *n, int lt, int lf)
{
    Symb s;
    int l;

    switch (n->op) {
    default:
        s = expr(n); /* TODO: insert comparison to 0 with proper type */
        fprintf(of, "\tjnz ");
        psymb(s);
        fprintf(of, ", @l%d, @l%d\n", lt, lf);
        break;
    case 'o':
        l = lbl;
        lbl += 1;
        branch(n->l, lt, l);
        fprintf(of, "@l%d\n", l);
        branch(n->r, lt, lf);
        break;
    case 'a':
        l = lbl;
        lbl += 1;
        branch(n->l, l, lf);
        fprintf(of, "@l%d\n", l);
        branch(n->r, lt, lf);
        break;
    }
}

int
stmt(Stmt *s, int b)
{
    int l, r;
    Symb x;

    if (!s)
        return 0;

    switch (s->t) 
    {
        case Ret:
            
            x = expr(s->p1);
            fprintf(of, "\tret ");
            psymb(x);
            fprintf(of, "\n");
            return 1;
        
        case Break:
            
            if (b < 0)
                die("break not in loop");
            fprintf(of, "\tjmp @l%d\n", b);
            return 1;
        
        case Expr:
            
            expr(s->p1);
            return 0;
        
        case Seq:
            
            return stmt(s->p1, b) || stmt(s->p2, b);
        
        case If:
            
            l = lbl;
            lbl += 3;
            branch(s->p1, l, l+1);
            fprintf(of, "@l%d\n", l);
            if (!(r=stmt(s->p2, b)))
            if (s->p3)
                fprintf(of, "\tjmp @l%d\n", l+2);
            fprintf(of, "@l%d\n", l+1);
            if (s->p3)
            if (!(r &= stmt(s->p3, b)))
                fprintf(of, "@l%d\n", l+2);
            return s->p3 && r;
        
        case While:
            
            l = lbl;
            lbl += 3;
            fprintf(of, "@l%d\n", l);
            branch(s->p1, l+1, l+2);
            fprintf(of, "@l%d\n", l+1);
            if (!stmt(s->p2, l+2))
                fprintf(of, "\tjmp @l%d\n", l);
            fprintf(of, "@l%d\n", l+2);
            return 0;
    }
}

Node *
mknode(char op, Node *l, Node *r)
{
    Node *n;

    n = alloc(sizeof *n);
    n->op = op;
    n->l = l;
    n->r = r;
    return n;
}

Node *
mkidx(Node *a, Node *i)
{
    Node *n;

    n = mknode('+', a, i);
    n = mknode('@', n, 0);
    return n;
}

Node *
mkneg(Node *n)
{
    static Node *z;

    if (!z) {
        z = mknode('N', 0, 0);
        z->u.n = 0;
    }
    return mknode('-', z, n);
}

Stmt *
mkstmt(int t, void *p1, void *p2, void *p3)
{
    Stmt *s;

    s = alloc(sizeof *s);
    s->t = t;
    s->p1 = p1;
    s->p2 = p2;
    s->p3 = p3;
    return s;
}

Node *
param(char *v, unsigned ctyp, Node *pl)
{
    Node *n;

    if (ctyp == NIL)
        die("invalid void declaration");
    n = mknode(0, 0, pl);
    varadd(v, 0, ctyp);
    strcpy(n->u.v, v);
    return n;
}

Stmt *
mkfor(Node *ini, Node *tst, Node *inc, Stmt *s)
{
    Stmt *s1, *s2;

    if (ini)
        s1 = mkstmt(Expr, ini, 0, 0);
    else
        s1 = 0;
    if (inc) {
        s2 = mkstmt(Expr, inc, 0, 0);
        s2 = mkstmt(Seq, s, s2, 0);
    } else
        s2 = s;
    if (!tst) {
        tst = mknode('N', 0, 0);
        tst->u.n = 1;
    }
    s2 = mkstmt(While, tst, s2, 0);
    if (s1)
        return mkstmt(Seq, s1, s2, 0);
    else
        return s2;
}


typedef union {
    Node *n;
    Stmt *s;
    unsigned u;
} yyunion;
#define YYSTYPE yyunion
short yyini = 0;
short yyntoks = 40;
short yyr1[] = {
   2,   2,   1,   1,   1,   1,   1,   3,   2,   3,
   2,   5,   7,   5,   9,   2,   0,   1,   3,   3,
   3,   3,   3,   3,   3,   3,   3,   3,   3,   3,
   3,   3,   3,   1,   0,   1,   2,   2,   2,   1,
   1,   1,   4,   3,   4,   4,   2,   2,   1,   0,
   1,   3,   1,   0,   4,   2,   2,   2,   2,   0,
   6,   5,   3,   0,   4,   0,   4
};
short yyr2[] = {
   0,   1,   1,   1,   1,   1,   2,   2,   2,   2,
   2,   2,   2,   2,   2,   3,   3,   4,   4,   4,
   4,   4,   4,   4,   4,   4,   4,   4,   4,   4,
   4,   4,   4,   5,   5,   6,   6,   6,   6,   7,
   7,   7,   7,   7,   7,   7,   7,   7,   8,   8,
   9,   9,  10,  10,  11,  11,  12,  12,  12,  12,
  13,  14,  15,  16,  17,  18,  18
};
short yyadef[] = {
  59,  -1,   0,  -1,  -1,  -1,  -1,   1,   2,   3,
   4,   5,   6,  16,  -1,   7,  -1,   8,  -1,  -1,
   9,  -1,  10,  -1,  -1,  -1,  -1,  11,  -1,  -1,
  -1,  -1,  13,  -1,  12,  -1,  34,  -1,  34,  -1,
  34,  -1,  -1,  14,  -1,  15,  17,  18,  19,  20,
  21,  22,  23,  24,  25,  26,  27,  28,  29,  30,
  31,  32,  33,  -1,  -1,  50,  -1,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  -1,  35,  -1,  36,  -1,  37,  -1,  38,  39,  40,
  41,  -1,  -1,  42,  -1,  43,  49,  -1,  44,  -1,
  45,  46,  47,  48,  -1,  51,  52,  55,  -1,  54,
  59,  56,  59,  57,  59,  58,  -1,  -1,  65,  16,
  60,  -1,  -1,  -1,  61,  62,  -1,  53,  -1,  64,
  -1,  66
};
short yygdef[] = {
  -1,   5,  45,  14,  21,  37,  46,  81,  97, 103,
 128, 109,   1, 110, 112, 114, 116, 117, 119
};
short yyadsp[] = {
 102,  11, -40, -11,  29,  58, 131, -40, -40, -40,
 -40, -40, -40, -40,  -1, -40, -15, -40, 107,  17,
 -40,  43, -40, -19, 107,  69, 233, -40, -12, 107,
  97, 233,  12, 233, -40,  -7, 107,  -5, 107,  -4,
 107,  24, 233, -40, 130, -40, -40, 250, -21, -21,
 -40, -40, -40,  25,  25,  25,  25,  53,  53, 312,
 286, 276, 250, 148, 176, 202, 107, 107, 107, 107,
 107, 107, 107, 107, 107, 107, 107, 107, 107, 107,
 107, 146, 107, -40, 107, -40, 107, -40, -40, -40,
  54,  74,  -6, -40, 107, -40, 107,  52, -40, 107,
 -40, -40, -40, -40, 107, -40, -40,  64,  -6, -40,
 102, -40, 102, -40, 102, -40, 104, 106, -40,  -6,
 -40, 108, 111, 103, -40, -40, 117,  -6, 120, -40,
 122, -40
};
short yygdsp[] = {
-132, 238, 211,  38, 326, 123, 103,-132,-132,  76,
-132,  64,  76,-132,-132,-132,-132,-132,-132
};
short yyact[] = {
  88,  89,  90,  11,   8,  10,   9,  91,  69,  70,
  71,   2,  28,  24,  23,  35,  16,  18,   7,  17,
  29,  86,  93,  74,  75,  36,  33,  82,  84,  38,
  40,  94, 107,  12,  13,  15,  66,  80,  79,  78,
  76,  77,  72,  73,  67,  68,  69,  70,  71,  74,
  75,  20,  67,  68,  69,  70,  71,  42,   7,  74,
  75, 121,  66,  80,  79,  78,  76,  77,  72,  73,
  67,  68,  69,  70,  71,  74,  75,  22,  72,  73,
  67,  68,  69,  70,  71,  98,  96,   7,  66,  80,
  79,  78,  76,  77,  72,  73,  67,  68,  69,  70,
  71, 108,  26,  74,  75, -65,  92, 126,  88,  89,
  90,  11,   8,  10,   9,  91,  66,  80,  79,  78,
  76,  77,  72,  73,  67,  68,  69,  70,  71,  86,
  31,  88,  89,  90, 130,  82,  84, 124,  91,  94,
 122, 118, 125,  28, 123,  23,  35,  16,  18, 127,
 101, 102,  86, 129,  74,  75, 131,  44,  82,  84,
   7,  39,  94,  41,  12,  13, 120,  66,  80,  79,
  78,  76,  77,  72,  73,  67,  68,  69,  70,  71,
 105,  95,  74,  75,  99,  83, 111,  85, 113,  87,
 115, 106,  -1,  -1,  -1,  66,  80,  79,  78,  76,
  77,  72,  73,  67,  68,  69,  70,  71,  74,  75,
  -1,  -1,  -1,  -1,  -1, 100,  -1,  -1,  -1,  -1,
  -1,  66,  80,  79,  78,  76,  77,  72,  73,  67,
  68,  69,  70,  71,  88,  89,  90,  27,  -1, 104,
  -1,  91,  32,  -1,  34,  -1,  28,  -1,  23,  35,
  16,  18,  -1,  43,  -1,  86,  74,  75,  -1,  -1,
  -1,  82,  84,  -1,  -1,  94,  -1,  12,  13,  66,
  80,  79,  78,  76,  77,  72,  73,  67,  68,  69,
  70,  71,  74,  75,  -1,  -1,  -1,  -1,  -1,  -1,
  -1,  -1,  74,  75,  -1,  -1,  -1,  79,  78,  76,
  77,  72,  73,  67,  68,  69,  70,  71,  78,  76,
  77,  72,  73,  67,  68,  69,  70,  71,  74,  75,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
   3,  -1,  -1,  -1,  -1,  76,  77,  72,  73,  67,
  68,  69,  70,  71,  19,  -1,   4,  -1,  -1,  -1,
  25,  -1,  -1,  -1,  -1,  30,  -1,   6,  -1,  -1,
  -1,  -1,  62,  -1,  62,   4,  62,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  -1,  -1,  47,  48,  49,  50,  51,  52,  53,  54,
  55,  56,  57,  58,  59,  60,  61,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  63,  -1,  65,  -1,  -1,  64,  -1,  -1,  -1,  -1,
  65
};
short yychk[] = {
   1,   2,   3,   9,  10,  11,  12,   8,  29,  30,
  31,   0,  13,  32,  15,  16,  17,  18,  29,  34,
  32,  22,  33,   6,   7,  32,  14,  28,  29,  34,
  34,  32,   3,  34,  35,  36,  19,  20,  21,  22,
  23,  24,  25,  26,  27,  28,  29,  30,  31,   6,
   7,  34,  27,  28,  29,  30,  31,  33,  29,   6,
   7,   3,  19,  20,  21,  22,  23,  24,  25,  26,
  27,  28,  29,  30,  31,   6,   7,  34,  25,  26,
  27,  28,  29,  30,  31,  33,  32,  29,  19,  20,
  21,  22,  23,  24,  25,  26,  27,  28,  29,  30,
  31,  37,  33,   6,   7,   3,  32,   3,   1,   2,
   3,   9,  10,  11,  12,   8,  19,  20,  21,  22,
  23,  24,  25,  26,  27,  28,  29,  30,  31,  22,
  33,   1,   2,   3,   3,  28,  29,  34,   8,  32,
  32,  35,  34,  13,  33,  15,  16,  17,  18,  32,
   4,   5,  22,  33,   6,   7,  34,  43,  28,  29,
  29,  45,  32,  45,  34,  35,  36,  19,  20,  21,
  22,  23,  24,  25,  26,  27,  28,  29,  30,  31,
  49,  33,   6,   7,  38,  46,  52,  46,  52,  46,
  52,  51,  -1,  -1,  -1,  19,  20,  21,  22,  23,
  24,  25,  26,  27,  28,  29,  30,  31,   6,   7,
  -1,  -1,  -1,  -1,  -1,  39,  -1,  -1,  -1,  -1,
  -1,  19,  20,  21,  22,  23,  24,  25,  26,  27,
  28,  29,  30,  31,   1,   2,   3,  42,  -1,  37,
  -1,   8,  42,  -1,  42,  -1,  13,  -1,  15,  16,
  17,  18,  -1,  42,  -1,  22,   6,   7,  -1,  -1,
  -1,  28,  29,  -1,  -1,  32,  -1,  34,  35,  19,
  20,  21,  22,  23,  24,  25,  26,  27,  28,  29,
  30,  31,   6,   7,  -1,  -1,  -1,  -1,  -1,  -1,
  -1,  -1,   6,   7,  -1,  -1,  -1,  21,  22,  23,
  24,  25,  26,  27,  28,  29,  30,  31,  22,  23,
  24,  25,  26,  27,  28,  29,  30,  31,   6,   7,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  41,  -1,  -1,  -1,  -1,  23,  24,  25,  26,  27,
  28,  29,  30,  31,  44,  -1,  41,  -1,  -1,  -1,
  44,  -1,  -1,  -1,  -1,  44,  -1,  41,  -1,  -1,
  -1,  -1,  44,  -1,  44,  41,  44,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  -1,  -1,  44,  44,  44,  44,  44,  44,  44,  44,
  44,  44,  44,  44,  44,  44,  44,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  44,  -1,  44,  -1,  -1,  44,  -1,  -1,  -1,  -1,
  44
};
#define NUM 128
#define STR 129
#define IDENT 130
#define PP 131
#define MM 132
#define LE 133
#define GE 134
#define SIZEOF 135
#define TVOID 136
#define TINT 137
#define TFLOAT 138
#define TLNG 139
#define IF 140
#define ELSE 141
#define WHILE 142
#define FOR 143
#define BREAK 144
#define RETURN 145
#define OR 146
#define AND 147
#define EQ 148
#define NE 149
short yytrns[] = {
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,  31,  22,   0,
  32,  33,  29,  27,  37,  28,   0,  30,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,  34,
  25,  19,  26,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,  38,   0,  39,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,  35,   0,  36,   0,   0,   1,   2,
   3,   4,   5,   6,   7,   8,   9,  10,  11,  12,
  13,  14,  15,  16,  17,  18,  20,  21,  23,  24
};

#ifndef YYSTYPE
#define YYSTYPE int
#endif
YYSTYPE yylval;

int
yyparse()
{
	enum {
		StackSize = 100,
		ActSz = sizeof yyact / sizeof yyact[0],
	};
	struct {
		YYSTYPE val;
		int state;
	} stk[StackSize], *ps;
	int r, h, n, s, tk;
	YYSTYPE yyval;

	ps = stk;
	ps->state = s = yyini;
	tk = -1;
loop:
	n = yyadsp[s];
	if (tk < 0 && n > -yyntoks)
		tk = yytrns[yylex()];
	n += tk;
	if (n < 0 || n >= ActSz || yychk[n] != tk) {
		r = yyadef[s];
		if (r < 0)
			return -1;
		goto reduce;
	}
	n = yyact[n];
	if (n == -1)
		return -1;
	if (n < 0) {
		r = - (n+2);
		goto reduce;
	}
	tk = -1;
	yyval = yylval;
stack:
	ps++;
	if (ps-stk >= StackSize)
		return -2;
	s = n;
	ps->state = s;
	ps->val = yyval;
	goto loop;
reduce:
	ps -= yyr1[r];
	h = yyr2[r];
	s = ps->state;
	n = yygdsp[h] + s;
	if (n < 0 || n >= ActSz || yychk[n] != yyntoks+h)
		n = yygdef[h];
	else
		n = yyact[n];
	switch (r) {
	case 0:
		yyval = ps[1].val; return 0;
		break;
	case 1:
{ yyval.u = IDIR(ps[1].val.u); }
		break;
	case 2:
{ yyval.u = INT; }
		break;
	case 3:
{ yyval.u = LNG; }
		break;
	case 4:
{ yyval.u = FLOAT; }
		break;
	case 5:
{ yyval.u = NIL; }
		break;
	case 6:
{ yyval.s = 0; }
		break;
	case 7:
{ yyval.s = ps[2].val.s; }
		break;
	case 8:
{ yyval.s = mkstmt(Break, 0, 0, 0); }
		break;
	case 9:
{ yyval.s = mkstmt(Ret, ps[2].val.n, 0, 0); }
		break;
	case 10:
{ yyval.s = mkstmt(Expr, ps[1].val.n, 0, 0); }
		break;
	case 11:
{ yyval.s = mkstmt(While, ps[3].val.n, ps[5].val.s, 0); }
		break;
	case 12:
{ yyval.s = mkstmt(If, ps[3].val.n, ps[5].val.s, ps[7].val.s); }
		break;
	case 13:
{ yyval.s = mkstmt(If, ps[3].val.n, ps[5].val.s, 0); }
		break;
	case 14:
{ yyval.s = mkfor(ps[3].val.n, ps[5].val.n, ps[7].val.n, ps[9].val.s); }
		break;
	case 15:
{ yyval.s = mkstmt(Seq, ps[1].val.s, ps[2].val.s, 0); }
		break;
	case 16:
{ yyval.s = 0; }
		break;
	case 17:
		break;
	case 18:
{ yyval.n = mknode('=', ps[1].val.n, ps[3].val.n); }
		break;
	case 19:
{ yyval.n = mknode('+', ps[1].val.n, ps[3].val.n); }
		break;
	case 20:
{ yyval.n = mknode('-', ps[1].val.n, ps[3].val.n); }
		break;
	case 21:
{ yyval.n = mknode('*', ps[1].val.n, ps[3].val.n); }
		break;
	case 22:
{ yyval.n = mknode('/', ps[1].val.n, ps[3].val.n); }
		break;
	case 23:
{ yyval.n = mknode('%', ps[1].val.n, ps[3].val.n); }
		break;
	case 24:
{ yyval.n = mknode('<', ps[1].val.n, ps[3].val.n); }
		break;
	case 25:
{ yyval.n = mknode('<', ps[3].val.n, ps[1].val.n); }
		break;
	case 26:
{ yyval.n = mknode('l', ps[1].val.n, ps[3].val.n); }
		break;
	case 27:
{ yyval.n = mknode('l', ps[3].val.n, ps[1].val.n); }
		break;
	case 28:
{ yyval.n = mknode('e', ps[1].val.n, ps[3].val.n); }
		break;
	case 29:
{ yyval.n = mknode('n', ps[1].val.n, ps[3].val.n); }
		break;
	case 30:
{ yyval.n = mknode('&', ps[1].val.n, ps[3].val.n); }
		break;
	case 31:
{ yyval.n = mknode('a', ps[1].val.n, ps[3].val.n); }
		break;
	case 32:
{ yyval.n = mknode('o', ps[1].val.n, ps[3].val.n); }
		break;
	case 33:
		break;
	case 34:
{ yyval.n = 0; }
		break;
	case 35:
		break;
	case 36:
{ yyval.n = mkneg(ps[2].val.n); }
		break;
	case 37:
{ yyval.n = mknode('@', ps[2].val.n, 0); }
		break;
	case 38:
{ yyval.n = mknode('A', ps[2].val.n, 0); }
		break;
	case 39:
		break;
	case 40:
		break;
	case 41:
		break;
	case 42:
{ yyval.n = mknode('N', 0, 0); yyval.n->u.n = SIZE(ps[3].val.u); }
		break;
	case 43:
{ yyval.n = ps[2].val.n; }
		break;
	case 44:
{ yyval.n = mknode('C', ps[1].val.n, ps[3].val.n); }
		break;
	case 45:
{ yyval.n = mkidx(ps[1].val.n, ps[3].val.n); }
		break;
	case 46:
{ yyval.n = mknode('P', ps[1].val.n, 0); }
		break;
	case 47:
{ yyval.n = mknode('M', ps[1].val.n, 0); }
		break;
	case 48:
		break;
	case 49:
{ yyval.n = 0; }
		break;
	case 50:
{ yyval.n = mknode(0, ps[1].val.n, 0); }
		break;
	case 51:
{ yyval.n = mknode(0, ps[1].val.n, ps[3].val.n); }
		break;
	case 52:
		break;
	case 53:
{ yyval.n = 0; }
		break;
	case 54:
{ yyval.n = param(ps[2].val.n->u.v, ps[1].val.u, ps[4].val.n); }
		break;
	case 55:
{ yyval.n = param(ps[2].val.n->u.v, ps[1].val.u, 0); }
		break;
	case 56:
		break;
	case 57:
		break;
	case 58:
		break;
	case 59:
		break;
	case 60:
{
    if (!stmt(ps[5].val.s, -1))
        fprintf(of, "\tret 0\n");
    fprintf(of, "}\n\n");
}
		break;
	case 61:
{
    varadd(ps[2].val.n->u.v, 1, FUNC(ps[1].val.u));
}
		break;
	case 62:
{
    if (ps[1].val.u == NIL)
        die("invalid void declaration");
    if (nglo == NGlo)
        die("too many string literals");
    ini[nglo] = alloc(sizeof "{ x 0 }");
    sprintf(ini[nglo], "{ %c 0 }", irtyp(ps[1].val.u));
    varadd(ps[2].val.n->u.v, nglo++, ps[1].val.u);
}
		break;
	case 63:
{
    varclr();
    tmp = 0;
}
		break;
	case 64:
{
    Symb *s;
    Node *n;
    int t, m;

    varadd(ps[1].val.n->u.v, 1, FUNC(INT));
    fprintf(of, "export function w $%s(", ps[1].val.n->u.v);
    n = ps[3].val.n;
    if (n)
        for (;;) {
            s = varget(n->u.v);
            fprintf(of, "%c ", irtyp(s->ctyp));
            fprintf(of, "%%t%d", tmp++);
            n = n->r;
            if (n)
                fprintf(of, ", ");
            else
                break;
        }
    fprintf(of, ") {\n");
    fprintf(of, "@l%d\n", lbl++);
    for (t=0, n=ps[3].val.n; n; t++, n=n->r) {
        s = varget(n->u.v);
        m = SIZE(s->ctyp);
        fprintf(of, "\t%%%s =l alloc%d %d\n", n->u.v, m, m);
        fprintf(of, "\tstore%c %%t%d", irtyp(s->ctyp), t);
        fprintf(of, ", %%%s\n", n->u.v);
    }
}
		break;
	case 65:
		break;
	case 66:
{
    int s;
    char *v;

    if (ps[2].val.u == NIL)
        die("invalid void declaration");
    v = ps[3].val.n->u.v;
    s = SIZE(ps[2].val.u);
    varadd(v, 0, ps[2].val.u);
    fprintf(of, "\t%%%s =l alloc%d %d\n", v, s, s);
}
		break;
	}
	goto stack;
}


int
yylex()
{
    struct {
        char *s;
        int t;
    } kwds[] = {
        { "void", TVOID },
        { "int", TINT },
        { "float", TFLOAT },
        { "long", TLNG },
        { "if", IF },
        { "else", ELSE },
        { "for", FOR },
        { "while", WHILE },
        { "return", RETURN },
        { "break", BREAK },
        { "sizeof", SIZEOF },
        { 0, 0 }
    };
    int i, c, c1, n;
    char v[NString], *p;

    do {
        c = getchar();
        if (c == '#')
            while ((c = getchar()) != '\n')
                ;
        if (c == '\n')
            line++;
    } while (isspace(c));


    if (c == EOF)
        return 0;


    if (isdigit(c)) {
        n = 0;
        do {
            n *= 10;
            n += c-'0';
            c = getchar();
        } while (isdigit(c));
        ungetc(c, stdin);
        yylval.n = mknode('N', 0, 0);
        yylval.n->u.n = n;
        return NUM;
    }

    if (isalpha(c)) {
        p = v;
        do {
            if (p == &v[NString-1])
                die("ident too long");
            *p++ = c;
            c = getchar();
        } while (isalpha(c) || c == '_');
        *p = 0;
        ungetc(c, stdin);
        for (i=0; kwds[i].s; i++)
            if (strcmp(v, kwds[i].s) == 0)
                return kwds[i].t;
        yylval.n = mknode('V', 0, 0);
        strcpy(yylval.n->u.v, v);
        return IDENT;
    }

    if (c == '"') {
        i = 0;
        n = 32;
        p = alloc(n);
        strcpy(p, "{ b \"");
        for (i=5;; i++) {
            c = getchar();
            if (c == EOF)
                die("unclosed string literal");
            if (i+8 >= n) {
                p = memcpy(alloc(n*2), p, n);
                n *= 2;
            }
            p[i] = c;
            if (c == '"' && p[i-1]!='\\')
                break;
        }
        strcpy(&p[i], "\", b 0 }");
        if (nglo == NGlo)
            die("too many globals");
        ini[nglo] = p;
        yylval.n = mknode('S', 0, 0);
        yylval.n->u.n = nglo++;
        return STR;
    }

    c1 = getchar();
#define DI(a, b) a + b*256
    switch (DI(c,c1)) {
    case DI('!','='): return NE;
    case DI('=','='): return EQ;
    case DI('<','='): return LE;
    case DI('>','='): return GE;
    case DI('+','+'): return PP;
    case DI('-','-'): return MM;
    case DI('&','&'): return AND;
    case DI('|','|'): return OR;
    }
#undef DI
    ungetc(c1, stdin);

    return c;
}

int
yyerror(char *err)
{
    die("parse error");
    return 0;
}

int main (int argc, char** argv)
{
    if (argc > 1) 
    {
        FILE *infile = fopen(argv[1], "r");
        if (!infile) {
            perror("fopen");
            return 1;
        }

        dup2(fileno(infile), fileno(stdin));
        fclose(infile);
    }

    int i;
    of      = stdout;
    nglo    = 1;
    
    if (yyparse() != 0)
        die("parse error");
    for (i=1; i<nglo; i++)
        fprintf(of, "data $glo%d = %s\n", i, ini[i]);
    return 0;
}
