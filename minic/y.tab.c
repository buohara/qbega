#line 1 "minic.y"


#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum {
	NString = 32,
	NGlo = 256,
	NVar = 512,
	NStr = 256,
};

enum { /* minic types */
	NIL,
	INT,
	LNG,
	PTR,
	FUN,
};

#define IDIR(x) (((x) << 3) + PTR)
#define FUNC(x) (((x) << 3) + FUN)
#define DREF(x) ((x) >> 3)
#define KIND(x) ((x) & 7)
#define SIZE(x)                                    \
	(x == NIL ? (die("void has no size"), 0) : \
	 x == INT ? 4 : 8)

typedef struct Node Node;
typedef struct Symb Symb;
typedef struct Stmt Stmt;

struct Symb {
	enum {
		Con,
		Tmp,
		Var,
		Glo,
	} t;
	union {
		int n;
		char v[NString];
	} u;
	unsigned long ctyp;
};

struct Node {
	char op;
	union {
		int n;
		char v[NString];
		Symb s;
	} u;
	Node *l, *r;
};

struct Stmt {
	enum {
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
struct {
	char v[NString];
	unsigned ctyp;
	int glo;
} varh[NVar];

void
die(char *s)
{
	fprintf(stderr, "error:%d: %s\n", line, s);
	exit(1);
}

void *
alloc(size_t s)
{
	void *p;

	p = malloc(s);
	if (!p)
		die("out of memory");
	return p;
}

unsigned
hash(char *s)
{
	unsigned h;

	h = 42;
	while (*s)
		h += 11 * h + *s++;
	return h % NVar;
}

void
varclr()
{
	unsigned h;

	for (h=0; h<NVar; h++)
		if (!varh[h].glo)
			varh[h].v[0] = 0;
}

void
varadd(char *v, int glo, unsigned ctyp)
{
	unsigned h0, h;

	h0 = hash(v);
	h = h0;
	do {
		if (varh[h].v[0] == 0) {
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

Symb *
varget(char *v)
{
	static Symb s;
	unsigned h0, h;

	h0 = hash(v);
	h = h0;
	do {
		if (strcmp(varh[h].v, v) == 0) {
			if (!varh[h].glo) {
				s.t = Var;
				strcpy(s.u.v, v);
			} else {
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

char
irtyp(unsigned ctyp)
{
	return SIZE(ctyp) == 8 ? 'l' : 'w';
}

void
psymb(Symb s)
{
	switch (s.t) {
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

void
sext(Symb *s)
{
	fprintf(of, "\t%%t%d =l extsw ", tmp);
	psymb(*s);
	fprintf(of, "\n");
	s->t = Tmp;
	s->ctyp = LNG;
	s->u.n = tmp++;
}

unsigned
prom(int op, Symb *l, Symb *r)
{
	Symb *t;
	int sz;

	if (l->ctyp == r->ctyp && KIND(l->ctyp) != PTR)
		return l->ctyp;

	if (l->ctyp == LNG && r->ctyp == INT) {
		sext(r);
		return LNG;
	}
	if (l->ctyp == INT && r->ctyp == LNG) {
		sext(l);
		return LNG;
	}

	if (op == '+') {
		if (KIND(r->ctyp) == PTR) {
			t = l;
			l = r;
			r = t;
		}
		if (KIND(r->ctyp) == PTR)
			die("pointers added");
		goto Scale;
	}

	if (op == '-') {
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
	else {
		if (irtyp(r->ctyp) != 'l')
			sext(r);
		fprintf(of, "\t%%t%d =l mul %d, ", tmp, sz);
		psymb(*r);
		fprintf(of, "\n");
		r->u.n = tmp++;
	}
	return l->ctyp;
}

void
load(Symb d, Symb s)
{
	char t;

	fprintf(of, "\t");
	psymb(d);
	t = irtyp(d.ctyp);
	fprintf(of, " =%c load%c ", t, t);
	psymb(s);
	fprintf(of, "\n");
}

void
call(Node *n, Symb *sr)
{
	Node *a;
	char *f;
	unsigned ft;

	f = n->l->u.v;
	if (varget(f)) {
		ft = varget(f)->ctyp;
		if (KIND(ft) != FUN)
			die("invalid call");
	} else
		ft = FUNC(INT);
	sr->ctyp = DREF(ft);
	for (a=n->r; a; a=a->r)
		a->u.s = expr(a->l);
	fprintf(of, "\t");
	psymb(*sr);
	fprintf(of, " =%c call $%s(", irtyp(sr->ctyp), f);
	for (a=n->r; a; a=a->r) {
		fprintf(of, "%c ", irtyp(a->u.s.ctyp));
		psymb(a->u.s);
		fprintf(of, ", ");
	}
	fprintf(of, "...)\n");
}

Symb
expr(Node *n)
{
	static char *otoa[] = {
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

	sr.t = Tmp;
	sr.u.n = tmp++;

	switch (n->op) {

	case 0:
		abort();

	case 'o':
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

	case 'V':
		s0 = lval(n);
		sr.ctyp = s0.ctyp;
		load(sr, s0);
		break;

	case 'N':
		sr.t = Con;
		sr.u.n = n->u.n;
		sr.ctyp = INT;
		break;

	case 'S':
		sr.t = Glo;
		sr.u.n = n->u.n;
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
	if (n->op == '-'
	&&  KIND(s0.ctyp) == PTR
	&&  KIND(s1.ctyp) == PTR) {
		fprintf(of, "\t%%t%d =l div ", tmp);
		psymb(sr);
		fprintf(of, ", %d\n", SIZE(DREF(s0.ctyp)));
		sr.u.n = tmp++;
	}
	if (n->op == 'P' || n->op == 'M') {
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

	switch (s->t) {
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


#line 639 "minic.y"
typedef union {
	Node *n;
	Stmt *s;
	unsigned u;
} yyunion;
#define YYSTYPE yyunion
short yyini = 0;
short yyntoks = 39;
short yyr1[] = {
   2,   2,   1,   1,   1,   1,   3,   2,   3,   2,
   5,   7,   5,   9,   2,   0,   1,   3,   3,   3,
   3,   3,   3,   3,   3,   3,   3,   3,   3,   3,
   3,   3,   1,   0,   1,   2,   2,   2,   1,   1,
   1,   4,   3,   4,   4,   2,   2,   1,   0,   1,
   3,   1,   0,   4,   2,   2,   2,   2,   0,   6,
   5,   3,   0,   4,   0,   4
};
short yyr2[] = {
   0,   1,   1,   1,   1,   2,   2,   2,   2,   2,
   2,   2,   2,   2,   3,   3,   4,   4,   4,   4,
   4,   4,   4,   4,   4,   4,   4,   4,   4,   4,
   4,   4,   5,   5,   6,   6,   6,   6,   7,   7,
   7,   7,   7,   7,   7,   7,   7,   8,   8,   9,
   9,  10,  10,  11,  11,  12,  12,  12,  12,  13,
  14,  15,  16,  17,  18,  18
};
short yyadef[] = {
  58,  -1,   0,  -1,  -1,  -1,  -1,   1,   2,   3,
   4,   5,  15,  -1,   6,  -1,   7,  -1,  -1,   8,
  -1,   9,  -1,  -1,  -1,  -1,  10,  -1,  -1,  -1,
  -1,  12,  -1,  11,  -1,  33,  -1,  33,  -1,  33,
  -1,  -1,  13,  -1,  14,  16,  17,  18,  19,  20,
  21,  22,  23,  24,  25,  26,  27,  28,  29,  30,
  31,  32,  -1,  -1,  49,  -1,  -1,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  34,  -1,  35,  -1,  36,  -1,  37,  38,  39,  40,
  -1,  -1,  41,  -1,  42,  48,  -1,  43,  -1,  44,
  45,  46,  47,  -1,  50,  51,  54,  -1,  53,  58,
  55,  58,  56,  58,  57,  -1,  -1,  64,  15,  59,
  -1,  -1,  -1,  60,  61,  -1,  52,  -1,  63,  -1,
  65
};
short yygdef[] = {
  -1,   5,  44,  13,  20,  36,  45,  80,  96, 102,
 127, 108,   1, 109, 111, 113, 115, 116, 118
};
short yyadsp[] = {
  95,   9, -39, -22,  28,  80,  81, -39, -39, -39,
 -39, -39, -39,  -1, -39, -21, -39, 313,  17, -39,
  42, -39, -23, 313,  67, 226, -39, -10, 313,  94,
 226,  12, 226, -39,  -9, 313,  -5, 313,  -4, 313,
  75, 226, -39, 126, -39, -39, 243, -25, -25, -39,
 -39, -39,  25,  25,  25,  25,  52,  52, 303, 278,
 268, 243, 144, 171, 196, 313, 313, 313, 313, 313,
 313, 313, 313, 313, 313, 313, 313, 313, 313, 313,
  98, 313, -39, 313, -39, 313, -39, -39, -39,  26,
  79,   8, -39, 313, -39, 313,  93, -39, 313, -39,
 -39, -39, -39, 313, -39, -39,  97,   8, -39,  95,
 -39,  95, -39,  95, -39, 108, 102, -39,   8, -39,
  99, 105, 106, -39, -39, 100,   8, 112, -39, 113,
 -39
};
short yygdsp[] = {
-131, 231, 205,  27, 319, 119,  98,-131,-131,  45,
-131,  23,  71,-131,-131,-131,-131,-131,-131
};
short yyact[] = {
  87,  88,  89,  68,  69,  70,   7,  90,  23,   2,
  92,  27,  16,  22,  34,  15,  17,  10,   8,   9,
  85,  28,  35,  73,  74,  32,  81,  83,  37,  39,
  93, 106,  11,  12,  14,  65,  79,  78,  77,  75,
  76,  71,  72,  66,  67,  68,  69,  70,  73,  74,
  19,  66,  67,  68,  69,  70,   7,  95,  73,  74,
  65,  79,  78,  77,  75,  76,  71,  72,  66,  67,
  68,  69,  70,  73,  74,  21,  71,  72,  66,  67,
  68,  69,  70, 120, 129,  65,  79,  78,  77,  75,
  76,  71,  72,  66,  67,  68,  69,  70, -64,  25,
  73,  74, 100, 101,  10,   8,   9,  41,   7,   7,
  91, 125,  65,  79,  78,  77,  75,  76,  71,  72,
  66,  67,  68,  69,  70,  97,  30,  87,  88,  89,
 121, 126, 124, 107,  90,  98, 117, 122,  27, 123,
  22,  34,  15,  17, 128,  43, 130,  85, 104, 105,
  73,  74,  -1,  81,  83,  -1,  38,  93,  40,  11,
  12, 119,  65,  79,  78,  77,  75,  76,  71,  72,
  66,  67,  68,  69,  70,  -1,  94,  73,  74,  82,
 110,  84, 112,  86, 114,  -1,  -1,  -1,  -1,  65,
  79,  78,  77,  75,  76,  71,  72,  66,  67,  68,
  69,  70,  73,  74,  -1,  -1,  -1,  -1,  -1,  99,
  -1,  -1,  -1,  -1,  65,  79,  78,  77,  75,  76,
  71,  72,  66,  67,  68,  69,  70,  87,  88,  89,
  26,  -1, 103,  -1,  90,  31,  -1,  33,  27,  -1,
  22,  34,  15,  17,  -1,  -1,  42,  85,  -1,  73,
  74,  -1,  -1,  81,  83,  -1,  -1,  93,  -1,  11,
  12,  65,  79,  78,  77,  75,  76,  71,  72,  66,
  67,  68,  69,  70,  73,  74,  -1,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,  73,  74,  -1,  -1,  78,  77,
  75,  76,  71,  72,  66,  67,  68,  69,  70,  77,
  75,  76,  71,  72,  66,  67,  68,  69,  70,  73,
  74,  -1,  -1,  -1,  87,  88,  89,  -1,  -1,  -1,
  -1,  90,   3,  -1,  -1,  75,  76,  71,  72,  66,
  67,  68,  69,  70,  85,  -1,  18,  -1,   4,  -1,
  81,  83,  24,  -1,  93,  -1,  -1,  29,  -1,   6,
  -1,  -1,  -1,  -1,  61,  -1,  61,   4,  61,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,  46,  47,  48,  49,  50,  51,
  52,  53,  54,  55,  56,  57,  58,  59,  60,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  -1,  -1,  62,  -1,  64,  -1,  -1,  63,  -1,  -1,
  -1,  -1,  64
};
short yychk[] = {
   1,   2,   3,  28,  29,  30,  28,   8,  31,   0,
  32,  12,  33,  14,  15,  16,  17,   9,  10,  11,
  21,  31,  31,   6,   7,  13,  27,  28,  33,  33,
  31,   3,  33,  34,  35,  18,  19,  20,  21,  22,
  23,  24,  25,  26,  27,  28,  29,  30,   6,   7,
  33,  26,  27,  28,  29,  30,  28,  31,   6,   7,
  18,  19,  20,  21,  22,  23,  24,  25,  26,  27,
  28,  29,  30,   6,   7,  33,  24,  25,  26,  27,
  28,  29,  30,   3,   3,  18,  19,  20,  21,  22,
  23,  24,  25,  26,  27,  28,  29,  30,   3,  32,
   6,   7,   4,   5,   9,  10,  11,  32,  28,  28,
  31,   3,  18,  19,  20,  21,  22,  23,  24,  25,
  26,  27,  28,  29,  30,  32,  32,   1,   2,   3,
  31,  31,  33,  36,   8,  37,  34,  32,  12,  33,
  14,  15,  16,  17,  32,  42,  33,  21,  48,  50,
   6,   7,  -1,  27,  28,  -1,  44,  31,  44,  33,
  34,  35,  18,  19,  20,  21,  22,  23,  24,  25,
  26,  27,  28,  29,  30,  -1,  32,   6,   7,  45,
  51,  45,  51,  45,  51,  -1,  -1,  -1,  -1,  18,
  19,  20,  21,  22,  23,  24,  25,  26,  27,  28,
  29,  30,   6,   7,  -1,  -1,  -1,  -1,  -1,  38,
  -1,  -1,  -1,  -1,  18,  19,  20,  21,  22,  23,
  24,  25,  26,  27,  28,  29,  30,   1,   2,   3,
  41,  -1,  36,  -1,   8,  41,  -1,  41,  12,  -1,
  14,  15,  16,  17,  -1,  -1,  41,  21,  -1,   6,
   7,  -1,  -1,  27,  28,  -1,  -1,  31,  -1,  33,
  34,  18,  19,  20,  21,  22,  23,  24,  25,  26,
  27,  28,  29,  30,   6,   7,  -1,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,   6,   7,  -1,  -1,  20,  21,
  22,  23,  24,  25,  26,  27,  28,  29,  30,  21,
  22,  23,  24,  25,  26,  27,  28,  29,  30,   6,
   7,  -1,  -1,  -1,   1,   2,   3,  -1,  -1,  -1,
  -1,   8,  40,  -1,  -1,  22,  23,  24,  25,  26,
  27,  28,  29,  30,  21,  -1,  43,  -1,  40,  -1,
  27,  28,  43,  -1,  31,  -1,  -1,  43,  -1,  40,
  -1,  -1,  -1,  -1,  43,  -1,  43,  40,  43,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  -1,  -1,  -1,  -1,  43,  43,  43,  43,  43,  43,
  43,  43,  43,  43,  43,  43,  43,  43,  43,  -1,
  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,
  -1,  -1,  43,  -1,  43,  -1,  -1,  43,  -1,  -1,
  -1,  -1,  43
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
#define TLNG 138
#define IF 139
#define ELSE 140
#define WHILE 141
#define FOR 142
#define BREAK 143
#define RETURN 144
#define OR 145
#define AND 146
#define EQ 147
#define NE 148
short yytrns[] = {
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,  30,  21,   0,
  31,  32,  28,  26,  36,  27,   0,  29,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,  33,
  24,  18,  25,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,  37,   0,  38,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
   0,   0,   0,  34,   0,  35,   0,   0,   1,   2,
   3,   4,   5,   6,   7,   8,   9,  10,  11,  12,
  13,  14,  15,  16,  17,  19,  20,  22,  23
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
#line 0 "minic.y"
		yyval = ps[1].val; return 0;
		break;
	case 1:
#line 751 "minic.y"
{ yyval.u = IDIR(ps[1].val.u); }
		break;
	case 2:
#line 752 "minic.y"
{ yyval.u = INT; }
		break;
	case 3:
#line 753 "minic.y"
{ yyval.u = LNG; }
		break;
	case 4:
#line 754 "minic.y"
{ yyval.u = NIL; }
		break;
	case 5:
#line 757 "minic.y"
{ yyval.s = 0; }
		break;
	case 6:
#line 758 "minic.y"
{ yyval.s = ps[2].val.s; }
		break;
	case 7:
#line 759 "minic.y"
{ yyval.s = mkstmt(Break, 0, 0, 0); }
		break;
	case 8:
#line 760 "minic.y"
{ yyval.s = mkstmt(Ret, ps[2].val.n, 0, 0); }
		break;
	case 9:
#line 761 "minic.y"
{ yyval.s = mkstmt(Expr, ps[1].val.n, 0, 0); }
		break;
	case 10:
#line 762 "minic.y"
{ yyval.s = mkstmt(While, ps[3].val.n, ps[5].val.s, 0); }
		break;
	case 11:
#line 763 "minic.y"
{ yyval.s = mkstmt(If, ps[3].val.n, ps[5].val.s, ps[7].val.s); }
		break;
	case 12:
#line 764 "minic.y"
{ yyval.s = mkstmt(If, ps[3].val.n, ps[5].val.s, 0); }
		break;
	case 13:
#line 766 "minic.y"
{ yyval.s = mkfor(ps[3].val.n, ps[5].val.n, ps[7].val.n, ps[9].val.s); }
		break;
	case 14:
#line 769 "minic.y"
{ yyval.s = mkstmt(Seq, ps[1].val.s, ps[2].val.s, 0); }
		break;
	case 15:
#line 770 "minic.y"
{ yyval.s = 0; }
		break;
	case 16:
#line 0 "minic.y"
		break;
	case 17:
#line 774 "minic.y"
{ yyval.n = mknode('=', ps[1].val.n, ps[3].val.n); }
		break;
	case 18:
#line 775 "minic.y"
{ yyval.n = mknode('+', ps[1].val.n, ps[3].val.n); }
		break;
	case 19:
#line 776 "minic.y"
{ yyval.n = mknode('-', ps[1].val.n, ps[3].val.n); }
		break;
	case 20:
#line 777 "minic.y"
{ yyval.n = mknode('*', ps[1].val.n, ps[3].val.n); }
		break;
	case 21:
#line 778 "minic.y"
{ yyval.n = mknode('/', ps[1].val.n, ps[3].val.n); }
		break;
	case 22:
#line 779 "minic.y"
{ yyval.n = mknode('%', ps[1].val.n, ps[3].val.n); }
		break;
	case 23:
#line 780 "minic.y"
{ yyval.n = mknode('<', ps[1].val.n, ps[3].val.n); }
		break;
	case 24:
#line 781 "minic.y"
{ yyval.n = mknode('<', ps[3].val.n, ps[1].val.n); }
		break;
	case 25:
#line 782 "minic.y"
{ yyval.n = mknode('l', ps[1].val.n, ps[3].val.n); }
		break;
	case 26:
#line 783 "minic.y"
{ yyval.n = mknode('l', ps[3].val.n, ps[1].val.n); }
		break;
	case 27:
#line 784 "minic.y"
{ yyval.n = mknode('e', ps[1].val.n, ps[3].val.n); }
		break;
	case 28:
#line 785 "minic.y"
{ yyval.n = mknode('n', ps[1].val.n, ps[3].val.n); }
		break;
	case 29:
#line 786 "minic.y"
{ yyval.n = mknode('&', ps[1].val.n, ps[3].val.n); }
		break;
	case 30:
#line 787 "minic.y"
{ yyval.n = mknode('a', ps[1].val.n, ps[3].val.n); }
		break;
	case 31:
#line 788 "minic.y"
{ yyval.n = mknode('o', ps[1].val.n, ps[3].val.n); }
		break;
	case 32:
#line 0 "minic.y"
		break;
	case 33:
#line 792 "minic.y"
{ yyval.n = 0; }
		break;
	case 34:
#line 0 "minic.y"
		break;
	case 35:
#line 796 "minic.y"
{ yyval.n = mkneg(ps[2].val.n); }
		break;
	case 36:
#line 797 "minic.y"
{ yyval.n = mknode('@', ps[2].val.n, 0); }
		break;
	case 37:
#line 798 "minic.y"
{ yyval.n = mknode('A', ps[2].val.n, 0); }
		break;
	case 38:
#line 0 "minic.y"
		break;
	case 39:
#line 0 "minic.y"
		break;
	case 40:
#line 0 "minic.y"
		break;
	case 41:
#line 804 "minic.y"
{ yyval.n = mknode('N', 0, 0); yyval.n->u.n = SIZE(ps[3].val.u); }
		break;
	case 42:
#line 805 "minic.y"
{ yyval.n = ps[2].val.n; }
		break;
	case 43:
#line 806 "minic.y"
{ yyval.n = mknode('C', ps[1].val.n, ps[3].val.n); }
		break;
	case 44:
#line 807 "minic.y"
{ yyval.n = mkidx(ps[1].val.n, ps[3].val.n); }
		break;
	case 45:
#line 808 "minic.y"
{ yyval.n = mknode('P', ps[1].val.n, 0); }
		break;
	case 46:
#line 809 "minic.y"
{ yyval.n = mknode('M', ps[1].val.n, 0); }
		break;
	case 47:
#line 0 "minic.y"
		break;
	case 48:
#line 813 "minic.y"
{ yyval.n = 0; }
		break;
	case 49:
#line 815 "minic.y"
{ yyval.n = mknode(0, ps[1].val.n, 0); }
		break;
	case 50:
#line 816 "minic.y"
{ yyval.n = mknode(0, ps[1].val.n, ps[3].val.n); }
		break;
	case 51:
#line 0 "minic.y"
		break;
	case 52:
#line 731 "minic.y"
{ yyval.n = 0; }
		break;
	case 53:
#line 733 "minic.y"
{ yyval.n = param(ps[2].val.n->u.v, ps[1].val.u, ps[4].val.n); }
		break;
	case 54:
#line 734 "minic.y"
{ yyval.n = param(ps[2].val.n->u.v, ps[1].val.u, 0); }
		break;
	case 55:
#line 0 "minic.y"
		break;
	case 56:
#line 0 "minic.y"
		break;
	case 57:
#line 0 "minic.y"
		break;
	case 58:
#line 0 "minic.y"
		break;
	case 59:
#line 693 "minic.y"
{
	if (!stmt(ps[5].val.s, -1))
		fprintf(of, "\tret 0\n");
	fprintf(of, "}\n\n");
}
		break;
	case 60:
#line 671 "minic.y"
{
	varadd(ps[2].val.n->u.v, 1, FUNC(ps[1].val.u));
}
		break;
	case 61:
#line 676 "minic.y"
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
	case 62:
#line 687 "minic.y"
{
	varclr();
	tmp = 0;
}
		break;
	case 63:
#line 700 "minic.y"
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
	case 64:
#line 0 "minic.y"
		break;
	case 65:
#line 739 "minic.y"
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
#line 819 "minic.y"


int
yylex()
{
	struct {
		char *s;
		int t;
	} kwds[] = {
		{ "void", TVOID },
		{ "int", TINT },
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

int
main()
{
	int i;

	of = stdout;
	nglo = 1;
	if (yyparse() != 0)
		die("parse error");
	for (i=1; i<nglo; i++)
		fprintf(of, "data $glo%d = %s\n", i, ini[i]);
	return 0;
}
