BIN = minic

CFLAGS += -g -Wall

$(BIN): yacc minic.y
	./yacc minic.y
	$(CC) $(CFLAGS) -o $@ y.tab.c

minicf: yacc minicf.y
	./yacc minicf.y
	$(CC) $(CFLAGS) -o $@ y.tab.c

clean:
	rm -f yacc minic minicf y.*

.PHONY: clean