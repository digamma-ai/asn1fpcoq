GCC = gcc
CFLAGS = -g -Wall
DEPS = $(shell ocamlc -where)

asn1fp: asn1fp.o
	$(GCC) $? $(CFLAGS) -o $@ -L$(DEPS) -I$(DEPS)

.c.o:
	$(CC) $(CFLAGS) -c $< -L$(DEPS) -I$(DEPS)