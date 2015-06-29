PROJECT_NAME=coq-ext-refine

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

uninstall:
	$(MAKE) -C theories uninstall


dist:
	@ git archive --prefix coq-ext-lib/ HEAD -o $(PROJECT_NAME).tgz

.PHONY: all clean dist theories examples
