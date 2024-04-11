MAKE=@make
DUNE=@dune
LN=@ln -sf
RM=@rm
BISECT=@bisect-ppx-report
EXE=unitcon

all:
	$(DUNE) build src/main.exe
	$(LN) _build/default/src/main.exe $(EXE)

fmt:
	$(DUNE) build @fmt --auto-promote

test: all
	$(DUNE) test

coverage:
	$(DUNE) runtest --instrument-with bisect_ppx --force
	$(BISECT) html
	$(BISECT) summary

clean:
	$(DUNE) clean
	$(RM) -rf $(EXE)
