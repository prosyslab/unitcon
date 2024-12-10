MAKE=@make
DUNE=@dune
LN=@ln -sf
RM=@rm
EXE=unitcon

all:
	$(DUNE) build src/main.exe
	$(LN) _build/default/src/main.exe $(EXE)

fmt:
	$(DUNE) build @fmt --auto-promote

test-unitcon: all
	./run.sh

profile:
	$(DUNE) build --instrument-with landmarks src/main.exe
	$(LN) _build/default/src/main.exe $(EXE)

coverage:
	rsync -a unitcon-infer _build/default/
	$(DUNE) runtest ./test

clean:
	$(DUNE) clean
	$(RM) -rf $(EXE)
