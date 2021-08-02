all: dlpag

.PHONY: clean dlpag mydlpag

clean:
	rm -f *~ -r __pycache__
	dune clean

dlpag:
	dune build bin/Dlpag.exe

mydlpag:
	dune build bin/Main2.exe

install:
	dune build @install
	dune install

test:
	dune runtest

uninstall:
	dune uninstall


errorfile:
	menhir --list-errors lib/Parser.mly > lib/Parser.messages
