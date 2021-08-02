all: mydlpag

.PHONY: clean mydlpag

clean:
	rm -f *~ -r __pycache__
	dune clean

mydlpag:
	dune build bin/Main2.exe

install:
	dune build @install
	dune install

test:
	dune runtest

uninstall:
	dune uninstall
