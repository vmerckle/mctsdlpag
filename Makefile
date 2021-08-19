all: main

.PHONY: clean main install test uninstall

main:
	dune build bin/Main.exe

run:
	make install
	mctsdlpag encodings/stupid.pa

install:
	dune build @install
	dune install

test:
	dune runtest

uninstall:
	dune uninstall

clean:
	dune clean
