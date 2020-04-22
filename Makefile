.PHONY: build html install clean

build:
	export HOME=`pwd`; dune build @install

install: build
	dune install

html: build
	./configure.sh
	make -f Makefile.coq html

clean:
	rm -rf _build || true
	rm -rf html || true
	rm theories/*.vo theories/*/*.vo || true
	rm theories/*.glob theories/*/*.glob || true
	rm theories/*.aux theories/*/*.aux || true

