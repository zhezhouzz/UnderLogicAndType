JOBS ?= $(shell getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

all: Makefile.coq
	+$(MAKE) -j$(JOBS) -f Makefile.coq all

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	+$(MAKE) -j$(JOBS) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: all clean
