VS=$(wildcard *.v)
VOS=$(VS:.v=.vo)
GLOBS=$(VS:.v=.glob)

all: $(VOS)
clean:
	rm -f $(VOS) $(GLOBS)

%.vo: %.v
	coqc $<
