vfiles=$(shell ls *.v)

all: $(vfiles:.v=.vo)

%.vo:%.v
	coqc $<

clean:
	rm -f *.vo *.glob .*.aux .lia.cache .nia.cache
