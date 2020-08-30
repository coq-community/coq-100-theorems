vfiles=$(shell ls *.v)

all: $(vfiles:.v=.vo)

%.vo:%.v
	coqc $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux .lia.cache .nia.cache
