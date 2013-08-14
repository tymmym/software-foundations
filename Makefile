VOFILES := Basics.vo Lists.vo Poly.vo Prop.vo

.PHONY: all clean

all: $(VOFILES)

clean:
	rm -f *.vo *.glob

%.vo: %.v
	coqc $*
