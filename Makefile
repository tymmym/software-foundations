VOFILES := Basics.vo Induction.vo Lists.vo Poly.vo MoreCoq.vo Prop.vo \
           MoreProp.vo Logic.vo Imp.vo

.PHONY: all clean

all: $(VOFILES)

clean:
	rm -f *.vo *.glob

%.vo: %.v
	coqc $*
