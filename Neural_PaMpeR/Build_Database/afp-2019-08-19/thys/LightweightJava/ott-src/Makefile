OTT=ott
PDFLATEX=pdflatex
OTT_SRC_FILES=lj_common.ott lj_base.ott lj.ott
ISA_TARGET=Lightweight_Java_Definition.thy

lj.pdf: lj.tex lj_included.tex
	$(PDFLATEX) lj.tex

lj_included.tex $(ISA_TARGET): $(OTT_SRC_FILES)
	$(OTT) -tex_wrap false -isabelle_inductive true \
	       -merge true -o lj_included.tex -o $(ISA_TARGET) \
               lj_common.ott lj_base.ott lj.ott

.PHONY: clean

clean:
	rm -f lj.{aux,log,pdf} lj_included.{aux,tex} $(ISA_TARGET)
