default: draft.pdf

draft.tex: draft.lhs
	lhs2TeX -o $@ $<

draft.pdf: draft.tex
	pdflatex $<
	pdflatex $<
	pdflatex $<
