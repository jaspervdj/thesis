default: draft.pdf

draft.tex: draft.lhs
	lhs2TeX -o $@ $<

draft.pdf: draft.tex references.bib
	pdflatex draft.tex
	bibtex draft.aux
	pdflatex draft.tex
	pdflatex draft.tex
