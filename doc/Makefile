default: draft.pdf thesis.pdf abstract.pdf

%.tex: %.lhs
	lhs2TeX -o $@ $<

draft.pdf: draft.tex references.bib
	pdflatex draft.tex
	bibtex draft.aux
	pdflatex draft.tex
	pdflatex draft.tex

abstract.pdf: abstract.tex references.bib plots
	pdflatex abstract.tex
	bibtex abstract.aux
	pdflatex abstract.tex
	pdflatex abstract.tex

thesis.pdf: thesis.tex references.bib plots
	cd plots; make
	xelatex thesis.tex
	bibtex thesis.aux
	xelatex thesis.tex
	xelatex thesis.tex

clean:
	rm -f *.aux *.bbl *.blg *.log *.pdf *.ptb *.tex *.toc
