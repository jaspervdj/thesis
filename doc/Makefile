default: draft.pdf thesis.pdf

%.tex: %.lhs
	lhs2TeX -o $@ $<

draft.pdf: draft.tex references.bib
	pdflatex draft.tex
	bibtex draft.aux
	pdflatex draft.tex
	pdflatex draft.tex

thesis.pdf: thesis.tex references.bib
	xelatex thesis.tex
	bibtex thesis.aux
	xelatex thesis.tex
	xelatex thesis.tex

clean:
	rm -f *.aux *.bbl *.blg *.log *.pdf *.ptb *.tex *.toc
