default: thesis.pdf

thesis.tex: thesis.lhs
	lhs2TeX -o thesis.tex thesis.lhs

thesis.pdf: thesis.tex
	pdflatex thesis.tex
	pdflatex thesis.tex
	pdflatex thesis.tex
