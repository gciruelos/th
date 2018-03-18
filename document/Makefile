
PDFLATEX = pdflatex

SRC=$(wildcard *.tex)

.PHONY = view clean debug

main.pdf: $(SRC)
	-${PDFLATEX} -interaction=nonstopmode main
	-bibtex main
	-${PDFLATEX} -interaction=nonstopmode main
	-${PDFLATEX} -interaction=nonstopmode main


stopmode:
	-${PDFLATEX} main

view: main.pdf $(SRC)
	zathura main.pdf &

debug: PDFLATEX=pplatex
debug: main.pdf

clean:
	rm -f *.aux
	rm -f *.nav
	rm -f *.snm
	rm -f *.toc
	rm -f *.log
	rm -f *.out
	rm -f *.brf
	rm -f *.pdf
