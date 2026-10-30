.PHONY: all clean

all: main.pdf

main.pdf: main.tex references.bib lipics-v2021.cls
	pdflatex -interaction=nonstopmode main.tex
	bibtex main
	pdflatex -interaction=nonstopmode main.tex
	pdflatex -interaction=nonstopmode main.tex

clean:
	rm -f main.aux main.bbl main.blg main.log main.out main.vtc
