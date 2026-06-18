MAIN = main
ABSTRACT = abstract
OUTDIR = build

TEX = pdflatex
BIBER = biber

FLAGS = -interaction=nonstopmode -output-directory=$(OUTDIR)

all: poster abstract

abstract:

	$(TEX) $(FLAGS) $(ABSTRACT).tex
	$(BIBER) $(OUTDIR)/$(ABSTRACT)
	$(TEX) $(FLAGS) $(ABSTRACT).tex
	$(TEX) $(FLAGS) $(ABSTRACT).tex

poster:
	latexmk -pdflatex='lualatex -interaction nonstopmode' -pdf main.tex


clean:
	latexmk -pdf -C
	rm -rf $(OUTDIR)/*

