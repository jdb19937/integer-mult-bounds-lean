.PHONY: all clean

all: pr589-hole.pdf

# two passes so cross-references and hyperlinks resolve
%.pdf: %.tex
	pdflatex -interaction=nonstopmode $<
	pdflatex -interaction=nonstopmode $<

clean:
	rm -f *.aux *.log *.out *.toc
