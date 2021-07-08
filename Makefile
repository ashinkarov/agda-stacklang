SRC := paper.tex \
	   paper.bib

# Artem uses custom version of Agda, so this Makefile is
# conditionalised bases on the name of the machine.
ifeq ($(shell uname -n),temanbk)
  ifeq ($(uname -v | grep "NixOS" >/dev/null && echo yes),yes)
  	AGDA := /home/tema/.local/bin/agda
  else
  	AGDA := /home/tema/.cabal/bin/agda
  endif
else
  AGDA := agda
endif

all: paper.pdf


.PHONY: paper.tex
paper.tex : latex/background.tex latex/psembedding.tex latex/extraction.tex latex/reduction.tex # latex/arraylang.tex \
#	    latex/aplcnn.tex latex/related.tex

latex/%.tex : %.lagda
	$(AGDA) -i. --latex $< #--only-scope-checking $<

paper.pdf: $(SRC)
	TEXINPUTS=./latex:$$TEXINPUTS latexmk -pdf -f -pdflatex='xelatex -halt-on-error' $<
	#bibtex $(patsubst %.tex,%,$<) && \
	#TEXINPUTS=./latex:$$TEXINPUTS xelatex $< ;\
	#TEXINPUTS=./latex:$$TEXINPUTS xelatex $< ;\

clean:
	$(RM) *.aux *.log *.out *.vrb paper.pdf \
              *.bbl *.blg *.fdb_latexmk *.toc *.fls *.cut \
              latex/*.tex latex/*.aux *.agdai
