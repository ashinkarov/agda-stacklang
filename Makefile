SRC := paper.tex

# Artem uses custom version of Agda, so this Makefile is
# conditionalised bases on the name of the machine.
ifeq ($(shell uname -n),temanbk)
  AGDA := /home/tema/.cabal/bin/agda
else
  AGDA := agda
endif

all: paper.pdf


.PHONY: paper.tex
#paper.tex : latex/background.tex latex/kaleidoskope.tex latex/arraylang.tex \
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
