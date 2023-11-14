paper/paper.pdf: paper/paper.tex paper/bibliography.bib
	(cd paper; latexmk -pdf -interaction=nonstopmode paper.tex)

paper/paper-extended.pdf: paper/paper-extended.tex paper/appendix-rules.tex paper/bibliography.bib
	(cd paper; latexmk -pdf -interaction=nonstopmode paper-extended.tex)

arxiv.tar.gz: paper/paper-extended.pdf
	(cd paper; tar czf ../arxiv.tar.gz paper-extended.tex paper-extended.bbl acmart.cls appendix-rules.tex)

paper-src.zip: paper/paper.pdf paper/acmart.cls
	(cd paper; zip ../paper-src.zip paper.tex paper.bbl acmart.cls)
