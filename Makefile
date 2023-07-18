paper/paper.pdf: paper/paper.tex
	(cd paper; latexmk -pdf -interaction=nonstopmode paper.tex)

arxiv.tar.gz: paper/paper.pdf
	(cd paper; tar czf ../arxiv.tar.gz paper.tex paper.bbl)
