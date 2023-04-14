.PHONY: all
all: report.pdf

report.pdf: report.md bibliography.bib
	pandoc --csl report/acm.csl report.md --bibliography bibliography.bib -d defaults.yaml -o report.pdf

.PHONY: clean
clean:
	rm -f report.pdf
