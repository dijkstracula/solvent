.PHONY: all
all: report.pdf

report.pdf: report.md bibliography.bib defaults.yaml
	pandoc --csl report/acm.csl report.md --bibliography bibliography.bib -d defaults.yaml -o report.pdf

.PHONY: clean
clean:
	rm -f report.pdf
