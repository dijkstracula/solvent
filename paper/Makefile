.PHONY: all
all: report.html

PANDOCARGS=--csl report/acm.csl --bibliography bibliography.bib -d defaults.yaml --embed-resources --standalone

report.html: report.md bibliography.bib defaults.yaml pandoc.css
	pandoc report.md $(PANDOCARGS) -o report.html

.PHONY: clean
clean:
	rm -f report.html
