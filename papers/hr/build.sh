#!/bin/sh
# Builds main.pdf from the LaTeX sources in this directory with three pdflatex passes
# (the later passes resolve cross-references and the table of contents).
# Requires a TeX distribution with pdflatex (built here with TeX Live 2026).
cd "$(dirname "$0")" || exit 1
for pass in 1 2 3; do
  pdflatex -interaction=batchmode main.tex || { echo "pdflatex pass $pass failed; see main.log" >&2; exit 1; }
done
grep 'Output written on' main.log
