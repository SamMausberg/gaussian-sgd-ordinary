#!/bin/sh
# Builds main.pdf from main.tex.
set -eu
cd "$(dirname "$0")"
for i in 1 2 3; do pdflatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null; done
grep -c "Overfull" main.log || true
