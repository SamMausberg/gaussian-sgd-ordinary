#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error ordinary_dimension.tex
pdflatex -interaction=nonstopmode -halt-on-error ordinary_dimension.tex
