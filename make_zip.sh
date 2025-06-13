#!/bin/sh
cp .github/README.md .
zip -r mechanization.zip _CoqProject gen_makefile.sh stdsharp.v syntax.v syntax_instances.v theory.v README.md
rm README.md