#!/bin/bash

echo "Running Agda..."

echo "Running markdownify.sh"

for file in `ls *.lagda`; do
    echo "Writing $(basename $file .lagda).lagda.md..."
    cat $file | ./markdownify.sh > $(basename $file .lagda).lagda.md
done

./hide_lagda.sh

agda --html --html-highlight=auto --css="Agda.css" UniformContinuityMonoid.lagda.md
agda --html --html-highlight=auto --css="Agda.css" Sheaf.lagda.md

echo "Running pandoc..."

echo "Copying Agda.css into `html`..."

cp Agda.css html/Agda.css

cd html

for file in `ls *.md`; do
	cat $file | pandoc -s --from=markdown --to=html --css Agda.css --toc -o "$(basename $file).html"
done

cd ..

./unhide_lagda.sh

rm -rf *.lagda.md
