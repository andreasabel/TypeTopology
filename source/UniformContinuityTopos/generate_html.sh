#!/bin/bash

echo "Running markdownify.sh"

for file in `ls *.lagda`; do
    echo "Writing $(basename $file .lagda).lagda.md..."
    cat $file | python3 markdownify.py > $(basename $file .lagda).lagda.md
done

for file in `ls *.lagda`; do
	echo "Hiding $file..."
	mv $file ".$file"
done

agda --html --html-highlight=auto --css="Agda.css" index.lagda.md

echo "Copying Agda.css into `html`..."

cp Agda.css html/Agda.css

echo "Running pandoc..."


cd html

for file in `ls *.md`; do
	cat $file | pandoc -s --from=markdown --to=html --css Agda.css --toc -o "$(basename -s '.md' $file).html"
done

cd ..

for file in `ls -d .* | grep lagda`; do
	echo "Unhiding $file..."
	mv $file $(echo $file | cut -c 2-)
done

rm -rf *.lagda.md
