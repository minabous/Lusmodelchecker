#!/bin/bash
# Based on file generated by ocamlbuild

# Clear all backup files from Emacs
cd .
rm -f --preserve-root *.*~
rm -f --preserve-root *#*.*#

cd ../examples/
rm -f --preserve-root *.*~
rm -f --preserve-root *#*.*#

# Also clean the script itself Optionel
# rm -f /home/stephane/Documents/Ocaml/Chapter2/_build/sanitize.sh
