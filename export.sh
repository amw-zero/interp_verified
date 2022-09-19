/Applications/Isabelle2021-1.app/bin/isabelle export -x "*:**" -d . bexp
mv export/bexp.BoolExp/code/*.ocaml bexp_ocaml/lib/
for file in bexp_ocaml/lib/*.ocaml; do 
    mv -- "$file" "${file%.ocaml}.ml"
done
