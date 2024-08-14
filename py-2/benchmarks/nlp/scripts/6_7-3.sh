# modified for agg. (split into 3 scripts)
cat $1 | grep 'light.\*light' | grep -vc 'light.\*light.\*light'
