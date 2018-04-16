cd ./$1

find . -name "infer\.log" | xargs rm
find . -name "*\.jaif" | xargs rm
find . -name "*\.class" | xargs rm
