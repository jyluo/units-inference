cd ./$1

find . -name "infer\.log" | xargs rm
find . -name "*\.jaif" | xargs rm
find . -name "*\.class" | xargs rm
find . -name "statistic.txt" | xargs rm
find . -name "solutions.txt" | xargs rm
