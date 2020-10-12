#!/bin/bash

echo "Compiling Java Dijkstra"
cd "java"
javac -cp "stdlib.jar:." DijkstraSP.java
cd ..

echo "Compiling ML Dijkstra"
cd "isabelle"
./build
cd ..

echo "Fetching Examples. ~360MiB, may take a while"
mkdir -p ex
cd ex
files="cl1300EWD.txt cl1500EWD.txt largeEWD.txt mediumEWD.txt tinyEWD.txt"
for f in $files; do
  test -f $f || wget "http://www21.in.tum.de/~lammich/refine_imp_hol/ex/$f"
done

cd ..
