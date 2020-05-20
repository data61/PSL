#!/bin/bash

tests="cl1300 cl1500 medium large"

for t in $tests; do
  echo "*********************"
  echo "$t"
  echo "*********************"

  name="ex/${t}EWD.txt"
  
  for m in fun imp; do
    ./isabelle/dijkstra $m 5 < $name | tee "$t.$m.log"
  done

  java -cp java/stdlib.jar:java/ DijkstraSP $name 0 5 | tee "$t.java.log"
done
