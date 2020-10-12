#!/bin/bash

tests="10000 100000 1000000 10000000"

for t in $tests; do
  echo "*********************"
  echo "$t"
  echo "*********************"

  ./isabelle/heapmap imp $t 5 | tee "$t.imp.log"
  # ./isabelle/heapmap fun $t 5 | tee "$t.fun.log"

  java -cp java/:java/stdlib.jar Test $t 5 | tee "$t.java.log"
done
