#!/bin/bash

tests="phils.4.0 phils.4.1 phils.5.0 phils.5.1 peterson.3.0 peterson.3.1 peterson.4.0 peterson.4.1"

# tests="peterson.4.1"
# tests="phils.4.0 phils.4.1"


for i in $tests; do

  echo '******************'
  echo $i
  echo '******************'

  name="ex/$i.states"
  
  for j in fun funs imp imps; do
    ./isabelle/NDFS_Benchmark $j < $name | tee "$i.$j.log"
  done

  ./c++/dfsO3 < $name | tee "$i.c++O3.log"
  ./c++/dfsO0 < $name | tee "$i.c++O0.log"
  
done
