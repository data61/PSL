#!/bin/bash

tests="cl1300 cl1500 medium large"

langs="fun imp java"

echo -ne "name  \t& "
for l in $langs; do echo -ne "$l\t& "; done
echo ""

for t in $tests; do
  echo -ne "$t\t& "
  for l in $langs; do
    log="$t.$l.log"
    time=`grep "Time:" $log | sed -re 's/.*Time: //g;s/ms//g'`
    echo -ne "$time\t& "
  done
  echo "\\\\"
done

