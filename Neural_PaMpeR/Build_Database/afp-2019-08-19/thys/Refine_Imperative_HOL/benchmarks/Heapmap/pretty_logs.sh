#!/bin/bash

tests="10000 100000 1000000 10000000"

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

