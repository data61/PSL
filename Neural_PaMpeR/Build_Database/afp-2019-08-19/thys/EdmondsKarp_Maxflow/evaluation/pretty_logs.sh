#!/bin/bash

tests=`cat tests`
platforms=`cat platforms`

tabs -12
echo -ne "name \t& "
for p in $platforms; do echo -ne "$p\t& "; done
echo ""

for t in $tests; do
  echo -ne "$t\t& "
  for p in $platforms; do
    log="fofu-$p/$t.$p.log"
    time=`grep "@@@time:" $log | sed -re 's/.*@@@time: //g;s/ms//g'`
    echo -ne "$time\t& "
  done
  echo "\\\\"
done

