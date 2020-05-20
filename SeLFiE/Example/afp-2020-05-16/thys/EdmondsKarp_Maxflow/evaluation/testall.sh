#!/bin/bash

tests=`cat tests`
platforms=`cat platforms`

for t in $tests; do
  echo "*********************"
  echo "$t"
  echo "*********************"

  name="../data/samples/g-$t.txt"

  for platform in $platforms; do
    echo "##### $platform"
    cd "fofu-$platform"
    ./run $name | tee "$t.$platform.log" | grep "^@@@"
    cd ..
  done
done
