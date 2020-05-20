#!/bin/bash

tests="phils.4.0 phils.4.1 phils.5.0 phils.5.1 peterson.3.0 peterson.3.1 peterson.4.0 peterson.4.1"

langs="fun funs imp imps c++O0 c++O3"

echo -ne "        \t& states  \t&"
for l in $langs; do echo -ne "$l\t& "; done
echo ""

for t in $tests; do
  statefile="ex/$t.states"
  numstates=`gawk '{print; exit}' < $statefile`

  echo -ne "$t\t& $numstates \t&"
  for l in $langs; do
    log="$t.$l.log"
    time=`grep "Time:" $log | sed -re 's/.*Time: //g;s/ms//g'`
    echo -ne "$time\t& "
  done
  echo "\\\\"
done

