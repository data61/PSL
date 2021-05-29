#!/bin/bash

FILES=./TIP15/*.thy

for f in $FILES
do
  echo -e "(* This Isabelle theory is produced using the TIP tool offered at the following website: \n\
     https://github.com/tip-org/tools \n\
   This file was originally provided as part of TIP benchmark at the following website:\n\
     https://github.com/tip-org/benchmarks \n\
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.\n\:w
   Some proofs were added by Yutaka Nagashima.*)\n\
  $(cat $f)" > $f
done
