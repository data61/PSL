#!/bin/bash

FILES=./Isaplanner/*.thy

for f in $FILES
do
  echo -e "(* Property from Case-Analysis for Rippling and Inductive Proof, \n\
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. \n\
   This Isabelle theory is produced using the TIP tool offered at the following website: \n\
     https://github.com/tip-org/tools \n\
   This file was originally provided as part of TIP benchmark at the following website:\n\
     https://github.com/tip-org/benchmarks \n\
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)\n\
  $(cat $f)" > $f
done
