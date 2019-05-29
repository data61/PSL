#!/bin/bash

smt_names=(
prop_01  prop_07  prop_13  prop_19  prop_25  prop_31  prop_37  prop_43  prop_49
prop_02  prop_08  prop_14  prop_20  prop_26  prop_32  prop_38  prop_44  prop_50
prop_03  prop_09  prop_15  prop_21  prop_27  prop_33  prop_39  prop_45
prop_04  prop_10  prop_16  prop_22  prop_28  prop_34  prop_40  prop_46
prop_05  prop_11  prop_17  prop_23  prop_29  prop_35  prop_41  prop_47
prop_06  prop_12  prop_18  prop_24  prop_30  prop_36  prop_42  prop_48
)

mkdir Prod
for smt in ${smt_names[*]}
do
  comm=("tip benchmarks/benchmarks/prod/"$smt".smt2 --isabelle ")
  echo $comm
  $comm  > Prod/TIP_$smt.thy
done

for smt in ${smt_names[*]}
do
  sed -i '1s/.*/theory TIP_'$smt'/' Prod/TIP_$smt.thy 
  $comm
done
