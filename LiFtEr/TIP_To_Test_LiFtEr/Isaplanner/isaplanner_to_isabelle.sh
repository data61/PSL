#!/bin/bash

smt_names=(
prop_01  prop_11  prop_21  prop_31  prop_41  prop_51  prop_61  prop_71  prop_81
prop_02  prop_12  prop_22  prop_32  prop_42  prop_52  prop_62  prop_72  prop_82
prop_03  prop_13  prop_23  prop_33  prop_43  prop_53  prop_63  prop_73  prop_83
prop_04  prop_14  prop_24  prop_34  prop_44  prop_54  prop_64  prop_74  prop_84
prop_05  prop_15  prop_25  prop_35  prop_45  prop_55  prop_65  prop_75  prop_85
prop_06  prop_16  prop_26  prop_36  prop_46  prop_56  prop_66  prop_76  prop_86
prop_07  prop_17  prop_27  prop_37  prop_47  prop_57  prop_67  prop_77  
prop_08  prop_18  prop_28  prop_38  prop_48  prop_58  prop_68  prop_78  
prop_09  prop_19  prop_29  prop_39  prop_49  prop_59  prop_69  prop_79  
prop_10  prop_20  prop_30  prop_40  prop_50  prop_60  prop_70  prop_80 
)

mkdir Isaplanner
for smt in ${smt_names[*]}
do
  comm=("tip ../benchmarks/benchmarks/isaplanner/"$smt".smt2 --isabelle ")
  echo $comm
  $comm  > Isaplanner/TIP_$smt.thy
done

for smt in ${smt_names[*]}
do
  sed -i '1s/.*/theory TIP_'$smt'/' Isaplanner/TIP_$smt.thy 
  sed -i '2s/.*/imports \"..\/..\/Test_Base\"/' Isaplanner/TIP_$smt.thy
done
