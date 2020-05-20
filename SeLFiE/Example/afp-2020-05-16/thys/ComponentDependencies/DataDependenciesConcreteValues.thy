(*<*)
(*
   Title:  Theory  DataDependenciesConcreteValues.thy
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2014
*)
(*>*)

section "Case Study: Definitions"
 
theory DataDependenciesConcreteValues
  imports Main
begin

datatype CSet = sA1| sA2| sA3| sA4| sA5| sA6| sA7| sA8| sA9|
               sA11| sA12| sA21| sA22| sA23|  sA31| sA32| sA41| sA42|
               sA71| sA72| sA81| sA82| sA91| sA92| sA93|
               sS1| sS2| sS3| sS4| sS5| sS6| sS7| sS8| sS9| sS10| sS11|
               sS12 |sS13| sS14| sS15| sS1opt | sS4opt | sS7opt | sS11opt

datatype chanID = data1| data2| data3| data4| data5| data6| data7| 
data8| data9| data10| data11| data12| data13| data14| data15| 
data16| data17| data18| data19| data20| data21| data22| data23| data24

datatype varID = stA1 | stA2 | stA4 | stA6

datatype AbstrLevelsID = level0 | level1 | level2 | level3

\<comment> \<open>function IN maps component ID to the set of its input channels\<close>
fun IN ::  "CSet \<Rightarrow> chanID set"
where 
   "IN sA1 = { data1 }" 
| "IN sA2 = { data2, data3 }"
| "IN sA3 = { data4, data5 }"
| "IN sA4 = { data6, data7, data13 }"
| "IN sA5 = { data8 }"
| "IN sA6 = { data14 }"
| "IN sA7 = { data15, data16 }"
| "IN sA8 = { data17, data18, data19, data22 }"
| "IN sA9 = { data20, data21 }"
| "IN sA11 = { data1 }"
| "IN sA12 = { data1 }"
| "IN sA21 = { data2 }"
| "IN sA22 = { data2, data3 }"
| "IN sA23 = { data2 }"
| "IN sA31 = { data4 }"
| "IN sA32 = { data5 }"
| "IN sA41 = { data6, data7 }"
| "IN sA42 = { data13 }"
| "IN sA71 = { data15 }"
| "IN sA72 = { data16 }"
| "IN sA81 = { data17, data22 }"
| "IN sA82 = { data18, data19 }"
| "IN sA91 = { data20 }"
| "IN sA92 = { data20 }"
| "IN sA93 = { data21 }"
| "IN sS1 = { data1 }"
| "IN sS2 = { data1 }"
| "IN sS3 = { data2 }"
| "IN sS4 = { data2 }"
| "IN sS5 = { data5 }"
| "IN sS6 = { data2, data7 }"
| "IN sS7 = { data13 }"
| "IN sS8 = { data8 }"
| "IN sS9 = { data14 }"
| "IN sS10 = { data15 }"
| "IN sS11 = { data16 }"
| "IN sS12 = { data17}"
| "IN sS13= { data20 }" 
| "IN sS14 = { data18, data19 }"
| "IN sS15 = { data21 }"
| "IN sS1opt = { data1 }"
| "IN sS4opt = { data2 }"
| "IN sS7opt = { data13 }" 
| "IN sS11opt = { data16, data19 }" 

\<comment> \<open>function OUT maps component ID to the set of its output channels\<close>
fun OUT ::  "CSet \<Rightarrow> chanID set"
where 
   "OUT sA1 = { data2, data10 }" 
| "OUT sA2 = { data4, data5, data11, data12 }"
| "OUT sA3 = { data6, data7 }"
| "OUT sA4 = { data3, data8 }"
| "OUT sA5 = { data9 }"
| "OUT sA6 = { data15, data16 }"
| "OUT sA7 = { data17, data18 }"
| "OUT sA8 = { data20, data21 }"
| "OUT sA9 = { data22, data23, data24 }"
| "OUT sA11 = { data2 }"
| "OUT sA12= { data10 }"
| "OUT sA21 = { data11 }"
| "OUT sA22 = { data4, data12 }"
| "OUT sA23 = { data5 }"
| "OUT sA31= { data6 }"
| "OUT sA32 = { data7 }"
| "OUT sA41 = { data3 }"
| "OUT sA42 = { data8 }"
| "OUT sA71 = { data17 }"
| "OUT sA72 = { data18 }"
| "OUT sA81 = { data20 }"
| "OUT sA82 = { data21 }"
| "OUT sA91 = { data22 }"
| "OUT sA92 = { data23 }"
| "OUT sA93 = { data24 }"
| "OUT sS1 = { data10 }"
| "OUT sS2 = { data2 }"
| "OUT sS3 = { data11 }"
| "OUT sS4 = { data5 }"
| "OUT sS5 = { data7 }"
| "OUT sS6 = { data12 }"
| "OUT sS7 = { data8 }"
| "OUT sS8 = { data9 }"
| "OUT sS9 = { data15, data16 }"
| "OUT sS10 = { data17 }"
| "OUT sS11 = { data18 }"
| "OUT sS12 = { data20}"
| "OUT sS13= { data23 }" 
| "OUT sS14 = { data21 }"
| "OUT sS15 = { data24 }"
| "OUT sS1opt = { data2, data10 }"
| "OUT sS4opt = { data12 }"
| "OUT sS7opt = { data9 }"
| "OUT sS11opt = { data24 }"


\<comment> \<open>function VAR maps component IDs to the set of its local variables\<close>
fun VAR ::  "CSet \<Rightarrow> varID set"
where 
   "VAR sA1 = { stA1 }" 
| "VAR sA2 = { stA2 }"
| "VAR sA3 = {}"
| "VAR sA4 = { stA4 }"
| "VAR sA5 = {}"
| "VAR sA6 = { stA6 }"
| "VAR sA7 = {}"
| "VAR sA8 = {}"
| "VAR sA9 = {}"
| "VAR sA11 = {}"
| "VAR sA12 = { stA1 }"
| "VAR sA21 = {}"
| "VAR sA22 = { stA2 }"
| "VAR sA23 = {}"
| "VAR sA31 = {}"
| "VAR sA32 = {}"
| "VAR sA41 = {stA4 }"
| "VAR sA42 = {}"
| "VAR sA71 = {}"
| "VAR sA72 = {}"
| "VAR sA81 = {}"
| "VAR sA82 = {}"
| "VAR sA91 = {}"
| "VAR sA92 = {}"
| "VAR sA93 = {}"
| "VAR sS1 = { stA1 }"
| "VAR sS2 = {}"
| "VAR sS3 = {}"
| "VAR sS4 = {}"
| "VAR sS5 = {}"
| "VAR sS6 = {stA2, stA4}"
| "VAR sS7 = {}"
| "VAR sS8 = {}"
| "VAR sS9 = {stA6}"
| "VAR sS10 = {}"
| "VAR sS11 = {}"
| "VAR sS12 = {}"
| "VAR sS13 = {}"
| "VAR sS14 = {}"
| "VAR sS15 = {}"
| "VAR sS1opt = { stA1 }"
| "VAR sS4opt = { stA2, stA4 }"
| "VAR sS7opt = {}"
| "VAR sS11opt = {}"


\<comment> \<open>function subcomp maps component ID to the set of its subcomponents\<close>
fun subcomp ::  "CSet \<Rightarrow> CSet set"
where 
   "subcomp sA1 = { sA11, sA12 }" 
| "subcomp sA2 = { sA21, sA22, sA23 }"
| "subcomp sA3 = { sA31, sA32 }"
| "subcomp sA4 = { sA41, sA42 }"
| "subcomp sA5 = {}"
| "subcomp sA6 = {}"
| "subcomp sA7 = { sA71, sA72 }"
| "subcomp sA8 = { sA81, sA82 }"
| "subcomp sA9 = { sA91, sA92, sA93 }" 
| "subcomp sA11 = {}"
| "subcomp sA12 = {}"
| "subcomp sA21 = {}"
| "subcomp sA22 = {}"
| "subcomp sA23 = {}"
| "subcomp sA31 = {}"
| "subcomp sA32 = {}"
| "subcomp sA41 = {}"
| "subcomp sA42 = {}"
| "subcomp sA71 = {}"
| "subcomp sA72 = {}"
| "subcomp sA81 = {}"
| "subcomp sA82 = {}"
| "subcomp sA91 = {}"
| "subcomp sA92 = {}"
| "subcomp sA93 = {}"
| "subcomp sS1 = { sA12 }"
| "subcomp sS2 = { sA11 }"
| "subcomp sS3 = { sA21 }"
| "subcomp sS4 = { sA23 }"
| "subcomp sS5 = { sA32 }"
| "subcomp sS6 = { sA22, sA31, sA41 }"
| "subcomp sS7 = { sA42}"
| "subcomp sS8 = { sA5 }"
| "subcomp sS9 = { sA6 }"
| "subcomp sS10 = { sA71 }"
| "subcomp sS11 = { sA72 }"
| "subcomp sS12 = { sA81, sA91 }"
| "subcomp sS13 = { sA92 }"
| "subcomp sS14 = { sA82 }"
| "subcomp sS15 = { sA93 }"
| "subcomp sS1opt = { sA11, sA12 }"
| "subcomp sS4opt = { sA22, sA23, sA31, sA32, sA41 }"
| "subcomp sS7opt = { sA42, sA5 }"
| "subcomp sS11opt = { sA72, sA82, sA93 }"

\<comment> \<open>function AbstrLevel maps abstraction level ID to the corresponding set of components\<close>
axiomatization
  AbstrLevel ::  "AbstrLevelsID \<Rightarrow> CSet set"
where
AbstrLevel0:
"AbstrLevel level0 = {sA1, sA2, sA3, sA4, sA5, sA6, sA7, sA8, sA9}"
and
AbstrLevel1:
"AbstrLevel level1 = {sA11, sA12, sA21, sA22, sA23, sA31, sA32, 
 sA41, sA42, sA5, sA6, sA71, sA72, sA81, sA82, sA91, sA92, sA93}"
and
AbstrLevel2:
"AbstrLevel level2 = {sS1, sS2, sS3, sS4, sS5, sS6, sS7, sS8, 
                               sS9, sS10, sS11, sS12, sS13, sS14, sS15}"
and
AbstrLevel3:
"AbstrLevel level3 = {sS1opt, sS3, sS4opt, sS7opt, sS9, sS10, sS11opt, sS12, sS13 }"

\<comment> \<open>function VARfrom maps variable ID to the set of input channels it depends from\<close>
fun VARfrom :: "varID \<Rightarrow> chanID set"
where
   "VARfrom stA1 = {data1}"
| "VARfrom stA2 = {data3}"
| "VARfrom stA4 = {data6, data7}" 
| "VARfrom stA6 = {data14}" 

\<comment> \<open>function VARto maps variable ID to the set of output channels depending from this variable\<close>
fun VARto :: "varID \<Rightarrow> chanID set"
where
   "VARto stA1 = {data10}"
| "VARto stA2 = {data4, data12}"
| "VARto stA4 = {data3}" 
| "VARto stA6 = {data15, data16}" 

\<comment> \<open>function OUTfromCh maps channel ID to the set of input channels\<close>
\<comment> \<open>from which it depends derectly;\<close>
\<comment> \<open>an empty set means that the channel is either input of the system or\<close>
\<comment> \<open>its values are computed from local variables or are generated\<close>
\<comment> \<open>within some component independently\<close>
fun OUTfromCh ::  "chanID \<Rightarrow> chanID set"
where
   "OUTfromCh data1 = {}"
| "OUTfromCh data2 = {data1}"
| "OUTfromCh data3 = {}"
| "OUTfromCh data4 = {data2}"
| "OUTfromCh data5 = {data2}"
| "OUTfromCh data6 = {data4}"
| "OUTfromCh data7 = {data5}"
| "OUTfromCh data8 = {data13}"
| "OUTfromCh data9 = {data8}"
| "OUTfromCh data10 = {}"
| "OUTfromCh data11 = {data2}"
| "OUTfromCh data12 = {}"
| "OUTfromCh data13 = {}"
| "OUTfromCh data14 = {}"
| "OUTfromCh data15 = {}"
| "OUTfromCh data16 = {}"
| "OUTfromCh data17 = {data15}"
| "OUTfromCh data18 = {data16}"
| "OUTfromCh data19 = {}"
| "OUTfromCh data20 = {data17, data22}"
| "OUTfromCh data21 = {data18, data19}"
| "OUTfromCh data22 = {data20}"
| "OUTfromCh data23 = {data21}"
| "OUTfromCh data24 = {data20}"

\<comment> \<open>function OUTfromV maps channel ID to the set of local variables it depends from\<close>
fun OUTfromV ::  "chanID \<Rightarrow> varID set" 
where
   "OUTfromV data1 = {}"
| "OUTfromV data2 = {}"
| "OUTfromV data3 = {stA4}"
| "OUTfromV data4 = {stA2}"
| "OUTfromV data5 = {}"
| "OUTfromV data6 = {}"
| "OUTfromV data7 = {}"
| "OUTfromV data8 = {}"
| "OUTfromV data9 = {}"
| "OUTfromV data10 = {stA1}"
| "OUTfromV data11 = {}"
| "OUTfromV data12 = {stA2}"
| "OUTfromV data13 = {}"
| "OUTfromV data14 = {}"
| "OUTfromV data15 = {stA6}"
| "OUTfromV data16 = {stA6}"
| "OUTfromV data17 = {}"
| "OUTfromV data18 = {}"
| "OUTfromV data19 = {}"
| "OUTfromV data20 = {}"
| "OUTfromV data21 = {}"
| "OUTfromV data22 = {}"
| "OUTfromV data23 = {}"
| "OUTfromV data24 = {}"

\<comment> \<open>Set of channels channels which have  UplSize measure greather that the predifined value $HighLoad$\<close>
definition
   UplSizeHighLoad ::  "chanID set"
where
  "UplSizeHighLoad \<equiv> {data1, data4, data5, data6, data7, data8, data18, data21}"

\<comment> \<open>Set of components from the abstraction level 1 for which the Perf measure is greather that the predifined value $HighPerf$\<close>
definition
   HighPerfSet ::  "CSet set"
where
  "HighPerfSet \<equiv> {sA22, sA23, sA41, sA42, sA72, sA93}"

end
