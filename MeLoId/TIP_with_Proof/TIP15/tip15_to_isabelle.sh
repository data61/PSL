#!/bin/bash

smt_names=(
bin_distrib                   nat_max_assoc                  sort_nat_NStoogeSort2Sorts
bin_nat_distrib               nat_max_comm                   sort_nat_NStoogeSortCount
bin_nat_plus_assoc            nat_max_idem                   sort_nat_NStoogeSortIsSort
bin_nat_plus_comm             nat_min_max_abs                sort_nat_NStoogeSortPermutes
bin_nat_plus                  nat_min_max_distrib            sort_nat_NStoogeSortSorts
bin_nat_s                     nat_pow_le_factorial           sort_nat_QSortCount
bin_nat_times_assoc           nat_pow_one                    sort_nat_QSortIsSort
bin_nat_times_comm            nat_pow_pow                    sort_nat_QSortPermutes
bin_nat_times                 nat_pow_times                  sort_nat_QSortSorts
bin_plus_assoc                nicomachus_theorem             sort_nat_SSortCount
bin_plus_comm                 polyrec_seq_index              sort_nat_SSortIsSort
bin_plus                      propositional_AndCommutative   sort_nat_SSortPermutes
bin_s                         propositional_AndIdempotent    sort_nat_SSortSorts
bin_times_assoc               propositional_AndImplication   sort_nat_StoogeSort2Count
bin_times_comm                propositional_Okay             sort_nat_StoogeSort2IsSort
bin_times                     propositional_Sound            sort_nat_StoogeSort2Permutes
escape_Injective              regexp_Deeps                   sort_nat_StoogeSort2Sorts
escape_NoSpecial              regexp_PlusAssociative         sort_nat_StoogeSortCount
fermat_last                   regexp_PlusCommutative         sort_nat_StoogeSortIsSort
int_add_assoc                 regexp_PlusIdempotent          sort_nat_StoogeSortPermutes
int_add_comm                  regexp_RecAtom                 sort_nat_StoogeSortSorts
int_add_ident_left            regexp_RecEps                  sort_nat_TSortCount
int_add_ident_right           regexp_RecNil                  sort_nat_TSortIsSort
int_add_inv_left              regexp_RecPlus                 sort_nat_TSortPermutes
int_add_inv_right             regexp_RecSeq                  sort_nat_TSortSorts
int_left_distrib              regexp_RecStar                 sort_NMSortTDCount
int_mul_assoc                 regexp_Reverse                 sort_NMSortTDIsSort
int_mul_comm                  regexp_SeqAssociative          sort_NMSortTDPermutes
int_mul_ident_left            regexp_SeqDistrPlus            sort_NMSortTDSorts
int_mul_ident_right           regexp_Star                    sort_NStoogeSort2Count
int_right_distrib             relaxedprefix_correct          sort_NStoogeSort2IsSort
list_append_inj_1             relaxedprefix_is_prefix_1      sort_NStoogeSort2Permutes
list_append_inj_2             relaxedprefix_is_prefix_2      sort_NStoogeSort2Sorts
list_assoc                    relaxedprefix_is_prefix_3      sort_NStoogeSortCount
list_concat_map_bind          relaxedprefix_is_prefix_4      sort_NStoogeSortIsSort
list_count_nub                rotate_mod                     sort_NStoogeSortPermutes
list_deleteAll_count          rotate_self                    sort_NStoogeSortSorts
list_elem_map                 rotate_snoc_self               sort_QSortCount
list_elem_nub_l               rotate_snoc                    sort_QSortIsSort
list_elem_nub_r               rotate_structural_mod          sort_QSortPermutes
list_elem                     sort_BSortCount                sort_QSortSorts
list_Interleave               sort_BSortIsSort               sort_SSortCount
list_nat_append_inj_1         sort_BSortPermutes             sort_SSortIsSort
list_nat_append_inj_2         sort_BSortSorts                sort_SSortPermutes
list_nat_count_nub            sort_BubSortCount              sort_SSortSorts
list_nat_deleteAll_count      sort_BubSortIsSort             sort_StoogeSort2Count
list_nat_elem_map             sort_BubSortPermutes           sort_StoogeSort2IsSort
list_nat_elem_nub_l           sort_BubSortSorts              sort_StoogeSort2Permutes
list_nat_elem_nub_r           sort_HSort2Count               sort_StoogeSort2Sorts
list_nat_elem                 sort_HSort2IsSort              sort_StoogeSortCount
list_nat_Interleave           sort_HSort2Permutes            sort_StoogeSortIsSort
list_nat_nub_nub              sort_HSort2Sorts               sort_StoogeSortPermutes
list_nat_PairEvens            sort_HSortCount                sort_StoogeSortSorts
list_nat_PairOdds             sort_HSortIsSort               sort_TSortCount
list_nat_PairUnpair           sort_HSortPermutes             sort_TSortIsSort
list_nat_perm_elem            sort_HSortSorts                sort_TSortPermutes
list_nat_perm_refl            sort_ISortCount                sort_TSortSorts
list_nat_perm_symm            sort_ISortPermutes             subst_SubstFreeNo
list_nat_perm_trans           sort_ISortSorts                subst_SubstFreeYes
list_nat_SelectPermutations   sort_MSortBU2Count             tree_Flatten1List
#list_nat_SelectPermutations'  
sort_MSortBU2IsSort            tree_Flatten1
list_nat_Select               sort_MSortBU2Permutes          tree_Flatten2
list_nub_nub                  sort_MSortBU2Sorts             tree_Flatten3
list_PairEvens                sort_MSortBUCount              tree_SwapAB
list_PairOdds                 sort_MSortBUIsSort             weird_nat_add3acc_assoc1
list_PairUnpair               sort_MSortBUPermutes           weird_nat_add3acc_assoc2
list_perm_elem                sort_MSortBUSorts              weird_nat_add3acc_assoc3
list_perm_refl                sort_MSortTDCount              weird_nat_add3acc_comm12
list_perm_symm                sort_MSortTDIsSort             weird_nat_add3acc_comm13
list_perm_trans               sort_MSortTDPermutes           weird_nat_add3acc_comm23
list_return_1                 sort_MSortTDSorts              weird_nat_add3acc_rot
list_return_2                 sort_nat_BSortCount            weird_nat_add3acc_rrot
list_SelectPermutations       sort_nat_BSortIsSort           weird_nat_add3acc_spec
#list_SelectPermutations'      
sort_nat_BSortPermutes         weird_nat_add3_assoc1
list_Select                   sort_nat_BSortSorts            weird_nat_add3_assoc2
list_weird_concat_map_bind    sort_nat_BubSortCount          weird_nat_add3_assoc3
list_weird_is_normal          sort_nat_BubSortIsSort         weird_nat_add3_comm12
mccarthy91_M1                 sort_nat_BubSortPermutes       weird_nat_add3_comm13
mccarthy91_M2                 sort_nat_BubSortSorts          weird_nat_add3_comm23
mod_same                      sort_nat_HSort2Count           weird_nat_add3_rot
nat_acc_alt_mul_assoc         sort_nat_HSort2IsSort          weird_nat_add3_rrot
nat_acc_alt_mul_comm          sort_nat_HSort2Permutes        weird_nat_add3_same
nat_acc_alt_mul_same          sort_nat_HSort2Sorts           weird_nat_add3_spec
nat_acc_plus_assoc            sort_nat_HSortCount            weird_nat_mul2_assoc
nat_acc_plus_comm             sort_nat_HSortIsSort           weird_nat_mul2_comm
nat_acc_plus_same             sort_nat_HSortPermutes         weird_nat_mul3acc_assoc1
nat_alt_mul_assoc             sort_nat_HSortSorts            weird_nat_mul3acc_assoc2
nat_alt_mul_comm              sort_nat_ISortCount            weird_nat_mul3acc_assoc3
nat_alt_mul_same              sort_nat_ISortPermutes         weird_nat_mul3acc_comm12
nat_boring_ge_antisym         sort_nat_ISortSorts            weird_nat_mul3acc_comm13
nat_boring_ge_reflexive       sort_nat_MSortBU2Count         weird_nat_mul3acc_comm23
nat_boring_ge_trans           sort_nat_MSortBU2IsSort        weird_nat_mul3acc_rot
nat_boring_gt_asymmetric      sort_nat_MSortBU2Permutes      weird_nat_mul3acc_rrot
nat_boring_gt_irreflexive     sort_nat_MSortBU2Sorts         weird_nat_mul3acc_spec
nat_boring_gt_trans           sort_nat_MSortBUCount          weird_nat_mul3_assoc1
nat_boring_max_min_abs        sort_nat_MSortBUIsSort         weird_nat_mul3_assoc2
nat_boring_max_min_distrib    sort_nat_MSortBUPermutes       weird_nat_mul3_assoc3
nat_boring_min_assoc          sort_nat_MSortBUSorts          weird_nat_mul3_comm12
nat_boring_min_comm           sort_nat_MSortTDCount          weird_nat_mul3_comm13
nat_boring_min_idem           sort_nat_MSortTDIsSort         weird_nat_mul3_comm23
nat_le_antisym                sort_nat_MSortTDPermutes       weird_nat_mul3_rot
nat_le_ge_eq                  sort_nat_MSortTDSorts          weird_nat_mul3_rrot
nat_le_ne_lt                  sort_nat_NMSortTDCount         weird_nat_mul3_same
nat_le_reflexive              sort_nat_NMSortTDIsSort        weird_nat_mul3_spec
nat_le_trans                  sort_nat_NMSortTDPermutes      weird_nat_op_assoc2
nat_lt_asymmetric             sort_nat_NMSortTDSorts         weird_nat_op_assoc
nat_lt_irreflexive            sort_nat_NStoogeSort2Count     weird_nat_op_comm_comm
nat_lt_ne                     sort_nat_NStoogeSort2IsSort    weird_nat_op_spec
nat_lt_trans                  sort_nat_NStoogeSort2Permutes
)

mkdir TIP15
for smt in ${smt_names[*]}
do
  comm=("tip ../benchmarks/benchmarks/tip2015/"$smt".smt2 --isabelle ")
  echo $comm
  $comm  > TIP15/TIP_$smt.thy
done

for smt in ${smt_names[*]}
do
  sed -i '1s/.*/theory TIP_'$smt'/' TIP15/TIP_$smt.thy 
  sed -i '2s/.*/imports \"..\/..\/Test_Base\"/' TIP15/TIP_$smt.thy
done
