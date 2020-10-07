theory Concrete_heap
imports
  "HOL-Library.Saturated"
  "../Proofs"
begin

type_synonym field = "3"
type_synonym mut = "2"
type_synonym ref = "5"

type_synonym concrete_local_state = "(field, mut, ref) local_state"
type_synonym clsts = "(field, mut, ref) lsts"

abbreviation mut_common_init_state :: concrete_local_state where
  "mut_common_init_state \<equiv> undefined\<lparr> ghost_handshake_phase := hp_IdleMarkSweep, ghost_honorary_grey := {}, ghost_honorary_root := {}, roots := {}, W := {} \<rparr>"

context gc_system
begin

abbreviation sys_init_heap :: "ref \<Rightarrow> (field, ref) object option" where
  "sys_init_heap \<equiv>
  [   0 \<mapsto> \<lparr> obj_mark = initial_mark,
           obj_fields = [ 0 \<mapsto> 5 ] \<rparr>,
      1 \<mapsto> \<lparr> obj_mark = initial_mark,
           obj_fields = Map.empty \<rparr>,
      2 \<mapsto> \<lparr> obj_mark = initial_mark,
           obj_fields = Map.empty \<rparr>,
      3 \<mapsto> \<lparr> obj_mark = initial_mark,
           obj_fields = [ 0 \<mapsto> 1 , 1 \<mapsto> 2 ] \<rparr>,
      4 \<mapsto> \<lparr> obj_mark = initial_mark,
           obj_fields = [ 1 \<mapsto> 0 ] \<rparr>,
      5 \<mapsto> \<lparr> obj_mark = initial_mark,
           obj_fields = Map.empty \<rparr>
  ]"

abbreviation mut_init_state0 :: concrete_local_state where
  "mut_init_state0 \<equiv> mut_common_init_state \<lparr> roots := {1, 2, 3} \<rparr>"

abbreviation mut_init_state1 :: concrete_local_state where
  "mut_init_state1 \<equiv> mut_common_init_state \<lparr> roots := {3} \<rparr>"

abbreviation mut_init_state2 :: concrete_local_state where
  "mut_init_state2 \<equiv> mut_common_init_state \<lparr> roots := {2, 5} \<rparr>"

end

end
