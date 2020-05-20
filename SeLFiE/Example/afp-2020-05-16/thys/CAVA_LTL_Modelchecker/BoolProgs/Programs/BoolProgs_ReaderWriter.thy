theory BoolProgs_ReaderWriter
imports 
  "../BoolProgs_Extras"
begin

(*
   Reader/Writers case study
   adapted from BEEM library (hTTp://anna.fi.muni.cz/models/)
*)

context begin interpretation BoolProg_Syntax .


(* variables *)
definition "ready \<equiv> 0::nat"
definition "readers_active \<equiv> 1::nat"
definition "writers_active \<equiv> 2::nat"
definition "q_error \<equiv> 3::nat"

definition "reading r w i \<equiv> (q_error + 1) + i"
definition "writing r w i \<equiv> (reading r w r) + i"

definition "activeR r w \<equiv> writing r w w"
definition "set_activeR r w v vs bs \<equiv> set_counter vs bs (activeR r w) r v"
definition "inc_activeR r w vs bs \<equiv> inc_counter vs bs (activeR r w) r"
definition "dec_activeR r w vs bs \<equiv> dec_counter vs bs (activeR r w) r"
definition "activeR_eq r w v \<equiv> counter_eq (activeR r w) r v"

definition rw_const :: "nat \<Rightarrow> const_map" where
  "rw_const n \<equiv> mapping_from_list [
              (STR ''ready'', V ready),
              (STR ''readers_active'', V readers_active),
              (STR ''writers_active'', V writers_active),
              (STR ''q_error'', V q_error) ]"

definition rw_fun :: "nat \<Rightarrow> fun_map" where
  "rw_fun n \<equiv> mapping_from_list [
             (STR ''reading'', \<lambda>i. V (reading n n i)),
             (STR ''writing'', \<lambda>i. V (writing n n i)),
             (STR ''activeR_eq'', activeR_eq n n) ]"


(* init variable list *)
definition rw_init where
  "rw_init r w \<equiv> bs_insert ready (bs_empty ())"

(* program *)
definition reader_control where
  "reader_control r w i \<equiv> [
     (
      V ready,
      [ready, readers_active] ::= [FF, TT]
     ), (
      And (V readers_active) (Not (V (reading r w i))),
      inc_activeR r w [reading r w i] [TT]
     ), (
      And (V readers_active) (V (reading r w i)),
      dec_activeR r w [reading r w i] [FF]
     ), (
      And (V readers_active) (activeR_eq r w 0),
      [readers_active, ready] ::= [FF, TT]
     )]"

definition writer_control where
  "writer_control r w i \<equiv> [
     (
      V ready,
      [ready, writers_active, writing r w i] ::= [FF, TT, TT]
     ), (
      And (V readers_active) (V (writing r w i)),
      [readers_active, q_error, writing r w i] ::= [FF,TT,FF]
    ), (
      And (V writers_active) (V (writing r w i)),
      [writers_active, ready, writing r w i] ::= [FF, TT, FF]
    )]"

fun rw_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (bexp \<times> com) list" where
  "rw_body _ _ 0 0 = []"
| "rw_body r w (Suc r') 0 = reader_control r w r' @ rw_body r w r' 0"
| "rw_body r w r' (Suc w') = writer_control r w w' @ rw_body r w r' w'"

definition reader_writer :: "nat \<Rightarrow> nat \<Rightarrow> bprog \<times> config" where
  "reader_writer r w =
     (optcomp(WHILE TT DO IF (rw_body r w r w) FI), (0, rw_init r w))"

(*
// Interesting property e.g.:
// G (not q_error)

// An "error" can be injected by changing the lines
//  // decrement actvR
//  IF actvR_1 THEN (actvR_0 := TT; actvR_1 := FF);
//  IF actvR_2 THEN (actvR_1 := TT; actvR_2 := FF);
// 
// to 
// (actvR_1 := TT; actvR_0 := FF; actvR_2 := FF)
// (actvR := 1 instead of actvR := actvR - 1)
// With only 2 writers, this is not really an error :)
*)

end

end
