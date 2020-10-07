theory BoolProgs_LeaderFilters
imports 
  "../BoolProgs_Extras"
begin

context begin interpretation BoolProg_Syntax .

(* variables *)
definition "elected \<equiv> 0 :: nat"
definition "error \<equiv> 1 :: nat"

definition "turn n i \<equiv> error + 1 + n*i"
definition "b n i \<equiv> turn n n + i"
definition "c n i \<equiv> b n n + i"

definition curr where "curr n i \<equiv> c n n + n * i"

definition "L_1 n i = curr n n + i"
definition "L_2 n i = L_1 n n + i"
definition "L_3 n i = L_2 n n + i"
definition "L_4 n i = L_3 n n + i"
definition "L_5 n i = L_4 n n + i"
definition "L_8 n i = L_5 n n + i"
definition "L_9 n i = L_8 n n + i"

definition "set_turn n i v vs bs \<equiv> set_counter vs bs (turn n i) n v"
definition "inc_turn n i vs bs \<equiv> inc_counter vs bs (turn n i) n"
definition "dec_turn n i vs bs \<equiv> dec_counter vs bs (turn n i) n"
definition "turn_eq n i v \<equiv> counter_eq (turn n i) n v"

definition "set_curr n i v vs bs \<equiv> set_counter vs bs (curr n i) n v"
definition "inc_curr n i vs bs \<equiv> inc_counter vs bs (curr n i) n"
definition "dec_curr n i vs bs \<equiv> dec_counter vs bs (curr n i) n"
definition "curr_eq n i v \<equiv> counter_eq (curr n i) n v"
definition "curr_access n i act \<equiv> array_access (curr_eq n i) act (n + 1)"
definition "curr_check n i chk \<equiv> array_check (curr_eq n i) chk (n + 1)"

definition lf_const :: "nat \<Rightarrow> const_map" where
  "lf_const n \<equiv> mapping_from_list [
              (STR ''elected'', V elected),
              (STR ''error'', V error)]"

definition lf_fun :: "nat \<Rightarrow> fun_map" where
  "lf_fun n \<equiv> mapping_from_list [
             (STR ''b'', \<lambda>i. V (b n i)),
             (STR ''c'', \<lambda>i. V (c n i))]"


(* init variable list *)

definition lf_init where
  "lf_init n \<equiv> foldl 
    (\<lambda>xs c. bs_insert c xs) (bs_empty ()) [(L_1 n 0)..<(L_1 n n)]"

definition process where
  "process n i = [
     (
       V (L_1 n i),
       curr_access n i (\<lambda>v. set_turn n v (i+1) [L_1 n i, L_2 n i] [FF, TT])
     ), (
       And (V (L_2 n i)) (curr_check n i (\<lambda>v. Not (V (b n v)))),
       [L_2 n i, L_3 n i] ::= [FF, TT]
     ), (
       V (L_3 n i),
       curr_access n i (\<lambda>v. [b n v, L_3 n i, L_4 n i] ::= [TT, FF, TT])
     ), (
       V (L_4 n i),
       curr_access n i (\<lambda>v. IF Not (turn_eq n v (i+1)) THEN [L_4 n i, L_5 n i] ::= [FF, TT] ELSE [L_4 n i, L_8 n i] ::= [FF, TT])
     ), (
       V (L_5 n i),
       curr_access n i (\<lambda>v. [c n v, b n v, L_5 n i] ::= [TT, FF, FF])
     ), (
       V (L_8 n i),
       IF curr_eq n i 0 THEN (inc_curr n i [L_8 n i, L_1 n i] [FF, TT])
       ELSE curr_access n i (\<lambda>v. IF Not (V (c n v)) THEN [L_8 n i, L_9 n i] ::= [FF, TT] ELSE inc_curr n i [L_8 n i, L_1 n i] [FF, TT])
     ), (
       And (V (L_9 n i)) (V elected),
       [error, L_9 n i] ::= [TT, FF]
     ), (
       V (L_9 n i),
       [elected, L_9 n i] ::= [TT, FF]
     )]"

definition processes where
  "processes n = concat (map (process n) [0..<n])"

definition leader_filters :: "nat \<Rightarrow> bprog \<times> config" where
  "leader_filters n =
     (optcomp(WHILE TT DO IF processes n FI), (0, lf_init n))"

end

hide_const b c turn error curr

end
