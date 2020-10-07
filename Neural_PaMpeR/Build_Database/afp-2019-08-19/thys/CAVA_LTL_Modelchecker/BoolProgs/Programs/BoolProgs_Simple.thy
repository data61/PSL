theory BoolProgs_Simple
imports 
  "../BoolProgs_Extras"
begin

context begin interpretation BoolProg_Syntax .

fun simple_prog :: "nat \<Rightarrow> nat \<Rightarrow> (bexp \<times> com) list" where
  "simple_prog _ 0 = []"
| "simple_prog r (Suc n) = (V n, [n] ::= [FF]) # simple_prog r n"

definition simple :: "nat \<Rightarrow> bprog \<times> config" where 
  "simple n = (optcomp 
    (WHILE TT DO IF simple_prog n n FI), 
    (0, foldl (\<lambda>xs i. bs_insert i xs) (bs_empty ()) [0..<n]))"

definition simple_const :: "nat \<Rightarrow> const_map"  where
  "simple_const n \<equiv> Mapping.empty"

definition simple_fun :: "nat \<Rightarrow> fun_map" where
  "simple_fun n \<equiv> mapping_from_list [(STR ''var'', \<lambda>i. V i)]"

end

end
