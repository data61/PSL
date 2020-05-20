theory BoolProgs_Philosophers
imports "../BoolProgs_Extras"
begin

context begin interpretation BoolProg_Syntax .

definition "eat m i = i"
definition "one m i = m + i"
definition "free m i = (2*m) + (i mod m)"
definition "Eat m i = V(eat m i)"
definition Free where "Free m i = V(free m i)"
definition One where "One m i = V(one m i)"

definition phil_const :: "nat \<Rightarrow> const_map" where
  "phil_const n \<equiv> Mapping.empty"

definition phil_fun :: "nat \<Rightarrow> fun_map" where
  "phil_fun n \<equiv> mapping_from_list [
              (STR ''eat'', Eat n),
              (STR ''one'', One n),
              (STR ''free'', Free n) ]"


definition phil_init :: "nat \<Rightarrow> state" where
  "phil_init n = foldl (\<lambda>xs i. bs_insert (free n i) xs) (bs_empty ()) [0..<n]"

(*definition phil_init :: "nat \<Rightarrow> state" where
  "phil_init n = replicate (2 * n) False @ replicate n True"
*)

fun dining :: "nat \<Rightarrow> nat \<Rightarrow> (bexp \<times> com) list" where
"dining m 0 = []" |
"dining m (Suc i) = [
  (
   And (Not (Eat m i)) (Free m i),
   [one m i, free m i] ::= [TT, FF]
  ), (
   And (One m i) (Free m (i + 1)),
   [one m i, free m (i+1), eat m i] ::= [FF, FF, TT]
  ), (
   Eat m i,
   [free m i, free m (i+1), eat m i] ::= [TT, TT, FF]
  )] @ dining m i"

definition philosophers :: " nat \<Rightarrow> bprog \<times> config" where
  "philosophers n = (optcomp (WHILE TT DO IF dining n n FI), (0, phil_init n))"

end

hide_const eat one free Eat Free One

end
