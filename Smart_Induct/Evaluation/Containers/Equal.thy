(* Title:  Containers/Equal.thy
   Author: Andreas Lochbihler, KIT *)

theory Equal imports Main begin

section \<open>Locales to abstract over HOL equality\<close>

locale equal_base = fixes equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

locale equal = equal_base +
  assumes equal_eq: "equal = (=)"
begin

lemma equal_conv_eq: "equal x y \<longleftrightarrow> x = y"
by(simp add: equal_eq)

end

end
