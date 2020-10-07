(*  Title:      Util_MinMax.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

section \<open>Order and linear order: min and max\<close>

theory Util_MinMax
imports Main
begin

subsection \<open>Additional lemmata about @{term min} and @{term max}\<close>

lemma min_less_imp_conj: "(z::'a::linorder) < min x y \<Longrightarrow> z < x \<and> z < y" by simp
lemma conj_less_imp_min: "\<lbrakk> z < x; z < y \<rbrakk> \<Longrightarrow> (z::'a::linorder) < min x y" by simp

(*lemma min_le_iff_conj: "((z::'a::linorder) \<le> min x y) = (z \<le> x \<and> z \<le> y)"*)
lemmas min_le_iff_conj = min.bounded_iff
lemma min_le_imp_conj: "(z::'a::linorder) \<le> min x y \<Longrightarrow> z \<le> x \<and> z \<le> y" by simp
(*lemma conj_le_imp_min: "\<lbrakk> z \<le> x; z \<le> y \<rbrakk> \<Longrightarrow> (z::'a::linorder) \<le> min x y"*)
lemmas conj_le_imp_min = min.boundedI

(*lemma min_eqL:"\<lbrakk> (x::('a::linorder)) \<le> y \<rbrakk> \<Longrightarrow> min x y = x"*)
lemmas min_eqL = min.absorb1
(*lemma min_eqR:"\<lbrakk> (y::('a::linorder)) \<le> x \<rbrakk> \<Longrightarrow> min x y = y"*)
lemmas min_eqR = min.absorb2
lemmas min_eq = min_eqL min_eqR

lemma max_less_imp_conj:"max x y < b \<Longrightarrow> x < (b::('a::linorder)) \<and> y < b" by simp
lemma conj_less_imp_max:"\<lbrakk> x < (b::('a::linorder)); y < b \<rbrakk> \<Longrightarrow> max x y < b" by simp

(*lemma max_le_iff_conj: "(max x y \<le> b) = (x \<le> (b::('a::linorder)) \<and> y \<le> b)"*)
lemmas max_le_iff_conj = max.bounded_iff
lemma max_le_imp_conj:"max x y \<le> b \<Longrightarrow> x \<le> (b::('a::linorder)) \<and> y \<le> b" by simp
(*lemma conj_le_imp_max:"\<lbrakk> x \<le> (b::('a::linorder)); y \<le> b \<rbrakk> \<Longrightarrow> max x y \<le> b"*)
lemmas conj_le_imp_max =  max.boundedI

(*lemma max_eqL:"\<lbrakk> (y::('a::linorder)) \<le> x \<rbrakk> \<Longrightarrow> max x y = x"*)
lemmas max_eqL = max.absorb1
(*lemma max_eqR:"\<lbrakk> (x::('a::linorder)) \<le> y \<rbrakk> \<Longrightarrow> max x y = y"*)
lemmas max_eqR =  max.absorb2
lemmas max_eq = max_eqL max_eqR

(*lemma le_minI1:"min x y \<le> (x::('a::linorder))"*)
lemmas le_minI1 = min.cobounded1
(*lemma le_minI2:"min x y \<le> (y::('a::linorder))"*)
lemmas le_minI2 = min.cobounded2


lemma
  min_le_monoR: "(a::'a::linorder) \<le> b \<Longrightarrow> min x a \<le> min x b" and
  min_le_monoL: "(a::'a::linorder) \<le> b \<Longrightarrow> min a x \<le> min b x"
by (fastforce simp: min.mono min_def)+
lemma
  max_le_monoR: "(a::'a::linorder) \<le> b \<Longrightarrow> max x a \<le> max x b" and
  max_le_monoL: "(a::'a::linorder) \<le> b \<Longrightarrow> max a x \<le> max b x"
by (fastforce simp: max.mono max_def)+

end
