(* License: LGPL *)
(*
Author: Julian Parsert <julian.parsert@gmail.com>
Author: Cezary Kaliszyk
*)


section \<open> Consumers  \<close>

text \<open> Consumption sets \<close>


theory Consumers
  imports
    "HOL-Analysis.Analysis"
    "../Syntax"
begin

subsection \<open> Pre Arrow-Debreu consumption set \<close>

text \<open> It turns out that the First Welfare Theorem does
       not require any particular limitations on the consumption set \<close>
locale pre_arrow_debreu_consumption_set =
  fixes consumption_set :: "('a::euclidean_space) set"
  assumes "x \<in> (UNIV:: 'a set) \<Longrightarrow> x \<in> consumption_set"
begin
end


subsection \<open> Arrow-Debreu model consumption set\<close>

text \<open> The Arrow-Debreu model consumption set includes more and stricter
        assumptions which are necessary for further results. \<close>
locale gen_pre_arrow_debreu_consum_set =
  fixes consumption_set :: "('a::ordered_euclidean_space) set"
begin

end

locale arrow_debreu_consum_set =
  fixes consumption_set :: "('a::ordered_euclidean_space) set"
  assumes r_plus: "consumption_set \<subseteq> {(x::'a). x \<ge> 0}"
  assumes closed: "closed consumption_set"
  assumes convex: "convex consumption_set"
  assumes non_empty: "consumption_set \<noteq> {}"
  assumes "\<forall>M \<in> consumption_set. (\<forall>x > M. x \<in> consumption_set)" (*unbounded above*)
begin

lemma x_larger_0: "x \<in> consumption_set \<Longrightarrow> x \<ge> 0"
  using r_plus by auto

lemma larger_in_consump_set:
  "x \<in> consumption_set \<and> y \<ge> x \<Longrightarrow> y \<in> consumption_set"
  using arrow_debreu_consum_set_axioms arrow_debreu_consum_set_def
    dual_order.order_iff_strict by fastforce

end

end