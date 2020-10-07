(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
section \<open>Auxiliary Results\<close>

subsection \<open>Reflexive Transitive Closures of Orders\<close>

theory Transitive_Closure_More
  imports Main
begin

lemma (in order) rtranclp_less_eq [simp]:
  "(\<le>)\<^sup>*\<^sup>* = (\<le>)"
  by (intro ext) (auto elim: rtranclp_induct)

lemma (in order) tranclp_less [simp]:
  "(<)\<^sup>+\<^sup>+ = (<)"
  by (intro ext) (auto elim: tranclp_induct)

lemma (in order) rtranclp_greater_eq [simp]:
  "(\<ge>)\<^sup>*\<^sup>* = (\<ge>)"
  by (intro ext) (auto elim: rtranclp_induct)

lemma (in order) tranclp_greater [simp]:
  "(>)\<^sup>+\<^sup>+ = (>)"
  by (intro ext) (auto elim: tranclp_induct)

end