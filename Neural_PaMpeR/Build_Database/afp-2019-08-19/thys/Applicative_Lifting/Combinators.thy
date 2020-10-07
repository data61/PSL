(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Combinators defined as closed lambda terms\<close>

theory Combinators
imports Beta_Eta
begin

definition I_def: "\<I> = Abs (Var 0)"
definition B_def: "\<B> = Abs (Abs (Abs (Var 2 \<degree> (Var 1 \<degree> Var 0))))"
definition T_def: "\<T> = Abs (Abs (Var 0 \<degree> Var 1))" \<comment> \<open>reverse application\<close>

lemma I_eval: "\<I> \<degree> x \<rightarrow>\<^sub>\<beta> x"
proof -
  have "\<I> \<degree> x \<rightarrow>\<^sub>\<beta> Var 0[x/0]" unfolding I_def ..
  then show ?thesis by simp
qed

lemma I_equiv[iff]: "\<I> \<degree> x \<leftrightarrow> x"
using I_eval ..

lemma I_closed[simp]: "liftn n \<I> k = \<I>"
unfolding I_def by simp

lemma B_eval1: "\<B> \<degree> g \<rightarrow>\<^sub>\<beta> Abs (Abs (lift (lift g 0) 0 \<degree> (Var 1 \<degree> Var 0)))"
proof -
  have "\<B> \<degree> g \<rightarrow>\<^sub>\<beta> Abs (Abs (Var 2 \<degree> (Var 1 \<degree> Var 0))) [g/0]" unfolding B_def ..
  then show ?thesis by (simp add: numerals)
qed

lemma B_eval2: "\<B> \<degree> g \<degree> f \<rightarrow>\<^sub>\<beta>\<^sup>* Abs (lift g 0 \<degree> (lift f 0 \<degree> Var 0))"
proof -
  have "\<B> \<degree> g \<degree> f \<rightarrow>\<^sub>\<beta>\<^sup>* Abs (Abs (lift (lift g 0) 0 \<degree> (Var 1 \<degree> Var 0))) \<degree> f"
    using B_eval1 by blast
  also have "... \<rightarrow>\<^sub>\<beta> Abs (lift (lift g 0) 0 \<degree> (Var 1 \<degree> Var 0)) [f/0]" ..
  also have "... = Abs (lift g 0 \<degree> (lift f 0 \<degree> Var 0))" by simp
  finally show ?thesis .
qed

lemma B_eval: "\<B> \<degree> g \<degree> f \<degree> x \<rightarrow>\<^sub>\<beta>\<^sup>* g \<degree> (f \<degree> x)"
proof -
  have "\<B> \<degree> g \<degree> f \<degree> x \<rightarrow>\<^sub>\<beta>\<^sup>* Abs (lift g 0 \<degree> (lift f 0 \<degree> Var 0)) \<degree> x"
    using B_eval2 by blast
  also have "... \<rightarrow>\<^sub>\<beta> (lift g 0 \<degree> (lift f 0 \<degree> Var 0)) [x/0]" ..
  also have "... = g \<degree> (f \<degree> x)" by simp
  finally show ?thesis .
qed

lemma B_equiv[iff]: "\<B> \<degree> g \<degree> f \<degree> x \<leftrightarrow> g \<degree> (f \<degree> x)"
using B_eval ..

lemma B_closed[simp]: "liftn n \<B> k = \<B>"
unfolding B_def by simp

lemma T_eval1: "\<T> \<degree> x \<rightarrow>\<^sub>\<beta> Abs (Var 0 \<degree> lift x 0)"
proof -
  have "\<T> \<degree> x \<rightarrow>\<^sub>\<beta> Abs (Var 0 \<degree> Var 1) [x/0]" unfolding T_def ..
  then show ?thesis by simp
qed

lemma T_eval: "\<T> \<degree> x \<degree> f \<rightarrow>\<^sub>\<beta>\<^sup>* f \<degree> x"
proof -
  have "\<T> \<degree> x \<degree> f \<rightarrow>\<^sub>\<beta>\<^sup>* Abs (Var 0 \<degree> lift x 0) \<degree> f"
    using T_eval1 by blast
  also have "... \<rightarrow>\<^sub>\<beta> (Var 0 \<degree> lift x 0) [f/0]" ..
  also have "... = f \<degree> x" by simp
  finally show ?thesis .
qed

lemma T_equiv[iff]: "\<T> \<degree> x \<degree> f \<leftrightarrow> f \<degree> x"
using T_eval ..

lemma T_closed[simp]: "liftn n \<T> k = \<T>"
unfolding T_def by simp

end
