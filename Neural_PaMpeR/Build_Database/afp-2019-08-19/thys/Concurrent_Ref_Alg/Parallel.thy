section \<open>Parallel Operator \label{S:parallel}\<close>

theory Parallel
imports Refinement_Lattice
begin

subsection \<open>Basic parallel operator\<close>

text \<open>
  The parallel operator is associative, commutative and has unit skip
  and has as an annihilator the lattice bottom. 
\<close>

locale skip = 
  fixes skip :: "'a::refinement_lattice"  ("skip") 

locale par =
  fixes par :: "'a::refinement_lattice \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<parallel>" 75)
  assumes abort_par:   "\<bottom> \<parallel> c = \<bottom>"    (* ++ *)

locale parallel = par + skip + par: comm_monoid par skip
begin

lemmas [algebra_simps, field_simps] =
  par.assoc
  par.commute
  par.left_commute

lemmas par_assoc = par.assoc            (* 36 *)
lemmas par_commute = par.commute        (* 37 *)
lemmas par_skip = par.right_neutral     (* 38 *)
lemmas par_skip_left = par.left_neutral (* 38 + 37 *)

end


subsection \<open>Distributed parallel\<close>

text \<open>
  The parallel operator distributes across arbitrary non-empty infima.
\<close>
locale par_distrib = parallel + 
  assumes par_Inf_distrib: "D \<noteq> {} \<Longrightarrow> c \<parallel> (\<Sqinter> D) = (\<Sqinter>d\<in>D. c \<parallel> d)"    (* 39+ *)

begin

lemma Inf_par_distrib: "D \<noteq> {} \<Longrightarrow> (\<Sqinter> D) \<parallel> c = (\<Sqinter>d\<in>D. d \<parallel> c)"
  using par_Inf_distrib par_commute by simp

lemma par_INF_distrib: "X \<noteq> {} \<Longrightarrow> c \<parallel> (\<Sqinter>x\<in>X. d x) = (\<Sqinter>x\<in>X. c \<parallel> d x)"
  using par_Inf_distrib by (auto simp add: image_comp)

lemma INF_par_distrib: "X \<noteq> {} \<Longrightarrow> (\<Sqinter>x\<in>X. d x) \<parallel> c = (\<Sqinter>x\<in>X. d x \<parallel> c)"
  using par_INF_distrib par_commute by (metis (mono_tags, lifting) INF_cong) 

lemma INF_INF_par_distrib: 
    "X \<noteq> {} \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> (\<Sqinter>x\<in>X. c x) \<parallel> (\<Sqinter>y\<in>Y. d y) = (\<Sqinter>x\<in>X. \<Sqinter>y\<in>Y. c x \<parallel> d y)"
proof -
  assume nonempty_X: "X \<noteq> {}"
  assume nonempty_Y: "Y \<noteq> {}"
  have "(\<Sqinter>x\<in>X. c x) \<parallel> (\<Sqinter>y\<in>Y. d y) = (\<Sqinter>x\<in>X. c x \<parallel> (\<Sqinter>y\<in>Y. d y))"
    using INF_par_distrib by (metis nonempty_X)
  also have "\<dots> = (\<Sqinter>x\<in>X. \<Sqinter>y\<in>Y. c x \<parallel> d y)" using par_INF_distrib by (metis nonempty_Y)
  thus ?thesis by (simp add: calculation) 
qed 

lemma inf_par_distrib: "(c\<^sub>0 \<sqinter> c\<^sub>1) \<parallel> d = (c\<^sub>0 \<parallel> d) \<sqinter> (c\<^sub>1 \<parallel> d)"
proof -
  have "(c\<^sub>0 \<sqinter> c\<^sub>1) \<parallel> d = (\<Sqinter> {c\<^sub>0, c\<^sub>1}) \<parallel> d" by simp
  also have "... = (\<Sqinter>c \<in> {c\<^sub>0, c\<^sub>1}. c \<parallel> d)" using Inf_par_distrib by (meson insert_not_empty) 
  also have "... = c\<^sub>0 \<parallel> d \<sqinter> c\<^sub>1 \<parallel> d" by simp
  finally show ?thesis .
qed

lemma inf_par_distrib2: "d \<parallel> (c\<^sub>0 \<sqinter> c\<^sub>1) = (d \<parallel> c\<^sub>0) \<sqinter> (d \<parallel> c\<^sub>1)"
  using inf_par_distrib par_commute by auto

lemma inf_par_product: "(a \<sqinter> b) \<parallel> (c \<sqinter> d) = (a \<parallel> c) \<sqinter> (a \<parallel> d) \<sqinter> (b \<parallel> c) \<sqinter> (b \<parallel> d)"
  by (simp add: inf_commute inf_par_distrib inf_par_distrib2 inf_sup_aci(3))

lemma par_mono: "c\<^sub>1 \<sqsubseteq> d\<^sub>1 \<Longrightarrow> c\<^sub>2 \<sqsubseteq> d\<^sub>2 \<Longrightarrow> c\<^sub>1 \<parallel> c\<^sub>2 \<sqsubseteq> d\<^sub>1 \<parallel> d\<^sub>2"
  by (metis inf.orderE le_inf_iff order_refl inf_par_distrib par_commute)

end
end
