section \<open>Iteration \label{S:iteration}\<close>

theory Iteration
imports
  Galois_Connections
  CRA
begin

subsection \<open>Possibly infinite iteration\<close>

text \<open>
  Iteration of finite or infinite steps can be defined using a least fixed point.
\<close>


(* hide_fact (open) Random_Sequence.iter_def *)

locale finite_or_infinite_iteration = seq_distrib + upper_galois_connections
begin

definition
  iter :: "'a \<Rightarrow> 'a" ("_\<^sup>\<omega>" [103] 102) (* this can be entered as \sup\circ *)
where
  "c\<^sup>\<omega> \<equiv> lfp (\<lambda> x. nil \<sqinter> c;x)"

lemma iter_step_mono: "mono (\<lambda> x. nil \<sqinter> c;x)"
  by (meson inf_mono order_refl seq_mono_right mono_def)

text \<open>
  This fixed point definition leads to the two core iteration lemmas:
  folding and induction.
\<close>

theorem iter_unfold: "c\<^sup>\<omega> = nil \<sqinter> c;c\<^sup>\<omega>"
  using iter_def iter_step_mono lfp_unfold by auto

lemma iter_induct_nil: "nil \<sqinter> c;x \<sqsubseteq> x \<Longrightarrow> c\<^sup>\<omega> \<sqsubseteq> x"
  by (simp add: iter_def lfp_lowerbound)

lemma iter0: "c\<^sup>\<omega> \<sqsubseteq> nil"
  by (metis iter_unfold sup.orderI sup_inf_absorb)

lemma iter1: "c\<^sup>\<omega> \<sqsubseteq> c"
  by (metis inf_le2 iter0 iter_unfold order.trans seq_mono_right seq_nil_right)

lemma iter2 [simp]: "c\<^sup>\<omega>;c\<^sup>\<omega> = c\<^sup>\<omega>"
proof (rule antisym)
  show "c\<^sup>\<omega>;c\<^sup>\<omega> \<sqsubseteq> c\<^sup>\<omega>" using iter0 seq_mono_right by fastforce
next
  have a: "nil \<sqinter> c;c\<^sup>\<omega>;c\<^sup>\<omega> \<sqsubseteq> nil \<sqinter> c;c\<^sup>\<omega> \<sqinter> c;c\<^sup>\<omega>;c\<^sup>\<omega>"
    by (metis inf_greatest inf_le2 inf_mono iter0 order_refl seq_distrib_left.seq_mono_right seq_distrib_left_axioms seq_nil_right) 
  then have b: "\<dots> = c\<^sup>\<omega> \<sqinter> c;c\<^sup>\<omega>;c\<^sup>\<omega>" using iter_unfold by auto 
  then have c: "\<dots> = (nil \<sqinter> c;c\<^sup>\<omega>);c\<^sup>\<omega>" by (simp add: inf_seq_distrib)
  thus "c\<^sup>\<omega> \<sqsubseteq> c\<^sup>\<omega>;c\<^sup>\<omega>" using a iter_induct_nil iter_unfold seq_assoc by auto 
qed

lemma iter_mono: "c \<sqsubseteq> d \<Longrightarrow> c\<^sup>\<omega> \<sqsubseteq> d\<^sup>\<omega>"
proof -
  assume "c \<sqsubseteq> d"
  then have "nil \<sqinter> c;d\<^sup>\<omega> \<sqsubseteq> d;d\<^sup>\<omega>" by (metis inf.absorb_iff2 inf_left_commute inf_seq_distrib)
  then have "nil \<sqinter> c;d\<^sup>\<omega> \<sqsubseteq> d\<^sup>\<omega>" by (metis inf.bounded_iff inf_sup_ord(1) iter_unfold) 
  thus ?thesis by (simp add: iter_induct_nil)
qed

lemma iter_abort: "\<bottom> = nil\<^sup>\<omega>"
  by (simp add: antisym iter_induct_nil)

lemma nil_iter: "\<top>\<^sup>\<omega> = nil"
   by (metis (no_types) inf_top.right_neutral iter_unfold seq_top)
(*
lemma iter_conj_distrib:
  assumes nil: "c \<sqsubseteq> nil"
    and repeat: "c \<sqsubseteq> c ; c"
  shows "c \<iinter> d\<^sup>\<omega> \<sqsubseteq> (c \<iinter> d)\<^sup>\<omega>"
proof (unfold iter_def)
  def F \<equiv> "(\<lambda> x. c \<iinter> x)"
  def G \<equiv> "(\<lambda> x. nil \<sqinter> d;x)"
  def H \<equiv> "(\<lambda> x. nil \<sqinter> ((c \<iinter> d);x))"

  have FG: "F \<circ> G = (\<lambda> x. c \<iinter> (nil \<sqinter> d;x))"  by (metis comp_def F_def G_def) 
  have HF: "H \<circ> F = (\<lambda> x. (nil \<sqinter> (c \<iinter> d);(c \<iinter> x)))" by (metis comp_def H_def F_def) 

  have "F (lfp G) \<sqsubseteq> lfp H"
  proof (rule fusion_lfp_leq)
    show "mono H" by (simp add: H_def iter_step_mono)
  next
    show "dist_over_sup F" by (simp add: F_def conj_Sup_distrib)
  next
    fix x
    have "c \<iinter> (nil \<sqinter> d;x) = (c \<iinter> nil) \<sqinter> (c \<iinter> d;x)" by (metis inf_conj_distrib conj_commute)
    also have "... \<sqsubseteq> nil \<sqinter> (c \<iinter> d;x)" by (metis conjunction_sup inf_mono_left le_iff_sup nil)
    also have "... \<sqsubseteq> nil \<sqinter> (c;c \<iinter> d;x)" by (metis inf_conj_distrib inf.absorb_iff2 inf_mono_right repeat)
    also have "... \<sqsubseteq> nil \<sqinter> (c \<iinter> d);(c \<iinter> x)" by (meson inf_mono_right sequential_interchange)
    finally show "(F \<circ> G) x \<sqsubseteq> (H \<circ> F) x" by (simp add: FG HF)
  qed

  then show "c \<iinter> lfp(\<lambda>x. nil \<sqinter> d ; x) \<sqsubseteq> lfp (\<lambda>x. nil \<sqinter> (c \<iinter> d) ; x)" using F_def G_def H_def by simp
qed

lemma iter_conj_distrib1: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<sqsubseteq> (c\<^sup>\<omega> \<iinter> d)\<^sup>\<omega>"
  by (simp add: iter0 iter_conj_distrib)

lemma iter_conj_distrib2: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<sqsubseteq> (c \<iinter> d)\<^sup>\<omega>"
proof -
  have a: "c\<^sup>\<omega> \<sqsubseteq> c" by (metis iter1)
  have b: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<sqsubseteq> (c\<^sup>\<omega> \<iinter> d)\<^sup>\<omega>" by (metis iter_conj_distrib1)
  have "c\<^sup>\<omega> \<iinter> d \<sqsubseteq> c \<iinter> d" by (metis a conj_mono order.refl) 
  thus ?thesis using a b by (metis refine_trans iter_mono) 
qed
*)
end



subsection \<open>Finite iteration\<close>

text \<open>
  Iteration of a finite number of steps (Kleene star) is defined
  using the greatest fixed point.
\<close>

locale finite_iteration = seq_distrib + lower_galois_connections
begin

definition
  fiter :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100)
where
  "c\<^sup>\<star> \<equiv> gfp (\<lambda> x. nil \<sqinter> c;x)"


lemma fin_iter_step_mono: "mono (\<lambda> x. nil \<sqinter> c;x)"
  by (meson inf_mono order_refl seq_mono_right mono_def)

text \<open>
  This definition leads to the two core iteration lemmas:
  folding and induction.
\<close>

lemma fiter_unfold: "c\<^sup>\<star> = nil \<sqinter> c;c\<^sup>\<star>"
  using fiter_def gfp_unfold fin_iter_step_mono by auto

lemma fiter_induct_nil: "x \<sqsubseteq> nil \<sqinter> c;x \<Longrightarrow> x \<sqsubseteq> c\<^sup>\<star>"
  by (simp add: fiter_def gfp_upperbound)

lemma fiter0: "c\<^sup>\<star> \<sqsubseteq> nil"
  by (metis fiter_unfold inf.cobounded1)

lemma fiter1: "c\<^sup>\<star> \<sqsubseteq> c"
  by (metis fiter0 fiter_unfold inf_le2 order.trans seq_mono_right seq_nil_right)

lemma fiter_induct_eq: "c\<^sup>\<star>;d = gfp (\<lambda> x. c;x \<sqinter> d)"
proof -
  define F where "F = (\<lambda> x. x;d)"
  define G where "G = (\<lambda> x. nil \<sqinter> c;x)"
  define H where "H = (\<lambda> x. c;x \<sqinter> d)"

  have FG: "F \<circ> G = (\<lambda> x. c;x;d \<sqinter> d)" by (simp add: F_def G_def comp_def inf_commute inf_seq_distrib)
  have HF: "H \<circ> F = (\<lambda> x. c;x;d \<sqinter> d)" by (metis comp_def seq_assoc H_def F_def) 

  have adjoint: "dist_over_inf F" using Inf_seq_distrib F_def by simp
  have monoH: "mono H"
    by (metis H_def inf_mono_left monoI seq_distrib_left.seq_mono_right seq_distrib_left_axioms)
  have monoG: "mono G" by (metis G_def inf_mono_right mono_def seq_mono_right) 
  have "\<forall> x. ((F \<circ> G) x = (H \<circ> F) x)" using FG HF by simp
  then have "F (gfp G) = gfp H" using adjoint monoG monoH fusion_gfp_eq by blast 
  then have "(gfp (\<lambda> x. nil \<sqinter> c;x));d = gfp (\<lambda> x. c;x \<sqinter> d)" using F_def G_def H_def inf_commute by simp
  thus ?thesis by (metis fiter_def) 
qed

theorem fiter_induct: "x \<sqsubseteq> d \<sqinter> c;x \<Longrightarrow> x \<sqsubseteq> c\<^sup>\<star>;d"
proof -
  assume "x \<sqsubseteq> d \<sqinter> c;x"
  then have "x \<sqsubseteq> c;x \<sqinter> d" using inf_commute by simp
  then have "x \<sqsubseteq> gfp (\<lambda> x. c;x \<sqinter> d)" by (simp add: gfp_upperbound)
  thus ?thesis by (metis (full_types) fiter_induct_eq)
qed

lemma fiter2 [simp]: "c\<^sup>\<star>;c\<^sup>\<star> = c\<^sup>\<star>"
proof -
  have lr: "c\<^sup>\<star>;c\<^sup>\<star> \<sqsubseteq> c\<^sup>\<star>" using fiter0 seq_mono_right seq_nil_right by fastforce 
  have rl: "c\<^sup>\<star> \<sqsubseteq> c\<^sup>\<star>;c\<^sup>\<star>" by (metis fiter_induct fiter_unfold inf.right_idem order_refl) 
  thus ?thesis by (simp add: antisym lr) 
qed

lemma fiter3 [simp]: "(c\<^sup>\<star>)\<^sup>\<star> = c\<^sup>\<star>"
  by (metis dual_order.refl fiter0 fiter1 fiter2 fiter_induct inf.commute inf_absorb1 seq_nil_right)

lemma fiter_mono: "c \<sqsubseteq> d \<Longrightarrow> c\<^sup>\<star> \<sqsubseteq> d\<^sup>\<star>"
proof -
  assume "c \<sqsubseteq> d"
  then have "c\<^sup>\<star> \<sqsubseteq> nil \<sqinter> d;c\<^sup>\<star>" by (metis fiter0 fiter1 fiter2 inf.bounded_iff refine_trans seq_mono_left)
  thus ?thesis  by (metis seq_nil_right fiter_induct)
qed

end



subsection \<open>Infinite iteration\<close>

text \<open>
  Iteration of infinite number of steps can be defined
  using a least fixed point.
\<close>

locale infinite_iteration = seq_distrib + lower_galois_connections
begin

definition
  infiter :: "'a  \<Rightarrow> 'a" ("_\<^sup>\<infinity>" [105] 106)
where
  "c\<^sup>\<infinity> \<equiv> lfp (\<lambda> x. c;x)"

lemma infiter_step_mono: "mono (\<lambda> x. c;x)"
  by (meson inf_mono order_refl seq_mono_right mono_def)

text \<open>
  This definition leads to the two core iteration lemmas:
  folding and induction.
\<close>

theorem infiter_unfold: "c\<^sup>\<infinity> = c;c\<^sup>\<infinity>"
  using infiter_def infiter_step_mono lfp_unfold by auto

lemma infiter_induct: "c;x \<sqsubseteq> x \<Longrightarrow> c\<^sup>\<infinity> \<sqsubseteq> x"
  by (simp add: infiter_def lfp_lowerbound)

theorem infiter_unfold_any: "c\<^sup>\<infinity> = (c \<^sup>;^ i) ; c\<^sup>\<infinity>"
proof (induct i)
  case 0
  thus ?case by simp
next
  case (Suc i)
  thus ?case using infiter_unfold seq_assoc seq_power_Suc by auto
qed

lemma infiter_annil: "c\<^sup>\<infinity>;x = c\<^sup>\<infinity>"
proof -
  have "\<forall>a. (\<bottom>::'a) \<sqsubseteq> a"
    by auto
  thus ?thesis
    by (metis (no_types) eq_iff inf.cobounded2 infiter_induct infiter_unfold inf_sup_ord(1) seq_assoc seq_bot weak_seq_inf_distrib seq_nil_right)
qed

end



subsection \<open>Combined iteration\<close>

text \<open>
  The three different iteration operators can be combined to show that 
  finite iteration refines finite-or-infinite iteration.
\<close>

locale iteration = finite_or_infinite_iteration + finite_iteration + 
                   infinite_iteration
begin

lemma refine_iter: "c\<^sup>\<omega> \<sqsubseteq> c\<^sup>\<star>"
  by (metis seq_nil_right order.refl iter_unfold fiter_induct)

lemma iter_absorption [simp]: "(c\<^sup>\<omega>)\<^sup>\<star> = c\<^sup>\<omega>"
proof (rule antisym)
  show "(c\<^sup>\<omega>)\<^sup>\<star> \<sqsubseteq> c\<^sup>\<omega>" by (metis fiter1)
next
  show "c\<^sup>\<omega> \<sqsubseteq> (c\<^sup>\<omega>)\<^sup>\<star>" by (metis fiter1 fiter_induct inf_left_idem iter2 iter_unfold seq_nil_right sup.cobounded2 sup.orderE sup_commute)
qed

lemma infiter_inf_top: "c\<^sup>\<infinity> = c\<^sup>\<omega> ; \<top>" 
proof -
  have lr: "c\<^sup>\<infinity> \<sqsubseteq> c\<^sup>\<omega> ; \<top>"
  proof -
    have "c ; (c\<^sup>\<omega> ; \<top>) = nil ; \<top> \<sqinter> c ; c\<^sup>\<omega> ; \<top>"
      using semigroup.assoc seq.semigroup_axioms by fastforce
    then show ?thesis
      by (metis (no_types) eq_refl finite_or_infinite_iteration.iter_unfold 
         finite_or_infinite_iteration_axioms infiter_induct 
         seq_distrib_right.inf_seq_distrib seq_distrib_right_axioms)
  qed 
  have rl: "c\<^sup>\<omega> ; \<top> \<sqsubseteq> c\<^sup>\<infinity>"
    by (metis inf_le2 infiter_annil infiter_unfold iter_induct_nil seq_mono_left) 
  thus ?thesis using antisym_conv lr by blast 
qed

lemma infiter_fiter_top:
  shows "c\<^sup>\<infinity> \<sqsubseteq> c\<^sup>\<star> ; \<top>"
  by (metis eq_iff fiter_induct inf_top_left infiter_unfold)

lemma inf_ref_infiter: "c\<^sup>\<omega> \<sqsubseteq> c\<^sup>\<infinity>"
  using infiter_unfold iter_induct_nil by auto

end

end

