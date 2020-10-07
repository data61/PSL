section \<open>Iteration for conjunctive models \label{S:conjunctive-iteration}\<close>

theory Conjunctive_Iteration
imports
  Conjunctive_Sequential
  Iteration
  Infimum_Nat
begin

text \<open>
  Sequential left-distributivity is only supported by conjunctive models
  but does not apply in general. The relational model is one such example.
\<close>

locale iteration_finite_conjunctive = seq_finite_conjunctive + iteration

begin

lemma isolation: "c\<^sup>\<omega> = c\<^sup>\<star> \<sqinter> c\<^sup>\<infinity>"
proof -
  define F where "F = (\<lambda> x. c\<^sup>\<star> \<sqinter> x)"
  define G where "G = (\<lambda> x. c;x)"
  define H where "H = (\<lambda> x. nil \<sqinter> c;x)"

  have FG: "F \<circ> G = (\<lambda> x. c\<^sup>\<star> \<sqinter> c;x)" using F_def G_def by auto
  have HF: "H \<circ> F = (\<lambda> x. nil \<sqinter> c;(c\<^sup>\<star> \<sqinter> x))" using F_def H_def by auto

  have adjoint: "dist_over_sup F" by (simp add: F_def inf_Sup)
  have monoH: "mono H" by (metis H_def inf_mono monoI order_refl seq_mono_right)
  have monoG: "mono G" by (metis G_def inf.absorb_iff2 monoI seq_inf_distrib)

  have "\<forall> x. ((F \<circ> G) x = (H \<circ> F) x)" using FG HF 
    by (metis fiter_unfold inf_sup_aci(2) seq_inf_distrib)
  then have "F (lfp G) = lfp H" using adjoint monoH monoG fusion_lfp_eq by blast
  then have "c\<^sup>\<star> \<sqinter> lfp (\<lambda> x. c;x) = lfp (\<lambda> x. nil \<sqinter> c;x)"
     using F_def G_def H_def by blast
  thus ?thesis by (simp add: infiter_def iter_def)
qed

lemma iter_induct_isolate: "c\<^sup>\<star>;d \<sqinter> c\<^sup>\<infinity> = lfp (\<lambda> x. d \<sqinter> c;x)"
proof - 
  define F where "F = (\<lambda> x. c\<^sup>\<star>;d \<sqinter> x)"
  define G where "G = (\<lambda> x. c;x)"
  define H where "H = (\<lambda> x. d \<sqinter> c;x)"

  have FG: "F \<circ> G = (\<lambda> x. c\<^sup>\<star>;d \<sqinter> c;x)" using F_def G_def by auto
  have HF: "H \<circ> F = (\<lambda> x. d \<sqinter> c;c\<^sup>\<star>;d \<sqinter> c;x)" using F_def H_def weak_seq_inf_distrib
    by (metis comp_apply inf.commute inf.left_commute seq_assoc seq_inf_distrib)
  have unroll: "c\<^sup>\<star>;d = (nil \<sqinter> c;c\<^sup>\<star>);d" using fiter_unfold by auto
  have distribute: "c\<^sup>\<star>;d = d \<sqinter> c;c\<^sup>\<star>;d" by (simp add: unroll inf_seq_distrib)
  have FGx: "(F \<circ> G) x = d \<sqinter> c;c\<^sup>\<star>;d \<sqinter> c;x" using FG distribute by simp

  have adjoint: "dist_over_sup F" by (simp add: F_def inf_Sup)
  have monoH: "mono H" by (metis H_def inf_mono monoI order_refl seq_mono_right)
  have monoG: "mono G" by (metis G_def inf.absorb_iff2 monoI seq_inf_distrib)

  have "\<forall> x. ((F \<circ> G) x = (H \<circ> F) x)" using FGx HF by (simp add: FG distribute)
  then have "F (lfp G) = lfp H" using adjoint monoH monoG fusion_lfp_eq by blast
  then have "c\<^sup>\<star>;d \<sqinter> lfp (\<lambda> x. c;x) = lfp (\<lambda> x. d \<sqinter> c;x)"
     using F_def G_def H_def by blast
  thus ?thesis by (simp add: infiter_def)
qed 

lemma iter_induct_eq: "c\<^sup>\<omega>;d = lfp (\<lambda> x. d \<sqinter> c;x)"
proof -
  have "c\<^sup>\<omega>;d = c\<^sup>\<star>;d \<sqinter> c\<^sup>\<infinity>;d" by (simp add: isolation inf_seq_distrib)
  then have "c\<^sup>\<star>;d \<sqinter> c\<^sup>\<infinity>;d = c\<^sup>\<star>;d \<sqinter> c\<^sup>\<infinity>" by (simp add: infiter_annil)
  then have "c\<^sup>\<star>;d \<sqinter> c\<^sup>\<infinity> = lfp (\<lambda> x. d \<sqinter> c;x)" by (simp add: iter_induct_isolate)
  thus ?thesis 
    by (simp add: \<open>c\<^sup>\<omega> ; d = c\<^sup>\<star> ; d \<sqinter> c\<^sup>\<infinity> ; d\<close> \<open>c\<^sup>\<star> ; d \<sqinter> c\<^sup>\<infinity> ; d = c\<^sup>\<star> ; d \<sqinter> c\<^sup>\<infinity>\<close>)
qed

lemma iter_induct: "d \<sqinter> c;x \<sqsubseteq> x \<Longrightarrow> c\<^sup>\<omega>;d \<sqsubseteq> x"
  by (simp add: iter_induct_eq lfp_lowerbound)

lemma iter_isolate: "c\<^sup>\<star>;d \<sqinter> c\<^sup>\<infinity> = c\<^sup>\<omega>;d"
  by (simp add: iter_induct_eq iter_induct_isolate)

lemma iter_isolate2: "c;c\<^sup>\<star>;d \<sqinter> c\<^sup>\<infinity> = c;c\<^sup>\<omega>;d"
  by (metis infiter_unfold iter_isolate seq_assoc seq_inf_distrib)

lemma iter_decomp: "(c \<sqinter> d)\<^sup>\<omega> = c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<omega>"
proof (rule antisym)
  have      "c;c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<omega> \<sqinter> (d;c\<^sup>\<omega>)\<^sup>\<omega> \<sqsubseteq> c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<omega>" by (metis inf_commute order.refl inf_seq_distrib seq_nil_left iter_unfold)
  thus "(c \<sqinter> d)\<^sup>\<omega> \<sqsubseteq> c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<omega>" by (metis inf.left_commute iter_induct_nil iter_unfold seq_assoc inf_seq_distrib)
next
  have "(c;(c \<sqinter> d)\<^sup>\<omega> \<sqinter> d;(c \<sqinter> d)\<^sup>\<omega>) \<sqinter> nil \<sqsubseteq> (c \<sqinter> d)\<^sup>\<omega>" by (metis inf_commute order.refl inf_seq_distrib iter_unfold) 
  then have a: "c\<^sup>\<omega>;(d;(c \<sqinter> d)\<^sup>\<omega> \<sqinter> nil) \<sqsubseteq> (c \<sqinter> d)\<^sup>\<omega>" 
  proof -
    have "nil \<sqinter> d;(c \<sqinter> d)\<^sup>\<omega> \<sqinter> c;(c \<sqinter> d)\<^sup>\<omega> \<sqsubseteq> (c \<sqinter> d)\<^sup>\<omega>"
      by (metis eq_iff inf.semigroup_axioms inf_commute inf_seq_distrib iter_unfold semigroup.assoc)
    thus ?thesis using iter_induct_eq by (metis inf_sup_aci(1) iter_induct) 
  qed
  then have "d;c\<^sup>\<omega>;(d;(c \<sqinter> d)\<^sup>\<omega> \<sqinter> nil) \<sqinter> nil \<sqsubseteq> d;(c \<sqinter> d)\<^sup>\<omega> \<sqinter> nil" by (metis inf_mono order.refl seq_assoc seq_mono) 
  then have "(d;c\<^sup>\<omega>)\<^sup>\<omega> \<sqsubseteq> d;(c \<sqinter> d)\<^sup>\<omega> \<sqinter> nil" by (metis inf_commute iter_induct_nil) 
  then have "c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<omega> \<sqsubseteq> c\<^sup>\<omega>;(d;(c \<sqinter> d)\<^sup>\<omega> \<sqinter> nil)" by (metis order.refl seq_mono) 
  thus "c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<omega> \<sqsubseteq> (c \<sqinter> d)\<^sup>\<omega>" using a refine_trans by blast
qed

lemma iter_leapfrog_var: "(c;d)\<^sup>\<omega>;c \<sqsubseteq> c;(d;c)\<^sup>\<omega>"
proof -
  have "c \<sqinter> c;d;c;(d;c)\<^sup>\<omega> \<sqsubseteq> c;(d;c)\<^sup>\<omega>"
    by (metis iter_unfold order_refl seq_assoc seq_inf_distrib seq_nil_right)
  thus ?thesis using iter_induct_eq by (metis iter_induct seq_assoc) 
qed

lemma iter_leapfrog: "c;(d;c)\<^sup>\<omega> = (c;d)\<^sup>\<omega>;c"
proof (rule antisym)
  show "(c;d)\<^sup>\<omega>;c \<sqsubseteq> c;(d;c)\<^sup>\<omega>" by (metis iter_leapfrog_var)
next
  have "(d;c)\<^sup>\<omega> \<sqsubseteq> ((d;c)\<^sup>\<omega>;d);c \<sqinter> nil" by (metis inf.bounded_iff order.refl seq_assoc seq_mono iter_unfold iter1 iter2) 
  then have "(d;c)\<^sup>\<omega> \<sqsubseteq> (d;(c;d)\<^sup>\<omega>);c \<sqinter> nil" by (metis inf.absorb_iff2 inf.boundedE inf_assoc iter_leapfrog_var inf_seq_distrib)
  then have "c;(d;c)\<^sup>\<omega> \<sqsubseteq> c;d;(c;d)\<^sup>\<omega>;c \<sqinter> nil;c" using inf.bounded_iff seq_assoc seq_mono_right seq_nil_left seq_nil_right by fastforce
  thus "c;(d;c)\<^sup>\<omega> \<sqsubseteq> (c;d)\<^sup>\<omega>;c" by (metis inf_commute inf_seq_distrib iter_unfold) 
qed

lemma fiter_leapfrog: "c;(d;c)\<^sup>\<star> = (c;d)\<^sup>\<star>;c"
proof -
  have lr: "c;(d;c)\<^sup>\<star> \<sqsubseteq> (c;d)\<^sup>\<star>;c"
  proof -
    have "(d ; c)\<^sup>\<star> = nil \<sqinter> d ; c ; (d ; c)\<^sup>\<star>"
      by (meson finite_iteration.fiter_unfold finite_iteration_axioms)
    then show ?thesis
      by (metis fiter_induct seq_assoc seq_distrib_left.weak_seq_inf_distrib 
          seq_distrib_left_axioms seq_nil_right)
  qed
  have rl: "(c;d)\<^sup>\<star>;c \<sqsubseteq> c;(d;c)\<^sup>\<star>" 
  proof -
    have a1: "(c;d)\<^sup>\<star>;c = c \<sqinter> c;d;(c;d)\<^sup>\<star>;c"
       by (metis finite_iteration.fiter_unfold finite_iteration_axioms 
           inf_seq_distrib seq_nil_left)  
    have a2: "(c;d)\<^sup>\<star>;c \<sqsubseteq> c;(d;c)\<^sup>\<star> \<longleftrightarrow> c \<sqinter> c;d;(c;d)\<^sup>\<star>;c \<sqsubseteq> c;(d;c)\<^sup>\<star>" by (simp add: a1)  
    then have a3: "... \<longleftrightarrow> c;( nil \<sqinter> d;(c;d)\<^sup>\<star>;c) \<sqsubseteq> c;(d;c)\<^sup>\<star>"
       by (metis a1 eq_iff fiter_unfold lr seq_assoc seq_inf_distrib seq_nil_right)  
    have a4: "(nil \<sqinter> d;(c;d)\<^sup>\<star>;c) \<sqsubseteq> (d;c)\<^sup>\<star> \<Longrightarrow> c;( nil \<sqinter> d;(c;d)\<^sup>\<star>;c) \<sqsubseteq> c;(d;c)\<^sup>\<star>"
       using seq_mono_right by blast
    have a5: "(nil \<sqinter> d;(c;d)\<^sup>\<star>;c) \<sqsubseteq> (d;c)\<^sup>\<star>"
      proof -
        have f1: "d ; (c ; d)\<^sup>\<star> ; c \<sqinter> nil = d ; ((c ; d)\<^sup>\<star> ; c) \<sqinter> nil \<sqinter> nil"
           by (simp add: seq_assoc)
        have "d ; c ; (d ; (c ; d)\<^sup>\<star> ; c \<sqinter> nil) = d ; ((c ; d)\<^sup>\<star> ; c)"
           by (metis (no_types) a1 inf_sup_aci(1) seq_assoc 
                seq_finite_conjunctive.seq_inf_distrib seq_finite_conjunctive_axioms 
                seq_nil_right)
        then show ?thesis
           using f1 by (metis (no_types) finite_iteration.fiter_induct finite_iteration_axioms 
                           inf.cobounded1 inf_sup_aci(1) seq_nil_right)
     qed
   thus ?thesis using a2 a3 a4 by blast 
  qed
  thus ?thesis by (simp add: eq_iff lr)
qed

end


locale iteration_infinite_conjunctive = seq_infinite_conjunctive + iteration + infimum_nat

begin

lemma fiter_seq_choice: "c\<^sup>\<star> = (\<Sqinter>i::nat. c \<^sup>;^ i)"
proof (rule antisym)
  show "c\<^sup>\<star> \<sqsubseteq> (\<Sqinter>i. c \<^sup>;^ i)"
  proof (rule INF_greatest) 
    fix i
    show "c\<^sup>\<star> \<sqsubseteq> c \<^sup>;^ i"
      proof (induct i type: nat)
        case 0
        show "c\<^sup>\<star> \<sqsubseteq> c \<^sup>;^ 0" by (simp add: fiter0)
      next
        case (Suc n)
        have "c\<^sup>\<star> \<sqsubseteq> c ; c\<^sup>\<star>" by (metis fiter_unfold inf_le2)
        also have "... \<sqsubseteq> c ; (c \<^sup>;^ n)" using Suc.hyps by (simp only: seq_mono_right)
        also have "... = c \<^sup>;^ Suc n" by simp
        finally show "c\<^sup>\<star> \<sqsubseteq> c \<^sup>;^ Suc n" .
      qed
  qed
next
  have "(\<Sqinter>i. c \<^sup>;^ i) \<sqsubseteq> (c \<^sup>;^ 0) \<sqinter> (\<Sqinter>i. c \<^sup>;^ Suc i)"
    by (meson INF_greatest INF_lower UNIV_I le_inf_iff)
  also have "... = nil \<sqinter> (\<Sqinter>i. c ; (c \<^sup>;^ i))" by simp
  also have "... = nil \<sqinter> c ; (\<Sqinter>i. c \<^sup>;^ i)" by (simp add: seq_INF_distrib)
  finally show "(\<Sqinter>i. c \<^sup>;^ i) \<sqsubseteq> c\<^sup>\<star>" using fiter_induct by fastforce
qed

lemma fiter_seq_choice_nonempty: "c ; c\<^sup>\<star> = (\<Sqinter>i\<in>{i. 0 < i}. c \<^sup>;^ i)"
proof -
  have "(\<Sqinter>i\<in>{i. 0 < i}. c \<^sup>;^ i) = (\<Sqinter>i. c \<^sup>;^ (Suc i))" by (simp add: INF_nat_shift)
  also have "... = (\<Sqinter>i. c ; (c \<^sup>;^ i))" by simp
  also have "... = c ; (\<Sqinter>i. c \<^sup>;^ i)" by (simp add: seq_INF_distrib_UNIV)
  also have "... = c ; c\<^sup>\<star>" by (simp add: fiter_seq_choice)
  finally show ?thesis by simp
qed

end

locale conj_iteration = cra + iteration_infinite_conjunctive

begin

lemma conj_distrib4: "c\<^sup>\<star> \<iinter> d\<^sup>\<star> \<sqsubseteq> (c \<iinter> d)\<^sup>\<star>"
proof -
  have "c\<^sup>\<star> \<iinter> d\<^sup>\<star> = (nil \<sqinter> (c;c\<^sup>\<star>)) \<iinter> d\<^sup>\<star>" by (metis fiter_unfold) 
  then have "c\<^sup>\<star> \<iinter> d\<^sup>\<star> = (nil \<iinter> d\<^sup>\<star>) \<sqinter> ((c;c\<^sup>\<star>) \<iinter> d\<^sup>\<star>)" by (simp add: inf_conj_distrib) 
  then have "c\<^sup>\<star> \<iinter> d\<^sup>\<star> \<sqsubseteq> nil \<sqinter> ((c;c\<^sup>\<star>) \<iinter> (d;d\<^sup>\<star>))" by (metis conj_idem fiter0 fiter_unfold inf.bounded_iff inf_le2 local.conj_mono)
  then have "c\<^sup>\<star> \<iinter> d\<^sup>\<star> \<sqsubseteq> nil \<sqinter> ((c \<iinter> d);(c\<^sup>\<star> \<iinter> d\<^sup>\<star>))" by (meson inf_mono_right order.trans sequential_interchange) 
  thus ?thesis by (metis seq_nil_right fiter_induct) 
qed

end

end

