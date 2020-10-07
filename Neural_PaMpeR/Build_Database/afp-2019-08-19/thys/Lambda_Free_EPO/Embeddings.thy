(*  Title:       The Embedding Relation for Lambda-Free Higher-Order Terms
    Author:      Alexander Bentkamp <a.bentkamp at vu.nl>, 2018
    Maintainer:  Alexander Bentkamp <a.bentkamp at vu.nl>
*)

section \<open>The Embedding Relation for Lambda-Free Higher-Order Terms\<close>

theory Embeddings
  imports Lambda_Free_RPOs.Lambda_Free_Term Lambda_Free_RPOs.Extension_Orders
begin

subsection \<open>Positions of terms\<close>

datatype dir = Left | Right

fun position_of :: "('s,'v) tm \<Rightarrow> dir list \<Rightarrow> bool" where
  position_of_Nil: "position_of _ [] = True" |
  position_of_Hd: "position_of (Hd _) (_#_) = False" |
  position_of_left: "position_of (App t s) (Left # ds) = position_of t ds" |
  position_of_right: "position_of (App t s) (Right # ds) = position_of s ds"

definition opp :: "dir \<Rightarrow> dir" where
  "opp d = (if d = Right then Left else Right)"

lemma opp_simps[simp]:
  "opp Right = Left" 
  "opp Left = Right"
  using opp_def by auto

lemma shallower_pos: "position_of t (p @ q @ [dq]) \<Longrightarrow> position_of t (p @ [dp])" 
proof (induct p arbitrary:t)
  case Nil
  then show ?case 
    apply (cases t)
     apply (metis position_of_Hd Nil_is_append_conv list.exhaust)
    by (metis (full_types) position_of_Nil position_of_left
        position_of_right dir.exhaust self_append_conv2)
next
  case (Cons a p)
  then show ?case 
    apply (cases a) 
    apply (metis position_of_Hd position_of_left append_Cons args.cases)
    by (metis position_of_Hd position_of_right append_Cons args.cases)
qed

lemma no_position_replicate_num_args: "\<not> position_of t (replicate (num_args t) Left @ [d])"
proof (induct "num_args t" arbitrary:t)
  case 0
  have "is_Hd t" 
    using "0.hyps" args_Nil_iff_is_Hd by auto
  then show ?case
    by (metis position_of.elims(2) snoc_eq_iff_butlast tm.discI(2))
next
  case (Suc n)
  have "is_App t" 
    using Suc.hyps(2) args_Nil_iff_is_Hd by force
  then have "\<not> position_of (fun t) (replicate (num_args (fun t)) dir.Left @ [d])" using Suc.hyps(1)[of "fun t"] 
    by (metis Suc Suc_inject args.elims length_0_conv length_append_singleton nat.distinct(1) tm.sel(4))
  have "\<And>ds. replicate (num_args t) dir.Left @ [d] \<noteq> dir.Right # ds" 
    by (metis \<open>is_App t\<close> args_Nil_iff_is_Hd dir.distinct(1) hd_append hd_replicate length_0_conv list.sel(1) replicate_empty)
  then show ?case using position_of.elims(2)[of t "(replicate (num_args t) dir.Left @ [d])"]
    by (metis position_of_left \<open>\<not> position_of (fun t) (replicate (num_args (fun t)) dir.Left @ [d])\<close> 
    \<open>is_App t\<close> append_Cons args.simps(2) length_append_singleton replicate_Suc tm.collapse(2))
qed

lemma shorten_position:"position_of t (p @ q) \<Longrightarrow> position_of t p"
proof (induct q rule: rev_induct)
case Nil
  then show ?case 
    by simp
next
  case (snoc x xs)
  then show ?case
    by (metis position_of_Nil append_assoc append_butlast_last_id shallower_pos)
qed

subsection \<open>Embedding step\<close>

text \<open>Embedding step at a given position. If the position is not present, default to identity.\<close>

fun emb_step_at :: "dir list \<Rightarrow> dir \<Rightarrow> ('s, 'v) tm  \<Rightarrow> ('s, 'v) tm"  where
  emb_step_at_left:"emb_step_at [] Left (App t s) = t"
| emb_step_at_right:"emb_step_at [] Right (App t s) = s"
| emb_step_at_left_context:"emb_step_at (Left # p) dir (App t s) = App (emb_step_at p dir t) s"
| emb_step_at_right_context:"emb_step_at (Right # p) dir (App t s) = App t (emb_step_at p dir s)"
| emb_step_at_head:"emb_step_at _ _ (Hd h) = Hd h"

abbreviation "emb_step_at' p t == emb_step_at (butlast p) (last p) t"

lemmas emb_step_at_induct = emb_step_at.induct[case_names left right left_context right_context head]

lemma emb_step_at_is_App:"emb_step_at p d u \<noteq> u \<Longrightarrow> is_App u"
  by (metis emb_step_at.simps(5) is_Hd_def)

text \<open>Definition of an embedding step without using positions.\<close>

inductive emb_step (infix "\<rightarrow>\<^sub>e\<^sub>m\<^sub>b" 50) where 
  left: "(App t1 t2) \<rightarrow>\<^sub>e\<^sub>m\<^sub>b t1" |
  right: "(App t1 t2) \<rightarrow>\<^sub>e\<^sub>m\<^sub>b t2" |
  context_left: "t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> (App t u) \<rightarrow>\<^sub>e\<^sub>m\<^sub>b (App s u)" |
  context_right: "t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> (App u t) \<rightarrow>\<^sub>e\<^sub>m\<^sub>b (App u s)"

text \<open>The two definitions of an embedding step are equivalent:\<close>

lemma emb_step_equiv: "emb_step t s \<longleftrightarrow> (\<exists>p d. emb_step_at p d t = s) \<and> t \<noteq> s"
proof
  show "t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> (\<exists>p d. emb_step_at p d t = s) \<and> t \<noteq> s"
  proof (induct t s rule:emb_step.induct) 
    case left
    then show ?case
      by (metis add_Suc_right emb_step_at.simps(1) leD le_add_same_cancel1 le_imp_less_Suc tm.size(4) zero_order(1))
  next
    case right
    then show ?case
      by (metis add.right_neutral add_le_cancel_left antisym emb_step_at.simps(2) le_add_same_cancel2 le_imp_less_Suc length_greater_0_conv list.size(3) tm.size(4) zero_order(1))
  next
    case (context_left t s)
    obtain p d where "emb_step_at p d t = s" 
      using context_left.hyps(2) by blast
    then have "\<And>u. emb_step_at (Left # p) d (App t u) = App s u"
      by (metis emb_step_at.simps(3))
    then show ?case
      using context_left.hyps(2) by blast
  next
    case (context_right t s)
    obtain p d where "emb_step_at p d t = s" 
      using context_right.hyps(2) by blast
    then have "\<And>u. emb_step_at (Right # p) d (App u t) = App u s"
      by (metis emb_step_at.simps(4))
    then show ?case
      using context_right.hyps(2) by blast
  qed
  show "(\<exists>p d. emb_step_at p d t = s) \<and> t \<noteq> s \<Longrightarrow> t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s"
  proof -
    assume "(\<exists>p d. emb_step_at p d t = s) \<and> t \<noteq> s"
    then obtain p d where "emb_step_at p d t = s" "t \<noteq> s" by blast
    then show ?thesis
    proof (induct arbitrary:t rule:emb_step_at_induct)
      case (left u1 u2)
      show ?case using left(1)
        apply (rule emb_step_at.elims) 
        using emb_step.left by blast+
    next
      case (right u1 u2)
      show ?case  using right(1)
        apply (rule emb_step_at.elims) 
        using emb_step.right by blast+
    next
      case (left_context u1 u2 t' s')
      show ?case 
        by (metis emb_step_at_left_context emb_step.simps emb_step_at_is_App left_context.hyps left_context.prems(1) left_context.prems(2) 
            tm.collapse(2) tm.inject(2)) 
    next
      case (right_context u1 u2 t' s')
      show ?case 
        by (metis emb_step_at_right_context emb_step.simps emb_step_at_is_App right_context.hyps right_context.prems(1) right_context.prems(2) tm.collapse(2) tm.inject(2))          
    next
      case (head uu uv h)
      show ?case using head(1)
        apply (rule emb_step_at.elims)
        using emb_step.left apply blast
        using emb_step.right apply blast
        apply simp_all
        using head.prems(2) by blast
    qed
  qed
qed

lemma emb_step_fun: "is_App t \<Longrightarrow> t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b (fun t)"
  by (metis emb_step.intros(1) tm.collapse(2))

lemma emb_step_arg: "is_App t \<Longrightarrow> t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b (arg t)"
  by (metis emb_step.intros(2) tm.collapse(2))

lemma emb_step_size: "t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> size t > size s" 
  by (induction rule: emb_step.induct; simp_all) 

lemma emb_step_vars: "t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> vars s \<subseteq> vars t" 
  by (induction rule: emb_step.induct, auto)

lemma emb_step_equiv': "emb_step t s \<longleftrightarrow> (\<exists>p. p \<noteq> [] \<and> emb_step_at' p t = s) \<and> t \<noteq> s"
  using butlast_snoc emb_step_equiv last_snoc
  by (metis snoc_eq_iff_butlast)

lemma position_if_emb_step_at: "emb_step_at p d t = u \<Longrightarrow> t \<noteq> u \<Longrightarrow> position_of t (p @ [d])"
proof (induct p arbitrary:t u)
  case Nil
  then show ?case by (metis emb_step_at_head position_of_Nil append_self_conv2 list.sel(3) position_of.elims(3))
next
  case (Cons a p)
  then show ?case  
  proof (cases t)
    case (Hd x)
    then show ?thesis using Cons by simp
  next
    case (App t1 t2)
    then show ?thesis using Cons  apply (cases a) apply simp 
      apply blast 
      by auto
  qed
qed

lemma emb_step_at_if_position:
  assumes
    "position_of t (p @ [d])"
  shows "t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b emb_step_at p d t" 
  using assms proof (induct p arbitrary:t)
  case Nil
  then show ?case
    by (cases d;cases t;simp add: emb_step.left emb_step.right)
next
  case (Cons a p)
  then show ?case
    apply (cases a) 
     apply (cases t)  
      apply (simp_all add: context_left context_right)
    apply (cases t) 
    by (simp_all add: context_left context_right)
qed

subsection \<open>Embedding relation\<close>

text \<open>Definition of an embedding as a sequence of embedding steps at given positions:\<close>

fun emb_at :: "(dir list \<times> dir) list \<Rightarrow> ('s, 'v) tm  \<Rightarrow> ('s, 'v) tm" where
  emb_at_Nil: "emb_at [] t = t" |
  emb_at_Cons: "emb_at ((p,d) # ps) t = emb_step_at p d (emb_at ps t)"

text \<open>Definition of an embedding without using positions:\<close>

inductive emb (infix "\<unrhd>\<^sub>e\<^sub>m\<^sub>b" 50) where
  refl: "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b t" |
  step: "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b u \<Longrightarrow> u \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"

abbreviation emb_neq (infix "\<rhd>\<^sub>e\<^sub>m\<^sub>b" 50) where "emb_neq t s \<equiv> t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s \<and> t \<noteq> s"

text \<open>The two definitions coincide:\<close>

lemma emb_equiv: "(t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s) = (\<exists>ps. emb_at ps t = s)"
proof
  show "\<exists>ps. emb_at ps t = s \<Longrightarrow> t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
  proof -
    assume "\<exists>ps. emb_at ps t = s"
    then obtain ps where "emb_at ps t = s"
      by blast
    then show ?thesis 
    proof (induct ps arbitrary:s)
      case Nil
      then show ?case by (simp add: emb.refl)
    next
      case (Cons a ps)
      show ?case 
        using Cons(2) apply (rule emb_at.elims)
       apply simp
       by (metis Cons.hyps emb.simps emb_step_equiv list.inject)
    qed
  qed
next
  show "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> \<exists>ps. emb_at ps t = s"
  proof (induct rule: emb.induct)
    case (refl t)
    then show ?case
      using emb_at_Nil by blast
  next
    case (step t u s)
    then show ?case
      by (metis emb_at_Cons emb_step_equiv)
  qed
qed

lemma emb_at_trans: "emb_at ps t = u \<Longrightarrow> emb_at qs u = s \<Longrightarrow> emb_at (qs @ ps) t = s"
  by (induct qs arbitrary:s; auto)

lemma emb_trans: "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b u \<Longrightarrow> u \<unrhd>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
  by (metis emb_at_trans emb_equiv)

lemma emb_step_is_emb: "t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
  by (meson emb.simps)

lemma emb_size: "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> size t \<ge> size s" 
  apply (induction rule: emb.induct)
  apply simp
  using emb_step_size by fastforce

lemma emb_prepend_step: "t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b u \<Longrightarrow> u \<unrhd>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
  using emb_step_is_emb emb_trans by blast

lemma sub_emb: "sub s t \<Longrightarrow> t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
proof (induction rule:sub.induct)
  case (sub_refl s)
  then show ?case 
    by (simp add: emb.refl)
next
  case (sub_fun s t u)
  then show ?case 
    using emb_prepend_step right by blast
next
  case (sub_arg s t u)
  then show ?case
    using emb_prepend_step left by blast
qed

lemma sequence_emb_steps: "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s \<longleftrightarrow> (\<exists>us. us\<noteq>[] \<and> hd us = t \<and> last us = s \<and> (\<forall>i. Suc i < length us \<longrightarrow> us ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b us ! Suc i))"
proof
  show "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> \<exists>us. us\<noteq>[] \<and> hd us = t \<and> last us = s \<and> (\<forall>i. Suc i < length us \<longrightarrow> us ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b us ! Suc i)"
  proof (induct rule:emb.induct)
    case (refl t)
    then show ?case 
      using Suc_less_eq add.right_neutral add_Suc_right append_Nil last_snoc list.sel(1) list.size(3) list.size(4) not_less_zero
      by auto
  next
    case (step t u s)
    then obtain us where 
      "us \<noteq> []" 
      "hd us = t" 
      "last us = u" 
      "\<forall>i. Suc i < length us \<longrightarrow> us ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b us ! Suc i" by blast
    then have "hd (us @ [s]) = t" "last (us @ [s]) = s" by simp_all
    moreover have  "(\<forall>i. Suc i < length (us @ [s]) \<longrightarrow> (us @ [s]) ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b (us @ [s]) ! Suc i)" 
      by (metis (mono_tags, lifting) Suc_less_eq \<open>\<forall>i. Suc i < length us \<longrightarrow> us ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b us ! Suc i\<close> \<open>last us = u\<close> \<open>us \<noteq> []\<close> 
           append_butlast_last_id length_append_singleton less_antisym nth_append nth_append_length step.hyps(3))
    ultimately show ?case by blast
  qed
  show "\<exists>us. us \<noteq> [] \<and> hd us = t \<and> last us = s \<and> (\<forall>i. Suc i < length us \<longrightarrow> us ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b us ! Suc i) \<Longrightarrow> t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
  proof -
    assume "\<exists>us. us \<noteq> [] \<and> hd us = t \<and> last us = s \<and> (\<forall>i. Suc i < length us \<longrightarrow> us ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b us ! Suc i)"
    then obtain us where "us \<noteq> []" "hd us = t" "last us = s" "\<forall>i. Suc i < length us \<longrightarrow> us ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b us ! Suc i" by blast
    then show ?thesis
    proof (induct us arbitrary:t)
      case Nil
      then show ?case by simp
    next
      case (Cons a us)
      then show ?case
        using emb.refl emb_step_is_emb emb_trans hd_conv_nth by fastforce
    qed
  qed
qed

lemma emb_induct_reverse [consumes 1, case_names refl step]:
  assumes
emb: "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s" and
refl: "\<And>t. P t t" and
step: "\<And>t u s. t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b u \<Longrightarrow> u \<unrhd>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> P u s \<Longrightarrow> P t s"
shows 
"P t s"
proof -
  obtain us where "us\<noteq>[]" "hd us = t" "last us = s" "\<forall>i. Suc i < length us \<longrightarrow> us ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b us ! Suc i"
    using emb sequence_emb_steps by blast
  define us' where "us' == tl us"
  then have "last ([t] @ us') = s" "\<forall>i. i < length us' \<longrightarrow> ([t] @ us') ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b ([t] @ us') ! Suc i" 
    using \<open>hd us = t\<close> \<open>last us = s\<close> \<open>us \<noteq> []\<close> apply force 
    using \<open>\<forall>i. Suc i < length us \<longrightarrow> us ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b us ! Suc i\<close> \<open>hd us = t\<close> \<open>us \<noteq> []\<close> us'_def by force
  then show ?thesis
  proof (induct us' arbitrary:t)
    case Nil
  then show ?case
    by (simp add: local.refl)
  next
    case (Cons a us')
    then have "P a s" 
      by (metis Suc_mono append_Cons append_Nil last.simps length_Cons list.discI nth_Cons_Suc)
    have "t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b a" 
      using Cons.prems(2) by auto
    have "a \<unrhd>\<^sub>e\<^sub>m\<^sub>b s" unfolding sequence_emb_steps 
      by (metis append_Cons append_Nil last_append list.sel(1) list.simps(3) local.Cons(2) local.Cons(3) nth_Cons_Suc)
    show ?case using step[OF \<open>t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b a\<close> \<open>a \<unrhd>\<^sub>e\<^sub>m\<^sub>b s\<close> \<open>P a s\<close>] .
  qed
qed

lemma emb_cases_reverse [consumes 1, case_names refl step]: 
  "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> (\<And>t'. t = t' \<Longrightarrow> s = t' \<Longrightarrow> P) \<Longrightarrow> (\<And>t' u s'. t = t' \<Longrightarrow> s = s' \<Longrightarrow> t' \<rightarrow>\<^sub>e\<^sub>m\<^sub>b u \<Longrightarrow> u \<unrhd>\<^sub>e\<^sub>m\<^sub>b s' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule:emb_induct_reverse; blast+)

lemma emb_vars: "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> vars s \<subseteq> vars t"
  apply (induct rule: emb.induct)
   apply simp
  using emb_step_vars by auto

lemma ground_emb: "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> ground t \<Longrightarrow> ground s"
  using emb_vars by blast

lemma arg_emb: "s \<in> set (args t) \<Longrightarrow> t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s" 
  by (simp add: sub_args sub_emb)

lemma emb_step_at_subst:
  assumes
    "position_of t (p @ [d])"
  shows
    "emb_step_at p d (subst \<rho> t) = subst \<rho> (emb_step_at p d t)"
using assms proof (induction p arbitrary:t)
  case Nil
  then obtain t1 t2 where "t = App t1 t2" 
    using position_of_Hd append_Nil tm.collapse(1) 
    by (metis tm.collapse(2))
  then show ?case 
    by (cases d; simp add: \<open>t = App t1 t2\<close>)
next
  case (Cons a p)
  then obtain t1 t2 where "t = App t1 t2" 
    using position_of.elims(2) by blast
  then show ?case 
    using Cons.IH Cons.prems by (cases a;auto)
qed

lemma emb_step_subst: "t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> subst \<rho> t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b subst \<rho> s"
  by (induct rule:emb_step.induct;
      simp_all add: emb_step.left emb_step.right context_left context_right)

lemma emb_subst: "t  \<unrhd>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> subst \<rho> t \<unrhd>\<^sub>e\<^sub>m\<^sub>b subst \<rho> s"
  apply (induct rule:emb.induct)
  apply (simp add: emb.refl)
  using emb.step emb_step_subst by blast

lemma emb_size_neq:
  assumes
    "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s" "t \<noteq> s"
  shows 
    "size t > size s"
  by (metis assms(1) assms(2) emb_cases_reverse emb_size emb_step_size leD le_imp_less_or_eq)

subsection \<open>How are positions preserved under embedding steps?\<close>

text \<open>Disjunct positions are preserved: For example, [L,R] is a position of f a (g b). When performing
an embedding step at [R,R] to obtain f a b, the position [L,R] still exists. (More precisely, it even
contains the same subterm, namely a.)\<close>

lemma pos_emb_step_at_disjunct:
  assumes
"take (length q) p \<noteq> q"
"take (length p) q \<noteq> p"
shows
"position_of t (p @ [d1]) \<longleftrightarrow> position_of  (emb_step_at q d2 t) (p @ [d1])"
  using assms
proof (induct "length p + length q" arbitrary:t p q rule:less_induct)
  case less
  then show ?case
  proof (cases "is_Hd t \<or> p = [] \<or> q = []")
    case True
    then show ?thesis
      by (metis emb_step_at_is_App less.prems(1) less.prems(2) list.size(3) take_eq_Nil)
  next
    case False
    then obtain t1 t2 p0 p' q0 q' where "t = App t1 t2" "p = p0 # p'" "q = q0 # q'"
      by (metis list.collapse tm.collapse(2))
    then show ?thesis 
      apply (cases p0; cases q0) 
      using less.hyps less.prems(1) less.prems(2) by auto
  qed
qed

text \<open>Even if only the last element of a position differs from the position of an embedding step, that
position is preserved. For example, [L] is a position of f (g b). After performing an embedding step
at [R,R] to obtain f b, the position [L] still exists. (More precisely, it even
contains the same subterm, namely f.)\<close>

lemma pos_emb_step_at_opp:
    "position_of t (p@[d1]) \<longleftrightarrow> position_of (emb_step_at (p @ [opp d1] @ q) d2 t) (p@[d1])"
proof (induct p arbitrary:t)
  case Nil
  then show ?case by (cases t, simp, cases d1, simp_all)
next
  case (Cons a p)
  then show ?case 
    apply (cases a) 
    apply (metis emb_step_at_left_context position_of_left append_Cons emb_step_at_is_App tm.collapse(2))
    by (metis emb_step_at_right_context position_of_right append_Cons emb_step_at_is_App tm.collapse(2))
qed

text \<open>Positions are preserved under embedding steps below them:\<close>

lemma pos_emb_step_at_nested:
  shows "position_of (emb_step_at (p @ [d1] @ q) d2 t) (p @ [d1]) \<longleftrightarrow> position_of t (p @ [d1])"
proof (induct p arbitrary:t)
  case Nil
  then show ?case by (cases t, simp, cases d1, simp_all)
next
  case (Cons a p)
  then show ?case 
    apply (cases a;cases t) 
    using Cons.hyps Cons.prems by auto 
qed

subsection "Swapping embedding steps"

text \<open>The order of embedding steps at disjunct position can be changed freely:\<close>

lemma swap_disjunct_emb_step_at:
  assumes
    "length p \<le> length q \<Longrightarrow> take (length p) q \<noteq> p" "length q \<le> length p \<Longrightarrow>take (length q) p \<noteq> q"
  shows
    "emb_step_at q d2 (emb_step_at p d1 t) = emb_step_at p d1 (emb_step_at q d2 t)"
  using assms
proof (induct "length p + length q" arbitrary:t p q rule:less_induct)
  case less
  then show ?case
  proof (cases "is_Hd t \<or> p = [] \<or> q = []")
    case True
    then show ?thesis
      using emb_step_at_is_App less.prems(1) less.prems(2) list.size(3) take_eq_Nil 
      by (metis le_zero_eq nat_le_linear)
  next
    case False
    then obtain t1 t2 p0 p' q0 q' where "t = App t1 t2" "p = p0 # p'" "q = q0 # q'"
      by (metis list.collapse tm.collapse(2))
    then show ?thesis 
      apply (cases p0; cases q0)
      using less.hyps less.prems(1) less.prems(2) by auto
  qed
qed

text \<open>An embedding step inside the branch that is removed in a second embedding step is useless. 
For example, the embedding f (g b) ->emb f b ->emb f can achieved using a single step f (g b) ->emb f.\<close>

lemma merge_emb_step_at:
  "emb_step_at p d1 (emb_step_at (p @ [opp d1] @ q) d2 t) = emb_step_at p d1 t"
proof (induct p arbitrary:t)
  case Nil
  then show ?case by (cases t, simp, cases d1, simp_all)
next
  case (Cons a p)
  then show ?case 
    apply (cases a) 
     apply (metis (full_types) emb_step_at_left_context append_Cons emb_step_at_is_App tm.collapse(2))
    by (metis (full_types) emb_step_at_right_context append_Cons emb_step_at_is_App tm.collapse(2))
qed

text \<open>When swapping two embedding steps of a position below another, one of the positions has to be
slightly changed:\<close>

lemma swap_nested_emb_step_at:
    "emb_step_at (p @ q) d2 (emb_step_at p d1 t) = emb_step_at p d1 (emb_step_at (p @ [d1] @ q) d2 t)"
proof (induct p arbitrary:t)
  case Nil
  then show ?case by (cases t, simp, cases d1, simp_all)
next
  case (Cons a p)
  then show ?case 
    apply (cases a;cases t) 
    using Cons.hyps Cons.prems by auto 
qed

subsection "Performing embedding steps in order of a given priority"

text \<open>We want to perform all embedding steps first that modify the head or the number of arguments
of a term. To this end we define the function prio\_emb\_step that performs the embedding step with
the highest priority possible. The priority is given by a function "prio" from positions to nats, where 
the lowest number has the highest priority.\<close>

definition prio_emb_pos :: "(dir list \<Rightarrow> nat) \<Rightarrow> ('s,'v) tm \<Rightarrow> ('s,'v) tm \<Rightarrow> dir list" where
  "prio_emb_pos prio t s = (ARG_MIN prio p. p \<noteq> [] \<and> position_of t p \<and> emb_step_at' p t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s)"

definition prio_emb_step :: "(dir list \<Rightarrow> nat) \<Rightarrow> ('s,'v) tm \<Rightarrow> ('s,'v) tm \<Rightarrow> ('s,'v) tm" where
  "prio_emb_step prio t s = emb_step_at' (prio_emb_pos prio t s) t"

lemma prio_emb_posI:
  "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s \<Longrightarrow> t \<noteq> s \<Longrightarrow> prio_emb_pos prio t s \<noteq> [] \<and> position_of t (prio_emb_pos prio t s) \<and> emb_step_at' (prio_emb_pos prio t s) t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
proof (induct rule:emb_induct_reverse)
  case (refl t)
  then show ?case by simp
next
  case (step t u s)
  obtain p where 0:"p \<noteq> [] \<and> position_of t p \<and> emb_step_at' p t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
    using emb_step_equiv' step.hyps(1) append_butlast_last_id position_if_emb_step_at
    by (metis step.hyps(2))
  then have "prio_emb_pos prio t s \<noteq> [] \<and> position_of t (prio_emb_pos prio t s) \<and> emb_step_at' (prio_emb_pos prio t s) t  \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
    using prio_emb_pos_def step.hyps(2) arg_min_natI by (metis (mono_tags, lifting))
  then show ?case by blast
qed

lemma prio_emb_pos_le:
  assumes "p \<noteq> []" "position_of t p" "emb_step_at' p t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
  shows "prio (prio_emb_pos prio t s) \<le> prio p"
  by (simp add: arg_min_nat_le assms(1) assms(2) assms(3) prio_emb_pos_def)

text \<open>We want an embedding step sequence in which the priority numbers monotonely increase. We can
get such a sequence if the priority function assigns greater values to deeper positions.\<close>

lemma prio_emb_pos_increase:
  assumes
    "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s" "t \<noteq> s" "prio_emb_step prio t s \<noteq> s" and
    valid_prio: "\<And>p q dp dq. prio (p @ [dp]) > prio (q @ [dq]) \<Longrightarrow> take (length p) q \<noteq> p" 
  shows
    "prio (prio_emb_pos prio t s) \<le> prio (prio_emb_pos prio (prio_emb_step prio t s) s)" 
    (is "prio ?p1 \<le> prio ?p2")
proof (rule ccontr)
  assume contr: "\<not> prio ?p1 \<le> prio ?p2"
  have "take (length (butlast ?p1)) (butlast ?p2) \<noteq> (butlast ?p1)"
    using contr valid_prio
    by (metis append_butlast_last_id assms(1) assms(2) assms(3) not_le_imp_less prio_emb_posI prio_emb_step_def)
  then have butlast_neq: "butlast ?p2 \<noteq> butlast ?p1" 
    by auto

  define u where "u = prio_emb_step prio (prio_emb_step prio t s) s"
  then have "u \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
    by (metis assms(1) assms(2) assms(3) prio_emb_posI prio_emb_step_def)

  define p where "p = butlast ?p2"
  define q where "q = drop (Suc (length (butlast ?p2))) (butlast ?p1)"
  define dp where "dp = last ?p2"
  define dq where "dq = last ?p1"
  define f where "f = butlast ?p1 ! length (butlast ?p2)"

  have position: "position_of (prio_emb_step prio t s) ?p2" 
    by (metis assms(1) assms(2) assms(3) prio_emb_posI prio_emb_step_def)

  show False
  proof (cases "take (length p) (butlast ?p1) = p")
    case True
    have "length (butlast ?p1) \<noteq> length p" using butlast_neq 
      using True p_def by auto
    then have "length (butlast ?p1) > length p" 
      using nat_le_linear True nat_neq_iff by auto
    then have 0:"p @ f # q = butlast ?p1" 
      by (metis True f_def id_take_nth_drop p_def q_def)
    have u1: "u = emb_step_at p dp (emb_step_at (p @ f # q) dq t)"
      unfolding 0 unfolding p_def u_def dp_def dq_def prio_emb_step_def by simp
    show False
    proof (cases "f = dp")
      case True
      then have "u = emb_step_at (p @ q) dq (emb_step_at p dp t)"
        using swap_nested_emb_step_at[of p q dq dp t] u1 by simp
      then have "emb_step_at p dp t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b u \<or> emb_step_at p dp t = u" 
        using emb_step_equiv[of "emb_step_at p dp t" u] by blast
      then have "emb_step_at p dp t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
        using \<open>u \<unrhd>\<^sub>e\<^sub>m\<^sub>b s\<close> emb_prepend_step by blast
      then have "position_of t ?p2"
        by (metis position "0" position_of_Nil True append_Cons append_Nil2 append_butlast_last_id 
        append_eq_append_conv_if append_eq_conv_conj dp_def dq_def p_def pos_emb_step_at_nested prio_emb_step_def)
      then show ?thesis 
        using assms(1) assms(2) assms(3) contr dp_def p_def prio_emb_posI 
         prio_emb_pos_le prio_emb_step_def
        by (metis \<open>emb_step_at p dp t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s\<close>)
    next
      case False
      then have "opp dp = f" 
        by (metis dir.exhaust opp_def)
      then have "u = emb_step_at p dp t" 
        by (subst merge_emb_step_at[of p dp q dq t, symmetric], simp add: u1)
      then have "position_of t ?p2"
        by (metis Cons_nth_drop_Suc position_of_Nil True dp_def 
            \<open>length p < length (butlast ?p1)\<close> \<open>opp dp = f\<close> append.assoc append_butlast_last_id 
            append_take_drop_id f_def list.sel(1) p_def pos_emb_step_at_opp position take_hd_drop prio_emb_step_def)
      then show ?thesis 
        by (metis dp_def p_def \<open>u = emb_step_at p dp t\<close> \<open>u \<unrhd>\<^sub>e\<^sub>m\<^sub>b s\<close> assms(1) assms(2) assms(3) contr 
         prio_emb_posI prio_emb_pos_le prio_emb_step_def)
    qed
  next
    case False
    define p' where "p' = butlast ?p1"
    have "take (length p') p \<noteq> p'" 
      using \<open>take (length (butlast ?p1)) (butlast ?p2) \<noteq> butlast ?p1\<close> p'_def p_def by blast
    have "take (length p) p' \<noteq> p" using False p'_def by metis
    have "u = emb_step_at p dp (emb_step_at p' dq t)" 
      unfolding u_def prio_emb_step_def 
      by (simp add: dp_def dq_def p'_def p_def prio_emb_step_def)
    then have "u = emb_step_at p' dq (emb_step_at p dp t)"
      using swap_disjunct_emb_step_at[of p p' dq dp t]
      by (simp add: \<open>take (length p') p \<noteq> p'\<close> \<open>take (length p) p' \<noteq> p\<close>)
    then have "emb_step_at p dp t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s" 
      by (metis \<open>u \<unrhd>\<^sub>e\<^sub>m\<^sub>b s\<close> emb_prepend_step emb_step_equiv)
    have "position_of t (p @ [dp])" using pos_emb_step_at_disjunct
      by (metis \<open>take (length p') p \<noteq> p'\<close> \<open>take (length p) p' \<noteq> p\<close> append_butlast_last_id butlast.simps(1) 
      dp_def list.size(3) p'_def p_def position take_eq_Nil prio_emb_step_def)
    then show ?thesis 
      by (metis False \<open>emb_step_at p dp t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s\<close> append_butlast_last_id butlast.simps(1) contr 
      dp_def list.size(3) p_def take_eq_Nil prio_emb_pos_le)
  qed
qed

lemma sequence_prio_emb_steps:
  assumes 
    "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
  shows
    "\<exists>us. us\<noteq>[] \<and> hd us = t \<and> last us = s \<and> 
    (\<forall>i. Suc i < length us \<longrightarrow> (prio_emb_step prio (us ! i) s = us ! Suc i \<and> us ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b us ! Suc i))"
  using assms   
proof (induct t rule:measure_induct_rule[of size])
  case (less t)
  show ?case
  proof (cases "t = s")
    case True
    then show ?thesis by auto
  next
    case False
    then have "prio_emb_pos prio t s \<noteq> []" "emb_step_at' (prio_emb_pos prio t s) t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s"
      using prio_emb_posI less by blast+
    have emb_step1:"t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b emb_step_at' (prio_emb_pos prio t s) t"
      by (simp add: False emb_step_at_if_position less.prems prio_emb_posI)
    have "size (emb_step_at' (prio_emb_pos prio t s) t) < size t"
      by (simp add: False emb_step_at_if_position emb_step_size less.prems(1) prio_emb_posI)
    then obtain us where us_def:
      "us \<noteq> []" 
      "hd us = emb_step_at' (prio_emb_pos prio t s) t" 
      "last us = s" 
      "\<forall>i. Suc i < length us \<longrightarrow> prio_emb_step prio (us ! i) s = us ! Suc i \<and> us ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b us ! Suc i"
      using less(1)[of "emb_step_at' (prio_emb_pos prio t s) t"] emb_step_size 
        \<open>emb_step_at' (prio_emb_pos prio t s) t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s\<close> by blast

    have "t # us \<noteq> []" " hd (t # us) = t" "last (t # us) = s" using us_def by simp_all
    have
      "\<forall>i. Suc i < length (t # us) \<longrightarrow> (prio_emb_step prio ((t # us) ! i) s = (t # us) ! Suc i \<and> (t # us) ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b (t # us) ! Suc i)" 
    proof (rule allI, rule impI)
      fix i assume " Suc i < length (t # us)" 
      show "prio_emb_step prio ((t # us) ! i) s = (t # us) ! Suc i \<and> (t # us) ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b (t # us) ! Suc i"
      proof (cases i)
        case 0
        show ?thesis 
          using "0" emb_step1 hd_conv_nth prio_emb_step_def us_def(1) us_def(2) by fastforce 
      next
        case (Suc nat)
        then show ?thesis 
          using \<open>Suc i < length (t # us)\<close> us_def(4) by auto
      qed 
    qed
    then show ?thesis
      using \<open>hd (t # us) = t\<close> \<open>last (t # us) = s\<close> by blast
  qed
qed

subsection "Embedding steps under arguments"

text \<open>We want to perform positions that modify the head and the umber of arguments first. Formally these
positions can be characterized as "list\_all (op = Left) p". We show here that embeddings at other positions
do not modify the head, the number of arguments. Moreover, for each argument, the argument after the step
is an embedding of the argument before the step. \<close>

lemma emb_step_under_args_head:
  assumes
    "\<not> list_all (\<lambda>x. x = Left) p"
  shows
    "head (emb_step_at p d t) = head t"
  using assms  proof(induction p arbitrary:t)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a p)
  then show ?case 
  proof (cases t)
    case (Hd x)
    then show ?thesis
      by (metis emb_step_at_head)
  next
    case (App t1 t2)
    then show ?thesis 
    proof (cases a)
      case Left
      then show ?thesis using Cons 
        by (simp add: App)
    next
      case Right
      then show ?thesis
        by (metis App emb_step_at_right_context head_App)
    qed
  qed
qed

lemma emb_step_under_args_num_args:
  assumes
    "\<not> list_all (\<lambda>x. x = Left) p"
  shows
    "num_args (emb_step_at p d t) = num_args t"
  using assms 
proof(induction p arbitrary:t)
  case Nil
  then show ?case 
    using list_all_simps(2) by blast
next
  case (Cons a p)
  then show ?case 
  proof (cases t)
    case (Hd x1)
    then show ?thesis
      by (metis emb_step_at_head)
  next
    case (App t1 t2)
    then show ?thesis unfolding App apply (cases a)
      using App Cons.IH Cons.prems(1) by auto
  qed
qed

lemma emb_step_under_args_emb_step:
  assumes
   "\<not> list_all (\<lambda>x. x = Left) p"
   "position_of t (p @ [d])"
 obtains i where
   "i < num_args t"
   "args t ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b args (emb_step_at p d t) ! i" and
   "\<And>j. j < num_args t \<Longrightarrow> i \<noteq> j \<Longrightarrow> args t ! j = args (emb_step_at p d t) ! j"
  using assms 
proof(induction p arbitrary:t thesis)
  case Nil
  then show ?case 
    by simp  
next
  case (Cons a p)
  obtain t1 t2 where App:"t = App t1 t2"
    by (metis Cons.prems(3) emb_step_at_if_position emb_step_at_is_App emb_step_equiv' tm.collapse(2))
  then show ?case
  proof (cases a)
    case Left
    have IH_cond1: "\<not> list_all (\<lambda>x. x = dir.Left) p" 
      using Cons.prems(2) Left by auto
    have IH_cond2: "position_of t1 (p @ [d])" 
      using App Cons.prems(3) Left by auto
    obtain i' where i'_def: 
      "i' < num_args t1"
      "args t1 ! i' \<rightarrow>\<^sub>e\<^sub>m\<^sub>b args (emb_step_at p d t1) ! i'"
      "\<And>j. j < num_args t1 \<Longrightarrow> i' \<noteq> j \<Longrightarrow> args t1 ! j = args (emb_step_at p d t1) ! j"
      using Cons.IH[OF _ IH_cond1 IH_cond2] by blast
    have num_args:"num_args (emb_step_at p d t1) = num_args t1"
      using App Cons.prems(1) Left emb_step_under_args_num_args
      by (simp add: emb_step_under_args_num_args IH_cond1)
    have 1:"i' < num_args t" 
      by (simp add: App i'_def(1) less_SucI)
    have 2:"args t ! i' \<rightarrow>\<^sub>e\<^sub>m\<^sub>b args (emb_step_at (a # p) d t) ! i'" 
      by (simp add: App Left i'_def(1) i'_def(2) nth_append num_args)
    have 3:"\<And>j. j < num_args t \<Longrightarrow> i' \<noteq> j \<Longrightarrow> args t ! j = args (emb_step_at (a # p) d t) ! j"
      by (simp add: App Left i'_def(3) nth_append num_args)
    show ?thesis using Cons.prems(1)[OF 1 2 3] by blast
  next
    case Right
    have 0:"\<And>j. j < num_args t \<Longrightarrow> num_args t - 1 \<noteq> j \<Longrightarrow> args t ! j = args (emb_step_at (a # p) d t) ! j"
      by (metis (no_types, lifting) App Cons.prems(2) emb_step_at_right_context Nitpick.size_list_simp(2) Right args.simps(2) butlast_snoc emb_step_under_args_num_args length_butlast length_tl less_antisym nth_butlast)
    show ?thesis 
      using Cons.prems(1)[of "num_args t - 1"]
      using App Cons.prems(3) Right emb_step_at_if_position 0 by auto
  qed
qed

lemma emb_step_under_args_emb:
  assumes "\<not> list_all (\<lambda>x. x = Left) p"
   "position_of t (p @ [d])"
  shows
    "\<forall>i. i < num_args t \<longrightarrow> args t ! i \<unrhd>\<^sub>e\<^sub>m\<^sub>b args (emb_step_at p d t) ! i"
  by (metis assms emb.simps emb_step_under_args_emb_step)

lemma position_Left_only_subst:
  assumes "list_all (\<lambda>x. x = Left) p" 
    and "position_of (subst \<rho> w) (p @ [d])"
    and "num_args (subst \<rho> w)  = num_args w"
  shows "position_of w (p @ [d])"
  using assms proof (induct p arbitrary:w)
  case Nil
  then show ?case 
    by (metis position_of_Hd position_of_Nil Hd_head_id append_self_conv2 args.simps(1) length_0_conv list.sel(3) position_of.elims(3))
next
  case (Cons a p)
  then show ?case 
  proof (cases w)
    case (Hd x)
    then show ?thesis 
      by (metis Cons.prems(2) Cons.prems(3) position_of_Hd Hd_head_id append_Cons args.simps(1) list.size(3))
  next
    case (App w1 w2)
    have "num_args (subst \<rho> w1) = num_args w1" 
      using App Cons.prems(3) by auto
    then show ?thesis
      by (metis (full_types) App Cons.hyps Cons.prems(1) Cons.prems(2) position_of_left 
          append_Cons list.pred_inject(2) subst.simps(2))
  qed 
qed

subsection \<open>Rearranging embedding steps: first above, then below arguments\<close>

lemma perform_emb_above_vars0:
  assumes 
    "subst \<rho> s \<unrhd>\<^sub>e\<^sub>m\<^sub>b u"
  obtains w where
    "s \<unrhd>\<^sub>e\<^sub>m\<^sub>b w"
    "subst \<rho> w \<unrhd>\<^sub>e\<^sub>m\<^sub>b u"
    "\<forall>w'. w \<rightarrow>\<^sub>e\<^sub>m\<^sub>b w' \<longrightarrow> \<not> subst \<rho> w' \<unrhd>\<^sub>e\<^sub>m\<^sub>b u"
  using assms   
proof (induct s rule:measure_induct_rule[of size])
  case (less s)
  show ?case
  proof (cases "\<forall>w'. s \<rightarrow>\<^sub>e\<^sub>m\<^sub>b w' \<longrightarrow> \<not> subst \<rho> w' \<unrhd>\<^sub>e\<^sub>m\<^sub>b u")
    case True
    then show ?thesis  
      using emb.refl less.prems(1)
      using less.prems(2) by blast
  next
    case False
    then show ?thesis 
      by (meson emb_step_is_emb emb_step_size emb_trans less.hyps less.prems(1))
  qed
qed
  
lemma emb_only_below_vars:
  assumes 
    "subst \<rho> s \<unrhd>\<^sub>e\<^sub>m\<^sub>b u"
    "s \<unrhd>\<^sub>e\<^sub>m\<^sub>b w"
    "is_Sym (head w)"
    "subst \<rho> w \<unrhd>\<^sub>e\<^sub>m\<^sub>b u"
    "\<forall>w'. w \<rightarrow>\<^sub>e\<^sub>m\<^sub>b w' \<longrightarrow> \<not> subst \<rho> w' \<unrhd>\<^sub>e\<^sub>m\<^sub>b u"
  obtains ws where
    "ws \<noteq> []"
    "hd ws = subst \<rho> w"
    "last ws = u"
    "\<forall>i. Suc i < length ws \<longrightarrow> 
      (\<exists>p d. emb_step_at p d (ws ! i) = ws ! Suc i \<and> \<not> list_all (\<lambda>x. x = Left) p)"
    "\<forall>i. i < length ws \<longrightarrow> head (ws ! i) = head w \<and> num_args (ws ! i) = num_args w"
    "\<forall>i. i < length ws \<longrightarrow> (\<forall>k. k < num_args w \<longrightarrow> args (subst \<rho> w) ! k \<unrhd>\<^sub>e\<^sub>m\<^sub>b args (ws ! i) ! k)"
proof -
  define prio :: "dir list \<Rightarrow> nat" where "prio = (\<lambda>p. if list_all (\<lambda>x. x = Left) (butlast p) then 0 else 1)"
  obtain ws where ws_def:
    "ws \<noteq> []"
    "hd ws = subst \<rho> w"
    "last ws = u"
    "\<forall>i. Suc i < length ws \<longrightarrow> prio_emb_step prio (ws ! i) u = ws ! Suc i \<and> ws ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b ws ! Suc i"
    using \<open>subst \<rho> w \<unrhd>\<^sub>e\<^sub>m\<^sub>b u\<close> sequence_prio_emb_steps by blast

  have ws_emb_u:"\<forall>i. Suc i < length ws \<longrightarrow> ws ! i \<noteq> u \<and> ws ! i \<unrhd>\<^sub>e\<^sub>m\<^sub>b u"
  proof (rule allI)
    {
      fix j assume "Suc j < length ws"
      then have "ws ! (length ws - (Suc (Suc j))) \<noteq> u  \<and> ws ! (length ws - (Suc (Suc j))) \<unrhd>\<^sub>e\<^sub>m\<^sub>b u"
      proof (induction j)
        case 0
        have "prio_emb_step prio (ws ! (length ws - Suc (Suc 0))) u = ws ! (length ws - (Suc 0))"
          using "0.prems" Suc_diff_Suc ws_def(4) by auto
        then show ?case 
          using "0.prems" One_nat_def Suc_diff_Suc Suc_lessD diff_Suc_less emb_step_equiv last_conv_nth ws_def(1) ws_def(3) ws_def(4)
          by (metis emb_step_is_emb)
      next
        case (Suc j)
        then have "ws ! (length ws - (Suc (Suc (Suc j)))) \<rightarrow>\<^sub>e\<^sub>m\<^sub>b ws ! (length ws - Suc (Suc j))"
          by (metis Suc_diff_Suc diff_Suc_less length_greater_0_conv ws_def(1) ws_def(4))
        then show ?case using emb_size_neq
          by (metis Suc.IH Suc.prems Suc_lessD emb_size emb_step_is_emb emb_trans leD)
      qed 
    }
    note 0 = this
    fix i
    show "Suc i < length ws \<longrightarrow> ws ! i \<noteq> u \<and> ws ! i \<unrhd>\<^sub>e\<^sub>m\<^sub>b u" using 0[of "length ws - Suc (Suc i)"]
      using Suc_diff_Suc ws_def(1) by auto
  qed

  { 
    fix i
    assume "i < length ws"
    then have "head (ws ! i) = head w 
             \<and> num_args (ws ! i) = num_args w
             \<and> (\<forall>k. k < num_args w \<longrightarrow> args (subst \<rho> w) ! k \<unrhd>\<^sub>e\<^sub>m\<^sub>b args (ws ! i) ! k)
             \<and> (Suc i < length ws \<longrightarrow> prio (prio_emb_pos prio (ws ! i) u) = 1)"
    proof (induct i)
      case 0
      have 1:"head (ws ! 0) = head w"
        by (metis assms(3) ground_imp_subst_iden hd.collapse(2) hd.simps(18) hd_conv_nth head_subst tm.sel(1) tm.simps(17) ws_def(1) ws_def(2))
      have 2:"num_args (ws ! 0) = num_args w"
        by (metis (no_types, lifting) append_self_conv2 args_subst assms(3) hd.case_eq_if hd_conv_nth length_map ws_def(1) ws_def(2))
      have 3:"\<forall>k. k < num_args w \<longrightarrow> args (subst \<rho> w) ! k \<unrhd>\<^sub>e\<^sub>m\<^sub>b args (ws ! 0) ! k"
        using emb.refl hd_conv_nth ws_def(1) ws_def(2) by fastforce
      have 4:"(Suc 0 < length ws \<longrightarrow> prio (prio_emb_pos prio (ws ! 0) u) = 1)"
        by (metis \<open>num_args (ws ! 0) = num_args w\<close> prio_def append_butlast_last_id assms(5) emb_step_at_if_position 
        emb_step_at_subst hd_conv_nth position_Left_only_subst prio_emb_posI ws_def(1) ws_def(2) ws_emb_u)
      show ?case using 1 2 3 4 by blast
    next
      case (Suc i)
      then have ih: 
        "prio (prio_emb_pos prio (ws ! i) u) = 1" 
        "head (ws ! i) = head w" 
        "num_args (ws ! i) = num_args w" by simp_all
      have 1:"head (ws ! Suc i) = head w"
        by (metis Suc.prems prio_def emb_step_under_args_head ih(1) ih(2) prio_emb_step_def ws_def(4) zero_neq_one)
      have 2:"num_args (ws ! Suc i) = num_args w"
        by (metis Suc.prems emb_step_under_args_num_args ih(1) ih(3) prio_def prio_emb_step_def ws_def(4) zero_neq_one)
      have "\<forall>k<num_args (ws ! i). args (ws ! i) ! k \<unrhd>\<^sub>e\<^sub>m\<^sub>b args (ws ! Suc i) ! k" 
        using Suc.prems emb_step_under_args_emb ih(1) prio_def prio_emb_step_def ws_def(4) zero_neq_one 
        by (metis (no_types, lifting) append_butlast_last_id prio_emb_posI ws_emb_u)
      then have 3:"\<forall>k. k < num_args w \<longrightarrow> args (subst \<rho> w) ! k \<unrhd>\<^sub>e\<^sub>m\<^sub>b args (ws ! Suc i) ! k"
        using Suc.hyps Suc.prems emb_trans by force
      have "\<And>p q dp dq. prio (q @ [dq]) < prio (p @ [dp]) \<Longrightarrow> take (length p) q \<noteq> p" unfolding prio_def
        using append_take_drop_id list_all_append 
        by (metis (mono_tags, lifting) butlast_snoc gr_implies_not0 less_not_refl2)
      then have 4:"Suc (Suc i) < length ws \<longrightarrow> prio (prio_emb_pos prio (ws ! Suc i) u) = 1"
        by (metis Suc.prems ih(1) not_one_le_zero prio_def prio_emb_pos_increase ws_def(4) ws_emb_u)
      then show ?case using 1 2 3 4 by auto
    qed
  }
  note 1 = this

  have "\<forall>i. Suc i < length ws \<longrightarrow> 
      (\<exists>p d. emb_step_at p d (ws ! i) = ws ! Suc i \<and> \<not> list_all (\<lambda>x. x = Left) p)" 
    by (metis "1" Suc_lessD prio_def prio_emb_step_def ws_def(4) zero_neq_one)

  then show ?thesis
    using that ws_def(1) ws_def(2) ws_def(3)
    using "1" by blast
qed

lemma perform_emb_above_vars:
  assumes 
    "subst \<rho> s \<unrhd>\<^sub>e\<^sub>m\<^sub>b u"
  obtains w where
    "s \<unrhd>\<^sub>e\<^sub>m\<^sub>b w"
    "subst \<rho> w \<unrhd>\<^sub>e\<^sub>m\<^sub>b u"
    "is_Sym (head w) \<Longrightarrow> head w = head u \<and> num_args w = num_args u \<and> (\<forall>k. k<num_args w \<longrightarrow> args (subst \<rho> w) ! k \<unrhd>\<^sub>e\<^sub>m\<^sub>b args u ! k)"
proof -
  obtain w where w_def:
    "s \<unrhd>\<^sub>e\<^sub>m\<^sub>b w" 
    "subst \<rho> w \<unrhd>\<^sub>e\<^sub>m\<^sub>b u" 
    "\<forall>w'. w \<rightarrow>\<^sub>e\<^sub>m\<^sub>b w' \<longrightarrow> \<not> subst \<rho> w' \<unrhd>\<^sub>e\<^sub>m\<^sub>b u" 
    using perform_emb_above_vars0[OF \<open>subst \<rho> s \<unrhd>\<^sub>e\<^sub>m\<^sub>b u\<close>] by metis
  {
    assume "is_Sym (head w)"
    obtain ws where ws_def:
      "ws \<noteq> []" 
      "hd ws = subst \<rho> w" 
      "last ws = u" 
      "\<forall>i. Suc i < length ws \<longrightarrow> (\<exists>p d. emb_step_at p d (ws ! i) = ws ! Suc i \<and> \<not> list_all (\<lambda>x. x = Left) p)"
      "\<forall>i<length ws. head (ws ! i) = head w \<and> num_args (ws ! i) = num_args w"
      "\<forall>i<length ws. \<forall>k<num_args w. args (subst \<rho> w) ! k \<unrhd>\<^sub>e\<^sub>m\<^sub>b args (ws ! i) ! k"
      using emb_only_below_vars[OF \<open>subst \<rho> s \<unrhd>\<^sub>e\<^sub>m\<^sub>b u\<close> \<open>s \<unrhd>\<^sub>e\<^sub>m\<^sub>b w\<close> \<open>is_Sym (head w)\<close> \<open>subst \<rho> w \<unrhd>\<^sub>e\<^sub>m\<^sub>b u\<close> w_def(3)] by metis
    then have "head w = head u \<and> num_args w = num_args u \<and> (\<forall>k. k<num_args w \<longrightarrow> args (subst \<rho> w) ! k \<unrhd>\<^sub>e\<^sub>m\<^sub>b args u ! k)"
      by (metis One_nat_def append_butlast_last_id diff_Suc_1 diff_Suc_less length_append_singleton length_greater_0_conv nth_append_length)

  }
  then show ?thesis 
    using that w_def(1) w_def(2) by blast
qed


end