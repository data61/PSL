theory L_Transform
imports
  Validity
  Bisimilarity_Implies_Equivalence
  FL_Equivalence_Implies_Bisimilarity
begin

section \<open>\texorpdfstring{$L$}{L}-Transform\<close>

subsection \<open>States\<close>

text \<open>The intuition is that states of kind~\<open>AC\<close> can perform ordinary actions, and states of
kind~\<open>EF\<close> can commit effects.\<close>

datatype ('state,'effect) L_state =
    AC "'effect \<times> 'effect fs_set \<times> 'state"
  | EF "'effect fs_set \<times> 'state"

instantiation L_state :: (pt,pt) pt
begin

  fun permute_L_state :: "perm \<Rightarrow> ('a,'b) L_state \<Rightarrow> ('a,'b) L_state" where
    "p \<bullet> (AC x) = AC (p \<bullet> x)"
  | "p \<bullet> (EF x) = EF (p \<bullet> x)"

  instance
  proof
    fix x :: "('a,'b) L_state"
    show "0 \<bullet> x = x" by (cases x, simp_all)
  next
    fix p q and x :: "('a,'b) L_state"
    show "(p + q) \<bullet> x = p \<bullet> q \<bullet> x" by (cases x, simp_all)
  qed

end

declare permute_L_state.simps [eqvt]

lemma supp_AC [simp]: "supp (AC x) = supp x"
unfolding supp_def by simp

lemma supp_EF [simp]: "supp (EF x) = supp x"
unfolding supp_def by simp

instantiation L_state :: (fs,fs) fs
begin

  instance
  proof
    fix x :: "('a,'b) L_state"
    show "finite (supp x)"
      by (cases x) (simp add: finite_supp)+
  qed

end


subsection \<open>Actions and binding names\<close>

datatype ('act,'effect) L_action =
    Act 'act
  | Eff 'effect

instantiation L_action :: (pt,pt) pt
begin

  fun permute_L_action :: "perm \<Rightarrow> ('a,'b) L_action \<Rightarrow> ('a,'b) L_action" where
    "p \<bullet> (Act \<alpha>) = Act (p \<bullet> \<alpha>)"
  | "p \<bullet> (Eff f) = Eff (p \<bullet> f)"

  instance
  proof
    fix x :: "('a,'b) L_action"
    show "0 \<bullet> x = x" by (cases x, simp_all)
  next
    fix p q and x :: "('a,'b) L_action"
    show "(p + q) \<bullet> x = p \<bullet> q \<bullet> x" by (cases x, simp_all)
  qed

end

declare permute_L_action.simps [eqvt]

lemma supp_Act [simp]: "supp (Act \<alpha>) = supp \<alpha>"
unfolding supp_def by simp

lemma supp_Eff [simp]: "supp (Eff f) = supp f"
unfolding supp_def by simp

instantiation L_action :: (fs,fs) fs
begin

  instance
  proof
    fix x :: "('a,'b) L_action"
    show "finite (supp x)"
      by (cases x) (simp add: finite_supp)+
  qed

end

instantiation L_action :: (bn,fs) bn
begin

  fun bn_L_action :: "('a,'b) L_action \<Rightarrow> atom set" where
    "bn_L_action (Act \<alpha>) = bn \<alpha>"
  | "bn_L_action (Eff _) = {}"

  instance
  proof
    fix p and \<alpha> :: "('a,'b) L_action"
    show "p \<bullet> bn \<alpha> = bn (p \<bullet> \<alpha>)"
      by (cases \<alpha>) (simp add: bn_eqvt, simp)
  next
    fix \<alpha> :: "('a,'b) L_action"
    show "finite (bn \<alpha>)"
      by (cases \<alpha>) (simp add: bn_finite, simp)
  qed

end


subsection \<open>Satisfaction\<close>

context effect_nominal_ts
begin

  fun L_satisfies :: "('state,'effect) L_state \<Rightarrow> 'pred \<Rightarrow> bool" (infix "\<turnstile>\<^sub>L" 70) where
    "AC (_,_,P) \<turnstile>\<^sub>L \<phi> \<longleftrightarrow> P \<turnstile> \<phi>"
  | "EF _       \<turnstile>\<^sub>L \<phi> \<longleftrightarrow> False"

  lemma L_satisfies_eqvt: assumes "P\<^sub>L \<turnstile>\<^sub>L \<phi>" shows "(p \<bullet> P\<^sub>L) \<turnstile>\<^sub>L (p \<bullet> \<phi>)"
  proof (cases P\<^sub>L)
    case (AC fFP)
    with assms have "snd (snd fFP) \<turnstile> \<phi>"
      by (metis L_satisfies.simps(1) prod.collapse)
    then have "snd (snd (p \<bullet> fFP)) \<turnstile> p \<bullet> \<phi>"
      by (metis satisfies_eqvt snd_eqvt)
    then show ?thesis
      using AC by (metis L_satisfies.simps(1) permute_L_state.simps(1) prod.collapse)
  next
    case EF
    with assms have "False"
      by simp
    then show ?thesis ..
  qed

end


subsection \<open>Transitions\<close>

context effect_nominal_ts
begin

  fun L_transition :: "('state,'effect) L_state \<Rightarrow> (('act,'effect) L_action, ('state,'effect) L_state) residual \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>L" 70) where
    "AC (f,F,P) \<rightarrow>\<^sub>L \<alpha>P' \<longleftrightarrow> (\<exists>\<alpha> P'. P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<and> \<alpha>P' = \<langle>Act \<alpha>, EF (L (\<alpha>,F,f), P')\<rangle> \<and> bn \<alpha> \<sharp>* (F,f))" \<comment> \<open>note the freshness condition\<close>
  | "EF (F,P) \<rightarrow>\<^sub>L \<alpha>P' \<longleftrightarrow> (\<exists>f. f \<in>\<^sub>f\<^sub>s F \<and> \<alpha>P' = \<langle>Eff f, AC (f, F, \<langle>f\<rangle>P)\<rangle>)"

  lemma L_transition_eqvt: assumes "P\<^sub>L \<rightarrow>\<^sub>L \<alpha>\<^sub>LP\<^sub>L'" shows "(p \<bullet> P\<^sub>L) \<rightarrow>\<^sub>L (p \<bullet> \<alpha>\<^sub>LP\<^sub>L')"
  proof (cases P\<^sub>L)
    case AC
    {
      fix f F P
      assume *: "P\<^sub>L = AC (f,F,P)"
      with assms obtain \<alpha> P' where trans: "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>" and \<alpha>P': "\<alpha>\<^sub>LP\<^sub>L' = \<langle>Act \<alpha>, EF (L (\<alpha>,F,f), P')\<rangle>" and fresh: "bn \<alpha> \<sharp>* (F,f)"
        by auto
      from trans have "p \<bullet> P \<rightarrow> \<langle>p \<bullet> \<alpha>, p \<bullet> P'\<rangle>"
        by (simp add: transition_eqvt')
      moreover from \<alpha>P' have "p \<bullet> \<alpha>\<^sub>LP\<^sub>L' = \<langle>Act (p \<bullet> \<alpha>), EF (L (p \<bullet> \<alpha>, p \<bullet> F, p \<bullet> f), p \<bullet> P')\<rangle>"
        by (simp add: L_eqvt')
      moreover from fresh have "bn (p \<bullet> \<alpha>) \<sharp>* (p \<bullet> F, p \<bullet> f)"
        by (metis bn_eqvt fresh_star_Pair fresh_star_permute_iff)
      ultimately have "p \<bullet> P\<^sub>L \<rightarrow>\<^sub>L p \<bullet> \<alpha>\<^sub>LP\<^sub>L'"
        using "*" by auto
    }
    with AC show ?thesis
      by (metis prod.collapse)
  next
    case EF
    {
      fix F P
      assume *: "P\<^sub>L = EF (F,P)"
      with assms obtain f where "f \<in>\<^sub>f\<^sub>s F" and "\<alpha>\<^sub>LP\<^sub>L' = \<langle>Eff f, AC (f, F, \<langle>f\<rangle>P)\<rangle>"
        by auto
      then have "(p \<bullet> f) \<in>\<^sub>f\<^sub>s (p \<bullet> F)" and "p \<bullet> \<alpha>\<^sub>LP\<^sub>L' = \<langle>Eff (p \<bullet> f), AC (p \<bullet> f, p \<bullet> F, \<langle>p \<bullet> f\<rangle>(p \<bullet> P))\<rangle>"
        by simp+
      then have "p \<bullet> P\<^sub>L \<rightarrow>\<^sub>L p \<bullet> \<alpha>\<^sub>LP\<^sub>L'"
        using "*" L_transition.simps(2) Pair_eqvt permute_L_state.simps(2) by force
    }
    with EF show ?thesis
      by (metis prod.collapse)
  qed

  text \<open>The binding names in the alpha-variant that witnesses the $L$-transition may be chosen fresh
  for any finitely supported context.\<close>

  lemma L_transition_AC_strong:
    assumes "finite (supp X)" and "AC (f,F,P) \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle>"
    shows "\<exists>\<alpha> P'. P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<and> \<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle> = \<langle>Act \<alpha>, EF (L (\<alpha>,F,f), P')\<rangle> \<and> bn \<alpha> \<sharp>* X"
  using assms proof -
    from \<open>AC (f,F,P) \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle>\<close> obtain \<alpha> P' where transition: "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>" and alpha: "\<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle> = \<langle>Act \<alpha>, EF (L (\<alpha>,F,f), P')\<rangle>" and fresh: "bn \<alpha> \<sharp>* (F,f)"
      by (metis L_transition.simps(1))
    let ?Act = "Act \<alpha> :: ('act,'effect) L_action" \<comment> \<open>the type annotation prevents a type that is too polymorphic and doesn't fix~@{typ 'effect}\<close>
    have "finite (bn \<alpha>)"
      by (fact bn_finite)
    moreover note \<open>finite (supp X)\<close>
    moreover have "finite (supp (\<langle>?Act, EF (L (\<alpha>,F,f), P')\<rangle>, \<langle>\<alpha>,P'\<rangle>, F, f))"
      by (metis finite_Diff finite_UnI finite_supp supp_Pair supp_abs_residual_pair)
    moreover from fresh have "bn \<alpha> \<sharp>* (\<langle>?Act, EF (L (\<alpha>,F,f), P')\<rangle>, \<langle>\<alpha>,P'\<rangle>, F, f)"
      by (auto simp add: fresh_star_def fresh_def supp_Pair supp_abs_residual_pair)
    ultimately obtain p where fresh_X: "(p \<bullet> bn \<alpha>) \<sharp>* X" and "supp (\<langle>?Act, EF (L (\<alpha>,F,f), P')\<rangle>, \<langle>\<alpha>,P'\<rangle>, F, f) \<sharp>* p"
      by (metis at_set_avoiding2)
    then have "supp \<langle>?Act, EF (L (\<alpha>,F,f), P')\<rangle> \<sharp>* p" and "supp \<langle>\<alpha>,P'\<rangle> \<sharp>* p" and "supp (F,f) \<sharp>* p"
      by (metis fresh_star_Un supp_Pair)+
    then have "p \<bullet> \<langle>?Act, EF (L (\<alpha>,F,f), P')\<rangle> = \<langle>?Act, EF (L (\<alpha>,F,f), P')\<rangle>" and "p \<bullet> \<langle>\<alpha>,P'\<rangle> = \<langle>\<alpha>,P'\<rangle>" and "p \<bullet> (F,f) = (F,f)"
      by (metis supp_perm_eq)+
    then have "\<langle>Act (p \<bullet> \<alpha>), EF (L (p \<bullet> \<alpha>, F, f), p \<bullet> P')\<rangle> = \<langle>?Act, EF (L (\<alpha>,F,f), P')\<rangle>" and "\<langle>p \<bullet> \<alpha>, p \<bullet> P'\<rangle> = \<langle>\<alpha>,P'\<rangle>"
      using permute_L_action.simps(1) permute_L_state.simps(2) abs_residual_pair_eqvt L_eqvt' Pair_eqvt by auto
    then show "\<exists>\<alpha> P'. P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<and> \<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle> = \<langle>Act \<alpha>, EF (L (\<alpha>,F,f), P')\<rangle> \<and> bn \<alpha> \<sharp>* X"
      using transition and alpha and fresh_X by (metis bn_eqvt)
  qed

  (* bn \<alpha> \<sharp>* (F,f) is required for the \<longleftarrow> implication as well as for the \<longrightarrow> implication;
     additionally bn \<alpha> \<sharp>* P is required for the \<longrightarrow> implication. *)

  lemma L_transition_AC_fresh:
    assumes "bn \<alpha> \<sharp>* (F,f,P)"
    shows "AC (f,F,P) \<rightarrow>\<^sub>L \<langle>Act \<alpha>, P\<^sub>L'\<rangle> \<longleftrightarrow> (\<exists>P'. P\<^sub>L' = EF (L (\<alpha>,F,f), P') \<and> P \<rightarrow> \<langle>\<alpha>,P'\<rangle>)"
  proof
    assume "AC (f,F,P) \<rightarrow>\<^sub>L \<langle>Act \<alpha>, P\<^sub>L'\<rangle>"
    moreover have "finite (supp (F,f,P))"
      by (fact finite_supp)
    ultimately obtain \<alpha>' P' where trans: "P \<rightarrow> \<langle>\<alpha>',P'\<rangle>" and eq: "\<langle>Act \<alpha> :: ('act,'effect) L_action, P\<^sub>L'\<rangle> = \<langle>Act \<alpha>', EF (L (\<alpha>',F,f), P')\<rangle>" and fresh: "bn \<alpha>' \<sharp>* (F,f,P)"
      using L_transition_AC_strong by blast
    from eq obtain p where p: "p \<bullet> (Act \<alpha> :: ('act,'effect) L_action, P\<^sub>L') = (Act \<alpha>', EF (L (\<alpha>',F,f), P'))" and supp_p: "supp p \<subseteq> bn (Act \<alpha> :: ('act,'effect) L_action) \<union> p \<bullet> bn (Act \<alpha> :: ('act,'effect) L_action)"
      using residual_eq_iff_perm_renaming by metis

    from p have p_\<alpha>: "p \<bullet> \<alpha> = \<alpha>'" and p_P\<^sub>L': "p \<bullet> P\<^sub>L' = EF (L (\<alpha>',F,f), P')"
      by simp_all

    from supp_p and p_\<alpha> and assms and fresh have "supp p \<sharp>* (F, f, P)"
      by (simp add: bn_eqvt fresh_star_def) blast
    then have p_F: "p \<bullet> F = F" and p_f: "p \<bullet> f = f" and p_P: "p \<bullet> P = P"
      by (simp_all add: fresh_star_Pair perm_supp_eq)

    from p_P\<^sub>L' have "P\<^sub>L' = -p \<bullet> EF (L (\<alpha>',F,f), P')"
      by (metis permute_minus_cancel(2))
    then have "P\<^sub>L' = EF (L (\<alpha>,F,f), -p \<bullet> P')"
      using p_\<alpha> p_F p_f by simp (metis (full_types) permute_minus_cancel(2))

    moreover from trans have "P \<rightarrow> \<langle>\<alpha>, -p \<bullet> P'\<rangle>"
      using p_P and p_\<alpha> by (metis permute_minus_cancel(2) transition_eqvt')

    ultimately show "\<exists>P'. P\<^sub>L' = EF (L (\<alpha>,F,f), P') \<and> P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
      by blast
  next
    assume "\<exists>P'. P\<^sub>L' = EF (L (\<alpha>,F,f), P') \<and> P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
    moreover from assms have "bn \<alpha> \<sharp>* (F,f)"
      by (simp add: fresh_star_Pair)
    ultimately show "AC (f, F, P) \<rightarrow>\<^sub>L \<langle>Act \<alpha>, P\<^sub>L'\<rangle>"
      using L_transition.simps(1) by blast
  qed

end


subsection \<open>Translation of \texorpdfstring{$F/L$}{F/L}-formulas into formulas without effects\<close>

text \<open>Since we defined formulas via a manual quotient construction, we also need to define the
$L$-transform via lifting from the underlying type of infinitely branching trees. As before, we
cannot use {\bf nominal\_function} because that generates proof obligations where, for formulas
of the form~@{term "Conj xset"}, the assumption that~@{term xset} has finite support is missing.\<close>

text \<open>The following auxiliary function returns trees (modulo $\alpha$-equivalence) rather than
formulas. This allows us to prove equivariance for \emph{all} argument trees, without an assumption
that they are (hereditarily) finitely supported. Further below--after this auxiliary function has
been lifted to $F/L$-formulas as arguments--we derive a version that returns formulas.\<close>

primrec L_transform_Tree :: "('idx,'pred::fs,'act::bn,'eff::fs) Tree \<Rightarrow> ('idx, 'pred, ('act,'eff) L_action) Formula.Tree\<^sub>\<alpha>" where
  "L_transform_Tree (tConj tset) = Formula.Conj\<^sub>\<alpha> (map_bset L_transform_Tree tset)"
| "L_transform_Tree (tNot t) = Formula.Not\<^sub>\<alpha> (L_transform_Tree t)"
| "L_transform_Tree (tPred f \<phi>) = Formula.Act\<^sub>\<alpha> (Eff f) (Formula.Pred\<^sub>\<alpha> \<phi>)"
| "L_transform_Tree (tAct f \<alpha> t) = Formula.Act\<^sub>\<alpha> (Eff f) (Formula.Act\<^sub>\<alpha> (Act \<alpha>) (L_transform_Tree t))"

lemma L_transform_Tree_eqvt [eqvt]: "p \<bullet> L_transform_Tree t = L_transform_Tree (p \<bullet> t)"
proof (induct t)
  case (tConj tset)
  then show ?case
    by simp (metis (no_types, hide_lams) bset.map_cong0 map_bset_eqvt permute_fun_def permute_minus_cancel(1))
qed simp_all

text \<open>@{const L_transform_Tree} respects $\alpha$-equivalence.\<close>

lemma alpha_Tree_L_transform_Tree:
  assumes "alpha_Tree t1 t2"
  shows "L_transform_Tree t1 = L_transform_Tree t2"
using assms proof (induction t1 t2 rule: alpha_Tree_induct')
  case (alpha_tConj tset1 tset2)
  then have "rel_bset (=) (map_bset L_transform_Tree tset1) (map_bset L_transform_Tree tset2)"
    by (simp add: bset.rel_map(1) bset.rel_map(2) bset.rel_mono_strong)
  then show ?case
    by (simp add: bset.rel_eq)
next
  case (alpha_tAct f1 \<alpha>1 t1 f2 \<alpha>2 t2)
  from \<open>alpha_Tree (FL_Formula.Tree.tAct f1 \<alpha>1 t1) (FL_Formula.Tree.tAct f2 \<alpha>2 t2)\<close>
    obtain p where *: "(bn \<alpha>1, t1) \<approx>set alpha_Tree (supp_rel alpha_Tree) p (bn \<alpha>2, t2)"
      and **: "(bn \<alpha>1, \<alpha>1) \<approx>set (=) supp p (bn \<alpha>2, \<alpha>2)" and "f1 = f2"
    by auto
  from * have fresh: "(supp_rel alpha_Tree t1 - bn \<alpha>1) \<sharp>* p" and alpha: "alpha_Tree (p \<bullet> t1) t2" and eq: "p \<bullet> bn \<alpha>1 = bn \<alpha>2"
    by (auto simp add: alpha_set)
  from alpha_tAct.IH(2) have "supp_rel Formula.alpha_Tree (Formula.rep_Tree\<^sub>\<alpha> (L_transform_Tree t1)) \<subseteq> supp_rel alpha_Tree t1"
    by (metis (no_types, lifting) infinite_mono Formula.alpha_Tree_permute_rep_commute L_transform_Tree_eqvt mem_Collect_eq subsetI supp_rel_def)
  with fresh have fresh': "(supp_rel Formula.alpha_Tree (Formula.rep_Tree\<^sub>\<alpha> (L_transform_Tree t1)) - bn \<alpha>1) \<sharp>* p"
    by (meson DiffD1 DiffD2 DiffI fresh_star_def subsetCE)
  moreover from alpha have alpha': "Formula.alpha_Tree (p \<bullet> Formula.rep_Tree\<^sub>\<alpha> (L_transform_Tree t1)) (Formula.rep_Tree\<^sub>\<alpha> (L_transform_Tree t2))"
    using alpha_tAct.IH(1) by (metis Formula.alpha_Tree_permute_rep_commute L_transform_Tree_eqvt)
  moreover from fresh' alpha' eq have "supp_rel Formula.alpha_Tree (Formula.rep_Tree\<^sub>\<alpha> (L_transform_Tree t1)) - bn \<alpha>1 = supp_rel Formula.alpha_Tree (Formula.rep_Tree\<^sub>\<alpha> (L_transform_Tree t2)) - bn \<alpha>2"
    by (metis (mono_tags) Diff_eqvt Formula.alpha_Tree_eqvt' Formula.alpha_Tree_eqvt_aux Formula.alpha_Tree_supp_rel atom_set_perm_eq)
  ultimately have "(bn \<alpha>1, Formula.rep_Tree\<^sub>\<alpha> (L_transform_Tree t1)) \<approx>set Formula.alpha_Tree (supp_rel Formula.alpha_Tree) p (bn \<alpha>2, Formula.rep_Tree\<^sub>\<alpha> (L_transform_Tree t2))"
    using eq by (simp add: alpha_set)
  moreover from ** have "(bn \<alpha>1, Act \<alpha>1) \<approx>set (=) supp p (bn \<alpha>2, Act \<alpha>2)"
    by (metis (mono_tags, lifting) L_Transform.supp_Act alpha_set permute_L_action.simps(1))
  ultimately have "Formula.Act\<^sub>\<alpha> (Act \<alpha>1) (L_transform_Tree t1) = Formula.Act\<^sub>\<alpha> (Act \<alpha>2) (L_transform_Tree t2)"
    by (auto simp add: Formula.Act\<^sub>\<alpha>_eq_iff)
  with \<open>f1 = f2\<close> show ?case
    by simp
qed simp_all

text \<open>$L$-transform for trees modulo $\alpha$-equivalence.\<close>

lift_definition L_transform_Tree\<^sub>\<alpha> :: "('idx,'pred::fs,'act::bn,'eff::fs) Tree\<^sub>\<alpha> \<Rightarrow> ('idx, 'pred, ('act,'eff) L_action) Formula.Tree\<^sub>\<alpha>" is
    L_transform_Tree
  by (fact alpha_Tree_L_transform_Tree)

lemma L_transform_Tree\<^sub>\<alpha>_eqvt [eqvt]: "p \<bullet> L_transform_Tree\<^sub>\<alpha> t\<^sub>\<alpha> = L_transform_Tree\<^sub>\<alpha> (p \<bullet> t\<^sub>\<alpha>)"
  by transfer (simp)

lemma L_transform_Tree\<^sub>\<alpha>_Conj\<^sub>\<alpha> [simp]: "L_transform_Tree\<^sub>\<alpha> (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>) = Formula.Conj\<^sub>\<alpha> (map_bset L_transform_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>)"
  by (simp add: Conj\<^sub>\<alpha>_def' L_transform_Tree\<^sub>\<alpha>.abs_eq) (metis (no_types, lifting) L_transform_Tree\<^sub>\<alpha>.rep_eq bset.map_comp bset.map_cong0 comp_apply)

lemma L_transform_Tree\<^sub>\<alpha>_Not\<^sub>\<alpha> [simp]: "L_transform_Tree\<^sub>\<alpha> (Not\<^sub>\<alpha> t\<^sub>\<alpha>) = Formula.Not\<^sub>\<alpha> (L_transform_Tree\<^sub>\<alpha> t\<^sub>\<alpha>)"
  by transfer simp

lemma L_transform_Tree\<^sub>\<alpha>_Pred\<^sub>\<alpha> [simp]: "L_transform_Tree\<^sub>\<alpha> (Pred\<^sub>\<alpha> f \<phi>) = Formula.Act\<^sub>\<alpha> (Eff f) (Formula.Pred\<^sub>\<alpha> \<phi>)"
  by transfer simp

lemma L_transform_Tree\<^sub>\<alpha>_Act\<^sub>\<alpha> [simp]: "L_transform_Tree\<^sub>\<alpha> (Act\<^sub>\<alpha> f \<alpha> t\<^sub>\<alpha>) = Formula.Act\<^sub>\<alpha> (Eff f) (Formula.Act\<^sub>\<alpha> (Act \<alpha>) (L_transform_Tree\<^sub>\<alpha> t\<^sub>\<alpha>))"
  by transfer simp

lemma finite_supp_map_bset_L_transform_Tree\<^sub>\<alpha> [simp]:
  assumes "finite (supp tset\<^sub>\<alpha>)"
  shows "finite (supp (map_bset L_transform_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>))"
proof -
  have "eqvt map_bset" and "eqvt L_transform_Tree\<^sub>\<alpha>"
    by (simp add: eqvtI)+
  then have "supp (map_bset L_transform_Tree\<^sub>\<alpha>) = {}"
    using supp_fun_eqvt supp_fun_app_eqvt by blast
  then have "supp (map_bset L_transform_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>) \<subseteq> supp tset\<^sub>\<alpha>"
    using supp_fun_app by blast
  with assms show "finite (supp (map_bset L_transform_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>))"
    by (metis finite_subset)
qed

lemma L_transform_Tree\<^sub>\<alpha>_preserves_hereditarily_fs:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "Formula.hereditarily_fs (L_transform_Tree\<^sub>\<alpha> t\<^sub>\<alpha>)"
using assms proof (induct rule: hereditarily_fs.induct)
  case (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>)
  then show ?case
    by (auto intro!: Formula.hereditarily_fs.Conj\<^sub>\<alpha>) (metis imageE map_bset.rep_eq)
next
  case (Not\<^sub>\<alpha> t\<^sub>\<alpha>)
  then show ?case
    by (simp add: Formula.hereditarily_fs.Not\<^sub>\<alpha>)
next
  case (Pred\<^sub>\<alpha> f \<phi>)
  then show ?case
    by (simp add: Formula.hereditarily_fs.Act\<^sub>\<alpha> Formula.hereditarily_fs.Pred\<^sub>\<alpha>)
next
  case (Act\<^sub>\<alpha> t\<^sub>\<alpha> f \<alpha>)
  then show ?case
    by (simp add: Formula.hereditarily_fs.Act\<^sub>\<alpha>)
qed

text \<open>$L$-transform for $F/L$-formulas.\<close>

lift_definition L_transform_formula :: "('idx,'pred::fs,'act::bn,'eff::fs) formula \<Rightarrow> ('idx, 'pred, ('act,'eff) L_action) Formula.Tree\<^sub>\<alpha>" is
    L_transform_Tree\<^sub>\<alpha>
  .

lemma L_transform_formula_eqvt [eqvt]: "p \<bullet> L_transform_formula x = L_transform_formula (p \<bullet> x)"
  by transfer (simp)

lemma L_transform_formula_Conj [simp]:
  assumes "finite (supp xset)"
  shows "L_transform_formula (Conj xset) = Formula.Conj\<^sub>\<alpha> (map_bset L_transform_formula xset)"
  using assms by (simp add: Conj_def L_transform_formula_def bset.map_comp map_fun_def)

lemma L_transform_formula_Not [simp]: "L_transform_formula (Not x) = Formula.Not\<^sub>\<alpha> (L_transform_formula x)"
  by transfer simp

lemma L_transform_formula_Pred [simp]: "L_transform_formula (Pred f \<phi>) = Formula.Act\<^sub>\<alpha> (Eff f) (Formula.Pred\<^sub>\<alpha> \<phi>)"
  by transfer simp

lemma L_transform_formula_Act [simp]: "L_transform_formula (FL_Formula.Act f \<alpha> x) = Formula.Act\<^sub>\<alpha> (Eff f) (Formula.Act\<^sub>\<alpha> (Act \<alpha>) (L_transform_formula x))"
  by transfer simp

lemma L_transform_formula_hereditarily_fs [simp]: "Formula.hereditarily_fs (L_transform_formula x)"
  by transfer (fact L_transform_Tree\<^sub>\<alpha>_preserves_hereditarily_fs)

text \<open>Finally, we define the proper $L$-transform, which returns formulas instead of trees.\<close>

definition L_transform :: "('idx,'pred::fs,'act::bn,'eff::fs) formula \<Rightarrow> ('idx, 'pred, ('act,'eff) L_action) Formula.formula" where
  "L_transform x = Formula.Abs_formula (L_transform_formula x)"

lemma L_transform_eqvt [eqvt]: "p \<bullet> L_transform x = L_transform (p \<bullet> x)"
  unfolding L_transform_def by simp

lemma finite_supp_map_bset_L_transform [simp]:
  assumes "finite (supp xset)"
  shows "finite (supp (map_bset L_transform xset))"
proof -
  have "eqvt map_bset" and "eqvt L_transform"
    by (simp add: eqvtI)+
  then have "supp (map_bset L_transform) = {}"
    using supp_fun_eqvt supp_fun_app_eqvt by blast
  then have "supp (map_bset L_transform xset) \<subseteq> supp xset"
    using supp_fun_app by blast
  with assms show "finite (supp (map_bset L_transform xset))"
    by (metis finite_subset)
qed

lemma L_transform_Conj [simp]:
  assumes "finite (supp xset)"
  shows "L_transform (Conj xset) = Formula.Conj (map_bset L_transform xset)"
  using assms unfolding L_transform_def by (simp add: Formula.Conj_def bset.map_comp o_def)

lemma L_transform_Not [simp]: "L_transform (Not x) = Formula.Not (L_transform x)"
  unfolding L_transform_def by (simp add: Formula.Not_def)

lemma L_transform_Pred [simp]: "L_transform (Pred f \<phi>) = Formula.Act (Eff f) (Formula.Pred \<phi>)"
  unfolding L_transform_def by (simp add: Formula.Act_def Formula.Pred_def Formula.hereditarily_fs.Pred\<^sub>\<alpha>)

lemma L_transform_Act [simp]: "L_transform (FL_Formula.Act f \<alpha> x) = Formula.Act (Eff f) (Formula.Act (Act \<alpha>) (L_transform x))"
  unfolding L_transform_def by (simp add: Formula.Act_def Formula.hereditarily_fs.Act\<^sub>\<alpha>)

context effect_nominal_ts
begin

  interpretation L_transform: nominal_ts "(\<turnstile>\<^sub>L)" "(\<rightarrow>\<^sub>L)"
  by unfold_locales (fact L_satisfies_eqvt, fact L_transition_eqvt)

  text \<open>The $L$-transform preserves satisfaction of formulas in the following sense:\<close>

  theorem FL_valid_iff_valid_L_transform:
    assumes "(x::('idx,'pred,'act,'effect) formula) \<in> \<A>[F]"
    shows "FL_valid P x \<longleftrightarrow> L_transform.valid (EF (F, P)) (L_transform x)"
  using assms proof (induct x arbitrary: P)
    case (Conj xset F)
    then show ?case
      by auto (metis imageE map_bset.rep_eq, simp add: map_bset.rep_eq)
  next
    case (Not F x)
    then show ?case by simp
  next
    case (Pred f F \<phi>)
    let ?\<phi> = "Formula.Pred \<phi> :: ('idx, 'pred, ('act,'effect) L_action) Formula.formula"
    show ?case
    proof
      assume "FL_valid P (Pred f \<phi>)"
      then have "L_transform.valid (AC (f, F, \<langle>f\<rangle>P)) ?\<phi>"
        by (simp add: L_transform.valid_Act)
      moreover from \<open>f \<in>\<^sub>f\<^sub>s F\<close> have "EF (F, P) \<rightarrow>\<^sub>L \<langle>Eff f, AC (f, F, \<langle>f\<rangle>P)\<rangle>"
        by (metis L_transition.simps(2))
      ultimately show "L_transform.valid (EF (F, P)) (L_transform (Pred f \<phi>))"
        using L_transform.valid_Act by fastforce
    next
      assume "L_transform.valid (EF (F, P)) (L_transform (Pred f \<phi>))"
      then obtain P' where trans: "EF (F, P) \<rightarrow>\<^sub>L \<langle>Eff f, P'\<rangle>" and valid: "L_transform.valid P' ?\<phi>"
        by simp (metis bn_L_action.simps(2) empty_iff fresh_star_def L_transform.valid_Act_fresh L_transform.valid_Pred L_transition.simps(2))
      from trans have "P' = AC (f, F, \<langle>f\<rangle>P)"
        by (simp add: residual_empty_bn_eq_iff)
      with valid show "FL_valid P (Pred f \<phi>)"
        by simp
    qed
  next
    case (Act f F \<alpha> x)
    show ?case
    proof
      assume "FL_valid P (FL_Formula.Act f \<alpha> x)"
      then obtain \<alpha>' x' P' where eq: "FL_Formula.Act f \<alpha> x = FL_Formula.Act f \<alpha>' x'" and trans: "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle>" and valid: "FL_valid P' x'" and fresh: "bn \<alpha>' \<sharp>* (F, f)"
        by (metis FL_valid_Act_strong finite_supp)
      from eq obtain p where p_x: "p \<bullet> x = x'" and p_\<alpha>: "p \<bullet> \<alpha> = \<alpha>'" and supp_p: "supp p \<subseteq> bn \<alpha> \<union> bn \<alpha>'"
        by (metis bn_eqvt FL_Formula.Act_eq_iff_perm_renaming)
      from \<open>bn \<alpha> \<sharp>* (F, f)\<close> and fresh have "supp (F, f) \<sharp>* p"
        using supp_p by (auto simp add: fresh_star_Pair fresh_star_def supp_Pair fresh_def)
      then have "p \<bullet> F = F" and "p \<bullet> f = f"
        using supp_perm_eq by fastforce+

      from valid have "FL_valid (-p \<bullet> P') x"
        using p_x by (metis FL_valid_eqvt permute_minus_cancel(2))
      then have "L_transform.valid (EF (L (\<alpha>, F, f), -p \<bullet> P')) (L_transform x)"
        using Act.hyps(4) by metis
      then have "L_transform.valid (p \<bullet> EF (L (\<alpha>, F, f), -p \<bullet> P')) (p \<bullet> L_transform x)"
        by (fact L_transform.valid_eqvt)
      then have "L_transform.valid (EF (L (\<alpha>', F, f), P')) (L_transform x')"
        using p_x and p_\<alpha> and \<open>p \<bullet> F = F\<close> and \<open>p \<bullet> f = f\<close> by simp

      then have "L_transform.valid (AC (f, F, \<langle>f\<rangle>P)) (Formula.Act (Act \<alpha>') (L_transform x'))"
        using trans fresh L_transform.valid_Act by fastforce
      with \<open>f \<in>\<^sub>f\<^sub>s F\<close> and eq show "L_transform.valid (EF (F, P)) (L_transform (FL_Formula.Act f \<alpha> x))"
        using L_transform.valid_Act by fastforce
    next
      assume *: "L_transform.valid (EF (F, P)) (L_transform (FL_Formula.Act f \<alpha> x))"

      \<comment> \<open>rename~@{term "bn \<alpha>"} to avoid~@{term "(F, f, P)"}, without touching~@{term F} or~@{term "FL_Formula.Act f \<alpha> x"}\<close>
      obtain p where 1: "(p \<bullet> bn \<alpha>) \<sharp>* (F, f, P)" and 2: "supp (F, FL_Formula.Act f \<alpha> x) \<sharp>* p"
      proof (rule at_set_avoiding2[of "bn \<alpha>" "(F, f, P)" "(F, FL_Formula.Act f \<alpha> x)", THEN exE])
        show "finite (bn \<alpha>)" by (fact bn_finite)
      next
        show "finite (supp (F, f, P))" by (fact finite_supp)
      next
        show "finite (supp (F, FL_Formula.Act f \<alpha> x))" by (simp add: finite_supp)
      next
        from \<open>bn \<alpha> \<sharp>* (F, f)\<close> show "bn \<alpha> \<sharp>* (F, FL_Formula.Act f \<alpha> x)"
          by (simp add: fresh_star_Pair fresh_star_def fresh_def supp_Pair)
      qed metis
      from 2 have "supp F \<sharp>* p" and Act_fresh: "supp (FL_Formula.Act f \<alpha> x) \<sharp>* p"
        by (simp add: fresh_star_Pair fresh_star_def supp_Pair)+
      from \<open>supp F \<sharp>* p\<close> have "p \<bullet> F = F"
        by (metis supp_perm_eq)
      from Act_fresh have "p \<bullet> f = f"
        using fresh_star_Un supp_perm_eq by fastforce
      from Act_fresh have eq: "FL_Formula.Act f \<alpha> x = FL_Formula.Act f (p \<bullet> \<alpha>) (p \<bullet> x)"
        by (metis FL_Formula.Act_eq_iff_perm FL_Formula.Act_eqvt supp_perm_eq)

      with * obtain P' where trans: "EF (F, P) \<rightarrow>\<^sub>L \<langle>Eff f,P'\<rangle>" and valid: "L_transform.valid P' (Formula.Act (Act (p \<bullet> \<alpha>)) (L_transform (p \<bullet> x)))"
        using L_transform_Act by (metis L_transform.valid_Act_fresh bn_L_action.simps(2) empty_iff fresh_star_def)
      from trans have P': "P' = AC (f, F, \<langle>f\<rangle>P)"
        by (simp add: residual_empty_bn_eq_iff)

      have supp_f_P: "supp (\<langle>f\<rangle>P) \<subseteq> supp f \<union> supp P"
        using effect_apply_eqvt supp_fun_app supp_fun_app_eqvt by fastforce
      with 1 have "bn (Act (p \<bullet> \<alpha>)) \<sharp>* AC (f, F, \<langle>f\<rangle>P)"
        by (auto simp add: bn_eqvt fresh_star_def fresh_def supp_Pair)
      with valid obtain P'' where trans': "AC (f, F, \<langle>f\<rangle>P) \<rightarrow>\<^sub>L \<langle>Act (p \<bullet> \<alpha>),P''\<rangle>" and valid': "L_transform.valid P'' (L_transform (p \<bullet> x))"
        using P' by (metis L_transform.valid_Act_fresh)

      from supp_f_P and 1 have "bn (p \<bullet> \<alpha>) \<sharp>* (F, f, \<langle>f\<rangle>P)"
        by (auto simp add: bn_eqvt fresh_star_def fresh_def supp_Pair)
      with trans' obtain P' where P'': "P'' = EF (L (p \<bullet> \<alpha>, F, f), P')" and trans'': "\<langle>f\<rangle>P \<rightarrow> \<langle>p \<bullet> \<alpha>,P'\<rangle>"
        by (metis L_transition_AC_fresh)

      from valid' have "L_transform.valid (-p \<bullet> P'') (L_transform x)"
        by (metis (mono_tags) L_transform.valid_eqvt L_transform_eqvt permute_minus_cancel(2))
      with P'' \<open>p \<bullet> F = F\<close> \<open>p \<bullet> f = f\<close> have "L_transform.valid (EF (L (\<alpha>, F, f), - p \<bullet> P')) (L_transform x)"
        by simp (metis pemute_minus_self permute_minus_cancel(1))
      then have "FL_valid P' (p \<bullet> x)"
        using Act.hyps(4) by (metis FL_valid_eqvt permute_minus_cancel(1))

      with trans'' and eq show "FL_valid P (FL_Formula.Act f \<alpha> x)"
        by (metis FL_valid_Act)
    qed
  qed

end


subsection \<open>Bisimilarity in the \texorpdfstring{$L$}{L}-transform\<close>

context effect_nominal_ts
begin

  (* Not quite sure why this is needed again? *)
  interpretation L_transform: nominal_ts "(\<turnstile>\<^sub>L)" "(\<rightarrow>\<^sub>L)"
  by unfold_locales (fact L_satisfies_eqvt, fact L_transition_eqvt)

  notation L_transform.bisimilar (infix "\<sim>\<cdot>\<^sub>L" 100)

  text \<open>$F/L$-bisimilarity is equivalent to bisimilarity in the $L$-transform.\<close>

  inductive L_bisimilar :: "('state,'effect) L_state \<Rightarrow> ('state,'effect) L_state \<Rightarrow> bool" where
    "P \<sim>\<cdot>[F] Q \<Longrightarrow> L_bisimilar (EF (F,P)) (EF (F,Q))"
  | "P \<sim>\<cdot>[F] Q \<Longrightarrow> f \<in>\<^sub>f\<^sub>s F \<Longrightarrow> L_bisimilar (AC (f, F, \<langle>f\<rangle>P)) (AC (f, F, \<langle>f\<rangle>Q))"

  lemma L_bisimilar_is_L_transform_bisimulation: "L_transform.is_bisimulation L_bisimilar"
  unfolding L_transform.is_bisimulation_def
  proof
    show "symp L_bisimilar"
      by (metis FL_bisimilar_symp L_bisimilar.cases L_bisimilar.intros symp_def)
  next
    have "\<forall>P\<^sub>L Q\<^sub>L. L_bisimilar P\<^sub>L Q\<^sub>L \<longrightarrow> (\<forall>\<phi>. P\<^sub>L \<turnstile>\<^sub>L \<phi> \<longrightarrow> Q\<^sub>L \<turnstile>\<^sub>L \<phi>)" (is ?S)
      using FL_bisimilar_is_L_bisimulation L_bisimilar.simps is_L_bisimulation_def by auto
    moreover have "\<forall>P\<^sub>L Q\<^sub>L. L_bisimilar P\<^sub>L Q\<^sub>L \<longrightarrow> (\<forall>\<alpha>\<^sub>L P\<^sub>L'. bn \<alpha>\<^sub>L \<sharp>* Q\<^sub>L \<longrightarrow> P\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle> \<longrightarrow> (\<exists>Q\<^sub>L'. Q\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,Q\<^sub>L'\<rangle> \<and> L_bisimilar P\<^sub>L' Q\<^sub>L'))" (is ?T)
      proof (clarify)
        fix P\<^sub>L Q\<^sub>L \<alpha>\<^sub>L P\<^sub>L'
        assume L_bisim: "L_bisimilar P\<^sub>L Q\<^sub>L" and fresh\<^sub>L: "bn \<alpha>\<^sub>L \<sharp>* Q\<^sub>L" and trans\<^sub>L: "P\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle>"
        obtain Q\<^sub>L' where "Q\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,Q\<^sub>L'\<rangle>" and "L_bisimilar P\<^sub>L' Q\<^sub>L'"
          using L_bisim proof (rule L_bisimilar.cases)
            fix P F Q
            assume P\<^sub>L: "P\<^sub>L = EF (F, P)" and Q\<^sub>L: "Q\<^sub>L = EF (F, Q)" and bisim: "P \<sim>\<cdot>[F] Q"
            from P\<^sub>L and trans\<^sub>L obtain f where effect: "f \<in>\<^sub>f\<^sub>s F" and \<alpha>\<^sub>LP\<^sub>L': "\<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle> = \<langle>Eff f, AC (f, F, \<langle>f\<rangle>P)\<rangle>"
              using L_transition.simps(2) by blast
            from Q\<^sub>L and effect have "Q\<^sub>L \<rightarrow>\<^sub>L \<langle>Eff f, AC (f, F, \<langle>f\<rangle>Q)\<rangle>"
              using L_transition.simps(2) by blast
            moreover from bisim and effect have "L_bisimilar (AC (f, F, \<langle>f\<rangle>P)) (AC (f, F, \<langle>f\<rangle>Q))"
              using L_bisimilar.intros(2) by blast
            moreover from \<alpha>\<^sub>LP\<^sub>L' have "\<alpha>\<^sub>L = Eff f" and "P\<^sub>L' = AC (f, F, \<langle>f\<rangle>P)"
              by (metis bn_L_action.simps(2) residual_empty_bn_eq_iff)+
            ultimately show "thesis"
              using \<open>\<And>Q\<^sub>L'. Q\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,Q\<^sub>L'\<rangle> \<Longrightarrow> L_bisimilar P\<^sub>L' Q\<^sub>L' \<Longrightarrow> thesis\<close> by blast
          next
            fix P F Q f
            assume P\<^sub>L: "P\<^sub>L = AC (f, F, \<langle>f\<rangle>P)" and Q\<^sub>L: "Q\<^sub>L = AC (f, F, \<langle>f\<rangle>Q)" and bisim: "P \<sim>\<cdot>[F] Q" and effect: "f \<in>\<^sub>f\<^sub>s F"
            have "finite (supp (\<langle>f\<rangle>Q, F, f))"
              by (fact finite_supp)
            with P\<^sub>L and trans\<^sub>L obtain \<alpha> P' where trans_P: "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle>" and \<alpha>\<^sub>LP\<^sub>L': "\<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle> = \<langle>Act \<alpha>, EF (L (\<alpha>,F,f), P')\<rangle>" and fresh: "bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F, f)"
              by (metis L_transition_AC_strong)
            from bisim and effect and fresh and trans_P obtain Q' where trans_Q: "\<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>" and bisim': "P' \<sim>\<cdot>[L (\<alpha>,F,f)] Q'"
              by (metis FL_bisimilar_simulation_step)
            from fresh have "bn \<alpha> \<sharp>* (F, f)"
              by (meson fresh_PairD(2) fresh_star_def)
            with Q\<^sub>L and trans_Q have trans_Q\<^sub>L: "Q\<^sub>L \<rightarrow>\<^sub>L \<langle>Act \<alpha>, EF (L (\<alpha>,F,f), Q')\<rangle>"
              by (metis L_transition.simps(1))

            from \<alpha>\<^sub>LP\<^sub>L' obtain p where p: "(\<alpha>\<^sub>L,P\<^sub>L') = p \<bullet> (Act \<alpha>, EF (L (\<alpha>,F,f), P'))" and supp_p: "supp p \<subseteq> bn \<alpha> \<union> bn \<alpha>\<^sub>L"
              by (metis (no_types, lifting) bn_L_action.simps(1) residual_eq_iff_perm_renaming)
            from supp_p and fresh and fresh\<^sub>L and Q\<^sub>L have "supp p \<sharp>* (\<langle>f\<rangle>Q, F, f)"
              unfolding fresh_star_def by (metis (no_types, hide_lams) Un_iff fresh_Pair fresh_def subsetCE supp_AC)
            then have p_fQ: "p \<bullet> \<langle>f\<rangle>Q = \<langle>f\<rangle>Q" and p_Ff: "p \<bullet> (F,f) = (F,f)"
              by (simp add: fresh_star_def perm_supp_eq)+
            from p and p_Ff have "\<alpha>\<^sub>L = Act (p \<bullet> \<alpha>)" and "P\<^sub>L' = EF (L (p \<bullet> \<alpha>, F, f), p \<bullet> P')"
              by auto

            moreover from Q\<^sub>L and p_fQ and p_Ff have "p \<bullet> Q\<^sub>L = Q\<^sub>L"
              by simp
            with trans_Q\<^sub>L have "Q\<^sub>L \<rightarrow>\<^sub>L p \<bullet> \<langle>Act \<alpha>, EF (L (\<alpha>,F,f), Q')\<rangle>"
              by (metis L_transform.transition_eqvt)
            then have "Q\<^sub>L \<rightarrow>\<^sub>L \<langle>Act (p \<bullet> \<alpha>), EF (L (p \<bullet> \<alpha>, F, f), p \<bullet> Q')\<rangle>"
              using p_Ff by simp

            moreover from p_Ff have "p \<bullet> F = F" and "p \<bullet> f = f"
              by simp+
            with bisim' have "(p \<bullet> P') \<sim>\<cdot>[L (p \<bullet> \<alpha>, F, f)] (p \<bullet> Q')"
              by (metis FL_bisimilar_eqvt L_eqvt')
            then have "L_bisimilar (EF (L (p \<bullet> \<alpha>, F, f), p \<bullet> P')) (EF (L (p \<bullet> \<alpha>, F, f), p \<bullet> Q'))"
              by (metis L_bisimilar.intros(1))

            ultimately show thesis
                using \<open>\<And>Q\<^sub>L'. Q\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,Q\<^sub>L'\<rangle> \<Longrightarrow> L_bisimilar P\<^sub>L' Q\<^sub>L' \<Longrightarrow> thesis\<close> by blast
          qed
        then show "\<exists>Q\<^sub>L'. Q\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,Q\<^sub>L'\<rangle> \<and> L_bisimilar P\<^sub>L' Q\<^sub>L'"
          by auto
      qed
    ultimately show "?S \<and> ?T"
      by metis
  qed

  definition invL_FL_bisimilar :: "'effect first \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
    "invL_FL_bisimilar F P Q \<equiv> EF (F,P) \<sim>\<cdot>\<^sub>L EF(F,Q)"

  lemma invL_FL_bisimilar_is_L_bisimulation: "is_L_bisimulation invL_FL_bisimilar"
  unfolding is_L_bisimulation_def
  proof
    fix F
    have "symp (invL_FL_bisimilar F)" (is ?R)
      by (metis L_transform.bisimilar_symp invL_FL_bisimilar_def symp_def)
    moreover have "\<forall>P Q. invL_FL_bisimilar F P Q \<longrightarrow> (\<forall>f. f \<in>\<^sub>f\<^sub>s F \<longrightarrow> (\<forall>\<phi>. \<langle>f\<rangle>P \<turnstile> \<phi> \<longrightarrow> \<langle>f\<rangle>Q \<turnstile> \<phi>))" (is ?S)
      proof (clarify)
        fix P Q f \<phi>
        assume bisim: "invL_FL_bisimilar F P Q" and effect: "f \<in>\<^sub>f\<^sub>s F" and satisfies: "\<langle>f\<rangle>P \<turnstile> \<phi>"
        from bisim have "EF (F,P) \<sim>\<cdot>\<^sub>L EF (F,Q)"
          by (metis invL_FL_bisimilar_def)
        moreover have "bn (Eff f) \<sharp>* EF (F,Q)"
          by (simp add: fresh_star_def)
        moreover from effect have "EF (F,P) \<rightarrow>\<^sub>L \<langle>Eff f, AC (f, F, \<langle>f\<rangle>P)\<rangle>"
          by (metis L_transition.simps(2))
        ultimately obtain Q\<^sub>L' where trans: "EF (F,Q) \<rightarrow>\<^sub>L \<langle>Eff f, Q\<^sub>L'\<rangle>" and L_bisim: "AC (f, F, \<langle>f\<rangle>P) \<sim>\<cdot>\<^sub>L Q\<^sub>L'"
          by (metis L_transform.bisimilar_simulation_step)
        from trans obtain f' where "\<langle>Eff f :: ('act,'effect) L_action, Q\<^sub>L'\<rangle> = \<langle>Eff f', AC (f', F, \<langle>f'\<rangle>Q)\<rangle>"
          by (metis L_transition.simps(2))
        then have Q\<^sub>L': "Q\<^sub>L' = AC (f, F, \<langle>f\<rangle>Q)"
          by (metis L_action.inject(2) bn_L_action.simps(2) residual_empty_bn_eq_iff)

        from satisfies have "AC (f, F, \<langle>f\<rangle>P) \<turnstile>\<^sub>L \<phi>"
          by (metis L_satisfies.simps(1))
        with L_bisim and Q\<^sub>L' have "AC (f, F, \<langle>f\<rangle>Q) \<turnstile>\<^sub>L \<phi>"
          by (metis L_transform.bisimilar_is_bisimulation L_transform.is_bisimulation_def)
        then show "\<langle>f\<rangle>Q \<turnstile> \<phi>"
          by (metis L_satisfies.simps(1))
      qed
    moreover have "\<forall>P Q. invL_FL_bisimilar F P Q \<longrightarrow> (\<forall>f. f \<in>\<^sub>f\<^sub>s F \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F, f) \<longrightarrow>
        \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. \<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> invL_FL_bisimilar (L (\<alpha>, F, f)) P' Q')))" (is ?T)
      proof (clarify)
        fix P Q f \<alpha> P'
        assume bisim: "invL_FL_bisimilar F P Q" and effect: "f \<in>\<^sub>f\<^sub>s F" and fresh: "bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F, f)" and trans: "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
        from bisim have "EF (F,P) \<sim>\<cdot>\<^sub>L EF (F,Q)"
          by (metis invL_FL_bisimilar_def)
        moreover have "bn (Eff f) \<sharp>* EF (F,Q)"
          by (simp add: fresh_star_def)
        moreover from effect have "EF (F,P) \<rightarrow>\<^sub>L \<langle>Eff f, AC (f, F, \<langle>f\<rangle>P)\<rangle>"
          by (metis L_transition.simps(2))
        ultimately obtain Q\<^sub>L' where trans\<^sub>L: "EF (F,Q) \<rightarrow>\<^sub>L \<langle>Eff f, Q\<^sub>L'\<rangle>" and L_bisim: "AC (f, F, \<langle>f\<rangle>P) \<sim>\<cdot>\<^sub>L Q\<^sub>L'"
          by (metis L_transform.bisimilar_simulation_step)
        from trans\<^sub>L obtain f' where "\<langle>Eff f :: ('act,'effect) L_action, Q\<^sub>L'\<rangle> = \<langle>Eff f', AC (f', F, \<langle>f'\<rangle>Q)\<rangle>"
          by (metis L_transition.simps(2))
        then have Q\<^sub>L': "Q\<^sub>L' = AC (f, F, \<langle>f\<rangle>Q)"
          by (metis L_action.inject(2) bn_L_action.simps(2) residual_empty_bn_eq_iff)

        from L_bisim and Q\<^sub>L' have "AC (f, F, \<langle>f\<rangle>P) \<sim>\<cdot>\<^sub>L AC (f, F, \<langle>f\<rangle>Q)"
          by metis
        moreover from fresh have "bn (Act \<alpha>) \<sharp>* AC (f, F, \<langle>f\<rangle>Q)"
          by (simp add: fresh_def fresh_star_def supp_Pair)
        moreover from fresh have "bn \<alpha> \<sharp>* (F, f)"
          by (simp add: fresh_star_Pair)
        with trans have "AC (f, F, \<langle>f\<rangle>P) \<rightarrow>\<^sub>L \<langle>Act \<alpha>, EF (L (\<alpha>,F,f), P')\<rangle>"
          by (metis L_transition.simps(1))
        ultimately obtain Q\<^sub>L'' where trans\<^sub>L': "AC (f, F, \<langle>f\<rangle>Q) \<rightarrow>\<^sub>L \<langle>Act \<alpha>, Q\<^sub>L''\<rangle>" and L_bisim': "EF (L (\<alpha>,F,f), P') \<sim>\<cdot>\<^sub>L Q\<^sub>L''"
          by (metis L_transform.bisimilar_simulation_step)

        have "finite (supp (\<langle>f\<rangle>Q, F, f))"
          by (fact finite_supp)
        with trans\<^sub>L' obtain \<alpha>' Q' where trans': "\<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>',Q'\<rangle>" and alpha: "\<langle>Act \<alpha> :: ('act,'effect) L_action, Q\<^sub>L''\<rangle> = \<langle>Act \<alpha>', EF (L (\<alpha>',F,f), Q')\<rangle>" and fresh': "bn \<alpha>' \<sharp>* (\<langle>f\<rangle>Q, F,f)"
          by (metis L_transition_AC_strong)

        from alpha obtain p where p: "(Act \<alpha> :: ('act,'effect) L_action, Q\<^sub>L'') = p \<bullet> (Act \<alpha>', EF (L (\<alpha>',F,f), Q'))" and supp_p: "supp p \<subseteq> bn \<alpha> \<union> bn \<alpha>'"
          by (metis Un_commute bn_L_action.simps(1) residual_eq_iff_perm_renaming)
        from supp_p and fresh and fresh' have "supp p \<sharp>* (\<langle>f\<rangle>Q, F,f)"
          unfolding fresh_star_def by (metis (no_types, hide_lams) Un_iff subsetCE)
        then have p_fQ: "p \<bullet> \<langle>f\<rangle>Q = \<langle>f\<rangle>Q" and p_F: "p \<bullet> F = F" and p_f: "p \<bullet> f = f"
          by (simp add: fresh_star_def perm_supp_eq)+
        from p and p_F and p_f have p_\<alpha>': "p \<bullet> \<alpha>' = \<alpha>" and Q\<^sub>L'': "Q\<^sub>L'' = EF (L (p \<bullet> \<alpha>', F, f), p \<bullet> Q')"
          by auto

        from trans' and p_fQ and p_\<alpha>' have "\<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>, p \<bullet> Q'\<rangle>"
          by (metis transition_eqvt')
        moreover from L_bisim' and Q\<^sub>L'' and p_\<alpha>' have "invL_FL_bisimilar (L (\<alpha>,F,f)) P' (p \<bullet> Q')"
          by (metis invL_FL_bisimilar_def)
        ultimately show "\<exists>Q'. \<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> invL_FL_bisimilar (L (\<alpha>,F,f)) P' Q'"
          by metis
      qed
    ultimately show "?R \<and> ?S \<and> ?T"
      by metis
  qed

  theorem "P \<sim>\<cdot>[F] Q \<longleftrightarrow> EF (F,P) \<sim>\<cdot>\<^sub>L EF(F,Q)"
  proof
    assume "P \<sim>\<cdot>[F] Q"
    then have "L_bisimilar (EF (F,P)) (EF (F,Q))"
        by (metis L_bisimilar.intros(1))
    then show "EF (F,P) \<sim>\<cdot>\<^sub>L EF(F,Q)"
      by (metis L_bisimilar_is_L_transform_bisimulation L_transform.bisimilar_def)
  next
    assume "EF (F, P) \<sim>\<cdot>\<^sub>L EF (F, Q)"
    then have "invL_FL_bisimilar F P Q"
      by (metis invL_FL_bisimilar_def)
    then show "P \<sim>\<cdot>[F] Q"
      by (metis invL_FL_bisimilar_is_L_bisimulation FL_bisimilar_def)
  qed

end

text \<open>The following (alternative) proof of the ``$\leftarrow$'' direction of this equivalence,
namely that bisimilarity in the $L$-transform implies $F/L$-bisimilarity, uses the fact that the
$L$-transform preserves satisfaction of formulas, together with the fact that bisimilarity (in the
$L$-transform) implies logical equivalence. However, since we proved the latter in the context of
indexed nominal transition systems, this proof requires an indexed nominal transition system with
effects where, additionally, the cardinality of the state set of the $L$-transform is bounded. We
could re-organize our formalization to remove this assumption: the proof of
@{thm indexed_nominal_ts.bisimilarity_implies_equivalence} does not actually make use of the
cardinality assumptions provided by indexed nominal transition systems.\<close>

locale L_transform_indexed_effect_nominal_ts = indexed_effect_nominal_ts L satisfies transition effect_apply
  for L :: "('act::bn) \<times> ('effect::fs) fs_set \<times> 'effect \<Rightarrow> 'effect fs_set" 
  and satisfies :: "'state::fs \<Rightarrow> 'pred::fs \<Rightarrow> bool" (infix "\<turnstile>" 70)
  and transition :: "'state \<Rightarrow> ('act,'state) residual \<Rightarrow> bool" (infix "\<rightarrow>" 70)
  and effect_apply :: "'effect \<Rightarrow> 'state \<Rightarrow> 'state" ("\<langle>_\<rangle>_" [0,101] 100) +
  assumes card_idx_L_transform_state: "|UNIV::('state, 'effect) L_state set| <o |UNIV::'idx set|"
begin

  interpretation L_transform: indexed_nominal_ts "(\<turnstile>\<^sub>L)" "(\<rightarrow>\<^sub>L)"
    by unfold_locales (fact L_satisfies_eqvt, fact L_transition_eqvt, fact card_idx_perm, fact card_idx_L_transform_state)

  notation L_transform.bisimilar (infix "\<sim>\<cdot>\<^sub>L" 100)

  theorem "EF (F,P) \<sim>\<cdot>\<^sub>L EF(F,Q) \<longrightarrow> P \<sim>\<cdot>[F] Q"
  proof
    assume "EF (F, P) \<sim>\<cdot>\<^sub>L EF (F, Q)"
    then have "L_transform.logically_equivalent (EF (F, P)) (EF (F, Q))"
      by (fact L_transform.bisimilarity_implies_equivalence)
    with FL_valid_iff_valid_L_transform have "FL_logically_equivalent F P Q"
      using FL_logically_equivalent_def L_transform.logically_equivalent_def by blast
    then show "P \<sim>\<cdot>[F] Q"
      by (fact FL_equivalence_implies_bisimilarity)
  qed

end

end
