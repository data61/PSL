theory FL_Validity
imports
  FL_Transition_System
  FL_Formula
begin

section \<open>Validity With Effects\<close>

text \<open>The following is needed to prove termination of~@{term FL_validTree}.\<close>

definition alpha_Tree_rel where
  "alpha_Tree_rel \<equiv> {(x,y). x =\<^sub>\<alpha> y}"

lemma alpha_Tree_relI [simp]:
  assumes "x =\<^sub>\<alpha> y" shows "(x,y) \<in> alpha_Tree_rel"
using assms unfolding alpha_Tree_rel_def by simp

lemma alpha_Tree_relE:
  assumes "(x,y) \<in> alpha_Tree_rel" and "x =\<^sub>\<alpha> y \<Longrightarrow> P"
  shows P
using assms unfolding alpha_Tree_rel_def by simp

lemma wf_alpha_Tree_rel_hull_rel_Tree_wf:
  "wf (alpha_Tree_rel O hull_rel O Tree_wf)"
proof (rule wf_relcomp_compatible)
  show "wf (hull_rel O Tree_wf)"
    by (metis Tree_wf_eqvt' wf_Tree_wf wf_hull_rel_relcomp)
next
  show "(hull_rel O Tree_wf) O alpha_Tree_rel \<subseteq> alpha_Tree_rel O (hull_rel O Tree_wf)"
  proof
    fix x :: "('e, 'f, 'g, 'h) Tree \<times> ('e, 'f, 'g, 'h) Tree"
    assume "x \<in> (hull_rel O Tree_wf) O alpha_Tree_rel"
    then obtain x1 x2 x3 x4 where x: "x = (x1,x4)" and 1: "(x1,x2) \<in> hull_rel" and 2: "(x2,x3) \<in> Tree_wf" and 3: "(x3,x4) \<in> alpha_Tree_rel"
      by auto
    from 2 have "(x1,x4) \<in> alpha_Tree_rel O hull_rel O Tree_wf"
      using 1 and 3 proof (induct rule: Tree_wf.induct)
        \<comment> \<open>@{const tConj}\<close>
        fix t and tset :: "('e,'f,'g,'h) Tree set['e]"
        assume *: "t \<in> set_bset tset" and **: "(x1,t) \<in> hull_rel" and ***: "(tConj tset, x4) \<in> alpha_Tree_rel"
        from "**" obtain p where x1: "x1 = p \<bullet> t"
          using hull_rel.cases by blast
        from "***" have "tConj tset =\<^sub>\<alpha> x4"
          by (rule alpha_Tree_relE)
        then obtain tset' where x4: "x4 = tConj tset'" and "rel_bset (=\<^sub>\<alpha>) tset tset'"
          by (cases "x4") simp_all
        with "*" obtain t' where t': "t' \<in> set_bset tset'" and "t =\<^sub>\<alpha> t'"
          by (metis rel_bset.rep_eq rel_set_def)
        with x1 have "(x1, p \<bullet> t') \<in> alpha_Tree_rel"
          by (metis Tree\<^sub>\<alpha>.abs_eq_iff alpha_Tree_relI permute_Tree\<^sub>\<alpha>.abs_eq)
        moreover have "(p \<bullet> t', t') \<in> hull_rel"
          by (rule hull_rel.intros)
        moreover from x4 and t' have "(t', x4) \<in> Tree_wf"
          by (simp add: Tree_wf.intros(1))
        ultimately show "(x1,x4) \<in> alpha_Tree_rel O hull_rel O Tree_wf"
          by auto
      next
        \<comment> \<open>@{const tNot}\<close>
        fix t
        assume *: "(x1,t) \<in> hull_rel" and **: "(tNot t, x4) \<in> alpha_Tree_rel"
        from "*" obtain p where x1: "x1 = p \<bullet> t"
          using hull_rel.cases by blast
        from "**" have "tNot t =\<^sub>\<alpha> x4"
          by (rule alpha_Tree_relE)
        then obtain t' where x4: "x4 = tNot t'" and "t =\<^sub>\<alpha> t'"
          by (cases "x4") simp_all
        with x1 have "(x1, p \<bullet> t') \<in> alpha_Tree_rel"
          by (metis Tree\<^sub>\<alpha>.abs_eq_iff alpha_Tree_relI permute_Tree\<^sub>\<alpha>.abs_eq x1)
        moreover have "(p \<bullet> t', t') \<in> hull_rel"
          by (rule hull_rel.intros)
        moreover from x4 have "(t', x4) \<in> Tree_wf"
          using Tree_wf.intros(2) by blast
        ultimately show "(x1,x4) \<in> alpha_Tree_rel O hull_rel O Tree_wf"
          by auto
      next
        \<comment> \<open>@{const tAct}\<close>
        fix f \<alpha> t
        assume *: "(x1,t) \<in> hull_rel" and **: "(tAct f \<alpha> t, x4) \<in> alpha_Tree_rel"
        from "*" obtain p where x1: "x1 = p \<bullet> t"
          using hull_rel.cases by blast
        from "**" have "tAct f \<alpha> t =\<^sub>\<alpha> x4"
          by (rule alpha_Tree_relE)
        then obtain q t' where x4: "x4 = tAct f (q \<bullet> \<alpha>) t'" and "q \<bullet> t =\<^sub>\<alpha> t'"
          by (cases "x4") (auto simp add: alpha_set)
        with x1 have "(x1, p \<bullet> -q \<bullet> t') \<in> alpha_Tree_rel"
          by (metis Tree\<^sub>\<alpha>.abs_eq_iff alpha_Tree_relI permute_Tree\<^sub>\<alpha>.abs_eq permute_minus_cancel(1))
        moreover have "(p \<bullet> -q \<bullet> t', t') \<in> hull_rel"
          by (metis hull_rel.simps permute_plus)
        moreover from x4 have "(t', x4) \<in> Tree_wf"
          by (simp add: Tree_wf.intros(3))
        ultimately show "(x1,x4) \<in> alpha_Tree_rel O hull_rel O Tree_wf"
          by auto
      qed
    with x show "x \<in> alpha_Tree_rel O hull_rel O Tree_wf"
      by simp
  qed
qed

lemma alpha_Tree_rel_relcomp_trivialI [simp]:
  assumes "(x, y) \<in> R"
  shows "(x, y) \<in> alpha_Tree_rel O R"
using assms unfolding alpha_Tree_rel_def
by (metis Tree\<^sub>\<alpha>.abs_eq_iff case_prodI mem_Collect_eq relcomp.relcompI)

lemma alpha_Tree_rel_relcompI [simp]:
  assumes "x =\<^sub>\<alpha> x'" and "(x', y) \<in> R"
  shows "(x, y) \<in> alpha_Tree_rel O R"
using assms unfolding alpha_Tree_rel_def
by (metis case_prodI mem_Collect_eq relcomp.relcompI)


subsection \<open>Validity for infinitely branching trees\<close>

context effect_nominal_ts
begin

  text \<open>Since we defined formulas via a manual quotient construction, we also need to define
  validity via lifting from the underlying type of infinitely branching trees. We cannot use
  {\bf nominal\_function} because that generates proof obligations where, for formulas of the
  form~@{term "Conj xset"}, the assumption that~@{term xset} has finite support is missing.\<close>

  declare conj_cong [fundef_cong]

  function (sequential) FL_valid_Tree :: "'state \<Rightarrow> ('idx,'pred,'act,'effect) Tree \<Rightarrow> bool" where
    "FL_valid_Tree P (tConj tset) \<longleftrightarrow> (\<forall>t\<in>set_bset tset. FL_valid_Tree P t)"
  | "FL_valid_Tree P (tNot t) \<longleftrightarrow> \<not> FL_valid_Tree P t"
  | "FL_valid_Tree P (tPred f \<phi>) \<longleftrightarrow> \<langle>f\<rangle>P \<turnstile> \<phi>"
  | "FL_valid_Tree P (tAct f \<alpha> t) \<longleftrightarrow> (\<exists>\<alpha>' t' P'. tAct f \<alpha> t =\<^sub>\<alpha> tAct f \<alpha>' t' \<and> \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> FL_valid_Tree P' t')"
  by pat_completeness auto
  termination proof
    let ?R = "inv_image (alpha_Tree_rel O hull_rel O Tree_wf) snd"
    {
      show "wf ?R"
        by (metis wf_alpha_Tree_rel_hull_rel_Tree_wf wf_inv_image)
    next
      fix P :: 'state and tset :: "('idx,'pred,'act,'effect) Tree set['idx]" and t
      assume "t \<in> set_bset tset" then show "((P, t), (P, tConj tset)) \<in> ?R"
        by (simp add: Tree_wf.intros(1))
    next
      fix P :: 'state and t :: "('idx,'pred,'act,'effect) Tree"
      show "((P, t), (P, tNot t)) \<in> ?R"
        by (simp add: Tree_wf.intros(2))
    next
      fix P1 P2 :: 'state and f and \<alpha>1 \<alpha>2 and t1 t2 :: "('idx,'pred,'act,'effect) Tree"
      assume "tAct f \<alpha>1 t1 =\<^sub>\<alpha> tAct f \<alpha>2 t2"
      then obtain p where "t2 =\<^sub>\<alpha> p \<bullet> t1"
        by (auto simp add: alphas) (metis alpha_Tree_symp sympE)
      then show "((P2, t2), (P1, tAct f \<alpha>1 t1)) \<in> ?R"
        by (simp add: Tree_wf.intros(3))
    }
  qed

  text \<open>@{const FL_valid_Tree} is equivariant.\<close>

  lemma FL_valid_Tree_eqvt': "FL_valid_Tree P t \<longleftrightarrow> FL_valid_Tree (p \<bullet> P) (p \<bullet> t)"
  proof (induction P t rule: FL_valid_Tree.induct)
    case (1 P tset) show ?case
      proof
        assume *: "FL_valid_Tree P (tConj tset)"
        {
          fix t
          assume "t \<in> p \<bullet> set_bset tset"
          with "1.IH" and "*" have "FL_valid_Tree (p \<bullet> P) t"
            by (metis (no_types, lifting) imageE permute_set_eq_image FL_valid_Tree.simps(1))
        }
        then show "FL_valid_Tree (p \<bullet> P) (p \<bullet> tConj tset)"
          by simp
      next
        assume *: "FL_valid_Tree (p \<bullet> P) (p \<bullet> tConj tset)"
        {
          fix t
          assume "t \<in> set_bset tset"
          with "1.IH" and "*" have "FL_valid_Tree P t"
            by (metis mem_permute_iff permute_Tree_tConj set_bset_eqvt FL_valid_Tree.simps(1))
        }
        then show "FL_valid_Tree P (tConj tset)"
          by simp
      qed
  next
    case 2 then show ?case by simp
  next
    case 3 show ?case by simp (metis effect_apply_eqvt' permute_minus_cancel(2) satisfies_eqvt)
  next
    case (4 P f \<alpha> t) show ?case
      proof
        assume "FL_valid_Tree P (tAct f \<alpha> t)"
        then obtain \<alpha>' t' P' where *: "tAct f \<alpha> t =\<^sub>\<alpha> tAct f \<alpha>' t' \<and> \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> FL_valid_Tree P' t'"
          by auto
        with "4.IH" have "FL_valid_Tree (p \<bullet> P') (p \<bullet> t')"
          by blast
        moreover from "*" have "p \<bullet> \<langle>f\<rangle>P \<rightarrow> \<langle>p \<bullet> \<alpha>', p \<bullet> P'\<rangle>"
          by (metis transition_eqvt')
        moreover from "*" have "p \<bullet> tAct f \<alpha> t =\<^sub>\<alpha> tAct (p \<bullet> f) (p \<bullet> \<alpha>') (p \<bullet> t')"
          by (metis alpha_Tree_eqvt permute_Tree.simps(4))
        ultimately show "FL_valid_Tree (p \<bullet> P) (p \<bullet> tAct f \<alpha> t)"
          by auto
      next
        assume "FL_valid_Tree (p \<bullet> P) (p \<bullet> tAct f \<alpha> t)"
        then obtain \<alpha>' t' P' where *: "p \<bullet> tAct f \<alpha> t =\<^sub>\<alpha> tAct (p \<bullet> f) \<alpha>' t' \<and> (p \<bullet> \<langle>f\<rangle>P) \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> FL_valid_Tree P' t'"
          by auto
        then have eq: "tAct f \<alpha> t =\<^sub>\<alpha> tAct f (-p \<bullet> \<alpha>') (-p \<bullet> t')"
          by (metis alpha_Tree_eqvt permute_Tree.simps(4) permute_minus_cancel(2))
        moreover from "*" have "\<langle>f\<rangle>P \<rightarrow> \<langle>-p \<bullet> \<alpha>', -p \<bullet> P'\<rangle>"
          by (metis permute_minus_cancel(2) transition_eqvt')
        moreover with "4.IH" have "FL_valid_Tree (-p \<bullet> P') (-p \<bullet> t')"
          using eq and "*" by simp
        ultimately show "FL_valid_Tree P (tAct f \<alpha> t)"
          by auto
      qed
  qed

  lemma FL_valid_Tree_eqvt [eqvt]:
    assumes "FL_valid_Tree P t" shows "FL_valid_Tree (p \<bullet> P) (p \<bullet> t)"
  using assms by (metis FL_valid_Tree_eqvt')

  text \<open>$\alpha$-equivalent trees validate the same states.\<close>

  lemma alpha_Tree_FL_valid_Tree:
    assumes "t1 =\<^sub>\<alpha> t2"
    shows "FL_valid_Tree P t1 \<longleftrightarrow> FL_valid_Tree P t2"
  using assms proof (induction t1 t2 arbitrary: P rule: alpha_Tree_induct)
    case tConj then show ?case
      by auto (metis (mono_tags) rel_bset.rep_eq rel_set_def)+
  next
    case (tAct f1 \<alpha>1 t1 f2 \<alpha>2 t2) show ?case
    proof
      assume "FL_valid_Tree P (tAct f1 \<alpha>1 t1)"
      then obtain \<alpha>' t' P' where "tAct f1 \<alpha>1 t1 =\<^sub>\<alpha> tAct f1 \<alpha>' t' \<and> \<langle>f1\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> FL_valid_Tree P' t'"
        by auto
      moreover from tAct.hyps have "tAct f1 \<alpha>1 t1 =\<^sub>\<alpha> tAct f2 \<alpha>2 t2"
        using alpha_tAct by blast
      ultimately show "FL_valid_Tree P (tAct f2 \<alpha>2 t2)"
        using tAct.hyps by (metis Tree\<^sub>\<alpha>.abs_eq_iff FL_valid_Tree.simps(4))
    next
      assume "FL_valid_Tree P (tAct f2 \<alpha>2 t2)"
      then obtain \<alpha>' t' P' where "tAct f2 \<alpha>2 t2 =\<^sub>\<alpha> tAct f2 \<alpha>' t' \<and> \<langle>f2\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> FL_valid_Tree P' t'"
        by auto
      moreover from tAct.hyps have "tAct f1 \<alpha>1 t1 =\<^sub>\<alpha> tAct f2 \<alpha>2 t2"
        using alpha_tAct by blast
      ultimately show "FL_valid_Tree P (tAct f1 \<alpha>1 t1)"
        using tAct.hyps by (metis Tree\<^sub>\<alpha>.abs_eq_iff FL_valid_Tree.simps(4))
    qed
  qed simp_all


  subsection \<open>Validity for trees modulo \texorpdfstring{$\alpha$}{alpha}-equivalence\<close>

  lift_definition FL_valid_Tree\<^sub>\<alpha> :: "'state \<Rightarrow> ('idx,'pred,'act,'effect) Tree\<^sub>\<alpha> \<Rightarrow> bool" is
    FL_valid_Tree
  by (fact alpha_Tree_FL_valid_Tree)

  lemma FL_valid_Tree\<^sub>\<alpha>_eqvt [eqvt]:
    assumes "FL_valid_Tree\<^sub>\<alpha> P t" shows "FL_valid_Tree\<^sub>\<alpha> (p \<bullet> P) (p \<bullet> t)"
  using assms by transfer (fact FL_valid_Tree_eqvt)

  lemma FL_valid_Tree\<^sub>\<alpha>_Conj\<^sub>\<alpha> [simp]: "FL_valid_Tree\<^sub>\<alpha> P (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>) \<longleftrightarrow> (\<forall>t\<^sub>\<alpha>\<in>set_bset tset\<^sub>\<alpha>. FL_valid_Tree\<^sub>\<alpha> P t\<^sub>\<alpha>)"
  proof -
    have "FL_valid_Tree P (rep_Tree\<^sub>\<alpha> (abs_Tree\<^sub>\<alpha> (tConj (map_bset rep_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>)))) \<longleftrightarrow> FL_valid_Tree P (tConj (map_bset rep_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>))"
      by (metis Tree\<^sub>\<alpha>_rep_abs alpha_Tree_FL_valid_Tree)
    then show ?thesis
      by (simp add: FL_valid_Tree\<^sub>\<alpha>_def Conj\<^sub>\<alpha>_def map_bset.rep_eq)
  qed

  lemma FL_valid_Tree\<^sub>\<alpha>_Not\<^sub>\<alpha> [simp]: "FL_valid_Tree\<^sub>\<alpha> P (Not\<^sub>\<alpha> t\<^sub>\<alpha>) \<longleftrightarrow> \<not> FL_valid_Tree\<^sub>\<alpha> P t\<^sub>\<alpha>"
  by transfer simp

  lemma FL_valid_Tree\<^sub>\<alpha>_Pred\<^sub>\<alpha> [simp]: "FL_valid_Tree\<^sub>\<alpha> P (Pred\<^sub>\<alpha> f \<phi>) \<longleftrightarrow> \<langle>f\<rangle>P \<turnstile> \<phi>"
  by transfer simp

  lemma FL_valid_Tree\<^sub>\<alpha>_Act\<^sub>\<alpha> [simp]: "FL_valid_Tree\<^sub>\<alpha> P (Act\<^sub>\<alpha> f \<alpha> t\<^sub>\<alpha>) \<longleftrightarrow> (\<exists>\<alpha>' t\<^sub>\<alpha>' P'. Act\<^sub>\<alpha> f \<alpha> t\<^sub>\<alpha> = Act\<^sub>\<alpha> f \<alpha>' t\<^sub>\<alpha>' \<and> \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> FL_valid_Tree\<^sub>\<alpha> P' t\<^sub>\<alpha>')"
  proof
    assume "FL_valid_Tree\<^sub>\<alpha> P (Act\<^sub>\<alpha> f \<alpha> t\<^sub>\<alpha>)"
    moreover have "Act\<^sub>\<alpha> f \<alpha> t\<^sub>\<alpha> = abs_Tree\<^sub>\<alpha> (tAct f \<alpha> (rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>))"
      by (metis Act\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>_abs_rep)
    ultimately show "\<exists>\<alpha>' t\<^sub>\<alpha>' P'. Act\<^sub>\<alpha> f \<alpha> t\<^sub>\<alpha> = Act\<^sub>\<alpha> f \<alpha>' t\<^sub>\<alpha>' \<and> \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> FL_valid_Tree\<^sub>\<alpha> P' t\<^sub>\<alpha>'"
      by (metis Act\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff FL_valid_Tree.simps(4) FL_valid_Tree\<^sub>\<alpha>.abs_eq)
  next
    assume "\<exists>\<alpha>' t\<^sub>\<alpha>' P'. Act\<^sub>\<alpha> f \<alpha> t\<^sub>\<alpha> = Act\<^sub>\<alpha> f \<alpha>' t\<^sub>\<alpha>' \<and> \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> FL_valid_Tree\<^sub>\<alpha> P' t\<^sub>\<alpha>'"
    moreover have "\<And>\<alpha>' t\<^sub>\<alpha>'. Act\<^sub>\<alpha> f \<alpha>' t\<^sub>\<alpha>' = abs_Tree\<^sub>\<alpha> (tAct f \<alpha>' (rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>'))"
      by (metis Act\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>_abs_rep)
    ultimately show "FL_valid_Tree\<^sub>\<alpha> P (Act\<^sub>\<alpha> f \<alpha> t\<^sub>\<alpha>)"
      by (metis Tree\<^sub>\<alpha>.abs_eq_iff FL_valid_Tree.simps(4) FL_valid_Tree\<^sub>\<alpha>.abs_eq FL_valid_Tree\<^sub>\<alpha>.rep_eq)
  qed


  subsection \<open>Validity for infinitary formulas\<close>

  lift_definition FL_valid :: "'state \<Rightarrow> ('idx,'pred,'act,'effect) formula \<Rightarrow> bool" (infix "\<Turnstile>" 70) is
    FL_valid_Tree\<^sub>\<alpha>
  .

  lemma FL_valid_eqvt [eqvt]:
    assumes "P \<Turnstile> x" shows "(p \<bullet> P) \<Turnstile> (p \<bullet> x)"
  using assms by transfer (metis FL_valid_Tree\<^sub>\<alpha>_eqvt)

  lemma FL_valid_Conj [simp]:
    assumes "finite (supp xset)"
    shows "P \<Turnstile> Conj xset \<longleftrightarrow> (\<forall>x\<in>set_bset xset. P \<Turnstile> x)"
  using assms by (simp add: FL_valid_def Conj_def map_bset.rep_eq)

  lemma FL_valid_Not [simp]: "P \<Turnstile> Not x \<longleftrightarrow> \<not> P \<Turnstile> x"
  by transfer simp

  lemma FL_valid_Pred [simp]: "P \<Turnstile> Pred f \<phi> \<longleftrightarrow> \<langle>f\<rangle>P \<turnstile> \<phi>"
  by transfer simp

  lemma FL_valid_Act: "P \<Turnstile> Act f \<alpha> x \<longleftrightarrow> (\<exists>\<alpha>' x' P'. Act f \<alpha> x = Act f \<alpha>' x' \<and> \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> P' \<Turnstile> x')"
  proof
    assume "P \<Turnstile> Act f \<alpha> x"
    moreover have "Rep_formula (Abs_formula (Act\<^sub>\<alpha> f \<alpha> (Rep_formula x))) = Act\<^sub>\<alpha> f \<alpha> (Rep_formula x)"
      by (metis Act.rep_eq Rep_formula_inverse)
    ultimately show "\<exists>\<alpha>' x' P'. Act f \<alpha> x = Act f \<alpha>' x' \<and> \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> P' \<Turnstile> x'"
      by (auto simp add: FL_valid_def Act_def) (metis Abs_formula_inverse Rep_formula' hereditarily_fs_alpha_renaming)
  next
    assume "\<exists>\<alpha>' x' P'. Act f \<alpha> x = Act f \<alpha>' x' \<and> \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> P' \<Turnstile> x'"
    then show "P \<Turnstile> Act f \<alpha> x"
      by (metis Act.rep_eq FL_valid.rep_eq FL_valid_Tree\<^sub>\<alpha>_Act\<^sub>\<alpha>)
  qed

  text \<open>The binding names in the alpha-variant that witnesses validity may be chosen fresh for any
  finitely supported context.\<close>

  lemma FL_valid_Act_strong:
    assumes "finite (supp X)"
    shows "P \<Turnstile> Act f \<alpha> x \<longleftrightarrow> (\<exists>\<alpha>' x' P'. Act f \<alpha> x = Act f \<alpha>' x' \<and> \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> P' \<Turnstile> x' \<and> bn \<alpha>' \<sharp>* X)"
  proof
    assume "P \<Turnstile> Act f \<alpha> x"
    then obtain \<alpha>' x' P' where eq: "Act f \<alpha> x = Act f \<alpha>' x'" and trans: "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle>" and valid: "P' \<Turnstile> x'"
      by (metis FL_valid_Act)

    have "finite (bn \<alpha>')"
      by (fact bn_finite)
    moreover note \<open>finite (supp X)\<close>
    moreover have "finite (supp (supp x' - bn \<alpha>', supp \<alpha>' - bn \<alpha>', \<langle>\<alpha>',P'\<rangle>))"
      by (simp add: supp_Pair finite_sets_supp finite_supp)
    moreover have "bn \<alpha>' \<sharp>* (supp x' - bn \<alpha>', supp \<alpha>' - bn \<alpha>', \<langle>\<alpha>',P'\<rangle>)"
      by (simp add: atom_fresh_star_disjoint finite_supp fresh_star_Pair)
    ultimately obtain p where fresh_X: "(p \<bullet> bn \<alpha>') \<sharp>* X" and fresh_p: "supp (supp x' - bn \<alpha>', supp \<alpha>' - bn \<alpha>', \<langle>\<alpha>',P'\<rangle>) \<sharp>* p"
      by (metis at_set_avoiding2)

    from fresh_p have "supp (supp x' - bn \<alpha>') \<sharp>* p" and "supp (supp \<alpha>' - bn \<alpha>') \<sharp>* p" and 1: "supp \<langle>\<alpha>',P'\<rangle> \<sharp>* p"
      by (meson fresh_Pair fresh_def fresh_star_def)+
    then have 2: "(supp x' - bn \<alpha>') \<sharp>* p" and 3: "(supp \<alpha>' - bn \<alpha>') \<sharp>* p"
      by (simp add: finite_supp supp_finite_atom_set)+
    moreover from 2 have "supp (p \<bullet> x') - bn (p \<bullet> \<alpha>') = supp x' - bn \<alpha>'"
      by (metis Diff_eqvt atom_set_perm_eq bn_eqvt supp_eqvt)
    moreover from 3 have "supp (p \<bullet> \<alpha>') - bn (p \<bullet> \<alpha>') = supp \<alpha>' - bn \<alpha>'"
      by (metis (no_types, hide_lams) Diff_eqvt atom_set_perm_eq bn_eqvt supp_eqvt)
    ultimately have "Act f \<alpha>' x' = Act f (p \<bullet> \<alpha>') (p \<bullet> x')"
      by (auto simp add: Act_eq_iff_perm)

    moreover from 1 have "\<langle>p \<bullet> \<alpha>', p \<bullet> P'\<rangle> = \<langle>\<alpha>',P'\<rangle>"
      by (metis abs_residual_pair_eqvt supp_perm_eq)

    ultimately show "\<exists>\<alpha>' x' P'. Act f \<alpha> x = Act f \<alpha>' x' \<and> \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> P' \<Turnstile> x' \<and> bn \<alpha>' \<sharp>* X"
      using eq and trans and valid and fresh_X by (metis bn_eqvt FL_valid_eqvt)
  next
    assume "\<exists>\<alpha>' x' P'. Act f \<alpha> x = Act f \<alpha>' x' \<and> \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> P' \<Turnstile> x' \<and> bn \<alpha>' \<sharp>* X"
    then show "P \<Turnstile> Act f \<alpha> x" by (metis FL_valid_Act)
  qed

  lemma FL_valid_Act_fresh:
    assumes "bn \<alpha> \<sharp>* \<langle>f\<rangle>P"
    shows "P \<Turnstile> Act f \<alpha> x \<longleftrightarrow> (\<exists>P'. \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<and> P' \<Turnstile> x)"
  proof
    assume "P \<Turnstile> Act f \<alpha> x"

    moreover have "finite (supp (\<langle>f\<rangle>P))"
      by (fact finite_supp)
    ultimately obtain \<alpha>' x' P' where
      eq: "Act f \<alpha> x = Act f \<alpha>' x'" and trans: "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>',P'\<rangle>" and valid: "P' \<Turnstile> x'" and fresh: "bn \<alpha>' \<sharp>* \<langle>f\<rangle>P"
      by (metis FL_valid_Act_strong)

    from eq obtain p where p_\<alpha>: "\<alpha>' = p \<bullet> \<alpha>" and p_x: "x' = p \<bullet> x" and supp_p: "supp p \<subseteq> bn \<alpha> \<union> p \<bullet> bn \<alpha>"
      by (metis Act_eq_iff_perm_renaming)

    from assms and fresh have "(bn \<alpha> \<union> p \<bullet> bn \<alpha>) \<sharp>* \<langle>f\<rangle>P"
      using p_\<alpha> by (metis bn_eqvt fresh_star_Un)
    then have "supp p \<sharp>* \<langle>f\<rangle>P"
      using supp_p by (metis fresh_star_def subset_eq)
    then have p_P: "-p \<bullet> \<langle>f\<rangle>P = \<langle>f\<rangle>P"
      by (metis perm_supp_eq supp_minus_perm)

    from trans have "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,-p \<bullet> P'\<rangle>"
      using p_P p_\<alpha> by (metis permute_minus_cancel(1) transition_eqvt')
    moreover from valid have "-p \<bullet> P' \<Turnstile> x"
      using p_x by (metis permute_minus_cancel(1) FL_valid_eqvt)
    ultimately show "\<exists>P'. \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<and> P' \<Turnstile> x"
      by meson
  next
    assume "\<exists>P'. \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<and> P' \<Turnstile> x"
    then show "P \<Turnstile> Act f \<alpha> x"
      by (metis FL_valid_Act)
  qed

end

end
