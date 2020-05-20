theory Validity
imports
  Transition_System
  Formula
begin

section \<open>Validity\<close>

text \<open>The following is needed to prove termination of~@{term validTree}.\<close>

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
    fix x :: "('d, 'e, 'f) Tree \<times> ('d, 'e, 'f) Tree"
    assume "x \<in> (hull_rel O Tree_wf) O alpha_Tree_rel"
    then obtain x1 x2 x3 x4 where x: "x = (x1,x4)" and 1: "(x1,x2) \<in> hull_rel" and 2: "(x2,x3) \<in> Tree_wf" and 3: "(x3,x4) \<in> alpha_Tree_rel"
      by auto
    from 2 have "(x1,x4) \<in> alpha_Tree_rel O hull_rel O Tree_wf"
      using 1 and 3 proof (induct rule: Tree_wf.induct)
        \<comment> \<open>@{const tConj}\<close>
        fix t and tset :: "('d,'e,'f) Tree set['d]"
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
        fix \<alpha> t
        assume *: "(x1,t) \<in> hull_rel" and **: "(tAct \<alpha> t, x4) \<in> alpha_Tree_rel"
        from "*" obtain p where x1: "x1 = p \<bullet> t"
          using hull_rel.cases by blast
        from "**" have "tAct \<alpha> t =\<^sub>\<alpha> x4"
          by (rule alpha_Tree_relE)
        then obtain q t' where x4: "x4 = tAct (q \<bullet> \<alpha>) t'" and "q \<bullet> t =\<^sub>\<alpha> t'"
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

context nominal_ts
begin

  text \<open>Since we defined formulas via a manual quotient construction, we also need to define
  validity via lifting from the underlying type of infinitely branching trees. We cannot use
  {\bf nominal\_function} because that generates proof obligations where, for formulas of the
  form~@{term "Conj xset"}, the assumption that~@{term xset} has finite support is missing.\<close>

  declare conj_cong [fundef_cong]

  function valid_Tree :: "'state \<Rightarrow> ('idx,'pred,'act) Tree \<Rightarrow> bool" where
    "valid_Tree P (tConj tset) \<longleftrightarrow> (\<forall>t\<in>set_bset tset. valid_Tree P t)"
  | "valid_Tree P (tNot t) \<longleftrightarrow> \<not> valid_Tree P t"
  | "valid_Tree P (tPred \<phi>) \<longleftrightarrow> P \<turnstile> \<phi>"
  | "valid_Tree P (tAct \<alpha> t) \<longleftrightarrow> (\<exists>\<alpha>' t' P'. tAct \<alpha> t =\<^sub>\<alpha> tAct \<alpha>' t' \<and> P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> valid_Tree P' t')"
  by pat_completeness auto
  termination proof
    let ?R = "inv_image (alpha_Tree_rel O hull_rel O Tree_wf) snd"
    {
      show "wf ?R"
        by (metis wf_alpha_Tree_rel_hull_rel_Tree_wf wf_inv_image)
    next
      fix P :: 'state and tset :: "('idx,'pred,'act) Tree set['idx]" and t
      assume "t \<in> set_bset tset" then show "((P, t), (P, tConj tset)) \<in> ?R"
        by (simp add: Tree_wf.intros(1))
    next
      fix P :: 'state and t :: "('idx,'pred,'act) Tree"
      show "((P, t), (P, tNot t)) \<in> ?R"
        by (simp add: Tree_wf.intros(2))
    next
      fix P1 P2 :: 'state and \<alpha>1 \<alpha>2 :: 'act and t1 t2 :: "('idx,'pred,'act) Tree"
      assume "tAct \<alpha>1 t1 =\<^sub>\<alpha> tAct \<alpha>2 t2"
      then obtain p where "t2 =\<^sub>\<alpha> p \<bullet> t1"
        by (auto simp add: alphas) (metis alpha_Tree_symp sympE)
      then show "((P2, t2), (P1, tAct \<alpha>1 t1)) \<in> ?R"
        by (simp add: Tree_wf.intros(3))
    }
  qed

  text \<open>@{const valid_Tree} is equivariant.\<close>

  lemma valid_Tree_eqvt': "valid_Tree P t \<longleftrightarrow> valid_Tree (p \<bullet> P) (p \<bullet> t)"
  proof (induction P t rule: valid_Tree.induct)
    case (1 P tset) show ?case
      proof
        assume *: "valid_Tree P (tConj tset)"
        {
          fix t
          assume "t \<in> p \<bullet> set_bset tset"
          with "1.IH" and "*" have "valid_Tree (p \<bullet> P) t"
            by (metis (no_types, lifting) imageE permute_set_eq_image valid_Tree.simps(1))
        }
        then show "valid_Tree (p \<bullet> P) (p \<bullet> tConj tset)"
          by simp
      next
        assume *: "valid_Tree (p \<bullet> P) (p \<bullet> tConj tset)"
        {
          fix t
          assume "t \<in> set_bset tset"
          with "1.IH" and "*" have "valid_Tree P t"
            by (metis mem_permute_iff permute_Tree_tConj set_bset_eqvt valid_Tree.simps(1))
        }
        then show "valid_Tree P (tConj tset)"
          by simp
      qed
  next
    case 2 then show ?case by simp
  next
    case 3 show ?case by simp (metis permute_minus_cancel(2) satisfies_eqvt)
  next
    case (4 P \<alpha> t) show ?case
      proof
        assume "valid_Tree P (tAct \<alpha> t)"
        then obtain \<alpha>' t' P' where *: "tAct \<alpha> t =\<^sub>\<alpha> tAct \<alpha>' t' \<and> P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> valid_Tree P' t'"
          by auto
        with "4.IH" have "valid_Tree (p \<bullet> P') (p \<bullet> t')"
          by blast
        moreover from "*" have "p \<bullet> P \<rightarrow> \<langle>p \<bullet> \<alpha>', p \<bullet> P'\<rangle>"
          by (metis transition_eqvt')
        moreover from "*" have "p \<bullet> tAct \<alpha> t =\<^sub>\<alpha> tAct (p \<bullet> \<alpha>') (p \<bullet> t')"
          by (metis alpha_Tree_eqvt permute_Tree.simps(4))
        ultimately show "valid_Tree (p \<bullet> P) (p \<bullet> tAct \<alpha> t)"
          by auto
      next
        assume "valid_Tree (p \<bullet> P) (p \<bullet> tAct \<alpha> t)"
        then obtain \<alpha>' t' P' where *: "p \<bullet> tAct \<alpha> t =\<^sub>\<alpha> tAct \<alpha>' t' \<and> (p \<bullet> P) \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> valid_Tree P' t'"
          by auto
        then have eq: "tAct \<alpha> t =\<^sub>\<alpha> tAct (-p \<bullet> \<alpha>') (-p \<bullet> t')"
          by (metis alpha_Tree_eqvt permute_Tree.simps(4) permute_minus_cancel(2))
        moreover from "*" have "P \<rightarrow> \<langle>-p \<bullet> \<alpha>', -p \<bullet> P'\<rangle>"
          by (metis permute_minus_cancel(2) transition_eqvt')
        moreover with "4.IH" have "valid_Tree (-p \<bullet> P') (-p \<bullet> t')"
          using eq and "*" by simp
        ultimately show "valid_Tree P (tAct \<alpha> t)"
          by auto
      qed
  qed

  lemma valid_Tree_eqvt (*[eqvt]*):
    assumes "valid_Tree P t" shows "valid_Tree (p \<bullet> P) (p \<bullet> t)"
  using assms by (metis valid_Tree_eqvt')

  text \<open>$\alpha$-equivalent trees validate the same states.\<close>

  lemma alpha_Tree_valid_Tree:
    assumes "t1 =\<^sub>\<alpha> t2"
    shows "valid_Tree P t1 \<longleftrightarrow> valid_Tree P t2"
  using assms proof (induction t1 t2 arbitrary: P rule: alpha_Tree_induct)
    case tConj then show ?case
      by auto (metis (mono_tags) rel_bset.rep_eq rel_set_def)+
  next
    case (tAct \<alpha>1 t1 \<alpha>2 t2) show ?case
    proof
      assume "valid_Tree P (tAct \<alpha>1 t1)"
      then obtain \<alpha>' t' P' where "tAct \<alpha>1 t1 =\<^sub>\<alpha> tAct \<alpha>' t' \<and> P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> valid_Tree P' t'"
        by auto
      moreover from tAct.hyps have "tAct \<alpha>1 t1 =\<^sub>\<alpha> tAct \<alpha>2 t2"
        using alpha_tAct by blast
      ultimately show "valid_Tree P (tAct \<alpha>2 t2)"
        by (metis Tree\<^sub>\<alpha>.abs_eq_iff valid_Tree.simps(4))
    next
      assume "valid_Tree P (tAct \<alpha>2 t2)"
      then obtain \<alpha>' t' P' where "tAct \<alpha>2 t2 =\<^sub>\<alpha> tAct \<alpha>' t' \<and> P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> valid_Tree P' t'"
        by auto
      moreover from tAct.hyps have "tAct \<alpha>1 t1 =\<^sub>\<alpha> tAct \<alpha>2 t2"
        using alpha_tAct by blast
      ultimately show "valid_Tree P (tAct \<alpha>1 t1)"
        by (metis Tree\<^sub>\<alpha>.abs_eq_iff valid_Tree.simps(4))
    qed
  qed simp_all


  subsection \<open>Validity for trees modulo \texorpdfstring{$\alpha$}{alpha}-equivalence\<close>

  lift_definition valid_Tree\<^sub>\<alpha> :: "'state \<Rightarrow> ('idx,'pred,'act) Tree\<^sub>\<alpha> \<Rightarrow> bool" is
    valid_Tree
  by (fact alpha_Tree_valid_Tree)

  lemma valid_Tree\<^sub>\<alpha>_eqvt (*[eqvt]*):
    assumes "valid_Tree\<^sub>\<alpha> P t" shows "valid_Tree\<^sub>\<alpha> (p \<bullet> P) (p \<bullet> t)"
  using assms by transfer (fact valid_Tree_eqvt)

  lemma valid_Tree\<^sub>\<alpha>_Conj\<^sub>\<alpha> [simp]: "valid_Tree\<^sub>\<alpha> P (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>) \<longleftrightarrow> (\<forall>t\<^sub>\<alpha>\<in>set_bset tset\<^sub>\<alpha>. valid_Tree\<^sub>\<alpha> P t\<^sub>\<alpha>)"
  proof -
    have "valid_Tree P (rep_Tree\<^sub>\<alpha> (abs_Tree\<^sub>\<alpha> (tConj (map_bset rep_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>)))) \<longleftrightarrow> valid_Tree P (tConj (map_bset rep_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>))"
      by (metis Tree\<^sub>\<alpha>_rep_abs alpha_Tree_valid_Tree)
    then show ?thesis
      by (simp add: valid_Tree\<^sub>\<alpha>_def Conj\<^sub>\<alpha>_def map_bset.rep_eq)
  qed

  lemma valid_Tree\<^sub>\<alpha>_Not\<^sub>\<alpha> [simp]: "valid_Tree\<^sub>\<alpha> P (Not\<^sub>\<alpha> t\<^sub>\<alpha>) \<longleftrightarrow> \<not> valid_Tree\<^sub>\<alpha> P t\<^sub>\<alpha>"
  by transfer simp

  lemma valid_Tree\<^sub>\<alpha>_Pred\<^sub>\<alpha> [simp]: "valid_Tree\<^sub>\<alpha> P (Pred\<^sub>\<alpha> \<phi>) \<longleftrightarrow> P \<turnstile> \<phi>"
  by transfer simp

  lemma valid_Tree\<^sub>\<alpha>_Act\<^sub>\<alpha> [simp]: "valid_Tree\<^sub>\<alpha> P (Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>) \<longleftrightarrow> (\<exists>\<alpha>' t\<^sub>\<alpha>' P'. Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha> = Act\<^sub>\<alpha> \<alpha>' t\<^sub>\<alpha>' \<and> P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> valid_Tree\<^sub>\<alpha> P' t\<^sub>\<alpha>')"
  proof
    assume "valid_Tree\<^sub>\<alpha> P (Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>)"
    moreover have "Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha> = abs_Tree\<^sub>\<alpha> (tAct \<alpha> (rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>))"
      by (metis Act\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>_abs_rep)
    ultimately show "\<exists>\<alpha>' t\<^sub>\<alpha>' P'. Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha> = Act\<^sub>\<alpha> \<alpha>' t\<^sub>\<alpha>' \<and> P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> valid_Tree\<^sub>\<alpha> P' t\<^sub>\<alpha>'"
      by (metis Act\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff valid_Tree.simps(4) valid_Tree\<^sub>\<alpha>.abs_eq)
  next
    assume "\<exists>\<alpha>' t\<^sub>\<alpha>' P'. Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha> = Act\<^sub>\<alpha> \<alpha>' t\<^sub>\<alpha>' \<and> P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> valid_Tree\<^sub>\<alpha> P' t\<^sub>\<alpha>'"
    moreover have "\<And>\<alpha>' t\<^sub>\<alpha>'. Act\<^sub>\<alpha> \<alpha>' t\<^sub>\<alpha>' = abs_Tree\<^sub>\<alpha> (tAct \<alpha>' (rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>'))"
      by (metis Act\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>_abs_rep)
    ultimately show "valid_Tree\<^sub>\<alpha> P (Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>)"
      by (metis Tree\<^sub>\<alpha>.abs_eq_iff valid_Tree.simps(4) valid_Tree\<^sub>\<alpha>.abs_eq valid_Tree\<^sub>\<alpha>.rep_eq)
  qed


  subsection \<open>Validity for infinitary formulas\<close>

  lift_definition valid :: "'state \<Rightarrow> ('idx,'pred,'act) formula \<Rightarrow> bool" (infix "\<Turnstile>" 70) is
    valid_Tree\<^sub>\<alpha>
  .

  lemma valid_eqvt (*[eqvt]*):
    assumes "P \<Turnstile> x" shows "(p \<bullet> P) \<Turnstile> (p \<bullet> x)"
  using assms by transfer (metis valid_Tree\<^sub>\<alpha>_eqvt)

  lemma valid_Conj [simp]:
    assumes "finite (supp xset)"
    shows "P \<Turnstile> Conj xset \<longleftrightarrow> (\<forall>x\<in>set_bset xset. P \<Turnstile> x)"
  using assms by (simp add: valid_def Conj_def map_bset.rep_eq)

  lemma valid_Not [simp]: "P \<Turnstile> Not x \<longleftrightarrow> \<not> P \<Turnstile> x"
  by transfer simp

  lemma valid_Pred [simp]: "P \<Turnstile> Pred \<phi> \<longleftrightarrow> P \<turnstile> \<phi>"
  by transfer simp

  lemma valid_Act: "P \<Turnstile> Act \<alpha> x \<longleftrightarrow> (\<exists>\<alpha>' x' P'. Act \<alpha> x = Act \<alpha>' x' \<and> P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> P' \<Turnstile> x')"
  proof
    assume "P \<Turnstile> Act \<alpha> x"
    moreover have "Rep_formula (Abs_formula (Act\<^sub>\<alpha> \<alpha> (Rep_formula x))) = Act\<^sub>\<alpha> \<alpha> (Rep_formula x)"
      by (metis Act.rep_eq Rep_formula_inverse)
    ultimately show "\<exists>\<alpha>' x' P'. Act \<alpha> x = Act \<alpha>' x' \<and> P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> P' \<Turnstile> x'"
      by (auto simp add: valid_def Act_def) (metis Abs_formula_inverse Rep_formula' hereditarily_fs_alpha_renaming)
  next
    assume "\<exists>\<alpha>' x' P'. Act \<alpha> x = Act \<alpha>' x' \<and> P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> P' \<Turnstile> x'"
    then show "P \<Turnstile> Act \<alpha> x"
      by (metis Act.rep_eq valid.rep_eq valid_Tree\<^sub>\<alpha>_Act\<^sub>\<alpha>)
  qed

  text \<open>The binding names in the alpha-variant that witnesses validity may be chosen fresh for any
  finitely supported context.\<close>

  lemma valid_Act_strong:
    assumes "finite (supp X)"
    shows "P \<Turnstile> Act \<alpha> x \<longleftrightarrow> (\<exists>\<alpha>' x' P'. Act \<alpha> x = Act \<alpha>' x' \<and> P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> P' \<Turnstile> x' \<and> bn \<alpha>' \<sharp>* X)"
  proof
    assume "P \<Turnstile> Act \<alpha> x"
    then obtain \<alpha>' x' P' where eq: "Act \<alpha> x = Act \<alpha>' x'" and trans: "P \<rightarrow> \<langle>\<alpha>',P'\<rangle>" and valid: "P' \<Turnstile> x'"
      by (metis valid_Act)
    have "finite (bn \<alpha>')"
      by (fact bn_finite)
    moreover note \<open>finite (supp X)\<close>
    moreover have "finite (supp (Act \<alpha>' x', \<langle>\<alpha>',P'\<rangle>))"
      by (metis finite_Diff finite_UnI finite_supp supp_Pair supp_abs_residual_pair)
    moreover have "bn \<alpha>' \<sharp>* (Act \<alpha>' x', \<langle>\<alpha>',P'\<rangle>)"
      by (auto simp add: fresh_star_def fresh_def supp_Pair supp_abs_residual_pair)
    ultimately obtain p where fresh_X: "(p \<bullet> bn \<alpha>') \<sharp>* X" and "supp (Act \<alpha>' x', \<langle>\<alpha>',P'\<rangle>) \<sharp>* p"
      by (metis at_set_avoiding2)
    then have "supp (Act \<alpha>' x') \<sharp>* p" and "supp \<langle>\<alpha>',P'\<rangle> \<sharp>* p"
      by (metis fresh_star_Un supp_Pair)+
    then have "Act (p \<bullet> \<alpha>') (p \<bullet> x') = Act \<alpha>' x'" and "\<langle>p \<bullet> \<alpha>', p \<bullet> P'\<rangle> = \<langle>\<alpha>',P'\<rangle>"
      by (metis Act_eqvt supp_perm_eq, metis abs_residual_pair_eqvt supp_perm_eq)
    then show "\<exists>\<alpha>' x' P'. Act \<alpha> x = Act \<alpha>' x' \<and> P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> P' \<Turnstile> x' \<and> bn \<alpha>' \<sharp>* X"
      using eq and trans and valid and fresh_X by (metis bn_eqvt valid_eqvt)
  next
    assume "\<exists>\<alpha>' x' P'. Act \<alpha> x = Act \<alpha>' x' \<and> P \<rightarrow> \<langle>\<alpha>',P'\<rangle> \<and> P' \<Turnstile> x' \<and> bn \<alpha>' \<sharp>* X"
    then show "P \<Turnstile> Act \<alpha> x"
      by (metis valid_Act)
  qed

  lemma valid_Act_fresh:
    assumes "bn \<alpha> \<sharp>* P"
    shows "P \<Turnstile> Act \<alpha> x \<longleftrightarrow> (\<exists>P'. P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<and> P' \<Turnstile> x)"
  proof
    assume "P \<Turnstile> Act \<alpha> x"

    moreover have "finite (supp P)"
      by (fact finite_supp)
    ultimately obtain \<alpha>' x' P' where
      eq: "Act \<alpha> x = Act \<alpha>' x'" and trans: "P \<rightarrow> \<langle>\<alpha>',P'\<rangle>" and valid: "P' \<Turnstile> x'" and fresh: "bn \<alpha>' \<sharp>* P"
      by (metis valid_Act_strong)

    from eq obtain p where p_\<alpha>: "\<alpha>' = p \<bullet> \<alpha>" and p_x: "x' = p \<bullet> x" and supp_p: "supp p \<subseteq> bn \<alpha> \<union> p \<bullet> bn \<alpha>"
      by (metis Act_eq_iff_perm_renaming)

    from assms and fresh have "(bn \<alpha> \<union> p \<bullet> bn \<alpha>) \<sharp>* P"
      using p_\<alpha> by (metis bn_eqvt fresh_star_Un)
    then have "supp p \<sharp>* P"
      using supp_p by (metis fresh_star_def subset_eq)
    then have p_P: "-p \<bullet> P = P"
      by (metis perm_supp_eq supp_minus_perm)

    from trans have "P \<rightarrow> \<langle>\<alpha>,-p \<bullet> P'\<rangle>"
      using p_P p_\<alpha> by (metis permute_minus_cancel(1) transition_eqvt')
    moreover from valid have "-p \<bullet> P' \<Turnstile> x"
      using p_x by (metis permute_minus_cancel(1) valid_eqvt)
    ultimately show "\<exists>P'. P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<and> P' \<Turnstile> x"
      by meson
  next
    assume "\<exists>P'. P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<and> P' \<Turnstile> x" then show "P \<Turnstile> Act \<alpha> x"
      by (metis valid_Act)
  qed

end

end
