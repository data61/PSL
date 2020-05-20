theory Formula
imports
  Nominal_Bounded_Set
  Nominal_Wellfounded
  Residual
begin

section \<open>Infinitary Formulas\<close>

subsection \<open>Infinitely branching trees\<close>

text \<open>First, we define a type of trees, with a constructor~@{term tConj} that maps (potentially
infinite) sets of trees into trees. To avoid paradoxes (note that there is no injection from the
powerset of trees into the set of trees), the cardinality of the argument set must be bounded.\<close>

datatype ('idx,'pred,'act) Tree =
    tConj "('idx,'pred,'act) Tree set['idx]"  \<comment> \<open>potentially infinite sets of trees\<close>
  | tNot "('idx,'pred,'act) Tree"
  | tPred 'pred
  | tAct 'act "('idx,'pred,'act) Tree"

text \<open>The (automatically generated) induction principle for trees allows us to prove that the
following relation over trees is well-founded. This will be useful for termination proofs when we
define functions by recursion over trees.\<close>

inductive_set Tree_wf :: "('idx,'pred,'act) Tree rel" where
  "t \<in> set_bset tset \<Longrightarrow> (t, tConj tset) \<in> Tree_wf"
| "(t, tNot t) \<in> Tree_wf"
| "(t, tAct \<alpha> t) \<in> Tree_wf"

lemma wf_Tree_wf: "wf Tree_wf"
unfolding wf_def
proof (rule allI, rule impI, rule allI)
  fix P :: "('idx,'pred,'act) Tree \<Rightarrow> bool" and t
  assume "\<forall>x. (\<forall>y. (y, x) \<in> Tree_wf \<longrightarrow> P y) \<longrightarrow> P x"
  then show "P t"
    proof (induction t)
      case tConj then show ?case
        by (metis Tree.distinct(2) Tree.distinct(5) Tree.inject(1) Tree_wf.cases)
    next
      case tNot then show ?case
        by (metis Tree.distinct(1) Tree.distinct(9) Tree.inject(2) Tree_wf.cases)
    next
      case tPred then show ?case
        by (metis Tree.distinct(11) Tree.distinct(3) Tree.distinct(7) Tree_wf.cases)
    next
      case tAct then show ?case
        by (metis Tree.distinct(10) Tree.distinct(6) Tree.inject(4) Tree_wf.cases)
    qed
qed

text \<open>We define a permutation operation on the type of trees.\<close>

instantiation Tree :: (type, pt, pt) pt
begin

  primrec permute_Tree :: "perm \<Rightarrow> (_,_,_) Tree \<Rightarrow> (_,_,_) Tree" where
    "p \<bullet> (tConj tset) = tConj (map_bset (permute p) tset)"  \<comment> \<open>neat trick to get around the fact that~@{term tset} is not of permutation type yet\<close>
  | "p \<bullet> (tNot t) = tNot (p \<bullet> t)"
  | "p \<bullet> (tPred \<phi>) = tPred (p \<bullet> \<phi>)"
  | "p \<bullet> (tAct \<alpha> t) = tAct (p \<bullet> \<alpha>) (p \<bullet> t)"

  instance
  proof
    fix t :: "(_,_,_) Tree"
    show "0 \<bullet> t = t"
    proof (induction t)
      case tConj then show ?case
        by (simp, transfer) (auto simp: image_def)
    qed simp_all
  next
    fix p q :: perm and t :: "(_,_,_) Tree"
    show "(p + q) \<bullet> t = p \<bullet> q \<bullet> t"
      proof (induction t)
        case tConj then show ?case
          by (simp, transfer) (auto simp: image_def)
      qed simp_all
  qed

end

text \<open>Now that the type of trees---and hence the type of (bounded) sets of trees---is a permutation
type, we can massage the definition of~@{term "p \<bullet> tConj tset"} into its more usual form.\<close>

lemma permute_Tree_tConj [simp]: "p \<bullet> tConj tset = tConj (p \<bullet> tset)"
by (simp add: map_bset_permute)

declare permute_Tree.simps(1) [simp del]

text \<open>The relation~@{const Tree_wf} is equivariant.\<close>

lemma Tree_wf_eqvt_aux:
  assumes "(t1, t2) \<in> Tree_wf" shows "(p \<bullet> t1, p \<bullet> t2) \<in> Tree_wf"
using assms proof (induction rule: Tree_wf.induct)
  fix t :: "('a,'b,'c) Tree" and tset :: "('a,'b,'c) Tree set['a]"
  assume "t \<in> set_bset tset" then show "(p \<bullet> t, p \<bullet> tConj tset) \<in> Tree_wf"
    by (metis Tree_wf.intros(1) mem_permute_iff permute_Tree_tConj set_bset_eqvt)
next
  fix t :: "('a,'b,'c) Tree"
  show "(p \<bullet> t, p \<bullet> tNot t) \<in> Tree_wf"
    by (metis Tree_wf.intros(2) permute_Tree.simps(2))
next
  fix t :: "('a,'b,'c) Tree" and \<alpha>
  show "(p \<bullet> t, p \<bullet> tAct \<alpha> t) \<in> Tree_wf"
    by (metis Tree_wf.intros(3) permute_Tree.simps(4))
qed

lemma Tree_wf_eqvt [eqvt, simp]: "p \<bullet> Tree_wf = Tree_wf"
proof
  show "p \<bullet> Tree_wf \<subseteq> Tree_wf"
    by (auto simp add: permute_set_def) (rule Tree_wf_eqvt_aux)
next
  show "Tree_wf \<subseteq> p \<bullet> Tree_wf"
    by (auto simp add: permute_set_def) (metis Tree_wf_eqvt_aux permute_minus_cancel(1))
qed

lemma Tree_wf_eqvt': "eqvt Tree_wf"
by (metis Tree_wf_eqvt eqvtI)

text \<open>The definition of~@{const permute} for trees gives rise to the usual notion of support. The
following lemmas, one for each constructor, describe the support of trees.\<close>

lemma supp_tConj [simp]: "supp (tConj tset) = supp tset"
unfolding supp_def by simp

lemma supp_tNot [simp]: "supp (tNot t) = supp t"
unfolding supp_def by simp

lemma supp_tPred [simp]: "supp (tPred \<phi>) = supp \<phi>"
unfolding supp_def by simp

lemma supp_tAct [simp]: "supp (tAct \<alpha> t) = supp \<alpha> \<union> supp t"
unfolding supp_def by (simp add: Collect_imp_eq Collect_neg_eq)


subsection \<open>Trees modulo \texorpdfstring{$\alpha$}{alpha}-equivalence\<close>

text \<open>We generalize the notion of support, which considers whether a permuted element is
\emph{equal} to itself, to arbitrary endorelations. This is available as @{const supp_rel} in
Nominal Isabelle.\<close>

lemma supp_rel_eqvt [eqvt]:
  "p \<bullet> supp_rel R x = supp_rel (p \<bullet> R) (p \<bullet> x)"
by (simp add: supp_rel_def)

text \<open>Usually, the definition of $\alpha$-equivalence presupposes a notion of free variables.
However, the variables that are ``free'' in an infinitary conjunction are not necessarily those
that are free in one of the conjuncts. For instance, consider a conjunction over \emph{all} names.
Applying any permutation will yield the same conjunction, i.e., this conjunction has \emph{no} free
variables.

To obtain the correct notion of free variables for infinitary conjunctions, we initially defined
$\alpha$-equivalence and free variables via mutual recursion. In particular, we defined the free
variables of a conjunction as term @{term "fv_Tree (tConj tset) = supp_rel alpha_Tree (tConj tset)"}.

We then realized that it is not necessary to define the concept of ``free variables'' at all, but
the definition of $\alpha$-equivalence becomes much simpler (in particular, it is no longer mutually
recursive) if we directly use the support modulo $\alpha$-equivalence.\<close>

text \<open>The following lemmas and constructions are used to prove termination of our definition.\<close>

lemma supp_rel_cong [fundef_cong]:
  "\<lbrakk> x=x'; \<And>a b. R ((a \<rightleftharpoons> b) \<bullet> x') x' \<longleftrightarrow> R' ((a \<rightleftharpoons> b) \<bullet> x') x' \<rbrakk> \<Longrightarrow> supp_rel R x = supp_rel R' x'"
by (simp add: supp_rel_def)

lemma rel_bset_cong [fundef_cong]:
  "\<lbrakk> x=x'; y=y'; \<And>a b. a \<in> set_bset x' \<Longrightarrow> b \<in> set_bset y' \<Longrightarrow> R a b \<longleftrightarrow> R' a b \<rbrakk> \<Longrightarrow> rel_bset R x y \<longleftrightarrow> rel_bset R' x' y'"
by (simp add: rel_bset_def rel_set_def)

lemma alpha_set_cong [fundef_cong]:
  "\<lbrakk> bs=bs'; x=x'; R (p' \<bullet> x') y' \<longleftrightarrow> R' (p' \<bullet> x') y'; f x' = f' x'; f y' = f' y'; p=p'; cs=cs'; y=y' \<rbrakk> \<Longrightarrow>
    alpha_set (bs, x) R f p (cs, y) \<longleftrightarrow> alpha_set (bs', x') R' f' p' (cs', y')"
by (simp add: alpha_set)

quotient_type
  ('idx,'pred,'act) Tree\<^sub>p = "('idx,'pred::pt,'act::bn) Tree" / "hull_relp"
  by (fact hull_relp_equivp)

lemma abs_Tree\<^sub>p_eq [simp]: "abs_Tree\<^sub>p (p \<bullet> t) = abs_Tree\<^sub>p t"
by (metis hull_relp.simps Tree\<^sub>p.abs_eq_iff)

lemma permute_rep_abs_Tree\<^sub>p:
  obtains p where "rep_Tree\<^sub>p (abs_Tree\<^sub>p t) = p \<bullet> t"
by (metis Quotient3_Tree\<^sub>p Tree\<^sub>p.abs_eq_iff rep_abs_rsp hull_relp.simps)

lift_definition Tree_wf\<^sub>p :: "('idx,'pred::pt,'act::bn) Tree\<^sub>p rel" is
  Tree_wf .

lemma Tree_wf\<^sub>pI [simp]:
  assumes "(a, b) \<in> Tree_wf"
  shows "(abs_Tree\<^sub>p (p \<bullet> a), abs_Tree\<^sub>p b) \<in> Tree_wf\<^sub>p"
using assms by (metis (erased, lifting) Tree\<^sub>p.abs_eq_iff Tree_wf\<^sub>p.abs_eq hull_relp.intros map_prod_simp rev_image_eqI)

lemma Tree_wf\<^sub>p_trivialI [simp]:
  assumes "(a, b) \<in> Tree_wf"
  shows "(abs_Tree\<^sub>p a, abs_Tree\<^sub>p b) \<in> Tree_wf\<^sub>p"
using assms by (metis Tree_wf\<^sub>pI permute_zero)

lemma Tree_wf\<^sub>pE:
  assumes "(a\<^sub>p, b\<^sub>p) \<in> Tree_wf\<^sub>p"
  obtains a b where "a\<^sub>p = abs_Tree\<^sub>p a" and "b\<^sub>p = abs_Tree\<^sub>p b" and "(a,b) \<in> Tree_wf"
using assms by (metis Pair_inject Tree_wf\<^sub>p.abs_eq prod_fun_imageE)

lemma wf_Tree_wf\<^sub>p: "wf Tree_wf\<^sub>p"
proof (rule wf_subset[of "inv_image (hull_rel O Tree_wf) rep_Tree\<^sub>p"])
  show "wf (inv_image (hull_rel O Tree_wf) rep_Tree\<^sub>p)"
    by (metis Tree_wf_eqvt' wf_Tree_wf wf_hull_rel_relcomp wf_inv_image)
next
  show "Tree_wf\<^sub>p \<subseteq> inv_image (hull_rel O Tree_wf) rep_Tree\<^sub>p"
  proof (standard, case_tac "x", clarify)
    fix a\<^sub>p b\<^sub>p :: "('d, 'e, 'f) Tree\<^sub>p"
    assume "(a\<^sub>p, b\<^sub>p) \<in> Tree_wf\<^sub>p"
    then obtain a b where 1: "a\<^sub>p = abs_Tree\<^sub>p a" and 2: "b\<^sub>p = abs_Tree\<^sub>p b" and 3: "(a,b) \<in> Tree_wf"
      by (rule Tree_wf\<^sub>pE)
    from 1 obtain p where 4: "rep_Tree\<^sub>p a\<^sub>p = p \<bullet> a"
      by (metis permute_rep_abs_Tree\<^sub>p)
    from 2 obtain q where 5: "rep_Tree\<^sub>p b\<^sub>p = q \<bullet> b"
      by (metis permute_rep_abs_Tree\<^sub>p)
    have "(p \<bullet> a, q \<bullet> a) \<in> hull_rel"
      by (metis hull_rel.simps permute_minus_cancel(2) permute_plus)
    moreover from 3 have "(q \<bullet> a, q \<bullet> b) \<in> Tree_wf"
      by (rule Tree_wf_eqvt_aux)
    ultimately show "(a\<^sub>p, b\<^sub>p) \<in> inv_image (hull_rel O Tree_wf) rep_Tree\<^sub>p"
      using 4 5 by auto
  qed
qed

fun alpha_Tree_termination :: "('a, 'b, 'c) Tree \<times> ('a, 'b, 'c) Tree \<Rightarrow> ('a, 'b::pt, 'c::bn) Tree\<^sub>p set" where
  "alpha_Tree_termination (t1, t2) = {abs_Tree\<^sub>p t1, abs_Tree\<^sub>p t2}"

text \<open>Here it comes \ldots\<close>

function (sequential)
  alpha_Tree :: "('idx,'pred::pt,'act::bn) Tree \<Rightarrow> ('idx,'pred,'act) Tree \<Rightarrow> bool" (infix "=\<^sub>\<alpha>" 50) where
\<comment> \<open>@{const alpha_Tree}\<close>
  alpha_tConj: "tConj tset1 =\<^sub>\<alpha> tConj tset2 \<longleftrightarrow> rel_bset alpha_Tree tset1 tset2"
| alpha_tNot: "tNot t1 =\<^sub>\<alpha> tNot t2 \<longleftrightarrow> t1 =\<^sub>\<alpha> t2"
| alpha_tPred: "tPred \<phi>1 =\<^sub>\<alpha> tPred \<phi>2 \<longleftrightarrow> \<phi>1 = \<phi>2"
\<comment> \<open>the action may have binding names\<close>
| alpha_tAct: "tAct \<alpha>1 t1 =\<^sub>\<alpha> tAct \<alpha>2 t2 \<longleftrightarrow>
    (\<exists>p. (bn \<alpha>1, t1) \<approx>set alpha_Tree (supp_rel alpha_Tree) p (bn \<alpha>2, t2) \<and> (bn \<alpha>1, \<alpha>1) \<approx>set ((=)) supp p (bn \<alpha>2, \<alpha>2))"
| alpha_other: "_ =\<^sub>\<alpha> _ \<longleftrightarrow> False"
\<comment> \<open>254 subgoals (!)\<close>
by pat_completeness auto
termination
proof
  let ?R = "inv_image (max_ext Tree_wf\<^sub>p) alpha_Tree_termination"
  show "wf ?R"
    by (metis max_ext_wf wf_Tree_wf\<^sub>p wf_inv_image)
qed (auto simp add: max_ext.simps Tree_wf.simps simp del: permute_Tree_tConj)

text \<open>We provide more descriptive case names for the automatically generated induction principle.\<close>

lemmas alpha_Tree_induct' = alpha_Tree.induct[case_names alpha_tConj alpha_tNot
  alpha_tPred alpha_tAct "alpha_other(1)" "alpha_other(2)" "alpha_other(3)" "alpha_other(4)"
  "alpha_other(5)" "alpha_other(6)" "alpha_other(7)" "alpha_other(8)" "alpha_other(9)"
  "alpha_other(10)" "alpha_other(11)" "alpha_other(12)" "alpha_other(13)" "alpha_other(14)"
  "alpha_other(15)" "alpha_other(16)" "alpha_other(17)" "alpha_other(18)"]

lemma alpha_Tree_induct[case_names tConj tNot tPred tAct, consumes 1]:
  assumes "t1 =\<^sub>\<alpha> t2"
  and "\<And>tset1 tset2. (\<And>a b. a \<in> set_bset tset1 \<Longrightarrow> b \<in> set_bset tset2 \<Longrightarrow> a =\<^sub>\<alpha> b \<Longrightarrow> P a b) \<Longrightarrow>
            rel_bset (=\<^sub>\<alpha>) tset1 tset2 \<Longrightarrow> P (tConj tset1) (tConj tset2)"
  and "\<And>t1 t2. t1 =\<^sub>\<alpha> t2 \<Longrightarrow> P t1 t2 \<Longrightarrow> P (tNot t1) (tNot t2)"
  and "\<And>\<phi>. P (tPred \<phi>) (tPred \<phi>)"
  and "\<And>\<alpha>1 t1 \<alpha>2 t2. (\<And>p. p \<bullet> t1 =\<^sub>\<alpha> t2 \<Longrightarrow> P (p \<bullet> t1) t2) \<Longrightarrow>
            (\<And>a b. ((a \<rightleftharpoons> b) \<bullet> t1) =\<^sub>\<alpha> t1 \<Longrightarrow> P ((a \<rightleftharpoons> b) \<bullet> t1) t1) \<Longrightarrow> (\<And>a b. ((a \<rightleftharpoons> b) \<bullet> t2) =\<^sub>\<alpha> t2 \<Longrightarrow> P ((a \<rightleftharpoons> b) \<bullet> t2) t2) \<Longrightarrow>
            (\<exists>p. (bn \<alpha>1, t1) \<approx>set (=\<^sub>\<alpha>) (supp_rel (=\<^sub>\<alpha>)) p (bn \<alpha>2, t2) \<and> (bn \<alpha>1, \<alpha>1) \<approx>set (=) supp p (bn \<alpha>2, \<alpha>2)) \<Longrightarrow>
            P (tAct \<alpha>1 t1) (tAct \<alpha>2 t2)"
  shows "P t1 t2"
using assms by (induction t1 t2 rule: alpha_Tree.induct) simp_all

text \<open>$\alpha$-equivalence is equivariant.\<close>

lemma alpha_Tree_eqvt_aux:
  assumes "\<And>a b. (a \<rightleftharpoons> b) \<bullet> t =\<^sub>\<alpha> t \<longleftrightarrow> p \<bullet> (a \<rightleftharpoons> b) \<bullet> t =\<^sub>\<alpha> p \<bullet> t"
  shows "p \<bullet> supp_rel (=\<^sub>\<alpha>) t = supp_rel (=\<^sub>\<alpha>) (p \<bullet> t)"
proof -
  {
    fix a
    let ?B = "{b. \<not> ((a \<rightleftharpoons> b) \<bullet> t) =\<^sub>\<alpha> t}"
    let ?pB = "{b. \<not> ((p \<bullet> a \<rightleftharpoons> b) \<bullet> p \<bullet> t) =\<^sub>\<alpha> (p \<bullet> t)}"
    {
      assume "finite ?B"
      moreover have "inj_on (unpermute p) ?pB"
        by (simp add: inj_on_def unpermute_def)
      moreover have "unpermute p ` ?pB \<subseteq> ?B"
        using assms by auto (metis (erased, lifting) eqvt_bound permute_eqvt swap_eqvt)
      ultimately have "finite ?pB"
        by (metis inj_on_finite)
    }
    moreover
    {
      assume "finite ?pB"
      moreover have "inj_on (permute p) ?B"
        by (simp add: inj_on_def)
      moreover have "permute p ` ?B \<subseteq> ?pB"
        using assms by auto (metis (erased, lifting) permute_eqvt swap_eqvt)
      ultimately have "finite ?B"
        by (metis inj_on_finite)
    }
    ultimately have "infinite ?B \<longleftrightarrow> infinite ?pB"
      by auto
  }
  then show ?thesis
    by (auto simp add: supp_rel_def permute_set_def) (metis eqvt_bound)
qed

lemma alpha_Tree_eqvt': "t1 =\<^sub>\<alpha> t2 \<longleftrightarrow> p \<bullet> t1 =\<^sub>\<alpha> p \<bullet> t2"
proof (induction t1 t2 rule: alpha_Tree_induct')
  case (alpha_tConj tset1 tset2) show ?case
  proof
    assume *: "tConj tset1 =\<^sub>\<alpha> tConj tset2"
    {
      fix x
      assume "x \<in> set_bset (p \<bullet> tset1)"
      then obtain x' where 1: "x' \<in> set_bset tset1" and 2: "x = p \<bullet> x'"
        by (metis imageE permute_bset.rep_eq permute_set_eq_image)
      from 1 obtain y' where 3: "y' \<in> set_bset tset2" and 4: "x' =\<^sub>\<alpha> y'"
        using "*" by (metis (mono_tags, lifting) Formula.alpha_tConj rel_bset.rep_eq rel_set_def)
      from 3 have "p \<bullet> y' \<in> set_bset (p \<bullet> tset2)"
        by (metis mem_permute_iff set_bset_eqvt)
      moreover from 1 and 2 and 3 and 4 have "x =\<^sub>\<alpha> p \<bullet> y'"
        using alpha_tConj.IH by blast
      ultimately have "\<exists>y\<in>set_bset (p \<bullet> tset2). x =\<^sub>\<alpha> y" ..
    }
    moreover
    {
      fix y
      assume "y \<in> set_bset (p \<bullet> tset2)"
      then obtain y' where 1: "y' \<in> set_bset tset2" and 2: "p \<bullet> y' = y"
        by (metis imageE permute_bset.rep_eq permute_set_eq_image)
      from 1 obtain x' where 3: "x' \<in> set_bset tset1" and 4: "x' =\<^sub>\<alpha> y'"
        using "*" by (metis (mono_tags, lifting) Formula.alpha_tConj rel_bset.rep_eq rel_set_def)
      from 3 have "p \<bullet> x' \<in> set_bset (p \<bullet> tset1)"
        by (metis mem_permute_iff set_bset_eqvt)
      moreover from 1 and 2 and 3 and 4 have "p \<bullet> x' =\<^sub>\<alpha> y"
        using alpha_tConj.IH by blast
      ultimately have "\<exists>x\<in>set_bset (p \<bullet> tset1). x =\<^sub>\<alpha> y" ..
    }
    ultimately show "p \<bullet> tConj tset1 =\<^sub>\<alpha> p \<bullet> tConj tset2"
      by (simp add: rel_bset_def rel_set_def)
  next
    assume *: "p \<bullet> tConj tset1 =\<^sub>\<alpha> p \<bullet> tConj tset2"
    {
      fix x
      assume 1: "x \<in> set_bset tset1"
      then have "p \<bullet> x \<in> set_bset (p \<bullet> tset1)"
        by (metis mem_permute_iff set_bset_eqvt)
      then obtain y' where 2: "y' \<in> set_bset (p \<bullet> tset2)" and 3: "p \<bullet> x =\<^sub>\<alpha> y'"
        using "*" by (metis Formula.alpha_tConj permute_Tree_tConj rel_bset.rep_eq rel_set_def)
      from 2 obtain y where 4: "y \<in> set_bset tset2" and 5: "y' = p \<bullet> y"
        by (metis imageE permute_bset.rep_eq permute_set_eq_image)
      from 1 and 3 and 4 and 5 have "x =\<^sub>\<alpha> y"
        using alpha_tConj.IH by blast
      with 4 have "\<exists>y\<in>set_bset tset2. x =\<^sub>\<alpha> y" ..
    }
    moreover
    {
      fix y
      assume 1: "y \<in> set_bset tset2"
      then have "p \<bullet> y \<in> set_bset (p \<bullet> tset2)"
        by (metis mem_permute_iff set_bset_eqvt)
      then obtain x' where 2: "x' \<in> set_bset (p \<bullet> tset1)" and 3: "x' =\<^sub>\<alpha> p \<bullet> y"
        using "*" by (metis Formula.alpha_tConj permute_Tree_tConj rel_bset.rep_eq rel_set_def)
      from 2 obtain x where 4: "x \<in> set_bset tset1" and 5: "p \<bullet> x = x'"
        by (metis imageE permute_bset.rep_eq permute_set_eq_image)
      from 1 and 3 and 4 and 5 have "x =\<^sub>\<alpha> y"
        using alpha_tConj.IH by blast
      with 4 have "\<exists>x\<in>set_bset tset1. x =\<^sub>\<alpha> y" ..
    }
    ultimately show "tConj tset1 =\<^sub>\<alpha> tConj tset2"
      by (simp add: rel_bset_def rel_set_def)
  qed
next
  case (alpha_tAct \<alpha>1 t1 \<alpha>2 t2)
  from alpha_tAct.IH(2) have t1: "p \<bullet> supp_rel (=\<^sub>\<alpha>) t1 = supp_rel (=\<^sub>\<alpha>) (p \<bullet> t1)"
    by (rule alpha_Tree_eqvt_aux)
  from alpha_tAct.IH(3) have t2: "p \<bullet> supp_rel (=\<^sub>\<alpha>) t2 = supp_rel (=\<^sub>\<alpha>) (p \<bullet> t2)"
    by (rule alpha_Tree_eqvt_aux)
  show ?case
  proof
    assume "tAct \<alpha>1 t1 =\<^sub>\<alpha> tAct \<alpha>2 t2"
    then obtain q where 1: "(bn \<alpha>1, t1) \<approx>set (=\<^sub>\<alpha>) (supp_rel (=\<^sub>\<alpha>)) q (bn \<alpha>2, t2)" and 2: "(bn \<alpha>1, \<alpha>1) \<approx>set (=) supp q (bn \<alpha>2, \<alpha>2)"
      by auto
    from 1 and t1 and t2 have "supp_rel (=\<^sub>\<alpha>) (p \<bullet> t1) - bn (p \<bullet> \<alpha>1) = supp_rel (=\<^sub>\<alpha>) (p \<bullet> t2) - bn (p \<bullet> \<alpha>2)"
      by (metis Diff_eqvt alpha_set bn_eqvt)
    moreover from 1 and t1 have "(supp_rel (=\<^sub>\<alpha>) (p \<bullet> t1) - bn (p \<bullet> \<alpha>1)) \<sharp>* (p + q - p)"
      by (metis Diff_eqvt alpha_set bn_eqvt fresh_star_permute_iff permute_perm_def)
    moreover from 1 and alpha_tAct.IH(1) have "p \<bullet> q \<bullet> t1 =\<^sub>\<alpha> p \<bullet> t2"
      by (simp add: alpha_set)
    moreover from 2 have "p \<bullet> q \<bullet> -p \<bullet> bn (p \<bullet> \<alpha>1) = bn (p \<bullet> \<alpha>2)"
      by (simp add: alpha_set bn_eqvt)
    ultimately have "(bn (p \<bullet> \<alpha>1), p \<bullet> t1) \<approx>set (=\<^sub>\<alpha>) (supp_rel (=\<^sub>\<alpha>)) (p + q - p) (bn (p \<bullet> \<alpha>2), p \<bullet> t2)"
      by (simp add: alpha_set)
    moreover from 2 have "(bn (p \<bullet> \<alpha>1), p \<bullet> \<alpha>1) \<approx>set (=) supp (p + q - p) (bn (p \<bullet> \<alpha>2), p \<bullet> \<alpha>2)"
      by (simp add: alpha_set) (metis (mono_tags, lifting) Diff_eqvt bn_eqvt fresh_star_permute_iff permute_minus_cancel(2) permute_perm_def supp_eqvt)
    ultimately show "p \<bullet> tAct \<alpha>1 t1 =\<^sub>\<alpha> p \<bullet> tAct \<alpha>2 t2"
      by auto
  next
    assume "p \<bullet> tAct \<alpha>1 t1 =\<^sub>\<alpha> p \<bullet> tAct \<alpha>2 t2"
    then obtain q where 1: "(bn (p \<bullet> \<alpha>1), p \<bullet> t1) \<approx>set (=\<^sub>\<alpha>) (supp_rel (=\<^sub>\<alpha>)) q (bn (p \<bullet> \<alpha>2), p \<bullet> t2)" and 2: "(bn (p \<bullet> \<alpha>1), p \<bullet> \<alpha>1) \<approx>set (=) supp q (bn (p \<bullet> \<alpha>2), p \<bullet> \<alpha>2)"
      by auto
    {
      from 1 and t1 and t2 have "supp_rel (=\<^sub>\<alpha>) t1 - bn \<alpha>1 = supp_rel (=\<^sub>\<alpha>) t2 - bn \<alpha>2"
        by (metis (no_types, lifting) Diff_eqvt alpha_set bn_eqvt permute_eq_iff)
      moreover with 1 and t2 have "(supp_rel (=\<^sub>\<alpha>) t1 - bn \<alpha>1) \<sharp>* (- p + q + p)"
        by (auto simp add: fresh_star_def fresh_perm alphas) (metis (no_types, lifting) DiffI bn_eqvt mem_permute_iff permute_minus_cancel(2))
      moreover from 1 have "- p \<bullet> q \<bullet> p \<bullet> t1 =\<^sub>\<alpha> t2"
        using alpha_tAct.IH(1) by (simp add: alpha_set) (metis (no_types, lifting) permute_eqvt permute_minus_cancel(2))
      moreover from 1 have "- p \<bullet> q \<bullet> p \<bullet> bn \<alpha>1 = bn \<alpha>2"
        by (metis alpha_set bn_eqvt permute_minus_cancel(2))
      ultimately have "(bn \<alpha>1, t1) \<approx>set (=\<^sub>\<alpha>) (supp_rel (=\<^sub>\<alpha>)) (-p + q + p) (bn \<alpha>2, t2)"
        by (simp add: alpha_set)
    }
    moreover
    {
      from 2 have "supp \<alpha>1 - bn \<alpha>1 = supp \<alpha>2 - bn \<alpha>2"
        by (metis (no_types, lifting) Diff_eqvt alpha_set bn_eqvt permute_eq_iff supp_eqvt)
      moreover with 2 have "(supp \<alpha>1 - bn \<alpha>1) \<sharp>* (-p + q + p)"
        by (auto simp add: fresh_star_def fresh_perm alphas) (metis (no_types, lifting) DiffI bn_eqvt mem_permute_iff permute_minus_cancel(1) supp_eqvt)
      moreover from 2 have "-p \<bullet> q \<bullet> p \<bullet> \<alpha>1 = \<alpha>2"
        by (simp add: alpha_set)
      moreover have "-p \<bullet> q \<bullet> p \<bullet> bn \<alpha>1 = bn \<alpha>2"
        by (simp add: bn_eqvt calculation(3))
      ultimately have "(bn \<alpha>1, \<alpha>1) \<approx>set (=) supp (-p + q + p) (bn \<alpha>2, \<alpha>2)"
        by (simp add: alpha_set)
    }
    ultimately show "tAct \<alpha>1 t1 =\<^sub>\<alpha> tAct \<alpha>2 t2"
      by auto
  qed
qed simp_all

lemma alpha_Tree_eqvt [eqvt]: "t1 =\<^sub>\<alpha> t2 \<Longrightarrow> p \<bullet> t1 =\<^sub>\<alpha> p \<bullet> t2"
by (metis alpha_Tree_eqvt')

text \<open>@{const alpha_Tree} is an equivalence relation.\<close>

lemma alpha_Tree_reflp: "reflp alpha_Tree"
proof (rule reflpI)
  fix t :: "('a,'b,'c) Tree"
  show "t =\<^sub>\<alpha> t"
  proof (induction t)
    case tConj then show ?case by (metis alpha_tConj rel_bset.rep_eq rel_setI)
  next
    case tNot then show ?case by (metis alpha_tNot)
  next
    case tPred show ?case by (metis alpha_tPred)
  next
    case tAct then show ?case by (metis (mono_tags) alpha_tAct alpha_refl(1))
  qed
qed

lemma alpha_Tree_symp: "symp alpha_Tree"
proof (rule sympI)
  fix x y :: "('a,'b,'c) Tree"
  assume "x =\<^sub>\<alpha> y" then show "y =\<^sub>\<alpha> x"
  proof (induction x y rule: alpha_Tree_induct)
    case tConj then show ?case
      by (simp add: rel_bset_def rel_set_def) metis
  next
    case (tAct \<alpha>1 t1 \<alpha>2 t2)
    then obtain p where "(bn \<alpha>1, t1) \<approx>set (=\<^sub>\<alpha>) (supp_rel (=\<^sub>\<alpha>)) p (bn \<alpha>2, t2) \<and> (bn \<alpha>1, \<alpha>1) \<approx>set (=) supp p (bn \<alpha>2, \<alpha>2)"
      by auto
    then have "(bn \<alpha>2, t2) \<approx>set (=\<^sub>\<alpha>) (supp_rel (=\<^sub>\<alpha>)) (-p) (bn \<alpha>1, t1) \<and> (bn \<alpha>2, \<alpha>2) \<approx>set (=) supp (-p) (bn \<alpha>1, \<alpha>1)"
      using tAct.IH by (metis (mono_tags, lifting) alpha_Tree_eqvt alpha_sym(1) permute_minus_cancel(2))
    then show ?case
      by auto
  qed simp_all
qed

lemma alpha_Tree_transp: "transp alpha_Tree"
proof (rule transpI)
  fix x y z:: "('a,'b,'c) Tree"
  assume "x =\<^sub>\<alpha> y" and "y =\<^sub>\<alpha> z"
  then show "x =\<^sub>\<alpha> z"
  proof (induction x y arbitrary: z rule: alpha_Tree_induct)
    case (tConj tset_x tset_y) show ?case
      proof (cases z)
        fix tset_z
        assume z: "z = tConj tset_z"
        have "rel_bset (=\<^sub>\<alpha>) tset_x tset_z"
          unfolding rel_bset.rep_eq rel_set_def Ball_def Bex_def
          proof
            show "\<forall>x'. x' \<in> set_bset tset_x \<longrightarrow> (\<exists>z'. z' \<in> set_bset tset_z \<and> x' =\<^sub>\<alpha> z')"
            proof (rule allI, rule impI)
              fix x' assume 1: "x' \<in> set_bset tset_x"
              then obtain y' where 2: "y' \<in> set_bset tset_y" and 3: "x' =\<^sub>\<alpha> y'"
                by (metis rel_bset.rep_eq rel_set_def tConj.hyps)
              from 2 obtain z' where 4: "z' \<in> set_bset tset_z" and 5: "y' =\<^sub>\<alpha> z'"
                by (metis alpha_tConj rel_bset.rep_eq rel_set_def tConj.prems z)
              from 1 2 3 5 have "x' =\<^sub>\<alpha> z'"
                by (rule tConj.IH)
              with 4 show "\<exists>z'. z' \<in> set_bset tset_z \<and> x' =\<^sub>\<alpha> z'"
                by auto
            qed
          next
            show "\<forall>z'. z' \<in> set_bset tset_z \<longrightarrow> (\<exists>x'. x' \<in> set_bset tset_x \<and> x' =\<^sub>\<alpha> z')"
            proof (rule allI, rule impI)
              fix z' assume 1: "z' \<in> set_bset tset_z"
              then obtain y' where 2: "y' \<in> set_bset tset_y" and 3: "y' =\<^sub>\<alpha> z'"
                by (metis alpha_tConj rel_bset.rep_eq rel_set_def tConj.prems z)
              from 2 obtain x' where 4: "x' \<in> set_bset tset_x" and 5: "x' =\<^sub>\<alpha> y'"
                by (metis rel_bset.rep_eq rel_set_def tConj.hyps)
              from 4 2 5 3 have "x' =\<^sub>\<alpha> z'"
                by (rule tConj.IH)
              with 4 show "\<exists>x'. x' \<in> set_bset tset_x \<and> x' =\<^sub>\<alpha> z'"
                by auto
            qed
          qed
        with z show "tConj tset_x =\<^sub>\<alpha> z"
          by simp
      qed (insert tConj.prems, auto)
  next
    case tNot then show ?case
      by (cases z) simp_all
  next
    case tPred then show ?case
      by simp
  next
    case (tAct \<alpha>1 t1 \<alpha>2 t2) show ?case
    proof (cases z)
      fix \<alpha> t
      assume z: "z = tAct \<alpha> t"
      obtain p where 1: "(bn \<alpha>1, t1) \<approx>set (=\<^sub>\<alpha>) (supp_rel (=\<^sub>\<alpha>)) p (bn \<alpha>2, t2) \<and> (bn \<alpha>1, \<alpha>1) \<approx>set (=) supp p (bn \<alpha>2, \<alpha>2)"
        using tAct.hyps by auto
      obtain q where 2: "(bn \<alpha>2, t2) \<approx>set (=\<^sub>\<alpha>) (supp_rel (=\<^sub>\<alpha>)) q (bn \<alpha>, t) \<and> (bn \<alpha>2, \<alpha>2) \<approx>set (=) supp q (bn \<alpha>, \<alpha>)"
        using tAct.prems z by auto
      have "(bn \<alpha>1, t1) \<approx>set (=\<^sub>\<alpha>) (supp_rel (=\<^sub>\<alpha>)) (q + p) (bn \<alpha>, t)"
        proof -
          have "supp_rel (=\<^sub>\<alpha>) t1 - bn \<alpha>1 = supp_rel (=\<^sub>\<alpha>) t - bn \<alpha>"
            using 1 and 2 by (metis alpha_set)
          moreover have "(supp_rel (=\<^sub>\<alpha>) t1 - bn \<alpha>1) \<sharp>* (q + p)"
            using 1 and 2 by (metis alpha_set fresh_star_plus)
          moreover have "(q + p) \<bullet> t1 =\<^sub>\<alpha> t"
            using 1 and 2 and tAct.IH by (metis (no_types, lifting) alpha_Tree_eqvt alpha_set permute_minus_cancel(1) permute_plus)
          moreover have "(q + p) \<bullet> bn \<alpha>1 = bn \<alpha>"
            using 1 and 2 by (metis alpha_set permute_plus)
          ultimately show ?thesis
            by (metis alpha_set)
        qed
      moreover have "(bn \<alpha>1, \<alpha>1) \<approx>set (=) supp (q + p) (bn \<alpha>, \<alpha>)"
        using 1 and 2 by (metis (mono_tags) alpha_trans(1) permute_plus)
      ultimately show "tAct \<alpha>1 t1 =\<^sub>\<alpha> z"
        using z by auto
    qed (insert tAct.prems, auto)
  qed
qed

lemma alpha_Tree_equivp: "equivp alpha_Tree"
by (auto intro: equivpI alpha_Tree_reflp alpha_Tree_symp alpha_Tree_transp)

text \<open>$alpha$-equivalent trees have the same support modulo $alpha$-equivalence.\<close>

lemma alpha_Tree_supp_rel:
  assumes "t1 =\<^sub>\<alpha> t2"
  shows "supp_rel (=\<^sub>\<alpha>) t1 = supp_rel (=\<^sub>\<alpha>) t2"
using assms proof (induction rule: alpha_Tree_induct)
  case (tConj tset1 tset2)
  have sym: "\<And>x y. rel_bset (=\<^sub>\<alpha>) x y \<longleftrightarrow> rel_bset (=\<^sub>\<alpha>) y x"
    by (meson alpha_Tree_symp bset.rel_symp sympE)
  {
    fix a b
    from tConj.hyps have *: "rel_bset (=\<^sub>\<alpha>) ((a \<rightleftharpoons> b) \<bullet> tset1) ((a \<rightleftharpoons> b) \<bullet> tset2)"
      by (metis alpha_tConj alpha_Tree_eqvt permute_Tree_tConj)
    have "rel_bset (=\<^sub>\<alpha>) ((a \<rightleftharpoons> b) \<bullet> tset1) tset1 \<longleftrightarrow> rel_bset (=\<^sub>\<alpha>) ((a \<rightleftharpoons> b) \<bullet> tset2) tset2"
      by (rule iffI) (metis "*" alpha_Tree_transp bset.rel_transp sym tConj.hyps transpE)+
  }
  then show ?case
    by (simp add: supp_rel_def)
next
  case tNot then show ?case
    by (simp add: supp_rel_def)
next
  case (tAct \<alpha>1 t1 \<alpha>2 t2)
  {
    fix a b
    have "tAct \<alpha>1 t1 =\<^sub>\<alpha> tAct \<alpha>2 t2"
      using tAct.hyps by simp
    then have "(a \<rightleftharpoons> b) \<bullet> tAct \<alpha>1 t1 =\<^sub>\<alpha> tAct \<alpha>1 t1 \<longleftrightarrow> (a \<rightleftharpoons> b) \<bullet> tAct \<alpha>2 t2 =\<^sub>\<alpha> tAct \<alpha>2 t2"
      by (metis (no_types, lifting) alpha_Tree_eqvt alpha_Tree_symp alpha_Tree_transp sympE transpE)
  }
  then show ?case
    by (simp add: supp_rel_def)
qed simp_all

text \<open>@{const tAct} preserves $\alpha$-equivalence.\<close>

lemma alpha_Tree_tAct:
  assumes "t1 =\<^sub>\<alpha> t2"
  shows "tAct \<alpha> t1 =\<^sub>\<alpha> tAct \<alpha> t2"
proof -
  have "(bn \<alpha>, t1) \<approx>set (=\<^sub>\<alpha>) (supp_rel (=\<^sub>\<alpha>)) 0 (bn \<alpha>, t2)"
    using assms by (simp add: alpha_Tree_supp_rel alpha_set fresh_star_zero)
  moreover have "(bn \<alpha>, \<alpha>) \<approx>set (=) supp 0 (bn \<alpha>, \<alpha>)"
    by (metis (full_types) alpha_refl(1))
  ultimately show ?thesis
    by auto
qed

text \<open>The following lemmas describe the support modulo $alpha$-equivalence.\<close>

lemma supp_rel_tNot [simp]: "supp_rel (=\<^sub>\<alpha>) (tNot t) = supp_rel (=\<^sub>\<alpha>) t"
unfolding supp_rel_def by simp

lemma supp_rel_tPred [simp]: "supp_rel (=\<^sub>\<alpha>) (tPred \<phi>) = supp \<phi>"
unfolding supp_rel_def supp_def by simp

text \<open>The support modulo $\alpha$-equivalence of~@{term "tAct \<alpha> t"} is not easily described:
when~@{term t} has infinite support (modulo $\alpha$-equivalence), the support (modulo
$\alpha$-equivalence) of~@{term "tAct \<alpha> t"} may still contain names in~@{term "bn \<alpha>"}. This
incongruity is avoided when~@{term t} has finite support modulo $\alpha$-equivalence.\<close>

lemma infinite_mono: "infinite S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> x \<in> T) \<Longrightarrow> infinite T"
by (metis infinite_super subsetI)

lemma supp_rel_tAct [simp]:
  assumes "finite (supp_rel (=\<^sub>\<alpha>) t)"
  shows "supp_rel (=\<^sub>\<alpha>) (tAct \<alpha> t) = supp \<alpha> \<union> supp_rel (=\<^sub>\<alpha>) t - bn \<alpha>"
proof
  show "supp \<alpha> \<union> supp_rel (=\<^sub>\<alpha>) t - bn \<alpha> \<subseteq> supp_rel (=\<^sub>\<alpha>) (tAct \<alpha> t)"
  proof
    fix x
    assume "x \<in> supp \<alpha> \<union> supp_rel (=\<^sub>\<alpha>) t - bn \<alpha>"
    moreover
    {
      assume x1: "x \<in> supp \<alpha>" and x2: "x \<notin> bn \<alpha>"
      from x1 have "infinite {b. (x \<rightleftharpoons> b) \<bullet> \<alpha> \<noteq> \<alpha>}"
        unfolding supp_def ..
      then have "infinite ({b. (x \<rightleftharpoons> b) \<bullet> \<alpha> \<noteq> \<alpha>} - supp \<alpha>)"
        by (simp add: finite_supp)
      moreover
      {
        fix b
        assume "b \<in> {b. (x \<rightleftharpoons> b) \<bullet> \<alpha> \<noteq> \<alpha>} - supp \<alpha>"
        then have b1: "(x \<rightleftharpoons> b) \<bullet> \<alpha> \<noteq> \<alpha>" and b2: "b \<notin> supp \<alpha> - bn \<alpha>"
          by simp+
        from b1 have "sort_of x = sort_of b"
          using swap_different_sorts by fastforce
        then have "(x \<rightleftharpoons> b) \<bullet> (supp \<alpha> - bn \<alpha>) \<noteq> supp \<alpha> - bn \<alpha>"
          using b2 x1 x2 by (simp add: swap_set_in)
        then have "b \<in> {b. \<not> (x \<rightleftharpoons> b) \<bullet> tAct \<alpha> t =\<^sub>\<alpha> tAct \<alpha> t}"
          by (auto simp add: alpha_set Diff_eqvt bn_eqvt)
      }
      ultimately have "infinite {b. \<not> (x \<rightleftharpoons> b) \<bullet> tAct \<alpha> t =\<^sub>\<alpha> tAct \<alpha> t}"
        by (rule infinite_mono)
      then have "x \<in> supp_rel (=\<^sub>\<alpha>) (tAct \<alpha> t)"
        unfolding supp_rel_def ..
    }
    moreover
    {
      assume x1: "x \<in> supp_rel (=\<^sub>\<alpha>) t" and x2: "x \<notin> bn \<alpha>"
      from x1 have "infinite {b. \<not> (x \<rightleftharpoons> b) \<bullet> t =\<^sub>\<alpha> t}"
        unfolding supp_rel_def ..
      then have "infinite ({b. \<not> (x \<rightleftharpoons> b) \<bullet> t =\<^sub>\<alpha> t} - supp_rel (=\<^sub>\<alpha>) t)"
        using assms by simp
      moreover
      {
        fix b
        assume "b \<in> {b. \<not> (x \<rightleftharpoons> b) \<bullet> t =\<^sub>\<alpha> t} - supp_rel (=\<^sub>\<alpha>) t"
        then have b1: "\<not> (x \<rightleftharpoons> b) \<bullet> t =\<^sub>\<alpha> t" and b2: "b \<notin> supp_rel (=\<^sub>\<alpha>) t - bn \<alpha>"
          by simp+
        from b1 have "(x \<rightleftharpoons> b) \<bullet> t \<noteq> t"
          by (metis alpha_Tree_reflp reflpE)
        then have "sort_of x = sort_of b"
          using swap_different_sorts by fastforce
        then have "(x \<rightleftharpoons> b) \<bullet> (supp_rel (=\<^sub>\<alpha>) t - bn \<alpha>) \<noteq> supp_rel (=\<^sub>\<alpha>) t - bn \<alpha>"
          using b2 x1 x2 by (simp add: swap_set_in)
        then have "supp_rel (=\<^sub>\<alpha>) ((x \<rightleftharpoons> b) \<bullet> t) - bn ((x \<rightleftharpoons> b) \<bullet> \<alpha>) \<noteq> supp_rel (=\<^sub>\<alpha>) t - bn \<alpha>"
          by (simp add: Diff_eqvt bn_eqvt)
        then have "b \<in> {b. \<not> (x \<rightleftharpoons> b) \<bullet> tAct \<alpha> t =\<^sub>\<alpha> tAct \<alpha> t}"
          by (simp add: alpha_set)
      }
      ultimately have "infinite {b. \<not> (x \<rightleftharpoons> b) \<bullet> tAct \<alpha> t =\<^sub>\<alpha> tAct \<alpha> t}"
        by (rule infinite_mono)
      then have "x \<in> supp_rel (=\<^sub>\<alpha>) (tAct \<alpha> t)"
        unfolding supp_rel_def ..
    }
    ultimately show "x \<in> supp_rel (=\<^sub>\<alpha>) (tAct \<alpha> t)"
      by auto
  qed
next
  show "supp_rel (=\<^sub>\<alpha>) (tAct \<alpha> t) \<subseteq> supp \<alpha> \<union> supp_rel (=\<^sub>\<alpha>) t - bn \<alpha>"
  proof
    fix x
    assume "x \<in> supp_rel (=\<^sub>\<alpha>) (tAct \<alpha> t)"
    then have *: "infinite {b. \<not> (x \<rightleftharpoons> b) \<bullet> tAct \<alpha> t =\<^sub>\<alpha> tAct \<alpha> t}"
      unfolding supp_rel_def ..
    moreover
    {
      fix b
      assume "\<not> (x \<rightleftharpoons> b) \<bullet> tAct \<alpha> t =\<^sub>\<alpha> tAct \<alpha> t"
      then have "(x \<rightleftharpoons> b) \<bullet> \<alpha> \<noteq> \<alpha> \<or> \<not> (x \<rightleftharpoons> b) \<bullet> t =\<^sub>\<alpha> t"
        using alpha_Tree_tAct by force
    }
    ultimately have "infinite {b. (x \<rightleftharpoons> b) \<bullet> \<alpha> \<noteq> \<alpha> \<or> \<not> (x \<rightleftharpoons> b) \<bullet> t =\<^sub>\<alpha> t}"
      by (metis (mono_tags, lifting) infinite_mono mem_Collect_eq)
    then have "infinite {b. (x \<rightleftharpoons> b) \<bullet> \<alpha> \<noteq> \<alpha>} \<or> infinite {b. \<not> (x \<rightleftharpoons> b) \<bullet> t =\<^sub>\<alpha> t}"
      by (metis (mono_tags) finite_Collect_disjI)
    then have "x \<in> supp \<alpha> \<union> supp_rel (=\<^sub>\<alpha>) t"
      by (simp add: supp_def supp_rel_def)
    moreover
    {
      assume **: "x \<in> bn \<alpha>"
      from "*" obtain b where b1: "\<not> (x \<rightleftharpoons> b) \<bullet> tAct \<alpha> t =\<^sub>\<alpha> tAct \<alpha> t" and b2: "b \<notin> supp \<alpha>" and b3: "b \<notin> supp_rel (=\<^sub>\<alpha>) t"
        using assms by (metis (no_types, lifting) UnCI finite_UnI finite_supp infinite_mono mem_Collect_eq)
      let ?p = "(x \<rightleftharpoons> b)"
      have "supp_rel (=\<^sub>\<alpha>) ((x \<rightleftharpoons> b) \<bullet> t) - bn ((x \<rightleftharpoons> b) \<bullet> \<alpha>) = supp_rel (=\<^sub>\<alpha>) t - bn \<alpha>"
        using "**" and b3 by (metis (no_types, lifting) Diff_eqvt Diff_iff alpha_Tree_eqvt' alpha_Tree_eqvt_aux bn_eqvt swap_set_not_in)
      moreover then have "(supp_rel (=\<^sub>\<alpha>) ((x \<rightleftharpoons> b) \<bullet> t) - bn ((x \<rightleftharpoons> b) \<bullet> \<alpha>)) \<sharp>* ?p"
        using "**" and b3 by (metis Diff_iff fresh_perm fresh_star_def swap_atom_simps(3))
      moreover have "?p \<bullet> (x \<rightleftharpoons> b) \<bullet> t =\<^sub>\<alpha> t"
        using alpha_Tree_reflp reflpE by force
      moreover have "?p \<bullet> bn ((x \<rightleftharpoons> b) \<bullet> \<alpha>) = bn \<alpha>"
        by (simp add: bn_eqvt)
      moreover have "supp ((x \<rightleftharpoons> b) \<bullet> \<alpha>) - bn ((x \<rightleftharpoons> b) \<bullet> \<alpha>) = supp \<alpha> - bn \<alpha>"
        using "**" and b2 by (metis (mono_tags, hide_lams) Diff_eqvt Diff_iff bn_eqvt supp_eqvt swap_set_not_in)
      moreover then have "(supp ((x \<rightleftharpoons> b) \<bullet> \<alpha>) - bn ((x \<rightleftharpoons> b) \<bullet> \<alpha>)) \<sharp>* ?p"
        using "**" and b2 by (simp add: fresh_star_def fresh_def supp_perm) (metis Diff_iff swap_atom_simps(3))
      moreover have "?p \<bullet> (x \<rightleftharpoons> b) \<bullet> \<alpha> = \<alpha>"
        by simp
      ultimately have "(x \<rightleftharpoons> b) \<bullet> tAct \<alpha> t =\<^sub>\<alpha> tAct \<alpha> t"
        by (auto simp add: alpha_set)
      with b1 have "False" ..
    }
    ultimately show "x \<in> supp \<alpha> \<union> supp_rel (=\<^sub>\<alpha>) t - bn \<alpha>"
      by blast
  qed
qed

text \<open>We define the type of (infinitely branching) trees quotiented by $\alpha$-equivalence.\<close>

(* FIXME: No map function defined. No relator found. *)
quotient_type
  ('idx,'pred,'act) Tree\<^sub>\<alpha> = "('idx,'pred::pt,'act::bn) Tree" / "alpha_Tree"
  by (fact alpha_Tree_equivp)

lemma Tree\<^sub>\<alpha>_abs_rep [simp]: "abs_Tree\<^sub>\<alpha> (rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>) = t\<^sub>\<alpha>"
by (metis Quotient_Tree\<^sub>\<alpha> Quotient_abs_rep)

lemma Tree\<^sub>\<alpha>_rep_abs [simp]: "rep_Tree\<^sub>\<alpha> (abs_Tree\<^sub>\<alpha> t) =\<^sub>\<alpha> t"
by (metis Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep)

text \<open>The permutation operation is lifted from trees.\<close>

instantiation Tree\<^sub>\<alpha> :: (type, pt, bn) pt
begin

  lift_definition permute_Tree\<^sub>\<alpha> :: "perm \<Rightarrow> ('a,'b,'c) Tree\<^sub>\<alpha> \<Rightarrow> ('a,'b,'c) Tree\<^sub>\<alpha>"
    is permute
  by (fact alpha_Tree_eqvt)

  instance
  proof
    fix t\<^sub>\<alpha> :: "(_,_,_) Tree\<^sub>\<alpha>"
    show "0 \<bullet> t\<^sub>\<alpha> = t\<^sub>\<alpha>"
      by transfer (metis alpha_Tree_equivp equivp_reflp permute_zero)
  next
    fix p q :: perm and t\<^sub>\<alpha> :: "(_,_,_) Tree\<^sub>\<alpha>"
    show "(p + q) \<bullet> t\<^sub>\<alpha> = p \<bullet> q \<bullet> t\<^sub>\<alpha>"
      by transfer (metis alpha_Tree_equivp equivp_reflp permute_plus)
  qed

end

text \<open>The abstraction function from trees to trees modulo $\alpha$-equivalence is equivariant. The
representation function is equivariant modulo $\alpha$-equivalence.\<close>

lemmas permute_Tree\<^sub>\<alpha>.abs_eq [eqvt, simp]

lemma alpha_Tree_permute_rep_commute [simp]: "p \<bullet> rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha> =\<^sub>\<alpha> rep_Tree\<^sub>\<alpha> (p \<bullet> t\<^sub>\<alpha>)"
by (metis Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep permute_Tree\<^sub>\<alpha>.abs_eq)


subsection \<open>Constructors for trees modulo \texorpdfstring{$\alpha$}{alpha}-equivalence\<close>

text \<open>The constructors are lifted from trees.\<close>

lift_definition Conj\<^sub>\<alpha> :: "('idx,'pred,'act) Tree\<^sub>\<alpha> set['idx] \<Rightarrow> ('idx,'pred::pt,'act::bn) Tree\<^sub>\<alpha>" is
  tConj
by simp

lemma map_bset_abs_rep_Tree\<^sub>\<alpha>: "map_bset abs_Tree\<^sub>\<alpha> (map_bset rep_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>) = tset\<^sub>\<alpha>"
by (metis (full_types) Quotient_Tree\<^sub>\<alpha> Quotient_abs_rep bset_lifting.bset_quot_map)

lemma Conj\<^sub>\<alpha>_def': "Conj\<^sub>\<alpha> tset\<^sub>\<alpha> = abs_Tree\<^sub>\<alpha> (tConj (map_bset rep_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>))"
by (metis Conj\<^sub>\<alpha>.abs_eq map_bset_abs_rep_Tree\<^sub>\<alpha>)

lift_definition Not\<^sub>\<alpha> :: "('idx,'pred,'act) Tree\<^sub>\<alpha> \<Rightarrow> ('idx,'pred::pt,'act::bn) Tree\<^sub>\<alpha>" is
  tNot
by simp

lift_definition Pred\<^sub>\<alpha> :: "'pred \<Rightarrow> ('idx,'pred::pt,'act::bn) Tree\<^sub>\<alpha>" is
  tPred
.

lift_definition Act\<^sub>\<alpha> :: "'act \<Rightarrow> ('idx,'pred,'act) Tree\<^sub>\<alpha> \<Rightarrow> ('idx,'pred::pt,'act::bn) Tree\<^sub>\<alpha>" is
  tAct
by (fact alpha_Tree_tAct)

text \<open>The lifted constructors are equivariant.\<close>

lemma Conj\<^sub>\<alpha>_eqvt [eqvt, simp]: "p \<bullet> Conj\<^sub>\<alpha> tset\<^sub>\<alpha> = Conj\<^sub>\<alpha> (p \<bullet> tset\<^sub>\<alpha>)"
proof -
  {
    fix x
    assume "x \<in> set_bset (p \<bullet> map_bset rep_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>)"
    then obtain y where "y \<in> set_bset (map_bset rep_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>)" and "x = p \<bullet> y"
      by (metis imageE permute_bset.rep_eq permute_set_eq_image)
    then obtain t\<^sub>\<alpha> where 1: "t\<^sub>\<alpha> \<in> set_bset tset\<^sub>\<alpha>" and 2: "x = p \<bullet> rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>"
      by (metis imageE map_bset.rep_eq)
    let ?x' = "rep_Tree\<^sub>\<alpha> (p \<bullet> t\<^sub>\<alpha>)"
    from 1 have "p \<bullet> t\<^sub>\<alpha> \<in> set_bset (p \<bullet> tset\<^sub>\<alpha>)"
      by (metis mem_permute_iff permute_bset.rep_eq)
    then have "?x' \<in> set_bset (map_bset rep_Tree\<^sub>\<alpha> (p \<bullet> tset\<^sub>\<alpha>))"
      by (simp add: bset.set_map)
    moreover from 2 have "x =\<^sub>\<alpha> ?x'"
      by (metis alpha_Tree_permute_rep_commute)
    ultimately have "\<exists>x'\<in>set_bset (map_bset rep_Tree\<^sub>\<alpha> (p \<bullet> tset\<^sub>\<alpha>)). x =\<^sub>\<alpha> x'"
      ..
  }
  moreover
  {
    fix y
    assume "y \<in> set_bset (map_bset rep_Tree\<^sub>\<alpha> (p \<bullet> tset\<^sub>\<alpha>))"
    then obtain x where "x \<in> set_bset (p \<bullet> tset\<^sub>\<alpha>)" and "rep_Tree\<^sub>\<alpha> x = y"
      by (metis imageE map_bset.rep_eq)
    then obtain t\<^sub>\<alpha> where 1: "t\<^sub>\<alpha> \<in> set_bset tset\<^sub>\<alpha>" and 2: "rep_Tree\<^sub>\<alpha> (p \<bullet> t\<^sub>\<alpha>) = y"
      by (metis imageE permute_bset.rep_eq permute_set_eq_image)
    let ?y' = "p \<bullet> rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>"
    from 1 have "rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha> \<in> set_bset (map_bset rep_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>)"
      by (simp add: bset.set_map)
    then have "?y' \<in> set_bset (p \<bullet> map_bset rep_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>)"
      by (metis mem_permute_iff permute_bset.rep_eq)
    moreover from 2 have "?y' =\<^sub>\<alpha> y"
      by (metis alpha_Tree_permute_rep_commute)
    ultimately have "\<exists>y'\<in>set_bset (p \<bullet> map_bset rep_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>). y' =\<^sub>\<alpha> y"
      ..
  }
  ultimately show ?thesis
    by (simp add: Conj\<^sub>\<alpha>_def' map_bset_eqvt rel_bset_def rel_set_def Tree\<^sub>\<alpha>.abs_eq_iff)
qed

lemma Not\<^sub>\<alpha>_eqvt [eqvt, simp]: "p \<bullet> Not\<^sub>\<alpha> t\<^sub>\<alpha> = Not\<^sub>\<alpha> (p \<bullet> t\<^sub>\<alpha>)"
by (induct t\<^sub>\<alpha>) (simp add: Not\<^sub>\<alpha>.abs_eq)

lemma Pred\<^sub>\<alpha>_eqvt [eqvt, simp]: "p \<bullet> Pred\<^sub>\<alpha> \<phi> = Pred\<^sub>\<alpha> (p \<bullet> \<phi>)"
by (simp add: Pred\<^sub>\<alpha>.abs_eq)

lemma Act\<^sub>\<alpha>_eqvt [eqvt, simp]: "p \<bullet> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha> = Act\<^sub>\<alpha> (p \<bullet> \<alpha>) (p \<bullet> t\<^sub>\<alpha>)"
by (induct t\<^sub>\<alpha>) (simp add: Act\<^sub>\<alpha>.abs_eq)

text \<open>The lifted constructors are injective (except for~@{const Act\<^sub>\<alpha>}).\<close>

lemma Conj\<^sub>\<alpha>_eq_iff [simp]: "Conj\<^sub>\<alpha> tset1\<^sub>\<alpha> = Conj\<^sub>\<alpha> tset2\<^sub>\<alpha> \<longleftrightarrow> tset1\<^sub>\<alpha> = tset2\<^sub>\<alpha>"
proof
  assume "Conj\<^sub>\<alpha> tset1\<^sub>\<alpha> = Conj\<^sub>\<alpha> tset2\<^sub>\<alpha>"
  then have "tConj (map_bset rep_Tree\<^sub>\<alpha> tset1\<^sub>\<alpha>) =\<^sub>\<alpha> tConj (map_bset rep_Tree\<^sub>\<alpha> tset2\<^sub>\<alpha>)"
    by (metis Conj\<^sub>\<alpha>_def' Tree\<^sub>\<alpha>.abs_eq_iff)
  then have "rel_bset (=\<^sub>\<alpha>) (map_bset rep_Tree\<^sub>\<alpha> tset1\<^sub>\<alpha>) (map_bset rep_Tree\<^sub>\<alpha> tset2\<^sub>\<alpha>)"
    by (auto elim: alpha_Tree.cases)
  then show "tset1\<^sub>\<alpha> = tset2\<^sub>\<alpha>"
    using Quotient_Tree\<^sub>\<alpha> Quotient_rel_abs2 bset_lifting.bset_quot_map map_bset_abs_rep_Tree\<^sub>\<alpha> by fastforce
qed (fact arg_cong)

lemma Not\<^sub>\<alpha>_eq_iff [simp]: "Not\<^sub>\<alpha> t1\<^sub>\<alpha> = Not\<^sub>\<alpha> t2\<^sub>\<alpha> \<longleftrightarrow> t1\<^sub>\<alpha> = t2\<^sub>\<alpha>"
proof
  assume "Not\<^sub>\<alpha> t1\<^sub>\<alpha> = Not\<^sub>\<alpha> t2\<^sub>\<alpha>"
  then have "tNot (rep_Tree\<^sub>\<alpha> t1\<^sub>\<alpha>) =\<^sub>\<alpha> tNot (rep_Tree\<^sub>\<alpha> t2\<^sub>\<alpha>)"
    by (metis Not\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep)
  then have "rep_Tree\<^sub>\<alpha> t1\<^sub>\<alpha> =\<^sub>\<alpha> rep_Tree\<^sub>\<alpha> t2\<^sub>\<alpha>"
    using alpha_Tree.cases by auto
  then show "t1\<^sub>\<alpha> = t2\<^sub>\<alpha>"
    by (metis Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep)
next
  assume "t1\<^sub>\<alpha> = t2\<^sub>\<alpha>" then show "Not\<^sub>\<alpha> t1\<^sub>\<alpha> = Not\<^sub>\<alpha> t2\<^sub>\<alpha>"
    by simp
qed

lemma Pred\<^sub>\<alpha>_eq_iff [simp]: "Pred\<^sub>\<alpha> \<phi>1 = Pred\<^sub>\<alpha> \<phi>2 \<longleftrightarrow> \<phi>1 = \<phi>2"
proof
  assume "Pred\<^sub>\<alpha> \<phi>1 = Pred\<^sub>\<alpha> \<phi>2"
  then have "(tPred \<phi>1 :: ('d, 'b, 'e) Tree) =\<^sub>\<alpha> tPred \<phi>2"  \<comment> \<open>note the unrelated type\<close>
    by (metis Pred\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff)
  then show "\<phi>1 = \<phi>2"
    using alpha_Tree.cases by auto
next
  assume "\<phi>1 = \<phi>2" then show "Pred\<^sub>\<alpha> \<phi>1 = Pred\<^sub>\<alpha> \<phi>2"
    by simp
qed

lemma Act\<^sub>\<alpha>_eq_iff: "Act\<^sub>\<alpha> \<alpha>1 t1 = Act\<^sub>\<alpha> \<alpha>2 t2 \<longleftrightarrow> tAct \<alpha>1 (rep_Tree\<^sub>\<alpha> t1) =\<^sub>\<alpha> tAct \<alpha>2 (rep_Tree\<^sub>\<alpha> t2)"
by (metis Act\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep)

text \<open>The lifted constructors are free (except for~@{const Act\<^sub>\<alpha>}).\<close>

lemma Tree\<^sub>\<alpha>_free [simp]:
  shows "Conj\<^sub>\<alpha> tset\<^sub>\<alpha> \<noteq> Not\<^sub>\<alpha> t\<^sub>\<alpha>"
  and "Conj\<^sub>\<alpha> tset\<^sub>\<alpha> \<noteq> Pred\<^sub>\<alpha> \<phi>"
  and "Conj\<^sub>\<alpha> tset\<^sub>\<alpha> \<noteq> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>"
  and "Not\<^sub>\<alpha> t\<^sub>\<alpha> \<noteq> Pred\<^sub>\<alpha> \<phi>"
  and "Not\<^sub>\<alpha> t1\<^sub>\<alpha> \<noteq> Act\<^sub>\<alpha> \<alpha> t2\<^sub>\<alpha>"
  and "Pred\<^sub>\<alpha> \<phi> \<noteq> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>"
by (simp add: Conj\<^sub>\<alpha>_def' Not\<^sub>\<alpha>_def Pred\<^sub>\<alpha>_def Act\<^sub>\<alpha>_def Tree\<^sub>\<alpha>.abs_eq_iff)+

text \<open>The following lemmas describe the support of constructed trees modulo $\alpha$-equivalence.\<close>

lemma supp_alpha_supp_rel: "supp t\<^sub>\<alpha> = supp_rel (=\<^sub>\<alpha>) (rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>)"
unfolding supp_def supp_rel_def by (metis (mono_tags, lifting) Collect_cong Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep alpha_Tree_permute_rep_commute)

lemma supp_Conj\<^sub>\<alpha> [simp]: "supp (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>) = supp tset\<^sub>\<alpha>"
unfolding supp_def by simp

lemma supp_Not\<^sub>\<alpha> [simp]: "supp (Not\<^sub>\<alpha> t\<^sub>\<alpha>) = supp t\<^sub>\<alpha>"
unfolding supp_def by simp

lemma supp_Pred\<^sub>\<alpha> [simp]: "supp (Pred\<^sub>\<alpha> \<phi>) = supp \<phi>"
unfolding supp_def by simp

lemma supp_Act\<^sub>\<alpha> [simp]:
  assumes "finite (supp t\<^sub>\<alpha>)"
  shows "supp (Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>) = supp \<alpha> \<union> supp t\<^sub>\<alpha> - bn \<alpha>"
using assms by (metis Act\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>_abs_rep Tree\<^sub>\<alpha>_rep_abs alpha_Tree_supp_rel supp_alpha_supp_rel supp_rel_tAct)


subsection \<open>Induction over trees modulo \texorpdfstring{$\alpha$}{alpha}-equivalence\<close>

lemma Tree\<^sub>\<alpha>_induct [case_names Conj\<^sub>\<alpha> Not\<^sub>\<alpha> Pred\<^sub>\<alpha> Act\<^sub>\<alpha> Env\<^sub>\<alpha>, induct type: Tree\<^sub>\<alpha>]:
  fixes t\<^sub>\<alpha>
  assumes "\<And>tset\<^sub>\<alpha>. (\<And>x. x \<in> set_bset tset\<^sub>\<alpha> \<Longrightarrow> P x) \<Longrightarrow> P (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>)"
    and "\<And>t\<^sub>\<alpha>. P t\<^sub>\<alpha> \<Longrightarrow> P (Not\<^sub>\<alpha> t\<^sub>\<alpha>)"
    and "\<And>pred. P (Pred\<^sub>\<alpha> pred)"
    and "\<And>act t\<^sub>\<alpha>. P t\<^sub>\<alpha> \<Longrightarrow> P (Act\<^sub>\<alpha> act t\<^sub>\<alpha>)"
  shows "P t\<^sub>\<alpha>"
proof (rule Tree\<^sub>\<alpha>.abs_induct)
  fix t show "P (abs_Tree\<^sub>\<alpha> t)"
    proof (induction t)
      case (tConj tset)
        let ?tset\<^sub>\<alpha> = "map_bset abs_Tree\<^sub>\<alpha> tset"
        have "abs_Tree\<^sub>\<alpha> (tConj tset) = Conj\<^sub>\<alpha> ?tset\<^sub>\<alpha>"
          by (simp add: Conj\<^sub>\<alpha>.abs_eq)
        then show ?case
          using assms(1) tConj.IH by (metis imageE map_bset.rep_eq)
    next
      case tNot then show ?case
        using assms(2) by (metis Not\<^sub>\<alpha>.abs_eq)
    next
      case tPred show ?case
        using assms(3) by (metis Pred\<^sub>\<alpha>.abs_eq)
    next
      case tAct then show ?case
        using assms(4) by (metis Act\<^sub>\<alpha>.abs_eq)
    qed
qed

text \<open>There is no (obvious) strong induction principle for trees modulo $\alpha$-equivalence: since
their support may be infinite, we may not be able to rename bound variables without also renaming
free variables.\<close>


subsection \<open>Hereditarily finitely supported trees\<close>

text \<open>We cannot obtain the type of infinitary formulas simply as the sub-type of all trees (modulo
$\alpha$-equivalence) that are finitely supported: since an infinite set of trees may be finitely
supported even though its members are not (and thus, would not be formulas), the sub-type of
\emph{all} finitely supported trees does not validate the induction principle that we desire for
formulas.

Instead, we define \emph{hereditarily} finitely supported trees. We require that environments and
state predicates are finitely supported.\<close>

inductive hereditarily_fs :: "('idx,'pred::fs,'act::bn) Tree\<^sub>\<alpha> \<Rightarrow> bool" where
  Conj\<^sub>\<alpha>: "finite (supp tset\<^sub>\<alpha>) \<Longrightarrow> (\<And>t\<^sub>\<alpha>. t\<^sub>\<alpha> \<in> set_bset tset\<^sub>\<alpha> \<Longrightarrow> hereditarily_fs t\<^sub>\<alpha>) \<Longrightarrow> hereditarily_fs (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>)"
| Not\<^sub>\<alpha>: "hereditarily_fs t\<^sub>\<alpha> \<Longrightarrow> hereditarily_fs (Not\<^sub>\<alpha> t\<^sub>\<alpha>)"
| Pred\<^sub>\<alpha>: "hereditarily_fs (Pred\<^sub>\<alpha> \<phi>)"
| Act\<^sub>\<alpha>: "hereditarily_fs t\<^sub>\<alpha> \<Longrightarrow> hereditarily_fs (Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>)"

text \<open>@{const hereditarily_fs} is equivariant.\<close>

lemma hereditarily_fs_eqvt [eqvt]:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "hereditarily_fs (p \<bullet> t\<^sub>\<alpha>)"
using assms proof (induction rule: hereditarily_fs.induct)
  case Conj\<^sub>\<alpha> then show ?case
    by (metis (erased, hide_lams) Conj\<^sub>\<alpha>_eqvt hereditarily_fs.Conj\<^sub>\<alpha> mem_permute_iff permute_finite permute_minus_cancel(1) set_bset_eqvt supp_eqvt)
next
  case Not\<^sub>\<alpha> then show ?case
    by (metis Not\<^sub>\<alpha>_eqvt hereditarily_fs.Not\<^sub>\<alpha>)
next
  case Pred\<^sub>\<alpha> then show ?case
    by (metis Pred\<^sub>\<alpha>_eqvt hereditarily_fs.Pred\<^sub>\<alpha>)
next
  case Act\<^sub>\<alpha> then show ?case
    by (metis Act\<^sub>\<alpha>_eqvt hereditarily_fs.Act\<^sub>\<alpha>)
qed

text \<open>@{const hereditarily_fs} is preserved under $\alpha$-renaming.\<close>

lemma hereditarily_fs_alpha_renaming:
  assumes "Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha> = Act\<^sub>\<alpha> \<alpha>' t\<^sub>\<alpha>'"
  shows "hereditarily_fs t\<^sub>\<alpha> \<longleftrightarrow> hereditarily_fs t\<^sub>\<alpha>'"
proof
  assume "hereditarily_fs t\<^sub>\<alpha>"
  then show "hereditarily_fs t\<^sub>\<alpha>'"
    using assms by (auto simp add: Act\<^sub>\<alpha>_def Tree\<^sub>\<alpha>.abs_eq_iff alphas) (metis Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep hereditarily_fs_eqvt permute_Tree\<^sub>\<alpha>.abs_eq)
next
  assume "hereditarily_fs t\<^sub>\<alpha>'"
  then show "hereditarily_fs t\<^sub>\<alpha>"
    using assms by (auto simp add: Act\<^sub>\<alpha>_def Tree\<^sub>\<alpha>.abs_eq_iff alphas) (metis Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep hereditarily_fs_eqvt permute_Tree\<^sub>\<alpha>.abs_eq permute_minus_cancel(2))
qed

text \<open>Hereditarily finitely supported trees have finite support.\<close>

lemma hereditarily_fs_implies_finite_supp:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "finite (supp t\<^sub>\<alpha>)"
using assms by (induction rule: hereditarily_fs.induct) (simp_all add: finite_supp)


subsection \<open>Infinitary formulas\<close>

text \<open>Now, infinitary formulas are simply the sub-type of hereditarily finitely supported trees.\<close>

typedef ('idx,'pred::fs,'act::bn) formula = "{t\<^sub>\<alpha>::('idx,'pred,'act) Tree\<^sub>\<alpha>. hereditarily_fs t\<^sub>\<alpha>}"
by (metis hereditarily_fs.Pred\<^sub>\<alpha> mem_Collect_eq)

text \<open>We set up Isabelle's lifting infrastructure so that we can lift definitions from the type of
trees modulo $\alpha$-equivalence to the sub-type of formulas.\<close>

(* FIXME: No relator found. *)
setup_lifting type_definition_formula

lemma Abs_formula_inverse [simp]:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "Rep_formula (Abs_formula t\<^sub>\<alpha>) = t\<^sub>\<alpha>"
using assms by (metis Abs_formula_inverse mem_Collect_eq)

lemma Rep_formula' [simp]: "hereditarily_fs (Rep_formula x)"
by (metis Rep_formula mem_Collect_eq)

text \<open>Now we lift the permutation operation.\<close>

instantiation formula :: (type, fs, bn) pt
begin

  lift_definition permute_formula :: "perm \<Rightarrow> ('a,'b,'c) formula \<Rightarrow> ('a,'b,'c) formula"
    is permute
  by (fact hereditarily_fs_eqvt)

  instance
  by standard (transfer, simp)+

end

text \<open>The abstraction and representation functions for formulas are equivariant, and they preserve
support.\<close>

lemma Abs_formula_eqvt [simp]:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "p \<bullet> Abs_formula t\<^sub>\<alpha> = Abs_formula (p \<bullet> t\<^sub>\<alpha>)"
by (metis assms eq_onp_same_args permute_formula.abs_eq)

lemma supp_Abs_formula [simp]:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "supp (Abs_formula t\<^sub>\<alpha>) = supp t\<^sub>\<alpha>"
proof -
  {
    fix p :: perm
    have "p \<bullet> Abs_formula t\<^sub>\<alpha> = Abs_formula (p \<bullet> t\<^sub>\<alpha>)"
      using assms by (metis Abs_formula_eqvt)
    moreover have "hereditarily_fs (p \<bullet> t\<^sub>\<alpha>)"
      using assms by (metis hereditarily_fs_eqvt)
    ultimately have "p \<bullet> Abs_formula t\<^sub>\<alpha> = Abs_formula t\<^sub>\<alpha> \<longleftrightarrow> p \<bullet> t\<^sub>\<alpha> = t\<^sub>\<alpha>"
      using assms by (metis Abs_formula_inverse)
  }
  then show ?thesis unfolding supp_def by simp
qed

lemmas Rep_formula_eqvt [eqvt, simp] = permute_formula.rep_eq[symmetric]

lemma supp_Rep_formula [simp]: "supp (Rep_formula x) = supp x"
by (metis Rep_formula' Rep_formula_inverse supp_Abs_formula)

lemma supp_map_bset_Rep_formula [simp]: "supp (map_bset Rep_formula xset) = supp xset"
proof
  have "eqvt (map_bset Rep_formula)"
    unfolding eqvt_def by (simp add: ext)
  then show "supp (map_bset Rep_formula xset) \<subseteq> supp xset"
    by (fact supp_fun_app_eqvt)
next
  {
    fix a :: atom
    have "inj (map_bset Rep_formula)"
      by (metis bset.inj_map Rep_formula_inject injI)
    then have "\<And>x y. x \<noteq> y \<Longrightarrow> map_bset Rep_formula x \<noteq> map_bset Rep_formula y"
      by (metis inj_eq)
    then have "{b. (a \<rightleftharpoons> b) \<bullet> xset \<noteq> xset} \<subseteq> {b. (a \<rightleftharpoons> b) \<bullet> map_bset Rep_formula xset \<noteq> map_bset Rep_formula xset}" (is "?S \<subseteq> ?T")
      by auto
    then have "infinite ?S \<Longrightarrow> infinite ?T"
      by (metis infinite_super)
  }
  then show "supp xset \<subseteq> supp (map_bset Rep_formula xset)"
    unfolding supp_def by auto
qed

text \<open>Formulas are in fact finitely supported.\<close>

instance formula :: (type, fs, bn) fs
by standard (metis Rep_formula' hereditarily_fs_implies_finite_supp supp_Rep_formula)


subsection \<open>Constructors for infinitary formulas\<close>

text \<open>We lift the constructors for trees (modulo $\alpha$-equivalence) to infinitary formulas.
Since~@{const Conj\<^sub>\<alpha>} does not necessarily yield a (hereditarily) finitely supported tree when
applied to a (potentially infinite) set of (hereditarily) finitely supported trees, we cannot use
Isabelle's {\bf lift\_definition} to define~@{term Conj}. Instead, theorems about terms of the
form~@{term "Conj xset"} will usually carry an assumption that~@{term xset} is finitely supported.\<close>

definition Conj :: "('idx,'pred,'act) formula set['idx] \<Rightarrow> ('idx,'pred::fs,'act::bn) formula" where
  "Conj xset = Abs_formula (Conj\<^sub>\<alpha> (map_bset Rep_formula xset))"

lemma finite_supp_implies_hereditarily_fs_Conj\<^sub>\<alpha> [simp]:
  assumes "finite (supp xset)"
  shows "hereditarily_fs (Conj\<^sub>\<alpha> (map_bset Rep_formula xset))"
proof (rule hereditarily_fs.Conj\<^sub>\<alpha>)
  show "finite (supp (map_bset Rep_formula xset))"
    using assms by (metis supp_map_bset_Rep_formula)
next
  fix t\<^sub>\<alpha> assume "t\<^sub>\<alpha> \<in> set_bset (map_bset Rep_formula xset)"
  then show "hereditarily_fs t\<^sub>\<alpha>"
    by (auto simp add: bset.set_map)
qed

lemma Conj_rep_eq:
  assumes "finite (supp xset)"
  shows "Rep_formula (Conj xset) = Conj\<^sub>\<alpha> (map_bset Rep_formula xset)"
using assms unfolding Conj_def by simp

lift_definition Not :: "('idx,'pred,'act) formula \<Rightarrow> ('idx,'pred::fs,'act::bn) formula" is
  Not\<^sub>\<alpha>
by (fact hereditarily_fs.Not\<^sub>\<alpha>)

lift_definition Pred :: "'pred \<Rightarrow> ('idx,'pred::fs,'act::bn) formula" is
  Pred\<^sub>\<alpha>
by (fact hereditarily_fs.Pred\<^sub>\<alpha>)

lift_definition Act :: "'act \<Rightarrow> ('idx,'pred,'act) formula \<Rightarrow> ('idx,'pred::fs,'act::bn) formula" is
  Act\<^sub>\<alpha>
by (fact hereditarily_fs.Act\<^sub>\<alpha>)

text \<open>The lifted constructors are equivariant (in the case of~@{const Conj}, on finitely supported
arguments).\<close>

lemma Conj_eqvt [simp]:
  assumes "finite (supp xset)"
  shows "p \<bullet> Conj xset = Conj (p \<bullet> xset)"
using assms unfolding Conj_def by simp

lemma Not_eqvt [eqvt, simp]: "p \<bullet> Not x = Not (p \<bullet> x)"
by transfer simp

lemma Pred_eqvt [eqvt, simp]: "p \<bullet> Pred \<phi> = Pred (p \<bullet> \<phi>)"
by transfer simp

lemma Act_eqvt [eqvt, simp]: "p \<bullet> Act \<alpha> x = Act (p \<bullet> \<alpha>) (p \<bullet> x)"
by transfer simp

text \<open>The following lemmas describe the support of constructed formulas.\<close>

lemma supp_Conj [simp]:
  assumes "finite (supp xset)"
  shows "supp (Conj xset) = supp xset"
using assms unfolding Conj_def by simp

lemma supp_Not [simp]: "supp (Not x) = supp x"
by (metis Not.rep_eq supp_Not\<^sub>\<alpha> supp_Rep_formula)

lemma supp_Pred [simp]: "supp (Pred \<phi>) = supp \<phi>"
by (metis Pred.rep_eq supp_Pred\<^sub>\<alpha> supp_Rep_formula)

lemma supp_Act [simp]: "supp (Act \<alpha> x) = supp \<alpha> \<union> supp x - bn \<alpha>"
by (metis Act.rep_eq finite_supp supp_Act\<^sub>\<alpha> supp_Rep_formula)

lemma bn_fresh_Act [simp]: "bn \<alpha> \<sharp>* Act \<alpha> x"
by (simp add: fresh_def fresh_star_def)

text \<open>The lifted constructors are injective (except for @{const Act}).\<close>

lemma Conj_eq_iff [simp]:
  assumes "finite (supp xset1)" and "finite (supp xset2)"
  shows "Conj xset1 = Conj xset2 \<longleftrightarrow> xset1 = xset2"
using assms
by (metis (erased, hide_lams) Conj\<^sub>\<alpha>_eq_iff Conj_rep_eq Rep_formula_inverse injI inj_eq bset.inj_map)

lemma Not_eq_iff [simp]: "Not x1 = Not x2 \<longleftrightarrow> x1 = x2"
by (metis Not.rep_eq Not\<^sub>\<alpha>_eq_iff Rep_formula_inverse)

lemma Pred_eq_iff [simp]: "Pred \<phi>1 = Pred \<phi>2 \<longleftrightarrow> \<phi>1 = \<phi>2"
by (metis Pred.rep_eq Pred\<^sub>\<alpha>_eq_iff)

lemma Act_eq_iff: "Act \<alpha>1 x1 = Act \<alpha>2 x2 \<longleftrightarrow> Act\<^sub>\<alpha> \<alpha>1 (Rep_formula x1) = Act\<^sub>\<alpha> \<alpha>2 (Rep_formula x2)"
by (metis Act.rep_eq Rep_formula_inverse)

text \<open>Helpful lemmas for dealing with equalities involving~@{const Act}.\<close>

lemma Act_eq_iff_perm: "Act \<alpha>1 x1 = Act \<alpha>2 x2 \<longleftrightarrow>
  (\<exists>p. supp x1 - bn \<alpha>1 = supp x2 - bn \<alpha>2 \<and> (supp x1 - bn \<alpha>1) \<sharp>* p \<and> p \<bullet> x1 = x2 \<and> supp \<alpha>1 - bn \<alpha>1 = supp \<alpha>2 - bn \<alpha>2 \<and> (supp \<alpha>1 - bn \<alpha>1) \<sharp>* p \<and> p \<bullet> \<alpha>1 = \<alpha>2)"
  (is "?l \<longleftrightarrow> ?r")
proof
  assume "?l"
  then obtain p where alpha: "(bn \<alpha>1, rep_Tree\<^sub>\<alpha> (Rep_formula x1)) \<approx>set (=\<^sub>\<alpha>) (supp_rel (=\<^sub>\<alpha>)) p (bn \<alpha>2, rep_Tree\<^sub>\<alpha> (Rep_formula x2))" and eq: "(bn \<alpha>1, \<alpha>1) \<approx>set (=) supp p (bn \<alpha>2, \<alpha>2)"
    by (metis Act_eq_iff Act\<^sub>\<alpha>_eq_iff alpha_tAct)
  from alpha have "supp x1 - bn \<alpha>1 = supp x2 - bn \<alpha>2"
    by (metis alpha_set.simps supp_Rep_formula supp_alpha_supp_rel)
  moreover from alpha have "(supp x1 - bn \<alpha>1) \<sharp>* p"
    by (metis alpha_set.simps supp_Rep_formula supp_alpha_supp_rel)
  moreover from alpha have "p \<bullet> x1 = x2"
    by (metis Rep_formula_eqvt Rep_formula_inject Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep alpha_Tree_permute_rep_commute alpha_set.simps)
  moreover from eq have "supp \<alpha>1 - bn \<alpha>1 = supp \<alpha>2 - bn \<alpha>2"
    by (metis alpha_set.simps)
  moreover from eq have "(supp \<alpha>1 - bn \<alpha>1) \<sharp>* p"
    by (metis alpha_set.simps)
  moreover from eq have "p \<bullet> \<alpha>1 = \<alpha>2"
    by (simp add: alpha_set.simps)
  ultimately show "?r"
    by metis
next
  assume "?r"
  then obtain p where 1: "supp x1 - bn \<alpha>1 = supp x2 - bn \<alpha>2" and 2: "(supp x1 - bn \<alpha>1) \<sharp>* p" and 3: "p \<bullet> x1 = x2"
    and 4: "supp \<alpha>1 - bn \<alpha>1 = supp \<alpha>2 - bn \<alpha>2" and 5: "(supp \<alpha>1 - bn \<alpha>1) \<sharp>* p" and 6: "p \<bullet> \<alpha>1 = \<alpha>2"
    by metis
  from 1 2 3 6 have "(bn \<alpha>1, rep_Tree\<^sub>\<alpha> (Rep_formula x1)) \<approx>set (=\<^sub>\<alpha>) (supp_rel (=\<^sub>\<alpha>)) p (bn \<alpha>2, rep_Tree\<^sub>\<alpha> (Rep_formula x2))"
    by (metis (no_types, lifting) Rep_formula_eqvt alpha_Tree_permute_rep_commute alpha_set.simps bn_eqvt supp_Rep_formula supp_alpha_supp_rel)
  moreover from 4 5 6 have "(bn \<alpha>1, \<alpha>1) \<approx>set (=) supp p (bn \<alpha>2, \<alpha>2)"
    by (simp add: alpha_set.simps bn_eqvt)
  ultimately show "Act \<alpha>1 x1 = Act \<alpha>2 x2"
    by (metis Act_eq_iff Act\<^sub>\<alpha>_eq_iff alpha_tAct)
qed

lemma Act_eq_iff_perm_renaming: "Act \<alpha>1 x1 = Act \<alpha>2 x2 \<longleftrightarrow>
  (\<exists>p. supp x1 - bn \<alpha>1 = supp x2 - bn \<alpha>2 \<and> (supp x1 - bn \<alpha>1) \<sharp>* p \<and> p \<bullet> x1 = x2 \<and> supp \<alpha>1 - bn \<alpha>1 = supp \<alpha>2 - bn \<alpha>2 \<and> (supp \<alpha>1 - bn \<alpha>1) \<sharp>* p \<and> p \<bullet> \<alpha>1 = \<alpha>2 \<and> supp p \<subseteq> bn \<alpha>1 \<union> p \<bullet> bn \<alpha>1)"
  (is "?l \<longleftrightarrow> ?r")
proof
  assume "?l"
  then obtain p where p: "supp x1 - bn \<alpha>1 = supp x2 - bn \<alpha>2 \<and> (supp x1 - bn \<alpha>1) \<sharp>* p \<and> p \<bullet> x1 = x2 \<and> supp \<alpha>1 - bn \<alpha>1 = supp \<alpha>2 - bn \<alpha>2 \<and> (supp \<alpha>1 - bn \<alpha>1) \<sharp>* p \<and> p \<bullet> \<alpha>1 = \<alpha>2"
    by (metis Act_eq_iff_perm)
  moreover obtain q where q_p: "\<forall>b\<in>bn \<alpha>1. q \<bullet> b = p \<bullet> b" and supp_q: "supp q \<subseteq> bn \<alpha>1 \<union> p \<bullet> bn \<alpha>1"
    by (metis set_renaming_perm2)
  have "supp q \<subseteq> supp p"
  proof
    fix a assume *: "a \<in> supp q" then show "a \<in> supp p"
    proof (cases "a \<in> bn \<alpha>1")
      case True then show ?thesis
        using "*" q_p by (metis mem_Collect_eq supp_perm)
    next
      case False then have "a \<in> p \<bullet> bn \<alpha>1"
        using "*" supp_q using UnE subsetCE by blast
      with False have "p \<bullet> a \<noteq> a"
        by (metis mem_permute_iff)
      then show ?thesis
        using fresh_def fresh_perm by blast
    qed
  qed
  with p have "(supp x1 - bn \<alpha>1) \<sharp>* q" and "(supp \<alpha>1 - bn \<alpha>1) \<sharp>* q"
    by (meson fresh_def fresh_star_def subset_iff)+
  moreover with p and q_p have "\<And>a. a \<in> supp \<alpha>1 \<Longrightarrow> q \<bullet> a = p \<bullet> a" and "\<And>a. a \<in> supp x1 \<Longrightarrow> q \<bullet> a = p \<bullet> a"
    by (metis Diff_iff fresh_perm fresh_star_def)+
  then have "q \<bullet> \<alpha>1 = p \<bullet> \<alpha>1" and "q \<bullet> x1 = p \<bullet> x1"
    by (metis supp_perm_perm_eq)+
  ultimately show "?r"
    using supp_q by (metis bn_eqvt)
next
  assume "?r" then show "?l"
    by (meson Act_eq_iff_perm)
qed

text \<open>The lifted constructors are free (except for @{const Act}).\<close>

lemma Tree_free [simp]:
  shows "finite (supp xset) \<Longrightarrow> Conj xset \<noteq> Not x"
  and "finite (supp xset) \<Longrightarrow> Conj xset \<noteq> Pred \<phi>"
  and "finite (supp xset) \<Longrightarrow> Conj xset \<noteq> Act \<alpha> x"
  and "Not x \<noteq> Pred \<phi>"
  and "Not x1 \<noteq> Act \<alpha> x2"
  and "Pred \<phi> \<noteq> Act \<alpha> x"
proof -
  show "finite (supp xset) \<Longrightarrow> Conj xset \<noteq> Not x"
    by (metis Conj_rep_eq Not.rep_eq Tree\<^sub>\<alpha>_free(1))
next
  show "finite (supp xset) \<Longrightarrow> Conj xset \<noteq> Pred \<phi>"
    by (metis Conj_rep_eq Pred.rep_eq Tree\<^sub>\<alpha>_free(2))
next
  show "finite (supp xset) \<Longrightarrow> Conj xset \<noteq> Act \<alpha> x"
    by (metis Conj_rep_eq Act.rep_eq Tree\<^sub>\<alpha>_free(3))
next
  show "Not x \<noteq> Pred \<phi>"
    by (metis Not.rep_eq Pred.rep_eq Tree\<^sub>\<alpha>_free(4))
next
  show "Not x1 \<noteq> Act \<alpha> x2"
    by (metis Not.rep_eq Act.rep_eq Tree\<^sub>\<alpha>_free(5))
next
  show "Pred \<phi> \<noteq> Act \<alpha> x"
    by (metis Pred.rep_eq Act.rep_eq Tree\<^sub>\<alpha>_free(6))
qed


subsection \<open>Induction over infinitary formulas\<close>

lemma formula_induct [case_names Conj Not Pred Act, induct type: formula]:
  fixes x
  assumes "\<And>xset. finite (supp xset) \<Longrightarrow> (\<And>x. x \<in> set_bset xset \<Longrightarrow> P x) \<Longrightarrow> P (Conj xset)"
    and "\<And>formula. P formula \<Longrightarrow> P (Not formula)"
    and "\<And>pred. P (Pred pred)"
    and "\<And>act formula. P formula \<Longrightarrow> P (Act act formula)"
  shows "P x"
proof (induction x)
  fix t\<^sub>\<alpha> :: "('a,'b,'c) Tree\<^sub>\<alpha>"
  assume "t\<^sub>\<alpha> \<in> {t\<^sub>\<alpha>. hereditarily_fs t\<^sub>\<alpha>}"
  then have "hereditarily_fs t\<^sub>\<alpha>"
    by simp
  then show "P (Abs_formula t\<^sub>\<alpha>)"
    proof (induction t\<^sub>\<alpha>)
      case (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>) show ?case
        proof -
          let ?tset = "map_bset Abs_formula tset\<^sub>\<alpha>"
          have "\<And>t\<^sub>\<alpha>'. t\<^sub>\<alpha>' \<in> set_bset tset\<^sub>\<alpha> \<Longrightarrow> t\<^sub>\<alpha>' = (Rep_formula \<circ> Abs_formula) t\<^sub>\<alpha>'"
            by (simp add: Conj\<^sub>\<alpha>.hyps)
          then have "tset\<^sub>\<alpha> = map_bset (Rep_formula \<circ> Abs_formula) tset\<^sub>\<alpha>"
            by (metis bset.map_cong0 bset.map_id id_apply)
          then have *: "tset\<^sub>\<alpha> = map_bset Rep_formula ?tset"
            by (metis bset.map_comp)
          then have "Abs_formula (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>) = Conj ?tset"
            by (metis Conj_def)
          moreover from "*" have "finite (supp ?tset)"
            using Conj\<^sub>\<alpha>.hyps(1) by (metis supp_map_bset_Rep_formula)
          moreover have "(\<And>t. t \<in> set_bset ?tset \<Longrightarrow> P t)"
            using Conj\<^sub>\<alpha>.IH by (metis imageE map_bset.rep_eq)
          ultimately show ?thesis
            using assms(1) by metis
        qed
    next
      case Not\<^sub>\<alpha> then show ?case
        using assms(2) by (metis Formula.Abs_formula_inverse Not.rep_eq Rep_formula_inverse)
    next
      case Pred\<^sub>\<alpha> show ?case
        using assms(3) by (metis Pred.abs_eq)
    next
      case Act\<^sub>\<alpha> then show ?case
        using assms(4) by (metis Formula.Abs_formula_inverse Act.rep_eq Rep_formula_inverse)
    qed
qed


subsection \<open>Strong induction over infinitary formulas\<close>

lemma formula_strong_induct_aux:
  fixes x
  assumes "\<And>xset c. finite (supp xset) \<Longrightarrow> (\<And>x. x \<in> set_bset xset \<Longrightarrow> (\<And>c. P c x)) \<Longrightarrow> P c (Conj xset)"
    and "\<And>formula c. (\<And>c. P c formula) \<Longrightarrow> P c (Not formula)"
    and "\<And>pred c. P c (Pred pred)"
    and "\<And>act formula c. bn act \<sharp>* c \<Longrightarrow> (\<And>c. P c formula) \<Longrightarrow> P c (Act act formula)"
  shows "\<And>(c :: 'd::fs) p. P c (p \<bullet> x)"
proof (induction x)
  case (Conj xset)
    moreover then have "finite (supp (p \<bullet> xset))"
      by (metis permute_finite supp_eqvt)
    moreover have "(\<And>x c. x \<in> set_bset (p \<bullet> xset) \<Longrightarrow> P c x)"
      using Conj.IH by (metis (full_types) eqvt_bound mem_permute_iff set_bset_eqvt)
    ultimately show ?case
      using assms(1) by simp
next
  case Not then show ?case
    using assms(2) by simp
next
  case Pred show ?case
    using assms(3) by simp
next
  case (Act \<alpha> x) show ?case
  proof -
    \<comment> \<open>rename~@{term "bn (p \<bullet> \<alpha>)"} to avoid~@{term c}, without touching~@{term "Act (p \<bullet> \<alpha>) (p \<bullet> x)"}\<close>
    obtain q where 1: "(q \<bullet> bn (p \<bullet> \<alpha>)) \<sharp>* c" and 2: "supp (Act (p \<bullet> \<alpha>) (p \<bullet> x)) \<sharp>* q"
      proof (rule at_set_avoiding2[of "bn (p \<bullet> \<alpha>)" c "Act (p \<bullet> \<alpha>) (p \<bullet> x)", THEN exE])
        show "finite (bn (p \<bullet> \<alpha>))" by (fact bn_finite)
      next
        show "finite (supp c)" by (fact finite_supp)
      next
        show "finite (supp (Act (p \<bullet> \<alpha>) (p \<bullet> x)))" by (simp add: finite_supp)
      next
        show "bn (p \<bullet> \<alpha>) \<sharp>* Act (p \<bullet> \<alpha>) (p \<bullet> x)" by (simp add: fresh_def fresh_star_def)
      qed metis
    from 1 have "bn (q \<bullet> p \<bullet> \<alpha>) \<sharp>* c"
      by (simp add: bn_eqvt)
    moreover from Act.IH have "\<And>c. P c (q \<bullet> p \<bullet> x)"
      by (metis permute_plus)
    ultimately have "P c (Act (q \<bullet> p \<bullet> \<alpha>) (q \<bullet> p \<bullet> x))"
      using assms(4) by simp
    moreover from 2 have "Act (q \<bullet> p \<bullet> \<alpha>) (q \<bullet> p \<bullet> x) = Act (p \<bullet> \<alpha>) (p \<bullet> x)"
      using supp_perm_eq by fastforce
    ultimately show ?thesis
      by simp
  qed
qed

lemmas formula_strong_induct = formula_strong_induct_aux[where p=0, simplified]
declare formula_strong_induct [case_names Conj Not Pred Act]

end
