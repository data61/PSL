(*  Author:     Tobias Nipkow, 2007  *)

theory QElin_inf
imports LinArith
begin

subsection \<open>Quantifier elimination with infinitesimals \label{sec:lin-inf}\<close>

text\<open>This section formalizes Loos and Weispfenning's quantifier
elimination procedure based on (the simulation of)
infinitesimals~\cite{LoosW93}.\<close>

fun asubst_peps :: "real * real list \<Rightarrow> atom \<Rightarrow> atom fm" ("asubst\<^sub>+") where
"asubst_peps (r,cs) (Less s (d#ds)) =
  (if d=0 then Atom(Less s ds) else
   let u = s - d*r; v = d *\<^sub>s cs + ds; less = Atom(Less u v)
   in if d<0 then less else Or less (Atom(Eq u v)))" |
"asubst_peps rcs (Eq r (d#ds)) = (if d=0 then Atom(Eq r ds) else FalseF)" |
"asubst_peps rcs a = Atom a"

abbreviation subst_peps :: "atom fm \<Rightarrow> real * real list \<Rightarrow> atom fm" ("subst\<^sub>+")
where "subst\<^sub>+ \<phi> rcs \<equiv> amap\<^sub>f\<^sub>m (asubst\<^sub>+ rcs) \<phi>"

definition "nolb f xs l x = (\<forall>y\<in>{l<..<x}. y \<notin> LB f xs)"

lemma nolb_And[simp]:
  "nolb (And f g) xs l x = (nolb f xs l x \<and> nolb g xs l x)"
apply(clarsimp simp:nolb_def)
apply blast
done

lemma nolb_Or[simp]:
  "nolb (Or f g) xs l x = (nolb f xs l x \<and> nolb g xs l x)"
apply(clarsimp simp:nolb_def)
apply blast
done

context notes [[simp_depth_limit=4]]
begin

lemma innermost_intvl:
  "\<lbrakk> nqfree f; nolb f xs l x; l < x; x \<notin> EQ f xs; R.I f (x#xs); l < y; y \<le> x\<rbrakk>
  \<Longrightarrow> R.I f (y#xs)"
proof(induct f)
  case (Atom a)
  show ?case
  proof (cases a)
    case [simp]: (Less r cs)
    show ?thesis
    proof (cases cs)
      case Nil thus ?thesis using Atom by (simp add:depends\<^sub>R_def)
    next
      case [simp]: (Cons c cs)
      hence "r < c*x + \<langle>cs,xs\<rangle>" using Atom by simp
      { assume "c=0" hence ?thesis using Atom by simp }
      moreover
      { assume "c<0"
        hence "x < (r - \<langle>cs,xs\<rangle>)/c" (is "_ < ?u") using \<open>r < c*x + \<langle>cs,xs\<rangle>\<close>
          by (simp add: field_simps)
        have ?thesis
        proof (rule ccontr)
          assume "\<not> R.I (Atom a) (y#xs)"
          hence "?u \<le> y" using Atom \<open>c<0\<close>
            by (auto simp add: field_simps)
          with \<open>x<?u\<close> show False using Atom \<open>c<0\<close>
            by(auto simp:depends\<^sub>R_def)
        qed } moreover
      { assume "c>0"
        hence "x > (r - \<langle>cs,xs\<rangle>)/c" (is "_ > ?l") using \<open>r < c*x + \<langle>cs,xs\<rangle>\<close>
          by (simp add: field_simps)
        then have "?l < y" using Atom \<open>c>0\<close>
            by (auto simp:depends\<^sub>R_def Ball_def nolb_def)
               (metis linorder_not_le antisym order_less_trans)
        hence ?thesis using \<open>c>0\<close> by (simp add: field_simps)
      } ultimately show ?thesis by force
    qed
  next
    case [simp]: (Eq r cs)
    show ?thesis
    proof (cases cs)
      case Nil thus ?thesis using Atom by (simp add:depends\<^sub>R_def)
    next
      case [simp]: (Cons c cs)
      hence "r = c*x + \<langle>cs,xs\<rangle>" using Atom by simp
      { assume "c=0" hence ?thesis using Atom by simp }
      moreover
      { assume "c\<noteq>0"
        hence ?thesis using \<open>r = c*x + \<langle>cs,xs\<rangle>\<close> Atom
          by(auto simp: ac_simps depends\<^sub>R_def split:if_splits) }
      ultimately show ?thesis by force
    qed
  qed
next
  case (And f1 f2) thus ?case by (fastforce)
next
  case (Or f1 f2) thus ?case by (fastforce)
qed simp+

definition "EQ2 = EQ"

lemma EQ2_Or[simp]: "EQ2 (Or f g) xs = (EQ2 f xs \<union> EQ2 g xs)"
by(auto simp:EQ2_def)

lemma EQ2_And[simp]: "EQ2 (And f g) xs = (EQ2 f xs \<union> EQ2 g xs)"
by(auto simp:EQ2_def)

lemma innermost_intvl2:
  "\<lbrakk> nqfree f; nolb f xs l x; l < x; x \<notin> EQ2 f xs; R.I f (x#xs); l < y; y \<le> x\<rbrakk>
  \<Longrightarrow> R.I f (y#xs)"
unfolding EQ2_def by(blast intro:innermost_intvl)

lemma I_subst_peps2:
 "nqfree f \<Longrightarrow> r+\<langle>cs,xs\<rangle> < x \<Longrightarrow> nolb f xs (r+\<langle>cs,xs\<rangle>) x
 \<Longrightarrow> \<forall>y \<in> {r+\<langle>cs,xs\<rangle> <.. x}. R.I f (y#xs) \<and> y \<notin> EQ2 f xs
 \<Longrightarrow> R.I (subst\<^sub>+ f (r,cs)) xs"
proof(induct f)
  case FalseF thus ?case
    by simp (metis linorder_antisym_conv1 linorder_neq_iff)
next
  case (Atom a)
  show ?case
  proof(cases "((r,cs),a)" rule:asubst_peps.cases)
    case (1 r cs s d ds)
    { assume "d=0" hence ?thesis using Atom 1 by auto }
    moreover
    { assume "d<0"
      have "s < d*x + \<langle>ds,xs\<rangle>" using Atom 1 by simp
      moreover have "d*x < d*(r + \<langle>cs,xs\<rangle>)" using \<open>d<0\<close> Atom 1
        by (simp add: mult_strict_left_mono_neg)
      ultimately have "s < d * (r + \<langle>cs,xs\<rangle>) + \<langle>ds,xs\<rangle>" by(simp add:algebra_simps)
      hence ?thesis using 1
        by (auto simp add: iprod_left_add_distrib algebra_simps)
    } moreover
    { let ?L = "(s - \<langle>ds,xs\<rangle>) / d" let ?U = "r + \<langle>cs,xs\<rangle>"
      assume "d>0"
      hence "?U < x" and "\<forall>y. ?U < y \<and> y < x \<longrightarrow> y \<noteq> ?L"
        and "\<forall>y. ?U < y \<and> y \<le> x \<longrightarrow> ?L < y" using Atom 1
        by(simp_all add:nolb_def depends\<^sub>R_def Ball_def field_simps)
      hence "?L < ?U \<or> ?L = ?U"
        by (metis linorder_neqE_linordered_idom order_refl)
      hence ?thesis using Atom 1 \<open>d>0\<close>
        by (simp add: iprod_left_add_distrib field_simps)
    } ultimately show ?thesis by force
  next
    case 2 thus ?thesis using Atom
      by (fastforce simp: nolb_def EQ2_def depends\<^sub>R_def field_simps split: if_split_asm)
  qed (insert Atom, auto)
next
  case Or thus ?case by(simp add:Ball_def)(metis order_refl innermost_intvl2)
qed simp_all

end

lemma I_subst_peps:
  "nqfree f \<Longrightarrow> R.I (subst\<^sub>+ f (r,cs)) xs \<Longrightarrow>
  (\<exists>leps>r+\<langle>cs,xs\<rangle>. \<forall>x. r+\<langle>cs,xs\<rangle> < x \<and> x \<le> leps \<longrightarrow> R.I f (x#xs))"
proof(induct f)
  case TrueF thus ?case by simp (metis less_add_one)
next
  case (Atom a)
  show ?case
  proof (cases "((r,cs),a)" rule: asubst_peps.cases)
    case (1 r cs s d ds)
    { assume "d=0" hence ?thesis using Atom 1 by auto (metis less_add_one) }
    moreover
    { assume "d<0"
      with Atom 1 have "r + \<langle>cs,xs\<rangle> < (s - \<langle>ds,xs\<rangle>)/d" (is "?a < ?b")
        by(simp add:field_simps iprod_left_add_distrib)
      then obtain x where "?a < x" "x < ?b" by(metis dense)
      hence " \<forall>y. ?a < y \<and> y \<le> x \<longrightarrow> s < d*y + \<langle>ds,xs\<rangle>"
        using \<open>d<0\<close> by (simp add:field_simps)
      (metis add_le_cancel_right mult_le_cancel_left order_antisym linear mult.commute xt1(8))
      hence ?thesis using 1 \<open>?a<x\<close> by auto
    } moreover
    { let ?a = "s - d * r" let ?b = "\<langle>d *\<^sub>s cs + ds,xs\<rangle>"
      assume "d>0"
      with Atom 1 have "?a < ?b \<or> ?a = ?b" by auto
      hence ?thesis
      proof
        assume "?a = ?b"
        thus ?thesis using \<open>d>0\<close> Atom 1
          by(simp add:field_simps iprod_left_add_distrib)
            (metis add_0_left add_less_cancel_right distrib_left mult.commute mult_strict_left_mono)
      next
        assume "?a < ?b"
        { fix x assume "r+\<langle>cs,xs\<rangle> < x \<and> x \<le> r+\<langle>cs,xs\<rangle> + 1"
          hence "d*(r + \<langle>cs,xs\<rangle>) < d*x"
            using \<open>d>0\<close> by(metis mult_strict_left_mono)
          hence "s < d*x + \<langle>ds,xs\<rangle>" using \<open>d>0\<close> \<open>?a < ?b\<close>
            by (simp add:algebra_simps iprod_left_add_distrib)
        }
        thus ?thesis using 1 \<open>d>0\<close>
          by(force simp: iprod_left_add_distrib)
      qed
    } ultimately show ?thesis by (metis less_linear)
  qed (insert Atom, auto split:if_split_asm intro: less_add_one)
next
  case And thus ?case
    apply clarsimp
    apply(rule_tac x="min leps lepsa" in exI)
    apply simp
    done
next
  case Or thus ?case by force
qed simp_all

lemma dense_interval:
assumes "finite L" "l \<in> L" "l < x" "P(x::real)"
and dense: "\<And>y l. \<lbrakk> \<forall>y\<in>{l<..<x}. y \<notin> L; l<x; l<y; y\<le>x \<rbrakk> \<Longrightarrow> P y"
shows "\<exists>l\<in>L. l<x \<and> (\<forall>y\<in>{l<..<x}. y \<notin> L) \<and> (\<forall>y. l<y \<and> y\<le>x \<longrightarrow> P y)"
proof -
  let ?L = "{l\<in>L. l < x}"
  let ?ll = "Max ?L"
  have "?L \<noteq> {}" using \<open>l \<in> L\<close> \<open>l<x\<close> by (blast intro:order_less_imp_le)
  hence "\<forall>y. ?ll<y \<and> y<x \<longrightarrow> y \<notin> L" using \<open>finite L\<close> by force
  moreover have "?ll \<in> L"
  proof
    show "?ll \<in> ?L" using \<open>finite L\<close> Max_in[OF _ \<open>?L \<noteq> {}\<close>] by simp
    show "?L \<subseteq> L" by blast
  qed
  moreover have "?ll < x" using \<open>finite L\<close> \<open>?L \<noteq> {}\<close> by simp
  ultimately show ?thesis using \<open>l < x\<close> \<open>?L \<noteq> {}\<close>
    by(blast intro!:dense greaterThanLessThan_iff[THEN iffD1])
qed

definition
"qe_eps\<^sub>1(f) =
(let as = R.atoms\<^sub>0 f; lbs = lbounds as; ebs = ebounds as
 in list_disj (inf\<^sub>- f # map (subst\<^sub>+ f) lbs @ map (subst f) ebs))"

theorem I_eps1:
assumes "nqfree f" shows "R.I (qe_eps\<^sub>1 f) xs = (\<exists>x. R.I f (x#xs))"
  (is "?QE = ?EX")
proof
  let ?as = "R.atoms\<^sub>0 f" let ?ebs = "ebounds ?as"
  assume ?QE
  { assume "R.I (inf\<^sub>- f) xs"
    hence ?EX using \<open>?QE\<close> min_inf[of f xs] \<open>nqfree f\<close>
      by(auto simp add:qe_eps\<^sub>1_def amap_fm_list_disj)
  } moreover
  { assume "\<forall>x \<in> EQ f xs. \<not>R.I f (x#xs)"
           "\<not> R.I (inf\<^sub>- f) xs"
    with \<open>?QE\<close> \<open>nqfree f\<close> obtain r cs where "R.I (subst\<^sub>+ f (r,cs)) xs"
      by (fastforce simp: qe_eps\<^sub>1_def set_ebounds diff_divide_distrib eval_def I_subst \<open>nqfree f\<close>)
    then obtain leps where "R.I f (leps#xs)"
      using I_subst_peps[OF \<open>nqfree f\<close>] by fastforce
    hence ?EX .. }
  ultimately show ?EX by blast
next
  let ?as = "R.atoms\<^sub>0 f" let ?ebs = "ebounds ?as"
  assume ?EX
  then obtain x where x: "R.I f (x#xs)" ..
  { assume "R.I (inf\<^sub>- f) xs"
    hence ?QE using \<open>nqfree f\<close> by(auto simp:qe_eps\<^sub>1_def)
  } moreover
  { assume "\<exists>rcs \<in> set ?ebs. R.I (subst f rcs) xs"
    hence ?QE by(auto simp:qe_eps\<^sub>1_def) } moreover
  { assume "\<not> R.I (inf\<^sub>- f) xs"
    and "\<forall>rcs \<in> set ?ebs. \<not> R.I (subst f rcs) xs"
    hence noE: "\<forall>e \<in> EQ f xs. \<not> R.I f (e#xs)" using \<open>nqfree f\<close>
      by (force simp:set_ebounds I_subst diff_divide_distrib eval_def split:if_split_asm)
    hence "x \<notin> EQ f xs" using x by fastforce
    obtain l where "l \<in> LB f xs" "l < x"
      using LBex[OF \<open>nqfree f\<close> x \<open>\<not> R.I(inf\<^sub>- f) xs\<close> \<open>x \<notin> EQ f xs\<close>] ..
    have "\<exists>l\<in>LB f xs. l<x \<and> nolb f xs l x \<and>
            (\<forall>y. l < y \<and> y \<le> x \<longrightarrow> R.I f (y#xs))"
      using dense_interval[where P = "\<lambda>x. R.I f (x#xs)", OF finite_LB \<open>l\<in>LB f xs\<close> \<open>l<x\<close> x] x innermost_intvl[OF \<open>nqfree f\<close> _ _ \<open>x \<notin> EQ f xs\<close>]
      by (simp add:nolb_def)
    then obtain r c cs
      where *: "Less r (c#cs) \<in> set(R.atoms\<^sub>0 f) \<and> c>0 \<and>
            (r - \<langle>cs,xs\<rangle>)/c < x \<and> nolb f xs ((r - \<langle>cs,xs\<rangle>)/c) x
            \<and> (\<forall>y. (r - \<langle>cs,xs\<rangle>)/c < y \<and> y \<le> x \<longrightarrow> R.I f (y#xs))"
      by blast
    then have "R.I (subst\<^sub>+ f (r/c, (-1/c) *\<^sub>s cs)) xs" using noE
      by(auto intro!: I_subst_peps2[OF \<open>nqfree f\<close>]
        simp:EQ2_def diff_divide_distrib algebra_simps)
    with * have ?QE
      by(simp add:qe_eps\<^sub>1_def bex_Un set_lbounds) metis
  } ultimately show ?QE by blast
qed

lemma qfree_asubst_peps: "qfree (asubst\<^sub>+ rcs a)"
by(cases "(rcs,a)" rule:asubst_peps.cases) simp_all

lemma qfree_subst_peps: "nqfree \<phi> \<Longrightarrow> qfree (subst\<^sub>+ \<phi> rcs)"
by(induct \<phi>) (simp_all add:qfree_asubst_peps)

lemma qfree_qe_eps\<^sub>1: "nqfree \<phi> \<Longrightarrow> qfree(qe_eps\<^sub>1 \<phi>)"
apply(simp add:qe_eps\<^sub>1_def)
apply(rule qfree_list_disj)
apply (auto simp:qfree_min_inf qfree_subst_peps qfree_map_fm)
done

definition "qe_eps = R.lift_nnf_qe qe_eps\<^sub>1"

lemma qfree_qe_eps: "qfree(qe_eps \<phi>)"
by(simp add: qe_eps_def R.qfree_lift_nnf_qe qfree_qe_eps\<^sub>1)

lemma I_qe_eps: "R.I (qe_eps \<phi>) xs = R.I \<phi> xs"
by(simp add:qe_eps_def R.I_lift_nnf_qe qfree_qe_eps\<^sub>1 I_eps1)

end
