(*  Author:     Tobias Nipkow, 2007  *)

theory QEdlo_inf
imports DLO
begin

subsection "Quantifier elimination with infinitesimals"

text\<open>This section presents a new quantifier elimination procedure
for dense linear orders based on (the simulation of) infinitesimals.
It is a fairly straightforward adaptation of the analogous algorithm
by Loos and Weispfenning for linear arithmetic described in
\S\ref{sec:lin-inf}.\<close>

fun asubst_peps :: "nat \<Rightarrow> atom \<Rightarrow> atom fm" ("asubst\<^sub>+") where
"asubst_peps k (Less 0 0) = FalseF" |
"asubst_peps k (Less 0 (Suc j)) = Atom(Less k j)" |
"asubst_peps k (Less (Suc i) 0) = (if i=k then TrueF
   else Or (Atom(Less i k)) (Atom(Eq i k)))" |
"asubst_peps k (Less (Suc i) (Suc j)) = Atom(Less i j)" |
"asubst_peps k (Eq 0 0) = TrueF" |
"asubst_peps k (Eq 0 _) = FalseF" |
"asubst_peps k (Eq _ 0) = FalseF" |
"asubst_peps k (Eq (Suc i) (Suc j)) = Atom(Eq i j)"

abbreviation subst_peps :: "atom fm \<Rightarrow> nat \<Rightarrow> atom fm" ("subst\<^sub>+") where
"subst\<^sub>+ \<phi> k \<equiv> amap\<^sub>f\<^sub>m (asubst\<^sub>+ k) \<phi>"

definition "nolb \<phi> xs l x = (\<forall>y\<in>{l<..<x}. y \<notin> LB \<phi> xs)"

lemma nolb_And[simp]:
  "nolb (And \<phi>\<^sub>1 \<phi>\<^sub>2) xs l x = (nolb \<phi>\<^sub>1 xs l x \<and> nolb \<phi>\<^sub>2 xs l x)"
apply(clarsimp simp:nolb_def)
apply blast
done

lemma nolb_Or[simp]:
  "nolb (Or \<phi>\<^sub>1 \<phi>\<^sub>2) xs l x = (nolb \<phi>\<^sub>1 xs l x \<and> nolb \<phi>\<^sub>2 xs l x)"
apply(clarsimp simp:nolb_def)
apply blast
done

context notes [[simp_depth_limit=3]]
begin

lemma innermost_intvl:
 "\<lbrakk> nqfree \<phi>; nolb \<phi> xs l x; l < x; x \<notin> EQ \<phi> xs; DLO.I \<phi> (x#xs); l < y; y \<le> x\<rbrakk>
  \<Longrightarrow> DLO.I \<phi> (y#xs)"
proof(induct \<phi>)
  case (Atom a)
  show ?case
  proof (cases a)
    case (Less i j)
    then show ?thesis using Atom
      unfolding nolb_def
      by (clarsimp simp: nth.simps Ball_def split:if_split_asm nat.splits)
         (metis not_le_imp_less order_antisym order_less_trans)+
  next
    case (Eq i j) thus ?thesis using Atom
      apply(clarsimp simp:EQ_def nolb_def nth_Cons')
      apply(case_tac "i=0 \<and> j=0") apply simp
      apply(case_tac "i\<noteq>0 \<and> j\<noteq>0") apply simp
      apply(case_tac "i=0 \<and> j\<noteq>0") apply (fastforce split:if_split_asm)
      apply(case_tac "i\<noteq>0 \<and> j=0") apply (fastforce split:if_split_asm)
      apply arith
      done
  qed
next
  case And thus ?case by (fastforce)
next
  case Or thus ?case by (fastforce)
qed simp+


lemma I_subst_peps2:
 "nqfree \<phi> \<Longrightarrow> xs!l < x \<Longrightarrow> nolb \<phi> xs (xs!l) x \<Longrightarrow> x \<notin> EQ \<phi> xs
 \<Longrightarrow> \<forall>y \<in> {xs!l <.. x}. DLO.I \<phi> (y#xs)
 \<Longrightarrow> DLO.I (subst\<^sub>+ \<phi> l) xs"
proof(induct \<phi>)
  case FalseF thus ?case
    by simp (metis linorder_antisym_conv1 linorder_neq_iff)
next
  case (Atom a)
  show ?case
  proof(cases "(l,a)" rule:asubst_peps.cases)
    case 3 thus ?thesis using Atom
      by (auto simp: nolb_def EQ_def Ball_def)
         (metis One_nat_def linorder_antisym_conv1 not_less_iff_gr_or_eq)
  qed (insert Atom, auto simp: nolb_def EQ_def Ball_def)
next
  case Or thus ?case by(simp add: Ball_def)(metis order_refl innermost_intvl)
qed simp_all

end

lemma dense_interval:
assumes "finite L" "l \<in> L" "l < x" "P(x::'a::dlo)"
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


lemma I_subst_peps:
  "nqfree \<phi> \<Longrightarrow> DLO.I (subst\<^sub>+ \<phi> l) xs \<longrightarrow>
  (\<exists>leps>xs!l. \<forall>x. xs!l < x \<and> x \<le> leps \<longrightarrow> DLO.I \<phi> (x#xs))"
proof(induct \<phi>)
  case TrueF thus ?case by simp (metis no_ub)
next
  case (Atom a)
  show ?case
  proof (cases "(l,a)" rule: asubst_peps.cases)
    case 2 thus ?thesis using Atom
      apply(auto)
      apply(drule dense)
      apply(metis One_nat_def xt1(7))
      done
  next
    case 3 thus ?thesis using Atom
      apply(auto)
        apply (metis no_ub)
       apply (metis no_ub less_trans)
      apply (metis no_ub)
      done
  next
    case 4 thus ?thesis using Atom by(auto)(metis no_ub)
  next
    case 5 thus ?thesis using Atom by(auto)(metis no_ub)
  next
    case 8 thus ?thesis using Atom by(auto)(metis no_ub)
  qed (insert Atom, auto)
next
  case And thus ?case
    apply clarsimp
    apply(rule_tac x="min leps lepsa" in exI)
    apply simp
    done
next
  case Or thus ?case by force
qed simp_all


definition
"qe_eps\<^sub>1(\<phi>) =
(let as = DLO.atoms\<^sub>0 \<phi>; lbs = lbounds as; ebs = ebounds as
 in list_disj (inf\<^sub>- \<phi> # map (subst\<^sub>+ \<phi>) lbs @ map (subst \<phi>) ebs))"

theorem I_qe_eps1:
assumes "nqfree \<phi>" shows "DLO.I (qe_eps\<^sub>1 \<phi>) xs = (\<exists>x. DLO.I \<phi> (x#xs))"
  (is "?QE = ?EX")
proof
  let ?as = "DLO.atoms\<^sub>0 \<phi>" let ?ebs = "ebounds ?as"
  assume ?QE
  { assume "DLO.I (inf\<^sub>- \<phi>) xs"
    hence ?EX using \<open>?QE\<close> min_inf[of \<phi> xs] \<open>nqfree \<phi>\<close>
      by(auto simp add:qe_eps\<^sub>1_def amap_fm_list_disj)
  } moreover
  { assume "\<forall>i \<in> set ?ebs. \<not>DLO.I \<phi> (xs!i # xs)"
           "\<not> DLO.I (inf\<^sub>- \<phi>) xs"
    with \<open>?QE\<close> \<open>nqfree \<phi>\<close> obtain l where "DLO.I (subst\<^sub>+ \<phi> l) xs"
      by(fastforce simp: I_subst qe_eps\<^sub>1_def set_ebounds set_lbounds)
    then obtain leps where "DLO.I \<phi> (leps#xs)"
      using I_subst_peps[OF \<open>nqfree \<phi>\<close>] by fastforce
    hence ?EX .. }
  ultimately show ?EX by blast
next
  let ?as = "DLO.atoms\<^sub>0 \<phi>" let ?ebs = "ebounds ?as"
  assume ?EX
  then obtain x where x: "DLO.I \<phi> (x#xs)" ..
  { assume "DLO.I (inf\<^sub>- \<phi>) xs"
    hence ?QE using \<open>nqfree \<phi>\<close> by(auto simp:qe_eps\<^sub>1_def)
  } moreover
  { assume "\<exists>k \<in> set ?ebs. DLO.I (subst \<phi> k) xs"
    hence ?QE by(auto simp:qe_eps\<^sub>1_def) } moreover
  { assume "\<not> DLO.I (inf\<^sub>- \<phi>) xs"
    and "\<forall>k \<in> set ?ebs. \<not> DLO.I (subst \<phi> k) xs"
    hence noE: "\<forall>e \<in> EQ \<phi> xs. \<not> DLO.I \<phi> (e#xs)" using \<open>nqfree \<phi>\<close>
      by (auto simp:set_ebounds EQ_def I_subst nth_Cons' split:if_split_asm)
    hence "x \<notin> EQ \<phi> xs" using x by fastforce
    obtain l where "l \<in> LB \<phi> xs" "l < x"
      using LBex[OF \<open>nqfree \<phi>\<close> x \<open>\<not> DLO.I(inf\<^sub>- \<phi>) xs\<close> \<open>x \<notin> EQ \<phi> xs\<close>] ..
    have "\<exists>l\<in>LB \<phi> xs. l<x \<and> nolb \<phi> xs l x \<and>
            (\<forall>y. l < y \<and> y \<le> x \<longrightarrow> DLO.I \<phi> (y#xs))"
      using dense_interval[where P = "\<lambda>x. DLO.I \<phi> (x#xs)", OF finite_LB \<open>l\<in>LB \<phi> xs\<close> \<open>l<x\<close> x] x innermost_intvl[OF \<open>nqfree \<phi>\<close> _ _ \<open>x \<notin> EQ \<phi> xs\<close>]
      by (simp add:nolb_def)
    then obtain m
      where *: "Less (Suc m) 0 \<in> set ?as \<and> xs!m < x \<and> nolb \<phi> xs (xs!m) x
            \<and> (\<forall>y. xs!m < y \<and> y \<le> x \<longrightarrow> DLO.I \<phi> (y#xs))"
      by blast
    then have "DLO.I (subst\<^sub>+ \<phi> m) xs"
      using noE by(auto intro!: I_subst_peps2[OF \<open>nqfree \<phi>\<close>])
    with * have ?QE
      by(simp add:qe_eps\<^sub>1_def bex_Un set_lbounds set_ebounds) metis
  } ultimately show ?QE by blast
qed

lemma qfree_asubst_peps: "qfree (asubst\<^sub>+ k a)"
by(cases "(k,a)" rule:asubst_peps.cases) simp_all

lemma qfree_subst_peps: "nqfree \<phi> \<Longrightarrow> qfree (subst\<^sub>+ \<phi> k)"
by(induct \<phi>) (simp_all add:qfree_asubst_peps)

lemma qfree_qe_eps\<^sub>1: "nqfree \<phi> \<Longrightarrow> qfree(qe_eps\<^sub>1 \<phi>)"
apply(simp add:qe_eps\<^sub>1_def)
apply(rule qfree_list_disj)
apply (auto simp:qfree_min_inf qfree_subst_peps qfree_map_fm)
done

definition "qe_eps = DLO.lift_nnf_qe qe_eps\<^sub>1"

lemma qfree_qe_eps: "qfree(qe_eps \<phi>)"
by(simp add: qe_eps_def DLO.qfree_lift_nnf_qe qfree_qe_eps\<^sub>1)

lemma I_qe_eps: "DLO.I (qe_eps \<phi>) xs = DLO.I \<phi> xs"
by(simp add:qe_eps_def DLO.I_lift_nnf_qe qfree_qe_eps\<^sub>1 I_qe_eps1)

end
