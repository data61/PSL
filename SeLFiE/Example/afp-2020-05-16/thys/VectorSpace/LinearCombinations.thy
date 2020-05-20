section \<open>Linear Combinations\<close>

theory LinearCombinations
imports Main
  "HOL-Algebra.Module"
  "HOL-Algebra.Coset"
  RingModuleFacts
  MonoidSums
  FunctionLemmas
begin

subsection \<open>Lemmas for simplification\<close>
text \<open>The following are helpful in certain simplifications (esp. congruence rules). Warning: arbitrary
use leads to looping.\<close>
lemma (in ring) coeff_in_ring:
  "\<lbrakk>a\<in>A\<rightarrow>carrier R; x\<in>A\<rbrakk> \<Longrightarrow> a x \<in>carrier R"
by (rule Pi_mem)

lemma (in ring) coeff_in_ring2:
  "\<lbrakk> x\<in>A;a\<in>A\<rightarrow>carrier R\<rbrakk> \<Longrightarrow> a x \<in>carrier R"
by (metis Pi_mem)

lemma ring_subset_carrier:
  "\<lbrakk>x \<in>A; A\<subseteq>carrier R\<rbrakk> \<Longrightarrow> x \<in>carrier R"
by auto

lemma disj_if:
  "\<lbrakk>A\<inter>B={}; x\<in> B\<rbrakk> \<Longrightarrow> (if x\<in>A then f x else g x) = g x"
by auto


lemmas (in module) sum_simp = ring_subset_carrier

subsection \<open>Linear combinations\<close>
text \<open>A linear combination is $\sum_{v\in A} a_v v$. $(a_v)_{v\in S}$ is a function 
$A\to K$, where $A\subseteq K$.\<close>
definition (in module) lincomb::"['c \<Rightarrow> 'a, 'c set]\<Rightarrow> 'c"
where "lincomb a A = (\<Oplus>\<^bsub>M\<^esub>  v\<in>A. (a v \<odot>\<^bsub>M\<^esub> v))"

lemma (in module) summands_valid:
  fixes A a
  assumes h2: "A\<subseteq> carrier M" and h3: "a\<in>(A\<rightarrow>carrier R)"
  shows "\<forall> v\<in> A. (((a v) \<odot>\<^bsub>M\<^esub> v)\<in> carrier M)"
proof - 
  from assms show ?thesis by auto
qed

lemma (in module) lincomb_closed [simp, intro]:
  fixes S a
  assumes h2: "S\<subseteq> carrier M" and h3: "a\<in>(S\<rightarrow>carrier R)"
  shows "lincomb a S \<in> carrier M"
proof -
  from h2 h3 show ?thesis by (unfold lincomb_def, auto intro:finsum_closed)
(*doesn't work with simp*)
qed

lemma (in comm_monoid) finprod_cong2:
  "[| A = B; 
      !!i. i \<in> B ==> f i = g i; f \<in> B \<rightarrow> carrier G|] ==> 
finprod G f A = finprod G g B"
by (intro finprod_cong, auto)

lemmas (in abelian_monoid) finsum_cong2 = add.finprod_cong2

lemma (in module) lincomb_cong:
  assumes h2: "A=B" and h3: "A \<subseteq> carrier M" 
    and h4: "\<And>v. v\<in>A \<Longrightarrow> a v = b v" and h5: "b\<in> B\<rightarrow>carrier R"
  shows "lincomb a A = lincomb b B"
using assms
    by (simp cong: finsum_cong2 add: lincomb_def summands_valid ring_subset_carrier)

lemma (in module) lincomb_union:
  fixes a A B 
  assumes h1: "finite (A\<union> B)"  and h3: "A\<union>B \<subseteq> carrier M" 
    and h4: "A\<inter>B={}" and h5: "a\<in>(A\<union>B\<rightarrow>carrier R)"
  shows "lincomb a (A\<union>B) = lincomb a A \<oplus>\<^bsub>M\<^esub> lincomb a B"
using assms
  by (auto cong: finsum_cong2 simp add: lincomb_def finsum_Un_disjoint summands_valid ring_subset_carrier)

text \<open>This is useful as a simp rule sometimes, for combining linear combinations.\<close>
lemma (in module) lincomb_union2:
  fixes a b A B 
  assumes h1: "finite (A\<union> B)"  and h3: "A\<union>B \<subseteq> carrier M" 
    and h4: "A\<inter>B={}" and h5: "a\<in>A\<rightarrow>carrier R" and h6: "b\<in>B\<rightarrow>carrier R"
  shows "lincomb a A \<oplus>\<^bsub>M\<^esub> lincomb b B = lincomb (\<lambda>v. if (v\<in>A) then a v else b v) (A\<union>B)"
    (is "lincomb a A \<oplus>\<^bsub>M\<^esub> lincomb b B = lincomb ?c (A\<union>B)")
using assms
  by (auto cong: finsum_cong2 
        simp add: lincomb_def finsum_Un_disjoint summands_valid ring_subset_carrier disj_if)

lemma (in module) lincomb_del2:
  fixes S a v
  assumes h1: "finite S" and h2: "S\<subseteq> carrier M" and h3: "a\<in>(S\<rightarrow>carrier R)" and h4:"v\<in>S"
  shows "lincomb a S = ((a v) \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> lincomb a (S-{v})"
proof - 
  from h4 have 1: "S={v}\<union>(S-{v})" by (metis insert_Diff insert_is_Un) 
  from assms show ?thesis
    apply (subst 1)
    apply (subst lincomb_union, auto)
    by (unfold lincomb_def, auto simp add: coeff_in_ring)
qed

(*alternate form of the above*)
lemma (in module) lincomb_insert:
  fixes S a v
  assumes h1: "finite S" and h2: "S\<subseteq> carrier M" and h3: "a\<in>(S\<union>{v}\<rightarrow>carrier R)" and h4:"v\<notin>S" and 
h5:"v\<in> carrier M"
  shows "lincomb a (S\<union>{v}) = ((a v) \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> lincomb a S"
using assms
  by (auto cong: finsum_cong2 
        simp add: lincomb_def finsum_Un_disjoint summands_valid ring_subset_carrier disj_if)

lemma (in module) lincomb_elim_if [simp]:
  fixes b c S
  assumes h1: "S \<subseteq> carrier M" and h2: "\<And>v. v\<in>S\<Longrightarrow> \<not>P v" and h3: "c\<in>S\<rightarrow>carrier R"
  shows "lincomb (\<lambda>w. if P w then b w else c w) S = lincomb c S"
using assms
  by (auto cong: finsum_cong2 
        simp add: lincomb_def finsum_Un_disjoint summands_valid ring_subset_carrier disj_if)

lemma (in module) lincomb_smult:
  fixes A c
  assumes h2: "A\<subseteq>carrier M"  and h3: "a\<in>A\<rightarrow>carrier R" and h4: "c\<in>carrier R"
  shows "lincomb (\<lambda>w. c\<otimes>\<^bsub>R\<^esub> a w) A = c\<odot>\<^bsub>M\<^esub> (lincomb a A)"
using assms
  by (auto cong: finsum_cong2 
        simp add: lincomb_def finsum_Un_disjoint finsum_smult ring_subset_carrier disj_if smult_assoc1 coeff_in_ring)

subsection \<open>Linear dependence and independence.\<close>
text \<open>A set $S$ in a module/vectorspace is linearly dependent if there is a finite set $A \subseteq S$
 and coefficients $(a_v)_{v\in A}$ such that $sum_{v\in A} a_vv=0$ and for some $v$, $a_v\neq 0$.\<close>
definition (in module) lin_dep where
  "lin_dep S = (\<exists>A a v. (finite A \<and> A\<subseteq>S \<and> (a\<in> (A\<rightarrow>carrier R)) \<and> (lincomb a A = \<zero>\<^bsub>M\<^esub>) \<and> (v\<in>A) \<and> (a v\<noteq> \<zero>\<^bsub>R\<^esub>)))"
  (*shows "\<exists>a. (a\<in> (S\<rightarrow>carrier K)) \<and> (lincomb a S = \<zero>\<^bsub>V\<^esub>) \<and> (\<exists>v\<in>S. a v\<noteq> \<zero>\<^bsub>K\<^esub>)"*)

abbreviation (in module) lin_indpt::"'c set \<Rightarrow> bool"
  where "lin_indpt S \<equiv> \<not>lin_dep S"

text \<open>In the finite case, we can take $A=S$. This may be more convenient (e.g., when adding two
linear combinations.\<close>
lemma (in module) finite_lin_dep: 
  fixes S
  assumes finS:"finite S" and ld: "lin_dep S" and inC: "S\<subseteq>carrier M"
  shows "\<exists>a v. (a\<in> (S\<rightarrow>carrier R)) \<and> (lincomb a S = \<zero>\<^bsub>M\<^esub>) \<and> (v\<in>S) \<and> (a v\<noteq> \<zero>\<^bsub>R\<^esub>)"
proof - 
  from ld obtain A a v where A: "(A\<subseteq>S \<and> (a\<in> (A\<rightarrow>carrier R)) \<and> (lincomb a A = \<zero>\<^bsub>M\<^esub>) \<and> (v\<in>A) \<and> (a v\<noteq> \<zero>\<^bsub>R\<^esub>))" 
    by (unfold lin_dep_def, auto)
  let ?b="\<lambda>w. if w\<in>A then a w else \<zero>\<^bsub>R\<^esub>" (*extend the coefficients to be 0 outside of A*)
  from finS inC A have if_in: "(\<Oplus>\<^bsub>M\<^esub>v\<in>S. (if v \<in> A then a v else \<zero>) \<odot>\<^bsub>M\<^esub> v) = (\<Oplus>\<^bsub>M\<^esub>v\<in>S. (if v \<in> A then a v \<odot>\<^bsub>M\<^esub> v else \<zero>\<^bsub>M\<^esub>))"
    apply auto
      apply (intro finsum_cong') 
    by (auto simp add: coeff_in_ring)  (*massage the sum*)
  from finS inC A have b: "lincomb ?b S = \<zero>\<^bsub>M\<^esub>"
    apply (unfold lincomb_def)
    apply (subst if_in)
    by (subst extend_sum, auto)
  from A b show ?thesis 
    apply (rule_tac x="?b" in exI)
    apply (rule_tac x="v" in exI)
    by auto
qed

text \<open>Criteria of linear dependency in a easy format to apply: apply (rule lin-dep-crit)\<close>
lemma (in module) lin_dep_crit: 
  fixes A S a v
  assumes fin: "finite A" and subset: "A\<subseteq>S" and h1: "(a\<in> (A\<rightarrow>carrier R))" and h2: "v\<in> A" 
    and h3:"a v\<noteq> \<zero>\<^bsub>R\<^esub>" and h4: "(lincomb a A = \<zero>\<^bsub>M\<^esub>)"
  shows "lin_dep S"
proof - 
  from assms show ?thesis
    by (unfold lin_dep_def, auto) 
qed

text \<open>If $\sum_{v\in A} a_vv=0$ implies $a_v=0$ for all $v\in S$, then $A$ is linearly independent.\<close>
lemma (in module) finite_lin_indpt2:
  fixes A 
  assumes A_fin: "finite A" and AinC: "A\<subseteq>carrier M" and
    lc0: "\<And>a. a\<in> (A\<rightarrow>carrier R) \<Longrightarrow> (lincomb a A = \<zero>\<^bsub>M\<^esub>) \<Longrightarrow> (\<forall> v\<in>A. a v= \<zero>\<^bsub>R\<^esub>)"
  shows "lin_indpt A"
proof (rule ccontr)
  assume "\<not>lin_indpt A"
  from A_fin AinC this obtain a v where av:
    "(a\<in> (A\<rightarrow>carrier R)) \<and> (lincomb a A = \<zero>\<^bsub>M\<^esub>) \<and> (v\<in>A) \<and> (a v\<noteq> \<zero>\<^bsub>R\<^esub>)"
    by (metis finite_lin_dep)
  from av lc0 show False by auto
qed

text \<open>Any set containing 0 is linearly dependent.\<close>
lemma (in module) zero_lin_dep: 
  assumes 0: "\<zero>\<^bsub>M\<^esub> \<in> S" and nonzero: "carrier R \<noteq> {\<zero>\<^bsub>R\<^esub>}"
  shows "lin_dep S"
proof - 
  from nonzero have zero_not_one: "\<zero>\<^bsub>R\<^esub> \<noteq> \<one>\<^bsub>R\<^esub>" by (rule nontrivial_ring)
  from 0 zero_not_one show ?thesis
    apply (unfold lin_dep_def)
    apply (rule_tac x="{\<zero>\<^bsub>M\<^esub>}" in exI)
    apply (rule_tac x="(\<lambda>v. \<one>\<^bsub>R\<^esub>)" in exI)
    apply (rule_tac x="\<zero>\<^bsub>M\<^esub>" in exI)
    by (unfold lincomb_def, auto)
qed

lemma (in module) zero_nin_lin_indpt: 
  assumes h2: "S\<subseteq>carrier M" and li: "\<not>(lin_dep S)" and nonzero: "carrier R \<noteq> {\<zero>\<^bsub>R\<^esub>}"
  shows "\<zero>\<^bsub>M\<^esub> \<notin> S"
proof (rule ccontr)
  assume a1: "\<not>(\<zero>\<^bsub>M\<^esub> \<notin> S)"
  from a1 have a2: "\<zero>\<^bsub>M\<^esub> \<in> S" by auto
  from a2 nonzero have ld: "lin_dep S" by (rule zero_lin_dep)
  from li ld show False by auto
qed

text \<open>The \<open>span\<close> of $S$ is the set of linear combinations with $A \subseteq S$.\<close>
definition (in module) span::"'c set \<Rightarrow>'c set" 
  where "span S = {lincomb a A | a A. finite A \<and> A\<subseteq>S \<and> a\<in> (A\<rightarrow>carrier R)}"

text \<open>The \<open>span\<close> interpreted as a module or vectorspace.\<close>
abbreviation (in module) span_vs::"'c set \<Rightarrow> ('a,'c,'d) module_scheme" 
  where "span_vs S \<equiv> M \<lparr>carrier := span S\<rparr>"

text \<open>In the finite case, we can take $A=S$ without loss of generality.\<close>
lemma (in module) finite_span:
  assumes fin: "finite S" and inC: "S\<subseteq>carrier M"
  shows "span S = {lincomb a S | a. a\<in> (S\<rightarrow>carrier R)}"
proof (rule equalityI) 
  {
    fix A a
    assume subset: "A \<subseteq> S" and   a: "a \<in> A \<rightarrow> carrier R"
    let ?b="(\<lambda>v. if v \<in> A then a v else \<zero>)"
    from fin inC subset a have if_in: "(\<Oplus>\<^bsub>M\<^esub>v\<in>S. ?b v \<odot>\<^bsub>M\<^esub> v) = (\<Oplus>\<^bsub>M\<^esub>v\<in>S. (if v \<in> A then a v \<odot>\<^bsub>M\<^esub> v else \<zero>\<^bsub>M\<^esub>))"
      apply (intro finsum_cong') 
        by (auto simp add: coeff_in_ring)  (*massage the sum*)
    from fin inC subset a have "\<exists>b. lincomb a A = lincomb b S \<and> b \<in> S \<rightarrow> carrier R"
      apply (rule_tac x="?b" in exI)
      apply (unfold lincomb_def, auto)
      apply (subst if_in)
      by (subst extend_sum, auto)
  }
  from this show "span S \<subseteq> {lincomb a S |a. a \<in> S \<rightarrow> carrier R}"
    by (unfold span_def, auto)
next
  from fin show "{lincomb a S |a. a \<in> S \<rightarrow> carrier R} \<subseteq> span S"
    by (unfold span_def, auto)
qed

text \<open>If $v\in \text{span S}$, then we can find a linear combination. This is in an easy to apply
format (e.g. obtain a A where\ldots)\<close>
lemma (in module) in_span:
  fixes S v
  assumes  h2: "S\<subseteq>carrier V" and h3: "v\<in>span S"
  shows "\<exists>a A. (A\<subseteq>S \<and> (a\<in>A\<rightarrow>carrier R) \<and> (lincomb a A=v))"
proof - 
  from h2 h3 show ?thesis
    apply (unfold span_def)
    by auto
qed

text \<open>In the finite case, we can take $A=S$.\<close>
lemma (in module) finite_in_span:
  fixes S v
  assumes fin: "finite S" and h2: "S\<subseteq>carrier M" and h3: "v\<in>span S"
  shows "\<exists>a. (a\<in>S\<rightarrow>carrier R) \<and> (lincomb a S=v)"
proof - 
  from fin h2 have fin_span: "span S = {lincomb a S |a. a \<in> S \<rightarrow> carrier R}" by (rule finite_span)
  from h3 fin_span show ?thesis by auto
qed

text \<open>If a subset is linearly independent, then any linear combination that is 0 must have a 
nonzero coefficient outside that set.\<close>
lemma (in module) lincomb_must_include:
  fixes A S T b v
  assumes  inC: "T\<subseteq>carrier M" and li: "lin_indpt S" and Ssub: "S\<subseteq>T" and Ssub: "A\<subseteq>T"
    and fin: "finite A"
    and b: "b\<in>A\<rightarrow>carrier R" and lc: "lincomb b A=\<zero>\<^bsub>M\<^esub>" and v_in: "v\<in>A"
    and nz_coeff: "b v\<noteq>\<zero>\<^bsub>R\<^esub>"
  shows "\<exists>w\<in>A-S. b w\<noteq>\<zero>\<^bsub>R\<^esub>"
proof (rule ccontr) 
  (*we may assume B doesn't intersect A.*)
  assume 0: "\<not>(\<exists> w\<in>A-S. b w\<noteq>\<zero>\<^bsub>R\<^esub>)"
  from 0 have 1: "\<And>w. w\<in>A-S\<Longrightarrow> b w=\<zero>\<^bsub>R\<^esub>" by auto
  have Auni: "A=(S\<inter>A) \<union>(A-S)" by auto
  from fin b Ssub inC 1 have 2: "lincomb b A = lincomb b (S\<inter>A)"(* \<oplus>\<^bsub>M\<^esub> lincomb b ((-S)\<inter>A)*)
    apply (subst Auni) 
    apply (subst lincomb_union, auto)
    (*apply (intro r_zero)*)
    apply (unfold lincomb_def)
    apply (subst (2) finsum_all0, auto)
    by (subst show_r_zero, auto intro!: finsum_closed)
  from 1 2 assms have ld: "lin_dep S" 
    apply (intro lin_dep_crit[where ?A="S\<inter>A" and ?a="b" and ?v="v"])
    by auto
  from ld li show False by auto
qed

text \<open>A generating set is a set such that the span of $S$ is all of $M$.\<close>
abbreviation (in module) gen_set::"'c set \<Rightarrow> bool"
  where "gen_set S \<equiv> (span S = carrier M)" 

subsection \<open>Submodules\<close>

lemma module_criteria:
  fixes R and M 
  assumes cring: "cring R"
      and zero: "\<zero>\<^bsub>M\<^esub>\<in> carrier M" 
      and add: "\<forall>v w. v\<in>carrier M \<and> w\<in>carrier M\<longrightarrow> v\<oplus>\<^bsub>M\<^esub> w\<in> carrier M"
      and neg: "\<forall>v\<in>carrier M. (\<exists>neg_v\<in>carrier M. v\<oplus>\<^bsub>M\<^esub>neg_v=\<zero>\<^bsub>M\<^esub>)"
      and smult: "\<forall>c v. c\<in> carrier R \<and> v\<in>carrier M\<longrightarrow> c\<odot>\<^bsub>M\<^esub> v \<in> carrier M"
      and comm: "\<forall>v w. v\<in>carrier M \<and> w\<in>carrier M\<longrightarrow> v\<oplus>\<^bsub>M\<^esub> w=w\<oplus>\<^bsub>M\<^esub> v"
      and assoc: "\<forall>v w x. v\<in>carrier M \<and> w\<in>carrier M \<and> x\<in>carrier M\<longrightarrow> (v\<oplus>\<^bsub>M\<^esub> w)\<oplus>\<^bsub>M\<^esub> x= v\<oplus>\<^bsub>M\<^esub> (w\<oplus>\<^bsub>M\<^esub> x)"
      and add_id: "\<forall>v\<in>carrier M. (v\<oplus>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub> =v)"
      and compat: "\<forall>a b v. a\<in> carrier R \<and> b\<in> carrier R \<and> v\<in>carrier M\<longrightarrow> (a\<otimes>\<^bsub>R\<^esub> b)\<odot>\<^bsub>M\<^esub> v =a\<odot>\<^bsub>M\<^esub> (b\<odot>\<^bsub>M\<^esub> v)"
      and smult_id: "\<forall>v\<in>carrier M. (\<one>\<^bsub>R\<^esub> \<odot>\<^bsub>M\<^esub> v =v)"
      and dist_f: "\<forall>a b v. a\<in> carrier R \<and> b\<in> carrier R \<and> v\<in>carrier M\<longrightarrow> (a\<oplus>\<^bsub>R\<^esub> b)\<odot>\<^bsub>M\<^esub> v =(a\<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (b\<odot>\<^bsub>M\<^esub> v)"
      and dist_add: "\<forall>a v w. a\<in> carrier R \<and> v\<in>carrier M \<and> w\<in>carrier M\<longrightarrow> a\<odot>\<^bsub>M\<^esub> (v\<oplus>\<^bsub>M\<^esub> w) =(a\<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (a\<odot>\<^bsub>M\<^esub> w)"
  shows "module R M"
proof - 
  from assms have 2: "abelian_group M" 
    by (intro abelian_groupI, auto)
  from assms have 3: "module_axioms R M"
    by (unfold module_axioms_def, auto)
  from 2 3 cring show ?thesis 
    by (unfold module_def module_def, auto)
qed

text \<open>A submodule is $N\subseteq M$ that is closed under addition and scalar multiplication, and
contains 0 (so is not empty).\<close>
locale submodule =
  fixes R and N and M (structure)
  assumes module: "module R M" 
    and subset: "N \<subseteq> carrier M"
    and m_closed [intro, simp]: "\<lbrakk>v \<in> N; w \<in> N\<rbrakk> \<Longrightarrow> v \<oplus> w \<in> N"
    and zero_closed [simp]: "\<zero> \<in> N" (*prevents N from being the empty set*)
    and smult_closed [intro, simp]: "\<lbrakk>c \<in> carrier R; v \<in> N\<rbrakk> \<Longrightarrow> c\<odot>v \<in> N"

abbreviation (in module) md::"'c set \<Rightarrow> ('a, 'c, 'd) module_scheme"
  where "md N \<equiv> M\<lparr>carrier :=N\<rparr>"

lemma (in module) carrier_vs_is_self [simp]:
  "carrier (md N) = N"
  by auto

lemma (in module) submodule_is_module:
  fixes N::"'c set"
  assumes 0: "submodule R N M"
  shows "module R (md N)"
proof  (unfold module_def, auto)
  show 1: "cring R"..
next
  from assms show 2: "abelian_group (md N)" 
    apply (unfold submodule_def)
    apply (intro abelian_groupI, auto)
      apply (metis (no_types, hide_lams) M.add.m_assoc contra_subsetD)
     apply (metis (no_types, hide_lams) M.add.m_comm contra_subsetD)
    apply (rename_tac v)
    txt \<open>The inverse of $v$ under addition is $-v$\<close>
    apply (rule_tac x="\<ominus>\<^bsub>M\<^esub>v" in bexI)
     apply (metis M.l_neg contra_subsetD)
    by (metis R.add.inv_closed one_closed smult_minus_1 subset_iff)
next
  from assms show 3: "module_axioms R (md N)"
    apply (unfold module_axioms_def submodule_def, auto)
      apply (metis (no_types, hide_lams) smult_l_distr contra_subsetD)
     apply (metis (no_types, hide_lams) smult_r_distr contra_subsetD)
    by (metis (no_types, hide_lams) smult_assoc1 contra_subsetD)
qed

text \<open>$N_1+N_2=\{x+y | x\in N_1,y\in N_2\}$\<close>
definition (in module) submodule_sum:: "['c set, 'c set] \<Rightarrow> 'c set"
  where "submodule_sum N1 N2 = (\<lambda> (x,y). x \<oplus>\<^bsub>M\<^esub> y) `{(x,y). x\<in>  N1 \<and> y\<in> N2}"
(*This only depends on the carriers, actually, so it could be defined on that level if desired.*)

text \<open>A module homomorphism $M\to N$ preserves addition and scalar multiplication.\<close>
definition module_hom:: "[('a, 'c0) ring_scheme, 
  ('a,'b1,'c1) module_scheme, ('a,'b2,'c2) module_scheme] \<Rightarrow>('b1\<Rightarrow>'b2) set"
  where "module_hom R M N = {f. 
    ((f\<in> carrier M \<rightarrow> carrier N)
    \<and> (\<forall>m1 m2. m1\<in>carrier M\<and> m2\<in>carrier M \<longrightarrow> f (m1 \<oplus>\<^bsub>M\<^esub> m2) = (f m1) \<oplus>\<^bsub>N\<^esub> (f m2))
    \<and> (\<forall>r m. r\<in>carrier R\<and> m\<in>carrier M \<longrightarrow>f (r \<odot>\<^bsub>M\<^esub> m) = r \<odot>\<^bsub>N\<^esub> (f m)))}"

lemma module_hom_closed: "f\<in> module_hom R M N \<Longrightarrow> f\<in> carrier M \<rightarrow> carrier N"
by (unfold module_hom_def, auto)

lemma module_hom_add: "\<lbrakk>f\<in> module_hom R M N; m1\<in>carrier M; m2\<in>carrier M \<rbrakk> \<Longrightarrow> f (m1 \<oplus>\<^bsub>M\<^esub> m2) = (f m1) \<oplus>\<^bsub>N\<^esub> (f m2)"
by (unfold module_hom_def, auto)

lemma module_hom_smult: "\<lbrakk>f\<in> module_hom R M N; r\<in>carrier R; m\<in>carrier M \<rbrakk>  \<Longrightarrow> f (r \<odot>\<^bsub>M\<^esub> m) = r \<odot>\<^bsub>N\<^esub> (f m)"
by (unfold module_hom_def, auto)

locale mod_hom = 
  M?: module R M + N?: module R N
    for R and M and N +
  fixes f
  assumes f_hom: "f \<in> module_hom R M N"
  notes f_add [simp] = module_hom_add [OF f_hom]
    and f_smult [simp] = module_hom_smult [OF f_hom]

text \<open>Some basic simplification rules for module homomorphisms.\<close>
context mod_hom
begin

lemma f_im [simp, intro]: 
assumes "v \<in> carrier M" (*doesn't work if \<Longrightarrow>*)
shows "f v \<in> carrier N"
proof - 
  have 0: "mod_hom R M N f"..
  from 0 assms show ?thesis
    apply (unfold mod_hom_def module_hom_def mod_hom_axioms_def Pi_def)
    by auto
qed

definition im:: "'e set"
  where "im = f`(carrier M)"

definition ker:: "'c set"
  where "ker = {v. v \<in> carrier M & f v = \<zero>\<^bsub>N\<^esub>}"

lemma f0_is_0[simp]: "f \<zero>\<^bsub>M\<^esub>=\<zero>\<^bsub>N\<^esub>"
proof -
  have 1: "f \<zero>\<^bsub>M\<^esub> = f (\<zero>\<^bsub>R\<^esub> \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub>)" by simp
  have 2: "f (\<zero>\<^bsub>R\<^esub> \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub>) = \<zero>\<^bsub>N\<^esub>"
    using M.M.zero_closed N.lmult_0 R.zero_closed f_im f_smult by presburger
  from 1 2 show ?thesis by auto
qed

lemma f_neg [simp]: "v \<in> carrier M\<Longrightarrow>f (\<ominus>\<^bsub>M\<^esub> v) = \<ominus>\<^bsub>N\<^esub> f v"
  by (simp flip: M.smult_minus_1 N.smult_minus_1)

lemma f_minus [simp]: "\<lbrakk>v\<in>carrier M; w\<in>carrier M\<rbrakk>\<Longrightarrow>f (v\<ominus>\<^bsub>M\<^esub>w) = f v \<ominus>\<^bsub>N\<^esub> f w"
  by (simp add: a_minus_def)

lemma ker_is_submodule: "submodule R ker M"
proof - 
  have 0: "mod_hom R M N f"..
  from 0 have 1: "module R M" by (unfold mod_hom_def, auto)
  show ?thesis
    by  (rule submodule.intro, auto simp add: ker_def, rule 1) (*rmult_0*)
qed

lemma im_is_submodule: "submodule R im N"
proof - 
  have 1: "im \<subseteq> carrier N" by (auto simp add: im_def image_def mod_hom_def module_hom_def f_im) 
  have 2: "\<And>w1 w2.\<lbrakk>w1 \<in> im; w2 \<in> im\<rbrakk> \<Longrightarrow> w1 \<oplus>\<^bsub>N\<^esub> w2 \<in> im" (*it can't auto convert \<And> and w/ o*)
  proof -
    fix w1 w2
    assume w1: "w1 \<in> im" and w2: "w2\<in> im"
    from w1 obtain v1 where 3: "v1\<in> carrier M \<and> f v1 = w1" by (unfold im_def, auto)
    from w2 obtain v2 where 4: "v2\<in> carrier M \<and> f v2 = w2" by (unfold im_def, auto)
    from 3 4 have 5: "f (v1\<oplus>\<^bsub>M\<^esub>v2) = w1 \<oplus>\<^bsub>N\<^esub> w2" by simp
    from 3 4 have 6: "v1\<oplus>\<^bsub>M\<^esub>v2\<in> carrier M" by simp
    from 5 6 have 7: "\<exists>x\<in>carrier M. w1 \<oplus>\<^bsub>N\<^esub> w2 = f x" by metis
    from 7 show "?thesis w1 w2" by (unfold im_def image_def, auto)
  qed
  have 3: " \<zero>\<^bsub>N\<^esub> \<in> im"
  proof -
    have 8: "f \<zero>\<^bsub>M\<^esub> = \<zero>\<^bsub>N\<^esub> \<and> \<zero>\<^bsub>M\<^esub>\<in>carrier M" by auto
    from 8 have 9: "\<exists>x\<in>carrier M. \<zero>\<^bsub>N\<^esub> = f x" by metis
    from 9 show ?thesis by (unfold im_def image_def, auto)
  qed
  have 4: "\<And>c w. \<lbrakk>c \<in> carrier R; w \<in> im\<rbrakk> \<Longrightarrow> c\<odot>\<^bsub>N\<^esub> w \<in> im" 
  proof -
    fix c w
    assume c: "c \<in> carrier R" and w: "w \<in> im"
    from w obtain v where 10: "v\<in> carrier M \<and> f v = w" by (unfold im_def, auto)
    from c 10 have 11: "f (c\<odot>\<^bsub>M\<^esub> v) = c\<odot>\<^bsub>N\<^esub> w\<and> (c \<odot>\<^bsub>M\<^esub> v\<in>carrier M)" by auto
    from 11 have 12: "\<exists>v1\<in>carrier M.  c\<odot>\<^bsub>N\<^esub> w=f v1" by metis 
    from 12 show "?thesis c w" by (unfold im_def image_def, auto) (*sensitive to ordering*)
  qed
  from 1 2 3 4 show ?thesis by (unfold_locales, auto)
qed

lemma (in mod_hom) f_ker:
  "v\<in>ker \<Longrightarrow> f v=\<zero>\<^bsub>N\<^esub>"
by (unfold ker_def, auto)
end

text \<open>We will show that for any set $S$, the space of functions $S\to K$ forms a vector space.\<close>
definition (in ring) func_space:: "'z set\<Rightarrow>('a,('z \<Rightarrow> 'a)) module"
  where "func_space S = \<lparr>carrier = S\<rightarrow>\<^sub>Ecarrier R, 
                  mult = (\<lambda> f g. restrict (\<lambda>v. \<zero>\<^bsub>R\<^esub>) S),
                  one =  restrict (\<lambda>v. \<zero>\<^bsub>R\<^esub>) S,
                  zero = restrict (\<lambda>v. \<zero>\<^bsub>R\<^esub>) S,
                  add = (\<lambda> f g. restrict (\<lambda>v. f v \<oplus>\<^bsub>R\<^esub> g v) S),
                  smult = (\<lambda> c f. restrict (\<lambda>v. c \<otimes>\<^bsub>R\<^esub> f v) S)\<rparr>"

lemma (in cring) func_space_is_module:
  fixes S
  shows "module R (func_space S)" 
proof -
have 0: "cring R"..
from 0 show ?thesis
  apply (auto intro!: module_criteria simp add: func_space_def)
           apply (auto simp add: module_def)
         apply (rename_tac f)
         apply (rule_tac x="restrict (\<lambda>v'. \<ominus>\<^bsub>R\<^esub> (f v')) S" in bexI)
          apply (auto simp add:restrict_def cong: if_cong split: if_split_asm, auto)
         apply (auto simp add: a_ac PiE_mem2 r_neg) (*intro: ext*)
      apply (unfold PiE_def extensional_def Pi_def)
      by (auto simp add: m_assoc l_distr r_distr)
qed

text \<open>Note: one can define $M^n$ from this.\<close>

text \<open>A linear combination is a module homomorphism from the space of coefficients to the module,
 $(a_v)\mapsto \sum_{v\in S} a_vv$.\<close>
lemma (in module) lincomb_is_mod_hom:
  fixes S
  assumes h: "finite S" and h2: "S\<subseteq>carrier M"
  shows "mod_hom R (func_space S) M (\<lambda>a. lincomb a S)" 
proof -
  have 0: "module R M"..
  { 
    fix m1 m2
    assume m1: "m1 \<in> S \<rightarrow>\<^sub>E carrier R" and m2: "m2 \<in> S \<rightarrow>\<^sub>E carrier R"
    from h h2 m1 m2 have a1: "(\<Oplus>\<^bsub>M\<^esub>v\<in>S. (\<lambda>v\<in>S. m1 v \<oplus>\<^bsub>R\<^esub> m2 v) v \<odot>\<^bsub>M\<^esub> v) = 
      (\<Oplus>\<^bsub>M\<^esub>v\<in>S. m1 v \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> m2 v \<odot>\<^bsub>M\<^esub> v)"
      by (intro finsum_cong', auto simp add: smult_l_distr PiE_mem2)
    from h h2 m1 m2 have a2: "(\<Oplus>\<^bsub>M\<^esub>v\<in>S. m1 v \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> m2 v \<odot>\<^bsub>M\<^esub> v) = 
      (\<Oplus>\<^bsub>M\<^esub>v\<in>S. m1 v \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>v\<in>S. m2 v \<odot>\<^bsub>M\<^esub> v)"
      by (intro finsum_addf, auto)
    from a1 a2 have "(\<Oplus>\<^bsub>M\<^esub>v\<in>S. (\<lambda>v\<in>S. m1 v \<oplus> m2 v) v \<odot>\<^bsub>M\<^esub> v) =
       (\<Oplus>\<^bsub>M\<^esub>v\<in>S. m1 v \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>v\<in>S. m2 v \<odot>\<^bsub>M\<^esub> v)" by auto
  }
  hence 1: "\<And>m1 m2.
       m1 \<in> S \<rightarrow>\<^sub>E carrier R \<Longrightarrow>
       m2 \<in> S \<rightarrow>\<^sub>E carrier R \<Longrightarrow> (\<Oplus>\<^bsub>M\<^esub>v\<in>S. (\<lambda>v\<in>S. m1 v \<oplus> m2 v) v \<odot>\<^bsub>M\<^esub> v) =
       (\<Oplus>\<^bsub>M\<^esub>v\<in>S. m1 v \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>v\<in>S. m2 v \<odot>\<^bsub>M\<^esub> v)" by auto
  { 
    fix r m
    assume r: "r \<in> carrier R" and m: "m \<in> S \<rightarrow>\<^sub>E carrier R"
    from h h2 r m have b1: "r \<odot>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>v\<in>S. m v \<odot>\<^bsub>M\<^esub> v) =  (\<Oplus>\<^bsub>M\<^esub>v\<in>S. r \<odot>\<^bsub>M\<^esub>(m v \<odot>\<^bsub>M\<^esub> v))"
      by (intro finsum_smult, auto) 
    from h h2 r m have b2: "(\<Oplus>\<^bsub>M\<^esub>v\<in>S. (\<lambda>v\<in>S. r \<otimes> m v) v \<odot>\<^bsub>M\<^esub> v) = r \<odot>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>v\<in>S. m v \<odot>\<^bsub>M\<^esub> v)"
      apply (subst b1)
      apply (intro finsum_cong', auto)
      by (subst smult_assoc1, auto)
  }
  hence 2: "\<And>r m. r \<in> carrier R \<Longrightarrow>
           m \<in> S \<rightarrow>\<^sub>E carrier R \<Longrightarrow> (\<Oplus>\<^bsub>M\<^esub>v\<in>S. (\<lambda>v\<in>S. r \<otimes> m v) v \<odot>\<^bsub>M\<^esub> v) = r \<odot>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>v\<in>S. m v \<odot>\<^bsub>M\<^esub> v)" 
            by auto
  from h h2 0 1 2 show ?thesis
    apply (unfold mod_hom_def, auto)
     apply (rule func_space_is_module)
    apply (unfold mod_hom_axioms_def module_hom_def, auto)
      apply (rule lincomb_closed, unfold func_space_def, auto)
     apply (unfold lincomb_def)
     by auto
qed

(*These are not really used.*)
lemma (in module) lincomb_sum:
  assumes A_fin: "finite A" and AinC: "A\<subseteq>carrier M" and a_fun: "a\<in>A\<rightarrow>carrier R" and 
    b_fun: "b\<in>A\<rightarrow>carrier R" 
  shows "lincomb (\<lambda>v. a v \<oplus>\<^bsub>R\<^esub> b v) A = lincomb a A \<oplus>\<^bsub>M\<^esub> lincomb b A"
proof - 
  from A_fin AinC interpret mh: mod_hom R "func_space A" M  "(\<lambda>a. lincomb a A)" by (rule 
    lincomb_is_mod_hom)
  let ?a="restrict a A"
  let ?b="restrict b A"
  from a_fun b_fun A_fin AinC
  have 1: "LinearCombinations.module.lincomb M (?a\<oplus>\<^bsub>(LinearCombinations.ring.func_space R A)\<^esub> ?b) A
    = LinearCombinations.module.lincomb M (\<lambda>x.  a x \<oplus>\<^bsub>R\<^esub> b x) A"
    by (auto simp add: func_space_def Pi_iff restrict_apply' cong: lincomb_cong)
  from a_fun b_fun A_fin AinC
  have 2: "LinearCombinations.module.lincomb M ?a A \<oplus>\<^bsub>M\<^esub> 
      LinearCombinations.module.lincomb M ?b A = LinearCombinations.module.lincomb M a A \<oplus>\<^bsub>M\<^esub> 
      LinearCombinations.module.lincomb M b A"
    by (simp_all add: sum_simp cong: lincomb_cong)
  from a_fun b_fun have ainC: "?a\<in>carrier (LinearCombinations.ring.func_space R A)" 
    and binC: "?b\<in>carrier (LinearCombinations.ring.func_space R A)" by (unfold func_space_def, auto)
  from ainC binC have "LinearCombinations.module.lincomb M (?a\<oplus>\<^bsub>(LinearCombinations.ring.func_space R A)\<^esub> ?b) A
    = LinearCombinations.module.lincomb M ?a A \<oplus>\<^bsub>M\<^esub> 
      LinearCombinations.module.lincomb M ?b A"  
    by (simp cong: lincomb_cong)
  with 1 2 show ?thesis by auto
qed

text \<open>The negative of a function is just pointwise negation.\<close>
lemma (in cring) func_space_neg: 
  fixes f
  assumes "f\<in> carrier (func_space S)"
  shows "\<ominus>\<^bsub>func_space S\<^esub> f = (\<lambda> v. if (v\<in>S) then \<ominus>\<^bsub>R\<^esub> f v else undefined)"
proof - 
  interpret fs: module R "func_space S" by (rule func_space_is_module)
  from assms show ?thesis
    apply (intro fs.minus_equality)
      apply (unfold func_space_def PiE_def extensional_def)
      apply auto
     apply (intro restrict_ext, auto)
    by (simp add: l_neg coeff_in_ring)
qed

text \<open>Ditto for subtraction. Note the above is really a special case, when a is the 0 function.\<close>
lemma (in module) lincomb_diff:
  assumes A_fin: "finite A" and AinC: "A\<subseteq>carrier M" and a_fun: "a\<in>A\<rightarrow>carrier R" and 
    b_fun: "b\<in>A\<rightarrow>carrier R" 
  shows "lincomb (\<lambda>v. a v \<ominus>\<^bsub>R\<^esub> b v) A = lincomb a A \<ominus>\<^bsub>M\<^esub> lincomb b A"
proof - 
  from A_fin AinC interpret mh: mod_hom R "func_space A" M  "(\<lambda>a. lincomb a A)" by (rule 
    lincomb_is_mod_hom)
  let ?a="restrict a A"
  let ?b="restrict b A"
  from a_fun b_fun have ainC: "?a\<in>carrier (LinearCombinations.ring.func_space R A)" 
    and binC: "?b\<in>carrier (LinearCombinations.ring.func_space R A)" by (unfold func_space_def, auto)
  from a_fun b_fun ainC binC A_fin AinC
  have 1: "LinearCombinations.module.lincomb M (?a\<ominus>\<^bsub>(func_space A)\<^esub> ?b) A
    = LinearCombinations.module.lincomb M (\<lambda>x.  a x \<ominus>\<^bsub>R\<^esub> b x) A"
    apply (subst mh.M.M.minus_eq)
    apply (intro lincomb_cong, auto)
    apply (subst func_space_neg, auto)
    apply (simp add: restrict_def func_space_def)
    by (subst R.minus_eq, auto)
  from a_fun b_fun A_fin AinC
  have 2: "LinearCombinations.module.lincomb M ?a A \<ominus>\<^bsub>M\<^esub> 
      LinearCombinations.module.lincomb M ?b A = LinearCombinations.module.lincomb M a A \<ominus>\<^bsub>M\<^esub> 
      LinearCombinations.module.lincomb M b A"
    by (simp cong: lincomb_cong)
  from ainC binC have "LinearCombinations.module.lincomb M (?a\<ominus>\<^bsub>(LinearCombinations.ring.func_space R A)\<^esub> ?b) A
    = LinearCombinations.module.lincomb M ?a A \<ominus>\<^bsub>M\<^esub> 
      LinearCombinations.module.lincomb M ?b A"  
    by (simp cong: lincomb_cong)
  with 1 2 show ?thesis by auto
qed

text \<open>The union of nested submodules is a submodule. We will use this to show that span of any
set is a submodule.\<close>
lemma (in module) nested_union_vs: 
  fixes I N N'
  assumes subm: "\<And>i. i\<in>I\<Longrightarrow> submodule R (N i) M"
    and max_exists: "\<And>i j. i\<in>I\<Longrightarrow>j\<in>I\<Longrightarrow> (\<exists>k. k\<in>I \<and> N i\<subseteq>N k \<and> N j \<subseteq>N k)" 
    and uni: "N'=(\<Union> i\<in>I. N i)"
    and ne: "I\<noteq>{}"
  shows "submodule R N' M"
proof -
  have 1: "module R M"..
  from subm have all_in: "\<And>i. i\<in>I \<Longrightarrow> N i \<subseteq> carrier M"
    by (unfold submodule_def, auto)
  from uni all_in have 2: "\<And>x. x \<in> N' \<Longrightarrow> x \<in> carrier M"
    by auto
  from uni have 3: "\<And>v w. v \<in> N' \<Longrightarrow> w \<in> N' \<Longrightarrow> v \<oplus>\<^bsub>M\<^esub> w \<in> N'"
  proof - 
    fix v w
    assume v: "v \<in> N'" and w: "w \<in> N'"
    from uni v w obtain i j where i: "i\<in>I\<and> v\<in> N i" and j: "j\<in>I\<and> w\<in> N j" by auto
    from max_exists i j obtain k where k: "k\<in>I \<and> N i \<subseteq> N k \<and> N j \<subseteq> N k" by presburger
    from v w i j k have v2: "v\<in>N k" and w2: "w\<in> N k" by auto
    from v2 w2 k subm[of k] have vw: "v \<oplus>\<^bsub>M\<^esub> w \<in> N k" apply (unfold submodule_def) by auto
    from k vw uni show "?thesis v w"  by auto
  qed
  have 4: "\<zero>\<^bsub>M\<^esub> \<in> N'"
  proof - 
    from ne obtain i where i: "i\<in>I" by auto
    from i subm have zi: "\<zero>\<^bsub>M\<^esub>\<in>N i" by (unfold submodule_def, auto)
    from i zi uni show ?thesis by auto
  qed
  from uni subm have 5: "\<And>c v. c \<in> carrier R \<Longrightarrow> v \<in> N' \<Longrightarrow> c \<odot>\<^bsub>M\<^esub> v \<in> N'"
    by (unfold submodule_def, auto)
  from 1 2 3 4 5 show ?thesis by (unfold submodule_def, auto)
qed

lemma (in module) span_is_monotone:
  fixes S T
  assumes subs: "S\<subseteq>T"
  shows "span S \<subseteq> span T"
proof -
  from subs show ?thesis 
    by (unfold span_def, auto)
qed


lemma (in module) span_is_submodule:
  fixes S
  assumes  h2: "S\<subseteq>carrier M"
  shows "submodule R (span S) M"
proof (cases "S={}")
  case True
  moreover have "module R M"..
  ultimately show ?thesis apply (unfold submodule_def span_def lincomb_def, auto) done
next 
  case False
  show ?thesis
  proof (rule nested_union_vs[where ?I="{F. F\<subseteq>S \<and> finite F}" and ?N="\<lambda>F. span F" and ?N'="span S"])
    show " \<And>F. F \<in> {F. F \<subseteq> S \<and> finite F} \<Longrightarrow> submodule R (span F) M"
    proof - 
      fix F
      assume F: "F \<in> {F. F \<subseteq> S \<and> finite F}"
      from F have h1: "finite F" by auto
      from F h2 have inC: "F\<subseteq>carrier M" by auto
      from h1 inC interpret mh: mod_hom R "(func_space F)" M "(\<lambda>a. lincomb a F)" 
        by (rule lincomb_is_mod_hom)
      from h1 inC have 1: "mh.im = span F" 
        apply (unfold mh.im_def) 
        apply (unfold func_space_def, simp) 
        apply (subst finite_span, auto)
        apply (unfold image_def, auto)
        apply (rule_tac x="restrict a F" in bexI)
         by (auto intro!: lincomb_cong)
      from 1 show "submodule R (span F) M" by (metis mh.im_is_submodule)
    qed
  next 
    show "\<And>i j. i \<in> {F. F \<subseteq> S \<and> finite F} \<Longrightarrow>
           j \<in> {F. F \<subseteq> S \<and> finite F} \<Longrightarrow>
           \<exists>k. k \<in> {F. F \<subseteq> S \<and> finite F} \<and> span i \<subseteq> span k \<and> span j \<subseteq> span k"
    proof -
      fix i j 
      assume i: "i \<in> {F. F \<subseteq> S \<and> finite F}" and j: "j \<in> {F. F \<subseteq> S \<and> finite F}"
      from i j show "?thesis i j"
        apply (rule_tac x="i\<union>j" in exI)
        apply (auto del: subsetI)
         by (intro span_is_monotone, auto del: subsetI)+
    qed
  next
    show "span S=(\<Union> i\<in>{F. F \<subseteq> S \<and> finite F}. span i)"
      by (unfold span_def,auto)
  next 
    have ne: "S\<noteq>{}" by fact
    from ne show "{F. F \<subseteq> S \<and> finite F} \<noteq> {}" by auto
  qed
qed

text \<open>A finite sum does not depend on the ambient module. This can be done for monoid, but 
"submonoid" isn't currently defined. (It can be copied, however, for groups\ldots)
This lemma requires a somewhat annoying lemma foldD-not-depend. Then we show that linear combinations, 
linear independence, span do not depend on the ambient module.\<close>
lemma (in module) finsum_not_depend:
  fixes a A N
  assumes h1: "finite A" and h2: "A\<subseteq>N" and h3: "submodule R N M" and h4: "f:A\<rightarrow>N"
  shows "(\<Oplus>\<^bsub>(md N)\<^esub> v\<in>A. f v) = (\<Oplus>\<^bsub>M\<^esub> v\<in>A. f v)"
proof -
  from h1 h2 h3 h4 show ?thesis
    apply (unfold finsum_def finprod_def)
    apply simp
    apply (intro foldD_not_depend[where ?B="A"])
         apply (unfold submodule_def LCD_def, auto)
    apply (meson M.add.m_lcomm PiE subsetCE)+
    done
qed

lemma (in module) lincomb_not_depend:
  fixes a A N
  assumes h1: "finite A" and h2: "A\<subseteq>N" and h3: "submodule R N M" and h4: "a:A\<rightarrow>carrier R"
  shows "lincomb a A = module.lincomb (md N) a A"
proof - 
  from h3 interpret N: module R "(md N)" by (rule submodule_is_module)
  have 3: "N=carrier (md N)" by auto
  have 4: "(smult M ) = (smult (md N))" by auto 
  from h1 h2 h3 h4 have "(\<Oplus>\<^bsub>(md N)\<^esub>v\<in>A. a v \<odot>\<^bsub>M\<^esub> v) = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. a v \<odot>\<^bsub>M\<^esub> v)"
    apply (intro finsum_not_depend)
    using N.summands_valid by auto
  from this show ?thesis by (unfold lincomb_def N.lincomb_def, simp)
qed

lemma (in module) span_li_not_depend:
  fixes S N
  assumes h2: "S\<subseteq>N" and  h3: "submodule R N M"
  shows "module.span R (md N) S = module.span R M S"
    and "module.lin_dep R (md N) S = module.lin_dep R M S"
proof -
  from h3 interpret w: module R "(md N)" by (rule submodule_is_module)
  from h2 have 1:"submodule R (module.span R (md N) S) (md N)" 
    by (intro w.span_is_submodule, simp)
  have 3: "\<And>a A. (finite A \<and> A\<subseteq>S \<and> a \<in> A \<rightarrow> carrier R \<Longrightarrow> 
    module.lincomb M a A = module.lincomb (md N) a A)"
  proof - 
    fix a A
    assume 31: "finite A \<and> A\<subseteq>S \<and> a \<in> A \<rightarrow> carrier R"
    from assms 31 show "?thesis a A"
      by (intro lincomb_not_depend, auto)
  qed
  from 3 show 4: "module.span R (md N) S = module.span R M S"
    apply (unfold span_def w.span_def)
    apply auto
    by (metis)
  have zeros: "\<zero>\<^bsub>md N\<^esub>=\<zero>\<^bsub>M\<^esub>" by auto
  from assms 3 show 5: "module.lin_dep R (md N) S = module.lin_dep R M S"
    apply (unfold lin_dep_def w.lin_dep_def)
    apply (subst zeros) 
    by metis
qed

lemma (in module) span_is_subset: 
  fixes S N
  assumes h2: "S\<subseteq>N" and  h3: "submodule R N M"
  shows "span S \<subseteq> N"
proof -  
  from h3 interpret w: module R "(md N)" by (rule submodule_is_module)
  from h2 have 1:"submodule R (module.span R (md N) S) (md N)" 
    by (intro w.span_is_submodule, simp)
  from assms have 4: "module.span R (md N) S = module.span R M S"
     by (rule span_li_not_depend)
  from 1 4 have 5: "submodule R (module.span R M S) (md N)" by auto
  from 5 show ?thesis by (unfold submodule_def, simp)
qed


lemma (in module) span_is_subset2:
  fixes S
  assumes h2: "S\<subseteq>carrier M"
  shows "span S \<subseteq> carrier M"
proof - 
  have 0: "module R M"..
  from 0 have h3: "submodule R (carrier M) M" by (unfold submodule_def, auto)
  from h2 h3 show ?thesis by (rule span_is_subset)
qed

lemma (in module) in_own_span: 
  fixes S
  assumes  inC:"S\<subseteq>carrier M"
  shows "S \<subseteq> span S"
proof - 
  from inC show ?thesis 
    apply (unfold span_def, auto)
    apply (rename_tac v)
    apply (rule_tac x="(\<lambda> w. if (w=v) then \<one>\<^bsub>R\<^esub> else \<zero>\<^bsub>R\<^esub>)" in exI)
    apply (rule_tac x="{v}" in exI)
    apply (unfold lincomb_def)
    by auto 
qed

lemma (in module) supset_ld_is_ld:
  fixes A B
  assumes ld: "lin_dep A" and sub: "A \<subseteq> B"
  shows "lin_dep B"
proof - 
  from ld obtain A' a v where 1: "(finite A' \<and> A'\<subseteq>A \<and> (a\<in> (A'\<rightarrow>carrier R)) \<and> (lincomb a A' = \<zero>\<^bsub>M\<^esub>) \<and> (v\<in>A') \<and> (a v\<noteq> \<zero>\<^bsub>R\<^esub>))"
    by (unfold lin_dep_def, auto)
  from 1 sub show ?thesis 
    apply (unfold lin_dep_def)
    apply (rule_tac x="A'" in exI)
    apply (rule_tac x="a" in exI)
    apply (rule_tac x="v" in exI)
    by auto
qed

lemma (in module) subset_li_is_li:
  fixes A B
  assumes li: "lin_indpt A" and sub: "B \<subseteq> A" 
  shows "lin_indpt B"
proof (rule ccontr)
  assume ld: "\<not>lin_indpt B"
  from ld sub have ldA: "lin_dep A" by (metis supset_ld_is_ld)
  from li ldA show False by auto
qed

lemma (in mod_hom) hom_sum:
  fixes A B g
  assumes h2: "A\<subseteq>carrier M" and h3: "g:A\<rightarrow>carrier M"
  shows "f (\<Oplus>\<^bsub>M\<^esub> a\<in>A. g a) = (\<Oplus>\<^bsub>N\<^esub> a\<in>A. f (g a))"
proof -   
  from h2 h3 show ?thesis
  proof (induct A rule: infinite_finite_induct) (*doesn't work on outside?*)
    case (insert a A)
    then have "(\<Oplus>\<^bsub>N\<^esub>a\<in>insert a A. f (g a)) = f (g a) \<oplus>\<^bsub>N\<^esub> (\<Oplus>\<^bsub>N\<^esub>a\<in>A. f (g a))"  
      by (intro finsum_insert, auto)
    with insert.prems insert.hyps show ?case
      by simp
  qed auto
qed


end
