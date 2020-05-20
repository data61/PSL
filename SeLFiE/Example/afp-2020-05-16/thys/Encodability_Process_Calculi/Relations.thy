theory Relations
  imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar"
begin

section \<open>Relations\<close>

subsection \<open>Basic Conditions\<close>

text \<open>We recall the standard definitions for reflexivity, symmetry, transitivity, preoders,
        equivalence, and inverse relations.\<close>

abbreviation "preorder Rel \<equiv> preorder_on UNIV Rel"
abbreviation "equivalence Rel \<equiv> equiv UNIV Rel"

text \<open>A symmetric preorder is an equivalence.\<close>

lemma symm_preorder_is_equivalence:
  fixes Rel :: "('a \<times> 'a) set"
  assumes "preorder Rel"
      and "sym Rel"
  shows "equivalence Rel"
      using assms
      unfolding preorder_on_def equiv_def
    by simp

text \<open>The symmetric closure of a relation is the union of this relation and its inverse.\<close>

definition symcl :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" where
  "symcl Rel = Rel \<union> Rel\<inverse>"

text \<open>For all (a, b) in R, the symmetric closure of R contains (a, b) as well as (b, a).\<close>

lemma elem_of_symcl:
  fixes Rel :: "('a \<times> 'a) set"
    and a b :: "'a"
  assumes elem: "(a, b) \<in> Rel"
  shows "(a, b) \<in> symcl Rel"
    and "(b, a) \<in> symcl Rel"
    by (auto simp add: elem symcl_def)

text \<open>The symmetric closure of a relation is symmetric.\<close>

lemma sym_symcl:
  fixes Rel :: "('a \<times> 'a) set"
  shows "sym (symcl Rel)"
    by (simp add: symcl_def sym_Un_converse)

text \<open>The reflexive and symmetric closure of a relation is equal to its symmetric and reflexive
        closure.\<close>

lemma refl_symm_closure_is_symm_refl_closure:
  fixes Rel :: "('a \<times> 'a) set"
  shows "symcl (Rel\<^sup>=) = (symcl Rel)\<^sup>="
    by (auto simp add: symcl_def refl)

text \<open>The symmetric closure of a reflexive relation is reflexive.\<close>

lemma refl_symcl_of_refl_rel:
  fixes Rel :: "('a \<times> 'a) set"
    and A   :: "'a set"
  assumes "refl_on A Rel"
  shows "refl_on A (symcl Rel)"
      using assms
    by (auto simp add: refl_on_def' symcl_def)

text \<open>Accordingly, the reflexive, symmetric, and transitive closure of a relation is equal to its
        symmetric, reflexive, and transitive closure.\<close>

lemma refl_symm_trans_closure_is_symm_refl_trans_closure:
  fixes Rel :: "('a \<times> 'a) set"
  shows "(symcl (Rel\<^sup>=))\<^sup>+ = (symcl Rel)\<^sup>*"
      using refl_symm_closure_is_symm_refl_closure[where Rel="Rel"]
    by simp

text \<open>The reflexive closure of a symmetric relation is symmetric.\<close>

lemma sym_reflcl_of_symm_rel:
  fixes Rel :: "('a \<times> 'a) set"
  assumes "sym Rel"
  shows "sym (Rel\<^sup>=)"
      using assms
    by (simp add: sym_Id sym_Un)

text \<open>The reflexive closure of a reflexive relation is the relation itself.\<close>

lemma reflcl_of_refl_rel:
  fixes Rel :: "('a \<times> 'a) set"
  assumes "refl Rel"
  shows "Rel\<^sup>= = Rel"
      using assms
      unfolding refl_on_def
    by auto

text \<open>The symmetric closure of a symmetric relation is the relation itself.\<close>

lemma symm_closure_of_symm_rel:
  fixes Rel :: "('a \<times> 'a) set"
  assumes "sym Rel"
  shows "symcl Rel = Rel"
      using assms
      unfolding symcl_def sym_def
    by auto

text \<open>The reflexive and transitive closure of a preorder Rel is Rel.\<close>

lemma rtrancl_of_preorder:
  fixes Rel :: "('a \<times> 'a) set"
  assumes "preorder Rel"
  shows "Rel\<^sup>* = Rel"
      using assms reflcl_of_refl_rel[of Rel] trancl_id[of "Rel\<^sup>="] trancl_reflcl[of Rel]
      unfolding preorder_on_def
    by auto

text \<open>The reflexive and transitive closure of a relation is a subset of its reflexive, symmetric,
        and transtive closure.\<close>

lemma refl_trans_closure_subset_of_refl_symm_trans_closure:
  fixes Rel :: "('a \<times> 'a) set"
  shows "Rel\<^sup>* \<subseteq> (symcl (Rel\<^sup>=))\<^sup>+"
proof clarify
  fix a b
  assume "(a, b) \<in> Rel\<^sup>*"
  hence "(a, b) \<in> (symcl Rel)\<^sup>*"
      using in_rtrancl_UnI[of "(a, b)" "Rel" "Rel\<inverse>"]
    by (simp add: symcl_def)
  thus "(a, b) \<in> (symcl (Rel\<^sup>=))\<^sup>+"
      using refl_symm_trans_closure_is_symm_refl_trans_closure[of Rel]
    by simp
qed

text \<open>If a preorder Rel satisfies the following two conditions, then its symmetric closure is
        transitive:
        (1) If (a, b) and (c, b) in Rel but not (a, c) in Rel, then (b, a) in Rel or (b, c) in Rel.
        (2) If (a, b) and (a, c) in Rel but not (b, c) in Rel, then (b, a) in Rel or (c, a) in Rel.
\<close>

lemma symm_closure_of_preorder_is_trans:
  fixes Rel :: "('a \<times> 'a) set"
  assumes condA: "\<forall>a b c. (a, b) \<in> Rel \<and> (c, b) \<in> Rel \<and> (a, c) \<notin> Rel
                  \<longrightarrow> (b, a) \<in> Rel \<or> (b, c) \<in> Rel"
      and condB: "\<forall>a b c. (a, b) \<in> Rel \<and> (a, c) \<in> Rel \<and> (b, c) \<notin> Rel
                  \<longrightarrow> (b, a) \<in> Rel \<or> (c, a) \<in> Rel"
      and reflR: "refl Rel"
      and tranR: "trans Rel"
  shows "trans (symcl Rel)"
    unfolding trans_def
proof clarify
  fix a b c
  have "\<lbrakk>(a, b) \<in> Rel; (b, c) \<in> Rel\<rbrakk> \<Longrightarrow> (a, c) \<in> symcl Rel"
  proof -
    assume "(a, b) \<in> Rel" and "(b, c) \<in> Rel"
    with tranR have "(a, c) \<in> Rel"
        unfolding trans_def
      by blast
    thus "(a, c) \<in> symcl Rel"
      by (simp add: symcl_def)
  qed
  moreover have "\<lbrakk>(a, b) \<in> Rel; (c, b) \<in> Rel; (a, c) \<notin> Rel\<rbrakk> \<Longrightarrow> (a, c) \<in> symcl Rel"
  proof -
    assume A1: "(a, b) \<in> Rel" and A2: "(c, b) \<in> Rel" and "(a, c) \<notin> Rel"
    with condA have "(b, a) \<in> Rel \<or> (b, c) \<in> Rel"
      by blast
    thus "(a, c) \<in> symcl Rel"
    proof auto
      assume "(b, a) \<in> Rel"
      with A2 tranR have "(c, a) \<in> Rel"
          unfolding trans_def
        by blast
      thus "(a, c) \<in> symcl Rel"
        by (simp add: symcl_def)
    next
      assume "(b, c) \<in> Rel"
      with A1 tranR have "(a, c) \<in> Rel"
          unfolding trans_def
        by blast
      thus "(a, c) \<in> symcl Rel"
        by (simp add: symcl_def)
    qed
  qed
  moreover have "\<lbrakk>(b, a) \<in> Rel; (b, c) \<in> Rel; (a, c) \<notin> Rel\<rbrakk> \<Longrightarrow> (a, c) \<in> symcl Rel"
  proof -
    assume B1: "(b, a) \<in> Rel" and B2: "(b, c) \<in> Rel" and "(a, c) \<notin> Rel"
    with condB have "(a, b) \<in> Rel \<or> (c, b) \<in> Rel"
      by blast
    thus "(a, c) \<in> symcl Rel"
    proof auto
      assume "(a, b) \<in> Rel"
      with B2 tranR have "(a, c) \<in> Rel"
          unfolding trans_def
        by blast
      thus "(a, c) \<in> symcl Rel"
        by (simp add: symcl_def)
    next
      assume "(c, b) \<in> Rel"
      with B1 tranR have "(c, a) \<in> Rel"
          unfolding trans_def
        by blast
      thus "(a, c) \<in> symcl Rel"
        by (simp add: symcl_def)
    qed
  qed
  moreover have "\<lbrakk>(b, a) \<in> Rel; (c, b) \<in> Rel\<rbrakk> \<Longrightarrow> (a, c) \<in> symcl Rel"
  proof -
    assume "(c, b) \<in> Rel" and "(b, a) \<in> Rel"
    with tranR have "(c, a) \<in> Rel"
        unfolding trans_def
      by blast
    thus "(a, c) \<in> symcl Rel"
      by (simp add: symcl_def)
  qed
  moreover assume "(a, b) \<in> symcl Rel" and "(b, c) \<in> symcl Rel"
  ultimately show "(a, c) \<in> symcl Rel"
    by (auto simp add: symcl_def)
qed

subsection \<open>Preservation, Reflection, and Respection of Predicates\<close>

text \<open>A relation R preserves some predicate P if P(a) implies P(b) for all (a, b) in R.\<close>

abbreviation rel_preserves_pred :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_preserves_pred Rel Pred \<equiv> \<forall>a b. (a, b) \<in> Rel \<and> Pred a \<longrightarrow> Pred b"

abbreviation rel_preserves_binary_pred :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_preserves_binary_pred Rel Pred \<equiv> \<forall>a b x. (a, b) \<in> Rel \<and> Pred a x \<longrightarrow> Pred b x"

text \<open>A relation R reflects some predicate P if P(b) implies P(a) for all (a, b) in R.\<close>

abbreviation rel_reflects_pred :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_reflects_pred Rel Pred \<equiv> \<forall>a b. (a, b) \<in> Rel \<and> Pred b \<longrightarrow> Pred a"

abbreviation rel_reflects_binary_pred :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_reflects_binary_pred Rel Pred \<equiv> \<forall>a b x. (a, b) \<in> Rel \<and> Pred b x \<longrightarrow> Pred a x"

text \<open>A relation respects a predicate if it preserves and reflects it.\<close>

abbreviation rel_respects_pred :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_respects_pred Rel Pred \<equiv> rel_preserves_pred Rel Pred \<and> rel_reflects_pred Rel Pred"

abbreviation rel_respects_binary_pred :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_respects_binary_pred Rel Pred \<equiv>
   rel_preserves_binary_pred Rel Pred \<and> rel_reflects_binary_pred Rel Pred"

text \<open>For symmetric relations preservation, reflection, and respection of predicates means the
        same.\<close>

lemma symm_relation_impl_preservation_equals_reflection:
  fixes Rel  :: "('a \<times> 'a) set"
    and Pred :: "'a \<Rightarrow> bool"
  assumes symm: "sym Rel"
  shows "rel_preserves_pred Rel Pred = rel_reflects_pred Rel Pred"
    and "rel_preserves_pred Rel Pred = rel_respects_pred Rel Pred"
    and "rel_reflects_pred Rel Pred = rel_respects_pred Rel Pred"
      using symm
      unfolding sym_def
    by blast+

lemma symm_relation_impl_preservation_equals_reflection_of_binary_predicates:
  fixes Rel  :: "('a \<times> 'a) set"
    and Pred :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes symm: "sym Rel"
  shows "rel_preserves_binary_pred Rel Pred = rel_reflects_binary_pred Rel Pred"
    and "rel_preserves_binary_pred Rel Pred = rel_respects_binary_pred Rel Pred"
    and "rel_reflects_binary_pred Rel Pred = rel_respects_binary_pred Rel Pred"
      using symm
      unfolding sym_def
    by blast+

text \<open>If a relation preserves a predicate then so does its reflexive or/and transitive closure.
\<close>

lemma preservation_and_closures:
  fixes Rel  :: "('a \<times> 'a) set"
    and Pred :: "'a \<Rightarrow> bool"
  assumes preservation: "rel_preserves_pred Rel Pred"
  shows "rel_preserves_pred (Rel\<^sup>=) Pred"
    and "rel_preserves_pred (Rel\<^sup>+) Pred"
    and "rel_preserves_pred (Rel\<^sup>*) Pred"
proof -
  from preservation show A: "rel_preserves_pred (Rel\<^sup>=) Pred"
    by (auto simp add: refl)
  have B: "\<And>Rel. rel_preserves_pred Rel Pred \<Longrightarrow> rel_preserves_pred (Rel\<^sup>+) Pred"
  proof clarify
    fix Rel a b
    assume "(a, b) \<in> Rel\<^sup>+" and "rel_preserves_pred Rel Pred" and "Pred a"
    thus "Pred b"
      by (induct, blast+)
  qed
  with preservation show "rel_preserves_pred (Rel\<^sup>+) Pred"
    by blast
  from preservation A B[where Rel="Rel\<^sup>="] show "rel_preserves_pred (Rel\<^sup>*) Pred"
      using trancl_reflcl[of Rel]
    by blast
qed

lemma preservation_of_binary_predicates_and_closures:
  fixes Rel  :: "('a \<times> 'a) set"
    and Pred :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes preservation: "rel_preserves_binary_pred Rel Pred"
  shows "rel_preserves_binary_pred (Rel\<^sup>=) Pred"
    and "rel_preserves_binary_pred (Rel\<^sup>+) Pred"
    and "rel_preserves_binary_pred (Rel\<^sup>*) Pred"
proof -
  from preservation show A: "rel_preserves_binary_pred (Rel\<^sup>=) Pred"
    by (auto simp add: refl)
  have B: "\<And>Rel. rel_preserves_binary_pred Rel Pred
           \<Longrightarrow> rel_preserves_binary_pred (Rel\<^sup>+) Pred"
  proof clarify
    fix Rel a b x
    assume "(a, b) \<in> Rel\<^sup>+" and "rel_preserves_binary_pred Rel Pred" and "Pred a x"
    thus "Pred b x"
      by (induct, blast+)
  qed
  with preservation show "rel_preserves_binary_pred (Rel\<^sup>+) Pred"
    by blast
  from preservation A B[where Rel="Rel\<^sup>="]
  show "rel_preserves_binary_pred (Rel\<^sup>*) Pred"
      using trancl_reflcl[of Rel]
    by fast
qed

text \<open>If a relation reflects a predicate then so does its reflexive or/and transitive closure.\<close>

lemma reflection_and_closures:
  fixes Rel  :: "('a \<times> 'a) set"
    and Pred :: "'a \<Rightarrow> bool"
  assumes reflection: "rel_reflects_pred Rel Pred"
  shows "rel_reflects_pred (Rel\<^sup>=) Pred"
    and "rel_reflects_pred (Rel\<^sup>+) Pred"
    and "rel_reflects_pred (Rel\<^sup>*) Pred"
proof -
  from reflection show A: "rel_reflects_pred (Rel\<^sup>=) Pred"
    by (auto simp add: refl)
  have B: "\<And>Rel. rel_reflects_pred Rel Pred \<Longrightarrow> rel_reflects_pred (Rel\<^sup>+) Pred"
  proof clarify
    fix Rel a b
    assume "(a, b) \<in> Rel\<^sup>+" and "rel_reflects_pred Rel Pred" and "Pred b"
    thus "Pred a"
      by (induct, blast+)
  qed
  with reflection show "rel_reflects_pred (Rel\<^sup>+) Pred"
    by blast
  from reflection A B[where Rel="Rel\<^sup>="] show "rel_reflects_pred (Rel\<^sup>*) Pred"
      using trancl_reflcl[of Rel]
    by fast
qed

lemma reflection_of_binary_predicates_and_closures:
  fixes Rel  :: "('a \<times> 'a) set"
    and Pred :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes reflection: "rel_reflects_binary_pred Rel Pred"
  shows "rel_reflects_binary_pred (Rel\<^sup>=) Pred"
    and "rel_reflects_binary_pred (Rel\<^sup>+) Pred"
    and "rel_reflects_binary_pred (Rel\<^sup>*) Pred"
proof -
  from reflection show A: "rel_reflects_binary_pred (Rel\<^sup>=) Pred"
    by (auto simp add: refl)
  have B: "\<And>Rel. rel_reflects_binary_pred Rel Pred \<Longrightarrow> rel_reflects_binary_pred (Rel\<^sup>+) Pred"
  proof clarify
    fix Rel a b x
    assume "(a, b) \<in> Rel\<^sup>+" and "rel_reflects_binary_pred Rel Pred" and "Pred b x"
    thus "Pred a x"
      by (induct, blast+)
  qed
  with reflection show "rel_reflects_binary_pred (Rel\<^sup>+) Pred"
    by blast
  from reflection A B[where Rel="Rel\<^sup>="]
  show "rel_reflects_binary_pred (Rel\<^sup>*) Pred"
      using trancl_reflcl[of Rel]
    by fast
qed

text \<open>If a relation respects a predicate then so does its reflexive, symmetric, or/and transitive
        closure.\<close>

lemma respection_and_closures:
  fixes Rel  :: "('a \<times> 'a) set"
    and Pred :: "'a \<Rightarrow> bool"
  assumes respection: "rel_respects_pred Rel Pred"
  shows "rel_respects_pred (Rel\<^sup>=) Pred"
    and "rel_respects_pred (symcl Rel) Pred"
    and "rel_respects_pred (Rel\<^sup>+) Pred"
    and "rel_respects_pred (symcl (Rel\<^sup>=)) Pred"
    and "rel_respects_pred (Rel\<^sup>*) Pred"
    and "rel_respects_pred ((symcl (Rel\<^sup>=))\<^sup>+) Pred"
proof -
  from respection show A: "rel_respects_pred (Rel\<^sup>=) Pred"
      using preservation_and_closures(1)[where Rel="Rel" and Pred="Pred"]
            reflection_and_closures(1)[where Rel="Rel" and Pred="Pred"]
    by blast
  have B: "\<And>Rel. rel_respects_pred Rel Pred \<Longrightarrow> rel_respects_pred (symcl Rel) Pred"
  proof
    fix Rel
    assume B1: "rel_respects_pred Rel Pred"
    show "rel_preserves_pred (symcl Rel) Pred"
    proof clarify
      fix a b
      assume "(a, b) \<in> symcl Rel"
      hence "(a, b) \<in> Rel \<or> (b, a) \<in> Rel"
        by (simp add: symcl_def)
      moreover assume "Pred a"
      ultimately show "Pred b"
          using B1
        by blast
    qed
  next
    fix Rel  :: "('a \<times> 'a) set"
    and Pred :: "'a \<Rightarrow> bool"
    assume B2: "rel_respects_pred Rel Pred"
    show "rel_reflects_pred (symcl Rel) Pred"
    proof clarify
      fix a b
      assume "(a, b) \<in> symcl Rel"
      hence "(a, b) \<in> Rel \<or> (b, a) \<in> Rel"
        by (simp add: symcl_def)
      moreover assume "Pred b"
      ultimately show "Pred a"
          using B2
        by blast
    qed
  qed
  from respection B[where Rel="Rel"] show "rel_respects_pred (symcl Rel) Pred"
    by blast
  have C: "\<And>Rel. rel_respects_pred Rel Pred \<Longrightarrow> rel_respects_pred (Rel\<^sup>+) Pred"
  proof -
    fix Rel
    assume "rel_respects_pred Rel Pred"
    thus "rel_respects_pred (Rel\<^sup>+) Pred"
        using preservation_and_closures(2)[where Rel="Rel" and Pred="Pred"]
              reflection_and_closures(2)[where Rel="Rel" and Pred="Pred"]
      by blast
  qed
  from respection C[where Rel="Rel"] show "rel_respects_pred (Rel\<^sup>+) Pred"
    by blast
  from A B[where Rel="Rel\<^sup>="] show "rel_respects_pred (symcl (Rel\<^sup>=)) Pred"
    by blast
  from A C[where Rel="Rel\<^sup>="] show "rel_respects_pred (Rel\<^sup>*) Pred"
      using trancl_reflcl[of Rel]
    by fast
  from A B[where Rel="Rel\<^sup>="] C[where Rel="symcl (Rel\<^sup>=)"]
  show "rel_respects_pred ((symcl (Rel\<^sup>=))\<^sup>+) Pred"
    by blast
qed

lemma respection_of_binary_predicates_and_closures:
  fixes Rel  :: "('a \<times> 'a) set"
    and Pred :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes respection: "rel_respects_binary_pred Rel Pred"
  shows "rel_respects_binary_pred (Rel\<^sup>=) Pred"
    and "rel_respects_binary_pred (symcl Rel) Pred"
    and "rel_respects_binary_pred (Rel\<^sup>+) Pred"
    and "rel_respects_binary_pred (symcl (Rel\<^sup>=)) Pred"
    and "rel_respects_binary_pred (Rel\<^sup>*) Pred"
    and "rel_respects_binary_pred ((symcl (Rel\<^sup>=))\<^sup>+) Pred"
proof -
  from respection show A: "rel_respects_binary_pred (Rel\<^sup>=) Pred"
      using preservation_of_binary_predicates_and_closures(1)[where Rel="Rel" and Pred="Pred"]
            reflection_of_binary_predicates_and_closures(1)[where Rel="Rel" and Pred="Pred"]
    by blast
  have B: "\<And>Rel. rel_respects_binary_pred Rel Pred \<Longrightarrow> rel_respects_binary_pred (symcl Rel) Pred"
  proof
    fix Rel
    assume B1: "rel_respects_binary_pred Rel Pred"
    show "rel_preserves_binary_pred (symcl Rel) Pred"
    proof clarify
      fix a b x
      assume "(a, b) \<in> symcl Rel"
      hence "(a, b) \<in> Rel \<or> (b, a) \<in> Rel"
        by (simp add: symcl_def)
      moreover assume "Pred a x"
      ultimately show "Pred b x"
          using B1
        by blast
    qed
  next
    fix Rel
    assume B2: "rel_respects_binary_pred Rel Pred"
    show "rel_reflects_binary_pred (symcl Rel) Pred"
    proof clarify
      fix a b x
      assume "(a, b) \<in> symcl Rel"
      hence "(a, b) \<in> Rel \<or> (b, a) \<in> Rel"
        by (simp add: symcl_def)
      moreover assume "Pred b x"
      ultimately show "Pred a x"
          using B2
        by blast
    qed
  qed
  from respection B[where Rel="Rel"] show "rel_respects_binary_pred (symcl Rel) Pred"
    by blast
  have C: "\<And>Rel. rel_respects_binary_pred Rel Pred \<Longrightarrow> rel_respects_binary_pred (Rel\<^sup>+) Pred"
  proof -
    fix Rel
    assume "rel_respects_binary_pred Rel Pred"
    thus "rel_respects_binary_pred (Rel\<^sup>+) Pred"
        using preservation_of_binary_predicates_and_closures(2)[where Rel="Rel" and Pred="Pred"]
              reflection_of_binary_predicates_and_closures(2)[where Rel="Rel" and Pred="Pred"]
      by blast
  qed
  from respection C[where Rel="Rel"] show "rel_respects_binary_pred (Rel\<^sup>+) Pred"
    by blast
  from A B[where Rel="Rel\<^sup>="]
  show "rel_respects_binary_pred (symcl (Rel\<^sup>=)) Pred"
    by blast
  from A C[where Rel="Rel\<^sup>="]
  show "rel_respects_binary_pred (Rel\<^sup>*) Pred"
      using trancl_reflcl[of Rel]
    by fast
  from A B[where Rel="Rel\<^sup>="] C[where Rel="symcl (Rel\<^sup>=)"]
  show "rel_respects_binary_pred ((symcl (Rel\<^sup>=))\<^sup>+) Pred"
    by blast
qed

end
