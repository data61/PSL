theory ProcessCalculi
  imports Relations
begin

section \<open>Process Calculi\<close>

text \<open>A process calculus is given by a set of process terms (syntax) and a relation on terms
        (semantics). We consider reduction as well as labelled variants of the semantics.\<close>

subsection \<open>Reduction Semantics\<close>

text \<open>A set of process terms and a relation on pairs of terms (called reduction semantics) define
        a process calculus.\<close>

record 'proc processCalculus =
  Reductions :: "'proc \<Rightarrow> 'proc \<Rightarrow> bool"

text \<open>A pair of the reduction relation is called a (reduction) step.\<close>

abbreviation step :: "'proc \<Rightarrow> 'proc processCalculus \<Rightarrow> 'proc \<Rightarrow> bool"
    ("_ \<longmapsto>_ _" [70, 70, 70] 80)
  where
  "P \<longmapsto>Cal Q \<equiv> Reductions Cal P Q"

text \<open>We use * to indicate the reflexive and transitive closure of the reduction relation.\<close>

primrec nSteps
  :: "'proc \<Rightarrow> 'proc processCalculus \<Rightarrow> nat \<Rightarrow> 'proc \<Rightarrow> bool"
    ("_ \<longmapsto>_\<^bsup>_\<^esup> _" [70, 70, 70, 70] 80)
  where
  "P \<longmapsto>Cal\<^bsup>0\<^esup> Q     = (P = Q)" |
  "P \<longmapsto>Cal\<^bsup>Suc n\<^esup> Q = (\<exists>P'. P \<longmapsto>Cal\<^bsup>n\<^esup> P' \<and> P' \<longmapsto>Cal Q)"

definition steps
  :: "'proc \<Rightarrow> 'proc processCalculus \<Rightarrow> 'proc \<Rightarrow> bool"
    ("_ \<longmapsto>_* _" [70, 70, 70] 80)
  where
  "P \<longmapsto>Cal* Q \<equiv> \<exists>n. P \<longmapsto>Cal\<^bsup>n\<^esup> Q"

text \<open>A process is divergent, if it can perform an infinite sequence of steps.\<close>

definition divergent
  :: "'proc \<Rightarrow> 'proc processCalculus \<Rightarrow> bool"
    ("_ \<longmapsto>_\<omega>" [70, 70] 80)
  where
  "P \<longmapsto>(Cal)\<omega> \<equiv> \<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>P''. P' \<longmapsto>Cal P'')"

text \<open>Each term can perform an (empty) sequence of steps to itself.\<close>

lemma steps_refl:
  fixes Cal :: "'proc processCalculus"
    and P   :: "'proc"
  shows "P \<longmapsto>Cal* P"
proof -
  have "P \<longmapsto>Cal\<^bsup>0\<^esup> P"
    by simp
  hence "\<exists>n. P \<longmapsto>Cal\<^bsup>n\<^esup> P"
    by blast
  thus "P \<longmapsto>Cal* P"
    by (simp add: steps_def)
qed

text \<open>A single step is a sequence of steps of length one.\<close>

lemma step_to_steps:
  fixes Cal  :: "'proc processCalculus"
    and P P' :: "'proc"
  assumes step: "P \<longmapsto>Cal P'"
  shows "P \<longmapsto>Cal* P'"
proof -
  from step have "P \<longmapsto>Cal\<^bsup>1\<^esup> P'"
    by simp
  thus ?thesis
    unfolding steps_def
    by blast
qed

text \<open>If there is a sequence of steps from P to Q and from Q to R, then there is also a sequence
        of steps from P to R.\<close>

lemma nSteps_add:
  fixes Cal   :: "'proc processCalculus"
    and n1 n2 :: "nat"
  shows "\<forall>P Q R. P \<longmapsto>Cal\<^bsup>n1\<^esup> Q \<and> Q \<longmapsto>Cal\<^bsup>n2\<^esup> R \<longrightarrow> P \<longmapsto>Cal\<^bsup>(n1 + n2)\<^esup> R"
proof (induct n2, simp)
  case (Suc n)
  assume IH: "\<forall>P Q R. P \<longmapsto>Cal\<^bsup>n1\<^esup> Q \<and> Q \<longmapsto>Cal\<^bsup>n\<^esup> R \<longrightarrow> P \<longmapsto>Cal\<^bsup>(n1 + n)\<^esup> R"
  show ?case
  proof clarify
    fix P Q R
    assume "Q \<longmapsto>Cal\<^bsup>Suc n\<^esup> R"
    from this obtain Q' where A1: "Q \<longmapsto>Cal\<^bsup>n\<^esup> Q'" and A2: "Q' \<longmapsto>Cal R"
      by auto
    assume "P \<longmapsto>Cal\<^bsup>n1\<^esup> Q"
    with A1 IH have "P \<longmapsto>Cal\<^bsup>(n1 + n)\<^esup> Q'"
      by blast
    with A2 show "P \<longmapsto>Cal\<^bsup>(n1 + Suc n)\<^esup> R"
      by auto
  qed
qed

lemma steps_add:
  fixes Cal   :: "'proc processCalculus"
    and P Q R :: "'proc"
  assumes A1: "P \<longmapsto>Cal* Q"
      and A2: "Q \<longmapsto>Cal* R"
  shows "P \<longmapsto>Cal* R"
proof -
  from A1 obtain n1 where "P \<longmapsto>Cal\<^bsup>n1\<^esup> Q"
    by (auto simp add: steps_def)
  moreover from A2 obtain n2 where "Q \<longmapsto>Cal\<^bsup>n2\<^esup> R"
    by (auto simp add: steps_def)
  ultimately have "P \<longmapsto>Cal\<^bsup>(n1 + n2)\<^esup> R"
    using nSteps_add[where Cal="Cal"]
    by blast
  thus "P \<longmapsto>Cal* R"
    by (simp add: steps_def, blast)
qed

subsubsection \<open>Observables or Barbs\<close>

text \<open>We assume a predicate that tests terms for some kind of observables. At this point we do
        not limit or restrict the kind of observables used for a calculus nor the method to check
        them.\<close>

record ('proc, 'barbs) calculusWithBarbs =
  Calculus :: "'proc processCalculus"
  HasBarb  :: "'proc \<Rightarrow> 'barbs \<Rightarrow> bool" ("_\<down>_" [70, 70] 80)

abbreviation hasBarb
  :: "'proc \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs \<Rightarrow> bool"
    ("_\<down><_>_" [70, 70, 70] 80)
  where
  "P\<down><CWB>a \<equiv> HasBarb CWB P a"

text \<open>A term reaches a barb if it can evolve to a term that has this barb.\<close>

abbreviation reachesBarb
  :: "'proc \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs \<Rightarrow> bool"
    ("_\<Down><_>_" [70, 70, 70] 80)
  where
  "P\<Down><CWB>a \<equiv> \<exists>P'. P \<longmapsto>(Calculus CWB)* P' \<and> P'\<down><CWB>a"

text \<open>A relation R preserves barbs if whenever (P, Q) in R and P has a barb then also Q has this
        barb.\<close>

abbreviation rel_preserves_barb_set
    :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs set \<Rightarrow> bool"
  where
  "rel_preserves_barb_set Rel CWB Barbs \<equiv>
   rel_preserves_binary_pred Rel (\<lambda>P a. a \<in> Barbs \<and> P\<down><CWB>a)"

abbreviation rel_preserves_barbs
    :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool"
  where
  "rel_preserves_barbs Rel CWB \<equiv> rel_preserves_binary_pred Rel (HasBarb CWB)"

lemma preservation_of_barbs_and_set_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "rel_preserves_barbs Rel CWB = (\<forall>Barbs. rel_preserves_barb_set Rel CWB Barbs)"
    by blast

text \<open>A relation R reflects barbs if whenever (P, Q) in R and Q has a barb then also P has this
        barb.\<close>

abbreviation rel_reflects_barb_set
    :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs set \<Rightarrow> bool"
  where
  "rel_reflects_barb_set Rel CWB Barbs \<equiv>
   rel_reflects_binary_pred Rel (\<lambda>P a. a \<in> Barbs \<and> P\<down><CWB>a)"

abbreviation rel_reflects_barbs
    :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool"
  where
  "rel_reflects_barbs Rel CWB \<equiv> rel_reflects_binary_pred Rel (HasBarb CWB)"

lemma reflection_of_barbs_and_set_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "rel_reflects_barbs Rel CWB = (\<forall>Barbs. rel_reflects_barb_set Rel CWB Barbs)"
    by blast

text \<open>A relation respects barbs if it preserves and reflects barbs.\<close>

abbreviation rel_respects_barb_set
    :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs set \<Rightarrow> bool"
  where
  "rel_respects_barb_set Rel CWB Barbs \<equiv>
   rel_preserves_barb_set Rel CWB Barbs \<and> rel_reflects_barb_set Rel CWB Barbs"

abbreviation rel_respects_barbs
    :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool"
  where
  "rel_respects_barbs Rel CWB \<equiv> rel_preserves_barbs Rel CWB \<and> rel_reflects_barbs Rel CWB"

lemma respection_of_barbs_and_set_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "rel_respects_barbs Rel CWB = (\<forall>Barbs. rel_respects_barb_set Rel CWB Barbs)"
    by blast

text \<open>If a relation preserves barbs then so does its reflexive or/and transitive closure.\<close>

lemma preservation_of_barbs_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes preservation: "rel_preserves_barbs Rel CWB"
  shows "rel_preserves_barbs (Rel\<^sup>=) CWB"
    and "rel_preserves_barbs (Rel\<^sup>+) CWB"
    and "rel_preserves_barbs (Rel\<^sup>*) CWB"
      using preservation
            preservation_of_binary_predicates_and_closures[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast+

text \<open>If a relation reflects barbs then so does its reflexive or/and transitive closure.\<close>

lemma reflection_of_barbs_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes reflection: "rel_reflects_barbs Rel CWB"
  shows "rel_reflects_barbs (Rel\<^sup>=) CWB"
    and "rel_reflects_barbs (Rel\<^sup>+) CWB"
    and "rel_reflects_barbs (Rel\<^sup>*) CWB"
      using reflection
            reflection_of_binary_predicates_and_closures[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast+

text \<open>If a relation respects barbs then so does its reflexive, symmetric, or/and transitive
        closure.\<close>

lemma respection_of_barbs_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes respection: "rel_respects_barbs Rel CWB"
  shows "rel_respects_barbs (Rel\<^sup>=) CWB"
    and "rel_respects_barbs (symcl Rel) CWB"
    and "rel_respects_barbs (Rel\<^sup>+) CWB"
    and "rel_respects_barbs (symcl (Rel\<^sup>=)) CWB"
    and "rel_respects_barbs (Rel\<^sup>*) CWB"
    and "rel_respects_barbs ((symcl (Rel\<^sup>=))\<^sup>+) CWB"
proof -
  from respection show "rel_respects_barbs (Rel\<^sup>=) CWB"
      using respection_of_binary_predicates_and_closures(1)[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast
next
  from respection show "rel_respects_barbs (symcl Rel) CWB"
      using respection_of_binary_predicates_and_closures(2)[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast
next
  from respection show "rel_respects_barbs (Rel\<^sup>+) CWB"
      using respection_of_binary_predicates_and_closures(3)[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast
next
  from respection show "rel_respects_barbs (symcl (Rel\<^sup>=)) CWB"
      using respection_of_binary_predicates_and_closures(4)[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast
next
  from respection show "rel_respects_barbs (Rel\<^sup>*) CWB"
      using respection_of_binary_predicates_and_closures(5)[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast
next
  from respection show "rel_respects_barbs ((symcl (Rel\<^sup>=))\<^sup>+) CWB"
      using respection_of_binary_predicates_and_closures(6)[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast
qed

text \<open>A relation R weakly preserves barbs if it preserves reachability of barbs, i.e., if (P, Q)
        in R and P reaches a barb then also Q has to reach this barb.\<close>

abbreviation rel_weakly_preserves_barb_set
    :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs set \<Rightarrow> bool"
  where
  "rel_weakly_preserves_barb_set Rel CWB Barbs \<equiv>
   rel_preserves_binary_pred Rel (\<lambda>P a. a \<in> Barbs \<and> P\<Down><CWB>a)"

abbreviation rel_weakly_preserves_barbs
    :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool"
  where
  "rel_weakly_preserves_barbs Rel CWB \<equiv> rel_preserves_binary_pred Rel (\<lambda>P a. P\<Down><CWB>a)"

lemma weak_preservation_of_barbs_and_set_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "rel_weakly_preserves_barbs Rel CWB
         = (\<forall>Barbs. rel_weakly_preserves_barb_set Rel CWB Barbs)"
    by blast

text \<open>A relation R weakly reflects barbs if it reflects reachability of barbs, i.e., if (P, Q) in
        R and Q reaches a barb then also P has to reach this barb.\<close>

abbreviation rel_weakly_reflects_barb_set
    :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs set \<Rightarrow> bool"
  where
  "rel_weakly_reflects_barb_set Rel CWB Barbs \<equiv>
   rel_reflects_binary_pred Rel (\<lambda>P a. a \<in> Barbs \<and> P\<Down><CWB>a)"

abbreviation rel_weakly_reflects_barbs
    :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool"
  where
  "rel_weakly_reflects_barbs Rel CWB \<equiv> rel_reflects_binary_pred Rel (\<lambda>P a. P\<Down><CWB>a)"

lemma weak_reflection_of_barbs_and_set_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "rel_weakly_reflects_barbs Rel CWB = (\<forall>Barbs. rel_weakly_reflects_barb_set Rel CWB Barbs)"
    by blast

text \<open>A relation weakly respects barbs if it weakly preserves and weakly reflects barbs.\<close>

abbreviation rel_weakly_respects_barb_set
    :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs set \<Rightarrow> bool"
  where
  "rel_weakly_respects_barb_set Rel CWB Barbs \<equiv>
   rel_weakly_preserves_barb_set Rel CWB Barbs \<and> rel_weakly_reflects_barb_set Rel CWB Barbs"

abbreviation rel_weakly_respects_barbs
    :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool"
  where
  "rel_weakly_respects_barbs Rel CWB \<equiv>
   rel_weakly_preserves_barbs Rel CWB \<and> rel_weakly_reflects_barbs Rel CWB"

lemma weak_respection_of_barbs_and_set_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "rel_weakly_respects_barbs Rel CWB = (\<forall>Barbs. rel_weakly_respects_barb_set Rel CWB Barbs)"
    by blast

text \<open>If a relation weakly preserves barbs then so does its reflexive or/and transitive closure.
\<close>

lemma weak_preservation_of_barbs_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes preservation: "rel_weakly_preserves_barbs Rel CWB"
  shows "rel_weakly_preserves_barbs (Rel\<^sup>=) CWB"
    and "rel_weakly_preserves_barbs (Rel\<^sup>+) CWB"
    and "rel_weakly_preserves_barbs (Rel\<^sup>*) CWB"
      using preservation preservation_of_binary_predicates_and_closures[where Rel="Rel"
                          and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast+

text \<open>If a relation weakly reflects barbs then so does its reflexive or/and transitive closure.
\<close>

lemma weak_reflection_of_barbs_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes reflection: "rel_weakly_reflects_barbs Rel CWB"
  shows "rel_weakly_reflects_barbs (Rel\<^sup>=) CWB"
    and "rel_weakly_reflects_barbs (Rel\<^sup>+) CWB"
    and "rel_weakly_reflects_barbs (Rel\<^sup>*) CWB"
      using reflection reflection_of_binary_predicates_and_closures[where Rel="Rel"
                        and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast+

text \<open>If a relation weakly respects barbs then so does its reflexive, symmetric, or/and
        transitive closure.\<close>

lemma weak_respection_of_barbs_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes respection: "rel_weakly_respects_barbs Rel CWB"
  shows "rel_weakly_respects_barbs (Rel\<^sup>=) CWB"
    and "rel_weakly_respects_barbs (symcl Rel) CWB"
    and "rel_weakly_respects_barbs (Rel\<^sup>+) CWB"
    and "rel_weakly_respects_barbs (symcl (Rel\<^sup>=)) CWB"
    and "rel_weakly_respects_barbs (Rel\<^sup>*) CWB"
    and "rel_weakly_respects_barbs ((symcl (Rel\<^sup>=))\<^sup>+) CWB"
proof -
  from respection show "rel_weakly_respects_barbs (Rel\<^sup>=) CWB"
      using respection_of_binary_predicates_and_closures(1)[where Rel="Rel"
              and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast
next
  from respection show "rel_weakly_respects_barbs (symcl Rel) CWB"
      using respection_of_binary_predicates_and_closures(2)[where Rel="Rel"
              and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast
next
  from respection show "rel_weakly_respects_barbs (Rel\<^sup>+) CWB"
      using respection_of_binary_predicates_and_closures(3)[where Rel="Rel"
              and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast
next
  from respection show "rel_weakly_respects_barbs (symcl (Rel\<^sup>=)) CWB"
      using respection_of_binary_predicates_and_closures(4)[where Rel="Rel"
              and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast
next
  from respection show "rel_weakly_respects_barbs (Rel\<^sup>*) CWB"
      using respection_of_binary_predicates_and_closures(5)[where Rel="Rel"
              and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast
next
  from respection show "rel_weakly_respects_barbs ((symcl (Rel\<^sup>=))\<^sup>+) CWB"
      using respection_of_binary_predicates_and_closures(6)[where Rel="Rel"
              and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast
qed

end
