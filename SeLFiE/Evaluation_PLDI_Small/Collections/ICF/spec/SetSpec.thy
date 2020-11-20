(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section \<open>\isaheader{Specification of Sets}\<close>
theory SetSpec
imports ICF_Spec_Base
begin
text_raw\<open>\label{thy:SetSpec}\<close>

(*@intf Set
  @abstype 'a set
  Sets
*)

text \<open>
  This theory specifies set operations by means of a mapping to
  HOL's standard sets.
\<close>

(* Drop some notation that gets in the way here*)
(*no_notation member (infixl "mem" 55)*)
notation insert ("set'_ins")

type_synonym ('x,'s) set_\<alpha> = "'s \<Rightarrow> 'x set"
type_synonym ('x,'s) set_invar = "'s \<Rightarrow> bool"
locale set =
  \<comment> \<open>Abstraction to set\<close>
  fixes \<alpha> :: "'s \<Rightarrow> 'x set"
  \<comment> \<open>Invariant\<close>
  fixes invar :: "'s \<Rightarrow> bool"

locale set_no_invar = set +
  assumes invar[simp, intro!]: "\<And>s. invar s"

subsection "Basic Set Functions"

subsubsection "Empty set"

locale set_empty = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes empty :: "unit \<Rightarrow> 's"
  assumes empty_correct:
    "\<alpha> (empty ()) = {}"
    "invar (empty ())"

subsubsection "Membership Query"

locale set_memb = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes memb :: "'x \<Rightarrow> 's \<Rightarrow> bool"
  assumes memb_correct:
    "invar s \<Longrightarrow> memb x s \<longleftrightarrow> x \<in> \<alpha> s"

subsubsection "Insertion of Element"

locale set_ins = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes ins :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  assumes ins_correct:
    "invar s \<Longrightarrow> \<alpha> (ins x s) = set_ins x (\<alpha> s)"
    "invar s \<Longrightarrow> invar (ins x s)"

subsubsection "Disjoint Insert"

locale set_ins_dj = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes ins_dj :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  assumes ins_dj_correct:
    "\<lbrakk>invar s; x\<notin>\<alpha> s\<rbrakk> \<Longrightarrow> \<alpha> (ins_dj x s) = set_ins x (\<alpha> s)"
    "\<lbrakk>invar s; x\<notin>\<alpha> s\<rbrakk> \<Longrightarrow> invar (ins_dj x s)"

subsubsection "Deletion of Single Element"

locale set_delete = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes delete :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  assumes delete_correct:
    "invar s \<Longrightarrow> \<alpha> (delete x s) = \<alpha> s - {x}"
    "invar s \<Longrightarrow> invar (delete x s)"

subsubsection "Emptiness Check"

locale set_isEmpty = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes isEmpty :: "'s \<Rightarrow> bool"
  assumes isEmpty_correct:
    "invar s \<Longrightarrow> isEmpty s \<longleftrightarrow> \<alpha> s = {}"

subsubsection "Bounded Quantifiers"

locale set_ball = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes ball :: "'s \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> bool"
  assumes ball_correct: "invar S \<Longrightarrow> ball S P \<longleftrightarrow> (\<forall>x\<in>\<alpha> S. P x)"

locale set_bex = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes bex :: "'s \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> bool"
  assumes bex_correct: "invar S \<Longrightarrow> bex S P \<longleftrightarrow> (\<exists>x\<in>\<alpha> S. P x)"

subsubsection "Finite Set"
locale finite_set = set +
  assumes finite[simp, intro!]: "invar s \<Longrightarrow> finite (\<alpha> s)"

subsubsection "Size"

locale set_size = finite_set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes size :: "'s \<Rightarrow> nat"
  assumes size_correct: 
    "invar s \<Longrightarrow> size s = card (\<alpha> s)"
  
locale set_size_abort = finite_set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes size_abort :: "nat \<Rightarrow> 's \<Rightarrow> nat"
  assumes size_abort_correct: 
    "invar s \<Longrightarrow> size_abort m s = min m (card (\<alpha> s))"

subsubsection "Singleton sets"

locale set_sng = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes sng :: "'x \<Rightarrow> 's"
  assumes sng_correct:
    "\<alpha> (sng x) = {x}"
    "invar (sng x)"

locale set_isSng = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes isSng :: "'s \<Rightarrow> bool"
  assumes isSng_correct:
    "invar s \<Longrightarrow> isSng s \<longleftrightarrow> (\<exists>e. \<alpha> s = {e})"
begin
  lemma isSng_correct_exists1 :
    "invar s \<Longrightarrow> (isSng s \<longleftrightarrow> (\<exists>!e. (e \<in> \<alpha> s)))"
  by (auto simp add: isSng_correct)

  lemma isSng_correct_card :
    "invar s \<Longrightarrow> (isSng s \<longleftrightarrow> (card (\<alpha> s) = 1))"
  by (auto simp add: isSng_correct card_Suc_eq)
end

subsection "Iterators"
text \<open>
  An iterator applies a
  function to a state and all the elements of the set.
  The function is applied in any order. Proofs over the iteration are
  done by establishing invariants over the iteration.
  Iterators may have a break-condition, that interrupts the iteration before
  the last element has been visited.
\<close>

(* Deprecated *)
(*
locale set_iteratei = finite_set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes iteratei :: "'s \<Rightarrow> ('x, '\<sigma>) set_iterator"

  assumes iteratei_rule: "invar S \<Longrightarrow> set_iterator (iteratei S) (\<alpha> S)"
begin
  lemma iteratei_rule_P:
    "\<lbrakk>
      invar S;
      I (\<alpha> S) \<sigma>0;
      !!x it \<sigma>. \<lbrakk> c \<sigma>; x \<in> it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>);
      !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>;
      !!\<sigma> it. \<lbrakk> it \<subseteq> \<alpha> S; it \<noteq> {}; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei S c f \<sigma>0)"
   apply (rule set_iterator_rule_P [OF iteratei_rule, of S I \<sigma>0 c f P])
   apply simp_all
  done

  lemma iteratei_rule_insert_P:
    "\<lbrakk>
      invar S;
      I {} \<sigma>0;
      !!x it \<sigma>. \<lbrakk> c \<sigma>; x \<in> \<alpha> S - it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (insert x it) (f x \<sigma>);
      !!\<sigma>. I (\<alpha> S) \<sigma> \<Longrightarrow> P \<sigma>;
      !!\<sigma> it. \<lbrakk> it \<subseteq> \<alpha> S; it \<noteq> \<alpha> S; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei S c f \<sigma>0)"
    apply (rule set_iterator_rule_insert_P [OF iteratei_rule, of S I \<sigma>0 c f P])
    apply simp_all
  done

  text {* Versions without break condition. *}
  lemma iterate_rule_P:
    "\<lbrakk>
      invar S;
      I (\<alpha> S) \<sigma>0;
      !!x it \<sigma>. \<lbrakk> x \<in> it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>);
      !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei S (\<lambda>_. True) f \<sigma>0)"
   apply (rule set_iterator_no_cond_rule_P [OF iteratei_rule, of S I \<sigma>0 f P])
   apply simp_all
  done

  lemma iterate_rule_insert_P:
    "\<lbrakk>
      invar S;
      I {} \<sigma>0;
      !!x it \<sigma>. \<lbrakk> x \<in> \<alpha> S - it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (insert x it) (f x \<sigma>);
      !!\<sigma>. I (\<alpha> S) \<sigma> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei S (\<lambda>_. True) f \<sigma>0)"
    apply (rule set_iterator_no_cond_rule_insert_P [OF iteratei_rule, of S I \<sigma>0 f P])
    apply simp_all
  done
end

lemma set_iteratei_I :
assumes "\<And>s. invar s \<Longrightarrow> set_iterator (iti s) (\<alpha> s)"
shows "set_iteratei \<alpha> invar iti"
proof
  fix s 
  assume invar_s: "invar s"
  from assms(1)[OF invar_s] show it_OK: "set_iterator (iti s) (\<alpha> s)" .
  
  from set_iterator_genord.finite_S0 [OF it_OK[unfolded set_iterator_def]]
  show "finite (\<alpha> s)" .
qed
*)

type_synonym ('x,'s) set_list_it
  = "'s \<Rightarrow> ('x,'x list) set_iterator"
locale poly_set_iteratei_defs =
  fixes list_it :: "'s \<Rightarrow> ('x,'x list) set_iterator"
begin
  definition iteratei :: "'s \<Rightarrow> ('x,'\<sigma>) set_iterator"
    where "iteratei S \<equiv> it_to_it (list_it S)"
  (*local_setup {* Locale_Code.lc_decl_del @{term iteratei} *}*)

  abbreviation "iterate s \<equiv> iteratei s (\<lambda>_. True)"
end

locale poly_set_iteratei =
  finite_set + poly_set_iteratei_defs list_it
  for list_it :: "'s \<Rightarrow> ('x,'x list) set_iterator" +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  assumes list_it_correct: "invar s \<Longrightarrow> set_iterator (list_it s) (\<alpha> s)"
begin
  lemma iteratei_correct: "invar S \<Longrightarrow> set_iterator (iteratei S) (\<alpha> S)"
    unfolding iteratei_def
    apply (rule it_to_it_correct)
    by (rule list_it_correct)

  lemma pi_iteratei[icf_proper_iteratorI]: 
    "proper_it (iteratei S) (iteratei S)"
    unfolding iteratei_def 
    by (intro icf_proper_iteratorI)

  lemma iteratei_rule_P:
    "\<lbrakk>
      invar S;
      I (\<alpha> S) \<sigma>0;
      !!x it \<sigma>. \<lbrakk> c \<sigma>; x \<in> it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>);
      !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>;
      !!\<sigma> it. \<lbrakk> it \<subseteq> \<alpha> S; it \<noteq> {}; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei S c f \<sigma>0)"
   apply (rule set_iterator_rule_P [OF iteratei_correct, of S I \<sigma>0 c f P])
   apply simp_all
  done

  lemma iteratei_rule_insert_P:
    "\<lbrakk>
      invar S;
      I {} \<sigma>0;
      !!x it \<sigma>. \<lbrakk> c \<sigma>; x \<in> \<alpha> S - it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (insert x it) (f x \<sigma>);
      !!\<sigma>. I (\<alpha> S) \<sigma> \<Longrightarrow> P \<sigma>;
      !!\<sigma> it. \<lbrakk> it \<subseteq> \<alpha> S; it \<noteq> \<alpha> S; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei S c f \<sigma>0)"
    apply (rule 
      set_iterator_rule_insert_P[OF iteratei_correct, of S I \<sigma>0 c f P])
    apply simp_all
  done

  text \<open>Versions without break condition.\<close>
  lemma iterate_rule_P:
    "\<lbrakk>
      invar S;
      I (\<alpha> S) \<sigma>0;
      !!x it \<sigma>. \<lbrakk> x \<in> it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>);
      !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei S (\<lambda>_. True) f \<sigma>0)"
   apply (rule set_iterator_no_cond_rule_P [OF iteratei_correct, of S I \<sigma>0 f P])
   apply simp_all
  done

  lemma iterate_rule_insert_P:
    "\<lbrakk>
      invar S;
      I {} \<sigma>0;
      !!x it \<sigma>. \<lbrakk> x \<in> \<alpha> S - it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (insert x it) (f x \<sigma>);
      !!\<sigma>. I (\<alpha> S) \<sigma> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei S (\<lambda>_. True) f \<sigma>0)"
    apply (rule set_iterator_no_cond_rule_insert_P [OF iteratei_correct, 
      of S I \<sigma>0 f P])
    apply simp_all
  done

end

subsection "More Set Operations"

subsubsection "Copy"
locale set_copy = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  +
  fixes copy :: "'s1 \<Rightarrow> 's2"
  assumes copy_correct: 
    "invar1 s1 \<Longrightarrow> \<alpha>2 (copy s1) = \<alpha>1 s1"
    "invar1 s1 \<Longrightarrow> invar2 (copy s1)"

subsubsection "Union"


locale set_union = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2 + s3: set \<alpha>3 invar3
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  and \<alpha>3 :: "'s3 \<Rightarrow> 'a set" and invar3
  +
  fixes union :: "'s1 \<Rightarrow> 's2 \<Rightarrow> 's3"
  assumes union_correct:
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> \<alpha>3 (union s1 s2) = \<alpha>1 s1 \<union> \<alpha>2 s2"
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> invar3 (union s1 s2)"


locale set_union_dj = 
  s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2 + s3: set \<alpha>3 invar3
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  and \<alpha>3 :: "'s3 \<Rightarrow> 'a set" and invar3
  +
  fixes union_dj :: "'s1 \<Rightarrow> 's2 \<Rightarrow> 's3"
  assumes union_dj_correct:
    "\<lbrakk>invar1 s1; invar2 s2; \<alpha>1 s1 \<inter> \<alpha>2 s2 = {}\<rbrakk> \<Longrightarrow> \<alpha>3 (union_dj s1 s2) = \<alpha>1 s1 \<union> \<alpha>2 s2"
    "\<lbrakk>invar1 s1; invar2 s2; \<alpha>1 s1 \<inter> \<alpha>2 s2 = {}\<rbrakk> \<Longrightarrow> invar3 (union_dj s1 s2)"

locale set_union_list = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  +
  fixes union_list :: "'s1 list \<Rightarrow> 's2"
  assumes union_list_correct:
    "\<forall>s1\<in>set l. invar1 s1 \<Longrightarrow> \<alpha>2 (union_list l) = \<Union>{\<alpha>1 s1 |s1. s1 \<in> set l}"
    "\<forall>s1\<in>set l. invar1 s1 \<Longrightarrow> invar2 (union_list l)"

subsubsection "Difference"

locale set_diff = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2 
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  +
  fixes diff :: "'s1 \<Rightarrow> 's2 \<Rightarrow> 's1"
  assumes diff_correct:
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> \<alpha>1 (diff s1 s2) = \<alpha>1 s1 - \<alpha>2 s2"
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> invar1 (diff s1 s2)"

subsubsection "Intersection"

locale set_inter = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2 + s3: set \<alpha>3 invar3
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  and \<alpha>3 :: "'s3 \<Rightarrow> 'a set" and invar3
  +
  fixes inter :: "'s1 \<Rightarrow> 's2 \<Rightarrow> 's3"
  assumes inter_correct:
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> \<alpha>3 (inter s1 s2) = \<alpha>1 s1 \<inter> \<alpha>2 s2"
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> invar3 (inter s1 s2)"

subsubsection "Subset"

locale set_subset = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  +
  fixes subset :: "'s1 \<Rightarrow> 's2 \<Rightarrow> bool"
  assumes subset_correct:
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> subset s1 s2 \<longleftrightarrow> \<alpha>1 s1 \<subseteq> \<alpha>2 s2"

subsubsection "Equal"

locale set_equal = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  +
  fixes equal :: "'s1 \<Rightarrow> 's2 \<Rightarrow> bool"
  assumes equal_correct:
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> equal s1 s2 \<longleftrightarrow> \<alpha>1 s1 = \<alpha>2 s2"


subsubsection "Image and Filter"

locale set_image_filter = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'b set" and invar2
  +
  fixes image_filter :: "('a \<Rightarrow> 'b option) \<Rightarrow> 's1 \<Rightarrow> 's2"
  assumes image_filter_correct_aux:
    "invar1 s \<Longrightarrow> \<alpha>2 (image_filter f s) = { b . \<exists>a\<in>\<alpha>1 s. f a = Some b }"
    "invar1 s \<Longrightarrow> invar2 (image_filter f s)"
begin
  \<comment> \<open>This special form will be checked first by the simplifier:\<close>
  lemma image_filter_correct_aux2: 
    "invar1 s \<Longrightarrow> 
    \<alpha>2 (image_filter (\<lambda>x. if P x then (Some (f x)) else None) s) 
    = f ` {x\<in>\<alpha>1 s. P x}"
    by (auto simp add: image_filter_correct_aux)

  lemmas image_filter_correct = 
    image_filter_correct_aux2 image_filter_correct_aux

end

locale set_inj_image_filter = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'b set" and invar2
  +
  fixes inj_image_filter :: "('a \<Rightarrow> 'b option) \<Rightarrow> 's1 \<Rightarrow> 's2"
  assumes inj_image_filter_correct:
    "\<lbrakk>invar1 s; inj_on f (\<alpha>1 s \<inter> dom f)\<rbrakk> \<Longrightarrow> \<alpha>2 (inj_image_filter f s) = { b . \<exists>a\<in>\<alpha>1 s. f a = Some b }"
    "\<lbrakk>invar1 s; inj_on f (\<alpha>1 s \<inter> dom f)\<rbrakk> \<Longrightarrow> invar2 (inj_image_filter f s)"

subsubsection "Image"

locale set_image = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'b set" and invar2
  +
  fixes image :: "('a \<Rightarrow> 'b) \<Rightarrow> 's1 \<Rightarrow> 's2"
  assumes image_correct:
    "invar1 s \<Longrightarrow> \<alpha>2 (image f s) = f`\<alpha>1 s"
    "invar1 s \<Longrightarrow> invar2 (image f s)"


locale set_inj_image = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'b set" and invar2
  +
  fixes inj_image :: "('a \<Rightarrow> 'b) \<Rightarrow> 's1 \<Rightarrow> 's2"
  assumes inj_image_correct:
    "\<lbrakk>invar1 s; inj_on f (\<alpha>1 s)\<rbrakk> \<Longrightarrow> \<alpha>2 (inj_image f s) = f`\<alpha>1 s"
    "\<lbrakk>invar1 s; inj_on f (\<alpha>1 s)\<rbrakk> \<Longrightarrow> invar2 (inj_image f s)"


subsubsection "Filter"

locale set_filter = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  +
  fixes filter :: "('a \<Rightarrow> bool) \<Rightarrow> 's1 \<Rightarrow> 's2"
  assumes filter_correct:
    "invar1 s \<Longrightarrow> \<alpha>2 (filter P s) = {e. e \<in> \<alpha>1 s \<and> P e}"
    "invar1 s \<Longrightarrow> invar2 (filter P s)"


subsubsection "Union of Set of Sets"

locale set_Union_image = 
  s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2 + s3: set \<alpha>3 invar3
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'b set" and invar2
  and \<alpha>3 :: "'s3 \<Rightarrow> 'b set" and invar3
  +
  fixes Union_image :: "('a \<Rightarrow> 's2) \<Rightarrow> 's1 \<Rightarrow> 's3"
  assumes Union_image_correct: 
    "\<lbrakk> invar1 s; !!x. x\<in>\<alpha>1 s \<Longrightarrow> invar2 (f x) \<rbrakk> \<Longrightarrow> 
      \<alpha>3 (Union_image f s) = \<Union>(\<alpha>2`f`\<alpha>1 s)"
    "\<lbrakk> invar1 s; !!x. x\<in>\<alpha>1 s \<Longrightarrow> invar2 (f x) \<rbrakk> \<Longrightarrow> invar3 (Union_image f s)"


subsubsection "Disjointness Check"

locale set_disjoint = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  +
  fixes disjoint :: "'s1 \<Rightarrow> 's2 \<Rightarrow> bool"
  assumes disjoint_correct:
    "invar1 s1 \<Longrightarrow> invar2 s2 \<Longrightarrow> disjoint s1 s2 \<longleftrightarrow> \<alpha>1 s1 \<inter> \<alpha>2 s2 = {}"

subsubsection "Disjointness Check With Witness"

locale set_disjoint_witness = s1: set \<alpha>1 invar1 + s2: set \<alpha>2 invar2
  for \<alpha>1 :: "'s1 \<Rightarrow> 'a set" and invar1
  and \<alpha>2 :: "'s2 \<Rightarrow> 'a set" and invar2
  +
  fixes disjoint_witness :: "'s1 \<Rightarrow> 's2 \<Rightarrow> 'a option"
  assumes disjoint_witness_correct:
    "\<lbrakk>invar1 s1; invar2 s2\<rbrakk> 
      \<Longrightarrow> disjoint_witness s1 s2 = None \<Longrightarrow> \<alpha>1 s1 \<inter> \<alpha>2 s2 = {}"
    "\<lbrakk>invar1 s1; invar2 s2; disjoint_witness s1 s2 = Some a\<rbrakk> 
      \<Longrightarrow> a\<in>\<alpha>1 s1 \<inter> \<alpha>2 s2"
begin
  lemma disjoint_witness_None: "\<lbrakk>invar1 s1; invar2 s2\<rbrakk> 
    \<Longrightarrow> disjoint_witness s1 s2 = None \<longleftrightarrow> \<alpha>1 s1 \<inter> \<alpha>2 s2 = {}"
    by (case_tac "disjoint_witness s1 s2")
       (auto dest: disjoint_witness_correct)
    
  lemma disjoint_witnessI: "\<lbrakk>
    invar1 s1; 
    invar2 s2; 
    \<alpha>1 s1 \<inter> \<alpha>2 s2 \<noteq> {}; 
    !!a. \<lbrakk>disjoint_witness s1 s2 = Some a\<rbrakk> \<Longrightarrow> P 
                            \<rbrakk> \<Longrightarrow> P"
    by (case_tac "disjoint_witness s1 s2")
       (auto dest: disjoint_witness_correct)

end

subsubsection "Selection of Element"

locale set_sel = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes sel :: "'s \<Rightarrow> ('x \<Rightarrow> 'r option) \<Rightarrow> 'r option"
  assumes selE: 
    "\<lbrakk> invar s; x\<in>\<alpha> s; f x = Some r; 
       !!x r. \<lbrakk>sel s f = Some r; x\<in>\<alpha> s; f x = Some r \<rbrakk> \<Longrightarrow> Q 
     \<rbrakk> \<Longrightarrow> Q"
  assumes selI: "\<lbrakk>invar s; \<forall>x\<in>\<alpha> s. f x = None \<rbrakk> \<Longrightarrow> sel s f = None"
begin

  lemma sel_someD:
    "\<lbrakk> invar s; sel s f = Some r; !!x. \<lbrakk>x\<in>\<alpha> s; f x = Some r\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
    apply (cases "\<exists>x\<in>\<alpha> s. \<exists>r. f x = Some r")
    apply (safe)
    apply (erule_tac f=f and x=x in selE)
    apply auto
    apply (drule (1) selI)
    apply simp
    done

  lemma sel_noneD: 
    "\<lbrakk> invar s; sel s f = None; x\<in>\<alpha> s \<rbrakk> \<Longrightarrow> f x = None"
    apply (cases "\<exists>x\<in>\<alpha> s. \<exists>r. f x = Some r")
    apply (safe)
    apply (erule_tac f=f and x=xa in selE)
    apply auto
    done
end

\<comment> \<open>Selection of element (without mapping)\<close>
locale set_sel' = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes sel' :: "'s \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> 'x option"
  assumes sel'E: 
    "\<lbrakk> invar s; x\<in>\<alpha> s; P x; 
       !!x. \<lbrakk>sel' s P = Some x; x\<in>\<alpha> s; P x \<rbrakk> \<Longrightarrow> Q 
     \<rbrakk> \<Longrightarrow> Q"
  assumes sel'I: "\<lbrakk>invar s; \<forall>x\<in>\<alpha> s. \<not> P x \<rbrakk> \<Longrightarrow> sel' s P = None"
begin

  lemma sel'_someD:
    "\<lbrakk> invar s; sel' s P = Some x \<rbrakk> \<Longrightarrow> x\<in>\<alpha> s \<and> P x"
    apply (cases "\<exists>x\<in>\<alpha> s. P x")
    apply (safe)
    apply (erule_tac P=P and x=xa in sel'E)
    apply auto
    apply (erule_tac P=P and x=xa in sel'E)
    apply auto
    apply (drule (1) sel'I)
    apply simp
    apply (drule (1) sel'I)
    apply simp
    done

  lemma sel'_noneD: 
    "\<lbrakk> invar s; sel' s P = None; x\<in>\<alpha> s \<rbrakk> \<Longrightarrow> \<not>P x"
    apply (cases "\<exists>x\<in>\<alpha> s. P x")
    apply (safe)
    apply (erule_tac P=P and x=xa in sel'E)
    apply auto
    done
end

subsubsection "Conversion of Set to List"

locale set_to_list = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes to_list :: "'s \<Rightarrow> 'x list"
  assumes to_list_correct: 
    "invar s \<Longrightarrow> set (to_list s) = \<alpha> s"
    "invar s \<Longrightarrow> distinct (to_list s)"

subsubsection "Conversion of List to Set"

locale list_to_set = set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes to_set :: "'x list \<Rightarrow> 's"
  assumes to_set_correct:
    "\<alpha> (to_set l) = set l"
    "invar (to_set l)"

subsection "Ordered Sets"

  locale ordered_set = set \<alpha> invar 
    for \<alpha> :: "'s \<Rightarrow> ('u::linorder) set" and invar

  locale ordered_finite_set = finite_set \<alpha> invar + ordered_set \<alpha> invar
    for \<alpha> :: "'s \<Rightarrow> ('u::linorder) set" and invar

subsubsection "Ordered Iteration"
  (* Deprecated *)
(*  locale set_iterateoi = ordered_finite_set \<alpha> invar
    for \<alpha> :: "'s \<Rightarrow> ('u::linorder) set" and invar
    +
    fixes iterateoi :: "'s \<Rightarrow> ('u,'\<sigma>) set_iterator"
    assumes iterateoi_rule: 
      "invar s \<Longrightarrow> set_iterator_linord (iterateoi s) (\<alpha> s)"
  begin
    lemma iterateoi_rule_P[case_names minv inv0 inv_pres i_complete i_inter]:
      assumes MINV: "invar m"
      assumes I0: "I (\<alpha> m) \<sigma>0"
      assumes IP: "!!k it \<sigma>. \<lbrakk> 
        c \<sigma>; 
        k \<in> it; 
        \<forall>j\<in>it. k\<le>j; 
        \<forall>j\<in>\<alpha> m - it. j\<le>k; 
        it \<subseteq> \<alpha> m; 
        I it \<sigma> 
      \<rbrakk> \<Longrightarrow> I (it - {k}) (f k \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      assumes II: "!!\<sigma> it. \<lbrakk> 
        it \<subseteq> \<alpha> m; 
        it \<noteq> {}; 
        \<not> c \<sigma>; 
        I it \<sigma>; 
        \<forall>k\<in>it. \<forall>j\<in>\<alpha> m - it. j\<le>k 
      \<rbrakk> \<Longrightarrow> P \<sigma>"
      shows "P (iterateoi m c f \<sigma>0)"  
    using set_iterator_linord_rule_P [OF iterateoi_rule, OF MINV, of I \<sigma>0 c f P,
       OF I0 _ IF] IP II
    by simp

    lemma iterateo_rule_P[case_names minv inv0 inv_pres i_complete]: 
      assumes MINV: "invar m"
      assumes I0: "I ((\<alpha> m)) \<sigma>0"
      assumes IP: "!!k it \<sigma>. \<lbrakk> k \<in> it; \<forall>j\<in>it. k\<le>j; \<forall>j\<in>(\<alpha> m) - it. j\<le>k; it \<subseteq> (\<alpha> m); I it \<sigma> \<rbrakk> 
                  \<Longrightarrow> I (it - {k}) (f k \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    shows "P (iterateoi m (\<lambda>_. True) f \<sigma>0)"
      apply (rule iterateoi_rule_P [where I = I])
      apply (simp_all add: assms)
    done
  end

  lemma set_iterateoi_I :
  assumes "\<And>s. invar s \<Longrightarrow> set_iterator_linord (itoi s) (\<alpha> s)"
  shows "set_iterateoi \<alpha> invar itoi"
  proof
    fix s
    assume invar_s: "invar s"
    from assms(1)[OF invar_s] show it_OK: "set_iterator_linord (itoi s) (\<alpha> s)" .
  
    from set_iterator_genord.finite_S0 [OF it_OK[unfolded set_iterator_linord_def]]
    show "finite (\<alpha> s)" by simp 
  qed

  (* Deprecated *)
  locale set_reverse_iterateoi = ordered_finite_set \<alpha> invar 
    for \<alpha> :: "'s \<Rightarrow> ('u::linorder) set" and invar
    +
    fixes reverse_iterateoi :: "'s \<Rightarrow> ('u,'\<sigma>) set_iterator"
    assumes reverse_iterateoi_rule: "
      invar m \<Longrightarrow> set_iterator_rev_linord (reverse_iterateoi m) (\<alpha> m)" 
  begin
    lemma reverse_iterateoi_rule_P[case_names minv inv0 inv_pres i_complete i_inter]:
      assumes MINV: "invar m"
      assumes I0: "I ((\<alpha> m)) \<sigma>0"
      assumes IP: "!!k it \<sigma>. \<lbrakk> 
        c \<sigma>; 
        k \<in> it; 
        \<forall>j\<in>it. k\<ge>j; 
        \<forall>j\<in>(\<alpha> m) - it. j\<ge>k; 
        it \<subseteq> (\<alpha> m); 
        I it \<sigma> 
      \<rbrakk> \<Longrightarrow> I (it - {k}) (f k \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      assumes II: "!!\<sigma> it. \<lbrakk> 
        it \<subseteq> (\<alpha> m); 
        it \<noteq> {}; 
        \<not> c \<sigma>; 
        I it \<sigma>; 
        \<forall>k\<in>it. \<forall>j\<in>(\<alpha> m) - it. j\<ge>k 
      \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (reverse_iterateoi m c f \<sigma>0)"
    using set_iterator_rev_linord_rule_P [OF reverse_iterateoi_rule, OF MINV, of I \<sigma>0 c f P,
       OF I0 _ IF] IP II
    by simp

    lemma reverse_iterateo_rule_P[case_names minv inv0 inv_pres i_complete]:
      assumes MINV: "invar m"
      assumes I0: "I ((\<alpha> m)) \<sigma>0"
      assumes IP: "!!k it \<sigma>. \<lbrakk> 
        k \<in> it; 
        \<forall>j\<in>it. k\<ge>j; 
        \<forall>j\<in> (\<alpha> m) - it. j\<ge>k; 
        it \<subseteq> (\<alpha> m); 
        I it \<sigma> 
      \<rbrakk> \<Longrightarrow> I (it - {k}) (f k \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    shows "P (reverse_iterateoi m (\<lambda>_. True) f \<sigma>0)"
      apply (rule reverse_iterateoi_rule_P [where I = I])
      apply (simp_all add: assms)
    done
  end

  lemma set_reverse_iterateoi_I :
  assumes "\<And>s. invar s \<Longrightarrow> set_iterator_rev_linord (itoi s) (\<alpha> s)"
  shows "set_reverse_iterateoi \<alpha> invar itoi"
  proof
    fix s
    assume invar_s: "invar s"
    from assms(1)[OF invar_s] show it_OK: "set_iterator_rev_linord (itoi s) (\<alpha> s)" .
  
    from set_iterator_genord.finite_S0 [OF it_OK[unfolded set_iterator_rev_linord_def]]
    show "finite (\<alpha> s)" by simp 
  qed
*)

locale poly_set_iterateoi_defs =
  fixes olist_it :: "'s \<Rightarrow> ('x,'x list) set_iterator"
begin
  definition iterateoi :: "'s \<Rightarrow> ('x,'\<sigma>) set_iterator"
    where "iterateoi S \<equiv> it_to_it (olist_it S)"
  (*local_setup {* Locale_Code.lc_decl_del @{term iterateoi} *}*)

  abbreviation "iterateo s \<equiv> iterateoi s (\<lambda>_. True)"
end


locale poly_set_iterateoi =
  finite_set \<alpha> invar + poly_set_iterateoi_defs list_ordered_it
  for \<alpha> :: "'s \<Rightarrow> 'x::linorder set" 
  and invar 
  and list_ordered_it :: "'s \<Rightarrow> ('x,'x list) set_iterator" +
  assumes list_ordered_it_correct: "invar x 
    \<Longrightarrow> set_iterator_linord (list_ordered_it x) (\<alpha> x)"
begin
  lemma iterateoi_correct: 
    "invar S \<Longrightarrow> set_iterator_linord (iterateoi S) (\<alpha> S)"
    unfolding iterateoi_def
    apply (rule it_to_it_linord_correct)
    by (rule list_ordered_it_correct)

  lemma pi_iterateoi[icf_proper_iteratorI]: 
    "proper_it (iterateoi S) (iterateoi S)"
    unfolding iterateoi_def 
    by (intro icf_proper_iteratorI)
  
  lemma iterateoi_rule_P[case_names minv inv0 inv_pres i_complete i_inter]:
    assumes MINV: "invar s"
    assumes I0: "I (\<alpha> s) \<sigma>0"
    assumes IP: "!!k it \<sigma>. \<lbrakk> 
      c \<sigma>; 
      k \<in> it; 
      \<forall>j\<in>it. k\<le>j; 
      \<forall>j\<in>\<alpha> s - it. j\<le>k; 
      it \<subseteq> \<alpha> s; 
      I it \<sigma> 
    \<rbrakk> \<Longrightarrow> I (it - {k}) (f k \<sigma>)"
    assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    assumes II: "!!\<sigma> it. \<lbrakk> 
      it \<subseteq> \<alpha> s; 
      it \<noteq> {}; 
      \<not> c \<sigma>; 
      I it \<sigma>; 
      \<forall>k\<in>it. \<forall>j\<in>\<alpha> s - it. j\<le>k 
    \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iterateoi s c f \<sigma>0)"  
  using set_iterator_linord_rule_P [OF iterateoi_correct, 
    OF MINV, of I \<sigma>0 c f P, OF I0 _ IF] IP II
  by simp

  lemma iterateo_rule_P[case_names minv inv0 inv_pres i_complete]: 
    assumes MINV: "invar s"
    assumes I0: "I ((\<alpha> s)) \<sigma>0"
    assumes IP: "!!k it \<sigma>. \<lbrakk> k \<in> it; \<forall>j\<in>it. k\<le>j; 
        \<forall>j\<in>(\<alpha> s) - it. j\<le>k; it \<subseteq> (\<alpha> s); I it \<sigma> \<rbrakk> 
      \<Longrightarrow> I (it - {k}) (f k \<sigma>)"
    assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
  shows "P (iterateo s f \<sigma>0)"
    apply (rule iterateoi_rule_P [where I = I])
    apply (simp_all add: assms)
  done
end

locale poly_set_rev_iterateoi_defs =
  fixes list_rev_it :: "'s \<Rightarrow> ('x::linorder,'x list) set_iterator"
begin
  definition rev_iterateoi :: "'s \<Rightarrow> ('x,'\<sigma>) set_iterator"
    where "rev_iterateoi S \<equiv> it_to_it (list_rev_it S)"
  (*local_setup {* Locale_Code.lc_decl_del @{term rev_iterateoi} *}*)

  abbreviation "rev_iterateo m \<equiv> rev_iterateoi m (\<lambda>_. True)"
  abbreviation "reverse_iterateoi \<equiv> rev_iterateoi"
  abbreviation "reverse_iterateo \<equiv> rev_iterateo"
end

locale poly_set_rev_iterateoi =
  finite_set \<alpha> invar + poly_set_rev_iterateoi_defs list_rev_it
  for \<alpha> :: "'s \<Rightarrow> 'x::linorder set" 
  and invar
  and list_rev_it :: "'s \<Rightarrow> ('x,'x list) set_iterator" +
  assumes list_rev_it_correct: 
    "invar s \<Longrightarrow> set_iterator_rev_linord (list_rev_it s) (\<alpha> s)"
begin
  lemma rev_iterateoi_correct: 
    "invar S \<Longrightarrow> set_iterator_rev_linord (rev_iterateoi S) (\<alpha> S)"
    unfolding rev_iterateoi_def
    apply (rule it_to_it_rev_linord_correct)
    by (rule list_rev_it_correct)

  lemma pi_rev_iterateoi[icf_proper_iteratorI]: 
    "proper_it (rev_iterateoi S) (rev_iterateoi S)"
    unfolding rev_iterateoi_def 
    by (intro icf_proper_iteratorI)

  lemma rev_iterateoi_rule_P[case_names minv inv0 inv_pres i_complete i_inter]:
    assumes MINV: "invar s"
    assumes I0: "I ((\<alpha> s)) \<sigma>0"
    assumes IP: "!!k it \<sigma>. \<lbrakk> 
      c \<sigma>; 
      k \<in> it; 
      \<forall>j\<in>it. k\<ge>j; 
      \<forall>j\<in>(\<alpha> s) - it. j\<ge>k; 
      it \<subseteq> (\<alpha> s); 
      I it \<sigma> 
    \<rbrakk> \<Longrightarrow> I (it - {k}) (f k \<sigma>)"
    assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    assumes II: "!!\<sigma> it. \<lbrakk> 
      it \<subseteq> (\<alpha> s); 
      it \<noteq> {}; 
      \<not> c \<sigma>; 
      I it \<sigma>; 
      \<forall>k\<in>it. \<forall>j\<in>(\<alpha> s) - it. j\<ge>k 
    \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (rev_iterateoi s c f \<sigma>0)"
  using set_iterator_rev_linord_rule_P [OF rev_iterateoi_correct, 
    OF MINV, of I \<sigma>0 c f P, OF I0 _ IF] IP II
  by simp

  lemma reverse_iterateo_rule_P[case_names minv inv0 inv_pres i_complete]:
    assumes MINV: "invar s"
    assumes I0: "I ((\<alpha> s)) \<sigma>0"
    assumes IP: "!!k it \<sigma>. \<lbrakk> 
      k \<in> it; 
      \<forall>j\<in>it. k\<ge>j; 
      \<forall>j\<in> (\<alpha> s) - it. j\<ge>k; 
      it \<subseteq> (\<alpha> s); 
      I it \<sigma> 
    \<rbrakk> \<Longrightarrow> I (it - {k}) (f k \<sigma>)"
    assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
  shows "P (rev_iterateo s f \<sigma>0)"
    apply (rule rev_iterateoi_rule_P [where I = I])
    apply (simp_all add: assms)
  done

end

subsubsection "Minimal and Maximal Element"

  locale set_min = ordered_set +
    constrains \<alpha> :: "'s \<Rightarrow> 'u::linorder set"
    fixes min :: "'s \<Rightarrow> ('u \<Rightarrow> bool) \<Rightarrow> 'u option"
    assumes min_correct:
      "\<lbrakk> invar s; x\<in>\<alpha> s; P x \<rbrakk> \<Longrightarrow> min s P \<in> Some ` {x\<in>\<alpha> s. P x}"
      "\<lbrakk> invar s; x\<in>\<alpha> s; P x \<rbrakk> \<Longrightarrow> (the (min s P)) \<le> x"
      "\<lbrakk> invar s; {x\<in>\<alpha> s. P x} = {} \<rbrakk> \<Longrightarrow> min s P = None"
  begin
   lemma minE: 
     assumes A: "invar s" "x\<in>\<alpha> s" "P x"
     obtains x' where
     "min s P = Some x'" "x'\<in>\<alpha> s" "P x'" "\<forall>x\<in>\<alpha> s. P x \<longrightarrow> x' \<le> x"
   proof -
     from min_correct(1)[of s x P, OF A] have 
       MIS: "min s P \<in> Some ` {x \<in> \<alpha> s. P x}" .
     then obtain x' where KV: "min s P = Some x'" "x'\<in>\<alpha> s" "P x'"
       by auto
     show thesis 
       apply (rule that[OF KV])
       apply (clarify)
       apply (drule (1) min_correct(2)[OF \<open>invar s\<close>])
       apply (simp add: KV(1))
       done
   qed

   lemmas minI = min_correct(3)

   lemma min_Some:
     "\<lbrakk> invar s; min s P = Some x \<rbrakk> \<Longrightarrow> x\<in>\<alpha> s"
     "\<lbrakk> invar s; min s P = Some x \<rbrakk> \<Longrightarrow> P x"
     "\<lbrakk> invar s; min s P = Some x; x'\<in>\<alpha> s; P x'\<rbrakk> \<Longrightarrow> x\<le>x'"
     apply -
     apply (cases "{x \<in> \<alpha> s. P x} = {}")
     apply (drule (1) min_correct(3))
     apply simp
     apply simp
     apply (erule exE)
     apply clarify
     apply (drule (2) min_correct(1)[of s _ P])
     apply auto [1]

     apply (cases "{x \<in> \<alpha> s. P x} = {}")
     apply (drule (1) min_correct(3))
     apply simp
     apply simp
     apply (erule exE)
     apply clarify
     apply (drule (2) min_correct(1)[of s _ P])
     apply auto [1]

     apply (drule (2) min_correct(2)[where P=P])
     apply auto
     done
     
   lemma min_None:
     "\<lbrakk> invar s; min s P = None \<rbrakk> \<Longrightarrow> {x\<in>\<alpha> s. P x} = {}"
     apply (cases "{x\<in>\<alpha> s. P x} = {}")
     apply simp
     apply simp
     apply (erule exE)
     apply clarify
     apply (drule (2) min_correct(1)[where P=P])
     apply auto
     done

  end

  locale set_max = ordered_set +
    constrains \<alpha> :: "'s \<Rightarrow> 'u::linorder set"
    fixes max :: "'s \<Rightarrow> ('u \<Rightarrow> bool) \<Rightarrow> 'u option"
    assumes max_correct:
      "\<lbrakk> invar s; x\<in>\<alpha> s; P x \<rbrakk> \<Longrightarrow> max s P \<in> Some ` {x\<in>\<alpha> s. P x}"
      "\<lbrakk> invar s; x\<in>\<alpha> s; P x \<rbrakk> \<Longrightarrow> the (max s P) \<ge> x"
      "\<lbrakk> invar s; {x\<in>\<alpha> s. P x} = {} \<rbrakk> \<Longrightarrow> max s P = None"
  begin
   lemma maxE: 
     assumes A: "invar s" "x\<in>\<alpha> s" "P x"
     obtains x' where
     "max s P = Some x'" "x'\<in>\<alpha> s" "P x'" "\<forall>x\<in>\<alpha> s. P x \<longrightarrow> x' \<ge> x"
   proof -
     from max_correct(1)[where P=P, OF A] have 
       MIS: "max s P \<in> Some ` {x\<in>\<alpha> s. P x}" .
     then obtain x' where KV: "max s P = Some x'" "x'\<in> \<alpha> s" "P x'"
       by auto
     show thesis 
       apply (rule that[OF KV])
       apply (clarify)
       apply (drule (1) max_correct(2)[OF \<open>invar s\<close>])
       apply (simp add: KV(1))
       done
   qed

   lemmas maxI = max_correct(3)

   lemma max_Some:
     "\<lbrakk> invar s; max s P = Some x \<rbrakk> \<Longrightarrow> x\<in>\<alpha> s"
     "\<lbrakk> invar s; max s P = Some x \<rbrakk> \<Longrightarrow> P x"
     "\<lbrakk> invar s; max s P = Some x; x'\<in>\<alpha> s; P x'\<rbrakk> \<Longrightarrow> x\<ge>x'"
     apply -
     apply (cases "{x\<in>\<alpha> s. P x} = {}")
     apply (drule (1) max_correct(3))
     apply simp
     apply simp
     apply (erule exE)
     apply clarify
     apply (drule (2) max_correct(1)[of s _ P])
     apply auto [1]

     apply (cases "{x\<in>\<alpha> s. P x} = {}")
     apply (drule (1) max_correct(3))
     apply simp
     apply simp
     apply (erule exE)
     apply clarify
     apply (drule (2) max_correct(1)[of s _ P])
     apply auto [1]

     apply (drule (1) max_correct(2)[where P=P])
     apply auto
     done
     
   lemma max_None:
     "\<lbrakk> invar s; max s P = None \<rbrakk> \<Longrightarrow> {x\<in>\<alpha> s. P x} = {}"
     apply (cases "{x\<in>\<alpha> s. P x} = {}")
     apply simp
     apply simp
     apply (erule exE)
     apply clarify
     apply (drule (1) max_correct(1)[where P=P])
     apply auto
     done

  end

subsection "Conversion to List"
  locale set_to_sorted_list = ordered_set + 
  constrains \<alpha> :: "'s \<Rightarrow> 'x::linorder set"
  fixes to_sorted_list :: "'s \<Rightarrow> 'x list"
  assumes to_sorted_list_correct: 
    "invar s \<Longrightarrow> set (to_sorted_list s) = \<alpha> s"
    "invar s \<Longrightarrow> distinct (to_sorted_list s)"
    "invar s \<Longrightarrow> sorted (to_sorted_list s)"

  locale set_to_rev_list = ordered_set + 
  constrains \<alpha> :: "'s \<Rightarrow> 'x::linorder set"
  fixes to_rev_list :: "'s \<Rightarrow> 'x list"
  assumes to_rev_list_correct: 
    "invar s \<Longrightarrow> set (to_rev_list s) = \<alpha> s"
    "invar s \<Longrightarrow> distinct (to_rev_list s)"
    "invar s \<Longrightarrow> sorted (rev (to_rev_list s))"

subsection "Record Based Interface"
  record ('x,'s) set_ops = 
    set_op_\<alpha> :: "'s \<Rightarrow> 'x set"
    set_op_invar :: "'s \<Rightarrow> bool"
    set_op_empty :: "unit \<Rightarrow> 's"
    set_op_memb :: "'x \<Rightarrow> 's \<Rightarrow> bool"
    set_op_ins :: "'x \<Rightarrow> 's \<Rightarrow> 's"
    set_op_ins_dj :: "'x \<Rightarrow> 's \<Rightarrow> 's"
    set_op_delete :: "'x \<Rightarrow> 's \<Rightarrow> 's"
    set_op_list_it :: "('x,'s) set_list_it"
    set_op_sng :: "'x \<Rightarrow> 's"
    set_op_isEmpty :: "'s \<Rightarrow> bool"
    set_op_isSng :: "'s \<Rightarrow> bool"
    set_op_ball :: "'s \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> bool"
    set_op_bex :: "'s \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> bool"
    set_op_size :: "'s \<Rightarrow> nat"
    set_op_size_abort :: "nat \<Rightarrow> 's \<Rightarrow> nat"
    set_op_union :: "'s \<Rightarrow> 's \<Rightarrow> 's"
    set_op_union_dj :: "'s \<Rightarrow> 's \<Rightarrow> 's"
    set_op_diff :: "'s \<Rightarrow> 's \<Rightarrow> 's"
    set_op_filter :: "('x \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's"
    set_op_inter :: "'s \<Rightarrow> 's \<Rightarrow> 's"
    set_op_subset :: "'s \<Rightarrow> 's \<Rightarrow> bool"
    set_op_equal :: "'s \<Rightarrow> 's \<Rightarrow> bool"
    set_op_disjoint :: "'s \<Rightarrow> 's \<Rightarrow> bool"
    set_op_disjoint_witness :: "'s \<Rightarrow> 's \<Rightarrow> 'x option"
    set_op_sel :: "'s \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> 'x option" \<comment> \<open>Version without mapping\<close>
    set_op_to_list :: "'s \<Rightarrow> 'x list"
    set_op_from_list :: "'x list \<Rightarrow> 's"

  locale StdSetDefs = 
    poly_set_iteratei_defs "set_op_list_it ops"
    for ops :: "('x,'s,'more) set_ops_scheme"
  begin
    abbreviation \<alpha> where "\<alpha> == set_op_\<alpha> ops"
    abbreviation invar where "invar == set_op_invar ops"
    abbreviation empty where "empty == set_op_empty ops"
    abbreviation memb where "memb == set_op_memb ops"
    abbreviation ins where "ins == set_op_ins ops"
    abbreviation ins_dj where "ins_dj == set_op_ins_dj ops"
    abbreviation delete where "delete == set_op_delete ops"
    abbreviation list_it where "list_it \<equiv> set_op_list_it ops"
    abbreviation sng where "sng == set_op_sng ops"
    abbreviation isEmpty where "isEmpty == set_op_isEmpty ops"
    abbreviation isSng where "isSng == set_op_isSng ops"
    abbreviation ball where "ball == set_op_ball ops"
    abbreviation bex where "bex == set_op_bex ops"
    abbreviation size where "size == set_op_size ops"
    abbreviation size_abort where "size_abort == set_op_size_abort ops"
    abbreviation union where "union == set_op_union ops"
    abbreviation union_dj where "union_dj == set_op_union_dj ops"
    abbreviation diff where "diff == set_op_diff ops"
    abbreviation filter where "filter == set_op_filter ops"
    abbreviation inter where "inter == set_op_inter ops"
    abbreviation subset where "subset == set_op_subset ops"
    abbreviation equal where "equal == set_op_equal ops"
    abbreviation disjoint where "disjoint == set_op_disjoint ops"
    abbreviation disjoint_witness 
      where "disjoint_witness == set_op_disjoint_witness ops"
    abbreviation sel where "sel == set_op_sel ops"
    abbreviation to_list where "to_list == set_op_to_list ops"
    abbreviation from_list where "from_list == set_op_from_list ops"
  end

  locale StdSet = StdSetDefs ops +
    set \<alpha> invar +
    set_empty \<alpha> invar empty + 
    set_memb \<alpha> invar memb + 
    set_ins \<alpha> invar ins + 
    set_ins_dj \<alpha> invar ins_dj +
    set_delete \<alpha> invar delete + 
    poly_set_iteratei \<alpha> invar list_it +
    set_sng \<alpha> invar sng + 
    set_isEmpty \<alpha> invar isEmpty + 
    set_isSng \<alpha> invar isSng + 
    set_ball \<alpha> invar ball + 
    set_bex \<alpha> invar bex + 
    set_size \<alpha> invar size + 
    set_size_abort \<alpha> invar size_abort + 
    set_union \<alpha> invar \<alpha> invar \<alpha> invar union + 
    set_union_dj \<alpha> invar \<alpha> invar \<alpha> invar union_dj + 
    set_diff \<alpha> invar \<alpha> invar diff + 
    set_filter \<alpha> invar \<alpha> invar filter +  
    set_inter \<alpha> invar \<alpha> invar \<alpha> invar inter + 
    set_subset \<alpha> invar \<alpha> invar subset + 
    set_equal \<alpha> invar \<alpha> invar equal + 
    set_disjoint \<alpha> invar \<alpha> invar disjoint + 
    set_disjoint_witness \<alpha> invar \<alpha> invar disjoint_witness + 
    set_sel' \<alpha> invar sel + 
    set_to_list \<alpha> invar to_list + 
    list_to_set \<alpha> invar from_list
    for ops :: "('x,'s,'more) set_ops_scheme"
  begin

    lemmas correct = 
      empty_correct
      sng_correct
      memb_correct
      ins_correct
      ins_dj_correct
      delete_correct
      isEmpty_correct
      isSng_correct
      ball_correct
      bex_correct
      size_correct
      size_abort_correct
      union_correct
      union_dj_correct
      diff_correct
      filter_correct
      inter_correct
      subset_correct
      equal_correct
      disjoint_correct
      disjoint_witness_correct
      to_list_correct
      to_set_correct

  end

  lemmas StdSet_intro = StdSet.intro[rem_dup_prems]

  locale StdSet_no_invar = StdSet + set_no_invar \<alpha> invar

  record ('x,'s) oset_ops = "('x::linorder,'s) set_ops" +
    set_op_ordered_list_it :: "'s \<Rightarrow> ('x,'x list) set_iterator"
    set_op_rev_list_it :: "'s \<Rightarrow> ('x,'x list) set_iterator"
    set_op_min :: "'s \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> 'x option"
    set_op_max :: "'s \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> 'x option"
    set_op_to_sorted_list :: "'s \<Rightarrow> 'x list"
    set_op_to_rev_list :: "'s \<Rightarrow> 'x list"
    
  locale StdOSetDefs = StdSetDefs ops
    + poly_set_iterateoi_defs "set_op_ordered_list_it ops"
    + poly_set_rev_iterateoi_defs "set_op_rev_list_it ops"
    for ops :: "('x::linorder,'s,'more) oset_ops_scheme"
  begin
    abbreviation "ordered_list_it \<equiv> set_op_ordered_list_it ops"
    abbreviation "rev_list_it \<equiv> set_op_rev_list_it ops"
    abbreviation min where "min == set_op_min ops"
    abbreviation max where "max == set_op_max ops"
    abbreviation to_sorted_list where 
      "to_sorted_list \<equiv> set_op_to_sorted_list ops"
    abbreviation to_rev_list where "to_rev_list \<equiv> set_op_to_rev_list ops"
  end

  locale StdOSet =
    StdOSetDefs ops +
    StdSet ops +
    poly_set_iterateoi \<alpha> invar ordered_list_it +
    poly_set_rev_iterateoi \<alpha> invar rev_list_it +
    set_min \<alpha> invar min +
    set_max \<alpha> invar max +
    set_to_sorted_list \<alpha> invar to_sorted_list +
    set_to_rev_list \<alpha> invar to_rev_list
    for ops :: "('x::linorder,'s,'more) oset_ops_scheme"
  begin
  end

  lemmas StdOSet_intro =
    StdOSet.intro[OF StdSet_intro, rem_dup_prems]

no_notation insert ("set'_ins")
(*notation member (infixl "mem" 55)*)

end
