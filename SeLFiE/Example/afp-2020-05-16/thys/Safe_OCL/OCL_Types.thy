(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Types\<close>
theory OCL_Types
  imports OCL_Basic_Types Errorable Tuple
begin

(*** Definition *************************************************************)

section \<open>Definition\<close>

text \<open>
  Types are parameterized over classes.\<close>

type_synonym telem = String.literal

datatype (plugins del: size) 'a type =
  OclSuper
| Required "'a basic_type" ("_[1]" [1000] 1000)
| Optional "'a basic_type" ("_[?]" [1000] 1000)
| Collection "'a type"
| Set "'a type"
| OrderedSet "'a type"
| Bag "'a type"
| Sequence "'a type"
| Tuple "telem \<rightharpoonup>\<^sub>f 'a type"

text \<open>
  We define the @{text OclInvalid} type separately, because we
  do not need types like @{text "Set(OclInvalid)"} in the theory.
  The @{text "OclVoid[1]"} type is not equal to @{text OclInvalid}.
  For example, @{text "Set(OclVoid[1])"} could theoretically be
  a valid type of the following expression:\<close>

text \<open>
\<^verbatim>\<open>Set{null}->excluding(null)\<close>\<close>

definition "OclInvalid :: 'a type\<^sub>\<bottom> \<equiv> \<bottom>"

instantiation type :: (type) size
begin

primrec size_type :: "'a type \<Rightarrow> nat" where
  "size_type OclSuper = 0"
| "size_type (Required \<tau>) = 0"
| "size_type (Optional \<tau>) = 0"
| "size_type (Collection \<tau>) = Suc (size_type \<tau>)"
| "size_type (Set \<tau>) = Suc (size_type \<tau>)"
| "size_type (OrderedSet \<tau>) = Suc (size_type \<tau>)"
| "size_type (Bag \<tau>) = Suc (size_type \<tau>)"
| "size_type (Sequence \<tau>) = Suc (size_type \<tau>)"
| "size_type (Tuple \<pi>) = Suc (ffold tcf 0 (fset_of_fmap (fmmap size_type \<pi>)))"

instance ..

end

inductive subtype :: "'a::order type \<Rightarrow> 'a type \<Rightarrow> bool" (infix "\<sqsubset>" 65) where
  "\<tau> \<sqsubset>\<^sub>B \<sigma> \<Longrightarrow> \<tau>[1] \<sqsubset> \<sigma>[1]"
| "\<tau> \<sqsubset>\<^sub>B \<sigma> \<Longrightarrow> \<tau>[?] \<sqsubset> \<sigma>[?]"
| "\<tau>[1] \<sqsubset> \<tau>[?]"
| "OclAny[?] \<sqsubset> OclSuper"

| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Collection \<tau> \<sqsubset> Collection \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Set \<tau> \<sqsubset> Set \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> OrderedSet \<tau> \<sqsubset> OrderedSet \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Bag \<tau> \<sqsubset> Bag \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Sequence \<tau> \<sqsubset> Sequence \<sigma>"
| "Set \<tau> \<sqsubset> Collection \<tau>"
| "OrderedSet \<tau> \<sqsubset> Collection \<tau>"
| "Bag \<tau> \<sqsubset> Collection \<tau>"
| "Sequence \<tau> \<sqsubset> Collection \<tau>"
| "Collection OclSuper \<sqsubset> OclSuper"

| "strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi> \<Longrightarrow>
   Tuple \<pi> \<sqsubset> Tuple \<xi>"
| "Tuple \<pi> \<sqsubset> OclSuper"

declare subtype.intros [intro!]

inductive_cases subtype_x_OclSuper [elim!]: "\<tau> \<sqsubset> OclSuper"
inductive_cases subtype_x_Required [elim!]: "\<tau> \<sqsubset> \<sigma>[1]"
inductive_cases subtype_x_Optional [elim!]: "\<tau> \<sqsubset> \<sigma>[?]"
inductive_cases subtype_x_Collection [elim!]: "\<tau> \<sqsubset> Collection \<sigma>"
inductive_cases subtype_x_Set [elim!]: "\<tau> \<sqsubset> Set \<sigma>"
inductive_cases subtype_x_OrderedSet [elim!]: "\<tau> \<sqsubset> OrderedSet \<sigma>"
inductive_cases subtype_x_Bag [elim!]: "\<tau> \<sqsubset> Bag \<sigma>"
inductive_cases subtype_x_Sequence [elim!]: "\<tau> \<sqsubset> Sequence \<sigma>"
inductive_cases subtype_x_Tuple [elim!]: "\<tau> \<sqsubset> Tuple \<pi>"

inductive_cases subtype_OclSuper_x [elim!]: "OclSuper \<sqsubset> \<sigma>"
inductive_cases subtype_Collection_x [elim!]: "Collection \<tau> \<sqsubset> \<sigma>"

lemma subtype_asym:
  "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> \<sigma> \<sqsubset> \<tau> \<Longrightarrow> False"
  apply (induct rule: subtype.induct)
  using basic_subtype_asym apply auto
  using subtuple_antisym by fastforce

(*** Constructors Bijectivity on Transitive Closures ************************)

section \<open>Constructors Bijectivity on Transitive Closures\<close>

lemma Required_bij_on_trancl [simp]:
  "bij_on_trancl subtype Required"
  by (auto simp add: inj_def)

lemma not_subtype_Optional_Required:
  "subtype\<^sup>+\<^sup>+ \<tau>[?] \<sigma> \<Longrightarrow> \<sigma> = \<rho>[1] \<Longrightarrow> P"
  by (induct arbitrary: \<rho> rule: tranclp_induct; auto)

lemma Optional_bij_on_trancl [simp]:
  "bij_on_trancl subtype Optional"
  apply (auto simp add: inj_def)
  using not_subtype_Optional_Required by blast

lemma subtype_tranclp_Collection_x:
  "subtype\<^sup>+\<^sup>+ (Collection \<tau>) \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> subtype\<^sup>+\<^sup>+ \<tau> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = OclSuper \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct, auto)
  by (metis subtype_Collection_x subtype_OclSuper_x tranclp.trancl_into_trancl)

lemma Collection_bij_on_trancl [simp]:
  "bij_on_trancl subtype Collection"
  apply (auto simp add: inj_def)
  using subtype_tranclp_Collection_x by auto

lemma Set_bij_on_trancl [simp]:
  "bij_on_trancl subtype Set"
  by (auto simp add: inj_def)

lemma OrderedSet_bij_on_trancl [simp]:
  "bij_on_trancl subtype OrderedSet"
  by (auto simp add: inj_def)

lemma Bag_bij_on_trancl [simp]:
  "bij_on_trancl subtype Bag"
  by (auto simp add: inj_def)

lemma Sequence_bij_on_trancl [simp]:
  "bij_on_trancl subtype Sequence"
  by (auto simp add: inj_def)

lemma Tuple_bij_on_trancl [simp]:
  "bij_on_trancl subtype Tuple"
  by (auto simp add: inj_def)

(*** Partial Order of Types *************************************************)

section \<open>Partial Order of Types\<close>

instantiation type :: (order) order
begin

definition "(<) \<equiv> subtype\<^sup>+\<^sup>+"
definition "(\<le>) \<equiv> subtype\<^sup>*\<^sup>*"

(*** Strict Introduction Rules **********************************************)

subsection \<open>Strict Introduction Rules\<close>

lemma type_less_x_Required_intro [intro]:
  "\<tau> = \<rho>[1] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < \<sigma>[1]"
  unfolding less_type_def less_basic_type_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_Optional_intro [intro]:
  "\<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < \<sigma>[?]"
  "\<tau> = \<rho>[?] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < \<sigma>[?]"
  unfolding less_type_def less_basic_type_def less_eq_basic_type_def
  apply simp_all
  apply (rule preserve_rtranclp''; auto)
  by (rule preserve_tranclp; auto)

lemma type_less_x_Collection_intro [intro]:
  "\<tau> = Collection \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  unfolding less_type_def less_eq_type_def
  apply simp_all
  apply (rule_tac ?f="Collection" in preserve_tranclp; auto)
  apply (rule preserve_rtranclp''; auto)
  apply (rule preserve_rtranclp''; auto)
  apply (rule preserve_rtranclp''; auto)
  by (rule preserve_rtranclp''; auto)

lemma type_less_x_Set_intro [intro]:
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Set \<sigma>"
  unfolding less_type_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_OrderedSet_intro [intro]:
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < OrderedSet \<sigma>"
  unfolding less_type_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_Bag_intro [intro]:
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Bag \<sigma>"
  unfolding less_type_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_Sequence_intro [intro]:
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Sequence \<sigma>"
  unfolding less_type_def
  by simp (rule preserve_tranclp; auto)

lemma fun_or_eq_refl [intro]:
  "reflp (\<lambda>x y. f x y \<or> x = y)"
  by (simp add: reflpI)

lemma type_less_x_Tuple_intro [intro]:
  assumes "\<tau> = Tuple \<pi>"
      and "strict_subtuple (\<le>) \<pi> \<xi>"
    shows "\<tau> < Tuple \<xi>"
proof -
  have "subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset> \<sigma> \<or> \<tau> = \<sigma>)\<^sup>*\<^sup>* \<pi> \<xi>"
    using assms(2) less_eq_type_def by auto
  hence "(subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset> \<sigma> \<or> \<tau> = \<sigma>))\<^sup>+\<^sup>+ \<pi> \<xi>"
    by simp (rule subtuple_to_trancl; auto)
  hence "(strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset> \<sigma> \<or> \<tau> = \<sigma>))\<^sup>*\<^sup>* \<pi> \<xi>"
    by (simp add: tranclp_into_rtranclp)
  hence "(strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset> \<sigma> \<or> \<tau> = \<sigma>))\<^sup>+\<^sup>+ \<pi> \<xi>"
    by (meson assms(2) rtranclpD)
  thus ?thesis
    unfolding less_type_def
    using assms(1) apply simp
    by (rule preserve_tranclp; auto)
qed

lemma type_less_x_OclSuper_intro [intro]:
  "\<tau> \<noteq> OclSuper \<Longrightarrow> \<tau> < OclSuper"
  unfolding less_type_def
proof (induct \<tau>)
  case OclSuper thus ?case by auto
next
  case (Required \<tau>)
  have "subtype\<^sup>*\<^sup>* \<tau>[1] OclAny[1]"
    apply (rule_tac ?f="Required" in preserve_rtranclp[of basic_subtype], auto)
    by (metis less_eq_basic_type_def type_less_eq_x_OclAny_intro)
  also have "subtype\<^sup>+\<^sup>+ OclAny[1] OclAny[?]" by auto
  also have "subtype\<^sup>+\<^sup>+ OclAny[?] OclSuper" by auto
  finally show ?case by auto
next
  case (Optional \<tau>)
  have "subtype\<^sup>*\<^sup>* \<tau>[?] OclAny[?]"
    apply (rule_tac ?f="Optional" in preserve_rtranclp[of basic_subtype], auto)
    by (metis less_eq_basic_type_def type_less_eq_x_OclAny_intro)
  also have "subtype\<^sup>+\<^sup>+ OclAny[?] OclSuper" by auto
  finally show ?case by auto
next
  case (Collection \<tau>)
  have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    apply (rule_tac ?f="Collection" in preserve_rtranclp[of subtype], auto)
    using Collection.hyps by force
  also have "subtype\<^sup>+\<^sup>+ (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (Set \<tau>)
  have "subtype\<^sup>+\<^sup>+ (Set \<tau>) (Collection \<tau>)" by auto
  also have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    apply (rule_tac ?f="Collection" in preserve_rtranclp[of subtype], auto)
    using Set.hyps by force
  also have "subtype\<^sup>*\<^sup>* (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (OrderedSet \<tau>)
  have "subtype\<^sup>+\<^sup>+ (OrderedSet \<tau>) (Collection \<tau>)" by auto
  also have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    apply (rule_tac ?f="Collection" in preserve_rtranclp[of subtype], auto)
    using OrderedSet.hyps by force
  also have "subtype\<^sup>*\<^sup>* (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (Bag \<tau>)
  have "subtype\<^sup>+\<^sup>+ (Bag \<tau>) (Collection \<tau>)" by auto
  also have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    apply (rule_tac ?f="Collection" in preserve_rtranclp[of subtype], auto)
    using Bag.hyps by force
  also have "subtype\<^sup>*\<^sup>* (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (Sequence \<tau>)
  have "subtype\<^sup>+\<^sup>+ (Sequence \<tau>) (Collection \<tau>)" by auto
  also have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    apply (rule_tac ?f="Collection" in preserve_rtranclp[of subtype], auto)
    using Sequence.hyps by force
  also have "subtype\<^sup>*\<^sup>* (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (Tuple x) thus ?case by auto
qed

(*** Strict Elimination Rules ***********************************************)

subsection \<open>Strict Elimination Rules\<close>

lemma type_less_x_Required [elim!]:
  assumes "\<tau> < \<sigma>[1]"
      and "\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = \<rho>[1]"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. \<tau>[1] < \<sigma>[1] \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_basic_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed
(*
lemma type_less_x_Optional [elim!]:
  assumes "\<tau> < \<sigma>[?]"
      and "\<tau> = OclVoid \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where
    "\<tau> = OclVoid \<or> \<tau> = \<rho>[1] \<or> \<tau> = \<rho>[?]"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. \<tau>[1] < \<sigma>[?] \<Longrightarrow> \<tau> \<le> \<sigma>"
    unfolding less_type_def less_eq_basic_type_def
    apply (drule tranclpD, auto)
    apply (erule subtype.cases, auto)
  moreover have "\<And>\<tau> \<sigma>. \<tau>[?] < \<sigma>[?] \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_basic_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed
*)
lemma type_less_x_Optional [elim!]:
  "\<tau> < \<sigma>[?] \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: converse_tranclp_induct)
  apply (metis subtype_x_Optional eq_refl less_basic_type_def tranclp.r_into_trancl)
  apply (erule subtype.cases; auto)
  apply (simp add: converse_rtranclp_into_rtranclp less_eq_basic_type_def)
  by (simp add: less_basic_type_def tranclp_into_tranclp2)

lemma type_less_x_Collection [elim!]:
  "\<tau> < Collection \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: converse_tranclp_induct)
  apply (metis (mono_tags) Nitpick.rtranclp_unfold
          subtype_x_Collection less_eq_type_def tranclp.r_into_trancl)
  by (erule subtype.cases;
      auto simp add: converse_rtranclp_into_rtranclp less_eq_type_def
                     tranclp_into_tranclp2 tranclp_into_rtranclp)

lemma type_less_x_Set [elim!]:
  assumes "\<tau> < Set \<sigma>"
      and "\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Set \<rho>"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Set \<tau> < Set \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_OrderedSet [elim!]:
  assumes "\<tau> < OrderedSet \<sigma>"
      and "\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = OrderedSet \<rho>"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. OrderedSet \<tau> < OrderedSet \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_Bag [elim!]:
  assumes "\<tau> < Bag \<sigma>"
      and "\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Bag \<rho>"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Bag \<tau> < Bag \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_Sequence [elim!]:
  assumes "\<tau> < Sequence \<sigma>"
      and "\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Sequence \<rho>"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Sequence \<tau> < Sequence \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

text \<open>
  We will be able to remove the acyclicity assumption only after
  we prove that the subtype relation is acyclic.\<close>

lemma type_less_x_Tuple':
  assumes "\<tau> < Tuple \<xi>"
      and "acyclicP_on (fmran' \<xi>) subtype"
      and "\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<pi> where "\<tau> = Tuple \<pi>"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover from assms(2) have
    "\<And>\<pi>. Tuple \<pi> < Tuple \<xi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi>"
    unfolding less_type_def less_eq_type_def
    by (rule_tac ?f="Tuple" in strict_subtuple_rtranclp_intro; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_OclSuper [elim!]:
  "\<tau> < OclSuper \<Longrightarrow> (\<tau> \<noteq> OclSuper \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (drule tranclpD, auto)

(*** Properties *************************************************************)

subsection \<open>Properties\<close>

lemma subtype_irrefl:
  "\<tau> < \<tau> \<Longrightarrow> False"
  for \<tau> :: "'a type"
  apply (induct \<tau>, auto)
  apply (erule type_less_x_Tuple', auto)
  unfolding less_type_def tranclp_unfold
  by auto

lemma subtype_acyclic:
  "acyclicP subtype"
  apply (rule acyclicI)
  apply (simp add: trancl_def)
  by (metis (mono_tags) OCL_Types.less_type_def OCL_Types.subtype_irrefl)

lemma less_le_not_le_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: "'a type"
proof
  show "\<tau> < \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
    apply (auto simp add: less_type_def less_eq_type_def)
    by (metis (mono_tags) subtype_irrefl less_type_def tranclp_rtranclp_tranclp)
  show "\<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> < \<sigma>"
    apply (auto simp add: less_type_def less_eq_type_def)
    by (metis rtranclpD)
qed

lemma order_refl_type [iff]:
  "\<tau> \<le> \<tau>"
  for \<tau> :: "'a type"
  unfolding less_eq_type_def by simp

lemma order_trans_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type"
  unfolding less_eq_type_def by simp

lemma antisym_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: "'a type"
  unfolding less_eq_type_def less_type_def
  by (metis (mono_tags, lifting) less_eq_type_def
      less_le_not_le_type less_type_def rtranclpD)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_type)
  apply (simp)
  using order_trans_type apply blast
  by (simp add: antisym_type)

end

(*** Non-Strict Introduction Rules ******************************************)

subsection \<open>Non-Strict Introduction Rules\<close>

lemma type_less_eq_x_Required_intro [intro]:
  "\<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[1]"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Optional_intro [intro]:
  "\<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  "\<tau> = \<rho>[?] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Collection_intro [intro]:
  "\<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Set_intro [intro]:
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Set \<sigma>"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_OrderedSet_intro [intro]:
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> OrderedSet \<sigma>"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Bag_intro [intro]:
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Bag \<sigma>"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Sequence_intro [intro]:
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Sequence \<sigma>"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Tuple_intro [intro]:
  "\<tau> = Tuple \<pi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> \<tau> \<le> Tuple \<xi>"
  using dual_order.strict_iff_order by blast

lemma type_less_eq_x_OclSuper_intro [intro]:
  "\<tau> \<le> OclSuper"
  unfolding dual_order.order_iff_strict by auto

(*** Non-Strict Elimination Rules *******************************************)

subsection \<open>Non-Strict Elimination Rules\<close>

lemma type_less_eq_x_Required [elim!]:
  "\<tau> \<le> \<sigma>[1] \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Optional [elim!]:
  "\<tau> \<le> \<sigma>[?] \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq, auto)

lemma type_less_eq_x_Collection [elim!]:
  "\<tau> \<le> Collection \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Set [elim!]:
   "\<tau> \<le> Set \<sigma> \<Longrightarrow>
    (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_OrderedSet [elim!]:
   "\<tau> \<le> OrderedSet \<sigma> \<Longrightarrow>
    (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Bag [elim!]:
   "\<tau> \<le> Bag \<sigma> \<Longrightarrow>
    (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Sequence [elim!]:
   "\<tau> \<le> Sequence \<sigma> \<Longrightarrow>
    (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_x_Tuple [elim!]:
  "\<tau> < Tuple \<xi> \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (erule type_less_x_Tuple')
  by (meson acyclic_def subtype_acyclic)

lemma type_less_eq_x_Tuple [elim!]:
  "\<tau> \<le> Tuple \<xi> \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule le_imp_less_or_eq, auto)
  by (simp add: fmap.rel_refl fmrel_to_subtuple)

(*** Simplification Rules ***************************************************)

subsection \<open>Simplification Rules\<close>

lemma type_less_left_simps [simp]:
  "OclSuper < \<sigma> = False"
  "\<rho>[1] < \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = OclSuper \<or>
      \<sigma> = \<upsilon>[1] \<and> \<rho> < \<upsilon> \<or>
      \<sigma> = \<upsilon>[?] \<and> \<rho> \<le> \<upsilon>)"
  "\<rho>[?] < \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = OclSuper \<or>
      \<sigma> = \<upsilon>[?] \<and> \<rho> < \<upsilon>)"
  "Collection \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclSuper \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> < \<phi>)"
  "Set \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclSuper \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = Set \<phi> \<and> \<tau> < \<phi>)"
  "OrderedSet \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclSuper \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = OrderedSet \<phi> \<and> \<tau> < \<phi>)"
  "Bag \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclSuper \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = Bag \<phi> \<and> \<tau> < \<phi>)"
  "Sequence \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclSuper \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = Sequence \<phi> \<and> \<tau> < \<phi>)"
  "Tuple \<pi> < \<sigma> = (\<exists>\<xi>.
      \<sigma> = OclSuper \<or>
      \<sigma> = Tuple \<xi> \<and> strict_subtuple (\<le>) \<pi> \<xi>)"
  by (induct \<sigma>; auto)+

lemma type_less_right_simps [simp]:
  "\<tau> < OclSuper = (\<tau> \<noteq> OclSuper)"
  "\<tau> < \<upsilon>[1] = (\<exists>\<rho>. \<tau> = \<rho>[1] \<and> \<rho> < \<upsilon>)"
  "\<tau> < \<upsilon>[?] = (\<exists>\<rho>. \<tau> = \<rho>[1] \<and> \<rho> \<le> \<upsilon> \<or> \<tau> = \<rho>[?] \<and> \<rho> < \<upsilon>)"
  "\<tau> < Collection \<sigma> = (\<exists>\<phi>.
      \<tau> = Collection \<phi> \<and> \<phi> < \<sigma> \<or>
      \<tau> = Set \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = OrderedSet \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = Bag \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = Sequence \<phi> \<and> \<phi> \<le> \<sigma>)"
  "\<tau> < Set \<sigma> = (\<exists>\<phi>. \<tau> = Set \<phi> \<and> \<phi> < \<sigma>)"
  "\<tau> < OrderedSet \<sigma> = (\<exists>\<phi>. \<tau> = OrderedSet \<phi> \<and> \<phi> < \<sigma>)"
  "\<tau> < Bag \<sigma> = (\<exists>\<phi>. \<tau> = Bag \<phi> \<and> \<phi> < \<sigma>)"
  "\<tau> < Sequence \<sigma> = (\<exists>\<phi>. \<tau> = Sequence \<phi> \<and> \<phi> < \<sigma>)"
  "\<tau> < Tuple \<xi> = (\<exists>\<pi>. \<tau> = Tuple \<pi> \<and> strict_subtuple (\<le>) \<pi> \<xi>)"
  by auto

(*** Upper Semilattice of Types *********************************************)

section \<open>Upper Semilattice of Types\<close>

instantiation type :: (semilattice_sup) semilattice_sup
begin

fun sup_type where
  "OclSuper \<squnion> \<sigma> = OclSuper"
| "Required \<tau> \<squnion> \<sigma> = (case \<sigma>
    of \<rho>[1] \<Rightarrow> (\<tau> \<squnion> \<rho>)[1]
     | \<rho>[?] \<Rightarrow> (\<tau> \<squnion> \<rho>)[?]
     | _ \<Rightarrow> OclSuper)"
| "Optional \<tau> \<squnion> \<sigma> = (case \<sigma>
    of \<rho>[1] \<Rightarrow> (\<tau> \<squnion> \<rho>)[?]
     | \<rho>[?] \<Rightarrow> (\<tau> \<squnion> \<rho>)[?]
     | _ \<Rightarrow> OclSuper)"
| "Collection \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "Set \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Set \<rho> \<Rightarrow> Set (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "OrderedSet \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> OrderedSet (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "Bag \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Bag (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "Sequence \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Sequence (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "Tuple \<pi> \<squnion> \<sigma> = (case \<sigma>
    of Tuple \<xi> \<Rightarrow> Tuple (fmmerge_fun (\<squnion>) \<pi> \<xi>)
     | _ \<Rightarrow> OclSuper)"

lemma sup_ge1_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: "'a type"
proof (induct \<tau> arbitrary: \<sigma>)
  case OclSuper show ?case by simp
  case (Required \<tau>) show ?case by (induct \<sigma>; auto)
  case (Optional \<tau>) show ?case by (induct \<sigma>; auto)
  case (Collection \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Set \<tau>) thus ?case by (induct \<sigma>; auto)
  case (OrderedSet \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Bag \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Sequence \<tau>) thus ?case by (induct \<sigma>; auto)
next
  case (Tuple \<pi>)
  moreover have Tuple_less_eq_sup:
    "(\<And>\<tau> \<sigma>. \<tau> \<in> fmran' \<pi> \<Longrightarrow> \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
     Tuple \<pi> \<le> Tuple \<pi> \<squnion> \<sigma>"
    by (cases \<sigma>, auto)
  ultimately show ?case by (cases \<sigma>, auto)
qed

lemma sup_commut_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: "'a type"
proof (induct \<tau> arbitrary: \<sigma>)
  case OclSuper show ?case by (cases \<sigma>; simp add: less_eq_type_def)
  case (Required \<tau>) show ?case by (cases \<sigma>; simp add: sup_commute)
  case (Optional \<tau>) show ?case by (cases \<sigma>; simp add: sup_commute)
  case (Collection \<tau>) thus ?case by (cases \<sigma>; simp)
  case (Set \<tau>) thus ?case by (cases \<sigma>; simp)
  case (OrderedSet \<tau>) thus ?case by (cases \<sigma>; simp)
  case (Bag \<tau>) thus ?case by (cases \<sigma>; simp)
  case (Sequence \<tau>) thus ?case by (cases \<sigma>; simp)
next
  case (Tuple \<pi>) thus ?case
    apply (cases \<sigma>; simp add: less_eq_type_def)
    using fmmerge_commut by blast
qed

lemma sup_least_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type"
proof (induct \<rho> arbitrary: \<tau> \<sigma>)
  case OclSuper show ?case using eq_refl by auto
next
  case (Required x) show ?case
    apply (insert Required)
    by (erule type_less_eq_x_Required; erule type_less_eq_x_Required; auto)
next
  case (Optional x) show ?case
    apply (insert Optional)
    by (erule type_less_eq_x_Optional; erule type_less_eq_x_Optional; auto)
next
  case (Collection \<rho>) show ?case
    apply (insert Collection)
    by (erule type_less_eq_x_Collection; erule type_less_eq_x_Collection; auto)
next
  case (Set \<rho>) show ?case
    apply (insert Set)
    by (erule type_less_eq_x_Set; erule type_less_eq_x_Set; auto)
next
  case (OrderedSet \<rho>) show ?case
    apply (insert OrderedSet)
    by (erule type_less_eq_x_OrderedSet; erule type_less_eq_x_OrderedSet; auto)
next
  case (Bag \<rho>) show ?case
    apply (insert Bag)
    by (erule type_less_eq_x_Bag; erule type_less_eq_x_Bag; auto)
next
  case (Sequence \<rho>) thus ?case
    apply (insert Sequence)
    by (erule type_less_eq_x_Sequence; erule type_less_eq_x_Sequence; auto)
next
  case (Tuple \<pi>) show ?case
    apply (insert Tuple)
    apply (erule type_less_eq_x_Tuple; erule type_less_eq_x_Tuple; auto)
    by (rule_tac ?\<pi>="(fmmerge (\<squnion>) \<pi>' \<pi>'')" in type_less_eq_x_Tuple_intro;
        simp add: fmrel_on_fset_fmmerge1)
qed

instance
  apply intro_classes
  apply (simp add: sup_ge1_type)
  apply (simp add: sup_commut_type sup_ge1_type)
  by (simp add: sup_least_type)

end

(*** Helper Relations *******************************************************)

section \<open>Helper Relations\<close>

abbreviation between ("_/ = _\<midarrow>_"  [51, 51, 51] 50) where
  "x = y\<midarrow>z \<equiv> y \<le> x \<and> x \<le> z"

inductive element_type where
  "element_type (Collection \<tau>) \<tau>"
| "element_type (Set \<tau>) \<tau>"
| "element_type (OrderedSet \<tau>) \<tau>"
| "element_type (Bag \<tau>) \<tau>"
| "element_type (Sequence \<tau>) \<tau>"

lemma element_type_alt_simps:
  "element_type \<tau> \<sigma> = 
     (Collection \<sigma> = \<tau> \<or>
      Set \<sigma> = \<tau> \<or>
      OrderedSet \<sigma> = \<tau> \<or>
      Bag \<sigma> = \<tau> \<or>
      Sequence \<sigma> = \<tau>)"
  by (auto simp add: element_type.simps)

inductive update_element_type where
  "update_element_type (Collection _) \<tau> (Collection \<tau>)"
| "update_element_type (Set _) \<tau> (Set \<tau>)"
| "update_element_type (OrderedSet _) \<tau> (OrderedSet \<tau>)"
| "update_element_type (Bag _) \<tau> (Bag \<tau>)"
| "update_element_type (Sequence _) \<tau> (Sequence \<tau>)"

inductive to_unique_collection where
  "to_unique_collection (Collection \<tau>) (Set \<tau>)"
| "to_unique_collection (Set \<tau>) (Set \<tau>)"
| "to_unique_collection (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "to_unique_collection (Bag \<tau>) (Set \<tau>)"
| "to_unique_collection (Sequence \<tau>) (OrderedSet \<tau>)"

inductive to_nonunique_collection where
  "to_nonunique_collection (Collection \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (Set \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (OrderedSet \<tau>) (Sequence \<tau>)"
| "to_nonunique_collection (Bag \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (Sequence \<tau>) (Sequence \<tau>)"

inductive to_ordered_collection where
  "to_ordered_collection (Collection \<tau>) (Sequence \<tau>)"
| "to_ordered_collection (Set \<tau>) (OrderedSet \<tau>)"
| "to_ordered_collection (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "to_ordered_collection (Bag \<tau>) (Sequence \<tau>)"
| "to_ordered_collection (Sequence \<tau>) (Sequence \<tau>)"

fun to_single_type where
  "to_single_type OclSuper = OclSuper"
| "to_single_type \<tau>[1] = \<tau>[1]"
| "to_single_type \<tau>[?] = \<tau>[?]"
| "to_single_type (Collection \<tau>) = to_single_type \<tau>"
| "to_single_type (Set \<tau>) = to_single_type \<tau>"
| "to_single_type (OrderedSet \<tau>) = to_single_type \<tau>"
| "to_single_type (Bag \<tau>) = to_single_type \<tau>"
| "to_single_type (Sequence \<tau>) = to_single_type \<tau>"
| "to_single_type (Tuple \<pi>) = Tuple \<pi>"

fun to_required_type where
  "to_required_type \<tau>[1] = \<tau>[1]"
| "to_required_type \<tau>[?] = \<tau>[1]"
| "to_required_type \<tau> = \<tau>"

fun to_optional_type_nested where
  "to_optional_type_nested OclSuper = OclSuper"
| "to_optional_type_nested \<tau>[1] = \<tau>[?]"
| "to_optional_type_nested \<tau>[?] = \<tau>[?]"
| "to_optional_type_nested (Collection \<tau>) = Collection (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (Set \<tau>) = Set (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (OrderedSet \<tau>) = OrderedSet (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (Bag \<tau>) = Bag (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (Sequence \<tau>) = Sequence (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (Tuple \<pi>) = Tuple (fmmap to_optional_type_nested \<pi>)"

(*** Determinism ************************************************************)

section \<open>Determinism\<close>

lemma element_type_det:
  "element_type \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   element_type \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: element_type.induct; simp add: element_type.simps)

lemma update_element_type_det:
  "update_element_type \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   update_element_type \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: update_element_type.induct; simp add: update_element_type.simps)

lemma to_unique_collection_det:
  "to_unique_collection \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   to_unique_collection \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: to_unique_collection.induct; simp add: to_unique_collection.simps)

lemma to_nonunique_collection_det:
  "to_nonunique_collection \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   to_nonunique_collection \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: to_nonunique_collection.induct; simp add: to_nonunique_collection.simps)

lemma to_ordered_collection_det:
  "to_ordered_collection \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   to_ordered_collection \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: to_ordered_collection.induct; simp add: to_ordered_collection.simps)

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred subtype .

function subtype_fun :: "'a::order type \<Rightarrow> 'a type \<Rightarrow> bool" where
  "subtype_fun OclSuper _ = False"
| "subtype_fun (Required \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | \<rho>[1] \<Rightarrow> basic_subtype_fun \<tau> \<rho>
     | \<rho>[?] \<Rightarrow> basic_subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Optional \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | \<rho>[?] \<Rightarrow> basic_subtype_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Collection \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Set \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | Set \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (OrderedSet \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | OrderedSet \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Bag \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | Bag \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Sequence \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | Sequence \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Tuple \<pi>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | Tuple \<xi> \<Rightarrow> strict_subtuple_fun (\<lambda>\<tau> \<sigma>. subtype_fun \<tau> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi>
     | _ \<Rightarrow> False)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(xs, ys). size ys)";
      auto simp add: elem_le_ffold' fmran'I)

lemma less_type_code [code]:
  "(<) = subtype_fun"
proof (intro ext iffI)
  fix \<tau> \<sigma> :: "'a type"
  show "\<tau> < \<sigma> \<Longrightarrow> subtype_fun \<tau> \<sigma>"
  proof (induct \<tau> arbitrary: \<sigma>)
    case OclSuper thus ?case by (cases \<sigma>; auto)
  next
    case (Required \<tau>) thus ?case
      by (cases \<sigma>; auto simp: less_basic_type_code less_eq_basic_type_code)
  next
    case (Optional \<tau>) thus ?case
      by (cases \<sigma>; auto simp: less_basic_type_code less_eq_basic_type_code)
  next
    case (Collection \<tau>) thus ?case by (cases \<sigma>; auto)
  next
    case (Set \<tau>) thus ?case by (cases \<sigma>; auto)
  next
    case (OrderedSet \<tau>) thus ?case by (cases \<sigma>; auto)
  next
    case (Bag \<tau>) thus ?case by (cases \<sigma>; auto)
  next
    case (Sequence \<tau>) thus ?case by (cases \<sigma>; auto)
  next
    case (Tuple \<pi>)
    have
      "\<And>\<xi>. subtuple (\<le>) \<pi> \<xi> \<longrightarrow>
       subtuple (\<lambda>\<tau> \<sigma>. subtype_fun \<tau> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi>"
      by (rule subtuple_mono; auto simp add: Tuple.hyps)
    with Tuple.prems show ?case by (cases \<sigma>; auto)
  qed
  show "subtype_fun \<tau> \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
  proof (induct \<sigma> arbitrary: \<tau>)
    case OclSuper thus ?case by (cases \<sigma>; auto)
  next
    case (Required \<sigma>) show ?case
      by (insert Required) (erule subtype_fun.elims;
          auto simp: less_basic_type_code less_eq_basic_type_code)
  next
    case (Optional \<sigma>) show ?case
      by (insert Optional) (erule subtype_fun.elims;
          auto simp: less_basic_type_code less_eq_basic_type_code)
  next
    case (Collection \<sigma>) show ?case
      apply (insert Collection)
      apply (erule subtype_fun.elims; auto)
      using order.strict_implies_order by auto
  next
    case (Set \<sigma>) show ?case
      by (insert Set) (erule subtype_fun.elims; auto)
  next
    case (OrderedSet \<sigma>) show ?case
      by (insert OrderedSet) (erule subtype_fun.elims; auto)
  next
    case (Bag \<sigma>) show ?case
      by (insert Bag) (erule subtype_fun.elims; auto)
  next
    case (Sequence \<sigma>) show ?case
      by (insert Sequence) (erule subtype_fun.elims; auto)
  next
    case (Tuple \<xi>)
    have subtuple_imp_simp:
      "\<And>\<pi>. subtuple (\<lambda>\<tau> \<sigma>. subtype_fun \<tau> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi> \<longrightarrow>
       subtuple (\<le>) \<pi> \<xi>"
      by (rule subtuple_mono; auto simp add: Tuple.hyps less_imp_le)
    show ?case
      apply (insert Tuple)
      by (erule subtype_fun.elims; auto simp add: subtuple_imp_simp)
  qed
qed

lemma less_eq_type_code [code]:
  "(\<le>) = (\<lambda>x y. subtype_fun x y \<or> x = y)"
  unfolding dual_order.order_iff_strict less_type_code
  by auto

code_pred element_type .
code_pred update_element_type .
code_pred to_unique_collection .
code_pred to_nonunique_collection .
code_pred to_ordered_collection .

end
