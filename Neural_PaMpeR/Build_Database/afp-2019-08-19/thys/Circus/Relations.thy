section\<open>Predicates and relations\<close>

theory Relations
imports Var
begin
default_sort type

text \<open>Unifying Theories of Programming (UTP) is a semantic framework based on 
an alphabetized relational calculus. An alphabetized predicate is a pair (alphabet, predicate) 
where the free variables appearing in the predicate are all in the alphabet.\<close>

text \<open>An alphabetized relation is an alphabetized predicate where the alphabet is
composed of input (undecorated) and output (dashed) variables. In this case the
predicate describes a relation between input and output variables.\<close>

subsection\<open>Definitions\<close>

text \<open>In this section, the definitions of predicates, relations and 
standard operators are given.\<close>

type_synonym '\<alpha> "alphabet"  = "'\<alpha>"
type_synonym '\<alpha> predicate = "'\<alpha> alphabet \<Rightarrow> bool"

definition  true::"'\<alpha> predicate"
where "true \<equiv> \<lambda>A. True"

definition  false::"'\<alpha> predicate"
where "false \<equiv> \<lambda>A. False"

definition  not::"'\<alpha> predicate \<Rightarrow> '\<alpha> predicate" ("\<not> _" [40] 40)
where "\<not> P  \<equiv> \<lambda>A. \<not> (P A)"

definition  conj::"'\<alpha> predicate \<Rightarrow> '\<alpha> predicate \<Rightarrow> '\<alpha> predicate" (infixr "\<and>" 35)
where "P \<and> Q \<equiv> \<lambda>A. P A \<and> Q A"

definition disj::"'\<alpha> predicate \<Rightarrow> '\<alpha> predicate \<Rightarrow> '\<alpha> predicate" (infixr "\<or>" 30)
where "P \<or> Q \<equiv> \<lambda>A. P A \<or> Q A"

definition impl::"'\<alpha> predicate \<Rightarrow> '\<alpha> predicate \<Rightarrow> '\<alpha> predicate" (infixr "\<longrightarrow>" 25)
where "P \<longrightarrow> Q \<equiv> \<lambda>A. P A \<longrightarrow> Q A"

definition iff::"'\<alpha> predicate \<Rightarrow> '\<alpha> predicate \<Rightarrow> '\<alpha> predicate" (infixr "\<longleftrightarrow>" 25)
where "P \<longleftrightarrow> Q \<equiv> \<lambda>A. P A \<longleftrightarrow> Q A"

definition ex::"['\<beta> \<Rightarrow>'\<alpha> predicate] \<Rightarrow> '\<alpha> predicate" (binder "\<^bold>\<exists>" 10)
where "\<^bold>\<exists>x. P x \<equiv> \<lambda>A. \<exists> x. (P x) A"

definition all::"['\<beta> \<Rightarrow>'\<alpha> predicate] \<Rightarrow> '\<alpha> predicate" (binder "\<^bold>\<forall>" 10)
where "\<^bold>\<forall>x. P x \<equiv> \<lambda> A. \<forall>x. (P x) A"

type_synonym '\<alpha> condition = "('\<alpha> \<times> '\<alpha>) \<Rightarrow> bool"
type_synonym '\<alpha> relation  = "('\<alpha> \<times> '\<alpha>) \<Rightarrow> bool"

definition cond::"'\<alpha> relation \<Rightarrow> '\<alpha> condition \<Rightarrow> '\<alpha> relation \<Rightarrow> '\<alpha> relation" 
                                                          ("(3_ \<triangleleft> _ \<triangleright> / _)" [14,0,15] 14)
where " (P \<triangleleft> b \<triangleright> Q) \<equiv> (b \<and> P) \<or> ((\<not> b) \<and> Q)"

definition comp::"(('\<alpha> \<times> '\<beta>) \<Rightarrow> bool) \<Rightarrow> (('\<beta> \<times> '\<gamma>) \<Rightarrow> bool) \<Rightarrow> ('\<alpha> \<times> '\<gamma>) \<Rightarrow> bool" 
                                                                          (infixr ";;" 25)
where "P ;; Q \<equiv> \<lambda>r. r : ({p. P p} O {q. Q q})"

definition Assign::"('a, 'b) var \<Rightarrow> 'a \<Rightarrow> 'b relation" 
  where "Assign x a \<equiv> \<lambda>(A, A'). A' = (assign x a) A"

syntax
  "_assignment" :: "id \<Rightarrow> 'a \<Rightarrow> 'b relation"  ("_ :== _")
translations
  "y :== vv"   => "CONST Assign (VAR y) vv"

abbreviation (input) closure::"'\<alpha> predicate \<Rightarrow> bool" ("[_]")
where "[ P ] \<equiv> \<forall> A. P A"

abbreviation (input) ndet::"'\<alpha> relation \<Rightarrow> '\<alpha> relation \<Rightarrow> '\<alpha> relation" ("(_ \<sqinter> _)")
where "P \<sqinter> Q \<equiv> P \<or> Q"

abbreviation (input) join::"'\<alpha> relation \<Rightarrow> '\<alpha> relation \<Rightarrow> '\<alpha> relation" ("(_ \<squnion> _)")
where "P \<squnion> Q \<equiv> P \<and> Q"

abbreviation (input) ndetS::"'\<alpha> relation set \<Rightarrow> '\<alpha> relation" ("(\<Sqinter> _)")
where "\<Sqinter> S \<equiv> \<lambda>A. A \<in> \<Union>{{p. P p} | P. P \<in> S}"

abbreviation (input) conjS::"'\<alpha> relation set \<Rightarrow> '\<alpha> relation" ("(\<Squnion> _)")
where "\<Squnion> S \<equiv> \<lambda>A. A \<in> \<Inter>{{p. P p} | P. P \<in> S}"

abbreviation (input) skip_r::"'\<alpha> relation" ("\<Pi>r")
where "\<Pi>r \<equiv> \<lambda> (A, A') . A = A'"

abbreviation (input) Bot::"'\<alpha> relation"
where "Bot \<equiv> true"

abbreviation (input) Top::"'\<alpha> relation"
where "Top \<equiv> false"


lemmas utp_defs = true_def false_def conj_def disj_def not_def impl_def iff_def
                  ex_def all_def cond_def comp_def Assign_def


subsection \<open>Proofs\<close>


text \<open>All useful proved lemmas over predicates and relations are presented here.
First, we introduce the most important lemmas that will be used by automatic tools to simplify
proofs. In the second part, other lemmas are proved using these basic ones.\<close>


subsubsection \<open>Setup of automated tools\<close>

lemma true_intro: "true x" by (simp add: utp_defs)
lemma false_elim: "false x \<Longrightarrow> C" by (simp add: utp_defs)
lemma true_elim: "true x \<Longrightarrow> C \<Longrightarrow> C" by (simp add: utp_defs)

lemma not_intro: "(P x \<Longrightarrow> false x) \<Longrightarrow> (\<not> P) x" by (auto simp add: utp_defs)
lemma not_elim: "(\<not> P) x \<Longrightarrow> P x \<Longrightarrow> C" by (auto simp add: utp_defs)
lemma not_dest: "(\<not> P) x \<Longrightarrow> \<not> P x" by (auto simp add: utp_defs)

lemma conj_intro: "P x \<Longrightarrow> Q x \<Longrightarrow> (P \<and> Q) x" by (auto simp add: utp_defs)
lemma conj_elim: "(P \<and> Q) x \<Longrightarrow> (P x \<Longrightarrow> Q x \<Longrightarrow> C) \<Longrightarrow> C" by (auto simp add: utp_defs)

lemma disj_introC: "(\<not> Q x \<Longrightarrow> P x) \<Longrightarrow> (P \<or> Q) x" by (auto simp add: utp_defs)
lemma disj_elim: "(P \<or> Q) x \<Longrightarrow> (P x \<Longrightarrow> C) \<Longrightarrow> (Q x \<Longrightarrow> C) \<Longrightarrow> C" by (auto simp add: utp_defs)

lemma impl_intro: "(P x \<Longrightarrow> Q x) \<Longrightarrow> (P \<longrightarrow> Q) x" by (auto simp add: utp_defs)
lemma impl_elimC: "(P \<longrightarrow> Q) x \<Longrightarrow> (\<not> P x \<Longrightarrow> R) \<Longrightarrow> (Q x \<Longrightarrow> R) \<Longrightarrow> R " by (auto simp add: utp_defs)

lemma iff_intro: "(P x \<Longrightarrow> Q x) \<Longrightarrow> (Q x \<Longrightarrow> P x) \<Longrightarrow> (P \<longleftrightarrow> Q) x" by (auto simp add: utp_defs)
lemma iff_elimC: 
"(P \<longleftrightarrow> Q) x \<Longrightarrow> (P x \<Longrightarrow> Q x \<Longrightarrow> R) \<Longrightarrow> (\<not> P x \<Longrightarrow> \<not> Q x \<Longrightarrow> R) \<Longrightarrow> R" by (auto simp add: utp_defs)

lemma all_intro: "(\<And>a. P a x) \<Longrightarrow> (\<^bold>\<forall>a. P a) x" by (auto simp add: utp_defs)
lemma all_elim: "(\<^bold>\<forall>a. P a) x \<Longrightarrow> (P a x \<Longrightarrow> R) \<Longrightarrow> R" by (auto simp add: utp_defs)

lemma ex_intro: "P a x \<Longrightarrow> (\<^bold>\<exists>a. P a) x" by (auto simp add: utp_defs)
lemma ex_elim: "(\<^bold>\<exists>a. P a) x \<Longrightarrow> (\<And>a. P a x \<Longrightarrow> Q) \<Longrightarrow> Q" by (auto simp add: utp_defs)

lemma comp_intro: "P (a, b) \<Longrightarrow> Q (b, c) \<Longrightarrow> (P ;; Q) (a, c)"
  by (auto simp add: comp_def)

lemma comp_elim: 
"(P ;; Q) ac \<Longrightarrow> (\<And>a b c. ac = (a, c) \<Longrightarrow> P (a, b) \<Longrightarrow> Q (b, c) \<Longrightarrow> C) \<Longrightarrow> C"
  by (auto simp add: comp_def)

declare not_def [simp]

declare iff_intro [intro!]
  and not_intro [intro!]
  and impl_intro [intro!]
  and disj_introC [intro!]
  and conj_intro [intro!]
  and true_intro [intro!]
  and comp_intro [intro]

declare not_dest [dest!]
  and iff_elimC [elim!]
  and false_elim [elim!]
  and impl_elimC [elim!]
  and disj_elim [elim!]
  and conj_elim [elim!]
  and comp_elim [elim!]
  and true_elim [elim!]

declare all_intro [intro!] and ex_intro [intro]
declare ex_elim [elim!] and all_elim [elim]

lemmas relation_rules = iff_intro not_intro impl_intro disj_introC conj_intro true_intro
                        comp_intro not_dest iff_elimC false_elim impl_elimC all_elim
                        disj_elim conj_elim comp_elim all_intro ex_intro ex_elim 
                        


lemma split_cond: 
"A ((P \<triangleleft> b \<triangleright> Q) x) = ((b x \<longrightarrow> A (P x)) \<and> (\<not> b x \<longrightarrow> A (Q x)))"
  by (cases "b x") (auto simp add: utp_defs)

lemma split_cond_asm: 
"A ((P \<triangleleft> b \<triangleright> Q) x) = (\<not> ((b x \<and> \<not> A (P x)) \<or> (\<not> b x \<and> \<not> A (Q x))))"
  by (cases "b x") (auto simp add: utp_defs)

lemmas cond_splits = split_cond split_cond_asm


subsubsection \<open>Misc lemmas\<close>

lemma cond_idem:"(P \<triangleleft> b \<triangleright> P) = P"
  by (rule ext) (auto split: cond_splits)

lemma cond_symm:"(P \<triangleleft> b \<triangleright> Q) = (Q \<triangleleft> \<not> b \<triangleright> P)"
  by (rule ext) (auto split: cond_splits)

lemma cond_assoc: "((P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> R) = (P \<triangleleft> b \<and> c \<triangleright> (Q \<triangleleft> c \<triangleright> R))"
  by (rule ext) (auto split: cond_splits)

lemma cond_distr: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> c \<triangleright> R)) = ((P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> (P \<triangleleft> b \<triangleright> R))"
  by (rule ext) (auto split: cond_splits)

lemma cond_unit_T:"(P \<triangleleft> true \<triangleright> Q) = P"
  by (rule ext) (auto split: cond_splits)

lemma cond_unit_F:"(P \<triangleleft> false \<triangleright> Q) = Q"
  by (rule ext) (auto split: cond_splits)

lemma cond_L6: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> b \<triangleright> R)) = (P \<triangleleft> b \<triangleright> R)"
  by (rule ext) (auto split: cond_splits)

lemma cond_L7: "(P \<triangleleft> b \<triangleright> (P \<triangleleft> c \<triangleright> Q)) = (P \<triangleleft> b \<or> c \<triangleright> Q)"
  by (rule ext) (auto split: cond_splits)

lemma cond_and_distr: "((P \<and> Q) \<triangleleft> b \<triangleright> (R \<and> S)) = ((P \<triangleleft> b \<triangleright> R) \<and> (Q \<triangleleft> b \<triangleright> S))"
  by (rule ext) (auto split: cond_splits)

lemma cond_or_distr: "((P \<or> Q) \<triangleleft> b \<triangleright> (R \<or> S)) = ((P \<triangleleft> b \<triangleright> R) \<or> (Q \<triangleleft> b \<triangleright> S))"
  by (rule ext) (auto split: cond_splits)

lemma cond_imp_distr: 
"((P \<longrightarrow> Q) \<triangleleft> b \<triangleright> (R \<longrightarrow> S)) = ((P \<triangleleft> b \<triangleright> R) \<longrightarrow> (Q \<triangleleft> b \<triangleright> S))"
  by (rule ext) (auto split: cond_splits)

lemma cond_eq_distr: 
"((P \<longleftrightarrow> Q) \<triangleleft> b \<triangleright> (R \<longleftrightarrow> S)) = ((P \<triangleleft> b \<triangleright> R) \<longleftrightarrow> (Q \<triangleleft> b \<triangleright> S))"
  by (rule ext) (auto split: cond_splits)

lemma comp_assoc: "(P ;; (Q ;; R)) = ((P ;; Q) ;; R)"
  by (rule ext) blast

lemma conj_comp: 
"(\<And> a b c. P (a, b) = P (a, c)) \<Longrightarrow> (P \<and> (Q ;; R)) = ((P \<and> Q) ;; R)"
  by (rule ext) blast

lemma comp_cond_left_distr:
  assumes "\<And>x y z. b (x, y) = b (x, z)"
  shows "((P \<triangleleft> b \<triangleright> Q) ;; R) = ((P ;; R) \<triangleleft> b \<triangleright> (Q ;; R))"
  using assms by (auto simp: fun_eq_iff utp_defs)

lemma ndet_symm: "(P::'a relation) \<sqinter> Q = Q \<sqinter> P"
  by (rule ext) blast

lemma ndet_assoc: "P \<sqinter> (Q \<sqinter> R) = (P \<sqinter> Q) \<sqinter> R"
  by (rule ext) blast

lemma ndet_idemp: "P \<sqinter> P = P"
  by (rule ext) blast

lemma ndet_distr: "P \<sqinter> (Q \<sqinter> R) = (P \<sqinter> Q) \<sqinter> (P \<sqinter> R)"
  by (rule ext) blast

lemma cond_ndet_distr: "(P \<triangleleft> b \<triangleright> (Q \<sqinter> R)) = ((P \<triangleleft> b \<triangleright> Q) \<sqinter> (P \<triangleleft> b \<triangleright> R))"
  by (rule ext) (auto split: cond_splits)

lemma ndet_cond_distr: "(P \<sqinter> (Q \<triangleleft> b \<triangleright> R)) = ((P \<sqinter> Q) \<triangleleft> b \<triangleright> (P \<sqinter> R))"
  by (rule ext) (auto split: cond_splits)

lemma comp_ndet_l_distr: "((P \<sqinter> Q) ;; R) = ((P ;; R) \<sqinter> (Q ;; R))"
  by (auto simp: fun_eq_iff utp_defs)

lemma comp_ndet_r_distr: "(P ;; (Q \<sqinter> R)) = ((P ;; Q) \<sqinter> (P ;; R))"
  by (auto simp: fun_eq_iff utp_defs)

lemma l2_5_1_A: "\<forall>X \<in> S. [X \<longrightarrow> (\<Sqinter> S)]"
  by blast

lemma l2_5_1_B: "(\<forall> X \<in> S. [X \<longrightarrow> P]) \<longrightarrow> [(\<Sqinter> S) \<longrightarrow> P]"
  by blast

lemma l2_5_1: "[(\<Sqinter> S) \<longrightarrow> P] \<longleftrightarrow> (\<forall> X \<in> S. [X \<longrightarrow> P])"
  by blast

lemma empty_disj: "\<Sqinter> {} = Top"
  by (rule ext) blast

lemma l2_5_1_2: "[P \<longrightarrow> (\<Squnion> S)] \<longleftrightarrow> (\<forall> X \<in> S. [P \<longrightarrow> X])"
  by blast

lemma empty_conj: "\<Squnion> {} = Bot"
  by (rule ext) blast

lemma l2_5_2: "((\<Squnion> S) \<sqinter> Q) = (\<Squnion>{P \<sqinter> Q | P. P\<in>S})"
  by (rule ext) blast

lemma l2_5_3: "((\<Sqinter> S) \<squnion> Q) = (\<Sqinter>{P \<squnion> Q | P. P \<in> S})"
  by (rule ext) blast

lemma l2_5_4: "((\<Sqinter> S) ;; Q) = (\<Sqinter>{P ;; Q | P. P \<in> S})"
  by (rule ext) blast

lemma l2_5_5: "(Q ;; (\<Sqinter> S)) = (\<Sqinter>{Q ;; P | P. P \<in> S})"
  by (rule ext) blast

lemma all_idem :"(\<^bold>\<forall>b. \<^bold>\<forall>a. P a) = (\<^bold>\<forall>a. P a)"
  by (simp add: all_def)

lemma comp_unit_R [simp]: "(P ;; \<Pi>r) = P"
  by (auto simp: fun_eq_iff utp_defs)

lemma comp_unit_L [simp]: "(\<Pi>r ;; P) = P"
  by (auto simp: fun_eq_iff utp_defs)

lemmas comp_unit_simps = comp_unit_R comp_unit_L

lemma not_cond: "(\<not>(P \<triangleleft> b \<triangleright> Q)) = ((\<not> P) \<triangleleft> b \<triangleright> (\<not> Q))"
  by (rule ext) (auto split: cond_splits)

lemma cond_conj_not_distr: 
"((P \<triangleleft> b \<triangleright> Q) \<and> \<not>(R \<triangleleft> b \<triangleright> S)) = ((P \<and> \<not>R) \<triangleleft> b \<triangleright> (Q \<and> \<not>S))"
  by (rule ext) (auto split: cond_splits)

lemma imp_cond_distr: "(R \<longrightarrow> (P \<triangleleft> b \<triangleright> Q)) = ((R \<longrightarrow> P) \<triangleleft> b \<triangleright> (R \<longrightarrow> Q))"
  by (rule ext) (auto split: cond_splits)

lemma cond_imp_dist: "((P \<triangleleft> b \<triangleright> Q) \<longrightarrow> R) = ((P \<longrightarrow> R) \<triangleleft> b \<triangleright> (Q \<longrightarrow> R))"
  by (rule ext) (auto split: cond_splits)

lemma cond_conj_distr: "((P \<triangleleft> b \<triangleright> Q) \<and> R) = ((P \<and> R) \<triangleleft> b \<triangleright> (Q \<and> R))"
  by (rule ext) (auto split: cond_splits)

lemma cond_disj_distr: "((P \<triangleleft> b \<triangleright> Q) \<or> R) = ((P \<or> R) \<triangleleft> b \<triangleright> (Q \<or> R))"
  by (rule ext) (auto split: cond_splits)

lemma cond_know_b: "(b \<and> (P \<triangleleft> b \<triangleright> Q)) = (b \<and> P)"
  by (rule ext) (auto split: cond_splits)

lemma cond_know_nb: "((\<not> (b)) \<and> (P \<triangleleft> b \<triangleright> Q)) = ((\<not> (b)) \<and> Q)"
  by (rule ext) (auto split: cond_splits)

lemma cond_ass_if: "(P \<triangleleft> b \<triangleright> Q) = (((b) \<and> P \<triangleleft> b \<triangleright> Q))"
  by (rule ext) (auto split: cond_splits)

lemma cond_ass_else: "(P \<triangleleft> b \<triangleright> Q) = (P \<triangleleft> b \<triangleright> ((\<not>b) \<and> Q))"
  by (rule ext) (auto split: cond_splits)

lemma not_true_eq_false: "(\<not> true) = false"
  by (rule ext) blast

lemma not_false_eq_true: "(\<not> false) = true"
  by (rule ext) blast

lemma conj_idem: "((P::'\<alpha> predicate) \<and> P) = P"
  by (rule ext) blast

lemma disj_idem: "((P::'\<alpha> predicate) \<or> P) = P"
  by (rule ext) blast

lemma conj_comm: "((P::'\<alpha> predicate) \<and> Q) = (Q \<and> P)"
  by (rule ext) blast

lemma disj_comm: "((P::'\<alpha> predicate) \<or> Q) = (Q \<or> P)"
  by (rule ext) blast

lemma conj_subst: "P = R \<Longrightarrow> ((P::'\<alpha> predicate) \<and> Q) = (R \<and> Q)"
  by (rule ext) blast

lemma disj_subst: "P = R \<Longrightarrow> ((P::'\<alpha> predicate) \<or> Q) = (R \<or> Q)"
  by (rule ext) blast

lemma conj_assoc:"(((P::'\<alpha> predicate) \<and> Q) \<and> S) = (P \<and> (Q \<and> S))"
  by (rule ext) blast

lemma disj_assoc:"(((P::'\<alpha> predicate) \<or> Q) \<or> S) = (P \<or> (Q \<or> S))"
  by (rule ext) blast

lemma conj_disj_abs:"((P::'\<alpha> predicate) \<and> (P \<or> Q)) = P"
  by (rule ext) blast

lemma disj_conj_abs:"((P::'\<alpha> predicate) \<or> (P \<and> Q)) = P"
  by (rule ext) blast

lemma conj_disj_distr:"((P::'\<alpha> predicate) \<and> (Q \<or> R)) = ((P \<and> Q) \<or> (P \<and> R))"
  by (rule ext) blast

lemma disj_conj_dsitr:"((P::'\<alpha> predicate) \<or> (Q \<and> R)) = ((P \<or> Q) \<and> (P \<or> R))"
  by (rule ext) blast

lemma true_conj_id:"(P \<and> true) = P"
  by (rule ext) blast

lemma true_dsij_zero:"(P \<or> true) = true"
  by (rule ext) blast

lemma true_conj_zero:"(P \<and> false) = false"
  by (rule ext) blast

lemma true_dsij_id:"(P \<or> false) = P"
  by (rule ext) blast

lemma imp_vacuous: "(false \<longrightarrow> u) = true"
  by (rule ext) blast

lemma p_and_not_p: "(P \<and> \<not> P) = false"
  by (rule ext) blast

lemma conj_disj_not_abs: "((P::'\<alpha> predicate) \<and> ((\<not>P) \<or> Q)) = (P \<and> Q)"
  by (rule ext) blast

lemma p_or_not_p: "(P \<or> \<not> P) = true"
  by (rule ext) blast

lemma double_negation: "(\<not> \<not> (P::'\<alpha> predicate)) = P"
  by (rule ext) blast

lemma not_conj_deMorgans: "(\<not> ((P::'\<alpha> predicate) \<and> Q)) = ((\<not> P) \<or> (\<not> Q))"
  by (rule ext) blast

lemma not_disj_deMorgans: "(\<not> ((P::'\<alpha> predicate) \<or> Q)) = ((\<not> P) \<and> (\<not> Q))"
  by (rule ext) blast

lemma p_imp_p: "(P \<longrightarrow> P) = true"
  by (rule ext) blast

lemma imp_imp: "((P::'\<alpha> predicate) \<longrightarrow> (Q \<longrightarrow> R)) = ((P \<and> Q) \<longrightarrow> R)"
  by (rule ext) blast

lemma imp_trans: "((P \<longrightarrow> Q) \<and> (Q \<longrightarrow> R) \<longrightarrow> P \<longrightarrow> R) = true"
  by (rule ext) blast

lemma p_equiv_p: "(P \<longleftrightarrow> P) = true"
  by (rule ext) blast

lemma equiv_eq: "((((P::'\<alpha> predicate) \<and> Q) \<or> (\<not>P \<and> \<not>Q)) = true) \<longleftrightarrow> (P = Q)"
  by (auto simp add: fun_eq_iff utp_defs)

lemma equiv_eq1: "(((P::'\<alpha> predicate) \<longleftrightarrow> Q) = true) \<longleftrightarrow> (P = Q)"
  by (auto simp add: fun_eq_iff utp_defs)

lemma cond_subst: "b = c \<Longrightarrow> (P \<triangleleft> b \<triangleright> Q) = (P \<triangleleft> c \<triangleright> Q)"
  by simp

lemma ex_disj_distr: "((\<^bold>\<exists>x. P x) \<or> (\<^bold>\<exists>x. Q x)) = (\<^bold>\<exists>x. (P x \<or> Q x))"
  by (rule ext) blast

lemma all_disj_distr: "((\<^bold>\<forall>x. P x) \<or> (\<^bold>\<forall>x. Q)) = (\<^bold>\<forall>x. (P x \<or> Q))"
  by (rule ext) blast

lemma all_conj_distr: "((\<^bold>\<forall>x. P x) \<and> (\<^bold>\<forall>x. Q x)) = (\<^bold>\<forall>x. (P x \<and> Q x))"
  by (rule ext) blast

lemma all_triv: "(\<^bold>\<forall>x. P) = P"
  by (rule ext) blast

lemma closure_true: "[true]"
  by blast

lemma closure_p_eq_true: "[P] \<longleftrightarrow> (P = true)"
  by (simp add: fun_eq_iff utp_defs)

lemma closure_equiv_eq: "[P \<longleftrightarrow> Q] \<longleftrightarrow> (P = Q)"
  by (simp add: fun_eq_iff utp_defs)

lemma closure_conj_distr: "([P] \<and> [Q]) = [P \<and> Q]"
  by blast

lemma closure_imp_distr: "[P \<longrightarrow> Q] \<longrightarrow> [P] \<longrightarrow> [Q]"
  by blast

lemma true_iff[simp]: "(P \<longleftrightarrow> true) = P"
  by blast

lemma true_imp[simp]: "(true \<longrightarrow> P) = P"
  by blast

end
