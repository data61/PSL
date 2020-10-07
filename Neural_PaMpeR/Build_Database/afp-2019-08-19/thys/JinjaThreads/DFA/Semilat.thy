(*  Title:      HOL/MicroJava/BV/Semilat.thy
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Semilattices.
*)

chapter \<open>Data Flow Analysis Framework \label{cha:bv}\<close>

section \<open>Semilattices\<close>

theory Semilat
imports Main "HOL-Library.While_Combinator"
begin

type_synonym 'a ord    = "'a \<Rightarrow> 'a \<Rightarrow> bool"
type_synonym 'a binop  = "'a \<Rightarrow> 'a \<Rightarrow> 'a"
type_synonym 'a sl     = "'a set \<times> 'a ord \<times> 'a binop"

definition lesub :: "'a \<Rightarrow> 'a ord \<Rightarrow> 'a \<Rightarrow> bool"
  where "lesub x r y \<longleftrightarrow> r x y"

definition lesssub :: "'a \<Rightarrow> 'a ord \<Rightarrow> 'a \<Rightarrow> bool"
  where "lesssub x r y \<longleftrightarrow> lesub x r y \<and> x \<noteq> y"

definition plussub :: "'a \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'c"
  where "plussub x f y = f x y"

notation (ASCII)
  "lesub"  ("(_ /<='__ _)" [50, 1000, 51] 50) and
  "lesssub"  ("(_ /<'__ _)" [50, 1000, 51] 50) and
  "plussub"  ("(_ /+'__ _)" [65, 1000, 66] 65)

notation
  "lesub"  ("(_ /\<sqsubseteq>\<^bsub>_\<^esub> _)" [50, 0, 51] 50) and
  "lesssub"  ("(_ /\<sqsubset>\<^bsub>_\<^esub> _)" [50, 0, 51] 50) and
  "plussub"  ("(_ /\<squnion>\<^bsub>_\<^esub> _)" [65, 0, 66] 65)

(* allow \<sub> instead of \<bsub>..\<esub> *)
abbreviation (input)
  lesub1 :: "'a \<Rightarrow> 'a ord \<Rightarrow> 'a \<Rightarrow> bool" ("(_ /\<sqsubseteq>\<^sub>_ _)" [50, 1000, 51] 50)
  where "x \<sqsubseteq>\<^sub>r y == x \<sqsubseteq>\<^bsub>r\<^esub> y"

abbreviation (input)
  lesssub1 :: "'a \<Rightarrow> 'a ord \<Rightarrow> 'a \<Rightarrow> bool" ("(_ /\<sqsubset>\<^sub>_ _)" [50, 1000, 51] 50)
  where "x \<sqsubset>\<^sub>r y == x \<sqsubset>\<^bsub>r\<^esub> y"

abbreviation (input)
  plussub1 :: "'a \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'c" ("(_ /\<squnion>\<^sub>_ _)" [65, 1000, 66] 65)
  where "x \<squnion>\<^sub>f y == x \<squnion>\<^bsub>f\<^esub> y"

definition ord :: "('a \<times> 'a) set \<Rightarrow> 'a ord"
where
  "ord r = (\<lambda>x y. (x,y) \<in> r)"

definition order :: "'a ord \<Rightarrow> bool"
where
  "order r \<longleftrightarrow> (\<forall>x. x \<sqsubseteq>\<^sub>r x) \<and> (\<forall>x y. x \<sqsubseteq>\<^sub>r y \<and> y \<sqsubseteq>\<^sub>r x \<longrightarrow> x=y) \<and> (\<forall>x y z. x \<sqsubseteq>\<^sub>r y \<and> y \<sqsubseteq>\<^sub>r z \<longrightarrow> x \<sqsubseteq>\<^sub>r z)"

definition top :: "'a ord \<Rightarrow> 'a \<Rightarrow> bool"
where
  "top r T \<longleftrightarrow> (\<forall>x. x \<sqsubseteq>\<^sub>r T)"
  
definition acc :: "'a set \<Rightarrow> 'a ord \<Rightarrow> bool"
where
  "acc A r \<longleftrightarrow> wf {(y,x). x \<in> A \<and> y \<in> A \<and> x \<sqsubset>\<^sub>r y}"

definition closed :: "'a set \<Rightarrow> 'a binop \<Rightarrow> bool"
where
  "closed A f \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. x \<squnion>\<^sub>f y \<in> A)"

definition semilat :: "'a sl \<Rightarrow> bool"
where
  "semilat = (\<lambda>(A,r,f). order r \<and> closed A f \<and> 
                       (\<forall>x\<in>A. \<forall>y\<in>A. x \<sqsubseteq>\<^sub>r x \<squnion>\<^sub>f y) \<and>
                       (\<forall>x\<in>A. \<forall>y\<in>A. y \<sqsubseteq>\<^sub>r x \<squnion>\<^sub>f y) \<and>
                       (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. x \<sqsubseteq>\<^sub>r z \<and> y \<sqsubseteq>\<^sub>r z \<longrightarrow> x \<squnion>\<^sub>f y \<sqsubseteq>\<^sub>r z))"

definition is_ub :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "is_ub r x y u \<longleftrightarrow> (x,u)\<in>r \<and> (y,u)\<in>r"

definition is_lub :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "is_lub r x y u \<longleftrightarrow> is_ub r x y u \<and> (\<forall>z. is_ub r x y z \<longrightarrow> (u,z)\<in>r)"

definition some_lub :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "some_lub r x y = (SOME z. is_lub r x y z)"

locale Semilat =
  fixes A :: "'a set"
  fixes r :: "'a ord"
  fixes f :: "'a binop"
  assumes semilat: "semilat (A, r, f)"

lemma order_refl [simp, intro]: "order r \<Longrightarrow> x \<sqsubseteq>\<^sub>r x"
  (*<*) by (unfold order_def) (simp (no_asm_simp)) (*>*)

lemma order_antisym: "\<lbrakk> order r; x \<sqsubseteq>\<^sub>r y; y \<sqsubseteq>\<^sub>r x \<rbrakk> \<Longrightarrow> x = y"
  (*<*) by (unfold order_def) (simp (no_asm_simp)) (*>*)

lemma order_trans: "\<lbrakk> order r; x \<sqsubseteq>\<^sub>r y; y \<sqsubseteq>\<^sub>r z \<rbrakk> \<Longrightarrow> x \<sqsubseteq>\<^sub>r z"
  (*<*) by (unfold order_def) blast (*>*)

lemma order_less_irrefl [intro, simp]: "order r \<Longrightarrow> \<not> x \<sqsubset>\<^sub>r x"
  (*<*) by (unfold order_def lesssub_def) blast (*>*)

lemma order_less_trans: "\<lbrakk> order r; x \<sqsubset>\<^sub>r y; y \<sqsubset>\<^sub>r z \<rbrakk> \<Longrightarrow> x \<sqsubset>\<^sub>r z"
  (*<*) by (unfold order_def lesssub_def) blast (*>*)

lemma topD [simp, intro]: "top r T \<Longrightarrow> x \<sqsubseteq>\<^sub>r T"
  (*<*) by (simp add: top_def) (*>*)

lemma top_le_conv [simp]: "\<lbrakk> order r; top r T \<rbrakk> \<Longrightarrow> (T \<sqsubseteq>\<^sub>r x) = (x = T)"
  (*<*) by (blast intro: order_antisym) (*>*)

lemma semilat_Def:
"semilat(A,r,f) \<longleftrightarrow> order r \<and> closed A f \<and> 
                 (\<forall>x\<in>A. \<forall>y\<in>A. x \<sqsubseteq>\<^sub>r x \<squnion>\<^sub>f y) \<and> 
                 (\<forall>x\<in>A. \<forall>y\<in>A. y \<sqsubseteq>\<^sub>r x \<squnion>\<^sub>f y) \<and> 
                 (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. x \<sqsubseteq>\<^sub>r z \<and> y \<sqsubseteq>\<^sub>r z \<longrightarrow> x \<squnion>\<^sub>f y \<sqsubseteq>\<^sub>r z)"
  (*<*) by (unfold semilat_def) clarsimp (*>*)

lemma (in Semilat) orderI [simp, intro]: "order r"
  (*<*) using semilat by (simp add: semilat_Def) (*>*)

lemma (in Semilat) closedI [simp, intro]: "closed A f"
  (*<*) using semilat by (simp add: semilat_Def) (*>*)

lemma closedD: "\<lbrakk> closed A f; x\<in>A; y\<in>A \<rbrakk> \<Longrightarrow> x \<squnion>\<^sub>f y \<in> A"
  (*<*) by (unfold closed_def) blast (*>*)

lemma closed_UNIV [simp]: "closed UNIV f"
  (*<*) by (simp add: closed_def) (*>*)

lemma (in Semilat) closed_f [simp, intro]: "\<lbrakk>x \<in> A; y \<in> A\<rbrakk>  \<Longrightarrow> x \<squnion>\<^sub>f y \<in> A"
  (*<*) by (simp add: closedD [OF closedI]) (*>*)

lemma (in Semilat) refl_r [intro, simp]: "x \<sqsubseteq>\<^sub>r x" by simp

lemma (in Semilat) antisym_r [intro?]: "\<lbrakk> x \<sqsubseteq>\<^sub>r y; y \<sqsubseteq>\<^sub>r x \<rbrakk> \<Longrightarrow> x = y"
  (*<*) by (rule order_antisym) auto (*>*)
  
lemma (in Semilat) trans_r [trans, intro?]: "\<lbrakk>x \<sqsubseteq>\<^sub>r y; y \<sqsubseteq>\<^sub>r z\<rbrakk> \<Longrightarrow> x \<sqsubseteq>\<^sub>r z"
  (*<*) by (auto intro: order_trans) (*>*)
  
lemma (in Semilat) ub1 [simp, intro?]: "\<lbrakk> x \<in> A; y \<in> A \<rbrakk> \<Longrightarrow> x \<sqsubseteq>\<^sub>r x \<squnion>\<^sub>f y"
  (*<*) by (insert semilat) (unfold semilat_Def, simp) (*>*)

lemma (in Semilat) ub2 [simp, intro?]: "\<lbrakk> x \<in> A; y \<in> A \<rbrakk> \<Longrightarrow> y \<sqsubseteq>\<^sub>r x \<squnion>\<^sub>f y"
  (*<*) by (insert semilat) (unfold semilat_Def, simp) (*>*)

lemma (in Semilat) lub [simp, intro?]:
  "\<lbrakk> x \<sqsubseteq>\<^sub>r z; y \<sqsubseteq>\<^sub>r z; x \<in> A; y \<in> A; z \<in> A \<rbrakk> \<Longrightarrow> x \<squnion>\<^sub>f y \<sqsubseteq>\<^sub>r z"
  (*<*) by (insert semilat) (unfold semilat_Def, simp) (*>*)

lemma (in Semilat) plus_le_conv [simp]:
  "\<lbrakk> x \<in> A; y \<in> A; z \<in> A \<rbrakk> \<Longrightarrow> (x \<squnion>\<^sub>f y \<sqsubseteq>\<^sub>r z) = (x \<sqsubseteq>\<^sub>r z \<and> y \<sqsubseteq>\<^sub>r z)"
  (*<*) by (blast intro: ub1 ub2 lub order_trans) (*>*)

lemma (in Semilat) le_iff_plus_unchanged:
  assumes "x \<in> A" and "y \<in> A"
  shows "x \<sqsubseteq>\<^sub>r y \<longleftrightarrow> x \<squnion>\<^sub>f y = y" (is "?P \<longleftrightarrow> ?Q")
(*<*)
proof
  assume ?P
  with assms show ?Q by (blast intro: antisym_r lub ub2)
next
  assume ?Q
  then have "y = x \<squnion>\<^bsub>f\<^esub> y" by simp
  moreover from assms have "x \<sqsubseteq>\<^bsub>r\<^esub> x \<squnion>\<^bsub>f\<^esub> y" by simp
  ultimately show ?P by simp
qed
(*>*)

lemma (in Semilat) le_iff_plus_unchanged2:
  assumes "x \<in> A" and "y \<in> A"
  shows "x \<sqsubseteq>\<^sub>r y \<longleftrightarrow> y \<squnion>\<^sub>f x = y" (is "?P \<longleftrightarrow> ?Q")
(*<*)
proof
  assume ?P
  with assms show ?Q by (blast intro: antisym_r lub ub1)
next
  assume ?Q
  then have "y = y \<squnion>\<^bsub>f\<^esub> x" by simp
  moreover from assms have "x \<sqsubseteq>\<^bsub>r\<^esub> y \<squnion>\<^bsub>f\<^esub> x" by simp
  ultimately show ?P by simp
qed
(*>*)

lemma (in Semilat) plus_assoc [simp]:
  assumes a: "a \<in> A" and b: "b \<in> A" and c: "c \<in> A"
  shows "a \<squnion>\<^sub>f (b \<squnion>\<^sub>f c) = a \<squnion>\<^sub>f b \<squnion>\<^sub>f c"
(*<*)
proof -
  from a b have ab: "a \<squnion>\<^sub>f b \<in> A" ..
  from this c have abc: "(a \<squnion>\<^sub>f b) \<squnion>\<^sub>f c \<in> A" ..
  from b c have bc: "b \<squnion>\<^sub>f c \<in> A" ..
  from a this have abc': "a \<squnion>\<^sub>f (b \<squnion>\<^sub>f c) \<in> A" ..

  show ?thesis
  proof    
    show "a \<squnion>\<^sub>f (b \<squnion>\<^sub>f c) \<sqsubseteq>\<^sub>r (a \<squnion>\<^sub>f b) \<squnion>\<^sub>f c"
    proof -
      from a b have "a \<sqsubseteq>\<^sub>r a \<squnion>\<^sub>f b" .. 
      also from ab c have "\<dots> \<sqsubseteq>\<^sub>r \<dots> \<squnion>\<^sub>f c" ..
      finally have "a<": "a \<sqsubseteq>\<^sub>r (a \<squnion>\<^sub>f b) \<squnion>\<^sub>f c" .
      from a b have "b \<sqsubseteq>\<^sub>r a \<squnion>\<^sub>f b" ..
      also from ab c have "\<dots> \<sqsubseteq>\<^sub>r \<dots> \<squnion>\<^sub>f c" ..
      finally have "b<": "b \<sqsubseteq>\<^sub>r (a \<squnion>\<^sub>f b) \<squnion>\<^sub>f c" .
      from ab c have "c<": "c \<sqsubseteq>\<^sub>r (a \<squnion>\<^sub>f b) \<squnion>\<^sub>f c" ..    
      from "b<" "c<" b c abc have "b \<squnion>\<^sub>f c \<sqsubseteq>\<^sub>r (a \<squnion>\<^sub>f b) \<squnion>\<^sub>f c" ..
      from "a<" this a bc abc show ?thesis ..
    qed
    show "(a \<squnion>\<^sub>f b) \<squnion>\<^sub>f c \<sqsubseteq>\<^sub>r a \<squnion>\<^sub>f (b \<squnion>\<^sub>f c)" 
    proof -
      from b c have "b \<sqsubseteq>\<^sub>r b \<squnion>\<^sub>f c" .. 
      also from a bc have "\<dots> \<sqsubseteq>\<^sub>r a \<squnion>\<^sub>f \<dots>" ..
      finally have "b<": "b \<sqsubseteq>\<^sub>r a \<squnion>\<^sub>f (b \<squnion>\<^sub>f c)" .
      from b c have "c \<sqsubseteq>\<^sub>r b \<squnion>\<^sub>f c" ..
      also from a bc have "\<dots> \<sqsubseteq>\<^sub>r a \<squnion>\<^sub>f \<dots>" ..
      finally have "c<": "c \<sqsubseteq>\<^sub>r a \<squnion>\<^sub>f (b \<squnion>\<^sub>f c)" .
      from a bc have "a<": "a \<sqsubseteq>\<^sub>r a \<squnion>\<^sub>f (b \<squnion>\<^sub>f c)" ..
      from "a<" "b<" a b abc' have "a \<squnion>\<^sub>f b \<sqsubseteq>\<^sub>r a \<squnion>\<^sub>f (b \<squnion>\<^sub>f c)" ..
      from this "c<" ab c abc' show ?thesis ..
    qed
  qed
qed
(*>*)

lemma (in Semilat) plus_com_lemma:
  "\<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a \<squnion>\<^sub>f b \<sqsubseteq>\<^sub>r b \<squnion>\<^sub>f a"
(*<*)
proof -
  assume a: "a \<in> A" and b: "b \<in> A"  
  from b a have "a \<sqsubseteq>\<^sub>r b \<squnion>\<^sub>f a" .. 
  moreover from b a have "b \<sqsubseteq>\<^sub>r b \<squnion>\<^sub>f a" ..
  moreover note a b
  moreover from b a have "b \<squnion>\<^sub>f a \<in> A" ..
  ultimately show ?thesis ..
qed
(*>*)

lemma (in Semilat) plus_commutative:
  "\<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a \<squnion>\<^sub>f b = b \<squnion>\<^sub>f a"
  (*<*) by(blast intro: order_antisym plus_com_lemma) (*>*)

lemma is_lubD:
  "is_lub r x y u \<Longrightarrow> is_ub r x y u \<and> (\<forall>z. is_ub r x y z \<longrightarrow> (u,z) \<in> r)"
  (*<*) by (simp add: is_lub_def) (*>*)

lemma is_ubI:
  "\<lbrakk> (x,u) \<in> r; (y,u) \<in> r \<rbrakk> \<Longrightarrow> is_ub r x y u"
  (*<*) by (simp add: is_ub_def) (*>*)

lemma is_ubD:
  "is_ub r x y u \<Longrightarrow> (x,u) \<in> r \<and> (y,u) \<in> r"
  (*<*) by (simp add: is_ub_def) (*>*)


lemma is_lub_bigger1 [iff]:  
  "is_lub (r^* ) x y y = ((x,y)\<in>r^* )"
(*<*)
  by (unfold is_lub_def is_ub_def) blast
(*>*)

lemma is_lub_bigger2 [iff]:
  "is_lub (r^* ) x y x = ((y,x)\<in>r^* )"
(*<*)
  by (unfold is_lub_def is_ub_def) blast 
(*>*)

lemma extend_lub:
  assumes "single_valued r"
    and "is_lub (r\<^sup>*) x y u"
    and "(x', x) \<in> r"
  shows "\<exists>v. is_lub (r\<^sup>*) x' y v"
(*<*)
proof (cases "(y, x) \<in> r\<^sup>*")
  case True show ?thesis
  proof (cases "(y, x') \<in> r\<^sup>*")
    case True with \<open>(y, x) \<in> r\<^sup>*\<close> show ?thesis by blast
  next
    case False with True assms show ?thesis
      by (unfold is_lub_def is_ub_def) (blast elim: converse_rtranclE dest: single_valuedD)
  qed
next
  case False
  from assms have "(x', u) \<in> r\<^sup>*" and "(y, u) \<in> r\<^sup>*"
    by (auto simp add: is_lub_def is_ub_def)
  moreover from False assms have "\<And>z. (x', z) \<in> r\<^sup>* \<Longrightarrow> (y, z) \<in> r\<^sup>* \<Longrightarrow> (u, z) \<in> r\<^sup>*"
    by (unfold is_lub_def is_ub_def) (blast intro: rtrancl_into_rtrancl
      converse_rtrancl_into_rtrancl elim: converse_rtranclE dest: single_valuedD)
  ultimately have "is_lub (r\<^sup>*) x' y u"
    by (unfold is_lub_def is_ub_def) blast
  then show ?thesis ..
qed
(*>*)

lemma single_valued_has_lubs:
  assumes "single_valued r"
    and in_r: "(x, u) \<in> r\<^sup>*" "(y, u) \<in> r\<^sup>*"
  shows "\<exists>z. is_lub (r\<^sup>*) x y z"
(*<*)
using in_r proof (induct arbitrary: y rule: converse_rtrancl_induct)
  case base then show ?case by (induct rule: converse_rtrancl_induct)
    (blast, blast intro: converse_rtrancl_into_rtrancl)
next
  case step with \<open>single_valued r\<close> show ?case by (blast intro: extend_lub)
qed
(*>*)

lemma some_lub_conv:
  "\<lbrakk> acyclic r; is_lub (r^* ) x y u \<rbrakk> \<Longrightarrow> some_lub (r^* ) x y = u"
(*<*)
apply (simp only: some_lub_def is_lub_def)
apply (rule someI2)
 apply (simp only: is_lub_def)
apply (blast intro: antisymD dest!: acyclic_impl_antisym_rtrancl)
done
(*>*)

lemma is_lub_some_lub:
  "\<lbrakk> single_valued r; acyclic r; (x,u)\<in>r^*; (y,u)\<in>r^* \<rbrakk> 
  \<Longrightarrow> is_lub (r^* ) x y (some_lub (r^* ) x y)"
  (*<*) by (fastforce dest: single_valued_has_lubs simp add: some_lub_conv) (*>*)

subsection\<open>An executable lub-finder\<close>

definition exec_lub :: "('a * 'a) set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a binop"
where
  "exec_lub r f x y = while (\<lambda>z. (x,z) \<notin> r\<^sup>*) f y"

lemma exec_lub_refl: "exec_lub r f T T = T"
by (simp add: exec_lub_def while_unfold)

lemma acyclic_single_valued_finite:
 "\<lbrakk>acyclic r; single_valued r; (x,y) \<in> r\<^sup>*\<rbrakk>
  \<Longrightarrow> finite (r \<inter> {a. (x, a) \<in> r\<^sup>*} \<times> {b. (b, y) \<in> r\<^sup>*})"
(*<*)
apply(erule converse_rtrancl_induct)
 apply(rule_tac B = "{}" in finite_subset)
  apply(simp only:acyclic_def)
  apply(blast intro:rtrancl_into_trancl2 rtrancl_trancl_trancl)
 apply simp
apply(rename_tac x x')
apply(subgoal_tac "r \<inter> {a. (x,a) \<in> r\<^sup>*} \<times> {b. (b,y) \<in> r\<^sup>*} =
                   insert (x,x') (r \<inter> {a. (x', a) \<in> r\<^sup>*} \<times> {b. (b, y) \<in> r\<^sup>*})")
 apply simp
apply(blast intro:converse_rtrancl_into_rtrancl
            elim:converse_rtranclE dest:single_valuedD)
done
(*>*)


lemma exec_lub_conv:
  "\<lbrakk> acyclic r; \<forall>x y. (x,y) \<in> r \<longrightarrow> f x = y; is_lub (r\<^sup>*) x y u \<rbrakk> \<Longrightarrow>
  exec_lub r f x y = u"
(*<*)
apply(unfold exec_lub_def)
apply(rule_tac P = "\<lambda>z. (y,z) \<in> r\<^sup>* \<and> (z,u) \<in> r\<^sup>*" and
               r = "(r \<inter> {(a,b). (y,a) \<in> r\<^sup>* \<and> (b,u) \<in> r\<^sup>*})^-1" in while_rule)
    apply(blast dest: is_lubD is_ubD)
   apply(erule conjE)
   apply(erule_tac z = u in converse_rtranclE)
    apply(blast dest: is_lubD is_ubD)
   apply(blast dest:rtrancl_into_rtrancl)
  apply(rename_tac s)
  apply(subgoal_tac "is_ub (r\<^sup>*) x y s")
   prefer 2 apply(simp add:is_ub_def)
  apply(subgoal_tac "(u, s) \<in> r\<^sup>*")
   prefer 2 apply(blast dest:is_lubD)
  apply(erule converse_rtranclE)
   apply blast
  apply(simp only:acyclic_def)
  apply(blast intro:rtrancl_into_trancl2 rtrancl_trancl_trancl)
 apply(rule finite_acyclic_wf)
  apply simp
  apply(erule acyclic_single_valued_finite)
   apply(blast intro:single_valuedI)
  apply(simp add:is_lub_def is_ub_def)
 apply simp
 apply(erule acyclic_subset)
 apply blast
apply simp
apply(erule conjE)
apply(erule_tac z = u in converse_rtranclE)
 apply(blast dest: is_lubD is_ubD)
apply(blast dest:rtrancl_into_rtrancl)
done
(*>*)

lemma is_lub_exec_lub:
  "\<lbrakk> single_valued r; acyclic r; (x,u):r^*; (y,u):r^*; \<forall>x y. (x,y) \<in> r \<longrightarrow> f x = y \<rbrakk>
  \<Longrightarrow> is_lub (r^* ) x y (exec_lub r f x y)"
  (*<*) by (fastforce dest: single_valued_has_lubs simp add: exec_lub_conv) (*>*)

end
