(*  Title:      HOL/MicroJava/BV/Err.thy
    Author:     Tobias Nipkow
    Copyright   2000 TUM

The error type.
*)

section \<open>The Error Type\<close>

theory Err
imports Semilat
begin

datatype 'a err = Err | OK 'a

type_synonym 'a ebinop = "'a \<Rightarrow> 'a \<Rightarrow> 'a err"
type_synonym 'a esl = "'a set \<times> 'a ord \<times> 'a ebinop"

primrec ok_val :: "'a err \<Rightarrow> 'a"
where
  "ok_val (OK x) = x"

definition lift :: "('a \<Rightarrow> 'b err) \<Rightarrow> ('a err \<Rightarrow> 'b err)"
where
  "lift f e = (case e of Err \<Rightarrow> Err | OK x \<Rightarrow> f x)"

definition lift2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c err) \<Rightarrow> 'a err \<Rightarrow> 'b err \<Rightarrow> 'c err"
where
  "lift2 f e\<^sub>1 e\<^sub>2 =
  (case e\<^sub>1 of Err  \<Rightarrow> Err | OK x \<Rightarrow> (case e\<^sub>2 of Err \<Rightarrow> Err | OK y \<Rightarrow> f x y))"

definition le :: "'a ord \<Rightarrow> 'a err ord"
where
  "le r e\<^sub>1 e\<^sub>2 =
  (case e\<^sub>2 of Err \<Rightarrow> True | OK y \<Rightarrow> (case e\<^sub>1 of Err \<Rightarrow> False | OK x \<Rightarrow> x \<sqsubseteq>\<^sub>r y))"

definition sup :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a err \<Rightarrow> 'b err \<Rightarrow> 'c err)"
where
  "sup f = lift2 (\<lambda>x y. OK (x \<squnion>\<^sub>f y))"

definition err :: "'a set \<Rightarrow> 'a err set"
where
  "err A = insert Err {OK x|x. x\<in>A}"

definition esl :: "'a sl \<Rightarrow> 'a esl"
where
  "esl = (\<lambda>(A,r,f). (A, r, \<lambda>x y. OK(f x y)))"

definition sl :: "'a esl \<Rightarrow> 'a err sl"
where
  "sl = (\<lambda>(A,r,f). (err A, le r, lift2 f))"

abbreviation
  err_semilat :: "'a esl \<Rightarrow> bool" where
  "err_semilat L == semilat(sl L)"

primrec strict  :: "('a \<Rightarrow> 'b err) \<Rightarrow> ('a err \<Rightarrow> 'b err)"
where
  "strict f Err    = Err"
| "strict f (OK x) = f x"

lemma err_def':
  "err A = insert Err {x. \<exists>y\<in>A. x = OK y}"
(*<*)
proof -
  have eq: "err A = insert Err {x. \<exists>y\<in>A. x = OK y}"
    by (unfold err_def) blast
  show "err A = insert Err {x. \<exists>y\<in>A. x = OK y}" by (simp add: eq)
qed
(*>*)

lemma strict_Some [simp]: 
  "(strict f x = OK y) = (\<exists>z. x = OK z \<and> f z = OK y)"
(*<*) by (cases x, auto) (*>*)

lemma not_Err_eq: "(x \<noteq> Err) = (\<exists>a. x = OK a)" 
(*<*) by (cases x) auto (*>*)

lemma not_OK_eq: "(\<forall>y. x \<noteq> OK y) = (x = Err)"
(*<*) by (cases x) auto   (*>*)

lemma unfold_lesub_err: "e1 \<sqsubseteq>\<^bsub>le r\<^esub> e2 = le r e1 e2"
(*<*) by (simp add: lesub_def) (*>*)

lemma le_err_refl: "\<forall>x. x \<sqsubseteq>\<^sub>r x \<Longrightarrow> e \<sqsubseteq>\<^bsub>le r\<^esub> e"
(*<*)
apply (unfold lesub_def le_def)
apply (simp split: err.split)
done 
(*>*)

lemma le_err_trans [rule_format]:
  "order r \<Longrightarrow> e1 \<sqsubseteq>\<^bsub>le r\<^esub> e2 \<longrightarrow> e2 \<sqsubseteq>\<^bsub>le r\<^esub> e3 \<longrightarrow> e1 \<sqsubseteq>\<^bsub>le r\<^esub> e3"
(*<*)
apply (unfold unfold_lesub_err le_def)
apply (simp split: err.split)
apply (blast intro: order_trans)
done
(*>*)

lemma le_err_antisym [rule_format]:
  "order r \<Longrightarrow> e1 \<sqsubseteq>\<^bsub>le r\<^esub> e2 \<longrightarrow> e2 \<sqsubseteq>\<^bsub>le r\<^esub> e1 \<longrightarrow> e1=e2"
(*<*)
apply (unfold unfold_lesub_err le_def)
apply (simp split: err.split)
apply (blast intro: order_antisym)
done 
(*>*)

lemma OK_le_err_OK: "(OK x \<sqsubseteq>\<^bsub>le r\<^esub> OK y) = (x \<sqsubseteq>\<^sub>r y)"
(*<*) by (simp add: unfold_lesub_err le_def) (*>*)

lemma order_le_err [iff]: "order(le r) = order r"
(*<*)
apply (rule iffI)
 apply (subst order_def)
 apply (blast dest: order_antisym OK_le_err_OK [THEN iffD2]
              intro: order_trans OK_le_err_OK [THEN iffD1])
apply (subst order_def)
apply (blast intro: le_err_refl le_err_trans le_err_antisym
             dest: order_refl)
done 
(*>*)

lemma le_Err [iff]: "e \<sqsubseteq>\<^bsub>le r\<^esub> Err"
(*<*) by (simp add: unfold_lesub_err le_def) (*>*)

lemma Err_le_conv [iff]: "Err \<sqsubseteq>\<^bsub>le r\<^esub> e  = (e = Err)"
(*<*) by (simp add: unfold_lesub_err le_def  split: err.split) (*>*)

lemma le_OK_conv [iff]: "e \<sqsubseteq>\<^bsub>le r\<^esub> OK x  =  (\<exists>y. e = OK y \<and> y \<sqsubseteq>\<^sub>r x)"
(*<*) by (simp add: unfold_lesub_err le_def split: err.split) (*>*)

lemma OK_le_conv: "OK x \<sqsubseteq>\<^bsub>le r\<^esub> e = (e = Err \<or> (\<exists>y. e = OK y \<and> x \<sqsubseteq>\<^sub>r y))"
(*<*) by (simp add: unfold_lesub_err le_def split: err.split) (*>*)

lemma top_Err [iff]: "top (le r) Err"
(*<*) by (simp add: top_def) (*>*)

lemma OK_less_conv [rule_format, iff]:
  "OK x \<sqsubset>\<^bsub>le r\<^esub> e = (e=Err \<or> (\<exists>y. e = OK y \<and> x \<sqsubset>\<^sub>r y))"
(*<*) by (simp add: lesssub_def lesub_def le_def split: err.split) (*>*)

lemma not_Err_less [rule_format, iff]: "\<not>(Err \<sqsubset>\<^bsub>le r\<^esub> x)"
(*<*) by (simp add: lesssub_def lesub_def le_def split: err.split) (*>*)

lemma semilat_errI [intro]: assumes "Semilat A r f"
shows "semilat(err A, le r, lift2(\<lambda>x y. OK(f x y)))"
(*<*)
proof -
  interpret Semilat A r f by fact
  show ?thesis
    apply(insert semilat)
    apply (simp only: semilat_Def closed_def plussub_def lesub_def 
              lift2_def le_def)
    apply (simp add: err_def' split: err.split)
    done
qed
(*>*)

lemma err_semilat_eslI_aux:
assumes "Semilat A r f" shows "err_semilat(esl(A,r,f))"
(*<*)
proof -
  interpret Semilat A r f by fact
  show ?thesis
    apply (unfold sl_def esl_def)
    apply (simp add: semilat_errI [OF \<open>Semilat A r f\<close>])
    done
qed
(*>*)

lemma err_semilat_eslI [intro, simp]:
  "semilat L \<Longrightarrow> err_semilat (esl L)"
(*<*) apply (cases L) apply simp
apply (drule Semilat.intro)
apply (simp add: err_semilat_eslI_aux split_tupled_all)
done (*>*)

lemma acc_err [simp, intro!]:  "acc A r \<Longrightarrow> acc (err A) (le r)"
(*<*)
apply (unfold acc_def lesub_def le_def lesssub_def)
apply (simp add: wf_eq_minimal split: err.split)
apply clarify
apply (case_tac "Err : Q")
 apply blast
apply (erule_tac x = "{a . OK a : Q}" in allE)
apply (case_tac "x")
 apply fast
apply (auto simp: err_def)
done 
(*>*)

lemma Err_in_err [iff]: "Err : err A"
(*<*) by (simp add: err_def') (*>*)

lemma Ok_in_err [iff]: "(OK x \<in> err A) = (x\<in>A)"
(*<*) by (auto simp add: err_def') (*>*)

subsection \<open>lift\<close>

lemma lift_in_errI:
  "\<lbrakk> e \<in> err S; \<forall>x\<in>S. e = OK x \<longrightarrow> f x \<in> err S \<rbrakk> \<Longrightarrow> lift f e \<in> err S"
(*<*)
apply (unfold lift_def)
apply (simp split: err.split)
apply blast
done 
(*>*)

lemma Err_lift2 [simp]: "Err \<squnion>\<^bsub>lift2 f\<^esub> x = Err"
(*<*) by (simp add: lift2_def plussub_def) (*>*)

lemma lift2_Err [simp]: "x \<squnion>\<^bsub>lift2 f\<^esub> Err = Err"
(*<*) by (simp add: lift2_def plussub_def split: err.split) (*>*)

lemma OK_lift2_OK [simp]: "OK x \<squnion>\<^bsub>lift2 f\<^esub> OK y = x \<squnion>\<^sub>f y"
(*<*) by (simp add: lift2_def plussub_def split: err.split) (*>*)


subsection \<open>sup\<close>

lemma Err_sup_Err [simp]: "Err \<squnion>\<^bsub>sup f\<^esub> x = Err"
(*<*) by (simp add: plussub_def sup_def lift2_def) (*>*)

lemma Err_sup_Err2 [simp]: "x \<squnion>\<^bsub>sup f\<^esub> Err = Err"
(*<*) by (simp add: plussub_def sup_def lift2_def split: err.split) (*>*)

lemma Err_sup_OK [simp]: "OK x \<squnion>\<^bsub>sup f\<^esub> OK y = OK (x \<squnion>\<^sub>f y)"
(*<*) by (simp add: plussub_def sup_def lift2_def) (*>*)

lemma Err_sup_eq_OK_conv [iff]:
  "(sup f ex ey = OK z) = (\<exists>x y. ex = OK x \<and> ey = OK y \<and> f x y = z)"
(*<*)
apply (unfold sup_def lift2_def plussub_def)
apply (rule iffI)
 apply (simp split: err.split_asm)
apply clarify
apply simp
done
(*>*)

lemma Err_sup_eq_Err [iff]: "(sup f ex ey = Err) = (ex=Err \<or> ey=Err)"
(*<*)
apply (unfold sup_def lift2_def plussub_def)
apply (simp split: err.split)
done 
(*>*)

subsection \<open>semilat (err A) (le r) f\<close>

lemma semilat_le_err_Err_plus [simp]:
  "\<lbrakk> x\<in> err A; semilat(err A, le r, f) \<rbrakk> \<Longrightarrow> Err \<squnion>\<^sub>f x = Err"
(*<*) by (blast intro: Semilat.le_iff_plus_unchanged [THEN iffD1, OF Semilat.intro] 
                   Semilat.le_iff_plus_unchanged2 [THEN iffD1, OF Semilat.intro]) (*>*)

lemma semilat_le_err_plus_Err [simp]:
  "\<lbrakk> x\<in> err A; semilat(err A, le r, f) \<rbrakk> \<Longrightarrow> x \<squnion>\<^sub>f Err = Err"
(*<*) by (blast intro: Semilat.le_iff_plus_unchanged [THEN iffD1, OF Semilat.intro]
                   Semilat.le_iff_plus_unchanged2 [THEN iffD1, OF Semilat.intro]) (*>*)

lemma semilat_le_err_OK1:
  "\<lbrakk> x\<in>A; y\<in>A; semilat(err A, le r, f); OK x \<squnion>\<^sub>f OK y = OK z \<rbrakk> 
  \<Longrightarrow> x \<sqsubseteq>\<^sub>r z"
(*<*)
apply (rule OK_le_err_OK [THEN iffD1])
apply (erule subst)
apply (simp add: Semilat.ub1 [OF Semilat.intro])
done
(*>*)

lemma semilat_le_err_OK2:
  "\<lbrakk> x\<in>A; y\<in>A; semilat(err A, le r, f); OK x \<squnion>\<^sub>f OK y = OK z \<rbrakk> 
  \<Longrightarrow> y \<sqsubseteq>\<^sub>r z"
(*<*)
apply (rule OK_le_err_OK [THEN iffD1])
apply (erule subst)
apply (simp add: Semilat.ub2 [OF Semilat.intro])
done
(*>*)

lemma eq_order_le:
  "\<lbrakk> x=y; order r \<rbrakk> \<Longrightarrow> x \<sqsubseteq>\<^sub>r y"
(*<*)
apply (unfold order_def)
apply blast
done
(*>*)

lemma OK_plus_OK_eq_Err_conv [simp]:
  assumes "x\<in>A"  "y\<in>A"  "semilat(err A, le r, fe)"
  shows "(OK x \<squnion>\<^bsub>fe\<^esub> OK y = Err) = (\<not>(\<exists>z\<in>A. x \<sqsubseteq>\<^sub>r z \<and> y \<sqsubseteq>\<^sub>r z))"
(*<*)
proof -
  have plus_le_conv3: "\<And>A x y z f r. 
    \<lbrakk> semilat (A,r,f); x \<squnion>\<^sub>f y \<sqsubseteq>\<^sub>r z; x\<in>A; y\<in>A; z\<in>A \<rbrakk> 
    \<Longrightarrow> x \<sqsubseteq>\<^sub>r z \<and> y \<sqsubseteq>\<^sub>r z"
(*<*) by (rule Semilat.plus_le_conv [OF Semilat.intro, THEN iffD1]) (*>*)
  from assms show ?thesis
  apply (rule_tac iffI)
   apply clarify
   apply (drule OK_le_err_OK [THEN iffD2])
   apply (drule OK_le_err_OK [THEN iffD2])
   apply (drule Semilat.lub[OF Semilat.intro, of _ _ _ "OK x" _ "OK y"])
        apply assumption
       apply assumption
      apply simp
     apply simp
    apply simp
   apply simp
  apply (case_tac "OK x \<squnion>\<^bsub>fe\<^esub> OK y")
   apply assumption
  apply (rename_tac z)
  apply (subgoal_tac "OK z\<in> err A")
  apply (drule eq_order_le)
    apply (erule Semilat.orderI [OF Semilat.intro])
   apply (blast dest: plus_le_conv3) 
  apply (erule subst)
  apply (blast intro: Semilat.closedI [OF Semilat.intro] closedD)
  done 
qed
(*>*)

subsection \<open>semilat (err(Union AS))\<close>

(* FIXME? *)
lemma all_bex_swap_lemma [iff]:
  "(\<forall>x. (\<exists>y\<in>A. x = f y) \<longrightarrow> P x) = (\<forall>y\<in>A. P(f y))"
(*<*) by blast (*>*)

lemma closed_err_Union_lift2I: 
  "\<lbrakk> \<forall>A\<in>AS. closed (err A) (lift2 f); AS \<noteq> {}; 
      \<forall>A\<in>AS.\<forall>B\<in>AS. A\<noteq>B \<longrightarrow> (\<forall>a\<in>A.\<forall>b\<in>B. a \<squnion>\<^sub>f b = Err) \<rbrakk> 
  \<Longrightarrow> closed (err(Union AS)) (lift2 f)"
(*<*)
apply (unfold closed_def err_def')
apply simp
apply clarify
apply simp
apply fast
done 
(*>*)

text \<open>
  If @{term "AS = {}"} the thm collapses to
  @{prop "order r \<and> closed {Err} f \<and> Err \<squnion>\<^sub>f Err = Err"}
  which may not hold 
\<close>
lemma err_semilat_UnionI:
  "\<lbrakk> \<forall>A\<in>AS. err_semilat(A, r, f); AS \<noteq> {}; 
      \<forall>A\<in>AS.\<forall>B\<in>AS. A\<noteq>B \<longrightarrow> (\<forall>a\<in>A.\<forall>b\<in>B. \<not>a \<sqsubseteq>\<^sub>r b \<and> a \<squnion>\<^sub>f b = Err) \<rbrakk> 
  \<Longrightarrow> err_semilat(Union AS, r, f)"
(*<*)
apply (unfold semilat_def sl_def)
apply (simp add: closed_err_Union_lift2I)
apply (rule conjI)
 apply blast
apply (simp add: err_def')
apply (rule conjI)
 apply clarify
 apply (rename_tac A a u B b)
 apply (case_tac "A = B")
  apply simp
 apply simp
apply (rule conjI)
 apply clarify
 apply (rename_tac A a u B b)
 apply (case_tac "A = B")
  apply simp
 apply simp
apply clarify
apply (rename_tac A ya yb B yd z C c a b)
apply (case_tac "A = B")
 apply (case_tac "A = C")
  apply simp
 apply simp
apply (case_tac "B = C")
 apply simp
apply simp
done 
(*>*)

end
