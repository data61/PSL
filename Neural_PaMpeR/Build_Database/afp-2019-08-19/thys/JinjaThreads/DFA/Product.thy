(*  Title:      HOL/MicroJava/BV/Product.thy
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Products as semilattices.
*)

section \<open>Products as Semilattices\<close>

theory Product
imports Err
begin

definition le :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('a \<times> 'b) ord"
where
  "le r\<^sub>A r\<^sub>B = (\<lambda>(a\<^sub>1,b\<^sub>1) (a\<^sub>2,b\<^sub>2). a\<^sub>1 \<sqsubseteq>\<^bsub>r\<^sub>A\<^esub> a\<^sub>2 \<and> b\<^sub>1 \<sqsubseteq>\<^bsub>r\<^sub>B\<^esub> b\<^sub>2)"

definition sup :: "'a ebinop \<Rightarrow> 'b ebinop \<Rightarrow> ('a \<times> 'b) ebinop"
where
  "sup f g = (\<lambda>(a\<^sub>1,b\<^sub>1)(a\<^sub>2,b\<^sub>2). Err.sup Pair (a\<^sub>1 \<squnion>\<^sub>f a\<^sub>2) (b\<^sub>1 \<squnion>\<^sub>g b\<^sub>2))"

definition esl :: "'a esl \<Rightarrow> 'b esl \<Rightarrow> ('a \<times> 'b ) esl"
where
  "esl = (\<lambda>(A,r\<^sub>A,f\<^sub>A) (B,r\<^sub>B,f\<^sub>B). (A \<times> B, le r\<^sub>A r\<^sub>B, sup f\<^sub>A f\<^sub>B))"

abbreviation
  lesubprod :: "'a \<times> 'b \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
    ("(_ /\<sqsubseteq>'(_,_') _)" [50, 0, 0, 51] 50) where
  "p \<sqsubseteq>(rA,rB) q == p \<sqsubseteq>\<^bsub>Product.le rA rB\<^esub> q"

(*<*)
notation
  lesubprod  ("(_ /<='(_,_') _)" [50, 0, 0, 51] 50)
(*>*)

lemma unfold_lesub_prod: "x \<sqsubseteq>(r\<^sub>A,r\<^sub>B) y = le r\<^sub>A r\<^sub>B x y"
(*<*) by (simp add: lesub_def) (*>*)

lemma le_prod_Pair_conv [iff]: "((a\<^sub>1,b\<^sub>1) \<sqsubseteq>(r\<^sub>A,r\<^sub>B) (a\<^sub>2,b\<^sub>2)) = (a\<^sub>1 \<sqsubseteq>\<^bsub>r\<^sub>A\<^esub> a\<^sub>2 & b\<^sub>1 \<sqsubseteq>\<^bsub>r\<^sub>B\<^esub> b\<^sub>2)"
(*<*) by (simp add: lesub_def le_def) (*>*)

lemma less_prod_Pair_conv:
  "((a\<^sub>1,b\<^sub>1) \<sqsubset>\<^bsub>Product.le r\<^sub>A r\<^sub>B\<^esub> (a\<^sub>2,b\<^sub>2)) = 
  (a\<^sub>1 \<sqsubset>\<^bsub>r\<^sub>A\<^esub> a\<^sub>2 & b\<^sub>1 \<sqsubseteq>\<^bsub>r\<^sub>B\<^esub> b\<^sub>2 | a\<^sub>1 \<sqsubseteq>\<^bsub>r\<^sub>A\<^esub> a\<^sub>2 & b\<^sub>1 \<sqsubset>\<^bsub>r\<^sub>B\<^esub> b\<^sub>2)"
(*<*)
apply (unfold lesssub_def)
apply simp
apply blast
done
(*>*)

lemma order_le_prod [iff]: "order(Product.le r\<^sub>A r\<^sub>B) = (order r\<^sub>A & order r\<^sub>B)"
(*<*)
apply (unfold order_def)
apply simp
apply safe
apply blast+
done 
(*>*)


lemma acc_le_prodI [intro!]:
  "\<lbrakk> acc A r\<^sub>A; acc B r\<^sub>B \<rbrakk> \<Longrightarrow> acc (A \<times> B) (Product.le r\<^sub>A r\<^sub>B)"
(*<*)
apply (unfold acc_def)
apply (rule wf_subset)
 apply (erule wf_lex_prod)
 apply assumption
apply (auto simp add: lesssub_def less_prod_Pair_conv lex_prod_def)
done
(*>*)


lemma closed_lift2_sup:
  "\<lbrakk> closed (err A) (lift2 f); closed (err B) (lift2 g) \<rbrakk> \<Longrightarrow> 
  closed (err(A\<times>B)) (lift2(sup f g))"
(*<*)
apply (unfold closed_def plussub_def lift2_def err_def' sup_def)
apply (simp split: err.split)
apply blast
done 
(*>*)

lemma unfold_plussub_lift2: "e\<^sub>1 \<squnion>\<^bsub>lift2 f\<^esub> e\<^sub>2 = lift2 f e\<^sub>1 e\<^sub>2"
(*<*) by (simp add: plussub_def) (*>*)


lemma plus_eq_Err_conv [simp]:
  assumes "x\<in>A"  "y\<in>A"  "semilat(err A, Err.le r, lift2 f)"
  shows "(x \<squnion>\<^sub>f y = Err) = (\<not>(\<exists>z\<in>A. x \<sqsubseteq>\<^sub>r z \<and> y \<sqsubseteq>\<^sub>r z))"
(*<*)
proof -
  have plus_le_conv2:
    "\<And>r f z. \<lbrakk> z \<in> err A; semilat (err A, r, f); OK x \<in> err A; OK y \<in> err A;
                 OK x \<squnion>\<^sub>f OK y \<sqsubseteq>\<^sub>r z\<rbrakk> \<Longrightarrow> OK x \<sqsubseteq>\<^sub>r z \<and> OK y \<sqsubseteq>\<^sub>r z"
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
  apply (case_tac "x \<squnion>\<^sub>f y")
   apply assumption
  apply (rename_tac "z")
  apply (subgoal_tac "OK z: err A")
  apply (frule plus_le_conv2)
       apply assumption
      apply simp
      apply blast
     apply simp
    apply (blast dest: Semilat.orderI [OF Semilat.intro] order_refl)
   apply blast
  apply (erule subst)
  apply (unfold semilat_def err_def' closed_def)
  apply simp
  done
qed
(*>*)

lemma err_semilat_Product_esl:
  "\<And>L\<^sub>1 L\<^sub>2. \<lbrakk> err_semilat L\<^sub>1; err_semilat L\<^sub>2 \<rbrakk> \<Longrightarrow> err_semilat(Product.esl L\<^sub>1 L\<^sub>2)"
(*<*)
apply (unfold esl_def Err.sl_def)
apply (simp (no_asm_simp) only: split_tupled_all)
apply simp
apply (simp (no_asm) only: semilat_Def)
apply (simp (no_asm_simp) only: Semilat.closedI [OF Semilat.intro] closed_lift2_sup)
apply (simp (no_asm) only: unfold_lesub_err Err.le_def unfold_plussub_lift2 sup_def)
apply (auto elim: semilat_le_err_OK1 semilat_le_err_OK2
            simp add: lift2_def  split: err.split)
apply (blast dest: Semilat.orderI [OF Semilat.intro])
apply (blast dest: Semilat.orderI [OF Semilat.intro])

apply (rule OK_le_err_OK [THEN iffD1])
apply (erule subst, subst OK_lift2_OK [symmetric], rule Semilat.lub [OF Semilat.intro])
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp

apply (rule OK_le_err_OK [THEN iffD1])
apply (erule subst, subst OK_lift2_OK [symmetric], rule Semilat.lub [OF Semilat.intro])
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp
done 
(*>*)

end
