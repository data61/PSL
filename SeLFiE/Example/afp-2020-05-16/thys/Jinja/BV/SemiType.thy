(*  Title:      Jinja/BV/SemiType.thy

    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM
*)

section \<open>The Jinja Type System as a Semilattice\<close>

theory SemiType
imports "../Common/WellForm" "../DFA/Semilattices"
begin

definition super :: "'a prog \<Rightarrow> cname \<Rightarrow> cname"
where "super P C \<equiv> fst (the (class P C))"

lemma superI:
  "(C,D) \<in> subcls1 P \<Longrightarrow> super P C = D"
  by (unfold super_def) (auto dest: subcls1D)


primrec the_Class :: "ty \<Rightarrow> cname"
where
  "the_Class (Class C) = C"

definition sup :: "'c prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty err"
where
  "sup P T\<^sub>1 T\<^sub>2 \<equiv>
  if is_refT T\<^sub>1 \<and> is_refT T\<^sub>2 then 
  OK (if T\<^sub>1 = NT then T\<^sub>2 else
      if T\<^sub>2 = NT then T\<^sub>1 else
      (Class (exec_lub (subcls1 P) (super P) (the_Class T\<^sub>1) (the_Class T\<^sub>2))))
  else 
  (if T\<^sub>1 = T\<^sub>2 then OK T\<^sub>1 else Err)"

lemma sup_def':
  "sup P = (\<lambda>T\<^sub>1 T\<^sub>2.
  if is_refT T\<^sub>1 \<and> is_refT T\<^sub>2 then 
  OK (if T\<^sub>1 = NT then T\<^sub>2 else
      if T\<^sub>2 = NT then T\<^sub>1 else
      (Class (exec_lub (subcls1 P) (super P) (the_Class T\<^sub>1) (the_Class T\<^sub>2))))
  else 
  (if T\<^sub>1 = T\<^sub>2 then OK T\<^sub>1 else Err))"
  by (simp add: sup_def fun_eq_iff)

abbreviation
  subtype :: "'c prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool"
  where "subtype P \<equiv> widen P"

definition esl :: "'c prog \<Rightarrow> ty esl"
where
  "esl P \<equiv> (types P, subtype P, sup P)"


(* FIXME: move to wellform *)
lemma is_class_is_subcls:
  "wf_prog m P \<Longrightarrow> is_class P C = P \<turnstile> C \<preceq>\<^sup>* Object"
(*<*)by (fastforce simp:is_class_def
                  elim: subcls_C_Object converse_rtranclE subcls1I
                  dest: subcls1D)
(*>*)


(* FIXME: move to wellform *)
lemma subcls_antisym:
  "\<lbrakk>wf_prog m P; P \<turnstile> C \<preceq>\<^sup>* D; P \<turnstile> D \<preceq>\<^sup>* C\<rbrakk> \<Longrightarrow> C = D"
  (*<*) by (auto dest: acyclic_subcls1 acyclic_impl_antisym_rtrancl antisymD) (*>*)

(* FIXME: move to wellform *)
lemma widen_antisym:
  "\<lbrakk> wf_prog m P; P \<turnstile> T \<le> U; P \<turnstile> U \<le> T \<rbrakk> \<Longrightarrow> T = U"
(*<*)
apply (cases T)
 apply (cases U)
 apply auto
apply (cases U)
 apply (auto elim!: subcls_antisym)
done
(*>*)

lemma order_widen [intro,simp]: 
  "wf_prog m P \<Longrightarrow> order (subtype P)"
(*<*)
  apply (unfold Semilat.order_def lesub_def)
  apply (auto intro: widen_trans widen_antisym)
  done
(*>*)

(* FIXME: move to TypeRel *)
lemma NT_widen:
  "P \<turnstile> NT \<le> T = (T = NT \<or> (\<exists>C. T = Class C))"
(*<*) by (cases T) auto (*>*)

(* FIXME: move to TypeRel *)
lemma Class_widen2: "P \<turnstile> Class C \<le> T = (\<exists>D. T = Class D \<and> P \<turnstile> C \<preceq>\<^sup>* D)"
(*<*) by (cases T) auto (*>*)
 
lemma wf_converse_subcls1_impl_acc_subtype:
  "wf ((subcls1 P)^-1) \<Longrightarrow> acc (subtype P)"
(*<*)
apply (unfold Semilat.acc_def lesssub_def)
apply (drule_tac p = "(subcls1 P)^-1 - Id" in wf_subset)
 apply blast
apply (drule wf_trancl)
apply (simp add: wf_eq_minimal)
apply clarify
apply (unfold lesub_def)
apply (rename_tac M T) 
apply (case_tac "\<exists>C. Class C \<in> M")
 prefer 2
 apply (case_tac T)
     apply fastforce
    apply fastforce
   apply fastforce
  apply simp
  apply (rule_tac x = NT in bexI)
   apply (rule allI)
   apply (rule impI, erule conjE) 
   apply (clarsimp simp add: NT_widen)
  apply simp
 apply clarsimp
apply (erule_tac x = "{C. Class C : M}" in allE)
apply auto
apply (rename_tac D)
apply (rule_tac x = "Class D" in bexI)
 prefer 2
 apply assumption
apply clarify
apply (clarsimp simp: Class_widen2)
apply (insert rtrancl_r_diff_Id [symmetric, of "subcls1 P"])
apply simp
apply (erule rtranclE)
 apply blast
apply (drule rtrancl_converseI)
apply (subgoal_tac "((subcls1 P)-Id)^-1 = ((subcls1 P)^-1 - Id)")
 prefer 2
 apply blast
apply simp
apply (blast intro: rtrancl_into_trancl2)
done
(*>*)

lemma wf_subtype_acc [intro, simp]:
  "wf_prog wf_mb P \<Longrightarrow> acc (subtype P)"
(*<*) by (rule wf_converse_subcls1_impl_acc_subtype, rule wf_subcls1) (*>*)

lemma exec_lub_refl [simp]: "exec_lub r f T T = T"
(*<*) by (simp add: exec_lub_def while_unfold) (*>*)

lemma closed_err_types:
  "wf_prog wf_mb P \<Longrightarrow> closed (err (types P)) (lift2 (sup P))"
(*<*)
  apply (unfold closed_def plussub_def lift2_def sup_def')
  apply (frule acyclic_subcls1)
  apply (frule single_valued_subcls1)
  apply (auto simp: is_type_def is_refT_def is_class_is_subcls split: err.split ty.splits)
  apply (blast dest!: is_lub_exec_lub is_lubD is_ubD intro!: is_ubI superI)
  done
(*>*)


lemma sup_subtype_greater:
  "\<lbrakk> wf_prog wf_mb P; is_type P t1; is_type P t2; sup P t1 t2 = OK s \<rbrakk> 
  \<Longrightarrow> subtype P t1 s \<and> subtype P t2 s"
(*<*)
proof -
  assume wf_prog: "wf_prog wf_mb P"
 
  { fix c1 c2
    assume is_class: "is_class P c1" "is_class P c2"
    with wf_prog 
    obtain 
      "P \<turnstile> c1 \<preceq>\<^sup>* Object"
      "P \<turnstile> c2 \<preceq>\<^sup>* Object"
      by (blast intro: subcls_C_Object)
    with single_valued_subcls1[OF wf_prog]
    obtain u where
      "is_lub ((subcls1 P)^* ) c1 c2 u"      
      by (blast dest: single_valued_has_lubs)
    moreover
    note acyclic_subcls1[OF wf_prog]
    moreover
    have "\<forall>x y. (x, y) \<in> subcls1 P \<longrightarrow> super P x = y"
      by (blast intro: superI)
    ultimately
    have "P \<turnstile> c1 \<preceq>\<^sup>* exec_lub (subcls1 P) (super P) c1 c2 \<and>
          P \<turnstile> c2 \<preceq>\<^sup>* exec_lub (subcls1 P) (super P) c1 c2"
      by (simp add: exec_lub_conv) (blast dest: is_lubD is_ubD)
  } note this [simp]

  assume "is_type P t1" "is_type P t2" "sup P t1 t2 = OK s"
  thus ?thesis
    apply (unfold sup_def) 
    apply (cases s)
    apply (auto simp add: is_refT_def split: if_split_asm)
    done
qed
(*>*)

lemma sup_subtype_smallest:
  "\<lbrakk> wf_prog wf_mb P; is_type P a; is_type P b; is_type P c; 
      subtype P a c; subtype P b c; sup P a b = OK d \<rbrakk>
  \<Longrightarrow> subtype P d c"
(*<*)
proof -
  assume wf_prog: "wf_prog wf_mb P"

  { fix c1 c2 D
    assume is_class: "is_class P c1" "is_class P c2"
    assume le: "P \<turnstile> c1 \<preceq>\<^sup>* D" "P \<turnstile> c2 \<preceq>\<^sup>* D"
    from wf_prog is_class
    obtain 
      "P \<turnstile> c1 \<preceq>\<^sup>* Object"
      "P \<turnstile> c2 \<preceq>\<^sup>* Object"
      by (blast intro: subcls_C_Object)
    with single_valued_subcls1[OF wf_prog]
    obtain u where
      lub: "is_lub ((subcls1 P)^* ) c1 c2 u"
      by (blast dest: single_valued_has_lubs)   
    with acyclic_subcls1[OF wf_prog]
    have "exec_lub (subcls1 P) (super P) c1 c2 = u"
      by (blast intro: superI exec_lub_conv)
    moreover
    from lub le
    have "P \<turnstile> u \<preceq>\<^sup>* D" 
      by (simp add: is_lub_def is_ub_def)
    ultimately     
    have "P \<turnstile> exec_lub (subcls1 P) (super P) c1 c2 \<preceq>\<^sup>* D"
      by blast
  } note this [intro]

  have [dest!]:
    "\<And>C T. P \<turnstile> Class C \<le> T \<Longrightarrow> \<exists>D. T=Class D \<and> P \<turnstile> C \<preceq>\<^sup>* D"
    by (frule Class_widen, auto)

  assume "is_type P a" "is_type P b" "is_type P c"
         "subtype P a c" "subtype P b c" "sup P a b = OK d"
  thus ?thesis
    by (auto simp add: sup_def is_refT_def
             split: if_split_asm)
qed
(*>*)

lemma sup_exists:
  "\<lbrakk> subtype P a c; subtype P b c \<rbrakk> \<Longrightarrow> \<exists>T. sup P a b = OK T"
(*<*)
apply (unfold sup_def)
apply (cases b)
apply auto
apply (cases a)
apply auto
apply (cases a)
apply auto
done
(*>*)

lemma err_semilat_JType_esl:
  "wf_prog wf_mb P \<Longrightarrow> err_semilat (esl P)"
(*<*)
proof -
  assume wf_prog: "wf_prog wf_mb P"  
  hence "order (subtype P)"..
  moreover from wf_prog
  have "closed (err (types P)) (lift2 (sup P))"
    by (rule closed_err_types)
  moreover
  from wf_prog have
    "(\<forall>x\<in>err (types P). \<forall>y\<in>err (types P). x \<sqsubseteq>\<^bsub>Err.le (subtype P)\<^esub> x \<squnion>\<^bsub>lift2 (sup P)\<^esub> y) \<and> 
     (\<forall>x\<in>err (types P). \<forall>y\<in>err (types P). y \<sqsubseteq>\<^bsub>Err.le (subtype P)\<^esub> x \<squnion>\<^bsub>lift2 (sup P)\<^esub> y)"
    by (auto simp add: lesub_def plussub_def Err.le_def lift2_def sup_subtype_greater split: err.split)
  moreover from wf_prog have
    "\<forall>x\<in>err (types P). \<forall>y\<in>err (types P). \<forall>z\<in>err (types P). 
    x \<sqsubseteq>\<^bsub>Err.le (subtype P)\<^esub> z \<and> y \<sqsubseteq>\<^bsub>Err.le (subtype P)\<^esub> z \<longrightarrow> x \<squnion>\<^bsub>lift2 (sup P)\<^esub> y \<sqsubseteq>\<^bsub>Err.le (subtype P)\<^esub> z"
    by (unfold lift2_def plussub_def lesub_def Err.le_def)
       (auto intro: sup_subtype_smallest dest:sup_exists split: err.split)
  ultimately show ?thesis by (simp add: esl_def semilat_def sl_def Err.sl_def)
qed
(*>*)


end
