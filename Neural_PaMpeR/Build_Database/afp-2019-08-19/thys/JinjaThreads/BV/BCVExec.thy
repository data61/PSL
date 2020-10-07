(*  Title:      JinjaThreads/BV/BCVExec.thy
    Author:     Andreas Lochbihler
*)

section \<open>Code generation for the byte code verifier\<close>

theory BCVExec
imports
  BVNoTypeError
  BVExec
begin

lemmas [code_unfold] = exec_lub_def

lemmas [code] = JVM_le_unfold[THEN meta_eq_to_obj_eq]

lemma err_code [code]:
  "Err.err A = Collect (case_err True (\<lambda>x. x \<in> A))"
by(auto simp add: err_def split: err.split)

lemma list_code [code]:
  "list n A = {xs. size xs = n \<and> list_all (\<lambda>x. x \<in> A) xs}"
unfolding list_def
by(auto intro!: ext simp add: list_all_iff)

lemma opt_code [code]:
  "opt A = Collect (case_option True (\<lambda>x. x \<in> A))"
by(auto simp add: opt_def split: option.split)

lemma Times_code [code_unfold]:
  "Sigma A (%_. B) = {(a, b). a \<in> A \<and> b \<in> B}"
by auto

lemma upto_esl_code [code]:
  "upto_esl m (A, r, f) = (Union ((\<lambda>n. list n A) ` {..m}), Listn.le r, Listn.sup f)"
by(auto simp add: upto_esl_def)

lemmas [code] = lesub_def plussub_def

lemma JVM_sup_unfold [code]:
  "JVM_SemiType.sup S m n = 
  lift2 (Opt.sup (Product.sup (Listn.sup (SemiType.sup S)) (\<lambda>x y. OK (map2 (lift2 (SemiType.sup S)) x y))))"
unfolding JVM_SemiType.sup_def JVM_SemiType.sl_def Opt.esl_def Err.sl_def
  stk_esl_def loc_sl_def Product.esl_def Listn.sl_def upto_esl_def 
  SemiType.esl_def Err.esl_def 
by simp

(* FIXME: why is @{thm sup_fun_def} declared [code del] in Lattices.thy? *)
declare sup_fun_def [code] 

lemma [code]: "states P mxs mxl = fst(sl P mxs mxl)"
unfolding states_def ..

lemma check_types_code [code]:
  "check_types P mxs mxl \<tau>s = (list_all (\<lambda>x. x \<in> (states P mxs mxl)) \<tau>s)"
unfolding check_types_def by(auto simp add: list_all_iff)

lemma wf_jvm_prog_code [code_unfold]:
  "wf_jvm_prog = wf_jvm_prog\<^sub>k"
by(simp add: fun_eq_iff jvm_kildall_correct)

definition "wf_jvm_prog' = wf_jvm_prog"

(* Formal code generation test *)
ML_val \<open>@{code wf_jvm_prog'}\<close>

end
