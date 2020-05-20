(*  Title:      HOL/MicroJava/J/State.thy

    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

section \<open>Objects and the Heap\<close>

theory Objects imports TypeRel Value begin

subsection\<open>Objects\<close>

type_synonym
  fields = "vname \<times> cname \<rightharpoonup> val"  \<comment> \<open>field name, defining class, value\<close>
type_synonym
  obj = "cname \<times> fields"    \<comment> \<open>class instance with class name and fields\<close>

definition obj_ty  :: "obj \<Rightarrow> ty"
where
  "obj_ty obj  \<equiv>  Class (fst obj)"

definition init_fields :: "((vname \<times> cname) \<times> ty) list \<Rightarrow> fields"
where
  "init_fields  \<equiv>  map_of \<circ> map (\<lambda>(F,T). (F,default_val T))"
  
  \<comment> \<open>a new, blank object with default values in all fields:\<close>
definition blank :: "'m prog \<Rightarrow> cname \<Rightarrow> obj"
where
  "blank P C  \<equiv>  (C,init_fields (fields P C))" 

lemma [simp]: "obj_ty (C,fs) = Class C"
(*<*)by (simp add: obj_ty_def)(*>*)

subsection\<open>Heap\<close>

type_synonym heap  = "addr \<rightharpoonup> obj"

abbreviation
  cname_of :: "heap \<Rightarrow> addr \<Rightarrow> cname" where
  "cname_of hp a == fst (the (hp a))"

definition new_Addr  :: "heap \<Rightarrow> addr option"
where
  "new_Addr h  \<equiv>  if \<exists>a. h a = None then Some(LEAST a. h a = None) else None"

definition cast_ok :: "'m prog \<Rightarrow> cname \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> bool"
where
  "cast_ok P C h v  \<equiv>  v = Null \<or> P \<turnstile> cname_of h (the_Addr v) \<preceq>\<^sup>* C"

definition hext :: "heap \<Rightarrow> heap \<Rightarrow> bool" ("_ \<unlhd> _" [51,51] 50)
where
  "h \<unlhd> h'  \<equiv>  \<forall>a C fs. h a = Some(C,fs) \<longrightarrow> (\<exists>fs'. h' a = Some(C,fs'))"

primrec typeof_h :: "heap \<Rightarrow> val \<Rightarrow> ty option"  ("typeof\<^bsub>_\<^esub>")
where
  "typeof\<^bsub>h\<^esub>  Unit    = Some Void"
| "typeof\<^bsub>h\<^esub>  Null    = Some NT"
| "typeof\<^bsub>h\<^esub> (Bool b) = Some Boolean"
| "typeof\<^bsub>h\<^esub> (Intg i) = Some Integer"
| "typeof\<^bsub>h\<^esub> (Addr a) = (case h a of None \<Rightarrow> None | Some(C,fs) \<Rightarrow> Some(Class C))"

lemma new_Addr_SomeD:
  "new_Addr h = Some a \<Longrightarrow> h a = None"
 (*<*)by(fastforce simp add:new_Addr_def split:if_splits intro:LeastI)(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some Boolean) = (\<exists>b. v = Bool b)"
 (*<*)by(induct v) auto(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some Integer) = (\<exists>i. v = Intg i)"
(*<*)by(cases v) auto(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some NT) = (v = Null)"
 (*<*)by(cases v) auto(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some(Class C)) = (\<exists>a fs. v = Addr a \<and> h a = Some(C,fs))"
 (*<*)by(cases v) auto(*>*)

lemma [simp]: "h a = Some(C,fs) \<Longrightarrow> typeof\<^bsub>(h(a\<mapsto>(C,fs')))\<^esub> v = typeof\<^bsub>h\<^esub> v"
 (*<*)by(induct v) (auto simp:fun_upd_apply)(*>*)

text\<open>For literal values the first parameter of @{term typeof} can be
set to @{term Map.empty} because they do not contain addresses:\<close>

abbreviation
  typeof :: "val \<Rightarrow> ty option" where
  "typeof v == typeof_h Map.empty v"

lemma typeof_lit_typeof:
  "typeof v = Some T \<Longrightarrow> typeof\<^bsub>h\<^esub> v = Some T"
 (*<*)by(cases v) auto(*>*)

lemma typeof_lit_is_type: 
  "typeof v = Some T \<Longrightarrow> is_type P T"
 (*<*)by (induct v) (auto simp:is_type_def)(*>*)


subsection \<open>Heap extension \<open>\<unlhd>\<close>\<close>

lemma hextI: "\<forall>a C fs. h a = Some(C,fs) \<longrightarrow> (\<exists>fs'. h' a = Some(C,fs')) \<Longrightarrow> h \<unlhd> h'"
(*<*)
apply (unfold hext_def)
apply auto
done
(*>*)

lemma hext_objD: "\<lbrakk> h \<unlhd> h'; h a = Some(C,fs) \<rbrakk> \<Longrightarrow> \<exists>fs'. h' a = Some(C,fs')"
(*<*)
apply (unfold hext_def)
apply (force)
done
(*>*)

lemma hext_refl [iff]: "h \<unlhd> h"
(*<*)
apply (rule hextI)
apply (fast)
done
(*>*)

lemma hext_new [simp]: "h a = None \<Longrightarrow> h \<unlhd> h(a\<mapsto>x)"
(*<*)
apply (rule hextI)
apply (auto simp:fun_upd_apply)
done
(*>*)

lemma hext_trans: "\<lbrakk> h \<unlhd> h'; h' \<unlhd> h'' \<rbrakk> \<Longrightarrow> h \<unlhd> h''"
(*<*)
apply (rule hextI)
apply (fast dest: hext_objD)
done
(*>*)

lemma hext_upd_obj: "h a = Some (C,fs) \<Longrightarrow> h \<unlhd> h(a\<mapsto>(C,fs'))"
(*<*)
apply (rule hextI)
apply (auto simp:fun_upd_apply)
done
(*>*)

lemma hext_typeof_mono: "\<lbrakk> h \<unlhd> h'; typeof\<^bsub>h\<^esub> v = Some T \<rbrakk> \<Longrightarrow> typeof\<^bsub>h'\<^esub> v = Some T"
(*<*)
apply(cases v)
    apply simp
   apply simp
  apply simp
 apply simp
apply(fastforce simp:hext_def)
done
(*>*)

text \<open>Code generator setup for @{term "new_Addr"}\<close>

definition gen_new_Addr :: "heap \<Rightarrow> addr \<Rightarrow> addr option"
where "gen_new_Addr h n \<equiv> if \<exists>a. a \<ge> n \<and> h a = None then Some(LEAST a. a \<ge> n \<and> h a = None) else None"

lemma new_Addr_code_code [code]:
  "new_Addr h = gen_new_Addr h 0"
by(simp add: new_Addr_def gen_new_Addr_def split del: if_split cong: if_cong)

lemma gen_new_Addr_code [code]:
  "gen_new_Addr h n = (if h n = None then Some n else gen_new_Addr h (Suc n))"
apply(simp add: gen_new_Addr_def)
apply(rule impI)
apply(rule conjI)
 apply safe[1]
  apply(fastforce intro: Least_equality)
 apply(rule arg_cong[where f=Least])
 apply(rule ext)
 apply(case_tac "n = ac")
  apply simp
 apply(auto)[1]
apply clarify
apply(subgoal_tac "a = n")
 apply simp
 apply(rule Least_equality)
 apply auto[2]
apply(rule ccontr)
apply(erule_tac x="a" in allE)
apply simp
done

end
