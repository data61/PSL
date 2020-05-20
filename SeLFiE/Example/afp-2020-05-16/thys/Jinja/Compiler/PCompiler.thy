(*  Title:      Jinja/Compiler/PCompiler.thy

    Author:     Tobias Nipkow
    Copyright   TUM 2003
*)

section \<open>Program Compilation\<close>

theory PCompiler
imports "../Common/WellForm"
begin

definition compM :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mdecl \<Rightarrow> 'b mdecl"
where
  "compM f  \<equiv>  \<lambda>(M, Ts, T, m). (M, Ts, T, f m)"

definition compC :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a cdecl \<Rightarrow> 'b cdecl"
where
  "compC f  \<equiv>  \<lambda>(C,D,Fdecls,Mdecls). (C,D,Fdecls, map (compM f) Mdecls)"

definition compP :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a prog \<Rightarrow> 'b prog"
where
  "compP f  \<equiv>  map (compC f)"

text\<open>Compilation preserves the program structure.  Therfore lookup
functions either commute with compilation (like method lookup) or are
preserved by it (like the subclass relation).\<close>

lemma map_of_map4:
  "map_of (map (\<lambda>(x,a,b,c).(x,a,b,f c)) ts) =
  map_option (\<lambda>(a,b,c).(a,b,f c)) \<circ> (map_of ts)"
(*<*)
apply(induct ts)
 apply simp
apply(rule ext)
apply fastforce
done
(*>*)


lemma class_compP:
  "class P C = Some (D, fs, ms)
  \<Longrightarrow> class (compP f P) C = Some (D, fs, map (compM f) ms)"
(*<*)by(simp add:class_def compP_def compC_def map_of_map4)(*>*)


lemma class_compPD:
  "class (compP f P) C = Some (D, fs, cms)
  \<Longrightarrow> \<exists>ms. class P C = Some(D,fs,ms) \<and> cms = map (compM f) ms"
(*<*)by(clarsimp simp add:class_def compP_def compC_def map_of_map4)(*>*)


lemma [simp]: "is_class (compP f P) C = is_class P C"
(*<*)by(auto simp:is_class_def dest: class_compP class_compPD)(*>*)


lemma [simp]: "class (compP f P) C = map_option (\<lambda>c. snd(compC f (C,c))) (class P C)"
(*<*)
apply(simp add:compP_def compC_def class_def map_of_map4)
apply(simp add:split_def)
done
(*>*)


lemma sees_methods_compP:
  "P \<turnstile> C sees_methods Mm \<Longrightarrow>
  compP f P \<turnstile> C sees_methods (map_option (\<lambda>((Ts,T,m),D). ((Ts,T,f m),D)) \<circ> Mm)"
(*<*)
apply(erule Methods.induct)
 apply(rule sees_methods_Object)
  apply(erule class_compP)
 apply(rule ext)
 apply(simp add:compM_def map_of_map4 option.map_comp)
 apply(case_tac "map_of ms x")
  apply simp
 apply fastforce
apply(rule sees_methods_rec)
   apply(erule class_compP)
  apply assumption
 apply assumption
apply(rule ext)
apply(simp add:map_add_def compM_def map_of_map4 option.map_comp split:option.split)
done
(*>*)


lemma sees_method_compP:
  "P \<turnstile> C sees M: Ts\<rightarrow>T = m in D \<Longrightarrow>
  compP f P \<turnstile> C sees M: Ts\<rightarrow>T = (f m) in D"
(*<*)by(fastforce elim:sees_methods_compP simp add:Method_def)(*>*)


lemma [simp]:
  "P \<turnstile> C sees M: Ts\<rightarrow>T = m in D \<Longrightarrow>
  method (compP f P) C M = (D,Ts,T,f m)"
(*<*)
apply(drule sees_method_compP)
apply(simp add:method_def)
apply(rule the_equality)
 apply simp
apply(fastforce dest:sees_method_fun)
done
(*>*)


lemma sees_methods_compPD:
  "\<lbrakk> cP \<turnstile> C sees_methods Mm'; cP = compP f P \<rbrakk> \<Longrightarrow>
  \<exists>Mm. P \<turnstile> C sees_methods Mm \<and>
        Mm' = (map_option (\<lambda>((Ts,T,m),D). ((Ts,T,f m),D)) \<circ> Mm)"
(*<*)
apply(erule Methods.induct)
 apply(clarsimp simp:compC_def)
 apply(rule exI)
 apply(rule conjI, erule sees_methods_Object)
 apply(rule refl)
 apply(rule ext)
 apply(simp add:compM_def map_of_map4 option.map_comp)
 apply(case_tac "map_of b x")
  apply simp
 apply fastforce
apply(clarsimp simp:compC_def)
apply(rule exI, rule conjI)
apply(erule (2) sees_methods_rec)
 apply(rule refl)
apply(rule ext)
apply(simp add:map_add_def compM_def map_of_map4 option.map_comp split:option.split)
done
(*>*)


lemma sees_method_compPD:
  "compP f P \<turnstile> C sees M: Ts\<rightarrow>T = fm in D \<Longrightarrow>
  \<exists>m. P \<turnstile> C sees M: Ts\<rightarrow>T = m in D \<and> f m = fm"
(*<*)
apply(simp add:Method_def)
apply clarify
apply(drule sees_methods_compPD[OF _ refl])
apply clarsimp
apply blast
done
(*>*)


lemma [simp]: "subcls1(compP f P) = subcls1 P"
(*<*)
by(fastforce simp add: is_class_def compC_def intro:subcls1I order_antisym dest:subcls1D)
(*>*)


lemma compP_widen[simp]: "(compP f P \<turnstile> T \<le> T') = (P \<turnstile> T \<le> T')"
(*<*)by(cases T')(simp_all add:widen_Class)(*>*)


lemma [simp]: "(compP f P \<turnstile> Ts [\<le>] Ts') = (P \<turnstile> Ts [\<le>] Ts')"
(*<*)
apply(induct Ts)
 apply simp
apply(cases Ts')
apply(auto simp:fun_of_def)
done
(*>*)


lemma [simp]: "is_type (compP f P) T = is_type P T"
(*<*)by(cases T) simp_all(*>*)


lemma [simp]: "(compP (f::'a\<Rightarrow>'b) P \<turnstile> C has_fields FDTs) = (P \<turnstile> C has_fields FDTs)"
(*<*)
 (is "?A = ?B")
proof
  { fix cP::"'b prog" assume "cP \<turnstile> C has_fields FDTs"
    hence "cP = compP f P \<Longrightarrow> P \<turnstile> C has_fields FDTs"
    proof induct
      case has_fields_Object
      thus ?case by(fast intro:Fields.has_fields_Object dest:class_compPD)
    next
      case has_fields_rec
      thus ?case by(fast intro:Fields.has_fields_rec dest:class_compPD)
    qed
  } note lem = this
  assume ?A
  with lem show ?B by blast
next
  assume ?B
  thus ?A
  proof induct
    case has_fields_Object
    thus ?case by(fast intro:Fields.has_fields_Object class_compP)
  next
    case has_fields_rec
    thus ?case by(fast intro:Fields.has_fields_rec class_compP)
  qed
qed
(*>*)


lemma [simp]: "fields (compP f P) C = fields P C"
(*<*)by(simp add:fields_def)(*>*)


lemma [simp]: "(compP f P \<turnstile> C sees F:T in D) = (P \<turnstile> C sees F:T in D)"
(*<*)by(simp add:sees_field_def)(*>*)


lemma [simp]: "field (compP f P) F D = field P F D"
(*<*)by(simp add:field_def)(*>*)


subsection\<open>Invariance of @{term wf_prog} under compilation\<close>

lemma [iff]: "distinct_fst (compP f P) = distinct_fst P"
(*<*)
apply(simp add:distinct_fst_def compP_def compC_def)
apply(induct P)
apply (auto simp:image_iff)
done
(*>*)


lemma [iff]: "distinct_fst (map (compM f) ms) = distinct_fst ms"
(*<*)
apply(simp add:distinct_fst_def compM_def)
apply(induct ms)
apply (auto simp:image_iff)
done
(*>*)


lemma [iff]: "wf_syscls (compP f P) = wf_syscls P"
(*<*)by(simp add:wf_syscls_def compP_def compC_def image_def Bex_def)(*>*)


lemma [iff]: "wf_fdecl (compP f P) = wf_fdecl P"
(*<*)by(simp add:wf_fdecl_def)(*>*)


lemma set_compP:
 "((C,D,fs,ms') \<in> set(compP f P)) =
  (\<exists>ms. (C,D,fs,ms) \<in> set P \<and> ms' = map (compM f) ms)"
(*<*)by(fastforce simp add:compP_def compC_def image_iff Bex_def)(*>*)


lemma wf_cdecl_compPI:
  "\<lbrakk> \<And>C M Ts T m. 
     \<lbrakk> wf_mdecl wf\<^sub>1 P C (M,Ts,T,m); P \<turnstile> C sees M:Ts\<rightarrow>T = m in C \<rbrakk>
     \<Longrightarrow> wf_mdecl wf\<^sub>2 (compP f P) C (M,Ts,T, f m);
    \<forall>x\<in>set P. wf_cdecl wf\<^sub>1 P x; x \<in> set (compP f P); wf_prog p P \<rbrakk>
  \<Longrightarrow> wf_cdecl wf\<^sub>2 (compP f P) x"
(*<*)
apply(clarsimp simp add:wf_cdecl_def Ball_def set_compP)
apply(rename_tac C D fs ms)
apply(rule conjI)
 apply (clarsimp simp:compM_def)
 apply (drule (2) mdecl_visible)
 apply simp
apply(clarify)
apply(drule sees_method_compPD[where f = f])
apply clarsimp 
apply(fastforce simp:image_iff compM_def)
done
(*>*)


lemma wf_prog_compPI:
assumes lift: 
  "\<And>C M Ts T m. 
    \<lbrakk> P \<turnstile> C sees M:Ts\<rightarrow>T = m in C; wf_mdecl wf\<^sub>1 P C (M,Ts,T,m) \<rbrakk>
    \<Longrightarrow> wf_mdecl wf\<^sub>2 (compP f P) C (M,Ts,T, f m)"
and wf: "wf_prog wf\<^sub>1 P"
shows "wf_prog wf\<^sub>2 (compP f P)"
(*<*)
using wf
by (simp add:wf_prog_def) (blast intro:wf_cdecl_compPI lift wf)
(*>*)


end
