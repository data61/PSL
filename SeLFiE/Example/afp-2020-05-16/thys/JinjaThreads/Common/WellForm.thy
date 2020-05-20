(*  Title:      JinjaThreads/Common/WellForm.thy
    Author:     Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory Common/WellForm.thy by Tobias Nipkow
*)

section \<open>Generic Well-formedness of programs\<close>

theory WellForm
imports
  SystemClasses
  ExternalCall
begin

text \<open>\noindent This theory defines global well-formedness conditions
for programs but does not look inside method bodies.  Hence it works
for both Jinja and JVM programs. Well-typing of expressions is defined
elsewhere (in theory \<open>WellType\<close>).

Because JinjaThreads does not have method overloading, its policy for method
overriding is the classical one: \emph{covariant in the result type
but contravariant in the argument types.} This means the result type
of the overriding method becomes more specific, the argument types
become more general.
\<close>

type_synonym 'm wf_mdecl_test = "'m prog \<Rightarrow> cname \<Rightarrow> 'm mdecl \<Rightarrow> bool"

definition wf_fdecl :: "'m prog \<Rightarrow> fdecl \<Rightarrow> bool"
where "wf_fdecl P \<equiv> \<lambda>(F,T,fm). is_type P T"

definition wf_mdecl :: "'m wf_mdecl_test \<Rightarrow> 'm prog \<Rightarrow> cname \<Rightarrow> 'm mdecl' \<Rightarrow> bool" where 
  "wf_mdecl wf_md P C \<equiv> 
  \<lambda>(M,Ts,T,m). (\<forall>T\<in>set Ts. is_type P T) \<and> is_type P T \<and> 
    (case m of Native \<Rightarrow> C\<bullet>M(Ts) :: T | \<lfloor>mb\<rfloor> \<Rightarrow> wf_md P C (M,Ts,T,mb))"

fun wf_overriding :: "'m prog \<Rightarrow> cname \<Rightarrow> 'm mdecl' \<Rightarrow> bool"
where
  "wf_overriding P D (M,Ts,T,m) =
  (\<forall>D' Ts' T' m'. P \<turnstile> D sees M:Ts' \<rightarrow> T' = m' in D' \<longrightarrow> P \<turnstile> Ts' [\<le>] Ts \<and> P \<turnstile> T \<le> T')"

definition wf_cdecl :: "'m wf_mdecl_test \<Rightarrow> 'm prog \<Rightarrow> 'm cdecl \<Rightarrow> bool"
where
  "wf_cdecl wf_md P  \<equiv>  \<lambda>(C,(D,fs,ms)).
  (\<forall>f\<in>set fs. wf_fdecl P f) \<and> distinct_fst fs \<and>
  (\<forall>m\<in>set ms. wf_mdecl wf_md P C m) \<and>
  distinct_fst ms \<and>
  (C \<noteq> Object \<longrightarrow>
   is_class P D \<and> \<not> P \<turnstile> D \<preceq>\<^sup>* C \<and>
   (\<forall>m\<in>set ms. wf_overriding P D m)) \<and>
  (C = Thread \<longrightarrow> (\<exists>m. (run, [], Void, m) \<in> set ms))"

definition wf_prog :: "'m wf_mdecl_test \<Rightarrow> 'm prog \<Rightarrow> bool"
where 
  "wf_prog wf_md P \<longleftrightarrow> wf_syscls P \<and> distinct_fst (classes P) \<and> (\<forall>c \<in> set (classes P). wf_cdecl wf_md P c)"

lemma wf_prog_def2:
  "wf_prog wf_md P \<longleftrightarrow> wf_syscls P \<and> (\<forall>C rest. class P C = \<lfloor>rest\<rfloor> \<longrightarrow> wf_cdecl wf_md P (C, rest)) \<and> distinct_fst (classes P)"
by(cases P)(auto simp add: wf_prog_def dest: map_of_SomeD map_of_SomeI)

subsection\<open>Well-formedness lemmas\<close>

lemma wf_prog_wf_syscls: "wf_prog wf_md P \<Longrightarrow> wf_syscls P"
by(simp add: wf_prog_def)

lemma class_wf: 
  "\<lbrakk>class P C = Some c; wf_prog wf_md P\<rbrakk> \<Longrightarrow> wf_cdecl wf_md P (C,c)"
by (cases P) (fastforce dest: map_of_SomeD simp add: wf_prog_def)

lemma [simp]:
  assumes "wf_prog wf_md P"
  shows class_Object: "\<exists>C fs ms. class P Object = Some (C,fs,ms)"
  and class_Thread:  "\<exists>C fs ms. class P Thread = Some (C,fs,ms)"
using wf_prog_wf_syscls[OF assms]
by(rule wf_syscls_class_Object wf_syscls_class_Thread)+

lemma [simp]:
  assumes "wf_prog wf_md P"
  shows is_class_Object: "is_class P Object"
  and is_class_Thread: "is_class P Thread"
using wf_prog_wf_syscls[OF assms] by simp_all

lemma xcpt_subcls_Throwable:
  "\<lbrakk> C \<in> sys_xcpts; wf_prog wf_md P \<rbrakk> \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* Throwable"
by(simp add: wf_prog_wf_syscls wf_syscls_xcpt_subcls_Throwable)

lemma is_class_Throwable:
  "wf_prog wf_md P \<Longrightarrow> is_class P Throwable"
by(rule wf_prog_wf_syscls wf_syscls_is_class_Throwable)+

lemma is_class_sub_Throwable:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> C \<preceq>\<^sup>* Throwable \<rbrakk> \<Longrightarrow> is_class P C"
by(rule wf_syscls_is_class_sub_Throwable[OF wf_prog_wf_syscls])

lemma is_class_xcpt:
  "\<lbrakk> C \<in> sys_xcpts; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_class P C"
by(rule wf_syscls_is_class_xcpt[OF _ wf_prog_wf_syscls])

context heap_base begin
lemma wf_preallocatedE:
  assumes "wf_prog wf_md P"
  and "preallocated h"
  and "C \<in> sys_xcpts"
  obtains "typeof_addr h (addr_of_sys_xcpt C) = \<lfloor>Class_type C\<rfloor>" "P \<turnstile> C \<preceq>\<^sup>* Throwable"
proof -
  from \<open>preallocated h\<close> \<open>C \<in> sys_xcpts\<close> have "typeof_addr h (addr_of_sys_xcpt C) = \<lfloor>Class_type C\<rfloor>" 
    by(rule typeof_addr_sys_xcp)
  moreover from \<open>C \<in> sys_xcpts\<close> \<open>wf_prog wf_md P\<close> have "P \<turnstile> C \<preceq>\<^sup>* Throwable" by(rule xcpt_subcls_Throwable)
  ultimately show thesis by(rule that)
qed

lemma wf_preallocatedD:
  assumes "wf_prog wf_md P"
  and "preallocated h"
  and "C \<in> sys_xcpts"
  shows "typeof_addr h (addr_of_sys_xcpt C) = \<lfloor>Class_type C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable"
using assms
by(rule wf_preallocatedE) blast

end

lemma (in heap_conf) hconf_start_heap:
  "wf_prog wf_md P \<Longrightarrow> hconf start_heap"
unfolding start_heap_def start_heap_data_def initialization_list_def sys_xcpts_list_def
using hconf_empty
by -(simp add: create_initial_object_simps del: hconf_empty, clarsimp split: prod.split elim!: not_empty_pairE simp del: hconf_empty, drule (1) allocate_Eps, drule (1) hconf_allocate_mono, simp add: is_class_xcpt)+

lemma subcls1_wfD:
  "\<lbrakk> P \<turnstile> C \<prec>\<^sup>1 D; wf_prog wf_md P \<rbrakk> \<Longrightarrow> D \<noteq> C \<and> \<not> (subcls1 P)\<^sup>+\<^sup>+ D C"
apply( frule tranclp.r_into_trancl[where r="subcls1 P"])
apply( drule subcls1D)
apply(clarify)
apply( drule (1) class_wf)
apply( unfold wf_cdecl_def)
apply(rule conjI)
 apply(force)
apply(unfold reflclp_tranclp[symmetric, where r="subcls1 P"])
apply(blast)
done

lemma wf_cdecl_supD: 
  "\<lbrakk>wf_cdecl wf_md P (C,D,r); C \<noteq> Object\<rbrakk> \<Longrightarrow> is_class P D"
(*<*)by (auto simp: wf_cdecl_def)(*>*)


lemma subcls_asym:
  "\<lbrakk> wf_prog wf_md P; (subcls1 P)\<^sup>+\<^sup>+ C D \<rbrakk> \<Longrightarrow> \<not> (subcls1 P)\<^sup>+\<^sup>+ D C"
(*<*)
apply(erule tranclp.cases)
apply(fast dest!: subcls1_wfD )
apply(fast dest!: subcls1_wfD intro: tranclp_trans)
done
(*>*)


lemma subcls_irrefl:
  "\<lbrakk> wf_prog wf_md P; (subcls1 P)\<^sup>+\<^sup>+ C D\<rbrakk> \<Longrightarrow> C \<noteq> D"
(*<*)
apply (erule tranclp_trans_induct)
apply  (auto dest: subcls1_wfD subcls_asym)
done
(*>*)

lemma acyclicP_def:
  "acyclicP r \<longleftrightarrow> (\<forall>x. \<not> r^++ x x)"
  unfolding acyclic_def trancl_def
by(auto)

lemma acyclic_subcls1:
  "wf_prog wf_md P \<Longrightarrow> acyclicP (subcls1 P)"
by(unfold acyclicP_def)(fast dest: subcls_irrefl)

lemma finite_conversep: "finite {(x, y). r\<inverse>\<inverse> x y} = finite {(x, y). r x y}"
by(subst finite_converse[unfolded converse_unfold, symmetric]) simp

lemma acyclicP_wf_subcls1:
  "acyclicP (subcls1 P) \<Longrightarrow> wfP ((subcls1 P)\<inverse>\<inverse>)"
unfolding wfP_def
by(rule finite_acyclic_wf)(simp_all only: finite_conversep finite_subcls1 acyclicP_converse)

lemma wf_subcls1:
  "wf_prog wf_md P \<Longrightarrow> wfP ((subcls1 P)\<inverse>\<inverse>)"
by(rule acyclicP_wf_subcls1)(rule acyclic_subcls1)

lemma single_valued_subcls1:
  "wf_prog wf_md G \<Longrightarrow> single_valuedp (subcls1 G)"
(*<*)
by(auto simp:wf_prog_def distinct_fst_def single_valuedp_def dest!:subcls1D)
(*>*)


lemma subcls_induct: 
  "\<lbrakk> wf_prog wf_md P; \<And>C. \<forall>D. (subcls1 P)\<^sup>+\<^sup>+ C D \<longrightarrow> Q D \<Longrightarrow> Q C \<rbrakk> \<Longrightarrow> Q C"
(*<*)
  (is "?A \<Longrightarrow> PROP ?P \<Longrightarrow> _")
proof -
  assume p: "PROP ?P"
  assume ?A thus ?thesis apply -
apply(drule wf_subcls1)
apply(drule wfP_trancl)
apply(simp only: tranclp_converse)
apply(erule_tac a = C in wfP_induct)
apply(rule p)
apply(auto)
done
qed
(*>*)


lemma subcls1_induct_aux:
  "\<lbrakk> is_class P C; wf_prog wf_md P; Q Object;
    \<And>C D fs ms.
    \<lbrakk> C \<noteq> Object; is_class P C; class P C = Some (D,fs,ms) \<and>
      wf_cdecl wf_md P (C,D,fs,ms) \<and> P \<turnstile> C \<prec>\<^sup>1 D \<and> is_class P D \<and> Q D\<rbrakk> \<Longrightarrow> Q C \<rbrakk>
  \<Longrightarrow> Q C"
(*<*)
  (is "?A \<Longrightarrow> ?B \<Longrightarrow> ?C \<Longrightarrow> PROP ?P \<Longrightarrow> _")
proof -
  assume p: "PROP ?P"
  assume ?A ?B ?C thus ?thesis apply -
apply(unfold is_class_def)
apply( rule impE)
prefer 2
apply(   assumption)
prefer 2
apply(  assumption)
apply( erule thin_rl)
apply( rule subcls_induct)
apply(  assumption)
apply( rule impI)
apply( case_tac "C = Object")
apply(  fast)
apply safe
apply( frule (1) class_wf)
apply( frule (1) wf_cdecl_supD)

apply( subgoal_tac "P \<turnstile> C \<prec>\<^sup>1 a")
apply( erule_tac [2] subcls1I)
apply(  rule p)
apply (unfold is_class_def)
apply auto
done
qed
(*>*)

lemma subcls1_induct [consumes 2, case_names Object Subcls]:
  "\<lbrakk> wf_prog wf_md P; is_class P C; Q Object;
    \<And>C D. \<lbrakk>C \<noteq> Object; P \<turnstile> C \<prec>\<^sup>1 D; is_class P D; Q D\<rbrakk> \<Longrightarrow> Q C \<rbrakk>
  \<Longrightarrow> Q C"
(*<*)
  apply (erule subcls1_induct_aux, assumption, assumption)
  apply blast
  done
(*>*)


lemma subcls_C_Object:
  "\<lbrakk> is_class P C; wf_prog wf_md P \<rbrakk> \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* Object"
(*<*)
apply(erule (1) subcls1_induct)
 apply( fast)
apply(erule (1) converse_rtranclp_into_rtranclp)
done
(*>*)

lemma converse_subcls_is_class:
  assumes wf: "wf_prog wf_md P"
  shows "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* D; is_class P C \<rbrakk> \<Longrightarrow> is_class P D"
proof(induct rule: rtranclp_induct)
  assume "is_class P C"
  thus "is_class P C" .
next
  fix D E
  assume PDE: "P \<turnstile> D \<prec>\<^sup>1 E"
    and IH: "is_class P C \<Longrightarrow> is_class P D"
    and iPC: "is_class P C"
  have "is_class P D" by (rule IH[OF iPC])
  with PDE obtain fsD MsD where classD: "class P D = \<lfloor>(E, fsD, MsD)\<rfloor>"
    by(auto simp add: is_class_def elim!: subcls1.cases)
  thus "is_class P E" using wf PDE
    by(auto elim!: subcls1.cases dest: class_wf simp: wf_cdecl_def)
qed

lemma is_class_is_subcls:
  "wf_prog m P \<Longrightarrow> is_class P C = P \<turnstile> C \<preceq>\<^sup>* Object"
(*<*)by (fastforce simp:is_class_def
                  elim: subcls_C_Object converse_rtranclpE subcls1I
                  dest: subcls1D)
(*>*)

lemma subcls_antisym:
  "\<lbrakk>wf_prog m P; P \<turnstile> C \<preceq>\<^sup>* D; P \<turnstile> D \<preceq>\<^sup>* C\<rbrakk> \<Longrightarrow> C = D"
apply(drule acyclic_subcls1)
apply(drule acyclic_impl_antisym_rtrancl)
apply(drule antisymD)
apply(unfold Transitive_Closure.rtrancl_def)
apply(auto)
done

lemma is_type_pTs:
  "\<lbrakk> wf_prog wf_md P; class P C = \<lfloor>(S,fs,ms)\<rfloor>; (M,Ts,T,m) \<in> set ms \<rbrakk> \<Longrightarrow> set Ts \<subseteq> types P"
by(fastforce dest: class_wf simp add: wf_cdecl_def wf_mdecl_def)

lemma widen_asym_1: 
  assumes wfP: "wf_prog wf_md P"
  shows "P \<turnstile> C \<le> D \<Longrightarrow> C = D \<or> \<not> (P \<turnstile> D \<le> C)"
proof (erule widen.induct)
  fix T
  show "T = T \<or> \<not> (P \<turnstile> T \<le> T)" by simp
next
  fix C D
  assume CscD: "P \<turnstile> C \<preceq>\<^sup>* D"
  then have CpscD: "C = D \<or> (C \<noteq> D \<and> (subcls1 P)\<^sup>+\<^sup>+ C D)" by (simp add: rtranclpD)
  { assume "P \<turnstile> D \<preceq>\<^sup>* C"
    then have DpscC: "D = C \<or> (D \<noteq> C \<and> (subcls1 P)\<^sup>+\<^sup>+ D C)" by (simp add: rtranclpD)
    { assume "(subcls1 P)\<^sup>+\<^sup>+ D C"
      with wfP have CnscD: "\<not> (subcls1 P)\<^sup>+\<^sup>+ C D" by (rule subcls_asym)
      with CpscD have "C = D" by simp
    }
    with DpscC have "C = D" by blast
  }
  hence "Class C = Class D \<or> \<not> (P \<turnstile> D \<preceq>\<^sup>* C)" by blast
  thus "Class C = Class D \<or> \<not> P \<turnstile> Class D \<le> Class C" by simp
next
  fix C
  show "NT = Class C \<or> \<not> P \<turnstile> Class C \<le> NT" by simp
next
  fix A
  { assume "P \<turnstile> A\<lfloor>\<rceil> \<le> NT"
    hence "A\<lfloor>\<rceil> = NT" by fastforce
    hence "False" by simp }
  hence "\<not> (P \<turnstile> A\<lfloor>\<rceil> \<le> NT)" by blast
  thus "NT = A\<lfloor>\<rceil> \<or> \<not> P \<turnstile> A\<lfloor>\<rceil> \<le> NT" by simp
next
  fix A
  show "A\<lfloor>\<rceil> = Class Object \<or> \<not> P \<turnstile> Class Object \<le> A\<lfloor>\<rceil>"
    by(auto dest: Object_widen)
next
  fix A B
  assume AsU: "P \<turnstile> A \<le> B" and BnpscA: "A = B \<or> \<not> P \<turnstile> B \<le> A"
  { assume "P \<turnstile> B\<lfloor>\<rceil> \<le> A\<lfloor>\<rceil>"
    hence "P \<turnstile> B \<le> A" by (auto dest: Array_Array_widen)
    with BnpscA have "A = B" by blast
    hence "A\<lfloor>\<rceil> = B\<lfloor>\<rceil>" by simp }
  thus "A\<lfloor>\<rceil> = B\<lfloor>\<rceil> \<or> \<not> P \<turnstile> B\<lfloor>\<rceil> \<le> A\<lfloor>\<rceil>" by blast
qed

lemma widen_asym: "\<lbrakk> wf_prog wf_md P; P \<turnstile> C \<le> D; C \<noteq> D \<rbrakk> \<Longrightarrow> \<not> (P \<turnstile> D \<le> C)"
proof -
  assume wfP: "wf_prog wf_md P" and CsD: "P \<turnstile> C \<le> D" and CneqD: "C \<noteq> D"
  from wfP CsD have "C = D \<or> \<not> (P \<turnstile> D \<le> C)" by (rule widen_asym_1)
  with CneqD show ?thesis by simp
qed

lemma widen_antisym:
  "\<lbrakk> wf_prog m P; P \<turnstile> T \<le> U; P \<turnstile> U \<le> T \<rbrakk> \<Longrightarrow> T = U"
by(auto dest: widen_asym)

lemma widen_C_Object: "\<lbrakk> wf_prog wf_md P; is_class P C \<rbrakk> \<Longrightarrow> P \<turnstile> Class C \<le> Class Object"
by(simp add: subcls_C_Object)

lemma is_refType_widen_Object:
  assumes wfP: "wf_prog wfmc P"
  shows "\<lbrakk> is_type P A; is_refT A \<rbrakk> \<Longrightarrow> P \<turnstile> A \<le> Class Object"
by(induct A)(auto elim: refTE intro: subcls_C_Object[OF _ wfP] widen_array_object)

lemma is_lub_unique:
  assumes wf: "wf_prog wf_md P"
  shows "\<lbrakk> P \<turnstile> lub(U, V) = T; P \<turnstile> lub(U, V) = T' \<rbrakk> \<Longrightarrow> T = T'"
by(auto elim!: is_lub.cases intro: widen_antisym[OF wf])

subsection\<open>Well-formedness and method lookup\<close>

lemma sees_wf_mdecl:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<rbrakk> \<Longrightarrow> wf_mdecl wf_md P D (M,Ts,T,m)"
(*<*)
apply(drule visible_method_exists)
apply(clarify)
apply(drule class_wf, assumption)
apply(drule map_of_SomeD)
apply(auto simp add: wf_cdecl_def)
done
(*>*)


lemma sees_method_mono [rule_format (no_asm)]: 
  "\<lbrakk> P \<turnstile> C' \<preceq>\<^sup>* C; wf_prog wf_md P \<rbrakk> \<Longrightarrow>
  \<forall>D Ts T m. P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<longrightarrow>
     (\<exists>D' Ts' T' m'. P \<turnstile> C' sees M:Ts'\<rightarrow>T' = m' in D' \<and> P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T' \<le> T)"
apply( drule rtranclpD)
apply( erule disjE)
apply(  fastforce intro: widen_refl widens_refl)
apply( erule conjE)
apply( erule tranclp_trans_induct)
prefer 2
apply(  clarify)
apply(  drule spec, drule spec, drule spec, drule spec, erule (1) impE)
apply clarify
apply(  fast elim: widen_trans widens_trans)
apply( clarify)
apply( drule subcls1D)
apply( clarify)
apply(clarsimp simp:Method_def)
apply(frule (2) sees_methods_rec)
apply(rule refl)
apply(case_tac "map_of ms M")
apply(rule_tac x = D in exI)
apply(rule_tac x = Ts in exI)
apply(rule_tac x = T in exI)
apply(clarsimp simp add: widens_refl)
apply(rule_tac x = m in exI)
apply(fastforce simp add:map_add_def split:option.split)
apply clarsimp
apply(rename_tac Ts' T' m')
apply( drule (1) class_wf)
apply( unfold wf_cdecl_def Method_def)
apply( frule map_of_SomeD)
apply(clarsimp)
apply(drule (1) bspec)+
apply clarsimp
apply(erule_tac x=D in allE)
apply(erule_tac x=Ts in allE)
apply(rotate_tac -1)
apply(erule_tac x=T in allE)
apply(fastforce simp:map_add_def Method_def split:option.split)
done
(*>*)

lemma sees_method_mono2:
  "\<lbrakk> P \<turnstile> C' \<preceq>\<^sup>* C; wf_prog wf_md P;
     P \<turnstile> C sees M:Ts\<rightarrow>T = m in D; P \<turnstile> C' sees M:Ts'\<rightarrow>T' = m' in D' \<rbrakk>
  \<Longrightarrow> P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T' \<le> T"
(*<*)by(blast dest:sees_method_mono sees_method_fun)(*>*)


lemma mdecls_visible:
  assumes wf: "wf_prog wf_md P" and "class": "is_class P C"
  shows "\<And>D fs ms. class P C = Some(D,fs,ms)
         \<Longrightarrow> \<exists>Mm. P \<turnstile> C sees_methods Mm \<and> (\<forall>(M,Ts,T,m) \<in> set ms. Mm M = Some((Ts,T,m),C))"
using wf "class"
proof (induct rule:subcls1_induct)
  case Object
  with wf have "distinct_fst ms"
    by(auto dest: class_wf simp add: wf_cdecl_def)
  with Object show ?case by(fastforce intro!: sees_methods_Object map_of_SomeI)
next
  case Subcls
  with wf have "distinct_fst ms"
    by(auto dest: class_wf simp add: wf_cdecl_def)
  with Subcls show ?case
    by(fastforce elim:sees_methods_rec dest:subcls1D map_of_SomeI
                simp:is_class_def)
qed


lemma mdecl_visible:
  assumes wf: "wf_prog wf_md P" and C: "class P C = \<lfloor>(S,fs,ms)\<rfloor>" and  m: "(M,Ts,T,m) \<in> set ms"
  shows "P \<turnstile> C sees M:Ts\<rightarrow>T = m in C"
proof -
  from C have "is_class P C" by(auto simp:is_class_def)
  with assms show ?thesis
    by(bestsimp simp:Method_def dest:mdecls_visible)
qed

lemma sees_wf_native:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> C sees M:Ts\<rightarrow>T=Native in D \<rbrakk> \<Longrightarrow> D\<bullet>M(Ts) :: T"
apply(drule (1) sees_wf_mdecl)
apply(simp add: wf_mdecl_def)
done

lemma Call_lemma:
  "\<lbrakk> P \<turnstile> C sees M:Ts\<rightarrow>T = m in D; P \<turnstile> C' \<preceq>\<^sup>* C; wf_prog wf_md P \<rbrakk>
  \<Longrightarrow> \<exists>D' Ts' T' m'.
       P \<turnstile> C' sees M:Ts'\<rightarrow>T' = m' in D' \<and> P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T' \<le> T \<and> P \<turnstile> C' \<preceq>\<^sup>* D'
       \<and> is_type P T' \<and> (\<forall>T\<in>set Ts'. is_type P T) \<and> (m' \<noteq> Native \<longrightarrow> wf_md P D' (M,Ts',T',the m'))"
apply(frule (2) sees_method_mono)
apply(fastforce intro:sees_method_decl_above dest:sees_wf_mdecl
               simp: wf_mdecl_def)
done

lemma sub_Thread_sees_run:
  assumes wf: "wf_prog wf_md P"
  and PCThread: "P \<turnstile> C \<preceq>\<^sup>* Thread"
  shows "\<exists>D mthd. P \<turnstile> C sees run: []\<rightarrow>Void = \<lfloor>mthd\<rfloor> in D"
proof -
  from class_Thread[OF wf] obtain T' fsT MsT
    where classT: "class P Thread = \<lfloor>(T', fsT, MsT)\<rfloor>" by blast
  hence wfcThread: "wf_cdecl wf_md P (Thread, T', fsT, MsT)" using wf by(rule class_wf)
  then obtain mrunT where runThread: "(run, [], Void, mrunT) \<in> set MsT"
    by(auto simp add: wf_cdecl_def)
  moreover have "\<exists>MmT. P \<turnstile> Thread sees_methods MmT \<and>
                       (\<forall>(M,Ts,T,m) \<in> set MsT. MmT M = Some((Ts,T,m),Thread))"
    by(rule mdecls_visible[OF wf is_class_Thread[OF wf] classT])
  then obtain MmT where ThreadMmT: "P \<turnstile> Thread sees_methods MmT"
    and MmT: "\<forall>(M,Ts,T,m) \<in> set MsT. MmT M = Some((Ts,T,m),Thread)"
    by blast
  ultimately obtain mthd
    where "MmT run = \<lfloor>(([], Void, mthd), Thread)\<rfloor>"
    by(fastforce)
  with ThreadMmT have Tseesrun: "P \<turnstile> Thread sees run: []\<rightarrow>Void = mthd in Thread"
    by(auto simp add: Method_def)
  from sees_method_mono[OF PCThread wf Tseesrun]
  obtain D' m' where "P \<turnstile> C sees run: []\<rightarrow>Void = m' in D'" by auto
  moreover have "m' \<noteq> None"
  proof
    assume "m' = None"
    with wf \<open>P \<turnstile> C sees run: []\<rightarrow>Void = m' in D'\<close> have "D'\<bullet>run([]) :: Void"
      by(auto intro: sees_wf_native)
    thus False by cases auto
  qed
  ultimately show ?thesis by auto
qed

lemma wf_prog_lift:
  assumes wf: "wf_prog (\<lambda>P C bd. A P C bd) P"
  and rule:
  "\<And>wf_md C M Ts C T m.
   \<lbrakk> wf_prog wf_md P; P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>m\<rfloor> in C; is_class P C; set Ts \<subseteq> types P; A P C (M,Ts,T,m) \<rbrakk>
   \<Longrightarrow> B P C (M,Ts,T,m)"
  shows "wf_prog (\<lambda>P C bd. B P C bd) P"
proof(cases P)
  case (Program P')
  thus ?thesis using wf
    apply(clarsimp simp add: wf_prog_def wf_cdecl_def)
    apply(drule (1) bspec)
    apply(rename_tac C D fs ms)
    apply(subgoal_tac "is_class P C")
     prefer 2
     apply(simp add: is_class_def)
     apply(drule weak_map_of_SomeI)
     apply(simp add: Program)
    apply(clarsimp simp add: Program wf_mdecl_def split del: option.split)
    apply(drule (1) bspec)
    apply clarsimp
    apply(rule conjI)
     apply clarsimp
    apply clarsimp
    apply(frule (1) map_of_SomeI)
    apply(rule rule[OF wf, unfolded Program])
    apply(clarsimp simp add: is_class_def)
    apply(rule mdecl_visible[OF wf[unfolded Program]])
    apply(fastforce intro: is_type_pTs [OF wf, unfolded Program])+
    done
qed
    
subsection\<open>Well-formedness and field lookup\<close>

lemma wf_Fields_Ex:
  "\<lbrakk> wf_prog wf_md P; is_class P C \<rbrakk> \<Longrightarrow> \<exists>FDTs. P \<turnstile> C has_fields FDTs"
(*<*)
apply(frule class_Object)
apply(erule (1) subcls1_induct)
 apply(blast intro:has_fields_Object)
apply(blast intro:has_fields_rec dest:subcls1D)
done
(*>*)


lemma has_fields_types:
  "\<lbrakk> P \<turnstile> C has_fields FDTs; (FD, T, fm) \<in> set FDTs; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_type P T"
(*<*)
apply(induct rule:Fields.induct)
 apply(fastforce dest!: class_wf simp: wf_cdecl_def wf_fdecl_def)
apply(fastforce dest!: class_wf simp: wf_cdecl_def wf_fdecl_def)
done
(*>*)


lemma sees_field_is_type:
  "\<lbrakk> P \<turnstile> C sees F:T (fm) in D; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_type P T"
by(fastforce simp: sees_field_def
            elim: has_fields_types map_of_SomeD[OF map_of_remap_SomeD])

lemma wf_has_field_mono2:
  assumes wf: "wf_prog wf_md P"
  and has: "P \<turnstile> C has F:T (fm) in E"
  shows "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* D; P \<turnstile> D \<preceq>\<^sup>* E \<rbrakk> \<Longrightarrow> P \<turnstile> D has F:T (fm) in E"
proof(induct rule: rtranclp_induct)
  case base show ?case using has .
next
  case (step D D')
  note DsubD' = \<open>P \<turnstile> D \<prec>\<^sup>1 D'\<close>
  from DsubD' obtain rest where classD: "class P D = \<lfloor>(D', rest)\<rfloor>"
    and DObj: "D \<noteq> Object" by(auto elim!: subcls1.cases)
  from DsubD' \<open>P \<turnstile> D' \<preceq>\<^sup>* E\<close> have DsubE: "P \<turnstile> D \<preceq>\<^sup>* E" and DsubE2: "(subcls1 P)^++ D E"
    by(rule converse_rtranclp_into_rtranclp rtranclp_into_tranclp2)+
  from wf DsubE2 have DnE: "D \<noteq> E" by(rule subcls_irrefl)
  from DsubE have hasD: "P \<turnstile> D has F:T (fm) in E" by(rule \<open>P \<turnstile> D \<preceq>\<^sup>* E \<Longrightarrow> P \<turnstile> D has F:T (fm) in E\<close>)
  then obtain FDTs where hasf: "P \<turnstile> D has_fields FDTs" and FE: "map_of FDTs (F, E) = \<lfloor>(T, fm)\<rfloor>"
    unfolding has_field_def by blast
  from hasf show ?case
  proof cases
    case has_fields_Object with DObj show ?thesis by simp
  next
    case (has_fields_rec DD' fs ms FDTs')
    with classD have [simp]: "DD' = D'" "rest = (fs, ms)"
      and hasf': "P \<turnstile> D' has_fields FDTs'"
      and FDTs: "FDTs = map (\<lambda>(F, Tm). ((F, D), Tm)) fs @ FDTs'" by auto
    from FDTs FE DnE hasf' show ?thesis by(auto dest: map_of_SomeD simp add: has_field_def)
  qed
qed

lemma wf_has_field_idemp:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> C has F:T (fm) in D \<rbrakk> \<Longrightarrow> P \<turnstile> D has F:T (fm) in D"
apply(frule has_field_decl_above)
apply(erule (2) wf_has_field_mono2)
apply(rule rtranclp.rtrancl_refl)
done

lemma map_of_remap_conv:
  "\<lbrakk> distinct_fst fs; map_of (map (\<lambda>(F, y). ((F, D), y)) fs) (F, D) = \<lfloor>T\<rfloor> \<rbrakk>
  \<Longrightarrow> map_of (map (\<lambda>((F, D), T). (F, D, T)) (map (\<lambda>(F, y). ((F, D), y)) fs)) F = \<lfloor>(D, T)\<rfloor>"
apply(induct fs)
apply auto
done

lemma has_field_idemp_sees_field:
  assumes wf: "wf_prog wf_md P"
  and has: "P \<turnstile> D has F:T (fm) in D"
  shows "P \<turnstile> D sees F:T (fm) in D"
proof -
  from has obtain FDTs where hasf: "P \<turnstile> D has_fields FDTs"
    and FD: "map_of FDTs (F, D) = \<lfloor>(T, fm)\<rfloor>" unfolding has_field_def by blast
  from hasf have "map_of (map (\<lambda>((F, D), T). (F, D, T)) FDTs) F = \<lfloor>(D, T, fm)\<rfloor>"
  proof cases
    case (has_fields_Object D' fs ms)
    from \<open>class P Object = \<lfloor>(D', fs, ms)\<rfloor>\<close> wf
    have "wf_cdecl wf_md P (Object, D', fs, ms)" by(rule class_wf)
    hence "distinct_fst fs" by(simp add: wf_cdecl_def)
    with FD has_fields_Object show ?thesis by(auto intro: map_of_remap_conv simp del: map_map)
  next
    case (has_fields_rec D' fs ms FDTs')
    hence [simp]: "FDTs = map (\<lambda>(F, Tm). ((F, D), Tm)) fs @ FDTs'"
      and classD: "class P D = \<lfloor>(D', fs, ms)\<rfloor>" and DnObj: "D \<noteq> Object"
      and hasf': "P \<turnstile> D' has_fields FDTs'" by auto
    from \<open>class P D = \<lfloor>(D', fs, ms)\<rfloor>\<close> wf
    have "wf_cdecl wf_md P (D, D', fs, ms)" by(rule class_wf)
    hence "distinct_fst fs" by(simp add: wf_cdecl_def)
    moreover have "map_of FDTs' (F, D) = None"
    proof(rule ccontr)
      assume "map_of FDTs' (F, D) \<noteq> None"
      then obtain T' fm' where "map_of FDTs' (F, D) = \<lfloor>(T', fm')\<rfloor>" by(auto)
      with hasf' have "P \<turnstile> D' \<preceq>\<^sup>* D" by(auto dest!: map_of_SomeD intro: has_fields_decl_above)
      with classD DnObj have "(subcls1 P)^++ D D"
        by(auto intro: subcls1.intros rtranclp_into_tranclp2)
      with wf show False by(auto dest: subcls_irrefl)
    qed
    ultimately show ?thesis using FD hasf'
      by(auto simp add: map_add_Some_iff intro: map_of_remap_conv simp del: map_map)
  qed
  with hasf show ?thesis unfolding sees_field_def by blast
qed

lemma has_fields_distinct:
  assumes wf: "wf_prog wf_md P"
  and "P \<turnstile> C has_fields FDTs"
  shows "distinct (map fst FDTs)"
using \<open>P \<turnstile> C has_fields FDTs\<close>
proof(induct)
  case (has_fields_Object D fs ms FDTs)
  have eq: "map (fst \<circ> (\<lambda>(F, y). ((F, Object), y))) fs = map ((\<lambda>F. (F, Object)) \<circ> fst) fs" by(auto)
  from \<open>class P Object = \<lfloor>(D, fs, ms)\<rfloor>\<close> wf
  have "wf_cdecl wf_md P (Object, D, fs, ms)" by(rule class_wf)
  hence "distinct (map fst fs)" by(simp add: wf_cdecl_def distinct_fst_def)
  hence "distinct (map (fst \<circ> (\<lambda>(F, y). ((F, Object), y))) fs)" 
    unfolding eq distinct_map by(auto intro: comp_inj_on inj_onI)
  thus ?case using \<open>FDTs = map (\<lambda>(F, T). ((F, Object), T)) fs\<close> by(simp)
next
  case (has_fields_rec C D fs ms FDTs FDTs')
  have eq: "map (fst \<circ> (\<lambda>(F, y). ((F, C), y))) fs = map ((\<lambda>F. (F, C)) \<circ> fst) fs" by(auto)
  from \<open>class P C = \<lfloor>(D, fs, ms)\<rfloor>\<close> wf
  have "wf_cdecl wf_md P (C, D, fs, ms)" by(rule class_wf)
  hence "distinct (map fst fs)" by(simp add: wf_cdecl_def distinct_fst_def)
  hence "distinct (map (fst \<circ> (\<lambda>(F, y). ((F, C), y))) fs)"
    unfolding eq distinct_map by(auto intro: comp_inj_on inj_onI)
  moreover from \<open>class P C = \<lfloor>(D, fs, ms)\<rfloor>\<close> \<open>C \<noteq> Object\<close>
  have "P \<turnstile> C \<prec>\<^sup>1 D" by(rule subcls1.intros)
  with \<open>P \<turnstile> D has_fields FDTs\<close>
  have "(fst \<circ> (\<lambda>(F, y). ((F, C), y))) ` set fs \<inter> fst ` set FDTs = {}"
    by(auto dest: subcls_notin_has_fields)
  ultimately show ?case using \<open>FDTs' = map (\<lambda>(F, T). ((F, C), T)) fs @ FDTs\<close> \<open>distinct (map fst FDTs)\<close> by simp
qed


subsection \<open>Code generation\<close>

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  [inductify]
  wf_overriding 
.

text \<open>
  Separate subclass acycilicity from class declaration check.
  Otherwise, cyclic class hierarchies might lead to non-termination
  as @{term "Methods"} recurses over the class hierarchy.
\<close>

definition acyclic_class_hierarchy :: "'m prog \<Rightarrow> bool"
where
  "acyclic_class_hierarchy P \<longleftrightarrow> 
  (\<forall>(C, D, fs, ml) \<in> set (classes P). C \<noteq> Object \<longrightarrow> \<not> P \<turnstile> D \<preceq>\<^sup>* C)"

definition wf_cdecl' :: "'m wf_mdecl_test \<Rightarrow> 'm prog \<Rightarrow> 'm cdecl \<Rightarrow> bool"
where
  "wf_cdecl' wf_md P = (\<lambda>(C,(D,fs,ms)).
  (\<forall>f\<in>set fs. wf_fdecl P f) \<and> distinct_fst fs \<and>
  (\<forall>m\<in>set ms. wf_mdecl wf_md P C m) \<and>
  distinct_fst ms \<and>
  (C \<noteq> Object \<longrightarrow> is_class P D \<and> (\<forall>m\<in>set ms. wf_overriding P D m)) \<and>
  (C = Thread \<longrightarrow> (\<exists>m. (run, [], Void, m) \<in> set ms)))"

lemma acyclic_class_hierarchy_code [code]:
  "acyclic_class_hierarchy P \<longleftrightarrow> (\<forall>(C, D, fs, ml) \<in> set (classes P). C \<noteq> Object \<longrightarrow> \<not> subcls' P D C)"
by(simp add: acyclic_class_hierarchy_def subcls'_def)

lemma wf_cdecl'_code [code]:
  "wf_cdecl' wf_md P = (\<lambda>(C,(D,fs,ms)).
  (\<forall>f\<in>set fs. wf_fdecl P f) \<and>  distinct_fst fs \<and>
  (\<forall>m\<in>set ms. wf_mdecl wf_md P C m) \<and>
  distinct_fst ms \<and>
  (C \<noteq> Object \<longrightarrow> is_class P D \<and> (\<forall>m\<in>set ms. wf_overriding P D m)) \<and>
  (C = Thread \<longrightarrow> ((run, [], Void) \<in> set (map (\<lambda>(M, Ts, T, b). (M, Ts, T)) ms))))"
by(auto simp add: wf_cdecl'_def intro!: ext intro: rev_image_eqI)

declare set_append [symmetric, code_unfold]

lemma wf_prog_code [code]:
  "wf_prog wf_md P \<longleftrightarrow>
   acyclic_class_hierarchy P \<and>
   wf_syscls P \<and> distinct_fst (classes P) \<and>
   (\<forall>c \<in> set (classes P). wf_cdecl' wf_md P c)"
unfolding wf_prog_def wf_cdecl_def wf_cdecl'_def acyclic_class_hierarchy_def split_def
by blast

end
