(*  Title:       CoreC++
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

   Based on extracts from the Jinja theories:
      Common/Objects.thy by David von Oheimb
      Common/Conform.thy by David von Oheimb and Tobias Nipkow
      Common/Exceptions.thy by Gerwin Klein and Martin Strecker
      J/BigStep.thy by Tobias Nipkow
      J/SmallStep.thy by Tobias Nipkow
      J/WellTypeRT.thy by Tobias Nipkow 
*)

section \<open>Heap Extension\<close>

theory HeapExtension
imports Progress
begin

subsection \<open>The Heap Extension\<close>

definition hext :: "heap \<Rightarrow> heap \<Rightarrow> bool" ("_ \<unlhd> _" [51,51] 50) where
  "h \<unlhd> h'  \<equiv>  \<forall>a C S. h a = Some(C,S) \<longrightarrow> (\<exists>S'. h' a = Some(C,S'))"

lemma hextI: "\<forall>a C S. h a = Some(C,S) \<longrightarrow> (\<exists>S'. h' a = Some(C,S')) \<Longrightarrow> h \<unlhd> h'"

apply (unfold hext_def)
apply auto
done


lemma hext_objD: "\<lbrakk> h \<unlhd> h'; h a = Some(C,S) \<rbrakk> \<Longrightarrow> \<exists>S'. h' a = Some(C,S')"

apply (unfold hext_def)
apply (force)
done


lemma hext_refl [iff]: "h \<unlhd> h"

apply (rule hextI)
apply (fast)
done


lemma hext_new [simp]: "h a = None \<Longrightarrow> h \<unlhd> h(a\<mapsto>x)"

apply (rule hextI)
apply (auto simp:fun_upd_apply)
done


lemma hext_trans: "\<lbrakk> h \<unlhd> h'; h' \<unlhd> h'' \<rbrakk> \<Longrightarrow> h \<unlhd> h''"

apply (rule hextI)
apply (fast dest: hext_objD)
done


lemma hext_upd_obj: "h a = Some (C,S) \<Longrightarrow> h \<unlhd> h(a\<mapsto>(C,S'))"

apply (rule hextI)
apply (auto simp:fun_upd_apply)
done



subsection \<open>\<open>\<unlhd>\<close> and preallocated\<close>

lemma preallocated_hext:
  "\<lbrakk> preallocated h; h \<unlhd> h' \<rbrakk> \<Longrightarrow> preallocated h'"
by (simp add: preallocated_def hext_def)


lemmas preallocated_upd_obj = preallocated_hext [OF _ hext_upd_obj]
lemmas preallocated_new  = preallocated_hext [OF _ hext_new]



subsection \<open>\<open>\<unlhd>\<close> in Small- and BigStep\<close>

lemma red_hext_incr: "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>  \<Longrightarrow> h \<unlhd> h'"
  and reds_hext_incr: "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle>  \<Longrightarrow> h \<unlhd> h'"

proof(induct rule:red_reds_inducts)
  case RedNew thus ?case
    by(fastforce dest:new_Addr_SomeD simp:hext_def split:if_splits)
next
  case RedFAss thus ?case by(simp add:hext_def split:if_splits)
qed simp_all


lemma step_hext_incr: "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>  \<Longrightarrow> hp s \<unlhd> hp s'"

proof(induct rule:converse_rtrancl_induct2)
  case refl thus ?case by(rule hext_refl)
next
  case (step e s e'' s'')
  have Red:"((e, s), e'', s'') \<in> Red P E"
    and hext:"hp s'' \<unlhd> hp s'" by fact+
  from Red have "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e'',s''\<rangle>" by simp
  hence "hp s \<unlhd> hp s''"
    by(cases s,cases s'')(auto dest:red_hext_incr)
  with hext show ?case by-(rule hext_trans)
qed


lemma steps_hext_incr: "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle>  \<Longrightarrow> hp s \<unlhd> hp s'"

proof(induct rule:converse_rtrancl_induct2)
  case refl thus ?case by(rule hext_refl)
next
  case (step es s es'' s'')
  have Reds:"((es, s), es'', s'') \<in> Reds P E"
    and hext:"hp s'' \<unlhd> hp s'" by fact+
  from Reds have "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es'',s''\<rangle>" by simp
  hence "hp s \<unlhd> hp s''"
    by(cases s,cases s'',auto dest:reds_hext_incr)
  with hext show ?case by-(rule hext_trans)
qed



lemma eval_hext: "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> h \<unlhd> h'"
and evals_hext:  "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<Rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> h \<unlhd> h'"

proof (induct rule:eval_evals_inducts)
  case New thus ?case
    by(fastforce intro!: hext_new intro:someI simp:new_Addr_def
                split:if_split_asm simp del:fun_upd_apply)
next
  case FAss thus ?case
    by(auto simp:sym[THEN hext_upd_obj] simp del:fun_upd_apply
            elim!: hext_trans)
qed (auto elim!: hext_trans)



subsection \<open>\<open>\<unlhd>\<close> and conformance\<close>

lemma conf_hext: "h \<unlhd> h' \<Longrightarrow> P,h \<turnstile> v :\<le> T \<Longrightarrow> P,h' \<turnstile> v :\<le> T"
by(cases T)(induct v,auto dest: hext_objD split:if_split_asm)+

lemma confs_hext: "P,h \<turnstile> vs [:\<le>] Ts \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,h' \<turnstile> vs [:\<le>] Ts"
by (erule list_all2_mono, erule conf_hext, assumption)

lemma fconf_hext: "\<lbrakk> P,h \<turnstile> fs (:\<le>) E; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> fs (:\<le>) E"

apply (unfold fconf_def)
apply  (fast elim: conf_hext)
done



lemmas fconf_upd_obj = fconf_hext [OF _ hext_upd_obj]
lemmas fconf_new = fconf_hext [OF _ hext_new]



lemma oconf_hext: "P,h \<turnstile> obj \<surd> \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,h' \<turnstile> obj \<surd>"

apply (auto simp:oconf_def)
apply (erule allE)
apply (erule_tac x="Cs" in allE)
apply (erule_tac x="fs'" in allE)
apply (fastforce elim:fconf_hext)
done


lemmas oconf_new = oconf_hext [OF _ hext_new]
lemmas oconf_upd_obj = oconf_hext [OF _ hext_upd_obj]


lemma hconf_new: "\<lbrakk> P \<turnstile> h \<surd>; h a = None; P,h \<turnstile> obj \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h(a\<mapsto>obj) \<surd>"
by (unfold hconf_def) (auto intro: oconf_new preallocated_new)

lemma "\<lbrakk>P \<turnstile> h \<surd>; h' = h(a \<mapsto> (C, Collect (init_obj P C))); h a = None; wf_prog wf_md P\<rbrakk>
  \<Longrightarrow> P \<turnstile> h' \<surd>"
apply (simp add:hconf_def oconf_def)
apply auto
     apply (rule_tac x="init_class_fieldmap P (last Cs)" in exI)
     apply (rule init_obj.intros)
     apply assumption
    apply (erule init_obj.cases)
    apply clarsimp
    apply (erule init_obj.cases)
    apply clarsimp
   apply (erule_tac x="a" in allE)
   apply clarsimp
   apply (erule init_obj.cases)
   apply simp
  apply (erule_tac x="a" in allE)
  apply clarsimp
  apply (erule init_obj.cases)
  apply clarsimp
  apply (drule Subobj_last_isClass)
   apply simp
  apply (auto simp:is_class_def)
  apply (rule fconf_init_fields)
  apply auto
 apply (erule_tac x="aa" in allE)
 apply (erule_tac x="aaa" in allE)
 apply (erule_tac x="b" in allE)
 apply clarsimp
 apply (rotate_tac -1)
 apply (erule_tac x="Cs" in allE)
 apply (erule_tac x="fs'" in allE)
 apply clarsimp thm fconf_new
 apply (erule fconf_new)
 apply simp
apply (rule preallocated_new)
apply simp_all
done



lemma hconf_upd_obj: 
"\<lbrakk> P \<turnstile> h\<surd>; h a = Some(C,S); P,h \<turnstile> (C,S')\<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h(a\<mapsto>(C,S'))\<surd>"
by (unfold hconf_def) (auto intro: oconf_upd_obj preallocated_upd_obj)

lemma lconf_hext: "\<lbrakk> P,h \<turnstile> l (:\<le>)\<^sub>w E; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l (:\<le>)\<^sub>w E"

apply (unfold lconf_def)
apply  (fast elim: conf_hext)
done



subsection \<open>\<open>\<unlhd>\<close> in the runtime type system\<close>

lemma hext_typeof_mono: "\<lbrakk> h \<unlhd> h'; P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T \<rbrakk> \<Longrightarrow> P \<turnstile> typeof\<^bsub>h'\<^esub> v = Some T"

apply(cases v)
    apply simp
   apply simp
  apply simp
 apply simp
apply(fastforce simp:hext_def)
done



lemma WTrt_hext_mono: "P,E,h \<turnstile> e : T \<Longrightarrow> (\<And>h'. h \<unlhd> h' \<Longrightarrow> P,E,h' \<turnstile> e : T)"
and WTrts_hext_mono: "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> (\<And>h'. h \<unlhd> h' \<Longrightarrow> P,E,h' \<turnstile> es [:] Ts)"

apply(induct rule: WTrt_inducts)
apply(simp add: WTrtNew)
apply(fastforce intro: WTrtDynCast)
apply(fastforce intro: WTrtStaticCast)
apply(fastforce simp: WTrtVal dest:hext_typeof_mono)
apply(simp add: WTrtVar)
apply(fastforce simp add: WTrtBinOp)
apply(fastforce simp add: WTrtLAss)
apply(fastforce simp: WTrtFAcc del:WTrt_WTrts.intros WTrt_elim_cases)
apply(simp add: WTrtFAccNT)
apply(fastforce simp: WTrtFAss del:WTrt_WTrts.intros WTrt_elim_cases)
apply(fastforce simp: WTrtFAssNT del:WTrt_WTrts.intros WTrt_elim_cases)
apply(fastforce simp: WTrtCall del:WTrt_WTrts.intros WTrt_elim_cases)
apply(fastforce simp: WTrtStaticCall del:WTrt_WTrts.intros WTrt_elim_cases)
apply(fastforce simp: WTrtCallNT del:WTrt_WTrts.intros WTrt_elim_cases)
apply(fastforce)
apply(fastforce simp add: WTrtSeq)
apply(fastforce simp add: WTrtCond)
apply(fastforce simp add: WTrtWhile)
apply(fastforce simp add: WTrtThrow)
apply(simp add: WTrtNil)
apply(simp add: WTrtCons)
done




end
