(*  Title:      HOL/MicroJava/BV/Kildall.thy
    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM

Kildall's algorithm.
*)

section \<open>Kildall's Algorithm \label{sec:Kildall}\<close>

theory Kildall
imports SemilatAlg
begin



primrec propa :: "'s binop \<Rightarrow> (nat \<times> 's) list \<Rightarrow> 's list \<Rightarrow> nat set \<Rightarrow> 's list * nat set"
where
  "propa f []      \<tau>s w = (\<tau>s,w)"
| "propa f (q'#qs) \<tau>s w = (let (q,\<tau>) = q';
                             u = \<tau> \<squnion>\<^bsub>f\<^esub> \<tau>s!q;
                             w' = (if u = \<tau>s!q then w else insert q w)
                         in propa f qs (\<tau>s[q := u]) w')"

definition iter :: "'s binop \<Rightarrow> 's step_type \<Rightarrow>
          's list \<Rightarrow> nat set \<Rightarrow> 's list \<times> nat set"
where
  "iter f step \<tau>s w =
   while (\<lambda>(\<tau>s,w). w \<noteq> {})
         (\<lambda>(\<tau>s,w). let p = SOME p. p \<in> w
                   in propa f (step p (\<tau>s!p)) \<tau>s (w-{p}))
         (\<tau>s,w)"

definition unstables :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> nat set"
where
  "unstables r step \<tau>s = {p. p < size \<tau>s \<and> \<not>stable r step \<tau>s p}"

definition kildall :: "'s ord \<Rightarrow> 's binop \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> 's list"
where
  "kildall r f step \<tau>s = fst(iter f step \<tau>s (unstables r step \<tau>s))"

primrec merges :: "'s binop \<Rightarrow> (nat \<times> 's) list \<Rightarrow> 's list \<Rightarrow> 's list"
where
  "merges f []      \<tau>s = \<tau>s"
| "merges f (p'#ps) \<tau>s = (let (p,\<tau>) = p' in merges f ps (\<tau>s[p := \<tau> \<squnion>\<^bsub>f\<^esub> \<tau>s!p]))"


lemmas [simp] = Let_def Semilat.le_iff_plus_unchanged [OF Semilat.intro, symmetric]


lemma (in Semilat) nth_merges:
 "\<And>ss. \<lbrakk>p < length ss; ss \<in> list n A; \<forall>(p,t)\<in>set ps. p<n \<and> t\<in>A \<rbrakk> \<Longrightarrow>
  (merges f ps ss)!p = map snd [(p',t') \<leftarrow> ps. p'=p] \<Squnion>\<^bsub>f\<^esub> ss!p"
  (is "\<And>ss. \<lbrakk>_; _; ?steptype ps\<rbrakk> \<Longrightarrow> ?P ss ps")
(*<*)
proof (induct ps)
  show "\<And>ss. ?P ss []" by simp

  fix ss p' ps'
  assume ss: "ss \<in> list n A"
  assume l:  "p < length ss"
  assume "?steptype (p'#ps')"
  then obtain a b where
    p': "p'=(a,b)" and ab: "a<n" "b\<in>A" and ps': "?steptype ps'"
    by (cases p') auto
  assume "\<And>ss. p< length ss \<Longrightarrow> ss \<in> list n A \<Longrightarrow> ?steptype ps' \<Longrightarrow> ?P ss ps'"
  hence IH: "\<And>ss. ss \<in> list n A \<Longrightarrow> p < length ss \<Longrightarrow> ?P ss ps'" using ps' by iprover

  from ss ab
  have "ss[a := b \<squnion>\<^bsub>f\<^esub> ss!a] \<in> list n A" by (simp add: closedD)
  moreover
  with l have "p < length (ss[a := b \<squnion>\<^bsub>f\<^esub> ss!a])" by simp
  ultimately
  have "?P (ss[a := b \<squnion>\<^bsub>f\<^esub> ss!a]) ps'" by (rule IH)
  with p' l
  show "?P ss (p'#ps')" by simp
qed
(*>*)


(** merges **)

lemma length_merges [simp]:
  "\<And>ss. size(merges f ps ss) = size ss"
(*<*) by (induct ps, auto) (*>*)

lemma (in Semilat) merges_preserves_type_lemma:
shows "\<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>(p,x) \<in> set ps. p<n \<and> x\<in>A)
         \<longrightarrow> merges f ps xs \<in> list n A"
(*<*)
apply (insert closedI)
apply (unfold closed_def)
apply (induct ps)
 apply simp
apply clarsimp
done
(*>*)

lemma (in Semilat) merges_preserves_type [simp]:
 "\<lbrakk> xs \<in> list n A; \<forall>(p,x) \<in> set ps. p<n \<and> x\<in>A \<rbrakk>
  \<Longrightarrow> merges f ps xs \<in> list n A"
by (simp add: merges_preserves_type_lemma)

lemma (in Semilat) merges_incr_lemma:
 "\<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>(p,x)\<in>set ps. p<size xs \<and> x \<in> A) \<longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] merges f ps xs"
(*<*)
apply (induct ps)
 apply simp
apply simp
apply clarify
apply (rule order_trans)
  apply simp
 apply (erule list_update_incr)
  apply simp
 apply simp
apply (blast intro!: listE_set intro: closedD listE_length [THEN nth_in])
done
(*>*)

lemma (in Semilat) merges_incr:
 "\<lbrakk> xs \<in> list n A; \<forall>(p,x)\<in>set ps. p<size xs \<and> x \<in> A \<rbrakk> 
  \<Longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] merges f ps xs"
  by (simp add: merges_incr_lemma)


lemma (in Semilat) merges_same_conv [rule_format]:
 "(\<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>(p,x)\<in>set ps. p<size xs \<and> x\<in>A) \<longrightarrow> 
     (merges f ps xs = xs) = (\<forall>(p,x)\<in>set ps. x \<sqsubseteq>\<^bsub>r\<^esub> xs!p))"
(*<*)
  apply (induct_tac ps)
   apply simp
  apply clarsimp
  apply (rename_tac p x ps xs)
  apply (rule iffI)
   apply (rule context_conjI)
    apply (subgoal_tac "xs[p := x \<squnion>\<^bsub>f\<^esub> xs!p] [\<sqsubseteq>\<^bsub>r\<^esub>] xs")
     apply (force dest!: le_listD simp add: nth_list_update)
    apply (erule subst, rule merges_incr)
       apply (blast intro!: listE_set intro: closedD listE_length [THEN nth_in])
      apply clarify
      apply (rule conjI)
       apply simp
       apply (blast dest: boundedD)
      apply blast
   apply clarify
   apply (erule allE)
   apply (erule impE)
    apply assumption
   apply (drule bspec)
    apply assumption
   apply (simp add: le_iff_plus_unchanged [THEN iffD1] list_update_same_conv [THEN iffD2])
   apply blast
  apply clarify 
  apply (simp add: le_iff_plus_unchanged [THEN iffD1] list_update_same_conv [THEN iffD2])
  done
(*>*)


lemma (in Semilat) list_update_le_listI [rule_format]:
  "set xs \<subseteq> A \<longrightarrow> set ys \<subseteq> A \<longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<longrightarrow> p < size xs \<longrightarrow>  
   x \<sqsubseteq>\<^bsub>r\<^esub> ys!p \<longrightarrow> x\<in>A \<longrightarrow> xs[p := x \<squnion>\<^bsub>f\<^esub> xs!p] [\<sqsubseteq>\<^bsub>r\<^esub>] ys"
(*<*)
  apply (insert semilat)
  apply (simp only: Listn.le_def lesub_def semilat_def)
  apply (simp add: list_all2_conv_all_nth nth_list_update)
  done
(*>*)

lemma (in Semilat) merges_pres_le_ub:
  assumes "set ts \<subseteq> A"  "set ss \<subseteq> A"
    "\<forall>(p,t)\<in>set ps. t \<sqsubseteq>\<^bsub>r\<^esub> ts!p \<and> t \<in> A \<and> p < size ts"  "ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts"
  shows "merges f ps ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts"
(*<*)
proof -
  { fix t ts ps
    have
    "\<And>qs. \<lbrakk>set ts \<subseteq> A; \<forall>(p,t)\<in>set ps. t \<sqsubseteq>\<^bsub>r\<^esub> ts!p \<and> t \<in> A \<and> p< size ts \<rbrakk> \<Longrightarrow>
    set qs \<subseteq> set ps  \<longrightarrow> 
    (\<forall>ss. set ss \<subseteq> A \<longrightarrow> ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts \<longrightarrow> merges f qs ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts)"
    apply (induct_tac qs)
     apply simp
    apply (simp (no_asm_simp))
    apply clarify
    apply simp
    apply (erule allE, erule impE, erule_tac [2] mp)
     apply (drule bspec, assumption)
     apply (simp add: closedD)
    apply (drule bspec, assumption)
    apply (simp add: list_update_le_listI)
    done 
  } note this [dest]  
  from assms show ?thesis by blast
qed
(*>*)


(** propa **)

lemma decomp_propa:
  "\<And>ss w. (\<forall>(q,t)\<in>set qs. q < size ss) \<Longrightarrow> 
   propa f qs ss w = 
   (merges f qs ss, {q. \<exists>t.(q,t)\<in>set qs \<and> t \<squnion>\<^bsub>f\<^esub> ss!q \<noteq> ss!q} \<union> w)"
(*<*)
  apply (induct qs)
   apply simp   
  apply (simp (no_asm))
  apply clarify  
  apply simp
  apply (rule conjI) 
   apply blast
  apply (simp add: nth_list_update)
  apply blast
  done 
(*>*)

(** iter **)

lemma (in Semilat) stable_pres_lemma:
shows "\<lbrakk>pres_type step n A; bounded step n; 
     ss \<in> list n A; p \<in> w; \<forall>q\<in>w. q < n; 
     \<forall>q. q < n \<longrightarrow> q \<notin> w \<longrightarrow> stable r step ss q; q < n; 
     \<forall>s'. (q,s') \<in> set (step p (ss!p)) \<longrightarrow> s' \<squnion>\<^bsub>f\<^esub> ss!q = ss!q; 
     q \<notin> w \<or> q = p \<rbrakk> 
  \<Longrightarrow> stable r step (merges f (step p (ss!p)) ss) q"
(*<*)
  apply (unfold stable_def)
  apply (subgoal_tac "\<forall>s'. (q,s') \<in> set (step p (ss!p)) \<longrightarrow> s' : A")
   prefer 2
   apply clarify
   apply (erule pres_typeD)
    prefer 3 apply assumption
    apply (rule listE_nth_in)
     apply assumption
    apply simp
   apply simp
  apply simp
  apply clarify
  apply (subst nth_merges)
       apply simp
       apply (blast dest: boundedD)
      apply assumption
     apply clarify
     apply (rule conjI)
      apply (blast dest: boundedD)
     apply (erule pres_typeD)
       prefer 3 apply assumption
      apply simp
     apply simp
apply(subgoal_tac "q < length ss")
prefer 2 apply simp
  apply (frule nth_merges [of q _ _ "step p (ss!p)"]) (* fixme: why does method subst not work?? *)
apply assumption
  apply clarify
  apply (rule conjI)
   apply (blast dest: boundedD)
  apply (erule pres_typeD)
     prefer 3 apply assumption
    apply simp
   apply simp
  apply (drule_tac P = "\<lambda>x. (a, b) \<in> set (step q x)" in subst)
   apply assumption

 apply (simp add: plusplus_empty)
 apply (cases "q \<in> w")
  apply simp
  apply (rule ub1')
     apply (rule Semilat.intro)
     apply (rule semilat)
    apply clarify
    apply (rule pres_typeD)
       apply assumption
      prefer 3 apply assumption
     apply (blast intro: listE_nth_in dest: boundedD)
    apply (blast intro: pres_typeD dest: boundedD)
   apply (blast intro: listE_nth_in dest: boundedD)
  apply assumption

 apply simp
 apply (erule allE, erule impE, assumption, erule impE, assumption)
 apply (rule order_trans)
   apply simp
  defer
 apply (rule pp_ub2)(*
    apply assumption*)
   apply simp
   apply clarify
   apply simp
   apply (rule pres_typeD)
      apply assumption
     prefer 3 apply assumption
    apply (blast intro: listE_nth_in dest: boundedD)
   apply (blast intro: pres_typeD dest: boundedD)
  apply (blast intro: listE_nth_in dest: boundedD)
 apply blast
 done
(*>*)


lemma (in Semilat) merges_bounded_lemma:
 "\<lbrakk> mono r step n A; bounded step n; 
    \<forall>(p',s') \<in> set (step p (ss!p)). s' \<in> A; ss \<in> list n A; ts \<in> list n A; p < n; 
    ss [\<sqsubseteq>\<^sub>r] ts; \<forall>p. p < n \<longrightarrow> stable r step ts p \<rbrakk> 
  \<Longrightarrow> merges f (step p (ss!p)) ss [\<sqsubseteq>\<^sub>r] ts" 
(*<*)
  apply (unfold stable_def)
  apply (rule merges_pres_le_ub)
     apply simp
    apply simp
   prefer 2 apply assumption

  apply clarsimp
  apply (drule boundedD, assumption+)
  apply (erule allE, erule impE, assumption)
  apply (drule bspec, assumption)
  apply simp

  apply (drule monoD [of _ _ _ _ p "ss!p"  "ts!p"])
     apply assumption
    apply simp
   apply (simp add: le_listD)
  
  apply (drule lesub_step_typeD, assumption) 
  apply clarify
  apply (drule bspec, assumption)
  apply simp
  apply (blast intro: order_trans)
  done
(*>*)

lemma termination_lemma: assumes "Semilat A r f"
shows "\<lbrakk> ss \<in> list n A; \<forall>(q,t)\<in>set qs. q<n \<and> t\<in>A; p\<in>w \<rbrakk> \<Longrightarrow> 
      ss [\<sqsubset>\<^sub>r] merges f qs ss \<or> 
  merges f qs ss = ss \<and> {q. \<exists>t. (q,t)\<in>set qs \<and> t \<squnion>\<^bsub>f\<^esub> ss!q \<noteq> ss!q} \<union> (w-{p}) \<subset> w"
(*<*) (is "PROP ?P")
proof -
  interpret Semilat A r f by fact
  show "PROP ?P"
  apply(insert semilat)
    apply (unfold lesssub_def)
    apply (simp (no_asm_simp) add: merges_incr)
    apply (rule impI)
    apply (rule merges_same_conv [THEN iffD1, elim_format]) 
    apply assumption+
      defer
      apply (rule sym, assumption)
     defer apply simp
     apply (subgoal_tac "\<forall>q t. \<not>((q, t) \<in> set qs \<and> t \<squnion>\<^bsub>f\<^esub> ss ! q \<noteq> ss ! q)")
     apply (blast intro!: psubsetI elim: equalityE)
     apply clarsimp
     apply (drule bspec, assumption) 
     apply (drule bspec, assumption)
     apply clarsimp
    done 
qed
(*>*)

lemma iter_properties[rule_format]: assumes "Semilat A r f"
shows "\<lbrakk> acc r; pres_type step n A; mono r step n A;
     bounded step n; \<forall>p\<in>w0. p < n; ss0 \<in> list n A;
     \<forall>p<n. p \<notin> w0 \<longrightarrow> stable r step ss0 p \<rbrakk> \<Longrightarrow>
   iter f step ss0 w0 = (ss',w')
   \<longrightarrow>
   ss' \<in> list n A \<and> stables r step ss' \<and> ss0 [\<sqsubseteq>\<^sub>r] ss' \<and>
   (\<forall>ts\<in>list n A. ss0 [\<sqsubseteq>\<^sub>r] ts \<and> stables r step ts \<longrightarrow> ss' [\<sqsubseteq>\<^sub>r] ts)"
(*<*) (is "PROP ?P")
proof -
  interpret Semilat A r f by fact
  show "PROP ?P"
  apply(insert semilat)
  apply (unfold iter_def stables_def)
  apply (rule_tac P = "\<lambda>(ss,w).
   ss \<in> list n A \<and> (\<forall>p<n. p \<notin> w \<longrightarrow> stable r step ss p) \<and> ss0 [\<sqsubseteq>\<^sub>r] ss \<and>
   (\<forall>ts\<in>list n A. ss0 [\<sqsubseteq>\<^sub>r] ts \<and> stables r step ts \<longrightarrow> ss [\<sqsubseteq>\<^sub>r] ts) \<and>
   (\<forall>p\<in>w. p < n)" and
   r = "{(ss',ss) . ss [\<sqsubset>\<^sub>r] ss'} <*lex*> finite_psubset"
         in while_rule)

  \<comment> \<open>Invariant holds initially:\<close>
  apply (simp add:stables_def)

  \<comment> \<open>Invariant is preserved:\<close>
  apply(simp add: stables_def split_paired_all)
  apply(rename_tac ss w)
  apply(subgoal_tac "(SOME p. p \<in> w) \<in> w")
   prefer 2 apply (fast intro: someI)
  apply(subgoal_tac "\<forall>(q,t) \<in> set (step (SOME p. p \<in> w) (ss ! (SOME p. p \<in> w))). q < length ss \<and> t \<in> A")
   prefer 2
   apply clarify
   apply (rule conjI)
    apply(clarsimp, blast dest!: boundedD)
   apply (erule pres_typeD)
    prefer 3
    apply assumption
    apply (erule listE_nth_in)
    apply blast
   apply blast
  apply (subst decomp_propa)
   apply blast
  apply simp
  apply (rule conjI)
   apply (rule merges_preserves_type)
   apply blast
   apply clarify
   apply (rule conjI)
    apply(clarsimp, blast dest!: boundedD)
   apply (erule pres_typeD)
    prefer 3
    apply assumption
    apply (erule listE_nth_in)
    apply blast
   apply blast
  apply (rule conjI)
   apply clarify
   apply (blast intro!: stable_pres_lemma)
  apply (rule conjI)
   apply (blast intro!: merges_incr intro: le_list_trans)
  apply (rule conjI)
   apply clarsimp
   apply (blast intro!: merges_bounded_lemma)
  apply (blast dest!: boundedD)


  \<comment> \<open>Postcondition holds upon termination:\<close>
  apply(clarsimp simp add: stables_def split_paired_all)

  \<comment> \<open>Well-foundedness of the termination relation:\<close>
  apply (rule wf_lex_prod)
   apply (insert orderI [THEN acc_le_listI])
   apply (simp only: acc_def lesssub_def)
  apply (rule wf_finite_psubset) 

  \<comment> \<open>Loop decreases along termination relation:\<close>
  apply(simp add: stables_def split_paired_all)
  apply(rename_tac ss w)
  apply(subgoal_tac "(SOME p. p \<in> w) \<in> w")
   prefer 2 apply (fast intro: someI)
  apply(subgoal_tac "\<forall>(q,t) \<in> set (step (SOME p. p \<in> w) (ss ! (SOME p. p \<in> w))). q < length ss \<and> t \<in> A")
   prefer 2
   apply clarify
   apply (rule conjI)
    apply(clarsimp, blast dest!: boundedD)
   apply (erule pres_typeD)
    prefer 3
    apply assumption
    apply (erule listE_nth_in)
    apply blast
   apply blast
  apply (subst decomp_propa)
   apply blast
  apply clarify
  apply (simp del: listE_length
      add: lex_prod_def finite_psubset_def 
           bounded_nat_set_is_finite)
  apply (rule termination_lemma)
  apply (rule assms)
  apply assumption+
  defer
  apply assumption
  apply clarsimp
  done
qed
(*>*)


lemma kildall_properties: assumes "Semilat A r f"
shows "\<lbrakk> acc r; pres_type step n A; mono r step n A;
     bounded step n; ss0 \<in> list n A \<rbrakk> \<Longrightarrow>
  kildall r f step ss0 \<in> list n A \<and>
  stables r step (kildall r f step ss0) \<and>
  ss0 [\<sqsubseteq>\<^sub>r] kildall r f step ss0 \<and>
  (\<forall>ts\<in>list n A. ss0 [\<sqsubseteq>\<^sub>r] ts \<and> stables r step ts \<longrightarrow>
                 kildall r f step ss0 [\<sqsubseteq>\<^sub>r] ts)"
(*<*) (is "PROP ?P")
proof -
  interpret Semilat A r f by fact
  show "PROP ?P"
  apply (unfold kildall_def)
  apply(case_tac "iter f step ss0 (unstables r step ss0)")
  apply(simp)
  apply (rule iter_properties)
  apply (simp_all add: unstables_def stable_def)
  apply (rule Semilat.intro)
  apply (rule semilat)
  done
qed


lemma is_bcv_kildall: assumes "Semilat A r f"
shows "\<lbrakk> acc r; top r T; pres_type step n A; bounded step n; mono r step n A \<rbrakk>
  \<Longrightarrow> is_bcv r T step n A (kildall r f step)" (is "PROP ?P")
proof -
  interpret Semilat A r f by fact
  show "PROP ?P"
  apply(unfold is_bcv_def wt_step_def)
  apply(insert \<open>Semilat A r f\<close> semilat kildall_properties[of A])
  apply(simp add:stables_def)
  apply clarify
  apply(subgoal_tac "kildall r f step \<tau>s\<^sub>0 \<in> list n A")
   prefer 2 apply (simp(no_asm_simp))
  apply (rule iffI)
   apply (rule_tac x = "kildall r f step \<tau>s\<^sub>0" in bexI) 
    apply (rule conjI)
     apply (blast)
    apply (simp  (no_asm_simp))
   apply(assumption)
  apply clarify
  apply(subgoal_tac "kildall r f step \<tau>s\<^sub>0!p <=_r \<tau>s!p")
   apply simp
  apply (blast intro!: le_listD less_lengthI)
  done
qed
(*>*)

end
