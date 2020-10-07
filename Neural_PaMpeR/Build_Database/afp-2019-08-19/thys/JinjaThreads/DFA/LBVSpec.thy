(*  Title:      HOL/MicroJava/BV/LBVSpec.thy
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

section \<open>The Lightweight Bytecode Verifier\<close>

theory LBVSpec
imports SemilatAlg Opt
begin

type_synonym
  's certificate = "'s list"   

primrec merge :: "'s certificate \<Rightarrow> 's binop \<Rightarrow> 's ord \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> (nat \<times> 's) list \<Rightarrow> 's \<Rightarrow> 's"
where
  "merge cert f r T pc []     x = x"
| "merge cert f r T pc (s#ss) x = merge cert f r T pc ss (let (pc',s') = s in 
                                  if pc'=pc+1 then s' \<squnion>\<^sub>f x
                                  else if s' \<sqsubseteq>\<^sub>r cert!pc' then x
                                  else T)"

definition wtl_inst :: "'s certificate \<Rightarrow> 's binop \<Rightarrow> 's ord \<Rightarrow> 's \<Rightarrow>
              's step_type \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> 's"
where
  "wtl_inst cert f r T step pc s = merge cert f r T pc (step pc s) (cert!(pc+1))"

definition wtl_cert :: "'s certificate \<Rightarrow> 's binop \<Rightarrow> 's ord \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow>
              's step_type \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> 's"
where
  "wtl_cert cert f r T B step pc s =
  (if cert!pc = B then 
    wtl_inst cert f r T step pc s
  else
    if s \<sqsubseteq>\<^sub>r cert!pc then wtl_inst cert f r T step pc (cert!pc) else T)"

primrec wtl_inst_list :: "'a list \<Rightarrow> 's certificate \<Rightarrow> 's binop \<Rightarrow> 's ord \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow>
                    's step_type \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> 's"
where
  "wtl_inst_list []     cert f r T B step pc s = s"
| "wtl_inst_list (i#is) cert f r T B step pc s = 
    (let s' = wtl_cert cert f r T B step pc s in
      if s' = T \<or> s = T then T else wtl_inst_list is cert f r T B step (pc+1) s')"

definition cert_ok :: "'s certificate \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool"
where
  "cert_ok cert n T B A \<longleftrightarrow> (\<forall>i < n. cert!i \<in> A \<and> cert!i \<noteq> T) \<and> (cert!n = B)"

definition bottom :: "'a ord \<Rightarrow> 'a \<Rightarrow> bool"
where
  "bottom r B \<longleftrightarrow> (\<forall>x. B \<sqsubseteq>\<^sub>r x)"


locale lbv = Semilat +
  fixes T :: "'a" ("\<top>") 
  fixes B :: "'a" ("\<bottom>") 
  fixes step :: "'a step_type" 
  assumes top: "top r \<top>"
  assumes T_A: "\<top> \<in> A"
  assumes bot: "bottom r \<bottom>" 
  assumes B_A: "\<bottom> \<in> A"

  fixes merge :: "'a certificate \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a"
  defines mrg_def: "merge cert \<equiv> LBVSpec.merge cert f r \<top>"

  fixes wti :: "'a certificate \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"
  defines wti_def: "wti cert \<equiv> wtl_inst cert f r \<top> step"
 
  fixes wtc :: "'a certificate \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"
  defines wtc_def: "wtc cert \<equiv> wtl_cert cert f r \<top> \<bottom> step"

  fixes wtl :: "'b list \<Rightarrow> 'a certificate \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"
  defines wtl_def: "wtl ins cert \<equiv> wtl_inst_list ins cert f r \<top> \<bottom> step"


lemma (in lbv) wti:
  "wti c pc s = merge c pc (step pc s) (c!(pc+1))"
  (*<*) by (simp add: wti_def mrg_def wtl_inst_def) (*>*)

lemma (in lbv) wtc: 
  "wtc c pc s = (if c!pc = \<bottom> then wti c pc s else if s \<sqsubseteq>\<^sub>r c!pc then wti c pc (c!pc) else \<top>)"
  (*<*) by (unfold wtc_def wti_def wtl_cert_def) rule (*>*)

lemma cert_okD1 [intro?]:
  "cert_ok c n T B A \<Longrightarrow> pc < n \<Longrightarrow> c!pc \<in> A"
  (*<*) by (unfold cert_ok_def) fast (*>*)

lemma cert_okD2 [intro?]:
  "cert_ok c n T B A \<Longrightarrow> c!n = B"
  (*<*) by (simp add: cert_ok_def) (*>*)

lemma cert_okD3 [intro?]:
  "cert_ok c n T B A \<Longrightarrow> B \<in> A \<Longrightarrow> pc < n \<Longrightarrow> c!Suc pc \<in> A"
  (*<*) by (drule Suc_leI) (auto simp add: le_eq_less_or_eq dest: cert_okD1 cert_okD2) (*>*)

lemma cert_okD4 [intro?]:
  "cert_ok c n T B A \<Longrightarrow> pc < n \<Longrightarrow> c!pc \<noteq> T"
  (*<*) by (simp add: cert_ok_def) (*>*)

declare Let_def [simp]

subsection "more semilattice lemmas"


lemma (in lbv) sup_top [simp, elim]:
  assumes x: "x \<in> A" 
  shows "x \<squnion>\<^sub>f \<top> = \<top>"
(*<*)
proof -
  from top have "x \<squnion>\<^sub>f \<top> \<sqsubseteq>\<^sub>r \<top>" ..
  moreover from x T_A have "\<top> \<sqsubseteq>\<^sub>r x \<squnion>\<^sub>f \<top>" ..
  ultimately show ?thesis ..
qed
(*>*)
  
lemma (in lbv) plusplussup_top [simp, elim]:
  "set xs \<subseteq> A \<Longrightarrow> xs \<Squnion>\<^bsub>f\<^esub> \<top> = \<top>"
  by (induct xs) auto


lemma (in Semilat) pp_ub1':
  assumes S: "snd`set S \<subseteq> A" 
  assumes y: "y \<in> A" and ab: "(a, b) \<in> set S" 
  shows "b \<sqsubseteq>\<^sub>r map snd [(p', t') \<leftarrow> S . p' = a] \<Squnion>\<^bsub>f\<^esub> y"
(*<*)
proof -
  from S have "\<forall>(x,y) \<in> set S. y \<in> A" by auto
  with Semilat_axioms show ?thesis using y ab by (rule ub1')
qed 
(*>*)

lemma (in lbv) bottom_le [simp, intro!]: "\<bottom> \<sqsubseteq>\<^sub>r x"
  by (insert bot) (simp add: bottom_def)

lemma (in lbv) le_bottom [simp]: "x \<sqsubseteq>\<^sub>r \<bottom> = (x = \<bottom>)"
  by (blast intro: antisym_r)


subsection "merge"

lemma (in lbv) merge_Nil [simp]:
  "merge c pc [] x = x" by (simp add: mrg_def)

lemma (in lbv) merge_Cons [simp]:
  "merge c pc (l#ls) x = merge c pc ls (if fst l=pc+1 then snd l +_f x
                                        else if snd l \<sqsubseteq>\<^sub>r c!fst l then x
                                        else \<top>)"
  by (simp add: mrg_def split_beta)

lemma (in lbv) merge_Err [simp]:
  "snd`set ss \<subseteq> A \<Longrightarrow> merge c pc ss \<top> = \<top>"
  by (induct ss) auto

lemma (in lbv) merge_not_top:
  "\<And>x. snd`set ss \<subseteq> A \<Longrightarrow> merge c pc ss x \<noteq> \<top> \<Longrightarrow> 
  \<forall>(pc',s') \<in> set ss. (pc' \<noteq> pc+1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc')"
  (is "\<And>x. ?set ss \<Longrightarrow> ?merge ss x \<Longrightarrow> ?P ss")
(*<*)
proof (induct ss)
  show "?P []" by simp
next
  fix x ls l
  assume "?set (l#ls)" then obtain set: "snd`set ls \<subseteq> A" by simp
  assume merge: "?merge (l#ls) x" 
  moreover
  obtain pc' s' where [simp]: "l = (pc',s')" by (cases l)
  ultimately
  obtain x' where merge': "?merge ls x'" by simp 
  assume "\<And>x. ?set ls \<Longrightarrow> ?merge ls x \<Longrightarrow> ?P ls" hence "?P ls" using set merge' .
  moreover
  from merge set
  have "pc' \<noteq> pc+1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'" by (simp split: if_split_asm)
  ultimately show "?P (l#ls)" by simp
qed
(*>*)


lemma (in lbv) merge_def:
  shows 
  "\<And>x. x \<in> A \<Longrightarrow> snd`set ss \<subseteq> A \<Longrightarrow>
  merge c pc ss x = 
  (if \<forall>(pc',s') \<in> set ss. pc'\<noteq>pc+1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc' then
    map snd [(p',t') \<leftarrow> ss. p'=pc+1] \<Squnion>\<^bsub>f\<^esub> x
  else \<top>)" 
  (is "\<And>x. _ \<Longrightarrow> _ \<Longrightarrow> ?merge ss x = ?if ss x" is "\<And>x. _ \<Longrightarrow> _ \<Longrightarrow> ?P ss x")
(*<*)
proof (induct ss)
  fix x show "?P [] x" by simp
next 
  fix x assume x: "x \<in> A" 
  fix l::"nat \<times> 'a" and ls  
  assume "snd`set (l#ls) \<subseteq> A"
  then obtain l: "snd l \<in> A" and ls: "snd`set ls \<subseteq> A" by auto
  assume "\<And>x. x \<in> A \<Longrightarrow> snd`set ls \<subseteq> A \<Longrightarrow> ?P ls x" 
  hence IH: "\<And>x. x \<in> A \<Longrightarrow> ?P ls x" using ls by iprover
  obtain pc' s' where [simp]: "l = (pc',s')" by (cases l)
  hence "?merge (l#ls) x = ?merge ls 
    (if pc'=pc+1 then s' \<squnion>\<^sub>f x else if s' \<sqsubseteq>\<^sub>r c!pc' then x else \<top>)"
    (is "?merge (l#ls) x = ?merge ls ?if'")
    by simp 
  also have "\<dots> = ?if ls ?if'" 
  proof -
    from l have "s' \<in> A" by simp
    with x have "s' \<squnion>\<^sub>f x \<in> A" by simp
    with x T_A have "?if' \<in> A" by auto
    hence "?P ls ?if'" by (rule IH) thus ?thesis by simp
  qed
  also have "\<dots> = ?if (l#ls) x"
    proof (cases "\<forall>(pc', s')\<in>set (l#ls). pc'\<noteq>pc+1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'")
      case True
      hence "\<forall>(pc', s')\<in>set ls. pc'\<noteq>pc+1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'" by auto
      moreover
      from True have 
        "map snd [(p',t') \<leftarrow> ls . p'=pc+1] \<Squnion>\<^bsub>f\<^esub> ?if' = 
        (map snd [(p',t') \<leftarrow> l#ls . p'=pc+1] \<Squnion>\<^bsub>f\<^esub> x)"
        by simp
      ultimately
      show ?thesis using True by simp
    next
      case False 
      moreover
      from ls have "set (map snd [(p', t') \<leftarrow> ls . p' = Suc pc]) \<subseteq> A" by auto
      ultimately show ?thesis by auto
    qed
  finally show "?P (l#ls) x" .
qed
(*>*)

lemma (in lbv) merge_not_top_s:
  assumes x:  "x \<in> A" and ss: "snd`set ss \<subseteq> A"
  assumes m:  "merge c pc ss x \<noteq> \<top>"
  shows "merge c pc ss x = (map snd [(p',t') \<leftarrow> ss. p'=pc+1] \<Squnion>\<^bsub>f\<^esub> x)"
(*<*)
proof -
  from ss m have "\<forall>(pc',s') \<in> set ss. (pc' \<noteq> pc+1 \<longrightarrow> s' <=_r c!pc')" 
    by (rule merge_not_top)
  with x ss m show ?thesis by - (drule merge_def, auto split: if_split_asm)
qed
(*>*)

subsection "wtl-inst-list"

lemmas [iff] = not_Err_eq

lemma (in lbv) wtl_Nil [simp]: "wtl [] c pc s = s" 
  by (simp add: wtl_def)

lemma (in lbv) wtl_Cons [simp]: 
  "wtl (i#is) c pc s = 
  (let s' = wtc c pc s in if s' = \<top> \<or> s = \<top> then \<top> else wtl is c (pc+1) s')"
  by (simp add: wtl_def wtc_def)

lemma (in lbv) wtl_Cons_not_top:
  "wtl (i#is) c pc s \<noteq> \<top> = 
  (wtc c pc s \<noteq> \<top> \<and> s \<noteq> T \<and> wtl is c (pc+1) (wtc c pc s) \<noteq> \<top>)"
  by (auto simp del: split_paired_Ex)

lemma (in lbv) wtl_top [simp]:  "wtl ls c pc \<top> = \<top>"
  by (cases ls) auto

lemma (in lbv) wtl_not_top:
  "wtl ls c pc s \<noteq> \<top> \<Longrightarrow> s \<noteq> \<top>"
  by (cases "s=\<top>") auto

lemma (in lbv) wtl_append [simp]:
  "\<And>pc s. wtl (a@b) c pc s = wtl b c (pc+length a) (wtl a c pc s)"
  by (induct a) auto

lemma (in lbv) wtl_take:
  "wtl is c pc s \<noteq> \<top> \<Longrightarrow> wtl (take pc' is) c pc s \<noteq> \<top>"
  (is "?wtl is \<noteq> _ \<Longrightarrow> _")
(*<*)
proof -
  assume "?wtl is \<noteq> \<top>"
  hence "?wtl (take pc' is @ drop pc' is) \<noteq> \<top>" by simp  
  thus ?thesis by (auto dest!: wtl_not_top simp del: append_take_drop_id)
qed
(*>*)

lemma take_Suc:
  "\<forall>n. n < length l \<longrightarrow> take (Suc n) l = (take n l)@[l!n]" (is "?P l")
(*<*)
proof (induct l)
  show "?P []" by simp
next
  fix x xs assume IH: "?P xs"  
  show "?P (x#xs)"
  proof (intro strip)
    fix n assume "n < length (x#xs)"
    with IH show "take (Suc n) (x # xs) = take n (x # xs) @ [(x # xs) ! n]" 
      by (cases n, auto)
  qed
qed
(*>*)

lemma (in lbv) wtl_Suc:
  assumes suc: "pc+1 < length is"
  assumes wtl: "wtl (take pc is) c 0 s \<noteq> \<top>"
  shows "wtl (take (pc+1) is) c 0 s = wtc c pc (wtl (take pc is) c 0 s)"
(*<*)
proof -
  from suc have "take (pc+1) is=(take pc is)@[is!pc]" by (simp add: take_Suc)
  with suc wtl show ?thesis by (simp add: min_def)
qed
(*>*)

lemma (in lbv) wtl_all:
  assumes all: "wtl is c 0 s \<noteq> \<top>" (is "?wtl is \<noteq> _") 
  assumes pc:  "pc < length is"
  shows  "wtc c pc (wtl (take pc is) c 0 s) \<noteq> \<top>"
(*<*)
proof -
  from pc have "0 < length (drop pc is)" by simp
  then  obtain i r where Cons: "drop pc is = i#r" 
    by (auto simp add: neq_Nil_conv simp del: length_drop drop_eq_Nil)
  hence "i#r = drop pc is" ..
  with all have take: "?wtl (take pc is@i#r) \<noteq> \<top>" by simp 
  from pc have "is!pc = drop pc is ! 0" by simp
  with Cons have "is!pc = i" by simp
  with take pc show ?thesis by (auto simp add: min_def split: if_split_asm)
qed
(*>*)

subsection "preserves-type"

lemma (in lbv) merge_pres:
  assumes s0: "snd`set ss \<subseteq> A" and x: "x \<in> A"
  shows "merge c pc ss x \<in> A"
(*<*)
proof -
  from s0 have "set (map snd [(p', t') \<leftarrow> ss . p'=pc+1]) \<subseteq> A" by auto
  with x semilat Semilat_axioms  have "(map snd [(p', t') \<leftarrow> ss . p'=pc+1] \<Squnion>\<^bsub>f\<^esub> x) \<in> A"
    by (auto intro!: plusplus_closed)
  with s0 x show ?thesis by (simp add: merge_def T_A)
qed
(*>*)
  
lemma pres_typeD2:
  "pres_type step n A \<Longrightarrow> s \<in> A \<Longrightarrow> p < n \<Longrightarrow> snd`set (step p s) \<subseteq> A"
  by auto (drule pres_typeD)

lemma (in lbv) wti_pres [intro?]:
  assumes pres: "pres_type step n A" 
  assumes cert: "c!(pc+1) \<in> A"
  assumes s_pc: "s \<in> A" "pc < n"
  shows "wti c pc s \<in> A"
(*<*)
proof -
  from pres s_pc have "snd`set (step pc s) \<subseteq> A" by (rule pres_typeD2)
  with cert show ?thesis by (simp add: wti merge_pres)
qed
(*>*)

lemma (in lbv) wtc_pres:
  assumes "pres_type step n A"
  assumes "c!pc \<in> A" and "c!(pc+1) \<in> A"
  assumes "s \<in> A" and "pc < n"
  shows "wtc c pc s \<in> A"
(*<*)
proof -
  have "wti c pc s \<in> A" using assms(1,3-5) ..
  moreover have "wti c pc (c!pc) \<in> A" using assms(1,3,2,5) ..
  ultimately show ?thesis using T_A by (simp add: wtc) 
qed
(*>*)

lemma (in lbv) wtl_pres:
  assumes pres: "pres_type step (length is) A"
  assumes cert: "cert_ok c (length is) \<top> \<bottom> A"
  assumes s:    "s \<in> A" 
  assumes all:  "wtl is c 0 s \<noteq> \<top>"
  shows "pc < length is \<Longrightarrow> wtl (take pc is) c 0 s \<in> A"
  (is "?len pc \<Longrightarrow> ?wtl pc \<in> A")
(*<*)
proof (induct pc)
  from s show "?wtl 0 \<in> A" by simp
next
  fix n assume Suc_n: "Suc n < length is"
  hence n1: "n+1 < length is" by simp
  then obtain n: "n < length is" by simp
  assume "n < length is \<Longrightarrow> ?wtl n \<in> A"
  hence "?wtl n \<in> A" using n .
  from pres _ _ this n
  have "wtc c n (?wtl n) \<in> A"
  proof (rule wtc_pres)
    from cert n show "c!n \<in> A" by (rule cert_okD1)
    from cert n1 show "c!(n+1) \<in> A" by (rule cert_okD1)
  qed
  also
  from all n have "?wtl n \<noteq> \<top>" by - (rule wtl_take)
  with n1 have "wtc c n (?wtl n) = ?wtl (n+1)" by (rule wtl_Suc [symmetric])
  finally  show "?wtl (Suc n) \<in> A" by simp
qed
(*>*)

end
