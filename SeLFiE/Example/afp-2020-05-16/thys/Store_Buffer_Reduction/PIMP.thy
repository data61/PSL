(* Copyright (C) 2007--2010 Norbert Schirmer
 * All rights reserved, DFKI GmbH 
 *)
(*
header {* Parallel - IMP *}
*)

subsection \<open>PIMP\<close>

theory PIMP
imports ReduceStoreBufferSimulation
begin

datatype expr = Const val | Mem bool addr | Tmp sop
              | Unop "val \<Rightarrow> val" expr 
              | Binop "val \<Rightarrow> val \<Rightarrow> val" expr expr
(* Hmm. addr's should be vals ? *)
datatype stmt = 
                Skip 
              | Assign bool expr expr "tmps \<Rightarrow> owns" "tmps \<Rightarrow> owns" "tmps \<Rightarrow> owns" "tmps \<Rightarrow> owns" 
              | CAS expr expr expr "tmps \<Rightarrow> owns" "tmps \<Rightarrow> owns" "tmps \<Rightarrow> owns" "tmps \<Rightarrow> owns" 
              | Seq "stmt" "stmt"
              | Cond expr "stmt" "stmt"
              | While  expr "stmt" 


              | SGhost "tmps \<Rightarrow> owns" "tmps \<Rightarrow> owns" "tmps \<Rightarrow> owns" "tmps \<Rightarrow> owns"
              | SFence

(*
FIXME:
Genralisation of Assignment and CAS (and SGhost) would be nice:
  * A L R W sets not just dependent on value of addr, but on tmps 
    (beware of domain: thm program_step_tmps_mono) or some ghost state
*)
primrec used_tmps:: "expr \<Rightarrow> nat" \<comment> \<open>number of temporaries used\<close>
where
"used_tmps (Const v) = 0"
| "used_tmps (Mem volatile addr) = 1"
| "used_tmps (Tmp sop) = 0"
| "used_tmps (Unop f e) = used_tmps e"
| "used_tmps (Binop f e\<^sub>1 e\<^sub>2) = used_tmps e\<^sub>1 + used_tmps e\<^sub>2"

primrec issue_expr:: "tmp \<Rightarrow> expr \<Rightarrow> instr list" \<comment> \<open>load operations\<close>
where
"issue_expr t (Const v) = []"
|"issue_expr t (Mem volatile a) = [Read volatile a t]"
|"issue_expr t (Tmp sop) = []"
|"issue_expr t (Unop f e) = issue_expr t e"
|"issue_expr t (Binop f e\<^sub>1 e\<^sub>2) = issue_expr t e\<^sub>1 @ issue_expr (t + (used_tmps e\<^sub>1)) e\<^sub>2" 

primrec eval_expr:: "tmp \<Rightarrow> expr \<Rightarrow> sop" \<comment> \<open>calculate result\<close>
where
"eval_expr t (Const v) = ({},\<lambda>\<theta>. v)"
|"eval_expr t (Mem volatile a) = ({t},\<lambda>\<theta>. the (\<theta> t))"
|"eval_expr t (Tmp sop) = sop"
(*
"eval_expr t (Tmp sop) = ({i. i \<in> fst sop \<and> i < t}, \<lambda>\<theta>. snd sop (\<theta> |`{i. i \<in> fst sop \<and> i < t}))"*)
                         \<comment> \<open>trick to enforce sop to be sensible in the current context, without
                               having to include wellformedness constraints\<close>
|"eval_expr t (Unop f e) = (let (D,f\<^sub>e) = eval_expr t e in (D,\<lambda>\<theta>. f (f\<^sub>e \<theta>))) "
|"eval_expr t (Binop f e\<^sub>1 e\<^sub>2) = (let (D\<^sub>1,f\<^sub>1) = eval_expr t e\<^sub>1;
                                    (D\<^sub>2,f\<^sub>2) = eval_expr (t + (used_tmps e\<^sub>1)) e\<^sub>2  
                                in (D\<^sub>1 \<union> D\<^sub>2,\<lambda>\<theta>. f (f\<^sub>1 \<theta>) (f\<^sub>2 \<theta>)))" 

primrec valid_sops_expr:: "nat \<Rightarrow> expr \<Rightarrow> bool"
where
"valid_sops_expr t (Const v) = True"
|"valid_sops_expr t (Mem volatile a) = True"
|"valid_sops_expr t (Tmp sop) = ((\<forall>t' \<in> fst sop. t' < t) \<and> valid_sop sop)"
|"valid_sops_expr t (Unop f e) = valid_sops_expr t e"
|"valid_sops_expr t (Binop f e\<^sub>1 e\<^sub>2) = (valid_sops_expr t e\<^sub>1 \<and> valid_sops_expr t e\<^sub>2)" 


primrec valid_sops_stmt:: "nat \<Rightarrow> stmt \<Rightarrow> bool"
where
"valid_sops_stmt t Skip = True"
|"valid_sops_stmt t (Assign volatile a e A L R W) = (valid_sops_expr t a \<and> valid_sops_expr t e)"
|"valid_sops_stmt t (CAS a c\<^sub>e s\<^sub>e A L R W) = (valid_sops_expr t a \<and> valid_sops_expr t c\<^sub>e \<and> 
                                            valid_sops_expr t s\<^sub>e)"
|"valid_sops_stmt t (Seq s\<^sub>1 s\<^sub>2) = (valid_sops_stmt t s\<^sub>1 \<and> valid_sops_stmt t s\<^sub>2)"
|"valid_sops_stmt t (Cond e s\<^sub>1 s\<^sub>2) = (valid_sops_expr t e \<and> valid_sops_stmt t s\<^sub>1 \<and> valid_sops_stmt t s\<^sub>2)"
|"valid_sops_stmt t (While e s) = (valid_sops_expr t e \<and> valid_sops_stmt t s)"
|"valid_sops_stmt t (SGhost A L R W) = True"
|"valid_sops_stmt t SFence = True"

  
type_synonym stmt_config = "stmt \<times> nat"
consts isTrue:: "val \<Rightarrow> bool"

inductive stmt_step:: "tmps \<Rightarrow> stmt_config  \<Rightarrow> stmt_config \<times> instrs  \<Rightarrow> bool" 
  ("_\<turnstile> _ \<rightarrow>\<^sub>s _" [60,60,60] 100)
for \<theta>
where

  AssignAddr:
  "\<forall>sop. a \<noteq> Tmp sop  \<Longrightarrow>
   \<theta>\<turnstile> (Assign volatile a e A L R W, t) \<rightarrow>\<^sub>s 
         ((Assign volatile (Tmp (eval_expr t a)) e A L R W, t + used_tmps a), issue_expr t a)"

|  Assign:
  "D \<subseteq> dom \<theta> \<Longrightarrow> 
   \<theta>\<turnstile> (Assign volatile (Tmp (D,a)) e A L R W, t) \<rightarrow>\<^sub>s 
         ((Skip, t + used_tmps e), 
           issue_expr t e@[Write volatile (a \<theta>) (eval_expr t e) (A \<theta>) (L \<theta>) (R \<theta>) (W \<theta>)])"


| CASAddr:
  "\<forall>sop. a \<noteq> Tmp sop  \<Longrightarrow>
   \<theta>\<turnstile> (CAS a c\<^sub>e s\<^sub>e A L R W, t) \<rightarrow>\<^sub>s 
         ((CAS (Tmp (eval_expr t a)) c\<^sub>e s\<^sub>e A L R W, t + used_tmps a), issue_expr t a)"


| CASComp:
  "\<forall>sop. c\<^sub>e \<noteq> Tmp sop  \<Longrightarrow>
   \<theta>\<turnstile> (CAS (Tmp (D\<^sub>a,a)) c\<^sub>e s\<^sub>e A L R W, t) \<rightarrow>\<^sub>s 
         ((CAS (Tmp (D\<^sub>a,a)) (Tmp (eval_expr t c\<^sub>e)) s\<^sub>e A L R W, t + used_tmps c\<^sub>e), issue_expr t c\<^sub>e)"

| CAS:
  "\<lbrakk>D\<^sub>a \<subseteq> dom \<theta>; D\<^sub>c \<subseteq> dom \<theta>; eval_expr t s\<^sub>e  = (D,f) \<rbrakk>  
   \<Longrightarrow>
   \<theta>\<turnstile> (CAS (Tmp (D\<^sub>a,a)) (Tmp (D\<^sub>c,c)) s\<^sub>e A L R W, t) \<rightarrow>\<^sub>s 
         ((Skip, Suc (t + used_tmps s\<^sub>e)), issue_expr t s\<^sub>e@
           [RMW (a \<theta>) (t + used_tmps s\<^sub>e) (D,f) (\<lambda>\<theta>. the (\<theta> (t + used_tmps s\<^sub>e)) = c \<theta>) (\<lambda>v\<^sub>1 v\<^sub>2. v\<^sub>1) 
            (A \<theta>) (L \<theta>) (R \<theta>) (W \<theta>) ])"

| Seq:
  "\<theta>\<turnstile> (s\<^sub>1, t) \<rightarrow>\<^sub>s ((s\<^sub>1', t'), is) 
   \<Longrightarrow> 
   \<theta>\<turnstile> (Seq s\<^sub>1 s\<^sub>2, t) \<rightarrow>\<^sub>s ((Seq s\<^sub>1' s\<^sub>2, t'),is)"

| SeqSkip:
  "\<theta>\<turnstile> (Seq Skip s\<^sub>2, t) \<rightarrow>\<^sub>s ((s\<^sub>2, t), [])"


| Cond:
  "\<forall>sop. e \<noteq> Tmp sop 
   \<Longrightarrow>
   \<theta>\<turnstile> (Cond e s\<^sub>1 s\<^sub>2, t) \<rightarrow>\<^sub>s 
    ((Cond (Tmp (eval_expr t e)) s\<^sub>1 s\<^sub>2, t + used_tmps e), issue_expr t e)"

| CondTrue:
  "\<lbrakk>D \<subseteq> dom \<theta>; isTrue (e \<theta>)\<rbrakk> 
   \<Longrightarrow> 
   \<theta>\<turnstile> (Cond (Tmp (D,e)) s\<^sub>1 s\<^sub>2, t) \<rightarrow>\<^sub>s ((s\<^sub>1, t),[])"

| CondFalse:
  "\<lbrakk>D \<subseteq> dom \<theta>; \<not> isTrue (e \<theta>)\<rbrakk> 
   \<Longrightarrow> 
   \<theta>\<turnstile> (Cond (Tmp (D,e)) s\<^sub>1 s\<^sub>2, t) \<rightarrow>\<^sub>s ((s\<^sub>2, t),[])"

| While:
  "\<theta>\<turnstile> (While e s, t) \<rightarrow>\<^sub>s 
   ((Cond e (Seq s (While e s)) Skip, t),[])"

| SGhost:
  "\<theta>\<turnstile> (SGhost A L R W, t) \<rightarrow>\<^sub>s ((Skip, t),[Ghost (A \<theta>) (L \<theta>) (R \<theta>) (W \<theta>)])"

| SFence:
  "\<theta>\<turnstile> (SFence, t) \<rightarrow>\<^sub>s ((Skip, t),[Fence])"

inductive_cases stmt_step_cases [cases set]:
"\<theta>\<turnstile> (Skip, t) \<rightarrow>\<^sub>s c"
"\<theta>\<turnstile> (Assign volatile a e A L R W, t) \<rightarrow>\<^sub>s c"
"\<theta>\<turnstile> (CAS a c\<^sub>e s\<^sub>e A L R W, t) \<rightarrow>\<^sub>s c"
"\<theta>\<turnstile> (Seq s\<^sub>1 s\<^sub>2, t) \<rightarrow>\<^sub>s c"
"\<theta>\<turnstile> (Cond e s\<^sub>1 s\<^sub>2, t) \<rightarrow>\<^sub>s c"
"\<theta>\<turnstile> (While e s, t) \<rightarrow>\<^sub>s c"
"\<theta>\<turnstile> (SGhost A L R W, t) \<rightarrow>\<^sub>s c"
"\<theta>\<turnstile> (SFence, t) \<rightarrow>\<^sub>s c"

lemma valid_sops_expr_mono: "\<And>t t'. valid_sops_expr t e \<Longrightarrow> t \<le> t'  \<Longrightarrow> valid_sops_expr t' e"
  by (induct e) auto

lemma valid_sops_stmt_mono: "\<And>t t'.  valid_sops_stmt t s \<Longrightarrow> t \<le> t'  \<Longrightarrow> valid_sops_stmt t' s"
  by (induct s) (auto intro: valid_sops_expr_mono)

lemma valid_sops_expr_valid_sop: "\<And>t. valid_sops_expr t e \<Longrightarrow> valid_sop (eval_expr t e)"
proof (induct e)
  case (Unop f e)
  then obtain "valid_sops_expr t e"
    by simp
  from Unop.hyps [OF this]
  have vs: "valid_sop (eval_expr t e)"
    by simp
  obtain D g where eval_e: "eval_expr t e = (D,g)"
    by (cases "eval_expr t e")

  interpret valid_sop "(D,g)"
    using vs eval_e
    by simp

  show ?case
    apply (clarsimp simp add: Let_def valid_sop_def eval_e)
    apply (drule valid_sop [OF refl])
    apply simp
    done
next
  case (Binop f e\<^sub>1 e\<^sub>2)
  then obtain v1: "valid_sops_expr t e\<^sub>1" and v2: "valid_sops_expr t e\<^sub>2"
    by simp
  with Binop.hyps (1) [of t]  Binop.hyps (2) [of "(t + used_tmps e\<^sub>1)"]  
    valid_sops_expr_mono [OF v2, of "(t + used_tmps e\<^sub>1)"]
  obtain vs1: "valid_sop (eval_expr t e\<^sub>1)" and vs2: "valid_sop (eval_expr (t + used_tmps e\<^sub>1) e\<^sub>2)"
    by auto
  obtain D\<^sub>1 g\<^sub>1 where eval_e\<^sub>1: "eval_expr t e\<^sub>1 = (D\<^sub>1,g\<^sub>1)"
    by (cases "eval_expr t e\<^sub>1")
  obtain D\<^sub>2 g\<^sub>2 where eval_e\<^sub>2: "eval_expr (t + used_tmps e\<^sub>1) e\<^sub>2 = (D\<^sub>2,g\<^sub>2)"
    by (cases "eval_expr (t + used_tmps e\<^sub>1) e\<^sub>2")
  interpret vs1: valid_sop "(D\<^sub>1,g\<^sub>1)"
    using vs1 eval_e\<^sub>1 by auto
  interpret vs2: valid_sop "(D\<^sub>2,g\<^sub>2)"
    using vs2 eval_e\<^sub>2 by auto
  {
    fix \<theta>:: "nat\<Rightarrow>val option" 
    assume D1: "D\<^sub>1 \<subseteq> dom \<theta>" 
    assume D2: "D\<^sub>2 \<subseteq> dom \<theta>"
    have "f (g\<^sub>1 \<theta>) (g\<^sub>2 \<theta>) = f (g\<^sub>1 (\<theta> |` (D\<^sub>1 \<union> D\<^sub>2))) (g\<^sub>2 (\<theta> |` (D\<^sub>1 \<union> D\<^sub>2)))"
    proof -
      from vs1.valid_sop [OF refl D1]
      have "g\<^sub>1 \<theta> = g\<^sub>1 (\<theta> |` D\<^sub>1)".
      also
      from D1 have D1': "D\<^sub>1 \<subseteq> dom (\<theta> |` (D\<^sub>1 \<union> D\<^sub>2))"
	by auto
      have "\<theta> |` (D\<^sub>1 \<union> D\<^sub>2) |` D\<^sub>1 = \<theta> |` D\<^sub>1"
	apply (rule ext)
	apply (auto simp add: restrict_map_def)
	done
      with vs1.valid_sop [OF refl D1']
      have "g\<^sub>1 (\<theta> |` D\<^sub>1) = g\<^sub>1 (\<theta> |` (D\<^sub>1 \<union> D\<^sub>2))"
	by auto
      finally have g1: "g\<^sub>1 (\<theta> |` (D\<^sub>1 \<union> D\<^sub>2)) = g\<^sub>1 \<theta>"
	by simp

      from vs2.valid_sop [OF refl D2]
      have "g\<^sub>2 \<theta> = g\<^sub>2 (\<theta> |` D\<^sub>2)".
      also
      from D2 have D2': "D\<^sub>2 \<subseteq> dom (\<theta> |` (D\<^sub>1 \<union> D\<^sub>2))"
	by auto
      have "\<theta> |` (D\<^sub>1 \<union> D\<^sub>2) |` D\<^sub>2 = \<theta> |` D\<^sub>2"
	apply (rule ext)
	apply (auto simp add: restrict_map_def)
	done
      with vs2.valid_sop [OF refl D2']
      have "g\<^sub>2 (\<theta> |` D\<^sub>2) = g\<^sub>2 (\<theta> |` (D\<^sub>1 \<union> D\<^sub>2))"
	by auto
      finally have g2: "g\<^sub>2 (\<theta> |` (D\<^sub>1 \<union> D\<^sub>2)) = g\<^sub>2 \<theta>"
	by simp

      from g1 g2 show ?thesis by simp
    qed
  }
      
  note lem=this
  show ?case
    apply (clarsimp simp add: Let_def valid_sop_def eval_e\<^sub>1 eval_e\<^sub>2)
    apply (rule lem)
    by auto
qed (auto simp add: valid_sop_def)

lemma valid_sops_expr_eval_expr_in_range: 
  "\<And>t. valid_sops_expr t e \<Longrightarrow> \<forall>t' \<in> fst (eval_expr t e). t' < t + used_tmps e"
proof (induct e)
  case (Unop f e)
  thus ?case
    apply (cases "eval_expr t e")
    apply auto
    done
next
  case (Binop f e\<^sub>1 e\<^sub>2)
  then obtain v1: "valid_sops_expr t e\<^sub>1" and v2: "valid_sops_expr t e\<^sub>2"
    by simp
  from valid_sops_expr_mono [OF v2]
  have v2': "valid_sops_expr (t + used_tmps e\<^sub>1) e\<^sub>2"
    by auto
  from Binop.hyps (1) [OF v1] Binop.hyps (2) [OF v2']
  show ?case
    apply (cases "eval_expr t e\<^sub>1")
    apply (cases "eval_expr (t + used_tmps e\<^sub>1) e\<^sub>2")
    apply auto
    done
qed auto



lemma stmt_step_tmps_count_mono:
  assumes step: "\<theta>\<turnstile> (s,t) \<rightarrow>\<^sub>s ((s',t'),is)"
  shows "t \<le> t'"
using step
by (induct x=="(s,t)" y=="((s',t'),is)" arbitrary: s t s' t' "is" rule: stmt_step.induct) force+
  

lemma valid_sops_stmt_invariant:
  assumes step: "\<theta>\<turnstile> (s,t) \<rightarrow>\<^sub>s ((s',t'),is)"
  shows "valid_sops_stmt t s \<Longrightarrow> valid_sops_stmt t' s'"
using step
proof (induct x=="(s,t)" y=="((s',t'),is)" arbitrary: s t s' t' "is" rule: stmt_step.induct)
  case AssignAddr thus ?case by 
  (force simp add: valid_sops_expr_valid_sop intro: valid_sops_stmt_mono valid_sops_expr_mono  
     dest: valid_sops_expr_eval_expr_in_range)
next
  case Assign thus ?case by simp
next
  case CASAddr thus ?case by 
  (force simp add: valid_sops_expr_valid_sop intro: valid_sops_stmt_mono valid_sops_expr_mono  
     dest: valid_sops_expr_eval_expr_in_range)
next
  case CASComp thus ?case by 
  (force simp add: valid_sops_expr_valid_sop intro: valid_sops_stmt_mono valid_sops_expr_mono  
     dest: valid_sops_expr_eval_expr_in_range)
next
  case CAS thus ?case by simp
next
  case Seq thus ?case by (force intro: valid_sops_stmt_mono dest: stmt_step_tmps_count_mono)
next
  case SeqSkip thus ?case by auto
next
  case Cond thus ?case 
    by (fastforce simp add: valid_sops_expr_valid_sop intro: valid_sops_stmt_mono 
     dest: valid_sops_expr_eval_expr_in_range)
next
  case CondTrue thus ?case by force
next
  case CondFalse thus ?case by force
next
  case While thus ?case by auto
next
  case SGhost thus ?case by simp
next
  case SFence thus ?case by simp
qed


lemma map_le_restrict_map_eq: "m\<^sub>1 \<subseteq>\<^sub>m m\<^sub>2 \<Longrightarrow> D \<subseteq> dom m\<^sub>1 \<Longrightarrow> m\<^sub>2 |` D = m\<^sub>1 |` D"
  apply (rule ext)
  apply (force simp add: restrict_map_def map_le_def)
  done


lemma sbh_step_preserves_load_tmps_bound: 
  assumes step: "(is,\<O>,\<D>,\<theta>,sb,\<S>,m) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h (is',\<O>',\<D>',\<theta>',sb',\<S>',m')"
  assumes less: "\<forall>i \<in> load_tmps is. i < n" 
  shows "\<forall>i \<in> load_tmps is'. i < n"
  using step less
  by cases auto

lemma sbh_step_preserves_read_tmps_bound:
  assumes step: "(is,\<theta>,sb,m,\<D>,\<O>,\<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h (is',\<theta>',sb',m',\<D>',\<O>',\<S>')"
  assumes less_is: "\<forall>i \<in> load_tmps is. i < n" 
  assumes less_sb: "\<forall>i \<in> read_tmps sb. i < n" 
  shows "\<forall>i \<in> read_tmps sb'. i < n"
  using step less_is less_sb
  by cases (auto simp add: read_tmps_append)

lemma sbh_step_preserves_tmps_bound:
  assumes step: "(is,\<theta>,sb,m,\<D>,\<O>,\<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h (is',\<theta>',sb',m',\<D>',\<O>',\<S>')"
  assumes less_dom: "\<forall>i \<in> dom \<theta>. i < n" 
  assumes less_is: "\<forall>i \<in> load_tmps is. i < n" 
  shows "\<forall>i \<in> dom \<theta>'. i < n"
  using step less_dom  less_is
  by cases (auto simp add: read_tmps_append)

lemma flush_step_preserves_read_tmps:
  assumes step: "(m,sb,\<O>) \<rightarrow>\<^sub>f (m',sb',\<O>')"
  assumes less_sb: "\<forall>i \<in> read_tmps sb. i < n" 
  shows "\<forall>i \<in> read_tmps sb'. i < n"
  using step less_sb
  by cases (auto simp add: read_tmps_append)

lemma flush_step_preserves_write_sops:
  assumes step: "(m,sb,\<O>) \<rightarrow>\<^sub>f (m',sb',\<O>')"
  assumes less_sb: "\<forall>i\<in>\<Union>(fst ` write_sops sb). i < t" 
  shows "\<forall>i\<in>\<Union>(fst ` write_sops sb'). i < t"
  using step less_sb
  by cases (auto simp add: read_tmps_append)

lemma issue_expr_load_tmps_range': 
  "\<And>t. load_tmps (issue_expr t e) = {i. t \<le> i \<and> i < t + used_tmps e}"
apply (induct e)
apply (force simp add: load_tmps_append)+
done


lemma issue_expr_load_tmps_range: 
  "\<And>t. \<forall>i \<in> load_tmps (issue_expr t e). t \<le> i \<and> i < t + (used_tmps e)"
by (auto simp add: issue_expr_load_tmps_range')


lemma stmt_step_load_tmps_range':
  assumes step: "\<theta>\<turnstile> (s, t) \<rightarrow>\<^sub>s ((s', t'),is)"
  shows "load_tmps is = {i. t \<le> i \<and> i < t'}"
  using step 
  apply (induct x=="(s,t)" y=="((s',t'),is)" arbitrary: s t s' t' "is" rule: stmt_step.induct)
  apply (force simp add: load_tmps_append simp add: issue_expr_load_tmps_range')+
  done


lemma stmt_step_load_tmps_range:
  assumes step: "\<theta>\<turnstile> (s, t) \<rightarrow>\<^sub>s ((s', t'),is)"
  shows "\<forall>i \<in> load_tmps is. t \<le> i \<and> i < t'"
using stmt_step_load_tmps_range' [OF step]
by auto


lemma distinct_load_tmps_issue_expr: "\<And>t. distinct_load_tmps (issue_expr t e)"
  apply (induct e)
  apply (auto simp add: distinct_load_tmps_append dest!: issue_expr_load_tmps_range [rule_format])
  done

lemma max_used_load_tmps: "t + used_tmps e \<notin> load_tmps (issue_expr t e)"
proof -
  from issue_expr_load_tmps_range [rule_format, of "t+used_tmps e"]
  show ?thesis
    by auto
qed

lemma stmt_step_distinct_load_tmps:
  assumes step: "\<theta>\<turnstile> (s, t) \<rightarrow>\<^sub>s ((s', t'),is)"
  shows "distinct_load_tmps is"
  using step 
  apply (induct x=="(s,t)" y=="((s',t'),is)" arbitrary: s t s' t' "is" rule: stmt_step.induct)
  apply (force simp add: distinct_load_tmps_append distinct_load_tmps_issue_expr max_used_load_tmps)+  
  done

lemma store_sops_issue_expr [simp]: "\<And>t. store_sops (issue_expr t e) = {}"
  apply (induct e)
  apply (auto simp add: store_sops_append)
  done


lemma stmt_step_data_store_sops_range:
  assumes step: "\<theta>\<turnstile> (s, t) \<rightarrow>\<^sub>s ((s', t'),is)"
  assumes valid: "valid_sops_stmt t s"
  shows "\<forall>(D,f) \<in> store_sops is. \<forall>i \<in> D. i < t'"
using step valid
proof (induct x=="(s,t)" y=="((s',t'),is)" arbitrary: s t s' t' "is" rule: stmt_step.induct)
  case AssignAddr
  thus ?case
    by auto
next
  case (Assign D volatile a e)
  thus ?case
    apply (cases "eval_expr t e")
    apply (auto simp add: store_sops_append intro: valid_sops_expr_eval_expr_in_range [rule_format])
    done
next
  case CASAddr
  thus ?case
    by auto
next
  case CASComp
  thus ?case
    by auto
next
  case (CAS _ _ D f a A L R)
  thus ?case
    by (fastforce simp add: store_sops_append dest: valid_sops_expr_eval_expr_in_range [rule_format])
next
  case Seq
  thus ?case
    by (force intro: valid_sops_stmt_mono )
next
  case SeqSkip thus ?case by simp
next
  case Cond thus ?case
    by auto
next
  case CondTrue thus ?case by auto
next
  case CondFalse thus ?case by auto
next
  case While thus ?case by auto
next
  case SGhost thus ?case by auto
next
  case SFence thus ?case by auto
qed

lemma sbh_step_distinct_load_tmps_prog_step: 
      assumes step: "\<theta>\<turnstile>(s,t) \<rightarrow>\<^sub>s ((s',t'),is')"
  assumes load_tmps_le: "\<forall>i \<in> load_tmps is. i < t"
  assumes read_tmps_le: "\<forall>i \<in> read_tmps sb. i < t"
  shows "distinct_load_tmps is' \<and> (load_tmps is' \<inter> load_tmps is = {}) \<and>
         (load_tmps is' \<inter> read_tmps sb) = {}"
proof - 
  from stmt_step_load_tmps_range [OF step] stmt_step_distinct_load_tmps [OF step] 
    load_tmps_le read_tmps_le
  show ?thesis
    by force
qed


lemma data_dependency_consistent_instrs_issue_expr: 
  "\<And>t T. data_dependency_consistent_instrs T (issue_expr t e)"
  apply (induct e)
  apply (auto simp add: data_dependency_consistent_instrs_append 
    dest!: issue_expr_load_tmps_range [rule_format] 
    )
  done

lemma dom_eval_expr:
  "\<And>t. \<lbrakk>valid_sops_expr t e; x \<in> fst (eval_expr t e)\<rbrakk> \<Longrightarrow> x \<in> {i. i < t} \<union> load_tmps (issue_expr t e)"
proof (induct e)
  case Const thus ?case by simp
next
  case Mem thus ?case by simp
next
  case Tmp thus ?case by simp
next
  case (Unop f e)
  thus ?case
    by (cases "eval_expr t e") auto
next
  case (Binop f e1 e2)
  then obtain valid1: "valid_sops_expr t e1" and valid2: "valid_sops_expr t e2"
    by auto
  from valid_sops_expr_mono [OF valid2] have valid2': "valid_sops_expr (t+used_tmps e1) e2"
    by auto

  from Binop.hyps (1) [OF valid1] Binop.hyps (2) [OF valid2'] Binop.prems
  show ?case
    apply (case_tac "eval_expr t e1")
    apply (case_tac "eval_expr (t+used_tmps e1) e2")
    apply (auto simp add: load_tmps_append issue_expr_load_tmps_range')
    done
qed


lemma Cond_not_s\<^sub>1: "s\<^sub>1 \<noteq> Cond e s\<^sub>1 s\<^sub>2 " 
  by (induct s\<^sub>1) auto

lemma Cond_not_s\<^sub>2: "s\<^sub>2 \<noteq> Cond e s\<^sub>1 s\<^sub>2 " 
  by (induct s\<^sub>2) auto

lemma Seq_not_s\<^sub>1: "s\<^sub>1 \<noteq> Seq s\<^sub>1 s\<^sub>2"
  by (induct s\<^sub>1) auto

lemma Seq_not_s\<^sub>2: "s\<^sub>2 \<noteq> Seq s\<^sub>1 s\<^sub>2"
  by (induct s\<^sub>2) auto

lemma prog_step_progress:
  assumes step: "\<theta>\<turnstile>(s,t) \<rightarrow>\<^sub>s ((s',t'),is)"
  shows "(s',t') \<noteq> (s,t) \<or> is \<noteq> []"
using step 
proof (induct x=="(s,t)" y=="((s',t'),is)" arbitrary: s t s' t' "is" rule: stmt_step.induct)
  case (AssignAddr a _ _ _ _ _ _ t) thus ?case 
    by (cases "eval_expr t a") auto
next
  case Assign thus ?case by auto
next
  case (CASAddr a _ _ _ _ _ _ t) thus ?case by (cases "eval_expr t a") auto 
next
  case (CASComp c\<^sub>e _ _ _ _ _ _ _ t) thus ?case by (cases "eval_expr t c\<^sub>e") auto  
next
  case CAS thus ?case by auto
next
  case (Cond e _ _ t) thus ?case by (cases "eval_expr t e") auto  
next
  case CondTrue thus ?case using Cond_not_s\<^sub>1 by auto
next
  case CondFalse thus ?case using Cond_not_s\<^sub>2 by auto
next
  case Seq thus ?case by force
next
  case SeqSkip thus ?case using Seq_not_s\<^sub>2 by auto
next
  case While thus ?case by auto
next
  case SGhost thus ?case by auto
next
  case SFence thus ?case by auto
qed

lemma stmt_step_data_dependency_consistent_instrs:
  assumes step: "\<theta>\<turnstile> (s, t) \<rightarrow>\<^sub>s ((s', t'),is)"
  assumes valid: "valid_sops_stmt t s"
  shows "data_dependency_consistent_instrs ({i. i < t}) is"
  using step valid 
proof (induct x=="(s,t)" y=="((s',t'),is)" arbitrary: s t s' t' "is" T rule: stmt_step.induct)
  case AssignAddr
  thus ?case
    by (fastforce simp add: simp add: data_dependency_consistent_instrs_append 
    data_dependency_consistent_instrs_issue_expr load_tmps_append
    dest: dom_eval_expr)
next
  case Assign
  thus ?case
    by (fastforce simp add: simp add: data_dependency_consistent_instrs_append 
    data_dependency_consistent_instrs_issue_expr load_tmps_append
    dest: dom_eval_expr)
next
  case CASAddr
  thus ?case
    by (fastforce simp add: simp add: data_dependency_consistent_instrs_append 
    data_dependency_consistent_instrs_issue_expr load_tmps_append
    dest: dom_eval_expr)
next
  case CASComp
  thus ?case
    by (fastforce simp add: simp add: data_dependency_consistent_instrs_append 
    data_dependency_consistent_instrs_issue_expr load_tmps_append
    dest: dom_eval_expr)
next
  case CAS
  thus ?case
    by (fastforce simp add: simp add: data_dependency_consistent_instrs_append 
      data_dependency_consistent_instrs_issue_expr load_tmps_append
      dest: dom_eval_expr)
next
  case Seq
  thus ?case
    by (fastforce simp add: simp add: data_dependency_consistent_instrs_append)
next
  case SeqSkip thus ?case by auto
next
  case Cond
  thus ?case
    by (fastforce simp add: simp add: data_dependency_consistent_instrs_append 
      data_dependency_consistent_instrs_issue_expr load_tmps_append
      dest: dom_eval_expr)
next
  case CondTrue thus ?case by auto
next
  case CondFalse thus ?case by auto
next
  case While
  thus ?case by auto
next
  case SGhost thus ?case by auto
next
  case SFence thus ?case by auto
qed



lemma sbh_valid_data_dependency_prog_step: 
  assumes step: "\<theta>\<turnstile>(s,t) \<rightarrow>\<^sub>s ((s',t'),is')"
  assumes store_sops_le: "\<forall>i \<in> \<Union>(fst ` store_sops is). i < t"
  assumes write_sops_le: "\<forall>i \<in> \<Union>(fst ` write_sops sb). i < t"
  assumes valid: "valid_sops_stmt t s"
  shows "data_dependency_consistent_instrs ({i. i < t}) is' \<and> 
         load_tmps is' \<inter> \<Union>(fst ` store_sops is)  = {} \<and>
         load_tmps is' \<inter> \<Union>(fst ` write_sops sb)  = {}"
proof -
  from stmt_step_data_dependency_consistent_instrs [OF step valid] stmt_step_load_tmps_range [OF step]
  store_sops_le write_sops_le
  show ?thesis
    by fastforce
qed

lemma sbh_load_tmps_fresh_prog_step:
  assumes step: "\<theta>\<turnstile>(s,t) \<rightarrow>\<^sub>s ((s',t'),is')"
  assumes tmps_le: "\<forall>i \<in> dom \<theta>. i < t"
  shows "load_tmps is' \<inter> dom \<theta> = {}"
proof -
  from stmt_step_load_tmps_range [OF step] tmps_le
  show ?thesis
    apply auto
    subgoal for x
    apply (drule_tac x=x in bspec )
    apply  assumption
    apply (drule_tac x=x in bspec )
    apply  fastforce
    apply simp
    done
    done
qed

lemma sbh_valid_sops_prog_step:
  assumes step: "\<theta>\<turnstile>(s,t) \<rightarrow>\<^sub>s ((s',t'),is)"
  assumes valid: "valid_sops_stmt t s"
  shows "\<forall>sop\<in>store_sops is. valid_sop sop"
using step valid
proof (induct x=="(s,t)" y=="((s',t'),is)" arbitrary: s t s' t' "is" rule: stmt_step.induct)
  case AssignAddr
  thus ?case by auto
next
  case Assign
  thus ?case
    by (auto simp add: store_sops_append valid_sops_expr_valid_sop)
next
  case CASAddr
  thus ?case by auto
next
  case CASComp
  thus ?case by auto
next
  case CAS
  thus ?case
    by (fastforce simp add: store_sops_append dest: valid_sops_expr_valid_sop)
next
  case Seq
  thus ?case
    by (force intro: valid_sops_stmt_mono )
next
  case SeqSkip thus ?case by simp
next
  case Cond thus ?case
    by auto
next
  case CondTrue thus ?case by auto
next
  case CondFalse thus ?case by auto
next
  case While thus ?case by auto
next
  case SGhost thus ?case by auto
next
  case SFence thus ?case by auto
qed

primrec prog_configs:: "'a memref list \<Rightarrow> 'a set"
where
"prog_configs [] = {}"
|"prog_configs (x#xs) = (case x of 
                         Prog\<^sub>s\<^sub>b p p' is \<Rightarrow> {p,p'} \<union> prog_configs xs
                       | _ \<Rightarrow> prog_configs xs)"

lemma prog_configs_append: "\<And>ys. prog_configs (xs@ys) = prog_configs xs \<union> prog_configs ys"
  by (induct xs) (auto split: memref.splits)

lemma prog_configs_in1: "Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 is \<in> set xs \<Longrightarrow> p\<^sub>1 \<in> prog_configs xs"
  by (induct xs) (auto split: memref.splits)

lemma prog_configs_in2: "Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 is \<in> set xs \<Longrightarrow> p\<^sub>2 \<in> prog_configs xs"
  by (induct xs) (auto split: memref.splits)

lemma prog_configs_mono: "\<And>ys. set xs \<subseteq> set ys \<Longrightarrow> prog_configs xs \<subseteq> prog_configs ys"
  by (induct xs) (auto split: memref.splits simp add: prog_configs_append
  prog_configs_in1 prog_configs_in2)

locale separated_tmps = 
fixes ts
assumes valid_sops_stmt: "\<lbrakk>i < length ts; ts!i = ((s,t),is,\<theta>,sb,\<D>,\<O>)\<rbrakk> 
  \<Longrightarrow> valid_sops_stmt t s"
assumes valid_sops_stmt_sb: "\<lbrakk>i < length ts; ts!i = ((s,t),is,\<theta>,sb,\<D>,\<O>); (s',t') \<in> prog_configs sb\<rbrakk> 
  \<Longrightarrow>  valid_sops_stmt t' s'"
assumes load_tmps_le: "\<lbrakk>i < length ts; ts!i = ((s,t),is,\<theta>,sb,\<D>,\<O>)\<rbrakk> 
  \<Longrightarrow> \<forall>i \<in> load_tmps is. i < t"
assumes read_tmps_le: "\<lbrakk>i < length ts; ts!i = ((s,t),is,\<theta>,sb,\<D>,\<O>)\<rbrakk> 
  \<Longrightarrow> \<forall>i \<in> read_tmps sb. i < t"
assumes store_sops_le: "\<lbrakk>i < length ts; ts!i = ((s,t),is,\<theta>,sb,\<D>,\<O>)\<rbrakk> 
  \<Longrightarrow> \<forall>i \<in> \<Union>(fst ` store_sops is). i < t"
assumes write_sops_le: "\<lbrakk>i < length ts; ts!i = ((s,t),is,\<theta>,sb,\<D>,\<O>)\<rbrakk> 
  \<Longrightarrow> \<forall>i \<in> \<Union>(fst ` write_sops sb). i < t"
assumes tmps_le: "\<lbrakk>i < length ts; ts!i = ((s,t),is,\<theta>,sb,\<D>,\<O>)\<rbrakk> 
  \<Longrightarrow> dom \<theta> \<union> load_tmps is = {i. i < t}"

lemma (in separated_tmps)
  tmps_le': 
  assumes i_bound: "i < length ts" 
  assumes ts_i: "ts!i = ((s,t),is,\<theta>,sb,\<D>,\<O>)"
  shows "\<forall>i \<in> dom \<theta>. i < t"
using tmps_le [OF i_bound ts_i] by auto



lemma (in separated_tmps) separated_tmps_nth_update: 
  "\<lbrakk>i < length ts; valid_sops_stmt t s; \<forall>(s',t') \<in> prog_configs sb. valid_sops_stmt t' s'; 
   \<forall>i \<in> load_tmps is. i < t;\<forall>i \<in> read_tmps sb. i < t;
    \<forall>i \<in> \<Union>(fst ` store_sops is). i < t; \<forall>i \<in> \<Union>(fst ` write_sops sb). i < t; dom \<theta> \<union> load_tmps is = {i. i < t}\<rbrakk> 
   \<Longrightarrow>
   separated_tmps (ts[i:=((s,t),is,\<theta>,sb,\<D>,\<O>)])"
  apply (unfold_locales)
  apply       (force intro: valid_sops_stmt  simp add: nth_list_update split: if_split_asm)
  apply      (fastforce intro: valid_sops_stmt_sb  simp add: nth_list_update split: if_split_asm)
  apply     (fastforce intro: load_tmps_le [rule_format] simp add: nth_list_update split: if_split_asm)
  apply    (fastforce intro: read_tmps_le [rule_format] simp add: nth_list_update split: if_split_asm)
  apply   (fastforce intro: store_sops_le [rule_format] simp add: nth_list_update split: if_split_asm)
  apply  (fastforce intro: write_sops_le [rule_format] simp add: nth_list_update split: if_split_asm)
  apply (fastforce dest: tmps_le [rule_format] simp add: nth_list_update split: if_split_asm)
  done

lemma hd_prog_app_in_first: "\<And>ys. Prog\<^sub>s\<^sub>b p p' is \<in> set xs \<Longrightarrow> hd_prog q (xs @ ys) = hd_prog q xs"
  by (induct xs) (auto split: memref.splits)

lemma hd_prog_app_in_eq: "\<And>ys. Prog\<^sub>s\<^sub>b p p' is \<in> set xs \<Longrightarrow> hd_prog q xs = hd_prog x xs"
  by (induct xs) (auto split: memref.splits)

lemma hd_prog_app_notin_first: "\<And>ys. \<forall>p p' is. Prog\<^sub>s\<^sub>b p p' is \<notin> set xs \<Longrightarrow> hd_prog q (xs @ ys) = hd_prog q ys"
  by (induct xs) (auto split: memref.splits)

lemma union_eq_subsetD: "A \<union> B = C \<Longrightarrow> A \<union> B \<subseteq> C \<and>  C \<subseteq> A \<union> B"
  by auto

lemma prog_step_preserves_separated_tmps:
  assumes i_bound: "i < length ts"  
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>)" 
  assumes prog_step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>s (p', is')"
  assumes sep: "separated_tmps ts"
  shows "separated_tmps 
             (ts [i:=(p',is@is',\<theta>,sb@[Prog\<^sub>s\<^sub>b p p' is'],\<D>,\<O>)])"
proof -
  obtain s t where p: "p=(s,t)" by (cases p)
  obtain s' t' where p': "p'=(s',t')" by (cases p')
  note ts_i = ts_i [simplified p]
  note step = prog_step [simplified p p']
  interpret separated_tmps ts by fact
  have "separated_tmps (ts[i := ((s',t'), is @ is', \<theta>, 
    sb @ [Prog\<^sub>s\<^sub>b (s,t) (s',t') is'], \<D>,\<O>)])"
  proof (rule separated_tmps_nth_update [OF i_bound])
    from stmt_step_load_tmps_range [OF step] load_tmps_le [OF i_bound ts_i]
    stmt_step_tmps_count_mono [OF step]
    show "\<forall>i\<in>load_tmps (is @ is'). i < t'"
      by (auto simp add: load_tmps_append)
  next
    from read_tmps_le [OF i_bound ts_i] stmt_step_tmps_count_mono [OF step]
    show "\<forall>i\<in>read_tmps (sb @ [Prog\<^sub>s\<^sub>b (s, t) (s', t') is']). i < t'"
      by (auto simp add: read_tmps_append)
  next
    from stmt_step_data_store_sops_range [OF step] stmt_step_tmps_count_mono [OF step]
    store_sops_le [OF i_bound ts_i] valid_sops_stmt [OF i_bound ts_i]
    show "\<forall>i\<in>\<Union>(fst ` store_sops (is @ is')). i < t'"
      by (fastforce simp add: store_sops_append)
  next
    from 
      stmt_step_tmps_count_mono [OF step] write_sops_le [OF i_bound ts_i]
    show "\<forall>i\<in>\<Union>(fst ` write_sops (sb @ [Prog\<^sub>s\<^sub>b (s, t) (s', t') is'])). i < t'"
      by (fastforce simp add: write_sops_append)
  next
    from tmps_le [OF i_bound ts_i] 
    have "dom \<theta> \<union> load_tmps is = {i. i < t}" by simp
    with stmt_step_load_tmps_range' [OF step] stmt_step_tmps_count_mono [OF step]
    show "dom \<theta> \<union> load_tmps (is @ is') = {i. i < t'}"
      apply (clarsimp simp add: load_tmps_append)
      apply rule
      apply  (drule union_eq_subsetD)
      apply  fastforce
      apply clarsimp
      subgoal for x
      apply (case_tac "t \<le> x")
      apply  simp
      apply (subgoal_tac "x < t")
      apply  fastforce
      apply fastforce
      done
      done
  next
    from valid_sops_stmt_invariant [OF prog_step [simplified p p'] valid_sops_stmt [OF i_bound ts_i]]
    show "valid_sops_stmt t' s'".
  next
    show "\<forall>(s', t')\<in>prog_configs (sb @ [Prog\<^sub>s\<^sub>b (s, t) (s', t') is']).
             valid_sops_stmt t' s'"
    proof -
      {
	fix s\<^sub>1 t\<^sub>1 
	assume cfgs: "(s\<^sub>1,t\<^sub>1) \<in> prog_configs (sb @ [Prog\<^sub>s\<^sub>b (s, t) (s', t') is'])"
	have "valid_sops_stmt t\<^sub>1 s\<^sub>1"
	proof -
	  from valid_sops_stmt [OF i_bound ts_i]
	  have "valid_sops_stmt t s".
	  moreover
	  from valid_sops_stmt_invariant [OF prog_step [simplified p p'] valid_sops_stmt [OF i_bound ts_i]]
	  have "valid_sops_stmt t' s'".
	  moreover
	  note valid_sops_stmt_sb [OF i_bound ts_i]
	  ultimately
	  show ?thesis
	    using cfgs
	    by (auto simp add: prog_configs_append)
	qed
      }
      thus ?thesis
	by auto
    qed
  qed
  then
  show ?thesis
    by (simp add: p p')
qed

lemma flush_step_sb_subset:
  assumes step: "(m,sb,\<O>) \<rightarrow>\<^sub>f (m', sb',\<O>')"
  shows "set sb' \<subseteq> set sb"
using step
apply (induct c1=="(m,sb,\<O>)" c2=="(m',sb',\<O>')" arbitrary: m sb \<O> acq m' sb' \<O>' acq
  rule: flush_step.induct)
apply auto
done

lemma flush_step_preserves_separated_tmps:
  assumes i_bound: "i < length ts"  
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)" 
  assumes flush_step: "(m,sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m', sb',\<O>',\<R>',\<S>')"
  assumes sep: "separated_tmps ts"
  shows "separated_tmps (ts [i:=(p,is,\<theta>,sb',\<D>,\<O>',\<R>')])"
proof -
  obtain s t where p: "p=(s,t)" by (cases p)
  note ts_i = ts_i [simplified p]
  interpret separated_tmps ts by fact
  have "separated_tmps (ts [i:=((s,t),is,\<theta>,sb',\<D>,\<O>',\<R>')])"
  proof (rule separated_tmps_nth_update [OF i_bound])
    from load_tmps_le [OF i_bound ts_i]
    show "\<forall>i\<in>load_tmps is. i < t".
  next
    from flush_step_preserves_read_tmps [OF flush_step read_tmps_le [OF i_bound ts_i] ]
    show "\<forall>i\<in>read_tmps sb'. i < t".
  next
    from store_sops_le [OF i_bound ts_i]
    show "\<forall>i\<in>\<Union>(fst ` store_sops is). i < t".
  next
    from flush_step_preserves_write_sops [OF flush_step write_sops_le [OF i_bound ts_i]]
    show "\<forall>i\<in>\<Union>(fst ` write_sops sb'). i < t".
  next
    from tmps_le [OF i_bound ts_i] 
    show "dom \<theta> \<union> load_tmps is = {i. i < t}"
      by auto
  next
    from valid_sops_stmt [OF i_bound ts_i]
    show "valid_sops_stmt t s".
  next
    from valid_sops_stmt_sb [OF i_bound ts_i] flush_step_sb_subset [OF flush_step]
    show "\<forall>(s', t')\<in>prog_configs sb'. valid_sops_stmt t' s'"
      by (auto dest!: prog_configs_mono)
  qed
  then
  show ?thesis
    by (simp add: p)
qed

lemma sbh_step_preserves_store_sops_bound:
  assumes step: "(is,\<theta>,sb,m,\<D>,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h (is',\<theta>',sb',m',\<D>',\<O>',\<R>',\<S>')"
  assumes store_sops_le: "\<forall>i\<in>\<Union>(fst ` store_sops is). i < t"
  shows "\<forall>i\<in>\<Union>(fst ` store_sops is'). i < t"
  using step store_sops_le
  by cases auto

lemma sbh_step_preserves_write_sops_bound:
  assumes step: "(is,\<theta>,sb,m,\<D>,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h (is',\<theta>',sb',m',\<D>',\<O>',\<R>',\<S>')"
  assumes store_sops_le: "\<forall>i\<in>\<Union>(fst ` store_sops is). i < t"
  assumes write_sops_le: "\<forall>i\<in>\<Union>(fst ` write_sops sb). i < t"
  shows "\<forall>i\<in>\<Union>(fst ` write_sops sb'). i < t"
  using step store_sops_le write_sops_le
  by cases (auto simp add: write_sops_append)

lemma sbh_step_prog_configs_eq:
  assumes step: "(is,\<theta>,sb,m,\<D>,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h (is',\<theta>',sb',m',\<D>',\<O>',\<R>',\<S>')"
  shows "prog_configs sb' = prog_configs sb"
using step
apply (cases)
apply (auto simp add: prog_configs_append)
done

lemma sbh_step_preserves_tmps_bound':
  assumes step: "(is,\<theta>,sb,m,\<D>,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h (is',\<theta>',sb',m',\<D>',\<O>',\<R>',\<S>')"
  shows "dom \<theta> \<union> load_tmps is = dom \<theta>' \<union> load_tmps is'"
  using step 
  apply cases 
  apply (auto simp add: read_tmps_append)
  done

lemma sbh_step_preserves_separated_tmps:
  assumes i_bound: "i < length ts" 
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)" 
  assumes memop_step: "(is, \<theta>, sb, m,\<D>, \<O>, \<R>,\<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h 
                        (is', \<theta>', sb', m',\<D>', \<O>', \<R>',\<S>')" 
  assumes instr: "separated_tmps ts"
  shows "separated_tmps (ts [i:=(p,is',\<theta>',sb',\<D>',\<O>',\<R>')])"
proof -
  obtain s t where p: "p=(s,t)" by (cases p)
  note ts_i = ts_i [simplified p]
  interpret separated_tmps ts by fact
  have "separated_tmps (ts [i:=((s,t),is',\<theta>',sb',\<D>',\<O>',\<R>')])"
  proof (rule separated_tmps_nth_update [OF i_bound])
    from sbh_step_preserves_load_tmps_bound [OF memop_step load_tmps_le [OF i_bound ts_i]]
    show "\<forall>i\<in>load_tmps is'. i < t".
  next
    from sbh_step_preserves_read_tmps_bound [OF memop_step load_tmps_le [OF i_bound ts_i]
        read_tmps_le [OF i_bound ts_i]]
    show "\<forall>i\<in>read_tmps sb'. i < t".
  next
    from sbh_step_preserves_store_sops_bound [OF memop_step store_sops_le [OF i_bound ts_i]]
    show "\<forall>i\<in>\<Union>(fst ` store_sops is'). i < t".
  next
    from sbh_step_preserves_write_sops_bound [OF memop_step store_sops_le [OF i_bound ts_i] 
      write_sops_le [OF i_bound ts_i]]
    show "\<forall>i\<in>\<Union>(fst ` write_sops sb'). i < t".
  next
    from sbh_step_preserves_tmps_bound' [OF memop_step] tmps_le [OF i_bound ts_i]
    show "dom \<theta>' \<union> load_tmps is' = {i. i < t}"
      by auto
  next
    from valid_sops_stmt [OF i_bound ts_i]
    show "valid_sops_stmt t s".
  next
    from valid_sops_stmt_sb [OF i_bound ts_i] sbh_step_prog_configs_eq [OF memop_step]
    show "\<forall>(s', t')\<in>prog_configs sb'. valid_sops_stmt t' s'"
      by auto
  qed
  then show ?thesis
    by (simp add: p)
qed

definition 
  "valid_pimp ts \<equiv> separated_tmps ts"

lemma prog_step_preserves_valid:
  assumes i_bound: "i < length ts"  
  assumes ts_i: "ts!i = (p,is,\<theta>,sb::stmt_config store_buffer,\<D>,\<O>,\<R>)" 
  assumes prog_step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>s (p', is')"
  assumes valid: "valid_pimp ts"
  shows "valid_pimp (ts [i:=(p',is@is',\<theta>,sb@[Prog\<^sub>s\<^sub>b p p' is'],\<D>,\<O>,\<R>)])"
using prog_step_preserves_separated_tmps [OF i_bound ts_i prog_step] valid
by (auto simp add: valid_pimp_def)

lemma flush_step_preserves_valid:
  assumes i_bound: "i < length ts"  
  assumes ts_i: "ts!i = (p,is,\<theta>,sb::stmt_config store_buffer,\<D>,\<O>,\<R>)" 
  assumes flush_step: "(m,sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m', sb',\<O>',\<R>',\<S>')"
  assumes valid: "valid_pimp ts"
  shows "valid_pimp (ts [i:=(p,is,\<theta>,sb',\<D>,\<O>',\<R>')])"
using flush_step_preserves_separated_tmps [OF i_bound ts_i flush_step] valid
by (auto simp add: valid_pimp_def)

lemma sbh_step_preserves_valid:
  assumes i_bound: "i < length ts" 
  assumes ts_i: "ts!i = (p,is,\<theta>,sb::stmt_config store_buffer,\<D>,\<O>,\<R>)" 
  assumes memop_step: "(is, \<theta>, sb, m,\<D>, \<O>, \<R>,\<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h 
                        (is', \<theta>', sb', m',\<D>', \<O>', \<R>', \<S>')" 
  assumes valid: "valid_pimp ts"
  shows "valid_pimp (ts [i:=(p,is',\<theta>',sb',\<D>',\<O>',\<R>')])"
using 
sbh_step_preserves_separated_tmps [OF i_bound ts_i memop_step] valid
by (auto simp add: valid_pimp_def)

lemma hd_prog_prog_configs: "hd_prog p sb = p \<or> hd_prog p sb \<in> prog_configs sb"
  by (induct sb) (auto split:memref.splits)


interpretation PIMP: xvalid_program_progress stmt_step "\<lambda>(s,t). valid_sops_stmt t s" valid_pimp
proof
  fix \<theta> p p' is'
  assume step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>s (p', is')" 
  obtain s t where p: "p = (s,t)"
    by (cases p)
  obtain s' t' where p': "p' = (s',t')"
    by (cases p')
  from prog_step_progress [OF step [simplified p p']]
  show "p' \<noteq> p \<or> is' \<noteq> []"
    by (simp add: p p')
next
  fix \<theta> p p' is'
  assume step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>s (p', is')" 
    and valid_stmt: "(\<lambda>(s, t). valid_sops_stmt t s) p"
  obtain s t where p: "p = (s,t)"
    by (cases p)
  obtain s' t' where p': "p' = (s',t')"
    by (cases p')
  from valid_sops_stmt_invariant [OF step [simplified p p'] valid_stmt [simplified p, simplified]]
  have "valid_sops_stmt t' s'".
  then show "(\<lambda>(s, t). valid_sops_stmt t s) p'" by (simp add: p')
next
  fix i ts p "is" \<O> \<R> \<D> \<theta> sb
  assume i_bound: "i < length ts" 
    and ts_i: "ts ! i = (p, is, \<theta>, sb::(stmt \<times> nat) memref list, \<D>, \<O>,\<R>)" 
    and valid: "valid_pimp ts"
  from valid have "separated_tmps ts"
    by (simp add: valid_pimp_def)
  then interpret separated_tmps ts .
  obtain s t where p: "p = (s,t)"
    by (cases p)
  from valid_sops_stmt [OF i_bound ts_i [simplified p]]
  show "(\<lambda>(s, t). valid_sops_stmt t s) p"
    by (auto simp add: p)
next
  fix i ts p "is" \<O> \<R> \<D>  \<theta> sb
  assume i_bound: "i < length ts" 
    and ts_i: "ts ! i = (p, is, \<theta>, sb::(stmt \<times> nat) memref list, \<D>, \<O>,\<R>)" 
    and valid: "valid_pimp ts"
  from valid have "separated_tmps ts"
    by (simp add: valid_pimp_def)
  then interpret separated_tmps ts .
  obtain s t where p: "p = (s,t)"
    by (cases p)
  from hd_prog_prog_configs [of p sb] valid_sops_stmt [OF i_bound ts_i [simplified p]]
  valid_sops_stmt_sb [OF i_bound ts_i [simplified p]]
  show "(\<lambda>(s, t). valid_sops_stmt t s) (hd_prog p sb)"
    by (auto simp add: p)
next
  fix i ts p "is" \<O> \<R> \<D> \<theta> sb p' is'
  assume i_bound: "i < length ts" 
    and ts_i: "ts ! i = (p, is, \<theta>, sb, \<D>, \<O>,\<R>)" 
    and step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>s (p', is')"
    and valid: "valid_pimp ts"
  show "distinct_load_tmps is' \<and>
          load_tmps is' \<inter> load_tmps is = {} \<and>
          load_tmps is' \<inter> read_tmps sb = {}"
  proof -
    obtain s t where p: "p=(s,t)" by (cases p)
    obtain s' t' where p': "p'=(s',t')" by (cases p')
    note ts_i = ts_i [simplified p]
    note step = step [simplified p p']
    from valid 
    interpret separated_tmps ts
      by (simp add: valid_pimp_def)
     

    from sbh_step_distinct_load_tmps_prog_step [OF step load_tmps_le [OF i_bound ts_i]
      read_tmps_le [OF i_bound ts_i]]
    show ?thesis .
  qed
next
  fix i ts p "is" \<O> \<R> \<D> \<theta> sb p' is'
  assume i_bound: "i < length ts" 
    and ts_i: "ts ! i = (p, is, \<theta>, sb, \<D>, \<O>,\<R>)" 
    and step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>s (p', is')"
    and valid: "valid_pimp ts"
  show "data_dependency_consistent_instrs (dom \<theta> \<union> load_tmps is) is' \<and>
          load_tmps is' \<inter> \<Union>(fst ` store_sops is) = {} \<and>
          load_tmps is' \<inter> \<Union>(fst ` write_sops sb) = {}"
  proof -
    obtain s t where p: "p=(s,t)" by (cases p)
    obtain s' t' where p': "p'=(s',t')" by (cases p')
    note ts_i = ts_i [simplified p]
    note step = step [simplified p p']
    from valid 
    interpret separated_tmps ts
      by (simp add: valid_pimp_def)

    from sbh_valid_data_dependency_prog_step [OF step store_sops_le [OF i_bound ts_i]
      write_sops_le [OF i_bound ts_i] valid_sops_stmt [OF i_bound ts_i]] tmps_le [OF i_bound ts_i]
    show ?thesis by auto
  qed
next
  fix i ts p "is" \<O> \<R> \<D> \<theta> sb p' is'
  assume i_bound: "i < length ts" 
    and ts_i: "ts ! i = (p, is, \<theta>, sb, \<D>, \<O>,\<R>)" 
    and step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>s (p', is')"
    and valid: "valid_pimp ts"
  show "load_tmps is' \<inter> dom \<theta> = {}"
  proof -
    obtain s t where p: "p=(s,t)" by (cases p)
    obtain s' t' where p': "p'=(s',t')" by (cases p')
    note ts_i = ts_i [simplified p]
    note step = step [simplified p p']
    from valid 
    interpret separated_tmps ts
      by (simp add: valid_pimp_def)  
    from sbh_load_tmps_fresh_prog_step [OF step tmps_le' [OF i_bound ts_i]]
    show ?thesis .
  qed
next
  fix \<theta> p p' "is"
  assume  step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>s (p', is)"
    and valid: "(\<lambda>(s, t). valid_sops_stmt t s) p"
  show  "\<forall>sop\<in>store_sops is. valid_sop sop"
  proof -
    obtain s t where p: "p=(s,t)" by (cases p)
    obtain s' t' where p': "p'=(s',t')" by (cases p')
    note step = step [simplified p p']
    from sbh_valid_sops_prog_step [OF step valid [simplified p,simplified]]
    show ?thesis .
  qed
next
  fix i ts p "is" \<O> \<R> \<D> \<theta> sb p' is'
  assume i_bound: "i < length ts" 
    and ts_i: "ts ! i = (p, is, \<theta>, sb::stmt_config store_buffer, \<D>, \<O>,\<R>)" 
    and step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>s (p', is')"
    and valid: "valid_pimp ts"
  from prog_step_preserves_valid [OF i_bound ts_i step valid]
  show "valid_pimp (ts[i := (p', is @ is', \<theta>, sb @ [Prog\<^sub>s\<^sub>b p p' is'], \<D>, \<O>,\<R>)])" .
next
  fix i ts p "is" \<O> \<R> \<D> \<theta> sb  \<S> m m' sb' \<O>' \<R>' \<S>'
  assume i_bound: "i < length ts" 
    and ts_i: "ts ! i = (p, is, \<theta>, sb::stmt_config store_buffer, \<D>, \<O>,\<R>)" 
    and step: "(m, sb, \<O>, \<R>,\<S>) \<rightarrow>\<^sub>f (m', sb',\<O>',\<R>',\<S>')"
    and valid: "valid_pimp ts"
  thm flush_step_preserves_valid [OF ]
  from flush_step_preserves_valid [OF i_bound ts_i step valid]
  show "valid_pimp (ts[i := (p, is, \<theta>, sb', \<D>, \<O>',\<R>')])" .
next
  fix i ts p "is" \<O> \<R> \<D> \<theta> sb \<S> m is' \<O>' \<R>' \<D>' \<theta>' sb' \<S>' m'
  assume i_bound: "i < length ts" 
    and ts_i: "ts ! i = (p, is, \<theta>, sb::stmt_config store_buffer, \<D>, \<O>,\<R>)"
    and step: "(is, \<theta>, sb, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h 
                  (is', \<theta>', sb', m',\<D>', \<O>', \<R>',\<S>')"
    and valid: "valid_pimp ts"
  from sbh_step_preserves_valid [OF i_bound ts_i step valid]
  show "valid_pimp (ts[i := (p, is', \<theta>', sb', \<D>', \<O>',\<R>')])" .
qed

thm PIMP.concurrent_direct_steps_simulates_store_buffer_history_step
thm PIMP.concurrent_direct_steps_simulates_store_buffer_history_steps
thm PIMP.concurrent_direct_steps_simulates_store_buffer_step

text \<open>We can instantiate PIMP with the various memory models.\<close>

(* FIXME: note I used () instead of sb , because simplifier rewrites sb::unit to sb.
  Make this consistent with interpretations/theorems in ReduceStoreBuffer *)
interpretation direct: 
  computation direct_memop_step empty_storebuffer_step stmt_step "\<lambda>p p' is sb. ()".
interpretation virtual: 
  computation virtual_memop_step empty_storebuffer_step stmt_step "\<lambda>p p' is sb. ()".
interpretation store_buffer:
  computation sb_memop_step store_buffer_step stmt_step "\<lambda>p p' is sb. sb" .
interpretation store_buffer_history:
  computation sbh_memop_step flush_step stmt_step "\<lambda>p p' is sb. sb @ [Prog\<^sub>s\<^sub>b p p' is]".

abbreviation direct_pimp_step:: 
  "(stmt_config,unit,bool,owns,rels,shared) global_config \<Rightarrow> (stmt_config,unit,bool,owns,rels,shared) global_config \<Rightarrow> bool" 
  ("_ \<Rightarrow>\<^sub>d\<^sub>p _" [60,60] 100)
where
"c \<Rightarrow>\<^sub>d\<^sub>p d \<equiv> direct.concurrent_step c d"

abbreviation direct_pimp_steps:: 
  "(stmt_config,unit,bool,owns,rels,shared) global_config \<Rightarrow> (stmt_config,unit,bool,owns,rels,shared) global_config \<Rightarrow> bool" 
  ("_ \<Rightarrow>\<^sub>d\<^sub>p\<^sup>* _" [60,60] 100)
where
"direct_pimp_steps == direct_pimp_step^**"

text \<open>Execution examples\<close>



lemma Assign_Const_ex: 
"([((Assign True (Tmp ({},\<lambda>\<theta>. a)) (Const c) (\<lambda>\<theta>. A) (\<lambda>\<theta>. L) (\<lambda>\<theta>. R) (\<lambda>\<theta>. W),t),[],\<theta>,(),\<D>,\<O>,\<R>)],m,\<S>) \<Rightarrow>\<^sub>d\<^sub>p\<^sup>* 
 ([((Skip,t),[],\<theta>,(),True,\<O> \<union> A - R,Map.empty)],m(a := c),\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
apply (rule converse_rtranclp_into_rtranclp)
apply  (rule direct.Program [where i=0])
apply    simp
apply   simp
apply  (rule Assign)
apply simp
apply (rule converse_rtranclp_into_rtranclp)
apply  (rule direct.Memop [where i=0])
apply    simp
apply   simp
apply  (rule direct_memop_step.WriteVolatile)
apply simp
done

lemma 
" ([((Assign True (Tmp ({},\<lambda>\<theta>. a)) (Binop (+) (Mem True x) (Mem True y)) (\<lambda>\<theta>. A) (\<lambda>\<theta>. L) (\<lambda>\<theta>. R) (\<lambda>\<theta>. W),t),[],\<theta>,(),\<D>,\<O>,\<R>)],m,S) 
 \<Rightarrow>\<^sub>d\<^sub>p\<^sup>* 
 ([((Skip,t + 2),[],\<theta>(t\<mapsto>m x, t + 1 \<mapsto>m y),(),True,\<O> \<union> A - R,Map.empty)],m(a := m x + m y),S  \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
apply (rule converse_rtranclp_into_rtranclp)
apply  (rule direct.Program [where i=0])
apply    simp
apply   simp
apply  (rule Assign)
apply simp

apply (rule converse_rtranclp_into_rtranclp)
apply  (rule direct.Memop)
apply    simp
apply   simp
apply  (rule direct_memop_step.Read )
apply simp

apply (rule converse_rtranclp_into_rtranclp)
apply  (rule direct.Memop)
apply    simp
apply   simp
apply  (rule direct_memop_step.Read)
apply simp

apply (rule converse_rtranclp_into_rtranclp)
apply  (rule direct.Memop)
apply    simp
apply   simp
apply  (rule direct_memop_step.WriteVolatile )
apply simp
done


lemma  
assumes isTrue: "isTrue c"
shows  
"([((Cond (Const c) (Assign True (Tmp ({},\<lambda>\<theta>. a)) (Const c) (\<lambda>\<theta>. A) (\<lambda>\<theta>. L) (\<lambda>\<theta>. R) (\<lambda>\<theta>. W)) Skip,t) ,[],\<theta>,(),\<D>,\<O>,\<R>)],m,\<S>) \<Rightarrow>\<^sub>d\<^sub>p\<^sup>* 
 ([((Skip,t),[],\<theta>,(),True,\<O> \<union> A - R,Map.empty)],m(a := c),\<S>  \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
apply (rule converse_rtranclp_into_rtranclp)
apply  (rule direct.Program [where i=0])
apply    simp
apply   simp
apply  (rule Cond)
apply  simp
apply simp

apply (rule converse_rtranclp_into_rtranclp)
apply  (rule direct.Program [where i=0])
apply    simp
apply   simp
apply  (rule CondTrue)
apply   simp
apply  (simp add: isTrue)
apply simp

apply (rule Assign_Const_ex)
done


end
