(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
section \<open>Annotations, assertions and associated operations\<close>

theory OG_Annotations
imports SmallStep
begin

type_synonym 's assn = "'s set"

datatype ('s, dead 'p, dead 'f) ann =
    AnnExpr "'s assn" 
  | AnnRec "'s assn" "('s, 'p, 'f) ann"
  | AnnWhile "'s assn" "'s assn" "('s, 'p, 'f) ann"
  | AnnComp "('s, 'p, 'f) ann" "('s, 'p, 'f) ann"
  | AnnBin "'s assn" "('s, 'p, 'f) ann" "('s, 'p, 'f) ann"
  | AnnPar "(('s, 'p, 'f) ann \<times> 's assn \<times> 's assn) list"
  | AnnCall "'s assn" nat

type_synonym ('s, 'p, 'f) ann_triple = "('s, 'p, 'f) ann \<times> 's assn \<times> 's assn"

text \<open>
 The list of \<open>ann_triple\<close> is useful if the code calls the same function multiple times
 and require different annotations for the function body each time.
\<close>
type_synonym ('s,'p,'f) proc_assns = "'p \<Rightarrow> (('s, 'p, 'f) ann) list option"

abbreviation  (input) pres:: "('s, 'p, 'f) ann_triple \<Rightarrow> ('s, 'p, 'f) ann"
where "pres a \<equiv> fst a"

abbreviation (input) postcond :: "('s, 'p, 'f) ann_triple \<Rightarrow> 's assn"
where "postcond a \<equiv> fst (snd a)"

abbreviation (input) abrcond :: "('s, 'p, 'f) ann_triple \<Rightarrow> 's assn"
where "abrcond a \<equiv> snd (snd a)"

fun pre :: "('s, 'p, 'f) ann \<Rightarrow> 's assn" where
  "pre (AnnExpr r)      = r"                                                                                               
| "pre (AnnRec r e)     = r"
| "pre (AnnWhile r i e) = r"
| "pre (AnnComp e\<^sub>1 e\<^sub>2)   =  pre e\<^sub>1"
| "pre (AnnBin r e\<^sub>1 e\<^sub>2)  = r"
| "pre (AnnPar as)      = \<Inter> (pre ` set (map pres (as)))"
| "pre (AnnCall r n)    = r"

fun pre_par :: "('s, 'p, 'f) ann \<Rightarrow> bool" where
  "pre_par (AnnComp e\<^sub>1 e\<^sub>2) =  pre_par e\<^sub>1"
| "pre_par (AnnPar as)  = True"
| "pre_par _    = False"

fun pre_set :: "('s, 'p, 'f) ann \<Rightarrow> ('s assn) set" where
  "pre_set (AnnExpr r)      = {r}"
| "pre_set (AnnRec r e)     = {r}"
| "pre_set (AnnWhile r i e) = {r}"
| "pre_set (AnnComp e\<^sub>1 e\<^sub>2)   =  pre_set e\<^sub>1"
| "pre_set (AnnBin r e\<^sub>1 e\<^sub>2)  = {r}"
| "pre_set (AnnPar as)       = \<Union> (pre_set ` set (map pres (as)))"
(*| "pre_set (AnnPar e\<^sub>1 e\<^sub>2)    = pre_set (pres e\<^sub>1) \<union> pre_set (pres e\<^sub>2)" *)
| "pre_set (AnnCall r n)    = {r}"

lemma fst_BNFs[simp]:
  "a \<in> Basic_BNFs.fsts (a,b)"
   using fsts.intros by auto

lemma "\<not>pre_par c  \<Longrightarrow> pre c \<in> pre_set c"
  by (induct c; simp)

lemma pre_set:
  "pre c = \<Inter> (pre_set c)"
  by (induct c; fastforce)

lemma pre_imp_pre_set:
  "s \<in> pre c \<Longrightarrow> a \<in> pre_set c \<Longrightarrow> s \<in> a"
  by (simp add: pre_set)

abbreviation precond :: "('s, 'p, 'f) ann_triple \<Rightarrow> 's assn"
where "precond a \<equiv> pre (fst a)"

fun strengthen_pre :: "('s, 'p, 'f) ann \<Rightarrow> 's assn \<Rightarrow> ('s, 'p, 'f) ann" where
  "strengthen_pre (AnnExpr r)      r' = AnnExpr (r \<inter> r')"                                                                                               
| "strengthen_pre (AnnRec r e)     r' = AnnRec (r \<inter> r') e"
| "strengthen_pre (AnnWhile r i e) r' = AnnWhile (r \<inter> r') i e"
| "strengthen_pre (AnnComp e\<^sub>1 e\<^sub>2)   r' = AnnComp (strengthen_pre e\<^sub>1 r') e\<^sub>2"
| "strengthen_pre (AnnBin r e\<^sub>1 e\<^sub>2) r' = AnnBin (r \<inter> r') e\<^sub>1 e\<^sub>2"
| "strengthen_pre (AnnPar as)    r' = (AnnPar as)"
| "strengthen_pre (AnnCall r n)    r' = AnnCall (r \<inter> r') n"

fun weaken_pre :: "('s, 'p, 'f) ann \<Rightarrow> 's assn \<Rightarrow> ('s, 'p, 'f) ann" where
  "weaken_pre (AnnExpr r)      r' = AnnExpr (r \<union> r')"                                                                                               
| "weaken_pre (AnnRec r e)     r' = AnnRec (r \<union> r') e"
| "weaken_pre (AnnWhile r i e) r' = AnnWhile (r \<union> r') i e"
| "weaken_pre (AnnComp e\<^sub>1 e\<^sub>2)   r' = AnnComp (weaken_pre e\<^sub>1 r') e\<^sub>2"
| "weaken_pre (AnnBin r e\<^sub>1 e\<^sub>2) r' = AnnBin (r \<union> r') e\<^sub>1 e\<^sub>2"
| "weaken_pre (AnnPar as)   r' = AnnPar as"
| "weaken_pre (AnnCall r n)    r' = AnnCall (r \<union> r') n"

lemma weaken_pre_empty[simp]:
  "weaken_pre r {} = r"
  by (induct r) auto

text \<open>Annotations for call definition (see Language.thy)\<close>
definition
 ann_call :: "'s assn \<Rightarrow> 's assn \<Rightarrow> nat \<Rightarrow>  's assn \<Rightarrow>'s assn \<Rightarrow>  's assn \<Rightarrow> 's assn \<Rightarrow> ('s,'p,'f) ann"
where
 "ann_call init r n restoreq return restorea A \<equiv> 
  AnnRec init (AnnComp (AnnComp (AnnComp (AnnExpr init) (AnnCall r n)) (AnnComp (AnnExpr restorea) (AnnExpr A)))
          (AnnRec restoreq (AnnComp (AnnExpr restoreq) (AnnExpr return))))"


inductive ann_matches :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) proc_assns \<Rightarrow> ('s, 'p, 'f) ann \<Rightarrow> ('s, 'p, 'f) com \<Rightarrow> bool" where
  ann_skip: "ann_matches \<Gamma> \<Theta> (AnnExpr a) Skip"
| ann_basic: "ann_matches \<Gamma> \<Theta> (AnnExpr a) (Basic f)"
| ann_spec: "ann_matches \<Gamma> \<Theta> (AnnExpr a) (Spec r)"
| ann_throw: "ann_matches \<Gamma> \<Theta> (AnnExpr a) (Throw)"
| ann_await: "ann_matches \<Gamma> \<Theta> a e \<Longrightarrow>
               ann_matches \<Gamma> \<Theta> (AnnRec r a) (Await b e)"
| ann_seq: "\<lbrakk> ann_matches \<Gamma> \<Theta> a1 p1; ann_matches \<Gamma> \<Theta> a2 p2 \<rbrakk> \<Longrightarrow>
               ann_matches \<Gamma> \<Theta> (AnnComp a1 a2) (Seq p1 p2)"
| ann_cond: "\<lbrakk> ann_matches \<Gamma> \<Theta> a1 c1; ann_matches \<Gamma> \<Theta> a2 c2 \<rbrakk> \<Longrightarrow>
               ann_matches \<Gamma> \<Theta> (AnnBin a a1 a2) (Cond b c1 c2)"
| ann_catch: "\<lbrakk> ann_matches \<Gamma> \<Theta> a1 c1; ann_matches \<Gamma> \<Theta> a2 c2 \<rbrakk> \<Longrightarrow>
                ann_matches \<Gamma> \<Theta> (AnnComp a1 a2) (Catch c1 c2)"
| ann_while: "ann_matches \<Gamma> \<Theta> a' e \<Longrightarrow>
                ann_matches \<Gamma> \<Theta> (AnnWhile a i a') (While b e)"
| ann_guard: "\<lbrakk> ann_matches \<Gamma> \<Theta> a' e \<rbrakk> \<Longrightarrow> 
                ann_matches \<Gamma> \<Theta> (AnnRec a a') (Guard f b e)"
| ann_call: "\<lbrakk> \<Theta> f = Some as; \<Gamma> f = Some b; n < length as;
               ann_matches \<Gamma> \<Theta> (as!n) b\<rbrakk> \<Longrightarrow>
   ann_matches \<Gamma> \<Theta> (AnnCall a n) (Call f)"
| ann_dyncom: "\<forall>s\<in>r. ann_matches \<Gamma> \<Theta> a (c s) \<Longrightarrow>
               ann_matches \<Gamma> \<Theta> (AnnRec r a) (DynCom c)"
| ann_parallel: "\<lbrakk> length as = length cs;
                   \<forall>i<length cs. ann_matches \<Gamma> \<Theta> (pres (as!i)) (cs!i) \<rbrakk> \<Longrightarrow>
   ann_matches \<Gamma> \<Theta> (AnnPar as) (Parallel cs)"

primrec ann_guards:: "'s assn \<Rightarrow> ('f \<times> 's bexp ) list \<Rightarrow>
                  ('s,'p,'f) ann \<Rightarrow> ('s,'p,'f) ann"
where
  "ann_guards _ [] c = c" |
  "ann_guards r (g#gs) c = AnnRec r (ann_guards (r \<inter> snd g) gs c)"

end
