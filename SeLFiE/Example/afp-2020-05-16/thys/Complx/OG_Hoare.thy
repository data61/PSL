(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
section \<open> Owicki-Gries for Partial Correctness \<close>
theory OG_Hoare
imports OG_Annotations 
begin

subsection \<open>Validity of Hoare Tuples: \<open>\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A\<close>\<close>

definition
  valid :: "[('s,'p,'f) body,'f set,'s assn,('s,'p,'f) com,'s assn,'s assn] => bool"
                ("_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ _ _, _"  [61,60,1000, 20, 1000,1000] 60)
where
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P c Q,A \<equiv> \<forall>s t c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c', t) \<longrightarrow> final (c', t ) \<longrightarrow> s \<in> Normal ` P \<longrightarrow> t \<notin> Fault ` F  
                      \<longrightarrow>  c' = Skip \<and> t \<in> Normal ` Q \<or> c' = Throw \<and> t \<in> Normal ` A"

subsection \<open>Interference Freedom\<close>

inductive
 atomicsR :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) proc_assns \<Rightarrow> ('s, 'p, 'f) ann \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s assn \<times> ('s, 'p, 'f) com) \<Rightarrow> bool"
  for \<Gamma>::"('s,'p,'f) body"
  and \<Theta> :: " ('s,'p,'f) proc_assns"
where
  AtBasic: "atomicsR \<Gamma> \<Theta> (AnnExpr p) (Basic f) (p, Basic f)"
| AtSpec: "atomicsR \<Gamma> \<Theta> (AnnExpr p) (Spec r) (p, Spec r)"
| AtAwait: "atomicsR \<Gamma> \<Theta> (AnnRec r ae) (Await b e) (r \<inter> b, Await b e)"
| AtWhileExpr: "atomicsR \<Gamma> \<Theta> p e a \<Longrightarrow> atomicsR \<Gamma> \<Theta> (AnnWhile r i p) (While b e) a"
| AtGuardExpr: "atomicsR \<Gamma> \<Theta> p e a \<Longrightarrow> atomicsR \<Gamma> \<Theta> (AnnRec r p) (Guard f b e) a" 
| AtDynCom: "x \<in> r \<Longrightarrow> atomicsR \<Gamma> \<Theta> ad (f x) a \<Longrightarrow> atomicsR \<Gamma> \<Theta> (AnnRec r ad) (DynCom f) a" 
| AtCallExpr: "\<Gamma> f = Some b \<Longrightarrow> \<Theta> f = Some as \<Longrightarrow>
                n < length as \<Longrightarrow>
                atomicsR \<Gamma> \<Theta>  (as!n) b a \<Longrightarrow>
               atomicsR \<Gamma> \<Theta> (AnnCall r n) (Call f) a"
| AtSeqExpr1: "atomicsR \<Gamma> \<Theta>  a1 c1 a \<Longrightarrow>
               atomicsR \<Gamma> \<Theta> (AnnComp a1 a2) (Seq c1 c2) a" 
| AtSeqExpr2: "atomicsR \<Gamma> \<Theta>  a2 c2 a \<Longrightarrow>
               atomicsR \<Gamma> \<Theta> (AnnComp a1 a2) (Seq c1 c2) a" 
| AtCondExpr1: "atomicsR \<Gamma> \<Theta>  a1 c1 a \<Longrightarrow>
               atomicsR \<Gamma> \<Theta> (AnnBin r a1 a2) (Cond b c1 c2) a" 
| AtCondExpr2: "atomicsR \<Gamma> \<Theta>  a2 c2 a \<Longrightarrow>
               atomicsR \<Gamma> \<Theta> (AnnBin r a1 a2) (Cond b c1 c2) a" 
| AtCatchExpr1: "atomicsR \<Gamma> \<Theta>  a1 c1 a \<Longrightarrow>
               atomicsR \<Gamma> \<Theta> (AnnComp a1 a2) (Catch c1 c2) a" 
| AtCatchExpr2: "atomicsR \<Gamma> \<Theta>  a2 c2 a \<Longrightarrow>
               atomicsR \<Gamma> \<Theta> (AnnComp a1 a2) (Catch c1 c2) a" 
| AtParallelExprs: "i < length cs \<Longrightarrow> atomicsR \<Gamma> \<Theta> (fst (as!i)) (cs!i) a \<Longrightarrow>
    atomicsR \<Gamma> \<Theta> (AnnPar as) (Parallel cs) a"

lemma atomicsR_Skip[simp]:
  "atomicsR \<Gamma> \<Theta> a Skip r = False"
 by (auto elim: atomicsR.cases)

lemma atomicsR_Throw[simp]:
  "atomicsR \<Gamma> \<Theta> a Throw r = False"
 by (auto elim: atomicsR.cases)

inductive
 assertionsR :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) proc_assns \<Rightarrow> 's assn \<Rightarrow> 's assn \<Rightarrow> ('s, 'p, 'f) ann \<Rightarrow> ('s,'p,'f) com \<Rightarrow> 's assn \<Rightarrow> bool"
  for \<Gamma>::"('s,'p,'f) body"
  and \<Theta> :: " ('s,'p,'f) proc_assns"
where
  AsSkip: "assertionsR \<Gamma> \<Theta> Q A (AnnExpr p) Skip p"
| AsThrow: "assertionsR \<Gamma> \<Theta> Q A (AnnExpr p) Throw p"
| AsBasic: "assertionsR \<Gamma> \<Theta> Q A (AnnExpr p) (Basic f) p"
| AsBasicSkip: "assertionsR \<Gamma> \<Theta> Q A (AnnExpr p) (Basic f) Q"
| AsSpec: "assertionsR \<Gamma> \<Theta> Q A (AnnExpr p) (Spec r) p"
| AsSpecSkip: "assertionsR \<Gamma> \<Theta> Q A (AnnExpr p) (Spec r) Q"
| AsAwaitSkip: "assertionsR \<Gamma> \<Theta> Q A (AnnRec r ae) (Await b e) Q"
| AsAwaitThrow: "assertionsR \<Gamma> \<Theta> Q A (AnnRec r ae) (Await b e) A"
| AsAwait: "assertionsR \<Gamma> \<Theta> Q A (AnnRec r ae) (Await b e) r"
| AsWhileExpr: "assertionsR \<Gamma> \<Theta> i A p e a \<Longrightarrow> assertionsR \<Gamma> \<Theta> Q A (AnnWhile r i p) (While b e) a" 
| AsWhileAs: "assertionsR \<Gamma> \<Theta> Q A (AnnWhile r i p) (While b e) r"
| AsWhileInv: "assertionsR \<Gamma> \<Theta> Q A (AnnWhile r i p) (While b e) i"
| AsWhileSkip: "assertionsR \<Gamma> \<Theta> Q A (AnnWhile r i p) (While b e) Q"
| AsGuardExpr: "assertionsR \<Gamma> \<Theta> Q A p e a \<Longrightarrow> assertionsR \<Gamma> \<Theta> Q A (AnnRec r p) (Guard f b e) a" 
| AsGuardAs: "assertionsR \<Gamma> \<Theta> Q A (AnnRec r p) (Guard f b e) r" 
| AsDynComExpr: "x \<in> r \<Longrightarrow> assertionsR \<Gamma> \<Theta> Q A ad (f x) a \<Longrightarrow> assertionsR \<Gamma> \<Theta> Q A (AnnRec r ad) (DynCom f) a" 
| AsDynComAs: "assertionsR \<Gamma> \<Theta> Q A (AnnRec r p) (DynCom f) r" 
| AsCallAs: "assertionsR \<Gamma> \<Theta> Q A (AnnCall r n) (Call f) r" 
| AsCallExpr: "\<Gamma> f = Some b \<Longrightarrow> \<Theta> f = Some as \<Longrightarrow>
                n < length as \<Longrightarrow>
                assertionsR \<Gamma> \<Theta> Q A (as!n) b a \<Longrightarrow>
               assertionsR \<Gamma> \<Theta> Q A (AnnCall r n) (Call f) a" 
| AsSeqExpr1: "assertionsR \<Gamma> \<Theta> (pre a2) A a1 c1 a \<Longrightarrow>
               assertionsR \<Gamma> \<Theta> Q A (AnnComp a1 a2) (Seq c1 c2) a" 
| AsSeqExpr2: "assertionsR \<Gamma> \<Theta> Q A a2 c2 a \<Longrightarrow>
               assertionsR \<Gamma> \<Theta> Q A (AnnComp a1 a2) (Seq c1 c2) a" 
| AsCondExpr1: "assertionsR \<Gamma> \<Theta> Q A a1 c1 a \<Longrightarrow>
               assertionsR \<Gamma> \<Theta> Q A (AnnBin r a1 a2) (Cond b c1 c2) a" 
| AsCondExpr2: "assertionsR \<Gamma> \<Theta> Q A a2 c2 a \<Longrightarrow>
               assertionsR \<Gamma> \<Theta> Q A (AnnBin r a1 a2) (Cond b c1 c2) a" 
| AsCondAs: "assertionsR \<Gamma> \<Theta> Q A (AnnBin r a1 a2) (Cond b c1 c2) r" 
| AsCatchExpr1: "assertionsR \<Gamma> \<Theta> Q (pre a2) a1 c1 a \<Longrightarrow>
               assertionsR \<Gamma> \<Theta> Q A (AnnComp a1 a2) (Catch c1 c2) a" 
| AsCatchExpr2: "assertionsR \<Gamma> \<Theta> Q A a2 c2 a \<Longrightarrow>
               assertionsR \<Gamma> \<Theta> Q A (AnnComp a1 a2) (Catch c1 c2) a" 

| AsParallelExprs: "i < length cs \<Longrightarrow> assertionsR \<Gamma> \<Theta> (postcond (as!i)) (abrcond (as!i)) (pres (as!i)) (cs!i) a \<Longrightarrow>
    assertionsR \<Gamma> \<Theta> Q A (AnnPar as) (Parallel cs) a" 
| AsParallelSkips: "Qs = \<Inter> (set (map postcond as)) \<Longrightarrow>
  assertionsR \<Gamma> \<Theta> Q A (AnnPar as) (Parallel cs) (Qs)" 

definition
  interfree_aux :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) proc_assns \<Rightarrow> 'f set \<Rightarrow> (('s,'p,'f) com \<times> ('s, 'p, 'f) ann_triple \<times> ('s,'p,'f) com \<times> ('s, 'p, 'f) ann) \<Rightarrow> bool"
where
  "interfree_aux \<Gamma> \<Theta> F \<equiv> \<lambda>(c\<^sub>1, (P\<^sub>1, Q\<^sub>1, A\<^sub>1), c\<^sub>2, P\<^sub>2).
                              (\<forall>p c .atomicsR \<Gamma> \<Theta> P\<^sub>2 c\<^sub>2 (p,c) \<longrightarrow> 
                               \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> (Q\<^sub>1 \<inter> p) c Q\<^sub>1,Q\<^sub>1  \<and> \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> (A\<^sub>1 \<inter> p) c A\<^sub>1,A\<^sub>1  \<and>
                                (\<forall>a. assertionsR \<Gamma> \<Theta> Q\<^sub>1 A\<^sub>1 P\<^sub>1 c\<^sub>1 a \<longrightarrow> \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> (a \<inter> p) c a,a))"

definition
  interfree :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) proc_assns \<Rightarrow> 'f set \<Rightarrow> (('s, 'p, 'f) ann_triple) list \<Rightarrow> ('s,'p,'f) com list  \<Rightarrow> bool"
where 
  "interfree \<Gamma> \<Theta> F Ps Ts \<equiv> \<forall>i j. i < length Ts \<and> j < length Ts \<and> i \<noteq> j \<longrightarrow> 
                         interfree_aux \<Gamma> \<Theta> F (Ts!i, Ps!i, Ts!j, fst (Ps!j))"

subsection \<open>The Owicki-Gries Logic for COMPLX\<close>

inductive
  oghoare :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) proc_assns \<Rightarrow> 'f set
              \<Rightarrow> ('s, 'p, 'f) ann \<Rightarrow> ('s,'p,'f) com \<Rightarrow> 's assn \<Rightarrow> 's assn \<Rightarrow> bool"
    ("(4_, _/ \<turnstile>\<^bsub>'/_\<^esub> (_/ (_)/ _, _))" [60,60,60,1000,1000,1000,1000]60)
and
  oghoare_seq :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) proc_assns \<Rightarrow> 'f set
              \<Rightarrow> 's assn \<Rightarrow> ('s, 'p, 'f) ann \<Rightarrow> ('s,'p,'f) com \<Rightarrow> 's assn \<Rightarrow> 's assn \<Rightarrow> bool"
    ("(4_, _/ \<tturnstile>\<^bsub>'/_\<^esub> (_/ _/ (_)/ _, _))" [60,60,60,1000,1000,1000,1000]60)

where
 Skip: " \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnExpr Q) Skip Q,A"

| Throw: "\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnExpr A) Throw Q,A"

| Basic: "\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnExpr {s. f s \<in> Q}) (Basic f) Q,A"

| Spec: "\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnExpr {s. (\<forall>t. (s,t) \<in> rel \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s,t) \<in> rel)}) (Spec rel) Q,A"

| Seq: "\<lbrakk>\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>1 c\<^sub>1 (pre P\<^sub>2),A;
         \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>2 c\<^sub>2 Q,A \<rbrakk>
         \<Longrightarrow> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnComp P\<^sub>1 P\<^sub>2) (Seq c\<^sub>1 c\<^sub>2) Q,A"

| Catch: "\<lbrakk>\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>1 c\<^sub>1 Q,(pre P\<^sub>2);
           \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>2 c\<^sub>2 Q,A \<rbrakk> 
      \<Longrightarrow>  \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnComp P\<^sub>1 P\<^sub>2) (Catch c\<^sub>1 c\<^sub>2) Q,A"
  
| Cond: "\<lbrakk> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>1 c\<^sub>1 Q,A;
           \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P\<^sub>2 c\<^sub>2 Q,A;
          r \<inter> b \<subseteq> pre P\<^sub>1;
          r \<inter> -b \<subseteq> pre P\<^sub>2 \<rbrakk>
         \<Longrightarrow> 
         \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnBin r P\<^sub>1 P\<^sub>2) (Cond b c\<^sub>1 c\<^sub>2) Q,A"

| While: "\<lbrakk> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P c i,A;
            i \<inter> b \<subseteq> pre P;
            i \<inter> -b \<subseteq> Q;
            r \<subseteq> i  \<rbrakk>
          \<Longrightarrow>
          \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnWhile r i P) (While b c) Q,A"

| Guard: "\<lbrakk> \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> P c Q,A;
            r \<inter> g \<subseteq> pre P;
            r \<inter> -g \<noteq> {} \<longrightarrow> f \<in> F\<rbrakk> \<Longrightarrow>
          \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnRec r P) (Guard f g c) Q,A"

| Call: "\<lbrakk>  \<Theta> p = Some as;
          (as ! n) = P;
          r \<subseteq> pre P;
          \<Gamma> p = Some b;
          n < length as;
          \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P b Q,A
          \<rbrakk> 
         \<Longrightarrow> 
         \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnCall r n) (Call p) Q,A"

| DynCom:
      "r \<subseteq> pre a \<Longrightarrow> \<forall>s\<in>r. \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> a (c s) Q,A 
      \<Longrightarrow> 
      \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnRec r a) (DynCom c) Q,A"

| Await: "\<lbrakk>\<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub>(r \<inter> b) P c Q,A; atom_com c \<rbrakk> \<Longrightarrow>
  \<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (AnnRec r P) (Await b c) Q,A"

| Parallel: "\<lbrakk> length as = length cs;
               \<forall>i < length cs. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub>(pres (as!i)) (cs!i) (postcond (as!i)),(abrcond (as!i));
               interfree \<Gamma> \<Theta> F as cs;
               \<Inter> (set (map postcond as)) \<subseteq> Q;
               \<Union> (set (map abrcond as)) \<subseteq> A
              \<rbrakk>
        \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (AnnPar as) (Parallel cs) Q,A"

| Conseq: "\<exists>P' Q' A'. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (weaken_pre P P') c Q',A' \<and> Q' \<subseteq> Q \<and> A' \<subseteq> A 
           \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"

| SeqSkip:   "\<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> Q (AnnExpr x) Skip Q,A"

| SeqThrow:   "\<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> A (AnnExpr x) Throw Q,A"

| SeqBasic:   "\<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> {s. f s \<in> Q} (AnnExpr x) (Basic f) Q,A"

| SeqSpec:   "\<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> {s. (\<forall>t. (s,t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s,t) \<in> r)} (AnnExpr x) (Spec r) Q,A"

| SeqSeq:    "\<lbrakk> \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> R P\<^sub>2 c\<^sub>2 Q,A ; \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P P\<^sub>1 c\<^sub>1 R,A\<rbrakk>
         \<Longrightarrow> \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P (AnnComp P\<^sub>1 P\<^sub>2) (Seq c\<^sub>1 c\<^sub>2) Q,A"

| SeqCatch:  "\<lbrakk>\<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> R P\<^sub>2 c2 Q,A ; \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P P\<^sub>1 c1 Q,R \<rbrakk> \<Longrightarrow>
    \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P (AnnComp P\<^sub>1 P\<^sub>2) (Catch c1 c2) Q,A"

| SeqCond: "\<lbrakk> \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> (P \<inter> b) P\<^sub>1 c\<^sub>1 Q,A;
           \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> (P \<inter> -b) P\<^sub>2 c\<^sub>2 Q,A \<rbrakk>
         \<Longrightarrow> 
         \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P (AnnBin r P\<^sub>1 P\<^sub>2) (Cond b c\<^sub>1 c\<^sub>2) Q,A"

| SeqWhile: "\<lbrakk> \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> (P\<inter>b) a c P,A \<rbrakk>
          \<Longrightarrow>
          \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P (AnnWhile r i a) (While b c) (P \<inter> -b),A"

| SeqGuard: "\<lbrakk> \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> (P\<inter>g) a c Q,A;
            P \<inter> -g \<noteq> {} \<Longrightarrow> f \<in> F\<rbrakk> \<Longrightarrow>
          \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P (AnnRec r a) (Guard f g c) Q,A"

| SeqCall: "\<lbrakk>  \<Theta> p = Some as;
          (as ! n) = P'';
          \<Gamma> p = Some b;
          n < length as;
          \<Gamma>,\<Theta> \<tturnstile>\<^bsub>/F\<^esub> P P'' b Q,A
          \<rbrakk> 
         \<Longrightarrow> 
         \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P (AnnCall r n) (Call p) Q,A"

| SeqDynCom:
      "r \<subseteq> pre a \<Longrightarrow>
      \<forall>s\<in>r. \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub>P a (c s) Q,A \<Longrightarrow>
      P\<subseteq>r
      \<Longrightarrow> 
      \<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P (AnnRec r a) (DynCom c) Q,A"

| SeqConseq: "\<lbrakk> P \<subseteq> P'; \<Gamma>,\<Theta>\<tturnstile>\<^bsub>/F\<^esub> P' a c Q',A'; Q' \<subseteq> Q; A' \<subseteq> A \<rbrakk>
           \<Longrightarrow> \<Gamma>,\<Theta>\<tturnstile>\<^bsub>/F\<^esub> P a c Q,A"

| SeqParallel: "P \<subseteq> pre (AnnPar as) \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (AnnPar as) (Parallel cs) Q,A
  \<Longrightarrow> \<Gamma>,\<Theta>\<tturnstile>\<^bsub>/F\<^esub> P (AnnPar as) (Parallel cs) Q,A"

lemmas oghoare_intros = "oghoare_oghoare_seq.intros"

lemmas oghoare_inducts = oghoare_oghoare_seq.inducts

lemmas oghoare_induct = oghoare_oghoare_seq.inducts(1)

lemmas oghoare_seq_induct = oghoare_oghoare_seq.inducts(2)

end
