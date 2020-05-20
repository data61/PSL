(*
Title: SIFUM-Type-Systems
Authors: Sylvia Grewe, Heiko Mantel, Daniel Schoepe
*)
section \<open>Type System for Ensuring SIFUM-Security of Commands\<close>

theory TypeSystem
imports Main Preliminaries Security Language Compositionality
begin

subsection \<open>Typing Rules\<close>

type_synonym Type = Sec

type_synonym 'Var TyEnv = "'Var \<rightharpoonup> Type"

(* We introduce a locale that instantiates the SIFUM-security property
  for the language from SIFUM_Lang.thy *)
locale sifum_types =
  sifum_lang ev\<^sub>A ev\<^sub>B + sifum_security dma Stop eval\<^sub>w
  for ev\<^sub>A :: "('Var, 'Val) Mem \<Rightarrow> 'AExp \<Rightarrow> 'Val"
  and ev\<^sub>B :: "('Var, 'Val) Mem \<Rightarrow> 'BExp \<Rightarrow> bool"

context sifum_types
begin

(* Redefined since Isabelle does not seem to be able to reuse the abbreviation from the old locale *)
abbreviation mm_equiv_abv2 :: "(_, _, _) LocalConf \<Rightarrow> (_, _, _) LocalConf \<Rightarrow> bool"
(infix "\<approx>" 60)
  where "mm_equiv_abv2 c c' \<equiv> mm_equiv_abv c c'"

abbreviation eval_abv2 :: "(_, 'Var, 'Val) LocalConf \<Rightarrow> (_, _, _) LocalConf \<Rightarrow> bool"
  (infixl "\<leadsto>" 70)
  where
  "x \<leadsto> y \<equiv> (x, y) \<in> eval\<^sub>w"

abbreviation low_indistinguishable_abv :: "'Var Mds \<Rightarrow> ('Var, 'AExp, 'BExp) Stmt \<Rightarrow> (_, _, _) Stmt \<Rightarrow> bool"
  ("_ \<sim>\<index> _" [100, 100] 80)
  where
  "c \<sim>\<^bsub>mds\<^esub> c' \<equiv> low_indistinguishable mds c c'"


definition to_total :: "'Var TyEnv \<Rightarrow> 'Var \<Rightarrow> Sec"
where "to_total \<Gamma> v \<equiv> if v \<in> dom \<Gamma> then the (\<Gamma> v) else dma v"

definition max_dom :: "Sec set \<Rightarrow> Sec"
  where "max_dom xs \<equiv> if High \<in> xs then High else Low"

inductive type_aexpr :: "'Var TyEnv \<Rightarrow> 'AExp \<Rightarrow> Type \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ \<in> _" [120, 120, 120] 1000)
  where
  type_aexpr [intro!]: "\<Gamma> \<turnstile>\<^sub>a e \<in> max_dom (image (\<lambda> x. to_total \<Gamma> x) (aexp_vars e))"

inductive_cases type_aexpr_elim [elim]: "\<Gamma> \<turnstile>\<^sub>a e \<in> t"

inductive type_bexpr :: "'Var TyEnv \<Rightarrow> 'BExp \<Rightarrow> Type \<Rightarrow> bool" ("_ \<turnstile>\<^sub>b _ \<in> _ " [120, 120, 120] 1000)
  where
  type_bexpr [intro!]: "\<Gamma> \<turnstile>\<^sub>b e \<in> max_dom (image (\<lambda> x. to_total \<Gamma> x) (bexp_vars e))"

inductive_cases type_bexpr_elim [elim]: "\<Gamma> \<turnstile>\<^sub>b e \<in> t"

definition mds_consistent :: "'Var Mds \<Rightarrow> 'Var TyEnv \<Rightarrow> bool"
  where "mds_consistent mds \<Gamma> \<equiv>
    dom \<Gamma> = {(x :: 'Var). (dma x = Low \<and> x \<in> mds AsmNoRead) \<or>
                          (dma x = High \<and> x \<in> mds AsmNoWrite)}"

fun add_anno_dom :: "'Var TyEnv \<Rightarrow> 'Var ModeUpd \<Rightarrow> 'Var set"
  where
  "add_anno_dom \<Gamma> (Acq v AsmNoRead) = (if dma v = Low then dom \<Gamma> \<union> {v} else dom \<Gamma>)" |
  "add_anno_dom \<Gamma> (Acq v AsmNoWrite) = (if dma v = High then dom \<Gamma> \<union> {v} else dom \<Gamma>)" |
  "add_anno_dom \<Gamma> (Acq v _) = dom \<Gamma>" |
  "add_anno_dom \<Gamma> (Rel v AsmNoRead) = (if dma v = Low then dom \<Gamma> - {v} else dom \<Gamma>)" |
  "add_anno_dom \<Gamma> (Rel v AsmNoWrite) = (if dma v = High then dom \<Gamma> - {v} else dom \<Gamma>)" |
  "add_anno_dom \<Gamma> (Rel v _) = dom \<Gamma>"

definition add_anno :: "'Var TyEnv \<Rightarrow> 'Var ModeUpd \<Rightarrow> 'Var TyEnv" (infix "\<oplus>" 60)
  where
  "\<Gamma> \<oplus> upd = ((\<lambda>x. Some (to_total \<Gamma> x)) |` add_anno_dom \<Gamma> upd)"

definition context_le :: "'Var TyEnv \<Rightarrow> 'Var TyEnv \<Rightarrow> bool" (infixr "\<sqsubseteq>\<^sub>c" 100)
  where
  "\<Gamma> \<sqsubseteq>\<^sub>c \<Gamma>' \<equiv> (dom \<Gamma> = dom \<Gamma>') \<and> (\<forall> x \<in> dom \<Gamma>. the (\<Gamma> x) \<sqsubseteq> the (\<Gamma>' x))"

inductive has_type :: "'Var TyEnv \<Rightarrow> ('Var, 'AExp, 'BExp) Stmt \<Rightarrow> 'Var TyEnv \<Rightarrow> bool"
  ("\<turnstile> _ {_} _" [120, 120, 120] 1000)
  where
  stop_type [intro]: "\<turnstile> \<Gamma> {Stop} \<Gamma>" |
  skip_type [intro] : "\<turnstile> \<Gamma> {Skip} \<Gamma>" |
  assign\<^sub>1 : "\<lbrakk> x \<notin> dom \<Gamma> ; \<Gamma> \<turnstile>\<^sub>a e \<in> t; t \<sqsubseteq> dma x \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma> {x \<leftarrow> e} \<Gamma>" |
  assign\<^sub>2 : "\<lbrakk> x \<in> dom \<Gamma> ; \<Gamma> \<turnstile>\<^sub>a e \<in> t \<rbrakk> \<Longrightarrow> has_type \<Gamma> (x \<leftarrow> e) (\<Gamma> (x := Some t))" |
  if_type [intro]: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>b e \<in> High \<longrightarrow> 
    ((\<forall> mds. mds_consistent mds \<Gamma> \<longrightarrow> (low_indistinguishable mds c\<^sub>1 c\<^sub>2)) \<and>
     (\<forall> x \<in> dom \<Gamma>'. \<Gamma>' x = Some High))
             ; \<turnstile> \<Gamma> { c\<^sub>1 } \<Gamma>'
             ; \<turnstile> \<Gamma> { c\<^sub>2 } \<Gamma>' \<rbrakk> \<Longrightarrow>
             \<turnstile> \<Gamma> { If e c\<^sub>1 c\<^sub>2 } \<Gamma>'" |
  while_type [intro]: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>b e \<in> Low ; \<turnstile> \<Gamma> { c } \<Gamma> \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma> { While e c } \<Gamma>" |
  anno_type [intro]: "\<lbrakk> \<Gamma>' = \<Gamma> \<oplus> upd ; \<turnstile> \<Gamma>' { c } \<Gamma>'' ; c \<noteq> Stop ;
                 \<forall> x. to_total \<Gamma> x \<sqsubseteq> to_total \<Gamma>' x \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma> { c@[upd] } \<Gamma>''" |
  seq_type [intro]: "\<lbrakk> \<turnstile> \<Gamma> { c\<^sub>1 } \<Gamma>' ; \<turnstile> \<Gamma>' { c\<^sub>2 } \<Gamma>'' \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma> { c\<^sub>1 ;; c\<^sub>2 } \<Gamma>''" |
  sub : "\<lbrakk> \<turnstile> \<Gamma>\<^sub>1 { c } \<Gamma>\<^sub>1' ; \<Gamma>\<^sub>2 \<sqsubseteq>\<^sub>c \<Gamma>\<^sub>1 ; \<Gamma>\<^sub>1' \<sqsubseteq>\<^sub>c \<Gamma>\<^sub>2' \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>\<^sub>2 { c } \<Gamma>\<^sub>2'"

subsection \<open>Typing Soundness\<close>

text \<open>The following predicate is needed to exclude some pathological
  cases, that abuse the @{term Stop} command which is not allowed to
  occur in actual programs.\<close>

fun has_annotated_stop :: "('Var, 'AExp, 'BExp) Stmt \<Rightarrow> bool"
  where
  "has_annotated_stop (c@[_]) = (if c = Stop then True else has_annotated_stop c)" |
  "has_annotated_stop (Seq p q) = (has_annotated_stop p \<or> has_annotated_stop q)" |
  "has_annotated_stop (If _ p q) = (has_annotated_stop p \<or> has_annotated_stop q)" |
  "has_annotated_stop (While _ p) = has_annotated_stop p" |
  "has_annotated_stop _ = False"

inductive_cases has_type_elim: "\<turnstile> \<Gamma> { c } \<Gamma>'"
inductive_cases has_type_stop_elim: "\<turnstile> \<Gamma> { Stop } \<Gamma>'"

definition tyenv_eq :: "'Var TyEnv \<Rightarrow> ('Var, 'Val) Mem \<Rightarrow> ('Var, 'Val) Mem \<Rightarrow> bool"
  (infix "=\<index>" 60)
  where "mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2 \<equiv> \<forall> x. (to_total \<Gamma> x = Low \<longrightarrow> mem\<^sub>1 x = mem\<^sub>2 x)"

lemma tyenv_eq_sym: "mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2 \<Longrightarrow> mem\<^sub>2 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>1"
  by (auto simp: tyenv_eq_def)


(* Parametrized relations for type soundness proof *)
inductive_set \<R>\<^sub>1 :: "'Var TyEnv \<Rightarrow> (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf rel"
  and \<R>\<^sub>1_abv :: "'Var TyEnv \<Rightarrow>
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
  bool" ("_ \<R>\<^sup>1\<index> _" [120, 120] 1000)
  for \<Gamma>' :: "'Var TyEnv"
  where
  "x \<R>\<^sup>1\<^bsub>\<Gamma>\<^esub> y \<equiv> (x, y) \<in> \<R>\<^sub>1 \<Gamma>" |
  intro [intro!] : "\<lbrakk> \<turnstile> \<Gamma> { c } \<Gamma>' ; mds_consistent mds \<Gamma> ; mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2 \<rbrakk> \<Longrightarrow> \<langle>c, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>'\<^esub> \<langle>c, mds, mem\<^sub>2\<rangle>"

inductive_set \<R>\<^sub>2 :: "'Var TyEnv \<Rightarrow> (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf rel"
  and \<R>\<^sub>2_abv :: "'Var TyEnv \<Rightarrow>
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
  bool" ("_ \<R>\<^sup>2\<index> _" [120, 120] 1000)
  for \<Gamma>' :: "'Var TyEnv"
  where
  "x \<R>\<^sup>2\<^bsub>\<Gamma>\<^esub> y \<equiv> (x, y) \<in> \<R>\<^sub>2 \<Gamma>" |
  intro [intro!] : "\<lbrakk> \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<approx> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> ;
                       \<forall> x \<in> dom \<Gamma>'. \<Gamma>' x = Some High ;
                       \<turnstile> \<Gamma>\<^sub>1 { c\<^sub>1 } \<Gamma>' ; \<turnstile> \<Gamma>\<^sub>2 { c\<^sub>2 } \<Gamma>' ;
                       mds_consistent mds \<Gamma>\<^sub>1 ; mds_consistent mds \<Gamma>\<^sub>2 \<rbrakk> \<Longrightarrow>
                     \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"

inductive \<R>\<^sub>3_aux :: "'Var TyEnv \<Rightarrow> (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
                 (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
                 bool" ("_ \<R>\<^sup>3\<index> _" [120, 120] 1000)
  and \<R>\<^sub>3 :: "'Var TyEnv \<Rightarrow> (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf rel"
  where
  "\<R>\<^sub>3 \<Gamma>' \<equiv> {(lc\<^sub>1, lc\<^sub>2). \<R>\<^sub>3_aux \<Gamma>' lc\<^sub>1 lc\<^sub>2}" |
  intro\<^sub>1 [intro] : "\<lbrakk> \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>; \<turnstile> \<Gamma> { c } \<Gamma>' \<rbrakk> \<Longrightarrow>
                      \<langle>Seq c\<^sub>1 c, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>'\<^esub> \<langle>Seq c\<^sub>2 c, mds, mem\<^sub>2\<rangle>" |
  intro\<^sub>2 [intro] : "\<lbrakk> \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>; \<turnstile> \<Gamma> { c } \<Gamma>' \<rbrakk> \<Longrightarrow>
                      \<langle>Seq c\<^sub>1 c, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>'\<^esub> \<langle>Seq c\<^sub>2 c, mds, mem\<^sub>2\<rangle>" |
  intro\<^sub>3 [intro] : "\<lbrakk> \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>; \<turnstile> \<Gamma> { c } \<Gamma>' \<rbrakk> \<Longrightarrow>
                      \<langle>Seq c\<^sub>1 c, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>'\<^esub> \<langle>Seq c\<^sub>2 c, mds, mem\<^sub>2\<rangle>"

(* A weaker property than bisimulation to reason about the sub-relations of \<R>: *)
definition weak_bisim :: "(('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf rel \<Rightarrow>
                        (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf rel \<Rightarrow> bool"
  where "weak_bisim \<T>\<^sub>1 \<T> \<equiv> \<forall> c\<^sub>1 c\<^sub>2 mds mem\<^sub>1 mem\<^sub>2 c\<^sub>1' mds' mem\<^sub>1'.
  ((\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> \<T>\<^sub>1 \<and>
   (\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>)) \<longrightarrow>
  (\<exists> c\<^sub>2' mem\<^sub>2'. \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and> 
                (\<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>, \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>) \<in> \<T>)"

inductive_set \<R> :: "'Var TyEnv \<Rightarrow>
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf rel"
  and \<R>_abv :: "'Var TyEnv \<Rightarrow>
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
  bool" ("_ \<R>\<^sup>u\<index> _" [120, 120] 1000)
  for \<Gamma> :: "'Var TyEnv"
  where
  "x \<R>\<^sup>u\<^bsub>\<Gamma>\<^esub> y \<equiv> (x, y) \<in> \<R> \<Gamma>" |
  intro\<^sub>1: "lc \<R>\<^sup>1\<^bsub>\<Gamma>\<^esub> lc' \<Longrightarrow> (lc, lc') \<in> \<R> \<Gamma>" |
  intro\<^sub>2: "lc \<R>\<^sup>2\<^bsub>\<Gamma>\<^esub> lc' \<Longrightarrow> (lc, lc') \<in> \<R> \<Gamma>" |
  intro\<^sub>3: "lc \<R>\<^sup>3\<^bsub>\<Gamma>\<^esub> lc' \<Longrightarrow> (lc, lc') \<in> \<R> \<Gamma>"

(* Some eliminators for the above relations *)
inductive_cases \<R>\<^sub>1_elim [elim]: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
inductive_cases \<R>\<^sub>2_elim [elim]: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
inductive_cases \<R>\<^sub>3_elim [elim]: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"

inductive_cases \<R>_elim [elim]: "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> \<R> \<Gamma>"
inductive_cases \<R>_elim': "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>) \<in> \<R> \<Gamma>"
inductive_cases \<R>\<^sub>1_elim' : "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>"
inductive_cases \<R>\<^sub>2_elim' : "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>"
inductive_cases \<R>\<^sub>3_elim' : "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>"

(* To prove that \<R> is a bisimulation, we first show symmetry *)

lemma \<R>\<^sub>1_sym: "sym (\<R>\<^sub>1 \<Gamma>)"
  unfolding sym_def
  apply auto
  by (metis (no_types) \<R>\<^sub>1.intro \<R>\<^sub>1_elim' tyenv_eq_sym)

lemma \<R>\<^sub>2_sym: "sym (\<R>\<^sub>2 \<Gamma>)"
  unfolding sym_def
  apply clarify
  by (metis (no_types) \<R>\<^sub>2.intro \<R>\<^sub>2_elim' mm_equiv_sym)

lemma \<R>\<^sub>3_sym: "sym (\<R>\<^sub>3 \<Gamma>)"
  unfolding sym_def
proof (clarify)
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mds' mem\<^sub>2
  assume asm: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2, mds', mem\<^sub>2\<rangle>"
  hence [simp]: "mds' = mds"
    using \<R>\<^sub>3_elim' by blast
  from asm show "\<langle>c\<^sub>2, mds', mem\<^sub>2\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>"
    apply auto
    apply (induct rule: \<R>\<^sub>3_aux.induct)
      apply (metis (lifting) \<R>\<^sub>1_sym \<R>\<^sub>3_aux.intro\<^sub>1 symD)
     apply (metis (lifting) \<R>\<^sub>2_sym \<R>\<^sub>3_aux.intro\<^sub>2 symD)
    by (metis (lifting) \<R>\<^sub>3_aux.intro\<^sub>3)
qed

lemma \<R>_mds [simp]: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2, mds', mem\<^sub>2\<rangle> \<Longrightarrow> mds = mds'"
  apply (rule \<R>_elim')
     apply (auto)
    apply (metis \<R>\<^sub>1_elim')
   apply (metis \<R>\<^sub>2_elim')
  apply (insert \<R>\<^sub>3_elim')
  by blast

lemma \<R>_sym: "sym (\<R> \<Gamma>)"
  unfolding sym_def
proof (clarify)
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mds\<^sub>2 mem\<^sub>2
  assume asm: "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>) \<in> \<R> \<Gamma>"
  with \<R>_mds have [simp]: "mds\<^sub>2 = mds"
    by blast
  from asm show "(\<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>, \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>) \<in> \<R> \<Gamma>"
    using \<R>.intro\<^sub>1 [of \<Gamma>] and \<R>.intro\<^sub>2 [of \<Gamma>] and \<R>.intro\<^sub>3 [of \<Gamma>]
    using \<R>\<^sub>1_sym [of \<Gamma>] and \<R>\<^sub>2_sym [of \<Gamma>] and \<R>\<^sub>3_sym [of \<Gamma>]
    apply simp
    apply (erule \<R>_elim)
      by (auto simp: sym_def)
qed

(* Next, we show that the relations are closed under globally consistent changes *)

lemma \<R>\<^sub>1_closed_glob_consistent: "closed_glob_consistent (\<R>\<^sub>1 \<Gamma>')"
  unfolding closed_glob_consistent_def
proof (clarify)
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 x \<Gamma>'
  assume R1: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  hence [simp]: "c\<^sub>2 = c\<^sub>1" by blast
  from R1 obtain \<Gamma> where \<Gamma>_props: "\<turnstile> \<Gamma> { c\<^sub>1 } \<Gamma>'" "mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2" "mds_consistent mds \<Gamma>"
    by blast
  hence "\<And> v. \<langle>c\<^sub>1, mds, mem\<^sub>1 (x := v)\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2 (x := v)\<rangle>"
    by (auto simp: tyenv_eq_def mds_consistent_def)
  moreover
  from \<Gamma>_props have "\<And> v\<^sub>1 v\<^sub>2. \<lbrakk> dma x = High ; x \<notin> mds AsmNoWrite \<rbrakk> \<Longrightarrow>
    \<langle>c\<^sub>1, mds, mem\<^sub>1(x := v\<^sub>1)\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2(x := v\<^sub>2)\<rangle>"
    apply (auto simp: mds_consistent_def tyenv_eq_def)
    by (metis (lifting, full_types) Sec.simps(2) mem_Collect_eq to_total_def)
  ultimately show
    "(dma x = High \<and> x \<notin> mds AsmNoWrite \<longrightarrow>
      (\<forall>v\<^sub>1 v\<^sub>2. \<langle>c\<^sub>1, mds, mem\<^sub>1(x := v\<^sub>1)\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2(x := v\<^sub>2)\<rangle>))
     \<and>
     (dma x = Low \<and> x \<notin> mds AsmNoWrite \<longrightarrow>
      (\<forall>v. \<langle>c\<^sub>1, mds, mem\<^sub>1(x := v)\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2(x := v)\<rangle>))"
    using intro\<^sub>1
    by auto
qed

lemma \<R>\<^sub>2_closed_glob_consistent: "closed_glob_consistent (\<R>\<^sub>2 \<Gamma>')"
  unfolding closed_glob_consistent_def
proof (clarify)
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 x \<Gamma>'
  assume R2: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  then obtain \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 where \<Gamma>_prop: "\<turnstile> \<Gamma>\<^sub>1 { c\<^sub>1 } \<Gamma>'" "\<turnstile> \<Gamma>\<^sub>2 { c\<^sub>2 } \<Gamma>'"
    "mds_consistent mds \<Gamma>\<^sub>1" "mds_consistent mds \<Gamma>\<^sub>2"
    by blast
  from R2 have bisim: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<approx> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
    by blast
  then obtain \<R>' where \<R>'_prop: "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> \<R>' \<and> strong_low_bisim_mm \<R>'"
    apply (rule mm_equiv_elim)
    by (auto simp: strong_low_bisim_mm_def)
  from \<R>'_prop have \<R>'_cons: "closed_glob_consistent \<R>'"
    by (auto simp: strong_low_bisim_mm_def)
  moreover
  from \<Gamma>_prop and \<R>'_prop
  have "\<And>mem\<^sub>1 mem\<^sub>2. (\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> \<R>' \<Longrightarrow> \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
    using \<R>\<^sub>2.intro [where \<Gamma>' = \<Gamma>' and \<Gamma>\<^sub>1 = \<Gamma>\<^sub>1 and \<Gamma>\<^sub>2 = \<Gamma>\<^sub>2]
    using mm_equiv_intro and R2
    by blast
  ultimately show
    "(dma x = High \<and> x \<notin> mds AsmNoWrite \<longrightarrow>
      (\<forall>v\<^sub>1 v\<^sub>2. \<langle>c\<^sub>1, mds, mem\<^sub>1(x := v\<^sub>1)\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2(x := v\<^sub>2)\<rangle>))
     \<and>
     (dma x = Low \<and> x \<notin> mds AsmNoWrite \<longrightarrow>
      (\<forall>v. \<langle>c\<^sub>1, mds, mem\<^sub>1(x := v)\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2(x := v)\<rangle>))"
    using \<R>'_prop
    unfolding closed_glob_consistent_def
    by simp
qed

(* A predicate like this seems to be necessary to make induct generate
    the correct goal in the following lemma. Without it, it somehow does
    not "unify" the local configuration components in the goal and the assumptions. *)
fun closed_glob_helper :: "'Var TyEnv \<Rightarrow> (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow> (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow> bool"
  where
  "closed_glob_helper \<Gamma>' \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle> =
  (\<forall> x. ((dma x = High \<and> x \<notin> mds AsmNoWrite) \<longrightarrow>
           (\<forall> v\<^sub>1 v\<^sub>2. (\<langle> c\<^sub>1, mds, mem\<^sub>1 (x := v\<^sub>1) \<rangle>, \<langle> c\<^sub>2, mds, mem\<^sub>2 (x := v\<^sub>2) \<rangle>) \<in> \<R>\<^sub>3 \<Gamma>')) \<and>
         ((dma x = Low \<and> x \<notin> mds AsmNoWrite) \<longrightarrow>
           (\<forall> v. (\<langle> c\<^sub>1, mds, mem\<^sub>1 (x := v) \<rangle>, \<langle> c\<^sub>2, mds, mem\<^sub>2 (x := v) \<rangle>) \<in> \<R>\<^sub>3 \<Gamma>')))"

lemma \<R>\<^sub>3_closed_glob_consistent:
  assumes R3: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  shows "\<forall> x.
    (dma x = High \<and> x \<notin> mds AsmNoWrite \<longrightarrow>
        (\<forall>v\<^sub>1 v\<^sub>2. (\<langle>c\<^sub>1, mds, mem\<^sub>1(x := v\<^sub>1)\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2(x := v\<^sub>2)\<rangle>) \<in> \<R>\<^sub>3 \<Gamma>')) \<and>
       (dma x = Low \<and> x \<notin> mds AsmNoWrite \<longrightarrow> (\<forall>v. (\<langle>c\<^sub>1, mds, mem\<^sub>1(x := v)\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2(x := v)\<rangle>) \<in> \<R>\<^sub>3 \<Gamma>'))"
proof -
  from R3 have "closed_glob_helper \<Gamma>' \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  proof (induct rule: \<R>\<^sub>3_aux.induct)
    case (intro\<^sub>1 \<Gamma> c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 c \<Gamma>')
    thus ?case
      using \<R>\<^sub>1_closed_glob_consistent [of \<Gamma>] and \<R>\<^sub>3_aux.intro\<^sub>1
      unfolding closed_glob_consistent_def
      by (simp, blast)
  next
    case (intro\<^sub>2 \<Gamma> c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 c \<Gamma>')
    thus ?case
      using \<R>\<^sub>2_closed_glob_consistent [of \<Gamma>] and \<R>\<^sub>3_aux.intro\<^sub>2
      unfolding closed_glob_consistent_def
      by (simp, blast)
  next
    case intro\<^sub>3
    thus ?case
      using \<R>\<^sub>3_aux.intro\<^sub>3
      by (simp, blast)
  qed
  thus ?thesis by simp
qed

lemma \<R>_closed_glob_consistent: "closed_glob_consistent (\<R> \<Gamma>')"
  unfolding closed_glob_consistent_def
proof (clarify, erule \<R>_elim, simp_all)
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 x
  assume R1: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  with \<R>\<^sub>1_closed_glob_consistent show
    "(dma x = High \<and> x \<notin> mds AsmNoWrite \<longrightarrow>
        (\<forall>v\<^sub>1 v\<^sub>2. (\<langle>c\<^sub>1, mds, mem\<^sub>1(x := v\<^sub>1)\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2(x := v\<^sub>2)\<rangle>) \<in> \<R> \<Gamma>')) \<and>
     (dma x = Low \<and> x \<notin> mds AsmNoWrite \<longrightarrow>
        (\<forall>v. (\<langle>c\<^sub>1, mds, mem\<^sub>1(x := v)\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2(x := v)\<rangle>) \<in> \<R> \<Gamma>'))"
    unfolding closed_glob_consistent_def
    using intro\<^sub>1
    apply clarify
    by metis
next
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 x
  assume R2: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  with \<R>\<^sub>2_closed_glob_consistent show
    "(dma x = High \<and> x \<notin> mds AsmNoWrite \<longrightarrow>
      (\<forall>v\<^sub>1 v\<^sub>2. (\<langle>c\<^sub>1, mds, mem\<^sub>1(x := v\<^sub>1)\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2(x := v\<^sub>2)\<rangle>) \<in> \<R> \<Gamma>'))
     \<and>
     (dma x = Low \<and> x \<notin> mds AsmNoWrite \<longrightarrow>
      (\<forall>v. (\<langle>c\<^sub>1, mds, mem\<^sub>1(x := v)\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2(x := v)\<rangle>) \<in> \<R> \<Gamma>'))"
    unfolding closed_glob_consistent_def
    using intro\<^sub>2
    apply clarify
    by metis
next
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 x \<Gamma>'
  assume R3: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  thus
    "(dma x = High \<and> x \<notin> mds AsmNoWrite \<longrightarrow>
       (\<forall>v\<^sub>1 v\<^sub>2. (\<langle>c\<^sub>1, mds, mem\<^sub>1(x := v\<^sub>1)\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2(x := v\<^sub>2)\<rangle>) \<in> \<R> \<Gamma>'))
     \<and>
     (dma x = Low \<and> x \<notin> mds AsmNoWrite \<longrightarrow>
       (\<forall>v. (\<langle>c\<^sub>1, mds, mem\<^sub>1(x := v)\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2(x := v)\<rangle>) \<in> \<R> \<Gamma>'))"
    using \<R>\<^sub>3_closed_glob_consistent
    apply auto
     apply (metis \<R>.intro\<^sub>3)
    by (metis (lifting) \<R>.intro\<^sub>3)
qed

(* It now remains to show that steps of the first of two related configurations
    can be matched by the second: *)

(* Some technical lemmas: *)
lemma type_low_vars_low:
  assumes typed: "\<Gamma> \<turnstile>\<^sub>a e \<in> Low"
  assumes mds_cons: "mds_consistent mds \<Gamma>"
  assumes x_in_vars: "x \<in> aexp_vars e"
  shows "to_total \<Gamma> x = Low"
  using assms
  by (metis (full_types) Sec.exhaust imageI max_dom_def type_aexpr_elim)

lemma type_low_vars_low_b:
  assumes typed : "\<Gamma> \<turnstile>\<^sub>b e \<in> Low"
  assumes mds_cons: "mds_consistent mds \<Gamma>"
  assumes x_in_vars: "x \<in> bexp_vars e"
  shows "to_total \<Gamma> x = Low"
  using assms
  by (metis (full_types) Sec.exhaust imageI max_dom_def type_bexpr.simps)

lemma mode_update_add_anno:
  "mds_consistent mds \<Gamma> \<Longrightarrow> mds_consistent (update_modes upd mds) (\<Gamma> \<oplus> upd)"
  apply (induct arbitrary: \<Gamma> rule: add_anno_dom.induct)
  by (auto simp: add_anno_def mds_consistent_def)

lemma context_le_trans: "\<lbrakk> \<Gamma> \<sqsubseteq>\<^sub>c \<Gamma>' ; \<Gamma>' \<sqsubseteq>\<^sub>c \<Gamma>'' \<rbrakk> \<Longrightarrow> \<Gamma> \<sqsubseteq>\<^sub>c \<Gamma>''"
  apply (auto simp: context_le_def)
  by (metis domI order_trans option.sel)

lemma context_le_refl [simp]: "\<Gamma> \<sqsubseteq>\<^sub>c \<Gamma>"
  by (metis context_le_def order_refl)

(* Strangely, using only \<turnstile> \<Gamma> { Stop } \<Gamma>' as assumption does not work *)
lemma stop_cxt :
  "\<lbrakk> \<turnstile> \<Gamma> { c } \<Gamma>' ; c = Stop \<rbrakk> \<Longrightarrow> \<Gamma> \<sqsubseteq>\<^sub>c \<Gamma>'"
  apply (induct rule: has_type.induct)
          apply auto
  by (metis context_le_trans)

(* First we show that (roughly) typeability is preserved by evaluation steps *)
lemma preservation:
  assumes typed: "\<turnstile> \<Gamma> { c } \<Gamma>'"
  assumes eval: "\<langle>c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
  shows "\<exists> \<Gamma>''. (\<turnstile> \<Gamma>'' { c' } \<Gamma>') \<and> (mds_consistent mds \<Gamma> \<longrightarrow> mds_consistent mds' \<Gamma>'')"
  using typed eval
proof (induct arbitrary: c' mds rule: has_type.induct)
  case (anno_type \<Gamma>'' \<Gamma> upd c\<^sub>1 \<Gamma>')
  hence "\<langle>c\<^sub>1, update_modes upd mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
    by (metis upd_elim)
  with anno_type(3) obtain \<Gamma>''' where
    "\<turnstile> \<Gamma>''' { c' } \<Gamma>' \<and> (mds_consistent (update_modes upd mds) \<Gamma>'' \<longrightarrow>
                          mds_consistent mds' \<Gamma>''')"
    by auto
  moreover
  have "mds_consistent mds \<Gamma> \<longrightarrow> mds_consistent (update_modes upd mds) \<Gamma>''"
    using anno_type
    apply auto
    by (metis mode_update_add_anno)
  ultimately show ?case
    by blast
next
  case stop_type
  with stop_no_eval show ?case ..
next
  case skip_type
  hence "c' = Stop \<and> mds' = mds"
    by (metis skip_elim)
  thus ?case
    by (metis stop_type)
next
  case (assign\<^sub>1 x \<Gamma> e t c' mds)
  hence "c' = Stop \<and> mds' = mds"
    by (metis assign_elim)
  thus ?case
    by (metis stop_type)
next
  case (assign\<^sub>2 x \<Gamma> e t c' mds)
  hence "c' = Stop \<and> mds' = mds"
    by (metis assign_elim)
  thus ?case
    apply (rule_tac x = "\<Gamma> (x \<mapsto> t)" in exI)
    apply (auto simp: mds_consistent_def)
         apply (metis Sec.exhaust)
        apply (metis (lifting, full_types) CollectD domI assign\<^sub>2(1))
       apply (metis (lifting, full_types) CollectD domI assign\<^sub>2(1))
      apply (metis (lifting) CollectE domI assign\<^sub>2(1))
     apply (metis (lifting, full_types) domD mem_Collect_eq)
    by (metis (lifting, full_types) domD mem_Collect_eq)
next
  case (if_type \<Gamma> e th el \<Gamma>' c' mds)
  thus ?case
    apply (rule_tac x = \<Gamma> in exI)
    by force
next
  case (while_type \<Gamma> e c c' mds)
  hence [simp]: "mds' = mds \<and> c' = If e (c ;; While e c) Stop"
    by (metis while_elim)
  thus ?case
    apply (rule_tac x = \<Gamma> in exI)
    apply auto
    by (metis Sec.simps(2) has_type.while_type if_type while_type(1) while_type(2) seq_type stop_type type_bexpr_elim)
next
  case (seq_type \<Gamma> c\<^sub>1 \<Gamma>\<^sub>1 c\<^sub>2 \<Gamma>\<^sub>2 c' mds)
  thus ?case
  proof (cases "c\<^sub>1 = Stop")
    assume [simp]: "c\<^sub>1 = Stop"
    with seq_type have [simp]: "mds' = mds \<and> c' = c\<^sub>2"
      by (metis seq_stop_elim)
    thus ?case
      apply auto
      by (metis (lifting) \<open>c\<^sub>1 = Stop\<close> context_le_refl seq_type(1) seq_type(3) stop_cxt sub)
  next
    assume "c\<^sub>1 \<noteq> Stop"
    then obtain c\<^sub>1' where "\<langle>c\<^sub>1, mds, mem\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem'\<rangle> \<and> c' = (c\<^sub>1' ;; c\<^sub>2)"
      by (metis seq_elim seq_type.prems)
    then obtain \<Gamma>''' where "\<turnstile> \<Gamma>''' {c\<^sub>1'} \<Gamma>\<^sub>1 \<and>
      (mds_consistent mds \<Gamma> \<longrightarrow> mds_consistent mds' \<Gamma>''')"
      using seq_type(2)
      by auto
    moreover
    from seq_type have "\<turnstile> \<Gamma>\<^sub>1 { c\<^sub>2 } \<Gamma>\<^sub>2" by auto
    moreover
    ultimately show ?case
      apply (rule_tac x = \<Gamma>''' in exI)
      by (metis (lifting) \<open>\<langle>c\<^sub>1, mds, mem\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem'\<rangle> \<and> c' = c\<^sub>1' ;; c\<^sub>2\<close> has_type.seq_type)
  qed
next
  case (sub \<Gamma>\<^sub>1 c \<Gamma>\<^sub>1' \<Gamma>\<^sub>2 \<Gamma>\<^sub>2' c' mds)
  then obtain \<Gamma>'' where "\<turnstile> \<Gamma>'' { c' } \<Gamma>\<^sub>1' \<and>
    (mds_consistent mds \<Gamma>\<^sub>1 \<longrightarrow> mds_consistent mds' \<Gamma>'')"
    by auto
  thus ?case
    apply (rule_tac x = \<Gamma>'' in exI)
    apply (rule conjI)
     apply (metis (lifting) has_type.sub sub(4) stop_cxt stop_type)
    apply (simp add: mds_consistent_def)
    by (metis context_le_def sub.hyps(3))
qed

lemma \<R>\<^sub>1_mem_eq: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<Longrightarrow> mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2"
  apply (rule \<R>\<^sub>1_elim)
   apply (auto simp: tyenv_eq_def mds_consistent_def to_total_def)
  by (metis (lifting) Sec.simps(1) low_mds_eq_def)

lemma \<R>\<^sub>2_mem_eq: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<Longrightarrow> mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2"
  apply (rule \<R>\<^sub>2_elim)
  by (auto simp: mm_equiv_elim strong_low_bisim_mm_def)

fun bisim_helper :: "(('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow> bool"
  where
  "bisim_helper \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle> = mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2"

lemma \<R>\<^sub>3_mem_eq: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<Longrightarrow> mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2"
  apply (subgoal_tac "bisim_helper \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>")
   apply simp
  apply (induct rule: \<R>\<^sub>3_aux.induct)
  by (auto simp: \<R>\<^sub>1_mem_eq \<R>\<^sub>2_mem_eq)

(* \<R>\<^sub>2 is a full bisimulation so we can show the stronger step statement here: *)

lemma \<R>\<^sub>2_bisim_step:
  assumes case2: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  assumes eval: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>"
  shows "\<exists> c\<^sub>2' mem\<^sub>2'. \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>"
proof -
  from case2 have aux: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<approx> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>" "\<forall> x \<in> dom \<Gamma>'. \<Gamma>' x = Some High"
    by (rule \<R>\<^sub>2_elim, auto)
  with eval obtain c\<^sub>2' mem\<^sub>2' where c\<^sub>2'_props:
    "\<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and>
     \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<approx> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>"
    using mm_equiv_strong_low_bisim strong_low_bisim_mm_def
    by metis
  (* with aux(1) obtain \<R>' where \<R>'_props: "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> \<R>'" "strong_low_bisim_mm \<R>'" *)
    (* using mm_equiv_elim *)
    (* by auto *)
  from case2 obtain \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 where "\<turnstile> \<Gamma>\<^sub>1 { c\<^sub>1 } \<Gamma>'" "\<turnstile> \<Gamma>\<^sub>2 { c\<^sub>2 } \<Gamma>'"
    "mds_consistent mds \<Gamma>\<^sub>1" "mds_consistent mds \<Gamma>\<^sub>2"
    by (metis \<R>\<^sub>2_elim')
  with preservation and c\<^sub>2'_props obtain \<Gamma>\<^sub>1' \<Gamma>\<^sub>2' where
    "\<turnstile> \<Gamma>\<^sub>1' {c\<^sub>1'} \<Gamma>'" "mds_consistent mds' \<Gamma>\<^sub>1'"
    "\<turnstile> \<Gamma>\<^sub>2' {c\<^sub>2'} \<Gamma>'" "mds_consistent mds' \<Gamma>\<^sub>2'"
    using eval
    by metis
  with c\<^sub>2'_props show ?thesis
    using \<R>\<^sub>2.intro aux(2) c\<^sub>2'_props
    by blast
qed

(* To achieve more "symmetry" later, we prove a property analogous to the ones
    for \<R>\<^sub>1 and \<R>\<^sub>3 which are not, by themselves, bisimulations. *)

lemma \<R>\<^sub>2_weak_bisim:
  "weak_bisim (\<R>\<^sub>2 \<Gamma>') (\<R> \<Gamma>')"
  unfolding weak_bisim_def
  using \<R>.intro\<^sub>2
  apply auto
  by (metis \<R>\<^sub>2_bisim_step)


(* Not actually needed, but an interesting "asymmetry" since
    \<R>\<^sub>1 and \<R>\<^sub>3 aren't bisimulations. *)
lemma \<R>\<^sub>2_bisim: "strong_low_bisim_mm (\<R>\<^sub>2 \<Gamma>')"
  unfolding strong_low_bisim_mm_def
  by (auto simp: \<R>\<^sub>2_sym \<R>\<^sub>2_closed_glob_consistent \<R>\<^sub>2_mem_eq \<R>\<^sub>2_bisim_step)

lemma annotated_no_stop: "\<lbrakk> \<not> has_annotated_stop (c@[upd]) \<rbrakk> \<Longrightarrow> \<not> has_annotated_stop c"
  apply (cases c)
  by auto

lemma typed_no_annotated_stop:
  "\<lbrakk> \<turnstile> \<Gamma> { c } \<Gamma>' \<rbrakk> \<Longrightarrow> \<not> has_annotated_stop c"
  by (induct rule: has_type.induct, auto)

lemma not_stop_eval:
  "\<lbrakk> c \<noteq> Stop ; \<not> has_annotated_stop c \<rbrakk> \<Longrightarrow>
  \<forall> mds mem. \<exists> c' mds' mem'. \<langle>c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
proof (induct)
  case (Assign x exp)
  thus ?case
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.assign eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq)
next
  case Skip
  thus ?case
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.skip)
next
  case (ModeDecl c mu)
  hence "\<not> has_annotated_stop c \<and> c \<noteq> Stop"
    by (metis has_annotated_stop.simps(1))
  with ModeDecl show ?case
    apply (clarify, rename_tac mds mem)
    apply simp
    apply (erule_tac x = "update_modes mu mds" in allE)
    apply (erule_tac x = mem in allE)
    apply (erule exE)+
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w.decl)
next
  case (Seq c\<^sub>1 c\<^sub>2)
  thus ?case
  proof (cases "c\<^sub>1 = Stop")
    assume "c\<^sub>1 = Stop"
    thus ?case
      by (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.seq_stop eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq)
  next
    assume "c\<^sub>1 \<noteq> Stop"
    with Seq show ?case
      by (metis eval\<^sub>w.seq has_annotated_stop.simps(2))
  qed
next
  case (If bexp c\<^sub>1 c\<^sub>2)
  thus ?case
    apply (clarify, rename_tac mds mem)
    apply (case_tac "ev\<^sub>B mem bexp")
     apply (metis cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.if_true)
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.if_false)
next
  case (While bexp c)
  thus ?case
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.while eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq)
next
  case Stop
  thus ?case by blast
qed

lemma stop_bisim:
  assumes bisim: "\<langle>Stop, mds, mem\<^sub>1\<rangle> \<approx> \<langle>c, mds, mem\<^sub>2\<rangle>"
  assumes typeable: "\<turnstile> \<Gamma> { c } \<Gamma>'"
  shows "c = Stop"
proof (rule ccontr)
  let ?lc\<^sub>1 = "\<langle>Stop, mds, mem\<^sub>1\<rangle>" and
      ?lc\<^sub>2 = "\<langle>c, mds, mem\<^sub>2\<rangle>"
  assume "c \<noteq> Stop"
  from typeable have "\<not> has_annotated_stop c"
    by (metis typed_no_annotated_stop)
  with \<open>c \<noteq> Stop\<close> obtain c' mds' mem\<^sub>2' where "?lc\<^sub>2 \<leadsto> \<langle>c', mds', mem\<^sub>2'\<rangle>"
    using not_stop_eval
    by blast
  moreover
  from bisim have "?lc\<^sub>2 \<approx> ?lc\<^sub>1"
    by (metis mm_equiv_sym)
  ultimately obtain c\<^sub>1' mds\<^sub>1' mem\<^sub>1'
    where "\<langle>Stop, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds\<^sub>1', mem\<^sub>1'\<rangle>"
    using mm_equiv_strong_low_bisim
    unfolding strong_low_bisim_mm_def
    by blast
  thus False
    by (metis (lifting) stop_no_eval)
qed

(* This is the main part of the proof and used in \<R>\<^sub>1_weak_bisim: *)

lemma \<R>_typed_step:
  "\<lbrakk> \<turnstile> \<Gamma> { c\<^sub>1 } \<Gamma>' ;
     mds_consistent mds \<Gamma> ;
     mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2 ;
     \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<rbrakk> \<Longrightarrow>
   (\<exists> c\<^sub>2' mem\<^sub>2'. \<langle>c\<^sub>1, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and>
                 \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>)"
proof (induct arbitrary: mds c\<^sub>1' rule: has_type.induct)
  case (seq_type \<Gamma> c\<^sub>1 \<Gamma>'' c\<^sub>2 \<Gamma>' mds)
  show ?case
  proof (cases "c\<^sub>1 = Stop")
    assume "c\<^sub>1 = Stop"
    hence [simp]: "c\<^sub>1' = c\<^sub>2" "mds' = mds" "mem\<^sub>1' = mem\<^sub>1"
      using seq_type
      by (auto simp: seq_stop_elim)
    from seq_type \<open>c\<^sub>1 = Stop\<close> have "\<Gamma> \<sqsubseteq>\<^sub>c \<Gamma>''"
      by (metis stop_cxt)
    hence "\<turnstile> \<Gamma> { c\<^sub>2 } \<Gamma>'"
      by (metis context_le_refl seq_type(3) sub)
    have "\<langle>c\<^sub>2, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
      apply (rule \<R>\<^sub>1.intro [of \<Gamma>])
      by (auto simp: seq_type \<open>\<turnstile> \<Gamma> { c\<^sub>2 } \<Gamma>'\<close>)
    thus ?case
      using \<R>.intro\<^sub>1
      apply clarify
      apply (rule_tac x = c\<^sub>2 in exI)
      apply (rule_tac x = mem\<^sub>2 in exI)
      apply (auto simp: \<open>c\<^sub>1 = Stop\<close>)
      by (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.seq_stop eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq)
  next
    assume "c\<^sub>1 \<noteq> Stop"
    with \<open>\<langle>c\<^sub>1 ;; c\<^sub>2, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>\<close> obtain c\<^sub>1'' where c\<^sub>1''_props:
      "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<and> c\<^sub>1' = c\<^sub>1'' ;; c\<^sub>2"
      by (metis seq_elim)
    with seq_type(2) obtain c\<^sub>2'' mem\<^sub>2' where c\<^sub>2''_props:
      "\<langle>c\<^sub>1, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle> \<and> \<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>''\<^esub> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>"
      by (metis seq_type(5) seq_type(6))
    hence "\<langle>c\<^sub>1'' ;; c\<^sub>2, mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2'' ;; c\<^sub>2, mds', mem\<^sub>2'\<rangle>"
      apply (rule conjE)
      apply (erule \<R>_elim, auto)
        apply (metis \<R>.intro\<^sub>3 \<R>\<^sub>3_aux.intro\<^sub>1 seq_type(3))
       apply (metis \<R>.intro\<^sub>3 \<R>\<^sub>3_aux.intro\<^sub>2 seq_type(3))
      by (metis \<R>.intro\<^sub>3 \<R>\<^sub>3_aux.intro\<^sub>3 seq_type(3))
    moreover
    from c\<^sub>2''_props have "\<langle>c\<^sub>1 ;; c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2'' ;; c\<^sub>2, mds', mem\<^sub>2'\<rangle>"
      by (metis eval\<^sub>w.seq)
    ultimately show ?case
      by (metis c\<^sub>1''_props)
  qed
next
  case (anno_type \<Gamma>' \<Gamma> upd c \<Gamma>'' mds)
  have "mem\<^sub>1 =\<^bsub>\<Gamma>'\<^esub> mem\<^sub>2"
    by (metis less_eq_Sec_def anno_type(5) anno_type(7) tyenv_eq_def)
  have "mds_consistent (update_modes upd mds) \<Gamma>'"
    by (metis (lifting) anno_type(1) anno_type(6) mode_update_add_anno)
  then obtain c\<^sub>2' mem\<^sub>2' where "(\<langle>c, update_modes upd mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and>
    \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>''\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>)"
    using anno_type
    apply auto
    by (metis \<open>mem\<^sub>1 =\<^bsub>\<Gamma>'\<^esub> mem\<^sub>2\<close> anno_type(1) upd_elim)
  thus ?case
    apply (rule_tac x = c\<^sub>2' in exI)
    apply (rule_tac x = mem\<^sub>2' in exI)
    apply auto
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w.decl)
next
  case stop_type
  with stop_no_eval show ?case by auto
next
  case (skip_type \<Gamma> mds)
  moreover
  with skip_type have [simp]: "mds' = mds" "c\<^sub>1' = Stop" "mem\<^sub>1' = mem\<^sub>1"
    using skip_elim
    by (metis, metis, metis)
  with skip_type have "\<langle>Stop, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>\<^esub> \<langle>Stop, mds, mem\<^sub>2\<rangle>"
    by auto
  thus ?case
    using \<R>.intro\<^sub>1 and unannotated [where c = Skip and E = "[]"]
    apply auto
    by (metis eval\<^sub>w_simple.skip)
next (* assign\<^sub>1 *)
  case (assign\<^sub>1 x \<Gamma> e t mds)
  hence [simp]: "c\<^sub>1' = Stop" "mds' = mds" "mem\<^sub>1' = mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)"
    using assign_elim
    by (auto, metis)
  have "mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e) =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)"
  proof (cases "to_total \<Gamma> x")
    assume "to_total \<Gamma> x = High"
    thus ?thesis
      using assign\<^sub>1 tyenv_eq_def
      by auto
  next
    assume "to_total \<Gamma> x = Low"
    with assign\<^sub>1 have [simp]: "t = Low"
      by (metis less_eq_Sec_def to_total_def)
    hence "dma x = Low"
      using assign\<^sub>1 \<open>to_total \<Gamma> x = Low\<close>
      by (metis to_total_def)
    with assign\<^sub>1 have "\<forall> v \<in> aexp_vars e. to_total \<Gamma> v = Low"
      using type_low_vars_low
      by auto
    thus ?thesis
      using eval_vars_det\<^sub>A
      apply (auto simp: tyenv_eq_def)
       apply (metis (no_types) assign\<^sub>1(5) tyenv_eq_def)
      by (metis assign\<^sub>1(5) tyenv_eq_def)
  qed
  hence "\<langle>x \<leftarrow> e, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    "\<langle>Stop, mds', mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>\<^esub> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    apply auto
     apply (metis cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.assign)
    by (rule \<R>.intro\<^sub>1, auto simp: assign\<^sub>1)
  thus ?case
    using \<open>c\<^sub>1' = Stop\<close> and \<open>mem\<^sub>1' = mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<close>
    by blast
next (* assign\<^sub>2 *)
  case (assign\<^sub>2 x \<Gamma> e t mds)
  hence [simp]: "c\<^sub>1' = Stop" "mds' = mds" "mem\<^sub>1' = mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)"
    using assign_elim assign\<^sub>2
    by (auto, metis)
  let ?\<Gamma>' = "\<Gamma> (x \<mapsto> t)"
  have "\<langle>x \<leftarrow> e, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>Stop, mds, mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    using assign\<^sub>2
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.assign eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq)
  moreover
  have "\<langle>Stop, mds, mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<rangle> \<R>\<^sup>1\<^bsub>?\<Gamma>'\<^esub> \<langle>Stop, mds, mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
  proof (auto)
    from assign\<^sub>2 show "mds_consistent mds ?\<Gamma>'"
      apply (simp add: mds_consistent_def)
      by (metis (lifting) insert_absorb assign\<^sub>2(1))
  next
    show "mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e) =\<^bsub>?\<Gamma>'\<^esub> mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)"
      unfolding tyenv_eq_def
    proof (auto)
      assume "to_total (\<Gamma>(x \<mapsto> t)) x = Low"
      with \<open>\<Gamma> \<turnstile>\<^sub>a e \<in> t\<close> have "\<And> x. x \<in> aexp_vars e \<Longrightarrow> to_total \<Gamma> x = Low"
        by (metis assign\<^sub>2.prems(1) domI fun_upd_same option.sel to_total_def type_low_vars_low)
      thus "ev\<^sub>A mem\<^sub>1 e = ev\<^sub>A mem\<^sub>2 e"
        by (metis assign\<^sub>2.prems(2) eval_vars_det\<^sub>A tyenv_eq_def)
    next
      fix y
      assume "y \<noteq> x" and "to_total (\<Gamma> (x \<mapsto> t)) y = Low"
      thus "mem\<^sub>1 y = mem\<^sub>2 y"
        by (metis (full_types) assign\<^sub>2.prems(2) domD domI fun_upd_other to_total_def tyenv_eq_def)
    qed
  qed
  ultimately have "\<langle>x \<leftarrow> e, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    "\<langle>Stop, mds', mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>(x \<mapsto> t)\<^esub> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    using \<R>.intro\<^sub>1
    by auto
  thus ?case
    using \<open>mds' = mds\<close> \<open>c\<^sub>1' = Stop\<close> \<open>mem\<^sub>1' = mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)\<close>
    by blast
next (* if *)
  case (if_type \<Gamma> e th el \<Gamma>')
  have "(\<langle>c\<^sub>1', mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>) \<in> \<R> \<Gamma>'"
    apply (rule intro\<^sub>1)
    apply clarify
    apply (rule \<R>\<^sub>1.intro [where \<Gamma> = \<Gamma> and \<Gamma>' = \<Gamma>'])
      apply (auto simp: if_type)
    by (metis (lifting) if_elim if_type(2) if_type(4) if_type(8))
  have eq_condition: "ev\<^sub>B mem\<^sub>1 e = ev\<^sub>B mem\<^sub>2 e \<Longrightarrow> ?case"
  proof -
    assume "ev\<^sub>B mem\<^sub>1 e = ev\<^sub>B mem\<^sub>2 e"
    with if_type(8) have "(\<langle>If e th el, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>)"
      apply (cases "ev\<^sub>B mem\<^sub>1 e")
       apply (subgoal_tac "c\<^sub>1' = th")
        apply clarify
        apply (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.if_true eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq if_type(8))
       apply (metis if_elim if_type(8))
      apply (subgoal_tac "c\<^sub>1' = el")
       apply (metis (hide_lams, mono_tags) cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.if_false if_type(8))
      by (metis if_elim if_type(8))
    thus ?thesis
      by (metis \<open>\<langle>c\<^sub>1', mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>\<close> if_elim if_type(8))
  qed
  have "mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2"
    apply (auto simp: low_mds_eq_def mds_consistent_def)
    apply (subgoal_tac "x \<notin> dom \<Gamma>")
     apply (metis if_type(7) to_total_def tyenv_eq_def)
    by (metis (lifting, mono_tags) CollectD Sec.simps(2) if_type(6) mds_consistent_def)
  obtain t where "\<Gamma> \<turnstile>\<^sub>b e \<in> t"
    by (metis type_bexpr.intros)
  from if_type show ?case
  proof (cases t)
    assume "t = High"
    with if_type show ?thesis
    proof (cases "ev\<^sub>B mem\<^sub>1 e = ev\<^sub>B mem\<^sub>2 e")
      assume "ev\<^sub>B mem\<^sub>1 e = ev\<^sub>B mem\<^sub>2 e"
      with eq_condition show ?thesis by auto
    next
      assume neq: "ev\<^sub>B mem\<^sub>1 e \<noteq> ev\<^sub>B mem\<^sub>2 e"
      from if_type \<open>t = High\<close> have "th \<sim>\<^bsub>mds\<^esub> el"
        by (metis \<open>\<Gamma> \<turnstile>\<^sub>b e \<in> t\<close>)
      from neq show ?thesis
      proof (cases "ev\<^sub>B mem\<^sub>1 e")
        assume "ev\<^sub>B mem\<^sub>1 e"
        hence "c\<^sub>1' = th"
          by (metis (lifting) if_elim if_type(8))
        hence "\<langle>If e th el, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>el, mds, mem\<^sub>2\<rangle>"
          by (metis \<open>ev\<^sub>B mem\<^sub>1 e\<close> cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.if_false if_type(8) neq)
        moreover
        with \<open>mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2\<close> have "\<langle>th, mds, mem\<^sub>1\<rangle> \<approx> \<langle>el, mds, mem\<^sub>2\<rangle>"
          by (metis low_indistinguishable_def \<open>th \<sim>\<^bsub>mds\<^esub> el\<close>)
        have "\<forall> x \<in> dom \<Gamma>'. \<Gamma>' x = Some High"
          using if_type \<open>t = High\<close>
          by (metis \<open>\<Gamma> \<turnstile>\<^sub>b e \<in> t\<close>)
        have "\<langle>th, mds, mem\<^sub>1\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>'\<^esub> \<langle>el, mds, mem\<^sub>2\<rangle>"
          by (metis (lifting) \<R>\<^sub>2.intro \<open>\<forall>x\<in>dom \<Gamma>'. \<Gamma>' x = Some High\<close> \<open>\<langle>th, mds, mem\<^sub>1\<rangle> \<approx> \<langle>el, mds, mem\<^sub>2\<rangle>\<close> if_type(2) if_type(4) if_type(6))
        ultimately show ?thesis
          using \<R>.intro\<^sub>2
          apply clarify
          by (metis \<open>c\<^sub>1' = th\<close> if_elim if_type(8))
      next
        assume "\<not> ev\<^sub>B mem\<^sub>1 e"
        hence [simp]: "c\<^sub>1' = el"
          by (metis (lifting) if_type(8) if_elim)
        hence "\<langle>If e th el, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>th, mds, mem\<^sub>2\<rangle>"
          by (metis (hide_lams, mono_tags) \<open>\<not> ev\<^sub>B mem\<^sub>1 e\<close> cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.if_true if_type(8) neq)
        moreover
        from \<open>th \<sim>\<^bsub>mds\<^esub> el\<close> have "el \<sim>\<^bsub>mds\<^esub> th"
          by (metis low_indistinguishable_sym)
        with \<open>mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2\<close> have "\<langle>el, mds, mem\<^sub>1\<rangle> \<approx> \<langle>th, mds, mem\<^sub>2\<rangle>"
          by (metis low_indistinguishable_def)
        have "\<forall> x \<in> dom \<Gamma>'. \<Gamma>' x = Some High"
          using if_type \<open>t = High\<close>
          by (metis \<open>\<Gamma> \<turnstile>\<^sub>b e \<in> t\<close>)
        have "\<langle>el, mds, mem\<^sub>1\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>'\<^esub> \<langle>th, mds, mem\<^sub>2\<rangle>"
          apply (rule \<R>\<^sub>2.intro [where \<Gamma>\<^sub>1 = \<Gamma> and \<Gamma>\<^sub>2 = \<Gamma>])
          by (auto simp: if_type \<open>\<langle>el, mds, mem\<^sub>1\<rangle> \<approx> \<langle>th, mds, mem\<^sub>2\<rangle>\<close> \<open>\<forall> x \<in> dom \<Gamma>'. \<Gamma>' x = Some High\<close>)
        ultimately show ?thesis
          using \<R>.intro\<^sub>2
          apply clarify
          by (metis \<open>c\<^sub>1' = el\<close> if_elim if_type(8))
      qed
    qed
  next
    assume "t = Low"
    with if_type have "ev\<^sub>B mem\<^sub>1 e = ev\<^sub>B mem\<^sub>2 e"
      using eval_vars_det\<^sub>B
      apply (simp add: tyenv_eq_def \<open>\<Gamma> \<turnstile>\<^sub>b e \<in> t\<close> type_low_vars_low_b)
      by (metis (lifting) \<open>\<Gamma> \<turnstile>\<^sub>b e \<in> t\<close> type_low_vars_low_b)
    with eq_condition show ?thesis by auto
  qed
next (* while *)
  case (while_type \<Gamma> e c)
  hence [simp]: "c\<^sub>1' = (If e (c ;; While e c) Stop)" and
    [simp]: "mds' = mds" and
    [simp]: "mem\<^sub>1' = mem\<^sub>1"
    by (auto simp: while_elim)
  with while_type have "\<langle>While e c, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>"
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.while eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq)
  moreover
  have "\<langle>c\<^sub>1', mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>"
    apply (rule \<R>\<^sub>1.intro [where \<Gamma> = \<Gamma>])
      apply (auto simp: while_type)
    apply (rule if_type)
      apply (metis (lifting) Sec.simps(1) while_type(1) type_bexpr_elim)
     apply (rule seq_type [where \<Gamma>' = \<Gamma>])
      by (auto simp: while_type)
  ultimately show ?case
    using \<R>.intro\<^sub>1 [of \<Gamma>]
    by (auto, blast)
next
  case (sub \<Gamma>\<^sub>1 c \<Gamma>\<^sub>1' \<Gamma> \<Gamma>' mds c\<^sub>1')
  hence "dom \<Gamma>\<^sub>1 \<subseteq> dom \<Gamma>" "dom \<Gamma>' \<subseteq> dom \<Gamma>\<^sub>1'"
    apply (metis (lifting) context_le_def equalityE)
    by (metis context_le_def sub(4) order_refl)
  hence "mds_consistent mds \<Gamma>\<^sub>1"
    using sub
    apply (auto simp: mds_consistent_def)
     apply (metis (lifting, full_types) context_le_def domD mem_Collect_eq)
    by (metis (lifting, full_types) context_le_def domD mem_Collect_eq)
  moreover have "mem\<^sub>1 =\<^bsub>\<Gamma>\<^sub>1\<^esub> mem\<^sub>2"
    unfolding tyenv_eq_def
    by (metis (lifting, no_types) context_le_def less_eq_Sec_def sub.hyps(3) sub.prems(2) to_total_def tyenv_eq_def)
  ultimately obtain c\<^sub>2' mem\<^sub>2' where c\<^sub>2'_props: "\<langle>c, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>"
    "\<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>\<^sub>1'\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>"
    using sub
    by blast
  moreover
  have "\<And> c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2. \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>\<^sub>1'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<Longrightarrow>
    \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  proof -
    fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2
    let ?lc\<^sub>1 = "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>" and ?lc\<^sub>2 = "\<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
    assume asm: "?lc\<^sub>1 \<R>\<^sup>u\<^bsub>\<Gamma>\<^sub>1'\<^esub> ?lc\<^sub>2"
    moreover
    have "?lc\<^sub>1 \<R>\<^sup>1\<^bsub>\<Gamma>\<^sub>1'\<^esub> ?lc\<^sub>2 \<Longrightarrow> ?lc\<^sub>1 \<R>\<^sup>1\<^bsub>\<Gamma>'\<^esub> ?lc\<^sub>2"
      apply (erule \<R>\<^sub>1_elim)
      apply auto
      by (metis (lifting) has_type.sub sub(4) stop_cxt stop_type)
    moreover
    have "?lc\<^sub>1 \<R>\<^sup>2\<^bsub>\<Gamma>\<^sub>1'\<^esub> ?lc\<^sub>2 \<Longrightarrow> ?lc\<^sub>1 \<R>\<^sup>2\<^bsub>\<Gamma>'\<^esub> ?lc\<^sub>2"
    proof -
      assume r2: "?lc\<^sub>1 \<R>\<^sup>2\<^bsub>\<Gamma>\<^sub>1'\<^esub> ?lc\<^sub>2"
      then obtain \<Lambda>\<^sub>1 \<Lambda>\<^sub>2 where "\<turnstile> \<Lambda>\<^sub>1 { c\<^sub>1 }  \<Gamma>\<^sub>1'" "\<turnstile> \<Lambda>\<^sub>2 { c\<^sub>2 } \<Gamma>\<^sub>1'" "mds_consistent mds \<Lambda>\<^sub>1"
        "mds_consistent mds \<Lambda>\<^sub>2"
        by (metis \<R>\<^sub>2_elim)
      hence "\<turnstile> \<Lambda>\<^sub>1 { c\<^sub>1 } \<Gamma>'"
        using sub(4)
        by (metis context_le_refl has_type.sub sub(4))
      moreover
      have "\<turnstile> \<Lambda>\<^sub>2 { c\<^sub>2 } \<Gamma>'"
        by (metis \<open>\<turnstile> \<Lambda>\<^sub>2 {c\<^sub>2} \<Gamma>\<^sub>1'\<close> context_le_refl has_type.sub sub(4))
      moreover
      from r2 have "\<forall> x \<in> dom \<Gamma>\<^sub>1'. \<Gamma>\<^sub>1' x = Some High"
        apply (rule \<R>\<^sub>2_elim)
        by auto
      hence "\<forall> x \<in> dom \<Gamma>'. \<Gamma>' x = Some High"
        by (metis Sec.simps(2) \<open>dom \<Gamma>' \<subseteq> dom \<Gamma>\<^sub>1'\<close> context_le_def domD less_eq_Sec_def sub(4) rev_subsetD option.sel)
      ultimately show ?thesis
        by (metis (no_types) \<R>\<^sub>2.intro \<R>\<^sub>2_elim' \<open>mds_consistent mds \<Lambda>\<^sub>1\<close> \<open>mds_consistent mds \<Lambda>\<^sub>2\<close> r2)
    qed
    moreover
    have "?lc\<^sub>1 \<R>\<^sup>3\<^bsub>\<Gamma>\<^sub>1'\<^esub> ?lc\<^sub>2 \<Longrightarrow> ?lc\<^sub>1 \<R>\<^sup>3\<^bsub>\<Gamma>'\<^esub> ?lc\<^sub>2"
      apply (erule \<R>\<^sub>3_elim)
      proof -
        fix \<Gamma> c\<^sub>1'' c\<^sub>2''' c
        assume [simp]: "c\<^sub>1 = c\<^sub>1'' ;; c" "c\<^sub>2 = c\<^sub>2''' ;; c"
        assume case1: "\<turnstile> \<Gamma> {c} \<Gamma>\<^sub>1'" "\<langle>c\<^sub>1'', mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2''', mds, mem\<^sub>2\<rangle>"
        hence "\<turnstile> \<Gamma> {c} \<Gamma>'"
          using context_le_refl has_type.sub sub.hyps(4)
          by blast
        with case1 show "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
          using \<R>\<^sub>3_aux.intro\<^sub>1 by simp
      next
        fix \<Gamma> c\<^sub>1'' c\<^sub>2''' c''
        assume [simp]: "c\<^sub>1 = c\<^sub>1'' ;; c''" "c\<^sub>2 = c\<^sub>2''' ;; c''"
        assume "\<langle>c\<^sub>1'', mds, mem\<^sub>1\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2''', mds, mem\<^sub>2\<rangle>" "\<turnstile> \<Gamma> {c''} \<Gamma>\<^sub>1'"
        thus "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
          using \<R>\<^sub>3_aux.intro\<^sub>2
          apply simp
          apply (rule \<R>\<^sub>3_aux.intro\<^sub>2 [where \<Gamma> = \<Gamma>])
           apply simp
          by (metis context_le_refl has_type.sub sub.hyps(4))
      next
        fix \<Gamma> c\<^sub>1'' c\<^sub>2''' c''
        assume [simp]: "c\<^sub>1 = c\<^sub>1'' ;; c''" "c\<^sub>2 = c\<^sub>2''' ;; c''"
        assume "\<langle>c\<^sub>1'', mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2''', mds, mem\<^sub>2\<rangle>" "\<turnstile> \<Gamma> {c''} \<Gamma>\<^sub>1'"
        thus "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
          using \<R>\<^sub>3_aux.intro\<^sub>3
          apply auto
          by (metis (hide_lams, no_types) context_le_refl has_type.sub sub.hyps(4))
      qed
    ultimately show "?thesis c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2"
      by (auto simp: \<R>.intros)
  qed
  with c\<^sub>2'_props show ?case
    by blast
qed

(* We can now show that \<R>\<^sub>1 and \<R>\<^sub>3 are weak bisimulations of \<R>,: *)
lemma \<R>\<^sub>1_weak_bisim:
  "weak_bisim (\<R>\<^sub>1 \<Gamma>') (\<R> \<Gamma>')"
  unfolding weak_bisim_def
  using \<R>\<^sub>1_elim \<R>_typed_step
  by auto

lemma \<R>_to_\<R>\<^sub>3: "\<lbrakk> \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> ; \<turnstile> \<Gamma> { c } \<Gamma>' \<rbrakk> \<Longrightarrow>
  \<langle>c\<^sub>1 ;; c, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2 ;; c, mds, mem\<^sub>2\<rangle>"
  apply (erule \<R>_elim)
  by auto

lemma \<R>\<^sub>2_implies_typeable: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<Longrightarrow> \<exists> \<Gamma>\<^sub>1. \<turnstile> \<Gamma>\<^sub>1 { c\<^sub>2 } \<Gamma>'"
  apply (erule \<R>\<^sub>2_elim)
  by auto

lemma \<R>\<^sub>3_weak_bisim:
  "weak_bisim (\<R>\<^sub>3 \<Gamma>') (\<R> \<Gamma>')"
proof -
  {
    fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 c\<^sub>1' mds' mem\<^sub>1'
    assume case3: "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> \<R>\<^sub>3 \<Gamma>'"
    assume eval: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>"
    have "\<exists> c\<^sub>2' mem\<^sub>2'. \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>"
      using case3 eval
      apply simp
      
    proof (induct arbitrary: c\<^sub>1' rule: \<R>\<^sub>3_aux.induct)
      case (intro\<^sub>1 \<Gamma> c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 c \<Gamma>')
      hence [simp]: "c\<^sub>2 = c\<^sub>1"
        by (metis (lifting) \<R>\<^sub>1_elim)
      thus ?case
      proof (cases "c\<^sub>1 = Stop")
        assume [simp]: "c\<^sub>1 = Stop"
        from intro\<^sub>1(1) show ?thesis
          apply (rule \<R>\<^sub>1_elim)
          apply simp
          apply (rule_tac x = c in exI)
          apply (rule_tac x = mem\<^sub>2 in exI)
          apply (rule conjI)
           apply (metis \<open>c\<^sub>1 = Stop\<close> cxt_to_stmt.simps(1) eval\<^sub>w_simplep.seq_stop eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq intro\<^sub>1.prems seq_stop_elim)
          apply (rule \<R>.intro\<^sub>1, clarify)
          by (metis (no_types) \<R>\<^sub>1.intro \<open>c\<^sub>1 = Stop\<close> context_le_refl intro\<^sub>1.prems intro\<^sub>1(2) seq_stop_elim stop_cxt sub)
      next
        assume "c\<^sub>1 \<noteq> Stop"
        from intro\<^sub>1
        obtain c\<^sub>1'' where "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<and> c\<^sub>1' = (c\<^sub>1'' ;; c)"
          by (metis \<open>c\<^sub>1 \<noteq> Stop\<close> intro\<^sub>1.prems seq_elim)
        with intro\<^sub>1
        obtain c\<^sub>2'' mem\<^sub>2' where "\<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>" "\<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>"
          using \<R>\<^sub>1_weak_bisim and weak_bisim_def
          by blast
        thus ?thesis
          using intro\<^sub>1(2) \<R>_to_\<R>\<^sub>3
          apply (rule_tac x = "c\<^sub>2'' ;; c" in exI)
          apply (rule_tac x = mem\<^sub>2' in exI)
          apply (rule conjI)
           apply (metis eval\<^sub>w.seq)
          apply auto
          apply (rule \<R>.intro\<^sub>3)
          by (metis (hide_lams, no_types) \<open>\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<and> c\<^sub>1' = c\<^sub>1'' ;; c\<close>)
      qed
    next
      case (intro\<^sub>2 \<Gamma> c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 cn \<Gamma>')
      thus ?case
      proof (cases "c\<^sub>1 = Stop")
        assume [simp]: "c\<^sub>1 = Stop"
        hence [simp]: "c\<^sub>1' = cn" "mds' = mds" "mem\<^sub>1' = mem\<^sub>1"
          using eval intro\<^sub>2 seq_stop_elim 
          by auto
        from intro\<^sub>2 have bisim: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<approx> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
          by (metis (lifting) \<R>\<^sub>2_elim')
        from intro\<^sub>2 obtain \<Gamma>\<^sub>1 where "\<turnstile> \<Gamma>\<^sub>1 { c\<^sub>2 } \<Gamma>"
          by (metis \<R>\<^sub>2_implies_typeable)
        with bisim have [simp]: "c\<^sub>2 = Stop"
          apply auto
          apply (rule stop_bisim [of mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 \<Gamma>\<^sub>1 \<Gamma>])
          by simp_all
        have "\<langle>c\<^sub>2 ;; cn, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>cn, mds', mem\<^sub>2\<rangle>"
          apply (auto simp: intro\<^sub>2)
          by (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.seq_stop eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq)
        moreover
        from intro\<^sub>2(1) have "mds_consistent mds \<Gamma>"
          apply auto
          apply (erule \<R>\<^sub>2_elim)
          apply (simp add: mds_consistent_def)
          by (metis context_le_def stop_cxt)
        moreover
        from bisim have "mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2"
          by (auto simp: mm_equiv.simps strong_low_bisim_mm_def)
        have "\<forall> x \<in> dom \<Gamma>. \<Gamma> x = Some High"
          using intro\<^sub>2(1)
          by (metis \<R>\<^sub>2_elim')
        hence "mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2"
          using \<open>mds_consistent mds \<Gamma>\<close> \<open>mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2\<close>
          apply (auto simp: tyenv_eq_def low_mds_eq_def mds_consistent_def)
          by (metis Sec.simps(1) \<open>\<forall>x\<in>dom \<Gamma>. \<Gamma> x = Some High\<close> \<open>mds' = mds\<close> domI option.sel to_total_def)
        ultimately have "\<langle>cn, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>'\<^esub> \<langle>cn, mds, mem\<^sub>2\<rangle>"
          by (metis (lifting) \<R>\<^sub>1.intro intro\<^sub>2(2))
        thus "?thesis"
          using \<R>.intro\<^sub>1
          apply auto
          by (metis \<open>\<langle>c\<^sub>2 ;; cn, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>cn, mds', mem\<^sub>2\<rangle>\<close> \<open>c\<^sub>2 = Stop\<close> \<open>mds' = mds\<close>)
      next
        assume "c\<^sub>1 \<noteq> Stop"
        then obtain c\<^sub>1''' where "c\<^sub>1' = c\<^sub>1''' ;; cn" "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1''', mds', mem\<^sub>1'\<rangle>"
          by (metis (no_types) intro\<^sub>2.prems seq_elim)
        then obtain c\<^sub>2''' mem\<^sub>2' where c\<^sub>2'''_props:
          "\<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2''', mds', mem\<^sub>2'\<rangle> \<and>
          \<langle>c\<^sub>1''', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>2\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2''', mds', mem\<^sub>2'\<rangle>"
          using \<R>\<^sub>2_bisim_step intro\<^sub>2
          by blast
        let ?c\<^sub>2' = "c\<^sub>2''' ;; cn"
        from c\<^sub>2'''_props have "\<langle>c\<^sub>2 ;; cn, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>?c\<^sub>2', mds', mem\<^sub>2'\<rangle>"
          by (metis (lifting) intro\<^sub>2 eval\<^sub>w.seq)
        moreover
        have "(\<langle>c\<^sub>1''' ;; cn, mds', mem\<^sub>1'\<rangle>, \<langle>?c\<^sub>2', mds', mem\<^sub>2'\<rangle>) \<in> \<R>\<^sub>3 \<Gamma>'"
          by (metis (lifting) \<R>\<^sub>3_aux.intro\<^sub>2 c\<^sub>2'''_props intro\<^sub>2(2) mem_Collect_eq case_prodI)
        ultimately show ?thesis
          using \<R>.intro\<^sub>3
          by (metis (lifting) \<R>\<^sub>3_aux.intro\<^sub>2 \<open>c\<^sub>1' = c\<^sub>1''' ;; cn\<close> c\<^sub>2'''_props intro\<^sub>2(2))
      qed
    next
      case (intro\<^sub>3 \<Gamma> c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 c \<Gamma>')
      thus ?case
        apply (cases "c\<^sub>1 = Stop")
         apply blast
      proof -
        assume "c\<^sub>1 \<noteq> Stop"
        then obtain c\<^sub>1'' where "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle>" "c\<^sub>1' = (c\<^sub>1'' ;; c)"
          by (metis intro\<^sub>3.prems seq_elim)
        then obtain c\<^sub>2'' mem\<^sub>2' where "\<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>" "\<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>"
          using intro\<^sub>3(2) mem_Collect_eq case_prodI
          by metis
        thus ?thesis
          apply (rule_tac x = "c\<^sub>2'' ;; c" in exI)
          apply (rule_tac x = mem\<^sub>2' in exI)
          apply (rule conjI)
           apply (metis eval\<^sub>w.seq)
          apply (erule \<R>_elim)
            apply simp_all
            apply (metis \<R>.intro\<^sub>3 \<R>_to_\<R>\<^sub>3 \<open>\<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>\<close> \<open>c\<^sub>1' = c\<^sub>1'' ;; c\<close> intro\<^sub>3(3))
           apply (metis (lifting) \<R>.intro\<^sub>3 \<R>_to_\<R>\<^sub>3 \<open>\<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>\<^esub> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>\<close> \<open>c\<^sub>1' = c\<^sub>1'' ;; c\<close> intro\<^sub>3(3))
          by (metis (lifting) \<R>.intro\<^sub>3 \<R>\<^sub>3_aux.intro\<^sub>3 \<open>c\<^sub>1' = c\<^sub>1'' ;; c\<close> intro\<^sub>3(3))
      qed
    qed
  }
  thus ?thesis
    unfolding weak_bisim_def
    by auto
qed

(* Hence \<R> is a bisimulation: *)
lemma \<R>_bisim: "strong_low_bisim_mm (\<R> \<Gamma>')"
  unfolding strong_low_bisim_mm_def
proof (auto)
  from \<R>_sym show "sym (\<R> \<Gamma>')" .
next
  from \<R>_closed_glob_consistent show "closed_glob_consistent (\<R> \<Gamma>')" .
next
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2
  assume "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  thus "mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2"
    apply (rule \<R>_elim)
    by (auto simp: \<R>\<^sub>1_mem_eq \<R>\<^sub>2_mem_eq \<R>\<^sub>3_mem_eq)
next
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 c\<^sub>1' mds' mem\<^sub>1'
  assume eval: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>"
  assume R: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  from R show "\<exists> c\<^sub>2' mem\<^sub>2'. \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and>
                            \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>"
    apply (rule \<R>_elim)
      apply (insert \<R>\<^sub>1_weak_bisim \<R>\<^sub>2_weak_bisim \<R>\<^sub>3_weak_bisim eval weak_bisim_def)
      apply (clarify, blast)+
    by (metis mem_Collect_eq case_prodI)
qed

lemma Typed_in_\<R>:
  assumes typeable: "\<turnstile> \<Gamma> { c } \<Gamma>'"
  assumes mds_cons: "mds_consistent mds \<Gamma>"
  assumes mem_eq: "\<forall> x. to_total \<Gamma> x = Low \<longrightarrow> mem\<^sub>1 x = mem\<^sub>2 x"
  shows "\<langle>c, mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'\<^esub> \<langle>c, mds, mem\<^sub>2\<rangle>"
  apply (rule \<R>.intro\<^sub>1 [of \<Gamma>'])
  apply clarify
  apply (rule \<R>\<^sub>1.intro [of \<Gamma>])
  by (auto simp: assms tyenv_eq_def) 

(* We then prove the main soundness theorem using the fact that typeable
    configurations can be related using \<R>\<^sub>1 *)
theorem type_soundness:
  assumes well_typed: "\<turnstile> \<Gamma> { c } \<Gamma>'"
  assumes mds_cons: "mds_consistent mds \<Gamma>"
  assumes mem_eq: "\<forall> x. to_total \<Gamma> x = Low \<longrightarrow> mem\<^sub>1 x = mem\<^sub>2 x"
  shows "\<langle>c, mds, mem\<^sub>1\<rangle> \<approx> \<langle>c, mds, mem\<^sub>2\<rangle>"
  using \<R>_bisim Typed_in_\<R>
  by (metis mds_cons mem_eq mm_equiv.simps well_typed)

definition "\<Gamma>\<^sub>0" :: "'Var TyEnv"
  where "\<Gamma>\<^sub>0 x = None"

(* The typing relation for lists of commands ("thread pools"). *)
inductive type_global :: "('Var, 'AExp, 'BExp) Stmt list \<Rightarrow> bool"
  ("\<turnstile> _" [120] 1000)
  where
  "\<lbrakk> list_all (\<lambda> c. \<turnstile> \<Gamma>\<^sub>0 { c } \<Gamma>\<^sub>0) cs ;
     \<forall> mem. sound_mode_use (add_initial_modes cs, mem) \<rbrakk> \<Longrightarrow>
    type_global cs"

inductive_cases type_global_elim: "\<turnstile> cs"

lemma mds\<^sub>s_consistent: "mds_consistent mds\<^sub>s \<Gamma>\<^sub>0"
  by (auto simp: mds\<^sub>s_def mds_consistent_def \<Gamma>\<^sub>0_def)

lemma typed_secure:
  "\<lbrakk> \<turnstile> \<Gamma>\<^sub>0 { c } \<Gamma>\<^sub>0 \<rbrakk> \<Longrightarrow> com_sifum_secure c"
  apply (auto simp: com_sifum_secure_def low_indistinguishable_def mds_consistent_def type_soundness)
  apply (auto simp: low_mds_eq_def)
  apply (rule type_soundness [of \<Gamma>\<^sub>0 c \<Gamma>\<^sub>0])
    apply (auto simp: mds\<^sub>s_consistent to_total_def \<Gamma>\<^sub>0_def)
  by (metis empty_iff mds\<^sub>s_def)

lemma "\<lbrakk> mds_consistent mds \<Gamma>\<^sub>0 ; dma x = Low \<rbrakk> \<Longrightarrow> x \<notin> mds AsmNoRead"
  by (auto simp: mds_consistent_def \<Gamma>\<^sub>0_def)

lemma list_all_set: "\<forall> x \<in> set xs. P x \<Longrightarrow> list_all P xs"
  by (metis (lifting) list_all_iff)

theorem type_soundness_global:
  assumes typeable: "\<turnstile> cs"
  assumes no_assms_term: "no_assumptions_on_termination cs"
  shows "prog_sifum_secure cs"
  using typeable
  apply (rule type_global_elim)
  apply (subgoal_tac "\<forall> c \<in> set cs. com_sifum_secure c")
   apply (metis list_all_set no_assms_term sifum_compositionality sound_mode_use.simps)
  by (metis (lifting) list_all_iff typed_secure)

end
end
