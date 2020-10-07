(*
Title: SIFUM-Type-Systems
Authors: Sylvia Grewe, Heiko Mantel, Daniel Schoepe
*)
section \<open>Language for Instantiating the SIFUM-Security Property\<close>

theory Language
imports Main Preliminaries
begin

subsection \<open>Syntax\<close>

datatype 'var ModeUpd = Acq "'var" Mode (infix "+=\<^sub>m" 75)
  | Rel "'var" Mode (infix "-=\<^sub>m" 75)

datatype ('var, 'aexp, 'bexp) Stmt = Assign "'var" "'aexp" (infix "\<leftarrow>" 130)
  | Skip
  | ModeDecl "('var, 'aexp, 'bexp) Stmt" "'var ModeUpd" ("_@[_]" [0, 0] 150)
  | Seq "('var, 'aexp, 'bexp) Stmt" "('var, 'aexp, 'bexp) Stmt" (infixr ";;" 150)
  | If "'bexp" "('var, 'aexp, 'bexp) Stmt" "('var, 'aexp, 'bexp) Stmt"
  | While "'bexp" "('var, 'aexp, 'bexp) Stmt"
  | Stop

type_synonym ('var, 'aexp, 'bexp) EvalCxt = "('var, 'aexp, 'bexp) Stmt list"

locale sifum_lang =
  fixes eval\<^sub>A :: "('Var, 'Val) Mem \<Rightarrow> 'AExp \<Rightarrow> 'Val"
  fixes eval\<^sub>B :: "('Var, 'Val) Mem \<Rightarrow> 'BExp \<Rightarrow> bool"
  fixes aexp_vars :: "'AExp \<Rightarrow> 'Var set"
  fixes bexp_vars :: "'BExp \<Rightarrow> 'Var set"
  fixes dma :: "'Var \<Rightarrow> Sec"
  assumes Var_finite : "finite {(x :: 'Var). True}"
  assumes eval_vars_det\<^sub>A : "\<lbrakk> \<forall> x \<in> aexp_vars e. mem\<^sub>1 x = mem\<^sub>2 x \<rbrakk> \<Longrightarrow> eval\<^sub>A mem\<^sub>1 e = eval\<^sub>A mem\<^sub>2 e"
  assumes eval_vars_det\<^sub>B : "\<lbrakk> \<forall> x \<in> bexp_vars b. mem\<^sub>1 x = mem\<^sub>2 x \<rbrakk> \<Longrightarrow> eval\<^sub>B mem\<^sub>1 b = eval\<^sub>B mem\<^sub>2 b"

context sifum_lang
begin

(* To make the examples look a bit nicer in the PDF. *)

notation (latex output)
  Seq ("_; _" 60)

notation (Rule output)
  Seq ("_ ; _" 60)

notation (Rule output)
  If ("if _ then _ else _ fi" 50)

notation (Rule output)
  While ("while _ do _ done")

abbreviation conf\<^sub>w_abv :: "('Var, 'AExp, 'BExp) Stmt \<Rightarrow>
  'Var Mds \<Rightarrow> ('Var, 'Val) Mem \<Rightarrow> (_,_,_) LocalConf"
  ("\<langle>_, _, _\<rangle>\<^sub>w" [0, 120, 120] 100)
  where
  "\<langle> c, mds, mem \<rangle>\<^sub>w \<equiv> ((c, mds), mem)"

subsection \<open>Semantics\<close>

primrec update_modes :: "'Var ModeUpd \<Rightarrow> 'Var Mds \<Rightarrow> 'Var Mds"
  where
  "update_modes (Acq x m) mds = mds (m := insert x (mds m))" |
  "update_modes (Rel x m) mds = mds (m := {y. y \<in> mds m \<and> y \<noteq> x})"

fun updated_var :: "'Var ModeUpd \<Rightarrow> 'Var"
  where
  "updated_var (Acq x _) = x" |
  "updated_var (Rel x _) = x"

fun updated_mode :: "'Var ModeUpd \<Rightarrow> Mode"
  where
  "updated_mode (Acq _ m) = m" |
  "updated_mode (Rel _ m) = m"

inductive_set eval\<^sub>w_simple :: "(('Var, 'AExp, 'BExp) Stmt \<times> ('Var, 'Val) Mem) rel"
and eval\<^sub>w_simple_abv :: "(('Var, 'AExp, 'BExp) Stmt \<times> ('Var, 'Val) Mem) \<Rightarrow>
  ('Var, 'AExp, 'BExp) Stmt \<times> ('Var, 'Val) Mem \<Rightarrow> bool"
  (infixr "\<leadsto>\<^sub>s" 60)
  where
  "c \<leadsto>\<^sub>s c' \<equiv> (c, c') \<in> eval\<^sub>w_simple" |
  assign: "((x \<leftarrow> e, mem), (Stop, mem (x := eval\<^sub>A mem e))) \<in> eval\<^sub>w_simple" |
  skip: "((Skip, mem), (Stop, mem)) \<in> eval\<^sub>w_simple" |
  seq_stop: "((Seq Stop c, mem), (c, mem)) \<in> eval\<^sub>w_simple" |
  if_true: "\<lbrakk> eval\<^sub>B mem b \<rbrakk> \<Longrightarrow> ((If b t e, mem), (t, mem)) \<in> eval\<^sub>w_simple" |
  if_false: "\<lbrakk> \<not> eval\<^sub>B mem b \<rbrakk> \<Longrightarrow> ((If b t e, mem), (e, mem)) \<in> eval\<^sub>w_simple" |
  while: "((While b c, mem), (If b (c ;; While b c) Stop, mem)) \<in> eval\<^sub>w_simple"

primrec cxt_to_stmt :: "('Var, 'AExp, 'BExp) EvalCxt \<Rightarrow> ('Var, 'AExp, 'BExp) Stmt
  \<Rightarrow> ('Var, 'AExp, 'BExp) Stmt"
  where
  "cxt_to_stmt [] c = c" |
  "cxt_to_stmt (c # cs) c' = Seq c' (cxt_to_stmt cs c)"

(* Design decision: Add "normal" rule for sequential statements here as well.
  Otherwise, one would have to take care of adding some sort of normalization
  later, so that one doesn't get stuck on expressions of the form (c ;; c') ;; c''.
*)
(* Normalization turned out to be more difficult, as it made the proofs of several
  helpful lemmas below quite difficult. *)

inductive_set eval\<^sub>w :: "(('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf rel"
and eval\<^sub>w_abv :: "(('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
                  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow> bool"
  (infixr "\<leadsto>\<^sub>w" 60)
  where
  "c \<leadsto>\<^sub>w c' \<equiv> (c, c') \<in> eval\<^sub>w" |
  unannotated: "\<lbrakk> (c, mem) \<leadsto>\<^sub>s (c', mem') \<rbrakk>
    \<Longrightarrow> (\<langle>cxt_to_stmt E c, mds, mem\<rangle>\<^sub>w, \<langle>cxt_to_stmt E c', mds, mem'\<rangle>\<^sub>w) \<in> eval\<^sub>w" |
  seq: "\<lbrakk> \<langle>c\<^sub>1, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c\<^sub>1', mds', mem'\<rangle>\<^sub>w \<rbrakk> \<Longrightarrow> (\<langle>(c\<^sub>1 ;; c\<^sub>2), mds, mem\<rangle>\<^sub>w, \<langle>(c\<^sub>1' ;; c\<^sub>2), mds', mem'\<rangle>\<^sub>w) \<in> eval\<^sub>w" |
  decl: "\<lbrakk> \<langle>c, update_modes mu mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<rbrakk> \<Longrightarrow>
         (\<langle>cxt_to_stmt E (ModeDecl c mu), mds, mem\<rangle>\<^sub>w, \<langle>cxt_to_stmt E c', mds', mem'\<rangle>\<^sub>w) \<in> eval\<^sub>w"

subsection \<open>Semantic Properties\<close>

text \<open>The following lemmas simplify working with evaluation contexts
  in the soundness proofs for the type system(s).\<close>

inductive_cases eval_elim: "(((c, mds), mem), ((c', mds'), mem')) \<in> eval\<^sub>w"
inductive_cases stop_no_eval' [elim]: "((Stop, mem), (c', mem')) \<in> eval\<^sub>w_simple"
inductive_cases assign_elim' [elim]: "((x \<leftarrow> e, mem), (c', mem')) \<in> eval\<^sub>w_simple"
inductive_cases skip_elim' [elim]: "(Skip, mem) \<leadsto>\<^sub>s (c', mem')"

lemma cxt_inv:
  "\<lbrakk> cxt_to_stmt E c = c' ; \<And> p q. c' \<noteq> Seq p q \<rbrakk> \<Longrightarrow> E = [] \<and> c' = c"
  by (metis cxt_to_stmt.simps(1) cxt_to_stmt.simps(2) neq_Nil_conv)

lemma cxt_inv_assign:
  "\<lbrakk> cxt_to_stmt E c = x \<leftarrow> e \<rbrakk> \<Longrightarrow> c = x \<leftarrow> e \<and> E = []"
  by (metis Stmt.simps(11) cxt_inv)

lemma cxt_inv_skip:
  "\<lbrakk> cxt_to_stmt E c = Skip \<rbrakk> \<Longrightarrow> c = Skip \<and> E = []"
  by (metis Stmt.simps(21) cxt_inv)

lemma cxt_inv_stop:
  "cxt_to_stmt E c = Stop \<Longrightarrow> c = Stop \<and> E = []"
  by (metis Stmt.simps(40) cxt_inv)

lemma cxt_inv_if:
  "cxt_to_stmt E c = If e p q \<Longrightarrow> c = If e p q \<and> E = []"
  by (metis Stmt.simps(37) cxt_inv)

lemma cxt_inv_while:
  "cxt_to_stmt E c = While e p \<Longrightarrow> c = While e p \<and> E = []"
  by (metis Stmt.simps(39) cxt_inv)

lemma skip_elim [elim]:
  "\<langle>Skip, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<Longrightarrow> c' = Stop \<and> mds = mds' \<and> mem = mem'"
  apply (erule eval_elim)
    apply (metis (lifting) cxt_inv_skip cxt_to_stmt.simps(1) skip_elim')
   apply (metis Stmt.simps(20))
  by (metis Stmt.simps(18) cxt_inv_skip)

lemma assign_elim [elim]:
  "\<langle>x \<leftarrow> e, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<Longrightarrow> c' = Stop \<and> mds = mds' \<and> mem' = mem (x := eval\<^sub>A mem e)"
  apply (erule eval_elim)
    apply (rename_tac c c'a E)
    apply (subgoal_tac "c = x \<leftarrow> e \<and> E = []")
     apply auto
      apply (metis cxt_inv_assign)
     apply (metis cxt_inv_assign)
    apply (metis Stmt.simps(8) cxt_inv_assign)
   apply (metis Stmt.simps(8) cxt_inv_assign)
  by (metis Stmt.simps(8) cxt_inv_assign)

inductive_cases if_elim' [elim!]: "(If b p q, mem) \<leadsto>\<^sub>s (c', mem')"

lemma if_elim [elim]:
  "\<And> P.
    \<lbrakk> \<langle>If b p q, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w ;
     \<lbrakk> c' = p; mem' = mem ; mds' = mds ; eval\<^sub>B mem b \<rbrakk> \<Longrightarrow> P ;
     \<lbrakk> c' = q; mem' = mem ; mds' = mds ; \<not> eval\<^sub>B mem b \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (erule eval_elim)
    apply (metis (no_types) cxt_inv_if cxt_to_stmt.simps(1) if_elim')
   apply (metis Stmt.simps(36))
  by (metis Stmt.simps(30) cxt_inv_if)

inductive_cases while_elim' [elim!]: "(While e c, mem) \<leadsto>\<^sub>s (c', mem')"

lemma while_elim [elim]:
  "\<lbrakk> \<langle>While e c, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<rbrakk> \<Longrightarrow> c' = If e (c ;; While e c) Stop \<and> mds' = mds \<and> mem' = mem"
  apply (erule eval_elim)
    apply (metis (no_types) cxt_inv_while cxt_to_stmt.simps(1) while_elim')
   apply (metis Stmt.simps(38))
  by (metis (lifting) Stmt.simps(33) cxt_inv_while)

inductive_cases upd_elim' [elim]: "(c@[upd], mem) \<leadsto>\<^sub>s (c', mem')"

lemma upd_elim [elim]:
  "\<langle>c@[upd], mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<Longrightarrow> \<langle>c, update_modes upd mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w"
  apply (erule eval_elim)
    apply (metis (lifting) Stmt.simps(28) cxt_inv upd_elim')
   apply (metis Stmt.simps(29))
  by (metis (lifting) Stmt.simps(2) Stmt.simps(29) cxt_inv cxt_to_stmt.simps(1))

lemma cxt_seq_elim [elim]:
  "c\<^sub>1 ;; c\<^sub>2 = cxt_to_stmt E c \<Longrightarrow> (E = [] \<and> c = c\<^sub>1 ;; c\<^sub>2) \<or> (\<exists> c' cs. E = c' # cs \<and> c = c\<^sub>1 \<and> c\<^sub>2 = cxt_to_stmt cs c')"
  apply (cases E)
   apply (metis cxt_to_stmt.simps(1))
  by (metis Stmt.simps(3) cxt_to_stmt.simps(2))

inductive_cases seq_elim' [elim]: "(c\<^sub>1 ;; c\<^sub>2, mem) \<leadsto>\<^sub>s (c', mem')"

lemma stop_no_eval: "\<not> (\<langle>Stop, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w)"
  apply auto
  apply (erule eval_elim)
    apply (metis cxt_inv_stop stop_no_eval')
   apply (metis Stmt.simps(41))
  by (metis Stmt.simps(35) cxt_inv_stop)

lemma seq_stop_elim [elim]:
  "\<langle>Stop ;; c, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<Longrightarrow> c' = c \<and> mds' = mds \<and> mem' = mem"
  apply (erule eval_elim)
    apply clarify
    apply (metis (no_types) cxt_seq_elim cxt_to_stmt.simps(1) seq_elim' stop_no_eval')
   apply (metis Stmt.inject(3) stop_no_eval)
  by (metis Stmt.distinct(23) Stmt.distinct(29) cxt_seq_elim)

lemma cxt_stmt_seq:
  "c ;; cxt_to_stmt E c' = cxt_to_stmt (c' # E) c"
  by (metis cxt_to_stmt.simps(2))


lemma seq_elim [elim]:
  "\<lbrakk> \<langle>c\<^sub>1 ;; c\<^sub>2, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w ; c\<^sub>1 \<noteq> Stop \<rbrakk> \<Longrightarrow>
  (\<exists> c\<^sub>1'. \<langle>c\<^sub>1, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c\<^sub>1', mds', mem'\<rangle>\<^sub>w \<and> c' = c\<^sub>1' ;; c\<^sub>2)"
  apply (erule eval_elim)
    apply clarify
    apply (drule cxt_seq_elim)
    apply (erule disjE)
     apply (metis seq_elim')
    apply auto
   apply (metis cxt_to_stmt.simps(1) eval\<^sub>w.unannotated)
  apply (subgoal_tac "c\<^sub>1 = (c@[mu])")
   apply simp
   apply (drule cxt_seq_elim)
   apply (metis Stmt.distinct(23) cxt_stmt_seq cxt_to_stmt.simps(1) eval\<^sub>w.decl)
  by (metis Stmt.distinct(23) cxt_seq_elim)

lemma stop_cxt: "Stop = cxt_to_stmt E c \<Longrightarrow> c = Stop"
  by (metis Stmt.simps(41) cxt_to_stmt.simps(1) cxt_to_stmt.simps(2) neq_Nil_conv)

end

end
