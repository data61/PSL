(*
Title: Value-Dependent SIFUM-Type-Systems
Authors: Toby Murray, Robert Sison, Edward Pierzchalski, Christine Rizkallah
(Based on the SIFUM-Type-Systems AFP entry, whose authors
 are: Sylvia Grewe, Heiko Mantel, Daniel Schoepe)
*)
section \<open>Language for Instantiating the SIFUM-Security Property\<close>

theory Language
imports Preliminaries
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
  | Await "'bexp" "('var, 'aexp, 'bexp) Stmt"
  | Stop

type_synonym ('var, 'aexp, 'bexp) EvalCxt = "('var, 'aexp, 'bexp) Stmt list"

locale sifum_lang_no_dma =
  fixes eval\<^sub>A :: "('Var, 'Val) Mem \<Rightarrow> 'AExp \<Rightarrow> 'Val"
  fixes eval\<^sub>B :: "('Var, 'Val) Mem \<Rightarrow> 'BExp \<Rightarrow> bool"
  fixes aexp_vars :: "'AExp \<Rightarrow> 'Var set"
  fixes bexp_vars :: "'BExp \<Rightarrow> 'Var set"
  assumes Var_finite : "finite {(x :: 'Var). True}"
  assumes eval_vars_det\<^sub>A : "\<lbrakk> \<forall> x \<in> aexp_vars e. mem\<^sub>1 x = mem\<^sub>2 x \<rbrakk> \<Longrightarrow> eval\<^sub>A mem\<^sub>1 e = eval\<^sub>A mem\<^sub>2 e"
  assumes eval_vars_det\<^sub>B : "\<lbrakk> \<forall> x \<in> bexp_vars b. mem\<^sub>1 x = mem\<^sub>2 x \<rbrakk> \<Longrightarrow> eval\<^sub>B mem\<^sub>1 b = eval\<^sub>B mem\<^sub>2 b"

locale sifum_lang = sifum_lang_no_dma eval\<^sub>A eval\<^sub>B aexp_vars bexp_vars
  for eval\<^sub>A :: "('Var, 'Val) Mem \<Rightarrow> 'AExp \<Rightarrow> 'Val"
  and eval\<^sub>B :: "('Var, 'Val) Mem \<Rightarrow> 'BExp \<Rightarrow> bool"
  and aexp_vars :: "'AExp \<Rightarrow> 'Var set"
  and bexp_vars :: "'BExp \<Rightarrow> 'Var set"+
  fixes dma :: "'Var \<Rightarrow> Sec"

context sifum_lang_no_dma
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

notation (Rule output)
  Await ("await _ do _ done")

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

lemma cond:
  "((If b t e, mem), (if eval\<^sub>B mem b then t else e, mem)) \<in> eval\<^sub>w_simple"
  apply(case_tac "eval\<^sub>B mem b")
   apply(auto intro: eval\<^sub>w_simple.intros)
  done

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

lemma rtrancl_mono_proof[mono]:
  "(\<And>a b. x a b \<longrightarrow> y a b) \<Longrightarrow> rtranclp x a b \<longrightarrow> rtranclp y a b"
  apply (rule impI, rotate_tac, induct rule: rtranclp.induct)
   apply simp_all
  apply (metis rtranclp.intros)
  done

lemma trancl_mono_proof[mono]:
  "(\<And>a b. x a b \<longrightarrow> y a b) \<Longrightarrow> tranclp x a b \<longrightarrow> tranclp y a b"
  apply (rule impI, rotate_tac, induct rule: tranclp.induct)
   apply simp_all
   apply blast
  by fastforce

inductive no_await :: "('Var, 'AExp, 'BExp) Stmt \<Rightarrow> bool" where
  "no_await (x \<leftarrow> e)" |
  "no_await c1 \<Longrightarrow> no_await c2 \<Longrightarrow> no_await (c1 ;; c2)" |
  "no_await c1 \<Longrightarrow> no_await c2 \<Longrightarrow> no_await (If b c1 c2)" |
  "no_await c \<Longrightarrow> no_await (While b c)" |
  "no_await Skip" |
  "no_await Stop" |
  "no_await c \<Longrightarrow> no_await (c@[m])"

inductive is_final :: "('Var, 'AExp, 'BExp) Stmt \<Rightarrow> bool" where
  "is_final Stop" |
  "is_final c \<Longrightarrow> is_final (c@[m])"

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
         (\<langle>cxt_to_stmt E (ModeDecl c mu), mds, mem\<rangle>\<^sub>w, \<langle>cxt_to_stmt E c', mds', mem'\<rangle>\<^sub>w) \<in> eval\<^sub>w" |
(* This is added instead of defining eval\<^sub>p -- see next comment*)
  await: "\<lbrakk>eval\<^sub>B mem b; no_await c\<^sub>1;
         (\<langle>c\<^sub>1, mds, mem\<rangle>\<^sub>w, \<langle>c\<^sub>2, mds', mem'\<rangle>\<^sub>w) \<in> eval\<^sub>w\<^sup>+;
         is_final c\<^sub>2\<rbrakk> \<Longrightarrow>
         (\<langle>Await b c\<^sub>1, mds, mem\<rangle>\<^sub>w, \<langle>c\<^sub>2, mds', mem'\<rangle>\<^sub>w) \<in> eval\<^sub>w"

abbreviation eval\<^sub>w_plus :: "
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
                  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow> bool" ("_ \<leadsto>\<^sub>w\<^sup>+ _") where
"ctx \<leadsto>\<^sub>w\<^sup>+ ctx' \<equiv> (ctx, ctx') \<in> eval\<^sub>w\<^sup>+"
  
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
  by (metis Stmt.simps(23) cxt_inv)

lemma cxt_inv_stop:
  "cxt_to_stmt E c = Stop \<Longrightarrow> c = Stop \<and> E = []"
  by (metis Stmt.simps(49) cxt_inv)

lemma cxt_inv_if:
  "cxt_to_stmt E c = If e p q \<Longrightarrow> c = If e p q \<and> E = []"
  by (metis Stmt.simps(43) cxt_inv)
  
lemma ctx_inv_anno:
  "cxt_to_stmt E c = c'@[mu] \<Longrightarrow> c = c'@[mu] \<and> E = []"
  using cxt_inv by blast 
  
lemma cxt_inv_await:
  "cxt_to_stmt E c = Await e p \<Longrightarrow> c = Await e p  \<and> E = []"
  by (metis Stmt.simps(47) cxt_inv)

lemma cxt_inv_while:
  "cxt_to_stmt E c = While e p \<Longrightarrow> c = While e p \<and> E = []"
  by (metis Stmt.simps(45) cxt_inv)

lemma skip_elim [elim]:
  "\<langle>Skip, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<Longrightarrow> c' = Stop \<and> mds = mds' \<and> mem = mem'"
  apply (erule eval_elim)
     apply (metis (lifting) cxt_inv_skip cxt_to_stmt.simps(1) skip_elim')
    apply (metis Stmt.simps(24))
   apply (metis Stmt.simps(21) cxt_inv_skip)
  by simp

lemma assign_elim [elim]:
  "\<langle>x \<leftarrow> e, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<Longrightarrow> c' = Stop \<and> mds = mds' \<and> mem' = mem (x := eval\<^sub>A mem e)"
  apply (erule eval_elim)
     apply (rename_tac c c'a E)
     apply (subgoal_tac "c = x \<leftarrow> e \<and> E = []")
      apply force 
     apply auto
      apply (metis cxt_inv_assign)
     apply (metis cxt_inv_assign)
    apply (metis Stmt.simps(9) cxt_inv_assign)
   apply (metis Stmt.simps(9) cxt_inv_assign)
  by (metis Stmt.simps(9) cxt_inv_assign)

inductive_cases if_elim' [elim!]: "(If b p q, mem) \<leadsto>\<^sub>s (c', mem')"

lemma if_elim [elim]:
  "\<And> P.
    \<lbrakk> \<langle>If b p q, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w ;
     \<lbrakk> c' = p; mem' = mem ; mds' = mds ; eval\<^sub>B mem b \<rbrakk> \<Longrightarrow> P ;
     \<lbrakk> c' = q; mem' = mem ; mds' = mds ; \<not> eval\<^sub>B mem b \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (erule eval_elim)
     apply (metis (no_types) cxt_inv_if cxt_to_stmt.simps(1) if_elim')
    apply (metis Stmt.simps(43))
   apply (metis Stmt.simps(35) cxt_inv_if)
  by simp

inductive_cases await_elim' [elim!]: "\<langle>Await b p, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c',mds', mem'\<rangle>\<^sub>w"

inductive_cases while_elim' [elim!]: "(While e c, mem) \<leadsto>\<^sub>s (c', mem')"

lemma while_elim [elim]:
  "\<lbrakk> \<langle>While e c, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<rbrakk> \<Longrightarrow> c' = If e (c ;; While e c) Stop \<and> mds' = mds \<and> mem' = mem"
  apply (erule eval_elim)
     apply (metis (no_types) cxt_inv_while cxt_to_stmt.simps(1) while_elim')
    apply (metis Stmt.simps(45))
   apply (metis (lifting) Stmt.simps(37) cxt_inv_while)
  by simp

inductive_cases upd_elim' [elim]: "(c@[upd], mem) \<leadsto>\<^sub>s (c', mem')"

lemma upd_elim [elim]:
  "\<langle>c@[upd], mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<Longrightarrow> \<langle>c, update_modes upd mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w"
  apply (erule eval_elim)
     apply (metis (lifting) Stmt.simps(33) cxt_inv upd_elim')
    apply (metis Stmt.simps(34))
   apply (metis (lifting) Stmt.simps(2) Stmt.simps(33) cxt_inv cxt_to_stmt.simps(1))
  by simp

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
    apply (metis Stmt.simps(49))
   apply (metis Stmt.simps(41) cxt_inv_stop)
  by simp

lemma seq_stop_elim [elim]:
  "\<langle>Stop ;; c, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<Longrightarrow> c' = c \<and> mds' = mds \<and> mem' = mem"
  apply (erule eval_elim)
     apply clarify
     apply (metis (no_types) cxt_seq_elim cxt_to_stmt.simps(1) seq_elim' stop_no_eval')
    apply (metis Stmt.inject(3) stop_no_eval)
   apply (metis Stmt.distinct(28) Stmt.distinct(36) cxt_seq_elim)
  by simp

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
     apply blast 
    apply auto
   apply (metis cxt_to_stmt.simps(1) eval\<^sub>w.unannotated)
  apply (subgoal_tac "c\<^sub>1 = c@[mu]")
   apply simp
   apply (drule cxt_seq_elim)
   apply (metis Stmt.distinct(27) cxt_stmt_seq cxt_to_stmt.simps(1) eval\<^sub>w.decl)
  using cxt_seq_elim by blast

lemma stop_cxt: "Stop = cxt_to_stmt E c \<Longrightarrow> c = Stop"
  by (metis Stmt.simps(50) cxt_to_stmt.simps(1) cxt_to_stmt.simps(2) neq_Nil_conv)

(* Additional helper lemmas added by TobyM and RobS *)

lemmas decl_eval\<^sub>w = decl[OF unannotated, OF skip, where E="[]", simplified, where E1="[]", simplified]
lemmas seq_stop_eval\<^sub>w = unannotated[OF seq_stop, where E="[]", simplified]
lemmas assign_eval\<^sub>w = unannotated[OF assign, where E="[]", simplified]
lemmas if_eval\<^sub>w = unannotated[OF cond, where E="[]", simplified]
lemmas if_false_eval\<^sub>w = unannotated[OF if_false, where E="[]", simplified]
lemmas skip_eval\<^sub>w = unannotated[OF skip, where E="[]", simplified]
lemmas while_eval\<^sub>w = unannotated[OF while, where E="[]", simplified]

lemma decl_eval\<^sub>w':
  assumes mem_unchanged: "mem' = mem"
  assumes upd: "mds' = update_modes upd mds"
  shows "(\<langle>Skip@[upd], mds, mem\<rangle>\<^sub>w, \<langle>Stop, mds', mem'\<rangle>\<^sub>w) \<in> eval\<^sub>w"
  using assms decl_eval\<^sub>w
  by auto

lemma assign_eval\<^sub>w':
  "\<lbrakk>mds = mds'; mem' = mem(x := eval\<^sub>A mem e)\<rbrakk> \<Longrightarrow>
  \<langle>x \<leftarrow> e, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>Stop, mds', mem'\<rangle>\<^sub>w"
  using assign_eval\<^sub>w
  by simp

(* Following the naming convention, but we actually apply these as dest, not elim rules... *)

lemma seq_decl_elim:
  "\<langle>(Skip@[upd]) ;; c, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<Longrightarrow>
   c' = Stop ;; c \<and> mem' = mem \<and> mds' = update_modes upd mds"
  apply(drule seq_elim, simp)
  apply(erule exE, clarsimp)
  apply(drule upd_elim)
  apply(drule skip_elim, clarsimp)
  done

lemma seq_assign_elim:
  "\<langle>(x \<leftarrow> e) ;; c, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<Longrightarrow>
   c' = Stop ;; c \<and> mds' = mds \<and> mem' = mem(x := eval\<^sub>A mem e)"
  apply(drule seq_elim, simp)
  apply(erule exE, clarsimp)
  apply(drule assign_elim, clarsimp)
  done

lemma no_await_trans: 
  "\<lbrakk> no_await c; \<langle>c, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c', mds', mem'\<rangle>\<^sub>w \<rbrakk> \<Longrightarrow> no_await c'"
  apply (induct arbitrary: c' mds rule: "no_await.induct")
        using assign_elim "no_await.simps" apply blast
       apply (rename_tac c1 c2 c3 mds)
       apply (case_tac "c1 = Stop")
        apply (simp, frule seq_stop_elim, clarsimp)
        using seq_elim no_await.intros apply metis
       using if_elim no_await.intros apply blast
      apply (frule while_elim, clarsimp)
     apply (rename_tac c b)
     apply (subgoal_tac "no_await (While b c)")
      apply (subgoal_tac "no_await (c ;; While b c)")
       using no_await.intros apply blast
      using no_await.intros apply blast
     using no_await.intros apply blast
    using no_await.intros skip_elim apply fast
   using no_await.intros stop_no_eval apply fast
  using no_await.intros upd_elim by fast

lemma no_await_no_await[elim]: "\<lbrakk> no_await c \<rbrakk> \<Longrightarrow> c \<noteq> Await b c'"
  using no_await.cases Stmt.distinct by fast

lemma no_await_trancl_impl: 
  "\<lbrakk>ctx \<leadsto>\<^sub>w\<^sup>+ ctx'\<rbrakk> \<Longrightarrow> no_await (fst (fst ctx)) \<longrightarrow> no_await (fst (fst ctx'))"
  apply (erule trancl.induct, clarsimp)
   using no_await_trans apply blast
  apply clarsimp
  using no_await_trans by blast
  
lemma no_await_trancl: 
  "\<lbrakk>ctx \<leadsto>\<^sub>w\<^sup>+ ctx'; no_await (fst (fst ctx))\<rbrakk> \<Longrightarrow> no_await (fst (fst ctx'))" 
  using no_await_trancl_impl by blast

lemma await_elim: 
  "\<lbrakk>\<langle>Await b c\<^sub>1, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w \<langle>c\<^sub>2, mds', mem'\<rangle>\<^sub>w\<rbrakk> \<Longrightarrow> 
    eval\<^sub>B mem b \<and> no_await c\<^sub>1 \<and> is_final c\<^sub>2  \<and>
    \<langle>c\<^sub>1, mds, mem\<rangle>\<^sub>w \<leadsto>\<^sub>w\<^sup>+ \<langle>c\<^sub>2, mds', mem'\<rangle>\<^sub>w"
  apply (erule "eval\<^sub>w.cases"; clarsimp)
   apply (subgoal_tac "cxt_to_stmt E c = Await b c\<^sub>1")
    apply (drule cxt_inv_await)
    using "eval\<^sub>w_simple.cases" apply force
   apply simp
  by (metis Stmt.distinct(33) cxt_inv_await)
  
end

end
