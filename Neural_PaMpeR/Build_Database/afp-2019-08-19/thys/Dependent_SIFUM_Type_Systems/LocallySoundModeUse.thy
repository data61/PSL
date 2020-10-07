(*
TiTitle: Value-Dependent SIFUM-Type-Systems
Authors: Toby Murray, Robert Sison, Edward Pierzchalski, Christine Rizkallah
(Based on the SIFUM-Type-Systems AFP entry, whose authors
 are: Sylvia Grewe, Heiko Mantel, Daniel Schoepe)
*)
section \<open>Type System for Ensuring Locally Sound Use of Modes\<close>

theory LocallySoundModeUse
imports Security Language
begin

subsection \<open>Typing Rules\<close>

locale sifum_modes = 
  sifum_lang_no_dma ev\<^sub>A ev\<^sub>B aexp_vars bexp_vars + sifum_security dma \<C>_vars \<C> eval\<^sub>w undefined
  for ev\<^sub>A :: "('Var, 'Val) Mem \<Rightarrow> 'AExp \<Rightarrow> 'Val"
  and ev\<^sub>B :: "('Var, 'Val) Mem \<Rightarrow> 'BExp \<Rightarrow> bool"
  and aexp_vars :: "'AExp \<Rightarrow> 'Var set"
  and bexp_vars :: "'BExp \<Rightarrow> 'Var set"
  and dma :: "('Var,'Val) Mem \<Rightarrow> 'Var \<Rightarrow> Sec"
  and \<C>_vars :: "'Var \<Rightarrow> 'Var set"
  and \<C> :: "'Var set"

context sifum_modes
begin

abbreviation 
  eval_abv_modes :: "(_, 'Var, 'Val) LocalConf \<Rightarrow> (_, _, _) LocalConf \<Rightarrow> bool"
  (infixl "\<leadsto>" 70)
where
  "x \<leadsto> y \<equiv> (x, y) \<in> eval\<^sub>w"

fun 
  update_annos :: "'Var Mds \<Rightarrow> 'Var ModeUpd list \<Rightarrow> 'Var Mds"
  (infix "\<oplus>" 140)
where
  "update_annos mds [] = mds" |
  "update_annos mds (a # as) = update_annos (update_modes a mds) as"

fun 
  annotate :: "('Var, 'AExp, 'BExp) Stmt \<Rightarrow> 'Var ModeUpd list \<Rightarrow> ('Var, 'AExp, 'BExp) Stmt"
  (infix "\<otimes>" 140)
where
  "annotate c [] = c" |
  "annotate c (a # as) = (annotate c as)@[a]"

inductive 
  mode_type :: "'Var Mds \<Rightarrow> ('Var, 'AExp, 'BExp) Stmt \<Rightarrow> 'Var Mds \<Rightarrow> bool" ("\<turnstile> _ { _ } _")
where
  skip: "\<turnstile> mds { Skip \<otimes> annos } (mds \<oplus> annos)" |
  assign: "\<lbrakk> x \<notin> mds GuarNoWrite \<union> mds GuarNoReadOrWrite ; aexp_vars e \<inter> mds GuarNoReadOrWrite = {};
             \<forall>v. (x \<in> \<C>_vars v \<longrightarrow> v \<notin> mds GuarNoWrite \<union> mds GuarNoReadOrWrite) \<and>
                 (\<C>_vars v \<inter> aexp_vars e \<noteq> {} \<longrightarrow> v \<notin> mds GuarNoReadOrWrite)\<rbrakk> \<Longrightarrow>
  \<turnstile> mds { (x \<leftarrow> e) \<otimes> annos } (mds \<oplus> annos)" |
  if_: "\<lbrakk> \<turnstile> (mds \<oplus> annos) { c\<^sub>1 } mds'' ;
          \<turnstile> (mds \<oplus> annos) { c\<^sub>2 } mds'' ;
          bexp_vars e \<inter> mds GuarNoReadOrWrite = {};
          \<forall> v. \<C>_vars v \<inter> bexp_vars e \<noteq> {} \<longrightarrow> v \<notin> mds GuarNoReadOrWrite\<rbrakk> \<Longrightarrow>
        \<turnstile> mds { If e c\<^sub>1 c\<^sub>2 \<otimes> annos } mds''" |
  while: "\<lbrakk> mds' = mds \<oplus> annos ; \<turnstile> mds' { c } mds' ; bexp_vars e \<inter> mds' GuarNoReadOrWrite = {};
            \<forall> v. \<C>_vars v \<inter> bexp_vars e \<noteq> {} \<longrightarrow> v \<notin> mds' GuarNoReadOrWrite\<rbrakk> \<Longrightarrow>
  \<turnstile> mds { While e c \<otimes> annos } mds'" |
  seq: "\<lbrakk> \<turnstile> mds { c\<^sub>1 } mds' ; \<turnstile> mds' { c\<^sub>2 } mds'' \<rbrakk> \<Longrightarrow> \<turnstile> mds { c\<^sub>1 ;; c\<^sub>2 } mds''" |
  sub: "\<lbrakk> \<turnstile> mds\<^sub>2 { c } mds\<^sub>2' ; mds\<^sub>1 \<le> mds\<^sub>2 ; mds\<^sub>2' \<le> mds\<^sub>1' \<rbrakk> \<Longrightarrow>
  \<turnstile> mds\<^sub>1 { c } mds\<^sub>1'"

subsection \<open>Soundness of the Type System\<close>

(* Special case for evaluation with an empty context *)
lemma cxt_eval:
  "\<lbrakk> \<langle>cxt_to_stmt [] c, mds, mem\<rangle> \<leadsto> \<langle>cxt_to_stmt [] c', mds', mem'\<rangle> \<rbrakk> \<Longrightarrow>
  \<langle>c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
  by auto

lemma update_preserves_le:
  "mds\<^sub>1 \<le> mds\<^sub>2 \<Longrightarrow> (mds\<^sub>1 \<oplus> annos) \<le> (mds\<^sub>2 \<oplus> annos)"
proof (induct annos arbitrary: mds\<^sub>1 mds\<^sub>2)
  case Nil
  thus ?case by simp
next
  case (Cons a annos mds\<^sub>1 mds\<^sub>2)
  hence "update_modes a mds\<^sub>1 \<le> update_modes a mds\<^sub>2"
    by (case_tac a, auto simp: le_fun_def)
  with Cons show ?case
    by auto
qed

(* Annotations do not affect doesnt_read and doesnt_modify: *)
lemma doesnt_read_annos:
  "doesnt_read_or_modify c x \<Longrightarrow> doesnt_read_or_modify (c \<otimes> annos) x"
  unfolding doesnt_read_or_modify_def doesnt_read_or_modify_vars_def
  apply clarify
  apply (induct annos)
   apply simp
   apply (metis (lifting))
  apply clarsimp
  apply (rule cxt_eval)
  apply (rule eval\<^sub>w.decl)
  apply (metis cxt_eval eval\<^sub>w.decl upd_elim)+
  done

lemma doesnt_modify_annos:
  "doesnt_modify c x \<Longrightarrow> doesnt_modify (c \<otimes> annos) x"
  unfolding doesnt_modify_def
  apply clarsimp
   apply (induct annos)
    apply simp 
   by (metis annotate.simps(2) upd_elim)
  
(* The following part contains some lemmas about evaluation of
   commands annotated using \<otimes> and characterisations of loc_reach for
   commands. *)

lemma stop_loc_reach:
  "\<lbrakk> \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>Stop, mds, mem\<rangle> \<rbrakk> \<Longrightarrow>
  c' = Stop \<and> mds' = mds"
  apply (induct rule: loc_reach.induct)
  by (auto simp: stop_no_eval)

lemma stop_doesnt_access:
  "doesnt_modify Stop x \<and> doesnt_read_or_modify Stop x"
  unfolding doesnt_modify_def and doesnt_read_or_modify_def doesnt_read_or_modify_vars_def
  using stop_no_eval
  by auto

lemma skip_eval_step:
  "\<langle>Skip \<otimes> annos, mds, mem\<rangle> \<leadsto> \<langle>Stop, mds \<oplus> annos, mem\<rangle>"
  apply (induct annos arbitrary: mds)
   apply simp
   apply (metis cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.skip)
  apply simp
  apply (insert eval\<^sub>w.decl)
  apply (rule cxt_eval)
  apply (rule eval\<^sub>w.decl)
  by auto

lemma skip_eval_elim:
  "\<lbrakk> \<langle>Skip \<otimes> annos, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle> \<rbrakk> \<Longrightarrow> c' = Stop \<and> mds' = mds \<oplus> annos \<and> mem' = mem"
  apply (rule ccontr)
  apply (insert skip_eval_step deterministic)
  apply clarify
  apply clarsimp
    by metis+

lemma skip_doesnt_read:
  "doesnt_read_or_modify (Skip \<otimes> annos) x"
  apply (rule doesnt_read_annos)
  apply (clarsimp simp: doesnt_read_or_modify_def doesnt_read_or_modify_vars_def)
  by (metis annotate.simps(1) skip_elim skip_eval_step)+

lemma skip_doesnt_write:
  "doesnt_modify (Skip \<otimes> annos) x"
  apply (rule doesnt_modify_annos)
  apply (clarsimp simp: doesnt_modify_def)
  by (metis skip_elim)+

lemma skip_loc_reach:
  "\<lbrakk> \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>Skip \<otimes> annos, mds, mem\<rangle> \<rbrakk> \<Longrightarrow>
  (c' = Stop \<and> mds' = (mds \<oplus> annos)) \<or> (c' = Skip \<otimes> annos \<and> mds' = mds)"
  apply (induct rule: loc_reach.induct)
    apply (metis fst_conv snd_conv)
   apply (metis skip_eval_elim stop_no_eval)
  by metis

lemma skip_doesnt_access:
  "\<lbrakk> lc \<in> loc_reach \<langle>Skip \<otimes> annos, mds, mem\<rangle> ; lc = \<langle>c', mds', mem'\<rangle> \<rbrakk> \<Longrightarrow> doesnt_read_or_modify c' x \<and> doesnt_modify c' x"
  apply (subgoal_tac "(c' = Stop \<and> mds' = (mds \<oplus> annos)) \<or> (c' = Skip \<otimes> annos \<and> mds' = mds)")
   apply (rule conjI, erule disjE)
     apply (simp add: doesnt_read_or_modify_def doesnt_read_or_modify_vars_def stop_no_eval)
    apply (metis (lifting) annotate.simps skip_doesnt_read)
   apply (erule disjE)
    apply (simp add: doesnt_modify_def stop_no_eval)
   apply (metis (lifting) annotate.simps skip_doesnt_write)
  by (metis skip_loc_reach)

lemma assign_doesnt_modify:
  "\<lbrakk> x \<noteq> y; x \<notin> \<C>_vars y \<rbrakk> \<Longrightarrow> doesnt_modify ((x \<leftarrow> e) \<otimes> annos) y"
  apply (rule doesnt_modify_annos)
  apply (simp add: doesnt_modify_def)
  by (metis assign_elim fun_upd_apply dma_\<C>_vars)
  
lemma assign_annos_eval:
  "\<langle>(x \<leftarrow> e) \<otimes> annos, mds, mem\<rangle> \<leadsto> \<langle>Stop, mds \<oplus> annos, mem (x := ev\<^sub>A mem e)\<rangle>"
  apply (induct annos arbitrary: mds)
   apply (simp only: annotate.simps update_annos.simps)
   apply (rule cxt_eval)
   apply (rule eval\<^sub>w.unannotated)
   apply (rule eval\<^sub>w_simple.assign)
  apply (rule cxt_eval)
  apply (simp del: cxt_to_stmt.simps)
  apply (rule eval\<^sub>w.decl)
  by auto

lemma assign_annos_eval_elim:
  "\<lbrakk> \<langle>(x \<leftarrow> e) \<otimes> annos, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle> \<rbrakk> \<Longrightarrow>
  c' = Stop \<and> mds' = mds \<oplus> annos"
  apply (rule ccontr)
  apply (insert deterministic assign_annos_eval)
  apply clarsimp
  by (metis (lifting))

lemma mem_upd_commute:
  "\<lbrakk> x \<noteq> y \<rbrakk> \<Longrightarrow> mem (x := v\<^sub>1, y := v\<^sub>2) = mem (y := v\<^sub>2, x := v\<^sub>1)"
  by (metis fun_upd_twist)

lemma assign_doesnt_read:
  "\<lbrakk> y \<noteq> x; y \<notin> aexp_vars e; x \<notin> \<C>_vars y; \<C>_vars y \<inter> aexp_vars e = {} \<rbrakk> \<Longrightarrow> doesnt_read_or_modify ((x \<leftarrow> e) \<otimes> annos) y"
  apply (rule doesnt_read_annos)
proof -
  assume  "y \<noteq> x"
          "y \<notin> aexp_vars e"
          "x \<notin> \<C>_vars y"
          "\<C>_vars y \<inter> aexp_vars e = {}"
  thus "doesnt_read_or_modify (x \<leftarrow> e) y"
    unfolding doesnt_read_or_modify_def doesnt_read_or_modify_vars_def
    apply -
    apply (rule allI)+
    apply (rename_tac mds mem c' mds' mem')
    apply (rule impI)
    apply (subgoal_tac "c' = Stop \<and> mds' = mds \<and> mem' = mem (x := ev\<^sub>A mem e)")
     apply simp
     apply clarify
     apply (rule conjI)
      apply clarify
      apply (subgoal_tac "mem (x := ev\<^sub>A mem e, y := v) = mem (y := v, x := ev\<^sub>A mem e)")
       apply simp
       apply (rule cxt_eval)
       apply (rule eval\<^sub>w.unannotated)      
       apply (metis eval\<^sub>w_simple.assign eval_vars_det\<^sub>A fun_upd_apply)
      apply (metis mem_upd_commute)
     apply clarify
     apply (rename_tac va v)
     apply (subgoal_tac "mem (x := ev\<^sub>A mem e, va := v) = mem (va := v, x := ev\<^sub>A mem e)")
      apply simp
      apply (rule cxt_eval)
      apply (rule eval\<^sub>w.unannotated)
      apply (subgoal_tac "va \<notin> aexp_vars e")
       apply (metis eval\<^sub>w_simple.assign eval_vars_det\<^sub>A fun_upd_apply)
      apply blast
     apply (metis mem_upd_commute)
    apply (metis assign_elim)
    done
qed

lemma assign_loc_reach:
  "\<lbrakk> \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>(x \<leftarrow> e) \<otimes> annos, mds, mem\<rangle> \<rbrakk> \<Longrightarrow>
  (c' = Stop \<and> mds' = (mds \<oplus> annos)) \<or> (c' = (x \<leftarrow> e) \<otimes> annos \<and> mds' = mds)"
  apply (induct rule: loc_reach.induct)
    apply simp_all
  by (metis assign_annos_eval_elim stop_no_eval)

lemma if_doesnt_modify:
  "doesnt_modify (If e c\<^sub>1 c\<^sub>2 \<otimes> annos) x"
  apply (rule doesnt_modify_annos)
  by (auto simp: doesnt_modify_def)

lemma vars_eval\<^sub>B:
  "x \<notin> bexp_vars e \<Longrightarrow> ev\<^sub>B mem e = ev\<^sub>B (mem (x := v)) e"
  by (metis (lifting) eval_vars_det\<^sub>B fun_upd_other)

lemma if_doesnt_read:
  "x \<notin> bexp_vars e \<Longrightarrow> \<C>_vars x \<inter> bexp_vars e = {} \<Longrightarrow> doesnt_read_or_modify (If e c\<^sub>1 c\<^sub>2 \<otimes> annos) x"
  apply (rule doesnt_read_annos)
  apply (clarsimp simp: doesnt_read_or_modify_def doesnt_read_or_modify_vars_def, safe)
   apply (rename_tac mds mem c' mds' mem' v)
   apply (case_tac "ev\<^sub>B mem e")
    apply (subgoal_tac "c' = c\<^sub>1 \<and> mds' = mds \<and> mem' = mem")
     prefer 2
     apply auto[1]
    apply clarsimp
    apply (rule cxt_eval)
    apply (rule eval\<^sub>w.unannotated)
    apply (rule eval\<^sub>w_simple.if_true)
    apply (metis (lifting) vars_eval\<^sub>B)
   apply (subgoal_tac "c' = c\<^sub>2 \<and> mds' = mds \<and> mem' = mem")
    prefer 2
    apply auto[1]
   apply clarsimp
   apply (rule cxt_eval)
   apply (rule eval\<^sub>w.unannotated)
   apply (rule eval\<^sub>w_simple.if_false)
   apply (metis (lifting) vars_eval\<^sub>B)
  apply (rename_tac mds mem c' mds' mem' va v)
  apply (case_tac "ev\<^sub>B mem e")
   apply (subgoal_tac "c' = c\<^sub>1 \<and> mds' = mds \<and> mem' = mem")
    prefer 2
    apply auto[1]
   apply clarsimp
   apply (rule cxt_eval)
   apply (rule eval\<^sub>w.unannotated)
   apply (rule eval\<^sub>w_simple.if_true)
   apply (subgoal_tac "va \<notin> bexp_vars e")
    apply (metis (lifting) vars_eval\<^sub>B)
   apply blast
  apply (subgoal_tac "c' = c\<^sub>2 \<and> mds' = mds \<and> mem' = mem")
   prefer 2
   apply auto[1]
  apply clarsimp
  apply (rule cxt_eval)
  apply (rule eval\<^sub>w.unannotated)
  apply (rule eval\<^sub>w_simple.if_false)
  apply (subgoal_tac "va \<notin> bexp_vars e")
   apply (metis (lifting) vars_eval\<^sub>B)
  apply blast
  done
  
lemma if_eval_true:
  "\<lbrakk> ev\<^sub>B mem e \<rbrakk> \<Longrightarrow>
  \<langle>If e c\<^sub>1 c\<^sub>2 \<otimes> annos, mds, mem\<rangle> \<leadsto> \<langle>c\<^sub>1, mds \<oplus> annos, mem\<rangle>"
  apply (induct annos arbitrary: mds)
   apply simp
   apply (metis cxt_eval eval\<^sub>w.unannotated eval\<^sub>w_simple.if_true)
  by (metis annotate.simps(2) cxt_eval eval\<^sub>w.decl update_annos.simps(2))

lemma if_eval_false:
  "\<lbrakk> \<not> ev\<^sub>B mem e \<rbrakk> \<Longrightarrow>
  \<langle>If e c\<^sub>1 c\<^sub>2 \<otimes> annos, mds, mem\<rangle> \<leadsto> \<langle>c\<^sub>2, mds \<oplus> annos, mem\<rangle>"
  apply (induct annos arbitrary: mds)
   apply simp
   apply (metis cxt_eval eval\<^sub>w.unannotated eval\<^sub>w_simple.if_false)
  by (metis annotate.simps(2) cxt_eval eval\<^sub>w.decl update_annos.simps(2))

lemma if_eval_elim:
  "\<lbrakk> \<langle>If e c\<^sub>1 c\<^sub>2 \<otimes> annos, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle> \<rbrakk> \<Longrightarrow>
  ((c' = c\<^sub>1 \<and> ev\<^sub>B mem e) \<or> (c' = c\<^sub>2 \<and> \<not> ev\<^sub>B mem e)) \<and> mds' = mds \<oplus> annos \<and> mem' = mem"
  apply (rule ccontr)
  apply (cases "ev\<^sub>B mem e")
   apply (insert if_eval_true deterministic)
   apply blast
  using if_eval_false deterministic
  by blast

lemma if_eval_elim':
  "\<lbrakk> \<langle>If e c\<^sub>1 c\<^sub>2, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle> \<rbrakk> \<Longrightarrow>
  ((c' = c\<^sub>1 \<and> ev\<^sub>B mem e) \<or> (c' = c\<^sub>2 \<and> \<not> ev\<^sub>B mem e)) \<and> mds' = mds \<and> mem' = mem"
  using if_eval_elim [where annos = "[]"]
  by auto

lemma loc_reach_refl':
  "\<langle>c, mds, mem\<rangle> \<in> loc_reach \<langle>c, mds, mem\<rangle>"
  apply (subgoal_tac "\<exists> lc. lc \<in> loc_reach lc \<and> lc = \<langle>c, mds, mem\<rangle>")
   apply blast
  by (metis loc_reach.refl fst_conv snd_conv)

lemma if_loc_reach:
  "\<lbrakk> \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>If e c\<^sub>1 c\<^sub>2 \<otimes> annos, mds, mem\<rangle> \<rbrakk> \<Longrightarrow>
  (c' = If e c\<^sub>1 c\<^sub>2 \<otimes> annos \<and> mds' = mds) \<or>
  (\<exists> mem''. \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>1, mds \<oplus> annos, mem''\<rangle>) \<or>
  (\<exists> mem''. \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>2, mds \<oplus> annos, mem''\<rangle>)"
  apply (induct rule: loc_reach.induct)
    apply (metis fst_conv snd_conv)
   apply (erule disjE)
    apply (erule conjE)
    apply simp
    apply (drule if_eval_elim)
    apply (erule conjE)+
    apply (erule disjE)
     apply (erule conjE)
     apply simp
     apply (metis loc_reach_refl')
    apply (metis loc_reach_refl')
   apply (metis loc_reach.step)
  by (metis loc_reach.mem_diff)

lemma if_loc_reach':
  "\<lbrakk> \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>If e c\<^sub>1 c\<^sub>2, mds, mem\<rangle> \<rbrakk> \<Longrightarrow>
  (c' = If e c\<^sub>1 c\<^sub>2 \<and> mds' = mds) \<or>
  (\<exists> mem''. \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>1, mds, mem''\<rangle>) \<or>
  (\<exists> mem''. \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>2, mds, mem''\<rangle>)"
  using if_loc_reach [where annos = "[]"]
  by simp

lemma seq_loc_reach:
  "\<lbrakk> \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>1 ;; c\<^sub>2, mds, mem\<rangle> \<rbrakk> \<Longrightarrow>
  (\<exists> c''. c' = c'' ;; c\<^sub>2 \<and> \<langle>c'', mds', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>1, mds, mem\<rangle>) \<or>
  (\<exists> c'' mds'' mem''. \<langle>Stop, mds'', mem''\<rangle> \<in> loc_reach \<langle>c\<^sub>1, mds, mem\<rangle> \<and> 
                      \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>2, mds'', mem''\<rangle>)"
  apply (induct rule: loc_reach.induct)
    apply simp
    apply (metis  loc_reach_refl')
   apply simp
   apply (metis (no_types) loc_reach.step loc_reach_refl' seq_elim seq_stop_elim)
  by (metis (lifting) loc_reach.mem_diff)

lemma seq_doesnt_read:
  "\<lbrakk> doesnt_read_or_modify c x \<rbrakk> \<Longrightarrow> doesnt_read_or_modify (c ;; c') x"
  apply (clarsimp simp: doesnt_read_or_modify_def doesnt_read_or_modify_vars_def | safe)+
   apply (rename_tac mds mem c'a mds' mem' v)
   apply (case_tac "c = Stop")
    apply clarsimp
    apply (subgoal_tac "c'a = c' \<and> mds' = mds \<and> mem' = mem")
     apply simp
     apply (metis cxt_eval eval\<^sub>w.unannotated eval\<^sub>w_simple.seq_stop)
    apply (metis (lifting) seq_stop_elim)
   apply (metis (lifting, no_types) eval\<^sub>w.seq seq_elim)
  apply (rename_tac mds mem c'a mds' mem' va v)
  apply (case_tac "c = Stop")
   apply clarsimp
   apply (subgoal_tac "c'a = c' \<and> mds' = mds \<and> mem' = mem")
    apply simp
    apply (metis cxt_eval eval\<^sub>w.unannotated eval\<^sub>w_simple.seq_stop)
   apply (metis (lifting) seq_stop_elim)
  apply (metis (lifting, no_types) eval\<^sub>w.seq seq_elim)
  done
  
lemma seq_doesnt_modify:
  "\<lbrakk> doesnt_modify c x \<rbrakk> \<Longrightarrow> doesnt_modify (c ;; c') x"
  apply (clarsimp simp: doesnt_modify_def | safe)+
   apply (case_tac "c = Stop")
    apply clarsimp
    apply (metis (lifting) seq_stop_elim)
   apply (metis (no_types) seq_elim)
  apply (case_tac "c = Stop")
   apply clarsimp
   apply (metis (lifting) seq_stop_elim)
  apply (metis (no_types) seq_elim)
  done
  
inductive_cases seq_stop_elim': "\<langle>Stop ;; c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"

lemma seq_stop_elim: "\<langle>Stop ;; c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle> \<Longrightarrow>
  c' = c \<and> mds' = mds \<and> mem' = mem"
  apply (erule seq_stop_elim')
    apply (metis eval\<^sub>w.unannotated seq_stop_elim)
   apply (metis eval\<^sub>w.seq seq_stop_elim)
  by (metis (lifting) Stmt.simps(34) Stmt.simps(42) cxt_seq_elim)

lemma seq_split:
  "\<lbrakk> \<langle>Stop, mds', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>1 ;; c\<^sub>2, mds, mem\<rangle> \<rbrakk> \<Longrightarrow>
  \<exists> mds'' mem''. \<langle>Stop, mds'', mem''\<rangle> \<in> loc_reach \<langle>c\<^sub>1, mds, mem\<rangle> \<and>
                 \<langle>Stop, mds', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>2, mds'', mem''\<rangle>"
  apply (drule seq_loc_reach)
  by (metis Stmt.simps(49))

lemma while_eval:
  "\<langle>While e c \<otimes> annos, mds, mem\<rangle> \<leadsto> \<langle>(If e (c ;; While e c) Stop), mds \<oplus> annos, mem\<rangle>"
  apply (induct annos arbitrary: mds)
   apply simp
   apply (rule cxt_eval)
   apply (rule eval\<^sub>w.unannotated)
   apply (metis (lifting) eval\<^sub>w_simple.while)
  apply simp
  by (metis cxt_eval eval\<^sub>w.decl)

lemma while_eval':
  "\<langle>While e c, mds, mem\<rangle> \<leadsto> \<langle>If e (c ;; While e c) Stop, mds, mem\<rangle>"
  using while_eval [where annos = "[]"]
  by auto

lemma while_eval_elim:
  "\<lbrakk> \<langle>While e c \<otimes> annos, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle> \<rbrakk> \<Longrightarrow>
   (c' = If e (c ;; While e c) Stop \<and> mds' = mds \<oplus> annos \<and> mem' = mem)"
  apply (rule ccontr)
  apply (insert while_eval deterministic)
  by blast

lemma while_eval_elim':
  "\<lbrakk> \<langle>While e c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle> \<rbrakk> \<Longrightarrow>
   (c' = If e (c ;; While e c) Stop \<and> mds' = mds \<and> mem' = mem)"
  using while_eval_elim [where annos = "[]"]
  by auto

lemma while_doesnt_read:
  "\<lbrakk> x \<notin> bexp_vars e \<rbrakk> \<Longrightarrow> doesnt_read_or_modify (While e c \<otimes> annos) x"
  unfolding doesnt_read_or_modify_def doesnt_read_or_modify_vars_def
  using while_eval while_eval_elim
  by metis

lemma while_doesnt_modify:
  "doesnt_modify (While e c \<otimes> annos) x"
  unfolding doesnt_modify_def
  using while_eval_elim
  by metis

(* TODO: try to find a better solution to this: *)
lemma disjE3:
  "\<lbrakk> A \<or> B \<or> C ; A \<Longrightarrow> P ; B \<Longrightarrow> P ; C \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto

lemma disjE5:
  "\<lbrakk> A \<or> B \<or> C \<or> D \<or> E ; A \<Longrightarrow> P ; B \<Longrightarrow> P ; C \<Longrightarrow> P ; D \<Longrightarrow> P ; E \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto

lemma if_doesnt_read':
  "x \<notin> bexp_vars e \<Longrightarrow> \<C>_vars x \<inter> bexp_vars e = {} \<Longrightarrow> doesnt_read_or_modify (If e c\<^sub>1 c\<^sub>2) x"
  using if_doesnt_read [where annos = "[]"]
  by auto

theorem mode_type_sound:
  assumes typeable: "\<turnstile> mds\<^sub>1 { c } mds\<^sub>1'"
  assumes mode_le: "mds\<^sub>2 \<le> mds\<^sub>1"
  shows "\<forall> mem. (\<langle>Stop, mds\<^sub>2', mem'\<rangle> \<in> loc_reach \<langle>c, mds\<^sub>2, mem\<rangle> \<longrightarrow> mds\<^sub>2' \<le> mds\<^sub>1') \<and> 
                locally_sound_mode_use \<langle>c, mds\<^sub>2, mem\<rangle>"
  using typeable mode_le
proof (induct arbitrary: mds\<^sub>2 mds\<^sub>2' mem' mem rule: mode_type.induct)
  case (skip mds annos)
  thus ?case
    apply (clarsimp, intro conjI)
     apply (metis (lifting) skip_eval_step skip_loc_reach stop_no_eval update_preserves_le)
    apply (simp add: locally_sound_mode_use_def)
    by (metis annotate.simps skip_doesnt_access)
next
  case (assign x mds e annos)
  hence "\<forall> mem. locally_sound_mode_use \<langle>(x \<leftarrow> e) \<otimes> annos, mds\<^sub>2, mem\<rangle>"
    unfolding locally_sound_mode_use_def
  proof (clarify)
    fix mem c' mds' mem' y
    assume asm: "\<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>(x \<leftarrow> e) \<otimes> annos, mds\<^sub>2, mem\<rangle>"
    hence "c' = (x \<leftarrow> e) \<otimes> annos \<and> mds' = mds\<^sub>2 \<or> c' = Stop \<and> mds' = mds\<^sub>2 \<oplus> annos"
      using assign_loc_reach by blast
    thus "(y \<in> mds' GuarNoReadOrWrite \<longrightarrow> doesnt_read_or_modify c' y) \<and>
          (y \<in> mds' GuarNoWrite \<longrightarrow> doesnt_modify c' y)"
    proof
      assume "c' = (x \<leftarrow> e) \<otimes> annos \<and> mds' = mds\<^sub>2"
      thus ?thesis
      proof (safe)
        assume nin: "y \<in> mds\<^sub>2 GuarNoReadOrWrite"
        hence nin: "y \<in> mds GuarNoReadOrWrite"
          using assign.prems unfolding le_fun_def by blast
        hence "y \<notin> aexp_vars e"
          by (metis IntD2 IntI assign.hyps(2) assign.prems empty_iff inf_apply le_iff_inf)
        moreover from nin assign.hyps(3) have "\<C>_vars y \<inter> aexp_vars e = {}"
          by (meson contra_subsetD)
        moreover from nin assign.hyps have "x \<notin> \<C>_vars y \<and> x \<noteq> y"
          by blast
        ultimately show "doesnt_read_or_modify ((x \<leftarrow> e) \<otimes> annos) y"
          using assign_doesnt_read
          by fastforce
      next
        assume "y \<in> mds\<^sub>2 GuarNoWrite"
        hence nin: "y \<in> mds GuarNoWrite"
          using assign.prems unfolding le_fun_def by blast
        hence "x \<noteq> y \<and> x \<notin> \<C>_vars y"
          using assign by blast
        with assign_doesnt_modify show "doesnt_modify ((x \<leftarrow> e) \<otimes> annos) y"
          by blast
      qed
    next
      assume "c' = Stop \<and> mds' = mds\<^sub>2 \<oplus> annos"
      with stop_doesnt_access show ?thesis by blast
    qed
  qed
  thus ?case
    apply clarsimp
    by (metis assign.prems assign_annos_eval assign_loc_reach stop_no_eval update_preserves_le)
next
  case (if_ mds annos c\<^sub>1 mds'' c\<^sub>2 e)
    let ?c = "(If e c\<^sub>1 c\<^sub>2) \<otimes> annos"
  from if_ have modes_le': "mds\<^sub>2 \<oplus> annos \<le> mds \<oplus> annos"
    by (metis (lifting) update_preserves_le)
  from if_ show ?case
    apply (simp add: locally_sound_mode_use_def)
    apply clarify
    apply (rule conjI)
     apply clarify
     prefer 2
     apply clarify
  proof -
    fix mem
    assume "\<langle>Stop, mds\<^sub>2', mem'\<rangle> \<in> loc_reach \<langle>If e c\<^sub>1 c\<^sub>2 \<otimes> annos, mds\<^sub>2, mem\<rangle>"
    with modes_le' and if_ show "mds\<^sub>2' \<le> mds''"
      by (metis if_eval_false if_eval_true if_loc_reach stop_no_eval)
  next
    fix mem c' mds' mem' x
    assume "\<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>If e c\<^sub>1 c\<^sub>2 \<otimes> annos, mds\<^sub>2, mem\<rangle>"
    hence "(c' = If e c\<^sub>1 c\<^sub>2 \<otimes> annos \<and> mds' = mds\<^sub>2) \<or>
           (\<exists> mem''. \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>1, mds\<^sub>2 \<oplus> annos, mem''\<rangle>) \<or>
           (\<exists> mem''. \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>2, mds\<^sub>2 \<oplus> annos, mem''\<rangle>)"
      using if_loc_reach by blast
    thus "(x \<in> mds' GuarNoReadOrWrite \<longrightarrow> doesnt_read_or_modify c' x) \<and>
          (x \<in> mds' GuarNoWrite \<longrightarrow> doesnt_modify c' x)"
    proof
      assume "c' = If e c\<^sub>1 c\<^sub>2 \<otimes> annos \<and> mds' = mds\<^sub>2"
      thus ?thesis
      proof (safe)
        assume "x \<in> mds\<^sub>2 GuarNoReadOrWrite"
        hence nin: "x \<in> mds GuarNoReadOrWrite"
          using if_ unfolding le_fun_def by auto
        with \<open>bexp_vars e \<inter> mds GuarNoReadOrWrite = {}\<close> have "x \<notin> bexp_vars e"
          by (metis IntD2 disjoint_iff_not_equal)
        moreover from if_(6) nin have "\<C>_vars x \<inter> bexp_vars e = {}"
          by blast
        ultimately show "doesnt_read_or_modify (If e c\<^sub>1 c\<^sub>2 \<otimes> annos) x"
          using if_doesnt_read by blast
      next
        assume "x \<in> mds\<^sub>2 GuarNoWrite"
        thus "doesnt_modify (If e c\<^sub>1 c\<^sub>2 \<otimes> annos) x"
          using if_doesnt_modify by blast
      qed
    next
      assume "(\<exists>mem''. \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>1, mds\<^sub>2 \<oplus> annos, mem''\<rangle>) \<or>
              (\<exists>mem''. \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>2, mds\<^sub>2 \<oplus> annos, mem''\<rangle>)"
      with if_ show ?thesis
        by (metis locally_sound_mode_use_def modes_le')
    qed
  qed
next
  case (while mdsa mds annos c e)
  hence "mds\<^sub>2 \<oplus> annos \<le> mds \<oplus> annos"
    by (metis (lifting) update_preserves_le)
  have while_loc_reach: "\<And> c' mds' mem' mem.
  \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>While e c \<otimes> annos, mds\<^sub>2, mem\<rangle> \<Longrightarrow>
  c' = While e c \<otimes> annos \<and> mds' = mds\<^sub>2 \<or>
  c' = While e c \<and> mds' \<le> mdsa \<or>
  c' = Stmt.If e (c ;; While e c) Stop \<and> mds' \<le> mdsa \<or>
  c' = Stop \<and> mds' \<le> mdsa \<or>
  (\<exists>c'' mem'' mds\<^sub>3.
      c' = c'' ;; While e c \<and>
      mds\<^sub>3 \<le> mdsa \<and> \<langle>c'', mds', mem'\<rangle> \<in> loc_reach \<langle>c, mds\<^sub>3, mem''\<rangle>)"
  proof -
    fix mem c' mds' mem'
    assume "\<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>While e c \<otimes> annos, mds\<^sub>2, mem\<rangle>"
    thus "?thesis c' mds' mem' mem"
      apply (induct rule: loc_reach.induct)
        apply simp_all
       apply (erule disjE)
        apply simp
        apply (metis \<open>mds\<^sub>2 \<oplus> annos \<le> mds \<oplus> annos\<close> while.hyps(1) while_eval_elim)
       apply (erule disjE)
        apply (metis while_eval_elim')
       apply (erule disjE)
        apply simp
        apply (metis if_eval_elim' loc_reach_refl')
       apply (erule disjE)
        apply (metis stop_no_eval)
       apply (erule exE)
       apply (rename_tac c' mds' mem' c'' mds'' mem'' c''a)
       apply (case_tac "c''a = Stop")
        apply (insert while.hyps(3))
        apply (metis seq_stop_elim while.hyps(3))
       apply (metis loc_reach.step seq_elim)
      by (metis (full_types) loc_reach.mem_diff)
  qed
  from while show ?case
  proof (safe)
    fix mem
    assume "\<langle>Stop, mds\<^sub>2', mem'\<rangle> \<in> loc_reach \<langle>While e c \<otimes> annos, mds\<^sub>2, mem\<rangle>"
    thus "mds\<^sub>2' \<le> mds \<oplus> annos"
      by (metis Stmt.distinct(35) Stmt.distinct(43) annotate.elims update_annos.simps(1) while.hyps(1) while.prems while_loc_reach)
  next
    fix mem
    from while have a: "bexp_vars e \<inter> (mds\<^sub>2 \<oplus> annos) GuarNoReadOrWrite = {}"
      by (metis (lifting, no_types) Int_empty_right Int_left_commute \<open>mds\<^sub>2 \<oplus> annos \<le> mds \<oplus> annos\<close> inf_fun_def le_iff_inf)
    from while have b: "\<forall>v.  \<C>_vars v \<inter> bexp_vars e \<noteq> {} \<longrightarrow> v \<notin> (mds\<^sub>2 \<oplus> annos) GuarNoReadOrWrite"
      by (meson \<open>mds\<^sub>2 \<oplus> annos \<le> mds \<oplus> annos\<close> le_fun_def subsetCE)    
    show "locally_sound_mode_use \<langle>While e c \<otimes> annos, mds\<^sub>2, mem\<rangle>"
      unfolding locally_sound_mode_use_def
      apply (rule allI)+
      apply (rule impI)
    proof -
      fix c' mds' mem'
      define lc where "lc = \<langle>While e c \<otimes> annos, mds\<^sub>2, mem\<rangle>"
      assume "\<langle>c', mds', mem'\<rangle> \<in> loc_reach lc"
      thus "\<forall>x. (x \<in> mds' GuarNoReadOrWrite \<longrightarrow> doesnt_read_or_modify c' x) \<and>
                 (x \<in> mds' GuarNoWrite \<longrightarrow> doesnt_modify c' x)"
        apply (simp add: lc_def)
        apply (drule while_loc_reach)
        apply (rule allI)
        apply (erule disjE5)
      proof (clarsimp)
        fix x
        show "(x \<in> mds\<^sub>2 GuarNoReadOrWrite \<longrightarrow> doesnt_read_or_modify (While e c \<otimes> annos) x) \<and>
              (x \<in> mds\<^sub>2 GuarNoWrite \<longrightarrow> doesnt_modify (While e c \<otimes> annos) x)"
          unfolding doesnt_read_or_modify_def doesnt_read_or_modify_vars_def and doesnt_modify_def
          using while_eval and while_eval_elim
          by blast
      next
        fix x
        assume a: "c' = Stmt.If e (c ;; While e c) Stop \<and> mds' \<le> mdsa"
        hence "mds' \<le> mdsa" by blast
        let ?c' = "If e (c ;; While e c) Stop"
        have "x \<in> mds' GuarNoReadOrWrite \<longrightarrow> doesnt_read_or_modify ?c' x"
          apply clarify
          apply (rule if_doesnt_read')
           apply (metis IntI \<open>mds' \<le> mdsa\<close> empty_iff le_fun_def rev_subsetD while.hyps(1) while.hyps(4))
          by (metis IntI \<open>mds' \<le> mdsa\<close> empty_iff le_fun_def rev_subsetD while.hyps(1) while.hyps(5))
        moreover
        have "x \<in> mds' GuarNoWrite \<longrightarrow> doesnt_modify ?c' x"
          by (metis annotate.simps(1) if_doesnt_modify)
        ultimately show "(x \<in> mds' GuarNoReadOrWrite \<longrightarrow> doesnt_read_or_modify c' x) \<and>
                         (x \<in> mds' GuarNoWrite \<longrightarrow> doesnt_modify c' x)"
          using a by simp 
      next
        fix x
        assume "c' = Stop \<and> mds' \<le> mdsa"
        thus "(x \<in> mds' GuarNoReadOrWrite \<longrightarrow> doesnt_read_or_modify c' x) \<and>
              (x \<in> mds' GuarNoWrite \<longrightarrow> doesnt_modify c' x)"
          by (simp, metis stop_doesnt_access)
      next
        fix x
        assume "\<exists>c'' mem'' mds\<^sub>3.
            c' = c'' ;; While e c \<and>
            mds\<^sub>3 \<le> mdsa \<and>
            \<langle>c'', mds', mem'\<rangle>
            \<in> loc_reach \<langle>c, mds\<^sub>3, mem''\<rangle>"
        from this obtain
         c'' mem'' mds\<^sub>3
        where "mds\<^sub>3 \<le> mdsa" and [simp]: "c' = c'' ;; While e c"
        and "\<langle>c'', mds', mem'\<rangle> \<in> loc_reach \<langle>c, mds\<^sub>3, mem''\<rangle>" by blast
        thus "(x \<in> mds' GuarNoReadOrWrite \<longrightarrow> doesnt_read_or_modify c' x) \<and>
              (x \<in> mds' GuarNoWrite \<longrightarrow> doesnt_modify c' x)"
          apply (clarsimp, safe)
           apply (rule seq_doesnt_read)
           apply (insert while(3))
           apply (metis \<open>mds\<^sub>3 \<le> mdsa\<close> locally_sound_mode_use_def while.hyps(1))
          apply (rule seq_doesnt_modify)
          by (metis \<open>mds\<^sub>3 \<le> mdsa\<close> locally_sound_mode_use_def while.hyps(1))
      next
        fix x
        assume "c' = While e c \<and> mds' \<le> mdsa"
        thus "(x \<in> mds' GuarNoReadOrWrite \<longrightarrow> doesnt_read_or_modify c' x) \<and>
              (x \<in> mds' GuarNoWrite \<longrightarrow> doesnt_modify c' x)"
          unfolding doesnt_read_or_modify_def doesnt_read_or_modify_vars_def and doesnt_modify_def
          using while_eval' and while_eval_elim'
          by blast
      qed
    qed
  qed
next
  case (seq mds c\<^sub>1 mds' c\<^sub>2 mds'')
  thus ?case
  proof (safe)
    fix mem
    assume "\<langle>Stop, mds\<^sub>2', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>1 ;; c\<^sub>2, mds\<^sub>2, mem\<rangle>"
    then obtain mds\<^sub>2'' mem'' where "\<langle>Stop, mds\<^sub>2'', mem''\<rangle> \<in> loc_reach \<langle>c\<^sub>1, mds\<^sub>2, mem\<rangle>" and
      "\<langle>Stop, mds\<^sub>2', mem'\<rangle> \<in> loc_reach \<langle>c\<^sub>2, mds\<^sub>2'', mem''\<rangle>"
      using seq_split by blast
    thus "mds\<^sub>2' \<le> mds''"
      using seq by blast
  next
    fix mem
    from seq show "locally_sound_mode_use \<langle>c\<^sub>1 ;; c\<^sub>2, mds\<^sub>2, mem\<rangle>"
      apply (simp add: locally_sound_mode_use_def)
      apply clarify
      apply (drule seq_loc_reach)
      apply (erule disjE)
       apply (metis seq_doesnt_modify seq_doesnt_read)
      by metis
  qed
next
  case (sub mds\<^sub>2'' c mds\<^sub>2' mds\<^sub>1 mds\<^sub>1' c\<^sub>1)
  thus ?case
    apply clarsimp
    by (metis (hide_lams, no_types) inf_absorb2 le_infI1)
qed

end

end
