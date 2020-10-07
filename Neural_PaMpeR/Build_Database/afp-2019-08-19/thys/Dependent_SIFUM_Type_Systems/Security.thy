(*
Title: Value-Dependent SIFUM-Type-Systems
Authors: Toby Murray, Robert Sison, Edward Pierzchalski, Christine Rizkallah
(Based on the SIFUM-Type-Systems AFP entry, whose authors
 are: Sylvia Grewe, Heiko Mantel, Daniel Schoepe)
*)

section \<open>Definition of the SIFUM-Security Property\<close>

theory Security
imports Preliminaries
begin

type_synonym ('var, 'val) adaptation = "'var \<rightharpoonup> ('val \<times> 'val)"

definition apply_adaptation ::
  "bool \<Rightarrow> ('Var, 'Val) Mem \<Rightarrow> ('Var, 'Val) adaptation \<Rightarrow> ('Var, 'Val) Mem"
  where "apply_adaptation first mem A =
         (\<lambda> x. case (A x) of
               Some (v\<^sub>1, v\<^sub>2) \<Rightarrow> if first then v\<^sub>1 else v\<^sub>2
             | None \<Rightarrow> mem x)"

abbreviation apply_adaptation\<^sub>1 ::
  "('Var, 'Val) Mem \<Rightarrow> ('Var, 'Val) adaptation \<Rightarrow> ('Var, 'Val) Mem"
  ("_ [\<parallel>\<^sub>1 _]" [900, 0] 1000)
  where "mem [\<parallel>\<^sub>1 A] \<equiv> apply_adaptation True mem A"

abbreviation apply_adaptation\<^sub>2 ::
  "('Var, 'Val) Mem \<Rightarrow> ('Var, 'Val) adaptation \<Rightarrow> ('Var, 'Val) Mem"
  ("_ [\<parallel>\<^sub>2 _]" [900, 0] 1000)
  where "mem [\<parallel>\<^sub>2 A] \<equiv> apply_adaptation False mem A"

definition
  var_asm_not_written :: "'Var Mds \<Rightarrow> 'Var \<Rightarrow> bool"
where
  "var_asm_not_written mds x \<equiv> x \<in> mds AsmNoWrite \<or> x \<in> mds AsmNoReadOrWrite"

context sifum_security_init begin

subsection \<open>Evaluation of Concurrent Programs\<close>

abbreviation eval_abv :: "('Com, 'Var, 'Val) LocalConf \<Rightarrow> (_, _, _) LocalConf \<Rightarrow> bool"
  (infixl "\<leadsto>" 70)
where
  "x \<leadsto> y \<equiv> (x, y) \<in> eval"

abbreviation conf_abv :: "'Com \<Rightarrow> 'Var Mds \<Rightarrow> ('Var, 'Val) Mem \<Rightarrow> (_,_,_) LocalConf"
  ("\<langle>_, _, _\<rangle>" [0, 0, 0] 1000)
where
  "\<langle> c, mds, mem \<rangle> \<equiv> ((c, mds), mem)"

(* Labelled evaluation global configurations: *)
inductive_set meval :: "((_,_,_) GlobalConf \<times> nat \<times> (_,_,_) GlobalConf) set"
  and meval_abv :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" ("_ \<leadsto>\<^bsub>_\<^esub> _" 70)
where
  "conf \<leadsto>\<^bsub>k\<^esub> conf' \<equiv> (conf, k, conf') \<in> meval" |
  meval_intro [iff]: "\<lbrakk> (cms ! n, mem) \<leadsto> (cm', mem'); n < length cms \<rbrakk> \<Longrightarrow>
  ((cms, mem), n, (cms [n := cm'], mem')) \<in> meval"

inductive_cases meval_elim [elim!]: "((cms, mem), k, (cms', mem')) \<in> meval"

inductive neval :: "('Com, 'Var, 'Val) LocalConf \<Rightarrow> nat \<Rightarrow> (_, _, _) LocalConf \<Rightarrow> bool"
  (infixl "\<leadsto>\<^bsup>_\<^esup>" 70)
where
  neval_0: "x = y \<Longrightarrow> x \<leadsto>\<^bsup>0\<^esup> y" |
  neval_S_n: "x \<leadsto> y \<Longrightarrow> y \<leadsto>\<^bsup>n\<^esup> z \<Longrightarrow> x \<leadsto>\<^bsup>Suc n\<^esup> z"

inductive_cases neval_ZeroE: "neval x 0 y"
inductive_cases neval_SucE: "neval x (Suc n) y"

lemma neval_det:
  "x \<leadsto>\<^bsup>n\<^esup> y \<Longrightarrow> x \<leadsto>\<^bsup>n\<^esup> y' \<Longrightarrow> y = y'"
  apply(induct arbitrary: y' rule: neval.induct)
   apply(blast elim: neval_ZeroE)
  apply(blast elim: neval_SucE dest: deterministic)
  done

lemma neval_Suc_simp [simp]:
  "neval x (Suc 0) y = x \<leadsto> y"
proof
  assume a: "neval x (Suc 0) y"
  have "\<And>n. neval x n y \<Longrightarrow> n = Suc 0 \<Longrightarrow> x \<leadsto> y"
  proof -
    fix n
    assume "neval x n y"
       and "n = Suc 0"
    thus "x \<leadsto> y"
    by(induct rule: neval.induct, auto elim: neval_ZeroE)
  qed
  with a show "x \<leadsto> y" by simp
  next
  assume "x \<leadsto> y"
  thus "neval x (Suc 0) y"
    by(force intro: neval.intros)
qed

fun 
  lc_set_var :: "(_, _, _) LocalConf \<Rightarrow> 'Var \<Rightarrow> 'Val \<Rightarrow> (_, _, _) LocalConf"
where
  "lc_set_var (c, mem) x v = (c, mem (x := v))"

fun 
  meval_sched :: "nat list \<Rightarrow> ('Com, 'Var, 'Val) GlobalConf \<Rightarrow> (_, _, _) GlobalConf \<Rightarrow> bool"
where
  "meval_sched [] c c' = (c = c')" |
  "meval_sched (n#ns) c c' = (\<exists> c''.  c \<leadsto>\<^bsub>n\<^esub> c'' \<and> meval_sched ns c'' c')"

abbreviation
  meval_sched_abv :: "(_,_,_) GlobalConf \<Rightarrow> nat list \<Rightarrow> (_,_,_) GlobalConf \<Rightarrow> bool" ("_ \<rightarrow>\<^bsub>_\<^esub> _" 70)
where
  "c \<rightarrow>\<^bsub>ns\<^esub> c' \<equiv> meval_sched ns c c'"

lemma meval_sched_det:
  "meval_sched ns c c' \<Longrightarrow> meval_sched ns c c'' \<Longrightarrow> c' = c''"
  apply(induct ns arbitrary: c)
   apply(auto dest: deterministic)
  done

subsection \<open>Low-equivalence and Strong Low Bisimulations\<close>

(* Low-equality between memory states: *)
definition 
  low_eq :: "('Var, 'Val) Mem \<Rightarrow> (_, _) Mem \<Rightarrow> bool" (infixl "=\<^sup>l" 80)
where
  "mem\<^sub>1 =\<^sup>l mem\<^sub>2 \<equiv> (\<forall> x. dma mem\<^sub>1 x = Low \<longrightarrow> mem\<^sub>1 x = mem\<^sub>2 x)"


(* Low-equality modulo a given mode state: *)
definition 
  low_mds_eq :: "'Var Mds \<Rightarrow> ('Var, 'Val) Mem \<Rightarrow> (_, _) Mem \<Rightarrow> bool"
  ("_ =\<index>\<^sup>l _" [100, 100] 80)
where
  "(mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2) \<equiv> (\<forall> x. dma mem\<^sub>1 x = Low \<and> (x \<in> \<C> \<or> x \<notin> mds AsmNoReadOrWrite) \<longrightarrow> mem\<^sub>1 x = mem\<^sub>2 x)"

lemma low_eq_low_mds_eq:
  "(mem\<^sub>1 =\<^sup>l mem\<^sub>2) = (mem\<^sub>1 =\<^bsub>(\<lambda>m. {})\<^esub>\<^sup>l mem\<^sub>2)"
  by(simp add: low_eq_def low_mds_eq_def)

lemma low_mds_eq_dma:
  "(mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2) \<Longrightarrow> dma mem\<^sub>1 = dma mem\<^sub>2"
  apply(rule dma_\<C>)
  apply(simp add: low_mds_eq_def \<C>_Low)
  done

lemma low_mds_eq_sym:
  "(mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2) \<Longrightarrow> (mem\<^sub>2 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>1)"
  apply(frule low_mds_eq_dma)
  apply(simp add: low_mds_eq_def)
  done

lemma low_eq_sym:
  "(mem\<^sub>1 =\<^sup>l mem\<^sub>2) \<Longrightarrow> (mem\<^sub>2 =\<^sup>l mem\<^sub>1)"
  apply(simp add: low_eq_low_mds_eq low_mds_eq_sym)
  done

lemma [simp]: "mem =\<^sup>l mem' \<Longrightarrow> mem =\<^bsub>mds\<^esub>\<^sup>l mem'"
  by (simp add: low_mds_eq_def low_eq_def)

lemma [simp]: "(\<forall> mds. mem =\<^bsub>mds\<^esub>\<^sup>l mem') \<Longrightarrow> mem =\<^sup>l mem'"
  by (auto simp: low_mds_eq_def low_eq_def)

lemma High_not_in_\<C> [simp]:
  "dma mem\<^sub>1 x = High \<Longrightarrow> x \<notin> \<C>"
  apply(case_tac "x \<in> \<C>")
  by(simp add: \<C>_Low)

(* Closedness under globally consistent changes: *)
definition 
  closed_glob_consistent :: "(('Com, 'Var, 'Val) LocalConf) rel \<Rightarrow> bool"
where
  "closed_glob_consistent \<R> =
  (\<forall> c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2. (\<langle> c\<^sub>1, mds, mem\<^sub>1 \<rangle>, \<langle> c\<^sub>2, mds, mem\<^sub>2 \<rangle>) \<in> \<R> \<longrightarrow>
   (\<forall> A. ((\<forall>x. case A x of Some (v,v') \<Rightarrow> (mem\<^sub>1 x \<noteq> v \<or> mem\<^sub>2 x \<noteq> v') \<longrightarrow> \<not> var_asm_not_written mds x | _ \<Rightarrow> True) \<and>
          (\<forall>x. dma (mem\<^sub>1 [\<parallel>\<^sub>1 A]) x \<noteq> dma mem\<^sub>1 x \<longrightarrow> \<not> var_asm_not_written mds x) \<and>
          (\<forall>x. dma (mem\<^sub>1 [\<parallel>\<^sub>1 A]) x = Low \<and> (x \<notin> mds AsmNoReadOrWrite \<or> x \<in> \<C>) \<longrightarrow> (mem\<^sub>1 [\<parallel>\<^sub>1 A]) x = (mem\<^sub>2 [\<parallel>\<^sub>2 A]) x)) \<longrightarrow>
         (\<langle> c\<^sub>1, mds, mem\<^sub>1[\<parallel>\<^sub>1 A] \<rangle>, \<langle> c\<^sub>2, mds, mem\<^sub>2[\<parallel>\<^sub>2 A] \<rangle>) \<in> \<R>))"

(* Strong low bisimulations modulo modes: *)
definition 
  strong_low_bisim_mm :: "(('Com, 'Var, 'Val) LocalConf) rel \<Rightarrow> bool"
where
  "strong_low_bisim_mm \<R> \<equiv>
  sym \<R> \<and>
  closed_glob_consistent \<R> \<and>
  (\<forall> c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2. (\<langle> c\<^sub>1, mds, mem\<^sub>1 \<rangle>, \<langle> c\<^sub>2, mds, mem\<^sub>2 \<rangle>) \<in> \<R> \<longrightarrow>
   (mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2) \<and>
   (\<forall> c\<^sub>1' mds' mem\<^sub>1'. \<langle> c\<^sub>1, mds, mem\<^sub>1 \<rangle> \<leadsto> \<langle> c\<^sub>1', mds', mem\<^sub>1' \<rangle> \<longrightarrow>
    (\<exists> c\<^sub>2' mem\<^sub>2'. \<langle> c\<^sub>2, mds, mem\<^sub>2 \<rangle> \<leadsto> \<langle> c\<^sub>2', mds', mem\<^sub>2' \<rangle> \<and>
                  (\<langle> c\<^sub>1', mds', mem\<^sub>1' \<rangle>, \<langle> c\<^sub>2', mds', mem\<^sub>2' \<rangle>) \<in> \<R>)))"

inductive_set mm_equiv :: "(('Com, 'Var, 'Val) LocalConf) rel"
  and mm_equiv_abv :: "('Com, 'Var, 'Val) LocalConf \<Rightarrow> 
  ('Com, 'Var, 'Val) LocalConf \<Rightarrow> bool" (infix "\<approx>" 60)
where
  "mm_equiv_abv x y \<equiv> (x, y) \<in> mm_equiv" |
  mm_equiv_intro [iff]: "\<lbrakk> strong_low_bisim_mm \<R> ; (lc\<^sub>1, lc\<^sub>2) \<in> \<R> \<rbrakk> \<Longrightarrow> (lc\<^sub>1, lc\<^sub>2) \<in> mm_equiv"

inductive_cases mm_equiv_elim [elim]: "\<langle> c\<^sub>1, mds, mem\<^sub>1 \<rangle> \<approx> \<langle> c\<^sub>2, mds, mem\<^sub>2 \<rangle>"

definition low_indistinguishable :: "'Var Mds \<Rightarrow> 'Com \<Rightarrow> 'Com \<Rightarrow> bool"
  ("_ \<sim>\<index> _" [100, 100] 80)
where 
  "c\<^sub>1 \<sim>\<^bsub>mds\<^esub> c\<^sub>2 = (\<forall> mem\<^sub>1 mem\<^sub>2. mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2 \<longrightarrow> \<langle> c\<^sub>1, mds, mem\<^sub>1 \<rangle> \<approx> \<langle> c\<^sub>2, mds, mem\<^sub>2 \<rangle>)"

subsection \<open>SIFUM-Security\<close>

(* SIFUM-security for commands: *)
definition 
  com_sifum_secure :: "'Com \<times> 'Var Mds \<Rightarrow> bool"
where 
  "com_sifum_secure cmd \<equiv> case cmd of (c,mds\<^sub>s) \<Rightarrow> c \<sim>\<^bsub>mds\<^sub>s\<^esub> c"

(* Continuous SIFUM-security 
   (where we don't care about whether the prog has any assumptions at termination *)
definition 
  prog_sifum_secure_cont :: "('Com \<times> 'Var Mds) list \<Rightarrow> bool"
where "prog_sifum_secure_cont cmds =
   (\<forall> mem\<^sub>1 mem\<^sub>2. INIT mem\<^sub>1 \<and> INIT mem\<^sub>2 \<and> mem\<^sub>1 =\<^sup>l mem\<^sub>2 \<longrightarrow>
    (\<forall> sched cms\<^sub>1' mem\<^sub>1'.
     (cmds, mem\<^sub>1) \<rightarrow>\<^bsub>sched\<^esub> (cms\<^sub>1', mem\<^sub>1') \<longrightarrow>
      (\<exists> cms\<^sub>2' mem\<^sub>2'. (cmds, mem\<^sub>2) \<rightarrow>\<^bsub>sched\<^esub> (cms\<^sub>2', mem\<^sub>2') \<and>
                      map snd cms\<^sub>1' = map snd cms\<^sub>2' \<and>
                      length cms\<^sub>2' = length cms\<^sub>1' \<and>
                      (\<forall> x. dma mem\<^sub>1' x = Low \<and> (x \<in> \<C> \<or> (\<forall> i < length cms\<^sub>1'.
                        x \<notin> snd (cms\<^sub>1' ! i) AsmNoReadOrWrite)) \<longrightarrow> mem\<^sub>1' x = mem\<^sub>2' x))))"

(* Note that it is equivalent to the following because the 
   programming language is deterministic *)
lemma prog_sifum_secure_cont_def2:
  "prog_sifum_secure_cont cmds \<equiv>
   (\<forall> mem\<^sub>1 mem\<^sub>2. INIT mem\<^sub>1 \<and> INIT mem\<^sub>2 \<and> mem\<^sub>1 =\<^sup>l mem\<^sub>2 \<longrightarrow>
    (\<forall> sched cms\<^sub>1' mem\<^sub>1'.
     (cmds, mem\<^sub>1) \<rightarrow>\<^bsub>sched\<^esub> (cms\<^sub>1', mem\<^sub>1') \<longrightarrow>
      (\<exists> cms\<^sub>2' mem\<^sub>2'. (cmds, mem\<^sub>2) \<rightarrow>\<^bsub>sched\<^esub> (cms\<^sub>2', mem\<^sub>2')) \<and>
      (\<forall> cms\<^sub>2' mem\<^sub>2'. (cmds, mem\<^sub>2) \<rightarrow>\<^bsub>sched\<^esub> (cms\<^sub>2', mem\<^sub>2') \<longrightarrow>
                      map snd cms\<^sub>1' = map snd cms\<^sub>2' \<and>
                      length cms\<^sub>2' = length cms\<^sub>1' \<and>
                      (\<forall> x. dma mem\<^sub>1' x = Low \<and> (x \<in> \<C> \<or> (\<forall> i < length cms\<^sub>1'.
                        x \<notin> snd (cms\<^sub>1' ! i) AsmNoReadOrWrite)) \<longrightarrow> mem\<^sub>1' x = mem\<^sub>2' x))))"
  apply(rule eq_reflection)
  unfolding prog_sifum_secure_cont_def
  apply(rule iffI)
   apply(blast dest: meval_sched_det)
  by fastforce

subsection \<open>Sound Mode Use\<close>


(* Suggestive notation for substitution / function application *)
definition 
  subst :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
where
  "subst f mem = (\<lambda> x. case f x of
                         None \<Rightarrow> mem x |
                         Some v \<Rightarrow> v)"

abbreviation 
  subst_abv :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" ("_ [\<mapsto>_]" [900, 0] 1000)
where
  "f [\<mapsto> \<sigma>] \<equiv> subst \<sigma> f"

lemma subst_not_in_dom : "\<lbrakk> x \<notin> dom \<sigma> \<rbrakk> \<Longrightarrow> mem [\<mapsto> \<sigma>] x = mem x"
  by (simp add: domIff subst_def)

(* Toby: we restrict not reading to also imply not modifying a variable.
         This is done mostly to simplify part of the reasoning in the
         Compositionality theory, but also because reconciling doesnt_read_or_modify
         forcing also not reading the variable's classification in the case
         in the case where it would allow non-reading modifications proved
         to get too unwieldy *)
definition 
  doesnt_read_or_modify_vars :: "'Com \<Rightarrow> 'Var set \<Rightarrow> bool"
where
  "doesnt_read_or_modify_vars c X = (\<forall> mds mem c' mds' mem'.
  \<langle> c, mds, mem \<rangle> \<leadsto> \<langle> c', mds', mem' \<rangle> \<longrightarrow>
  ((\<forall>x\<in>X. (\<forall> v. \<langle> c, mds, mem (x := v) \<rangle> \<leadsto> \<langle> c', mds', mem' (x := v) \<rangle>))))"

definition
  vars_\<C> :: "'Var set \<Rightarrow> 'Var set"
where
  "vars_\<C> X \<equiv> \<Union>x\<in>X. \<C>_vars x"

lemma vars_\<C>_subset_\<C>:
  "vars_\<C> X \<subseteq> \<C>"
  by(auto simp: \<C>_def vars_\<C>_def)

(* Toby: doesnt_read_or_modify now implies that the classification is not read too *)
definition 
  doesnt_read_or_modify :: "'Com \<Rightarrow> 'Var \<Rightarrow> bool"
where
  "doesnt_read_or_modify c x \<equiv> doesnt_read_or_modify_vars c ({x} \<union> \<C>_vars x)"

definition 
  doesnt_modify :: "'Com \<Rightarrow> 'Var \<Rightarrow> bool"
where
  "doesnt_modify c x = (\<forall> mds mem c' mds' mem'. (\<langle> c, mds, mem \<rangle> \<leadsto> \<langle> c', mds', mem' \<rangle>) \<longrightarrow>
                        mem x = mem' x \<and>  dma mem x = dma mem' x)"

lemma noread_nowrite:
  assumes step: "\<langle>c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
  assumes noread: "(\<And>v. \<langle>c, mds, mem(x := v)\<rangle> \<leadsto> \<langle>c', mds', mem'(x := v)\<rangle>)"
  shows "mem x = mem' x"
proof -
  from noread have "\<langle>c, mds, mem(x := (mem x))\<rangle> \<leadsto> \<langle>c', mds', mem'(x := (mem x))\<rangle>"
    by blast
  hence "\<langle>c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'(x := (mem x))\<rangle>" by simp
  from step this have "mem' = mem'(x := (mem x))" by (blast dest: deterministic)
  hence "mem' x = (mem'(x := (mem x))) x" by(rule arg_cong)
  thus ?thesis by simp
qed

(* Toby: not sure whether this implication should just be made explicit in the
         definition of doesnt_read_or_modify or not *)
lemma doesnt_read_or_modify_doesnt_modify:
  "doesnt_read_or_modify c x \<Longrightarrow> doesnt_modify c x"
  by(fastforce simp: doesnt_modify_def doesnt_read_or_modify_def doesnt_read_or_modify_vars_def 
               intro: noread_nowrite dma_\<C>_vars)

(* Local reachability of local configurations: *)
inductive_set 
  loc_reach :: "('Com, 'Var, 'Val) LocalConf \<Rightarrow> ('Com, 'Var, 'Val) LocalConf set"
  for lc :: "(_, _, _) LocalConf"
where
  refl : "\<langle>fst (fst lc), snd (fst lc), snd lc\<rangle> \<in> loc_reach lc" |
  step : "\<lbrakk> \<langle>c', mds', mem'\<rangle> \<in> loc_reach lc;
            \<langle>c', mds', mem'\<rangle> \<leadsto> \<langle>c'', mds'', mem''\<rangle> \<rbrakk> \<Longrightarrow>
          \<langle>c'', mds'', mem''\<rangle> \<in> loc_reach lc" |
  mem_diff : "\<lbrakk> \<langle> c', mds', mem' \<rangle> \<in> loc_reach lc;
                (\<forall> x. var_asm_not_written mds' x \<longrightarrow> mem' x = mem'' x \<and> dma mem' x = dma mem'' x) \<rbrakk> \<Longrightarrow>
              \<langle> c', mds', mem'' \<rangle> \<in> loc_reach lc"

lemma neval_loc_reach:
  "neval lc' n lc'' \<Longrightarrow> lc' \<in> loc_reach lc \<Longrightarrow> lc'' \<in> loc_reach lc"
proof(induct rule: neval.induct)
  case (neval_0 x y)
    thus ?case by simp
next
  case (neval_S_n x y n z)
  from \<open>x \<in> loc_reach lc\<close> and \<open>x \<leadsto> y\<close> have "y \<in> loc_reach lc" 
    (* TODO: can we get rid of this case_tac nonsense? *)
    apply(case_tac x, rename_tac a b, case_tac a, clarsimp)
    apply(case_tac y, rename_tac c d, case_tac c, clarsimp)
    by(blast intro: loc_reach.step)
  thus ?case
    using neval_S_n(3) by blast
qed
    

definition 
  locally_sound_mode_use :: "(_, _, _) LocalConf \<Rightarrow> bool"
where
  "locally_sound_mode_use lc =
  (\<forall> c' mds' mem'. \<langle> c', mds', mem' \<rangle> \<in> loc_reach lc \<longrightarrow>
    (\<forall> x. (x \<in> mds' GuarNoReadOrWrite \<longrightarrow> doesnt_read_or_modify c' x) \<and>
          (x \<in> mds' GuarNoWrite \<longrightarrow> doesnt_modify c' x)))"

(* RobS: The same property, but for an individual evaluation. Note it doesn't rely on mem! *)
definition 
  respects_own_guarantees :: "('Com \<times> 'Var Mds) \<Rightarrow> bool"
where
  "respects_own_guarantees cm \<equiv>
  (\<forall> x. (x \<in> (snd cm) GuarNoReadOrWrite \<longrightarrow> doesnt_read_or_modify (fst cm) x) \<and>
        (x \<in> (snd cm) GuarNoWrite \<longrightarrow> doesnt_modify (fst cm) x))"

lemma locally_sound_mode_use_def2:
  "locally_sound_mode_use lc \<equiv> \<forall>lc' \<in> loc_reach lc. respects_own_guarantees (fst lc')"
  apply(rule eq_reflection)
  apply(simp add: locally_sound_mode_use_def respects_own_guarantees_def)
  apply force
  done

lemma locally_sound_respects_guarantees:
  "locally_sound_mode_use (cm, mem) \<Longrightarrow> respects_own_guarantees cm"
  unfolding locally_sound_mode_use_def respects_own_guarantees_def
  by (metis fst_conv loc_reach.refl)

definition 
  compatible_modes :: "('Var Mds) list \<Rightarrow> bool"
where
  "compatible_modes mdss = (\<forall> (i :: nat) x. i < length mdss \<longrightarrow>
    (x \<in> (mdss ! i) AsmNoReadOrWrite \<longrightarrow>
     (\<forall> j < length mdss. j \<noteq> i \<longrightarrow> x \<in> (mdss ! j) GuarNoReadOrWrite)) \<and>
    (x \<in> (mdss ! i) AsmNoWrite \<longrightarrow>
     (\<forall> j < length mdss. j \<noteq> i \<longrightarrow> x \<in> (mdss ! j) GuarNoWrite)))"

definition 
  reachable_mode_states :: "('Com, 'Var, 'Val) GlobalConf \<Rightarrow> (('Var Mds) list) set"
where 
  "reachable_mode_states gc \<equiv>
     {mdss. (\<exists> cms' mem' sched. gc \<rightarrow>\<^bsub>sched\<^esub> (cms', mem') \<and> map snd cms' = mdss)}"

definition 
  globally_sound_mode_use :: "('Com, 'Var, 'Val) GlobalConf \<Rightarrow> bool"
where 
  "globally_sound_mode_use gc \<equiv>
     (\<forall> mdss. mdss \<in> reachable_mode_states gc \<longrightarrow> compatible_modes mdss)"

primrec 
  sound_mode_use :: "(_, _, _) GlobalConf \<Rightarrow> bool"
where
  "sound_mode_use (cms, mem) =
     (list_all (\<lambda> cm. locally_sound_mode_use (cm, mem)) cms \<and>
      globally_sound_mode_use (cms, mem))"

(* We now show that mm_equiv itself forms a strong low bisimulation modulo modes: *)
lemma mm_equiv_sym:
  assumes equivalent: "\<langle>c\<^sub>1, mds\<^sub>1, mem\<^sub>1\<rangle> \<approx> \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>"
  shows "\<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle> \<approx> \<langle>c\<^sub>1, mds\<^sub>1, mem\<^sub>1\<rangle>"
proof -
  from equivalent obtain \<R>
    where \<R>_bisim: "strong_low_bisim_mm \<R> \<and> (\<langle>c\<^sub>1, mds\<^sub>1, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>) \<in> \<R>"
    by (metis mm_equiv.simps)
  hence "sym \<R>"
    by (auto simp: strong_low_bisim_mm_def)
  hence "(\<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>, \<langle>c\<^sub>1, mds\<^sub>1, mem\<^sub>1\<rangle>) \<in> \<R>"
    by (metis \<R>_bisim symE)
  thus ?thesis
    by (metis \<R>_bisim mm_equiv.intros)
qed

lemma low_indistinguishable_sym: "lc \<sim>\<^bsub>mds\<^esub> lc' \<Longrightarrow> lc' \<sim>\<^bsub>mds\<^esub> lc"
  apply(clarsimp simp: low_indistinguishable_def)
  apply(rule mm_equiv_sym)
  apply(blast dest: low_mds_eq_sym)
  done

lemma mm_equiv_glob_consistent: "closed_glob_consistent mm_equiv"
  unfolding closed_glob_consistent_def
  apply clarify
  apply (erule mm_equiv_elim)
  by (auto simp: strong_low_bisim_mm_def closed_glob_consistent_def)

lemma mm_equiv_strong_low_bisim: "strong_low_bisim_mm mm_equiv"
  unfolding strong_low_bisim_mm_def
proof (auto)
  show "closed_glob_consistent mm_equiv" by (rule mm_equiv_glob_consistent)
next
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 x
  assume "\<langle> c\<^sub>1, mds, mem\<^sub>1 \<rangle> \<approx> \<langle> c\<^sub>2, mds, mem\<^sub>2 \<rangle>"
  then obtain \<R> where
    "strong_low_bisim_mm \<R> \<and> (\<langle> c\<^sub>1, mds, mem\<^sub>1 \<rangle>, \<langle> c\<^sub>2, mds, mem\<^sub>2 \<rangle>) \<in> \<R>"
    by blast
  thus "mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2" by (auto simp: strong_low_bisim_mm_def)
next
  fix c\<^sub>1 :: 'Com
  fix mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 c\<^sub>1' mds' mem\<^sub>1'
  let ?lc\<^sub>1 = "\<langle> c\<^sub>1, mds, mem\<^sub>1 \<rangle>" and
      ?lc\<^sub>1' = "\<langle> c\<^sub>1', mds', mem\<^sub>1' \<rangle>" and
      ?lc\<^sub>2 = "\<langle> c\<^sub>2, mds, mem\<^sub>2 \<rangle>"
  assume "?lc\<^sub>1 \<approx> ?lc\<^sub>2"
  then obtain \<R> where "strong_low_bisim_mm \<R> \<and> (?lc\<^sub>1, ?lc\<^sub>2) \<in> \<R>"
    by (rule mm_equiv_elim, blast)
  moreover assume "?lc\<^sub>1 \<leadsto> ?lc\<^sub>1'"
  ultimately show "\<exists> c\<^sub>2' mem\<^sub>2'. ?lc\<^sub>2 \<leadsto> \<langle> c\<^sub>2', mds', mem\<^sub>2' \<rangle> \<and> ?lc\<^sub>1' \<approx> \<langle> c\<^sub>2', mds', mem\<^sub>2' \<rangle>"
    by (simp add: strong_low_bisim_mm_def mm_equiv_sym, blast)
next
  show "sym mm_equiv"
    by (auto simp: sym_def mm_equiv_sym)
qed

end

end
