(*
Title: SIFUM-Type-Systems
Authors: Sylvia Grewe, Heiko Mantel, Daniel Schoepe
*)
section \<open>Definition of the SIFUM-Security Property\<close>

theory Security
imports Main Preliminaries
begin

context sifum_security begin

subsection \<open>Evaluation of Concurrent Programs\<close>

abbreviation eval_abv :: "('Com, 'Var, 'Val) LocalConf \<Rightarrow> (_, _, _) LocalConf \<Rightarrow> bool"
  (infixl "\<leadsto>" 70)
  where
  "x \<leadsto> y \<equiv> (x, y) \<in> eval"

abbreviation conf_abv :: "'Com \<Rightarrow> 'Var Mds \<Rightarrow> ('Var, 'Val) Mem \<Rightarrow> (_,_,_) LocalConf"
  ("\<langle>_, _, _\<rangle>" [0, 0, 0] 1000)
  where
  "\<langle> c, mds, mem \<rangle> \<equiv> ((c, mds), mem)"

(* Evaluation of global configurations: *)
inductive_set meval :: "(_,_,_) GlobalConf rel"
  and meval_abv :: "_ \<Rightarrow> _ \<Rightarrow> bool" (infixl "\<rightarrow>" 70)
  where
  "conf \<rightarrow> conf' \<equiv> (conf, conf') \<in> meval" |
  meval_intro [iff]: "\<lbrakk> (cms ! n, mem) \<leadsto> (cm', mem'); n < length cms \<rbrakk> \<Longrightarrow>
  ((cms, mem), (cms [n := cm'], mem')) \<in> meval"

inductive_cases meval_elim [elim!]: "((cms, mem), (cms', mem')) \<in> meval"

(* Syntactic sugar for the reflexive-transitive closure of meval: *)
abbreviation meval_clos :: "_ \<Rightarrow> _ \<Rightarrow> bool" (infixl "\<rightarrow>\<^sup>*" 70)
  where
  "conf \<rightarrow>\<^sup>* conf' \<equiv> (conf, conf') \<in> meval\<^sup>*"

fun lc_set_var :: "(_, _, _) LocalConf \<Rightarrow> 'Var \<Rightarrow> 'Val \<Rightarrow> (_, _, _) LocalConf"
  where
  "lc_set_var (c, mem) x v = (c, mem (x := v))"

fun meval_k :: "nat \<Rightarrow> ('Com, 'Var, 'Val) GlobalConf \<Rightarrow> (_, _, _) GlobalConf \<Rightarrow> bool"
  where
  "meval_k 0 c c' = (c = c')" |
  "meval_k (Suc n) c c' = (\<exists> c''. meval_k n c c'' \<and> c'' \<rightarrow> c')"

(* k steps of evaluation (for global configurations: *)
abbreviation meval_k_abv :: "nat \<Rightarrow> (_, _, _) GlobalConf \<Rightarrow> (_, _, _) GlobalConf \<Rightarrow> bool"
  ("_ \<rightarrow>\<index> _" [100, 100] 80)
  where
  "gc \<rightarrow>\<^bsub>k \<^esub>gc' \<equiv> meval_k k gc gc'"

subsection \<open>Low-equivalence and Strong Low Bisimulations\<close>

(* Low-equality between memory states: *)
definition low_eq :: "('Var, 'Val) Mem \<Rightarrow> (_, _) Mem \<Rightarrow> bool" (infixl "=\<^sup>l" 80)
  where
  "mem\<^sub>1 =\<^sup>l mem\<^sub>2 \<equiv> (\<forall> x. dma x = Low \<longrightarrow> mem\<^sub>1 x = mem\<^sub>2 x)"

(* Low-equality modulo a given mode state: *)
definition low_mds_eq :: "'Var Mds \<Rightarrow> ('Var, 'Val) Mem \<Rightarrow> (_, _) Mem \<Rightarrow> bool"
  ("_ =\<index>\<^sup>l _" [100, 100] 80)
  where
  "(mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2) \<equiv> (\<forall> x. dma x = Low \<and> x \<notin> mds AsmNoRead \<longrightarrow> mem\<^sub>1 x = mem\<^sub>2 x)"

(* Initial mode state: *)
definition "mds\<^sub>s" :: "'Var Mds" where
  "mds\<^sub>s x = {}"

lemma [simp]: "mem =\<^sup>l mem' \<Longrightarrow> mem =\<^bsub>mds\<^esub>\<^sup>l mem'"
  by (simp add: low_mds_eq_def low_eq_def)

lemma [simp]: "(\<forall> mds. mem =\<^bsub>mds\<^esub>\<^sup>l mem') \<Longrightarrow> mem =\<^sup>l mem'"
  by (auto simp: low_mds_eq_def low_eq_def)

(* Closedness under globally consistent changes: *)
definition closed_glob_consistent :: "(('Com, 'Var, 'Val) LocalConf) rel \<Rightarrow> bool"
  where
  "closed_glob_consistent \<R> =
  (\<forall> c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2. (\<langle> c\<^sub>1, mds, mem\<^sub>1 \<rangle>, \<langle> c\<^sub>2, mds, mem\<^sub>2 \<rangle>) \<in> \<R> \<longrightarrow>
   (\<forall> x. ((dma x = High \<and> x \<notin> mds AsmNoWrite) \<longrightarrow>
           (\<forall> v\<^sub>1 v\<^sub>2. (\<langle> c\<^sub>1, mds, mem\<^sub>1 (x := v\<^sub>1) \<rangle>, \<langle> c\<^sub>2, mds, mem\<^sub>2 (x := v\<^sub>2) \<rangle>) \<in> \<R>)) \<and>
         ((dma x = Low \<and> x \<notin> mds AsmNoWrite) \<longrightarrow>
           (\<forall> v. (\<langle> c\<^sub>1, mds, mem\<^sub>1 (x := v) \<rangle>, \<langle> c\<^sub>2, mds, mem\<^sub>2 (x := v) \<rangle>) \<in> \<R>))))"

(* Strong low bisimulations modulo modes: *)
definition strong_low_bisim_mm :: "(('Com, 'Var, 'Val) LocalConf) rel \<Rightarrow> bool"
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
  where "c\<^sub>1 \<sim>\<^bsub>mds\<^esub> c\<^sub>2 = (\<forall> mem\<^sub>1 mem\<^sub>2. mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2 \<longrightarrow>
    \<langle> c\<^sub>1, mds, mem\<^sub>1 \<rangle> \<approx> \<langle> c\<^sub>2, mds, mem\<^sub>2 \<rangle>)"

subsection \<open>SIFUM-Security\<close>

(* SIFUM-security for commands: *)
definition com_sifum_secure :: "'Com \<Rightarrow> bool"
  where "com_sifum_secure c = c \<sim>\<^bsub>mds\<^sub>s\<^esub> c"

definition add_initial_modes :: "'Com list \<Rightarrow> ('Com \<times> 'Var Mds) list"
  where "add_initial_modes cmds = zip cmds (replicate (length cmds) mds\<^sub>s)"

definition no_assumptions_on_termination :: "'Com list \<Rightarrow> bool"
  where "no_assumptions_on_termination cmds =
  (\<forall> mem mem' cms'.
    (add_initial_modes cmds, mem) \<rightarrow>\<^sup>* (cms', mem') \<and>
    list_all (\<lambda> c. c = stop) (map fst cms') \<longrightarrow>
      (\<forall> mds' \<in> set (map snd cms'). mds' AsmNoRead = {} \<and> mds' AsmNoWrite = {}))"

(* SIFUM-security for programs: *)
definition prog_sifum_secure :: "'Com list \<Rightarrow> bool"
  where "prog_sifum_secure cmds =
  (no_assumptions_on_termination cmds \<and>
   (\<forall> mem\<^sub>1 mem\<^sub>2. mem\<^sub>1 =\<^sup>l mem\<^sub>2 \<longrightarrow>
    (\<forall> k cms\<^sub>1' mem\<^sub>1'.
     (add_initial_modes cmds, mem\<^sub>1) \<rightarrow>\<^bsub>k\<^esub> (cms\<^sub>1', mem\<^sub>1') \<longrightarrow>
      (\<exists> cms\<^sub>2' mem\<^sub>2'. (add_initial_modes cmds, mem\<^sub>2) \<rightarrow>\<^bsub>k\<^esub> (cms\<^sub>2', mem\<^sub>2') \<and>
                      map snd cms\<^sub>1' = map snd cms\<^sub>2' \<and>
                      length cms\<^sub>2' = length cms\<^sub>1' \<and>
                      (\<forall> x. dma x = Low \<and> (\<forall> i < length cms\<^sub>1'.
                        x \<notin> snd (cms\<^sub>1' ! i) AsmNoRead) \<longrightarrow> mem\<^sub>1' x = mem\<^sub>2' x)))))"

subsection \<open>Sound Mode Use\<close>

definition doesnt_read :: "'Com \<Rightarrow> 'Var \<Rightarrow> bool"
  where
  "doesnt_read c x = (\<forall> mds mem c' mds' mem'.
  \<langle> c, mds, mem \<rangle> \<leadsto> \<langle> c', mds', mem' \<rangle> \<longrightarrow>
  ((\<forall> v. \<langle> c, mds, mem (x := v) \<rangle> \<leadsto> \<langle> c', mds', mem' (x := v) \<rangle>) \<or>
   (\<forall> v. \<langle> c, mds, mem (x := v) \<rangle> \<leadsto> \<langle> c', mds', mem' \<rangle>)))"

definition doesnt_modify :: "'Com \<Rightarrow> 'Var \<Rightarrow> bool"
  where
  "doesnt_modify c x = (\<forall> mds mem c' mds' mem'. (\<langle> c, mds, mem \<rangle> \<leadsto> \<langle> c', mds', mem' \<rangle>) \<longrightarrow>
                        mem x = mem' x)"

(* Local reachability of local configurations: *)
inductive_set loc_reach :: "('Com, 'Var, 'Val) LocalConf \<Rightarrow> ('Com, 'Var, 'Val) LocalConf set"
  for lc :: "(_, _, _) LocalConf"
  where
  refl : "\<langle>fst (fst lc), snd (fst lc), snd lc\<rangle> \<in> loc_reach lc" |
  step : "\<lbrakk> \<langle>c', mds', mem'\<rangle> \<in> loc_reach lc;
            \<langle>c', mds', mem'\<rangle> \<leadsto> \<langle>c'', mds'', mem''\<rangle> \<rbrakk> \<Longrightarrow>
          \<langle>c'', mds'', mem''\<rangle> \<in> loc_reach lc" |
  mem_diff : "\<lbrakk> \<langle> c', mds', mem' \<rangle> \<in> loc_reach lc;
                (\<forall> x \<in> mds' AsmNoWrite. mem' x = mem'' x) \<rbrakk> \<Longrightarrow>
              \<langle> c', mds', mem'' \<rangle> \<in> loc_reach lc"

definition locally_sound_mode_use :: "(_, _, _) LocalConf \<Rightarrow> bool"
  where
  "locally_sound_mode_use lc =
  (\<forall> c' mds' mem'. \<langle> c', mds', mem' \<rangle> \<in> loc_reach lc \<longrightarrow>
    (\<forall> x. (x \<in> mds' GuarNoRead \<longrightarrow> doesnt_read c' x) \<and>
          (x \<in> mds' GuarNoWrite \<longrightarrow> doesnt_modify c' x)))"

definition compatible_modes :: "('Var Mds) list \<Rightarrow> bool"
  where
  "compatible_modes mdss = (\<forall> (i :: nat) x. i < length mdss \<longrightarrow>
    (x \<in> (mdss ! i) AsmNoRead \<longrightarrow>
     (\<forall> j < length mdss. j \<noteq> i \<longrightarrow> x \<in> (mdss ! j) GuarNoRead)) \<and>
    (x \<in> (mdss ! i) AsmNoWrite \<longrightarrow>
     (\<forall> j < length mdss. j \<noteq> i \<longrightarrow> x \<in> (mdss ! j) GuarNoWrite)))"

definition reachable_mode_states :: "('Com, 'Var, 'Val) GlobalConf \<Rightarrow> (('Var Mds) list) set"
  where "reachable_mode_states gc =
  {mdss. (\<exists> cms' mem'. gc \<rightarrow>\<^sup>* (cms', mem') \<and> map snd cms' = mdss)}"

definition globally_sound_mode_use :: "('Com, 'Var, 'Val) GlobalConf \<Rightarrow> bool"
  where "globally_sound_mode_use gc =
  (\<forall> mdss. mdss \<in> reachable_mode_states gc \<longrightarrow> compatible_modes mdss)"

primrec sound_mode_use :: "(_, _, _) GlobalConf \<Rightarrow> bool"
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
  by (auto simp: mm_equiv_sym low_indistinguishable_def low_mds_eq_def)

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
