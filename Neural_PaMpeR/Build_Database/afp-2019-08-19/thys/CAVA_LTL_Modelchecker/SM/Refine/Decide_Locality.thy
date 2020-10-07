section \<open>Decide Locality of Variables\<close>
theory Decide_Locality
imports "../RefPoint/SM_Semantics"
begin

lemmas [simp del] = union_mset_add_mset_left union_mset_add_mset_right

lemma dom_init_valuation_eq_set[simp]: "dom (init_valuation l) = set l"
  unfolding init_valuation_def[abs_def]
  by (auto split: if_split_asm)

lemma bind_set_map: "\<lbrakk> g`m=m'; \<And>x. x\<in>m \<Longrightarrow> f x = f' (g x) \<rbrakk> \<Longrightarrow> m\<bind>f = m'\<bind>f'"
  by auto

lemma image_mset_eq_add_conv:
  "f `# m = a' + b' \<longleftrightarrow> (\<exists> a b. m = a + b \<and> f `# a = a' \<and> f `# b = b')"
  using image_mset_union mset_map_split_orig by metis

lemma image_mset_eq_sng_conv:
  "image_mset f m = {#y#} \<longleftrightarrow> (\<exists>x. m={#x#} \<and> y = f x)"
  by (cases m) auto

(* TODO: Move to general analysis *)
subsection \<open>Variables\<close>  

text \<open>Executions do not change the variables of the state\<close>
abbreviation "ls_vars ls \<equiv> (dom (local_state.variables ls))"
abbreviation "lc_vars lc \<equiv> ls_vars (local_config.state lc)"

abbreviation "gs_vars gs \<equiv> (dom (global_state.variables gs))"
abbreviation "gc_vars gc \<equiv> gs_vars (global_config.state gc)"

lemma la_ex_pres_ls_vars[simp]: 
  "la_ex (ls,gs) a = Some (ls',gs') \<Longrightarrow> ls_vars ls' = ls_vars ls"
  by (induction a) (auto split: if_split_asm Option.bind_splits)

lemma la_ex_pres_gs_vars[simp]: 
  "la_ex (ls,gs) a = Some (ls',gs') \<Longrightarrow> gs_vars gs' = gs_vars gs"
  by (induction a) (auto split: if_split_asm Option.bind_splits)


text \<open>We define a program transformation that statically decides whether
   variable accesses are local or global\<close>

fun dloc_exp :: "ident set \<Rightarrow> exp \<Rightarrow> exp" where
  "dloc_exp L (e_var x) = (if x\<in>L then e_localvar x else e_globalvar x)"
| "dloc_exp _ (e_localvar x) = e_localvar x"  
| "dloc_exp _ (e_globalvar x) = e_globalvar x"  
| "dloc_exp _ (e_const c) = e_const c"
| "dloc_exp L (e_bin bop e1 e2) = e_bin bop (dloc_exp L e1) (dloc_exp L e2)"
| "dloc_exp L (e_un uop e) = e_un uop (dloc_exp L e)"

fun dloc_cmd :: "ident set \<Rightarrow> cmd \<Rightarrow> cmd" where
  "dloc_cmd L (Assign c x e) = 
    (if x\<in>L then Assign_local else Assign_global) (dloc_exp L c) x (dloc_exp L e)"
| "dloc_cmd L (Assign_local c x e) = Assign_local (dloc_exp L c) x (dloc_exp L e)"
| "dloc_cmd L (Assign_global c x e) = Assign_global (dloc_exp L c) x (dloc_exp L e)"
| "dloc_cmd L (Test e) = Test (dloc_exp L e)"
| "dloc_cmd L Skip = Skip"
| "dloc_cmd L (Seq c1 c2) = Seq (dloc_cmd L c1) (dloc_cmd L c2)"
| "dloc_cmd L (Or c1 c2) = Or (dloc_cmd L c1) (dloc_cmd L c2)"
| "dloc_cmd L Break = Break"
| "dloc_cmd L Continue = Continue"
| "dloc_cmd L (Iterate c1 c2) = Iterate (dloc_cmd L c1) (dloc_cmd L c2)"
| "dloc_cmd L Invalid = Invalid"

definition dloc_proc :: "proc_decl \<Rightarrow> proc_decl" where
  "dloc_proc pd \<equiv> proc_decl.body_update (dloc_cmd (set (proc_decl.local_vars pd))) pd"

definition dloc :: "program \<Rightarrow> program" where 
  "dloc \<equiv> program.processes_update (map dloc_proc)"

definition dloc_lc :: "local_config \<Rightarrow> local_config" where
  "dloc_lc lc \<equiv> \<lparr> 
    local_config.command 
      = dloc_cmd 
          (lc_vars lc) 
          (local_config.command lc),
    local_config.state = local_config.state lc\<rparr>"

definition dloc_gc :: "global_config \<Rightarrow> global_config" where
  "dloc_gc gc \<equiv> \<lparr>
    global_config.processes = image_mset dloc_lc (global_config.processes gc),
    global_config.state = global_config.state gc
  \<rparr>"

lemma dloc_rel_init: "dloc_gc (init_gc prog) = init_gc (dloc prog)"
  unfolding dloc_gc_def init_gc_def dloc_lc_def[abs_def] init_pc_def[abs_def]
    dloc_def dloc_proc_def[abs_def] 
  apply (auto simp: image_mset.compositionality)
  apply (fo_rule fun_cong arg_cong)+
  apply (auto)
  done

fun dloc_a :: "ident set \<Rightarrow> action \<Rightarrow> action" where
  "dloc_a L ((AAssign c x e)) = ((if x\<in>L then AAssign_local else AAssign_global)
    (dloc_exp L c) x (dloc_exp L e))"
| "dloc_a L ((AAssign_local c x e)) = (AAssign_local (dloc_exp L c) x (dloc_exp L e))"
| "dloc_a L ((AAssign_global c x e)) = (AAssign_global (dloc_exp L c) x (dloc_exp L e))"
| "dloc_a L ((ATest e)) = (ATest (dloc_exp L e))"
| "dloc_a L (ASkip) = ASkip"

fun dloc_ai :: "ident set \<Rightarrow> action+brk_ctd \<Rightarrow> action+brk_ctd" where
  "dloc_ai L (Inr x) = Inr x"
| "dloc_ai L (Inl x) = Inl (dloc_a L x)"

lemma dloc_ai_conv:
  "Inr b = dloc_ai L y \<longleftrightarrow> y=Inr b"
  "Inl a = dloc_ai L y \<longleftrightarrow> (\<exists>aa. y=Inl aa \<and> a=dloc_a L aa)"
  apply (cases y, auto) []
  apply (cases y, auto) []
  done

lemma dloc_eq_skip_conv[simp]:
  "Skip=dloc_cmd L c \<longleftrightarrow> c=Skip"
  "dloc_cmd L c=Skip \<longleftrightarrow> c=Skip"
  by ((case_tac c, auto) [])+

lemma cfg_dloc: "cfg (dloc_cmd L c) da dc' \<longleftrightarrow> (\<exists>c' a. dc'=dloc_cmd L c' \<and> da=dloc_ai L a \<and> cfg c a c')"
proof (safe)
  have aux1: "\<And>c1 c2 c' S. Seq c1 c2 = dloc_cmd S c' 
  \<longleftrightarrow> (\<exists>c1' c2'. c'=Seq c1' c2' \<and> c1=dloc_cmd S c1' \<and> c2=dloc_cmd S c2')"
    by (case_tac "(S,c')" rule: dloc_cmd.cases) auto

  assume A: "cfg (dloc_cmd L c) da dc'"
  thus "\<exists>c' a. dc'=dloc_cmd L c' \<and> da=dloc_ai L a \<and> cfg c a c'"
  proof (induction "dloc_cmd L c" da dc' arbitrary: c)
    case Ass thus ?case by (cases c) (auto intro: cfg.intros split: if_split_asm)
  next
    case (Assl x e) thus ?case by (cases c) (auto intro: cfg.intros intro!: exI split: if_split_asm)
  next
    case (Assg x e) thus ?case by (cases c) (auto intro: cfg.intros intro!: exI split: if_split_asm)
  next
    case (Test e) thus ?case by (cases c) (auto intro: cfg.intros intro!: exI split: if_split_asm)
  next
    case (Seq1 dc2 c) thus ?case
      apply (auto simp add: aux1)
      apply (intro exI conjI)
      apply (auto intro: cfg.Seq1)
      done
  next 
    case (Seq2' dc1 da dc2 c) thus ?case
      apply (auto simp add: aux1)
      apply (fastforce intro: cfg.Seq2')   
      done
  next
    case (Seq2 dc1 da dc1' dc2 c)
    with aux1 obtain c1 c2 where [simp]: "c=Seq c1 c2" "dc1=dloc_cmd L c1" "dc2=dloc_cmd L c2"
      by auto
    from Seq2.hyps(2) obtain c1' a where 
      [simp]: "dc1' = dloc_cmd L c1'" "da = dloc_ai L a" 
      and 1: "cfg c1 a c1'"
      by fastforce
    from \<open>dc1'\<noteq>Skip\<close> have "c1'\<noteq>Skip" by simp
    with cfg.Seq2[OF 1] show ?case by force
  next
    case (Iterate2' dc1 da dc2 c)
    from Iterate2'.hyps(3)
    obtain c1 c2 where [simp]: "c = Iterate c1 c2" "dc1 = dloc_cmd L c1" "dc2 = dloc_cmd L c2"
      by (cases c) (auto split: if_split_asm) 
    from Iterate2'.hyps(2) obtain a where 
      S1: "Inl da = dloc_ai L a" 
      and 1: "cfg c1 a Skip"
      by fastforce
    then obtain aa where [simp]: "a=Inl aa" by (cases a) (auto split: if_split_asm)
    note [simp] = S1
    from cfg.Iterate2'[OF 1[simplified]] show ?case by force
  next
    case (Iterate2 dc1 da dc1' dc2)
    from Iterate2.hyps(4)
    obtain c1 c2 where [simp]: "c = Iterate c1 c2" "dc1 = dloc_cmd L c1" "dc2 = dloc_cmd L c2"
      by (cases c) (auto split: if_split_asm) 
    from Iterate2.hyps(2) obtain c1' a where 
      S1: "dc1' = dloc_cmd L c1'" "Inl da = dloc_ai L a" 
      and 1: "cfg c1 a c1'"
      by fastforce
    then obtain aa where [simp]: "a=Inl aa" by (cases a) (auto split: if_split_asm)
    note [simp] = S1
    from cfg.Iterate2[OF 1[simplified]] \<open>dc1' \<noteq> Skip\<close> show ?case by force
  next
    case (IterateBrk dc1 dc1' dc2) 
    from IterateBrk.hyps(3)
    obtain c1 c2 where [simp]: "c = Iterate c1 c2" "dc1 = dloc_cmd L c1" "dc2 = dloc_cmd L c2"
      by (cases c) (auto split: if_split_asm) 
    from IterateBrk.hyps(2) obtain c1' a where 
      S1: "dc1' = dloc_cmd L c1'" and "Inr AIBreak = dloc_ai L a" 
      and 1: "cfg c1 a c1'"
      by fastforce
    hence [simp]: "a=Inr AIBreak" by (cases "(L,a)" rule: dloc_ai.cases) simp_all
    note [simp] = S1
    from cfg.IterateBrk[OF 1[simplified]] show ?case by force
  next
    case (IterateCtd dc1 dc1' dc2) 
    from IterateCtd.hyps(3)
    obtain c1 c2 where [simp]: "c = Iterate c1 c2" "dc1 = dloc_cmd L c1" "dc2 = dloc_cmd L c2"
      by (cases c) (auto split: if_split_asm) 
    from IterateCtd.hyps(2) obtain c1' a where 
      S1: "dc1' = dloc_cmd L c1'" and "Inr AIContinue = dloc_ai L a" 
      and 1: "cfg c1 a c1'"
      by fastforce
    hence [simp]: "a=Inr AIContinue" by (cases "(L,a)" rule: dloc_ai.cases) simp_all
    note [simp] = S1
    from cfg.IterateCtd[OF 1[simplified]] show ?case by force
  next
    case (Or1 dc1 da dc1' dc2) thus ?case
      apply (case_tac c, simp_all split: if_split_asm)
      apply (fastforce intro: cfg.intros)
      done
  next    
    case (Or2 dc2 da dc2' dc1) thus ?case
      apply (case_tac c, simp_all split: if_split_asm)
      apply (fastforce intro: cfg.intros)
      done
    apply_end (case_tac c, auto intro: cfg.intros intro!: exI split: if_split_asm) []
    apply_end (case_tac c, auto intro: cfg.intros intro!: exI split: if_split_asm) []
    apply_end (case_tac ca, auto intro: cfg.intros intro!: exI split: if_split_asm) []
  qed
next
  fix c' a
  assume "cfg c a c'"
  thus "cfg (dloc_cmd L c) (dloc_ai L a) (dloc_cmd L c')"
    by (induction) (auto intro: cfg.intros)
qed
    
lemma choose_action_as_map_aux: " 
  (map_prod (dloc_ai (lc_vars lc)) (dloc_cmd (lc_vars lc)))`{(a, c'). cfg (command lc) a c'}
  = {(a, c'). cfg (command (dloc_lc lc)) a c'}"
  by (auto simp: dloc_lc_def map_prod_def image_def cfg_dloc)

lemma dloc_lc_state[simp]: "local_config.state (dloc_lc lc) = local_config.state lc"  
  unfolding dloc_lc_def by simp

lemma dloc_gc_state[simp]: "global_config.state (dloc_gc gc) = global_config.state gc"  
  unfolding dloc_gc_def by simp

lemma dloc_exp_correct[simp]: 
  "eval_exp (dloc_exp (ls_vars ls) e) (ls, gs) = eval_exp e (ls,gs)"
  by (induction e) (auto split: option.splits)

lemma dloc_la_en_correct[simp]: 
  "la_en (ls, gs) (dloc_a (ls_vars ls) a) = la_en (ls, gs) a"
  by (cases a) auto

lemma dloc_la_ex_correct[simp]:
  "la_ex (ls,gs) (dloc_a (ls_vars ls) a) = la_ex (ls,gs) a"
  by (cases a) auto

lemma dloc_rel_gstep_succ: 
  "li.gstep_succ (dloc_gc gc) = map_option dloc_gc ` li.gstep_succ gc"
  apply (rule sym)
  apply safe

  apply (erule li.gstep_succE, simp_all) []
    apply (force 
      intro: li.gstep_succ_fail_cmd li.gstep_succ_fail_en li.gstep_succ_fail_ex
      simp: dloc_gc_def cfg_dloc dloc_lc_def) []

    apply (force 
      intro: li.gstep_succ_fail_cmd li.gstep_succ_fail_en li.gstep_succ_fail_ex
      simp: dloc_gc_def cfg_dloc dloc_lc_def) []

    apply (force intro: li.gstep_succ_fail_en li.gstep_succ_fail_ex
      simp: dloc_gc_def cfg_dloc dloc_lc_def) []
    apply (force intro: li.gstep_succ_fail_en li.gstep_succ_fail_ex li.gstep_succ_succ
      simp: dloc_gc_def cfg_dloc dloc_lc_def) []

  apply (erule li.gstep_succE, 
      clarsimp_all 
        simp: dloc_gc_def image_mset_eq_add_conv image_mset_eq_sng_conv
        simp: cfg_dloc dloc_lc_def dloc_ai_conv
      ) []
    apply (force 
      intro: li.gstep_succ_fail_cmd li.gstep_succ_fail_en li.gstep_succ_fail_ex
      simp: dloc_gc_def cfg_dloc dloc_lc_def) []
    apply (force intro: li.gstep_succ_fail_en li.gstep_succ_fail_ex
      simp: dloc_gc_def cfg_dloc dloc_lc_def) []
    apply (auto intro: li.gstep_succ_fail_en li.gstep_succ_fail_ex
      simp: dloc_gc_def cfg_dloc dloc_lc_def) []
    apply (force intro!: li.gstep_succ_succ image_eqI[rotated]
      simp: dloc_gc_def cfg_dloc dloc_lc_def) []

  done

lemma dloc_rel_gstep: "(map_option dloc_gc gc, dgc') \<in> li.gstep \<longleftrightarrow>
  (\<exists> gc'. dgc'= map_option dloc_gc gc' \<and> (gc, gc') \<in> li.gstep)"
  using li.gstep_eq_conv dloc_rel_gstep_succ by auto
  

lemma dloc_rel_label: "li.label (map_option dloc_gc gc) = li.label gc"
  apply (cases gc, simp_all)
  done

interpretation dloc_sim: lbisimulation "br (map_option dloc_gc) (\<lambda> _. True)"
  "li.system_automaton prog" "li.system_automaton (dloc prog)"
  for prog
proof -
  interpret bisim: lbisimulation "br (map_option dloc_gc) (\<lambda> _. True)"
    "li.system_automaton' prog" "li.system_automaton' (dloc prog)"
    apply unfold_locales
    apply (auto simp: build_rel_def li.init_conv simp: dloc_rel_init dloc_rel_gstep dloc_rel_label)
    done
  interpret bisim: lbisimulation "br (map_option dloc_gc) (\<lambda> _. True)"
    "li.system_automaton prog" "li.system_automaton (dloc prog)"
    unfolding li.system_automaton_alt_def
    using bisim.lstutter_extend by this
  show "lbisimulation (br (map_option dloc_gc) (\<lambda> _. True))
    (li.system_automaton prog) (li.system_automaton (dloc prog))"
    by unfold_locales
qed

end

