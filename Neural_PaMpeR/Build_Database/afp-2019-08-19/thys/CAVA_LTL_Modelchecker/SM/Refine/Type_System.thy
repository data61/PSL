section \<open>Type System\<close>
theory Type_System
imports Main Gen_Scheduler_Refine Decide_Locality
begin
  text \<open>Currently only a very basic type system:
    Checks that no expression contains overflowing numerals,
    and that all accessed variables exist.
\<close>

  section \<open>Typing of Programs\<close>

  type_synonym tenv_valuation = "ident \<rightharpoonup> unit"
  type_synonym tenv_fs = "tenv_valuation \<times> tenv_valuation"

  definition ty_val :: "tenv_valuation \<Rightarrow> valuation \<Rightarrow> bool" where
    "ty_val \<Gamma> vars \<equiv> dom \<Gamma> = dom vars"

  abbreviation "ty_local_state \<Gamma> ls \<equiv> ty_val \<Gamma> (local_state.variables ls)"
  abbreviation "ty_global_state \<Gamma> gs \<equiv> ty_val \<Gamma> (global_state.variables gs)"

  fun ty_fs :: "tenv_fs \<Rightarrow> focused_state \<Rightarrow> bool" where
    "ty_fs (\<Gamma>l, \<Gamma>g) (ls,gs) \<longleftrightarrow> ty_local_state \<Gamma>l ls \<and> ty_global_state \<Gamma>g gs"

  declare ty_fs.simps[simp del]  

  fun ty_expr :: "tenv_fs \<Rightarrow> exp \<rightharpoonup> unit"
  where
    "ty_expr (\<Gamma>l, \<Gamma>g) (e_var x) = (if x\<in>dom \<Gamma>l \<or> x\<in>dom \<Gamma>g then Some () else None)"
  | "ty_expr (\<Gamma>l, \<Gamma>g) (e_localvar x) = (if x\<in>dom \<Gamma>l then Some () else None)"
  | "ty_expr (\<Gamma>l, \<Gamma>g) (e_globalvar x) = (if x\<in>dom \<Gamma>g then Some () else None)"
  | "ty_expr _ (e_const c) = (if min_signed \<le> c \<and> c \<le> max_signed then Some () else None)"
  | "ty_expr (\<Gamma>l, \<Gamma>g) (e_bin bop e1 e2) = do {
      ty_expr (\<Gamma>l, \<Gamma>g) e1;
      ty_expr (\<Gamma>l, \<Gamma>g) e2;
      Some ()
    }"
  | "ty_expr (\<Gamma>l, \<Gamma>g) (e_un uop e) = do {
      ty_expr (\<Gamma>l, \<Gamma>g) e;
      Some ()
    }"

  lemma ty_expr_noerr: 
    notes [simp] = ty_fs.simps
    shows "ty_fs \<Gamma> fs \<Longrightarrow> eval_exp e fs \<noteq> None \<longleftrightarrow> ty_expr \<Gamma> e \<noteq> None"
    apply (induction e)
    apply (cases fs, cases \<Gamma>)
    apply (auto split: option.splits simp: ty_val_def) []
    apply (cases fs, cases \<Gamma>)
    apply (auto split: option.splits simp: ty_val_def) []
    apply (cases fs, cases \<Gamma>)
    apply (auto split: option.splits simp: ty_val_def) []
    apply (cases fs, cases \<Gamma>)
    apply (auto split: option.splits simp: ty_val_def) []
    apply (cases fs, cases \<Gamma>)
    apply (auto split: option.splits Option.bind_splits simp: ty_val_def) []
    apply (cases fs, cases \<Gamma>)
    apply (auto split: option.splits simp: ty_val_def) []
    done

  lemma ty_expr_noerr': 
    "ty_fs \<Gamma> fs \<Longrightarrow> ty_expr \<Gamma> e = Some () \<longleftrightarrow> (\<exists>v. eval_exp e fs = Some v)"
    using ty_expr_noerr
    by auto

  type_synonym tenv_cmd = "tenv_fs \<times> bool" 

  function ty_cmd :: "tenv_cmd \<Rightarrow> cmd \<Rightarrow> bool" where
    "ty_cmd ((\<Gamma>l,\<Gamma>g),loop) (Assign c x e) \<longleftrightarrow> ty_expr (\<Gamma>l,\<Gamma>g) c \<noteq> None \<and>
      (x\<in>dom \<Gamma>l | x\<in>dom \<Gamma>g) \<and> ty_expr (\<Gamma>l,\<Gamma>g) e \<noteq> None"
  | "ty_cmd ((\<Gamma>l,\<Gamma>g),loop) (Assign_local c x e) \<longleftrightarrow> ty_expr (\<Gamma>l,\<Gamma>g) c \<noteq> None \<and>
      (x\<in>dom \<Gamma>l) \<and> ty_expr (\<Gamma>l,\<Gamma>g) e \<noteq> None"
  | "ty_cmd ((\<Gamma>l,\<Gamma>g),loop) (Assign_global c x e) \<longleftrightarrow> ty_expr (\<Gamma>l,\<Gamma>g) c \<noteq> None \<and>
      (x\<in>dom \<Gamma>g) \<and> ty_expr (\<Gamma>l,\<Gamma>g) e \<noteq> None"
  | "ty_cmd ((\<Gamma>l,\<Gamma>g),loop) (Test e) \<longleftrightarrow> ty_expr (\<Gamma>l,\<Gamma>g) e \<noteq> None"
  | "ty_cmd ((\<Gamma>l,\<Gamma>g),loop) (Skip) \<longleftrightarrow> True"
  | "ty_cmd ((\<Gamma>l,\<Gamma>g),loop) (Seq c1 c2) \<longleftrightarrow> ty_cmd ((\<Gamma>l,\<Gamma>g),loop) c1 \<and> ty_cmd ((\<Gamma>l,\<Gamma>g),loop) c2"
  | "ty_cmd ((\<Gamma>l,\<Gamma>g),loop) (Or c1 c2) \<longleftrightarrow> ty_cmd ((\<Gamma>l,\<Gamma>g),loop) c1 \<and> ty_cmd ((\<Gamma>l,\<Gamma>g),loop) c2"
  | "ty_cmd ((\<Gamma>l,\<Gamma>g),loop) (Break) \<longleftrightarrow> loop"
  | "ty_cmd ((\<Gamma>l,\<Gamma>g),loop) (Continue) \<longleftrightarrow> loop"
  | "ty_cmd ((\<Gamma>l,\<Gamma>g),loop) (Iterate c1 c2) \<longleftrightarrow> ty_cmd ((\<Gamma>l,\<Gamma>g),True) c1 \<and> ty_cmd ((\<Gamma>l,\<Gamma>g),True) c2"
  | "ty_cmd ((\<Gamma>l,\<Gamma>g),loop) (Invalid) \<longleftrightarrow> False"
  by pat_completeness auto
  
  termination
    apply (relation "inv_image (reachable_term_order_aux <*mlex*> measure size) snd")
    apply (auto simp: mlex_prod_def)
    done
    
  theorem ty_cmd_no_internal: "ty_cmd (\<Gamma>,False) c \<Longrightarrow> cfg c a c' \<Longrightarrow> isl a"
    apply (rotate_tac)
    apply (induction rule: cfg.induct)
    apply (cases \<Gamma>, (auto) [])+
    done

  lemma ty_cmd_pres_aux: "ty_cmd ((\<Gamma>l,\<Gamma>g),loop) c \<Longrightarrow> cfg c a c' \<Longrightarrow> 
    (ty_cmd ((\<Gamma>l,\<Gamma>g),loop) c' \<or> a=Inr AIBreak \<or> a=Inr AIContinue)"  
    apply (rotate_tac)
    apply (induction arbitrary: loop rule: cfg.induct)
    apply auto
    done
  
  corollary ty_cmd_pres: 
    "ty_cmd ((\<Gamma>l,\<Gamma>g),False) c \<Longrightarrow> cfg c a c' \<Longrightarrow> ty_cmd ((\<Gamma>l,\<Gamma>g),False) c'"
    apply (frule (1) ty_cmd_pres_aux)
    apply (frule (1) ty_cmd_no_internal)
    apply auto
    done

  definition ty_proc_decl :: "tenv_valuation \<Rightarrow> proc_decl \<Rightarrow> bool" where
    "ty_proc_decl \<Gamma>g pd \<equiv> let
      \<Gamma>l = (\<lambda>x. if x \<in> set (proc_decl.local_vars pd) then Some () else None)
    in
      ty_cmd ((\<Gamma>l,\<Gamma>g),False) (proc_decl.body pd)"

  definition ty_program :: "program \<Rightarrow> bool" where
    "ty_program prog == let
      \<Gamma>g = (\<lambda>x. if x\<in>set (program.global_vars prog) then Some () else None)
    in
      \<forall>pd\<in>set (program.processes prog). ty_proc_decl \<Gamma>g pd"

  definition ty_local :: "cmd \<Rightarrow> local_state \<Rightarrow> global_state \<Rightarrow> bool" where
    "ty_local c ls gs \<equiv> \<exists>\<Gamma>. ty_cmd (\<Gamma>,False) c \<and> ty_fs \<Gamma> (ls,gs)"

  definition "cfg' c a c' \<equiv> cfg c (Inl a) c'"
  lemma cfg'_eq: "ty_cmd (\<Gamma>,False) c \<Longrightarrow> cfg c a c' \<longleftrightarrow> (\<exists>aa. a=Inl aa \<and> cfg' c aa c')"
    by (cases a) (auto dest: ty_cmd_no_internal[of _ c a c'] simp: cfg'_def)

  lemma cfg_eq: "ty_cmd (\<Gamma>,False) c \<Longrightarrow> cfg' c a c' \<longleftrightarrow> cfg c (Inl a) c'" 
    by (auto simp: cfg'_eq)

  section \<open>Typing of Actions\<close>  
  text \<open>
    We split the proof that steps from well-typed configurations
    do not fail and preserve well-typedness in two steps:
    
    First, we show that actions from well-types commands are well-typed.
    Then, we show that well-typed actions do not fail, and preserve 
      well-typedness.
\<close>


  fun ty_la :: "tenv_fs \<Rightarrow> action \<Rightarrow> bool" where
    "ty_la (\<Gamma>l,\<Gamma>g) (AAssign c x e) \<longleftrightarrow> ty_expr (\<Gamma>l,\<Gamma>g) c \<noteq> None \<and>
      (x\<in>dom \<Gamma>l \<or> x\<in>dom \<Gamma>g) \<and> ty_expr (\<Gamma>l,\<Gamma>g) e \<noteq> None"  
  | "ty_la (\<Gamma>l,\<Gamma>g) (AAssign_local c x e) \<longleftrightarrow> ty_expr (\<Gamma>l,\<Gamma>g) c \<noteq> None \<and>
      x\<in>dom \<Gamma>l \<and> ty_expr (\<Gamma>l,\<Gamma>g) e \<noteq> None"
  | "ty_la (\<Gamma>l,\<Gamma>g) (AAssign_global c x e) \<longleftrightarrow> ty_expr (\<Gamma>l,\<Gamma>g) c \<noteq> None \<and>
      x\<in>dom \<Gamma>g \<and> ty_expr (\<Gamma>l,\<Gamma>g) e \<noteq> None"
  | "ty_la (\<Gamma>l,\<Gamma>g) (ATest e) \<longleftrightarrow> ty_expr (\<Gamma>l,\<Gamma>g) e \<noteq> None"
  | "ty_la (\<Gamma>l,\<Gamma>g) (ASkip) \<longleftrightarrow> True"


  lemma ty_cmd_imp_ty_la_aux:
    assumes "ty_cmd (\<Gamma>,loop) c"
    assumes "cfg c (Inl a) c'"
    shows "ty_la \<Gamma> a"
    using assms (2,1)
    apply (induction c "Inl a::action+brk_ctd" c' arbitrary: loop)
    apply (case_tac [!] \<Gamma>)
    apply auto
    done

  lemma ty_cmd_imp_ty_la:
    assumes "ty_cmd (\<Gamma>,False) c"
    assumes "cfg' c a c'"
    shows "ty_la \<Gamma> a"
    using assms
    unfolding cfg_eq[OF assms(1)]
    by (rule ty_cmd_imp_ty_la_aux)

  lemma ty_en_defined:
    assumes "ty_fs \<Gamma> fs"
    assumes "ty_la \<Gamma> a"
    shows "la_en fs a \<noteq> None"
    using assms
    apply (cases \<Gamma>, cases fs)
    apply (cases a)
    apply (auto
      split: Option.bind_splits 
      dest: ty_expr_noerr)
    done

  lemma ty_ex_defined:  
    assumes "ty_fs \<Gamma> fs"
    assumes "ty_la \<Gamma> a"
    assumes "la_en fs a = Some True"
    shows "la_ex fs a \<noteq> None"
    using assms
    apply (cases \<Gamma>, cases fs)
    apply (cases a)
    apply (auto
      split: Option.bind_splits 
      dest: ty_expr_noerr, 
      auto simp: ty_val_def ty_fs.simps)
    apply blast+
    done

  lemma ty_ex_pres:
    assumes "ty_fs \<Gamma> fs"
    assumes "la_ex fs a = Some fs'"
    shows "ty_fs \<Gamma> fs'"
    using assms
    apply (cases \<Gamma>, cases fs)
    apply (cases a)
    apply (auto
      split: Option.bind_splits if_split_asm 
      dest: ty_expr_noerr, 
      auto simp: ty_val_def ty_fs.simps)
    done


  section \<open>Actions that do not fail\<close>  

  text \<open>
    We define a refinement of the actions, which 
    map failure to not enabled/identity.
    
    This allows for simple POR-related proofs, as non-failure can
    be assumed.
  \<close>
  definition "la_en' fs a \<equiv> case la_en fs a of Some b \<Rightarrow> b | None \<Rightarrow> False"
  definition "la_ex' fs a \<equiv> case la_ex fs a of Some fs' \<Rightarrow> fs' | None \<Rightarrow> fs"

  interpretation li': Gen_Scheduler'_linit cfg' la_en' la_ex' "{init_gc prog}" global_config.state
    for prog .

  interpretation li': sched_typing
    cfg la_en la_ex
    cfg' la_en' la_ex'
    ty_local
    apply unfold_locales
    unfolding ty_local_def
    apply (auto 
      simp: cfg'_eq
      simp: la_en'_def dest: ty_en_defined[OF _ ty_cmd_imp_ty_la]
      simp: la_ex'_def dest: ty_ex_defined[OF _ ty_cmd_imp_ty_la]
      dest: ty_ex_pres ty_cmd_pres
      split: option.splits
      ) [4]

    apply (clarsimp)
    apply (intro exI conjI)
    apply assumption+
    apply (frule (1) ty_ex_pres)
    apply (simp add: ty_val_def ty_fs.simps)
    done
    
  locale well_typed_prog =
    fixes prog
    assumes well_typed_prog: "ty_program prog"
  begin
    lemma ty_init[simp, intro!]: "li'.wf_gglobal (init_gc prog)"
      using well_typed_prog
      apply (auto 
        simp: in_multiset_in_set
        simp: init_gc_def init_pc_def li'.wf_gglobal_def ty_local_def
        simp: ty_program_def ty_proc_decl_def
        dest!: split_list)
      apply (intro exI conjI)
      apply assumption
      apply (auto 
        simp: ty_fs.simps ty_val_def init_valuation_def 
        split: if_split_asm
        )
      done
 
    sublocale li': sched_typing_init
      cfg la_en la_ex
      cfg' la_en' la_ex'
      "{init_gc prog}" global_config.state
      ty_local
      apply unfold_locales
      by auto

    lemma "li'.sa.accept prog = ref_accept prog"  
      by (rule li'.accept_eq)

    lemma "ref_is_run prog r \<longleftrightarrow> (\<exists>r'. r=Some o r' \<and> li'.sa.is_run prog r')"  
      by (rule li'.is_run_conv)

  end

end
