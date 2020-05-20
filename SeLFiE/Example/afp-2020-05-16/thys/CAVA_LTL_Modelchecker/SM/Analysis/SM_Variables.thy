section \<open>Accessed Variables\<close>
theory SM_Variables
imports "../Refine/SM_Pid"
begin

  subsection "Expressions"

  primrec udvars_of_exp :: "exp \<Rightarrow> ident set" where
      "udvars_of_exp (e_var x) = {x}"
    | "udvars_of_exp (e_localvar x) = {}"
    | "udvars_of_exp (e_globalvar x) = {}"
    | "udvars_of_exp (e_const c) = {}"
    | "udvars_of_exp (e_bin bop e1 e2) = (udvars_of_exp e1) \<union> (udvars_of_exp e2)"
    | "udvars_of_exp (e_un uop e) = (udvars_of_exp e)"

  primrec lvars_of_exp :: "exp \<Rightarrow> ident set" where
      "lvars_of_exp (e_var x) = {}"
    | "lvars_of_exp (e_localvar x) = {x}"
    | "lvars_of_exp (e_globalvar x) = {}"
    | "lvars_of_exp (e_const c) = {}"
    | "lvars_of_exp (e_bin bop e1 e2) = (lvars_of_exp e1) \<union> (lvars_of_exp e2)"
    | "lvars_of_exp (e_un uop e) = (lvars_of_exp e)"
      
  primrec gvars_of_exp :: "exp \<Rightarrow> ident set" where
      "gvars_of_exp (e_var x) = {}"
    | "gvars_of_exp (e_localvar x) = {}"
    | "gvars_of_exp (e_globalvar x) = {x}"
    | "gvars_of_exp (e_const c) = {}"
    | "gvars_of_exp (e_bin bop e1 e2) = (gvars_of_exp e1) \<union> (gvars_of_exp e2)"
    | "gvars_of_exp (e_un uop e) = (gvars_of_exp e)"

  subsection "Commands"
  primrec join_cmd_exp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (exp \<Rightarrow> 'a) \<Rightarrow> cmd \<Rightarrow> 'a" where  
    "join_cmd_exp z join f (Assign c x e) = join (f c) (f e)"
  | "join_cmd_exp z join f (Assign_local c x e) = join (f c) (f e)"
  | "join_cmd_exp z join f (Assign_global c x e) = join (f c) (f e)"
  | "join_cmd_exp z join f (Test e) = f e"
  | "join_cmd_exp z join f (Skip) = z"
  | "join_cmd_exp z join f (Seq c1 c2) 
      = join (join_cmd_exp z join f c1) (join_cmd_exp z join f c2)"
  | "join_cmd_exp z join f (Or c1 c2) 
      = join (join_cmd_exp z join f c1) (join_cmd_exp z join f c2)"
  | "join_cmd_exp z join f (Break) = z"
  | "join_cmd_exp z join f (Continue) = z"
  | "join_cmd_exp z join f (Iterate c1 c2) 
      = join (join_cmd_exp z join f c1) (join_cmd_exp z join f c2)"
  | "join_cmd_exp z join f (Invalid) = z"

  abbreviation "union_cmd_exp \<equiv> join_cmd_exp {} (\<union>)"
  abbreviation "all_cmd_exp \<equiv> join_cmd_exp True (\<and>)"
  abbreviation "ex_cmd_exp \<equiv> join_cmd_exp False (\<or>)"

  abbreviation "ud_rvars_of_cmd == union_cmd_exp udvars_of_exp"
  abbreviation "g_rvars_of_cmd == union_cmd_exp gvars_of_exp"
  abbreviation "l_rvars_of_cmd == union_cmd_exp lvars_of_exp"

  primrec ud_wvars_of_cmd :: "cmd \<Rightarrow> ident set" where  
    "ud_wvars_of_cmd (Assign c x e) = {x}"
  | "ud_wvars_of_cmd (Assign_local c x e) = {}"
  | "ud_wvars_of_cmd (Assign_global c x e) = {}"
  | "ud_wvars_of_cmd (Test e) = {}"
  | "ud_wvars_of_cmd (Skip) = {}"
  | "ud_wvars_of_cmd (Seq c1 c2) = (ud_wvars_of_cmd c1 \<union> ud_wvars_of_cmd c2)"
  | "ud_wvars_of_cmd (Or c1 c2) = (ud_wvars_of_cmd c1 \<union> ud_wvars_of_cmd c2)"
  | "ud_wvars_of_cmd (Break) = {}"
  | "ud_wvars_of_cmd (Continue) = {}"
  | "ud_wvars_of_cmd (Iterate c1 c2) = (ud_wvars_of_cmd c1 \<union> ud_wvars_of_cmd c2)"
  | "ud_wvars_of_cmd (Invalid) = {}"

  primrec l_wvars_of_cmd :: "cmd \<Rightarrow> ident set" where  
    "l_wvars_of_cmd (Assign c x e) = {}"
  | "l_wvars_of_cmd (Assign_local c x e) = {x}"
  | "l_wvars_of_cmd (Assign_global c x e) = {}"
  | "l_wvars_of_cmd (Test e) = {}"
  | "l_wvars_of_cmd (Skip) = {}"
  | "l_wvars_of_cmd (Seq c1 c2) = (l_wvars_of_cmd c1 \<union> l_wvars_of_cmd c2)"
  | "l_wvars_of_cmd (Or c1 c2) = (l_wvars_of_cmd c1 \<union> l_wvars_of_cmd c2)"
  | "l_wvars_of_cmd (Break) = {}"
  | "l_wvars_of_cmd (Continue) = {}"
  | "l_wvars_of_cmd (Iterate c1 c2) = (l_wvars_of_cmd c1 \<union> l_wvars_of_cmd c2)"
  | "l_wvars_of_cmd (Invalid) = {}"

  primrec g_wvars_of_cmd :: "cmd \<Rightarrow> ident set" where  
    "g_wvars_of_cmd (Assign c x e) = {}"
  | "g_wvars_of_cmd (Assign_local c x e) = {}"
  | "g_wvars_of_cmd (Assign_global c x e) = {x}"
  | "g_wvars_of_cmd (Test e) = {}"
  | "g_wvars_of_cmd (Skip) = {}"
  | "g_wvars_of_cmd (Seq c1 c2) = (g_wvars_of_cmd c1 \<union> g_wvars_of_cmd c2)"
  | "g_wvars_of_cmd (Or c1 c2) = (g_wvars_of_cmd c1 \<union> g_wvars_of_cmd c2)"
  | "g_wvars_of_cmd (Break) = {}"
  | "g_wvars_of_cmd (Continue) = {}"
  | "g_wvars_of_cmd (Iterate c1 c2) = (g_wvars_of_cmd c1 \<union> g_wvars_of_cmd c2)"
  | "g_wvars_of_cmd (Invalid) = {}"


  definition "udvars_of_cmd c \<equiv> ud_rvars_of_cmd c \<union> ud_wvars_of_cmd c"
  definition "lvars_of_cmd c \<equiv> l_rvars_of_cmd c \<union> l_wvars_of_cmd c"
  definition "gvars_of_cmd c \<equiv> g_rvars_of_cmd c \<union> g_wvars_of_cmd c"

  fun read_globals :: "action \<Rightarrow> ident set" where
    "read_globals (AAssign c _ e) = gvars_of_exp c \<union> udvars_of_exp c \<union>
      gvars_of_exp e \<union> udvars_of_exp e"
  | "read_globals (AAssign_local c _ e) = gvars_of_exp c \<union> udvars_of_exp c \<union>
      gvars_of_exp e \<union> udvars_of_exp e"
  | "read_globals (AAssign_global c _ e) = gvars_of_exp c \<union> udvars_of_exp c \<union>
      gvars_of_exp e \<union> udvars_of_exp e"
  | "read_globals (ATest e) = gvars_of_exp e \<union> udvars_of_exp e"
  | "read_globals (ASkip) = {}"

  fun write_globals :: "action \<Rightarrow> ident set" where
    "write_globals (AAssign _ x _) = {x}"
  | "write_globals (AAssign_local _ _ _) = {}"
  | "write_globals (AAssign_global _ x _) = {x}"
  | "write_globals (ATest e) = {}"
  | "write_globals (ASkip) = {}"

  abbreviation "rw_globals a \<equiv> read_globals a \<union> write_globals a"

  definition eq_on :: "ident set \<Rightarrow> valuation \<Rightarrow> valuation \<Rightarrow> bool"
    where "eq_on X s1 s2 \<equiv> \<forall>x\<in>X. s1 x = s2 x"

  lemma eq_onD: "\<lbrakk>eq_on X s1 s2; x\<in>X\<rbrakk> \<Longrightarrow> s1 x = s2 x"
    unfolding eq_on_def by auto  
    
  lemma 
    eq_on_refl[simp]: "eq_on X s s" and
    eq_on_sym: "eq_on X s1 s2 \<Longrightarrow> eq_on X s2 s1" and
    eq_on_sym_eq: "eq_on X s1 s2 \<longleftrightarrow> eq_on X s2 s1" and
    eq_on_trans[trans]: "\<lbrakk>eq_on Xa s1 s2; eq_on Xb s2 s3\<rbrakk> 
      \<Longrightarrow> eq_on (Xa\<inter>Xb) s1 s3" and
    eq_on_UNIV_eq[simp]: "eq_on UNIV s1 s2 \<longleftrightarrow> s1=s2"  
    unfolding eq_on_def by auto

  lemma eq_on_join: "\<lbrakk>eq_on X s s'; eq_on Y s s'\<rbrakk> \<Longrightarrow> eq_on (X\<union>Y) s s'"
    unfolding eq_on_def by auto

  abbreviation ls_eq_on :: "ident set \<Rightarrow> local_state \<Rightarrow> local_state \<Rightarrow> bool"
    where "ls_eq_on X ls1 ls2 \<equiv> 
      eq_on X (local_state.variables ls1) (local_state.variables ls2)"  

  abbreviation gs_eq_on :: "ident set \<Rightarrow> global_state \<Rightarrow> global_state \<Rightarrow> bool"
    where "gs_eq_on X ls1 ls2 \<equiv> 
      eq_on X (global_state.variables ls1) (global_state.variables ls2)"  

  lemma eval_dep_vars:
    assumes "gs_eq_on X gs gs'"    
    assumes "udvars_of_exp e \<subseteq> X" "gvars_of_exp e \<subseteq> X"
    shows "eval_exp e (ls,gs) = eval_exp e (ls,gs')"
    using assms
    apply (induction e)
    apply (auto split: option.splits simp: eq_on_def)
    done    

  lemma en_dep_read:
    assumes "gs_eq_on X gs gs'"
    assumes "read_globals a \<subseteq> X"
    shows "la_en' (ls,gs) a = la_en' (ls,gs') a"
    using assms
    apply (cases a)
    apply (auto 
      simp: la_en'_def eval_dep_vars 
      split: Option.bind_splits)
    done

  lemma ex_mod_limit: 
    assumes "la_ex' (ls,gs) a = (ls',gs')"
    shows "gs_eq_on (-write_globals a) gs gs'"
    using assms
    apply (cases a)
    apply (auto 
      simp: la_ex'_def eval_dep_vars eq_on_def 
      split: option.splits Option.bind_splits if_split_asm)
    done    

  lemma ex_dep_pres:
    assumes "gs_eq_on X gs1 gs2"
    assumes "read_globals a \<subseteq> X"
    assumes "la_ex' (ls,gs1) a = (ls1',gs1')"
    assumes "la_ex' (ls,gs2) a = (ls2',gs2')"
    shows "ls1'=ls2' \<and> gs_eq_on X gs1' gs2'"
    using assms
    apply (cases a)
    apply (auto 
      simp: la_ex'_def eval_dep_vars eq_on_def
      split: Option.bind_splits option.splits bool.splits if_split_asm)
    done


  lemma ex_swap_global:
    assumes DJ:
      "write_globals a1 \<inter> read_globals a2 = {}"
      "write_globals a2 \<inter> read_globals a1 = {}"
      "write_globals a1 \<inter> write_globals a2 = {}"
    assumes EXA: 
      "la_ex' (ls1,gs) a1 = (ls1a, gsa)"
      "la_ex' (ls2, gsa) a2 = (ls2a, gsa')"
    assumes EXB:
      "la_ex' (ls2,gs) a2 = (ls2b, gsb)"
      "la_ex' (ls1, gsb) a1 = (ls1b, gsb')"
    shows "ls1a=ls1b" "ls2a=ls2b" "gsa'=gsb'"
  proof -
    from ex_dep_pres[OF ex_mod_limit[OF EXB(1)] _ EXA(1) EXB(2)] DJ
    have "ls1a = ls1b" and E1: "gs_eq_on (- write_globals a2) gsa gsb'"
      by auto
    thus [simp]: "ls1a=ls1b" by simp
      
    from 
      ex_dep_pres[OF 
        ex_mod_limit[OF EXA(1), THEN eq_on_sym] _ EXA(2) EXB(1)
      ] DJ
    have "ls2a = ls2b" and E2: "gs_eq_on (- write_globals a1) gsa' gsb"
      by auto
    thus [simp]: "ls2a=ls2b" by simp

    from DJ have [simp]: "- write_globals a1 \<union> - write_globals a2 = UNIV" 
      by auto

    from eq_on_trans[OF E2 ex_mod_limit[OF EXB(2)]]
    have "gs_eq_on (- write_globals a1) gsa' gsb'" by simp
    also from eq_on_trans[OF ex_mod_limit[OF EXA(2), THEN eq_on_sym] E1]
    have "gs_eq_on (- write_globals a2) gsa' gsb'" by simp
    finally (eq_on_join) have "gs_eq_on UNIV gsa' gsb'" by simp
    thus "gsa' = gsb'" 
      apply (cases gsa', cases gsb')
      apply simp
      done
  qed

  lemma ex_pres_en:
    assumes EX: "la_ex' (ls1,gs) a1 = (ls1',gs')"
    assumes DJ: "write_globals a1 \<inter> read_globals a2 = {}"
    shows "la_en' (ls2,gs') a2 = la_en' (ls2,gs) a2"
    using en_dep_read[OF ex_mod_limit[OF EX], of a2] DJ by auto



end

