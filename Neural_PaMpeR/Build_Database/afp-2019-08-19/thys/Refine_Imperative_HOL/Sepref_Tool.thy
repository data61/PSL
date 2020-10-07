section \<open>Sepref Tool\<close>
theory Sepref_Tool
imports Sepref_Translate Sepref_Definition Sepref_Combinator_Setup Sepref_Intf_Util
begin

text \<open>In this theory, we set up the sepref tool.\<close>

subsection \<open>Sepref Method\<close>


lemma CONS_init: 
  assumes "hn_refine \<Gamma> c \<Gamma>' R a"
  assumes "\<Gamma>' \<Longrightarrow>\<^sub>t \<Gamma>c'"
  assumes "\<And>a c. hn_ctxt R a c \<Longrightarrow>\<^sub>t hn_ctxt Rc a c"
  shows "hn_refine \<Gamma> c \<Gamma>c' Rc a"
  apply (rule hn_refine_cons)
  apply (rule entt_refl)
  apply (rule assms[unfolded hn_ctxt_def])+
  done

lemma ID_init: "\<lbrakk>ID a a' TYPE('T); hn_refine \<Gamma> c \<Gamma>' R a'\<rbrakk> 
  \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a" by simp

lemma TRANS_init: "\<lbrakk> hn_refine \<Gamma> c \<Gamma>' R a; CNV c c' \<rbrakk> 
  \<Longrightarrow> hn_refine \<Gamma> c' \<Gamma>' R a"
  by simp

lemma infer_post_triv: "P \<Longrightarrow>\<^sub>t P" by (rule entt_refl)

ML \<open>
  structure Sepref = struct
    structure sepref_preproc_simps = Named_Thms (
      val name = @{binding sepref_preproc}
      val description = "Sepref: Preprocessor simplifications"
    )

    structure sepref_opt_simps = Named_Thms (
      val name = @{binding sepref_opt_simps}
      val description = "Sepref: Post-Translation optimizations, phase 1"
    )

    structure sepref_opt_simps2 = Named_Thms (
      val name = @{binding sepref_opt_simps2}
      val description = "Sepref: Post-Translation optimizations, phase 2"
    )

    fun cons_init_tac ctxt = Sepref_Frame.weaken_post_tac ctxt THEN' resolve_tac ctxt @{thms CONS_init}
    fun cons_solve_tac dbg ctxt = let
      val dbgSOLVED' = if dbg then I else SOLVED'
    in
      dbgSOLVED' (
        resolve_tac ctxt @{thms infer_post_triv}
        ORELSE' Sepref_Translate.side_frame_tac ctxt
      )
    end

    fun preproc_tac ctxt = let
      val ctxt = put_simpset HOL_basic_ss ctxt
      val ctxt = ctxt addsimps (sepref_preproc_simps.get ctxt)  
    in
      Sepref_Rules.prepare_hfref_synth_tac ctxt THEN'
      Simplifier.simp_tac ctxt
    end

    fun id_tac ctxt = 
      resolve_tac ctxt @{thms ID_init} 
      THEN' CONVERSION Thm.eta_conversion
      THEN' DETERM o Id_Op.id_tac Id_Op.Normal ctxt

    fun id_init_tac ctxt = 
      resolve_tac ctxt @{thms ID_init} 
      THEN' CONVERSION Thm.eta_conversion
      THEN' Id_Op.id_tac Id_Op.Init ctxt

    fun id_step_tac ctxt = 
      Id_Op.id_tac Id_Op.Step ctxt

    fun id_solve_tac ctxt = 
      Id_Op.id_tac Id_Op.Solve ctxt

    (*fun id_param_tac ctxt = CONVERSION (Refine_Util.HOL_concl_conv 
      (K (Sepref_Param.id_param_conv ctxt)) ctxt)*)

    fun monadify_tac ctxt = Sepref_Monadify.monadify_tac ctxt

    (*fun lin_ana_tac ctxt = Sepref_Lin_Ana.lin_ana_tac ctxt*)

    fun trans_tac ctxt = Sepref_Translate.trans_tac ctxt

    fun opt_tac ctxt = let 
      val opt1_ss = put_simpset HOL_basic_ss ctxt
        addsimps sepref_opt_simps.get ctxt
        addsimprocs [@{simproc "HOL.let_simp"}]
      |> Simplifier.add_cong @{thm SP_cong}
      |> Simplifier.add_cong @{thm PR_CONST_cong}

      val unsp_ss = put_simpset HOL_basic_ss ctxt addsimps @{thms SP_def}

      val opt2_ss = put_simpset HOL_basic_ss ctxt
        addsimps sepref_opt_simps2.get ctxt
        addsimprocs [@{simproc "HOL.let_simp"}]

    in 
      simp_tac opt1_ss THEN' simp_tac unsp_ss THEN'
      simp_tac opt2_ss THEN' simp_tac unsp_ss THEN'
      CONVERSION Thm.eta_conversion THEN'
      resolve_tac ctxt @{thms CNV_I}
    end

    fun sepref_tac dbg ctxt = 
      (K Sepref_Constraints.ensure_slot_tac) 
      THEN'
      Sepref_Basic.PHASES'
        [ 
          ("preproc",preproc_tac,0),
          ("cons_init",cons_init_tac,2),
          ("id",id_tac,0),
          ("monadify",monadify_tac false,0),
          ("opt_init",fn ctxt => resolve_tac ctxt @{thms TRANS_init},1),
          ("trans",trans_tac,~1),
          ("opt",opt_tac,~1),
          ("cons_solve1",cons_solve_tac false,~1),
          ("cons_solve2",cons_solve_tac false,~1),
          ("constraints",fn ctxt => K (Sepref_Constraints.solve_constraint_slot ctxt THEN Sepref_Constraints.remove_slot_tac),~1)
        ] (Sepref_Basic.flag_phases_ctrl dbg) ctxt
    
    val setup = I
      #> sepref_preproc_simps.setup 
      #> sepref_opt_simps.setup 
      #> sepref_opt_simps2.setup
  end
\<close>

setup Sepref.setup

method_setup sepref = \<open>Scan.succeed (fn ctxt =>
  SIMPLE_METHOD (DETERM (SOLVED' (IF_EXGOAL (
      Sepref.sepref_tac false ctxt  
    )) 1)))\<close>
  \<open>Automatic refinement to Imperative/HOL\<close>

method_setup sepref_dbg_keep = \<open>Scan.succeed (fn ctxt => let
    (*val ctxt = Config.put Id_Op.cfg_id_debug true ctxt*)
  in
    SIMPLE_METHOD (IF_EXGOAL (Sepref.sepref_tac true ctxt) 1)
  end)\<close>
  \<open>Automatic refinement to Imperative/HOL, debug mode\<close>

subsubsection \<open>Default Optimizer Setup\<close>
lemma return_bind_eq_let: "do { x\<leftarrow>return v; f x } = do { let x=v; f x }" by simp
lemmas [sepref_opt_simps] = return_bind_eq_let bind_return bind_bind id_def

text \<open>We allow the synthesized function to contain tagged function applications.
  This is important to avoid higher-order unification problems when synthesizing
  generic algorithms, for example the to-list algorithm for foreach-loops.\<close>
lemmas [sepref_opt_simps] = Autoref_Tagging.APP_def


text \<open>Revert case-pulling done by monadify\<close>
lemma case_prod_return_opt[sepref_opt_simps]:
  "case_prod (\<lambda>a b. return (f a b)) p = return (case_prod f p)"
  by (simp split: prod.split)

lemma case_option_return_opt[sepref_opt_simps]:
  "case_option (return fn) (\<lambda>s. return (fs s)) v = return (case_option fn fs v)"
  by (simp split: option.split)

lemma case_list_return[sepref_opt_simps]:
  "case_list (return fn) (\<lambda>x xs. return (fc x xs)) l = return (case_list fn fc l)"
  by (simp split: list.split)

lemma if_return[sepref_opt_simps]:
  "If b (return t) (return e) = return (If b t e)" by simp

text \<open>In some cases, pushing in the returns is more convenient\<close>
lemma case_prod_opt2[sepref_opt_simps2]:
  "(\<lambda>x. return (case x of (a,b) \<Rightarrow> f a b)) 
  = (\<lambda>(a,b). return (f a b))"
  by auto



subsection \<open>Debugging Methods\<close>
ML \<open>
  fun SIMPLE_METHOD_NOPARAM' tac = Scan.succeed (fn ctxt => SIMPLE_METHOD' (IF_EXGOAL (tac ctxt)))
  fun SIMPLE_METHOD_NOPARAM tac = Scan.succeed (fn ctxt => SIMPLE_METHOD (tac ctxt))
\<close>
method_setup sepref_dbg_preproc = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => K (Sepref_Constraints.ensure_slot_tac) THEN' Sepref.preproc_tac ctxt)\<close>
  \<open>Sepref debug: Preprocessing phase\<close>
(*method_setup sepref_dbg_id_param = \<open>SIMPLE_METHOD_NOPARAM' Sepref.id_param_tac\<close>
  \<open>Sepref debug: Identify parameters phase\<close>*)
method_setup sepref_dbg_cons_init = \<open>SIMPLE_METHOD_NOPARAM' Sepref.cons_init_tac\<close>
  \<open>Sepref debug: Initialize consequence reasoning\<close>
method_setup sepref_dbg_id = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.id_tac)\<close>
  \<open>Sepref debug: Identify operations phase\<close>
method_setup sepref_dbg_id_keep = \<open>SIMPLE_METHOD_NOPARAM' (Config.put Id_Op.cfg_id_debug true #> Sepref.id_tac)\<close>
  \<open>Sepref debug: Identify operations phase. Debug mode, keep intermediate subgoals on failure.\<close>
method_setup sepref_dbg_monadify = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.monadify_tac false)\<close>
  \<open>Sepref debug: Monadify phase\<close>
method_setup sepref_dbg_monadify_keep = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.monadify_tac true)\<close>
  \<open>Sepref debug: Monadify phase\<close>

method_setup sepref_dbg_monadify_arity = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Monadify.arity_tac)\<close>
  \<open>Sepref debug: Monadify phase: Arity phase\<close>
method_setup sepref_dbg_monadify_comb = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Monadify.comb_tac)\<close>
  \<open>Sepref debug: Monadify phase: Comb phase\<close>
method_setup sepref_dbg_monadify_check_EVAL = \<open>SIMPLE_METHOD_NOPARAM' (K (CONCL_COND' (not o Sepref_Monadify.contains_eval)))\<close>
  \<open>Sepref debug: Monadify phase: check_EVAL phase\<close>
method_setup sepref_dbg_monadify_mark_params = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Monadify.mark_params_tac)\<close>
  \<open>Sepref debug: Monadify phase: mark_params phase\<close>
method_setup sepref_dbg_monadify_dup = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Monadify.dup_tac)\<close>
  \<open>Sepref debug: Monadify phase: dup phase\<close>
method_setup sepref_dbg_monadify_remove_pass = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Monadify.remove_pass_tac)\<close>
  \<open>Sepref debug: Monadify phase: remove_pass phase\<close>

(*method_setup sepref_dbg_lin_ana = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.lin_ana_tac true)\<close>
  \<open>Sepref debug: Linearity analysis phase\<close>*)
method_setup sepref_dbg_opt_init = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => resolve_tac ctxt @{thms TRANS_init})\<close>
  \<open>Sepref debug: Translation phase initialization\<close>
method_setup sepref_dbg_trans = \<open>SIMPLE_METHOD_NOPARAM' Sepref.trans_tac\<close>
  \<open>Sepref debug: Translation phase\<close>
method_setup sepref_dbg_opt = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => 
  Sepref.opt_tac ctxt
  THEN' CONVERSION Thm.eta_conversion
  THEN' TRY o resolve_tac ctxt @{thms CNV_I}
)\<close>
  \<open>Sepref debug: Optimization phase\<close>
method_setup sepref_dbg_cons_solve = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.cons_solve_tac false)\<close>
  \<open>Sepref debug: Solve post-consequences\<close>
method_setup sepref_dbg_cons_solve_keep = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.cons_solve_tac true)\<close>
  \<open>Sepref debug: Solve post-consequences, keep intermediate results\<close>

method_setup sepref_dbg_constraints = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => IF_EXGOAL (K (
    Sepref_Constraints.solve_constraint_slot ctxt
    THEN Sepref_Constraints.remove_slot_tac
  )))\<close>
  \<open>Sepref debug: Solve accumulated constraints\<close>

(*
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints

*)

method_setup sepref_dbg_id_init = \<open>SIMPLE_METHOD_NOPARAM' Sepref.id_init_tac\<close>
  \<open>Sepref debug: Initialize operation identification phase\<close>
method_setup sepref_dbg_id_step = \<open>SIMPLE_METHOD_NOPARAM' Sepref.id_step_tac\<close>
  \<open>Sepref debug: Single step operation identification phase\<close>
method_setup sepref_dbg_id_solve = \<open>SIMPLE_METHOD_NOPARAM' Sepref.id_solve_tac\<close>
  \<open>Sepref debug: Complete current operation identification goal\<close>

method_setup sepref_dbg_trans_keep = \<open>SIMPLE_METHOD_NOPARAM' Sepref_Translate.trans_keep_tac\<close>
  \<open>Sepref debug: Translation phase, stop at failed subgoal\<close>

method_setup sepref_dbg_trans_step = \<open>SIMPLE_METHOD_NOPARAM' Sepref_Translate.trans_step_tac\<close>
  \<open>Sepref debug: Translation step\<close>

method_setup sepref_dbg_trans_step_keep = \<open>SIMPLE_METHOD_NOPARAM' Sepref_Translate.trans_step_keep_tac\<close>
  \<open>Sepref debug: Translation step, keep unsolved subgoals\<close>

method_setup sepref_dbg_side = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => REPEAT_ALL_NEW_FWD (Sepref_Translate.side_cond_dispatch_tac false (K no_tac) ctxt))\<close>
method_setup sepref_dbg_side_unfold = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Translate.side_unfold_tac)\<close>
method_setup sepref_dbg_side_keep = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => REPEAT_ALL_NEW_FWD (Sepref_Translate.side_cond_dispatch_tac true (K no_tac) ctxt))\<close>

method_setup sepref_dbg_prepare_frame = \<open>SIMPLE_METHOD_NOPARAM' Sepref_Frame.prepare_frame_tac\<close>
  \<open>Sepref debug: Prepare frame inference\<close>

method_setup sepref_dbg_frame = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Frame.frame_tac (Sepref_Translate.side_fallback_tac))\<close>
  \<open>Sepref debug: Frame inference\<close>

method_setup sepref_dbg_merge = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Frame.merge_tac (Sepref_Translate.side_fallback_tac))\<close>
  \<open>Sepref debug: Frame inference, merge\<close>

method_setup sepref_dbg_frame_step = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Frame.frame_step_tac (Sepref_Translate.side_fallback_tac) false)\<close>
  \<open>Sepref debug: Frame inference, single-step\<close>

method_setup sepref_dbg_frame_step_keep = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Frame.frame_step_tac (Sepref_Translate.side_fallback_tac) true)\<close>
  \<open>Sepref debug: Frame inference, single-step, keep partially solved side conditions\<close>


subsection \<open>Utilities\<close>

subsubsection \<open>Manual hfref-proofs\<close>
method_setup sepref_to_hnr = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => 
  Sepref.preproc_tac ctxt THEN' Sepref_Frame.weaken_post_tac ctxt)\<close>
  \<open>Sepref: Convert to hnr-goal and weaken postcondition\<close>

method_setup sepref_to_hoare = \<open>
  let
    fun sepref_to_hoare_tac ctxt = let
      val ss = put_simpset HOL_basic_ss ctxt
        addsimps @{thms hn_ctxt_def pure_def}

    in
      Sepref.preproc_tac ctxt 
      THEN' Sepref_Frame.weaken_post_tac ctxt 
      THEN' resolve_tac ctxt @{thms hn_refineI}
      THEN' asm_full_simp_tac ss
    end  
  in
    SIMPLE_METHOD_NOPARAM' sepref_to_hoare_tac
  end
\<close> \<open>Sepref: Convert to hoare-triple\<close>



subsubsection \<open>Copying of Parameters\<close>
lemma fold_COPY: "x = COPY x" by simp

sepref_register COPY

text \<open>Copy is treated as normal operator, and one can just declare rules for it! \<close>
lemma hnr_pure_COPY[sepref_fr_rules]:
  "CONSTRAINT is_pure R \<Longrightarrow> (return, RETURN o COPY) \<in> R\<^sup>k \<rightarrow>\<^sub>a R"
  by (sep_auto simp: is_pure_conv pure_def intro!: hfrefI hn_refineI)


subsubsection \<open>Short-Circuit Boolean Evaluation\<close>
text \<open>Convert boolean operators to short-circuiting. 
  When applied before monadify, this will generate a short-circuit execution.\<close>
lemma short_circuit_conv:  
  "(a \<and> b) \<longleftrightarrow> (if a then b else False)"
  "(a \<or> b) \<longleftrightarrow> (if a then True else b)"
  "(a\<longrightarrow>b) \<longleftrightarrow> (if a then b else True)"
  by auto

subsubsection \<open>Eliminating higher-order\<close>
  (* TODO: Add similar rules for other cases! *)
  lemma ho_prod_move[sepref_preproc]: "case_prod (\<lambda>a b x. f x a b) = (\<lambda>p x. case_prod (f x) p)"
    by (auto intro!: ext)

  declare o_apply[sepref_preproc]




subsubsection \<open>Precision Proofs\<close>
  text \<open>
    We provide a method that tries to extract equalities from
    an assumption of the form 
    \<open>_ \<Turnstile> P1 * \<dots> * Pn \<and>\<^sub>A P1' * \<dots> * Pn'\<close>,
    if it find a precision rule for Pi and Pi'.
    The precision rules are extracted from the constraint rules.

    TODO: Extracting the precision rules from the constraint rules
      is not a clean solution. It might be better to collect precision rules
      separately, and feed them into the constraint solver.
    \<close>

  definition "prec_spec h \<Gamma> \<Gamma>' \<equiv> h \<Turnstile> \<Gamma> * true \<and>\<^sub>A \<Gamma>' * true"
  lemma prec_specI: "h \<Turnstile> \<Gamma> \<and>\<^sub>A \<Gamma>' \<Longrightarrow> prec_spec h \<Gamma> \<Gamma>'"
    unfolding prec_spec_def 
    by (auto simp: mod_and_dist mod_star_trueI)

  lemma prec_split1_aux: "A*B*true \<Longrightarrow>\<^sub>A A*true"
    apply (fr_rot 2, fr_rot_rhs 1)
    apply (rule ent_star_mono)
    by simp_all

  lemma prec_split2_aux: "A*B*true \<Longrightarrow>\<^sub>A B*true"
    apply (fr_rot 1, fr_rot_rhs 1)
    apply (rule ent_star_mono)
    by simp_all

  lemma prec_spec_splitE: 
    assumes "prec_spec h (A*B) (C*D)"  
    obtains "prec_spec h A C" "prec_spec h B D"
    apply (thin_tac "\<lbrakk>_;_\<rbrakk> \<Longrightarrow> _")
    apply (rule that)
    using assms
    apply -
    unfolding prec_spec_def
    apply (erule entailsD[rotated])
    apply (rule ent_conjI)
    apply (rule ent_conjE1)
    apply (rule prec_split1_aux)
    apply (rule ent_conjE2)
    apply (rule prec_split1_aux)

    apply (erule entailsD[rotated])
    apply (rule ent_conjI)
    apply (rule ent_conjE1)
    apply (rule prec_split2_aux)
    apply (rule ent_conjE2)
    apply (rule prec_split2_aux)
    done

  lemma prec_specD:
    assumes "precise R"
    assumes "prec_spec h (R a p) (R a' p)"
    shows "a=a'"
    using assms unfolding precise_def prec_spec_def CONSTRAINT_def by blast
  
  ML \<open>
    fun prec_extract_eqs_tac ctxt = let
      fun is_precise thm = case Thm.concl_of thm of
        @{mpat "Trueprop (precise _)"} => true
      | _ => false  
  
      val thms = Sepref_Constraints.get_constraint_rules ctxt
        @ Sepref_Constraints.get_safe_constraint_rules ctxt
      val thms = thms  
        |> filter is_precise 
      val thms = @{thms snga_prec sngr_prec} @ thms
      val thms = map (fn thm => thm RS @{thm prec_specD}) thms
  
      val thin_prec_spec_rls = @{thms thin_rl[Pure.of "prec_spec a b c" for a b c]}
  
      val tac = 
        forward_tac ctxt @{thms prec_specI}
        THEN' REPEAT_ALL_NEW (ematch_tac ctxt @{thms prec_spec_splitE})
        THEN' REPEAT o (dresolve_tac ctxt thms)
        THEN' REPEAT o (eresolve_tac ctxt thin_prec_spec_rls )
    in tac end    
\<close>  

  method_setup prec_extract_eqs = \<open>SIMPLE_METHOD_NOPARAM' prec_extract_eqs_tac\<close>
    \<open>Extract equalities from "_ |= _ & _" assumption, using precision rules\<close>


  subsubsection \<open>Combinator Rules\<close>  
  
  lemma split_merge: "\<lbrakk>A \<or>\<^sub>A B \<Longrightarrow>\<^sub>t X; X \<or>\<^sub>A C \<Longrightarrow>\<^sub>t D\<rbrakk> \<Longrightarrow> (A \<or>\<^sub>A B \<or>\<^sub>A C \<Longrightarrow>\<^sub>t D)"
  proof -
    assume a1: "X \<or>\<^sub>A C \<Longrightarrow>\<^sub>t D"
    assume "A \<or>\<^sub>A B \<Longrightarrow>\<^sub>t X"
    then have "A \<or>\<^sub>A B \<Longrightarrow>\<^sub>A D * true"
      using a1 by (meson ent_disjI1_direct ent_frame_fwd enttD entt_def_true)
    then show ?thesis
      using a1 by (metis (no_types) Assertions.ent_disjI2 ent_disjE enttD enttI semigroup.assoc sup.semigroup_axioms)
  qed
    
    
  ML \<open>
    fun prep_comb_rule thm = let
      fun mrg t = case Logic.strip_assums_concl t of
        @{mpat "Trueprop (_ \<or>\<^sub>A _ \<or>\<^sub>A _ \<Longrightarrow>\<^sub>t _)"} => (@{thm split_merge},true)
      | @{mpat "Trueprop (hn_refine _ _ ?G _ _)"} => (
          if not (is_Var (head_of G)) then (@{thm hn_refine_cons_post}, true)
          else (asm_rl,false)
        )
      | _ => (asm_rl,false)
      
      val inst = Thm.prems_of thm |> map mrg
    in
      if exists snd inst then
        prep_comb_rule (thm OF (map fst inst))
      else
        thm |> zero_var_indexes
    end
  \<close>  

  attribute_setup sepref_prep_comb_rule = \<open>Scan.succeed (Thm.rule_attribute [] (K prep_comb_rule))\<close>
    \<open>Preprocess combinator rule: Split merge-rules and add missing frame rules\<close>

end

