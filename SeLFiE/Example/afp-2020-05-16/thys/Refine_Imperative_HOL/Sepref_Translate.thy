section \<open>Translation\<close>
theory Sepref_Translate
imports 
  Sepref_Monadify 
  Sepref_Constraints 
  Sepref_Frame 
  "Lib/Pf_Mono_Prover"
  Sepref_Rules 
  Sepref_Combinator_Setup
  "Lib/User_Smashing"
begin


text \<open>
  This theory defines the translation phase.
  
  The main functionality of the translation phase is to
  apply refinement rules. Thereby, the linearity information is
  exploited to create copies of parameters that are still required, but
  would be destroyed by a synthesized operation.
  These \emph{frame-based} rules are in the named theorem collection
  \<open>sepref_fr_rules\<close>, and the collection \<open>sepref_copy_rules\<close>
  contains rules to handle copying of parameters.

  Apart from the frame-based rules described above, there is also a set of
  rules for combinators, in the collection \<open>sepref_comb_rules\<close>, 
  where no automatic copying of parameters is applied.

  Moreover, this theory contains 
  \begin{itemize}
    \item A setup for the  basic monad combinators and recursion.
    \item A tool to import parametricity theorems.
    \item Some setup to identify pure refinement relations, i.e., those not
      involving the heap.
    \item A preprocessor that identifies parameters in refinement goals,
      and flags them with a special tag, that allows their correct handling.
  \end{itemize}
\<close>

(*subsection \<open>Basic Translation Tool\<close>  
definition COPY -- "Copy operation"
   where [simp]: "COPY \<equiv> RETURN" 

lemma tagged_nres_monad1: "Refine_Basic.bind$(RETURN$x)$(\<lambda>\<^sub>2x. f x) = f x" by simp

text \<open>The PREPARED-tag is used internally, to flag a refinement goal
  with the index of the refinement rule to be used\<close>
definition PREPARED_TAG :: "'a => nat => 'a"
  where [simp]: "PREPARED_TAG x i == x"
lemma PREPARED_TAG_I: 
  "hn_refine \<Gamma> c \<Gamma>' R a \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R (PREPARED_TAG a i)"
  by simp

lemmas prepare_refine_simps = tagged_nres_monad1 COPY_def 
  PREPARED_TAG_def

lemma mono_trigger: "mono_Heap F \<Longrightarrow> mono_Heap F" .
*)

text \<open>Tag to keep track of abstract bindings. 
  Required to recover information for side-condition solving.\<close>
definition "bind_ref_tag x m \<equiv> RETURN x \<le> m"

(*
abbreviation DEP_SIDE_PRECOND
  -- \<open>Precondition that depends on information from relators, 
    like maximum size. It must be processed after frame inference,
    when the relator variables have been fixed.\<close>
  where "DEP_SIDE_PRECOND \<Phi> \<equiv> DEFER_tag (PRECOND_tag \<Phi>)"

lemma DEP_SIDE_PRECOND_D: "DEP_SIDE_PRECOND P \<Longrightarrow> P"
  by simp
*)

text \<open>Tag to keep track of preconditions in assertions\<close>
definition "vassn_tag \<Gamma> \<equiv> \<exists>h. h\<Turnstile>\<Gamma>"

lemma vassn_tagI: "h\<Turnstile>\<Gamma> \<Longrightarrow> vassn_tag \<Gamma>" 
  unfolding vassn_tag_def ..

lemma vassn_dest[dest!]:
  "vassn_tag (\<Gamma>\<^sub>1 * \<Gamma>\<^sub>2) \<Longrightarrow> vassn_tag \<Gamma>\<^sub>1 \<and> vassn_tag \<Gamma>\<^sub>2"
  "vassn_tag (hn_ctxt R a b) \<Longrightarrow> a\<in>rdom R"
  unfolding vassn_tag_def rdomp_def[abs_def]
  by (auto simp: mod_star_conv hn_ctxt_def)

lemma entails_preI:
  assumes "vassn_tag A \<Longrightarrow> A \<Longrightarrow>\<^sub>A B"
  shows "A \<Longrightarrow>\<^sub>A B"
  using assms
  by (auto simp: entails_def vassn_tag_def)

lemma invalid_assn_const: 
  "invalid_assn (\<lambda>_ _. P) x y = \<up>(vassn_tag P) * true"
  by (simp_all add: invalid_assn_def vassn_tag_def)

lemma vassn_tag_simps[simp]: 
  "vassn_tag emp"
  "vassn_tag true"
  by (sep_auto simp: vassn_tag_def mod_emp)+

definition "GEN_ALGO f \<Phi> \<equiv> \<Phi> f"
\<comment> \<open>Tag to synthesize @{term f} with property @{term \<Phi>}.\<close>

lemma is_GEN_ALGO: "GEN_ALGO f \<Phi> \<Longrightarrow> GEN_ALGO f \<Phi>" .


text \<open>Tag for side-condition solver to discharge by assumption\<close>
definition RPREM :: "bool \<Rightarrow> bool" where [simp]: "RPREM P = P"
lemma RPREMI: "P \<Longrightarrow> RPREM P" by simp

lemma trans_frame_rule:
  assumes "RECOVER_PURE \<Gamma> \<Gamma>'"
  assumes "vassn_tag \<Gamma>' \<Longrightarrow> hn_refine \<Gamma>' c \<Gamma>'' R a"
  shows "hn_refine (F*\<Gamma>) c (F*\<Gamma>'') R a"
  apply (rule hn_refine_frame[OF _ entt_refl])
  applyF (rule hn_refine_cons_pre)
    focus using assms(1) unfolding RECOVER_PURE_def apply assumption solved
    
    apply1 (rule hn_refine_preI)
    apply1 (rule assms)
    applyS (auto simp add: vassn_tag_def)
  solved
  done

lemma recover_pure_cons: \<comment> \<open>Used for debugging\<close>
  assumes "RECOVER_PURE \<Gamma> \<Gamma>'"
  assumes "hn_refine \<Gamma>' c \<Gamma>'' R a"
  shows "hn_refine (\<Gamma>) c (\<Gamma>'') R a"
  using trans_frame_rule[where F=emp, OF assms] by simp


\<comment> \<open>Tag to align structure of refinement assertions for consequence rule\<close>
definition CPR_TAG :: "assn \<Rightarrow> assn \<Rightarrow> bool" where [simp]: "CPR_TAG y x \<equiv> True"
lemma CPR_TAG_starI:
  assumes "CPR_TAG P1 Q1"
  assumes "CPR_TAG P2 Q2"
  shows "CPR_TAG (P1*P2) (Q1*Q2)"
  by simp
lemma CPR_tag_ctxtI: "CPR_TAG (hn_ctxt R x xi) (hn_ctxt R' x xi)" by simp
lemma CPR_tag_fallbackI: "CPR_TAG P Q" by simp

lemmas CPR_TAG_rules = CPR_TAG_starI CPR_tag_ctxtI CPR_tag_fallbackI

lemma cons_pre_rule: \<comment> \<open>Consequence rule to be applied if no direct operation rule matches\<close>
  assumes "CPR_TAG P P'"
  assumes "P \<Longrightarrow>\<^sub>t P'"
  assumes "hn_refine P' c Q R m"
  shows "hn_refine P c Q R m"
  using assms(2-) by (rule hn_refine_cons_pre)

named_theorems_rev sepref_gen_algo_rules \<open>Sepref: Generic algorithm rules\<close>


ML \<open>

structure Sepref_Translate = struct

  val cfg_debug = 
    Attrib.setup_config_bool @{binding sepref_debug_translate} (K false)
  
  val dbg_msg_tac = Sepref_Debugging.dbg_msg_tac cfg_debug  

  fun gen_msg_analyze t ctxt = let
    val t = Logic.strip_assums_concl t
  in
    case t of
      @{mpat "Trueprop ?t"} => (case t of
            @{mpat "_ \<or>\<^sub>A _ \<Longrightarrow>\<^sub>t _"} => "t_merge"
          | @{mpat "_ \<Longrightarrow>\<^sub>t _"} => "t_frame"
          | @{mpat "INDEP _"} => "t_indep"
          | @{mpat "CONSTRAINT _ _"} => "t_constraint"
          | @{mpat "mono_Heap _"} => "t_mono"
          | @{mpat "PREFER_tag _"} => "t_prefer"
          | @{mpat "DEFER_tag _"} => "t_defer"
          | @{mpat "RPREM _"} => "t_rprem" 
          | @{mpat "hn_refine _ _ _ _ ?a"} => Pretty.block [Pretty.str "t_hnr: ",Pretty.brk 1, Syntax.pretty_term ctxt a] |> Pretty.string_of 
          | _ => "Unknown goal type"
        )
    | _ => "Non-Trueprop goal"
  end  

  fun msg_analyze msg = Sepref_Debugging.msg_from_subgoal msg gen_msg_analyze

  fun check_side_conds thm = let
    open Sepref_Basic
    (* Check that term is no binary operator on assertions *)
    fun is_atomic (Const (_,@{typ "assn\<Rightarrow>assn\<Rightarrow>assn"})$_$_) = false
      | is_atomic _ = true

    val is_atomic_star_list = ("Expected atoms separated by star",forall is_atomic o strip_star)

    val is_trueprop = ("Expected Trueprop conclusion",can HOLogic.dest_Trueprop)

    fun assert t' (msg,p) t = if p t then () else raise TERM(msg,[t',t])

    fun chk_prem t = let
      val assert = assert t
      
      fun chk @{mpat "?l \<or>\<^sub>A ?r \<Longrightarrow>\<^sub>t ?m"} = (
            assert is_atomic_star_list l;
            assert is_atomic_star_list r;
            assert is_atomic_star_list m
          )
        | chk (t as @{mpat "_ \<Longrightarrow>\<^sub>A _"}) = raise TERM("Invalid frame side condition (old-style ent)",[t])
        | chk @{mpat "?l \<Longrightarrow>\<^sub>t ?r"} = (
            assert is_atomic_star_list l;
            assert is_atomic_star_list r
          )
        | chk _ = ()  

      val t = Logic.strip_assums_concl t 
    in
      assert is_trueprop t;
      chk (HOLogic.dest_Trueprop t)
    end    

  in
    map chk_prem (Thm.prems_of thm)
  end

  structure sepref_comb_rules = Named_Sorted_Thms (
    val name = @{binding "sepref_comb_rules"}
    val description = "Sepref: Combinator rules"
    val sort = K I
    fun transform _ thm = let
      val _ = check_side_conds thm  
    in
      [thm]
    end
  )

  structure sepref_fr_rules = Named_Sorted_Thms (
    val name = @{binding "sepref_fr_rules"}
    val description = "Sepref: Frame-based rules"
    val sort = K I
    fun transform context thm = let
      val ctxt = Context.proof_of context
      val thm = Sepref_Rules.ensure_hnr ctxt thm
        |> Conv.fconv_rule (Sepref_Frame.align_rl_conv ctxt)

      val _ = check_side_conds thm  
      val _ = case try (Sepref_Rules.analyze_hnr ctxt) thm of 
          NONE =>
            (Pretty.block [
              Pretty.str "hnr-analysis failed", 
              Pretty.str ":", 
              Pretty.brk 1, 
              Thm.pretty_thm ctxt thm])
            |> Pretty.string_of |> error  
        | SOME ana => let
            val _ = Sepref_Combinator_Setup.is_valid_abs_op ctxt (fst (#ahead ana))
              orelse Pretty.block [
                Pretty.str "Invalid abstract head:",
                Pretty.brk 1,
                Pretty.enclose "(" ")" [Syntax.pretty_term ctxt (fst (#ahead ana))],
                Pretty.brk 1,
                Pretty.str "in thm",
                Pretty.brk 1,
                Thm.pretty_thm ctxt thm                
              ]
            |> Pretty.string_of |> error  
          in () end
    in
      [thm]
    end
  )

  (***** Side Condition Solving *)
  local
    open Sepref_Basic
  in
  
    fun side_unfold_tac ctxt = let
      (*val ctxt = put_simpset HOL_basic_ss ctxt
        addsimps sepref_prep_side_simps.get ctxt*)
    in
      CONVERSION (Id_Op.unprotect_conv ctxt)
      THEN' SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms bind_ref_tag_def})
      (*THEN' asm_full_simp_tac ctxt*)
    end
  
    fun side_fallback_tac ctxt = side_unfold_tac ctxt THEN' TRADE (SELECT_GOAL o auto_tac) ctxt
  
    val side_frame_tac = Sepref_Frame.frame_tac side_fallback_tac
    val side_merge_tac = Sepref_Frame.merge_tac side_fallback_tac
    fun side_constraint_tac ctxt = Sepref_Constraints.constraint_tac ctxt
    fun side_mono_tac ctxt = side_unfold_tac ctxt THEN' TRADE Pf_Mono_Prover.mono_tac ctxt
  
    fun side_gen_algo_tac ctxt = 
      side_unfold_tac ctxt
      THEN' resolve_tac ctxt (Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_gen_algo_rules})
  
    fun side_pref_def_tac ctxt = 
      side_unfold_tac ctxt THEN' 
      TRADE (fn ctxt => 
        resolve_tac ctxt @{thms PREFER_tagI DEFER_tagI} 
        THEN' (Sepref_Debugging.warning_tac' "Obsolete PREFER/DEFER side condition" ctxt THEN' Tagged_Solver.solve_tac ctxt)
      ) ctxt


    fun side_rprem_tac ctxt = 
      resolve_tac ctxt @{thms RPREMI} THEN' Refine_Util.rprems_tac ctxt
      THEN' (K (smash_new_rule ctxt))

    (*
      Solve side condition, or invoke hnr_tac on hn_refine goal.

      In debug mode, side-condition solvers are allowed to not completely solve 
      the side condition, but must change the goal.
    *)  
    fun side_cond_dispatch_tac dbg hnr_tac ctxt = let
      fun MK tac = if dbg then CHANGED o tac ctxt else SOLVED' (tac ctxt)

      val t_merge = MK side_merge_tac
      val t_frame = MK side_frame_tac
      val t_indep = MK Indep_Vars.indep_tac
      val t_constraint = MK side_constraint_tac
      val t_mono = MK side_mono_tac
      val t_pref_def = MK side_pref_def_tac
      val t_rprem = MK side_rprem_tac
      val t_gen_algo = side_gen_algo_tac ctxt
      val t_fallback = MK side_fallback_tac
    in
      WITH_concl 
        (fn @{mpat "Trueprop ?t"} => (case t of
              @{mpat "_ \<or>\<^sub>A _ \<Longrightarrow>\<^sub>t _"} => t_merge
            | @{mpat "_ \<Longrightarrow>\<^sub>t _"} => t_frame
            | @{mpat "_ \<Longrightarrow>\<^sub>A _"} => Sepref_Debugging.warning_tac' "Old-style frame side condition" ctxt THEN' (K no_tac)
            | @{mpat "INDEP _"} => t_indep     (* TODO: Get rid of this!? *)
            | @{mpat "CONSTRAINT _ _"} => t_constraint
            | @{mpat "mono_Heap _"} => t_mono
            | @{mpat "PREFER_tag _"} => t_pref_def
            | @{mpat "DEFER_tag _"} => t_pref_def
            | @{mpat "RPREM _"} => t_rprem
            | @{mpat "GEN_ALGO _ _"} => t_gen_algo
            | @{mpat "hn_refine _ _ _ _ _"} => hnr_tac 
            | _ => t_fallback
          )
        | _ => K no_tac  
      )
    end

  end  

  (***** Main Translation Tactic *)
  local
    open Sepref_Basic STactical

    (* ATTENTION: Beware of evaluation order, as some initialization operations on
      context are expensive, and should not be repeated during proof search! *)
  in


    (* Translate combinator, yields new translation goals and side conditions
      which must be processed in order. *)
    fun trans_comb_tac ctxt = let
      val comb_rl_net = sepref_comb_rules.get ctxt
        |> Tactic.build_net

    in
      DETERM o (
        resolve_from_net_tac ctxt comb_rl_net 
        ORELSE' ( 
          Sepref_Frame.norm_goal_pre_tac ctxt 
          THEN' resolve_from_net_tac ctxt comb_rl_net
        )
      )
    end

    (* Translate operator. Only succeeds if it finds an operator rule such that
      all resulting side conditions can be solved. Takes the first such rule.

      In debug mode, it returns a sequence of the unsolved side conditions of
      each applicable rule.
    *)
    fun gen_trans_op_tac dbg ctxt = let
      val fr_rl_net = sepref_fr_rules.get ctxt |> Tactic.build_net
      val fr_rl_tac = 
        resolve_from_net_tac ctxt fr_rl_net (* Try direct match *)
        ORELSE' (
          Sepref_Frame.norm_goal_pre_tac ctxt (* Normalize precondition *) 
          THEN' (
            resolve_from_net_tac ctxt fr_rl_net
            ORELSE' (
              resolve_tac ctxt @{thms cons_pre_rule} (* Finally, generate a frame condition *)
              THEN_ALL_NEW_LIST [
                SOLVED' (REPEAT_ALL_NEW_FWD (DETERM o resolve_tac ctxt @{thms CPR_TAG_rules})),
                K all_tac,  (* Frame remains unchanged as first goal, even if fr_rl creates side-conditions *)
                resolve_from_net_tac ctxt fr_rl_net
              ]
            )
          )  
        )
      
      val side_tac = REPEAT_ALL_NEW_FWD (side_cond_dispatch_tac false (K no_tac) ctxt)

      val fr_tac = 
        if dbg then (* Present all possibilities with (partially resolved) side conditions *)
          fr_rl_tac THEN_ALL_NEW_FWD (TRY o side_tac)
        else (* Choose first rule that solves all side conditions *)
          DETERM o SOLVED' (fr_rl_tac THEN_ALL_NEW_FWD (SOLVED' side_tac))

    in
      PHASES' [
        ("Align goal",Sepref_Frame.align_goal_tac, 0),
        ("Frame rule",fn ctxt => resolve_tac ctxt @{thms trans_frame_rule}, 1),
        (* RECOVER_PURE goal *)
        ("Recover pure",Sepref_Frame.recover_pure_tac, ~1),
        (* hn-refine goal with stripped precondition *)
        ("Apply rule",K fr_tac,~1)
      ] (flag_phases_ctrl dbg) ctxt
    end

    (* Translate combinator, operator, or side condition. *)
    fun gen_trans_step_tac dbg ctxt = side_cond_dispatch_tac dbg
      (trans_comb_tac ctxt ORELSE' gen_trans_op_tac dbg ctxt)
      ctxt

    val trans_step_tac = gen_trans_step_tac false  
    val trans_step_keep_tac = gen_trans_step_tac true

    fun gen_trans_tac dbg ctxt = 
      PHASES' [
        ("Translation steps",REPEAT_DETERM' o trans_step_tac,~1),
        ("Constraint solving",fn ctxt => fn _ => Sepref_Constraints.process_constraint_slot ctxt, 0)
      ] (flag_phases_ctrl dbg) ctxt

    val trans_tac = gen_trans_tac false  
    val trans_keep_tac = gen_trans_tac true


  end


  val setup = I
    #> sepref_fr_rules.setup
    #> sepref_comb_rules.setup


end

\<close>

setup Sepref_Translate.setup



subsubsection \<open>Basic Setup\<close>
              
lemma hn_pass[sepref_fr_rules]:
  shows "hn_refine (hn_ctxt P x x') (return x') (hn_invalid P x x') P (PASS$x)"
  apply rule apply (sep_auto simp: hn_ctxt_def invalidate_clone')
  done

(*lemma hn_pass_pure[sepref_fr_rules]:
  shows "hn_refine (hn_val P x x') (return x') (hn_val P x x') (pure P) (PASS$x)"
  by rule (sep_auto simp: hn_ctxt_def pure_def)
*)

lemma hn_bind[sepref_comb_rules]:
  assumes D1: "hn_refine \<Gamma> m' \<Gamma>1 Rh m"
  assumes D2: 
    "\<And>x x'. bind_ref_tag x m \<Longrightarrow> 
      hn_refine (\<Gamma>1 * hn_ctxt Rh x x') (f' x') (\<Gamma>2 x x') R (f x)"
  assumes IMP: "\<And>x x'. \<Gamma>2 x x' \<Longrightarrow>\<^sub>t \<Gamma>' * hn_ctxt Rx x x'"
  shows "hn_refine \<Gamma> (m'\<bind>f') \<Gamma>' R (Refine_Basic.bind$m$(\<lambda>\<^sub>2x. f x))"
  using assms
  unfolding APP_def PROTECT2_def bind_ref_tag_def
  by (rule hnr_bind)


lemma hn_RECT'[sepref_comb_rules]:
  assumes "INDEP Ry" "INDEP Rx" "INDEP Rx'"
  assumes FR: "P \<Longrightarrow>\<^sub>t hn_ctxt Rx ax px * F"
  assumes S: "\<And>cf af ax px. \<lbrakk>
    \<And>ax px. hn_refine (hn_ctxt Rx ax px * F) (cf px) (hn_ctxt Rx' ax px * F) Ry 
      (RCALL$af$ax)\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt Rx ax px * F) (cB cf px) (F' ax px) Ry 
          (aB af ax)"
  assumes FR': "\<And>ax px. F' ax px \<Longrightarrow>\<^sub>t hn_ctxt Rx' ax px * F"
  assumes M: "(\<And>x. mono_Heap (\<lambda>f. cB f x))"
  (*assumes PREC[unfolded CONSTRAINT_def]: "CONSTRAINT precise Ry"*)
  shows "hn_refine 
    (P) (heap.fixp_fun cB px) (hn_ctxt Rx' ax px * F) Ry 
        (RECT$(\<lambda>\<^sub>2D x. aB D x)$ax)"
  unfolding APP_def PROTECT2_def 
  apply (rule hn_refine_cons_pre[OF FR])
  apply (rule hnr_RECT)

  apply (rule hn_refine_cons_post[OF _ FR'])
  apply (rule S[unfolded RCALL_def APP_def])
  apply assumption
  apply fact+
  done

lemma hn_RCALL[sepref_comb_rules]:
  assumes "RPREM (hn_refine P' c Q' R (RCALL $ a $ b))"
    and "P \<Longrightarrow>\<^sub>t F * P'"
  shows "hn_refine P c (F * Q') R (RCALL $ a $ b)"
  using assms hn_refine_frame[where m="RCALL$a$b"] 
  by simp


definition "monadic_WHILEIT I b f s \<equiv> do {
  RECT (\<lambda>D s. do {
    ASSERT (I s);
    bv \<leftarrow> b s;
    if bv then do {
      s \<leftarrow> f s;
      D s
    } else do {RETURN s}
  }) s
}"

definition "heap_WHILET b f s \<equiv> do {
  heap.fixp_fun (\<lambda>D s. do {
    bv \<leftarrow> b s;
    if bv then do {
      s \<leftarrow> f s;
      D s
    } else do {return s}
  }) s
}"

lemma heap_WHILET_unfold[code]: "heap_WHILET b f s = 
  do {
    bv \<leftarrow> b s;
    if bv then do {
      s \<leftarrow> f s;
      heap_WHILET b f s
    } else
      return s
  }"
  unfolding heap_WHILET_def
  apply (subst heap.mono_body_fixp)
  apply pf_mono
  apply simp
  done



lemma WHILEIT_to_monadic: "WHILEIT I b f s = monadic_WHILEIT I (\<lambda>s. RETURN (b s)) f s"
  unfolding WHILEIT_def monadic_WHILEIT_def
  unfolding WHILEI_body_def bind_ASSERT_eq_if
  by (simp cong: if_cong)

lemma WHILEIT_pat[def_pat_rules]:
  "WHILEIT$I \<equiv> UNPROTECT (WHILEIT I)"
  "WHILET \<equiv> PR_CONST (WHILEIT (\<lambda>_. True))"
  by (simp_all add: WHILET_def)

lemma id_WHILEIT[id_rules]: 
  "PR_CONST (WHILEIT I) ::\<^sub>i TYPE(('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'a nres)"
  by simp

lemma WHILE_arities[sepref_monadify_arity]:
  (*"WHILET \<equiv> WHILEIT$(\<lambda>\<^sub>2_. True)"*)
  "PR_CONST (WHILEIT I) \<equiv> \<lambda>\<^sub>2b f s. SP (PR_CONST (WHILEIT I))$(\<lambda>\<^sub>2s. b$s)$(\<lambda>\<^sub>2s. f$s)$s"
  by (simp_all add: WHILET_def)

lemma WHILEIT_comb[sepref_monadify_comb]:
  "PR_CONST (WHILEIT I)$(\<lambda>\<^sub>2x. b x)$f$s \<equiv> 
    Refine_Basic.bind$(EVAL$s)$(\<lambda>\<^sub>2s. 
      SP (PR_CONST (monadic_WHILEIT I))$(\<lambda>\<^sub>2x. (EVAL$(b x)))$f$s
    )"
  by (simp_all add: WHILEIT_to_monadic)

lemma hn_monadic_WHILE_aux:
  assumes FR: "P \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt Rs s' s"
  assumes b_ref: "\<And>s s'. I s' \<Longrightarrow> hn_refine 
    (\<Gamma> * hn_ctxt Rs s' s)
    (b s)
    (\<Gamma>b s' s)
    (pure bool_rel)
    (b' s')"
  assumes b_fr: "\<And>s' s. \<Gamma>b s' s \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt Rs s' s"

  assumes f_ref: "\<And>s' s. \<lbrakk>I s'\<rbrakk> \<Longrightarrow> hn_refine
    (\<Gamma> * hn_ctxt Rs s' s)
    (f s)
    (\<Gamma>f s' s)
    Rs
    (f' s')"
  assumes f_fr: "\<And>s' s. \<Gamma>f s' s \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt (\<lambda>_ _. true) s' s"
  (*assumes PREC: "precise Rs"*)
  shows "hn_refine (P) (heap_WHILET b f s) (\<Gamma> * hn_invalid Rs s' s) Rs (monadic_WHILEIT I b' f' s')"
  unfolding monadic_WHILEIT_def heap_WHILET_def
  apply1 (rule hn_refine_cons_pre[OF FR])
  apply weaken_hnr_post
  focus (rule hn_refine_cons_pre[OF _ hnr_RECT])
    applyS (subst mult_ac(2)[of \<Gamma>]; rule entt_refl; fail)

    apply1 (rule hnr_ASSERT)
    focus (rule hnr_bind)
      focus (rule hn_refine_cons[OF _ b_ref b_fr entt_refl])
        applyS (simp add: star_aci)
        applyS assumption
      solved  

      focus (rule hnr_If)
        applyS (sep_auto; fail)
        focus (rule hnr_bind)
          focus (rule hn_refine_cons[OF _ f_ref f_fr entt_refl])
            apply (sep_auto simp: hn_ctxt_def pure_def intro!: enttI; fail)
            apply assumption
          solved
      
          focus (rule hn_refine_frame)
            applyS rprems
            applyS (rule enttI; solve_entails)
          solved
  
          apply (sep_auto intro!: enttI; fail)
        solved  
        applyF (sep_auto,rule hn_refine_frame)
          applyS (rule hnr_RETURN_pass)
          (*apply (tactic {* Sepref_Frame.frame_tac @{context} 1*})*)
          apply (rule enttI)
          apply (fr_rot_rhs 1)
          apply (fr_rot 1, rule fr_refl)
          apply (rule fr_refl)
          apply solve_entails
        solved

        apply (rule entt_refl)
      solved  

      apply (rule enttI)
      applyF (rule ent_disjE)
        apply1 (sep_auto simp: hn_ctxt_def pure_def)
        apply1 (rule ent_true_drop)
        apply1 (rule ent_true_drop)
        applyS (rule ent_refl)
        
        applyS (sep_auto simp: hn_ctxt_def pure_def)
      solved    
    solved
    apply pf_mono
  solved
  done

lemma hn_monadic_WHILE_lin[sepref_comb_rules]:
  assumes "INDEP Rs"
  assumes FR: "P \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt Rs s' s"
  assumes b_ref: "\<And>s s'. I s' \<Longrightarrow> hn_refine 
    (\<Gamma> * hn_ctxt Rs s' s)
    (b s)
    (\<Gamma>b s' s)
    (pure bool_rel)
    (b' s')"
  assumes b_fr: "\<And>s' s. TERM (monadic_WHILEIT,''cond'') \<Longrightarrow> \<Gamma>b s' s \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt Rs s' s"

  assumes f_ref: "\<And>s' s. I s' \<Longrightarrow> hn_refine
    (\<Gamma> * hn_ctxt Rs s' s)
    (f s)
    (\<Gamma>f s' s)
    Rs
    (f' s')"
  assumes f_fr: "\<And>s' s. TERM (monadic_WHILEIT,''body'') \<Longrightarrow> \<Gamma>f s' s \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt (\<lambda>_ _. true) s' s"
  shows "hn_refine 
    P 
    (heap_WHILET b f s) 
    (\<Gamma> * hn_invalid Rs s' s) 
    Rs 
    (PR_CONST (monadic_WHILEIT I)$(\<lambda>\<^sub>2s'. b' s')$(\<lambda>\<^sub>2s'. f' s')$(s'))"
  using assms(2-)
  unfolding APP_def PROTECT2_def CONSTRAINT_def PR_CONST_def
  by (rule hn_monadic_WHILE_aux)

lemma monadic_WHILEIT_refine[refine]:  
  assumes [refine]: "(s',s) \<in> R"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s \<rbrakk> \<Longrightarrow> I' s'"  
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s' \<rbrakk> \<Longrightarrow> b' s' \<le>\<Down>bool_rel (b s)"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s'; nofail (b s); inres (b s) True \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (f s)"
  shows "monadic_WHILEIT I' b' f' s' \<le>\<Down>R (monadic_WHILEIT I b f s)"
  unfolding monadic_WHILEIT_def
  by (refine_rcg bind_refine'; assumption?; auto)
  
lemma monadic_WHILEIT_refine_WHILEIT[refine]:  
  assumes [refine]: "(s',s) \<in> R"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s \<rbrakk> \<Longrightarrow> I' s'"  
  assumes [THEN order_trans,refine_vcg]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s' \<rbrakk> \<Longrightarrow> b' s' \<le> SPEC (\<lambda>r. r = b s)"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s'; b s \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (f s)"
  shows "monadic_WHILEIT I' b' f' s' \<le>\<Down>R (WHILEIT I b f s)"
  unfolding WHILEIT_to_monadic
  by (refine_vcg; assumption?; auto)
  
lemma monadic_WHILEIT_refine_WHILET[refine]:  
  assumes [refine]: "(s',s) \<in> R"
  assumes [THEN order_trans,refine_vcg]: "\<And>s' s. \<lbrakk> (s',s)\<in>R \<rbrakk> \<Longrightarrow> b' s' \<le> SPEC (\<lambda>r. r = b s)"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; b s \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (f s)"
  shows "monadic_WHILEIT (\<lambda>_. True) b' f' s' \<le>\<Down>R (WHILET b f s)"
  unfolding WHILET_def
  by (refine_vcg; assumption?)  

lemma monadic_WHILEIT_pat[def_pat_rules]:
  "monadic_WHILEIT$I \<equiv> UNPROTECT (monadic_WHILEIT I)"
  by auto  
    
lemma id_monadic_WHILEIT[id_rules]: 
  "PR_CONST (monadic_WHILEIT I) ::\<^sub>i TYPE(('a \<Rightarrow> bool nres) \<Rightarrow> ('a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'a nres)"
  by simp
    
lemma monadic_WHILEIT_arities[sepref_monadify_arity]:
  "PR_CONST (monadic_WHILEIT I) \<equiv> \<lambda>\<^sub>2b f s. SP (PR_CONST (monadic_WHILEIT I))$(\<lambda>\<^sub>2s. b$s)$(\<lambda>\<^sub>2s. f$s)$s"
  by (simp)

lemma monadic_WHILEIT_comb[sepref_monadify_comb]:
  "PR_CONST (monadic_WHILEIT I)$b$f$s \<equiv> 
    Refine_Basic.bind$(EVAL$s)$(\<lambda>\<^sub>2s. 
      SP (PR_CONST (monadic_WHILEIT I))$b$f$s
    )"
  by (simp)
    
    
definition [simp]: "op_ASSERT_bind I m \<equiv> Refine_Basic.bind (ASSERT I) (\<lambda>_. m)"
lemma pat_ASSERT_bind[def_pat_rules]:
  "Refine_Basic.bind$(ASSERT$I)$(\<lambda>\<^sub>2_. m) \<equiv> UNPROTECT (op_ASSERT_bind I)$m"
  by simp

term "PR_CONST (op_ASSERT_bind I)"
lemma id_op_ASSERT_bind[id_rules]: 
  "PR_CONST (op_ASSERT_bind I) ::\<^sub>i TYPE('a nres \<Rightarrow> 'a nres)"
  by simp

lemma arity_ASSERT_bind[sepref_monadify_arity]:
  "PR_CONST (op_ASSERT_bind I) \<equiv> \<lambda>\<^sub>2m. SP (PR_CONST (op_ASSERT_bind I))$m"
  apply (rule eq_reflection)
  by auto

lemma hn_ASSERT_bind[sepref_comb_rules]: 
  assumes "I \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R m"
  shows "hn_refine \<Gamma> c \<Gamma>' R (PR_CONST (op_ASSERT_bind I)$m)"
  using assms
  apply (cases I)
  apply auto
  done

definition [simp]: "op_ASSUME_bind I m \<equiv> Refine_Basic.bind (ASSUME I) (\<lambda>_. m)"
lemma pat_ASSUME_bind[def_pat_rules]:
  "Refine_Basic.bind$(ASSUME$I)$(\<lambda>\<^sub>2_. m) \<equiv> UNPROTECT (op_ASSUME_bind I)$m"
  by simp

lemma id_op_ASSUME_bind[id_rules]: 
  "PR_CONST (op_ASSUME_bind I) ::\<^sub>i TYPE('a nres \<Rightarrow> 'a nres)"
  by simp

lemma arity_ASSUME_bind[sepref_monadify_arity]:
  "PR_CONST (op_ASSUME_bind I) \<equiv> \<lambda>\<^sub>2m. SP (PR_CONST (op_ASSUME_bind I))$m"
  apply (rule eq_reflection)
  by auto

lemma hn_ASSUME_bind[sepref_comb_rules]: 
  assumes "vassn_tag \<Gamma> \<Longrightarrow> I"
  assumes "I \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R m"
  shows "hn_refine \<Gamma> c \<Gamma>' R (PR_CONST (op_ASSUME_bind I)$m)"
  apply (rule hn_refine_preI)
  using assms
  apply (cases I)
  apply (auto simp: vassn_tag_def)
  done
    
    
subsection "Import of Parametricity Theorems"
lemma pure_hn_refineI:
  assumes "Q \<longrightarrow> (c,a)\<in>R"
  shows "hn_refine (\<up>Q) (return c) (\<up>Q) (pure R) (RETURN a)"
  unfolding hn_refine_def using assms
  by (sep_auto simp: pure_def)

lemma pure_hn_refineI_no_asm:
  assumes "(c,a)\<in>R"
  shows "hn_refine emp (return c) emp (pure R) (RETURN a)"
  unfolding hn_refine_def using assms
  by (sep_auto simp: pure_def)

lemma import_param_0:
  "(P\<Longrightarrow>Q) \<equiv> Trueprop (PROTECT P \<longrightarrow> Q)"
  apply (rule, simp+)+
  done

lemma import_param_1: 
  "(P\<Longrightarrow>Q) \<equiv> Trueprop (P\<longrightarrow>Q)"
  "(P\<longrightarrow>Q\<longrightarrow>R) \<longleftrightarrow> (P\<and>Q \<longrightarrow> R)"
  "PROTECT (P \<and> Q) \<equiv> PROTECT P \<and> PROTECT Q"
  "(P \<and> Q) \<and> R \<equiv> P \<and> Q \<and> R"
  "(a,c)\<in>Rel \<and> PROTECT P \<longleftrightarrow> PROTECT P \<and> (a,c)\<in>Rel"
  apply (rule, simp+)+
  done

lemma import_param_2:
  "Trueprop (PROTECT P \<and> Q \<longrightarrow> R) \<equiv> (P \<Longrightarrow> Q\<longrightarrow>R)"
  apply (rule, simp+)+
  done

lemma import_param_3:
  "\<up>(P \<and> Q) = \<up>P*\<up>Q"
  "\<up>((c,a)\<in>R) = hn_val R a c"
  by (simp_all add: hn_ctxt_def pure_def)

named_theorems_rev sepref_import_rewrite \<open>Rewrite rules on importing parametricity theorems\<close>

lemma to_import_frefD: 
  assumes "(f,g)\<in>fref P R S"
  shows "\<lbrakk>PROTECT (P y); (x,y)\<in>R\<rbrakk> \<Longrightarrow> (f x, g y)\<in>S"
  using assms
  unfolding fref_def
  by auto

lemma add_PR_CONST: "(c,a)\<in>R \<Longrightarrow> (c,PR_CONST a)\<in>R" by simp

ML \<open>
structure Sepref_Import_Param = struct

  (* TODO: Almost clone of Sepref_Rules.to_foparam*)
  fun to_import_fo ctxt thm = let
    val unf_thms = @{thms 
      split_tupled_all prod_rel_simp uncurry_apply cnv_conj_to_meta Product_Type.split}
  in
    case Thm.concl_of thm of
      @{mpat "Trueprop ((_,_) \<in> fref _ _ _)"} =>
        (@{thm to_import_frefD} OF [thm])
        |> forall_intr_vars
        |> Local_Defs.unfold0 ctxt unf_thms
        |> Variable.gen_all ctxt
    | @{mpat "Trueprop ((_,_) \<in> _)"} =>
        Parametricity.fo_rule thm
    | _ => raise THM("Expected parametricity or fref theorem",~1,[thm])
  end

  fun add_PR_CONST thm = case Thm.concl_of thm of
    @{mpat "Trueprop ((_,_) \<in> fref _ _ _)"} => thm (* TODO: Hack. Need clean interfaces for fref and param rules. Also add PR_CONST to fref rules! *)
  | @{mpat "Trueprop ((_,PR_CONST _) \<in> _)"} => thm
  | @{mpat "Trueprop ((_,?a) \<in> _)"} => if is_Const a orelse is_Free a orelse is_Var a then
      thm
    else
      thm RS @{thm add_PR_CONST}
  | _ => thm  


  fun import ctxt thm = let
    open Sepref_Basic
    val thm = thm
      |> Conv.fconv_rule Thm.eta_conversion
      |> add_PR_CONST
      |> Local_Defs.unfold0 ctxt @{thms import_param_0}
      |> Local_Defs.unfold0 ctxt @{thms imp_to_meta}
      |> to_import_fo ctxt
      |> Local_Defs.unfold0 ctxt @{thms import_param_1}
      |> Local_Defs.unfold0 ctxt @{thms import_param_2}

    val thm = case Thm.concl_of thm of
      @{mpat "Trueprop (_\<longrightarrow>_)"} => thm RS @{thm pure_hn_refineI}
    | _ => thm RS @{thm pure_hn_refineI_no_asm}

    val thm = Local_Defs.unfold0 ctxt @{thms import_param_3} thm
      |> Conv.fconv_rule (hn_refine_concl_conv_a (K (Id_Op.protect_conv ctxt)) ctxt)

    val thm = Local_Defs.unfold0 ctxt (Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_import_rewrite}) thm
    val thm = Sepref_Rules.add_pure_constraints_rule ctxt thm
  in
    thm
  end

  val import_attr = Scan.succeed (Thm.mixed_attribute (fn (context,thm) =>
    let
      val thm = import (Context.proof_of context) thm
      val context = Sepref_Translate.sepref_fr_rules.add_thm thm context
    in (context,thm) end
  ))

  val import_attr_rl = Scan.succeed (Thm.rule_attribute [] (fn context =>
    import (Context.proof_of context) #> Sepref_Rules.ensure_hfref (Context.proof_of context)
  ))

  val setup = I
    #> Attrib.setup @{binding sepref_import_param} import_attr
        "Sepref: Import parametricity rule"
    #> Attrib.setup @{binding sepref_param} import_attr_rl
        "Sepref: Transform parametricity rule to sepref rule"
    #> Attrib.setup @{binding sepref_dbg_import_rl_only} 
        (Scan.succeed (Thm.rule_attribute [] (import o Context.proof_of)))
        "Sepref: Parametricity to hnr-rule, no conversion to hfref"    

end
\<close>

setup Sepref_Import_Param.setup


subsection "Purity"
definition "import_rel1 R \<equiv> \<lambda>A c ci. \<up>(is_pure A \<and> (ci,c)\<in>\<langle>the_pure A\<rangle>R)"
definition "import_rel2 R \<equiv> \<lambda>A B c ci. \<up>(is_pure A \<and> is_pure B \<and> (ci,c)\<in>\<langle>the_pure A, the_pure B\<rangle>R)"
  
lemma import_rel1_pure_conv: "import_rel1 R (pure A) = pure (\<langle>A\<rangle>R)"
  unfolding import_rel1_def
  apply simp
  apply (simp add: pure_def)
  done

lemma import_rel2_pure_conv: "import_rel2 R (pure A) (pure B) = pure (\<langle>A,B\<rangle>R)"
  unfolding import_rel2_def
  apply simp
  apply (simp add: pure_def)
  done

lemma precise_pure[constraint_rules]: "single_valued R \<Longrightarrow> precise (pure R)"
  unfolding precise_def pure_def
  by (auto dest: single_valuedD)

lemma precise_pure_iff_sv: "precise (pure R) \<longleftrightarrow> single_valued R"          
  apply (auto simp: precise_pure)
  using preciseD[where R="pure R" and F=emp and F'=emp]
  by (sep_auto simp: mod_and_dist intro: single_valuedI)

lemma pure_precise_iff_sv: "\<lbrakk>is_pure R\<rbrakk> 
  \<Longrightarrow> precise R \<longleftrightarrow> single_valued (the_pure R)"
  by (auto simp: is_pure_conv precise_pure_iff_sv)



lemmas [safe_constraint_rules] = single_valued_Id br_sv


end

