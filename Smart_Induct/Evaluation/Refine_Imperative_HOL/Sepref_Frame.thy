section \<open>Frame Inference\<close>
theory Sepref_Frame
imports Sepref_Basic Sepref_Constraints
begin
  text \<open> In this theory, we provide a specific frame inference tactic
    for Sepref.

    The first tactic, \<open>frame_tac\<close>, is a standard frame inference tactic, 
    based on the assumption that only @{const hn_ctxt}-assertions need to be
    matched.

    The second tactic, \<open>merge_tac\<close>, resolves entailments of the form
      \<open>F1 \<or>\<^sub>A F2 \<Longrightarrow>\<^sub>t ?F\<close>
    that occur during translation of if and case statements.
    It synthesizes a new frame ?F, where refinements of variables 
    with equal refinements in \<open>F1\<close> and \<open>F2\<close> are preserved,
    and the others are set to @{const hn_invalid}.
    \<close>

definition mismatch_assn :: "('a \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> assn"
  where "mismatch_assn R1 R2 x y \<equiv> R1 x y \<or>\<^sub>A R2 x y"

abbreviation "hn_mismatch R1 R2 \<equiv> hn_ctxt (mismatch_assn R1 R2)"

lemma recover_pure_aux: "CONSTRAINT is_pure R \<Longrightarrow> hn_invalid R x y \<Longrightarrow>\<^sub>t hn_ctxt R x y"
  by (auto simp: is_pure_conv invalid_pure_recover hn_ctxt_def)



lemma frame_thms:
  "P \<Longrightarrow>\<^sub>t P"
  "P\<Longrightarrow>\<^sub>tP' \<Longrightarrow> F\<Longrightarrow>\<^sub>tF' \<Longrightarrow> F*P \<Longrightarrow>\<^sub>t F'*P'"
  "hn_ctxt R x y \<Longrightarrow>\<^sub>t hn_invalid R x y"
  "hn_ctxt R x y \<Longrightarrow>\<^sub>t hn_ctxt (\<lambda>_ _. true) x y"
  "CONSTRAINT is_pure R \<Longrightarrow> hn_invalid R x y \<Longrightarrow>\<^sub>t hn_ctxt R x y"
  apply -
  applyS simp
  applyS (rule entt_star_mono; assumption)
  subgoal
    apply (simp add: hn_ctxt_def)
    apply (rule enttI)
    apply (rule ent_trans[OF invalidate[of R]])
    by solve_entails
  applyS (sep_auto simp: hn_ctxt_def)  
  applyS (erule recover_pure_aux)
  done

named_theorems_rev sepref_frame_match_rules \<open>Sepref: Additional frame rules\<close>

text \<open>Rules to discharge unmatched stuff\<close>
(*lemma frame_rem_thms:
  "P \<Longrightarrow>\<^sub>t P"
  "P \<Longrightarrow>\<^sub>t emp"
  by sep_auto+
*)
lemma frame_rem1: "P\<Longrightarrow>\<^sub>tP" by simp

lemma frame_rem2: "F \<Longrightarrow>\<^sub>t F' \<Longrightarrow> F * hn_ctxt A x y \<Longrightarrow>\<^sub>t F' * hn_ctxt A x y"
  apply (rule entt_star_mono) by auto

lemma frame_rem3: "F \<Longrightarrow>\<^sub>t F' \<Longrightarrow> F * hn_ctxt A x y \<Longrightarrow>\<^sub>t F'"
  using frame_thms(2) by fastforce
  
lemma frame_rem4: "P \<Longrightarrow>\<^sub>t emp" by simp

lemmas frame_rem_thms = frame_rem1 frame_rem2 frame_rem3 frame_rem4

named_theorems_rev sepref_frame_rem_rules
  \<open>Sepref: Additional rules to resolve remainder of frame-pairing\<close>

lemma ent_disj_star_mono:
  "\<lbrakk> A \<or>\<^sub>A C \<Longrightarrow>\<^sub>A E; B \<or>\<^sub>A D \<Longrightarrow>\<^sub>A F \<rbrakk> \<Longrightarrow> A*B \<or>\<^sub>A C*D \<Longrightarrow>\<^sub>A E*F"
  by (metis ent_disjI1 ent_disjI2 ent_disjE ent_star_mono)  

lemma entt_disj_star_mono:
  "\<lbrakk> A \<or>\<^sub>A C \<Longrightarrow>\<^sub>t E; B \<or>\<^sub>A D \<Longrightarrow>\<^sub>t F \<rbrakk> \<Longrightarrow> A*B \<or>\<^sub>A C*D \<Longrightarrow>\<^sub>t E*F"
proof -
  assume a1: "A \<or>\<^sub>A C \<Longrightarrow>\<^sub>t E"
  assume "B \<or>\<^sub>A D \<Longrightarrow>\<^sub>t F"
  then have "A * B \<or>\<^sub>A C * D \<Longrightarrow>\<^sub>A true * E * (true * F)"
    using a1 by (simp add: ent_disj_star_mono enttD)
  then show ?thesis
    by (metis (no_types) assn_times_comm enttI merge_true_star_ctx star_aci(3))
qed
    


lemma hn_merge1:
  (*"emp \<or>\<^sub>A emp \<Longrightarrow>\<^sub>A emp"*)
  "F \<or>\<^sub>A F \<Longrightarrow>\<^sub>t F"
  "\<lbrakk> hn_ctxt R1 x x' \<or>\<^sub>A hn_ctxt R2 x x' \<Longrightarrow>\<^sub>t hn_ctxt R x x'; Fl \<or>\<^sub>A Fr \<Longrightarrow>\<^sub>t F \<rbrakk> 
    \<Longrightarrow> Fl * hn_ctxt R1 x x' \<or>\<^sub>A Fr * hn_ctxt R2 x x' \<Longrightarrow>\<^sub>t F * hn_ctxt R x x'"
  apply simp
  by (rule entt_disj_star_mono; simp)

lemma hn_merge2:
  "hn_invalid R x x' \<or>\<^sub>A hn_ctxt R x x' \<Longrightarrow>\<^sub>t hn_invalid R x x'"
  "hn_ctxt R x x' \<or>\<^sub>A hn_invalid R x x' \<Longrightarrow>\<^sub>t hn_invalid R x x'"
  by (sep_auto eintros: invalidate ent_disjE intro!: ent_imp_entt simp: hn_ctxt_def)+

lemma invalid_assn_mono: "hn_ctxt A x y \<Longrightarrow>\<^sub>t hn_ctxt B x y 
  \<Longrightarrow> hn_invalid A x y \<Longrightarrow>\<^sub>t hn_invalid B x y"
  by (clarsimp simp: invalid_assn_def entailst_def entails_def hn_ctxt_def)
      (force simp: mod_star_conv)

lemma hn_merge3: (* Not used *)
  "\<lbrakk>NO_MATCH (hn_invalid XX) R2; hn_ctxt R1 x x' \<or>\<^sub>A hn_ctxt R2 x x' \<Longrightarrow>\<^sub>t hn_ctxt Rm x x'\<rbrakk> \<Longrightarrow> hn_invalid R1 x x' \<or>\<^sub>A hn_ctxt R2 x x' \<Longrightarrow>\<^sub>t hn_invalid Rm x x'"
  "\<lbrakk>NO_MATCH (hn_invalid XX) R1; hn_ctxt R1 x x' \<or>\<^sub>A hn_ctxt R2 x x' \<Longrightarrow>\<^sub>t hn_ctxt Rm x x'\<rbrakk> \<Longrightarrow> hn_ctxt R1 x x' \<or>\<^sub>A hn_invalid R2 x x' \<Longrightarrow>\<^sub>t hn_invalid Rm x x'"
  apply (meson entt_disjD1 entt_disjD2 entt_disjE entt_trans frame_thms(3) invalid_assn_mono)  
  apply (meson entt_disjD1 entt_disjD2 entt_disjE entt_trans frame_thms(3) invalid_assn_mono)  
  done

lemmas merge_thms = hn_merge1 hn_merge2 

named_theorems sepref_frame_merge_rules \<open>Sepref: Additional merge rules\<close>


lemma hn_merge_mismatch: "hn_ctxt R1 x x' \<or>\<^sub>A hn_ctxt R2 x x' \<Longrightarrow>\<^sub>t hn_mismatch R1 R2 x x'"
  by (sep_auto simp: hn_ctxt_def mismatch_assn_def)

lemma is_merge: "P1\<or>\<^sub>AP2\<Longrightarrow>\<^sub>tP \<Longrightarrow> P1\<or>\<^sub>AP2\<Longrightarrow>\<^sub>tP" .

lemma merge_mono: "\<lbrakk>A\<Longrightarrow>\<^sub>tA'; B\<Longrightarrow>\<^sub>tB'; A'\<or>\<^sub>AB' \<Longrightarrow>\<^sub>t C\<rbrakk> \<Longrightarrow> A\<or>\<^sub>AB \<Longrightarrow>\<^sub>t C"
  by (meson entt_disjE entt_disjI1_direct entt_disjI2_direct entt_trans)
  
text \<open>Apply forward rule on left or right side of merge\<close>
lemma gen_merge_cons1: "\<lbrakk>A\<Longrightarrow>\<^sub>tA'; A'\<or>\<^sub>AB \<Longrightarrow>\<^sub>t C\<rbrakk> \<Longrightarrow> A\<or>\<^sub>AB \<Longrightarrow>\<^sub>t C"
  by (meson merge_mono entt_refl)

lemma gen_merge_cons2: "\<lbrakk>B\<Longrightarrow>\<^sub>tB'; A\<or>\<^sub>AB' \<Longrightarrow>\<^sub>t C\<rbrakk> \<Longrightarrow> A\<or>\<^sub>AB \<Longrightarrow>\<^sub>t C"
  by (meson merge_mono entt_refl)
  
lemmas gen_merge_cons = gen_merge_cons1 gen_merge_cons2


text \<open>These rules are applied to recover pure values that have been destroyed by rule application\<close>

definition "RECOVER_PURE P Q \<equiv> P \<Longrightarrow>\<^sub>t Q"

lemma recover_pure:
  "RECOVER_PURE emp emp"
  "\<lbrakk>RECOVER_PURE P2 Q2; RECOVER_PURE P1 Q1\<rbrakk> \<Longrightarrow> RECOVER_PURE (P1*P2) (Q1*Q2)"
  "CONSTRAINT is_pure R \<Longrightarrow> RECOVER_PURE (hn_invalid R x y) (hn_ctxt R x y)"
  "RECOVER_PURE (hn_ctxt R x y) (hn_ctxt R x y)"
  unfolding RECOVER_PURE_def
  subgoal by sep_auto
  subgoal by (drule (1) entt_star_mono)
  subgoal by (rule recover_pure_aux)
  subgoal by sep_auto
  done
  
lemma recover_pure_triv: 
  "RECOVER_PURE P P"
  unfolding RECOVER_PURE_def by sep_auto


text \<open>Weakening the postcondition by converting @{const invalid_assn} to @{term "\<lambda>_ _. true"}\<close>
definition "WEAKEN_HNR_POST \<Gamma> \<Gamma>' \<Gamma>'' \<equiv> (\<exists>h. h\<Turnstile>\<Gamma>) \<longrightarrow> (\<Gamma>'' \<Longrightarrow>\<^sub>t \<Gamma>')"

lemma weaken_hnr_postI:
  assumes "WEAKEN_HNR_POST \<Gamma> \<Gamma>'' \<Gamma>'"
  assumes "hn_refine \<Gamma> c \<Gamma>' R a"
  shows "hn_refine \<Gamma> c \<Gamma>'' R a"
  apply (rule hn_refine_preI)
  apply (rule hn_refine_cons_post)
  apply (rule assms)
  using assms(1) unfolding WEAKEN_HNR_POST_def by blast

lemma weaken_hnr_post_triv: "WEAKEN_HNR_POST \<Gamma> P P"
  unfolding WEAKEN_HNR_POST_def
  by sep_auto

lemma weaken_hnr_post:
  "\<lbrakk>WEAKEN_HNR_POST \<Gamma> P P'; WEAKEN_HNR_POST \<Gamma>' Q Q'\<rbrakk> \<Longrightarrow> WEAKEN_HNR_POST (\<Gamma>*\<Gamma>') (P*Q) (P'*Q')"
  "WEAKEN_HNR_POST (hn_ctxt R x y) (hn_ctxt R x y) (hn_ctxt R x y)"
  "WEAKEN_HNR_POST (hn_ctxt R x y) (hn_invalid R x y) (hn_ctxt (\<lambda>_ _. true) x y)"
proof (goal_cases)
  case 1 thus ?case
    unfolding WEAKEN_HNR_POST_def
    apply clarsimp
    apply (rule entt_star_mono) 
    by (auto simp: mod_star_conv)
next
  case 2 thus ?case by (rule weaken_hnr_post_triv)
next
  case 3 thus ?case 
    unfolding WEAKEN_HNR_POST_def 
    by (sep_auto simp: invalid_assn_def hn_ctxt_def)
qed



lemma reorder_enttI:
  assumes "A*true = C*true"
  assumes "B*true = D*true"
  shows "(A\<Longrightarrow>\<^sub>tB) \<equiv> (C\<Longrightarrow>\<^sub>tD)"
  apply (intro eq_reflection)
  unfolding entt_def_true
  by (simp add: assms)
  
  

lemma merge_sat1: "(A\<or>\<^sub>AA' \<Longrightarrow>\<^sub>t Am) \<Longrightarrow> (A\<or>\<^sub>AAm \<Longrightarrow>\<^sub>t Am)"
  using entt_disjD1 entt_disjE by blast
lemma merge_sat2: "(A\<or>\<^sub>AA' \<Longrightarrow>\<^sub>t Am) \<Longrightarrow> (Am\<or>\<^sub>AA' \<Longrightarrow>\<^sub>t Am)"
  using entt_disjD2 entt_disjE by blast





ML \<open>
signature SEPREF_FRAME = sig


  (* Check if subgoal is a frame obligation *)
  (*val is_frame : term -> bool *)
  (* Check if subgoal is a merge obligation *)
  val is_merge: term -> bool
  (* Perform frame inference *)
  val frame_tac: (Proof.context -> tactic') -> Proof.context -> tactic'
  (* Perform merging *)
  val merge_tac: (Proof.context -> tactic') -> Proof.context -> tactic'

  val frame_step_tac: (Proof.context -> tactic') -> bool -> Proof.context -> tactic'

  (* Reorder frame *)
  val prepare_frame_tac : Proof.context -> tactic'
  (* Solve a RECOVER_PURE goal, inserting constraints as necessary *)
  val recover_pure_tac: Proof.context -> tactic'

  (* Split precondition of hnr-goal into frame and arguments *)
  val align_goal_tac: Proof.context -> tactic'
  (* Normalize goal's precondition *)
  val norm_goal_pre_tac: Proof.context -> tactic'
  (* Rearrange precondition of hnr-term according to parameter order, normalize all relations *)
  val align_rl_conv: Proof.context -> conv

  (* Convert hn_invalid to \<lambda>_ _. true in postcondition of hnr-goal. Makes proving the goal easier.*)
  val weaken_post_tac: Proof.context -> tactic'

  val add_normrel_eq : thm -> Context.generic -> Context.generic
  val del_normrel_eq : thm -> Context.generic -> Context.generic
  val get_normrel_eqs : Proof.context -> thm list

  val cfg_debug: bool Config.T

  val setup: theory -> theory
end


structure Sepref_Frame : SEPREF_FRAME = struct

  val cfg_debug = 
    Attrib.setup_config_bool @{binding sepref_debug_frame} (K false)

  val DCONVERSION = Sepref_Debugging.DBG_CONVERSION cfg_debug
  val dbg_msg_tac = Sepref_Debugging.dbg_msg_tac cfg_debug


  structure normrel_eqs = Named_Thms (
    val name = @{binding sepref_frame_normrel_eqs}
    val description = "Equations to normalize relations for frame matching"
  )

  val add_normrel_eq = normrel_eqs.add_thm
  val del_normrel_eq = normrel_eqs.del_thm
  val get_normrel_eqs = normrel_eqs.get

  val mk_entailst = HOLogic.mk_binrel @{const_name "entailst"}


  local
    open Sepref_Basic Refine_Util Conv
  
    fun assn_ord p = case apply2 dest_hn_ctxt_opt p of
        (NONE,NONE) => EQUAL
      | (SOME _, NONE) => LESS
      | (NONE, SOME _) => GREATER
      | (SOME (_,a,_), SOME (_,a',_)) => Term_Ord.fast_term_ord (a,a')

  in
    fun reorder_ctxt_conv ctxt ct = let
      val cert = Thm.cterm_of ctxt

      val new_ct = Thm.term_of ct 
        |> strip_star
        |> sort assn_ord
        |> list_star
        |> cert

      val thm = Goal.prove_internal ctxt [] (mk_cequals (ct,new_ct)) 
        (fn _ => simp_tac 
          (put_simpset HOL_basic_ss ctxt addsimps @{thms star_aci}) 1)

    in
      thm
    end
  
    fun prepare_fi_conv ctxt ct = case Thm.term_of ct of
      @{mpat "?P \<Longrightarrow>\<^sub>t ?Q"} => let
        val cert = Thm.cterm_of ctxt
  
        (* Build table from abs-vars to ctxt *)
        val (Qm, Qum) = strip_star Q |> filter_out is_true |> List.partition is_hn_ctxt

        val Qtab = (
          Qm |> map (fn x => (#2 (dest_hn_ctxt x),(NONE,x))) 
          |> Termtab.make
        ) handle
            e as (Termtab.DUP _) => (
              tracing ("Dup heap: " ^ @{make_string} ct); raise e)
        
        (* Go over entries in P and try to find a partner *)
        val (Qtab,Pum) = fold (fn a => fn (Qtab,Pum) => 
          case dest_hn_ctxt_opt a of
            NONE => (Qtab,a::Pum)
          | SOME (_,p,_) => ( case Termtab.lookup Qtab p of
              SOME (NONE,tg) => (Termtab.update (p,(SOME a,tg)) Qtab, Pum)
            | _ => (Qtab,a::Pum)
            )
        ) (strip_star P) (Qtab,[])

        val Pum = filter_out is_true Pum

        (* Read out information from Qtab *)
        val (pairs,Qum2) = Termtab.dest Qtab |> map #2 
          |> List.partition (is_some o #1)
          |> apfst (map (apfst the))
          |> apsnd (map #2)
  
        (* Build reordered terms: P' = fst pairs * Pum, Q' = snd pairs * (Qum2*Qum) *)
        val P' = mk_star (list_star (map fst pairs), list_star Pum)
        val Q' = mk_star (list_star (map snd pairs), list_star (Qum2@Qum))
        
        val new_ct = mk_entailst (P', Q') |> cert
  
        val msg_tac = dbg_msg_tac (Sepref_Debugging.msg_allgoals "Solving frame permutation") ctxt 1
        val tac = msg_tac THEN ALLGOALS (resolve_tac ctxt @{thms reorder_enttI}) THEN star_permute_tac ctxt

        val thm = Goal.prove_internal ctxt [] (mk_cequals (ct,new_ct)) (fn _ => tac)
  
      in 
        thm
      end
    | _ => no_conv ct
  
  end

  fun is_merge @{mpat "Trueprop (_ \<or>\<^sub>A _ \<Longrightarrow>\<^sub>t _)"} = true | is_merge _ = false
  fun is_gen_frame @{mpat "Trueprop (_ \<Longrightarrow>\<^sub>t _)"} = true | is_gen_frame _ = false


  fun prepare_frame_tac ctxt = let
    open Refine_Util Conv
    val frame_ss = put_simpset HOL_basic_ss ctxt addsimps 
      @{thms mult_1_right[where 'a=assn] mult_1_left[where 'a=assn]}
  in
    CONVERSION Thm.eta_conversion THEN'
    (*CONCL_COND' is_frame THEN'*)
    simp_tac frame_ss THEN'
    CONVERSION (HOL_concl_conv (fn _ => prepare_fi_conv ctxt) ctxt)
  end    


  local
    fun wrap_side_tac side_tac dbg tac = tac THEN_ALL_NEW_FWD (
      CONCL_COND' is_gen_frame 
      ORELSE' (if dbg then TRY_SOLVED' else SOLVED') side_tac
    )
  in  
    fun frame_step_tac side_tac dbg ctxt = let
      open Refine_Util Conv

      (* Constraint solving is built-in *)
      val side_tac = Sepref_Constraints.constraint_tac ctxt ORELSE' side_tac ctxt

      val frame_thms = @{thms frame_thms} @
        Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_frame_match_rules} 
      val merge_thms = @{thms merge_thms} @
        Named_Theorems.get ctxt @{named_theorems sepref_frame_merge_rules}
      val ss = put_simpset HOL_basic_ss ctxt addsimps normrel_eqs.get ctxt
      fun frame_thm_tac dbg = wrap_side_tac side_tac dbg (resolve_tac ctxt frame_thms)
      fun merge_thm_tac dbg = wrap_side_tac side_tac dbg (resolve_tac ctxt merge_thms)
  
      fun thm_tac dbg = CONCL_COND' is_merge THEN_ELSE' (merge_thm_tac dbg, frame_thm_tac dbg)
    in
      full_simp_tac ss THEN' thm_tac dbg
    end
  end  

  fun frame_loop_tac side_tac ctxt = let

  in
    TRY o (
      REPEAT_ALL_NEW (DETERM o frame_step_tac side_tac false ctxt)
    )
  end


  fun frame_tac side_tac ctxt = let
    open Refine_Util Conv
    val frame_rem_thms = @{thms frame_rem_thms}
      @ Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_frame_rem_rules}
    val solve_remainder_tac = TRY o REPEAT_ALL_NEW (DETERM o resolve_tac ctxt frame_rem_thms)
  in
    (prepare_frame_tac ctxt
      THEN' resolve_tac ctxt @{thms ent_star_mono entt_star_mono})
    THEN_ALL_NEW_LIST [
      frame_loop_tac side_tac ctxt,
      solve_remainder_tac
    ]  
  end

  fun merge_tac side_tac ctxt = let
    open Refine_Util Conv
    val merge_conv = arg1_conv (binop_conv (reorder_ctxt_conv ctxt))
  in
    CONVERSION Thm.eta_conversion THEN'
    CONCL_COND' is_merge THEN'
    simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms star_aci}) THEN'
    CONVERSION (HOL_concl_conv (fn _ => merge_conv) ctxt) THEN'
    frame_loop_tac side_tac ctxt
  end

  val setup = normrel_eqs.setup

  local
    open Sepref_Basic
    fun is_invalid @{mpat "hn_invalid _ _ _ :: assn"} = true | is_invalid _ = false
    fun contains_invalid @{mpat "Trueprop (RECOVER_PURE ?Q _)"} = exists is_invalid (strip_star Q)
      | contains_invalid _ = false

  in
    fun recover_pure_tac ctxt = 
      CONCL_COND' contains_invalid THEN_ELSE' (
        REPEAT_ALL_NEW (DETERM o (resolve_tac ctxt @{thms recover_pure} ORELSE' Sepref_Constraints.constraint_tac ctxt)),
        resolve_tac ctxt @{thms recover_pure_triv}
      )
  end

  local
    open Sepref_Basic Refine_Util
    datatype cte = Other of term | Hn of term * term * term
    fun dest_ctxt_elem @{mpat "hn_ctxt ?R ?a ?c"} = Hn (R,a,c)
      | dest_ctxt_elem t = Other t

    fun mk_ctxt_elem (Other t) = t 
      | mk_ctxt_elem (Hn (R,a,c)) = @{mk_term "hn_ctxt ?R ?a ?c"}

    fun match x (Hn (_,y,_)) = x aconv y
      | match _ _ = false

    fun dest_with_frame (*ctxt*) _ t = let
      val (P,c,Q,R,a) = dest_hn_refine t
  
      val (_,(_,args)) = dest_hnr_absfun a
      val pre_ctes = strip_star P |> map dest_ctxt_elem
  
      val (pre_args,frame) = 
        (case split_matching match args pre_ctes of
            NONE => raise TERM("align_conv: Could not match all arguments",[P,a])
          | SOME x => x)

    in
      ((frame,pre_args),c,Q,R,a)
    end
  
    fun align_goal_conv_aux ctxt t = let
      val ((frame,pre_args),c,Q,R,a) = dest_with_frame ctxt t
      val P' = apply2 (list_star o map mk_ctxt_elem) (frame,pre_args) |> mk_star
      val t' = mk_hn_refine (P',c,Q,R,a)
    in t' end  

    fun align_rl_conv_aux ctxt t = let
      val ((frame,pre_args),c,Q,R,a) = dest_with_frame ctxt t

      val _ = frame = [] orelse raise TERM ("align_rl_conv: Extra preconditions in rule",[t,list_star (map mk_ctxt_elem frame)])

      val P' = list_star (map mk_ctxt_elem pre_args)
      val t' = mk_hn_refine (P',c,Q,R,a)
    in t' end  


    fun normrel_conv ctxt = let
      val ss = put_simpset HOL_basic_ss ctxt addsimps normrel_eqs.get ctxt
    in
      Simplifier.rewrite ss
    end

  in
    fun align_goal_conv ctxt = f_tac_conv ctxt (align_goal_conv_aux ctxt) (star_permute_tac ctxt)

    fun norm_goal_pre_conv ctxt = let
      open Conv
      val nr_conv = normrel_conv ctxt
    in
      HOL_concl_conv (fn _ => hn_refine_conv nr_conv all_conv all_conv all_conv all_conv) ctxt
    end  

    fun norm_goal_pre_tac ctxt = CONVERSION (norm_goal_pre_conv ctxt)

    fun align_rl_conv ctxt = let
      open Conv
      val nr_conv = normrel_conv ctxt
    in
      HOL_concl_conv (fn ctxt => f_tac_conv ctxt (align_rl_conv_aux ctxt) (star_permute_tac ctxt)) ctxt
      then_conv HOL_concl_conv (K (hn_refine_conv nr_conv all_conv nr_conv nr_conv all_conv)) ctxt
    end

    fun align_goal_tac ctxt = 
      CONCL_COND' is_hn_refine_concl 
      THEN' DCONVERSION ctxt (HOL_concl_conv align_goal_conv ctxt)
  end


  fun weaken_post_tac ctxt = TRADE (fn ctxt =>
    resolve_tac ctxt @{thms weaken_hnr_postI} 
    THEN' SOLVED' (REPEAT_ALL_NEW (DETERM o resolve_tac ctxt @{thms weaken_hnr_post weaken_hnr_post_triv}))
  ) ctxt

end
\<close>

setup Sepref_Frame.setup

method_setup weaken_hnr_post = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Sepref_Frame.weaken_post_tac ctxt))\<close>
  \<open>Convert "hn_invalid" to "hn_ctxt (\<lambda>_ _. true)" in postcondition of hn_refine goal\<close>

(* TODO: Improper, modifies all h\<Turnstile>_ premises that happen to be there. Use tagging to protect! *)
method extract_hnr_invalids = (
  rule hn_refine_preI,
  ((drule mod_starD hn_invalidI | elim conjE exE)+)?
) \<comment> \<open>Extract \<open>hn_invalid _ _ _ = true\<close> preconditions from \<open>hn_refine\<close> goal.\<close>
  


lemmas [sepref_frame_normrel_eqs] = the_pure_pure pure_the_pure

end

