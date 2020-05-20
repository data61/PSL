theory Sepref_Constraints
imports Main Automatic_Refinement.Refine_Lib Sepref_Basic
begin

definition "CONSTRAINT_SLOT (x::prop) \<equiv> x"

(* TODO: Find something better than True to put in empty slot! Perhaps "A\<Longrightarrow>A" *)
lemma insert_slot_rl1:
  assumes "PROP P \<Longrightarrow> PROP (CONSTRAINT_SLOT (Trueprop True)) \<Longrightarrow> PROP Q"
  shows "PROP (CONSTRAINT_SLOT (PROP P)) \<Longrightarrow> PROP Q"
  using assms unfolding CONSTRAINT_SLOT_def by simp

lemma insert_slot_rl2:
  assumes "PROP P \<Longrightarrow> PROP (CONSTRAINT_SLOT S) \<Longrightarrow> PROP Q"
  shows "PROP (CONSTRAINT_SLOT (PROP S &&& PROP P)) \<Longrightarrow> PROP Q"
  using assms unfolding CONSTRAINT_SLOT_def conjunction_def .

lemma remove_slot: "PROP (CONSTRAINT_SLOT (Trueprop True))"
  unfolding CONSTRAINT_SLOT_def by (rule TrueI)

definition CONSTRAINT where [simp]: "CONSTRAINT P x \<equiv> P x"

lemma CONSTRAINT_D:
  assumes "CONSTRAINT (P::'a => bool) x"
  shows "P x"
  using assms unfolding CONSTRAINT_def by simp

lemma CONSTRAINT_I:
  assumes "P x"
  shows "CONSTRAINT (P::'a => bool) x"
  using assms unfolding CONSTRAINT_def by simp

text \<open>Special predicate to indicate unsolvable constraint.
  The constraint solver refuses to put those into slot.
  Thus, adding safe rules introducing this can be used to indicate 
  unsolvable constraints early.
\<close>
definition CN_FALSE :: "('a\<Rightarrow>bool) \<Rightarrow> 'a \<Rightarrow> bool" where [simp]: "CN_FALSE P x \<equiv> False"  
lemma CN_FALSEI: "CN_FALSE P x \<Longrightarrow> P x" by simp


named_theorems constraint_simps \<open>Simplification of constraints\<close>

named_theorems constraint_abbrevs \<open>Constraint Solver: Abbreviations\<close>
lemmas split_constraint_rls 
    = atomize_conj[symmetric] imp_conjunction all_conjunction conjunction_imp

ML \<open>
  signature SEPREF_CONSTRAINTS = sig
    (******** Constraint Slot *)
    (* Tactic with slot subgoal *)
    val WITH_SLOT: tactic' -> tactic
    (* Process all goals in slot *)
    val ON_SLOT: tactic -> tactic
    (* Create slot as last subgoal. Fail if slot already present. *)
    val create_slot_tac: tactic
    (* Create slot if there isn't one already *)
    val ensure_slot_tac: tactic
    (* Remove empty slot *)
    val remove_slot_tac: tactic
    (* Move slot to first subgoal *)
    val prefer_slot_tac: tactic
    (* Destruct slot *)
    val dest_slot_tac: tactic'
    (* Check if goal state has slot *)
    val has_slot: thm -> bool
    (* Defer subgoal to slot *)
    val to_slot_tac: tactic'
    (* Print slot constraints *)
    val print_slot_tac: Proof.context -> tactic

    (* Focus on goals in slot *)
    val focus: tactic
    (* Unfocus goals in slot *)
    val unfocus: tactic
    (* Unfocus goals, and insert them as first subgoals *)
    val unfocus_ins:tactic

    (* Focus on some goals in slot *)
    val cond_focus: (term -> bool) -> tactic
    (* Move some goals to slot *)
    val some_to_slot_tac: (term -> bool) -> tactic


    (******** Constraints *)
    (* Check if subgoal is a constraint. To be used with COND' *)
    val is_constraint_goal: term -> bool
    (* Identity on constraint subgoal, no_tac otherwise *)
    val is_constraint_tac: tactic'
    (* Defer constraint to slot *)
    val slot_constraint_tac: int -> tactic

    (******** Constraint solving *)

    val add_constraint_rule: thm -> Context.generic -> Context.generic
    val del_constraint_rule: thm -> Context.generic -> Context.generic
    val get_constraint_rules: Proof.context -> thm list

    val add_safe_constraint_rule: thm -> Context.generic -> Context.generic
    val del_safe_constraint_rule: thm -> Context.generic -> Context.generic
    val get_safe_constraint_rules: Proof.context -> thm list

    (* Solve constraint subgoal *)
    val solve_constraint_tac: Proof.context -> tactic'
    (* Solve constraint subgoal if solvable, fail if definitely unsolvable, 
      apply simplification and unique rules otherwise. *)
    val safe_constraint_tac: Proof.context -> tactic'

    (* CONSTRAINT tag on goal is optional *)
    val solve_constraint'_tac: Proof.context -> tactic'
    (* CONSTRAINT tag on goal is optional *)
    val safe_constraint'_tac: Proof.context -> tactic'
    
    (* Solve, or apply safe-rules and defer to constraint slot *)
    val constraint_tac: Proof.context -> tactic'

    (* Apply safe rules to all constraint goals in slot *)
    val process_constraint_slot: Proof.context -> tactic

    (* Solve all constraint goals in slot, insert unsolved ones as first subgoals *)
    val solve_constraint_slot: Proof.context -> tactic


    val setup: theory -> theory

  end


  structure Sepref_Constraints: SEPREF_CONSTRAINTS  = struct
    fun is_slot_goal @{mpat "CONSTRAINT_SLOT _"} = true | is_slot_goal _ = false

    fun slot_goal_num st = let
      val i = find_index is_slot_goal (Thm.prems_of st) + 1
    in
      i
    end

    fun has_slot st = slot_goal_num st > 0

    fun WITH_SLOT tac st = let
      val si = slot_goal_num st
    in
      if si>0 then tac si st else (warning "Constraints: No slot"; Seq.empty)
    end

    val to_slot_tac = IF_EXGOAL (fn i => WITH_SLOT (fn si => 
      if i<si then
        prefer_tac si THEN prefer_tac (i+1)
        THEN (
          PRIMITIVE (fn st => Drule.comp_no_flatten (st, 0) 1 @{thm insert_slot_rl1}) 
          ORELSE PRIMITIVE (fn st => Drule.comp_no_flatten (st, 0) 1 @{thm insert_slot_rl2})
        )
        THEN defer_tac 1
      else no_tac))

    val create_slot_tac = 
      COND (has_slot) no_tac
        (PRIMITIVE (Thm.implies_intr @{cterm "CONSTRAINT_SLOT (Trueprop True)"}) 
        THEN defer_tac 1)
        
    val ensure_slot_tac = TRY create_slot_tac
          
      
    val prefer_slot_tac = WITH_SLOT prefer_tac

    val dest_slot_tac = SELECT_GOAL (
      ALLGOALS (
        CONVERSION (Conv.rewr_conv @{thm CONSTRAINT_SLOT_def}) 
        THEN' Goal.conjunction_tac
        THEN' TRY o resolve0_tac @{thms TrueI})
      THEN distinct_subgoals_tac
    )

    val remove_slot_tac = WITH_SLOT (resolve0_tac @{thms remove_slot})

    val focus = WITH_SLOT (fn i => 
      PRIMITIVE (Goal.restrict i 1) 
      THEN ALLGOALS dest_slot_tac
      THEN create_slot_tac)

    val unfocus_ins = 
      PRIMITIVE (Goal.unrestrict 1)
      THEN WITH_SLOT defer_tac

    fun some_to_slot_tac cond = (ALLGOALS (COND' (fn t => is_slot_goal t orelse not (cond t)) ORELSE' to_slot_tac))

    val unfocus = 
      some_to_slot_tac (K true)
      THEN unfocus_ins

    fun cond_focus cond =
      focus 
      THEN some_to_slot_tac (not o cond)


    fun ON_SLOT tac = focus THEN tac THEN unfocus

    fun print_slot_tac ctxt = ON_SLOT (print_tac ctxt "SLOT:")

    local
      (*fun prepare_constraint_conv ctxt = let
        open Conv 
        fun CONSTRAINT_conv ct = case Thm.term_of ct of
          @{mpat "Trueprop (_ _)"} => 
            HOLogic.Trueprop_conv 
              (rewr_conv @{thm CONSTRAINT_def[symmetric]}) ct
          | _ => raise CTERM ("CONSTRAINT_conv", [ct])

        fun rec_conv ctxt ct = (
          CONSTRAINT_conv
          else_conv 
          implies_conv (rec_conv ctxt) (rec_conv ctxt)
          else_conv
          forall_conv (rec_conv o #2) ctxt
        ) ct
      in
        rec_conv ctxt
      end*)

      fun unfold_abbrevs ctxt = 
        Local_Defs.unfold0 ctxt (
          @{thms split_constraint_rls CONSTRAINT_def} 
          @ Named_Theorems.get ctxt @{named_theorems constraint_abbrevs}
          @ Named_Theorems.get ctxt @{named_theorems constraint_simps})
        #> Conjunction.elim_conjunctions
  
      fun check_constraint_rl thm = let
        fun ck (t as @{mpat "Trueprop (?C _)"}) = 
              if is_Var (Term.head_of C) then
                raise TERM ("Schematic head in constraint rule",[t,Thm.prop_of thm])
              else ()
          | ck @{mpat "\<And>_. PROP ?t"} = ck t
          | ck @{mpat "PROP ?s \<Longrightarrow> PROP ?t"} = (ck s; ck t)
          | ck t = raise TERM ("Invalid part of constraint rule",[t,Thm.prop_of thm])
  
      in
        ck (Thm.prop_of thm); thm
      end

      fun check_unsafe_constraint_rl thm = let
        val _ = Thm.nprems_of thm = 0 
          andalso raise TERM("Unconditional constraint rule must be safe (register this as safe rule)",[Thm.prop_of thm])
      in
        thm
      end

    in
      structure constraint_rules = Named_Sorted_Thms (
        val name = @{binding constraint_rules}
        val description = "Constraint rules"
        val sort = K I
        fun transform context = let
          open Conv
          val ctxt = Context.proof_of context
        in
          unfold_abbrevs ctxt #> map (check_constraint_rl o check_unsafe_constraint_rl)
        end
      )

      structure safe_constraint_rules = Named_Sorted_Thms (
        val name = @{binding safe_constraint_rules}
        val description = "Safe Constraint rules"
        val sort = K I
        fun transform context = let
          open Conv
          val ctxt = Context.proof_of context
        in
          unfold_abbrevs ctxt #> map check_constraint_rl
        end
      )

    end  

    val add_constraint_rule = constraint_rules.add_thm
    val del_constraint_rule = constraint_rules.del_thm
    val get_constraint_rules = constraint_rules.get

    val add_safe_constraint_rule = safe_constraint_rules.add_thm
    val del_safe_constraint_rule = safe_constraint_rules.del_thm
    val get_safe_constraint_rules = safe_constraint_rules.get

    fun is_constraint_goal t = case Logic.strip_assums_concl t of
      @{mpat "Trueprop (CONSTRAINT _ _)"} => true
    | _ => false

    val is_constraint_tac = COND' is_constraint_goal

    fun is_slottable_constraint_goal t = case Logic.strip_assums_concl t of
      @{mpat "Trueprop (CONSTRAINT (CN_FALSE _) _)"} => false
    | @{mpat "Trueprop (CONSTRAINT _ _)"} => true
    | _ => false

    val slot_constraint_tac = COND' is_slottable_constraint_goal THEN' to_slot_tac

    datatype 'a seq_cases = SC_NONE | SC_SINGLE of 'a Seq.seq | SC_MULTIPLE of 'a Seq.seq

    fun seq_cases seq = 
      case Seq.pull seq of
        NONE => SC_NONE
      | SOME (st1,seq) => case Seq.pull seq of
          NONE => SC_SINGLE (Seq.single st1)
        | SOME (st2,seq) => SC_MULTIPLE (Seq.cons st1 (Seq.cons st2 seq))  

    fun SEQ_CASES tac (single_tac, multiple_tac) st = let
      val res = tac st
    in
      case seq_cases res of
        SC_NONE => Seq.empty
      | SC_SINGLE res => Seq.maps single_tac res
      | SC_MULTIPLE res => Seq.maps multiple_tac res
    end

    fun SAFE tac = SEQ_CASES tac (all_tac, no_tac)
    fun SAFE' tac = SAFE o tac

    local
      fun simp_constraints_tac ctxt = let
        val ctxt = put_simpset HOL_basic_ss ctxt 
          addsimps (Named_Theorems.get ctxt @{named_theorems constraint_simps})
      in
        simp_tac ctxt
      end

      fun unfold_abbrevs_tac ctxt =  let
        val ctxt = put_simpset HOL_basic_ss ctxt 
          addsimps (Named_Theorems.get ctxt @{named_theorems constraint_abbrevs})
        val ethms = @{thms conjE}  
        val ithms = @{thms conjI}  
      in
        full_simp_tac ctxt 
        THEN_ALL_NEW TRY o REPEAT_ALL_NEW (ematch_tac ctxt ethms)
        THEN_ALL_NEW TRY o REPEAT_ALL_NEW (match_tac ctxt ithms)
      end
  
      fun WITH_RULE_NETS tac ctxt = let
        val scn_net = safe_constraint_rules.get ctxt |> Tactic.build_net
        val cn_net = constraint_rules.get ctxt |> Tactic.build_net
      in
        tac (scn_net,cn_net) ctxt
      end

      fun wrap_tac step_tac ctxt = REPEAT_ALL_NEW (
        simp_constraints_tac ctxt 
        THEN_ALL_NEW unfold_abbrevs_tac ctxt
        THEN_ALL_NEW step_tac ctxt
      )

      fun solve_step_tac (scn_net,cn_net) ctxt = REPEAT_ALL_NEW (
        DETERM o resolve_from_net_tac ctxt scn_net
        ORELSE' resolve_from_net_tac ctxt cn_net
      )

      fun safe_step_tac (scn_net,cn_net) ctxt = REPEAT_ALL_NEW (
        DETERM o resolve_from_net_tac ctxt scn_net
        ORELSE' SAFE' (resolve_from_net_tac ctxt cn_net)
      )

      fun solve_tac cn_nets ctxt = SOLVED' (wrap_tac (solve_step_tac cn_nets) ctxt)
      fun safe_tac cn_nets ctxt =  
        simp_constraints_tac ctxt
        THEN_ALL_NEW unfold_abbrevs_tac ctxt
        THEN_ALL_NEW (solve_tac cn_nets ctxt ORELSE' TRY o wrap_tac (safe_step_tac cn_nets) ctxt)

    in
      val solve_constraint_tac = TRADE (fn ctxt =>
        is_constraint_tac
        THEN' resolve_tac ctxt @{thms CONSTRAINT_I}
        THEN' WITH_RULE_NETS solve_tac ctxt)

      val safe_constraint_tac = TRADE (fn ctxt =>
        is_constraint_tac
        THEN' resolve_tac ctxt @{thms CONSTRAINT_I}
        THEN' WITH_RULE_NETS safe_tac ctxt
        THEN_ALL_NEW fo_resolve_tac @{thms CONSTRAINT_D} ctxt) (* TODO/FIXME: fo_resolve_tac has non-canonical parameter order *)

      val solve_constraint'_tac = TRADE (fn ctxt =>
        TRY o resolve_tac ctxt @{thms CONSTRAINT_I}
        THEN' WITH_RULE_NETS solve_tac ctxt)

      val safe_constraint'_tac = TRADE (fn ctxt =>
        TRY o resolve_tac ctxt @{thms CONSTRAINT_I}
        THEN' WITH_RULE_NETS safe_tac ctxt)


    end  

    fun constraint_tac ctxt = 
      safe_constraint_tac ctxt THEN_ALL_NEW slot_constraint_tac

    fun process_constraint_slot ctxt = ON_SLOT (ALLGOALS (TRY o safe_constraint_tac ctxt))

    fun solve_constraint_slot ctxt = 
      cond_focus is_constraint_goal 
        THEN ALLGOALS (
          COND' is_slot_goal
          ORELSE' (
            solve_constraint_tac ctxt
            ORELSE' TRY o safe_constraint_tac ctxt
          )
        )
      THEN unfocus_ins


    val setup = I
      #> constraint_rules.setup
      #> safe_constraint_rules.setup

  end
\<close>

setup Sepref_Constraints.setup

method_setup print_slot = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (Sepref_Constraints.print_slot_tac ctxt))\<close>

method_setup solve_constraint = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Sepref_Constraints.solve_constraint'_tac ctxt))\<close>
method_setup safe_constraint = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Sepref_Constraints.safe_constraint'_tac ctxt))\<close>


end
