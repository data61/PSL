
signature STURM =
sig
  val sturm_conv : Proof.context -> conv
  val sturm_tac :  Proof.context -> bool -> int -> tactic
end;

structure Sturm : STURM =
struct

  fun sturm_conv ctxt = Code_Runtime.dynamic_holds_conv ctxt (* FIXME prefer static converson? *)
(*    [@{const_name count_roots_between}, @{const_name count_roots},
     @{const_name count_roots_above},@{const_name count_roots_below},
     @{const_name Trueprop}, @{const_name Rat.of_int}, 
     @{const_name Power.power_class.power},
     @{const_name Real.ord_real_inst.less_eq_real},
     @{const_name Real.ord_real_inst.less_real},
     @{const_name Num.nat_of_num}]*)

  val sturm_id_thmss = [@{thms sturm_id_PR_prio2}, @{thms sturm_id_PR_prio1}, 
          @{thms sturm_id_PR_prio0}]
  val sturm_PR_tag_intro_thmss = [@{thms PR_TAG_intro_prio2}, @{thms PR_TAG_intro_prio1}, @{thms PR_TAG_intro_prio0}]

  fun extract_PR_tags (t as (Const (@{const_name PR_TAG}, _) $ _)) acc = t :: acc
    | extract_PR_tags (s $ t) acc = extract_PR_tags s (extract_PR_tags t acc)
    | extract_PR_tags (Abs (_,_,t)) acc = extract_PR_tags t acc
    | extract_PR_tags _ acc = acc

  fun sturm_preprocess_tac ctxt i =
    let fun subst_tac thms = EqSubst.eqsubst_tac ctxt [1] thms i
        fun process_PR_tag_tac thm =
          let val trms = extract_PR_tags (Thm.prop_of thm) []
              fun tac trm = 
                let val subst = Thm.reflexive (Thm.cterm_of ctxt trm) RS @{thm HOL.meta_eq_to_obj_eq}
                    val subst = subst RS @{thm HOL.trans}
                    val subst = subst RS @{thm HOL.ssubst}
                in  TRY (resolve_tac ctxt [subst] i
                    THEN REPEAT_ALL_NEW (FIRST' (map (fn thms => 
                             DETERM o resolve_tac ctxt thms) sturm_PR_tag_intro_thmss)) i)
                end;
          in  EVERY (map tac trms) thm
          end;
    in  FIRST (map subst_tac sturm_id_thmss)
        THEN REPEAT (subst_tac @{thms HOL.nnf_simps(1,2,5) not_less not_le})
        THEN process_PR_tag_tac
    end;

  fun find_sturm_card_eq_thm ctxt s =
    let val thy = Proof_Context.theory_of ctxt
        fun matches thm =
          case Thm.concl_of thm of
            Const (@{const_name Trueprop}, _) $ (Const (@{const_name HOL.eq}, _) $ 
                (Const (@{const_name Finite_Set.card}, _) $ s') $ _)
              => Pattern.matches thy (s',s)
          | _ => 
              let val _ = warning ("Invalid theorem in " ^
                          "sturm_card_eq_substs: \n" ^ Pretty.string_of (
                            Syntax.pretty_term ctxt (Thm.concl_of thm)));
               in false
              end
        val thm = find_first matches @{thms sturm_card_substs};
    in
        thm
    end;

  fun sturm_card_eq_instantiate_tac ctxt _ thm =
    let val prop = case Thm.prems_of thm of p :: _ => p | _ => Thm.concl_of thm  (* FIXME tactic must not access main conclusion *)
        val prop = case prop of Const (@{const_name Pure.prop}, _) $ prop => prop
                                | _ => prop
        val prop = case prop of Const (@{const_name Pure.conjunction}, _) $ 
                                    (Const (@{const_name Pure.term}, _) $ _) $ prop => prop
                                 | _ => prop
        val (lhs,rhs) = prop |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
        val vars = Term.add_vars rhs []
    in case vars of
          [v] => let val (idxname,ty) = v
                      val n = Code_Evaluation.dynamic_value ctxt lhs  (* FIXME prefer static converson? *)
                  in case n of
                     NONE => Seq.empty
                   | SOME n => 
                       (* FIXME fragile term as string composition *)
                       let val n' = (if ty = @{typ nat} then "" else "%_. ") ^ Int.toString (snd (HOLogic.dest_number n))
                       in  Seq.single (Rule_Insts.read_instantiate ctxt [((idxname, Position.none), n')] [] thm)
                       end
                  end
        | _ => Seq.single thm
    end;
    

  fun sturm_card_eq_tac ctxt i thm =
    let val prop = case Thm.prems_of thm of p :: _ => p | _ => Thm.concl_of thm (* FIXME tactic must not access main conclusion *)
        val prop = case prop of Const (@{const_name Pure.prop}, _) $ prop => prop
                                | _ => prop
        val prop = case prop of Const (@{const_name Pure.conjunction}, _) $ 
                                    (Const (@{const_name Pure.term}, _) $ _) $ prop => prop
                                 | _ => prop
        val s = case prop of
                        Const (@{const_name Trueprop}, _) $
                        (Const (@{const_name HOL.eq}, _) $ 
                          (Const (@{const_name Finite_Set.card}, _) $ s) $ _)
                        => s;
        val thm' = find_sturm_card_eq_thm ctxt s
    in  case thm' of
          NONE => Seq.empty
        |  SOME thm'' => (EqSubst.eqsubst_tac ctxt [1] [thm''] i
                          THEN sturm_card_eq_instantiate_tac ctxt i) thm
    end;

  fun find_sturm_prop_thm ctxt prop =
    let val thy = Proof_Context.theory_of ctxt
        fun matches thm =
          case Thm.concl_of thm of
            Const (@{const_name Trueprop}, _) $ (Const (@{const_name HOL.eq}, _) $ prop' $ _)
              => Pattern.matches thy (prop',prop)
          | _ => 
              let val _ = warning ("Invalid theorem in " ^
                          "sturm_prop_substs: \n" ^ Pretty.string_of (
                            Syntax.pretty_term ctxt (Thm.concl_of thm)));
               in false
              end
        val thm = find_first matches @{thms sturm_prop_substs};
    in
        thm
    end;

  fun sturm_prop_tac ctxt i thm =
    let val prop = case Thm.prems_of thm of p :: _ => p | _ => Thm.concl_of thm (* FIXME tactic must not access main conclusion *)
        val prop = case prop of Const (@{const_name Pure.prop}, _) $ prop => prop
                                 | _ => prop
        val prop = case prop of Const (@{const_name Pure.conjunction}, _) $ 
                                    (Const (@{const_name Pure.term}, _) $ _) $ prop => prop
                                 | _ => prop
        val prop = case prop of Const (@{const_name Trueprop}, _) $ prop => prop
                                 | _ => prop
        val thm' = find_sturm_prop_thm ctxt prop
    in  case thm' of
          NONE => Seq.empty
        | SOME thm' => EqSubst.eqsubst_tac ctxt [1] [thm'] i thm
    end;

  fun sturm_main_tac ctxt keep_goal i thm =
    let val prop = case Thm.prems_of thm of p :: _ => p | _ => Thm.concl_of thm (* FIXME tactic must not access main conclusion *)
        val prop = case prop of Const (@{const_name Pure.prop}, _) $ prop => prop
                               | _  => prop
        val prop = case prop of Const (@{const_name Pure.conjunction}, _) $ 
                                    (Const (@{const_name Pure.term}, _) $ _) $ prop => prop
                                 | _ => prop
        val tac = case prop of
                Const (@{const_name Trueprop}, _) $
                  (Const (@{const_name HOL.eq}, _) $ 
                    (Const (@{const_name Finite_Set.card}, _) $ _) $ _) 
                  => sturm_card_eq_tac
              | _ => sturm_prop_tac;
    in  ((tac ctxt i
         THEN CONVERSION (sturm_conv ctxt) i
         THEN resolve_tac ctxt @{thms TrueI} i
        ) ORELSE (if keep_goal then all_tac else no_tac)) thm
    end;

    fun convert_meta_spec_tac ctxt = SUBGOAL (fn (goal, i) =>
      let val frees = Term.add_frees goal []  (* FIXME !? *)
      in case frees of
           [_] =>
                let
                  val goal' = Logic.close_form goal
                  val rule = Goal.prove ctxt [] [] (Logic.mk_implies (goal', goal)) (fn _ =>
                     dresolve_tac ctxt @{thms sturm_meta_spec} i THEN assume_tac ctxt i)
                in resolve_tac ctxt [rule] i end
         | _ => no_tac
      end)

    fun sturm_tac ctxt keep_goal = SELECT_GOAL
       (prune_params_tac ctxt
        THEN TRY (Object_Logic.full_atomize_tac ctxt 1)
        THEN TRY (EqSubst.eqsubst_tac ctxt [1] @{thms sturm_imp_conv} 1)
        THEN TRY (convert_meta_spec_tac ctxt 1)
        THEN TRY (Object_Logic.full_atomize_tac ctxt 1)
        THEN sturm_preprocess_tac ctxt 1
        THEN sturm_main_tac ctxt keep_goal 1)

end;
