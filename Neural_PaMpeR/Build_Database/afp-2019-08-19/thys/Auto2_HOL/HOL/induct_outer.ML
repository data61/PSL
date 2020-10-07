(*
  File: induct_outer.ML
  Author: Bohua Zhan

  Proof language for induction.
*)

signature INDUCT_PROOFSTEPS =
sig
  val add_induct_data: string -> term * thm -> theory -> theory
  val add_typed_induct_data: string -> typ * thm -> theory -> theory
  val get_typed_ind_th: theory -> string -> typ -> thm
  val get_term_ind_th: theory -> string -> term -> thm

  val check_strong_ind_prop: term -> term list * term
  val add_strong_induct_rule: thm -> theory -> theory
  val add_case_induct_rule: thm -> theory -> theory
  val add_prop_induct_rule: thm -> theory -> theory
  val add_var_induct_rule: thm -> theory -> theory
  val add_cases_rule: thm -> theory -> theory
  val add_fun_induct_rule: term * thm -> theory -> theory

  val strong_induct_cmd: string * string list -> Proof.state -> Proof.state
  val apply_induct_hyp_cmd: string list -> Proof.state -> Proof.state
  val case_induct_cmd: string -> Proof.state -> Proof.state
  val prop_induct_cmd: string * string option -> Proof.state -> Proof.state
  val induct_cmd:
      string -> string * string option * string list * string option ->
      Proof.state -> Proof.state
  val is_simple_fun_induct: thm -> bool
  val fun_induct_cmd:
      string * string list * string option -> Proof.state -> Proof.state
end;

structure Induct_ProofSteps : INDUCT_PROOFSTEPS =
struct

structure Data = Theory_Data (
  type T = ((term * thm) list) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge_list (eq_fst (op =))
)

fun add_induct_data str (t, ind_th) =
    Data.map (Symtab.map_default (str, []) (cons (t, ind_th)))

fun add_typed_induct_data str (ty, ind_th) =
    add_induct_data str (Term.dummy_pattern ty, ind_th)

fun get_typed_ind_th thy ind_type ty =
    let
      val typ_can_match =
          can (fn t' => Sign.typ_match thy (type_of t', ty) Vartab.empty)
    in
      case Symtab.lookup (Data.get thy) ind_type of
          NONE => raise Fail (ind_type ^ ": cannot find theorem.")
        | SOME lst =>
          case find_first (fn (t', _) => typ_can_match t') lst of
              NONE => raise Fail (ind_type ^ ": cannot find theorem.")
            | SOME (_, ind_th) => ind_th
    end

fun get_term_ind_th thy ind_type t =
    let
      val data = Symtab.lookup_list (Data.get thy) ind_type

      fun match_data (pat, th) =
          let
            val inst = Pattern.first_order_match thy (pat, t) fo_init
          in
            SOME (Util.subst_thm_thy thy inst th)
          end
          handle Pattern.MATCH => NONE
    in
      case get_first match_data data of
          NONE => raise Fail (ind_type ^ ": cannot find theorem.")
        | SOME ind_th => ind_th
    end

(* Check a strong induction theorem ind_th is of the right form, and
   extract the induction variables and substitution.
 *)
fun check_strong_ind_prop ind_prop =
    let
      fun err str = "Strong induction: " ^ str
      val (cond_ind, concl) =
          ind_prop |> Logic.dest_implies |> apply2 dest_Trueprop

      (* concl must be of form ?P [?vars]. *)
      val err_concl = err "concl of ind_th must be ?P [?vars]."
      val (P, pat_vars) = Term.strip_comb concl
                          handle TERM _ => error err_concl
      val _ = assert (is_Var P andalso forall is_Var pat_vars andalso
                      (dest_Var P |> fst |> fst) = "P") err_concl

      (* cond_ind must be of form !n. P' n --> ?P n. Return the
         substitution pattern P'.
       *)
      val err_ind_hyp = err "cond_ind of ind_th must be !n. P' --> ?P vars."
      fun dest_one_all var body =
          case body of
              Const (c, _) $ Abs (_, _, t) =>
              if c = UtilBase.All_name then subst_bound (var, t)
              else error err_ind_hyp
            | _ => error err_ind_hyp
      val (pat_subst, P_vars) =
          cond_ind |> fold dest_one_all pat_vars |> dest_imp
      val _ = assert (P_vars aconv concl) err_ind_hyp
    in
      (pat_vars, pat_subst)
    end

fun add_strong_induct_rule ind_th thy =
    let
      val name = Util.name_of_thm ind_th
      val ctxt = Proof_Context.init_global thy
      val ind_th' = apply_to_thm (UtilLogic.to_obj_conv_on_horn ctxt) ind_th
      val (pat_var, pat_subst) =
          check_strong_ind_prop (Thm.prop_of ind_th') |> apfst the_single
          handle List.Empty => error "Strong induction: more than one var."
      val ty_var = type_of pat_var
      val _ = writeln (name ^ "\nSubstitution: " ^
                       (Util.string_of_terms_global thy [pat_var, pat_subst]))
    in
      thy |> add_typed_induct_data "strong_induct" (ty_var, ind_th')
    end

fun add_case_induct_rule ind_th thy =
    let
      val init_assum = ind_th |> Thm.prems_of |> hd |> dest_Trueprop
    in
      thy |> add_induct_data "case_induct" (init_assum, ind_th)
    end

fun add_prop_induct_rule ind_th thy =
    let
      val init_assum = ind_th |> Thm.prems_of |> hd |> dest_Trueprop
    in
      thy |> add_induct_data "prop_induct" (init_assum, ind_th)
    end

fun add_var_induct_rule ind_th thy =
    let
      val (P, n) = ind_th |> concl_of' |> Term.dest_comb
      val _ = assert (Term.is_Var P andalso Term.is_Var n)
                     "add_var_induct_rule: concl of ind_th must be ?P ?var"
    in
      thy |> add_typed_induct_data "var_induct" (type_of n, ind_th)
    end

fun add_cases_rule ind_th thy =
    let
      val (P, n) = ind_th |> concl_of' |> Term.dest_comb
      val _ = assert (Term.is_Var P andalso Term.is_Var n)
                     "add_cases_rule: concl of ind_th must be ?P ?var"
    in
      thy |> add_typed_induct_data "cases" (type_of n, ind_th)
    end

fun add_fun_induct_rule (t, ind_th) thy =
    thy |> add_induct_data "fun_induct" (t, ind_th)

(* Obtain the induction statement. *)
fun get_induct_stmt ctxt (filt_A, ind_vars, stmt, arbitrary) =
    case stmt of
        NONE =>
        let
          val (_, (As, C)) = ctxt |> Auto2_State.get_subgoal
                                  |> Util.strip_meta_horn
          val obj_As = As |> map dest_Trueprop |> filter filt_A
          val obj_C = dest_Trueprop C
        in
          (UtilLogic.list_obj_horn (arbitrary, (obj_As, obj_C)))
              |> fold Util.lambda_abstract (rev ind_vars)
        end
      | SOME s =>
        (UtilLogic.list_obj_horn (arbitrary, ([], Syntax.read_term ctxt s)))
            |> fold Util.lambda_abstract (rev ind_vars)

fun apply_simple_induct_th ind_th vars arbitraries prem_only state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val prop = Auto2_State.get_selected ctxt

      val (vars', _) = prop |> Thm.prems_of |> the_single
                            |> Util.strip_meta_horn

      val ind_th =
          ind_th |> apply_to_thm (Conv.binop_conv (UtilLogic.to_meta_conv ctxt))

      val assum = hd (Drule.cprems_of ind_th)
      val ind_th =
          ind_th |> Util.send_first_to_hyps
                 |> fold Thm.forall_elim (map (Thm.cterm_of ctxt) arbitraries)
                 |> fold Thm.forall_intr (map (Thm.cterm_of ctxt) vars')
                 |> Thm.implies_intr assum

      val t' = case Thm.prop_of ind_th of
                   imp $ A $ B => imp $ Util.rename_abs_term vars A $ B
                 | _ => raise Fail "strong_induct_cmd"

      val ind_th = ind_th |> Thm.renamed_prop t'

      val prop = prop |> Auto2_Outer.refine_subgoal_th ind_th
    in
      if prem_only then
        let
          val (_, (As, _)) = prop |> Thm.prems_of |> the_single
                                  |> Util.strip_meta_horn
          val stmt = dest_Trueprop (hd As)
        in
          state |> Proof.map_contexts (Auto2_State.map_head_th (K prop))
                |> Proof.map_contexts (Auto2_State.set_induct_stmt stmt)
                |> Proof.map_contexts (Auto2_State.add_prem_only stmt)
        end
      else
        state |> Proof.map_contexts (Auto2_State.map_head_th (K prop))
    end

fun strong_induct_cmd (s, t) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt
      val var = Syntax.read_term ctxt s

      val arbitraries = map (Syntax.read_term ctxt) t

      val P = get_induct_stmt ctxt (K true, [var], NONE, arbitraries)
      val ind_th = get_typed_ind_th thy "strong_induct" (type_of var)

      val (var_P, var_n) = ind_th |> concl_of' |> Term.dest_comb
      val inst = fold (Pattern.match thy) [(var_P, P), (var_n, var)] fo_init
      val ind_th = Util.subst_thm ctxt inst ind_th
    in
      state |> apply_simple_induct_th ind_th [var] arbitraries true
    end

val arbitrary =
    Scan.option (@{keyword "arbitrary"} |-- Scan.repeat Parse.term)

val _ =
  Outer_Syntax.command @{command_keyword "@strong_induct"}
    "apply strong induction"
    ((Parse.term -- arbitrary) >> (fn (s, t) =>
         Toplevel.proof (fn state => strong_induct_cmd (s, these t) state)))

fun apply_induct_hyp_cmd s state =
    let
      val {context = ctxt, ...} = Proof.goal state

      val ts = Syntax.read_terms ctxt s

      val induct_stmt = Auto2_State.get_last_induct_stmt ctxt
      val stmt = induct_stmt |> the |> mk_Trueprop |> Thm.cterm_of ctxt
                 handle Option.Option =>
                        raise Fail "apply_induct_hyp: no induct_stmt"

      val prop = Auto2_State.get_selected ctxt
      val (_, (As, _)) = prop |> Thm.prems_of |> the_single
                              |> Util.strip_meta_horn
      val _ = assert (member (op aconv) As (Thm.term_of stmt))
                     "apply_induct_hyp: induct_stmt not found among As."
      val cAs = map (Thm.cterm_of ctxt) As

      val th = stmt |> Thm.assume
                    |> apply_to_thm (UtilLogic.to_meta_conv ctxt)
                    |> fold Thm.forall_elim (map (Thm.cterm_of ctxt) ts)
                    |> apply_to_thm (Util.normalize_meta_all_imp ctxt)

      val prems = th |> Thm.prems_of
                     |> map (fn t => Logic.list_implies (As, t))
                     |> map (Thm.cterm_of ctxt)

      val prems_th = (map (Auto2_Outer.auto2_solve ctxt) prems)
                         |> map Util.send_all_to_hyps
      val concl = th |> fold Thm.elim_implies prems_th
                     |> fold Thm.implies_intr (rev cAs)
      val _ = writeln ("Obtained " ^
                       Syntax.string_of_term ctxt (Thm.concl_of concl))
    in
      state |> Proof.map_contexts (
        Auto2_State.map_head_th (Auto2_Outer.have_after_qed ctxt concl))
    end

val _ =
  Outer_Syntax.command @{command_keyword "@apply_induct_hyp"}
    "apply induction hypothesis"
    ((Scan.repeat Parse.term) >> (fn s =>
         Toplevel.proof (fn state => apply_induct_hyp_cmd s state)))

fun solve_goals ind_th pats_opt filt_As state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val (_, (As, _)) = ctxt |> Auto2_State.get_subgoal
                              |> Util.strip_meta_horn
      val use_As = filter filt_As As
      val cAs = map (Thm.cterm_of ctxt) As
      val ind_goals =
          ind_th |> Thm.prems_of
                 |> map (fn t => Logic.list_implies (use_As, t))
                 |> map (Thm.cterm_of ctxt)
                 |> map (UtilLogic.to_meta_conv ctxt)
  in
    case pats_opt of
        NONE =>
        let
          (* Solve the right side, obtain the left side. *)
          fun solve_eq eq =
              Thm.equal_elim (meta_sym eq)
                             (Auto2_Outer.auto2_solve ctxt (Thm.rhs_of eq))

          val ths = ind_goals |> map solve_eq
                              |> map Util.send_all_to_hyps
          val ind_concl = ind_th |> fold Thm.elim_implies ths
                                 |> fold Thm.implies_intr (rev cAs)
          val after_qed = Auto2_Outer.have_after_qed ctxt ind_concl
        in
          state |> Proof.map_contexts (Auto2_State.map_head_th after_qed)
        end
      | SOME pats =>
        let
          (* Create new block with the subgoals *)
          fun after_qed ths prop =
              let
                val ths' =
                    (ind_goals ~~ ths)
                        |> map (fn (eq, th) => Thm.equal_elim (meta_sym eq) th)
                        |> map Util.send_all_to_hyps

                val ind_concl =
                    ind_th |> fold Thm.elim_implies ths'
                           |> fold Thm.implies_intr (rev cAs)
              in
                Auto2_Outer.have_after_qed ctxt ind_concl prop
              end

          val _ = writeln ("Patterns: " ^ Util.string_of_terms ctxt pats)
          val new_frame =
              Auto2_State.multiple_frame (
                pats ~~ map Thm.rhs_of ind_goals, SOME ([], after_qed))
        in
          state |> Proof.map_contexts (Auto2_State.push_head new_frame)
        end
    end

fun case_induct_cmd s state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt

      val start = Syntax.read_term ctxt s
      val ind_th = get_term_ind_th thy "case_induct" start

      (* Obtain list of assumptions *)
      val (_, (_, C)) = ctxt |> Auto2_State.get_subgoal
                             |> Util.strip_meta_horn

      (* Instantiate the induction theorem *)
      val var_P = concl_of' ind_th
      val inst = Pattern.match thy (var_P, dest_Trueprop C) fo_init
      val ind_th = Util.subst_thm_thy thy inst ind_th
    in
      state |> solve_goals ind_th NONE (K true)
    end

val _ =
  Outer_Syntax.command @{command_keyword "@case_induct"} "apply induction"
    (Parse.term >>
        (fn s =>
            Toplevel.proof (fn state => case_induct_cmd s state)))

val for_stmt =
    Scan.option (@{keyword "for"} |-- Parse.term)

fun prop_induct_cmd (s, t) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt

      val start = Syntax.read_term ctxt s

      val ind_th = get_term_ind_th thy "prop_induct" start

      val (var_P, args) = ind_th |> concl_of' |> Term.strip_comb

      val start_As = strip_conj start
      val filt_A = (fn t => not (member (op aconv) start_As t))
      val P = get_induct_stmt ctxt (filt_A, args, t, [])
      val _ = writeln ("Induct statement: " ^ Syntax.string_of_term ctxt P)

      val inst = Pattern.match thy (var_P, P) fo_init

      (* Instantiate the induction theorem *)
      val ind_th = Util.subst_thm_thy thy inst ind_th
    in
      state |> solve_goals ind_th NONE (K true)
    end

val _ =
  Outer_Syntax.command @{command_keyword "@prop_induct"} "apply induction"
    ((Parse.term -- for_stmt) >>
        (fn (s, t) =>
            Toplevel.proof (fn state => prop_induct_cmd (s, t) state)))

(* Given an induction subgoal of the form !!x_i. A_i ==> C, retrieve
   the list of induction patterns.
 *)
fun retrieve_pat ind_vars t =
    let
      val (vars, (_, C)) = Util.strip_meta_horn t
      fun free_to_var t =
          let val (x, T) = Term.dest_Free t in Var ((x,0), T) end
      val pat_vars = map free_to_var vars
      val args = C |> dest_Trueprop |> Util.dest_args
                   |> map (Term.subst_atomic (vars ~~ pat_vars))
    in
      HOLogic.mk_tuple (map mk_eq (ind_vars ~~ args))
    end

fun induct_cmd ind_ty_str (s, t, u, v) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt
      val var = Syntax.read_term ctxt s
      val arbitraries = map (Syntax.read_term ctxt) u

      val filt_A = Util.occurs_frees (var :: arbitraries)
      val P = get_induct_stmt ctxt (filt_A, [var], t, arbitraries)
      val ind_th = get_typed_ind_th thy ind_ty_str (type_of var)

      (* Instantiate the induction theorem *)
      val concl = concl_of' ind_th
      val (var_P, var_n) = Term.dest_comb concl

      val inst = fold (Pattern.match thy) [(var_P, P), (var_n, var)] fo_init
      val ind_th' = Util.subst_thm_thy thy inst ind_th

      val pats =
          case v of
              NONE => NONE
            | _ => SOME (map (retrieve_pat [var]) (Thm.prems_of ind_th))
    in
      state |> solve_goals ind_th' pats (not o filt_A)
    end

val _ =
  Outer_Syntax.command @{command_keyword "@induct"} "apply induction"
    (Parse.term -- for_stmt -- arbitrary -- Scan.option @{keyword "@with"} >>
        (fn (((s, t), u), v) =>
            Toplevel.proof (
              fn state => induct_cmd "var_induct" (s, t, these u, v) state)))

val _ =
  Outer_Syntax.command @{command_keyword "@cases"} "apply induction"
    (Parse.term -- Scan.option @{keyword "@with"} >>
        (fn (s, v) =>
            Toplevel.proof (
              fn state => induct_cmd "cases" (s, NONE, [], v) state)))

fun get_fun_induct_th thy t =
    let
      val ind_th =
          get_term_ind_th thy "fun_induct" (Term.head_of t)
          handle Fail _ =>
                 Global_Theory.get_thm thy (Util.get_head_name t ^ ".induct")
                 handle ERROR _ => raise Fail "fun_induct: cannot find theorem."

      val (_, args) = Term.strip_comb t
      val (_, pat_args) = ind_th |> concl_of' |> Term.strip_comb
      val inst = Util.first_order_match_list thy (pat_args ~~ args) fo_init
    in
      Util.subst_thm_thy thy inst ind_th
    end

fun is_simple_fun_induct ind_th =
    let
      val prems = Thm.prems_of ind_th
    in
      if length prems > 1 then false
      else let
        val (var, (_, C)) = Util.strip_meta_horn (the_single prems)
        val (_, args) = Term.strip_comb (dest_Trueprop C)
      in
        eq_list (op aconv) (var, args)
      end
    end

fun fun_induct_cmd (s, t, u) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt
      val expr = Syntax.read_term ctxt s
      val arbitraries = map (Syntax.read_term ctxt) t

      val ind_th = get_fun_induct_th thy expr
      val (var_P, vars) = ind_th |> concl_of' |> Term.strip_comb
    in
      if is_simple_fun_induct ind_th then
        let
          val _ = assert (is_none u) "fun_induct: simple induction."

          (* Instantiate the induction theorem *)
          val P = get_induct_stmt ctxt (K true, vars, NONE, arbitraries)
          val inst = Pattern.match thy (var_P, P) fo_init
          val ind_th = Util.subst_thm_thy thy inst ind_th
        in
          state |> apply_simple_induct_th ind_th vars arbitraries false
        end
      else
        let
          (* Instantiate the induction theorem *)
          val filt_A = Util.occurs_frees (vars @ arbitraries)
          val P = get_induct_stmt ctxt (filt_A, vars, NONE, arbitraries)
          val inst = Pattern.match thy (var_P, P) fo_init
          val ind_th' = ind_th |> Util.subst_thm_thy thy inst

          val prems = Thm.prems_of ind_th
          val pats = case u of NONE => NONE
                             | SOME _ => SOME (map (retrieve_pat vars) prems)
        in
          state |> solve_goals ind_th' pats (not o filt_A)
        end
    end

val _ =
  Outer_Syntax.command @{command_keyword "@fun_induct"} "apply induction"
    (Parse.term -- arbitrary -- Scan.option @{keyword "@with"} >>
        (fn ((s, t), u) =>
            Toplevel.proof (fn state => fun_induct_cmd (s, these t, u) state)))

end  (* structure Induct_ProofSteps. *)

val add_strong_induct_rule = Induct_ProofSteps.add_strong_induct_rule
val add_case_induct_rule = Induct_ProofSteps.add_case_induct_rule
val add_prop_induct_rule = Induct_ProofSteps.add_prop_induct_rule
val add_var_induct_rule = Induct_ProofSteps.add_var_induct_rule
val add_fun_induct_rule = Induct_ProofSteps.add_fun_induct_rule
val add_cases_rule = Induct_ProofSteps.add_cases_rule
