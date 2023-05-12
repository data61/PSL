(*
 * Top_Donw_Util2.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)

(*** Utils ***)
fun rm_typ (Const (str, _))  = Const (str, dummyT)
  | rm_typ (Free  (str, _))  = Free  (str, dummyT)
  | rm_typ (Var   (idx, _))  = Var   (idx, dummyT)
  | rm_typ (Bound  i      )  = Bound i
  | rm_typ (Abs (str, _, t)) = Abs   (str, dummyT, t)
  | rm_typ (tm1 $ tm2)       = rm_typ tm1 $ rm_typ tm2;

fun non_prop_trm_to_dummy_eq (ctxt:Proof.context) (lhs:term) =
  let
(*
    val standardized_lhs = Isabelle_Utils.standardize_vnames lhs: term;
*)
    val new_free_var     = Top_Down_Util.get_fresh_free_var_of_typ_in_trm ctxt dummyT lhs;
    val dummy_eq         = HOLogic.mk_eq (lhs, new_free_var);
    val dummy_eq_prop    = HOLogic.mk_Trueprop dummy_eq;
    val checked_eq       = try (Syntax.check_prop ctxt) dummy_eq_prop;
    val dummy_cterm      = Option.map (Thm.cterm_of ctxt) checked_eq;
    val dummy_thm        = Option.map Thm.trivial dummy_cterm;
  in
    dummy_thm
  end;

fun simp_non_prop_term (ctxt:Proof.context) (trm:term) =
  let
    val dummy_thm            = non_prop_trm_to_dummy_eq ctxt trm: thm option;
    val simplifier           = Basic_Simplifier.simplify ctxt
    val simped_dummy_thm     = Option.mapPartial (try (Isabelle_Utils.timeout_apply (Time.fromSeconds 1) simplifier)) dummy_thm: thm option;
    val simped_fst_goal      = Option.map Thm.concl_of simped_dummy_thm: term option;
    val simped_fst_pair      = Option.mapPartial (try (HOLogic.dest_eq o HOLogic.dest_Trueprop)) simped_fst_goal: (term * term) option;
    val simped_lhs           = Option.map fst simped_fst_pair: term option;
    val possibly_simped_term = if is_some simped_lhs then the simped_lhs else trm: term;
  in
    possibly_simped_term: term
  end;

fun is_in (small:term) (big:term) =
  let
    fun is_in' (small':term) (big':term) =
      if small' = big'
      then true
      else case big' of
          Abs (_, _, middle) => is_in' small' middle
        | mid1 $ mid2 => is_in' small' mid1 orelse is_in' small' mid2
        | _ => false
  in
    is_in' (rm_typ small) (rm_typ big)
  end;

fun strip_outermost_meta_quantifier (trm as (quantifier $ abstraction)) =
   (case quantifier of
      Const ("Pure.all", _) => (case abstraction of
        Abs (var_name, var_type, _) =>
          (let
             val variable = Term.Free (var_name, var_type)
           in (true, Term.betapply (abstraction, variable))
           end)
      | _ => (false, trm))
    | _ => (false, trm))
  | strip_outermost_meta_quantifier trm = (false, trm);

fun strip_outermost_meta_quantifiers (trm:term) =
    let
      val (worked, res) = strip_outermost_meta_quantifier trm
    in
      if worked
      then
        strip_outermost_meta_quantifiers res
      else
        res
    end;

fun mk_extended_rhses (ctxt:Proof.context) (candidate_args:terms) (candidate_func as Const _:term): terms =
  let
   (*TODO: if func does not take explicit functions, filter out non-nullary constants from candidate_args*)
    val candidate_func_wo_type_consts = Top_Down_Util.remove_type_consts candidate_func      : term;
    val candidate_args_wo_type_consts = map Top_Down_Util.remove_type_consts candidate_args  : terms;
    val arg_numb                      = type_of candidate_func |> Term.binder_types |> length: int;
    fun mk_rhses (n:int) (partial_cnjct:term) =
      if n > 0
      then
        let
          val unchecked_partial_terms      = map (fn arg => partial_cnjct $ arg) candidate_args_wo_type_consts: terms;
          val checked_partial_terms        = Top_Down_Util.check_terms ctxt unchecked_partial_terms                         : terms;
          val partial_terms_wo_type_consts = map Top_Down_Util.remove_type_consts checked_partial_terms                     : terms;
          val result                       = map (mk_rhses (n-1)) partial_terms_wo_type_consts |> flat        : terms;
        in
           result
        end
      else [partial_cnjct];
    val rhses = mk_rhses arg_numb candidate_func_wo_type_consts: terms;
    val rhses_wo_type_consts = map Top_Down_Util.remove_type_consts rhses: terms;
    val simped_rhses = map (simp_non_prop_term ctxt) rhses_wo_type_consts;
    val rhses_wo_duplications =  distinct (op =) simped_rhses: terms;
  in
    rhses_wo_duplications |> map Top_Down_Util.remove_type_consts
  end
  | mk_extended_rhses _ _ _ = [];

fun replace_redundant_compound_subtrm_with_free_var' (ctxt:Proof.context) (lhs, rhs) =
  let
    val ((*func*)_, args) = strip_comb lhs: (term * terms);
    val fvars_in_rhs = Isabelle_Utils.get_free_var_names_in_trm rhs: strings;
    fun in_rhs (fvar_name:string) = exists (equal fvar_name) fvars_in_rhs: bool;
    fun has_fvar_that_is_not_in_rhs (arg:term) =
      let
        val fvar_names_in_arg = Isabelle_Utils.get_free_var_names_in_trm arg: strings;
        val result = forall (fn fvar_in_arg => not (in_rhs fvar_in_arg)) fvar_names_in_arg: bool;
      in
        result
      end;
    val compound_args = filter (fn arg => Isabelle_Utils.is_Abs arg orelse Isabelle_Utils.is_App arg) args: terms;
    val args_to_be_abstracted = filter has_fvar_that_is_not_in_rhs compound_args;
    val numb_of_args_to_be_abstracted = length args_to_be_abstracted: int
    val fresh_free_vars = Top_Down_Util.get_fresh_free_vars_of_typ_in_trm ctxt dummyT (lhs $ rhs) numb_of_args_to_be_abstracted: terms;
    val subst = subst_free (args_to_be_abstracted ~~ fresh_free_vars)
    val new_lhs = subst lhs
  in
    (new_lhs, rhs)
  end;

fun is_only_in_subtrm_of (small:term) (subtrm:term) (big:term) =
  let
    val small'  = rm_typ small;
    val subtrm' = rm_typ subtrm;
    val big'    = rm_typ big;
    fun is_only_in_subtrm_of' (big' as Abs (_, _, mid)) =
        if   subtrm' = big'
        then true
        else (is_only_in_subtrm_of' mid)
      | is_only_in_subtrm_of' (big' as mid1 $ mid2) =
        if subtrm' = big'
        then true
        else
            (if (is_only_in_subtrm_of' mid1) then true else not (is_in small' mid1))
          andalso
            (if (is_only_in_subtrm_of' mid2) then true else not (is_in small' mid2))
      | is_only_in_subtrm_of' atom = subtrm' = atom; 
  in
            is_in small'  subtrm'
    andalso is_in subtrm' big'
    andalso is_only_in_subtrm_of' big'
  end;

fun has_fvar_appearing_only_in_the_same_compound_trm (trm:term) =
(* this might be strictly more powerful than replace_redundant_compound_subtrm_with_free_var' *)
let
(*flatten ignores Abs!*)
  val subtrms = Isabelle_Utils.flatten_trm trm |> map rm_typ |> distinct (op =): terms;
  val compound_subtrms = filter (fn subtrm => Isabelle_Utils.is_Abs subtrm orelse Isabelle_Utils.is_App subtrm) subtrms: terms;
  val free_vars = filter is_Free subtrms: terms;
  fun fvar_appears_only_in_the_same_compound_trm (fvar:term) = exists (fn sub => is_only_in_subtrm_of fvar sub trm) compound_subtrms;
  val result = exists fvar_appears_only_in_the_same_compound_trm free_vars
in
  result
end

fun replace_redundant_compound_subtrm_with_free_var ctxt (lhs, rhs) =
   replace_redundant_compound_subtrm_with_free_var' ctxt (lhs, rhs)
|> swap
|> replace_redundant_compound_subtrm_with_free_var' ctxt
|> swap;

fun remove_Trueprop (Abs (name, typ, trm)) = Abs (name, typ, remove_Trueprop trm)
  | remove_Trueprop (Const ("HOL.Trueprop", _) $ trm2) = remove_Trueprop trm2
  | remove_Trueprop (trm1 $ trm2) = remove_Trueprop trm1 $ remove_Trueprop trm2
  | remove_Trueprop atom = atom;

fun parallel_filter_in_or_out (filter_in:bool) (condition:'a -> bool) (xs:'a list) =
let
  val bools          = Par_List.map condition xs: bool list;
  val pairs          = xs ~~ bools              : ('a * bool) list;
  val filtered_pairs = if filter_in
                       then filter     snd pairs
                       else filter_out snd pairs: ('a * bool) list;
  val result         = map fst filtered_pairs   : 'a list;
in
  result
end;

fun parallel_filter     (condition:'a -> bool) (xs:'a list) = parallel_filter_in_or_out true  condition xs;
fun parallel_filter_out (condition:'a -> bool) (xs:'a list) = parallel_filter_in_or_out false condition xs;

(*** signature TOP_DOWN_CONJECTURING ***)
signature TOP_DOWN_CONJECTURING =
sig

val top_down_conjectures: Proof.context -> term -> (string * term) list;

end;
