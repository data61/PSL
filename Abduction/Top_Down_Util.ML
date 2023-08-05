(*
 * Top_Down_Util.ML
 *
 * Utility functions for our top-down approach, as known as "deep conjecturing".
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
(*** signature TOP_DOWN_UTIL ***)
signature TOP_DOWN_UTIL =
sig

exception NOT_THE_SAME_TERMS;
val standardize_vnames               : term -> term;
val alpha_eq_over_fvar               : term -> term -> bool;
val remove_Trueprop                  : term -> term;
val mk_free_variable_of_typ          : typ -> int -> term;
val numb_of_distinct_fvars           : term -> int;
val numb_of_distinct_bvars           : term -> int;
val get_subtrms                      : term -> terms;
val get_both_sides_of_eqs_in_term    : term -> (term * term) list;
val get_consts_for_conjecturing      : Proof.context -> term -> terms;
val remove_type_consts               : term -> term;
val read_terms                       : Proof.context -> strings -> terms;
val read_props                       : Proof.context -> strings -> terms;
val check_terms                      : Proof.context -> terms -> terms;
val get_fresh_free_var_of_typ_in_trm : Proof.context -> typ -> term -> term;
val get_fresh_free_vars_of_typ_in_trm: Proof.context -> typ -> term -> int -> terms;
val is_prop                          : term -> bool;
val mk_unbound_bound_vars_free_vars  : Proof.context -> term -> term;
val get_lemma_names_from_sh_output   : theory -> string -> strings;
val is_thm_registered                : Proof.context -> string -> bool;
val mk_new_lemma_name                : Proof.context -> string;
val term_compare                     : term * term -> order;

end;

(*** structure Top_Down_Util ***)
structure Top_Down_Util: TOP_DOWN_UTIL =
struct

(* How to standardize variable names to var_n? *)
exception NOT_THE_SAME_TERMS;

fun standardize_vnames' (Free (fvar_name, typ)) (mapping:(string * string) list): term * ((string * string) list) =
(*TODO: check if we have a constant of the same name.*)
    if AList.defined (op =) mapping fvar_name
      then (Free (the (AList.lookup (op =) mapping fvar_name), typ), mapping)
      else (Free ("var_" ^ Int.toString (length mapping), typ),
             (fvar_name, "var_" ^ Int.toString (length mapping))::mapping)
  | standardize_vnames' (Abs (_, typ, trm)) mapping =
      let
        val (new_trm, new_mapping) = standardize_vnames' trm mapping
      in
        (Abs ("", typ, new_trm), new_mapping)
      end
  | standardize_vnames' (trm1 $ trm2) mapping =
      let
        val (new_trm1, new_mapping1) = standardize_vnames' trm1 mapping
        val (new_trm2, new_mapping2) = standardize_vnames' trm2 new_mapping1
      in
        (new_trm1 $ new_trm2, new_mapping2)
      end
  | standardize_vnames' trm mapping = (trm, mapping)

fun standardize_vnames trm = fst (standardize_vnames' trm []);

fun remove_Trueprop (Abs (name, typ, trm)) = Abs (name, typ, remove_Trueprop trm)
  | remove_Trueprop (Const ("HOL.Trueprop", _) $ trm2) = remove_Trueprop trm2
  | remove_Trueprop (trm1 $ trm2) = remove_Trueprop trm1 $ remove_Trueprop trm2
  | remove_Trueprop atom = atom;

fun alpha_eq_over_fvar trm1 trm2 =
  let
    val (non_prop1, non_prop2) = Utils.map_pair remove_Trueprop (trm1, trm2): (term * term);
    val converted1 = standardize_vnames non_prop1
    val converted2 = standardize_vnames non_prop2
  in
    converted1 = converted2
  end;

(* How to make a free variable of a particular type and a name of "var_i"? *)
fun mk_free_variable_of_typ (typ:typ) (i:int) = Free ("var_" ^ Int.toString i, typ);

fun numb_of_distinct_atom (is_atom:term -> bool) (trm:term) =
   Term.fold_aterms (fn t => fn acc => if is_atom t then t :: acc else acc) trm []
|> distinct (op =)
|> length;

fun numb_of_distinct_fvars (trm:term) = numb_of_distinct_atom is_Free trm;

fun numb_of_distinct_bvars (trm:term) = numb_of_distinct_atom is_Bound trm;

(* How to get the list of subterms? *)(*TODO: code-duplication with Proof_Goal_Transformer.*)
fun get_subtrms (Const p:term) = [Const p]
 |  get_subtrms (Free  p:term) = [Free  p]
 |  get_subtrms (Var   p:term) = [Var   p]
 |  get_subtrms (Bound i:term) = [Bound i]
 |  get_subtrms (trm as Abs (_, _, sub)) = trm :: get_subtrms sub
 |  get_subtrms (trm as trm1 $ trm2) = trm :: get_subtrms trm1 @ get_subtrms trm2;

fun get_both_sides_of_eqs_in_term (term:term): (term * term) list =
  let
    val subtrms = get_subtrms term: terms;
    val pairs   = List.mapPartial (try HOLogic.dest_eq) subtrms;
  in
    pairs
  end;

(* How can I find a list of constants used in the definitions of the constants appearing in a term? *)
fun get_consts_for_conjecturing (ctxt:Proof.context) (trm:term) =
  let
    val cnames_in_trm   = Isabelle_Utils.get_cnames_in_trm trm: string list;
    val simp_rules      = map (Find_Theorems2.get_thms_of_name_with_suffix ctxt "simps") cnames_in_trm |> flat;
    val consts_in_simps = map Isabelle_Utils.get_consts_in_thm simp_rules |> flat |> distinct (op =);
  in
    consts_in_simps : terms
  end;

val remove_type_consts = Isabelle_Utils.strip_atyp: term -> term;
fun read_terms ctxt    = List.mapPartial (try (Syntax.read_term ctxt)): strings -> terms;
fun read_props ctxt    = List.mapPartial (try (Syntax.read_prop ctxt)): strings -> terms;
fun check_terms ctxt   = List.mapPartial (try (Syntax.check_term ctxt)): terms -> terms;

fun get_fresh_free_var_name_in_trm' (ctxt:Proof.context) (trm:term) (n:int) =
  let
    val numb_of_fvars = numb_of_distinct_fvars trm + n;
    val fst_candidate = mk_free_variable_of_typ dummyT numb_of_fvars |> dest_Free |> fst: string;
    fun is_free_in_ctxt (name:string) = is_Free (Syntax.read_term ctxt name): bool;
    fun get_all_names_in_trm trm =
        Isabelle_Utils.get_cnames_in_trm trm @ Isabelle_Utils.get_abs_names_in_trm trm @ Isabelle_Utils.get_free_var_names_in_trm trm;
    val all_names_in_trm  = get_all_names_in_trm trm |> distinct (op =): strings;                                                                                                                      
    fun is_fresh (current_candidate:string) = 
        not (member (op =) all_names_in_trm current_candidate) andalso is_free_in_ctxt current_candidate;
    fun add_a_if_taken (current_candidate:string): string =
      if is_fresh current_candidate then current_candidate else add_a_if_taken (current_candidate ^ "a");
    val result = add_a_if_taken fst_candidate: string
  in
    result
  end;

fun is_prop trm = body_type (type_of trm) = @{typ "prop"};

fun get_all_names_in_trm trm =
  Isabelle_Utils.get_cnames_in_trm trm @ Isabelle_Utils.get_abs_names_in_trm trm @ Isabelle_Utils.get_free_var_names_in_trm trm;

fun get_fresh_free_var_name_in_trm' (ctxt:Proof.context) (trm:term) (n:int) =
  let
    val numb_of_fvars = numb_of_distinct_fvars trm + n;
    val fst_candidate = mk_free_variable_of_typ dummyT numb_of_fvars |> dest_Free |> fst: string;
    fun is_free_in_ctxt (name:string) = is_Free (Syntax.read_term ctxt name): bool;
    val all_names_in_trm  = get_all_names_in_trm trm |> distinct (op =): strings;
    fun is_fresh (current_candidate:string) =
        not (member (op =) all_names_in_trm current_candidate) andalso is_free_in_ctxt current_candidate;
    fun add_a_if_taken (current_candidate:string): string =
      if is_fresh current_candidate then current_candidate else add_a_if_taken (current_candidate ^ "a");
    val result = add_a_if_taken fst_candidate: string
  in
    result
  end;

local

fun get_fresh_free_var_of_typ_in_trm' (ctxt:Proof.context) (typ:typ) (trm:term) (n:int) =
  Free (get_fresh_free_var_name_in_trm' ctxt trm n, typ);

in

fun get_fresh_free_var_of_typ_in_trm (ctxt:Proof.context) (typ:typ) (trm:term) =
    get_fresh_free_var_of_typ_in_trm' (ctxt:Proof.context) (typ:typ) (trm:term) (0:int)

fun get_fresh_free_vars_of_typ_in_trm (ctxt:Proof.context) (typ:typ) (trm:term) (n:int) =
    map (get_fresh_free_var_of_typ_in_trm' ctxt typ trm) (List.tabulate (n, I)): terms;

end;

fun strip_all_body_nested (Const ("Pure.all", _) $ Abs (_, _, t)) = strip_all_body_nested t
  | strip_all_body_nested (Abs (str, typ, trm)) = Abs (str, typ, strip_all_body_nested trm)
  | strip_all_body_nested (trm1 $ trm2) = strip_all_body_nested trm1 $ strip_all_body_nested trm2
  | strip_all_body_nested t = t;

fun mk_unbound_bound_vars_free_vars (ctxt:Proof.context) (trm:term) =
  let
    val trm = standardize_vnames trm;
    val stripped_trm = strip_all_body_nested trm;
    val bvars = Term.fold_aterms (fn t => fn acc => if is_Bound t then t :: acc else acc) stripped_trm [];
    val distinct_bvars = distinct (op =) bvars: terms;
    val numb_of_distinct_bvars = length distinct_bvars: int;
    val fvars = get_fresh_free_vars_of_typ_in_trm ctxt dummyT stripped_trm numb_of_distinct_bvars: terms;
    val bvar_fvar_pairs = distinct_bvars ~~ fvars: (term * term) list;
    fun replace_bvar (bvar:term, fvar: term) (trm as Bound _)      = if trm = bvar then fvar else trm
      | replace_bvar  p                      (Abs (str, typ, trm)) = Abs (str, typ, replace_bvar p trm)
      | replace_bvar  p                      (trm1 $ trm2)         = replace_bvar p trm1 $ replace_bvar p trm2
      | replace_bvar  _                       trm                  = trm;
    val result = fold replace_bvar bvar_fvar_pairs trm: term;
  in
    result: term
  end;

fun get_lemma_names_from_sh_output (thy:theory) (sh_output:string) =
  let
    val keywords      = Thy_Header.get_keywords thy                       : Keyword.keywords;
    val tokens        = Token.explode keywords Position.none sh_output    : Token.T list;
    val strings       = map Token.unparse tokens                          : strings;
    fun get_base_name (name:string) = if Long_Name.is_qualified name then Long_Name.base_name name else name;
    val base_names    = map get_base_name strings: strings;
    val filtered      = filter (String.isPrefix "top_down_lemma_") base_names: strings;
in
    filtered
end;

fun is_thm_registered (ctxt:Proof.context) (thm_name:string) = try (Proof_Context.get_thm ctxt) thm_name |> is_some: bool;

fun mk_new_lemma_name (ctxt:Proof.context): string =
  let
    val candidate_name = "top_down_lemma_" ^ Int.toString (serial()): string;
    val this_name_is_already_taken = is_thm_registered ctxt candidate_name;
  in
    if   this_name_is_already_taken
    then mk_new_lemma_name ctxt
    else candidate_name
  end

fun term_compare (trm1, trm2) =
  Term_Ord.term_ord (standardize_vnames trm1, standardize_vnames trm2);

end;


(*** Util2 ***)
fun rm_typ (Const (str, _))  = Const (str, dummyT)
  | rm_typ (Free  (str, _))  = Free  (str, dummyT)
  | rm_typ (Var   (idx, _))  = Var   (idx, dummyT)
  | rm_typ (Bound  i      )  = Bound i
  | rm_typ (Abs (str, _, t)) = Abs   (str, dummyT, t)
  | rm_typ (tm1 $ tm2)       = rm_typ tm1 $ rm_typ tm2;

fun non_prop_trm_to_dummy_eq (ctxt:Proof.context) (lhs:term) =
  let
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

(* mk_pst_to_prove_from_term *)
(*TODO: Don't ignore local assumptions.
        Code-duplication.*)
fun mk_pst_to_prove_from_term (pst:Proof.state) (term:term): Proof.state =
    let 
      val prop = if Top_Down_Util.is_prop term then term else HOLogic.mk_Trueprop term;
    in
      Proof.theorem NONE (K I) [[(prop, [])]] (Proof.context_of pst): Proof.state
    end;

fun mk_pst_to_prove_from_ctxt_n_term (ctxt:Proof.context) (term:term) =
    let
      val prop = if Top_Down_Util.is_prop term then term else HOLogic.mk_Trueprop term;
    in
      Proof.theorem NONE (K I) [[(prop, [])]] ctxt: Proof.state
    end;


(*** signature TOP_DOWN_CONJECTURING ***)
signature TOP_DOWN_CONJECTURING =
sig

val top_down_conjectures: Proof.state -> term -> (string * term) list;

end;
