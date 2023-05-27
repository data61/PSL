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
val mk_pst_to_prove_from_term        : Proof.context -> term -> Proof.state;
val mk_unbound_bound_vars_free_vars  : Proof.context -> term -> term;
val get_lemma_names_from_sh_output   : theory -> string -> strings;
val assume_cnjctrs_in_pst            : (string * term) list -> Proof.state -> Proof.state;
val is_thm_registered                : Proof.context -> string -> bool;
val mk_new_lemma_name                : Proof.context -> string;

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

fun mk_pst_to_prove_from_term (ctxt:Proof.context) (term:term) =
    let
      val prop = if is_prop term then term else HOLogic.mk_Trueprop term;
    in
      Proof.theorem NONE (K I) [[(prop, [])]] ctxt: Proof.state
    end;

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
    val filtered      = filter (String.isPrefix "top_down_lemma_") strings: strings;
in
    filtered
end;

(*TODO: FIXME: how? Proof.assume?*)
fun assume_cnjctrs_in_pst (name_term_pairs: (string * term) list) (pst:Proof.state): Proof.state =
  Proof.map_context (TBC_Utils.assume_terms_in_ctxt name_term_pairs) pst;

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

end;