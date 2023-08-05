(*
 * Generalise_Then_Extend.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)

(*** structure Generalise_Then_Extend ***)
structure Generalise_Then_Extend: TOP_DOWN_CONJECTURING =
struct

open Top_Down_Util;

fun extension_for_one_lhs_n_one_func (ctxt:Proof.context) (lhs:term, candidate_args:terms) (candidate_func:term) =
  let
    val lhs_wo_type_consts          = Isabelle_Utils.strip_atyp lhs                                      : term
    val rhses                       = mk_extended_rhses ctxt candidate_args candidate_func               : terms;
    val rhses_wo_type_consts        = map Isabelle_Utils.strip_atyp rhses                                : terms;
    val eq_pairs                    = map (pair lhs_wo_type_consts) rhses_wo_type_consts                 : (term * term) list;
    val eq_pairs_filtered           = map (replace_redundant_compound_subtrm_with_free_var ctxt) eq_pairs: (term * term) list;
    val eqs                         = map HOLogic.mk_eq eq_pairs_filtered                                : terms;
    val standardized_eqs            = map standardize_vnames eqs                                         : terms;
    val distinct_eqs                = distinct (op =) standardized_eqs                                   : terms;
    val eqs_checked                 = check_terms ctxt distinct_eqs                                      : terms;(*Warning: somehow Syntax.read_prop does not work here*)
    val eqs_wo_meaningless_compound = filter_out has_fvar_appearing_only_in_the_same_compound_trm eqs_checked
    val result_as_strings           = map (Isabelle_Utils.trm_to_string ctxt) eqs_wo_meaningless_compound: strings;
    val result_as_terms             = List.mapPartial (try (Syntax.read_prop ctxt)) result_as_strings    : terms;
    val result_wo_type_consts       = map remove_type_consts result_as_terms                             : terms;
  in
    result_wo_type_consts
  end;

fun extension_for_one_lhs (ctxt:Proof.context) (candidate_funcs:terms) (lhs:term, candidate_args:terms) =
   map (extension_for_one_lhs_n_one_func ctxt (lhs:term, candidate_args:terms)) candidate_funcs
|> flat
|> map standardize_vnames
|> distinct (op =);

open Term_Table_for_Abduction;

fun generalise_exactly_one_subterm_str (ctxt:Proof.context) (trm:term) =
  let
    val trm                    = standardize_vnames trm                                        : term;
    val p2u_table              = Inner_Path_To_Unode.pst_n_trm_to_path_to_unode_table (Proof.init ctxt) trm   : table;
    val numb_of_distinct_fvars = numb_of_distinct_fvars trm                                    : int;
    fun mk_new_unode_of_fvar (var_id:int) (path:ints) = new_unode_of_fvar var_id path                         : unode;
    fun unode_is_not_var ({node,...}:unode) = not (Unique_Node.is_NF node orelse
                                                   Unique_Node.is_NV node orelse
                                                   Unique_Node.is_NB node)                                    : bool;
    fun unode_is_not_func ({tag,...}:unode) = (#take_n_params tag = SOME 0) orelse (#take_n_params tag = NONE): bool;
    fun condition_on_unode (unode:unode)    = unode_is_not_var unode andalso unode_is_not_func unode          : bool;
    val all_non_var_paths   = Inner_Path_Table.dest p2u_table |> filter (condition_on_unode o snd) |> map fst : ints list;
    val var_id_n_path_pairs = map (pair numb_of_distinct_fvars) all_non_var_paths                             : (int * ints) list;
    fun abstract_over_one_print (table:table) (var_id:int, path:ints): table =
      let
        val unode     = mk_new_unode_of_fvar var_id path;
        val new_table = update_unode_then_its_ancestors_in_table table path unode;
      in
        new_table
      end;
    val new_tables       = map (abstract_over_one_print p2u_table) var_id_n_path_pairs : table list;
    val roots            = map (the o Utils.flip Inner_Path_Table.lookup []) new_tables: unode list;
    val roots_prints     = map #print roots                                            : strings;
  in
    roots_prints
  end;

fun read_terms ctxt = List.mapPartial (try (Syntax.read_term ctxt)): strings -> terms;

fun generalise_exactly_one_subterm (ctxt:Proof.context) (trm:term): terms =
let
  val result_strs  = generalise_exactly_one_subterm_str ctxt trm: strings;
  val result_terms = read_terms ctxt result_strs                : terms;
in
  result_terms
end;

(*We do not use Isabelle_Utils.get_free_var_names_in_trm here because we do not want to call Utils.remove__s.*)
fun get_free_vars_in_trm' trm = if Term.is_Free trm then [trm] else [];
fun get_free_vars_in_trm  trm = Term.fold_aterms (fn trm => fn acc => get_free_vars_in_trm' trm @ acc |> distinct (op =)) trm [];
fun mk_fvar_of        (i:int) = Free ("var_" ^ Int.toString i, dummyT);
fun mk_fvars          (i:int) = map mk_fvar_of (List.tabulate (i, I));

fun top_down_conjectures (pst:Proof.state) (orig_trm:term) =
  let
    val ctxt                      = Proof.context_of pst                                              : Proof.context;
    val freevars_in_orig          = get_free_vars_in_trm orig_trm                                     : terms;
    val standardized_fvars_in_gen = mk_fvars (length freevars_in_orig + 1)                            : terms;
    val consts                    = get_consts_for_conjecturing ctxt orig_trm                         : terms;
    val equality_pairs            = get_both_sides_of_eqs_in_term orig_trm                            : (term * term) list;
    val cleaned_pairs             = map (apply2 (mk_unbound_bound_vars_free_vars ctxt)) equality_pairs: (term * term) list;
    (*TODO: move this filter to mk_extended_rhses*)
    fun is_nullary_const (Const (_, typ)) = Isabelle_Utils.count_numb_of_args_of_fun_typ typ = 0
      | is_nullary_const  _               = false
    val nullalry_consts = filter is_nullary_const consts

    fun generalise_pairs (lhs: term, rhs: term) =
    let
      val generalised_lhses = generalise_exactly_one_subterm ctxt lhs: terms;
      val generalised_rhses = generalise_exactly_one_subterm ctxt rhs: terms;
      val new_pairs    = map (fn new_lhs => pair new_lhs rhs) (lhs::generalised_lhses)
                       @ map (fn new_lhs => pair new_lhs lhs) (rhs::generalised_rhses)
    in
      new_pairs: (term * term) list
    end;
    val generalised_pairs  = map generalise_pairs cleaned_pairs |> flat;
    fun add_candidate_args (lhs, rhs) = (lhs, distinct (op =) (rhs :: nullalry_consts @ standardized_fvars_in_gen) |> distinct (op =))  : term * term list;
    val candidate_pairs    = map add_candidate_args generalised_pairs                      : (term * term list) list;

    val filtered_pairs     = filter_out (is_Free o fst) candidate_pairs                    : (term * term list) list;

    val extension_eqs      = map (extension_for_one_lhs ctxt consts) filtered_pairs |> flat: terms;
    val checked_eqs        = check_terms ctxt extension_eqs                                : terms;
    val results            = map (pair "generalisation_then_extension") checked_eqs
  in
    results
  end;

end;