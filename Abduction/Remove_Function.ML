(*
 * Remove_Function.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)

(*** structure Remove_Function ***)
structure Remove_Function: TOP_DOWN_CONJECTURING =
struct

open Top_Down_Util;
open Term_Table_for_Abduction;

fun path_is_app (table:table) (path:ints) = Inner_Path_To_Unode.defined table (path @ [1]);

fun remove_path_in_table (table:table) (app_path:ints) =
  let
    val is_defined           = Inner_Path_To_Unode.defined table app_path: bool;
    val _                    = if is_defined then () else error "remove_function_in_table failed. undefined unique_node.";
    val children_paths       = get_children table app_path                                                       : ints list;
    val children             = map (the o Inner_Path_Table.lookup table) children_paths                          : unode list;
    val children_w_new_paths = map (update_inner_path_of_unode app_path) children                                : unode list;
    val app_removed_tables   = map (update_unode_then_its_ancestors_in_table table app_path) children_w_new_paths: table list;
    val roots                = map (the o Utils.flip Inner_Path_Table.lookup []) app_removed_tables              : unode list;
    val roots_prints         = map #print roots                                                                  : strings;
  in
    roots_prints: strings
  end;

fun remove_function_in_table (table:table) =
  let
    val keys      = Inner_Path_Table.keys table                           : ints list;
    val apps_keys = filter (path_is_app table) keys                       : ints list;
    val results   = map (remove_path_in_table table) apps_keys |> flat: strings;
  in
    results
  end;

fun remove_functions_in_trm (ctxt:Proof.context) (trm:term) =
  let
    val p2u_table    = Inner_Path_To_Unode.pst_n_trm_to_path_to_unode_table (Proof.init ctxt) trm: Inner_Path_To_Unode.path_to_unode_table;
    val cnjctrs_strs = remove_function_in_table p2u_table                                        : strings;
    val cnjctrs      = map (try (Syntax.read_prop ctxt)) cnjctrs_strs |> map the_list |> flat    : terms;
    val simped_cnjctrs = map (simp_non_prop_term ctxt) cnjctrs
  in
    simped_cnjctrs
  end;

open Unique_Node;

fun remove_multiple_occurrences_of_functions (ctxt:Proof.context) (trm:term) =
  let
    val const_names = Term.add_const_names trm []: strings;
    fun rm_a_func_of_name (Const (name, typ) $ arg) (cname:string) =
        if cname = name then arg else (Const (name, typ) $ rm_a_func_of_name arg cname)
      | rm_a_func_of_name (func $ arg) (cname:string) = rm_a_func_of_name func cname $ rm_a_func_of_name arg cname
      | rm_a_func_of_name (Abs (str, typ, subtrm)) (cname:string) = Abs (str, typ, rm_a_func_of_name subtrm cname)
      | rm_a_func_of_name trm _ = trm
    val trms_wo_func = map (rm_a_func_of_name trm) const_names: terms;
    val trms_dummyT  = map Isabelle_Utils.strip_atyp trms_wo_func: terms;
    val new_strs     = map (Isabelle_Utils.trm_to_string ctxt) trms_dummyT: strings;
    val cnjctrs      = Top_Down_Util.read_props ctxt new_strs: terms;
  in
    cnjctrs: terms
  end;

fun top_down_conjectures _ (pst:Proof.state) (trm:term) =
  let
    val ctxt                 = Proof.context_of pst                             : Proof.context;
    val one_less_occ         = remove_functions_in_trm ctxt trm                 : terms;
    val one_less_prnt        = remove_multiple_occurrences_of_functions ctxt trm: terms;
    val cnjctrs              = one_less_occ @ one_less_prnt |> distinct (op =)  : terms;
    val standardized_cnjctrs = map standardize_vnames cnjctrs    : terms;
    val unique_cnjectrs      = distinct (op =) standardized_cnjctrs             : terms;
    val tagged_cnjctrs       = map (pair "remove_function") unique_cnjectrs    : (string * term) list;
  in
    tagged_cnjctrs: (string * term) list
  end;

end;