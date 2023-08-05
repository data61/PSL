(*
 * Abstract_Same_Term.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)

(*** structure Abstract_Same_Term ***)
structure Abstract_Same_Term: TOP_DOWN_CONJECTURING =
struct

open Top_Down_Util;
open Term_Table_for_Abduction;

fun abstract_same_term_str (ctxt:Proof.context) (trm:term) =
  let
    val trm       = standardize_vnames trm: term;
    val p2u_table = Inner_Path_To_Unode.pst_n_trm_to_path_to_unode_table (Proof.init ctxt) trm;  
    val p2p_table = Print_To_Inner_Paths.path_to_unode_table_to_print_to_paths_table p2u_table;
    val numb_of_distinct_fvars = numb_of_distinct_fvars trm: int;
  
    fun mk_new_unode_of_fvar (var_id:int) (path:ints) = new_unode_of_fvar var_id path: unode;
  
    fun mk_paths_n_unodes_pairs (var_id:int, paths:ints list) = map (fn path => (path, mk_new_unode_of_fvar var_id path)) paths: (ints * unode) list;
  
    fun update_table_for_pair (path:ints, unode:unode) (t:table): table = update_unode_then_its_ancestors_in_table t path unode;
  
    val same_print_paths = Print_Table.dest p2p_table |> map snd: ints list list;
  
    fun unode_is_compound ({node,...}:unode) = Unique_Node.is_NL node orelse Unique_Node.is_NA node: bool;
  
    fun points_to_compound_subtrm (path:ints) =
       Inner_Path_Table.lookup p2u_table path <$> unode_is_compound |> Utils.is_some_true: bool;
  
    fun all_paths_point_to_compound (paths:ints list) = forall points_to_compound_subtrm paths: bool;
  
    val same_compound_print_paths = filter all_paths_point_to_compound same_print_paths: ints list list;
  
    fun powerset (xs:'a list) =
      let
        fun poset ([],    base) = single base
          | poset (y::ys, base) = (poset (ys, base)) @ (poset (ys, y::base))
      in
        poset (xs, [])
      end;
  
    val paths_powerset = powerset same_compound_print_paths: ints list list list;
  
    fun tag_var_id_to_paths_set' _      ([]:ints list list) acc = acc: (int * ints list) list
      | tag_var_id_to_paths_set' var_id (paths::set)        acc = tag_var_id_to_paths_set' (var_id + 1) set (pair var_id paths :: acc);
  
    fun tag_var_id_to_paths_set paths_set = tag_var_id_to_paths_set' numb_of_distinct_fvars paths_set []: (int * ints list) list;
  
    val var_id_n_paths_powerset = map tag_var_id_to_paths_set paths_powerset: (int * ints list) list list;
  
    fun abstract_over_one_print (var_id:int, paths:ints list) (table:table): table =
      let
        val path_n_unode_pairs = mk_paths_n_unodes_pairs (var_id, paths): (ints * unode) list;
      in
        fold update_table_for_pair path_n_unode_pairs table
      end;
  
    fun abstract_over_mult_prints (pairs:(int * ints list) list) = fold abstract_over_one_print pairs p2u_table: table;
    val new_tables       = map abstract_over_mult_prints var_id_n_paths_powerset: table list;
    val roots            = map (the o Utils.flip Inner_Path_Table.lookup []) new_tables: unode list;
    val roots_prints     = map #print roots                                            : strings;
  in
    roots_prints
  end;
  
  fun top_down_conjectures (pst:Proof.state) (trm:term) =
    let
      val ctxt                 = Proof.context_of pst                                                  : Proof.context;
      val cnjctrs_strs         = abstract_same_term_str ctxt trm                                       : strings;
      val cnjctrs              = map (try (Syntax.read_prop ctxt)) cnjctrs_strs |> map the_list |> flat: terms;
      val standardized_cnjctrs = map standardize_vnames cnjctrs                                        : terms;
      val unique_cnjectrs      = distinct (op =) standardized_cnjctrs                                  : terms;
      val tagged_cnjctrs       = map (pair "abstract_same_term)") unique_cnjectrs                      : (string * term) list;
    in
      tagged_cnjctrs
    end;

end;