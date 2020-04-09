(*  Title:      PSL/SeLFiE/src/Eval_Quantifier_Domain.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** signature: QUANTIFIER_DOMAIN  ***)
signature QUANTIFIER_DOMAIN =
sig

val  qtyp_to_qdomain: SeLFiE_Util.qtyp -> Proof.state -> term -> SeLFiE_Util.induct_arguments-> Eval_Parameter.literals;

end;

(*** structure: Quantifier_Domain ***)
structure Quantifier_Domain: QUANTIFIER_DOMAIN =
struct

structure SU = SeLFiE_Util;
structure EP = Eval_Parameter;

type inner_path_to_node_table = Inner_Path_To_Unode.path_to_unode_table;
type outer_path_to_node_table = Outer_Path_To_Unode.path_to_unode_table;

type print_to_inner_paths_table = Print_To_Inner_Paths.print_to_paths_table;
type print_to_outer_paths_table = Print_To_Outer_Paths.print_to_paths_table;

fun mk_all_inner_paths  pst term = Inner_Path_To_Unode.pst_n_trm_to_path_to_unode_table pst term |> Inner_Path_To_Unode.table_to_paths: UN.inner_paths;
fun mk_all_outer_paths  pst term = Outer_Path_To_Unode.pst_n_trm_to_path_to_unode_table pst term |> Outer_Path_To_Unode.table_to_paths: outer_paths;

fun mk_all_prints pst_n_trm_to_path_to_unode_table path_to_unode_table_to_print_to_paths_table print_to_paths_table_to_prints
    pst term =
  let
    val path_to_node_table   = pst_n_trm_to_path_to_unode_table pst term;
    val print_to_paths_table = path_to_unode_table_to_print_to_paths_table path_to_node_table;
  in
    print_to_paths_table_to_prints print_to_paths_table
  end;

val mk_all_inner_prints = mk_all_prints Inner_Path_To_Unode.pst_n_trm_to_path_to_unode_table Print_To_Inner_Paths.path_to_unode_table_to_print_to_paths_table Print_To_Inner_Paths.print_to_paths_table_to_prints
                        : Proof.state -> term -> strings;
val mk_all_outer_prints = mk_all_prints Outer_Path_To_Unode.pst_n_trm_to_path_to_unode_table Print_To_Outer_Paths.path_to_unode_table_to_print_to_paths_table Print_To_Outer_Paths.print_to_paths_table_to_prints
                        : Proof.state -> term -> strings;

fun pst_n_trm_to_numb_of_paths mk_all_paths (pst:Proof.state) (trm:term) = mk_all_paths pst trm |> length
(*
|> (fn len => (tracing "psn_to_trm_to_numb_of_paths is ";Int.toString len |> tracing;
     tracing ("---term in pst_n_trm_to_numb_of_paths is " ^ Isabelle_Utils.trm_to_string (Proof.context_of pst) trm)
;len))
*): int;

val pst_n_trm_to_numb_of_inner_paths = pst_n_trm_to_numb_of_paths mk_all_inner_prints: Proof.state -> term -> int;
val pst_n_trm_to_numb_of_outer_paths = pst_n_trm_to_numb_of_paths mk_all_outer_prints: Proof.state -> term -> int;

(*TODO: FIXME: This is only for Outer.*)
fun pst_to_numb_of_max_arity (pst:Proof.state) =
  let
    val subgoals      = Isabelle_Utils.pst_to_subgs pst                         : terms;
    val chained_terms = Isabelle_Utils.pstate_to_chained_facts_as_terms pst     : terms;
    val types         = map (fn trm => Term.add_consts trm []) (subgoals @ chained_terms)
                     |> flat |> map snd                                         : typ list;
    val arities       = map Isabelle_Utils.count_numb_of_args_of_fun_typ types  : ints;
    val max_arity_opt = Utils.ints_to_max_option arities: int option            : int option;
    val max_arity     = if is_none max_arity_opt then 0 else the max_arity_opt: int;
  in
    max_arity
  end;

fun pst_n_trm_to_max_numb_inner (pst:Proof.state) (trm:term) = Int.max (pst_n_trm_to_numb_of_inner_paths pst trm, pst_to_numb_of_max_arity pst(*TODO: FIXME: We need this for Inner.*)): int;
fun pst_n_trm_to_max_numb_outer (pst:Proof.state) (trm:term) = Int.max (pst_n_trm_to_numb_of_outer_paths pst trm, pst_to_numb_of_max_arity pst): int;

fun gen_pst_n_trm_to_numb_domain pst_n_trm_to_max_numb (pst:Proof.state) (trm:term) = List.tabulate (pst_n_trm_to_max_numb pst trm, EP.Non_Path o EP.Number): EP.literals;
fun pst_n_trm_to_inner_numb_domain (pst:Proof.state) (trm:term) = gen_pst_n_trm_to_numb_domain pst_n_trm_to_max_numb_inner pst trm: EP.literals;
fun pst_n_trm_to_outer_numb_domain (pst:Proof.state) (trm:term) = gen_pst_n_trm_to_numb_domain pst_n_trm_to_max_numb_outer pst trm: EP.literals;

val map_Non_Path_Print = map (EP.Non_Path o EP.Print);

fun qtyp_to_qdomain SU.QInner_Number pst trm _ = pst_n_trm_to_inner_numb_domain pst trm
  | qtyp_to_qdomain SU.QOuter_Number pst trm _ = pst_n_trm_to_outer_numb_domain pst trm
  | qtyp_to_qdomain SU.QInner_Path   pst trm _ = mk_all_inner_paths pst trm |> map EP.Inner_Path
  | qtyp_to_qdomain SU.QOuter_Path   pst trm _ = mk_all_outer_paths pst trm |> map EP.Outer_Path
  | qtyp_to_qdomain SU.QInner_Print  pst trm _ = mk_all_inner_prints pst trm |> (fn list => (tracing ("qtyp_to_qdomain in Quantifier_Domain. The length of list is " ^ Int.toString (length list));list))|> map_Non_Path_Print
  | qtyp_to_qdomain SU.QOuter_Print  pst trm _ = mk_all_outer_prints pst trm |> (fn list => (tracing ("qtyp_to_qdomain in Quantifier_Domain. The length of list is " ^ Int.toString (length list));list))|> map_Non_Path_Print
  | qtyp_to_qdomain SU.QInd  _   _  (SeLFiE_Util.Induct_Arguments {ons,...})   = map_Non_Path_Print ons
  | qtyp_to_qdomain SU.QArb  _   _  (SeLFiE_Util.Induct_Arguments {arbs,...})  = map_Non_Path_Print arbs
  | qtyp_to_qdomain SU.QRule _   _  (SeLFiE_Util.Induct_Arguments {rules,...}) = map_Non_Path_Print rules

end;