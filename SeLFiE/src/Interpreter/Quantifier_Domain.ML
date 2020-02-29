(*  Title:      PSL/SeLFiE/src/Eval_Quantifier_Domain.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** signature: QUANTIFIER_DOMAIN  ***)
signature QUANTIFIER_DOMAIN =
sig

type parameter;

val  qtyp_to_qdomain: SeLFiE_Util.qtyp -> Proof.state -> term -> SeLFiE_Util.induct_arguments-> parameter list;

type path;
type path_to_node_table;
type print_to_paths_table;

val mk_all_paths:  Proof.state -> term -> path list;
val mk_all_prints: Proof.state -> term -> strings;

end;

(*** functor: make_Quantifier_Domain  ***)
functor make_Quantifier_Domain
  (structure Print_To_Paths:PRINT_TO_PATHS
         and Path_To_Unode :PATH_TO_UNODE
         and Eval_Variable:EVAL_VARIABLE
   sharing type Eval_Variable.path                 = Path_To_Unode.path
   sharing type Print_To_Paths.path                = Path_To_Unode.path
   sharing type Print_To_Paths.path_to_unode_table = Path_To_Unode.path_to_unode_table): QUANTIFIER_DOMAIN =
struct

structure SU = SeLFiE_Util;

type parameter = Eval_Variable.parameter;

type path                 = Print_To_Paths.path;
type path_to_node_table   = Path_To_Unode.path_to_unode_table;
type print_to_paths_table = Print_To_Paths.print_to_paths_table;

fun mk_all_paths  pst term = Path_To_Unode.pst_n_trm_to_path_to_unode_table pst term |> Path_To_Unode.table_to_paths: path list;

fun mk_all_prints pst term =
  let
    val path_to_node_table   = Path_To_Unode.pst_n_trm_to_path_to_unode_table pst term                      : Path_To_Unode.path_to_unode_table;
    val print_to_paths_table = Print_To_Paths.path_to_unode_table_to_print_to_paths_table path_to_node_table: print_to_paths_table;
  in
    Print_To_Paths.print_to_paths_table_to_prints print_to_paths_table
  end;

fun pst_n_trm_to_numb_of_pahts (pst:Proof.state) (trm:term) = mk_all_paths pst trm |> length
|> (fn len => (tracing "psn_to_trm_to_numb_of_paths is ";Int.toString len |> tracing;
     tracing ("term in pst_n_trm_to_numb_of_paths is " ^ )
;len)): int;

fun pst_to_numb_of_max_arity (pst:Proof.state) =
  let
    val subgoals      = Isabelle_Utils.pst_to_subgs pst                         : terms;
    val chained_terms = Isabelle_Utils.pstate_to_chained_facts_as_terms pst     : terms;
    val types         = map (fn trm => Term.add_consts trm []) (subgoals @ chained_terms)
                     |> flat |> map snd                                         : typ list;
    val arities       = map Isabelle_Utils.count_numb_of_args_of_fun_typ types  : ints;
    val max_arity_opt = Utils.ints_to_max_option arities: int option            : int option;
    val max_arity     = if is_none max_arity_opt   then 0 else the max_arity_opt: int;
  in
    max_arity
  end;

fun pst_n_trm_to_max_numb    (pst:Proof.state) (trm:term) = Int.max (pst_n_trm_to_numb_of_pahts pst trm |> (fn i => ("pst_n_trm_to_numb_of_paths is "^(Int.toString i) |> tracing ; i)), pst_to_numb_of_max_arity pst |> (fn i => (Int.toString i |> tracing ; i))): int;

fun pst_n_trm_to_numb_domain (pst:Proof.state) (trm:term) = List.tabulate (pst_n_trm_to_max_numb pst trm, Eval_Variable.Non_Path o SU.Number): Eval_Variable.parameter list;

val map_Non_Path_Print = map (Eval_Variable.Non_Path o SU.Print);

fun qtyp_to_qdomain SU.QNumber    pst trm _ = pst_n_trm_to_numb_domain pst trm
  | qtyp_to_qdomain SU.QFull_Path pst trm _ = (tracing "qtyp_to_qdomain QFull_Path in Quantifier_Domain";mk_all_paths  pst trm |> (fn list => (tracing ("qtyp_to_qdomain in Quantifier_Domain. The length of list is " ^ Int.toString (length list));list))|> map Eval_Variable.Path)
  | qtyp_to_qdomain SU.QPrint     pst trm _ = (tracing "qtyp_to_qdomain QPrint     in Quantifier_Domain";mk_all_prints pst trm |> (fn list => (tracing ("qtyp_to_qdomain in Quantifier_Domain. The length of list is " ^ Int.toString (length list));list))|> map_Non_Path_Print )
  | qtyp_to_qdomain SU.QInd       _   _  (SeLFiE_Util.Induct_Arguments {ons,...})   = map_Non_Path_Print ons
  | qtyp_to_qdomain SU.QArb       _   _  (SeLFiE_Util.Induct_Arguments {arbs,...})  = map_Non_Path_Print arbs
  | qtyp_to_qdomain SU.QRule      _   _  (SeLFiE_Util.Induct_Arguments {rules,...}) = map_Non_Path_Print rules

end;