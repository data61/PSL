(*  Title:      PSL/SeLFiE/src/Eval_Quantifier_Domain.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** signature: QUANTIFIER_DOMAIN  ***)
signature QUANTIFIER_DOMAIN =
sig

val  qtyp_to_qdomain: SeLFiE_Util.qtyp -> Proof.state -> term -> SeLFiE_Util.induct_arguments-> Eval_Parameter.literals;

type domain = Eval_Parameter.literals;

type domains = {
  number: Eval_Parameter.literals,
  path  : Eval_Parameter.literals,
  print : Eval_Parameter.literals,
  ind   : Eval_Parameter.literals,
  arb   : Eval_Parameter.literals,
  rule  : Eval_Parameter.literals
};

datatype inout = In | Out;

val inout_pst_n_trm_n_induct_args_to_domains: inout -> Proof.state -> term -> SeLFiE_Util.induct_arguments -> domains;

val domains_n_qtyp_to_domain: domains -> SeLFiE_Util.qtyp -> domain;

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

(*TODO: Probably, I should avoid calling these mk_all_*_paths too many times.*)
(*      These unnecessary calls probably slow down the SeLFiE interpreter when it processes nested quantifiers.*)
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

val numb_domain = List.tabulate ((*10 is a magic number here*)10, EP.Non_Path o EP.Number): EP.literals;

val map_Non_Path_Print = map (EP.Non_Path o EP.Print);

val tracing' = if true then K () else tracing;

fun qtyp_to_qdomain SU.QInner_Number _   _   _ = numb_domain
  | qtyp_to_qdomain SU.QOuter_Number _   _   _ = numb_domain
  | qtyp_to_qdomain SU.QInner_Path   pst trm _ = mk_all_inner_paths pst trm |> map EP.Inner_Path
  | qtyp_to_qdomain SU.QOuter_Path   pst trm _ = mk_all_outer_paths pst trm |> map EP.Outer_Path
  | qtyp_to_qdomain SU.QInner_Print  pst trm _ = mk_all_inner_prints pst trm |> (fn list => (tracing' ("qtyp_to_qdomain in Quantifier_Domain. The length of list is " ^ Int.toString (length list));list))|> map_Non_Path_Print
  | qtyp_to_qdomain SU.QOuter_Print  pst trm _ = mk_all_outer_prints pst trm |> (fn list => (tracing' ("qtyp_to_qdomain in Quantifier_Domain. The length of list is " ^ Int.toString (length list));list))|> map_Non_Path_Print
  | qtyp_to_qdomain SU.QInd  _   _  (SeLFiE_Util.Induct_Arguments {ons,...})   = map_Non_Path_Print ons
  | qtyp_to_qdomain SU.QArb  _   _  (SeLFiE_Util.Induct_Arguments {arbs,...})  = map_Non_Path_Print arbs
  | qtyp_to_qdomain SU.QRule _   _  (SeLFiE_Util.Induct_Arguments {rules,...}) = map_Non_Path_Print rules;

type domain = Eval_Parameter.literals;

type domains = {
  number: domain,
  path  : domain,
  print : domain,
  ind   : domain,
  arb   : domain,
  rule  : domain
};

datatype inout = In | Out;

fun inout_pst_n_trm_n_induct_args_to_domains (In: inout) (pst:Proof.state) (trm:term) (induct_args) =
 {number = qtyp_to_qdomain SU.QInner_Number pst trm induct_args: EP.literals,
  path   = qtyp_to_qdomain SU.QInner_Path   pst trm induct_args: EP.literals,
  print  = qtyp_to_qdomain SU.QInner_Print  pst trm induct_args: EP.literals,
  ind    = qtyp_to_qdomain SU.QInd          pst trm induct_args: EP.literals,
  arb    = qtyp_to_qdomain SU.QArb          pst trm induct_args: EP.literals,
  rule   = qtyp_to_qdomain SU.QRule         pst trm induct_args: EP.literals}: domains
  | inout_pst_n_trm_n_induct_args_to_domains (Out: inout) (pst:Proof.state) (trm:term) (induct_args) =
 {number = qtyp_to_qdomain SU.QOuter_Number pst trm induct_args: EP.literals,
  path   = qtyp_to_qdomain SU.QOuter_Path   pst trm induct_args: EP.literals,
  print  = qtyp_to_qdomain SU.QOuter_Print  pst trm induct_args: EP.literals,
  ind    = qtyp_to_qdomain SU.QInd          pst trm induct_args: EP.literals,
  arb    = qtyp_to_qdomain SU.QArb          pst trm induct_args: EP.literals,
  rule   = qtyp_to_qdomain SU.QRule         pst trm induct_args: EP.literals}: domains;

fun domains_n_qtyp_to_domain (domains:domains) SU.QOuter_Path   = #path   domains
  | domains_n_qtyp_to_domain (domains:domains) SU.QInner_Path   = #path   domains
  | domains_n_qtyp_to_domain (domains:domains) SU.QOuter_Print  = #print  domains
  | domains_n_qtyp_to_domain (domains:domains) SU.QInner_Print  = #print  domains
  | domains_n_qtyp_to_domain (domains:domains) SU.QOuter_Number = #number domains
  | domains_n_qtyp_to_domain (domains:domains) SU.QInner_Number = #number domains
  | domains_n_qtyp_to_domain (domains:domains) SU.QInd          = #ind    domains
  | domains_n_qtyp_to_domain (domains:domains) SU.QArb          = #arb    domains
  | domains_n_qtyp_to_domain (domains:domains) SU.QRule         = #rule   domains

end;