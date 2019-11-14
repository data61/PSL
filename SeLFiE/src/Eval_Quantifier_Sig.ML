(*  Title:      PSL/SeLFiE/src/Eval_Quantifier_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_QUANTIFIER =
sig

type parameter;
type parameter_assert;

(* The data-type constructors for boolean operations have to be declared in this signature.
 * because we need them in From_Var_To_Quantifier.*)
datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Eval_Parameter of parameter_assert;

type qtyp(* = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;*)

datatype expr =
  Var     of string
| Lambda  of string * expr
| Apply   of expr   * expr
| Literal of parameter
| Assert  of assert * expr list
| All     of string * qtyp * expr
| Some    of string * qtyp * expr;

val eval: term -> Proof.state -> expr -> expr;

end;

signature QUANTIFIER_DOMAIN =
sig

type qtyp;
type parameter;

val  qtyp_to_qdomain: qtyp -> parameter list;

type path;
type path_to_node_table   = path Path_Table.table;
type print_to_paths_table = path list Print_Table.table;

val mk_all_paths:  Proof.state -> term -> path list;
val mk_all_prints: Proof.state -> term -> LiFtEr_Util.prints;

end;