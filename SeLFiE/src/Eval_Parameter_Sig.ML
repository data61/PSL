(*  Title:      PSL/SeLFeE/src/Eval_Parameter_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_PARAMETER =
sig

type path    = LiFtEr_Util.path;
type print   = LiFtEr_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;

datatype parameter =
  Path      of path
| Print     of print
| String    of string(*redundant?*)
| Number    of number
| Int       of int
| Command   of command;

type parameters = parameter list;

type parameter_assert;

type path_to_unode_table = Path_To_Unode.path_to_unode_table;

val trm_n_pst_to_path_to_unode_table: term -> Proof.state -> path_to_unode_table;

val eval: term -> Proof.state -> parameter_assert -> parameters -> Eval_Connective.assert;

end;