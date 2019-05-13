(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Util_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Helper functions for LiFtEr.
*)

(*** LiFtEr_Util ***)
structure LiFtEr_Util: LIFTER_UTIL =
struct

type     path   = ints;
(* print: the printed format of a sub-tree in the syntax tree of a term. *)
datatype print  = Print of string;
type     prints = print list;
fun same_prints (Print p1) (Print p2) = p1 = p2;

fun dest_print (Print str) = str;

infix isSubstring;

val (op isSubstring) = uncurry String.isSubstring;

fun is_subprint_of (Print p1) (Print p2) = p2 isSubstring p1;

fun ctxt_n_print_to_cname  (ctxt:Proof.context) (print:print) =
  let
    val trm_option = try dest_print print >>= try (Syntax.read_term ctxt): term   option;
    val trm_cname  = trm_option >>= try Term.dest_Const <$> fst          : string option;
  in
    trm_cname
  end;

datatype induct_on   = Ind_On   of print;
datatype induct_arb  = Ind_Arb  of print;
datatype induct_rule = Ind_Rule of string;
datatype ind_mods    = Ind_Mods of {ons: induct_on list, arbs: induct_arb list, rules: induct_rule list};

fun dest_induct_on   (Ind_On print)    = print;
fun dest_induct_arb  (Ind_Arb print)   = print;
fun dest_induct_rule (Ind_Rule string) = string;

end;