(*  Title:      PSL/LiFtEr/src/LiFtEr_Util_Struct.ML
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
fun same_normalized_prints (ctxt:Proof.context) (Print p1) (Print p2) =
  let
    val normalize          = Isabelle_Utils.normalize_trm_as_string ctxt;
    val (norm_p1, norm_p2) = apply2 normalize (p1, p2);
  in
    norm_p1 = norm_p2
  end;

fun dest_print (Print str) = str;

fun path_to_string'  []               (acc:string) = acc
  | path_to_string' (step::path:ints) (acc:string)= path_to_string' path (acc ^ "," ^ Int.toString step);

fun path_to_string  []               = ""
  | path_to_string (step::path:ints) = "Path is " ^ Int.toString step ^ path_to_string' path "";

infix isSubstring;

fun is_subprint_of (Print p1) (Print p2) = String.isSubstring p1 p2;

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

fun dest_induct_on   (Ind_On    print            ) = print;
fun dest_induct_arb  (Ind_Arb   print            ) = print;
fun dest_induct_rule (Ind_Rule  string           ) = string;
fun dest_mods        (Ind_Mods {ons, arbs, rules}) = {ons = ons, arbs = arbs, rules = rules};

fun string_to_induct_on   (trm_str:string) = (Ind_On  o Print) trm_str
fun string_to_induct_arb  (trm_str:string) = (Ind_Arb o Print) trm_str;
fun string_to_induct_rule (trm_str:string) = Ind_Rule trm_str;

fun induct_on_to_string   (on:   induct_on)   = (dest_print o dest_induct_on)  on  : string;
fun induct_arb_to_string  (arb:  induct_arb)  = (dest_print o dest_induct_arb) arb : string;
fun induct_rule_to_string (rule: induct_rule) =  dest_induct_rule              rule: string;

end;