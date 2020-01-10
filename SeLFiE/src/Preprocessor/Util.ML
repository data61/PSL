(*  Title:      PSL/SeLFiE/src/Preprocessor/Util.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Helper functions for SeLFiE.
*)

(*** signature SELFIE_UTIL ***)
signature SELFIE_UTIL =
sig

type     inner_path   = ints;
(*print: the printed format of a sub-tree in the syntax tree of a term.*)
datatype print  = Print of string;
type     prints = print list;
val same_prints           : print -> print -> bool;
val same_normalized_prints: Proof.context -> print -> print -> bool;
val inner_path_to_string  : inner_path -> string;

val dest_print           : print -> string;
val is_subprint_of       : print -> print -> bool;
val ctxt_n_print_to_cname: Proof.context -> print -> string option;

(*arguments passed to the induct method*)
datatype induct_arguments = Induct_Arguments of {ons: prints, arbs: prints, rules: prints};
val dest_induct_arguments: induct_arguments  -> {ons: prints, arbs: prints, rules: prints};

end;

(*** structure SeLFiE_Util ***)
structure SeLFiE_Util: SELFIE_UTIL =
struct

type     inner_path   = ints;
(*print: the printed format of a sub-tree in the syntax tree of a term.*)
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

fun inner_path_to_string  []               = ""
  | inner_path_to_string (step::path:ints) = "Path is " ^ Int.toString step ^ path_to_string' path "";

infix isSubstring;

fun is_subprint_of (Print p1) (Print p2) = String.isSubstring p1 p2;

fun ctxt_n_print_to_cname  (ctxt:Proof.context) (print:print) =
  let
    val trm_option = try dest_print print >>= try (Syntax.read_term ctxt): term   option;
    val trm_cname  = trm_option >>= try Term.dest_Const <$> fst          : string option;
  in
    trm_cname
  end;

(*arguments passed to the induct method*)
datatype induct_arguments = Induct_Arguments of {ons: prints, arbs: prints, rules: prints};
fun dest_induct_arguments (Induct_Arguments arguments) = arguments;

end;