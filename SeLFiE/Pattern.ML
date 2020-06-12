(*  Title:      PSL/SeLFiE/src/Preprocessor/Pattern.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

ML types and operations to describe patterns of constant definitions in Isabelle/HOL.
*)

(*** signature PATTERN ***)
signature PATTERN =
sig

(** type and operation about command **)
datatype command  = Definition | Fun | Function | Inductive | Inductive_Set | Primrec | Unknown;
val  get_command : Proof.context -> string -> command;
val print_command: command -> string;

end;


(*** structure Pattern ***)
structure Pattern:PATTERN =
struct

structure IU = Isabelle_Utils;

(** type: command **)
datatype command  = Definition | Fun | Function | Inductive | Inductive_Set | Primrec | Unknown;

(** operation: command **)
fun has_rule_with_suffix (ctxt:Proof.context) (cnst_name:string) (suffix:string) =
  can (Proof_Context.get_thms ctxt) (cnst_name ^ "." ^ suffix);

fun has_no_rule_with_suffix (ctxt:Proof.context) (cnst_name:string) (suffix:string) =
  can (Proof_Context.get_thms ctxt) (cnst_name ^ "." ^ suffix) |> not;

fun has_set_member (trm:term) = Term.exists_Const (equal "Set.member" o fst) trm: bool;
fun always_has_set_mbmer (trms: terms) = forall has_set_member trms: bool;
fun is_defined_with_inductive_set (ctxt:Proof.context) (cname:string) =
   try (Proof_Context.get_thms ctxt) (cname ^ ".intros")
|> these
|> map Thm.prop_of
|> always_has_set_mbmer;



val suffix_for_definition = (["_def"], ["cases", "elims", "induct", "pelims", "simps", "intros"]);
val suffix_for_fun =       (["cases", "elims", "induct", "pelims", "simps"], ["inducts", "intros"]);(*The "fun" keyword produces psimps.*)
val suffix_for_function =  (["cases", "pelims", "psimps"], ["elims", "simps", "intros"]);
val suffix_for_primrec =   (["simps"], ["cases", "pelims", "psimps","elims", "intros"]);
val suffix_for_inductive = (["cases", "induct", "inducts", "intros", "simps"], ["pelims", "elims"]);
(*TODO*)val suffix_for_inductive_set = suffix_for_inductive;
(* Note that the "inductive_set" keyword creates "_eq" as well. But it is computationally expensive
 * to check the existence of this sort of derived lemma because we have to use regular expression.
 * Instead of this, we should check the type of this constant. *)

type suffixes = (string list * string list);

fun check_suffix (ctxt:Proof.context) (cnst_name:string) ((haves, donts): suffixes) =
   (map (has_rule_with_suffix ctxt cnst_name) haves @  (map (has_no_rule_with_suffix ctxt cnst_name) donts))
  |> filter_out I
  |> null;

fun get_command (ctxt:Proof.context) (trm_name:string) =
  let
    val check_suffix  = check_suffix ctxt trm_name;
    val is_fun        = check_suffix suffix_for_fun;
    val is_function   = check_suffix suffix_for_function;
    val is_primrec    = check_suffix suffix_for_primrec;
    val is_inductive  = check_suffix suffix_for_inductive;
    val is_definition = check_suffix suffix_for_definition;
    val checks        = [is_primrec, is_fun, is_function, is_inductive, is_definition]: bool list;
  in
    (if checks = [true,  false, false, false, false] then Primrec   else
     if checks = [false, true,  false, false, false] then Fun       else
     if checks = [false, false, true,  false, false] then Function  else
     if checks = [false, false, false, true,  false] andalso is_defined_with_inductive_set ctxt trm_name then Inductive_Set else
     if checks = [false, false, false, true,  false] then Inductive else
     if checks = [false, false, false, false, true ] then Definition else
     Unknown)
  end;

fun print_command Definition    = "Definition"
  | print_command Fun           = "Fun"
  | print_command Function      = "Function"
  | print_command Inductive     = "Inductive"
  | print_command Inductive_Set = "Inductive_Set"
  | print_command Primrec       = "Primrec"
  | print_command Unknown       = "Unknown";

end;