(*  Title:      PSL/SeLFiE/src/Preprocessor/Pattern.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

ML types and operations to describe patterns of constant definitions in Isabelle/HOL.
*)

(*** signature PATTERN ***)
signature PATTERN =
sig

(** type and operation about command **)
datatype command                        = Definition | Fun | Function | Inductive | Primrec | Unknown;
val get_command                         : Proof.context -> string -> command;

end;


(*** structure Pattern ***)
structure Pattern:PATTERN =
struct

open Matrix;
structure IU = Isabelle_Utils;

(** type: command **)
datatype command  = Definition | Fun | Function | Inductive | Primrec | Unknown;

(** operation: command **)
fun has_rule_with_suffix (ctxt:Proof.context) (cnst_name:string) (suffix:string) =
  can (Proof_Context.get_thms ctxt) (cnst_name ^ "." ^ suffix);

fun has_no_rule_with_suffix (ctxt:Proof.context) (cnst_name:string) (suffix:string) =
  can (Proof_Context.get_thms ctxt) (cnst_name ^ "." ^ suffix) |> not;

val suffix_for_definition = ([(*"_def"*)], ["cases", "elims", "induct", "pelims", "simps", "intros"]);
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
    val checks        = [is_primrec, is_fun, is_function, is_inductive]: bool list;
  in
    (if checks = [true,  false, false, false] then Primrec   else
     if checks = [false, true,  false, false] then Fun       else
     if checks = [false, false, true,  false] then Function  else
     if checks = [false, false, false, true ] then Inductive else
     Unknown)
  end;

(** type: pattern **)
datatype hol_typ = Fun_Typ | List_Typ | Nat_Typ | Int_Typ | Set_Typ;(*commonly used HOL types*)

(* get_left *)
fun get_left (trm:term): term option =
    try HOLogic.dest_Trueprop trm
>>= try HOLogic.dest_eq
>>= try fst;

(* get_many *)
fun get_many (ctxt:Proof.context) (name:string) (getter:term -> term option) : term list =
   try (Proof_Context.get_thms ctxt) name
|> these
|> map Thm.prop_of
|> map getter
|> Utils.somes;

(* get_lefts *)
fun get_lefts (ctxt:Proof.context) (name:string) = get_many ctxt name get_left: term list;

fun mk_pattern_matrix_for_function (ctxt:Proof.context) (cname:string) =
   try (Proof_Context.get_thms ctxt) (cname ^ ".psimps") |> these
|> map Thm.prop_of
|> map Logic.strip_imp_concl
|> map get_left
|> Utils.somes: terms;

(* mk_pattern_matrix_for_primrec *)
fun mk_pattern_matrix_for_primrec (ctxt:Proof.context) (cname:string) =
   get_lefts ctxt (cname ^ ".simps"): terms;

(* mk_pattern_matrix_for_fun *)
fun mk_pattern_matrix_for_fun (ctxt:Proof.context) (cname:string) = mk_pattern_matrix_for_primrec ctxt cname: terms;;

(* mk_pattern_matrix_for_induct *)
fun mk_pattern_matrix_for_inductive (ctxt:Proof.context) (cname:string) =
   try (Proof_Context.get_thms ctxt) (cname ^ ".intros") |> these
|> map Thm.prop_of
|> map Logic.strip_imp_concl
|> map HOLogic.dest_Trueprop: terms;;

(* mk_pattern_matrix *)
fun mk_pattern_matrix (ctxt:Proof.context) (cname:string) =
  let
    val command = get_command ctxt cname: command;
    val result = case command of
        Primrec   => mk_pattern_matrix_for_primrec   ctxt cname
      | Fun       => mk_pattern_matrix_for_fun       ctxt cname
      | Function  => mk_pattern_matrix_for_function  ctxt cname
      | Inductive => mk_pattern_matrix_for_inductive ctxt cname
      | _(*TODO*) => error "mk_pattern_matrix failed"
  in
    result
  end;

end;