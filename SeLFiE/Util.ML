(*  Title:      PSL/SeLFiE/src/Preprocessor/Util.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Helper functions for SeLFiE.
*)

(*** signature SELFIE_UTIL ***)
signature SELFIE_UTIL =
sig

val max_int: int;

val same_strings_when_normalized: Proof.context -> string -> string -> bool;

val ctxt_n_string_to_cname: Proof.context -> string -> string option;

(*arguments passed to the induct method*)
datatype induct_arguments = Induct_Arguments of {ons: strings, arbs: strings, rules: strings};
val dest_induct_arguments     : induct_arguments  -> {ons: strings, arbs: strings, rules: strings};
val induct_arguments_to_string: induct_arguments -> string;
val ord_induct_arguments      : induct_arguments * induct_arguments -> order;
val sort_induct_argumentss    : induct_arguments list -> induct_arguments list;

datatype qtyp = QOuter_Path | QInner_Path | QOuter_Print | QInner_Print | QOuter_Number | QInner_Number | QInd | QArb | QRule;

val print_qtyp: qtyp -> string;

datatype atomic_assert =
(*Eval_Node*)
  Node_Is_Cnst
| Node_Is_Free
| Node_Is_Var
| Node_Is_Bound
| Node_Is_Lambda
| Node_Is_App
| Is_Rule_Of_Node
| Node_Is_Defined_With
| Node_Takes_N_Arguments
| Node_Takes_Less_Than_N_Arguments
| Node_Is_Defined_With_N_Clauses
(*Eval_Unode*)
| Has_Same_Prnt_As
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Nth_Child
| Is_N_Plus_One_th_Child
| Is_Root_In_A_Location
(*Eval_Print*)
| Are_Same_Prints
| Is_Subprint_Of
| Is_Nth_Induct
| Is_Nth_Arbitrary
| Is_Induct
| Is_Arbitrary
| Is_Rule
| Is_Rule_Of_Print
(*Eval_Print for node*)
| Print_Is_Cnst
| Print_Is_Free
| Print_Is_Var
| Print_Is_Bound
| Print_Is_Lambda
| Print_Is_App
| Print_Is_Defined_With
| Print_Is_Defined_With_N_Clauses
| Print_Takes_N_Arguments
| Print_Takes_Less_Than_N_Arguments
(*Eval_Path*)
| Unode_Has_Print
| Is_In_Subgoal
| Is_In_Chained_Fact
| Is_In_Nth_Subgoal
| Is_In_Nth_Chained_Fact
| Are_In_Same_Location
| Is_Parent_Of
| Is_Path_Above
| Is_Same_Path_As
| Is_An_Argument_Of
| Is_An_Argument_Or_Below_Argument_Of
| Is_Nth_Child_Or_Below_Nth_Child_Of
| Is_Below_N_Plus_One_th_Child_Of
| Is_Nth_Argument_Of
| Is_Nth_Argument_Or_Below_Nth_Argument_Of
| Is_A_Meta_Premise
| Is_A_Meta_Conclusion
| Is_A_Meta_Premise_Or_Below
| Is_A_Meta_Conclusion_Or_Below
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Less_Than_By_One
(*debug*)
| Debug_Non_Path_Literal
| Debug_Print_Unode
| Dummy;

val print_atomic_assert: atomic_assert -> string;

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

val print_assert: assert -> string;

val rule_to_const_name: Proof.context -> string -> string;

val ctxt_n_cname_to_definitions: Proof.context -> string -> terms;

val pst_n_cname_to_definitions: Proof.state -> string -> terms;

val ctxt_n_cname_to_number_of_defining_clauses: Proof.context -> string -> int;

end;

(*** structure SeLFiE_Util ***)
structure SeLFiE_Util: SELFIE_UTIL =
struct

val max_int = 10: int;

fun same_strings_when_normalized (ctxt:Proof.context) st1 st2 =
  let
    val normalize          = Isabelle_Utils.normalize_trm_as_string ctxt;
    val (norm_p1, norm_p2) = apply2 (try normalize) (st1, st2);
  in
    Utils.opt_equal (norm_p1, norm_p2)
  end;

infix isSubstring;

fun ctxt_n_string_to_cname  (ctxt:Proof.context) (str:string) =
  let
    val trm_option = try (Syntax.read_term ctxt) str           : term   option;
    val trm_cname  = trm_option >>= try Term.dest_Const <$> fst: string option;
  in
    trm_cname
  end;

(*arguments passed to the induct method*)
datatype induct_arguments = Induct_Arguments of {ons: strings, arbs: strings, rules: strings};
fun dest_induct_arguments (Induct_Arguments arguments) = arguments;

fun induct_arguments_to_string (Induct_Arguments {ons, arbs, rules}) =
  let
    val ons'  = map (enclose "\"" "\"") ons;
    val on    = String.concatWith " " ons': string;
    val arb   = if null arbs  then "" else " arbitrary:" ^ String.concatWith " " arbs : string;
    val rule  = if null rules then "" else " rule:"      ^ String.concatWith " " rules: string;
    val apply = "(induct " ^ on ^ arb ^ rule ^ ")"
  in
    apply
  end;

fun numb_of_args (Induct_Arguments {ons, arbs, rules}) = length ons + length arbs + length rules: int;

fun ord_induct_arguments (args1, args2) = (Int.compare (numb_of_args args1, numb_of_args args2)): order;

fun sort_induct_argumentss (induct_argumentss:induct_arguments list) = sort ord_induct_arguments induct_argumentss
  : induct_arguments list;

datatype qtyp = QOuter_Path | QInner_Path | QOuter_Print | QInner_Print | QOuter_Number | QInner_Number | QInd | QArb | QRule;

fun print_qtyp QOuter_Path = "QOuter_Path"
  | print_qtyp QInner_Path = "QInner_Path"
  | print_qtyp QOuter_Print = "QOuter_Print"
  | print_qtyp QInner_Print = "QInner_Print"
  | print_qtyp QOuter_Number = "QOuter_Number"
  | print_qtyp QInner_Number = "QInner_Number"
  | print_qtyp QInd = "QInd"
  | print_qtyp QArb = "QArb"
  | print_qtyp QRule = "QRule";


datatype atomic_assert =
(*Eval_Node*)
  Node_Is_Cnst
| Node_Is_Free
| Node_Is_Var
| Node_Is_Bound
| Node_Is_Lambda
| Node_Is_App
| Is_Rule_Of_Node
| Node_Is_Defined_With
| Node_Takes_N_Arguments
| Node_Takes_Less_Than_N_Arguments
| Node_Is_Defined_With_N_Clauses
(*Eval_Unode*)
| Has_Same_Prnt_As
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Nth_Child
| Is_N_Plus_One_th_Child
| Is_Root_In_A_Location
(*Eval_Print*)
| Are_Same_Prints
| Is_Subprint_Of
| Is_Nth_Induct
| Is_Nth_Arbitrary
| Is_Induct
| Is_Arbitrary
| Is_Rule
| Is_Rule_Of_Print
(*Eval_Print for node*)
| Print_Is_Cnst
| Print_Is_Free
| Print_Is_Var
| Print_Is_Bound
| Print_Is_Lambda
| Print_Is_App
| Print_Is_Defined_With
| Print_Is_Defined_With_N_Clauses
| Print_Takes_N_Arguments
| Print_Takes_Less_Than_N_Arguments
(*Eval_Path*)
| Unode_Has_Print
| Is_In_Subgoal
| Is_In_Chained_Fact
| Is_In_Nth_Subgoal
| Is_In_Nth_Chained_Fact
| Are_In_Same_Location
| Is_Parent_Of
| Is_Path_Above
| Is_Same_Path_As
| Is_An_Argument_Of
| Is_An_Argument_Or_Below_Argument_Of
| Is_Nth_Child_Or_Below_Nth_Child_Of
| Is_Below_N_Plus_One_th_Child_Of
| Is_Nth_Argument_Of
| Is_Nth_Argument_Or_Below_Nth_Argument_Of
| Is_A_Meta_Premise
| Is_A_Meta_Conclusion
| Is_A_Meta_Premise_Or_Below
| Is_A_Meta_Conclusion_Or_Below
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Less_Than_By_One
(*debug*)
| Debug_Non_Path_Literal
| Debug_Print_Unode
| Dummy;

fun(*Eval_Node*)
    print_atomic_assert (Node_Is_Cnst                              ) = "Node_Is_Cnst"
  | print_atomic_assert (Node_Is_Free                              ) = "Node_Is_Free"
  | print_atomic_assert (Node_Is_Var                               ) = "Node_Is_Var"
  | print_atomic_assert (Node_Is_Bound                             ) = "Node_Is_Bound"
  | print_atomic_assert (Node_Is_Lambda                            ) = "Node_Is_Lambda"
  | print_atomic_assert (Node_Is_App                               ) = "Node_Is_App"
  | print_atomic_assert (Node_Takes_Less_Than_N_Arguments          ) = "Node_Takes_Less_Than_N_Arguments"
  | print_atomic_assert (Node_Is_Defined_With                      ) = "Node_Is_Defined_With"
  | print_atomic_assert (Node_Is_Defined_With_N_Clauses            ) = "Node_Is_Defined_With_N_Clauses"
  | print_atomic_assert (Is_Rule_Of_Node                           ) = "Is_Rule_Of_Node"
  | print_atomic_assert (Node_Takes_N_Arguments                    ) = "Takes_N_Arguments"
  | print_atomic_assert (Has_Same_Prnt_As                          ) = "Has_Same_Prnt_As"
  | print_atomic_assert (Is_Deeper_Than                            ) = "Is_Deeper_Than"
  | print_atomic_assert (Is_Shallower_Than                         ) = "Is_Shallower_Than"
  | print_atomic_assert (Is_Nth_Child                              ) = "Is_Nth_Child"
  | print_atomic_assert (Is_N_Plus_One_th_Child                    ) = "Is_N_Plus_One_th_Child"
  | print_atomic_assert (Is_Root_In_A_Location                     ) = "Is_Root_In_A_Location"
  | print_atomic_assert (Are_Same_Prints                           ) = "Are_Same_Prints"
  | print_atomic_assert (Is_Subprint_Of                            ) = "Is_Subprint_Of"
  | print_atomic_assert (Unode_Has_Print                           ) = "Unode_Has_Print"
  | print_atomic_assert (Is_In_Subgoal                             ) = "Is_In_Subgoal"
  | print_atomic_assert (Is_In_Chained_Fact                        ) = "Is_In_Chained_Fact"
  | print_atomic_assert (Is_In_Nth_Subgoal                         ) = "Is_In_Nth_Subgoal"
  | print_atomic_assert (Is_In_Nth_Chained_Fact                    ) = "Is_In_Nth_Chained_Fact"
  | print_atomic_assert (Are_In_Same_Location                      ) = "Are_In_Same_Location"
  | print_atomic_assert (Is_Parent_Of                              ) = "Is_Parent_Of"
  | print_atomic_assert (Is_Path_Above                             ) = "Is_Path_Above"
  | print_atomic_assert (Is_Same_Path_As                           ) = "Is_Same_Path_As"
  | print_atomic_assert (Is_An_Argument_Of                         ) = "Is_An_Argument_Of"
  | print_atomic_assert (Is_An_Argument_Or_Below_Argument_Of       ) = "Is_An_Argument_Or_Below_Argument_Of"
  | print_atomic_assert (Is_Nth_Child_Or_Below_Nth_Child_Of        ) = "Is_Nth_Child_Or_Below_Nth_Child_Of"
  | print_atomic_assert (Is_Below_N_Plus_One_th_Child_Of           ) = "Is_Below_N_Plus_One_th_Child_Of"
  | print_atomic_assert (Is_Nth_Argument_Of                        ) = "Is_Nth_Argument_Of"
  | print_atomic_assert (Is_Nth_Argument_Or_Below_Nth_Argument_Of  ) = "Is_Nth_Arg_Or_Below_Nth_Arg_Of"
  | print_atomic_assert (Is_A_Meta_Premise                         ) = "Is_A_Meta_Premise"
  | print_atomic_assert (Is_A_Meta_Conclusion                      ) = "Is_A_Meta_Conclusion"
  | print_atomic_assert (Is_A_Meta_Premise_Or_Below                ) = "Is_A_Meta_Premise"
  | print_atomic_assert (Is_A_Meta_Conclusion_Or_Below             ) = "Is_A_Meta_Conclusion"
  | print_atomic_assert (Are_Same_Number                           ) = "Are_Same_Number"
  | print_atomic_assert (Is_Less_Than                              ) = "Is_Less_Than"
  | print_atomic_assert (Is_Less_Than_By_One                       ) = "Is_Less_Than_By_One"
  | print_atomic_assert (Is_Nth_Induct                             ) = "Is_Nth_Induct"
  | print_atomic_assert (Is_Nth_Arbitrary                          ) = "Is_Nth_Arbitrary"
  | print_atomic_assert (Is_Induct                                 ) = "Is_Induct"
  | print_atomic_assert (Is_Arbitrary                              ) = "Is_Arbitrary"
  | print_atomic_assert (Is_Rule                                   ) = "Is_Rule"
  | print_atomic_assert (Is_Rule_Of_Print                          ) = "Is_Rule_Of_Print"
  (*Eval_Print for node*)
  | print_atomic_assert (Print_Is_Cnst                             ) = "Print_Is_Cnst"
  | print_atomic_assert (Print_Is_Free                             ) = "Print_Is_Free"
  | print_atomic_assert (Print_Is_Var                              ) = "Print_Is_Var"
  | print_atomic_assert (Print_Is_Bound                            ) = "Print_Is_Bound"
  | print_atomic_assert (Print_Is_Lambda                           ) = "Print_Is_Lambda"
  | print_atomic_assert (Print_Is_App                              ) = "Print_Is_App"
  | print_atomic_assert (Print_Is_Defined_With                     ) = "Print_Is_Defined_With"
  | print_atomic_assert (Print_Is_Defined_With_N_Clauses           ) = "Print_Is_Defined_With_N_Clauses"
  | print_atomic_assert (Print_Takes_N_Arguments                   ) = "Print_Takes_N_Arguments"
  | print_atomic_assert (Print_Takes_Less_Than_N_Arguments         ) = "Print_Takes_Less_Than_N_Arguments"
  | print_atomic_assert (Debug_Non_Path_Literal                    ) = "Debug_Non_Path_Literal"
  | print_atomic_assert (Debug_Print_Unode                         ) = "Debug_Print_Unode"
  | print_atomic_assert (Dummy                                     ) = "Dummy";

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

fun print_assert Not   = "Not"
  | print_assert And   = "And"
  | print_assert Or    = "Or"
  | print_assert Nor   = "Nor"
  | print_assert Imply = "Imply"
  | print_assert Ands  = "Ands"
  | print_assert Ors   = "Ors"
  | print_assert (Atomic ass) = "Atomic " ^   print_atomic_assert ass ^ " "

datatype non_path_literal =
  Bool    of bool
| Print   of string
| Number  of int
| Command of Pattern.command;

datatype 'path literal = Path of 'path | Non_Path of non_path_literal;

type 'path literals = 'path literal list;

fun split_using_period x = String.tokens (fn splitter => splitter = #".") x;

fun rule_to_const_name (ctxt:Proof.context) (rule_name:string) =
  try split_using_period rule_name
<$> Utils.init
<$> String.concatWith "."
>>= try (Syntax.read_term ctxt)
>>= try Term.dest_Const
<$> fst
 |> (fn opt => Option.getOpt (opt, "fake_name"));

local

fun ctxt_n_cname_to_definition_for_def (ctxt:Proof.context) (cname:string) (suffix:string) =
  try (Proof_Context.get_thms ctxt) (cname ^ suffix) |> these |> map Thm.prop_of;

fun get_definitions_using_suffix (ctxt:Proof.context) (cname:string) (suffix:string) =
   try (Proof_Context.get_thms ctxt) (cname ^ "." ^ suffix)
|> these
|> map Thm.prop_of;

fun ctxt_n_cname_to_definitions_for_inductive (ctxt:Proof.context) (cname:string) =
   get_definitions_using_suffix ctxt cname "intros": terms;

fun ctxt_n_cname_to_definitions_for_primrec (ctxt:Proof.context) (cname:string) =
   get_definitions_using_suffix ctxt cname "simps": terms;

val ctxt_n_cname_to_definitions_for_fun = ctxt_n_cname_to_definitions_for_primrec;

fun ctxt_n_cname_to_definitions_for_function (ctxt:Proof.context) (cname:string) =
   get_definitions_using_suffix ctxt cname "psimps"
|> map Logic.strip_imp_concl: terms;

in

fun ctxt_n_cname_to_definitions (ctxt:Proof.context) (cname:string) :terms =
  let
    val command = Pattern.get_command ctxt cname;
    fun command_to_definitions Pattern.Definition = ctxt_n_cname_to_definition_for_def        ctxt cname "_def"
      | command_to_definitions Pattern.Fun        = ctxt_n_cname_to_definitions_for_fun       ctxt cname
      | command_to_definitions Pattern.Primrec    = ctxt_n_cname_to_definitions_for_primrec   ctxt cname
      | command_to_definitions Pattern.Function   = ctxt_n_cname_to_definitions_for_function  ctxt cname
      | command_to_definitions Pattern.Inductive  = ctxt_n_cname_to_definitions_for_inductive ctxt cname
      (*TODO: Inductive_Set*)
      | command_to_definitions Pattern.Inductive_Set  = ctxt_n_cname_to_definitions_for_inductive ctxt cname
      | command_to_definitions Pattern.Unknown    = [];
  in
    command_to_definitions command: terms
  end;

fun pst_n_cname_to_definitions (pst:Proof.state) (cname:string) =
  let
    val ctxt        = Proof.context_of pst                  : Proof.context;
    val definitions = ctxt_n_cname_to_definitions ctxt cname: terms;
  in
    definitions:terms
  end;

fun ctxt_n_cname_to_number_of_defining_clauses (ctxt:Proof.context) (cname:string): int =
  let
    val terms = ctxt_n_cname_to_definitions ctxt cname: terms;
  in
    length terms: int
  end;

end;

end;