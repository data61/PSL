(*  Title:      Assertions.ML
    Author:     Yilun He, Data61, CSIRO
                Yutaka Nagashima, CIIRC, CTU
    
    This file stores the written assertions, which can be used to extract features from proof state.

    eval_assertion converts a proof state to a list of real values, which is the feature vector of
    the state.

    Users can add their own assertion as functions of type "thm -> context -> boolean".
*)

(** ASSERT_UTILS: Generic utility and assertion functions to write Assertions. **)
signature ASSERT_UTIL =
sig
type location = Isabelle_Utils.location;
type context  = Proof.context;
val fst_subg_has_const_of                 : thm -> (string -> bool) -> bool;
val all_cnames_satisfy                    : thm -> (string -> bool) -> bool;
val fst_subg_has_const_of_name            : thm -> string -> bool;
val fst_subg_has_const_more_than_n_times  : thm -> string -> int -> bool;
val fst_subg_has_const_prefixed_with      : thm -> string -> bool;
val fst_subg_has_const_of_name_subst      : thm -> string -> bool;
val fst_subg_has_typ_of                   : thm -> (string -> bool) -> bool;
val fst_subg_has_typ_of_name              : thm -> string -> bool;
val fst_subg_has_typ_of_name_subst        : thm -> string -> bool;
val outermost_cname_in_1st_subg_is        : thm -> string -> bool;
val fst_subg_has_cname_not_as_outmost     : thm -> string -> bool;
val has_thms_of_name_with_all_substrings  : context -> string list -> bool;
val has_all_substrings_when_printed       : location -> thm -> context -> string list -> bool;
val has_thms_with_suffixes                : thm -> context -> string list -> bool;
val has_thms_of_lnames_with_suffix        : context -> string list -> string -> bool;
val has_thms_of_cname_with_all_substrs    : thm -> context -> string list -> bool;
val has_thms_of_tname_with_all_substrs    : thm -> context -> string list -> bool;
val is_fun_not_fully_applied              : term -> bool;(*Not very reliable*)
val fst_subg_is_classified_as             : thm -> context -> Spec_Rules.rough_classification -> bool;
val fst_has_one_of_these_consts           : thm -> string list -> bool;
val fst_has_one_of_these_tnames           : thm -> string list -> bool;
val assrt_on_outmost_after_pure_imp_in    : (term -> bool) -> term -> bool;
end;

(** ASSERT_UTILS: Generic utility and assertion functions to write assertions. **)
structure Assert_Util : ASSERT_UTIL =
struct

type location = Isabelle_Utils.location;
type context  = Proof.context;

infix 1 >>= liftM;
fun (m >>= f)   = Option.mapPartial f m;
fun (m liftM f) = Option.map f m;

(* The first subgoal has a constant that satisfies the given assertion. *)
fun fst_subg_has_const_of (goal:thm) (assert:string -> bool) = goal
  |>    Isabelle_Utils.get_1st_subg
  liftM Term.exists_Const (assert o fst)
  |>    Utils.is_some_true: bool;

(* The first subgoal has a constant of the given name. *)
fun fst_subg_has_const_of_name (goal:thm) (name:string) =
  fst_subg_has_const_of goal (equal name): bool;

(* The first subgoal has a constant of the given name more than n times. *)
fun fst_subg_has_const_more_than_n_times (goal:thm) (name:string) (n:int) = goal
  |>    Isabelle_Utils.get_1st_subg
  liftM (fn trm => Isabelle_Utils.add_const_names_mult trm [])
  liftM (Utils.count_str name)
  liftM (fn m => m > n)
  |> Utils.is_some_true:bool;

(* all_cnames_satisfy checks if all constant meet given criteria *)
fun all_cnames_satisfy goal (assert:string -> bool) = 
  let
    val cnames_in_1st_subg = Isabelle_Utils.get_cnames_in_1st_subg goal;
    val holds_for_all      = forall assert cnames_in_1st_subg;
  in holds_for_all:bool end;

(* The first subgoal has a constant that has a name with the given prefix. *)
fun fst_subg_has_const_prefixed_with goal (prefix:string) =
  let
    fun is_prefixed cname = Isabelle_Utils.fst_qualifier cname = prefix;
  in
    fst_subg_has_const_of goal is_prefixed: bool
  end;

(* The first subgoal has a constant that has a name which has the given string as a substring. *)
fun fst_subg_has_const_of_name_subst goal (substr:string) =
  fst_subg_has_const_of goal (String.isSubstring substr);

(* The first subgoal has a term of a type that satisfies the given assertion. *)
fun fst_subg_has_typ_of (goal:thm) (assert:string -> bool) = goal
  |> Isabelle_Utils.get_typ_names_in_1st_subg
  |> exists assert;

(* The first subgoal has a term of the given type name. *)
fun fst_subg_has_typ_of_name (goal:thm) (name:string) =
  fst_subg_has_typ_of goal (equal name);

(* The first subgoal has a term of type that has a name which has the given string as a substring. *)
fun fst_subg_has_typ_of_name_subst (goal:thm) (substr:string) =
  fst_subg_has_typ_of goal (String.isSubstring substr);

(* outermost_cname_in_1st_subg_is checks if the first subgoal has a constant of the given name as the outermost constant. *)
fun outermost_cname_in_1st_subg_is (goal:thm) (cname:string) = SOME goal
  >>=   Isabelle_Utils.get_1st_subg
  >>=   Isabelle_Utils.get_outmost_cname
  liftM equal cname
 |>     Utils.is_some_true: bool;

(* fst_subg_has_cname_not_as_outmost checks if the first subgoal has a constant of the given name, but not as the outermost constant. *)
fun fst_subg_has_cname_not_as_outmost (goal:thm) (cname:string) =
  fst_subg_has_const_of_name goal cname andalso not (outermost_cname_in_1st_subg_is goal cname);

(* is_fun_not_fully_applied checks if the term is a function that is ready to take arguments. *)
fun is_fun_not_fully_applied (trm:term) = Term.type_of trm |> Term.size_of_typ |> equal 1;

(* FIXME: fst_subg_is_classified_as roughly classifies the first subgoal *)
fun fst_subg_is_classified_as  (goal:thm) (ctxt:context) (rclass:Spec_Rules.rough_classification) =
  let
    val fst_subg         = Isabelle_Utils.get_1st_subg goal: term option;
    val classifications  = Option.map (Spec_Rules.retrieve ctxt) fst_subg |> these;
    val rough_classes    = map fst classifications: Spec_Rules.rough_classification list;
    val is_classified_as = exists (equal rclass) rough_classes: bool;
  in
    is_classified_as
  end;

(* has_thms_of_name_with_all_substrings checks if the context contains thms that are named after the base-name of the constant and other strings. *)
fun has_thms_of_name_with_all_substrings (ctxt:context) (substrs:string list) =
  Find_Theorems2.get_thms_of_name_with_these_substrs ctxt substrs |> null |> not: bool;

(* has_thms_of_cname_with_all_substrs check if the context has a thm such that its name consists of the base-name of a constant appearing *)
(* in the first sub-goal and other specified strings. *)
fun has_thms_of_cname_with_all_substrs (goal:thm) (ctxt:context) (strs:string list) =
  let
    val long_cnames    = Isabelle_Utils.get_cnames_in_1st_subg goal: string list;
    fun get_thms lname = Find_Theorems2.get_thms_of_name_with_these_substrs ctxt (Long_Name.base_name lname :: strs);
    val result         = map get_thms long_cnames |> flat |> null |> not;
  in result:bool end;

(* has_thms_of_tname_with_all_substrs checks if the context has a thm such that its name consists *)
(* of the base-name of a constant appearing in the first sub-goal and other specified strings. *)
fun has_thms_of_tname_with_all_substrs (goal:thm) (ctxt:context) (strs:string list) =
  let
    open Isabelle_Utils Utils Find_Theorems2;
    fun get_thms btname = (get_thms_of_name_with_these_substrs ctxt (btname :: strs));
    val result = goal
      |>    get_trm_in Fst_Subg
      liftM get_typ_names_in_trm
      liftM map Long_Name.base_name
      liftM map ((*filter_out (is_in_Main ctxt) o*) get_thms)
      liftM (not o null o flat)
      |>    is_some_true;
  in result : bool end;

(* has_thms_of_lname_with_suffix checks if the current context contains thms that are named after a given constant with a given suffix. *)
fun has_thms_of_lname_with_suffix (ctxt:context) (sfx:string) (cname:string) =
  Find_Theorems2.get_thms_of_name_with_suffix ctxt sfx cname |> null |> not: bool;

(* has_thms_of_cnames_with_suffix is similar to has_thms_of_lname_with_suffix, but with multiple constant names. *)
fun has_thms_of_lnames_with_suffix (ctxt:context) (names:string list) (sfx:string) =
  exists (has_thms_of_lname_with_suffix ctxt sfx) names: bool;

(* has_thms_with_suffixes checks if the context contains thms that are named after a constant in the goal but with one of the given suffixes. *)
fun has_thms_with_suffixes (goal:thm) (ctxt:context) (sfxes:string list) =
  let
    val cnames    = Isabelle_Utils.get_cnames_in_1st_subg goal;
    val typ_names = Isabelle_Utils.get_typ_names_in_1st_subg goal;
    (*FIXME: to reduce the computational cost, assertion should focus on either cnames or type_names.*)
    val names     = cnames @ typ_names;
    val has_thms  = forall (has_thms_of_lnames_with_suffix ctxt names) sfxes;
  in has_thms end:bool;

(* has_all_substrings_when_printed checks if the given list of strings are all appear in the given proof obligation when printed out. *)
fun has_all_substrings_when_printed (wo:Isabelle_Utils.location) (goal:thm) (ctxt:context) (strs:string list) =
  let
    fun all_are_substr (substrs:string list) (fst_g:string) = forall (Utils.flip String.isSubstring fst_g) substrs: bool;
    val result = Isabelle_Utils.get_trm_in wo goal
      liftM Syntax.string_of_term ctxt
      liftM all_are_substr strs
      |>    Utils.is_some_true;
  in result end;

(* has_one_of_these_consts_in_fsg checks if goal:thm has one of the specified constants as a part
   of the first sub-goal. *)
fun fst_has_one_of_these_consts goal (const_names:string list) = goal
  |>    Isabelle_Utils.get_trm_in Isabelle_Utils.Fst_Subg
  liftM Isabelle_Utils.get_cnames_in_trm
  |>    these
  |>    exists (Utils.is_one_of_strings const_names);

(* has_one_of_these_tnames_in_fsg checks if goal:thm has one of the specified type names as a part
   of the first sub-goal. *)
fun fst_has_one_of_these_tnames goal (const_names:string list) = goal
  |>    Isabelle_Utils.get_trm_in Isabelle_Utils.Fst_Subg
  liftM Isabelle_Utils.get_typ_names_in_trm
  |>    these
  |>    exists (Utils.is_one_of_strings const_names);

fun assrt_on_outmost_after_pure_imp_in (assrt:term -> bool) (@{term "Pure.imp"} $ (concl $ prems)) =
      assrt prems orelse
      assrt_on_outmost_after_pure_imp_in assrt concl orelse
      assrt_on_outmost_after_pure_imp_in assrt prems
  | assrt_on_outmost_after_pure_imp_in assrt (trm1 $ trm2) =
      assrt_on_outmost_after_pure_imp_in assrt trm1 orelse
      assrt_on_outmost_after_pure_imp_in assrt trm2
 | assrt_on_outmost_after_pure_imp_in assrt (Abs (_, _, trm)) = assrt_on_outmost_after_pure_imp_in assrt trm
 | assrt_on_outmost_after_pure_imp_in  _ _ = false;

end;

(*** ASSERTIONS ***)
signature ASSERTIONS =
sig
  val eval_assertion_gen        : Proof.state -> (thm -> Proof.context -> thm list -> bool) list -> bool list;
  val eval_assertion_for_ML_real: Proof.state -> real list;
  val eval_assertion_for_ML_bool: Proof.state -> bool list;
  val eval_assertion:             Proof.state -> string;
  val assertions:                 (thm -> Proof.context -> thm list -> bool) list;
  val explanations:               string list;
end;

(*** Assertions: Implementation of assertions ***)
structure Assertions : ASSERTIONS =
struct

structure AU = Assert_Util;

infix 1 >>= liftM;

type context  = Proof.context;

fun (m >>= f)   = Option.mapPartial f m;
fun (m liftM f) = Option.map f m;

(** Assertions about the existence of certain objects (rules) in the proof state **)

(* ASSERT 01. checks if the proof context contains local assumption *)
fun check_local_assms _ ctxt _ = ctxt
  |> Proof_Context.theory_of
  |> Proof_Context.init_global
  |> Assumption.local_assms_of ctxt
  |> null
  |> not;

(* ASSERT 56. check if Proof.state contains local facts such as those chained by the using keyword. *)
fun has_eventually goal _ facts = goal::facts
  |> map Isabelle_Utils.get_trms_in_thm
  |> flat
  |> map (Term.exists_Const (equal "Filter.eventually" o fst))
  |> exists (equal true);

(* ASSERT 05. checks if the proof context contains a "pinduct" rule associated with a constant in the first subgoal. *)
fun fact_pinduct goal ctxt _ = AU.has_thms_with_suffixes goal ctxt ["pinduct"]

(* ASSERT 50. checks if the proof context contains a "induct" rule associated with a constant in the first subgoal. *)
fun fact_induct goal ctxt _ = AU.has_thms_with_suffixes goal ctxt ["induct"]

(* ASSERT 06. checks if the proof context contains a "psimp" rule associated with a constant in the first subgoal. *)
fun fact_psimp   goal ctxt _ = AU.has_thms_with_suffixes goal ctxt ["psimps"]

(* ASSERT 07. checks if the proof context contains a "pelims" rule associated with a constant in the first subgoal. *)
fun fact_pelims  goal ctxt _ = AU.has_thms_with_suffixes goal ctxt ["pelims"]

(* ASSERT 08. checks if the proof context contains a "cases" rule associated with a constant in the first subgoal. *)
fun fact_cases   goal ctxt _ = AU.has_thms_with_suffixes goal ctxt ["cases"]

(* ASSERT 09. check if the proof context contains an "intros" rule associated with a constant in the first subgoal. *)
fun fact_intros  goal ctxt _ = AU.has_thms_with_suffixes goal ctxt ["intros"]

(* ASSERT 10. checks if the proof context contains a recursive simplification rule associated with a constant in the first subgoal. *)
fun check_rec_simp goal ctxt _ =
  let
    val cnames = Isabelle_Utils.get_cnames_in_1st_subg goal;
    fun is_recursive (cname:string) (_ $ (Term.Const ("HOL.eq",_) $ A $ B)) =
      let
         val cname_is_in_lhs = Term.exists_Const (fn (s,_) => cname = s) A;
         val cname_is_in_rhs = Term.exists_Const (fn (s,_) => cname = s) B;
      in cname_is_in_lhs andalso cname_is_in_rhs end
     |  is_recursive _ _ = false;
    fun check_thm_list (thms:thm list) (cname:string) = List.exists (is_recursive cname o Thm.concl_of) thms;
    fun exist_related_rsimp  []             = false
     |  exist_related_rsimp (cname::cnames) = 
         (check_thm_list (Proof_Context.get_thms ctxt (cname^".simps")) cname handle ERROR _ =>
          exist_related_rsimp cnames);
  in
    exist_related_rsimp cnames
  end;

(* ASSERT 12. checks if the proof context contains facts that are generated by the lift_definition *)
(*            command and are associated with a constant in the first subgoal. *)
fun fact_lift_def goal ctxt _ = AU.has_thms_with_suffixes goal ctxt ["abs_eq","rsp","transfer","rep_eq"];

(* ASSERT 13. checks if the proof context contains facts that are generated by the primcorec *)
(*            command and are associated with a constant in the first subgoal. *)
fun fact_primcorec goal ctxt _ = AU.has_thms_with_suffixes goal ctxt ["code","ctr","sel"];

(* ASSERT 57. checks if the proof context contains facts that are generated by the inductive keyword or inductive_set keyword. *)
fun fact_inductive goal ctxt _ = AU.has_thms_with_suffixes goal ctxt [(*"cases", "induct",*) "inducts"(*, "intros", "simps"*)];

(* ASSERT 58. checks if the proof context contains facts that are generated by the fun keyword. *)
fun fact_fun goal ctxt _ = AU.has_thms_with_suffixes goal ctxt [(*"cases", *)"elims"(*, "induct", "pelims", "simps"*)];

(* ASSERT 14. checks if the proof obligation has intro_locales*)
fun is_locale_intro1 goal ctxt _ = AU.has_thms_of_cname_with_all_substrs goal ctxt [".axioms"];

(* ASSERT 43. checks if the proof obligation has intro_locales*)
fun is_locale_intro2 goal ctxt _ = AU.has_thms_of_cname_with_all_substrs goal ctxt ["local.", "_axioms"];

(* ASSERT 53. checks if the proof obligation has a variable of a type that is defined with the datatype command. *)
fun has_datatype_var goal ctxt _ = AU.has_thms_of_tname_with_all_substrs goal ctxt ["rec_transfer"];

(* ASSERT 54. checks if the proof obligation has variable of a type that is defined the datatype command with a parameter. *)
fun has_datatype_var_para goal ctxt _ = AU.has_thms_of_tname_with_all_substrs goal ctxt ["inj_map_strong"];

(* ASSERT 55. checks if the proof obligation has a variable of a type that is defined with the record command. *)
fun has_var_of_rec goal ctxt _ = AU.has_thms_of_tname_with_all_substrs goal ctxt ["Abs_", "_ext_inject"];

(* ASSERT 61. checks if the proof obligation has a variable of a type that is defined with the codatatype command. *)
fun has_var_of_codata goal ctxt _ = AU.has_thms_of_tname_with_all_substrs goal ctxt ["corec_disc"];

(* ASSERT 44. checks if the outermost constant visible to users has a name such that the underlying   *)
(*            proof context has a theorem of name ".base_name_of_the_constant.".                      *)
(*            We expect that this assertion is useful to detect the use of the unfold_locales method. *)
fun is_unfold_locale goal ctxt _ =
  let
    fun get_rules (strs:string list) = Find_Theorems2.all_names_to_rules "" strs ctxt goal: (Find_Theorems2.ref * thm) list;
    val result = goal
      |>    Isabelle_Utils.get_trm_in Isabelle_Utils.Fst_Subg
      >>=   Isabelle_Utils.get_outmost_cname
      liftM Long_Name.base_name
      liftM (fn bname => ["." ^ bname ^ ".", bname ^ "_def", bname ^ "_axioms_def"])
      liftM (forall (not o null o get_rules o single))
      |>    Utils.is_some_true: bool
  in result end;

(* ASSERT 82. checks if the first sub-goal has a constant defined with the fixrec command. *)
fun fact_fixrec (goal:thm) ctxt _ =
 AU.has_thms_with_suffixes goal ctxt ["unfold"];

(* ASSERT 83. checks if the proof obligation has a variable of a type that is defined with the domain command. *)
fun has_domain_var goal ctxt _ = AU.has_thms_of_tname_with_all_substrs goal ctxt ["unfold"];

(* ASSERT 84. disjunction of ASSERT 82. and ASSERT 83. *)
fun fact_fixrec_or_domain goal ctxt _ = fact_fixrec goal ctxt () orelse has_domain_var goal ctxt ();

(* ASSERT 85. checks if the proof context contains a "narrowing...simps" rule associated with a type of variables in the first subgoal. *)
(*We expect that this assertion is useful to detect the use of the nominal_induct method.*)
fun has_nominal_datatype_var1 goal ctxt _ = AU.has_thms_of_tname_with_all_substrs goal ctxt ["narrowing", "simps"];

(* ASSERT 86. checks if the proof context contains a "constr_rep" rule associated with a type of variables in the first subgoal. *)
(*We expect that this assertion is useful to detect the use of the nominal_induct method.*)
fun has_nominal_datatype_var2 goal ctxt _ = AU.has_thms_of_tname_with_all_substrs goal ctxt ["constr_rep"];

(* ASSERT 87. checks if the proof context contains a "rec_unique" rule associated with a type of variables in the first subgoal. *)
(*We expect that this assertion is useful to detect the use of the nominal_induct method.*)
fun has_nominal_datatype_var3 goal ctxt _ = AU.has_thms_of_tname_with_all_substrs goal ctxt ["rec_unique"];

(* ASSERT 89. checks if the proof context contains a "inducts" rule associated with a constant.    *)
(*            that appears as the outermost constant (modulo Trueprop) of a premise of a Pure.imp. *)

(*We expect that this assertion is useful to detect the use of ind_case method.*)
local

fun outmost_cname (Const (cname, _) $ _) = cname
 |  outmost_cname  _                     = "";

fun has_inducts_rule (ctxt:Proof.context) (trm:term) =
  Assert_Util.has_thms_of_lnames_with_suffix ctxt [outmost_cname trm] "inducts";

in

fun inductive_as_outmost_in_pure_imp_prems (goal:thm) (ctxt:Proof.context) _ = goal
  |>    Isabelle_Utils.get_1st_subg
  liftM (ctxt |> has_inducts_rule |> Assert_Util.assrt_on_outmost_after_pure_imp_in)
  |>    Utils.is_some_true;

end;

(* ASSERT 90. check if the goal or its chained facts have one of the following constants: \<ge>, >, <, \<le>. *)
(*We expect that this assertion is useful for the linarith method.*)
fun is_linarith goal _ facts = goal::facts
  |> map (Utils.flip AU.fst_has_one_of_these_consts ["Orderings.ord_class.less_eq",
    "Orderings.ord_class.less", "Orderings.greater", "Orderings.greater_eq"])
  |> exists I;

(* ASSERT 93. checks if the first sub-goal has a constant defined with the quotient_definition keyword. *)
(*We expect that this assertion is useful for the lifting method and descending method.*)
fun has_quotient_definition goal ctxt _ = AU.has_thms_with_suffixes goal ctxt ["rsp"]

(* ASSERT 94. checks if the first sub-goal has a term of a type defined with the quotient_type keyword. *)
(*We expect that this assertion is useful for the lifting method and descending method.*)
fun has_quotient_type goal ctxt _ = AU.has_thms_of_tname_with_all_substrs goal ctxt ["Quotient_"];

(* ASSERT 95. disjunction of ASSERT 93 and ASSERT 94. *)
fun has_quotient_definition_or_quotient_type goal ctxt _ = has_quotient_definition goal ctxt ()
  orelse has_quotient_type goal ctxt ();

(* ASSERT 96. conjunction of ASSERT 93 and ASSERT 94. *)
fun has_quotient_definition_and_quotient_type goal ctxt _ = has_quotient_definition goal ctxt ()
  andalso has_quotient_type goal ctxt ();

(** Assertions about the first subgoal itself. **)
(* ASSERT 2. checks if the first subgoal contains a case declaration *)
fun has_case_ goal _ _ =
  let 
     fun is_case_ cons_name = String.isSubstring "case_" cons_name;
     val fst_subg_has_case  = AU.fst_subg_has_const_of goal is_case_;
  in
    fst_subg_has_case
  end;

(* ASSERT 16. checks if the first subgoal has rel_fun *)
fun has_rel_fun goal _ _ = AU.fst_subg_has_const_of_name goal "BNF_Def.rel_fun";

(* ASSERT 17. checks if the first subgoal has map_fun *)
fun has_map_fun goal _ _ = AU.fst_subg_has_const_of_name goal "Fun.map_fun";

(* ASSERT 62. check if the first subgoal has rel_fun or map_fun. *)
fun has_rel_fun_or_map_fun goal _ _ =
  AU.fst_subg_has_const_of_name goal "BNF_Def.rel_fun" orelse
  AU.fst_subg_has_const_of_name goal "Fun.map_fun";

(* ASSERT 18. checks if the first subgoal has a schematic variable *)
fun fst_subg_has_schematic_var (goal:thm) _ _ =
  let
    val fst_subg          = Isabelle_Utils.get_1st_subg goal:term option;
    fun has_schematic trm = Term.exists_subterm Term.is_Var trm: bool;
    val result            = fst_subg liftM has_schematic |> Utils.is_some_true: bool;
  in
    result
  end;

(* ASSERT. checks if the first subgoal contains a constant that is defined with the locale keyword. *)
(*This assertion causes problems when applied to HOL-Analysis.*)
fun has_locale_const goal (ctxt:Proof.context) _ =
  let
    val thy          = Proof_Context.theory_of ctxt;
    val locale_names = try Locale.pretty_locale_deps thy |> these |> map #name: string list;
    val test         = AU.fst_subg_has_const_of_name goal: string -> bool;
    val result       = exists test locale_names: bool;
  in
    result
  end;

(* ASSERT 11. checks if there is a constant with prefix "Num" in the first subgoal *)
fun has_const_prefixed_with_Num goal _ _ = AU.fst_subg_has_const_prefixed_with goal "Num";

(* ASSERT 19. checks if there is a constant with prefix "Real" in the first subgoal *)
fun has_const_prefixed_with_Real goal _ _ = AU.fst_subg_has_const_prefixed_with goal "Real";

(* ASSERT 20. checks if there is a constant with prefix "List" in the first subgoal *)
fun has_const_prefixed_with_List goal _ _ = AU.fst_subg_has_const_prefixed_with goal "List";

(* ASSERT 49. checks if there is a constant with prefix "Set" in the first subgoal *)
fun has_const_prefixed_with_Set goal _ _ = AU.fst_subg_has_const_prefixed_with goal "Set";

(* ASSERT 51. checks if there is a constant with prefix "Nat" in the first subgoal *)
fun has_const_prefixed_with_Nat goal _ _ = AU.fst_subg_has_const_prefixed_with goal "Nat";

(* ASSERT 52. checks if there is a constant with prefix "Int" in the first subgoal *)
fun has_const_prefixed_with_Int goal _ _ = AU.fst_subg_has_const_prefixed_with goal "Int";

local

fun fst_subg_size_more_than_n (n:int) (goal:thm) =  Isabelle_Utils.get_1st_subg goal
  liftM Term.size_of_term
  liftM curry Int.< n
  |>    Utils.is_some_true: bool;

in

(* ASSERT 63. The term size of the first subgoal is more than 5. *)
fun fst_subg_size_more_than_5 (goal:thm) _ _ = fst_subg_size_more_than_n 5 goal;

(* ASSERT 64. The term size of the first subgoal is more than 10. *)
fun fst_subg_size_more_than_10 (goal:thm) _ _ = fst_subg_size_more_than_n 10 goal;

(* ASSERT 65. The term size of the first subgoal is more than 20. *)
fun fst_subg_size_more_than_20 (goal:thm) _ _ = fst_subg_size_more_than_n 20 goal;

(* ASSERT 66. The term size of the first subgoal is more than 40. *)
fun fst_subg_size_more_than_40 (goal:thm) _ _ = fst_subg_size_more_than_n 40 goal;

(* ASSERT 67. The term size of the first subgoal is more than 80. *)
fun fst_subg_size_more_than_80 (goal:thm) _ _ = fst_subg_size_more_than_n 80 goal;

end;

(* ASSERT 68. "Groups.times_class.times" *)
(*This assertion is expected to be useful to detect the algebra method.*)
fun fst_subg_has_times (goal:thm) _ _ = AU.fst_subg_has_const_of_name goal "Groups.times_class.times";

(* ASSERT 69. "Groups.plus_class.plus" *)
(*This assertion is expected to be useful to detect the algebra method.*)
fun fst_subg_has_plus (goal:thm) _ _ = AU.fst_subg_has_const_of_name goal "Groups.plus_class.plus";

(* ASSERT 70. "Power.power_class.power" *)
(*This assertion is expected to be useful to detect the algebra method.*)
fun fst_subg_has_power (goal:thm) _ _ = AU.fst_subg_has_const_of_name goal "Power.power_class.power";

(* ASSERT 71. "Groups.minus_class.minus" *)
(*This assertion is expected to be useful to detect the algebra method.*)
fun fst_subg_has_minus (goal:thm) _ _ = AU.fst_subg_has_const_of_name goal "Groups.minus_class.minus";

(* ASSERT 72. "Groups.uminus_class.uminus" *)
(*This assertion is expected to be useful to detect the algebra method.*)
fun fst_subg_has_uminus (goal:thm) _ _ = AU.fst_subg_has_const_of_name goal "Groups.uminus_class.uminus";

(* ASSERT 73. "Fields.inverse_class.inverse_divide" *)
(*This assertion is expected to be useful to detect the algebra method.*)
fun fst_subg_has_inverse (goal:thm) _ _ = AU.fst_subg_has_const_of_name goal "Fields.inverse_class.inverse_divide";

(* ASSERT 74. disjunction of ASSERT 68. to ASSERT 73. *)
(*This assertion is expected to be useful to detect the algebra method.*)
fun fst_subg_has_algebra_consts (goal:thm) _ _ = AU.fst_has_one_of_these_consts goal
 ["Groups.times_class.times", "Groups.plus_class.plus", "Power.power_class.power",
  "Groups.minus_class.minus", "Groups.uminus_class.uminus", "Fields.inverse_class.inverse_divide"];

(* ASSERT 75. constants with the prefix "Groups". *)
(*This assertion is expected to be useful to detect the algebra method.*)
fun has_const_prefixed_with_Group goal _ _ = AU.fst_subg_has_const_prefixed_with goal "Group";

(* ASSERT 76. constants with the prefix "Language". *)
(*This assertion is expected to be useful to detect the vcg method. *)
fun has_const_prefixed_with_Language goal _ _ = AU.fst_subg_has_const_prefixed_with goal "Language";

(* ASSERT 77. constant with the prefix "Finite_Catesian_Product". *)
(*This assertion is expected to be useful to detect the vector method.*)
fun has_const_prefixed_with_Cartesian_Euclidean_Space goal _ _ =
  AU.fst_subg_has_const_prefixed_with goal "Cartesian_Euclidean_Space";

(* ASSERT 78. constant with "vec" as a sub-string of its name. *)
(*This assertion is expected to be useful to detect the vector method.*)
fun has_subg_has_vec_const (goal:thm) _ _ = AU.fst_subg_has_const_of_name_subst goal "vec";

(* ASSERT 79. term of the type "Finite_Cartesian_Product.vec". *)
fun fst_subg_has_vec_type (goal:thm) _ _ = AU.fst_subg_has_typ_of_name goal "Finite_Cartesian_Product.vec";

(* ASSERT 80. checks if the first subgoal has more than 1 occurrence of "Pure.imp". *)
(*This assertion is expected to be useful to detect the hypsubst method.*)
fun fst_subg_has_Pure_imp_more_than_once (goal:thm) _ _ =
  AU.fst_subg_has_const_more_than_n_times goal "Pure.imp" 1;

(* ASSERT 81. checks if the first subgoal has more than 2 occurrence of "Pure.imp". *)
(*This assertion is expected to be useful to detect the hypsubst method.*)
fun fst_subg_has_Pure_imp_more_than_twice (goal:thm) _ _ =
  AU.fst_subg_has_const_more_than_n_times goal "Pure.imp" 2;

(* ASSERT 88. checks if the goal is started with the Isar-keyword "obtain". *)
fun is_obtain_proof goal ctxt _ = AU.has_all_substrings_when_printed Isabelle_Utils.Fst_Subg goal ctxt ["thesis", "\<Longrightarrow>", ")"];

(* ASSERT 91. checks if the first sub-goal has a term of one of the numeral types. *)
(*We expect that this assertion is useful to recommend liarith method.*)
fun has_trm_of_nat_int_rat_real goal _ _ = AU.fst_has_one_of_these_tnames goal
  ["Nat.nat", "Int.int", "Rat.rat", "Real.real"]

(* ASSERT 92. disjunction of ASSERT 91 and ASSERT 92. *)
(*We expect that this assertion is useful to recommend liarith method.*)
fun is_linarith2 goal _ facts = is_linarith goal () facts orelse
  has_trm_of_nat_int_rat_real goal () ();

(* ASSERT 93. checks if the first sub-goal has a term of type real. *)
(*We expect that this assertion is useful to recommend the approximation method or sos method.*)
fun has_trm_of_real goal _ _ = AU.fst_has_one_of_these_tnames goal ["Real.real"]

(* ASSERT 98. checks if there is a constant with prefix "Seq" in the first subgoal *)
(*We expect that this assertion is useful to recommend methods defined in HOL/HOLCF/IOA/Sequence.thy.*)
fun has_const_prefixed_with_Seq goal _ _ = AU.fst_subg_has_const_prefixed_with goal "Seq";

(* ASSERT 99. checks if there is a constant with prefix "Sequence" in the first subgoal *)
(*We expect that this assertion is useful to recommend methods defined in HOL/HOLCF/IOA/Sequence.thy.*)
fun has_const_prefixed_with_Sequence goal _ _ = AU.fst_subg_has_const_prefixed_with goal "Sequence";

(* ASSERT 100. disjunction of ASSERT 98 and ASSERT 99. *)
(*We expect that this assertion is useful to recommend methods defined in HOL/HOLCF/IOA/Sequence.thy.*)
fun has_const_prefixed_with_Seq_or_Sequence goal _ _ =
  has_const_prefixed_with_Seq goal () () orelse
  has_const_prefixed_with_Sequence goal () ();

(* ASSERT 101. conjunction of ASSERT 98 and ASSERT 99. *)
(*We expect that this assertion is useful to recommend methods defined in HOL/HOLCF/IOA/Sequence.thy.*)
fun has_const_prefixed_with_Seq_and_Sequence goal _ _ =
  has_const_prefixed_with_Seq goal () () andalso
  has_const_prefixed_with_Sequence goal () ();

(* ASSERT 102. checks if the first sub-goal has a term of a type defined in Seq. *)
(*We expect that this assertion is useful to recommend methods defined in HOL/HOLCF/IOA/Sequence.thy.*)
fun has_type_defined_in_Seq goal _ _ = AU.fst_subg_has_typ_of_name_subst goal "Seq";

(* ASSERT 103. checks if the first sub-goal has a term of a type defined in Sequence. *)
(*We expect that this assertion is useful to recommend methods defined in HOL/HOLCF/IOA/Sequence.thy.*)
fun has_type_defined_in_Sequence goal _ _ = AU.fst_subg_has_typ_of_name_subst goal "Sequence";

(* ASSERT 104. disjunction of ASSERT 102 and ASSERT 103. *)
(*We expect that this assertion is useful to recommend methods defined in HOL/HOLCF/IOA/Sequence.thy.*)
fun has_type_defined_in_Seq_or_Sequence goal _ _ = has_type_defined_in_Seq goal () () orelse
  has_type_defined_in_Sequence goal () ();

(* ASSERT 105. disjunction of ASSERT 100 and ASSERT 104. *)
(*We expect that this assertion is useful to recommend methods defined in HOL/HOLCF/IOA/Sequence.thy.*)
fun has_const_or_type_of_Seq_or_Sequence goal _ _ = has_const_prefixed_with_Seq_or_Sequence goal () ()
 orelse has_type_defined_in_Seq_or_Sequence goal () ();

(* ASSERT 40. checks if the proof obligation consists of "All" and "_dom" when printed out as a string. *)
fun is_termination_proof goal ctxt _ = AU.has_all_substrings_when_printed Isabelle_Utils.Fst_Subg goal ctxt ["All", "_dom"];

(* ASSERT 41. checks if the proof obligation consists of "_sumC" *)
(*It would be slightly better if we check if the constant of name "*_sum" is really a variable.*)
fun function_package goal ctxt _ = AU.has_all_substrings_when_printed Isabelle_Utils.All_Subg goal ctxt ["_sumC"];

(* ASSERT 42. checks if the proof obligation is generated by the "instance" keyword. *)
fun is_instance_proof goal ctxt _ = AU.has_all_substrings_when_printed Isabelle_Utils.Fst_Subg goal ctxt ["OFCLASS"];

(* ASSERT 106. checks if the proof obligation is an instance proof for countable_class. *)
fun is_countable_class goal ctxt _ = AU.has_all_substrings_when_printed Isabelle_Utils.Fst_Subg goal ctxt ["OFCLASS", "countable_class"];

(* ASSERT 03. check if the word_bitwise method is a promising method or not. *)
fun is_word_bitwise goal _ _ = AU.fst_has_one_of_these_consts goal
  ["Bits.bits_class.test_bit", "Bits.bits_class.lsb", "Bits.bits_class.set_bit",
   "Bits.bits_class.set_bits", "Bits.bits_class.shiftl", "Bits.bits_class.shiftr"];

(* ASSERT 04. check if the unat_arith or uint_arith method is a promising method or not. *)
fun is_u_arith goal _ _ = AU.fst_has_one_of_these_consts goal
  ["Orderings.ord_class.less_eq", "Orderings.ord_class.less", "Groups.plus_class.plus"];

(* ASSERT 60. check if the firs subgoal has "CompoScheds.mkex" in it. *)
(*We expect that this assertion is useful for the mkex_induct method.*)
fun is_mkex_induct goal _ _ = AU.fst_has_one_of_these_consts goal ["CompoScheds.mkex"];

(** Assertions about all constants appearing in the first subgoal itself. **)
(* ASSERT 21. checks if all constants are defined in Main *)
fun all_consts_in_main goal ctxt _ =
  let
    val this_thy          = Proof_Context.theory_of ctxt:theory;
    val thy_names_in_main = Context.get_theory this_thy "Main"
      |> Theory.ancestors_of
      |> map Context.theory_name:string list;
    fun in_Main str = exists (str |> Isabelle_Utils.fst_qualifier |> equal) thy_names_in_main;
  in
    AU.all_cnames_satisfy goal in_Main
  end;

(* ASSERT TODO. check if the first subgoal has a constant that is defined with the "class" keyword. *)
(*This assertion is currently not used, as it causes problems when mining HOL-Analysis.*)
fun has_class_const goal _ _ = AU.fst_subg_has_const_of goal (String.isSubstring ".class.");

(** Assertions about the classification of terms (according to Spec_Rules.retrieve) in the first subgoal. **)
(* ASSERT 22. checks if the first subgoal is an "Equational" problem or not. *)
fun fst_subg_is_classified_as_Equational goal ctxt _ = AU.fst_subg_is_classified_as goal ctxt Spec_Rules.Equational;

(* ASSERT 23. checks if the first subgoal is an "Inductive" problem or not. *)
fun fst_subg_is_classified_as_Inductive goal ctxt _ = AU.fst_subg_is_classified_as goal ctxt Spec_Rules.Inductive;

(* ASSERT 24. checks if the first subgoal is a "Co_Inductive" problem or not. *)
fun fst_subg_is_classified_as_Co_Inductive goal ctxt _ = AU.fst_subg_is_classified_as goal ctxt Spec_Rules.Co_Inductive;

(* ASSERT 25. checks if the first subgoal is an "Unknown" problem or not. *)
fun fst_subg_is_classified_as_Unknown goal ctxt _ = AU.fst_subg_is_classified_as goal ctxt Spec_Rules.Unknown;

(** Assertions about the outermost construct of the first subgoal. **)
(* ASSERT 26. checks if the outermost construct in the first subgoal is the meta equality. *)
fun outermost_is_pure_eq goal _ _ = AU.outermost_cname_in_1st_subg_is goal "Pure.eq";

(* ASSERT 27. checks if the outermost construct in the first subgoal is the HOL equality. *)
fun outermost_is_hol_eq goal _ _ = AU.outermost_cname_in_1st_subg_is goal "HOL.eq";

(* ASSERT 28. checks if the outermost construct in the first subgoal is the meta implication. *)
fun outermost_is_pure_imp goal _ _ = AU.outermost_cname_in_1st_subg_is goal "Pure.imp";

(* ASSERT 29. checks if the outermost construct in the first subgoal is the HOL implication. *)
fun outermost_is_hol_imp goal _ _ = AU.outermost_cname_in_1st_subg_is goal "HOL.implies";

(* ASSERT 30. checks if the outermost construct in the first subgoal is the meta all. *)
fun outermost_is_pure_all goal _ _ = AU.outermost_cname_in_1st_subg_is goal "Pure.all";

(* ASSERT 31. checks if the outermost construct in the first subgoal is the HOL all. *)
fun outermost_is_hol_all goal _ _ = AU.outermost_cname_in_1st_subg_is goal "HOL.All";

(* ASSERT 32. checks if the outermost construct in the first subgoal is the HOL existential quantifier. *)
fun outermost_is_hol_ex goal _ _ = AU.outermost_cname_in_1st_subg_is goal "HOL.Ex";

(* ASSERT 46. checks if the outermost construct in the first subgoal is the HOL conjunction. *)
fun outermost_is_hol_and goal _ _ = AU.outermost_cname_in_1st_subg_is goal "HOL.conj";

(* ASSERT 47. checks if the outermost construct in the first subgoal is the HOL disjunction. *)
fun outermost_is_hol_or goal _ _ = AU.outermost_cname_in_1st_subg_is goal "HOL.disj";

(* ASSERT 48. checks if the outermost construct in the first subgoal is the HOL Not. *)
fun outermost_is_hol_not goal _ _ = AU.outermost_cname_in_1st_subg_is goal "HOL.Not";

(* ASSERT 15. checks if the outermost construct in the first suboal is a function that is not fully applied yet. *)
fun outermost_is_fun_not_fully_applied goal _ _ =
  let
    val fst_subg   = Isabelle_Utils.get_1st_subg goal: term option;
    val is_applied = Option.map AU.is_fun_not_fully_applied fst_subg: bool option;
  in
    Utils.is_some_true is_applied:bool
  end;

(* ASSERT 33. checks if the outermost construct in the first subgoal is the meta equality. *)
fun fst_subg_has_pure_eq_not_as_outmost goal _ _ = AU.fst_subg_has_cname_not_as_outmost goal "Pure.eq";

(* ASSERT 34. checks if the outermost construct in the first subgoal is the HOL equality. *)
fun fst_subg_has_hol_eq_not_as_outmost goal _ _ = AU.fst_subg_has_cname_not_as_outmost goal "HOL.eq";

(* ASSERT 35. checks if the outermost construct in the first subgoal is the meta implication. *)
fun fst_subg_has_pure_imp_not_as_outmost goal _ _ = AU.fst_subg_has_cname_not_as_outmost goal "Pure.imp";

(* ASSERT 36. checks if the outermost construct in the first subgoal is the HOL implication. *)
fun fst_subg_has_hol_imp_not_as_outmost goal _ _ = AU.fst_subg_has_cname_not_as_outmost goal "HOL.implies";

(* ASSERT 37. checks if the outermost construct in the first subgoal is the meta all. *)
fun fst_subg_has_pure_all_not_as_outmost goal _ _ = AU.fst_subg_has_cname_not_as_outmost goal "Pure.all";

(* ASSERT 38. checks if the outermost construct in the first subgoal is the HOL all. *)
fun fst_subg_has_hol_all_not_as_outmost goal _ _ = AU.fst_subg_has_cname_not_as_outmost goal "HOL.All";

(* ASSERT 39. checks if the outermost construct in the first subgoal is the HOL existential quantifier. *)
fun fst_subg_has_hol_ex_not_as_outmost goal _ _ = AU.fst_subg_has_cname_not_as_outmost goal "HOL.Ex";

(* ASSERT 45. checks if the first goal contains a term of type "Word.word". *)
fun fst_subg_has_word goal _ _ = goal
  |>    Isabelle_Utils.get_trm_in Isabelle_Utils.Fst_Subg
  liftM Isabelle_Utils.get_typ_names_in_trm
  |>    these
  |>    exists (equal "Word.word"): bool;

(* ASSERT 59. checks if the outermost construct in the first subgoal is Abstraction.temp_strengthening. *)
fun outermost_is_temp_strengthening goal _ _ =  AU.outermost_cname_in_1st_subg_is goal "Abstraction.temp_strengthening";

(** The list of assertions currently used **)
val assertions =
(*01*) [check_local_assms,
(*02*)  has_case_,
(*03*)  is_word_bitwise,
(*04*)  is_u_arith,
(*05*)  fact_pinduct,
(*06*)  fact_psimp,
(*07*)  fact_pelims,
(*08*)  fact_cases,
(*09*)  fact_intros,
(*10*)  check_rec_simp,
(*11*)  has_const_prefixed_with_Num,
(*12*)  fact_lift_def,
(*13*)  fact_primcorec,
(*14*)  is_locale_intro1,
(*15*)  outermost_is_fun_not_fully_applied,
(*16*)  has_rel_fun,
(*17*)  has_map_fun,
(*18*)  fst_subg_has_schematic_var,
(*19*)  has_const_prefixed_with_Real,
(*20*)  has_const_prefixed_with_List,
(*21*)  all_consts_in_main,
(*22*)  fst_subg_is_classified_as_Equational,
(*23*)  fst_subg_is_classified_as_Inductive,
(*24*)  fst_subg_is_classified_as_Co_Inductive,
(*25*)  fst_subg_is_classified_as_Unknown,
(*26*)  outermost_is_pure_eq,
(*27*)  outermost_is_hol_eq,
(*28*)  outermost_is_pure_imp,
(*29*)  outermost_is_hol_imp,
(*30*)  outermost_is_pure_all,
(*31*)  outermost_is_hol_all,
(*32*)  outermost_is_hol_ex,
(*33*)  fst_subg_has_pure_eq_not_as_outmost,
(*34*)  fst_subg_has_hol_eq_not_as_outmost,
(*35*)  fst_subg_has_pure_imp_not_as_outmost,
(*36*)  fst_subg_has_hol_imp_not_as_outmost,
(*37*)  fst_subg_has_pure_all_not_as_outmost,
(*38*)  fst_subg_has_hol_all_not_as_outmost,
(*39*)  fst_subg_has_hol_ex_not_as_outmost,
(*40*)  is_termination_proof,
(*41*)  function_package,
(*42*)  is_instance_proof,
(*43*)  is_locale_intro2,
(*44*)  is_unfold_locale,
(*45*)  fst_subg_has_word,
(*46*)  outermost_is_hol_and,
(*47*)  outermost_is_hol_or,
(*48*)  outermost_is_hol_not,
(*49*)  has_const_prefixed_with_Set,
(*50*)  fact_induct,
(*51*)  has_const_prefixed_with_Nat,
(*52*)  has_const_prefixed_with_Int,
(*53*)  has_datatype_var,
(*54*)  has_datatype_var_para,
(*55*)  has_var_of_rec,
(*56*)  has_eventually,
(*57*)  fact_inductive,
(*58*)  fact_fun,
(*59*)  outermost_is_temp_strengthening,
(*60*)  is_mkex_induct,
(*61*)  has_var_of_codata,
(*62*)  has_rel_fun_or_map_fun(*,
(*63*)  fst_subg_size_more_than_5,
(*64*)  fst_subg_size_more_than_10,
(*65*)  fst_subg_size_more_than_20,
(*66*)  fst_subg_size_more_than_40,
(*67*)  fst_subg_size_more_than_80*),
(*68*)  fst_subg_has_times,
(*69*)  fst_subg_has_plus,
(*70*)  fst_subg_has_power,
(*71*)  fst_subg_has_minus,
(*72*)  fst_subg_has_uminus,
(*73*)  fst_subg_has_inverse,
(*74*)  fst_subg_has_algebra_consts,
(*75*)  has_const_prefixed_with_Group,
(*76*)  has_const_prefixed_with_Language,
(*77*)  has_const_prefixed_with_Cartesian_Euclidean_Space,
(*78*)  has_subg_has_vec_const,
(*79*)  fst_subg_has_vec_type,
(*80*)  fst_subg_has_Pure_imp_more_than_once,
(*81*)  fst_subg_has_Pure_imp_more_than_twice,
(*82*)  fact_fixrec,
(*83*)  has_domain_var,
(*84*)  fact_fixrec_or_domain,
(*85*)  has_nominal_datatype_var1,
(*86*)  has_nominal_datatype_var2,
(*87*)  has_nominal_datatype_var3,
(*88*)  is_obtain_proof,
(*89*)  inductive_as_outmost_in_pure_imp_prems,
(*90*)  is_linarith,
(*91*)  has_trm_of_nat_int_rat_real,
(*92*)  is_linarith2,
(*93*)  has_trm_of_real,
(*94*)  has_quotient_definition,
(*95*)  has_quotient_type,
(*96*)  has_quotient_definition_or_quotient_type,
(*97*)  has_quotient_definition_and_quotient_type,
(*98*)  has_const_prefixed_with_Seq,
(*99*)  has_const_prefixed_with_Sequence,
(*100*) has_const_prefixed_with_Seq_or_Sequence,
(*101*) has_const_prefixed_with_Seq_and_Sequence,
(*102*) has_type_defined_in_Seq,
(*103*) has_type_defined_in_Sequence,
(*104*) has_type_defined_in_Seq_or_Sequence,
(*105*) has_const_or_type_of_Seq_or_Sequence,
(*106*) is_countable_class]

(** functions to generate qualitative explanations **)
fun const_in_fst consts= "the first subgoal has one of the following constants: " ^ consts: string;

val second_line = "  Note that these rules are automatically derived by the ":string;

fun related_const_rule rule_name isar_keyword = "the underlying proof context has a " ^ rule_name ^
 " rule associated to one of the constants appearing in the first subgoal.\n" ^
 second_line ^ isar_keyword ^ " keyword.";

fun const_in_fst_prefixed_with (pre:string) = "the first subgoal has a constant defined in " ^ pre ^ ".";

fun classified_as (class:string) = "Isabelle thinks that the first subgoal should be classified as "
 ^ class ^ " problem.";

fun outermost_is (outmost:string) = "the outermost constant of the first subgoal is " ^ outmost ^ ".";

fun not_as_outermost (cname:string) = "the first subgoal has " ^ cname ^ " somewhere inside " ^
  "not as the outermost constant.";

fun type_in_fst (tname:string) = "the first subgoal has a variable of type " ^ tname ^ ".";

fun type_in_fst_subst (tname:string) = "the first subgoal has a term of a type related to " ^ tname ^ ".";

fun related_type_rule (rule_name:string) (isar_keyword) = "the underlying proof context has a " ^
  rule_name ^ " associated to one of the variables appearing in the first subgoal.\n" ^
  second_line ^ isar_keyword ^ " keyword.";

fun related_const_or_type_rule (crule_name:string) (cisa_keyword:string) (trule_name:string) (tisa_keyword:string) =
  related_const_rule crule_name cisa_keyword ^ "\nOr else because " ^ 
  related_type_rule trule_name tisa_keyword;

fun trm_size_bigger_than (numb:string) = "the term size of first subgoal is more than " ^ numb ^ ".";

val explanations =
[
(*01*)  (*check_local_assms,                     *)
"the context has locally defined assumptions.",
(*02*)  (*has_case_,                             *)
"the first subgoal has case distinctions",
(*03*)  (*is_word_bitwise,                       *)
const_in_fst "Bits.bits_class.test_bit, Bits.bits_class.lsb, Bits.bits_class.set_bit, " ^ 
"Bits.bits_class.bits, Bits.bits_class.shiftl, Bits.bits_class.shiftr.",
(*04*)  (*is_u_arith,                            *)
const_in_fst "Orderings.ord_class.less_eq, Orderings.ord_class.less, Groups.plus_class.plus.",
(*05*)  (*fact_pinduct,                          *)
related_const_rule "pinduct" "function or fun",
(*06*)  (*fact_psimp,                            *)
related_const_rule "psimp" "function",
(*07*)  (*fact_pelims,                           *)
related_const_rule "pelims" "fun and function",
(*08*)  (*fact_cases,                            *)
related_const_rule "cases" "fun and function",
(*09*)  (*fact_intros,                           *)
related_const_rule "intros" "inductive or inductive_set",
(*10*)  (*check_rec_simp,                        *)
"the underlying proof context has a recursive simplification rule related to a constant appearing " ^
"in the first subgoal.",
(*11*)  (*has_const_prefixed_with_Num,           *)
const_in_fst_prefixed_with "Num",
(*12*)  (*fact_lift_def,                         *)
related_const_rule "abs_eq, rsp, transfer, and rep_eq" "lift_definition.",
(*13*)  (*fact_primcorec,                        *)
related_const_rule "code, ctr, sel" "primcorec",
(*14*)  (*is_locale_intro1,                      *)
related_const_rule ".axiom" "locale",
(*15*)  (*outermost_is_fun_not_fully_applied,    *)
"the outer most function is not fully applied.",
(*16*)  (*has_rel_fun,                           *)
const_in_fst "BNF_Def.rel_fun",
(*17*)  (*has_map_fun,                           *)
const_in_fst "Fun.map_fun",
(*18*)  (*fst_subg_has_schematic_var,            *)
"the first subgoal has a schematic variable.",
(*19*)  (*has_const_prefixed_with_Real,          *)
const_in_fst_prefixed_with "Real",
(*20*)  (*has_const_prefixed_with_List,          *)
const_in_fst_prefixed_with "List",
(*21*)  (*all_consts_in_main,                    *)
"all constants in the first subgoal are defined in HOL/Main.",
(*22*)  (*fst_subg_is_classified_as_Equational,  *)
classified_as "equational",
(*23*)  (*fst_subg_is_classified_as_Inductive,   *)
classified_as "inductive",
(*24*)  (*fst_subg_is_classified_as_Co_Inductive,*)
classified_as "co_Inductive",
(*25*)  (*fst_subg_is_classified_as_Unknown,     *)
classified_as "unknown",
(*26*)  (*outermost_is_pure_eq,                  *)
outermost_is "Pure equality",
(*27*)  (*outermost_is_hol_eq,                   *)
outermost_is "HOL equality",
(*28*)  (*outermost_is_pure_imp,                 *)
outermost_is "Pure implication",
(*29*)  (*outermost_is_hol_imp,                  *)
outermost_is "HOL implication",
(*30*)  (*outermost_is_pure_all,                 *)
outermost_is "Pure universal quantifier",
(*31*)  (*outermost_is_hol_all,                  *)
outermost_is "HOL universal quantifier",
(*32*)  (*outermost_is_hol_ex,                   *)
outermost_is "HOL existential quantifier",
(*33*)  (*fst_subg_has_pure_eq_not_as_outmost,   *)
not_as_outermost "Pure equality",
(*34*)  (*fst_subg_has_hol_eq_not_as_outmost,    *)
not_as_outermost "HOL equality",
(*35*)  (*fst_subg_has_pure_imp_not_as_outmost,  *)
not_as_outermost  "Pure implication",
(*36*)  (*fst_subg_has_hol_imp_not_as_outmost,   *)
not_as_outermost "HOL implication",
(*37*)  (*fst_subg_has_pure_all_not_as_outmost,  *)
not_as_outermost "Pure universal quantifier",
(*38*)  (*fst_subg_has_hol_all_not_as_outmost,   *)
not_as_outermost "HOL universal quantifier",
(*39*)  (*fst_subg_has_hol_ex_not_as_outmost,    *)
not_as_outermost "HOL existential quantifier",
(*40*)  (*is_termination_proof,                  *)
"this conjecture is about termination.",
(*41*)  (*function_package,                      *)
"at least one subgoal has _sumC in it. \n  Note that a constant of _sumC is related to the function package,",
(*42*)  (*is_instance_proof,                     *)
"the first subgoal has OFCLASS.\n  Note that OFCLASS appears in instantiation proofs.",
(*43*)  (*is_locale_intro2,                      *)
"a constant has locally defined axioms. \n  Note that the locale package often introduces locally defined axioms.",
(*44*)  (*is_unfold_locale,                      *)
"the proof context has _def and _axioms_def rules related to the outermost constant of the first subgoal.\n" ^
"  Note that the locale package often introduces locally defined axioms.",
(*45*)  (*fst_subg_has_word,                     *)
type_in_fst "Word.word",
(*46*)  (*outermost_is_hol_and,                  *)
outermost_is "HOL conjunction",
(*47*)  (*outermost_is_hol_or,                   *)
outermost_is "HOL disjunction",
(*48*)  (*outermost_is_hol_not,                  *)
outermost_is "HOL negation",
(*49*)  (*has_const_prefixed_with_Set,           *)
const_in_fst_prefixed_with "Set",
(*50*)  (*fact_induct,                           *)
related_const_rule "induct" "inductive and inductive_set",
(*51*)  (*has_const_prefixed_with_Nat,           *)
const_in_fst_prefixed_with "Nat",
(*52*)  (*has_const_prefixed_with_Int,           *)
const_in_fst_prefixed_with "Int",
(*53*)  (*has_datatype_var,                      *)
related_type_rule "rec_transfer" "datatype",
(*54*)  (*has_datatype_var_para,                 *)
related_type_rule "inj_map_strong" "datatype",
(*55*)  (*has_var_of_rec,                        *)
related_type_rule "Abs__ext_inject" "record",
(*56*)  (*has_eventually,                        *)
"the proof obligation involves Filter.eventually.",
(*57*)  (*fact_inductive,                        *)
related_const_rule "inducts" "inductive",
(*58*)  (*fact_fun,                              *)
related_const_rule "elims" "fun",
(*59*)  (*outermost_is_temp_strengthening,       *)
outermost_is "Abstract.temp_strengthening",
(*60*)  (*is_mkex_induct,                        *)
const_in_fst "CompoScheds.mkex",
(*61*)  (*has_var_of_codata,                     *)
related_type_rule "corec_disc" "codatatype",
(*62*)  (*has_rel_fun_or_map_fun,                *)
const_in_fst "BNF_Def.rel_fun, Fun.map_fun"(*,
(*63*)  (*fst_subg_size_more_than_5,             *)
trm_size_bigger_than "5",
(*64*)  (*fst_subg_size_more_than_10,            *)
trm_size_bigger_than "10",
(*65*)  (*fst_subg_size_more_than_20,            *)
trm_size_bigger_than "20",
(*66*)  (*fst_subg_size_more_than_40,            *)
trm_size_bigger_than "40",
(*67*)  (*fst_subg_size_more_than_80             *)
trm_size_bigger_than "80"*),
(*68*) (*fst_subg_has_times*)
const_in_fst "Groups.times_class.times",
(*69*) (*fst_subg_has_plus*)
const_in_fst "Groups.plus_class.plus",
(*70*) (*fst_subg_has_power*)
const_in_fst "Power.power_class.power",
(*71*) (*fst_subg_has_minus*)
const_in_fst "Groups.minus_class.minus",
(*72*) (*fst_subg_has_uminus*)
const_in_fst "Groups.uminus_class.uminus",
(*73*) (*fst_subg_has_inverse*)
const_in_fst "Fields.inverse_class.inverse_divide",
(*74*) (*fst_subg_has_algebra_consts*)
const_in_fst ("Groups.times_class.times, Groups.plus_class.plus, Power.power_class.power, " ^
   "Groups.minus_class.minus, Groups.uminus_class.uminus, and Fields.inverse_class.inverse_divide"),
(*75*) (*has_const_prefixed_with_Group*)
const_in_fst_prefixed_with "Group",
(*76*) (*has_const_prefixed_with_Language*)
const_in_fst_prefixed_with "Language",
(*77*) (*has_const_prefixed_with_Cartesian_Euclidean_Space*)
const_in_fst_prefixed_with "Cartesian_Euclidean_Space",
(*78*) (*has_subg_has_vec_const*)
const_in_fst "vec",
(*79*) (*fst_subg_has_vec_type*)
"the first subgoal has a term of type Finite_Cartesian_Product.vec",
(*80*) (*fst_subg_has_Pure_imp_more_than_once*)
"the first subgoal has Pure.imp more than once",
(*81*) (*fst_subg_has_Pure_imp_more_than_twice*)
"the first subgoal has Pure.imp more than two times",
(*82*) (*fact_fixrec*)
related_const_rule "unfold" "fixrec",
(*83*) (*has_domain_var*)
related_type_rule "unfold" "domain",
(*84*) (*fact_fixrec_or_domain*)
related_const_or_type_rule "unfold" "fixrec" "unfold" "domain",
(*86*) (*has_nominal_datatype_var1,*)
related_type_rule "narrowing...simp" "nominal_datatype",
(*87*) (*has_nominal_datatype_var2,*)
related_type_rule "constr_rep" "nominal_datatype",
(*87*) (*has_nominal_datatype_var3*)
related_type_rule "rec_unique" "nominal_datatype",
(*88*) (*is_obtain_proof*)
"this proof obligation stared by the obtain keyword",
(*89*) (*inductive_as_outmost_in_pure_imp_prems*)
("the first sub-goal has a constant defined with the inductive keyword or the inductive_set keyword" ^
 " as the outermost constant of a premise of meta-implication"),
(*90*) (*is_linarith*)
const_in_fst "Orderings.ord_class.less_eq, Orderings.ord_class.less, Orderings.greater, Orderings.greater_eq",
(*91*) (*has_trm_of_nat_int_rat_real*)
type_in_fst "Nat.nat, Int.int, Rat.rat, or Real.real",
(*92*) (*is_linarith2*)
(const_in_fst "Orderings.ord_class.less_eq, Orderings.ord_class.less, Orderings.greater, Orderings.greater_eq" ^
 " or " ^ type_in_fst "Nat.nat, Int.int, Rat.rat, or Real.real"),
(*93*) (*has_trm_of_real*)
type_in_fst "Real.real",
(*94*) (*has_quotient_definition*)
related_const_rule "rsp" "quotient_definition",
(*95*) (*has_quotient_type*)
related_type_rule "Quotient_" "quotient_type",
(*96*) (*has_quotient_definition_or_quotient_type*)
related_const_rule "rsp" "quotient_definition" ^ " or " ^ related_type_rule "Quotient_" "quotient_type",
(*97*) (*has_quotient_definition_and_quotient_type*)
related_const_rule "rsp" "quotient_definition" ^ " and " ^ related_type_rule "Quotient_" "quotient_type",
(*98*)  (*has_const_prefixed_with_Seq*)
const_in_fst_prefixed_with "Seq",
(*99*)  (*has_const_prefixed_with_Sequence*)
const_in_fst_prefixed_with "Sequence",
(*100*) (*has_const_prefixed_with_Seq_or_Sequence*)
const_in_fst_prefixed_with "Seq or Sequence",
(*101*) (*has_const_prefixed_with_Seq_and_Sequence*)
const_in_fst_prefixed_with "Seq and Sequence",
(*102*) (*has_type_defined_in_Seq*)
type_in_fst_subst "Seq",
(*103*) (*has_type_defined_in_Sequence*)
type_in_fst_subst "Sequence",
(*104*) (*has_type_defined_in_Seq_or_Sequence*)
type_in_fst_subst "Seq or Sequence",
(*105*) (*has_const_or_type_of_Seq_or_Sequence*)
const_in_fst_prefixed_with "Seq or Sequence" ^ "Or else " ^ type_in_fst_subst "Seq or Sequence",
(*106*) (*is_countable_class*)
"the first subgoal is about instantiation proof of a countable_class."
]

(** Function used to generate database **)

(* Parse the argument of command by/apply into the name of method*)
fun get_name (Method.Source src) = (Token.name_of_src src |> fst) (*
                                  ^" "^          
                                  (*this part add the argument of applied method*)
                                  (space_implode "" (map Token.content_of (Token.args_of_src src))) *)
 |  get_name _ = ""

(* evaluate assertions and return a string for generating/matching database*)
fun eval_assertion_gen (state:Proof.state) (assrts:(thm -> context -> thm list -> bool) list) =
    let
      val {goal:thm, context:context, facts:thm list} = Proof.goal state;
      fun curry2 f (a, b, c) = f a b c;
      val asserts_exps = assrts ~~ explanations;
      fun apply_ass (assert, expl) trpl = ((*(fn _ => tracing expl) trpl;*) curry2 assert trpl);
      val fvector = Isabelle_Utils.if_solved goal [] (Utils.map_arg (goal, context, facts) (map apply_ass asserts_exps));
    in
      fvector : bool list
    end;

fun eval_assertion_for_ML_real state = eval_assertion_gen state assertions |> map Utils.bool_to_real: real list;

fun eval_assertion_for_ML_bool state = eval_assertion_gen state assertions: bool list;

fun bool_to_string b = if b then "1" else "0";

fun eval_assertion state = eval_assertion_gen state assertions
  |> map bool_to_string
  |> String.concatWith ","

end;
