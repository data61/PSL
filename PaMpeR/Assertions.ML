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
val fst_subg_has_const_prefixed_with      : thm -> string -> bool;
val outermost_cname_in_1st_subg_is        : thm -> string -> bool;
val fst_subg_has_cname_not_as_outmost     : thm -> string -> bool;
val has_thms_of_name_with_all_substrings  : context -> string list -> bool;
val has_all_substrings_when_printed       : location -> thm -> context -> string list -> bool;
val has_thms_with_suffixes                : thm -> context -> string list -> bool;
val has_thms_of_lnames_with_suffix        : context -> string list -> string -> bool;
val has_thms_of_cname_with_all_substrs    : thm -> context -> string list -> bool;
val has_thms_of_tname_with_all_substrs    : thm -> context -> string list -> bool;
(*Not very reliable*)
val is_fun_not_fully_applied              : term -> bool;
val fst_subg_is_classified_as             : thm -> context -> Spec_Rules.rough_classification -> bool;
end;

(** ASSERT_UTILS: Generic utility and assertion functions to write assertions. **)
structure Assert_Util : ASSERT_UTIL =
struct

type location = Isabelle_Utils.location;
type context  = Proof.context;

infix 1 >>= >=> liftM;
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

(* all_cnames_satisfy checks if all constant meet given criteria *)
fun all_cnames_satisfy goal (assert:string -> bool) = 
  let
    val cnames_in_1st_subg = Isabelle_Utils.get_cnames_in_1st_subg goal;
    val holds_for_all      = forall assert cnames_in_1st_subg;
  in holds_for_all:bool end;

(* The first subgoal has a constant that has the name with the given prefix. *)
fun fst_subg_has_const_prefixed_with goal (prefix:string) =
  let
    fun is_prefixed cname = Isabelle_Utils.fst_qualifier cname = prefix;
  in
    fst_subg_has_const_of goal is_prefixed: bool
  end;

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
    (*TODO? move this function to Isabelle_Utils*)
    fun is_in_Main (ctxt:Proof.context) (thm:thm) =
      let
        val this_thy          = Proof_Context.theory_of ctxt:theory;
        val thy_names_in_main = Context.get_theory this_thy "Main"
          |> Theory.ancestors_of
          |> map Context.theory_name:string list;
        fun get_theory_name (thm:thm) = thm |> Thm.get_name_hint |> fst_qualifier;
        val thy_name = get_theory_name thm;
        val result = exists (equal thy_name) thy_names_in_main;
      in
        result
      end;
    fun get_thms btname = (get_thms_of_name_with_these_substrs ctxt (btname :: strs));
    val result = goal
      |>    get_trm_in Fst_Subg
      liftM get_typ_names_in_trm
      liftM map Long_Name.base_name
      liftM map (filter_out (is_in_Main ctxt) o get_thms)
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
    fun none_is_substr (substrs:string list) (fst_g:string) = forall (Utils.flip String.isSubstring fst_g) substrs: bool;
    val result = Isabelle_Utils.get_trm_in wo goal
      liftM Syntax.string_of_term ctxt
      liftM none_is_substr strs
      |>    Utils.is_some_true;
  in result end;

end;

(*** ASSERTIONS ***)
signature ASSERTIONS =
sig
  (*written assertions*)
  val eval_assertion_for_ML: Proof.state -> bool list
  val eval_assertion:        Proof.state -> string
end;

(*** Assertions: Implementation of assertions ***)
structure Assertions(*:ASSERTIONS*) =
struct

structure AU = Assert_Util;

infix 1 >>= >=> liftM;

type context  = Proof.context;

fun (m >>= f)   = Option.mapPartial f m;
fun (f >=> g)   = Option.composePartial (g f);
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
  |> map (Term.exists_Const ((equal "Filter.eventually") o fst))
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

(* ASSERT 57. checks if the proof context contains facts that are generated by the inductive keyword. *)
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
    fun get_rules (strs:string list) = Find_Theorems2.all_names_to_rules "" strs ctxt goal;
    val result = goal
      |>    Isabelle_Utils.get_trm_in Isabelle_Utils.Fst_Subg
      >>=   Isabelle_Utils.get_outmost_cname
      liftM Long_Name.base_name
      liftM (fn bname => ["." ^ bname ^ ".", bname ^ "_def", bname ^ "_axioms_def"])
      liftM (forall (not o null o get_rules o single))
      |>    Utils.is_some_true: bool
  in result end;

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

(* ASSERT 59. checks if the first subgoal contains a constant that is defined with the locale keyword. *)
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

(* ASSERT 60. check if the first subgoal has a constant that is defined with the "class" keyword. *)
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

(* ASSERT 40. checks if the proof obligation consists of "All" and "_dom" when printed out as a string. *)
fun is_termination_proof goal ctxt _ = AU.has_all_substrings_when_printed Isabelle_Utils.Fst_Subg goal ctxt ["All", "_dom"];

(* ASSERT 41. checks if the proof obligation consists of "_sumC" *)
(*It would be slightly better if we check if the constant of name "*_sum" is really a variable.*)
fun function_package goal ctxt _ = AU.has_all_substrings_when_printed Isabelle_Utils.All_Subg goal ctxt ["_sumC"];

(* ASSERT 42. checks if the proof obligation is generated by the "instance" keyword. *)
fun is_instance_proof goal ctxt _ = AU.has_all_substrings_when_printed Isabelle_Utils.Fst_Subg goal ctxt ["OFCLASS"];

(* ASSERT 03. check if the word_bitwise method is a promising method or not. *)
fun is_word_bitwise goal _ _ = goal
  |>    Isabelle_Utils.get_trm_in Isabelle_Utils.Fst_Subg
  liftM Isabelle_Utils.get_cnames_in_trm
  |>    these
  |>    exists (Utils.eq "Bits.bits_class.test_bit" orf
                Utils.eq "Bits.bits_class.lsb" orf
                Utils.eq "Bits.bits_class.set_bit" orf
                Utils.eq "Bits.bits_class.set_bits" orf
                Utils.eq "Bits.bits_class.shiftl" orf
                Utils.eq "Bits.bits_class.shiftr");

(* ASSERT 04. check if the unat_arith or uinit_arith method is a promising method or not. *)
fun is_u_arith goal _ _ = goal
  |>    Isabelle_Utils.get_trm_in Isabelle_Utils.Fst_Subg
  liftM Isabelle_Utils.get_cnames_in_trm
  |>    these
  |>    exists (Utils.eq "Orderings.ord_class.less_eq" orf
                Utils.eq "Orderings.ord_class.less" orf
                Utils.eq "Groups.plus_class.plus");

(* ASSERT 45. checks if the first goal contains a term of type "Word.word". *)
fun fst_subg_has_word goal _ _ = goal
  |>    Isabelle_Utils.get_trm_in Isabelle_Utils.Fst_Subg
  liftM Isabelle_Utils.get_typ_names_in_trm
  |>    these
  |>    exists (equal "Word.word"): bool;

(** the list of assertions currently used **)
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
(*59*)  has_locale_const,
(*60*)  has_class_const,
(*61*)  has_var_of_codata,
(*62*)  has_rel_fun_or_map_fun]

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
      val fvector = Isabelle_Utils.if_solved goal [] (Utils.map_arg (goal, context, facts) (map (curry2) assrts));
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
