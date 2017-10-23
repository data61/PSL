(*  Title:      Assertions.ML
    Author:     Yilun He, Data61, CSIRO
                Yutaka Nagashima, CIIRC, CTU
    
    This file stores the written assertions, which can be used to extract features from proof state.

    eval_assertion converts a proof state to a list of real values, which is the feature vector of
    the state.

    Users can add their own assertion as functions of type "thm -> context -> boolean".
*)

signature ASSERTIONS =
sig
  (*written assertions*)
  val eval_assertion_for_ML: Proof.state -> real list
  val eval_assertion:        Proof.state -> string
end;

(*** Implementation of assertions ***)
structure Assertions(*:ASSERTIONS*) =
struct
(** Generic utility and assertion functions **)

fun if_solved (goal:thm) then_clause else_clause =
  if Thm.nprems_of goal = 0 then then_clause else else_clause;
val prems_of  = Thm.prems_of;
fun is_some_true maybe = Option.getOpt (maybe, false);

infix 1 >>= >=> liftM;
fun (m >>= f)   = Option.mapPartial f m;
fun (f >=> g)   = Option.composePartial (g f);
fun (m liftM f) = Option.map f m;

(* The first subgoal has a constant that satisfies the given assertion. *)
fun fst_subg_has_const_of (goal:thm) (assert:string -> bool) =
  let
    fun test (str,_)    = assert str;
    val fst_subg        = Isabelle_Utils.get_1st_subg goal:term option;
    val result_unsolved = Option.map (Term.exists_Const test) fst_subg:bool option;
    val result          = is_some_true result_unsolved;
  in
    result
  end;

(* The first subgoal has a constant of the given name. *)
fun fst_subg_has_const_of_name (goal:thm) (name:string) =
fst_subg_has_const_of goal (fn cname => name = cname);

(* get the first quantifier of the given long name *)
fun fst_qualifier (lname:string) = Option.getOpt (lname |> Long_Name.explode |> try hd, "");

(* The first subgoal has a constant that has the name with the given prefix. *)
fun fst_subg_has_const_prefixed_with goal (prefix:string) =
  let
    fun is_prefixed (lname:string) = fst_qualifier lname = prefix;
  in
    fst_subg_has_const_of goal is_prefixed
  end;

(* get_outmost_name returns the outermost name of given term. *)
fun get_outmost_name (trm:term) =
  let
    val cnames                = Isabelle_Utils.get_const_names_in_trm trm: string list;
    val numb                  = length cnames: int;
    val last_cname            = try (nth cnames) (numb - 1): string option;
    val snd_last_cname        = try (nth cnames) (numb - 2): string option;
    val outmost_is_pure_const = Option.map (curry (op =) "HOL.Trueprop") last_cname: bool option;
  in
    Option.map (Utils.If (snd_last_cname, last_cname)) outmost_is_pure_const |> Option.join: string option
  end;

(* outermost_const_name_in_1st_subg_is checks if the first subgoal has a constant of the given name as the outermost constant. *)
fun outermost_const_name_in_1st_subg_is (goal:thm) (cname:string) = SOME goal
  >>=   Isabelle_Utils.get_1st_subg
  >>=   get_outmost_name
  liftM (curry (op =) cname)
  liftM (Utils.If (true, false))
  |>    Utils.flip (curry Option.getOpt) false: bool;

(* fst_subg_has_const_name_not_as_outmost checks if the first subgoal has a constant of the given name, but not as the outermost constant. *)
fun fst_subg_has_const_name_not_as_outmost (goal:thm) (cname:string) =
  fst_subg_has_const_of_name goal cname andalso not (outermost_const_name_in_1st_subg_is goal cname);

(* is_fun_not_fully_applied checks if the term is a function that is ready to take arguments. *)
fun is_fun_not_fully_applied (trm:term) = Term.type_of trm |> Term.size_of_typ |> (fn i => 1 = i);

(* fst_subg_is_classified_as roughly classifies the first subgoal *)(*FIXME*)
fun fst_subg_is_classified_as (ctxt:Proof.context) (goal:thm) (rclass:Spec_Rules.rough_classification) =
  let
    val fst_subg         = Isabelle_Utils.get_1st_subg goal:term option;
    val classifications  = Option.map (Spec_Rules.retrieve ctxt) fst_subg |> these;
    val rough_classes    = map fst classifications: Spec_Rules.rough_classification list;
    val is_classified_as = exists (fn class => rclass = class) rough_classes:bool;
  in
    is_classified_as
  end;

(* const_all_assert checks if all constant meet given criteria *)
fun const_all_assert goal (assert:string -> bool) = 
  let
    val const_names_in_1st_subg = Isabelle_Utils.get_const_names_in_1st_subg goal;
    val holds_for_all           = List.all assert const_names_in_1st_subg;
  in holds_for_all:bool end;

(* get_thms_of_name_with_all_substrings gets the thms that are named after a base-name of the constant and other given strings. *)
fun get_thms_of_name_with_all_substrings (ctxt:Proof.context) (substrs:string list) (cname:string) =
  let
    val short_cname    = Long_Name.base_name cname;
    val criterion      = Find_Theorems2.get_criterion "" (short_cname :: substrs): (bool * term Find_Theorems2.criterion) list;
    val relevant_rules = Find_Theorems.find_theorems ctxt NONE NONE true criterion |> snd |> map snd;
  in
    relevant_rules: thm list
  end;

(* has_thms_of_name_with_all_substrings checks if the context contains thms that are named after the base-name of the constant and other strings. *)
fun has_thms_of_name_with_all_substrings (ctxt:Proof.context) (substrs:string list) (cname:string) =
  get_thms_of_name_with_all_substrings ctxt substrs cname |> null |> not: bool;

(* get_thms_of_cname_with_all_substrings check if the context has a thm such that its name consists of the base-name of a constant appearing *)
(* in the first sub-goal and other specified strings. *)
fun get_thms_of_cname_with_all_substrings (goal:thm) (ctxt:Proof.context) (strs:string list) =
  let
    val const_names = Isabelle_Utils.get_const_names_in_1st_subg goal: string list;
    val result = map (get_thms_of_name_with_all_substrings ctxt strs) const_names |> flat |> null |> not;
  in result end;

(* get_thms_of_const_name_with_suffix returns the thms that are named after a given constant with a given suffix from the current context. *)
fun get_thms_of_const_name_with_suffix (ctxt:Proof.context) (sfx:string) (cname:string) =
  try (Proof_Context.get_thms ctxt) (cname ^ "." ^ sfx) |> these:thm list;

(* has_thms_of_const_name_with_suffix checks if the current context contains thms that are named after a given constant with a given suffix. *)
fun has_thms_of_const_name_with_suffix (ctxt:Proof.context) (sfx:string) (cname:string) =
  get_thms_of_const_name_with_suffix ctxt sfx cname |> null |> not:bool;

(* get_thms_of_const_names_with_suffix is similar to get_thms_of_const_name_with_suffix, but with multiple constant names. *)
fun get_thms_of_const_names_with_suffix (ctxt:Proof.context) (cnames:string list) (sfx:string) =
  map (get_thms_of_const_name_with_suffix ctxt sfx) cnames |> flat:thm list;

(* has_thms_of_const_names_with_suffix is similar to has_thms_of_const_name_with_suffix, but with multiple constant names. *)
fun has_thms_of_const_names_with_suffix (ctxt:Proof.context) (cnames:string list) (sfx:string) =
  exists (has_thms_of_const_name_with_suffix ctxt sfx) cnames:bool;

(* has_thms_with_suffixes checks if the context contains thms that are named after a constant in the goal but with one of the given suffixes. *)
fun has_thms_with_suffixes (goal:thm) (ctxt:Proof.context) (sfxes:string list) =
  let
    val const_names = Isabelle_Utils.get_const_names_in_1st_subg goal;
    val typ_names   = Isabelle_Utils.get_typ_names_in_1st_subg goal;
    val names       = const_names @ typ_names;
    val has_thms    = forall (has_thms_of_const_names_with_suffix ctxt names) sfxes;
  in has_thms end:bool;

(* has_these_as_substrings checks if the given list of strings are all appear in the given proof obligation when printed out. *)
fun has_these_as_substrings (wo:Isabelle_Utils.where_in_thm) (goal:thm) (ctxt:Proof.context) (strs:string list) =
  let
    fun none_is_substr (substrs:string list) (fst_g:string) = forall (Utils.flip String.isSubstring fst_g) substrs: bool;
    val result = Isabelle_Utils.get_trm_in wo goal
      liftM (Syntax.string_of_term ctxt)
      liftM (none_is_substr strs)
      |> is_some_true;
  in result end;

(* get_typ_names_of_freevs_in_trm takes a term and returns a list of names of types of variables that *)
(* appear in the term. *)
fun get_typ_names_of_freevs_in_trm (trm:term) = Term.add_frees trm []
  |> map snd
  |> map (the_list o try Term.dest_Type)
  |> flat
  |> map fst: string list;

(** Assertions about the existence of certain objects (rules) in the proof state **)

(* ASSERT 01. checks if the proof context contains local assumption *)
fun check_local_assms _ ctxt = ctxt
  |> Proof_Context.theory_of
  |> Proof_Context.init_global
  |> Assumption.local_assms_of ctxt
  |> null
  |> not

(* ASSERT 05. checks if the proof context contains a "pinduct" rule associated with a constant in the first subgoal. *)
fun fact_pinduct goal ctxt = has_thms_with_suffixes goal ctxt ["pinduct"]

(* ASSERT 06. checks if the proof context contains a "psimp" rule associated with a constant in the first subgoal. *)
fun fact_psimp   goal ctxt = has_thms_with_suffixes goal ctxt ["psimps"]

(* ASSERT 07. checks if the proof context contains a "pelims" rule associated with a constant in the first subgoal. *)
fun fact_pelims  goal ctxt = has_thms_with_suffixes goal ctxt ["pelims"]

(* ASSERT 08. checks if the proof context contains a "cases" rule associated with a constant in the first subgoal. *)
fun fact_cases   goal ctxt = has_thms_with_suffixes goal ctxt ["cases"]

(* ASSERT 09. check if the proof context contains an "intros" rule associated with a constant in the first subgoal. *)
fun fact_intros  goal ctxt = has_thms_with_suffixes goal ctxt ["intros"]

(* ASSERT 10. checks if the proof context contains a recursive simplification rule associated with a constant in the first subgoal. *)
fun check_rec_simp goal ctxt =
  let
    val const_names = Isabelle_Utils.get_const_names_in_1st_subg goal;
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
    exist_related_rsimp const_names
  end;

(* ASSERT 12. checks if the proof context contains facts that are generated by the lift_definition *)
(*            command and are associated with a constant in the first subgoal. *)
fun fact_lift_def goal ctxt =
  let
    val lift_lemmas = ["abs_eq","rsp","transfer","rep_eq"]
  in
    has_thms_with_suffixes goal ctxt lift_lemmas
  end;

(* ASSERT 13. checks if the proof context contains facts that are generated by the primcorec *)
(*            command and are associated with a constant in the first subgoal. *)
fun fact_primcorec goal ctxt = has_thms_with_suffixes goal ctxt ["code","ctr","sel"];

(* ASSERT 14. checks if the proof obligation has intro_locales*)
fun is_locale_intro1 goal ctxt = get_thms_of_cname_with_all_substrings goal ctxt [".axioms"];

(* ASSERT 43. checks if the proof obligation has intro_locales*)
fun is_locale_intro2 goal ctxt = get_thms_of_cname_with_all_substrings goal ctxt ["local.", "_axioms"];

(* ASSERT 44. checks if the outermost constant visible to users has a name such that the underlying   *)
(*            proof context has a theorem of name ".base_name_of_the_constant.".                      *)
(*            We expect that this assertion is useful to detect the use of the unfold_locales method. *)
fun is_unfold_locale goal ctxt=
  let
    fun get_rules name_with_dots = Find_Theorems2.all_names_to_rules "" [name_with_dots] ctxt goal;
    val some_result = goal
      |> Isabelle_Utils.get_trm_in Isabelle_Utils.Fst_Subg
      >>= get_outmost_name
      liftM Long_Name.base_name
      liftM (fn bname => "." ^ bname ^ ".")
      liftM get_rules
      liftM (not o null) : bool option;
  in is_some_true some_result end;

(** Assertions about the first subgoal itself. **)
(* ASSERT 2. checks if the first subgoal contains a case declaration *)
fun has_case_ goal _ =
  let 
     fun is_case_ cons_name = String.isSubstring "case_" cons_name;
     val fst_subg_has_case  = fst_subg_has_const_of goal is_case_;
  in
    fst_subg_has_case
  end;

(* TODO: checks if the first subgoal contains a variable of type record. *)
(*TODO*)fun has_record _ _ = undefined;

(* TODO: checks if the first subgoal uses type class definition *)
(*TODO*)fun uses_type_class _ _ = undefined;
(*use "_class" as a hint*)

(* ASSERT 16. checks if the first subgoal has rel_fun *)
fun has_rel_fun goal _ = fst_subg_has_const_of_name goal "BNF_Def.rel_fun";

(* ASSERT 17. checks if the first subgoal has map_fun *)
fun has_map_fun goal _ = fst_subg_has_const_of_name goal "Fun.map_fun";

(* ASSERT 18. checks if the first subgoal has a schematic variable *)
fun fst_subg_has_schematic_var (goal:thm) _ =
  let
    val fst_subg          = Isabelle_Utils.get_1st_subg goal:term option;
    fun has_schematic trm = Term.exists_subterm Term.is_Var trm: bool;
    val result            = Option.map has_schematic fst_subg |> is_some_true: bool;
  in
    result
  end;

(*use Term.is_Var and Term.exists_subterm*)

(* ASSERT 11. checks if there is a constant with prefix "Num" in the first subgoal *)
fun has_const_prefixed_with_Num goal _ = fst_subg_has_const_prefixed_with goal "Num";

(* ASSERT 19. checks if there is a constant with prefix "Real" in the first subgoal *)
fun has_const_prefixed_with_Real goal _ = fst_subg_has_const_prefixed_with goal "Real";

(* ASSERT 20. checks if there is a constant with prefix "List" in the first subgoal *)
fun has_const_prefixed_with_List goal _ = fst_subg_has_const_prefixed_with goal "List";

(** Assertions about all constants appearing in the first subgoal itself. **)
(* ASSERT 21. checks if all constants are defined in Main *)
fun all_consts_in_main goal ctxt =
  let
    val this_thy          = Proof_Context.theory_of ctxt:theory;
    val thy_names_in_main = Context.get_theory this_thy "Main"
      |> Theory.ancestors_of
      |> map Context.theory_name:string list;
    fun in_Main str = exists (fn s => s = (Long_Name.explode str|> hd)) thy_names_in_main;
  in
    const_all_assert goal in_Main
  end;

(** Assertions about the classification of terms (according to Spec_Rules.retrieve) in the first subgoal. **)
(* ASSERT 22. checks if the first subgoal is an "Equational" problem or not. *)
fun fst_subg_is_classified_as_Equational goal ctxt = fst_subg_is_classified_as ctxt goal Spec_Rules.Equational;

(* ASSERT 23. checks if the first subgoal is an "Inductive" problem or not. *)
fun fst_subg_is_classified_as_Inductive goal ctxt = fst_subg_is_classified_as ctxt goal Spec_Rules.Inductive;

(* ASSERT 24. checks if the first subgoal is a "Co_Inductive" problem or not. *)
fun fst_subg_is_classified_as_Co_Inductive goal ctxt = fst_subg_is_classified_as ctxt goal Spec_Rules.Co_Inductive;

(* ASSERT 25. checks if the first subgoal is an "Unknown" problem or not. *)
fun fst_subg_is_classified_as_Unknown goal ctxt = fst_subg_is_classified_as ctxt goal Spec_Rules.Unknown;

(** Assertions about the outermost construct of the first subgoal. **)
(* ASSERT 26. checks if the outermost construct in the first subgoal is the meta equality. *)
fun outermost_is_pure_eq goal _ = outermost_const_name_in_1st_subg_is goal "Pure.eq";

(* ASSERT 27. checks if the outermost construct in the first subgoal is the HOL equality. *)
fun outermost_is_hol_eq goal _ = outermost_const_name_in_1st_subg_is goal "HOL.eq";

(* ASSERT 28. checks if the outermost construct in the first subgoal is the meta implication. *)
fun outermost_is_pure_imp goal _ = outermost_const_name_in_1st_subg_is goal "Pure.imp";

(* ASSERT 29. checks if the outermost construct in the first subgoal is the HOL implication. *)
fun outermost_is_hol_imp goal _ = outermost_const_name_in_1st_subg_is goal "HOL.implies";

(* ASSERT 30. checks if the outermost construct in the first subgoal is the meta all. *)
fun outermost_is_pure_all goal _ = outermost_const_name_in_1st_subg_is goal "Pure.all";

(* ASSERT 31. checks if the outermost construct in the first subgoal is the HOL all. *)
fun outermost_is_hol_all goal _ = outermost_const_name_in_1st_subg_is goal "HOL.All";

(* ASSERT 32. checks if the outermost construct in the first subgoal is the HOL existential quantifier. *)
fun outermost_is_hol_ex goal _ = outermost_const_name_in_1st_subg_is goal "HOL.Ex";

(* ASSERT 15. checks if the outermost construct in the first suboal is a function that is not fully applied yet. *)
fun outermost_is_fun_not_fully_applied goal _ =
  let
    val fst_subg   = Isabelle_Utils.get_1st_subg goal: term option;
    val is_applied = Option.map is_fun_not_fully_applied fst_subg: bool option;
  in
    is_some_true is_applied:bool
  end;

(* ASSERT 33. checks if the outermost construct in the first subgoal is the meta equality. *)
fun fst_subg_has_pure_eq_not_as_outmost goal _ = fst_subg_has_const_name_not_as_outmost goal "Pure.eq";

(* ASSERT 34. checks if the outermost construct in the first subgoal is the HOL equality. *)
fun fst_subg_has_hol_eq_not_as_outmost goal _ = fst_subg_has_const_name_not_as_outmost goal "HOL.eq";

(* ASSERT 35. checks if the outermost construct in the first subgoal is the meta implication. *)
fun fst_subg_has_pure_imp_not_as_outmost goal _ = fst_subg_has_const_name_not_as_outmost goal "Pure.imp";

(* ASSERT 36. checks if the outermost construct in the first subgoal is the HOL implication. *)
fun fst_subg_has_hol_imp_not_as_outmost goal _ = fst_subg_has_const_name_not_as_outmost goal "HOL.implies";

(* ASSERT 37. checks if the outermost construct in the first subgoal is the meta all. *)
fun fst_subg_has_pure_all_not_as_outmost goal _ = fst_subg_has_const_name_not_as_outmost goal "Pure.all";

(* ASSERT 38. checks if the outermost construct in the first subgoal is the HOL all. *)
fun fst_subg_has_hol_all_not_as_outmost goal _ = fst_subg_has_const_name_not_as_outmost goal "HOL.All";

(* ASSERT 39. checks if the outermost construct in the first subgoal is the HOL existential quantifier. *)
fun fst_subg_has_hol_ex_not_as_outmost goal _ = fst_subg_has_const_name_not_as_outmost goal "HOL.Ex";

(* ASSERT 40. checks if the proof obligation consists of "All" and "_dom" when printed out as a string. *)
fun is_termination_proof goal ctxt = has_these_as_substrings Isabelle_Utils.Fst_Subg goal ctxt ["All", "_dom"];

(* ASSERT 41. checks if the proof obligation consists of "_sumC" *)
(*It would be slightly better if we check if the constant of name "*_sum" is really a variable.*)
fun function_package goal ctxt = has_these_as_substrings Isabelle_Utils.All_Subg goal ctxt ["_sumC"];

(* ASSERT 42. checks if the proof obligation is generated by the "instance" keyword. *)
fun is_instance_proof goal ctxt = has_these_as_substrings Isabelle_Utils.Fst_Subg goal ctxt ["OFCLASS"];

(* TODO: ASSERT 03. check if the word_bitwise method is a promising method or not. *)
fun is_word_bitwise _ _ = true;

(* TODO: ASSERT 04. check if the unat_arith or uinit_arith method is a promising method or not. *)
fun is_u_arith _ _ = true;

(* ASSERT 45. checks if the first goal contains a term of type "Word.word". *)
fun fst_subg_has_word goal _ = goal
      |> Isabelle_Utils.get_trm_in Isabelle_Utils.Fst_Subg
      liftM Isabelle_Utils.get_typ_names_in_trm
      |> these
      |> exists (curry (op =) "Word.word"): bool;

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
(*45*)  fst_subg_has_word]

(* check if there is a constant with prefix real *)
fun const_real (goal, _) = 
  let
    fun isReal str = (Long_Name.explode str |> hd handle Empty => "") = "Real";
  in
    fst_subg_has_const_of goal isReal
  end

(** Function used to generate database **)

(* Parse the argument of command by/apply into the name of method*)
fun get_name (Method.Source src) = (Token.name_of_src src |> fst) (*
                                  ^" "^          
                                  (*this part add the argument of applied method*)
                                  (space_implode "" (map Token.content_of (Token.args_of_src src))) *)
 |  get_name _ = ""

(* evaluate assertions and return a string for generating/matching database*)
fun eval_assertion_gen (state:Proof.state) (assrts:(thm -> Proof.context -> bool) list) =
    let
      val {goal:thm, context:Proof.context, facts:thm list} = Proof.goal state;
      val fvector = if_solved goal [] (Utils.map_arg (goal, context) (map uncurry assrts));
    in
      fvector : bool list
    end;

fun eval_assertion_for_ML state = eval_assertion_gen state assertions |> map Utils.bool_to_real: real list;

fun bool_to_string b = if b then "1" else "0";

fun eval_assertion state = eval_assertion_gen state assertions
|> map bool_to_string
|> String.concatWith ","

end;
