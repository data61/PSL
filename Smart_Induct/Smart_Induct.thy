(*  Title:      MeLoId/src/Smart_Induct.thy
    Author:     Yutaka Nagashima, CIIRC, CTU, University of Innsbruck
*)
theory Smart_Induct
  imports  "../LiFtEr/LiFtEr"
  keywords "smart_induct" :: diag
begin

ML\<open> structure Dynamic_Induct =
struct

(* Induct_Seed: The seed to make the tactic-generator for the induct method. *)
structure Induct_Seed  =
struct

datatype modifier = 
  On        of string
| Arbitrary of string
| Rule      of string;

type modifiers = modifier list;

fun get_ons   (fvars:string list) = map On fvars;
fun get_arbs  (fvars:string list) = map Arbitrary fvars;
fun get_rules (rules:string list) = map Rule rules;

fun order' ordered [] = ordered
 |  order' (ons, arbs, rules) (On        var :: mods) = order' (ons @ [On var], arbs,                   rules              ) mods
 |  order' (ons, arbs, rules) (Arbitrary var :: mods) = order' (ons,            arbs @ [Arbitrary var], rules              ) mods
 |  order' (ons, arbs, rules) (Rule     rule :: mods) = order' (ons,            arbs,                   rules @ [Rule rule]) mods;

fun order (mods:modifiers) = (*(ons, arbs, rules)*)
  order' ([],[],[]) mods : (modifiers * modifiers * modifiers)

fun get_name (On        name) = name
  | get_name (Arbitrary name) = name
  | get_name (Rule      name) = name;

val get_names = map get_name;

fun mods_have_two_rules' (Rule _::mods) acc = mods_have_two_rules' mods (acc + 1)
  | mods_have_two_rules' (_     ::mods) acc = mods_have_two_rules' mods acc
  | mods_have_two_rules' []             acc = acc;

fun mods_have_more_than_one_rule mods = mods_have_two_rules' mods 0 > 1;

fun filter_out_mods_w_too_many_rules (modss:modifiers Seq.seq) =
    Seq.filter (not o mods_have_more_than_one_rule) modss: modifiers Seq.seq;

fun mods_to_string (mods:modifiers) =
  let 
    val prefix_if_nonnil = Utils.prefix_if_nonempty;
  in
    mods |> order |> (fn (ons, arbs, rules) =>
    get_names ons
    @ prefix_if_nonnil "arbitrary:" (get_names arbs)
    @ prefix_if_nonnil "rule:"      (get_names rules))
    |> Dynamic_Utils.get_meth_nm ""
  end;

fun get_all_modifiers (state:Proof.state) =
  let
    val {context: Proof.context, goal: thm,...} = Proof.goal state;
    val free_var_names   = Isabelle_Utils.get_free_var_names_in_1st_subg goal;
    val induct_rules     = Find_Theorems2.get_induct_rule_names context goal : string list;
    val all_induct_mods  = get_ons free_var_names @ get_arbs free_var_names @ get_rules induct_rules;
  in
    all_induct_mods : modifiers
  end;

val pick_vars = filter     (fn modi => case modi of On _ => true | _ => false);
val dump_vars = filter_out (fn modi => case modi of On _ => true | _ => false);

fun reordered_mods (mods:modifiers)=
  let
    val vars   = pick_vars mods : modifiers;
    val varss  = Nitpick_Util.all_permutations vars : modifiers list;
    val others = dump_vars mods : modifiers;
    val combs  = map (fn vs => vs @ others) varss;
  in
    combs:modifiers list
  end;

end;

(* ITG: Induct_Tactic_Generator. *)
structure ITG : DYNAMIC_TACTIC_GENERATOR = mk_Dynamic_Tactic_Generator (Induct_Seed);

fun pst_to_modifiers (state:Proof.state) =
  let
    val all_modifiers  = ITG.get_all_modifiers state : ITG.modifiers;
    (*We need to consider all permutations because induct is order sensitive.*)
    val all_modifierss = Seq2.powerset (Seq.of_list all_modifiers)
                      |> Seq.map Seq.list_of
                      |> Seq.map Induct_Seed.reordered_mods
                      |> Seq.map Seq.of_list
                      |> Seq.flat
                      |> Induct_Seed.filter_out_mods_w_too_many_rules
                      |> Seq.chop 300 |> fst : ITG.modifiers list;
    val _ = tracing ("smart_induct produced " ^ Int.toString (length all_modifierss) ^ " combinations of arguments for the induct method." )
  in
    all_modifierss: ITG.modifiers list
  end;

end;
\<close>

ML\<open> fun modifiers_to_str (mods: Dynamic_Induct.Induct_Seed.modifiers) : string =
  enclose "apply (" ")" ("induct" ^ Dynamic_Induct.Induct_Seed.mods_to_string mods);
\<close>

ML\<open> (* Example assertions in LiFtEr. *)
local

open LiFtEr_Util LiFtEr;
infix And Imply Is_An_Arg_Of Is_Rule_Of Is_Nth_Ind Is_In_Trm_Loc Is_In_Trm_Str;

in

(* Example 1-a *)
val all_ind_term_are_non_const_wo_syntactic_sugar =
 All_Ind (Trm 1,
   Some_Trm_Occ (Trm_Occ 1,
       Trm_Occ_Is_Of_Trm (Trm_Occ 1, Trm 1)
     And
       Not (Is_Cnst (Trm_Occ 1)))): assrt;

(* Example 1-b *)
val all_ind_term_are_non_const_with_syntactic_sugar =
 All_Ind (Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
     Not (Is_Cnst (Trm_Occ 1)))): assrt;

(* Example 2 *)
val all_ind_terms_have_an_occ_as_variable_at_bottom =
 All_Ind (Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
       Is_Atom (Trm_Occ 1)
     Imply
       Is_At_Deepest (Trm_Occ 1)));

(* Example 3 *)
val all_ind_vars_are_arguments_of_a_recursive_function =
Some_Trm (Trm 1,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    All_Ind (Trm 2,
      Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
           Is_Recursive_Cnst (Trm_Occ 1)
         And
           (Trm_Occ 2 Is_An_Arg_Of Trm_Occ 1)))));

(* Example 4 *)
val all_ind_vars_are_arguments_of_a_rec_func_where_pattern_match_is_complete =
 Not (Some_Rule (Rule 1, True))
Imply
 Some_Trm (Trm 1,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    Is_Recursive_Cnst (Trm_Occ 1)
   And
    All_Ind (Trm 2,
      Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
       Some_Numb (Numb 1,
         Pattern (Numb 1, Trm_Occ 1, All_Constr)
        And
         Is_Nth_Arg_Of (Trm_Occ 2, Numb 1, Trm_Occ 1))))));

(* Example 5 *)
val all_ind_terms_are_arguments_of_a_const_with_a_related_rule_in_order =
 Some_Rule (Rule 1, True)
Imply
 Some_Rule (Rule 1,
  Some_Trm (Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    (Rule 1 Is_Rule_Of Trm_Occ 1)
    And
    (All_Ind (Trm 2,
     (Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
       Some_Numb (Numb 1,
         Is_Nth_Arg_Of (Trm_Occ 2, Numb 1, Trm_Occ 1)
        And
        (Trm 2 Is_Nth_Ind Numb 1)))))))));

(* Example 6-a *)
val ind_is_not_arb =
All_Arb (Trm 1,
 Not (Some_Ind (Trm 2,
  Are_Same_Trm (Trm 1, Trm 2))));

(* Example 6-b *)
val vars_in_ind_terms_are_generalized =
 Some_Ind (Trm 1,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
   (All_Trm (Trm 2,
     Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
       ((Trm_Occ 2 Is_In_Trm_Loc Trm_Occ 1)
       And
        Is_Free (Trm_Occ 2))
      Imply
       Some_Arb (Trm 3,
        Are_Same_Trm (Trm 2, Trm 3)))))));

val Example6 = ind_is_not_arb And vars_in_ind_terms_are_generalized;

val at_least_one_recursive_term =
  Some_Trm_Occ (Trm_Occ 1,
    Is_Recursive_Cnst (Trm_Occ 1))
Imply
  Some_Trm (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
      Some_Trm (Trm 2,
        Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
          Some_Ind (Trm 3,
            Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
                 Is_Recursive_Cnst (Trm_Occ 1)
               And
                 (Trm_Occ 2 Is_An_Arg_Of Trm_Occ 1)
               And
                  Are_Same_Trm (Trm 2, Trm 3)))))));

val at_least_one_on = Some_Ind (Trm 1, True);

val one_on_is_deepest =
  Some_Ind (Trm 1, True)
Imply
  Some_Ind (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1, Is_At_Deepest (Trm_Occ 1)));

val ons_and_arbs_share_func =
All_Ind (Trm 1,
 All_Arb (Trm 2,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
    Some_Trm_Occ (Trm_Occ 3,
      ((Trm_Occ 1) Is_An_Arg_Of (Trm_Occ 3)
     And
      ((Trm_Occ 2) Is_An_Arg_Of (Trm_Occ 3))))))));

infix Or Trm_Occ_Is_Of_Trm Is_Const_Of_Name Is_Printed_As;

val all_args_of_rule_as_ons =
 Some_Rule (Rule 1, True)
Imply
 Some_Rule (Rule 1,
   Some_Trm_Occ (Trm_Occ 1,
     (Rule 1 Is_Rule_Of Trm_Occ 1)
    And
      All_Trm_Occ (Trm_Occ 2,
        (Trm_Occ 2 Is_An_Arg_Of Trm_Occ 1)
       Imply
        Some_Ind (Trm 2,
          Trm_Occ 2 Trm_Occ_Is_Of_Trm Trm 2
))
));

val arb_share_parent_with_ind =
 Some_Arb (Trm 1, True)
Imply
 Some_Arb (Trm 1,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
   Some_Ind (Trm 2,
    Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
     Some_Trm_Occ (Trm_Occ 3,
       (Trm_Occ 1 Is_An_Arg_Of Trm_Occ 3)
      And
       (Trm_Occ 2 Is_An_Arg_Of Trm_Occ 3)
)))));

val no_arb_should_be_at_the_same_loc_as_ind =
 Some_Arb (Trm 1, True)
Imply
  (All_Arb (Trm 1,
   Not
    (Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
     (Some_Trm (Trm 3,
      (Some_Trm_Occ_Of (Trm_Occ 31, Trm 3,
       (Some_Numb (Numb 4,
         (Is_Nth_Arg_Of (Trm_Occ 1, Numb 4, Trm_Occ 31))
        And
         (Some_Ind (Trm 2,
          (Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
           (Some_Trm_Occ_Of (Trm_Occ 32, Trm 3,
            (Is_Nth_Arg_Of (Trm_Occ 2, Numb 4, Trm_Occ 32))
))))))))))))))));

val only_one_rule =
 Some_Rule (Rule 1, True)
Imply
  (All_Rule (Rule 1,
    All_Rule (Rule 2,
     (Are_Same_Rule (Rule 1, Rule 2)))))

end;
\<close>

setup\<open> Apply_LiFtEr.update_assert "heuristic_1a" all_ind_term_are_non_const_wo_syntactic_sugar                           \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_2"  all_ind_terms_have_an_occ_as_variable_at_bottom                         \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_3"  all_ind_vars_are_arguments_of_a_recursive_function                      \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_4"  all_ind_vars_are_arguments_of_a_rec_func_where_pattern_match_is_complete\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_5"  all_ind_terms_are_arguments_of_a_const_with_a_related_rule_in_order     \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_6a" ind_is_not_arb                                                          \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_6a2" ind_is_not_arb                                                          \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_7" at_least_one_recursive_term                                              \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_8" at_least_one_on                                                          \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_9" one_on_is_deepest                                                        \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_10" ons_and_arbs_share_func                         \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_11" all_args_of_rule_as_ons                         \<close>
setup\<open> Apply_LiFtEr.update_assert "arb_share_parent_with_ind" arb_share_parent_with_ind          \<close>
setup\<open> Apply_LiFtEr.update_assert "no_arb_should_be_at_the_same_loc_as_ind" no_arb_should_be_at_the_same_loc_as_ind \<close>
setup\<open> Apply_LiFtEr.update_assert "no_arb_should_be_at_the_same_loc_as_ind2" no_arb_should_be_at_the_same_loc_as_ind \<close>
setup\<open> Apply_LiFtEr.update_assert "only_one_rule" only_one_rule \<close>

ML\<open>
local

structure LiFtEr_Assertion = Apply_LiFtEr.LiFtEr_Assertion;

type trans_trans = Toplevel.transition -> Toplevel.transition;
open Parser_Combinator;
open LiFtEr_Util;

in

fun pst_n_ind_mods_to_result_pair (pst:Proof.state) (ind_mod:ind_mods) =
  let
    val ctxt                = Proof.context_of pst: Proof.context;
    val all_asserts         = (Symtab.dest o LiFtEr_Assertion.get) (Context.Proof ctxt) |> map snd: LiFtEr.assrt list;
    val numb_of_all_asserts = length all_asserts: int;
    fun mk_clean_mods (ind_mods:ind_mods) =
      let
        val normalize = Isabelle_Utils.normalize_trm_as_string ctxt;
        val {ons, arbs, rules} = dest_mods ind_mods;
        fun normalize_rule_as_string (rule_as_string:string) =
          let
            val short_cname_option = try (space_explode ".") rule_as_string
                                 <$> Utils.init <$> Utils.last: string option;
            val long_name_option = short_cname_option <$> normalize: string option;
            val clean_rule_name  = long_name_option <$> curry (op ^) <*> SOME ".induct";
            val result           = if is_some clean_rule_name then the clean_rule_name else "";
          in
            result
          end;
         val clean_ons   = map (string_to_induct_on   o normalize                o induct_on_to_string  ) ons  : induct_on   list;
         val clean_arbs  = map (string_to_induct_arb  o normalize                o induct_arb_to_string ) arbs : induct_arb  list;
         val clean_rules = map (string_to_induct_rule o normalize_rule_as_string o induct_rule_to_string) rules: induct_rule list;
      in
        Ind_Mods {ons = clean_ons, arbs = clean_arbs, rules = clean_rules}: ind_mods
      end;
    fun apply_assrt (assrt:LiFtEr.assrt) (pst:Proof.state) (ind_mods:LiFtEr.ind_mods) =
        LiFtEr.eval (pst, assrt, ind_mods): bool;
    fun run_test (assrt:LiFtEr.assrt) (pst:Proof.state) (ind_mods:LiFtEr.ind_mods) =
        apply_assrt assrt pst ind_mods = true;
    val succeeded_assrts = filter (fn assrt => apply_assrt assrt pst (mk_clean_mods ind_mod)) all_asserts: LiFtEr.assrt list;
    val numb_of_succeeded_assrts = length succeeded_assrts: int;
(*
    val _ = tracing ("Out of " ^ Int.toString numb_of_all_asserts ^ " assertions, " ^
                     Int.toString numb_of_succeeded_assrts ^ " assertions succeeded.");
*)

  in
    numb_of_succeeded_assrts: int
  end;

datatype ind_mod_gen = Ion of LiFtEr_Util.induct_on | Iarb of LiFtEr_Util.induct_arb | Irule of LiFtEr_Util.induct_rule;

fun psl_ind_mod_to_lifter_ind_mod (Dynamic_Induct.Induct_Seed.On        str) = LiFtEr_Util.Print str |> LiFtEr_Util.Ind_On  |> Ion
  | psl_ind_mod_to_lifter_ind_mod (Dynamic_Induct.Induct_Seed.Arbitrary str) = LiFtEr_Util.Print str |> LiFtEr_Util.Ind_Arb |> Iarb
  | psl_ind_mod_to_lifter_ind_mod (Dynamic_Induct.Induct_Seed.Rule      str) = LiFtEr_Util.Ind_Rule str |> Irule;

fun psl_ind_mods_to_lifter_ind_mods' (psl_ind_mod::psl_ind_mods) (acc as Ind_Mods {ons, arbs, rules}) = (case psl_ind_mod_to_lifter_ind_mod psl_ind_mod of
      Ion   modi => psl_ind_mods_to_lifter_ind_mods' (psl_ind_mods) (Ind_Mods {ons = ons @ [modi], arbs = arbs,          rules = rules})
    | Iarb  modi => psl_ind_mods_to_lifter_ind_mods' (psl_ind_mods) (Ind_Mods {ons = ons,          arbs = arbs @ [modi], rules = rules})
    | Irule modi => psl_ind_mods_to_lifter_ind_mods' (psl_ind_mods) (Ind_Mods {ons = ons,          arbs = arbs,          rules = rules @ [modi]}))
  | psl_ind_mods_to_lifter_ind_mods' [] acc = acc;

fun psl_ind_mods_to_lifter_ind_mods (psl_ind_mods: Dynamic_Induct.Induct_Seed.modifier list) =
    psl_ind_mods_to_lifter_ind_mods' psl_ind_mods (Ind_Mods {ons = [], arbs = [], rules = []}): LiFtEr_Util.ind_mods;

val on_construct   = Dynamic_Induct.Induct_Seed.On;
val arb_construct  = Dynamic_Induct.Induct_Seed.Arbitrary;
val rule_construct = Dynamic_Induct.Induct_Seed.Rule;

fun lifter_ind_mods_to_psl_ind_mods (Ind_Mods {ons, arbs, rules}) =
    map (on_construct   o dest_print o dest_induct_on) ons @
    map (arb_construct  o dest_print o dest_induct_arb) arbs @
    map (rule_construct o dest_induct_rule) rules;

val smart_induct_cmd =
  Toplevel.keep_proof (fn top: Toplevel.state =>
    let
      val _ = tracing "started extracting features logically";
      val state                      = Toplevel.proof_of top                                   : Proof.state;
      val psl_modifierss             = Dynamic_Induct.pst_to_modifiers state                   : Dynamic_Induct.Induct_Seed.modifier list list;
      val lifter_modifierss          = map psl_ind_mods_to_lifter_ind_mods psl_modifierss      : LiFtEr_Util.ind_mods list;
      fun ind_mods_to_pair ind_mods  = ((pst_n_ind_mods_to_result_pair state ind_mods), ind_mods): (int * ind_mods);
      val pairs                      = Par_List.map ind_mods_to_pair lifter_modifierss                  : (int * LiFtEr_Util.ind_mods) list;
      val sorted_pairs               = sort (fn (p1, p2) => Int.compare (fst p1, fst p2)) pairs |> rev: (int * LiFtEr_Util.ind_mods) list;
      val _                = tracing "Try these inductions!": unit;
      val best_pairs       = List.take (sorted_pairs, 20);
      fun mk_message (i, mods) = (modifiers_to_str o lifter_ind_mods_to_psl_ind_mods) mods ^ " (* The score is " ^ Int.toString i ^ ". *)";
      val best_messages  = map mk_message best_pairs: strings;
      val sendback         = Active.sendback_markup_properties [Markup.padding_command]: string -> string;
      val _                = map (tracing o sendback) best_messages;
    in () end);

end;
\<close>

ML\<open>
val _ = Outer_Syntax.command @{command_keyword smart_induct} "recommend which method to use." (Scan.succeed smart_induct_cmd);
\<close>

primrec rev :: "'a list \<Rightarrow> 'a list" where
  "rev []       = []" |
  "rev (x # xs) = rev xs @ [x]"

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev []     ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"

lemma "itrev xs ys = rev xs @ ys"
  assert_LiFtEr heuristic_11  [on["xs", "ys"],arb[],rule["Smart_Induct.itrev.induct"]]
  assert_LiFtEr only_one_rule [on["xs", "ys"],arb[],rule["Smart_Induct.itrev.induct"]]
  (*This should fail:
   assert_LiFtEr heuristic_11 [on["xs"],      arb[],rule["Smart_Induct.itrev.induct"]]*)
  assert_LiFtEr no_arb_should_be_at_the_same_loc_as_ind [on["xs"],arb["ys"],rule[]]
  oops

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sep a [] = []" |
  "sep a [x] = [x]" |
  "sep a (x#y#zs) = x # a # sep a (y#zs)"

lemma "map f (sep a xs) = sep (f a) (map f xs)"

  assert_LiFtEr no_arb_should_be_at_the_same_loc_as_ind [on["xs"],arb["a"],rule[]]
  apply (induct a xs rule: Smart_Induct.sep.induct)
  apply auto
  done

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = N int | V vname | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s"

value "aval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"

text {* The same state more concisely: *}
value "aval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"

text {* A little syntax magic to write larger states compactly: *}

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

text {* \noindent
  We can now write a series of updates to the function @{text "\<lambda>x. 0"} compactly:
*}
lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)

value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"


text {* In  the @{term[source] "<a := b>"} syntax, variables that are not mentioned are 0 by default:
*}
value "aval (Plus (V ''x'') (N 5)) <''y'' := 7>"

text{* Note that this @{text"<\<dots>>"} syntax works for any function space
@{text"\<tau>\<^sub>1 \<Rightarrow> \<tau>\<^sub>2"} where @{text "\<tau>\<^sub>2"} has a @{text 0}. *}


subsection "Constant Folding"

text{* Evaluate constant subexpressions: *}

fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N n) = N n" |
  "asimp_const (V x) = V x" |
  "asimp_const (Plus a\<^sub>1 a\<^sub>2) =
  (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N(n\<^sub>1+n\<^sub>2) |
    (b\<^sub>1,b\<^sub>2) \<Rightarrow> Plus b\<^sub>1 b\<^sub>2)"

theorem aval_asimp_const:
  "aval (asimp_const a) s = aval a s"
  apply(induction a)
    apply (auto split: aexp.split)
  done

text{* Now we also eliminate all occurrences 0 in additions. The standard
method: optimized versions of the constructors: *}

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
  "plus (N i) a = (if i=0 then a else Plus (N i) a)" |
  "plus a (N i) = (if i=0 then a else Plus a (N i))" |
  "plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"

lemma aval_plus [simp]:
  "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply(induction a1 a2 rule: plus.induct)
              apply auto
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)"


text{* Note that in @{const asimp_const} the optimized constructor was
inlined. Making it a separate function @{const plus} improves modularity of
the code and the proofs. *}

value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"

theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"

  apply(induction a)
    apply auto
  done

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec1 (LOADI n) _ stk  =  n # stk" |
  "exec1 (LOAD x) s stk  =  s(x) # stk" |
  "exec1  ADD _ (j#i#stk)  =  (i + j) # stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec [] _ stk = stk" |
  "exec (i#is) s stk = exec is s (exec1 i s stk)"

value "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]"

lemma exec_append_model_prf[simp]:
  "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"

  apply (induct is2 arbitrary: s) (* The score is 16. *)
  apply auto
  apply (induct is1 arbitrary: s stk) (* The score is 16. *)
  oops
end