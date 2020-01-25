(*  Title:      MeLoId/src/Smart_Induct.thy
    Author:     Yutaka Nagashima, CIIRC, CTU, University of Innsbruck
*)
theory Smart_Induct
  imports  "../LiFtEr/LiFtEr"
  keywords "smart_induct" :: diag
begin

ML\<open> structure Dynamic_Induct =
struct

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

fun mods_to_string (mods:modifiers): string =
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
                      |> Seq.chop 10000 |> fst : ITG.modifiers list;
    val _ = tracing ("smart_induct produced " ^ Int.toString (length all_modifierss) ^ " combinations of arguments for the induct method." )
  in
    all_modifierss: ITG.modifiers list
  end;

structure IS = Induct_Seed;




fun modifiers_to_str (mods: IS.modifiers) : string =
  enclose "apply (" ")" ("induct" ^ IS.mods_to_string mods);

structure DU = Dynamic_Utils;
structure IU = Isabelle_Utils;

fun str_to_nontac (meth:string) : DU.state DU.nontac =
  IU.TIMEOUT_in 3.0 (Utils.try_with (K Seq.empty) DU.string_to_nontac_on_pstate meth);

fun state_to_nontacs (pst:DU.state): DU.state DU.nontac list = pst
  |> pst_to_modifiers
  |> map (fn mods => "induct" ^ IS.mods_to_string mods)
  |> map (try str_to_nontac)
  |> Utils.somes;

fun get_fst_result (pst:Proof.state) (nontac: Proof.state DU.nontac) : DU.state option =
      (try nontac pst: DU.state Seq.seq option)
  >>= (try Seq.hd: DU.state Seq.seq -> Dynamic_Utils.state option);

fun mods_return_something (pst:Proof.state) (mods: IS.modifiers) =
  Option.isSome (get_fst_result pst (str_to_nontac ("induct " ^ IS.mods_to_string mods)));

fun pst_to_functioning_modifiers (pst:Proof.state) =
  let
    val modifierss     = pst_to_modifiers pst                         : ITG.modifiers list;
    fun tag_mods mods  = (mods_return_something pst mods, mods)       : (bool * ITG.modifiers);
    val tagged_modss   = Par_List.map tag_mods modifierss             : (bool * ITG.modifiers) list;
    val filtered_modss = filter (fst) tagged_modss |> map snd         : ITG.modifiers list;
    val _              = tracing ("... out of which " ^ Int.toString (length filtered_modss) ^ " of them return some results.");
  in
    filtered_modss
  end;

fun mods_to_returned_thm_option (pst:Proof.state) (mods:IS.modifiers) =
  let
    val returned_pst_option = get_fst_result pst (str_to_nontac ("induct " ^ IS.mods_to_string mods)): Proof.state option;
    val returend_thm_option = Option.map IU.proof_state_to_thm returned_pst_option: thm option;
  in
    returend_thm_option
  end;

fun post_is_in_pre_when_printed (pst:Proof.state) (mods:IS.modifiers) =
let
  val ctxt              = Proof.context_of pst                       : Proof.context;
  val trm_to_string     = IU.trm_to_string ctxt                      : term -> string;
  val no_local_assms    = Isabelle_Utils.pstate_to_usings pst |> null: bool;
  val pre_subgoals      = IU.pst_to_subgs pst                        : term list;
  val numb_pre_subgoals = length pre_subgoals                        : int;  
  val pre_fst_goal_opt      = IU.pst_to_fst_subg pst                 : term option;
  val pre_fst_goal_str_opt  = Option.map trm_to_string pre_fst_goal_opt: string option;
  val pre_subgoals          = IU.pst_to_subgs pst                      : terms;
  val pre_subgoals_str      = map trm_to_string pre_subgoals           : strings;
  
  fun is_not_in_them (inn:string) (them:strings) = exists (String.isSubstring inn) them |> not;

  val pre_fst_goal_str_opt  = Option.map trm_to_string pre_fst_goal_opt                              : string option;
  val pre_fst_goal_str      = Utils.try_with "empty_string_because_no_term" the pre_fst_goal_str_opt : string;

  val post_fst_goal_pst = get_fst_result pst (str_to_nontac ("induct " ^ IS.mods_to_string mods)): Proof.state option;
  val post_subgoals_trm  = Option.map IU.pst_to_subgs post_fst_goal_pst |> these: term list;
  val numb_post_subgoals = length post_subgoals_trm: int; 
  val post_subgoals_str  = map trm_to_string post_subgoals_trm: strings;
  val numb_new_subgoals  = numb_post_subgoals - numb_pre_subgoals + 1;
  val new_subgoals_trm   = take numb_new_subgoals post_subgoals_trm: terms;
  val new_subgoals_have_duplicates = has_duplicates (op =) new_subgoals_trm: bool;
  val new_subgoals_str   = take numb_new_subgoals post_subgoals_str: strings;
  val pre_fst_goal_is_in_new_post_subgoals = forall (String.isSubstring ("\<Longrightarrow> " ^ pre_fst_goal_str)) new_subgoals_str;
(*
  val pre_fst_goal_is_in_new_post_subgoals = exists (String.isSubstring (*pre_fst_goal_str*)"is_filter") new_subgoals_str;
*)
  fun opt_substring  (SOME inner:string option) (SOME outer:string option) = String.isSubstring inner outer
    | opt_substring   _                          _                         = false;
(*
val _ = if pre_fst_goal_is_in_new_post_subgoals then tracing (("pre_fst_goal_is_in_new_post_subgoals    induct" ^ IS.mods_to_string mods)) else ();
val _ = if new_subgoals_have_duplicates then tracing         (("new_subgoals_have_duplicates            induct" ^ IS.mods_to_string mods)) else ();
*)
  val result = (if no_local_assms then pre_fst_goal_is_in_new_post_subgoals else false) orelse new_subgoals_have_duplicates;
(*opt_substring pre_fst_goal_str post_fst_goal_str;
*)
in
  result
end;

fun no_sch_in_pre_but_in_post (pst:Proof.state) (mods:IS.modifiers) =
let              
  val pre_fst_goal      = IU.pst_to_fst_subg pst                                                 : term option;
  val post_fst_goal_pst = get_fst_result pst (str_to_nontac ("induct " ^ IS.mods_to_string mods)): Proof.state option;
  val post_fst_goal_trm = Option.mapPartial IU.pst_to_fst_subg post_fst_goal_pst                 : term option;
  fun no_sche_in trm    = Term.add_var_names trm [] |> null                                      : bool;
  val no_shce_in_post   = Option.map no_sche_in post_fst_goal_trm |> Utils.is_some_true          : bool;
  val no_sche_in_pre    = Option.map no_sche_in pre_fst_goal      |> Utils.is_some_true          : bool;
  val result            = if no_sche_in_pre then no_shce_in_post else true                       : bool;
val _ = if not result then tracing         (("schematic variable was introduced       induct" ^ IS.mods_to_string mods)) else ();
in
  result
end;

fun pst_to_promising_modss (pst:Proof.state) =
let
  val functioning_modifiers  = pst_to_functioning_modifiers pst: ITG.modifiers list;
  val non_is_substring_modss = filter_out (post_is_in_pre_when_printed pst) functioning_modifiers: ITG.modifiers list;
  val _                      = tracing ("... out of which only " ^ Int.toString (length non_is_substring_modss) ^ " of them return a first goal that does not contain the original first goal as its sub-term.");
  val no_sche_introducing_modss = filter (no_sch_in_pre_but_in_post pst) non_is_substring_modss: ITG.modifiers list;
  val _                         = tracing ("... out of which only " ^ Int.toString (length no_sche_introducing_modss) ^ " of them return a first goal that does not newly introduce a schematic variable.");
  val first_modss    = take 1000 no_sche_introducing_modss                      : ITG.modifiers list;
  val _ = tracing ("LiFtEr assertions are evaluating the first " ^ Int.toString (length first_modss) ^ " of them.");
in
  first_modss
end;

end;
\<close>

ML\<open> (* Example assertions in LiFtEr. *)
local

open LiFtEr_Util LiFtEr;
infix And Imply Is_An_Arg_Of Is_Rule_Of Is_Nth_Ind Is_In_Trm_Loc Is_In_Trm_Str;
infix Or Trm_Occ_Is_Of_Trm Is_Const_Of_Name Is_Printed_As Is_At_Depth Is_Defined_With;

in

(* heuristic_1 *)
val all_ind_term_are_non_const_wo_syntactic_sugar =
 All_Ind (Trm 1,
   Some_Trm_Occ (Trm_Occ 1,
       (Trm_Occ 1 Trm_Occ_Is_Of_Trm Trm 1)
     And
       Not (Is_Cnst (Trm_Occ 1)))): assrt;

(* heuristic_2 *)
val all_ind_terms_have_an_occ_as_variable_at_bottom =
 All_Ind (Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
       Is_Atom (Trm_Occ 1)
     Imply
       Is_At_Deepest (Trm_Occ 1)));

(* heuristic_3 *)
val all_ind_vars_are_arguments_of_a_recursive_function =
Some_Trm (Trm 1,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    All_Ind (Trm 2,
      Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
         (((Trm_Occ 1 Is_Defined_With Fun)
          Or
           (Trm_Occ 1 Is_Defined_With Function)
          Or
           (Trm_Occ 1 Is_Defined_With Inductive)
          Or
           (Trm_Occ 1 Is_Defined_With  Primrec))
         And
           (Trm_Occ 2 Is_An_Arg_Of Trm_Occ 1))))));

(* heuristic_4 *)
val all_ind_vars_are_arguments_of_a_rec_func_where_pattern_match_is_complete =
 Not (Some_Rule (Rule 1, True))
Imply
 Some_Trm (Trm 1,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
    ((Trm_Occ 1 Is_Defined_With Fun)
    Or
     (Trm_Occ 1 Is_Defined_With  Function)
    Or
     (Trm_Occ 1 Is_Defined_With Inductive)
    Or
     (Trm_Occ 1 Is_Defined_With  Primrec))
   And
    All_Ind (Trm 2,
      Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
       Some_Numb (Numb 1,
         Pattern (Numb 1, Trm_Occ 1, All_Constr)
        And
         Is_Nth_Arg_Of (Trm_Occ 2, Numb 1, Trm_Occ 1))))));

(* heuristic_5 *)
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

(* heuristic_6 and heuristic_18 *)
val ind_is_not_arb =
All_Arb (Trm 1,
 Not (Some_Ind (Trm 2,
  Are_Same_Trm (Trm 1, Trm 2))));

(* heuristic_7 *)
val at_least_one_recursive_term =
  Some_Trm_Occ (Trm_Occ 1,
    (Trm_Occ 1 Is_Defined_With Fun)
   Or
    (Trm_Occ 1 Is_Defined_With Function)
   Or
    (Trm_Occ 1 Is_Defined_With Inductive)
   Or
    (Trm_Occ 1 Is_Defined_With Primrec))
Imply
  Some_Trm (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
      Some_Trm (Trm 2,
        Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
          Some_Ind (Trm 3,
            Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
                ((Trm_Occ 1 Is_Defined_With Fun)
                Or
                 (Trm_Occ 1 Is_Defined_With Function)
                Or
                 (Trm_Occ 1 Is_Defined_With Inductive)
                Or
                 (Trm_Occ 1 Is_Defined_With Primrec))
               And
                 (Trm_Occ 2 Is_An_Arg_Of Trm_Occ 1)
               And
                  Are_Same_Trm (Trm 2, Trm 3)))))));

(* heuristic_8 *)
val at_least_one_on = Some_Ind (Trm 1, True);

(* heuristic_9 *)
val one_on_is_deepest =
  Some_Ind (Trm 1, True)
Imply
  Some_Ind (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1, Is_At_Deepest (Trm_Occ 1)));

(* heuristic_10 *)
val ons_and_arbs_share_func =
All_Ind (Trm 1,
 All_Arb (Trm 2,
  Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
    Some_Trm_Occ (Trm_Occ 3,
      ((Trm_Occ 1) Is_An_Arg_Of (Trm_Occ 3)
     And
      ((Trm_Occ 2) Is_An_Arg_Of (Trm_Occ 3))))))));

(* heuristic_11 *)
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

(* heuristic_12 *)
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

(* heuristic_13 and heuristic_19 *)
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

(* heuristic_14 *)
val only_one_rule =
 Some_Rule (Rule 1, True)
Imply
  (All_Rule (Rule 1,
    All_Rule (Rule 2,
     (Are_Same_Rule (Rule 1, Rule 2)))));

(* heuristic_15 *)
val inner_rec_const_rule =
 Some_Rule (Rule 1,
   Some_Trm_Occ (Trm_Occ 1,
      ((Trm_Occ 1 Is_Defined_With Fun)
      Or
       (Trm_Occ 1 Is_Defined_With Function)
      Or
       (Trm_Occ 1 Is_Defined_With Inductive)
      Or
       (Trm_Occ 1 Is_Defined_With Primrec))
    And
     Some_Trm_Occ (Trm_Occ 2,
        ((Trm_Occ 2 Is_Defined_With Fun)
        Or
         (Trm_Occ 2 Is_Defined_With Function)
        Or
         (Trm_Occ 2 Is_Defined_With Inductive)
        Or
         (Trm_Occ 2 Is_Defined_With Primrec))
      And
       Are_Diff_Str (Trm_Occ 1, Trm_Occ 2)
      And
       Some_Trm_Occ (Trm_Occ 3,
        (Trm_Occ 3 Is_An_Arg_Of Trm_Occ 1)
        And
        (Trm_Occ 2 Is_In_Trm_Loc Trm_Occ 3)
        And
         All_Ind (Trm 4,
          All_Trm_Occ_Of (Trm_Occ 4, Trm 4,
           Is_Atom (Trm_Occ 4)))))))
Imply
 Some_Rule (Rule 1,
   Some_Trm_Occ (Trm_Occ 1,
      ((Trm_Occ 1 Is_Defined_With Fun)
      Or
       (Trm_Occ 1 Is_Defined_With Function)
      Or
       (Trm_Occ 1 Is_Defined_With Inductive)
      Or
       (Trm_Occ 1 Is_Defined_With Primrec))
    And
     Some_Trm_Occ (Trm_Occ 2,
        ((Trm_Occ 2 Is_Defined_With Fun)
        Or
         (Trm_Occ 2 Is_Defined_With Function)
        Or
         (Trm_Occ 2 Is_Defined_With Inductive)
        Or
         (Trm_Occ 2 Is_Defined_With Primrec))
      And
       Some_Trm_Occ (Trm_Occ 3,
        (Trm_Occ 3 Is_An_Arg_Of Trm_Occ 1)
        And
        (Trm_Occ 2 Is_In_Trm_Loc Trm_Occ 3)
        And
        (Rule 1 Is_Rule_Of Trm_Occ 2)))));

(* heuristic_16 *)
val no_ind_at_nth_arg_if_two_occ_of_recs =
 (Not (Some_Rule (Rule 1, True))
 And
  Some_Ind (Trm 1, True))
Imply
 Not
 (Some_Trm (Trm 1,
   Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
     ((Trm_Occ 1 Is_Defined_With Fun)
     Or
      (Trm_Occ 1 Is_Defined_With Function)
     Or
      (Trm_Occ 1 Is_Defined_With Inductive)
     Or
      (Trm_Occ 1 Is_Defined_With Primrec))
    And
      Some_Trm (Trm 2,
        Are_Same_Trm (Trm 1, Trm 2)
       And
       (Some_Trm_Occ_Of (Trm_Occ 2, Trm 2,
          Not (Are_At_Same_Loc (Trm_Occ 1, Trm_Occ 2))
         And
          Some_Numb (Numb 3,
           Some_Trm_Occ (Trm_Occ 3,
            (Is_Nth_Arg_Of (Trm_Occ 1, Numb 3, Trm_Occ 4)
           And
             Is_Nth_Arg_Of (Trm_Occ 2, Numb 3, Trm_Occ 4)
           And
            Some_Ind (Trm 5,
              ((Trm_Occ 1 Trm_Occ_Is_Of_Trm Trm 5)
              And
               (Trm_Occ 1 Trm_Occ_Is_Of_Trm Trm 5))
))))))))));

(* heuristic_17 *)
val no_diff_var_at_same_pos_for_diff_occ_of_rec =
 Not (Some_Rule (Rule 1, True))
Imply
 ((Some_Ind (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
     Some_Trm (Trm 2,
      Some_Trm_Occ_Of (Trm_Occ 21, Trm 2,
        ((Trm_Occ 21 Is_Defined_With Fun)
        Or
         (Trm_Occ 21 Is_Defined_With Function)
        Or
         (Trm_Occ 21 Is_Defined_With Inductive)
        Or
         (Trm_Occ 21 Is_Defined_With Primrec))
       And
        Some_Numb (Numb 5,
          Is_Nth_Arg_Of(Trm_Occ 1, Numb 5, Trm_Occ 21)
         And
          Some_Trm_Occ_Of (Trm_Occ 22, Trm 2,
            Some_Numb (Numb 6,
              (Trm_Occ 21 Is_At_Depth Numb 6)
             And
              (Trm_Occ 21 Is_At_Depth Numb 6))
           And
            Some_Trm (Trm 3,
              Not (Are_Same_Trm (Trm 1, Trm 3))
             And
              Some_Trm_Occ_Of (Trm_Occ 3, Trm 3,
               Is_Nth_Arg_Of (Trm_Occ 3, Numb 5, Trm_Occ 22))))))))))
 Imply
  Some_Ind (Trm 1,
    Some_Trm_Occ_Of (Trm_Occ 1, Trm 1,
     Some_Trm (Trm 2,
      Some_Trm_Occ_Of (Trm_Occ 21, Trm 2,
        ((Trm_Occ 21 Is_Defined_With Fun)
        Or
         (Trm_Occ 21 Is_Defined_With Function)
        Or
         (Trm_Occ 21 Is_Defined_With Inductive)
        Or
         (Trm_Occ 21 Is_Defined_With Primrec))
       And
        Some_Numb (Numb 5,
          Is_Nth_Arg_Of(Trm_Occ 1, Numb 5, Trm_Occ 21)
         And
          Pattern (Numb 5, Trm_Occ 21, All_Constr)
         And
          Some_Trm_Occ_Of (Trm_Occ 22, Trm 2,
            Some_Numb (Numb 6,
              (Trm_Occ 21 Is_At_Depth Numb 6)
             And
              (Trm_Occ 21 Is_At_Depth Numb 6))
           And
            Some_Trm (Trm 3,
              Not (Are_Same_Trm (Trm 1, Trm 3))
             And
              Some_Trm_Occ_Of (Trm_Occ 3, Trm 3,
               Is_Nth_Arg_Of (Trm_Occ 3, Numb 5, Trm_Occ 22)
               And
                Pattern (Numb 5, Trm_Occ 22, All_Constr))))))))))


(* heuristic_20 *)
val rule_inversion_on_premise =
 (  Some_Rule (Rule 1, True)
  And
    Some_Trm_Occ (Trm_Occ 1,
       (Trm_Occ 1 Is_Defined_With Inductive)
      And
       (Is_In_Prems (Trm_Occ 1))
    )
  )
Imply
  Some_Rule (Rule 2,
    Some_Trm_Occ (Trm_Occ 2,
       (Trm_Occ 2 Is_Defined_With Inductive)
      And
       (Is_In_Prems (Trm_Occ 2))
      And
       (Rule 2 Is_Rule_Of Trm_Occ 2)
    )
  );

end;
\<close>

setup\<open> Apply_LiFtEr.update_assert "heuristic_1" all_ind_term_are_non_const_wo_syntactic_sugar                           \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_2"  all_ind_terms_have_an_occ_as_variable_at_bottom                         \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_3"  all_ind_vars_are_arguments_of_a_recursive_function                      \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_4"  all_ind_vars_are_arguments_of_a_rec_func_where_pattern_match_is_complete\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_5"  all_ind_terms_are_arguments_of_a_const_with_a_related_rule_in_order     \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_6"  ind_is_not_arb                                                          \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_7" at_least_one_recursive_term                                              \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_8" at_least_one_on                                                          \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_9" one_on_is_deepest                                                        \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_10" ons_and_arbs_share_func \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_11" all_args_of_rule_as_ons \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_12" arb_share_parent_with_ind \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_13" no_arb_should_be_at_the_same_loc_as_ind \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_14" only_one_rule \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_15" inner_rec_const_rule \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_16" no_ind_at_nth_arg_if_two_occ_of_recs \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_17" no_diff_var_at_same_pos_for_diff_occ_of_rec \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_18" ind_is_not_arb \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_19" no_arb_should_be_at_the_same_loc_as_ind \<close> 
setup\<open> Apply_LiFtEr.update_assert "heuristic_20" rule_inversion_on_premise \<close> 

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
      val psl_modifierss             = Dynamic_Induct.pst_to_promising_modss state             : Dynamic_Induct.Induct_Seed.modifier list list;
      val lifter_modifierss          = map psl_ind_mods_to_lifter_ind_mods psl_modifierss      : LiFtEr_Util.ind_mods list;
      fun ind_mods_to_pair ind_mods  = ((pst_n_ind_mods_to_result_pair state ind_mods), ind_mods): (int * ind_mods);
      val pairs                      = Par_List.map ind_mods_to_pair lifter_modifierss                  : (int * LiFtEr_Util.ind_mods) list;
      val sorted_pairs               = sort (fn (p1, p2) => Int.compare (fst p1, fst p2)) pairs |> rev: (int * LiFtEr_Util.ind_mods) list;
      val _                   = tracing "Try these 10 most promising inductions!": unit;
      val best_pairs          = take 10 sorted_pairs;
      val fst_and_snd = ["1st candidate is ", "2nd candidate is "]
      val third_till_tenth = List.tabulate (11, I) |> map Int.toString |> drop 3 |> map (fn rank => rank ^ "th candidate is ");
      val fst_till_tenth   = fst_and_snd @ third_till_tenth;
      val ctxt                = Proof.context_of state            : Proof.context;
      val all_asserts         = (Symtab.dest o LiFtEr_Assertion.get) (Context.Proof ctxt);
      val numb_of_all_asserts = length all_asserts: int;
      fun ind_mdos_to_sendback ind_mods = lifter_ind_mods_to_psl_ind_mods ind_mods
                                       |> Dynamic_Induct.modifiers_to_str 
                                       |> Active.sendback_markup_properties [Markup.padding_command]: string;
      fun mk_message (i, mods) = ind_mdos_to_sendback mods ^
                                " (* The score is " ^ Int.toString i ^ " out of " ^ Int.toString numb_of_all_asserts ^ ". *)";
      val best_messages  = map mk_message best_pairs: strings;
      val numb_of_best_messages = length best_messages
      val best_mess_w_ranks = take numb_of_best_messages fst_till_tenth ~~ best_messages |>  map (op ^);
      val _                = map tracing best_mess_w_ranks;
    in () end);

end;
\<close>

ML\<open>
val _ = Outer_Syntax.command @{command_keyword smart_induct} "recommend which method to use." (Scan.succeed smart_induct_cmd);
\<close>

lemma "True"
  apply induct
  oops

end