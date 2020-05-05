(*  Title:      Smart_Induct/src/Multi_Stage_Screening.thy
    Author:     Yutaka Nagashima, CIIRC, CTU, University of Innsbruck
*)
structure Multi_Stage_Screening =
struct

open Dynamic_Induct

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
(*This is harmful:
  val non_is_substring_modss = filter_out (post_is_in_pre_when_printed pst) functioning_modifiers: ITG.modifiers list;
*)
  (*val _                      = tracing ("... out of which only " ^ Int.toString (length non_is_substring_modss) ^ " of them return a first goal that does not contain the original first goal as its sub-term.");*)
  val no_sche_introducing_modss = filter (no_sch_in_pre_but_in_post pst) (*non_is_substring_modss*)functioning_modifiers: ITG.modifiers list;
  val _                         = tracing ("... out of which only " ^ Int.toString (length no_sche_introducing_modss) ^ " of them passes the second screening stage.");
  val first_modss    = take 1000 no_sche_introducing_modss                      : ITG.modifiers list;
  val _ = tracing ("LiFtEr assertions are evaluating the first " ^ Int.toString (length first_modss) ^ " of them.");
in
  first_modss
end;

end;