(*  Title:      SeLFiE/Multi_Stage_Screening_For_SeLFiE.thy
    Author:     Yutaka Nagashima, CIIRC, CTU, University of Innsbruck
*)
structure Screening =
struct

structure IU = Isabelle_Utils;
structure SU = SeLFiE_Util;

fun induction_arguments_to_tactic_on_proof_state (ind_args:SU.induct_arguments) (proof_state:Proof.state) =
  let
    val ctxt               = Proof.context_of proof_state                                        : Proof.context;
    val meth_as_str        = SU.induct_arguments_to_string ind_args                              : string;
    val meth               = Utils.rm_parentheses meth_as_str                                    : string;
    fun split str          = let val strs = space_explode " " str in (hd strs, tl strs) end      : string * string list;
    val hd_tl              = split meth                                                          : string * string list;
    val tokens             = Dynamic_Utils.str_to_tokens ctxt (String.concatWith " " (snd hd_tl)): Token.T list;
    val src                = Token.make_src (fst hd_tl, Position.none) tokens                    : Token.src;
    val checked_src        = Dynamic_Utils.check_src ctxt src                                    : Token.src;
    val text               = Method.Source checked_src                                           : Method.text;
    val text_range         = (text, (Position.none, Position.none))                              : Method.text_range;
    val applied_text_range = Proof.apply text_range                                              : Proof.state -> Proof.state Seq.result Seq.seq;
    val results            = applied_text_range proof_state                                      : Proof.state Seq.result Seq.seq;
    val filtered_results   = Seq.filter_results results                                          : Proof.state Seq.seq;
  in
    filtered_results
  end;

fun induction_arguments_to_tactic_on_proof_state_w_timeout (ind_args:SU.induct_arguments) pst =
  let
    val tactic_on_proof_state_result = Seq2.try_seq (IU.TIMEOUT_in 3.0 (induction_arguments_to_tactic_on_proof_state ind_args)) pst;
    val result                       = (tactic_on_proof_state_result);
  in
    result
  end;

fun if_no_schematic_in_pre_then_no_schematic_in_post (pre_fst_goal:term, post_fst_goal:term) =
  let
    fun no_sche_in trm    = Term.add_var_names trm [] |> null               : bool;
    val no_sche_in_post   = no_sche_in post_fst_goal                        : bool;
    val no_sche_in_pre    = no_sche_in pre_fst_goal                         : bool;
    val result            = if no_sche_in_pre then no_sche_in_post else true: bool;
  in
    result
  end;

fun pre_to_post_transition_is_promising (pre_fst_goal:term, post_fst_goal:term) =
  if_no_schematic_in_pre_then_no_schematic_in_post (pre_fst_goal, post_fst_goal) andalso not (pre_fst_goal = post_fst_goal);

fun induct_arguments_is_promising_for_proof_state (pst:Proof.state) (score:real, ind_args:SU.induct_arguments) =
  let
    val pre_first_goal_opt    = IU.pst_to_fst_subg pst                                                        : term option;
    val tactic_w_timeout      = Seq2.try_seq (induction_arguments_to_tactic_on_proof_state_w_timeout ind_args): Proof.state -> Proof.state Seq.seq;
    val tactic_results_pst    = IU.TIMEOUT_in 3.0 tactic_w_timeout pst                                        : Proof.state Seq.seq;
    val post_proof_state_opt  = try Seq.hd tactic_results_pst                                                 : Proof.state option;
    val post_first_goal_opt   = post_proof_state_opt >>= IU.pst_to_fst_subg                                   : term option;
    val option_pair           = Utils.mk_option_pair (pre_first_goal_opt, post_first_goal_opt)                : (term * term) option;
    val is_promising          = if   is_some pre_first_goal_opt
                                then Utils.is_some_true (option_pair <$> pre_to_post_transition_is_promising)
                                else false: bool;
  in
    (score, ind_args, is_promising): (real * SU.induct_arguments * bool)(*true is good*)
  end;

local

type quadruple  =  (real * SeLFiE_Util.induct_arguments * bool);
type quadruples = quadruple list;

fun show_how_many_survived (numb_surviving_combs:int) (numb_original_combs:int) (numb_of_step:int) = ()
(*tracing ("smart_induct: only " ^ Int.toString numb_surviving_combs ^ " combinations survived Step " ^ Int.toString numb_of_step ^ " out of " ^ Int.toString numb_original_combs);
 *)
fun pst_n_score_n_induct_argumentss_to_quadruples (pst:Proof.state) (score_n_induct_argumentss:(real * SU.induct_arguments) list) =
  Par_List.map (induct_arguments_is_promising_for_proof_state pst) score_n_induct_argumentss

in
(*TODO: rename some outdated names.*)
fun proof_state_to_promising_induct_argumentss_wo_arbs_n_resultss (pst:Proof.state) =
  let
    val induct_argumentss        = Smart_Construction.proof_state_to_induct_argumentss pst                      : SU.induct_arguments list;
    val zero_w_induct_argumentss = map (fn induct_arg => (0.0, induct_arg)) induct_argumentss                   : (real * SU.induct_arguments) list;
    val quadruples               = pst_n_score_n_induct_argumentss_to_quadruples pst zero_w_induct_argumentss   : quadruples;
    val promising_args           = filter (fn (_, _, b) => b) quadruples |> map (fn (score, a, _) => (score, a)): (real * SU.induct_arguments) list;
    val _ = show_how_many_survived (length promising_args) (length induct_argumentss) 2: unit;
  in
    promising_args: (real * SU.induct_arguments) list
  end;

fun induct_argumentss_n_proof_state_to_promising_induct_argumentss_w_arbs_n_resultss
  (score_n_induct_argumentss:(real * SU.induct_arguments) list) (pst:Proof.state) =
  let
    fun ord_triple ((_, args1), (_, args2)) = SU.ord_induct_arguments (args1, args2): order;
    val sorted_promisings = sort ord_triple score_n_induct_argumentss;
    val _                 = show_how_many_survived (length score_n_induct_argumentss) (length score_n_induct_argumentss) 4: unit;
  in
    sorted_promisings: (real * SU.induct_arguments) list
  end;

end;

end;