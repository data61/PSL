(*  Title:      PSL/SeLFiE/Smart_Construction.ML
 *  Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
 *)
structure Smart_Construction =
struct

open UN

fun futrm_w_prnt_n_tag_to_tag_n_print (FUC_Prnt_Tag (_, _, print, tag)) = (tag, print)
  | futrm_w_prnt_n_tag_to_tag_n_print (FUF_Prnt_Tag (_, _, print, tag)) = (tag, print)
  | futrm_w_prnt_n_tag_to_tag_n_print (FUV_Prnt_Tag (_, _, print, tag)) = (tag, print)
  | futrm_w_prnt_n_tag_to_tag_n_print (FUB_Prnt_Tag (_, _, print, tag)) = (tag, print)
  | futrm_w_prnt_n_tag_to_tag_n_print (FUL_Prnt_Tag (_, _, print, tag)) = (tag, print)
  | futrm_w_prnt_n_tag_to_tag_n_print (FUA_Prnt_Tag (_, _, print, tag)) = (tag, print);

type command_n_print = (Definition_Pattern.command * string);

fun futrm_w_prnt_n_tag_to_arguments (FUC_Prnt_Tag _) = []
  | futrm_w_prnt_n_tag_to_arguments (FUF_Prnt_Tag _) = []
  | futrm_w_prnt_n_tag_to_arguments (FUV_Prnt_Tag _) = []
  | futrm_w_prnt_n_tag_to_arguments (FUB_Prnt_Tag _) = []
  | futrm_w_prnt_n_tag_to_arguments (FUL_Prnt_Tag ( _, subtrm, _, _)) = futrm_w_prnt_n_tag_to_arguments subtrm
  | futrm_w_prnt_n_tag_to_arguments (FUA_Prnt_Tag (func, args, _, _)) =
  let
    val func_print_w_opt      = futrm_w_prnt_n_tag_to_tag_n_print func |> apfst #is_defined_with: (Definition_Pattern.command option * string);
    val func_print            = if is_some (fst func_print_w_opt)
                                then apfst the func_print_w_opt
                                else (Definition_Pattern.Unknown, snd func_print_w_opt): command_n_print;
    val args_print            = map (snd o futrm_w_prnt_n_tag_to_tag_n_print) args: strings;
    val results_from_subterms = map futrm_w_prnt_n_tag_to_arguments args |> flat: (command_n_print * strings) list;
  in
    (func_print, args_print)::results_from_subterms: (command_n_print * strings) list
  end;

(*ordered_set_to_ordered_powerset*)
fun powerset (xs:'a list) =
  let
    fun poset ([]        , base) = [base]
      | poset (head::tail, base) = (poset (tail, base)) @ (poset (tail, base @ [head]))
  in
    poset (xs, [])
  end;

fun context_n_term_to_argument_powersets (ctxt:Proof.context) (trm:term) =
  let
    val trm_wo_abb      = Isabelle_Utils.contract_abbrevs ctxt trm               : term;
    val futrm_w_prnt    = UN.context_n_term_to_futrm_w_prnt_n_tag ctxt trm_wo_abb: UN.futrm_w_prnt_n_tag;
    val func_args_pairs = futrm_w_prnt_n_tag_to_arguments futrm_w_prnt           : (command_n_print * strings) list;
    fun func_args_pair_to_func_powerset_of_args_pair (command_n_print:command_n_print, args:strings) =
        let
          val powerset_of_args = powerset args |> distinct (op =)                             : strings list;
          val pairs            = map (fn subset => (command_n_print, subset)) powerset_of_args: (command_n_print * strings) list;
        in
          pairs
        end;
    val func_n_powerset_of_args_pairs = map func_args_pair_to_func_powerset_of_args_pair func_args_pairs |> flat: (command_n_print * strings) list;
  in
    func_n_powerset_of_args_pairs |> distinct (op =): (command_n_print * strings) list
  end;

structure SU = SeLFiE_Util;

fun powerset_to_induct_arguments [] = []
  | powerset_to_induct_arguments (((command, func), args)::pairs) =
    SU.Induct_Arguments {ons = args, arbs = [], rules = []}
 :: (case command of Definition_Pattern.Inductive_Set
         => (SU.Induct_Arguments {ons = [],   arbs = [], rules = [SU.Ind_Set (func)]} |> (tracing o SU.induct_arguments_to_string); SU.Induct_Arguments {ons = [],   arbs = [], rules = [SU.Ind_Set (func)]})
     | _ => SU.Induct_Arguments {ons = args, arbs = [], rules = [SU.Ind_Rule (func ^ ".induct")]})
 :: powerset_to_induct_arguments pairs;

(*TODO: Do we really want is_not_string_of_const?*)
fun proof_state_to_induct_argumentss (pst:Proof.state) =
let
  val ctxt             = Proof.context_of pst;
  val terms            = Isabelle_Utils.pstate_to_1st_subg_n_chained_facts pst: term list;
  fun is_not_string_of_const (cname:string) = try (Syntax.read_term ctxt) cname <$> Term.is_Const |> Utils.is_some_false: bool;
  fun is_wellfounded (SU.Induct_Arguments {rules,...}) = rules = [SU.Ind_Rule "Wellfounded.accp.induct"];(*TODO: FIXME: termination proof for  goodsteinC in Goodstein.thy*)
  fun all_ons_meet_condition (SU.Induct_Arguments {ons,rules,...}) = (forall is_not_string_of_const ons) andalso 
      (case rules of
         [SU.Ind_Set  _ ] => true
       |  _               => not (null ons)): bool;
  val induct_arguments = map (context_n_term_to_argument_powersets ctxt) terms
                      |> flat
                      |> distinct (op =)
                      |> powerset_to_induct_arguments
                      |> distinct (op =)
                      |> SU.sort_induct_argumentss
                      |> filter all_ons_meet_condition (*TODO: we should do something better than this.*)
                      |> filter_out is_wellfounded: SeLFiE_Util.induct_arguments list;
(*
val _ = (map (tracing o SU.induct_arguments_to_string) induct_arguments);
val _ = tracing ("Smart constuct produced " ^ Int.toString (length induct_arguments) ^ " combinations.");*)
in
  induct_arguments: SU.induct_arguments list
end;

fun proof_state_n_terms_n_score_n_induct_arguments_to_score_n_induct_argumentss_w_arbs (pst:Proof.state) (trms:terms) (score, SU.Induct_Arguments {ons, rules,...}) =
  let
    val ctxt              = Proof.context_of pst;
    val trms_wo_abb       = map (Isabelle_Utils.contract_abbrevs ctxt) trms               : terms;
    val free_names        = fold Term.add_free_names trms_wo_abb []  |> distinct (op =)   : strings;
    val fnames_not_in_ons = filter_out (member (op =) ons) free_names                     : strings;
    val arbss             = powerset fnames_not_in_ons: strings list;(*TODO: refactor with proof_state_to_induct_argumentss.*)
    fun mk_new_pair arbs  = (score, SU.Induct_Arguments {ons=ons, arbs=arbs, rules=rules}): (real * SU.induct_arguments);
    val induct_argss      = map mk_new_pair arbss                                         : (real * SU.induct_arguments) list;
  in
    induct_argss: (real * SU.induct_arguments) list
  end;

fun proof_state_n_terms_n_induct_argumentss_to_induct_argumentss_w_arbs (pst:Proof.state) (trms:terms) (score_n_argss:(real * SU.induct_arguments) list) =
   map (fn score_n_args => proof_state_n_terms_n_score_n_induct_arguments_to_score_n_induct_argumentss_w_arbs pst trms score_n_args) score_n_argss
|> flat:  (real * SeLFiE_Util.induct_arguments) list;

end;