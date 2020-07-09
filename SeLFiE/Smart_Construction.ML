(*  Title:      PSL/SeLFiE/Smart_Construction.ML
 *  Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
 *)
structure Smart_Construction =
struct

open UN

fun futrm_w_prnt_to_print (FUC_Prnt (_, _,    print)) = print
  | futrm_w_prnt_to_print (FUF_Prnt (_, _,    print)) = print
  | futrm_w_prnt_to_print (FUV_Prnt (_, _,    print)) = print
  | futrm_w_prnt_to_print (FUB_Prnt (_, _,    print)) = print
  | futrm_w_prnt_to_print (FUL_Prnt (_, _, _, print)) = print
  | futrm_w_prnt_to_print (FUA_Prnt (_, _,    print)) = print;

fun futrm_w_prnt_to_arguments (FUC_Prnt _) = []
  | futrm_w_prnt_to_arguments (FUF_Prnt _) = []
  | futrm_w_prnt_to_arguments (FUV_Prnt _) = []
  | futrm_w_prnt_to_arguments (FUB_Prnt _) = []
  | futrm_w_prnt_to_arguments (FUL_Prnt (_, _, subtrm, _)) = futrm_w_prnt_to_arguments subtrm
  | futrm_w_prnt_to_arguments (FUA_Prnt (func, args, _)) =
  let
    val func_print            = futrm_w_prnt_to_print func                : string;
    val args_print            = map futrm_w_prnt_to_print args            : strings;
    val results_from_subterms = map futrm_w_prnt_to_arguments args |> flat: (string * strings) list;
  in
    (func_print, args_print)::results_from_subterms: (string * strings) list
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
    val futrm_w_prnt    = UN.context_n_term_to_futrm_w_prnt ctxt trm: UN.futrm_w_prnt;
    val func_args_pairs = futrm_w_prnt_to_arguments futrm_w_prnt    : (string * strings) list;
    fun func_args_pair_to_func_powerset_of_args_pair (func:string, args:strings) =
        let
          val powerset_of_args = powerset args |> distinct (op =): strings list;
          val pairs = map (fn subset => (func, subset)) powerset_of_args: (string * strings) list;
        in
          pairs
        end;
    val func_n_powerset_of_args_pairs = map func_args_pair_to_func_powerset_of_args_pair func_args_pairs |> flat: (string * strings) list;
  in
    func_n_powerset_of_args_pairs |> distinct (op =) : (string * strings) list
  end;

structure SU = SeLFiE_Util;

fun powerset_to_induct_arguments [] = []
  | powerset_to_induct_arguments ((func, args)::pairs) =
    SU.Induct_Arguments {ons = args, arbs = [], rules = []}
 :: SU.Induct_Arguments {ons = args, arbs = [], rules = [func ^ ".induct"]}
 :: powerset_to_induct_arguments pairs;

fun proof_state_to_induct_argumentss (pst:Proof.state) =
let
  val ctxt             = Proof.context_of pst;
  val terms            = Isabelle_Utils.pstate_to_1st_subg_n_chained_facts pst: term list;
  val pretty_printed_terms = map (Isabelle_Utils.trm_to_string (Proof_Context.set_mode Proof_Context.mode_default ctxt)) terms |> String.concat: string;
  fun is_string_of_const (cname:string) = try (Syntax.read_term ctxt) cname <$> Term.is_Const |> Utils.is_some_true: bool;
  fun is_wellfounded (SU.Induct_Arguments {rules,...}) = rules = ["Wellfounded.accp.induct"];(*TODO: FIXME: termination proof for  goodsteinC in Goodstein.thy*)
  fun is_const_or_unabbreviated (on:string) = is_string_of_const on orelse String.isSubstring on pretty_printed_terms;
  fun all_ons_meet_condition (SU.Induct_Arguments {ons,...}) = (forall is_const_or_unabbreviated ons) andalso not (null ons): bool
  val induct_arguments = map (context_n_term_to_argument_powersets ctxt) terms
                      |> flat
                      |> distinct (op =)
                      |> powerset_to_induct_arguments
                      |> distinct (op =)
                      |> SU.sort_induct_argumentss
                      |> filter all_ons_meet_condition (*TODO: we should do something better than this.*)
                      |> filter_out is_wellfounded: SeLFiE_Util.induct_arguments list;
  val _ = tracing ("Smart constuct produced " ^ Int.toString (length induct_arguments) ^ " combinations.");
in
  induct_arguments: SU.induct_arguments list
end;

fun proof_state_n_terms_n_score_n_induct_arguments_to_score_n_induct_argumentss_w_arbs (pst:Proof.state) (trms:terms) (score, SU.Induct_Arguments {ons, rules,...}) =
  let
    val free_names           = fold Term.add_free_names trms []  |> distinct (op =)          : strings;
    val fnames_not_in_ons    = filter_out (member (op =) ons) free_names                     : strings;
    val ctxt                 = Proof.context_of pst;
    val terms                = Isabelle_Utils.pstate_to_1st_subg_n_chained_facts pst         : term list;
    val pretty_printed_terms = map (Isabelle_Utils.trm_to_string (Proof_Context.set_mode Proof_Context.mode_default ctxt)) terms |> String.concat: string;
    fun fname_appears_in_terms (fvar_name:string) = String.isSubstring (fvar_name ^ " ") pretty_printed_terms
                                             orelse String.isSubstring (" " ^ fvar_name) pretty_printed_terms
                                             orelse String.isSubstring ("(" ^ fvar_name) pretty_printed_terms
                                             orelse String.isSubstring (fvar_name ^ ")") pretty_printed_terms;
    val arbss             = powerset fnames_not_in_ons
                         |> filter (forall fname_appears_in_terms)                        : strings list;(*TODO: we can do better than this. refactor with proof_state_to_induct_argumentss.*)
    fun mk_new_pair arbs  = (score, SU.Induct_Arguments {ons=ons, arbs=arbs, rules=rules}): (int * SU.induct_arguments);
    val induct_argss      = map mk_new_pair arbss                                         : (int * SU.induct_arguments) list;
  in
    induct_argss: (int * SU.induct_arguments) list
  end;

fun proof_state_n_terms_n_induct_argumentss_to_induct_argumentss_w_arbs (pst:Proof.state) (trms:terms) (score_n_argss:(int * SU.induct_arguments) list) =
   map (fn score_n_args => proof_state_n_terms_n_score_n_induct_arguments_to_score_n_induct_argumentss_w_arbs pst trms score_n_args) score_n_argss
|> flat:  (int * SeLFiE_Util.induct_arguments) list;

end;