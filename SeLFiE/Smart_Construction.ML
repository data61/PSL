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
  fun is_wellfounded (SU.Induct_Arguments {rules,...}) = rules = ["Wellfounded.accp.induct"];(*TODO: FIXME: termination proof for  goodsteinC in Goodstein.thy*)
  val induct_arguments = map (context_n_term_to_argument_powersets ctxt) terms
                      |> flat
                      |> distinct (op =)
                      |> powerset_to_induct_arguments
                      |> distinct (op =)
                      |> SU.sort_induct_argumentss
                      |> filter_out is_wellfounded: SeLFiE_Util.induct_arguments list;
  val _ = tracing ("Smart constuct produced " ^ Int.toString (length induct_arguments) ^ " combinations.");
in
  induct_arguments: SU.induct_arguments list
end;

val induct_arguments = Term.add_free_names;

end;