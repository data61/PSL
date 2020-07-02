theory Smart_Construction
imports SeLFiE
begin

ML\<open>

local

open UN

in

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
  val induct_arguments = map (context_n_term_to_argument_powersets ctxt) terms
                      |> flat
                      |> distinct (op =)
                      |> powerset_to_induct_arguments: SeLFiE_Util.induct_arguments list;
in
  induct_arguments: SU.induct_arguments list
end;

val _ = SU.induct_arguments_to_string: SU.induct_arguments -> string;
(* TODO: using smart_induct, implement an Isar command, semantic_induct *)

end;

\<close>

ML_file "Multi_Stage_Screening_For_SeLFiE.ML"

ML\<open>
(*
 * 1. apply all induction heuristics and give points to each result
 * 1a. collect all the modifier combinations for induction without generalization.
 * 1b. apply all induction heuristics to each of them and count scores. Use some code base for smart_induct
 *     (fst o Multi_Stage_Screening.proof_state_to_promising_induct_argumentss_n_resultss) pst
 * 2. apply all generalization heuristics and give points to each result
 *)
infix 1 >>= <$> <|> <*>;
fun (m >>= f) = Option.mapPartial f m;
fun (m <$> f) = Option.map f m;
fun (f <*> m) = Utils.opt_app f m;
fun (NONE   <|> NONE  ) = NONE
  | (NONE   <|> SOME x) = SOME x
  | (SOME x <|> NONE  ) = SOME x
  | (SOME x <|> SOME _) = SOME x

structure SeLFiE_Heuristics =
struct



end;
\<close>

end