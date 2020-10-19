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

type func_print                       = string;
type manually_developed_ind_rule_name = string option;
type argument_prints                  = strings;
type seed_quadruple                   = Definition_Pattern.command * func_print * manually_developed_ind_rule_name * argument_prints;
type seed_quadruples                  = seed_quadruple list;

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
    (*quadruple_for_trancl_induct*)
    val const_names  = Term.add_const_names trm [];
    val has_trancl = exists (equal "Transitive_Closure.trancl") const_names;
    val quadruple_for_trancl_induct = if has_trancl
        then (
              [(Definition_Pattern.Unknown, "dummy", SOME "trancl_induct",  []),
               (Definition_Pattern.Unknown, "dummy", SOME "trancl_induct2", []),
               (Definition_Pattern.Unknown, "dummy", SOME "converse_trancl_induct",  []),
               (Definition_Pattern.Unknown, "dummy", SOME "converse_trancl_induct2", [])]): seed_quadruples
        else ([]);
    (*quadruple_for_tranclp_induct*)
    val has_tranclp = exists (equal "Transitive_Closure.tranclp") const_names;
    val quadruple_for_tranclp_induct = if has_tranclp
        then (
              [(Definition_Pattern.Unknown, "dummy", SOME "tranclp_induct",  []),
               (Definition_Pattern.Unknown, "dummy", SOME "tranclp_induct2", []),
               (Definition_Pattern.Unknown, "dummy", SOME "converse_tranclp_induct",  []),
               (Definition_Pattern.Unknown, "dummy", SOME "converse_tranclp_induct2", [])]): seed_quadruples
        else ([]);
    (*quadruple_for_rtrancl_induct*)
    val has_rtrancl = exists (equal "Transitive_Closure.rtrancl") const_names;
    val quadruple_for_rtrancl_induct = if has_rtrancl
        then (
              [(Definition_Pattern.Unknown, "dummy", SOME "rtrancl_induct",  []),
               (Definition_Pattern.Unknown, "dummy", SOME "rtrancl_induct2", []),
               (Definition_Pattern.Unknown, "dummy", SOME "converse_rtrancl_induct",  []),
               (Definition_Pattern.Unknown, "dummy", SOME "converse_rtrancl_induct2", [])]): seed_quadruples
        else ([]);
    (*quadruple_for_rtranclp_induct*)
    val has_rtranclp = exists (equal "Transitive_Closure.rtranclp") const_names;
    val quadruple_for_rtranclp_induct = if has_rtranclp
        then (
              [(Definition_Pattern.Unknown, "dummy", SOME "rtranclp_induct",  []),
               (Definition_Pattern.Unknown, "dummy", SOME "rtranclp_induct2", []),
               (Definition_Pattern.Unknown, "dummy", SOME "converse_rtranclp_induct",  []),
               (Definition_Pattern.Unknown, "dummy", SOME "converse_rtranclp_induct2", [])]): seed_quadruples
        else ([]);
    val trm_wo_abb      = Isabelle_Utils.contract_abbrevs ctxt trm               : term;
    val futrm_w_prnt    = UN.context_n_term_to_futrm_w_prnt_n_tag ctxt trm_wo_abb: UN.futrm_w_prnt_n_tag;
    fun futrm_w_prnt_n_tag_to_arguments (FUC_Prnt_Tag _) = []
      | futrm_w_prnt_n_tag_to_arguments (FUF_Prnt_Tag _) = []
      | futrm_w_prnt_n_tag_to_arguments (FUV_Prnt_Tag _) = []
      | futrm_w_prnt_n_tag_to_arguments (FUB_Prnt_Tag _) = []
      | futrm_w_prnt_n_tag_to_arguments (FUL_Prnt_Tag ( _, subtrm, _, _)) = futrm_w_prnt_n_tag_to_arguments subtrm
      | futrm_w_prnt_n_tag_to_arguments (app as FUA_Prnt_Tag (func, args, _, _)) =
      let
        fun futrm_w_prnt_n_tag_to_print futrm_w_prnt_n_tag = futrm_w_prnt_n_tag_to_tag_n_print futrm_w_prnt_n_tag |> snd: string;
        (*quadruple_for_list_induct2*)
        fun is_unary_func_taking func_name (FUA_Prnt_Tag (FUC_Prnt_Tag (cname,_,_,_), [arg], _, _)) = if cname = func_name then SOME (futrm_w_prnt_n_tag_to_print arg) else NONE
          | is_unary_func_taking _ _                                                                = NONE;
        val is_length_of = is_unary_func_taking "List.length";
        val is_size_of   = is_unary_func_taking "Nat.size_class.size";
        fun is_equation_of_lengths_of (FUA_Prnt_Tag (FUC_Prnt_Tag ("HOL.eq",_,_,_), [lhs, rhs], _, _)) =
            let
              val lhs_length_of_opt = is_length_of lhs: string option;
              val rhs_length_of_opt = is_length_of rhs: string option;
            in
              if   is_some lhs_length_of_opt andalso is_some rhs_length_of_opt
              then [the lhs_length_of_opt, the rhs_length_of_opt]
              else
                let
                  val lhs_size_of_opt = is_size_of lhs: string option;
                  val rhs_size_of_opt = is_size_of rhs: string option;
                in
                  if   is_some lhs_size_of_opt andalso is_some rhs_size_of_opt
                  then [the lhs_size_of_opt, the rhs_size_of_opt]
                  else []
                end
            end
          | is_equation_of_lengths_of _ = [];
        val quadruple_for_list_induct2 =
            if null (is_equation_of_lengths_of app)
            then []
            else ([(Definition_Pattern.Unknown, futrm_w_prnt_n_tag_to_print func, SOME "List.list_induct2", (is_equation_of_lengths_of app)(*[(*naively specifying induction terms here causes problems for lemma "length_mapi" in Hybrid_Logic.*)]*))]);
        (*quadruple_for_list_induct2'*)
        fun trm_is_of_list trm      = UN.futrm_w_prnt_n_tag_to_typ trm <$> Isabelle_Utils.is_list_typ |> Utils.is_some_true;
        fun all_trms_are_lists trms = forall (fn trm => trm_is_of_list trm) trms;
        val quadruple_for_list_induct2' = if length args = 2 andalso all_trms_are_lists args
            then ([(Definition_Pattern.Unknown, futrm_w_prnt_n_tag_to_print func, SOME "List.list_induct2'",  map futrm_w_prnt_n_tag_to_print args)]): seed_quadruples
            else ([]);
        (*quadruple_for_list_induct2'_due_to_map2*)
        fun is_app_of_map2 (FUA_Prnt_Tag (FUC_Prnt_Tag ("List.map2",_,_,_), [_, fst_arg, snd_arg], _, _)) = map futrm_w_prnt_n_tag_to_print [fst_arg, snd_arg]
          | is_app_of_map2 _ = [];
        val quadruple_for_list_induct2'_due_to_map2 = if null (is_app_of_map2 app)
            then []
            else ([(Definition_Pattern.Unknown, futrm_w_prnt_n_tag_to_print func, SOME "List.list_induct2'", is_app_of_map2 app)]): seed_quadruples;
        (*quadruple_for_list_all2*)
        val quadruple_for_list_all2 = if futrm_w_prnt_n_tag_to_print func = "List.list.list_all2" (*andalso length args = 3*)
            then ([(Definition_Pattern.Unknown, futrm_w_prnt_n_tag_to_print func, SOME "List.list_all2_induct",  map futrm_w_prnt_n_tag_to_print (drop 1 args))])
            else ([]);
        (*quadruple_for_inc_induct*)
        fun is_app_of_less_eq (FUA_Prnt_Tag (FUC_Prnt_Tag ("Orderings.ord_class.less_eq",_,_,_), [lhs, rhs], _, _)) = [lhs, rhs]
          | is_app_of_less_eq _ = [];
        val is_app_of_less_eq_on_nat = is_app_of_less_eq app |> map UN.futrm_w_prnt_n_tag_to_typ |> Utils.somes |> exists (Isabelle_Utils.is_typ_of_name "Nat.nat");(*TODO: This may miss out some cases where variables of type "nat" is "hidden" by lambda-abstraction or function application.*)
        val quadruple_for_inc_induct = if is_app_of_less_eq_on_nat
            then ([(Definition_Pattern.Unknown, futrm_w_prnt_n_tag_to_print func, SOME "Nat.inc_induct", [])]): seed_quadruples
            else ([]);
        (*quadruple_for_length_induct*)
        fun is_less_eq_of_lengths_of (FUA_Prnt_Tag (FUC_Prnt_Tag ("Orderings.ord_class.less_eq",_,_,_), [_, rhs], _, _)) =
            let
              val rhs_length_of_opt = is_length_of rhs: string option;
            in
              if   is_some rhs_length_of_opt
              then [the rhs_length_of_opt]
              else []
            end
          | is_less_eq_of_lengths_of _ = [];
        val quadruple_for_length_induct: seed_quadruples =
            if null (is_less_eq_of_lengths_of app)
            then []
            else [(Definition_Pattern.Unknown, futrm_w_prnt_n_tag_to_print func, SOME "List.length_induct", is_less_eq_of_lengths_of app)];

        (*quadruple_for_list_nonempty_induct_and_rev_nonempty_induct*)
        fun rhs_is_empty_and_lhs_of_eq_is (FUA_Prnt_Tag (FUC_Prnt_Tag ("HOL.not_equal",_,_,_), [lhs,rhs], _, _)) =
              if futrm_w_prnt_n_tag_to_print rhs = "List.list.Nil"
              then [futrm_w_prnt_n_tag_to_print lhs] else []
          | rhs_is_empty_and_lhs_of_eq_is  _ = [];
        fun nonempty_induct (equation): seed_quadruples =
            let
              val rhs_of_eq = rhs_is_empty_and_lhs_of_eq_is equation: strings;
            in
              case rhs_of_eq of
                 [rhs] =>  [(Definition_Pattern.Unknown, futrm_w_prnt_n_tag_to_print func, SOME "List.list_nonempty_induct", [rhs]),
                            (Definition_Pattern.Unknown, futrm_w_prnt_n_tag_to_print func, SOME "List.rev_nonempty_induct",  [rhs])]
              | _ => []
            end;
        val quadruple_for_nonempty_induct = nonempty_induct app
        (*standard quadruples*)
        val func_print_w_opt      = futrm_w_prnt_n_tag_to_tag_n_print func |> apfst #is_defined_with: (Definition_Pattern.command option * string);
        val (command, func_print) = if is_some (fst func_print_w_opt)
                                    then apfst the func_print_w_opt
                                    else (Definition_Pattern.Unknown, snd func_print_w_opt): (Definition_Pattern.command * func_print);
        val args_print            = map (snd o futrm_w_prnt_n_tag_to_tag_n_print) args: argument_prints;
        val results_from_subterms = map futrm_w_prnt_n_tag_to_arguments args |> flat: seed_quadruples;
      in
        (command, func_print, NONE, args_print)::results_from_subterms
        @ quadruple_for_trancl_induct
        @ quadruple_for_tranclp_induct
        @ quadruple_for_rtrancl_induct
        @ quadruple_for_rtranclp_induct
        @ quadruple_for_inc_induct
        @ quadruple_for_list_all2
        @ quadruple_for_list_induct2
        @ quadruple_for_list_induct2'
        @ quadruple_for_list_induct2'_due_to_map2
        @ quadruple_for_length_induct
        @ quadruple_for_nonempty_induct
        : seed_quadruples
      end;

    val func_args_pairs = futrm_w_prnt_n_tag_to_arguments futrm_w_prnt: seed_quadruples;
    fun func_args_pair_to_func_powerset_of_args_pair (command, func_print, ind_rule_opt, args:strings) =
        let
          val powerset_of_args = powerset args |> distinct (op =)                             : strings list;
          val pairs            = map (fn subset => (command, func_print, ind_rule_opt, subset)) powerset_of_args: seed_quadruples;
        in
          pairs
        end;
    val func_n_powerset_of_args_pairs = map func_args_pair_to_func_powerset_of_args_pair func_args_pairs |> flat: seed_quadruples;
  in
    func_n_powerset_of_args_pairs |> distinct (op =): seed_quadruple list
  end;

structure SU = SeLFiE_Util;

fun powerset_to_induct_arguments ([]:seed_quadruples) = []
  | powerset_to_induct_arguments ((command, func, NONE, args)::quadruples:seed_quadruples) =
    SU.Induct_Arguments {ons = args, arbs = [], rules = []}
 :: (case command of Definition_Pattern.Inductive_Set
         => SU.Induct_Arguments {ons = [], arbs = [], rules = [SU.Ind_Set (func)]}
     | _ => SU.Induct_Arguments {ons = args, arbs = [], rules = [SU.Ind_Rule (func ^ ".induct")]})
 :: powerset_to_induct_arguments quadruples
  | powerset_to_induct_arguments ((_, _, SOME ind_rule, args)::quadruples) =
    SU.Induct_Arguments {ons = args, arbs = [], rules = [SU.Hand_Rule ind_rule]}
 :: powerset_to_induct_arguments quadruples
 : SeLFiE_Util.induct_arguments list;

(*TODO: Do we really want is_not_string_of_const?*)
fun proof_state_to_induct_argumentss (pst:Proof.state) =
let
  val ctxt             = Proof.context_of pst;
  val terms            = Isabelle_Utils.pstate_to_1st_subg_n_chained_facts pst: term list;
  fun is_not_string_of_const (cname:string) = try (Syntax.read_term ctxt) cname <$> Term.is_Const |> Utils.is_some_false: bool;
  fun is_wellfounded (SU.Induct_Arguments {rules,...}) = rules = [SU.Ind_Rule "Wellfounded.accp.induct"];(*TODO: FIXME: termination proof for  goodsteinC in Goodstein.thy*)
  fun all_ons_meet_condition (SU.Induct_Arguments {ons,rules,...}) = (forall is_not_string_of_const ons) andalso 
      (case rules of
         [SU.Ind_Set   _] => true
       | [SU.Hand_Rule _] => true
       |  _               => not (null ons)): bool;
  fun rule_name_is_defined rule_name = try (Proof_Context.get_thm ctxt) rule_name |> is_some;
  fun all_rules_exist (SU.Induct_Arguments {rules,...}) = forall (rule_name_is_defined o SU.rule_or_set_to_string) rules
  val induct_arguments = map (context_n_term_to_argument_powersets ctxt) terms
                      |> flat
                      |> distinct (op =)
                      |> powerset_to_induct_arguments
                      |> distinct (op =)
                      |> filter all_ons_meet_condition (*TODO: we should do something better than this.*)
                      |> filter all_rules_exist
                      |> filter_out is_wellfounded
                      |> SU.sort_induct_argumentss: SeLFiE_Util.induct_arguments list;
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