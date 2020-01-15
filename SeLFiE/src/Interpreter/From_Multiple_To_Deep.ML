(*  Title:      PSL/SeLFeE/src/From_Quantifier_To_Multi_Arity.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
functor from_Multiple_to_Deep (*This does not have to be a functor. A structure will do.*)
 (structure Eval_Outer_Multiple:EVAL_MULTI_ARITY
  and       Outer_Path_To_Unode:PATH_TO_UNODE
  and       Eval_Inner_Multiple:EVAL_MULTI_ARITY
  and       Inner_Path_To_Unode:PATH_TO_UNODE
  sharing type Outer_Path_To_Unode.path = Eval_Outer_Multiple.path
  sharing type Inner_Path_To_Unode.path = Eval_Inner_Multiple.path): EVAL_DEEP =

struct

structure EOM = Eval_Outer_Multiple;
structure EIM = Eval_Inner_Multiple;
structure SU  = SeLFiE_Util;

type outer_path = EOM.path;
type inner_path = EIM.path;
type command    = Pattern.command;
type qtyp       = SeLFiE_Util.qtyp;

datatype outer_parameter = Outer_Path of outer_path | Outer_Non_Path of SeLFiE_Util.non_path_parameter;
datatype inner_parameter = Inner_Path of inner_path | Inner_Non_Path of SeLFiE_Util.non_path_parameter;

fun go_away_outer_parameter (Outer_Path     p ) = EOM.Path p
  | go_away_outer_parameter (Outer_Non_Path np) = EOM.Non_Path np;

fun come_back_outer_parameter (EOM.Path     p ) = Outer_Path     p
  | come_back_outer_parameter (EOM.Non_Path np) = Outer_Non_Path np;

fun go_away_inner_parameter (Inner_Path     p ) = EIM.Path p
  | go_away_inner_parameter (Inner_Non_Path np) = EIM.Non_Path np;

fun come_back_inner_parameter (EIM.Path     p ) = Inner_Path     p
  | come_back_inner_parameter (EIM.Non_Path np) = Inner_Non_Path np;

fun move_in_parameter (Outer_Non_Path np) = Inner_Non_Path np
  | move_in_parameter (Outer_Path     _)  = error "move_in_parameter in From_Multiple_To_Deep.ML failed. move_in_parameter is not defined for Outer_Path";

fun move_out_parameter (Inner_Non_Path np) = Outer_Non_Path np
  | move_out_parameter (Inner_Path    _) = error "move_out_parameter in From_Multiple_To_Deep.ML failed. move_out_parameter is not defined for Inner_Path";

datatype outer_expression =
  Outer_Variable of string
| Outer_Lambdas  of strings * outer_expression
| Outer_Applies  of outer_expression * outer_expression list
| Outer_Literal  of outer_parameter
| Outer_Assert   of SU.assert * outer_expression list
| Outer_Alls     of (string * qtyp) list * outer_expression
| Outer_Somes    of (string * qtyp) list * outer_expression
| Dive_In        of (outer_expression * inner_expression * outer_expression list)
and inner_expression =
  Inner_Variable of string
| Inner_Lambdas  of strings * inner_expression
| Inner_Applies  of inner_expression    * inner_expression list
| Inner_Literal  of inner_parameter
| Inner_Assert   of SU.assert * inner_expression list
| Inner_Alls     of (string * qtyp) list * inner_expression
| Inner_Somes    of (string * qtyp) list * inner_expression
| Dive_Deeper    of (inner_expression * inner_expression * inner_expression list);

fun come_back_outer_expression (EOM.Literal p) = come_back_outer_parameter p |> Outer_Literal
  | come_back_outer_expression _ = error "come_back_outer_expression in From_Multiple_To_Deep.ML failed."

fun come_back_inner_expression (EIM.Literal p) = come_back_inner_parameter p |> Inner_Literal
  | come_back_inner_expression _ = error "come_back_inner_expression in From_Multiple_To_Deep.ML failed."

datatype expr = Outer of outer_expression | Inner of inner_expression;

fun move_in_literal (Outer_Literal outer_param) = Inner_Literal (move_in_parameter outer_param): inner_expression
  | move_in_literal  _ = error "move_in_literal in From_Multiple_To_Deep.ML failed. move_in_literal is defined only for Outer_Literal.";

fun move_out_literal (Inner_Literal inner_param) = Outer_Literal (move_out_parameter inner_param): outer_expression
  | move_out_literal  _ = error "move_out_literal in From_Multiple_To_Deep.ML failed. move_out_literal is defined only for Outer_Literal.";

fun go_away_outer_literal (Outer_Literal outer_param) = EOM.Literal (go_away_outer_parameter outer_param)
  | go_away_outer_literal  _  = error "go_away_outer_literal in From_Multiple_To_Deep.ML failed. go_away_outer_literal is defined only for Outer_Literal."

fun go_away_inner_literal (Inner_Literal inner_param) = EIM.Literal (go_away_inner_parameter inner_param)
  | go_away_inner_literal  _  = error "go_away_outer_literal in From_Multiple_To_Deep.ML failed. go_away_outer_literal is defined only for Outer_Literal."

fun get_definitions_using_suffix (ctxt:Proof.context) (cname:string) (suffix:string) =
   try (Proof_Context.get_thms ctxt) (cname ^ "." ^ suffix)
|> these
|> map Thm.prop_of;

fun ctxt_n_cname_to_definitions_for_inductive (ctxt:Proof.context) (cname:string) =
   get_definitions_using_suffix ctxt cname "intros": terms;

fun ctxt_n_cname_to_definitions_for_primrec (ctxt:Proof.context) (cname:string) =
   get_definitions_using_suffix ctxt cname "simps": terms;

val ctxt_n_cname_to_definitions_for_fun = ctxt_n_cname_to_definitions_for_primrec;

fun ctxt_n_cname_to_definitions_for_function (ctxt:Proof.context) (cname:string) =
   get_definitions_using_suffix ctxt cname "psimps"
|> map Logic.strip_imp_concl: terms;

fun ctxt_n_cname_to_definitions (ctxt:Proof.context) (cname:string) =
  let
    val command = Pattern.get_command ctxt cname;
    fun command_to_definitions Pattern.Definition = [(*TODO*)]
      | command_to_definitions Pattern.Fun        = ctxt_n_cname_to_definitions_for_fun       ctxt cname
      | command_to_definitions Pattern.Primrec    = ctxt_n_cname_to_definitions_for_primrec   ctxt cname
      | command_to_definitions Pattern.Function   = ctxt_n_cname_to_definitions_for_function  ctxt cname
      | command_to_definitions Pattern.Inductive  = ctxt_n_cname_to_definitions_for_inductive ctxt cname
      | command_to_definitions Pattern.Unknown    = error "ctxt_n_cname_to_definitions in From_Multiple_To_Deep.ML faild. Unknown pattern!";
  in
    command_to_definitions command: terms
  end;

fun gen_path_to_definitions (pst:Proof.state) (term:term) path pst_n_term_n_path_to_cname =
  let
    val cname       = pst_n_term_n_path_to_cname pst term path                    : string option;
    val ctxt        = Proof.context_of pst                                        : Proof.context;
    val definitions = Option.map (ctxt_n_cname_to_definitions ctxt) cname |> these: terms;
  in
    definitions:terms
  end;

fun outer_literal_to_definitions (pst:Proof.state) (term:term) (Outer_Literal (Outer_Path (outer_path))) =
    gen_path_to_definitions pst term outer_path Outer_Path_To_Unode.pst_n_term_n_path_to_cname
  | outer_literal_to_definitions _ _ _ = error "outer_literal_to_simp_rules in From_Multiple_To_Deep.ML failed. outer_literal_to_simp_rules is defined only for Outer_Literal.";

fun inner_literal_to_definitions (pst:Proof.state) (term:term) (Inner_Literal (Inner_Path (inner_path))) =
    gen_path_to_definitions pst term inner_path Inner_Path_To_Unode.pst_n_term_n_path_to_cname
  | inner_literal_to_definitions  _ _ _ = error "inner_literal_to_simp_rules in From_Multiple_To_Deep.ML failed. inner_literal_to_simp_rules is defined only for Outer_Literal.";

fun eval_outer (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) (outer_expression:outer_expression) (trm:term) =
  let
    val eval_eom = EOM.eval trm pst induct_args;
    fun eval_outer' (Outer_Variable vname             ) = eval_eom (EOM.Variable vname)
      | eval_outer' (Outer_Lambdas (vnames, sub_expr )) = eval_eom (EOM.Lambdas (vnames, eval_outer' sub_expr))
      | eval_outer' (Outer_Applies (func,   args     )) = eval_eom (EOM.Applies (eval_outer' func, map eval_outer' args))
      | eval_outer' (Outer_Literal  parameter         ) = eval_eom (EOM.Literal (go_away_outer_parameter parameter))
      | eval_outer' (Outer_Assert  (assert, sub_exprs)) = eval_eom (EOM.Assert  (assert, map eval_outer' sub_exprs))
      | eval_outer' (Outer_Alls    (pairs,  sub_expr )) = eval_eom (EOM.Alls    (pairs, eval_outer' sub_expr))
      | eval_outer' (Outer_Somes   (pairs,  sub_expr )) = eval_eom (EOM.Somes   (pairs, eval_outer' sub_expr))
      | eval_outer' (Dive_In (target, Inner_Lambdas inner_lambda, outer_args)) =
        let
          val inner_args    = map move_in_literal outer_args                        : inner_expression list;
          val simp_rules    = outer_literal_to_definitions pst trm target           : term list;
          val inner_apps    = Inner_Applies (Inner_Lambdas inner_lambda, inner_args): inner_expression;
          val inner_results = map (eval_inner pst induct_args inner_apps) simp_rules: inner_expression list;
          val inner_ands    = Inner_Assert (SU.Ands, inner_results)                 : inner_expression;
          val inner_result  = eval_inner pst induct_args inner_ands Term.dummy      : inner_expression;
          val outer_result  = move_out_literal inner_result                         : outer_expression;
        in
          go_away_outer_literal outer_result
        end
      | eval_outer' (Dive_In _) = error "eval_outer' in From_Multiple_To_Deep.ML failed. An inner expression passed to eval_outer' for Dive_In has to be Inner_Lambda."
  in
    eval_outer' outer_expression |> come_back_outer_expression
  end
and eval_inner (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) (inner_expression:inner_expression) (trm:term) =
  let
    val eval_eim = EIM.eval trm pst induct_args;
    fun eval_inner' (Inner_Variable vname)              = eval_eim (EIM.Variable vname)
      | eval_inner' (Inner_Lambdas (vnames, sub_expr))  = eval_eim (EIM.Lambdas (vnames, eval_inner' sub_expr))
      | eval_inner' (Inner_Applies (func,   args     )) = eval_eim (EIM.Applies (eval_inner' func, map eval_inner' args))
      | eval_inner' (Inner_Literal  parameter         ) = eval_eim (EIM.Literal (go_away_inner_parameter parameter))
      | eval_inner' (Inner_Assert  (assert, sub_exprs)) = eval_eim (EIM.Assert  (assert, map eval_inner' sub_exprs))
      | eval_inner' (Inner_Alls    (pairs,  sub_expr )) = eval_eim (EIM.Alls    (pairs, eval_inner' sub_expr))
      | eval_inner' (Inner_Somes   (pairs,  sub_expr )) = eval_eim (EIM.Somes   (pairs, eval_inner' sub_expr))
      | eval_inner' (Dive_Deeper (target, Inner_Lambdas inner_lambda, inner_args)) =
        let
          val simp_rules    = inner_literal_to_definitions pst trm target           : term list;
          val inner_apps    = Inner_Applies (Inner_Lambdas inner_lambda, inner_args): inner_expression;
          val inner_results = map (eval_inner pst induct_args inner_apps) simp_rules: inner_expression list;
          val inner_ands    = Inner_Assert (SU.Ands, inner_results)                 : inner_expression;
          val inner_result  = eval_inner pst induct_args inner_ands Term.dummy      : inner_expression;
        in
          go_away_inner_literal inner_result
        end
      | eval_inner' (Dive_Deeper _) = error "eval_inner' in From_Multiple_To_Deep.ML failed. An inner expression passed to eval_inner' for Dive_Deeper has to be Inner_Lambda."
  in
    eval_inner' inner_expression |> come_back_inner_expression
  end;

fun eval (term:term) (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) (Outer outer_expr) = eval_outer pst induct_args outer_expr term |> Outer
  | eval _ _ _ _ = error "eval in From_Multiple_To_Deep.ML failed. eval is defined only for Outer.";

end;