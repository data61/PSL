(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Deep_Bound.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** EVAL_UNARY ***)
signature EVAL_UNARY =
sig

datatype expr =
  Bound     of int
| Lambda    of expr
| Apply     of expr * expr
| Literal   of Eval_Parameter.literal
| Assert    of SeLFiE_Util.assert * expr list
| Dive_In   of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| Deep_Dive of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| All       of SeLFiE_Util.qtyp * expr
| Some      of SeLFiE_Util.qtyp * expr;

val eval: Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;

(*** Eval_Unary ***)
structure Eval_Unary: EVAL_UNARY =
struct

structure EPWB = Eval_Parameter_With_Bool;
structure SU   = SeLFiE_Util;
structure EP   = Eval_Parameter;

type command = Pattern.command;

datatype expr =
  Bound     of int
| Lambda    of expr
| Apply     of expr * expr
| Literal   of Eval_Parameter.literal
| Assert    of SU.assert * expr list
| Dive_In   of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| Deep_Dive of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| All       of SeLFiE_Util.qtyp * expr
| Some      of SeLFiE_Util.qtyp * expr;

local

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

fun ctxt_n_cname_to_definitions (ctxt:Proof.context) (cname:string) :terms =
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

in

fun outer_literal_to_definitions (pst:Proof.state) (term:term) (EP.Outer_Path (outer_path)) =
    gen_path_to_definitions pst term outer_path Outer_Path_To_Unode.pst_n_term_n_path_to_cname
  | outer_literal_to_definitions _ _ _ = error "outer_literal_to_simp_rules in From_Multiple_To_Deep.ML failed. outer_literal_to_simp_rules is defined only for Outer_Literal.";

fun inner_literal_to_definitions (pst:Proof.state) (term:term) (EP.Inner_Path (inner_path)) =
    gen_path_to_definitions pst term inner_path Inner_Path_To_Unode.pst_n_term_n_path_to_cname
  | inner_literal_to_definitions  _ _ _ = error "inner_literal_to_simp_rules in From_Multiple_To_Deep.ML failed. inner_literal_to_simp_rules is defined only for Outer_Literal.";

end;

fun shift 0 _ u                     = u
  | shift i d (Bound j)             = if j >= d then Bound (j+i) else Bound j
  | shift i d (Lambda t)            = Lambda (shift i (d+1) t)
  | shift i d (Apply (t, u))        = Apply (shift i d t, shift i d u)
  | shift _ _ (Literal param)       = Literal param
  | shift i d (Assert (ass, exprs)) = Assert (ass, map (shift i d) exprs)
  | shift _ _ (Dive_In _)           = error "shift is not defined for Dive_In"
  | shift _ _ (Deep_Dive _)         = error "shift is not defined for Deep_Dive"
  | shift _ _ (All _)               = error "shift is not defined for All"
  | shift _ _ (Some _)              = error "shift is not defined for Some";

fun subst i u (Bound j) =
      if      j < i then Bound j (*locally bound*)
      else if j = i then shift i 0 u
      else               Bound (j-1)
  | subst i u (Lambda t)               = Lambda (subst (i+1) u t)
  | subst i u (Apply (t1, t2))         = Apply (subst i u t1, subst i u t2)
  | subst _ _ (Literal param)          = Literal param
  | subst i u (Assert (ass, exprs))    = Assert (ass, map (subst i u) exprs)
  | subst i u (Dive_In   (t, l, args)) = Dive_In   (subst i u t, subst i u l, map (subst i u) args)
  | subst i u (Deep_Dive (t, l, args)) = Deep_Dive (subst i u t, subst i u l, map (subst i u) args)
  | subst i u (All  (typ, expr))       = All  (typ, subst (i+1) u expr)
  | subst i u (Some (typ, expr))       = Some (typ, subst (i+1) u expr)

fun print_expr (Bound i)            = "B.Bound " ^ Int.toString i ^ " "
  | print_expr (Lambda expr)        = "B.Lambda (" ^ print_expr expr ^ " ) "
  | print_expr (Apply (exp1, exp2)) = "B.Apply (" ^ print_expr exp1 ^ ", " ^ print_expr exp2 ^ ") "
  | print_expr (Literal p) = " B.Literal " ^ (case p of
       EP.Outer_Path _ => "Outer_Path"
     | EP.Inner_Path _ => "Inner_Path"
     | EP.Non_Path non_path  => case non_path of
         EP.Bool    b => if b then "True" else "False"
       | EP.Print   _ => "print!"
       | EP.Number  _ => "number!"
       | EP.Command _ => "command!")
  | print_expr (Assert (_, expres)) = "B.Assert " ^ (fold_rev (curry (op ^)) (map print_expr expres) " ")
  | print_expr (Dive_In   (target, lambda, args)) = "B.Dive_In ( "   ^ print_expr target ^ ", " ^ print_expr lambda ^ ", " ^ (String.concat o map print_expr) args ^ ") "
  | print_expr (Deep_Dive (target, lambda, args)) = "B.Deep_Dive ( " ^ print_expr target ^ ", " ^ print_expr lambda ^ ", " ^ (String.concat o map print_expr) args ^ ") "
  | print_expr (All (typ, expr)) = "B.All ( "  ^ SU.print_qtyp typ ^ ", " ^ print_expr expr ^ " ) "
  | print_expr (Some (typ, expr)) = "B.All ( " ^ SU.print_qtyp typ ^ ", " ^ print_expr expr ^ " ) ";

fun param_with_bool_to_bound (Literal param) = param
  | param_with_bool_to_bound  expr           =
    let
      val mssg = print_expr expr;
    in
      error ("eval_prim in Eval_Bound failed with " ^ mssg)
    end;

fun check_all_args_are_non_path_lits  []                           = true
  | check_all_args_are_non_path_lits (Literal (EP.Non_Path _)::ls) = check_all_args_are_non_path_lits ls
  | check_all_args_are_non_path_lits _ = error "check_all_args_are_non_path_lits only takes non_paths.";

fun mk_nested_app func []          = func
  | mk_nested_app func (arg::args) = mk_nested_app (Apply (func, arg)) args;

fun mk_nested_lamb (Lambda lambda) 0 = Lambda lambda
  | mk_nested_lamb (Lambda lambda) n = if n = ~1 then lambda else
                                       if n < 0  then error "mk_nested_lamb failed." else Lambda (mk_nested_lamb lambda (n - 1))
  | mk_nested_lamb expr n = error ("mk_nested_lamb failed with " ^ print_expr expr ^ Int.toString n);

fun mk_inner_expr (lamb as Lambda _) (arguments:expr list) =
    mk_nested_app (mk_nested_lamb lamb (length arguments - 1)) arguments
  | mk_inner_expr _ _ = error "mk_inner_expr failed!"

fun eval (pst:Proof.state) (induct_args:SU.induct_arguments) (expr:expr) =
  let
    fun subexpr_n_qtyp_to_apps (subexpr:expr) (qtyp:SU.qtyp) (ands_or_ors:SU.assert) (trm:term) =
      let
        val params = Quantifier_Domain.qtyp_to_qdomain qtyp pst trm induct_args    : Eval_Parameter.literals;
        val apps   = map (fn param => Apply (Lambda subexpr, Literal param)) params: expr list;
      in
        Assert (ands_or_ors, apps): expr
      end;
    val thm      = Isabelle_Utils.proof_state_to_thm pst: thm;
    val thm_term = Thm.prop_of thm                      : term;
    fun eval' (Apply (func, arg)) term =
         (case eval' func term of
          Lambda  u   => eval' (subst 0 (eval' arg term) u) term
        | Literal l   => Literal l
        | Bound   i   => Bound i
        | Dive_In t   => Dive_In t
        | Deep_Dive t => Deep_Dive t
        | u1          => Apply (u1, eval' arg term))
      | eval' (Assert (assert, param_exprs)) term =
          let
            (* Note that param_exprs are always Literal at this point
             * because the evaluation function in From_Bound_To_Quantifier evaluated
             * param_exprs eagerly.*)
            val lazy_param_exprs = Seq.of_list param_exprs                                                             : expr Seq.seq
            val lazy_params      = Seq.map (param_with_bool_to_bound o (fn param => eval' param term)) lazy_param_exprs: Eval_Parameter.literal Seq.seq;
          in
            EPWB.eval term pst induct_args assert lazy_params |> Literal
          end
      | eval' (Dive_In   (triple as (Literal (EP.Outer_Path _), Lambda _, _))) term = dive triple term outer_literal_to_definitions
      | eval' (Deep_Dive (triple as (Literal (EP.Inner_Path _), Lambda _, _))) term = dive triple term inner_literal_to_definitions
      | eval' (All  (qtyp, subexpr)) term  = eval' (subexpr_n_qtyp_to_apps subexpr qtyp SU.Ands term) term
      | eval' (Some (qtyp, subexpr)) term  = eval' (subexpr_n_qtyp_to_apps subexpr qtyp SU.Ors  term) term
      | eval' expr _ = expr
    and dive (Literal path, Lambda lambda, args) trm (literal_to_definitions:Proof.state -> term -> EP.literal -> terms) =
        let
          val _             = if check_all_args_are_non_path_lits args then () else error "Some arguments in Dive_In are not Literal Non_Path";
          val simp_rules    = literal_to_definitions pst trm path: terms;
          val curried_expr  = mk_inner_expr (Lambda lambda) args : expr;
          val inner_results = map (eval' curried_expr) simp_rules: expr list;
          val ands          = Assert (SU.Ands, inner_results)    : expr;
          val result        = eval' ands trm                     : expr;
        in
          result
        end
      | dive _ _ _ = error "dive failed."
  in
    eval' expr thm_term
  end;

end;