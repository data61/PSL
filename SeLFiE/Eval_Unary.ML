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

type cached_val  = expr;
type inner_key   = (expr * expr * expr list);
type inner_alist = (inner_key * cached_val) list;
type outer_key   = term;
type outer_alist = (outer_key * inner_alist) list;
val cache_term_to_alist: outer_alist Unsynchronized.ref;
val cache_for_dive_in: ((term * (expr * expr * expr list)) * expr) list Unsynchronized.ref;

val eval: Proof.state -> Outer_Path_To_Unode.path_to_unode_table -> SeLFiE_Util.induct_arguments -> expr -> expr;

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

type exprs = expr list;

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

fun mk_inner_expr (lamb as Lambda _) (arguments:exprs) =
    mk_nested_app (mk_nested_lamb lamb (length arguments - 1)) arguments
  | mk_inner_expr _ _ = error "mk_inner_expr failed!"

(*TODO? Maybe we do not have to call OPTU or IPTU here.*)
structure OPTU = Outer_Path_To_Unode;
structure IPTU = Inner_Path_To_Unode;
structure OPTP = Print_To_Outer_Paths;
structure IPTP = Print_To_Inner_Paths;
structure GP   = Gen_Path;
structure QD   = Quantifier_Domain;

type literals = Eval_Parameter.literals;

type cached_val  = expr;
type inner_key   = (expr * expr * expr list);
type inner_alist = (inner_key * cached_val) list;
type outer_key   = term;
type outer_alist = (outer_key * inner_alist) list;
val cache_term_to_alist = Unsynchronized.ref []: outer_alist Unsynchronized.ref;

type triple = (expr * expr * expr list);
val cache_for_dive_in = Unsynchronized.ref ([]:((term * triple) * expr) list);

fun eval (pst:Proof.state) (outer_path_table:OPTU.path_to_unode_table) (induct_args:SU.induct_arguments) (expr:expr) =
  let
    fun subexpr_n_qtyp_n_domains_to_apps (subexpr:expr) (qtyp:SU.qtyp) (ands_or_ors:SU.assert) (domains:QD.domains) =
      let
        val params = QD.domains_n_qtyp_to_domain domains qtyp                      : EP.literals;
        val apps   = map (fn param => Apply (Lambda subexpr, Literal param)) params: exprs;
      in
        Assert (ands_or_ors, apps): expr
      end;
    val thm              = Isabelle_Utils.proof_state_to_thm pst                                                     : thm;
    val thm_term         = Thm.prop_of thm                                                                           : term;
    val gen_path_table   = SOME (GP.Outer_Path_To_Unode outer_path_table)                                            : GP.gen_path_to_unode_table option;
    val outer_domains    = QD.inout_pst_n_trm_n_induct_args_to_domains QD.Out gen_path_table pst thm_term induct_args: QD.domains;
    fun eval' (Apply (func, arg)) table (domains:QD.domains) =
         (case eval' func table domains of
          Lambda  u   => eval' (subst 0 (eval' arg table domains) u) table domains
        | Literal l   => Literal l
        | Bound   i   => Bound i
        | Dive_In t   => Dive_In t
        | Deep_Dive t => Deep_Dive t
        | u1          => Apply (u1, eval' arg table domains))
      | eval' (Assert (assert, param_exprs)) table domains =
          let
            (* Note that param_exprs are always Literal at this point because of the strict evaluation of Standard ML.*)
            val lazy_param_exprs = Seq.of_list param_exprs                                                                          : expr Seq.seq
            val lazy_params      = Seq.map (param_with_bool_to_bound o (fn param => eval' param table domains)) lazy_param_exprs: Eval_Parameter.literal Seq.seq;
          in
            EPWB.eval pst table induct_args assert lazy_params |> Literal
          end
      | eval' (Dive_In   (triple as (Literal (EP.Non_Path (EP.Print _)), Lambda _, _))) table domains = check_cache_then_dive_in triple table domains
      | eval' (Dive_In _) _ _                                                                         = error "Dive_In failed in Eval_Unary.ML"
      | eval' (Deep_Dive (triple as (Literal (EP.Non_Path (EP.Print _)), Lambda _, _))) table domains = check_cache_then_dive_in triple table domains
      | eval' (Deep_Dive _) _ _                                                                       = error "Deep_Dive failed in Eval_Unary.ML"
      | eval' (All  (qtyp, subexpr)) table domains = eval' (subexpr_n_qtyp_n_domains_to_apps subexpr qtyp SU.Ands domains) table domains
      | eval' (Some (qtyp, subexpr)) table domains = eval' (subexpr_n_qtyp_n_domains_to_apps subexpr qtyp SU.Ors  domains) table domains
      | eval' expr _ _ = expr
    and check_cache_then_dive_in triple table domains =(*TODO: Can this be a little better?*)
      let
        val old_cache              = !cache_term_to_alist                                                     : outer_alist;
        val cached_inner_alist_opt = AList.lookup (op =) old_cache thm_term                                   : inner_alist option;
        val cached_result_opt      = cached_inner_alist_opt >>= (fn alist => AList.lookup (op =) alist triple): cached_val option;
      in
        if   is_some cached_inner_alist_opt
        then (*some inner associative list*)
          let
            val cached_inner_alist = the cached_inner_alist_opt: inner_alist;
          in
            if  is_some cached_result_opt
            then (*some result in cache*)
              the cached_result_opt
            else (*no result in cache*)
              let
                val new_result      = dive triple table domains                                                                         : cached_val;
                val new_inner_alist = AList.update (op =) (triple, new_result) cached_inner_alist                                       : inner_alist;
                val _               = Unsynchronized.:= (cache_term_to_alist, AList.update (op =) (thm_term, new_inner_alist) old_cache): unit;
              in
                new_result
              end
          end
        else(*no inner associative list*)
          let
            val new_result = dive triple table domains;
            val _          = Unsynchronized.:= (cache_term_to_alist, AList.update (op =) (thm_term, [(triple, new_result)]) old_cache): unit;
          in
            new_result
          end
      end
    and dive (Literal (EP.Non_Path (EP.Print cname)), Lambda lambda, args) table domains =
        let
          val _             = if check_all_args_are_non_path_lits args then () else error "Some arguments in Dive_In are not Literal Non_Path";
          val simp_rules    = SU.pst_n_cname_to_definitions pst cname: terms;
          val curried_expr  = mk_inner_expr (Lambda lambda) args  : expr;
          (*TODO: use simp_rule_tables instead of simp_rules.*)
          val inner_results = map (fn trm =>
                              let
                                (*TODO: We should avoid constructing tables too many times here. Use a reference to an association list of (term * (table * domain) list.*)
                                val table   = (GP.Inner_Path_To_Unode o Inner_Path_To_Unode.pst_n_trm_to_path_to_unode_table pst) trm: GP.gen_path_to_unode_table;
                                val domains = QD.inout_pst_n_trm_n_induct_args_to_domains QD.In NONE pst trm induct_args             : QD.domains;
                              in
                                eval' curried_expr table domains
                              end) simp_rules                : exprs;
          val ands          = Assert (SU.Ands, inner_results): expr;
          val result        = eval' ands table domains       : expr;
        in
          result
        end
      | dive _ _ _ = error "dive failed."
  in
    eval' expr (GP.Outer_Path_To_Unode outer_path_table) (outer_domains:QD.domains)
  end;

end;