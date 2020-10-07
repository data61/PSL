(* Author: Joshua Schneider, ETH Zurich *)

signature APPLICATIVE =
sig
  type afun
  val intern: Context.generic -> xstring -> string
  val extern: Context.generic -> string -> xstring
  val afun_of_generic: Context.generic -> string -> afun
  val afun_of: Proof.context -> string -> afun
  val afuns_of_term_generic: Context.generic -> term -> afun list
  val afuns_of_term: Proof.context -> term -> afun list
  val afuns_of_typ_generic: Context.generic -> typ -> afun list
  val afuns_of_typ: Proof.context -> typ -> afun list
  val name_of_afun: afun -> binding
  val unfolds_of_afun: afun -> thm list

  type afun_inst
  val match_afun_inst: Proof.context -> afun -> term * int -> afun_inst
  val import_afun_inst: afun -> Proof.context -> afun_inst * Proof.context
  val inner_sort_of: afun_inst -> sort
  val mk_type: afun_inst -> typ -> typ
  val mk_pure: afun_inst -> typ -> term
  val lift_term: afun_inst -> term -> term
  val mk_ap: afun_inst -> typ * typ -> term
  val mk_comb: afun_inst -> typ -> term * term -> term
  val mk_set: afun_inst -> typ -> term
  val dest_type: Proof.context -> afun_inst -> typ -> typ option
  val dest_type': Proof.context -> afun_inst -> typ -> typ
  val dest_pure: Proof.context -> afun_inst -> term -> term
  val dest_comb: Proof.context -> afun_inst -> term -> term * term
  val infer_comb: Proof.context -> afun_inst -> term * term -> term
  val subst_lift_term: afun_inst -> (term * term) list -> term -> term
  val generalize_lift_terms: afun_inst -> term list -> Proof.context -> term list * Proof.context

  val afun_unfold_tac: Proof.context -> afun -> int -> tactic
  val afun_fold_tac: Proof.context -> afun -> int -> tactic
  val unfold_all_tac: Proof.context -> int -> tactic
  val normalform_conv: Proof.context -> afun -> conv
  val normalize_rel_tac: Proof.context -> afun -> int -> tactic
  val general_normalform_conv: Proof.context -> afun -> cterm * cterm -> thm * thm
  val general_normalize_rel_tac: Proof.context -> afun -> int -> tactic
  val forward_lift_rule: Proof.context -> afun -> thm -> thm
  val unfold_wrapper_tac: Proof.context -> afun option -> int -> tactic
  val fold_wrapper_tac: Proof.context -> afun option -> int -> tactic
  val normalize_wrapper_tac: Proof.context -> afun option -> int -> tactic
  val lifting_wrapper_tac: Proof.context -> afun option -> int -> tactic

  val setup_combinators: (string * thm) list -> local_theory -> local_theory
  val combinator_rule_attrib: string list option -> attribute
  val parse_opt_afun: afun option context_parser
  val applicative_cmd: (((((binding * string list) * string) * string) * string option) * string option) ->
    local_theory -> Proof.state
  val print_afuns: Proof.context -> unit
  val add_unfold_attrib: xstring option -> attribute
  val forward_lift_attrib: xstring -> attribute
end;

structure Applicative : APPLICATIVE =
struct

open Ctr_Sugar_Util

(** General utilities **)

fun fold_options xs = fold (fn x =>
  (case x of
    SOME x' => cons x'
  | NONE => I)) xs [];

fun the_pair [x, y] = (x, y)
  | the_pair _ = raise General.Size;

fun strip_comb2 (f $ x $ y) = (f, (x, y))
  | strip_comb2 t = raise TERM ("strip_comb2", [t]);

fun mk_comb_pattern (t, n) =
  let
    val Ts = take n (binder_types (fastype_of t));
    val maxidx = maxidx_of_term t;
    val vars = map (fn (T, i) => ((Name.uu, maxidx + i), T)) (Ts ~~ (1 upto n));
  in (vars, Term.betapplys (t, map Var vars)) end;

fun match_comb_pattern ctxt tn u =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (vars, pat) = mk_comb_pattern tn;
    val envs = Pattern.match thy (pat, u) (Vartab.empty, Vartab.empty)
      handle Pattern.MATCH => raise TERM ("match_comb_pattern", [u, pat]);
  in (vars, envs) end;

fun dest_comb_pattern ctxt tn u =
  let val (vars, (_, env)) = match_comb_pattern ctxt tn u;
  in map (the o Envir.lookup1 env) vars end;

fun norm_term_types tyenv t = Term_Subst.map_types_same (Envir.norm_type_same tyenv) t
  handle Same.SAME => t;

val mk_TFrees_of = mk_TFrees' oo replicate;

fun mk_Free name typ ctxt = yield_singleton Variable.variant_fixes name ctxt
  |>> (fn name' => Free (name', typ));

(*tuples with explicit sentinel*)
fun mk_tuple' ts = fold_rev (curry HOLogic.mk_prod) ts HOLogic.unit;
fun strip_tuple' (Const (@{const_name Unity}, _)) = []
  | strip_tuple' (Const (@{const_name Pair}, _) $ t1 $ t2) = t1 :: strip_tuple' t2
  | strip_tuple' t = raise TERM ("strip_tuple'", [t]);

fun mk_eq_on S =
  let val (SA, ST) = `HOLogic.dest_setT (fastype_of S);
  in Const (@{const_name eq_on}, ST --> BNF_Util.mk_pred2T SA SA) $ S end;


(* Polymorphic terms and term groups *)

type poly_type = typ list * typ;
type poly_term = typ list * term;

fun instantiate_poly_type (tvars, T) insts = typ_subst_atomic (tvars ~~ insts) T;
fun instantiate_poly_term (tvars, t) insts = subst_atomic_types (tvars ~~ insts) t;

fun dest_poly_type ctxt (tvars, T) U =
  let
    val thy = Proof_Context.theory_of ctxt;
    val tyenv = Sign.typ_match thy (T, U) Vartab.empty
      handle Type.TYPE_MATCH => raise TYPE ("dest_poly_type", [U, T], []);
  in map (Type.lookup tyenv o dest_TVar) tvars end;

fun poly_type_to_term (tvars, T) = (tvars, Logic.mk_type T);
fun poly_type_of_term (tvars, t) = (tvars, Logic.dest_type t);

(*
  Schematic variables are treated uniformly in packed terms, thus forming an ad hoc context
  of type variables. Otherwise, morphisms are allowed to rename schematic variables
  non-consistently in separate terms, and occasionally will do so.
*)
fun pack_poly_term (tvars, t) = HOLogic.mk_prod (mk_tuple' (map Logic.mk_type tvars), t);
fun unpack_poly_term t =
  let val (tvars, t') = HOLogic.dest_prod t;
  in (map Logic.dest_type (strip_tuple' tvars), t') end;

val pack_poly_terms = mk_tuple' o map pack_poly_term;
val unpack_poly_terms = map unpack_poly_term o strip_tuple';

(*match and instantiate schematic type variables which are not "quantified" in the packed term*)
fun match_poly_terms_type ctxt (pt, i) (U, maxidx) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val pt' = Logic.incr_indexes ([], [], maxidx + 1) pt;
    val (tvars, T) = poly_type_of_term (nth (unpack_poly_terms pt') i);
    val tyenv = Sign.typ_match thy (T, U) Vartab.empty
      handle Type.TYPE_MATCH => raise TYPE ("match_poly_terms", [U, T], []);
    val tyenv' = fold Vartab.delete_safe (map (#1 o dest_TVar) tvars) tyenv;
    val pt'' = Envir.subst_term_types tyenv' pt';
  in unpack_poly_terms pt'' end;

fun match_poly_terms ctxt (pt, i) (t, maxidx) =
  match_poly_terms_type ctxt (pt, i) (fastype_of t, maxidx);

(*fix schematic type variables which are not "quantified", as well as schematic term variables*)
fun import_poly_terms pt ctxt =
  let
    fun insert_paramTs (tvars, t) = fold_types (fold_atyps
      (fn TVar v => if member (op =) tvars (TVar v) then I else insert (op =) v
        | _ => I)) t;
    val paramTs = rev (fold insert_paramTs (unpack_poly_terms pt) []);
    val (tfrees, ctxt') = Variable.invent_types (map #2 paramTs) ctxt;
    val instT = paramTs ~~ map TFree tfrees;
    val params = map (apsnd (Term_Subst.instantiateT instT)) (rev (Term.add_vars pt []));
    val (frees, ctxt'') = Variable.variant_fixes (map (Name.clean o #1 o #1) params) ctxt';
    val inst = params ~~ map Free (frees ~~ map #2 params);
    val pt' = Term_Subst.instantiate (instT, inst) pt;
  in (unpack_poly_terms pt', ctxt'') end;


(** Internal representation **)

(* Applicative functors *)

type rel_thms = {
  pure_transfer: thm,
  ap_rel_fun: thm
};

fun map_rel_thms f {pure_transfer, ap_rel_fun} =
  {pure_transfer = f pure_transfer, ap_rel_fun = f ap_rel_fun};

type afun_thms = {
  hom: thm,
  ichng: thm,
  reds: thm Symtab.table,
  rel_thms: rel_thms option,
  rel_intros: thm list,
  pure_comp_conv: thm
};

fun map_afun_thms f {hom, ichng, reds, rel_thms, rel_intros, pure_comp_conv} =
  {hom = f hom, ichng = f ichng, reds = Symtab.map (K f) reds,
    rel_thms = Option.map (map_rel_thms f) rel_thms, rel_intros = map f rel_intros,
    pure_comp_conv = f pure_comp_conv};

datatype afun = AFun of {
  name: binding,
  terms: term,
  rel: term option,
  thms: afun_thms,
  unfolds: thm Item_Net.T
};

fun rep_afun (AFun af) = af;
val name_of_afun = #name o rep_afun;
val terms_of_afun = #terms o rep_afun;
val rel_of_afun = #rel o rep_afun;
val thms_of_afun = #thms o rep_afun;
val unfolds_of_afun = Item_Net.content o #unfolds o rep_afun;

val red_of_afun = Symtab.lookup o #reds o thms_of_afun;
val has_red_afun = is_some oo red_of_afun;

fun mk_afun name terms rel thms =
  AFun {name = name, terms = terms, rel = rel, thms = thms, unfolds = Thm.full_rules};

fun map_afun f1 f2 f3 f4 f5 (AFun {name, terms, rel, thms, unfolds}) =
  AFun {name = f1 name, terms = f2 terms, rel = f3 rel, thms = f4 thms, unfolds = f5 unfolds};

fun map_unfolds f thms = fold Item_Net.update (map f (Item_Net.content thms)) Thm.full_rules;

fun morph_afun phi =
  let
    val binding = Morphism.binding phi;
    val term = Morphism.term phi;
    val thm = Morphism.thm phi;
  in map_afun binding term (Option.map term) (map_afun_thms thm) (map_unfolds thm) end;

val transfer_afun = morph_afun o Morphism.transfer_morphism;

fun add_unfolds_afun thms = map_afun I I I I (fold Item_Net.update thms);

fun patterns_of_afun af =
  let
    val [Tt, (_, pure), (_, ap), _] = unpack_poly_terms (terms_of_afun af);
    val (_, T) = poly_type_of_term Tt;
  in [#2 (mk_comb_pattern (pure, 1)), #2 (mk_comb_pattern (ap, 2)), Net.encode_type T] end;


(* Combinator rules *)

datatype combinator_rule = Combinator_Rule of {
  strong_premises: string Ord_List.T,
  weak_premises: bool,
  conclusion: string,
  eq_thm: thm
};

fun rep_combinator_rule (Combinator_Rule rule) = rule;
val conclusion_of_rule = #conclusion o rep_combinator_rule;
val thm_of_rule = #eq_thm o rep_combinator_rule;

fun eq_combinator_rule (rule1, rule2) =
  pointer_eq (rule1, rule2) orelse Thm.eq_thm (thm_of_rule rule1, thm_of_rule rule2);

fun is_applicable_rule rule have_weak have_premises =
  let val {strong_premises, weak_premises, ...} = rep_combinator_rule rule;
  in (have_weak orelse not weak_premises) andalso have_premises strong_premises end;

fun map_combinator_rule f1 f2 f3 f4
  (Combinator_Rule {strong_premises, weak_premises, conclusion, eq_thm}) =
    Combinator_Rule {strong_premises = f1 strong_premises, weak_premises = f2 weak_premises,
      conclusion = f3 conclusion, eq_thm = f4 eq_thm};

fun transfer_combinator_rule thy = map_combinator_rule I I I (Thm.transfer thy);

fun mk_combinator_rule comb_names weak_premises thm =
  let
    val (lhs, rhs) = Logic.dest_equals (Thm.prop_of thm);
    val conclusion = the (Symtab.lookup comb_names (#1 (dest_Const lhs)));
    val premises = Ord_List.make fast_string_ord
      (fold_options (map (Symtab.lookup comb_names o #1) (Term.add_consts rhs [])));
    val weak_premises' = Ord_List.make fast_string_ord (these weak_premises);
    val strong_premises = Ord_List.subtract fast_string_ord weak_premises' premises;
  in Combinator_Rule {strong_premises = strong_premises, weak_premises = is_some weak_premises,
    conclusion = conclusion, eq_thm = thm} end;


(* Generic data *)

(*FIXME: needs tests, especially around theory merging*)

fun merge_afuns _ (af1, af2) = if pointer_eq (af1, af2)
  then raise Change_Table.SAME
  else map_afun I I I I (fn thms1 => Item_Net.merge (thms1, #unfolds (rep_afun af2))) af1;

structure Data = Generic_Data
(
  type T = {
    combinators: thm Symtab.table * combinator_rule list,
    afuns: afun Name_Space.table,
    patterns: (string * term list) Item_Net.T
  };
  val empty = {
    combinators = (Symtab.empty, []),
    afuns = Name_Space.empty_table "applicative functor",
    patterns = Item_Net.init (op = o apply2 #1) #2
  };
  val extend = I;
  fun merge ({combinators = (cd1, cr1), afuns = a1, patterns = p1},
             {combinators = (cd2, cr2), afuns = a2, patterns = p2}) =
    {combinators = (Symtab.merge (K true) (cd1, cd2), Library.merge eq_combinator_rule (cr1, cr2)),
      afuns = Name_Space.join_tables merge_afuns (a1, a2),
      patterns = Item_Net.merge (p1, p2)};
);

fun get_combinators context =
  let
    val thy = Context.theory_of context;
    val {combinators = (defs, rules), ...} = Data.get context;
  in (Symtab.map (K (Thm.transfer thy)) defs, map (transfer_combinator_rule thy) rules) end;

val get_afun_table = #afuns o Data.get;
val get_afun_space = Name_Space.space_of_table o get_afun_table;
val get_patterns = #patterns o Data.get;

fun map_data f1 f2 f3 {combinators, afuns, patterns} =
  {combinators = f1 combinators, afuns = f2 afuns, patterns = f3 patterns};

val intern = Name_Space.intern o get_afun_space;
fun extern context = Name_Space.extern (Context.proof_of context) (get_afun_space context);

local fun undeclared name = error ("Undeclared applicative functor " ^ quote name);
in

fun afun_of_generic context name = case Name_Space.lookup (get_afun_table context) name of
    SOME af => transfer_afun (Context.theory_of context) af
  | NONE => undeclared name;

val afun_of = afun_of_generic o Context.Proof;

fun update_afun name f context = if Name_Space.defined (get_afun_table context) name
  then Data.map (map_data I (Name_Space.map_table_entry name f) I) context
  else undeclared name;

end;

fun match_term context = map #1 o Item_Net.retrieve_matching (get_patterns context);
fun match_typ context = match_term context o Net.encode_type;

(*works only with terms which are combinations of pure and ap*)
fun afuns_of_term_generic context = map (afun_of_generic context) o match_term context;
val afuns_of_term = afuns_of_term_generic o Context.Proof;

fun afuns_of_typ_generic context = map (afun_of_generic context) o match_typ context;
val afuns_of_typ = afuns_of_typ_generic o Context.Proof;

fun all_unfolds_of_generic context =
  let val unfolds_of = map (Thm.transfer'' context) o unfolds_of_afun;
  in Name_Space.fold_table (fn (_, af) => append (unfolds_of af)) (get_afun_table context) [] end;

val all_unfolds_of = all_unfolds_of_generic o Context.Proof;


(** Term construction and destruction **)

type afun_inst = {
  T: poly_type,
  pure: poly_term,
  ap: poly_term,
  set: poly_term
};

fun mk_afun_inst [T, pure, ap, set] = {T = poly_type_of_term T, pure = pure, ap = ap, set = set};
fun pack_afun_inst {T, pure, ap, set} = pack_poly_terms [poly_type_to_term T, pure, ap, set];

fun match_afun_inst ctxt af = match_poly_terms ctxt (terms_of_afun af, 0) #> mk_afun_inst;
fun import_afun_inst_raw terms = import_poly_terms terms #>> mk_afun_inst;
val import_afun_inst = import_afun_inst_raw o terms_of_afun;

fun inner_sort_of {T = (tvars, _), ...} = Type.sort_of_atyp (the_single tvars);

fun mk_type {T, ...} = instantiate_poly_type T o single;
fun mk_pure {pure, ...} = instantiate_poly_term pure o single;
fun mk_ap {ap, ...} (T1, T2) = instantiate_poly_term ap [T1, T2];
fun mk_set {set, ...} = instantiate_poly_term set o single;

fun lift_term af_inst t = Term.betapply (mk_pure af_inst (Term.fastype_of t), t);
fun mk_comb af_inst funT (t1, t2) = Term.betapplys (mk_ap af_inst (dest_funT funT), [t1, t2]);

fun dest_type ctxt {T, ...} = the_single o dest_poly_type ctxt T;
val dest_type' = the_default HOLogic.unitT ooo dest_type;

fun dest_pure ctxt {pure = (_, pure), ...} = the_single o dest_comb_pattern ctxt (pure, 1);
fun dest_comb ctxt {ap = (_, ap), ...} = the_pair o dest_comb_pattern ctxt (ap, 2);

fun infer_comb ctxt af_inst (t1, t2) =
  let val funT = the_default (dummyT --> dummyT) (dest_type ctxt af_inst (fastype_of t1));
  in mk_comb af_inst funT (t1, t2) end;

(*lift a term, except for non-combination subterms mapped by subst*)
fun subst_lift_term af_inst subst tm =
  let
    fun subst_lift (s $ t) =
        (case (subst_lift s, subst_lift t) of
          (NONE, NONE) => NONE
        | (SOME s', NONE) => SOME (mk_comb af_inst (fastype_of s) (s', lift_term af_inst t))
        | (NONE, SOME t') => SOME (mk_comb af_inst (fastype_of s) (lift_term af_inst s, t'))
        | (SOME s', SOME t') => SOME (mk_comb af_inst (fastype_of s) (s', t')))
      | subst_lift t = AList.lookup (op aconv) subst t;
  in
    (case subst_lift tm of
      NONE => lift_term af_inst tm
    | SOME tm' => tm')
  end;

fun add_lifted_vars (s $ t) = add_lifted_vars s #> add_lifted_vars t
  | add_lifted_vars (Abs (_, _, t)) = Term.add_vars t
  | add_lifted_vars _ = I;

(*lift terms, where schematic variables are generalized to the functor and then fixed*)
fun generalize_lift_terms af_inst ts ctxt =
  let
    val vars = subtract (op =) (fold add_lifted_vars ts []) (fold Term.add_vars ts []);
    val (var_names, Ts) = split_list vars;
    val (free_names, ctxt') = Variable.variant_fixes (map #1 var_names) ctxt;
    val Ts' = map (mk_type af_inst) Ts;
    val subst = map Var vars ~~ map Free (free_names ~~ Ts');
  in (map (subst_lift_term af_inst subst) ts, ctxt') end;


(** Reasoning with applicative functors **)

(* Utilities *)

val clean_name = perhaps (perhaps_apply [try Name.dest_skolem, try Name.dest_internal]);

(*based on term_name from Pure/term.ML*)
fun term_to_vname (Const (x, _)) = Long_Name.base_name x
  | term_to_vname (Free (x, _)) = clean_name x
  | term_to_vname (Var ((x, _), _)) = clean_name x
  | term_to_vname _ = "x";

fun afuns_of_rel precise ctxt t =
  let val (_, (lhs, rhs)) = Variable.focus NONE t ctxt
    |> #1 |> #2
    |> Logic.strip_imp_concl
    |> Envir.beta_eta_contract
    |> HOLogic.dest_Trueprop
    |> strip_comb2;
  in if precise
    then (case afuns_of_term ctxt lhs of
        [] => afuns_of_term ctxt rhs
      | afs => afs)
    else afuns_of_typ ctxt (fastype_of lhs) end;

fun AUTO_AFUNS precise tac ctxt opt_af = case opt_af of
    SOME af => tac [af]
  | NONE => SUBGOAL (fn (goal, i) => (case afuns_of_rel precise ctxt goal of
      [] => no_tac
    | afs => tac afs i) handle TERM _ => no_tac);

fun AUTO_AFUN precise tac = AUTO_AFUNS precise (tac o hd);

fun binop_par_conv cv ct =
  let
    val ((binop, arg1), arg2) = Thm.dest_comb ct |>> Thm.dest_comb;
    val (th1, th2) = cv (arg1, arg2);
  in Drule.binop_cong_rule binop th1 th2 end;

fun binop_par_conv_tac cv = CONVERSION (HOLogic.Trueprop_conv (binop_par_conv cv));

val fold_goal_tac = SELECT_GOAL oo Raw_Simplifier.fold_goals_tac;


(* Unfolding of lifted constants *)

fun afun_unfold_tac ctxt af = Raw_Simplifier.rewrite_goal_tac ctxt (unfolds_of_afun af);
fun afun_fold_tac ctxt af = fold_goal_tac ctxt (unfolds_of_afun af);

fun unfold_all_tac ctxt = Raw_Simplifier.rewrite_goal_tac ctxt (all_unfolds_of ctxt);


(* Basic conversions *)

fun pure_conv ctxt {pure = (_, pure), ...} cv ct =
  let
    val ([var], (tyenv, env)) = match_comb_pattern ctxt (pure, 1) (Thm.term_of ct);
    val arg = the (Envir.lookup1 env var);
    val thm = cv (Thm.cterm_of ctxt arg);
  in
    if Thm.is_reflexive thm then Conv.all_conv ct
    else
      let val pure_inst = Envir.subst_term_types tyenv pure;
      in Drule.arg_cong_rule (Thm.cterm_of ctxt pure_inst) thm end
  end;

fun ap_conv ctxt {ap = (_, ap), ...} cv1 cv2 ct =
  let
    val ([var1, var2], (tyenv, env)) = match_comb_pattern ctxt (ap, 2) (Thm.term_of ct);
    val (arg1, arg2) = apply2 (the o Envir.lookup1 env) (var1, var2);
    val thm1 = cv1 (Thm.cterm_of ctxt arg1);
    val thm2 = cv2 (Thm.cterm_of ctxt arg2);
  in
    if Thm.is_reflexive thm1 andalso Thm.is_reflexive thm2 then Conv.all_conv ct
    else
      let val ap_inst = Envir.subst_term_types tyenv ap;
      in Drule.binop_cong_rule (Thm.cterm_of ctxt ap_inst) thm1 thm2 end
  end;


(* Normal form conversion *)

(*convert a term into applicative normal form*)
fun normalform_conv ctxt af ct =
  let
    val {hom, ichng, pure_comp_conv, ...} = thms_of_afun af;
    val the_red = the o red_of_afun af;
    val leaf_conv = Conv.rewr_conv (mk_meta_eq (the_red "I") |> Thm.symmetric);
    val merge_conv = Conv.rewr_conv (mk_meta_eq hom);
    val swap_conv = Conv.rewr_conv (mk_meta_eq ichng);
    val rotate_conv = Conv.rewr_conv (mk_meta_eq (the_red "B") |> Thm.symmetric);
    val pure_rotate_conv = Conv.rewr_conv (mk_meta_eq pure_comp_conv);

    val af_inst = match_afun_inst ctxt af (Thm.term_of ct, Thm.maxidx_of_cterm ct);
    fun left_conv cv = ap_conv ctxt af_inst cv Conv.all_conv;

    fun norm_pure_nf ct =
      ((pure_rotate_conv then_conv left_conv norm_pure_nf) else_conv merge_conv) ct;
    val norm_nf_pure = swap_conv then_conv norm_pure_nf;
    fun norm_nf_nf ct = ((rotate_conv then_conv
        left_conv (left_conv norm_pure_nf then_conv norm_nf_nf)) else_conv
      norm_nf_pure) ct;
    fun normalize ct = ((ap_conv ctxt af_inst normalize normalize then_conv norm_nf_nf) else_conv
      pure_conv ctxt af_inst Conv.all_conv else_conv
      leaf_conv) ct;
  in normalize ct end;

val normalize_rel_tac = binop_par_conv_tac o apply2 oo normalform_conv;


(* Bracket abstraction and generalized unlifting *)

(*TODO: use proper conversions*)

datatype apterm =
    Pure of term  (*includes pure application*)
  | ApVar of int * term  (*unique index, instantiated term*)
  | Ap of apterm * apterm;

fun apterm_vars (Pure _) = I
  | apterm_vars (ApVar v) = cons v
  | apterm_vars (Ap (t1, t2)) = apterm_vars t1 #> apterm_vars t2;

fun occurs_any _ (Pure _) = false
  | occurs_any vs (ApVar (i, _)) = exists (fn j => i = j) vs
  | occurs_any vs (Ap (t1, t2)) = occurs_any vs t1 orelse occurs_any vs t2;

fun term_of_apterm ctxt af_inst t =
  let
    fun tm_of (Pure t) = t
      | tm_of (ApVar (_, t)) = t
      | tm_of (Ap (t1, t2)) = infer_comb ctxt af_inst (tm_of t1, tm_of t2);
  in tm_of t end;

fun apterm_of_term ctxt af_inst t =
  let
    fun aptm_of t i = case try (dest_comb ctxt af_inst) t of
        SOME (t1, t2) => i |> aptm_of t1 ||>> aptm_of t2 |>> Ap
      | NONE => if can (dest_pure ctxt af_inst) t
          then (Pure t, i)
          else (ApVar (i, t), i + 1);
  in aptm_of t end;

(*find a common variable sequence for two applicative terms, depending on available combinators*)
fun consolidate ctxt af (t1, t2) =
  let
    fun common_inst (i, t) (j, insts) = case Termtab.lookup insts t of
        SOME k => (((i, t), k), (j, insts))
      | NONE => (((i, t), j), (j + 1, Termtab.update (t, j) insts));

    val (vars, _) = (0, Termtab.empty)
      |> fold_map common_inst (apterm_vars t1 [])
      ||>> fold_map common_inst (apterm_vars t2 []);

    fun merge_adjacent (([], _), _) [] = []
      | merge_adjacent ((is, t), d) [] = [((is, t), d)]
      | merge_adjacent (([], _), _) (((i, t), d)::xs) = merge_adjacent (([i], t), d) xs
      | merge_adjacent ((is, t), d) (((i', t'), d')::xs) = if d = d'
          then merge_adjacent ((i'::is, t), d) xs
          else ((is, t), d) :: merge_adjacent (([i'], t'), d') xs;

    fun align _ [] = NONE
      | align ((i, t), d) (((i', t'), d')::xs) = if d = d'
          then SOME ([((i @ i', t), d)], xs)
          else Option.map (apfst (cons ((i', t'), d'))) (align ((i, t), d) xs);
    fun merge ([], ys) = ys
      | merge (xs, []) = xs
      | merge ((xs as ((is1, t1), d1)::xs'), ys as (((is2, t2), d2)::ys')) = if d1 = d2
          then ((is1 @ is2, t1), d1) :: merge (xs', ys')
          else case (align ((is2, t2), d2) xs, align ((is1, t1), d1) ys) of
              (SOME (zs, xs''), NONE) => zs @ merge (xs'', ys')
            | (NONE, SOME (zs, ys'')) => zs @ merge (xs', ys'')
            | _ => ((is1, t1), d1) :: ((is2, t2), d2) :: merge (xs', ys');

    fun unbalanced vs = error ("Unbalanced opaque terms " ^
      commas_quote (map (Syntax.string_of_term ctxt o #2 o #1) vs));
    fun mismatch (t1, t2) = error ("Mismatched opaque terms " ^
      quote (Syntax.string_of_term ctxt t1) ^ " and " ^ quote (Syntax.string_of_term ctxt t2));
    fun same ([], []) = []
      | same ([], ys) = unbalanced ys
      | same (xs, []) = unbalanced xs
      | same ((((i1, t1), d1)::xs), (((i2, t2), d2)::ys)) = if d1 = d2
          then ((i1 @ i2, t1), d1) :: same (xs, ys)
          else mismatch (t1, t2);
  in vars
    |> has_red_afun af "C" ? apply2 (sort (int_ord o apply2 #2))
    |> apply2 (if has_red_afun af "W"
        then merge_adjacent (([], Term.dummy), 0)
        else map (apfst (apfst single)))
    |> (if has_red_afun af "K" then merge else same)
    |> map #1
  end;

fun ap_cong ctxt af_inst thm1 thm2 =
  let
    val funT = the_default (dummyT --> dummyT)
      (dest_type ctxt af_inst (Thm.typ_of_cterm (Thm.lhs_of thm1)));
    val ap_inst = Thm.cterm_of ctxt (mk_ap af_inst (dest_funT funT));
  in Drule.binop_cong_rule ap_inst thm1 thm2 end;

fun rewr_subst_ap ctxt af_inst rewr thm1 thm2 =
  let
    val rule1 = ap_cong ctxt af_inst thm1 thm2;
    val rule2 = Conv.rewr_conv rewr (Thm.rhs_of rule1);
  in Thm.transitive rule1 rule2 end;

fun merge_pures ctxt af_inst merge_thm tt =
  let
    fun merge (Pure t) = SOME (Thm.reflexive (Thm.cterm_of ctxt t))
      | merge (ApVar _) = NONE
      | merge (Ap (tt1, tt2)) = case merge tt1 of
          NONE => NONE
        | SOME thm1 => case merge tt2 of
            NONE => NONE
          | SOME thm2 => SOME (rewr_subst_ap ctxt af_inst merge_thm thm1 thm2);
  in merge tt end;

exception ASSERT of string;

(*abstract over a variable (opaque subterm)*)
fun eliminate ctxt (af, af_inst) tt (v, v_tm) =
  let
    val {hom, ichng, ...} = thms_of_afun af;
    val the_red = the o red_of_afun af;
    val hom_conv = mk_meta_eq hom;
    val ichng_conv = mk_meta_eq ichng;
    val mk_combI = Thm.symmetric o mk_meta_eq;
    val id_conv = mk_combI (the_red "I");
    val comp_conv = mk_combI (the_red "B");
    val flip_conv = Option.map mk_combI (red_of_afun af "C");
    val const_conv = Option.map mk_combI (red_of_afun af "K");
    val dup_conv = Option.map mk_combI (red_of_afun af "W");

    val rewr_subst_ap = rewr_subst_ap ctxt af_inst;
    fun extract_comb n thm = Pure (thm |> Thm.rhs_of |> funpow n Thm.dest_arg1 |> Thm.term_of);
    fun refl_step tt = (tt, Thm.reflexive (Thm.cterm_of ctxt (term_of_apterm ctxt af_inst tt)));
    fun comb2_step def (tt1, thm1) (tt2, thm2) =
      let val thm = rewr_subst_ap def thm1 thm2;
      in (Ap (Ap (extract_comb 3 thm, tt1), tt2), thm) end;
    val B_step = comb2_step comp_conv;
    fun swap_B_step (tt1, thm1) thm2 =
      let
        val thm3 = rewr_subst_ap ichng_conv thm1 thm2;
        val thm4 = Thm.transitive thm3 (Conv.rewr_conv comp_conv (Thm.rhs_of thm3));
      in (Ap (Ap (extract_comb 3 thm4, extract_comb 1 thm3), tt1), thm4) end;
    fun I_step tm =
      let val thm = Conv.rewr_conv id_conv (Thm.cterm_of ctxt tm)
      in (extract_comb 1 thm, thm) end;
    fun W_step s1 s2 =
      let
        val (Ap (Ap (tt1, tt2), tt3), thm1) = B_step s1 s2;
        val thm2 = Conv.rewr_conv comp_conv (Thm.rhs_of thm1 |> funpow 2 Thm.dest_arg1);
        val thm3 = merge_pures ctxt af_inst hom_conv tt3 |> the;
        val (tt4, thm4) = swap_B_step (Ap (Ap (extract_comb 3 thm2, tt1), tt2), thm2) thm3;
        val var = Thm.rhs_of thm1 |> Thm.dest_arg;
        val thm5 = rewr_subst_ap (the dup_conv) thm4 (Thm.reflexive var);
        val thm6 = Thm.transitive thm1 thm5;
      in (Ap (extract_comb 2 thm6, tt4), thm6) end;
    fun S_step s1 s2 =
      let
        val (Ap (Ap (tt1, tt2), tt3), thm1) = comb2_step (the flip_conv) s1 s2;
        val thm2 = Conv.rewr_conv comp_conv (Thm.rhs_of thm1 |> Thm.dest_arg1);
        val var = Thm.rhs_of thm1 |> Thm.dest_arg;
        val thm3 = rewr_subst_ap (the dup_conv) thm2 (Thm.reflexive var);
        val thm4 = Thm.transitive thm1 thm3;
        val tt = Ap (extract_comb 2 thm4, Ap (Ap (extract_comb 3 thm2, Ap (tt1, tt2)), tt3));
      in (tt, thm4) end;
    fun K_step tt tm =
      let
        val ct = Thm.cterm_of ctxt tm;
        val T_opt = Term.fastype_of tm |> dest_type ctxt af_inst |> Option.map (Thm.ctyp_of ctxt);
        val thm = Thm.instantiate' [T_opt] [SOME ct]
          (Conv.rewr_conv (the const_conv) (term_of_apterm ctxt af_inst tt |> Thm.cterm_of ctxt))
      in (Ap (extract_comb 2 thm, tt), thm) end;
    fun unreachable _ = raise ASSERT "eliminate: assertion failed";
    fun elim (Pure _) = unreachable ()
      | elim (ApVar (i, t)) = if exists (fn x => x = i) v then I_step t else unreachable ()
      | elim (Ap (t1, t2)) = (case (occurs_any v t1, occurs_any v t2) of
            (false, false) => unreachable ()
          | (false, true) => B_step (refl_step t1) (elim t2)
          | (true, false) => (case merge_pures ctxt af_inst hom_conv t2 of
                SOME thm => swap_B_step (elim t1) thm
              | NONE => comb2_step (the flip_conv) (elim t1) (refl_step t2))
          | (true, true) => if is_some flip_conv
              then S_step (elim t1) (elim t2)
              else W_step (elim t1) (elim t2));
  in if occurs_any v tt
    then elim tt
    else K_step tt v_tm
  end;

(*convert a pair of terms into equal canonical forms, modulo pure terms*)
fun general_normalform_conv ctxt af cts =
  let
    val (t1, t2) = apply2 (Thm.term_of) cts;
    val maxidx = Int.max (apply2 Thm.maxidx_of_cterm cts);
    (* TODO: is there a better strategy for finding the instantiated functor? *)
    val af_inst = match_afun_inst ctxt af (t1, maxidx);
    val ((apt1, apt2), _) = 0 |> apterm_of_term ctxt af_inst t1 ||>> apterm_of_term ctxt af_inst t2;
    val vs = consolidate ctxt af (apt1, apt2);
    val merge_thm = mk_meta_eq (#hom (thms_of_afun af));
    fun elim_all tt [] = the (merge_pures ctxt af_inst merge_thm tt)
      | elim_all tt (v::vs) =
          let
            val (tt', rule1) = eliminate ctxt (af, af_inst) tt v;
            val rule2 = elim_all tt' vs;
            val (_, vartm) = dest_comb ctxt af_inst (Thm.term_of (Thm.rhs_of rule1));
            val rule3 = ap_cong ctxt af_inst rule2 (Thm.reflexive (Thm.cterm_of ctxt vartm));
          in Thm.transitive rule1 rule3 end;
  in (elim_all apt1 vs, elim_all apt2 vs) end;

val general_normalize_rel_tac = binop_par_conv_tac oo general_normalform_conv;


(* Reduce canonical forms to base relation *)

fun rename_params names i st =
  let
    val (_, Bs, Bi, C) = Thm.dest_state (st, i);
    val Bi' = Logic.list_rename_params names Bi;
  in Thm.renamed_prop (Logic.list_implies (Bs @ [Bi'], C)) st end;

(*
  R' (pure f <> x1 <> ... <> xn) (pure g <> x1 <> ... <> xn)
    ===> !!y1 ... yn. [| yi : setF xi ... |] ==> R (f y1 ... yn) (g y1 ... yn),
  where either both R and R' are equality, or R' = relF R for relator relF of the functor.
  The premises yi : setF xi are added only in the latter case and if the set operator is available.
  Succeeds if partial progress can be made. The names of the new parameters yi are derived
  from the arguments xi.
*)
fun head_cong_tac ctxt af renames =
  let
    val {rel_intros, ...} = thms_of_afun af;
    fun term_name tm = case AList.lookup (op aconv) renames tm of
        SOME n => n
      | NONE => term_to_vname tm;
    fun gather_vars' af_inst tm = case try (dest_comb ctxt af_inst) tm of
        SOME (t1, t2) => term_name t2 :: gather_vars' af_inst t1
      | NONE => [];
    fun gather_vars prop = case prop of
        Const (@{const_name Trueprop}, _) $ (_ $ rhs) =>
          rev (gather_vars' (match_afun_inst ctxt af (rhs, maxidx_of_term prop)) rhs)
      | _ => [];
  in SUBGOAL (fn (subgoal, i) =>
    (REPEAT_DETERM (resolve_tac ctxt rel_intros i) THEN
      REPEAT_DETERM (resolve_tac ctxt [ext, @{thm rel_fun_eq_onI}] i ORELSE
        eresolve_tac ctxt [@{thm UNIV_E}] i) THEN
      PRIMITIVE (rename_params (gather_vars subgoal) i)))
  end;


(* Forward lifting *)

(*
  TODO: add limited support for premises, where used variables are not generalized in the conclusion
*)
fun forward_lift_rule ctxt af thm =
  let
    val thm = Object_Logic.rulify ctxt thm;
    val (af_inst, ctxt_inst) = import_afun_inst af ctxt;
    val (prop, ctxt_Ts) = yield_singleton Variable.importT_terms (Thm.prop_of thm) ctxt_inst;
    val (lhs, rhs) = prop |> HOLogic.dest_Trueprop |> HOLogic.dest_eq;
    val ([lhs', rhs'], ctxt_lifted) = generalize_lift_terms af_inst [lhs, rhs] ctxt_Ts;
    val lifted = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs', rhs'));
    val (lifted', ctxt') = yield_singleton (Variable.import_terms true) lifted ctxt_lifted;

    fun tac {prems, context} = HEADGOAL (general_normalize_rel_tac context af THEN'
      head_cong_tac context af [] THEN'
      resolve_tac context [prems MRS thm]);
    val thm' = singleton (Variable.export ctxt' ctxt)
      (Goal.prove ctxt' [] [] lifted' tac);
    val thm'' = Raw_Simplifier.fold_rule ctxt (unfolds_of_afun af) thm';
  in thm'' end;

fun forward_lift_attrib name =
  Thm.rule_attribute [] (fn context => fn thm =>
    let val af = afun_of_generic context (intern context name)  (* FIXME !?!? *)
    in forward_lift_rule (Context.proof_of context) af thm end);


(* High-level tactics *)

fun unfold_wrapper_tac ctxt = AUTO_AFUNS false (fn afs =>
  Simplifier.safe_asm_full_simp_tac (ctxt addsimps flat (map unfolds_of_afun afs))) ctxt;

fun fold_wrapper_tac ctxt = AUTO_AFUN true (fold_goal_tac ctxt o unfolds_of_afun) ctxt;

fun WRAPPER tac ctxt opt_af =
  REPEAT_DETERM o resolve_tac ctxt [@{thm allI}] THEN'
  Subgoal.FOCUS (fn {context = ctxt, params, ...} =>
    let val renames = map (swap o apsnd Thm.term_of) params
    in
      AUTO_AFUNS false (EVERY' o map (afun_unfold_tac ctxt)) ctxt opt_af 1 THEN
      AUTO_AFUN true (fn af =>
        afun_unfold_tac ctxt af THEN'
        CONVERSION Drule.beta_eta_conversion THEN'
        tac ctxt af THEN'
        head_cong_tac ctxt af renames) ctxt opt_af 1
    end) ctxt THEN'
  Raw_Simplifier.rewrite_goal_tac ctxt [Drule.triv_forall_equality];

val normalize_wrapper_tac = WRAPPER normalize_rel_tac;
val lifting_wrapper_tac = WRAPPER general_normalize_rel_tac;

val parse_opt_afun = Scan.peek (fn context =>
  Scan.option Parse.name >> Option.map (intern context #> afun_of_generic context));


(** Declaration **)

(* Combinator setup *)

fun declare_combinators combs phi =
  let
    val (names, thms) = split_list combs;
    val thms' = map (Morphism.thm phi) thms;
    fun add_combs (defs, rules) = (fold (Symtab.insert (K false)) (names ~~ thms') defs, rules);
  in Data.map (map_data add_combs I I) end;

val setup_combinators =
  Local_Theory.declaration {syntax = false, pervasive = false} o declare_combinators;

fun combinator_of_red thm =
  let
    val (lhs, _) = Logic.dest_equals (Thm.prop_of thm);
    val (head, _) = strip_comb lhs;
  in #1 (dest_Const head) end;

fun register_combinator_rule weak_premises thm context =
  let
    val (lhs, rhs) = Logic.dest_equals (Thm.prop_of thm);
    val ltvars = Term.add_tvars lhs [];
    val rtvars = Term.add_tvars rhs [];
    val _ = if exists (not o member op = ltvars) rtvars
      then Pretty.breaks
         [Pretty.str "Combinator equation",
          Pretty.quote (Syntax.pretty_term (Context.proof_of context) (Thm.prop_of thm)),
          Pretty.str "has additional type variables on right-hand side."]
        |> Pretty.block |> Pretty.string_of |> error
      else ();

    val (defs, _) = #combinators (Data.get context);
    val comb_names =
      Symtab.make (map (fn (name, thm) => (combinator_of_red thm, name)) (Symtab.dest defs));
    val rule = mk_combinator_rule comb_names weak_premises thm;
    fun add_rule (defs, rules) = (defs, insert eq_combinator_rule rule rules);
  in Data.map (map_data add_rule I I) context end;

val combinator_rule_attrib = Thm.declaration_attribute o register_combinator_rule;


(* Derivation of combinator reductions *)

fun combinator_closure rules have_weak combs =
  let
    fun apply rule (cs, changed) =
      if not (Ord_List.member fast_string_ord cs (conclusion_of_rule rule)) andalso
        is_applicable_rule rule have_weak (fn prems => Ord_List.subset fast_string_ord (prems, cs))
      then (Ord_List.insert fast_string_ord (conclusion_of_rule rule) cs, true)
      else (cs, changed);
    fun loop cs =
      (case fold apply rules (cs, false) of
        (cs', true) => loop cs'
      | (_, false) => cs);
  in loop combs end;

fun derive_combinator_red ctxt af_inst red_thms (base_thm, eq_thm) =
  let
    val base_prop = Thm.prop_of base_thm;
    val tvars = Term.add_tvars base_prop [];
    val (Ts, ctxt_Ts) = mk_TFrees_of (length tvars) (inner_sort_of af_inst) ctxt;
    val base_prop' = Term_Subst.instantiate (tvars ~~ Ts, []) base_prop;
    val (lhs, rhs) = Logic.dest_equals base_prop';
    val ([lhs', rhs'], ctxt') = generalize_lift_terms af_inst [lhs, rhs] ctxt_Ts;
    val lifted_prop = (lhs', rhs') |> HOLogic.mk_eq |> HOLogic.mk_Trueprop;
    val unfold_comb_conv = HOLogic.Trueprop_conv
      (HOLogic.eq_conv (Conv.top_sweep_conv (K (Conv.rewr_conv eq_thm)) ctxt') Conv.all_conv);
    val tac = HEADGOAL (CONVERSION unfold_comb_conv THEN'
      Raw_Simplifier.rewrite_goal_tac ctxt' red_thms THEN'
      resolve_tac ctxt' [@{thm refl}]);
  in singleton (Variable.export ctxt' ctxt) (Goal.prove ctxt' [] [] lifted_prop (K tac)) end;

(*derive all instantiations with pure terms which can be simplified by homomorphism*)
(*FIXME: more of a workaround than a sensible solution*)
fun weak_red_closure ctxt (af_inst, merge_thm) strong_red =
  let
    val (lhs, _) = Thm.prop_of strong_red |> Logic.dest_equals;
    val vars = rev (Term.add_vars lhs []);
    fun closure [] prev thms = (prev::thms)
      | closure ((v, af_T)::vs) prev thms =
          (case try (dest_type ctxt af_inst) af_T of
            NONE => closure vs prev thms
          | SOME T_opt =>
            let
              val (T, ctxt') = (case T_opt of
                  NONE => yield_singleton Variable.invent_types (inner_sort_of af_inst) ctxt
                    |>> TFree
                | SOME T => (T, ctxt));
              val (v', ctxt'') = mk_Free (#1 v) T ctxt';
              val pure_v = Thm.cterm_of ctxt'' (lift_term af_inst v');
              val next = Drule.instantiate_normalize ([], [((v, af_T), pure_v)]) prev;
              val next' = Raw_Simplifier.rewrite_rule ctxt'' [merge_thm] next;
              val next'' = singleton (Variable.export ctxt'' ctxt) next';
            in closure vs next'' (prev::thms) end);
   in closure vars strong_red [] end;

fun combinator_red_closure ctxt (comb_defs, rules) (af_inst, merge_thm) weak_reds combs =
  let
    val have_weak = not (null weak_reds);
    val red_thms0 = Symtab.fold (fn (_, thm) => cons (mk_meta_eq thm)) combs weak_reds;
    val red_thms = flat (map (weak_red_closure ctxt (af_inst, merge_thm)) red_thms0);
    fun apply rule ((cs, rs), changed) =
      if not (Symtab.defined cs (conclusion_of_rule rule)) andalso
        is_applicable_rule rule have_weak (forall (Symtab.defined cs))
      then
        let
          val conclusion = conclusion_of_rule rule;
          val def = the (Symtab.lookup comb_defs conclusion);
          val new_red_thm = derive_combinator_red ctxt af_inst rs (def, thm_of_rule rule);
          val new_red_thms = weak_red_closure ctxt (af_inst, merge_thm) (mk_meta_eq new_red_thm);
        in ((Symtab.update (conclusion, new_red_thm) cs, new_red_thms @ rs), true) end
      else ((cs, rs), changed);
    fun loop xs =
      (case fold apply rules (xs, false) of
        (xs', true) => loop xs'
      | (_, false) => xs);
  in #1 (loop (combs, red_thms)) end;


(* Preparation of AFun data *)

fun mk_terms ctxt (raw_pure, raw_ap, raw_rel, raw_set) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val show_typ = quote o Syntax.string_of_typ ctxt;
    val show_term = quote o Syntax.string_of_term ctxt;

    fun closed_poly_term t =
      let val poly_t = singleton (Variable.polymorphic ctxt) t;
      in case Term.add_vars (singleton
          (Variable.export_terms (Variable.auto_fixes t ctxt) ctxt) t) [] of
          [] => (case (Term.hidden_polymorphism poly_t) of
              [] => poly_t
            | _ => error ("Hidden type variables in term " ^ show_term t))
        | _ => error ("Locally free variables in term " ^ show_term t)
      end;

    val pure = closed_poly_term raw_pure;
    val (tvar, T1) = fastype_of pure |> dest_funT |>> dest_TVar
      handle TYPE _ => error ("Bad type for pure: " ^ show_typ (fastype_of pure));
    val maxidx_pure = maxidx_of_term pure;
    val ap = Logic.incr_indexes ([], [], maxidx_pure + 1) (closed_poly_term raw_ap);
    fun bad_ap _ = error ("Bad type for ap: " ^ show_typ (fastype_of ap));
    val (T23, (T2, T3)) = fastype_of ap |> dest_funT ||> dest_funT
      handle TYPE _ => bad_ap ();
    val maxidx_common = Term.maxidx_term ap maxidx_pure;

    (*unify type variables, while keeping the live variables separate*)
    fun no_unifier (T, U) = error ("Unable to infer common functor type from " ^
      commas (map show_typ [T, U]));
    fun unify_ap_type T (tyenv, maxidx) =
      let
        val argT = TVar ((Name.aT, maxidx + 1), []);
        val T1' = Term_Subst.instantiateT [(tvar, argT)] T1;
        val (tyenv', maxidx') = Sign.typ_unify thy (T1', T) (tyenv, maxidx + 1)
          handle Type.TUNIFY => no_unifier (T1', T);
      in (argT, (tyenv', maxidx')) end;
    val (ap_args, (ap_env, maxidx_env)) =
      fold_map unify_ap_type [T2, T3, T23] (Vartab.empty, maxidx_common);
    val [T2_arg, T3_arg, T23_arg] = map (Envir.norm_type ap_env) ap_args;
    val (tvar2, tvar3) = (dest_TVar T2_arg, dest_TVar T3_arg) handle TYPE _ => bad_ap ();
    val _ = if T23_arg = T2_arg --> T3_arg then () else bad_ap ();
    val sort = foldl1 (Sign.inter_sort thy) (map #2 [tvar, tvar2, tvar3]);
    val _ = Sign.of_sort thy (Term.aT sort --> Term.aT sort, sort) orelse
      error ("Sort constraint " ^ quote (Syntax.string_of_sort ctxt sort) ^
        " not closed under function types");
    fun update_sort (v, S) (tyenv, maxidx) =
      (Vartab.update_new (v, (S, TVar ((Name.aT, maxidx + 1), sort))) tyenv, maxidx + 1);
    val (common_env, _) = fold update_sort [tvar, tvar2, tvar3] (ap_env, maxidx_env);

    val tvar' = Envir.norm_type common_env (TVar tvar);
    val pure' = norm_term_types common_env pure;
    val (tvar2', tvar3') = apply2 (Envir.norm_type common_env) (T2_arg, T3_arg);
    val ap' = norm_term_types common_env ap;

    fun bad_set set = error ("Bad type for set: " ^ show_typ (fastype_of set));
    fun mk_set set =
      let
        val tyenv = Sign.typ_match thy (domain_type (fastype_of set), range_type (fastype_of pure'))
          Vartab.empty
          handle Type.TYPE_MATCH => bad_set set;
        val set' = Envir.subst_term_types tyenv set;
        val set_tvar = fastype_of set' |> range_type |> HOLogic.dest_setT |> dest_TVar
          handle TYPE _ => bad_set set;
        val _ = if Term.eq_tvar (dest_TVar tvar', set_tvar) then () else bad_set set;
      in ([tvar'], set') end
    val set = (case raw_set of
        NONE => ([tvar'], Abs ("x", tvar', HOLogic.mk_UNIV tvar'))
      | SOME t => mk_set (closed_poly_term t));

    val terms = Term_Subst.zero_var_indexes (pack_poly_terms
      [poly_type_to_term ([tvar'], range_type (fastype_of pure')),
      ([tvar'], pure'), ([tvar2', tvar3'], ap'), set]);

    (*TODO: also infer the relator type?*)
    fun bad_rel rel = error ("Bad type for rel: " ^ show_typ (fastype_of rel));
    fun mk_rel rel =
      let
        val ((T1, T2), (T1_af, T2_af)) = fastype_of rel
          |> dest_funT
          |>> BNF_Util.dest_pred2T
          ||> BNF_Util.dest_pred2T;
        val _ = (dest_TVar T1; dest_TVar T2);
        val _ = if T1 = T2 then bad_rel rel else ();
        val af_inst = mk_afun_inst (match_poly_terms_type ctxt (terms, 0) (T1_af, maxidx_of_term rel));
        val (T1', T2') = apply2 (dest_type ctxt af_inst) (T1_af, T2_af);
        val _ = if (is_none T1' andalso is_none T2') orelse (T1' = SOME T1 andalso T2' = SOME T2)
          then () else bad_rel rel;
      in Term_Subst.zero_var_indexes (pack_poly_terms [([T1, T2], rel)]) end
      handle TYPE _ => bad_rel rel;
    val rel = Option.map (mk_rel o closed_poly_term) raw_rel;
  in (terms, rel) end;

fun mk_rel_intros {pure_transfer, ap_rel_fun} =
  let val pure_rel_intro = pure_transfer RS @{thm rel_funD};
  in [pure_rel_intro, ap_rel_fun] end;

fun mk_afun_thms ctxt af_inst (hom_thm, ichng_thm, reds, rel_axioms) =
  let
    val pure_comp_conv =
      let
        val ([T1, T2, T3], ctxt_Ts) = mk_TFrees_of 3 (inner_sort_of af_inst) ctxt;
        val (((g, f), x), ctxt') = ctxt_Ts
          |> mk_Free "g" (T2 --> T3)
          ||>> mk_Free "f" (mk_type af_inst (T1 --> T2))
          ||>> mk_Free "x" (mk_type af_inst T1);
        val comb = mk_comb af_inst;
        val lhs = comb (T2 --> T3) (lift_term af_inst g, comb (T1 --> T2) (f, x));
        val B_g = Abs ("f", T1 --> T2, Abs ("x", T1, Term.betapply (g, Bound 1 $ Bound 0)));
        val rhs = comb (T1 --> T3)
          (comb ((T1 --> T2) --> T1 --> T3) (lift_term af_inst B_g, f), x);
        val prop = HOLogic.mk_eq (lhs, rhs) |> HOLogic.mk_Trueprop;

        val merge_rule = mk_meta_eq hom_thm;
        val B_intro = the (Symtab.lookup reds "B") |> mk_meta_eq |> Thm.symmetric;
        val tac =
          HEADGOAL (Raw_Simplifier.rewrite_goal_tac ctxt' [B_intro, merge_rule] THEN'
          resolve_tac ctxt' [@{thm refl}]);
      in singleton (Variable.export ctxt' ctxt) (Goal.prove ctxt' [] [] prop (K tac)) end;

    val eq_intros =
      let
        val ([T1, T2], ctxt_Ts) = mk_TFrees_of 2 (inner_sort_of af_inst) ctxt;
        val T12 = mk_type af_inst (T1 --> T2);
        val (((((x, y), x'), f), g), ctxt') = ctxt_Ts
          |> mk_Free "x" T1
          ||>> mk_Free "y" T1
          ||>> mk_Free "x" (mk_type af_inst T1)
          ||>> mk_Free "f" T12
          ||>> mk_Free "g" T12;
        val pure_fun = mk_pure af_inst T1;
        val pure_cong = Drule.infer_instantiate' ctxt'
          (map (SOME o Thm.cterm_of ctxt') [x, y, pure_fun]) @{thm arg_cong};
        val ap_fun = mk_ap af_inst (T1, T2);
        val ap_cong1 = Drule.infer_instantiate' ctxt'
          (map (SOME o Thm.cterm_of ctxt')  [f, g, ap_fun, x']) @{thm arg1_cong};
      in Variable.export ctxt' ctxt [pure_cong, ap_cong1] end;

    val rel_intros = case rel_axioms of
        NONE => []
      | SOME axioms => mk_rel_intros axioms;
  in
    {hom = hom_thm,
      ichng = ichng_thm,
      reds = reds,
      rel_thms = rel_axioms,
      rel_intros = eq_intros @ rel_intros,
      pure_comp_conv = pure_comp_conv}
  end;

fun reuse_TFrees n S (ctxt, Ts) =
  let
    val have_n = Int.min (n, length Ts);
    val (more_Ts, ctxt') = mk_TFrees_of (n - have_n) S ctxt;
  in (take have_n Ts @ more_Ts, (ctxt', Ts @ more_Ts)) end;

fun mk_comb_prop lift_pos thm af_inst ctxt_Ts =
  let
    val base = Thm.prop_of thm;
    val tvars = Term.add_tvars base [];
    val (Ts, (ctxt', Ts')) = reuse_TFrees (length tvars) (inner_sort_of af_inst) ctxt_Ts;
    val base' = Term_Subst.instantiate (tvars ~~ Ts, []) base;
    val (lhs, rhs) = Logic.dest_equals base';
    val (_, lhs_args) = strip_comb lhs;
    val lift_var = Var o apsnd (mk_type af_inst) o dest_Var;
    val (lhs_args', subst) = fold_index (fn (i, v) =>
      if member (op =) lift_pos i then apfst (cons v)
      else map_prod (cons (lift_var v)) (cons (v, lift_var v))) lhs_args ([], []);
    val (lhs', rhs') = apply2 (subst_lift_term af_inst subst) (lhs, rhs);
    val lifted = (lhs', rhs') |> HOLogic.mk_eq |> HOLogic.mk_Trueprop;
  in (fold Logic.all lhs_args' lifted, (ctxt', Ts')) end;

fun mk_homomorphism_prop af_inst ctxt_Ts =
  let
    val ([T1, T2], (ctxt', Ts')) = reuse_TFrees 2 (inner_sort_of af_inst) ctxt_Ts;
    val ((f, x), _) = ctxt'
      |> mk_Free "f" (T1 --> T2)
      ||>> mk_Free "x" T1;
    val lhs = mk_comb af_inst (T1 --> T2) (lift_term af_inst f, lift_term af_inst x);
    val rhs = lift_term af_inst (f $ x);
    val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in (Logic.all f (Logic.all x prop), (ctxt', Ts')) end;

fun mk_interchange_prop af_inst ctxt_Ts =
  let
    val ([T1, T2], (ctxt', Ts')) = reuse_TFrees 2 (inner_sort_of af_inst) ctxt_Ts;
    val ((f, x), _) = ctxt'
      |> mk_Free "f" (mk_type af_inst (T1 --> T2))
      ||>> mk_Free "x" T1;
    val lhs = mk_comb af_inst (T1 --> T2) (f, lift_term af_inst x);
    val T_x = Abs ("f", T1 --> T2, Bound 0 $ x);
    val rhs = mk_comb af_inst ((T1 --> T2) --> T2) (lift_term af_inst T_x, f);
    val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in (Logic.all f (Logic.all x prop), (ctxt', Ts')) end;

fun mk_rel_props (af_inst, rel_inst) ctxt_Ts =
  let
    fun mk_af_rel tm =
      let val (T1, T2) = BNF_Util.dest_pred2T (fastype_of tm);
      in betapply (instantiate_poly_term rel_inst [T1, T2], tm) end;

    val ([T1, T2, T3], (ctxt', Ts')) = reuse_TFrees 3 (inner_sort_of af_inst) ctxt_Ts;
    val (pure_R, _) = mk_Free "R" (T1 --> T2 --> @{typ bool}) ctxt';
    val rel_pure = BNF_Util.mk_rel_fun pure_R (mk_af_rel pure_R) $ mk_pure af_inst T1 $
      mk_pure af_inst T2;
    val pure_prop = Logic.all pure_R (HOLogic.mk_Trueprop rel_pure);

    val ((((f, g), x), ap_R), _) = ctxt'
      |> mk_Free "f" (mk_type af_inst (T1 --> T2))
      ||>> mk_Free "g" (mk_type af_inst (T1 --> T3))
      ||>> mk_Free "x" (mk_type af_inst T1)
      ||>> mk_Free "R" (T2 --> T3 --> @{typ bool});
    val fun_rel = BNF_Util.mk_rel_fun (mk_eq_on (mk_set af_inst T1 $ x)) ap_R;
    val rel_ap = Logic.mk_implies (HOLogic.mk_Trueprop (mk_af_rel fun_rel $ f $ g),
      HOLogic.mk_Trueprop (mk_af_rel ap_R $ mk_comb af_inst (T1 --> T2) (f, x) $
        mk_comb af_inst (T1 --> T3) (g, x)));
    val ap_prop = fold_rev Logic.all [ap_R, f, g, x] rel_ap;
  in ([pure_prop, ap_prop], (ctxt', Ts')) end;

fun mk_interchange ctxt ((comb_defs, _), comb_unfolds) (af_inst, merge_thm) reds =
  let
    val T_def = the (Symtab.lookup comb_defs "T");
    val T_red = the (Symtab.lookup reds "T");
    val (weak_prop, (ctxt', _)) = mk_comb_prop [0] T_def af_inst (ctxt, []);
    fun tac {context, ...} =
      HEADGOAL (Raw_Simplifier.rewrite_goal_tac context [Thm.symmetric merge_thm] THEN'
      resolve_tac context [T_red]);
    val weak_red = singleton (Variable.export ctxt' ctxt) (Goal.prove ctxt' [] [] weak_prop tac);
  in Raw_Simplifier.rewrite_rule ctxt (comb_unfolds) weak_red RS sym end;

fun mk_weak_reds ctxt ((comb_defs, _), comb_unfolds) af_inst (hom_thm, ichng_thm, reds) =
  let
    val unfolded_reds =
      Symtab.map (K (Raw_Simplifier.rewrite_rule ctxt comb_unfolds)) reds;
    val af_thms = mk_afun_thms ctxt af_inst (hom_thm, ichng_thm, unfolded_reds, NONE);
    val af = mk_afun Binding.empty (pack_afun_inst af_inst) NONE af_thms;

    fun tac {context, ...} = HEADGOAL (normalize_wrapper_tac context (SOME af) THEN'
      Raw_Simplifier.rewrite_goal_tac context comb_unfolds THEN'
      resolve_tac context [refl]);
    fun mk comb lift_pos =
      let
        val def = the (Symtab.lookup comb_defs comb);
        val (prop, (ctxt', _)) = mk_comb_prop lift_pos def af_inst (ctxt, []);
        val hol_thm = singleton (Variable.export ctxt' ctxt) (Goal.prove ctxt' [] [] prop tac);
      in mk_meta_eq hol_thm end;

    val uncurry_thm = mk_meta_eq (forward_lift_rule ctxt af @{thm uncurry_pair});
  in
    [mk "C" [1], mk "C" [2], uncurry_thm]
  end;

fun mk_comb_reds ctxt combss af_inst user_combs (hom_thm, user_thms, ichng_thms) =
  let
    val ((comb_defs, comb_rules), comb_unfolds) = combss;
    val merge_thm = mk_meta_eq hom_thm;
    val user_reds = Symtab.make (user_combs ~~ user_thms);
    val reds0 = combinator_red_closure ctxt (comb_defs, comb_rules) (af_inst, merge_thm) [] user_reds;
    val ichng_thm = case ichng_thms of
        [] => singleton (Variable.export ctxt ctxt) (mk_interchange ctxt combss (af_inst, merge_thm) reds0)
      | [thm] => thm;
    val weak_reds = mk_weak_reds ctxt combss af_inst (hom_thm, ichng_thm, reds0);
    val reds1 = combinator_red_closure ctxt (comb_defs, comb_rules) (af_inst, merge_thm) weak_reds reds0;
    val unfold = Raw_Simplifier.rewrite_rule ctxt comb_unfolds;
  in (Symtab.map (K unfold) reds1, ichng_thm) end;

fun note_afun_thms af =
  let
    val thms = thms_of_afun af;
    val named_thms =
      [("homomorphism", [#hom thms]),
        ("interchange", [#ichng thms]),
        ("afun_rel_intros", #rel_intros thms)] @
      map (fn (name, thm) => ("pure_" ^ name ^ "_conv", [thm])) (Symtab.dest (#reds thms)) @
      (case #rel_thms thms of
        NONE => []
      | SOME rel_thms' =>
          [("pure_transfer", [#pure_transfer rel_thms']),
            ("ap_rel_fun_cong", [#ap_rel_fun rel_thms'])]);

    val base_name = Binding.name_of (name_of_afun af);
    fun mk_note (name, thms) =
      ((Binding.qualify true base_name (Binding.name name), []), [(thms, [])]);
  in Local_Theory.notes (map mk_note named_thms) #> #2 end;

fun register_afun af =
  let fun decl phi context = Data.map (fn {combinators, afuns, patterns} =>
    let
      val af' = morph_afun phi af;
      val (name, afuns') = Name_Space.define context true (name_of_afun af', af') afuns;
      val patterns' = Item_Net.update (name, patterns_of_afun af') patterns;
    in {combinators = combinators, afuns = afuns', patterns = patterns'} end) context;
  in Local_Theory.declaration {syntax = false, pervasive = false} decl end;

fun applicative_cmd (((((name, flags), raw_pure), raw_ap), raw_rel), raw_set) lthy =
  let
    val comb_unfolds = Named_Theorems.get lthy @{named_theorems combinator_unfold};
    val comb_reprs = Named_Theorems.get lthy @{named_theorems combinator_repr};
    val (comb_defs, comb_rules) = get_combinators (Context.Proof lthy);

    val _ = fold (fn name =>
      if Symtab.defined comb_defs name then I else error ("Unknown combinator " ^ quote name))
      flags ();
    val _ = if has_duplicates op = flags
      then warning "Ignoring duplicate combinators"
      else ();
    val user_combs0 = Ord_List.make fast_string_ord flags;

    val raw_pure' = Syntax.read_term lthy raw_pure;
    val raw_ap' = Syntax.read_term lthy raw_ap;
    val raw_rel' = Option.map (Syntax.read_term lthy) raw_rel;
    val raw_set' = Option.map (Syntax.read_term lthy) raw_set;
    val (terms, rel) = mk_terms lthy (raw_pure', raw_ap', raw_rel', raw_set');

    val derived_combs0 = combinator_closure comb_rules false user_combs0;
    val required_combs = Ord_List.make fast_string_ord ["B", "I"];
    val user_combs = Ord_List.union fast_string_ord user_combs0
      (Ord_List.subtract fast_string_ord derived_combs0 required_combs);
    val derived_combs1 = combinator_closure comb_rules false user_combs;
    val derived_combs2 = combinator_closure comb_rules true derived_combs1;
    fun is_redundant comb = eq_list (op =) (derived_combs2,
      (combinator_closure comb_rules true (Ord_List.remove fast_string_ord comb user_combs)));
    val redundant_combs = filter is_redundant user_combs;
    val _ = if null redundant_combs then () else
      warning ("Redundant combinators: " ^ commas redundant_combs);
    val prove_interchange = not (Ord_List.member fast_string_ord derived_combs1 "T");

    val (af_inst, ctxt_af) = import_afun_inst_raw terms lthy;
    (* TODO: reuse TFrees from above *)
    val (rel_insts, ctxt_inst) = (case rel of
        NONE => (NONE, ctxt_af)
      | SOME r =>
          let
            val (rel_inst, ctxt') = import_poly_terms r ctxt_af |>> the_single;
            val T = fastype_of (#2 rel_inst) |> range_type |> domain_type;
            val af_inst = match_poly_terms_type ctxt' (terms, 0) (T, ~1) |> mk_afun_inst;
          in (SOME (af_inst, rel_inst), ctxt') end);

    val mk_propss = [apfst single o mk_homomorphism_prop af_inst,
      fold_map (fn comb => mk_comb_prop [] (the (Symtab.lookup comb_defs comb)) af_inst) user_combs,
      if prove_interchange then apfst single o mk_interchange_prop af_inst else pair [],
      if is_some rel then mk_rel_props (the rel_insts) else pair []];
    val (propss, (ctxt_Ts, _)) = fold_map I mk_propss (ctxt_inst, []);

    fun repr_tac ctxt = Raw_Simplifier.rewrite_goals_tac ctxt comb_reprs;
    fun after_qed thmss lthy' =
      let
        val [[hom_thm], user_thms, ichng_thms, rel_thms] = map (Variable.export lthy' ctxt_inst) thmss;
        val (reds, ichng_thm) = mk_comb_reds ctxt_inst ((comb_defs, comb_rules), comb_unfolds)
          af_inst user_combs (hom_thm, user_thms, ichng_thms);
        val rel_axioms = case rel_thms of
            [] => NONE
          | [thm1, thm2] => SOME {pure_transfer = thm1, ap_rel_fun = thm2};
        val af_thms = mk_afun_thms ctxt_inst af_inst (hom_thm, ichng_thm, reds, rel_axioms);
        val af_thms = map_afun_thms (singleton (Variable.export ctxt_inst lthy)) af_thms;
        val af = mk_afun name terms rel af_thms;
      in lthy
        |> register_afun af
        |> note_afun_thms af
      end;
  in
    Proof.theorem NONE after_qed ((map o map) (rpair []) propss) ctxt_Ts
    |> Proof.refine (Method.Basic (SIMPLE_METHOD o repr_tac))
    |> Seq.the_result ""
  end;

fun print_afuns ctxt =
  let
    fun pretty_afun (name, af) =
      let
        val [pT, (_, pure), (_, ap), (_, set)] = unpack_poly_terms (terms_of_afun af);
        val ([tvar], T) = poly_type_of_term pT;
        val rel = Option.map (#2 o the_single o unpack_poly_terms) (rel_of_afun af);
        val combinators = Symtab.keys (#reds (thms_of_afun af));
      in Pretty.block (Pretty.fbreaks ([Pretty.block [Pretty.str name, Pretty.str ":", Pretty.brk 1,
          Pretty.quote (Syntax.pretty_typ ctxt T), Pretty.brk 1, Pretty.str "of", Pretty.brk 1,
          Syntax.pretty_typ ctxt tvar],
        Pretty.block [Pretty.str "pure:", Pretty.brk 1, Pretty.quote (Syntax.pretty_term ctxt pure)],
        Pretty.block [Pretty.str "ap:", Pretty.brk 1, Pretty.quote (Syntax.pretty_term ctxt ap)],
        Pretty.block [Pretty.str "set:", Pretty.brk 1, Pretty.quote (Syntax.pretty_term ctxt set)]] @
        (case rel of
          NONE => []
        | SOME rel' => [Pretty.block [Pretty.str "rel:", Pretty.brk 1,
            Pretty.quote (Syntax.pretty_term ctxt rel')]]) @
        [Pretty.block ([Pretty.str "combinators:", Pretty.brk 1] @
          Pretty.commas (map Pretty.str combinators))])) end;
    val afuns = sort_by #1 (Name_Space.fold_table cons (get_afun_table (Context.Proof ctxt)) []);
  in Pretty.writeln (Pretty.big_list "Registered applicative functors:" (map pretty_afun afuns)) end;


(* Unfolding *)

fun add_unfold_thm name thm context =
  let
    val (lhs, _) = Thm.prop_of thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
      handle TERM _ => error "Not an equation";
    val names = case name of
        SOME n => [intern context n]
      | NONE => case match_typ context (Term.fastype_of lhs) of
          ns as (_::_) => ns
        | [] => error "Unable to determine applicative functor instance";
    val _ = map (afun_of_generic context) names;
    (*TODO: check equation*)
    val thm' = mk_meta_eq thm;
  in fold (fn n => update_afun n (add_unfolds_afun [thm'])) names context end;

fun add_unfold_attrib name = Thm.declaration_attribute (add_unfold_thm name);

(*TODO: attribute to delete unfolds*)

end;
