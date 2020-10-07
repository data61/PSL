(*
  File: items.ML
  Author: Bohua Zhan

  Items and matching on items.
*)

val TY_NULL = "NULL"
val TY_EQ = "EQ"
val TY_VAR = "VAR"
val TY_PROP = "PROP"
val TY_TERM = "TERM"
val TY_PROPERTY = "PROPERTY"

datatype raw_item = Handler of term list * term * thm
                  | Fact of string * term list * thm
type box_item = {uid: int, id: box_id, sc: int, ty_str: string,
                 tname: cterm list, prop: thm}

signature BOXITEM =
sig
  (* Facts. *)
  val var_to_fact: term -> raw_item
  val term_to_fact: term -> raw_item
  val is_fact_raw: raw_item -> bool
  val match_ty_str_raw: string -> raw_item -> bool
  val match_ty_strs_raw: string list -> raw_item -> bool
  val get_tname_raw: raw_item -> term list
  val get_thm_raw: raw_item -> thm
  (* Handlers. *)
  val is_handler_raw: raw_item -> bool
  val dest_handler_raw: raw_item -> term list * term * thm
  (* Misc. functions. *)
  val eq_ritem: raw_item * raw_item -> bool
  val instantiate: (cterm * cterm) list -> raw_item -> raw_item
  val obtain_variant_frees:
      Proof.context * raw_item list -> Proof.context * (cterm * cterm) list

  val null_item: box_item
  val item_with_id: box_id -> box_item -> box_item
  val item_with_incr: box_item -> box_item
  val item_replace_incr: box_item -> box_item
  val eq_item: box_item * box_item -> bool
  val match_ty_str: string -> box_item -> bool
  val match_ty_strs: string list -> box_item -> bool
  (* Misc. functions. *)
  val merged_id: Proof.context -> box_item list -> box_id
  val mk_box_item: Proof.context -> int * box_id * int * raw_item -> box_item
end;

structure BoxItem : BOXITEM =
struct

fun var_to_fact t = Fact (TY_VAR, [t], true_th)
fun term_to_fact t = Fact (TY_TERM, [t], true_th)

fun is_fact_raw ritem =
    case ritem of Fact _ => true | _ => false
fun match_ty_str_raw s ritem =
    case ritem of Fact (ty_str, _, _) => s = "" orelse ty_str = s | _ => false
fun match_ty_strs_raw slist ritem =
    case ritem of Fact (ty_str, _, _) => member (op =) slist ty_str | _ => false
fun get_tname_raw ritem =
    case ritem of Fact (_, ts, _) => ts | _ => raise Fail "get_tname_raw"
fun get_thm_raw ritem =
    case ritem of Fact (_, _, th) => th | _ => raise Fail "get_thm_raw"

fun is_handler_raw ritem =
    case ritem of Handler _ => true | _ => false
fun dest_handler_raw ritem =
    case ritem of Handler (vars, t, ex_th) => (vars, t, ex_th)
                | _ => raise Fail "dest_handler_raw: wrong type"

fun eq_ritem (ritem1, ritem2) =
    case ritem1 of
        Fact (ty1, ts1, th1) =>
        (case ritem2 of
             Fact (ty2, ts2, th2) =>
             ty1 = ty2 andalso eq_list (op aconv) (ts1, ts2) andalso
             Thm.eq_thm_prop (th1, th2)
           | _ => false)
      | Handler (vars1, t1, ex_th1) =>
        (case ritem2 of
             Fact _ => false
           | Handler (vars2, t2, ex_th2) =>
             eq_list (op aconv) (vars1, vars2) andalso t1 aconv t2 andalso
             Thm.eq_thm_prop (ex_th1, ex_th2))

(* Given a context and list of raw items, obtain fresh names of free
   variables for each internal (schematic) variable declared in the
   raw items, and declare the new variables in context. Return the
   substitution from internal schematic variables to the new free
   variables.
 *)
fun obtain_variant_frees (ctxt, ritems) =
    let
      (* Original internal variables. *)
      val all_vars =
          ritems |> filter (match_ty_str_raw TY_VAR) |> maps get_tname_raw
                 |> filter is_Free |> map dest_Free
                 |> filter (Util.is_just_internal o fst)
      (* New names for these variables. *)
      val all_vars' =
          all_vars |> map (fn (x, T) => (Name.dest_internal x, T))
                   |> Variable.variant_frees ctxt []
      val subst = map (apply2 (Thm.cterm_of ctxt o Free)) (all_vars ~~ all_vars')
    in
      (fold Util.declare_free_term (map Free all_vars') ctxt, subst)
    end

(* Here inst is the return value of obtain_variant_frees. Perform the
   replacement on the ritems.
 *)
fun instantiate subst ritem =
    let
      val subst_fun = Term.subst_atomic (map (apply2 Thm.term_of) subst)
    in
      case ritem of
          Handler (vars, t, ex_th) =>
          Handler (map subst_fun vars, subst_fun t,
                   Util.subst_thm_atomic subst ex_th)
        | Fact (ty_str, tname, th) =>
          Fact (ty_str, map subst_fun tname, Util.subst_thm_atomic subst th)
    end

val null_item = {uid = 0, id = [], sc = 0, ty_str = TY_NULL,
                 tname = [], prop = true_th}
fun item_with_id id {uid, sc, ty_str, tname, prop, ...} =
    {uid = uid, id = id, sc = sc, ty_str = ty_str, tname = tname, prop = prop}
fun item_with_incr item =
    item_with_id (BoxID.add_incr_id (#id item)) item
fun item_replace_incr item =
    item_with_id (BoxID.replace_incr_id (#id item)) item
fun eq_item (item1, item2) = (#uid item1 = #uid item2)
fun match_ty_str s {ty_str, ...} = (s = "" orelse s = ty_str)
fun match_ty_strs slist {ty_str, ...} = member (op =) slist ty_str

fun merged_id ctxt items =
    case items of
        [] => []
      | {id, ...} :: items' => BoxID.merge_boxes ctxt (id, merged_id ctxt items')

fun mk_box_item ctxt (uid, id, sc, ritem) =
    case ritem of
        Handler _ => raise Fail "mk_box_item: ritem must be Fact"
      | Fact (ty_str, ts, prop) =>
        {uid = uid, id = id, sc = sc, ty_str = ty_str,
         tname = map (Thm.cterm_of ctxt) ts, prop = prop}

end  (* structure BoxItem. *)

(* Specifies a method for matching patterns against items.

   - pre_match is a filter function checking whether it is possible
     for the pattern to match the item, after possibly instantiating
     some schematic variables in the pattern (for example, this
     function should always return true if input pattern is ?A).

   - match is the actual matching function, returning instantiation,
     as well as theorem justifying the instantiated pattern.

   If the matcher is for justifying a proposition, the input term to
   pre_match and match is of type bool. Othewise, the restrictions
   depend on type of item to match.
 *)
type item_matcher = {
  pre_match: term -> box_item -> Proof.context -> bool,
  match: term -> box_item -> Proof.context -> id_inst -> id_inst_th list
}

(* Output function for items of a given type. *)
type item_output = Proof.context -> term list * thm -> string

(* Data structure containing methods involved in the input / output of
   items of a given type.

   - prop_matchers: methods for matching the item against a desired
     proposition.

   - typed_matchers: methods for matching the item against a pattern
     for items of the same type.

   - output_fn: printing function of theorems. Input is tname and the
     proposition.
 *)
type item_io_info = {
  prop_matchers: item_matcher list,
  typed_matchers: item_matcher list,
  term_fn: (term list -> term list) option,
  output_fn: item_output option,
  shadow_fn: (Proof.context -> box_id -> term list * cterm list -> bool) option
}

datatype match_arg = PropMatch of term
                   | TypedMatch of string * term
                   | TypedUniv of string
                   | PropertyMatch of term
                   | WellFormMatch of term * term

type prfstep_filter = Proof.context -> id_inst -> bool

signature ITEM_IO =
sig
  val pat_of_match_arg: match_arg -> term
  val subst_arg: Type.tyenv * Envir.tenv -> match_arg -> match_arg
  val assert_valid_arg: match_arg -> unit
  val check_ty_str: string -> match_arg -> bool
  val is_ordinary_match: match_arg -> bool
  val is_side_match: match_arg -> bool

  val add_item_type:
      string * (term list -> term list) option *
      item_output option *
      (Proof.context -> box_id -> term list * cterm list -> bool) option ->
      theory -> theory
  val add_prop_matcher: string * item_matcher -> theory -> theory
  val add_typed_matcher: string * item_matcher -> theory -> theory
  val get_io_info: theory -> string -> item_io_info
  val get_prop_matchers: theory -> string -> item_matcher list
  val get_typed_matchers: theory -> string -> item_matcher list
  val prop_matcher: item_matcher
  val term_prop_matcher: item_matcher
  val null_eq_matcher: item_matcher
  val term_typed_matcher: item_matcher
  val eq_tname_typed_matcher: item_matcher
  val null_property_matcher: item_matcher
  val term_property_matcher: item_matcher
  val pre_match_arg: Proof.context -> match_arg -> box_item -> bool
  val match_arg: Proof.context -> match_arg -> box_item -> id_inst ->
                 id_inst_th list

  val no_rewr_terms: term list -> term list
  val rewr_terms_of_item: Proof.context -> string * term list -> term list
  val output_prop_fn: item_output
  val string_of_item_info: Proof.context -> string * term list * thm -> string
  val add_basic_item_io: theory -> theory
  val string_of_raw_item: Proof.context -> raw_item -> string
  val string_of_item: Proof.context -> box_item -> string
  val trace_ritem: Proof.context -> string -> raw_item -> unit
  val trace_item: Proof.context -> string -> box_item -> unit
  val trace_ritems: Proof.context -> string -> raw_item list -> unit
  val trace_items: Proof.context -> string -> box_item list -> unit
end;

structure ItemIO : ITEM_IO =
struct

fun add_prop_matcher_to_info
        mtch {prop_matchers, typed_matchers, term_fn, output_fn, shadow_fn} =
    {prop_matchers = mtch :: prop_matchers, typed_matchers = typed_matchers,
     term_fn = term_fn, output_fn = output_fn, shadow_fn = shadow_fn}

fun add_typed_matcher_to_info
        mtch {prop_matchers, typed_matchers, term_fn, output_fn, shadow_fn} =
    {prop_matchers = prop_matchers, typed_matchers = mtch :: typed_matchers,
     term_fn = term_fn, output_fn = output_fn, shadow_fn = shadow_fn}

fun join_infos (
  {prop_matchers = pm1, typed_matchers = tm1, term_fn = tf1, output_fn = of1,
   shadow_fn = sf1},
  {prop_matchers = pm2, typed_matchers = tm2, term_fn = tf2, output_fn = of2,
   shadow_fn = sf2}) =
    {prop_matchers = merge pointer_eq (pm1, pm2),
     typed_matchers = merge pointer_eq (tm1, tm2),
     term_fn = (if pointer_eq (tf1, tf2) then tf1
                else raise Fail "join_infos: term_fn non-equal"),
     output_fn = (if pointer_eq (of1, of2) then of1
                  else raise Fail "join_infos: output_fn non-equal"),
     shadow_fn = (if pointer_eq (sf1, sf2) then sf1
                  else raise Fail "join_infos: shadow_fn non-equal")}

structure Data = Theory_Data (
  type T = item_io_info Symtab.table
  val empty = Symtab.empty
  val extend = I;
  val merge = Symtab.join (fn _ => join_infos)
)

fun pat_of_match_arg arg =
    case arg of
        PropMatch pat => pat
      | TypedMatch (_, pat) => pat
      | TypedUniv _ => Term.dummy
      | PropertyMatch pat => pat
      | WellFormMatch (_, req) => req

fun subst_arg inst arg =
    case arg of
        PropMatch pat => PropMatch (Util.subst_term_norm inst pat)
      | TypedMatch (ty_str, pat) =>
        TypedMatch (ty_str, Util.subst_term_norm inst pat)
      | TypedUniv ty_str => TypedUniv ty_str
      | PropertyMatch pat =>
        PropertyMatch (Util.subst_term_norm inst pat)
      | WellFormMatch (t, req) =>
        WellFormMatch (Util.subst_term_norm inst t, Util.subst_term_norm inst req)

fun assert_valid_arg arg =
    case arg of
        PropMatch pat =>
        assert (fastype_of pat = boolT)
               "assert_valid_arg: arg for PropMatch should be bool."
      | TypedMatch _ => ()
      | TypedUniv _ => ()
      | PropertyMatch pat =>
        assert (fastype_of pat = boolT)
               "assert_valid_arg: arg for PropertyMatch should be bool."
      | WellFormMatch (_, req) =>
        assert (fastype_of req = boolT)
               "assert_valid_arg: arg for WellFormMatch should be bool."

fun check_ty_str ty_str arg =
    case arg of
        TypedMatch (ty_str', _) => ty_str = ty_str'
      | TypedUniv ty_str' => ty_str = ty_str'
      | _ => true

fun is_ordinary_match arg =
    case arg of PropMatch _ => true
              | TypedMatch _ => true
              | _ => false

fun is_side_match arg =
    case arg of PropertyMatch _ => true
              | WellFormMatch _ => true
              | _ => false

fun add_item_type (ty_str, term_fn, output_fn, shadow_fn) =
    let
      val item_info = {prop_matchers = [], typed_matchers = [],
                       term_fn = term_fn, output_fn = output_fn,
                       shadow_fn = shadow_fn}
    in
      Data.map (Symtab.update_new (ty_str, item_info))
    end

fun add_prop_matcher (ty_str, it_match) = Data.map (
      Symtab.map_entry ty_str (add_prop_matcher_to_info it_match))

fun add_typed_matcher (ty_str, it_match) = Data.map (
      Symtab.map_entry ty_str (add_typed_matcher_to_info it_match))

fun get_io_info thy ty_str =
    the (Symtab.lookup (Data.get thy) ty_str)
    handle Option.Option => raise Fail ("get_io_info: not found " ^ ty_str)

fun get_prop_matchers thy ty_str = #prop_matchers (get_io_info thy ty_str)
fun get_typed_matchers thy ty_str = #typed_matchers (get_io_info thy ty_str)

(* Prop-matching with a PROP item. *)
val prop_matcher =
    let
      fun pre_match pat {tname, ...} ctxt =
          let
            val ct = the_single tname
            val t = Thm.term_of ct
          in
            if is_neg pat then
              is_neg t andalso
              Matcher.pre_match_head ctxt (get_neg pat, UtilLogic.get_cneg ct)
            else
              Term.is_Var pat orelse
              (not (is_neg t) andalso Matcher.pre_match_head ctxt (pat, ct))
          end

      fun match pat {tname, prop, ...} ctxt (id, inst) =
          let
            val ct = the_single tname
            val t = Thm.term_of ct
          in
            if is_neg pat andalso is_neg t then
              let
                val insts' = Matcher.rewrite_match_head
                                 ctxt (get_neg pat, UtilLogic.get_cneg ct) (id, inst)
                fun process_inst (inst, eq_th) =
                    let
                      (* This version certainly will not cancel ~~ on
                         two sides.
                       *)
                      val make_neg_eq' = Thm.combination (Thm.reflexive UtilBase.cNot)
                    in
                      (inst, Thm.equal_elim (
                         make_trueprop_eq (make_neg_eq' (meta_sym eq_th))) prop)
                    end
              in
                map process_inst insts'
              end
            else if not (is_neg pat) andalso
                    (Term.is_Var pat orelse not (is_neg t)) then
              let
                val insts' = Matcher.rewrite_match_head ctxt (pat, ct) (id, inst)
                fun process_inst (inst, eq_th) =
                    (inst, Thm.equal_elim (
                       make_trueprop_eq (meta_sym eq_th)) prop)
              in
                map process_inst insts'
              end
            else []
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Prop-matching with a TERM item (used to justify equalities). *)
val term_prop_matcher =
    let
      fun pre_match pat {tname, ...} ctxt =
          if not (Util.has_vars pat) then false
          else if is_eq_term pat then
            Matcher.pre_match ctxt (fst (dest_eq pat), the_single tname)
          else false

      fun match pat {tname, ...} ctxt (id, inst) =
          if not (is_eq_term pat) then [] else
          if not (Util.has_vars pat) then [] else
          let
            val (lhs, rhs) = dest_eq pat
            val cu = the_single tname
            val pairs = if Term.is_Var lhs then
                          [(false, (lhs, cu)), (true, (rhs, cu))]
                        else [(true, (lhs, cu)), (false, (rhs, cu))]
            val insts' = Matcher.rewrite_match_list ctxt pairs (id, inst)
            fun process_inst (inst, ths) =
                let
                  (* th1: lhs(env) == u, th2: rhs(env) == u. *)
                  val (th1, th2) = the_pair ths
                in
                  (inst, to_obj_eq (Util.transitive_list [th1, meta_sym th2]))
                end
          in
            map process_inst insts'
          end
    in
      {pre_match = pre_match, match = match}
    end

val null_eq_matcher =
    let
      fun pre_match pat _ _ = is_eq_term pat

      fun match pat _ ctxt (id, inst) =
          if not (is_eq_term pat) then [] else
          if Util.has_vars pat then [] else
          let
            val (lhs, rhs) = dest_eq pat
            val infos = RewriteTable.equiv_info_t ctxt id (lhs, rhs)
            fun process_info (id', th) =
                ((id', inst), to_obj_eq th)
          in
            map process_info infos
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Typed matching with a TERM item. *)
val term_typed_matcher =
    let
      fun pre_match pat {tname, ...} ctxt =
          Matcher.pre_match_head ctxt (pat, the_single tname)

      (* Return value is (inst, eq), where eq is pat(inst) == tname. *)
      fun match pat {tname, ...} ctxt (id, inst) =
          Matcher.rewrite_match_head ctxt (pat, the_single tname) (id, inst)
    in
      {pre_match = pre_match, match = match}
    end

(* Typed matching for items representing an equality ?A = ?B, where
   the tname is the pair (?A, ?B). Pattern is expected to be of the
   form ?A = ?B.
 *)
val eq_tname_typed_matcher =
    let
      fun pre_match pat {tname, ...} ctxt =
          let
            val thy = Proof_Context.theory_of ctxt
            val (lhs, rhs) = the_pair (map Thm.term_of tname)
            val _ = Pattern.first_order_match thy (pat, mk_eq (lhs, rhs)) fo_init
          in
            true
          end
          handle Pattern.MATCH => false

      fun match pat {tname, ...} ctxt (id, inst) =
          let
            val thy = Proof_Context.theory_of ctxt
            val (lhs, rhs) = the_pair (map Thm.term_of tname)
            val inst' =
                Pattern.first_order_match thy (pat, mk_eq (lhs, rhs)) inst
          in
            [((id, inst'), true_th)]
          end
          handle Pattern.MATCH => []
    in
      {pre_match = pre_match, match = match}
    end

(* Obtain a proposition from the property table. *)
val null_property_matcher =
    let
      fun pre_match pat _ _ =
          Property.is_property pat

      fun match pat _ ctxt (id, inst) =
          if Util.has_vars pat then []
          else if not (Property.is_property pat) then []
          else map (fn (id', th) => ((id', inst), th))
                   (PropertyData.get_property_t ctxt (id, pat))
    in
      {pre_match = pre_match, match = match}
    end

(* Obtain a proposition from the property table, matching the argument
   of the property with the given term.
 *)
val term_property_matcher =
    let
      fun pre_match pat {tname, ...} ctxt =
          Property.is_property pat andalso
          Matcher.pre_match_head ctxt (
            Property.get_property_arg pat, the_single tname)

      fun match pat {tname, ...} ctxt (id, inst) =
          if not (Util.has_vars pat) then [] else
          if not (Property.is_property pat) then
            []
          else let
            val arg = Property.get_property_arg pat
          in
            let
              val insts' = Matcher.rewrite_match_head
                               ctxt (arg, the_single tname) (id, inst)
              fun process_inst ((id', inst'), _) =
                  let
                    val t = Util.subst_term_norm inst' pat
                  in
                    map (fn (id'', th) => ((id'', inst'), th))
                        (PropertyData.get_property_t ctxt (id', t))
                  end
            in
              maps process_inst insts'
            end
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Generic pre-matching function. Returns whether there is a possible
   match among any of the registered matchers.
 *)
fun pre_match_arg ctxt arg (item as {ty_str, ...}) =
    if not (check_ty_str ty_str arg) then false else
    let
      val _ = assert_valid_arg arg
      val thy = Proof_Context.theory_of ctxt
      val {prop_matchers, typed_matchers, ...} = get_io_info thy ty_str
    in
      case arg of
          PropMatch pat =>
          Term.is_Var pat orelse
          (is_neg pat andalso Term.is_Var (get_neg pat)) orelse
          not (Util.is_pattern pat) orelse
          exists (fn f => f pat item ctxt) (map #pre_match prop_matchers)
        | TypedMatch (_, pat) =>
          not (Util.is_pattern pat) orelse
          exists (fn f => f pat item ctxt) (map #pre_match typed_matchers)
        | TypedUniv _ => true
        | PropertyMatch _ =>
          raise Fail "pre_match_arg: should not be called on PropertyMatch."
        | WellFormMatch _ =>
          raise Fail "pre_match_arg: should not be called on WellFormMatch."
    end

(* Generic matching function. Returns list of all matches (iterating
   over all registered matchers for the given item type. Note box_id
   for item is taken into account here.
 *)
fun match_arg ctxt arg (item as {id, ty_str, ...}) (id', inst) =
    if not (check_ty_str ty_str arg) then [] else
    let
      val _ = assert_valid_arg arg
      val thy = Proof_Context.theory_of ctxt
      val {prop_matchers, typed_matchers, ...} = get_io_info thy ty_str
      val pat = pat_of_match_arg arg
      val id'' = BoxID.merge_boxes ctxt (id, id')
    in
      case arg of
          PropMatch _ => maps (fn f => f pat item ctxt (id'', inst))
                              (map #match prop_matchers)
        | TypedUniv _ => [((id'', inst), true_th)]
        | TypedMatch _ => maps (fn f => f pat item ctxt (id'', inst))
                               (map #match typed_matchers)
        | PropertyMatch _ =>
          raise Fail "match_arg: should not be called on PropertyMatch."
        | WellFormMatch _ =>
          raise Fail "match_arg: should not be called on WellFormMatch."
    end

val no_rewr_terms = K []

fun arg_rewr_terms ts = maps Util.dest_args ts

fun prop_rewr_terms ts =
    let
      val t = the_single ts
    in
      if is_neg t then t |> dest_arg |> Util.dest_args
      else t |> Util.dest_args
    end

fun rewr_terms_of_item ctxt (ty_str, tname) =
    let
      val thy = Proof_Context.theory_of ctxt
      val {term_fn, ...} = get_io_info thy ty_str
    in
      case term_fn of
          NONE => tname
        | SOME f => f tname
    end

fun output_prop_fn ctxt (_, th) = Thm.prop_of th |> Syntax.string_of_term ctxt

fun string_of_item_info ctxt (ty_str, ts, th) =
    let
      val thy = Proof_Context.theory_of ctxt
      val {output_fn, ...} = get_io_info thy ty_str
    in
      case output_fn of
          NONE => ty_str ^ " " ^ (Util.string_of_terms ctxt ts)
        | SOME f => f ctxt (ts, th)
    end

fun string_of_raw_item ctxt ritem =
    case ritem of
        Handler (_, t, _) => "Handler " ^ (Syntax.string_of_term ctxt t)
      | Fact info => string_of_item_info ctxt info

fun string_of_item ctxt {ty_str, tname, prop, ...} =
    string_of_item_info ctxt (ty_str, map Thm.term_of tname, prop)

fun trace_ritem ctxt s ritem =
    tracing (s ^ " " ^ (string_of_raw_item ctxt ritem))

fun trace_ritems ctxt s ritems =
    tracing (s ^ "\n" ^ (cat_lines (map (string_of_raw_item ctxt) ritems)))

fun trace_item ctxt s item =
    tracing (s ^ " " ^ (string_of_item ctxt item))

fun trace_items ctxt s items =
    tracing (s ^ "\n" ^ (cat_lines (map (string_of_item ctxt) items)))

(* We assume ts1 is the new item at the given id, while cts2 is for an
   existing item, at some previous id.
 *)
fun shadow_prop_fn ctxt id (ts1, cts2) =
    let
      val (t1, ct2) = (the_single ts1, the_single cts2)
      val (lhs, crhs) = if is_neg t1 andalso is_neg (Thm.term_of ct2) then
                          (get_neg t1, UtilLogic.get_cneg ct2)
                        else
                          (t1, ct2)
    in
      (Matcher.rewrite_match_head ctxt (lhs, crhs) (id, fo_init))
          |> filter (fn ((id', _), _) => id' = id)
          |> not o null
    end

fun shadow_term_fn ctxt id (ts1, cts2) =
    let
      val (lhs, crhs) = (the_single ts1, the_single cts2)
    in
      (Matcher.rewrite_match_head ctxt (lhs, crhs) (id, fo_init))
          |> filter (fn ((id', _), _) => id' = id)
          |> not o null
    end

val add_basic_item_io =
    fold add_item_type [
      (TY_NULL, NONE, NONE, NONE),
      (TY_PROP, SOME prop_rewr_terms, SOME output_prop_fn, SOME shadow_prop_fn),
      (TY_TERM, SOME no_rewr_terms, NONE, SOME shadow_term_fn),
      (TY_EQ, NONE, SOME output_prop_fn, NONE),
      (TY_VAR, NONE, NONE, NONE),
      (TY_PROPERTY, SOME arg_rewr_terms, NONE, NONE)

    ] #> fold add_prop_matcher [
      (TY_PROP, prop_matcher), (TY_TERM, term_prop_matcher),
      (TY_NULL, null_eq_matcher), (TY_NULL, null_property_matcher),
      (TY_TERM, term_property_matcher)

    ] #> fold add_typed_matcher [
      (TY_PROP, prop_matcher), (TY_TERM, term_typed_matcher),
      (TY_VAR, term_typed_matcher), (TY_EQ, eq_tname_typed_matcher)
    ]

end  (* structure ItemIO. *)
