(*
  File: rewrite.ML
  Author: Bohua Zhan

  Maintains the congruence closure of the currently known equalities.
  Automatically apply transitivity and the congruence property.
*)

(* Order on equality theorems, by comparing the right side. *)
val simp_ord = Term_Ord.term_ord o (apply2 Util.rhs_of)

(* Equality on box_id * thm, comparing the right side. *)
fun eq_info ((id, th), (id', th')) =
    (id = id' andalso Util.rhs_of th aconv Util.rhs_of th')

(* Debug functions. *)
fun print_info ctxt (id, th) = "(" ^ (BoxID.string_of_box_id id) ^ ", " ^
                               (th |> Util.rhs_of |> Syntax.string_of_term ctxt) ^ ")"
fun print_infos ctxt lst = commas (map (print_info ctxt) lst)
fun print_info' ctxt (id, ths) =
    "(" ^ (BoxID.string_of_box_id id) ^ ", " ^
    (ths |> map Util.rhs_of |> Util.string_of_terms ctxt) ^ ")"
fun print_infos' ctxt lst = cat_lines (map (print_info' ctxt) lst)

(* Data structure for rewrite table. *)
type rewrite_table = {
  (* terms[t] is the list of ids at which t is present. *)
  terms: (box_id list * cterm) Termtab.table,
  (* equiv[a] is list of (id, th), where th is "a == a'" under id. *)
  equiv: ((box_id * thm) list) Termtab.table,
  (* Index of reachability under equiv. *)
  all_equiv: ((box_id * thm) list) Termtab.table,
  (* contain[A] is the list of terms for which A is a direct subterm. *)
  contain: (cterm list) Termtab.table,
  (* Rewrite info of a term. *)
  simp: ((box_id * thm) list) Termtab.table,
  (* Subterm rewrite info of a term. *)
  subsimp: ((box_id * thm) list) Termtab.table,
  (* Reverse of subsimp. Head rep of a term. *)
  reps: ((box_id * thm) list) Termtab.table
}

signature REWRITE_TABLE =
sig
  (* Construction and modification. *)
  val clean_resolved: box_id -> Proof.context -> Proof.context
  val clear_incr: Proof.context -> Proof.context

  (* contain table. *)
  val add_contain: cterm -> term -> Proof.context -> Proof.context
  val immediate_contains: Proof.context -> term -> cterm list

  (* terms table. *)
  val in_table_raw_ids: Proof.context -> term -> box_id list
  val in_table_raw_for_id: Proof.context -> box_id * term -> bool
  val in_table_raw: Proof.context -> term -> bool
  val add_term_raw: box_id * cterm -> Proof.context -> Proof.context
  val get_all_terms: Proof.context -> cterm list
  val get_all_id_terms: Proof.context -> (box_id * cterm) list

  (* equiv table. *)
  val add_equiv: box_id * thm -> Proof.context -> Proof.context
  val equiv_neighs: Proof.context -> term -> (box_id * thm) list
  val get_all_equiv: Proof.context -> term -> (box_id * thm) list

  (* simp table. *)
  val update_simp: box_id * thm -> Proof.context -> Proof.context
  val get_rewrite_info: Proof.context -> cterm -> (box_id * thm) list
  val get_rewrite: box_id -> Proof.context -> cterm -> thm

  (* subsimp and rep tables. *)
  val get_subterm_rewrite_info: Proof.context -> cterm -> (box_id * thm) list
  val remove_rep: box_id * thm -> Proof.context -> Proof.context
  val update_subsimp: box_id * thm -> Proof.context -> Proof.context
  val get_head_rep_info: Proof.context -> term -> (box_id * thm) list
  val get_head_rep: box_id -> Proof.context -> term -> thm option
  val get_head_rep_with_id_th:
      Proof.context -> box_id * thm -> (box_id * thm) list
  val get_cached_subterm_rewrite_info:
      Proof.context -> term -> (box_id * thm) list
  val get_cached_subterm_rewrite: box_id -> Proof.context -> cterm -> thm

  (* Simplification of arbitrary terms. *)
  val head_simplify: box_id -> Proof.context -> cterm -> thm
  val simplify: box_id -> Proof.context -> cterm -> thm
  val subterm_simplify: box_id -> Proof.context -> cterm -> thm
  val simp_val: box_id -> Proof.context -> cterm -> cterm
  val simp_val_t: box_id -> Proof.context -> term -> term
  val simplify_info: Proof.context -> cterm -> (box_id * thm) list
  val subterm_simplify_info: Proof.context -> cterm -> (box_id * thm) list
  val is_equiv: box_id -> Proof.context -> cterm * cterm -> bool
  val is_equiv_t: box_id -> Proof.context -> term * term -> bool

  (* Computation of head equiv. *)
  val get_head_equiv: Proof.context -> cterm -> (box_id * thm) list
  val get_head_equiv_with_t:
      Proof.context -> box_id * cterm -> term -> (box_id * thm) list

  (* Update of whole rewrite table. *)
  val process_update_simp: (box_id * thm) list -> Proof.context -> Proof.context
  val equiv_info:
      Proof.context -> box_id -> cterm * cterm -> (box_id * thm) list
  val equiv_info_t:
      Proof.context -> box_id -> term * term -> (box_id * thm) list
  val subequiv_info:
      Proof.context -> box_id -> cterm * cterm -> (box_id * thm) list
  val add_rewrite_raw: box_id -> thm -> Proof.context -> Proof.context
  val get_reachable_terms: bool -> Proof.context -> term list -> term list
  val complete_table: Proof.context -> (box_id * thm) list * Proof.context
  val add_term:
      box_id * cterm -> Proof.context -> (box_id * thm) list * Proof.context
  val add_term_list:
      (box_id * cterm) list -> Proof.context -> (box_id * thm) list * Proof.context
  val add_rewrite:
      box_id * thm -> Proof.context -> (box_id * thm) list * Proof.context

  (* Updating rewrite table from list of (id, th) pairs. *)
  val get_new_terms: Proof.context * Proof.context -> (box_id * cterm) list
end;

structure RewriteTable : REWRITE_TABLE =
struct

(*** Initialization and modification of rewrite table ***)

structure Data = Proof_Data
(
  type T = rewrite_table
  fun init _ = {terms = Termtab.empty, equiv = Termtab.empty,
                all_equiv = Termtab.empty, contain = Termtab.empty,
                simp = Termtab.empty, subsimp = Termtab.empty,
                reps = Termtab.empty}
)

fun clean_resolved id ctxt =
    let
      val {terms, equiv, all_equiv, contain, simp, subsimp, reps} =
          Data.get ctxt

      fun clean tb id_fun =
          tb |> Termtab.map
             (fn _ => filter_out (BoxID.is_eq_ancestor ctxt id o id_fun))

      fun clean_terms_1 (ids, ct) =
          (filter_out (BoxID.is_eq_ancestor ctxt id) ids, ct)

      fun clean_terms tb =
          tb |> Termtab.map (fn _ => clean_terms_1)
    in
      ctxt |> Data.map (
        K {terms = clean_terms terms, equiv = clean equiv fst,
           all_equiv = clean all_equiv fst,
           contain = contain, simp = clean simp fst, subsimp = clean subsimp fst,
           reps = clean reps fst})
    end

(* equiv_eq_better ctxt info1 info2 means info2 is extraneous in the
   equiv table.
 *)
fun equiv_eq_better ctxt (id, th) (id', th') =
    Util.rhs_of th aconv Util.rhs_of th' andalso BoxID.is_eq_ancestor ctxt id id'

(* simp_eq_better ctxt info1 info2 means info2 is extraneous in the
   simp table.
 *)
fun simp_eq_better ctxt (id, th) (id', th') =
    if BoxID.is_eq_ancestor ctxt id id' then
      let val (t, t') = (Util.rhs_of th, Util.rhs_of th')
      in t aconv t' orelse Term_Ord.term_ord (t, t') = LESS end
    else false

fun clear_incr ctxt =
    let
      val {terms, equiv, all_equiv, contain, simp, subsimp, reps} =
          Data.get ctxt

      fun clear_one cmp infos =
          if exists (BoxID.has_incr_id o fst) infos then
            infos |> map (apfst BoxID.replace_incr_id)
                  |> Util.max_partial cmp
          else
            infos

      fun clear cmp tb =
          tb |> Termtab.map (fn _ => clear_one cmp)

      fun clear_term_one (ids, ct) =
          if exists BoxID.has_incr_id ids then
            (ids |> map BoxID.replace_incr_id
                 |> Util.max_partial (BoxID.is_eq_ancestor ctxt), ct)
          else
            (ids, ct)

      fun clear_term tb =
          tb |> Termtab.map (fn _ => clear_term_one)
    in
      ctxt |> Data.map (
        K {terms = clear_term terms,
           equiv = clear (equiv_eq_better ctxt) equiv,
           all_equiv = clear (equiv_eq_better ctxt) all_equiv,
           contain = contain,
           simp = clear (simp_eq_better ctxt) simp,
           subsimp = clear (simp_eq_better ctxt) subsimp,
           reps = clear (equiv_eq_better ctxt) reps})
    end

fun map_terms f {terms, equiv, all_equiv, contain, simp, subsimp, reps} =
    {terms = f terms, equiv = equiv, all_equiv = all_equiv,
     contain = contain, simp = simp, subsimp = subsimp, reps = reps}

fun map_equiv f {terms, equiv, all_equiv, contain, simp, subsimp, reps} =
    {terms = terms, equiv = f equiv, all_equiv = all_equiv,
     contain = contain, simp = simp, subsimp = subsimp, reps = reps}

fun map_all_equiv f {terms, equiv, all_equiv, contain, simp, subsimp, reps} =
    {terms = terms, equiv = equiv, all_equiv = f all_equiv,
     contain = contain, simp = simp, subsimp = subsimp, reps = reps}

fun map_contain f {terms, equiv, all_equiv, contain, simp, subsimp, reps} =
    {terms = terms, equiv = equiv, all_equiv = all_equiv,
     contain = f contain, simp = simp, subsimp = subsimp, reps = reps}

fun map_simp f {terms, equiv, all_equiv, contain, simp, subsimp, reps} =
    {terms = terms, equiv = equiv, all_equiv = all_equiv,
     contain = contain, simp = f simp, subsimp = subsimp, reps = reps}

fun map_subsimp f {terms, equiv, all_equiv, contain, simp, subsimp, reps} =
    {terms = terms, equiv = equiv, all_equiv = all_equiv,
     contain = contain, simp = simp, subsimp = f subsimp, reps = reps}

fun map_reps f {terms, equiv, all_equiv, contain, simp, subsimp, reps} =
    {terms = terms, equiv = equiv, all_equiv = all_equiv,
     contain = contain, simp = simp, subsimp = subsimp, reps = f reps}

(*** Basic manipulation of contain table. ***)

(* Add the information that t contains subt directly. *)
fun add_contain ct subt ctxt =
    let
      val {contain, ...} = Data.get ctxt
      val contain_subt = the_default [] (Termtab.lookup contain subt)
    in
      if member (op aconvc) contain_subt ct then ctxt
      else ctxt |> Data.map (map_contain (Termtab.update (subt,  ct :: contain_subt)))
    end

(* Get all terms that directly contains t. *)
fun immediate_contains ctxt t =
    let
      val {contain, ...} = Data.get ctxt
    in
      the_default [] (Termtab.lookup contain t)
    end

(*** Basic manipulation of the terms table. ***)

(* Return ids in which t is directly in table. *)
fun in_table_raw_ids ctxt t =
    let
      val {terms, ...} = Data.get ctxt
    in
      case Termtab.lookup terms t of
          NONE => []
        | SOME (ids, _) => ids
    end

(* Whether the term is present in table at the given id. *)
fun in_table_raw_for_id ctxt (id, t) =
    exists (BoxID.is_eq_descendent ctxt id) (in_table_raw_ids ctxt t)

(* Whether the term is present at any id. *)
fun in_table_raw ctxt t =
    length (in_table_raw_ids ctxt t) > 0

(* Add t to table at the given id. *)
fun add_term_raw (id, ct) ctxt =
    let
      val t = Thm.term_of ct
      val prev_ids = in_table_raw_ids ctxt t
      val ids_t = (id :: prev_ids)
                      |> Util.max_partial (BoxID.is_eq_ancestor ctxt)
    in
      ctxt |> Data.map (map_terms (Termtab.update (t, (ids_t, ct))))
    end

(* Return list of all terms (at any ids) present in table. *)
fun get_all_terms ctxt =
    let
      val {terms, ...} = Data.get ctxt
    in
      map (fn (_, (_, ct)) => ct) (Termtab.dest terms)
    end

(* Return list of all terms with ids present in table. *)
fun get_all_id_terms ctxt =
    let
      val {terms, ...} = Data.get ctxt
    in
      maps (fn (_, (ids, ct)) => map (rpair ct) ids)
           (Termtab.dest terms)
    end

(*** Basic manipulation of equiv table. ***)

fun has_equiv_eq_better ctxt infos info' =
    exists (fn info => equiv_eq_better ctxt info info') infos

(* Add one way equivalence edge. Maintain the non-comparable property
   of the set of equivalence edges between any two nodes. cur_info is
   of form (id, t == t').
 *)
fun add_equiv_raw (cur_info as (_, th)) ctxt =
    let
      val {equiv, ...} = Data.get ctxt
      val t = Util.lhs_of th
      val equiv_t = the_default [] (Termtab.lookup equiv t)
    in
      if exists (fn info => equiv_eq_better ctxt info cur_info) equiv_t then ctxt
      else ctxt |> Data.map (map_equiv (
          Termtab.update (
            t, equiv_t |> filter_out (equiv_eq_better ctxt cur_info)
                       |> cons cur_info)))
    end

(* Add the given equivalence edge. *)
fun add_equiv (id, th) ctxt =
    let
      val _ = assert (not (Util.lhs_of th aconv Util.rhs_of th)) "add_equiv: t == t'"
    in
      ctxt |> add_equiv_raw (id, th)
           |> add_equiv_raw (id, meta_sym th)
    end

(* Get all edges coming from t in the equiv graph. *)
fun equiv_neighs ctxt t =
    let
      val {equiv, ...} = Data.get ctxt
    in
      case Termtab.lookup equiv t of
          NONE => []
        | SOME infos => infos
    end

fun get_all_equiv ctxt t =
    let
      val {all_equiv, ...} = Data.get ctxt
    in
      the (Termtab.lookup all_equiv t)
      handle Option.Option => raise Fail "all_equiv: not found"
    end

(*** Basic manipulation of simp table. ***)

(* Update rewrite of t under id to th: t == t'. Similar to
   add_equiv_raw.
 *)
fun update_simp (id, th) ctxt =
    let
      val {simp, ...} = Data.get ctxt
      val ct = Thm.lhs_of th
      val t = Thm.term_of ct
      val simp_t = the_default [([], Thm.reflexive ct)] (Termtab.lookup simp t)
    in
      if exists (fn info => simp_eq_better ctxt info (id, th)) simp_t then ctxt
      else
        ctxt |> Data.map (map_simp (
          Termtab.update (
            t, simp_t |> filter_out (simp_eq_better ctxt (id, th))
                      |> cons (id, th))))
    end

(* Get the entire rewrite info of t as stored directly in
   table. Return as a list of (id, th) pairs.
 *)
fun get_rewrite_info ctxt ct =
    let
      val {simp, ...} = Data.get ctxt
    in
      case Termtab.lookup simp (Thm.term_of ct) of
          NONE => [([], Thm.reflexive ct)]
        | SOME infos => infos
    end

(* Return the rewrite of t under a given id, as stored directly in
   table. Return t == t if not in table.
 *)
fun get_rewrite id ctxt ct =
    case get_rewrite_info ctxt ct of
        [] => Thm.reflexive ct
      | ths' => ths' |> filter (BoxID.is_eq_descendent ctxt id o fst)
                     |> map snd
                     |> Util.max (rev_order o simp_ord)

(*** Basic manipulation of subsimp and rep tables. ***)

(* Given list of lists of simplifying infos indexed by term and then
   id, return simplifying infos indexed first by id and then term.
 *)
fun merge_simp_infos ctxt lsts =
    let
      val ids = map (map fst) lsts |> BoxID.get_all_merges ctxt
      fun get_for_id_lst id lst =
          lst |> filter (BoxID.is_eq_descendent ctxt id o fst)
              |> map snd |> Util.max (rev_order o simp_ord)
      fun get_for_id id = (id, map (get_for_id_lst id) lsts)
    in
      map get_for_id ids
    end

(* Get entire subterm rewrite info of t. Return as a list of (id,
   rewrite) pairs.
 *)
fun get_subterm_rewrite_info ctxt ct =
    let
      val (cf, subs) = Drule.strip_comb ct
    in
      if null subs then [([], Thm.reflexive ct)] else
      (map (get_rewrite_info ctxt) subs)
          |> merge_simp_infos ctxt
          |> map (fn (id, equivs) => (id, Util.comb_equiv (cf, equivs)))
          |> Util.max_partial (simp_eq_better ctxt)
    end

(* Given a head rep (id, th) (where th is reverse of a subterm
   rewrite), remove th from the reps table.
 *)
fun remove_rep (id, th) ctxt =
    let
      val {reps, ...} = Data.get ctxt
      val t = Util.lhs_of th
      val reps_t = the_default [] (Termtab.lookup reps t)
      val _ = assert (member eq_info reps_t (id, th)) "remove_rep: not found"
    in
      ctxt |> Data.map (map_reps (Termtab.map_entry t (remove eq_info (id, th))))
    end

(* Update subterm rewrite of t under id to th: t == t'. Also update
   the reps table (reverse of subsimp table).
 *)
fun update_subsimp (id, th) ctxt =
    let
      val {subsimp, ...} = Data.get ctxt
      val (t, t') = (Util.lhs_of th, Util.rhs_of th)
      val subsimp_t = the_default [] (Termtab.lookup subsimp t)
    in
      if exists (fn info => simp_eq_better ctxt info (id, th)) subsimp_t then ctxt
      else
        let
          val th' = meta_sym th
          val (rem, keep) = filter_split (simp_eq_better ctxt (id, th)) subsimp_t
        in
          ctxt |> Data.map (map_subsimp (Termtab.update (t, (id, th) :: keep)))
               |> Data.map (map_reps (Termtab.map_default (t', []) (cons (id, th'))))
               |> fold remove_rep (map (apsnd meta_sym) rem)
        end
    end

(* Returns the list of (id, th) pairs, where th is t == t', such that
   t' subterm rewrites to t at box id.
 *)
fun get_head_rep_info ctxt t =
    let
      val {reps, ...} = Data.get ctxt
    in
      case Termtab.lookup reps t of
          NONE => []
        | SOME infos => infos
    end

(* Assume t is subterm simplified under id. Return SOME (t == v) if v
   is a term in the rewrite table that is subterm rewrites to t, under
   the given id. If there is no such v, return NONE.
 *)
fun get_head_rep id ctxt t =
    get_first (fn (id', t') =>
                  if BoxID.is_eq_ancestor ctxt id' id then SOME t' else NONE)
              (get_head_rep_info ctxt t)

(* Returns head representations of the right side of th under id, or
   under more restrictive assumptions. Merge the equivalence theorems
   with th. Not guaranteed to be non-redundant.
 *)
fun get_head_rep_with_id_th ctxt (id, th) =
    get_head_rep_info ctxt (Util.rhs_of th) |> map (BoxID.merge_eq_infos ctxt (id, th))

(* Using the subsimp table for subterm simplification. *)
fun get_cached_subterm_rewrite_info ctxt t =
    let
      val {subsimp, ...} = Data.get ctxt
    in
      case Termtab.lookup subsimp t of
          NONE => []
        | SOME infos => infos
    end

(* Obtain the subterm simplification of t under id, or a less
   restrictive assumption.
 *)
fun get_cached_subterm_rewrite id ctxt ct =
    case get_cached_subterm_rewrite_info ctxt (Thm.term_of ct) of
        [] => Thm.reflexive ct
      | ths' => ths' |> filter (BoxID.is_eq_descendent ctxt id o fst)
                     |> map snd
                     |> Util.max (rev_order o simp_ord)

(*** Simplification of terms not indexed in table. ***)

(* Assume t is subterm simplified under id. *)
fun head_simplify id ctxt ct =
    case get_head_rep id ctxt (Thm.term_of ct) of
        NONE => Thm.reflexive ct
      | SOME th => Util.transitive_list [th, get_rewrite id ctxt (Thm.rhs_of th)]

(* First simplify subterms, then simplify head. *)
fun simplify id ctxt ct =
    if in_table_raw ctxt (Thm.term_of ct) then
      get_rewrite id ctxt ct else
    let
      val th = subterm_simplify id ctxt ct
    in
      Util.transitive_list [th, head_simplify id ctxt (Thm.rhs_of th)]
    end

(* Simplify subterms, but not head. *)
and subterm_simplify id ctxt ct =
    if in_table_raw ctxt (Thm.term_of ct) then
      get_cached_subterm_rewrite id ctxt ct else
    let
      val (cf, subs) = Drule.strip_comb ct
      val equivs = map (simplify id ctxt) subs
    in
      Util.comb_equiv (cf, equivs)
    end

(* Convenient function for getting simplified value. *)
fun simp_val id ctxt ct = Thm.rhs_of (simplify id ctxt ct)

fun simp_val_t id ctxt t =
    Util.rhs_of (simplify id ctxt (Thm.cterm_of ctxt t))

(* Get all simplifications and subterm-simplifications. *)
fun simplify_info ctxt ct =
    if in_table_raw ctxt (Thm.term_of ct) then
      get_rewrite_info ctxt ct else
    let
      val subterm_info = subterm_simplify_info ctxt ct
      fun get_rewrite_with_id_th (id', th') =
          (get_rewrite_info ctxt (Thm.rhs_of th'))
              |> map (BoxID.merge_eq_infos ctxt (id', th'))
      val head_info =
          subterm_info |> maps (get_head_rep_with_id_th ctxt)
                       |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
                       |> maps get_rewrite_with_id_th
    in
      subterm_info @ head_info |> Util.max_partial (simp_eq_better ctxt)
    end

(* Note similarity with get_subterm_rewrite_info. *)
and subterm_simplify_info ctxt ct =
    if in_table_raw ctxt (Thm.term_of ct) then
      get_cached_subterm_rewrite_info ctxt (Thm.term_of ct) else
    let
      val (cf, subs) = Drule.strip_comb ct
    in
      if null subs then [([], Thm.reflexive ct)] else
      (map (simplify_info ctxt) subs)
          |> merge_simp_infos ctxt
          |> map (fn (id, equivs) => (id, Util.comb_equiv (cf, equivs)))
          |> Util.max_partial (simp_eq_better ctxt)
    end

(* Exported equivalence function. *)
fun is_equiv id ctxt (ct1, ct2) =
    ct1 aconvc ct2 orelse simp_val id ctxt ct1 aconvc simp_val id ctxt ct2

fun is_equiv_t id ctxt (t1, t2) =
    t1 aconv t2 orelse is_equiv id ctxt (Thm.cterm_of ctxt t1, Thm.cterm_of ctxt t2)

(* No assumption on u. Get list of (id', u') pairs where id <= id', u'
   is in the table equivalent to u under id', and the head of u' is
   the same as that for t. If (id1, u1) and (id2, u2) are such that
   id2 implies id1 and all arguments of u1, u2 are equivalent under
   t2, then (id2, u2) is not included in the results. This
   function is much faster when u is in table (uses get_all_equiv
   directly).
 *)
fun get_head_equiv ctxt cu =
    let
      val u = Thm.term_of cu
      val _ = assert (not (Term.is_open u)) "get_all_head_equivs: u is open"

      fun rep_eq_better (id1, th1) (id2, th2) =
          BoxID.is_eq_ancestor ctxt id1 id2 andalso
          is_equiv id2 ctxt (Thm.rhs_of th1, Thm.rhs_of th2)

      fun get_all_equiv_under_id (id', th') =
          (get_all_equiv ctxt (Util.rhs_of th'))
              |> map (BoxID.merge_eq_infos ctxt (id', th'))
    in
      if in_table_raw ctxt u then
        (* Get all equivs from table. *)
        get_all_equiv ctxt u
      else
        cu |> subterm_simplify_info ctxt
           |> maps (get_head_rep_with_id_th ctxt)
           |> Util.max_partial rep_eq_better
           |> maps get_all_equiv_under_id
           |> cons ([], Thm.reflexive cu)
           |> Util.max_partial (equiv_eq_better ctxt)
    end

(* Get list of head equivs for cu, whose head agrees (or matches) with t. *)
fun get_head_equiv_with_t ctxt (id, cu) t =
    let
      fun is_valid (_, th) =
          if Term.is_Var t then true
          else if Term.is_Var (Term.head_of t) then true
          else Term.aconv_untyped (Term.head_of (Util.rhs_of th), Term.head_of t)
    in
      (get_head_equiv ctxt cu)
          |> filter is_valid
          |> BoxID.merge_box_with_info ctxt id
    end

(*** Adding rewrite rules and maintain invariants of the table. ***)

(* Work out all consequences of updating simps in the rewrite
   table. This includes updating simp of neighboring nodes, and
   updating simps / subsimps of nodes for which the current node is a
   subterm. inits is a list of simps to be added, where each element
   is of the form (id, t == t') updating simp of t. In this function
   we maintain a list of simplifications (to_process) that have been
   added to the table, but whose consequences (on neighboring terms
   and containing terms) need to be processed.
 *)
fun process_update_simp inits ctxt =
    let
      fun eq_update ((id, th), (id', th')) =
          (id = id' andalso Thm.prop_of th aconv Thm.prop_of th')

      (* Add the simp (id, th) for the left side of th to the
         table. If (id, th) is not redundant, add (id, th) to the list
         of simps whose consequences need to be processed.
       *)
      fun process_simp (id, th) (to_process, ctxt) =
          if simp_ord (th, get_rewrite id ctxt (Thm.lhs_of th)) = LESS then
            (insert eq_update (id, th) to_process, update_simp (id, th) ctxt)
          else
            (to_process, ctxt)

      (* Recompute subterm simplifications of t. Update the subsimp
         table as well as the simp table (in the latter case possibly
         adding to the to_process list.
       *)
      fun process_term ct (to_process, ctxt) =
          let
            val subsimps = get_subterm_rewrite_info ctxt ct
            val ctxt' = fold update_subsimp subsimps ctxt
          in
            fold process_simp subsimps (to_process, ctxt')
          end

      (* Pull the first item of to_process and work out its
         consequences.
       *)
      fun update_step (to_process, ctxt) =
          case to_process of
              [] => ([], ctxt)
            | (id, th) :: rest =>
              let
                val t = Util.lhs_of th
                (* th: t == simp_t, th': t = t', result: t' = simp_t. *)
                fun process_neigh (id', th') =
                    BoxID.merge_eq_infos ctxt (id', meta_sym th') (id, th)
                val new_simp = map process_neigh (equiv_neighs ctxt t)
              in
                (rest, ctxt) |> fold process_simp new_simp
                             |> fold process_term (immediate_contains ctxt t)
                             |> update_step
              end
    in
      ([], ctxt) |> fold process_simp inits |> update_step |> snd
    end

(* Return list of ids that are descendents of id at which t1 and t2
   are equiv.
 *)
fun equiv_info ctxt id (ct1, ct2) =
    let
      val simp1 = simplify_info ctxt ct1
      val simp2 = simplify_info ctxt ct2
      fun compare (id1, th1) (id2, th2) =
          if Util.rhs_of th1 aconv Util.rhs_of th2 then
            [(BoxID.merge_boxes ctxt (id1, id2), Util.transitive_list [th1, meta_sym th2])]
          else []
    in
      (maps (fn s1 => maps (compare s1) simp2) simp1)
          |> BoxID.merge_box_with_info ctxt id
          |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
    end

fun equiv_info_t ctxt id (t1, t2) =
    equiv_info ctxt id (Thm.cterm_of ctxt t1, Thm.cterm_of ctxt t2)

(* Return list of ids that are descendents of id at which t1 and t2
   are subterm equiv.
 *)
fun subequiv_info ctxt id (ct1, ct2) =
    if not ((Term.head_of (Thm.term_of ct1))
                aconv Term.head_of (Thm.term_of ct2)) then []
    else let
      val simp1 = subterm_simplify_info ctxt ct1
      val simp2 = subterm_simplify_info ctxt ct2
      fun compare (id1, th1) (id2, th2) =
          if Util.rhs_of th1 aconv Util.rhs_of th2 then
            [(BoxID.merge_boxes ctxt (id1, id2),
              Util.transitive_list [th1, meta_sym th2])]
          else []
    in
      (maps (fn s1 => maps (compare s1) simp2) simp1)
          |> BoxID.merge_box_with_info ctxt id
          |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
    end

(* Get list of terms reachable from the terms ts. If trav_contains =
   false, only travel along equiv edges. Otherwise also travel from t
   to any term containing t.
 *)
fun get_reachable_terms trav_contains ctxt ts =
    let
      fun helper (new, all) =
          case new of
              [] => ([], all)
            | t :: rest =>
              let
                val contains =
                    if trav_contains then
                      map Thm.term_of (immediate_contains ctxt t)
                    else []
                val neighs = (equiv_neighs ctxt t)
                                 |> map (fn (_, th) => Util.rhs_of th)
                val new' = (contains @ neighs)
                               |> distinct (op aconv)
                               |> subtract (op aconv) all
                val all' = new' @ all
              in
                helper (rest @ new', all')
              end
    in
      snd (helper (ts, ts))
    end

fun add_all_equiv_raw (cur_info as (_, th)) ctxt =
    let
      val {all_equiv, ...} = Data.get ctxt
      val t = Util.lhs_of th
      val equiv_t = the_default [] (Termtab.lookup all_equiv t)
    in
      if exists (fn info => equiv_eq_better ctxt info cur_info) equiv_t then ctxt
      else ctxt |> Data.map (map_all_equiv (
          Termtab.update (
            t, equiv_t |> filter_out (equiv_eq_better ctxt cur_info)
                       |> cons cur_info)))
    end

fun update_all_equiv id th ctxt =
    let
      val (ct1, ct2) = (Thm.lhs_of th, Thm.rhs_of th)
      val t1_equiv = get_all_equiv ctxt (Thm.term_of ct1)
      val t2_equiv = get_all_equiv ctxt (Thm.term_of ct2)

      (* eq1 is t1 == t1', eq2 is t2 == t2', add t1' == t2' and t2' ==
         t1' to all_equiv.
       *)
      fun process_pair ((id1, eq1), (id2, eq2)) ctxt =
          let
            val id' = BoxID.merge_boxes
                          ctxt (id, BoxID.merge_boxes ctxt (id1, id2))
            val eq = Util.transitive_list [meta_sym eq1, th, eq2]
          in
            ctxt |> add_all_equiv_raw (id', eq)
                 |> add_all_equiv_raw (id', meta_sym eq)
          end
    in
      fold process_pair (Util.all_pairs (t1_equiv, t2_equiv)) ctxt
    end

(* Assume t1 and t2 are already in table. Add equiv edge th: t1 == t2 and
   work out all the consequences.
 *)
fun add_rewrite_raw id th ctxt =
    let
      val (ct1, ct2) = (Thm.lhs_of th, Thm.rhs_of th)

      (* New simplifications. *)
      val t1_rinfo = get_rewrite_info ctxt ct1
      val t2_rinfo = get_rewrite_info ctxt ct2
      val t1_news = t2_rinfo |> map (BoxID.merge_eq_infos ctxt (id, th))
      val t2_news = t1_rinfo |> map (BoxID.merge_eq_infos ctxt (id, meta_sym th))
    in
      ctxt |> add_equiv (id, th)
           |> process_update_simp (t1_news @ t2_news)
           |> update_all_equiv id th
    end

(* Add equiv edges so the rewrite table is consistent. That is, any two nodes that
   have the same simp should be connected in the equiv graph. Also
   return the list of equiv edges added.
 *)
fun complete_table ctxt =
    let
      fun find_new_equiv ct =
          let
            val equivs = get_all_equiv ctxt (Thm.term_of ct)
          in
            (get_subterm_rewrite_info ctxt ct)
                |> maps (get_head_rep_with_id_th ctxt)
                |> Util.max_partial (equiv_eq_better ctxt)
                |> filter_out (has_equiv_eq_better ctxt equivs)
          end
      val new_equivs = (maps find_new_equiv (get_all_terms ctxt))
                           |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
    in
      case new_equivs of
          [] => ([], ctxt)
        | (id, th) :: _ =>
          (* Add bi-directional edges for terms with the same subterm
             simplification. Keep track of list of edges added.
           *)
          let
            val ctxt' = ctxt |> add_rewrite_raw id th
            val (edges, ctxt'') = complete_table ctxt'
          in
            ((id, th) :: edges, ctxt'')
          end
    end

(* Add term t to rewrite table at box id. The primed version (used in
   add_rewrite_thm) add t and all its subterms to the table. The
   unprimed version also add new equiv edges if necessary, resulting
   is a consistent rewrite table.
 *)
fun add_term' (id, ct) ctxt =
    if in_table_raw_for_id ctxt (id, Thm.term_of ct) then ctxt
    else let
      (* First add subterms. *)
      val t = Thm.term_of ct
      val imm_subterms = UtilLogic.list_subterms t
      val id_subs = map (fn t => (id, Thm.cterm_of ctxt t)) imm_subterms
      val ctxt' = ctxt |> fold add_term' id_subs |> add_term_raw (id, ct)
    in
      (* If t is already in table (just not at id), then we are
         done. Otherwise compute all indexed info for t.
       *)
      if in_table_raw ctxt t then ctxt'
      else let
        (* Compute simplification and properties of t. Note we are
           doing this in box [] (not id), so it does not need to be
           recomputed if a term is added to a more general box.
         *)
        val simps = get_subterm_rewrite_info ctxt' ct
      in
        ctxt' |> fold (add_contain ct) imm_subterms
              |> fold update_simp simps
              |> fold update_subsimp simps
              |> add_all_equiv_raw ([], Thm.reflexive ct)
      end
    end

fun add_term (id, ct) ctxt =
    if in_table_raw_for_id ctxt (id, Thm.term_of ct) then ([], ctxt)
    else ctxt |> add_term' (id, ct) |> complete_table

fun add_term_list term_infos ctxt =
    case term_infos of
        [] => ([], ctxt)
      | (id, ct) :: rest =>
        let
          val (edges, ctxt') = add_term (id, ct) ctxt
          val (edges', ctxt'') = add_term_list rest ctxt'
        in
          (edges @ edges', ctxt'')
        end

(* First make sure t1 and t2 are in table. Add t1 == t2 to the table,
   and work out any consequences. The result is a consistent rewrite
   table.
 *)
fun add_rewrite (id, eq_th) ctxt =
    let
      (* eq_th is meta-equality when between lambda terms. *)
      val meta_eq = if Util.is_meta_eq (Thm.prop_of eq_th) then eq_th
                    else to_meta_eq eq_th
      val (ct1, ct2) = meta_eq |> Thm.cprop_of |> Thm.dest_equals
    in
      if is_equiv id ctxt (ct1, ct2) then ([], ctxt)
      else
        ctxt |> add_term' (id, ct1) |> add_term' (id, ct2)
             |> add_rewrite_raw id meta_eq
             |> complete_table
             |> apfst (cons (id, meta_eq))
    end

(* Returns the list of terms in ctxt' that is not in ctxt. *)
fun get_new_terms (ctxt, ctxt') =
    let
      fun get_for_term ct =
          (in_table_raw_ids ctxt' (Thm.term_of ct))
              |> filter_out (fn id => in_table_raw_for_id ctxt (id, Thm.term_of ct))
              |> map (rpair ct)
    in
      maps get_for_term (get_all_terms ctxt')
    end

end  (* structure RewriteTable. *)
