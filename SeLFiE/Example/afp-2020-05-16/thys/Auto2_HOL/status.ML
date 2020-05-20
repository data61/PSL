(*
  File: status.ML
  Author: Bohua Zhan

  Definition of updates and proof status.
*)

datatype raw_update
  = AddItems of {id: box_id, sc: int option, raw_items: raw_item list}
  | AddBoxes of {id: box_id, sc: int option, init_assum: term}
  | ResolveBox of {id: box_id, th: thm}
  | ShadowItem of {id: box_id, item: box_item}
type update = {sc: int, prfstep_name: string, source: box_item list,
               raw_updt: raw_update}

signature UPDATE =
sig
  val target_of_update: raw_update -> box_id
  val replace_id_of_update: raw_update -> raw_update
  val string_of_raw_update: Proof.context -> raw_update -> string
  val thm_to_ritem: thm -> raw_item
  val thm_update: box_id * thm -> raw_update
  val thm_update_sc: int -> box_id * thm -> raw_update

  val apply_exists_ritems: Proof.context -> thm -> raw_item list * thm
  val update_info: Proof.context -> box_id -> raw_item list -> string
  val source_info: update -> string
end;

structure Update : UPDATE =
struct

fun target_of_update raw_updt =
    case raw_updt of
        AddItems {id, ...} => id
      | AddBoxes {id, ...} => id
      | ResolveBox {id, ...} => id
      | ShadowItem {id, ...} => id

fun replace_id_of_update raw_updt =
    let
      val id = target_of_update raw_updt
      val _ = assert (BoxID.has_incr_id id) "replace_id_of_update"
      val id' = BoxID.replace_incr_id id
    in
      case raw_updt of
          AddItems {sc, raw_items, ...} =>
          AddItems {id = id', sc = sc, raw_items = raw_items}
        | AddBoxes {sc, init_assum, ...} =>
          AddBoxes {id = id', sc = sc, init_assum = init_assum}
        | ResolveBox {th, ...} => ResolveBox {id = id', th = th}
        | ShadowItem {item, ...} => ShadowItem {id = id', item = item}
    end

(* Debugging output for raw update. *)
fun string_of_raw_update ctxt raw_updt =
    case raw_updt of
        AddItems {id, raw_items, ...} =>
        "Add items " ^ (Util.string_of_list (
                           ItemIO.string_of_raw_item ctxt) raw_items) ^
        " to box " ^ (BoxID.string_of_box_id id)
      | AddBoxes {id, init_assum, ...} =>
        "Add box " ^ (Syntax.string_of_term ctxt init_assum) ^
        " under box " ^ (BoxID.string_of_box_id id)
      | ResolveBox {id, ...} =>
        "Resolve box " ^ (BoxID.string_of_box_id id)
      | ShadowItem {id, item} =>
        "Shadow item " ^ (ItemIO.string_of_item ctxt item) ^
        " in box " ^ (BoxID.string_of_box_id id)

(* Create raw_item from theorem. *)
fun thm_to_ritem th =
    let
      val prop = Thm.prop_of th
      val _ = assert (is_Trueprop prop) "thm_update: prop is not Trueprop."
      val _ = assert (not (Util.has_vars prop))
                     "thm_to_ritem: prop contains schematic variables."
    in
      Fact (TY_PROP, [dest_Trueprop prop], th)
    end

(* Create raw_update from id and theorem. *)
fun thm_update (id, th) =
    if Thm.prop_of th aconv pFalse then
      ResolveBox {id = id, th = th}
    else
      AddItems {id = id, sc = NONE, raw_items = [thm_to_ritem th]}

fun thm_update_sc sc (id, th) =
    if Thm.prop_of th aconv pFalse then
      ResolveBox {id = id, th = th}
    else
      AddItems {id = id, sc = SOME sc, raw_items = [thm_to_ritem th]}

(* Apply the given existence theorem. Return a pair (ritems, th),
   ritems contain the new variables and the new handler, and th is the
   instantiated property of the new variables, which can either be
   processed further, or made into an ritem using thm_update.
 *)
fun apply_exists_ritems ctxt ex_th =
    let
      val (vars, body) = (UtilLogic.strip_exists (prop_of' ex_th))
                             |> Util.to_internal_vars ctxt
                             |> apsnd mk_Trueprop
    in
      if null vars then ([], ex_th)
      else (map (BoxItem.var_to_fact) vars @ [Handler (vars, body, ex_th)],
            Thm.assume (Thm.cterm_of ctxt body))
    end

(* Print a list of raw items. *)
fun update_info ctxt id ritems =
    (Util.string_of_list' (ItemIO.string_of_raw_item ctxt)
                     (filter (not o BoxItem.is_handler_raw) ritems)) ^
    " at box " ^ (BoxID.string_of_box_id id)

(* Print the source of the update. *)
fun source_info {prfstep_name, source, ...} =
    prfstep_name ^ " on " ^
    (Util.string_of_list'
         (fn {uid, ...} => "(" ^ string_of_int uid ^ ")") source)

end  (* structure Update. *)

structure Updates_Heap =
Heap (
  type elem = update
  fun ord ({sc = sc1, ...}, {sc = sc2, ...}) = int_ord (sc1, sc2)
)

type status = {
  assums: term list,
  handlers: (box_id * (term list * term * thm)) list,
  items: (box_item * box_id list) Inttab.table,
  queue: Updates_Heap.T,
  resolve_th: thm option,
  ctxt: Proof.context
}

signature STATUS =
sig
  val empty_status: Proof.context -> status

  val map_context: (Proof.context -> Proof.context) -> status -> status
  val add_handler: box_id * (term list * term * thm) -> status -> status
  val get_handlers: status -> (box_id * (term list * term * thm)) list
  val add_item: box_item -> status -> status
  val get_items: status -> box_item list
  val get_all_items_at_id: status -> box_id -> box_item list
  val get_num_items: status -> int
  val set_resolve_th: thm -> status -> status
  val get_resolve_th: status -> thm
  val add_prim_box: box_id -> term -> status -> int * status
  val add_resolved: box_id -> status -> status
  val get_init_assums: status -> box_id -> term list
  val get_init_assum: status -> int -> term

  val lookup_item: status -> int -> (box_item * box_id list) option
  val clear_incr: status -> status
  val add_shadowed: box_id * box_item -> status -> status
  val query_shadowed: status -> box_id -> box_item -> bool
  val query_removed: status -> box_item -> bool

  val find_fact: status -> box_id -> term -> thm option
  val find_ritem_exact: status -> box_id -> raw_item -> bool
  val invoke_handler: Proof.context -> term list * term * thm -> thm -> thm
  val get_on_resolve: status -> box_id -> int -> thm -> thm
  val find_prim_box: status -> box_id -> term -> int option

  val map_queue: (Updates_Heap.T -> Updates_Heap.T) -> status -> status
  val add_to_queue: update -> status -> status
  val delmin_from_queue: status -> status
end;

structure Status : STATUS =
struct

fun empty_status ctxt =
    {assums = [UtilLogic.term_of_bool true],
     handlers = [],
     items = Inttab.empty,
     queue = Updates_Heap.empty,
     ctxt = ctxt,
     resolve_th = NONE}

fun map_context f {assums, handlers, items, queue, ctxt, resolve_th} =
    {assums = assums, handlers = handlers, items = items, queue = queue,
     ctxt = f ctxt, resolve_th = resolve_th}

fun add_handler (id, handler) {assums, handlers, items, queue, ctxt,
                               resolve_th} =
    {assums = assums, handlers = (id, handler) :: handlers, items = items,
     queue = queue, ctxt = ctxt, resolve_th = resolve_th}

fun get_handlers {handlers, ...} = handlers

fun map_items f {assums, handlers, items, queue, ctxt, resolve_th} =
    {assums = assums, handlers = handlers, items = f items, queue = queue,
     ctxt = ctxt, resolve_th = resolve_th}

fun add_item (item as {uid, ...}) st =
    st |> map_items (Inttab.update_new (uid, (item, [])))

fun get_items {items, ...} =
    items |> Inttab.dest |> map snd
          |> filter_out (fn ({id, ...}, shadow_ids) =>
                            member (op =) shadow_ids id)
          |> map fst

fun get_items_at_id (st as {ctxt, ...}) id =
    st |> get_items
       |> filter (fn {id = id', ...} => BoxID.is_eq_ancestor ctxt id' id)

fun get_all_items_at_id {items, ctxt, ...} id =
    items |> Inttab.dest |> map snd |> map fst
          |> filter (fn {id = id', ...} => BoxID.is_eq_ancestor ctxt id' id)

fun get_num_items {items, ...} = length (Inttab.dest items)

fun set_resolve_th th {assums, handlers, items, queue, ctxt, ...} =
    {assums = assums, handlers = handlers, items = items, queue = queue,
     ctxt = ctxt, resolve_th = SOME th}

fun get_resolve_th {resolve_th, ...} =
    case resolve_th of
        NONE => raise Fail "get_resolve_th: not resolved."
      | SOME th => th

fun add_prim_box parent_id assum
                 {assums, handlers, items, queue, ctxt, resolve_th} =
    let
      val (id, ctxt') = BoxID.add_prim_id parent_id ctxt
    in
      (id, {assums = assums @ [assum],
            handlers = handlers, items = items, queue = queue,
            ctxt = ctxt', resolve_th = resolve_th})
    end

fun add_resolved id {assums, handlers, items, queue, ctxt, resolve_th} =
    let
      val ctxt' = BoxID.add_resolved id ctxt
    in
      {assums = assums, handlers = handlers, items = items, queue = queue,
       ctxt = ctxt' |> RewriteTable.clean_resolved id
                    |> PropertyData.clean_resolved id
                    |> WellformData.clean_resolved id,
       resolve_th = resolve_th}
    end

fun get_init_assums {assums, ctxt, ...} id =
    let
      val parents = BoxID.get_ancestors_prim ctxt id
    in
      map (nth assums) parents
    end

fun get_init_assum {assums, ...} prim_id =
    nth assums prim_id

fun lookup_item {items, ...} uid =
    Inttab.lookup items uid

fun clear_incr st =
    st |> map_items (
      Inttab.map (fn _ => fn (item, ids) => (BoxItem.item_replace_incr item, ids)))

fun add_shadowed (shadow_id, {uid, ...}) (st as {ctxt, ...}) =
    case lookup_item st uid of
        NONE => raise Fail "add_shadowed: item not found."
      | SOME (item, shadow_ids) =>
        let
          val shadow_ids' = (shadow_id :: shadow_ids)
                                |> Util.max_partial (BoxID.is_eq_ancestor ctxt)
        in
          st |> map_items (Inttab.update (uid, (item, shadow_ids')))
        end

fun query_shadowed (st as {ctxt, ...}) shadow_id {uid, ...} =
    case lookup_item st uid of
        NONE => raise Fail "query_shadowed: item not found."
      | SOME (_, shadow_ids) =>
        exists (BoxID.is_eq_descendent ctxt shadow_id) shadow_ids

fun query_removed st (item as {id, ...}) = query_shadowed st id item

(* Try to find fact at id or above with the proposition t. Return SOME
   th if found.
 *)
fun find_fact (st as {ctxt, ...}) id t =
    let
      val ct = Thm.cterm_of ctxt t
      val items = get_items_at_id st id
      val res = (WellformData.find_fact ctxt items (id, ct))
                    |> filter (fn (id', _) => id' = id)
    in
      case res of
          [] => NONE
        | (_, th) :: _ => SOME th
    end

(* Find item with the exact ty_str and tname, whose id is an
   eq-ancestor of the given id.

   There are two special cases: if the ritem in question is of type EQ
   and PROPERTY, in which case we try to find it in the rewrite table.
 *)
fun find_ritem_exact (st as {ctxt, ...}) id ritem =
    case ritem of
        Handler _ => false
      | Fact (ty_str, tname, _) =>
        if ty_str = TY_EQ then
          let
            val (lhs, rhs) = the_pair (BoxItem.get_tname_raw ritem)
          in
            RewriteTable.is_equiv_t id ctxt (lhs, rhs)
          end
        else if ty_str = TY_PROPERTY then
          let
            val prop = the_single tname
            val infos =
                (PropertyData.get_property_t ctxt (id, prop))
                    |> filter (fn (id', _) => BoxID.is_eq_ancestor ctxt id' id)
          in
            not (null infos)
          end
        else
          let
            val thy = Proof_Context.theory_of ctxt
            val {shadow_fn, ...} = ItemIO.get_io_info thy ty_str

            fun eq_item {ty_str = ty_str2, tname = tname2, ...} =
                if ty_str <> ty_str2 then false else
                case shadow_fn of
                    NONE => eq_list (op aconv) (tname, map Thm.term_of tname2)
                  | SOME f => f ctxt id (tname, tname2)
          in
            exists eq_item (get_all_items_at_id st id)
          end

(* Invoke a single handler (vars, t, ex_th) on the theorem th. *)
fun invoke_handler ctxt (vars, t, ex_th) th =
    if member (op aconv) (Thm.hyps_of th) t then
      th |> Thm.implies_intr (Thm.cterm_of ctxt t)
         |> fold (UtilLogic.ex_elim ctxt) (rev vars)
         |> Thm.elim_implies ex_th
    else th

(* Derive the consequence if box id is resolved, to the parent id
   formed by getting parent at index i.
 *)
fun get_on_resolve (st as {ctxt, ...}) id i th =
    let
      (* First get list of handlers to invoke. *)
      val prim_id = nth id i
      val handlers =
          st |> get_handlers
             |> filter (fn (id', _) =>
                           BoxID.is_eq_ancestor ctxt [prim_id] id' andalso
                           BoxID.is_eq_descendent ctxt id id')
             |> map snd
      val init_assum = get_init_assum st prim_id
      val th' = th |> fold (invoke_handler ctxt) handlers
                   |> Thm.implies_intr (Thm.cterm_of ctxt init_assum)
                   |> apply_to_thm UtilLogic.rewrite_from_contra_form
      val _ = assert (prim_id <> BoxID.home_id orelse null (Thm.hyps_of th'))
                     "get_on_resolve: did not remove all hypothesis at box 0."
    in
      th'
    end

(* Find a primitive box (if there is any) whose initial facts agree
   exactly with the given initial facts. Note we cannot yet handle new
   variables.
 *)
fun find_prim_box {assums, ctxt, ...} id init_assum =
    let
      fun agree_at_id prim_id' =
          let
            val parent = BoxID.get_parent_prim ctxt prim_id'
            val is_equiv_t = RewriteTable.is_equiv_t parent ctxt
          in
            is_equiv_t (init_assum, nth assums prim_id')
          end

      fun can_test_id prim_id' =
          BoxID.is_eq_ancestor ctxt (BoxID.get_parent_prim ctxt prim_id') id

      val ids_to_test = filter can_test_id (0 upto (length assums - 1))
    in
      find_first agree_at_id ids_to_test
    end

fun map_queue f {assums, handlers, items, queue, ctxt, resolve_th} =
    {assums = assums, handlers = handlers, items = items, queue = f queue,
     ctxt = ctxt, resolve_th = resolve_th}

fun add_to_queue updt = map_queue (Updates_Heap.insert updt)
val delmin_from_queue = map_queue Updates_Heap.delete_min

end  (* structure Status *)

val _ = Theory.setup (ItemIO.add_basic_item_io)
