(*
  File: box_id.ML
  Author: Bohua Zhan

  Definition and functions on box_id. Box ID is used for keeping track of case
  analysis. Each primitive ID, encoded by integers starting at 1, represents a
  new case. A box ID in general consists of a list of primitive IDs. The
  primitive ID 0 is reserved as a flag for incremental matching.
*)

signature BOXID =
sig
  type box_id
  val string_of_box_id: box_id -> string

  type box_lattice
  val home_id: int
  val has_incr_id: box_id -> bool
  val add_incr_id: box_id -> box_id
  val replace_incr_id: box_id -> box_id

  val get_parent_prim: Proof.context -> int -> box_id
  val get_ancestors_prim: Proof.context -> box_id -> int list
  val reduce_box_id: Proof.context -> int list -> box_id
  val get_parent_at_i: Proof.context -> box_id -> int -> box_id
  val merge_boxes: Proof.context -> box_id * box_id -> box_id
  val get_all_merges: Proof.context -> box_id list list -> box_id list
  val get_all_merges_info:
      Proof.context -> (box_id * 'a) list list -> (box_id * 'a list) list
  val is_eq_ancestor: Proof.context -> box_id -> box_id -> bool
  val is_eq_descendent: Proof.context -> box_id -> box_id -> bool
  val is_box_resolved: Proof.context -> box_id -> bool
  val is_box_unresolved: Proof.context -> box_id -> bool
  val id_is_eq_ancestor: Proof.context -> box_id * 'a -> box_id * 'a -> bool
  val info_eq_better: Proof.context -> box_id * thm -> box_id * thm -> bool
  val merge_box_with_info:
      Proof.context -> box_id -> (box_id * 'a) list -> (box_id * 'a) list
  val merge_eq_infos: Proof.context -> box_id * thm -> box_id * thm -> box_id * thm
  val add_prim_id: box_id -> Proof.context -> int * Proof.context
  val add_resolved: box_id -> Proof.context -> Proof.context
end;

structure BoxID : BOXID =
struct

type box_id = int list

fun string_of_box_id id =
    if length id = 1 then string_of_int (hd id)
    else "(" ^ commas (map string_of_int id) ^ ")"

structure Boxidtab = Table (type key = box_id val ord = list_ord int_ord)

type box_lattice = {
  parents: box_id vector,
  resolved: box_id list
}

(* Initialize with primitive ID zero (used to designate incremental
   matching).
 *)
structure Data = Proof_Data
(
  type T = box_lattice
  fun init _ = {parents = Vector.fromList [[]], resolved = []}
)

val home_id = 1

fun has_incr_id id =
    case id of [] => false | x :: _ => x = 0

fun add_incr_id id =
    if has_incr_id id then raise Fail "add_incr_id"
    else 0 :: id

fun replace_incr_id id =
    if has_incr_id id then tl id else id

fun get_parent_prim ctxt prim_id =
    let
      val {parents, ...} = Data.get ctxt
    in
      Vector.sub (parents, prim_id)
    end
    handle Subscript => raise Fail "get_parent_prim: prim_id out of bounds."

(* Returns the list of primitive ancestors of id. Result may not be in
   order.
 *)
fun get_ancestors_prim ctxt id =
    let
      fun helper all_ids cur_ids =
          let
            val new_ids =
                (maps (get_parent_prim ctxt) cur_ids)
                    |> distinct (op =) |> subtract (op =) all_ids
          in
            if null new_ids then all_ids
            else helper (all_ids @ new_ids) new_ids
          end
    in
      helper id id
    end
    handle Option.Option =>
           raise Fail "get_ancestors_prim: unexpected prim id."

(* For any {a, b} in ids where a is an ancestor of b, remove a from
   ids. Assume input is in order. Output is a valid box_id.
 *)
fun reduce_box_id ctxt prim_lst =
    let
      fun helper taken rest =
          case rest of
              [] => taken
            | cur :: rest' =>
              let val cur_ancestors = get_ancestors_prim ctxt [cur]
              in helper (cur :: subtract (op =) cur_ancestors taken) rest' end
    in
      rev (helper [] prim_lst)
    end

(* Given two ordered lists of integers without duplicates, merge them
   into a sorted list (the merge part of mergesort).
 *)
fun ordered_merge ms ns =
    case (ms, ns) of
        ([], _) => ns
      | (_, []) => ms
      | (m :: ms', n :: ns') =>
        if m < n then m :: ordered_merge ms' ns
        else if n < m then n :: ordered_merge ms ns'
        else m :: ordered_merge ms' ns'

(* Returns box_id of the immediate parent coming from expanding the
   parent of the ith primitive id in the current box_id.
 *)
fun get_parent_at_i ctxt id i =
    reduce_box_id ctxt (ordered_merge (nth_drop i id)
                                      (get_parent_prim ctxt (nth id i)))

(* Merge two generalized boxes. *)
fun merge_boxes ctxt (id1, id2) =
    let
      val merged = ordered_merge id1 id2
      val merged_len = length merged
    in
      if merged_len = length id1 then id1
      else if merged_len = length id2 then id2
      else reduce_box_id ctxt merged
    end

(* Returns list of ids that are all possible intersections of subsets
   of ids.
 *)
fun get_all_merges ctxt id_lsts =
    let
      fun merge2 ids1 ids2 =
          maps (fn id1 => map (fn id2 => merge_boxes ctxt (id1, id2)) ids2) ids1
               |> distinct (op =)
    in
      fold merge2 id_lsts [[]]
    end

(* Given a list a_p, where each a_p is a list of entries b_{pq}, where
   each entry is of the form (id_{pq}, x_{pq}), return all ways of
   choosing one entry b_{pq} from each a_p, combining them by merging
   id_{pq} and putting x_{pq} into a list.
 *)
fun get_all_merges_info ctxt lsts =
    if null lsts then
      raise Fail "get_all_merges_info: lsts is empty."
    else
      let
        fun merge ((id1, x), (id2, xs))
            = (merge_boxes ctxt (id1, id2), x :: xs)

        fun merge2 (lst1, lst2) = map merge (Util.all_pairs (lst1, lst2))
      in
        Library.foldr merge2 (lsts, [([], [])])
      end

(* Returns whether id is an ancestor / descendent of id'. *)
fun is_eq_ancestor ctxt id id' = (id' = merge_boxes ctxt (id, id'))
fun is_eq_descendent ctxt id id' = (id = merge_boxes ctxt (id, id'))

fun is_box_resolved ctxt id =
    let
      val {resolved, ...} = Data.get ctxt
    in
      exists (is_eq_descendent ctxt id) resolved
    end

val is_box_unresolved = not oo is_box_resolved

fun id_is_eq_ancestor ctxt (id, _) (id', _) = is_eq_ancestor ctxt id id'

fun info_eq_better ctxt (id, th) (id', th') =
    Thm.prop_of th aconv Thm.prop_of th' andalso is_eq_ancestor ctxt id id'

fun merge_box_with_info ctxt id =
    map (apfst (fn id' => merge_boxes ctxt (id, id')))

fun merge_eq_infos ctxt (id, th) (id', th') =
    (merge_boxes ctxt (id, id'), Util.transitive_list [th, th'])

fun add_prim_id parent_id ctxt =
    let
      val {parents, resolved} = Data.get ctxt
      val prim_id = Vector.length parents
      val parents' = Vector.concat [parents, Vector.fromList [parent_id]]
    in
      (prim_id, ctxt |> Data.map (K {parents = parents', resolved = resolved}))
    end

fun add_resolved id ctxt =
    let
      val {parents, resolved} = Data.get ctxt
    in
      if exists (is_eq_descendent ctxt id) resolved then ctxt
      else let
        val resolved' = id :: filter_out (is_eq_ancestor ctxt id) resolved
      in
        ctxt |> Data.map (K {parents = parents, resolved = resolved'})
      end
    end

end  (* structure BoxID *)

type box_id = BoxID.box_id
type id_inst = box_id * (Type.tyenv * Envir.tenv)
type id_inst_th = id_inst * thm
type id_inst_ths = id_inst * thm list
structure Boxidtab = Table (type key = BoxID.box_id val ord = list_ord int_ord)
