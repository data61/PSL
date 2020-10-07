(*
  File: auto2_data.ML
  Author: Bohua Zhan

  Updating of all data maintained at proof time.
*)

signature AUTO2_DATA =
sig
  val relevant_terms_single: box_item -> term list
  val add_terms:
      box_item list -> (box_id * cterm) list -> Proof.context -> Proof.context
  val get_incr_type:
      box_item list -> box_item list -> Proof.context -> Proof.context
  val get_single_type: Proof.context -> Proof.context
end;

structure Auto2Data : AUTO2_DATA =
struct

(* Procedure to add a new term. Here old_items is the list of existing
   items. term_infos is a list of (id, ct) pairs.
 *)
fun add_terms old_items term_infos ctxt =
    let
      val ts = map (Thm.term_of o snd) term_infos
      val (edges, ctxt') = RewriteTable.add_term_list term_infos ctxt
      val new_ts = map (Thm.term_of o snd)
                       (RewriteTable.get_new_terms (ctxt, ctxt'))
      val imm_properties =
          maps (PropertyData.apply_property_update_on_term ctxt' []) ts
    in
      ctxt' |> PropertyData.process_update_property imm_properties
            |> fold PropertyData.process_rewrite_property edges
            |> fold WellformData.initialize_wellform_data ts
            |> WellformData.complete_wellform_data_for_terms old_items new_ts
    end

(* Helper function for the two functions below. *)
fun relevant_terms_single item =
    let
      val {ty_str, tname, ...} = item
    in
      if ty_str = "EQ" then map Thm.term_of tname else []
    end

(* Use the given items to update the current context data, producing
   the incremental context. Here old_items is the list of existing
   items. items is the list of new items. Update the rewrite table,
   property table, wellform table, and the custom tables.
 *)
fun get_incr_type old_items items ctxt =
    let
      (* List of relevant terms. *)
      val relevant_terms =
          items |> maps relevant_terms_single
                |> RewriteTable.get_reachable_terms true ctxt

      fun add_one_info item ctxt =
          let
            val {id, ty_str, prop, ...} = item
          in
            if ty_str = "EQ" then
              let
                val (edges, ctxt') = RewriteTable.add_rewrite (id, prop) ctxt
              in
                ctxt' |> fold PropertyData.process_rewrite_property edges
              end
            else if ty_str = "PROPERTY" then
              PropertyData.add_property (id, prop) ctxt
            else ctxt
          end

      val match_items =
          items @
          filter (fn {tname, ...} => exists (Util.has_subterm relevant_terms)
                                            (map Thm.term_of tname)) old_items
    in
      ctxt |> fold add_one_info items
           |> WellformData.complete_wellform_data match_items
    end

fun get_single_type ctxt =
    ctxt |> RewriteTable.clear_incr
         |> PropertyData.clear_incr
         |> WellformData.clear_incr

end  (* Auto2Data *)
