(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CIMP
imports
  CIMP_pred
  CIMP_lang
  CIMP_vcg
  "HOL-Library.Sublist"
keywords
  "inv_definition" "locset_definition" :: thy_defn
begin

text\<open>

Infrastructure for reasoning about CIMP programs. See AFP entry \<open>ConcurrentGC\<close> for examples
of use.

\<close>

named_theorems com "Command definitions"
named_theorems inv "Location-sensitive invariant definitions"
named_theorems loc "Location set membership cache"

ML\<open>

signature CIMP =
sig
    val com_locs_fold : (term -> 'b -> 'b) -> 'b -> term -> 'b
    val com_locs_map : (term -> 'b) -> term -> 'b list
    val com_locs_fold_no_response : (term -> 'b -> 'b) -> 'b -> term -> 'b
    val com_locs_map_no_response : (term -> 'b) -> term -> 'b list
    val def_inv : thm -> local_theory -> local_theory
    val def_locset : thm -> local_theory -> local_theory
end;

structure Cimp : CIMP =
struct

fun com_locs_fold f x (Const (@{const_name Request}, _) $ l $ _ $ _ )    = f l x
  | com_locs_fold f x (Const (@{const_name Response}, _) $ l $ _)        = f l x
  | com_locs_fold f x (Const (@{const_name LocalOp}, _) $ l $ _)         = f l x
  | com_locs_fold f x (Const (@{const_name Cond1}, _) $ l $ _ $ c)       = com_locs_fold f (f l x) c
  | com_locs_fold f x (Const (@{const_name Cond2}, _) $ l $ _ $ c1 $ c2) = com_locs_fold f (com_locs_fold f (f l x) c1) c2
  | com_locs_fold f x (Const (@{const_name Loop}, _) $ c)                = com_locs_fold f x c
  | com_locs_fold f x (Const (@{const_name While}, _) $ l $ _ $ c)       = com_locs_fold f (f l x) c
  | com_locs_fold f x (Const (@{const_name Seq}, _) $ c1 $ c2)           = com_locs_fold f (com_locs_fold f x c1) c2
  | com_locs_fold f x (Const (@{const_name Choose}, _) $ c1 $ c2)        = com_locs_fold f (com_locs_fold f x c1) c2
  | com_locs_fold _ x _ = x;

fun com_locs_map f com = com_locs_fold (fn l => fn acc => f l :: acc) [] com

fun com_locs_fold_no_response f x (Const (@{const_name Request}, _) $ l $ _ $ _ )    = f l x
  | com_locs_fold_no_response _ x (Const (@{const_name Response}, _) $ _ $ _)        = x (* can often ignore \<open>Response\<close> *)
  | com_locs_fold_no_response f x (Const (@{const_name LocalOp}, _) $ l $ _)         = f l x
  | com_locs_fold_no_response f x (Const (@{const_name Cond1}, _) $ l $ _ $ c)       = com_locs_fold_no_response f (f l x) c
  | com_locs_fold_no_response f x (Const (@{const_name Cond2}, _) $ l $ _ $ c1 $ c2) = com_locs_fold_no_response f (com_locs_fold_no_response f (f l x) c1) c2
  | com_locs_fold_no_response f x (Const (@{const_name Loop}, _) $ c)                = com_locs_fold_no_response f x c
  | com_locs_fold_no_response f x (Const (@{const_name While}, _) $ l $ _ $ c)       = com_locs_fold_no_response f (f l x) c
  | com_locs_fold_no_response f x (Const (@{const_name Seq}, _) $ c1 $ c2)           = com_locs_fold_no_response f (com_locs_fold_no_response f x c1) c2
  | com_locs_fold_no_response f x (Const (@{const_name Choose}, _) $ c1 $ c2)        = com_locs_fold_no_response f (com_locs_fold_no_response f x c1) c2
  | com_locs_fold_no_response _ x _ = x;

fun com_locs_map_no_response f com = com_locs_fold_no_response (fn l => fn acc => f l :: acc) [] com

(* Cache location set membership facts.

Decide membership in the given set for each label in the CIMP programs
in the Named_Theorems "com".

If the label set and com types differ, we probably get a nasty error.

*)

fun def_locset thm ctxt =
  let
    val set_name = thm
                   |> Local_Defs.meta_rewrite_rule ctxt (* handle `=` or `\<equiv>` *)
                   |> Thm.cprop_of |> Thm.dest_equals |> fst |> Thm.term_of
    val set_typ = set_name |> type_of
    val elt_typ = case set_typ of Type ("Set.set", [t]) => t | _ => raise Fail "thm should define a set"
    val set_name_str = case set_name of Const (c, _) => c | Free (c, _) => c | _ => error ("Not an equation of the form x = set: " ^ Thm.string_of_thm ctxt thm)
    val thm_name = Binding.qualify true set_name_str (Binding.name "memb")
    fun mk_memb l = Thm.cterm_of ctxt (Const (@{const_name "Set.member"}, elt_typ --> set_typ --> @{typ "bool"}) $ l $ set_name)
    val rewrite_tac = Simplifier.rewrite (ctxt addsimps ([thm] @ Named_Theorems.get ctxt @{named_theorems "loc"})) (* probably want the ambient simpset + some stuff *)
    val coms = Named_Theorems.get ctxt @{named_theorems "com"} |> map (Thm.cprop_of #> Thm.dest_equals #> snd #> Thm.term_of)
    val attrs = [(* Attrib.internal (K (Clasimp.iff_add)), *) Attrib.internal (K (Named_Theorems.add @{named_theorems "loc"}))]
(* Parallel *)
    fun mk_thms coms = Par_List.map rewrite_tac (maps (com_locs_map_no_response mk_memb) coms)
(* Sequential *)
(*    fun mk_thms coms = List.foldl (fn (c, thms) => com_locs_fold (fn l => fn thms => rewrite_tac (mk_memb l) :: thms) thms c) [] coms *)
  in
    ctxt
    |> Local_Theory.note ((thm_name, attrs), mk_thms coms)
    |> snd
  end;

(* FIXME later need to rewrite using interned labels (fold defs). *)
fun def_inv thm ctxt : local_theory =
  let
    val attrs = [Attrib.internal (K (Named_Theorems.add @{named_theorems "inv"}))]
  in
    ctxt
    |> Local_Theory.note ((Binding.empty, attrs), [thm])
    |> snd
  end;

end;

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>inv_definition\<close> "constant definition for invariants"
    (Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
      Parse_Spec.if_assumes -- Parse.for_fixes >> (fn (((decl, spec), prems), params) => fn b => fn lthy =>
        Specification.definition_cmd decl params prems spec b lthy
        |> (fn ((_, (_, thm)), lthy) => (thm, lthy)) |> uncurry Cimp.def_inv));

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>locset_definition\<close> "constant definition for sets of locations"
    (Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
      Parse_Spec.if_assumes -- Parse.for_fixes >> (fn (((decl, spec), prems), params) => fn b => fn lthy =>
        Specification.definition_cmd decl params prems spec b lthy
        |> (fn ((_, (_, thm)), lthy) => (thm, lthy)) |> uncurry Cimp.def_locset));
\<close>

end
(*>*)
