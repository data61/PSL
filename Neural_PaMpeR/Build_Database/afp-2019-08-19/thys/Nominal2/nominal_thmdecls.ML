(*  Title:      nominal_thmdecls.ML
    Author:     Christian Urban
    Author:     Tjark Weber

  Infrastructure for the lemma collections "eqvts", "eqvts_raw".

  Provides the attributes [eqvt] and [eqvt_raw], and the theorem
  lists "eqvts" and "eqvts_raw".

  The [eqvt] attribute expects a theorem of the form

    ?p \<bullet> (c ?x1 ?x2 ...) = c (?p \<bullet> ?x1) (?p \<bullet> ?x2) ...    (1)

  or, if c is a relation with arity >= 1, of the form

    c ?x1 ?x2 ... ==> c (?p \<bullet> ?x1) (?p \<bullet> ?x2) ...         (2)

  [eqvt] will store this theorem in the form (1) or, if c
  is a relation with arity >= 1, in the form

    c (?p \<bullet> ?x1) (?p \<bullet> ?x2) ... = c ?x1 ?x2 ...           (3)

  in "eqvts". (The orientation of (3) was chosen because
  Isabelle's simplifier uses equations from left to right.)
  [eqvt] will also derive and store the theorem

    ?p \<bullet> c == c                                           (4)

  in "eqvts_raw".

  (1)-(4) are all logically equivalent. We consider (1) and (2)
  to be more end-user friendly, i.e., slightly more natural to
  understand and prove, while (3) and (4) make the rewriting
  system for equivariance more predictable and less prone to
  looping in Isabelle.

  The [eqvt_raw] attribute expects a theorem of the form (4),
  and merely stores it in "eqvts_raw".

  [eqvt_raw] is provided because certain equivariance theorems
  would lead to looping when used for simplification in the form
  (1): notably, equivariance of permute (infix \<bullet>), i.e.,
  ?p \<bullet> (?q \<bullet> ?x) = (?p \<bullet> ?q) \<bullet> (?p \<bullet> ?x).

  To support binders such as All/Ex/Ball/Bex etc., which are
  typically applied to abstractions, argument terms ?xi (as well
  as permuted arguments ?p \<bullet> ?xi) in (1)-(3) need not be eta-
  contracted, i.e., they may be of the form "%z. ?xi z" or
  "%z. (?p \<bullet> ?x) z", respectively.

  For convenience, argument terms ?xi (as well as permuted
  arguments ?p \<bullet> ?xi) in (1)-(3) may actually be tuples, e.g.,
  "(?xi, ?xj)" or "(?p \<bullet> ?xi, ?p \<bullet> ?xj)", respectively.

  In (1)-(4), "c" is either a (global) constant or a locally
  fixed parameter, e.g., of a locale or type class.
*)

signature NOMINAL_THMDECLS =
sig
  val eqvt_add: attribute
  val eqvt_del: attribute
  val eqvt_raw_add: attribute
  val eqvt_raw_del: attribute
  val get_eqvts_thms: Proof.context -> thm list
  val get_eqvts_raw_thms: Proof.context -> thm list
  val eqvt_transform: Proof.context -> thm -> thm
  val is_eqvt: Proof.context -> term -> bool
end;

structure Nominal_ThmDecls: NOMINAL_THMDECLS =
struct

structure EqvtData = Generic_Data
( type T = thm Item_Net.T;
  val empty = Thm.full_rules;
  val extend = I;
  val merge = Item_Net.merge);

(* EqvtRawData is implemented with a Termtab (rather than an
   Item_Net) so that we can efficiently decide whether a given
   constant has a corresponding equivariance theorem stored, cf.
   the function is_eqvt. *)
structure EqvtRawData = Generic_Data
( type T = thm Termtab.table;
  val empty = Termtab.empty;
  val extend = I;
  val merge = Termtab.merge (K true));

val eqvts = Item_Net.content o EqvtData.get
val eqvts_raw = map snd o Termtab.dest o EqvtRawData.get

val _ =
  Theory.setup
   (Global_Theory.add_thms_dynamic (@{binding "eqvts"}, eqvts) #>
    Global_Theory.add_thms_dynamic (@{binding "eqvts_raw"}, eqvts_raw))

val get_eqvts_thms = eqvts o Context.Proof
val get_eqvts_raw_thms = eqvts_raw o Context.Proof


(** raw equivariance lemmas **)

(* Returns true iff an equivariance lemma exists in "eqvts_raw"
   for a given term. *)
val is_eqvt =
  Termtab.defined o EqvtRawData.get o Context.Proof

(* Returns c if thm is of the form (4), raises an error
   otherwise. *)
fun key_of_raw_thm context thm =
  let
    fun error_msg () =
      error
        ("Theorem must be of the form \"?p \<bullet> c \<equiv> c\", with c a constant or fixed parameter:\n" ^
         Syntax.string_of_term (Context.proof_of context) (Thm.prop_of thm))
  in
    case Thm.prop_of thm of
      Const (@{const_name Pure.eq}, _) $ (Const (@{const_name "permute"}, _) $ p $ c) $ c' =>
        if is_Var p andalso is_fixed (Context.proof_of context) c andalso c aconv c' then
          c
        else
          error_msg ()
    | _ => error_msg ()
  end

fun add_raw_thm thm context =
  let
    val c = key_of_raw_thm context thm
  in
    if Termtab.defined (EqvtRawData.get context) c then
      warning ("Replacing existing raw equivariance theorem for \"" ^
        Syntax.string_of_term (Context.proof_of context) c ^ "\".")
    else ();
    EqvtRawData.map (Termtab.update (c, thm)) context
  end

fun del_raw_thm thm context =
  let
    val c = key_of_raw_thm context thm
  in
    if Termtab.defined (EqvtRawData.get context) c then
      EqvtRawData.map (Termtab.delete c) context
    else (
      warning ("Cannot delete non-existing raw equivariance theorem for \"" ^
        Syntax.string_of_term (Context.proof_of context) c ^ "\".");
      context
    )
  end


(** adding/deleting lemmas to/from "eqvts" **)

fun add_thm thm context =
  (
    if Item_Net.member (EqvtData.get context) thm then
      warning ("Theorem already declared as equivariant:\n" ^
        Syntax.string_of_term (Context.proof_of context) (Thm.prop_of thm))
    else ();
    EqvtData.map (Item_Net.update thm) context
  )

fun del_thm thm context =
  (
    if Item_Net.member (EqvtData.get context) thm then
      EqvtData.map (Item_Net.remove thm) context
    else (
      warning ("Cannot delete non-existing equivariance theorem:\n" ^
        Syntax.string_of_term (Context.proof_of context) (Thm.prop_of thm));
      context
    )
  )


(** transformation of equivariance lemmas **)

(* Transforms a theorem of the form (1) into the form (4). *)
local

fun tac ctxt thm =
  let
    val ss_thms = @{thms "permute_minus_cancel" "permute_prod.simps" "split_paired_all"}
  in
    REPEAT o FIRST'
      [CHANGED o simp_tac (put_simpset HOL_basic_ss ctxt addsimps ss_thms),
       resolve_tac ctxt [thm RS @{thm trans}],
       resolve_tac ctxt @{thms trans[OF "permute_fun_def"]} THEN'
       resolve_tac ctxt @{thms ext}]
  end

in

fun thm_4_of_1 ctxt thm =
  let
    val (p, c) = thm |> Thm.prop_of |> HOLogic.dest_Trueprop
      |> HOLogic.dest_eq |> fst |> dest_perm ||> fst o (fixed_nonfixed_args ctxt)
    val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (mk_perm p c, c))
    val ([goal', p'], ctxt') = Variable.import_terms false [goal, p] ctxt
  in
    Goal.prove ctxt [] [] goal' (fn {context, ...} => tac context thm 1)
      |> singleton (Proof_Context.export ctxt' ctxt)
      |> (fn th => th RS @{thm "eq_reflection"})
      |> zero_var_indexes
  end
  handle TERM _ =>
    raise THM ("thm_4_of_1", 0, [thm])

end (* local *)

(* Transforms a theorem of the form (2) into the form (1). *)
local

fun tac ctxt thm thm' =
  let
    val ss_thms = @{thms "permute_minus_cancel"(2)}
  in
    EVERY' [resolve_tac ctxt @{thms iffI},
      dresolve_tac ctxt @{thms permute_boolE},
      resolve_tac ctxt [thm],
      assume_tac ctxt,
      resolve_tac ctxt @{thms permute_boolI},
      dresolve_tac ctxt [thm'],
      full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps ss_thms)]
  end

in

fun thm_1_of_2 ctxt thm =
  let
    val (prem, concl) = thm |> Thm.prop_of |> Logic.dest_implies |> apply2 HOLogic.dest_Trueprop
    (* since argument terms "?p \<bullet> ?x1" may actually be eta-expanded
       or tuples, we need the following function to find ?p *)
    fun find_perm (Const (@{const_name "permute"}, _) $ (p as Var _) $ _) = p
      | find_perm (Const (@{const_name "Pair"}, _) $ x $ _) = find_perm x
      | find_perm (Abs (_, _, body)) = find_perm body
      | find_perm _ = raise THM ("thm_3_of_2", 0, [thm])
    val p = concl |> dest_comb |> snd |> find_perm
    val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (mk_perm p prem, concl))
    val ([goal', p'], ctxt') = Variable.import_terms false [goal, p] ctxt
    val thm' = infer_instantiate ctxt' [(#1 (dest_Var p), Thm.cterm_of ctxt' (mk_minus p'))] thm
  in
    Goal.prove ctxt' [] [] goal' (fn {context = ctxt'', ...} => tac ctxt'' thm thm' 1)
      |> singleton (Proof_Context.export ctxt' ctxt)
  end
  handle TERM _ =>
    raise THM ("thm_1_of_2", 0, [thm])

end (* local *)

(* Transforms a theorem of the form (1) into the form (3). *)
fun thm_3_of_1 _ thm =
  (thm RS (@{thm "permute_bool_def"} RS @{thm "sym"} RS @{thm "trans"}) RS @{thm "sym"})
    |> zero_var_indexes

local
  val msg = cat_lines
    ["Equivariance theorem must be of the form",
     "  ?p \<bullet> (c ?x1 ?x2 ...) = c (?p \<bullet> ?x1) (?p \<bullet> ?x2) ...",
     "or, if c is a relation with arity >= 1, of the form",
     "  c ?x1 ?x2 ... ==> c (?p \<bullet> ?x1) (?p \<bullet> ?x2) ..."]
in

(* Transforms a theorem of the form (1) or (2) into the form (4). *)
fun eqvt_transform ctxt thm =
  (case Thm.prop_of thm of @{const "Trueprop"} $ _ =>
    thm_4_of_1 ctxt thm
  | @{const Pure.imp} $ _ $ _ =>
    thm_4_of_1 ctxt (thm_1_of_2 ctxt thm)
  | _ =>
    error msg)
  handle THM _ =>
    error msg

(* Transforms a theorem of the form (1) into theorems of the
   form (1) (or, if c is a relation with arity >= 1, of the form
   (3)) and (4); transforms a theorem of the form (2) into
   theorems of the form (3) and (4). *)
fun eqvt_and_raw_transform ctxt thm =
  (case Thm.prop_of thm of @{const "Trueprop"} $ (Const (@{const_name "HOL.eq"}, _) $ _ $ c_args) =>
    let
      val th' =
        if fastype_of c_args = @{typ "bool"}
            andalso (not o null) (snd (fixed_nonfixed_args ctxt c_args)) then
          thm_3_of_1 ctxt thm
        else
          thm
    in
      (th', thm_4_of_1 ctxt thm)
    end
  | @{const Pure.imp} $ _ $ _ =>
    let
      val th1 = thm_1_of_2 ctxt thm
    in
      (thm_3_of_1 ctxt th1, thm_4_of_1 ctxt th1)
    end
  | _ =>
    error msg)
  handle THM _ =>
    error msg

end (* local *)


(** attributes **)

val eqvt_raw_add = Thm.declaration_attribute add_raw_thm
val eqvt_raw_del = Thm.declaration_attribute del_raw_thm

fun eqvt_add_or_del eqvt_fn raw_fn =
  Thm.declaration_attribute
    (fn thm => fn context =>
      let
        val (eqvt, raw) = eqvt_and_raw_transform (Context.proof_of context) thm
      in
        context |> eqvt_fn eqvt |> raw_fn raw
      end)

val eqvt_add = eqvt_add_or_del add_thm add_raw_thm
val eqvt_del = eqvt_add_or_del del_thm del_raw_thm

val _ =
  Theory.setup
   (Attrib.setup @{binding "eqvt"} (Attrib.add_del eqvt_add eqvt_del)
      "Declaration of equivariance lemmas - they will automatically be brought into the form ?p \<bullet> c \<equiv> c" #>
    Attrib.setup @{binding "eqvt_raw"} (Attrib.add_del eqvt_raw_add eqvt_raw_del)
      "Declaration of raw equivariance lemmas - no transformation is performed")

end;
