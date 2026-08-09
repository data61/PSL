(*  Title:      TBC/Pretty_Consts.ML
    Author:     Timothy Bourke and Gerwin Klein, NICTA
    Author:     Yutaka Nagashima, Huawei Technologies Research & Development (UK) Limited.

This code-block is an adaptation of the following file found in Isabelle 2022.
    Title:      Pure/Tools/find_consts.ML
    Author:     Timothy Bourke and Gerwin Klein, NICTA

Hoogle-like (https://www-users.cs.york.ac.uk/~ndm/hoogle) searching by
type over constants, but matching is not fuzzy.
*)
(*** signature PRETTY_CONSTS ***)
signature PRETTY_CONSTS =
sig

val pretty_consts: Proof.context -> (bool * Find_Consts.criterion) list -> (string * typ) list;

end;

(*** structure Pretty_Consts ***)
structure Pretty_Consts: PRETTY_CONSTS =
struct

(* matching types/consts *)

fun matches_subtype thy typat =
  Term.exists_subtype (fn ty => Sign.typ_instance thy (ty, typat));

fun check_const pred (c, (ty, _)) =
  if pred (c, ty) then SOME (Term.size_of_typ ty) else NONE;

fun opt_not f (c as (_, (ty, _))) =
  if is_some (f c) then NONE else SOME (Term.size_of_typ ty);

fun filter_const _ _ NONE = NONE
  | filter_const c f (SOME rank) =
      (case f c of
        NONE => NONE
      | SOME i => SOME (Int.min (rank, i)));

(* find_consts *)

fun pretty_consts ctxt raw_criteria =
  let
    val thy = Proof_Context.theory_of ctxt;
    val low_ranking = 10000;

    fun make_pattern crit =
      let
        val raw_T = Syntax.parse_typ ctxt crit;
        val t =
          Syntax.check_term
            (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)
            (Term.dummy_pattern raw_T);
      in Term.type_of t end;

    fun make_match (Find_Consts.Strict arg) =
          let val qty = make_pattern arg; in
            fn (_, (ty, _)) =>
              let
                val tye = Vartab.build (Sign.typ_match thy (qty, ty));
                val sub_size =
                  Vartab.fold (fn (_, (_, t)) => fn n => Term.size_of_typ t + n) tye 0;
              in SOME sub_size end handle Type.TYPE_MATCH => NONE
          end
      | make_match (Find_Consts.Loose arg) =
          check_const (matches_subtype thy (make_pattern arg) o snd)
      | make_match (Find_Consts.Name arg) = check_const (match_string arg o fst);

    fun make_criterion (b, crit) = (if b then I else opt_not) (make_match crit);
    val criteria = map make_criterion raw_criteria;

    fun user_visible (c, _) =
      if Consts.is_concealed (Proof_Context.consts_of ctxt) c
      then NONE else SOME low_ranking;

    fun eval_entry c =
      fold (filter_const c) (user_visible :: criteria) (SOME low_ranking);

    val {constants, ...} = Consts.dest (Sign.consts_of thy);
    val matches =
      fold (fn c => (case eval_entry c of NONE => I | SOME rank => cons (rank, c))) constants []
      |> sort (prod_ord (rev_order o int_ord) (string_ord o apply2 fst))
      |> map (apsnd fst o snd);
  in
    matches
  end;
end;
