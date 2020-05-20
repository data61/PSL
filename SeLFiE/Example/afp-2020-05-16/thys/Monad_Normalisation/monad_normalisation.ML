(*  Title:      monad_normalisation.ML
    Author:     Joshua Schneider, ETH Zurich
    Author:     Manuel Eberl, TU München

Normalisation of monadic expressions: commutation, distribution over control operators.
*)

signature MONAD_NORMALISATION =
sig
  val normalise_step: Proof.context -> cterm -> thm option
end;

structure Monad_Normalisation : MONAD_NORMALISATION =
struct

(*
  Copy of term_ord from Pure/term_ord.ML, with inverse order of bound variables.
  This aims to be stable under the substitution of bound variables with free variables when
  the simplifier descends into an abstraction, but relies on the particular naming scheme of
  the new variables (see Name.bound).
*)

local

fun hd_depth (t $ _, n) = hd_depth (t, n + 1)
  | hd_depth p = p;

fun dest_hd (Const (a, T)) = (((a, 0), T), 0)
  | dest_hd (Free (a, T)) = (((a, 0), T), 1)
  | dest_hd (Var v) = (v, 2)
  | dest_hd (Bound i) = ((("", ~i), dummyT), 3)
  | dest_hd (Abs (_, T, _)) = ((("", 0), T), 4);

in

fun term_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (Abs (_, T, t), Abs(_, U, u)) =>
        (case term_ord (t, u) of EQUAL => Term_Ord.typ_ord (T, U) | ord => ord)
    | (t, u) =>
        (case int_ord (size_of_term t, size_of_term u) of
          EQUAL =>
            (case prod_ord hd_ord int_ord (hd_depth (t, 0), hd_depth (u, 0)) of
              EQUAL => args_ord (t, u) | ord => ord)
        | ord => ord))
and hd_ord (f, g) =
  prod_ord (prod_ord Term_Ord.indexname_ord Term_Ord.typ_ord) int_ord (dest_hd f, dest_hd g)
and args_ord (f $ t, g $ u) =
      (case args_ord (f, g) of EQUAL => term_ord (t, u) | ord => ord)
  | args_ord _ = EQUAL;

end;


fun rename_commute_rule thm ct =
  let val (v1, v2) = (case Thm.term_of ct of
      (_ $ _ $ Abs (x1, _, _ $ _ $ y)) => (x1, case y of
          Abs (x2, _, _) => x2
        | _ => "x")
    | _ => ("x", "y"));
  in Drule.rename_bvars' [SOME v1, SOME v2, SOME v1] thm end;

fun dest_bind_term (Const (bindc, _) $ x $ y) = (bindc, x, y)
  | dest_bind_term _ = ("", Term.dummy, Term.dummy);

fun inst_bind_distrib ctxt ct = Drule.infer_instantiate' ctxt [SOME (Thm.dest_fun2 ct)];

fun normalise_step ctxt ct =
  let
    val (bindc, _, y) = dest_bind_term (Thm.term_of ct);

    fun search_control t1 t2 =
      let
        fun lookup i u = (case Term.head_of u of
            Const (c, _) => Option.map (pair i) (Monad_Rules.get_distrib_rule ctxt c)
          | _ => NONE);
        fun search (i, u1, u2) = if Term.loose_bvar1 (u1, i) then NONE
          else (case u2 of
              Abs (_, _, u2' as (Const (c, _) $ v1 $ v2)) =>
                if c = bindc then search (i + 1, v1, v2) else lookup (i + 1) u2'
            | Abs (_, _, u2') => lookup (i + 1) u2'
            | _ => NONE);
      in search (0, t1, t2) end;

    fun commute_distrib commute_eq distrib_eq depth =
      let fun conv ctxt' 0 ct' = Conv.rewr_conv (inst_bind_distrib ctxt' ct' distrib_eq) ct'
            | conv ctxt' i ct' = (Conv.rewr_conv (rename_commute_rule commute_eq ct') then_conv
                Conv.arg_conv (Conv.abs_conv (fn (_, ctxt'') => conv ctxt'' (i - 1)) ctxt')) ct'
      in try (conv ctxt depth) ct end;

    fun commute' commute_eq u ct' = if Term.loose_bvar1 (u, 0) then NONE
      else
        let val ct'' = Conv.rewr_conv commute_eq ct' |> Thm.rhs_of;
        in if is_less (term_ord (apply2 (Envir.beta_eta_contract o Thm.term_of) (ct'', ct')))
          then SOME (rename_commute_rule commute_eq ct') else NONE end;

    fun commute info u v = (case #bind_commute info of
        NONE => NONE
      | SOME commute_thm =>
          let val commute_eq = mk_meta_eq commute_thm
          in
            case search_control u v of
              SOME (depth, distrib_thm) =>
                (case commute_distrib commute_eq (mk_meta_eq distrib_thm) depth of
                  SOME thm => SOME thm
                | NONE => commute' commute_eq u ct)
            | NONE => commute' commute_eq u ct
          end);

    fun distribute t = (case Term.head_of t of
        Const (c, _) =>
          Option.map (inst_bind_distrib ctxt ct o mk_meta_eq) (Monad_Rules.get_distrib_rule ctxt c)
      | _ => NONE);
  in
    case Monad_Rules.get_monad ctxt bindc of
      NONE => NONE
    | SOME info => (case y of
        Abs (_, _, z as (Const (bindc', _) $ u $ v)) => if bindc = bindc' then
            commute info u v
          else
            distribute z
      | Abs (_, _, z) => distribute z
      | _ => NONE)
  end;

end;
