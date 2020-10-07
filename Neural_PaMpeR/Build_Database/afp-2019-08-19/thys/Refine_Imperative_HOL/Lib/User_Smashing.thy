theory User_Smashing
  imports Pure
begin
(* Alternative flex-flex smasher by Simon Wimmer *)
ML \<open>
  fun enumerate xs = fold (fn x => fn (i, xs) => (i +1, (x, i) :: xs)) xs (0, []) |> snd
\<close>

ML \<open>
  fun dummy_abs _ [] t = t
    | dummy_abs n (T :: Ts) t = Abs ("x" ^ Int.toString n, T, dummy_abs (n + 1) Ts t)
\<close>

ML \<open>
  fun common_prefix Ts (t1 as Abs (_, T, t)) (u1 as Abs (_, U, u)) =
    if U = T then common_prefix (T :: Ts) t u else ([], t1, u1)
    | common_prefix Ts t u = (Ts, t, u);

  fun dest_app acc (t $ u) = dest_app (u :: acc) t
    | dest_app acc t = (t, acc);

  fun add_bound (Bound i, n) bs = (i, n) :: bs
    | add_bound _ bs = bs;
\<close>

ML \<open>
  fun smash_pair ctxt thm (t, u) =
    let
      val idx = Thm.maxidx_of thm + 1;
      val ctxt' = ctxt;
      val (Ts, t1, _) = common_prefix [] t u;
      val (tas, t2) = Term.strip_abs t;
      val (uas, u2) = Term.strip_abs u;
      val (tx as Var (_, T1), ts) = Term.strip_comb t2;
      val (ux as Var (_, U1), us) = Term.strip_comb u2;
      val Ts1 = Term.binder_types T1;
      val Us1 = Term.binder_types U1;
      val T = Term.fastype_of1 (Ts, t1);
      val tshift = length tas - length Ts;
      val ushift = length uas - length Ts;
      val tbs = fold add_bound (enumerate (rev ts)) [] |> map (apfst (fn i => i - tshift));
      val ubs = fold add_bound (enumerate (rev us)) [] |> map (apfst (fn i => i - ushift));
      val bounds = inter (op =) (map fst tbs) (map fst ubs) |> distinct (=);
      val T' = map (nth Ts) bounds ---> T;
      val v = Var (("simon", idx), T');
      val tbs' = map (fn i => find_first (fn (j, _) => i = j) tbs |> the |> snd |> Bound) bounds;
      val t' = list_comb (v, tbs') |> dummy_abs 0 Ts1;
      (* Need to add bounds for superfluous abstractions here *)
      val ubs' = map (fn i => find_first (fn (j, _) => i = j) ubs |> the |> snd |> Bound) bounds;
      val u' = list_comb (v, ubs') |> dummy_abs 0 Us1;
      val subst = [(Term.dest_Var tx, Thm.cterm_of ctxt' t'), (Term.dest_Var ux, Thm.cterm_of ctxt' u')];
    in
      instantiate_normalize ([], subst) thm
    end;
    fun smash ctxt thm =
      case (Thm.tpairs_of thm) of
        [] => thm
      | (p :: _) => smash_pair ctxt thm p;
    fun smashed_attrib ctxt thm =
      (NONE, SOME (smash ctxt thm));
\<close>

ML \<open>
  val smash_new_rule = Seq.single oo smash;
\<close>

end
