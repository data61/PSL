(*
  File: rewrite_test.ML
  Author: Bohua Zhan

  Unit test for rewrite.ML.
*)

local

val init = @{context}

fun add_prim_id (prim_id, id) ctxt =
    let
      val (prim_id', ctxt') = BoxID.add_prim_id id ctxt
      val _ = assert (prim_id = prim_id') "add_prim_id"
    in
      ctxt'
    end

(* Conversion between (id, th) used in rewrite.ML and (id, t) used in
   test cases.
 *)
fun to_term_info (id, th) = (id, Util.rhs_of th)
(* Comparison of list of box_ids. *)
val eq_id_list = eq_set (op =)
(* Comparison of list of (box_id, term) pairs. *)
val eq_info_list = eq_set (eq_pair (op =) (op aconv))

fun print_term_info ctxt (id, t) =
    "(" ^ (BoxID.string_of_box_id id) ^ ", " ^ (Syntax.string_of_term ctxt t) ^ ")"
fun print_term_infos ctxt lst =
    commas (map (print_term_info ctxt) lst)
val string_of_box_id_list = Util.string_of_list BoxID.string_of_box_id

fun done str _ = let val _ = tracing ("Finished " ^ str) in () end

(* info is expected, in box_id * term form, info' is returned value,
   in box_id * thm form (to be printed).
 *)
fun assert_eq_info (info, info') txt ctxt =
    if eq_info_list (info, map to_term_info info') then ctxt
    else let
      val _ = tracing ("Expected: " ^ print_term_infos ctxt info ^ "\n" ^
                       "Actual: " ^ print_infos ctxt info')
    in
      raise Fail txt
    end

fun assert_rew_info str info_str ctxt =
    let
      val t = Syntax.read_term ctxt str
      val ct = Thm.cterm_of ctxt t
      val info = map (apsnd (Syntax.read_term ctxt)) info_str
    in
      assert_eq_info (info, RewriteTable.get_rewrite_info ctxt ct)
                     "assert_rew_info" ctxt
    end

fun assert_srew_info str info_str ctxt =
    let
      val t = Syntax.read_term ctxt str
      val ct = Thm.cterm_of ctxt t
      val info = map (apsnd (Syntax.read_term ctxt)) info_str
    in
      assert_eq_info (info, RewriteTable.get_subterm_rewrite_info ctxt ct)
                     "assert_srew_info" ctxt
    end

fun assert_head_rep (id, str) info_str ctxt =
    let
      val t = Syntax.read_term ctxt str
      val ct = Thm.cterm_of ctxt t
      val info = map (apsnd (Syntax.read_term ctxt)) info_str
      val th = Thm.reflexive ct
    in
      assert_eq_info (info, RewriteTable.get_head_rep_with_id_th ctxt (id, th))
                     "assert_head_rep" ctxt
    end

fun assert_equiv_gen exp_equiv id (str1, str2) ctxt =
    let
      val (t1, t2) = (Syntax.read_term ctxt str1, Syntax.read_term ctxt str2)
    in
      if exp_equiv = RewriteTable.is_equiv_t id ctxt (t1, t2) then ctxt
      else let
        val _ = tracing ("id: " ^ (BoxID.string_of_box_id id))
        val _ = trace_tlist ctxt "Input:" [t1, t2]
      in
        raise Fail (if exp_equiv then "assert_equiv" else "assert_not_equiv")
      end
    end

val assert_equiv = assert_equiv_gen true
val assert_not_equiv = assert_equiv_gen false

fun assert_simpl_info str info_str ctxt =
    let
      val t = Syntax.read_term ctxt str
      val ct = Thm.cterm_of ctxt t
      val info = map (apsnd (Syntax.read_term ctxt)) info_str
    in
      assert_eq_info (info, RewriteTable.simplify_info ctxt ct)
                     "assert_simpl_info" ctxt
    end

fun assert_simpl id (str, str') ctxt =
    let
      val (t, t') = (Syntax.read_term ctxt str, Syntax.read_term ctxt str')
      val ct = Thm.cterm_of ctxt t
      val res = Util.rhs_of (RewriteTable.simplify id ctxt ct)
    in
      if res aconv t' then ctxt
      else let
        val _ = trace_t ctxt "Input:" t
        val _ = trace_t ctxt "Expected:" t'
        val _ = trace_t ctxt "Actual:" res
      in
        raise Fail "assert_simpl"
      end
    end

(* Collect all head equivs under box id. The return value of
   get_head_equiv is in the form [(head, [((id, th), groups), ...]), ...],
   and we want to collect the set of (id, th).
 *)
fun assert_head_equivs (id, str) info_str ctxt =
    let
      val cu = Thm.cterm_of ctxt (Syntax.read_term ctxt str)
      val info = map (apsnd (Syntax.read_term ctxt)) info_str
      val res = (RewriteTable.get_head_equiv ctxt cu)
                    |> BoxID.merge_box_with_info ctxt id
    in
      assert_eq_info (info, res) "assert_head_equivs" ctxt
    end

fun index_reps ctxt =
    let
      fun index_reps_t t =
          fold RewriteTable.update_subsimp
               (RewriteTable.get_subterm_rewrite_info ctxt t)
    in
      fold index_reps_t (RewriteTable.get_all_terms ctxt) ctxt
    end

fun declare_term str ctxt =
    Variable.auto_fixes (Syntax.read_term ctxt str) ctxt

(* First part: test internal functions. *)

(* Modification functions using terms. *)
fun add_equiv id (str1, str2) ctxt =
    let
      val (t1, t2) = (Syntax.read_term ctxt str1, Syntax.read_term ctxt str2)
      val thy = Proof_Context.theory_of ctxt
      val eq_th = Util.assume_meta_eq thy (t1, t2)
    in
      ctxt |> RewriteTable.add_equiv (id, eq_th)
    end

fun add_term str ctxt =
    ctxt |> RewriteTable.add_term ([], Thm.cterm_of ctxt (Syntax.read_term ctxt str)) |> snd

fun assert_eq_edges (str1, str2) ids ctxt =
    let
      val (t1, t2) = (Syntax.read_term ctxt str1, Syntax.read_term ctxt str2)
      val ids' = (RewriteTable.equiv_neighs ctxt t1)
                     |> map to_term_info
                     |> filter (fn (_, t2') => t2 aconv t2') |> map fst
    in
      if eq_id_list (ids, ids') then ctxt
      else let
        val _ = trace_tlist ctxt "Input:" [t1, t2]
        val _ = tracing ("Expected: " ^ (string_of_box_id_list ids) ^ "\n" ^
                         "Actual: " ^ (string_of_box_id_list ids'))
      in
        raise Fail "assert_eq_edges"
      end
    end

fun update_simp id (str1, str2) ctxt =
    let
      val (t1, t2) = (Syntax.read_term ctxt str1, Syntax.read_term ctxt str2)
      val thy = Proof_Context.theory_of ctxt
      val eq_th = Util.assume_meta_eq thy (t1, t2)
    in
      ctxt |> RewriteTable.update_simp (id, eq_th)
    end

fun assert_rewrite id (str, str') ctxt =
    let
      val (t, t') = (Syntax.read_term ctxt str, Syntax.read_term ctxt str')
      val res = Util.rhs_of (RewriteTable.get_rewrite id ctxt (Thm.cterm_of ctxt t))
    in
      if res aconv t' then ctxt
      else let
        val _ = trace_t ctxt "Input:" t
        val _ = trace_t ctxt "Expected:" t'
        val _ = trace_t ctxt "Actual:" res
      in
        raise Fail "assert_rewrite"
      end
    end

fun add_rewrite id (str1, str2) ctxt =
    let
      val (t1, t2) = (Syntax.read_term ctxt str1, Syntax.read_term ctxt str2)
      val thy = Proof_Context.theory_of ctxt
      val th = assume_eq thy (t1, t2)
    in
      ctxt |> RewriteTable.add_rewrite (id, th) |> snd
    end

in

val test_equiv_basic =
    init |> fold add_prim_id [(1, []), (2, [1]), (3, [1]), (4, [2])]
         |> declare_term "[a, b, c, d]"
         |> fold add_term ["a", "b", "c", "d"]
         |> add_equiv [2] ("a", "b") |> assert_eq_edges ("a", "b") [[2]]
         |> add_equiv [3] ("b", "c") |> assert_eq_edges ("b", "c") [[3]]
         |> add_equiv [] ("a", "b")  |> assert_eq_edges ("a", "b") [[]]
         |> add_equiv [4] ("a", "d") |> assert_eq_edges ("a", "d") [[4]]
         |> add_equiv [3] ("a", "d") |> assert_eq_edges ("a", "d") [[3], [4]]
         |> add_equiv [2] ("a", "d") |> assert_eq_edges ("a", "d") [[2], [3]]
         |> add_equiv [] ("a", "d")  |> assert_eq_edges ("a", "d") [[]]
         |> done "test_equiv_basic"

val test_simp_basic =
    init |> fold add_prim_id [(1, []), (2, [1]), (3, [1]), (4, [2])]
         |> declare_term "[a, b, c, d, e]"
         |> fold add_term ["a", "b", "c", "d", "e"]
         |> update_simp [2] ("e", "d") |> assert_rewrite [2, 3] ("e", "d")
         |> update_simp [3] ("e", "c") |> assert_rewrite [3] ("e", "c")
         |> update_simp [3] ("e", "b") |> assert_rewrite [2, 3] ("e", "b")
         |> update_simp [4] ("e", "a") |> assert_rewrite [2, 3] ("e", "b")
         |> update_simp [2] ("e", "b")
         |> update_simp [2, 3] ("e", "a")
         |> assert_rew_info "e" [([], "e"), ([4], "a"), ([3], "b"),
                                 ([2], "b"), ([2, 3], "a")]
         |> done "test_simp_basic"

val test_head_rep =
    init |> fold add_prim_id [(1, []), (2, [1]), (3, [1])]
         |> fold declare_term ["[a, b, c, d]", "f a b"]
         |> add_term "f b d"
         |> update_simp [2] ("d", "c")
         |> update_simp [3] ("b", "a")
         |> assert_srew_info "f b d" [([], "f b d"), ([2], "f b c"),
                                      ([3], "f a d"), ([2, 3], "f a c")]
         |> index_reps
         |> assert_head_rep ([], "f a c") [([2, 3], "f b d")]
         |> assert_head_rep ([], "f b c") [([2], "f b d")]
         |> assert_head_rep ([], "f a d") [([3], "f b d")]
         |> assert_head_rep ([], "f b d") [([], "f b d")]
         |> assert_head_rep ([3], "f b c") [([2, 3], "f b d")]
         |> done "test_head_rep"

val test_head_rep3 =
    init |> fold add_prim_id [(1, []), (2, [1]), (3, [1])]
         |> fold declare_term ["[a, b, c, d]", "f a b"]
         |> add_term "f b c" |> add_term "f a d"
         |> update_simp [2] ("d", "c")
         |> update_simp [3] ("b", "a")
         |> index_reps
         |> assert_head_rep ([], "f a c") [([2], "f a d"), ([3], "f b c")]
         |> assert_head_rep ([2], "f a c") [([2], "f a d"), ([2, 3], "f b c")]
         |> assert_head_rep ([3], "f a c") [([3], "f b c"), ([2, 3], "f a d")]
         |> done "test_head_rep3"

val test_add_term =
    init |> fold add_prim_id [(1, []), (2, [1]), (3, [1])]
         |> fold declare_term ["[a, b, c, d]", "f a b"]
         |> add_rewrite [2] ("d", "c")
         |> add_rewrite [3] ("b", "a")
         |> index_reps
         |> add_term "f b c" |> add_term "f a d"
         |> assert_head_rep ([], "f a c") [([2], "f a d"), ([3], "f b c")]
         |> assert_eq_edges ("f a d", "f b c") [[2, 3]]
         |> add_term "f a c" |> add_term "f b d"
         |> assert_head_rep ([], "f a c") [([], "f a c"), ([2], "f a d"),
                                           ([3], "f b c"), ([2, 3], "f b d")]
         |> assert_equiv [2, 3] ("f a c", "f b d")
         |> assert_not_equiv [2] ("f a c", "f b d")
         |> assert_not_equiv [3] ("f a c", "f b d")
         |> done "test_add_term"

val test_add_rewrite =
    init |> fold add_prim_id [(1, []), (2, [1]), (3, [1])]
         |> fold declare_term ["[a, b, c, d]", "f a b"]
         |> add_term "f a d"
         |> add_rewrite [2] ("d", "c")
         |> assert_head_rep ([], "f a c") [([2], "f a d")]
         |> add_term "f b d"
         |> assert_head_rep ([], "f b c") [([2], "f b d")]
         |> add_rewrite [3] ("a", "b")
         |> assert_eq_edges ("f a d", "f b d") [[3]]
         |> assert_rew_info "f b d" [([], "f b d"), ([2], "f b c"),
                                     ([3], "f a d"), ([2, 3], "f a c")]
         |> add_term "f b c"
         |> assert_head_rep ([], "f a c") [([2], "f a d"), ([3], "f b c"),
                                           ([2, 3], "f b d")]
         |> done "test_add_rewrite"

val test_simplify =
    init |> fold add_prim_id [(1, []), (2, [1]), (3, [1])]
         |> fold declare_term ["[a, b, c, d]", "[f a b, e]"]
         |> add_rewrite [1] ("f b d", "e")
         |> add_rewrite [2] ("d", "c")
         |> add_rewrite [3] ("b", "a")
         |> assert_simpl_info "f a c" [([], "f a c"), ([2, 3], "e")]
         |> assert_simpl_info "f a d" [([], "f a d"), ([2], "f a c"),
                                       ([3], "e")]
         |> assert_simpl_info "f b c" [([], "f b c"), ([3], "f a c"),
                                       ([2], "e")]
         |> assert_simpl_info "f b d" [([], "f b d"), ([1], "e")]
         |> assert_simpl [2] ("f a c", "f a c")
         |> assert_simpl [2, 3] ("f a c", "e")
         |> assert_simpl [2] ("f a d", "f a c")
         |> assert_simpl [3] ("f a d", "e")
         |> assert_simpl [2, 3] ("f a d", "e")
         |> add_rewrite [] ("f b d", "e")
         |> assert_simpl_info "f b d" [([], "e")]
         |> add_term "f a c"
         |> assert_equiv [2, 3] ("f a c", "f b d")
         |> done "test_simplify"

val test_simplify2 =
    init |> fold add_prim_id [(1, []), (2, [1]), (3, [1]), (4, [2])]
         |> declare_term "[a, b, c, d]"
         |> add_rewrite [3] ("b", "c")
         |> add_rewrite [4] ("a", "b")
         |> add_rewrite [2] ("c", "d")
         |> assert_simpl_info "c" [([], "c"), ([3], "b"), ([3, 4], "a")]
         |> assert_simpl_info "d" [([], "d"), ([2], "c"), ([2, 3], "b"),
                                   ([3, 4], "a")]
         |> done "test_simplify2"

val test_simplify3 =
    init |> fold add_prim_id [(1, []), (2, [1])]
         |> declare_term "[a, b, c, d, e, g]"
         |> add_rewrite [1] ("e", "c") |> add_rewrite [1] ("g", "d")
         |> add_rewrite [2] ("e", "b") |> add_rewrite [2] ("g", "a")
         |> add_rewrite [] ("e", "g")
         |> assert_simpl_info "e" [([], "e"), ([1], "c"), ([2], "a")]
         |> assert_simpl_info "g" [([], "e"), ([1], "c"), ([2], "a")]
         |> done "test_simplify3"

val test_head_equivs =
    init |> fold add_prim_id [(1, []), (2, [1]), (3, [1])]
         |> fold declare_term ["[a, b, c, d]", "[f a b, e]"]
         |> add_rewrite [1] ("f b d", "e")
         |> add_rewrite [2] ("d", "c")
         |> add_rewrite [3] ("b", "a")
         |> assert_head_equivs ([], "c") [([], "c"), ([2], "d")]
         |> assert_head_equivs ([], "f b d") [([], "f b d"), ([1], "e")]
         |> assert_head_equivs ([2], "f b c") [([2], "f b c"), ([2], "e"), ([2], "f b d")]
         |> assert_head_equivs ([], "f b c") [([], "f b c"), ([2], "e"), ([2], "f b d")]
         |> assert_head_equivs ([], "f a c") [([], "f a c"), ([2, 3], "e"), ([2, 3], "f b d")]
         |> add_term "f a c"
         |> assert_head_equivs ([], "f b d") [([], "f b d"), ([1], "e"), ([2, 3], "f a c")]
         |> assert_head_equivs ([], "f a c") [([], "f a c"), ([2, 3], "e"), ([2, 3], "f b d")]
         |> assert_head_equivs ([], "f b c") [([], "f b c"), ([2], "e"), ([2], "f b d"), ([3], "f a c")]
         |> done "test_head_equivs"

val test_head_equivs2 =
    init |> fold add_prim_id [(1, []), (2, [1]), (3, [1]), (4, [2])]
         |> declare_term "[a, b, c, d]"
         |> add_rewrite [3] ("b", "c")
         |> add_rewrite [4] ("a", "b")
         |> assert_head_equivs ([], "b") [([], "b"), ([3], "c"), ([4], "a")]
         |> add_rewrite [2] ("c", "d")
         |> assert_head_equivs ([], "b") [([], "b"), ([3], "c"), ([4], "a"),
                                          ([2, 3], "d")]
         |> done "test_head_equivs2"

val test_head_equivs3 =
    init |> fold add_prim_id [(1, []), (2, [1]), (3, [1])]
         |> fold declare_term ["[a, b, c, d]", "[f a b, e]"]
         |> add_rewrite [] ("b", "a")
         |> add_rewrite [2] ("f b d", "e")
         |> add_rewrite [3] ("f a d", "e")
         (* Both fbd and fad are ok in the result. *)
         |> assert_head_equivs ([], "f a d") [([], "f b d"), ([2], "e"), ([3], "e"), ([], "f a d")]
         |> assert_head_equivs ([], "f b d") [([], "f a d"), ([2], "e"), ([3], "e"), ([], "f b d")]
         |> done "test_head_equivs3"

val test_head_equivs4 =
    init |> fold add_prim_id [(1, []), (2, [1]), (3, [1])]
         |> fold declare_term ["[a, b, c, d]", "[f a b, e]"]
         |> add_rewrite [2] ("b", "a")
         |> add_rewrite [] ("f b c", "e")
         |> add_rewrite [3] ("f a c", "e")  (* Note fbc ~ fac under 3. *)
         |> assert_head_equivs ([], "f b c") [([], "f b c"), ([], "e"), ([3], "f a c"), ([2], "f a c")]
         |> assert_head_equivs ([], "f a c") [([], "f a c"), ([2], "e"), ([3], "e"), ([3], "f b c"), ([2], "f b c")]
         |> done "test_head_equivs4"

(* Simplify with nat variables. *)
val test_simplify_nat =
    init |> declare_term "[a::nat, b, c]"
         |> add_rewrite [] ("a + b", "b + a")
         |> add_rewrite [] ("a", "c")
         |> assert_simpl [] ("b + c", "a + b")
         |> assert_equiv [] ("b + c", "a + b")
         |> done "test_simplify_nat"

end;  (* local *)
