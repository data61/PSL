(*
  File: matcher_test.ML
  Author: Bohua Zhan

  Unit test of matcher.ML.
*)

local

val init = @{context}

(* Conversion between (id, th) used in rewrite.ML and (id, t) used in
   test cases.
 *)
fun to_term_info (id, th) = (id, Util.rhs_of th)

(* Comparison of list of (box_id, term) pairs. *)
fun eq_info_list (l1, l2) =
    (length l1 = length l2) andalso eq_set (eq_pair (op =) (op aconv)) (l1, l2)

fun print_term_info ctxt (id, t) =
    "(" ^ (BoxID.string_of_box_id id) ^ ", " ^ (Syntax.string_of_term ctxt t) ^ ")"

fun print_term_infos ctxt lst =
    commas (map (print_term_info ctxt) lst)

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

fun add_prim_id (prim_id, id) ctxt =
    let
      val (prim_id', ctxt') = BoxID.add_prim_id id ctxt
      val _ = assert (prim_id = prim_id') "add_prim_id"
    in
      ctxt'
    end

fun declare_term str ctxt =
    Variable.auto_fixes (Syntax.read_term ctxt str) ctxt

fun declare_pat str ctxt =
    Variable.auto_fixes (Proof_Context.read_term_pattern ctxt str) ctxt

fun add_rewrite id (str1, str2) ctxt =
    let
      val (t1, t2) = (Syntax.read_term ctxt str1, Syntax.read_term ctxt str2)
      val thy = Proof_Context.theory_of ctxt
      val th = assume_eq thy (t1, t2)
    in
      ctxt |> RewriteTable.add_rewrite (id, th) |> snd
    end

(* Check th is actually t(env) == u. *)
fun check_info (t, u) txt ctxt ((_, inst), th) =
    let
      val t' = Util.subst_term_norm inst t
      val (lhs, rhs) = Logic.dest_equals (Thm.prop_of th)
    in
      if lhs aconv t' andalso rhs aconv u then ()
      else let
        val _ = tracing ("inst does not match th.\nt', u' = " ^
                         (Util.string_of_terms ctxt [t', u]) ^
                         "\nth = " ^
                         (Syntax.string_of_term ctxt (Thm.prop_of th)))
      in raise Fail txt end
    end

fun assert_match_gen matcher ((str_t, str_u), info_str) ctxt =
    let
      val (t, u) = (Proof_Context.read_term_pattern ctxt str_t,
                    Syntax.read_term ctxt str_u)
      val _ = trace_tlist ctxt "Matching" [t, u]
      val info = map (apsnd (Syntax.read_term ctxt)) info_str
      val info' = matcher ctxt [] (t, Thm.cterm_of ctxt u) ([], fo_init)
      val _ = map (check_info (t, u) "assert_match" ctxt) info'
      val info'' = map (fn ((id, _), th) => (id, meta_sym th)) info'
    in
      assert_eq_info (info, info'') "assert_match" ctxt
    end

val assert_match = assert_match_gen Matcher.match

fun assert_match_list (pairs_str, info_str) ctxt =
    let
      val pairs =
          map (fn (is_head, (str_t, str_u)) =>
                  (is_head, (Proof_Context.read_term_pattern ctxt str_t,
                             Thm.cterm_of ctxt (Syntax.read_term ctxt str_u))))
              pairs_str
      val info = map (apsnd (map (Syntax.read_term ctxt))) info_str
      val info' = Matcher.rewrite_match_list ctxt pairs ([], fo_init)
      fun check_info_list (instsp, ths) =
          let
            fun check_pair ((t, cu), th) =
                check_info (t, Thm.term_of cu)
                           "assert_match_list" ctxt (instsp, th)
          in
            map check_pair (map snd pairs ~~ ths)
          end
      val _ = map check_info_list info'
      val info'' = map (fn ((id, _), ths) => (id, map meta_sym ths)) info'
      val eq_info_list' = eq_set (eq_pair (op =) (eq_list (op aconv)))
      fun to_term_info' (id, ths) = (id, map Util.rhs_of ths)
    in
      if eq_info_list' (info, map to_term_info' info'') then ctxt
      else let
        val _ = tracing ("got " ^ print_infos' ctxt info'')
      in
        raise Fail "assert_match_list"
      end
    end

fun done str _ = let val _ = tracing ("Finished " ^ str) in () end

in

(* Basic rewriting. *)
val test_rewrite =
    init |> add_prim_id (1, []) |> add_prim_id (2, [])
         |> declare_term "[a::nat, b, c]"
         |> declare_term "f::(nat => nat => nat)"
         |> declare_pat "[?m::nat, ?n]"
         |> declare_pat "?A::('a::{plus})"
         |> add_rewrite [1] ("a", "b")
         |> add_rewrite [2] ("a", "c")
         |> fold assert_match
         [(("a", "b"), [([1], "a")]),
          (("c", "a"), [([2], "c")]),
          (("?n + ?n", "a + b"), [([1], "a + a")]),
          (("?A + ?A", "c + a"), [([2], "c + c")]),
          (("?A + ?A + ?A", "a + b + c"), [([1, 2], "a + a + a")]),
          (("f ?m ?n", "f a b"), [([], "f a b")]),
          (("f ?m ?m", "f c a"), [([2], "f c c")])]
         |> done "test_rewrite"

(* Rewriting from atomic to function application. *)
val test_rewrite2 =
    init |> add_prim_id (1, []) |> add_prim_id (2, [])
         |> declare_term "[a::nat, b, c]"
         |> declare_pat "[?n::nat]"
         |> add_rewrite [1] ("a", "b + c")
         |> add_rewrite [2] ("b", "c")
         |> assert_match (("?n + ?n", "a"), [([1, 2], "b + b")])
         |> done "test_rewrite2"

(* Abstractions. *)
val test_abstraction =
    init |> declare_term "[m::nat, n]"
         |> declare_term "P::(nat => nat => nat)"
         |> declare_pat "?A::(nat => nat => 'a::{plus})"
         |> fold assert_match
         [(("%x y. ?A x y", "%m n. P m n"), [([], "%m n. P m n")]),
          (("%x y. ?A x y + ?A y x", "%m n. P m n + P n m"),
           [([], "%m n. P m n + P n m")]),
          (("%x y. ?A x y", "%x y. (x::nat) + y + y"),
           [([], "%x y. (x::nat) + y + y")])]
         |> done "test_abstraction"

(* Abstractions with rewriting. *)
val test_abstraction_rewrite =
    init |> declare_term "[m::nat, n, p]"
         |> declare_term "P::(nat => nat => nat)"
         |> declare_term "f::(nat => nat => 'a::{plus})"
         |> declare_pat "?A::(nat => ?'a::{plus})"
         |> add_rewrite [] ("m", "n")
         |> add_rewrite [] ("p", "0::nat")
         |> assert_match (("%x. ?A x + ?A x", "%x. P x m + P x n"),
                          [([], "%x. P x m + P x m")])
         |> assert_match (("%x. f x 0", "%x. f x p"), [([], "%x. f x 0")])
         |> done "test_abstraction_rewrite"

(* Test matching of higher order patterns. *)
val test_higher_order =
    init |> declare_term "f::(nat => nat)"
         |> declare_pat "?f::(nat => nat)"
         |> assert_match (("%n. (?f n, ?f (n + 1))", "%n. (f n, f (n + 1))"),
                          [([], "%n. (f n, f (n + 1))")])
         |> assert_match (("%n. (?f (n + 1), ?f n)", "%n. (f (n + 1), f n)"),
                          [([], "%n. (f (n + 1), f n)")])
         |> done "test_higher_order"

(* Test handling of schematic type variables. *)
val test_match_type =
    init |> assert_match (("image_mset ?f {#}", "{#i. i :# {#}#}"),
                          [([], "{#i. i :# {#}#}")])
         |> assert_match (("image_mset ?f {#}", "{#(i::nat). i :# {#}#}"),
                          [([], "{#(i::nat). i :# {#}#}")])
         (* sorted [] has concrete type, but not []. *)
         |> assert_match (("sorted []", "sorted []"), [([], "sorted []")])
         |> done "test_match_type"

(* Test special schematic variable ?NUMC. *)
val test_numc =
    init |> declare_term "[k::int, m]"
         |> add_rewrite [] ("k", "1::int")
         |> assert_match (("?NUMC::int", "k"), [([], "1::int")])
         |> assert_match (("?NUMC", "k"), [([], "1::int")])
         |> assert_match (("?NUMC", "m"), [])
         |> done "test_numc"

(* Test match list. *)
val test_match_list =
    init |> declare_term "[k::nat, l]"
         |> declare_pat "?a::nat"
         |> add_rewrite [] ("k", "l")
         |> assert_match_list ([(false, ("?a", "k")), (false, ("?a", "l"))],
                               [([], ["k", "k"])])
         |> assert_match_list ([(false, ("?a", "k")), (true, ("?a", "l"))], [])
         |> assert_match_list ([(true, ("?a", "k")), (false, ("?a", "l"))],
                               [([], ["k", "k"])])
         |> assert_match_list ([(true, ("?a + b", "k + b")),
                                (true, ("?a + b", "l + b"))],
                               [([], ["k + b", "k + b"])])
         |> done "test_match_list"

(* Test of pre-matcher. *)
fun assert_pre_match_gen res at_head (str_t, str_u) ctxt =
    let
      val (t, cu) = (Proof_Context.read_term_pattern ctxt str_t,
                     Thm.cterm_of ctxt (Syntax.read_term ctxt str_u))
      val pre_match_fn = if at_head then Matcher.pre_match_head
                         else Matcher.pre_match
    in
      if pre_match_fn ctxt (t, cu) = res then ctxt
      else let
        val _ = trace_tlist ctxt "Pattern, term: " [t, Thm.term_of cu]
      in
        raise Fail ("assert_pre_match (expected " ^ (Util.string_of_bool res) ^ ")")
      end
    end

val assert_pre_match = assert_pre_match_gen true false
val assert_not_pre_match = assert_pre_match_gen false false

val test_pre_match =
    init |> declare_term "[m::nat, n]"
         |> declare_term "[a::'a]"
         |> declare_pat "?n::nat"
         |> declare_pat "?a::?'a"
         |> assert_pre_match ("?a", "n")
         |> assert_pre_match ("?n", "n")
         |> assert_not_pre_match ("?n", "a")
         |> assert_not_pre_match ("m", "n")
         |> done "test_pre_match"

val test_pre_match_quant =
    init |> declare_term "[P::(nat => bool), Q]"
         |> declare_term "[S::(nat => nat => bool), T]"
         |> declare_term "[x::nat, y, z]"
         |> assert_pre_match ("ALL x. P x", "ALL y. P y")
         |> assert_not_pre_match ("ALL x. P x", "ALL x. Q x")
         |> assert_pre_match ("ALL x y. S x y", "ALL y z. S y z")
         |> assert_not_pre_match ("ALL x y. S x y", "ALL x y. S y x")
         |> assert_not_pre_match ("ALL x y. S x y", "ALL x y. T x y")
         |> assert_pre_match ("ALL x y. ?S x y", "ALL x y. x < y")
         |> assert_pre_match ("ALL x. x + y = z & ?P x",
                              "ALL x. x + y = z & P x")
         |> done "test_pre_match_quant"

end
