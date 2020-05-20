(*
  File: list_matcher_test.ML
  Author: Bohua Zhan

  Unit test for matching of assertions on linked lists.
*)

local

  open SepUtil

  val ctxt = @{context}

  fun eq_info_list (l1, l2) =
      length l1 = length l2 andalso
      eq_set (eq_pair (op =) (op aconv)) (l1, l2)

  fun print_term_info ctxt (id, t) =
      "(" ^ (BoxID.string_of_box_id id) ^ ", " ^ (Syntax.string_of_term ctxt t) ^ ")"

  fun print_term_infos ctxt lst =
      commas (map (print_term_info ctxt) lst)

  fun add_rewrite id (str1, str2) ctxt =
      let
        val (t1, t2) = (Syntax.read_term ctxt str1, Syntax.read_term ctxt str2)
        val thy = Proof_Context.theory_of ctxt
        val th = assume_eq thy (t1, t2)
      in
        ctxt |> RewriteTable.add_rewrite (id, th)
      end

  val ts = [@{term "[p::nat node ref option, n1, s1, s2]"},
            @{term "[pp::nat node ref, pp']"},
            @{term "[x::nat]"},
            @{term "[xs::nat list, ys, zs]"}]

  val ctxt' = ctxt |> fold Proof_Context.augment ts
                   |> RewriteTable.add_term ([], Thm.cterm_of ctxt (Free ("P", assnT))) |> snd
                   |> add_rewrite [] ("n1", "None::nat node ref option") |> snd
                   |> add_rewrite [] ("s1", "Some pp") |> snd
                   |> add_rewrite [] ("s2", "Some pp'") |> snd
                   |> add_rewrite [] ("zs", "x # xs") |> snd
in

fun test test_fun str (pat_str, t_str, info_str) =
    let
      val pat = Proof_Context.read_term_pattern ctxt' pat_str
      val t = Syntax.read_term ctxt' t_str
      val ct = Thm.cterm_of ctxt t
      val info = map (apsnd (Syntax.read_term ctxt')) info_str
      val info' = (test_fun ctxt' (pat, ct) ([], fo_init)) |> map (apsnd prop_of')
      val infol = info' |> map snd |> map dest_arg1
      val infor = info' |> map (fn ((id, _), t) => (id, dest_arg t))
    in
      if forall (fn t' => t' aconv t) infol andalso
         eq_info_list (info, infor) then ()
      else let
        val _ = tracing ("Expected: " ^ print_term_infos ctxt' info)
        val _ = tracing ("Actual: " ^ print_term_infos ctxt' infor)
      in
        raise Fail str
      end
    end

val test_assn_term_matcher =
    let
      val test_data = [
        ("os_list ?xs n1", "emp", [([], "os_list [] n1 * emp")]),
        ("os_list ?xs n1", "sngr_assn a 1",
         [([], "os_list [] n1 * sngr_assn a 1")]),
        ("os_list ?xs s1", "sngr_assn pp (Node x r) * os_list xs r",
         [([], "os_list (x # xs) s1 * emp")]),
        ("os_list (?x # ?xs) s1", "sngr_assn pp (Node x r) * os_list xs r",
         [([], "os_list (x # xs) s1 * emp")]),
        ("os_list ys s1", "sngr_assn pp (Node x r) * os_list xs r", []),
        ("os_list zs s1", "sngr_assn pp (Node x r) * os_list xs r",
         [([], "os_list zs s1 * emp")]),
        ("os_list zs s1",
         "sngr_assn pp (Node x r) * os_list xs r * os_list ys p",
         [([], "os_list zs s1 * os_list ys p")])
      ]
    in
      map (test AssnMatcher.assn_match_term "test_assn_term_matcher") test_data
    end

val test_list_prop_matcher =
    let
      val test_data = [
        ("os_list ?xs s1", "sngr_assn pp (Node x r) * os_list xs r",
         [([], "os_list (x # xs) s1")]),
        ("os_list zs s1", "sngr_assn pp (Node x r) * os_list xs r",
         [([], "os_list zs s1")]),
        ("os_list ?xs p * os_list ?ys q", "os_list ys q * os_list xs p",
         [([], "os_list xs p * os_list ys q")]),
        ("os_list ?xs p", "os_list xs p * os_list ys q", []),
        ("sngr_assn a 1", "sngr_assn a 1", [([], "sngr_assn a 1")]),
        ("sngr_assn ?a 1 * os_list ?ys q * os_list ?zs r",
         "os_list ys q * os_list zs r * sngr_assn a 1",
         [([], "sngr_assn a 1 * os_list ys q * os_list zs r")])
      ]
    in
      map (test AssnMatcher.assn_match_strict "test_list_prop_matcher") test_data
    end

end
