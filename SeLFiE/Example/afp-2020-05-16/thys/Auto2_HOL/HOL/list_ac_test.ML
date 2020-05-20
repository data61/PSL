(*
  File: list_ac_test.ML
  Author: Bohua Zhan

  Unit test for list_ac.ML.
*)

local

  val ts = map (fn x => Free (x, @{typ "nat list"})) ["xs"]
  val ctxt = fold Util.declare_free_term ts @{context}
  val T = @{typ nat}

in

fun test_norm_t err_str (str1, str2) =
    let
      val (t1, t2) = apply2 (Syntax.read_term ctxt) (str1, str2)
      val (ct1, ct2) = apply2 (Thm.cterm_of ctxt) (t1, t2)
      val ts1 = List_AC.dest_list_full ctxt T ct1
      val ts2 = List_AC.dest_list_full ctxt T ct2
    in
      if eq_list (op aconvc) (ts1, ts2) then ()
      else let
        val _ = trace_tlist ctxt "Inputs" [t1, t2]
        val _ = trace_tlist ctxt "ts1" (map Thm.term_of ts1)
        val _ = trace_tlist ctxt "ts2" (map Thm.term_of ts2)
      in
        raise Fail err_str
      end
    end

val test =
    let
      val test_data = [
        ("xs @ ys", "xs @ ys"),
        ("a # xs", "[a] @ xs"),
        ("[] @ xs", "xs"),
        ("xs @ []", "xs"),
        ("xs @ ys @ zs @ []", "xs @ ys @ zs"),
        ("(xs @ ys @ zs) @ []", "xs @ ys @ zs")
      ]
    in
      map (Util.test_conv ctxt (List_AC.normalize_list T) "test") test_data @
      map (test_norm_t "test_norm") test_data
    end

end
