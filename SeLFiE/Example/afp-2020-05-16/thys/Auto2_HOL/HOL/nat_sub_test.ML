(*
  File: nat_sub_test.ML
  Author: Bohua Zhan

  Unit test for nat_sub.ML.
*)

local

  val ts = map (fn x => Free (x, natT)) ["a", "b", "c", "m", "n"]
  val ctxt = fold Util.declare_free_term ts @{context}

in

fun test_term ctxt f err_str (str1, str2) =
    let
      val (t1, t2) = (Proof_Context.read_term_pattern ctxt str1,
                      Proof_Context.read_term_pattern ctxt str2)
      val t2' = f (Thm.cterm_of ctxt t1)
    in
      if t2 aconv t2' then ()
      else let
        val _ = trace_t ctxt "Input:" t1
        val _ = trace_t ctxt "Expected:" t2
        val _ = trace_t ctxt "Actual:" t2'
      in
        raise Fail err_str
      end
    end

val test =
    let
      val test_data = [
        (* No repeated terms. *)
        ("a", "a"),
        ("a + b", "a + b"),
        ("a - b", "a - b"),
        ("a - b + c", "a + c - b"),
        ("a - b - c", "a - (b + c)"),
        ("a - b + (c - d)", "a + c - (b + d)"),
        ("a - b - (c - d)", "a + d - (b + c)"),
        ("a + b + c - d - e - f", "a + b + c - (d + e + f)"),
        ("a - b + c - d + e - f", "a + c + e - (b + d + f)"),

        (* Numerical constants (on one side only). *)
        ("0::nat", "0::nat"),
        ("2::nat", "2::nat"),
        ("a + 2 + 3", "a + 5"),
        ("a - b - 2 - 3", "a - (b + 5)"),
        ("2 + 3 + a", "a + 5"),
        ("a - 2 - b - 3", "a - (b + 5)"),
        ("0 + a - 0 - b", "a - b"),

        (* Cancellation needed. *)
        ("a - a", "(0::nat)"),
        ("a - 0", "a"),
        ("a + b - a", "b"),
        ("a - (a - a)", "a"),
        ("a + b - a - c", "b - c"),
        ("a + b - a - b", "0::nat"),
        ("a + b + c - a - b", "c"),
        ("c + (b + (b + a - b) - b)", "a + c"),

        (* Cancellation of constants needed. *)
        ("a + 5 - b - 3", "a + 2 - b"),
        ("a + 3 - b - 5", "a - (b + 2)"),
        ("a + 5 - b - 5", "a - b"),
        ("a - 5 - (b - 3)", "a - (b + 2)"),
        ("a - 3 - (b - 5)", "(a + 2) - b"),
        ("a + 5 - 3", "a + 2"),
        ("a - 5 + 3", "a - 2"),
        ("5 - a - 3", "2 - a"),
        ("3 - a - 3", "0 - a"),
        ("(5::nat) - 3", "2::nat"),
        ("(3::nat) - 3", "0::nat"),

        (* Monomial *)
        ("a * 3", "a * 3"),
        ("a * b + b * a", "a * b * 2"),

        (* Cancellation between terms *)
        ("a * 3 + a * 2", "a * 5"),
        ("a * 3 - a * 2", "a"),
        ("a * 3 + b - a * 2", "a + b"),
        ("a * 2 + b - a * 3", "b - a"),
        ("a * 2 + b * 3 - a * 3 - b * 2", "b - a"),
        ("a * 3 - a * 2 - a", "0::nat"),

        (* Distributivity *)
        ("(a + 2) * b", "b * 2 + a * b"),
        ("(a + 2) * 2", "a * 2 + 4"),
        ("(a - 2) * b", "a * b - b * 2"),
        ("(a - 2) * 2", "a * 2 - 4"),
        ("(a + 1) * (a - 1)", "a * a - 1"),
        ("(a + 3) * (a - 2)", "a + a * a - 6"),
        ("(a - 1) * (a - 1)", "a * a + 1 - a * 2")
      ]
    in
      map (WfTerm.test_wfconv ctxt NatSub.fheads NatSub.norm_minus "test") test_data @
      map (test_term ctxt NatSub.norm_ring_term "test_t") test_data
    end

end
