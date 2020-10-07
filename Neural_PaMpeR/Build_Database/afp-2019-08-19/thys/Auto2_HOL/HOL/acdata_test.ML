(*
  File: acdata_test.ML
  Author: Bohua Zhan

  Unit test for acdata.ML.
*)

local
  val thy = @{theory}
  val ctxt = @{context}
in

val test_comb_ac_equiv =
    let
      fun err n = "test_comb_ac_equiv: " ^ (string_of_int n)
      fun test n (t1, t2) =
          let
            val ac_info = the (ACUtil.get_head_ac_info thy t1)
                          handle Option.Option =>
                                 raise Fail "test_comb_ac_equiv: ac_info"
            val ts1 = ACUtil.dest_ac ac_info t1
            val ts2 = ACUtil.dest_ac ac_info t2
            fun eq (t1', t2') =
                Thm.assume (Thm.global_cterm_of thy (Logic.mk_equals (t1', t2')))
            val eqs = map eq (ts1 ~~ ts2)
            val th = ACUtil.comb_ac_equiv ac_info eqs
          in
            if Thm.prop_of th aconv Logic.mk_equals (t1, t2) then ()
            else raise Fail (err n)
          end
      val _ = test 0 (@{term "(a::nat) + b + c"}, @{term "(d::nat) + e + f"})
    in () end

(* Generic function for testing conv with ac_info argument. *)
fun test_ac_conv ctxt cv err_str (str1, str2) =
    let
      val t1 = Proof_Context.read_term_pattern ctxt str1
    in
      case ACUtil.get_head_ac_info thy t1 of
          NONE =>
          let
            val _ = trace_t ctxt "t1:" t1
          in
            raise Fail "test_ac_conv: ac_info"
          end
        | SOME ac_info => Util.test_conv ctxt (cv ac_info) err_str (str1, str2)
    end

val test_normalize_assoc =
    let
      val test_data = [
        ("(a::nat) + (b + d) + (c + e)", "(a::nat) + b + d + c + e"),
        ("((a::nat) + 0) + (b + 0)", "(a::nat) + 0 + b + 0")
      ]
    in
      map (test_ac_conv ctxt ACUtil.normalize_assoc "test_normalize_assoc") test_data
    end

val test_move_outmost =
    let
      val err_str = "test_move_outmost"
      fun test (stru, (str1, str2)) =
          let
            val (t1, u) = (Proof_Context.read_term_pattern ctxt str1,
                           Proof_Context.read_term_pattern ctxt stru)
            val ac_info =
                the (ACUtil.get_head_ac_info thy t1)
                handle Option.Option => raise Fail (err_str ^ ": ac_info")
          in
            Util.test_conv ctxt (ACUtil.move_outmost ac_info u) err_str (str1, str2)
          end
      val test_data = [
        ("a::nat", ("(a::nat) + b", "(b::nat) + a")),
        ("a::nat", ("(a::nat) + b + c", "(b::nat) + c + a")),
        ("a::nat", ("(b::nat) + a", "(b::nat) + a")),
        ("a::nat", ("(b::nat) + a + c", "(b::nat) + c + a"))
      ]
    in
      map test test_data
    end

end;  (* local *)
