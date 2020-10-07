(*
  File: util_test.ML
  Author: Bohua Zhan

  Unit test for util.ML.
*)

local

  val ctxt = @{context}

in

val test_normalize_meta_all_imp =
    let
      val test_data = [
        ("!!x. (A ==> B x)", "A ==> (!!x. B x)")
      ]
    in
      map (Util.test_conv ctxt (Util.normalize_meta_all_imp ctxt)
                          "normalize_meta_all_imp") test_data
    end

val test_to_obj_conv =
    let
      fun err n = "test_to_obj_conv: " ^ (string_of_int n)
      fun assert_eq th ct txt =
          let val ct' = Thm.rhs_of th
          in if ct' aconvc ct then () else raise Fail txt end
      val ct1 = @{cprop "A ==> B ==> (!!(n::nat). C n) ==> D"}
      val ct2 = @{cprop "A --> B --> (!(n::nat). C n) --> D"}
      val ct3 = @{cprop "!(y::nat) (x::nat). P x y --> (!z. Q x y z)"}
      val _ = assert_eq (UtilLogic.to_obj_conv ctxt ct1) ct2 (err 0)
      val _ = assert_eq (UtilLogic.to_meta_conv ctxt ct2)
              @{cprop "A ==> B ==> (!(n::nat). C n) ==> D"} (err 1)
      val _ = assert_eq (UtilLogic.to_meta_conv ctxt ct3)
              @{cprop "!!(y::nat) (x::nat) z. P x y ==> Q x y z"} (err 2)
      val _ = assert_eq (UtilLogic.to_obj_conv_on_horn ctxt ct1)
              @{cprop "A ==> B ==> (!(n::nat). C n) ==> D"} (err 4)
    in () end

val test_is_pattern =
    let
      fun test b str =
          let
            val t = Proof_Context.read_term_pattern ctxt str
          in
            if b = Util.is_pattern t then ()
            else raise Fail "test_is_pattern"
          end

      val test_positive = ["?f", "!n. ?f n", "!m n. ?f m n",
                           "!n. ?f n < ?f (n + 1)",
                           "!n. ?f (n + 1) < ?f n", "!n. ?g (?f n) & ?g n"]
      val test_negative = ["?f ?n", "!n. ?f n n", "!n. ?f (?f n)",
                           "!n. (?f n < ?g (n + 1)) & (?f (n + 1) < ?g n)"]
    in
      map (test true) test_positive @ map (test false) test_negative
    end

end
