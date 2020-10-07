(*
  File: normalize_test.ML
  Author: Bohua Zhan

  Unit test for normalizer.ML.
*)

local

  val ts = map (fn x => Free (x, boolT)) ["A", "B", "C"]
  val ctxt = fold Util.declare_free_term ts @{context}

in

val test_normalize =
    let
      fun test (str, strs) =
          let
            val t = Syntax.read_term ctxt str
            val ts = map (Syntax.read_term ctxt) strs
            val ritem =
                Update.thm_to_ritem (Util.assume_thm ctxt (mk_Trueprop t))
            val ritems' = Normalizer.normalize ctxt ritem
            val ts' = map (dest_Trueprop o Thm.prop_of o BoxItem.get_thm_raw)
                          ritems'
          in
            if length ts = length ts' andalso
               eq_set (op aconv) (ts, ts') then ()
            else let
              val _ = trace_t ctxt "Input:" t
              val _ = trace_tlist ctxt "Expected:" ts
              val _ = trace_tlist ctxt "Actual:" ts'
            in
              raise Fail "test_normalize"
            end
          end

      val test_data = [
        ("A & B & C", ["A", "B", "C"]),
        ("~ (A | B | C)", ["~ A", "~ B", "~ C"]),
        ("~ ~ (~ A & (~ ~ B))", ["~ A", "B"])
      ]
    in
      map test test_data
    end

val test_use_vardefs =
    let
      fun test (s1, s2) =
          let
            val (t1, t2) = the_pair (Syntax.read_terms ctxt [s1, s2])
            val t2 = if fastype_of t2 = propT then t2 else mk_Trueprop t2

            val th1 = t1 |> mk_Trueprop |> Thm.cterm_of ctxt |> Thm.assume
                         |> apply_to_thm (UtilLogic.to_meta_conv ctxt)
                         |> Util.forall_elim_sch
            val (_, th2) = Normalizer.meta_use_vardefs th1
          in
            if Thm.prop_of th2 aconv t2 then ()
            else let
              val _ = trace_t ctxt "Input:" t1
              val _ = trace_t ctxt "Expected:" t2
              val _ = trace_t ctxt "Actual:" (Thm.prop_of th2)
            in
              raise Fail "test_use_vardefs"
            end
          end

      val test_data = [
        ("!s. s = f x --> P s", "P (f x)"),
        ("!s t. s = f x --> t = g x --> P s t", "P (f x) (g x)"),
        ("!s t. x < y --> s = f x --> t = g y --> P s t",
         "x < y ==> P (f x) (g y)"),
        ("!s. ~s = f x | P s", "P (f x)"),
        ("!s t. ~s = f x | ~t = g x | P s t", "P (f x) (g x)"),
        ("!s t. ~x < y | ~s = f x | ~t = g y | P s t", "~x < y | P (f x) (g y)"),
        ("!s. P s | ~s = f x", "P (f x)"),

        ("!a b. (a,b) = c --> P a b", "P (fst c) (snd c)"),
        ("!a b. (a,b) ~= c | P a b", "P (fst c) (snd c)"),
        ("!a b c. (a,(b,c)) = d --> P a b c",
         "P (fst d) (fst (snd d)) (snd (snd d))"),
        ("!a b c. ((a,b),c) = d --> P a b c",
         "P (fst (fst d)) (snd (fst d)) (snd d)")
      ]
    in
      map test test_data
    end

end  (* local *)
