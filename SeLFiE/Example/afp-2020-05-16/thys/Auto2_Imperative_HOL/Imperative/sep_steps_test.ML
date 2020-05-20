(*
  File: sep_steps_test.ML
  Author: Bohua Zhan

  Unit test for sep_steps.ML.
*)

local
  open SepUtil
  val ctxt = @{context}
  val ctxt' = ctxt |> fold Proof_Context.augment [
        Free ("P", assnT), Free ("Q", assnT), Free ("R", assnT),
        Free ("S", natT --> assnT), Free ("T", natT --> assnT)]
in

val test_normalize_assn =
    let
      val test_data = [
        ("P * (Q * R)", "P * Q * R"),
        ("P * \<up>(b)", "P * \<up>(b)"),
        ("\<up>(b) * P", "P * \<up>(b)"),
        ("P * \<up>(b) * Q", "P * Q * \<up>(b)"),
        ("\<up>(b) * (P * \<up>(c)) * Q", "P * Q * \<up>(b) * \<up>(c)"),
        ("EXA x. S x", "EXA x. S x"),
        ("(EXA x. S x) * P", "EXA x. P * S x"),
        ("P * (EXA x. S x)", "EXA x. P * S x"),
        ("(EXA x. S x) * (EXA y. T y)", "EXA x y. S x * T y"),
        ("EXA x. S x * \<up>(B x) * T x", "EXA x. S x * T x * \<up>(B x)"),
        ("P * true * true", "P * true"),
        ("true * P * true", "P * true"),
        ("true * P * true * \<up>(b)", "P * true * \<up>(b)"),
        ("(EXA x. S x) * P * Q", "EXA x. P * Q * S x"),
        ("\<up>(b1 & b2)", "\<up>b1 * \<up>b2")
      ]
    in
      map (Util.test_conv ctxt' (SepUtil.normalize_assn_cv ctxt')
                          "normalize_assn")
          test_data
    end

val test_contract_hoare =
    let
      val test_data = [
        ("<P * \<up>(b)> c <S>", "<P * \<up>(b)> c <S>"),
        ("b --> <P> c <S>", "<P * \<up>(b)> c <S>"),
        ("b1 --> b2 --> <P> c <S>", "<P * \<up>(b2) * \<up>(b1)> c <S>"),
        ("b1 --> <P * \<up>(b2)> c <S>", "<P * \<up>(b2) * \<up>(b1)> c <S>"),
        ("<Q * P> c <S>", "<P * Q> c <S>")
      ]
    in
      map (Util.test_conv ctxt' (SepLogic.contract_hoare_cv ctxt')
                          "contract_hoare")
          test_data
    end

val test_normalize_hoare_goal =
    let
      val test_data = [
        ("~<P> c <S>", "~<P> c <S>"),
        ("~<\<up>(b)> c <S>", "~<emp> c <S> & b"),
        ("~<P * \<up>(b)> c <S>", "~<P> c <S> & b"),
        ("~<\<up>(b1) * \<up>(b2)> c <S>", "(~<emp> c <S> & b1) & b2"),
        ("~<P * Q> c <S>", "~<P * Q> c <S>"),
        ("EX x. ~<T x> c <S>", "EX x. ~<T x> c <S>"),
        ("EX x. ~<\<up>(b x)> c <S>", "EX x. ~<emp> c <S> & b x")
      ]
    in
      map (Util.test_conv ctxt' (SepLogic.normalize_hoare_goal_cv ctxt')
                          "normalize_hoare_goal")
          test_data
    end

val test_normalize_entail_goal =
    let
      val test_data = [
        ("~(entails P Q)", "~(entails P Q)"),
        ("~(entails (\<up>b) Q)", "~(entails emp Q) & b"),
        ("~(entails (\<up>b * P) Q)", "~(entails P Q) & b"),
        ("~(entails (EXA x. S x) Q)", "EX x. ~(entails (S x) Q)")
      ]
    in
      map (Util.test_conv ctxt' (SepLogic.normalize_entail_goal_cv ctxt')
                          "normalize_entail_goal")
          test_data
    end

end
