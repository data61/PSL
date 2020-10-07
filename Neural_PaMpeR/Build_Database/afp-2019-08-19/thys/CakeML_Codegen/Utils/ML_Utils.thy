theory ML_Utils
imports
  "HOL-Library.FSet"
  "Dict_Construction.Dict_Construction"
begin

ML_file "utils.ML"

ML\<open>
fun econtr_tac neg_thms ctxt =
  let
    val neg_thms = map (fn thm => @{thm notE} OF [thm]) neg_thms
  in SOLVED' (eresolve_tac ctxt neg_thms) end

(* from HOL.thy *)
fun eval_tac ctxt =
  let val conv = Code_Runtime.dynamic_holds_conv ctxt
  in
    CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1 conv)) ctxt) THEN'
    resolve_tac ctxt [TrueI]
  end
\<close>

lemma norm_all_conjunction:
  "\<And>P Q. ((\<And>x. PROP P x) &&& PROP Q) \<equiv> (\<And>x. PROP P x &&& PROP Q)"
  "\<And>P Q. (PROP P &&& (\<And>x. PROP Q x)) \<equiv> (\<And>x. PROP P &&& PROP Q x)"
proof -
  show "((\<And>x. PROP P x) &&& PROP Q) \<equiv> (\<And>x. PROP P x &&& PROP Q)" for P Q
    proof
      fix x
      assume "(\<And>x. PROP P x) &&& PROP Q"
      note Pure.conjunctionD1[OF this, rule_format] Pure.conjunctionD2[OF this]
      thus "PROP P x &&& PROP Q" .
    next
      assume "(\<And>x. PROP P x &&& PROP Q)"
      note Pure.conjunctionD1[OF this] Pure.conjunctionD2[OF this]
      thus "(\<And>x. PROP P x) &&& PROP Q" .
    qed
next
  show "(PROP P &&& (\<And>x. PROP Q x)) \<equiv> (\<And>x. PROP P &&& PROP Q x)" for P Q
    proof
      fix x
      assume "PROP P &&& (\<And>x. PROP Q x)"
      note Pure.conjunctionD1[OF this] Pure.conjunctionD2[OF this, rule_format]
      thus "PROP P &&& PROP Q x" .
    next
      assume "(\<And>x. PROP P &&& PROP Q x)"
      note Pure.conjunctionD1[OF this] Pure.conjunctionD2[OF this]
      thus "PROP P &&& (\<And>x. PROP Q x)" .
    qed
qed

ML\<open>
fun norm_all_conjunction_tac ctxt =
  CONVERSION (repeat1_conv (Dict_Construction_Util.changed_conv (Conv.top_sweep_conv
    (K (Conv.rewrs_conv @{thms norm_all_conjunction})) ctxt)))
\<close>

end