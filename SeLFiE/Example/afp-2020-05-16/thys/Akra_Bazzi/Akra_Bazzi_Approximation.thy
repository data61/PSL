theory Akra_Bazzi_Approximation
imports
  Complex_Main
  Akra_Bazzi_Method
  "HOL-Decision_Procs.Approximation"
begin

(* 
  This is a temporary workaround since recent changes broke approximation of the "powr" function. 
  Once it works again, this entire section can be removed.
*)

context akra_bazzi_params_nonzero
begin

lemma sum_alt: "(\<Sum>i<k. as!i * bs!i powr p') = (\<Sum>i<k. as!i * exp (p' * ln (bs!i)))"
proof (intro sum.cong)
  fix i assume "i \<in> {..<k}"
  with b_bounds have "bs!i > 0" by simp
  thus "as!i * bs!i powr p' = as!i * exp (p' * ln (bs!i))" by (simp add: powr_def)
qed simp

lemma akra_bazzi_p_rel_intros_aux:
  "1 < (\<Sum>i<k. as!i * exp (p' * ln (bs!i))) \<Longrightarrow> p' < p"
  "1 > (\<Sum>i<k. as!i * exp (p' * ln (bs!i))) \<Longrightarrow> p' > p"
  "1 \<le> (\<Sum>i<k. as!i * exp (p' * ln (bs!i))) \<Longrightarrow> p' \<le> p"
  "1 \<ge> (\<Sum>i<k. as!i * exp (p' * ln (bs!i))) \<Longrightarrow> p' \<ge> p"
  "(\<Sum>i<k. as!i * exp (x * ln (bs!i))) \<le> 1 \<and> (\<Sum>i<k. as!i * exp (y * ln (bs!i))) \<ge> 1 \<Longrightarrow> p \<in> {y..x}"
  "(\<Sum>i<k. as!i * exp (x * ln (bs!i))) < 1 \<and> (\<Sum>i<k. as!i * exp (y * ln (bs!i))) > 1 \<Longrightarrow> p \<in> {y<..<x}"
  using p_lessI p_greaterI p_leI p_geI p_boundsI p_boundsI' by (simp_all only: sum_alt)
end

lemmas akra_bazzi_p_rel_intros_exp = 
  akra_bazzi_params_nonzero.akra_bazzi_p_rel_intros_aux[rotated, OF _ akra_bazzi_params_nonzeroI]

lemma eval_akra_bazzi_sum:
  "(\<Sum>i<0. as!i * exp (x * ln (bs!i))) = 0"
  "(\<Sum>i<Suc 0. (a#as)!i * exp (x * ln ((b#bs)!i))) = a * exp (x * ln b)"
  "(\<Sum>i<Suc k. (a#as)!i * exp (x * ln ((b#bs)!i))) = a * exp (x * ln b) + 
      (\<Sum>i<k. as!i * exp (x * ln (bs!i)))"
  apply simp
  apply simp
  apply (induction k arbitrary: a as b bs)
  apply simp_all
  done

(* end workaround *)


ML \<open>
signature AKRA_BAZZI_APPROXIMATION =
sig
  val akra_bazzi_approximate_tac : int -> Proof.context -> int -> tactic
end

structure Akra_Bazzi_Approximation: AKRA_BAZZI_APPROXIMATION =
struct

fun akra_bazzi_approximate_tac prec ctxt =
  let 
    val simps = @{thms eval_length eval_akra_bazzi_sum add_0_left add_0_right 
                       mult_1_left mult_1_right}
  in
    SELECT_GOAL (
      resolve_tac ctxt @{thms akra_bazzi_p_rel_intros_exp} 1
      THEN ALLGOALS (fn i => 
        if i > 1 then 
          SELECT_GOAL (
            Local_Defs.unfold_tac ctxt 
              @{thms bex_set_simps ball_set_simps greaterThanLessThan_iff eval_length}
            THEN TRY (SOLVE (Eval_Numeral.eval_numeral_tac ctxt 1))
          ) i
        else 
          SELECT_GOAL (Local_Defs.unfold_tac ctxt simps) i
          THEN Approximation.approximation_tac prec [] NONE ctxt i
      ) 
    )
  end
   
end;
\<close>

method_setup akra_bazzi_approximate = \<open>
  Scan.lift Parse.nat >> 
    (fn prec => fn ctxt => 
      SIMPLE_METHOD' (Akra_Bazzi_Approximation.akra_bazzi_approximate_tac prec ctxt))
\<close> "approximate transcendental Akra-Bazzi parameters"

end
