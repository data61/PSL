
(* Author: Florian Haftmann, TU Muenchen *)

section \<open>A barebone conversion for discrete summation\<close>

theory Summation_Conversion
imports Factorials Discrete_Summation
begin

text \<open>Extensible theorem collection for solving summation problems\<close>

named_theorems summation "rules for solving summation problems"

declare
  \<Sigma>_const [summation] \<Sigma>_add [summation]
  \<Sigma>_factor [summation] monomial_ffact [summation]

lemma intervall_simps [summation]:
  "(\<Sum>k::nat = 0..0. f k) = f 0"
  "(\<Sum>k::nat = 0..Suc n. f k) = f (Suc n) + (\<Sum>k::nat = 0..n. f k)"
  by (simp_all add: add.commute)

lemma \<Delta>_ffact:
  "\<Delta> (ffact (Suc n)) k = of_nat (Suc n) * ffact n (of_int k :: 'a :: comm_ring_1)"
proof (induct n)
  case 0 then show ?case
    by (simp add: \<Delta>_def ffact_Suc)
next
  case (Suc n)
  obtain m where "m = Suc n" by blast
  have "\<Delta> (ffact (Suc m)) k =
    ffact (Suc m) (of_int (k + 1)) - ffact (Suc m) (of_int k :: 'a)" 
    by (simp add: \<Delta>_def)
  also have "\<dots> = of_int (k + 1) * ffact m (of_int k)
    - (ffact m (of_int k) * (of_int k - of_nat m))"
    using ffact_Suc_rev [of m "(of_int k :: 'a :: comm_ring_1)"]
    by (simp add: ac_simps ffact_Suc)
  also have "\<dots> = (of_int k + 1 - of_int k + of_nat m) * ffact m (of_int k)"
    by (simp add: algebra_simps)
  also have "\<dots> = of_nat (Suc m) * ffact m (of_int k)" by simp
  also have "\<dots> = of_nat (Suc m) * ffact (Suc m - 1) (of_int k)" by simp
  finally show ?case by (simp only: \<open>m = Suc n\<close> diff_Suc_1)
qed

lemma \<Sigma>_ffact_divide [summation]:
  "\<Sigma> (ffact n) j l =
    (ffact (Suc n) (of_int l :: 'a :: {idom_divide, semiring_char_0}) - ffact (Suc n) (of_int j)) div of_nat (Suc n)"
proof -
  have *: "(of_nat (Suc n) * \<Sigma> (ffact n) j l) div of_nat (Suc n) = (\<Sigma> (ffact n) j l :: 'a)"
    using of_nat_neq_0 [where ?'a = 'a] by simp
  have "ffact (Suc n) (of_int l :: 'a) - ffact (Suc n) (of_int j) =
    \<Sigma> (\<lambda>k. \<Delta> (ffact (Suc n)) k) j l"
    by (simp add: \<Sigma>_\<Delta>)
  also have "\<dots> = \<Sigma> (\<lambda>k. of_nat (Suc n) * ffact n (of_int k)) j l"
    by (simp add: \<Delta>_ffact)
  also have "\<dots> = of_nat (Suc n) * \<Sigma> (ffact n \<circ> of_int) j l"
    by (simp add: \<Sigma>_factor comp_def)
  finally show ?thesis by (simp only: \<Sigma>_comp_of_int * of_nat_eq_0_iff)
qed


text \<open>Various other rules\<close>

lemma of_int_coeff:
  "(of_int l :: 'a::comm_ring_1) * numeral k = of_int (l * numeral k)"
  by simp

lemmas nat_simps =
  add_0_left add_0_right add_Suc add_Suc_right
  mult_Suc mult_Suc_right mult_zero_left mult_zero_right
  One_nat_def of_nat_simps

lemmas of_int_pull_out =
  of_int_add [symmetric] of_int_diff [symmetric] of_int_mult [symmetric]
  of_int_coeff

lemma of_nat_coeff:
  "(of_nat n :: 'a::comm_semiring_1) * numeral m = of_nat (n * numeral m)"
  by (induct n) simp_all
  
lemmas of_nat_pull_out =
  of_nat_add [symmetric] of_nat_mult [symmetric] of_nat_coeff

lemmas nat_pull_in =
  nat_int_add

lemmas of_int_pull_in =
  of_int_pull_out [symmetric] add_divide_distrib diff_divide_distrib of_int_power
  of_int_numeral of_int_neg_numeral times_divide_eq_left [symmetric]

  
text \<open>Special for @{typ nat}\<close>

definition lift_nat :: "(nat \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> int"
where
  "lift_nat f = int \<circ> f \<circ> nat"

definition \<Sigma>_nat :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" ("\<Sigma>\<^sub>\<nat>")
where
  [summation]: "\<Sigma>\<^sub>\<nat> f m n = nat (\<Sigma> (lift_nat f) (int m) (int n))"  

definition pos_id :: "int \<Rightarrow> int"
where
  "pos_id k = (if k < 0 then 0 else k)"

lemma \<Sigma>_pos_id [summation]:
  "0 \<le> k \<Longrightarrow> 0 \<le> l \<Longrightarrow> \<Sigma> (\<lambda>r. f (pos_id r)) k l = \<Sigma> f k l"
  by (simp add: \<Sigma>_def pos_id_def)

lemma [summation]:
  "(0::int) \<le> 0"
  "(0::int) \<le> 1"
  "(0::int) \<le> numeral m"
  "(0::int) \<le> int n"
  by simp_all
  
lemma [summation]:
  "lift_nat (\<lambda>n. m) = (\<lambda>k. int m)"
  by (simp add: lift_nat_def fun_eq_iff)

lemma [summation]:
  "lift_nat (\<lambda>n. n) = pos_id"
  by (simp add: lift_nat_def fun_eq_iff pos_id_def)

lemma [summation]:
  "lift_nat (\<lambda>n. f n + g n) = (\<lambda>k. lift_nat f k + lift_nat g k)"
  by (simp add: lift_nat_def fun_eq_iff)

lemma [summation]:
  "lift_nat (\<lambda>n. m * f n) = (\<lambda>k. int m * lift_nat f k)"
  by (simp add: lift_nat_def fun_eq_iff)

lemma [summation]:
  "lift_nat (\<lambda>n. f n * m) = (\<lambda>k. lift_nat f k * int m)"
  by (simp add: lift_nat_def fun_eq_iff)

lemma [summation]:
  "lift_nat (\<lambda>n. f n ^ m) = (\<lambda>k. lift_nat f k ^ m)"
  by (simp add: lift_nat_def fun_eq_iff)

  
text \<open>Generic conversion\<close>  

ML \<open>
signature SUMMATION =
sig
  val conv: Proof.context -> conv
end

structure Summation : SUMMATION =
struct

val simps2 = @{thms Stirling.simps ffact_0 ffact_Suc nat_simps};
val simpset3 =
  @{context}
  |> fold Simplifier.add_simp @{thms field_simps}
  |> Simplifier.simpset_of;
val simps4 = @{thms of_int_pull_out of_nat_pull_out nat_pull_in};
val simps6 = @{thms of_int_pull_in};

fun conv ctxt =
  let
    val ctxt1 =
      ctxt
      |> put_simpset HOL_basic_ss
      |> fold Simplifier.add_simp (Named_Theorems.get ctxt @{named_theorems summation})
    val ctxt2 =
      ctxt
      |> put_simpset HOL_basic_ss
      |> fold Simplifier.add_simp simps2
    val ctxt3 =
      ctxt
      |> put_simpset simpset3
    val ctxt4 =
      ctxt
      |> put_simpset HOL_basic_ss
      |> fold Simplifier.add_simp simps4
    val semiring_conv_base = Semiring_Normalizer.semiring_normalize_conv ctxt
    val semiring_conv = Conv.arg_conv (Conv.arg1_conv (Conv.arg_conv semiring_conv_base))
      else_conv Conv.arg1_conv (Conv.arg_conv semiring_conv_base)
      else_conv semiring_conv_base
    val ctxt6 =
      ctxt
      |> put_simpset HOL_basic_ss
      |> fold Simplifier.add_simp simps6
  in
     Simplifier.rewrite ctxt1
     then_conv Simplifier.rewrite ctxt2
     then_conv Simplifier.rewrite ctxt3
     then_conv Simplifier.rewrite ctxt4
     then_conv semiring_conv
     then_conv Simplifier.rewrite ctxt6
  end

end
\<close>

hide_fact (open) nat_simps of_int_pull_out of_int_pull_in

end
