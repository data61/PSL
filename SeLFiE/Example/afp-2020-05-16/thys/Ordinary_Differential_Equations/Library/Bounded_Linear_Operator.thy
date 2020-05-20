section \<open>Bounded Linear Operator\<close>
theory Bounded_Linear_Operator
imports
  "HOL-Analysis.Analysis"
begin

typedef (overloaded) 'a blinop = "UNIV::('a, 'a) blinfun set"
by simp

setup_lifting type_definition_blinop

lift_definition blinop_apply::"('a::real_normed_vector) blinop \<Rightarrow> 'a \<Rightarrow> 'a" is blinfun_apply .
lift_definition Blinop::"('a::real_normed_vector \<Rightarrow> 'a) \<Rightarrow> 'a blinop" is Blinfun .

no_notation vec_nth (infixl "$" 90)
notation blinop_apply (infixl "$" 999)
declare [[coercion "blinop_apply :: ('a::real_normed_vector) blinop \<Rightarrow> 'a \<Rightarrow> 'a"]]

instantiation blinop :: (real_normed_vector) real_normed_vector
begin

lift_definition norm_blinop :: "'a blinop \<Rightarrow> real" is norm .

lift_definition minus_blinop :: "'a blinop \<Rightarrow> 'a blinop \<Rightarrow> 'a blinop" is minus .

lift_definition dist_blinop :: "'a blinop \<Rightarrow> 'a blinop \<Rightarrow> real" is dist .

definition uniformity_blinop :: "('a blinop \<times> 'a blinop) filter" where
  "uniformity_blinop = (INF e\<in>{0<..}. principal {(x, y). dist x y < e})"

definition open_blinop :: "'a blinop set \<Rightarrow> bool" where
  "open_blinop U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"

lift_definition uminus_blinop :: "'a blinop \<Rightarrow> 'a blinop" is uminus .

lift_definition zero_blinop :: "'a blinop" is 0 .

lift_definition plus_blinop :: "'a blinop \<Rightarrow> 'a blinop \<Rightarrow> 'a blinop" is plus .

lift_definition scaleR_blinop::"real \<Rightarrow> 'a blinop \<Rightarrow> 'a blinop" is scaleR .

lift_definition sgn_blinop :: "'a blinop \<Rightarrow> 'a blinop" is sgn .

instance
  apply standard
  apply (transfer', simp add: algebra_simps sgn_div_norm open_uniformity norm_triangle_le
    uniformity_blinop_def dist_norm
    open_blinop_def)+
  done
end


lemma bounded_bilinear_blinop_apply: "bounded_bilinear ($)"
  unfolding bounded_bilinear_def
  by transfer (simp add: blinfun.bilinear_simps blinfun.bounded)

interpretation blinop: bounded_bilinear "($)"
  by (rule bounded_bilinear_blinop_apply)

lemma blinop_eqI: "(\<And>i. x $ i = y $ i) \<Longrightarrow> x = y"
  by transfer (rule blinfun_eqI)

lemmas bounded_linear_apply_blinop[intro, simp] = blinop.bounded_linear_left
declare blinop.tendsto[tendsto_intros]
declare blinop.FDERIV[derivative_intros]
declare blinop.continuous[continuous_intros]
declare blinop.continuous_on[continuous_intros]

instance blinop :: (banach) banach
  apply standard
  unfolding convergent_def LIMSEQ_def Cauchy_def
  apply transfer
  unfolding convergent_def[symmetric] LIMSEQ_def[symmetric] Cauchy_def[symmetric]
    Cauchy_convergent_iff
  .

instance blinop :: (euclidean_space) heine_borel
  apply standard
  unfolding LIMSEQ_def bounded_def
  apply transfer
  unfolding LIMSEQ_def[symmetric] bounded_def[symmetric]
  apply (rule bounded_imp_convergent_subsequence)
  .

instantiation blinop::("{real_normed_vector, perfect_space}") real_normed_algebra_1
begin

lift_definition one_blinop::"'a blinop" is id_blinfun .
lemma blinop_apply_one_blinop[simp]: "1 $ x = x"
  by transfer simp

lift_definition times_blinop :: "'a blinop \<Rightarrow> 'a blinop \<Rightarrow> 'a blinop" is blinfun_compose .

lemma blinop_apply_times_blinop[simp]: "(f * g) $ x = f $ (g $ x)"
  by transfer simp

instance
proof
  from not_open_singleton[of "0::'a"] have "{0::'a} \<noteq> UNIV" by force
  then obtain x :: 'a where "x \<noteq> 0" by auto
  show "0 \<noteq> (1::'a blinop)"
    apply transfer
    apply transfer
    apply (auto dest!: fun_cong[where x=x] simp: \<open>x \<noteq> 0\<close>)
    done
qed (transfer, transfer,
  simp add: o_def linear_simps onorm_compose onorm_id onorm_compose[simplified o_def])+
end

lemmas bounded_bilinear_bounded_uniform_limit_intros[uniform_limit_intros] =
  bounded_bilinear.bounded_uniform_limit[OF Bounded_Linear_Operator.bounded_bilinear_blinop_apply]
  bounded_bilinear.bounded_uniform_limit[OF Bounded_Linear_Function.bounded_bilinear_blinfun_apply]
  bounded_bilinear.bounded_uniform_limit[OF Bounded_Linear_Operator.blinop.flip]
  bounded_bilinear.bounded_uniform_limit[OF Bounded_Linear_Function.blinfun.flip]
  bounded_linear.uniform_limit[OF blinop.bounded_linear_right]
  bounded_linear.uniform_limit[OF blinop.bounded_linear_left]
  bounded_linear.uniform_limit[OF bounded_linear_apply_blinop]

no_notation
  blinop_apply (infixl "$" 999)
notation vec_nth (infixl "$" 90)

end
