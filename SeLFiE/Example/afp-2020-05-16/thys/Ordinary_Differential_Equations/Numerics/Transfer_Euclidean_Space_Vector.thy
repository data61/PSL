theory Transfer_Euclidean_Space_Vector
imports
  "../Refinement/Refine_Vector_List"
  Transfer_ODE
begin

type_synonym 'n rvec = "(real, 'n) vec"
type_synonym 'n vec1 = "(real, 'n) vec \<times> ((real, 'n) vec, 'n) vec" \<comment> \<open>vector with C1 information\<close>
type_synonym 'a c1_info = "'a \<times> ('a \<Rightarrow>\<^sub>L 'a)"
type_synonym 'n eucl1 = "'n rvec c1_info" \<comment> \<open>abstract C1 information\<close>

subsection \<open>Casting function\<close>

definition "cast = eucl_of_list o list_of_eucl"

lemma cast_eqI: "cast x = y" if "list_of_eucl x = list_of_eucl y"
  using that by (auto simp: cast_def)

lemma cast_eqI2: "cast (x::'a) = (y::'b)"
  if "x = cast y" and "DIM('a::executable_euclidean_space) = DIM('b::executable_euclidean_space)"
  apply (rule cast_eqI)
  using that
  by (auto intro!: nth_equalityI simp: cast_def)

lemma cast_Basis_list_nth[simp]: "cast (Basis_list ! i::'a) = (Basis_list ! i::'b)"
  if "DIM('a::executable_euclidean_space) = DIM('b::executable_euclidean_space)" "i < DIM('b)"
  apply (rule cast_eqI)
  using that
  by (auto simp: inner_Basis nth_eq_iff_index_eq intro!: nth_equalityI)

lemma cast_inner[simp]:
  "cast x \<bullet> (cast y::'b) = x \<bullet> (y::'a)"
  if "DIM('a::executable_euclidean_space) = DIM('b::executable_euclidean_space)"
  using that
  by (subst (2) euclidean_inner)
     (auto simp: cast_def eucl_of_list_inner_eq inner_lv_rel_def sum_Basis_sum_nth_Basis_list
      sum_list_sum_nth atLeast0LessThan)

lemma cast_inner_Basis_list_nth[simp]:
  "cast x \<bullet> (Basis_list::'a list) ! i = x \<bullet> (Basis_list::'b list) ! i"
  if "DIM('a::executable_euclidean_space) = DIM('b::executable_euclidean_space)" "i < DIM('b)"
  using that
  by (auto simp: cast_def eucl_of_list_inner)

lemma cast_eucl_of_list[simp]:
  "cast (eucl_of_list xs::'a) = (eucl_of_list xs::'b)"
  if "DIM('a::executable_euclidean_space) = DIM('b::executable_euclidean_space)" "length xs = DIM('b)"
  using that
  by (auto simp: intro!: euclidean_eqI[where 'a='b])
     (auto simp: cast_def eucl_of_list_inner dest!: in_Basis_index_Basis_list)

lemma norm_cast[simp]: "norm (cast x::'a) = norm (x::'b)"
  if "DIM('a::executable_euclidean_space) = DIM('b::executable_euclidean_space)"
  unfolding norm_conv_dist
  apply (subst (1 2) euclidean_dist_l2)
  using that
  apply (auto simp: L2_set_def sum_Basis_sum_nth_Basis_list  cong: sum.cong)
  apply (subst sum.cong[OF refl])
   apply (subst cast_inner_Basis_list_nth)
     apply auto
  done

lemma linear_cast: "linear (cast::'a\<Rightarrow>'b)"
  if "DIM('a::executable_euclidean_space) = DIM('b::executable_euclidean_space)"
  apply standard
  using that
  by (auto simp: inner_simps intro!: cast_eqI nth_equalityI exI[where x=1])

lemma bounded_linear_cast: "bounded_linear (cast::'a\<Rightarrow>'b)"
  if "DIM('a::executable_euclidean_space) = DIM('b::executable_euclidean_space)"
  apply standard
  using that
  by (auto simp: inner_simps intro!: cast_eqI nth_equalityI exI[where x=1])

lemmas [bounded_linear_intros] = bounded_linear_compose[OF bounded_linear_cast]

lemma cast_id[simp]: "cast i = i"
  by (simp add: cast_eqI)

definition cast_bl where "cast_bl f = Blinfun (cast o blinfun_apply f o cast)"

lemma cast_bl_rep: "cast_bl (f::'a \<Rightarrow>\<^sub>L 'b) x = (cast (f (cast (x::'c)))::'d)"
  if [bounded_linear_intros]:
    "DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
     "DIM('b::executable_euclidean_space) = DIM('d::executable_euclidean_space)"
  unfolding cast_bl_def o_def
  apply (subst bounded_linear_Blinfun_apply)
   apply (rule bounded_linear_intros)+
  apply auto
  done

definition "cast_eucl1 x = (cast (fst x), cast_bl (snd x))"

definition [simp]: "op_cast_image = (`) cast"
definition [simp]: "op_cast_eucl1_image = (`) cast_eucl1"
context includes autoref_syntax begin
lemma [autoref_op_pat_def]:
  "(`) cast \<equiv> OP op_cast_image"
  "(`) cast_eucl1 \<equiv> OP op_cast_eucl1_image"
  by auto
end

lemma cast_idem[simp]:
  "cast (cast (x::'c)::'b) = (cast x::'a)"
  if "DIM('a::executable_euclidean_space) = DIM('c::executable_euclidean_space)"
    "DIM('b::executable_euclidean_space) = DIM('c)"
  using that
  by (auto simp: cast_def intro!: )

lemma cast_bl_idem[simp]:
  "cast_bl (cast_bl (x::'c\<Rightarrow>\<^sub>L'c)::'b\<Rightarrow>\<^sub>L'b) = (cast_bl x::'a\<Rightarrow>\<^sub>L'a)"
  if "DIM('a::executable_euclidean_space) = DIM('c::executable_euclidean_space)"
    "DIM('b::executable_euclidean_space) = DIM('c)"
  using that
  by (auto simp: cast_bl_rep o_def intro!: blinfun_eqI)

lemma cast_eucl1_idem[simp]:
  "cast_eucl1 (cast_eucl1 (x::'c c1_info)::'b c1_info) = (cast_eucl1 x::'a c1_info)"
  if "DIM('a::executable_euclidean_space) = DIM('c::executable_euclidean_space)"
    "DIM('b::executable_euclidean_space) = DIM('c)"
  using that
  by (auto simp: cast_def cast_eucl1_def intro!: )

lemma linear_cast_bl:
  "linear (cast_bl::('a \<Rightarrow>\<^sub>L'b) \<Rightarrow> ('c \<Rightarrow>\<^sub>L 'd))"
  if "DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
     "DIM('b::executable_euclidean_space) = DIM('d::executable_euclidean_space)"
  by standard
    (auto intro!: blinfun_eqI
      simp: cast_bl_rep that blinfun.bilinear_simps linear_cast linear_add linear.scaleR)
lemma norm_cast_bl_le: "norm ((cast_bl::('a \<Rightarrow>\<^sub>L'b) \<Rightarrow> ('c \<Rightarrow>\<^sub>L 'd)) x) \<le> norm x"
  if "DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
  "DIM('b::executable_euclidean_space) = DIM('d::executable_euclidean_space)"
  apply (rule norm_blinfun_bound)
  using that
   apply (auto simp: cast_bl_rep)
  apply (rule norm_blinfun[THEN order_trans])
  apply auto
  done

lemma norm_cast_bl_idem[simp]: "cast_bl ((cast_bl::('a \<Rightarrow>\<^sub>L'b) \<Rightarrow> ('c \<Rightarrow>\<^sub>L 'd)) x) = x"
  if "DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
     "DIM('b::executable_euclidean_space) = DIM('d::executable_euclidean_space)"
  by (auto intro!: blinfun_eqI simp: that cast_bl_rep)

lemma norm_cast_bl[simp]: "norm ((cast_bl::('a \<Rightarrow>\<^sub>L'b) \<Rightarrow> ('c \<Rightarrow>\<^sub>L 'd)) x) = norm x"
  if "DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
     "DIM('b::executable_euclidean_space) = DIM('d::executable_euclidean_space)"
proof (rule antisym)
  show "norm ((cast_bl::('a \<Rightarrow>\<^sub>L'b) \<Rightarrow> ('c \<Rightarrow>\<^sub>L 'd)) x) \<le> norm x"
    by (rule norm_cast_bl_le; fact)
  have "norm x = norm ((cast_bl::('c \<Rightarrow>\<^sub>L'd) \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'b)) ((cast_bl::('a \<Rightarrow>\<^sub>L'b) \<Rightarrow> ('c \<Rightarrow>\<^sub>L 'd)) x))"
    by (simp add: that)
  also note norm_cast_bl_le[OF that, of "cast_bl x"]
  finally show "norm x \<le> norm ((cast_bl::('a \<Rightarrow>\<^sub>L'b) \<Rightarrow> ('c \<Rightarrow>\<^sub>L 'd)) x)"
    apply (rule order_trans)
     defer
     apply (rule norm_cast_bl_le)
    using that by auto
qed

lemma bounded_linear_cast_bl:
  "bounded_linear (cast_bl::('a \<Rightarrow>\<^sub>L'b) \<Rightarrow> ('c \<Rightarrow>\<^sub>L 'd))"
  if "DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
     "DIM('b::executable_euclidean_space) = DIM('d::executable_euclidean_space)"
  by standard
    (auto intro!: blinfun_eqI exI[where x=1]
      simp: cast_bl_rep that blinfun.bilinear_simps linear_cast linear_add linear.scaleR)

lemma cast_bl_has_derivative[derivative_intros]:
  "((\<lambda>a. (cast_bl::('a \<Rightarrow>\<^sub>L'b) \<Rightarrow> ('c \<Rightarrow>\<^sub>L 'd)) (g a)) has_derivative (\<lambda>x. (cast_bl::('a \<Rightarrow>\<^sub>L'b) \<Rightarrow> ('c \<Rightarrow>\<^sub>L 'd)) (g' x))) (at x within X)"
  if "(g has_derivative g') (at x within X)"
     "DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
     "DIM('b::executable_euclidean_space) = DIM('d::executable_euclidean_space)"
  apply (rule has_derivative_compose[of g _ _ _ cast_bl, THEN has_derivative_eq_rhs])
    defer apply (rule bounded_linear_imp_has_derivative)
    apply (rule bounded_linear_cast_bl)
  using that
     apply auto
  done

lemma cast_bl_has_vector_derivative[derivative_intros]:
  "((\<lambda>a. (cast_bl::('a \<Rightarrow>\<^sub>L'b) \<Rightarrow> ('c \<Rightarrow>\<^sub>L 'd)) (g a)) has_vector_derivative cast_bl g') (at x within X)"
  if "(g has_vector_derivative g') (at x within X)"
  "DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
  "DIM('b::executable_euclidean_space) = DIM('d::executable_euclidean_space)"
  using that
  by (auto simp: has_vector_derivative_def blinfun.bilinear_simps cast_bl_rep linear.scaleR
      linear_cast_bl
      intro!: cast_bl_has_derivative derivative_eq_intros ext blinfun_eqI)

lemma cast_bl_has_vderiv_on:
  "((\<lambda>a. (cast_bl::('a \<Rightarrow>\<^sub>L'b) \<Rightarrow> ('c \<Rightarrow>\<^sub>L 'd)) (g a)) has_vderiv_on vd) X"
  if "(g has_vderiv_on g') X" "\<And>t. t \<in> X \<Longrightarrow> vd t = cast_bl (g' t)"
  "DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
  "DIM('b::executable_euclidean_space) = DIM('d::executable_euclidean_space)"
  using that
  by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)

lemma cast_bl_compose:
  "(cast_bl::('a \<Rightarrow>\<^sub>L'b) \<Rightarrow> ('c \<Rightarrow>\<^sub>L 'd)) (g  o\<^sub>L h) =
    ((cast_bl:: 'e \<Rightarrow>\<^sub>L 'b \<Rightarrow> 'f \<Rightarrow>\<^sub>L 'd) g o\<^sub>L (cast_bl:: 'a \<Rightarrow>\<^sub>L 'e \<Rightarrow> 'c \<Rightarrow>\<^sub>L 'f) h)"
  if "DIM('c::executable_euclidean_space) = DIM('a::executable_euclidean_space)"
  "DIM('b::executable_euclidean_space) = DIM('d::executable_euclidean_space)"
  "DIM('e::executable_euclidean_space) = DIM('f::executable_euclidean_space)"
  by (auto intro!: blinfun_eqI simp: cast_bl_rep that)

locale transfer_eucl_vec =
  fixes a::"'a::executable_euclidean_space" and n::"'n::enum"
  assumes dim[simp]: "DIM('a) = CARD('n)"
begin

context includes lifting_syntax begin

subsection \<open>Transfer from euclidean space to vector\<close>

definition "rel_ve (x::(real, 'n)vec) (y::'a) \<longleftrightarrow> list_of_eucl x = list_of_eucl y"

lemma [transfer_rule]: "bi_total rel_ve"
  apply (auto intro!: bi_totalI left_totalI right_totalI simp: rel_ve_def intro!: )
  subgoal for x by (auto intro!: exI[where x="eucl_of_list (list_of_eucl x)"] nth_equalityI simp: dim)
  subgoal for x by (auto intro!: exI[where x="eucl_of_list (list_of_eucl x)"] nth_equalityI simp: dim)
  done

lemma [transfer_rule]: "bi_unique rel_ve"
  by (auto intro!: bi_uniqueI left_uniqueI right_uniqueI simp: rel_ve_def )
    (metis eucl_of_list_list_of_eucl)+

text \<open>@{const Inf} is underspecified\<close>
text \<open>@{const Sup} is underspecified\<close>

lemma inf_transfer[transfer_rule]:
  "(rel_ve ===> rel_ve ===> rel_ve) inf inf"
  by (auto simp: rel_ve_def nth_eq_iff_index inner_Basis_inf_left
      list_of_eucl_eq_iff intro!: rel_funI)

lemma sup_transfer[transfer_rule]:
  "(rel_ve ===> rel_ve ===> rel_ve) sup sup"
  by (auto simp: rel_ve_def nth_eq_iff_index inner_Basis_sup_left
      list_of_eucl_eq_iff intro!: rel_funI)

lemma abs_transfer[transfer_rule]:
  "(rel_ve ===> rel_ve) abs abs"
  by (auto simp: rel_ve_def nth_eq_iff_index inner_Basis_sup_left abs_inner
      list_of_eucl_eq_iff intro!: rel_funI)

lemma less_eq_transfer[transfer_rule]:
  "(rel_ve ===> rel_ve ===> (=)) less_eq less_eq"
  by (auto simp: rel_ve_def nth_eq_iff_index eucl_le_Basis_list_iff[where 'a='a]
      eucl_le_Basis_list_iff[where 'a="'n rvec"]
      list_of_eucl_eq_iff intro!: rel_funI )

lemma scaleR_transfer[transfer_rule]:
  "((=) ===> rel_ve ===> rel_ve) scaleR scaleR"
  by (auto simp: rel_ve_def algebra_simps nth_eq_iff_index
      list_of_eucl_eq_iff intro!: rel_funI)

lemma Basis_transfer[transfer_rule]:
  "(rel_set rel_ve) Basis Basis"
  apply (rule rel_setI)
  subgoal for x by (auto simp: rel_ve_def list_of_eucl_eq_iff inner_Basis nth_eq_iff_index
        intro!: bexI[where x="Basis_list ! index Basis_list x"])
  subgoal for x by (auto simp: rel_ve_def list_of_eucl_eq_iff inner_Basis nth_eq_iff_index
        intro!: bexI[where x="Basis_list ! index Basis_list x"])
  done

lemma zero_transfer[transfer_rule]:
  "rel_ve 0 0"
  by (auto simp: rel_ve_def algebra_simps nth_eq_iff_index
      list_of_eucl_eq_iff intro!: rel_funI)

lemma uminus_transfer[transfer_rule]:
  "(rel_ve ===> rel_ve) uminus uminus"
  by (auto simp: rel_ve_def algebra_simps nth_eq_iff_index
      list_of_eucl_eq_iff intro!: rel_funI)

lemma plus_transfer[transfer_rule]:
  "(rel_ve ===> rel_ve ===> rel_ve) (+) (+)"
  by (auto simp: rel_ve_def algebra_simps nth_eq_iff_index
      list_of_eucl_eq_iff intro!: rel_funI)

lemma minus_transfer[transfer_rule]:
  "(rel_ve ===> rel_ve ===> rel_ve) (-) (-)"
  by (auto simp: rel_ve_def algebra_simps nth_eq_iff_index
      list_of_eucl_eq_iff intro!: rel_funI)

lemma Basis_list_transfer[transfer_rule]:
  "(list_all2 rel_ve) Basis_list Basis_list"
  by (auto simp: list_all2_iff in_set_zip rel_ve_def inner_Basis
      nth_eq_iff_index intro!: nth_equalityI)

lemma eucl_down_transfer[transfer_rule]:
  "((=) ===> rel_ve ===> rel_ve) eucl_down eucl_down"
  unfolding eucl_down_def
  by (auto simp: rel_ve_def algebra_simps nth_eq_iff_index
      list_of_eucl_eq_iff intro!: rel_funI)

lemma eucl_truncate_up_transfer[transfer_rule]:
  "((=) ===> rel_ve ===> rel_ve) eucl_truncate_up eucl_truncate_up"
  by (auto simp: rel_ve_def algebra_simps nth_eq_iff_index
      list_of_eucl_eq_iff intro!: rel_funI)

lemma eucl_truncate_down_transfer[transfer_rule]:
  "((=) ===> rel_ve ===> rel_ve) eucl_truncate_down eucl_truncate_down"
  by (auto simp: rel_ve_def algebra_simps nth_eq_iff_index
      list_of_eucl_eq_iff intro!: rel_funI)

lemma inner_transfer[transfer_rule]:
  "(rel_ve ===> rel_ve ===> (=)) inner inner"
  apply (subst euclidean_inner[where 'a="'a", abs_def])
  apply (subst euclidean_inner[where 'a="'n rvec", abs_def])
  by (auto simp: rel_ve_def algebra_simps nth_eq_iff_index inner_simps nth_eq_iff_index
      sum_Basis_sum_nth_Basis_list list_of_eucl_eq_iff intro!: rel_funI)

lemma rel_ve_cast: "rel_ve (x::'n rvec) (y::'a) \<longleftrightarrow> x = cast y"
  apply (auto simp: rel_ve_def cast_def intro!: rel_funI)
  by (metis eucl_of_list_list_of_eucl)

lemma rel_ve_cast': "rel_ve (x::'n rvec) (y::'a) \<longleftrightarrow> cast x = y"
  by (auto simp: rel_ve_def cast_def)

lemma cast_transfer[transfer_rule]: "(rel_ve ===> (=)) (\<lambda>x. x) cast"
  by (auto simp: rel_ve_cast)

lemma cast_transfer'[transfer_rule]: "((=) ===> rel_ve) (\<lambda>x. x) cast"
  by (auto simp: rel_ve_cast')

lemma bounded_linear_cast: "bounded_linear (cast::'a \<Rightarrow> 'n rvec)"
  by transfer (rule bounded_linear_ident)

lemma bounded_linear_cast': "bounded_linear (cast::'n rvec \<Rightarrow> 'a)"
  by transfer (rule bounded_linear_ident)

context includes blinfun.lifting begin

lemmas [simp] = cast_bl_rep

lemma eucl_of_list_transfer[transfer_rule]: "(list_all2 (=) ===> rel_ve) eucl_of_list eucl_of_list"
  unfolding eucl_of_list_def
  by transfer_prover

lemma list_of_eucl_transfer[transfer_rule]: "(rel_ve ===> list_all2 (=)) list_of_eucl list_of_eucl"
  unfolding list_of_eucl_def
  by transfer_prover

lemma blinfun_of_matrix_transfer[transfer_rule]:
  "((rel_ve ===> rel_ve ===> (=)) ===> (rel_blinfun rel_ve rel_ve)) blinfun_of_matrix blinfun_of_matrix"
  apply (rule rel_funI)
  apply transfer
  apply (rule rel_funI)
  unfolding rel_blinfun_def
  unfolding sum_Basis_sum_nth_Basis_list
  apply simp
  unfolding rel_ve_def list_of_eucl_eq_iff inner_sum_left
  apply simp
  apply (intro allI impI sum.cong refl)
  apply (rule arg_cong2[where f="(*)"])
  subgoal for a b c d e f g
    apply (rule arg_cong2[where f="(*)"])
    subgoal by simp
    apply (drule rel_funD[where x="Basis_list ! f"]) defer
     apply (drule rel_funD[where x="Basis_list ! g"]) defer
      apply assumption
    subgoal
      by (clarsimp simp: inner_Basis)
        (metis Basis_list_transfer dim index_Basis_list_nth length_Basis_list list_all2_lengthD)
    subgoal
      by (clarsimp simp: inner_Basis)
        (metis Basis_list_transfer dim index_Basis_list_nth length_Basis_list list_all2_lengthD)
    done
  subgoal for a b c d e f g
    apply (clarsimp simp: inner_Basis)
    by (metis (full_types, hide_lams) Basis_list_transfer dim index_Basis_list_nth length_Basis_list
        list_all2_conv_all_nth)
  done

lemma transfer_cast[transfer_rule]: "(rel_ve ===> rel_ve) (\<lambda>x. x) cast"
  by (auto simp:)

end

end

end

lemma
  assumes [simp]: "DIM('a::executable_euclidean_space) = CARD('n::enum)"
  shows cast_cast[simp]: "cast (cast x::'n rvec) = (x::'a)" "cast (cast y::'a) = (y::'n rvec)"
  by (auto simp: cast_def cast_def)

lifting_update blinfun.lifting
lifting_forget blinfun.lifting

locale transfer_eucl_vec_ll_on_open = transfer_eucl_vec a n + ll_on_open T f X
  for a::"'a::executable_euclidean_space" and n::"'n::enum" and T f and X::"'a set" +
  fixes vf vX
  defines "vf \<equiv> \<lambda>t x::'n rvec. cast (f t (cast x))::'n rvec"
  defines "vX \<equiv> cast ` X::'n rvec set"
begin

lemma transfer_X[transfer_rule]: "rel_set rel_ve vX X"
  and transfer_f[transfer_rule]: "(rel_fun (=) (rel_fun rel_ve rel_ve)) vf f"
  by (auto simp: rel_ve_cast cast_eqI vX_def vf_def intro!: rel_setI rel_funI)

sublocale v: ll_on_open T vf vX
  by (rule ll_on_open_axioms[untransferred])

context includes lifting_syntax begin

lemma transfer_csols[transfer_rule]:
  "((=) ===> rel_ve ===> rel_set (rel_prod ((=) ===> rel_ve) (=))) v.csols csols"
  unfolding csols_def v.csols_def
  by transfer_prover

lemma transfer_existence_ivl[transfer_rule]:
  "((=) ===> rel_ve ===> rel_set (=)) v.existence_ivl existence_ivl"
  unfolding existence_ivl_def v.existence_ivl_def
  by transfer_prover

lemma cast_v_flow_cast_eq:
  assumes "t \<in> existence_ivl t0 x0"
  shows "cast (v.flow t0 (cast x0) t) = flow t0 x0 t"
  apply (rule equals_flowI[OF _ _ order_refl])
  subgoal
    apply (rule existence_ivl_initial_time)
    using assms mem_existence_ivl_iv_defined(1) apply blast
    using assms mem_existence_ivl_iv_defined(2) by blast
  subgoal by (rule is_interval_existence_ivl)
  subgoal
    apply (rule solves_odeI)
    subgoal using assms
     by (transfer) (rule v.flow_has_vderiv_on[OF v.mem_existence_ivl_iv_defined])
   subgoal using assms
     by transfer (rule v.flow_in_domain)
   done
  subgoal
    using mem_existence_ivl_iv_defined[OF assms]
    apply (auto simp: )
    apply (subst v.flow_initial_time)
    subgoal by simp
    subgoal by transfer
    subgoal by transfer simp
    done
  subgoal by fact
  done

lemma transfer_flow[transfer_rule]:
  "((=) ===> rel_ve ===> (=) ===> rel_ve) v.flow flow"
  apply (auto intro!: rel_funI simp: rel_ve_cast)
  subgoal for t0 x0 t
    apply (cases "t \<in> existence_ivl t0 (cast x0)")
    subgoal by (simp add: cast_eqI cast_v_flow_cast_eq[symmetric])
    subgoal
      apply (subst v.flow_def) apply (subst flow_def)
      apply (auto simp: cast_eqI)
      subgoal by transfer simp
      subgoal by transfer simp
      done
    done
  done

end

end


locale transfer_c1_on_open_euclidean = transfer_eucl_vec a n + c1_on_open_euclidean f f' X
  for a::"'a::executable_euclidean_space" and n::"'n::enum" and f f' and X::"'a set" +
  fixes vf and vf'::"'n rvec \<Rightarrow> 'n rvec \<Rightarrow>\<^sub>L 'n rvec" and vX
  defines "vf \<equiv> \<lambda>x::'n rvec. cast (f (cast x))::'n rvec"
  defines  vf'_def: "vf' \<equiv> \<lambda>x. cast_bl (f' (cast x))"
  defines "vX \<equiv> cast ` X::'n rvec set"
begin

context includes lifting_syntax begin

lemma transfer_X[transfer_rule]: "rel_set rel_ve vX X"
  and transfer_f[transfer_rule]: "(rel_fun rel_ve rel_ve) vf f"
  by (auto simp: rel_ve_cast vX_def vf_def cast_eqI intro!: rel_setI rel_funI)

lemma transfer_f'[transfer_rule]: "(rel_ve ===> (rel_blinfun rel_ve rel_ve)) vf' f'"
  by (auto intro!: rel_funI simp: cast_eqI rel_blinfun_def rel_ve_cast vf'_def)

end

sublocale v: c1_on_open_euclidean vf vf' vX
  unfolding c1_on_open_euclidean_def
  by (rule c1_on_open_axioms[unfolded c1_on_open_euclidean_def, untransferred])

context includes lifting_syntax begin

lemma transfer_csols[transfer_rule]:
  "((=) ===> rel_ve ===> rel_set (rel_prod ((=) ===> rel_ve) (=))) v.csols csols"
  unfolding csols_def v.csols_def
  by transfer_prover

lemma transfer_existence_ivl[transfer_rule]:
  "((=) ===> rel_ve ===> rel_set (=)) v.existence_ivl existence_ivl"
  unfolding existence_ivl_def v.existence_ivl_def
  by transfer_prover

lemma transfer_existence_ivl0[transfer_rule]:
  "(rel_ve ===> rel_set (=)) v.existence_ivl0 existence_ivl0"
proof -
  interpret ll: transfer_eucl_vec_ll_on_open a n UNIV "\<lambda>_. f" X "\<lambda>_. vf" vX
    by unfold_locales (auto simp: vf_def)
  show ?thesis
    unfolding existence_ivl0_def v.existence_ivl0_def
    by transfer_prover
qed

lemma transfer_flow0[transfer_rule]:
  "(rel_ve ===> (=) ===> rel_ve) v.flow0 flow0"
proof -
  interpret ll: transfer_eucl_vec_ll_on_open a n UNIV "\<lambda>_. f" X "\<lambda>_. vf" vX
    by unfold_locales (auto simp: vf_def)
  show ?thesis
    unfolding flow0_def v.flow0_def
    by transfer_prover
qed

lemma cast_v_Dflow_cast_eq:
  assumes "t \<in> existence_ivl0 x0"
  shows "cast_bl (v.Dflow (cast x0) t) = Dflow x0 t"
proof -
  have "x0 \<in> X"
    using assms mem_existence_ivl_iv_defined(1) by blast
  have "0 \<in> existence_ivl0 x0"
    apply (rule existence_ivl_initial_time)
    apply simp
    apply fact
    done
  show ?thesis
  unfolding Dflow_def
  apply (rule mvar.equals_flowI[OF _ _ order_refl])
  subgoal
    apply (rule mvar.existence_ivl_initial_time)
     apply fact
    apply blast
    done
  subgoal by (rule mvar.is_interval_existence_ivl)
  subgoal
    apply (rule solves_odeI)
    subgoal
    proof -
      have *: "mvar.existence_ivl x0 0 1\<^sub>L = (v.mvar.existence_ivl (cast x0) 0 1\<^sub>L)"
        apply (subst mvar_existence_ivl_eq_existence_ivl, fact)
        apply (subst v.mvar_existence_ivl_eq_existence_ivl)
        subgoal using \<open>0 \<in> existence_ivl0 x0\<close> by (transfer)
        subgoal by transfer simp
        done
      have D: "(v.Dflow (cast x0) has_vderiv_on (\<lambda>t. v.vareq (cast x0) t o\<^sub>L v.mvar.flow (cast x0) 0 1\<^sub>L t))
        (mvar.existence_ivl x0 0 1\<^sub>L)"
        unfolding * v.Dflow_def
        apply (rule v.mvar.flow_has_vderiv_on[of 0 "cast x0" "1\<^sub>L"])
        subgoal using \<open>0 \<in> existence_ivl0 x0\<close> by (transfer)
        subgoal by transfer simp
        done
      have vareq_transfer: "vareq x0 x = cast_bl (v.vareq (cast x0) x)"
        if "x \<in> mvar.existence_ivl x0 0 1\<^sub>L"
        for x
        using that
        apply (subst (asm) mvar_existence_ivl_eq_existence_ivl)
        using \<open>0 \<in> existence_ivl0 x0\<close> apply simp
        unfolding vareq_def v.vareq_def
        apply (auto simp: blinfun_ext)
        apply transfer
        apply simp
        done
      show ?thesis
        apply (rule cast_bl_has_vderiv_on)
           apply (rule D)
          apply (simp_all add: v.Dflow_def blinfun_compose_assoc vareq_transfer)
        apply (subst cast_bl_compose)
           apply (auto simp: cast_bl_compose)
        done
    qed
    subgoal by simp
    done
  subgoal
    unfolding Dflow_def[symmetric]
    apply (subst Dflow_zero)
     apply fact
    apply (subst v.Dflow_zero)
    subgoal using \<open>x0 \<in> X\<close> by transfer simp
    subgoal by (auto simp: blinfun_ext)
    done
  subgoal
    by (subst mvar_existence_ivl_eq_existence_ivl; fact)
  done
qed

lemma transfer_Dflow[transfer_rule]:
  "(rel_ve ===> (=) ===> rel_blinfun rel_ve rel_ve) v.Dflow Dflow"
  apply (auto intro!: rel_funI simp: rel_ve_cast rel_blinfun_def)
  subgoal for x0 t d
    apply (cases "t \<in> mvar.existence_ivl (cast x0) 0 1\<^sub>L")
    subgoal
      apply (subst cast_v_Dflow_cast_eq[symmetric])
      using mvar.existence_ivl_subset[of "cast x0" 0 id_blinfun]
      by auto
    subgoal premises prems
    proof -
      have x0: "x0 \<notin> X \<longleftrightarrow> cast x0 \<notin> vX"
        by transfer simp
      have mvars: "mvar.existence_ivl x0 0 1\<^sub>L = v.mvar.existence_ivl (cast x0) 0 1\<^sub>L"
        apply (cases "cast x0 \<in> X")
        subgoal
          apply (subst mvar_existence_ivl_eq_existence_ivl)
           apply simp
          apply (subst v.mvar_existence_ivl_eq_existence_ivl)
           apply simp
           apply transfer apply simp
          apply transfer apply simp
          done
        subgoal premises prems
        proof -
          have "mvar.existence_ivl (cast x0) 0 1\<^sub>L = {}"
            apply (subst mvar.existence_ivl_empty_iff)
            using prems
            by simp
          moreover have "v.mvar.existence_ivl (cast x0) 0 1\<^sub>L = {}"
            apply (subst v.mvar.existence_ivl_empty_iff)
            using prems
            apply simp
            apply transfer apply simp
            done
          ultimately show ?thesis
            apply simp
            using \<open>mvar.existence_ivl (cast x0) 0 1\<^sub>L = {}\<close> \<open>v.mvar.existence_ivl (cast x0) 0 1\<^sub>L = {}\<close> by auto
        qed
        done
      show ?thesis
        using prems
        apply (subst v.Dflow_def) apply (subst Dflow_def)
        apply (subst v.mvar.flow_def) apply (subst mvar.flow_def)
        unfolding mvars
        apply (auto simp: blinfun.bilinear_simps)
        using mvars apply blast
        subgoal premises apply transfer by simp
        done
    qed
    done
  done

lemma returns_to_transfer[transfer_rule]:
  "(rel_set rel_ve ===> rel_ve ===> (=)) v.returns_to returns_to"
  unfolding returns_to_def v.returns_to_def
  by transfer_prover

lemma return_time_transfer[transfer_rule]:
  "(rel_set rel_ve ===> rel_ve ===> (=)) v.return_time return_time"
  unfolding return_time_def v.return_time_def
  by transfer_prover

lemma poincare_map_transfer[transfer_rule]:
  "(rel_set rel_ve ===> rel_ve ===> rel_ve) v.poincare_map poincare_map"
  unfolding v.poincare_map_def poincare_map_def
  by transfer_prover

lemma poincare_mapsto_transfer[transfer_rule]:
  "(rel_set rel_ve
   ===> rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve))
   ===> rel_set rel_ve
   ===> rel_set rel_ve
   ===> rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve))
   ===> (=)) v.poincare_mapsto poincare_mapsto"
  unfolding poincare_mapsto_def v.poincare_mapsto_def
    has_derivative_within differentiable_def
  by transfer_prover

lemma flowsto_transfer[transfer_rule]:
  "(rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve))
   ===> rel_set (=)
   ===> rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve))
   ===> rel_set (rel_prod rel_ve (rel_blinfun rel_ve rel_ve))
   ===> (=)) v.flowsto flowsto"
  unfolding flowsto_def v.flowsto_def
  by transfer_prover

end

end

end
