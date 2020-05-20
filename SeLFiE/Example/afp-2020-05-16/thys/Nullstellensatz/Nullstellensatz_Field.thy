(* Author: Alexander Maletzky *)

section \<open>Field-Theoretic Version of Hilbert's Nullstellensatz\<close>

theory Nullstellensatz_Field
  imports Nullstellensatz "HOL-Types_To_Sets.Types_To_Sets"
begin

text \<open>Building upon the geometric version of Hilbert's Nullstellensatz in
  @{theory Nullstellensatz.Nullstellensatz}, we prove its field-theoretic version here. To that end we employ
  the `types to sets' methodology.\<close>

subsection \<open>Getting Rid of Sort Constraints in Geometric Version\<close>

text \<open>We can use the `types to sets' approach to get rid of the @{class countable} and @{class linorder}
  sort constraints on the type of indeterminates in the geometric version of the Nullstellensatz.
  Once the `types to sets' methodology is integrated as a standard component into the main library of
  Isabelle, the theorems in @{theory Nullstellensatz.Nullstellensatz} could be replaced by their counterparts
  in this section.\<close>

lemmas radical_idealI_internalized = radical_idealI[unoverload_type 'x]

lemma radical_idealI:
  assumes "finite X" and "F \<subseteq> P[X]" and "f \<in> P[X]" and "x \<notin> X"
    and "\<V> (insert (1 - punit.monom_mult 1 (Poly_Mapping.single x 1) f) F) = {}"
  shows "(f::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::alg_closed_field) \<in> \<surd>ideal F"
proof -
  define Y where "Y = insert x X"
  from assms(1) have fin_Y: "finite Y" by (simp add: Y_def)
  have "X \<subseteq> Y" by (auto simp: Y_def)
  hence "P[X] \<subseteq> P[Y]" by (rule Polys_mono)
  with assms(2, 3) have F_sub: "F \<subseteq> P[Y]" and "f \<in> P[Y]" by auto
  {
    text \<open>We define the type @{typ 'y} to be isomorphic to @{term Y}.\<close>
    assume "\<exists>(Rep :: 'y \<Rightarrow> 'x) Abs. type_definition Rep Abs Y"
    then obtain rep :: "'y \<Rightarrow> 'x" and abs :: "'x \<Rightarrow> 'y" where t: "type_definition rep abs Y"
      by blast
    then interpret y: type_definition rep abs Y .

    from well_ordering obtain le_y'::"('y \<times> 'y) set" where fld: "Field le_y' = UNIV"
      and wo: "Well_order le_y'" by meson
    define le_y where "le_y = (\<lambda>a b::'y. (a, b) \<in> le_y')"

    from \<open>f \<in> P[Y]\<close> have 0: "map_indets rep (map_indets abs f) = f" unfolding map_indets_map_indets
      by (intro map_indets_id) (auto intro!: y.Abs_inverse dest: PolysD)
    have 1: "map_indets (rep \<circ> abs) ` F = F"
    proof
      from F_sub show "map_indets (rep \<circ> abs) ` F \<subseteq> F"
        by (smt PolysD(2) comp_apply image_subset_iff map_indets_id subsetD y.Abs_inverse)
    next
      from F_sub show "F \<subseteq> map_indets (rep \<circ> abs) ` F"
        by (smt PolysD(2) comp_apply image_eqI map_indets_id subsetD subsetI y.Abs_inverse)
    qed
    have 2: "inj rep" by (meson inj_onI y.Rep_inject)
    hence 3: "inj (map_indets rep)" by (rule map_indets_injI)
    from fin_Y have 4: "finite (abs ` Y)" by (rule finite_imageI)
    from wo have le_y_refl: "le_y x x" for x
      by (simp add: le_y_def well_order_on_def linear_order_on_def partial_order_on_def
                    preorder_on_def refl_on_def fld)
    have le_y_total: "le_y x y \<or> le_y y x" for x y
    proof (cases "x = y")
      case True
      thus ?thesis by (simp add: le_y_refl)
    next
      case False
      with wo show ?thesis
        by (simp add: le_y_def well_order_on_def linear_order_on_def total_on_def
                      Relation.total_on_def fld)
    qed

    from 4 finite_imp_inj_to_nat_seg y.Abs_image have "class.countable TYPE('y)"
      by unfold_locales fastforce
    moreover have "class.linorder le_y (strict le_y)"
      apply standard
      subgoal by (fact refl)
      subgoal by (fact le_y_refl)
      subgoal using wo
        by (auto simp: le_y_def well_order_on_def linear_order_on_def partial_order_on_def
                      preorder_on_def fld dest: transD)
      subgoal using wo
        by (simp add: le_y_def well_order_on_def linear_order_on_def partial_order_on_def
                      preorder_on_def antisym_def fld)
      subgoal by (fact le_y_total)
      done
    moreover from assms(1) have "finite (abs ` X)" by (rule finite_imageI)
    moreover have "map_indets abs ` F \<subseteq> P[abs ` X]"
    proof (rule subset_trans)
      from assms(2) show "map_indets abs ` F \<subseteq> map_indets abs ` P[X]" by (rule image_mono)
    qed (simp only: image_map_indets_Polys)
    moreover have "map_indets abs f \<in> P[abs ` X]"
    proof
      from assms(3) show "map_indets abs f \<in> map_indets abs ` P[X]" by (rule imageI)
    qed (simp only: image_map_indets_Polys)
    moreover from assms(4) y.Abs_inject have "abs x \<notin> abs ` X" unfolding Y_def by blast
    moreover have "\<V> (insert (1 - punit.monom_mult 1 (Poly_Mapping.single (abs x) (Suc 0))
                                    (map_indets abs f)) (map_indets abs ` F)) = {}"
    proof (intro set_eqI iffI)
      fix a
      assume "a \<in> \<V> (insert (1 - punit.monom_mult 1 (Poly_Mapping.single (abs x) (Suc 0))
                                    (map_indets abs f)) (map_indets abs ` F))"
      also have "\<dots> = (\<lambda>b. b \<circ> abs) -` \<V> (insert (1 - punit.monom_mult 1 (Poly_Mapping.single x 1) f) F)"
        by (simp add: map_indets_minus map_indets_times map_indets_monomial
                flip: variety_of_map_indets times_monomial_left)
      finally show "a \<in> {}" by (simp only: assms(5) vimage_empty)
    qed simp
    ultimately have "map_indets abs f \<in> \<surd>ideal (map_indets abs ` F)"
      by (rule radical_idealI_internalized[where 'x='y, untransferred, simplified])
    hence "map_indets rep (map_indets abs f) \<in> map_indets rep ` \<surd>ideal (map_indets abs ` F)"
      by (rule imageI)
    also from 2 have "\<dots> = \<surd>(ideal F \<inter> P[Y]) \<inter> P[Y]"
      by (simp add: image_map_indets_ideal image_map_indets_radical image_image map_indets_map_indets
                    1 y.Rep_range)
    also have "\<dots> \<subseteq> \<surd>ideal F" using radical_mono by blast
    finally have ?thesis by (simp only: 0)
  }
  note rl = this[cancel_type_definition]
  have "Y \<noteq> {}" by (simp add: Y_def)
  thus ?thesis by (rule rl)
qed

corollary radical_idealI_extend_indets:
  assumes "finite X" and "F \<subseteq> P[X]"
    and "\<V> (insert (1 - punit.monom_mult 1 (Poly_Mapping.single None 1) (extend_indets f))
                            (extend_indets ` F)) = {}"
  shows "(f::_ \<Rightarrow>\<^sub>0 _::alg_closed_field) \<in> \<surd>ideal F"
proof -
  define Y where "Y = X \<union> indets f"
  from assms(1) have fin_Y: "finite Y" by (simp add: Y_def finite_indets)
  have "P[X] \<subseteq> P[Y]" by (rule Polys_mono) (simp add: Y_def)
  with assms(2) have F_sub: "F \<subseteq> P[Y]" by (rule subset_trans)
  have f_in: "f \<in> P[Y]" by (simp add: Y_def Polys_alt)

  let ?F = "extend_indets ` F"
  let ?f = "extend_indets f"
  let ?X = "Some ` Y"
  from fin_Y have "finite ?X" by (rule finite_imageI)
  moreover from F_sub have "?F \<subseteq> P[?X]"
    by (auto simp: indets_extend_indets intro!: PolysI_alt imageI dest!: PolysD(2) subsetD[of F])
  moreover from f_in have "?f \<in> P[?X]"
    by (auto simp: indets_extend_indets intro!: PolysI_alt imageI dest!: PolysD(2))
  moreover have "None \<notin> ?X" by simp
  ultimately have "?f \<in> \<surd>ideal ?F" using assms(3) by (rule radical_idealI)
  also have "?f \<in> \<surd>ideal ?F \<longleftrightarrow> f \<in> \<surd>ideal F"
  proof
    assume "f \<in> \<surd>ideal F"
    then obtain m where "f ^ m \<in> ideal F" by (rule radicalE)
    hence "extend_indets (f ^ m) \<in> extend_indets ` ideal F" by (rule imageI)
    with extend_indets_ideal_subset have "?f ^ m \<in> ideal ?F" unfolding extend_indets_power ..
    thus "?f \<in> \<surd>ideal ?F" by (rule radicalI)
  next
    assume "?f \<in> \<surd>ideal ?F"
    then obtain m where "?f ^ m \<in> ideal ?F" by (rule radicalE)
    moreover have "?f ^ m \<in> P[- {None}]"
      by (rule Polys_closed_power) (auto intro!: PolysI_alt simp: indets_extend_indets)
    ultimately have "extend_indets (f ^ m) \<in> extend_indets ` ideal F"
      by (simp add: extend_indets_ideal extend_indets_power)
    hence "f ^ m \<in> ideal F" by (simp only: inj_image_mem_iff[OF inj_extend_indets])
    thus "f \<in> \<surd>ideal F" by (rule radicalI)
  qed
  finally show ?thesis .
qed

theorem Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]"
    and "(f::_ \<Rightarrow>\<^sub>0 _::alg_closed_field) \<in> \<I> (\<V> F)"
  shows "f \<in> \<surd>ideal F"
  using assms(1, 2)
proof (rule radical_idealI_extend_indets)
  let ?f = "punit.monom_mult 1 (monomial 1 None) (extend_indets f)"
  show "\<V> (insert (1 - ?f) (extend_indets ` F)) = {}"
  proof (intro subset_antisym subsetI)
    fix a
    assume "a \<in> \<V> (insert (1 - ?f) (extend_indets ` F))"
    moreover have "1 - ?f \<in> insert (1 - ?f) (extend_indets ` F)" by simp
    ultimately have "poly_eval a (1 - ?f) = 0" by (rule variety_ofD)
    hence "poly_eval a (extend_indets f) \<noteq> 0"
      by (auto simp: poly_eval_minus poly_eval_times simp flip: times_monomial_left)
    hence "poly_eval (a \<circ> Some) f \<noteq> 0" by (simp add: poly_eval_extend_indets)
    have "a \<circ> Some \<in> \<V> F"
    proof (rule variety_ofI)
      fix f'
      assume "f' \<in> F"
      hence "extend_indets f' \<in> insert (1 - ?f) (extend_indets ` F)" by simp
      with \<open>a \<in> _\<close> have "poly_eval a (extend_indets f') = 0" by (rule variety_ofD)
      thus "poly_eval (a \<circ> Some) f' = 0" by (simp only: poly_eval_extend_indets)
    qed
    with assms(3) have "poly_eval (a \<circ> Some) f = 0" by (rule ideal_ofD)
    with \<open>poly_eval (a \<circ> Some) f \<noteq> 0\<close> show "a \<in> {}" ..
  qed simp
qed

theorem strong_Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]"
  shows "\<I> (\<V> F) = \<surd>ideal (F::(_ \<Rightarrow>\<^sub>0 _::alg_closed_field) set)"
proof (intro subset_antisym subsetI)
  fix f
  assume "f \<in> \<I> (\<V> F)"
  with assms show "f \<in> \<surd>ideal F" by (rule Nullstellensatz)
qed (metis ideal_ofI variety_ofD variety_of_radical_ideal)

theorem weak_Nullstellensatz:
  assumes "finite X" and "F \<subseteq> P[X]" and "\<V> F = ({}::(_ \<Rightarrow> _::alg_closed_field) set)"
  shows "ideal F = UNIV"
proof -
  from assms(1, 2) have "\<I> (\<V> F) = \<surd>ideal F" by (rule strong_Nullstellensatz)
  thus ?thesis by (simp add: assms(3) flip: radical_ideal_eq_UNIV_iff)
qed

lemma radical_ideal_iff:
  assumes "finite X" and "F \<subseteq> P[X]" and "f \<in> P[X]" and "x \<notin> X"
  shows "(f::_ \<Rightarrow>\<^sub>0 _::alg_closed_field) \<in> \<surd>ideal F \<longleftrightarrow>
            1 \<in> ideal (insert (1 - punit.monom_mult 1 (Poly_Mapping.single x 1) f) F)"
proof -
  let ?f = "punit.monom_mult 1 (Poly_Mapping.single x 1) f"
  show ?thesis
  proof
    assume "f \<in> \<surd>ideal F"
    then obtain m where "f ^ m \<in> ideal F" by (rule radicalE)
    from assms(1) have "finite (insert x X)" by simp
    moreover have "insert (1 - ?f) F \<subseteq> P[insert x X]" unfolding insert_subset
    proof (intro conjI Polys_closed_minus one_in_Polys Polys_closed_monom_mult PPs_closed_single)
      have "P[X] \<subseteq> P[insert x X]" by (rule Polys_mono) blast
      with assms(2, 3) show "f \<in> P[insert x X]" and "F \<subseteq> P[insert x X]" by blast+
    qed simp
    moreover have "\<V> (insert (1 - ?f) F) = {}"
    proof (intro subset_antisym subsetI)
      fix a
      assume "a \<in> \<V> (insert (1 - ?f) F)"
      moreover have "1 - ?f \<in> insert (1 - ?f) F" by simp
      ultimately have "poly_eval a (1 - ?f) = 0" by (rule variety_ofD)
      hence "poly_eval a (f ^ m) \<noteq> 0"
        by (auto simp: poly_eval_minus poly_eval_times poly_eval_power simp flip: times_monomial_left)
      from \<open>a \<in> _\<close> have "a \<in> \<V> (ideal (insert (1 - ?f) F))" by (simp only: variety_of_ideal)
      moreover from \<open>f ^ m \<in> ideal F\<close> ideal.span_mono have "f ^ m \<in> ideal (insert (1 - ?f) F)"
        by (rule rev_subsetD) blast
      ultimately have "poly_eval a (f ^ m) = 0" by (rule variety_ofD)
      with \<open>poly_eval a (f ^ m) \<noteq> 0\<close> show "a \<in> {}" ..
    qed simp
    ultimately have "ideal (insert (1 - ?f) F) = UNIV" by (rule weak_Nullstellensatz)
    thus "1 \<in> ideal (insert (1 - ?f) F)" by simp
  next
    assume "1 \<in> ideal (insert (1 - ?f) F)"
    have "\<V> (insert (1 - ?f) F) = {}"
    proof (intro subset_antisym subsetI)
      fix a
      assume "a \<in> \<V> (insert (1 - ?f) F)"
      hence "a \<in> \<V> (ideal (insert (1 - ?f) F))" by (simp only: variety_of_ideal)
      hence "poly_eval a 1 = 0" using \<open>1 \<in> _\<close> by (rule variety_ofD)
      thus "a \<in> {}" by simp
    qed simp
    with assms show "f \<in> \<surd>ideal F" by (rule radical_idealI)
  qed
qed

subsection \<open>Field-Theoretic Version of the Nullstellensatz\<close>

text \<open>Due to the possibility of infinite indeterminate-types, we have to explicitly add the set of
  indeterminates under consideration to the definition of maximal ideals.\<close>

definition generates_max_ideal :: "'x set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_ring_1) set \<Rightarrow> bool"
  where "generates_max_ideal X F \<longleftrightarrow> (ideal F \<noteq> UNIV \<and>
                                      (\<forall>F'. F' \<subseteq> P[X] \<longrightarrow> ideal F \<subset> ideal F' \<longrightarrow> ideal F' = UNIV))"

lemma generates_max_idealI:
  assumes "ideal F \<noteq> UNIV" and "\<And>F'. F' \<subseteq> P[X] \<Longrightarrow> ideal F \<subset> ideal F' \<Longrightarrow> ideal F' = UNIV"
  shows "generates_max_ideal X F"
  using assms by (simp add: generates_max_ideal_def)

lemma generates_max_idealI_alt:
  assumes "ideal F \<noteq> UNIV" and "\<And>p. p \<in> P[X] \<Longrightarrow> p \<notin> ideal F \<Longrightarrow> 1 \<in> ideal (insert p F)"
  shows "generates_max_ideal X F"
  using assms(1)
proof (rule generates_max_idealI)
  fix F'
  assume "F' \<subseteq> P[X]" and sub: "ideal F \<subset> ideal F'"
  from this(2) ideal.span_subset_spanI have "\<not> F' \<subseteq> ideal F" by blast
  then obtain p where "p \<in> F'" and "p \<notin> ideal F" by blast
  from this(1) \<open>F' \<subseteq> P[X]\<close> have "p \<in> P[X]" ..
  hence "1 \<in> ideal (insert p F)" using \<open>p \<notin> _\<close> by (rule assms(2))
  also have "\<dots> \<subseteq> ideal (F' \<union> F)" by (rule ideal.span_mono) (simp add: \<open>p \<in> F'\<close>)
  also have "\<dots> = ideal (ideal F' \<union> ideal F)" by (simp add: ideal.span_Un ideal.span_span)
  also from sub have "ideal F' \<union> ideal F = ideal F'" by blast
  finally show "ideal F' = UNIV" by (simp only: ideal_eq_UNIV_iff_contains_one ideal.span_span)
qed

lemma generates_max_idealD:
  assumes "generates_max_ideal X F"
  shows "ideal F \<noteq> UNIV" and "F' \<subseteq> P[X] \<Longrightarrow> ideal F \<subset> ideal F' \<Longrightarrow> ideal F' = UNIV"
  using assms by (simp_all add: generates_max_ideal_def)

lemma generates_max_ideal_cases:
  assumes "generates_max_ideal X F" and "F' \<subseteq> P[X]" and "ideal F \<subseteq> ideal F'"
  obtains "ideal F = ideal F'" | "ideal F' = UNIV"
  using assms by (auto simp: generates_max_ideal_def)

lemma max_ideal_UNIV_radical:
  assumes "generates_max_ideal UNIV F"
  shows "\<surd>ideal F = ideal F"
proof (rule ccontr)
  assume "\<surd>ideal F \<noteq> ideal F"
  with radical_superset have "ideal F \<subset> \<surd>ideal F" by blast
  also have "\<dots> = ideal (\<surd>ideal F)" by simp
  finally have "ideal F \<subset> ideal (\<surd>ideal F)" .
  with assms _ have "ideal (\<surd>ideal F) = UNIV" by (rule generates_max_idealD) simp
  hence "\<surd>ideal F = UNIV" by simp
  hence "1 \<in> \<surd>ideal F" by simp
  hence "1 \<in> ideal F" by (auto elim: radicalE)
  hence "ideal F = UNIV" by (simp only: ideal_eq_UNIV_iff_contains_one)
  moreover from assms have "ideal F \<noteq> UNIV" by (rule generates_max_idealD)
  ultimately show False by simp
qed

lemma max_ideal_shape_aux:
  "(\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0) ` X \<subseteq> P[X]"
  by (auto intro!: Polys_closed_minus Polys_closed_monomial PPs_closed_single zero_in_PPs)

lemma max_ideal_shapeI:
  "generates_max_ideal X ((\<lambda>x. monomial (1::'a::field) (Poly_Mapping.single x 1) - monomial (a x) 0) ` X)"
    (is "generates_max_ideal X ?F")
proof (rule generates_max_idealI_alt)
  (* Proof modeled after https://math.stackexchange.com/a/1028331. *)

  show "ideal ?F \<noteq> UNIV"
  proof
    assume "ideal ?F = UNIV"
    hence "\<V> (ideal ?F) = \<V> UNIV" by (rule arg_cong)
    hence "\<V> ?F = {}" by simp
    moreover have "a \<in> \<V> ?F" by (rule variety_ofI) (auto simp: poly_eval_minus poly_eval_monomial)
    ultimately show False by simp
  qed
next
  fix p
  assume "p \<in> P[X]" and "p \<notin> ideal ?F"
  have "p \<in> ideal (insert p ?F)" by (rule ideal.span_base) simp
  let ?f = "\<lambda>x. monomial (1::'a) (Poly_Mapping.single x 1) - monomial (a x) 0"
  let ?g = "\<lambda>x. monomial (1::'a) (Poly_Mapping.single x 1) + monomial (a x) 0"
  define q where "q = poly_subst ?g p"
  have "p = poly_subst ?f q" unfolding q_def poly_subst_poly_subst
    by (rule sym, rule poly_subst_id)
        (simp add: poly_subst_plus poly_subst_monomial subst_pp_single flip: times_monomial_left)
  also have "\<dots> = (\<Sum>t\<in>keys q. punit.monom_mult (lookup q t) 0 (subst_pp ?f t))" by (fact poly_subst_def)
  also have "\<dots> = punit.monom_mult (lookup q 0) 0 (subst_pp ?f 0) +
                  (\<Sum>t\<in>keys q - {0}. monomial (lookup q t) 0 * subst_pp ?f t)"
      (is "_ = _ + ?r")
    by (cases "0 \<in> keys q") (simp_all add: sum.remove in_keys_iff flip: times_monomial_left)
  also have "\<dots> = monomial (lookup q 0) 0 + ?r" by (simp flip: times_monomial_left)
  finally have eq: "p - ?r = monomial (lookup q 0) 0" by simp
  have "?r \<in> ideal ?F"
  proof (intro ideal.span_sum ideal.span_scale)
    fix t
    assume "t \<in> keys q - {0}"
    hence "t \<in> keys q" and "keys t \<noteq> {}" by simp_all
    from this(2) obtain x where "x \<in> keys t" by blast
    hence "x \<in> indets q" using \<open>t \<in> keys q\<close> by (rule in_indetsI)
    then obtain y where "y \<in> indets p" and "x \<in> indets (?g y)" unfolding q_def
      by (rule in_indets_poly_substE)
    from this(2) indets_plus_subset have "x \<in> indets (monomial (1::'a) (Poly_Mapping.single y 1)) \<union>
                                                indets (monomial (a y) 0)" ..
    with \<open>y \<in> indets p\<close> have "x \<in> indets p" by (simp add: indets_monomial)
    also from \<open>p \<in> P[X]\<close> have "\<dots> \<subseteq> X" by (rule PolysD)
    finally have "x \<in> X" .
    from \<open>x \<in> keys t\<close> have "lookup t x \<noteq> 0" by (simp add: in_keys_iff)
    hence eq: "b ^ lookup t x = b ^ Suc (lookup t x - 1)" for b by simp

    have "subst_pp ?f t = (\<Prod>y\<in>keys t. ?f y ^ lookup t y)" by (fact subst_pp_def)
    also from \<open>x \<in> keys t\<close> have "\<dots> = ((\<Prod>y\<in>keys t - {x}. ?f y ^ lookup t y) * ?f x ^ (lookup t x - 1)) * ?f x"
      by (simp add: prod.remove mult.commute eq)
    also from \<open>x \<in> X\<close> have "\<dots> \<in> ideal ?F" by (intro ideal.span_scale ideal.span_base imageI)
    finally show "subst_pp ?f t \<in> ideal ?F" .
  qed
  also have "\<dots> \<subseteq> ideal (insert p ?F)" by (rule ideal.span_mono) blast
  finally have "?r \<in> ideal (insert p ?F)" .
  with \<open>p \<in> ideal _\<close> have "p - ?r \<in> ideal (insert p ?F)" by (rule ideal.span_diff)
  hence "monomial (lookup q 0) 0 \<in> ideal (insert p ?F)" by (simp only: eq)
  hence "monomial (inverse (lookup q 0)) 0 * monomial (lookup q 0) 0 \<in> ideal (insert p ?F)"
    by (rule ideal.span_scale)
  hence "monomial (inverse (lookup q 0) * lookup q 0) 0 \<in> ideal (insert p ?F)"
    by (simp add: times_monomial_monomial)
  moreover have "lookup q 0 \<noteq> 0"
  proof
    assume "lookup q 0 = 0"
    with eq \<open>?r \<in> ideal ?F\<close> have "p \<in> ideal ?F" by simp
    with \<open>p \<notin> ideal ?F\<close> show False ..
  qed
  ultimately show "1 \<in> ideal (insert p ?F)" by simp
qed

text \<open>We first prove the following lemma assuming that the type of indeterminates is finite, and then
  transfer the result to arbitrary types of indeterminates by using the `types to sets' methodology.
  This approach facilitates the proof considerably.\<close>

lemma max_ideal_shapeD_finite:
  assumes "generates_max_ideal UNIV (F::(('x::finite \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::alg_closed_field) set)"
  obtains a where "ideal F = ideal (range (\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0))"
proof -
  have fin: "finite (UNIV::'x set)" by simp
  have "(\<Inter>a\<in>\<V> F. ideal (range (\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0))) = \<I> (\<V> F)"
    (is "?A = _")
  proof (intro set_eqI iffI ideal_ofI INT_I)
    fix p a
    assume "p \<in> ?A" and "a \<in> \<V> F"
    hence "p \<in> ideal (range (\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0))"
      (is "_ \<in> ideal ?B") ..
    have "a \<in> \<V> ?B"
    proof (rule variety_ofI)
      fix f
      assume "f \<in> ?B"
      then obtain x where "f = monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0" ..
      thus "poly_eval a f = 0" by (simp add: poly_eval_minus poly_eval_monomial)
    qed
    hence "a \<in> \<V> (ideal ?B)" by (simp only: variety_of_ideal)
    thus "poly_eval a p = 0" using \<open>p \<in> ideal _\<close> by (rule variety_ofD)
  next
    fix p a
    assume "p \<in> \<I> (\<V> F)" and "a \<in> \<V> F"
    hence eq: "poly_eval a p = 0" by (rule ideal_ofD)
    have "p \<in> \<surd>ideal (range (\<lambda>x. monomial 1 (monomial 1 x) - monomial (a x) 0))" (is "_ \<in> \<surd>ideal ?B")
      using fin max_ideal_shape_aux
    proof (rule Nullstellensatz)
      show "p \<in> \<I> (\<V> ?B)"
      proof (rule ideal_ofI)
        fix a0
        assume "a0 \<in> \<V> ?B"
        have "a0 = a"
        proof
          fix x
          have "monomial 1 (monomial 1 x) - monomial (a x) 0 \<in> ?B" by (rule rangeI)
          with \<open>a0 \<in> _\<close> have "poly_eval a0 (monomial 1 (monomial 1 x) - monomial (a x) 0) = 0"
            by (rule variety_ofD)
          thus "a0 x = a x" by (simp add: poly_eval_minus poly_eval_monomial)
        qed
        thus "poly_eval a0 p = 0" by (simp only: eq)
      qed
    qed
    also have "\<dots> = ideal (range (\<lambda>x. monomial 1 (monomial 1 x) - monomial (a x) 0))"
      using max_ideal_shapeI by (rule max_ideal_UNIV_radical)
    finally show "p \<in> ideal (range (\<lambda>x. monomial 1 (monomial 1 x) - monomial (a x) 0))" .
  qed
  also from fin have "\<dots> = \<surd>ideal F" by (rule strong_Nullstellensatz) simp
  also from assms have "\<dots> = ideal F" by (rule max_ideal_UNIV_radical)
  finally have eq: "?A = ideal F" .
  also from assms have "\<dots> \<noteq> UNIV" by (rule generates_max_idealD)
  finally obtain a where "a \<in> \<V> F"
    and "ideal (range (\<lambda>x. monomial 1 (Poly_Mapping.single x (1::nat)) - monomial (a x) 0)) \<noteq> UNIV"
      (is "?B \<noteq> _") by auto
  from \<open>a \<in> \<V> F\<close> have "ideal F \<subseteq> ?B" by (auto simp flip: eq)
  with assms max_ideal_shape_aux show ?thesis
  proof (rule generates_max_ideal_cases)
    assume "ideal F = ?B"
    thus ?thesis ..
  next
    assume "?B = UNIV"
    with \<open>?B \<noteq> UNIV\<close> show ?thesis ..
  qed
qed

lemmas max_ideal_shapeD_internalized = max_ideal_shapeD_finite[unoverload_type 'x]

lemma max_ideal_shapeD:
  assumes "finite X" and "F \<subseteq> P[X]"
    and "generates_max_ideal X (F::(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::alg_closed_field) set)"
  obtains a where "ideal F = ideal ((\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial (a x) 0) ` X)"
proof (cases "X = {}")
  case True
  from assms(3) have "ideal F \<noteq> UNIV" by (rule generates_max_idealD)
  hence "1 \<notin> ideal F" by (simp add: ideal_eq_UNIV_iff_contains_one)
  have "F \<subseteq> {0}"
  proof
    fix f
    assume "f \<in> F"
    with assms(2) have "f \<in> P[X]" ..
    then obtain c where f: "f = monomial c 0" by (auto simp: True Polys_empty)
    with \<open>f \<in> F\<close> have "monomial c 0 \<in> ideal F" by (simp only: ideal.span_base)
    hence "monomial (inverse c) 0 * monomial c 0 \<in> ideal F" by (rule ideal.span_scale)
    hence "monomial (inverse c * c) 0 \<in> ideal F" by (simp add: times_monomial_monomial)
    with \<open>1 \<notin> ideal F\<close> left_inverse have "c = 0" by fastforce
    thus "f \<in> {0}" by (simp add: f)
  qed
  hence "ideal F = ideal ((\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial (undefined x) 0) ` X)"
    by (simp add: True)
  thus ?thesis ..
next
  case False
  {
    text \<open>We define the type @{typ 'y} to be isomorphic to @{term X}.\<close>
    assume "\<exists>(Rep :: 'y \<Rightarrow> 'x) Abs. type_definition Rep Abs X"
    then obtain rep :: "'y \<Rightarrow> 'x" and abs :: "'x \<Rightarrow> 'y" where t: "type_definition rep abs X"
      by blast
    then interpret y: type_definition rep abs X .

    have 1: "map_indets (rep \<circ> abs) ` A = A" if "A \<subseteq> P[X]" for A::"(_ \<Rightarrow>\<^sub>0 'a) set"
    proof
      from that show "map_indets (rep \<circ> abs) ` A \<subseteq> A"
        by (smt PolysD(2) comp_apply image_subset_iff map_indets_id subsetD y.Abs_inverse)
    next
      from that show "A \<subseteq> map_indets (rep \<circ> abs) ` A"
        by (smt PolysD(2) comp_apply image_eqI map_indets_id subsetD subsetI y.Abs_inverse)
    qed
    have 2: "inj rep" by (meson inj_onI y.Rep_inject)
    hence 3: "inj (map_indets rep)" by (rule map_indets_injI)

    have "class.finite TYPE('y)"
    proof
      from assms(1) have "finite (abs ` X)" by (rule finite_imageI)
      thus "finite (UNIV::'y set)" by (simp only: y.Abs_image)
    qed
    moreover have "generates_max_ideal UNIV (map_indets abs ` F)"
    proof (intro generates_max_idealI notI)
      assume "ideal (map_indets abs ` F) = UNIV"
      hence "1 \<in> ideal (map_indets abs ` F)" by simp
      hence "map_indets rep 1 \<in> map_indets rep ` ideal (map_indets abs ` F)" by (rule imageI)
      also from map_indets_plus map_indets_times have "\<dots> \<subseteq> ideal (map_indets rep ` map_indets abs ` F)"
        by (rule image_ideal_subset)
      also from assms(2) have "map_indets rep ` map_indets abs ` F = F"
        by (simp only: image_image map_indets_map_indets 1)
      finally have "1 \<in> ideal F" by simp
      moreover from assms(3) have "ideal F \<noteq> UNIV" by (rule generates_max_idealD)
      ultimately show False by (simp add: ideal_eq_UNIV_iff_contains_one)
    next
      fix F'
      assume "ideal (map_indets abs ` F) \<subset> ideal F'"
      with inj_on_subset have "map_indets rep ` ideal (map_indets abs ` F) \<subset> map_indets rep ` ideal F'"
        by (rule inj_on_strict_subset) (fact 3, fact subset_UNIV)
      hence sub: "ideal F \<inter> P[X] \<subset> ideal (map_indets rep ` F') \<inter> P[X]" using 2 assms(2)
        by (simp add: image_map_indets_ideal image_image map_indets_map_indets 1 y.Rep_range)
      have "ideal F \<subset> ideal (map_indets rep ` F')"
      proof (intro psubsetI notI ideal.span_subset_spanI subsetI)
        fix p
        assume "p \<in> F"
        with assms(2) ideal.span_base sub show "p \<in> ideal (map_indets rep ` F')" by blast
      next
        assume "ideal F = ideal (map_indets rep ` F')"
        with sub show False by simp
      qed
      with assms(3) _ have "ideal (map_indets rep ` F') = UNIV"
      proof (rule generates_max_idealD)
        from subset_UNIV have "map_indets rep ` F' \<subseteq> range (map_indets rep)" by (rule image_mono)
        also have "\<dots> = P[X]" by (simp only: range_map_indets y.Rep_range)
        finally show "map_indets rep ` F' \<subseteq> P[X]" .
      qed
      hence "P[range rep] = ideal (map_indets rep ` F') \<inter> P[range rep]" by simp
      also from 2 have "\<dots> = map_indets rep ` ideal F'" by (simp only: image_map_indets_ideal)
      finally have "map_indets rep ` ideal F' = range (map_indets rep)"
        by (simp only: range_map_indets)
      with 3 show "ideal F' = UNIV" by (metis inj_image_eq_iff)
    qed
    ultimately obtain a
      where *: "ideal (map_indets abs ` F) =
                 ideal (range (\<lambda>x. monomial 1 (Poly_Mapping.single x (Suc 0)) - monomial (a x) 0))"
        (is "_ = ?A")
      by (rule max_ideal_shapeD_internalized[where 'x='y, untransferred, simplified])
    hence "map_indets rep ` ideal (map_indets abs ` F) = map_indets rep ` ?A" by simp
    with 2 assms(2) have "ideal F \<inter> P[X] =
           ideal (range (\<lambda>x. monomial 1 (Poly_Mapping.single (rep x) 1) - monomial (a x) 0)) \<inter> P[X]"
        (is "_ = ideal ?B \<inter> _")
      by (simp add: image_map_indets_ideal y.Rep_range image_image map_indets_map_indets
              map_indets_minus map_indets_monomial 1)
    also have "?B = (\<lambda>x. monomial 1 (Poly_Mapping.single x 1) - monomial ((a \<circ> abs) x) 0) ` X"
        (is "_ = ?C")
    proof
      show "?B \<subseteq> ?C" by (smt comp_apply image_iff image_subset_iff y.Abs_image y.Abs_inverse)
    next
      from y.Rep_inverse y.Rep_range show "?C \<subseteq> ?B" by auto
    qed
    finally have eq: "ideal F \<inter> P[X] = ideal ?C \<inter> P[X]" .
    have "ideal F = ideal ?C"
    proof (intro subset_antisym ideal.span_subset_spanI subsetI)
      fix p
      assume "p \<in> F"
      with assms(2) ideal.span_base have "p \<in> ideal F \<inter> P[X]" by blast
      thus "p \<in> ideal ?C" by (simp add: eq)
    next
      fix p
      assume "p \<in> ?C"
      then obtain x where "x \<in> X" and "p = monomial 1 (monomial 1 x) - monomial ((a \<circ> abs) x) 0" ..
      note this(2)
      also from \<open>x \<in> X\<close> have "\<dots> \<in> P[X]"
        by (intro Polys_closed_minus Polys_closed_monomial PPs_closed_single zero_in_PPs)
      finally have "p \<in> P[X]" .
      with \<open>p \<in> ?C\<close> have "p \<in> ideal ?C \<inter> P[X]" by (simp add: ideal.span_base)
      also have "\<dots> = ideal F \<inter> P[X]" by (simp only: eq)
      finally show "p \<in> ideal F" by simp
    qed
    hence ?thesis ..
  }
  note rl = this[cancel_type_definition]
  from False show ?thesis by (rule rl)
qed

theorem Nullstellensatz_field:
  assumes "finite X" and "F \<subseteq> P[X]" and "generates_max_ideal X (F::(_ \<Rightarrow>\<^sub>0 _::alg_closed_field) set)"
    and "x \<in> X"
  shows "{0} \<subset> ideal F \<inter> P[{x}]"
  unfolding subset_not_subset_eq
proof (intro conjI notI)
  show "{0} \<subseteq> ideal F \<inter> P[{x}]" by (auto intro: ideal.span_zero zero_in_Polys)
next
  from assms(1, 2, 3) obtain a
    where eq: "ideal F = ideal ((\<lambda>x. monomial 1 (monomial 1 x) - monomial (a x) 0) ` X)"
    by (rule max_ideal_shapeD)
  let ?p = "\<lambda>x. monomial 1 (monomial 1 x) - monomial (a x) 0"
  from assms(4) have "?p x \<in> ?p ` X" by (rule imageI)
  also have "\<dots> \<subseteq> ideal F" unfolding eq by (rule ideal.span_superset)
  finally have "?p x \<in> ideal F" .
  moreover have "?p x \<in> P[{x}]"
    by (auto intro!: Polys_closed_minus Polys_closed_monomial PPs_closed_single zero_in_PPs)
  ultimately have "?p x \<in> ideal F \<inter> P[{x}]" ..
  also assume "\<dots> \<subseteq> {0}"
  finally show False
    by (metis diff_eq_diff_eq diff_self monomial_0D monomial_inj one_neq_zero singletonD)
qed

end (* theory *)
