(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Lagrange Interpolation\<close>

text \<open>We formalized the Lagrange interpolation, i.e., a method to interpolate a polynomial $p$
  from a list of points $(x_1,p(x_1)), (x_2, p(x_2)), \ldots$. The interpolation algorithm is proven
  to be sound and complete.\<close>

theory Lagrange_Interpolation
imports 
  Missing_Polynomial
begin

definition lagrange_basis_poly :: "'a :: field list \<Rightarrow> 'a \<Rightarrow> 'a poly" where
  "lagrange_basis_poly xs xj \<equiv> let ys = filter (\<lambda> x. x \<noteq> xj) xs
    in prod_list (map (\<lambda> xi. smult (inverse (xj - xi)) [: - xi, 1 :]) ys)"

definition lagrange_interpolation_poly :: "('a :: field \<times> 'a)list \<Rightarrow> 'a poly" where
  "lagrange_interpolation_poly xs_ys \<equiv> let 
    xs = map fst xs_ys
    in sum_list (map (\<lambda> (xj,yj). smult yj (lagrange_basis_poly xs xj)) xs_ys)"

lemma [code]: 
  "lagrange_basis_poly xs xj = (let ys = filter (\<lambda> x. x \<noteq> xj) xs
    in prod_list (map (\<lambda> xi. let ii = inverse (xj - xi) in [: - ii * xi, ii :]) ys))"
  unfolding lagrange_basis_poly_def Let_def by simp

lemma degree_lagrange_basis_poly: "degree (lagrange_basis_poly xs xj) \<le> length (filter (\<lambda> x. x \<noteq> xj) xs)"
  unfolding lagrange_basis_poly_def Let_def
  by (rule order.trans[OF degree_prod_list_le], rule order_trans[OF sum_list_mono[of _ _ "\<lambda> _. 1"]], 
  auto simp: o_def, induct xs, auto)

lemma degree_lagrange_interpolation_poly:  
  shows "degree (lagrange_interpolation_poly xs_ys) \<le> length xs_ys - 1"
proof -
  {
    fix a b
    assume ab: "(a,b) \<in> set xs_ys" 
    let ?xs = "filter (\<lambda>x. x\<noteq>a) (map fst xs_ys)"
    from ab have "a \<in> set (map fst xs_ys)" by force
    hence "Suc (length ?xs) \<le> length xs_ys"
      by (induct xs_ys, auto)
    hence "length ?xs \<le> length xs_ys - 1" by auto
  } note main = this
  show ?thesis
    unfolding lagrange_interpolation_poly_def Let_def
    by (rule degree_sum_list_le, auto, rule order_trans[OF degree_lagrange_basis_poly], insert main, auto)
qed

lemma lagrange_basis_poly_1: 
  "poly (lagrange_basis_poly (map fst xs_ys) x) x = 1"
  unfolding lagrange_basis_poly_def Let_def poly_prod_list
  by (rule prod_list_neutral, auto)
  (metis field_class.field_inverse mult.commute right_diff_distrib right_minus_eq)

lemma lagrange_basis_poly_0: assumes "x' \<in> set (map fst xs_ys)" and "x' \<noteq> x" 
  shows "poly (lagrange_basis_poly (map fst xs_ys) x) x' = 0"
proof -
  let ?f = "\<lambda>xi. smult (inverse (x - xi)) [:- xi, 1:]"
  let ?xs = "filter (\<lambda>c. c\<noteq>x) (map fst xs_ys)"
  have mem: "?f x' \<in> set (map ?f ?xs)" using assms by auto
  show ?thesis
    unfolding lagrange_basis_poly_def Let_def poly_prod_list prod_list_map_remove1[OF mem]
    by simp
qed

lemma lagrange_interpolation_poly: assumes dist: "distinct (map fst xs_ys)"
  and p: "p = lagrange_interpolation_poly xs_ys"
  shows "\<And> x y. (x,y) \<in> set xs_ys \<Longrightarrow> poly p x = y"
proof -
  let ?xs = "map fst xs_ys"
  {
    fix x y
    assume xy: "(x,y) \<in> set xs_ys"
    show "poly p x = y" unfolding p lagrange_interpolation_poly_def Let_def poly_sum_list map_map o_def
    proof (subst sum_list_map_remove1[OF xy], unfold split poly_smult lagrange_basis_poly_1,
      subst sum_list_neutral)
      fix v
      assume "v \<in> set (map (\<lambda>xa. poly (case xa of (xj, yj) \<Rightarrow> smult yj (lagrange_basis_poly ?xs xj))
                               x)
                 (remove1 (x, y) xs_ys))" (is "_ \<in> set (map ?f ?xy)")
      then obtain xy' where mem: "xy' \<in> set ?xy" and v: "v = ?f xy'" by auto
      obtain x' y' where xy': "xy' = (x',y')" by force
      from v[unfolded this split] have v: "v = poly (smult y' (lagrange_basis_poly ?xs x')) x" .
      have neq: "x' \<noteq> x"
      proof
        assume "x' = x"
        with mem[unfolded xy'] have mem: "(x,y') \<in> set (remove1 (x,y) xs_ys)" by auto
        hence mem': "(x,y') \<in> set xs_ys" by (meson notin_set_remove1)
        from dist[unfolded distinct_map] have inj: "inj_on fst (set xs_ys)" by auto
        with mem' xy have y': "y' = y" unfolding inj_on_def by force
        from dist have "distinct xs_ys" using distinct_map by blast
        hence "(x,y) \<notin> set (remove1 (x,y) xs_ys)" by simp
        with mem[unfolded y']         
        show False by auto
      qed
      have "poly (lagrange_basis_poly ?xs x') x = 0"
        by (rule lagrange_basis_poly_0, insert xy mem[unfolded xy'] dist neq, force+) 
      thus "v = 0" unfolding v by simp
    qed simp
  } note sound = this
qed

end
