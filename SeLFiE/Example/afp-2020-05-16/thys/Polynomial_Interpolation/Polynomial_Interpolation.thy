(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Polynomial Interpolation\<close>

text \<open>We combine Newton's, Lagrange's, and Neville-Aitken's interpolation algorithms 
  to a combined interpolation algorithm which is parametric. This parametric algorithm is then
  further extend from fields to also perform interpolation of integer polynomials.
  
  In experiments it is revealed that Newton's algorithm performs better than the one
  of Lagrange. Moreover, on the integer numbers, only Newton's algorithm has been
  optimized with fast failure capabilities.\<close>
theory Polynomial_Interpolation
imports
  Improved_Code_Equations
  Newton_Interpolation
  Lagrange_Interpolation
  Neville_Aitken_Interpolation
begin

datatype interpolation_algorithm = Newton | Lagrange | Neville_Aitken

fun interpolation_poly :: "interpolation_algorithm \<Rightarrow> ('a :: field \<times> 'a)list \<Rightarrow> 'a poly" where
  "interpolation_poly Newton = newton_interpolation_poly"
| "interpolation_poly Lagrange = lagrange_interpolation_poly"
| "interpolation_poly Neville_Aitken = neville_aitken_interpolation_poly"

fun interpolation_poly_int :: "interpolation_algorithm \<Rightarrow> (int \<times> int)list \<Rightarrow> int poly option" where
  "interpolation_poly_int Newton xs_ys = newton_interpolation_poly_int xs_ys"
| "interpolation_poly_int alg xs_ys = (let 
     rxs_ys = map (\<lambda> (x,y). (of_int x, of_int y)) xs_ys;
     rp = interpolation_poly alg rxs_ys
     in if (\<forall> x \<in> set (coeffs rp). is_int_rat x) then
       Some (map_poly int_of_rat rp) else None)"

lemma interpolation_poly_int_def: "distinct (map fst xs_ys) \<Longrightarrow>
  interpolation_poly_int alg xs_ys = (let 
     rxs_ys = map (\<lambda> (x,y). (of_int x, of_int y)) xs_ys;
     rp = interpolation_poly alg rxs_ys
     in if (\<forall> x \<in> set (coeffs rp). is_int_rat x) then
       Some (map_poly int_of_rat rp) else None)"
  by (cases alg, auto simp: newton_interpolation_poly_int)

lemma interpolation_poly: assumes dist: "distinct (map fst xs_ys)"
  and p: "p = interpolation_poly alg xs_ys"
  and xy: "(x,y) \<in> set xs_ys"
  shows "poly p x = y"
proof (cases alg)
  case Newton
  thus ?thesis using newton_interpolation_poly[OF dist _ xy] p by simp
next
  case Lagrange
  thus ?thesis using lagrange_interpolation_poly[OF dist _ xy] p by simp
next
  case Neville_Aitken
  thus ?thesis using neville_aitken_interpolation_poly[OF dist _ xy] p by simp
qed

lemma degree_interpolation_poly:  
  shows "degree (interpolation_poly alg xs_ys) \<le> length xs_ys - 1"
  using degree_lagrange_interpolation_poly[of xs_ys]
    degree_newton_interpolation_poly[of xs_ys]
    degree_neville_aitken_interpolation_poly[of xs_ys]
  by (cases alg, auto)

lemma uniqueness_of_interpolation: fixes p :: "'a :: idom poly" 
  assumes cS: "card S = Suc n"
  and "degree p \<le> n" and "degree q \<le> n" and
   id: "\<And> x. x \<in> S \<Longrightarrow> poly p x = poly q x"
  shows "p = q"
proof -
  define f where "f = p - q"
  let ?R = "{x. poly f x = 0}"
  have sub: "S \<subseteq> ?R" unfolding f_def using id by auto
  show ?thesis
  proof (cases "f = 0")
    case True thus ?thesis unfolding f_def by simp
  next
    case False note f = this
    let ?R = "{x. poly f x = 0}"
    from poly_roots_finite[OF f] have "finite ?R" .
    from card_mono[OF this sub] poly_roots_degree[OF f] 
    have "Suc n \<le> degree f" unfolding cS by auto
    also have "\<dots> \<le> n" unfolding f_def
      by (rule degree_diff_le, insert assms, auto)
    finally show ?thesis by auto
  qed
qed

lemma uniqueness_of_interpolation_point_list: fixes p :: "'a :: idom poly" 
  assumes dist: "distinct (map fst xs_ys)"
  and p: "\<And> x y. (x,y) \<in> set xs_ys \<Longrightarrow> poly p x = y" "degree p < length xs_ys" 
  and q: "\<And> x y. (x,y) \<in> set xs_ys \<Longrightarrow> poly q x = y" "degree q < length xs_ys" 
  shows "p = q"
proof -
  let ?xs = "map fst xs_ys"
  from q obtain n where len: "length xs_ys = Suc n" and dq: "degree q \<le> n" by (cases xs_ys, auto)
  from p have dp: "degree p \<le> n" unfolding len by auto
  from dist have card: "card (set ?xs) = Suc n" unfolding len[symmetric]
    using distinct_card by fastforce
  show "p = q"
  proof (rule uniqueness_of_interpolation[OF card dp dq])
    fix x
    assume "x \<in> set ?xs"
    then obtain y where "(x,y) \<in> set xs_ys" by auto
    from p(1)[OF this] q(1)[OF this] show "poly p x = poly q x" by simp
  qed  
qed

lemma exactly_one_poly_interpolation: assumes xs: "xs_ys \<noteq> []" and dist: "distinct (map fst xs_ys)"
  shows "\<exists>! p. degree p < length xs_ys \<and> (\<forall> x y. (x,y) \<in> set xs_ys \<longrightarrow> poly p x = (y :: 'a :: field))"
proof -
  let ?alg = "undefined"
  let ?p = "interpolation_poly ?alg xs_ys"
  note inter = interpolation_poly[OF dist refl]
  show ?thesis
  proof (rule ex1I[of _ ?p], intro conjI allI impI)
    show dp: "degree ?p < length xs_ys" using degree_interpolation_poly[of ?alg xs_ys] xs by (cases xs_ys, auto)
    show "\<And>x y. (x, y) \<in> set xs_ys \<Longrightarrow> poly (interpolation_poly ?alg xs_ys) x = y"
      by (rule inter)
    fix q 
    assume q: "degree q < length xs_ys \<and> (\<forall>x y. (x, y) \<in> set xs_ys \<longrightarrow> poly q x = y)"
    show "q = ?p"
      by (rule uniqueness_of_interpolation_point_list[OF dist _ _ inter dp], insert q, auto)
  qed
qed


lemma interpolation_poly_int_Some: assumes dist': "distinct (map fst xs_ys)"
  and p: "interpolation_poly_int alg xs_ys = Some p"
  shows "\<And> x y. (x,y) \<in> set xs_ys \<Longrightarrow> poly p x = y" "degree p \<le> length xs_ys - 1"
proof -
  let ?r = "rat_of_int"
  define rxs_ys where "rxs_ys = map (\<lambda>(x, y). (?r x, ?r y)) xs_ys"
  have dist: "distinct (map fst rxs_ys)" using dist' unfolding distinct_map rxs_ys_def inj_on_def by force
  obtain rp where rp: "rp = interpolation_poly alg rxs_ys" by blast
  from p[unfolded interpolation_poly_int_def[OF dist'] Let_def, folded rxs_ys_def rp]
  have p: "p = map_poly int_of_rat rp" and ball: "Ball (set (coeffs rp)) is_int_rat"
    by (auto split: if_splits)
  have id: "rp = map_poly ?r p" unfolding p
    by (rule sym, subst map_poly_map_poly, force, rule map_poly_idI, insert ball, auto)
  note inter = interpolation_poly[OF dist rp]
  {
    fix x y
    assume "(x,y) \<in> set xs_ys"
    hence "(?r x, ?r y) \<in> set rxs_ys" unfolding rxs_ys_def by auto
    from inter[OF this] have "poly rp (?r x) = ?r y" by auto
    from this[unfolded id of_int_hom.poly_map_poly] show "poly p x = y" by auto
  }
  show "degree p \<le> length xs_ys - 1" using degree_interpolation_poly[of alg rxs_ys, folded rp]
    unfolding id rxs_ys_def by simp
qed  
  

lemma interpolation_poly_int_None: assumes dist: "distinct (map fst xs_ys)"
  and p: "interpolation_poly_int alg xs_ys = None"
  and q: "\<And> x y. (x,y) \<in> set xs_ys \<Longrightarrow> poly q x = y"
  and dq: "degree q < length xs_ys"
  shows False
proof -
  let ?r = "rat_of_int"
  let ?rp = "map_poly ?r"
  define rxs_ys where "rxs_ys = map (\<lambda>(x, y). (?r x, ?r y)) xs_ys"
  have dist': "distinct (map fst rxs_ys)" using dist unfolding distinct_map rxs_ys_def inj_on_def by force
  obtain rp where rp: "rp = interpolation_poly alg rxs_ys" by blast
  note degrp = degree_interpolation_poly[of alg rxs_ys, folded rp]
  from q have q': "\<And> x y. (x,y) \<in> set rxs_ys \<Longrightarrow> poly (?rp q) x = y" unfolding rxs_ys_def 
    by auto
  have [simp]: "degree (?rp q) = degree q" by simp
  have id: "rp = ?rp q"
    by (rule uniqueness_of_interpolation_point_list[OF dist' interpolation_poly[OF dist' rp]],
    insert q' dq degrp, auto simp: rxs_ys_def)
  from p[unfolded interpolation_poly_int_def[OF dist] Let_def, folded rxs_ys_def rp]
  have "\<exists> c \<in> set (coeffs rp). c \<notin> \<int>" by (auto split: if_splits)
  from this[unfolded id] show False by auto
qed

lemmas newton_interpolation_poly_int_Some = 
  interpolation_poly_int_Some[where alg = Newton, unfolded interpolation_poly_int.simps]

lemmas newton_interpolation_poly_int_None = 
  interpolation_poly_int_None[where alg = Newton, unfolded interpolation_poly_int.simps]

text \<open>We can also use Newton's improved algorithm for integer polynomials to show that
    there is no polynomial $p$ over the integers such that $p(0) = 0$ and $p(2) = 1$.
    The reason is that the intermediate result for computing the linear interpolant for these
    two point fails, and so adding further points (which corresponds to increasing the degree)
    will also fail. Of course, this can be generalized, showing that whenever you cannot
    interpolate a set of $n$ points with an integer polynomial of degree $n-1$, then you
    cannot interpolate this set of points with any integer polynomial. However, we did not
    formally prove this more general fact.\<close>

lemma impossible_p_0_is_0_and_p_2_is_1: "\<not> (\<exists> p. poly p 0 = 0 \<and> poly p 2 = (1 :: int))"
proof
  assume "\<exists> p. poly p 0 = 0 \<and> poly p 2 = (1 :: int)"
  then obtain p where p: "poly p 0 = 0" "poly p 2 = (1 :: int)" by auto
  define xs_ys where "xs_ys = map (\<lambda> i. (int i, poly p (int i))) [ 3 ..< 3 + degree p]"
  let ?l = "\<lambda> xs. (0,0) # (2 :: int,1 :: int) # xs" 
  let ?xs_ys = "?l xs_ys"
  define list where "list = map fst ?xs_ys"
  have dist: "distinct (map fst ?xs_ys)" unfolding xs_ys_def by (auto simp: o_def distinct_map inj_on_def)
  have p: "\<And> x y. (x,y) \<in> set ?xs_ys \<Longrightarrow> poly p x = y" unfolding xs_ys_def using p by auto
  have deg: "degree p < length ?xs_ys" unfolding xs_ys_def by simp
  have "newton_coefficients_main_int list (rev (map snd ?xs_ys)) (rev (map fst ?xs_ys)) = None"
  proof (induct xs_ys rule: rev_induct)
    case Nil
    show ?case unfolding list_def by (simp add: divmod_int_def)
  next
    case (snoc xy xs_ys) note IH = this
    obtain x y where xy: "xy = (x,y)" by force
    show ?case
    proof (cases xs_ys rule: rev_cases)
      case Nil
      show ?thesis unfolding Nil xy
        by (simp add: list_def divmod_int_def)
    next
      case (snoc xs_ys' xy')
      obtain x' y' where xy': "xy' = (x',y')" by force
      show ?thesis using IH unfolding xy' snoc xy by simp
    qed
  qed
  hence newton: "newton_interpolation_poly_int ?xs_ys = None"
    unfolding newton_interpolation_poly_int_def Let_def newton_poly_impl_int_def
      Newton_Interpolation.newton_coefficients_int_def list_def by simp
  from newton_interpolation_poly_int_None[OF dist newton p deg]
  show False .
qed
    
end
