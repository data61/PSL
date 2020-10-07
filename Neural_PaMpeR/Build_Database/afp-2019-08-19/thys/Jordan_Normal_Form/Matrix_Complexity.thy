(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Application: Complexity of Matrix Orderings\<close>

text \<open>In this theory we provide various carriers which can be used for matrix interpretations.\<close>

theory Matrix_Complexity 
imports
  Matrix_Comparison
  Complexity_Carrier
  Show_Arctic
begin

subsection \<open>Locales for Carriers of Matrix Interpretations and Polynomial Orders\<close>

locale matrix_carrier = SN_one_mono_ordered_semiring_1 d gt
  for gt :: "'a :: {show,ordered_semiring_1} \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succ>" 50) and d :: "'a"

locale mono_matrix_carrier = complexity_one_mono_ordered_semiring_1 gt d bound
  for gt :: "'a :: {show,large_real_ordered_semiring_1} \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succ>" 50) and d :: 'a
  and bound :: "'a \<Rightarrow> nat" 
+ fixes mono :: "'a \<Rightarrow> bool"
  assumes mono: "\<And> x y z. mono x \<Longrightarrow> y \<succ> z \<Longrightarrow> x \<ge> 0 \<Longrightarrow> x * y \<succ> x * z"


text \<open>The weak version make comparison with $>$ and then synthesize a suitable
  $\delta$-ordering by choosing the least difference in the finite set of
  comparisons.\<close>

locale weak_complexity_linear_poly_order_carrier = 
  fixes weak_gt :: "'a :: {large_real_ordered_semiring_1,show} \<Rightarrow> 'a \<Rightarrow> bool"
   and  default :: "'a"
   and  mono :: "'a \<Rightarrow> bool"
  assumes weak_gt_mono: "\<forall> x y. (x,y) \<in> set xys \<longrightarrow> weak_gt x y 
  \<Longrightarrow> \<exists> gt bound. mono_matrix_carrier gt default bound mono \<and> (\<forall> x y. (x,y) \<in> set xys \<longrightarrow> gt x y)"
begin

abbreviation weak_mat_gt :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "weak_mat_gt \<equiv> mat_gt weak_gt"

lemma weak_mat_gt_mono: assumes sd_n: "sd \<le> n" and
    orient: "\<And> A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow> (A,B) \<in> set ABs \<Longrightarrow> weak_mat_gt sd A B"
   shows "\<exists> gt bound. mono_matrix_carrier gt default bound mono 
   \<and> (\<forall> A B. A \<in> carrier_mat n n \<longrightarrow> B \<in> carrier_mat n n \<longrightarrow> (A, B) \<in> set ABs \<longrightarrow> mat_gt gt sd A B)"
proof -
  let ?n = "[0 ..< n]"
  let ?m1x = "[ A $$ (i,j) . A <- map fst ABs, i <- ?n, j <- ?n]"
  let ?m2y = "[ B $$ (i,j) . B <- map snd ABs, i <- ?n, j <- ?n]"
  let ?pairs = "concat (map (\<lambda> x. map (\<lambda> y. (x,y)) ?m2y) ?m1x)"
  let ?strict = "filter (\<lambda> (x,y). weak_gt x y) ?pairs"
  have "\<forall> x y. (x,y) \<in> set ?strict \<longrightarrow> weak_gt x y" by auto
  from weak_gt_mono[OF this] obtain gt bound where order: "mono_matrix_carrier gt default bound mono" 
    and orient2: "\<And> x y. (x, y) \<in> set ?strict \<Longrightarrow> gt x y" by auto
  show ?thesis
  proof (intro exI allI conjI impI, rule order)
    fix A B
    assume A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
      and AB: "(A, B) \<in> set ABs"          
    from orient[OF this] have "mat_gt weak_gt sd A B" by auto
    from mat_gtD[OF this] obtain i j where
      ge: "A \<ge>\<^sub>m B" and ij: "i < sd" "j < sd" and wgt: "weak_gt (A $$ (i,j)) (B $$ (i,j))"
      by auto
    from ij \<open>sd \<le> n\<close> have ij': "i < n" "j < n" by auto
    have gt: "gt (A $$ (i,j)) (B $$ (i,j))"
      by (rule orient2, insert ij' AB wgt, force)
    show "mat_gt gt sd A B" using ij gt ge by auto
  qed
qed
end

sublocale mono_matrix_carrier \<subseteq> SN_strict_mono_ordered_semiring_1 d gt mono
proof
  show "SN {(x,y). y \<ge> 0 \<and> x \<succ> y}" 
    unfolding SN_def
    by (intro allI deriv_bound_SN_on[OF bound])
qed (rule mono)

sublocale mono_matrix_carrier \<subseteq> matrix_carrier ..

subsection \<open>The Integers as Carrier\<close>

lemma int_complexity:
  "mono_matrix_carrier ((>) :: int \<Rightarrow> int \<Rightarrow> bool) 1 nat int_mono"
proof (unfold_locales)
  fix x
  let ?R = "{(x, y). 0 \<le> (y :: int) \<and> y < x}" 
  show "deriv_bound ?R x (nat x)"
    unfolding deriv_bound_def
  proof
    assume "(\<exists> y. (x,y) \<in> ?R ^^ Suc (nat x))"
    then obtain y where xy: "(x,y) \<in> ?R ^^ Suc (nat x)" ..
    from xy have y: "0 \<le> y" by auto
    obtain n where n: "n = Suc (nat x)" by auto
    from xy[unfolded n[symmetric]]
    have "x \<ge> y + int n"
    proof (induct n arbitrary: x y)
      case 0 thus ?case by auto
    next
      case (Suc n)
      from Suc(2) obtain z where xz: "(x,z) \<in> ?R ^^ n" and zy: "(z,y) \<in> ?R"
        by auto
      from Suc(1)[OF xz] have le: "z + int n \<le> x" .
      from zy have le2: "y + 1 \<le> z" by simp
      with le show ?case by auto
    qed
    with y have nx: "int n \<le> x" by simp
    from nx have x0: "x \<ge> 0" by simp
    with nx n
    show False by simp
  qed      
qed (insert int_SN.mono, auto)

lemma int_weak_complexity:
  "weak_complexity_linear_poly_order_carrier (>) 1 int_mono"
  by (unfold_locales, intro exI[of _ "(>)"] exI[of _ nat] conjI, rule int_complexity, auto)

subsection \<open>The Rational and Real Numbers as Carrier\<close>

definition delta_bound :: "'a :: floor_ceiling \<Rightarrow> 'a \<Rightarrow> nat"
where
  "delta_bound d x = nat (ceiling (x * of_int (ceiling (1 / d))))"

lemma delta_complexity:
  assumes d0: "d > 0" and d1: "d \<le> def" 
  shows "mono_matrix_carrier (delta_gt d) def (delta_bound d) delta_mono"
proof -
  from d0 have d00: "0 \<le> d" by simp
  define N where "N = ceiling (1 / d)"
  let ?N = "of_int N :: 'a"
  from d0 have "1 / d > 0" by (auto simp: field_simps)
  with ceiling_correct[of "1 / d"] have Nd: "1 / d \<le> ?N" and N: "N > 0" unfolding N_def by auto
  let ?nat = "\<lambda> x. nat (ceiling (x * ?N))"
  let ?gt = "delta_gt d"
  have nn: "delta_bound d = ?nat" unfolding fun_eq_iff N_def by (simp add: delta_bound_def)
  from delta_interpretation[OF d0 d1]
  interpret SN_strict_mono_ordered_semiring_1 "def" ?gt delta_mono .
  show ?thesis unfolding nn
  proof(unfold_locales)
    show "?nat 0 = 0" by auto
  next
    fix x y :: 'a
    assume xy: "x \<ge> y"
    show "?nat x \<ge> ?nat y" 
      by (rule nat_mono, rule ceiling_mono, insert xy N, auto simp: field_simps)
  next
    have "1 \<le> nat 1" by simp
    also have "... \<le> ?nat 1"
    proof (rule nat_mono)
      have "1 = ceiling (1 :: rat)" by simp
      also have "... \<le> ceiling (1 * ?N)" using N by simp
      finally show "1 \<le> ceiling (1 * ?N)" .
    qed
    finally show "1 \<le> ?nat 1" .
  next
    fix x y :: 'a
    have "ceiling ((x + y) * ?N) = ceiling (x * ?N + y * ?N)" by (simp add: field_simps)
    also have "... \<le> ceiling (x * ?N) + ceiling (y * ?N)" by (rule ceiling_add_le)
    finally show "?nat (x + y) \<le> ?nat x + ?nat y" by auto
  next
    fix x :: 'a and n :: nat
    assume x: "0 \<le> x" 
    interpret mono_matrix_carrier "(>)" 1 nat int_mono by (rule int_complexity)
    have "?nat (x + of_nat n) = nat (ceiling (x * ?N + of_nat n * ?N))" 
      by (simp add: field_simps)
    also have id: "of_nat n * ?N = of_int (of_nat (n * nat N))" using N by (simp add: field_simps)
    also have "ceiling (x * ?N + of_int (of_nat (n * nat N))) = ceiling (x * ?N) + of_nat (n * nat N)" unfolding ceiling_add_of_int ..
    also have "nat (ceiling (x * ?N) + of_nat (n * nat N)) = ?nat x + nat (int (n * nat N))"
    proof (rule bound_plus_of_nat)
      have "x * ?N \<ge> 0" 
        by (rule mult_nonneg_nonneg, insert x N, auto)
      thus "ceiling (x * ?N) \<ge> 0" by auto
    qed 
    also have "(nat (int (n * nat N))) = n * nat N" by presburger
    also have "n * nat N = ?nat (of_nat n)" using N by (metis id ceiling_of_int nat_int)
    finally
    show "?nat (x + of_nat n) = ?nat x + ?nat (of_nat n)" .
  next
    fix x y z :: 'a
    assume *: "delta_mono x" "delta_gt d y z" and x: "0 \<le> x"
    from mono[OF * x]
    show "delta_gt d (x * y) (x * z)" .
  next
    fix x :: 'a
    let ?R = "{(x,y). 0 \<le> y \<and> ?gt x y}"
    show "deriv_bound ?R x (?nat x)" unfolding deriv_bound_def
    proof
      assume "(\<exists> y. (x,y) \<in> ?R ^^ Suc (?nat x))"
      then obtain y where xy: "(x,y) \<in> ?R ^^ Suc (?nat x)" ..
      from xy have y: "0 \<le> y" by auto
      obtain n where n: "n = Suc (?nat x)" by auto
      from xy[unfolded n[symmetric]]
      have "x \<ge> y + d * of_nat n"
      proof (induct n arbitrary: x y)
        case 0 thus ?case by auto
      next
        case (Suc n)
        from Suc(2) obtain z where xz: "(x,z) \<in> ?R ^^ n" and zy: "(z,y) \<in> ?R"
          by auto
        from Suc(1)[OF xz] have le: "z + d * of_nat n \<le> x" .
        from zy[unfolded delta_gt_def] have le2: "y + d \<le> z" by simp
        with le show ?case by (auto simp: field_simps)
      qed
      with y have nx: "d * of_nat n \<le> x" by simp
      have "0 \<le> d * of_nat n" by (rule mult_nonneg_nonneg, insert d00, auto)
      with nx have x0: "x \<ge> 0" by auto
      have xd0: "0 \<le> x / d"
        by (rule divide_nonneg_pos[OF x0 d0])
      from nx[unfolded n]      
      have "d + d * of_nat (?nat x) \<le> x" by (simp add: field_simps)
      with d0 have less: "d * of_nat (?nat x) < x" by simp
      from Nd d0 have "1 \<le> d * ?N" by (auto simp: field_simps)
      from mult_left_mono[OF this x0]
      have "x \<le> d * (x * ?N)" by (simp add: ac_simps)
      also have "\<dots> \<le> d * of_nat (?nat x)"
      proof (rule mult_left_mono[OF _ d00])
        show "x * ?N \<le> of_nat (nat \<lceil>x * ?N\<rceil>)" using x0 ceiling_correct[of "x * ?N"] 
          by (metis int_nat_eq le_cases of_int_0_le_iff of_int_of_nat_eq order_trans)
      qed
      also have "\<dots> < x" using less .
      finally show False by simp
    qed
  qed 
qed


lemma delta_weak_complexity_carrier:
  assumes d0: "def > 0" 
  shows "weak_complexity_linear_poly_order_carrier (>) def delta_mono"
proof
  fix xys :: "('a \<times> 'a) list"
  assume ass: "\<forall>x y. (x, y) \<in> set xys \<longrightarrow> y < x"
  let ?cs = "map (\<lambda> (x,y). x - y) xys"
  let ?ds = "def # ?cs"
  define d where "d = Min (set ?ds)"
  have d: "d \<le> def" and dcs: "\<And> x. x \<in> set ?cs \<Longrightarrow> d \<le> x" unfolding d_def by auto
  have "d \<in> set ?ds" unfolding d_def by (rule Min_in, auto)
  hence "d = def \<or> d \<in> set ?cs" by auto
  hence d0: "d > 0"
    by (cases, insert d0 ass, auto simp: field_simps)
  show "\<exists>gt bound. mono_matrix_carrier gt def bound delta_mono \<and> (\<forall>x y. (x, y) \<in> set xys \<longrightarrow> gt x y)"
    by (intro exI conjI, rule delta_complexity[OF d0 d], insert dcs, force simp: delta_gt_def)
qed

subsection \<open>The Arctic Numbers as Carrier\<close>

lemma arctic_delta_weak_carrier:
  "weak_SN_both_mono_ordered_semiring_1 weak_gt_arctic_delta 1 pos_arctic_delta" ..

lemma arctic_weak_carrier:
  "weak_SN_both_mono_ordered_semiring_1 (>) 1 pos_arctic"
proof -
  have SN: "SN_both_mono_ordered_semiring_1 1 (>) pos_arctic" ..
  show ?thesis
    by (unfold_locales, intro conjI exI, rule SN, auto)
qed

end
