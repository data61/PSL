section \<open>Separation of Roots: Sturm\<close>

text \<open>We adapt the existing theory on Sturm's theorem to work on rational numbers instead of real 
  numbers. The reason is that we want to implement real numbers as real algebraic numbers with the
  help of Sturm's theorem to separate the roots. To this end, we just copy the definitions of
  of the algorithms w.r.t. Sturm and let them be executed on rational numbers. We then
  prove that corresponds to a homomorphism and therefore can transfer the existing soundness results.\<close>

theory Sturm_Rat
imports 
  Sturm_Sequences.Sturm_Theorem
  Algebraic_Numbers_Prelim
begin

(* TODO: Move *)
lemma root_primitive_part [simp]:
  fixes p :: "'a :: {semiring_gcd, semiring_no_zero_divisors} poly"
  shows  "poly (primitive_part p) x = 0 \<longleftrightarrow> poly p x = 0"
proof(cases "p = 0")
  case True
  then show ?thesis by auto
next
  case False
  have "poly p x = content p * poly (primitive_part p) x"
    by (metis content_times_primitive_part poly_smult)
  also have "\<dots> = 0 \<longleftrightarrow> poly (primitive_part p) x = 0" by (simp add: False)
  finally show ?thesis by auto
qed

(*TODO: Move*)
lemma irreducible_primitive_part:
  assumes "irreducible p" and "degree p > 0"
  shows "primitive_part p = p"
  using irreducible_content[OF assms(1), unfolded primitive_iff_content_eq_1] assms(2)
  by (auto simp: primitive_part_def abs_poly_def)


subsection \<open>Interface for Separating Roots\<close>

text \<open>For a given rational polynomial, we need to know how many real roots are in a given closed interval,
  and how many real roots are in an interval $(-\infty,r]$.\<close>

datatype root_info = Root_Info (l_r: "rat \<Rightarrow> rat \<Rightarrow> nat") (number_root: "rat \<Rightarrow> nat")
hide_const (open) l_r
hide_const (open) number_root

definition count_roots_interval_sf :: "real poly \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> nat) \<times> (real \<Rightarrow> nat)" where
  "count_roots_interval_sf p = (let ps = sturm_squarefree p
    in ((\<lambda> a b. sign_changes ps a - sign_changes ps b + (if poly p a = 0 then 1 else 0)),
       (\<lambda> a. sign_changes_neg_inf ps - sign_changes ps a)))"

definition count_roots_interval :: "real poly \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> nat) \<times> (real \<Rightarrow> nat)" where
  "count_roots_interval p = (let ps = sturm p
    in ((\<lambda> a b. sign_changes ps a - sign_changes ps b + (if poly p a = 0 then 1 else 0)),
       (\<lambda> a. sign_changes_neg_inf ps - sign_changes ps a)))"

lemma count_roots_interval_iff: "square_free p \<Longrightarrow> count_roots_interval p = count_roots_interval_sf p"
  unfolding count_roots_interval_def count_roots_interval_sf_def sturm_squarefree_def
    square_free_iff_separable separable_def by (cases "p = 0", auto)

lemma count_roots_interval_sf: assumes p: "p \<noteq> 0" 
  and cr: "count_roots_interval_sf p = (cr,nr)"
  shows "a \<le> b \<Longrightarrow> cr a b = (card {x. a \<le> x \<and> x \<le> b \<and> poly p x = 0})"
    "nr a = card {x. x \<le> a \<and> poly p x = 0}"
proof -
  have id: "a \<le> b \<Longrightarrow> { x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} = 
    { x. a < x \<and> x \<le> b \<and> poly p x = 0} \<union> (if poly p a = 0 then {a} else {})" 
    (is "_ \<Longrightarrow> _ = ?R \<union> ?S") using not_less by force
  have RS: "finite ?R" "finite ?S" "?R \<inter> ?S = {}"  using p by (auto simp: poly_roots_finite)   
  show "a \<le> b \<Longrightarrow> cr a b = (card {x. a \<le> x \<and> x \<le> b \<and> poly p x = 0})"
    "nr a = card {x. x \<le> a \<and> poly p x = 0}" using cr unfolding arg_cong[OF id, of card] card_Un_disjoint[OF RS] 
    count_roots_interval_sf_def count_roots_between_correct[symmetric]
    count_roots_below_correct[symmetric] count_roots_below_def
    count_roots_between_def Let_def using p by auto
qed

lemma count_roots_interval: assumes cr: "count_roots_interval p = (cr,nr)"
  and sf: "square_free p"
  shows "a \<le> b \<Longrightarrow> cr a b = (card {x. a \<le> x \<and> x \<le> b \<and> poly p x = 0})"
    "nr a = card {x. x \<le> a \<and> poly p x = 0}"
  using count_roots_interval_sf[OF _ cr[unfolded count_roots_interval_iff[OF sf]]] 
    sf[unfolded square_free_def] by blast+

definition root_cond :: "int poly \<times> rat \<times> rat \<Rightarrow> real \<Rightarrow> bool" where
  "root_cond plr x = (case plr of (p,l,r) \<Rightarrow> of_rat l \<le> x \<and> x \<le> of_rat r \<and> ipoly p x = 0)"

definition root_info_cond :: "root_info \<Rightarrow> int poly \<Rightarrow> bool" where
  "root_info_cond ri p \<equiv> (\<forall> a b. a \<le> b \<longrightarrow> root_info.l_r ri a b = card {x. root_cond (p,a,b) x})
    \<and> (\<forall> a. root_info.number_root ri a = card {x. x \<le> real_of_rat a \<and> ipoly p x = 0})"

lemma root_info_condD: "root_info_cond ri p \<Longrightarrow> a \<le> b \<Longrightarrow> root_info.l_r ri a b = card {x. root_cond (p,a,b) x}"
  "root_info_cond ri p \<Longrightarrow> root_info.number_root ri a = card {x. x \<le> real_of_rat a \<and> ipoly p x = 0}"
  unfolding root_info_cond_def by auto

  
definition count_roots_interval_sf_rat :: "int poly \<Rightarrow> root_info" where
  "count_roots_interval_sf_rat  p = (let pp = real_of_int_poly p;
    (cr,nr) = count_roots_interval_sf pp
  in Root_Info (\<lambda> a b. cr (of_rat a) (of_rat b)) (\<lambda> a. nr (of_rat a)))"

definition count_roots_interval_rat :: "int poly \<Rightarrow> root_info" where
  [code del]: "count_roots_interval_rat  p = (let pp = real_of_int_poly p;
    (cr,nr) = count_roots_interval pp
  in Root_Info (\<lambda> a b. cr (of_rat a) (of_rat b)) (\<lambda> a. nr (of_rat a)))"

definition count_roots_rat :: "int poly \<Rightarrow> nat" where
  [code del]: "count_roots_rat  p = (count_roots (real_of_int_poly p))"

lemma count_roots_interval_sf_rat: assumes p: "p \<noteq> 0" 
  shows "root_info_cond (count_roots_interval_sf_rat p) p"
proof -  
  let ?p = "real_of_int_poly p"
  let ?r = real_of_rat
  let ?ri = "count_roots_interval_sf_rat p"
  from p have p: "?p \<noteq> 0" by auto
  obtain cr nr where cr: "count_roots_interval_sf ?p = (cr,nr)" by force
  have "?ri = Root_Info (\<lambda>a b. cr (?r a) (?r b)) (\<lambda>a. nr (?r a))"
    unfolding count_roots_interval_sf_rat_def Let_def cr by auto
  hence id: "root_info.l_r ?ri = (\<lambda>a b. cr (?r a) (?r b))" "root_info.number_root ?ri = (\<lambda>a. nr (?r a))"
    by auto
  note cr = count_roots_interval_sf[OF p cr]
  show ?thesis unfolding root_info_cond_def id
  proof (intro conjI impI allI)
    fix a
    show "nr (?r a) = card {x. x \<le> (?r a) \<and> ipoly p x = 0}"
      using cr(2)[of "?r a"] by simp
  next
    fix a b :: rat
    assume ab: "a \<le> b"
    from ab have ab: "?r a \<le> ?r b" by (simp add: of_rat_less_eq)
    from cr(1)[OF this] show "cr (?r a) (?r b) = card (Collect (root_cond (p, a, b)))"
      unfolding root_cond_def[abs_def] split by simp
  qed
qed
  
lemma of_rat_of_int_poly: "map_poly of_rat (of_int_poly p) = of_int_poly p" 
  by (subst map_poly_map_poly, auto simp: o_def)
  
lemma square_free_of_int_poly: assumes "square_free p" 
  shows "square_free (of_int_poly p :: 'a :: {field_gcd, field_char_0} poly)" 
proof - 
  have "square_free (map_poly of_rat (of_int_poly p) :: 'a poly)"
    unfolding of_rat_hom.square_free_map_poly by (rule square_free_int_rat[OF assms])
  thus ?thesis unfolding of_rat_of_int_poly .
qed

lemma count_roots_interval_rat: assumes sf: "square_free p"
  shows "root_info_cond (count_roots_interval_rat p) p"
proof -
  from sf have sf: "square_free (real_of_int_poly p)" by (rule square_free_of_int_poly)
  from sf have p: "p \<noteq> 0" unfolding square_free_def by auto
  show ?thesis
  using count_roots_interval_sf_rat[OF p]
  unfolding count_roots_interval_rat_def count_roots_interval_sf_rat_def 
    Let_def count_roots_interval_iff[OF sf] .
qed


lemma count_roots_rat: "count_roots_rat p = card {x. ipoly p x = (0 :: real)}"
  unfolding count_roots_rat_def count_roots_correct ..

subsection \<open>Implementing Sturm on Rational Polynomials\<close>

function sturm_aux_rat where
"sturm_aux_rat (p :: rat poly) q =
    (if degree q = 0 then [p,q] else p # sturm_aux_rat q (-(p mod q)))"
  by (pat_completeness, simp_all)
termination by (relation "measure (degree \<circ> snd)",
                simp_all add: o_def degree_mod_less')

lemma sturm_aux_rat: "sturm_aux (real_of_rat_poly p) (real_of_rat_poly q) = 
  map real_of_rat_poly (sturm_aux_rat p q)"
proof (induct p q rule: sturm_aux_rat.induct)
  case (1 p q)
  interpret map_poly_inj_idom_hom of_rat..
  note deg = of_int_hom.degree_map_poly_hom
  show ?case 
    unfolding sturm_aux.simps[of "real_of_rat_poly p"] sturm_aux_rat.simps[of p]
    using 1 by (cases "degree q = 0"; simp add: hom_distribs)
qed

definition sturm_rat where "sturm_rat p = sturm_aux_rat p (pderiv p)"

lemma sturm_rat: "sturm (real_of_rat_poly p) = map real_of_rat_poly (sturm_rat p)"
  unfolding sturm_rat_def sturm_def
  apply (fold of_rat_hom.map_poly_pderiv)
  unfolding sturm_aux_rat..

definition poly_number_rootat :: "rat poly \<Rightarrow> rat" where 
  "poly_number_rootat p \<equiv> sgn (coeff p (degree p))"

definition poly_neg_number_rootat :: "rat poly \<Rightarrow> rat" where 
  "poly_neg_number_rootat p \<equiv> if even (degree p) then sgn (coeff p (degree p))
                                       else -sgn (coeff p (degree p))"

lemma poly_number_rootat: "poly_inf (real_of_rat_poly p) = real_of_rat (poly_number_rootat p)"
  unfolding poly_inf_def poly_number_rootat_def of_int_hom.degree_map_poly_hom of_rat_hom.coeff_map_poly_hom
    real_of_rat_sgn by simp

lemma poly_neg_number_rootat: "poly_neg_inf (real_of_rat_poly p) = real_of_rat (poly_neg_number_rootat p)"
  unfolding poly_neg_inf_def poly_neg_number_rootat_def of_int_hom.degree_map_poly_hom of_rat_hom.coeff_map_poly_hom
    real_of_rat_sgn by (simp add:hom_distribs)

definition sign_changes_rat where
"sign_changes_rat ps (x::rat) =
    length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map (\<lambda>p. sgn (poly p x)) ps))) - 1"

definition sign_changes_number_rootat where
  "sign_changes_number_rootat ps = 
    length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map poly_number_rootat ps))) - 1"

definition sign_changes_neg_number_rootat where
  "sign_changes_neg_number_rootat ps = 
      length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map poly_neg_number_rootat ps))) - 1"

lemma real_of_rat_list_neq: "list_neq (map real_of_rat xs) 0 
  = map real_of_rat (list_neq xs 0)"
  by (induct xs, auto)

lemma real_of_rat_remdups_adj: "remdups_adj (map real_of_rat xs) = map real_of_rat (remdups_adj xs)"
  by (induct xs rule: remdups_adj.induct, auto)

lemma sign_changes_rat: "sign_changes (map real_of_rat_poly ps) (real_of_rat x)
  = sign_changes_rat ps x" (is "?l = ?r")
proof - 
  define xs where "xs = list_neq (map (\<lambda>p. sgn (poly p x)) ps) 0"
  have "?l = length (remdups_adj (list_neq (map real_of_rat (map (\<lambda>xa.  (sgn (poly xa x))) ps)) 0)) - 1"
    by (simp add: sign_changes_def real_of_rat_sgn o_def)
  also have "\<dots> = ?r" unfolding sign_changes_rat_def real_of_rat_list_neq 
    unfolding real_of_rat_remdups_adj by simp
  finally show ?thesis .
qed

lemma sign_changes_neg_number_rootat: "sign_changes_neg_inf (map real_of_rat_poly ps)
  =  sign_changes_neg_number_rootat ps" (is "?l = ?r")
proof - 
  have "?l = length (remdups_adj (list_neq (map real_of_rat (map poly_neg_number_rootat ps)) 0)) - 1"
    by (simp add: sign_changes_neg_inf_def o_def real_of_rat_sgn poly_neg_number_rootat)
  also have "\<dots> = ?r" unfolding sign_changes_neg_number_rootat_def real_of_rat_list_neq 
    unfolding real_of_rat_remdups_adj by simp
  finally show ?thesis .
qed

lemma sign_changes_number_rootat: "sign_changes_inf (map real_of_rat_poly ps)
  =  sign_changes_number_rootat ps" (is "?l = ?r")
proof - 
  have "?l = length (remdups_adj (list_neq (map real_of_rat (map poly_number_rootat ps)) 0)) - 1"
    unfolding sign_changes_inf_def
    unfolding map_map o_def real_of_rat_sgn poly_number_rootat ..
  also have "\<dots> = ?r" unfolding sign_changes_number_rootat_def real_of_rat_list_neq 
    unfolding real_of_rat_remdups_adj by simp
  finally show ?thesis .
qed

lemma count_roots_interval_rat_code[code]:
  "count_roots_interval_rat p = (let rp = map_poly rat_of_int p; ps = sturm_rat rp
    in Root_Info 
      (\<lambda> a b. sign_changes_rat ps a - sign_changes_rat ps b + (if poly rp a = 0 then 1 else 0))
      (\<lambda> a. sign_changes_neg_number_rootat ps - sign_changes_rat ps a))"
  unfolding count_roots_interval_rat_def Let_def count_roots_interval_def split of_rat_of_int_poly[symmetric, where 'a = real]
    sturm_rat sign_changes_rat 
    by (simp add: sign_changes_neg_number_rootat)

lemma count_roots_rat_code[code]:
  "count_roots_rat p = (let rp = map_poly rat_of_int p in if p = 0 then 0 else let ps = sturm_rat rp
    in sign_changes_neg_number_rootat ps - sign_changes_number_rootat ps)"
  unfolding count_roots_rat_def Let_def sturm_rat count_roots_code of_rat_of_int_poly[symmetric, where 'a = real]
    sign_changes_neg_number_rootat sign_changes_number_rootat
  by simp

hide_const (open) count_roots_interval_sf_rat

text \<open>Finally we provide an even more efficient implementation which
  avoids the "poly p x = 0" test, but it is restricted to irreducible polynomials.\<close>

definition root_info :: "int poly \<Rightarrow> root_info" where
  "root_info p = (if degree p = 1 then 
    (let x = Rat.Fract (- coeff p 0) (coeff p 1)
     in Root_Info (\<lambda> l r. if l \<le> x \<and> x \<le> r then 1 else 0)  (\<lambda> b. if x \<le> b then 1 else 0)) else 
    (let rp = map_poly rat_of_int p; ps = sturm_rat rp in 
   Root_Info (\<lambda> a b. sign_changes_rat ps a - sign_changes_rat ps b)
      (\<lambda> a. sign_changes_neg_number_rootat ps - sign_changes_rat ps a)))" 

lemma root_info:
  assumes irr: "irreducible p" and deg: "degree p > 0"
  shows "root_info_cond (root_info p) p"
proof (cases "degree p = 1")
  case deg: True
  from degree1_coeffs[OF this] obtain a b where p: "p = [:b,a:]" and "a \<noteq> 0" by auto
  from deg have "degree (real_of_int_poly p) = 1" by simp
  from roots1[OF this, unfolded roots1_def] p
  have id: "(ipoly p x = 0) = ((x :: real) = - b / a)" for x by auto
  have idd: "{x. real_of_rat aa \<le> x \<and>
                 x \<le> real_of_rat ba \<and> x = real_of_int (- b) / real_of_int a} 
   = (if real_of_rat aa \<le> real_of_int (- b) / real_of_int a \<and>
                 real_of_int (- b) / real_of_int a \<le> real_of_rat ba then {real_of_int (- b) / real_of_int a} else {})" 
    for aa ba by auto
  have iddd: "{x. x \<le> real_of_rat aa \<and> x = real_of_int (- b) / real_of_int a}
    = (if real_of_int (- b) / real_of_int a \<le> real_of_rat aa then {real_of_int (- b) / real_of_int a} else {})" for aa
    by auto
  have id4: "real_of_int x = real_of_rat (rat_of_int x)" for x by simp
  show ?thesis unfolding root_info_def deg unfolding root_info_cond_def id root_cond_def split
    unfolding p Fract_of_int_quotient Let_def idd iddd 
    unfolding id4 of_rat_divide[symmetric] of_rat_less_eq by auto
next
  case False
  have irr_d: "irreducible\<^sub>d p" by (simp add: deg irr irreducible_connect_rev)
  from irreducible\<^sub>d_int_rat[OF this]
  have "irreducible (of_int_poly p :: rat poly)" by auto
  from irreducible_root_free[OF this]
  have idd: "(poly (of_int_poly p) a = 0) = False" for a :: rat
    unfolding root_free_def using False by auto
  have id: "root_info p = count_roots_interval_rat p"
    unfolding root_info_def if_False count_roots_interval_rat_code Let_def idd using False by auto
  show ?thesis unfolding id
    by (rule count_roots_interval_rat[OF irreducible\<^sub>d_square_free[OF irr_d]])
qed

end
