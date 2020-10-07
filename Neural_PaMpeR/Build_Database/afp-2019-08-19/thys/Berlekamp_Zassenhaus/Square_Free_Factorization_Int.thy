(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
theory Square_Free_Factorization_Int
imports 
  Square_Free_Int_To_Square_Free_GFp 
  Suitable_Prime
  Code_Abort_Gcd
  Gcd_Finite_Field_Impl
begin

definition yun_wrel :: "int poly \<Rightarrow> rat \<Rightarrow> rat poly \<Rightarrow> bool" where
  "yun_wrel F c f = (map_poly rat_of_int F = smult c f)" 

definition yun_rel :: "int poly \<Rightarrow> rat \<Rightarrow> rat poly \<Rightarrow> bool" where
  "yun_rel F c f = (yun_wrel F c f
    \<and> content F = 1 \<and> lead_coeff F > 0 \<and> monic f)" 

definition yun_erel :: "int poly \<Rightarrow> rat poly \<Rightarrow> bool" where
  "yun_erel F f = (\<exists> c. yun_rel F c f)" 

lemma yun_wrelD: assumes "yun_wrel F c f"
  shows "map_poly rat_of_int F = smult c f" 
  using assms unfolding yun_wrel_def by auto

lemma yun_relD: assumes "yun_rel F c f"
  shows "yun_wrel F c f" "map_poly rat_of_int F = smult c f" 
    "degree F = degree f" "F \<noteq> 0" "lead_coeff F > 0" "monic f" 
    "f = 1 \<longleftrightarrow> F = 1" "content F = 1" 
proof -
  note * = assms[unfolded yun_rel_def yun_wrel_def, simplified]
  then have "degree (map_poly rat_of_int F) = degree f" by auto
  then show deg: "degree F = degree f" by simp
  show "F \<noteq> 0" "lead_coeff F > 0" "monic f" "content F = 1" 
    "map_poly rat_of_int F = smult c f"
    "yun_wrel F c f" using * by (auto simp: yun_wrel_def)
  {
    assume "f = 1" 
    with deg have "degree F = 0" by auto
    from degree0_coeffs[OF this] obtain c where F: "F = [:c:]" and c: "c = lead_coeff F" by auto
    from c * have c0: "c > 0" by auto
    hence cF: "content F = c" unfolding F content_def by auto
    with * have "c = 1" by auto
    with F have "F = 1" by simp
  }
  moreover
  {
    assume "F = 1"
    with deg have "degree f = 0" by auto
    with \<open>monic f\<close> have "f = 1" 
      using monic_degree_0 by blast
  }
  ultimately show "(f = 1) \<longleftrightarrow> (F = 1)" by auto
qed

lemma yun_erel_1_eq: assumes "yun_erel F f"
  shows "(F = 1) \<longleftrightarrow> (f = 1)" 
proof -
  from assms[unfolded yun_erel_def] obtain c where "yun_rel F c f" by auto
  from yun_relD[OF this] show ?thesis by simp
qed

lemma yun_rel_1[simp]: "yun_rel 1 1 1" 
  by (auto simp: yun_rel_def yun_wrel_def content_def)

lemma yun_erel_1[simp]: "yun_erel 1 1" unfolding yun_erel_def using yun_rel_1 by blast

lemma yun_rel_mult: "yun_rel F c f \<Longrightarrow> yun_rel G d g \<Longrightarrow> yun_rel (F * G) (c * d) (f * g)" 
  unfolding yun_rel_def yun_wrel_def content_mult lead_coeff_mult 
  by (auto simp: monic_mult hom_distribs)

lemma yun_erel_mult: "yun_erel F f \<Longrightarrow> yun_erel G g \<Longrightarrow> yun_erel (F * G) (f * g)" 
  unfolding yun_erel_def using yun_rel_mult[of F _ f G _ g] by blast

lemma yun_rel_pow: assumes "yun_rel F c f"
  shows "yun_rel (F^n) (c^n) (f^n)" 
  by (induct n, insert assms yun_rel_mult, auto)

lemma yun_erel_pow: "yun_erel F f \<Longrightarrow> yun_erel (F^n) (f^n)" 
  using yun_rel_pow unfolding yun_erel_def by blast

lemma yun_wrel_pderiv: assumes "yun_wrel F c f"
  shows "yun_wrel (pderiv F) c (pderiv f)" 
  by (unfold yun_wrel_def, simp add: yun_wrelD[OF assms] pderiv_smult hom_distribs)

lemma yun_wrel_minus: assumes "yun_wrel F c f" "yun_wrel G c g" 
  shows "yun_wrel (F - G) c (f - g)" 
  using assms unfolding yun_wrel_def by (auto simp: smult_diff_right hom_distribs)

lemma gcd_smult_left: assumes "c \<noteq> 0"
  shows "gcd (smult c f) g = gcd f (g :: 'b :: {field, factorial_ring_gcd} poly)"
proof -
  from assms have "normalize c = 1"
    by (meson dvd_field_iff is_unit_normalize)
  then show ?thesis
    by (metis (no_types) Polynomial.normalize_smult gcd.commute gcd.left_commute gcd_left_idem gcd_self smult_1_left)
qed

lemma gcd_smult_right: "c \<noteq> 0 \<Longrightarrow> gcd f (smult c g) = gcd f (g :: 'b :: {field, factorial_ring_gcd} poly)"
  using gcd_smult_left[of c g f] by (simp add: gcd.commute)

lemma gcd_rat_to_gcd_int: "gcd (of_int_poly f :: rat poly) (of_int_poly g) = 
  smult (inverse (of_int (lead_coeff (gcd f g)))) (of_int_poly (gcd f g))" 
proof (cases "f = 0 \<and> g = 0")
  case True
  thus ?thesis by simp
next
  case False
  let ?r = rat_of_int
  let ?rp = "map_poly ?r" 
  from False have gcd0: "gcd f g \<noteq> 0" by auto
  hence lc0: "lead_coeff (gcd f g) \<noteq> 0" by auto
  hence inv: "inverse (?r (lead_coeff (gcd f g))) \<noteq> 0" by auto
  show ?thesis
  proof (rule sym, rule gcdI, goal_cases)
    case 1
    have "gcd f g dvd f" by auto
    then obtain h where f: "f = gcd f g * h" unfolding dvd_def by auto    
    show ?case by (rule smult_dvd[OF _ inv], insert arg_cong[OF f, of ?rp], simp add: hom_distribs) 
  next
    case 2
    have "gcd f g dvd g" by auto
    then obtain h where g: "g = gcd f g * h" unfolding dvd_def by auto    
    show ?case by (rule smult_dvd[OF _ inv], insert arg_cong[OF g, of ?rp], simp add: hom_distribs) 
  next
    case (3 h)    
    show ?case 
    proof (rule dvd_smult)
      obtain ch ph where h: "rat_to_normalized_int_poly h = (ch, ph)" by force
      from 3 obtain ff where f: "?rp f = h * ff" unfolding dvd_def by auto
      from 3 obtain gg where g: "?rp g = h * gg" unfolding dvd_def by auto
      from rat_to_int_factor_explicit[OF f h] obtain f' where f: "f = ph * f'" by blast
      from rat_to_int_factor_explicit[OF g h] obtain g' where g: "g = ph * g'" by blast
      from f g have "ph dvd gcd f g" by auto
      then obtain gg where gcd: "gcd f g = ph * gg" unfolding dvd_def by auto
      note * = rat_to_normalized_int_poly[OF h]
      show "h dvd ?rp (gcd f g)" unfolding gcd *(1)
        by (rule smult_dvd, insert *(2), auto)
    qed
  next
    case 4
    show ?case unfolding normalize_poly_def 
      by (rule poly_eqI) (simp add: one_poly_def [symmetric])
  qed
qed


lemma yun_wrel_div: assumes f: "yun_wrel F c f" and g: "yun_wrel G d g" 
  and dvd: "G dvd F" "g dvd f" 
  and G0: "G \<noteq> 0" 
  shows "yun_wrel (F div G) (c / d) (f div g)" 
proof -
  let ?r = "rat_of_int" 
  let ?rp = "map_poly ?r" 
  from dvd obtain H h where fgh: "F = G * H" "f = g * h" unfolding dvd_def by auto
  from G0 yun_wrelD[OF g] have g0: "g \<noteq> 0" and d0: "d \<noteq> 0" by auto
  from arg_cong[OF fgh(1), of "\<lambda> x. x div G"] have H: "H = F div G" using G0 by simp
  from arg_cong[OF fgh(1), of ?rp] have "?rp F = ?rp G * ?rp H" by (auto simp: hom_distribs)
  from arg_cong[OF this, of "\<lambda> x. x div ?rp G"] G0 have id: "?rp H = ?rp F div ?rp G" by auto
  have "?rp (F div G) = ?rp F div ?rp G" unfolding H[symmetric] id by simp
  also have "\<dots> = smult c f div smult d g" using f g unfolding yun_wrel_def by auto
  also have "\<dots> = smult (c / d) (f div g)" unfolding div_smult_right[OF d0] div_smult_left
    by (simp add: field_simps)
  finally show ?thesis unfolding yun_wrel_def by simp
qed

lemma yun_rel_div: assumes f: "yun_rel F c f" and g: "yun_rel G d g" 
  and dvd: "G dvd F" "g dvd f" 
shows "yun_rel (F div G) (c / d) (f div g)" 
proof -
  note ff = yun_relD[OF f] 
  note gg = yun_relD[OF g]
  show ?thesis unfolding yun_rel_def
  proof (intro conjI)
    from yun_wrel_div[OF ff(1) gg(1) dvd gg(4)]
    show "yun_wrel (F div G) (c / d) (f div g)" by auto
    from dvd have fg: "f = g * (f div g)" by auto
    from arg_cong[OF fg, of monic] ff(6) gg(6) 
    show "monic (f div g)" using monic_factor by blast
    from dvd have FG: "F = G * (F div G)" by auto
    from arg_cong[OF FG, of content, unfolded content_mult] ff(8) gg(8)
    show "content (F div G) = 1" by simp
    from arg_cong[OF FG, of lead_coeff, unfolded lead_coeff_mult] ff(5) gg(5)
    show "lead_coeff (F div G) > 0" by (simp add: zero_less_mult_iff)
  qed
qed 
  


lemma yun_wrel_gcd: assumes "yun_wrel F c' f" "yun_wrel G c g" and c: "c' \<noteq> 0" "c \<noteq> 0" 
  and d: "d = rat_of_int (lead_coeff (gcd F G))" "d \<noteq> 0" 
  shows "yun_wrel (gcd F G) d (gcd f g)" 
proof -
  let ?r = "rat_of_int" 
  let ?rp = "map_poly ?r" 
  have "smult d (gcd f g) = smult d (gcd (smult c' f) (smult c g))" 
    by (simp add: c gcd_smult_left gcd_smult_right)
  also have "\<dots> = smult d (gcd (?rp F) (?rp G))" using assms(1-2)[unfolded yun_wrel_def] by simp
  also have "\<dots> = smult (d * inverse d) (?rp (gcd F G))" 
    unfolding gcd_rat_to_gcd_int d by simp
  also have "d * inverse d = 1" using d by auto
  finally show ?thesis  unfolding yun_wrel_def by simp
qed

lemma yun_rel_gcd: assumes f: "yun_rel F c f" and g: "yun_wrel G c' g"  and c': "c' \<noteq> 0" 
  and d: "d = rat_of_int (lead_coeff (gcd F G))"  
shows "yun_rel (gcd F G) d (gcd f g)" 
  unfolding yun_rel_def
proof (intro conjI)
  note ff = yun_relD[OF f]
  from ff have c0: "c \<noteq> 0" by auto
  from ff d have d0: "d \<noteq> 0" by auto
  from yun_wrel_gcd[OF ff(1) g c0 c' d d0]
  show "yun_wrel (gcd F G) d (gcd f g)" by auto
  from ff have "gcd f g \<noteq> 0" by auto
  thus "monic (gcd f g)" by (simp add: poly_gcd_monic)
  obtain H where H: "gcd F G = H" by auto
  obtain lc where lc: "coeff H (degree H) = lc" by auto
  from ff have "gcd F G \<noteq> 0" by auto
  hence "H \<noteq> 0" "lc \<noteq> 0" unfolding H[symmetric] lc[symmetric] by auto
  thus "0 < lead_coeff (gcd F G)" unfolding 
    arg_cong[OF normalize_gcd[of F G], of lead_coeff, symmetric]
    unfolding normalize_poly_eq_map_poly H
    by (auto, subst Polynomial.coeff_map_poly, auto, 
    subst Polynomial.degree_map_poly, auto simp: sgn_if)
  have "H dvd F" unfolding H[symmetric] by auto
  then obtain K where F: "F = H * K" unfolding dvd_def by auto
  from arg_cong[OF this, of content, unfolded content_mult ff(8)]
    content_ge_0_int[of H] have "content H = 1"
    by (auto simp add: zmult_eq_1_iff)
  thus "content (gcd F G) = 1" unfolding H .
qed
  


lemma yun_factorization_main_int: assumes f: "f = p div gcd p (pderiv p)"
    and "g = pderiv p div gcd p (pderiv p)" "monic p" 
    and "yun_gcd.yun_factorization_main gcd f g i hs = res"
    and "yun_gcd.yun_factorization_main gcd F G i Hs = Res" 
    and "yun_rel F c f" "yun_wrel G c g" "list_all2 (rel_prod yun_erel (=)) Hs hs"
  shows "list_all2 (rel_prod yun_erel (=)) Res res" 
proof -
  let ?P = "\<lambda> f g. \<forall> i hs res F G Hs Res c. 
    yun_gcd.yun_factorization_main gcd f g i hs = res
    \<longrightarrow> yun_gcd.yun_factorization_main gcd F G i Hs = Res 
    \<longrightarrow> yun_rel F c f \<longrightarrow> yun_wrel G c g \<longrightarrow> list_all2 (rel_prod yun_erel (=)) Hs hs
    \<longrightarrow> list_all2 (rel_prod yun_erel (=)) Res res" 
  note simps = yun_gcd.yun_factorization_main.simps
  note rel = yun_relD
  let ?rel = "\<lambda> F f. map_poly rat_of_int F = smult (rat_of_int (lead_coeff F)) f" 
  show ?thesis
  proof (induct rule: yun_factorization_induct[of ?P, rule_format, OF _ _ assms])
    case (1 f g i hs res F G Hs Res c)
    from rel[OF 1(4)] 1(1) have "f = 1" "F = 1" by auto
    from 1(2-3)[unfolded simps[of _ 1] this] have "res = hs" "Res = Hs" by auto
    with 1(6) show ?case by simp
  next
    case (2 f g i hs res F G Hs Res c)
    define d where "d = g - pderiv f" 
    define a where "a = gcd f d"  
    define D where "D = G - pderiv F" 
    define A where "A = gcd F D"  
    note f = 2(5)
    note g = 2(6)
    note hs = 2(7)
    note f1 = 2(1)
    from f1 rel[OF f] have *: "(f = 1) = False" "(F = 1) = False" and c: "c \<noteq> 0" by auto
    note res = 2(3)[unfolded simps[of _ f] * if_False Let_def, folded d_def a_def]
    note Res = 2(4)[unfolded simps[of _ F] * if_False Let_def, folded D_def A_def]
    note IH = 2(2)[folded d_def a_def, OF res Res]
    obtain c' where c': "c' = rat_of_int (lead_coeff (gcd F D))" by auto
    show ?case
    proof (rule IH)
      from yun_wrel_minus[OF g yun_wrel_pderiv[OF rel(1)[OF f]]]
      have d: "yun_wrel D c d" unfolding D_def d_def .
      have a: "yun_rel A c' a" unfolding A_def a_def
        by (rule yun_rel_gcd[OF f d c c'])
      hence "yun_erel A a" unfolding yun_erel_def by auto
      thus "list_all2 (rel_prod yun_erel (=)) ((A, i) # Hs) ((a, i) # hs)" 
        using hs by auto      
      have A0: "A \<noteq> 0" by (rule rel(4)[OF a])
      have "A dvd D" "a dvd d" unfolding A_def a_def by auto
      from yun_wrel_div[OF d rel(1)[OF a] this A0]
      show "yun_wrel (D div A) (c / c') (d div a)" .
      have "A dvd F" "a dvd f" unfolding A_def a_def by auto
      from yun_rel_div[OF f a this]
      show "yun_rel (F div A) (c / c') (f div a)" .
    qed
  qed
qed

lemma yun_monic_factorization_int_yun_rel: assumes  
    res: "yun_gcd.yun_monic_factorization gcd f = res"
    and Res: "yun_gcd.yun_monic_factorization gcd F = Res" 
    and f: "yun_rel F c f" 
  shows "list_all2 (rel_prod yun_erel (=)) Res res" 
proof -
  note ff = yun_relD[OF f]
  let ?g = "gcd f (pderiv f)"
  let ?yf = "yun_gcd.yun_factorization_main gcd (f div ?g) (pderiv f div ?g) 0 []" 
  let ?G = "gcd F (pderiv F)"
  let ?yF = "yun_gcd.yun_factorization_main gcd (F div ?G) (pderiv F div ?G) 0 []" 
  obtain r R where r: "?yf = r" and R: "?yF = R" by blast  
  from res[unfolded yun_gcd.yun_monic_factorization_def Let_def r]
  have res: "res = [(a, i)\<leftarrow>r . a \<noteq> 1]" by simp
  from Res[unfolded yun_gcd.yun_monic_factorization_def Let_def R]
  have Res: "Res = [(A, i)\<leftarrow>R . A \<noteq> 1]" by simp
  from yun_wrel_pderiv[OF ff(1)] have f': "yun_wrel (pderiv F) c (pderiv f)" .
  from ff have c: "c \<noteq> 0" by auto
  from yun_rel_gcd[OF f f' c refl] obtain d where g: "yun_rel ?G d ?g" ..
  from yun_rel_div[OF f g] have 1: "yun_rel (F div ?G) (c / d) (f div ?g)" by auto
  from yun_wrel_div[OF f' yun_relD(1)[OF g] _ _ yun_relD(4)[OF g]] 
  have 2: "yun_wrel (pderiv F div ?G) (c / d) (pderiv f div ?g)" by auto
  from yun_factorization_main_int[OF refl refl ff(6) r R 1 2] 
  have "list_all2 (rel_prod yun_erel (=)) R r" by simp
  thus ?thesis unfolding res Res
    by (induct R r rule: list_all2_induct, auto dest: yun_erel_1_eq)
qed

lemma yun_rel_same_right: assumes "yun_rel f c G" "yun_rel g d G" 
  shows "f = g" 
proof -
  note f = yun_relD[OF assms(1)]
  note g = yun_relD[OF assms(2)]
  let ?r = "rat_of_int" 
  let ?rp = "map_poly ?r" 
  from g have d: "d \<noteq> 0" by auto
  obtain a b where quot: "quotient_of (c / d) = (a,b)" by force
  from quotient_of_nonzero[of "c/d", unfolded quot] have b: "b \<noteq> 0" by simp
  note f(2)
  also have "smult c G = smult (c / d) (smult d G)" using d by (auto simp: field_simps)
  also have "smult d G = ?rp g" using g(2) by simp
  also have cd: "c / d = (?r a / ?r b)" using quotient_of_div[OF quot] .
  finally have fg: "?rp f = smult (?r a / ?r b) (?rp g)" by simp
  from f have "c \<noteq> 0" by auto
  with cd d have a: "a \<noteq> 0" by auto
  from arg_cong[OF fg, of "\<lambda> x. smult (?r b) x"]
  have "smult (?r b) (?rp f) = smult (?r a) (?rp g)" using b by auto
  hence "?rp (smult b f) = ?rp (smult a g)" by (auto simp: hom_distribs)
  then have fg: "[:b:] * f = [:a:] * g" by auto
  from arg_cong[OF this, of content, unfolded content_mult f(8) g(8)] 
  have "content [: b :] = content [: a :]" by simp
  hence abs: "abs a = abs b" unfolding content_def using b a by auto
  from arg_cong[OF fg, of "\<lambda> x. lead_coeff x > 0", unfolded lead_coeff_mult] f(5) g(5) a b 
  have "(a > 0) = (b > 0)" by (simp add: zero_less_mult_iff)
  with a b abs have "a = b" by auto
  with arg_cong[OF fg, of "\<lambda> x. x div [:b:]"] b show ?thesis
    by (metis nonzero_mult_div_cancel_left pCons_eq_0_iff)
qed



definition square_free_factorization_int_main :: "int poly \<Rightarrow> (int poly \<times> nat) list" where 
  "square_free_factorization_int_main f = (case square_free_heuristic f of None \<Rightarrow> 
    yun_gcd.yun_monic_factorization gcd f | Some p \<Rightarrow> [(f,0)])"

lemma square_free_factorization_int_main: assumes res: "square_free_factorization_int_main f = fs"
  and ct: "content f = 1" and lc: "lead_coeff f > 0" 
  and deg: "degree f \<noteq> 0" 
shows "square_free_factorization f (1,fs) \<and> (\<forall> fi i. (fi, i) \<in> set fs \<longrightarrow> content fi = 1 \<and> lead_coeff fi > 0) \<and>
  distinct (map snd fs)" 
proof (cases "square_free_heuristic f")
  case None  
  from lc have f0: "f \<noteq> 0" by auto
  from res None have fs: "yun_gcd.yun_monic_factorization gcd f = fs" 
    unfolding square_free_factorization_int_main_def by auto
  let ?r = "rat_of_int" 
  let ?rp = "map_poly ?r" 
  define G where "G = smult (inverse (lead_coeff (?rp f))) (?rp f)" 
  have "?rp f \<noteq> 0" using f0 by auto
  hence mon: "monic G" unfolding G_def coeff_smult by simp    
  obtain Fs where Fs: "yun_gcd.yun_monic_factorization gcd G = Fs" by blast
  from lc have lg: "lead_coeff (?rp f) \<noteq> 0" by auto
  let ?c = "lead_coeff (?rp f)" 
  define c where "c = ?c"
  have rp: "?rp f = smult c G" unfolding G_def c_def by (simp add: field_simps)
  have in_rel: "yun_rel f c G" unfolding yun_rel_def yun_wrel_def
    using rp mon lc ct by auto
  from yun_monic_factorization_int_yun_rel[OF Fs fs in_rel]
  have out_rel: "list_all2 (rel_prod yun_erel (=)) fs Fs" by auto
  from yun_monic_factorization[OF Fs mon]
  have "square_free_factorization G (1, Fs)" and dist: "distinct (map snd Fs)" by auto
  note sff = square_free_factorizationD[OF this(1)]
  from out_rel have "map snd fs = map snd Fs" by (induct fs Fs rule: list_all2_induct, auto)
  with dist have dist': "distinct (map snd fs)" by auto
  have main: "square_free_factorization f (1, fs) \<and> (\<forall> fi i. (fi, i) \<in> set fs \<longrightarrow> content fi = 1 \<and> lead_coeff fi > 0)"
    unfolding square_free_factorization_def split
  proof (intro conjI allI impI)
    from ct have "f \<noteq> 0" by auto
    thus "f = 0 \<Longrightarrow> 1 = 0" "f = 0 \<Longrightarrow> fs = []" by auto
    from dist' show "distinct fs" by (simp add: distinct_map)
    {
      fix a i
      assume a: "(a,i) \<in> set fs" 
      with out_rel obtain bj where "bj \<in> set Fs" and "rel_prod yun_erel (=) (a,i) bj" 
        unfolding list_all2_conv_all_nth set_conv_nth by fastforce
      then obtain b where b: "(b,i) \<in> set Fs" and ab: "yun_erel a b" by (cases bj, auto simp: rel_prod.simps)
      from sff(2)[OF b] have b': "square_free b" "degree b \<noteq> 0" by auto
      from ab obtain c where rel: "yun_rel a c b" unfolding yun_erel_def by auto
      note aa = yun_relD[OF this]
      from aa have c0: "c \<noteq> 0" by auto
      from b' aa(3) show "degree a > 0" by simp
      from square_free_smult[OF c0 b'(1), folded aa(2)]
      show "square_free a" unfolding square_free_def by (force simp: dvd_def hom_distribs)
      show cnt: "content a = 1" and lc: "lead_coeff a > 0" using aa by auto
      fix A I
      assume A: "(A,I) \<in> set fs" and diff: "(a,i) \<noteq> (A,I)" 
      from a[unfolded set_conv_nth] obtain k where k: "fs ! k = (a,i)" "k < length fs" by auto
      from A[unfolded set_conv_nth] obtain K where K: "fs ! K = (A,I)" "K < length fs" by auto
      from diff k K have kK: "k \<noteq> K" by auto
      from dist'[unfolded distinct_conv_nth length_map, rule_format, OF k(2) K(2) kK] 
      have iI: "i \<noteq> I" using k K by simp
      from A out_rel obtain Bj where "Bj \<in> set Fs" and "rel_prod yun_erel (=) (A,I) Bj" 
        unfolding list_all2_conv_all_nth set_conv_nth by fastforce
      then obtain B where B: "(B,I) \<in> set Fs" and AB: "yun_erel A B" by (cases Bj, auto simp: rel_prod.simps)
      then obtain C where Rel: "yun_rel A C B" unfolding yun_erel_def by auto
      note AA = yun_relD[OF this]
      from iI have "(b,i) \<noteq> (B,I)" by auto
      from sff(3)[OF b B this] have cop: "coprime b B" by simp
      from AA have C: "C \<noteq> 0" by auto
      from yun_rel_gcd[OF rel AA(1) C refl] obtain c where "yun_rel (gcd a A) c (gcd b B)" by auto
      note rel = yun_relD[OF this]
      from rel(2) cop have "?rp (gcd a A) = [: c :]" by simp
      from arg_cong[OF this, of degree] have "degree (gcd a A) = 0" by simp
      from degree0_coeffs[OF this] obtain c where gcd: "gcd a A = [: c :]" by auto
      from rel(8) rel(5) show "Rings.coprime a A"
        by (auto intro!: gcd_eq_1_imp_coprime simp add: gcd)
    }
    let ?prod = "\<lambda> fs. (\<Prod>(a, i)\<in>set fs. a ^ Suc i)" 
    let ?pr = "\<lambda> fs. (\<Prod>(a, i)\<leftarrow>fs. a ^ Suc i)"
    define pr where "pr = ?prod fs" 
    from \<open>distinct fs\<close> have pfs: "?prod fs = ?pr fs" by (rule prod.distinct_set_conv_list)
    from \<open>distinct Fs\<close> have pFs: "?prod Fs = ?pr Fs" by (rule prod.distinct_set_conv_list)
    from out_rel have "yun_erel (?prod fs) (?prod Fs)" unfolding pfs pFs
    proof (induct fs Fs rule: list_all2_induct)
      case (Cons ai fs Ai Fs)
      obtain a i where ai: "ai = (a,i)" by force
      from Cons(1) ai obtain A where Ai: "Ai = (A,i)" 
        and rel: "yun_erel a A" by (cases Ai, auto simp: rel_prod.simps)
      show ?case unfolding ai Ai using yun_erel_mult[OF yun_erel_pow[OF rel, of "Suc i"] Cons(3)]
        by auto
    qed simp
    also have "?prod Fs = G" using sff(1) by simp
    finally obtain d where rel: "yun_rel pr d G" unfolding yun_erel_def pr_def by auto
    with in_rel have "f = pr" by (rule yun_rel_same_right)
    thus "f = smult 1 (?prod fs)" unfolding pr_def by simp
  qed
  from main dist' show ?thesis by auto
next
  case (Some p)
  from res[unfolded square_free_factorization_int_main_def Some] have fs: "fs = [(f,0)]" by auto
  from lc have f0: "f \<noteq> 0" by auto
  from square_free_heuristic[OF Some] poly_mod_prime.separable_impl(1)[of p f] square_free_mod_imp_square_free[of p f] deg
  show ?thesis unfolding fs
    by (auto simp: ct lc square_free_factorization_def f0 poly_mod_prime_def)
qed

definition square_free_factorization_int' :: "int poly \<Rightarrow> int \<times> (int poly \<times> nat)list" where
  "square_free_factorization_int' f = (if degree f = 0
    then (lead_coeff f,[]) else (let \<comment> \<open>content factorization\<close>
      c = content f;
      d = (sgn (lead_coeff f) * c);
      g = sdiv_poly f d
      \<comment> \<open>and \<open>square_free\<close> factorization\<close>
    in (d, square_free_factorization_int_main g)))"


lemma square_free_factorization_int': assumes res: "square_free_factorization_int' f = (d, fs)"
  shows "square_free_factorization f (d,fs)" 
    "(fi, i) \<in> set fs \<Longrightarrow> content fi = 1 \<and> lead_coeff fi > 0" 
    "distinct (map snd fs)" 
proof -
  note res = res[unfolded square_free_factorization_int'_def Let_def]
  have "square_free_factorization f (d,fs) 
    \<and> ((fi, i) \<in> set fs \<longrightarrow> content fi = 1 \<and> lead_coeff fi > 0)
    \<and> distinct (map snd fs)"
  proof (cases "degree f = 0")
    case True
    from degree0_coeffs[OF True] obtain c where f: "f = [: c :]" by auto
    thus ?thesis using res by (simp add: square_free_factorization_def)
  next
    case False
    let ?s = "sgn (lead_coeff f)" 
    have s: "?s \<in> {-1,1}" using False unfolding sgn_if by auto
    define g where "g = smult ?s f" 
    let ?d = "?s * content f"
    have "content g = content ([:?s:] * f)" unfolding g_def by simp
    also have "\<dots> = content [:?s:] * content f" unfolding content_mult by simp
    also have "content [:?s:] = 1" using s by (auto simp: content_def)
    finally have cg: "content g = content f" by simp
    from False res 
    have d: "d = ?d" and fs: "fs = square_free_factorization_int_main (sdiv_poly f ?d)" by auto
    let ?g = "primitive_part g" 
    define ng where "ng = primitive_part g" 
    note fs
    also have "sdiv_poly f ?d = sdiv_poly g (content g)" unfolding cg unfolding g_def
      by (rule poly_eqI, unfold coeff_sdiv_poly coeff_smult, insert s, auto simp: div_minus_right)
    finally have fs: "square_free_factorization_int_main ng = fs" 
      unfolding primitive_part_alt_def ng_def by simp
    have "lead_coeff f \<noteq> 0" using False by auto
    hence lg: "lead_coeff g > 0" unfolding g_def lead_coeff_smult
      by (meson linorder_neqE_linordered_idom sgn_greater sgn_less zero_less_mult_iff)
    hence g0: "g \<noteq> 0" by auto
    from g0 have "content g \<noteq> 0" by simp
    from arg_cong[OF content_times_primitive_part[of g], of lead_coeff, unfolded lead_coeff_smult]
      lg content_ge_0_int[of g] have lg': "lead_coeff ng > 0" unfolding ng_def 
      by (metis \<open>content g \<noteq> 0\<close> dual_order.antisym dual_order.strict_implies_order zero_less_mult_iff)
    from content_primitive_part[OF g0] have c_ng: "content ng = 1" unfolding ng_def .
    have "degree ng = degree f" using \<open>content [:sgn (lead_coeff f):] = 1\<close> g_def ng_def
      by (auto simp add: sgn_eq_0_iff)
    with False have "degree ng \<noteq> 0" by auto
    note main = square_free_factorization_int_main[OF fs c_ng lg' this] 
    show ?thesis
    proof (intro conjI impI)
      {
        assume "(fi, i) \<in> set fs" 
        with main show "content fi = 1" "0 < lead_coeff fi" by auto
      }
      have d0: "d \<noteq> 0" using \<open>content [:?s:] = 1\<close> d by (auto simp:sgn_eq_0_iff)
      have "smult d ng = smult ?s (smult (content g) (primitive_part g))" 
        unfolding ng_def d cg by simp
      also have "smult (content g) (primitive_part g) = g" using content_times_primitive_part .
      also have "smult ?s g = f" unfolding g_def using s by auto
      finally have id: "smult d ng = f" .
      from main have "square_free_factorization ng (1, fs)" by auto
      from square_free_factorization_smult[OF d0 this]
      show "square_free_factorization f (d,fs)" unfolding id by simp
      show "distinct (map snd fs)" using main by auto
    qed
  qed
  thus  "square_free_factorization f (d,fs)" 
    "(fi, i) \<in> set fs \<Longrightarrow> content fi = 1 \<and> lead_coeff fi > 0" "distinct (map snd fs)" by auto
qed

 
definition x_split :: "'a :: semiring_0 poly \<Rightarrow> nat \<times> 'a poly" where
  "x_split f = (let fs = coeffs f; zs = takeWhile ((=) 0) fs
     in case zs of [] \<Rightarrow> (0,f) | _ \<Rightarrow> (length zs, poly_of_list (dropWhile ((=) 0) fs)))" 
  
lemma x_split: assumes "x_split f = (n, g)" 
  shows "f = monom 1 n * g" "n \<noteq> 0 \<or> f \<noteq> 0 \<Longrightarrow> \<not> monom 1 1 dvd g"
proof -
  define zs where "zs = takeWhile ((=) 0) (coeffs f)" 
  note res = assms[unfolded zs_def[symmetric] x_split_def Let_def]
  have "f = monom 1 n * g \<and> ((n \<noteq> 0 \<or> f \<noteq> 0) \<longrightarrow> \<not> (monom 1 1 dvd g))" (is "_ \<and> (_ \<longrightarrow> \<not> (?x dvd _))")
  proof (cases "f = 0")
    case True
    with res have "n = 0" "g = 0" unfolding zs_def by auto
    thus ?thesis using True by auto
  next
    case False note f = this
    show ?thesis
    proof (cases "zs = []")
      case True
      hence choice: "coeff f 0 \<noteq> 0" using f unfolding zs_def coeff_f_0_code poly_compare_0_code
        by (cases "coeffs f", auto)
      have dvd: "?x dvd h \<longleftrightarrow> coeff h 0 = 0" for h by (simp add: monom_1_dvd_iff')
      from True choice res f show ?thesis unfolding dvd by auto
    next
      case False
      define ys where "ys = dropWhile ((=) 0) (coeffs f)" 
      have dvd: "?x dvd h \<longleftrightarrow> coeff h 0 = 0" for h by (simp add: monom_1_dvd_iff')
      from res False have n: "n = length zs" and g: "g = poly_of_list ys" unfolding ys_def
        by (cases zs, auto)+
      obtain xx where xx: "coeffs f = xx" by auto
      have "coeffs f = zs @ ys" unfolding zs_def ys_def by auto
      also have "zs = replicate n 0" unfolding zs_def n xx by (induct xx, auto)
      finally have ff: "coeffs f = replicate n 0 @ ys" by auto
      from f have "lead_coeff f \<noteq> 0" by auto
      then have nz: "coeffs f \<noteq> []" "last (coeffs f) \<noteq> 0"
        by (simp_all add: last_coeffs_eq_coeff_degree)
      have ys: "ys \<noteq> []" using nz[unfolded ff] by auto            
      with ys_def have hd: "hd ys \<noteq> 0" by (metis (full_types) hd_dropWhile)
      hence "coeff (poly_of_list ys) 0 \<noteq> 0" unfolding poly_of_list_def coeff_Poly using ys by (cases ys, auto)
      moreover have "coeffs (Poly ys) = ys"
        by (simp add: ys_def strip_while_dropWhile_commute)
      then have "coeffs (monom_mult n (Poly ys)) = replicate n 0 @ ys"
        by (simp add: coeffs_eq_iff monom_mult_def [symmetric] ff ys monom_mult_code)
      ultimately show ?thesis unfolding dvd g
        by (auto simp add: coeffs_eq_iff monom_mult_def [symmetric] ff)
    qed
  qed
  thus "f = monom 1 n * g" "n \<noteq> 0 \<or> f \<noteq> 0 \<Longrightarrow> \<not> monom 1 1 dvd g" by auto
qed
      

definition square_free_factorization_int :: "int poly \<Rightarrow> int \<times> (int poly \<times> nat)list" where
  "square_free_factorization_int f = (case x_split f of (n,g) \<comment> \<open>extract \<open>x^n\<close>\<close>
    \<Rightarrow> case square_free_factorization_int' g of (d,fs)
    \<Rightarrow> if n = 0 then (d,fs) else (d, (monom 1 1, n - 1) # fs))" 

lemma square_free_factorization_int: assumes res: "square_free_factorization_int f = (d, fs)"
  shows "square_free_factorization f (d,fs)" 
    "(fi, i) \<in> set fs \<Longrightarrow> primitive fi \<and> lead_coeff fi > 0" 
proof -
  obtain n g where xs: "x_split f = (n,g)" by force
  obtain c hs where sf: "square_free_factorization_int' g = (c,hs)" by force
  from res[unfolded square_free_factorization_int_def xs sf split] 
  have d: "d = c" and fs: "fs = (if n = 0 then hs else (monom 1 1, n - 1) # hs)" by (cases n, auto)
  note sff = square_free_factorization_int'(1-2)[OF sf]
  note xs = x_split[OF xs]
  let ?x = "monom 1 1 :: int poly" 
  have x: "primitive ?x \<and> lead_coeff ?x = 1 \<and> degree ?x = 1"
    by (auto simp add: degree_monom_eq content_def monom_Suc)
  thus "(fi, i) \<in> set fs \<Longrightarrow> primitive fi \<and> lead_coeff fi > 0" using sff(2) unfolding fs
    by (cases n, auto)
  show "square_free_factorization f (d,fs)" 
  proof (cases n)
    case 0
    with d fs sff xs show ?thesis by auto
  next
    case (Suc m)
    with xs have fg: "f = monom 1 (Suc m) * g" and dvd: "\<not> ?x dvd g" by auto
    from Suc have fs: "fs = (?x,m) # hs" unfolding fs by auto
    have degx: "degree ?x = 1" by code_simp 
    from irreducible\<^sub>d_square_free[OF linear_irreducible\<^sub>d[OF this]] have sfx: "square_free ?x" by auto
    have fg: "f = ?x ^ n * g" unfolding fg Suc by (metis x_pow_n)
    have eq0: "?x ^ n * g = 0 \<longleftrightarrow> g = 0" by simp
    note sf = square_free_factorizationD[OF sff(1)]
    {
      fix a i
      assume ai: "(a,i) \<in> set hs" 
      with sf(4) have g0: "g \<noteq> 0" by auto
      from split_list[OF ai] obtain ys zs where hs: "hs = ys @ (a,i) # zs" by auto
      have "a dvd g" unfolding square_free_factorization_prod_list[OF sff(1)] hs
        by (rule dvd_smult, simp add: ac_simps)
      moreover have "\<not> ?x dvd g" using xs[unfolded Suc] by auto
      ultimately have dvd: "\<not> ?x dvd a" using dvd_trans by blast
      from sf(2)[OF ai] have "a \<noteq> 0" by auto
      have "1 = gcd ?x a"
      proof (rule gcdI)
        fix d
        assume d: "d dvd ?x" "d dvd a" 
        from content_dvd_contentI[OF d(1)] x have cnt: "is_unit (content d)" by auto
        show "is_unit d"
        proof (cases "degree d = 1")
          case False
          with divides_degree[OF d(1), unfolded degx] have "degree d = 0" by auto
          from degree0_coeffs[OF this] obtain c where dc: "d = [:c:]" by auto
          from cnt[unfolded dc] have "is_unit c" by (auto simp: content_def, cases "c = 0", auto)
          hence "d * d = 1" unfolding dc by (cases "c = -1"; cases "c = 1", auto)
          thus "is_unit d" by (metis dvd_triv_right)
        next
          case True
          from d(1) obtain e where xde: "?x = d * e" unfolding dvd_def by auto
          from arg_cong[OF this, of degree] degx have "degree d + degree e = 1"
            by (metis True add.right_neutral degree_0 degree_mult_eq one_neq_zero)
          with True have "degree e = 0" by auto
          from degree0_coeffs[OF this] xde obtain e where xde: "?x = [:e:] * d" by auto
          from arg_cong[OF this, of content, unfolded content_mult] x
          have "content [:e:] * content d = 1" by auto
          also have "content [:e :] = abs e" by (auto simp: content_def, cases "e = 0", auto)
          finally have "\<bar>e\<bar> * content d = 1" .
          from pos_zmult_eq_1_iff_lemma[OF this] have "e * e = 1" by (cases "e = 1"; cases "e = -1", auto)
          with arg_cong[OF xde, of "smult e"] have "d = ?x * [:e:]" by auto
          hence "?x dvd d" unfolding dvd_def by blast
          with d(2) have "?x dvd a" by (metis dvd_trans)
          with dvd show ?thesis by auto
        qed
      qed auto
      hence "coprime ?x a"
        by (simp add: gcd_eq_1_imp_coprime)
      note this dvd
    } note hs_dvd_x = this
    from hs_dvd_x[of ?x m]
    have nmem: "(?x,m) \<notin> set hs" by auto
    hence eq: "?x ^ n * g = smult c (\<Prod>(a, i)\<in>set fs. a ^ Suc i)" 
      unfolding sf(1) unfolding fs Suc by simp
    show ?thesis unfolding fg d unfolding square_free_factorization_def split eq0 unfolding eq
    proof (intro conjI allI impI, rule refl)
      fix a i 
      assume ai: "(a,i) \<in> set fs" 
      thus "square_free a" "degree a > 0" using sf(2) sfx degx unfolding fs by auto
      fix b j
      assume bj: "(b,j) \<in> set fs" and diff: "(a,i) \<noteq> (b,j)" 
      consider (hs_hs) "(a,i) \<in> set hs" "(b,j) \<in> set hs" 
        | (hs_x) "(a,i) \<in> set hs" "b = ?x" 
        | (x_hs) "(b,j) \<in> set hs" "a = ?x" 
        using ai bj diff unfolding fs by auto
      then show "Rings.coprime a b"
      proof cases
        case hs_hs
        from sf(3)[OF this diff] show ?thesis .
      next
        case hs_x
        from hs_dvd_x(1)[OF hs_x(1)] show ?thesis unfolding hs_x(2) by (simp add: ac_simps)
      next
        case x_hs
        from hs_dvd_x(1)[OF x_hs(1)] show ?thesis unfolding x_hs(2) by simp
      qed
    next
      show "g = 0 \<Longrightarrow> c = 0" using sf(4) by auto
      show "g = 0 \<Longrightarrow> fs = []" using sf(4) xs Suc by auto
      show "distinct fs" using sf(5) nmem unfolding fs by auto
    qed
  qed
qed

end
