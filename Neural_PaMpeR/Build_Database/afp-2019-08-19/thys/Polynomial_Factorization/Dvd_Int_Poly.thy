(*  
    Author:      Sebastiaan Joosten
                 René Thiemann                  
    License:     BSD
*)

section \<open>Division of Polynomials over Integers\<close>

text \<open>This theory contains an algorithm to efficiently compute
  divisibility of two integer polynomials.\<close>

theory Dvd_Int_Poly
imports
  Polynomial_Interpolation.Ring_Hom_Poly
  Polynomial_Interpolation.Divmod_Int
  Polynomial_Interpolation.Is_Rat_To_Rat
begin

definition div_int_poly_step :: "int poly \<Rightarrow> int \<Rightarrow> (int poly \<times> int poly) option \<Rightarrow> (int poly \<times> int poly) option" where
 "div_int_poly_step q = (\<lambda>a sro. case sro of Some (s, r) \<Rightarrow>
      let ar = pCons a r; (b,m) = divmod_int (coeff ar (degree q)) (coeff q (degree q))
      in if m = 0 then Some (pCons b s, ar - smult b q) else None | None \<Rightarrow> None)"

declare div_int_poly_step_def[code_unfold]

definition div_mod_int_poly :: "int poly \<Rightarrow> int poly \<Rightarrow> (int poly \<times> int poly) option" where
 "div_mod_int_poly p q = (if q = 0 then None
    else (let n = degree q; qn = coeff q n
    in fold_coeffs (div_int_poly_step q) p (Some (0, 0))))"

definition div_int_poly :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly option" where
  "div_int_poly p q = 
    (case div_mod_int_poly p q of None \<Rightarrow> None | Some (d,m) \<Rightarrow> if m = 0 then Some d else None)"

definition div_rat_poly_step :: "'a::field poly \<Rightarrow> 'a \<Rightarrow> 'a poly \<times> 'a poly \<Rightarrow> 'a poly \<times> 'a poly" where
   "div_rat_poly_step q = (\<lambda>a (s, r).
      let b = coeff (pCons a r) (degree q) / coeff q (degree q)
      in (pCons b s, pCons a r - smult b q))"

lemma foldr_cong_plus: (* a more elaborate version of foldr_cong. Using f'=id, g'=id and s = set lst would give foldr_cong exactly. *)
  assumes f_is_g : "\<And> a b c. b \<in> s \<Longrightarrow> f' a = f b (f' c) \<Longrightarrow> g' a = g b (g' c)" (* main assumption *)
      and f'_inj : "\<And> a b. f' a = f' b \<Longrightarrow> a = b"
      and f_bit_sur : "\<And> a b c. f' a = f b c \<Longrightarrow> \<exists> c'. c = f' c'" (* should be provable by cases c *)
      and lst_in_s : "set lst \<subseteq> s" (* formulated like this to make induction easier *)
  shows "f' a = foldr f lst (f' b) \<Longrightarrow> g' a = foldr g lst (g' b)"
using lst_in_s
proof (induct lst arbitrary: a)
  case (Cons x xs)
  have prems: "f' a = (f x \<circ> foldr f xs) (f' b)" using Cons.prems unfolding foldr_Cons by auto
  hence "\<exists> c'. f' c' = foldr f xs (f' b)" using f_bit_sur by fastforce
  then obtain c' where c'_def: "f' c' = foldr f xs (f' b)" by blast
  hence "f' a = f x (f' c')" using prems by simp
  hence "g' a = g x (g' c')" using f_is_g Cons.prems(2) by simp
  also have "g' c' = foldr g xs (g' b)" using Cons.hyps[of c'] c'_def Cons.prems(2) by auto
  finally have "g' a = (g x \<circ> foldr g xs) (g' b)" by simp
  thus ?case using foldr_Cons by simp
qed (insert f'_inj, auto)

abbreviation (input) rp :: "int poly \<Rightarrow> rat poly" where 
  "rp \<equiv> map_poly rat_of_int"

(* fully transitive proof, right to left also holds without the precondition: 
     int_step_then_rat_poly_step
   Left to right holds if q\<noteq>0: rat_poly_step_then_int_step *)
lemma rat_int_poly_step_agree :
  assumes "coeff (pCons b c2) (degree q) mod coeff q (degree q) = 0"
  shows "(rp a1,rp a2) = (div_rat_poly_step (rp q) \<circ> rat_of_int) b (rp c1,rp c2)
         \<longleftrightarrow> Some (a1,a2) = div_int_poly_step q b (Some (c1,c2))"
proof -
  have coeffs: "coeff (pCons b c2) (degree q) mod coeff q (degree q) = 0" using assms by auto
  let ?ri = "rat_of_int"
  let ?withDiv1 = "pCons (?ri (coeff (pCons b c2) (degree q) div coeff q (degree q))) (rp c1)"
  let ?withSls1 = "pCons (coeff (pCons (?ri b) (rp c2)) (degree q) / coeff (rp q) (degree q)) (rp c1)"
  let ?ident1 = "?withDiv1 = ?withSls1"
  let ?withDiv2 = "rp (pCons b c2 - smult (coeff (pCons b c2) (degree q) div coeff q (degree q)) q)"
  let ?withSls2 = "pCons (?ri b) (rp c2) - smult (coeff (pCons (?ri b) (rp c2)) (degree q) / coeff (rp q) (degree q)) (rp q)"
  let ?ident2 = "?withDiv2 = ?withSls2"
  note simps = div_int_poly_step_def option.simps Let_def prod.simps
  have id1:"?ri (coeff (pCons b c2) (degree q) div coeff q (degree q)) = 
            ?ri (coeff (pCons b c2) (degree q)) / ?ri (coeff q (degree q))" using coeffs by auto
  have id2:"?ident1" unfolding id1
    by (simp, fold of_int_hom.coeff_map_poly_hom of_int_hom.map_poly_pCons_hom, simp)
  hence id3:"?ident2" using id2 by (auto simp: hom_distribs)

  have c1:"((rp (pCons (coeff (pCons b c2) (degree q) div coeff q (degree q)) c1)
            ,rp (pCons b c2 - smult (coeff (pCons b c2) (degree q) div coeff q (degree q)) q))
           = div_rat_poly_step (rp q) (?ri b) (rp c1,rp c2)) \<longleftrightarrow> (?ident1 \<and> ?ident2)"
    unfolding div_rat_poly_step_def simps
    by (simp add: hom_distribs)
  have "((rp a1, rp a2) = (div_rat_poly_step (rp q) \<circ> rat_of_int) b (rp c1, rp c2)) \<longleftrightarrow>
             (rp a1 = ?withSls1 \<and> rp a2 = ?withSls2)"
    unfolding div_rat_poly_step_def simps by simp
  also have "\<dots> \<longleftrightarrow>
      ((a1 = pCons (coeff (pCons b c2) (degree q) div coeff q (degree q)) c1) \<and>
       (a2 = pCons b c2 - smult (coeff (pCons b c2) (degree q) div coeff q (degree q)) q))"
    by (fold id2 id3 of_int_hom.map_poly_pCons_hom, unfold of_int_poly_hom.eq_iff, auto)
  also have c0:"\<dots> \<longleftrightarrow> Some (a1,a2) = div_int_poly_step q b (Some (c1,c2))" 
    unfolding divmod_int_def div_int_poly_step_def option.simps Let_def prod.simps
    using coeffs by (auto split: option.splits prod.splits if_splits)
  finally show ?thesis .
qed

lemma int_step_then_rat_poly_step :
  assumes Some:"Some (a1,a2) = div_int_poly_step q b (Some (c1,c2))"
  shows "(rp a1,rp a2) = (div_rat_poly_step (rp q) \<circ> rat_of_int) b (rp c1,rp c2)"
proof -
  note simps = div_int_poly_step_def option.simps Let_def divmod_int_def prod.simps
  from Some[unfolded simps] have mod0: "coeff (pCons b c2) (degree q) mod coeff q (degree q) = 0" 
    by (auto split: option.splits prod.splits if_splits)
  thus ?thesis using assms rat_int_poly_step_agree by auto
qed

lemma is_int_rat_division : 
  assumes "y \<noteq> 0"
  shows "is_int_rat (rat_of_int x / rat_of_int y) \<longleftrightarrow> x mod y = 0"
proof
  assume "is_int_rat (rat_of_int x / rat_of_int y)"
  then obtain v where v_def:"rat_of_int v = rat_of_int x / rat_of_int y"
                using int_of_rat(2) is_int_rat by fastforce
  hence "v = \<lfloor>rat_of_int x / rat_of_int y\<rfloor>" by linarith
  hence "v * y = x - x mod y" using div_is_floor_divide_rat mod_div_equality_int by simp
  hence "rat_of_int v * rat_of_int y = rat_of_int x - rat_of_int (x mod y)"
    by (fold hom_distribs, unfold of_int_hom.eq_iff)
  hence "(rat_of_int x / rat_of_int y) * rat_of_int y = rat_of_int x - rat_of_int (x mod y)"
    using v_def by simp
  hence "rat_of_int x = rat_of_int x - rat_of_int (x mod y)" by (simp add: assms)
  thus "x mod y = 0" by simp
qed (force)

lemma pCons_of_rp_contains_ints :
  assumes "rp a = pCons b c"
    shows "is_int_rat b"
proof -
  have "\<And> b n. rp a = b \<Longrightarrow> is_int_rat (coeff b n)" by auto
  hence "rp a = pCons b c \<Longrightarrow> is_int_rat (coeff (pCons b c) 0)".
  thus ?thesis using assms by auto
qed

lemma rat_step_then_int_poly_step :
  assumes "q \<noteq> 0"
      and "(rp a1,rp a2) = (div_rat_poly_step (rp q) \<circ> rat_of_int) b2 (rp c1,rp c2)"
  shows "Some (a1,a2) = div_int_poly_step q b2 (Some (c1,c2))"
proof -
  let ?mustbeint = "rat_of_int (coeff (pCons b2 c2) (degree q)) / rat_of_int (coeff q (degree q))"
  let ?mustbeint2 = "coeff (pCons (rat_of_int b2) (rp c2)) (degree (rp q)) 
    / coeff (rp q) (degree (rp q))"
  have mustbeint : "?mustbeint = ?mustbeint2" by (fold hom_distribs of_int_hom.coeff_map_poly_hom, simp)
  note simps = div_int_poly_step_def option.simps Let_def divmod_int_def prod.simps
  from assms leading_coeff_neq_0[of q] have q0:"coeff q (degree q) \<noteq> 0" by simp

  have "rp a1 = pCons ?mustbeint2 (rp c1)"
    using assms(2) unfolding div_rat_poly_step_def by (simp add:div_int_poly_step_def Let_def)
  hence "is_int_rat ?mustbeint2"
    unfolding div_rat_poly_step_def using pCons_of_rp_contains_ints by simp
  hence "is_int_rat ?mustbeint" unfolding mustbeint by simp
  hence "coeff (pCons b2 c2) (degree q) mod coeff q (degree q) = 0"
    using is_int_rat_division q0 by simp
  thus ?thesis using rat_int_poly_step_agree assms by simp
qed

lemma div_int_poly_step_surjective : "Some a = div_int_poly_step q b c \<Longrightarrow> \<exists> c'. c = Some c'"
  unfolding div_int_poly_step_def by(cases c, simp_all)

lemma  div_mod_int_poly_then_pdivmod:
  assumes "div_mod_int_poly p q = Some (r,m)"
  shows   "(rp p div rp q, rp p mod rp q) = (rp r, rp m)"
    and   "q \<noteq> 0"
proof -
  let ?rpp = "(\<lambda> (a,b). (rp a,rp b))"
  let ?p = "rp p"
  let ?q = "rp q"
  let ?r = "rp r"
  let ?m = "rp m"
  let ?div_rat_step = "div_rat_poly_step ?q"
  let ?div_int_step = "div_int_poly_step q"
  from assms show q0 : "q \<noteq> 0" using div_mod_int_poly_def by auto
  hence "div_mod_int_poly p q = Some (r,m) \<longleftrightarrow> Some (r,m) = foldr (div_int_poly_step q) (coeffs p) (Some (0, 0))"
    unfolding div_mod_int_poly_def fold_coeffs_def by (auto split: option.splits prod.splits if_splits)
  hence innerRes: "Some (r,m) = foldr (?div_int_step) (coeffs p) (Some (0, 0))" using assms by simp
  { fix oldRes res :: "int poly \<times> int poly"
    fix lst :: "int list"
    have "Some res = foldr ?div_int_step lst (Some oldRes) \<Longrightarrow>
          ?rpp res = foldr (?div_rat_step \<circ> rat_of_int) lst (?rpp oldRes)"
      using foldr_cong_plus[of "set lst" Some ?div_int_step ?rpp "?div_rat_step \<circ> rat_of_int" 
        lst res oldRes] int_step_then_rat_poly_step div_int_poly_step_surjective by auto
    hence "Some res = foldr ?div_int_step lst (Some oldRes) 
      \<Longrightarrow> ?rpp res = foldr ?div_rat_step (map rat_of_int lst) (?rpp oldRes)" 
      using foldr_map[of ?div_rat_step rat_of_int lst] by simp
  }
  hence equal_foldr : "Some (r,m) = foldr (?div_int_step) (coeffs p) (Some (0,0)) 
    \<Longrightarrow> ?rpp (r,m) = foldr (?div_rat_step) (map rat_of_int (coeffs p)) (?rpp (0,0))".
  have "(map rat_of_int (coeffs p) = coeffs ?p)" by simp
  hence "(?r,?m) = (foldr (?div_rat_step) (coeffs ?p) (0,0))" using equal_foldr innerRes by simp
  thus "(?p div ?q, ?p mod ?q) = (?r,?m)" 
    using fold_coeffs_def [of "?div_rat_step" ?p] q0 
      div_mod_fold_coeffs [of ?p ?q]
    unfolding div_rat_poly_step_def by auto
qed

lemma div_rat_poly_step_sur:
 assumes "(case a of (a, b) \<Rightarrow> (rp a, rp b)) = (div_rat_poly_step (rp q) \<circ> rat_of_int) x pair"
   shows "\<exists>c'. pair = (case c' of (a, b) \<Rightarrow> (rp a, rp b))"
proof -
  obtain b1 b2 where pair: "pair = (b1, b2)" by (cases pair) simp
  define p12 where "p12 = coeff (pCons (rat_of_int x) b2) (degree (rp q)) / coeff (rp q) (degree (rp q))"
  obtain a1 a2 where "a = (a1, a2)" by (cases a) simp
  with assms pair have "(rp a1, rp a2) = div_rat_poly_step (rp q) (rat_of_int x) (b1, b2)"
    by simp    
  then have a1: "rp a1 = pCons p12 b1"
    and "rp a2 = pCons (rat_of_int x) b2 - smult p12 (rp q)"
    by (auto split: prod.splits simp add: Let_def div_rat_poly_step_def p12_def)
  then obtain p21 p22 where "rp p21 = pCons p22 b2"
    apply (simp add: field_simps)
    apply (metis coeff_pCons_0 of_int_hom.map_poly_hom_add of_int_hom.map_poly_hom_smult of_int_hom.coeff_map_poly_hom)
    done
  moreover obtain p21' p21q where "p21 = pCons p21' p21q"
    by (rule pCons_cases)
  ultimately obtain p2 where "b2 = rp p2 "
    by (auto simp: hom_distribs)
  moreover obtain a1' a1q where "a1 = pCons a1' a1q"
    by (rule pCons_cases)
  with a1 obtain p1 where "b1 = rp p1"
    by (auto simp: hom_distribs)
  ultimately have "pair = (rp p1, rp p2)" using pair by simp
  then show ?thesis by auto
qed

lemma  pdivmod_then_div_mod_int_poly:
  assumes q0: "q \<noteq> 0" and "(rp p div rp q, rp p mod rp q) = (rp r, rp m)" 
  shows   "div_mod_int_poly p q = Some (r,m)"
proof -
  let ?rpp = "(\<lambda> (a,b). (rp a,rp b))" (* rp pair *)
  let ?p = "rp p"
  let ?q = "rp q"
  let ?r = "rp r"
  let ?m = "rp m"
  let ?div_rat_step = "div_rat_poly_step ?q"
  let ?div_int_step = "div_int_poly_step q"
  { fix oldRes res :: "int poly \<times> int poly"
    fix lst :: "int list"
    have inj: "(\<And>a b. (case a of (a, b) \<Rightarrow> (rp a, rp b)) = (case b of (a, b) \<Rightarrow> (rp a, rp b)) \<Longrightarrow> a = b)"
      by auto
    have "(\<And>a b c. b \<in> set lst \<Longrightarrow>
              (case a of (a, b) \<Rightarrow> (map_poly rat_of_int a, map_poly rat_of_int b)) =
              (div_rat_poly_step (map_poly rat_of_int q) \<circ> rat_of_int) b
               (case c of (a, b) \<Rightarrow> (map_poly rat_of_int a, map_poly rat_of_int b)) \<Longrightarrow>
              Some a = div_int_poly_step q b (Some c))"
      using rat_step_then_int_poly_step[OF q0] by auto
    hence "?rpp res = foldr (?div_rat_step \<circ> rat_of_int) lst (?rpp oldRes)
          \<Longrightarrow> Some res = foldr ?div_int_step lst (Some oldRes)"
      using foldr_cong_plus[of "set lst" ?rpp "?div_rat_step \<circ> rat_of_int" Some ?div_int_step lst res oldRes]
            div_rat_poly_step_sur inj by simp
    hence "?rpp res = foldr ?div_rat_step (map rat_of_int lst) (?rpp oldRes)
       \<Longrightarrow> Some res = foldr ?div_int_step lst (Some oldRes)"
       using foldr_map[of ?div_rat_step rat_of_int lst] by auto
  }
  hence equal_foldr : "?rpp (r,m) = foldr (?div_rat_step) (map rat_of_int (coeffs p)) (?rpp (0,0))
                   \<Longrightarrow> Some (r,m) = foldr (?div_int_step) (coeffs p) (Some (0,0))"
    by simp
  have "(?r,?m) = (foldr (?div_rat_step) (coeffs ?p) (0,0))"
    using fold_coeffs_def[of "?div_rat_step" ?p] assms
      div_mod_fold_coeffs [of ?p ?q]
    unfolding div_rat_poly_step_def by auto
  hence "Some (r,m) = foldr (?div_int_step) (coeffs p) (Some (0,0))"
    using equal_foldr by simp
  thus ?thesis using q0 unfolding div_mod_int_poly_def by (simp add: fold_coeffs_def)
qed

lemma div_int_then_rqp:
  assumes "div_int_poly p q = Some r"
  shows "r * q = p"
    and "q \<noteq> 0"
proof -
  let ?rpp = "(\<lambda> (a,b). (rp a,rp b))" (* rp pair *)
  let ?p = "rp p"
  let ?q = "rp q"
  let ?r = "rp r"
  have "Some (r,0) = div_mod_int_poly p q" using assms unfolding div_int_poly_def
      by (auto split:  option.splits prod.splits if_splits)
  with div_mod_int_poly_then_pdivmod[of p q r 0]
  have "?p div ?q = ?r \<and> ?p mod ?q = 0" by simp
  with div_mult_mod_eq[of ?p ?q]
  have "?p = ?r * ?q" by auto
  also have "\<dots> = rp (r * q)" by (simp add: hom_distribs)
  finally have "?p = rp (r * q)".
  thus "r * q = p" by simp
  show "q \<noteq> 0" using assms unfolding div_int_poly_def div_mod_int_poly_def
    by (auto split: option.splits prod.splits if_splits)
qed 

lemma rqp_then_div_int:
  assumes "r * q = p"
      and q0:"q \<noteq> 0"
  shows "div_int_poly p q = Some r"
proof -
  let ?rpp = "(\<lambda> (a,b). (rp a,rp b))" (* rp pair *)
  let ?p = "rp p"
  let ?q = "rp q"
  let ?r = "rp r"
  have "?p = ?r * ?q" using assms(1) by (auto simp: hom_distribs)
  hence "?p div ?q = ?r" and "?p mod ?q = 0"
    using q0 by simp_all
  hence "(rp p div rp q, rp p mod rp q) = (rp r, 0)" by (auto split: prod.splits)
  hence "(rp p div rp q, rp p mod rp q) = (rp r, rp 0)" by simp
  hence "Some (r,0) = div_mod_int_poly p q"
    using pdivmod_then_div_mod_int_poly[OF q0,of p r 0] by simp
  thus ?thesis unfolding div_mod_int_poly_def div_int_poly_def using q0 
    by (metis (mono_tags, lifting) option.simps(5) split_conv)
qed

lemma div_int_poly: "(div_int_poly p q = Some r) \<longleftrightarrow> (q \<noteq> 0 \<and> p = r * q)"
  using div_int_then_rqp rqp_then_div_int by blast

definition dvd_int_poly :: "int poly \<Rightarrow> int poly \<Rightarrow> bool" where
  "dvd_int_poly q p = (if q = 0 then p = 0 else div_int_poly p q \<noteq> None)"

lemma dvd_int_poly[simp]: "dvd_int_poly q p = (q dvd p)"
  unfolding dvd_def dvd_int_poly_def using div_int_poly[of p q]
  by (cases "q = 0", auto)

definition dvd_int_poly_non_0 :: "int poly \<Rightarrow> int poly \<Rightarrow> bool" where
  "dvd_int_poly_non_0 q p = (div_int_poly p q \<noteq> None)"

lemma dvd_int_poly_non_0[simp]: "q \<noteq> 0 \<Longrightarrow> dvd_int_poly_non_0 q p = (q dvd p)"
  unfolding dvd_def dvd_int_poly_non_0_def using div_int_poly[of p q] by auto

lemma [code_unfold]: "p dvd q \<longleftrightarrow> dvd_int_poly p q" by simp

hide_const rp
end

