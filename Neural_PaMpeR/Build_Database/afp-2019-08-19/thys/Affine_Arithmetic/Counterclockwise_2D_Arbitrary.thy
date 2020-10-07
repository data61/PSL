section \<open>CCW for Arbitrary Points in the Plane\<close>
theory Counterclockwise_2D_Arbitrary
imports Counterclockwise_2D_Strict
begin

subsection \<open>Interpretation of Knuth's axioms in the plane\<close>

definition lex::"point \<Rightarrow> point \<Rightarrow> bool" where
  "lex p q \<longleftrightarrow> (fst p < fst q \<or> fst p = fst q \<and> snd p < snd q \<or> p = q)"

definition psi::"point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "psi p q r \<longleftrightarrow> (lex p q \<and> lex q r)"

definition ccw::"point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "ccw p q r \<longleftrightarrow> ccw' p q r \<or> (det3 p q r = 0 \<and> (psi p q r \<or> psi q r p \<or> psi r p q))"

interpretation ccw: linorder_list0 "ccw x" for x .

lemma ccw'_imp_ccw: "ccw' a b c \<Longrightarrow> ccw a b c"
  by (simp add: ccw_def)

lemma ccw_ncoll_imp_ccw: "ccw a b c \<Longrightarrow> \<not>coll a b c \<Longrightarrow> ccw' a b c"
  by (simp add: ccw_def)

lemma ccw_translate: "ccw p (p + q) (p + r) = ccw 0 q r"
  by (auto simp: ccw_def psi_def lex_def)

lemma ccw_translate_origin: "NO_MATCH 0 p \<Longrightarrow> ccw p q r = ccw 0 (q - p) (r - p)"
  using ccw_translate[of p "q - p" "r - p"]
  by simp

lemma psi_scale:
  "psi (r *\<^sub>R a) (r *\<^sub>R b) 0 = (if r > 0 then psi a b 0 else if r < 0 then psi 0 b a else True)"
  "psi (r *\<^sub>R a) 0 (r *\<^sub>R b) = (if r > 0 then psi a 0 b else if r < 0 then psi b 0 a else True)"
  "psi 0 (r *\<^sub>R a) (r *\<^sub>R b) = (if r > 0 then psi 0 a b else if r < 0 then psi b a 0 else True)"
  by (auto simp: psi_def lex_def det3_def' not_less sign_simps)

lemma ccw_scale23: "ccw 0 a b \<Longrightarrow> r > 0 \<Longrightarrow> ccw 0 (r *\<^sub>R a) (r *\<^sub>R b)"
  by (auto simp: ccw_def psi_scale)

lemma psi_notI: "distinct3 p q r \<Longrightarrow> psi p q r \<Longrightarrow> \<not> psi q p r"
  by (auto simp: algebra_simps psi_def lex_def)

lemma not_lex_eq: "\<not> lex a b \<longleftrightarrow> lex b a \<and> a \<noteq> b"
  by (auto simp: algebra_simps lex_def prod_eq_iff)

lemma lex_trans: "lex a b \<Longrightarrow> lex b c \<Longrightarrow> lex a c"
  by (auto simp: lex_def)

lemma lex_sym_eqI: "lex a b \<Longrightarrow> lex b a \<Longrightarrow> a = b"
  and lex_sym_eq_iff: "lex a b \<Longrightarrow> lex b a \<longleftrightarrow> a = b"
  by (auto simp: lex_def)

lemma lex_refl[simp]: "lex p p"
  by (metis not_lex_eq)

lemma psi_disjuncts:
  "distinct3 p q r \<Longrightarrow> psi p q r \<or> psi p r q \<or> psi q r p \<or> psi q p r \<or> psi r p q \<or> psi r q p"
  by (auto simp: psi_def not_lex_eq)

lemma nlex_ccw_left: "lex x 0 \<Longrightarrow> ccw 0 (0, 1) x"
  by (auto simp: ccw_def lex_def psi_def ccw'_def det3_def')

interpretation ccw_system123 ccw
  apply unfold_locales
  subgoal by (force simp: ccw_def ccw'_def det3_def' algebra_simps)
  subgoal by (force simp: ccw_def ccw'_def det3_def' psi_def algebra_simps lex_sym_eq_iff)
  subgoal by (drule psi_disjuncts) (force simp: ccw_def ccw'_def det3_def' algebra_simps)
  done

lemma lex_scaleR_nonneg: "lex a b \<Longrightarrow> r \<ge> 0 \<Longrightarrow> lex a (a + r *\<^sub>R (b - a))"
  by (auto simp: lex_def)

lemma lex_scale1_zero:
    "lex (v *\<^sub>R u) 0 = (if v > 0 then lex u 0 else if v < 0 then lex 0 u else True)"
  and lex_scale2_zero:
    "lex 0 (v *\<^sub>R u) = (if v > 0 then lex 0 u else if v < 0 then lex u 0 else True)"
  by (auto simp: lex_def prod_eq_iff less_eq_prod_def sign_simps)

lemma nlex_add:
  assumes "lex a 0" "lex b 0"
  shows "lex (a + b) 0"
  using assms by (auto simp: lex_def)

lemma nlex_sum:
  assumes "finite X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> lex (f x) 0"
  shows "lex (sum f X) 0"
  using assms
  by induction (auto intro!: nlex_add)

lemma abs_add_nlex:
  assumes "coll 0 a b"
  assumes "lex a 0"
  assumes "lex b 0"
  shows "abs (a + b) = abs a + abs b"
proof (rule antisym[OF abs_triangle_ineq])
  have "fst (\<bar>a\<bar> + \<bar>b\<bar>) \<le> fst \<bar>a + b\<bar>"
    using assms
    by (auto simp add: det3_def' abs_prod_def lex_def)
  moreover
  {
    assume H: "fst a < 0" "fst b < 0"
    hence "snd b \<le> 0 \<longleftrightarrow> snd a \<le> 0"
      using assms
      by (auto simp: lex_def det3_def' mult.commute)
        (metis mult_le_cancel_left_neg mult_zero_right)+
    hence "\<bar>snd a\<bar> + \<bar>snd b\<bar> \<le> \<bar>snd a + snd b\<bar>"
      using H by auto
  } hence "snd (\<bar>a\<bar> + \<bar>b\<bar>) \<le> snd \<bar>a + b\<bar>"
    using assms
    by (auto simp add: det3_def' abs_prod_def lex_def)
  ultimately
  show "\<bar>a\<bar> + \<bar>b\<bar> \<le> \<bar>a + b\<bar>" unfolding less_eq_prod_def ..
qed

lemma lex_sum_list: "(\<And>x. x \<in> set xs \<Longrightarrow> lex x 0) \<Longrightarrow> lex (sum_list xs) 0"
  by (induct xs) (auto simp: nlex_add)

lemma
  abs_sum_list_coll:
  assumes coll: "list_all (coll 0 x) xs"
  assumes "x \<noteq> 0"
  assumes up: "list_all (\<lambda>x. lex x 0) xs"
  shows "abs (sum_list xs) = sum_list (map abs xs)"
  using assms
proof (induct xs)
  case (Cons y ys)
  hence "coll 0 x y" "coll 0 x (sum_list ys)"
    by (auto simp: list_all_iff intro!: coll_sum_list)
  hence "coll 0 y (sum_list ys)" using \<open>x \<noteq> 0\<close>
    by (rule coll_trans)
  hence "\<bar>y + sum_list ys\<bar> = abs y + abs (sum_list ys)" using Cons
    by (subst abs_add_nlex) (auto simp: list_all_iff lex_sum_list)
  thus ?case using Cons by simp
qed simp

lemma lex_diff1: "lex (a - b) c = lex a (c + b)"
  and lex_diff2: "lex c (a - b) = lex (c + b) a"
  by (auto simp: lex_def)

lemma sum_list_eq_0_iff_nonpos:
  fixes xs::"'a::ordered_ab_group_add list"
  shows "list_all (\<lambda>x. x \<le> 0) xs \<Longrightarrow> sum_list xs = 0 \<longleftrightarrow> (\<forall>n\<in>set xs. n = 0)"
  by (auto simp: list_all_iff sum_list_sum_nth sum_nonpos_eq_0_iff)
    (auto simp add: in_set_conv_nth)

lemma sum_list_nlex_eq_zeroI:
  assumes nlex: "list_all (\<lambda>x. lex x 0) xs"
  assumes "sum_list xs = 0"
  assumes "x \<in> set xs"
  shows "x = 0"
proof -
  from assms(2) have z1: "sum_list (map fst xs) = 0" and z2: "sum_list (map snd xs) = 0"
    by (auto simp: prod_eq_iff fst_sum_list snd_sum_list)
  from nlex have "list_all (\<lambda>x. x \<le> 0) (map fst xs)"
    by (auto simp: lex_def list_all_iff)
  from sum_list_eq_0_iff_nonpos[OF this] z1 nlex
  have
    z1': "list_all (\<lambda>x. x = 0) (map fst xs)"
    and "list_all (\<lambda>x. x \<le> 0) (map snd xs)"
    by (auto simp: list_all_iff lex_def)
  from sum_list_eq_0_iff_nonpos[OF this(2)] z2
  have "list_all (\<lambda>x. x = 0) (map snd xs)" by (simp add: list_all_iff)
  with z1' show "x = 0" by (auto simp: list_all_iff zero_prod_def assms prod_eq_iff)
qed

lemma sum_list_eq0I: "(\<forall>x\<in>set xs. x = 0) \<Longrightarrow> sum_list xs = 0"
  by (induct xs) auto

lemma sum_list_nlex_eq_zero_iff:
  assumes nlex: "list_all (\<lambda>x. lex x 0) xs"
  shows "sum_list xs = 0 \<longleftrightarrow> list_all ((=) 0) xs"
  using assms
  by (auto intro: sum_list_nlex_eq_zeroI sum_list_eq0I simp: list_all_iff)

lemma
  assumes "lex p q" "lex q r" "0 \<le> a" "0 \<le> b" "0 \<le> c" "a + b + c = 1"
  assumes comb_def: "comb = a *\<^sub>R p + b *\<^sub>R q + c *\<^sub>R r"
  shows lex_convex3: "lex p comb" "lex comb r"
proof -
  from convex3_alt[OF assms(3-6), of p q r]
  obtain u v where
    uv: "a *\<^sub>R p + b *\<^sub>R q + c *\<^sub>R r = p + u *\<^sub>R (q - p) + v *\<^sub>R (r - p)" "0 \<le> u" "0 \<le> v" "u + v \<le> 1" .
  have "lex p r"
    using assms by (metis lex_trans)
  hence "lex (v *\<^sub>R (p - r)) 0" using uv
    by (simp add: lex_scale1_zero lex_diff1)
  also
  have "lex 0 (u *\<^sub>R (q - p))" using \<open>lex p q\<close> uv
    by (simp add: lex_scale2_zero lex_diff2)
  finally (lex_trans)
  show "lex p comb"
    unfolding comb_def uv
    by (simp add: lex_def prod_eq_iff algebra_simps)
  from comb_def have comb_def': "comb = c *\<^sub>R r + b *\<^sub>R q + a *\<^sub>R p" by simp
  from assms have "c + b + a = 1" by simp
  from convex3_alt[OF assms(5,4,3) this, of r q p]
  obtain u v where uv: "c *\<^sub>R r + b *\<^sub>R q + a *\<^sub>R p = r + u *\<^sub>R (q - r) + v *\<^sub>R (p - r)"
    "0 \<le> u" "0 \<le> v" "u + v \<le> 1"
    by auto
  have "lex (u *\<^sub>R (q - r)) 0"
    using uv \<open>lex q r\<close>
    by (simp add: lex_scale1_zero lex_diff1)
  also have "lex 0  (v *\<^sub>R (r - p))"
    using uv \<open>lex p r\<close>
    by (simp add: lex_scale2_zero lex_diff2)
  finally (lex_trans) show "lex comb r"
    unfolding comb_def' uv
    by (simp add: lex_def prod_eq_iff algebra_simps)
qed

lemma lex_convex_self2:
  assumes "lex p q" "0 \<le> a" "a \<le> 1"
  defines "r \<equiv> a *\<^sub>R p + (1 - a) *\<^sub>R q"
  shows "lex p r" (is ?th1)
    and "lex r q" (is ?th2)
  using lex_convex3[OF \<open>lex p q\<close>, of q a "1 - a" 0 r]
      assms
  by (simp_all add: r_def)

lemma lex_uminus0[simp]: "lex (-a) 0 = lex 0 a"
  by (auto simp: lex_def)

lemma
  lex_fst_zero_imp:
  "fst x = 0 \<Longrightarrow> lex x 0 \<Longrightarrow> lex y 0 \<Longrightarrow> \<not>coll 0 x y \<Longrightarrow> ccw' 0 y x"
  by (auto simp: ccw'_def det3_def' lex_def sign_simps)

lemma lex_ccw_left: "lex x y \<Longrightarrow> r > 0 \<Longrightarrow> ccw y (y + (0, r)) x"
  by (auto simp: ccw_def ccw'_def det3_def' algebra_simps lex_def psi_def)

lemma lex_translate_origin: "NO_MATCH 0 a \<Longrightarrow> lex a b = lex 0 (b - a)"
  by (auto simp: lex_def)


subsection \<open>Order prover setup\<close>

definition "lexs p q \<longleftrightarrow> (lex p q \<and> p \<noteq> q)"

lemma lexs_irrefl: "\<not> lexs p p"
  and lexs_imp_lex: "lexs x y \<Longrightarrow> lex x y"
  and not_lexs: "(\<not> lexs x y) = (lex y x)"
  and not_lex: "(\<not> lex x y) = (lexs y x)"
  and eq_lex_refl: "x = y \<Longrightarrow> lex x y"
  by (auto simp: lexs_def lex_def prod_eq_iff)

lemma lexs_trans: "lexs x y \<Longrightarrow> lexs y z \<Longrightarrow> lexs x z"
  and lexs_lex_trans: "lexs x y \<Longrightarrow> lex y z \<Longrightarrow> lexs x z"
  and lex_lexs_trans: "lex x y \<Longrightarrow> lexs y z \<Longrightarrow> lexs x z"
  and lex_neq_trans: "lex a b \<Longrightarrow> a \<noteq> b \<Longrightarrow> lexs a b"
  and neq_lex_trans: "a \<noteq> b \<Longrightarrow> lex a b \<Longrightarrow> lexs a b"
  and lexs_imp_neq: "lexs a b \<Longrightarrow> a \<noteq> b"
  by (auto simp: lexs_def lex_def prod_eq_iff)

declare
  lexs_irrefl[THEN notE, order add less_reflE: linorder "(=) :: point => point => bool" lex lexs]
declare lex_refl[order add le_refl: linorder "(=) :: point => point => bool" lex lexs]
declare lexs_imp_lex[order add less_imp_le: linorder "(=) :: point => point => bool" lex lexs]
declare
  not_lexs[THEN iffD2, order add not_lessI: linorder "(=) :: point => point => bool" lex lexs]
declare not_lex[THEN iffD2, order add not_leI: linorder "(=) :: point => point => bool" lex lexs]
declare
  not_lexs[THEN iffD1, order add not_lessD: linorder "(=) :: point => point => bool" lex lexs]
declare not_lex[THEN iffD1, order add not_leD: linorder "(=) :: point => point => bool" lex lexs]
declare lex_sym_eqI[order add eqI: linorder "(=) :: point => point => bool" lex lexs]
declare eq_lex_refl[order add eqD1: linorder "(=) :: point => point => bool" lex lexs]
declare sym[THEN eq_lex_refl, order add eqD2: linorder "(=) :: point => point => bool" lex lexs]
declare lexs_trans[order add less_trans: linorder "(=) :: point => point => bool" lex lexs]
declare lexs_lex_trans[order add less_le_trans: linorder "(=) :: point => point => bool" lex lexs]
declare lex_lexs_trans[order add le_less_trans: linorder "(=) :: point => point => bool" lex lexs]
declare lex_trans[order add le_trans: linorder "(=) :: point => point => bool" lex lexs]
declare lex_neq_trans[order add le_neq_trans: linorder "(=) :: point => point => bool" lex lexs]
declare neq_lex_trans[order add neq_le_trans: linorder "(=) :: point => point => bool" lex lexs]
declare lexs_imp_neq[order add less_imp_neq: linorder "(=) :: point => point => bool" lex lexs]
declare
  eq_neq_eq_imp_neq[order add eq_neq_eq_imp_neq: linorder "(=) :: point => point => bool" lex lexs]
declare not_sym[order add not_sym: linorder "(=) :: point => point => bool" lex lexs]


subsection \<open>Contradictions\<close>

lemma
  assumes d: "distinct4 s p q r"
  shows contra1: "\<not>(lex p q \<and> lex q r \<and> lex r s \<and> indelta s p q r)" (is ?th1)
    and contra2: "\<not>(lex s p \<and> lex p q \<and> lex q r \<and> indelta s p q r)" (is ?th2)
    and contra3: "\<not>(lex p r \<and> lex p s \<and> lex q r \<and> lex q s \<and> insquare p r q s)" (is ?th3)
proof -
  {
    assume "det3 s p q = 0" "det3 s q r = 0" "det3 s r p = 0" "det3 p q r = 0"
    hence ?th1 ?th2 ?th3 using d
      by (auto simp add: det3_def' ccw'_def ccw_def psi_def algebra_simps)
  } moreover {
    assume *: "\<not>(det3 s p q = 0 \<and> det3 s q r = 0 \<and> det3 s r p = 0 \<and> det3 p q r = 0)"
    {
      assume d0: "det3 p q r = 0"
      with d have "?th1 \<and> ?th2"
        by (force simp add: det3_def' ccw'_def ccw_def psi_def algebra_simps)
    } moreover {
      assume dp: "det3 p q r \<noteq> 0"
      have "?th1 \<and> ?th2"
        unfolding de_Morgan_disj[symmetric]
      proof (rule notI, goal_cases)
        case prems: 1
        hence **: "indelta s p q r" by auto
        hence nonnegs: "det3 p q r \<ge> 0" "0 \<le> det3 s q r" "0 \<le> det3 p s r" "0 \<le> det3 p q s"
          by (auto simp: ccw_def ccw'_def det3_def' algebra_simps)
        hence det_pos: "det3 p q r > 0" using dp by simp
        have det_eq: "det3 s q r + det3 p s r + det3 p q s = det3 p q r"
          by (auto simp: ccw_def det3_def' algebra_simps)
        hence det_div_eq:
          "det3 s q r / det3 p q r + det3 p s r / det3 p q r + det3 p q s / det3 p q r = 1"
          using det_pos by (auto simp: field_simps)
        from lex_convex3[OF _ _ _ _ _ det_div_eq convex_comb_dets[OF det_pos, of s]]
        have "lex p s" "lex s r"
          using prems by (auto simp: nonnegs)
        with prems d show False by (simp add: lex_sym_eq_iff)
      qed
    } moreover have ?th3
    proof (safe, goal_cases)
      case prems: 1
      have nonnegs: "det3 p r q \<ge> 0" "det3 r q s \<ge> 0" "det3 s p r \<ge> 0" "det3 q s p \<ge> 0"
        using prems
        by (auto simp add: ccw_def ccw'_def less_eq_real_def)
      have dets_eq: "det3 p r q + det3 q s p = det3 r q s + det3 s p r"
        by (auto simp: det3_def')
      hence **: "det3 p r q = 0 \<and> det3 q s p = 0 \<Longrightarrow> det3 r q s = 0 \<and> det3 s p r = 0"
        using prems
        by (auto simp: ccw_def ccw'_def)
      moreover
      {
        fix p r q s
        assume det_pos: "det3 p r q > 0"
        assume dets_eq: "det3 p r q + det3 q s p = det3 r q s + det3 s p r"
        assume nonnegs:"det3 r q s \<ge> 0" "det3 s p r \<ge> 0" "det3 q s p \<ge> 0"
        assume g14: "lex p r" "lex p s" "lex q r" "lex q s"
        assume d: "distinct4 s p q r"

        let ?sum = "(det3 p r q + det3 q s p) / det3 p r q"
        have eqs: "det3 s p r = det3 p r s" "det3 r q s = det3 s r q" "det3 q s p = - det3 p s q"
          by (auto simp: det3_def' algebra_simps)
        from convex_comb_dets[OF det_pos, of s]
        have "((det3 p r q / det3 p r q) *\<^sub>R s + (det3 q s p / det3 p r q) *\<^sub>R r) /\<^sub>R ?sum =
            ((det3 r q s / det3 p r q) *\<^sub>R p + (det3 s p r / det3 p r q) *\<^sub>R q) /\<^sub>R ?sum"
          unfolding eqs
          by (simp add: algebra_simps prod_eq_iff)
        hence srpq: "(det3 p r q / det3 p r q / ?sum) *\<^sub>R s + (det3 q s p / det3 p r q / ?sum) *\<^sub>R r =
          (det3 r q s / det3 p r q / ?sum) *\<^sub>R p + (det3 s p r / det3 p r q  / ?sum) *\<^sub>R q"
          (is "?s *\<^sub>R s + ?r *\<^sub>R r = ?p *\<^sub>R p + ?q *\<^sub>R q")
          using det_pos
          by (simp add: algebra_simps inverse_eq_divide)
        have eqs: "?s + ?r = 1" "?p + ?q = 1"
          and s: "?s \<ge> 0" "?s \<le> 1"
          and r: "?r \<ge> 0" "?r \<le> 1"
          and p: "?p \<ge> 0" "?p \<le> 1"
          and q: "?q \<ge> 0" "?q \<le> 1"
          unfolding add_divide_distrib[symmetric]
          using det_pos nonnegs dets_eq
          by (auto)
        from eqs have eqs': "1 - ?s = ?r" "1 - ?r = ?s" "1 - ?p = ?q" "1 - ?q = ?p"
          by auto
        have comm: "?r *\<^sub>R r + ?s *\<^sub>R s = ?s *\<^sub>R s + ?r *\<^sub>R r"
          "?q *\<^sub>R q + ?p *\<^sub>R p = ?p *\<^sub>R p + ?q *\<^sub>R q"
          by simp_all
        define K
          where "K = (det3 r q s / det3 p r q / ?sum) *\<^sub>R p + (det3 s p r / det3 p r q  / ?sum) *\<^sub>R q"
        note rewrs = eqs' comm srpq K_def[symmetric]
        from lex_convex_self2[OF _ s, of s r, unfolded rewrs]
           lex_convex_self2[OF _ r, of r s, unfolded rewrs]
           lex_convex_self2[OF _ p, of p q, unfolded rewrs]
           lex_convex_self2[OF _ q, of q p, unfolded rewrs]
        have False using g14 d det_pos
          by (metis lex_trans not_lex_eq)
      } note wlog = this
      from dets_eq have 1: "det3 q s p + det3 p r q = det3 s p r + det3 r q s"
        by simp
      from d have d': "distinct4 r q p s" by auto
      note wlog[of q s p r, OF _ 1 nonnegs(3,2,1) prems(4,3,2,1) d']
        wlog[of p r q s, OF _ dets_eq nonnegs(2,3,4) prems(1-4) d]
      ultimately show False using nonnegs d *
        by (auto simp: less_eq_real_def det3_def' algebra_simps)
    qed
    ultimately have ?th1 ?th2 ?th3 by blast+
  } ultimately show ?th1 ?th2 ?th3 by force+
qed

lemma ccw'_subst_psi_disj:
  assumes "det3 t r s = 0"
  assumes "psi t r s \<or> psi t s r \<or> psi s r t"
  assumes "s \<noteq> t"
  assumes "ccw' t r p"
  shows "ccw' t s p"
proof cases
  assume "r \<noteq> s"
  from assms have "r \<noteq> t" by (auto simp: det3_def' ccw'_def algebra_simps)
  from assms have "det3 r s t = 0"
    by (auto simp: algebra_simps det3_def')
  from coll_ex_scaling[OF assms(3) this]
  obtain x where s: "r = s + x *\<^sub>R (t - s)" by auto
  from assms(4)[simplified s]
  have "0 < det3 0 (s + x *\<^sub>R (t - s) - t) (p - t)"
    by (auto simp: algebra_simps det3_def' ccw'_def)
  also have "s + x *\<^sub>R (t - s) - t = (1 - x) *\<^sub>R (s - t)"
    by (simp add: algebra_simps)
  finally have ccw': "ccw' 0 ((1 - x) *\<^sub>R (s - t)) (p - t)"
    by (simp add: ccw'_def)
  hence neq: "x \<noteq> 1" by (auto simp add: det3_def' ccw'_def)
  have tr: "fst s < fst r \<Longrightarrow> fst t = fst s \<Longrightarrow> snd t \<le> snd r"
    by (simp add: s)
  from s have "fst (r - s) = fst (x *\<^sub>R (t - s))" "snd (r - s) = snd (x *\<^sub>R (t - s))"
    by (auto simp: )
  hence "x = (if fst (t - s) = 0 then snd (r - s) / snd (t - s) else fst (r - s) / fst (t - s))"
    using \<open>s \<noteq> t\<close>
    by (auto simp add: field_simps prod_eq_iff)
  also have "\<dots> \<le> 1"
    using assms
    by (auto simp: lex_def psi_def tr)
  finally have "x < 1" using neq by simp
  thus ?thesis using ccw'
    by (auto simp: ccw'.translate_origin)
qed (insert assms, simp)

lemma lex_contr:
  assumes "distinct4 t s q r"
  assumes "lex t s" "lex s r"
  assumes "det3 t s r = 0"
  assumes "ccw' t s q"
  assumes "ccw' t q r"
  shows "False"
  using ccw'_subst_psi_disj[of t s r q] assms
  by (cases "r = t") (auto simp: det3_def' algebra_simps psi_def ccw'_def)

lemma contra4:
  assumes "distinct4 s r q p"
  assumes lex: "lex q p" "lex p r" "lex r s"
  assumes ccw: "ccw r q s" "ccw r s p" "ccw r q p"
  shows False
proof cases
  assume c: "ccw s q p"
  from c have *: "indelta s r q p"
    using assms by simp
  with contra1[OF assms(1)]
  have "\<not> (lex r q \<and> lex q p \<and> lex p s)" by blast
  hence "\<not> lex q p"
    using \<open>ccw s q p\<close> contra1 cyclic assms nondegenerate by blast
  thus False using assms by simp
next
  assume "\<not> ccw s q p"
  with ccw have "ccw q s p \<and> ccw s p r \<and> ccw p r q \<and> ccw r q s"
    by (metis assms(1) ccw'.cyclic ccw_def not_ccw'_eq psi_disjuncts)
  moreover
  from lex have "lex q r" "lex q s" "lex p r" "lex p s" by order+
  ultimately show False using contra3[of r q p s] \<open>distinct4 s r q p\<close> by blast
qed

lemma not_coll_ordered_lexI:
  assumes "l \<noteq> x0"
    and "lex x1 r"
    and "lex x1 l"
    and "lex r x0"
    and "lex l x0"
    and "ccw' x0 l x1"
    and "ccw' x0 x1 r"
  shows "det3 x0 l r \<noteq> 0"
proof
  assume "coll x0 l r"
  from \<open>coll x0 l r\<close> have 1: "coll 0 (l - x0) (r - x0)"
    by (simp add: det3_def' algebra_simps)
  from \<open>lex r x0\<close> have 2: "lex (r - x0) 0" by (auto simp add: lex_def)
  from \<open>lex l x0\<close> have 3: "lex (l - x0) 0" by (auto simp add: lex_def)
  from \<open>ccw' x0 l x1\<close> have 4: "ccw' 0 (l - x0) (x1 - x0)"
    by (simp add: det3_def' ccw'_def algebra_simps)
  from \<open>ccw' x0 x1 r\<close> have 5: "ccw' 0 (x1 - x0) (r - x0)"
    by (simp add: det3_def' ccw'_def algebra_simps)
  from \<open>lex x1 r\<close> have 6: "lex 0 (r - x0 - (x1 - x0))" by (auto simp: lex_def)
  from \<open>lex x1 l\<close> have 7: "lex 0 (l - x0 - (x1 - x0))" by (auto simp: lex_def)
  define r' where "r' = r - x0"
  define l' where "l' = l - x0"
  define x0' where "x0' = x1 - x0"
  from 1 2 3 4 5 6 7
  have rs: "coll 0 l' r'" "lex r' 0"
    "lex l' 0"
    "ccw' 0 l' x0'"
    "ccw' 0 x0' r'"
    "lex 0 (r' - x0')"
    "lex 0 (l' - x0')"
    unfolding r'_def[symmetric] l'_def[symmetric] x0'_def[symmetric]
    by auto
  from assms have "l' \<noteq> 0"
    by (auto simp: l'_def)
  from coll_scale[OF \<open>coll 0 l' _\<close> this]
  obtain y where y: "r' = y *\<^sub>R l'" by auto
  {
    assume "y > 0"
    with rs have False
      by (auto simp: det3_def' algebra_simps y ccw'_def)
  } moreover {
    assume "y < 0"
    with rs have False
      by (auto simp: lex_def not_less sign_simps y ccw'_def)
  } moreover {
    assume "y = 0"
    from this rs have False
      by (simp add: ccw'_def y)
  } ultimately show False by arith
qed

interpretation ccw_system4 ccw
proof unfold_locales
  fix p q r t
  assume ccw: "ccw t q r" "ccw p t r" "ccw p q t"
  show "ccw p q r"
  proof (cases "det3 t q r = 0 \<and> det3 p t r = 0 \<and> det3 p q t = 0")
    case True
    {
      assume "psi t q r \<or> psi q r t \<or> psi r t q"
        "psi p t r \<or> psi t r p \<or> psi r p t"
        "psi p q t \<or> psi q t p \<or> psi t p q"
      hence "psi p q r \<or> psi q r p \<or> psi r p q"
        using lex_sym_eq_iff psi_def by blast
    }
    with True ccw show ?thesis
      by (simp add: det3_def' algebra_simps ccw_def ccw'_def)
  next
    case False
    hence "0 \<le> det3 t q r" "0 \<le> det3 p t r" "0 \<le> det3 p q t"
      using ccw by (auto simp: less_eq_real_def ccw_def ccw'_def)
    with False show ?thesis
      by (auto simp: ccw_def det3_def' algebra_simps ccw'_def intro!: disjI1)
  qed
qed

lemma lex_total: "lex t q \<and> t \<noteq> q \<or> lex q t \<and> t \<noteq> q \<or> t = q"
  by auto

lemma
  ccw_two_up_contra:
  assumes c: "ccw' t p q" "ccw' t q r"
  assumes ccws: "ccw t s p" "ccw t s q" "ccw t s r" "ccw t p q" "ccw t q r" "ccw t r p"
  assumes distinct: "distinct5 t s p q r"
  shows False
proof -
  from ccws
  have nn: "det3 t s p \<ge> 0" "det3 t s q \<ge> 0" "det3 t s r \<ge> 0" "det3 t r p \<ge> 0"
    by (auto simp add: less_eq_real_def ccw_def ccw'_def)
  with c det_identity[of t p q s r]
  have tsr: "coll t s r" and tsp: "coll t s p"
    by (auto simp: add_nonneg_eq_0_iff ccw'_def)
  moreover
  have trp: "coll t r p"
    by (metis ccw'_subst_collinear distinct not_ccw'_eq tsr tsp)
  ultimately have tpr: "coll t p r"
    by (auto simp: det3_def' algebra_simps)
  moreover
  have psi: "psi t p r \<or> psi t r p \<or> psi r p t"
    unfolding psi_def
  proof -
    have ntsr: "\<not> ccw' t s r" "\<not> ccw' t r s"
      using tsr
      by (auto simp: not_ccw'_eq det3_def' algebra_simps)
    have f8: "\<not> ccw' t r s"
      using tsr not_ccw'_eq by blast
    have f9: "\<not> ccw' t r p"
      using tpr by (simp add: not_ccw'_eq)
    have f10: "(lex t r \<and> lex r p \<or> lex r p \<and> lex p t \<or> lex p t \<and> lex t r)"
      using ccw_def ccws(6) psi_def f9 by auto

    have "\<not> ccw' t r q"
      using c(2) not_ccw'_eq by blast
    moreover
    have "\<not>coll t q s"
      using ntsr ccw'_subst_collinear distinct c(2) by blast
    hence "ccw' t s q"
      by (meson ccw_def ccws(2) not_ccw'_eq)
    moreover
    from tsr tsp \<open>coll t r p\<close> have "coll t p s" "coll t p r" "coll t r s"
      by (auto simp add: det3_def' algebra_simps)
    ultimately
    show "lex t p \<and> lex p r \<or> lex t r \<and> lex r p \<or> lex r p \<and> lex p t"
      by (metis ccw'_subst_psi_disj distinct ccw_def ccws(3) contra4 tsp ntsr(1) f10 lex_total
        psi_def trp)
  qed
  moreover
  from distinct have "r \<noteq> t" by auto
  ultimately
  have "ccw' t r q" using c(1)
    by (rule ccw'_subst_psi_disj)
  thus False
    using c(2) by (simp add: ccw'_contra)
qed

lemma
  ccw_transitive_contr:
  fixes t s p q r
  assumes ccws: "ccw t s p" "ccw t s q" "ccw t s r" "ccw t p q" "ccw t q r" "ccw t r p"
  assumes distinct: "distinct5 t s p q r"
  shows False
proof -
  from ccws distinct have *: "ccw p t r" "ccw p q t" by (metis cyclic)+
  with distinct have "ccw r p q" using interior[OF _ _ ccws(5) *, of UNIV]
    by (auto intro: cyclic)

  from ccws have nonnegs: "det3 t s p \<ge> 0" "det3 t s q \<ge> 0" "det3 t s r \<ge> 0" "det3 t p q \<ge> 0"
    "det3 t q r \<ge> 0" "det3 t r p \<ge> 0"
    by (auto simp add: less_eq_real_def ccw_def ccw'_def)
  {
    assume "ccw' t p q" "ccw' t q r" "ccw' t r p"
    hence False
      using ccw_two_up_contra ccws distinct by blast
  } moreover {
    assume c: "coll t q r" "coll t r p"
    with distinct four_points_aligned(1)[OF c, of s]
    have "coll t p q"
      by auto
    hence "(psi t p q \<or> psi p q t \<or> psi q t p)"
      "psi t q r \<or> psi q r t \<or> psi r t q"
      "psi t r p \<or> psi r p t \<or> psi p t r"
      using ccws(4,5,6) c
      by (simp_all add: ccw_def ccw'_def)
    hence False
      using distinct
      by (auto simp: psi_def ccw'_def)
  } moreover {
    assume c: "det3 t p q = 0" "det3 t q r > 0" "det3 t r p = 0"
    have "\<And>x. det3 t q r = 0 \<or> t = x \<or> r = q \<or> q = x \<or> r = p \<or> p = x \<or> r = x"
      by (meson c(1) c(3) distinct four_points_aligned(1))
    hence False
      by (metis (full_types) c(2) distinct less_irrefl)
  } moreover {
    assume c: "det3 t p q = 0" "det3 t q r = 0" "det3 t r p > 0"
    have "\<And>x. det3 t r p = 0 \<or> t = x \<or> r = x \<or> q = x \<or> p = x"
      by (meson c(1) c(2) distinct four_points_aligned(1))
    hence False
      by (metis (no_types) c(3) distinct less_numeral_extra(3))
  } moreover {
    assume c: "ccw' t p q" "ccw' t q r"
    from ccw_two_up_contra[OF this ccws distinct]
    have False .
  } moreover {
    assume c: "ccw' t p q" "ccw' t r p"
    from ccw_two_up_contra[OF this(2,1), of s] ccws distinct
    have False by auto
  } moreover {
    assume c: "ccw' t q r" "ccw' t r p"
    from ccw_two_up_contra[OF this, of s] ccws distinct
    have False by auto
  } ultimately show "False"
    using \<open>0 \<le> det3 t p q\<close>
    \<open>0 \<le> det3 t q r\<close>\<open>0 \<le> det3 t r p\<close>
    by (auto simp: less_eq_real_def ccw'_def)
qed

interpretation ccw: ccw_system ccw
  by unfold_locales (metis ccw_transitive_contr nondegenerate)

lemma ccw_scaleR1:
  "det3 0 xr P \<noteq> 0 \<Longrightarrow> 0 < e \<Longrightarrow> ccw 0 xr P \<Longrightarrow> ccw 0 (e*\<^sub>Rxr) P"
  by (simp add: ccw_def)

lemma ccw_scaleR2:
  "det3 0 xr P \<noteq> 0 \<Longrightarrow> 0 < e \<Longrightarrow> ccw 0 xr P \<Longrightarrow> ccw 0 xr (e*\<^sub>RP)"
  by (simp add: ccw_def)

lemma ccw_translate3_aux:
  assumes "\<not>coll 0 a b"
  assumes "x < 1"
  assumes "ccw 0 (a - x*\<^sub>Ra) (b - x *\<^sub>R a)"
  shows "ccw 0 a b"
proof -
  from assms have "\<not> coll 0 (a - x*\<^sub>Ra) (b - x *\<^sub>R a)"
    by simp
  with assms have "ccw' 0 ((1 - x) *\<^sub>R a) (b - x *\<^sub>R a)"
    by (simp add: algebra_simps ccw_def)
  thus "ccw 0 a b"
    using \<open>x < 1\<close>
    by (simp add: ccw_def)
qed

lemma ccw_translate3_minus: "det3 0 a b \<noteq> 0 \<Longrightarrow> x < 1 \<Longrightarrow> ccw 0 a (b - x *\<^sub>R a) \<Longrightarrow> ccw 0 a b"
  using ccw_translate3_aux[of a b x] ccw_scaleR1[of a "b - x *\<^sub>R a" "1-x" ]
  by (auto simp add: algebra_simps)

lemma ccw_translate3: "det3 0 a b \<noteq> 0 \<Longrightarrow> x < 1 \<Longrightarrow> ccw 0 a b \<Longrightarrow> ccw 0 a (x *\<^sub>R a + b)"
  by (rule ccw_translate3_minus) (auto simp add: algebra_simps)

lemma ccw_switch23: "det3 0 P Q \<noteq> 0 \<Longrightarrow> (\<not> ccw 0 Q P \<longleftrightarrow> ccw 0 P Q)"
  by (auto simp: ccw_def algebra_simps not_ccw'_eq ccw'_not_coll)

lemma ccw0_upward: "fst a > 0 \<Longrightarrow> snd a = 0 \<Longrightarrow> snd b > snd a \<Longrightarrow> ccw 0 a b"
  by (auto simp: ccw_def det3_def' algebra_simps ccw'_def)

lemma ccw_uminus3[simp]: "det3 a b c \<noteq> 0 \<Longrightarrow> ccw (-a) (-b) (-c) = ccw a b c"
  by (auto simp: ccw_def ccw'_def algebra_simps det3_def')

lemma coll_minus_eq: "coll (x - a) (x - b) (x - c) = coll a b c"
  by (auto simp: det3_def' algebra_simps)

lemma ccw_minus3: "\<not> coll a b c \<Longrightarrow> ccw (x - a) (x - b) (x - c) \<longleftrightarrow> ccw a b c"
  by (simp add: ccw_def coll_minus_eq)

lemma ccw0_uminus[simp]: "\<not> coll 0 a b \<Longrightarrow> ccw 0 (-a) (-b) \<longleftrightarrow> ccw 0 a b"
  using ccw_uminus3[of 0 a b]
  by simp

lemma lex_convex2:
  assumes "lex p q" "lex p r" "0 \<le> u" "u \<le> 1"
  shows "lex p (u *\<^sub>R q + (1 - u) *\<^sub>R r)"
proof cases
  note \<open>lex p q\<close>
  also
  assume "lex q r"
  hence "lex q (u *\<^sub>R q + (1 - u) *\<^sub>R r)"
    using \<open>0 \<le> u\<close> \<open>u \<le> 1\<close>
    by (rule lex_convex_self2)
  finally (lex_trans) show ?thesis .
next
  note \<open>lex p r\<close>
  also
  assume "\<not> lex q r"
  hence "lex r q"
    by simp
  hence "lex r ((1 - u) *\<^sub>R r + (1 - (1 - u)) *\<^sub>R q)"
    using \<open>0 \<le> u\<close> \<open>u \<le> 1\<close>
    by (intro lex_convex_self2) simp_all
  finally (lex_trans) show ?thesis by (simp add: ac_simps)
qed

lemma lex_convex2':
  assumes "lex q p" "lex r p" "0 \<le> u" "u \<le> 1"
  shows "lex (u *\<^sub>R q + (1 - u) *\<^sub>R r) p"
proof -
  have "lex (- p) (u *\<^sub>R (-q) + (1 - u) *\<^sub>R (-r))"
    using assms
    by (intro lex_convex2) (auto simp: lex_def)
  thus ?thesis
    by (auto simp: lex_def algebra_simps)
qed

lemma psi_convex1:
  assumes "psi c a b"
  assumes "psi d a b"
  assumes "0 \<le> u" "0 \<le> v" "u + v = 1"
  shows "psi (u *\<^sub>R c + v *\<^sub>R d) a b"
proof -
  from assms have v: "v = (1 - u)" by simp
  show ?thesis
    using assms
    by (auto simp: psi_def v intro!: lex_convex2' lex_convex2)
qed

lemma psi_convex2:
  assumes "psi a c b"
  assumes "psi a d b"
  assumes "0 \<le> u" "0 \<le> v" "u + v = 1"
  shows "psi a (u *\<^sub>R c + v *\<^sub>R d) b"
proof -
  from assms have v: "v = (1 - u)" by simp
  show ?thesis
    using assms
    by (auto simp: psi_def v intro!: lex_convex2' lex_convex2)
qed

lemma psi_convex3:
  assumes "psi a b c"
  assumes "psi a b d"
  assumes "0 \<le> u" "0 \<le> v" "u + v = 1"
  shows "psi a b (u *\<^sub>R c + v *\<^sub>R d)"
proof -
  from assms have v: "v = (1 - u)" by simp
  show ?thesis
    using assms
    by (auto simp: psi_def v intro!: lex_convex2)
qed

lemma coll_convex:
  assumes "coll a b c" "coll a b d"
  assumes "0 \<le> u" "0 \<le> v" "u + v = 1"
  shows "coll a b (u *\<^sub>R c + v *\<^sub>R d)"
proof cases
  assume "a \<noteq> b"
  with assms(1, 2)
  obtain x y where xy: "c - a = x *\<^sub>R (b - a)" "d - a = y *\<^sub>R (b - a)"
    by (auto simp: det3_translate_origin dest!: coll_scale)
  from assms have "(u + v) *\<^sub>R a = a" by simp
  hence "u *\<^sub>R c + v *\<^sub>R d - a = u *\<^sub>R (c - a) + v *\<^sub>R (d - a)"
    by (simp add: algebra_simps)
  also have "\<dots> = u *\<^sub>R x *\<^sub>R (b - a) + v *\<^sub>R y *\<^sub>R (b - a)"
    by (simp add: xy)
  also have "\<dots> = (u * x + v * y) *\<^sub>R (b - a)" by (simp add: algebra_simps)
  also have "coll 0 (b - a) \<dots>"
    by (simp add: coll_scaleR_right_eq)
  finally show ?thesis
    by (auto simp: det3_translate_origin)
qed simp

lemma (in ccw_vector_space) convex3:
  assumes "u \<ge> 0" "v \<ge> 0" "u + v = 1" "ccw a b d" "ccw a b c"
  shows "ccw a b (u *\<^sub>R c + v *\<^sub>R d)"
proof -
  have "v = 1 - u" using assms by simp
  hence "ccw 0 (b - a) (u *\<^sub>R (c - a) + v *\<^sub>R (d - a))"
    using assms
    by (cases "u = 0" "v = 0" rule: bool.exhaust[case_product bool.exhaust])
      (auto simp add: translate_origin intro!: add3)
  also
  have "(u + v) *\<^sub>R a = a" by (simp add: assms)
  hence "u *\<^sub>R (c - a) + v *\<^sub>R (d - a) = u *\<^sub>R c + v *\<^sub>R d - a"
    by (auto simp: algebra_simps)
  finally show ?thesis by (simp add: translate_origin)
qed

lemma ccw_self[simp]: "ccw a a b" "ccw b a a"
  by (auto simp: ccw_def psi_def intro: cyclic)

lemma ccw_sefl'[simp]: "ccw a b a"
  by (rule cyclic) simp

lemma ccw_convex':
  assumes uv: "u \<ge> 0" "v \<ge> 0" "u + v = 1"
  assumes "ccw a b c" and 1: "coll a b c"
  assumes "ccw a b d" and 2: "\<not> coll a b d"
  shows "ccw a b (u *\<^sub>R c + v *\<^sub>R d)"
proof -
  from assms have u: "0 \<le> u" "u \<le> 1" and v: "v = 1 - u"
    by (auto simp: algebra_simps)
  let ?c = "u *\<^sub>R c + v *\<^sub>R d"
  from 1 have abd: "ccw' a b d"
    using assms by (auto simp: ccw_def)
  {
    assume 2: "\<not> coll a b c"
    from 2 have "ccw' a b c"
      using assms by (auto simp: ccw_def)
    with abd have "ccw' a b ?c"
      using assms by (auto intro!: ccw'.convex3)
    hence ?thesis
      by (simp add: ccw_def)
  } moreover {
    assume 2: "coll a b c"
    {
      assume "a = b"
      hence ?thesis by simp
    } moreover {
      assume "v = 0"
      hence ?thesis
        by (auto simp: v assms)
    } moreover {
      assume "v \<noteq> 0" "a \<noteq> b"
      have "coll c a b" using 2 by (auto simp: det3_def' algebra_simps)
      from coll_ex_scaling[OF \<open>a \<noteq> b\<close> this]
      obtain r where c: "c = a + r *\<^sub>R (b - a)" by auto
      have *: "u *\<^sub>R (a + r *\<^sub>R (b - a)) + v *\<^sub>R d - a = (u * r) *\<^sub>R (b - a)  + (1 - u) *\<^sub>R (d - a)"
        by (auto simp: algebra_simps v)
      have "ccw' a b ?c"
        using \<open>v \<noteq> 0\<close> uv abd
        by (simp add: ccw'.translate_origin c *)
      hence ?thesis by (simp add: ccw_def)
    } ultimately have ?thesis by blast
  } ultimately show ?thesis by blast
qed

lemma ccw_convex:
  assumes uv: "u \<ge> 0" "v \<ge> 0" "u + v = 1"
  assumes "ccw a b c"
  assumes "ccw a b d"
  assumes lex: "coll a b c \<Longrightarrow> coll a b d \<Longrightarrow> lex b a"
  shows "ccw a b (u *\<^sub>R c + v *\<^sub>R d)"
proof -
  from assms have u: "0 \<le> u" "u \<le> 1" and v: "v = 1 - u"
    by (auto simp: algebra_simps)
  let ?c = "u *\<^sub>R c + v *\<^sub>R d"
  {
    assume coll: "coll a b c \<and> coll a b d"
    hence "coll a b ?c"
      by (auto intro!: coll_convex assms)
    moreover
    from coll have "psi a b c \<or> psi b c a \<or> psi c a b" "psi a b d \<or> psi b d a \<or> psi d a b"
      using assms by (auto simp add: ccw_def ccw'_not_coll)
    hence "psi a b ?c \<or> psi b ?c a \<or> psi ?c a b"
      using coll uv lex
      by (auto simp: psi_def ccw_def not_lex lexs_def v intro: lex_convex2 lex_convex2')
    ultimately have ?thesis
      by (simp add: ccw_def)
  } moreover {
    assume 1: "\<not> coll a b d" and 2: "\<not> coll a b c"
    from 1 have abd: "ccw' a b d"
      using assms by (auto simp: ccw_def)
    from 2 have "ccw' a b c"
      using assms by (auto simp: ccw_def)
    with abd have "ccw' a b ?c"
      using assms by (auto intro!: ccw'.convex3)
    hence ?thesis
      by (simp add: ccw_def)
  } moreover {
    assume "\<not> coll a b d" "coll a b c"
    have ?thesis
      by (rule ccw_convex') fact+
  } moreover {
    assume 1: "coll a b d" and 2: "\<not> coll a b c"
    have "0 \<le> 1 - u" using assms by (auto )
    from ccw_convex'[OF this \<open>0 \<le> u\<close> _ \<open>ccw a b d\<close> 1 \<open>ccw a b c\<close> 2]
    have ?thesis by (simp add: algebra_simps v)
  } ultimately show ?thesis by blast
qed

interpretation ccw: ccw_convex ccw S "\<lambda>a b. lex b a" for S
  by unfold_locales (rule ccw_convex)

lemma ccw_sorted_scaleR: "ccw.sortedP 0 xs \<Longrightarrow> r > 0 \<Longrightarrow> ccw.sortedP 0 (map ((*\<^sub>R) r) xs)"
  by (induct xs)
    (auto intro!: ccw.sortedP.Cons ccw_scale23 elim!: ccw.sortedP_Cons simp del: scaleR_Pair)

lemma ccw_sorted_implies_ccw'_sortedP:
  assumes nonaligned: "\<And>y z. y \<in> set Ps \<Longrightarrow> z \<in> set Ps \<Longrightarrow> y \<noteq> z \<Longrightarrow> \<not> coll 0 y z"
  assumes sorted: "linorder_list0.sortedP (ccw 0) Ps"
  assumes "distinct Ps"
  shows "linorder_list0.sortedP (ccw' 0 ) Ps"
  using assms
proof (induction Ps)
  case (Cons P Ps)
  {
    fix p assume p: "p \<in> set Ps"
    moreover
    from p Cons.prems have "ccw 0 P p"
      by (auto elim!: linorder_list0.sortedP_Cons intro: Cons)
    ultimately
    have "ccw' 0 P p"
      using \<open>distinct (P#Ps)\<close>
      by (intro ccw_ncoll_imp_ccw Cons) auto
  }
  moreover
  have "linorder_list0.sortedP (ccw' 0) Ps"
    using Cons.prems
    by (intro Cons) (auto elim!: linorder_list0.sortedP_Cons intro: Cons)
  ultimately
  show ?case
    by (auto intro!: linorder_list0.Cons )
qed (auto intro: linorder_list0.Nil)

end
