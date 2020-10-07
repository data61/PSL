(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
theory Hensel_Lifting_Type_Based
imports Hensel_Lifting
begin


subsection\<open>Hensel Lifting in a Type-Based Setting\<close>

(* TODO: Move? *)

lemma degree_smult_eq_iff:
  "degree (smult a p) = degree p \<longleftrightarrow> degree p = 0 \<or> a * lead_coeff p \<noteq> 0"
  by (metis (no_types, lifting) coeff_smult degree_0 degree_smult_le le_antisym 
      le_degree le_zero_eq leading_coeff_0_iff)

lemma degree_smult_eqI[intro!]:
  assumes "degree p \<noteq> 0 \<Longrightarrow> a * lead_coeff p \<noteq> 0"
  shows "degree (smult a p) = degree p"
  using assms degree_smult_eq_iff by auto

lemma degree_mult_eq2:
  assumes lc: "lead_coeff p * lead_coeff q \<noteq> 0"
  shows "degree (p * q) = degree p + degree q" (is "_ = ?r")
proof(intro antisym[OF degree_mult_le] le_degree, unfold coeff_mult)
  let ?f = "\<lambda>i. coeff p i * coeff q (?r - i)"
  have "(\<Sum>i\<le>?r. ?f i) = sum ?f {..degree p} + sum ?f {Suc (degree p)..?r}"
    by (rule sum_up_index_split)
  also have "sum ?f {Suc (degree p)..?r} = 0"
    proof-
      { fix x assume "x > degree p"
        then have "coeff p x = 0" by (rule coeff_eq_0)
        then have "?f x = 0" by auto
      }
      then show ?thesis by (intro sum.neutral, auto)
    qed
  also have "sum ?f {..degree p} = sum ?f {..<degree p} + ?f (degree p)"
    by(fold lessThan_Suc_atMost, unfold sum.lessThan_Suc, auto)
  also have "sum ?f {..<degree p} = 0"
    proof-
      {fix x assume "x < degree p"
        then have "coeff q (?r - x) = 0" by (intro coeff_eq_0, auto)
        then have "?f x = 0" by auto
      }
      then show ?thesis by (intro sum.neutral, auto)
    qed
  finally show "(\<Sum>i\<le>?r. ?f i) \<noteq> 0" using assms by (auto simp:)
qed

lemma degree_mult_eq_left_unit:
  fixes p q :: "'a :: comm_semiring_1 poly"
  assumes unit: "lead_coeff p dvd 1" and q0: "q \<noteq> 0"
  shows "degree (p * q) = degree p + degree q"
proof(intro degree_mult_eq2 notI)
  from unit obtain c where "lead_coeff p * c = 1" by (elim dvdE,auto)
  then have "c * lead_coeff p = 1" by (auto simp: ac_simps)
  moreover assume "lead_coeff p * lead_coeff q = 0"
    then have "c * lead_coeff p * lead_coeff q = 0" by (auto simp: ac_simps)
  ultimately have "lead_coeff q = 0" by auto
  with q0 show False by auto
qed

context ring_hom begin
lemma monic_degree_map_poly_hom: "monic p \<Longrightarrow> degree (map_poly hom p) = degree p"
  by (auto intro: degree_map_poly)

lemma monic_map_poly_hom: "monic p \<Longrightarrow> monic (map_poly hom p)"
  by (simp add: monic_degree_map_poly_hom)

end

lemma of_nat_zero:
  assumes "CARD('a::nontriv) dvd n"
  shows "(of_nat n :: 'a mod_ring) = 0"
  apply (transfer fixing: n) using assms by (presburger)

abbreviation rebase :: "'a :: nontriv mod_ring \<Rightarrow> 'b :: nontriv mod_ring "("@_" [100]100)
  where "@x \<equiv> of_int (to_int_mod_ring x)"

abbreviation rebase_poly :: "'a :: nontriv mod_ring poly \<Rightarrow> 'b :: nontriv mod_ring poly" ("#_" [100]100)
  where "#x \<equiv> of_int_poly (to_int_poly x)"

lemma rebase_self [simp]:
  "@x = x"
  by (simp add: of_int_of_int_mod_ring)

lemma map_poly_rebase [simp]:
  "map_poly rebase p = #p"
  by (induct p) simp_all

lemma rebase_poly_0: "#0 = 0"
  by simp

lemma rebase_poly_1: "#1 = 1"
  by simp

lemma rebase_poly_pCons[simp]: "#pCons a p = pCons (@a) (#p)"
by(cases "a = 0 \<and> p = 0", simp, fold map_poly_rebase, subst map_poly_pCons, auto)

lemma rebase_poly_self[simp]: "#p = p" by (induct p, auto)

lemma degree_rebase_poly_le: "degree (#p) \<le> degree p"
  by (fold map_poly_rebase, subst degree_map_poly_le, auto)

lemma(in comm_ring_hom) degree_map_poly_unit: assumes "lead_coeff p dvd 1"
  shows "degree (map_poly hom p) = degree p"
  using hom_dvd_1[OF assms] by (auto intro: degree_map_poly)

lemma rebase_poly_eq_0_iff:
  "(#p :: 'a :: nontriv mod_ring poly) = 0 \<longleftrightarrow> (\<forall>i. (@coeff p i :: 'a mod_ring) = 0)" (is "?l \<longleftrightarrow> ?r")
proof(intro iffI)
  assume ?l
  then have "coeff (#p :: 'a mod_ring poly) i = 0" for i by auto
  then show ?r by auto
next
  assume ?r
  then have "coeff (#p :: 'a mod_ring poly) i = 0" for i by auto
  then show ?l by (intro poly_eqI, auto)
qed

lemma mod_mod_le:
  assumes ab: "(a::int) \<le> b" and a0: "0 < a" and c0: "c \<ge> 0" shows "(c mod a) mod b = c mod a"
  by (meson Divides.pos_mod_bound Divides.pos_mod_sign a0 ab less_le_trans mod_pos_pos_trivial)

locale rebase_ge =
  fixes ty1 :: "'a :: nontriv itself" and ty2 :: "'b :: nontriv itself"
  assumes card: "CARD('a) \<le> CARD('b)"
begin

lemma ab: "int CARD('a) \<le> CARD('b)" using card by auto

lemma rebase_eq_0[simp]:
  shows "(@(x :: 'a mod_ring) :: 'b mod_ring) = 0 \<longleftrightarrow> x = 0"
  using card by (transfer, auto)

lemma degree_rebase_poly_eq[simp]:
  shows "degree (#(p :: 'a mod_ring poly) :: 'b mod_ring poly) = degree p"
  by (subst degree_map_poly; simp)

lemma lead_coeff_rebase_poly[simp]:
  "lead_coeff (#(p::'a mod_ring poly) :: 'b mod_ring poly) = @lead_coeff p"
  by simp

lemma to_int_mod_ring_rebase: "to_int_mod_ring(@(x :: 'a mod_ring)::'b mod_ring) = to_int_mod_ring x"
  using card by (transfer, auto)

lemma rebase_id[simp]: "@(@(x::'a mod_ring) :: 'b mod_ring) = @x"
  using card by (transfer, auto)

lemma rebase_poly_id[simp]: "#(#(p::'a mod_ring poly) :: 'b mod_ring poly) = #p" by (induct p, auto)

end

locale rebase_dvd =
  fixes ty1 :: "'a :: nontriv itself" and ty2 :: "'b :: nontriv itself"
  assumes dvd: "CARD('b) dvd CARD('a)"
begin

lemma ab: "CARD('a) \<ge> CARD('b)" by (rule dvd_imp_le[OF dvd], auto)

lemma rebase_id[simp]: "@(@(x::'b mod_ring) :: 'a mod_ring) = x" using ab by (transfer, auto)

lemma rebase_poly_id[simp]: "#(#(p::'b mod_ring poly) :: 'a mod_ring poly) = p" by (induct p, auto)


lemma rebase_of_nat[simp]: "(@(of_nat n :: 'a mod_ring) :: 'b mod_ring) = of_nat n"
  apply transfer apply (rule mod_mod_cancel) using dvd by presburger

lemma mod_1_lift_nat:
  assumes "(of_int (int x) :: 'a mod_ring) = 1"
  shows "(of_int (int x) :: 'b mod_ring) = 1"
proof -
  from assms have "int x mod CARD('a) = 1"
    by transfer
  then have "x mod CARD('a) = 1"
    by (simp add: of_nat_mod [symmetric])
  then have "x mod CARD('b) = 1"
    by (metis dvd mod_mod_cancel one_mod_card)
  then have "int x mod CARD('b) = 1"
    by (simp add: of_nat_mod [symmetric])
  then show ?thesis
    by transfer
qed

sublocale comm_ring_hom "rebase :: 'a mod_ring \<Rightarrow> 'b mod_ring"
proof
  fix x y :: "'a mod_ring"
  show hom_add: "(@(x+y) :: 'b mod_ring) = @x + @y"
    by transfer (simp add: mod_simps dvd mod_mod_cancel)
  show "(@(x*y) :: 'b mod_ring) = @x * @y"
    by transfer (simp add: mod_simps dvd mod_mod_cancel)
qed auto

lemma of_nat_CARD_eq_0[simp]: "(of_nat CARD('a) :: 'b mod_ring) = 0"
  using dvd by (transfer, presburger)

interpretation map_poly_hom: map_poly_comm_ring_hom "rebase :: 'a mod_ring \<Rightarrow> 'b mod_ring"..

sublocale poly: comm_ring_hom "rebase_poly :: 'a mod_ring poly \<Rightarrow> 'b mod_ring poly"
  by (fold map_poly_rebase, unfold_locales)

lemma poly_rebase[simp]: "@poly p x = poly (#(p :: 'a mod_ring poly) :: 'b mod_ring poly) (@(x::'a mod_ring) :: 'b mod_ring)"
  by (fold map_poly_rebase poly_map_poly, rule)

lemma rebase_poly_smult[simp]: "(#(smult a p :: 'a mod_ring poly) :: 'b mod_ring poly) = smult (@a) (#p)"
  by(induct p, auto simp: hom_distribs)

end

locale rebase_mult =
  fixes ty1 :: "'a :: nontriv itself"
    and ty2 :: "'b :: nontriv itself"
    and ty3 :: "'d :: nontriv itself" (* due to some type reason, 'd has to be nontriv. *)
  assumes d: "CARD('a) = CARD('b) * CARD('d)"
begin

sublocale rebase_dvd ty1 ty2 using d by (unfold_locales, auto)

lemma rebase_mult_eq[simp]: "(of_nat CARD('d) * a :: 'a mod_ring) = of_nat CARD('d) * a' \<longleftrightarrow> (@a :: 'b mod_ring) = @a'"
proof-
  from dvd obtain d' where "CARD('a) = d' * CARD('b)" by (elim dvdE, auto)
  then show ?thesis by (transfer, auto simp:d)
qed

lemma rebase_poly_smult_eq[simp]:
  fixes a a' :: "'a mod_ring poly"
  defines "d \<equiv> of_nat CARD('d) :: 'a mod_ring"
  shows "smult d a = smult d a' \<longleftrightarrow> (#a :: 'b mod_ring poly) = #a'" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI)
  assume l: ?l show "?r"
  proof (intro poly_eqI)
    fix n
    from l have "coeff (smult d a) n = coeff (smult d a') n" by auto
    then have "d * coeff a n = d * coeff a' n" by auto
    from this[unfolded d_def rebase_mult_eq]
    show "coeff (#a :: 'b mod_ring poly) n = coeff (#a') n" by auto
  qed
next
  assume r: ?r show ?l
  proof(intro poly_eqI)
    fix n
    from r have "coeff (#a :: 'b mod_ring poly) n = coeff (#a') n" by auto
    then have "(@coeff a n :: 'b mod_ring) = @coeff a' n" by auto
    from this[folded d_def rebase_mult_eq]
    show "coeff (smult d a) n = coeff (smult d a') n" by auto
  qed
qed

lemma rebase_eq_0_imp_ex_mult:
  "(@(a :: 'a mod_ring) :: 'b mod_ring) = 0 \<Longrightarrow> (\<exists>c :: 'd mod_ring. a = of_nat CARD('b) * @c)" (is "?l \<Longrightarrow> ?r")
proof(cases "CARD('a) = CARD('b)")
  case True then show "?l \<Longrightarrow> ?r"
    by (transfer, auto)
next
  case False
  have [simp]: "int CARD('b) mod int CARD('a) = int CARD('b)"
    by(rule mod_pos_pos_trivial, insert ab False, auto)
  {
    fix a
    assume a: "0 \<le> a" "a < int CARD('a)" and mod: "a mod int CARD('b) = 0"
    from mod have "int CARD('b) dvd a" by auto
    then obtain i where *: "a = int CARD('b) * i" by (elim dvdE, auto)
    from * a have "i < int CARD('d)" by (simp add:d)
    moreover
      hence "(i mod int CARD('a)) = i"
        by (metis dual_order.order_iff_strict less_le_trans not_le of_nat_less_iff "*" a(1) a(2)
             mod_pos_pos_trivial mult_less_cancel_right1 nat_neq_iff nontriv of_nat_1)
      with * a have "a = int CARD('b) * (i mod int CARD('a)) mod int CARD('a)"
        by (auto simp:d)
    moreover from * a have "0 \<le> i"
      using linordered_semiring_strict_class.mult_pos_neg of_nat_0_less_iff zero_less_card_finite
      by (simp add: zero_le_mult_iff)
    ultimately have "\<exists>i\<ge>0. i < int CARD('d) \<and> a = int CARD('b) * (i mod int CARD('a)) mod int CARD('a)"
      by (auto intro: exI[of _ i])
  }
  then show "?l \<Longrightarrow> ?r" by (transfer, auto simp:d)
qed

lemma rebase_poly_eq_0_imp_ex_smult:
  "(#(p :: 'a mod_ring poly) :: 'b mod_ring poly) = 0 \<Longrightarrow>
   (\<exists>p' :: 'd mod_ring poly. (p = 0 \<longleftrightarrow> p' = 0) \<and> degree p' \<le> degree p \<and> p = smult (of_nat CARD('b)) (#p'))"
  (is "?l \<Longrightarrow> ?r")
proof(induct p)
  case 0
  then show ?case by (intro exI[of _ 0],auto)
next
  case IH: (pCons a p)
  from IH(3) have "(#p :: 'b mod_ring poly) = 0" by auto
  from IH(2)[OF this] obtain p' :: "'d mod_ring poly"
  where *: "p = 0 \<longleftrightarrow> p' = 0" "degree p' \<le> degree p" "p = smult (of_nat CARD('b)) (#p')" by (elim exE conjE)
  from IH have "(@a :: 'b mod_ring) = 0" by auto
  from rebase_eq_0_imp_ex_mult[OF this]
  obtain a' :: "'d mod_ring" where a': "of_nat CARD('b) * (@a') = a" by auto
  from IH(1) have "pCons a p \<noteq> 0" by auto
  moreover from *(1,2) have "degree (pCons a' p') \<le> degree (pCons a p)" by auto
  moreover from a' *(3)
  have "pCons a p = smult (of_nat CARD('b)) (#pCons a' p')" by auto
  ultimately show ?case by (intro exI[of _ "pCons a' p'"], auto)
qed

end



lemma mod_mod_nat[simp]: "a mod b mod (b * c :: nat) = a mod b" by (simp add: Divides.mod_mult2_eq)

locale Knuth_ex_4_6_2_22_base =
  fixes ty_p :: "'p :: nontriv itself"
    and ty_q :: "'q :: nontriv itself"
    and ty_pq :: "'pq :: nontriv itself"
  assumes pq: "CARD('pq) = CARD('p) * CARD('q)"
    and p_dvd_q: "CARD('p) dvd CARD('q)"
begin

sublocale rebase_q_to_p: rebase_dvd "TYPE('q)" "TYPE('p)" using p_dvd_q by (unfold_locales, auto)
sublocale rebase_pq_to_p: rebase_mult "TYPE('pq)" "TYPE('p)" "TYPE('q)" using pq by (unfold_locales, auto)
sublocale rebase_pq_to_q: rebase_mult "TYPE('pq)" "TYPE('q)" "TYPE('p)" using pq by (unfold_locales, auto)

sublocale rebase_p_to_q: rebase_ge "TYPE('p)" "TYPE ('q)" by (unfold_locales, insert p_dvd_q, simp add: dvd_imp_le)
sublocale rebase_p_to_pq: rebase_ge "TYPE('p)" "TYPE ('pq)" by (unfold_locales, simp add: pq)
sublocale rebase_q_to_pq: rebase_ge "TYPE('q)" "TYPE ('pq)" by (unfold_locales, simp add: pq)


(* TODO: needs ugly workaround to fix 'p... *)
definition "p \<equiv> if (ty_p :: 'p itself) = ty_p then CARD('p) else undefined"
lemma p[simp]: "p \<equiv> CARD('p)" unfolding p_def by auto

definition "q \<equiv> if (ty_q :: 'q itself) = ty_q then CARD('q) else undefined"
lemma q[simp]: "q = CARD('q)" unfolding q_def by auto

lemma p1: "int p > 1"
  using nontriv [where ?'a = 'p] p by simp
lemma q1: "int q > 1"
  using nontriv [where ?'a = 'q] q by simp
lemma q0: "int q > 0"
  using q1 by auto

lemma pq2[simp]: "CARD('pq) = p * q" using pq by simp

lemma qq_eq_0[simp]: "(of_nat CARD('q) * of_nat CARD('q) :: 'pq mod_ring) = 0"
proof-
  have "(of_nat (q * q) :: 'pq mod_ring) = 0" by (rule of_nat_zero, auto simp: p_dvd_q)
  then show ?thesis by auto
qed

lemma of_nat_q[simp]: "of_nat q :: 'q mod_ring \<equiv> 0" by (fold of_nat_card_eq_0, auto)

lemma rebase_rebase[simp]: "(@(@(x::'pq mod_ring) :: 'q mod_ring) :: 'p mod_ring) = @x"
  using p_dvd_q by (transfer) (simp add: mod_mod_cancel)

lemma rebase_rebase_poly[simp]: "(#(#(f::'pq mod_ring poly) :: 'q mod_ring poly) :: 'p mod_ring poly) = #f"
  by (induct f, auto)

end

definition dupe_monic where
  "dupe_monic D H S T U = (case pdivmod_monic (T * U) D of (q,r) \<Rightarrow> (S * U + H * q, r))"

lemma dupe_monic:
  fixes D :: "'a :: prime_card mod_ring poly"
  assumes 1: "D*S + H*T = 1"
  and mon: "monic D"
  and dupe: "dupe_monic D H S T U = (A,B)" 
  shows "A * D + B * H = U" "B = 0 \<or> degree B < degree D"
    "coprime D H \<Longrightarrow> A' * D + B' * H = U \<Longrightarrow> B' = 0 \<or> degree B' < degree D \<Longrightarrow> A' = A \<and> B' = B"
proof -
  obtain q r where div: "pdivmod_monic (T * U) D = (q,r)" by force
  from dupe[unfolded dupe_monic_def div split]
  have A: "A = (S * U + H * q)" and B: "B = r" by auto
  from pdivmod_monic[OF mon div] have TU: "T * U = D * q + r" and 
    deg: "r = 0 \<or> degree r < degree D" by auto
  hence r: "r = T * U - D * q" by simp
  have "A * D + B * H = (S * U + H * q) * D + (T * U - D * q) * H" unfolding A B r by simp
  also have "... = (D * S + H * T) * U" by (simp add: field_simps)
  also have "D * S + H * T = 1" using 1 by simp  
  finally show eq: "A * D + B * H = U" by simp
  show degB: "B = 0 \<or> degree B < degree D" using deg unfolding B by (cases "r = 0", auto)
  assume another: "A' * D + B' * H = U" and degB': "B' = 0 \<or> degree B' < degree D" 
    and cop: "coprime D H"
  from degB have degB: "B = 0 \<or> degree B < degree D" by auto
  from degB' have degB': "B' = 0 \<or> degree B' < degree D" by auto
  from mon have D0: "D \<noteq> 0" by auto
  from another eq have "A' * D + B' * H = A * D + B * H" by simp
  from uniqueness_poly_equality[OF cop degB' degB D0 this]
  show "A' = A \<and> B' = B" by auto
qed


locale Knuth_ex_4_6_2_22_main = Knuth_ex_4_6_2_22_base p_ty q_ty pq_ty
  for p_ty :: "'p::nontriv itself"
  and q_ty :: "'q::nontriv itself"
  and pq_ty :: "'pq::nontriv itself" +
  fixes a b :: "'p mod_ring poly" and u :: "'pq mod_ring poly" and v w :: "'q mod_ring poly"
  assumes uvw: "(#u :: 'q mod_ring poly) = v * w"
      and degu: "degree u = degree v + degree w" (* not in Knuth's book *)
      and avbw: "(a * #v + b * #w :: 'p mod_ring poly) = 1"
      and monic_v: "monic v" (* stronger than Knuth's *)
(* not needed!
      and aw: "degree a < degree w" *)
      and bv: "degree b < degree v"
begin

lemma deg_v: "degree (#v :: 'p mod_ring poly) = degree v"
  using monic_v by (simp add: of_int_hom.monic_degree_map_poly_hom)

lemma u0: "u \<noteq> 0" using degu bv by auto

lemma ex_f: "\<exists>f :: 'p mod_ring poly. u = #v * #w + smult (of_nat q) (#f)"
proof-
  from uvw have "(#(u - #v * #w) :: 'q mod_ring poly) = 0" by (auto simp:hom_distribs)
  from rebase_pq_to_q.rebase_poly_eq_0_imp_ex_smult[OF this]
  obtain f :: "'p mod_ring poly" where "u - #v * #w = smult (of_nat q) (#f)" by force
  then have "u = #v * #w + smult (of_nat q) (#f)" by (metis add_diff_cancel_left' add_diff_eq)
  then show ?thesis by (intro exI[of _ f], auto)
qed

definition "f :: 'p mod_ring poly \<equiv> SOME f. u = #v * #w + smult (of_nat q) (#f)"

lemma u: "u = #v * #w + smult (of_nat q) (#f)"
  using ex_f[folded some_eq_ex] f_def by auto

lemma t_ex: "\<exists>t :: 'p mod_ring poly. degree (b * f - t * #v) < degree v"
proof-
  define v' where "v' \<equiv> #v :: 'p mod_ring poly"
  from monic_v
  have 1: "lead_coeff v' = 1" by (simp add: v'_def deg_v)
  then have 4: "v' \<noteq> 0" by auto
  obtain t rem :: "'p mod_ring poly"
  where "pseudo_divmod (b * f) v' = (t,rem)" by force
  from pseudo_divmod[OF 4 this, folded, unfolded 1]
  have "b * f = v' * t + rem" and deg: "rem = 0 \<or> degree rem < degree v'" by auto
  then have "rem = b * f - t * v'" by(auto simp: ac_simps)
  also have "... = b * f - #(#t :: 'p mod_ring poly) * v'" (is "_ = _ - ?t * v'") by simp
  also have "... = b * f - ?t * #v"
    by (unfold v'_def, rule)
  finally have "degree rem = degree ..." by auto
  with deg bv have "degree (b * f - ?t * #v :: 'p mod_ring poly) < degree v" by (auto simp: v'_def deg_v)
  then show ?thesis by (rule exI)
qed

definition t where "t \<equiv> SOME t :: 'p mod_ring poly. degree (b * f - t * #v) < degree v"

definition "v' \<equiv> b * f - t * #v"
definition "w' \<equiv> a * f + t * #w"

lemma f: "w' * #v + v' * #w = f" (is "?l = _")
proof-
  have "?l = f * (a * #v + b * #w :: 'p mod_ring poly)" by (simp add: v'_def w'_def ring_distribs ac_simps)
  also
    from avbw have "(#(a * #v + b * #w) :: 'p mod_ring poly) = 1" by auto
    then have "(a * #v + b * #w :: 'p mod_ring poly) = 1" by auto
  finally show ?thesis by auto
qed

lemma degv': "degree v' < degree v" by (unfold v'_def t_def, rule someI_ex, rule t_ex)

lemma degqf[simp]: "degree (smult (of_nat CARD('q)) (#f :: 'pq mod_ring poly)) = degree (#f :: 'pq mod_ring poly)"
proof (intro degree_smult_eqI)
  assume "degree (#f :: 'pq mod_ring poly) \<noteq> 0"
  then have f0: "degree f \<noteq> 0" by simp
  moreover define l where "l \<equiv> lead_coeff f"
  ultimately have l0: "l \<noteq> 0" by auto
  then show "of_nat CARD('q) * lead_coeff (#f::'pq mod_ring poly) \<noteq> 0"
  apply (unfold rebase_p_to_pq.lead_coeff_rebase_poly, fold l_def)
  apply (transfer)
  using q1 by (simp add: pq mod_mod_cancel)
qed

lemma degw': "degree w' \<le> degree w"
proof(rule ccontr)
  let ?f = "#f :: 'pq mod_ring poly"
  let ?qf = "smult (of_nat q) (#f) :: 'pq mod_ring poly"

  have "degree (#w::'p mod_ring poly) \<le> degree w" by (rule degree_rebase_poly_le)
  also assume "\<not> degree w' \<le> degree w"
  then have 1: "degree w < degree w'" by auto
  finally have 2: "degree (#w :: 'p mod_ring poly) < degree w'" by auto
  then have w'0: "w' \<noteq> 0" by auto

  have 3: "degree (#v * w') = degree (#v :: 'p mod_ring poly) + degree w'"
      using monic_v[unfolded] by (intro degree_monic_mult[OF _ w'0], auto simp: deg_v)

  have "degree f \<le> degree u"
  proof(rule ccontr)
    assume "\<not>?thesis"
    then have *: "degree u < degree f" by auto
    with degu have 1: "degree v + degree w < degree f" by auto
    define lcf where "lcf \<equiv> lead_coeff f"
    with 1 have lcf0: "lcf \<noteq> 0" by (unfold, auto)
    have "degree f = degree ?qf" by simp
    also have "... = degree (#v * #w + ?qf)"
    proof(rule sym, rule degree_add_eq_right)
      from 1 degree_mult_le[of "#v::'pq mod_ring poly" "#w"]
      show "degree (#v * #w :: 'pq mod_ring poly) < degree ?qf" by simp
    qed
    also have "... < degree f" using * u by auto
    finally show "False" by auto
  qed
  with degu have "degree f \<le> degree v + degree w" by auto
  also note f[symmetric]
  finally have "degree (w' * #v + v' * #w) \<le> degree v + degree w".
  moreover have "degree (w' * #v + v' * #w) = degree (w' * #v)"
  proof(rule degree_add_eq_left)
    have "degree (v' * #w) \<le> degree v' + degree (#w :: 'p mod_ring poly)"
      by(rule degree_mult_le)
    also have "... < degree v + degree (#w :: 'p mod_ring poly)" using degv' by auto
    also have "... < degree (#v :: 'p mod_ring poly) + degree w'" using 2 by (auto simp: deg_v)
    also have "... = degree (#v * w')" using 3 by auto
    finally show "degree (v' * #w) < degree (w' * #v)" by (auto simp: ac_simps)
  qed
  ultimately have "degree (w' * #v) \<le> degree v + degree w" by auto
  moreover
    from 3 have "degree (w' * #v) = degree w' + degree v" by (auto simp: ac_simps deg_v)
    with 1 have "degree w + degree v < degree (w' * #v)" by auto
  ultimately show False by auto
qed

abbreviation "qv' \<equiv> smult (of_nat q) (#v') :: 'pq mod_ring poly"
abbreviation "qw' \<equiv> smult (of_nat q) (#w') :: 'pq mod_ring poly"

abbreviation "V \<equiv> #v + qv'"
abbreviation "W \<equiv> #w + qw'"

lemma vV: "v = #V" by (auto simp: v'_def hom_distribs)

lemma wW: "w = #W" by (auto simp: w'_def hom_distribs)

lemma uVW: "u = V * W"
  by (subst u, fold f, simp add: ring_distribs add.left_cancel smult_add_right[symmetric] hom_distribs)

lemma degV: "degree V = degree v"
  and lcV: "lead_coeff V = @lead_coeff v"
  and degW: "degree W = degree w"
proof-
  from p1 q1 have "int p < int p * int q" by auto
  from less_trans[OF _ this]
  have 1: "l < int p \<Longrightarrow> l < int p * int q" for l by auto
  have "degree qv' = degree (#v' :: 'pq mod_ring poly)"
  proof (rule degree_smult_eqI, safe, unfold rebase_p_to_pq.degree_rebase_poly_eq)
    define l where "l \<equiv> lead_coeff v'"
    assume "degree v' > 0"
    then have "lead_coeff v' \<noteq> 0" by auto
    then have "(@l :: 'pq mod_ring) \<noteq> 0" by (simp add: l_def)
    then have "(of_nat q * @l :: 'pq mod_ring) \<noteq> 0"
      apply (transfer fixing:q_ty) using p_dvd_q p1 q1 1 by auto
    moreover assume " of_nat q * coeff (#v') (degree v') = (0 :: 'pq mod_ring)"
    ultimately show False by (auto simp: l_def)
  qed
  also from degv' have "... < degree (#v::'pq mod_ring poly)" by simp
  finally have *: "degree qv' < degree (#v :: 'pq mod_ring poly)".
  from degree_add_eq_left[OF *]
  show **: "degree V = degree v" by (simp add: v'_def)

  from * have "coeff qv' (degree v) = 0" by (intro coeff_eq_0, auto)
  then show "lead_coeff V = @lead_coeff v" by (unfold **, auto simp: v'_def)

  with u0 uVW have "degree (V * W) = degree V + degree W"
    by (intro degree_mult_eq_left_unit, auto simp: monic_v)
  from this[folded uVW, unfolded degu **] show "degree W = degree w" by auto
qed

end

locale Knuth_ex_4_6_2_22_prime = Knuth_ex_4_6_2_22_main ty_p ty_q ty_pq a b u v w
  for ty_p :: "'p :: prime_card itself"
  and ty_q :: "'q :: nontriv itself"
  and ty_pq :: "'pq :: nontriv itself"
  and a b u v w +
  assumes coprime: "coprime (#v :: 'p mod_ring poly) (#w)" (* not in Knuth *)

begin

lemma coprime_preserves: "coprime (#V :: 'p mod_ring poly) (#W)"
  apply (intro coprimeI,simp add: rebase_q_to_p.of_nat_CARD_eq_0[simplified] hom_distribs)
  using coprime by (elim coprimeE, auto)

lemma pre_unique:
  assumes f2: "w'' * #v + v'' * #w = f"
      and degv'': "degree v'' < degree v"
  shows "v'' = v' \<and> w'' = w'"
proof(intro conjI)
  from f f2
  have "w' * #v + v' * #w = w'' * #v + v'' * #w" by auto
  also have "... - w'' * #v = v'' * #w" by auto
  also have "... - v' * #w = (v''- v') * #w" by (auto simp: left_diff_distrib)
  finally have *: "(w' - w'') * #v = (v''- v') * #w" by (auto simp: left_diff_distrib)
  then have "#v dvd (v'' - v') * #w" by (auto intro: dvdI[of _ _ "w' - w''"] simp: ac_simps)
  with coprime have "#v dvd v'' - v'"
    by (simp add: coprime_dvd_mult_left_iff)
  moreover have "degree (v'' - v') < degree v" by (rule degree_diff_less[OF degv'' degv'])
  ultimately have "v'' - v' = 0"
    by (metis deg_v degree_0 gr_implies_not_zero poly_divides_conv0)
  then show "v'' = v'" by auto
  with * have "(w' - w'') * #v = 0" by auto
  with bv have "w' - w'' = 0"
    by (metis deg_v degree_0 gr_implies_not_zero mult_eq_0_iff)
  then show "w'' = w'" by auto
qed

lemma unique:
  assumes vV2: "v = #V2" and wW2: "w = #W2" and uVW2: "u = V2 * W2"
      and degV2: "degree V2 = degree v" and degW2: "degree W2 = degree w"
      and lc: "lead_coeff V2 = @lead_coeff v"
  shows "V2 = V" "W2 = W"
proof-
  from vV2 have "(#(V2 - #v) :: 'q mod_ring poly) = 0" by (auto simp: hom_distribs)
  from rebase_pq_to_q.rebase_poly_eq_0_imp_ex_smult[OF this]
  obtain v'' :: "'p mod_ring poly"
  where deg: "degree v'' \<le> degree (V2 - #v)"
    and v'': "V2 - #v = smult (of_nat CARD('q)) (#v'')" by (elim exE conjE)
  then have V2: "V2 = #v + ..." by (metis add_diff_cancel_left' diff_add_cancel)

  from lc[unfolded degV2, unfolded V2]
  have "of_nat q * (@coeff v'' (degree v) :: 'pq mod_ring) = of_nat q * 0" by auto
  from this[unfolded q rebase_pq_to_p.rebase_mult_eq]
  have "coeff v'' (degree v) = 0" by simp
  moreover have "degree v'' \<le>  degree v" using deg degV2
    by (metis degree_diff_le le_antisym nat_le_linear rebase_q_to_pq.degree_rebase_poly_eq)
  ultimately have degv'': "degree v'' < degree v"
    using bv eq_zero_or_degree_less by fastforce

  from wW2 have "(#(W2 - #w) :: 'q mod_ring poly) = 0" by (auto simp: hom_distribs)
  from rebase_pq_to_q.rebase_poly_eq_0_imp_ex_smult[OF this] pq
  obtain w'' :: "'p mod_ring poly" where w'': "W2 - #w = smult (of_nat q) (#w'')" by force
  then have W2: "W2 = #w + ..." by (metis add_diff_cancel_left' diff_add_cancel)

  have "u = #v * #w + smult (of_nat q) (#w'' * #v + #v'' * #w) + smult (of_nat (q * q)) (#v'' * #w'')"
    by(simp add: uVW2 V2 W2 ring_distribs smult_add_right ac_simps)
  also have "smult (of_nat (q * q)) (#v'' * #w'' :: 'pq mod_ring poly) = 0" by simp
  finally have "u - #v * #w = smult (of_nat q) (#w'' * #v + #v'' * #w)" by auto
  also have "u - #v * #w = smult (of_nat q) (#f)" by (subst u, simp)
  finally have "w'' * #v + v'' * #w = f" by (simp add: hom_distribs)
  from pre_unique[OF this degv'']
  have pre: "v'' = v'" "w'' = w'" by auto
  with V2 W2 show "V2 = V" "W2 = W" by auto
qed

end

definition
  "hensel_1 (ty ::'p :: prime_card itself)
    (u :: 'pq :: nontriv mod_ring poly) (v :: 'q :: nontriv mod_ring poly) (w :: 'q mod_ring poly) \<equiv>
   if v = 1 then (1,u) else
   let (s, t) = bezout_coefficients (#v :: 'p mod_ring poly) (#w) in
   let (a, b) = dupe_monic (#v::'p mod_ring poly) (#w) s t 1 in
   (Knuth_ex_4_6_2_22_main.V TYPE('q) b u v w, Knuth_ex_4_6_2_22_main.W TYPE('q) a b u v w)"

lemma hensel_1:
  fixes u :: "'pq :: nontriv mod_ring poly"
    and v w :: "'q :: nontriv mod_ring poly"
  assumes "CARD('pq) = CARD('p :: prime_card) * CARD('q)"
      and "CARD('p) dvd CARD('q)"
      and uvw: "#u = v * w"
      and degu: "degree u = degree v + degree w"
      and monic: "monic v"
      and coprime: "coprime (#v :: 'p mod_ring poly) (#w)"
      and out: "hensel_1 TYPE('p) u v w = (V',W')"
  shows "u = V' * W' \<and> v = #V' \<and> w = #W' \<and> degree V' = degree v \<and> degree W' = degree w \<and>
         monic V' \<and> coprime (#V' :: 'p mod_ring poly) (#W')" (is ?main)
    and "(\<forall>V'' W''. u = V'' * W'' \<longrightarrow> v = #V'' \<longrightarrow> w = #W'' \<longrightarrow>
          degree V'' = degree v \<longrightarrow> degree W'' = degree w \<longrightarrow> lead_coeff V'' = @lead_coeff v \<longrightarrow>
          V'' = V' \<and> W'' = W')" (is "?unique")
proof-
  from monic
  have degv: "degree (#v :: 'p mod_ring poly) = degree v"
    by (simp add: of_int_hom.monic_degree_map_poly_hom)
  from monic
  have monic2: "monic (#v :: 'p mod_ring poly)"
    by (auto simp: degv)
  obtain s t where bezout: "bezout_coefficients (#v :: 'p mod_ring poly) (#w) = (s, t)"
    by (auto simp add: prod_eq_iff)
  then have "s * #v + t * #w = gcd (#v :: 'p mod_ring poly) (#w)"
    by (rule bezout_coefficients)
  with coprime have vswt: "#v * s + #w * t = 1"
    by (simp add: ac_simps)
  obtain a b where dupe: "dupe_monic (#v) (#w) s t 1 = (a, b)" by force
  from dupe_monic(1,2)[OF vswt monic2, where U=1, unfolded this]
  have avbw: "a * #v + b * #w = 1" and degb: "b = 0 \<or> degree b < degree (#v::'p mod_ring poly)" by auto
  have "?main \<and> ?unique"
  proof (cases "b = 0")
    case b0: True
    with avbw have "a * #v = 1" by auto
    then have "degree (#v :: 'p mod_ring poly) = 0"
      by (metis degree_1 degree_mult_eq_0 mult_zero_left one_neq_zero)
    from this[unfolded degv] monic_degree_0[OF monic[unfolded]]
    have 1: "v = 1" by auto
    with b0 out uvw have 2: "V' = 1" "W' = u"
      by (unfold split hensel_1_def Let_def dupe) auto
    have 3: ?unique apply (simp add: 1 2) by (metis monic_degree_0 mult.left_neutral)
    with uvw degu show ?thesis unfolding 1 2 by auto
  next
    case b0: False
    with degb degv have degb: "degree b < degree v" by auto
    then have v1: "v \<noteq> 1" by auto
    interpret Knuth_ex_4_6_2_22_prime "TYPE('p)" "TYPE('q)" "TYPE('pq)" a b
      by (unfold_locales; fact assms degb avbw)
    show ?thesis
    proof (intro conjI)
      from out [unfolded hensel_1_def] v1
      have 1 [simp]: "V' = V" "W' = W" by (auto simp: bezout dupe)
      from uVW show "u = V' * W'" by auto
      from degV show [simp]: "degree V' = degree v" by simp
      from degW show [simp]: "degree W' = degree w" by simp
      from lcV have "lead_coeff V' = @lead_coeff v" by simp
      with monic_v show "monic V'" by (simp add:)
      from vV show "v = #V'" by simp
      from wW show "w = #W'" by simp
      from coprime_preserves show "coprime (#V' :: 'p mod_ring poly) (#W')" by simp
      show 9: ?unique by (unfold 1, intro allI conjI impI; rule unique)
    qed
  qed
  then show ?main ?unique by (fact conjunct1, fact conjunct2)
qed

end
