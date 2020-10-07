(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Polynomial Reduction\<close>

theory Reduction
imports "Polynomials.MPoly_Type_Class_Ordered" Confluence
begin

text \<open>This theory formalizes the concept of @{emph \<open>reduction\<close>} of polynomials by polynomials.\<close>

context ordered_term
begin

definition red_single :: "('t \<Rightarrow>\<^sub>0 'b::field) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'a \<Rightarrow> bool"
  where "red_single p q f t \<longleftrightarrow> (f \<noteq> 0 \<and> lookup p (t \<oplus> lt f) \<noteq> 0 \<and>
                                q = p - monom_mult ((lookup p (t \<oplus> lt f)) / lc f) t f)"

definition red :: "('t \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "red F p q \<longleftrightarrow> (\<exists>f\<in>F. \<exists>t. red_single p q f t)"

definition is_red :: "('t \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "is_red F a \<longleftrightarrow> \<not> relation.is_final (red F) a"

subsection \<open>Basic Properties of Reduction\<close>

lemma red_setI:
  assumes "f \<in> F" and a: "red_single p q f t"
  shows "red F p q"
  unfolding red_def
proof
  from \<open>f \<in> F\<close> show "f \<in> F" .
next
  from a show "\<exists>t. red_single p q f t" ..
qed

lemma red_setE:
  assumes "red F p q"
  obtains f and t where "f \<in> F" and "red_single p q f t"
proof -
  from assms obtain f where "f \<in> F" and t: "\<exists>t. red_single p q f t" unfolding red_def by auto
  from t obtain t where "red_single p q f t" ..
  from \<open>f \<in> F\<close> this show "?thesis" ..
qed

lemma red_empty: "\<not> red {} p q"
  by (rule, elim red_setE, simp)

lemma red_singleton_zero: "\<not> red {0} p q"
  by (rule, elim red_setE, simp add: red_single_def)

lemma red_union: "red (F \<union> G) p q = (red F p q \<or> red G p q)"
proof
  assume "red (F \<union> G) p q"
  from red_setE[OF this] obtain f t where "f \<in> F \<union> G" and r: "red_single p q f t" .
  from \<open>f \<in> F \<union> G\<close> have "f \<in> F \<or> f \<in> G" by simp
  thus "red F p q \<or> red G p q"
  proof
    assume "f \<in> F" 
    show ?thesis by (intro disjI1, rule red_setI[OF \<open>f \<in> F\<close> r])
  next
    assume "f \<in> G" 
    show ?thesis by (intro disjI2, rule red_setI[OF \<open>f \<in> G\<close> r])
  qed
next
  assume "red F p q \<or> red G p q"
  thus "red (F \<union> G) p q"
  proof
    assume "red F p q"
    from red_setE[OF this] obtain f t where "f \<in> F" and "red_single p q f t" .
    show ?thesis by (intro red_setI[of f _ _ _ t], rule UnI1, rule \<open>f \<in> F\<close>, fact)
  next
    assume "red G p q"
    from red_setE[OF this] obtain f t where "f \<in> G" and "red_single p q f t" .
    show ?thesis by (intro red_setI[of f _ _ _ t], rule UnI2, rule \<open>f \<in> G\<close>, fact)
  qed
qed

lemma red_unionI1:
  assumes "red F p q"
  shows "red (F \<union> G) p q"
  unfolding red_union by (rule disjI1, fact)

lemma red_unionI2:
  assumes "red G p q"
  shows "red (F \<union> G) p q"
  unfolding red_union by (rule disjI2, fact)

lemma red_subset:
  assumes "red G p q" and "G \<subseteq> F"
  shows "red F p q"
proof -
  from \<open>G \<subseteq> F\<close> obtain H where "F = G \<union> H" by auto
  show ?thesis unfolding \<open>F = G \<union> H\<close> by (rule red_unionI1, fact)
qed

lemma red_union_singleton_zero: "red (F \<union> {0}) = red F"
  by (intro ext, simp only: red_union red_singleton_zero, simp)

lemma red_minus_singleton_zero: "red (F - {0}) = red F"
  by (metis Un_Diff_cancel2 red_union_singleton_zero)

lemma red_rtrancl_subset:
  assumes major: "(red G)\<^sup>*\<^sup>* p q" and "G \<subseteq> F"
  shows "(red F)\<^sup>*\<^sup>* p q"
  using major
proof (induct rule: rtranclp_induct)
  show "(red F)\<^sup>*\<^sup>* p p" ..
next
  fix r q
  assume "red G r q" and "(red F)\<^sup>*\<^sup>* p r"
  show "(red F)\<^sup>*\<^sup>* p q"
  proof
    show "(red F)\<^sup>*\<^sup>* p r" by fact
  next
    from red_subset[OF \<open>red G r q\<close> \<open>G \<subseteq> F\<close>] show "red F r q" .
  qed
qed

lemma red_singleton: "red {f} p q \<longleftrightarrow> (\<exists>t. red_single p q f t)"
  unfolding red_def
proof
  assume "\<exists>f\<in>{f}. \<exists>t. red_single p q f t"
  from this obtain f0 where "f0 \<in> {f}" and a: "\<exists>t. red_single p q f0 t" ..
  from \<open>f0 \<in> {f}\<close> have "f0 = f" by simp
  from this a show "\<exists>t. red_single p q f t" by simp
next
  assume a: "\<exists>t. red_single p q f t"
  show "\<exists>f\<in>{f}. \<exists>t. red_single p q f t"
  proof (rule, simp)
    from a show "\<exists>t. red_single p q f t" .
  qed
qed

lemma red_single_lookup:
  assumes "red_single p q f t"
  shows "lookup q (t \<oplus> lt f) = 0"
  using assms unfolding red_single_def
proof
  assume "f \<noteq> 0" and "lookup p (t \<oplus> lt f) \<noteq> 0 \<and> q = p - monom_mult (lookup p (t \<oplus> lt f) / lc f) t f"
  hence "lookup p (t \<oplus> lt f) \<noteq> 0" and q_def: "q = p - monom_mult (lookup p (t \<oplus> lt f) / lc f) t f"
    by auto
  from lookup_minus[of p "monom_mult (lookup p (t \<oplus> lt f) / lc f) t f" "t \<oplus> lt f"]
       lookup_monom_mult_plus[of "lookup p (t \<oplus> lt f) / lc f" t f "lt f"]
       lc_not_0[OF \<open>f \<noteq> 0\<close>]
    show ?thesis unfolding q_def lc_def by simp
qed

lemma red_single_higher:
  assumes "red_single p q f t"
  shows "higher q (t \<oplus> lt f) = higher p (t \<oplus> lt f)"
  using assms unfolding higher_eq_iff red_single_def
proof (intro allI, intro impI)
  fix u
  assume a: "t \<oplus> lt f \<prec>\<^sub>t u"
    and "f \<noteq> 0 \<and> lookup p (t \<oplus> lt f) \<noteq> 0 \<and> q = p - monom_mult (lookup p (t \<oplus> lt f) / lc f) t f"
  hence "f \<noteq> 0"
    and "lookup p (t \<oplus> lt f) \<noteq> 0"
    and q_def: "q = p - monom_mult (lookup p (t \<oplus> lt f) / lc f) t f"
    by simp_all
  from \<open>lookup p (t \<oplus> lt f) \<noteq> 0\<close> lc_not_0[OF \<open>f \<noteq> 0\<close>] have c_not_0: "lookup p (t \<oplus> lt f) / lc f \<noteq> 0"
    by (simp add: field_simps)
  from q_def lookup_minus[of p "monom_mult (lookup p (t \<oplus> lt f) / lc f) t f"]
    have q_lookup: "\<And>s. lookup q s = lookup p s - lookup (monom_mult (lookup p (t \<oplus> lt f) / lc f) t f) s"
    by simp
  from a lt_monom_mult[OF c_not_0 \<open>f \<noteq> 0\<close>, of t]
    have "\<not> u \<preceq>\<^sub>t lt (monom_mult (lookup p (t \<oplus> lt f) / lc f) t f)" by simp
  with lt_max[of "monom_mult (lookup p (t \<oplus> lt f) / lc f) t f" u]
  have "lookup (monom_mult (lookup p (t \<oplus> lt f) / lc f) t f) u = 0" by auto
  thus "lookup q u = lookup p u" using q_lookup[of u] by simp
qed

lemma red_single_ord:
  assumes "red_single p q f t"
  shows "q \<prec>\<^sub>p p"
  unfolding ord_strict_higher
proof (intro exI, intro conjI)
  from red_single_lookup[OF assms] show "lookup q (t \<oplus> lt f) = 0" .
next
  from assms show "lookup p (t \<oplus> lt f) \<noteq> 0" unfolding red_single_def by simp
next
  from red_single_higher[OF assms] show "higher q (t \<oplus> lt f) = higher p (t \<oplus> lt f)" .
qed

lemma red_single_nonzero1:
  assumes "red_single p q f t"
  shows "p \<noteq> 0"
proof
  assume "p = 0"
  from this red_single_ord[OF assms] ord_p_zero_min[of q] show False by simp
qed

lemma red_single_nonzero2:
  assumes "red_single p q f t"
  shows "f \<noteq> 0"
proof
  assume "f = 0"
  from assms monom_mult_zero_right have "f \<noteq> 0" by (simp add: red_single_def)
  from this \<open>f = 0\<close> show False by simp
qed

lemma red_single_self:
  assumes "p \<noteq> 0"
  shows "red_single p 0 p 0"
proof -
  from lc_not_0[OF assms] have lc: "lc p \<noteq> 0" .
  show ?thesis unfolding red_single_def
  proof (intro conjI)
    show "p \<noteq> 0" by fact
  next
    from lc show "lookup p (0 \<oplus> lt p) \<noteq> 0" unfolding lc_def by (simp add: term_simps)
  next
    from lc have "(lookup p (0 \<oplus> lt p)) / lc p = 1" unfolding lc_def by (simp add: term_simps)
    from this monom_mult_one_left[of p] show "0 = p - monom_mult (lookup p (0 \<oplus> lt p) / lc p) 0 p"
      by simp
  qed
qed

lemma red_single_trans:
  assumes "red_single p p0 f t" and "lt g adds\<^sub>t lt f" and "g \<noteq> 0"
  obtains p1 where "red_single p p1 g (t + (lp f - lp g))"
proof -
  let ?s = "t + (lp f - lp g)"
  let ?p = "p - monom_mult (lookup p (?s \<oplus> lt g) / lc g) ?s g"
  have "red_single p ?p g ?s" unfolding red_single_def
  proof (intro conjI)
    from assms(2) have eq: "?s \<oplus> lt g = t \<oplus> lt f" using adds_term_alt splus_assoc
      by (auto simp: term_simps)
    from \<open>red_single p p0 f t\<close> have "lookup p (t \<oplus> lt f) \<noteq> 0" unfolding red_single_def by simp
    thus "lookup p (?s \<oplus> lt g) \<noteq> 0" by (simp add: eq)
  qed (fact, fact refl)
  thus ?thesis ..
qed

lemma red_nonzero:
  assumes "red F p q"
  shows "p \<noteq> 0"
proof -
  from red_setE[OF assms] obtain f t where "red_single p q f t" .
  show ?thesis by (rule red_single_nonzero1, fact)
qed

lemma red_self:
  assumes "p \<noteq> 0"
  shows "red {p} p 0"
unfolding red_singleton
proof
  from red_single_self[OF assms] show "red_single p 0 p 0" .
qed

lemma red_ord:
  assumes "red F p q"
  shows "q \<prec>\<^sub>p p"
proof -
  from red_setE[OF assms] obtain f and t where "red_single p q f t" .
  from red_single_ord[OF this] show "q \<prec>\<^sub>p p" .
qed

lemma red_indI1:
  assumes "f \<in> F" and "f \<noteq> 0" and "p \<noteq> 0" and adds: "lt f adds\<^sub>t lt p"
  shows "red F p (p - monom_mult (lc p / lc f) (lp p - lp f) f)"
proof (intro red_setI[OF \<open>f \<in> F\<close>])
  let ?s = "lp p - lp f"
  have c: "lookup p (?s \<oplus> lt f) = lc p" unfolding lc_def
    by (metis add_diff_cancel_right' adds adds_termE pp_of_term_splus)
  show "red_single p (p - monom_mult (lc p / lc f) ?s f) f ?s" unfolding red_single_def
  proof (intro conjI, fact)
    from c lc_not_0[OF \<open>p \<noteq> 0\<close>] show "lookup p (?s \<oplus> lt f) \<noteq> 0" by simp
  next
    from c show "p - monom_mult (lc p / lc f) ?s f = p - monom_mult (lookup p (?s \<oplus> lt f) / lc f) ?s f"
      by simp
  qed
qed

lemma red_indI2:
  assumes "p \<noteq> 0" and r: "red F (tail p) q"
  shows "red F p (q + monomial (lc p) (lt p))"
proof -
  from red_setE[OF r] obtain f t where "f \<in> F" and rs: "red_single (tail p) q f t" by auto
  from rs have "f \<noteq> 0" and ct: "lookup (tail p) (t \<oplus> lt f) \<noteq> 0"
    and q: "q = tail p - monom_mult (lookup (tail p) (t \<oplus> lt f) / lc f) t f"
    unfolding red_single_def by simp_all
  from ct lookup_tail[of p "t \<oplus> lt f"] have "t \<oplus> lt f \<prec>\<^sub>t lt p" by (auto split: if_splits)
  hence c: "lookup (tail p) (t \<oplus> lt f) = lookup p (t \<oplus> lt f)" using lookup_tail[of p] by simp
  show ?thesis
  proof (intro red_setI[OF \<open>f \<in> F\<close>])
    show "red_single p (q + Poly_Mapping.single (lt p) (lc p)) f t" unfolding red_single_def
    proof (intro conjI, fact)
      from ct c show "lookup p (t \<oplus> lt f) \<noteq> 0" by simp
    next
      from q have "q + monomial (lc p) (lt p) =
                  (monomial (lc p) (lt p) + tail p) - monom_mult (lookup (tail p) (t \<oplus> lt f) / lc f) t f"
        by simp
      also have "\<dots> = p - monom_mult (lookup (tail p) (t \<oplus> lt f) / lc f) t f"
        using leading_monomial_tail[of p] by auto
      finally show "q + monomial (lc p) (lt p) = p - monom_mult (lookup p (t \<oplus> lt f) / lc f) t f"
        by (simp only: c)
    qed
  qed
qed

lemma red_indE:
  assumes "red F p q"
  shows "(\<exists>f\<in>F. f \<noteq> 0 \<and> lt f adds\<^sub>t lt p \<and>
            (q = p - monom_mult (lc p / lc f) (lp p - lp f) f)) \<or>
            red F (tail p) (q - monomial (lc p) (lt p))"
proof -
  from red_nonzero[OF assms] have "p \<noteq> 0" .
  from red_setE[OF assms] obtain f t where "f \<in> F" and rs: "red_single p q f t" by auto
  from rs have "f \<noteq> 0"
    and cn0: "lookup p (t \<oplus> lt f) \<noteq> 0"
    and q: "q = p - monom_mult ((lookup p (t \<oplus> lt f)) / lc f) t f"
    unfolding red_single_def by simp_all
  show ?thesis
  proof (cases "lt p = t \<oplus> lt f")
    case True
    hence "lt f adds\<^sub>t lt p" by (simp add: term_simps)
    from True have eq1: "lp p - lp f = t" by (simp add: term_simps)
    from True have eq2: "lc p = lookup p (t \<oplus> lt f)" unfolding lc_def by simp
    show ?thesis
    proof (intro disjI1, rule bexI[of _ f], intro conjI, fact+)
      from q eq1 eq2 show "q = p - monom_mult (lc p / lc f) (lp p - lp f) f"
        by simp
    qed (fact)
  next
    case False
    from this lookup_tail_2[of p "t \<oplus> lt f"]
      have ct: "lookup (tail p) (t \<oplus> lt f) = lookup p (t \<oplus> lt f)" by simp
    show ?thesis
    proof (intro disjI2, intro red_setI[of f], fact)
      show "red_single (tail p) (q - monomial (lc p) (lt p)) f t" unfolding red_single_def
      proof (intro conjI, fact)
        from cn0 ct show "lookup (tail p) (t \<oplus> lt f) \<noteq> 0" by simp
      next
        from leading_monomial_tail[of p]
          have "p - monomial (lc p) (lt p) = (monomial (lc p) (lt p) + tail p) - monomial (lc p) (lt p)"
          by simp
        also have "\<dots> = tail p" by simp
        finally have eq: "p - monomial (lc p) (lt p) = tail p" .
        from q have "q - monomial (lc p) (lt p) =
                    (p - monomial (lc p) (lt p)) - monom_mult ((lookup p (t \<oplus> lt f)) / lc f) t f" by simp
        also from eq have "\<dots> = tail p - monom_mult ((lookup p (t \<oplus> lt f)) / lc f) t f" by simp
        finally show "q - monomial (lc p) (lt p) = tail p - monom_mult (lookup (tail p) (t \<oplus> lt f) / lc f) t f"
          using ct by simp
      qed
    qed
  qed
qed

lemma is_redI:
  assumes "red F a b"
  shows "is_red F a"
  unfolding is_red_def relation.is_final_def by (simp, intro exI[of _ b], fact)

lemma is_redE:
  assumes "is_red F a"
  obtains b where "red F a b"
  using assms unfolding is_red_def relation.is_final_def
proof simp
  assume r: "\<And>b. red F a b \<Longrightarrow> thesis" and b: "\<exists>x. red F a x"
  from b obtain b where "red F a b" ..
  show thesis by (rule r[of b], fact)
qed

lemma is_red_alt:
  shows "is_red F a \<longleftrightarrow> (\<exists>b. red F a b)"
proof
  assume "is_red F a"
  from is_redE[OF this] obtain b where "red F a b" .
  show "\<exists>b. red F a b" by (intro exI[of _ b], fact)
next
  assume "\<exists>b. red F a b"
  from this obtain b where "red F a b" ..
  show "is_red F a" by (rule is_redI, fact)
qed

lemma is_red_singletonI:
  assumes "is_red F q"
  obtains p where "p \<in> F" and "is_red {p} q"
proof -
  from assms obtain q0 where "red F q q0" unfolding is_red_alt ..
  from this red_def[of F q q0] obtain p where "p \<in> F" and t: "\<exists>t. red_single q q0 p t" by auto
  have "is_red {p} q" unfolding is_red_alt
  proof
    from red_singleton[of p q q0] t show "red {p} q q0" by simp
  qed
  from \<open>p \<in> F\<close> this show ?thesis ..
qed

lemma is_red_singletonD:
  assumes "is_red {p} q" and "p \<in> F"
  shows "is_red F q"
proof -
  from assms(1) obtain q0 where "red {p} q q0" unfolding is_red_alt ..
  from red_singleton[of p q q0] this have "\<exists>t. red_single q q0 p t" ..
  from this obtain t where "red_single q q0 p t" ..
  show ?thesis unfolding is_red_alt
    by (intro exI[of _ q0], intro red_setI[OF assms(2), of q q0 t], fact)
qed

lemma is_red_singleton_trans:
  assumes "is_red {f} p" and "lt g adds\<^sub>t lt f" and "g \<noteq> 0"
  shows "is_red {g} p"
proof -
  from \<open>is_red {f} p\<close> obtain q where "red {f} p q" unfolding is_red_alt ..
  from this red_singleton[of f p q] obtain t where "red_single p q f t" by auto
  from red_single_trans[OF this assms(2, 3)] obtain q0 where
    "red_single p q0 g (t + (lp f - lp g))" .
  show ?thesis
  proof (rule is_redI[of "{g}" p q0])
    show "red {g} p q0" unfolding red_def
      by (intro bexI[of _ g], intro exI[of _ "t + (lp f - lp g)"], fact, simp)
  qed
qed

lemma is_red_singleton_not_0:
  assumes "is_red {f} p"
  shows "f \<noteq> 0"
using assms unfolding is_red_alt
proof
  fix q
  assume "red {f} p q"
  from this red_singleton[of f p q] obtain t where "red_single p q f t" by auto
  thus ?thesis unfolding red_single_def ..
qed

lemma irred_0:
  shows "\<not> is_red F 0"
proof (rule, rule is_redE)
  fix b
  assume "red F 0 b"
  from ord_p_zero_min[of b] red_ord[OF this] show False by simp
qed

lemma is_red_indI1:
  assumes "f \<in> F" and "f \<noteq> 0" and "p \<noteq> 0" and "lt f adds\<^sub>t lt p"
  shows "is_red F p"
by (intro is_redI, rule red_indI1[OF assms])

lemma is_red_indI2:
  assumes "p \<noteq> 0" and "is_red F (tail p)"
  shows "is_red F p"
proof -
  from is_redE[OF \<open>is_red F (tail p)\<close>] obtain q where "red F (tail p) q" .
  show ?thesis by (intro is_redI, rule red_indI2[OF \<open>p \<noteq> 0\<close>], fact)
qed

lemma is_red_indE:
  assumes "is_red F p"
  shows "(\<exists>f\<in>F. f \<noteq> 0 \<and> lt f adds\<^sub>t lt p) \<or> is_red F (tail p)"
proof -
  from is_redE[OF assms] obtain q where "red F p q" .
  from red_indE[OF this] show ?thesis
  proof
    assume "\<exists>f\<in>F. f \<noteq> 0 \<and> lt f adds\<^sub>t lt p \<and> q = p - monom_mult (lc p / lc f) (lp p - lp f) f"
    from this obtain f where "f \<in> F" and "f \<noteq> 0" and "lt f adds\<^sub>t lt p" by auto
    show ?thesis by (intro disjI1, rule bexI[of _ f], intro conjI, fact+)
  next
    assume "red F (tail p) (q - monomial (lc p) (lt p))"
    show ?thesis by (intro disjI2, intro is_redI, fact)
  qed
qed

lemma rtrancl_0:
  assumes "(red F)\<^sup>*\<^sup>* 0 x"
  shows "x = 0"
proof -
  from irred_0[of F] have "relation.is_final (red F) 0" unfolding is_red_def by simp
  from relation.rtrancl_is_final[OF \<open>(red F)\<^sup>*\<^sup>* 0 x\<close> this] show ?thesis by simp
qed

lemma red_rtrancl_ord:
  assumes "(red F)\<^sup>*\<^sup>* p q"
  shows "q \<preceq>\<^sub>p p"
  using assms
proof induct
  case base
  show ?case ..
next
  case (step y z)
  from step(2) have "z \<prec>\<^sub>p y" by (rule red_ord)
  hence "z \<preceq>\<^sub>p y" by simp
  also note step(3)
  finally show ?case .
qed

lemma components_red_subset:
  assumes "red F p q"
  shows "component_of_term ` keys q \<subseteq> component_of_term ` keys p \<union> component_of_term ` Keys F"
proof -
  from assms obtain f t where "f \<in> F" and "red_single p q f t" by (rule red_setE)
  from this(2) have q: "q = p - monom_mult ((lookup p (t \<oplus> lt f)) / lc f) t f"
    by (simp add: red_single_def)
  have "component_of_term ` keys q \<subseteq>
        component_of_term ` (keys p \<union> keys (monom_mult ((lookup p (t \<oplus> lt f)) / lc f) t f))"
    by (rule image_mono, simp add: q keys_minus)
  also have "... \<subseteq> component_of_term ` keys p \<union> component_of_term ` Keys F"
  proof (simp add: image_Un, rule)
    fix k
    assume "k \<in> component_of_term ` keys (monom_mult (lookup p (t \<oplus> lt f) / lc f) t f)"
    then obtain v where "v \<in> keys (monom_mult (lookup p (t \<oplus> lt f) / lc f) t f)"
      and "k = component_of_term v" ..
    from this(1) keys_monom_mult_subset have "v \<in> (\<oplus>) t ` keys f" ..
    then obtain u where "u \<in> keys f" and "v = t \<oplus> u" ..
    have "k = component_of_term u" by (simp add: \<open>k = component_of_term v\<close> \<open>v = t \<oplus> u\<close> term_simps)
    with \<open>u \<in> keys f\<close> have "k \<in> component_of_term ` keys f" by fastforce
    also have "... \<subseteq> component_of_term ` Keys F" by (rule image_mono, rule keys_subset_Keys, fact)
    finally show "k \<in> component_of_term ` keys p \<union> component_of_term ` Keys F" by simp
  qed
  finally show ?thesis .
qed

corollary components_red_rtrancl_subset:
  assumes "(red F)\<^sup>*\<^sup>* p q"
  shows "component_of_term ` keys q \<subseteq> component_of_term ` keys p \<union> component_of_term ` Keys F"
  using assms
proof (induct)
  case base
  show ?case by simp
next
  case (step q r)
  from step(2) have "component_of_term ` keys r \<subseteq> component_of_term ` keys q \<union> component_of_term ` Keys F"
    by (rule components_red_subset)
  also from step(3) have "... \<subseteq> component_of_term ` keys p \<union> component_of_term ` Keys F" by blast
  finally show ?case .
qed

subsection \<open>Reducibility and Addition \& Multiplication\<close>

lemma red_single_monom_mult:
  assumes "red_single p q f t" and "c \<noteq> 0"
  shows "red_single (monom_mult c s p) (monom_mult c s q) f (s + t)"
proof -
  from assms(1) have "f \<noteq> 0"
    and "lookup p (t \<oplus> lt f) \<noteq> 0"
    and q_def: "q = p - monom_mult ((lookup p (t \<oplus> lt f)) / lc f) t f"
    unfolding red_single_def by auto
  have assoc: "(s + t) \<oplus> lt f = s \<oplus> (t \<oplus> lt f)" by (simp add: ac_simps)
  have g2: "lookup (monom_mult c s p) ((s + t) \<oplus> lt f) \<noteq> 0"
  proof
    assume "lookup (monom_mult c s p) ((s + t) \<oplus> lt f) = 0"
    hence "c * lookup p (t \<oplus> lt f) = 0" using assoc by (simp add: lookup_monom_mult_plus)
    thus False using \<open>c \<noteq> 0\<close> \<open>lookup p (t \<oplus> lt f) \<noteq> 0\<close> by simp
  qed
  have g3: "monom_mult c s q =
    (monom_mult c s p) - monom_mult ((lookup (monom_mult c s p) ((s + t) \<oplus> lt f)) / lc f) (s + t) f"
  proof -
    from q_def monom_mult_dist_right_minus[of c s p]
      have "monom_mult c s q =
            monom_mult c s p - monom_mult c s (monom_mult (lookup p (t \<oplus> lt f) / lc f) t f)" by simp
    also from monom_mult_assoc[of c s "lookup p (t \<oplus> lt f) / lc f" t f] assoc
      have "monom_mult c s (monom_mult (lookup p (t \<oplus> lt f) / lc f) t f) =
            monom_mult ((lookup (monom_mult c s p) ((s + t) \<oplus> lt f)) / lc f) (s + t) f"
        by (simp add: lookup_monom_mult_plus)
    finally show ?thesis .
  qed
  from \<open>f \<noteq> 0\<close> g2 g3 show ?thesis unfolding red_single_def by auto
qed

lemma red_single_plus_1:
  assumes "red_single p q f t" and "t \<oplus> lt f \<notin> keys (p + r)"
  shows "red_single (q + r) (p + r) f t"
proof -
  from assms have "f \<noteq> 0" and "lookup p (t \<oplus> lt f) \<noteq> 0"
    and q: "q = p - monom_mult ((lookup p (t \<oplus> lt f)) / lc f) t f"
    by (simp_all add: red_single_def)
  from assms(1) have cq_0: "lookup q (t \<oplus> lt f) = 0" by (rule red_single_lookup)
  from assms(2) have "lookup (p + r) (t \<oplus> lt f) = 0"
    by (simp add: in_keys_iff)
  with neg_eq_iff_add_eq_0[of "lookup p (t \<oplus> lt f)" "lookup r (t \<oplus> lt f)"]
    have cr: "lookup r (t \<oplus> lt f) = - (lookup p (t \<oplus> lt f))" by (simp add: lookup_add)
  hence cr_not_0: "lookup r (t \<oplus> lt f) \<noteq> 0" using \<open>lookup p (t \<oplus> lt f) \<noteq> 0\<close> by simp
  from \<open>f \<noteq> 0\<close> show ?thesis unfolding red_single_def
  proof (intro conjI)
    from cr_not_0 show "lookup (q + r) (t \<oplus> lt f) \<noteq> 0" by (simp add: lookup_add cq_0)
  next
    from lc_not_0[OF \<open>f \<noteq> 0\<close>]
      have "monom_mult ((lookup (q + r) (t \<oplus> lt f)) / lc f) t f =
                  monom_mult ((lookup r (t \<oplus> lt f)) / lc f) t f"
        by (simp add: field_simps lookup_add cq_0)
    thus "p + r = q + r - monom_mult (lookup (q + r) (t \<oplus> lt f) / lc f) t f"
      by (simp add: cr q monom_mult_uminus_left)
  qed
qed

lemma red_single_plus_2:
  assumes "red_single p q f t" and "t \<oplus> lt f \<notin> keys (q + r)"
  shows "red_single (p + r) (q + r) f t"
proof -
  from assms have "f \<noteq> 0" and cp: "lookup p (t \<oplus> lt f) \<noteq> 0"
    and q: "q = p - monom_mult ((lookup p (t \<oplus> lt f)) / lc f) t f"
    by (simp_all add: red_single_def)
  from assms(1) have cq_0: "lookup q (t \<oplus> lt f) = 0" by (rule red_single_lookup)
  with assms(2) have cr_0: "lookup r (t \<oplus> lt f) = 0"
    by (simp add: lookup_add in_keys_iff)
  from \<open>f \<noteq> 0\<close> show ?thesis unfolding red_single_def
  proof (intro conjI)
    from cp show "lookup (p + r) (t \<oplus> lt f) \<noteq> 0" by (simp add: lookup_add cr_0)
  next
    show "q + r = p + r - monom_mult (lookup (p + r) (t \<oplus> lt f) / lc f) t f"
      by (simp add: cr_0 q lookup_add)
  qed
qed

lemma red_single_plus_3:
  assumes "red_single p q f t" and "t \<oplus> lt f \<in> keys (p + r)" and "t \<oplus> lt f \<in> keys (q + r)"
  shows "\<exists>s. red_single (p + r) s f t \<and> red_single (q + r) s f t"
proof -
  let ?t = "t \<oplus> lt f"
  from assms have "f \<noteq> 0" and "lookup p ?t \<noteq> 0"
    and q: "q = p - monom_mult ((lookup p ?t) / lc f) t f"
    by (simp_all add: red_single_def)
  from assms(2) have cpr: "lookup (p + r) ?t \<noteq> 0" by (simp add: in_keys_iff)
  from assms(3) have cqr: "lookup (q + r) ?t \<noteq> 0" by (simp add: in_keys_iff)
  from assms(1) have cq_0: "lookup q ?t = 0" by (rule red_single_lookup)
  let ?s = "(p + r) - monom_mult ((lookup (p + r) ?t) / lc f) t f"
  from \<open>f \<noteq> 0\<close> cpr have "red_single (p + r) ?s f t" by (simp add: red_single_def)
  moreover from \<open>f \<noteq> 0\<close> have "red_single (q + r) ?s f t" unfolding red_single_def
  proof (intro conjI)
    from cqr show "lookup (q + r) ?t \<noteq> 0" .
  next
    from lc_not_0[OF \<open>f \<noteq> 0\<close>]
      monom_mult_dist_left[of "(lookup p ?t) / lc f" "(lookup r ?t) / lc f" t f]
      have "monom_mult ((lookup (p + r) ?t) / lc f) t f =
                (monom_mult ((lookup p ?t) / lc f) t f) +
                  (monom_mult ((lookup r ?t) / lc f) t f)"
        by (simp add: field_simps lookup_add)
    moreover from lc_not_0[OF \<open>f \<noteq> 0\<close>]
      monom_mult_dist_left[of "(lookup q ?t) / lc f" "(lookup r ?t) / lc f" t f]
      have "monom_mult ((lookup (q + r) ?t) / lc f) t f =
                monom_mult ((lookup r ?t) / lc f) t f"
        by (simp add: field_simps lookup_add cq_0)
    ultimately show "p + r - monom_mult (lookup (p + r) ?t / lc f) t f =
                     q + r - monom_mult (lookup (q + r) ?t / lc f) t f" by (simp add: q)
  qed
  ultimately show ?thesis by auto
qed

lemma red_single_plus:
  assumes "red_single p q f t"
  shows "red_single (p + r) (q + r) f t \<or>
          red_single (q + r) (p + r) f t \<or>
          (\<exists>s. red_single (p + r) s f t \<and> red_single (q + r) s f t)" (is "?A \<or> ?B \<or> ?C")
proof (cases "t \<oplus> lt f \<in> keys (p + r)")
  case True
  show ?thesis
  proof (cases "t \<oplus> lt f \<in> keys (q + r)")
    case True
    with assms \<open>t \<oplus> lt f \<in> keys (p + r)\<close> have ?C by (rule red_single_plus_3)
    thus ?thesis by simp
  next
    case False
    with assms have ?A by (rule red_single_plus_2)
    thus ?thesis ..
  qed
next
  case False
  with assms have ?B by (rule red_single_plus_1)
  thus ?thesis by simp
qed

lemma red_single_diff:
  assumes "red_single (p - q) r f t"
  shows "red_single p (r + q) f t \<or> red_single q (p - r) f t \<or>
          (\<exists>p' q'. red_single p p' f t \<and> red_single q q' f t \<and> r = p' - q')" (is "?A \<or> ?B \<or> ?C")
proof -
  let ?s = "t \<oplus> lt f"
  from assms have "f \<noteq> 0"
    and "lookup (p - q) ?s \<noteq> 0"
    and r: "r = p - q - monom_mult ((lookup (p - q) ?s) / lc f) t f"
    unfolding red_single_def by auto
  from this(2) have diff: "lookup p ?s \<noteq> lookup q ?s" by (simp add: lookup_minus)
  show ?thesis
  proof (cases "lookup p ?s = 0")
    case True
    with diff have "?s \<in> keys q" by (simp add: in_keys_iff)
    moreover have "lookup (p - q) ?s = - lookup q ?s" by (simp add: lookup_minus True)
    ultimately have ?B using \<open>f \<noteq> 0\<close> by (simp add: in_keys_iff red_single_def r monom_mult_uminus_left)
    thus ?thesis by simp
  next
    case False
    hence "?s \<in> keys p" by (simp add: in_keys_iff)
    show ?thesis
    proof (cases "lookup q ?s = 0")
      case True
      hence "lookup (p - q) ?s = lookup p ?s" by (simp add: lookup_minus)
      hence ?A using \<open>f \<noteq> 0\<close> \<open>?s \<in> keys p\<close> by (simp add: in_keys_iff red_single_def r monom_mult_uminus_left)
      thus ?thesis ..
    next
      case False
      hence "?s \<in> keys q" by (simp add: in_keys_iff)
      let ?p = "p - monom_mult ((lookup p ?s) / lc f) t f"
      let ?q = "q - monom_mult ((lookup q ?s) / lc f) t f"
      have ?C
      proof (intro exI conjI)
        from \<open>f \<noteq> 0\<close> \<open>?s \<in> keys p\<close> show "red_single p ?p f t" by (simp add: in_keys_iff red_single_def)
      next
        from \<open>f \<noteq> 0\<close> \<open>?s \<in> keys q\<close> show "red_single q ?q f t" by (simp add: in_keys_iff red_single_def)
      next
        from \<open>f \<noteq> 0\<close> have "lc f \<noteq> 0" by (rule lc_not_0)
        hence eq: "(lookup p ?s - lookup q ?s) / lc f =
                   lookup p ?s / lc f - lookup q ?s / lc f" by (simp add: field_simps)
        show "r = ?p - ?q" by (simp add: r lookup_minus eq monom_mult_dist_left_minus)
      qed
      thus ?thesis by simp
    qed
  qed
qed

lemma red_monom_mult:
  assumes a: "red F p q" and "c \<noteq> 0"
  shows "red F (monom_mult c s p) (monom_mult c s q)"
proof -
  from red_setE[OF a] obtain f and t where "f \<in> F" and rs: "red_single p q f t" by auto
  from red_single_monom_mult[OF rs \<open>c \<noteq> 0\<close>, of s] show ?thesis by (intro red_setI[OF \<open>f \<in> F\<close>])
qed

lemma red_plus_keys_disjoint:
  assumes "red F p q" and "keys p \<inter> keys r = {}"
  shows "red F (p + r) (q + r)"
proof -
  from assms(1) obtain f t where "f \<in> F" and *: "red_single p q f t" by (rule red_setE)
  from this(2) have "red_single (p + r) (q + r) f t"
  proof (rule red_single_plus_2)
    from * have "lookup q (t \<oplus> lt f) = 0"
      by (simp add: red_single_def lookup_minus lookup_monom_mult lc_def[symmetric] lc_not_0 term_simps)
    hence "t \<oplus> lt f \<notin> keys q" by (simp add: in_keys_iff)
    moreover have "t \<oplus> lt f \<notin> keys r"
    proof
      assume "t \<oplus> lt f \<in> keys r"
      moreover from * have "t \<oplus> lt f \<in> keys p" by (simp add: in_keys_iff red_single_def)
      ultimately have "t \<oplus> lt f \<in> keys p \<inter> keys r" by simp
      with assms(2) show False by simp
    qed
    ultimately have "t \<oplus> lt f \<notin> keys q \<union> keys r" by simp
    thus "t \<oplus> lt f \<notin> keys (q + r)"
      by (meson Poly_Mapping.keys_add subsetD)
  qed
  with \<open>f \<in> F\<close> show ?thesis by (rule red_setI)
qed

lemma red_plus:
  assumes "red F p q"
  obtains s where "(red F)\<^sup>*\<^sup>* (p + r) s" and "(red F)\<^sup>*\<^sup>* (q + r) s"
proof -
  from red_setE[OF assms] obtain f and t where "f \<in> F" and rs: "red_single p q f t" by auto
  from red_single_plus[OF rs, of r] show ?thesis
  proof
    assume c1: "red_single (p + r) (q + r) f t"
    show ?thesis
    proof
      from c1 show "(red F)\<^sup>*\<^sup>* (p + r) (q + r)" by (intro r_into_rtranclp, intro red_setI[OF \<open>f \<in> F\<close>])
    next
      show "(red F)\<^sup>*\<^sup>* (q + r) (q + r)" ..
    qed
  next
    assume "red_single (q + r) (p + r) f t \<or> (\<exists>s. red_single (p + r) s f t \<and> red_single (q + r) s f t)"
    thus ?thesis
    proof
      assume c2: "red_single (q + r) (p + r) f t"
      show ?thesis
      proof
        show "(red F)\<^sup>*\<^sup>* (p + r) (p + r)" ..
      next
        from c2 show "(red F)\<^sup>*\<^sup>* (q + r) (p + r)" by (intro r_into_rtranclp, intro red_setI[OF \<open>f \<in> F\<close>])
      qed
    next
      assume "\<exists>s. red_single (p + r) s f t \<and> red_single (q + r) s f t"
      then obtain s where s1: "red_single (p + r) s f t" and s2: "red_single (q + r) s f t" by auto
      show ?thesis
      proof
        from s1 show "(red F)\<^sup>*\<^sup>* (p + r) s" by (intro r_into_rtranclp, intro red_setI[OF \<open>f \<in> F\<close>])
      next
        from s2 show "(red F)\<^sup>*\<^sup>* (q + r) s" by (intro r_into_rtranclp, intro red_setI[OF \<open>f \<in> F\<close>])
      qed
    qed
  qed
qed

corollary red_plus_cs:
  assumes "red F p q"
  shows "relation.cs (red F) (p + r) (q + r)"
  unfolding relation.cs_def
proof -
  from assms obtain s where "(red F)\<^sup>*\<^sup>* (p + r) s" and "(red F)\<^sup>*\<^sup>* (q + r) s" by (rule red_plus)
  show "\<exists>s. (red F)\<^sup>*\<^sup>* (p + r) s \<and> (red F)\<^sup>*\<^sup>* (q + r) s" by (intro exI, intro conjI, fact, fact)
qed

lemma red_uminus:
  assumes "red F p q"
  shows "red F (-p) (-q)"
  using red_monom_mult[OF assms, of "-1" 0] by (simp add: uminus_monom_mult)

lemma red_diff:
  assumes "red F (p - q) r"
  obtains p' q' where "(red F)\<^sup>*\<^sup>* p p'" and "(red F)\<^sup>*\<^sup>* q q'" and "r = p' - q'"
proof -
  from assms obtain f t where "f \<in> F" and "red_single (p - q) r f t" by (rule red_setE)
  from red_single_diff[OF this(2)] show ?thesis
  proof (elim disjE)
    assume "red_single p (r + q) f t"
    with \<open>f \<in> F\<close> have *: "red F p (r + q)" by (rule red_setI)
    show ?thesis
    proof
      from * show "(red F)\<^sup>*\<^sup>* p (r + q)" ..
    next
      show "(red F)\<^sup>*\<^sup>* q q" ..
    qed simp
  next
    assume "red_single q (p - r) f t"
    with \<open>f \<in> F\<close> have *: "red F q (p - r)" by (rule red_setI)
    show ?thesis
    proof
      show "(red F)\<^sup>*\<^sup>* p p" ..
    next
      from * show "(red F)\<^sup>*\<^sup>* q (p - r)" ..
    qed simp
  next
    assume "\<exists>p' q'. red_single p p' f t \<and> red_single q q' f t \<and> r = p' - q'"
    then obtain p' q' where 1: "red_single p p' f t" and 2: "red_single q q' f t" and "r = p' - q'"
      by blast
    from \<open>f \<in> F\<close> 2 have "red F q q'" by (rule red_setI)
    from \<open>f \<in> F\<close> 1 have "red F p p'" by (rule red_setI)
    hence "(red F)\<^sup>*\<^sup>* p p'" ..
    moreover from \<open>red F q q'\<close> have "(red F)\<^sup>*\<^sup>* q q'" ..
    moreover note \<open>r = p' - q'\<close>
    ultimately show ?thesis ..
  qed
qed

lemma red_diff_rtrancl':
  assumes "(red F)\<^sup>*\<^sup>* (p - q) r"
  obtains p' q' where "(red F)\<^sup>*\<^sup>* p p'" and "(red F)\<^sup>*\<^sup>* q q'" and "r = p' - q'"
  using assms
proof (induct arbitrary: thesis rule: rtranclp_induct)
  case base
  show ?case by (rule base, fact rtrancl_refl[to_pred], fact rtrancl_refl[to_pred], fact refl)
next
  case (step y z)
  obtain p1 q1 where p1: "(red F)\<^sup>*\<^sup>* p p1" and q1: "(red F)\<^sup>*\<^sup>* q q1" and y: "y = p1 - q1" by (rule step(3))
  from step(2) obtain p' q' where p': "(red F)\<^sup>*\<^sup>* p1 p'" and q': "(red F)\<^sup>*\<^sup>* q1 q'" and z: "z = p' - q'"
    unfolding y by (rule red_diff)
  show ?case
  proof (rule step(4))
    from p1 p' show "(red F)\<^sup>*\<^sup>* p p'" by simp
  next
    from q1 q' show "(red F)\<^sup>*\<^sup>* q q'" by simp
  qed fact
qed

lemma red_diff_rtrancl:
  assumes "(red F)\<^sup>*\<^sup>* (p - q) 0"
  obtains s where "(red F)\<^sup>*\<^sup>* p s" and "(red F)\<^sup>*\<^sup>* q s"
proof -
  from assms obtain p' q' where p': "(red F)\<^sup>*\<^sup>* p p'" and q': "(red F)\<^sup>*\<^sup>* q q'" and "0 = p' - q'"
    by (rule red_diff_rtrancl')
  from this(3) have "q' = p'" by simp
  from p' q' show ?thesis unfolding \<open>q' = p'\<close> ..
qed

corollary red_diff_rtrancl_cs:
  assumes "(red F)\<^sup>*\<^sup>* (p - q) 0"
  shows "relation.cs (red F) p q"
  unfolding relation.cs_def
proof -
  from assms obtain s where "(red F)\<^sup>*\<^sup>* p s" and "(red F)\<^sup>*\<^sup>* q s" by (rule red_diff_rtrancl)
  show "\<exists>s. (red F)\<^sup>*\<^sup>* p s \<and> (red F)\<^sup>*\<^sup>* q s" by (intro exI, intro conjI, fact, fact)
qed

subsection \<open>Confluence of Reducibility\<close>

lemma confluent_distinct_aux:
  assumes r1: "red_single p q1 f1 t1" and r2: "red_single p q2 f2 t2"
    and "t1 \<oplus> lt f1 \<prec>\<^sub>t t2 \<oplus> lt f2" and "f1 \<in> F" and "f2 \<in> F"
  obtains s where "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s"
proof -
  from r1 have "f1 \<noteq> 0" and c1: "lookup p (t1 \<oplus> lt f1) \<noteq> 0"
    and q1_def: "q1 = p - monom_mult (lookup p (t1 \<oplus> lt f1) / lc f1) t1 f1"
    unfolding red_single_def by auto
  from r2 have "f2 \<noteq> 0" and c2: "lookup p (t2 \<oplus> lt f2) \<noteq> 0"
    and q2_def: "q2 = p - monom_mult (lookup p (t2 \<oplus> lt f2) / lc f2) t2 f2"
    unfolding red_single_def by auto
  from \<open>t1 \<oplus> lt f1 \<prec>\<^sub>t t2 \<oplus> lt f2\<close>
  have "lookup (monom_mult (lookup p (t1 \<oplus> lt f1) / lc f1) t1 f1) (t2 \<oplus> lt f2) = 0"
    by (simp add: lookup_monom_mult_eq_zero)
  from lookup_minus[of p _ "t2 \<oplus> lt f2"] this have c: "lookup q1 (t2 \<oplus> lt f2) = lookup p (t2 \<oplus> lt f2)"
    unfolding q1_def by simp
  define q3 where "q3 \<equiv> q1 - monom_mult ((lookup q1 (t2 \<oplus> lt f2)) / lc f2) t2 f2"
  have "red_single q1 q3 f2 t2" unfolding red_single_def
  proof (rule, fact, rule)
    from c c2 show "lookup q1 (t2 \<oplus> lt f2) \<noteq> 0" by simp
  next
    show "q3 = q1 - monom_mult (lookup q1 (t2 \<oplus> lt f2) / lc f2) t2 f2" unfolding q3_def ..
  qed
  hence "red F q1 q3" by (intro red_setI[OF \<open>f2 \<in> F\<close>])
  hence q1q3: "(red F)\<^sup>*\<^sup>* q1 q3" by (intro r_into_rtranclp)
  from r1 have "red F p q1" by (intro red_setI[OF \<open>f1 \<in> F\<close>])
  from red_plus[OF this, of "- monom_mult ((lookup p (t2 \<oplus> lt f2)) / lc f2) t2 f2"] obtain s
    where r3: "(red F)\<^sup>*\<^sup>* (p - monom_mult (lookup p (t2 \<oplus> lt f2) / lc f2) t2 f2) s"
    and r4: "(red F)\<^sup>*\<^sup>* (q1 - monom_mult (lookup p (t2 \<oplus> lt f2) / lc f2) t2 f2) s" by auto
  from r3 have q2s: "(red F)\<^sup>*\<^sup>* q2 s" unfolding q2_def by simp
  from r4 c have q3s: "(red F)\<^sup>*\<^sup>* q3 s" unfolding q3_def by simp
  show ?thesis
  proof
    from rtranclp_trans[OF q1q3 q3s] show "(red F)\<^sup>*\<^sup>* q1 s" .
  next
    from q2s show "(red F)\<^sup>*\<^sup>* q2 s" .
  qed
qed

lemma confluent_distinct:
  assumes r1: "red_single p q1 f1 t1" and r2: "red_single p q2 f2 t2"
    and ne: "t1 \<oplus> lt f1 \<noteq> t2 \<oplus> lt f2" and "f1 \<in> F" and "f2 \<in> F"
  obtains s where "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s"
proof -
  from ne have "t1 \<oplus> lt f1 \<prec>\<^sub>t t2 \<oplus> lt f2 \<or> t2 \<oplus> lt f2 \<prec>\<^sub>t t1 \<oplus> lt f1" by auto
  thus ?thesis
  proof
    assume a1: "t1 \<oplus> lt f1 \<prec>\<^sub>t t2 \<oplus> lt f2"
    from confluent_distinct_aux[OF r1 r2 a1 \<open>f1 \<in> F\<close> \<open>f2 \<in> F\<close>] obtain s where
      "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s" .
    thus ?thesis ..
  next
    assume a2: "t2 \<oplus> lt f2 \<prec>\<^sub>t t1 \<oplus> lt f1"
    from confluent_distinct_aux[OF r2 r1 a2 \<open>f2 \<in> F\<close> \<open>f1 \<in> F\<close>] obtain s where
      "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s" .
    thus ?thesis ..
  qed
qed

corollary confluent_same:
  assumes r1: "red_single p q1 f t1" and r2: "red_single p q2 f t2" and "f \<in> F"
  obtains s where "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s"
proof (cases "t1 = t2")
  case True
  with r1 r2 have "q1 = q2" by (simp add: red_single_def)
  show ?thesis
  proof
    show "(red F)\<^sup>*\<^sup>* q1 q2" unfolding \<open>q1 = q2\<close> ..
  next
    show "(red F)\<^sup>*\<^sup>* q2 q2" ..
  qed
next
  case False
  hence "t1 \<oplus> lt f \<noteq> t2 \<oplus> lt f" by (simp add: term_simps)
  from r1 r2 this \<open>f \<in> F\<close> \<open>f \<in> F\<close> obtain s where "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s"
    by (rule confluent_distinct)
  thus ?thesis ..
qed

subsection \<open>Reducibility and Module Membership\<close>

lemma srtc_in_pmdl:
  assumes "relation.srtc (red F) p q"
  shows "p - q \<in> pmdl F"
  using assms unfolding relation.srtc_def
proof (induct rule: rtranclp.induct)
  fix p
  show "p - p \<in> pmdl F" by (simp add: pmdl.span_zero)
next
  fix p r q
  assume pr_in: "p - r \<in> pmdl F" and red: "red F r q \<or> red F q r"
  from red obtain f c t where "f \<in> F" and "q = r - monom_mult c t f"
  proof
    assume "red F r q"
    from red_setE[OF this] obtain f t where "f \<in> F" and "red_single r q f t" .
    hence "q = r - monom_mult (lookup r (t \<oplus> lt f) / lc f) t f" by (simp add: red_single_def)
    show thesis by (rule, fact, fact)
  next
    assume "red F q r"
    from red_setE[OF this] obtain f t where "f \<in> F" and "red_single q r f t" .
    hence "r = q - monom_mult (lookup q (t \<oplus> lt f) / lc f) t f" by (simp add: red_single_def)
    hence "q = r + monom_mult (lookup q (t \<oplus> lt f) / lc f) t f" by simp
    hence "q = r - monom_mult (-(lookup q (t \<oplus> lt f) / lc f)) t f"
      using monom_mult_uminus_left[of _ t f] by simp
    show thesis by (rule, fact, fact)
  qed
  hence eq: "p - q = (p - r) + monom_mult c t f" by simp
  show "p - q \<in> pmdl F" unfolding eq
    by (rule pmdl.span_add, fact, rule monom_mult_in_pmdl, fact)
qed

lemma in_pmdl_srtc:
  assumes "p \<in> pmdl F"
  shows "relation.srtc (red F) p 0"
  using assms
proof (induct p rule: pmdl_induct)
  show "relation.srtc (red F) 0 0" unfolding relation.srtc_def ..
next
  fix a f c t
  assume a_in: "a \<in> pmdl F" and IH: "relation.srtc (red F) a 0" and "f \<in> F"
  show "relation.srtc (red F) (a + monom_mult c t f) 0"
  proof (cases "c = 0")
    assume "c = 0"
    hence "a + monom_mult c t f = a" by simp
    thus ?thesis using IH by simp
  next
    assume "c \<noteq> 0"
    show ?thesis
    proof (cases "f = 0")
      assume "f = 0"
      hence "a + monom_mult c t f = a" by simp
      thus ?thesis using IH by simp
    next
      assume "f \<noteq> 0"
      from lc_not_0[OF this] have "lc f \<noteq> 0" .
      have "red F (monom_mult c t f) 0"
      proof (intro red_setI[OF \<open>f \<in> F\<close>])
        from lookup_monom_mult_plus[of c t f "lt f"]
          have eq: "lookup (monom_mult c t f) (t \<oplus> lt f) = c * lc f" unfolding lc_def .
        show "red_single (monom_mult c t f) 0 f t" unfolding red_single_def eq
        proof (intro conjI, fact)
          from \<open>c \<noteq> 0\<close> \<open>lc f \<noteq> 0\<close> show "c * lc f \<noteq> 0" by simp
        next
          from \<open>lc f \<noteq> 0\<close> show "0 = monom_mult c t f - monom_mult (c * lc f / lc f) t f" by simp
        qed
      qed
      from red_plus[OF this, of a] obtain s where
        s1: "(red F)\<^sup>*\<^sup>* (monom_mult c t f + a) s" and s2: "(red F)\<^sup>*\<^sup>* (0 + a) s" .
      have "relation.cs (red F) (a + monom_mult c t f) a" unfolding relation.cs_def
      proof (intro exI[of _ s], intro conjI)
        from s1 show "(red F)\<^sup>*\<^sup>* (a + monom_mult c t f) s" by (simp only: add.commute)
      next
        from s2 show "(red F)\<^sup>*\<^sup>* a s" by simp
      qed
      from relation.srtc_transitive[OF relation.cs_implies_srtc[OF this] IH] show ?thesis .
    qed
  qed
qed

lemma red_rtranclp_diff_in_pmdl:
  assumes "(red F)\<^sup>*\<^sup>* p q"
  shows "p - q \<in> pmdl F"
proof -
  from assms have "relation.srtc (red F) p q"
    by (simp add: r_into_rtranclp relation.rtc_implies_srtc)
  thus ?thesis by (rule srtc_in_pmdl)
qed

corollary red_diff_in_pmdl:
  assumes "red F p q"
  shows "p - q \<in> pmdl F"
  by (rule red_rtranclp_diff_in_pmdl, rule r_into_rtranclp, fact)
  
corollary red_rtranclp_0_in_pmdl:
  assumes "(red F)\<^sup>*\<^sup>* p 0"
  shows "p \<in> pmdl F"
  using assms red_rtranclp_diff_in_pmdl by fastforce

lemma pmdl_closed_red:
  assumes "pmdl B \<subseteq> pmdl A" and "p \<in> pmdl A" and "red B p q"
  shows "q \<in> pmdl A"
proof -
  have "q - p \<in> pmdl A"
  proof
    have "p - q \<in> pmdl B" by (rule red_diff_in_pmdl, fact)
    hence "- (p - q) \<in> pmdl B" by (rule pmdl.span_neg)
    thus "q - p \<in> pmdl B" by simp
  qed fact
  from pmdl.span_add[OF this \<open>p \<in> pmdl A\<close>] show ?thesis by simp
qed

subsection \<open>More Properties of @{const red}, @{const red_single} and @{const is_red}\<close>

lemma red_rtrancl_mult:
  assumes "(red F)\<^sup>*\<^sup>* p q"
  shows "(red F)\<^sup>*\<^sup>* (monom_mult c t p) (monom_mult c t q)"
proof (cases "c = 0")
  case True
  have "(red F)\<^sup>*\<^sup>* 0 0" by simp
  thus ?thesis by (simp only: True monom_mult_zero_left)
next
  case False
  from assms show ?thesis
  proof (induct rule: rtranclp_induct)
    show "(red F)\<^sup>*\<^sup>* (monom_mult c t p) (monom_mult c t p)" by simp
  next
    fix q0 q
    assume "(red F)\<^sup>*\<^sup>* p q0" and "red F q0 q" and "(red F)\<^sup>*\<^sup>* (monom_mult c t p) (monom_mult c t q0)"
    show "(red F)\<^sup>*\<^sup>* (monom_mult c t p) (monom_mult c t q)"
    proof (rule rtranclp.intros(2)[OF \<open>(red F)\<^sup>*\<^sup>* (monom_mult c t p) (monom_mult c t q0)\<close>])
      from red_monom_mult[OF \<open>red F q0 q\<close> False, of t] show "red F (monom_mult c t q0) (monom_mult c t q)" .
    qed
  qed
qed

corollary red_rtrancl_uminus:
  assumes "(red F)\<^sup>*\<^sup>* p q"
  shows "(red F)\<^sup>*\<^sup>* (-p) (-q)"
  using red_rtrancl_mult[OF assms, of "-1" 0] by (simp add: uminus_monom_mult)

lemma red_rtrancl_diff_induct [consumes 1, case_names base step]:
  assumes a: "(red F)\<^sup>*\<^sup>* (p - q) r"
    and cases: "P p p" "!!y z. [| (red F)\<^sup>*\<^sup>* (p - q) z; red F z y; P p (q + z)|] ==> P p (q + y)"
  shows "P p (q + r)"
  using a
proof (induct rule: rtranclp_induct)
  from cases(1) show "P p (q + (p - q))" by simp
next
  fix y z
  assume "(red F)\<^sup>*\<^sup>* (p - q) z" "red F z y" "P p (q + z)"
  thus "P p (q + y)" using cases(2) by simp
qed

lemma red_rtrancl_diff_0_induct [consumes 1, case_names base step]:
  assumes a: "(red F)\<^sup>*\<^sup>* (p - q) 0"
    and base: "P p p" and ind: "\<And>y z. [| (red F)\<^sup>*\<^sup>* (p - q) y; red F y z; P p (y + q)|] ==> P p (z + q)"
  shows "P p q"
proof -
  from ind red_rtrancl_diff_induct[of F p q 0 P, OF a base] have "P p (0 + q)"
    by (simp add: ac_simps)
  thus ?thesis by simp
qed

lemma is_red_union: "is_red (A \<union> B) p \<longleftrightarrow> (is_red A p \<or> is_red B p)"
  unfolding is_red_alt red_union by auto

lemma red_single_0_lt:
  assumes "red_single f 0 h t"
  shows "lt f = t \<oplus> lt h"
proof -
  from red_single_nonzero1[OF assms] have "f \<noteq> 0" .
  {
    assume "h \<noteq> 0" and neq: "lookup f (t \<oplus> lt h) \<noteq> 0" and
      eq: "f = monom_mult (lookup f (t \<oplus> lt h) / lc h) t h"
    from lc_not_0[OF \<open>h \<noteq> 0\<close>] have "lc h \<noteq> 0" .
    with neq have "(lookup f (t \<oplus> lt h) / lc h) \<noteq> 0" by simp
    from eq lt_monom_mult[OF this \<open>h \<noteq> 0\<close>, of t] have "lt f = t \<oplus> lt h" by simp
    hence "lt f = t \<oplus> lt h" by (simp add: ac_simps)
  }
  with assms show ?thesis unfolding red_single_def by auto
qed

lemma red_single_lt_distinct_lt:
  assumes rs: "red_single f g h t" and "g \<noteq> 0" and "lt g \<noteq> lt f"
  shows "lt f = t \<oplus> lt h"
proof -
  from red_single_nonzero1[OF rs] have "f \<noteq> 0" .
  from red_single_ord[OF rs] have "g \<preceq>\<^sub>p f" by simp
  from ord_p_lt[OF this] \<open>lt g \<noteq> lt f\<close> have "lt g \<prec>\<^sub>t lt f" by simp
  {
    assume "h \<noteq> 0" and neq: "lookup f (t \<oplus> lt h) \<noteq> 0" and
      eq: "f = g + monom_mult (lookup f (t \<oplus> lt h) / lc h) t h" (is "f = g + ?R")
    from lc_not_0[OF \<open>h \<noteq> 0\<close>] have "lc h \<noteq> 0" .
    with neq have "(lookup f (t \<oplus> lt h) / lc h) \<noteq> 0" (is "?c \<noteq> 0") by simp
    from eq lt_monom_mult[OF this \<open>h \<noteq> 0\<close>, of t] have ltR: "lt ?R = t \<oplus> lt h" by simp
    from monom_mult_eq_zero_iff[of ?c t h] \<open>?c \<noteq> 0\<close> \<open>h \<noteq> 0\<close> have "?R \<noteq> 0" by auto
    from lt_plus_lessE[of g] eq \<open>lt g \<prec>\<^sub>t lt f\<close> have "lt g \<prec>\<^sub>t lt ?R" by auto
    from lt_plus_eqI[OF this] eq ltR have "lt f = t \<oplus> lt h" by (simp add: ac_simps)
  }
  with assms show ?thesis unfolding red_single_def by auto
qed

lemma zero_reducibility_implies_lt_divisibility':
  assumes "(red F)\<^sup>*\<^sup>* f 0" and "f \<noteq> 0"
  shows "\<exists>h\<in>F. h \<noteq> 0 \<and> (lt h adds\<^sub>t lt f)"
  using assms
proof (induct rule: converse_rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step f g)
  show ?case
  proof (cases "g = 0")
    case True
    with step.hyps have "red F f 0" by simp
    from red_setE[OF this] obtain h t where "h \<in> F" and rs: "red_single f 0 h t" by auto
    show ?thesis
    proof
      from red_single_0_lt[OF rs] have "lt h adds\<^sub>t lt f" by (simp add: term_simps)
      also from rs have "h \<noteq> 0" by (simp add: red_single_def) 
      ultimately show "h \<noteq> 0 \<and> lt h adds\<^sub>t lt f" by simp
    qed (rule \<open>h \<in> F\<close>)
  next
    case False
    show ?thesis
    proof (cases "lt g = lt f")
      case True
      with False step.hyps show ?thesis by simp
    next
      case False
      from red_setE[OF \<open>red F f g\<close>] obtain h t where "h \<in> F" and rs: "red_single f g h t" by auto
      show ?thesis
      proof
        from red_single_lt_distinct_lt[OF rs \<open>g \<noteq> 0\<close> False] have "lt h adds\<^sub>t lt f"
          by (simp add: term_simps)
        also from rs have "h \<noteq> 0" by (simp add: red_single_def) 
        ultimately show "h \<noteq> 0 \<and> lt h adds\<^sub>t lt f" by simp
      qed (rule \<open>h \<in> F\<close>)
    qed
  qed
qed
  
lemma zero_reducibility_implies_lt_divisibility:
  assumes "(red F)\<^sup>*\<^sup>* f 0" and "f \<noteq> 0"
  obtains h where "h \<in> F" and "h \<noteq> 0" and "lt h adds\<^sub>t lt f"
  using zero_reducibility_implies_lt_divisibility'[OF assms] by auto

lemma is_red_addsI:
  assumes "f \<in> F" and "f \<noteq> 0" and "v \<in> keys p" and "lt f adds\<^sub>t v"
  shows "is_red F p"
  using assms
proof (induction p rule: poly_mapping_tail_induct)
  case 0
  from \<open>v \<in> keys 0\<close> show ?case by auto
next
  case (tail p)
  from "tail.IH"[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> _ \<open>lt f adds\<^sub>t v\<close>] have imp: "v \<in> keys (tail p) \<Longrightarrow> is_red F (tail p)" .
  show ?case
  proof (cases "v = lt p")
    case True
    show ?thesis
    proof (rule is_red_indI1[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> \<open>p \<noteq> 0\<close>])
      from \<open>lt f adds\<^sub>t v\<close> True show "lt f adds\<^sub>t lt p" by simp
    qed
  next
    case False
    with \<open>v \<in> keys p\<close> \<open>p \<noteq> 0\<close> have "v \<in> keys (tail p)"
      by (simp add: lookup_tail_2 in_keys_iff) 
    from is_red_indI2[OF \<open>p \<noteq> 0\<close> imp[OF this]] show ?thesis .
  qed
qed

lemma is_red_addsE':
  assumes "is_red F p"
  shows "\<exists>f\<in>F. \<exists>v\<in>keys p. f \<noteq> 0 \<and> lt f adds\<^sub>t v"
  using assms
proof (induction p rule: poly_mapping_tail_induct)
  case 0
  with irred_0[of F] show ?case by simp
next
  case (tail p)
  from is_red_indE[OF \<open>is_red F p\<close>] show ?case
  proof
    assume "\<exists>f\<in>F. f \<noteq> 0 \<and> lt f adds\<^sub>t lt p"
    then obtain f where "f \<in> F" and "f \<noteq> 0" and "lt f adds\<^sub>t lt p" by auto
    show ?case
    proof
      show "\<exists>v\<in>keys p. f \<noteq> 0 \<and> lt f adds\<^sub>t v"
      proof (intro bexI, intro conjI)
        from \<open>p \<noteq> 0\<close> show "lt p \<in> keys p" by (metis in_keys_iff lc_def lc_not_0)
      qed (rule \<open>f \<noteq> 0\<close>, rule \<open>lt f adds\<^sub>t lt p\<close>)
    qed (rule \<open>f \<in> F\<close>)
  next
    assume "is_red F (tail p)"
    from "tail.IH"[OF this] obtain f v
      where "f \<in> F" and "f \<noteq> 0" and v_in_keys_tail: "v \<in> keys (tail p)" and "lt f adds\<^sub>t v" by auto
    from "tail.hyps" v_in_keys_tail have v_in_keys: "v \<in> keys p" by (metis lookup_tail in_keys_iff)
    show ?case
    proof
      show "\<exists>v\<in>keys p. f \<noteq> 0 \<and> lt f adds\<^sub>t v"
        by (intro bexI, intro conjI, rule \<open>f \<noteq> 0\<close>, rule \<open>lt f adds\<^sub>t v\<close>, rule v_in_keys)
    qed (rule \<open>f \<in> F\<close>)
  qed
qed

lemma is_red_addsE:
  assumes "is_red F p"
  obtains f v where "f \<in> F" and "v \<in> keys p" and "f \<noteq> 0" and "lt f adds\<^sub>t v"
  using is_red_addsE'[OF assms] by auto

lemma is_red_adds_iff:
  shows "(is_red F p) \<longleftrightarrow> (\<exists>f\<in>F. \<exists>v\<in>keys p. f \<noteq> 0 \<and> lt f adds\<^sub>t v)"
  using is_red_addsE' is_red_addsI by auto
    
lemma is_red_subset:
  assumes red: "is_red A p" and sub: "A \<subseteq> B"
  shows "is_red B p"
proof -
  from red obtain f v where "f \<in> A" and "v \<in> keys p" and "f \<noteq> 0" and "lt f adds\<^sub>t v" by (rule is_red_addsE)
  show ?thesis by (rule is_red_addsI, rule, fact+)
qed

lemma not_is_red_empty: "\<not> is_red {} f"
  by (simp add: is_red_adds_iff)

lemma red_single_mult_const:
  assumes "red_single p q f t" and "c \<noteq> 0"
  shows "red_single p q (monom_mult c 0 f) t"
proof -
  let ?s = "t \<oplus> lt f"
  let ?f = "monom_mult c 0 f"
  from assms(1) have "f \<noteq> 0" and "lookup p ?s \<noteq> 0"
    and "q = p - monom_mult ((lookup p ?s) / lc f) t f" by (simp_all add: red_single_def)
  from this(1) assms(2) have lt: "lt ?f = lt f" and lc: "lc ?f = c * lc f"
    by (simp add: lt_monom_mult term_simps, simp)
  show ?thesis unfolding red_single_def
  proof (intro conjI)
    from \<open>f \<noteq> 0\<close> assms(2) show "?f \<noteq> 0" by (simp add: monom_mult_eq_zero_iff)
  next
    from \<open>lookup p ?s \<noteq> 0\<close> show "lookup p (t \<oplus> lt ?f) \<noteq> 0" by (simp add: lt)
  next
    show "q = p - monom_mult (lookup p (t \<oplus> lt ?f) / lc ?f) t ?f"
      by (simp add: lt monom_mult_assoc lc assms(2), fact)
  qed
qed

lemma red_rtrancl_plus_higher:
  assumes "(red F)\<^sup>*\<^sup>* p q" and "\<And>u v. u \<in> keys p \<Longrightarrow> v \<in> keys r \<Longrightarrow> u \<prec>\<^sub>t v"
  shows "(red F)\<^sup>*\<^sup>* (p + r) (q + r)"
  using assms(1)
proof induct
  case base
  show ?case ..
next
  case (step y z)
  from step(1) have "y \<preceq>\<^sub>p p" by (rule red_rtrancl_ord)
  hence "lt y \<preceq>\<^sub>t lt p" by (rule ord_p_lt)
  from step(2) have "red F (y + r) (z + r)"
  proof (rule red_plus_keys_disjoint)
    show "keys y \<inter> keys r = {}"
    proof (rule ccontr)
      assume "keys y \<inter> keys r \<noteq> {}"
      then obtain v where "v \<in> keys y" and "v \<in> keys r" by auto
      from this(1) have "v \<preceq>\<^sub>t lt y" and "y \<noteq> 0" using lt_max by (auto simp: in_keys_iff)
      with \<open>y \<preceq>\<^sub>p p\<close> have "p \<noteq> 0" using ord_p_zero_min[of y] by auto
      hence "lt p \<in> keys p" by (rule lt_in_keys)
      from this \<open>v \<in> keys r\<close> have "lt p \<prec>\<^sub>t v" by (rule assms(2))
      with \<open>lt y \<preceq>\<^sub>t lt p\<close> have "lt y \<prec>\<^sub>t v" by simp
      with \<open>v \<preceq>\<^sub>t lt y\<close>  show False by simp
    qed
  qed
  with step(3) show ?case ..
qed

lemma red_mult_scalar_leading_monomial: "(red {f})\<^sup>*\<^sup>* (p \<odot> monomial (lc f) (lt f)) (- p \<odot> tail f)"
proof (cases "f = 0")
  case True
  show ?thesis by (simp add: True lc_def)
next
  case False
  show ?thesis
  proof (induct p rule: punit.poly_mapping_tail_induct)
    case 0
    show ?case by simp
  next
    case (tail p)
    from False have "lc f \<noteq> 0" by (rule lc_not_0)
    from tail(1) have "punit.lc p \<noteq> 0" by (rule punit.lc_not_0)
    let ?t = "punit.tail p \<odot> monomial (lc f) (lt f)"
    let ?m = "monom_mult (punit.lc p) (punit.lt p) (monomial (lc f) (lt f))"
    from \<open>lc f \<noteq> 0\<close> have kt: "keys ?t = (\<lambda>t. t \<oplus> lt f) ` keys (punit.tail p)"
      by (rule keys_mult_scalar_monomial_right)
    have km: "keys ?m = {punit.lt p \<oplus> lt f}"
      by (simp add: keys_monom_mult[OF \<open>punit.lc p \<noteq> 0\<close>] \<open>lc f \<noteq> 0\<close>)
    from tail(2) have "(red {f})\<^sup>*\<^sup>* (?t + ?m) (- punit.tail p \<odot> tail f + ?m)"
    proof (rule red_rtrancl_plus_higher)
      fix u v
      assume "u \<in> keys ?t" and "v \<in> keys ?m"
      from this(1) obtain s where "s \<in> keys (punit.tail p)" and u: "u = s \<oplus> lt f" unfolding kt ..
      from this(1) have "punit.tail p \<noteq> 0" and "s \<preceq> punit.lt (punit.tail p)" using punit.lt_max by (auto simp: in_keys_iff)
      moreover from \<open>punit.tail p \<noteq> 0\<close> have "punit.lt (punit.tail p) \<prec> punit.lt p" by (rule punit.lt_tail)
      ultimately have "s \<prec> punit.lt p" by simp
      moreover from \<open>v \<in> keys ?m\<close> have "v = punit.lt p \<oplus> lt f" by (simp only: km, simp)
      ultimately show "u \<prec>\<^sub>t v" by (simp add: u splus_mono_strict_left)
    qed
    hence *: "(red {f})\<^sup>*\<^sup>* (p \<odot> monomial (lc f) (lt f)) (?m - punit.tail p \<odot> tail f)"
      by (simp add: punit.leading_monomial_tail[symmetric, of p] mult_scalar_monomial[symmetric]
            mult_scalar_distrib_right[symmetric] add.commute[of "punit.tail p"])
    have "red {f} ?m (- (monomial (punit.lc p) (punit.lt p)) \<odot> tail f)" unfolding red_singleton
    proof
      show "red_single ?m (- (monomial (punit.lc p) (punit.lt p)) \<odot> tail f) f (punit.lt p)"
      proof (simp add: red_single_def \<open>f \<noteq> 0\<close> km lookup_monom_mult \<open>lc f \<noteq> 0\<close> \<open>punit.lc p \<noteq> 0\<close> term_simps,
              simp add: monom_mult_dist_right_minus[symmetric] mult_scalar_monomial)
        have "monom_mult (punit.lc p) (punit.lt p) (monomial (lc f) (lt f) - f) =
              - monom_mult (punit.lc p) (punit.lt p) (f - monomial (lc f) (lt f))"
          by (metis minus_diff_eq monom_mult_uminus_right)
        also have "... = - monom_mult (punit.lc p) (punit.lt p) (tail f)" by (simp only: tail_alt_2)
        finally show "- monom_mult (punit.lc p) (punit.lt p) (tail f) =
                      monom_mult (punit.lc p) (punit.lt p) (monomial (lc f) (lt f) - f)" by simp
      qed
    qed
    hence "red {f} (?m + (- punit.tail p \<odot> tail f))
                    (- (monomial (punit.lc p) (punit.lt p)) \<odot> tail f + (- punit.tail p \<odot> tail f))"
    proof (rule red_plus_keys_disjoint)
      show "keys ?m \<inter> keys (- punit.tail p \<odot> tail f) = {}"
      proof (cases "punit.tail p = 0")
        case True
        show ?thesis by (simp add: True)
      next
        case False
        from tail(2) have "- punit.tail p \<odot> tail f \<preceq>\<^sub>p ?t" by (rule red_rtrancl_ord)
        hence "lt (- punit.tail p \<odot> tail f) \<preceq>\<^sub>t lt ?t" by (rule ord_p_lt)
        also from \<open>lc f \<noteq> 0\<close> False have "... = punit.lt (punit.tail p) \<oplus> lt f"
          by (rule lt_mult_scalar_monomial_right)
        also from punit.lt_tail[OF False] have "... \<prec>\<^sub>t punit.lt p \<oplus> lt f" by (rule splus_mono_strict_left)
        finally have "punit.lt p \<oplus> lt f \<notin> keys (- punit.tail p \<odot> tail f)" using lt_gr_keys by blast
        thus ?thesis by (simp add: km)
      qed
    qed
    hence "red {f} (?m - punit.tail p \<odot> tail f)
            (- (monomial (punit.lc p) (punit.lt p)) \<odot> tail f - punit.tail p \<odot> tail f)"
      by (simp add: term_simps)
    also have "... = - p \<odot> tail f" using punit.leading_monomial_tail[symmetric, of p]
      by (metis (mono_tags, lifting) add_uminus_conv_diff minus_add_distrib mult_scalar_distrib_right
          mult_scalar_minus_mult_left)
    finally have "red {f} (?m - punit.tail p \<odot> tail f) (- p \<odot> tail f)" .
    with * show ?case ..
  qed
qed

corollary red_mult_scalar_lt:
  assumes "f \<noteq> 0"
  shows "(red {f})\<^sup>*\<^sup>* (p \<odot> monomial c (lt f)) (monom_mult (- c / lc f) 0 (p \<odot> tail f))"
proof -
  from assms have "lc f \<noteq> 0" by (rule lc_not_0)
  hence 1: "p \<odot> monomial c (lt f) = punit.monom_mult (c / lc f) 0 p \<odot> monomial (lc f) (lt f)"
    by (simp add: punit.mult_scalar_monomial[symmetric] mult.commute
        mult_scalar_assoc mult_scalar_monomial_monomial term_simps)
  have 2: "monom_mult (- c / lc f) 0 (p \<odot> tail f) = - punit.monom_mult (c / lc f) 0 p \<odot> tail f"
    by (simp add: times_monomial_left[symmetric] mult_scalar_assoc
        monom_mult_uminus_left mult_scalar_monomial)
  show ?thesis unfolding 1 2 by (fact red_mult_scalar_leading_monomial)
qed

lemma is_red_monomial_iff: "is_red F (monomial c v) \<longleftrightarrow> (c \<noteq> 0 \<and> (\<exists>f\<in>F. f \<noteq> 0 \<and> lt f adds\<^sub>t v))"
  by (simp add: is_red_adds_iff)

lemma is_red_monomialI:
  assumes "c \<noteq> 0" and "f \<in> F" and "f \<noteq> 0" and "lt f adds\<^sub>t v"
  shows "is_red F (monomial c v)"
  unfolding is_red_monomial_iff using assms by blast

lemma is_red_monomialD:
  assumes "is_red F (monomial c v)"
  shows "c \<noteq> 0"
  using assms unfolding is_red_monomial_iff ..

lemma is_red_monomialE:
  assumes "is_red F (monomial c v)"
  obtains f where "f \<in> F" and "f \<noteq> 0" and "lt f adds\<^sub>t v"
  using assms unfolding is_red_monomial_iff by blast

lemma replace_lt_adds_stable_is_red:
  assumes red: "is_red F f" and "q \<noteq> 0" and "lt q adds\<^sub>t lt p"
  shows "is_red (insert q (F - {p})) f"
proof -
  from red obtain g v where "g \<in> F" and "g \<noteq> 0" and "v \<in> keys f" and "lt g adds\<^sub>t v"
    by (rule is_red_addsE)
  show ?thesis
  proof (cases "g = p")
    case True
    show ?thesis
    proof (rule is_red_addsI)
      show "q \<in> insert q (F - {p})" by simp
    next
      have "lt q adds\<^sub>t lt p" by fact
      also have "... adds\<^sub>t v" using \<open>lt g adds\<^sub>t v\<close> unfolding True .
      finally show "lt q adds\<^sub>t v" .
    qed (fact+)
  next
    case False
    with \<open>g \<in> F\<close> have "g \<in> insert q (F - {p})" by blast
    from this \<open>g \<noteq> 0\<close> \<open>v \<in> keys f\<close> \<open>lt g adds\<^sub>t v\<close> show ?thesis by (rule is_red_addsI)
  qed
qed
  
lemma conversion_property:
  assumes "is_red {p} f" and "red {r} p q"
  shows "is_red {q} f \<or> is_red {r} f"
proof -
  let ?s = "lp p - lp r"
  from \<open>is_red {p} f\<close> obtain v where "v \<in> keys f" and "lt p adds\<^sub>t v" and "p \<noteq> 0"
    by (rule is_red_addsE, simp)
  from red_indE[OF \<open>red {r} p q\<close>]
    have "(r \<noteq> 0 \<and> lt r adds\<^sub>t lt p \<and> q = p - monom_mult (lc p / lc r) ?s r) \<or>
          red {r} (tail p) (q - monomial (lc p) (lt p))" by simp
  thus ?thesis
  proof
    assume "r \<noteq> 0 \<and> lt r adds\<^sub>t lt p \<and> q = p - monom_mult (lc p / lc r) ?s r"
    hence "r \<noteq> 0" and "lt r adds\<^sub>t lt p" by simp_all
    show ?thesis by (intro disjI2, rule is_red_singleton_trans, rule \<open>is_red {p} f\<close>, fact+)
  next
    assume "red {r} (tail p) (q - monomial (lc p) (lt p))" (is "red _ ?p' ?q'")
    with red_ord have "?q' \<prec>\<^sub>p ?p'" .
    hence "?p' \<noteq> 0"
      and assm: "(?q' = 0 \<or> ((lt ?q') \<prec>\<^sub>t (lt ?p') \<or> (lt ?q') = (lt ?p')))"
      unfolding ord_strict_p_rec[of ?q' ?p'] by (auto simp add: Let_def lc_def)
    have "lt ?p' \<prec>\<^sub>t lt p" by (rule lt_tail, fact)
    let ?m = "monomial (lc p) (lt p)"
    from monomial_0D[of "lt p" "lc p"] lc_not_0[OF \<open>p \<noteq> 0\<close>] have "?m \<noteq> 0" by blast
    have "lt ?m = lt p" by (rule lt_monomial, rule lc_not_0, fact)
    have "q \<noteq> 0 \<and> lt q = lt p"
    proof (cases "?q' = 0")
      case True
      hence "q = ?m" by simp
      with \<open>?m \<noteq> 0\<close> \<open>lt ?m = lt p\<close> show ?thesis by simp
    next
      case False
      from assm show ?thesis
      proof
        assume "(lt ?q') \<prec>\<^sub>t (lt ?p') \<or> (lt ?q') = (lt ?p')"
        hence "lt ?q' \<preceq>\<^sub>t lt ?p'" by auto
        also have "... \<prec>\<^sub>t lt p" by fact
        finally have "lt ?q' \<prec>\<^sub>t lt p" .
        hence "lt ?q' \<prec>\<^sub>t lt ?m" unfolding \<open>lt ?m = lt p\<close> .
        from lt_plus_eqI[OF this] \<open>lt ?m = lt p\<close> have "lt q = lt p" by simp
        show ?thesis
        proof (intro conjI, rule ccontr)
          assume "\<not> q \<noteq> 0"
          hence "q = 0" by simp
          hence "?q' = -?m" by simp
          hence "lt ?q' = lt (-?m)" by simp
          also have "... = lt ?m" using lt_uminus .
          finally have "lt ?q' = lt ?m" .
          with \<open>lt ?q' \<prec>\<^sub>t lt ?m\<close> show False by simp
        qed (fact)
      next
        assume "?q' = 0"
        with False show ?thesis ..
      qed
    qed
    hence "q \<noteq> 0" and "lt q adds\<^sub>t lt p" by (simp_all add: term_simps)
    show ?thesis by (intro disjI1, rule is_red_singleton_trans, rule \<open>is_red {p} f\<close>, fact+)
  qed
qed
  
lemma replace_red_stable_is_red:
  assumes a1: "is_red F f" and a2: "red (F - {p}) p q"
  shows "is_red (insert q (F - {p})) f" (is "is_red ?F' f")
proof -
  from a1 obtain g where "g \<in> F" and "is_red {g} f" by (rule is_red_singletonI)
  show ?thesis
  proof (cases "g = p")
    case True
    from a2 obtain h where "h \<in> F - {p}" and "red {h} p q" unfolding red_def by auto
    from \<open>is_red {g} f\<close> have "is_red {p} f" unfolding True .
    have "is_red {q} f \<or> is_red {h} f" by (rule conversion_property, fact+)
    thus ?thesis
    proof
      assume "is_red {q} f"
      show ?thesis
      proof (rule is_red_singletonD)
        show "q \<in> ?F'" by auto
      qed fact
    next
      assume "is_red {h} f"
      show ?thesis
      proof (rule is_red_singletonD)
        from \<open>h \<in> F - {p}\<close> show "h \<in> ?F'" by simp
      qed fact
    qed
  next
    case False
    show ?thesis
    proof (rule is_red_singletonD)
      from \<open>g \<in> F\<close> False show "g \<in> ?F'" by blast
    qed fact
  qed
qed

lemma is_red_map_scale:
  assumes "is_red F (c \<cdot> p)"
  shows "is_red F p"
proof -
  from assms obtain f u where "f \<in> F" and "u \<in> keys (c \<cdot> p)" and "f \<noteq> 0"
    and a: "lt f adds\<^sub>t u" by (rule is_red_addsE)
  from this(2) keys_map_scale_subset have "u \<in> keys p" ..
  with \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> show ?thesis using a by (rule is_red_addsI)
qed

corollary is_irred_map_scale: "\<not> is_red F p \<Longrightarrow> \<not> is_red F (c \<cdot> p)"
  by (auto dest: is_red_map_scale)

lemma is_red_map_scale_iff: "is_red F (c \<cdot> p) \<longleftrightarrow> (c \<noteq> 0 \<and> is_red F p)"
proof (intro iffI conjI notI)
  assume "is_red F (c \<cdot> p)" and "c = 0"
  thus False by (simp add: irred_0)
next
  assume "is_red F (c \<cdot> p)"
  thus "is_red F p" by (rule is_red_map_scale)
next
  assume "c \<noteq> 0 \<and> is_red F p"
  hence "is_red F (inverse c \<cdot> c \<cdot> p)" by (simp add: map_scale_assoc)
  thus "is_red F (c \<cdot> p)" by (rule is_red_map_scale)
qed

lemma is_red_uminus: "is_red F (- p) \<longleftrightarrow> is_red F p"
  by (auto elim!: is_red_addsE simp: keys_uminus intro: is_red_addsI)

lemma is_red_plus:
  assumes "is_red F (p + q)"
  shows "is_red F p \<or> is_red F q"
proof -
  from assms obtain f u where "f \<in> F" and "u \<in> keys (p + q)" and "f \<noteq> 0"
    and a: "lt f adds\<^sub>t u" by (rule is_red_addsE)
  from this(2) have "u \<in> keys p \<union> keys q"
    by (meson Poly_Mapping.keys_add subsetD)
  thus ?thesis
  proof
    assume "u \<in> keys p"
    with \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> have "is_red F p" using a by (rule is_red_addsI)
    thus ?thesis ..
  next
    assume "u \<in> keys q"
    with \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> have "is_red F q" using a by (rule is_red_addsI)
    thus ?thesis ..
  qed
qed

lemma is_irred_plus: "\<not> is_red F p \<Longrightarrow> \<not> is_red F q \<Longrightarrow> \<not> is_red F (p + q)"
  by (auto dest: is_red_plus)

lemma is_red_minus:
  assumes "is_red F (p - q)"
  shows "is_red F p \<or> is_red F q"
proof -
  from assms have "is_red F (p + (- q))" by simp
  hence "is_red F p \<or> is_red F (- q)" by (rule is_red_plus)
  thus ?thesis by (simp only: is_red_uminus)
qed

lemma is_irred_minus: "\<not> is_red F p \<Longrightarrow> \<not> is_red F q \<Longrightarrow> \<not> is_red F (p - q)"
  by (auto dest: is_red_minus)

end (* ordered_term *)

subsection \<open>Well-foundedness and Termination\<close>

context gd_term
begin

lemma dgrad_set_le_red_single:
  assumes "dickson_grading d" and "red_single p q f t"
  shows "dgrad_set_le d {t} (pp_of_term ` keys p)"
proof (rule dgrad_set_leI, simp)
  have "t adds t + lp f" by simp
  with assms(1) have "d t \<le> d (pp_of_term (t \<oplus> lt f))"
    by (simp add: term_simps, rule dickson_grading_adds_imp_le)
  moreover from assms(2) have "t \<oplus> lt f \<in> keys p" by (simp add: in_keys_iff red_single_def)
  ultimately show "\<exists>v\<in>keys p. d t \<le> d (pp_of_term v)" ..
qed

lemma dgrad_p_set_le_red_single:
  assumes "dickson_grading d" and "red_single p q f t"
  shows "dgrad_p_set_le d {q} {f, p}"
proof -
  let ?f = "monom_mult ((lookup p (t \<oplus> lt f)) / lc f) t f"
  from assms(2) have "t \<oplus> lt f \<in> keys p" and q: "q = p - ?f" by (simp_all add: red_single_def in_keys_iff)
  have "dgrad_p_set_le d {q} {p, ?f}" unfolding q by (fact dgrad_p_set_le_minus)
  also have "dgrad_p_set_le d ... {f, p}"
  proof (rule dgrad_p_set_leI_insert)
    from assms(1) have "dgrad_set_le d (pp_of_term ` keys ?f) (insert t (pp_of_term ` keys f))"
      by (rule dgrad_set_le_monom_mult)
    also have "dgrad_set_le d ... (pp_of_term ` (keys f \<union> keys p))"
    proof (rule dgrad_set_leI, simp)
      fix s
      assume "s = t \<or> s \<in> pp_of_term ` keys f"
      thus "\<exists>u\<in>keys f \<union> keys p. d s \<le> d (pp_of_term u)"
      proof
        assume "s = t"
        from assms have "dgrad_set_le d {s} (pp_of_term ` keys p)" unfolding \<open>s = t\<close>
          by (rule dgrad_set_le_red_single)
        moreover have "s \<in> {s}" ..
        ultimately obtain s0 where "s0 \<in> pp_of_term ` keys p" and "d s \<le> d s0" by (rule dgrad_set_leE)
        from this(1) obtain u where "u \<in> keys p" and "s0 = pp_of_term u" ..
        from this(1) have "u \<in> keys f \<union> keys p" by simp
        with \<open>d s \<le> d s0\<close> show ?thesis unfolding \<open>s0 = pp_of_term u\<close> ..
      next
        assume "s \<in> pp_of_term ` keys f"
        hence "s \<in> pp_of_term ` (keys f \<union> keys p)" by blast
        then obtain u where "u \<in> keys f \<union> keys p" and "s = pp_of_term u" ..
        note this(1)
        moreover have "d s \<le> d s" ..
        ultimately show ?thesis unfolding \<open>s = pp_of_term u\<close> ..
      qed
    qed
    finally show "dgrad_p_set_le d {?f} {f, p}" by (simp add: dgrad_p_set_le_def Keys_insert)
  next
    show "dgrad_p_set_le d {p} {f, p}" by (rule dgrad_p_set_le_subset, simp)
  qed
  finally show ?thesis .
qed

lemma dgrad_p_set_le_red:
  assumes "dickson_grading d" and "red F p q"
  shows "dgrad_p_set_le d {q} (insert p F)"
proof -
  from assms(2) obtain f t where "f \<in> F" and "red_single p q f t" by (rule red_setE)
  from assms(1) this(2) have "dgrad_p_set_le d {q} {f, p}" by (rule dgrad_p_set_le_red_single)
  also have "dgrad_p_set_le d ... (insert p F)" by (rule dgrad_p_set_le_subset, auto intro: \<open>f \<in> F\<close>)
  finally show ?thesis .
qed

corollary dgrad_p_set_le_red_rtrancl:
  assumes "dickson_grading d" and "(red F)\<^sup>*\<^sup>* p q"
  shows "dgrad_p_set_le d {q} (insert p F)"
  using assms(2)
proof (induct)
  case base
  show ?case by (rule dgrad_p_set_le_subset, simp)
next
  case (step y z)
  from assms(1) step(2) have "dgrad_p_set_le d {z} (insert y F)" by (rule dgrad_p_set_le_red)
  also have "dgrad_p_set_le d ... (insert p F)"
  proof (rule dgrad_p_set_leI_insert)
    show "dgrad_p_set_le d F (insert p F)" by (rule dgrad_p_set_le_subset, blast)
  qed fact
  finally show ?case .
qed

lemma dgrad_p_set_red_single_pp:
  assumes "dickson_grading d" and "p \<in> dgrad_p_set d m" and "red_single p q f t"
  shows "d t \<le> m"
proof -
  from assms(1) assms(3) have "dgrad_set_le d {t} (pp_of_term ` keys p)" by (rule dgrad_set_le_red_single)
  moreover have "t \<in> {t}" ..
  ultimately obtain s where "s \<in> pp_of_term ` keys p" and "d t \<le> d s" by (rule dgrad_set_leE)
  from this(1) obtain u where "u \<in> keys p" and "s = pp_of_term u" ..
  from assms(2) this(1) have "d (pp_of_term u) \<le> m" by (rule dgrad_p_setD)
  with \<open>d t \<le> d s\<close> show ?thesis unfolding \<open>s = pp_of_term u\<close> by (rule le_trans)
qed

lemma dgrad_p_set_closed_red_single:
  assumes "dickson_grading d" and "p \<in> dgrad_p_set d m" and "f \<in> dgrad_p_set d m"
    and "red_single p q f t"
  shows "q \<in> dgrad_p_set d m"
proof -
  from dgrad_p_set_le_red_single[OF assms(1, 4)] have "{q} \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from assms(2, 3) show "{f, p} \<subseteq> dgrad_p_set d m" by simp
  qed
  thus ?thesis by simp
qed

lemma dgrad_p_set_closed_red:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_p_set d m" and "p \<in> dgrad_p_set d m" and "red F p q"
  shows "q \<in> dgrad_p_set d m"
proof -
  from assms(4) obtain f t where "f \<in> F" and *: "red_single p q f t" by (rule red_setE)
  from assms(2) this(1) have "f \<in> dgrad_p_set d m" ..
  from assms(1) assms(3) this * show ?thesis by (rule dgrad_p_set_closed_red_single)
qed

lemma dgrad_p_set_closed_red_rtrancl:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_p_set d m" and "p \<in> dgrad_p_set d m" and "(red F)\<^sup>*\<^sup>* p q"
  shows "q \<in> dgrad_p_set d m"
  using assms(4)
proof (induct)
  case base
  from assms(3) show ?case .
next
  case (step r q)
  from assms(1) assms(2) step(3) step(2) show "q \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_red)
qed

lemma red_rtrancl_repE:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m" and "finite G" and "p \<in> dgrad_p_set d m"
    and "(red G)\<^sup>*\<^sup>* p r"
  obtains q where "p = r + (\<Sum>g\<in>G. q g \<odot> g)" and "\<And>g. q g \<in> punit.dgrad_p_set d m"
    and "\<And>g. lt (q g \<odot> g) \<preceq>\<^sub>t lt p"
  using assms(5)
proof (induct r arbitrary: thesis)
  case base
  show ?case
  proof (rule base)
    show "p = p + (\<Sum>g\<in>G. 0 \<odot> g)" by simp
  qed (simp_all add: punit.zero_in_dgrad_p_set min_term_min)
next
  case (step r' r)
  from step.hyps(2) obtain g t where "g \<in> G" and rs: "red_single r' r g t" by (rule red_setE)
  from this(2) have "r' = r + monomial (lookup r' (t \<oplus> lt g) / lc g) t \<odot> g"
    by (simp add: red_single_def mult_scalar_monomial)
  moreover define q0 where "q0 = monomial (lookup r' (t \<oplus> lt g) / lc g) t"
  ultimately have r': "r' = r + q0 \<odot> g" by simp
  obtain q' where p: "p = r' + (\<Sum>g\<in>G. q' g \<odot> g)" and 1: "\<And>g. q' g \<in> punit.dgrad_p_set d m"
    and 2: "\<And>g. lt (q' g \<odot> g) \<preceq>\<^sub>t lt p" by (rule step.hyps) blast
  define q where "q = q'(g := q0 + q' g)"
  show ?case
  proof (rule step.prems)
    from assms(3) \<open>g \<in> G\<close> have "p = (r + q0 \<odot> g) + (q' g \<odot> g + (\<Sum>g\<in>G - {g}. q' g \<odot> g))"
      by (simp add: p r' sum.remove)
    also have "\<dots> = r + (q g \<odot> g + (\<Sum>g\<in>G - {g}. q' g \<odot> g))"
      by (simp add: q_def mult_scalar_distrib_right)
    also from refl have "(\<Sum>g\<in>G - {g}. q' g \<odot> g) = (\<Sum>g\<in>G - {g}. q g \<odot> g)"
      by (rule sum.cong) (simp add: q_def)
    finally show "p = r + (\<Sum>g\<in>G. q g \<odot> g)" using assms(3) \<open>g \<in> G\<close> by (simp only: sum.remove)
  next
    fix g0
    have "q g0 \<in> punit.dgrad_p_set d m \<and> lt (q g0 \<odot> g0) \<preceq>\<^sub>t lt p"
    proof (cases "g0 = g")
      case True
      have eq: "q g = q0 + q' g" by (simp add: q_def)
      show ?thesis unfolding True eq
      proof
        from assms(1, 2, 4) step.hyps(1) have "r' \<in> dgrad_p_set d m"
          by (rule dgrad_p_set_closed_red_rtrancl)
        with assms(1) have "d t \<le> m" using rs by (rule dgrad_p_set_red_single_pp)
        hence "q0 \<in> punit.dgrad_p_set d m" by (simp add: q0_def punit.dgrad_p_set_def dgrad_set_def)
        thus "q0 + q' g \<in> punit.dgrad_p_set d m" by (intro punit.dgrad_p_set_closed_plus 1)
      next
        have "lt (q0 \<odot> g + q' g \<odot> g) \<preceq>\<^sub>t ord_term_lin.max (lt (q0 \<odot> g)) (lt (q' g \<odot> g))"
          by (fact lt_plus_le_max)
        also have "\<dots> \<preceq>\<^sub>t lt p"
        proof (intro ord_term_lin.max.boundedI 2)
          have "lt (q0 \<odot> g) \<preceq>\<^sub>t t \<oplus> lt g" by (simp add: q0_def mult_scalar_monomial lt_monom_mult_le)
          also from rs have "\<dots> \<preceq>\<^sub>t lt r'" by (intro lt_max) (simp add: red_single_def)
          also from step.hyps(1) have "\<dots> \<preceq>\<^sub>t lt p" by (intro ord_p_lt red_rtrancl_ord)
          finally show "lt (q0 \<odot> g) \<preceq>\<^sub>t lt p" .
        qed
        finally show "lt ((q0 + q' g) \<odot> g) \<preceq>\<^sub>t lt p" by (simp only: mult_scalar_distrib_right)
      qed
    next
      case False
      hence "q g0 = q' g0" by (simp add: q_def)
      thus ?thesis by (simp add: 1 2)
    qed
    thus "q g0 \<in> punit.dgrad_p_set d m" and "lt (q g0 \<odot> g0) \<preceq>\<^sub>t lt p" by simp_all
  qed
qed

lemma is_relation_order_red:
  assumes "dickson_grading d"
  shows "Confluence.relation_order (red F) (\<prec>\<^sub>p) (dgrad_p_set d m)"
proof
  show "wfp_on (\<prec>\<^sub>p) (dgrad_p_set d m)"
  proof (rule wfp_onI_min)
    fix x::"'t \<Rightarrow>\<^sub>0 'c" and Q
    assume "x \<in> Q" and "Q \<subseteq> dgrad_p_set d m"
    with assms obtain q where "q \<in> Q" and *: "\<And>y. y \<prec>\<^sub>p q \<Longrightarrow> y \<notin> Q"
      by (rule ord_p_minimum_dgrad_p_set, auto)
    from this(1) show "\<exists>z\<in>Q. \<forall>y\<in>dgrad_p_set d m. y \<prec>\<^sub>p z \<longrightarrow> y \<notin> Q"
    proof
      from * show "\<forall>y\<in>dgrad_p_set d m. y \<prec>\<^sub>p q \<longrightarrow> y \<notin> Q" by auto
    qed
  qed
next
  show "red F \<le> (\<prec>\<^sub>p)\<inverse>\<inverse>" by (simp add: predicate2I red_ord)
qed (fact ord_strict_p_transitive)

lemma red_wf_dgrad_p_set_aux:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_p_set d m"
  shows "wfp_on (red F)\<inverse>\<inverse> (dgrad_p_set d m)"
proof (rule wfp_onI_min)
  fix x::"'t \<Rightarrow>\<^sub>0 'b" and Q
  assume "x \<in> Q" and "Q \<subseteq> dgrad_p_set d m"
  with assms(1) obtain q where "q \<in> Q" and *: "\<And>y. y \<prec>\<^sub>p q \<Longrightarrow> y \<notin> Q"
    by (rule ord_p_minimum_dgrad_p_set, auto)
  from this(1) show "\<exists>z\<in>Q. \<forall>y\<in>dgrad_p_set d m. (red F)\<inverse>\<inverse> y z \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y\<in>dgrad_p_set d m. (red F)\<inverse>\<inverse> y q \<longrightarrow> y \<notin> Q"
    proof (intro ballI impI, simp)
      fix y
      assume "red F q y"
      hence "y \<prec>\<^sub>p q" by (rule red_ord)
      thus "y \<notin> Q" by (rule *)
    qed
  qed
qed

lemma red_wf_dgrad_p_set:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_p_set d m"
  shows "wfP (red F)\<inverse>\<inverse>"
proof (rule wfI_min[to_pred])
  fix x::"'t \<Rightarrow>\<^sub>0 'b" and Q
  assume "x \<in> Q"
  from assms(2) obtain n where "m \<le> n" and "x \<in> dgrad_p_set d n" and "F \<subseteq> dgrad_p_set d n"
    by (rule dgrad_p_set_insert)
  let ?Q = "Q \<inter> dgrad_p_set d n"
  from assms(1) \<open>F \<subseteq> dgrad_p_set d n\<close> have "wfp_on (red F)\<inverse>\<inverse> (dgrad_p_set d n)"
    by (rule red_wf_dgrad_p_set_aux)
  moreover from \<open>x \<in> Q\<close> \<open>x \<in> dgrad_p_set d n\<close> have "x \<in> ?Q" ..
  moreover have "?Q \<subseteq> dgrad_p_set d n" by simp
  ultimately obtain z where "z \<in> ?Q" and *: "\<And>y. (red F)\<inverse>\<inverse> y z \<Longrightarrow> y \<notin> ?Q" by (rule wfp_onE_min) blast
  from this(1) have "z \<in> Q" and "z \<in> dgrad_p_set d n" by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y. (red F)\<inverse>\<inverse> y z \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y. (red F)\<inverse>\<inverse> y z \<longrightarrow> y \<notin> Q"
    proof (intro allI impI)
      fix y
      assume "(red F)\<inverse>\<inverse> y z"
      hence "red F z y" by simp
      with assms(1) \<open>F \<subseteq> dgrad_p_set d n\<close> \<open>z \<in> dgrad_p_set d n\<close> have "y \<in> dgrad_p_set d n"
        by (rule dgrad_p_set_closed_red)
      moreover from \<open>(red F)\<inverse>\<inverse> y z\<close> have "y \<notin> ?Q" by (rule *)
      ultimately show "y \<notin> Q" by blast
    qed
  qed
qed

lemmas red_wf_finite = red_wf_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

lemma cbelow_on_monom_mult:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_p_set d m" and "d t \<le> m" and "c \<noteq> 0"
    and "cbelow_on (dgrad_p_set d m) (\<prec>\<^sub>p) z (\<lambda>a b. red F a b \<or> red F b a) p q"
  shows "cbelow_on (dgrad_p_set d m) (\<prec>\<^sub>p) (monom_mult c t z) (\<lambda>a b. red F a b \<or> red F b a)
          (monom_mult c t p) (monom_mult c t q)"
  using assms(5)
proof (induct rule: cbelow_on_induct)
  case base
  show ?case unfolding cbelow_on_def
  proof (rule disjI1, intro conjI, fact refl)
    from assms(5) have "p \<in> dgrad_p_set d m" by (rule cbelow_on_first_in)
    with assms(1) assms(3) show "monom_mult c t p \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_monom_mult)
  next
    from assms(5) have "p \<prec>\<^sub>p z" by (rule cbelow_on_first_below)
    from this assms(4) show "monom_mult c t p \<prec>\<^sub>p monom_mult c t z" by (rule ord_strict_p_monom_mult)
  qed
next
  case (step q' q)
  let ?R = "\<lambda>a b. red F a b \<or> red F b a"
  from step(5) show ?case
  proof
    from assms(1) assms(3) step(3) show "monom_mult c t q \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_monom_mult)
  next
    from step(2) red_monom_mult[OF _ assms(4)] show "?R (monom_mult c t q') (monom_mult c t q)" by auto
  next
    from step(4) assms(4) show "monom_mult c t q \<prec>\<^sub>p monom_mult c t z" by (rule ord_strict_p_monom_mult)
  qed
qed

lemma cbelow_on_monom_mult_monomial:
  assumes "c \<noteq> 0"
    and "cbelow_on (dgrad_p_set d m) (\<prec>\<^sub>p) (monomial c' v) (\<lambda>a b. red F a b \<or> red F b a) p q"
  shows "cbelow_on (dgrad_p_set d m) (\<prec>\<^sub>p) (monomial c (t \<oplus> v)) (\<lambda>a b. red F a b \<or> red F b a) p q"
proof -
  have *: "f \<prec>\<^sub>p monomial c' v \<Longrightarrow> f \<prec>\<^sub>p monomial c (t \<oplus> v)" for f
  proof (simp add: ord_strict_p_monomial_iff assms(1), elim conjE disjE, erule disjI1, rule disjI2)
    assume "lt f \<prec>\<^sub>t v"
    also have "... \<preceq>\<^sub>t t \<oplus> v" using local.zero_min using splus_mono_left splus_zero by fastforce
    finally show "lt f \<prec>\<^sub>t t \<oplus> v" .
  qed
  from assms(2) show ?thesis
  proof (induct rule: cbelow_on_induct)
    case base
    show ?case unfolding cbelow_on_def
    proof (rule disjI1, intro conjI, fact refl)
      from assms(2) show "p \<in> dgrad_p_set d m" by (rule cbelow_on_first_in)
    next
      from assms(2) have "p \<prec>\<^sub>p monomial c' v" by (rule cbelow_on_first_below)
      thus "p \<prec>\<^sub>p monomial c (t \<oplus> v)" by (rule *)
    qed
  next
    case (step q' q)
    let ?R = "\<lambda>a b. red F a b \<or> red F b a"
    from step(5) step(3) step(2) show ?case
    proof
      from step(4) show "q \<prec>\<^sub>p monomial c (t \<oplus> v)" by (rule *)
    qed
  qed
qed

lemma cbelow_on_plus:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_p_set d m" and "r \<in> dgrad_p_set d m"
    and "keys r \<inter> keys z = {}"
    and "cbelow_on (dgrad_p_set d m) (\<prec>\<^sub>p) z (\<lambda>a b. red F a b \<or> red F b a) p q"
  shows "cbelow_on (dgrad_p_set d m) (\<prec>\<^sub>p) (z + r) (\<lambda>a b. red F a b \<or> red F b a) (p + r) (q + r)"
  using assms(5)
proof (induct rule: cbelow_on_induct)
  case base
  show ?case unfolding cbelow_on_def
  proof (rule disjI1, intro conjI, fact refl)
    from assms(5) have "p \<in> dgrad_p_set d m" by (rule cbelow_on_first_in)
    from this assms(3) show "p + r \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_plus)
  next
    from assms(5) have "p \<prec>\<^sub>p z" by (rule cbelow_on_first_below)
    from this assms(4) show "p + r \<prec>\<^sub>p z + r" by (rule ord_strict_p_plus)
  qed
next
  case (step q' q)
  let ?RS = "\<lambda>a b. red F a b \<or> red F b a"
  let ?A = "dgrad_p_set d m"
  let ?R = "red F"
  let ?ord = "(\<prec>\<^sub>p)"
  from assms(1) have ro: "relation_order ?R ?ord ?A"
    by (rule is_relation_order_red)
  have dw: "relation.dw_closed ?R ?A"
    by (rule relation.dw_closedI, rule dgrad_p_set_closed_red, rule assms(1), rule assms(2))
  from step(2) have "relation.cs (red F) (q' + r) (q + r)"
  proof
    assume "red F q q'"
    hence "relation.cs (red F) (q + r) (q' + r)" by (rule red_plus_cs)
    thus ?thesis by (rule relation.cs_sym)
  next
    assume "red F q' q"
    thus ?thesis by (rule red_plus_cs)
  qed
  with ro dw have "cbelow_on ?A ?ord (z + r) ?RS (q' + r) (q + r)"
  proof (rule relation_order.cs_implies_cbelow_on)
    from step(1) have "q' \<in> ?A" by (rule cbelow_on_second_in)
    from this assms(3) show "q' + r \<in> ?A" by (rule dgrad_p_set_closed_plus)
  next
    from step(3) assms(3) show "q + r \<in> ?A" by (rule dgrad_p_set_closed_plus)
  next
    from step(1) have "q' \<prec>\<^sub>p z" by (rule cbelow_on_second_below)
    from this assms(4) show "q' + r \<prec>\<^sub>p z + r" by (rule ord_strict_p_plus)
  next
    from step(4) assms(4) show "q + r \<prec>\<^sub>p z + r" by (rule ord_strict_p_plus)
  qed
  with step(5) show ?case by (rule cbelow_on_transitive)
qed

lemma is_full_pmdlI_lt_dgrad_p_set:
  assumes "dickson_grading d" and "B \<subseteq> dgrad_p_set d m"
  assumes "\<And>k. k \<in> component_of_term ` Keys (B::('t \<Rightarrow>\<^sub>0 'b::field) set) \<Longrightarrow>
            (\<exists>b\<in>B. b \<noteq> 0 \<and> component_of_term (lt b) = k \<and> lp b = 0)"
  shows "is_full_pmdl B"
proof (rule is_full_pmdlI)
  fix p::"'t \<Rightarrow>\<^sub>0 'b"
  from assms(1, 2) have "wfP (red B)\<inverse>\<inverse>" by (rule red_wf_dgrad_p_set)
  moreover assume "component_of_term ` keys p \<subseteq> component_of_term ` Keys B"
  ultimately show "p \<in> pmdl B"
  proof (induct p)
    case (less p)
    show ?case
    proof (cases "p = 0")
      case True
      show ?thesis by (simp add: True pmdl.span_zero)
    next
      case False
      hence "lt p \<in> keys p" by (rule lt_in_keys)
      hence "component_of_term (lt p) \<in> component_of_term ` keys p" by simp
      also have "... \<subseteq> component_of_term ` Keys B" by fact
      finally have "\<exists>b\<in>B. b \<noteq> 0 \<and> component_of_term (lt b) = component_of_term (lt p) \<and> lp b = 0"
        by (rule assms(3))
      then obtain b where "b \<in> B" and "b \<noteq> 0" and "component_of_term (lt b) = component_of_term (lt p)"
        and "lp b = 0" by blast
      from this(3, 4) have eq: "lp p \<oplus> lt b = lt p" by (simp add: splus_def term_of_pair_pair)
      define q where "q = p - monom_mult (lookup p ((lp p) \<oplus> lt b) / lc b) (lp p) b"
      have "red_single p q b (lp p)"
        by (auto simp: red_single_def \<open>b \<noteq> 0\<close> q_def eq \<open>lt p \<in> keys p\<close>)
      with \<open>b \<in> B\<close> have "red B p q" by (rule red_setI)
      hence "(red B)\<inverse>\<inverse> q p" ..
      moreover have "component_of_term ` keys q \<subseteq> component_of_term ` Keys B"
      proof (rule subset_trans)
        from \<open>red B p q\<close> show "component_of_term ` keys q \<subseteq> component_of_term ` keys p \<union> component_of_term ` Keys B"
          by (rule components_red_subset)
      next
        from less(2) show "component_of_term ` keys p \<union> component_of_term ` Keys B \<subseteq> component_of_term ` Keys B"
          by blast
      qed
      ultimately have "q \<in> pmdl B" by (rule less.hyps)
      have "q + monom_mult (lookup p ((lp p) \<oplus> lt b) / lc b) (lp p) b \<in> pmdl B"
        by (rule pmdl.span_add, fact, rule pmdl_closed_monom_mult, rule pmdl.span_base, fact)
      thus ?thesis by (simp add: q_def)
    qed
  qed
qed

lemmas is_full_pmdlI_lt_finite = is_full_pmdlI_lt_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

end (* gd_term *)

subsection \<open>Algorithms\<close>

subsubsection \<open>Function \<open>find_adds\<close>\<close>

context ordered_term
begin

primrec find_adds :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> 't \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero) option" where
  "find_adds [] _ = None"|
  "find_adds (f # fs) u = (if f \<noteq> 0 \<and> lt f adds\<^sub>t u then Some f else find_adds fs u)"

lemma find_adds_SomeD1:
  assumes "find_adds fs u = Some f"
  shows "f \<in> set fs"
  using assms by (induct fs, simp, simp split: if_splits)

lemma find_adds_SomeD2:
  assumes "find_adds fs u = Some f"
  shows "f \<noteq> 0"
  using assms by (induct fs, simp, simp split: if_splits)

lemma find_adds_SomeD3:
  assumes "find_adds fs u = Some f"
  shows "lt f adds\<^sub>t u"
  using assms by (induct fs, simp, simp split: if_splits)

lemma find_adds_NoneE:
  assumes "find_adds fs u = None" and "f \<in> set fs"
  assumes "f = 0 \<Longrightarrow> thesis" and "f \<noteq> 0 \<Longrightarrow> \<not> lt f adds\<^sub>t u \<Longrightarrow> thesis"
  shows thesis
  using assms
proof (induct fs arbitrary: thesis)
  case Nil
  from Nil(2) show ?case by simp
next
  case (Cons a fs)
  from Cons(2) have 1: "a = 0 \<or> \<not> lt a adds\<^sub>t u" and 2: "find_adds fs u = None"
    by (simp_all split: if_splits)
  from Cons(3) have "f = a \<or> f \<in> set fs" by simp
  thus ?case
  proof
    assume "f = a"
    show ?thesis
    proof (cases "a = 0")
      case True
      show ?thesis by (rule Cons(4), simp add: \<open>f = a\<close> True)
    next
      case False
      with 1 have *: "\<not> lt a adds\<^sub>t u" by simp
      show ?thesis by (rule Cons(5), simp_all add: \<open>f = a\<close> * False)
    qed
  next
    assume "f \<in> set fs"
    with 2 show ?thesis
    proof (rule Cons(1))
      assume "f = 0"
      thus ?thesis by (rule Cons(4))
    next
      assume "f \<noteq> 0" and "\<not> lt f adds\<^sub>t u"
      thus ?thesis by (rule Cons(5))
    qed
  qed
qed

lemma find_adds_SomeD_red_single:
  assumes "p \<noteq> 0" and "find_adds fs (lt p) = Some f"
  shows "red_single p (tail p - monom_mult (lc p / lc f) (lp p - lp f) (tail f)) f (lp p - lp f)"
proof -
  let ?f = "monom_mult (lc p / lc f) (lp p - lp f) f"
  from assms(2) have "f \<noteq> 0" and "lt f adds\<^sub>t lt p" by (rule find_adds_SomeD2, rule find_adds_SomeD3)
  from this(2) have eq: "(lp p - lp f) \<oplus> lt f = lt p"
    by (simp add: adds_minus_splus adds_term_def term_of_pair_pair)
  from assms(1) have "lc p \<noteq> 0" by (rule lc_not_0)
  moreover from \<open>f \<noteq> 0\<close> have "lc f \<noteq> 0" by (rule lc_not_0)
  ultimately have "lc p / lc f \<noteq> 0" by simp
  hence "lt ?f = (lp p - lp f) \<oplus> lt f" by (simp add: lt_monom_mult \<open>f \<noteq> 0\<close>)
  hence lt_f: "lt ?f = lt p" by (simp only: eq)
  have "lookup ?f (lt p) = lookup ?f ((lp p - lp f) \<oplus> lt f)" by (simp only: eq)
  also have "... = (lc p / lc f) * lookup f (lt f)" by (rule lookup_monom_mult_plus)
  also from \<open>lc f \<noteq> 0\<close> have "... = lookup p (lt p)" by (simp add: lc_def)
  finally have lc_f: "lookup ?f (lt p) = lookup p (lt p)" .
  have "red_single p (p - ?f) f (lp p - lp f)"
    by (auto simp: red_single_def eq lc_def \<open>f \<noteq> 0\<close> lt_in_keys assms(1))
  moreover have "p - ?f = tail p - monom_mult (lc p / lc f) (lp p - lp f) (tail f)"
    by (rule poly_mapping_eqI,
        simp add: tail_monom_mult[symmetric] lookup_minus lookup_tail_2 lt_f lc_f split: if_split)
  ultimately show ?thesis by simp
qed

lemma find_adds_SomeD_red:
  assumes "p \<noteq> 0" and "find_adds fs (lt p) = Some f"
  shows "red (set fs) p (tail p - monom_mult (lc p / lc f) (lp p - lp f) (tail f))"
proof (rule red_setI)
  from assms(2) show "f \<in> set fs" by (rule find_adds_SomeD1)
next
  from assms show "red_single p (tail p - monom_mult (lc p / lc f) (lp p - lp f) (tail f)) f (lp p - lp f)"
    by (rule find_adds_SomeD_red_single)
qed

end (* ordered_term *)

subsubsection \<open>Function \<open>trd\<close>\<close>

context gd_term
begin

definition trd_term :: "('a \<Rightarrow> nat) \<Rightarrow> ((('t \<Rightarrow>\<^sub>0 'b::field) list \<times> ('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)) \<times>
                                        (('t \<Rightarrow>\<^sub>0 'b) list \<times> ('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b))) set"
  where "trd_term d = {(x, y). dgrad_p_set_le d (set (fst (snd x) # fst x)) (set (fst (snd y) # fst y)) \<and> fst (snd x) \<prec>\<^sub>p fst (snd y)}"

lemma trd_term_wf:
  assumes "dickson_grading d"
  shows "wf (trd_term d)"
proof (rule wfI_min)
  fix x :: "('t \<Rightarrow>\<^sub>0 'b::field) list \<times> ('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b)" and Q
  assume "x \<in> Q"
  let ?A = "set (fst (snd x) # fst x)"
  have "finite ?A" ..
  then obtain m where A: "?A \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  let ?B = "dgrad_p_set d m"
  let ?Q = "{q \<in> Q. set (fst (snd q) # fst q) \<subseteq> ?B}"
  note assms
  moreover have "fst (snd x) \<in> fst ` snd ` ?Q"
    by (rule, fact refl, rule, fact refl, simp only: mem_Collect_eq A \<open>x \<in> Q\<close>)
  moreover have "fst ` snd ` ?Q \<subseteq> ?B" by auto
  ultimately obtain z0 where "z0 \<in> fst ` snd ` ?Q"
    and *: "\<And>y. y \<prec>\<^sub>p z0 \<Longrightarrow> y \<notin> fst ` snd ` ?Q" by (rule ord_p_minimum_dgrad_p_set, blast)
  from this(1) obtain z where "z \<in> {q \<in> Q. set (fst (snd q) # fst q) \<subseteq> ?B}" and z0: "z0 = fst (snd z)"
    by fastforce
  from this(1) have "z \<in> Q" and a: "set (fst (snd z) # fst z) \<subseteq> ?B" by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> trd_term d \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y. (y, z) \<in> trd_term d \<longrightarrow> y \<notin> Q"
    proof (intro allI impI)
      fix y
      assume "(y, z) \<in> trd_term d"
      hence b: "dgrad_p_set_le d (set (fst (snd y) # fst y)) (set (fst (snd z) # fst z))" and "fst (snd y) \<prec>\<^sub>p z0"
        by (simp_all add: trd_term_def z0)
      from this(2) have "fst (snd y) \<notin> fst ` snd ` ?Q" by (rule *)
      hence "y \<notin> Q \<or> \<not> set (fst (snd y) # fst y) \<subseteq> ?B" by auto
      moreover from b a have "set (fst (snd y) # fst y) \<subseteq> ?B" by (rule dgrad_p_set_le_dgrad_p_set)
      ultimately show "y \<notin> Q" by simp
    qed
  qed
qed

function trd_aux :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field)" where
  "trd_aux fs p r =
    (if p = 0 then
      r
    else
      case find_adds fs (lt p) of
        None   \<Rightarrow> trd_aux fs (tail p) (r + monomial (lc p) (lt p))
      | Some f \<Rightarrow> trd_aux fs (tail p - monom_mult (lc p / lc f) (lp p - lp f) (tail f)) r
    )"
  by auto
termination proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading d" ..
  let ?R = "trd_term d"
  show ?thesis
  proof (rule, rule trd_term_wf, fact)
    fix fs and p r::"'t \<Rightarrow>\<^sub>0 'b"
    assume "p \<noteq> 0"
    show "((fs, tail p, r + monomial (lc p) (lt p)), fs, p, r) \<in> trd_term d"
    proof (simp add: trd_term_def, rule)
      show "dgrad_p_set_le d (insert (tail p) (set fs)) (insert p (set fs))"
      proof (rule dgrad_p_set_leI_insert_keys, rule dgrad_p_set_le_subset, rule subset_insertI,
            rule dgrad_set_le_subset, simp add: Keys_insert image_Un)
        have "keys (tail p) \<subseteq> keys p" by (auto simp: keys_tail)
        hence "pp_of_term ` keys (tail p) \<subseteq> pp_of_term ` keys p" by (rule image_mono)
        thus "pp_of_term ` keys (tail p) \<subseteq> pp_of_term ` keys p \<union> pp_of_term ` Keys (set fs)" by blast
      qed
    next
      from \<open>p \<noteq> 0\<close> show "tail p \<prec>\<^sub>p p" by (rule tail_ord_p)
    qed
  next
    fix fs::"('t \<Rightarrow>\<^sub>0 'b) list" and p r f ::"'t \<Rightarrow>\<^sub>0 'b"
    assume "p \<noteq> 0" and "find_adds fs (lt p) = Some f"
    hence "red (set fs) p (tail p - monom_mult (lc p / lc f) (lp p - lp f) (tail f))"
      (is "red _ p ?q") by (rule find_adds_SomeD_red)
    show "((fs, ?q, r), fs, p, r) \<in> trd_term d"
      by (simp add: trd_term_def, rule, rule dgrad_p_set_leI_insert, rule dgrad_p_set_le_subset, rule subset_insertI,
            rule dgrad_p_set_le_red, fact dg, fact \<open>red (set fs) p ?q\<close>, rule red_ord, fact)
  qed
qed

definition trd :: "('t \<Rightarrow>\<^sub>0 'b::field) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b)"
  where "trd fs p = trd_aux fs p 0"

lemma trd_aux_red_rtrancl: "(red (set fs))\<^sup>*\<^sup>* p (trd_aux fs p r - r)"
proof (induct fs p r rule: trd_aux.induct)
  case (1 fs p r)
  show ?case
  proof (simp, split option.split, intro conjI impI allI)
    assume "p \<noteq> 0" and "find_adds fs (lt p) = None"
    hence "(red (set fs))\<^sup>*\<^sup>* (tail p) (trd_aux fs (tail p) (r + monomial (lc p) (lt p)) - (r + monomial (lc p) (lt p)))"
      by (rule 1(1))
    hence "(red (set fs))\<^sup>*\<^sup>* (tail p + monomial (lc p) (lt p))
              (trd_aux fs (tail p) (r + monomial (lc p) (lt p)) - (r + monomial (lc p) (lt p)) + monomial (lc p ) (lt p))"
    proof (rule red_rtrancl_plus_higher)
      fix u v
      assume "u \<in> keys (tail p)"
      assume "v \<in> keys (monomial (lc p) (lt p))"
      also have "... \<subseteq> {lt p}" by (simp add: keys_monomial)
      finally have "v = lt p" by simp
      from \<open>u \<in> keys (tail p)\<close> show "u \<prec>\<^sub>t v" unfolding \<open>v = lt p\<close> by (rule keys_tail_less_lt)
    qed
    thus "(red (set fs))\<^sup>*\<^sup>* p (trd_aux fs (tail p) (r + monomial (lc p) (lt p)) - r)"
      by (simp only: leading_monomial_tail[symmetric] add.commute[of _ "monomial (lc p) (lt p)"], simp)
  next
    fix f
    assume "p \<noteq> 0" and "find_adds fs (lt p) = Some f"
    hence "(red (set fs))\<^sup>*\<^sup>* (tail p - monom_mult (lc p / lc f) (lp p - lp f) (tail f))
                    (trd_aux fs (tail p - monom_mult (lc p / lc f) (lp p - lp f) (tail f)) r - r)"
      and *: "red (set fs) p (tail p - monom_mult (lc p / lc f) (lp p - lp f) (tail f))"
      by (rule 1(2), rule find_adds_SomeD_red)
    let ?q = "tail p - monom_mult (lc p / lc f) (lp p - lp f) (tail f)"
    from * have "(red (set fs))\<^sup>*\<^sup>* p ?q" ..
    moreover have "(red (set fs))\<^sup>*\<^sup>* ?q (trd_aux fs ?q r - r)" by fact
    ultimately show "(red (set fs))\<^sup>*\<^sup>* p (trd_aux fs ?q r - r)" by (rule rtranclp_trans)
  qed
qed

corollary trd_red_rtrancl: "(red (set fs))\<^sup>*\<^sup>* p (trd fs p)"
proof -
  have "(red (set fs))\<^sup>*\<^sup>* p (trd fs p - 0)" unfolding trd_def by (rule trd_aux_red_rtrancl)
  thus ?thesis by simp
qed

lemma trd_aux_irred:
  assumes "\<not> is_red (set fs) r"
  shows "\<not> is_red (set fs) (trd_aux fs p r)"
  using assms
proof (induct fs p r rule: trd_aux.induct)
  case (1 fs p r)
  show ?case
  proof (simp add: 1(3), split option.split, intro impI conjI allI)
    assume "p \<noteq> 0" and *: "find_adds fs (lt p) = None"
    thus "\<not> is_red (set fs) (trd_aux fs (tail p) (r + monomial (lc p) (lt p)))"
    proof (rule 1(1))
      show "\<not> is_red (set fs) (r + monomial (lc p) (lt p))"
      proof
        assume "is_red (set fs) (r + monomial (lc p) (lt p))"
        then obtain f u where "f \<in> set fs" and "f \<noteq> 0" and "u \<in> keys (r + monomial (lc p) (lt p))"
          and "lt f adds\<^sub>t u" by (rule is_red_addsE)
        note this(3)
        also have "keys (r + monomial (lc p) (lt p)) \<subseteq> keys r \<union> keys (monomial (lc p) (lt p))"
          by (rule Poly_Mapping.keys_add)
        also have "... \<subseteq> insert (lt p) (keys r)" by auto
        finally show False
        proof
          assume "u = lt p"
          from * \<open>f \<in> set fs\<close> show ?thesis
          proof (rule find_adds_NoneE)
            assume "f = 0"
            with \<open>f \<noteq> 0\<close> show ?thesis ..
          next
            assume "\<not> lt f adds\<^sub>t lt p"
            from this \<open>lt f adds\<^sub>t u\<close> show ?thesis unfolding \<open>u = lt p\<close> ..
          qed
        next
          assume "u \<in> keys r"
          from \<open>f \<in> set fs\<close> \<open>f \<noteq> 0\<close> this \<open>lt f adds\<^sub>t u\<close> have "is_red (set fs) r" by (rule is_red_addsI)
          with 1(3) show ?thesis ..
        qed
      qed
    qed
  next
    fix f
    assume "p \<noteq> 0" and "find_adds fs (lt p) = Some f"
    from this 1(3) show "\<not> is_red (set fs) (trd_aux fs (tail p - monom_mult (lc p / lc f) (lp p - lp f) (tail f)) r)" 
      by (rule 1(2))
  qed
qed

corollary trd_irred: "\<not> is_red (set fs) (trd fs p)"
  unfolding trd_def using irred_0 by (rule trd_aux_irred)

lemma trd_in_pmdl: "p - (trd fs p) \<in> pmdl (set fs)"
  using trd_red_rtrancl by (rule red_rtranclp_diff_in_pmdl)

lemma pmdl_closed_trd:
  assumes "p \<in> pmdl B" and "set fs \<subseteq> pmdl B"
  shows "(trd fs p) \<in> pmdl B"
proof -
  from assms(2) have "pmdl (set fs) \<subseteq> pmdl B" by (rule pmdl.span_subset_spanI)
  with trd_in_pmdl have "p - trd fs p \<in> pmdl B" ..
  with assms(1) have "p - (p - trd fs p) \<in> pmdl B" by (rule pmdl.span_diff)
  thus ?thesis by simp
qed

end (* gd_term *)

end (* theory *)
