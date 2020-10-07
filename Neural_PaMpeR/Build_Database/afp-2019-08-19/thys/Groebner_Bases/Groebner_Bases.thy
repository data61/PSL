(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Gr\"obner Bases and Buchberger's Theorem\<close>

theory Groebner_Bases
imports Reduction
begin

text \<open>This theory provides the main results about Gr\"obner bases for modules of multivariate polynomials.\<close>

context gd_term
begin

definition crit_pair :: "('t \<Rightarrow>\<^sub>0 'b::field) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('t \<Rightarrow>\<^sub>0 'b) \<times> ('t \<Rightarrow>\<^sub>0 'b))"
  where "crit_pair p q =
          (if component_of_term (lt p) = component_of_term (lt q) then
            (monom_mult (1 / lc p) ((lcs (lp p) (lp q)) - (lp p)) (tail p),
            monom_mult (1 / lc q) ((lcs (lp p) (lp q)) - (lp q)) (tail q))
          else (0, 0))"

definition crit_pair_cbelow_on :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "crit_pair_cbelow_on d m F p q \<longleftrightarrow>
                cbelow_on (dgrad_p_set d m) (\<prec>\<^sub>p)
                          (monomial 1 (term_of_pair (lcs (lp p) (lp q), component_of_term (lt p))))
                          (\<lambda>a b. red F a b \<or> red F b a) (fst (crit_pair p q)) (snd (crit_pair p q))"

definition spoly :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field)"
  where "spoly p q = (let v1 = lt p; v2 = lt q in
                      if component_of_term v1 = component_of_term v2 then
                        let t1 = pp_of_term v1; t2 = pp_of_term v2; l = lcs t1 t2 in
                        (monom_mult (1 / lookup p v1) (l - t1) p) - (monom_mult (1 / lookup q v2) (l - t2) q)
                      else 0)"

definition (in ordered_term) is_Groebner_basis :: "('t \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> bool"
  where "is_Groebner_basis F \<equiv> relation.is_ChurchRosser (red F)"

subsection \<open>Critical Pairs and S-Polynomials\<close>

lemma crit_pair_same: "fst (crit_pair p p) = snd (crit_pair p p)"
  by (simp add: crit_pair_def)

lemma crit_pair_swap: "crit_pair p q = (snd (crit_pair q p), fst (crit_pair q p))"
  by (simp add: crit_pair_def lcs_comm)

lemma crit_pair_zero [simp]: "fst (crit_pair 0 q) = 0" and "snd (crit_pair p 0) = 0"
  by (simp_all add: crit_pair_def)

lemma dgrad_p_set_le_crit_pair_zero: "dgrad_p_set_le d {fst (crit_pair p 0)} {p}"
proof (simp add: crit_pair_def lt_def[of 0] lcs_comm lcs_zero dgrad_p_set_le_def Keys_insert
      min_term_def term_simps, intro conjI impI dgrad_set_leI)
  fix s
  assume "s \<in> pp_of_term ` keys (monom_mult (1 / lc p) 0 (tail p))"
  then obtain v where "v \<in> keys (monom_mult (1 / lc p) 0 (tail p))" and "s = pp_of_term v" ..
  from this(1) keys_monom_mult_subset have "v \<in> (\<oplus>) 0 ` keys (tail p)" ..
  hence "v \<in> keys (tail p)" by (simp add: image_iff term_simps)
  hence "v \<in> keys p" by (simp add: keys_tail)
  hence "s \<in> pp_of_term ` keys p" by (simp add: \<open>s = pp_of_term v\<close>)
  moreover have "d s \<le> d s" ..
  ultimately show "\<exists>t\<in>pp_of_term ` keys p. d s \<le> d t" ..
qed simp

lemma dgrad_p_set_le_fst_crit_pair:
  assumes "dickson_grading d"
  shows "dgrad_p_set_le d {fst (crit_pair p q)} {p, q}"
proof (cases "q = 0")
  case True
  have "dgrad_p_set_le d {fst (crit_pair p q)} {p}" unfolding True
    by (fact dgrad_p_set_le_crit_pair_zero)
  also have "dgrad_p_set_le d ... {p, q}" by (rule dgrad_p_set_le_subset, simp)
  finally show ?thesis .
next
  case False
  show ?thesis
  proof (cases "p = 0")
    case True
    have "dgrad_p_set_le d {fst (crit_pair p q)} {q}"
      by (simp add: True dgrad_p_set_le_def dgrad_set_le_def)
    also have "dgrad_p_set_le d ... {p, q}" by (rule dgrad_p_set_le_subset, simp)
    finally show ?thesis .
  next
    case False
    show ?thesis
    proof (simp add: dgrad_p_set_le_def Keys_insert crit_pair_def, intro conjI impI)
      define t where "t = lcs (lp p) (lp q) - lp p"
      let ?m = "monom_mult (1 / lc p) t (tail p)"
      from assms have "dgrad_set_le d (pp_of_term ` keys ?m) (insert t (pp_of_term ` keys (tail p)))"
        by (rule dgrad_set_le_monom_mult)
      also have "dgrad_set_le d ... (pp_of_term ` (keys p \<union> keys q))"
      proof (rule dgrad_set_leI, simp)
        fix s
        assume "s = t \<or> s \<in> pp_of_term ` keys (tail p)"
        thus "\<exists>v\<in>keys p \<union> keys q. d s \<le> d (pp_of_term v)"
        proof
          assume "s = t"
          from assms have "d s \<le> ord_class.max (d (lp p)) (d (lp q))"
            unfolding \<open>s = t\<close> t_def by (rule dickson_grading_lcs_minus)
          hence "d s \<le> d (lp p) \<or> d s \<le> d (lp q)" by auto
          thus ?thesis
          proof
            from \<open>p \<noteq> 0\<close> have "lt p \<in> keys p" by (rule lt_in_keys)
            hence "lt p \<in> keys p \<union> keys q" by simp
            moreover assume "d s \<le> d (lp p)"
            ultimately show ?thesis ..
          next
            from \<open>q \<noteq> 0\<close> have "lt q \<in> keys q" by (rule lt_in_keys)
            hence "lt q \<in> keys p \<union> keys q" by simp
            moreover assume "d s \<le> d (lp q)"
            ultimately show ?thesis ..
          qed
        next
          assume "s \<in> pp_of_term ` keys (tail p)"
          hence "s \<in> pp_of_term ` (keys p \<union> keys q)" by (auto simp: keys_tail)
          then obtain v where "v \<in> keys p \<union> keys q" and "s = pp_of_term v" ..
          note this(1)
          moreover have "d s \<le> d (pp_of_term v)" by (simp add: \<open>s = pp_of_term v\<close>)
          ultimately show ?thesis ..
        qed
      qed
      finally show "dgrad_set_le d (pp_of_term ` keys ?m) (pp_of_term ` (keys p \<union> keys q))" .
    qed (rule dgrad_set_leI, simp)
  qed
qed

lemma dgrad_p_set_le_snd_crit_pair:
  assumes "dickson_grading d"
  shows "dgrad_p_set_le d {snd (crit_pair p q)} {p, q}"
  by (simp add: crit_pair_swap[of p] insert_commute[of p q], rule dgrad_p_set_le_fst_crit_pair, fact)

lemma dgrad_p_set_closed_fst_crit_pair:
  assumes "dickson_grading d" and "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m"
  shows "fst (crit_pair p q) \<in> dgrad_p_set d m"
proof -
  from dgrad_p_set_le_fst_crit_pair[OF assms(1)] have "{fst (crit_pair p q)} \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from assms(2, 3) show "{p, q} \<subseteq> dgrad_p_set d m" by simp
  qed
  thus ?thesis by simp
qed

lemma dgrad_p_set_closed_snd_crit_pair:
  assumes "dickson_grading d" and "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m"
  shows "snd (crit_pair p q) \<in> dgrad_p_set d m"
  by (simp add: crit_pair_swap[of p q], rule dgrad_p_set_closed_fst_crit_pair, fact+)

lemma fst_crit_pair_below_lcs:
  "fst (crit_pair p q) \<prec>\<^sub>p monomial 1 (term_of_pair (lcs (lp p) (lp q), component_of_term (lt p)))"
proof (cases "tail p = 0")
  case True
  thus ?thesis by (simp add: crit_pair_def ord_strict_p_monomial_iff)
next
  case False
  let ?t1 = "lp p"
  let ?t2 = "lp q"
  from False have "p \<noteq> 0" by auto
  hence "lc p \<noteq> 0" by (rule lc_not_0)
  hence "1 / lc p \<noteq> 0" by simp
  from this False have "lt (monom_mult (1 / lc p) (lcs ?t1 ?t2 - ?t1) (tail p)) =
                        (lcs ?t1 ?t2 - ?t1) \<oplus> lt (tail p)"
    by (rule lt_monom_mult)
  also from lt_tail[OF False] have "... \<prec>\<^sub>t (lcs ?t1 ?t2 - ?t1) \<oplus> lt p"
    by (rule splus_mono_strict)
  also from adds_lcs have "... = term_of_pair (lcs ?t1 ?t2, component_of_term (lt p))"
    by (simp add: adds_lcs adds_minus splus_def)
  finally show ?thesis by (auto simp add: crit_pair_def ord_strict_p_monomial_iff)
qed

lemma snd_crit_pair_below_lcs:
  "snd (crit_pair p q) \<prec>\<^sub>p monomial 1 (term_of_pair (lcs (lp p) (lp q), component_of_term (lt p)))"
proof (cases "component_of_term (lt p) = component_of_term (lt q)")
  case True
  show ?thesis
    by (simp add: True crit_pair_swap[of p] lcs_comm[of "lp p"], fact fst_crit_pair_below_lcs)
next
  case False
  show ?thesis by (simp add: crit_pair_def False ord_strict_p_monomial_iff)
qed

lemma crit_pair_cbelow_same:
  assumes "dickson_grading d" and "p \<in> dgrad_p_set d m"
  shows "crit_pair_cbelow_on d m F p p"
proof (simp add: crit_pair_cbelow_on_def crit_pair_same cbelow_on_def term_simps, intro disjI1 conjI)
  from assms(1) assms(2) assms(2) show "snd (crit_pair p p) \<in> dgrad_p_set d m"
    by (rule dgrad_p_set_closed_snd_crit_pair)
next
  from snd_crit_pair_below_lcs[of p p] show "snd (crit_pair p p) \<prec>\<^sub>p monomial 1 (lt p)"
    by (simp add: term_simps)
qed

lemma crit_pair_cbelow_distinct_component:
  assumes "component_of_term (lt p) \<noteq> component_of_term (lt q)"
  shows "crit_pair_cbelow_on d m F p q"
  by (simp add: crit_pair_cbelow_on_def crit_pair_def assms cbelow_on_def
      ord_strict_p_monomial_iff zero_in_dgrad_p_set)

lemma crit_pair_cbelow_sym:
  assumes "crit_pair_cbelow_on d m F p q"
  shows "crit_pair_cbelow_on d m F q p"
proof (cases "component_of_term (lt q) = component_of_term (lt p)")
  case True
  from assms show ?thesis
  proof (simp add: crit_pair_cbelow_on_def crit_pair_swap[of p q] lcs_comm True,
         elim cbelow_on_symmetric)
    show "symp (\<lambda>a b. red F a b \<or> red F b a)" by (simp add: symp_def)
  qed
next
  case False
  thus ?thesis by (rule crit_pair_cbelow_distinct_component)
qed

lemma crit_pair_cs_imp_crit_pair_cbelow_on:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_p_set d m" and "p \<in> dgrad_p_set d m"
    and "q \<in> dgrad_p_set d m"
    and "relation.cs (red F) (fst (crit_pair p q)) (snd (crit_pair p q))"
  shows "crit_pair_cbelow_on d m F p q"
proof -
  from assms(1) have "relation_order (red F) (\<prec>\<^sub>p) (dgrad_p_set d m)" by (rule is_relation_order_red)
  moreover have "relation.dw_closed (red F) (dgrad_p_set d m)"
    by (rule relation.dw_closedI, rule dgrad_p_set_closed_red, rule assms(1), rule assms(2))
  moreover note assms(5)
  moreover from assms(1) assms(3) assms(4) have "fst (crit_pair p q) \<in> dgrad_p_set d m"
    by (rule dgrad_p_set_closed_fst_crit_pair)
  moreover from assms(1) assms(3) assms(4) have "snd (crit_pair p q) \<in> dgrad_p_set d m"
    by (rule dgrad_p_set_closed_snd_crit_pair)
  moreover note fst_crit_pair_below_lcs snd_crit_pair_below_lcs
  ultimately show ?thesis unfolding crit_pair_cbelow_on_def by (rule relation_order.cs_implies_cbelow_on)
qed

lemma crit_pair_cbelow_mono:
  assumes "crit_pair_cbelow_on d m F p q" and "F \<subseteq> G"
  shows "crit_pair_cbelow_on d m G p q"
  using assms(1) unfolding crit_pair_cbelow_on_def
proof (induct rule: cbelow_on_induct)
  case base
  show ?case by (simp add: cbelow_on_def, intro disjI1 conjI, fact+)
next
  case (step b c)
  from step(2) have "red G b c \<or> red G c b" using red_subset[OF _ assms(2)] by blast
  from step(5) step(3) this step(4) show ?case ..
qed

lemma lcs_red_single_fst_crit_pair:
  assumes "p \<noteq> 0" and "component_of_term (lt p) = component_of_term (lt q)"
  defines "t1 \<equiv> lp p"
  defines "t2 \<equiv> lp q"
  shows "red_single (monomial (- 1) (term_of_pair (lcs t1 t2, component_of_term (lt p))))
                    (fst (crit_pair p q)) p (lcs t1 t2 - t1)"
proof -
  let ?l = "term_of_pair (lcs t1 t2, component_of_term (lt p))"
  from assms(1) have "lc p \<noteq> 0" by (rule lc_not_0)
  have "lt p adds\<^sub>t ?l" by (simp add: adds_lcs adds_term_def t1_def term_simps)
  hence eq1: "(lcs t1 t2 - t1) \<oplus> lt p = ?l"
    by (simp add: adds_lcs adds_minus splus_def t1_def)
  with assms(1) show ?thesis
  proof (simp add: crit_pair_def red_single_def assms(2))
    have eq2: "monomial (- 1) ?l = monom_mult (- (1 / lc p)) (lcs t1 t2 - t1) (monomial (lc p) (lt p))"
      by (simp add: monom_mult_monomial eq1 \<open>lc p \<noteq> 0\<close>)
    show "monom_mult (1 / lc p) (lcs (lp p) (lp q) - lp p) (tail p) =
          monomial (- 1) (term_of_pair (lcs t1 t2, component_of_term (lt q))) - monom_mult (- (1 / lc p)) (lcs t1 t2 - t1) p"
      apply (simp add: t1_def t2_def monom_mult_dist_right_minus tail_alt_2 monom_mult_uminus_left)
      by (metis assms(2) eq2 monom_mult_uminus_left t1_def t2_def)
  qed
qed

corollary lcs_red_single_snd_crit_pair:
  assumes "q \<noteq> 0" and "component_of_term (lt p) = component_of_term (lt q)"
  defines "t1 \<equiv> lp p"
  defines "t2 \<equiv> lp q"
  shows "red_single (monomial (- 1) (term_of_pair (lcs t1 t2, component_of_term (lt p))))
                    (snd (crit_pair p q)) q (lcs t1 t2 - t2)"
  by (simp add: crit_pair_swap[of p q] lcs_comm[of "lp p"] assms(2) t1_def t2_def,
        rule lcs_red_single_fst_crit_pair, simp_all add: assms(1, 2))

lemma GB_imp_crit_pair_cbelow_dgrad_p_set:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_p_set d m" and "is_Groebner_basis F"
  assumes "p \<in> F" and "q \<in> F" and "p \<noteq> 0" and "q \<noteq> 0"
  shows "crit_pair_cbelow_on d m F p q"
proof (cases "component_of_term (lt p) = component_of_term (lt q)")
  case True
  from assms(1, 2) show ?thesis
  proof (rule crit_pair_cs_imp_crit_pair_cbelow_on)
    from assms(4, 2) show "p \<in> dgrad_p_set d m" ..
  next
    from assms(5, 2) show "q \<in> dgrad_p_set d m" ..
  next
    let ?cp = "crit_pair p q"
    let ?l = "monomial (- 1) (term_of_pair (lcs (lp p) (lp q), component_of_term (lt p)))"
    from assms(4) lcs_red_single_fst_crit_pair[OF assms(6) True] have "red F ?l (fst ?cp)"
      by (rule red_setI)
    hence 1: "(red F)\<^sup>*\<^sup>* ?l (fst ?cp)" ..
    from assms(5) lcs_red_single_snd_crit_pair[OF assms(7) True] have "red F ?l (snd ?cp)"
      by (rule red_setI)
    hence 2: "(red F)\<^sup>*\<^sup>* ?l (snd ?cp)" ..
    from assms(3) have "relation.is_confluent_on (red F) UNIV"
      by (simp only: is_Groebner_basis_def relation.confluence_equiv_ChurchRosser[symmetric]
          relation.is_confluent_def)
    from this 1 2 show "relation.cs (red F) (fst ?cp) (snd ?cp)"
      by (simp add: relation.is_confluent_on_def)
  qed
next
  case False
  thus ?thesis by (rule crit_pair_cbelow_distinct_component)
qed

lemma spoly_alt:
  assumes "p \<noteq> 0" and "q \<noteq> 0"
  shows "spoly p q = fst (crit_pair p q) - snd (crit_pair p q)"
proof (cases "component_of_term (lt p) = component_of_term (lt q)")
  case ec: True
  show ?thesis
  proof (rule poly_mapping_eqI, simp only: lookup_minus)
    fix v
    define t1 where "t1 = lp p"
    define t2 where "t2 = lp q"
    let ?l = "lcs t1 t2"
    let ?lv = "term_of_pair (?l, component_of_term (lt p))"
    let ?cp = "crit_pair p q"
    let ?a = "\<lambda>x. monom_mult (1 / lc p) (?l - t1) x"
    let ?b = "\<lambda>x. monom_mult (1 / lc q) (?l - t2) x"
    have l_1: "(?l - t1) \<oplus> lt p = ?lv" by (simp add: adds_lcs adds_minus splus_def t1_def)
    have l_2: "(?l - t2) \<oplus> lt q = ?lv" by (simp add: ec adds_lcs_2 adds_minus splus_def t2_def)
    show "lookup (spoly p q) v = lookup (fst ?cp) v - lookup (snd ?cp) v"
    proof (cases "v = ?lv")
      case True
      have v_1: "v = (?l - t1) \<oplus> lt p" by (simp add: True l_1)
      from \<open>p \<noteq> 0\<close> have "lt p \<in> keys p" by (rule lt_in_keys)
      hence v_2: "v = (?l - t2) \<oplus> lt q" by (simp add: True l_2)
      from \<open>q \<noteq> 0\<close> have "lt q \<in> keys q" by (rule lt_in_keys)
      from \<open>lt p \<in> keys p\<close> have "lookup (?a p) v = 1"
        by (simp add: in_keys_iff v_1 lookup_monom_mult lc_def term_simps)
      also from \<open>lt q \<in> keys q\<close> have "... = lookup (?b q) v"
        by (simp add: in_keys_iff v_2 lookup_monom_mult lc_def term_simps)
      finally have "lookup (spoly p q) v = 0"
        by (simp add: spoly_def ec Let_def t1_def t2_def lookup_minus lc_def)
      moreover have "lookup (fst ?cp) v = 0"
        by (simp add: crit_pair_def ec v_1 lookup_monom_mult t1_def t2_def term_simps,
            simp only: not_in_keys_iff_lookup_eq_zero[symmetric] keys_tail, simp)
      moreover have "lookup (snd ?cp) v = 0"
        by (simp add: crit_pair_def ec v_2 lookup_monom_mult t1_def t2_def term_simps,
            simp only: not_in_keys_iff_lookup_eq_zero[symmetric] keys_tail, simp)
      ultimately show ?thesis by simp
    next
      case False
      have "lookup (?a (tail p)) v = lookup (?a p) v"
      proof (cases "?l - t1 adds\<^sub>p v")
        case True
        then obtain u where v: "v = (?l - t1) \<oplus> u" ..
        have "u \<noteq> lt p"
        proof
          assume "u = lt p"
          hence "v = ?lv" by (simp add: v l_1)
          with \<open>v \<noteq> ?lv\<close> show False ..
        qed
        thus ?thesis by (simp add: v lookup_monom_mult lookup_tail_2 term_simps)
      next
        case False
        thus ?thesis by (simp add: lookup_monom_mult)
      qed
      moreover have "lookup (?b (tail q)) v = lookup (?b q) v"
      proof (cases "?l - t2 adds\<^sub>p v")
        case True
        then obtain u where v: "v = (?l - t2) \<oplus> u" ..
        have "u \<noteq> lt q"
        proof
          assume "u = lt q"
          hence "v = ?lv" by (simp add: v l_2)
          with \<open>v \<noteq> ?lv\<close> show False ..
        qed
        thus ?thesis by (simp add: v lookup_monom_mult lookup_tail_2 term_simps)
      next
        case False
        thus ?thesis by (simp add: lookup_monom_mult)
      qed
      ultimately show ?thesis
        by (simp add: ec spoly_def crit_pair_def lookup_minus t1_def t2_def Let_def lc_def)
    qed
  qed
next
  case False
  show ?thesis by (simp add: spoly_def crit_pair_def False)
qed

lemma spoly_same: "spoly p p = 0"
  by (simp add: spoly_def)

lemma spoly_swap: "spoly p q = - spoly q p"
  by (simp add: spoly_def lcs_comm Let_def)

lemma spoly_red_zero_imp_crit_pair_cbelow_on:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_p_set d m" and "p \<in> dgrad_p_set d m"
    and "q \<in> dgrad_p_set d m" and "p \<noteq> 0" and "q \<noteq> 0" and "(red F)\<^sup>*\<^sup>* (spoly p q) 0"
  shows "crit_pair_cbelow_on d m F p q"
proof -
  from assms(7) have "relation.cs (red F) (fst (crit_pair p q)) (snd (crit_pair p q))"
    unfolding spoly_alt[OF assms(5) assms(6)] by (rule red_diff_rtrancl_cs)
  with assms(1) assms(2) assms(3) assms(4) show ?thesis by (rule crit_pair_cs_imp_crit_pair_cbelow_on)
qed

lemma dgrad_p_set_le_spoly_zero: "dgrad_p_set_le d {spoly p 0} {p}"
proof (simp add: term_simps spoly_def lt_def[of 0] lcs_comm lcs_zero dgrad_p_set_le_def Keys_insert
      Let_def min_term_def lc_def[symmetric], intro conjI impI dgrad_set_leI)
  fix s
  assume "s \<in> pp_of_term ` keys (monom_mult (1 / lc p) 0 p)"
  then obtain u where "u \<in> keys (monom_mult (1 / lc p) 0 p)" and "s = pp_of_term u" ..
  from this(1) keys_monom_mult_subset have "u \<in> (\<oplus>) 0 ` keys p" ..
  hence "u \<in> keys p" by (simp add: image_iff term_simps)
  hence "s \<in> pp_of_term ` keys p" by (simp add: \<open>s = pp_of_term u\<close>)
  moreover have "d s \<le> d s" ..
  ultimately show "\<exists>t\<in>pp_of_term ` keys p. d s \<le> d t" ..
qed simp

lemma dgrad_p_set_le_spoly:
  assumes "dickson_grading d"
  shows "dgrad_p_set_le d {spoly p q} {p, q}"
proof (cases "p = 0")
  case True
  have "dgrad_p_set_le d {spoly p q} {spoly q 0}" unfolding True spoly_swap[of 0 q]
    by (fact dgrad_p_set_le_uminus)
  also have "dgrad_p_set_le d ... {q}" by (fact dgrad_p_set_le_spoly_zero)
  also have "dgrad_p_set_le d ... {p, q}" by (rule dgrad_p_set_le_subset, simp)
  finally show ?thesis .
next
  case False
  show ?thesis
  proof (cases "q = 0")
    case True
    have "dgrad_p_set_le d {spoly p q} {p}" unfolding True by (fact dgrad_p_set_le_spoly_zero)
    also have "dgrad_p_set_le d ... {p, q}" by (rule dgrad_p_set_le_subset, simp)
    finally show ?thesis .
  next
    case False
    have "dgrad_p_set_le d {spoly p q} {fst (crit_pair p q), snd (crit_pair p q)}"
      unfolding spoly_alt[OF \<open>p \<noteq> 0\<close> False] by (rule dgrad_p_set_le_minus)
    also have "dgrad_p_set_le d ... {p, q}"
    proof (rule dgrad_p_set_leI_insert)
      from assms show "dgrad_p_set_le d {fst (crit_pair p q)} {p, q}"
        by (rule dgrad_p_set_le_fst_crit_pair)
    next
      from assms show "dgrad_p_set_le d {snd (crit_pair p q)} {p, q}"
        by (rule dgrad_p_set_le_snd_crit_pair)
    qed
    finally show ?thesis .
  qed
qed

lemma dgrad_p_set_closed_spoly:
  assumes "dickson_grading d" and "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m"
  shows "spoly p q \<in> dgrad_p_set d m"
proof -
  from dgrad_p_set_le_spoly[OF assms(1)] have "{spoly p q} \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from assms(2, 3) show "{p, q} \<subseteq> dgrad_p_set d m" by simp
  qed
  thus ?thesis by simp
qed

lemma components_spoly_subset: "component_of_term ` keys (spoly p q) \<subseteq> component_of_term ` Keys {p, q}"
  unfolding spoly_def Let_def
proof (split if_split, intro conjI impI)
  define c where "c = (1 / lookup p (lt p))"
  define d where "d = (1 / lookup q (lt q))"
  define s where "s = lcs (lp p) (lp q) - lp p"
  define t where "t = lcs (lp p) (lp q) - lp q"
  show "component_of_term ` keys (monom_mult c s p - monom_mult d t q) \<subseteq> component_of_term ` Keys {p, q}"
  proof
    fix k
    assume "k \<in> component_of_term ` keys (monom_mult c s p - monom_mult d t q)"
    then obtain v where "v \<in> keys (monom_mult c s p - monom_mult d t q)" and k: "k = component_of_term v" ..
    from this(1) keys_minus have "v \<in> keys (monom_mult c s p) \<union> keys (monom_mult d t q)" ..
    thus "k \<in> component_of_term ` Keys {p, q}"
    proof
      assume "v \<in> keys (monom_mult c s p)"
      from this keys_monom_mult_subset have "v \<in> (\<oplus>) s ` keys p" ..
      then obtain u where "u \<in> keys p" and v: "v = s \<oplus> u" ..
      have "u \<in> Keys {p, q}" by (rule in_KeysI, fact, simp)
      moreover have "k = component_of_term u" by (simp add: v k term_simps)
      ultimately show ?thesis by simp
    next
      assume "v \<in> keys (monom_mult d t q)"
      from this keys_monom_mult_subset have "v \<in> (\<oplus>) t ` keys q" ..
      then obtain u where "u \<in> keys q" and v: "v = t \<oplus> u" ..
      have "u \<in> Keys {p, q}" by (rule in_KeysI, fact, simp)
      moreover have "k = component_of_term u" by (simp add: v k term_simps)
      ultimately show ?thesis by simp
    qed
  qed
qed simp

lemma pmdl_closed_spoly:
  assumes "p \<in> pmdl F" and "q \<in> pmdl F"
  shows "spoly p q \<in> pmdl F"
proof (cases "component_of_term (lt p) = component_of_term (lt q)")
  case True
  show ?thesis
    by (simp add: spoly_def True Let_def, rule pmdl.span_diff,
        (rule pmdl_closed_monom_mult, fact)+)
next
  case False
  show ?thesis by (simp add: spoly_def False pmdl.span_zero)
qed

subsection \<open>Buchberger's Theorem\<close>

text \<open>Before proving the main theorem of Gr\"obner bases theory for S-polynomials, as is usually done
  in textbooks, we first prove it for critical pairs: a set \<open>F\<close> yields a confluent reduction
  relation if the critical pairs of all \<open>p \<in> F\<close> and \<open>q \<in> F\<close> can be connected below
  the least common sum of the leading power-products of \<open>p\<close> and \<open>q\<close>.
  The reason why we proceed in this way is that it becomes much easier to prove the correctness of
  Buchberger's second criterion for avoiding useless pairs.\<close>

lemma crit_pair_cbelow_imp_confluent_dgrad_p_set:
  assumes dg: "dickson_grading d" and "F \<subseteq> dgrad_p_set d m"
  assumes main: "\<And>p q. p \<in> F \<Longrightarrow> q \<in> F \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m F p q"
  shows "relation.is_confluent_on (red F) (dgrad_p_set d m)"
proof -
  let ?A = "dgrad_p_set d m"
  let ?R = "red F"
  let ?RS = "\<lambda>a b. red F a b \<or> red F b a"
  let ?ord = "(\<prec>\<^sub>p)"
  from dg have ro: "Confluence.relation_order ?R ?ord ?A"
    by (rule is_relation_order_red)
  have dw: "relation.dw_closed ?R ?A"
    by (rule relation.dw_closedI, rule dgrad_p_set_closed_red, rule dg, rule assms(2))
  show ?thesis
  proof (rule relation_order.loc_connectivity_implies_confluence, fact ro)
    show "is_loc_connective_on ?A ?ord ?R" unfolding is_loc_connective_on_def
    proof (intro ballI allI impI)
      fix a b1 b2 :: "'t \<Rightarrow>\<^sub>0 'b"
      assume "a \<in> ?A"
      assume "?R a b1 \<and> ?R a b2"
      hence "?R a b1" and "?R a b2" by simp_all
      hence "b1 \<in> ?A" and "b2 \<in> ?A" and "?ord b1 a" and "?ord b2 a"
        using red_ord dgrad_p_set_closed_red[OF dg assms(2) \<open>a \<in> ?A\<close>] by blast+
      from this(1) this(2) have "b1 - b2 \<in> ?A" by (rule dgrad_p_set_closed_minus)
      from \<open>red F a b1\<close> obtain f1 and t1 where "f1 \<in> F" and r1: "red_single a b1 f1 t1" by (rule red_setE)
      from \<open>red F a b2\<close> obtain f2 and t2 where "f2 \<in> F" and r2: "red_single a b2 f2 t2" by (rule red_setE)
      from r1 r2 have "f1 \<noteq> 0" and "f2 \<noteq> 0" by (simp_all add: red_single_def)
      hence lc1: "lc f1 \<noteq> 0" and lc2: "lc f2 \<noteq> 0" using lc_not_0 by auto
      show "cbelow_on ?A ?ord a (\<lambda>a b. ?R a b \<or> ?R b a) b1 b2"
      proof (cases "t1 \<oplus> lt f1 = t2 \<oplus> lt f2")
        case False
        from confluent_distinct[OF r1 r2 False \<open>f1 \<in> F\<close> \<open>f2 \<in> F\<close>] obtain s
          where s1: "(red F)\<^sup>*\<^sup>* b1 s" and s2: "(red F)\<^sup>*\<^sup>* b2 s" .
        have "relation.cs ?R b1 b2" unfolding relation.cs_def by (intro exI conjI, fact s1, fact s2)
        from ro dw this \<open>b1 \<in> ?A\<close> \<open>b2 \<in> ?A\<close> \<open>?ord b1 a\<close> \<open>?ord b2 a\<close> show ?thesis
          by (rule relation_order.cs_implies_cbelow_on)
      next
        case True
        hence ec: "component_of_term (lt f1) = component_of_term (lt f2)"
          by (metis component_of_term_splus)
        let ?l1 = "lp f1"
        let ?l2 = "lp f2"
        define v where "v \<equiv> t2 \<oplus> lt f2"
        define l where "l \<equiv> lcs ?l1 ?l2"
        define a' where "a' = except a {v}"
        define ma where "ma = monomial (lookup a v) v"
        have v_alt: "v = t1 \<oplus> lt f1" by (simp only: True v_def)
        have "a = ma + a'" unfolding ma_def a'_def by (fact plus_except)
        have comp_f1: "component_of_term (lt f1) = component_of_term v" by (simp add: v_alt term_simps)

        have "?l1 adds l" unfolding l_def by (rule adds_lcs)
        have "?l2 adds l" unfolding l_def by (rule adds_lcs_2)
        have "?l1 adds\<^sub>p (t1 \<oplus> lt f1)" by (simp add: adds_pp_splus term_simps)
        hence "?l1 adds\<^sub>p v" by (simp add: v_alt)
        have "?l2 adds\<^sub>p v" by (simp add: v_def adds_pp_splus term_simps)
        from \<open>?l1 adds\<^sub>p v\<close> \<open>?l2 adds\<^sub>p v\<close> have "l adds\<^sub>p v" by (simp add: l_def adds_pp_def lcs_adds)
        have "pp_of_term (v \<ominus> ?l1) = t1" by (simp add: v_alt term_simps)
        with \<open>l adds\<^sub>p v\<close> \<open>?l1 adds l\<close> have tf1': "pp_of_term ((l - ?l1) \<oplus> (v \<ominus> l)) = t1"
          by (simp add: minus_splus_sminus_cancel)
        hence tf1: "((pp_of_term v) - l) + (l - ?l1) = t1" by (simp add: add.commute term_simps)
        have "pp_of_term (v \<ominus> ?l2) = t2" by (simp add: v_def term_simps)
        with \<open>l adds\<^sub>p v\<close> \<open>?l2 adds l\<close> have tf2': "pp_of_term ((l - ?l2) \<oplus> (v \<ominus> l)) = t2"
          by (simp add: minus_splus_sminus_cancel)
        hence tf2: "((pp_of_term v) - l) + (l - ?l2) = t2" by (simp add: add.commute term_simps)
        let ?ca = "lookup a v"
        let ?v = "pp_of_term v - l"
        have "?v + l = pp_of_term v" using \<open>l adds\<^sub>p v\<close> adds_minus adds_pp_def by blast
        from tf1' have "?v adds t1" unfolding pp_of_term_splus add.commute[of "l - ?l1"] pp_of_term_sminus
          using addsI by blast
        with dg have "d ?v \<le> d t1" by (rule dickson_grading_adds_imp_le)
        also from dg \<open>a \<in> ?A\<close> r1 have "... \<le> m" by (rule dgrad_p_set_red_single_pp)
        finally have "d ?v \<le> m" .
        from r2 have "?ca \<noteq> 0" by (simp add: red_single_def v_def)
        hence "- ?ca \<noteq> 0" by simp

        (* b1 *)
        from r1 have "b1 = a - monom_mult (?ca / lc f1) t1 f1" by (simp add: red_single_def v_alt)
        also have "... = monom_mult (- ?ca) ?v (fst (crit_pair f1 f2)) + a'"
        proof (simp add: a'_def ec crit_pair_def l_def[symmetric] monom_mult_assoc tf1,
              rule poly_mapping_eqI, simp add: lookup_add lookup_minus)
          fix u
          show "lookup a u - lookup (monom_mult (?ca / lc f1) t1 f1) u =
                lookup (monom_mult (- (?ca / lc f1)) t1 (tail f1)) u + lookup (except a {v}) u"
          proof (cases "u = v")
            case True
            show ?thesis
              by (simp add: True lookup_except v_alt lookup_monom_mult lookup_tail_2 lc_def[symmetric] lc1 term_simps)
          next
            case False
            hence "u \<notin> {v}" by simp
            moreover
            {
              assume "t1 adds\<^sub>p u"
              hence "t1 \<oplus> (u \<ominus> t1) = u" by (simp add: adds_pp_sminus)
              hence "u \<ominus> t1 \<noteq> lt f1" using False v_alt by auto
              hence "lookup f1 (u \<ominus> t1) = lookup (tail f1) (u \<ominus> t1)" by (simp add: lookup_tail_2)
            }
            ultimately show ?thesis using False by (simp add: lookup_except lookup_monom_mult)
          qed
        qed
        finally have b1: "b1 = monom_mult (- ?ca) ?v (fst (crit_pair f1 f2)) + a'" .

        (* b2 *)
        from r2 have "b2 = a - monom_mult (?ca / lc f2) t2 f2"
          by (simp add: red_single_def v_def True)
        also have "... = monom_mult (- ?ca) ?v (snd (crit_pair f1 f2)) + a'"
        proof (simp add: a'_def ec crit_pair_def l_def[symmetric] monom_mult_assoc tf2,
              rule poly_mapping_eqI, simp add: lookup_add lookup_minus)
          fix u
          show "lookup a u - lookup (monom_mult (?ca / lc f2) t2 f2) u =
                lookup (monom_mult (- (?ca / lc f2)) t2 (tail f2)) u + lookup (except a {v}) u"
          proof (cases "u = v")
            case True
            show ?thesis
              by (simp add: True lookup_except v_def lookup_monom_mult lookup_tail_2 lc_def[symmetric] lc2 term_simps)
          next
            case False
            hence "u \<notin> {v}" by simp
            moreover
            {
              assume "t2 adds\<^sub>p u"
              hence "t2 \<oplus> (u \<ominus> t2) = u" by (simp add: adds_pp_sminus)
              hence "u \<ominus> t2 \<noteq> lt f2" using False v_def by auto
              hence "lookup f2 (u \<ominus> t2) = lookup (tail f2) (u \<ominus> t2)" by (simp add: lookup_tail_2)
            }
            ultimately show ?thesis using False by (simp add: lookup_except lookup_monom_mult)
          qed
        qed
        finally have b2: "b2 = monom_mult (- ?ca) ?v (snd (crit_pair f1 f2)) + a'" .

        let ?lv = "term_of_pair (l, component_of_term (lt f1))"
        from \<open>f1 \<in> F\<close> \<open>f2 \<in> F\<close> \<open>f1 \<noteq> 0\<close> \<open>f2 \<noteq> 0\<close> have "crit_pair_cbelow_on d m F f1 f2" by (rule main)
        hence "cbelow_on ?A ?ord (monomial 1 ?lv) ?RS (fst (crit_pair f1 f2)) (snd (crit_pair f1 f2))"
          by (simp only: crit_pair_cbelow_on_def l_def)
        with dg assms (2) \<open>d ?v \<le> m\<close> \<open>- ?ca \<noteq> 0\<close>
        have "cbelow_on ?A ?ord (monom_mult (- ?ca) ?v (monomial 1 ?lv)) ?RS
              (monom_mult (- ?ca) ?v (fst (crit_pair f1 f2)))
              (monom_mult (- ?ca) ?v (snd (crit_pair f1 f2)))"
          by (rule cbelow_on_monom_mult)
        hence "cbelow_on ?A ?ord (monomial (- ?ca) v) ?RS
              (monom_mult (- ?ca) ?v (fst (crit_pair f1 f2)))
              (monom_mult (- ?ca) ?v (snd (crit_pair f1 f2)))"
          by (simp add: monom_mult_monomial \<open>(pp_of_term v - l) + l = pp_of_term v\<close> splus_def comp_f1 term_simps)
        with \<open>?ca \<noteq> 0\<close> have "cbelow_on ?A ?ord (monomial ?ca (0 \<oplus> v)) ?RS
              (monom_mult (-?ca) ?v (fst (crit_pair f1 f2))) (monom_mult (-?ca) ?v (snd (crit_pair f1 f2)))"
          by (rule cbelow_on_monom_mult_monomial)
        hence "cbelow_on ?A ?ord ma ?RS
              (monom_mult (-?ca) ?v (fst (crit_pair f1 f2))) (monom_mult (-?ca) ?v (snd (crit_pair f1 f2)))"
          by (simp add: ma_def term_simps)
        with dg assms(2) _ _
        show "cbelow_on ?A ?ord a ?RS b1 b2" unfolding \<open>a = ma + a'\<close> b1 b2
        proof (rule cbelow_on_plus)
          show "a' \<in> ?A"
            by (rule, simp add: a'_def keys_except, erule conjE, intro dgrad_p_setD,
                rule \<open>a \<in> dgrad_p_set d m\<close>)
        next
          show "keys a' \<inter> keys ma = {}" by (simp add: ma_def a'_def keys_except)
        qed
      qed
    qed
  qed fact
qed

corollary crit_pair_cbelow_imp_GB_dgrad_p_set:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_p_set d m"
  assumes "\<And>p q. p \<in> F \<Longrightarrow> q \<in> F \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m F p q"
  shows "is_Groebner_basis F"
  unfolding is_Groebner_basis_def
proof (rule relation.confluence_implies_ChurchRosser,
      simp only: relation.is_confluent_def relation.is_confluent_on_def, intro ballI allI impI)
  fix a b1 b2
  assume a: "(red F)\<^sup>*\<^sup>* a b1 \<and> (red F)\<^sup>*\<^sup>* a b2"
  from assms(2) obtain n where "m \<le> n" and "a \<in> dgrad_p_set d n" and "F \<subseteq> dgrad_p_set d n"
    by (rule dgrad_p_set_insert)
  {
    fix p q
    assume "p \<in> F" and "q \<in> F" and "p \<noteq> 0" and "q \<noteq> 0"
    hence "crit_pair_cbelow_on d m F p q" by (rule assms(3))
    from this dgrad_p_set_subset[OF \<open>m \<le> n\<close>] have "crit_pair_cbelow_on d n F p q"
      unfolding crit_pair_cbelow_on_def by (rule cbelow_on_mono)
  }
  with assms(1) \<open>F \<subseteq> dgrad_p_set d n\<close> have "relation.is_confluent_on (red F) (dgrad_p_set d n)"
    by (rule crit_pair_cbelow_imp_confluent_dgrad_p_set)
  from this \<open>a \<in> dgrad_p_set d n\<close> have "\<forall>b1 b2. (red F)\<^sup>*\<^sup>* a b1 \<and> (red F)\<^sup>*\<^sup>* a b2 \<longrightarrow> relation.cs (red F) b1 b2"
    unfolding relation.is_confluent_on_def ..
  with a show "relation.cs (red F) b1 b2" by blast
qed

corollary Buchberger_criterion_dgrad_p_set:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_p_set d m"
  assumes "\<And>p q. p \<in> F \<Longrightarrow> q \<in> F \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> p \<noteq> q \<Longrightarrow>
                      component_of_term (lt p) = component_of_term (lt q) \<Longrightarrow> (red F)\<^sup>*\<^sup>* (spoly p q) 0"
  shows "is_Groebner_basis F"
  using assms(1) assms(2)
proof (rule crit_pair_cbelow_imp_GB_dgrad_p_set)
  fix p q
  assume "p \<in> F" and "q \<in> F" and "p \<noteq> 0" and "q \<noteq> 0"
  from this(1, 2) assms(2) have p: "p \<in> dgrad_p_set d m" and q: "q \<in> dgrad_p_set d m" by auto
  show "crit_pair_cbelow_on d m F p q"
  proof (cases "p = q")
    case True
    from assms(1) q show ?thesis unfolding True by (rule crit_pair_cbelow_same)
  next
    case False
    show ?thesis
    proof (cases "component_of_term (lt p) = component_of_term (lt q)")
      case True
      from assms(1) assms(2) p q \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> show "crit_pair_cbelow_on d m F p q"
      proof (rule spoly_red_zero_imp_crit_pair_cbelow_on)
        from \<open>p \<in> F\<close> \<open>q \<in> F\<close> \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> \<open>p \<noteq> q\<close> True show "(red F)\<^sup>*\<^sup>* (spoly p q) 0"
          by (rule assms(3))
      qed
    next
      case False
      thus ?thesis by (rule crit_pair_cbelow_distinct_component)
    qed
  qed
qed

lemmas Buchberger_criterion_finite = Buchberger_criterion_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

lemma (in ordered_term) GB_imp_zero_reducibility:
  assumes "is_Groebner_basis G" and "f \<in> pmdl G"
  shows "(red G)\<^sup>*\<^sup>* f 0"
proof -
  from in_pmdl_srtc[OF \<open>f \<in> pmdl G\<close>] \<open>is_Groebner_basis G\<close> have "relation.cs (red G) f 0"
    unfolding is_Groebner_basis_def relation.is_ChurchRosser_def by simp
  then obtain s where rfs: "(red G)\<^sup>*\<^sup>* f s" and r0s: "(red G)\<^sup>*\<^sup>* 0 s" unfolding relation.cs_def by auto
  from rtrancl_0[OF r0s] and rfs show ?thesis by simp
qed

lemma (in ordered_term) GB_imp_reducibility:
  assumes "is_Groebner_basis G" and "f \<noteq> 0" and "f \<in> pmdl G"
  shows "is_red G f"
  using assms by (meson GB_imp_zero_reducibility is_red_def relation.rtrancl_is_final)

lemma is_Groebner_basis_empty: "is_Groebner_basis {}"
  by (rule Buchberger_criterion_finite, rule, simp)

lemma is_Groebner_basis_singleton: "is_Groebner_basis {f}"
  by (rule Buchberger_criterion_finite, simp, simp add: spoly_same)

subsection \<open>Buchberger's Criteria for Avoiding Useless Pairs\<close>

text \<open>Unfortunately, the product criterion is only applicable to scalar polynomials.\<close>
lemma (in gd_powerprod) product_criterion:
  assumes "dickson_grading d" and "F \<subseteq> punit.dgrad_p_set d m" and "p \<in> F" and "q \<in> F"
    and "p \<noteq> 0" and "q \<noteq> 0" and "gcs (punit.lt p) (punit.lt q) = 0"
  shows "punit.crit_pair_cbelow_on d m F p q"
proof -
  let ?lt = "punit.lt p"
  let ?lq = "punit.lt q"
  let ?l = "lcs ?lt ?lq"
  define s where "s = punit.monom_mult (- 1 / (punit.lc p * punit.lc q)) 0 (punit.tail p * punit.tail q)"
  from assms(7) have "?l = ?lt + ?lq" by (metis add_cancel_left_left gcs_plus_lcs)
  hence "?l - ?lt = ?lq" and "?l - ?lq = ?lt" by simp_all

  have "(punit.red {q})\<^sup>*\<^sup>* (punit.tail p * (monomial (1 / punit.lc p) (punit.lt q)))
        (punit.monom_mult (- (1 / punit.lc p) / punit.lc q) 0 (punit.tail p * punit.tail q))"
    unfolding punit_mult_scalar[symmetric] using \<open>q \<noteq> 0\<close> by (rule punit.red_mult_scalar_lt)
  moreover have "punit.monom_mult (1 / punit.lc p) (punit.lt q) (punit.tail p) =
                  punit.tail p * (monomial (1 / punit.lc p) (punit.lt q))"
    by (simp add: times_monomial_left[symmetric])
  ultimately have "(punit.red {q})\<^sup>*\<^sup>* (fst (punit.crit_pair p q)) s"
    by (simp add: punit.crit_pair_def \<open>?l - ?lt = ?lq\<close> s_def)
  moreover from \<open>q \<in> F\<close> have "{q} \<subseteq> F" by simp
  ultimately have 1: "(punit.red F)\<^sup>*\<^sup>* (fst (punit.crit_pair p q)) s" by (rule punit.red_rtrancl_subset)

  have "(punit.red {p})\<^sup>*\<^sup>* (punit.tail q * (monomial (1 / punit.lc q) (punit.lt p)))
        (punit.monom_mult (- (1 / punit.lc q) / punit.lc p) 0 (punit.tail q * punit.tail p))"
    unfolding punit_mult_scalar[symmetric] using \<open>p \<noteq> 0\<close> by (rule punit.red_mult_scalar_lt)
  hence "(punit.red {p})\<^sup>*\<^sup>* (snd (punit.crit_pair p q)) s"
    by (simp add: punit.crit_pair_def \<open>?l - ?lq = ?lt\<close> s_def mult.commute flip: times_monomial_left)
  moreover from \<open>p \<in> F\<close> have "{p} \<subseteq> F" by simp
  ultimately have 2: "(punit.red F)\<^sup>*\<^sup>* (snd (punit.crit_pair p q)) s" by (rule punit.red_rtrancl_subset)

  note assms(1) assms(2)
  moreover from \<open>p \<in> F\<close> \<open>F \<subseteq> punit.dgrad_p_set d m\<close> have "p \<in> punit.dgrad_p_set d m" ..
  moreover from \<open>q \<in> F\<close> \<open>F \<subseteq> punit.dgrad_p_set d m\<close> have "q \<in> punit.dgrad_p_set d m" ..
  moreover from 1 2 have "relation.cs (punit.red F) (fst (punit.crit_pair p q)) (snd (punit.crit_pair p q))"
    unfolding relation.cs_def by blast
  ultimately show ?thesis by (rule punit.crit_pair_cs_imp_crit_pair_cbelow_on)
qed

lemma chain_criterion:
  assumes "dickson_grading d" and "F \<subseteq> dgrad_p_set d m" and "p \<in> F" and "q \<in> F"
    and "p \<noteq> 0" and "q \<noteq> 0" and "lp r adds lcs (lp p) (lp q)"
    and "component_of_term (lt r) = component_of_term (lt p)"
    and pr: "crit_pair_cbelow_on d m F p r" and rq: "crit_pair_cbelow_on d m F r q"
  shows "crit_pair_cbelow_on d m F p q"
proof (cases "component_of_term (lt p) = component_of_term (lt q)")
  case True
  with assms(8) have comp_r: "component_of_term (lt r) = component_of_term (lt q)" by simp
  let ?A = "dgrad_p_set d m"
  let ?RS = "\<lambda>a b. red F a b \<or> red F b a"
  let ?lt = "lp p"
  let ?lq = "lp q"
  let ?lr = "lp r"
  let ?ltr = "lcs ?lt ?lr"
  let ?lrq = "lcs ?lr ?lq"
  let ?ltq = "lcs ?lt ?lq"

  from \<open>p \<in> F\<close> \<open>F \<subseteq> dgrad_p_set d m\<close> have "p \<in> dgrad_p_set d m" ..
  from this \<open>p \<noteq> 0\<close> have "d ?lt \<le> m" by (rule dgrad_p_setD_lp)
  from \<open>q \<in> F\<close> \<open>F \<subseteq> dgrad_p_set d m\<close> have "q \<in> dgrad_p_set d m" ..
  from this \<open>q \<noteq> 0\<close> have "d ?lq \<le> m" by (rule dgrad_p_setD_lp)
  from assms(1) have "d ?ltq \<le> ord_class.max (d ?lt) (d ?lq)" by (rule dickson_grading_lcs)
  also from \<open>d ?lt \<le> m\<close> \<open>d ?lq \<le> m\<close> have "... \<le> m" by simp
  finally have "d ?ltq \<le> m" .

  from adds_lcs \<open>?lr adds ?ltq\<close> have "?ltr adds ?ltq" by (rule lcs_adds)
  then obtain up where "?ltq = ?ltr + up" ..
  hence up1: "?ltq - ?lt = up + (?ltr - ?lt)" and up2: "up + (?ltr - ?lr) = ?ltq - ?lr"
    by (metis add.commute adds_lcs minus_plus, metis add.commute adds_lcs_2 minus_plus)
  have fst_pq: "fst (crit_pair p q) = monom_mult 1 up (fst (crit_pair p r))"
    by (simp add: crit_pair_def monom_mult_assoc up1 True comp_r)
  from assms(1) assms(2) _ _ pr
  have "cbelow_on ?A (\<prec>\<^sub>p) (monom_mult 1 up (monomial 1 (term_of_pair (?ltr, component_of_term (lt p))))) ?RS
                  (fst (crit_pair p q)) (monom_mult 1 up (snd (crit_pair p r)))"
    unfolding fst_pq crit_pair_cbelow_on_def
  proof (rule cbelow_on_monom_mult)
    from \<open>d ?ltq \<le> m\<close> show "d up \<le> m" by (simp add: \<open>?ltq = ?ltr + up\<close> dickson_gradingD1[OF assms(1)])
  qed simp
  hence 1: "cbelow_on ?A (\<prec>\<^sub>p) (monomial 1 (term_of_pair (?ltq, component_of_term (lt p)))) ?RS
                      (fst (crit_pair p q)) (monom_mult 1 up (snd (crit_pair p r)))"
    by (simp add: monom_mult_monomial \<open>?ltq = ?ltr + up\<close> add.commute splus_def term_simps)

  from \<open>?lr adds ?ltq\<close> adds_lcs_2 have "?lrq adds ?ltq" by (rule lcs_adds)
  then obtain uq where "?ltq = ?lrq + uq" ..
  hence uq1: "?ltq - ?lq = uq + (?lrq - ?lq)" and uq2: "uq + (?lrq - ?lr) = ?ltq - ?lr"
   by (metis add.commute adds_lcs_2 minus_plus, metis add.commute adds_lcs minus_plus)
  have eq: "monom_mult 1 uq (fst (crit_pair r q)) = monom_mult 1 up (snd (crit_pair p r))"
    by (simp add: crit_pair_def monom_mult_assoc up2 uq2 True comp_r)
  have snd_pq: "snd (crit_pair p q) = monom_mult 1 uq (snd (crit_pair r q))"
    by (simp add: crit_pair_def monom_mult_assoc uq1 True comp_r)
  from assms(1) assms(2) _ _ rq
  have "cbelow_on ?A (\<prec>\<^sub>p) (monom_mult 1 uq (monomial 1 (term_of_pair (?lrq, component_of_term (lt p))))) ?RS
                  (monom_mult 1 uq (fst (crit_pair r q))) (snd (crit_pair p q))"
    unfolding snd_pq crit_pair_cbelow_on_def assms(8)
  proof (rule cbelow_on_monom_mult)
    from \<open>d ?ltq \<le> m\<close> show "d uq \<le> m" by (simp add: \<open>?ltq = ?lrq + uq\<close> dickson_gradingD1[OF assms(1)])
  qed simp
  hence "cbelow_on ?A (\<prec>\<^sub>p) (monomial 1 (term_of_pair (?ltq, component_of_term (lt p)))) ?RS
                   (monom_mult 1 uq (fst (crit_pair r q))) (snd (crit_pair p q))"
    by (simp add: monom_mult_monomial \<open>?ltq = ?lrq + uq\<close> add.commute splus_def term_simps)
  hence "cbelow_on ?A (\<prec>\<^sub>p) (monomial 1 (term_of_pair (?ltq, component_of_term (lt p)))) ?RS
                   (monom_mult 1 up (snd (crit_pair p r))) (snd (crit_pair p q))"
    by (simp only: eq)
  
  with 1 show ?thesis unfolding crit_pair_cbelow_on_def by (rule cbelow_on_transitive)
next
  case False
  thus ?thesis by (rule crit_pair_cbelow_distinct_component)
qed

subsection \<open>Weak and Strong Gr\"obner Bases\<close>

lemma ord_p_wf_on:
  assumes "dickson_grading d"
  shows "wfp_on (\<prec>\<^sub>p) (dgrad_p_set d m)"
proof (rule wfp_onI_min)
  fix x::"'t \<Rightarrow>\<^sub>0 'b" and Q
  assume "x \<in> Q" and "Q \<subseteq> dgrad_p_set d m"
  with assms obtain z where "z \<in> Q" and *: "\<And>y. y \<prec>\<^sub>p z \<Longrightarrow> y \<notin> Q"
    by (rule ord_p_minimum_dgrad_p_set, blast)
  from this(1) show "\<exists>z\<in>Q. \<forall>y\<in>dgrad_p_set d m. y \<prec>\<^sub>p z \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y\<in>dgrad_p_set d m. y \<prec>\<^sub>p z \<longrightarrow> y \<notin> Q" by (intro ballI impI *)
  qed
qed

(* TODO: Collect all "_dgrad_p_set"-facts in a locale? *)
lemma is_red_implies_0_red_dgrad_p_set:
  assumes "dickson_grading d" and "B \<subseteq> dgrad_p_set d m"
  assumes "pmdl B \<subseteq> pmdl A" and "\<And>q. q \<in> pmdl A \<Longrightarrow> q \<in> dgrad_p_set d m \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> is_red B q"
    and "p \<in> pmdl A" and "p \<in> dgrad_p_set d m"
  shows "(red B)\<^sup>*\<^sup>* p 0"
proof -
  from ord_p_wf_on[OF assms(1)] assms(6, 5) show ?thesis
  proof (induction p rule: wfp_on_induct)
    case (less p)
    show ?case
    proof (cases "p = 0")
      case True
      thus ?thesis by simp
    next
      case False
      from assms(4)[OF less(3, 1) False] obtain q where redpq: "red B p q" unfolding is_red_alt ..
      with assms(1) assms(2) less(1) have "q \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_red)
      moreover from redpq have "q \<prec>\<^sub>p p" by (rule red_ord)
      moreover from \<open>pmdl B \<subseteq> pmdl A\<close> \<open>p \<in> pmdl A\<close> \<open>red B p q\<close> have "q \<in> pmdl A"
        by (rule pmdl_closed_red)
      ultimately have "(red B)\<^sup>*\<^sup>* q 0" by (rule less(2))
      show ?thesis by (rule converse_rtranclp_into_rtranclp, rule redpq, fact)
    qed
  qed
qed

lemma is_red_implies_0_red_dgrad_p_set':
  assumes "dickson_grading d" and "B \<subseteq> dgrad_p_set d m"
  assumes "pmdl B \<subseteq> pmdl A" and "\<And>q. q \<in> pmdl A \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> is_red B q"
    and "p \<in> pmdl A"
  shows "(red B)\<^sup>*\<^sup>* p 0"
proof -
  from assms(2) obtain n where "m \<le> n" and "p \<in> dgrad_p_set d n" and B: "B \<subseteq> dgrad_p_set d n"
    by (rule dgrad_p_set_insert)
  from ord_p_wf_on[OF assms(1)] this(2) assms(5) show ?thesis
  proof (induction p rule: wfp_on_induct)
    case (less p)
    show ?case
    proof (cases "p = 0")
      case True
      thus ?thesis by simp
    next
      case False
      from assms(4)[OF \<open>p \<in> (pmdl A)\<close> False] obtain q where redpq: "red B p q" unfolding is_red_alt ..
      with assms(1) B \<open>p \<in> dgrad_p_set d n\<close> have "q \<in> dgrad_p_set d n" by (rule dgrad_p_set_closed_red)
      moreover from redpq have "q \<prec>\<^sub>p p" by (rule red_ord)
      moreover from \<open>pmdl B \<subseteq> pmdl A\<close> \<open>p \<in> pmdl A\<close> \<open>red B p q\<close> have "q \<in> pmdl A"
        by (rule pmdl_closed_red)
      ultimately have "(red B)\<^sup>*\<^sup>* q 0" by (rule less(2))
      show ?thesis by (rule converse_rtranclp_into_rtranclp, rule redpq, fact)
    qed
  qed
qed

lemma pmdl_eqI_adds_lt_dgrad_p_set:
  fixes G::"('t \<Rightarrow>\<^sub>0 'b::field) set"
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m" and "B \<subseteq> dgrad_p_set d m" and "pmdl G \<subseteq> pmdl B"
  assumes "\<And>f. f \<in> pmdl B \<Longrightarrow> f \<in> dgrad_p_set d m \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> (\<exists>g \<in> G. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f)"
  shows "pmdl G = pmdl B"
proof
  show "pmdl B \<subseteq> pmdl G"
  proof (rule pmdl.span_subset_spanI, rule)
    fix p
    assume "p \<in> B"
    hence "p \<in> pmdl B" and "p \<in> dgrad_p_set d m" by (rule pmdl.span_base, rule, intro assms(3))
    with assms(1, 2, 4) _ have "(red G)\<^sup>*\<^sup>* p 0"
    proof (rule is_red_implies_0_red_dgrad_p_set)
      fix f
      assume "f \<in> pmdl B" and "f \<in> dgrad_p_set d m" and "f \<noteq> 0"
      hence "(\<exists>g \<in> G. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f)" by (rule assms(5))
      then obtain g where "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t lt f" by blast
      thus "is_red G f" using \<open>f \<noteq> 0\<close> is_red_indI1 by blast
    qed
    thus "p \<in> pmdl G" by (rule red_rtranclp_0_in_pmdl)
  qed
qed fact

lemma pmdl_eqI_adds_lt_dgrad_p_set':
  fixes G::"('t \<Rightarrow>\<^sub>0 'b::field) set"
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m" and "pmdl G \<subseteq> pmdl B"
  assumes "\<And>f. f \<in> pmdl B \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> (\<exists>g \<in> G. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f)"
  shows "pmdl G = pmdl B"
proof
  show "pmdl B \<subseteq> pmdl G"
  proof
    fix p
    assume "p \<in> pmdl B"
    with assms(1, 2, 3) _ have "(red G)\<^sup>*\<^sup>* p 0"
    proof (rule is_red_implies_0_red_dgrad_p_set')
      fix f
      assume "f \<in> pmdl B" and "f \<noteq> 0"
      hence "(\<exists>g \<in> G. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f)" by (rule assms(4))
      then obtain g where "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t lt f" by blast
      thus "is_red G f" using \<open>f \<noteq> 0\<close> is_red_indI1 by blast
    qed
    thus "p \<in> pmdl G" by (rule red_rtranclp_0_in_pmdl)
  qed
qed fact

lemma GB_implies_unique_nf_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G"
  shows "\<exists>! h. (red G)\<^sup>*\<^sup>* f h \<and> \<not> is_red G h"
proof -
  from assms(1) assms(2) have "wfP (red G)\<inverse>\<inverse>" by (rule red_wf_dgrad_p_set)
  then obtain h where ftoh: "(red G)\<^sup>*\<^sup>* f h" and irredh: "relation.is_final (red G) h"
    by (rule relation.wf_imp_nf_ex)
  show ?thesis
  proof
    from ftoh and irredh show "(red G)\<^sup>*\<^sup>* f h \<and> \<not> is_red G h" by (simp add: is_red_def)
  next
    fix h'
    assume "(red G)\<^sup>*\<^sup>* f h' \<and> \<not> is_red G h'"
    hence ftoh': "(red G)\<^sup>*\<^sup>* f h'" and irredh': "relation.is_final (red G) h'" by (simp_all add: is_red_def)
    show "h' = h"
    proof (rule relation.ChurchRosser_unique_final)
      from isGB show "relation.is_ChurchRosser (red G)" by (simp only: is_Groebner_basis_def)
    qed fact+
  qed
qed

lemma translation_property':
  assumes "p \<noteq> 0" and red_p_0: "(red F)\<^sup>*\<^sup>* p 0"
  shows "is_red F (p + q) \<or> is_red F q"
proof (rule disjCI)
  assume not_red: "\<not> is_red F q"
  from red_p_0 \<open>p \<noteq> 0\<close> obtain f where "f \<in> F" and "f \<noteq> 0" and lt_adds: "lt f adds\<^sub>t lt p"
    by (rule zero_reducibility_implies_lt_divisibility)
  show "is_red F (p + q)"
  proof (cases "q = 0")
    case True
    with is_red_indI1[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> \<open>p \<noteq> 0\<close> lt_adds] show ?thesis by simp
  next
    case False
    from not_red is_red_addsI[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> _ lt_adds, of q] have "\<not> lt p \<in> (keys q)" by blast
    hence "lookup q (lt p) = 0" by (simp add: in_keys_iff)
    with lt_in_keys[OF \<open>p \<noteq> 0\<close>] have "lt p \<in> (keys (p + q))" unfolding in_keys_iff by (simp add: lookup_add)
    from is_red_addsI[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> this lt_adds] show ?thesis .
  qed
qed
  
lemma translation_property:
  assumes "p \<noteq> q" and red_0: "(red F)\<^sup>*\<^sup>* (p - q) 0"
  shows "is_red F p \<or> is_red F q"
proof -
  from \<open>p \<noteq> q\<close> have "p - q \<noteq> 0" by simp
  from translation_property'[OF this red_0, of q] show ?thesis by simp
qed

lemma weak_GB_is_strong_GB_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m"
  assumes "\<And>f. f \<in> pmdl G \<Longrightarrow> f \<in> dgrad_p_set d m \<Longrightarrow> (red G)\<^sup>*\<^sup>* f 0"
  shows "is_Groebner_basis G"
  using assms(1, 2)
proof (rule Buchberger_criterion_dgrad_p_set)
  fix p q
  assume "p \<in> G" and "q \<in> G"
  hence "p \<in> pmdl G" and "q \<in> pmdl G" by (auto intro: pmdl.span_base)
  hence "spoly p q \<in> pmdl G" by (rule pmdl_closed_spoly)
  thus "(red G)\<^sup>*\<^sup>* (spoly p q) 0"
  proof (rule assms(3))
    note assms(1)
    moreover from \<open>p \<in> G\<close> assms(2) have "p \<in> dgrad_p_set d m" ..
    moreover from \<open>q \<in> G\<close> assms(2) have "q \<in> dgrad_p_set d m" ..
    ultimately show "spoly p q \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_spoly)
  qed
qed

lemma weak_GB_is_strong_GB:
  assumes "\<And>f. f \<in> (pmdl G) \<Longrightarrow> (red G)\<^sup>*\<^sup>* f 0"
  shows "is_Groebner_basis G"
  unfolding is_Groebner_basis_def
proof (rule relation.confluence_implies_ChurchRosser,
      simp add: relation.is_confluent_def relation.is_confluent_on_def, intro allI impI, erule conjE)
  fix f p q
  assume "(red G)\<^sup>*\<^sup>* f p" and "(red G)\<^sup>*\<^sup>* f q"
  hence "relation.srtc (red G) p q"
    by (meson relation.rtc_implies_srtc relation.srtc_symmetric relation.srtc_transitive)
  hence "p - q \<in> pmdl G" by (rule srtc_in_pmdl)
  hence "(red G)\<^sup>*\<^sup>* (p - q) 0" by (rule assms)
  thus "relation.cs (red G) p q" by (rule red_diff_rtrancl_cs)
qed

corollary GB_alt_1_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m"
  shows "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> pmdl G. f \<in> dgrad_p_set d m \<longrightarrow> (red G)\<^sup>*\<^sup>* f 0)"
  using weak_GB_is_strong_GB_dgrad_p_set[OF assms] GB_imp_zero_reducibility by blast

corollary GB_alt_1: "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> pmdl G. (red G)\<^sup>*\<^sup>* f 0)"
  using weak_GB_is_strong_GB GB_imp_zero_reducibility by blast

lemma isGB_I_is_red:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m"
  assumes "\<And>f. f \<in> pmdl G \<Longrightarrow> f \<in> dgrad_p_set d m \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> is_red G f"
  shows "is_Groebner_basis G"
  unfolding GB_alt_1_dgrad_p_set[OF assms(1, 2)]
proof (intro ballI impI)
  fix f
  assume "f \<in> pmdl G" and "f \<in> dgrad_p_set d m"
  with assms(1, 2) subset_refl assms(3) show "(red G)\<^sup>*\<^sup>* f 0"
    by (rule is_red_implies_0_red_dgrad_p_set)
qed

lemma GB_alt_2_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m"
  shows "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> pmdl G. f \<noteq> 0 \<longrightarrow> is_red G f)"
proof
  assume "is_Groebner_basis G"
  show "\<forall>f\<in>pmdl G. f \<noteq> 0 \<longrightarrow> is_red G f"
  proof (intro ballI, intro impI)
    fix f
    assume "f \<in> (pmdl G)" and "f \<noteq> 0"
    show "is_red G f" by (rule GB_imp_reducibility, fact+)
  qed
next
  assume a2: "\<forall>f\<in>pmdl G. f \<noteq> 0 \<longrightarrow> is_red G f"
  show "is_Groebner_basis G" unfolding GB_alt_1
  proof
    fix f
    assume "f \<in> pmdl G"
    from assms show "(red G)\<^sup>*\<^sup>* f 0"
    proof (rule is_red_implies_0_red_dgrad_p_set')
      fix q
      assume "q \<in> pmdl G" and "q \<noteq> 0"
      thus "is_red G q" by (rule a2[rule_format])
    qed (fact subset_refl, fact)
  qed
qed
  
lemma GB_adds_lt:
  assumes "is_Groebner_basis G" and "f \<in> pmdl G" and "f \<noteq> 0"
  obtains g where "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t lt f"
proof -
  from assms(1) assms(2) have "(red G)\<^sup>*\<^sup>* f 0" by (rule GB_imp_zero_reducibility)
  show ?thesis by (rule zero_reducibility_implies_lt_divisibility, fact+)
qed

lemma isGB_I_adds_lt:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m"
  assumes "\<And>f. f \<in> pmdl G \<Longrightarrow> f \<in> dgrad_p_set d m \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> (\<exists>g \<in> G. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f)"
  shows "is_Groebner_basis G"
  using assms(1, 2)
proof (rule isGB_I_is_red)
  fix f
  assume "f \<in> pmdl G" and "f \<in> dgrad_p_set d m" and "f \<noteq> 0"
  hence "(\<exists>g \<in> G. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f)" by (rule assms(3))
  then obtain g where "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t lt f" by blast
  thus "is_red G f" using \<open>f \<noteq> 0\<close> is_red_indI1 by blast
qed

lemma GB_alt_3_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m"
  shows "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> pmdl G. f \<noteq> 0 \<longrightarrow> (\<exists>g \<in> G. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f))"
    (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (intro ballI impI)
    fix f
    assume "f \<in> pmdl G" and "f \<noteq> 0"
    with \<open>?L\<close> obtain g where "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t lt f" by (rule GB_adds_lt)
    thus "\<exists>g\<in>G. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f" by blast
  qed
next
  assume ?R
  show ?L unfolding GB_alt_2_dgrad_p_set[OF assms]
  proof (intro ballI impI)
    fix f
    assume "f \<in> pmdl G" and "f \<noteq> 0"
    with \<open>?R\<close> have "(\<exists>g \<in> G. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f)" by blast
    then obtain g where "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t lt f" by blast
    thus "is_red G f" using \<open>f \<noteq> 0\<close> is_red_indI1 by blast
  qed
qed
  
lemma GB_insert:
  assumes "is_Groebner_basis G" and "f \<in> pmdl G"
  shows "is_Groebner_basis (insert f G)"
  using assms unfolding GB_alt_1
  by (metis insert_subset pmdl.span_insert_idI red_rtrancl_subset subsetI)

lemma GB_subset:
  assumes "is_Groebner_basis G" and "G \<subseteq> G'" and "pmdl G' = pmdl G"
  shows "is_Groebner_basis G'"
  using assms(1) unfolding GB_alt_1 using assms(2) assms(3) red_rtrancl_subset by blast

lemma (in ordered_term) GB_remove_0_stable_GB:
  assumes "is_Groebner_basis G"
  shows "is_Groebner_basis (G - {0})"
  using assms by (simp only: is_Groebner_basis_def red_minus_singleton_zero)

lemmas is_red_implies_0_red_finite = is_red_implies_0_red_dgrad_p_set'[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_implies_unique_nf_finite = GB_implies_unique_nf_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_alt_2_finite = GB_alt_2_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_alt_3_finite = GB_alt_3_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas pmdl_eqI_adds_lt_finite = pmdl_eqI_adds_lt_dgrad_p_set'[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

subsection \<open>Alternative Characterization of Gr\"obner Bases via Representations of S-Polynomials\<close>

definition spoly_rep :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) \<Rightarrow> bool"
  where "spoly_rep d m G g1 g2 \<longleftrightarrow> (\<exists>q. spoly g1 g2 = (\<Sum>g\<in>G. q g \<odot> g) \<and>
                (\<forall>g. q g \<in> punit.dgrad_p_set d m \<and>
                        (q g \<odot> g \<noteq> 0 \<longrightarrow> lt (q g \<odot> g) \<prec>\<^sub>t term_of_pair (lcs (lp g1) (lp g2),
                                                                      component_of_term (lt g2)))))"

lemma spoly_repI:
  "spoly g1 g2 = (\<Sum>g\<in>G. q g \<odot> g) \<Longrightarrow> (\<And>g. q g \<in> punit.dgrad_p_set d m) \<Longrightarrow>
    (\<And>g. q g \<odot> g \<noteq> 0 \<Longrightarrow> lt (q g \<odot> g) \<prec>\<^sub>t term_of_pair (lcs (lp g1) (lp g2),
                                                        component_of_term (lt g2))) \<Longrightarrow>
    spoly_rep d m G g1 g2"
  by (auto simp: spoly_rep_def)

lemma spoly_repI_zero:
  assumes "spoly g1 g2 = 0"
  shows "spoly_rep d m G g1 g2"
proof (rule spoly_repI)
  show "spoly g1 g2 = (\<Sum>g\<in>G. 0 \<odot> g)" by (simp add: assms)
qed (simp_all add: punit.zero_in_dgrad_p_set)

lemma spoly_repE:
  assumes "spoly_rep d m G g1 g2"
  obtains q where "spoly g1 g2 = (\<Sum>g\<in>G. q g \<odot> g)" and "\<And>g. q g \<in> punit.dgrad_p_set d m"
    and "\<And>g. q g \<odot> g \<noteq> 0 \<Longrightarrow> lt (q g \<odot> g) \<prec>\<^sub>t term_of_pair (lcs (lp g1) (lp g2),
                                                             component_of_term (lt g2))"
  using assms by (auto simp: spoly_rep_def)

corollary isGB_D_spoly_rep:
  assumes "dickson_grading d" and "is_Groebner_basis G" and "G \<subseteq> dgrad_p_set d m" and "finite G"
    and "g1 \<in> G" and "g2 \<in> G" and "g1 \<noteq> 0" and "g2 \<noteq> 0"
  shows "spoly_rep d m G g1 g2"
proof (cases "spoly g1 g2 = 0")
  case True
  thus ?thesis by (rule spoly_repI_zero)
next
  case False
  let ?v = "term_of_pair (lcs (lp g1) (lp g2), component_of_term (lt g1))"
  let ?h = "crit_pair g1 g2"
  from assms(7, 8) have eq: "spoly g1 g2 = fst ?h + (- snd ?h)" by (simp add: spoly_alt)
  have "fst ?h \<prec>\<^sub>p monomial 1 ?v" by (fact fst_crit_pair_below_lcs)
  hence d1: "fst ?h = 0 \<or> lt (fst ?h) \<prec>\<^sub>t ?v" by (simp only: ord_strict_p_monomial_iff)
  have "snd ?h \<prec>\<^sub>p monomial 1 ?v" by (fact snd_crit_pair_below_lcs)
  hence d2: "snd ?h = 0 \<or> lt (- snd ?h) \<prec>\<^sub>t ?v" by (simp only: ord_strict_p_monomial_iff lt_uminus)
  note assms(1)
  moreover from assms(5, 3) have "g1 \<in> dgrad_p_set d m" ..
  moreover from assms(6, 3) have "g2 \<in> dgrad_p_set d m" ..
  ultimately have "spoly g1 g2 \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_spoly)
  from assms(5) have "g1 \<in> pmdl G" by (rule pmdl.span_base)
  moreover from assms(6) have "g2 \<in> pmdl G" by (rule pmdl.span_base)
  ultimately have "spoly g1 g2 \<in> pmdl G" by (rule pmdl_closed_spoly)
  with assms(2) have "(red G)\<^sup>*\<^sup>* (spoly g1 g2) 0" by (rule GB_imp_zero_reducibility)
  with assms(1, 3, 4) \<open>spoly _ _ \<in> dgrad_p_set _ _\<close> obtain q
    where 1: "spoly g1 g2 = 0 + (\<Sum>g\<in>G. q g \<odot> g)" and 2: "\<And>g. q g \<in> punit.dgrad_p_set d m"
      and "\<And>g. lt (q g \<odot> g) \<preceq>\<^sub>t lt (spoly g1 g2)" by (rule red_rtrancl_repE) blast
  show ?thesis
  proof (rule spoly_repI)
    fix g
    note \<open>lt (q g \<odot> g) \<preceq>\<^sub>t lt (spoly g1 g2)\<close>
    also from d1 have "lt (spoly g1 g2) \<prec>\<^sub>t ?v"
    proof
      assume "fst ?h = 0"
      hence eq: "spoly g1 g2 = - snd ?h" by (simp add: eq)
      also from d2 have "lt \<dots> \<prec>\<^sub>t ?v"
      proof
        assume "snd ?h = 0"
        with False show ?thesis by (simp add: eq)
      qed
      finally show ?thesis .
    next
      assume *: "lt (fst ?h) \<prec>\<^sub>t ?v"
      from d2 show ?thesis
      proof
        assume "snd ?h = 0"
        with * show ?thesis by (simp add: eq)
      next
        assume **: "lt (- snd ?h) \<prec>\<^sub>t ?v"
        have "lt (spoly g1 g2) \<preceq>\<^sub>t ord_term_lin.max (lt (fst ?h)) (lt (- snd ?h))" unfolding eq
          by (fact lt_plus_le_max)
        also from * ** have "\<dots> \<prec>\<^sub>t ?v" by (simp only: ord_term_lin.max_less_iff_conj)
        finally show ?thesis .
      qed
    qed
    also from False have "\<dots> = term_of_pair (lcs (lp g1) (lp g2), component_of_term (lt g2))"
      by (simp add: spoly_def Let_def split: if_split_asm)
    finally show "lt (q g \<odot> g) \<prec>\<^sub>t term_of_pair (lcs (lp g1) (lp g2), component_of_term (lt g2))" .
  qed (simp_all add: 1 2)
qed

text \<open>The finiteness assumption on \<open>G\<close> in the following theorem could be dropped, but it makes the
  proof a lot easier (although it is still fairly complicated).\<close>

lemma isGB_I_spoly_rep:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m" and "finite G"
    and "\<And>g1 g2. g1 \<in> G \<Longrightarrow> g2 \<in> G \<Longrightarrow> g1 \<noteq> 0 \<Longrightarrow> g2 \<noteq> 0 \<Longrightarrow> spoly g1 g2 \<noteq> 0 \<Longrightarrow> spoly_rep d m G g1 g2"
  shows "is_Groebner_basis G"
proof (rule ccontr)
  assume "\<not> is_Groebner_basis G"
  then obtain p where "p \<in> pmdl G" and p_in: "p \<in> dgrad_p_set d m" and "\<not> (red G)\<^sup>*\<^sup>* p 0"
    by (auto simp: GB_alt_1_dgrad_p_set[OF assms(1, 2)])
  from \<open>\<not> is_Groebner_basis G\<close> have "G \<noteq> {}" by (auto simp: is_Groebner_basis_empty)

  obtain r where p_red: "(red G)\<^sup>*\<^sup>* p r" and r_irred: "\<not> is_red G r"
  proof -
    define A where "A = {q. (red G)\<^sup>*\<^sup>* p q}"
    from assms(1, 2) have "wfP (red G)\<inverse>\<inverse>" by (rule red_wf_dgrad_p_set)
    moreover have "p \<in> A" by (simp add: A_def)
    ultimately obtain r where "r \<in> A" and r_min: "\<And>z. (red G)\<inverse>\<inverse> z r \<Longrightarrow> z \<notin> A"
      by (rule wfE_min[to_pred]) blast
    show ?thesis
    proof
      from \<open>r \<in> A\<close> show *: "(red G)\<^sup>*\<^sup>* p r" by (simp add: A_def)

      show "\<not> is_red G r"
      proof
        assume "is_red G r"
        then obtain z where "(red G) r z" by (rule is_redE)
        hence "(red G)\<inverse>\<inverse> z r" by simp
        hence "z \<notin> A" by (rule r_min)
        hence "\<not> (red G)\<^sup>*\<^sup>* p z" by (simp add: A_def)
        moreover from * \<open>(red G) r z\<close> have "(red G)\<^sup>*\<^sup>* p z" ..
        ultimately show False ..
      qed
    qed
  qed
  from assms(1, 2) p_in p_red have r_in: "r \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_red_rtrancl)
  from p_red \<open>\<not> (red G)\<^sup>*\<^sup>* p 0\<close> have "r \<noteq> 0" by blast
  from p_red have "p - r \<in> pmdl G" by (rule red_rtranclp_diff_in_pmdl)
  with \<open>p \<in> pmdl G\<close> have "p - (p - r) \<in> pmdl G" by (rule pmdl.span_diff)
  hence "r \<in> pmdl G" by simp
  with assms(3) obtain q0 where r: "r = (\<Sum>g\<in>G. q0 g \<odot> g)" by (rule pmdl.span_finiteE)
  from assms(3) have "finite (q0 ` G)" by (rule finite_imageI)
  then obtain m0 where "q0 ` G \<subseteq> punit.dgrad_p_set d m0" by (rule punit.dgrad_p_set_exhaust)
  define m' where "m' = ord_class.max m m0"
  have "dgrad_p_set d m \<subseteq> dgrad_p_set d m'" by (rule dgrad_p_set_subset) (simp add: m'_def)
  with assms(2) have G_sub: "G \<subseteq> dgrad_p_set d m'" by (rule subset_trans)
  have "punit.dgrad_p_set d m0 \<subseteq> punit.dgrad_p_set d m'"
    by (rule punit.dgrad_p_set_subset) (simp add: m'_def)
  with \<open>q0 ` G \<subseteq> _\<close> have "q0 ` G \<subseteq> punit.dgrad_p_set d m'" by (rule subset_trans)

  define mlt where "mlt = (\<lambda>q. ord_term_lin.Max (lt ` {q g \<odot> g | g. g \<in> G \<and> q g \<odot> g \<noteq> 0}))"
  define mnum where "mnum = (\<lambda>q. card {g\<in>G. q g \<odot> g \<noteq> 0 \<and> lt (q g \<odot> g) = mlt q})"
  define rel where "rel = (\<lambda>q1 q2. mlt q1 \<prec>\<^sub>t mlt q2 \<or> (mlt q1 = mlt q2 \<and> mnum q1 < mnum q2))"
  define rel_dom where "rel_dom = {q. q ` G \<subseteq> punit.dgrad_p_set d m' \<and> r = (\<Sum>g\<in>G. q g \<odot> g)}"

  have mlt_in: "mlt q \<in> lt ` {q g \<odot> g | g. g \<in> G \<and> q g \<odot> g \<noteq> 0}" if "q \<in> rel_dom" for q
    unfolding mlt_def
  proof (rule ord_term_lin.Max_in, simp_all add: assms(3), rule ccontr)
    assume "\<nexists>g. g \<in> G \<and> q g \<odot> g \<noteq> 0"
    hence "q g \<odot> g = 0" if "g \<in> G" for g using that by simp
    with that have "r = 0" by (simp add: rel_dom_def)
    with \<open>r \<noteq> 0\<close> show False ..
  qed
  
  have rel_dom_dgrad_set: "pp_of_term ` mlt ` rel_dom \<subseteq> dgrad_set d m'"
  proof (rule subsetI, elim imageE)
    fix q v t
    assume "q \<in> rel_dom" and v: "v = mlt q" and t: "t = pp_of_term v"
    from this(1) have "v \<in> lt ` {q g \<odot> g | g. g \<in> G \<and> q g \<odot> g \<noteq> 0}" unfolding v by (rule mlt_in)
    then obtain g where "g \<in> G" and "q g \<odot> g \<noteq> 0" and v: "v = lt (q g \<odot> g)" by blast
    from this(2) have "q g \<noteq> 0" and "g \<noteq> 0" by auto
    hence "v = punit.lt (q g) \<oplus> lt g" unfolding v by (rule lt_mult_scalar)
    hence "t = punit.lt (q g) + lp g" by (simp add: t pp_of_term_splus)
    also from assms(1) have "d \<dots> = ord_class.max (d (punit.lt (q g))) (d (lp g))"
      by (rule dickson_gradingD1)
    also have "\<dots> \<le> m'"
    proof (rule max.boundedI)
      from \<open>g \<in> G\<close> \<open>q \<in> rel_dom\<close> have "q g \<in> punit.dgrad_p_set d m'" by (auto simp: rel_dom_def)
      moreover from \<open>q g \<noteq> 0\<close> have "punit.lt (q g) \<in> keys (q g)" by (rule punit.lt_in_keys)
      ultimately show "d (punit.lt (q g)) \<le> m'" by (rule punit.dgrad_p_setD[simplified])
    next
      from \<open>g \<in> G\<close> G_sub have "g \<in> dgrad_p_set d m'" ..
      moreover from \<open>g \<noteq> 0\<close> have "lt g \<in> keys g" by (rule lt_in_keys)
      ultimately show "d (lp g) \<le> m'" by (rule dgrad_p_setD)
    qed
    finally show "t \<in> dgrad_set d m'" by (simp add: dgrad_set_def)
  qed

  obtain q where "q \<in> rel_dom" and q_min: "\<And>q'. rel q' q \<Longrightarrow> q' \<notin> rel_dom"
  proof -
    from \<open>q0 ` G \<subseteq> punit.dgrad_p_set d m'\<close> have "q0 \<in> rel_dom" by (simp add: rel_dom_def r)
    hence "mlt q0 \<in> mlt ` rel_dom" by (rule imageI)
    with assms(1) obtain u where "u \<in> mlt ` rel_dom" and u_min: "\<And>w. w \<prec>\<^sub>t u \<Longrightarrow> w \<notin> mlt ` rel_dom"
      using rel_dom_dgrad_set by (rule ord_term_minimum_dgrad_set) blast
    from this(1) obtain q' where "q' \<in> rel_dom" and u: "u = mlt q'" ..
    hence "q' \<in> rel_dom \<inter> {q. mlt q = u}" (is "_ \<in> ?A") by simp
    hence "mnum q' \<in> mnum ` ?A" by (rule imageI)
    with wf[to_pred] obtain k where "k \<in> mnum ` ?A" and k_min: "\<And>l. l < k \<Longrightarrow> l \<notin> mnum ` ?A"
      by (rule wfE_min[to_pred]) blast
    from this(1) obtain q'' where "q'' \<in> rel_dom" and mlt'': "mlt q'' = u" and k: "k = mnum q''"
      by blast
    from this(1) show ?thesis
    proof
      fix q0
      assume "rel q0 q''"
      show "q0 \<notin> rel_dom"
      proof
        assume "q0 \<in> rel_dom"
        from \<open>rel q0 q''\<close> show False unfolding rel_def
        proof (elim disjE conjE)
          assume "mlt q0 \<prec>\<^sub>t mlt q''"
          hence "mlt q0 \<notin> mlt ` rel_dom" unfolding mlt'' by (rule u_min)
          moreover from \<open>q0 \<in> rel_dom\<close> have "mlt q0 \<in> mlt ` rel_dom" by (rule imageI)
          ultimately show ?thesis ..
        next
          assume "mlt q0 = mlt q''"
          with \<open>q0 \<in> rel_dom\<close> have "q0 \<in> ?A" by (simp add: mlt'')
          assume "mnum q0 < mnum q''"
          hence "mnum q0 \<notin> mnum ` ?A" unfolding k[symmetric] by (rule k_min)
          with \<open>q0 \<in> ?A\<close> show ?thesis by blast
        qed
      qed
    qed
  qed
  from this(1) have q_in: "\<And>g. g \<in> G \<Longrightarrow> q g \<in> punit.dgrad_p_set d m'"
    and r: "r = (\<Sum>g\<in>G. q g \<odot> g)" by (auto simp: rel_dom_def)

  define v where "v = mlt q"
  from \<open>q \<in> rel_dom\<close> have "v \<in> lt ` {q g \<odot> g | g. g \<in> G \<and> q g \<odot> g \<noteq> 0}" unfolding v_def
    by (rule mlt_in)
  then obtain g1 where "g1 \<in> G" and "q g1 \<odot> g1 \<noteq> 0" and v1: "v = lt (q g1 \<odot> g1)" by blast
  moreover define M where "M = {g\<in>G. q g \<odot> g \<noteq> 0 \<and> lt (q g \<odot> g) = v}"
  ultimately have "g1 \<in> M" by simp
  have v_max: "lt (q g \<odot> g) \<prec>\<^sub>t v" if "g \<in> G" and "g \<notin> M" and "q g \<odot> g \<noteq> 0" for g
  proof -
    from that have "lt (q g \<odot> g) \<noteq> v" by (auto simp: M_def)
    moreover have "lt (q g \<odot> g) \<preceq>\<^sub>t v" unfolding v_def mlt_def
      by (rule ord_term_lin.Max_ge) (auto simp: assms(3) \<open>q g \<odot> g \<noteq> 0\<close> intro!: imageI \<open>g \<in> G\<close>)
    ultimately show ?thesis by simp
  qed
  from \<open>q g1 \<odot> g1 \<noteq> 0\<close> have "q g1 \<noteq> 0" and "g1 \<noteq> 0" by auto
  hence v1': "v = punit.lt (q g1) \<oplus> lt g1" unfolding v1 by (rule lt_mult_scalar)
  have "M - {g1} \<noteq> {}"
  proof
    assume "M - {g1} = {}"
    have "v \<in> keys (q g1 \<odot> g1)" unfolding v1 using \<open>q g1 \<odot> g1 \<noteq> 0\<close> by (rule lt_in_keys)
    moreover have "v \<notin> keys (\<Sum>g\<in>G-{g1}. q g \<odot> g)"
    proof
      assume "v \<in> keys (\<Sum>g\<in>G-{g1}. q g \<odot> g)"
      also have "\<dots> \<subseteq> (\<Union>g\<in>G-{g1}. keys (q g \<odot> g))" by (fact keys_sum_subset)
      finally obtain g where "g \<in> G - {g1}" and "v \<in> keys (q g \<odot> g)" ..
      from this(2) have "q g \<odot> g \<noteq> 0" and "v \<preceq>\<^sub>t lt (q g \<odot> g)" by (auto intro: lt_max_keys)
      from \<open>g \<in> G - {g1}\<close> \<open>M - {g1} = {}\<close> have "g \<in> G" and "g \<notin> M" by blast+
      hence "lt (q g \<odot> g) \<prec>\<^sub>t v" by (rule v_max) fact
      with \<open>v \<preceq>\<^sub>t _\<close> show False by simp
    qed
    ultimately have "v \<in> keys (q g1 \<odot> g1 + (\<Sum>g\<in>G-{g1}. q g \<odot> g))" by (rule in_keys_plusI1)
    also from \<open>g1 \<in> G\<close> assms(3) have "\<dots> = keys r" by (simp add: r sum.remove)
    finally have "v \<in> keys r" .
    with \<open>g1 \<in> G\<close> \<open>g1 \<noteq> 0\<close> have "is_red G r" by (rule is_red_addsI) (simp add: v1' term_simps)
    with r_irred show False ..
  qed
  then obtain g2 where "g2 \<in> M" and "g1 \<noteq> g2" by blast
  from this(1) have "g2 \<in> G" and "q g2 \<odot> g2 \<noteq> 0" and v2: "v = lt (q g2 \<odot> g2)" by (simp_all add: M_def)
  from this(2) have "q g2 \<noteq> 0" and "g2 \<noteq> 0" by auto
  hence v2': "v = punit.lt (q g2) \<oplus> lt g2" unfolding v2 by (rule lt_mult_scalar)
  hence "component_of_term (punit.lt (q g1) \<oplus> lt g1) = component_of_term (punit.lt (q g2) \<oplus> lt g2)"
    by (simp only: v1' flip: v2')
  hence cmp_eq: "component_of_term (lt g1) = component_of_term (lt g2)" by (simp add: term_simps)

  have "M \<subseteq> G" by (simp add: M_def)
  have "r = q g1 \<odot> g1 + (\<Sum>g\<in>G - {g1}. q g \<odot> g)"
    using assms(3) \<open>g1 \<in> G\<close> by (simp add: r sum.remove)
  also have "\<dots> = q g1 \<odot> g1 + q g2 \<odot> g2 + (\<Sum>g\<in>G - {g1} - {g2}. q g \<odot> g)"
    using assms(3) \<open>g2 \<in> G\<close> \<open>g1 \<noteq> g2\<close>
    by (metis (no_types, lifting) add.assoc finite_Diff insert_Diff insert_Diff_single insert_iff
                sum.insert_remove)
  finally have r: "r = q g1 \<odot> g1 + q g2 \<odot> g2 + (\<Sum>g\<in>G - {g1, g2}. q g \<odot> g)"
    by (simp flip: Diff_insert2)

  let ?l = "lcs (lp g1) (lp g2)"
  let ?v = "term_of_pair (?l, component_of_term (lt g2))"
  have "lp g1 adds lp (q g1 \<odot> g1)" by (simp add: v1' pp_of_term_splus flip: v1)
  moreover have "lp g2 adds lp (q g1 \<odot> g1)" by (simp add: v2' pp_of_term_splus flip: v1)
  ultimately have l_adds: "?l adds lp (q g1 \<odot> g1)" by (rule lcs_adds)

  have "spoly_rep d m G g1 g2"
  proof (cases "spoly g1 g2 = 0")
    case True
    thus ?thesis by (rule spoly_repI_zero)
  next
    case False
    with \<open>g1 \<in> G\<close> \<open>g2 \<in> G\<close> \<open>g1 \<noteq> 0\<close> \<open>g2 \<noteq> 0\<close> show ?thesis by (rule assms(4))
  qed
  then obtain q' where spoly: "spoly g1 g2 = (\<Sum>g\<in>G. q' g \<odot> g)"
    and "\<And>g. q' g \<in> punit.dgrad_p_set d m" and "\<And>g. q' g \<odot> g \<noteq> 0 \<Longrightarrow> lt (q' g \<odot> g) \<prec>\<^sub>t ?v"
    by (rule spoly_repE) blast
  note this(2)
  also have "punit.dgrad_p_set d m \<subseteq> punit.dgrad_p_set d m'"
    by (rule punit.dgrad_p_set_subset) (simp add: m'_def)
  finally have q'_in: "\<And>g. q' g \<in> punit.dgrad_p_set d m'" .

  define mu where "mu = monomial (lc (q g1 \<odot> g1)) (lp (q g1 \<odot> g1) - ?l)"
  define mu1 where "mu1 = monomial (1 / lc g1) (?l - lp g1)"
  define mu2 where "mu2 = monomial (1 / lc g2) (?l - lp g2)"
    define q'' where "q'' = (\<lambda>g. q g + mu * q' g)
                              (g1:=punit.tail (q g1) + mu * q' g1, g2:=q g2 + mu * q' g2 + mu * mu2)"
  from \<open>q g1 \<odot> g1 \<noteq> 0\<close> have "mu \<noteq> 0" by (simp add: mu_def monomial_0_iff lc_eq_zero_iff)
  from \<open>g1 \<noteq> 0\<close> l_adds have mu_times_mu1: "mu * mu1 = monomial (punit.lc (q g1)) (punit.lt (q g1))"
    by (simp add: mu_def mu1_def times_monomial_monomial lc_mult_scalar lc_eq_zero_iff
              minus_plus_minus_cancel adds_lcs v1' pp_of_term_splus flip: v1)
  from l_adds have mu_times_mu2: "mu * mu2 = monomial (lc (q g1 \<odot> g1) / lc g2) (punit.lt (q g2))"
    by (simp add: mu_def mu2_def times_monomial_monomial lc_mult_scalar minus_plus_minus_cancel
              adds_lcs_2 v2' pp_of_term_splus flip: v1)
  have "mu1 \<odot> g1 - mu2 \<odot> g2 = spoly g1 g2"
    by (simp add: spoly_def Let_def cmp_eq lc_def mult_scalar_monomial mu1_def mu2_def)
  also have "\<dots> = q' g1 \<odot> g1 + (\<Sum>g\<in>G - {g1}. q' g \<odot> g)"
    using assms(3) \<open>g1 \<in> G\<close> by (simp add: spoly sum.remove)
  also have "\<dots> = q' g1 \<odot> g1 + q' g2 \<odot> g2 + (\<Sum>g\<in>G - {g1} - {g2}. q' g \<odot> g)"
    using assms(3) \<open>g2 \<in> G\<close> \<open>g1 \<noteq> g2\<close>
    by (metis (no_types, lifting) add.assoc finite_Diff insert_Diff insert_Diff_single insert_iff
                sum.insert_remove)
  finally have "(q' g1 - mu1) \<odot> g1 + (q' g2 + mu2) \<odot> g2 + (\<Sum>g\<in>G - {g1, g2}. q' g \<odot> g) = 0"
    by (simp add: algebra_simps flip: Diff_insert2)
  hence "0 = mu \<odot> ((q' g1 - mu1) \<odot> g1 + (q' g2 + mu2) \<odot> g2 + (\<Sum>g\<in>G - {g1, g2}. q' g \<odot> g))" by simp
  also have "\<dots> = (mu * q' g1 - mu * mu1) \<odot> g1 + (mu * q' g2 + mu * mu2) \<odot> g2 +
                    (\<Sum>g\<in>G - {g1, g2}. (mu * q' g) \<odot> g)"
    by (simp add: mult_scalar_distrib_left sum_mult_scalar_distrib_left distrib_left right_diff_distrib
            flip: mult_scalar_assoc)
  finally have "r = r + (mu * q' g1 - mu * mu1) \<odot> g1 + (mu * q' g2 + mu * mu2) \<odot> g2 +
                          (\<Sum>g\<in>G - {g1, g2}. (mu * q' g) \<odot> g)" by simp
  also have "\<dots> = (q g1 - mu * mu1 + mu * q' g1) \<odot> g1 + (q g2 + mu * q' g2 + mu * mu2) \<odot> g2 +
                    (\<Sum>g\<in>G - {g1, g2}. (q g + mu * q' g) \<odot> g)"
    by (simp add: r algebra_simps flip: sum.distrib)
  also have "q g1 - mu * mu1 = punit.tail (q g1)"
    by (simp only: mu_times_mu1 punit.leading_monomial_tail diff_eq_eq add.commute[of "punit.tail (q g1)"])
  finally have "r = q'' g1 \<odot> g1 + q'' g2 \<odot> g2 + (\<Sum>g\<in>G - {g1} - {g2}. q'' g \<odot> g)"
    using \<open>g1 \<noteq> g2\<close> by (simp add: q''_def flip: Diff_insert2)
  also from \<open>finite G\<close> \<open>g1 \<noteq> g2\<close> \<open>g1 \<in> G\<close> \<open>g2 \<in> G\<close> have "\<dots> = (\<Sum>g\<in>G. q'' g \<odot> g)"
    by (simp add: sum.remove) (metis (no_types, lifting) finite_Diff insert_Diff insert_iff sum.remove)
  finally have r: "r = (\<Sum>g\<in>G. q'' g \<odot> g)" .

  have 1: "lt ((mu * q' g) \<odot> g) \<prec>\<^sub>t v" if "(mu * q' g) \<odot> g \<noteq> 0" for g
  proof -
    from that have "q' g \<odot> g \<noteq> 0" by (auto simp: mult_scalar_assoc)
    hence *: "lt (q' g \<odot> g) \<prec>\<^sub>t ?v" by fact
    from \<open>q' g \<odot> g \<noteq> 0\<close> \<open>mu \<noteq> 0\<close> have "lt ((mu * q' g) \<odot> g) = (lp (q g1 \<odot> g1) - ?l) \<oplus> lt (q' g \<odot> g)"
      by (simp add: mult_scalar_assoc lt_mult_scalar) (simp add: mu_def punit.lt_monomial monomial_0_iff)
    also from * have "\<dots> \<prec>\<^sub>t (lp (q g1 \<odot> g1) - ?l) \<oplus> ?v" by (rule splus_mono_strict)
    also from l_adds have "\<dots> = v" by (simp add: splus_def minus_plus term_simps v1' flip: cmp_eq v1)
    finally show ?thesis .
  qed

  have 2: "lt (q'' g1 \<odot> g1) \<prec>\<^sub>t v" if "q'' g1 \<odot> g1 \<noteq> 0" using that
  proof (rule lt_less)
    fix u
    assume "v \<preceq>\<^sub>t u"
    have "u \<notin> keys (q'' g1 \<odot> g1)"
    proof
      assume "u \<in> keys (q'' g1 \<odot> g1)"
      also from \<open>g1 \<noteq> g2\<close> have "\<dots> = keys ((punit.tail (q g1) + mu * q' g1) \<odot> g1)"
        by (simp add: q''_def)
      also have "\<dots> \<subseteq> keys (punit.tail (q g1) \<odot> g1) \<union> keys ((mu * q' g1) \<odot> g1)"
        unfolding mult_scalar_distrib_right by (fact Poly_Mapping.keys_add)
      finally show False
      proof
        assume "u \<in> keys (punit.tail (q g1) \<odot> g1)"
        hence "u \<preceq>\<^sub>t lt (punit.tail (q g1) \<odot> g1)" by (rule lt_max_keys)
        also have "\<dots> \<preceq>\<^sub>t punit.lt (punit.tail (q g1)) \<oplus> lt g1"
          by (metis in_keys_mult_scalar_le lt_def lt_in_keys min_term_min)
        also have "\<dots> \<prec>\<^sub>t punit.lt (q g1) \<oplus> lt g1"
        proof (intro splus_mono_strict_left punit.lt_tail notI)
          assume "punit.tail (q g1) = 0"
          with \<open>u \<in> keys (punit.tail (q g1) \<odot> g1)\<close> show False by simp
        qed
        also have "\<dots> = v" by (simp only: v1')
        finally show ?thesis using \<open>v \<preceq>\<^sub>t u\<close> by simp
      next
        assume "u \<in> keys ((mu * q' g1) \<odot> g1)"
        hence "(mu * q' g1) \<odot> g1 \<noteq> 0" and "u \<preceq>\<^sub>t lt ((mu * q' g1) \<odot> g1)" by (auto intro: lt_max_keys)
        note this(2)
        also from \<open>(mu * q' g1) \<odot> g1 \<noteq> 0\<close> have "lt ((mu * q' g1) \<odot> g1) \<prec>\<^sub>t v" by (rule 1)
        finally show ?thesis using \<open>v \<preceq>\<^sub>t u\<close> by simp
      qed
    qed
    thus "lookup (q'' g1 \<odot> g1) u = 0" by (simp add: in_keys_iff)
  qed

  have 3: "lt (q'' g2 \<odot> g2) \<preceq>\<^sub>t v"
  proof (rule lt_le)
    fix u
    assume "v \<prec>\<^sub>t u"
    have "u \<notin> keys (q'' g2 \<odot> g2)"
    proof
      assume "u \<in> keys (q'' g2 \<odot> g2)"
      also have "\<dots> = keys ((q g2 + mu * q' g2 + mu * mu2) \<odot> g2)" by (simp add: q''_def)
      also have "\<dots> \<subseteq> keys (q g2 \<odot> g2 + (mu * q' g2) \<odot> g2) \<union> keys ((mu * mu2) \<odot> g2)"
        unfolding mult_scalar_distrib_right by (fact Poly_Mapping.keys_add)
      finally show False
      proof
        assume "u \<in> keys (q g2 \<odot> g2 + (mu * q' g2) \<odot> g2)"
        also have "\<dots> \<subseteq> keys (q g2 \<odot> g2) \<union> keys ((mu * q' g2) \<odot> g2)" by (fact Poly_Mapping.keys_add)
        finally show ?thesis
        proof
          assume "u \<in> keys (q g2 \<odot> g2)"
          hence "u \<preceq>\<^sub>t lt (q g2 \<odot> g2)" by (rule lt_max_keys)
          with \<open>v \<prec>\<^sub>t u\<close> show ?thesis by (simp add: v2)
        next
          assume "u \<in> keys ((mu * q' g2) \<odot> g2)"
          hence "(mu * q' g2) \<odot> g2 \<noteq> 0" and "u \<preceq>\<^sub>t lt ((mu * q' g2) \<odot> g2)" by (auto intro: lt_max_keys)
          note this(2)
          also from \<open>(mu * q' g2) \<odot> g2 \<noteq> 0\<close> have "lt ((mu * q' g2) \<odot> g2) \<prec>\<^sub>t v" by (rule 1)
          finally show ?thesis using \<open>v \<prec>\<^sub>t u\<close> by simp
        qed
      next
        assume "u \<in> keys ((mu * mu2) \<odot> g2)"
        hence "(mu * mu2) \<odot> g2 \<noteq> 0" and "u \<preceq>\<^sub>t lt ((mu * mu2) \<odot> g2)" by (auto intro: lt_max_keys)
        from this(1) have "(mu * mu2) \<noteq> 0" by auto
        note \<open>u \<preceq>\<^sub>t _\<close>
        also from \<open>mu * mu2 \<noteq> 0\<close> \<open>g2 \<noteq> 0\<close> have "lt ((mu * mu2) \<odot> g2) = punit.lt (q g2) \<oplus> lt g2"
          by (simp add: lt_mult_scalar) (simp add: mu_times_mu2 punit.lt_monomial monomial_0_iff)
        finally show ?thesis using \<open>v \<prec>\<^sub>t u\<close> by (simp add: v2')
      qed
    qed
    thus "lookup (q'' g2 \<odot> g2) u = 0" by (simp add: in_keys_iff)
  qed

  have 4: "lt (q'' g \<odot> g) \<preceq>\<^sub>t v" if "g \<in> M" for g
  proof (cases "g \<in> {g1, g2}")
    case True
    hence "g = g1 \<or> g = g2" by simp
    thus ?thesis
    proof
      assume "g = g1"
      show ?thesis
      proof (cases "q'' g1 \<odot> g1 = 0")
        case True
        thus ?thesis by (simp add: \<open>g = g1\<close> min_term_min)
      next
        case False
        hence "lt (q'' g \<odot> g) \<prec>\<^sub>t v" unfolding \<open>g = g1\<close> by (rule 2)
        thus ?thesis by simp
      qed
    next
      assume "g = g2"
      with 3 show ?thesis by simp
    qed
  next
    case False
    hence q'': "q'' g = q g + mu * q' g" by (simp add: q''_def)
    show ?thesis
    proof (rule lt_le)
      fix u
      assume "v \<prec>\<^sub>t u"
      have "u \<notin> keys (q'' g \<odot> g)"
      proof
        assume "u \<in> keys (q'' g \<odot> g)"
        also have "\<dots> \<subseteq> keys (q g \<odot> g) \<union> keys ((mu * q' g) \<odot> g)"
          unfolding q'' mult_scalar_distrib_right by (fact Poly_Mapping.keys_add)
        finally show False
        proof
          assume "u \<in> keys (q g \<odot> g)"
          hence "u \<preceq>\<^sub>t lt (q g \<odot> g)" by (rule lt_max_keys)
          with \<open>g \<in> M\<close> \<open>v \<prec>\<^sub>t u\<close> show ?thesis by (simp add: M_def)
        next
          assume "u \<in> keys ((mu * q' g) \<odot> g)"
          hence "(mu * q' g) \<odot> g \<noteq> 0" and "u \<preceq>\<^sub>t lt ((mu * q' g) \<odot> g)" by (auto intro: lt_max_keys)
          note this(2)
          also from \<open>(mu * q' g) \<odot> g \<noteq> 0\<close> have "lt ((mu * q' g) \<odot> g) \<prec>\<^sub>t v" by (rule 1)
          finally show ?thesis using \<open>v \<prec>\<^sub>t u\<close> by simp
        qed
      qed
      thus "lookup (q'' g \<odot> g) u = 0" by (simp add: in_keys_iff)
    qed
  qed

  have 5: "lt (q'' g \<odot> g) \<prec>\<^sub>t v" if "g \<in> G" and "g \<notin> M" and "q'' g \<odot> g \<noteq> 0" for g using that(3)
  proof (rule lt_less)
    fix u
    assume "v \<preceq>\<^sub>t u"
    from that(2) \<open>g1 \<in> M\<close> \<open>g2 \<in> M\<close> have "g \<noteq> g1" and "g \<noteq> g2" by blast+
    hence q'': "q'' g = q g + mu * q' g" by (simp add: q''_def)
    have "u \<notin> keys (q'' g \<odot> g)"
    proof
      assume "u \<in> keys (q'' g \<odot> g)"
      also have "\<dots> \<subseteq> keys (q g \<odot> g) \<union> keys ((mu * q' g) \<odot> g)"
        unfolding q'' mult_scalar_distrib_right by (fact Poly_Mapping.keys_add)
      finally show False
      proof
        assume "u \<in> keys (q g \<odot> g)"
        hence "q g \<odot> g \<noteq> 0" and "u \<preceq>\<^sub>t lt (q g \<odot> g)" by (auto intro: lt_max_keys)
        note this(2)
        also from that(1, 2) \<open>q g \<odot> g \<noteq> 0\<close> have "\<dots> \<prec>\<^sub>t v" by (rule v_max)
        finally show ?thesis using \<open>v \<preceq>\<^sub>t u\<close> by simp
      next
        assume "u \<in> keys ((mu * q' g) \<odot> g)"
        hence "(mu * q' g) \<odot> g \<noteq> 0" and "u \<preceq>\<^sub>t lt ((mu * q' g) \<odot> g)" by (auto intro: lt_max_keys)
        note this(2)
        also from \<open>(mu * q' g) \<odot> g \<noteq> 0\<close> have "lt ((mu * q' g) \<odot> g) \<prec>\<^sub>t v" by (rule 1)
        finally show ?thesis using \<open>v \<preceq>\<^sub>t u\<close> by simp
      qed
    qed
    thus "lookup (q'' g \<odot> g) u = 0" by (simp add: in_keys_iff)
  qed

  define u where "u = mlt q''"
  have u_in: "u \<in> lt ` {q'' g \<odot> g | g. g \<in> G \<and> q'' g \<odot> g \<noteq> 0}" unfolding u_def mlt_def
  proof (rule ord_term_lin.Max_in, simp_all add: assms(3), rule ccontr)
    assume "\<nexists>g. g \<in> G \<and> q'' g \<odot> g \<noteq> 0"
    hence "q'' g \<odot> g = 0" if "g \<in> G" for g using that by simp
    hence "r = 0" by (simp add: r)
    with \<open>r \<noteq> 0\<close> show False ..
  qed
  have u_max: "lt (q'' g \<odot> g) \<preceq>\<^sub>t u" if "g \<in> G" for g
  proof (cases "q'' g \<odot> g = 0")
    case True
    thus ?thesis by (simp add: min_term_min)
  next
    case False
    show ?thesis unfolding u_def mlt_def
      by (rule ord_term_lin.Max_ge) (auto simp: assms(3) False intro!: imageI \<open>g \<in> G\<close>)
  qed
  have "q'' \<in> rel_dom"
  proof (simp add: rel_dom_def r, intro subsetI, elim imageE)
    fix g
    assume "g \<in> G"
    from assms(1) l_adds have "d (lp (q g1 \<odot> g1) - ?l) \<le> d (lp (q g1 \<odot> g1))"
      by (rule dickson_grading_minus)
    also have "\<dots> = d (punit.lt (q g1) + lp g1)" by (simp add: v1' term_simps flip: v1)
    also from assms(1) have "\<dots> = ord_class.max (d (punit.lt (q g1))) (d (lp g1))"
      by (rule dickson_gradingD1)
    also have "\<dots> \<le> m'"
    proof (rule max.boundedI)
      from \<open>g1 \<in> G\<close> have "q g1 \<in> punit.dgrad_p_set d m'" by (rule q_in)
      moreover from \<open>q g1 \<noteq> 0\<close> have "punit.lt (q g1) \<in> keys (q g1)" by (rule punit.lt_in_keys)
      ultimately show "d (punit.lt (q g1)) \<le> m'" by (rule punit.dgrad_p_setD[simplified])
    next
      from \<open>g1 \<in> G\<close> G_sub have "g1 \<in> dgrad_p_set d m'" ..
      moreover from \<open>g1 \<noteq> 0\<close> have "lt g1 \<in> keys g1" by (rule lt_in_keys)
      ultimately show "d (lp g1) \<le> m'" by (rule dgrad_p_setD)
    qed
    finally have d1: "d (lp (q g1 \<odot> g1) - ?l) \<le> m'" .
    have "d (?l - lp g2) \<le> ord_class.max (d (lp g2)) (d (lp g1))"
      unfolding lcs_comm[of "lp g1"] using assms(1) by (rule dickson_grading_lcs_minus)
    also have "\<dots> \<le> m'"
    proof (rule max.boundedI)
      from \<open>g2 \<in> G\<close> G_sub have "g2 \<in> dgrad_p_set d m'" ..
      moreover from \<open>g2 \<noteq> 0\<close> have "lt g2 \<in> keys g2" by (rule lt_in_keys)
      ultimately show "d (lp g2) \<le> m'" by (rule dgrad_p_setD)
    next
      from \<open>g1 \<in> G\<close> G_sub have "g1 \<in> dgrad_p_set d m'" ..
      moreover from \<open>g1 \<noteq> 0\<close> have "lt g1 \<in> keys g1" by (rule lt_in_keys)
      ultimately show "d (lp g1) \<le> m'" by (rule dgrad_p_setD)
    qed
    finally have mu2: "mu2 \<in> punit.dgrad_p_set d m'"
      by (simp add: mu2_def punit.dgrad_p_set_def dgrad_set_def)
    fix z
    assume z: "z = q'' g"
    have "g = g1 \<or> g = g2 \<or> (g \<noteq> g1 \<and> g \<noteq> g2)" by blast
    thus "z \<in> punit.dgrad_p_set d m'"
    proof (elim disjE conjE)
      assume "g = g1"
      with \<open>g1 \<noteq> g2\<close> have "q'' g = punit.tail (q g1) + mu * q' g1" by (simp add: q''_def)
      also have "\<dots> \<in> punit.dgrad_p_set d m'" unfolding mu_def times_monomial_left
        by (intro punit.dgrad_p_set_closed_plus punit.dgrad_p_set_closed_tail
                punit.dgrad_p_set_closed_monom_mult d1 assms(1) q_in q'_in \<open>g1 \<in> G\<close>)
      finally show ?thesis by (simp only: z)
    next
      assume "g = g2"
      hence "q'' g = q g2 + mu * q' g2 + mu * mu2" by (simp add: q''_def)
      also have "\<dots> \<in> punit.dgrad_p_set d m'" unfolding mu_def times_monomial_left
        by (intro punit.dgrad_p_set_closed_plus punit.dgrad_p_set_closed_monom_mult
                d1 mu2 q_in q'_in assms(1) \<open>g2 \<in> G\<close>)
      finally show ?thesis by (simp only: z)
    next
      assume "g \<noteq> g1" and "g \<noteq> g2"
      hence "q'' g = q g + mu * q' g" by (simp add: q''_def)
      also have "\<dots> \<in> punit.dgrad_p_set d m'" unfolding mu_def times_monomial_left
        by (intro punit.dgrad_p_set_closed_plus punit.dgrad_p_set_closed_monom_mult
                d1 assms(1) q_in q'_in \<open>g \<in> G\<close>)
      finally show ?thesis by (simp only: z)
    qed
  qed
  with q_min have "\<not> rel q'' q" by blast
  hence "v \<preceq>\<^sub>t u" and "u \<noteq> v \<or> mnum q \<le> mnum q''" by (auto simp: v_def u_def rel_def)
  moreover have "u \<preceq>\<^sub>t v"
  proof -
    from u_in obtain g where "g \<in> G" and "q'' g \<odot> g \<noteq> 0" and u: "u = lt (q'' g \<odot> g)" by blast
    show ?thesis
    proof (cases "g \<in> M")
      case True
      thus ?thesis unfolding u by (rule 4)
    next
      case False
      with \<open>g \<in> G\<close> have "lt (q'' g \<odot> g) \<prec>\<^sub>t v" using \<open>q'' g \<odot> g \<noteq> 0\<close> by (rule 5)
      thus ?thesis by (simp add: u)
    qed
  qed
  ultimately have u_v: "u = v" and "mnum q \<le> mnum q''" by simp_all
  note this(2)
  also have "mnum q'' < card M" unfolding mnum_def
  proof (rule psubset_card_mono)
    from \<open>M \<subseteq> G\<close> \<open>finite G\<close> show "finite M" by (rule finite_subset)
  next
    have "{g\<in>G. q'' g \<odot> g \<noteq> 0 \<and> lt (q'' g \<odot> g) = v} \<subseteq> M - {g1}"
    proof
      fix g
      assume "g \<in> {g\<in>G. q'' g \<odot> g \<noteq> 0 \<and> lt (q'' g \<odot> g) = v}"
      hence "g \<in> G" and "q'' g \<odot> g \<noteq> 0" and "lt (q'' g \<odot> g) = v" by simp_all
      with 2 5 show "g \<in> M - {g1}" by blast
    qed
    also from \<open>g1 \<in> M\<close> have "\<dots> \<subset> M" by blast
    finally show "{g\<in>G. q'' g \<odot> g \<noteq> 0 \<and> lt (q'' g \<odot> g) = mlt q''} \<subset> M"
      by (simp only: u_v flip: u_def)
  qed
  also have "\<dots> = mnum q" by (simp only: M_def mnum_def v_def)
  finally show False ..
qed

subsection \<open>Replacing Elements in Gr\"obner Bases\<close>

lemma replace_in_dgrad_p_set:
  assumes "G \<subseteq> dgrad_p_set d m"
  obtains n where "q \<in> dgrad_p_set d n" and "G \<subseteq> dgrad_p_set d n"
    and "insert q (G - {p}) \<subseteq> dgrad_p_set d n"
proof -
  from assms obtain n where "m \<le> n" and 1: "q \<in> dgrad_p_set d n" and 2: "G \<subseteq> dgrad_p_set d n"
    by (rule dgrad_p_set_insert)
  from this(2, 3) have "insert q (G - {p}) \<subseteq> dgrad_p_set d n" by auto
  with 1 2 show ?thesis ..
qed

lemma GB_replace_lt_adds_stable_GB_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "q \<noteq> 0" and q: "q \<in> (pmdl G)" and "lt q adds\<^sub>t lt p"
  shows "is_Groebner_basis (insert q (G - {p}))" (is "is_Groebner_basis ?G'")
proof -
  from assms(2) obtain n where 1: "G \<subseteq> dgrad_p_set d n" and 2: "?G' \<subseteq> dgrad_p_set d n"
    by (rule replace_in_dgrad_p_set)
  from isGB show ?thesis unfolding GB_alt_3_dgrad_p_set[OF assms(1) 1] GB_alt_3_dgrad_p_set[OF assms(1) 2]
  proof (intro ballI impI)
    fix f
    assume f1: "f \<in> (pmdl ?G')" and "f \<noteq> 0"
      and a1: "\<forall>f\<in>pmdl G. f \<noteq> 0 \<longrightarrow> (\<exists>g\<in>G. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f)"
    from f1 pmdl.replace_span[OF q, of p] have "f \<in> pmdl G" ..
    from a1[rule_format, OF this \<open>f \<noteq> 0\<close>] obtain g where "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t lt f" by auto
    show "\<exists>g\<in>?G'. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f"
    proof (cases "g = p")
      case True
      show ?thesis
      proof
        from \<open>lt q adds\<^sub>t lt p\<close> have "lt q adds\<^sub>t lt g" unfolding True .
        also have "... adds\<^sub>t lt f" by fact
        finally have "lt q adds\<^sub>t lt f" .
        with \<open>q \<noteq> 0\<close> show "q \<noteq> 0 \<and> lt q adds\<^sub>t lt f" ..
      next
        show "q \<in> ?G'" by simp
      qed
    next
      case False
      show ?thesis
      proof
        show "g \<noteq> 0 \<and> lt g adds\<^sub>t lt f" by (rule, fact+)
      next
        from \<open>g \<in> G\<close> False show "g \<in> ?G'" by blast
      qed
    qed
  qed
qed
  
lemma GB_replace_lt_adds_stable_pmdl_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "q \<noteq> 0" and "q \<in> pmdl G" and "lt q adds\<^sub>t lt p"
  shows "pmdl (insert q (G - {p})) = pmdl G" (is "pmdl ?G' = pmdl G")
proof (rule, rule pmdl.replace_span, fact, rule)
  fix f
  assume "f \<in> pmdl G"
  note assms(1)
  moreover from assms(2) obtain n where "?G' \<subseteq> dgrad_p_set d n" by (rule replace_in_dgrad_p_set)
  moreover have "is_Groebner_basis ?G'" by (rule GB_replace_lt_adds_stable_GB_dgrad_p_set, fact+)
  ultimately have "\<exists>! h. (red ?G')\<^sup>*\<^sup>* f h \<and> \<not> is_red ?G' h" by (rule GB_implies_unique_nf_dgrad_p_set)
  then obtain h where ftoh: "(red ?G')\<^sup>*\<^sup>* f h" and irredh: "\<not> is_red ?G' h" by auto
  have "\<not> is_red G h"
  proof
    assume "is_red G h"
    have "is_red ?G' h" by (rule replace_lt_adds_stable_is_red, fact+)
    with irredh show False ..
  qed
  have "f - h \<in> pmdl ?G'" by (rule red_rtranclp_diff_in_pmdl, rule ftoh)
  have "f - h \<in> pmdl G" by (rule, fact, rule pmdl.replace_span, fact)
  from pmdl.span_diff[OF this \<open>f \<in> pmdl G\<close>] have "-h \<in> pmdl G" by simp
  from pmdl.span_neg[OF this] have "h \<in> pmdl G" by simp
  with isGB \<open>\<not> is_red G h\<close> have "h = 0" using GB_imp_reducibility by auto
  with ftoh have "(red ?G')\<^sup>*\<^sup>* f 0" by simp
  thus "f \<in> pmdl ?G'" by (simp add: red_rtranclp_0_in_pmdl)
qed
  
lemma GB_replace_red_stable_GB_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and q: "red (G - {p}) p q"
  shows "is_Groebner_basis (insert q (G - {p}))" (is "is_Groebner_basis ?G'")
proof -
  from assms(2) obtain n where 1: "G \<subseteq> dgrad_p_set d n" and 2: "?G' \<subseteq> dgrad_p_set d n"
    by (rule replace_in_dgrad_p_set)
  from isGB show ?thesis unfolding GB_alt_2_dgrad_p_set[OF assms(1) 1] GB_alt_2_dgrad_p_set[OF assms(1) 2]
  proof (intro ballI impI)
    fix f
    assume f1: "f \<in> (pmdl ?G')" and "f \<noteq> 0"
      and a1: "\<forall>f\<in>pmdl G. f \<noteq> 0 \<longrightarrow> is_red G f"
    have "q \<in> pmdl G"
    proof (rule pmdl_closed_red, rule pmdl.span_mono)
      from pmdl.span_superset \<open>p \<in> G\<close> show "p \<in> pmdl G" ..
    next
      show "G - {p} \<subseteq> G" by (rule Diff_subset)
    qed (rule q)
    from f1 pmdl.replace_span[OF this, of p] have "f \<in> pmdl G" ..
    have "is_red G f" by (rule a1[rule_format], fact+)
    show "is_red ?G' f" by (rule replace_red_stable_is_red, fact+)
  qed
qed

lemma GB_replace_red_stable_pmdl_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and ptoq: "red (G - {p}) p q"
  shows "pmdl (insert q (G - {p})) = pmdl G" (is "pmdl ?G' = _")
proof -
  from \<open>p \<in> G\<close> pmdl.span_superset have "p \<in> pmdl G" ..
  have "q \<in> pmdl G"
    by (rule pmdl_closed_red, rule pmdl.span_mono, rule Diff_subset, rule \<open>p \<in> pmdl G\<close>, rule ptoq)
  show ?thesis
  proof (rule, rule pmdl.replace_span, fact, rule)
    fix f
    assume "f \<in> pmdl G"
    note assms(1)
    moreover from assms(2) obtain n where "?G' \<subseteq> dgrad_p_set d n" by (rule replace_in_dgrad_p_set)
    moreover have "is_Groebner_basis ?G'" by (rule GB_replace_red_stable_GB_dgrad_p_set, fact+)
    ultimately have "\<exists>! h. (red ?G')\<^sup>*\<^sup>* f h \<and> \<not> is_red ?G' h" by (rule GB_implies_unique_nf_dgrad_p_set)
    then obtain h where ftoh: "(red ?G')\<^sup>*\<^sup>* f h" and irredh: "\<not> is_red ?G' h" by auto
    have "\<not> is_red G h"
    proof
      assume "is_red G h"
      have "is_red ?G' h" by (rule replace_red_stable_is_red, fact+)
      with irredh show False ..
    qed
    have "f - h \<in> pmdl ?G'" by (rule red_rtranclp_diff_in_pmdl, rule ftoh)
    have "f - h \<in> pmdl G" by (rule, fact, rule pmdl.replace_span, fact)
    from pmdl.span_diff[OF this \<open>f \<in> pmdl G\<close>] have "-h \<in> pmdl G" by simp
    from pmdl.span_neg[OF this] have "h \<in> pmdl G" by simp
    with isGB \<open>\<not> is_red G h\<close> have "h = 0" using GB_imp_reducibility by auto
    with ftoh have "(red ?G')\<^sup>*\<^sup>* f 0" by simp
    thus "f \<in> pmdl ?G'" by (simp add: red_rtranclp_0_in_pmdl)
  qed
qed
  
lemma GB_replace_red_rtranclp_stable_GB_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and ptoq: "(red (G - {p}))\<^sup>*\<^sup>* p q"
  shows "is_Groebner_basis (insert q (G - {p}))"
  using ptoq
proof (induct q rule: rtranclp_induct)
  case base
  from isGB \<open>p \<in> G\<close> show ?case by (simp add: insert_absorb)
next
  case (step y z)
  show ?case
  proof (cases "y = p")
    case True
    from assms(1) assms(2) isGB \<open>p \<in> G\<close> show ?thesis
    proof (rule GB_replace_red_stable_GB_dgrad_p_set)
      from \<open>red (G - {p}) y z\<close> show "red (G - {p}) p z" unfolding True .
    qed
  next
    case False
    show ?thesis
      proof (cases "y \<in> G")
        case True
        with \<open>y \<noteq> p\<close> have "y \<in> G - {p}" (is "_ \<in> ?G'") by blast
        hence "insert y (G - {p}) = ?G'" by auto
        with step(3) have "is_Groebner_basis ?G'" by simp
        from \<open>y \<in> ?G'\<close> pmdl.span_superset have "y \<in> pmdl ?G'" ..
        have "z \<in> pmdl ?G'" by (rule pmdl_closed_red, rule subset_refl, fact+)
        show "is_Groebner_basis (insert z ?G')" by (rule GB_insert, fact+)
      next
        case False
        from assms(2) obtain n where "insert y (G - {p}) \<subseteq> dgrad_p_set d n"
            by (rule replace_in_dgrad_p_set)
        from assms(1) this step(3) have "is_Groebner_basis (insert z (insert y (G - {p}) - {y}))"
        proof (rule GB_replace_red_stable_GB_dgrad_p_set)
          from \<open>red (G - {p}) y z\<close> False show "red ((insert y (G - {p})) - {y}) y z" by simp
        qed simp
        moreover from False have "... = (insert z (G - {p}))" by simp
        ultimately show ?thesis by simp
      qed
  qed
qed

lemma GB_replace_red_rtranclp_stable_pmdl_dgrad_p_set:
  assumes "dickson_grading d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and ptoq: "(red (G - {p}))\<^sup>*\<^sup>* p q"
  shows "pmdl (insert q (G - {p})) = pmdl G"
  using ptoq
proof (induct q rule: rtranclp_induct)
  case base
  from \<open>p \<in> G\<close> show ?case by (simp add: insert_absorb)
next
  case (step y z)
  show ?case
  proof (cases "y = p")
    case True
    from assms(1) assms(2) isGB \<open>p \<in> G\<close> step(2) show ?thesis unfolding True
      by (rule GB_replace_red_stable_pmdl_dgrad_p_set)
  next
    case False
    have gb: "is_Groebner_basis (insert y (G - {p}))"
      by (rule GB_replace_red_rtranclp_stable_GB_dgrad_p_set, fact+)
    show ?thesis
    proof (cases "y \<in> G")
      case True
      with \<open>y \<noteq> p\<close> have "y \<in> G - {p}" (is "_ \<in> ?G'") by blast
      hence eq: "insert y ?G' = ?G'" by auto
      from \<open>y \<in> ?G'\<close> have "y \<in> pmdl ?G'" by (rule pmdl.span_base)
      have "z \<in> pmdl ?G'" by (rule pmdl_closed_red, rule subset_refl, fact+)
      hence "pmdl (insert z ?G') = pmdl ?G'" by (rule pmdl.span_insert_idI)
      also from step(3) have "... = pmdl G" by (simp only: eq)
      finally show ?thesis .
    next
      case False
      from assms(2) obtain n where 1: "insert y (G - {p}) \<subseteq> dgrad_p_set d n"
        by (rule replace_in_dgrad_p_set)
      from False have "pmdl (insert z (G - {p})) = pmdl (insert z (insert y (G - {p}) - {y}))"
        by auto
      also from assms(1) 1 gb have "... = pmdl (insert y (G - {p}))"
      proof (rule GB_replace_red_stable_pmdl_dgrad_p_set)
        from step(2) False show "red ((insert y (G - {p})) - {y}) y z" by simp
      qed simp
      also have "... = pmdl G" by fact
      finally show ?thesis .
    qed
  qed
qed

lemmas GB_replace_lt_adds_stable_GB_finite =
  GB_replace_lt_adds_stable_GB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_lt_adds_stable_pmdl_finite =
  GB_replace_lt_adds_stable_pmdl_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_red_stable_GB_finite =
  GB_replace_red_stable_GB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_red_stable_pmdl_finite =
  GB_replace_red_stable_pmdl_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_red_rtranclp_stable_GB_finite =
  GB_replace_red_rtranclp_stable_GB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_red_rtranclp_stable_pmdl_finite =
  GB_replace_red_rtranclp_stable_pmdl_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

subsection \<open>An Inconstructive Proof of the Existence of Finite Gr\"obner Bases\<close>

lemma ex_finite_GB_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  obtains G where "G \<subseteq> dgrad_p_set d m" and "finite G" and "is_Groebner_basis G" and "pmdl G = pmdl F"
proof -
  define S where "S = {lt f | f. f \<in> pmdl F \<and> f \<in> dgrad_p_set d m \<and> f \<noteq> 0}"
  note assms(1)
  moreover from _ assms(2) have "finite (component_of_term ` S)"
  proof (rule finite_subset)
    have "component_of_term ` S \<subseteq> component_of_term ` Keys (pmdl F)"
      by (rule image_mono, rule, auto simp add: S_def intro!: in_KeysI lt_in_keys)
    thus "component_of_term ` S \<subseteq> component_of_term ` Keys F" by (simp only: components_pmdl)
  qed
  moreover have "pp_of_term ` S \<subseteq> dgrad_set d m"
  proof
    fix s
    assume "s \<in> pp_of_term ` S"
    then obtain u where "u \<in> S" and "s = pp_of_term u" ..
    from this(1) obtain f where "f \<in> pmdl F \<and> f \<in> dgrad_p_set d m \<and> f \<noteq> 0" and u: "u = lt f"
      unfolding S_def by blast
    from this(1) have "f \<in> dgrad_p_set d m" and "f \<noteq> 0" by simp_all
    have "u \<in> keys f" unfolding u by (rule lt_in_keys, fact)
    with \<open>f \<in> dgrad_p_set d m\<close> have "d (pp_of_term u) \<le> m" unfolding u by (rule dgrad_p_setD)
    thus "s \<in> dgrad_set d m" by (simp add: \<open>s = pp_of_term u\<close> dgrad_set_def)
  qed
  ultimately obtain T where "finite T" and "T \<subseteq> S" and *: "\<And>s. s \<in> S \<Longrightarrow> (\<exists>t\<in>T. t adds\<^sub>t s)"
    by (rule ex_finite_adds_term, blast)
  define crit where "crit = (\<lambda>t f. f \<in> pmdl F \<and> f \<in> dgrad_p_set d m \<and> f \<noteq> 0 \<and> t = lt f)"
  have ex_crit: "t \<in> T \<Longrightarrow> (\<exists>f. crit t f)" for t
  proof -
    assume "t \<in> T"
    from this \<open>T \<subseteq> S\<close> have "t \<in> S" ..
    then obtain f where "f \<in> pmdl F \<and> f \<in> dgrad_p_set d m \<and> f \<noteq> 0" and "t = lt f"
      unfolding S_def by blast
    thus "\<exists>f. crit t f" unfolding crit_def by blast
  qed
  define G where "G = (\<lambda>t. SOME g. crit t g) ` T"
  have G: "g \<in> G \<Longrightarrow> g \<in> pmdl F \<and> g \<in> dgrad_p_set d m \<and> g \<noteq> 0" for g
  proof -
    assume "g \<in> G"
    then obtain t where "t \<in> T" and g: "g = (SOME h. crit t h)" unfolding G_def ..
    have "crit t g" unfolding g by (rule someI_ex, rule ex_crit, fact)
    thus "g \<in> pmdl F \<and> g \<in> dgrad_p_set d m \<and> g \<noteq> 0" by (simp add: crit_def)
  qed
  have **: "t \<in> T \<Longrightarrow> (\<exists>g\<in>G. lt g = t)" for t
  proof -
    assume "t \<in> T"
    define g where "g = (SOME h. crit t h)"
    from \<open>t \<in> T\<close> have "g \<in> G" unfolding g_def G_def by blast
    thus "\<exists>g\<in>G. lt g = t"
    proof
      have "crit t g" unfolding g_def by (rule someI_ex, rule ex_crit, fact)
      thus "lt g = t" by (simp add: crit_def)
    qed
  qed
  have adds: "f \<in> pmdl F \<Longrightarrow> f \<in> dgrad_p_set d m \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> (\<exists>g\<in>G. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f)" for f
  proof -
    assume "f \<in> pmdl F" and "f \<in> dgrad_p_set d m" and "f \<noteq> 0"
    hence "lt f \<in> S" unfolding S_def by blast
    hence "\<exists>t\<in>T. t adds\<^sub>t (lt f)" by (rule *)
    then obtain t where "t \<in> T" and "t adds\<^sub>t (lt f)" ..
    from this(1) have "\<exists>g\<in>G. lt g = t" by (rule **)
    then obtain g where "g \<in> G" and "lt g = t" ..
    show "\<exists>g\<in>G. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f"
    proof (intro bexI conjI)
      from G[OF \<open>g \<in> G\<close>] show "g \<noteq> 0" by (elim conjE)
    next
      from \<open>t adds\<^sub>t lt f\<close> show "lt g adds\<^sub>t lt f" by (simp only: \<open>lt g = t\<close>)
    qed fact
  qed
  have sub1: "pmdl G \<subseteq> pmdl F"
  proof (rule pmdl.span_subset_spanI, rule)
    fix g
    assume "g \<in> G"
    from G[OF this] show "g \<in> pmdl F" ..
  qed
  have sub2: "G \<subseteq> dgrad_p_set d m"
  proof
    fix g
    assume "g \<in> G"
    from G[OF this] show "g \<in> dgrad_p_set d m" by (elim conjE)
  qed
  show ?thesis
  proof
    from \<open>finite T\<close> show "finite G" unfolding G_def ..
  next
    from assms(1) sub2 adds show "is_Groebner_basis G"
    proof (rule isGB_I_adds_lt)
      fix f
      assume "f \<in> pmdl G"
      from this sub1 show "f \<in> pmdl F" ..
    qed
  next
    show "pmdl G = pmdl F"
    proof
      show "pmdl F \<subseteq> pmdl G"
      proof (rule pmdl.span_subset_spanI, rule)
        fix f
        assume "f \<in> F"
        hence "f \<in> pmdl F" by (rule pmdl.span_base)
        from \<open>f \<in> F\<close> assms(3) have "f \<in> dgrad_p_set d m" ..
        with assms(1) sub2 sub1 _ \<open>f \<in> pmdl F\<close> have "(red G)\<^sup>*\<^sup>* f 0"
        proof (rule is_red_implies_0_red_dgrad_p_set)
          fix q
          assume "q \<in> pmdl F" and "q \<in> dgrad_p_set d m" and "q \<noteq> 0"
          hence "(\<exists>g \<in> G. g \<noteq> 0 \<and> lt g adds\<^sub>t lt q)" by (rule adds)
          then obtain g where "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t lt q" by blast
          thus "is_red G q" using \<open>q \<noteq> 0\<close> is_red_indI1 by blast
        qed
        thus "f \<in> pmdl G" by (rule red_rtranclp_0_in_pmdl)
      qed
    qed fact
  next
    show "G \<subseteq> dgrad_p_set d m"
    proof
      fix g
      assume "g \<in> G"
      hence "g \<in> pmdl F \<and> g \<in> dgrad_p_set d m \<and> g \<noteq> 0" by (rule G)
      thus "g \<in> dgrad_p_set d m" by (elim conjE)
    qed
  qed
qed

text \<open>The preceding lemma justifies the following definition.\<close>

definition some_GB :: "('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) set"
  where "some_GB F = (SOME G. finite G \<and> is_Groebner_basis G \<and> pmdl G = pmdl F)"

lemma some_GB_props_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "finite (some_GB F) \<and> is_Groebner_basis (some_GB F) \<and> pmdl (some_GB F) = pmdl F"
proof -
  from assms obtain G where "finite G" and "is_Groebner_basis G" and "pmdl G = pmdl F"
    by (rule ex_finite_GB_dgrad_p_set)
  hence "finite G \<and> is_Groebner_basis G \<and> pmdl G = pmdl F" by simp
  thus "finite (some_GB F) \<and> is_Groebner_basis (some_GB F) \<and> pmdl (some_GB F) = pmdl F"
    unfolding some_GB_def by (rule someI)
qed

lemma finite_some_GB_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "finite (some_GB F)"
  using some_GB_props_dgrad_p_set[OF assms] ..

lemma some_GB_isGB_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "is_Groebner_basis (some_GB F)"
  using some_GB_props_dgrad_p_set[OF assms] by (elim conjE)

lemma some_GB_pmdl_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "pmdl (some_GB F) = pmdl F"
  using some_GB_props_dgrad_p_set[OF assms] by (elim conjE)

lemma finite_imp_finite_component_Keys:
  assumes "finite F"
  shows "finite (component_of_term ` Keys F)"
  by (rule finite_imageI, rule finite_Keys, fact)

lemma finite_some_GB_finite: "finite F \<Longrightarrow> finite (some_GB F)"
  by (rule finite_some_GB_dgrad_p_set, rule dickson_grading_dgrad_dummy,
      erule finite_imp_finite_component_Keys, erule dgrad_p_set_exhaust_expl)

lemma some_GB_isGB_finite: "finite F \<Longrightarrow> is_Groebner_basis (some_GB F)"
  by (rule some_GB_isGB_dgrad_p_set, rule dickson_grading_dgrad_dummy,
      erule finite_imp_finite_component_Keys, erule dgrad_p_set_exhaust_expl)

lemma some_GB_pmdl_finite: "finite F \<Longrightarrow> pmdl (some_GB F) = pmdl F"
  by (rule some_GB_pmdl_dgrad_p_set, rule dickson_grading_dgrad_dummy,
      erule finite_imp_finite_component_Keys, erule dgrad_p_set_exhaust_expl)

text \<open>Theory \<open>Buchberger\<close> implements an algorithm for effectively computing Gr\"obner bases.\<close>

subsection \<open>Relation \<open>red_supset\<close>\<close>

text \<open>The following relation is needed for proving the termination of Buchberger's algorithm (i.\,e.
  function \<open>gb_schema_aux\<close>).\<close>

definition red_supset::"('t \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> bool" (infixl "\<sqsupset>p" 50)
  where "red_supset A B \<equiv> (\<exists>p. is_red A p \<and> \<not> is_red B p) \<and> (\<forall>p. is_red B p \<longrightarrow> is_red A p)"

lemma red_supsetE:
  assumes "A \<sqsupset>p B"
  obtains p where "is_red A p" and "\<not> is_red B p"
proof -
  from assms have "\<exists>p. is_red A p \<and> \<not> is_red B p" by (simp add: red_supset_def)
  from this obtain p where "is_red A p" and " \<not> is_red B p" by auto
  thus ?thesis ..
qed

lemma red_supsetD:
  assumes a1: "A \<sqsupset>p B" and a2: "is_red B p"
  shows "is_red A p"
proof -
  from assms have "\<forall>p. is_red B p \<longrightarrow> is_red A p" by (simp add: red_supset_def)
  hence "is_red B p \<longrightarrow> is_red A p" ..
  from a2 this show ?thesis by simp
qed

lemma red_supsetI [intro]:
  assumes "\<And>q. is_red B q \<Longrightarrow> is_red A q" and "is_red A p" and "\<not> is_red B p"
  shows "A \<sqsupset>p B"
  unfolding red_supset_def using assms by auto

lemma red_supset_insertI:
  assumes "x \<noteq> 0" and "\<not> is_red A x"
  shows "(insert x A) \<sqsupset>p A"
proof
  fix q
  assume "is_red A q"
  thus "is_red (insert x A) q" unfolding is_red_alt
  proof
    fix a
    assume "red A q a"
    from red_unionI2[OF this, of "{x}"] have "red (insert x A) q a" by simp
    show "\<exists>qa. red (insert x A) q qa"
    proof
      show "red (insert x A) q a" by fact
    qed
  qed
next
  show "is_red (insert x A) x" unfolding is_red_alt
  proof
    from red_unionI1[OF red_self[OF \<open>x \<noteq> 0\<close>], of A] show "red (insert x A) x 0" by simp
  qed
next
  show "\<not> is_red A x" by fact
qed

lemma red_supset_transitive:
  assumes "A \<sqsupset>p B" and "B \<sqsupset>p C"
  shows "A \<sqsupset>p C"
proof -
  from assms(2) obtain p where "is_red B p" and "\<not> is_red C p" by (rule red_supsetE)
  show ?thesis
  proof
    fix q
    assume "is_red C q"
    with assms(2) have "is_red B q" by (rule red_supsetD)
    with assms(1) show "is_red A q" by (rule red_supsetD)
  next
    from assms(1) \<open>is_red B p\<close> show "is_red A p" by (rule red_supsetD)
  qed fact
qed

lemma red_supset_wf_on:
  assumes "dickson_grading d" and "finite K"
  shows "wfp_on (\<sqsupset>p) (Pow (dgrad_p_set d m) \<inter> {F. component_of_term ` Keys F \<subseteq> K})"
proof (rule wfp_onI_chain, rule, erule exE)
  let ?A = "dgrad_p_set d m"
  fix f::"nat \<Rightarrow> (('t \<Rightarrow>\<^sub>0 'b) set)"
  assume "\<forall>i. f i \<in> Pow ?A \<inter> {F. component_of_term ` Keys F \<subseteq> K} \<and> f (Suc i) \<sqsupset>p f i"
  hence a1_subset: "f i \<subseteq> ?A" and comp_sub: "component_of_term ` Keys (f i) \<subseteq> K"
    and a1: "f (Suc i) \<sqsupset>p f i" for i by simp_all

  have a1_trans: "i < j \<Longrightarrow> f j \<sqsupset>p f i" for i j
  proof -
    assume "i < j"
    thus "f j \<sqsupset>p f i"
    proof (induct j)
      case 0
      thus ?case by simp
    next
      case (Suc j)
      from Suc(2) have "i = j \<or> i < j" by auto
      thus ?case
      proof
        assume "i = j"
        show ?thesis unfolding \<open>i = j\<close> by (fact a1)
      next
        assume "i < j"
        from a1 have "f (Suc j) \<sqsupset>p f j" .
        also from \<open>i < j\<close> have "... \<sqsupset>p f i" by (rule Suc(1))
        finally(red_supset_transitive) show ?thesis .
      qed
    qed
  qed

  have a2: "\<exists>p \<in> f (Suc i). \<exists>q. is_red {p} q \<and> \<not> is_red (f i) q" for i
  proof -
    from a1 have "f (Suc i) \<sqsupset>p f i" .
    then obtain q where red: "is_red (f (Suc i)) q" and irred: "\<not> is_red (f i) q"
      by (rule red_supsetE)
    from red obtain p where "p \<in> f (Suc i)" and "is_red {p} q" by (rule is_red_singletonI)
    show "\<exists>p\<in>f (Suc i). \<exists>q. is_red {p} q \<and> \<not> is_red (f i) q"
    proof
      show "\<exists>q. is_red {p} q \<and> \<not> is_red (f i) q"
      proof (intro exI, intro conjI)
        show "is_red {p} q" by fact
      qed (fact)
    next
      show "p \<in> f (Suc i)" by fact
    qed
  qed

  let ?P = "\<lambda>i p. p \<in> (f (Suc i)) \<and> (\<exists>q. is_red {p} q \<and> \<not> is_red (f i) q)"
  define g where "g \<equiv> \<lambda>i::nat. (SOME p. ?P i p)"
  have a3: "?P i (g i)" for i
  proof -
    from a2[of i] obtain gi where "gi \<in> f (Suc i)" and "\<exists>q. is_red {gi} q \<and> \<not> is_red (f i) q" ..
    show ?thesis unfolding g_def by (rule someI[of _ gi], intro conjI, fact+)
  qed

  have a4: "i < j \<Longrightarrow> \<not> lt (g i) adds\<^sub>t (lt (g j))" for i j
  proof
    assume "i < j" and adds: "lt (g i) adds\<^sub>t lt (g j)"
    from a3 have "\<exists>q. is_red {g j} q \<and> \<not> is_red (f j) q" ..
    then obtain q where redj: "is_red {g j} q" and "\<not> is_red (f j) q" by auto
    have *: "\<not> is_red (f (Suc i)) q"
    proof -
      from \<open>i < j\<close> have "i + 1 < j \<or> i + 1 = j" by auto
      thus ?thesis
      proof
        assume "i + 1 < j"
        from red_supsetD[OF a1_trans[rule_format, OF this], of q] \<open>\<not> is_red (f j) q\<close>
          show ?thesis by auto
      next
        assume "i + 1 = j"
        thus ?thesis using \<open>\<not> is_red (f j) q\<close> by simp
      qed
    qed
    from a3 have "g i \<in> f (i + 1)" and redi: "\<exists>q. is_red {g i} q \<and> \<not> is_red (f i) q" by simp_all
    have "\<not> is_red {g i} q"
    proof
      assume "is_red {g i} q"
      from is_red_singletonD[OF this \<open>g i \<in> f (i + 1)\<close>] * show False by simp
    qed
    have "g i \<noteq> 0"
    proof -
      from redi obtain q0 where "is_red {g i} q0" by auto
      from is_red_singleton_not_0[OF this] show ?thesis .
    qed
    from \<open>\<not> is_red {g i} q\<close> is_red_singleton_trans[OF redj adds \<open>g i \<noteq> 0\<close>] show False by simp
  qed

  from _ assms(2) have a5: "finite (component_of_term ` range (lt \<circ> g))"
  proof (rule finite_subset)
    show "component_of_term ` range (lt \<circ> g) \<subseteq> K"
    proof (rule, elim imageE, simp)
      fix i
      from a3 have "g i \<in> f (Suc i)" and "\<exists>q. is_red {g i} q \<and> \<not> is_red (f i) q" by simp_all
      from this(2) obtain q where "is_red {g i} q" by auto
      hence "g i \<noteq> 0" by (rule is_red_singleton_not_0)
      hence "lt (g i) \<in> keys (g i)" by (rule lt_in_keys)
      hence "component_of_term (lt (g i)) \<in> component_of_term ` keys (g i)" by simp
      also have "... \<subseteq> component_of_term ` Keys (f (Suc i))"
        by (rule image_mono, rule keys_subset_Keys, fact)
      also have "... \<subseteq> K" by (fact comp_sub)
      finally show "component_of_term (lt (g i)) \<in> K" .
    qed
  qed

  have a6: "pp_of_term ` range (lt \<circ> g) \<subseteq> dgrad_set d m"
  proof (rule, elim imageE, simp)
    fix i
    from a3 have "g i \<in> f (Suc i)" and "\<exists>q. is_red {g i} q \<and> \<not> is_red (f i) q" by simp_all
    from this(2) obtain q where "is_red {g i} q" by auto
    hence "g i \<noteq> 0" by (rule is_red_singleton_not_0)
    from a1_subset \<open>g i \<in> f (Suc i)\<close> have "g i \<in> ?A" ..
    from this \<open>g i \<noteq> 0\<close> have "d (lp (g i)) \<le> m" by (rule dgrad_p_setD_lp)
    thus "lp (g i) \<in> dgrad_set d m" by (rule dgrad_setI)
  qed

  from assms(1) a5 a6 obtain i j where "i < j" and "(lt \<circ> g) i adds\<^sub>t (lt \<circ> g) j" by (rule Dickson_termE)
  from this a4[OF \<open>i < j\<close>] show False by simp
qed

end (* gd_term *)

lemma in_lex_prod_alt:
  "(x, y) \<in> r <*lex*> s \<longleftrightarrow> (((fst x), (fst y)) \<in> r \<or> (fst x = fst y \<and> ((snd x), (snd y)) \<in> s))"
  by (metis in_lex_prod prod.collapse prod.inject surj_pair)

subsection \<open>Context @{locale od_term}\<close>

context od_term
begin

lemmas red_wf = red_wf_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]
lemmas Buchberger_criterion = Buchberger_criterion_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]

end (* od_term *)

end (* theory *)
