(* Author: Alexander Maletzky *)

section \<open>More Properties of Power-Products and Multivariate Polynomials\<close>

theory More_MPoly
  imports Prelims Polynomials.MPoly_Type_Class_Ordered
begin

subsection \<open>Power-Products\<close>

lemma (in comm_powerprod) minus_plus': "s adds t \<Longrightarrow> u + (t - s) = (u + t) - s"
  using add_commute minus_plus by auto

context ulcs_powerprod
begin

lemma lcs_alt_2:
  assumes "a + x = b + y"
  shows "lcs x y = (b + y) - gcs a b"
proof -
  have "a + (lcs x y + gcs a b) = lcs (a + x) (a + y) + gcs a b" by (simp only: lcs_plus_left ac_simps)
  also have "... = lcs (b + y) (a + y) + gcs a b" by (simp only: assms)
  also have "... = (lcs a b + y) + gcs a b" by (simp only: lcs_plus_right lcs_comm)
  also have "... = (gcs a b + lcs a b) + y" by (simp only: ac_simps)
  also have "... = a + (b + y)" by (simp only: gcs_plus_lcs, simp add: ac_simps)
  finally have "(lcs x y + gcs a b) - gcs a b = (b + y) - gcs a b" by simp
  thus ?thesis by simp
qed

corollary lcs_alt_1:
  assumes "a + x = b + y"
  shows "lcs x y = (a + x) - gcs a b"
proof -
  have "lcs x y = lcs y x" by (simp only: lcs_comm)
  also from assms[symmetric] have "... = (a + x) - gcs b a" by (rule lcs_alt_2)
  also have "... = (a + x) - gcs a b" by (simp only: gcs_comm)
  finally show ?thesis .
qed

corollary lcs_minus_1:
  assumes "a + x = b + y"
  shows "lcs x y - x = a - gcs a b"
  by (simp add: lcs_alt_1[OF assms] diff_right_commute)

corollary lcs_minus_2:
  assumes "a + x = b + y"
  shows "lcs x y - y = b - gcs a b"
  by (simp add: lcs_alt_2[OF assms] diff_right_commute)

lemma gcs_minus:
  assumes "u adds s" and "u adds t"
  shows "gcs (s - u) (t - u) = gcs s t - u"
proof -
  from assms have "gcs s t = gcs ((s - u) + u) ((t - u) + u)" by (simp add: minus_plus)
  also have "... = gcs (s - u) (t - u) + u" by (simp only: gcs_plus_right)
  finally show ?thesis by simp
qed

corollary gcs_minus_gcs: "gcs (s - (gcs s t)) (t - (gcs s t)) = 0"
  by (simp add: gcs_minus gcs_adds gcs_adds_2)

end (* ulcs_powerprod *)

subsection \<open>Miscellaneous\<close>

lemma poly_mapping_rangeE:
  assumes "c \<in> Poly_Mapping.range p"
  obtains k where "k \<in> keys p" and "c = lookup p k"
  using assms by (transfer, auto)

lemma poly_mapping_range_nonzero: "0 \<notin> Poly_Mapping.range p"
  by (transfer, auto)

lemma (in term_powerprod) Keys_range_vectorize_poly: "Keys (Poly_Mapping.range (vectorize_poly p)) = pp_of_term ` keys p"
proof
  show "Keys (Poly_Mapping.range (vectorize_poly p)) \<subseteq> pp_of_term ` keys p"
  proof
    fix t
    assume "t \<in> Keys (Poly_Mapping.range (vectorize_poly p))"
    then obtain q where "q \<in> Poly_Mapping.range (vectorize_poly p)" and "t \<in> keys q" by (rule in_KeysE)
    from this(1) obtain k where q: "q = lookup (vectorize_poly p) k" by (metis DiffE imageE range.rep_eq)
    with \<open>t \<in> keys q\<close> have "term_of_pair (t, k) \<in> keys p"
      by (metis in_keys_iff lookup_proj_poly lookup_vectorize_poly)
    hence "pp_of_term (term_of_pair (t, k)) \<in> pp_of_term ` keys p" by (rule imageI)
    thus "t \<in> pp_of_term ` keys p" by (simp only: pp_of_term_of_pair)
  qed
next
  show "pp_of_term ` keys p \<subseteq> Keys (Poly_Mapping.range (vectorize_poly p))"
  proof
    fix t
    assume "t \<in> pp_of_term ` keys p"
    then obtain x where "x \<in> keys p" and "t = pp_of_term x" ..
    from this(2) have "term_of_pair (t, component_of_term x) = x" by (simp add: term_of_pair_pair)
    with \<open>x \<in> keys p\<close> have "lookup p (term_of_pair (t, component_of_term x)) \<noteq> 0"
      by (simp add: in_keys_iff)
    hence "lookup (proj_poly (component_of_term x) p) t \<noteq> 0" by (simp add: lookup_proj_poly)
    hence t: "t \<in> keys (proj_poly (component_of_term x) p)"
      by (simp add: in_keys_iff)
    from \<open>x \<in> keys p\<close> have "component_of_term x \<in> keys (vectorize_poly p)"
      by (simp add: keys_vectorize_poly)
    from t show "t \<in> Keys (Poly_Mapping.range (vectorize_poly p))"
    proof (rule in_KeysI)
      have "proj_poly (component_of_term x) p = lookup (vectorize_poly p) (component_of_term x)"
        by (simp only: lookup_vectorize_poly)
      also from \<open>component_of_term x \<in> keys (vectorize_poly p)\<close>
      have "... \<in> Poly_Mapping.range (vectorize_poly p)" by (rule in_keys_lookup_in_range)
      finally show "proj_poly (component_of_term x) p \<in> Poly_Mapping.range (vectorize_poly p)" .
    qed
  qed
qed

subsection \<open>@{const ordered_term.lt} and @{const ordered_term.higher}\<close>

context ordered_term
begin

lemma lt_lookup_vectorize: "punit.lt (lookup (vectorize_poly p) (component_of_term (lt p))) = lp p"
proof (cases "p = 0")
  case True
  thus ?thesis by (simp add: vectorize_zero min_term_def pp_of_term_of_pair)
next
  case False
  show ?thesis
  proof (rule punit.lt_eqI_keys)
    from False have "lt p \<in> keys p" by (rule lt_in_keys)
    thus "lp p \<in> keys (lookup (vectorize_poly p) (component_of_term (lt p)))"
      by (simp add: lookup_vectorize_poly keys_proj_poly)
  next
    fix t
    assume "t \<in> keys (lookup (vectorize_poly p) (component_of_term (lt p)))"
    also have "... = pp_of_term ` {x\<in>keys p. component_of_term x = component_of_term (lt p)}"
      by (simp only: lookup_vectorize_poly keys_proj_poly)
    finally obtain v where "v \<in> keys p" and 1: "component_of_term v = component_of_term (lt p)"
      and t: "t = pp_of_term v" by auto
    from this(1) have "v \<preceq>\<^sub>t lt p" by (rule lt_max_keys)
    show "t \<preceq> lp p"
    proof (rule ccontr)
      assume "\<not> t \<preceq> lp p"
      hence "lp p \<prec> pp_of_term v" by (simp add: t)
      hence "lp p \<noteq> pp_of_term v" and "lp p \<preceq> pp_of_term v" by simp_all
      note this(2)
      moreover from 1 have "component_of_term (lt p) \<le> component_of_term v" by simp
      ultimately have "lt p \<preceq>\<^sub>t v" by (rule ord_termI)
      with \<open>v \<preceq>\<^sub>t lt p\<close> have "v = lt p" by (rule ord_term_lin.antisym)
      with \<open>lp p \<noteq> pp_of_term v\<close> show False by simp
    qed
  qed
qed

lemma lower_higher_zeroI: "u \<preceq>\<^sub>t v \<Longrightarrow> lower (higher p v) u = 0"
  by (simp add: lower_eq_zero_iff lookup_higher_when)

lemma lookup_minus_higher: "lookup (p - higher p v) u = (lookup p u when u \<preceq>\<^sub>t v)"
  by (auto simp: lookup_minus lookup_higher_when when_def)

lemma keys_minus_higher: "keys (p - higher p v) = {u \<in> keys p. u \<preceq>\<^sub>t v}"
  by (rule set_eqI, simp add: lookup_minus_higher conj_commute flip: lookup_not_eq_zero_eq_in_keys)

lemma lt_minus_higher: "v \<in> keys p \<Longrightarrow> lt (p - higher p v) = v"
  by (rule lt_eqI_keys, simp_all add: keys_minus_higher)

lemma lc_minus_higher: "v \<in> keys p \<Longrightarrow> lc (p - higher p v) = lookup p v"
  by (simp add: lc_def lt_minus_higher lookup_minus_higher)

lemma tail_minus_higher: "v \<in> keys p \<Longrightarrow> tail (p - higher p v) = lower p v"
  by (rule poly_mapping_eqI, simp add: lookup_tail_when lt_minus_higher lookup_lower_when lookup_minus_higher cong: when_cong)

end (* ordered_term *)

subsection \<open>@{const gd_term.dgrad_p_set}\<close>

lemma (in gd_term) dgrad_p_set_closed_mult_scalar:
  assumes "dickson_grading d" and "p \<in> punit.dgrad_p_set d m" and "r \<in> dgrad_p_set d m"
  shows "p \<odot> r \<in> dgrad_p_set d m"
proof (rule dgrad_p_setI)
  fix v
  assume "v \<in> keys (p \<odot> r)"
  then obtain t u where "t \<in> keys p" and "u \<in> keys r" and v: "v = t \<oplus> u"
    by (rule in_keys_mult_scalarE)
  from assms(2) \<open>t \<in> keys p\<close> have "d t \<le> m" by (rule punit.dgrad_p_setD[simplified])
  moreover from assms(3) \<open>u \<in> keys r\<close> have "d (pp_of_term u) \<le> m" by (rule dgrad_p_setD)
  ultimately have "d (t + pp_of_term u) \<le> m" using assms(1) by (simp add: dickson_gradingD1)
  thus "d (pp_of_term v) \<le> m" by (simp only: v pp_of_term_splus)
qed

subsection \<open>Regular Sequences\<close>

definition is_regular_sequence :: "('a::comm_powerprod \<Rightarrow>\<^sub>0 'b::comm_ring_1) list \<Rightarrow> bool"
  where "is_regular_sequence fs \<longleftrightarrow> (\<forall>j<length fs. \<forall>q. q * fs ! j \<in> ideal (set (take j fs)) \<longrightarrow>
                                                      q \<in> ideal (set (take j fs)))"

lemma is_regular_sequenceD:
  "is_regular_sequence fs \<Longrightarrow> j < length fs \<Longrightarrow> q * fs ! j \<in> ideal (set (take j fs)) \<Longrightarrow>
    q \<in> ideal (set (take j fs))"
  by (simp add: is_regular_sequence_def)

lemma is_regular_sequence_Nil: "is_regular_sequence []"
  by (simp add: is_regular_sequence_def)

lemma is_regular_sequence_snocI:
  assumes "\<And>q. q * f \<in> ideal (set fs) \<Longrightarrow> q \<in> ideal (set fs)" and "is_regular_sequence fs"
  shows "is_regular_sequence (fs @ [f])"
proof (simp add: is_regular_sequence_def, intro impI allI)
  fix j q
  assume 1: "j < Suc (length fs)" and 2: "q * (fs @ [f]) ! j \<in> ideal (set (take j fs))"
  show "q \<in> ideal (set (take j fs))"
  proof (cases "j = length fs")
    case True
    from 2 have "q * f \<in> ideal (set fs)" by (simp add: True)
    hence "q \<in> ideal (set fs)" by (rule assms(1))
    thus ?thesis by (simp add: True)
  next
    case False
    with 1 have "j < length fs" by simp
    with 2 have "q * fs ! j \<in> ideal (set (take j fs))" by (simp add: nth_append)
    with assms(2) \<open>j < length fs\<close> show "q \<in> ideal (set (take j fs))" by (rule is_regular_sequenceD)
  qed
qed

lemma is_regular_sequence_snocD:
  assumes "is_regular_sequence (fs @ [f])"
  shows "\<And>q. q * f \<in> ideal (set fs) \<Longrightarrow> q \<in> ideal (set fs)"
    and "is_regular_sequence fs"
proof -
  fix q
  assume 1: "q * f \<in> ideal (set fs)"
  note assms
  moreover have "length fs < length (fs @ [f])" by simp
  moreover from 1 have "q * (fs @ [f]) ! (length fs) \<in> ideal (set (take (length fs) (fs @ [f])))"
    by simp
  ultimately have "q \<in> ideal (set (take (length fs) (fs @ [f])))" by (rule is_regular_sequenceD)
  thus "q \<in> ideal (set fs)" by simp
next
  show "is_regular_sequence fs" unfolding is_regular_sequence_def
  proof (intro impI allI)
    fix j q
    assume 1: "j < length fs" and 2: "q * fs ! j \<in> ideal (set (take j fs))"
    note assms
    moreover from 1 have "j < length (fs @ [f])" by simp
    moreover from 1 2 have "q * (fs @ [f]) ! j \<in> ideal (set (take j (fs @ [f])))"
      by (simp add: nth_append)
    ultimately have "q \<in> ideal (set (take j (fs @ [f])))" by (rule is_regular_sequenceD)
    with 1 show "q \<in> ideal (set (take j fs))" by simp
  qed
qed

lemma is_regular_sequence_removeAll_zero:
  assumes "is_regular_sequence fs"
  shows "is_regular_sequence (removeAll 0 fs)"
  using assms
proof (induct fs rule: rev_induct)
  case Nil
  show ?case by (simp add: is_regular_sequence_Nil)
next
  case (snoc f fs)
  have "set (removeAll 0 fs) = set fs - {0}" by simp
  also have "ideal ... = ideal (set fs)" by (fact ideal.span_Diff_zero)
  finally have eq: "ideal (set (removeAll 0 fs)) = ideal (set fs)" .
  from snoc(2) have *: "is_regular_sequence fs" by (rule is_regular_sequence_snocD)
  show ?case
  proof (simp, intro conjI impI)
    show "is_regular_sequence (removeAll 0 fs @ [f])"
    proof (rule is_regular_sequence_snocI)
      fix q
      assume "q * f \<in> ideal (set (removeAll 0 fs))"
      hence "q * f \<in> ideal (set fs)" by (simp only: eq)
      with snoc(2) have "q \<in> ideal (set fs)" by (rule is_regular_sequence_snocD)
      thus "q \<in> ideal (set (removeAll 0 fs))" by (simp only: eq)
    next
      from * show "is_regular_sequence (removeAll 0 fs)" by (rule snoc.hyps)
    qed
  next
    from * show "is_regular_sequence (removeAll 0 fs)" by (rule snoc.hyps)
  qed
qed

lemma is_regular_sequence_remdups:
  assumes "is_regular_sequence fs"
  shows "is_regular_sequence (rev (remdups (rev fs)))"
  using assms
proof (induct fs rule: rev_induct)
  case Nil
  show ?case by (simp add: is_regular_sequence_Nil)
next
  case (snoc f fs)
  from snoc(2) have *: "is_regular_sequence fs" by (rule is_regular_sequence_snocD)
  show ?case
  proof (simp, intro conjI impI)
    show "is_regular_sequence (rev (remdups (rev fs)) @ [f])"
    proof (rule is_regular_sequence_snocI)
      fix q
      assume "q * f \<in> ideal (set (rev (remdups (rev fs))))"
      hence "q * f \<in> ideal (set fs)" by simp
      with snoc(2) have "q \<in> ideal (set fs)" by (rule is_regular_sequence_snocD)
      thus "q \<in> ideal (set (rev (remdups (rev fs))))" by simp
    next
      from * show "is_regular_sequence (rev (remdups (rev fs)))" by (rule snoc.hyps)
    qed
  next
    from * show "is_regular_sequence (rev (remdups (rev fs)))" by (rule snoc.hyps)
  qed
qed

end (* theory *)
