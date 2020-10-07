(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Type-Class-Multivariate Polynomials\<close>

theory MPoly_Type_Class
  imports
    Utils
    Power_Products
    More_Modules
begin

text \<open>This theory views @{typ "'a \<Rightarrow>\<^sub>0 'b"} as multivariate polynomials, where type class constraints
  on @{typ 'a} ensure that @{typ 'a} represents something like monomials.\<close>

lemma when_distrib: "f (a when b) = (f a when b)" if "\<not> b \<Longrightarrow> f 0 = 0"
  using that by (auto simp: when_def)

definition mapp_2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'c::zero) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'd::zero)"
  where "mapp_2 f p q = Abs_poly_mapping (\<lambda>k. f k (lookup p k) (lookup q k) when k \<in> keys p \<union> keys q)"

lemma lookup_mapp_2:
  "lookup (mapp_2 f p q) k = (f k (lookup p k) (lookup q k) when k \<in> keys p \<union> keys q)"
proof -
  have "lookup (Abs_poly_mapping (\<lambda>k. f k (lookup p k) (lookup q k) when k \<in> keys p \<union> keys q)) =
        (\<lambda>k. f k (lookup p k) (lookup q k) when k \<in> keys p \<union> keys q)"
    by (rule Abs_poly_mapping_inverse, simp)
  thus ?thesis by (simp add: mapp_2_def)
qed

lemma lookup_mapp_2_homogenous:
  assumes "f k 0 0 = 0"
  shows "lookup (mapp_2 f p q) k = f k (lookup p k) (lookup q k)"
  by (simp add: lookup_mapp_2 when_def in_keys_iff assms)

lemma mapp_2_cong [fundef_cong]:
  assumes "p = p'" and "q = q'"
  assumes "\<And>k. k \<in> keys p' \<union> keys q' \<Longrightarrow> f k (lookup p' k) (lookup q' k) = f' k (lookup p' k) (lookup q' k)"
  shows "mapp_2 f p q = mapp_2 f' p' q'"
  by (rule poly_mapping_eqI, simp add: assms(1, 2) lookup_mapp_2, rule when_cong, fact refl, rule assms(3), blast)

lemma keys_mapp_subset: "keys (mapp_2 f p q) \<subseteq> keys p \<union> keys q"
proof
  fix t
  assume "t \<in> keys (mapp_2 f p q)"
  hence "lookup (mapp_2 f p q) t \<noteq> 0" by (simp add: in_keys_iff) 
  thus "t \<in> keys p \<union> keys q" by (simp add: lookup_mapp_2 when_def split: if_split_asm)
qed

lemma mapp_2_mapp: "mapp_2 (\<lambda>t a. f t) 0 p = Poly_Mapping.mapp f p"
  by (rule poly_mapping_eqI, simp add: lookup_mapp lookup_mapp_2)

subsection \<open>@{const keys}\<close>

lemma in_keys_plusI1:
  assumes "t \<in> keys p" and "t \<notin> keys q"
  shows "t \<in> keys (p + q)"
  using assms unfolding in_keys_iff lookup_add by simp

lemma in_keys_plusI2:
  assumes "t \<in> keys q" and "t \<notin> keys p"
  shows "t \<in> keys (p + q)"
  using assms unfolding in_keys_iff lookup_add by simp

lemma keys_plus_eqI:
  assumes "keys p \<inter> keys q = {}"
  shows "keys (p + q) = (keys p \<union> keys q)"
proof
  show "keys (p + q) \<subseteq> keys p \<union> keys q"
    by (simp add: Poly_Mapping.keys_add)
  show "keys p \<union> keys q \<subseteq> keys (p + q)"
    by (simp add: More_MPoly_Type.keys_add assms)
qed
  
lemma keys_uminus: "keys (- p) = keys p"
  by (transfer, auto)

lemma keys_minus: "keys (p - q) \<subseteq> (keys p \<union> keys q)"
  by (transfer, auto)

subsection \<open>Monomials\<close>

abbreviation "monomial \<equiv> (\<lambda>c t. Poly_Mapping.single t c)"

lemma keys_of_monomial:
  assumes "c \<noteq> 0"
  shows "keys (monomial c t) = {t}"
  using assms by simp

lemma monomial_uminus:
  shows "- monomial c s = monomial (- c) s"
  by (transfer, rule ext, simp add: Poly_Mapping.when_def)

lemma monomial_inj:
  assumes "monomial c s = monomial (d::'b::zero_neq_one) t"
  shows "(c = 0 \<and> d = 0) \<or> (c = d \<and> s = t)"
  using assms unfolding poly_mapping_eq_iff
  by (metis (mono_tags, hide_lams) lookup_single_eq lookup_single_not_eq)

definition is_monomial :: "('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool"
  where "is_monomial p \<longleftrightarrow> card (keys p) = 1"

lemma monomial_is_monomial:
  assumes "c \<noteq> 0"
  shows "is_monomial (monomial c t)"
  using keys_single[of t c] assms by (simp add: is_monomial_def)

lemma is_monomial_monomial:
  assumes "is_monomial p"
  obtains c t where "c \<noteq> 0" and "p = monomial c t"
proof -
  from assms have "card (keys p) = 1" unfolding is_monomial_def .
  then obtain t where sp: "keys p = {t}" by (rule card_1_singletonE)
  let ?c = "lookup p t"
  from sp have "?c \<noteq> 0" by fastforce
  show ?thesis
  proof
    show "p = monomial ?c t"
    proof (intro poly_mapping_keys_eqI)
      from sp show "keys p = keys (monomial ?c t)" using \<open>?c \<noteq> 0\<close> by simp
    next
      fix s
      assume "s \<in> keys p"
      with sp have "s = t" by simp
      show "lookup p s = lookup (monomial ?c t) s" by (simp add: \<open>s = t\<close>)
    qed
  qed fact
qed
  
lemma is_monomial_uminus: "is_monomial (-p) \<longleftrightarrow> is_monomial p"
  unfolding is_monomial_def keys_uminus ..

lemma monomial_not_0:
  assumes "is_monomial p"
  shows "p \<noteq> 0"
  using assms unfolding is_monomial_def by auto

lemma keys_subset_singleton_imp_monomial:
  assumes "keys p \<subseteq> {t}"
  shows "monomial (lookup p t) t = p"
proof (rule poly_mapping_eqI, simp add: lookup_single when_def, rule)
  fix s
  assume "t \<noteq> s"
  hence "s \<notin> keys p" using assms by blast
  thus "lookup p s = 0" by (simp add: in_keys_iff) 
qed

lemma monomial_0I:
  assumes "c = 0"
  shows "monomial c t = 0"
  using assms by transfer (auto)

lemma monomial_0D:
  assumes "monomial c t = 0"
  shows "c = 0"
  using assms by transfer (auto simp: fun_eq_iff when_def; meson)

corollary monomial_0_iff: "monomial c t = 0 \<longleftrightarrow> c = 0"
  by (rule, erule monomial_0D, erule monomial_0I)

lemma lookup_times_monomial_left: "lookup (monomial c t * p) s = (c * lookup p (s - t) when t adds s)"
  for c::"'b::semiring_0" and t::"'a::comm_powerprod"
proof (induct p rule: poly_mapping_except_induct, simp)
  fix p::"'a \<Rightarrow>\<^sub>0 'b" and w
  assume "p \<noteq> 0" and "w \<in> keys p"
    and IH: "lookup (monomial c t * except p {w}) s =
             (c * lookup (except p {w}) (s - t) when t adds s)" (is "_ = ?x")
  have "monomial c t * p = monomial c t * (monomial (lookup p w) w + except p {w})"
    by (simp only: plus_except[symmetric])
  also have "... = monomial c t * monomial (lookup p w) w + monomial c t * except p {w}"
    by (simp add: algebra_simps)
  also have "... = monomial (c * lookup p w) (t + w) + monomial c t * except p {w}"
    by (simp only: mult_single)
  finally have "lookup (monomial c t * p) s = lookup (monomial (c * lookup p w) (t + w)) s + ?x"
    by (simp only: lookup_add IH)
  also have "... = (lookup (monomial (c * lookup p w) (t + w)) s +
                    c * lookup (except p {w}) (s - t) when t adds s)"
    by (rule when_distrib, auto simp add: lookup_single when_def)
  also from refl have "... = (c * lookup p (s - t) when t adds s)"
  proof (rule when_cong)
    assume "t adds s"
    then obtain u where u: "s = t + u" ..
    show "lookup (monomial (c * lookup p w) (t + w)) s + c * lookup (except p {w}) (s - t) =
          c * lookup p (s - t)"
      by (simp add: u, cases "u = w", simp_all add: lookup_except lookup_single add.commute)
  qed
  finally show "lookup (monomial c t * p) s = (c * lookup p (s - t) when t adds s)" .
qed

lemma lookup_times_monomial_right: "lookup (p * monomial c t) s = (lookup p (s - t) * c when t adds s)"
  for c::"'b::semiring_0" and t::"'a::comm_powerprod"
proof (induct p rule: poly_mapping_except_induct, simp)
  fix p::"'a \<Rightarrow>\<^sub>0 'b" and w
  assume "p \<noteq> 0" and "w \<in> keys p"
    and IH: "lookup (except p {w} * monomial c t) s =
             ((lookup (except p {w}) (s - t)) * c when t adds s)"
            (is "_ = ?x")
  have "p * monomial c t = (monomial (lookup p w) w + except p {w}) * monomial c t"
    by (simp only: plus_except[symmetric])
  also have "... = monomial (lookup p w) w * monomial c t + except p {w} * monomial c t"
    by (simp add: algebra_simps)
  also have "... = monomial (lookup p w * c) (w + t) + except p {w} * monomial c t"
    by (simp only: mult_single)
  finally have "lookup (p * monomial c t) s = lookup (monomial (lookup p w * c) (w + t)) s + ?x"
    by (simp only: lookup_add IH)
  also have "... = (lookup (monomial (lookup p w * c) (w + t)) s +
                    lookup (except p {w}) (s - t) * c when t adds s)"
    by (rule when_distrib, auto simp add: lookup_single when_def)
  also from refl have "... = (lookup p (s - t) * c when t adds s)"
  proof (rule when_cong)
    assume "t adds s"
    then obtain u where u: "s = t + u" ..
    show "lookup (monomial (lookup p w * c) (w + t)) s + lookup (except p {w}) (s - t) * c =
          lookup p (s - t) * c"
      by (simp add: u, cases "u = w", simp_all add: lookup_except lookup_single add.commute)
  qed
  finally show "lookup (p * monomial c t) s = (lookup p (s - t) * c when t adds s)" .
qed

subsection \<open>Vector-Polynomials\<close>

text \<open>From now on we consider multivariate vector-polynomials, i.\,e. vectors of scalar polynomials.
  We do this by adding a @{emph \<open>component\<close>} to each power-product, yielding
  @{emph \<open>terms\<close>}. Vector-polynomials are then again just linear combinations of terms.
  Note that a term is @{emph \<open>not\<close>} the same as a vector of power-products!\<close>

text \<open>We use define terms in a locale, such that later on we can interpret the
  locale also by ordinary power-products (without components), exploiting the canonical isomorphism
  between @{typ 'a} and @{typ \<open>'a \<times> unit\<close>}.\<close>

named_theorems term_simps "simplification rules for terms"

locale term_powerprod =
		fixes pair_of_term::"'t \<Rightarrow> ('a::comm_powerprod \<times> 'k::linorder)"
		fixes term_of_pair::"('a \<times> 'k) \<Rightarrow> 't"
		assumes term_pair [term_simps]: "term_of_pair (pair_of_term v) = v"
		assumes pair_term [term_simps]: "pair_of_term (term_of_pair p) = p"
begin

lemma pair_of_term_injective:
  assumes "pair_of_term u = pair_of_term v"
  shows "u = v"
proof -
  from assms have "term_of_pair (pair_of_term u) = term_of_pair (pair_of_term v)" by (simp only:)
  thus ?thesis by (simp add: term_simps)
qed

corollary pair_of_term_inj: "inj pair_of_term"
  using pair_of_term_injective by (rule injI)

lemma term_of_pair_injective:
  assumes "term_of_pair p = term_of_pair q"
  shows "p = q"
proof -
  from assms have "pair_of_term (term_of_pair p) = pair_of_term (term_of_pair q)" by (simp only:)
  thus ?thesis by (simp add: term_simps)
qed

corollary term_of_pair_inj: "inj term_of_pair"
  using term_of_pair_injective by (rule injI)

definition pp_of_term :: "'t \<Rightarrow> 'a"
  where "pp_of_term v = fst (pair_of_term v)"

definition component_of_term :: "'t \<Rightarrow> 'k"
  where "component_of_term v = snd (pair_of_term v)"

lemma term_of_pair_pair [term_simps]: "term_of_pair (pp_of_term v, component_of_term v) = v"
  by (simp add: pp_of_term_def component_of_term_def term_pair)

lemma pp_of_term_of_pair [term_simps]: "pp_of_term (term_of_pair (t, k)) = t"
  by (simp add: pp_of_term_def pair_term)

lemma component_of_term_of_pair [term_simps]: "component_of_term (term_of_pair (t, k)) = k"
  by (simp add: component_of_term_def pair_term)

subsubsection \<open>Additive Structure of Terms\<close>

definition splus :: "'a \<Rightarrow> 't \<Rightarrow> 't" (infixl "\<oplus>" 75)
  where "splus t v = term_of_pair (t + pp_of_term v, component_of_term v)"

definition sminus :: "'t \<Rightarrow> 'a \<Rightarrow> 't" (infixl "\<ominus>" 75)
  where "sminus v t = term_of_pair (pp_of_term v - t, component_of_term v)"

text \<open>Note that the argument order in @{const sminus} is reversed compared to the order in @{const splus}.\<close>

definition adds_pp :: "'a \<Rightarrow> 't \<Rightarrow> bool" (infix "adds\<^sub>p" 50)
  where "adds_pp t v \<longleftrightarrow> t adds pp_of_term v"

definition adds_term :: "'t \<Rightarrow> 't \<Rightarrow> bool" (infix "adds\<^sub>t" 50)
  where "adds_term u v \<longleftrightarrow> component_of_term u = component_of_term v \<and> pp_of_term u adds pp_of_term v"

lemma pp_of_term_splus [term_simps]: "pp_of_term (t \<oplus> v) = t + pp_of_term v"
  by (simp add: splus_def term_simps)

lemma component_of_term_splus [term_simps]: "component_of_term (t \<oplus> v) = component_of_term v"
  by (simp add: splus_def term_simps)

lemma pp_of_term_sminus [term_simps]: "pp_of_term (v \<ominus> t) = pp_of_term v - t"
  by (simp add: sminus_def term_simps)

lemma component_of_term_sminus [term_simps]: "component_of_term (v \<ominus> t) = component_of_term v"
  by (simp add: sminus_def term_simps)

lemma splus_sminus [term_simps]: "(t \<oplus> v) \<ominus> t = v"
  by (simp add: sminus_def term_simps)

lemma splus_zero [term_simps]: "0 \<oplus> v = v"
  by (simp add: splus_def term_simps)

lemma sminus_zero [term_simps]: "v \<ominus> 0 = v"
  by (simp add: sminus_def term_simps)

lemma splus_assoc [ac_simps]: "(s + t) \<oplus> v = s \<oplus> (t \<oplus> v)"
  by (simp add: splus_def ac_simps term_simps)

lemma splus_left_commute [ac_simps]: "s \<oplus> (t \<oplus> v) = t \<oplus> (s \<oplus> v)"
  by (simp add: splus_def ac_simps term_simps)

lemma splus_right_canc [term_simps]: "t \<oplus> v = s \<oplus> v \<longleftrightarrow> t = s"
  by (metis add_right_cancel pp_of_term_splus)

lemma splus_left_canc [term_simps]: "t \<oplus> v = t \<oplus> u \<longleftrightarrow> v = u"
  by (metis splus_sminus)

lemma adds_ppI [intro?]:
  assumes "v = t \<oplus> u"
  shows "t adds\<^sub>p v"
  by (simp add: adds_pp_def assms splus_def term_simps)

lemma adds_ppE [elim?]:
  assumes "t adds\<^sub>p v"
  obtains u where "v = t \<oplus> u"
proof -
  from assms obtain s where *: "pp_of_term v = t + s" unfolding adds_pp_def ..
  have "v = t \<oplus> (term_of_pair (s, component_of_term v))"
    by (simp add: splus_def term_simps, metis * add.commute term_of_pair_pair)
  thus ?thesis ..
qed

lemma adds_pp_alt: "t adds\<^sub>p v \<longleftrightarrow> (\<exists>u. v = t \<oplus> u)"
  by (meson adds_ppE adds_ppI)

lemma adds_pp_refl [term_simps]: "(pp_of_term v) adds\<^sub>p v"
  by (simp add: adds_pp_def)

lemma adds_pp_trans [trans]:
  assumes "s adds t" and "t adds\<^sub>p v"
  shows "s adds\<^sub>p v"
proof -
  note assms(1)
  also from assms(2) have "t adds pp_of_term v" by (simp only: adds_pp_def)
  finally show ?thesis by (simp only: adds_pp_def)
qed

lemma zero_adds_pp [term_simps]: "0 adds\<^sub>p v"
  by (simp add: adds_pp_def)

lemma adds_pp_splus:
  assumes "t adds\<^sub>p v"
  shows "t adds\<^sub>p s \<oplus> v"
  using assms by (simp add: adds_pp_def term_simps)

lemma adds_pp_triv [term_simps]: "t adds\<^sub>p t \<oplus> v"
  by (simp add: adds_pp_def term_simps)

lemma plus_adds_pp_mono:
  assumes "s adds t"
    and "u adds\<^sub>p v"
  shows "s + u adds\<^sub>p t \<oplus> v"
  using assms by (simp add: adds_pp_def term_simps) (rule plus_adds_mono)

lemma plus_adds_pp_left:
  assumes "s + t adds\<^sub>p v"
  shows "s adds\<^sub>p v"
  using assms by (simp add: adds_pp_def plus_adds_left)

lemma plus_adds_pp_right:
  assumes "s + t adds\<^sub>p v"
  shows "t adds\<^sub>p v"
  using assms by (simp add: adds_pp_def plus_adds_right)

lemma adds_pp_sminus:
  assumes "t adds\<^sub>p v"
  shows "t \<oplus> (v \<ominus> t) = v"
proof -
  from assms adds_pp_alt[of t v] obtain u where u: "v = t \<oplus> u" by (auto simp: ac_simps)
  hence "v \<ominus> t = u" by (simp add: term_simps)
  thus ?thesis using u by simp
qed

lemma adds_pp_canc: "t + s adds\<^sub>p (t \<oplus> v) \<longleftrightarrow> s adds\<^sub>p v"
  by (simp add: adds_pp_def adds_canc_2 term_simps)

lemma adds_pp_canc_2: "s + t adds\<^sub>p (t \<oplus> v) \<longleftrightarrow> s adds\<^sub>p v"
  by (simp add: adds_pp_canc add.commute[of s t])

lemma plus_adds_pp_0:
  assumes "(s + t) adds\<^sub>p v"
  shows "s adds\<^sub>p (v \<ominus> t)"
  using assms by (simp add: adds_pp_def term_simps) (rule plus_adds_0)

lemma plus_adds_ppI_1:
  assumes "t adds\<^sub>p v" and "s adds\<^sub>p (v \<ominus> t)"
  shows "(s + t) adds\<^sub>p v"
  using assms by (simp add: adds_pp_def term_simps) (rule plus_adds_2)

lemma plus_adds_ppI_2:
  assumes "t adds\<^sub>p v" and "s adds\<^sub>p (v \<ominus> t)"
  shows "(t + s) adds\<^sub>p v"
  unfolding add.commute[of t s] using assms by (rule plus_adds_ppI_1)

lemma plus_adds_pp: "(s + t) adds\<^sub>p v \<longleftrightarrow> (t adds\<^sub>p v \<and> s adds\<^sub>p (v \<ominus> t))"
  by (simp add: adds_pp_def plus_adds term_simps)

lemma minus_splus:
  assumes "s adds t"
  shows "(t - s) \<oplus> v = (t \<oplus> v) \<ominus> s"
  by (simp add: assms minus_plus sminus_def splus_def term_simps)

lemma minus_splus_sminus:
  assumes "s adds t" and "u adds\<^sub>p v"
  shows "(t - s) \<oplus> (v \<ominus> u) = (t \<oplus> v) \<ominus> (s + u)"
  using assms minus_plus_minus term_powerprod.adds_pp_def term_powerprod_axioms sminus_def
    splus_def term_simps by fastforce

lemma minus_splus_sminus_cancel:
  assumes "s adds t" and "t adds\<^sub>p v"
  shows "(t - s) \<oplus> (v \<ominus> t) = v \<ominus> s"
  by (simp add: adds_pp_sminus assms minus_splus)

lemma sminus_plus:
  assumes "s adds\<^sub>p v" and "t adds\<^sub>p (v \<ominus> s)"
  shows "v \<ominus> (s + t) = (v \<ominus> s) \<ominus> t"
  by (simp add: diff_diff_add sminus_def term_simps)

lemma adds_termI [intro?]:
  assumes "v = t \<oplus> u"
  shows "u adds\<^sub>t v"
  by (simp add: adds_term_def assms splus_def term_simps)

lemma adds_termE [elim?]:
  assumes "u adds\<^sub>t v"
  obtains t where "v = t \<oplus> u"
proof -
  from assms have eq: "component_of_term u = component_of_term v" and "pp_of_term u adds pp_of_term v"
    by (simp_all add: adds_term_def)
  from this(2) obtain s where *: "s + pp_of_term u = pp_of_term v" unfolding adds_term_def
    using adds_minus by blast
  have "v = s \<oplus> u" by (simp add: splus_def eq * term_simps)
  thus ?thesis ..
qed

lemma adds_term_alt: "u adds\<^sub>t v \<longleftrightarrow> (\<exists>t. v = t \<oplus> u)"
  by (meson adds_termE adds_termI)

lemma adds_term_refl [term_simps]: "v adds\<^sub>t v"
  by (simp add: adds_term_def)

lemma adds_term_trans [trans]:
  assumes "u adds\<^sub>t v" and "v adds\<^sub>t w"
  shows "u adds\<^sub>t w"
  using assms unfolding adds_term_def using adds_trans by auto

lemma adds_term_splus:
  assumes "u adds\<^sub>t v"
  shows "u adds\<^sub>t s \<oplus> v"
  using assms by (simp add: adds_term_def term_simps)

lemma adds_term_triv [term_simps]: "v adds\<^sub>t t \<oplus> v"
  by (simp add: adds_term_def term_simps)

lemma splus_adds_term_mono:
  assumes "s adds t"
    and "u adds\<^sub>t v"
  shows "s \<oplus> u adds\<^sub>t t \<oplus> v"
  using assms by (auto simp: adds_term_def term_simps intro: plus_adds_mono)

lemma splus_adds_term:
  assumes "t \<oplus> u adds\<^sub>t v"
  shows "u adds\<^sub>t v"
  using assms by (auto simp add: adds_term_def term_simps elim: plus_adds_right)

lemma adds_term_adds_pp:
  "u adds\<^sub>t v \<longleftrightarrow> (component_of_term u = component_of_term v \<and> pp_of_term u adds\<^sub>p v)"
  by (simp add: adds_term_def adds_pp_def)

lemma adds_term_canc: "t \<oplus> u adds\<^sub>t t \<oplus> v \<longleftrightarrow> u adds\<^sub>t v"
  by (simp add: adds_term_def adds_canc_2 term_simps)

lemma adds_term_canc_2: "s \<oplus> v adds\<^sub>t t \<oplus> v \<longleftrightarrow> s adds t"
  by (simp add: adds_term_def adds_canc term_simps)

lemma splus_adds_term_0:
  assumes "t \<oplus> u adds\<^sub>t v"
  shows "u adds\<^sub>t (v \<ominus> t)"
  using assms by (simp add: adds_term_def add.commute[of t] term_simps) (auto intro: plus_adds_0)

lemma splus_adds_termI_1:
  assumes "t adds\<^sub>p v" and "u adds\<^sub>t (v \<ominus> t)"
  shows "t \<oplus> u adds\<^sub>t v"
  using assms apply (simp add: adds_term_def term_simps) by (metis add.commute adds_pp_def plus_adds_2)

lemma splus_adds_term_iff: "t \<oplus> u adds\<^sub>t v \<longleftrightarrow> (t adds\<^sub>p v \<and> u adds\<^sub>t (v \<ominus> t))"
  by (metis adds_ppI adds_pp_splus adds_termE splus_adds_termI_1 splus_adds_term_0)

lemma adds_minus_splus:
  assumes "pp_of_term u adds t"
  shows "(t - pp_of_term u) \<oplus> u = term_of_pair (t, component_of_term u)"
  by (simp add: splus_def adds_minus[OF assms])

subsubsection \<open>Projections and Conversions\<close>

lift_definition proj_poly :: "'k \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero)"
  is "\<lambda>k p t. p (term_of_pair (t, k))"
proof -
  fix k::'k and p::"'t \<Rightarrow> 'b"
  assume fin: "finite {v. p v \<noteq> 0}"
  have "{t. p (term_of_pair (t, k)) \<noteq> 0} \<subseteq> pp_of_term ` {v. p v \<noteq> 0}"
  proof (rule, simp)
    fix t
    assume "p (term_of_pair (t, k)) \<noteq> 0"
    hence *: "term_of_pair (t, k) \<in> {v. p v \<noteq> 0}" by simp
    have "t = pp_of_term (term_of_pair (t, k))" by (simp add: pp_of_term_def pair_term)
    from this * show "t \<in> pp_of_term ` {v. p v \<noteq> 0}" ..
  qed
  moreover from fin have "finite (pp_of_term ` {v. p v \<noteq> 0})" by (rule finite_imageI)
  ultimately show "finite {t. p (term_of_pair (t, k)) \<noteq> 0}" by (rule finite_subset)
qed

definition vectorize_poly :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('k \<Rightarrow>\<^sub>0 ('a \<Rightarrow>\<^sub>0 'b::zero))"
  where "vectorize_poly p = Abs_poly_mapping (\<lambda>k. proj_poly k p)"

definition atomize_poly :: "('k \<Rightarrow>\<^sub>0 ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero)"
  where "atomize_poly p = Abs_poly_mapping (\<lambda>v. lookup (lookup p (component_of_term v)) (pp_of_term v))"

lemma lookup_proj_poly: "lookup (proj_poly k p) t = lookup p (term_of_pair (t, k))"
  by (transfer, simp)

lemma lookup_vectorize_poly: "lookup (vectorize_poly p) k = proj_poly k p"
proof -
  have "lookup (Abs_poly_mapping (\<lambda>k. proj_poly k p)) = (\<lambda>k. proj_poly k p)"
  proof (rule Abs_poly_mapping_inverse, simp)
    have "{k. proj_poly k p \<noteq> 0} \<subseteq> component_of_term ` keys p"
    proof (rule, simp)
      fix k
      assume "proj_poly k p \<noteq> 0"
      hence "keys (proj_poly k p) \<noteq> {}" using poly_mapping_eq_zeroI by blast
      then obtain t where "lookup (proj_poly k p) t \<noteq> 0" by blast
      hence "term_of_pair (t, k) \<in> keys p" by (simp add: lookup_proj_poly in_keys_iff)
      hence "component_of_term (term_of_pair (t, k)) \<in> component_of_term ` keys p" by fastforce
      thus "k \<in> component_of_term ` keys p" by (simp add: term_simps)
    qed
    moreover from finite_keys have "finite (component_of_term ` keys p)" by (rule finite_imageI)
    ultimately show "finite {k. proj_poly k p \<noteq> 0}" by (rule finite_subset)
  qed
  thus ?thesis by (simp add: vectorize_poly_def)
qed

lemma lookup_atomize_poly:
  "lookup (atomize_poly p) v = lookup (lookup p (component_of_term v)) (pp_of_term v)"
proof -
  have "lookup (Abs_poly_mapping (\<lambda>v. lookup (lookup p (component_of_term v)) (pp_of_term v))) =
        (\<lambda>v. lookup (lookup p (component_of_term v)) (pp_of_term v))"
  proof (rule Abs_poly_mapping_inverse, simp)
    have "{v. pp_of_term v \<in> keys (lookup p (component_of_term v))} \<subseteq>
          (\<Union>k\<in>keys p. (\<lambda>t. term_of_pair (t, k)) ` keys (lookup p k))" (is "_ \<subseteq> ?A")
    proof (rule, simp)
      fix v
      assume *: "pp_of_term v \<in> keys (lookup p (component_of_term v))"
      hence "keys (lookup p (component_of_term v)) \<noteq> {}" by blast
      hence "lookup p (component_of_term v) \<noteq> 0" by auto
      hence "component_of_term v \<in> keys p" (is "?k \<in> _") 
        by (simp add: in_keys_iff)
      thus "\<exists>k\<in>keys p. v \<in> (\<lambda>t. term_of_pair (t, k)) ` keys (lookup p k)"
      proof
        have "v = term_of_pair (pp_of_term v, component_of_term v)" by (simp add: term_simps)
        from this * show "v \<in> (\<lambda>t. term_of_pair (t, ?k)) ` keys (lookup p ?k)" ..
      qed
    qed
    moreover have "finite ?A" by (rule, fact finite_keys, rule finite_imageI, rule finite_keys)
    ultimately show "finite {x. lookup (lookup p (component_of_term x)) (pp_of_term x) \<noteq> 0}"
      by (simp add: finite_subset in_keys_iff)
  qed
  thus ?thesis by (simp add: atomize_poly_def)
qed

lemma keys_proj_poly: "keys (proj_poly k p) = pp_of_term ` {x\<in>keys p. component_of_term x = k}"
proof
  show "keys (proj_poly k p) \<subseteq> pp_of_term ` {x\<in>keys p. component_of_term x = k}"
  proof
    fix t
    assume "t \<in> keys (proj_poly k p)"
    hence "lookup (proj_poly k p) t \<noteq> 0" by (simp add: in_keys_iff)
    hence "term_of_pair (t, k) \<in> keys p" by (simp add: in_keys_iff lookup_proj_poly)
    hence "term_of_pair (t, k) \<in> {x\<in>keys p. component_of_term x = k}" by (simp add: term_simps)
    hence "pp_of_term (term_of_pair (t, k)) \<in> pp_of_term ` {x\<in>keys p. component_of_term x = k}" by (rule imageI)
    thus "t \<in> pp_of_term ` {x\<in>keys p. component_of_term x = k}" by (simp only: pp_of_term_of_pair)
  qed
next
  show "pp_of_term ` {x\<in>keys p. component_of_term x = k} \<subseteq> keys (proj_poly k p)"
  proof
    fix t
    assume "t \<in> pp_of_term ` {x\<in>keys p. component_of_term x = k}"
    then obtain x where "x \<in> {x\<in>keys p. component_of_term x = k}" and "t = pp_of_term x" ..
    from this(1) have "x \<in> keys p" and "k = component_of_term x" by simp_all
    from this(2) have "x = term_of_pair (t, k)" by (simp add: term_of_pair_pair \<open>t = pp_of_term x\<close>)
    with \<open>x \<in> keys p\<close> have "lookup p (term_of_pair (t, k)) \<noteq> 0" by (simp add: in_keys_iff)
    hence "lookup (proj_poly k p) t \<noteq> 0" by (simp add: lookup_proj_poly)
    thus "t \<in> keys (proj_poly k p)" by (simp add: in_keys_iff)
  qed
qed

lemma keys_vectorize_poly: "keys (vectorize_poly p) = component_of_term ` keys p"
proof
  show "keys (vectorize_poly p) \<subseteq> component_of_term ` keys p"
  proof
    fix k
    assume "k \<in> keys (vectorize_poly p)"
    hence "lookup (vectorize_poly p) k \<noteq> 0" by (simp add: in_keys_iff)
    hence "proj_poly k p \<noteq> 0" by (simp add: lookup_vectorize_poly)
    then obtain t where "lookup (proj_poly k p) t \<noteq> 0" using aux by blast
    hence "term_of_pair (t, k) \<in> keys p" by (simp add: lookup_proj_poly in_keys_iff)
    hence "component_of_term (term_of_pair (t, k)) \<in> component_of_term ` keys p" by (rule imageI)
    thus "k \<in> component_of_term ` keys p" by (simp only: component_of_term_of_pair)
  qed
next
  show "component_of_term ` keys p \<subseteq> keys (vectorize_poly p)"
  proof
    fix k
    assume "k \<in> component_of_term ` keys p"
    then obtain x where "x \<in> keys p" and "k = component_of_term x" ..
    from this(2) have "term_of_pair (pp_of_term x, k) = x" by (simp add: term_of_pair_pair)
    with \<open>x \<in> keys p\<close> have "lookup p (term_of_pair (pp_of_term x, k)) \<noteq> 0" by (simp add: in_keys_iff)
    hence "lookup (proj_poly k p) (pp_of_term x) \<noteq> 0" by (simp add: lookup_proj_poly)
    hence "proj_poly k p \<noteq> 0" by auto
    hence "lookup (vectorize_poly p) k \<noteq> 0" by (simp add: lookup_vectorize_poly)
    thus "k \<in> keys (vectorize_poly p)" by (simp add: in_keys_iff)
  qed
qed

lemma keys_atomize_poly:
  "keys (atomize_poly p) = (\<Union>k\<in>keys p. (\<lambda>t. term_of_pair (t, k)) ` keys (lookup p k))" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
  proof
    fix v
    assume "v \<in> ?l"
    hence "lookup (atomize_poly p) v \<noteq> 0" by (simp add: in_keys_iff)
    hence *: "pp_of_term v \<in> keys (lookup p (component_of_term v))" by (simp add: in_keys_iff lookup_atomize_poly)
    hence "lookup p (component_of_term v) \<noteq> 0" by fastforce
    hence "component_of_term v \<in> keys p" by (simp add: in_keys_iff)
    thus "v \<in> ?r"
    proof
      from * have "term_of_pair (pp_of_term v, component_of_term v) \<in>
                    (\<lambda>t. term_of_pair (t, component_of_term v)) ` keys (lookup p (component_of_term v))"
        by (rule imageI)
      thus "v \<in> (\<lambda>t. term_of_pair (t, component_of_term v)) ` keys (lookup p (component_of_term v))"
        by (simp only: term_of_pair_pair)
    qed
  qed
next
  show "?r \<subseteq> ?l"
  proof
    fix v
    assume "v \<in> ?r"
    then obtain k where "k \<in> keys p" and "v \<in> (\<lambda>t. term_of_pair (t, k)) ` keys (lookup p k)" ..
    from this(2) obtain t where "t \<in> keys (lookup p k)" and v: "v = term_of_pair (t, k)" ..
    from this(1) have "lookup (atomize_poly p) v \<noteq> 0" by (simp add: v lookup_atomize_poly in_keys_iff term_simps)
    thus "v \<in> ?l" by (simp add: in_keys_iff)
  qed
qed

lemma proj_atomize_poly [term_simps]: "proj_poly k (atomize_poly p) = lookup p k"
  by (rule poly_mapping_eqI, simp add: lookup_proj_poly lookup_atomize_poly term_simps)

lemma vectorize_atomize_poly [term_simps]: "vectorize_poly (atomize_poly p) = p"
  by (rule poly_mapping_eqI, simp add: lookup_vectorize_poly term_simps)

lemma atomize_vectorize_poly [term_simps]: "atomize_poly (vectorize_poly p) = p"
  by (rule poly_mapping_eqI, simp add: lookup_atomize_poly lookup_vectorize_poly lookup_proj_poly term_simps)

lemma proj_zero [term_simps]: "proj_poly k 0 = 0"
  by (rule poly_mapping_eqI, simp add: lookup_proj_poly)

lemma proj_plus: "proj_poly k (p + q) = proj_poly k p + proj_poly k q"
  by (rule poly_mapping_eqI, simp add: lookup_proj_poly lookup_add)

lemma proj_uminus [term_simps]: "proj_poly k (- p) = - proj_poly k p"
  by (rule poly_mapping_eqI, simp add: lookup_proj_poly)

lemma proj_minus: "proj_poly k (p - q) = proj_poly k p - proj_poly k q"
  by (rule poly_mapping_eqI, simp add: lookup_proj_poly lookup_minus)

lemma vectorize_zero [term_simps]: "vectorize_poly 0 = 0"
  by (rule poly_mapping_eqI, simp add: lookup_vectorize_poly term_simps)

lemma vectorize_plus: "vectorize_poly (p + q) = vectorize_poly p + vectorize_poly q"
  by (rule poly_mapping_eqI, simp add: lookup_vectorize_poly lookup_add proj_plus)

lemma vectorize_uminus [term_simps]: "vectorize_poly (- p) = - vectorize_poly p"
  by (rule poly_mapping_eqI, simp add: lookup_vectorize_poly term_simps)

lemma vectorize_minus: "vectorize_poly (p - q) = vectorize_poly p - vectorize_poly q"
  by (rule poly_mapping_eqI, simp add: lookup_vectorize_poly lookup_minus proj_minus)

lemma atomize_zero [term_simps]: "atomize_poly 0 = 0"
  by (rule poly_mapping_eqI, simp add: lookup_atomize_poly)

lemma atomize_plus: "atomize_poly (p + q) = atomize_poly p + atomize_poly q"
  by (rule poly_mapping_eqI, simp add: lookup_atomize_poly lookup_add)

lemma atomize_uminus [term_simps]: "atomize_poly (- p) = - atomize_poly p"
  by (rule poly_mapping_eqI, simp add: lookup_atomize_poly)

lemma atomize_minus: "atomize_poly (p - q) = atomize_poly p - atomize_poly q"
  by (rule poly_mapping_eqI, simp add: lookup_atomize_poly lookup_minus)

lemma proj_monomial:
  "proj_poly k (monomial c v) = (monomial c (pp_of_term v) when component_of_term v = k)"
proof (rule poly_mapping_eqI, simp add: lookup_proj_poly lookup_single when_def term_simps, intro impI)
  fix t
  assume 1: "pp_of_term v = t" and 2: "component_of_term v = k"
  assume "v \<noteq> term_of_pair (t, k)"
  moreover have "v = term_of_pair (t, k)" by (simp add: 1[symmetric] 2[symmetric] term_simps)
  ultimately show "c = 0" ..
qed

lemma vectorize_monomial:
  "vectorize_poly (monomial c v) = monomial (monomial c (pp_of_term v)) (component_of_term v)"
  by (rule poly_mapping_eqI, simp add: lookup_vectorize_poly proj_monomial lookup_single)

lemma atomize_monomial_monomial:
  "atomize_poly (monomial (monomial c t) k) = monomial c (term_of_pair (t, k))"
proof -
  define v where "v = term_of_pair (t, k)"
  have t: "t = pp_of_term v" and k: "k = component_of_term v" by (simp_all add: v_def term_simps)
  show ?thesis by (simp add: t k vectorize_monomial[symmetric] term_simps)
qed

lemma poly_mapping_eqI_proj:
  assumes "\<And>k. proj_poly k p = proj_poly k q"
  shows "p = q"
proof (rule poly_mapping_eqI)
  fix v::'t
  have "proj_poly (component_of_term v) p = proj_poly (component_of_term v) q" by (rule assms)
  hence "lookup (proj_poly (component_of_term v) p) (pp_of_term v) =
          lookup (proj_poly (component_of_term v) q) (pp_of_term v)" by simp
  thus "lookup p v = lookup q v" by (simp add: lookup_proj_poly term_simps)
qed

subsection \<open>Scalar Multiplication by Monomials\<close>

definition monom_mult :: "'b::semiring_0 \<Rightarrow> 'a::comm_powerprod \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b)"
  where "monom_mult c t p = Abs_poly_mapping (\<lambda>v. if t adds\<^sub>p v then c * (lookup p (v \<ominus> t)) else 0)"

lemma keys_monom_mult_aux:
  "{v. (if t adds\<^sub>p v then c * lookup p (v \<ominus> t) else 0) \<noteq> 0} \<subseteq> (\<oplus>) t ` keys p" (is "?l \<subseteq> ?r")
  for c::"'b::semiring_0"
proof
  fix v::'t
  assume "v \<in> ?l"
  hence "(if t adds\<^sub>p v then c * lookup p (v \<ominus> t) else 0) \<noteq> 0" by simp
  hence "t adds\<^sub>p v" and cp_not_zero: "c * lookup p (v \<ominus> t) \<noteq> 0" by (simp_all split: if_split_asm)
  show "v \<in> ?r"
  proof
    from adds_pp_sminus[OF \<open>t adds\<^sub>p v\<close>] show "v = t \<oplus> (v \<ominus> t)" by simp
  next
    from mult_not_zero[OF cp_not_zero] show "v \<ominus> t \<in> keys p"
      by (simp add: in_keys_iff)
  qed
qed

lemma lookup_monom_mult:
  "lookup (monom_mult c t p) v = (if t adds\<^sub>p v then c * lookup p (v \<ominus> t) else 0)"
proof -
  have "lookup (monom_mult c t p) = (\<lambda>v. if t adds\<^sub>p v then c * lookup p (v \<ominus> t) else 0)"
    unfolding monom_mult_def
  proof (rule Abs_poly_mapping_inverse)
    from finite_keys have "finite ((\<oplus>) t ` keys p)" ..
    with keys_monom_mult_aux have "finite {v. (if t adds\<^sub>p v then c * lookup p (v \<ominus> t) else 0) \<noteq> 0}"
      by (rule finite_subset)
    thus "(\<lambda>v. if t adds\<^sub>p v then c * lookup p (v \<ominus> t) else 0) \<in> {f. finite {x. f x \<noteq> 0}}" by simp
  qed
  thus ?thesis by simp
qed

lemma lookup_monom_mult_plus:
  "lookup (monom_mult c t p) (t \<oplus> v) = (c::'b::semiring_0) * lookup p v"
  by (simp add: lookup_monom_mult term_simps)

lemma monom_mult_assoc: "monom_mult c s (monom_mult d t p) = monom_mult (c * d) (s + t) p"
proof (rule poly_mapping_eqI, simp add: lookup_monom_mult sminus_plus ac_simps, intro conjI impI)
  fix v
  assume "s adds\<^sub>p v" and "t adds\<^sub>p v \<ominus> s"
  hence "s + t adds\<^sub>p v" by (rule plus_adds_ppI_2)
  moreover assume "\<not> s + t adds\<^sub>p v"
  ultimately show "c * (d * lookup p (v \<ominus> s \<ominus> t)) = 0" by simp
next
  fix v
  assume "s + t adds\<^sub>p v"
  hence "s adds\<^sub>p v" by (rule plus_adds_pp_left)
  moreover assume "\<not> s adds\<^sub>p v"
  ultimately show "c * (d * lookup p (v \<ominus> (s + t))) = 0" by simp
next
  fix v
  assume "s + t adds\<^sub>p v"
  hence "t adds\<^sub>p v \<ominus> s" by (simp add: add.commute plus_adds_pp_0)
  moreover assume "\<not> t adds\<^sub>p v \<ominus> s"
  ultimately show "c * (d * lookup p (v \<ominus> (s + t))) = 0" by simp
qed

lemma monom_mult_uminus_left: "monom_mult (- c) t p = - monom_mult (c::'b::ring) t p"
  by (rule poly_mapping_eqI, simp add: lookup_monom_mult)

lemma monom_mult_uminus_right: "monom_mult c t (- p) = - monom_mult (c::'b::ring) t p"
  by (rule poly_mapping_eqI, simp add: lookup_monom_mult)

lemma uminus_monom_mult: "- p = monom_mult (-1::'b::comm_ring_1) 0 p"
  by (rule poly_mapping_eqI, simp add: lookup_monom_mult term_simps)

lemma monom_mult_dist_left: "monom_mult (c + d) t p = (monom_mult c t p) + (monom_mult d t p)"
  by (rule poly_mapping_eqI, simp add: lookup_monom_mult lookup_add algebra_simps)

lemma monom_mult_dist_left_minus:
  "monom_mult (c - d) t p = (monom_mult c t p) - (monom_mult (d::'b::ring) t p)"
  using monom_mult_dist_left[of c "-d" t p] monom_mult_uminus_left[of d t p] by simp

lemma monom_mult_dist_right:
  "monom_mult c t (p + q) = (monom_mult c t p) + (monom_mult c t q)"
  by (rule poly_mapping_eqI, simp add: lookup_monom_mult lookup_add algebra_simps)

lemma monom_mult_dist_right_minus:
  "monom_mult c t (p - q) = (monom_mult c t p) - (monom_mult (c::'b::ring) t q)"
  using monom_mult_dist_right[of c t p "-q"] monom_mult_uminus_right[of c t q] by simp

lemma monom_mult_zero_left [simp]: "monom_mult 0 t p = 0"
  by (rule poly_mapping_eqI, simp add: lookup_monom_mult)

lemma monom_mult_zero_right [simp]: "monom_mult c t 0 = 0"
  by (rule poly_mapping_eqI, simp add: lookup_monom_mult)

lemma monom_mult_one_left [simp]: "(monom_mult (1::'b::semiring_1) 0 p) = p"
  by (rule poly_mapping_eqI, simp add: lookup_monom_mult term_simps)

lemma monom_mult_monomial:
  "monom_mult c s (monomial d v) = monomial (c * (d::'b::semiring_0)) (s \<oplus> v)"
  by (rule poly_mapping_eqI, auto simp add: lookup_monom_mult lookup_single adds_pp_alt when_def term_simps, metis)

lemma monom_mult_eq_zero_iff: "(monom_mult c t p = 0) \<longleftrightarrow> ((c::'b::semiring_no_zero_divisors) = 0 \<or> p = 0)"
proof
  assume eq: "monom_mult c t p = 0"
  show "c = 0 \<or> p = 0"
  proof (rule ccontr, simp)
    assume "c \<noteq> 0 \<and> p \<noteq> 0"
    hence "c \<noteq> 0" and "p \<noteq> 0" by simp_all
    from lookup_zero poly_mapping_eq_iff[of p 0] \<open>p \<noteq> 0\<close> obtain v where "lookup p v \<noteq> 0" by fastforce
    from eq lookup_zero have "lookup (monom_mult c t p) (t \<oplus> v) = 0" by simp
    hence "c * lookup p v = 0" by (simp only: lookup_monom_mult_plus)
    with \<open>c \<noteq> 0\<close> \<open>lookup p v \<noteq> 0\<close> show False by auto
  qed
next
  assume "c = 0 \<or> p = 0"
  with monom_mult_zero_left[of t p] monom_mult_zero_right[of c t] show "monom_mult c t p = 0" by auto
qed

lemma lookup_monom_mult_zero: "lookup (monom_mult c 0 p) t = c * lookup p t"
proof -
  have "lookup (monom_mult c 0 p) t = lookup (monom_mult c 0 p) (0 \<oplus> t)" by (simp add: term_simps)
  also have "... = c * lookup p t" by (rule lookup_monom_mult_plus)
  finally show ?thesis .
qed

lemma monom_mult_inj_1:
  assumes "monom_mult c1 t p = monom_mult c2 t p"
    and "(p::(_ \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors_cancel)) \<noteq> 0"
  shows "c1 = c2"
proof -
  from assms(2) have "keys p \<noteq> {}" using poly_mapping_eq_zeroI by blast
  then obtain v where "v \<in> keys p" by blast
  hence *: "lookup p v \<noteq> 0" by (simp add: in_keys_iff)
  from assms(1) have "lookup (monom_mult c1 t p) (t \<oplus> v) = lookup (monom_mult c2 t p) (t \<oplus> v)"
    by simp
  hence "c1 * lookup p v = c2 * lookup p v" by (simp only: lookup_monom_mult_plus)
  with * show ?thesis by auto
qed

text \<open>Multiplication by a monomial is injective in the second argument (the power-product) only in
  context @{locale ordered_powerprod}; see lemma \<open>monom_mult_inj_2\<close> below.\<close>

lemma monom_mult_inj_3:
  assumes "monom_mult c t p1 = monom_mult c t (p2::(_ \<Rightarrow>\<^sub>0 'b::semiring_no_zero_divisors_cancel))"
    and "c \<noteq> 0"
  shows "p1 = p2"
proof (rule poly_mapping_eqI)
  fix v
  from assms(1) have "lookup (monom_mult c t p1) (t \<oplus> v) = lookup (monom_mult c t p2) (t \<oplus> v)"
    by simp
  hence "c * lookup p1 v = c * lookup p2 v" by (simp only: lookup_monom_mult_plus)
  with assms(2) show "lookup p1 v = lookup p2 v" by simp
qed
    
lemma keys_monom_multI:
  assumes "v \<in> keys p" and "c \<noteq> (0::'b::semiring_no_zero_divisors)"
  shows "t \<oplus> v \<in> keys (monom_mult c t p)"
  using assms unfolding in_keys_iff lookup_monom_mult_plus by simp

lemma keys_monom_mult_subset: "keys (monom_mult c t p) \<subseteq> ((\<oplus>) t) ` (keys p)"
proof -
  have "keys (monom_mult c t p) \<subseteq> {v. (if t adds\<^sub>p v then c * lookup p (v \<ominus> t) else 0) \<noteq> 0}" (is "_ \<subseteq> ?A")
  proof
    fix v
    assume "v \<in> keys (monom_mult c t p)"
    hence "lookup (monom_mult c t p) v \<noteq> 0" by (simp add: in_keys_iff)
    thus "v \<in> ?A" unfolding lookup_monom_mult by simp
  qed
  also note keys_monom_mult_aux
  finally show ?thesis .
qed

lemma keys_monom_multE:
  assumes "v \<in> keys (monom_mult c t p)"
  obtains u where "u \<in> keys p" and "v = t \<oplus> u"
proof -
  note assms
  also have "keys (monom_mult c t p) \<subseteq> ((\<oplus>) t) ` (keys p)" by (fact keys_monom_mult_subset)
  finally have "v \<in> ((\<oplus>) t) ` (keys p)" .
  then obtain u where "u \<in> keys p" and "v = t \<oplus> u" ..
  thus ?thesis ..
qed

lemma keys_monom_mult:
  assumes "c \<noteq> (0::'b::semiring_no_zero_divisors)"
  shows "keys (monom_mult c t p) = ((\<oplus>) t) ` (keys p)"
proof (rule, fact keys_monom_mult_subset, rule)
  fix v
  assume "v \<in> (\<oplus>) t ` keys p"
  then obtain u where "u \<in> keys p" and v: "v = t \<oplus> u" ..
  from \<open>u \<in> keys p\<close> assms show "v \<in> keys (monom_mult c t p)" unfolding v by (rule keys_monom_multI)
qed

lemma monom_mult_when: "monom_mult c t (p when P) = ((monom_mult c t p) when P)"
  by (cases P, simp_all)

lemma when_monom_mult: "monom_mult (c when P) t p = ((monom_mult c t p) when P)"
  by (cases P, simp_all)

lemma monomial_power: "(monomial c t) ^ n = monomial (c ^ n) (\<Sum>i=0..<n. t)"
  by (induct n, simp_all add: mult_single monom_mult_monomial add.commute)

subsection \<open>Component-wise Lifting\<close>

text \<open>Component-wise lifting of functions on @{typ "'a \<Rightarrow>\<^sub>0 'b"} to functions on @{typ "'t \<Rightarrow>\<^sub>0 'b"}.\<close>

definition lift_poly_fun_2 :: "(('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero)"
  where "lift_poly_fun_2 f p q = atomize_poly (mapp_2 (\<lambda>_. f) (vectorize_poly p) (vectorize_poly q))"

definition lift_poly_fun :: "(('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero)"
  where "lift_poly_fun f p = lift_poly_fun_2 (\<lambda>_. f) 0 p"

lemma lookup_lift_poly_fun_2:
  "lookup (lift_poly_fun_2 f p q) v =
    (lookup (f (proj_poly (component_of_term v) p) (proj_poly (component_of_term v) q)) (pp_of_term v)
        when component_of_term v \<in> keys (vectorize_poly p) \<union> keys (vectorize_poly q))"
  by (simp add: lift_poly_fun_2_def lookup_atomize_poly lookup_mapp_2 lookup_vectorize_poly
      when_distrib[of _ "\<lambda>q. lookup q (pp_of_term v)", OF lookup_zero])

lemma lookup_lift_poly_fun:
  "lookup (lift_poly_fun f p) v =
    (lookup (f (proj_poly (component_of_term v) p)) (pp_of_term v) when component_of_term v \<in> keys (vectorize_poly p))"
  by (simp add: lift_poly_fun_def lookup_lift_poly_fun_2 term_simps)

lemma lookup_lift_poly_fun_2_homogenous:
  assumes "f 0 0 = 0"
  shows "lookup (lift_poly_fun_2 f p q) v =
         lookup (f (proj_poly (component_of_term v) p) (proj_poly (component_of_term v) q)) (pp_of_term v)"
  by (simp add: lookup_lift_poly_fun_2 when_def in_keys_iff lookup_vectorize_poly assms)

lemma proj_lift_poly_fun_2_homogenous:
  assumes "f 0 0 = 0"
  shows "proj_poly k (lift_poly_fun_2 f p q) = f (proj_poly k p) (proj_poly k q)"
  by (rule poly_mapping_eqI,
      simp add: lookup_proj_poly lookup_lift_poly_fun_2_homogenous[of f, OF assms] term_simps)

lemma lookup_lift_poly_fun_homogenous:
  assumes "f 0 = 0"
  shows "lookup (lift_poly_fun f p) v = lookup (f (proj_poly (component_of_term v) p)) (pp_of_term v)"
  by (simp add: lookup_lift_poly_fun when_def in_keys_iff lookup_vectorize_poly assms)

lemma proj_lift_poly_fun_homogenous:
  assumes "f 0 = 0"
  shows "proj_poly k (lift_poly_fun f p) = f (proj_poly k p)"
  by (rule poly_mapping_eqI,
      simp add: lookup_proj_poly lookup_lift_poly_fun_homogenous[of f, OF assms] term_simps)

subsection \<open>Component-wise Multiplication\<close>

definition mult_vec :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::semiring_0)" (infixl "**" 75)
  where "mult_vec = lift_poly_fun_2 (*)"

lemma lookup_mult_vec:
  "lookup (p ** q) v = lookup ((proj_poly (component_of_term v) p) * (proj_poly (component_of_term v) q)) (pp_of_term v)"
  unfolding mult_vec_def by (rule lookup_lift_poly_fun_2_homogenous, simp)

lemma proj_mult_vec [term_simps]: "proj_poly k (p ** q) = (proj_poly k p) * (proj_poly k q)"
  unfolding mult_vec_def by (rule proj_lift_poly_fun_2_homogenous, simp)

lemma mult_vec_zero_left: "0 ** p = 0"
  by (rule poly_mapping_eqI_proj, simp add: term_simps)

lemma mult_vec_zero_right: "p ** 0 = 0"
  by (rule poly_mapping_eqI_proj, simp add: term_simps)

lemma mult_vec_assoc: "(p ** q) ** r = p ** (q ** r)"
  by (rule poly_mapping_eqI_proj, simp add: ac_simps term_simps)

lemma mult_vec_distrib_right: "(p + q) ** r = p ** r + q ** r"
  by (rule poly_mapping_eqI_proj, simp add: algebra_simps proj_plus term_simps)

lemma mult_vec_distrib_left: "r ** (p + q) = r ** p + r ** q"
  by (rule poly_mapping_eqI_proj, simp add: algebra_simps proj_plus term_simps)

lemma mult_vec_minus_mult_left: "(- p) ** q = - (p ** q)"
  by (rule sym, rule minus_unique, simp add: mult_vec_distrib_right[symmetric] mult_vec_zero_left)

lemma mult_vec_minus_mult_right: "p ** (- q) = - (p ** q)"
  by (rule sym, rule minus_unique, simp add: mult_vec_distrib_left [symmetric] mult_vec_zero_right)

lemma minus_mult_vec_minus: "(- p) ** (- q) = p ** q"
  by (simp add: mult_vec_minus_mult_left mult_vec_minus_mult_right)

lemma minus_mult_vec_commute: "(- p) ** q = p ** (- q)"
  by (simp add: mult_vec_minus_mult_left mult_vec_minus_mult_right)

lemma mult_vec_right_diff_distrib: "r ** (p - q) = r ** p - r ** q"
  for r::"_ \<Rightarrow>\<^sub>0 'b::ring"
  using mult_vec_distrib_left [of r p "- q"] by (simp add: mult_vec_minus_mult_right)

lemma mult_vec_left_diff_distrib: "(p - q) ** r = p ** r - q ** r"
  for p::"_ \<Rightarrow>\<^sub>0 'b::ring"
  using mult_vec_distrib_right [of p "- q" r] by (simp add: mult_vec_minus_mult_left)

lemma mult_vec_commute: "p ** q = q ** p" for p::"_ \<Rightarrow>\<^sub>0 'b::comm_semiring_0"
  by (rule poly_mapping_eqI_proj, simp add: term_simps ac_simps)

lemma mult_vec_left_commute: "p ** (q ** r) = q ** (p ** r)"
  for p::"_ \<Rightarrow>\<^sub>0 'b::comm_semiring_0"
  by (rule poly_mapping_eqI_proj, simp add: term_simps ac_simps)

lemma mult_vec_monomial_monomial:
  "(monomial c u) ** (monomial d v) =
          (monomial (c * d) (term_of_pair (pp_of_term u + pp_of_term v, component_of_term u)) when
            component_of_term u = component_of_term v)"
  by (rule poly_mapping_eqI_proj, simp add: proj_monomial mult_single when_def term_simps)

lemma mult_vec_rec_left: "p ** q = monomial (lookup p v) v ** q + (except p {v}) ** q"
proof -
  from plus_except[of p v] have "p ** q = (monomial (lookup p v) v + except p {v}) ** q" by simp
  also have "... = monomial (lookup p v) v ** q + except p {v} ** q"
    by (simp only: mult_vec_distrib_right)
  finally show ?thesis .
qed

lemma mult_vec_rec_right: "p ** q = p ** monomial (lookup q v) v + p ** except q {v}"
proof -
  have "p ** monomial (lookup q v) v + p ** except q {v} = p ** (monomial (lookup q v) v + except q {v})"
    by (simp only: mult_vec_distrib_left)
  also have "... = p ** q" by (simp only: plus_except[of q v, symmetric])
  finally show ?thesis by simp
qed

lemma in_keys_mult_vecE:
  assumes "w \<in> keys (p ** q)"
  obtains u v where "u \<in> keys p" and "v \<in> keys q" and "component_of_term u = component_of_term v"
    and "w = term_of_pair (pp_of_term u + pp_of_term v, component_of_term u)"
proof -
  from assms have "0 \<noteq> lookup (p ** q) w" by (simp add: in_keys_iff)
  also have "lookup (p ** q) w =
      lookup ((proj_poly (component_of_term w) p) * (proj_poly (component_of_term w) q)) (pp_of_term w)"
    by (fact lookup_mult_vec)
  finally have "pp_of_term w \<in> keys ((proj_poly (component_of_term w) p) * (proj_poly (component_of_term w) q))"
    by (simp add: in_keys_iff)
  from this keys_mult
  have "pp_of_term w \<in> {t + s |t s. t \<in> keys (proj_poly (component_of_term w) p) \<and>
                                   s \<in> keys (proj_poly (component_of_term w) q)}" ..
  then obtain t s where 1: "t \<in> keys (proj_poly (component_of_term w) p)"
    and 2: "s \<in> keys (proj_poly (component_of_term w) q)"
    and eq: "pp_of_term w = t + s" by fastforce
  let ?u = "term_of_pair (t, component_of_term w)"
  let ?v = "term_of_pair (s, component_of_term w)"
  from 1 have "?u \<in> keys p" by (simp only: in_keys_iff lookup_proj_poly not_False_eq_True)
  moreover from 2 have "?v \<in> keys q" by (simp only: in_keys_iff lookup_proj_poly not_False_eq_True)
  moreover have "component_of_term ?u = component_of_term ?v" by (simp add: term_simps)
  moreover have "w = term_of_pair (pp_of_term ?u + pp_of_term ?v, component_of_term ?u)"
    by (simp add: eq[symmetric] term_simps)
  ultimately show ?thesis ..
qed

lemma lookup_mult_vec_monomial_left:
  "lookup (monomial c v ** p) u =
        (c * lookup p (term_of_pair (pp_of_term u - pp_of_term v, component_of_term u)) when v adds\<^sub>t u)"
proof -
  have eq1: "lookup ((monomial c (pp_of_term v) when component_of_term v = component_of_term u) * proj_poly (component_of_term u) p)
                (pp_of_term u) =
        (lookup ((monomial c (pp_of_term v)) * proj_poly (component_of_term u) p) (pp_of_term u) when
                component_of_term v = component_of_term u)"
    by (rule when_distrib, simp)
  show ?thesis
    by (simp add: lookup_mult_vec proj_monomial eq1 lookup_times_monomial_left when_when
        adds_term_def lookup_proj_poly conj_commute)
qed

lemma lookup_mult_vec_monomial_right:
  "lookup (p ** monomial c v) u =
        (lookup p (term_of_pair (pp_of_term u - pp_of_term v, component_of_term u)) * c when v adds\<^sub>t u)"
proof -
  have eq1: "lookup (proj_poly (component_of_term u) p * (monomial c (pp_of_term v) when component_of_term v = component_of_term u))
                (pp_of_term u) =
        (lookup (proj_poly (component_of_term u) p * (monomial c (pp_of_term v))) (pp_of_term u) when
                component_of_term v = component_of_term u)"
    by (rule when_distrib, simp)
  show ?thesis
    by (simp add: lookup_mult_vec proj_monomial eq1 lookup_times_monomial_right when_when
        adds_term_def lookup_proj_poly conj_commute)
qed

subsection \<open>Scalar Multiplication\<close>

definition mult_scalar :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::semiring_0)" (infixl "\<odot>" 75)
  where "mult_scalar p = lift_poly_fun ((*) p)"

lemma lookup_mult_scalar:
  "lookup (p \<odot> q) v = lookup (p * (proj_poly (component_of_term v) q)) (pp_of_term v)"
  unfolding mult_scalar_def by (rule lookup_lift_poly_fun_homogenous, simp)

lemma lookup_mult_scalar_explicit:
  "lookup (p \<odot> q) u = (\<Sum>t\<in>keys p. lookup p t * (\<Sum>v\<in>keys q. lookup q v when u = t \<oplus> v))"
proof -
  let ?f = "\<lambda>t s. lookup (proj_poly (component_of_term u) q) s when pp_of_term u = t + s"
  note lookup_mult_scalar
  also have "lookup (p * proj_poly (component_of_term u) q) (pp_of_term u) =
              (\<Sum>t. lookup p t * (Sum_any (?f t)))"
    by (fact lookup_mult)
  also from finite_keys have "\<dots> = (\<Sum>t\<in>keys p. lookup p t * (Sum_any (?f t)))"
    by (rule Sum_any.expand_superset) (auto simp: in_keys_iff dest: mult_not_zero)
  also from refl have "\<dots> = (\<Sum>t\<in>keys p. lookup p t * (\<Sum>v\<in>keys q. lookup q v when u = t \<oplus> v))"
  proof (rule sum.cong)
    fix t
    assume "t \<in> keys p"
    from finite_keys have "Sum_any (?f t) = (\<Sum>s\<in>keys (proj_poly (component_of_term u) q). ?f t s)"
      by (rule Sum_any.expand_superset) (auto simp: in_keys_iff)
    also have "\<dots> = (\<Sum>v\<in>{x \<in> keys q. component_of_term x = component_of_term u}. ?f t (pp_of_term v))"
      unfolding keys_proj_poly
    proof (intro sum.reindex[simplified o_def] inj_onI)
      fix v1 v2
      assume "v1 \<in> {x \<in> keys q. component_of_term x = component_of_term u}"
        and "v2 \<in> {x \<in> keys q. component_of_term x = component_of_term u}"
      hence "component_of_term v1 = component_of_term v2" by simp
      moreover assume "pp_of_term v1 = pp_of_term v2"
      ultimately show "v1 = v2" by (metis term_of_pair_pair)
    qed
    also from finite_keys have "\<dots> = (\<Sum>v\<in>keys q. lookup q v when u = t \<oplus> v)"
    proof (intro sum.mono_neutral_cong_left ballI)
      fix v
      assume "v \<in> keys q - {x \<in> keys q. component_of_term x = component_of_term u}"
      hence "u \<noteq> t \<oplus> v" by (auto simp: component_of_term_splus)
      thus "(lookup q v when u = t \<oplus> v) = 0" by simp
    next
      fix v
      assume "v \<in> {x \<in> keys q. component_of_term x = component_of_term u}"
      hence eq[symmetric]: "component_of_term v = component_of_term u" by simp
      have "u = t \<oplus> v \<longleftrightarrow> pp_of_term u = t + pp_of_term v"
      proof
        assume "pp_of_term u = t + pp_of_term v"
        hence "pp_of_term u = pp_of_term (t \<oplus> v)" by (simp only: pp_of_term_splus)
        moreover have "component_of_term u = component_of_term (t \<oplus> v)"
          by (simp only: eq component_of_term_splus)
        ultimately show "u = t \<oplus> v" by (metis term_of_pair_pair)
      qed (simp add: pp_of_term_splus)
      thus "?f t (pp_of_term v) = (lookup q v when u = t \<oplus> v)"
        by (simp add: lookup_proj_poly eq term_of_pair_pair)
    qed auto
    finally show "lookup p t * (Sum_any (?f t)) = lookup p t * (\<Sum>v\<in>keys q. lookup q v when u = t \<oplus> v)"
      by (simp only:)
  qed
  finally show ?thesis .
qed

lemma proj_mult_scalar [term_simps]: "proj_poly k (p \<odot> q) = p * (proj_poly k q)"
  unfolding mult_scalar_def by (rule proj_lift_poly_fun_homogenous, simp)

lemma mult_scalar_zero_left [simp]: "0 \<odot> p = 0"
  by (rule poly_mapping_eqI_proj, simp add: term_simps)

lemma mult_scalar_zero_right [simp]: "p \<odot> 0 = 0"
  by (rule poly_mapping_eqI_proj, simp add: term_simps)

lemma mult_scalar_one [simp]: "(1::_ \<Rightarrow>\<^sub>0 'b::semiring_1) \<odot> p = p"
  by (rule poly_mapping_eqI_proj, simp add: term_simps)

lemma mult_scalar_assoc [ac_simps]: "(p * q) \<odot> r = p \<odot> (q \<odot> r)"
  by (rule poly_mapping_eqI_proj, simp add: ac_simps term_simps)

lemma mult_scalar_distrib_right [algebra_simps]: "(p + q) \<odot> r = p \<odot> r + q \<odot> r"
  by (rule poly_mapping_eqI_proj, simp add: algebra_simps proj_plus term_simps)

lemma mult_scalar_distrib_left [algebra_simps]: "r \<odot> (p + q) = r \<odot> p + r \<odot> q"
  by (rule poly_mapping_eqI_proj, simp add: algebra_simps proj_plus term_simps)

lemma mult_scalar_minus_mult_left [simp]: "(- p) \<odot> q = - (p \<odot> q)"
  by (rule sym, rule minus_unique, simp add: mult_scalar_distrib_right[symmetric])

lemma mult_scalar_minus_mult_right [simp]: "p \<odot> (- q) = - (p \<odot> q)"
  by (rule sym, rule minus_unique, simp add: mult_scalar_distrib_left [symmetric])

lemma minus_mult_scalar_minus [simp]: "(- p) \<odot> (- q) = p \<odot> q"
  by simp

lemma minus_mult_scalar_commute: "(- p) \<odot> q = p \<odot> (- q)"
  by simp

lemma mult_scalar_right_diff_distrib [algebra_simps]: "r \<odot> (p - q) = r \<odot> p - r \<odot> q"
  for r::"_ \<Rightarrow>\<^sub>0 'b::ring"
  using mult_scalar_distrib_left [of r p "- q"] by simp

lemma mult_scalar_left_diff_distrib [algebra_simps]: "(p - q) \<odot> r = p \<odot> r - q \<odot> r"
  for p::"_ \<Rightarrow>\<^sub>0 'b::ring"
  using mult_scalar_distrib_right [of p "- q" r] by simp

lemma sum_mult_scalar_distrib_left: "r \<odot> (sum f A) = (\<Sum>a\<in>A. r \<odot> f a)"
  by (induct A rule: infinite_finite_induct, simp_all add: algebra_simps)

lemma sum_mult_scalar_distrib_right: "(sum f A) \<odot> v = (\<Sum>a\<in>A. f a \<odot> v)"
  by (induct A rule: infinite_finite_induct, simp_all add: algebra_simps)

lemma mult_scalar_monomial_monomial: "(monomial c t) \<odot> (monomial d v) = monomial (c * d) (t \<oplus> v)"
  by (rule poly_mapping_eqI_proj, simp add: proj_monomial mult_single when_def term_simps)

lemma mult_scalar_monomial: "(monomial c t) \<odot> p = monom_mult c t p"
  by (rule poly_mapping_eqI_proj, rule poly_mapping_eqI,
      auto simp add: lookup_times_monomial_left lookup_proj_poly lookup_monom_mult when_def
        adds_pp_def sminus_def term_simps)

lemma mult_scalar_rec_left: "p \<odot> q = monom_mult (lookup p t) t q + (except p {t}) \<odot> q"
proof -
  from plus_except[of p t] have "p \<odot> q = (monomial (lookup p t) t + except p {t}) \<odot> q" by simp
  also have "... = monomial (lookup p t) t \<odot> q + except p {t} \<odot> q" by (simp only: algebra_simps)
  finally show ?thesis by (simp only: mult_scalar_monomial)
qed

lemma mult_scalar_rec_right: "p \<odot> q = p \<odot> monomial (lookup q v) v + p \<odot> except q {v}"
proof -
  have "p \<odot> monomial (lookup q v) v + p \<odot> except q {v} = p \<odot> (monomial (lookup q v) v + except q {v})"
    by (simp only: mult_scalar_distrib_left)
  also have "... = p \<odot> q" by (simp only: plus_except[of q v, symmetric])
  finally show ?thesis by simp
qed

lemma in_keys_mult_scalarE:
  assumes "v \<in> keys (p \<odot> q)"
  obtains t u where "t \<in> keys p" and "u \<in> keys q" and "v = t \<oplus> u"
proof -
  from assms have "0 \<noteq> lookup (p \<odot> q) v" by (simp add: in_keys_iff)
  also have "lookup (p \<odot> q) v = lookup (p * (proj_poly (component_of_term v) q)) (pp_of_term v)"
    by (fact lookup_mult_scalar)
  finally have "pp_of_term v \<in> keys (p * proj_poly (component_of_term v) q)" by (simp add: in_keys_iff)
  from this keys_mult have "pp_of_term v \<in> {t + s |t s. t \<in> keys p \<and> s \<in> keys (proj_poly (component_of_term v) q)}" ..
  then obtain t s where "t \<in> keys p" and *: "s \<in> keys (proj_poly (component_of_term v) q)"
    and eq: "pp_of_term v = t + s" by fastforce
  note this(1)
  moreover from * have "term_of_pair (s, component_of_term v) \<in> keys q"
    by (simp only: in_keys_iff lookup_proj_poly not_False_eq_True)
  moreover have "v = t \<oplus> term_of_pair (s, component_of_term v)"
    by (simp add: splus_def eq[symmetric] term_simps)
  ultimately show ?thesis ..
qed

lemma lookup_mult_scalar_monomial_right:
  "lookup (p \<odot> monomial c v) u = (lookup p (pp_of_term u - pp_of_term v) * c when v adds\<^sub>t u)"
proof -
  have eq1: "lookup (p * (monomial c (pp_of_term v) when component_of_term v = component_of_term u)) (pp_of_term u) =
             (lookup (p * (monomial c (pp_of_term v))) (pp_of_term u) when component_of_term v = component_of_term u)"
    by (rule when_distrib, simp)
  show ?thesis
    by (simp add: lookup_mult_scalar eq1 proj_monomial lookup_times_monomial_right when_when
        adds_term_def lookup_proj_poly conj_commute)
qed

lemma lookup_mult_scalar_monomial_right_plus: "lookup (p \<odot> monomial c v) (t \<oplus> v) = lookup p t * c"
  by (simp add: lookup_mult_scalar_monomial_right term_simps)

lemma keys_mult_scalar_monomial_right_subset: "keys (p \<odot> monomial c v) \<subseteq> (\<lambda>t. t \<oplus> v) ` keys p"
proof
  fix u
  assume "u \<in> keys (p \<odot> monomial c v)"
  then obtain t w where "t \<in> keys p" and "w \<in> keys (monomial c v)" and "u = t \<oplus> w"
    by (rule in_keys_mult_scalarE)
  from this(2) have "w = v" by (metis empty_iff insert_iff keys_single)
  from \<open>t \<in> keys p\<close> show "u \<in> (\<lambda>t. t \<oplus> v) ` keys p" unfolding \<open>u = t \<oplus> w\<close> \<open>w = v\<close> by fastforce
qed

lemma keys_mult_scalar_monomial_right:
  assumes "c \<noteq> (0::'b::semiring_no_zero_divisors)"
  shows "keys (p \<odot> monomial c v) = (\<lambda>t. t \<oplus> v) ` keys p"
proof
  show "(\<lambda>t. t \<oplus> v) ` keys p \<subseteq> keys (p \<odot> monomial c v)"
  proof
    fix u
    assume "u \<in> (\<lambda>t. t \<oplus> v) ` keys p"
    then obtain t where "t \<in> keys p" and "u = t \<oplus> v" ..
    have "lookup (p \<odot> monomial c v) (t \<oplus> v) = lookup p t * c"
      by (fact lookup_mult_scalar_monomial_right_plus)
    also from \<open>t \<in> keys p\<close> assms have "... \<noteq> 0" by (simp add: in_keys_iff)
    finally show "u \<in> keys (p \<odot> monomial c v)" by (simp add: in_keys_iff \<open>u = t \<oplus> v\<close>)
  qed
qed (fact keys_mult_scalar_monomial_right_subset)

end (* term_powerprod *)

subsection \<open>Sums and Products\<close>

lemma sum_poly_mapping_eq_zeroI:
  assumes "p ` A \<subseteq> {0}"
  shows "sum p A = (0::(_ \<Rightarrow>\<^sub>0 'b::comm_monoid_add))"
proof (rule ccontr)
  assume "sum p A \<noteq> 0"
  then obtain a where "a \<in> A" and "p a \<noteq> 0"
    by (rule comm_monoid_add_class.sum.not_neutral_contains_not_neutral)
  with assms show False by auto
qed

lemma lookup_sum_list: "lookup (sum_list ps) a = sum_list (map (\<lambda>p. lookup p a) ps)"
proof (induct ps)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  thus ?case by (simp add: lookup_add)
qed

text \<open>Legacy:\<close>
lemmas keys_sum_subset = Poly_Mapping.keys_sum

lemma keys_sum_list_subset: "keys (sum_list ps) \<subseteq> Keys (set ps)"
proof (induct ps)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  have "keys (sum_list (p # ps)) = keys (p + sum_list ps)" by simp
  also have "\<dots> \<subseteq> keys p \<union> keys (sum_list ps)" by (fact Poly_Mapping.keys_add)
  also from Cons have "\<dots> \<subseteq> keys p \<union> Keys (set ps)" by blast
  also have "\<dots> = Keys (set (p # ps))" by (simp add: Keys_insert)
  finally show ?case .
qed

lemma keys_sum:
  assumes "finite A" and "\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> a1 \<noteq> a2 \<Longrightarrow> keys (f a1) \<inter> keys (f a2) = {}"
  shows "keys (sum f A) = (\<Union>a\<in>A. keys (f a))"
  using assms
proof (induct A)
  case empty
  show ?case by simp
next
  case (insert a A)
  have IH: "keys (sum f A) = (\<Union>i\<in>A. keys (f i))" by (rule insert(3), rule insert.prems, simp_all)
  have "keys (sum f (insert a A)) = keys (f a) \<union> keys (sum f A)"
  proof (simp only: comm_monoid_add_class.sum.insert[OF insert(1) insert(2)], rule keys_add[symmetric])
    have "keys (f a) \<inter> keys (sum f A) = (\<Union>i\<in>A. keys (f a) \<inter> keys (f i))"
      by (simp only: IH Int_UN_distrib)
    also have "... = {}"
    proof -
      have "i \<in> A \<Longrightarrow> keys (f a) \<inter> keys (f i) = {}" for i
      proof (rule insert.prems)
        assume "i \<in> A"
        with insert(2) show "a \<noteq> i" by blast
      qed simp_all
      thus ?thesis by simp
    qed
    finally show "keys (f a) \<inter> keys (sum f A) = {}" .
  qed
  also have "... = (\<Union>a\<in>insert a A. keys (f a))" by (simp add: IH)
  finally show ?case .
qed

lemma poly_mapping_sum_monomials: "(\<Sum>a\<in>keys p. monomial (lookup p a) a) = p"
proof (induct p rule: poly_mapping_plus_induct)
  case 1
  show ?case by simp
next
  case step: (2 p c t)
  from step(2) have "lookup p t = 0" by (simp add: in_keys_iff)
  have *: "keys (monomial c t + p) = insert t (keys p)"
  proof -
    from step(1) have a: "keys (monomial c t) = {t}" by simp
    with step(2) have "keys (monomial c t) \<inter> keys p = {}" by simp
    hence "keys (monomial c t + p) = {t} \<union> keys p" by (simp only: a keys_plus_eqI)
    thus ?thesis by simp
  qed
  have **: "(\<Sum>ta\<in>keys p. monomial ((c when t = ta) + lookup p ta) ta) = (\<Sum>ta\<in>keys p. monomial (lookup p ta) ta)"
  proof (rule comm_monoid_add_class.sum.cong, rule refl)
    fix s
    assume "s \<in> keys p"
    with step(2) have "t \<noteq> s" by auto
    thus "monomial ((c when t = s) + lookup p s) s = monomial (lookup p s) s" by simp
  qed
    show ?case by (simp only: * comm_monoid_add_class.sum.insert[OF finite_keys step(2)],
                   simp add: lookup_add lookup_single \<open>lookup p t = 0\<close> ** step(3))
  qed

lemma monomial_sum: "monomial (sum f C) a = (\<Sum>c\<in>C. monomial (f c) a)"
  by (rule fun_sum_commute, simp_all add: single_add)

lemma monomial_Sum_any:
  assumes "finite {c. f c \<noteq> 0}"
  shows "monomial (Sum_any f) a = (\<Sum>c. monomial (f c) a)"
proof -
  have "{c. monomial (f c) a \<noteq> 0} \<subseteq> {c. f c \<noteq> 0}" by (rule, auto)
  with assms show ?thesis
    by (simp add: Groups_Big_Fun.comm_monoid_add_class.Sum_any.expand_superset monomial_sum)
qed

context term_powerprod
begin

lemma proj_sum: "proj_poly k (sum f A) = (\<Sum>a\<in>A. proj_poly k (f a))"
  using proj_zero proj_plus by (rule fun_sum_commute)

lemma proj_sum_list: "proj_poly k (sum_list xs) = sum_list (map (proj_poly k) xs)"
  using proj_zero proj_plus by (rule fun_sum_list_commute)

lemma mult_scalar_sum_monomials: "q \<odot> p = (\<Sum>t\<in>keys q. monom_mult (lookup q t) t p)"
  by (rule poly_mapping_eqI_proj, simp add: proj_sum mult_scalar_monomial[symmetric]
      sum_distrib_right[symmetric] poly_mapping_sum_monomials term_simps)

lemma fun_mult_scalar_commute:
  assumes "f 0 = 0" and "\<And>x y. f (x + y) = f x + f y"
    and "\<And>c t. f (monom_mult c t p) = monom_mult c t (f p)"
  shows "f (q \<odot> p) = q \<odot> (f p)"
  by (simp add: mult_scalar_sum_monomials assms(3)[symmetric], rule fun_sum_commute, fact+)

lemma fun_mult_scalar_commute_canc:
  assumes "\<And>x y. f (x + y) = f x + f y" and "\<And>c t. f (monom_mult c t p) = monom_mult c t (f p)"
  shows "f (q \<odot> p) = q \<odot> (f (p::'t \<Rightarrow>\<^sub>0 'b::{semiring_0,cancel_comm_monoid_add}))"
  by (simp add: mult_scalar_sum_monomials assms(2)[symmetric], rule fun_sum_commute_canc, fact)

lemma monom_mult_sum_left: "monom_mult (sum f C) t p = (\<Sum>c\<in>C. monom_mult (f c) t p)"
  by (rule fun_sum_commute, simp_all add: monom_mult_dist_left)

lemma monom_mult_sum_right: "monom_mult c t (sum f P) = (\<Sum>p\<in>P. monom_mult c t (f p))"
  by (rule fun_sum_commute, simp_all add: monom_mult_dist_right)

lemma monom_mult_Sum_any_left:
  assumes "finite {c. f c \<noteq> 0}"
  shows "monom_mult (Sum_any f) t p = (\<Sum>c. monom_mult (f c) t p)"
proof -
  have "{c. monom_mult (f c) t p \<noteq> 0} \<subseteq> {c. f c \<noteq> 0}" by (rule, auto)
  with assms show ?thesis
    by (simp add: Groups_Big_Fun.comm_monoid_add_class.Sum_any.expand_superset monom_mult_sum_left)
qed

lemma monom_mult_Sum_any_right:
  assumes "finite {p. f p \<noteq> 0}"
  shows "monom_mult c t (Sum_any f) = (\<Sum>p. monom_mult c t (f p))"
proof -
  have "{p. monom_mult c t (f p) \<noteq> 0} \<subseteq> {p. f p \<noteq> 0}" by (rule, auto)
  with assms show ?thesis
    by (simp add: Groups_Big_Fun.comm_monoid_add_class.Sum_any.expand_superset monom_mult_sum_right)
qed

lemma monomial_prod_sum: "monomial (prod c I) (sum a I) = (\<Prod>i\<in>I. monomial (c i) (a i))"
proof (cases "finite I")
  case True
  thus ?thesis
  proof (induct I)
    case empty
    show ?case by simp
  next
    case (insert i I)
    show ?case
      by (simp only: comm_monoid_add_class.sum.insert[OF insert(1) insert(2)]
         comm_monoid_mult_class.prod.insert[OF insert(1) insert(2)] insert(3) mult_single[symmetric])
  qed
next
  case False
  thus ?thesis by simp
qed

subsection \<open>Submodules\<close>

sublocale pmdl: module mult_scalar
  apply standard
  subgoal by (rule poly_mapping_eqI_proj, simp add: algebra_simps proj_plus)
  subgoal by (rule poly_mapping_eqI_proj, simp add: algebra_simps proj_plus)
  subgoal by (rule poly_mapping_eqI_proj, simp add: ac_simps)
  subgoal by (rule poly_mapping_eqI_proj, simp)
  done

lemmas [simp del] = pmdl.scale_one pmdl.scale_zero_left pmdl.scale_zero_right pmdl.scale_scale
  pmdl.scale_minus_left pmdl.scale_minus_right pmdl.span_eq_iff

lemmas [algebra_simps del] = pmdl.scale_left_distrib pmdl.scale_right_distrib
  pmdl.scale_left_diff_distrib pmdl.scale_right_diff_distrib

abbreviation "pmdl \<equiv> pmdl.span"

lemma pmdl_closed_monom_mult:
  assumes "p \<in> pmdl B"
  shows "monom_mult c t p \<in> pmdl B"
  unfolding mult_scalar_monomial[symmetric] using assms by (rule pmdl.span_scale)

lemma monom_mult_in_pmdl: "b \<in> B \<Longrightarrow> monom_mult c t b \<in> pmdl B"
  by (intro pmdl_closed_monom_mult pmdl.span_base)

lemma pmdl_induct [consumes 1, case_names module_0 module_plus]:
  assumes "p \<in> pmdl B" and "P 0"
    and "\<And>a p c t. a \<in> pmdl B \<Longrightarrow> P a \<Longrightarrow> p \<in> B \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> P (a + monom_mult c t p)"
  shows "P p"
  using assms(1)
proof (induct p rule: pmdl.span_induct')
  case base
  from assms(2) show ?case .
next
  case (step a q b)
  from this(1) this(2) show ?case
  proof (induct q arbitrary: a rule: poly_mapping_except_induct)
    case 1
    thus ?case by simp
  next
    case step: (2 q0 t)
    from this(4) step(5) \<open>b \<in> B\<close> have "P (a + monomial (lookup q0 t) t \<odot> b)"
      unfolding mult_scalar_monomial
    proof (rule assms(3))
      from step(2) show "lookup q0 t \<noteq> 0" by (simp add: in_keys_iff)
    qed
    with _ have "P ((a + monomial (lookup q0 t) t \<odot> b) + except q0 {t} \<odot> b)"
    proof (rule step(3))
      from \<open>b \<in> B\<close> have "b \<in> pmdl B" by (rule pmdl.span_base)
      hence "monomial (lookup q0 t) t \<odot> b \<in> pmdl B" by (rule pmdl.span_scale)
      with step(4) show "a + monomial (lookup q0 t) t \<odot> b \<in> pmdl B" by (rule pmdl.span_add)
    qed
    hence "P (a + (monomial (lookup q0 t) t + except q0 {t}) \<odot> b)" by (simp add: algebra_simps)
    thus ?case by (simp only: plus_except[of q0 t, symmetric])
  qed
qed

lemma components_pmdl: "component_of_term ` Keys (pmdl B) = component_of_term ` Keys B"
proof
  show "component_of_term ` Keys (pmdl B) \<subseteq> component_of_term ` Keys B"
  proof
    fix k
    assume "k \<in> component_of_term ` Keys (pmdl B)"
    then obtain v where "v \<in> Keys (pmdl B)" and "k = component_of_term v" ..
    from this(1) obtain b where "b \<in> pmdl B" and "v \<in> keys b" by (rule in_KeysE)
    thus "k \<in> component_of_term ` Keys B"
    proof (induct b rule: pmdl_induct)
      case module_0
      thus ?case by simp
    next
      case ind: (module_plus a p c t)
      from ind.prems Poly_Mapping.keys_add have "v \<in> keys a \<union> keys (monom_mult c t p)" ..
      thus ?case
      proof
        assume "v \<in> keys a"
        thus ?thesis by (rule ind.hyps(2))
      next
        assume "v \<in> keys (monom_mult c t p)"
        from this keys_monom_mult_subset have "v \<in> (\<oplus>) t ` keys p" ..
        then obtain u where "u \<in> keys p" and "v = t \<oplus> u" ..
        have "k = component_of_term u" by (simp add: \<open>k = component_of_term v\<close> \<open>v = t \<oplus> u\<close> term_simps)
        moreover from \<open>u \<in> keys p\<close> ind.hyps(3) have "u \<in> Keys B" by (rule in_KeysI)
        ultimately show ?thesis ..
      qed
    qed
  qed
next
  show "component_of_term ` Keys B \<subseteq> component_of_term ` Keys (pmdl B)"
    by (rule image_mono, rule Keys_mono, fact pmdl.span_superset)
qed

lemma pmdl_idI:
  assumes "0 \<in> B" and "\<And>b1 b2. b1 \<in> B \<Longrightarrow> b2 \<in> B \<Longrightarrow> b1 + b2 \<in> B"
    and "\<And>c t b. b \<in> B \<Longrightarrow> monom_mult c t b \<in> B"
  shows "pmdl B = B"
proof
  show "pmdl B \<subseteq> B"
  proof
    fix p
    assume "p \<in> pmdl B"
    thus "p \<in> B"
    proof (induct p rule: pmdl_induct)
      case module_0
      show ?case by (fact assms(1))
    next
      case step: (module_plus a b c t)
      from step(2) show ?case
      proof (rule assms(2))
        from step(3) show "monom_mult c t b \<in> B" by (rule assms(3))
      qed
    qed
  qed
qed (fact pmdl.span_superset)

definition full_pmdl :: "'k set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero) set"
  where "full_pmdl K = {p. component_of_term ` keys p \<subseteq> K}"

definition is_full_pmdl :: "('t \<Rightarrow>\<^sub>0 'b::comm_ring_1) set \<Rightarrow> bool"
  where "is_full_pmdl B \<longleftrightarrow> (\<forall>p. component_of_term ` keys p \<subseteq> component_of_term ` Keys B \<longrightarrow> p \<in> pmdl B)"

lemma full_pmdl_iff: "p \<in> full_pmdl K \<longleftrightarrow> component_of_term ` keys p \<subseteq> K"
  by (simp add: full_pmdl_def)

lemma full_pmdlI:
  assumes "\<And>v. v \<in> keys p \<Longrightarrow> component_of_term v \<in> K"
  shows "p \<in> full_pmdl K"
  using assms by (auto simp add: full_pmdl_iff)

lemma full_pmdlD:
  assumes "p \<in> full_pmdl K" and "v \<in> keys p"
  shows "component_of_term v \<in> K"
  using assms by (auto simp add: full_pmdl_iff)

lemma full_pmdl_empty: "full_pmdl {} = {0}"
  by (simp add: full_pmdl_def)

lemma full_pmdl_UNIV: "full_pmdl UNIV = UNIV"
  by (simp add: full_pmdl_def)

lemma zero_in_full_pmdl: "0 \<in> full_pmdl K"
  by (simp add: full_pmdl_iff)

lemma full_pmdl_closed_plus:
  assumes "p \<in> full_pmdl K" and "q \<in> full_pmdl K"
  shows "p + q \<in> full_pmdl K"
proof (rule full_pmdlI)
  fix v
  assume "v \<in> keys (p + q)"
  also have "... \<subseteq> keys p \<union> keys q" by (fact Poly_Mapping.keys_add)
  finally show "component_of_term v \<in> K"
  proof
    assume "v \<in> keys p"
    with assms(1) show ?thesis by (rule full_pmdlD)
  next
    assume "v \<in> keys q"
    with assms(2) show ?thesis by (rule full_pmdlD)
  qed
qed

lemma full_pmdl_closed_monom_mult:
  assumes "p \<in> full_pmdl K"
  shows "monom_mult c t p \<in> full_pmdl K"
proof (rule full_pmdlI)
  fix v
  assume "v \<in> keys (monom_mult c t p)"
  also have "... \<subseteq> (\<oplus>) t ` keys p" by (fact keys_monom_mult_subset)
  finally obtain u where "u \<in> keys p" and v: "v = t \<oplus> u" ..
  have "component_of_term v = component_of_term u" by (simp add: v term_simps)
  also from assms \<open>u \<in> keys p\<close> have "... \<in> K" by (rule full_pmdlD)
  finally show "component_of_term v \<in> K" .
qed

lemma pmdl_full_pmdl: "pmdl (full_pmdl K) = full_pmdl K"
  using zero_in_full_pmdl full_pmdl_closed_plus full_pmdl_closed_monom_mult by (rule pmdl_idI)

lemma components_full_pmdl_subset:
  "component_of_term ` Keys ((full_pmdl K)::('t \<Rightarrow>\<^sub>0 'b::zero) set) \<subseteq> K" (is "?l \<subseteq> _")
proof
  let ?M = "(full_pmdl K)::('t \<Rightarrow>\<^sub>0 'b) set"
  fix k
  assume "k \<in> ?l"
  then obtain v where "v \<in> Keys ?M" and k: "k = component_of_term v" ..
  from this(1) obtain p where "p \<in> ?M" and "v \<in> keys p" by (rule in_KeysE)
  thus "k \<in> K" unfolding k by (rule full_pmdlD)
qed

lemma components_full_pmdl:
  "component_of_term ` Keys ((full_pmdl K)::('t \<Rightarrow>\<^sub>0 'b::zero_neq_one) set) = K" (is "?l = _")
proof
  let ?M = "(full_pmdl K)::('t \<Rightarrow>\<^sub>0 'b) set"
  show "K \<subseteq> ?l"
  proof
    fix k
    assume "k \<in> K"
    hence "monomial 1 (term_of_pair (0, k)) \<in> ?M" by (simp add: full_pmdl_iff term_simps)
    hence "keys (monomial (1::'b) (term_of_pair (0, k))) \<subseteq> Keys ?M" by (rule keys_subset_Keys)
    hence "term_of_pair (0, k) \<in> Keys ?M" by simp
    hence "component_of_term (term_of_pair (0, k)) \<in> component_of_term ` Keys ?M" by (rule imageI)
    thus "k \<in> ?l" by (simp only: component_of_term_of_pair)
  qed
qed (fact components_full_pmdl_subset)

lemma is_full_pmdlI:
  assumes "\<And>p. component_of_term ` keys p \<subseteq> component_of_term ` Keys B \<Longrightarrow> p \<in> pmdl B"
  shows "is_full_pmdl B"
  unfolding is_full_pmdl_def using assms by blast

lemma is_full_pmdlD:
  assumes "is_full_pmdl B" and "component_of_term ` keys p \<subseteq> component_of_term ` Keys B"
  shows "p \<in> pmdl B"
  using assms unfolding is_full_pmdl_def by blast

lemma is_full_pmdl_alt: "is_full_pmdl B \<longleftrightarrow> pmdl B = full_pmdl (component_of_term ` Keys B)"
proof -
  have "b \<in> pmdl B \<Longrightarrow> v \<in> keys b \<Longrightarrow> component_of_term v \<in> component_of_term ` Keys B" for b v
    by (metis components_pmdl image_eqI in_KeysI)
  thus ?thesis by (auto simp add: is_full_pmdl_def full_pmdl_def)
qed

lemma is_full_pmdl_pmdl: "is_full_pmdl (pmdl B) \<longleftrightarrow> is_full_pmdl B"
  by (simp only: is_full_pmdl_def pmdl.span_span components_pmdl)

lemma is_full_pmdl_subset:
  assumes "is_full_pmdl B1" and "is_full_pmdl B2"
    and "component_of_term ` Keys B1 \<subseteq> component_of_term ` Keys B2"
  shows "pmdl B1 \<subseteq> pmdl B2"
proof
  fix p
  assume "p \<in> pmdl B1"
  from assms(2) show "p \<in> pmdl B2"
  proof (rule is_full_pmdlD)
    have "component_of_term ` keys p \<subseteq> component_of_term ` Keys (pmdl B1)"
      by (rule image_mono, rule keys_subset_Keys, fact)
    also have "... = component_of_term ` Keys B1" by (fact components_pmdl)
    finally show "component_of_term ` keys p \<subseteq> component_of_term ` Keys B2" using assms(3)
      by (rule subset_trans)
  qed
qed

lemma is_full_pmdl_eq:
  assumes "is_full_pmdl B1" and "is_full_pmdl B2"
    and "component_of_term ` Keys B1 = component_of_term ` Keys B2"
  shows "pmdl B1 = pmdl B2"
proof
  have "component_of_term ` Keys B1 \<subseteq> component_of_term ` Keys B2" by (simp add: assms(3))
  with assms(1, 2) show "pmdl B1 \<subseteq> pmdl B2" by (rule is_full_pmdl_subset)
next
  have "component_of_term ` Keys B2 \<subseteq> component_of_term ` Keys B1" by (simp add: assms(3))
  with assms(2, 1) show "pmdl B2 \<subseteq> pmdl B1" by (rule is_full_pmdl_subset)
qed

end (* term_powerprod *)

definition map_scale :: "'b \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::mult_zero)" (infixr "\<cdot>" 71)
  where "map_scale c = Poly_Mapping.map ((*) c)"

text \<open>If the polynomial mapping \<open>p\<close> is interpreted as a power-product, then @{term "c \<cdot> p"}
  corresponds to exponentiation; if it is interpreted as a (vector-) polynomial, then @{term "c \<cdot> p"}
  corresponds to multiplication by scalar from the coefficient type.\<close>

lemma lookup_map_scale [simp]: "lookup (c \<cdot> p) = (\<lambda>x. c * lookup p x)"
  by (auto simp: map_scale_def map.rep_eq when_def)

lemma map_scale_single [simp]: "k \<cdot> Poly_Mapping.single x l = Poly_Mapping.single x (k * l)"
  by (simp add: map_scale_def)

lemma map_scale_zero_left [simp]: "0 \<cdot> t = 0"
  by (rule poly_mapping_eqI) simp

lemma map_scale_zero_right [simp]: "k \<cdot> 0 = 0"
  by (rule poly_mapping_eqI) simp

lemma map_scale_eq_0_iff: "c \<cdot> t = 0 \<longleftrightarrow> ((c::_::semiring_no_zero_divisors) = 0 \<or> t = 0)"
  by (metis aux lookup_map_scale mult_eq_0_iff)

lemma keys_map_scale_subset: "keys (k \<cdot> t) \<subseteq> keys t"
  by (metis in_keys_iff lookup_map_scale mult_zero_right subsetI)

lemma keys_map_scale: "keys ((k::'b::semiring_no_zero_divisors) \<cdot> t) = (if k = 0 then {} else keys t)"
proof (split if_split, intro conjI impI)
  assume "k = 0"
  thus "keys (k \<cdot> t) = {}" by simp
next
  assume "k \<noteq> 0"
  show "keys (k \<cdot> t) = keys t"
  proof
    show "keys t \<subseteq> keys (k \<cdot> t)" by rule (simp add: \<open>k \<noteq> 0\<close> flip: lookup_not_eq_zero_eq_in_keys)
  qed (fact keys_map_scale_subset)
qed

lemma map_scale_one_left [simp]: "(1::'b::{mult_zero,monoid_mult}) \<cdot> t = t"
  by (rule poly_mapping_eqI) simp

lemma map_scale_assoc [ac_simps]: "c \<cdot> d \<cdot> t = (c * d) \<cdot> (t::_ \<Rightarrow>\<^sub>0 _::{semigroup_mult,zero})"
  by (rule poly_mapping_eqI) (simp add: ac_simps)

lemma map_scale_distrib_left [algebra_simps]: "(k::'b::semiring_0) \<cdot> (s + t) = k \<cdot> s + k \<cdot> t"
  by (rule poly_mapping_eqI) (simp add: lookup_add distrib_left)

lemma map_scale_distrib_right [algebra_simps]: "(k + (l::'b::semiring_0)) \<cdot> t = k \<cdot> t + l \<cdot> t"
  by (rule poly_mapping_eqI) (simp add: lookup_add distrib_right)

lemma map_scale_Suc: "(Suc k) \<cdot> t = k \<cdot> t + t"
  by (rule poly_mapping_eqI) (simp add: lookup_add distrib_right)

lemma map_scale_uminus_left: "(- k::'b::ring) \<cdot> p = - (k \<cdot> p)"
  by (rule poly_mapping_eqI) auto

lemma map_scale_uminus_right: "(k::'b::ring) \<cdot> (- p) = - (k \<cdot> p)"
  by (rule poly_mapping_eqI) auto

lemma map_scale_uminus_uminus [simp]: "(- k::'b::ring) \<cdot> (- p) = k \<cdot> p"
  by (simp add: map_scale_uminus_left map_scale_uminus_right)

lemma map_scale_minus_distrib_left [algebra_simps]:
  "(k::'b::comm_semiring_1_cancel) \<cdot> (p - q) = k \<cdot> p - k \<cdot> q"
  by (rule poly_mapping_eqI) (auto simp add: lookup_minus right_diff_distrib')

lemma map_scale_minus_distrib_right [algebra_simps]:
  "(k - (l::'b::comm_semiring_1_cancel)) \<cdot> f = k \<cdot> f - l \<cdot> f"
  by (rule poly_mapping_eqI) (auto simp add: lookup_minus left_diff_distrib')

lemma map_scale_sum_distrib_left: "(k::'b::semiring_0) \<cdot> (sum f A) = (\<Sum>a\<in>A. k \<cdot> f a)"
  by (induct A rule: infinite_finite_induct) (simp_all add: map_scale_distrib_left)

lemma map_scale_sum_distrib_right: "(sum (f::_ \<Rightarrow> 'b::semiring_0) A) \<cdot> p = (\<Sum>a\<in>A. f a \<cdot> p)"
  by (induct A rule: infinite_finite_induct) (simp_all add: map_scale_distrib_right)

lemma deg_pm_map_scale: "deg_pm (k \<cdot> t) = (k::'b::semiring_0) * deg_pm t"
proof -
  from keys_map_scale_subset finite_keys have "deg_pm (k \<cdot> t) = sum (lookup (k \<cdot> t)) (keys t)"
    by (rule deg_pm_superset)
  also have "\<dots> = k * sum (lookup t) (keys t)" by (simp add: sum_distrib_left)
  also from subset_refl finite_keys have "sum (lookup t) (keys t) = deg_pm t"
    by (rule deg_pm_superset[symmetric])
  finally show ?thesis .
qed

interpretation phull: module map_scale
  apply standard
  subgoal by (fact map_scale_distrib_left)
  subgoal by (fact map_scale_distrib_right)
  subgoal by (fact map_scale_assoc)
  subgoal by (fact map_scale_one_left)
  done

text \<open>Since the following lemmas are proved for more general ring-types above, we do not need to
  have them in the simpset.\<close>

lemmas [simp del] = phull.scale_one phull.scale_zero_left phull.scale_zero_right phull.scale_scale
  phull.scale_minus_left phull.scale_minus_right phull.span_eq_iff

lemmas [algebra_simps del] = phull.scale_left_distrib phull.scale_right_distrib
  phull.scale_left_diff_distrib phull.scale_right_diff_distrib

abbreviation "phull \<equiv> phull.span"

text \<open>@{term \<open>phull B\<close>} is a module over the coefficient ring @{typ 'b}, whereas
  @{term \<open>term_powerprod.pmdl B\<close>} is a module over the (scalar) polynomial ring @{typ \<open>'a \<Rightarrow>\<^sub>0 'b\<close>}.
  Nevertheless, both modules can be sets of @{emph \<open>vector-polynomials\<close>} of type @{typ \<open>'t \<Rightarrow>\<^sub>0 'b\<close>}.\<close>

context term_powerprod
begin

lemma map_scale_eq_monom_mult: "c \<cdot> p = monom_mult c 0 p"
  by (rule poly_mapping_eqI) (simp only: lookup_map_scale lookup_monom_mult_zero)

lemma map_scale_eq_mult_scalar: "c \<cdot> p = monomial c 0 \<odot> p"
  by (simp only: map_scale_eq_monom_mult mult_scalar_monomial)

lemma phull_closed_mult_scalar: "p \<in> phull B \<Longrightarrow> monomial c 0 \<odot> p \<in> phull B"
  unfolding map_scale_eq_mult_scalar[symmetric] by (rule phull.span_scale)

lemma mult_scalar_in_phull: "b \<in> B \<Longrightarrow> monomial c 0 \<odot> b \<in> phull B"
  by (intro phull_closed_mult_scalar phull.span_base)

lemma phull_subset_module: "phull B \<subseteq> pmdl B"
proof
  fix p
  assume "p \<in> phull B"
  thus "p \<in> pmdl B"
  proof (induct p rule: phull.span_induct')
    case base
    show ?case by (fact pmdl.span_zero)
  next
    case (step a c p)
    from step(3) have "p \<in> pmdl B" by (rule pmdl.span_base)
    hence "c \<cdot> p \<in> pmdl B" unfolding map_scale_eq_monom_mult by (rule pmdl_closed_monom_mult)
    with step(2) show ?case by (rule pmdl.span_add)
  qed
qed

lemma components_phull: "component_of_term ` Keys (phull B) = component_of_term ` Keys B"
proof
  have "component_of_term ` Keys (phull B) \<subseteq> component_of_term ` Keys (pmdl B)"
    by (rule image_mono, rule Keys_mono, fact phull_subset_module)
  also have "... = component_of_term ` Keys B" by (fact components_pmdl)
  finally show "component_of_term ` Keys (phull B) \<subseteq> component_of_term ` Keys B" .
next
  show "component_of_term ` Keys B \<subseteq> component_of_term ` Keys (phull B)"
    by (rule image_mono, rule Keys_mono, fact phull.span_superset)
qed

end

subsection \<open>Interpretations\<close>

subsubsection \<open>Isomorphism between @{typ 'a} and @{typ "'a \<times> unit"}\<close>

definition to_pair_unit :: "'a \<Rightarrow> ('a \<times> unit)"
  where "to_pair_unit x = (x, ())"

lemma fst_to_pair_unit: "fst (to_pair_unit x) = x"
  by (simp add: to_pair_unit_def)

lemma to_pair_unit_fst: "to_pair_unit (fst x) = (x::_ \<times> unit)"
  by (metis (full_types) old.unit.exhaust prod.collapse to_pair_unit_def)

interpretation punit: term_powerprod to_pair_unit fst
  apply standard
  subgoal by (fact fst_to_pair_unit)
  subgoal by (fact to_pair_unit_fst)
  done

text \<open>For technical reasons it seems to be better not to put the following lemmas as rewrite-rules
  of interpretation \<open>punit\<close>.\<close>

lemma punit_pp_of_term [simp]: "punit.pp_of_term = (\<lambda>x. x)"
  by (rule, simp add: punit.pp_of_term_def punit.term_pair)

lemma punit_component_of_term [simp]: "punit.component_of_term = (\<lambda>_. ())"
  by (rule, simp add: punit.component_of_term_def)

lemma punit_splus [simp]: "punit.splus = (+)"
  by (rule, rule, simp add: punit.splus_def)

lemma punit_sminus [simp]: "punit.sminus = (-)"
  by (rule, rule, simp add: punit.sminus_def)

lemma punit_adds_pp [simp]: "punit.adds_pp = (adds)"
  by (rule, rule, simp add: punit.adds_pp_def)

lemma punit_adds_term [simp]: "punit.adds_term = (adds)"
  by (rule, rule, simp add: punit.adds_term_def)

lemma punit_proj_poly [simp]: "punit.proj_poly = (\<lambda>_. id)"
  by (rule, rule, rule poly_mapping_eqI, simp add: punit.lookup_proj_poly)

lemma punit_mult_vec [simp]: "punit.mult_vec = (*)"
  by (rule, rule, rule poly_mapping_eqI, simp add: punit.lookup_mult_vec)

lemma punit_mult_scalar [simp]: "punit.mult_scalar = (*)"
  by (rule, rule, rule poly_mapping_eqI, simp add: punit.lookup_mult_scalar)

context term_powerprod
begin

lemma proj_monom_mult: "proj_poly k (monom_mult c t p) = punit.monom_mult c t (proj_poly k p)"
  by (metis mult_scalar_monomial proj_mult_scalar punit.mult_scalar_monomial punit_mult_scalar)

lemma mult_scalar_monom_mult: "(punit.monom_mult c t p) \<odot> q = monom_mult c t (p \<odot> q)"
  by (simp add: punit.mult_scalar_monomial[symmetric] mult_scalar_assoc mult_scalar_monomial)

end (* term_powerprod *)

subsubsection \<open>Interpretation of @{locale term_powerprod} by @{typ "'a \<times> 'k"}\<close>

interpretation pprod: term_powerprod "(\<lambda>x::'a::comm_powerprod \<times> 'k::linorder. x)" "\<lambda>x. x"
  by (standard, simp)

lemma pprod_pp_of_term [simp]: "pprod.pp_of_term = fst"
  by (rule, simp add: pprod.pp_of_term_def)

lemma pprod_component_of_term [simp]: "pprod.component_of_term = snd"
  by (rule, simp add: pprod.component_of_term_def)

subsubsection \<open>Simplifier Setup\<close>

text \<open>There is no reason to keep the interpreted theorems as simplification rules.\<close>

lemmas [term_simps del] = term_simps

lemmas times_monomial_monomial = punit.mult_scalar_monomial_monomial[simplified]
lemmas times_monomial_left = punit.mult_scalar_monomial[simplified]
lemmas times_rec_left = punit.mult_scalar_rec_left[simplified]
lemmas times_rec_right = punit.mult_scalar_rec_right[simplified]
lemmas in_keys_timesE = punit.in_keys_mult_scalarE[simplified]
lemmas punit_monom_mult_monomial = punit.monom_mult_monomial[simplified]
lemmas lookup_times = punit.lookup_mult_scalar_explicit[simplified]
lemmas map_scale_eq_times = punit.map_scale_eq_mult_scalar[simplified]

end (* theory *)
