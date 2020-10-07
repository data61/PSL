(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Abstract Power-Products\<close>

theory Power_Products
  imports Complex_Main
  "HOL-Library.Function_Algebras"
  "HOL-Library.Countable"
  "More_MPoly_Type"
  "Utils"
  Well_Quasi_Orders.Well_Quasi_Orders
begin

text \<open>This theory formalizes the concept of "power-products". A power-product can be thought of as
  the product of some indeterminates, such as $x$, $x^2\,y$, $x\,y^3\,z^7$, etc., without any
  scalar coefficient.

The approach in this theory is to capture the notion of "power-product" (also called "monomial") as
type class. A canonical instance for power-product is the type @{typ "'var \<Rightarrow>\<^sub>0 nat"}, which is
interpreted as mapping from variables in the power-product to exponents.

A slightly unintuitive (but fitting better with the standard type class instantiations of
@{typ "'a \<Rightarrow>\<^sub>0 'b"}) approach is to write addition to denote "multiplication" of power products.
For example, $x^2y$ would be represented as a function \<open>p = (X \<mapsto> 2, Y \<mapsto> 1)\<close>, $xz$ as a
function \<open>q = (X \<mapsto> 1, Z \<mapsto> 1)\<close>. With the (pointwise) instantiation of addition of @{typ "'a \<Rightarrow>\<^sub>0 'b"},
we will write \<open>p + q = (X \<mapsto> 3, Y \<mapsto> 1, Z \<mapsto> 1)\<close> for the product $x^2y \cdot xz = x^3yz$
\<close>

subsection \<open>Constant @{term Keys}\<close>

text \<open>Legacy:\<close>
lemmas keys_eq_empty_iff = keys_eq_empty

definition Keys :: "('a \<Rightarrow>\<^sub>0 'b::zero) set \<Rightarrow> 'a set"
  where "Keys F = \<Union>(keys ` F)"

lemma in_Keys: "s \<in> Keys F \<longleftrightarrow> (\<exists>f\<in>F. s \<in> keys f)"
  unfolding Keys_def by simp

lemma in_KeysI:
  assumes "s \<in> keys f" and "f \<in> F"
  shows "s \<in> Keys F"
  unfolding in_Keys using assms ..

lemma in_KeysE:
  assumes "s \<in> Keys F"
  obtains f where "s \<in> keys f" and "f \<in> F"
  using assms unfolding in_Keys ..

lemma Keys_mono:
  assumes "A \<subseteq> B"
  shows "Keys A \<subseteq> Keys B"
  using assms by (auto simp add: Keys_def)

lemma Keys_insert: "Keys (insert a A) = keys a \<union> Keys A"
  by (simp add: Keys_def)

lemma Keys_Un: "Keys (A \<union> B) = Keys A \<union> Keys B"
  by (simp add: Keys_def)

lemma finite_Keys:
  assumes "finite A"
  shows "finite (Keys A)"
  unfolding Keys_def by (rule, fact assms, rule finite_keys)

lemma Keys_not_empty:
  assumes "a \<in> A" and "a \<noteq> 0"
  shows "Keys A \<noteq> {}"
proof
  assume "Keys A = {}"
  from \<open>a \<noteq> 0\<close> have "keys a \<noteq> {}" using aux by fastforce
  then obtain s where "s \<in> keys a" by blast
  from this assms(1) have "s \<in> Keys A" by (rule in_KeysI)
  with \<open>Keys A = {}\<close> show False by simp
qed

lemma Keys_empty [simp]: "Keys {} = {}"
  by (simp add: Keys_def)

lemma Keys_zero [simp]: "Keys {0} = {}"
  by (simp add: Keys_def)

lemma keys_subset_Keys:
  assumes "f \<in> F"
  shows "keys f \<subseteq> Keys F"
  using in_KeysI[OF _ assms] by auto

lemma Keys_minus: "Keys (A - B) \<subseteq> Keys A"
  by (auto simp add: Keys_def)

lemma Keys_minus_zero: "Keys (A - {0}) = Keys A"
proof (cases "0 \<in> A")
  case True
  hence "(A - {0}) \<union> {0} = A" by auto
  hence "Keys A = Keys ((A - {0}) \<union> {0})" by simp
  also have "... = Keys (A - {0}) \<union> Keys {0::('a \<Rightarrow>\<^sub>0 'b)}" by (fact Keys_Un)
  also have "... = Keys (A - {0})" by simp
  finally show ?thesis by simp
next
  case False
  hence "A - {0} = A" by simp
  thus ?thesis by simp
qed

subsection \<open>Constant @{term except}\<close>

definition except_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b::zero)"
  where "except_fun f S = (\<lambda>x. (f x when x \<notin> S))"

lift_definition except :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero)" is except_fun
proof -
  fix p::"'a \<Rightarrow> 'b" and S::"'a set"
  assume "finite {t. p t \<noteq> 0}"
  show "finite {t. except_fun p S t \<noteq> 0}"
  proof (rule finite_subset[of _ "{t. p t \<noteq> 0}"], rule)
    fix u
    assume "u \<in> {t. except_fun p S t \<noteq> 0}"
    hence "p u \<noteq> 0" by (simp add: except_fun_def)
    thus "u \<in> {t. p t \<noteq> 0}" by simp
  qed fact
qed

lemma lookup_except_when: "lookup (except p S) = (\<lambda>t. lookup p t when t \<notin> S)"
  by (auto simp: except.rep_eq except_fun_def)

lemma lookup_except: "lookup (except p S) = (\<lambda>t. if t \<in> S then 0 else lookup p t)"
  by (rule ext) (simp add: lookup_except_when)

lemma lookup_except_singleton: "lookup (except p {t}) t = 0"
  by (simp add: lookup_except)

lemma except_zero [simp]: "except 0 S = 0"
  by (rule poly_mapping_eqI) (simp add: lookup_except)

lemma lookup_except_eq_idI:
  assumes "t \<notin> S"
  shows "lookup (except p S) t = lookup p t"
  using assms by (simp add: lookup_except)

lemma lookup_except_eq_zeroI:
  assumes "t \<in> S"
  shows "lookup (except p S) t = 0"
  using assms by (simp add: lookup_except)

lemma except_empty [simp]: "except p {} = p"
  by (rule poly_mapping_eqI) (simp add: lookup_except)

lemma except_eq_zeroI:
  assumes "keys p \<subseteq> S"
  shows "except p S = 0"
proof (rule poly_mapping_eqI, simp)
  fix t
  show "lookup (except p S) t = 0"
  proof (cases "t \<in> S")
    case True
    thus ?thesis by (rule lookup_except_eq_zeroI)
  next
    case False then show ?thesis
      by (metis assms in_keys_iff lookup_except_eq_idI subset_eq) 
  qed
qed

lemma except_eq_zeroE:
  assumes "except p S = 0"
  shows "keys p \<subseteq> S"
  by (metis assms aux in_keys_iff lookup_except_eq_idI subset_iff)

lemma except_eq_zero_iff: "except p S = 0 \<longleftrightarrow> keys p \<subseteq> S"
  by (rule, elim except_eq_zeroE, elim except_eq_zeroI)

lemma except_keys [simp]: "except p (keys p) = 0"
  by (rule except_eq_zeroI, rule subset_refl)

lemma plus_except: "p = Poly_Mapping.single t (lookup p t) + except p {t}"
  by (rule poly_mapping_eqI, simp add: lookup_add lookup_single lookup_except when_def split: if_split)

lemma keys_except: "keys (except p S) = keys p - S"
  by (transfer, auto simp: except_fun_def)

lemma except_single: "except (Poly_Mapping.single u c) S = (Poly_Mapping.single u c when u \<notin> S)"
  by (rule poly_mapping_eqI) (simp add: lookup_except lookup_single when_def)

lemma except_plus: "except (p + q) S = except p S + except q S"
  by (rule poly_mapping_eqI) (simp add: lookup_except lookup_add)

lemma except_minus: "except (p - q) S = except p S - except q S"
  by (rule poly_mapping_eqI) (simp add: lookup_except lookup_minus)

lemma except_uminus: "except (- p) S = - except p S"
  by (rule poly_mapping_eqI) (simp add: lookup_except)

lemma except_except: "except (except p S) T = except p (S \<union> T)"
  by (rule poly_mapping_eqI) (simp add: lookup_except)

lemma poly_mapping_keys_eqI:
  assumes a1: "keys p = keys q" and a2: "\<And>t. t \<in> keys p \<Longrightarrow> lookup p t = lookup q t"
  shows "p = q"
proof (rule poly_mapping_eqI)
  fix t
  show "lookup p t = lookup q t"
  proof (cases "t \<in> keys p")
    case True
    thus ?thesis by (rule a2)
  next
    case False
    moreover from this have "t \<notin> keys q" unfolding a1 .
    ultimately have "lookup p t = 0" and "lookup q t = 0" unfolding in_keys_iff by simp_all
    thus ?thesis by simp
  qed
qed

lemma except_id_iff: "except p S = p \<longleftrightarrow> keys p \<inter> S = {}"
  by (metis Diff_Diff_Int Diff_eq_empty_iff Diff_triv inf_le2 keys_except lookup_except_eq_idI
      lookup_except_eq_zeroI not_in_keys_iff_lookup_eq_zero poly_mapping_keys_eqI)

lemma keys_subset_wf:
  "wfP (\<lambda>p q::('a, 'b::zero) poly_mapping. keys p \<subset> keys q)"
unfolding wfP_def
proof (intro wfI_min)
  fix x::"('a, 'b) poly_mapping" and Q
  assume x_in: "x \<in> Q"
  let ?Q0 = "card ` keys ` Q"
  from x_in have "card (keys x) \<in> ?Q0" by simp
  from wfE_min[OF wf this] obtain z0
    where z0_in: "z0 \<in> ?Q0" and z0_min: "\<And>y. (y, z0) \<in> {(x, y). x < y} \<Longrightarrow> y \<notin> ?Q0" by auto
  from z0_in obtain z where z0_def: "z0 = card (keys z)" and "z \<in> Q" by auto
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> {(p, q). keys p \<subset> keys q} \<longrightarrow> y \<notin> Q"
  proof (intro bexI[of _ z], rule, rule)
    fix y::"('a, 'b) poly_mapping"
    let ?y0 = "card (keys y)"
    assume "(y, z) \<in> {(p, q). keys p \<subset> keys q}"
    hence "keys y \<subset> keys z" by simp
    hence "?y0 < z0" unfolding z0_def by (simp add: psubset_card_mono) 
    hence "(?y0, z0) \<in> {(x, y). x < y}" by simp
    from z0_min[OF this] show "y \<notin> Q" by auto
  qed (fact)
qed

lemma poly_mapping_except_induct:
  assumes base: "P 0" and ind: "\<And>p t. p \<noteq> 0 \<Longrightarrow> t \<in> keys p \<Longrightarrow> P (except p {t}) \<Longrightarrow> P p"
  shows "P p"
proof (induct rule: wfP_induct[OF keys_subset_wf])
  fix p::"('a, 'b) poly_mapping"
  assume "\<forall>q. keys q \<subset> keys p \<longrightarrow> P q"
  hence IH: "\<And>q. keys q \<subset> keys p \<Longrightarrow> P q" by simp
  show "P p"
  proof (cases "p = 0")
    case True
    thus ?thesis using base by simp
  next
    case False
    hence "keys p \<noteq> {}" by simp
    then obtain t where "t \<in> keys p" by blast
    show ?thesis
    proof (rule ind, fact, fact, rule IH, simp only: keys_except, rule, rule Diff_subset, rule)
      assume "keys p - {t} = keys p"
      hence "t \<notin> keys p" by blast
      from this \<open>t \<in> keys p\<close> show False ..
    qed
  qed
qed

lemma poly_mapping_except_induct':
  assumes "\<And>p. (\<And>t. t \<in> keys p \<Longrightarrow> P (except p {t})) \<Longrightarrow> P p"
  shows "P p"
proof (induct "card (keys p)" arbitrary: p)
  case 0
  with finite_keys[of p] have "keys p = {}" by simp
  show ?case by (rule assms, simp add: \<open>keys p = {}\<close>)
next
  case step: (Suc n)
  show ?case
  proof (rule assms)
    fix t
    assume "t \<in> keys p"
    show "P (except p {t})"
    proof (rule step(1), simp add: keys_except)
      from step(2) \<open>t \<in> keys p\<close> finite_keys[of p] show "n = card (keys p - {t})" by simp
    qed
  qed
qed

lemma poly_mapping_plus_induct:
  assumes "P 0" and "\<And>p c t. c \<noteq> 0 \<Longrightarrow> t \<notin> keys p \<Longrightarrow> P p \<Longrightarrow> P (Poly_Mapping.single t c + p)"
  shows "P p"
proof (induct "card (keys p)" arbitrary: p)
  case 0
  with finite_keys[of p] have "keys p = {}" by simp
  hence "p = 0" by simp
  with assms(1) show ?case by simp
next
  case step: (Suc n)
  from step(2) obtain t where t: "t \<in> keys p" by (metis card_eq_SucD insert_iff)
  define c where "c = lookup p t"
  define q where "q = except p {t}"
  have *: "p = Poly_Mapping.single t c + q"
    by (rule poly_mapping_eqI, simp add: lookup_add lookup_single Poly_Mapping.when_def, intro conjI impI,
        simp add: q_def lookup_except c_def, simp add: q_def lookup_except_eq_idI)
  show ?case
  proof (simp only: *, rule assms(2))
    from t show "c \<noteq> 0"
      using c_def by auto
  next
    show "t \<notin> keys q" by (simp add: q_def keys_except)
  next
    show "P q"
    proof (rule step(1))
      from step(2) \<open>t \<in> keys p\<close> show "n = card (keys q)" unfolding q_def keys_except
        by (metis Suc_inject card.remove finite_keys)
    qed
  qed
qed

lemma except_Diff_singleton: "except p (keys p - {t}) = Poly_Mapping.single t (lookup p t)"
  by (rule poly_mapping_eqI) (simp add: lookup_single in_keys_iff lookup_except when_def)

lemma except_Un_plus_Int: "except p (U \<union> V) + except p (U \<inter> V) = except p U + except p V"
  by (rule poly_mapping_eqI) (simp add: lookup_except lookup_add)

corollary except_Int:
  assumes "keys p \<subseteq> U \<union> V"
  shows "except p (U \<inter> V) = except p U + except p V"
proof -
  from assms have "except p (U \<union> V) = 0" by (rule except_eq_zeroI)
  hence "except p (U \<inter> V) = except p (U \<union> V) + except p (U \<inter> V)" by simp
  also have "\<dots> = except p U + except p V" by (fact except_Un_plus_Int)
  finally show ?thesis .
qed

lemma except_keys_Int [simp]: "except p (keys p \<inter> U) = except p U"
  by (rule poly_mapping_eqI) (simp add: in_keys_iff lookup_except)

lemma except_Int_keys [simp]: "except p (U \<inter> keys p) = except p U"
  by (simp only: Int_commute[of U] except_keys_Int)

lemma except_keys_Diff: "except p (keys p - U) = except p (- U)"
proof -
  have "except p (keys p - U) = except p (keys p \<inter> (- U))" by (simp only: Diff_eq)
  also have "\<dots> = except p (- U)" by simp
  finally show ?thesis .
qed

lemma except_decomp: "p = except p U + except p (- U)"
  by (rule poly_mapping_eqI) (simp add: lookup_except lookup_add)

corollary except_Compl: "except p (- U) = p - except p U"
  by (metis add_diff_cancel_left' except_decomp)

subsection \<open>'Divisibility' on Additive Structures\<close>

context plus begin

definition adds :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "adds" 50)
  where "b adds a \<longleftrightarrow> (\<exists>k. a = b + k)"

lemma addsI [intro?]: "a = b + k \<Longrightarrow> b adds a"
  unfolding adds_def ..

lemma addsE [elim?]: "b adds a \<Longrightarrow> (\<And>k. a = b + k \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding adds_def by blast

end

context comm_monoid_add
begin

lemma adds_refl [simp]: "a adds a"
proof
  show "a = a + 0" by simp
qed

lemma adds_trans [trans]:
  assumes "a adds b" and "b adds c"
  shows "a adds c"
proof -
  from assms obtain v where "b = a + v"
    by (auto elim!: addsE)
  moreover from assms obtain w where "c = b + w"
    by (auto elim!: addsE)
  ultimately have "c = a + (v + w)"
    by (simp add: add.assoc)
  then show ?thesis ..
qed

lemma subset_divisors_adds: "{c. c adds a} \<subseteq> {c. c adds b} \<longleftrightarrow> a adds b"
  by (auto simp add: subset_iff intro: adds_trans)

lemma strict_subset_divisors_adds: "{c. c adds a} \<subset> {c. c adds b} \<longleftrightarrow> a adds b \<and> \<not> b adds a"
  by (auto simp add: subset_iff intro: adds_trans)

lemma zero_adds [simp]: "0 adds a"
  by (auto intro!: addsI)

lemma adds_plus_right [simp]: "a adds c \<Longrightarrow> a adds (b + c)"
  by (auto intro!: add.left_commute addsI elim!: addsE)

lemma adds_plus_left [simp]: "a adds b \<Longrightarrow> a adds (b + c)"
  using adds_plus_right [of a b c] by (simp add: ac_simps)

lemma adds_triv_right [simp]: "a adds b + a"
  by (rule adds_plus_right) (rule adds_refl)

lemma adds_triv_left [simp]: "a adds a + b"
  by (rule adds_plus_left) (rule adds_refl)

lemma plus_adds_mono:
  assumes "a adds b"
    and "c adds d"
  shows "a + c adds b + d"
proof -
  from \<open>a adds b\<close> obtain b' where "b = a + b'" ..
  moreover from \<open>c adds d\<close> obtain d' where "d = c + d'" ..
  ultimately have "b + d = (a + c) + (b' + d')"
    by (simp add: ac_simps)
  then show ?thesis ..
qed

lemma plus_adds_left: "a + b adds c \<Longrightarrow> a adds c"
  by (simp add: adds_def add.assoc) blast

lemma plus_adds_right: "a + b adds c \<Longrightarrow> b adds c"
  using plus_adds_left [of b a c] by (simp add: ac_simps)

end

class ninv_comm_monoid_add = comm_monoid_add +
  assumes plus_eq_zero: "s + t = 0 \<Longrightarrow> s = 0"
begin

lemma plus_eq_zero_2: "t = 0" if "s + t = 0"
  using that
  by (simp only: add_commute[of s t] plus_eq_zero)

lemma adds_zero: "s adds 0 \<longleftrightarrow> (s = 0)"
proof
  assume "s adds 0"
  from this obtain k where "0 = s + k" unfolding adds_def ..
  from this plus_eq_zero[of s k] show "s = 0"
    by blast
next
  assume "s = 0"
  thus "s adds 0" by simp
qed

end

context canonically_ordered_monoid_add
begin
subclass ninv_comm_monoid_add by (standard, simp)
end

class comm_powerprod = cancel_comm_monoid_add
begin

lemma adds_canc: "s + u adds t + u \<longleftrightarrow> s adds t" for s t u::'a
  unfolding adds_def
  apply auto
   apply (metis local.add.left_commute local.add_diff_cancel_left' local.add_diff_cancel_right')
  using add_assoc add_commute by auto

lemma adds_canc_2: "u + s adds u + t \<longleftrightarrow> s adds t"
  by (simp add: adds_canc ac_simps)

lemma add_minus_2: "(s + t) - s = t"
  by simp

lemma adds_minus:
  assumes "s adds t"
  shows "(t - s) + s = t"
proof -
  from assms adds_def[of s t] obtain u where u: "t = u + s" by (auto simp: ac_simps)
  then have "t - s = u"
    by simp
  thus ?thesis using u by simp
qed

lemma plus_adds_0:
  assumes "(s + t) adds u"
  shows "s adds (u - t)"
proof -
  from assms have "(s + t) adds ((u - t) + t)" using adds_minus local.plus_adds_right by presburger
  thus ?thesis using adds_canc[of s t "u - t"] by simp
qed

lemma plus_adds_2:
  assumes "t adds u" and "s adds (u - t)"
  shows "(s + t) adds u"
  by (metis adds_canc adds_minus assms)

lemma plus_adds:
  shows "(s + t) adds u \<longleftrightarrow> (t adds u \<and> s adds (u - t))"
proof
  assume a1: "(s + t) adds u"
  show "t adds u \<and> s adds (u - t)"
  proof
    from plus_adds_right[OF a1] show "t adds u" .
  next
    from plus_adds_0[OF a1] show "s adds (u - t)" .
  qed
next
  assume "t adds u \<and> s adds (u - t)"
  hence "t adds u" and "s adds (u - t)" by auto
  from plus_adds_2[OF \<open>t adds u\<close> \<open>s adds (u - t)\<close>] show "(s + t) adds u" .
qed

lemma minus_plus:
  assumes "s adds t"
  shows "(t - s) + u = (t + u) - s"
proof -
  from assms obtain k where k: "t = s + k" unfolding adds_def ..
  hence "t - s = k" by simp
  also from k have "(t + u) - s = k + u"
    by (simp add: add_assoc)
  finally show ?thesis by simp
qed

lemma minus_plus_minus:
  assumes "s adds t" and "u adds v"
  shows "(t - s) + (v - u) = (t + v) - (s + u)"
  using add_commute assms(1) assms(2) diff_diff_add minus_plus by auto

lemma minus_plus_minus_cancel:
  assumes "u adds t" and "s adds u"
  shows "(t - u) + (u - s) = t - s"
  by (metis assms(1) assms(2) local.add_diff_cancel_left' local.add_diff_cancel_right local.addsE minus_plus)

end

text \<open>Instances of class \<open>lcs_powerprod\<close> are types of commutative power-products admitting
  (not necessarily unique) least common sums (inspired from least common multiplies).
  Note that if the components of indeterminates are arbitrary integers (as for instance in Laurent
  polynomials), then no unique lcss exist.\<close>
class lcs_powerprod = comm_powerprod +
  fixes lcs::"'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes adds_lcs: "s adds (lcs s t)"
  assumes lcs_adds: "s adds u \<Longrightarrow> t adds u \<Longrightarrow> (lcs s t) adds u"
  assumes lcs_comm: "lcs s t = lcs t s"
begin

lemma adds_lcs_2: "t adds (lcs s t)"
  by (simp only: lcs_comm[of s t], rule adds_lcs)

lemma lcs_adds_plus: "lcs s t adds s + t" by (simp add: lcs_adds)

text \<open>"gcs" stands for "greatest common summand".\<close>
definition gcs :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where "gcs s t = (s + t) - (lcs s t)"

lemma gcs_plus_lcs: "(gcs s t) + (lcs s t) = s + t"
  unfolding gcs_def by (rule adds_minus, fact lcs_adds_plus)

lemma gcs_adds: "(gcs s t) adds s"
proof -
  have "t adds (lcs s t)" (is "t adds ?l") unfolding lcs_comm[of s t] by (fact adds_lcs)
  then obtain u where eq1: "?l = t + u" unfolding adds_def ..
  from lcs_adds_plus[of s t] obtain v where eq2: "s + t = ?l + v" unfolding adds_def ..
  hence "t + s = t + (u + v)" unfolding eq1 by (simp add: ac_simps)
  hence s: "s = u + v" unfolding add_left_cancel .
  show ?thesis unfolding eq2 gcs_def unfolding s by simp
qed

lemma gcs_comm: "gcs s t = gcs t s" unfolding gcs_def by (simp add: lcs_comm ac_simps)

lemma gcs_adds_2: "(gcs s t) adds t"
  by (simp only: gcs_comm[of s t], rule gcs_adds)

end

class ulcs_powerprod = lcs_powerprod + ninv_comm_monoid_add
begin

lemma adds_antisym:
  assumes "s adds t" "t adds s"
  shows "s = t"
proof -
  from \<open>s adds t\<close> obtain u where u_def: "t = s + u" unfolding adds_def ..
  from \<open>t adds s\<close> obtain v where v_def: "s = t + v" unfolding adds_def ..
  from u_def v_def have "s = (s + u) + v" by (simp add: ac_simps)
  hence "s + 0 = s + (u + v)" by (simp add: ac_simps)
  hence "u + v = 0" by simp
  hence "u = 0" using plus_eq_zero[of u v] by simp
  thus ?thesis using u_def by simp
qed

lemma lcs_unique:
  assumes "s adds l" and "t adds l" and *: "\<And>u. s adds u \<Longrightarrow> t adds u \<Longrightarrow> l adds u"
  shows "l = lcs s t"
  by (rule adds_antisym, rule *, fact adds_lcs, fact adds_lcs_2, rule lcs_adds, fact+)

lemma lcs_zero: "lcs 0 t = t"
  by (rule lcs_unique[symmetric], fact zero_adds, fact adds_refl)

lemma lcs_plus_left: "lcs (u + s) (u + t) = u + lcs s t" 
proof (rule lcs_unique[symmetric], simp_all only: adds_canc_2, fact adds_lcs, fact adds_lcs_2,
    simp add: add.commute[of u] plus_adds)
  fix v
  assume "u adds v \<and> s adds v - u"
  hence "s adds v - u" ..
  assume "t adds v - u"
  with \<open>s adds v - u\<close> show "lcs s t adds v - u" by (rule lcs_adds)
qed

lemma lcs_plus_right: "lcs (s + u) (t + u) = (lcs s t) + u"
  using lcs_plus_left[of u s t] by (simp add: ac_simps)

lemma adds_gcs:
  assumes "u adds s" and "u adds t"
  shows "u adds (gcs s t)"
proof -
  from assms have "s + u adds s + t" and "t + u adds t + s"
    by (simp_all add: plus_adds_mono)
  hence "lcs (s + u) (t + u) adds s + t"
    by (auto intro: lcs_adds simp add: ac_simps)
  hence "u + (lcs s t) adds s + t" unfolding lcs_plus_right by (simp add: ac_simps)
  hence "u adds (s + t) - (lcs s t)" unfolding plus_adds ..
  thus ?thesis unfolding gcs_def .
qed

lemma gcs_unique:
  assumes "g adds s" and "g adds t" and *: "\<And>u. u adds s \<Longrightarrow> u adds t \<Longrightarrow> u adds g"
  shows "g = gcs s t"
  by (rule adds_antisym, rule adds_gcs, fact, fact, rule *, fact gcs_adds, fact gcs_adds_2)

lemma gcs_plus_left: "gcs (u + s) (u + t) = u + gcs s t"
proof -
  have "u + s + (u + t) - (u + lcs s t) = u + s + (u + t) - u - lcs s t" by (simp only: diff_diff_add)
  also have "... = u + s + t + (u - u) - lcs s t" by (simp add: add.left_commute)
  also have "... = u + s + t - lcs s t" by simp
  also have "... =  u + (s + t - lcs s t)"
    using add_assoc add_commute local.lcs_adds_plus local.minus_plus by auto
  finally show ?thesis unfolding gcs_def lcs_plus_left .
qed

lemma gcs_plus_right: "gcs (s + u) (t + u) = (gcs s t) + u"
  using gcs_plus_left[of u s t] by (simp add: ac_simps)

lemma lcs_same [simp]: "lcs s s = s"
proof -
  have "lcs s s adds s" by (rule lcs_adds, simp_all)
  moreover have "s adds lcs s s" by (rule adds_lcs)
  ultimately show ?thesis by (rule adds_antisym)
qed

lemma gcs_same [simp]: "gcs s s = s"
proof -
  have "gcs s s adds s" by (rule gcs_adds)
  moreover have "s adds gcs s s" by (rule adds_gcs, simp_all)
  ultimately show ?thesis by (rule adds_antisym)
qed

end

subsection \<open>Dickson Classes\<close>

definition (in plus) dickson_grading :: "('a \<Rightarrow> nat) \<Rightarrow> bool"
  where "dickson_grading d \<longleftrightarrow>
          ((\<forall>s t. d (s + t) = max (d s) (d t)) \<and> (\<forall>n::nat. almost_full_on (adds) {x. d x \<le> n}))"

definition dgrad_set :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'a set"
  where "dgrad_set d m = {t. d t \<le> m}"

definition dgrad_set_le :: "('a \<Rightarrow> nat) \<Rightarrow> ('a set) \<Rightarrow> ('a set) \<Rightarrow> bool"
  where "dgrad_set_le d S T \<longleftrightarrow> (\<forall>s\<in>S. \<exists>t\<in>T. d s \<le> d t)"

lemma dickson_gradingI:
  assumes "\<And>s t. d (s + t) = max (d s) (d t)"
  assumes "\<And>n::nat. almost_full_on (adds) {x. d x \<le> n}"
  shows "dickson_grading d"
  unfolding dickson_grading_def using assms by blast

lemma dickson_gradingD1: "dickson_grading d \<Longrightarrow> d (s + t) = max (d s) (d t)"
  by (auto simp add: dickson_grading_def)

lemma dickson_gradingD2: "dickson_grading d \<Longrightarrow> almost_full_on (adds) {x. d x \<le> n}"
  by (auto simp add: dickson_grading_def)

lemma dickson_gradingD2':
  assumes "dickson_grading (d::'a::comm_monoid_add \<Rightarrow> nat)"
  shows "wqo_on (adds) {x. d x \<le> n}"
proof (intro wqo_onI transp_onI)
  fix x y z :: 'a
  assume "x adds y" and "y adds z"
  thus "x adds z" by (rule adds_trans)
next
  from assms show "almost_full_on (adds) {x. d x \<le> n}" by (rule dickson_gradingD2)
qed

lemma dickson_gradingE:
  assumes "dickson_grading d" and "\<And>i::nat. d ((seq::nat \<Rightarrow> 'a::plus) i) \<le> n"
  obtains i j where "i < j" and "seq i adds seq j"
proof -
  from assms(1) have "almost_full_on (adds) {x. d x \<le> n}" by (rule dickson_gradingD2)
  moreover from assms(2) have "\<And>i. seq i \<in> {x. d x \<le> n}" by simp
  ultimately obtain i j where "i < j" and "seq i adds seq j" by (rule almost_full_onD)
  thus ?thesis ..
qed

lemma dickson_grading_adds_imp_le:
  assumes "dickson_grading d" and "s adds t"
  shows "d s \<le> d t"
proof -
  from assms(2) obtain u where "t = s + u" ..
  hence "d t = max (d s) (d u)" by (simp only: dickson_gradingD1[OF assms(1)])
  thus ?thesis by simp
qed

lemma dickson_grading_minus:
  assumes "dickson_grading d" and "s adds (t::'a::cancel_ab_semigroup_add)"
  shows "d (t - s) \<le> d t"
proof -
  from assms(2) obtain u where "t = s + u" ..
  hence "t - s = u" by simp
  from assms(1) have "d t = ord_class.max (d s) (d u)" unfolding \<open>t = s + u\<close> by (rule dickson_gradingD1)
  thus ?thesis by (simp add: \<open>t - s = u\<close>)
qed

lemma dickson_grading_lcs:
  assumes "dickson_grading d"
  shows "d (lcs s t) \<le> max (d s) (d t)"
proof -
  from assms have "d (lcs s t) \<le> d (s + t)" by (rule dickson_grading_adds_imp_le, intro lcs_adds_plus)
  thus ?thesis by (simp only: dickson_gradingD1[OF assms])
qed

lemma dickson_grading_lcs_minus:
  assumes "dickson_grading d"
  shows "d (lcs s t - s) \<le> max (d s) (d t)"
proof -
  from assms have "d (lcs s t - s) \<le> d (lcs s t)" by (rule dickson_grading_minus, intro adds_lcs)
  also from assms have "... \<le> max (d s) (d t)" by (rule dickson_grading_lcs)
  finally show ?thesis .
qed

lemma dgrad_set_leI:
  assumes "\<And>s. s \<in> S \<Longrightarrow> \<exists>t\<in>T. d s \<le> d t"
  shows "dgrad_set_le d S T"
  using assms by (auto simp: dgrad_set_le_def)

lemma dgrad_set_leE:
  assumes "dgrad_set_le d S T" and "s \<in> S"
  obtains t where "t \<in> T" and "d s \<le> d t"
  using assms by (auto simp: dgrad_set_le_def)

lemma dgrad_set_exhaust_expl:
  assumes "finite F"
  shows "F \<subseteq> dgrad_set d (Max (d ` F))"
proof
  fix f
  assume "f \<in> F"
  hence "d f \<in> d ` F" by simp
  with _ have "d f \<le> Max (d ` F)"
  proof (rule Max_ge)
    from assms show "finite (d ` F)" by auto
  qed
  hence "dgrad_set d (d f) \<subseteq> dgrad_set d (Max (d ` F))" by (auto simp: dgrad_set_def)
  moreover have "f \<in> dgrad_set d (d f)" by (simp add: dgrad_set_def)
  ultimately show "f \<in> dgrad_set d (Max (d ` F))" ..
qed

lemma dgrad_set_exhaust:
  assumes "finite F"
  obtains m where "F \<subseteq> dgrad_set d m"
proof
  from assms show "F \<subseteq> dgrad_set d (Max (d ` F))" by (rule dgrad_set_exhaust_expl)
qed

lemma dgrad_set_le_trans [trans]:
  assumes "dgrad_set_le d S T" and "dgrad_set_le d T U"
  shows "dgrad_set_le d S U"
  unfolding dgrad_set_le_def
proof
  fix s
  assume "s \<in> S"
  with assms(1) obtain t where "t \<in> T" and 1: "d s \<le> d t" by (auto simp add: dgrad_set_le_def)
  from assms(2) this(1) obtain u where "u \<in> U" and 2: "d t \<le> d u" by (auto simp add: dgrad_set_le_def)
  from this(1) show "\<exists>u\<in>U. d s \<le> d u"
  proof
    from 1 2 show "d s \<le> d u" by (rule le_trans)
  qed
qed

lemma dgrad_set_le_Un: "dgrad_set_le d (S \<union> T) U \<longleftrightarrow> (dgrad_set_le d S U \<and> dgrad_set_le d T U)"
  by (auto simp add: dgrad_set_le_def)

lemma dgrad_set_le_subset:
  assumes "S \<subseteq> T"
  shows "dgrad_set_le d S T"
  unfolding dgrad_set_le_def using assms by blast

lemma dgrad_set_le_refl: "dgrad_set_le d S S"
  by (rule dgrad_set_le_subset, fact subset_refl)

lemma dgrad_set_le_dgrad_set:
  assumes "dgrad_set_le d F G" and "G \<subseteq> dgrad_set d m"
  shows "F \<subseteq> dgrad_set d m"
proof
  fix f
  assume "f \<in> F"
  with assms(1) obtain g where "g \<in> G" and *: "d f \<le> d g" by (auto simp add: dgrad_set_le_def)
  from assms(2) this(1) have "g \<in> dgrad_set d m" ..
  hence "d g \<le> m" by (simp add: dgrad_set_def)
  with * have "d f \<le> m" by (rule le_trans)
  thus "f \<in> dgrad_set d m" by (simp add: dgrad_set_def)
qed

lemma dgrad_set_dgrad: "p \<in> dgrad_set d (d p)"
  by (simp add: dgrad_set_def)

lemma dgrad_setI [intro]:
  assumes "d t \<le> m"
  shows "t \<in> dgrad_set d m"
  using assms by (auto simp: dgrad_set_def)

lemma dgrad_setD:
  assumes "t \<in> dgrad_set d m"
  shows "d t \<le> m"
  using assms by (simp add: dgrad_set_def)

lemma dgrad_set_zero [simp]: "dgrad_set (\<lambda>_. 0) m = UNIV"
  by auto

lemma subset_dgrad_set_zero: "F \<subseteq> dgrad_set (\<lambda>_. 0) m"
  by simp

lemma dgrad_set_subset:
  assumes "m \<le> n"
  shows "dgrad_set d m \<subseteq> dgrad_set d n"
  using assms by (auto simp: dgrad_set_def)

lemma dgrad_set_closed_plus:
  assumes "dickson_grading d" and "s \<in> dgrad_set d m" and "t \<in> dgrad_set d m"
  shows "s + t \<in> dgrad_set d m"
proof -
  from assms(1) have "d (s + t) = ord_class.max (d s) (d t)" by (rule dickson_gradingD1)
  also from assms(2, 3) have "... \<le> m" by (simp add: dgrad_set_def)
  finally show ?thesis by (simp add: dgrad_set_def)
qed

lemma dgrad_set_closed_minus:
  assumes "dickson_grading d" and "s \<in> dgrad_set d m" and "t adds (s::'a::cancel_ab_semigroup_add)"
  shows "s - t \<in> dgrad_set d m"
proof -
  from assms(1, 3) have "d (s - t) \<le> d s" by (rule dickson_grading_minus)
  also from assms(2) have "... \<le> m" by (simp add: dgrad_set_def)
  finally show ?thesis by (simp add: dgrad_set_def)
qed

lemma dgrad_set_closed_lcs:
  assumes "dickson_grading d" and "s \<in> dgrad_set d m" and "t \<in> dgrad_set d m"
  shows "lcs s t \<in> dgrad_set d m"
proof -
  from assms(1) have "d (lcs s t) \<le> ord_class.max (d s) (d t)" by (rule dickson_grading_lcs)
  also from assms(2, 3) have "... \<le> m" by (simp add: dgrad_set_def)
  finally show ?thesis by (simp add: dgrad_set_def)
qed

lemma dickson_gradingD_dgrad_set: "dickson_grading d \<Longrightarrow> almost_full_on (adds) (dgrad_set d m)"
  by (auto dest: dickson_gradingD2 simp: dgrad_set_def)

lemma ex_finite_adds:
  assumes "dickson_grading d" and "S \<subseteq> dgrad_set d m"
  obtains T where "finite T" and "T \<subseteq> S" and "\<And>s. s \<in> S \<Longrightarrow> (\<exists>t\<in>T. t adds (s::'a::cancel_comm_monoid_add))"
proof -
  have "reflp ((adds)::'a \<Rightarrow> _)" by (simp add: reflp_def)
  moreover from assms(2) have "almost_full_on (adds) S"
  proof (rule almost_full_on_subset)
    from assms(1) show "almost_full_on (adds) (dgrad_set d m)" by (rule dickson_gradingD_dgrad_set)
  qed
  ultimately obtain T where "finite T" and "T \<subseteq> S" and "\<And>s. s \<in> S \<Longrightarrow> (\<exists>t\<in>T. t adds s)"
    by (rule almost_full_on_finite_subsetE, blast)
  thus ?thesis ..
qed

class graded_dickson_powerprod = ulcs_powerprod +
  assumes ex_dgrad: "\<exists>d::'a \<Rightarrow> nat. dickson_grading d"
begin

definition dgrad_dummy where "dgrad_dummy = (SOME d. dickson_grading d)"

lemma dickson_grading_dgrad_dummy: "dickson_grading dgrad_dummy"
  unfolding dgrad_dummy_def using ex_dgrad by (rule someI_ex)

end (* graded_dickson_powerprod *)

class dickson_powerprod = ulcs_powerprod +
  assumes dickson: "almost_full_on (adds) UNIV"
begin

lemma dickson_grading_zero: "dickson_grading (\<lambda>_::'a. 0)"
  by (simp add: dickson_grading_def dickson)

subclass graded_dickson_powerprod by (standard, rule, fact dickson_grading_zero)

end (* dickson_powerprod *)

text \<open>Class @{class graded_dickson_powerprod} is a slightly artificial construction. It is needed,
  because type @{typ "nat \<Rightarrow>\<^sub>0 nat"} does not satisfy the usual conditions of a "Dickson domain" (as
  formulated in class @{class dickson_powerprod}), but we still want to use that type as the type of
  power-products in the computation of Gr\"obner bases. So, we exploit the fact that in a finite
  set of polynomials (which is the input of Buchberger's algorithm) there is always some "highest"
  indeterminate that occurs with non-zero exponent, and no "higher" indeterminates are generated
  during the execution of the algorithm. This allows us to prove that the algorithm terminates, even
  though there are in principle infinitely many indeterminates.\<close>

subsection \<open>Additive Linear Orderings\<close>
  
lemma group_eq_aux: "a + (b - a) = (b::'a::ab_group_add)"
proof -
  have "a + (b - a) = b - a + a" by simp
  also have "... = b" by simp
  finally show ?thesis .
qed

class semi_canonically_ordered_monoid_add = ordered_comm_monoid_add +
  assumes le_imp_add: "a \<le> b \<Longrightarrow> (\<exists>c. b = a + c)"

context canonically_ordered_monoid_add
begin
subclass semi_canonically_ordered_monoid_add
  by (standard, simp only: le_iff_add)
end

class add_linorder_group = ordered_ab_semigroup_add_imp_le + ab_group_add + linorder

class add_linorder = ordered_ab_semigroup_add_imp_le + cancel_comm_monoid_add + semi_canonically_ordered_monoid_add + linorder
begin

subclass ordered_comm_monoid_add ..

subclass ordered_cancel_comm_monoid_add ..

lemma le_imp_inv:
  assumes "a \<le> b"
  shows "b = a + (b - a)"
  using le_imp_add[OF assms] by auto

lemma max_eq_sum:
  obtains y where "max a b = a + y"
  unfolding max_def
proof (cases "a \<le> b")
  case True
  hence "b = a + (b - a)" by (rule le_imp_inv)
  then obtain c where eq: "b = a + c" ..
  show ?thesis
  proof
    from True show "max a b = a + c" unfolding max_def eq by simp
  qed
next
  case False
  show ?thesis
  proof
    from False show "max a b = a + 0" unfolding max_def by simp
  qed
qed
  
lemma min_plus_max:
  shows "(min a b) + (max a b) = a + b"
proof (cases "a \<le> b")
  case True
  thus ?thesis unfolding min_def max_def by simp
next
  case False
  thus ?thesis unfolding min_def max_def by (simp add: ac_simps)
qed

end (* add_linorder *)

class add_linorder_min = add_linorder +
  assumes zero_min: "0 \<le> x"
begin

subclass ninv_comm_monoid_add
proof
  fix x y
  assume *: "x + y = 0"
  show "x = 0"
  proof -
    from zero_min[of x] have "0 = x \<or> x > 0" by auto
    thus ?thesis
    proof
      assume "x > 0"
      have "0 \<le> y" by (fact zero_min)
      also have "... = 0 + y" by simp
      also from \<open>x > 0\<close> have "... < x + y" by (rule add_strict_right_mono)
      finally have "0 < x + y" .
      hence "x + y \<noteq> 0" by simp
      from this * show ?thesis ..
    qed simp
  qed
qed
  
lemma leq_add_right:
  shows "x \<le> x + y"
  using add_left_mono[OF zero_min[of y], of x] by simp

lemma leq_add_left:
  shows "x \<le> y + x"
  using add_right_mono[OF zero_min[of y], of x] by simp

subclass canonically_ordered_monoid_add
  by (standard, rule, elim le_imp_add, elim exE, simp add: leq_add_right)

end (* add_linorder_min *)
  
class add_wellorder = add_linorder_min + wellorder
  
instantiation nat :: add_linorder
begin

instance by (standard, simp)

end (* add_linorder *)
  
instantiation nat :: add_linorder_min
begin
instance by (standard, simp)
end
  
instantiation nat :: add_wellorder
begin
instance ..
end
  
context add_linorder_group
begin
  
subclass add_linorder
proof (standard, intro exI)
  fix a b
  show "b = a + (b - a)" using add_commute local.diff_add_cancel by auto
qed

end (* add_linorder_group *)
  
instantiation int :: add_linorder_group
begin
instance ..
end

instantiation rat :: add_linorder_group
begin
instance ..
end

instantiation real :: add_linorder_group
begin
instance ..
end

subsection \<open>Ordered Power-Products\<close>

locale ordered_powerprod =
  ordered_powerprod_lin: linorder ord ord_strict
  for ord::"'a \<Rightarrow> 'a::comm_powerprod \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict::"'a \<Rightarrow> 'a::comm_powerprod \<Rightarrow> bool" (infixl "\<prec>" 50) +
  assumes zero_min: "0 \<preceq> t"
  assumes plus_monotone: "s \<preceq> t \<Longrightarrow> s + u \<preceq> t + u"
begin

abbreviation ord_conv (infixl "\<succeq>" 50) where "ord_conv \<equiv> (\<preceq>)\<inverse>\<inverse>"
abbreviation ord_strict_conv (infixl "\<succ>" 50) where "ord_strict_conv \<equiv> (\<prec>)\<inverse>\<inverse>"

lemma ord_canc:
  assumes "s + u \<preceq> t + u"
  shows "s \<preceq> t"
proof (rule ordered_powerprod_lin.le_cases[of s t], simp)
  assume "t \<preceq> s"
  from assms plus_monotone[OF this, of u] have "t + u = s + u"
    using ordered_powerprod_lin.eq_iff by simp
  hence "t = s" by simp
  thus "s \<preceq> t" by simp
qed

lemma ord_adds:
  assumes "s adds t"
  shows "s \<preceq> t"
proof -
  from assms have "\<exists>u. t = s + u" unfolding adds_def by simp
  then obtain k where "t = s + k" ..
  thus ?thesis using plus_monotone[OF zero_min[of k], of s] by (simp add: ac_simps)
qed

lemma ord_canc_left:
  assumes "u + s \<preceq> u + t"
  shows "s \<preceq> t"
  using assms unfolding add.commute[of u] by (rule ord_canc)

lemma ord_strict_canc:
  assumes "s + u \<prec> t + u"
  shows "s \<prec> t"
  using assms ord_canc[of s u t] add_right_cancel[of s u t]
    ordered_powerprod_lin.le_imp_less_or_eq ordered_powerprod_lin.order.strict_implies_order by blast

lemma ord_strict_canc_left:
  assumes "u + s \<prec> u + t"
  shows "s \<prec> t"
  using assms unfolding add.commute[of u] by (rule ord_strict_canc)

lemma plus_monotone_left:
  assumes "s \<preceq> t"
  shows "u + s \<preceq> u + t"
  using assms
  by (simp add: add.commute, rule plus_monotone)

lemma plus_monotone_strict:
  assumes "s \<prec> t"
  shows "s + u \<prec> t + u"
  using assms
  by (simp add: ordered_powerprod_lin.order.strict_iff_order plus_monotone)

lemma plus_monotone_strict_left:
  assumes "s \<prec> t"
  shows "u + s \<prec> u + t"
  using assms
  by (simp add: ordered_powerprod_lin.order.strict_iff_order plus_monotone_left)

end

locale gd_powerprod =
  ordered_powerprod ord ord_strict
  for ord::"'a \<Rightarrow> 'a::graded_dickson_powerprod \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50)
begin

definition dickson_le :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "dickson_le d m s t \<longleftrightarrow> (d s \<le> m \<and> d t \<le> m \<and> s \<preceq> t)"

definition dickson_less :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "dickson_less d m s t \<longleftrightarrow> (d s \<le> m \<and> d t \<le> m \<and> s \<prec> t)"

lemma dickson_leI:
  assumes "d s \<le> m" and "d t \<le> m" and "s \<preceq> t"
  shows "dickson_le d m s t"
  using assms by (simp add: dickson_le_def)

lemma dickson_leD1:
  assumes "dickson_le d m s t"
  shows "d s \<le> m"
  using assms by (simp add: dickson_le_def)

lemma dickson_leD2:
  assumes "dickson_le d m s t"
  shows "d t \<le> m"
  using assms by (simp add: dickson_le_def)

lemma dickson_leD3:
  assumes "dickson_le d m s t"
  shows "s \<preceq> t"
  using assms by (simp add: dickson_le_def)

lemma dickson_le_trans:
  assumes "dickson_le d m s t" and "dickson_le d m t u"
  shows "dickson_le d m s u"
  using assms by (auto simp add: dickson_le_def)

lemma dickson_lessI:
  assumes "d s \<le> m" and "d t \<le> m" and "s \<prec> t"
  shows "dickson_less d m s t"
  using assms by (simp add: dickson_less_def)

lemma dickson_lessD1:
  assumes "dickson_less d m s t"
  shows "d s \<le> m"
  using assms by (simp add: dickson_less_def)

lemma dickson_lessD2:
  assumes "dickson_less d m s t"
  shows "d t \<le> m"
  using assms by (simp add: dickson_less_def)

lemma dickson_lessD3:
  assumes "dickson_less d m s t"
  shows "s \<prec> t"
  using assms by (simp add: dickson_less_def)

lemma dickson_less_irrefl: "\<not> dickson_less d m t t"
  by (simp add: dickson_less_def)

lemma dickson_less_trans:
  assumes "dickson_less d m s t" and "dickson_less d m t u"
  shows "dickson_less d m s u"
  using assms by (auto simp add: dickson_less_def)

lemma transp_dickson_less: "transp (dickson_less d m)"
  by (rule transpI, fact dickson_less_trans)

lemma wfp_on_ord_strict:
  assumes "dickson_grading d"
  shows "wfp_on (\<prec>) {x. d x \<le> n}"
proof -
  let ?A = "{x. d x \<le> n}"
  have "strict (\<preceq>) = (\<prec>)" by (intro ext, simp only: ordered_powerprod_lin.less_le_not_le)
  have "qo_on (adds) ?A" by (auto simp: qo_on_def reflp_on_def transp_on_def dest: adds_trans)
  moreover from assms have "wqo_on (adds) ?A" by (rule dickson_gradingD2')
  ultimately have "(\<forall>Q. (\<forall>x\<in>?A. \<forall>y\<in>?A. x adds y \<longrightarrow> Q x y) \<and> qo_on Q ?A \<longrightarrow> wfp_on (strict Q) ?A)"
    by (simp only: wqo_extensions_wf_conv)
  hence "(\<forall>x\<in>?A. \<forall>y\<in>?A. x adds y \<longrightarrow> x \<preceq> y) \<and> qo_on (\<preceq>) ?A \<longrightarrow> wfp_on (strict (\<preceq>)) ?A" ..
  thus ?thesis unfolding \<open>strict (\<preceq>) = (\<prec>)\<close>
  proof
    show "(\<forall>x\<in>?A. \<forall>y\<in>?A. x adds y \<longrightarrow> x \<preceq> y) \<and> qo_on (\<preceq>) ?A"
    proof (intro conjI ballI impI ord_adds)
      show "qo_on (\<preceq>) ?A" by (auto simp: qo_on_def reflp_on_def transp_on_def)
    qed
  qed
qed

lemma wf_dickson_less:
  assumes "dickson_grading d"
  shows "wfP (dickson_less d m)"
proof (rule wfP_chain)
  show "\<not> (\<exists>seq. \<forall>i. dickson_less d m (seq (Suc i)) (seq i))"
  proof
    assume "\<exists>seq. \<forall>i. dickson_less d m (seq (Suc i)) (seq i)"
    then obtain seq::"nat \<Rightarrow> 'a" where "\<forall>i. dickson_less d m (seq (Suc i)) (seq i)" ..
    hence *: "\<And>i. dickson_less d m (seq (Suc i)) (seq i)" ..
    with transp_dickson_less have seq_decr: "\<And>i j. i < j \<Longrightarrow> dickson_less d m (seq j) (seq i)"
      by (rule transp_sequence)

    from assms obtain i j where "i < j" and i_adds_j: "seq i adds seq j"
    proof (rule dickson_gradingE)
      fix i
      from * show "d (seq i) \<le> m" by (rule dickson_lessD2)
    qed
    from \<open>i < j\<close> have "dickson_less d m (seq j) (seq i)" by (rule seq_decr)
    hence "seq j \<prec> seq i" by (rule dickson_lessD3)
    moreover from i_adds_j have "seq i \<preceq> seq j" by (rule ord_adds)
    ultimately show False by simp
  qed
qed

end

text \<open>\<open>gd_powerprod\<close> stands for @{emph \<open>graded ordered Dickson power-products\<close>}.\<close>

locale od_powerprod =
  ordered_powerprod ord ord_strict
  for ord::"'a \<Rightarrow> 'a::dickson_powerprod \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50)
begin

sublocale gd_powerprod by standard

lemma wf_ord_strict: "wfP (\<prec>)"
proof (rule wfP_chain)
  show "\<not> (\<exists>seq. \<forall>i. seq (Suc i) \<prec> seq i)"
  proof
    assume "\<exists>seq. \<forall>i. seq (Suc i) \<prec> seq i"
    then obtain seq::"nat \<Rightarrow> 'a" where "\<forall>i. seq (Suc i) \<prec> seq i" ..
    hence "\<And>i. seq (Suc i) \<prec> seq i" ..
    with ordered_powerprod_lin.transp_less have seq_decr: "\<And>i j. i < j \<Longrightarrow> (seq j) \<prec> (seq i)"
      by (rule transp_sequence)

    from dickson obtain i j::nat where "i < j" and i_adds_j: "seq i adds seq j"
      by (auto elim!: almost_full_onD)
    from seq_decr[OF \<open>i < j\<close>] have "seq j \<preceq> seq i \<and> seq j \<noteq> seq i" by auto
    hence "seq j \<preceq> seq i" and "seq j \<noteq> seq i" by simp_all
    from \<open>seq j \<noteq> seq i\<close> \<open>seq j \<preceq> seq i\<close> ord_adds[OF i_adds_j]
         ordered_powerprod_lin.eq_iff[of "seq j" "seq i"]
      show False by simp
  qed
qed

end

text \<open>\<open>od_powerprod\<close> stands for @{emph \<open>ordered Dickson power-products\<close>}.\<close>

subsection \<open>Functions as Power-Products\<close>

lemma finite_neq_0:
  assumes fin_A: "finite {x. f x \<noteq> 0}" and fin_B: "finite {x. g x \<noteq> 0}" and "\<And>x. h x 0 0 = 0"
  shows "finite {x. h x (f x) (g x) \<noteq> 0}"
proof -
  from fin_A fin_B have  "finite ({x. f x \<noteq> 0} \<union> {x. g x \<noteq> 0})" by (intro finite_UnI)
  hence finite_union: "finite {x. (f x \<noteq> 0) \<or> (g x \<noteq> 0)}" by (simp only: Collect_disj_eq)
  have "{x. h x (f x) (g x) \<noteq> 0} \<subseteq> {x. (f x \<noteq> 0) \<or> (g x \<noteq> 0)}"
  proof (intro Collect_mono, rule)
    fix x::'a
    assume h_not_zero: "h x (f x) (g x) \<noteq> 0"
    have "f x = 0 \<Longrightarrow> g x \<noteq> 0"
    proof
      assume "f x = 0" "g x = 0"
      thus False using h_not_zero \<open>h x 0 0 = 0\<close>  by simp
    qed
    thus "f x \<noteq> 0 \<or> g x \<noteq> 0" by auto
  qed
  from finite_subset[OF this] finite_union show "finite {x. h x (f x) (g x) \<noteq> 0}" .
qed

lemma finite_neq_0':
  assumes "finite {x. f x \<noteq> 0}" and "finite {x. g x \<noteq> 0}" and "h 0 0 = 0"
  shows "finite {x. h (f x) (g x) \<noteq> 0}"
  using assms by (rule finite_neq_0)

lemma finite_neq_0_inv:
  assumes fin_A: "finite {x. h x (f x) (g x) \<noteq> 0}" and fin_B: "finite {x. f x \<noteq> 0}" and "\<And>x y. h x 0 y = y"
  shows "finite {x. g x \<noteq> 0}"
proof -
  from fin_A and fin_B have "finite ({x. h x (f x) (g x) \<noteq> 0} \<union> {x. f x \<noteq> 0})" by (intro finite_UnI)
  hence finite_union: "finite {x. (h x (f x) (g x) \<noteq> 0) \<or> f x \<noteq> 0}" by (simp only: Collect_disj_eq)
  have "{x. g x \<noteq> 0} \<subseteq> {x. (h x (f x) (g x) \<noteq> 0) \<or> f x \<noteq> 0}"
    by (intro Collect_mono, rule, rule disjCI, simp add: assms(3))
  from this finite_union show "finite {x. g x \<noteq> 0}" by (rule finite_subset)
qed

lemma finite_neq_0_inv':
  assumes inf_A: "finite {x. h (f x) (g x) \<noteq> 0}" and fin_B: "finite {x. f x \<noteq> 0}" and "\<And>x. h 0 x = x"
  shows "finite {x. g x \<noteq> 0}"
  using assms by (rule finite_neq_0_inv)

subsubsection \<open>@{typ "'a \<Rightarrow> 'b"} belongs to class @{class comm_powerprod}\<close>

instance "fun" :: (type, cancel_comm_monoid_add) comm_powerprod
  by standard

subsubsection \<open>@{typ "'a \<Rightarrow> 'b"} belongs to class @{class ninv_comm_monoid_add}\<close>

instance "fun" :: (type, ninv_comm_monoid_add) ninv_comm_monoid_add
  by (standard, simp only: plus_fun_def zero_fun_def fun_eq_iff, intro allI, rule plus_eq_zero, auto)

subsubsection \<open>@{typ "'a \<Rightarrow> 'b"} belongs to class @{class lcs_powerprod}\<close>

instantiation "fun" :: (type, add_linorder) lcs_powerprod
begin

definition lcs_fun::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where "lcs f g = (\<lambda>x. max (f x) (g x))"

lemma adds_funI:
  assumes "s \<le> t"
  shows "s adds (t::'a \<Rightarrow> 'b)"
proof (rule addsI, rule)
  fix x
  from assms have "s x \<le> t x" unfolding le_fun_def ..
  hence "t x = s x + (t x - s x)" by (rule le_imp_inv)
  thus "t x = (s + (t - s)) x" by simp
qed

lemma adds_fun_iff: "f adds (g::'a \<Rightarrow> 'b) \<longleftrightarrow> (\<forall>x. f x adds g x)"
  unfolding adds_def plus_fun_def by metis

lemma adds_fun_iff': "f adds (g::'a \<Rightarrow> 'b) \<longleftrightarrow> (\<forall>x. \<exists>y. g x = f x + y)"
  unfolding adds_fun_iff unfolding adds_def plus_fun_def ..

lemma adds_lcs_fun:
  shows "s adds (lcs s (t::'a \<Rightarrow> 'b))"
  by (rule adds_funI, simp only: le_fun_def lcs_fun_def, auto simp: max_def)

lemma lcs_comm_fun:  "lcs s t = lcs t (s::'a \<Rightarrow> 'b)"
  unfolding lcs_fun_def
  by (auto simp: max_def intro!: ext)

lemma lcs_adds_fun:
  assumes "s adds u" and "t adds (u::'a \<Rightarrow> 'b)"
  shows "(lcs s t) adds u"
  using assms unfolding lcs_fun_def adds_fun_iff'
proof -
  assume a1: "\<forall>x. \<exists>y. u x = s x + y" and a2: "\<forall>x. \<exists>y. u x = t x + y"
  show "\<forall>x. \<exists>y. u x = max (s x) (t x) + y"
  proof
    fix x
    from a1 have b1: "\<exists>y. u x = s x + y" ..
    from a2 have b2: "\<exists>y. u x = t x + y" ..
    show "\<exists>y. u x = max (s x) (t x) + y" unfolding max_def
      by (split if_split, intro conjI impI, rule b2, rule b1)
  qed
qed

instance
  apply standard
  subgoal by (rule adds_lcs_fun)
  subgoal by (rule lcs_adds_fun)
  subgoal by (rule lcs_comm_fun)
  done

end

lemma leq_lcs_fun_1: "s \<le> (lcs s (t::'a \<Rightarrow> 'b::add_linorder))"
  by (simp add: lcs_fun_def le_fun_def)

lemma leq_lcs_fun_2: "t \<le> (lcs s (t::'a \<Rightarrow> 'b::add_linorder))"
  by (simp add: lcs_fun_def le_fun_def)

lemma lcs_leq_fun:
  assumes "s \<le> u" and "t \<le> (u::'a \<Rightarrow> 'b::add_linorder)"
  shows "(lcs s t) \<le> u"
  using assms by (simp add: lcs_fun_def le_fun_def)

lemma adds_fun: "s adds t \<longleftrightarrow> s \<le> t"
  for s t::"'a \<Rightarrow> 'b::add_linorder_min"
proof
  assume "s adds t"
  from this obtain k where "t = s + k" ..
  show "s \<le> t" unfolding \<open>t = s + k\<close> le_fun_def plus_fun_def le_iff_add by (simp add: leq_add_right)
qed (rule adds_funI)

lemma gcs_fun: "gcs s (t::'a \<Rightarrow> ('b::add_linorder)) = (\<lambda>x. min (s x) (t x))"
proof -
  show ?thesis unfolding gcs_def lcs_fun_def fun_diff_def
  proof (simp, rule)
    fix x
    have eq: "s x + t x = max (s x) (t x) + min (s x) (t x)" by (metis add.commute min_def max_def)
    thus "s x + t x - max (s x) (t x) = min (s x) (t x)" by simp
  qed
qed

lemma gcs_leq_fun_1: "(gcs s (t::'a \<Rightarrow> 'b::add_linorder)) \<le> s"
  by (simp add: gcs_fun le_fun_def)

lemma gcs_leq_fun_2: "(gcs s (t::'a \<Rightarrow> 'b::add_linorder)) \<le> t"
  by (simp add: gcs_fun le_fun_def)

lemma leq_gcs_fun:
  assumes "u \<le> s" and "u \<le> (t::'a \<Rightarrow> 'b::add_linorder)"
  shows "u \<le> (gcs s t)"
  using assms by (simp add: gcs_fun le_fun_def)

subsubsection \<open>@{typ "'a \<Rightarrow> 'b"} belongs to class @{class ulcs_powerprod}\<close>

instance "fun" :: (type, add_linorder_min) ulcs_powerprod ..

subsubsection \<open>Power-products in a given set of indeterminates\<close>

definition supp_fun::"('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a set" where "supp_fun f = {x. f x \<noteq> 0}"

text \<open>@{term supp_fun} for general functions is like @{term keys} for @{type poly_mapping},
  but does not need to be finite.\<close>

lemma keys_eq_supp: "keys s = supp_fun (lookup s)"
  unfolding supp_fun_def by (transfer, rule)

lemma supp_fun_zero [simp]: "supp_fun 0 = {}"
  by (auto simp: supp_fun_def)

lemma supp_fun_eq_zero_iff: "supp_fun f = {} \<longleftrightarrow> f = 0"
  by (auto simp: supp_fun_def)

lemma sub_supp_empty: "supp_fun s \<subseteq> {} \<longleftrightarrow> (s = 0)"
  by (auto simp: supp_fun_def)

lemma except_fun_idI: "supp_fun f \<inter> V = {} \<Longrightarrow> except_fun f V = f"
  by (auto simp: except_fun_def supp_fun_def when_def intro!: ext)

lemma supp_except_fun: "supp_fun (except_fun s V) = supp_fun s - V"
  by (auto simp: except_fun_def supp_fun_def)

lemma supp_fun_plus_subset: "supp_fun (s + t) \<subseteq> supp_fun s \<union> supp_fun (t::'a \<Rightarrow> 'b::monoid_add)"
  unfolding supp_fun_def by force

lemma fun_eq_zeroI:
  assumes "\<And>x. x \<in> supp_fun f \<Longrightarrow> f x = 0"
  shows "f = 0"
proof (rule, simp)
  fix x
  show "f x = 0"
  proof (cases "x \<in> supp_fun f")
    case True
    then show ?thesis by (rule assms)
  next
    case False
    then show ?thesis by (simp add: supp_fun_def)
  qed
qed

lemma except_fun_cong1:
  "supp_fun s \<inter> ((V - U) \<union> (U - V)) \<subseteq> {} \<Longrightarrow> except_fun s V = except_fun s U"
  by (auto simp: except_fun_def when_def supp_fun_def intro!: ext)

lemma adds_except_fun:
  "s adds t = (except_fun s V adds except_fun t V \<and> except_fun s (- V) adds except_fun t (- V))"
  for s t :: "'a \<Rightarrow> 'b::add_linorder"
  by (auto simp: supp_fun_def except_fun_def adds_fun_iff when_def)

lemma adds_except_fun_singleton: "s adds t = (except_fun s {v} adds except_fun t {v} \<and> s v adds t v)"
  for s t :: "'a \<Rightarrow> 'b::add_linorder"
  by (auto simp: supp_fun_def except_fun_def adds_fun_iff when_def)

subsubsection \<open>Dickson's lemma for power-products in finitely many indeterminates\<close>

lemma Dickson_fun:
  assumes "finite V"
  shows "almost_full_on (adds) {x::'a \<Rightarrow> 'b::add_wellorder. supp_fun x \<subseteq> V}"
  using assms
proof (induct V)
  case empty
  have "finite {0}" by simp
  moreover have "reflp_on (adds) {0::'a \<Rightarrow> 'b}" by (simp add: reflp_on_def)
  ultimately have "almost_full_on (adds) {0::'a \<Rightarrow> 'b}" by (rule finite_almost_full_on)
  thus ?case by (simp add: supp_fun_eq_zero_iff)
next
  case (insert v V)
  show ?case
  proof (rule almost_full_onI)
    fix seq::"nat \<Rightarrow> 'a \<Rightarrow> 'b"
    assume "\<forall>i. seq i \<in> {x. supp_fun x \<subseteq> insert v V}"
    hence a: "supp_fun (seq i) \<subseteq> insert v V" for i by simp
    define seq' where "seq' = (\<lambda>i. (except_fun (seq i) {v}, except_fun (seq i) V))"
    have "almost_full_on (adds) {x::'a \<Rightarrow> 'b. supp_fun x \<subseteq> {v}}"
    proof (rule almost_full_onI)
      fix f::"nat \<Rightarrow> 'a \<Rightarrow> 'b"
      assume "\<forall>i. f i \<in> {x. supp_fun x \<subseteq> {v}}"
      hence b: "supp_fun (f i) \<subseteq> {v}" for i by simp
      let ?f = "\<lambda>i. f i v"
      have "wfP ((<)::'b \<Rightarrow> _)" by (simp add: wf wfP_def)
      hence "\<forall>f::nat \<Rightarrow> 'b. \<exists>i. f i \<le> f (Suc i)"
        by (simp add: wf_iff_no_infinite_down_chain[to_pred] not_less)
      hence "\<exists>i. ?f i \<le> ?f (Suc i)" ..
      then obtain i where "?f i \<le> ?f (Suc i)" ..
      have "i < Suc i" by simp
      moreover have "f i adds f (Suc i)" unfolding adds_fun_iff
      proof
        fix x
        show "f i x adds f (Suc i) x"
        proof (cases "x = v")
          case True
          with \<open>?f i \<le> ?f (Suc i)\<close> show ?thesis by (simp add: adds_def le_iff_add)
        next
          case False
          with b have "x \<notin> supp_fun (f i)" and "x \<notin> supp_fun (f (Suc i))" by blast+
          thus ?thesis by (simp add: supp_fun_def)
        qed
      qed
      ultimately show "good (adds) f" by (meson goodI)
    qed
    with insert(3) have
      "almost_full_on (prod_le (adds) (adds)) ({x::'a \<Rightarrow> 'b. supp_fun x \<subseteq> V} \<times> {x::'a \<Rightarrow> 'b. supp_fun x \<subseteq> {v}})"
      (is "almost_full_on ?P ?A") by (rule almost_full_on_Sigma)
    moreover from a have "seq' i \<in> ?A" for i by (auto simp add: seq'_def supp_except_fun)
    ultimately obtain i j where "i < j" and "?P (seq' i) (seq' j)" by (rule almost_full_onD)
    have "seq i adds seq j" unfolding adds_except_fun[where s="seq i" and V=V]
    proof
      from \<open>?P (seq' i) (seq' j)\<close> show "except_fun (seq i) V adds except_fun (seq j) V"
        by (simp add: prod_le_def seq'_def)
    next
      from \<open>?P (seq' i) (seq' j)\<close> have "except_fun (seq i) {v} adds except_fun (seq j) {v}"
        by (simp add: prod_le_def seq'_def)
      moreover have "except_fun (seq i) (- V) = except_fun (seq i) {v}"
        by (rule except_fun_cong1; use a[of i] insert.hyps(2) in blast)
      moreover have "except_fun (seq j) (- V) = except_fun (seq j) {v}"
        by (rule except_fun_cong1; use a[of j] insert.hyps(2) in blast)
      ultimately show "except_fun (seq i) (- V) adds except_fun (seq j) (- V)" by simp
    qed
    with \<open>i < j\<close> show "good (adds) seq" by (meson goodI)
  qed
qed

instance "fun" :: (finite, add_wellorder) dickson_powerprod
proof
  have "finite (UNIV::'a set)" by simp
  hence "almost_full_on (adds) {x::'a \<Rightarrow> 'b. supp_fun x \<subseteq> UNIV}" by (rule Dickson_fun)
  thus "almost_full_on (adds) (UNIV::('a \<Rightarrow> 'b) set)" by simp
qed

subsubsection \<open>Lexicographic Term Order\<close>

text \<open>Term orders are certain linear orders on power-products, satisfying additional requirements.
  Further information on term orders can be found, e.\,g., in @{cite Robbiano1985}.\<close>

context wellorder
begin

lemma neq_fun_alt:
  assumes "s \<noteq> (t::'a \<Rightarrow> 'b)"
  obtains x where "s x \<noteq> t x" and "\<And>y. s y \<noteq> t y \<Longrightarrow> x \<le> y"
proof -
  from assms ext[of s t] have "\<exists>x. s x \<noteq> t x" by auto
  with exists_least_iff[of "\<lambda>x. s x \<noteq> t x"]
  obtain x where x1: "s x \<noteq> t x" and x2: "\<And>y. y < x \<Longrightarrow> s y = t y"
    by auto
  show ?thesis
  proof
    from x1 show "s x \<noteq> t x" .
  next
    fix y
    assume "s y \<noteq> t y"
    with x2[of y] have "\<not> y < x" by auto
    thus "x \<le> y" by simp
  qed
qed

definition lex_fun::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "lex_fun s t \<equiv> (\<forall>x. s x \<le> t x \<or> (\<exists>y<x. s y \<noteq> t y))"

definition "lex_fun_strict s t \<longleftrightarrow> lex_fun s t \<and> \<not> lex_fun t s"

text \<open>Attention! @{term lex_fun} reverses the order of the indeterminates: if @{term x} is smaller than
  @{term y} w.r.t. the order on @{typ 'a}, then the @{emph \<open>power-product\<close>} @{term x} is
  @{emph \<open>greater\<close>} than the @{emph \<open>power-product\<close>} @{term y}.\<close>

lemma lex_fun_alt:
  shows "lex_fun s t = (s = t \<or> (\<exists>x. s x < t x \<and> (\<forall>y<x. s y = t y)))" (is "?L = ?R")
proof
  assume ?L
  show ?R
  proof (cases "s = t")
    assume "s = t"
    thus ?R by simp
  next
    assume "s \<noteq> t"
    from neq_fun_alt[OF this] obtain x0
      where x0_neq: "s x0 \<noteq> t x0" and x0_min: "\<And>z. s z \<noteq> t z \<Longrightarrow> x0 \<le> z" by auto
    show ?R
    proof (intro disjI2, rule exI[of _ x0], intro conjI)
      from \<open>?L\<close> have "s x0 \<le> t x0 \<or> (\<exists>y. y < x0 \<and> s y \<noteq> t y)" unfolding lex_fun_def ..
      thus "s x0 < t x0"
      proof
        assume "s x0 \<le> t x0"
        from this x0_neq show ?thesis by simp
      next
        assume "\<exists>y. y < x0 \<and> s y \<noteq> t y"
        then obtain y where "y < x0" and y_neq: "s y \<noteq> t y" by auto
        from \<open>y < x0\<close> x0_min[OF y_neq] show ?thesis by simp
      qed
    next
      show "\<forall>y<x0. s y = t y"
      proof (rule, rule)
        fix y
        assume "y < x0"
        hence "\<not> x0 \<le> y" by simp
        from this x0_min[of y] show "s y = t y" by auto
      qed
    qed
  qed
next
  assume ?R
  thus ?L
  proof
    assume "s = t"
    thus ?thesis by (simp add: lex_fun_def)
  next
    assume "\<exists>x. s x < t x \<and> (\<forall>y<x. s y = t y)"
    then obtain y where y: "s y < t y" and y_min: "\<forall>z<y. s z = t z" by auto
    show ?thesis unfolding lex_fun_def
    proof
      fix x
      show "s x \<le> t x \<or> (\<exists>y<x. s y \<noteq> t y)"
      proof (cases "s x \<le> t x")
        assume "s x \<le> t x"
        thus ?thesis by simp
      next
        assume x: "\<not> s x \<le> t x"
        show ?thesis
        proof (intro disjI2, rule exI[of _ y], intro conjI)
          have "\<not> x \<le> y"
          proof
            assume "x \<le> y"
            hence "x < y \<or> y = x" by auto
            thus False
            proof
              assume "x < y"
              from x y_min[rule_format, OF this] show ?thesis by simp
            next
              assume "y = x"
              from this x y show ?thesis
                by (auto simp: preorder_class.less_le_not_le)
            qed
          qed
          thus "y < x" by simp
        next
          from y show "s y \<noteq> t y" by simp
        qed
      qed
    qed
  qed
qed

lemma lex_fun_refl: "lex_fun s s"
unfolding lex_fun_alt by simp

lemma lex_fun_antisym:
  assumes "lex_fun s t" and "lex_fun t s"
  shows "s = t"
proof
  fix x
  from assms(1) have "s = t \<or> (\<exists>x. s x < t x \<and> (\<forall>y<x. s y = t y))"
    unfolding lex_fun_alt .
  thus "s x = t x"
  proof
    assume "s = t"
    thus ?thesis by simp
  next
    assume "\<exists>x. s x < t x \<and> (\<forall>y<x. s y = t y)"
    then obtain x0 where x0: "s x0 < t x0" and x0_min: "\<forall>y<x0. s y = t y" by auto
    from assms(2) have "t = s \<or> (\<exists>x. t x < s x \<and> (\<forall>y<x. t y = s y))" unfolding lex_fun_alt .
    thus ?thesis
    proof
      assume "t = s"
      thus ?thesis by simp
    next
      assume "\<exists>x. t x < s x \<and> (\<forall>y<x. t y = s y)"
      then obtain x1 where x1: "t x1 < s x1" and x1_min: "\<forall>y<x1. t y = s y" by auto
      have "x0 < x1 \<or> x1 < x0 \<or> x1 = x0" using local.antisym_conv3 by auto
      show ?thesis
      proof (rule linorder_cases[of x0 x1])
        assume "x1 < x0"
        from x0_min[rule_format, OF this] x1 show ?thesis by simp
      next
        assume "x0 = x1"
        from this x0 x1 show ?thesis by simp
      next
        assume "x0 < x1"
        from x1_min[rule_format, OF this] x0 show ?thesis by simp
      qed
    qed
  qed
qed

lemma lex_fun_trans:
  assumes "lex_fun s t" and "lex_fun t u"
  shows "lex_fun s u"
proof -
  from assms(1) have "s = t \<or> (\<exists>x. s x < t x \<and> (\<forall>y<x. s y = t y))" unfolding lex_fun_alt .
  thus ?thesis
  proof
    assume "s = t"
    from this assms(2) show ?thesis by simp
  next
    assume "\<exists>x. s x < t x \<and> (\<forall>y<x. s y = t y)"
    then obtain x0 where x0: "s x0 < t x0" and x0_min: "\<forall>y<x0. s y = t y"
      by auto
    from assms(2) have "t = u \<or> (\<exists>x. t x < u x \<and> (\<forall>y<x. t y = u y))" unfolding lex_fun_alt .
    thus ?thesis
    proof
      assume "t = u"
      from this assms(1) show ?thesis by simp
    next
      assume "\<exists>x. t x < u x \<and> (\<forall>y<x. t y = u y)"
      then obtain x1 where x1: "t x1 < u x1" and x1_min: "\<forall>y<x1. t y = u y" by auto
      show ?thesis unfolding lex_fun_alt
      proof (intro disjI2)
        show "\<exists>x. s x < u x \<and> (\<forall>y<x. s y = u y)"
        proof (rule linorder_cases[of x0 x1])
          assume "x1 < x0"
          show ?thesis
          proof (rule exI[of _ x1], intro conjI)
            from x0_min[rule_format, OF \<open>x1 < x0\<close>] x1 show "s x1 < u x1" by simp
          next
            show "\<forall>y<x1. s y = u y"
            proof (intro allI, intro impI)
              fix y
              assume "y < x1"
              from this \<open>x1 < x0\<close> have "y < x0" by simp
              from x0_min[rule_format, OF this] x1_min[rule_format, OF \<open>y < x1\<close>]
                show "s y = u y" by simp
            qed
          qed
        next
          assume "x0 < x1"
          show ?thesis
          proof (rule exI[of _ x0], intro conjI)
            from x1_min[rule_format, OF \<open>x0 < x1\<close>] x0 show "s x0 < u x0" by simp
          next
            show "\<forall>y<x0. s y = u y"
            proof (intro allI, intro impI)
              fix y
              assume "y < x0"
              from this \<open>x0 < x1\<close> have "y < x1" by simp
              from x0_min[rule_format, OF \<open>y < x0\<close>] x1_min[rule_format, OF this]
                show "s y = u y" by simp
            qed
          qed
        next
          assume "x0 = x1"
          show ?thesis
          proof (rule exI[of _ x1], intro conjI)
            from \<open>x0 = x1\<close> x0 x1 show "s x1 < u x1" by simp
          next
            show "\<forall>y<x1. s y = u y"
            proof (intro allI, intro impI)
              fix y
              assume "y < x1"
              hence "y < x0" using \<open>x0 = x1\<close> by simp
              from x0_min[rule_format, OF this] x1_min[rule_format, OF \<open>y < x1\<close>]
                show "s y = u y" by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma lex_fun_lin: "lex_fun s t \<or> lex_fun t s" for s t::"'a \<Rightarrow> 'b::{ordered_comm_monoid_add, linorder}"
proof (intro disjCI)
  assume "\<not> lex_fun t s"
  hence a: "\<forall>x. \<not> (t x < s x) \<or> (\<exists>y<x. t y \<noteq> s y)" unfolding lex_fun_alt by auto
  show "lex_fun s t" unfolding lex_fun_def
  proof
    fix x
    from a have "\<not> (t x < s x) \<or> (\<exists>y<x. t y \<noteq> s y)" ..
    thus "s x \<le> t x \<or> (\<exists>y<x. s y \<noteq> t y)" by auto
  qed
qed

corollary lex_fun_strict_alt [code]:
  "lex_fun_strict s t = (\<not> lex_fun t s)" for s t::"'a \<Rightarrow> 'b::{ordered_comm_monoid_add, linorder}"
  unfolding lex_fun_strict_def using lex_fun_lin[of s t] by auto

lemma lex_fun_zero_min: "lex_fun 0 s" for s::"'a \<Rightarrow> 'b::add_linorder_min"
  by (simp add: lex_fun_def zero_min)

lemma lex_fun_plus_monotone:
  "lex_fun (s + u) (t + u)" if "lex_fun s t"
  for s t::"'a \<Rightarrow> 'b::ordered_cancel_comm_monoid_add"
unfolding lex_fun_def
proof
  fix x
  from that have "s x \<le> t x \<or> (\<exists>y<x. s y \<noteq> t y)" unfolding lex_fun_def ..
  thus "(s + u) x \<le> (t + u) x \<or> (\<exists>y<x. (s + u) y \<noteq> (t + u) y)"
  proof
    assume a1: "s x \<le> t x"
    show ?thesis
    proof (intro disjI1)
      from a1 show "(s + u) x \<le> (t + u) x" by (auto simp: add_right_mono)
    qed
  next
    assume "\<exists>y<x. s y \<noteq> t y"
    then obtain y where "y < x" and a2: "s y \<noteq> t y" by auto
    show ?thesis
    proof (intro disjI2, rule exI[of _ y], intro conjI, fact)
      from a2 show "(s + u) y \<noteq> (t + u) y" by (auto simp: add_right_mono)
    qed
  qed
qed

end (* wellorder *)

subsubsection \<open>Degree\<close>

definition deg_fun::"('a \<Rightarrow> 'b::comm_monoid_add) \<Rightarrow> 'b" where "deg_fun s \<equiv> \<Sum>x\<in>(supp_fun s). s x"

lemma deg_fun_zero[simp]: "deg_fun 0 = 0"
  by (auto simp: deg_fun_def)

lemma deg_fun_eq_0_iff:
  assumes "finite (supp_fun (s::'a \<Rightarrow> 'b::add_linorder_min))"
  shows "deg_fun s = 0 \<longleftrightarrow> s = 0"
proof
  assume "deg_fun s = 0"
  hence *: "(\<Sum>x\<in>(supp_fun s). s x) = 0" by (simp only: deg_fun_def)
  have **: "\<And>x. 0 \<le> s x" by (rule zero_min)
  from * have "\<And>x. x \<in> supp_fun s \<Longrightarrow> s x = 0" by (simp only: sum_nonneg_eq_0_iff[OF assms **])
  thus "s = 0" by (rule fun_eq_zeroI)
qed simp

lemma deg_fun_superset:
  fixes A::"'a set"
  assumes "supp_fun s \<subseteq> A" and "finite A"
  shows "deg_fun s = (\<Sum>x\<in>A. s x)"
  unfolding deg_fun_def
proof (rule sum.mono_neutral_cong_left, fact, fact, rule)
  fix x
  assume "x \<in> A - supp_fun s"
  hence "x \<notin> supp_fun s" by simp
  thus "s x = 0" by (simp add: supp_fun_def)
qed rule

lemma deg_fun_plus:
  assumes "finite (supp_fun s)" and "finite (supp_fun t)"
  shows "deg_fun (s + t) = deg_fun s + deg_fun (t::'a \<Rightarrow> 'b::comm_monoid_add)"
proof -
  from assms have fin: "finite (supp_fun s \<union> supp_fun t)" by simp
  have "deg_fun (s + t) = (\<Sum>x\<in>(supp_fun (s + t)). s x + t x)" by (simp add: deg_fun_def)
  also from fin have "... = (\<Sum>x\<in>(supp_fun s \<union> supp_fun t). s x + t x)"
  proof (rule sum.mono_neutral_cong_left)
    show "\<forall>x\<in>supp_fun s \<union> supp_fun t - supp_fun (s + t). s x + t x = 0"
    proof
      fix x
      assume "x \<in> supp_fun s \<union> supp_fun t - supp_fun (s + t)"
      hence "x \<notin> supp_fun (s + t)" by simp
      thus "s x + t x = 0" by (simp add: supp_fun_def)
    qed
  qed (rule supp_fun_plus_subset, rule)
  also have "\<dots> = (\<Sum>x\<in>(supp_fun s \<union> supp_fun t). s x) + (\<Sum>x\<in>(supp_fun s \<union> supp_fun t). t x)"
    by (rule sum.distrib)
  also from fin have "(\<Sum>x\<in>(supp_fun s \<union> supp_fun t). s x) = deg_fun s" unfolding deg_fun_def
  proof (rule sum.mono_neutral_cong_right)
    show "\<forall>x\<in>supp_fun s \<union> supp_fun t - supp_fun s. s x = 0"
    proof
      fix x
      assume "x \<in> supp_fun s \<union> supp_fun t - supp_fun s"
      hence "x \<notin> supp_fun s" by simp
      thus "s x = 0" by (simp add: supp_fun_def)
    qed
  qed simp_all
  also from fin have "(\<Sum>x\<in>(supp_fun s \<union> supp_fun t). t x) = deg_fun t" unfolding deg_fun_def
  proof (rule sum.mono_neutral_cong_right)
  show "\<forall>x\<in>supp_fun s \<union> supp_fun t - supp_fun t. t x = 0"
    proof
      fix x
      assume "x \<in> supp_fun s \<union> supp_fun t - supp_fun t"
      hence "x \<notin> supp_fun t" by simp
      thus "t x = 0" by (simp add: supp_fun_def)
    qed
  qed simp_all
  finally show ?thesis .
qed

lemma deg_fun_leq:
  assumes "finite (supp_fun s)" and "finite (supp_fun t)" and "s \<le> (t::'a \<Rightarrow> 'b::ordered_comm_monoid_add)"
  shows "deg_fun s \<le> deg_fun t"
proof -
  let ?A = "supp_fun s \<union> supp_fun t"
  from assms(1) assms(2) have 1: "finite ?A" by simp
  have s: "supp_fun s \<subseteq> ?A" and t: "supp_fun t \<subseteq> ?A" by simp_all
  show ?thesis unfolding deg_fun_superset[OF s 1] deg_fun_superset[OF t 1]
  proof (rule sum_mono)
    fix i
    from assms(3) show "s i \<le> t i" unfolding le_fun_def ..
  qed
qed

subsubsection \<open>General Degree-Orders\<close>

context linorder
begin

lemma ex_min:
  assumes "finite (A::'a set)" and "A \<noteq> {}"
  shows "\<exists>y\<in>A. (\<forall>z\<in>A. y \<le> z)"
using assms
proof (induct rule: finite_induct)
  assume "{} \<noteq> {}"
  thus "\<exists>y\<in>{}. \<forall>z\<in>{}. y \<le> z" by simp
next
  fix a::'a and A::"'a set"
  assume "a \<notin> A" and IH: "A \<noteq> {} \<Longrightarrow> \<exists>y\<in>A. (\<forall>z\<in>A. y \<le> z)"
  show "\<exists>y\<in>insert a A. (\<forall>z\<in>insert a A. y \<le> z)"
  proof (cases "A = {}")
    case True
    show ?thesis
    proof (rule bexI[of _ a], intro ballI)
      fix z
      assume "z \<in> insert a A"
      from this True have "z = a" by simp
      thus "a \<le> z" by simp
    qed (simp)
  next
    case False
    from IH[OF False] obtain y where "y \<in> A" and y_min: "\<forall>z\<in>A. y \<le> z" by auto
    from linear[of a y] show ?thesis
    proof
      assume "y \<le> a"
      show ?thesis
      proof (rule bexI[of _ y], intro ballI)
        fix z
        assume "z \<in> insert a A"
        hence "z = a \<or> z \<in> A" by simp
        thus "y \<le> z"
        proof
          assume "z = a"
          from this \<open>y \<le> a\<close> show "y \<le> z" by simp
        next
          assume "z \<in> A"
          from y_min[rule_format, OF this] show "y \<le> z" .
        qed
      next
        from \<open>y \<in> A\<close> show "y \<in> insert a A" by simp
      qed
    next
      assume "a \<le> y"
      show ?thesis
      proof (rule bexI[of _ a], intro ballI)
        fix z
        assume "z \<in> insert a A"
        hence "z = a \<or> z \<in> A" by simp
        thus "a \<le> z"
        proof
          assume "z = a"
          from this show "a \<le> z" by simp
        next
          assume "z \<in> A"
          from y_min[rule_format, OF this] \<open>a \<le> y\<close> show "a \<le> z" by simp
        qed
      qed (simp)
    qed
  qed
qed

definition dord_fun::"(('a \<Rightarrow> 'b::ordered_comm_monoid_add) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "dord_fun ord s t \<equiv> (let d1 = deg_fun s; d2 = deg_fun t in (d1 < d2 \<or> (d1 = d2 \<and> ord s t)))"

lemma dord_fun_degD:
  assumes "dord_fun ord s t"
  shows "deg_fun s \<le> deg_fun t"
  using assms unfolding dord_fun_def Let_def by auto

lemma dord_fun_refl:
  assumes "ord s s"
  shows "dord_fun ord s s"
  using assms unfolding dord_fun_def by simp

lemma dord_fun_antisym:
  assumes ord_antisym: "ord s t \<Longrightarrow> ord t s \<Longrightarrow> s = t" and "dord_fun ord s t" and "dord_fun ord t s"
  shows "s = t"
proof -
  from assms(3) have ts: "deg_fun t < deg_fun s \<or> (deg_fun t = deg_fun s \<and> ord t s)"
    unfolding dord_fun_def Let_def .
  from assms(2) have st: "deg_fun s < deg_fun t \<or> (deg_fun s = deg_fun t \<and> ord s t)"
    unfolding dord_fun_def Let_def .
  thus ?thesis
  proof
    assume "deg_fun s < deg_fun t"
    thus ?thesis using ts by auto
  next
    assume "deg_fun s = deg_fun t \<and> ord s t"
    hence "deg_fun s = deg_fun t" and "ord s t" by simp_all
    from \<open>deg_fun s = deg_fun t\<close> ts have "ord t s" by simp
    with \<open>ord s t\<close> show ?thesis by (rule ord_antisym)
  qed
qed

lemma dord_fun_trans:
  assumes ord_trans: "ord s t \<Longrightarrow> ord t u \<Longrightarrow> ord s u" and "dord_fun ord s t" and "dord_fun ord t u"
  shows "dord_fun ord s u"
proof -
  from assms(3) have ts: "deg_fun t < deg_fun u \<or> (deg_fun t = deg_fun u \<and> ord t u)"
    unfolding dord_fun_def Let_def .
  from assms(2) have st: "deg_fun s < deg_fun t \<or> (deg_fun s = deg_fun t \<and> ord s t)"
    unfolding dord_fun_def Let_def .
  thus ?thesis
  proof
    assume "deg_fun s < deg_fun t"
    from this dord_fun_degD[OF assms(3)] have "deg_fun s < deg_fun u" by simp
    thus ?thesis by (simp add: dord_fun_def Let_def)
  next
    assume "deg_fun s = deg_fun t \<and> ord s t"
    hence "deg_fun s = deg_fun t" and "ord s t" by simp_all
    from ts show ?thesis
    proof
      assume "deg_fun t < deg_fun u"
      hence "deg_fun s < deg_fun u" using \<open>deg_fun s = deg_fun t\<close> by simp
      thus ?thesis by (simp add: dord_fun_def Let_def)
    next
      assume "deg_fun t = deg_fun u \<and> ord t u"
      hence "deg_fun t = deg_fun u" and "ord t u" by simp_all
      from ord_trans[OF \<open>ord s t\<close> \<open>ord t u\<close>] \<open>deg_fun s = deg_fun t\<close> \<open>deg_fun t = deg_fun u\<close> show ?thesis
        by (simp add: dord_fun_def Let_def)
    qed
  qed
qed

lemma dord_fun_lin:
  "dord_fun ord s t \<or> dord_fun ord t s"
  if "ord s t \<or> ord t s"
  for s t::"'a \<Rightarrow> 'b::{ordered_comm_monoid_add, linorder}"
proof (intro disjCI)
  assume "\<not> dord_fun ord t s"
  hence "deg_fun s \<le> deg_fun t \<and> (deg_fun t \<noteq> deg_fun s \<or> \<not> ord t s)"
    unfolding dord_fun_def Let_def by auto
  hence "deg_fun s \<le> deg_fun t" and dis1: "deg_fun t \<noteq> deg_fun s \<or> \<not> ord t s" by simp_all
  show "dord_fun ord s t" unfolding dord_fun_def Let_def
  proof (intro disjCI)
    assume "\<not> (deg_fun s = deg_fun t \<and> ord s t)"
    hence dis2: "deg_fun s \<noteq> deg_fun t \<or> \<not> ord s t" by simp
    show "deg_fun s < deg_fun t"
    proof (cases "deg_fun s = deg_fun t")
      case True
      from True dis1 have "\<not> ord t s" by simp
      from True dis2 have "\<not> ord s t" by simp
      from \<open>\<not> ord s t\<close> \<open>\<not> ord t s\<close> that show ?thesis by simp
    next
      case False
      from this \<open>deg_fun s \<le> deg_fun t\<close> show ?thesis by simp
    qed
  qed
qed

lemma dord_fun_zero_min:
  fixes s t::"'a \<Rightarrow> 'b::add_linorder_min"
  assumes ord_refl: "\<And>t. ord t t" and "finite (supp_fun s)"
  shows "dord_fun ord 0 s"
  unfolding dord_fun_def Let_def deg_fun_zero
proof (rule disjCI)
  assume "\<not> (0 = deg_fun s \<and> ord 0 s)"
  hence dis: "deg_fun s \<noteq> 0 \<or> \<not> ord 0 s" by simp
  show "0 < deg_fun s"
  proof (cases "deg_fun s = 0")
    case True
    hence "s = 0" using deg_fun_eq_0_iff[OF assms(2)] by auto
    hence "ord 0 s" using ord_refl by simp
    with True dis show ?thesis by simp
  next
    case False
    thus ?thesis by (auto simp: zero_less_iff_neq_zero)
  qed
qed

lemma dord_fun_plus_monotone:
  fixes s t u ::"'a \<Rightarrow> 'b::{ordered_comm_monoid_add, ordered_ab_semigroup_add_imp_le}"
  assumes ord_monotone: "ord s t \<Longrightarrow> ord (s + u) (t + u)" and "finite (supp_fun s)"
    and "finite (supp_fun t)" and "finite (supp_fun u)" and "dord_fun ord s t"
  shows "dord_fun ord (s + u) (t + u)"
proof -
  from assms(5) have "deg_fun s < deg_fun t \<or> (deg_fun s = deg_fun t \<and> ord s t)"
    unfolding dord_fun_def Let_def .
  thus ?thesis
  proof
    assume "deg_fun s < deg_fun t"
    hence "deg_fun (s + u) < deg_fun (t + u)" by (auto simp: deg_fun_plus[OF _ assms(4)] assms(2) assms(3))
    thus ?thesis unfolding dord_fun_def Let_def by simp
  next
    assume "deg_fun s = deg_fun t \<and> ord s t"
    hence "deg_fun s = deg_fun t" and "ord s t" by simp_all
    from \<open>deg_fun s = deg_fun t\<close> have "deg_fun (s + u) = deg_fun (t + u)"
      by (auto simp: deg_fun_plus[OF _ assms(4)] assms(2) assms(3))
    from this ord_monotone[OF \<open>ord s t\<close>] show ?thesis unfolding dord_fun_def Let_def by simp
  qed
qed

end (* linorder *)

context wellorder
begin

subsubsection \<open>Degree-Lexicographic Term Order\<close>

definition dlex_fun::"('a \<Rightarrow> 'b::ordered_comm_monoid_add) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "dlex_fun \<equiv> dord_fun lex_fun"

definition "dlex_fun_strict s t \<longleftrightarrow> dlex_fun s t \<and> \<not> dlex_fun t s"

lemma dlex_fun_refl:
  shows "dlex_fun s s"
unfolding dlex_fun_def by (rule dord_fun_refl, rule lex_fun_refl)

lemma dlex_fun_antisym:
  assumes "dlex_fun s t" and "dlex_fun t s"
  shows "s = t"
  by (rule dord_fun_antisym, erule lex_fun_antisym, assumption,
      simp_all only: dlex_fun_def[symmetric], fact+)

lemma dlex_fun_trans:
  assumes "dlex_fun s t" and "dlex_fun t u"
  shows "dlex_fun s u"
  by (simp only: dlex_fun_def, rule dord_fun_trans, erule lex_fun_trans, assumption,
      simp_all only: dlex_fun_def[symmetric], fact+)

lemma dlex_fun_lin: "dlex_fun s t \<or> dlex_fun t s"
  for s t::"('a \<Rightarrow> 'b::{ordered_comm_monoid_add, linorder})"
  unfolding dlex_fun_def by (rule dord_fun_lin, rule lex_fun_lin)

corollary dlex_fun_strict_alt [code]:
  "dlex_fun_strict s t = (\<not> dlex_fun t s)" for s t::"'a \<Rightarrow> 'b::{ordered_comm_monoid_add, linorder}"
  unfolding dlex_fun_strict_def using dlex_fun_lin by auto

lemma dlex_fun_zero_min:
  fixes s t::"('a \<Rightarrow> 'b::add_linorder_min)"
  assumes "finite (supp_fun s)"
  shows "dlex_fun 0 s"
  unfolding dlex_fun_def by (rule dord_fun_zero_min, rule lex_fun_refl, fact)

lemma dlex_fun_plus_monotone:
  fixes s t u::"'a \<Rightarrow> 'b::{ordered_cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le}"
  assumes "finite (supp_fun s)" and "finite (supp_fun t)" and "finite (supp_fun u)" and "dlex_fun s t"
  shows "dlex_fun (s + u) (t + u)"
  using lex_fun_plus_monotone[of s t u] assms unfolding dlex_fun_def
  by (rule dord_fun_plus_monotone)

subsubsection \<open>Degree-Reverse-Lexicographic Term Order\<close>

abbreviation rlex_fun::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "rlex_fun s t \<equiv> lex_fun t s"

text \<open>Note that @{const rlex_fun} is not precisely the reverse-lexicographic order relation on
  power-products. Normally, the @{emph \<open>last\<close>} (i.\,e. highest) indeterminate whose exponent differs
  in the two power-products to be compared is taken, but since we do not require the domain to be finite,
  there might not be such a last indeterminate. Therefore, we simply take the converse of
  @{const lex_fun}.\<close>

definition drlex_fun::"('a \<Rightarrow> 'b::ordered_comm_monoid_add) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "drlex_fun \<equiv> dord_fun rlex_fun"

definition "drlex_fun_strict s t \<longleftrightarrow> drlex_fun s t \<and> \<not> drlex_fun t s"

lemma drlex_fun_refl:
  shows "drlex_fun s s"
  unfolding drlex_fun_def by (rule dord_fun_refl, fact lex_fun_refl)

lemma drlex_fun_antisym:
  assumes "drlex_fun s t" and "drlex_fun t s"
  shows "s = t"
  by (rule dord_fun_antisym, erule lex_fun_antisym, assumption,
      simp_all only: drlex_fun_def[symmetric], fact+)

lemma drlex_fun_trans:
  assumes "drlex_fun s t" and "drlex_fun t u"
  shows "drlex_fun s u"
  by (simp only: drlex_fun_def, rule dord_fun_trans, erule lex_fun_trans, assumption,
      simp_all only: drlex_fun_def[symmetric], fact+)

lemma drlex_fun_lin: "drlex_fun s t \<or> drlex_fun t s"
  for s t::"('a \<Rightarrow> 'b::{ordered_comm_monoid_add, linorder})"
  unfolding drlex_fun_def by (rule dord_fun_lin, rule lex_fun_lin)

corollary drlex_fun_strict_alt [code]:
  "drlex_fun_strict s t = (\<not> drlex_fun t s)" for s t::"'a \<Rightarrow> 'b::{ordered_comm_monoid_add, linorder}"
  unfolding drlex_fun_strict_def using drlex_fun_lin by auto

lemma drlex_fun_zero_min:
  fixes s t::"('a \<Rightarrow> 'b::add_linorder_min)"
  assumes "finite (supp_fun s)"
  shows "drlex_fun 0 s"
  unfolding drlex_fun_def by (rule dord_fun_zero_min, rule lex_fun_refl, fact)

lemma drlex_fun_plus_monotone:
  fixes s t u::"'a \<Rightarrow> 'b::{ordered_cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le}"
  assumes "finite (supp_fun s)" and "finite (supp_fun t)" and "finite (supp_fun u)" and "drlex_fun s t"
  shows "drlex_fun (s + u) (t + u)"
  using lex_fun_plus_monotone[of t s u] assms unfolding drlex_fun_def
  by (rule dord_fun_plus_monotone)

end (* wellorder *)

text\<open>Every finite linear ordering is also a well-ordering. This fact is particularly useful when
  working with fixed finite sets of indeterminates.\<close>
class finite_linorder = finite + linorder
begin

subclass wellorder
proof
  fix P::"'a \<Rightarrow> bool" and a
  assume hyp: "\<And>x. (\<And>y. (y < x) \<Longrightarrow> P y) \<Longrightarrow> P x"
  show "P a"
  proof (rule ccontr)
    assume "\<not> P a"
    have "finite {x. \<not> P x}" (is "finite ?A") by simp
    from \<open>\<not> P a\<close> have "a \<in> ?A" by simp
    hence "?A \<noteq> {}" by auto
    from ex_min[OF \<open>finite ?A\<close> this] obtain b where "b \<in> ?A" and b_min: "\<forall>y\<in>?A. b \<le> y" by auto
    from \<open>b \<in> ?A\<close> have "\<not> P b" by simp
    with hyp[of b] obtain y where "y < b" and "\<not> P y" by auto
    from \<open>\<not> P y\<close> have "y \<in> ?A" by simp
    with b_min have "b \<le> y" by simp
    with \<open>y < b\<close> show False by simp
  qed
qed

end


subsection \<open>Type @{type poly_mapping}\<close>

lemma poly_mapping_eq_zeroI:
  assumes "keys s = {}"
  shows "s = (0::('a, 'b::zero) poly_mapping)"
proof (rule poly_mapping_eqI, simp)
  fix x
  from assms show "lookup s x = 0" by auto
qed

lemma keys_plus_ninv_comm_monoid_add: "keys (s + t) = keys s \<union> keys (t::'a \<Rightarrow>\<^sub>0 'b::ninv_comm_monoid_add)"
proof (rule, fact Poly_Mapping.keys_add, rule)
  fix x
  assume "x \<in> keys s \<union> keys t"
  thus "x \<in> keys (s + t)"
  proof
    assume "x \<in> keys s"
    thus ?thesis
      by (metis in_keys_iff lookup_add plus_eq_zero)
  next
    assume "x \<in> keys t"
    thus ?thesis
      by (metis in_keys_iff lookup_add plus_eq_zero_2)
  qed
qed

lemma lookup_zero_fun: "lookup 0 = 0"
  by (simp only: zero_poly_mapping.rep_eq zero_fun_def)

lemma lookup_plus_fun: "lookup (s + t) = lookup s + lookup t"
  by (simp only: plus_poly_mapping.rep_eq plus_fun_def)

lemma lookup_uminus_fun: "lookup (- s) = - lookup s"
  by (fact uminus_poly_mapping.rep_eq)

lemma lookup_minus_fun: "lookup (s - t) = lookup s - lookup t"
  by (simp only: minus_poly_mapping.rep_eq, rule, simp only: minus_apply)

lemma poly_mapping_adds_iff: "s adds t \<longleftrightarrow> lookup s adds lookup t"
  unfolding adds_def
proof
  assume "\<exists>k. t = s + k"
  then obtain k where *: "t = s + k" ..
  show "\<exists>k. lookup t = lookup s + k"
  proof
    from * show "lookup t = lookup s + lookup k" by (simp only: lookup_plus_fun)
  qed
next
  assume "\<exists>k. lookup t = lookup s + k"
  then obtain k where *: "lookup t = lookup s + k" ..
  have **: "k \<in> {f. finite {x. f x \<noteq> 0}}"
  proof
    have "finite {x. lookup t x \<noteq> 0}" by transfer
    hence "finite {x. lookup s x + k x \<noteq> 0}" by (simp only: * plus_fun_def)
    moreover have "finite {x. lookup s x \<noteq> 0}" by transfer
    ultimately show "finite {x. k x \<noteq> 0}" by (rule finite_neq_0_inv', simp)
  qed
  show "\<exists>k. t = s + k"
  proof
    show "t = s + Abs_poly_mapping k"
      by (rule poly_mapping_eqI, simp add: * lookup_add Abs_poly_mapping_inverse[OF **])
  qed
qed

subsubsection \<open>@{typ "('a, 'b) poly_mapping"} belongs to class @{class comm_powerprod}\<close>

instance poly_mapping :: (type, cancel_comm_monoid_add) comm_powerprod
  by standard

subsubsection \<open>@{typ "('a, 'b) poly_mapping"} belongs to class @{class ninv_comm_monoid_add}\<close>

instance poly_mapping :: (type, ninv_comm_monoid_add) ninv_comm_monoid_add
proof (standard, transfer)
  fix s t::"'a \<Rightarrow> 'b"
  assume "(\<lambda>k. s k + t k) = (\<lambda>_. 0)"
  hence "s + t = 0" by (simp only: plus_fun_def zero_fun_def)
  hence "s = 0" by (rule plus_eq_zero)
  thus "s = (\<lambda>_. 0)" by (simp only: zero_fun_def)
qed

subsubsection \<open>@{typ "('a, 'b) poly_mapping"} belongs to class @{class lcs_powerprod}\<close>

instantiation poly_mapping :: (type, add_linorder) lcs_powerprod
begin

lift_definition lcs_poly_mapping::"('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" is "\<lambda>s t. \<lambda>x. max (s x) (t x)"
proof -
  fix fun1 fun2::"'a \<Rightarrow> 'b"
  assume "finite {t. fun1 t \<noteq> 0}" and "finite {t. fun2 t \<noteq> 0}"
  from finite_neq_0'[OF this, of max] show "finite {t. max (fun1 t) (fun2 t) \<noteq> 0}"
    by (auto simp: max_def)
qed

lemma adds_poly_mappingI:
  assumes "lookup s \<le> lookup (t::'a \<Rightarrow>\<^sub>0 'b)"
  shows "s adds t"
  unfolding poly_mapping_adds_iff using assms by (rule adds_funI)

lemma lookup_lcs_fun: "lookup (lcs s t) = lcs (lookup s) (lookup (t:: 'a \<Rightarrow>\<^sub>0 'b))"
  by (simp only: lcs_poly_mapping.rep_eq lcs_fun_def)

instance
  by (standard, simp_all only: poly_mapping_adds_iff lookup_lcs_fun, rule adds_lcs, elim lcs_adds,
      assumption, rule poly_mapping_eqI, simp only: lookup_lcs_fun lcs_comm)

end

lemma adds_poly_mapping: "s adds t \<longleftrightarrow> lookup s \<le> lookup t"
  for s t::"'a \<Rightarrow>\<^sub>0 'b::add_linorder_min"
  by (simp only: poly_mapping_adds_iff adds_fun)

lemma lookup_gcs_fun: "lookup (gcs s (t::'a \<Rightarrow>\<^sub>0 ('b::add_linorder))) = gcs (lookup s) (lookup t)"
proof
  fix x
  show "lookup (gcs s t) x = gcs (lookup s) (lookup t) x"
    by (simp add: gcs_def lookup_minus lookup_add lookup_lcs_fun)
qed

subsubsection \<open>@{typ "('a, 'b) poly_mapping"} belongs to class @{class ulcs_powerprod}\<close>

instance poly_mapping :: (type, add_linorder_min) ulcs_powerprod ..

subsubsection \<open>Power-products in a given set of indeterminates.\<close>

lemma adds_except:
  "s adds t = (except s V adds except t V \<and> except s (- V) adds except t (- V))"
  for s t :: "'a \<Rightarrow>\<^sub>0 'b::add_linorder"
  by (simp add: poly_mapping_adds_iff adds_except_fun[of "lookup s", where V=V] except.rep_eq)

lemma adds_except_singleton:
  "s adds t \<longleftrightarrow> (except s {v} adds except t {v} \<and> lookup s v adds lookup t v)"
  for s t :: "'a \<Rightarrow>\<^sub>0 'b::add_linorder"
  by (simp add: poly_mapping_adds_iff adds_except_fun_singleton[of "lookup s", where v=v] except.rep_eq)

subsubsection \<open>Dickson's lemma for power-products in finitely many indeterminates\<close>

context countable
begin

definition elem_index :: "'a \<Rightarrow> nat" where "elem_index = (SOME f. inj f)"

lemma inj_elem_index: "inj elem_index"
  unfolding elem_index_def using ex_inj by (rule someI_ex)

lemma elem_index_inj:
  assumes "elem_index x = elem_index y"
  shows "x = y"
  using inj_elem_index assms by (rule injD)

lemma finite_nat_seg: "finite {x. elem_index x < n}"
proof (rule finite_imageD)
  have "elem_index ` {x. elem_index x < n} \<subseteq> {0..<n}" by auto
  moreover have "finite ..." ..
  ultimately show "finite (elem_index ` {x. elem_index x < n})" by (rule finite_subset)
next
  from inj_elem_index show "inj_on elem_index {x. elem_index x < n}" using inj_on_subset by blast
qed

end (* countable *)

lemma Dickson_poly_mapping:
  assumes "finite V"
  shows "almost_full_on (adds) {x::'a \<Rightarrow>\<^sub>0 'b::add_wellorder. keys x \<subseteq> V}"
proof (rule almost_full_onI)
  fix seq::"nat \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b"
  assume a: "\<forall>i. seq i \<in> {x::'a \<Rightarrow>\<^sub>0 'b. keys x \<subseteq> V}"
  define seq' where "seq' = (\<lambda>i. lookup (seq i))"
  from assms have "almost_full_on (adds) {x::'a \<Rightarrow> 'b. supp_fun x \<subseteq> V}" by (rule Dickson_fun)
  moreover from a have "\<And>i. seq' i \<in> {x::'a \<Rightarrow> 'b. supp_fun x \<subseteq> V}"
    by (auto simp: seq'_def keys_eq_supp)
  ultimately obtain i j where "i < j" and "seq' i adds seq' j" by (rule almost_full_onD)
  from this(2) have "seq i adds seq j" by (simp add: seq'_def poly_mapping_adds_iff)
  with \<open>i < j\<close> show "good (adds) seq" by (rule goodI)
qed

definition varnum :: "'x set \<Rightarrow> ('x::countable \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> nat"
  where "varnum X t = (if keys t - X = {} then 0 else Suc (Max (elem_index ` (keys t - X))))"

lemma elem_index_less_varnum:
  assumes "x \<in> keys t"
  obtains "x \<in> X" | "elem_index x < varnum X t"
proof (cases "x \<in> X")
  case True
  thus ?thesis ..
next
  case False
  with assms have 1: "x \<in> keys t - X" by simp
  hence "keys t - X \<noteq> {}" by blast
  hence eq: "varnum X t = Suc (Max (elem_index ` (keys t - X)))" by (simp add: varnum_def)
  hence "elem_index x < varnum X t" using 1 by (simp add: less_Suc_eq_le)
  thus ?thesis ..
qed

lemma varnum_plus:
  "varnum X (s + t) = max (varnum X s) (varnum X (t::'x::countable \<Rightarrow>\<^sub>0 'b::ninv_comm_monoid_add))"
proof (simp add: varnum_def keys_plus_ninv_comm_monoid_add image_Un Un_Diff del: Diff_eq_empty_iff, intro impI)
  assume 1: "keys s - X \<noteq> {}" and 2: "keys t - X \<noteq> {}"
  have "finite (elem_index ` (keys s - X))" by simp
  moreover from 1 have "elem_index ` (keys s - X) \<noteq> {}" by simp
  moreover have "finite (elem_index ` (keys t - X))" by simp
  moreover from 2 have "elem_index ` (keys t - X) \<noteq> {}" by simp
  ultimately show "Max (elem_index ` (keys s - X) \<union> elem_index ` (keys t - X)) =
                    max (Max (elem_index ` (keys s - X))) (Max (elem_index ` (keys t - X)))"
    by (rule Max_Un)
qed

lemma dickson_grading_varnum:
  assumes "finite X"
  shows "dickson_grading ((varnum X)::('x::countable \<Rightarrow>\<^sub>0 'b::add_wellorder) \<Rightarrow> nat)"
  using varnum_plus
proof (rule dickson_gradingI)
  fix m::nat
  let ?V = "X \<union> {x. elem_index x < m}"
  have "{t::'x \<Rightarrow>\<^sub>0 'b. varnum X t \<le> m} \<subseteq> {t. keys t \<subseteq> ?V}"
  proof (rule, simp, intro subsetI, simp)
    fix t::"'x \<Rightarrow>\<^sub>0 'b" and x::'x
    assume "varnum X t \<le> m"
    assume "x \<in> keys t"
    thus "x \<in> X \<or> elem_index x < m"
    proof (rule elem_index_less_varnum)
      assume "x \<in> X"
      thus ?thesis ..
    next
      assume "elem_index x < varnum X t"
      hence "elem_index x < m" using \<open>varnum X t \<le> m\<close> by (rule less_le_trans)
      thus ?thesis ..
    qed
  qed
  thus "almost_full_on (adds) {t::'x \<Rightarrow>\<^sub>0 'b. varnum X t \<le> m}"
  proof (rule almost_full_on_subset)
    from assms finite_nat_seg have "finite ?V" by (rule finite_UnI)
    thus "almost_full_on (adds) {t::'x \<Rightarrow>\<^sub>0 'b. keys t \<subseteq> ?V}" by (rule Dickson_poly_mapping)
  qed
qed

corollary dickson_grading_varnum_empty:
  "dickson_grading ((varnum {})::(_ \<Rightarrow>\<^sub>0 _::add_wellorder) \<Rightarrow> nat)"
  using finite.emptyI by (rule dickson_grading_varnum)

lemma varnum_le_iff: "varnum X t \<le> n \<longleftrightarrow> keys t \<subseteq> X \<union> {x. elem_index x < n}"
  by (auto simp: varnum_def Suc_le_eq)

lemma varnum_zero [simp]: "varnum X 0 = 0"
  by (simp add: varnum_def)

lemma varnum_empty_eq_zero_iff: "varnum {} t = 0 \<longleftrightarrow> t = 0"
proof
  assume "varnum {} t = 0"
  hence "keys t = {}" by (simp add: varnum_def split: if_splits)
  thus "t = 0" by (rule poly_mapping_eq_zeroI)
qed simp

instance poly_mapping :: (countable, add_wellorder) graded_dickson_powerprod
  by standard (rule, fact dickson_grading_varnum_empty)

instance poly_mapping :: (finite, add_wellorder) dickson_powerprod
proof
  have "finite (UNIV::'a set)" by simp
  hence "almost_full_on (adds) {x::'a \<Rightarrow>\<^sub>0 'b. keys x \<subseteq> UNIV}" by (rule Dickson_poly_mapping)
  thus "almost_full_on (adds) (UNIV::('a \<Rightarrow>\<^sub>0 'b) set)" by simp
qed

subsubsection \<open>Lexicographic Term Order\<close>

definition lex_pm :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a::linorder \<Rightarrow>\<^sub>0 'b::{zero,linorder}) \<Rightarrow> bool"
  where "lex_pm = (\<le>)"

definition lex_pm_strict :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a::linorder \<Rightarrow>\<^sub>0 'b::{zero,linorder}) \<Rightarrow> bool"
  where "lex_pm_strict = (<)"

lemma lex_pm_alt: "lex_pm s t = (s = t \<or> (\<exists>x. lookup s x < lookup t x \<and> (\<forall>y<x. lookup s y = lookup t y)))"
  unfolding lex_pm_def by (metis less_eq_poly_mapping.rep_eq less_funE less_funI poly_mapping_eq_iff)

lemma lex_pm_refl: "lex_pm s s"
  by (simp add: lex_pm_def)

lemma lex_pm_antisym: "lex_pm s t \<Longrightarrow> lex_pm t s \<Longrightarrow> s = t"
  by (simp add: lex_pm_def)

lemma lex_pm_trans: "lex_pm s t \<Longrightarrow> lex_pm t u \<Longrightarrow> lex_pm s u"
  by (simp add: lex_pm_def)

lemma lex_pm_lin: "lex_pm s t \<or> lex_pm t s"
  by (simp add: lex_pm_def linear)

corollary lex_pm_strict_alt [code]: "lex_pm_strict s t = (\<not> lex_pm t s)"
  by (auto simp: lex_pm_strict_def lex_pm_def)

lemma lex_pm_zero_min: "lex_pm 0 s" for s::"_ \<Rightarrow>\<^sub>0 _::add_linorder_min"
proof (rule ccontr)
  assume "\<not> lex_pm 0 s"
  hence "lex_pm_strict s 0" by (simp add: lex_pm_strict_alt)
  thus False by (simp add: lex_pm_strict_def less_poly_mapping.rep_eq less_fun_def)
qed

lemma lex_pm_plus_monotone: "lex_pm s t \<Longrightarrow> lex_pm (s + u) (t + u)"
  for s t::"_ \<Rightarrow>\<^sub>0 _::{ordered_comm_monoid_add, ordered_ab_semigroup_add_imp_le}"
  by (simp add: lex_pm_def add_right_mono)

subsubsection \<open>Degree\<close>

lift_definition deg_pm::"('a \<Rightarrow>\<^sub>0 'b::comm_monoid_add) \<Rightarrow> 'b" is deg_fun .

lemma deg_pm_zero[simp]: "deg_pm 0 = 0"
  by (simp add: deg_pm.rep_eq lookup_zero_fun)

lemma deg_pm_eq_0_iff[simp]: "deg_pm s = 0 \<longleftrightarrow> s = 0" for s::"'a \<Rightarrow>\<^sub>0 'b::add_linorder_min"
  by (simp only: deg_pm.rep_eq poly_mapping_eq_iff lookup_zero_fun, rule deg_fun_eq_0_iff,
      simp add: keys_eq_supp[symmetric])

lemma deg_pm_superset:
  assumes "keys s \<subseteq> A" and "finite A"
  shows "deg_pm s = (\<Sum>x\<in>A. lookup s x)"
  using assms by (simp only: deg_pm.rep_eq keys_eq_supp, elim deg_fun_superset)

lemma deg_pm_plus: "deg_pm (s + t) = deg_pm s + deg_pm (t::'a \<Rightarrow>\<^sub>0 'b::comm_monoid_add)"
  by (simp only: deg_pm.rep_eq lookup_plus_fun, rule deg_fun_plus, simp_all add: keys_eq_supp[symmetric])

lemma deg_pm_single: "deg_pm (Poly_Mapping.single x k) = k"
proof -
  have "keys (Poly_Mapping.single x k) \<subseteq> {x}" by simp
  moreover have "finite {x}" by simp
  ultimately have "deg_pm (Poly_Mapping.single x k) = (\<Sum>y\<in>{x}. lookup (Poly_Mapping.single x k) y)"
    by (rule deg_pm_superset)
  also have "... = k" by simp
  finally show ?thesis .
qed

subsubsection \<open>General Degree-Orders\<close>

context linorder
begin

lift_definition dord_pm::"(('a \<Rightarrow>\<^sub>0 'b::ordered_comm_monoid_add) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  is dord_fun by (metis local.dord_fun_def)

lemma dord_pm_alt: "dord_pm ord = (\<lambda>x y. deg_pm x < deg_pm y \<or> (deg_pm x = deg_pm y \<and> ord x y))"
  by (intro ext) (transfer, simp add: dord_fun_def Let_def)

lemma dord_pm_degD:
  assumes "dord_pm ord s t"
  shows "deg_pm s \<le> deg_pm t"
  using assms by (simp only: dord_pm.rep_eq deg_pm.rep_eq, elim dord_fun_degD)

lemma dord_pm_refl:
  assumes "ord s s"
  shows "dord_pm ord s s"
  using assms by (simp only: dord_pm.rep_eq, intro dord_fun_refl, simp add: lookup_inverse)

lemma dord_pm_antisym:
  assumes "ord s t \<Longrightarrow> ord t s \<Longrightarrow> s = t" and "dord_pm ord s t" and "dord_pm ord t s"
  shows "s = t"
  using assms
proof (simp only: dord_pm.rep_eq poly_mapping_eq_iff)
  assume 1: "(ord s t \<Longrightarrow> ord t s \<Longrightarrow> lookup s = lookup t)"
  assume 2: "dord_fun (map_fun Abs_poly_mapping id \<circ> ord \<circ> Abs_poly_mapping) (lookup s) (lookup t)"
  assume 3: "dord_fun (map_fun Abs_poly_mapping id \<circ> ord \<circ> Abs_poly_mapping) (lookup t) (lookup s)"
  from _ 2 3 show "lookup s = lookup t" by (rule dord_fun_antisym, simp add: lookup_inverse 1)
qed

lemma dord_pm_trans:
  assumes "ord s t \<Longrightarrow> ord t u \<Longrightarrow> ord s u" and "dord_pm ord s t" and "dord_pm ord t u"
  shows "dord_pm ord s u"
  using assms
proof (simp only: dord_pm.rep_eq poly_mapping_eq_iff)
  assume 1: "(ord s t \<Longrightarrow> ord t u \<Longrightarrow> ord s u)"
  assume 2: "dord_fun (map_fun Abs_poly_mapping id \<circ> ord \<circ> Abs_poly_mapping) (lookup s) (lookup t)"
  assume 3: "dord_fun (map_fun Abs_poly_mapping id \<circ> ord \<circ> Abs_poly_mapping) (lookup t) (lookup u)"
  from _ 2 3 show "dord_fun (map_fun Abs_poly_mapping id \<circ> ord \<circ> Abs_poly_mapping) (lookup s) (lookup u)"
    by (rule dord_fun_trans, simp add: lookup_inverse 1)
qed

lemma dord_pm_lin:
  "dord_pm ord s t \<or> dord_pm ord t s"
  if "ord s t \<or> ord t s"
  for s t::"'a \<Rightarrow>\<^sub>0 'b::{ordered_comm_monoid_add, linorder}"
  using that by (simp only: dord_pm.rep_eq, intro dord_fun_lin, simp add: lookup_inverse)

lemma dord_pm_zero_min: "dord_pm ord 0 s"
  if ord_refl: "\<And>t. ord t t"
  for s t::"'a \<Rightarrow>\<^sub>0 'b::add_linorder_min"
  using that
  by (simp only: dord_pm.rep_eq lookup_zero_fun, intro dord_fun_zero_min,
      simp add: lookup_inverse, simp add: keys_eq_supp[symmetric])

lemma dord_pm_plus_monotone:
  fixes s t u ::"'a \<Rightarrow>\<^sub>0 'b::{ordered_comm_monoid_add, ordered_ab_semigroup_add_imp_le}"
  assumes "ord s t \<Longrightarrow> ord (s + u) (t + u)" and "dord_pm ord s t"
  shows "dord_pm ord (s + u) (t + u)"
  using assms
  by (simp only: dord_pm.rep_eq lookup_plus_fun, intro dord_fun_plus_monotone,
      simp add: lookup_inverse lookup_plus_fun[symmetric],
      simp add: keys_eq_supp[symmetric],
      simp add: keys_eq_supp[symmetric],
      simp add: keys_eq_supp[symmetric],
      simp add: lookup_inverse)

end (* linorder *)

subsubsection \<open>Degree-Lexicographic Term Order\<close>

definition dlex_pm::"('a::linorder \<Rightarrow>\<^sub>0 'b::{ordered_comm_monoid_add,linorder}) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "dlex_pm \<equiv> dord_pm lex_pm"

definition "dlex_pm_strict s t \<longleftrightarrow> dlex_pm s t \<and> \<not> dlex_pm t s"

lemma dlex_pm_refl: "dlex_pm s s"
  unfolding dlex_pm_def using lex_pm_refl by (rule dord_pm_refl)

lemma dlex_pm_antisym: "dlex_pm s t \<Longrightarrow> dlex_pm t s \<Longrightarrow> s = t"
  unfolding dlex_pm_def using lex_pm_antisym by (rule dord_pm_antisym)

lemma dlex_pm_trans: "dlex_pm s t \<Longrightarrow> dlex_pm t u \<Longrightarrow> dlex_pm s u"
  unfolding dlex_pm_def using lex_pm_trans by (rule dord_pm_trans)

lemma dlex_pm_lin: "dlex_pm s t \<or> dlex_pm t s"
  unfolding dlex_pm_def using lex_pm_lin by (rule dord_pm_lin)

corollary dlex_pm_strict_alt [code]: "dlex_pm_strict s t = (\<not> dlex_pm t s)"
  unfolding dlex_pm_strict_def using dlex_pm_lin by auto

lemma dlex_pm_zero_min: "dlex_pm 0 s"
  for s t::"(_ \<Rightarrow>\<^sub>0 _::add_linorder_min)"
  unfolding dlex_pm_def using lex_pm_refl by (rule dord_pm_zero_min)

lemma dlex_pm_plus_monotone: "dlex_pm s t \<Longrightarrow> dlex_pm (s + u) (t + u)"
  for s t::"_ \<Rightarrow>\<^sub>0 _::{ordered_ab_semigroup_add_imp_le, ordered_cancel_comm_monoid_add}"
  unfolding dlex_pm_def using lex_pm_plus_monotone by (rule dord_pm_plus_monotone)

subsubsection \<open>Degree-Reverse-Lexicographic Term Order\<close>

definition drlex_pm::"('a::linorder \<Rightarrow>\<^sub>0 'b::{ordered_comm_monoid_add,linorder}) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "drlex_pm \<equiv> dord_pm (\<lambda>s t. lex_pm t s)"

definition "drlex_pm_strict s t \<longleftrightarrow> drlex_pm s t \<and> \<not> drlex_pm t s"

lemma drlex_pm_refl: "drlex_pm s s"
  unfolding drlex_pm_def using lex_pm_refl by (rule dord_pm_refl)

lemma drlex_pm_antisym: "drlex_pm s t \<Longrightarrow> drlex_pm t s \<Longrightarrow> s = t"
  unfolding drlex_pm_def using lex_pm_antisym by (rule dord_pm_antisym)

lemma drlex_pm_trans: "drlex_pm s t \<Longrightarrow> drlex_pm t u \<Longrightarrow> drlex_pm s u"
  unfolding drlex_pm_def using lex_pm_trans by (rule dord_pm_trans)

lemma drlex_pm_lin: "drlex_pm s t \<or> drlex_pm t s"
  unfolding drlex_pm_def using lex_pm_lin by (rule dord_pm_lin)

corollary drlex_pm_strict_alt [code]: "drlex_pm_strict s t = (\<not> drlex_pm t s)"
  unfolding drlex_pm_strict_def using drlex_pm_lin by auto

lemma drlex_pm_zero_min: "drlex_pm 0 s"
  for s t::"(_ \<Rightarrow>\<^sub>0 _::add_linorder_min)"
  unfolding drlex_pm_def using lex_pm_refl by (rule dord_pm_zero_min)

lemma drlex_pm_plus_monotone: "drlex_pm s t \<Longrightarrow> drlex_pm (s + u) (t + u)"
  for s t::"_ \<Rightarrow>\<^sub>0 _::{ordered_ab_semigroup_add_imp_le, ordered_cancel_comm_monoid_add}"
  unfolding drlex_pm_def using lex_pm_plus_monotone by (rule dord_pm_plus_monotone)

end (* theory *)
