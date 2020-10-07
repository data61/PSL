(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Definition of Equivalence Classes\<close>

theory Equiv_Relations_on_Functions
imports
  Preliminaries
  Twelvefold_Way_Core
begin

subsection \<open>Permutation on the Domain\<close>

definition domain_permutation
where
  "domain_permutation A B = {(f, f') \<in> (A \<rightarrow>\<^sub>E B) \<times> (A \<rightarrow>\<^sub>E B). \<exists>p. p permutes A \<and> (\<forall>x \<in> A. f x = f' (p x))}"

lemma equiv_domain_permutation:
  "equiv (A \<rightarrow>\<^sub>E B) (domain_permutation A B)"
proof (rule equivI)
  show "refl_on (A \<rightarrow>\<^sub>E B) (domain_permutation A B)"
  proof (rule refl_onI)
    show "domain_permutation A B \<subseteq> (A \<rightarrow>\<^sub>E B) \<times> (A \<rightarrow>\<^sub>E B)"
      unfolding domain_permutation_def by auto
  next
    fix f
    assume "f \<in> A \<rightarrow>\<^sub>E B"
    from this show "(f, f) \<in> domain_permutation A B"
      using permutes_id unfolding domain_permutation_def by fastforce
  qed
next
  show "sym (domain_permutation A B)"
  proof (rule symI)
    fix f f'
    assume "(f, f') \<in> domain_permutation A B"
    from this obtain p where "p permutes A" and "\<forall>x\<in>A. f x = f' (p x)"
      unfolding domain_permutation_def by auto
    from \<open>(f, f') \<in> domain_permutation A B\<close> have "f \<in> A \<rightarrow>\<^sub>E B" "f' \<in> A \<rightarrow>\<^sub>E B"
      unfolding domain_permutation_def by auto
    moreover from \<open>p permutes A\<close> have "inv p permutes A"
      by (simp add: permutes_inv)
    moreover from \<open>p permutes A\<close> \<open>\<forall>x\<in>A. f x = f' (p x)\<close> have "\<forall>x\<in>A. f' x = f (inv p x)"
      using permutes_in_image permutes_inverses(1) by (metis (mono_tags, hide_lams))
    ultimately show "(f', f) \<in> domain_permutation A B"
      unfolding domain_permutation_def by auto
  qed
next
  show "trans (domain_permutation A B)"
  proof (rule transI)
    fix f f' f''
    assume "(f, f') \<in> domain_permutation A B" "(f', f'') \<in> domain_permutation A B"
    from \<open>(f, f') \<in> _\<close> obtain p where "p permutes A" and "\<forall>x\<in>A. f x = f' (p x)"
      unfolding domain_permutation_def by auto
    from \<open>(f', f'') \<in> _\<close> obtain p' where "p' permutes A" and "\<forall>x\<in>A. f' x = f'' (p' x)"
      unfolding domain_permutation_def by auto
    from \<open>(f, f') \<in> domain_permutation A B\<close> have "f \<in> A \<rightarrow>\<^sub>E B"
      unfolding domain_permutation_def by auto
    moreover from \<open>(f', f'') \<in> domain_permutation A B\<close> have "f'' \<in> A \<rightarrow>\<^sub>E B"
      unfolding domain_permutation_def by auto
    moreover from \<open>p permutes A\<close> \<open>p' permutes A\<close> have "(p' \<circ> p) permutes A"
      by (simp add: permutes_compose)
    moreover have "\<forall>x\<in>A. f x = f'' ((p' \<circ> p) x)"
      using \<open>\<forall>x\<in>A. f x = f' (p x)\<close> \<open>\<forall>x\<in>A. f' x = f'' (p' x)\<close> \<open>p permutes A\<close>
      by (simp add: permutes_in_image)
    ultimately show "(f, f'') \<in> domain_permutation A B"
      unfolding domain_permutation_def by auto
  qed
qed

subsubsection \<open>Respecting Functions\<close>

lemma inj_on_respects_domain_permutation:
  "(\<lambda>f. inj_on f A) respects domain_permutation A B"
proof (rule congruentI)
  fix f f'
  assume "(f, f') \<in> domain_permutation A B"
  from this obtain p where p: "p permutes A" "\<forall>x\<in>A. f x = f' (p x)"
    unfolding domain_permutation_def by auto
  have inv_p: "\<forall>x\<in>A. f' x = f (inv p x)"
    using p by (metis permutes_inverses(1) permutes_not_in)
  show "inj_on f A \<longleftrightarrow> inj_on f' A"
  proof
    assume "inj_on f A"
    show "inj_on f' A"
    proof (rule inj_onI)
      fix a a'
      assume "a \<in> A" "a' \<in> A" "f' a = f' a'"
      from this \<open>p permutes A\<close> have "inv p a \<in> A" "inv p a' \<in> A"
        by (simp add:  permutes_in_image permutes_inv)+
      have "f (inv p a) = f (inv p a')"
        using \<open>f' a = f' a'\<close> \<open>a \<in> A\<close> \<open>a' \<in> A\<close> inv_p by auto
      from \<open>inj_on f A\<close> this \<open>inv p a \<in> A\<close> \<open>inv p a' \<in> A\<close> have "inv p a = inv p a'"
        using inj_on_contraD by fastforce
      from this show "a = a'"
        by (metis \<open>p permutes A\<close> permutes_inverses(1))
    qed
  next
    assume "inj_on f' A"
    from this p show "inj_on f A"
      unfolding inj_on_def
      by (metis inj_on_contraD permutes_in_image permutes_inj_on)
  qed
qed

lemma image_respects_domain_permutation:
  "(\<lambda>f. f ` A) respects (domain_permutation A B)"
proof (rule congruentI)
  fix f f'
  assume "(f, f') \<in> domain_permutation A B"
  from this obtain p where p: "p permutes A" and f_eq: "\<forall>x\<in>A. f x = f' (p x)"
    unfolding domain_permutation_def by auto
  show "f ` A = f' ` A"
  proof
    from p f_eq show "f ` A \<subseteq> f' ` A"
      by (auto simp add: permutes_in_image)
  next
    from \<open>p permutes A\<close> \<open>\<forall>x\<in>A. f x = f' (p x)\<close> have "\<forall>x\<in>A. f' x = f (inv p x)"
      using permutes_in_image permutes_inverses(1) by (metis (mono_tags, hide_lams))
    from this show "f' ` A \<subseteq> f ` A"
      using \<open>p permutes A\<close> by (auto simp add: permutes_inv permutes_in_image)
  qed
qed

lemma surjective_respects_domain_permutation:
  "(\<lambda>f. f ` A = B) respects domain_permutation A B"
by (metis image_respects_domain_permutation congruentD congruentI)

lemma bij_betw_respects_domain_permutation:
  "(\<lambda>f. bij_betw f A B) respects domain_permutation A B"
proof (rule congruentI)
  fix f f'
  assume "(f, f') \<in> domain_permutation A B"
  from this obtain p where "p permutes A" and "\<forall>x\<in>A. f x = f' (p x)"
    unfolding domain_permutation_def by auto
  have "bij_betw f A B \<longleftrightarrow> bij_betw (f' o p) A B"
    using \<open>\<forall>x\<in>A. f x = f' (p x)\<close>
    by (metis (mono_tags, hide_lams) bij_betw_cong comp_apply)
  also have "... \<longleftrightarrow> bij_betw f' A B"
    using \<open>p permutes A\<close>
    by (auto intro!: bij_betw_comp_iff[symmetric] permutes_imp_bij)
  finally show "bij_betw f A B \<longleftrightarrow> bij_betw f' A B" .
qed

lemma image_mset_respects_domain_permutation:
  shows "(\<lambda>f. image_mset f (mset_set A)) respects (domain_permutation A B)"
proof (rule congruentI)
  fix f f'
  assume "(f, f') \<in> domain_permutation A B"
  from this obtain p where "p permutes A" and "\<forall>x\<in>A. f x = f' (p x)"
    unfolding domain_permutation_def by auto
  from this show "image_mset f (mset_set A) = image_mset f' (mset_set A)"
    using permutes_implies_image_mset_eq by fastforce
qed

subsection \<open>Permutation on the Range\<close>

definition range_permutation
where
  "range_permutation A B = {(f, f') \<in> (A \<rightarrow>\<^sub>E B) \<times> (A \<rightarrow>\<^sub>E B). \<exists>p. p permutes B \<and> (\<forall>x \<in> A. f x = p (f' x))}"

lemma equiv_range_permutation:
  "equiv (A \<rightarrow>\<^sub>E B) (range_permutation A B)"
proof (rule equivI)
  show "refl_on (A \<rightarrow>\<^sub>E B) (range_permutation A B)"
  proof (rule refl_onI)
    show "range_permutation A B \<subseteq> (A \<rightarrow>\<^sub>E B) \<times> (A \<rightarrow>\<^sub>E B)"
      unfolding range_permutation_def by auto
  next
    fix f
    assume "f \<in> A \<rightarrow>\<^sub>E B"
    from this show "(f, f) \<in> range_permutation A B"
      using permutes_id unfolding range_permutation_def by fastforce
  qed
next
  show "sym (range_permutation A B)"
  proof (rule symI)
    fix f f'
    assume "(f, f') \<in> range_permutation A B"
    from this obtain p where "p permutes B" and "\<forall>x\<in>A. f x = p (f' x)"
      unfolding range_permutation_def by auto
    from \<open>(f, f') \<in> range_permutation A B\<close> have "f \<in> A \<rightarrow>\<^sub>E B" "f' \<in> A \<rightarrow>\<^sub>E B"
      unfolding range_permutation_def by auto
    moreover from \<open>p permutes B\<close> have "inv p permutes B"
      by (simp add: permutes_inv)
    moreover from \<open>p permutes B\<close> \<open>\<forall>x\<in>A. f x = p (f' x)\<close> have "\<forall>x\<in>A. f' x = inv p (f x)"
      by (simp add: permutes_inverses(2))
    ultimately show "(f', f) \<in> range_permutation A B"
      unfolding range_permutation_def by auto
  qed
next
  show "trans (range_permutation A B)"
  proof (rule transI)
    fix f f' f''
    assume "(f, f') \<in> range_permutation A B" "(f', f'') \<in> range_permutation A B"
    from \<open>(f, f') \<in> _\<close> obtain p where "p permutes B" and "\<forall>x\<in>A. f x = p (f' x)"
      unfolding range_permutation_def by auto
    from \<open>(f', f'') \<in> _\<close> obtain p' where "p' permutes B" and "\<forall>x\<in>A. f' x = p' (f'' x)"
      unfolding range_permutation_def by auto
    from \<open>(f, f') \<in> range_permutation A B\<close> have "f \<in> A \<rightarrow>\<^sub>E B"
      unfolding range_permutation_def by auto
    moreover from \<open>(f', f'') \<in> range_permutation A B\<close> have "f'' \<in> A \<rightarrow>\<^sub>E B"
      unfolding range_permutation_def by auto
    moreover from \<open>p permutes B\<close> \<open>p' permutes B\<close> have "(p \<circ> p') permutes B"
      by (simp add: permutes_compose)
    moreover have "\<forall>x\<in>A. f x = (p \<circ> p') (f'' x)"
      using \<open>\<forall>x\<in>A. f x = p (f' x)\<close> \<open>\<forall>x\<in>A. f' x = p' (f'' x)\<close> by auto
    ultimately show "(f, f'') \<in> range_permutation A B"
      unfolding range_permutation_def by auto
  qed
qed

subsubsection \<open>Respecting Functions\<close>

lemma inj_on_respects_range_permutation:
  "(\<lambda>f. inj_on f A) respects range_permutation A B"
proof (rule congruentI)
  fix f f'
  assume "(f, f') \<in> range_permutation A B"
  from this obtain p where p: "p permutes B" "\<forall>x\<in>A. f x = p (f' x)"
    unfolding range_permutation_def by auto
  have inv_p: "\<forall>x\<in>A. f' x = inv p (f x)"
    using p by (simp add: permutes_inverses(2))
  show "inj_on f A \<longleftrightarrow> inj_on f' A"
  proof
    assume "inj_on f A"
    from this p show "inj_on f' A"
      unfolding inj_on_def by auto
  next
    assume "inj_on f' A"
    from this inv_p show "inj_on f A"
      unfolding inj_on_def by auto
  qed
qed

lemma surj_on_respects_range_permutation:
  "(\<lambda>f. f ` A = B) respects range_permutation A B"
proof (rule congruentI)
  fix f f'
  assume a: "(f, f') \<in> range_permutation A B"
  from this have "f \<in> A \<rightarrow>\<^sub>E B" "f' \<in> A \<rightarrow>\<^sub>E B"
    unfolding range_permutation_def by auto
  from a obtain p where p: "p permutes B" "\<forall>x\<in>A. f x = p (f' x)"
    unfolding range_permutation_def by auto
  have 1: "f ` A = (\<lambda>x. p (f' x)) ` A"
    using p by (meson image_cong)
  have 2: "inv p ` ((\<lambda>x. p (f' x)) ` A) = f' ` A"
    using p by (simp add: image_image image_inv_f_f permutes_inj)
  show "(f ` A = B) = (f' ` A = B)"
  proof
    assume "f ` A = B"
    from this 1 2 show "f' ` A = B"
      using p by (simp add: permutes_image permutes_inv)
  next
    assume "f' ` A = B"
    from this 1 2 show "f ` A = B"
      using p by (metis image_image permutes_image)
  qed
qed

lemma bij_betw_respects_range_permutation:
  "(\<lambda>f. bij_betw f A B) respects range_permutation A B"
proof (rule congruentI)
  fix f f'
  assume "(f, f') \<in> range_permutation A B"
  from this obtain p where "p permutes B" and "\<forall>x\<in>A. f x = p (f' x)"
    and "f' \<in> A \<rightarrow>\<^sub>E B"
    unfolding range_permutation_def by auto
  have "bij_betw f A B \<longleftrightarrow> bij_betw (p o f') A B"
    using \<open>\<forall>x\<in>A. f x = p (f' x)\<close>
    by (metis (mono_tags, hide_lams) bij_betw_cong comp_apply)
  also have "... \<longleftrightarrow> bij_betw f' A B"
    using \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> \<open>p permutes B\<close>
    by (auto intro!: bij_betw_comp_iff2[symmetric] permutes_imp_bij)
  finally show "bij_betw f A B \<longleftrightarrow> bij_betw f' A B" .
qed

lemma domain_partitions_respects_range_permutation:
  "(\<lambda>f. (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) respects range_permutation A B"
proof (rule congruentI)
  fix f f'
  assume "(f, f') \<in> range_permutation A B"
  from this obtain p where p: "p permutes B" "\<forall>x \<in> A. f x = p (f' x)"
    unfolding range_permutation_def by blast
  have "{} \<in> (\<lambda>b. {x \<in> A. f' x = b}) ` B \<longleftrightarrow> \<not> (\<forall>b \<in> B. \<exists>x \<in> A. f' x = b)" by auto
  also have "(\<forall>b \<in> B. \<exists>x \<in> A. f' x = b) \<longleftrightarrow> (\<forall>b \<in> B. \<exists>x \<in> A. p (f' x) = b)"
  proof
    assume "\<forall>b\<in>B. \<exists>x\<in>A. f' x = b"
    from this show "\<forall>b\<in>B. \<exists>x\<in>A. p (f' x) = b"
      using \<open>p permutes B\<close> unfolding permutes_def by metis
  next
    assume "\<forall>b\<in>B. \<exists>x\<in>A. p (f' x) = b"
    from this show "\<forall>b\<in>B. \<exists>x\<in>A. f' x = b"
      using \<open>p permutes B\<close> by (metis bij_betwE permutes_imp_bij permutes_inverses(2))
  qed
  also have "\<not> (\<forall>b\<in>B. \<exists>x\<in>A. p (f' x) = b) \<longleftrightarrow> {} \<in> (\<lambda>b. {x \<in> A. p (f' x) = b}) ` B" by auto
  finally have "{} \<in> (\<lambda>b. {x \<in> A. f' x = b}) ` B \<longleftrightarrow> {} \<in> (\<lambda>b. {x \<in> A. p (f' x) = b}) ` B" .
  moreover have "(\<lambda>b. {x \<in> A. f' x = b}) ` B = (\<lambda>b. {x \<in> A. p (f' x) = b}) ` B"
    using \<open>p permutes B\<close> permutes_implies_inv_image_on_eq by blast
  ultimately have "(\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}} = (\<lambda>b. {x \<in> A. p (f' x) = b}) ` B - {{}}" by auto
  also have "\<dots> = (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
    using \<open>\<forall>x \<in> A. f x = p (f' x)\<close> Collect_cong image_cong by auto
  finally show "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = (\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}" ..
qed

subsection \<open>Permutation on the Domain and the Range\<close>

definition domain_and_range_permutation
where
  "domain_and_range_permutation A B = {(f, f') \<in> (A \<rightarrow>\<^sub>E B) \<times> (A \<rightarrow>\<^sub>E B).
    \<exists>p\<^sub>A p\<^sub>B. p\<^sub>A permutes A \<and> p\<^sub>B permutes B \<and> (\<forall>x \<in> A. f x = p\<^sub>B (f' (p\<^sub>A x)))}"

lemma equiv_domain_and_range_permutation:
  "equiv (A \<rightarrow>\<^sub>E B) (domain_and_range_permutation A B)"
proof (rule equivI)
  show "refl_on (A \<rightarrow>\<^sub>E B) (domain_and_range_permutation A B)"
  proof (rule refl_onI)
    show "domain_and_range_permutation A B \<subseteq> (A \<rightarrow>\<^sub>E B) \<times> (A \<rightarrow>\<^sub>E B)"
      unfolding domain_and_range_permutation_def by auto
  next
    fix f
    assume "f \<in> A \<rightarrow>\<^sub>E B"
    from this show "(f, f) \<in> domain_and_range_permutation A B"
      using permutes_id[of A] permutes_id[of B]
      unfolding domain_and_range_permutation_def by fastforce
  qed
next
  show "sym (domain_and_range_permutation A B)"
  proof (rule symI)
    fix f f'
    assume "(f, f') \<in> domain_and_range_permutation A B"
    from this obtain p\<^sub>A p\<^sub>B where "p\<^sub>A permutes A" "p\<^sub>B permutes B" and "\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))"
      unfolding domain_and_range_permutation_def by auto
    from \<open>(f, f') \<in> domain_and_range_permutation A B\<close> have f: "f \<in> A \<rightarrow>\<^sub>E B" "f' \<in> A \<rightarrow>\<^sub>E B"
      unfolding domain_and_range_permutation_def by auto
    moreover from \<open>p\<^sub>A permutes A\<close> \<open>p\<^sub>B permutes B\<close> have "inv p\<^sub>A permutes A" "inv p\<^sub>B permutes B"
      by (auto simp add: permutes_inv)
    moreover from \<open>\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))\<close> have "\<forall>x\<in>A. f' x = inv p\<^sub>B (f (inv p\<^sub>A x))"
      using \<open>p\<^sub>A permutes A\<close> \<open>p\<^sub>B permutes B\<close> \<open>inv p\<^sub>A permutes A\<close> \<open>inv p\<^sub>B permutes B\<close>
      by (metis (no_types, lifting) bij_betwE bij_inv_eq_iff permutes_bij permutes_imp_bij)
    ultimately show "(f', f) \<in> domain_and_range_permutation A B"
      unfolding domain_and_range_permutation_def by auto
  qed
next
  show "trans (domain_and_range_permutation A B)"
  proof (rule transI)
    fix f f' f''
    assume "(f, f') \<in> domain_and_range_permutation A B"
    assume "(f', f'') \<in> domain_and_range_permutation A B"
    from \<open>(f, f') \<in> _\<close> obtain p\<^sub>A p\<^sub>B where
      "p\<^sub>A permutes A" "p\<^sub>B permutes B" and "\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))"
      unfolding domain_and_range_permutation_def by auto
    from \<open>(f', f'') \<in> _\<close> obtain p'\<^sub>A p'\<^sub>B where
      "p'\<^sub>A permutes A" "p'\<^sub>B permutes B" and "\<forall>x\<in>A. f' x = p'\<^sub>B (f'' (p'\<^sub>A x))"
      unfolding domain_and_range_permutation_def by auto
    from \<open>(f, f') \<in> domain_and_range_permutation A B\<close> have "f \<in> A \<rightarrow>\<^sub>E B"
      unfolding domain_and_range_permutation_def by auto
    moreover from \<open>(f', f'') \<in> domain_and_range_permutation A B\<close> have "f'' \<in> A \<rightarrow>\<^sub>E B"
      unfolding domain_and_range_permutation_def by auto
    moreover from \<open>p\<^sub>A permutes A\<close> \<open>p'\<^sub>A permutes A\<close> have "(p'\<^sub>A \<circ> p\<^sub>A) permutes A"
      by (simp add: permutes_compose)
    moreover from \<open>p\<^sub>B permutes B\<close> \<open>p'\<^sub>B permutes B\<close> have "(p\<^sub>B \<circ> p'\<^sub>B) permutes B"
      by (simp add: permutes_compose)
    moreover have "\<forall>x\<in>A. f x = (p\<^sub>B \<circ> p'\<^sub>B) (f'' ((p'\<^sub>A \<circ> p\<^sub>A) x))"
      using \<open>\<forall>x\<in>A. f' x = p'\<^sub>B (f'' (p'\<^sub>A x))\<close> \<open>\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))\<close> \<open>p\<^sub>A permutes A\<close>
      by (simp add: permutes_in_image)
    ultimately show "(f, f'') \<in> domain_and_range_permutation A B"
      unfolding domain_and_range_permutation_def by fastforce
  qed
qed

subsubsection \<open>Respecting Functions\<close>

lemma inj_on_respects_domain_and_range_permutation:
  "(\<lambda>f. inj_on f A) respects domain_and_range_permutation A B"
proof (rule congruentI)
  fix f f'
  assume "(f, f') \<in> domain_and_range_permutation A B"
  from this obtain p\<^sub>A p\<^sub>B where "p\<^sub>A permutes A" "p\<^sub>B permutes B" and "\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))"
    unfolding domain_and_range_permutation_def by auto
  from \<open>(f, f') \<in> domain_and_range_permutation A B\<close> have "f' ` A \<subseteq> B"
    unfolding domain_and_range_permutation_def by auto
  from \<open>p\<^sub>A permutes A\<close> have "p\<^sub>A ` A = A" by (auto simp add: permutes_image)
  from \<open>p\<^sub>A permutes A\<close> have "inj_on p\<^sub>A A"
    using bij_betw_imp_inj_on permutes_imp_bij by blast
  from \<open>p\<^sub>B permutes B\<close> have "inj_on p\<^sub>B B"
    using bij_betw_imp_inj_on permutes_imp_bij by blast
  show "inj_on f A \<longleftrightarrow> inj_on f' A"
  proof -
    have "inj_on f A \<longleftrightarrow> inj_on (\<lambda>x. p\<^sub>B (f' (p\<^sub>A x))) A"
      using \<open>\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))\<close> inj_on_cong comp_apply by fastforce
    have "inj_on f A \<longleftrightarrow> inj_on (p\<^sub>B o f' o p\<^sub>A) A"
      by (simp add: \<open>\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))\<close> inj_on_def)
    also have "inj_on (p\<^sub>B o f' o p\<^sub>A) A \<longleftrightarrow> inj_on (p\<^sub>B o f') A"
      using \<open>inj_on p\<^sub>A A\<close> \<open>p\<^sub>A ` A = A\<close>
      by (auto dest: inj_on_imageI intro: comp_inj_on)
    also have "inj_on (p\<^sub>B o f') A \<longleftrightarrow> inj_on f' A"
      using \<open>inj_on p\<^sub>B B\<close> \<open>f' ` A \<subseteq> B\<close>
      by (auto dest: inj_on_imageI2 intro: comp_inj_on subset_inj_on)
    finally show ?thesis .
  qed
qed

lemma surjective_respects_domain_and_range_permutation:
  "(\<lambda>f. f ` A = B) respects domain_and_range_permutation A B"
proof (rule congruentI)
  fix f f'
  assume "(f, f') \<in> domain_and_range_permutation A B"
  from this obtain p\<^sub>A p\<^sub>B where
    permutes: "p\<^sub>A permutes A" "p\<^sub>B permutes B" and "\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))"
    unfolding domain_and_range_permutation_def by auto
  from permutes have "p\<^sub>A ` A = A" "p\<^sub>B ` B = B" by (auto simp add: permutes_image)
  from \<open>p\<^sub>B permutes B\<close> have "inj p\<^sub>B" by (simp add: permutes_inj)
  show "(f ` A = B) \<longleftrightarrow> (f' ` A = B)"
  proof -
    have "f ` A = B \<longleftrightarrow> (\<lambda>x. p\<^sub>B (f' (p\<^sub>A x))) ` A = B"
      using \<open>\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))\<close> by (metis (mono_tags, lifting) image_cong)
    also have "(\<lambda>x. p\<^sub>B (f' (p\<^sub>A x))) ` A = B \<longleftrightarrow> (\<lambda>x. p\<^sub>B (f' x)) ` A = B"
      using \<open>p\<^sub>A ` A = A\<close> by (metis image_image)
    also have "(\<lambda>x. p\<^sub>B (f' x)) ` A = B \<longleftrightarrow> (f' ` A = B)"
      using \<open>p\<^sub>B ` B = B\<close> \<open>inj p\<^sub>B\<close> by (metis image_image image_inv_f_f)
    finally show ?thesis .
  qed
qed

lemma bij_betw_respects_domain_and_range_permutation:
  "(\<lambda>f. bij_betw f A B) respects domain_and_range_permutation A B"
proof (rule congruentI)
  fix f f'
  assume "(f, f') \<in> domain_and_range_permutation A B"
  from this obtain p\<^sub>A p\<^sub>B where "p\<^sub>A permutes A" "p\<^sub>B permutes B"
    and "\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))" and "f' \<in> A \<rightarrow>\<^sub>E B"
    unfolding domain_and_range_permutation_def by auto
  have "bij_betw f A B \<longleftrightarrow> bij_betw (p\<^sub>B o f' o p\<^sub>A) A B"
    using \<open>\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))\<close> bij_betw_congI by fastforce
  also have "... \<longleftrightarrow> bij_betw (p\<^sub>B o f')  A B"
    using \<open>p\<^sub>A permutes A\<close>
    by (auto intro!: bij_betw_comp_iff[symmetric] permutes_imp_bij)
  also have "... \<longleftrightarrow> bij_betw f' A B"
    using \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> \<open>p\<^sub>B permutes B\<close>
    by (auto intro!: bij_betw_comp_iff2[symmetric] permutes_imp_bij)
  finally show "bij_betw f A B \<longleftrightarrow> bij_betw f' A B" .
qed

lemma count_image_mset':
  "count (image_mset f A) x = sum (count A) {x' \<in> set_mset A. f x' = x}"
proof -
  have "count (image_mset f A) x = sum (count A) (f -` {x} \<inter> set_mset A)"
    unfolding count_image_mset ..
  also have "\<dots> = sum (count A) {x' \<in> set_mset A. f x' = x}"
  proof -
    have "(f -` {x} \<inter> set_mset A) = {x' \<in> set_mset A. f x' = x}" by blast
    from this show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma multiset_of_partition_cards_respects_domain_and_range_permutation:
  assumes "finite B"
  shows "(\<lambda>f. image_mset (\<lambda>X. card X) (mset_set (((\<lambda>b. {x \<in> A. f x = b})) ` B - {{}}))) respects domain_and_range_permutation A B"
proof (rule congruentI)
  fix f f'
  assume "(f, f') \<in> domain_and_range_permutation A B"
  from this obtain p\<^sub>A p\<^sub>B where "p\<^sub>A permutes A" "p\<^sub>B permutes B" "\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))"
    unfolding domain_and_range_permutation_def by auto
  have "(\<lambda>b. {x \<in> A. f x = b}) ` B = (\<lambda>b. {x \<in> A. p\<^sub>B (f' (p\<^sub>A x)) = b}) ` B"
    using \<open>\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))\<close> by auto
  from this have "image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})) =
    image_mset card (mset_set ((\<lambda>b. {x \<in> A. p\<^sub>B (f' (p\<^sub>A x)) = b}) ` B - {{}}))" by simp
  also have "image_mset card (mset_set ((\<lambda>b. {x \<in> A. p\<^sub>B (f' (p\<^sub>A x)) = b}) ` B - {{}})) =
    image_mset card (mset_set ((\<lambda>b. {x \<in> A. f' (p\<^sub>A x) = b}) ` B - {{}}))"
    using permutes_implies_inv_image_on_eq[OF \<open>p\<^sub>B permutes B\<close>, of A] by metis
  also have "image_mset card (mset_set ((\<lambda>b. {x \<in> A. f' (p\<^sub>A x) = b}) ` B - {{}})) =
    image_mset card (mset_set ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}))"
  proof (rule multiset_eqI)
    fix n
    have "bij_betw (\<lambda>X. p\<^sub>A ` X) {X \<in> (\<lambda>b. {x \<in> A. f' (p\<^sub>A x) = b}) ` B - {{}}. card X = n} {X \<in> (\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}. card X = n}"
    proof (rule bij_betw_byWitness)
      show "\<forall>X\<in>{X \<in> (\<lambda>b. {x \<in> A. f' (p\<^sub>A x) = b}) ` B - {{}}. card X = n}. inv p\<^sub>A ` p\<^sub>A ` X = X"
        by (meson \<open>p\<^sub>A permutes A\<close> image_inv_f_f permutes_inj)
      show "\<forall>X\<in>{X \<in> (\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}. card X = n}. p\<^sub>A ` inv p\<^sub>A ` X = X"
        by (meson \<open>p\<^sub>A permutes A\<close> image_f_inv_f permutes_surj)
      show "(\<lambda>X. p\<^sub>A ` X) ` {X \<in> (\<lambda>b. {x \<in> A. f' (p\<^sub>A x) = b}) ` B - {{}}. card X = n} \<subseteq> {X \<in> (\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}. card X = n}"
      proof -
        have "card (p\<^sub>A ` {x \<in> A. f' (p\<^sub>A x) = b}) = card {x \<in> A. f' (p\<^sub>A x) = b}" for b
        proof -
          have "inj_on p\<^sub>A {x \<in> A. f' (p\<^sub>A x) = b}"
            by (metis (no_types, lifting) \<open>p\<^sub>A permutes A\<close> injD inj_onI permutes_inj)
          from this show ?thesis by (simp add: card_image)
        qed
        moreover have "p\<^sub>A ` {x \<in> A. f' (p\<^sub>A x) = b} = {x \<in> A. f' x = b}" for b
        proof
          show "p\<^sub>A ` {x \<in> A. f' (p\<^sub>A x) = b} \<subseteq> {x \<in> A. f' x = b}"
            by (auto simp add: \<open>p\<^sub>A permutes A\<close> permutes_in_image)
          show "{x \<in> A. f' x = b} \<subseteq> p\<^sub>A ` {x \<in> A. f' (p\<^sub>A x) = b}"
          proof
            fix x
            assume "x \<in> {x \<in> A. f' x = b}"
            moreover have "p\<^sub>A (inv p\<^sub>A x) = x"
              using \<open>p\<^sub>A permutes A\<close> permutes_inverses(1) by fastforce
            moreover from \<open>x \<in> {x \<in> A. f' x = b}\<close> have "inv p\<^sub>A x \<in> A"
              by (simp add: \<open>p\<^sub>A permutes A\<close> permutes_in_image permutes_inv)
            ultimately show "x \<in> p\<^sub>A ` {x \<in> A. f' (p\<^sub>A x) = b}"
              by (auto intro: image_eqI[where x="inv p\<^sub>A x"])
          qed
        qed
        ultimately show ?thesis by auto
      qed
      show "(\<lambda>X. inv p\<^sub>A ` X) ` {X \<in> (\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}. card X = n} \<subseteq> {X \<in> (\<lambda>b. {x \<in> A. f' (p\<^sub>A x) = b}) ` B - {{}}. card X = n}"
      proof -
        have "card (inv p\<^sub>A ` {x \<in> A. f' x = b}) = card {x \<in> A. f' x = b}" for b
        proof -
          have "inj_on (inv p\<^sub>A) {x \<in> A. f' x = b}"
            by (metis (no_types, lifting) \<open>p\<^sub>A permutes A\<close> injD inj_onI permutes_surj surj_imp_inj_inv)
          from this show ?thesis by (simp add: card_image)
        qed
        moreover have "inv p\<^sub>A ` {x \<in> A. f' x = b} = {x \<in> A. f' (p\<^sub>A x) = b}" for b
        proof
          show "inv p\<^sub>A ` {x \<in> A. f' x = b} \<subseteq> {x \<in> A. f' (p\<^sub>A x) = b}"
            using \<open>p\<^sub>A permutes A\<close>
            by (auto simp add: permutes_in_image permutes_inv permutes_inverses(1))
          show "{x \<in> A. f' (p\<^sub>A x) = b} \<subseteq> inv p\<^sub>A ` {x \<in> A. f' x = b}"
          proof
            fix x
            assume "x \<in> {x \<in> A. f' (p\<^sub>A x) = b}"
            moreover have "inv p\<^sub>A (p\<^sub>A x) = x"
              by (meson \<open>p\<^sub>A permutes A\<close> permutes_inverses(2))
            moreover from \<open>x \<in> {x \<in> A. f' (p\<^sub>A x) = b}\<close> have "p\<^sub>A x \<in> A"
              by (simp add: \<open>p\<^sub>A permutes A\<close> permutes_in_image)
            ultimately show "x \<in> inv p\<^sub>A ` {x \<in> A. f' x = b}"
              by (auto intro: image_eqI[where x="p\<^sub>A x"])
          qed
        qed
        ultimately show ?thesis by auto
      qed
    qed
    from this have "card {x' \<in> (\<lambda>b. {x \<in> A. f' (p\<^sub>A x) = b}) ` B - {{}}. card x' = n} = card {x' \<in> (\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}. card x' = n}"
      by (rule bij_betw_same_card)
    from this show "count (image_mset card (mset_set ((\<lambda>b. {x \<in> A. f' (p\<^sub>A x) = b}) ` B - {{}}))) n =
      count (image_mset card (mset_set ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}))) n"
      using \<open>finite B\<close> by (simp add: count_image_mset')
  qed
  finally show "image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})) =
    image_mset card (mset_set ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}))" .
qed

end
