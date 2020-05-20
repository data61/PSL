(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Surjections from A to B\<close>

theory Twelvefold_Way_Entry3
imports
  Twelvefold_Way_Entry9
begin

lemma card_of_equiv_class:
  assumes "finite B"
  assumes "F \<in> {f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // range_permutation A B"
  shows "card F = fact (card B)"
proof -
  from \<open>F \<in> {f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // range_permutation A B\<close> obtain f where
    "f \<in> A \<rightarrow>\<^sub>E B" and "f ` A = B"
    and F_eq: "F = range_permutation A B `` {f}" using quotientE by blast
  have set_eq: "range_permutation A B `` {f} = (\<lambda>p x. if x \<in> A then p (f x) else undefined) ` {p. p permutes B}"
  proof
    show "range_permutation A B `` {f} \<subseteq> (\<lambda>p x. if x \<in> A then p (f x) else undefined) ` {p. p permutes B}"
    proof
      fix f'
      assume "f' \<in> range_permutation A B `` {f}"
      from this obtain p where "p permutes B" "\<forall>x\<in>A. f x = p (f' x)"
        unfolding range_permutation_def by auto
      from \<open>f' \<in> range_permutation A B `` {f}\<close> have "f' \<in> A \<rightarrow>\<^sub>E B"
        unfolding range_permutation_def by auto
      have "f' = (\<lambda>x. if x \<in> A then inv p (f x) else undefined)"
      proof
        fix x
        show "f' x = (if x \<in> A then inv p (f x) else undefined)"
          using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> \<open>\<forall>x\<in>A. f x = p (f' x)\<close>
            \<open>p permutes B\<close> permutes_inverses(2) by fastforce
      qed
      moreover have "inv p permutes B" using \<open>p permutes B\<close> by (simp add: permutes_inv)
      ultimately show "f' \<in> (\<lambda>p. (\<lambda>x. if x \<in> A then p (f x) else undefined)) ` {p. p permutes B}"
        by auto
    qed
  next
    show "(\<lambda>p x. if x \<in> A then p (f x) else undefined) ` {p. p permutes B} \<subseteq> range_permutation A B `` {f}"
    proof
      fix f'
      assume "f' \<in> (\<lambda>p x. if x \<in> A then p (f x) else undefined) ` {p. p permutes B}"
      from this obtain p where "p permutes B" and f'_eq: "f' = (\<lambda>x. if x \<in> A then p (f x) else undefined)" by auto
      from this have "f' \<in> A \<rightarrow>\<^sub>E B"
        using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> permutes_in_image by fastforce
      moreover have "inv p permutes B" using \<open>p permutes B\<close> by (simp add: permutes_inv)
      moreover have "\<forall>x\<in>A. f x = inv p (f' x)"
        using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> f'_eq
          \<open>p permutes B\<close> permutes_inverses(2) by fastforce
      ultimately show "f' \<in> range_permutation A B `` {f}"
        using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> unfolding range_permutation_def by auto
    qed
  qed
  have "inj_on (\<lambda>p x. if x \<in> A then p (f x) else undefined) {p. p permutes B}"
  proof (rule inj_onI)
    fix p p'
    assume "p \<in> {p. p permutes B}" "p' \<in> {p. p permutes B}"
      and eq: "(\<lambda>x. if x \<in> A then p (f x) else undefined) = (\<lambda>x. if x \<in> A then p' (f x) else undefined)"
    {
      fix x
      have "p x = p' x"
      proof cases
        assume "x \<in> B"
        from this obtain y where "y \<in> A" and "x = f y"
          using \<open>f ` A = B\<close> by blast
        from eq this have "p (f y) = p' (f y)" by meson
        from this \<open>x = f y\<close> show "p x = p' x" by simp
      next
        assume "x \<notin> B"
        from this show "p x = p' x"
          using \<open>p \<in> {p. p permutes B}\<close> \<open>p' \<in> {p. p permutes B}\<close>
          by (simp add: permutes_def)
      qed
    }
    from this show "p = p'" by auto
  qed
  have "card F = card ((\<lambda>p x. if x \<in> A then p (f x) else undefined) ` {p. p permutes B})"
    unfolding F_eq set_eq ..
  also have "\<dots> = card {p. p permutes B}"
    using \<open>inj_on (\<lambda>p x. if x \<in> A then p (f x) else undefined) {p. p permutes B}\<close>
    by (simp add: card_image)
  also have "\<dots> = fact (card B)"
    using \<open>finite B\<close> by (simp add: card_permutations)
  finally show ?thesis .
qed

lemma card_extensional_funcset_surj_on:
  assumes "finite A" "finite B"
  shows "card {f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} = fact (card B) * Stirling (card A) (card B)" (is "card ?F = _")
proof -
  have "card ?F = fact (card B) * card (?F // range_permutation A B)"
    using \<open>finite B\<close>
    by (simp only: card_equiv_class_restricted_same_size[OF equiv_range_permutation surj_on_respects_range_permutation card_of_equiv_class])
  also have "\<dots> = fact (card B) * Stirling (card A) (card B)"
    using \<open>finite A\<close> \<open>finite B\<close>
    by (simp only: card_surjective_functions_range_permutation)
  finally show ?thesis .
qed

end
