theory StutterEquivalence
imports Samplers

begin

section \<open>Stuttering Equivalence\<close>

text \<open>
  Stuttering equivalence of two sequences is formally defined as the equality
  of their maximally reduced versions.
\<close>

definition stutter_equiv  (infix "\<approx>" 50) where
  "\<sigma> \<approx> \<tau> \<equiv> \<natural>\<sigma> = \<natural>\<tau>"

text \<open>
  Stuttering equivalence is an equivalence relation.
\<close>

lemma stutter_equiv_refl: "\<sigma> \<approx> \<sigma>"
  unfolding stutter_equiv_def ..

lemma stutter_equiv_sym [sym]: "\<sigma> \<approx> \<tau> \<Longrightarrow> \<tau> \<approx> \<sigma>"
  unfolding stutter_equiv_def by (rule sym)

lemma stutter_equiv_trans [trans]: "\<rho> \<approx> \<sigma> \<Longrightarrow> \<sigma> \<approx> \<tau> \<Longrightarrow> \<rho> \<approx> \<tau>"
  unfolding stutter_equiv_def by simp

text \<open>
  In particular, any sequence sampled by a stuttering sampler
  is stuttering equivalent to the original one.
\<close>
lemma sampled_stutter_equiv:
  assumes "stutter_sampler f \<sigma>"
  shows "\<sigma> \<circ> f \<approx> \<sigma>"
  using assms unfolding stutter_equiv_def by (rule sample_max_sample)

lemma stutter_reduced_equivalent: "\<natural>\<sigma> \<approx> \<sigma>"
  unfolding stutter_equiv_def by (rule stutter_reduced_reduced)

text \<open>
  For proving stuttering equivalence of two sequences, it is enough
  to exhibit two arbitrary sampling functions that equalize the reductions
  of the sequences. This can be more convenient than computing the
  maximal stutter-reduced version of the sequences.
\<close>

lemma stutter_equivI:
  assumes f: "stutter_sampler f \<sigma>" and g: "stutter_sampler g \<tau>" 
      and eq: "\<sigma> \<circ> f = \<tau> \<circ> g"
  shows "\<sigma> \<approx> \<tau>"
proof -
  from f have "\<natural>\<sigma> = \<natural>(\<sigma> \<circ> f)" by (rule sample_max_sample[THEN sym])
  also from eq have "... = \<natural>(\<tau> \<circ> g)" by simp
  also from g have "... = \<natural>\<tau>" by (rule sample_max_sample)
  finally show ?thesis by (unfold stutter_equiv_def)
qed

text \<open>
  The corresponding elimination rule is easy to prove, given that the
  maximal stuttering sampling function is a stuttering sampling function.
\<close>

lemma stutter_equivE:
  assumes eq: "\<sigma> \<approx> \<tau>"
  and p: "\<And>f g. \<lbrakk> stutter_sampler f \<sigma>; stutter_sampler g \<tau>; \<sigma> \<circ> f = \<tau> \<circ> g \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof (rule p)
  from eq show "\<sigma> \<circ> (max_stutter_sampler \<sigma>) = \<tau> \<circ> (max_stutter_sampler \<tau>)"
    by (unfold stutter_equiv_def stutter_reduced_def)
qed (rule max_stutter_sampler)+

text \<open>
  Therefore we get the following alternative characterization: two
  sequences are stuttering equivalent iff there are stuttering sampling
  functions that equalize the two sequences.
\<close>
lemma stutter_equiv_eq:
  "\<sigma> \<approx> \<tau> = (\<exists>f g. stutter_sampler f \<sigma> \<and> stutter_sampler g \<tau> \<and> \<sigma> \<circ> f = \<tau> \<circ> g)"
  by (blast intro: stutter_equivI elim: stutter_equivE)

text \<open>
  The initial elements of stutter equivalent sequences are equal.
\<close>
lemma stutter_equiv_0:
  assumes "\<sigma> \<approx> \<tau>"
  shows "\<sigma> 0 = \<tau> 0"
proof -
  have "\<sigma> 0 = (\<natural>\<sigma>) 0" by (rule stutter_reduced_0[THEN sym])
  with assms[unfolded stutter_equiv_def] show ?thesis
    by (simp add: stutter_reduced_0)
qed

abbreviation suffix_notation ("_ [_..]")
where
  "suffix_notation w k \<equiv> suffix k w"

text \<open>
  Given any stuttering sampling function \<open>f\<close> for sequence \<open>\<sigma>\<close>,
  any suffix of \<open>\<sigma>\<close> starting at index \<open>f n\<close> is stuttering
  equivalent to the suffix of the stutter-reduced version of \<open>\<sigma>\<close>
  starting at \<open>n\<close>.
\<close>
lemma suffix_stutter_equiv:
  assumes f: "stutter_sampler f \<sigma>"
  shows "suffix (f n) \<sigma> \<approx> suffix n (\<sigma> \<circ> f)"
proof -
  from f have "stutter_sampler (\<lambda>k. f (n+k) - f n) (\<sigma>[f n ..])"
    by (rule stutter_sampler_suffix)
  moreover
  have "stutter_sampler id ((\<sigma> \<circ> f)[n ..])"
    by (rule id_stutter_sampler)
  moreover
  have "(\<sigma>[f n ..]) \<circ> (\<lambda>k. f (n+k) - f n) = ((\<sigma> \<circ> f)[n ..]) \<circ> id"
  proof (rule ext, auto)
    fix i
    from f[THEN stutter_sampler_mono, THEN strict_mono_mono]
    have "f n \<le> f (n+i)" by (rule monoD) simp
    thus "\<sigma> (f n + (f (n+i) - f n)) = \<sigma> (f (n+i))" by simp
  qed
  ultimately show ?thesis
    by (rule stutter_equivI)
qed

text \<open>
  Given a stuttering sampling function \<open>f\<close> and a point \<open>n\<close>
  within the interval from \<open>f k\<close> to \<open>f (k+1)\<close>, the suffix
  starting at \<open>n\<close> is stuttering equivalent to the suffix starting
  at \<open>f k\<close>.
\<close>
lemma stutter_equiv_within_interval:
  assumes f: "stutter_sampler f \<sigma>"
      and lo: "f k \<le> n" and hi: "n < f (Suc k)"
  shows "\<sigma>[n ..] \<approx> \<sigma>[f k ..]"
proof -
  have "stutter_sampler id (\<sigma>[n ..])" by (rule id_stutter_sampler)
  moreover
  from lo have "stutter_sampler (\<lambda>i. if i=0 then 0 else n + i - f k) (\<sigma>[f k ..])"
    (is "stutter_sampler ?f _")
  proof (auto simp: stutter_sampler_def strict_mono_def)
    fix i
    assume i: "i < Suc n - f k"
    from f show "\<sigma> (f k + i) = \<sigma> (f k)"
    proof (rule stutter_sampler_between)
      from i hi show "f k + i < f (Suc k)" by simp
    qed simp
  qed
  moreover
  have "(\<sigma>[n ..]) \<circ> id = (\<sigma>[f k ..]) \<circ> ?f"
  proof (rule ext, auto)
    from f lo hi show "\<sigma> n = \<sigma> (f k)" by (rule stutter_sampler_between)
  next
    fix i
    from lo show "\<sigma> (n+i) = \<sigma> (f k + (n + i - f k))" by simp
  qed
  ultimately show ?thesis by (rule stutter_equivI)
qed

text \<open>
  Given two stuttering equivalent sequences \<open>\<sigma>\<close> and \<open>\<tau>\<close>,
  we obtain a zig-zag relationship as follows: for any suffix \<open>\<tau>[n..]\<close>
  there is a suffix \<open>\<sigma>[m..]\<close> such that:
  \begin{enumerate}
  \item \<open>\<sigma>[m..] \<approx> \<tau>[n..]\<close> and
  \item for every suffix \<open>\<sigma>[j..]\<close> where \<open>j<m\<close> there is a
    corresponding suffix \<open>\<tau>[k..]\<close> for some \<open>k<n\<close>.
  \end{enumerate}
\<close>
theorem stutter_equiv_suffixes_left:
  assumes "\<sigma> \<approx> \<tau>"
  obtains m where "\<sigma>[m..] \<approx> \<tau>[n..]" and "\<forall>j<m. \<exists>k<n. \<sigma>[j..] \<approx> \<tau>[k..]"
using assms proof (rule stutter_equivE)
  fix f g
  assume f: "stutter_sampler f \<sigma>"
     and g: "stutter_sampler g \<tau>"
     and eq: "\<sigma> \<circ> f = \<tau> \<circ> g"
  from g obtain i where i: "g i \<le> n" "n < g (Suc i)"
    by (rule stutter_sampler_interval)
  with g have "\<tau>[n..] \<approx> \<tau>[g i ..]"
    by (rule stutter_equiv_within_interval)
  also from g have "... \<approx> (\<tau> \<circ> g)[i ..]"
    by (rule suffix_stutter_equiv)
  also from eq have "... = (\<sigma> \<circ> f)[i ..]"
    by simp
  also from f have "... \<approx> \<sigma>[f i ..]"
    by (rule suffix_stutter_equiv[THEN stutter_equiv_sym])
  finally have "\<sigma>[f i ..] \<approx> \<tau>[n ..]"
    by (rule stutter_equiv_sym)
  moreover
  {
    fix j
    assume j: "j < f i"
    from f obtain a where a: "f a \<le> j" "j < f (Suc a)"
      by (rule stutter_sampler_interval)
    from a j have "f a < f i" by simp
    with f[THEN stutter_sampler_mono] have "a < i"
      by (simp add: strict_mono_less)
    with g[THEN stutter_sampler_mono] have "g a < g i"
      by (simp add: strict_mono_less)
    with i have 1: "g a < n" by simp

    from f a have "\<sigma>[j..] \<approx> \<sigma>[f a ..]"
      by (rule stutter_equiv_within_interval)
    also from f have "... \<approx> (\<sigma> \<circ> f)[a ..]"
      by (rule suffix_stutter_equiv)
    also from eq have "... = (\<tau> \<circ> g)[a ..]" by simp
    also from g have "... \<approx> \<tau>[g a ..]"
      by (rule suffix_stutter_equiv[THEN stutter_equiv_sym])
    finally have "\<sigma>[j ..] \<approx> \<tau>[g a ..]" .
    with 1 have "\<exists>k<n. \<sigma>[j..] \<approx> \<tau>[k ..]" by blast
  }
  moreover
  note that
  ultimately show ?thesis by blast
qed

theorem stutter_equiv_suffixes_right:
  assumes "\<sigma> \<approx> \<tau>"
  obtains n where "\<sigma>[m..] \<approx> \<tau>[n..]" and "\<forall>j<n. \<exists>k<m. \<sigma>[k..] \<approx> \<tau>[j..]"
proof -
  from assms have "\<tau> \<approx> \<sigma>" 
    by (rule stutter_equiv_sym)
  then obtain n where "\<tau>[n..] \<approx> \<sigma>[m..]" "\<forall>j<n. \<exists>k<m. \<tau>[j..] \<approx> \<sigma>[k..]"
    by (rule stutter_equiv_suffixes_left)
  with that show ?thesis 
    by (blast dest: stutter_equiv_sym)
qed

text \<open>
  In particular, if \<open>\<sigma>\<close> and \<open>\<tau>\<close> are stutter equivalent then
  every element that occurs in one sequence also occurs in the other.
\<close>
lemma stutter_equiv_element_left:
  assumes "\<sigma> \<approx> \<tau>"
  obtains m where "\<sigma> m = \<tau> n" and "\<forall>j<m. \<exists>k<n. \<sigma> j = \<tau> k"
proof -
  from assms obtain m where "\<sigma>[m..] \<approx> \<tau>[n..]" "\<forall>j<m. \<exists>k<n. \<sigma>[j..] \<approx> \<tau>[k..]"
    by (rule stutter_equiv_suffixes_left)
  with that show ?thesis
    by (force dest: stutter_equiv_0)
qed

lemma stutter_equiv_element_right:
  assumes "\<sigma> \<approx> \<tau>"
  obtains n where "\<sigma> m = \<tau> n" and "\<forall>j<n. \<exists>k<m. \<sigma> k = \<tau> j"
proof -
  from assms obtain n where "\<sigma>[m..] \<approx> \<tau>[n..]" "\<forall>j<n. \<exists>k<m. \<sigma>[k..] \<approx> \<tau>[j..]"
    by (rule stutter_equiv_suffixes_right)
  with that show ?thesis
    by (force dest: stutter_equiv_0)
qed

end
