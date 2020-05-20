subsection \<open>Pure pattern matching rule sets\<close>

theory Rewriting_Pterm
imports Rewriting_Pterm_Elim
begin

type_synonym prule = "name \<times> pterm"

primrec prule :: "prule \<Rightarrow> bool" where
"prule (_, rhs) \<longleftrightarrow> wellformed rhs \<and> closed rhs \<and> is_abs rhs"

lemma pruleI[intro!]: "wellformed rhs \<Longrightarrow> closed rhs \<Longrightarrow> is_abs rhs \<Longrightarrow> prule (name, rhs)"
by simp

locale prules = constants C_info "fst |`| rs" for C_info and rs :: "prule fset" +
  assumes all_rules: "fBall rs prule"
  assumes fmap: "is_fmap rs"
  assumes not_shadows: "fBall rs (\<lambda>(_, rhs). \<not> shadows_consts rhs)"
  assumes welldefined_rs: "fBall rs (\<lambda>(_, rhs). welldefined rhs)"

subsubsection \<open>Rewriting\<close>

inductive prewrite :: "prule fset \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" ("_/ \<turnstile>\<^sub>p/ _ \<longrightarrow>/ _" [50,0,50] 50) for rs where
step: "(name, rhs) |\<in>| rs \<Longrightarrow> rs \<turnstile>\<^sub>p Pconst name \<longrightarrow> rhs" |
beta: "c |\<in>| cs \<Longrightarrow> c \<turnstile> t \<rightarrow> t' \<Longrightarrow> rs \<turnstile>\<^sub>p Pabs cs $\<^sub>p t \<longrightarrow> t'" |
"fun": "rs \<turnstile>\<^sub>p t \<longrightarrow> t' \<Longrightarrow> rs \<turnstile>\<^sub>p t $\<^sub>p u \<longrightarrow> t' $\<^sub>p u" |
arg: "rs \<turnstile>\<^sub>p u \<longrightarrow> u' \<Longrightarrow> rs \<turnstile>\<^sub>p t $\<^sub>p u \<longrightarrow> t $\<^sub>p u'"

global_interpretation prewrite: rewriting "prewrite rs" for rs
by standard (auto intro: prewrite.intros simp: app_pterm_def)+

abbreviation prewrite_rt :: "prule fset \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" ("_/ \<turnstile>\<^sub>p/ _ \<longrightarrow>*/ _" [50,0,50] 50) where
"prewrite_rt rs \<equiv> (prewrite rs)\<^sup>*\<^sup>*"

subsubsection \<open>Translation from @{typ irule_set} to @{typ "prule fset"}\<close>

definition finished :: "irule_set \<Rightarrow> bool" where
"finished rs = fBall rs (\<lambda>(_, irs). arity irs = 0)"

definition translate_rhs :: "irules \<Rightarrow> pterm" where
"translate_rhs = snd \<circ> fthe_elem"

definition compile :: "irule_set \<Rightarrow> prule fset" where
"compile = fimage (map_prod id translate_rhs)"

lemma compile_heads: "fst |`| compile rs = fst |`| rs"
unfolding compile_def by simp

subsubsection \<open>Correctness of translation\<close>

lemma arity_zero_shape:
  assumes "arity_compatibles rs" "arity rs = 0" "is_fmap rs" "rs \<noteq> {||}"
  obtains t where "rs = {| ([], t) |}"
proof -
  from assms obtain ppats prhs where "(ppats, prhs) |\<in>| rs"
    by fast

  moreover {
    fix pats rhs
    assume "(pats, rhs) |\<in>| rs"
    with assms have "length pats = 0"
      by (metis arity_compatible_length)
    hence "pats = []"
      by simp
  }
  note all = this

  ultimately have proto: "([], prhs) |\<in>| rs" by auto

  have "fBall rs (\<lambda>(pats, rhs). pats = [] \<and> rhs = prhs)"
    proof safe
      fix pats rhs
      assume cur: "(pats, rhs) |\<in>| rs"
      with all show "pats = []" .
      with cur have "([], rhs) |\<in>| rs" by auto

      with proto show "rhs = prhs"
        using assms by (auto dest: is_fmapD)
    qed
  hence "fBall rs (\<lambda>r. r = ([], prhs))"
    by blast
  with assms have "rs = {| ([], prhs) |}"
    by (simp add: singleton_fset_is)
  thus thesis
    by (rule that)
qed

lemma (in irules) compile_rules:
  assumes "finished rs"
  shows "prules C_info (compile rs)"
proof
  show "is_fmap (compile rs)"
    using fmap
    unfolding compile_def map_prod_def id_apply
    by (rule is_fmap_image)
next
  show "fdisjnt (fst |`| compile rs) C"
    unfolding compile_def
    using disjnt by simp
next
  have
    "fBall (compile rs) prule"
    "fBall (compile rs) (\<lambda>(_, rhs). \<not> shadows_consts rhs)"
    "fBall (compile rs) (\<lambda>(_, rhs). welldefined rhs)"
    proof (safe del: fsubsetI)
      fix name rhs
      assume "(name, rhs) |\<in>| compile rs" (* FIXME clone of compile_correct *)
      then obtain irs where "(name, irs) |\<in>| rs" "rhs = translate_rhs irs"
        unfolding compile_def by force
      hence "is_fmap irs" "irs \<noteq> {||}" "arity irs = 0"
        using assms inner unfolding finished_def by blast+
      moreover have "arity_compatibles irs"
        using \<open>(name, irs) |\<in>| rs\<close> inner by (blast dest: fpairwiseD)
      ultimately obtain u where "irs = {| ([], u) |}"
        by (metis arity_zero_shape)
      hence "rhs = u" and u: "([], u) |\<in>| irs"
        unfolding \<open>rhs = _\<close> translate_rhs_def by simp+
      hence "abs_ish [] u"
        using inner \<open>(name, irs) |\<in>| rs\<close> by blast
      thus "is_abs rhs"
        unfolding abs_ish_def \<open>rhs = u\<close> by simp

      show "wellformed rhs"
        using u \<open>(name, irs) |\<in>| rs\<close> inner unfolding \<open>rhs = u\<close>
        by blast

      have "closed_except u {||}"
        using u inner \<open>(name, irs) |\<in>| rs\<close>
        by (metis (mono_tags, lifting) case_prod_conv fbspec freess_empty)
      thus "closed rhs"
        unfolding \<open>rhs = u\<close> .

      {
        assume "shadows_consts rhs"
        hence "shadows_consts u"
          unfolding compile_def \<open>rhs = u\<close> by simp
        moreover have "\<not> shadows_consts u"
          using inner \<open>([], u) |\<in>| irs\<close> \<open>(name, irs) |\<in>| rs\<close> by blast
        ultimately show False by blast
      }

      have "welldefined u"
        using fbspec[OF inner \<open>(name, irs) |\<in>| rs\<close>, simplified] \<open>([], u) |\<in>| irs\<close>
        by blast
      thus "welldefined rhs"
        unfolding \<open>rhs = u\<close> compile_def
        by simp
    qed
  thus
    "fBall (compile rs) prule"
    "fBall (compile rs) (\<lambda>(_, rhs). \<not> pre_constants.shadows_consts C_info (fst |`| compile rs) rhs)"
    "fBall (compile rs) (\<lambda>(_, rhs). pre_constants.welldefined C_info (fst |`| compile rs) rhs)"
    unfolding compile_heads by auto
next
  show "distinct all_constructors"
    by (fact distinct_ctr)
qed

theorem (in irules) compile_correct:
  assumes "compile rs \<turnstile>\<^sub>p t \<longrightarrow> t'" "finished rs"
  shows "rs \<turnstile>\<^sub>i t \<longrightarrow> t'"
using assms(1) proof induction
  case (step name rhs)
  then obtain irs where "rhs = translate_rhs irs" "(name, irs) |\<in>| rs"
    unfolding compile_def by force
  hence "arity_compatibles irs"
    using inner by (blast dest: fpairwiseD)

  have "is_fmap irs" "irs \<noteq> {||}" "arity irs = 0"
    using assms inner \<open>(name, irs) |\<in>| rs\<close> unfolding finished_def by blast+
  then obtain u where "irs = {| ([], u) |}"
    using \<open>arity_compatibles irs\<close>
    by (metis arity_zero_shape)

  show ?case
    unfolding \<open>rhs = _\<close>
    apply (rule irewrite.step)
      apply fact
    unfolding \<open>irs = _\<close> translate_rhs_def irewrite_step_def
    by (auto simp: const_term_def)
qed (auto intro: irewrite.intros)

theorem (in irules) compile_complete:
  assumes "rs \<turnstile>\<^sub>i t \<longrightarrow> t'" "finished rs"
  shows "compile rs \<turnstile>\<^sub>p t \<longrightarrow> t'"
using assms(1) proof induction
  case (step name irs params rhs t t')
  hence "arity_compatibles irs"
    using inner by (blast dest: fpairwiseD)

  have "is_fmap irs" "irs \<noteq> {||}" "arity irs = 0"
    using assms inner step unfolding finished_def by blast+
  then obtain u where "irs = {| ([], u) |}"
    using \<open>arity_compatibles irs\<close>
    by (metis arity_zero_shape)
  with step have "name, [], u \<turnstile>\<^sub>i t \<rightarrow> t'"
    by simp
  hence "t = Pconst name"
    unfolding irewrite_step_def
    by (cases t) (auto split: if_splits simp: const_term_def)
  hence "t' = u"
    using \<open>name, [], u \<turnstile>\<^sub>i t \<rightarrow> t'\<close>
    unfolding irewrite_step_def
    by (cases t) (auto split: if_splits simp: const_term_def)

  have "(name, t') |\<in>| compile rs"
    unfolding compile_def
    proof
      show "(name, t') = map_prod id translate_rhs (name, irs)"
        using \<open>irs = _\<close> \<open>t' = u\<close>
        by (simp add: split_beta translate_rhs_def)
    qed fact
  thus ?case
    unfolding \<open>t = _\<close>
    by (rule prewrite.step)
qed (auto intro: prewrite.intros)

export_code
  compile finished
  checking Scala

end