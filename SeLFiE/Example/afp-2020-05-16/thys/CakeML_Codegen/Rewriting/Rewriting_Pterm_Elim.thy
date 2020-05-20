section \<open>Higher-order term rewriting with explicit pattern matching\<close>

theory Rewriting_Pterm_Elim
imports
  Rewriting_Nterm
  "../Terms/Pterm"
begin

subsection \<open>Intermediate rule sets\<close>

type_synonym irules = "(term list \<times> pterm) fset"
type_synonym irule_set = "(name \<times> irules) fset"

locale pre_irules = constants C_info "fst |`| rs" for C_info and rs :: "irule_set"

locale irules = pre_irules +
  assumes fmap: "is_fmap rs"
  assumes nonempty: "rs \<noteq> {||}"
  assumes inner:
    "fBall rs (\<lambda>(_, irs).
      arity_compatibles irs \<and>
      is_fmap irs \<and>
      patterns_compatibles irs \<and>
      irs \<noteq> {||} \<and>
      fBall irs (\<lambda>(pats, rhs).
        linears pats \<and>
        abs_ish pats rhs \<and>
        closed_except rhs (freess pats) \<and>
        fdisjnt (freess pats) all_consts \<and>
        wellformed rhs \<and>
        \<not> shadows_consts rhs \<and>
        welldefined rhs))"

lemma (in pre_irules) irulesI:
  assumes "\<And>name irs. (name, irs) |\<in>| rs \<Longrightarrow> arity_compatibles irs"
  assumes "\<And>name irs. (name, irs) |\<in>| rs \<Longrightarrow> is_fmap irs"
  assumes "\<And>name irs. (name, irs) |\<in>| rs \<Longrightarrow> patterns_compatibles irs"
  assumes "\<And>name irs. (name, irs) |\<in>| rs \<Longrightarrow> irs \<noteq> {||}"
  assumes "\<And>name irs pats rhs. (name, irs) |\<in>| rs \<Longrightarrow> (pats, rhs) |\<in>| irs \<Longrightarrow> linears pats"
  assumes "\<And>name irs pats rhs. (name, irs) |\<in>| rs \<Longrightarrow> (pats, rhs) |\<in>| irs \<Longrightarrow> abs_ish pats rhs"
  assumes "\<And>name irs pats rhs. (name, irs) |\<in>| rs \<Longrightarrow> (pats, rhs) |\<in>| irs \<Longrightarrow> fdisjnt (freess pats) all_consts"
  assumes "\<And>name irs pats rhs. (name, irs) |\<in>| rs \<Longrightarrow> (pats, rhs) |\<in>| irs \<Longrightarrow> closed_except rhs (freess pats)"
  assumes "\<And>name irs pats rhs. (name, irs) |\<in>| rs \<Longrightarrow> (pats, rhs) |\<in>| irs \<Longrightarrow> wellformed rhs"
  assumes "\<And>name irs pats rhs. (name, irs) |\<in>| rs \<Longrightarrow> (pats, rhs) |\<in>| irs \<Longrightarrow> \<not> shadows_consts rhs"
  assumes "\<And>name irs pats rhs. (name, irs) |\<in>| rs \<Longrightarrow> (pats, rhs) |\<in>| irs \<Longrightarrow> welldefined rhs"
  assumes "is_fmap rs" "rs \<noteq> {||}"
  shows "irules C_info rs"
using assms unfolding irules_axioms_def irules_def
by (auto simp: prod_fBallI intro: pre_irules_axioms)

lemmas irulesI[intro!] = pre_irules.irulesI[unfolded pre_irules_def]

subsubsection \<open>Translation from @{typ nterm} to @{typ pterm}\<close>

fun nterm_to_pterm :: "nterm \<Rightarrow> pterm" where
"nterm_to_pterm (Nvar s) = Pvar s" |
"nterm_to_pterm (Nconst s) = Pconst s" |
"nterm_to_pterm (t\<^sub>1 $\<^sub>n t\<^sub>2) = nterm_to_pterm t\<^sub>1 $\<^sub>p nterm_to_pterm t\<^sub>2" |
"nterm_to_pterm (\<Lambda>\<^sub>n x. t) = (\<Lambda>\<^sub>p x. nterm_to_pterm t)"

lemma nterm_to_pterm_inj: "nterm_to_pterm x = nterm_to_pterm y \<Longrightarrow> x = y"
by (induction y arbitrary: x) (auto elim: nterm_to_pterm.elims)

lemma nterm_to_pterm:
  assumes "no_abs t"
  shows "nterm_to_pterm t = convert_term t"
using assms
apply induction
apply auto
by (auto simp: free_nterm_def free_pterm_def const_nterm_def const_pterm_def app_nterm_def app_pterm_def)

lemma nterm_to_pterm_frees[simp]: "frees (nterm_to_pterm t) = frees t"
by (induct t) auto

lemma closed_nterm_to_pterm[intro]: "closed_except (nterm_to_pterm t) (frees t)"
unfolding closed_except_def by simp

lemma (in constants) shadows_nterm_to_pterm[simp]: "shadows_consts (nterm_to_pterm t) = shadows_consts t"
by (induct t) (auto simp: shadows_consts_def fdisjnt_alt_def)

lemma wellformed_nterm_to_pterm[intro]: "wellformed (nterm_to_pterm t)"
by (induct t) auto

lemma consts_nterm_to_pterm[simp]: "consts (nterm_to_pterm t) = consts t"
by (induct t) auto

subsubsection \<open>Translation from @{typ crule_set} to @{typ irule_set}\<close>

definition translate_crules :: "crules \<Rightarrow> irules" where
"translate_crules = fimage (map_prod id nterm_to_pterm)"

definition compile :: "crule_set \<Rightarrow> irule_set" where
"compile = fimage (map_prod id translate_crules)"

lemma compile_heads: "fst |`| compile rs = fst |`| rs"
unfolding compile_def by simp

lemma (in crules) compile_rules: "irules C_info (compile rs)"
proof
  have "is_fmap rs"
    using fmap by simp
  thus "is_fmap (compile rs)"
    unfolding compile_def map_prod_def id_apply by (rule is_fmap_image)

  show "compile rs \<noteq> {||}"
    using nonempty unfolding compile_def by auto

  show "constants C_info (fst |`| compile rs)"
    proof
      show "fdisjnt (fst |`| compile rs) C"
        using disjnt unfolding compile_def
        by force
    next
      show "distinct all_constructors"
        by (fact distinct_ctr)
    qed

  fix name irs
  assume irs: "(name, irs) |\<in>| compile rs"
  then obtain irs' where "(name, irs') |\<in>| rs" "irs = translate_crules irs'"
    unfolding compile_def by force
  hence "arity_compatibles irs'"
    using inner by (blast dest: fpairwiseD)
  thus "arity_compatibles irs"
    unfolding \<open>irs = translate_crules irs'\<close> translate_crules_def
    by (force dest: fpairwiseD)

  have "patterns_compatibles irs'"
    using \<open>(name, irs') |\<in>| rs\<close> inner
    by (blast dest: fpairwiseD)
  thus "patterns_compatibles irs"
    unfolding \<open>irs = _\<close> translate_crules_def
    by (auto dest: fpairwiseD)

  have "is_fmap irs'"
    using \<open>(name, irs') |\<in>| rs\<close> inner by auto
  thus "is_fmap irs"
    unfolding \<open>irs = translate_crules irs'\<close> translate_crules_def map_prod_def id_apply
    by (rule is_fmap_image)

  have "irs' \<noteq> {||}"
    using \<open>(name, irs') |\<in>| rs\<close> inner by auto
  thus "irs \<noteq> {||}"
    unfolding \<open>irs = translate_crules irs'\<close> translate_crules_def by simp

  fix pats rhs
  assume "(pats, rhs) |\<in>| irs"
  then obtain rhs' where "(pats, rhs') |\<in>| irs'" "rhs = nterm_to_pterm rhs'"
    unfolding \<open>irs = translate_crules irs'\<close> translate_crules_def by force
  hence "linears pats" "pats \<noteq> []" "frees rhs' |\<subseteq>| freess pats" "\<not> shadows_consts rhs'"
    using fbspec[OF inner \<open>(name, irs') |\<in>| rs\<close>]
    by blast+

  show "linears pats" by fact
  show "closed_except rhs (freess pats)"
    unfolding \<open>rhs = nterm_to_pterm rhs'\<close>
    using \<open>frees rhs' |\<subseteq>| freess pats\<close>
    by (metis dual_order.trans closed_nterm_to_pterm closed_except_def)

  show "wellformed rhs"
    unfolding \<open>rhs = nterm_to_pterm rhs'\<close> by auto

  have "fdisjnt (freess pats) all_consts"
    using \<open>(pats, rhs') |\<in>| irs'\<close> \<open>(name, irs') |\<in>| rs\<close> inner
    by blast
  thus "fdisjnt (freess pats) (pre_constants.all_consts C_info (fst |`| compile rs))"
    unfolding compile_def by simp

  have "\<not> shadows_consts rhs"
    unfolding \<open>rhs = _\<close> using \<open>\<not> shadows_consts _\<close> by simp
  thus "\<not> pre_constants.shadows_consts C_info (fst |`| compile rs) rhs"
    unfolding compile_heads .

  show "abs_ish pats rhs"
    using \<open>pats \<noteq> []\<close> unfolding abs_ish_def by simp

  have "welldefined rhs'"
    using fbspec[OF inner \<open>(name, irs') |\<in>| rs\<close>, simplified]
    using \<open>(pats, rhs') |\<in>| irs'\<close>
    by blast

  thus "pre_constants.welldefined C_info (fst |`| compile rs) rhs"
    unfolding compile_def \<open>rhs = _\<close>
    by simp
qed

sublocale crules \<subseteq> crules_as_irules: irules C_info "compile rs"
by (fact compile_rules)

subsubsection \<open>Transformation of @{typ irule_set}\<close>

definition transform_irules :: "irules \<Rightarrow> irules" where
"transform_irules rs = (
  if arity rs = 0 then rs
  else map_prod id Pabs |`| fgroup_by (\<lambda>(pats, rhs). (butlast pats, (last pats, rhs))) rs)"

lemma arity_compatibles_transform_irules:
  assumes "arity_compatibles rs"
  shows "arity_compatibles (transform_irules rs)"
proof (cases "arity rs = 0")
  case True
  thus ?thesis
    unfolding transform_irules_def using assms by simp
next
  case False
  let ?rs' = "transform_irules rs"
  let ?f = "\<lambda>(pats, rhs). (butlast pats, (last pats, rhs))"
  let ?grp = "fgroup_by ?f rs"
  have rs': "?rs' = map_prod id Pabs |`| ?grp"
    using False unfolding transform_irules_def by simp
  show ?thesis
    proof safe
      fix pats\<^sub>1 rhs\<^sub>1 pats\<^sub>2 rhs\<^sub>2
      assume "(pats\<^sub>1, rhs\<^sub>1) |\<in>| ?rs'" "(pats\<^sub>2, rhs\<^sub>2) |\<in>| ?rs'"
      then obtain rhs\<^sub>1' rhs\<^sub>2' where "(pats\<^sub>1, rhs\<^sub>1') |\<in>| ?grp" "(pats\<^sub>2, rhs\<^sub>2') |\<in>| ?grp"
        unfolding rs' by auto
      then obtain pats\<^sub>1' pats\<^sub>2' x y \<comment> \<open>dummies\<close>
        where "fst (?f (pats\<^sub>1', x)) = pats\<^sub>1" "(pats\<^sub>1', x) |\<in>| rs"
          and "fst (?f (pats\<^sub>2', y)) = pats\<^sub>2" "(pats\<^sub>2', y) |\<in>| rs"
        by (fastforce simp: split_beta elim: fgroup_byE2)
      hence "pats\<^sub>1 = butlast pats\<^sub>1'" "pats\<^sub>2 = butlast pats\<^sub>2'" "length pats\<^sub>1' = length pats\<^sub>2'"
        using assms by (force dest: fpairwiseD)+
      thus "length pats\<^sub>1 = length pats\<^sub>2"
        by auto
    qed
qed

lemma arity_transform_irules:
  assumes "arity_compatibles rs" "rs \<noteq> {||}"
  shows "arity (transform_irules rs) = (if arity rs = 0 then 0 else arity rs - 1)"
proof (cases "arity rs = 0")
  case True
  thus ?thesis
    unfolding transform_irules_def by simp
next
  case False
  let ?f = "\<lambda>(pats, rhs). (butlast pats, (last pats, rhs))"
  let ?grp = "fgroup_by ?f rs"
  let ?rs' = "map_prod id Pabs |`| ?grp"

  have "arity ?rs' = arity rs - 1"
    proof (rule arityI)
      show "fBall ?rs' (\<lambda>(pats, _). length pats = arity rs - 1)"
        proof (rule prod_fBallI)
          fix pats rhs
          assume "(pats, rhs) |\<in>| ?rs'"
          then obtain cs where "(pats, cs) |\<in>| ?grp" "rhs = Pabs cs"
            by force
          then obtain pats' x \<comment> \<open>dummy\<close>
            where "pats = butlast pats'" "(pats', x) |\<in>| rs"
            by (fastforce simp: split_beta elim: fgroup_byE2)
          hence "length pats' = arity rs"
            using assms by (metis arity_compatible_length)
          thus "length pats = arity rs - 1"
            unfolding \<open>pats = butlast pats'\<close> using False by simp
        qed
    next
      show "?rs' \<noteq> {||}"
        using assms by (simp add: fgroup_by_nonempty)
    qed

  with False show ?thesis
    unfolding transform_irules_def by simp
qed

definition transform_irule_set :: "irule_set \<Rightarrow> irule_set" where
"transform_irule_set = fimage (map_prod id transform_irules)"

lemma transform_irule_set_heads: "fst |`| transform_irule_set rs = fst |`| rs"
unfolding transform_irule_set_def by simp

lemma (in irules) rules_transform: "irules C_info (transform_irule_set rs)"
proof
  have "is_fmap rs"
    using fmap by simp
  thus "is_fmap (transform_irule_set rs)"
    unfolding transform_irule_set_def map_prod_def id_apply by (rule is_fmap_image)

  show "transform_irule_set rs \<noteq> {||}"
    using nonempty unfolding transform_irule_set_def by auto

  show "constants C_info (fst |`| transform_irule_set rs)"
    proof
      show "fdisjnt (fst |`| transform_irule_set rs) C"
        using disjnt unfolding transform_irule_set_def
        by force
    next
      show "distinct all_constructors"
        by (fact distinct_ctr)
    qed

  fix name irs
  assume irs: "(name, irs) |\<in>| transform_irule_set rs"
  then obtain irs' where "(name, irs') |\<in>| rs" "irs = transform_irules irs'"
    unfolding transform_irule_set_def by force
  hence "arity_compatibles irs'"
    using inner by (blast dest: fpairwiseD)
  thus "arity_compatibles irs"
    unfolding \<open>irs = transform_irules irs'\<close> by (rule arity_compatibles_transform_irules)

  have "irs' \<noteq> {||}"
    using \<open>(name, irs') |\<in>| rs\<close> inner by blast
  thus "irs \<noteq> {||}"
    unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def
    by (simp add: fgroup_by_nonempty)

  let ?f = "\<lambda>(pats, rhs). (butlast pats, (last pats, rhs))"
  let ?grp = "fgroup_by ?f irs'"

  have "patterns_compatibles irs'"
    using \<open>(name, irs') |\<in>| rs\<close> inner
    by (blast dest: fpairwiseD)
  show "patterns_compatibles irs"
    proof (cases "arity irs' = 0")
      case True
      thus ?thesis
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def
        using \<open>patterns_compatibles irs'\<close> by simp
    next
      case False
      hence irs': "irs = map_prod id Pabs |`| ?grp"
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def by simp

      show ?thesis
        proof safe
          fix pats\<^sub>1 rhs\<^sub>1 pats\<^sub>2 rhs\<^sub>2
          assume "(pats\<^sub>1, rhs\<^sub>1) |\<in>| irs" "(pats\<^sub>2, rhs\<^sub>2) |\<in>| irs"
          with irs' obtain cs\<^sub>1 cs\<^sub>2 where "(pats\<^sub>1, cs\<^sub>1) |\<in>| ?grp" "(pats\<^sub>2, cs\<^sub>2) |\<in>| ?grp"
            by force
          then obtain pats\<^sub>1' pats\<^sub>2' and x y \<comment> \<open>dummies\<close>
            where "(pats\<^sub>1', x) |\<in>| irs'" "(pats\<^sub>2', y) |\<in>| irs'"
              and "pats\<^sub>1 = butlast pats\<^sub>1'" "pats\<^sub>2 = butlast pats\<^sub>2'"
            unfolding irs'
            by (fastforce elim: fgroup_byE2)
          hence "patterns_compatible pats\<^sub>1' pats\<^sub>2'"
            using \<open>patterns_compatibles irs'\<close> by (auto dest: fpairwiseD)
          thus "patterns_compatible pats\<^sub>1 pats\<^sub>2"
            unfolding \<open>pats\<^sub>1 = _\<close> \<open>pats\<^sub>2 = _\<close>
            by auto
        qed
    qed

  have "is_fmap irs'"
    using \<open>(name, irs') |\<in>| rs\<close> inner by blast
  show "is_fmap irs"
    proof (cases "arity irs' = 0")
      case True
      thus ?thesis
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def
        using \<open>is_fmap irs'\<close> by simp
    next
      case False
      hence irs': "irs = map_prod id Pabs |`| ?grp"
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def by simp

      show ?thesis
        proof
          fix pats rhs\<^sub>1 rhs\<^sub>2
          assume "(pats, rhs\<^sub>1) |\<in>| irs" "(pats, rhs\<^sub>2) |\<in>| irs"
          with irs' obtain cs\<^sub>1 cs\<^sub>2
            where "(pats, cs\<^sub>1) |\<in>| ?grp" "rhs\<^sub>1 = Pabs cs\<^sub>1"
              and "(pats, cs\<^sub>2) |\<in>| ?grp" "rhs\<^sub>2 = Pabs cs\<^sub>2"
            by force
          moreover have "is_fmap ?grp"
            by auto
          ultimately show "rhs\<^sub>1 = rhs\<^sub>2"
            by (auto dest: is_fmapD)
        qed
    qed

  fix pats rhs
  assume "(pats, rhs) |\<in>| irs"

  show "linears pats"
    proof (cases "arity irs' = 0")
      case True
      thus ?thesis
        using \<open>(pats, rhs) |\<in>| irs\<close> \<open>(name, irs') |\<in>| rs\<close> inner
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def
        by (smt fBallE split_conv)
    next
      case False
      hence irs': "irs = map_prod id Pabs |`| ?grp"
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def by simp
      then obtain cs where "(pats, cs) |\<in>| ?grp"
        using \<open>(pats, rhs) |\<in>| irs\<close> by force
      then obtain pats' x \<comment> \<open>dummy\<close>
        where "fst (?f (pats', x)) = pats" "(pats', x) |\<in>| irs'"
        by (fastforce simp: split_beta elim: fgroup_byE2)
      hence "pats = butlast pats'"
        by simp
      moreover have "linears pats'"
        using \<open>(pats', x) |\<in>| irs'\<close> \<open>(name, irs') |\<in>| rs\<close> inner
        by blast
      ultimately show ?thesis
        by auto
    qed

  have "fdisjnt (freess pats) all_consts"
    proof (cases "arity irs' = 0")
      case True
      thus ?thesis
        using \<open>(pats, rhs) |\<in>| irs\<close> \<open>(name, irs') |\<in>| rs\<close> inner
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def
        by (smt fBallE split_conv)
    next
      case False
      hence irs': "irs = map_prod id Pabs |`| ?grp"
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def by simp
      then obtain cs where "(pats, cs) |\<in>| ?grp"
        using \<open>(pats, rhs) |\<in>| irs\<close> by force
      then obtain pats' x \<comment> \<open>dummy\<close>
        where "fst (?f (pats', x)) = pats" "(pats', x) |\<in>| irs'"
        by (fastforce simp: split_beta elim: fgroup_byE2)
      hence "pats = butlast pats'"
        by simp
      moreover have "fdisjnt (freess pats') all_consts"
        using \<open>(pats', x) |\<in>| irs'\<close> \<open>(name, irs') |\<in>| rs\<close> inner by blast
      ultimately show ?thesis
        by (metis subsetI in_set_butlastD freess_subset fdisjnt_subset_left)
    qed

  thus "fdisjnt (freess pats) (pre_constants.all_consts C_info (fst |`| transform_irule_set rs))"
    unfolding transform_irule_set_def by simp

  show "closed_except rhs (freess pats)"
    proof (cases "arity irs' = 0")
      case True
      thus ?thesis
        using \<open>(pats, rhs) |\<in>| irs\<close> \<open>(name, irs') |\<in>| rs\<close> inner
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def
        by (smt fBallE split_conv)
    next
      case False
      hence irs': "irs = map_prod id Pabs |`| ?grp"
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def by simp
      then obtain cs where "(pats, cs) |\<in>| ?grp" "rhs = Pabs cs"
        using \<open>(pats, rhs) |\<in>| irs\<close> by force

      show ?thesis
        unfolding \<open>rhs = Pabs cs\<close> closed_except_simps
        proof safe
          fix pat t
          assume "(pat, t) |\<in>| cs"
          then obtain pats' where "(pats', t) |\<in>| irs'" "?f (pats', t) = (pats, (pat, t))"
            using \<open>(pats, cs) |\<in>| ?grp\<close> by auto
          hence "closed_except t (freess pats')"
            using \<open>(name, irs') |\<in>| rs\<close> inner by blast

          have "pats' \<noteq> []"
            using \<open>arity_compatibles irs'\<close> \<open>(pats', t) |\<in>| irs'\<close> False
            by (metis list.size(3) arity_compatible_length)
          hence "pats' = pats @ [pat]"
            using \<open>?f (pats', t) = (pats, (pat, t))\<close>
            by (fastforce simp: split_beta snoc_eq_iff_butlast)
          hence "freess pats |\<union>| frees pat = freess pats'"
            unfolding freess_def by auto

          thus "closed_except t (freess pats |\<union>| frees pat)"
            using \<open>closed_except t (freess pats')\<close> by simp
        qed
    qed

  show "wellformed rhs"
    proof (cases "arity irs' = 0")
      case True
      thus ?thesis
        using \<open>(pats, rhs) |\<in>| irs\<close> \<open>(name, irs') |\<in>| rs\<close> inner
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def
        by (smt fBallE split_conv)
    next
      case False
      hence irs': "irs = map_prod id Pabs |`| ?grp"
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def by simp
      then obtain cs where "(pats, cs) |\<in>| ?grp" "rhs = Pabs cs"
        using \<open>(pats, rhs) |\<in>| irs\<close> by force

      show ?thesis
        unfolding \<open>rhs = Pabs cs\<close>
        proof (rule wellformed_PabsI)
          show "cs \<noteq> {||}"
            using \<open>(pats, cs) |\<in>| ?grp\<close> \<open>irs' \<noteq> {||}\<close>
            by (meson femptyE fgroup_by_nonempty_inner)
        next
          show "is_fmap cs"
            proof
              fix pat t\<^sub>1 t\<^sub>2
              assume "(pat, t\<^sub>1) |\<in>| cs" "(pat, t\<^sub>2) |\<in>| cs"
              then obtain pats\<^sub>1' pats\<^sub>2'
                where "(pats\<^sub>1', t\<^sub>1) |\<in>| irs'" "?f (pats\<^sub>1', t\<^sub>1) = (pats, (pat, t\<^sub>1))"
                  and "(pats\<^sub>2', t\<^sub>2) |\<in>| irs'" "?f (pats\<^sub>2', t\<^sub>2) = (pats, (pat, t\<^sub>2))"
                using \<open>(pats, cs) |\<in>| ?grp\<close> by force
              moreover hence "pats\<^sub>1' \<noteq> []" "pats\<^sub>2' \<noteq> []"
                using \<open>arity_compatibles irs'\<close> False
                unfolding prod.case
                by (metis list.size(3) arity_compatible_length)+
              ultimately have "pats\<^sub>1' = pats @ [pat]" "pats\<^sub>2' = pats @ [pat]"
                unfolding split_beta fst_conv snd_conv
                by (metis prod.inject snoc_eq_iff_butlast)+
              with \<open>is_fmap irs'\<close> show "t\<^sub>1 = t\<^sub>2"
                using \<open>(pats\<^sub>1', t\<^sub>1) |\<in>| irs'\<close> \<open>(pats\<^sub>2', t\<^sub>2) |\<in>| irs'\<close>
                by (blast dest: is_fmapD)
            qed
        next
          show "pattern_compatibles cs"
            proof safe
              fix pat\<^sub>1 rhs\<^sub>1 pat\<^sub>2 rhs\<^sub>2
              assume "(pat\<^sub>1, rhs\<^sub>1) |\<in>| cs" "(pat\<^sub>2, rhs\<^sub>2) |\<in>| cs"
              then obtain pats\<^sub>1' pats\<^sub>2'
                where "(pats\<^sub>1', rhs\<^sub>1) |\<in>| irs'" "?f (pats\<^sub>1', rhs\<^sub>1) = (pats, (pat\<^sub>1, rhs\<^sub>1))"
                  and "(pats\<^sub>2', rhs\<^sub>2) |\<in>| irs'" "?f (pats\<^sub>2', rhs\<^sub>2) = (pats, (pat\<^sub>2, rhs\<^sub>2))"
                using \<open>(pats, cs) |\<in>| ?grp\<close>
                by force
              moreover hence "pats\<^sub>1' \<noteq> []" "pats\<^sub>2' \<noteq> []"
                using \<open>arity_compatibles irs'\<close> False
                unfolding prod.case
                by (metis list.size(3) arity_compatible_length)+
              ultimately have "pats\<^sub>1' = pats @ [pat\<^sub>1]" "pats\<^sub>2' = pats @ [pat\<^sub>2]"
                unfolding split_beta fst_conv snd_conv
                by (metis prod.inject snoc_eq_iff_butlast)+
              moreover have "patterns_compatible pats\<^sub>1' pats\<^sub>2'"
                using \<open>(pats\<^sub>1', rhs\<^sub>1) |\<in>| irs'\<close> \<open>(pats\<^sub>2', rhs\<^sub>2) |\<in>| irs'\<close> \<open>patterns_compatibles irs'\<close>
                by (auto dest: fpairwiseD)
              ultimately show "pattern_compatible pat\<^sub>1 pat\<^sub>2"
                by (auto elim: rev_accum_rel_snoc_eqE)
            qed
        next
          fix pat t
          assume "(pat, t) |\<in>| cs"
          then obtain pats' where "(pats', t) |\<in>| irs'" "pat = last pats'"
            using \<open>(pats, cs) |\<in>| ?grp\<close> by auto
          moreover hence "pats' \<noteq> []"
            using \<open>arity_compatibles irs'\<close> False
            by (metis list.size(3) arity_compatible_length)
          ultimately have "pat \<in> set pats'"
            by auto

          moreover have "linears pats'"
            using \<open>(pats', t) |\<in>| irs'\<close> \<open>(name, irs') |\<in>| rs\<close> inner by blast
          ultimately show "linear pat"
            by (metis linears_linear)

          show "wellformed t"
            using \<open>(pats', t) |\<in>| irs'\<close> \<open>(name, irs') |\<in>| rs\<close> inner by blast
        qed
    qed

  have "\<not> shadows_consts rhs"
    proof (cases "arity irs' = 0")
      case True
      thus ?thesis
        using \<open>(pats, rhs) |\<in>| irs\<close> \<open>(name, irs') |\<in>| rs\<close> inner
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def
        by (smt fBallE split_conv)
    next
      case False
      hence irs': "irs = map_prod id Pabs |`| ?grp"
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def by simp
      then obtain cs where "(pats, cs) |\<in>| ?grp" "rhs = Pabs cs"
        using \<open>(pats, rhs) |\<in>| irs\<close> by force

      show ?thesis
        unfolding \<open>rhs = _\<close>
        proof
          assume "shadows_consts (Pabs cs)"
          then obtain pat t where "(pat, t) |\<in>| cs" "shadows_consts t \<or> shadows_consts pat"
            by force
          then obtain pats' where "(pats', t) |\<in>| irs'" "pat = last pats'"
            using \<open>(pats, cs) |\<in>| ?grp\<close> by auto
          moreover hence "pats' \<noteq> []"
            using \<open>arity_compatibles irs'\<close> False
            by (metis list.size(3) arity_compatible_length)
          ultimately have "pat \<in> set pats'"
            by auto

          show False
            using \<open>shadows_consts t \<or> shadows_consts pat\<close>
            proof
              assume "shadows_consts t"
              thus False
                using \<open>(name, irs') |\<in>| rs\<close> \<open>(pats', t) |\<in>| irs'\<close> inner by blast
            next
              assume "shadows_consts pat"

              have "fdisjnt (freess pats') all_consts"
                using \<open>(name, irs') |\<in>| rs\<close> \<open>(pats', t) |\<in>| irs'\<close> inner by blast
              have "fdisjnt (frees pat) all_consts"
                apply (rule fdisjnt_subset_left)
                 apply (subst freess_single[symmetric])
                 apply (rule freess_subset)
                 apply simp
                 apply fact+
                done

              thus False
                using \<open>shadows_consts pat\<close>
                unfolding shadows_consts_def fdisjnt_alt_def by auto
          qed
        qed
    qed
  thus "\<not> pre_constants.shadows_consts C_info (fst |`| transform_irule_set rs) rhs"
    by (simp add: transform_irule_set_heads)

  show "abs_ish pats rhs"
    proof (cases "arity irs' = 0")
      case True
      thus ?thesis
        using \<open>(pats, rhs) |\<in>| irs\<close> \<open>(name, irs') |\<in>| rs\<close> inner
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def
        by (smt fBallE split_conv)
    next
      case False
      hence irs': "irs = map_prod id Pabs |`| ?grp"
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def by simp
      then obtain cs where "(pats, cs) |\<in>| ?grp" "rhs = Pabs cs"
        using \<open>(pats, rhs) |\<in>| irs\<close> by force
      thus ?thesis
        unfolding abs_ish_def by (simp add: is_abs_def term_cases_def)
    qed

  have "welldefined rhs"
    proof (cases "arity irs' = 0")
      case True
      hence \<open>(pats, rhs) |\<in>| irs'\<close>
        using \<open>(pats, rhs) |\<in>| irs\<close> \<open>(name, irs') |\<in>| rs\<close> inner
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def
        by (smt fBallE split_conv)
      thus ?thesis
        unfolding transform_irule_set_def
        using fbspec[OF inner \<open>(name, irs') |\<in>| rs\<close>, simplified]
        by force
    next
      case False
      hence irs': "irs = map_prod id Pabs |`| ?grp"
        unfolding \<open>irs = transform_irules irs'\<close> transform_irules_def by simp
      then obtain cs where "(pats, cs) |\<in>| ?grp" "rhs = Pabs cs"
        using \<open>(pats, rhs) |\<in>| irs\<close> by force
      show ?thesis
        unfolding \<open>rhs = _\<close>
        apply simp
        apply (rule ffUnion_least)
        unfolding ball_simps
        apply rule
        apply (rename_tac x, case_tac x, hypsubst_thin)
        apply simp
        subgoal premises prems for pat t
          proof -
            from prems obtain pats' where "(pats', t) |\<in>| irs'"
              using \<open>(pats, cs) |\<in>| ?grp\<close> by auto
            hence "welldefined t"
              using fbspec[OF inner \<open>(name, irs') |\<in>| rs\<close>, simplified]
              by blast
            thus ?thesis
              unfolding transform_irule_set_def
              by simp
          qed
        done
    qed
  thus "pre_constants.welldefined C_info (fst |`| transform_irule_set rs) rhs"
    unfolding transform_irule_set_heads .
qed


subsubsection \<open>Matching and rewriting\<close>

definition irewrite_step :: "name \<Rightarrow> term list \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm option" where
"irewrite_step name pats rhs t = map_option (subst rhs) (match (name $$ pats) t)"

abbreviation irewrite_step' :: "name \<Rightarrow> term list \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" ("_, _, _ \<turnstile>\<^sub>i/ _ \<rightarrow>/ _" [50,0,50] 50) where
"name, pats, rhs \<turnstile>\<^sub>i t \<rightarrow> u \<equiv> irewrite_step name pats rhs t = Some u"

lemma irewrite_stepI:
  assumes "match (name $$ pats) t = Some env" "subst rhs env = u"
  shows "name, pats, rhs \<turnstile>\<^sub>i t \<rightarrow> u"
using assms unfolding irewrite_step_def by simp

inductive irewrite :: "irule_set \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" ("_/ \<turnstile>\<^sub>i/ _ \<longrightarrow>/ _" [50,0,50] 50) for irs where
step: "\<lbrakk> (name, rs) |\<in>| irs; (pats, rhs) |\<in>| rs; name, pats, rhs \<turnstile>\<^sub>i t \<rightarrow> t' \<rbrakk> \<Longrightarrow> irs \<turnstile>\<^sub>i t \<longrightarrow> t'" |
beta: "\<lbrakk> c |\<in>| cs; c \<turnstile> t \<rightarrow> t' \<rbrakk> \<Longrightarrow> irs \<turnstile>\<^sub>i Pabs cs $\<^sub>p t \<longrightarrow> t'" |
"fun": "irs \<turnstile>\<^sub>i t \<longrightarrow> t' \<Longrightarrow> irs \<turnstile>\<^sub>i t $\<^sub>p u \<longrightarrow> t' $\<^sub>p u" |
arg: "irs \<turnstile>\<^sub>i u \<longrightarrow> u' \<Longrightarrow> irs \<turnstile>\<^sub>i t $\<^sub>p u \<longrightarrow> t $\<^sub>p u'"

global_interpretation irewrite: rewriting "irewrite rs" for rs
by standard (auto intro: irewrite.intros simp: app_pterm_def)+

abbreviation irewrite_rt :: "irule_set \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" ("_/ \<turnstile>\<^sub>i/ _ \<longrightarrow>*/ _" [50,0,50] 50) where
"irewrite_rt rs \<equiv> (irewrite rs)\<^sup>*\<^sup>*"

lemma (in irules) irewrite_closed:
  assumes "rs \<turnstile>\<^sub>i t \<longrightarrow> u" "closed t"
  shows "closed u"
using assms proof induction
  case (step name rs pats rhs t t')
  then obtain env where "match (name $$ pats) t = Some env" "t' = subst rhs env"
    unfolding irewrite_step_def by auto
  hence "closed_env env"
    using step by (auto intro: closed.match)

  show ?case
    unfolding \<open>t' = _\<close>
    apply (subst closed_except_def)
    apply (subst subst_frees)
     apply fact
    apply (subst match_dom)
     apply fact
    apply (subst frees_list_comb)
    apply simp
    apply (subst closed_except_def[symmetric])
    using inner step by blast
next
  case (beta c cs t t')
  then obtain pat rhs where "c = (pat, rhs)"
    by (cases c) auto
  with beta obtain env where "match pat t = Some env" "t' = subst rhs env"
    by auto
  moreover have "closed t"
    using beta unfolding closed_except_def by simp
  ultimately have "closed_env env"
    using beta by (auto intro: closed.match)

  show ?case
    unfolding \<open>t' = subst rhs env\<close>
    apply (subst closed_except_def)
    apply (subst subst_frees)
     apply fact
    apply (subst match_dom)
     apply fact
    apply simp
    apply (subst closed_except_def[symmetric])
    using inner beta \<open>c = _\<close> by (auto simp: closed_except_simps)
qed (auto simp: closed_except_def)

corollary (in irules) irewrite_rt_closed:
  assumes "rs \<turnstile>\<^sub>i t \<longrightarrow>* u" "closed t"
  shows "closed u"
using assms by induction (auto intro: irewrite_closed)

subsubsection \<open>Correctness of translation\<close>

abbreviation irelated :: "nterm \<Rightarrow> pterm \<Rightarrow> bool" ("_ \<approx>\<^sub>i _" [0,50] 50) where
"n \<approx>\<^sub>i p \<equiv> nterm_to_pterm n = p"

global_interpretation irelated: term_struct_rel_strong irelated
by standard
   (auto simp: app_pterm_def app_nterm_def const_pterm_def const_nterm_def elim: nterm_to_pterm.elims)

lemma irelated_vars: "t \<approx>\<^sub>i u \<Longrightarrow> frees t = frees u"
by auto

lemma irelated_no_abs:
  assumes "t \<approx>\<^sub>i u"
  shows "no_abs t \<longleftrightarrow> no_abs u"
using assms
apply (induction arbitrary: t)
 apply (auto elim!: nterm_to_pterm.elims)
   apply (fold const_nterm_def const_pterm_def free_nterm_def free_pterm_def app_pterm_def app_nterm_def)
by auto

lemma irelated_subst:
  assumes "t \<approx>\<^sub>i u" "irelated.P_env nenv penv"
  shows "subst t nenv \<approx>\<^sub>i subst u penv"
using assms proof (induction arbitrary: nenv penv u rule: nterm_to_pterm.induct)
  case (1 s)
  then show ?case
    by (auto elim!: fmrel_cases[where x = s])
next
  case 4
  from 4(2)[symmetric] show ?case
    apply simp
    apply (rule 4)
     apply simp
    using 4(3)
    by (simp add: fmrel_drop)
qed auto

lemma related_irewrite_step:
  assumes "name, pats, nterm_to_pterm rhs \<turnstile>\<^sub>i u \<rightarrow> u'" "t \<approx>\<^sub>i u"
  obtains t' where "unsplit_rule (name, pats, rhs) \<turnstile> t \<rightarrow> t'" "t' \<approx>\<^sub>i u'"
proof -
  let ?rhs' = "nterm_to_pterm rhs"
  let ?x = "name $$ pats"

  from assms obtain env where "match ?x u = Some env" "u' = subst ?rhs' env"
    unfolding irewrite_step_def by blast
  then obtain nenv where "match ?x t = Some nenv" "irelated.P_env nenv env"
    using assms
    by (metis Option.is_none_def not_None_eq option.rel_distinct(1) option.sel rel_option_unfold irelated.match_rel)

  show thesis
    proof
      show "unsplit_rule (name, pats, rhs) \<turnstile> t \<rightarrow> subst rhs nenv"
        using \<open>match ?x t = _\<close> by auto
    next
      show "subst rhs nenv \<approx>\<^sub>i u'"
        unfolding \<open>u' = _\<close> using \<open>irelated.P_env nenv env\<close>
        by (auto intro: irelated_subst)
    qed
qed

theorem (in nrules) compile_correct:
  assumes "compile (consts_of rs) \<turnstile>\<^sub>i u \<longrightarrow> u'" "t \<approx>\<^sub>i u" "closed t"
  obtains t' where "rs \<turnstile>\<^sub>n t \<longrightarrow> t'" "t' \<approx>\<^sub>i u'"
using assms(1-3) proof (induction arbitrary: t thesis rule: irewrite.induct)
  case (step name irs pats rhs u u')
  then obtain crs where "irs = translate_crules crs" "(name, crs) |\<in>| consts_of rs"
    unfolding compile_def by force
  moreover with step obtain rhs' where "rhs = nterm_to_pterm rhs'" "(pats, rhs') |\<in>| crs"
    unfolding translate_crules_def by force
  ultimately obtain rule where "split_rule rule = (name, (pats, rhs'))" "rule |\<in>| rs"
    unfolding consts_of_def by blast
  hence "nrule rule"
    using all_rules by blast

  obtain t' where "unsplit_rule (name, pats, rhs') \<turnstile> t \<rightarrow> t'" "t' \<approx>\<^sub>i u'"
    using \<open>name, pats, rhs \<turnstile>\<^sub>i u \<rightarrow> u'\<close> \<open>t \<approx>\<^sub>i u\<close> unfolding \<open>rhs = nterm_to_pterm rhs'\<close>
    by (elim related_irewrite_step)
  hence "rule \<turnstile> t \<rightarrow> t'"
    using \<open>nrule rule\<close> \<open>split_rule rule = (name, (pats, rhs'))\<close>
    by (metis unsplit_split)

  show ?case
    proof (rule step.prems)
      show "rs \<turnstile>\<^sub>n t \<longrightarrow> t'"
        apply (rule nrewrite.step)
         apply fact
        apply fact
        done
    next
      show "t' \<approx>\<^sub>i u'"
        by fact
    qed
next
  case (beta c cs u u')
  then obtain pat rhs where "c = (pat, rhs)" "(pat, rhs) |\<in>| cs"
    by (cases c) auto
  obtain v w where "t = v $\<^sub>n w" "v \<approx>\<^sub>i Pabs cs" "w \<approx>\<^sub>i u"
    using \<open>t \<approx>\<^sub>i Pabs cs $\<^sub>p u\<close> by (auto elim: nterm_to_pterm.elims)
  obtain x nrhs irhs where "v = (\<Lambda>\<^sub>n x. nrhs)" "cs = {| (Free x, irhs) |}" "nrhs \<approx>\<^sub>i irhs"
    using \<open>v \<approx>\<^sub>i Pabs cs\<close> by (auto elim: nterm_to_pterm.elims)
  hence "t = (\<Lambda>\<^sub>n x. nrhs) $\<^sub>n w" "\<Lambda>\<^sub>n x. nrhs \<approx>\<^sub>i \<Lambda>\<^sub>p x. irhs"
    unfolding \<open>t = v $\<^sub>n w\<close> using \<open>v \<approx>\<^sub>i Pabs cs\<close> by auto

  have "pat = Free x" "rhs = irhs"
    using \<open>cs = {| (Free x, irhs) |}\<close> \<open>(pat, rhs) |\<in>| cs\<close> by auto
  hence "(Free x, irhs) \<turnstile> u \<rightarrow> u'"
    using beta \<open>c = _\<close> by simp
  hence "u' = subst irhs (fmap_of_list [(x, u)])"
    by simp

  show ?case
    proof (rule beta.prems)
      show "rs \<turnstile>\<^sub>n t \<longrightarrow> subst nrhs (fmap_of_list [(x, w)])"
        unfolding \<open>t = (\<Lambda>\<^sub>n x. nrhs) $\<^sub>n w\<close>
        by (rule nrewrite.beta)
    next
      show "subst nrhs (fmap_of_list [(x, w)]) \<approx>\<^sub>i u'"
        unfolding \<open>u' = subst irhs _\<close>
        apply (rule irelated_subst)
         apply fact
        apply simp
        apply rule
         apply rule
        apply fact
        done
    qed
next
  case ("fun" v v' u)
  obtain w x where "t = w $\<^sub>n x" "w \<approx>\<^sub>i v" "x \<approx>\<^sub>i u"
    using \<open>t \<approx>\<^sub>i v $\<^sub>p u\<close> by (auto elim: nterm_to_pterm.elims)
  with "fun" obtain w' where "rs \<turnstile>\<^sub>n w \<longrightarrow> w'" "w' \<approx>\<^sub>i v'"
    unfolding closed_except_def by auto

  show ?case
    proof (rule fun.prems)
      show "rs \<turnstile>\<^sub>n t \<longrightarrow> w' $\<^sub>n x"
        unfolding \<open>t = w $\<^sub>n x\<close>
        by (rule nrewrite.fun) fact
    next
      show "w' $\<^sub>n x \<approx>\<^sub>i v' $\<^sub>p u"
        by auto fact+
    qed
next
  case (arg u u' v)
  obtain w x where "t = w $\<^sub>n x" "w \<approx>\<^sub>i v" "x \<approx>\<^sub>i u"
    using \<open> t \<approx>\<^sub>i v $\<^sub>p u\<close> by (auto elim: nterm_to_pterm.elims)
  with arg obtain x' where "rs \<turnstile>\<^sub>n x \<longrightarrow> x'" "x' \<approx>\<^sub>i u'"
    unfolding closed_except_def by auto

  show ?case
    proof (rule arg.prems)
      show "rs \<turnstile>\<^sub>n t \<longrightarrow> w $\<^sub>n x'"
        unfolding \<open>t = w $\<^sub>n x\<close>
        by (rule nrewrite.arg) fact
    next
      show "w $\<^sub>n x' \<approx>\<^sub>i v $\<^sub>p u'"
        by auto fact+
    qed
qed

corollary (in nrules) compile_correct_rt:
  assumes "compile (consts_of rs) \<turnstile>\<^sub>i u \<longrightarrow>* u'" "t \<approx>\<^sub>i u" "closed t"
  obtains t' where "rs \<turnstile>\<^sub>n t \<longrightarrow>* t'" "t' \<approx>\<^sub>i u'"
using assms proof (induction arbitrary: thesis t) (* FIXME clone of transform_correct_rt, maybe locale? *)
  case (step u' u'')

  obtain t' where "rs \<turnstile>\<^sub>n t \<longrightarrow>* t'" "t' \<approx>\<^sub>i u'"
    using step by blast

  obtain t'' where "rs \<turnstile>\<^sub>n t' \<longrightarrow>* t''" "t'' \<approx>\<^sub>i u''"
    proof (rule compile_correct)
      show "compile (consts_of rs) \<turnstile>\<^sub>i u' \<longrightarrow> u''" "t' \<approx>\<^sub>i u'"
        by fact+
    next
      show "closed t'"
        using \<open>rs \<turnstile>\<^sub>n t \<longrightarrow>* t'\<close> \<open>closed t\<close>
        by (rule nrewrite_rt_closed)
    qed blast

  show ?case
    proof (rule step.prems)
      show "rs \<turnstile>\<^sub>n t \<longrightarrow>* t''"
        using \<open>rs \<turnstile>\<^sub>n t \<longrightarrow>* t'\<close> \<open>rs \<turnstile>\<^sub>n t' \<longrightarrow>* t''\<close> by auto
    qed fact
qed blast

subsubsection \<open>Completeness of translation\<close>

lemma (in nrules) compile_complete:
  assumes "rs \<turnstile>\<^sub>n t \<longrightarrow> t'" "closed t"
  shows "compile (consts_of rs) \<turnstile>\<^sub>i nterm_to_pterm t \<longrightarrow> nterm_to_pterm t'"
  using assms proof induction
  case (step r t t')
  then obtain pat rhs' where "r = (pat, rhs')"
    by force
  then have "(pat, rhs') |\<in>| rs" "(pat, rhs') \<turnstile> t \<rightarrow> t'"
    using step by blast+
  then have "nrule (pat, rhs')"
    using all_rules by blast
  then obtain name pats where "(name, (pats, rhs')) = split_rule r" "pat = name $$ pats"
    unfolding split_rule_def \<open>r = _\<close>
    apply atomize_elim
    by (auto simp: split_beta)

  obtain crs where "(name, crs) |\<in>| consts_of rs" "(pats, rhs') |\<in>| crs"
    using step \<open>_ = split_rule r\<close> \<open>r = _\<close>
    by (metis consts_of_def fgroup_by_complete fst_conv snd_conv)
  then obtain irs where "irs = translate_crules crs"
    by blast
  then have "(name, irs) |\<in>| compile (consts_of rs)"
    unfolding compile_def
    using \<open>(name, _) |\<in>| _\<close>
    by (metis fimageI id_def map_prod_simp)
  obtain rhs where "rhs = nterm_to_pterm rhs'" "(pats, rhs) |\<in>| irs"
    using \<open>irs = _\<close> \<open>_ |\<in>| crs\<close>
    unfolding translate_crules_def
    by (metis fimageI id_def map_prod_simp)

  from step obtain env' where "match pat t = Some env'" "t' = subst rhs' env'"
    unfolding \<open>r = _\<close> using rewrite_step.simps
    by force
  then obtain env where "match pat (nterm_to_pterm t) = Some env" "irelated.P_env env' env"
    by (metis irelated.match_rel option_rel_Some1)
  then have "subst rhs env = nterm_to_pterm t'"
    unfolding \<open>t' = _\<close>
    apply -
    apply (rule sym)
    apply (rule irelated_subst)
    unfolding \<open>rhs = _\<close>
    by auto

  have "name, pats, rhs \<turnstile>\<^sub>i nterm_to_pterm t \<rightarrow> nterm_to_pterm t'"
    apply (rule irewrite_stepI)
    using \<open>match _ _ = Some env\<close> unfolding \<open>pat = _\<close>
     apply assumption
    by fact

  show ?case
    by rule fact+
next
  case (beta x t t')
  obtain c where "c = (Free x, nterm_to_pterm t)"
    by blast
  from beta have "closed (nterm_to_pterm t')"
    using closed_nterm_to_pterm[where t = t']
    unfolding closed_except_def
    by auto
  show ?case
    apply simp
    apply rule
    using \<open>c = _\<close>
    by (fastforce intro: irelated_subst[THEN sym])+
next
  case ("fun" t t' u)
  show ?case
    apply simp
    apply rule
    apply (rule "fun")
    using "fun"
    unfolding closed_except_def
    apply simp
    done
next
  case (arg u u' t)
  show ?case
    apply simp
    apply rule
    apply (rule arg)
    using arg
    unfolding closed_except_def
    by simp
qed


subsubsection \<open>Correctness of transformation\<close>

abbreviation irules_deferred_matches :: "pterm list \<Rightarrow> irules \<Rightarrow> (term \<times> pterm) fset" where
"irules_deferred_matches args \<equiv> fselect
  (\<lambda>(pats, rhs). map_option (\<lambda>env. (last pats, subst rhs env)) (matchs (butlast pats) args))"

context irules begin

inductive prelated :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" ("_ \<approx>\<^sub>p _" [0,50] 50) where
const: "Pconst x \<approx>\<^sub>p Pconst x" |
var: "Pvar x \<approx>\<^sub>p Pvar x" |
app: "t\<^sub>1 \<approx>\<^sub>p u\<^sub>1 \<Longrightarrow> t\<^sub>2 \<approx>\<^sub>p u\<^sub>2 \<Longrightarrow> t\<^sub>1 $\<^sub>p t\<^sub>2 \<approx>\<^sub>p u\<^sub>1 $\<^sub>p u\<^sub>2" |
pat: "rel_fset (rel_prod (=) prelated) cs\<^sub>1 cs\<^sub>2 \<Longrightarrow> Pabs cs\<^sub>1 \<approx>\<^sub>p Pabs cs\<^sub>2" |
"defer":
  "(name, rsi) |\<in>| rs \<Longrightarrow> 0 < arity rsi \<Longrightarrow>
   rel_fset (rel_prod (=) prelated) (irules_deferred_matches args rsi) cs \<Longrightarrow>
   list_all closed args \<Longrightarrow>
   name $$ args \<approx>\<^sub>p Pabs cs"

inductive_cases prelated_absE[consumes 1, case_names pat "defer"]: "t \<approx>\<^sub>p Pabs cs"

lemma prelated_refl[intro!]: "t \<approx>\<^sub>p t"
proof (induction t)
  case Pabs
  thus ?case
    by (auto simp: snds.simps fmember.rep_eq intro!: prelated.pat rel_fset_refl_strong rel_prod.intros)
qed (auto intro: prelated.intros)

sublocale prelated: term_struct_rel prelated
by standard (auto simp: const_pterm_def app_pterm_def intro: prelated.intros elim: prelated.cases)

lemma prelated_pvars:
  assumes "t \<approx>\<^sub>p u"
  shows "frees t = frees u"
using assms proof (induction rule: prelated.induct)
  case (pat cs\<^sub>1 cs\<^sub>2)
  show ?case
    apply simp
    apply (rule arg_cong[where f = ffUnion])
    apply (rule rel_fset_image_eq)
     apply fact
    apply auto
    done
next
  case ("defer" name rsi args cs)

  {
    fix pat t
    assume "(pat, t) |\<in>| cs"
    with "defer" obtain t'
      where "(pat, t') |\<in>| irules_deferred_matches args rsi" "frees t = frees t'"
      by (auto elim: rel_fsetE2)
    then obtain pats rhs env
      where "pat = last pats" "(pats, rhs) |\<in>| rsi"
        and "matchs (butlast pats) args = Some env" "t' = subst rhs env"
      by auto

    have "closed_except rhs (freess pats)" "linears pats"
      using \<open>(pats, rhs) |\<in>| rsi\<close> \<open>(name, rsi) |\<in>| rs\<close> inner by blast+

    have "arity_compatibles rsi"
      using "defer" inner by (blast dest: fpairwiseD)
    have "length pats > 0"
      by (subst arity_compatible_length) fact+
    hence "pats = butlast pats @ [last pats]"
      by simp

    note \<open>frees t = frees t'\<close>
    also have "frees t' = frees rhs - fmdom env"
      unfolding \<open>t' = _\<close>
      apply (rule subst_frees)
      apply (rule closed.matchs)
       apply fact+
      done
    also have "\<dots> = frees rhs - freess (butlast pats)"
      using \<open>matchs _ _ = _\<close> by (metis matchs_dom)
    also have "\<dots> |\<subseteq>| freess pats - freess (butlast pats)"
      using \<open>closed_except _ _\<close>
      by (auto simp: closed_except_def)
    also have "\<dots> = frees (last pats) |-| freess (butlast pats)"
      by (subst \<open>pats = _\<close>) (simp add: funion_fminus)
    also have "\<dots> = frees (last pats)"
      proof (rule fminus_triv)
        have "fdisjnt (freess (butlast pats)) (freess [last pats])"
          using \<open>linears pats\<close> \<open>pats = _\<close>
          by (metis linears_appendD)
        thus "frees (last pats) |\<inter>| freess (butlast pats) = {||}"
          by (fastforce simp: fdisjnt_alt_def)
      qed
    also have "\<dots> = frees pat" unfolding \<open>pat = _\<close> ..
    finally have "frees t |\<subseteq>| frees pat" .
  }
  hence "closed (Pabs cs)"
    unfolding closed_except_simps
    by (auto simp: closed_except_def)
  moreover have "closed (name $$ args)"
    unfolding closed_list_comb by fact
  ultimately show ?case
    unfolding closed_except_def by simp
qed auto

corollary prelated_closed: "t \<approx>\<^sub>p u \<Longrightarrow> closed t \<longleftrightarrow> closed u"
unfolding closed_except_def
by (auto simp: prelated_pvars)

lemma prelated_no_abs_right:
  assumes "t \<approx>\<^sub>p u" "no_abs u"
  shows "t = u"
using assms
apply (induction rule: prelated.induct)
    apply auto
 apply (fold app_pterm_def)
 apply auto
done

corollary env_prelated_refl[intro!]: "prelated.P_env env env"
by (auto intro: fmap.rel_refl)

text \<open>
  The following, more general statement does not hold:
    @{prop "t \<approx>\<^sub>p u \<Longrightarrow> rel_option prelated.P_env (match x t) (match x u)"}
  If @{text t} and @{text u} are related because of the @{thm [source=true] prelated.defer} rule,
  they have completely different shapes.
  Establishing @{prop "is_abs t \<longleftrightarrow> is_abs u"} as a precondition would rule out this case, but at
  the same time be too restrictive.

  Instead, we use @{thm prelated.related_match}.
\<close>

lemma prelated_subst:
  assumes "t\<^sub>1 \<approx>\<^sub>p t\<^sub>2" "prelated.P_env env\<^sub>1 env\<^sub>2"
  shows "subst t\<^sub>1 env\<^sub>1 \<approx>\<^sub>p subst t\<^sub>2 env\<^sub>2"
using assms proof (induction arbitrary: env\<^sub>1 env\<^sub>2 rule: prelated.induct)
  case (var x)
  thus ?case
    proof (cases rule: fmrel_cases[where x = x])
      case none
      thus ?thesis
        by (auto intro: prelated.var)
    next
      case (some t u)
      thus ?thesis
        by simp
    qed
next
  case (pat cs\<^sub>1 cs\<^sub>2)
  let ?drop = "\<lambda>env. \<lambda>(pat::term). fmdrop_fset (frees pat) env"
  from pat have "prelated.P_env (?drop env\<^sub>1 pat) (?drop env\<^sub>2 pat)" for pat
    by blast
  with pat show ?case
    by (auto intro!: prelated.pat rel_fset_image)
next
  case ("defer" name rsi args cs)
  have "name $$ args \<approx>\<^sub>p Pabs cs"
    apply (rule prelated.defer)
       apply fact+
     apply (rule fset.rel_mono_strong)
      apply fact
     apply force
    apply fact
    done
  moreover have "closed (name $$ args)"
    unfolding closed_list_comb by fact
  ultimately have "closed (Pabs cs)"
    by (metis prelated_closed)

  let ?drop = "\<lambda>env. \<lambda>pat. fmdrop_fset (frees pat) env"
  let ?f = "\<lambda>env. (\<lambda>(pat, rhs). (pat, subst rhs (?drop env pat)))"

  have "name $$ args \<approx>\<^sub>p Pabs (?f env\<^sub>2 |`| cs)"
    proof (rule prelated.defer)
      show "(name, rsi) |\<in>| rs" "0 < arity rsi" "list_all closed args"
        using "defer" by auto
    next
      {
        fix pat\<^sub>1 rhs\<^sub>1
        fix pat\<^sub>2 rhs\<^sub>2
        assume "(pat\<^sub>2, rhs\<^sub>2) |\<in>| cs"
        assume "pat\<^sub>1 = pat\<^sub>2" "rhs\<^sub>1 \<approx>\<^sub>p rhs\<^sub>2"
        have "rhs\<^sub>1 \<approx>\<^sub>p subst rhs\<^sub>2 (fmdrop_fset (frees pat\<^sub>2) env\<^sub>2)"
          by (subst subst_closed_pabs) fact+
      }
      hence "rel_fset (rel_prod (=) prelated) (id |`| irules_deferred_matches args rsi) (?f env\<^sub>2 |`| cs)"
        by (force intro!: rel_fset_image[OF \<open>rel_fset _ _ _\<close>])

      thus "rel_fset (rel_prod (=) prelated) (irules_deferred_matches args rsi) (?f env\<^sub>2 |`| cs)"
        by simp
    qed

  moreover have "map (\<lambda>t. subst t env\<^sub>1) args = args"
    apply (rule map_idI)
    apply (rule subst_closed_id)
    using "defer" by (simp add: list_all_iff)

  ultimately show ?case
    by (simp add: subst_list_comb)
qed (auto intro: prelated.intros)

lemma prelated_step:
  assumes "name, pats, rhs \<turnstile>\<^sub>i u \<rightarrow> u'" "t \<approx>\<^sub>p u"
  obtains t' where "name, pats, rhs \<turnstile>\<^sub>i t \<rightarrow> t'" "t' \<approx>\<^sub>p u'"
proof -
  let ?lhs = "name $$ pats"
  from assms obtain env where "match ?lhs u = Some env" "u' = subst rhs env"
    unfolding irewrite_step_def by blast
  then obtain env' where "match ?lhs t = Some env'" "prelated.P_env env' env"
    using assms by (auto elim: prelated.related_match)
  hence "subst rhs env' \<approx>\<^sub>p subst rhs env"
    using assms by (auto intro: prelated_subst)

  show thesis
    proof
      show "name, pats, rhs \<turnstile>\<^sub>i t \<rightarrow> subst rhs env'"
        unfolding irewrite_step_def using \<open>match ?lhs t = Some env'\<close>
        by simp
    next
      show "subst rhs env' \<approx>\<^sub>p u'"
        unfolding \<open>u' = subst rhs env\<close>
        by fact
    qed
qed

(* FIXME write using relators *)
lemma prelated_beta: \<comment> \<open>same problem as @{thm [source=true] prelated.related_match}\<close>
  assumes "(pat, rhs\<^sub>2) \<turnstile> t\<^sub>2 \<rightarrow> u\<^sub>2" "rhs\<^sub>1 \<approx>\<^sub>p rhs\<^sub>2" "t\<^sub>1 \<approx>\<^sub>p t\<^sub>2"
  obtains u\<^sub>1 where "(pat, rhs\<^sub>1) \<turnstile> t\<^sub>1 \<rightarrow> u\<^sub>1" "u\<^sub>1 \<approx>\<^sub>p u\<^sub>2"
proof -
  from assms obtain env\<^sub>2 where "match pat t\<^sub>2 = Some env\<^sub>2" "u\<^sub>2 = subst rhs\<^sub>2 env\<^sub>2"
    by auto
  with assms obtain env\<^sub>1 where "match pat t\<^sub>1 = Some env\<^sub>1" "prelated.P_env env\<^sub>1 env\<^sub>2"
    by (auto elim: prelated.related_match)
  with assms have "subst rhs\<^sub>1 env\<^sub>1 \<approx>\<^sub>p subst rhs\<^sub>2 env\<^sub>2"
    by (auto intro: prelated_subst)

  show thesis
    proof
      show "(pat, rhs\<^sub>1) \<turnstile> t\<^sub>1 \<rightarrow> subst rhs\<^sub>1 env\<^sub>1"
        using \<open>match pat t\<^sub>1 = _\<close> by simp
    next
      show "subst rhs\<^sub>1 env\<^sub>1 \<approx>\<^sub>p u\<^sub>2"
        unfolding \<open>u\<^sub>2 = _\<close> by fact
    qed
qed

theorem transform_correct:
  assumes "transform_irule_set rs \<turnstile>\<^sub>i u \<longrightarrow> u'" "t \<approx>\<^sub>p u" "closed t"
  obtains t' where "rs \<turnstile>\<^sub>i t \<longrightarrow>* t'" \<comment> \<open>zero or one step\<close> and "t' \<approx>\<^sub>p u'"
using assms(1-3) proof (induction arbitrary: t thesis rule: irewrite.induct)
  case (beta c cs\<^sub>2 u\<^sub>2 x\<^sub>2')
  obtain v u\<^sub>1 where "t = v $\<^sub>p u\<^sub>1" "v \<approx>\<^sub>p Pabs cs\<^sub>2" "u\<^sub>1 \<approx>\<^sub>p u\<^sub>2"
    using \<open>t \<approx>\<^sub>p Pabs cs\<^sub>2 $\<^sub>p u\<^sub>2\<close> by cases
  with beta have "closed u\<^sub>1"
    by (simp add: closed_except_def)

  obtain pat rhs\<^sub>2 where "c = (pat, rhs\<^sub>2)" by (cases c) auto

  from \<open>v \<approx>\<^sub>p Pabs cs\<^sub>2\<close> show ?case
    proof (cases rule: prelated_absE)
      case (pat cs\<^sub>1)
      with beta \<open>c = _\<close> obtain rhs\<^sub>1 where "(pat, rhs\<^sub>1) |\<in>| cs\<^sub>1" "rhs\<^sub>1 \<approx>\<^sub>p rhs\<^sub>2"
        by (auto elim: rel_fsetE2)
      with beta obtain x\<^sub>1' where "(pat, rhs\<^sub>1) \<turnstile> u\<^sub>1 \<rightarrow> x\<^sub>1'" "x\<^sub>1' \<approx>\<^sub>p x\<^sub>2'"
        using \<open>u\<^sub>1 \<approx>\<^sub>p u\<^sub>2\<close> assms \<open>c = _\<close>
        by (auto elim: prelated_beta simp del: rewrite_step.simps)

      show ?thesis
        proof (rule beta.prems)
          show "rs \<turnstile>\<^sub>i t \<longrightarrow>* x\<^sub>1'"
            unfolding \<open>t = _\<close> \<open>v = _\<close>
            by (intro r_into_rtranclp irewrite.beta) fact+
        next
          show "x\<^sub>1' \<approx>\<^sub>p x\<^sub>2'"
            by fact
      qed
    next
      case ("defer" name rsi args)
      with beta \<open>c = _\<close> obtain rhs\<^sub>1' where "(pat, rhs\<^sub>1') |\<in>| irules_deferred_matches args rsi" "rhs\<^sub>1' \<approx>\<^sub>p rhs\<^sub>2"
        by (auto elim: rel_fsetE2)
      then obtain env\<^sub>a rhs\<^sub>1 pats
        where "matchs (butlast pats) args = Some env\<^sub>a" "pat = last pats" "rhs\<^sub>1' = subst rhs\<^sub>1 env\<^sub>a"
          and "(pats, rhs\<^sub>1) |\<in>| rsi"
        by auto
      hence "linears pats"
        using \<open>(name, rsi) |\<in>| rs\<close> inner unfolding irules_def by blast

      have "arity_compatibles rsi"
        using "defer" inner by (blast dest: fpairwiseD)
      have "length pats > 0"
        by (subst arity_compatible_length) fact+
      hence "pats = butlast pats @ [pat]"
        unfolding \<open>pat = _\<close> by simp

      from beta \<open>c = _\<close> obtain env\<^sub>b where "match pat u\<^sub>2 = Some env\<^sub>b" "x\<^sub>2' = subst rhs\<^sub>2 env\<^sub>b"
        by fastforce
      with \<open>u\<^sub>1 \<approx>\<^sub>p u\<^sub>2\<close> obtain env\<^sub>b' where "match pat u\<^sub>1 = Some env\<^sub>b'" "prelated.P_env env\<^sub>b' env\<^sub>b"
        by (metis prelated.related_match)

      have "closed_env env\<^sub>a"
        by (rule closed.matchs) fact+
      have "closed_env env\<^sub>b'"
        apply (rule closed.matchs[where pats = "[pat]" and ts = "[u\<^sub>1]"])
         apply simp
         apply fact
        apply simp
        apply fact
        done

      have "fmdom env\<^sub>a = freess (butlast pats)"
        by (rule matchs_dom) fact
      moreover have "fmdom env\<^sub>b' = frees pat"
        by (rule match_dom) fact
      moreover have "fdisjnt (freess (butlast pats)) (frees pat)"
        using \<open>pats = _\<close> \<open>linears pats\<close>
        by (metis freess_single linears_appendD(3))
      ultimately have "fdisjnt (fmdom env\<^sub>a) (fmdom env\<^sub>b')"
        by simp

      show ?thesis
        proof (rule beta.prems)
          have "rs \<turnstile>\<^sub>i name $$ args $\<^sub>p u\<^sub>1 \<longrightarrow> subst rhs\<^sub>1' env\<^sub>b'"
            proof (rule irewrite.step)
              show "(name, rsi) |\<in>| rs" "(pats, rhs\<^sub>1) |\<in>| rsi"
                by fact+
            next
              show "name, pats, rhs\<^sub>1 \<turnstile>\<^sub>i name $$ args $\<^sub>p u\<^sub>1 \<rightarrow> subst rhs\<^sub>1' env\<^sub>b'"
                apply (rule irewrite_stepI)
                 apply (fold app_pterm_def)
                 apply (subst list_comb_snoc)
                 apply (subst matchs_match_list_comb)
                 apply (subst \<open>pats = _\<close>)
                 apply (rule matchs_appI)
                  apply fact
                 apply simp
                 apply fact
                unfolding \<open>rhs\<^sub>1' = _\<close>
                apply (rule subst_indep')
                 apply fact+
                done
            qed
          thus "rs \<turnstile>\<^sub>i t \<longrightarrow>* subst rhs\<^sub>1' env\<^sub>b'"
            unfolding \<open>t = _\<close> \<open>v = _\<close>
            by (rule r_into_rtranclp)
        next
          show "subst rhs\<^sub>1' env\<^sub>b' \<approx>\<^sub>p x\<^sub>2'"
            unfolding \<open>x\<^sub>2' = _\<close>
            by (rule prelated_subst) fact+
        qed
    qed
next
  case (step name rs\<^sub>2 pats rhs u u')
  then obtain rs\<^sub>1 where "rs\<^sub>2 = transform_irules rs\<^sub>1" "(name, rs\<^sub>1) |\<in>| rs"
    unfolding transform_irule_set_def by force
  hence "arity_compatibles rs\<^sub>1"
    using inner by (blast dest: fpairwiseD)

  show ?case
    proof (cases "arity rs\<^sub>1 = 0")
      case True
      hence "rs\<^sub>2 = rs\<^sub>1"
        unfolding \<open>rs\<^sub>2 = _\<close> transform_irules_def by simp
      with step have "(pats, rhs) |\<in>| rs\<^sub>1"
        by simp
      from step obtain t' where "name, pats, rhs \<turnstile>\<^sub>i t \<rightarrow> t'" "t' \<approx>\<^sub>p u'"
        using assms
        by (auto elim: prelated_step)

      show ?thesis
        proof (rule step.prems)
          show "rs \<turnstile>\<^sub>i t \<longrightarrow>* t'"
            by (intro conjI exI r_into_rtranclp irewrite.step) fact+
        qed fact
    next
      let ?f = "\<lambda>(pats, rhs). (butlast pats, last pats, rhs)"
      let ?grp = "fgroup_by ?f rs\<^sub>1"

      case False
      hence "rs\<^sub>2 = map_prod id Pabs |`| ?grp"
        unfolding \<open>rs\<^sub>2 = _\<close> transform_irules_def by simp
      with step obtain cs where "rhs = Pabs cs" "(pats, cs) |\<in>| ?grp"
        by force

      from step obtain env\<^sub>2 where "match (name $$ pats) u = Some env\<^sub>2" "u' = subst rhs env\<^sub>2"
        unfolding irewrite_step_def by auto
      then obtain args\<^sub>2 where "u = name $$ args\<^sub>2" "matchs pats args\<^sub>2 = Some env\<^sub>2"
        by (auto elim: match_list_combE)
      with step obtain args\<^sub>1 where "t = name $$ args\<^sub>1" "list_all2 prelated args\<^sub>1 args\<^sub>2"
        by (auto elim: prelated.list_combE)

      then obtain env\<^sub>1 where "matchs pats args\<^sub>1 = Some env\<^sub>1" "prelated.P_env env\<^sub>1 env\<^sub>2"
        using \<open>matchs pats args\<^sub>2 = _\<close> by (metis prelated.related_matchs)
      hence "fmdom env\<^sub>1 = freess pats"
        by (auto simp: matchs_dom)

      obtain cs' where "u' = Pabs cs'"
        unfolding \<open>u' = _\<close> \<open>rhs = _\<close> by auto

      hence "cs' = (\<lambda>(pat, rhs). (pat, subst rhs (fmdrop_fset (frees pat) env\<^sub>2 ))) |`| cs"
        using \<open>u' = subst rhs env\<^sub>2\<close> unfolding \<open>rhs = _\<close>
        by simp

      show ?thesis
        proof (rule step.prems)
          show "rs \<turnstile>\<^sub>i t \<longrightarrow>* t"
            by (rule rtranclp.rtrancl_refl)
        next
          show "t \<approx>\<^sub>p u'"
            unfolding \<open>u' = Pabs cs'\<close> \<open>t = _\<close>
            proof (intro prelated.defer rel_fsetI; safe?)
              show "(name, rs\<^sub>1) |\<in>| rs"
                by fact
            next
              show "0 < arity rs\<^sub>1"
                using False by simp
            next
              show "list_all closed args\<^sub>1"
                using \<open>closed t\<close> unfolding \<open>t = _\<close> closed_list_comb .
            next
              fix pat rhs'
              assume "(pat, rhs') |\<in>| irules_deferred_matches args\<^sub>1 rs\<^sub>1"
              then obtain pats' rhs env
                where "(pats', rhs) |\<in>| rs\<^sub>1"
                  and "matchs (butlast pats') args\<^sub>1 = Some env" "pat = last pats'" "rhs' = subst rhs env"
                by auto
              with False have "pats' \<noteq> []"
                using \<open>arity_compatibles rs\<^sub>1\<close>
                by (metis list.size(3) arity_compatible_length)
              hence "butlast pats' @ [last pats'] = pats'"
                by simp

              from \<open>(pats, cs) |\<in>| ?grp\<close> obtain pats\<^sub>e rhs\<^sub>e
                where "(pats\<^sub>e, rhs\<^sub>e) |\<in>| rs\<^sub>1" "pats = butlast pats\<^sub>e"
                by (auto elim: fgroup_byE2)

              have "patterns_compatible (butlast pats') pats"
                unfolding \<open>pats = _\<close>
                apply (rule rev_accum_rel_butlast)
                using \<open>(pats', rhs) |\<in>| rs\<^sub>1\<close> \<open>(pats\<^sub>e, rhs\<^sub>e) |\<in>| rs\<^sub>1\<close> \<open>(name, rs\<^sub>1) |\<in>| rs\<close> inner
                by (blast dest: fpairwiseD)

              interpret irules': irules C_info "transform_irule_set rs" by (rule rules_transform)

              have "butlast pats' = pats" "env = env\<^sub>1"
                 apply (rule matchs_compatible_eq)
                subgoal by fact
                subgoal
                  apply (rule linears_butlastI)
                  using \<open>(pats', rhs) |\<in>| rs\<^sub>1\<close> \<open>(name, rs\<^sub>1) |\<in>| rs\<close> inner by blast
                subgoal
                  using \<open>(pats, _) |\<in>| rs\<^sub>2\<close> \<open>(name, rs\<^sub>2) |\<in>| transform_irule_set rs\<close>
                  using irules'.inner by blast
                  apply fact+
                subgoal
                  apply (rule matchs_compatible_eq)
                      apply fact
                     apply (rule linears_butlastI)
                  using \<open>(pats', rhs) |\<in>| rs\<^sub>1\<close> \<open>(name, rs\<^sub>1) |\<in>| rs\<close> inner
                     apply blast
                  using \<open>(pats, _) |\<in>| rs\<^sub>2\<close> \<open>(name, rs\<^sub>2) |\<in>| transform_irule_set rs\<close>
                  using irules'.inner apply blast
                  by fact+
                done

              let ?rhs_subst = "\<lambda>env. subst rhs (fmdrop_fset (frees pat) env)"

              have "fmdom env\<^sub>2 = freess pats"
                using \<open>match (_ $$ _) _ = Some env\<^sub>2\<close>
                by (simp add: match_dom)

              show "fBex cs' (rel_prod (=) prelated (pat, rhs'))"
                unfolding \<open>rhs' = _\<close>
                proof (rule fBexI, rule rel_prod.intros)
                  have "fdisjnt (freess (butlast pats')) (frees (last pats'))"
                    apply (subst freess_single[symmetric])
                    apply (rule linears_appendD)
                    apply (subst \<open>butlast pats' @ [last pats'] = pats'\<close>)
                    using \<open>(pats', rhs) |\<in>| rs\<^sub>1\<close> \<open>(name, rs\<^sub>1) |\<in>| rs\<close> inner
                    by blast

                  show "subst rhs env \<approx>\<^sub>p ?rhs_subst env\<^sub>2"
                    apply (rule prelated_subst)
                     apply (rule prelated_refl)
                    unfolding fmfilter_alt_defs
                    apply (subst fmfilter_true)
                    subgoal premises prems for x y
                      using fmdomI[OF prems]
                      unfolding \<open>pat = _\<close> \<open>fmdom env\<^sub>2 = _\<close>
                      apply (subst (asm) \<open>butlast pats' = pats\<close>[symmetric])
                      using \<open>fdisjnt (freess (butlast pats')) (frees (last pats'))\<close>
                      by (auto simp: fdisjnt_alt_def)
                    subgoal
                      unfolding \<open>env = _\<close>
                      by fact
                    done
                next
                  have "(pat, rhs) |\<in>| cs"
                    unfolding \<open>pat = _\<close>
                    apply (rule fgroup_byD[where a = "(x, y)" for x y])
                      apply fact
                     apply simp
                     apply (intro conjI)
                       apply fact
                      apply (rule refl)+
                    apply fact
                    done
                  thus "(pat, ?rhs_subst env\<^sub>2) |\<in>| cs'"
                    unfolding \<open>cs' = _\<close> by force
                qed simp
            next
              fix pat rhs'
              assume "(pat, rhs') |\<in>| cs'"
              then obtain rhs
                where "(pat, rhs) |\<in>| cs"
                  and "rhs' = subst rhs (fmdrop_fset (frees pat) env\<^sub>2 )"
                unfolding \<open>cs' = _\<close> by auto
              with \<open>(pats, cs) |\<in>| ?grp\<close> obtain pats'
                where "(pats', rhs) |\<in>| rs\<^sub>1" "pats = butlast pats'" "pat = last pats'"
                by auto
              with False have "length pats' \<noteq> 0"
                using \<open>arity_compatibles _\<close> by (metis arity_compatible_length)
              hence "pats' = pats @ [pat]"
                unfolding \<open>pats = _\<close> \<open>pat = _\<close> by auto
              moreover have "linears pats'"
                using \<open>(pats', rhs) |\<in>| rs\<^sub>1\<close> \<open>(name, rs\<^sub>1) |\<in>| _\<close> inner by blast
              ultimately have "fdisjnt (fmdom env\<^sub>1) (frees pat)"
                unfolding \<open>fmdom env\<^sub>1 = _\<close>
                by (auto dest: linears_appendD)

              let ?rhs_subst = "\<lambda>env. subst rhs (fmdrop_fset (frees pat) env)"

              show "fBex (irules_deferred_matches args\<^sub>1 rs\<^sub>1) (\<lambda>e. rel_prod (=) prelated e (pat, rhs'))"
                unfolding \<open>rhs' = _\<close>
                proof (rule fBexI, rule rel_prod.intros)
                  show "?rhs_subst env\<^sub>1 \<approx>\<^sub>p ?rhs_subst env\<^sub>2"
                    using \<open>prelated.P_env env\<^sub>1 env\<^sub>2\<close> inner
                    by (auto intro: prelated_subst)
                next
                  have "matchs (butlast pats') args\<^sub>1 = Some env\<^sub>1"
                    using \<open>matchs pats args\<^sub>1 = _\<close> \<open>pats = _\<close> by simp
                  moreover have "subst rhs env\<^sub>1 = ?rhs_subst env\<^sub>1"
                    apply (rule arg_cong[where f = "subst rhs"])
                    unfolding fmfilter_alt_defs
                    apply (rule fmfilter_true[symmetric])
                    using \<open>fdisjnt (fmdom env\<^sub>1) _\<close>
                    by (auto simp: fdisjnt_alt_def intro: fmdomI)
                  ultimately show "(pat, ?rhs_subst env\<^sub>1) |\<in>| irules_deferred_matches args\<^sub>1 rs\<^sub>1"
                    using \<open>(pats', rhs) |\<in>| rs\<^sub>1\<close> \<open>pat = last pats'\<close>
                    by auto
                qed simp
            qed
        qed
    qed
next
  case ("fun" v v' u)
  obtain w x where "t = w $\<^sub>p x" "w \<approx>\<^sub>p v" "x \<approx>\<^sub>p u" "closed w"
    using \<open>t \<approx>\<^sub>p v $\<^sub>p u\<close> \<open>closed t\<close> by cases (auto simp: closed_except_def)
  with "fun" obtain w' where "rs \<turnstile>\<^sub>i w \<longrightarrow>* w'" "w' \<approx>\<^sub>p v'"
    by blast

  show ?case
    proof (rule fun.prems)
      show "rs \<turnstile>\<^sub>i t \<longrightarrow>* w' $\<^sub>p x"
        unfolding \<open>t = _\<close>
        by (intro irewrite.rt_comb[unfolded app_pterm_def] rtranclp.rtrancl_refl) fact
    next
      show "w' $\<^sub>p x \<approx>\<^sub>p v' $\<^sub>p u"
        by (rule prelated.app) fact+
    qed
next
  case (arg u u' v)
  obtain w x where "t = w $\<^sub>p x" "w \<approx>\<^sub>p v" "x \<approx>\<^sub>p u" "closed x"
    using \<open>t \<approx>\<^sub>p v $\<^sub>p u\<close> \<open>closed t\<close> by cases (auto simp: closed_except_def)
  with arg obtain x' where "rs \<turnstile>\<^sub>i x \<longrightarrow>* x'" "x' \<approx>\<^sub>p u'"
    by blast

  show ?case
    proof (rule arg.prems)
      show "rs \<turnstile>\<^sub>i t \<longrightarrow>* w $\<^sub>p x'"
        unfolding \<open>t = w $\<^sub>p x\<close>
        by (intro irewrite.rt_comb[unfolded app_pterm_def] rtranclp.rtrancl_refl) fact
    next
      show "w $\<^sub>p x' \<approx>\<^sub>p v $\<^sub>p u'"
        by (rule prelated.app) fact+
    qed
qed

end

subsubsection \<open>Completeness of transformation\<close>

lemma (in irules) transform_completeness:
  assumes "rs \<turnstile>\<^sub>i t \<longrightarrow> t'" "closed t"
  shows "transform_irule_set rs \<turnstile>\<^sub>i t \<longrightarrow>* t'"
using assms proof induction
  case (step name irs' pats' rhs' t t')
  then obtain irs where "irs = transform_irules irs'" "(name, irs) |\<in>| transform_irule_set rs"
    unfolding transform_irule_set_def
    by (metis fimageI id_apply map_prod_simp)
  show ?case
  proof (cases "arity irs' = 0")
    case True
    hence "irs = irs'"
      unfolding \<open>irs = _\<close>
      unfolding transform_irules_def
      by simp
    with step have "(pats', rhs') |\<in>| irs" "name, pats', rhs' \<turnstile>\<^sub>i t \<rightarrow> t'"
      by blast+
    have "transform_irule_set rs \<turnstile>\<^sub>i t \<longrightarrow>* t'"
      apply (rule r_into_rtranclp)
      apply rule
      by fact+

    show ?thesis by fact
  next
    let ?f = "\<lambda>(pats, rhs). (butlast pats, last pats, rhs)"
    let ?grp = "fgroup_by ?f irs'"
    note closed_except_def [simp add]
    case False
    then have "irs = map_prod id Pabs |`| ?grp"
      unfolding \<open>irs = _\<close>
      unfolding transform_irules_def
      by simp
    with False have "irs = transform_irules irs'"
      unfolding transform_irules_def
      by simp
    obtain pat pats where "pat = last pats'" "pats = butlast pats'"
      by blast
    from step False have "length pats' \<noteq> 0"
      using arity_compatible_length inner
      by (smt fBallE prod.simps(2))
    then have "pats' = pats @ [pat]"
      unfolding \<open>pat = _\<close> \<open>pats = _\<close>
      by simp
    from step have "linears pats'"
      using inner fBallE
      by (metis (mono_tags, lifting) old.prod.case)
    then have "fdisjnt (freess pats) (frees pat)"
      unfolding \<open>pats' = _\<close>
      using linears_appendD(3) freess_single
      by force

    from step obtain cs where "(pats, cs) |\<in>| ?grp"
      unfolding \<open>pats = _\<close>
      by (metis (no_types, lifting) fgroup_by_complete fst_conv prod.simps(2))
    with step have "(pat, rhs') |\<in>| cs"
      unfolding \<open>pat = _\<close> \<open>pats = _\<close>
      by (meson fgroup_byD old.prod.case)
    have "(pats, Pabs cs) |\<in>| irs"
      using \<open>irs = map_prod id Pabs |`| ?grp\<close> \<open>(pats, cs) |\<in>| _\<close>
      by (metis (no_types, lifting) eq_snd_iff fst_conv fst_map_prod id_def rev_fimage_eqI snd_map_prod)
    from step obtain env' where "match (name $$ pats') t = Some env'" "subst rhs' env' = t'"
      using irewrite_step_def by auto
    have "name $$ pats' = (name $$ pats) $ pat"
      unfolding \<open>pats' = _\<close>
      by (simp add: app_term_def)
    then obtain t\<^sub>0 t\<^sub>1 env\<^sub>0 env\<^sub>1 where "t = t\<^sub>0 $\<^sub>p t\<^sub>1" "match (name $$ pats) t\<^sub>0 = Some env\<^sub>0" "match pat t\<^sub>1 = Some env\<^sub>1" "env' = env\<^sub>0 ++\<^sub>f env\<^sub>1"
      using match_appE_split[OF \<open>match (name $$ pats') _ = _\<close>[unfolded \<open>name $$ pats' = _\<close>], unfolded app_pterm_def]
      by blast
    with step have "closed t\<^sub>0" "closed t\<^sub>1"
      by auto
    then have "closed_env env\<^sub>0" "closed_env env\<^sub>1"
      using match_vars[OF \<open>match _ t\<^sub>0 = _\<close>] match_vars[OF \<open>match _ t\<^sub>1 = _\<close>]
      unfolding closed_except_def
      by auto
    obtain t\<^sub>0' where "subst (Pabs cs) env\<^sub>0 = t\<^sub>0'"
      by blast
    then obtain cs' where "t\<^sub>0' = Pabs cs'" "cs' = ((\<lambda>(pat, rhs). (pat, subst rhs (fmdrop_fset (frees pat) env\<^sub>0))) |`| cs)"
      using subst_pterm.simps(3) by blast
    obtain rhs where "subst rhs' (fmdrop_fset (frees pat) env\<^sub>0) = rhs"
      by blast
    then have "(pat, rhs) |\<in>| cs'"
      unfolding \<open>cs' = _\<close>
      using \<open>_ |\<in>| cs\<close>
      by (metis (mono_tags, lifting) old.prod.case rev_fimage_eqI)
    have "env\<^sub>0 ++\<^sub>f env\<^sub>1 = (fmdrop_fset (frees pat) env\<^sub>0) ++\<^sub>f env\<^sub>1"
      apply (subst fmadd_drop_left_dom[symmetric])
      using \<open>match pat _ = _\<close> match_dom
      by metis
    have "fdisjnt (fmdom env\<^sub>0) (fmdom env\<^sub>1)"
      using match_dom
      using \<open>match pat _ = _\<close> \<open>match (name $$ pats) _ = _\<close>
      using \<open>fdisjnt _ _\<close>
      unfolding fdisjnt_alt_def
      by (metis matchs_dom match_list_combE)
    have "subst rhs env\<^sub>1 = t'"
      unfolding \<open>_ = rhs\<close>[symmetric]
      unfolding \<open>_ = t'\<close>[symmetric]
      unfolding \<open>env' = _\<close>
      unfolding \<open>env\<^sub>0 ++\<^sub>f _ = _\<close>
      apply (subst subst_indep')
      using \<open>closed_env env\<^sub>0\<close>
        apply blast
      using \<open>fdisjnt (fmdom _) _\<close>
      unfolding fdisjnt_alt_def
      by auto

    show ?thesis
      unfolding \<open>t = _\<close>
      apply rule
       apply (rule r_into_rtranclp)
       apply (rule irewrite.intros(3))
       apply rule
         apply fact+
       apply (rule irewrite_stepI)
        apply fact+
      unfolding \<open>t\<^sub>0' = _\<close>
      apply rule
       apply fact
      using \<open>match pat t\<^sub>1 = _\<close> \<open>subst rhs _ = _\<close>
      by force
  qed
qed (auto intro: irewrite.rt_comb[unfolded app_pterm_def] intro!: irewrite.intros simp: closed_except_def)


subsubsection \<open>Computability\<close>

export_code
  compile transform_irules
  checking Scala SML

end