section \<open>Additional material over the \<open>Higher_Order_Terms\<close> AFP entry\<close>

theory Terms_Extras
imports
  "../Utils/Compiler_Utils"
  Higher_Order_Terms.Pats
  "Dict_Construction.Dict_Construction"
begin

no_notation Mpat_Antiquot.mpaq_App (infixl "$$" 900)

ML_file "hol_term.ML"

primrec basic_rule :: "_ \<Rightarrow> bool" where
"basic_rule (lhs, rhs) \<longleftrightarrow>
  linear lhs \<and>
  is_const (fst (strip_comb lhs)) \<and>
  \<not> is_const lhs \<and>
  frees rhs |\<subseteq>| frees lhs"

lemma basic_ruleI[intro]:
  assumes "linear lhs"
  assumes "is_const (fst (strip_comb lhs))"
  assumes "\<not> is_const lhs"
  assumes "frees rhs |\<subseteq>| frees lhs"
  shows "basic_rule (lhs, rhs)"
using assms by simp

primrec split_rule :: "(term \<times> 'a) \<Rightarrow> (name \<times> (term list \<times> 'a))" where
"split_rule (lhs, rhs) = (let (name, args) = strip_comb lhs in (const_name name, (args, rhs)))"

fun unsplit_rule :: "(name \<times> (term list \<times> 'a)) \<Rightarrow> (term \<times> 'a)" where
"unsplit_rule (name, (args, rhs)) = (name $$ args, rhs)"

lemma split_unsplit: "split_rule (unsplit_rule t) = t"
by (induct t rule: unsplit_rule.induct) (simp add: strip_list_comb const_name_def)

lemma unsplit_split:
  assumes "basic_rule r"
  shows "unsplit_rule (split_rule r) = r"
using assms
by (cases r) (simp add: split_beta)

datatype pat = Patvar name | Patconstr name "pat list"

fun mk_pat :: "term \<Rightarrow> pat" where
"mk_pat pat = (case strip_comb pat of (Const s, args) \<Rightarrow> Patconstr s (map mk_pat args) | (Free s, []) \<Rightarrow> Patvar s)"

declare mk_pat.simps[simp del]

lemma mk_pat_simps[simp]:
  "mk_pat (name $$ args) = Patconstr name (map mk_pat args)"
  "mk_pat (Free name) = Patvar name"
apply (auto simp: mk_pat.simps strip_list_comb_const)
apply (simp add: const_term_def)
done

primrec patvars :: "pat \<Rightarrow> name fset" where
"patvars (Patvar name) = {| name |}" |
"patvars (Patconstr _ ps) = ffUnion (fset_of_list (map patvars ps))"

lemma mk_pat_frees:
  assumes "linear p"
  shows "patvars (mk_pat p) = frees p"
using assms proof (induction p rule: linear_pat_induct)
  case (comb name args)

  have "map (patvars \<circ> mk_pat) args = map frees args"
    using comb by force
  hence "fset_of_list (map (patvars \<circ> mk_pat) args) = fset_of_list (map frees args)"
    by metis
  thus ?case
    by (simp add: freess_def)
qed simp


text \<open>
  This definition might seem a little counter-intuitive. Assume we have two defining equations
  of a function, e.g.\ @{term map}:
    @{prop "map f [] = []"}
    @{prop "map f (x # xs) = f x # map f xs"}
  The pattern "matrix" is compiled right-to-left. Equal patterns are grouped together. This
  definition is needed to avoid the following situation:
    @{prop "map f [] = []"}
    @{prop "map g (x # xs) = g x # map g xs"}
  While this is logically the same as above, the problem is that @{text f} and @{text g} are
  overlapping but distinct patterns. Hence, instead of grouping them together, they stay separate.
  This leads to overlapping patterns in the target language which will produce wrong results.
  One way to deal with this is to rename problematic variables before invoking the compiler.
\<close>

fun pattern_compatible :: "term \<Rightarrow> term \<Rightarrow> bool" where
"pattern_compatible (t\<^sub>1 $ t\<^sub>2) (u\<^sub>1 $ u\<^sub>2) \<longleftrightarrow> pattern_compatible t\<^sub>1 u\<^sub>1 \<and> (t\<^sub>1 = u\<^sub>1 \<longrightarrow> pattern_compatible t\<^sub>2 u\<^sub>2)" |
"pattern_compatible t u \<longleftrightarrow> t = u \<or> non_overlapping t u"

lemmas pattern_compatible_simps[simp] =
  pattern_compatible.simps[folded app_term_def]

lemmas pattern_compatible_induct = pattern_compatible.induct[case_names app_app]

lemma pattern_compatible_refl[intro?]: "pattern_compatible t t"
by (induct t) auto

corollary pattern_compatile_reflP[intro!]: "reflp pattern_compatible"
by (auto intro: pattern_compatible_refl reflpI)

lemma pattern_compatible_cases[consumes 1]:
  assumes "pattern_compatible t u"
  obtains (eq) "t = u"
        | (non_overlapping) "non_overlapping t u"
using assms proof (induction arbitrary: thesis rule: pattern_compatible_induct)
  case (app_app t\<^sub>1 t\<^sub>2 u\<^sub>1 u\<^sub>2)

  show ?case
    proof (cases "t\<^sub>1 = u\<^sub>1 \<and> t\<^sub>2 = u\<^sub>2")
      case True
      with app_app show thesis
        by simp
    next
      case False
      from app_app have "pattern_compatible t\<^sub>1 u\<^sub>1" "t\<^sub>1 = u\<^sub>1 \<Longrightarrow> pattern_compatible t\<^sub>2 u\<^sub>2"
        by auto
      with False have "non_overlapping (t\<^sub>1 $ t\<^sub>2) (u\<^sub>1 $ u\<^sub>2)"
        using app_app by (metis non_overlapping_appI1 non_overlapping_appI2)
      thus thesis
        by (rule app_app.prems(2))
    qed
qed auto

inductive rev_accum_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" for R where
nil: "rev_accum_rel R [] []" |
snoc: "rev_accum_rel R xs ys \<Longrightarrow> (xs = ys \<Longrightarrow> R x y) \<Longrightarrow> rev_accum_rel R (xs @ [x]) (ys @ [y])"

lemma rev_accum_rel_refl[intro]: "reflp R \<Longrightarrow> rev_accum_rel R xs xs"
unfolding reflp_def
by (induction xs rule: rev_induct) (auto intro: rev_accum_rel.intros)

lemma rev_accum_rel_length:
  assumes "rev_accum_rel R xs ys"
  shows "length xs = length ys"
using assms
by induct auto

context begin

private inductive_cases rev_accum_relE[consumes 1, case_names nil snoc]: "rev_accum_rel P xs ys"

lemma rev_accum_rel_butlast[intro]:
  assumes "rev_accum_rel P xs ys"
  shows "rev_accum_rel P (butlast xs) (butlast ys)"
using assms by (cases rule: rev_accum_relE) (auto intro: rev_accum_rel.intros)

lemma rev_accum_rel_snoc_eqE: "rev_accum_rel P (xs @ [a]) (xs @ [b]) \<Longrightarrow> P a b"
by (auto elim: rev_accum_relE)

end

abbreviation patterns_compatible :: "term list \<Rightarrow> term list \<Rightarrow> bool" where
"patterns_compatible \<equiv> rev_accum_rel pattern_compatible"

abbreviation patterns_compatibles :: "(term list \<times> 'a) fset \<Rightarrow> bool" where
"patterns_compatibles \<equiv> fpairwise (\<lambda>(pats\<^sub>1, _) (pats\<^sub>2, _). patterns_compatible pats\<^sub>1 pats\<^sub>2)"

lemma pattern_compatible_combD:
  assumes "length xs = length ys" "pattern_compatible (list_comb f xs) (list_comb f ys)"
  shows "patterns_compatible xs ys"
using assms by (induction xs ys rule: rev_induct2) (auto intro: rev_accum_rel.intros)

lemma pattern_compatible_combI[intro]:
  assumes "patterns_compatible xs ys" "pattern_compatible f g"
  shows "pattern_compatible (list_comb f xs) (list_comb g ys)"
using assms
proof (induction rule: rev_accum_rel.induct)
  case (snoc xs ys x y)

  then have "pattern_compatible (list_comb f xs) (list_comb g ys)"
    by auto

  moreover have " pattern_compatible x y" if "list_comb f xs = list_comb g ys"
    proof (rule snoc, rule list_comb_semi_inj)
      show "length xs = length ys"
        using snoc by (auto dest: rev_accum_rel_length)
    qed fact

  ultimately show ?case
    by auto
qed (auto intro: rev_accum_rel.intros)

experiment begin

\<comment> \<open>The above example can be made concrete here. In general, the following identity does not hold:\<close>

lemma "pattern_compatible t u \<longleftrightarrow> t = u \<or> non_overlapping t u"
  apply rule
   apply (erule pattern_compatible_cases; simp)
  apply (erule disjE)
   apply (metis pattern_compatible_refl)
  oops

\<comment> \<open>The counterexample:\<close>

definition "pats1 = [Free (Name ''f''), Const (Name ''nil'')]"
definition "pats2 = [Free (Name ''g''), Const (Name ''cons'') $ Free (Name ''x'') $ Free (Name ''xs'')]"

proposition "non_overlapping (list_comb c pats1) (list_comb c pats2)"
  unfolding pats1_def pats2_def
  apply (simp add: app_term_def)
  apply (rule non_overlapping_appI2)
  apply (rule non_overlapping_const_appI)
  done

proposition "\<not> patterns_compatible pats1 pats2"
  unfolding pats1_def pats2_def
  apply rule
  apply (erule rev_accum_rel.cases)
   apply simp
  apply auto
  apply (erule rev_accum_rel.cases)
   apply auto
  apply (erule rev_accum_rel.cases)
   apply auto
  apply (metis overlapping_var1I)
  done

end

abbreviation pattern_compatibles :: "(term \<times> 'a) fset \<Rightarrow> bool" where
"pattern_compatibles \<equiv> fpairwise (\<lambda>(lhs\<^sub>1, _) (lhs\<^sub>2, _). pattern_compatible lhs\<^sub>1 lhs\<^sub>2)"

corollary match_compatible_pat_eq:
  assumes "pattern_compatible t\<^sub>1 t\<^sub>2" "linear t\<^sub>1" "linear t\<^sub>2"
  assumes "match t\<^sub>1 u = Some env\<^sub>1" "match t\<^sub>2 u = Some env\<^sub>2"
  shows "t\<^sub>1 = t\<^sub>2"
using assms by (metis pattern_compatible_cases match_overlapping)

corollary match_compatible_env_eq:
  assumes "pattern_compatible t\<^sub>1 t\<^sub>2" "linear t\<^sub>1" "linear t\<^sub>2"
  assumes "match t\<^sub>1 u = Some env\<^sub>1" "match t\<^sub>2 u = Some env\<^sub>2"
  shows "env\<^sub>1 = env\<^sub>2"
using assms by (metis match_compatible_pat_eq option.inject)

corollary matchs_compatible_eq:
  assumes "patterns_compatible ts\<^sub>1 ts\<^sub>2" "linears ts\<^sub>1" "linears ts\<^sub>2"
  assumes "matchs ts\<^sub>1 us = Some env\<^sub>1" "matchs ts\<^sub>2 us = Some env\<^sub>2"
  shows "ts\<^sub>1 = ts\<^sub>2" "env\<^sub>1 = env\<^sub>2"
proof -
  fix name
  have "match (name $$ ts\<^sub>1) (name $$ us) = Some env\<^sub>1" "match (name $$ ts\<^sub>2) (name $$ us) = Some env\<^sub>2"
    using assms by auto
  moreover have "length ts\<^sub>1 = length ts\<^sub>2"
    using assms by (metis matchs_some_eq_length)
  ultimately have "pattern_compatible (name $$ ts\<^sub>1) (name $$ ts\<^sub>2)"
    using assms by (auto simp: const_term_def)
  moreover have "linear (name $$ ts\<^sub>1)" "linear (name $$ ts\<^sub>2)"
    using assms by (auto intro: linear_list_comb')
  note * = calculation

  from * have "name $$ ts\<^sub>1 = name $$ ts\<^sub>2"
    by (rule match_compatible_pat_eq) fact+
  thus "ts\<^sub>1 = ts\<^sub>2"
    by (meson list_comb_inj_second injD)

  from * show "env\<^sub>1 = env\<^sub>2"
    by (rule match_compatible_env_eq) fact+
qed

lemma compatible_find_match:
   assumes "pattern_compatibles (fset_of_list cs)" "list_all (linear \<circ> fst) cs" "is_fmap (fset_of_list cs)"
   assumes "match pat t = Some env" "(pat, rhs) \<in> set cs"
   shows "find_match cs t = Some (env, pat, rhs)"
using assms proof (induction cs arbitrary: pat rhs)
  case (Cons c cs)
  then obtain pat' rhs' where [simp]: "c = (pat', rhs')"
    by force
  have "find_match ((pat', rhs') # cs) t = Some (env, pat, rhs)"
    proof (cases "match pat' t")
      case None
      have "pattern_compatibles (fset_of_list cs)"
        using Cons
        by (force simp: fpairwise_alt_def)
      have "list_all (linear \<circ> fst) cs"
        using Cons
        by (auto simp: list_all_iff)
      have "is_fmap (fset_of_list cs)"
        using Cons
        by (meson fset_of_list_subset is_fmap_subset set_subset_Cons)
      show ?thesis
        apply (simp add: None)
        apply (rule Cons)
            apply fact+
        using Cons None by force
    next
      case (Some env')
      have "linear pat" "linear pat'"
        using Cons apply (metis Ball_set comp_apply fst_conv)
        using Cons by simp
      moreover from Cons have "pattern_compatible pat pat'"
        apply (cases "pat = pat'")
         apply (simp add: pattern_compatible_refl)
        unfolding fpairwise_alt_def
        by (force simp: fset_of_list_elem)
      ultimately have "env' = env" "pat' = pat"
        using match_compatible_env_eq match_compatible_pat_eq
        using Cons Some
        by blast+
      with Cons have "rhs' = rhs"
        using is_fmapD
        by (metis \<open>c = (pat', rhs')\<close> fset_of_list_elem list.set_intros(1))
      show ?thesis
        apply (simp add: Some)
        apply (intro conjI)
        by fact+
    qed
  thus ?case
    unfolding \<open>c = _\<close> .
qed auto

context "term" begin

definition arity_compatible :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"arity_compatible t\<^sub>1 t\<^sub>2 = (
  let
    (head\<^sub>1, pats\<^sub>1) = strip_comb t\<^sub>1;
    (head\<^sub>2, pats\<^sub>2) = strip_comb t\<^sub>2
  in head\<^sub>1 = head\<^sub>2 \<longrightarrow> length pats\<^sub>1 = length pats\<^sub>2
)"

abbreviation arity_compatibles :: "('a \<times> 'b) fset \<Rightarrow> bool" where
"arity_compatibles \<equiv> fpairwise (\<lambda>(lhs\<^sub>1, _) (lhs\<^sub>2, _). arity_compatible lhs\<^sub>1 lhs\<^sub>2)"

definition head :: "'a \<Rightarrow> name" where
"head t \<equiv> const_name (fst (strip_comb t))"

abbreviation heads_of :: "(term \<times> 'a) fset \<Rightarrow> name fset" where
"heads_of rs \<equiv> (head \<circ> fst) |`| rs"

end

definition arity :: "('a list \<times> 'b) fset \<Rightarrow> nat" where
"arity rs = fthe_elem' ((length \<circ> fst) |`| rs)"

lemma arityI:
  assumes "fBall rs (\<lambda>(pats, _). length pats = n)" "rs \<noteq> {||}"
  shows "arity rs = n"
proof -
  have "(length \<circ> fst) |`| rs = {| n |}"
    using assms by force
  thus ?thesis
    unfolding arity_def fthe_elem'_eq by simp
qed

end