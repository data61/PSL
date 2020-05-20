(*<*)
theory Regex
  imports Trace "HOL-Library.Lattice_Syntax" "HOL-Library.Extended_Nat"
begin
(*>*)

section \<open>Regular expressions\<close>

context begin

qualified datatype (atms: 'a) regex = Skip nat | Test 'a
  | Plus "'a regex" "'a regex" | Times "'a regex" "'a regex"  | Star "'a regex"

lemma finite_atms[simp]: "finite (atms r)"
  by (induct r) auto

definition "Wild = Skip 1"

lemma size_regex_estimation[termination_simp]: "x \<in> atms r \<Longrightarrow> y < f x \<Longrightarrow> y < size_regex f r"
  by (induct r) auto

lemma size_regex_estimation'[termination_simp]: "x \<in> atms r \<Longrightarrow> y \<le> f x \<Longrightarrow> y \<le> size_regex f r"
  by (induct r) auto

qualified definition "TimesL r S = Times r ` S"
qualified definition "TimesR R s = (\<lambda>r. Times r s) ` R"

qualified primrec fv_regex where
  "fv_regex fv (Skip n) = {}"
| "fv_regex fv (Test \<phi>) = fv \<phi>"
| "fv_regex fv (Plus r s) = fv_regex fv r \<union> fv_regex fv s"
| "fv_regex fv (Times r s) = fv_regex fv r \<union> fv_regex fv s"
| "fv_regex fv (Star r) = fv_regex fv r"

lemma fv_regex_cong[fundef_cong]:
  "r = r' \<Longrightarrow> (\<And>z. z \<in> atms r \<Longrightarrow> fv z = fv' z) \<Longrightarrow> fv_regex fv r = fv_regex fv' r'"
  by (induct r arbitrary: r') auto

lemma finite_fv_regex[simp]: "(\<And>z. z \<in> atms r \<Longrightarrow> finite (fv z)) \<Longrightarrow> finite (fv_regex fv r)"
  by (induct r) auto

lemma fv_regex_commute:
  "(\<And>z. z \<in> atms r \<Longrightarrow> x \<in> fv z \<longleftrightarrow> g x \<in> fv' z) \<Longrightarrow> x \<in> fv_regex fv r \<longleftrightarrow> g x \<in> fv_regex fv' r"
  by (induct r) auto

lemma fv_regex_alt: "fv_regex fv r = (\<Union>z \<in> atms r. fv z)"
  by (induct r) auto

qualified definition nfv_regex where
  "nfv_regex fv r = Max (insert 0 (Suc ` fv_regex fv r))"

lemma insert_Un: "insert x (A \<union> B) = insert x A \<union> insert x B"
  by auto

lemma nfv_regex_simps[simp]:
  assumes [simp]: "(\<And>z. z \<in> atms r \<Longrightarrow> finite (fv z))" "(\<And>z. z \<in> atms s \<Longrightarrow> finite (fv z))"
  shows
  "nfv_regex fv (Skip n) = 0"
  "nfv_regex fv (Test \<phi>) = Max (insert 0 (Suc ` fv \<phi>))"
  "nfv_regex fv (Plus r s) = max (nfv_regex fv r) (nfv_regex fv s)"
  "nfv_regex fv (Times r s) = max (nfv_regex fv r) (nfv_regex fv s)"
  "nfv_regex fv (Star r) = nfv_regex fv r"
  unfolding nfv_regex_def
  by (auto simp add: image_Un Max_Un insert_Un simp del: Un_insert_right Un_insert_left)

abbreviation "min_regex_default f r j \<equiv> (if atms r = {} then j else Min ((\<lambda>z. f z j) ` atms r))"

qualified primrec match :: "(nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a regex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "match test (Skip n) = (\<lambda>i j. j = i + n)"
| "match test (Test \<phi>) = (\<lambda>i j. i = j \<and> test i \<phi>)"
| "match test (Plus r s) = match test r \<squnion> match test s"
| "match test (Times r s) = match test r OO match test s"
| "match test (Star r) = (match test r)\<^sup>*\<^sup>*"

lemma match_cong[fundef_cong]:
  "r = r' \<Longrightarrow> (\<And>i z. z \<in> atms r \<Longrightarrow> t i z = t' i z) \<Longrightarrow> match t r = match t' r'"
  by (induct r arbitrary: r') auto

qualified primrec eps where
  "eps test i (Skip n) = (n = 0)"
| "eps test i (Test \<phi>) = test i \<phi>"
| "eps test i (Plus r s) = (eps test i r \<or> eps test i s)"
| "eps test i (Times r s) = (eps test i r \<and> eps test i s)"
| "eps test i (Star r) = True"

qualified primrec lpd where
  "lpd test i (Skip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> {Skip m})"
| "lpd test i (Test \<phi>) = {}"
| "lpd test i (Plus r s) = (lpd test i r \<union> lpd test i s)"
| "lpd test i (Times r s) = TimesR (lpd test i r) s \<union> (if eps test i r then lpd test i s else {})"
| "lpd test i (Star r) = TimesR (lpd test i r) (Star r)"

qualified primrec lpd\<kappa> where
  "lpd\<kappa> \<kappa> test i (Skip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> {\<kappa> (Skip m)})"
| "lpd\<kappa> \<kappa> test i (Test \<phi>) = {}"
| "lpd\<kappa> \<kappa> test i (Plus r s) = lpd\<kappa> \<kappa> test i r \<union> lpd\<kappa> \<kappa> test i s"
| "lpd\<kappa> \<kappa> test i (Times r s) = lpd\<kappa> (\<lambda>t. \<kappa> (Times t s)) test i r \<union> (if eps test i r then lpd\<kappa> \<kappa> test i s else {})"
| "lpd\<kappa> \<kappa> test i (Star r) = lpd\<kappa> (\<lambda>t. \<kappa> (Times t (Star r))) test i r"

qualified primrec rpd where
  "rpd test i (Skip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> {Skip m})"
| "rpd test i (Test \<phi>) = {}"
| "rpd test i (Plus r s) = (rpd test i r \<union> rpd test i s)"
| "rpd test i (Times r s) = TimesL r (rpd test i s) \<union> (if eps test i s then rpd test i r else {})"
| "rpd test i (Star r) = TimesL (Star r) (rpd test i r)"

qualified primrec rpd\<kappa> where
  "rpd\<kappa> \<kappa> test i (Skip n) = (case n of 0 \<Rightarrow> {} | Suc m \<Rightarrow> {\<kappa> (Skip m)})"
| "rpd\<kappa> \<kappa> test i (Test \<phi>) = {}"
| "rpd\<kappa> \<kappa> test i (Plus r s) = rpd\<kappa> \<kappa> test i r \<union> rpd\<kappa> \<kappa> test i s"
| "rpd\<kappa> \<kappa> test i (Times r s) = rpd\<kappa> (\<lambda>t. \<kappa> (Times r t)) test i s \<union> (if eps test i s then rpd\<kappa> \<kappa> test i r else {})"
| "rpd\<kappa> \<kappa> test i (Star r) = rpd\<kappa> (\<lambda>t. \<kappa> (Times (Star r) t)) test i r"

lemma lpd\<kappa>_lpd: "lpd\<kappa> \<kappa> test i r = \<kappa> ` lpd test i r"
  by (induct r arbitrary: \<kappa>) (auto simp: TimesR_def split: nat.splits)

lemma rpd\<kappa>_rpd: "rpd\<kappa> \<kappa> test i r = \<kappa> ` rpd test i r"
  by (induct r arbitrary: \<kappa>) (auto simp: TimesL_def split: nat.splits)

lemma match_le: "match test r i j \<Longrightarrow> i \<le> j"
proof (induction r arbitrary: i j)
  case (Times r s)
  then show ?case using order.trans by fastforce
next
  case (Star r)
  from Star.prems show ?case
    unfolding match.simps by (induct i j rule: rtranclp.induct) (force dest: Star.IH)+
qed auto

lemma match_rtranclp_le: "(match test r)\<^sup>*\<^sup>* i j \<Longrightarrow> i \<le> j"
  by (metis match.simps(5) match_le)

lemma eps_match: "eps test i r \<longleftrightarrow> match test r i i"
  by (induction r) (auto dest: antisym[OF match_le match_le])

lemma lpd_match: "i < j \<Longrightarrow> match test r i j \<longleftrightarrow> (\<Squnion>s \<in> lpd test i r. match test s) (i + 1) j"
proof (induction r arbitrary: i j)
  case (Times r s)
  have "match test (Times r s) i j \<longleftrightarrow> (\<exists>k. match test r i k \<and> match test s k j)"
    by auto
  also have "\<dots> \<longleftrightarrow> match test r i i \<and> match test s i j \<or>
    (\<exists>k>i. match test r i k \<and> match test s k j)"
    using match_le[of test r i] nat_less_le by auto
  also have "\<dots> \<longleftrightarrow> match test r i i \<and> (\<Squnion>t \<in> lpd test i s. match test t) (i + 1) j \<or>
    (\<exists>k>i. (\<Squnion>t \<in> lpd test i r. match test t) (i + 1) k \<and> match test s k j)"
    using Times.IH(1) Times.IH(2)[OF Times.prems] by metis
  also have "\<dots> \<longleftrightarrow> match test r i i \<and> (\<Squnion>t \<in> lpd test i s. match test t) (i + 1) j \<or>
    (\<exists>k. (\<Squnion>t \<in> lpd test i r. match test t) (i + 1) k \<and> match test s k j)"
    using Times.prems by (intro disj_cong[OF refl] iff_exI) (auto dest: match_le)
  also have "\<dots> \<longleftrightarrow> (\<Squnion> (match test ` lpd test i (Times r s))) (i + 1) j"
    by (force simp: TimesL_def TimesR_def eps_match)
  finally show ?case .
next
  case (Star r)
  have "\<exists>s\<in>lpd test i r. (match test s OO (match test r)\<^sup>*\<^sup>*) (i + 1) j" if "(match test r)\<^sup>*\<^sup>* i j"
    using that Star.prems match_le[of test _ "i + 1"]
  proof (induct rule: converse_rtranclp_induct)
    case (step i k)
    then show ?case
      by (cases "i < k") (auto simp: not_less Star.IH dest: match_le)
  qed simp
  with Star.prems show ?case using match_le[of test _  "i + 1"]
    by (auto simp: TimesL_def TimesR_def Suc_le_eq Star.IH[of i]
      elim!: converse_rtranclp_into_rtranclp[rotated])
qed (auto split: nat.splits)

lemma rpd_match: "i < j \<Longrightarrow> match test r i j \<longleftrightarrow> (\<Squnion>s \<in> rpd test j r. match test s) i (j - 1)"
proof (induction r arbitrary: i j)
  case (Times r s)
  have "match test (Times r s) i j \<longleftrightarrow> (\<exists>k. match test r i k \<and> match test s k j)"
    by auto
  also have "\<dots> \<longleftrightarrow> match test r i j \<and> match test s j j \<or>
    (\<exists>k<j. match test r i k \<and> match test s k j)"
    using match_le[of test s _ j] nat_less_le by auto
  also have "\<dots> \<longleftrightarrow> (\<Squnion>t \<in> rpd test j r. match test t) i (j - 1) \<and> match test s j j  \<or>
    (\<exists>k<j. match test r i k \<and> (\<Squnion>t \<in> rpd test j s. match test t) k (j - 1))"
    using Times.IH(1)[OF Times.prems] Times.IH(2) by metis
  also have "\<dots> \<longleftrightarrow> (\<Squnion>t \<in> rpd test j r. match test t) i (j - 1) \<and> match test s j j  \<or>
    (\<exists>k. match test r i k \<and> (\<Squnion>t \<in> rpd test j s. match test t) k (j - 1))"
    using Times.prems by (intro disj_cong[OF refl] iff_exI) (auto dest: match_le)
  also have "\<dots> \<longleftrightarrow> (\<Squnion> (match test ` rpd test j (Times r s))) i (j - 1)"
    by (force simp: TimesL_def TimesR_def eps_match)
  finally show ?case .
next
  case (Star r)
  have "\<exists>s\<in>rpd test j r. ((match test r)\<^sup>*\<^sup>* OO match test s) i (j - 1)" if "(match test r)\<^sup>*\<^sup>* i j"
    using that Star.prems match_le[of test _ _ "j - 1"]
  proof (induct rule: rtranclp_induct)
    case (step k j)
    then show ?case
      by (cases "k < j") (auto simp: not_less Star.IH dest: match_le)
  qed simp
  with Star.prems show ?case
    by (auto 0 3 simp: TimesL_def TimesR_def intro: Star.IH[of _ j, THEN iffD2]
      elim!: rtranclp.rtrancl_into_rtrancl dest: match_le[of test _ _ "j - 1", unfolded One_nat_def])
qed (auto split: nat.splits)

lemma lpd_fv_regex: "s \<in> lpd test i r \<Longrightarrow> fv_regex fv s \<subseteq> fv_regex fv r"
  by (induct r arbitrary: s) (auto simp: TimesR_def TimesL_def split: if_splits nat.splits)+

lemma rpd_fv_regex: "s \<in> rpd test i r \<Longrightarrow> fv_regex fv s \<subseteq> fv_regex fv r"
  by (induct r arbitrary: s) (auto simp: TimesR_def TimesL_def split: if_splits nat.splits)+

lemma match_fv_cong:
  "(\<And>i x. x \<in> atms r \<Longrightarrow> test i x = test' i x) \<Longrightarrow> match test r = match test' r"
  by (induct r) auto

lemma eps_fv_cong:
  "(\<And>i x. x \<in> atms r \<Longrightarrow> test i x = test' i x) \<Longrightarrow> eps test i r = eps test' i r"
  by (induct r) auto

datatype modality = Past | Futu
datatype safety = Strict | Lax

context
  fixes fv :: "'a \<Rightarrow> 'b set"
  and safe :: "safety \<Rightarrow> 'a \<Rightarrow> bool"
begin

qualified fun safe_regex :: "modality \<Rightarrow> safety \<Rightarrow> 'a regex \<Rightarrow> bool" where
  "safe_regex m _ (Skip n) = True"
| "safe_regex m g (Test \<phi>) = safe g \<phi>"
| "safe_regex m g (Plus r s) = ((g = Lax \<or> fv_regex fv r = fv_regex fv s) \<and> safe_regex m g r \<and> safe_regex m g s)"
| "safe_regex Futu g (Times r s) =
    ((g = Lax \<or> fv_regex fv r \<subseteq> fv_regex fv s) \<and> safe_regex Futu g s \<and> safe_regex Futu Lax r)"
| "safe_regex Past g (Times r s) =
    ((g = Lax \<or> fv_regex fv s \<subseteq> fv_regex fv r) \<and> safe_regex Past g r \<and> safe_regex Past Lax s)"
| "safe_regex m g (Star r) = ((g = Lax \<or> fv_regex fv r = {}) \<and> safe_regex m g r)"

lemmas safe_regex_induct = safe_regex.induct[case_names Skip Test Plus TimesF TimesP Star]

lemma safe_cosafe:
  "(\<And>x. x \<in> atms r \<Longrightarrow> safe Strict x \<Longrightarrow> safe Lax x) \<Longrightarrow> safe_regex m Strict r \<Longrightarrow> safe_regex m Lax r"
  by (induct r; cases m) auto

lemma safe_lpd_fv_regex_le: "safe_regex Futu Strict r \<Longrightarrow> s \<in> lpd test i r \<Longrightarrow> fv_regex fv r \<subseteq> fv_regex fv s"
  by (induct r) (auto simp: TimesR_def split: if_splits)

lemma safe_lpd_fv_regex: "safe_regex Futu Strict r \<Longrightarrow> s \<in> lpd test i r \<Longrightarrow> fv_regex fv s = fv_regex fv r"
  by (simp add: eq_iff lpd_fv_regex safe_lpd_fv_regex_le)

lemma cosafe_lpd: "safe_regex Futu Lax r \<Longrightarrow> s \<in> lpd test i r \<Longrightarrow> safe_regex Futu Lax s"
proof (induct r arbitrary: s)
  case (Plus r1 r2)
  from Plus(3,4) show ?case
    by (auto elim: Plus(1,2))
next
  case (Times r1 r2)
  from Times(3,4) show ?case
    by (auto simp: TimesR_def elim: Times(1,2) split: if_splits)
qed (auto simp: TimesR_def split: nat.splits)

lemma safe_lpd: "(\<forall>x \<in> atms r. safe Strict x \<longrightarrow> safe Lax x) \<Longrightarrow>
  safe_regex Futu Strict r \<Longrightarrow> s \<in> lpd test i r \<Longrightarrow> safe_regex Futu Strict s"
proof (induct r arbitrary: s)
  case (Plus r1 r2)
  from Plus(3,4,5) show ?case
    by (auto elim: Plus(1,2) simp: ball_Un)
next
  case (Times r1 r2)
  from Times(3,4,5) show ?case
    by (force simp: TimesR_def ball_Un elim: Times(1,2) cosafe_lpd dest: lpd_fv_regex split: if_splits)
next
  case (Star r)
  from Star(2,3,4) show ?case
    by (force simp: TimesR_def elim: Star(1) cosafe_lpd
      dest: safe_cosafe[rotated] lpd_fv_regex[where fv=fv] split: if_splits)
qed (auto split: nat.splits)

lemma safe_rpd_fv_regex_le: "safe_regex Past Strict r \<Longrightarrow> s \<in> rpd test i r \<Longrightarrow> fv_regex fv r \<subseteq> fv_regex fv s"
  by (induct r) (auto simp: TimesL_def split: if_splits)

lemma safe_rpd_fv_regex: "safe_regex Past Strict r \<Longrightarrow> s \<in> rpd test i r \<Longrightarrow> fv_regex fv s = fv_regex fv r"
  by (simp add: eq_iff rpd_fv_regex safe_rpd_fv_regex_le)

lemma cosafe_rpd: "safe_regex Past Lax r \<Longrightarrow> s \<in> rpd test i r \<Longrightarrow> safe_regex Past Lax s"
proof (induct r arbitrary: s)
  case (Plus r1 r2)
  from Plus(3,4) show ?case
    by (auto elim: Plus(1,2))
next
  case (Times r1 r2)
  from Times(3,4) show ?case
    by (auto simp: TimesL_def elim: Times(1,2) split: if_splits)
qed (auto simp: TimesL_def split: nat.splits)

lemma safe_rpd: "(\<forall>x \<in> atms r. safe Strict x \<longrightarrow> safe Lax x) \<Longrightarrow>
  safe_regex Past Strict r \<Longrightarrow> s \<in> rpd test i r \<Longrightarrow> safe_regex Past Strict s"
proof (induct r arbitrary: s)
  case (Plus r1 r2)
  from Plus(3,4,5) show ?case
    by (auto elim: Plus(1,2) simp: ball_Un)
next
  case (Times r1 r2)
  from Times(3,4,5) show ?case
    by (force simp: TimesL_def ball_Un elim: Times(1,2) cosafe_rpd dest: rpd_fv_regex split: if_splits)
next
  case (Star r)
  from Star(2,3,4) show ?case
    by (force simp: TimesL_def elim: Star(1) cosafe_rpd
      dest: safe_cosafe[rotated] rpd_fv_regex[where fv=fv] split: if_splits)
qed (auto split: nat.splits)

lemma safe_regex_safe: "(\<And>g r. safe g r \<Longrightarrow> safe Lax r) \<Longrightarrow>
  safe_regex m g r \<Longrightarrow> x \<in> atms r \<Longrightarrow> safe Lax x"
  by (induct m g r rule: safe_regex.induct) auto

lemma safe_regex_map_regex:
  "(\<And>g x. x \<in> atms r \<Longrightarrow> safe g x \<Longrightarrow>  safe g (f x)) \<Longrightarrow> (\<And>x. x \<in> atms r \<Longrightarrow> fv (f x) = fv x) \<Longrightarrow>
   safe_regex m g r \<Longrightarrow> safe_regex m g (map_regex f r)"
  by (induct m g r rule: safe_regex.induct) (auto simp: fv_regex_alt regex.set_map)

end

lemma safe_regex_cong[fundef_cong]:
  "(\<And>g x. x \<in> atms r \<Longrightarrow> safe g x = safe' g x) \<Longrightarrow>
  Regex.safe_regex fv safe m g r = Regex.safe_regex fv safe' m g r"
  by (induct m g r rule: safe_regex.induct) auto

lemma safe_regex_mono:
  "(\<And>g x. x \<in> atms r \<Longrightarrow> safe g x \<Longrightarrow> safe' g x) \<Longrightarrow>
  Regex.safe_regex fv safe m g r \<Longrightarrow> Regex.safe_regex fv safe' m g r"
  by (induct m g r rule: safe_regex.induct) auto

lemma match_map_regex: "match t (map_regex f r) = match (\<lambda>k z. t k (f z)) r"
  by (induct r) auto

lemma match_cong_strong:
  "(\<And>k z. k \<in> {i ..< j + 1} \<Longrightarrow> z \<in> atms r \<Longrightarrow> t k z = t' k z) \<Longrightarrow> match t r i j = match t' r i j"
proof (induction r arbitrary: i j)
  case (Times r s)
  from Times.prems show ?case
    by (auto 0 4 simp: relcompp_apply intro: le_less_trans match_le less_Suc_eq_le
      dest: Times.IH[THEN iffD1, rotated -1] Times.IH[THEN iffD2, rotated -1] match_le)
next
  case (Star r)
  show ?case unfolding match.simps
  proof (rule iffI)
    assume *: "(match t r)\<^sup>*\<^sup>* i j"
    then have "i \<le> j" unfolding match.simps(5)[symmetric]
      by (rule match_le)
    with * show "(match t' r)\<^sup>*\<^sup>* i j" using Star.prems
    proof (induction i j rule: rtranclp.induct)
      case (rtrancl_into_rtrancl a b c)
      from rtrancl_into_rtrancl(1,2,4,5) show ?case
        by (intro rtranclp.rtrancl_into_rtrancl[OF rtrancl_into_rtrancl.IH])
          (auto dest!: Star.IH[THEN iffD1, rotated -1]
            dest: match_le match_rtranclp_le simp: less_Suc_eq_le)
    qed simp
  next
    assume *: "(match t' r)\<^sup>*\<^sup>* i j"
    then have "i \<le> j" unfolding match.simps(5)[symmetric]
      by (rule match_le)
    with * show "(match t r)\<^sup>*\<^sup>* i j" using Star.prems
    proof (induction i j rule: rtranclp.induct)
      case (rtrancl_into_rtrancl a b c)
      from rtrancl_into_rtrancl(1,2,4,5) show ?case
        by (intro rtranclp.rtrancl_into_rtrancl[OF rtrancl_into_rtrancl.IH])
          (auto dest!: Star.IH[THEN iffD2, rotated -1]
            dest: match_le match_rtranclp_le simp: less_Suc_eq_le)
    qed simp
  qed
qed auto

end

(*<*)
end
(*>*)
