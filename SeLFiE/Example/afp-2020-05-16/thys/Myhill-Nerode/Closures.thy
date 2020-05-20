(* Author: Christian Urban, Xingyuan Zhang, Chunhan Wu *)
theory Closures
imports Myhill "HOL-Library.Infinite_Set"
begin

section \<open>Closure properties of regular languages\<close>

abbreviation
  regular :: "'a lang \<Rightarrow> bool"
where
  "regular A \<equiv> \<exists>r. A = lang r"

subsection \<open>Closure under \<open>\<union>\<close>, \<open>\<cdot>\<close> and \<open>\<star>\<close>\<close>

lemma closure_union [intro]:
  assumes "regular A" "regular B" 
  shows "regular (A \<union> B)"
proof -
  from assms obtain r1 r2::"'a rexp" where "lang r1 = A" "lang r2 = B" by auto
  then have "A \<union> B = lang (Plus r1 r2)" by simp
  then show "regular (A \<union> B)" by blast
qed

lemma closure_seq [intro]:
  assumes "regular A" "regular B" 
  shows "regular (A \<cdot> B)"
proof -
  from assms obtain r1 r2::"'a rexp" where "lang r1 = A" "lang r2 = B" by auto
  then have "A \<cdot> B = lang (Times r1 r2)" by simp
  then show "regular (A \<cdot> B)" by blast
qed

lemma closure_star [intro]:
  assumes "regular A"
  shows "regular (A\<star>)"
proof -
  from assms obtain r::"'a rexp" where "lang r = A" by auto
  then have "A\<star> = lang (Star r)" by simp
  then show "regular (A\<star>)" by blast
qed

subsection \<open>Closure under complementation\<close>

text \<open>Closure under complementation is proved via the 
  Myhill-Nerode theorem\<close>

lemma closure_complement [intro]:
  fixes A::"('a::finite) lang"
  assumes "regular A"
  shows "regular (- A)"
proof -
  from assms have "finite (UNIV // \<approx>A)" by (simp add: Myhill_Nerode)
  then have "finite (UNIV // \<approx>(-A))" by (simp add: str_eq_def)
  then show "regular (- A)" by (simp add: Myhill_Nerode)
qed

subsection \<open>Closure under \<open>-\<close> and \<open>\<inter>\<close>\<close>

lemma closure_difference [intro]:
  fixes A::"('a::finite) lang"
  assumes "regular A" "regular B" 
  shows "regular (A - B)"
proof -
  have "A - B = - (- A \<union> B)" by blast
  moreover
  have "regular (- (- A \<union> B))" 
    using assms by blast
  ultimately show "regular (A - B)" by simp
qed

lemma closure_intersection [intro]:
  fixes A::"('a::finite) lang"
  assumes "regular A" "regular B" 
  shows "regular (A \<inter> B)"
proof -
  have "A \<inter> B = - (- A \<union> - B)" by blast
  moreover
  have "regular (- (- A \<union> - B))" 
    using assms by blast
  ultimately show "regular (A \<inter> B)" by simp
qed

subsection \<open>Closure under string reversal\<close>

fun
  Rev :: "'a rexp \<Rightarrow> 'a rexp"
where
  "Rev Zero = Zero"
| "Rev One = One"
| "Rev (Atom c) = Atom c"
| "Rev (Plus r1 r2) = Plus (Rev r1) (Rev r2)"
| "Rev (Times r1 r2) = Times (Rev r2) (Rev r1)"
| "Rev (Star r) = Star (Rev r)"

lemma rev_seq[simp]:
  shows "rev ` (B \<cdot> A) = (rev ` A) \<cdot> (rev ` B)"
unfolding conc_def image_def
by (auto) (metis rev_append)+

lemma rev_star1:
  assumes a: "s \<in> (rev ` A)\<star>"
  shows "s \<in> rev ` (A\<star>)"
using a
proof(induct rule: star_induct)
  case (append s1 s2)
  have inj: "inj (rev::'a list \<Rightarrow> 'a list)" unfolding inj_on_def by auto
  have "s1 \<in> rev ` A" "s2 \<in> rev ` (A\<star>)" by fact+
  then obtain x1 x2 where "x1 \<in> A" "x2 \<in> A\<star>" and eqs: "s1 = rev x1" "s2 = rev x2" by auto
  then have "x1 \<in> A\<star>" "x2 \<in> A\<star>" by (auto)
  then have "x2 @ x1 \<in> A\<star>" by (auto)
  then have "rev (x2 @ x1) \<in> rev ` A\<star>" using inj by (simp only: inj_image_mem_iff)
  then show "s1 @ s2 \<in>  rev ` A\<star>" using eqs by simp
qed (auto)

lemma rev_star2:
  assumes a: "s \<in> A\<star>"
  shows "rev s \<in> (rev ` A)\<star>"
using a
proof(induct rule: star_induct)
  case (append s1 s2)
  have inj: "inj (rev::'a list \<Rightarrow> 'a list)" unfolding inj_on_def by auto
  have "s1 \<in> A"by fact
  then have "rev s1 \<in> rev ` A" using inj by (simp only: inj_image_mem_iff)
  then have "rev s1 \<in> (rev ` A)\<star>" by (auto)
  moreover
  have "rev s2 \<in> (rev ` A)\<star>" by fact
  ultimately show "rev (s1 @ s2) \<in>  (rev ` A)\<star>" by (auto)
qed (auto)

lemma rev_star [simp]:
  shows " rev ` (A\<star>) = (rev ` A)\<star>"
using rev_star1 rev_star2 by auto

lemma rev_lang:
  shows "rev ` (lang r) = lang (Rev r)"
by (induct r) (simp_all add: image_Un)

lemma closure_reversal [intro]:
  assumes "regular A"
  shows "regular (rev ` A)"
proof -
  from assms obtain r::"'a rexp" where "A = lang r" by auto
  then have "lang (Rev r) = rev ` A" by (simp add: rev_lang)
  then show "regular (rev` A)" by blast
qed
  
subsection \<open>Closure under left-quotients\<close>

abbreviation
  "Deriv_lang A B \<equiv> \<Union>x \<in> A. Derivs x B"

lemma closure_left_quotient:
  assumes "regular A"
  shows "regular (Deriv_lang B A)"
proof -
  from assms obtain r::"'a rexp" where eq: "lang r = A" by auto
  have fin: "finite (pderivs_lang B r)" by (rule finite_pderivs_lang)
  
  have "Deriv_lang B (lang r) = (\<Union> (lang ` pderivs_lang B r))"
    by (simp add: Derivs_pderivs pderivs_lang_def)
  also have "\<dots> = lang (\<Uplus>(pderivs_lang B r))" using fin by simp
  finally have "Deriv_lang B A = lang (\<Uplus>(pderivs_lang B r))" using eq
    by simp
  then show "regular (Deriv_lang B A)" by auto
qed

subsection \<open>Finite and co-finite sets are regular\<close>

lemma singleton_regular:
  shows "regular {s}"
proof (induct s)
  case Nil
  have "{[]} = lang (One)" by simp
  then show "regular {[]}" by blast
next
  case (Cons c s)
  have "regular {s}" by fact
  then obtain r where "{s} = lang r" by blast
  then have "{c # s} = lang (Times (Atom c) r)" 
    by (auto simp add: conc_def)
  then show "regular {c # s}" by blast
qed

lemma finite_regular:
  assumes "finite A"
  shows "regular A"
using assms
proof (induct)
  case empty
  have "{} = lang (Zero)" by simp
  then show "regular {}" by blast
next
  case (insert s A)
  have "regular {s}" by (simp add: singleton_regular)
  moreover
  have "regular A" by fact
  ultimately have "regular ({s} \<union> A)" by (rule closure_union)
  then show "regular (insert s A)" by simp
qed

lemma cofinite_regular:
  fixes A::"'a::finite lang"
  assumes "finite (- A)"
  shows "regular A"
proof -
  from assms have "regular (- A)" by (simp add: finite_regular)
  then have "regular (-(- A))" by (rule closure_complement)
  then show "regular A" by simp
qed


subsection \<open>Continuation lemma for showing non-regularity of languages\<close>

lemma continuation_lemma:
  fixes A B::"'a::finite lang"
  assumes reg: "regular A"
  and     inf: "infinite B"
  shows "\<exists>x \<in> B. \<exists>y \<in> B. x \<noteq> y \<and> x \<approx>A y"
proof -
  define eqfun where "eqfun = (\<lambda>A x::('a::finite list). (\<approx>A) `` {x})"
  have "finite (UNIV // \<approx>A)" using reg by (simp add: Myhill_Nerode)
  moreover
  have "(eqfun A) ` B \<subseteq> UNIV // (\<approx>A)"
    unfolding eqfun_def quotient_def by auto
  ultimately have "finite ((eqfun A) ` B)" by (rule rev_finite_subset)
  with inf have "\<exists>a \<in> B. infinite {b \<in> B. eqfun A b = eqfun A a}"
    by (rule pigeonhole_infinite)
  then obtain a where in_a: "a \<in> B" and "infinite {b \<in> B. eqfun A b = eqfun A a}"
    by blast
  moreover 
  have "{b \<in> B. eqfun A b = eqfun A a} = {b \<in> B. b \<approx>A a}"
    unfolding eqfun_def Image_def str_eq_def by auto
  ultimately have "infinite {b \<in> B. b \<approx>A a}" by simp
  then have "infinite ({b \<in> B. b \<approx>A a} - {a})" by simp
  moreover
  have "{b \<in> B. b \<approx>A a} - {a} = {b \<in> B. b \<approx>A a \<and> b \<noteq> a}" by auto
  ultimately have "infinite {b \<in> B. b \<approx>A a \<and> b \<noteq> a}" by simp
  then have "{b \<in> B. b \<approx>A a \<and> b \<noteq> a} \<noteq> {}"
    by (metis finite.emptyI)
  then obtain b where "b \<in> B" "b \<noteq> a" "b \<approx>A a" by blast
  with in_a show "\<exists>x \<in> B. \<exists>y \<in> B. x \<noteq> y \<and> x \<approx>A y"
    by blast
qed


subsection \<open>The language \<open>a\<^sup>n b\<^sup>n\<close> is not regular\<close>

abbreviation
  replicate_rev ("_ ^^^ _" [100, 100] 100)
where
  "a ^^^ n \<equiv> replicate n a"

lemma an_bn_not_regular:
  shows "\<not> regular (\<Union>n. {CHR ''a'' ^^^ n @ CHR ''b'' ^^^ n})"
proof
  define A where "A = (\<Union>n. {CHR ''a'' ^^^ n @ CHR ''b'' ^^^ n})"
  assume as: "regular A"
  define B where "B = (\<Union>n. {CHR ''a'' ^^^ n})"

  have sameness: "\<And>i j. CHR ''a'' ^^^ i @ CHR ''b'' ^^^ j \<in> A \<longleftrightarrow> i = j"
    unfolding A_def 
    apply auto
    apply(drule_tac f="\<lambda>s. length (filter ((=) (CHR ''a'')) s) = length (filter ((=) (CHR ''b'')) s)" 
      in arg_cong)
    apply(simp)
    done

  have b: "infinite B"
    unfolding infinite_iff_countable_subset
    unfolding inj_on_def B_def
    by (rule_tac x="\<lambda>n. CHR ''a'' ^^^ n" in exI) (auto)
  moreover
  have "\<forall>x \<in> B. \<forall>y \<in> B. x \<noteq> y \<longrightarrow> \<not> (x \<approx>A y)"
    apply(auto)
    unfolding B_def
    apply(auto)
    apply(simp add: str_eq_def)
    apply(drule_tac x="CHR ''b'' ^^^ xa" in spec)
    apply(simp add: sameness)
    done
  ultimately 
  show "False" using continuation_lemma[OF as] by blast
qed


end
