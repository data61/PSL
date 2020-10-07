(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section \<open>Miscellaneous Mathematics\<close>

theory Misc 
imports 
  "HOL-Analysis.Analysis"
begin

text_raw \<open>\label{s:misc}\<close>

lemma sum_UNIV:
  fixes S::"'a::finite set"
  assumes complete: "\<And>x. x\<notin>S \<Longrightarrow> f x = 0"
  shows "sum f S = sum f UNIV"
proof -
  from complete have "sum f S = sum f (UNIV - S) + sum f S" by(simp)
  also have "... = sum f UNIV"
    by(auto intro: sum.subset_diff[symmetric])
  finally show ?thesis .
qed

lemma cInf_mono:
  fixes A::"'a::conditionally_complete_lattice set"
  assumes lower: "\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. a \<le> b"
      and bounded: "\<And>a. a \<in> A \<Longrightarrow> c \<le> a"
      and ne: "B \<noteq> {}"
  shows "Inf A \<le> Inf B"
proof(rule cInf_greatest[OF ne])
  fix b assume bin: "b \<in> B"
  with lower obtain a where ain: "a \<in> A" and le: "a \<le> b" by(auto)
  from ain bounded have "Inf A \<le> a" by(intro cInf_lower bdd_belowI, auto)
  also note le
  finally show "Inf A \<le> b" .
qed

lemma max_distrib:
  fixes c::real
  assumes nn: "0 \<le> c"
  shows "c * max a b = max (c * a) (c * b)"
proof(cases "a \<le> b")
  case True
  moreover with nn have "c * a \<le> c * b" by(auto intro:mult_left_mono)
  ultimately show ?thesis by(simp add:max.absorb2)
next
  case False then have "b \<le> a" by(auto)
  moreover with nn have "c * b \<le> c * a" by(auto intro:mult_left_mono)
  ultimately show ?thesis by(simp add:max.absorb1)
qed

lemma mult_div_mono_left:
  fixes c::real
  assumes nnc: "0 \<le> c" and nzc: "c \<noteq> 0"
      and inv: "a \<le> inverse c * b"
  shows "c * a \<le> b"
proof -
  from nnc inv have "c * a \<le> (c * inverse c) * b"
    by(auto simp:mult.assoc intro:mult_left_mono)
  also from nzc have "... = b" by(simp)
  finally show "c * a \<le> b" .
qed

lemma mult_div_mono_right:
  fixes c::real
  assumes nnc: "0 \<le> c" and nzc: "c \<noteq> 0"
      and inv: "inverse c * a \<le> b"
  shows "a \<le> c * b"
proof -
  from nzc have "a = (c * inverse c) * a " by(simp)
  also from nnc inv have "(c * inverse c) * a \<le> c * b"
    by(auto simp:mult.assoc intro:mult_left_mono)
  finally show "a \<le> c * b" .
qed

lemma min_distrib:
  fixes c::real
  assumes nnc: "0 \<le> c"
  shows "c * min a b = min (c * a) (c * b)"
proof(cases "a \<le> b")
  case True moreover with nnc have "c * a \<le> c * b"
    by(blast intro:mult_left_mono)
  ultimately show ?thesis by(auto)
next
  case False hence "b \<le> a" by(auto)
  moreover with nnc have "c * b \<le> c * a"
    by(blast intro:mult_left_mono)
  ultimately show ?thesis by(simp add:min.absorb2)
qed

lemma finite_set_least:
  fixes S::"'a::linorder set"
  assumes finite: "finite S"
      and ne: "S \<noteq> {}"
  shows "\<exists>x\<in>S. \<forall>y\<in>S. x \<le> y"
proof -
  have "S = {} \<or> (\<exists>x\<in>S. \<forall>y\<in>S. x \<le> y)"
  proof(rule finite_induct, simp_all add:assms)
    fix x::'a and S::"'a set"
    assume IH: "S = {} \<or> (\<exists>x\<in>S. \<forall>y\<in>S. x \<le> y)"
    show "(\<forall>y\<in>S. x \<le> y) \<or> (\<exists>x'\<in>S. x' \<le> x \<and> (\<forall>y\<in>S. x' \<le> y))"
    proof(cases "S={}")
      case True then show ?thesis by(auto)
    next
      case False with IH have "\<exists>x\<in>S. \<forall>y\<in>S. x \<le> y" by(auto)
      then obtain z where zin: "z \<in> S" and zmin: "\<forall>y\<in>S. z \<le> y" by(auto)
      thus ?thesis by(cases "z \<le> x", auto)
    qed
  qed
  with ne show ?thesis by(auto)
qed

lemma cSup_add:
  fixes c::real
  assumes ne: "S \<noteq> {}"
      and bS: "\<And>x. x\<in>S \<Longrightarrow> x \<le> b"
  shows "Sup S + c = Sup {x + c |x. x \<in> S}"
proof(rule antisym)
  from ne bS show "Sup {x + c |x. x \<in> S} \<le> Sup S + c"
    by(auto intro!:cSup_least add_right_mono cSup_upper bdd_aboveI)

  have "Sup S \<le> Sup {x + c |x. x \<in> S} - c"
  proof(intro cSup_least ne)
    fix x assume xin: "x \<in> S"
    from bS have "\<And>x. x\<in>S \<Longrightarrow> x + c \<le> b + c" by(auto intro:add_right_mono)
    hence "bdd_above {x + c |x. x \<in> S}" by(intro bdd_aboveI, blast)
    with xin have "x + c \<le> Sup {x + c |x. x \<in> S}" by(auto intro:cSup_upper)
    thus "x \<le> Sup {x + c |x. x \<in> S} - c" by(auto)
  qed
  thus "Sup S + c \<le> Sup {x + c |x. x \<in> S}" by(auto)
qed

lemma cSup_mult:
  fixes c::real
  assumes ne: "S \<noteq> {}"
      and bS: "\<And>x. x\<in>S \<Longrightarrow> x \<le> b"
      and nnc: "0 \<le> c"
  shows "c * Sup S = Sup {c * x |x. x \<in> S}"
proof(cases)
  assume "c = 0"
  moreover from ne have "\<exists>x. x \<in> S" by(auto)
  ultimately show ?thesis by(simp)
next
  assume cnz: "c \<noteq> 0"
  show ?thesis
  proof(rule antisym)
    from bS have baS: "bdd_above S" by(intro bdd_aboveI, auto)
    with ne nnc show "Sup {c * x |x. x \<in> S} \<le> c * Sup S"
      by(blast intro!:cSup_least mult_left_mono[OF cSup_upper])
    have "Sup S \<le> inverse c * Sup {c * x |x. x \<in> S}"
    proof(intro cSup_least ne)
      fix x assume xin: "x\<in>S"
      moreover from bS nnc have "\<And>x. x\<in>S \<Longrightarrow> c * x \<le> c * b" by(auto intro:mult_left_mono)
      ultimately have "c * x \<le> Sup {c * x |x. x \<in> S}"
        by(auto intro!:cSup_upper bdd_aboveI)
      moreover from nnc have "0 \<le> inverse c" by(auto)
      ultimately have "inverse c * (c * x) \<le> inverse c * Sup {c * x |x. x \<in> S}"
        by(auto intro:mult_left_mono)
      with cnz show "x \<le> inverse c * Sup {c * x |x. x \<in> S}"
        by(simp add:mult.assoc[symmetric])
    qed
    with nnc have "c * Sup S \<le> c * (inverse c * Sup {c * x |x. x \<in> S})"
      by(auto intro:mult_left_mono)
    with cnz show "c * Sup S \<le> Sup {c * x |x. x \<in> S}"
      by(simp add:mult.assoc[symmetric])
  qed
qed

lemma closure_contains_Sup:
  fixes S :: "real set"
  assumes neS: "S \<noteq> {}" and bS: "\<forall>x\<in>S. x \<le> B"
  shows "Sup S \<in> closure S"
proof -
  let ?T = "uminus ` S"
  from neS have neT: "?T \<noteq> {}" by(auto)
  from bS have bT: "\<forall>x\<in>?T. -B \<le> x" by(auto)
  hence bbT: "bdd_below ?T" by(intro bdd_belowI, blast)

  have "Sup S = - Inf ?T"
  proof(rule antisym)
    from neT bbT
    have "\<And>x. x\<in>S \<Longrightarrow> Inf (uminus ` S) \<le> -x"
      by(blast intro:cInf_lower)
    hence "\<And>x. x\<in>S \<Longrightarrow> -1 * -x \<le> -1 * Inf (uminus ` S)"
      by(rule mult_left_mono_neg, auto)
    hence lenInf: "\<And>x. x\<in>S \<Longrightarrow> x \<le> - Inf (uminus ` S)"
      by(simp)
    with neS bS show "Sup S \<le> - Inf ?T"
      by(blast intro:cSup_least)

    have "- Sup S \<le> Inf ?T"
    proof(rule cInf_greatest[OF neT])
      fix x assume "x \<in> uminus ` S"
      then obtain y where yin: "y \<in> S" and rwx: "x = -y" by(auto)
      from yin bS have "y \<le> Sup S"
        by(intro cSup_upper bdd_belowI, auto)
      hence "-1 * Sup S \<le> -1 * y"
        by(simp add:mult_left_mono_neg)
      with rwx show "- Sup S \<le> x" by(simp)
    qed
    hence "-1 * Inf ?T \<le> -1 * (- Sup S)"
      by(simp add:mult_left_mono_neg)
    thus "- Inf ?T \<le> Sup S" by(simp)
  qed
  also {
    from neT bbT have "Inf ?T \<in> closure ?T" by(rule closure_contains_Inf)
    hence "- Inf ?T \<in> uminus ` closure ?T" by(auto)
  }
  also {
    have "linear uminus" by(auto intro:linearI)
    hence "uminus ` closure ?T \<subseteq> closure (uminus ` ?T)"
      by(rule closure_linear_image_subset)
  }
  also {
    have "uminus ` ?T \<subseteq> S" by(auto)
    hence "closure (uminus ` ?T) \<subseteq> closure S" by(rule closure_mono)
  }
  finally show "Sup S \<in> closure S" .
qed

lemma tendsto_min:
  fixes x y::real
  assumes ta: "a \<longlonglongrightarrow> x"
      and tb: "b \<longlonglongrightarrow> y"
  shows "(\<lambda>i. min (a i) (b i)) \<longlonglongrightarrow> min x y"
proof(rule LIMSEQ_I, simp)
  fix e::real assume pe: "0 < e"

  from ta pe obtain noa where balla: "\<forall>n\<ge>noa. abs (a n - x) < e"
    by(auto dest:LIMSEQ_D)
  from tb pe obtain nob where ballb: "\<forall>n\<ge>nob. abs (b n - y) < e"
    by(auto dest:LIMSEQ_D)

  {
    fix n
    assume ge: "max noa nob \<le> n"
    hence gea: "noa \<le> n" and geb: "nob \<le> n" by(auto)
    have "abs (min (a n) (b n) - min x y) < e"
    proof cases
      assume le: "min (a n) (b n) \<le> min x y"
      show ?thesis
      proof cases
        assume "a n \<le> b n"
        hence rwmin: "min (a n) (b n) = a n" by(auto)
        with le have "a n \<le> min x y" by(simp)
        moreover from gea balla have "abs (a n - x) < e" by(simp)
        moreover have "min x y \<le> x" by(auto)
        ultimately have "abs (a n - min x y) < e" by(auto)
        with rwmin show "abs (min (a n) (b n) - min x y) < e" by(simp)
      next
        assume "\<not> a n \<le> b n"
        hence "b n \<le> a n" by(auto)
        hence rwmin: "min (a n) (b n) = b n" by(auto)
        with le have "b n \<le> min x y" by(simp)
        moreover from geb ballb have "abs (b n - y) < e" by(simp)
        moreover have "min x y \<le> y" by(auto)
        ultimately have "abs (b n - min x y) < e" by(auto)
        with rwmin show "abs (min (a n) (b n) - min x y) < e" by(simp)
      qed
    next
      assume "\<not> min (a n) (b n) \<le> min x y"
      hence le: "min x y \<le> min (a n) (b n)" by(auto)
      show ?thesis
      proof cases
        assume "x \<le> y"
        hence rwmin: "min x y = x" by(auto)
        with le have "x \<le> min (a n) (b n)" by(simp)
        moreover from gea balla have "abs (a n - x) < e" by(simp)
        moreover have "min (a n) (b n) \<le> a n" by(auto)
        ultimately have "abs (min (a n) (b n) - x) < e" by(auto)
        with rwmin show "abs (min (a n) (b n) - min x y) < e" by(simp)
      next
        assume "\<not> x \<le> y"
        hence "y \<le> x" by(auto)
        hence rwmin: "min x y = y" by(auto)
        with le have "y \<le> min (a n) (b n)" by(simp)
        moreover from geb ballb have "abs (b n - y) < e" by(simp)
        moreover have "min (a n) (b n) \<le> b n" by(auto)
        ultimately have "abs (min (a n) (b n) - y) < e" by(auto)
        with rwmin show "abs (min (a n) (b n) - min x y) < e" by(simp)
      qed
    qed
  }
  thus "\<exists>no. \<forall>n\<ge>no. \<bar>min (a n) (b n) - min x y\<bar> < e" by(blast)
qed

definition supp :: "('s \<Rightarrow> real) \<Rightarrow> 's set"
where "supp f = {x. f x \<noteq> 0}"

definition dist_remove :: "('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> real"
where "dist_remove p x = (\<lambda>y. if y=x then 0 else p y / (1 - p x))"

lemma supp_dist_remove:
  "p x \<noteq> 0 \<Longrightarrow> p x \<noteq> 1 \<Longrightarrow> supp (dist_remove p x) = supp p - {x}"
  by(auto simp:dist_remove_def supp_def)

lemma supp_empty:
  "supp f = {} \<Longrightarrow> f x = 0"
  by(simp add:supp_def)

lemma nsupp_zero:
  "x \<notin> supp f \<Longrightarrow> f x = 0"
  by(simp add:supp_def)

lemma sum_supp:
  fixes f::"'a::finite \<Rightarrow> real"
  shows "sum f (supp f) = sum f UNIV"
proof -
  have "sum f (UNIV - supp f) = 0"
    by(simp add:supp_def)
  hence "sum f (supp f) = sum f (UNIV - supp f) + sum f (supp f)"
    by(simp)
  also have "... = sum f UNIV"
    by(simp add:sum.subset_diff[symmetric])
  finally show ?thesis .
qed

subsection \<open>Truncated Subtraction\<close>
text_raw \<open>\label{s:trunc_sub}\<close>

definition
  tminus :: "real \<Rightarrow> real \<Rightarrow> real" (infixl "\<ominus>" 60)
where
  "x \<ominus> y = max (x - y) 0"

lemma minus_le_tminus[intro!,simp]:
  "a - b \<le> a \<ominus> b"
  unfolding tminus_def by(auto)

lemma tminus_cancel_1:
  "0 \<le> a \<Longrightarrow> a + 1 \<ominus> 1 = a"
  unfolding tminus_def by(simp)

lemma tminus_zero_imp_le:
  "x \<ominus> y \<le> 0 \<Longrightarrow> x \<le> y"
  by(simp add:tminus_def)

lemma tminus_zero[simp]:
  "0 \<le> x \<Longrightarrow> x \<ominus> 0 = x"
  by(simp add:tminus_def)

lemma tminus_left_mono:
  "a \<le> b \<Longrightarrow> a \<ominus> c \<le> b \<ominus> c"
  unfolding tminus_def
  by(case_tac "a \<le> c", simp_all)

lemma tminus_less:
  "\<lbrakk> 0 \<le> a; 0 \<le> b \<rbrakk> \<Longrightarrow> a \<ominus> b \<le> a"
  unfolding tminus_def by(force)

lemma tminus_left_distrib:
  assumes nna: "0 \<le> a"
  shows "a * (b \<ominus> c) = a * b \<ominus> a * c"
proof(cases "b \<le> c")
  case True note le = this
  hence "a * max (b - c) 0 = 0" by(simp add:max.absorb2)
  also {
    from nna le have "a * b \<le> a * c" by(blast intro:mult_left_mono)
    hence "0 = max (a * b - a * c) 0" by(simp add:max.absorb1)
  }
  finally show ?thesis by(simp add:tminus_def)
next
  case False hence le: "c \<le> b" by(auto)
  hence "a * max (b - c) 0 = a * (b - c)" by(simp only:max.absorb1)
  also {
    from nna le have "a * c \<le> a * b" by(blast intro:mult_left_mono)
    hence "a * (b - c) = max (a * b - a * c) 0" by(simp add:max.absorb1 field_simps)
  }
  finally show ?thesis by(simp add:tminus_def)
qed

lemma tminus_le[simp]:
  "b \<le> a \<Longrightarrow> a \<ominus> b = a - b"
  unfolding tminus_def by(simp)

lemma tminus_le_alt[simp]:
  "a \<le> b \<Longrightarrow> a \<ominus> b = 0"
  by(simp add:tminus_def)

lemma tminus_nle[simp]:
  "\<not>b \<le> a \<Longrightarrow> a \<ominus> b = 0"
  unfolding tminus_def by(simp)

lemma tminus_add_mono:
  "(a+b) \<ominus> (c+d) \<le> (a\<ominus>c) + (b\<ominus>d)"
proof(cases "0 \<le> a - c")
  case True note pac = this
  show ?thesis
  proof(cases "0 \<le> b - d")
    case True note pbd = this
    from pac and pbd have "(c + d) \<le> (a + b)" by(simp)
    with pac and pbd show ?thesis by(simp)
  next
    case False with pac show ?thesis
      by(cases "c + d \<le> a + b", auto)
  qed
next
  case False note nac = this
  show ?thesis
  proof(cases "0 \<le> b - d")
    case True with nac show ?thesis
      by(cases "c + d \<le> a + b", auto)
  next
    case False note nbd = this
    with nac have "\<not>(c + d) \<le> (a + b)" by(simp)
    with nac and nbd show ?thesis by(simp)
  qed
qed

lemma tminus_sum_mono:
  assumes fS: "finite S"
  shows "sum f S \<ominus> sum g S \<le> sum (\<lambda>x. f x \<ominus> g x) S"
        (is "?X S")
proof(rule finite_induct)
  from fS show "finite S" .

  show "?X {}" by(simp)

  fix x and F
  assume fF: "finite F" and xniF: "x \<notin> F"
     and IH: "?X F"
  have "f x + sum f F \<ominus> g x + sum g F \<le>
        (f x \<ominus> g x) + (sum f F \<ominus> sum g F)"
    by(rule tminus_add_mono)
  also from IH have "... \<le> (f x \<ominus> g x) + (\<Sum>x\<in>F. f x \<ominus> g x)"
    by(rule add_left_mono)
  finally show "?X (insert x F)"
    by(simp add:sum.insert[OF fF xniF])
qed

lemma tminus_nneg[simp,intro]:
  "0 \<le> a \<ominus> b"
  by(cases "b \<le> a", auto)

lemma tminus_right_antimono:
  assumes clb: "c \<le> b"
  shows "a \<ominus> b \<le> a \<ominus> c"
proof(cases "b \<le> a")
  case True
  moreover with clb have "c \<le> a" by(auto)
  moreover note clb
  ultimately show ?thesis by(simp)
next
  case False then show ?thesis by(simp)
qed

lemma min_tminus_distrib:
  "min a b \<ominus> c = min (a \<ominus> c) (b \<ominus> c)"
  unfolding tminus_def by(auto)

end
