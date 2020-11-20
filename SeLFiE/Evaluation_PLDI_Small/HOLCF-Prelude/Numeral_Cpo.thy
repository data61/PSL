section \<open>Cpo for Numerals\<close>

theory Numeral_Cpo
  imports HOLCF_Main
begin

class plus_cpo = plus + cpo +
  assumes cont_plus1: "cont (\<lambda>x::'a::{plus,cpo}. x + y)"
  assumes cont_plus2: "cont (\<lambda>y::'a::{plus,cpo}. x + y)"
begin

abbreviation plus_section :: "'a \<rightarrow> 'a \<rightarrow> 'a" ("'(+')") where
  "(+) \<equiv> \<Lambda> x y. x + y"

abbreviation plus_section_left :: "'a \<Rightarrow> 'a \<rightarrow> 'a" ("'(_+')") where
  "(x+) \<equiv> \<Lambda> y. x + y"

abbreviation plus_section_right :: "'a \<Rightarrow> 'a \<rightarrow> 'a" ("'(+_')") where
  "(+y) \<equiv> \<Lambda> x. x + y"

end

class minus_cpo = minus + cpo +
  assumes cont_minus1: "cont (\<lambda>x::'a::{minus,cpo}. x - y)"
  assumes cont_minus2: "cont (\<lambda>y::'a::{minus,cpo}. x - y)"
begin

abbreviation minus_section :: "'a \<rightarrow> 'a \<rightarrow> 'a" ("'(-')") where
  "(-) \<equiv> \<Lambda> x y. x - y"

abbreviation minus_section_left :: "'a \<Rightarrow> 'a \<rightarrow> 'a" ("'(_-')") where
  "(x-) \<equiv> \<Lambda> y. x - y"

abbreviation minus_section_right :: "'a \<Rightarrow> 'a \<rightarrow> 'a" ("'(-_')") where
  "(-y) \<equiv> \<Lambda> x. x - y"

end

class times_cpo = times + cpo +
  assumes cont_times1: "cont (\<lambda>x::'a::{times,cpo}. x * y)"
  assumes cont_times2: "cont (\<lambda>y::'a::{times,cpo}. x * y)"
begin

(*
This clashes with comment syntax
abbreviation times_section :: "'a \<rightarrow> 'a \<rightarrow> 'a" ("'(?')") where
  "(?) \<equiv> \<Lambda> x y. x * y"

abbreviation times_section_left :: "'a \<Rightarrow> 'a \<rightarrow> 'a" ("'(_?')") where
  "(x?) \<equiv> \<Lambda> y. x * y"

abbreviation times_section_right :: "'a \<Rightarrow> 'a \<rightarrow> 'a" ("'(?_')") where
  "(?y) \<equiv> \<Lambda> x. x - y"
*)
end


lemma cont2cont_plus [simp, cont2cont]:
  assumes "cont (\<lambda>x. f x)" and "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. f x + g x :: 'a::plus_cpo)"
  apply (rule cont_apply [OF assms(1) cont_plus1])
  apply (rule cont_apply [OF assms(2) cont_plus2])
  apply (rule cont_const)
  done

lemma cont2cont_minus [simp, cont2cont]:
  assumes "cont (\<lambda>x. f x)" and "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. f x - g x :: 'a::minus_cpo)"
  apply (rule cont_apply [OF assms(1) cont_minus1])
  apply (rule cont_apply [OF assms(2) cont_minus2])
  apply (rule cont_const)
  done

lemma cont2cont_times [simp, cont2cont]:
  assumes "cont (\<lambda>x. f x)" and "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. f x * g x :: 'a::times_cpo)"
  apply (rule cont_apply [OF assms(1) cont_times1])
  apply (rule cont_apply [OF assms(2) cont_times2])
  apply (rule cont_const)
  done

instantiation u :: ("{zero,cpo}") zero
begin
  definition "zero_u = up\<cdot>(0::'a)"
  instance ..
end

instantiation u :: ("{one,cpo}") one
begin
  definition "one_u = up\<cdot>(1::'a)"
  instance ..
end

instantiation u :: (plus_cpo) plus
begin
  definition "plus_u x y = (\<Lambda>(up\<cdot>a) (up\<cdot>b). up\<cdot>(a + b))\<cdot>x\<cdot>y" for x y :: "'a\<^sub>\<bottom>"
  instance ..
end

instantiation u :: (minus_cpo) minus
begin
  definition "minus_u x y = (\<Lambda>(up\<cdot>a) (up\<cdot>b). up\<cdot>(a - b))\<cdot>x\<cdot>y" for x y :: "'a\<^sub>\<bottom>"
  instance ..
end

instantiation u :: (times_cpo) times
begin
  definition "times_u x y = (\<Lambda>(up\<cdot>a) (up\<cdot>b). up\<cdot>(a * b))\<cdot>x\<cdot>y" for x y :: "'a\<^sub>\<bottom>"
  instance ..
end

lemma plus_u_strict [simp]:
  fixes x :: "_ u" shows "x + \<bottom> = \<bottom>" and "\<bottom> + x = \<bottom>"
  unfolding plus_u_def by (cases x, simp, simp)+

lemma minus_u_strict [simp]:
  fixes x :: "_ u" shows "x - \<bottom> = \<bottom>" and "\<bottom> - x = \<bottom>"
  unfolding minus_u_def by (cases x, simp_all)+

lemma times_u_strict [simp]:
  fixes x :: "_ u" shows "x * \<bottom> = \<bottom>" and "\<bottom> * x = \<bottom>"
  unfolding times_u_def by (cases x, simp_all)+

lemma plus_up_up [simp]: "up\<cdot>x + up\<cdot>y = up\<cdot>(x + y)"
  unfolding plus_u_def by simp

lemma minus_up_up [simp]: "up\<cdot>x - up\<cdot>y = up\<cdot>(x - y)"
  unfolding minus_u_def by simp

lemma times_up_up [simp]: "up\<cdot>x * up\<cdot>y = up\<cdot>(x * y)"
  unfolding times_u_def by simp

instance u :: (plus_cpo) plus_cpo
  by standard (simp_all add: plus_u_def)

instance u :: (minus_cpo) minus_cpo
  by standard (simp_all add: minus_u_def)

instance u :: (times_cpo) times_cpo
  by standard (simp_all add: times_u_def)

instance u :: ("{semigroup_add,plus_cpo}") semigroup_add
proof
  fix a b c :: "'a u"
  show "(a + b) + c = a + (b + c)"
    unfolding plus_u_def
    by (cases a; cases b; cases c) (simp_all add: add.assoc)
qed

instance u :: ("{ab_semigroup_add,plus_cpo}") ab_semigroup_add
proof
  fix a b :: "'a u"
  show "a + b = b + a"
    by (cases a; cases b) (simp_all add: add.commute)
qed

instance u :: ("{monoid_add,plus_cpo}") monoid_add
proof
  fix a :: "'a u"
  show "0 + a = a"
    unfolding zero_u_def by (cases a) simp_all
  show "a + 0 = a"
    unfolding zero_u_def by (cases a) simp_all
qed

instance u :: ("{comm_monoid_add,plus_cpo}") comm_monoid_add
proof
  fix a :: "'a u"
  show "0 + a = a"
    unfolding zero_u_def by (cases a) simp_all
qed

instance u :: ("{numeral, plus_cpo}") numeral ..

instance int :: plus_cpo
  by standard simp_all

instance int :: minus_cpo
  by standard simp_all

end
