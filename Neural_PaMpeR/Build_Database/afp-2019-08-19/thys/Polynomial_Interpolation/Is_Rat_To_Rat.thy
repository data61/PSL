(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Conversions to Rational Numbers\<close>

text \<open>We define a class which provides tests whether a number is rational, and
  a conversion from to rational numbers. 
  These conversion functions are principle the inverse functions of \emph{of-rat}, but
  they can be implemented for individual types more efficiently.
  
  Similarly, we define tests and conversions between integer and rational numbers.\<close>

theory Is_Rat_To_Rat
imports 
  Sqrt_Babylonian.Sqrt_Babylonian_Auxiliary
begin

class is_rat = field_char_0 +
  fixes is_rat :: "'a \<Rightarrow> bool"
  and to_rat :: "'a \<Rightarrow> rat"
  assumes is_rat[simp]: "is_rat x = (x \<in> \<rat>)"
  and to_rat: "to_rat x = (if x \<in> \<rat> then (THE y. x = of_rat y) else 0)"

lemma of_rat_to_rat[simp]: "x \<in> \<rat> \<Longrightarrow> of_rat (to_rat x) = x"
  unfolding to_rat Rats_def by auto

lemma to_rat_of_rat[simp]: "to_rat (of_rat x) = x" unfolding to_rat by simp

instantiation rat :: is_rat
begin
definition "is_rat_rat (x :: rat) = True"
definition "to_rat_rat (x :: rat) = x"
  instance
  by (intro_classes, auto simp: is_rat_rat_def to_rat_rat_def Rats_def)
end

text \<open>The definition for reals at the moment is not executable, but it will become
  executable after loading the real algebraic numbers theory.\<close>
instantiation real :: is_rat
begin
definition "is_rat_real (x :: real) = (x \<in> \<rat>)"
definition "to_rat_real (x :: real) = (if x \<in> \<rat> then (THE y. x = of_rat y) else 0)"
  instance by (intro_classes, auto simp: is_rat_real_def to_rat_real_def)
end

lemma of_nat_complex: "of_nat n = Complex (of_nat n) 0"
  by (simp add: complex_eqI)

lemma of_int_complex: "of_int z = Complex (of_int z) 0"
  by (simp add: complex_eq_iff)

lemma of_rat_complex: "of_rat q = Complex (of_rat q) 0"
proof -
  obtain d n where dn: "quotient_of q = (d,n)" by force
  from quotient_of_div[OF dn] have q: "q = of_int d / of_int n" by auto
  then have "of_rat q = complex_of_real (real_of_rat q) \<or> (0::complex) = of_int n \<or> 0 = real_of_int n"
    by (simp add: of_rat_divide q)
  then show ?thesis
    using Complex_eq_0 complex_of_real_def q by auto
qed

lemma complex_of_real_of_rat[simp]: "complex_of_real (real_of_rat q) = of_rat q"
  unfolding complex_of_real_def of_rat_complex by simp

lemma is_rat_complex_iff: "x \<in> \<rat> \<longleftrightarrow> Re x \<in> \<rat> \<and> Im x = 0"
proof
  assume "x \<in> \<rat>"
  then obtain q where x: "x = of_rat q" unfolding Rats_def by auto
  let ?y = "Complex (of_rat q) 0"
  have "x - ?y = 0" unfolding x by (simp add: Complex_eq)
  hence x: "x = ?y" by simp
  show "Re x \<in> \<rat> \<and> Im x = 0" unfolding x complex.sel by auto
next
  assume "Re x \<in> \<rat> \<and> Im x = 0"
  then obtain q where "Re x = of_rat q" "Im x = 0" unfolding Rats_def by auto
  hence "x = Complex (of_rat q) 0" by (metis complex_surj)
  thus "x \<in> \<rat>" by (simp add: Complex_eq)
qed
  
instantiation complex :: is_rat
begin
definition "is_rat_complex (x :: complex) = (is_rat (Re x) \<and> Im x = 0)"
definition "to_rat_complex (x :: complex) = (if is_rat (Re x) \<and> Im x = 0 then to_rat (Re x) else 0)"


instance proof (intro_classes, auto simp: is_rat_complex_def to_rat_complex_def is_rat_complex_iff)
  fix x
  assume r: "Re x \<in> \<rat>" and i: "Im x = 0"
  hence "x \<in> \<rat>" unfolding is_rat_complex_iff by auto
  then obtain y where x: "x = of_rat y" unfolding Rats_def by blast
  from this[unfolded of_rat_complex] have x: "x = Complex (real_of_rat y) 0" by auto
  show "to_rat (Re x) = (THE y. x = of_rat y)" 
    by (subst of_rat_eq_iff[symmetric, where 'a = real], unfold of_rat_to_rat[OF r] of_rat_complex,
    unfold x complex.sel, auto)
qed
end

lemma [code_unfold]: "(x \<in> \<rat>) = (is_rat x)" by simp

definition is_int_rat :: "rat \<Rightarrow> bool" where
  "is_int_rat x \<equiv> snd (quotient_of x) = 1"

definition int_of_rat :: "rat \<Rightarrow> int" where
  "int_of_rat x \<equiv> fst (quotient_of x)"

lemma is_int_rat[simp]: "is_int_rat x = (x \<in> \<int>)"
  unfolding is_int_rat_def Ints_def 
  by (metis Ints_def Ints_induct 
    quotient_of_int is_int_rat_def old.prod.exhaust quotient_of_inject rangeI snd_conv)

lemma int_of_rat[simp]: "int_of_rat (rat_of_int x) = x" "z \<in> \<int> \<Longrightarrow> rat_of_int (int_of_rat z) = z"
proof (force simp: int_of_rat_def)
  assume "z \<in> \<int>"
  thus "rat_of_int (int_of_rat z) = z" unfolding int_of_rat_def
    by (metis Ints_cases Pair_inject quotient_of_int surjective_pairing)
qed

lemma int_of_rat_0[simp]: "(int_of_rat x = 0) = (x = 0)" unfolding int_of_rat_def
  using quotient_of_div[of x] by (cases "quotient_of x", auto)

end
