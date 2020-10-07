(* Title:      Regular Algebras
   Author:     Simon Foster, Georg Struth
   Maintainer: Simon Foster <s.foster at york.ac.uk>
               Georg Struth <g.struth at sheffield.ac.uk>               
*)

section \<open>Pratt's Counterexamples\<close>

theory Pratts_Counterexamples
  imports Regular_Algebras
begin

text \<open>We create two regular algebra models due to Pratt~\cite{Pratt} which are used to
        distinguish K1 algebras from K1l and K1r algebras.\<close>

datatype pratt1 = 
  P1Bot ("\<bottom>\<^sub>1") |
  P1Nat nat ("[_]\<^sub>1") | 
  P1Infty ("\<infinity>\<^sub>1") |
  P1Top ("\<top>\<^sub>1")

datatype pratt2 = 
  P2Bot ("\<bottom>\<^sub>2") |
  P2Nat nat ("[_]\<^sub>2") | 
  P2Infty ("\<infinity>\<^sub>2") |
  P2Top ("\<top>\<^sub>2")

fun pratt1_max where
  "pratt1_max [x]\<^sub>1 [y]\<^sub>1 = [max x y]\<^sub>1" |
  "pratt1_max x \<bottom>\<^sub>1 = x" |
  "pratt1_max \<bottom>\<^sub>1 y = y" |
  "pratt1_max \<infinity>\<^sub>1 [y]\<^sub>1 = \<infinity>\<^sub>1" |
  "pratt1_max [y]\<^sub>1 \<infinity>\<^sub>1 = \<infinity>\<^sub>1" |
  "pratt1_max \<infinity>\<^sub>1 \<infinity>\<^sub>1 = \<infinity>\<^sub>1" |
  "pratt1_max \<top>\<^sub>1 x = \<top>\<^sub>1" |
  "pratt1_max x \<top>\<^sub>1 = \<top>\<^sub>1"

fun pratt1_plus :: "pratt1 \<Rightarrow> pratt1 \<Rightarrow> pratt1" (infixl "+\<^sub>1" 65) where
  "[x]\<^sub>1 +\<^sub>1 [y]\<^sub>1 = [x + y]\<^sub>1" |
  "\<bottom>\<^sub>1 +\<^sub>1 x = \<bottom>\<^sub>1" |
  "x +\<^sub>1 \<bottom>\<^sub>1 = \<bottom>\<^sub>1" |
  "\<infinity>\<^sub>1 +\<^sub>1 [0]\<^sub>1 = \<infinity>\<^sub>1" |
  "[0]\<^sub>1 +\<^sub>1 \<infinity>\<^sub>1 = \<infinity>\<^sub>1" |
  "\<infinity>\<^sub>1 +\<^sub>1 \<infinity>\<^sub>1 = \<top>\<^sub>1" | (* Can be adjusted to PInfty *)
  "\<top>\<^sub>1 +\<^sub>1 x = \<top>\<^sub>1" |
  "x +\<^sub>1 \<top>\<^sub>1 = \<top>\<^sub>1" |
  "[x]\<^sub>1 +\<^sub>1 \<infinity>\<^sub>1 = \<infinity>\<^sub>1" |
  "\<infinity>\<^sub>1 +\<^sub>1 x = \<top>\<^sub>1"

lemma plusl_top_infty: "\<top>\<^sub>1 +\<^sub>1 \<infinity>\<^sub>1 = \<top>\<^sub>1"
  by (simp)

lemma plusl_infty_top: "\<infinity>\<^sub>1 +\<^sub>1 \<top>\<^sub>1  = \<top>\<^sub>1"
  by (simp)

lemma plusl_bot_infty: "\<bottom>\<^sub>1 +\<^sub>1 \<infinity>\<^sub>1 = \<bottom>\<^sub>1"
  by (simp)

lemma plusl_infty_bot: "\<infinity>\<^sub>1 +\<^sub>1 \<bottom>\<^sub>1  = \<bottom>\<^sub>1"
  by (simp)

lemma plusl_zero_infty: "[0]\<^sub>1 +\<^sub>1 \<infinity>\<^sub>1 = \<infinity>\<^sub>1"
  by (simp)

lemma plusl_infty_zero: "\<infinity>\<^sub>1 +\<^sub>1 [0]\<^sub>1 = \<infinity>\<^sub>1"
  by (simp)

lemma plusl_infty_num [simp]: "x > 0 \<Longrightarrow> \<infinity>\<^sub>1 +\<^sub>1 [x]\<^sub>1 = \<top>\<^sub>1"
  by (case_tac x, simp_all)

lemma plusl_num_infty [simp]: "x > 0 \<Longrightarrow> [x]\<^sub>1 +\<^sub>1 \<infinity>\<^sub>1 = \<infinity>\<^sub>1"
  by (case_tac x, simp_all)

fun pratt2_max where
  "pratt2_max [x]\<^sub>2 [y]\<^sub>2 = [max x y]\<^sub>2" |
  "pratt2_max x \<bottom>\<^sub>2 = x" |
  "pratt2_max \<bottom>\<^sub>2 y = y" |
  "pratt2_max \<infinity>\<^sub>2 [y]\<^sub>2 = \<infinity>\<^sub>2" |
  "pratt2_max [y]\<^sub>2 \<infinity>\<^sub>2 = \<infinity>\<^sub>2" |
  "pratt2_max \<infinity>\<^sub>2 \<infinity>\<^sub>2 = \<infinity>\<^sub>2" |
  "pratt2_max \<top>\<^sub>2 x = \<top>\<^sub>2" |
  "pratt2_max x \<top>\<^sub>2 = \<top>\<^sub>2"

fun pratt2_plus :: "pratt2 \<Rightarrow> pratt2 \<Rightarrow> pratt2" (infixl "+\<^sub>2" 65) where
  "[x]\<^sub>2 +\<^sub>2 [y]\<^sub>2 = [x + y]\<^sub>2" |
  "\<bottom>\<^sub>2 +\<^sub>2 x = \<bottom>\<^sub>2" |
  "x +\<^sub>2 \<bottom>\<^sub>2 = \<bottom>\<^sub>2" |
  "\<infinity>\<^sub>2 +\<^sub>2 [0]\<^sub>2 = \<infinity>\<^sub>2" |
  "[0]\<^sub>2 +\<^sub>2 \<infinity>\<^sub>2 = \<infinity>\<^sub>2" |
  "\<infinity>\<^sub>2 +\<^sub>2 \<infinity>\<^sub>2 = \<top>\<^sub>2" | (* Can be adjusted to PInfty *)
  "\<top>\<^sub>2 +\<^sub>2 x = \<top>\<^sub>2" |
  "x +\<^sub>2 \<top>\<^sub>2 = \<top>\<^sub>2" |
  "x +\<^sub>2 \<infinity>\<^sub>2 = \<top>\<^sub>2" |
  "\<infinity>\<^sub>2 +\<^sub>2 [x]\<^sub>2 = \<infinity>\<^sub>2"

instantiation pratt1 :: selective_semiring
begin

  definition zero_pratt1_def:
    "0 \<equiv> \<bottom>\<^sub>1"

  definition one_pratt1_def:
    "1 \<equiv> [0]\<^sub>1"

  definition plus_pratt1_def:
    "x + y \<equiv> pratt1_max x y"

  definition times_pratt1_def:
    "x * y \<equiv> x +\<^sub>1 y"

  definition less_eq_pratt1_def:
    "(x::pratt1) \<le> y \<equiv> x + y = y"

  definition less_pratt1_def:
    "(x::pratt1) < y \<equiv> x \<le> y \<and> x \<noteq> y"

  instance
  proof
    fix x y z :: pratt1
    show "x + y + z = x + (y + z)"
      by (case_tac x, case_tac[!] y, case_tac[!] z, simp_all add: plus_pratt1_def)
    show "x + y = y + x"
      by (cases x, case_tac[!] y, simp_all add: plus_pratt1_def)
    show "x * y * z = x * (y * z)"
      apply (cases x, case_tac[!] y, case_tac[!] z, simp_all add: plus_pratt1_def times_pratt1_def)
      apply (rename_tac[!] n, case_tac[!] n, auto)
      apply (metis nat.exhaust plusl_zero_infty pratt1_plus.simps(14))
      apply (metis not0_implies_Suc plusl_infty_zero plusl_zero_infty pratt1_plus.simps(14))
      apply (metis neq0_conv plusl_num_infty plusl_zero_infty pratt1_plus.simps(15))
      apply (metis not0_implies_Suc plusl_infty_zero pratt1_plus.simps(15) pratt1_plus.simps(9))
      apply (metis not0_implies_Suc plusl_infty_zero pratt1_plus.simps(15) pratt1_plus.simps(9))
    done
    show "(x + y) * z = x * z + y * z"
      apply (cases x, case_tac[!] y, case_tac[!] z, simp_all add: plus_pratt1_def times_pratt1_def)
      apply (rename_tac[!] n, case_tac[!] n, auto)
      apply (metis neq0_conv plusl_num_infty plusl_zero_infty pratt1_max.simps(8))+
    done
    show "1 * x = x"
      by (cases x, simp_all add: one_pratt1_def times_pratt1_def)
    show "x * 1 = x"
      by (cases x, simp_all add: one_pratt1_def times_pratt1_def)
    show "0 + x = x"
      by (cases x, simp_all add: plus_pratt1_def zero_pratt1_def)
    show "0 * x = 0"
      by (cases x, simp_all add: times_pratt1_def zero_pratt1_def)
    show "x * 0 = 0"
      by (cases x, simp_all add: times_pratt1_def zero_pratt1_def)
    show "x \<le> y \<longleftrightarrow> x + y = y"
      by (metis less_eq_pratt1_def)
    show "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
      by (metis less_pratt1_def)
    show "x + y = x \<or> x + y = y"
      by (cases x, case_tac[!] y, simp_all add: plus_pratt1_def max_def)
    show "x * (y + z) = x * y + x * z"
      apply (cases x, case_tac[!] y, case_tac[!] z, simp_all add: plus_pratt1_def times_pratt1_def)
      apply (rename_tac[!] n, case_tac[!] n, auto)
      apply (metis nat.exhaust plusl_zero_infty pratt1_max.simps(7) pratt1_plus.simps(14))
      apply (metis neq0_conv plusl_num_infty plusl_zero_infty pratt1_max.simps(7))
      apply (metis nat.exhaust plusl_zero_infty pratt1_max.simps(6) pratt1_plus.simps(14))
      apply (metis neq0_conv plusl_num_infty plusl_zero_infty pratt1_max.simps(6))
      apply (metis neq0_conv plusl_infty_num plusl_infty_zero pratt1_max.simps(10) pratt1_max.simps(8))
      apply (metis not0_implies_Suc plusl_infty_zero pratt1_max.simps(11) pratt1_max.simps(13) pratt1_plus.simps(15))
    done 
  qed
end 

instance pratt1 :: dioid_one_zero ..

instantiation pratt2 :: selective_semiring
begin

  definition zero_pratt2_def:
    "0 \<equiv> \<bottom>\<^sub>2"

  definition one_pratt2_def:
    "1 \<equiv> [0]\<^sub>2"

  definition times_pratt2_def:
    "x * y \<equiv> x +\<^sub>2 y"

  definition plus_pratt2 :: "pratt2 \<Rightarrow> pratt2 \<Rightarrow> pratt2" where
    "plus_pratt2 x y \<equiv> pratt2_max x y"

  definition less_eq_pratt2_def:
    "(x::pratt2) \<le> y \<equiv> x + y = y"

  definition less_pratt2_def:
    "(x::pratt2) < y \<equiv> x \<le> y \<and> x \<noteq> y"

  instance
  proof
    fix x y z :: pratt2
    show "x + y + z = x + (y + z)"
      by (case_tac x, case_tac[!] y, case_tac[!] z, simp_all add: plus_pratt2_def)
    show "x + y = y + x"
      by (cases x, case_tac[!] y, simp_all add: plus_pratt2_def)
    show "x * y * z = x * (y * z)"
      apply (cases x, case_tac[!] y, case_tac[!] z, auto simp add: times_pratt2_def)
      apply (rename_tac[!] n, case_tac[!] n, auto)
      apply (metis not0_implies_Suc pratt2_plus.simps(14) pratt2_plus.simps(6) pratt2_plus.simps(7) pratt2_plus.simps(9))
      apply (metis not0_implies_Suc pratt2_plus.simps(14) pratt2_plus.simps(15) pratt2_plus.simps(7) pratt2_plus.simps(9))
      apply (metis not0_implies_Suc pratt2_plus.simps(15) pratt2_plus.simps(6))
      apply (metis not0_implies_Suc pratt2_plus.simps(15) pratt2_plus.simps(6))
    done
    show "(x + y) * z = x * z + y * z"
      apply (cases x, case_tac[!] y, case_tac[!] z, simp_all add: plus_pratt2_def times_pratt2_def)
      apply (rename_tac[!] n, case_tac[!] n, auto)
      apply (metis not0_implies_Suc pratt2_max.simps(10) pratt2_max.simps(8) pratt2_plus.simps(14) pratt2_plus.simps(7))
      apply (metis max_0L max_0R max.left_idem nat.exhaust pratt2_max.simps(11) 
                   pratt2_max.simps(13) pratt2_plus.simps(14) pratt2_plus.simps(7))
    done
    show "1 * x = x"
      by (cases x, simp_all add: one_pratt2_def times_pratt2_def)
    show "x * 1 = x"
      by (cases x, simp_all add: one_pratt2_def times_pratt2_def)
    show "0 + x = x"
      by (cases x, simp_all add: plus_pratt2_def zero_pratt2_def)
    show "0 * x = 0"
      by (cases x, simp_all add: times_pratt2_def zero_pratt2_def)
    show "x * 0 = 0"
      by (cases x, simp_all add: times_pratt2_def zero_pratt2_def)
    show "x \<le> y \<longleftrightarrow> x + y = y"
      by (metis less_eq_pratt2_def)
    show "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
      by (metis less_pratt2_def)
    show "x + y = x \<or> x + y = y"
      by (cases x, case_tac[!] y, simp_all add: plus_pratt2_def max_def)
    show "x * (y + z) = x * y + x * z"
      apply (cases x, case_tac[!] y, case_tac[!] z, simp_all add: plus_pratt2_def times_pratt2_def)
      apply (rename_tac[!] n, case_tac[!] n, auto)
      apply (metis not0_implies_Suc pratt2_max.simps(12) pratt2_max.simps(7) pratt2_plus.simps(14) pratt2_plus.simps(7))
      apply (metis nat.exhaust pratt2_max.simps(12) pratt2_max.simps(7) pratt2_plus.simps(14) pratt2_plus.simps(7))
      apply (metis not0_implies_Suc pratt2_max.simps(6) pratt2_max.simps(9) pratt2_plus.simps(14) pratt2_plus.simps(7))
      apply (metis nat.exhaust pratt2_max.simps(6) pratt2_max.simps(9) pratt2_plus.simps(14) pratt2_plus.simps(7))
      apply (metis not0_implies_Suc pratt2_max.simps(8) pratt2_plus.simps(15) pratt2_plus.simps(6))
      apply (metis not0_implies_Suc pratt2_max.simps(8) pratt2_plus.simps(15) pratt2_plus.simps(6))
    done
  qed
end 

lemma top_greatest: "x \<le> \<top>\<^sub>1"
  by (case_tac x, auto simp add: less_eq_pratt1_def plus_pratt1_def)
  
instantiation pratt1 :: star_op
begin

  definition star_pratt1 where
    "x\<^sup>\<star> \<equiv> if (x = \<bottom>\<^sub>1 \<or> x = [0]\<^sub>1) then [0]\<^sub>1 else \<top>\<^sub>1"
  instance ..
end

instantiation pratt2 :: star_op
begin
  definition star_pratt2 where
    "x\<^sup>\<star> \<equiv> if (x = \<bottom>\<^sub>2 \<or> x = [0]\<^sub>2) then [0]\<^sub>2 else \<top>\<^sub>2"
  instance ..
end

instance pratt1 :: K1r_algebra
proof
  fix x :: pratt1
  show "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
    by  (case_tac x, auto simp add: star_pratt1_def one_pratt1_def times_pratt1_def less_eq_pratt1_def plus_pratt1_def)
next
  fix x y :: pratt1
  show "y \<cdot> x \<le> y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
    apply (case_tac x, case_tac[!] y)
    apply (auto simp add:star_pratt1_def one_pratt1_def times_pratt1_def less_eq_pratt1_def plus_pratt1_def)
    apply (rename_tac n, case_tac n)
    apply (simp_all)
    by (metis not0_implies_Suc plusl_zero_infty pratt1.distinct(7) pratt1_max.simps(6) pratt1_plus.simps(14))
qed

instance pratt2 :: K1l_algebra
proof
  fix x :: pratt2
  show "1 + x\<cdot>x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (case_tac x, auto simp add: star_pratt2_def one_pratt2_def times_pratt2_def less_eq_pratt2_def plus_pratt2_def)
next
  fix x y :: pratt2
  show "x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"
    apply (case_tac x, case_tac[!] y)
    apply (auto simp add:star_pratt2_def one_pratt2_def times_pratt2_def less_eq_pratt2_def plus_pratt2_def)
    apply (rename_tac n, case_tac n)
    apply (simp_all)
    apply (rename_tac n, case_tac n)
    apply (auto simp add:star_pratt2_def one_pratt2_def times_pratt2_def less_eq_pratt2_def plus_pratt2_def)
  done
qed

lemma one_star_top: "[1]\<^sub>1\<^sup>\<star> = \<top>\<^sub>1"
  by (simp add:star_pratt1_def one_pratt1_def)

lemma pratt1_kozen_1l_counterexample:
  "\<exists> x y :: pratt1. \<not> (x \<cdot> y \<le> y \<and> x\<^sup>\<star> \<cdot> y \<le> y)"
proof -
  have "\<not> ([1]\<^sub>1 \<cdot> \<infinity>\<^sub>1 \<le> \<infinity>\<^sub>1 \<and> [1]\<^sub>1\<^sup>\<star> \<cdot> \<infinity>\<^sub>1 \<le> \<infinity>\<^sub>1)"
    by (auto simp add: star_pratt1_def times_pratt1_def less_eq_pratt1_def plus_pratt1_def)
  thus ?thesis
    by auto
qed

lemma pratt2_kozen_1r_counterexample:
  "\<exists> x y :: pratt2. \<not> (y \<cdot> x \<le> y \<and> y \<cdot> x\<^sup>\<star> \<le> y)"
proof -
  have "\<not> (\<infinity>\<^sub>2 \<cdot> [1]\<^sub>2 \<le> \<infinity>\<^sub>2 \<and> \<infinity>\<^sub>2 \<cdot> [1]\<^sub>2\<^sup>\<star> \<le> \<infinity>\<^sub>2)"
    by (auto simp add: star_pratt2_def times_pratt2_def less_eq_pratt2_def plus_pratt2_def)
  thus ?thesis
    by auto
qed

end
