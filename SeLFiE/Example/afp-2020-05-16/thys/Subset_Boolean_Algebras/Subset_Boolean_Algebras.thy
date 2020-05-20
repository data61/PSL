(* Title:      Subset Boolean Algebras
   Authors:    Walter Guttmann, Bernhard Möller
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

theory Subset_Boolean_Algebras

imports Stone_Algebras.P_Algebras

begin

section \<open>Boolean Algebras\<close>

text \<open>
We show that Isabelle/HOL's \<open>boolean_algebra\<close> class is equivalent to Huntington's axioms \cite{Huntington1933}.
See \cite{WamplerDoty2016} for related results.
\<close>

subsection \<open>Huntington's Axioms\<close>

text \<open>Definition 1\<close>

class huntington = sup + uminus +
  assumes associative: "x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
  assumes commutative: "x \<squnion> y = y \<squnion> x"
  assumes huntington: "x = -(-x \<squnion> y) \<squnion> -(-x \<squnion> -y)"
begin

lemma top_unique:
  "x \<squnion> -x = y \<squnion> -y"
proof -
  have "x \<squnion> -x = y \<squnion> -(--y \<squnion> -x) \<squnion> -(--y \<squnion> --x)"
    by (smt associative commutative huntington)
  thus ?thesis
    by (metis associative huntington)
qed

end

subsection \<open>Equivalence to \<open>boolean_algebra\<close> Class\<close>

text \<open>Definition 2\<close>

class extended = sup + inf + minus + uminus + bot + top + ord +
  assumes top_def: "top = (THE x . \<forall>y . x = y \<squnion> -y)" (* define without imposing uniqueness *)
  assumes bot_def: "bot = -(THE x . \<forall>y . x = y \<squnion> -y)"
  assumes inf_def: "x \<sqinter> y = -(-x \<squnion> -y)"
  assumes minus_def: "x - y = -(-x \<squnion> y)"
  assumes less_eq_def: "x \<le> y \<longleftrightarrow> x \<squnion> y = y"
  assumes less_def: "x < y \<longleftrightarrow> x \<squnion> y = y \<and> \<not> (y \<squnion> x = x)"

class huntington_extended = huntington + extended
begin

lemma top_char:
  "top = x \<squnion> -x"
  using top_def top_unique by auto

lemma bot_char:
  "bot = -top"
  by (simp add: bot_def top_def)

subclass boolean_algebra
proof
  show 1: "\<And>x y. (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_def less_eq_def)
  show 2: "\<And>x. x \<le> x"
  proof -
    fix x
    have "x \<squnion> top = top \<squnion> --x"
      by (metis (full_types) associative top_char)
    thus "x \<le> x"
      by (metis (no_types) associative huntington less_eq_def top_char)
  qed
  show 3: "\<And>x y z. x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (metis associative less_eq_def)
  show 4: "\<And>x y. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: commutative less_eq_def)
  show 5: "\<And>x y. x \<sqinter> y \<le> x"
    using 2 by (metis associative huntington inf_def less_eq_def)
  show 6: "\<And>x y. x \<sqinter> y \<le> y"
    using 5 commutative inf_def by fastforce
  show 8: "\<And>x y. x \<le> x \<squnion> y"
    using 2 associative less_eq_def by auto
  show 9: "\<And>y x. y \<le> x \<squnion> y"
    using 8 commutative by fastforce
  show 10: "\<And>y x z. y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (metis associative less_eq_def)
  show 11: "\<And>x. bot \<le> x"
    using 8 by (metis bot_char huntington top_char)
  show 12: "\<And>x. x \<le> top"
    using 6 11 by (metis huntington bot_def inf_def less_eq_def top_def)
  show 13: "\<And>x y z. x \<squnion> y \<sqinter> z = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
  proof -
    have 2: "\<And>x y z . x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
      by (simp add: associative)
    have 3: "\<And>x y z . (x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
      using 2 by metis
    have 4: "\<And>x y . x \<squnion> y = y \<squnion> x"
      by (simp add: commutative)
    have 5: "\<And>x y . x = - (- x \<squnion> y) \<squnion> - (- x \<squnion> - y)"
      by (simp add: huntington)
    have 6: "\<And>x y . - (- x \<squnion> y) \<squnion> - (- x \<squnion> - y) = x"
      using 5 by metis
    have 7: "\<And>x y . x \<sqinter> y = - (- x \<squnion> - y)"
      by (simp add: inf_def)
    have 10: "\<And>x y z . x \<squnion> (y \<squnion> z) = y \<squnion> (x \<squnion> z)"
      using 3 4 by metis
    have 11: "\<And>x y z . - (- x \<squnion> y) \<squnion> (- (- x \<squnion> - y) \<squnion> z) = x \<squnion> z"
      using 3 6 by metis
    have 12: "\<And>x y . - (x \<squnion> - y) \<squnion> - (- y \<squnion> - x) = y"
      using 4 6 by metis
    have 13: "\<And>x y . - (- x \<squnion> y) \<squnion> - (- y \<squnion> - x) = x"
      using 4 6 by metis
    have 14: "\<And>x y . - x \<squnion> - (- (- x \<squnion> y) \<squnion> - - (- x \<squnion> - y)) = - x \<squnion> y"
      using 6 by metis
    have 18: "\<And>x y z . - (x \<squnion> - y) \<squnion> (- (- y \<squnion> - x) \<squnion> z) = y \<squnion> z"
      using 3 12 by metis
    have 20: "\<And>x y . - (- x \<squnion> - y) \<squnion> - (y \<squnion> - x) = x"
      using 4 12 by metis
    have 21: "\<And>x y . - (x \<squnion> - y) \<squnion> - (- x \<squnion> - y) = y"
      using 4 12 by metis
    have 22: "\<And>x y . - x \<squnion> - (- (y \<squnion> - x) \<squnion> - - (- x \<squnion> - y)) = y \<squnion> - x"
      using 6 12 by metis
    have 23: "\<And>x y . - x \<squnion> - (- x \<squnion> (- y \<squnion> - (y \<squnion> - x))) = y \<squnion> - x"
      using 3 4 6 12 by metis
    have 24: "\<And>x y . - x \<squnion> - (- (- x \<squnion> - y) \<squnion> - - (- x \<squnion> y)) = - x \<squnion> - y"
      using 6 12 by metis
    have 28: "\<And>x y . - (- x \<squnion> - y) \<squnion> - (- y \<squnion> x) = y"
      using 4 13 by metis
    have 30: "\<And>x y . - x \<squnion> - (- y \<squnion> (- x \<squnion> - (- x \<squnion> y))) = - x \<squnion> y"
      using 3 4 6 13 by metis
    have 32: "\<And>x y z . - (- x \<squnion> y) \<squnion> (z \<squnion> - (- y \<squnion> - x)) = z \<squnion> x"
      using 10 13 by metis
    have 37: "\<And>x y z . - (- x \<squnion> - y) \<squnion> (- (y \<squnion> - x) \<squnion> z) = x \<squnion> z"
      using 3 20 by metis
    have 39: "\<And>x y z . - (- x \<squnion> - y) \<squnion> (z \<squnion> - (y \<squnion> - x)) = z \<squnion> x"
      using 10 20 by metis
    have 40: "\<And>x y z . - (x \<squnion> - y) \<squnion> (- (- x \<squnion> - y) \<squnion> z) = y \<squnion> z"
      using 3 21 by metis
    have 43: "\<And>x y . - x \<squnion> - (- y \<squnion> (- x \<squnion> - (y \<squnion> - x))) = y \<squnion> - x"
      using 3 4 6 21 by metis
    have 47: "\<And>x y z . - (x \<squnion> y) \<squnion> - (- (- x \<squnion> z) \<squnion> - (- (- x \<squnion> - z) \<squnion> y)) = - x \<squnion> z"
      using 6 11 by metis
    have 55: "\<And>x y . x \<squnion> - (- y \<squnion> - - x) = y \<squnion> - (- x \<squnion> y)"
      using 4 11 12 by metis
    have 58: "\<And>x y . x \<squnion> - (- - y \<squnion> - x) = x \<squnion> - (- x \<squnion> y)"
      using 4 11 13 by metis
    have 63: "\<And>x y . x \<squnion> - (- - x \<squnion> - y) = y \<squnion> - (- x \<squnion> y)"
      using 4 11 21 by metis
    have 71: "\<And>x y . x \<squnion> - (- y \<squnion> x) = y \<squnion> - (- x \<squnion> y)"
      using 4 11 28 by metis
    have 75: "\<And>x y . x \<squnion> - (- y \<squnion> x) = y \<squnion> - (y \<squnion> - x)"
      using 4 71 by metis
    have 78: "\<And>x y . - x \<squnion> (y \<squnion> - (- x \<squnion> (y \<squnion> - - (- x \<squnion> - y)))) = - x \<squnion> - (- x \<squnion> - y)"
      using 3 4 6 71 by metis
    have 86: "\<And>x y . - (- x \<squnion> - (- y \<squnion> x)) \<squnion> - (y \<squnion> - (- x \<squnion> y)) = - y \<squnion> x"
      using 4 20 71 by metis
    have 172: "\<And>x y . - x \<squnion> - (- x \<squnion> - y) = y \<squnion> - (- - x \<squnion> y)"
      using 14 75 by metis
    have 201: "\<And>x y . x \<squnion> - (- y \<squnion> - - x) = y \<squnion> - (y \<squnion> - x)"
      using 4 55 by metis
    have 236: "\<And>x y . x \<squnion> - (- - y \<squnion> - x) = x \<squnion> - (y \<squnion> - x)"
      using 4 58 by metis
    have 266: "\<And>x y . - x \<squnion> - (- (- x \<squnion> - (y \<squnion> - - x)) \<squnion> - - (- x \<squnion> - - (- - x \<squnion> y))) = - x \<squnion> - (- - x \<squnion> y)"
      using 14 58 236 by metis
    have 678: "\<And>x y z . - (- x \<squnion> - (- y \<squnion> x)) \<squnion> (- (y \<squnion> - (- x \<squnion> y)) \<squnion> z) = - y \<squnion> (x \<squnion> z)"
      using 3 4 37 71 by smt
    have 745: "\<And>x y z . - (- x \<squnion> - (- y \<squnion> x)) \<squnion> (z \<squnion> - (y \<squnion> - (- x \<squnion> y))) = z \<squnion> (- y \<squnion> x)"
      using 4 39 71 by metis
    have 800: "\<And>x y . - - x \<squnion> (- y \<squnion> (- (y \<squnion> - - x) \<squnion> - (- x \<squnion> (- - x \<squnion> (- y \<squnion> - (y \<squnion> - - x)))))) = x \<squnion> - (y \<squnion> - - x)"
      using 3 23 63 by metis
    have 944: "\<And>x y . x \<squnion> - (x \<squnion> - - (- (- x \<squnion> - y) \<squnion> - - (- x \<squnion> y))) = - (- x \<squnion> - y) \<squnion> - (- (- x \<squnion> - y) \<squnion> - - (- x \<squnion> y))"
      using 4 24 71 by metis
    have 948: "\<And>x y . - x \<squnion> - (- (y \<squnion> - (y \<squnion> - - x)) \<squnion> - - (- x \<squnion> (- y \<squnion> - x))) = - x \<squnion> - (- y \<squnion> - x)"
      using 24 75 by metis
    have 950: "\<And>x y . - x \<squnion> - (- (y \<squnion> - (- - x \<squnion> y)) \<squnion> - - (- x \<squnion> (- x \<squnion> - y))) = - x \<squnion> - (- x \<squnion> - y)"
      using 24 75 by metis
    have 961: "\<And>x y . - x \<squnion> - (- (y \<squnion> - (- - x \<squnion> y)) \<squnion> - - (- x \<squnion> (- - - x \<squnion> - y))) = y \<squnion> - (- - x \<squnion> y)"
      using 24 63 by metis
    have 966: "\<And>x y . - x \<squnion> - (- (y \<squnion> - (y \<squnion> - - x)) \<squnion> - - (- x \<squnion> (- y \<squnion> - - - x))) = y \<squnion> - (y \<squnion> - - x)"
      using 24 201 by metis
    have 969: "\<And>x y . - x \<squnion> - (- (- x \<squnion> - (y \<squnion> - - x)) \<squnion> - - (- x \<squnion> (- - y \<squnion> - - x))) = - x \<squnion> - (y \<squnion> - - x)"
      using 24 236 by metis
    have 1096: "\<And>x y z . - x \<squnion> (- (- x \<squnion> - y) \<squnion> z) = y \<squnion> (- (- - x \<squnion> y) \<squnion> z)"
      using 3 172 by metis
    have 1098: "\<And>x y z . - x \<squnion> (y \<squnion> - (- x \<squnion> - z)) = y \<squnion> (z \<squnion> - (- - x \<squnion> z))"
      using 10 172 by metis
    have 1105: "\<And>x y . x \<squnion> - x = y \<squnion> - y"
      using 4 10 12 32 172 by metis
    have 1109: "\<And>x y z . x \<squnion> (- x \<squnion> y) = z \<squnion> (- z \<squnion> y)"
      using 3 1105 by metis
    have 1110: "\<And>x y z . x \<squnion> - x = y \<squnion> (z \<squnion> - (y \<squnion> z))"
      using 3 1105 by metis
    have 1114: "\<And>x y . - (- x \<squnion> - - x) = - (y \<squnion> - y)"
      using 7 1105 by metis
    have 1115: "\<And>x y z . x \<squnion> (y \<squnion> - y) = z \<squnion> (x \<squnion> - z)"
      using 10 1105 by metis
    have 1117: "\<And>x y . - (x \<squnion> - - x) \<squnion> - (y \<squnion> - y) = - x"
      using 4 13 1105 by metis
    have 1121: "\<And>x y . - (x \<squnion> - x) \<squnion> - (y \<squnion> - - y) = - y"
      using 4 28 1105 by metis
    have 1122: "\<And>x . - - x = x"
      using 4 28 1105 1117 by metis
    have 1134: "\<And>x y z . - (x \<squnion> - y) \<squnion> (z \<squnion> - z) = y \<squnion> (- y \<squnion> - x)"
      using 18 1105 1122 by metis
    have 1140: "\<And>x . - x \<squnion> - (x \<squnion> (x \<squnion> - x)) = - x \<squnion> - x"
      using 4 22 1105 1122 1134 by metis
    have 1143: "\<And>x y . x \<squnion> (- x \<squnion> y) = y \<squnion> (x \<squnion> - y)"
      using 37 1105 1122 1134 by metis
    have 1155: "\<And>x y . - (x \<squnion> - x) \<squnion> - (y \<squnion> y) = - y"
      using 1121 1122 by metis
    have 1156: "\<And>x y . - (x \<squnion> x) \<squnion> - (y \<squnion> - y) = - x"
      using 1117 1122 by metis
    have 1157: "\<And>x y . - (x \<squnion> - x) = - (y \<squnion> - y)"
      using 4 1114 1122 by metis
    have 1167: "\<And>x y z . - x \<squnion> (y \<squnion> - (- x \<squnion> - z)) = y \<squnion> (z \<squnion> - (x \<squnion> z))"
      using 1098 1122 by metis
    have 1169: "\<And>x y z . - x \<squnion> (- (- x \<squnion> - y) \<squnion> z) = y \<squnion> (- (x \<squnion> y) \<squnion> z)"
      using 1096 1122 by metis
    have 1227: "\<And>x y . - x \<squnion> - (- x \<squnion> (y \<squnion> (x \<squnion> - (- x \<squnion> - (y \<squnion> x))))) = - x \<squnion> - (y \<squnion> x)"
      using 3 4 969 1122 by smt
    have 1230: "\<And>x y . - x \<squnion> - (- x \<squnion> (- y \<squnion> (- x \<squnion> - (y \<squnion> - (y \<squnion> x))))) = y \<squnion> - (y \<squnion> x)"
      using 3 4 966 1122 by smt
    have 1234: "\<And>x y . - x \<squnion> - (- x \<squnion> (- x \<squnion> (- y \<squnion> - (y \<squnion> - (x \<squnion> y))))) = y \<squnion> - (x \<squnion> y)"
      using 3 4 961 1122 by metis
    have 1239: "\<And>x y . - x \<squnion> - (- x \<squnion> - y) = y \<squnion> - (x \<squnion> y)"
      using 3 4 950 1122 1234 by metis
    have 1240: "\<And>x y . - x \<squnion> - (- y \<squnion> - x) = y \<squnion> - (y \<squnion> x)"
      using 3 4 948 1122 1230 by metis
    have 1244: "\<And>x y . x \<squnion> - (x \<squnion> (y \<squnion> (y \<squnion> - (x \<squnion> y)))) = - (- x \<squnion> - y) \<squnion> - (y \<squnion> (y \<squnion> - (x \<squnion> y)))"
      using 3 4 944 1122 1167 by metis
    have 1275: "\<And>x y . x \<squnion> (- y \<squnion> (- (y \<squnion> x) \<squnion> - (x \<squnion> (- x \<squnion> (- y \<squnion> - (y \<squnion> x)))))) = x \<squnion> - (y \<squnion> x)"
      using 10 800 1122 by metis
    have 1346: "\<And>x y . - x \<squnion> - (x \<squnion> (y \<squnion> (y \<squnion> (x \<squnion> - (x \<squnion> (y \<squnion> x)))))) = - x \<squnion> - (x \<squnion> y)"
      using 3 4 10 266 1122 1167 by smt
    have 1377: "\<And>x y . - x \<squnion> (y \<squnion> - (- x \<squnion> (y \<squnion> (- x \<squnion> - y)))) = y \<squnion> - (x \<squnion> y)"
      using 78 1122 1239 by metis
    have 1394: "\<And>x y . - (- x \<squnion> - y) \<squnion> - (y \<squnion> (y \<squnion> (- x \<squnion> - (x \<squnion> y)))) = x"
      using 3 4 10 20 30 1122 1239 by smt
    have 1427: "\<And>x y . - (- x \<squnion> - y) \<squnion> - (y \<squnion> - (x \<squnion> (x \<squnion> - (x \<squnion> y)))) = x \<squnion> (x \<squnion> - (x \<squnion> y))"
      using 3 4 30 40 1240 by smt
    have 1436: "\<And>x . - x \<squnion> - (x \<squnion> (x \<squnion> (- x \<squnion> - x))) = - x \<squnion> (- x \<squnion> - (x \<squnion> - x))"
      using 3 4 30 1140 1239 by smt
    have 1437: "\<And>x y . - (x \<squnion> y) \<squnion> - (x \<squnion> - y) = - x"
      using 6 1122 by metis
    have 1438: "\<And>x y . - (x \<squnion> y) \<squnion> - (y \<squnion> - x) = - y"
      using 12 1122 by metis
    have 1439: "\<And>x y . - (x \<squnion> y) \<squnion> - (- y \<squnion> x) = - x"
      using 13 1122 by metis
    have 1440: "\<And>x y . - (x \<squnion> - y) \<squnion> - (y \<squnion> x) = - x"
      using 20 1122 by metis
    have 1441: "\<And>x y . - (x \<squnion> y) \<squnion> - (- x \<squnion> y) = - y"
      using 21 1122 by metis
    have 1568: "\<And>x y . x \<squnion> (- y \<squnion> - x) = y \<squnion> (- y \<squnion> x)"
      using 10 1122 1143 by metis
    have 1598: "\<And>x . - x \<squnion> - (x \<squnion> (x \<squnion> (x \<squnion> - x))) = - x \<squnion> (- x \<squnion> - (x \<squnion> - x))"
      using 4 1436 1568 by metis
    have 1599: "\<And>x y . - x \<squnion> (y \<squnion> - (x \<squnion> (- x \<squnion> (- x \<squnion> y)))) = y \<squnion> - (x \<squnion> y)"
      using 10 1377 1568 by smt
    have 1617: "\<And>x . x \<squnion> (- x \<squnion> (- x \<squnion> - (x \<squnion> - x))) = x \<squnion> - x"
      using 3 4 10 71 1122 1155 1568 1598 by metis
    have 1632: "\<And>x y z . - (x \<squnion> - x) \<squnion> - (- y \<squnion> (- (z \<squnion> - z) \<squnion> - (y \<squnion> - (x \<squnion> - x)))) = y \<squnion> - (x \<squnion> - x)"
      using 43 1157 by metis
    have 1633: "\<And>x y z . - (x \<squnion> - x) \<squnion> - (- y \<squnion> (- (x \<squnion> - x) \<squnion> - (y \<squnion> - (z \<squnion> - z)))) = y \<squnion> - (x \<squnion> - x)"
      using 43 1157 by metis
    have 1636: "\<And>x y . x \<squnion> - (y \<squnion> (- y \<squnion> - (x \<squnion> x))) = x \<squnion> x"
      using 43 1109 1122 by metis
    have 1645: "\<And>x y . x \<squnion> - x = y \<squnion> (y \<squnion> - y)"
      using 3 1110 1156 by metis
    have 1648: "\<And>x y z . - (x \<squnion> (y \<squnion> (- y \<squnion> - x))) \<squnion> - (z \<squnion> - z) = - (y \<squnion> - y)"
      using 3 1115 1156 by metis
    have 1657: "\<And>x y z . x \<squnion> - x = y \<squnion> (z \<squnion> - z)"
      using 1105 1645 by metis
    have 1664: "\<And>x y z . x \<squnion> - x = y \<squnion> (z \<squnion> - y)"
      using 1115 1645 by metis
    have 1672: "\<And>x y z . x \<squnion> - x = y \<squnion> (- y \<squnion> z)"
      using 3 4 1657 by metis
    have 1697: "\<And>x y z . - x \<squnion> (y \<squnion> x) = z \<squnion> - z"
      using 1122 1664 by metis
    have 1733: "\<And>x y z . - (x \<squnion> y) \<squnion> - (- (z \<squnion> - z) \<squnion> - (- (- x \<squnion> - x) \<squnion> y)) = x \<squnion> - x"
      using 4 47 1105 1122 by metis
    have 1791: "\<And>x y z . x \<squnion> - (y \<squnion> (- y \<squnion> z)) = x \<squnion> - (x \<squnion> - x)"
      using 4 71 1122 1672 by metis
    have 1818: "\<And>x y z . x \<squnion> - (- y \<squnion> (z \<squnion> y)) = x \<squnion> - (x \<squnion> - x)"
      using 4 71 1122 1697 by metis
    have 1861: "\<And>x y z . - (x \<squnion> - x) \<squnion> - (y \<squnion> - (z \<squnion> - z)) = - y"
      using 1437 1657 by metis
    have 1867: "\<And>x y z . - (x \<squnion> - x) \<squnion> - (- y \<squnion> - (z \<squnion> y)) = y"
      using 1122 1437 1697 by metis
    have 1868: "\<And>x y . x \<squnion> - (y \<squnion> - y) = x"
      using 1122 1155 1633 1861 by metis
    have 1869: "\<And>x y z . - (x \<squnion> - x) \<squnion> - (- y \<squnion> (- (z \<squnion> - z) \<squnion> - y)) = y"
      using 1632 1868 by metis
    have 1870: "\<And>x y . - (x \<squnion> - x) \<squnion> - y = - y"
      using 1861 1868 by metis
    have 1872: "\<And>x y z . x \<squnion> - (- y \<squnion> (z \<squnion> y)) = x"
      using 1818 1868 by metis
    have 1875: "\<And>x y z . x \<squnion> - (y \<squnion> (- y \<squnion> z)) = x"
      using 1791 1868 by metis
    have 1883: "\<And>x y . - (x \<squnion> (y \<squnion> (- y \<squnion> - x))) = - (y \<squnion> - y)"
      using 1648 1868 by metis
    have 1885: "\<And>x . x \<squnion> (x \<squnion> - x) = x \<squnion> - x"
      using 4 1568 1617 1868 by metis
    have 1886: "\<And>x . - x \<squnion> - x = - x"
      using 1598 1868 1885 by metis
    have 1890: "\<And>x . - (x \<squnion> x) = - x"
      using 1156 1868 by metis
    have 1892: "\<And>x y . - (x \<squnion> - x) \<squnion> y = y"
      using 1122 1869 1870 1886 by metis
    have 1893: "\<And>x y . - (- x \<squnion> - (y \<squnion> x)) = x"
      using 1867 1892 by metis
    have 1902: "\<And>x y . x \<squnion> (y \<squnion> - (x \<squnion> y)) = x \<squnion> - x"
      using 3 4 1122 1733 1886 1892 by metis
    have 1908: "\<And>x . x \<squnion> x = x"
      using 1636 1875 1890 by metis
    have 1910: "\<And>x y . x \<squnion> - (y \<squnion> x) = - y \<squnion> x"
      using 1599 1875 by metis
    have 1921: "\<And>x y . x \<squnion> (- y \<squnion> - (y \<squnion> x)) = - y \<squnion> x"
      using 1275 1875 1910 by metis
    have 1951: "\<And>x y . - x \<squnion> - (y \<squnion> x) = - x"
      using 1227 1872 1893 1908 by metis
    have 1954: "\<And>x y z . x \<squnion> (y \<squnion> - (x \<squnion> z)) = y \<squnion> (- z \<squnion> x)"
      using 745 1122 1910 1951 by metis
    have 1956: "\<And>x y z . x \<squnion> (- (x \<squnion> y) \<squnion> z) = - y \<squnion> (x \<squnion> z)"
      using 678 1122 1910 1951 by metis
    have 1959: "\<And>x y . x \<squnion> - (x \<squnion> y) = - y \<squnion> x"
      using 86 1122 1910 1951 by metis
    have 1972: "\<And>x y . x \<squnion> (- x \<squnion> y) = x \<squnion> - x"
      using 1902 1910 by metis
    have 2000: "\<And>x y . - (- x \<squnion> - y) \<squnion> - (y \<squnion> (- x \<squnion> y)) = x \<squnion> - (y \<squnion> (- x \<squnion> y))"
      using 4 1244 1910 1959 by metis
    have 2054: "\<And>x y . x \<squnion> - (y \<squnion> (- x \<squnion> y)) = x"
      using 1394 1921 2000 by metis
    have 2057: "\<And>x y . - (x \<squnion> (y \<squnion> - y)) = - (y \<squnion> - y)"
      using 1883 1972 by metis
    have 2061: "\<And>x y . x \<squnion> (- y \<squnion> x) = x \<squnion> - y"
      using 4 1122 1427 1910 1959 2054 by metis
    have 2090: "\<And>x y z . x \<squnion> (- (y \<squnion> x) \<squnion> z) = x \<squnion> (- y \<squnion> z)"
      using 1122 1169 1956 by metis
    have 2100: "\<And>x y . - x \<squnion> - (x \<squnion> y) = - x"
      using 4 1346 1868 1885 1910 1959 1972 2057 by metis
    have 2144: "\<And>x y . x \<squnion> - (y \<squnion> - x) = x"
      using 1122 1440 2000 2061 by metis
    have 2199: "\<And>x y . x \<squnion> (x \<squnion> y) = x \<squnion> y"
      using 3 1908 by metis
    have 2208: "\<And>x y z . x \<squnion> (- (y \<squnion> - x) \<squnion> z) = x \<squnion> z"
      using 3 2144 by metis
    have 2349: "\<And>x y z . - (x \<squnion> y) \<squnion> - (x \<squnion> (y \<squnion> z)) = - (x \<squnion> y)"
      using 3 2100 by metis
    have 2432: "\<And>x y z . - (x \<squnion> (y \<squnion> z)) \<squnion> - (y \<squnion> (z \<squnion> - x)) = - (y \<squnion> z)"
      using 3 1438 by metis
    have 2530: "\<And>x y z . - (- (x \<squnion> y) \<squnion> z) = - (y \<squnion> (- x \<squnion> z)) \<squnion> - (- y \<squnion> z)"
      using 4 1122 1439 2090 2208 by smt
    have 3364: "\<And>x y z . - (- x \<squnion> y) \<squnion> (z \<squnion> - (x \<squnion> y)) = z \<squnion> - y"
      using 3 4 1122 1441 1910 1954 2199 by metis
    have 5763: "\<And>x y z . - (x \<squnion> y) \<squnion> - (- x \<squnion> (y \<squnion> z)) = - (x \<squnion> y) \<squnion> - (y \<squnion> z)"
      using 4 2349 3364 by metis
    have 6113: "\<And>x y z . - (x \<squnion> (y \<squnion> z)) \<squnion> - (z \<squnion> - x) = - (y \<squnion> z) \<squnion> - (z \<squnion> - x)"
      using 4 2432 3364 5763 by metis
    show "\<And>x y z. x \<squnion> y \<sqinter> z = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
    proof -
      fix x y z
      have "- (y \<sqinter> z \<squnion> x) = - (- (- y \<squnion> z) \<squnion> - (- y \<squnion> - z) \<squnion> x) \<squnion> - (x \<squnion> - - z)"
        using 1437 2530 6113 by (smt commutative inf_def)
      thus "x \<squnion> y \<sqinter> z = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
        using 12 1122 by (metis commutative inf_def)
    qed
  qed
  show 14: "\<And>x. x \<sqinter> - x = bot"
  proof -
    fix x
    have "(bot \<squnion> x) \<sqinter> (bot \<squnion> -x) = bot"
      using huntington bot_def inf_def by auto
    thus "x \<sqinter> -x = bot"
      using 11 less_eq_def by force
  qed
  show 15: "\<And>x. x \<squnion> - x = top"
    using 5 14 by (metis (no_types, lifting) huntington bot_def less_eq_def top_def)
  show 16: "\<And>x y. x - y = x \<sqinter> - y"
    using 15 by (metis commutative huntington inf_def minus_def)
  show 7: "\<And>x y z. x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (simp add: 13 less_eq_def)
qed

end

context boolean_algebra
begin

sublocale ba_he: huntington_extended
proof
  show "\<And>x y z. x \<squnion> (y \<squnion> z) = x \<squnion> y \<squnion> z"
    by (simp add: sup_assoc)
  show "\<And>x y. x \<squnion> y = y \<squnion> x"
    by (simp add: sup_commute)
  show "\<And>x y. x = - (- x \<squnion> y) \<squnion> - (- x \<squnion> - y)"
    by simp
  show "top = (THE x. \<forall>y. x = y \<squnion> - y)"
    by auto
  show "bot = - (THE x. \<forall>y. x = y \<squnion> - y)"
    by auto
  show "\<And>x y. x \<sqinter> y = - (- x \<squnion> - y)"
    by simp
  show "\<And>x y. x - y = - (- x \<squnion> y)"
    by (simp add: diff_eq)
  show "\<And>x y. (x \<le> y) = (x \<squnion> y = y)"
    by (simp add: le_iff_sup)
  show "\<And>x y. (x < y) = (x \<squnion> y = y \<and> y \<squnion> x \<noteq> x)"
    using sup.strict_order_iff sup_commute by auto
qed

end

subsection \<open>Stone Algebras\<close>

text \<open>
We relate Stone algebras to Boolean algebras.
\<close>

class stone_algebra_extended = stone_algebra + minus +
  assumes stone_minus_def[simp]: "x - y = x \<sqinter> -y"

class regular_stone_algebra = stone_algebra_extended +
  assumes double_complement[simp]: "--x = x"
begin

subclass boolean_algebra
proof
  show "\<And>x. x \<sqinter> - x = bot"
    by simp
  show "\<And>x. x \<squnion> - x = top"
    using regular_dense_top by fastforce
  show "\<And>x y. x - y = x \<sqinter> - y"
    by simp
qed

end

context boolean_algebra
begin

sublocale ba_rsa: regular_stone_algebra
proof
  show "\<And>x y. x - y = x \<sqinter> - y"
    by (simp add: diff_eq)
  show "\<And>x. - - x = x"
    by simp
qed

end

section \<open>Alternative Axiomatisations of Boolean Algebras\<close>

text \<open>
We consider four axiomatisations of Boolean algebras based only on join and complement.
The first three are from the literature and the fourth, a version using equational axioms, is new.
The motivation for Byrne's and the new axiomatisation is that the axioms are easier to understand than Huntington's third axiom.
We also include Meredith's axiomatisation.
\<close>

subsection \<open>Lee Byrne's Formulation A\<close>

text \<open>
The following axiomatisation is from \cite[Formulation A]{Byrne1946}; see also \cite{Frink1941}.
\<close>

text \<open>Theorem 3\<close>

class boolean_algebra_1 = sup + uminus +
  assumes ba1_associative: "x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
  assumes ba1_commutative: "x \<squnion> y = y \<squnion> x"
  assumes ba1_complement: "x \<squnion> -y = z \<squnion> -z \<longleftrightarrow> x \<squnion> y = x"
begin

subclass huntington
proof
  show 1: "\<And>x y z. x \<squnion> (y \<squnion> z) = x \<squnion> y \<squnion> z"
    by (simp add: ba1_associative)
  show "\<And>x y. x \<squnion> y = y \<squnion> x"
    by (simp add: ba1_commutative)
  show "\<And>x y. x = - (- x \<squnion> y) \<squnion> - (- x \<squnion> - y)"
  proof -
    have 2: "\<forall>x y. y \<squnion> (y \<squnion> x) = y \<squnion> x"
      using 1 by (metis ba1_complement)
    hence "\<forall>x. --x = x"
      by (smt ba1_associative ba1_commutative ba1_complement)
    hence "\<forall>x y. y \<squnion> -(y \<squnion> -x) = y \<squnion> x"
      by (smt ba1_associative ba1_commutative ba1_complement)
    thus "\<And>x y. x = -(-x \<squnion> y) \<squnion> -(-x \<squnion> - y)"
      using 2 by (smt ba1_commutative ba1_complement)
  qed
qed

end

context huntington
begin

sublocale h_ba1: boolean_algebra_1
proof
  show "\<And>x y z. x \<squnion> (y \<squnion> z) = x \<squnion> y \<squnion> z"
    by (simp add: associative)
  show "\<And>x y. x \<squnion> y = y \<squnion> x"
    by (simp add: commutative)
  show "\<And>x y z. (x \<squnion> - y = z \<squnion> - z) = (x \<squnion> y = x)"
  proof
    fix x y z
    have 1: "\<And>x y z. -(-x \<squnion> y) \<squnion> (-(-x \<squnion> -y) \<squnion> z) = x \<squnion> z"
      using associative huntington by force
    have 2: "\<And>x y. -(x \<squnion> -y) \<squnion> -(-y \<squnion> -x) = y"
      by (metis commutative huntington)
    show "x \<squnion> - y = z \<squnion> - z \<Longrightarrow> x \<squnion> y = x"
      by (metis 1 2 associative commutative top_unique)
    show "x \<squnion> y = x \<Longrightarrow> x \<squnion> - y = z \<squnion> - z"
      by (metis associative huntington commutative top_unique)
  qed
qed

end

subsection \<open>Lee Byrne's Formulation B\<close>

text \<open>
The following axiomatisation is from \cite[Formulation B]{Byrne1946}.
\<close>

text \<open>Theorem 4\<close>

class boolean_algebra_2 = sup + uminus +
  assumes ba2_associative_commutative: "(x \<squnion> y) \<squnion> z = (y \<squnion> z) \<squnion> x"
  assumes ba2_complement: "x \<squnion> -y = z \<squnion> -z \<longleftrightarrow> x \<squnion> y = x"
begin

subclass boolean_algebra_1
proof
  show "\<And>x y z. x \<squnion> (y \<squnion> z) = x \<squnion> y \<squnion> z"
    by (smt ba2_associative_commutative ba2_complement)
  show "\<And>x y. x \<squnion> y = y \<squnion> x"
    by (metis ba2_associative_commutative ba2_complement)
  show "\<And>x y z. (x \<squnion> - y = z \<squnion> - z) = (x \<squnion> y = x)"
    by (simp add: ba2_complement)
qed

end

context boolean_algebra_1
begin

sublocale ba1_ba2: boolean_algebra_2
proof
  show "\<And>x y z. x \<squnion> y \<squnion> z = y \<squnion> z \<squnion> x"
    using ba1_associative commutative by force
  show "\<And>x y z. (x \<squnion> - y = z \<squnion> - z) = (x \<squnion> y = x)"
    by (simp add: ba1_complement)
qed

end

subsection \<open>Meredith's Equational Axioms\<close>

text \<open>
The following axiomatisation is from \cite[page 221 (1) \{A,N\}]{MeredithPrior1968}.
\<close>

class boolean_algebra_mp = sup + uminus +
  assumes ba_mp_1: "-(-x \<squnion> y) \<squnion> x = x"
  assumes ba_mp_2: "-(-x \<squnion> y) \<squnion> (z \<squnion> y) = y \<squnion> (z \<squnion> x)"
begin

subclass huntington
proof
  show "\<And>x y z. x \<squnion> (y \<squnion> z) = x \<squnion> y \<squnion> z"
    by (metis ba_mp_1 ba_mp_2)
  show "\<And>x y. x \<squnion> y = y \<squnion> x"
    by (metis ba_mp_1 ba_mp_2)
  show "\<And>x y. x = - (- x \<squnion> y) \<squnion> - (- x \<squnion> - y)"
    by (metis ba_mp_1 ba_mp_2)
qed

end

context huntington
begin

sublocale mp_h: boolean_algebra_mp
proof
  show 1: "\<And>x y. - (- x \<squnion> y) \<squnion> x = x"
    by (metis h_ba1.ba1_associative h_ba1.ba1_complement huntington)
  show "\<And>x y z. - (- x \<squnion> y) \<squnion> (z \<squnion> y) = y \<squnion> (z \<squnion> x)"
  proof -
    fix x y z
    have "y = -(-x \<squnion> -y) \<squnion> y"
      using 1 h_ba1.ba1_commutative by auto
    thus "-(-x \<squnion> y) \<squnion> (z \<squnion> y) = y \<squnion> (z \<squnion> x)"
      by (metis h_ba1.ba1_associative h_ba1.ba1_commutative huntington)
  qed
qed

end

subsection \<open>An Equational Axiomatisation based on Semilattices\<close>

text \<open>
The following version is an equational axiomatisation based on semilattices.
We add the double complement rule and that \<open>top\<close> is unique.
The final axiom \<open>ba3_export\<close> encodes the logical statement $P \vee Q = P \vee (\neg P \wedge Q)$.
Its dual appears in \cite{BalbesHorn1970}.
\<close>

text \<open>Theorem 5\<close>

class boolean_algebra_3 = sup + uminus +
  assumes ba3_associative: "x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
  assumes ba3_commutative: "x \<squnion> y = y \<squnion> x"
  assumes ba3_idempotent[simp]: "x \<squnion> x = x"
  assumes ba3_double_complement[simp]: "--x = x"
  assumes ba3_top_unique: "x \<squnion> -x = y \<squnion> -y"
  assumes ba3_export: "x \<squnion> -(x \<squnion> y) = x \<squnion> -y"
begin

subclass huntington
proof
  show "\<And>x y z. x \<squnion> (y \<squnion> z) = x \<squnion> y \<squnion> z"
    by (simp add: ba3_associative)
  show "\<And>x y. x \<squnion> y = y \<squnion> x"
    by (simp add: ba3_commutative)
  show "\<And>x y. x = - (- x \<squnion> y) \<squnion> - (- x \<squnion> - y)"
    by (metis ba3_commutative ba3_double_complement ba3_export ba3_idempotent ba3_top_unique)
qed

end

context huntington
begin

sublocale h_ba3: boolean_algebra_3
proof
  show "\<And>x y z. x \<squnion> (y \<squnion> z) = x \<squnion> y \<squnion> z"
    by (simp add: h_ba1.ba1_associative)
  show "\<And>x y. x \<squnion> y = y \<squnion> x"
    by (simp add: h_ba1.ba1_commutative)
  show 3: "\<And>x. x \<squnion> x = x"
    using h_ba1.ba1_complement by blast
  show 4: "\<And>x. - - x = x"
    by (metis h_ba1.ba1_commutative huntington top_unique)
  show "\<And>x y. x \<squnion> - x = y \<squnion> - y"
    by (simp add: top_unique)
  show "\<And>x y. x \<squnion> - (x \<squnion> y) = x \<squnion> - y"
    using 3 4 by (smt h_ba1.ba1_ba2.ba2_associative_commutative h_ba1.ba1_complement)
qed

end

section \<open>Subset Boolean Algebras\<close>

text \<open>
We apply Huntington's axioms to the range of a unary operation, which serves as complement on the range.
This gives a Boolean algebra structure on the range without imposing any further constraints on the set.
The obtained structure is used as a reference in the subsequent development and to inherit the results proved here.
This is taken from \cite{Guttmann2012c,GuttmannStruthWeber2011b} and follows the development of Boolean algebras in \cite{Maddux1996}.
\<close>

text \<open>Definition 6\<close>

class subset_boolean_algebra = sup + uminus +
  assumes sub_associative: "-x \<squnion> (-y \<squnion> -z) = (-x \<squnion> -y) \<squnion> -z"
  assumes sub_commutative: "-x \<squnion> -y = -y \<squnion> -x"
  assumes sub_complement: "-x = -(--x \<squnion> -y) \<squnion> -(--x \<squnion> --y)"
  assumes sub_sup_closed: "-x \<squnion> -y = --(-x \<squnion> -y)"
begin

text \<open>uniqueness of \<open>top\<close>, resulting in the lemma \<open>top_def\<close> to replace the assumption \<open>sub_top_def\<close>\<close>

lemma top_unique:
  "-x \<squnion> --x = -y \<squnion> --y"
  by (metis sub_associative sub_commutative sub_complement)

text \<open>consequences for join and complement\<close>

lemma double_negation[simp]:
  "---x = -x"
  by (metis sub_complement sub_sup_closed)

lemma complement_1:
  "--x = -(-x \<squnion> -y) \<squnion> -(-x \<squnion> --y)"
  by (metis double_negation sub_complement)

lemma sup_right_zero_var:
  "-x \<squnion> (-y \<squnion> --y) = -z \<squnion> --z"
  by (smt complement_1 sub_associative sub_sup_closed top_unique)

lemma sup_right_unit_idempotent:
  "-x \<squnion> -x = -x \<squnion> -(-y \<squnion> --y)"
  by (metis complement_1 double_negation sub_sup_closed sup_right_zero_var)

lemma sup_idempotent[simp]:
  "-x \<squnion> -x = -x"
  by (smt complement_1 double_negation sub_associative sup_right_unit_idempotent)

lemma complement_2:
  "-x = -(-(-x \<squnion> -y) \<squnion> -(-x \<squnion> --y))"
  using complement_1 by auto

lemma sup_eq_cases:
  "-x \<squnion> -y = -x \<squnion> -z \<Longrightarrow> --x \<squnion> -y = --x \<squnion> -z \<Longrightarrow> -y = -z"
  by (metis complement_2 sub_commutative)

lemma sup_eq_cases_2:
  "-y \<squnion> -x = -z \<squnion> -x \<Longrightarrow> -y \<squnion> --x = -z \<squnion> --x \<Longrightarrow> -y = -z"
  using sub_commutative sup_eq_cases by auto

end

text \<open>Definition 7\<close>

class subset_extended = sup + inf + minus + uminus + bot + top + ord +
  assumes sub_top_def: "top = (THE x . \<forall>y . x = -y \<squnion> --y)" (* define without imposing uniqueness *)
  assumes sub_bot_def: "bot = -(THE x . \<forall>y . x = -y \<squnion> --y)"
  assumes sub_inf_def: "-x \<sqinter> -y = -(--x \<squnion> --y)"
  assumes sub_minus_def: "-x - -y = -(--x \<squnion> -y)"
  assumes sub_less_eq_def: "-x \<le> -y \<longleftrightarrow> -x \<squnion> -y = -y"
  assumes sub_less_def: "-x < -y \<longleftrightarrow> -x \<squnion> -y = -y \<and> \<not> (-y \<squnion> -x = -x)"

class subset_boolean_algebra_extended = subset_boolean_algebra + subset_extended
begin

lemma top_def:
  "top = -x \<squnion> --x"
  using sub_top_def top_unique by blast

text \<open>consequences for meet\<close>

lemma inf_closed:
  "-x \<sqinter> -y = --(-x \<sqinter> -y)"
  by (simp add: sub_inf_def)

lemma inf_associative:
  "-x \<sqinter> (-y \<sqinter> -z) = (-x \<sqinter> -y) \<sqinter> -z"
  using sub_associative sub_inf_def sub_sup_closed by auto

lemma inf_commutative:
  "-x \<sqinter> -y = -y \<sqinter> -x"
  by (simp add: sub_commutative sub_inf_def)

lemma inf_idempotent[simp]:
  "-x \<sqinter> -x = -x"
  by (simp add: sub_inf_def)

lemma inf_absorb[simp]:
  "(-x \<squnion> -y) \<sqinter> -x = -x"
  by (metis complement_1 sup_idempotent sub_inf_def sub_associative sub_sup_closed)

lemma sup_absorb[simp]:
  "-x \<squnion> (-x \<sqinter> -y) = -x"
  by (metis sub_associative sub_complement sub_inf_def sup_idempotent)

lemma inf_demorgan:
  "-(-x \<sqinter> -y) = --x \<squnion> --y"
  using sub_inf_def sub_sup_closed by auto

lemma sub_sup_demorgan:
  "-(-x \<squnion> -y) = --x \<sqinter> --y"
  by (simp add: sub_inf_def)

lemma sup_cases:
  "-x = (-x \<sqinter> -y) \<squnion> (-x \<sqinter> --y)"
  by (metis inf_closed inf_demorgan sub_complement)

lemma inf_cases:
  "-x = (-x \<squnion> -y) \<sqinter> (-x \<squnion> --y)"
  by (metis complement_2 sub_sup_closed sub_sup_demorgan)

lemma inf_complement_intro:
  "(-x \<squnion> -y) \<sqinter> --x = -y \<sqinter> --x"
proof -
  have "(-x \<squnion> -y) \<sqinter> --x = (-x \<squnion> -y) \<sqinter> (--x \<squnion> -y) \<sqinter> --x"
    by (metis inf_absorb inf_associative sub_sup_closed)
  also have "... = -y \<sqinter> --x"
    by (metis inf_cases sub_commutative)
  finally show ?thesis
    .
qed

lemma sup_complement_intro:
  "-x \<squnion> -y = -x \<squnion> (--x \<sqinter> -y)"
  by (metis inf_absorb inf_commutative inf_complement_intro sub_sup_closed sup_cases)

lemma inf_left_dist_sup:
  "-x \<sqinter> (-y \<squnion> -z) = (-x \<sqinter> -y) \<squnion> (-x \<sqinter> -z)"
proof -
  have "-x \<sqinter> (-y \<squnion> -z) = (-x \<sqinter> (-y \<squnion> -z) \<sqinter> -y) \<squnion> (-x \<sqinter> (-y \<squnion> -z) \<sqinter> --y)"
    by (metis sub_inf_def sub_sup_closed sup_cases)
  also have "... = (-x \<sqinter> -y) \<squnion> (-x \<sqinter> -z \<sqinter> --y)"
    by (metis inf_absorb inf_associative inf_complement_intro sub_sup_closed)
  also have "... = (-x \<sqinter> -y) \<squnion> ((-x \<sqinter> -y \<sqinter> -z) \<squnion> (-x \<sqinter> -z \<sqinter> --y))"
    using sub_associative sub_inf_def sup_absorb by auto
  also have "... = (-x \<sqinter> -y) \<squnion> ((-x \<sqinter> -z \<sqinter> -y) \<squnion> (-x \<sqinter> -z \<sqinter> --y))"
    by (metis inf_associative inf_commutative)
  also have "... = (-x \<sqinter> -y) \<squnion> (-x \<sqinter> -z)"
    by (metis sub_inf_def sup_cases)
  finally show ?thesis
    .
qed

lemma sup_left_dist_inf:
  "-x \<squnion> (-y \<sqinter> -z) = (-x \<squnion> -y) \<sqinter> (-x \<squnion> -z)"
proof -
  have "-x \<squnion> (-y \<sqinter> -z) = -(--x \<sqinter> (--y \<squnion> --z))"
    by (metis sub_inf_def sub_sup_closed sub_sup_demorgan)
  also have "... = (-x \<squnion> -y) \<sqinter> (-x \<squnion> -z)"
    by (metis inf_left_dist_sup sub_sup_closed sub_sup_demorgan)
  finally show ?thesis
    .
qed

lemma sup_right_dist_inf:
  "(-y \<sqinter> -z) \<squnion> -x = (-y \<squnion> -x) \<sqinter> (-z \<squnion> -x)"
  using sub_commutative sub_inf_def sup_left_dist_inf by auto

lemma inf_right_dist_sup:
  "(-y \<squnion> -z) \<sqinter> -x = (-y \<sqinter> -x) \<squnion> (-z \<sqinter> -x)"
  by (metis inf_commutative inf_left_dist_sup sub_sup_closed)

lemma case_duality:
  "(--x \<sqinter> -y) \<squnion> (-x \<sqinter> -z) = (-x \<squnion> -y) \<sqinter> (--x \<squnion> -z)"
proof -
  have 1: "-(--x \<sqinter> --y) \<sqinter> ----x = --x \<sqinter> -y"
    using inf_commutative inf_complement_intro sub_sup_closed sub_sup_demorgan by auto
  have 2: "-(----x \<squnion> -(--x \<squnion> -z)) = -----x \<sqinter> ---z"
    by (metis (no_types) double_negation sup_complement_intro sub_sup_demorgan)
  have 3: "-(--x \<sqinter> --y) \<sqinter> -x = -x"
    using inf_commutative inf_left_dist_sup sub_sup_closed sub_sup_demorgan by auto
  hence "-(--x \<sqinter> --y) = -x \<squnion> -y"
    using sub_sup_closed sub_sup_demorgan by auto
  thus ?thesis
    by (metis double_negation 1 2 3 inf_associative inf_left_dist_sup sup_complement_intro)
qed

lemma case_duality_2:
  "(-x \<sqinter> -y) \<squnion> (--x \<sqinter> -z) = (-x \<squnion> -z) \<sqinter> (--x \<squnion> -y)"
  using case_duality sub_commutative sub_inf_def by auto

lemma complement_cases:
  "((-v \<sqinter> -w) \<squnion> (--v \<sqinter> -x)) \<sqinter> -((-v \<sqinter> -y) \<squnion> (--v \<sqinter> -z)) = (-v \<sqinter> -w \<sqinter> --y) \<squnion> (--v \<sqinter> -x \<sqinter> --z)"
proof -
  have 1: "(--v \<squnion> -w) = --(--v \<squnion> -w) \<and> (-v \<squnion> -x) = --(-v \<squnion> -x) \<and> (--v \<squnion> --y) = --(--v \<squnion> --y) \<and> (-v \<squnion> --z) = --(-v \<squnion> --z)"
    using sub_inf_def sub_sup_closed by auto
  have 2: "(-v \<squnion> (-x \<sqinter> --z)) = --(-v \<squnion> (-x \<sqinter> --z))"
    using sub_inf_def sub_sup_closed by auto
  have "((-v \<sqinter> -w) \<squnion> (--v \<sqinter> -x)) \<sqinter> -((-v \<sqinter> -y) \<squnion> (--v \<sqinter> -z)) = ((-v \<sqinter> -w) \<squnion> (--v \<sqinter> -x)) \<sqinter> (-(-v \<sqinter> -y) \<sqinter> -(--v \<sqinter> -z))"
    using sub_inf_def by auto
  also have "... = ((-v \<sqinter> -w) \<squnion> (--v \<sqinter> -x)) \<sqinter> ((--v \<squnion> --y) \<sqinter> (-v \<squnion> --z))"
    using inf_demorgan by auto
  also have "... = (--v \<squnion> -w) \<sqinter> (-v \<squnion> -x) \<sqinter> ((--v \<squnion> --y) \<sqinter> (-v \<squnion> --z))"
    by (metis case_duality double_negation)
  also have "... = (--v \<squnion> -w) \<sqinter> ((-v \<squnion> -x) \<sqinter> ((--v \<squnion> --y) \<sqinter> (-v \<squnion> --z)))"
    by (metis 1 inf_associative sub_inf_def)
  also have "... = (--v \<squnion> -w) \<sqinter> ((-v \<squnion> -x) \<sqinter> (--v \<squnion> --y) \<sqinter> (-v \<squnion> --z))"
    by (metis 1 inf_associative)
  also have "... = (--v \<squnion> -w) \<sqinter> ((--v \<squnion> --y) \<sqinter> (-v \<squnion> -x) \<sqinter> (-v \<squnion> --z))"
    by (metis 1 inf_commutative)
  also have "... = (--v \<squnion> -w) \<sqinter> ((--v \<squnion> --y) \<sqinter> ((-v \<squnion> -x) \<sqinter> (-v \<squnion> --z)))"
    by (metis 1 inf_associative)
  also have "... = (--v \<squnion> -w) \<sqinter> ((--v \<squnion> --y) \<sqinter> (-v \<squnion> (-x \<sqinter> --z)))"
    by (simp add: sup_left_dist_inf)
  also have "... = (--v \<squnion> -w) \<sqinter> (--v \<squnion> --y) \<sqinter> (-v \<squnion> (-x \<sqinter> --z))"
    using 1 2 by (metis inf_associative)
  also have "... = (--v \<squnion> (-w \<sqinter> --y)) \<sqinter> (-v \<squnion> (-x \<sqinter> --z))"
    by (simp add: sup_left_dist_inf)
  also have "... = (-v \<sqinter> (-w \<sqinter> --y)) \<squnion> (--v \<sqinter> (-x \<sqinter> --z))"
    by (metis case_duality complement_1 complement_2 sub_inf_def)
  also have "... = (-v \<sqinter> -w \<sqinter> --y) \<squnion> (--v \<sqinter> -x \<sqinter> --z)"
    by (simp add: inf_associative)
  finally show ?thesis
    .
qed

lemma inf_cases_2: "--x = -(-x \<sqinter> -y) \<sqinter> -(-x \<sqinter> --y)"
  using sub_inf_def sup_cases by auto

text \<open>consequences for \<open>top\<close> and \<open>bot\<close>\<close>

lemma sup_complement[simp]:
  "-x \<squnion> --x = top"
  using top_def by auto

lemma inf_complement[simp]:
  "-x \<sqinter> --x = bot"
  by (metis sub_bot_def sub_inf_def sub_top_def top_def)

lemma complement_bot[simp]:
  "-bot = top"
  using inf_complement inf_demorgan sup_complement by fastforce

lemma complement_top[simp]:
  "-top = bot"
  using sub_bot_def sub_top_def by blast

lemma sup_right_zero[simp]:
  "-x \<squnion> top = top"
  using sup_right_zero_var by auto

lemma sup_left_zero[simp]:
  "top \<squnion> -x = top"
  by (metis complement_bot sub_commutative sup_right_zero)

lemma inf_right_unit[simp]:
  "-x \<sqinter> bot = bot"
  by (metis complement_bot complement_top double_negation sub_sup_demorgan sup_right_zero)

lemma inf_left_unit[simp]:
  "bot \<sqinter> -x = bot"
  by (metis complement_top inf_commutative inf_right_unit)

lemma sup_right_unit[simp]:
  "-x \<squnion> bot = -x"
  using sup_right_unit_idempotent by auto

lemma sup_left_unit[simp]:
  "bot \<squnion> -x = -x"
  by (metis complement_top sub_commutative sup_right_unit)

lemma inf_right_zero[simp]:
  "-x \<sqinter> top = -x"
  by (metis inf_left_dist_sup sup_cases top_def)

lemma sub_inf_left_zero[simp]:
  "top \<sqinter> -x = -x"
  using inf_absorb top_def by fastforce

lemma bot_double_complement[simp]:
  "--bot = bot"
  by simp

lemma top_double_complement[simp]:
  "--top = top"
  by simp

text \<open>consequences for the order\<close>

lemma reflexive:
  "-x \<le> -x"
  by (simp add: sub_less_eq_def)

lemma transitive:
  "-x \<le> -y \<Longrightarrow> -y \<le> -z \<Longrightarrow> -x \<le> -z"
  by (metis sub_associative sub_less_eq_def)

lemma antisymmetric:
  "-x \<le> -y \<Longrightarrow> -y \<le> -x \<Longrightarrow> -x = -y"
  by (simp add: sub_commutative sub_less_eq_def)

lemma sub_bot_least:
  "bot \<le> -x"
  using sup_left_unit complement_top sub_less_eq_def by blast

lemma top_greatest:
  "-x \<le> top"
  using complement_bot sub_less_eq_def sup_right_zero by blast

lemma upper_bound_left:
  "-x \<le> -x \<squnion> -y"
  by (metis sub_associative sub_less_eq_def sub_sup_closed sup_idempotent)

lemma upper_bound_right:
  "-y \<le> -x \<squnion> -y"
  using sub_commutative upper_bound_left by fastforce

lemma sub_sup_left_isotone:
  assumes "-x \<le> -y"
    shows "-x \<squnion> -z \<le> -y \<squnion> -z"
proof -
  have "-x \<squnion> -y = -y"
    by (meson assms sub_less_eq_def)
  thus ?thesis
    by (metis (full_types) sub_associative sub_commutative sub_sup_closed upper_bound_left)
qed

lemma sub_sup_right_isotone:
  "-x \<le> -y \<Longrightarrow> -z \<squnion> -x \<le> -z \<squnion> -y"
  by (simp add: sub_commutative sub_sup_left_isotone)

lemma sup_isotone:
  assumes "-p \<le> -q"
      and "-r \<le> -s"
    shows "-p \<squnion> -r \<le> -q \<squnion> -s"
proof -
  have "\<And>x y. \<not> -x \<le> -y \<squnion> -r \<or> -x \<le> -y \<squnion> -s"
    by (metis (full_types) assms(2) sub_sup_closed sub_sup_right_isotone transitive)
  thus ?thesis
    by (metis (no_types) assms(1) sub_sup_closed sub_sup_left_isotone)
qed

lemma sub_complement_antitone:
  "-x \<le> -y \<Longrightarrow> --y \<le> --x"
  by (metis inf_absorb inf_demorgan sub_less_eq_def)

lemma less_eq_inf:
  "-x \<le> -y \<longleftrightarrow> -x \<sqinter> -y = -x"
  by (metis inf_absorb inf_commutative sub_less_eq_def upper_bound_right sup_absorb)

lemma inf_complement_left_antitone:
  "-x \<le> -y \<Longrightarrow> -(-y \<sqinter> -z) \<le> -(-x \<sqinter> -z)"
  by (simp add: sub_complement_antitone inf_demorgan sub_sup_left_isotone)

lemma sub_inf_left_isotone:
  "-x \<le> -y \<Longrightarrow> -x \<sqinter> -z \<le> -y \<sqinter> -z"
  using sub_complement_antitone inf_closed inf_complement_left_antitone by fastforce

lemma sub_inf_right_isotone:
  "-x \<le> -y \<Longrightarrow> -z \<sqinter> -x \<le> -z \<sqinter> -y"
  by (simp add: inf_commutative sub_inf_left_isotone)

lemma inf_isotone:
  assumes "-p \<le> -q"
      and "-r \<le> -s"
    shows "-p \<sqinter> -r \<le> -q \<sqinter> -s"
proof -
  have "\<forall>w x y z. (-w \<le> -x \<sqinter> -y \<or> \<not> -w \<le> -x \<sqinter> -z) \<or> \<not> -z \<le> -y"
    by (metis (no_types) inf_closed sub_inf_right_isotone transitive)
  thus ?thesis
    by (metis (no_types) assms inf_closed sub_inf_left_isotone)
qed

lemma least_upper_bound:
  "-x \<le> -z \<and> -y \<le> -z \<longleftrightarrow> -x \<squnion> -y \<le> -z"
  by (metis sub_sup_closed transitive upper_bound_right sup_idempotent sup_isotone upper_bound_left)

lemma lower_bound_left:
  "-x \<sqinter> -y \<le> -x"
  by (metis sub_inf_def upper_bound_right sup_absorb)

lemma lower_bound_right:
  "-x \<sqinter> -y \<le> -y"
  using inf_commutative lower_bound_left by fastforce

lemma greatest_lower_bound:
  "-x \<le> -y \<and> -x \<le> -z \<longleftrightarrow> -x \<le> -y \<sqinter> -z"
  by (metis inf_closed sub_inf_left_isotone less_eq_inf transitive lower_bound_left lower_bound_right)

lemma less_eq_sup_top:
  "-x \<le> -y \<longleftrightarrow> --x \<squnion> -y = top"
  by (metis complement_1 inf_commutative inf_complement_intro sub_inf_left_zero less_eq_inf sub_complement sup_complement_intro top_def)

lemma less_eq_inf_bot:
  "-x \<le> -y \<longleftrightarrow> -x \<sqinter> --y = bot"
  by (metis complement_bot complement_top double_negation inf_demorgan less_eq_sup_top sub_inf_def)

lemma shunting:
  "-x \<sqinter> -y \<le> -z \<longleftrightarrow> -y \<le> --x \<squnion> -z"
proof (cases "--x \<squnion> (-z \<squnion> --y) = top")
  case True
  have "\<forall>v w. -v \<le> -w \<or> -w \<squnion> --v \<noteq> top"
    using less_eq_sup_top sub_commutative by blast
  thus ?thesis
    by (metis True sub_associative sub_commutative sub_inf_def sub_sup_closed)
next
  case False
  hence "--x \<squnion> (-z \<squnion> --y) \<noteq> top \<and> \<not> -y \<le> -z \<squnion> --x"
    by (metis (no_types) less_eq_sup_top sub_associative sub_commutative sub_sup_closed)
  thus ?thesis
    using less_eq_sup_top sub_associative sub_commutative sub_inf_def sub_sup_closed by auto
qed

lemma shunting_right:
  "-x \<sqinter> -y \<le> -z \<longleftrightarrow> -x \<le> -z \<squnion> --y"
  by (metis inf_commutative sub_commutative shunting)

lemma sup_less_eq_cases:
  assumes "-z \<le> -x \<squnion> -y"
      and "-z \<le> --x \<squnion> -y"
    shows "-z \<le> -y"
proof -
  have "-z \<le> (-x \<squnion> -y) \<sqinter> (--x \<squnion> -y)"
    by (metis assms greatest_lower_bound sub_sup_closed)
  also have "... = -y"
    by (metis inf_cases sub_commutative)
  finally show ?thesis
    .
qed

lemma sup_less_eq_cases_2:
  "-x \<squnion> -y \<le> -x \<squnion> -z \<Longrightarrow> --x \<squnion> -y \<le> --x \<squnion> -z \<Longrightarrow> -y \<le> -z"
  by (metis least_upper_bound sup_less_eq_cases sub_sup_closed)

lemma sup_less_eq_cases_3:
  "-y \<squnion> -x \<le> -z \<squnion> -x \<Longrightarrow> -y \<squnion> --x \<le> -z \<squnion> --x \<Longrightarrow> -y \<le> -z"
  by (simp add: sup_less_eq_cases_2 sub_commutative)

lemma inf_less_eq_cases:
  "-x \<sqinter> -y \<le> -z \<Longrightarrow> --x \<sqinter> -y \<le> -z \<Longrightarrow> -y \<le> -z"
  by (simp add: shunting sup_less_eq_cases)

lemma inf_less_eq_cases_2:
  "-x \<sqinter> -y \<le> -x \<sqinter> -z \<Longrightarrow> --x \<sqinter> -y \<le> --x \<sqinter> -z \<Longrightarrow> -y \<le> -z"
  by (metis greatest_lower_bound inf_closed inf_less_eq_cases)

lemma inf_less_eq_cases_3:
  "-y \<sqinter> -x \<le> -z \<sqinter> -x \<Longrightarrow> -y \<sqinter> --x \<le> -z \<sqinter> --x \<Longrightarrow> -y \<le> -z"
  by (simp add: inf_commutative inf_less_eq_cases_2)

lemma inf_eq_cases:
  "-x \<sqinter> -y = -x \<sqinter> -z \<Longrightarrow> --x \<sqinter> -y = --x \<sqinter> -z \<Longrightarrow> -y = -z"
  by (metis inf_commutative sup_cases)

lemma inf_eq_cases_2:
  "-y \<sqinter> -x = -z \<sqinter> -x \<Longrightarrow> -y \<sqinter> --x = -z \<sqinter> --x \<Longrightarrow> -y = -z"
  using inf_commutative inf_eq_cases by auto

lemma wnf_lemma_1:
  "((-x \<squnion> -y) \<sqinter> (--x \<squnion> -z)) \<squnion> -x = -x \<squnion> -y"
proof -
  have "\<forall>u v w. (-u \<sqinter> (-v \<squnion> --w)) \<squnion> -w = -u \<squnion> -w"
    by (metis inf_right_zero sub_associative sub_sup_closed sup_complement sup_idempotent sup_right_dist_inf)
  thus ?thesis
    by (metis (no_types) sub_associative sub_commutative sub_sup_closed sup_idempotent)
qed

lemma wnf_lemma_2:
  "((-x \<squnion> -y) \<sqinter> (-z \<squnion> --y)) \<squnion> -y = -x \<squnion> -y"
  using sub_commutative wnf_lemma_1 by fastforce

lemma wnf_lemma_3:
  "((-x \<squnion> -z) \<sqinter> (--x \<squnion> -y)) \<squnion> --x = --x \<squnion> -y"
  by (metis case_duality case_duality_2 double_negation sub_commutative wnf_lemma_2)

lemma wnf_lemma_4:
  "((-z \<squnion> -y) \<sqinter> (-x \<squnion> --y)) \<squnion> --y = -x \<squnion> --y"
  using sub_commutative wnf_lemma_3 by auto

end

class subset_boolean_algebra' = sup + uminus +
  assumes sub_associative': "-x \<squnion> (-y \<squnion> -z) = (-x \<squnion> -y) \<squnion> -z"
  assumes sub_commutative': "-x \<squnion> -y = -y \<squnion> -x"
  assumes sub_complement': "-x = -(--x \<squnion> -y) \<squnion> -(--x \<squnion> --y)"
  assumes sub_sup_closed': "\<exists>z . -x \<squnion> -y = -z"
begin

subclass subset_boolean_algebra
proof
  show "\<And>x y z. - x \<squnion> (- y \<squnion> - z) = - x \<squnion> - y \<squnion> - z"
    by (simp add: sub_associative')
  show "\<And>x y. - x \<squnion> - y = - y \<squnion> - x"
    by (simp add: sub_commutative')
  show "\<And>x y. - x = - (- - x \<squnion> - y) \<squnion> - (- - x \<squnion> - - y)"
    by (simp add: sub_complement')
  show "\<And>x y. - x \<squnion> - y = - - (- x \<squnion> - y)"
  proof -
    fix x y
    have "\<forall>x y. -y \<squnion> (-(--y \<squnion> -x) \<squnion> -(---x \<squnion> -y)) = -y \<squnion> --x"
      by (metis (no_types) sub_associative' sub_commutative' sub_complement')
    hence "\<forall>x. ---x = -x"
      by (metis (no_types) sub_commutative' sub_complement')
    thus "-x \<squnion> -y = --(-x \<squnion> -y)"
      by (metis sub_sup_closed')
  qed
qed

end

text \<open>
We introduce a type for the range of complement and show that it is an instance of \<open>boolean_algebra\<close>.
\<close>

typedef (overloaded) 'a boolean_subset = "{ x::'a::uminus . \<exists>y . x = -y }"
  by auto

lemma simp_boolean_subset[simp]:
  "\<exists>y . Rep_boolean_subset x = -y"
  using Rep_boolean_subset by simp

setup_lifting type_definition_boolean_subset

text \<open>Theorem 8.1\<close>

instantiation boolean_subset :: (subset_boolean_algebra) huntington
begin

lift_definition sup_boolean_subset :: "'a boolean_subset \<Rightarrow> 'a boolean_subset \<Rightarrow> 'a boolean_subset" is sup
  using sub_sup_closed by auto

lift_definition uminus_boolean_subset :: "'a boolean_subset \<Rightarrow> 'a boolean_subset" is uminus
  by auto

instance
proof
  show "\<And>x y z::'a boolean_subset. x \<squnion> (y \<squnion> z) = x \<squnion> y \<squnion> z"
    apply transfer
    using sub_associative by blast
  show "\<And>x y::'a boolean_subset. x \<squnion> y = y \<squnion> x"
    apply transfer
    using sub_commutative by blast
  show "\<And>x y::'a boolean_subset. x = - (- x \<squnion> y) \<squnion> - (- x \<squnion> - y)"
    apply transfer
    using sub_complement by blast
qed

end

text \<open>Theorem 8.2\<close>

instantiation boolean_subset :: (subset_boolean_algebra_extended) huntington_extended
begin

lift_definition inf_boolean_subset :: "'a boolean_subset \<Rightarrow> 'a boolean_subset \<Rightarrow> 'a boolean_subset" is inf
  using inf_closed by auto

lift_definition minus_boolean_subset :: "'a boolean_subset \<Rightarrow> 'a boolean_subset \<Rightarrow> 'a boolean_subset" is minus
  using sub_minus_def by auto

lift_definition bot_boolean_subset :: "'a boolean_subset" is bot
  by (metis complement_top)

lift_definition top_boolean_subset :: "'a boolean_subset" is top
  by (metis complement_bot)

lift_definition less_eq_boolean_subset :: "'a boolean_subset \<Rightarrow> 'a boolean_subset \<Rightarrow> bool" is less_eq .

lift_definition less_boolean_subset :: "'a boolean_subset \<Rightarrow> 'a boolean_subset \<Rightarrow> bool" is less .

instance
proof
  show 1: "top = (THE x. \<forall>y::'a boolean_subset. x = y \<squnion> - y)"
  proof (rule the_equality[symmetric])
    show "\<forall>y::'a boolean_subset. top = y \<squnion> - y"
      apply transfer
      by auto
    show "\<And>x::'a boolean_subset. \<forall>y. x = y \<squnion> - y \<Longrightarrow> x = top"
      apply transfer
      by force
  qed
  have "(bot::'a boolean_subset) = - top"
    apply transfer
    by simp
  thus "bot = - (THE x. \<forall>y::'a boolean_subset. x = y \<squnion> - y)"
    using 1 by simp
  show "\<And>x y::'a boolean_subset. x \<sqinter> y = - (- x \<squnion> - y)"
    apply transfer
    using sub_inf_def by blast
  show "\<And>x y::'a boolean_subset. x - y = - (- x \<squnion> y)"
    apply transfer
    using sub_minus_def by blast
  show "\<And>x y::'a boolean_subset. (x \<le> y) = (x \<squnion> y = y)"
    apply transfer
    using sub_less_eq_def by blast
  show "\<And>x y::'a boolean_subset. (x < y) = (x \<squnion> y = y \<and> y \<squnion> x \<noteq> x)"
    apply transfer
    using sub_less_def by blast
qed

end

section \<open>Subset Boolean algebras with Additional Structure\<close>

text \<open>
We now discuss axioms that make the range of a unary operation a Boolean algebra, but add further properties that are common to the intended models.
In the intended models, the unary operation can be a complement, a pseudocomplement or the antidomain operation.
For simplicity, we mostly call the unary operation `complement'.

We first look at structures based only on join and complement, and then add axioms for the remaining operations of Boolean algebras.
In the intended models, the operation that is meet on the range of the complement can be a meet in the whole algebra or composition.
\<close>

subsection \<open>Axioms Derived from the New Axiomatisation\<close>

text \<open>
The axioms of the first algebra are based on \<open>boolean_algebra_3\<close>.
\<close>

text \<open>Definition 9\<close>

class subset_boolean_algebra_1 = sup + uminus +
  assumes sba1_associative: "x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
  assumes sba1_commutative: "x \<squnion> y = y \<squnion> x"
  assumes sba1_idempotent[simp]: "x \<squnion> x = x"
  assumes sba1_double_complement[simp]: "---x = -x"
  assumes sba1_bot_unique: "-(x \<squnion> -x) = -(y \<squnion> -y)"
  assumes sba1_export: "-x \<squnion> -(-x \<squnion> y) = -x \<squnion> -y"
begin

text \<open>Theorem 11.1\<close>

subclass subset_boolean_algebra
proof
  show "\<And>x y z. - x \<squnion> (- y \<squnion> - z) = - x \<squnion> - y \<squnion> - z"
    by (simp add: sba1_associative)
  show "\<And>x y. - x \<squnion> - y = - y \<squnion> - x"
    by (simp add: sba1_commutative)
  show "\<And>x y. - x = - (- - x \<squnion> - y) \<squnion> - (- - x \<squnion> - - y)"
    by (smt sba1_bot_unique sba1_commutative sba1_double_complement sba1_export sba1_idempotent)
  thus "\<And>x y. - x \<squnion> - y = - - (- x \<squnion> - y)"
    by (metis sba1_double_complement sba1_export)
qed

definition "sba1_bot \<equiv> THE x . \<forall>z . x = -(z \<squnion> -z)"

lemma sba1_bot:
  "sba1_bot = -(z \<squnion> -z)"
  using sba1_bot_def sba1_bot_unique by auto

end

text \<open>Boolean algebra operations based on join and complement\<close>

text \<open>Definition 10\<close>

class subset_extended_1 = sup + inf + minus + uminus + bot + top + ord +
  assumes ba_bot: "bot = (THE x . \<forall>z . x = -(z \<squnion> -z))"
  assumes ba_top: "top = -(THE x . \<forall>z . x = -(z \<squnion> -z))"
  assumes ba_inf: "-x \<sqinter> -y = -(--x \<squnion> --y)"
  assumes ba_minus: "-x - -y = -(--x \<squnion> -y)"
  assumes ba_less_eq: "x \<le> y \<longleftrightarrow> x \<squnion> y = y"
  assumes ba_less: "x < y \<longleftrightarrow> x \<squnion> y = y \<and> \<not> (y \<squnion> x = x)"

class subset_extended_2 = subset_extended_1 +
  assumes ba_bot_unique: "-(x \<squnion> -x) = -(y \<squnion> -y)"
begin

lemma ba_bot_def:
  "bot = -(z \<squnion> -z)"
  using ba_bot ba_bot_unique by auto

lemma ba_top_def:
  "top = --(z \<squnion> -z)"
  using ba_bot_def ba_top by simp

end

text \<open>Subset forms Boolean Algebra, extended by Boolean algebra operations\<close>

class subset_boolean_algebra_1_extended = subset_boolean_algebra_1 + subset_extended_1
begin

subclass subset_extended_2
proof
  show "\<And>x y. - (x \<squnion> - x) = - (y \<squnion> - y)"
    by (simp add: sba1_bot_unique)
qed

subclass semilattice_sup
proof
  show "\<And>x y. (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: ba_less ba_less_eq)
  show "\<And>x. x \<le> x"
    by (simp add: ba_less_eq)
  show "\<And>x y z. x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (metis sba1_associative ba_less_eq)
  show "\<And>x y. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: sba1_commutative ba_less_eq)
  show "\<And>x y. x \<le> x \<squnion> y"
    by (simp add: sba1_associative ba_less_eq)
  thus "\<And>y x. y \<le> x \<squnion> y"
    by (simp add: sba1_commutative)
  show "\<And>y x z. y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (metis sba1_associative ba_less_eq)
qed

text \<open>Theorem 11.2\<close>

subclass subset_boolean_algebra_extended
proof
  show "top = (THE x. \<forall>y. x = - y \<squnion> - - y)"
    by (smt ba_bot ba_bot_def ba_top sub_sup_closed the_equality)
  thus "bot = - (THE x. \<forall>y. x = - y \<squnion> - - y)"
    using ba_bot_def ba_top_def by force
  show "\<And>x y. - x \<sqinter> - y = - (- - x \<squnion> - - y)"
    by (simp add: ba_inf)
  show "\<And>x y. - x - - y = - (- - x \<squnion> - y)"
    by (simp add: ba_minus)
  show "\<And>x y. (- x \<le> - y) = (- x \<squnion> - y = - y)"
    using le_iff_sup by auto
  show "\<And>x y. (- x < - y) = (- x \<squnion> - y = - y \<and> - y \<squnion> - x \<noteq> - x)"
    by (simp add: ba_less)
qed

end

subsection \<open>Stronger Assumptions based on Join and Complement\<close>

text \<open>
We add further axioms covering properties common to the antidomain and (pseudo)complement instances.
\<close>

text \<open>Definition 12\<close>

class subset_boolean_algebra_2 = sup + uminus +
  assumes sba2_associative: "x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
  assumes sba2_commutative: "x \<squnion> y = y \<squnion> x"
  assumes sba2_idempotent[simp]: "x \<squnion> x = x"
  assumes sba2_bot_unit: "x \<squnion> -(y \<squnion> -y) = x"
  assumes sba2_sub_sup_demorgan: "-(x \<squnion> y) = -(--x \<squnion> --y)"
  assumes sba2_export: "-x \<squnion> -(-x \<squnion> y) = -x \<squnion> -y"
begin

text \<open>Theorem 13.1\<close>

subclass subset_boolean_algebra_1
proof
  show "\<And>x y z. x \<squnion> (y \<squnion> z) = x \<squnion> y \<squnion> z"
    by (simp add: sba2_associative)
  show "\<And>x y. x \<squnion> y = y \<squnion> x"
    by (simp add: sba2_commutative)
  show "\<And>x. x \<squnion> x = x"
    by simp
  show "\<And>x. - - - x = - x"
    by (metis sba2_idempotent sba2_sub_sup_demorgan)
  show "\<And>x y. - (x \<squnion> - x) = - (y \<squnion> - y)"
    by (metis sba2_bot_unit sba2_commutative)
  show "\<And>x y. - x \<squnion> - (- x \<squnion> y) = - x \<squnion> - y"
    by (simp add: sba2_export)
qed

text \<open>Theorem 13.2\<close>

lemma double_complement_dist_sup:
  "--(x \<squnion> y) = --x \<squnion> --y"
  by (metis sba2_commutative sba2_export sba2_idempotent sba2_sub_sup_demorgan)

lemma maddux_3_3[simp]:
  "-(x \<squnion> y) \<squnion> -(x \<squnion> -y) = -x"
  by (metis double_complement_dist_sup sba1_double_complement sba2_commutative sub_complement)

lemma huntington_3_pp[simp]:
  "-(-x \<squnion> -y) \<squnion> -(-x \<squnion> y) = --x"
  using sba2_commutative maddux_3_3 by fastforce

end

class subset_boolean_algebra_2_extended = subset_boolean_algebra_2 + subset_extended_1
begin

subclass subset_boolean_algebra_1_extended ..

subclass bounded_semilattice_sup_bot
proof
  show "\<And>x. bot \<le> x"
    using sba2_bot_unit ba_bot_def sup_right_divisibility by auto
qed

text \<open>Theorem 13.3\<close>

lemma complement_antitone:
  "x \<le> y \<Longrightarrow> -y \<le> -x"
  by (metis le_iff_sup maddux_3_3 sba2_export sup_monoid.add_commute)

lemma double_complement_isotone:
  "x \<le> y \<Longrightarrow> --x \<le> --y"
  by (simp add: complement_antitone)

lemma sup_demorgan:
  "-(x \<squnion> y) = -x \<sqinter> -y"
  using sba2_sub_sup_demorgan ba_inf by auto

end

subsection \<open>Axioms for Meet\<close>

text \<open>
We add further axioms of \<open>inf\<close> covering properties common to the antidomain and pseudocomplement instances.
We omit the left distributivity rule and the right zero rule as they do not hold in some models.
In particular, the operation \<open>inf\<close> does not have to be commutative.
\<close>

text \<open>Definition 14\<close>

class subset_boolean_algebra_3_extended = subset_boolean_algebra_2_extended +
  assumes sba3_inf_associative: "x \<sqinter> (y \<sqinter> z) = (x \<sqinter> y) \<sqinter> z"
  assumes sba3_inf_right_dist_sup: "(x \<squnion> y) \<sqinter> z = (x \<sqinter> z) \<squnion> (y \<sqinter> z)"
  assumes sba3_inf_complement_bot: "-x \<sqinter> x = bot"
  assumes sba3_inf_left_unit[simp]: "top \<sqinter> x = x"
  assumes sba3_complement_inf_double_complement: "-(x \<sqinter> --y) = -(x \<sqinter> y)"
begin

text \<open>Theorem 15\<close>

lemma inf_left_zero:
  "bot \<sqinter> x = bot"
  by (metis inf_right_unit sba3_inf_associative sba3_inf_complement_bot)

lemma inf_double_complement_export:
  "--(--x \<sqinter> y) = --x \<sqinter> --y"
  by (metis inf_closed sba3_complement_inf_double_complement)

lemma inf_left_isotone:
  "x \<le> y \<Longrightarrow> x \<sqinter> z \<le> y \<sqinter> z"
  using sba3_inf_right_dist_sup sup_right_divisibility by auto

lemma inf_complement_export:
  "--(-x \<sqinter> y) = -x \<sqinter> --y"
  by (metis inf_double_complement_export sba1_double_complement)

lemma double_complement_above:
  "--x \<sqinter> x = x"
  by (metis sup_monoid.add_0_right complement_bot inf_demorgan sba1_double_complement sba3_inf_complement_bot sba3_inf_right_dist_sup sba3_inf_left_unit)

lemma "x \<le> y \<Longrightarrow> z \<sqinter> x \<le> z \<sqinter> y" nitpick [expect=genuine] oops
lemma "x \<sqinter> top = x" nitpick [expect=genuine] oops
lemma "x \<sqinter> y = y \<sqinter> x" nitpick [expect=genuine] oops

end

subsection \<open>Stronger Assumptions for Meet\<close>

text \<open>
The following axioms also hold in both models, but follow from the axioms of \<open>subset_boolean_algebra_5_operations\<close>.
\<close>

text \<open>Definition 16\<close>

class subset_boolean_algebra_4_extended = subset_boolean_algebra_3_extended +
  assumes sba4_inf_right_unit[simp]: "x \<sqinter> top = x"
  assumes inf_right_isotone: "x \<le> y \<Longrightarrow> z \<sqinter> x \<le> z \<sqinter> y"
begin

lemma "x \<squnion> top = top" nitpick [expect=genuine] oops
lemma "x \<sqinter> bot = bot" nitpick [expect=genuine] oops
lemma "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)" nitpick [expect=genuine] oops
lemma "(x \<sqinter> y = bot) = (x \<le> - y)" nitpick [expect=genuine] oops

end

section \<open>Boolean Algebras in Stone Algebras\<close>

text \<open>
We specialise \<open>inf\<close> to meet and complement to pseudocomplement.
This puts Stone algebras into the picture; for these it is well known that regular elements form a Boolean subalgebra \cite{Graetzer1971}.
\<close>

text \<open>Definition 17\<close>

class subset_boolean_algebra_5_extended = subset_boolean_algebra_3_extended +
  assumes sba5_inf_commutative: "x \<sqinter> y = y \<sqinter> x"
  assumes sba5_inf_absorb: "x \<sqinter> (x \<squnion> y) = x"
begin

subclass distrib_lattice_bot
proof
  show "\<And>x y. x \<sqinter> y \<le> x"
    by (metis sba5_inf_commutative sba3_inf_right_dist_sup sba5_inf_absorb sup_right_divisibility)
  show "\<And>x y. x \<sqinter> y \<le> y"
    by (metis inf_left_isotone sba5_inf_absorb sba5_inf_commutative sup_ge2)
  show "\<And>x y z. x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (metis inf_left_isotone sba5_inf_absorb sup.orderE sup_monoid.add_commute)
  show "\<And>x y z. x \<squnion> y \<sqinter> z = (x \<squnion> y) \<sqinter> (x \<squnion> z) "
    by (metis sba3_inf_right_dist_sup sba5_inf_absorb sba5_inf_commutative sup_assoc)
qed

lemma inf_demorgan_2:
  "-(x \<sqinter> y) = -x \<squnion> -y"
  using sba3_complement_inf_double_complement sba5_inf_commutative sub_sup_closed sub_sup_demorgan by auto

lemma inf_export:
  "x \<sqinter> -(x \<sqinter> y) = x \<sqinter> -y"
  using inf_demorgan_2 sba3_inf_complement_bot sba3_inf_right_dist_sup sba5_inf_commutative by auto

lemma complement_inf[simp]:
  "x \<sqinter> -x = bot"
  using sba3_inf_complement_bot sba5_inf_commutative by auto

text \<open>Theorem 18.2\<close>

subclass stone_algebra
proof
  show "\<And>x. x \<le> top"
    by (simp add: inf.absorb_iff2)
  show "\<And>x y. (x \<sqinter> y = bot) = (x \<le> - y)"
    by (metis (full_types) complement_bot complement_inf inf.cobounded1 inf.order_iff inf_export sba3_complement_inf_double_complement sba3_inf_left_unit)
  show "\<And>x. - x \<squnion> - - x = top"
    by simp
qed

text \<open>Theorem 18.1\<close>

subclass subset_boolean_algebra_4_extended
proof
  show "\<And>x. x \<sqinter> top = x"
    by simp
  show "\<And>x y z. x \<le> y \<Longrightarrow> z \<sqinter> x \<le> z \<sqinter> y"
    using inf.sup_right_isotone by blast
qed

end

context stone_algebra_extended
begin

text \<open>Theorem 18.3\<close>

subclass subset_boolean_algebra_5_extended
proof
  show "\<And>x y z. x \<squnion> (y \<squnion> z) = x \<squnion> y \<squnion> z"
    using sup_assoc by auto
  show "\<And>x y. x \<squnion> y = y \<squnion> x"
    by (simp add: sup_commute)
  show "\<And>x. x \<squnion> x = x"
    by simp
  show "\<And>x y. x \<squnion> - (y \<squnion> - y) = x"
    by simp
  show "\<And>x y. - (x \<squnion> y) = - (- - x \<squnion> - - y)"
    by auto
  show "\<And>x y. - x \<squnion> - (- x \<squnion> y) = - x \<squnion> - y"
    by (metis maddux_3_21_pp p_dist_sup regular_closed_p)
  show "bot = (THE x. \<forall>z. x = - (z \<squnion> - z))"
    by simp
  thus "top = - (THE x. \<forall>z. x = - (z \<squnion> - z))"
    using p_bot by blast
  show "\<And>x y. - x \<sqinter> - y = - (- - x \<squnion> - - y)"
    by simp
  show "\<And>x y. - x - - y = - (- - x \<squnion> - y)"
    by auto
  show "\<And>x y. (x \<le> y) = (x \<squnion> y = y)"
    by (simp add: le_iff_sup)
  thus "\<And>x y. (x < y) = (x \<squnion> y = y \<and> y \<squnion> x \<noteq> x)"
    by (simp add: less_le_not_le)
  show "\<And>x y z. x \<sqinter> (y \<sqinter> z) = x \<sqinter> y \<sqinter> z"
    by (simp add: inf.sup_monoid.add_assoc)
  show "\<And>x y z. (x \<squnion> y) \<sqinter> z = x \<sqinter> z \<squnion> y \<sqinter> z"
    by (simp add: inf_sup_distrib2)
  show "\<And>x. - x \<sqinter> x = bot"
    by simp
  show "\<And>x. top \<sqinter> x = x"
    by simp
  show "\<And>x y. - (x \<sqinter> - - y) = - (x \<sqinter> y)"
    by simp
  show "\<And>x y. x \<sqinter> y = y \<sqinter> x"
    by (simp add: inf_commute)
  show "\<And>x y. x \<sqinter> (x \<squnion> y) = x"
    by simp
qed

end

section \<open>Domain Semirings\<close>

text \<open>
The following development of tests in IL-semirings, prepredomain semirings, predomain semirings and domain semirings is mostly based on \cite{MoellerDesharnais2019}; see also \cite{DesharnaisMoeller2014}.
See \cite{DesharnaisMoellerStruth2006b} for domain axioms in idempotent semirings.
See \cite{DesharnaisJipsenStruth2009,JacksonStokes2004} for domain axioms in semigroups and monoids.
Some variants have been implemented in \cite{GomesGuttmannHoefnerStruthWeber2016}.
\<close>

subsection \<open>Idempotent Left Semirings\<close>

text \<open>Definition 19\<close>

class il_semiring = sup + inf + bot + top + ord +
  assumes il_associative: "x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
  assumes il_commutative: "x \<squnion> y = y \<squnion> x"
  assumes il_idempotent[simp]: "x \<squnion> x = x"
  assumes il_bot_unit: "x \<squnion> bot = x"
  assumes il_inf_associative: "x \<sqinter> (y \<sqinter> z) = (x \<sqinter> y) \<sqinter> z"
  assumes il_inf_right_dist_sup: "(x \<squnion> y) \<sqinter> z = (x \<sqinter> z) \<squnion> (y \<sqinter> z)"
  assumes il_inf_left_unit[simp]: "top \<sqinter> x = x"
  assumes il_inf_right_unit[simp]: "x \<sqinter> top = x"
  assumes il_sub_inf_left_zero[simp]: "bot \<sqinter> x = bot"
  assumes il_sub_inf_right_isotone: "x \<le> y \<Longrightarrow> z \<sqinter> x \<le> z \<sqinter> y"
  assumes il_less_eq: "x \<le> y \<longleftrightarrow> x \<squnion> y = y"
  assumes il_less_def: "x < y \<longleftrightarrow> x \<le> y \<and> \<not>(y \<le> x)"
begin

lemma il_unit_bot: "bot \<squnion> x = x"
  using il_bot_unit il_commutative by fastforce

subclass order
proof
  show "\<And>x y. (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: il_less_def)
  show "\<And>x. x \<le> x"
    by (simp add: il_less_eq)
  show "\<And>x y z. x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (metis il_associative il_less_eq)
  show "\<And>x y. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: il_commutative il_less_eq)
qed

lemma il_sub_inf_right_isotone_var:
  "(x \<sqinter> y) \<squnion> (x \<sqinter> z) \<le> x \<sqinter> (y \<squnion> z)"
  by (smt il_associative il_commutative il_idempotent il_less_eq il_sub_inf_right_isotone)

lemma il_sub_inf_left_isotone:
  "x \<le> y \<Longrightarrow> x \<sqinter> z \<le> y \<sqinter> z"
  by (metis il_inf_right_dist_sup il_less_eq)

lemma il_sub_inf_left_isotone_var:
  "(y \<sqinter> x) \<squnion> (z \<sqinter> x) \<le> (y \<squnion> z) \<sqinter> x"
  by (simp add: il_inf_right_dist_sup)

lemma sup_left_isotone:
  "x \<le> y \<Longrightarrow> x \<squnion> z \<le> y \<squnion> z"
  by (smt il_associative il_commutative il_idempotent il_less_eq)

lemma sup_right_isotone:
  "x \<le> y \<Longrightarrow> z \<squnion> x \<le> z \<squnion> y"
  by (simp add: il_commutative sup_left_isotone)

lemma bot_least:
  "bot \<le> x"
  by (simp add: il_less_eq il_unit_bot)

lemma less_eq_bot:
  "x \<le> bot \<longleftrightarrow> x = bot"
  by (simp add: il_bot_unit il_less_eq)

abbreviation are_complementary :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "are_complementary x y \<equiv> x \<squnion> y = top \<and> x \<sqinter> y = bot \<and> y \<sqinter> x = bot"

abbreviation test :: "'a \<Rightarrow> bool"
  where "test x \<equiv> \<exists>y . are_complementary x y"

definition tests :: "'a set"
  where "tests = { x . test x }"

lemma bot_test:
  "test bot"
  by (simp add: il_unit_bot)

lemma top_test:
  "test top"
  by (simp add: il_bot_unit)

lemma test_sub_identity:
  "test x \<Longrightarrow> x \<le> top"
  using il_associative il_less_eq by auto

lemma neg_unique:
  "are_complementary x y \<Longrightarrow> are_complementary x z \<Longrightarrow> y = z"
  by (metis antisym il_inf_left_unit il_inf_right_dist_sup il_inf_right_unit il_sub_inf_right_isotone_var)

definition neg :: "'a \<Rightarrow> 'a" ("!")
  where "!x \<equiv> THE y . are_complementary x y"

lemma neg_char:
  assumes "test x"
    shows "are_complementary x (!x)"
proof (unfold neg_def)
  from assms obtain y where 1: "are_complementary x y"
    by auto
  show "are_complementary x (THE y. are_complementary x y)"
  proof (rule theI)
    show "are_complementary x y"
      using 1 by simp
    show "\<And>z. are_complementary x z \<Longrightarrow> z = y"
      using 1 neg_unique by blast
  qed
qed

lemma are_complementary_symmetric:
  "are_complementary x y \<longleftrightarrow> are_complementary y x"
  using il_commutative by auto

lemma neg_test:
  "test x \<Longrightarrow> test (!x)"
  using are_complementary_symmetric neg_char by blast

lemma are_complementary_test:
  "test x \<Longrightarrow> are_complementary x y \<Longrightarrow> test y"
  using il_commutative by auto

lemma neg_involutive:
  "test x \<Longrightarrow> !(!x) = x"
  using are_complementary_symmetric neg_char neg_unique by blast

lemma test_inf_left_below:
  "test x \<Longrightarrow> x \<sqinter> y \<le> y"
  by (metis il_associative il_idempotent il_inf_left_unit il_inf_right_dist_sup il_less_eq)

lemma test_inf_right_below:
  "test x \<Longrightarrow> y \<sqinter> x \<le> y"
  by (metis il_inf_right_unit il_sub_inf_right_isotone test_sub_identity)

lemma neg_bot:
  "!bot = top"
  using il_unit_bot neg_char by fastforce

lemma neg_top:
  "!top = bot"
  using bot_test neg_bot neg_involutive by fastforce

lemma test_inf_idempotent:
  "test x \<Longrightarrow> x \<sqinter> x = x"
  by (metis il_bot_unit il_inf_left_unit il_inf_right_dist_sup)

lemma test_inf_semicommutative:
  assumes "test x"
      and "test y"
  shows "x \<sqinter> y \<le> y \<sqinter> x"
proof -
  have "x \<sqinter> y = (y \<sqinter> x \<sqinter> y) \<squnion> (!y \<sqinter> x \<sqinter> y)"
    by (metis assms(2) il_inf_left_unit il_inf_right_dist_sup neg_char)
  also have "... \<le> (y \<sqinter> x \<sqinter> y) \<squnion> (!y \<sqinter> y)"
  proof -
    obtain z where "are_complementary y z"
      using assms(2) by blast
    hence "y \<sqinter> (x \<sqinter> y) \<squnion> !y \<sqinter> (x \<sqinter> y) \<le> y \<sqinter> (x \<sqinter> y)"
      by (metis assms(1) calculation il_sub_inf_left_isotone il_bot_unit il_idempotent il_inf_associative il_less_eq neg_char test_inf_right_below)
    thus ?thesis
      by (simp add: il_associative il_inf_associative il_less_eq)
  qed
  also have "... \<le> (y \<sqinter> x) \<squnion> (!y \<sqinter> y)"
    by (metis assms(2) il_bot_unit il_inf_right_unit il_sub_inf_right_isotone neg_char test_sub_identity)
  also have "... = y \<sqinter> x"
    by (simp add: assms(2) il_bot_unit neg_char)
  finally show ?thesis
    .
qed

lemma test_inf_commutative:
  "test x \<Longrightarrow> test y \<Longrightarrow> x \<sqinter> y = y \<sqinter> x"
  by (simp add: antisym test_inf_semicommutative)

lemma test_inf_bot:
  "test x \<Longrightarrow> x \<sqinter> bot = bot"
  using il_inf_associative test_inf_idempotent by fastforce

lemma test_absorb_1:
  "test x \<Longrightarrow> test y \<Longrightarrow> x \<squnion> (x \<sqinter> y) = x"
  using il_commutative il_less_eq test_inf_right_below by auto

lemma test_absorb_2:
  "test x \<Longrightarrow> test y \<Longrightarrow> x \<squnion> (y \<sqinter> x) = x"
  by (metis test_absorb_1 test_inf_commutative)

lemma test_absorb_3:
  "test x \<Longrightarrow> test y \<Longrightarrow> x \<sqinter> (x \<squnion> y) = x"
  apply (rule antisym)
  apply (metis il_associative il_inf_right_unit il_less_eq il_sub_inf_right_isotone test_sub_identity)
  by (metis il_sub_inf_right_isotone_var test_absorb_1 test_inf_idempotent)

lemma test_absorb_4:
  "test x \<Longrightarrow> test y \<Longrightarrow> (x \<squnion> y) \<sqinter> x = x"
  by (smt il_inf_right_dist_sup test_inf_idempotent il_commutative il_less_eq test_inf_left_below)

lemma test_import_1:
  assumes "test x"
      and "test y"
    shows "x \<squnion> (!x \<sqinter> y) = x \<squnion> y"
proof -
  have "x \<squnion> (!x \<sqinter> y) = x \<squnion> ((y \<squnion> !y) \<sqinter> x) \<squnion> (!x \<sqinter> y)"
    by (simp add: assms(2) neg_char)
  also have "... = x \<squnion> (!y \<sqinter> x) \<squnion> (x \<sqinter> y) \<squnion> (!x \<sqinter> y)"
    by (smt assms il_associative il_commutative il_inf_right_dist_sup test_inf_commutative)
  also have "... = x \<squnion> ((x \<squnion> !x) \<sqinter> y)"
    by (smt calculation il_associative il_commutative il_idempotent il_inf_right_dist_sup)
  also have "... = x \<squnion> y"
    by (simp add: assms(1) neg_char)
  finally show ?thesis
    .
qed

lemma test_import_2:
  assumes "test x"
      and "test y"
    shows "x \<squnion> (y \<sqinter> !x) = x \<squnion> y"
proof -
  obtain z where 1: "are_complementary y z"
    using assms(2) by moura
  obtain w where 2: "are_complementary x w"
    using assms(1) by auto
  hence "x \<sqinter> !x = bot"
    using neg_char by blast
  hence "!x \<sqinter> y = y \<sqinter> !x"
    using 1 2 by (metis il_commutative neg_char test_inf_commutative)
  thus ?thesis
    using 1 2 by (metis test_import_1)
qed

lemma test_import_3:
  assumes "test x"
    shows "(!x \<squnion> y) \<sqinter> x = y \<sqinter> x"
  by (simp add: assms(1) il_inf_right_dist_sup il_unit_bot neg_char)

lemma test_import_4:
  assumes "test x"
      and "test y"
    shows "(!x \<squnion> y) \<sqinter> x = x \<sqinter> y"
  by (metis assms test_import_3 test_inf_commutative)

lemma test_inf:
  "test x \<Longrightarrow> test y \<Longrightarrow> test z \<Longrightarrow> z \<le> x \<sqinter> y \<longleftrightarrow> z \<le> x \<and> z \<le> y"
  apply (rule iffI)
  using dual_order.trans test_inf_left_below test_inf_right_below apply blast
  by (smt il_less_eq il_sub_inf_right_isotone test_absorb_4)

lemma test_shunting:
  assumes "test x"
      and "test y"
    shows "x \<sqinter> y \<le> z \<longleftrightarrow> x \<le> !y \<squnion> z"
proof
  assume 1: "x \<sqinter> y \<le> z"
  have "x = (!y \<sqinter> x) \<squnion> (y \<sqinter> x)"
    by (metis assms(2) il_commutative il_inf_left_unit il_inf_right_dist_sup neg_char)
  also have "... \<le> !y \<squnion> (y \<sqinter> x)"
    by (simp add: assms(1) sup_left_isotone test_inf_right_below)
  also have "... \<le> !y \<squnion> z"
    using 1 by (simp add: assms sup_right_isotone test_inf_commutative)
  finally show "x \<le> !y \<squnion> z"
    .
next
  assume "x \<le> !y \<squnion> z"
  hence "x \<sqinter> y \<le> (!y \<squnion> z) \<sqinter> y"
    using il_sub_inf_left_isotone by blast
  also have "... = z \<sqinter> y"
    by (simp add: assms(2) test_import_3)
  also have "... \<le> z"
    by (simp add: assms(2) test_inf_right_below)
  finally show "x \<sqinter> y \<le> z"
    .
qed

lemma test_shunting_bot:
  assumes "test x"
      and "test y"
    shows "x \<le> y \<longleftrightarrow> x \<sqinter> !y \<le> bot"
  by (simp add: assms il_bot_unit neg_involutive neg_test test_shunting)

lemma test_shunting_bot_eq:
  assumes "test x"
      and "test y"
    shows "x \<le> y \<longleftrightarrow> x \<sqinter> !y = bot"
  by (simp add: assms test_shunting_bot less_eq_bot)

lemma neg_antitone:
  assumes "test x"
      and "test y"
      and "x \<le> y"
    shows "!y \<le> !x"
proof -
  have 1: "x \<sqinter> !y = bot"
    using assms test_shunting_bot_eq by blast
  have 2: "x \<squnion> !x = top"
    by (simp add: assms(1) neg_char)
  have "are_complementary y (!y)"
    by (simp add: assms(2) neg_char)
  thus ?thesis
    using 1 2 by (metis il_unit_bot il_commutative il_inf_left_unit il_inf_right_dist_sup il_inf_right_unit il_sub_inf_right_isotone test_sub_identity)
qed

lemma test_sup_neg_1:
  assumes "test x"
      and "test y"
    shows "(x \<squnion> y) \<squnion> (!x \<sqinter> !y) = top"
proof -
  have "x \<squnion> !x = top"
    by (simp add: assms(1) neg_char)
  hence "x \<squnion> (y \<squnion> !x) = top"
    by (metis assms(2) il_associative il_commutative il_idempotent)
  hence "x \<squnion> (y \<squnion> !x \<sqinter> !y) = top"
    by (simp add: assms neg_test test_import_2)
  thus ?thesis
    by (simp add: il_associative)
qed

lemma test_sup_neg_2:
  assumes "test x"
      and "test y"
    shows "(x \<squnion> y) \<sqinter> (!x \<sqinter> !y) = bot"
proof -
  have 1: "are_complementary y (!y)"
    by (simp add: assms(2) neg_char)
  obtain z where 2: "are_complementary x z"
    using assms(1) by auto
  hence "!x = z"
    using neg_char neg_unique by blast
  thus ?thesis
    using 1 2 by (metis are_complementary_symmetric il_inf_associative neg_involutive test_import_3 test_inf_bot test_inf_commutative)
qed

lemma de_morgan_1:
  assumes "test x"
      and "test y"
      and "test (x \<sqinter> y)"
    shows "!(x \<sqinter> y) = !x \<squnion> !y"
proof (rule antisym)
  have 1: "test (!(x \<sqinter> y))"
    by (simp add: assms neg_test)
  have "x \<le> (x \<sqinter> y) \<squnion> !y"
    by (metis (full_types) assms il_commutative neg_char test_shunting test_shunting_bot_eq)
  hence "x \<sqinter> !(x \<sqinter> y) \<le> !y"
    using 1 by (simp add: assms(1,3) neg_involutive test_shunting)
  hence "!(x \<sqinter> y) \<sqinter> x \<le> !y"
    using 1 by (metis assms(1) test_inf_commutative)
  thus "!(x \<sqinter> y) \<le> !x \<squnion> !y"
    using 1 assms(1) test_shunting by blast
  have 2: "!x \<le> !(x \<sqinter> y)"
    by (simp add: assms neg_antitone test_inf_right_below)
  have "!y \<le> !(x \<sqinter> y)"
    by (simp add: assms neg_antitone test_inf_left_below)
  thus "!x \<squnion> !y \<le> !(x \<sqinter> y)"
    using 2 by (metis il_associative il_less_eq)
qed

lemma de_morgan_2:
  assumes "test x"
      and "test y"
      and "test (x \<squnion> y)"
    shows "!(x \<squnion> y) = !x \<sqinter> !y"
proof (rule antisym)
  have 1: "!(x \<squnion> y) \<le> !x"
    by (metis assms il_inf_left_unit il_sub_inf_left_isotone neg_antitone test_absorb_3 test_sub_identity)
  have "!(x \<squnion> y) \<le> !y"
    by (metis assms il_commutative il_inf_left_unit il_sub_inf_left_isotone neg_antitone test_absorb_3 test_sub_identity)
  thus "!(x \<squnion> y) \<le> !x \<sqinter> !y"
    using 1 by (simp add: assms neg_test test_inf)
  have "top \<le> x \<squnion> y \<squnion> !(x \<squnion> y)"
    by (simp add: assms(3) neg_char)
  hence "top \<sqinter> !x \<le> y \<squnion> !(x \<squnion> y)"
    by (smt assms(1) assms(3) il_commutative il_inf_right_dist_sup il_inf_right_unit il_sub_inf_right_isotone il_unit_bot neg_char test_sub_identity)
  thus "!x \<sqinter> !y \<le> !(x \<squnion> y)"
    by (simp add: assms(1) assms(2) neg_involutive neg_test test_shunting)
qed

lemma test_inf_closed_sup_complement:
  assumes "test x"
      and "test y"
      and "\<forall>u v . test u \<and> test v \<longrightarrow> test (u \<sqinter> v)"
    shows "!x \<sqinter> !y \<sqinter> (x \<squnion> y) = bot"
proof -
  have 1: "!(!x \<sqinter> !y) = x \<squnion> y"
    by (simp add: assms de_morgan_1 neg_involutive neg_test)
  have "test (!(!x \<sqinter> !y))"
    by (metis assms neg_test)
  thus ?thesis
    using 1 by (metis assms(1,2) de_morgan_2 neg_char)
qed

lemma test_sup_complement_sup_closed:
  assumes "test x"
      and "test y"
      and "\<forall>u v . test u \<and> test v \<longrightarrow> !u \<sqinter> !v \<sqinter> (u \<squnion> v) = bot"
    shows "test (x \<squnion> y)"
  by (meson assms test_sup_neg_1 test_sup_neg_2)

lemma test_inf_closed_sup_closed:
  assumes "test x"
      and "test y"
      and "\<forall>u v . test u \<and> test v \<longrightarrow> test (u \<sqinter> v)"
    shows "test (x \<squnion> y)"
  using assms test_inf_closed_sup_complement test_sup_complement_sup_closed by simp

end

subsection \<open>Prepredomain Semirings\<close>

class dom =
  fixes d :: "'a \<Rightarrow> 'a"

class ppd_semiring = il_semiring + dom +
  assumes d_closed: "test (d x)"
  assumes d1: "x \<le> d x \<sqinter> x"
begin

lemma d_sub_identity:
  "d x \<le> top"
  using d_closed test_sub_identity by blast

lemma d1_eq:
  "x = d x \<sqinter> x"
proof -
  have "x = (d x \<squnion> top) \<sqinter> x"
    using d_sub_identity il_less_eq by auto
  thus ?thesis
    using d1 il_commutative il_inf_right_dist_sup il_less_eq by force
qed

lemma d_increasing_sub_identity:
  "x \<le> top \<Longrightarrow> x \<le> d x"
  by (metis d1_eq il_inf_right_unit il_sub_inf_right_isotone)

lemma d_top:
  "d top = top"
  by (simp add: d_increasing_sub_identity d_sub_identity dual_order.antisym)

lemma d_bot_only:
  "d x = bot \<Longrightarrow> x = bot"
  by (metis d1_eq il_sub_inf_left_zero)

lemma d_strict: "d bot \<le> bot" nitpick [expect=genuine] oops
lemma d_isotone_var: "d x \<le> d (x \<squnion> y)" nitpick [expect=genuine] oops
lemma d_fully_strict: "d x = bot \<longleftrightarrow> x = bot" nitpick [expect=genuine] oops
lemma test_d_fixpoint: "test x \<Longrightarrow> d x = x" nitpick [expect=genuine] oops

end

subsection \<open>Predomain Semirings\<close>

class pd_semiring = ppd_semiring +
  assumes d2: "test p \<Longrightarrow> d (p \<sqinter> x) \<le> p"
begin

lemma d_strict:
  "d bot \<le> bot"
  using bot_test d2 by fastforce

lemma d_strict_eq:
  "d bot = bot"
  using d_strict il_bot_unit il_less_eq by auto

lemma test_d_fixpoint:
  "test x \<Longrightarrow> d x = x"
  by (metis antisym d1_eq d2 test_inf_idempotent test_inf_right_below)

lemma d_surjective:
  "test x \<Longrightarrow> \<exists>y . d y = x"
  using test_d_fixpoint by blast

lemma test_d_fixpoint_iff:
  "test x \<longleftrightarrow> d x = x"
  by (metis d_closed test_d_fixpoint)

lemma d_surjective_iff:
  "test x \<longleftrightarrow> (\<exists>y . d y = x)"
  using d_surjective d_closed by blast

lemma tests_d_range:
  "tests = range d"
  using tests_def image_def d_surjective_iff by auto

lemma llp:
  assumes "test y"
    shows "d x \<le> y \<longleftrightarrow> x \<le> y \<sqinter> x"
  by (metis assms d1_eq d2 eq_iff il_sub_inf_left_isotone test_inf_left_below)

lemma gla:
  assumes "test y"
    shows "y \<le> !(d x) \<longleftrightarrow> y \<sqinter> x \<le> bot"
proof -
  obtain ad where 1: "\<forall>x. are_complementary (d x) (ad x)"
    using d_closed by moura
  hence 2: "\<forall>x y. d (d y \<sqinter> x) \<le> d y"
    using d2 by blast
  have 3: "\<forall>x. ad x \<sqinter> x = bot"
    using 1 by (metis d1_eq il_inf_associative il_sub_inf_left_zero)
  have 4: "\<forall>x y. d y \<sqinter> x \<squnion> ad y \<sqinter> x = top \<sqinter> x"
    using 1 by (metis il_inf_right_dist_sup)
  have 5: "\<forall>x y z. z \<sqinter> y \<le> x \<sqinter> y \<or> (z \<squnion> x) \<sqinter> y \<noteq> x \<sqinter> y"
    by (simp add: il_inf_right_dist_sup il_less_eq)
  have 6: "\<forall>x. !(d x) = ad x"
    using 1 neg_char neg_unique by blast
  have 7: "\<forall>x. top \<sqinter> x = x"
    by auto
  hence "\<forall>x. y \<sqinter> x \<squnion> !y \<sqinter> x = x"
    by (metis assms il_inf_right_dist_sup neg_char)
  thus ?thesis
    using 1 2 3 4 5 6 7 by (metis assms d1_eq il_commutative il_less_eq test_d_fixpoint)
qed

lemma gla_var:
  "test y \<Longrightarrow> y \<sqinter> d x \<le> bot \<longleftrightarrow> y \<sqinter> x \<le> bot"
  using gla d_closed il_bot_unit test_shunting by auto

lemma llp_var:
  assumes "test y"
    shows "y \<le> !(d x) \<longleftrightarrow> x \<le> !y \<sqinter> x"
  apply (rule iffI)
  apply (metis (no_types, hide_lams) assms gla Least_equality il_inf_left_unit il_inf_right_dist_sup il_less_eq il_unit_bot order.refl neg_char)
  by (metis assms gla gla_var llp il_commutative il_sub_inf_right_isotone neg_char)

lemma d_idempotent:
  "d (d x) = d x"
  using d_closed test_d_fixpoint_iff by auto

lemma d_neg:
  "test x \<Longrightarrow> d (!x) = !x"
  using il_commutative neg_char test_d_fixpoint_iff by fastforce

lemma d_fully_strict:
  "d x = bot \<longleftrightarrow> x = bot"
  using d_strict_eq d_bot_only by blast

lemma d_ad_comp:
  "!(d x) \<sqinter> x = bot"
proof -
  have "\<forall>x. !(d x) \<sqinter> d x = bot"
    by (simp add: d_closed neg_char)
  thus ?thesis
    by (metis d1_eq il_inf_associative il_sub_inf_left_zero)
qed

lemma d_isotone:
  assumes "x \<le> y"
    shows "d x \<le> d y"
proof -
  obtain ad where 1: "\<forall>x. are_complementary (d x) (ad x)"
    using d_closed by moura
  hence "ad y \<sqinter> x \<le> bot"
    by (metis assms d1_eq il_inf_associative il_sub_inf_left_zero il_sub_inf_right_isotone)
  thus ?thesis
    using 1 by (metis d2 il_bot_unit il_inf_left_unit il_inf_right_dist_sup il_less_eq)
qed

lemma d_isotone_var:
  "d x \<le> d (x \<squnion> y)"
  using d_isotone il_associative il_less_eq by auto

lemma d3_conv:
  "d (x \<sqinter> y) \<le> d (x \<sqinter> d y)"
  by (metis (mono_tags, hide_lams) d1_eq d2 d_closed il_inf_associative)

lemma d_test_inf_idempotent:
  "d x \<sqinter> d x = d x"
  by (metis d_idempotent d1_eq)

lemma d_test_inf_closed:
  assumes "test x"
      and "test y"
    shows "d (x \<sqinter> y) = x \<sqinter> y"
proof (rule antisym)
  have "d (x \<sqinter> y) = d (x \<sqinter> y) \<sqinter> d (x \<sqinter> y)"
    by (simp add: d_test_inf_idempotent)
  also have "... \<le> x \<sqinter> d (x \<sqinter> y)"
    by (simp add: assms(1) d2 il_sub_inf_left_isotone)
  also have "... \<le> x \<sqinter> y"
    by (metis assms d_isotone il_sub_inf_right_isotone test_inf_left_below test_d_fixpoint)
  finally show "d (x \<sqinter> y) \<le> x \<sqinter> y"
    .
  show "x \<sqinter> y \<le> d (x \<sqinter> y)"
    using assms d_increasing_sub_identity dual_order.trans test_inf_left_below test_sub_identity by blast
qed

lemma test_inf_closed:
  "test x \<Longrightarrow> test y \<Longrightarrow> test (x \<sqinter> y)"
  using d_test_inf_closed test_d_fixpoint_iff by simp

lemma test_sup_closed:
  "test x \<Longrightarrow> test y \<Longrightarrow> test (x \<squnion> y)"
  using test_inf_closed test_inf_closed_sup_closed by simp

lemma d_export:
  assumes "test x"
    shows "d (x \<sqinter> y) = x \<sqinter> d y"
proof (rule antisym)
  have 1: "d (x \<sqinter> y) \<le> x"
    by (simp add: assms d2)
  have "d (x \<sqinter> y) \<le> d y"
    by (metis assms d_isotone_var il_inf_left_unit il_inf_right_dist_sup)
  thus "d (x \<sqinter> y) \<le> x \<sqinter> d y"
    using 1 by (metis assms d_idempotent llp dual_order.trans il_sub_inf_right_isotone)
  have "y = (!x \<sqinter> y) \<squnion> (x \<sqinter> y)"
    by (metis assms il_commutative il_inf_left_unit il_inf_right_dist_sup neg_char)
  also have "... = (!x \<sqinter> y) \<squnion> (d (x \<sqinter> y) \<sqinter> x \<sqinter> y)"
    by (metis d1_eq il_inf_associative)
  also have "... = (!x \<sqinter> y) \<squnion> (d (x \<sqinter> y) \<sqinter> y)"
    using 1 by (smt calculation d1_eq il_associative il_commutative il_inf_associative il_inf_right_dist_sup il_less_eq il_sub_inf_right_isotone_var)
  also have "... = (!x \<squnion> d (x \<sqinter> y)) \<sqinter> y"
    by (simp add: il_inf_right_dist_sup)
  finally have "y \<le> (!x \<squnion> d (x \<sqinter> y)) \<sqinter> y"
    by simp
  hence "d y \<le> !x \<squnion> d (x \<sqinter> y)"
    using assms llp test_sup_closed neg_test d_closed by simp
  hence "d y \<sqinter> x \<le> d (x \<sqinter> y)"
    by (simp add: assms d_closed test_shunting)
  thus "x \<sqinter> d y \<le> d (x \<sqinter> y)"
    by (metis assms d_closed test_inf_commutative)
qed

lemma test_inf_left_dist_sup:
  assumes "test x"
      and "test y"
      and "test z"
    shows "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
proof -
  have "x \<sqinter> (y \<squnion> z) = (y \<squnion> z) \<sqinter> x"
    using assms test_sup_closed test_inf_commutative by smt
  also have "... = (y \<sqinter> x) \<squnion> (z \<sqinter> x)"
    using il_inf_right_dist_sup by simp
  also have "... = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
    using assms test_sup_closed test_inf_commutative by smt
  finally show ?thesis
    .
qed

lemma "!x \<squnion> !y = !(!(!x \<squnion> !y))" nitpick [expect=genuine] oops
lemma "d x = !(!x)" nitpick [expect=genuine] oops

sublocale subset_boolean_algebra where uminus = "\<lambda> x . !(d x)"
proof
  show "\<And>x y z. !(d x) \<squnion> (!(d y) \<squnion> !(d z)) = !(d x) \<squnion> !(d y) \<squnion> !(d z)"
    using il_associative by blast
  show "\<And>x y. !(d x) \<squnion> !(d y) = !(d y) \<squnion> !(d x)"
    by (simp add: il_commutative)
  show "\<And>x y. !(d x) \<squnion> !(d y) = !(d (!(d (!(d x) \<squnion> !(d y)))))"
  proof -
    fix x y
    have "test (!(d x)) \<and> test (!(d y))"
      by (simp add: d_closed neg_test)
    hence "test (!(d x) \<squnion> !(d y))"
      by (simp add: test_sup_closed)
    thus "!(d x) \<squnion> !(d y) = !(d (!(d (!(d x) \<squnion> !(d y)))))"
      by (simp add: d_neg neg_involutive test_d_fixpoint)
  qed
  show "\<And>x y. !(d x) = !(d (!(d (!(d x))) \<squnion> !(d y))) \<squnion> !(d (!(d (!(d x))) \<squnion> !(d (!(d y)))))"
  proof -
    fix x y
    have "!(d (!(d (!(d x))) \<squnion> !(d y))) \<squnion> !(d (!(d (!(d x))) \<squnion> !(d (!(d y))))) = !(d x \<squnion> !(d y)) \<squnion> !(d x \<squnion> d y)"
      using d_closed neg_test test_sup_closed neg_involutive test_d_fixpoint by auto
    also have "... = (!(d x) \<sqinter> d y) \<squnion> (!(d x) \<sqinter> !(d y))"
      using d_closed neg_test test_sup_closed neg_involutive de_morgan_2 by auto
    also have "... = !(d x) \<sqinter> (d y \<squnion> !(d y))"
      using d_closed neg_test test_inf_left_dist_sup by auto
    also have "... = !(d x) \<sqinter> top"
      by (simp add: neg_char d_closed)
    finally show "!(d x) = !(d (!(d (!(d x))) \<squnion> !(d y))) \<squnion> !(d (!(d (!(d x))) \<squnion> !(d (!(d y)))))"
      by simp
  qed
qed

lemma d_dist_sup:
  "d (x \<squnion> y) = d x \<squnion> d y"
proof (rule antisym)
  have "x \<le> d x \<sqinter> x"
    by (simp add: d1)
  also have "... \<le> (d x \<squnion> d y) \<sqinter> (x \<squnion> y)"
    using il_associative il_inf_right_dist_sup il_less_eq il_sub_inf_right_isotone by auto
  finally have 1: "x \<le> (d x \<squnion> d y) \<sqinter> (x \<squnion> y)"
    .
  have "y \<le> d y \<sqinter> y"
    by (simp add: d1)
  also have "... \<le> (d y \<squnion> d x) \<sqinter> (y \<squnion> x)"
    using il_associative il_idempotent il_inf_right_dist_sup il_less_eq il_sub_inf_right_isotone by simp
  finally have "y \<le> (d x \<squnion> d y) \<sqinter> (x \<squnion> y)"
    using il_commutative by auto
  hence "x \<squnion> y \<le> (d x \<squnion> d y) \<sqinter> (x \<squnion> y)"
    using 1 by (metis il_associative il_less_eq)
  thus "d (x \<squnion> y) \<le> d x \<squnion> d y"
    using llp test_sup_closed neg_test d_closed by simp
  show "d x \<squnion> d y \<le> d (x \<squnion> y)"
    using d_isotone_var il_associative il_commutative il_less_eq by fastforce
qed

end

class pd_semiring_extended = pd_semiring + uminus +
  assumes uminus_def: "-x = !(d x)"
begin

subclass subset_boolean_algebra
  by (metis subset_boolean_algebra_axioms uminus_def ext)

end

subsection \<open>Domain Semirings\<close>

class d_semiring = pd_semiring +
  assumes d3: "d (x \<sqinter> d y) \<le> d (x \<sqinter> y)"
begin

lemma d3_eq: "d (x \<sqinter> d y) = d (x \<sqinter> y)"
  by (simp add: antisym d3 d3_conv)

end

text \<open>
Axioms (d1), (d2) and (d3) are independent in IL-semirings.
\<close>

context il_semiring
begin

context
  fixes d :: "'a \<Rightarrow> 'a"
  assumes d_closed: "test (d x)"
begin

context
  assumes d1: "x \<le> d x \<sqinter> x"
  assumes d2: "test p \<Longrightarrow> d (p \<sqinter> x) \<le> p"
begin

lemma d3: "d (x \<sqinter> d y) \<le> d (x \<sqinter> y)" nitpick [expect=genuine] oops

end

context
  assumes d1: "x \<le> d x \<sqinter> x"
  assumes d3: "d (x \<sqinter> d y) \<le> d (x \<sqinter> y)"
begin

lemma d2: "test p \<Longrightarrow> d (p \<sqinter> x) \<le> p" nitpick [expect=genuine] oops

end

context
  assumes d2: "test p \<Longrightarrow> d (p \<sqinter> x) \<le> p"
  assumes d3: "d (x \<sqinter> d y) \<le> d (x \<sqinter> y)"
begin

lemma d1: "x \<le> d x \<sqinter> x" nitpick [expect=genuine] oops

end

end

end

class d_semiring_var = ppd_semiring +
  assumes d3_var: "d (x \<sqinter> d y) \<le> d (x \<sqinter> y)"
  assumes d_strict_eq_var: "d bot = bot"
begin

lemma d2_var:
  assumes "test p"
    shows "d (p \<sqinter> x) \<le> p"
proof -
  have "!p \<sqinter> p \<sqinter> x = bot"
    by (simp add: assms neg_char)
  hence "d (!p \<sqinter> p \<sqinter> x) = bot"
    by (simp add: d_strict_eq_var)
  hence "d (!p \<sqinter> d (p \<sqinter> x)) = bot"
    by (metis d3_var il_inf_associative less_eq_bot)
  hence "!p \<sqinter> d (p \<sqinter> x) = bot"
    using d_bot_only by blast
  thus ?thesis
    by (metis (no_types, hide_lams) assms d_sub_identity il_bot_unit il_inf_left_unit il_inf_right_dist_sup il_inf_right_unit il_sub_inf_right_isotone neg_char)
qed

subclass d_semiring
proof
  show "\<And>p x. test p \<Longrightarrow> d (p \<sqinter> x) \<le> p"
    by (simp add: d2_var)
  show "\<And>x y. d (x \<sqinter> d y) \<le> d (x \<sqinter> y)"
    by (simp add: d3_var)
qed

end

section \<open>Antidomain Semirings\<close>

text \<open>
We now develop prepreantidomain semirings, preantidomain semirings and antidomain semirings.
See \cite{DesharnaisStruth2008b,DesharnaisStruth2008a,DesharnaisStruth2011} for related work on internal axioms for antidomain.
\<close>

subsection \<open>Prepreantidomain Semirings\<close>

text \<open>Definition 20\<close>

class ppa_semiring = il_semiring + uminus +
  assumes a_inf_complement_bot: "-x \<sqinter> x = bot"
  assumes a_stone[simp]: "-x \<squnion> --x = top"
begin

text \<open>Theorem 21\<close>

lemma l1:
  "-top = bot"
  by (metis a_inf_complement_bot il_inf_right_unit)

lemma l2:
  "-bot = top"
  by (metis l1 a_stone il_unit_bot)

lemma l3:
  "-x \<le> -y \<Longrightarrow> -x \<sqinter> y = bot"
  by (metis a_inf_complement_bot il_bot_unit il_inf_right_dist_sup il_less_eq)

lemma l5:
  "--x \<le> --y \<Longrightarrow> -y \<le> -x"
  by (metis (mono_tags, hide_lams) l3 a_stone bot_least il_bot_unit il_inf_left_unit il_inf_right_dist_sup il_inf_right_unit il_sub_inf_right_isotone sup_right_isotone)

lemma l4:
  "---x = -x"
  by (metis l5 a_inf_complement_bot a_stone antisym bot_least il_inf_left_unit il_inf_right_dist_sup il_inf_right_unit il_sub_inf_right_isotone il_unit_bot)

lemma l6:
  "-x \<sqinter> --x = bot"
  by (metis l3 l5 a_inf_complement_bot a_stone il_inf_left_unit il_inf_right_dist_sup il_inf_right_unit il_less_eq il_sub_inf_right_isotone il_unit_bot)

lemma l7:
  "-x \<sqinter> -y = -y \<sqinter> -x"
  using l6 a_inf_complement_bot a_stone test_inf_commutative by blast

lemma l8:
  "x \<le> --x \<sqinter> x"
  by (metis a_inf_complement_bot a_stone il_idempotent il_inf_left_unit il_inf_right_dist_sup il_less_eq il_unit_bot)

sublocale ppa_ppd: ppd_semiring where d = "\<lambda>x . --x"
proof
  show "\<And>x. test (- - x)"
    using l4 l6 by force
  show "\<And>x. x \<le> - - x \<sqinter> x"
    by (simp add: l8)
qed

(*
The following statements have counterexamples, but they take a while to find.

lemma "- x = - (- - x \<squnion> - y) \<squnion> - (- - x \<squnion> - - y)" nitpick [card=8, expect=genuine] oops
lemma "- x \<squnion> - y = - - (- x \<squnion> - y)" nitpick [card=8, expect=genuine] oops
*)

end

subsection \<open>Preantidomain Semirings\<close>

text \<open>Definition 22\<close>

class pa_semiring = ppa_semiring +
  assumes pad2: "--x \<le> -(-x \<sqinter> y)"
begin

text \<open>Theorem 23\<close>

lemma l10:
  "-x \<sqinter> y = bot \<Longrightarrow> -x \<le> -y"
  by (metis a_stone il_inf_left_unit il_inf_right_dist_sup il_unit_bot l4 pad2)

lemma l10_iff:
  "-x \<sqinter> y = bot \<longleftrightarrow> -x \<le> -y"
  using l10 l3 by blast

lemma l13:
  "--(--x \<sqinter> y) \<le> --x"
  by (metis l4 l5 pad2)

lemma l14:
  "-(x \<sqinter> --y) \<le> -(x \<sqinter> y)"
  by (metis il_inf_associative l4 pad2 ppa_ppd.d1_eq)

lemma l9:
  "x \<le> y \<Longrightarrow> -y \<le> -x"
  by (metis l10 a_inf_complement_bot il_commutative il_less_eq il_sub_inf_right_isotone il_unit_bot)

lemma l11:
  "- x \<squnion> - y = - (- - x \<sqinter> - - y)"
proof -
  have 1: "\<And>x y . x \<le> y \<longleftrightarrow> x \<squnion> y = y"
    by (simp add: il_less_eq)
  have 4: "\<And>x y . \<not>(x \<le> y) \<or> x \<squnion> y = y"
    using 1 by metis
  have 5: "\<And>x y z . (x \<sqinter> y) \<squnion> (x \<sqinter> z) \<le> x \<sqinter> (y \<squnion> z)"
    by (simp add: il_sub_inf_right_isotone_var)
  have 6: "\<And>x y . - - x \<le> - (- x \<sqinter> y)"
    by (simp add: pad2)
  have 7: "\<And>x y z . x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
    by (simp add: il_associative)
  have 8: "\<And>x y z . (x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
    using 7 by metis
  have 9: "\<And>x y . x \<squnion> y = y \<squnion> x"
    by (simp add: il_commutative)
  have 10: "\<And>x . x \<squnion> bot = x"
    by (simp add: il_bot_unit)
  have 11: "\<And>x . x \<squnion> x = x"
    by simp
  have 12: "\<And>x y z . x \<sqinter> (y \<sqinter> z) = (x \<sqinter> y) \<sqinter> z"
    by (simp add: il_inf_associative)
  have 13: "\<And>x y z . (x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
    using 12 by metis
  have 14: "\<And>x . top \<sqinter> x = x"
    by simp
  have 15: "\<And>x . x \<sqinter> top = x"
    by simp
  have 16: "\<And>x y z . (x \<squnion> y) \<sqinter> z = (x \<sqinter> z) \<squnion> (y \<sqinter> z)"
    by (simp add: il_inf_right_dist_sup)
  have 17: "\<And>x y z . (x \<sqinter> y) \<squnion> (z \<sqinter> y) = (x \<squnion> z) \<sqinter> y"
    using 16 by metis
  have 18: "\<And>x . bot \<sqinter> x = bot"
    by simp
  have 19: "\<And>x . - x \<squnion> - - x = top"
    by simp
  have 20: "\<And>x . - x \<sqinter> x = bot"
    by (simp add: a_inf_complement_bot)
  have 23: "\<And>x y z . ((x \<sqinter> y) \<squnion> (x \<sqinter> z)) \<squnion> (x \<sqinter> (y \<squnion> z)) = x \<sqinter> (y \<squnion> z)"
    using 4 5 by metis
  have 24: "\<And>x y z . (x \<sqinter> (y \<squnion> z)) \<squnion> ((x \<sqinter> y) \<squnion> (x \<sqinter> z)) = x \<sqinter> (y \<squnion> z)"
    using 9 23 by metis
  have 25: "\<And>x y . - - x \<squnion> - (- x \<sqinter> y) = - (- x \<sqinter> y)"
    using 4 6 by metis
  have 26: "\<And>x y z . x \<squnion> (y \<squnion> z) = y \<squnion> (x \<squnion> z)"
    using 8 9 by metis
  have 27: "\<And>x y z . (x \<sqinter> y) \<squnion> ((x \<sqinter> z) \<squnion> (x \<sqinter> (y \<squnion> z))) = x \<sqinter> (y \<squnion> z)"
    using 9 24 26 by metis
  have 30: "\<And>x . bot \<squnion> x = x"
    using 9 10 by metis
  have 31: "\<And>x y . x \<squnion> (x \<squnion> y) = x \<squnion> y"
    using 8 11 by metis
  have 34: "\<And>u x y z . ((x \<squnion> y) \<sqinter> z) \<squnion> u = (x \<sqinter> z) \<squnion> ((y \<sqinter> z) \<squnion> u)"
    using 8 17 by metis
  have 35: "\<And>u x y z . (x \<sqinter> (y \<sqinter> z)) \<squnion> (u \<sqinter> z) = ((x \<sqinter> y) \<squnion> u) \<sqinter> z"
    using 13 17 by metis
  have 36: "\<And>u x y z . (x \<sqinter> y) \<squnion> (z \<sqinter> (u \<sqinter> y)) = (x \<squnion> (z \<sqinter> u)) \<sqinter> y"
    using 13 17 by metis
  have 39: "\<And>x y . - x \<squnion> (- - x \<squnion> y) = top \<squnion> y"
    using 8 19 by metis
  have 41: "\<And>x y . - x \<sqinter> (x \<sqinter> y) = bot"
    using 13 18 20 by metis
  have 42: "- top = bot"
    using 15 20 by metis
  have 43: "\<And>x y . (- x \<squnion> y) \<sqinter> x = y \<sqinter> x"
    using 17 20 30 by metis
  have 44: "\<And>x y . (x \<squnion> - y) \<sqinter> y = x \<sqinter> y"
    using 9 17 20 30 by metis
  have 46: "\<And>x . - bot \<squnion> - - x = - bot"
    using 9 20 25 by metis
  have 50: "- bot = top"
    using 19 30 42 by metis
  have 51: "\<And>x . top \<squnion> - - x = top"
    using 46 50 by metis
  have 63: "\<And>x y . x \<squnion> ((x \<sqinter> - y) \<squnion> (x \<sqinter> - - y)) = x"
    using 9 15 19 26 27 by metis
  have 66: "\<And>x y . (- (x \<squnion> y) \<sqinter> x) \<squnion> (- (x \<squnion> y) \<sqinter> y) = bot"
    using 9 20 27 30 by metis
  have 67: "\<And>x y z . (x \<sqinter> - - y) \<squnion> (x \<sqinter> - (- y \<sqinter> z)) = x \<sqinter> - (- y \<sqinter> z)"
    using 11 25 27 by metis
  have 70: "\<And>x y . x \<squnion> (x \<sqinter> - - y) = x"
    using 9 15 27 31 51 by metis
  have 82: "\<And>x . top \<squnion> - x = top"
    using 9 19 31 by metis
  have 89: "\<And>x y . x \<squnion> (- y \<sqinter> x) = x"
    using 14 17 82 by metis
  have 102: "\<And>x y z . x \<squnion> (y \<squnion> (x \<sqinter> - - z)) = y \<squnion> x"
    using 26 70 by metis
  have 104: "\<And>x y . x \<squnion> (x \<sqinter> - y) = x"
    using 9 63 102 by metis
  have 112: "\<And>x y z . (- x \<sqinter> y) \<squnion> ((- - x \<sqinter> y) \<squnion> z) = y \<squnion> z"
    using 14 19 34 by metis
  have 117: "\<And>x y z . x \<squnion> ((x \<sqinter> - y) \<squnion> z) = x \<squnion> z"
    using 8 104 by metis
  have 120: "\<And>x y z . x \<squnion> (y \<squnion> (x \<sqinter> - z)) = y \<squnion> x"
    using 26 104 by metis
  have 124: "\<And>x . - - x \<sqinter> x = x"
    using 14 19 43 by metis
  have 128: "\<And>x y . - - x \<sqinter> (x \<sqinter> y) = x \<sqinter> y"
    using 13 124 by metis
  have 131: "\<And>x . - x \<squnion> - - - x = - x"
    using 9 25 124 by metis
  have 133: "\<And>x . - - - x = - x"
    using 9 104 124 131 by metis
  have 135: "\<And>x y . - x \<squnion> - (- - x \<sqinter> y) = - (- - x \<sqinter> y)"
    using 25 133 by metis
  have 137: "\<And>x y . (- x \<squnion> y) \<sqinter> - - x = y \<sqinter> - - x"
    using 43 133 by metis
  have 145: "\<And>x y z . ((- (x \<sqinter> y) \<sqinter> x) \<squnion> z) \<sqinter> y = z \<sqinter> y"
    using 20 30 35 by metis
  have 183: "\<And>x y z . (x \<squnion> (- - (y \<sqinter> z) \<sqinter> y)) \<sqinter> z = (x \<squnion> y) \<sqinter> z"
    using 17 36 124 by metis
  have 289: "\<And>x y . - x \<squnion> - (- x \<sqinter> y) = top"
    using 25 39 82 by metis
  have 316: "\<And>x y . - (- x \<sqinter> y) \<sqinter> x = x"
    using 14 43 289 by metis
  have 317: "\<And>x y z . - (- x \<sqinter> y) \<sqinter> (x \<sqinter> z) = x \<sqinter> z"
    using 13 316 by metis
  have 320: "\<And>x y . - x \<squnion> - - (- x \<sqinter> y) = - x"
    using 9 25 316 by metis
  have 321: "\<And>x y . - - (- x \<sqinter> y) \<sqinter> x = bot"
    using 41 316 by metis
  have 374: "\<And>x y . - x \<squnion> - (x \<sqinter> y) = - (x \<sqinter> y)"
    using 25 128 133 by metis
  have 388: "\<And>x y . - (x \<sqinter> y) \<sqinter> - x = - x"
    using 128 316 by metis
  have 389: "\<And>x y . - - (x \<sqinter> y) \<sqinter> - x = bot"
    using 128 321 by metis
  have 405: "\<And>x y z . - (x \<sqinter> y) \<sqinter> (- x \<sqinter> z) = - x \<sqinter> z"
    using 13 388 by metis
  have 406: "\<And>x y z . - (x \<sqinter> (y \<sqinter> z)) \<sqinter> - (x \<sqinter> y) = - (x \<sqinter> y)"
    using 13 388 by metis
  have 420: "\<And>x y . - x \<sqinter> - - (- x \<sqinter> y) = - - (- x \<sqinter> y)"
    using 316 388 by metis
  have 422: "\<And>x y z . - - (x \<sqinter> y) \<sqinter> (- x \<sqinter> z) = bot"
    using 13 18 389 by metis
  have 758: "\<And>x y z . x \<squnion> (x \<sqinter> (- y \<sqinter> - z)) = x"
    using 13 104 117 by metis
  have 1092: "\<And>x y . - (x \<squnion> y) \<sqinter> x = bot"
    using 9 30 31 66 by metis
  have 1130: "\<And>x y z . (- (x \<squnion> y) \<squnion> z) \<sqinter> x = z \<sqinter> x"
    using 17 30 1092 by metis
  have 1156: "\<And>x y . - - x \<sqinter> - (- x \<sqinter> y) = - - x"
    using 67 104 124 133 by metis
  have 2098: "\<And>x y . - - (x \<squnion> y) \<sqinter> x = x"
    using 14 19 1130 by metis
  have 2125: "\<And>x y . - - (x \<squnion> y) \<sqinter> y = y"
    using 9 2098 by metis
  have 2138: "\<And>x y . - x \<squnion> - - (x \<squnion> y) = top"
    using 9 289 2098 by metis
  have 2139: "\<And>x y . - x \<sqinter> - (x \<squnion> y) = - (x \<squnion> y)"
    using 316 2098 by metis
  have 2192: "\<And>x y . - - x \<sqinter> (- y \<sqinter> x) = - y \<sqinter> x"
    using 89 2125 by metis
  have 2202: "\<And>x y . - x \<squnion> - - (y \<squnion> x) = top"
    using 9 289 2125 by metis
  have 2344: "\<And>x y . - (- x \<sqinter> y) \<squnion> - - y = top"
    using 89 2202 by metis
  have 2547: "\<And>x y z . - x \<squnion> ((- - x \<sqinter> - y) \<squnion> z) = - x \<squnion> (- y \<squnion> z)"
    using 112 117 by metis
  have 3023: "\<And>x y . - x \<squnion> - (- y \<sqinter> - x) = top"
    using 9 133 2344 by metis
  have 3134: "\<And>x y . - (- x \<sqinter> - y) \<sqinter> y = y"
    using 14 43 3023 by metis
  have 3135: "\<And>x y . - x \<sqinter> (- y \<sqinter> - x) = - y \<sqinter> - x"
    using 14 44 3023 by metis
  have 3962: "\<And>x y . - - (x \<squnion> y) \<sqinter> - - x = - - x"
    using 14 137 2138 by metis
  have 5496: "\<And>x y z . - - (x \<sqinter> y) \<sqinter> - (x \<squnion> z) = bot"
    using 422 2139 by metis
  have 9414: "\<And>x y . - - (- x \<sqinter> y) \<sqinter> y = - x \<sqinter> y"
    using 9 104 183 320 by metis
  have 9520: "\<And>x y z . - - (- x \<sqinter> y) \<sqinter> - - (x \<sqinter> z) = bot"
    using 374 5496 by metis
  have 11070: "\<And>x y z . - (- - x \<sqinter> y) \<squnion> (- x \<sqinter> - z) = - (- - x \<sqinter> y)"
    using 317 758 by metis
  have 12371: "\<And>x y . - x \<sqinter> - (- - x \<sqinter> y) = - x"
    using 133 1156 by metis
  have 12377: "\<And>x y . - x \<sqinter> - (x \<sqinter> y) = - x"
    using 128 133 1156 by metis
  have 12384: "\<And>x y . - (x \<squnion> y) \<sqinter> - y = - (x \<squnion> y)"
    using 133 1156 2125 by metis
  have 12394: "\<And>x y . - - (- x \<sqinter> - y) = - x \<sqinter> - y"
    using 1156 3134 9414 by metis
  have 12640: "\<And>x y . - x \<sqinter> - (- y \<sqinter> x) = - x"
    using 89 12384 by metis
  have 24648: "\<And>x y . (- x \<sqinter> - y) \<squnion> - (- x \<sqinter> - y) = top"
    using 19 12394 by metis
  have 28270: "\<And>x y z . - - (x \<sqinter> y) \<squnion> - (- x \<sqinter> z) = - (- x \<sqinter> z)"
    using 374 405 by metis
  have 28339: "\<And>x y . - (- - (x \<sqinter> y) \<sqinter> x) = - (x \<sqinter> y)"
    using 124 406 12371 by metis
  have 28423: "\<And>x y . - (- x \<sqinter> - y) = - (- y \<sqinter> - x)"
    using 13 3135 12394 28339 by metis
  have 28487: "\<And>x y . - x \<sqinter> - y = - y \<sqinter> - x"
    using 2098 3962 12394 28423 by metis
  have 52423: "\<And>x y . - (- x \<sqinter> - (- x \<sqinter> y)) \<sqinter> y = y"
    using 14 145 24648 28487 by metis
  have 52522: "\<And>x y . - x \<sqinter> - (- x \<sqinter> y) = - x \<sqinter> - y"
    using 13 12377 12394 12640 28487 52423 by metis
  have 61103: "\<And>x y z . - (- - x \<sqinter> y) \<squnion> z = - x \<squnion> (- y \<squnion> z)"
    using 112 2547 12371 52522 by metis
  have 61158: "\<And>x y . - - (- x \<sqinter> y) = - x \<sqinter> - - y"
    using 420 52522 by metis
  have 61231: "\<And>x y z . - x \<sqinter> (- - y \<sqinter> - (x \<sqinter> z)) = - x \<sqinter> - - y"
    using 13 15 50 133 9520 52522 61158 by metis
  have 61313: "\<And>x y . - x \<squnion> - y = - (- - y \<sqinter> x)"
    using 120 11070 61103 by metis
  have 61393: "\<And>x y . - (- x \<sqinter> - - y) = - (- x \<sqinter> y)"
    using 13 28270 61158 61231 61313 by metis
  have 61422: "\<And>x y . - (- - x \<sqinter> y) = - (- - y \<sqinter> x)"
    using 13 135 2192 61158 61313 by metis
  show ?thesis
    using 61313 61393 61422 by metis
qed

lemma l12:
  "- x \<sqinter> - y = - (x \<squnion> y)"
proof -
  have 1: "\<And>x y . x \<le> y \<longleftrightarrow> x \<squnion> y = y"
    by (simp add: il_less_eq)
  have 4: "\<And>x y . \<not>(x \<le> y) \<or> x \<squnion> y = y"
    using 1 by metis
  have 5: "\<And>x y z . (x \<sqinter> y) \<squnion> (x \<sqinter> z) \<le> x \<sqinter> (y \<squnion> z)"
    by (simp add: il_sub_inf_right_isotone_var)
  have 6: "\<And>x y . - - x \<le> - (- x \<sqinter> y)"
    by (simp add: pad2)
  have 7: "\<And>x y z . x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
    by (simp add: il_associative)
  have 8: "\<And>x y z . (x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
    using 7 by metis
  have 9: "\<And>x y . x \<squnion> y = y \<squnion> x"
    by (simp add: il_commutative)
  have 10: "\<And>x . x \<squnion> bot = x"
    by (simp add: il_bot_unit)
  have 11: "\<And>x . x \<squnion> x = x"
    by simp
  have 12: "\<And>x y z . x \<sqinter> (y \<sqinter> z) = (x \<sqinter> y) \<sqinter> z"
    by (simp add: il_inf_associative)
  have 13: "\<And>x y z . (x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
    using 12 by metis
  have 14: "\<And>x . top \<sqinter> x = x"
    by simp
  have 15: "\<And>x . x \<sqinter> top = x"
    by simp
  have 16: "\<And>x y z . (x \<squnion> y) \<sqinter> z = (x \<sqinter> z) \<squnion> (y \<sqinter> z)"
    by (simp add: il_inf_right_dist_sup)
  have 17: "\<And>x y z . (x \<sqinter> y) \<squnion> (z \<sqinter> y) = (x \<squnion> z) \<sqinter> y"
    using 16 by metis
  have 18: "\<And>x . bot \<sqinter> x = bot"
    by simp
  have 19: "\<And>x . - x \<squnion> - - x = top"
    by simp
  have 20: "\<And>x . - x \<sqinter> x = bot"
    by (simp add: a_inf_complement_bot)
  have 22: "\<And>x y z . ((x \<sqinter> y) \<squnion> (x \<sqinter> z)) \<squnion> (x \<sqinter> (y \<squnion> z)) = x \<sqinter> (y \<squnion> z)"
    using 4 5 by metis
  have 23: "\<And>x y z . (x \<sqinter> (y \<squnion> z)) \<squnion> ((x \<sqinter> y) \<squnion> (x \<sqinter> z)) = x \<sqinter> (y \<squnion> z)"
    using 9 22 by metis
  have 24: "\<And>x y . - - x \<squnion> - (- x \<sqinter> y) = - (- x \<sqinter> y)"
    using 4 6 by metis
  have 25: "\<And>x y z . x \<squnion> (y \<squnion> z) = y \<squnion> (x \<squnion> z)"
    using 8 9 by metis
  have 26: "\<And>x y z . (x \<sqinter> y) \<squnion> ((x \<sqinter> z) \<squnion> (x \<sqinter> (y \<squnion> z))) = x \<sqinter> (y \<squnion> z)"
    using 9 23 25 by metis
  have 29: "\<And>x . bot \<squnion> x = x"
    using 9 10 by metis
  have 30: "\<And>x y . x \<squnion> (x \<squnion> y) = x \<squnion> y"
    using 8 11 by metis
  have 32: "\<And>x y . x \<squnion> (y \<squnion> x) = y \<squnion> x"
    using 8 9 11 by metis
  have 33: "\<And>u x y z . ((x \<squnion> y) \<sqinter> z) \<squnion> u = (x \<sqinter> z) \<squnion> ((y \<sqinter> z) \<squnion> u)"
    using 8 17 by metis
  have 34: "\<And>u x y z . (x \<sqinter> (y \<sqinter> z)) \<squnion> (u \<sqinter> z) = ((x \<sqinter> y) \<squnion> u) \<sqinter> z"
    using 13 17 by metis
  have 35: "\<And>u x y z . (x \<sqinter> y) \<squnion> (z \<sqinter> (u \<sqinter> y)) = (x \<squnion> (z \<sqinter> u)) \<sqinter> y"
    using 13 17 by metis
  have 36: "\<And>x y . (top \<squnion> x) \<sqinter> y = y \<squnion> (x \<sqinter> y)"
    using 14 17 by metis
  have 37: "\<And>x y . (x \<squnion> top) \<sqinter> y = y \<squnion> (x \<sqinter> y)"
    using 9 14 17 by metis
  have 38: "\<And>x y . - x \<squnion> (- - x \<squnion> y) = top \<squnion> y"
    using 8 19 by metis
  have 40: "\<And>x y . - x \<sqinter> (x \<sqinter> y) = bot"
    using 13 18 20 by metis
  have 41: "- top = bot"
    using 15 20 by metis
  have 42: "\<And>x y . (- x \<squnion> y) \<sqinter> x = y \<sqinter> x"
    using 17 20 29 by metis
  have 43: "\<And>x y . (x \<squnion> - y) \<sqinter> y = x \<sqinter> y"
    using 9 17 20 29 by metis
  have 45: "\<And>x . - bot \<squnion> - - x = - bot"
    using 9 20 24 by metis
  have 46: "\<And>u x y z . (x \<sqinter> y) \<squnion> (z \<squnion> (u \<sqinter> y)) = z \<squnion> ((x \<squnion> u) \<sqinter> y)"
    using 17 25 by metis
  have 47: "\<And>x y . - x \<squnion> (y \<squnion> - - x) = y \<squnion> top"
    using 19 25 by metis
  have 49: "- bot = top"
    using 19 29 41 by metis
  have 50: "\<And>x . top \<squnion> - - x = top"
    using 45 49 by metis
  have 54: "\<And>u x y z . (x \<sqinter> y) \<squnion> ((x \<sqinter> z) \<squnion> ((x \<sqinter> (y \<squnion> z)) \<squnion> u)) = (x \<sqinter> (y \<squnion> z)) \<squnion> u"
    using 8 26 by metis
  have 58: "\<And>u x y z . (x \<sqinter> (y \<sqinter> z)) \<squnion> ((x \<sqinter> (y \<sqinter> u)) \<squnion> (x \<sqinter> (y \<sqinter> (z \<squnion> u)))) = x \<sqinter> (y \<sqinter> (z \<squnion> u))"
    using 13 26 by metis
  have 60: "\<And>x y . x \<squnion> ((x \<sqinter> y) \<squnion> (x \<sqinter> (y \<squnion> top))) = x \<sqinter> (y \<squnion> top)"
    using 15 25 26 by metis
  have 62: "\<And>x y . x \<squnion> ((x \<sqinter> - y) \<squnion> (x \<sqinter> - - y)) = x"
    using 9 15 19 25 26 by metis
  have 65: "\<And>x y . (- (x \<squnion> y) \<sqinter> x) \<squnion> (- (x \<squnion> y) \<sqinter> y) = bot"
    using 9 20 26 29 by metis
  have 66: "\<And>x y z . (x \<sqinter> - - y) \<squnion> (x \<sqinter> - (- y \<sqinter> z)) = x \<sqinter> - (- y \<sqinter> z)"
    using 11 24 26 by metis
  have 69: "\<And>x y . x \<squnion> (x \<sqinter> - - y) = x"
    using 9 15 26 30 50 by metis
  have 81: "\<And>x . top \<squnion> - x = top"
    using 9 19 30 by metis
  have 82: "\<And>x y z . (x \<sqinter> y) \<squnion> (x \<sqinter> (y \<squnion> z)) = x \<sqinter> (y \<squnion> z)"
    using 11 26 30 by metis
  have 83: "\<And>x y . x \<squnion> (x \<sqinter> (y \<squnion> top)) = x \<sqinter> (y \<squnion> top)"
    using 60 82 by metis
  have 88: "\<And>x y . x \<squnion> (- y \<sqinter> x) = x"
    using 14 17 81 by metis
  have 89: "\<And>x y . top \<squnion> (x \<squnion> - y) = x \<squnion> top"
    using 25 81 by metis
  have 91: "\<And>x y z . x \<squnion> (y \<squnion> (z \<squnion> x)) = y \<squnion> (z \<squnion> x)"
    using 8 32 by metis
  have 94: "\<And>x y z . x \<squnion> (y \<squnion> (- z \<sqinter> x)) = y \<squnion> x"
    using 25 88 by metis
  have 101: "\<And>x y z . x \<squnion> (y \<squnion> (x \<sqinter> - - z)) = y \<squnion> x"
    using 25 69 by metis
  have 102: "\<And>x . x \<squnion> (x \<sqinter> bot) = x"
    using 41 49 69 by metis
  have 103: "\<And>x y . x \<squnion> (x \<sqinter> - y) = x"
    using 9 62 101 by metis
  have 109: "\<And>x y . x \<squnion> (y \<squnion> (x \<sqinter> bot)) = y \<squnion> x"
    using 25 102 by metis
  have 111: "\<And>x y z . (- x \<sqinter> y) \<squnion> ((- - x \<sqinter> y) \<squnion> z) = y \<squnion> z"
    using 14 19 33 by metis
  have 116: "\<And>x y z . x \<squnion> ((x \<sqinter> - y) \<squnion> z) = x \<squnion> z"
    using 8 103 by metis
  have 119: "\<And>x y z . x \<squnion> (y \<squnion> (x \<sqinter> - z)) = y \<squnion> x"
    using 25 103 by metis
  have 123: "\<And>x . - - x \<sqinter> x = x"
    using 14 19 42 by metis
  have 127: "\<And>x y . - - x \<sqinter> (x \<sqinter> y) = x \<sqinter> y"
    using 13 123 by metis
  have 130: "\<And>x . - x \<squnion> - - - x = - x"
    using 9 24 123 by metis
  have 132: "\<And>x . - - - x = - x"
    using 9 103 123 130 by metis
  have 134: "\<And>x y . - x \<squnion> - (- - x \<sqinter> y) = - (- - x \<sqinter> y)"
    using 24 132 by metis
  have 136: "\<And>x y . (- x \<squnion> y) \<sqinter> - - x = y \<sqinter> - - x"
    using 42 132 by metis
  have 138: "\<And>x . - x \<sqinter> - x = - x"
    using 123 132 by metis
  have 144: "\<And>x y z . ((- (x \<sqinter> y) \<sqinter> x) \<squnion> z) \<sqinter> y = z \<sqinter> y"
    using 20 29 34 by metis
  have 157: "\<And>x y . (- x \<squnion> y) \<sqinter> - x = (top \<squnion> y) \<sqinter> - x"
    using 17 36 138 by metis
  have 182: "\<And>x y z . (x \<squnion> (- - (y \<sqinter> z) \<sqinter> y)) \<sqinter> z = (x \<squnion> y) \<sqinter> z"
    using 17 35 123 by metis
  have 288: "\<And>x y . - x \<squnion> - (- x \<sqinter> y) = top"
    using 24 38 81 by metis
  have 315: "\<And>x y . - (- x \<sqinter> y) \<sqinter> x = x"
    using 14 42 288 by metis
  have 316: "\<And>x y z . - (- x \<sqinter> y) \<sqinter> (x \<sqinter> z) = x \<sqinter> z"
    using 13 315 by metis
  have 319: "\<And>x y . - x \<squnion> - - (- x \<sqinter> y) = - x"
    using 9 24 315 by metis
  have 320: "\<And>x y . - - (- x \<sqinter> y) \<sqinter> x = bot"
    using 40 315 by metis
  have 373: "\<And>x y . - x \<squnion> - (x \<sqinter> y) = - (x \<sqinter> y)"
    using 24 127 132 by metis
  have 387: "\<And>x y . - (x \<sqinter> y) \<sqinter> - x = - x"
    using 127 315 by metis
  have 388: "\<And>x y . - - (x \<sqinter> y) \<sqinter> - x = bot"
    using 127 320 by metis
  have 404: "\<And>x y z . - (x \<sqinter> y) \<sqinter> (- x \<sqinter> z) = - x \<sqinter> z"
    using 13 387 by metis
  have 405: "\<And>x y z . - (x \<sqinter> (y \<sqinter> z)) \<sqinter> - (x \<sqinter> y) = - (x \<sqinter> y)"
    using 13 387 by metis
  have 419: "\<And>x y . - x \<sqinter> - - (- x \<sqinter> y) = - - (- x \<sqinter> y)"
    using 315 387 by metis
  have 420: "\<And>x y . - - x \<sqinter> - - (x \<sqinter> y) = - - (x \<sqinter> y)"
    using 387 by metis
  have 421: "\<And>x y z . - - (x \<sqinter> y) \<sqinter> (- x \<sqinter> z) = bot"
    using 13 18 388 by metis
  have 536: "\<And>x y . (x \<squnion> - - y) \<sqinter> y = (x \<squnion> top) \<sqinter> y"
    using 42 47 by metis
  have 662: "\<And>u x y z . (x \<sqinter> y) \<squnion> ((x \<sqinter> (z \<squnion> y)) \<squnion> u) = (x \<sqinter> (z \<squnion> y)) \<squnion> u"
    using 9 32 54 by metis
  have 705: "\<And>u x y z . (x \<sqinter> (y \<squnion> z)) \<squnion> ((x \<sqinter> (y \<squnion> (z \<sqinter> bot))) \<squnion> u) = (x \<sqinter> (y \<squnion> z)) \<squnion> u"
    using 25 54 109 662 by metis
  have 755: "\<And>x y z . (x \<sqinter> - y) \<squnion> (z \<squnion> x) = z \<squnion> x"
    using 32 91 116 by metis
  have 757: "\<And>x y z . x \<squnion> (x \<sqinter> (- y \<sqinter> - z)) = x"
    using 13 103 116 by metis
  have 930: "\<And>x y z . (- (x \<sqinter> (y \<squnion> z)) \<sqinter> (x \<sqinter> y)) \<squnion> (- (x \<sqinter> (y \<squnion> z)) \<sqinter> (x \<sqinter> z)) = bot"
    using 9 20 29 58 by metis
  have 1091: "\<And>x y . - (x \<squnion> y) \<sqinter> x = bot"
    using 9 29 30 65 by metis
  have 1092: "\<And>x y . - (x \<squnion> y) \<sqinter> y = bot"
    using 29 30 65 1091 by metis
  have 1113: "\<And>u x y z . - (x \<squnion> ((y \<squnion> z) \<sqinter> u)) \<sqinter> (x \<squnion> (z \<sqinter> u)) = bot"
    using 29 46 65 1091 by metis
  have 1117: "\<And>x y z . - (x \<squnion> y) \<sqinter> (x \<squnion> (- z \<sqinter> y)) = bot"
    using 29 65 94 1092 by metis
  have 1128: "\<And>x y z . - (x \<squnion> (y \<squnion> z)) \<sqinter> (x \<squnion> y) = bot"
    using 8 1091 by metis
  have 1129: "\<And>x y z . (- (x \<squnion> y) \<squnion> z) \<sqinter> x = z \<sqinter> x"
    using 17 29 1091 by metis
  have 1155: "\<And>x y . - - x \<sqinter> - (- x \<sqinter> y) = - - x"
    using 66 103 123 132 by metis
  have 1578: "\<And>x y z . - (x \<sqinter> (y \<squnion> z)) \<sqinter> (x \<sqinter> y) = bot"
    using 82 1091 by metis
  have 1594: "\<And>x y z . - (x \<sqinter> (y \<squnion> z)) \<sqinter> (x \<sqinter> z) = bot"
    using 29 930 1578 by metis
  have 2094: "\<And>x y z . - (x \<squnion> (y \<sqinter> (z \<squnion> top))) \<sqinter> (x \<squnion> y) = bot"
    using 83 1128 by metis
  have 2097: "\<And>x y . - - (x \<squnion> y) \<sqinter> x = x"
    using 14 19 1129 by metis
  have 2124: "\<And>x y . - - (x \<squnion> y) \<sqinter> y = y"
    using 9 2097 by metis
  have 2135: "\<And>x y . - - ((top \<squnion> x) \<sqinter> y) \<sqinter> y = y"
    using 36 2097 by metis
  have 2136: "\<And>x y . - - ((x \<squnion> top) \<sqinter> y) \<sqinter> y = y"
    using 37 2097 by metis
  have 2137: "\<And>x y . - x \<squnion> - - (x \<squnion> y) = top"
    using 9 288 2097 by metis
  have 2138: "\<And>x y . - x \<sqinter> - (x \<squnion> y) = - (x \<squnion> y)"
    using 315 2097 by metis
  have 2151: "\<And>x y . - x \<squnion> - (x \<squnion> y) = - x"
    using 9 132 373 2097 by metis
  have 2191: "\<And>x y . - - x \<sqinter> (- y \<sqinter> x) = - y \<sqinter> x"
    using 88 2124 by metis
  have 2201: "\<And>x y . - x \<squnion> - - (y \<squnion> x) = top"
    using 9 288 2124 by metis
  have 2202: "\<And>x y . - x \<sqinter> - (y \<squnion> x) = - (y \<squnion> x)"
    using 315 2124 by metis
  have 2320: "\<And>x y . - (x \<sqinter> (y \<squnion> top)) = - x"
    using 83 373 2151 by metis
  have 2343: "\<And>x y . - (- x \<sqinter> y) \<squnion> - - y = top"
    using 88 2201 by metis
  have 2546: "\<And>x y z . - x \<squnion> ((- - x \<sqinter> - y) \<squnion> z) = - x \<squnion> (- y \<squnion> z)"
    using 111 116 by metis
  have 2706: "\<And>x y z . - x \<squnion> (y \<squnion> - - ((top \<squnion> z) \<sqinter> - x)) = y \<squnion> - - ((top \<squnion> z) \<sqinter> - x)"
    using 755 2135 by metis
  have 2810: "\<And>x y . - x \<sqinter> - ((y \<squnion> top) \<sqinter> x) = - ((y \<squnion> top) \<sqinter> x)"
    using 315 2136 by metis
  have 3022: "\<And>x y . - x \<squnion> - (- y \<sqinter> - x) = top"
    using 9 132 2343 by metis
  have 3133: "\<And>x y . - (- x \<sqinter> - y) \<sqinter> y = y"
    using 14 42 3022 by metis
  have 3134: "\<And>x y . - x \<sqinter> (- y \<sqinter> - x) = - y \<sqinter> - x"
    using 14 43 3022 by metis
  have 3961: "\<And>x y . - - (x \<squnion> y) \<sqinter> - - x = - - x"
    using 14 136 2137 by metis
  have 4644: "\<And>x y z . - (x \<sqinter> - y) \<sqinter> (x \<sqinter> - (y \<squnion> z)) = bot"
    using 1594 2151 by metis
  have 5495: "\<And>x y z . - - (x \<sqinter> y) \<sqinter> - (x \<squnion> z) = bot"
    using 421 2138 by metis
  have 9413: "\<And>x y . - - (- x \<sqinter> y) \<sqinter> y = - x \<sqinter> y"
    using 9 103 182 319 by metis
  have 9519: "\<And>x y z . - - (- x \<sqinter> y) \<sqinter> - - (x \<sqinter> z) = bot"
    using 373 5495 by metis
  have 11069: "\<And>x y z . - (- - x \<sqinter> y) \<squnion> (- x \<sqinter> - z) = - (- - x \<sqinter> y)"
    using 316 757 by metis
  have 12370: "\<And>x y . - x \<sqinter> - (- - x \<sqinter> y) = - x"
    using 132 1155 by metis
  have 12376: "\<And>x y . - x \<sqinter> - (x \<sqinter> y) = - x"
    using 127 132 1155 by metis
  have 12383: "\<And>x y . - (x \<squnion> y) \<sqinter> - y = - (x \<squnion> y)"
    using 132 1155 2124 by metis
  have 12393: "\<And>x y . - - (- x \<sqinter> - y) = - x \<sqinter> - y"
    using 1155 3133 9413 by metis
  have 12407: "\<And>x y . - - x \<sqinter> - - (x \<squnion> y) = - - x"
    using 1155 2138 by metis
  have 12639: "\<And>x y . - x \<sqinter> - (- y \<sqinter> x) = - x"
    using 88 12383 by metis
  have 24647: "\<And>x y . (- x \<sqinter> - y) \<squnion> - (- x \<sqinter> - y) = top"
    using 19 12393 by metis
  have 28269: "\<And>x y z . - - (x \<sqinter> y) \<squnion> - (- x \<sqinter> z) = - (- x \<sqinter> z)"
    using 373 404 by metis
  have 28338: "\<And>x y . - (- - (x \<sqinter> y) \<sqinter> x) = - (x \<sqinter> y)"
    using 123 405 12370 by metis
  have 28422: "\<And>x y . - (- x \<sqinter> - y) = - (- y \<sqinter> - x)"
    using 13 3134 12393 28338 by metis
  have 28485: "\<And>x y . - x \<sqinter> - y = - y \<sqinter> - x"
    using 2097 3961 12393 28422 by metis
  have 30411: "\<And>x y . - x \<sqinter> (x \<squnion> (x \<sqinter> y)) = bot"
    using 9 82 2094 2320 by metis
  have 30469: "\<And>x . - x \<sqinter> (x \<squnion> - - x) = bot"
    using 9 123 132 30411 by metis
  have 37513: "\<And>x y . - (- x \<sqinter> - y) \<sqinter> - (y \<squnion> x) = bot"
    using 2202 4644 by metis
  have 52421: "\<And>x y . - (- x \<sqinter> - (- x \<sqinter> y)) \<sqinter> y = y"
    using 14 144 24647 28485 by metis
  have 52520: "\<And>x y . - x \<sqinter> - (- x \<sqinter> y) = - x \<sqinter> - y"
    using 13 12376 12393 12639 28485 52421 by metis
  have 52533: "\<And>x y z . - - (x \<squnion> (y \<sqinter> (z \<squnion> top))) \<sqinter> (x \<squnion> y) = x \<squnion> y"
    using 15 49 2094 52421 by metis
  have 61101: "\<And>x y z . - (- - x \<sqinter> y) \<squnion> z = - x \<squnion> (- y \<squnion> z)"
    using 111 2546 12370 52520 by metis
  have 61156: "\<And>x y . - - (- x \<sqinter> y) = - x \<sqinter> - - y"
    using 419 52520 by metis
  have 61162: "\<And>x y . - (x \<squnion> (x \<sqinter> y)) = - x"
    using 15 49 2138 30411 52520 by metis
  have 61163: "\<And>x . - (x \<squnion> - - x) = - x"
    using 15 49 2138 30469 52520 by metis
  have 61229: "\<And>x y z . - x \<sqinter> (- - y \<sqinter> - (x \<sqinter> z)) = - x \<sqinter> - - y"
    using 13 15 49 132 9519 52520 61156 by metis
  have 61311: "\<And>x y . - x \<squnion> - y = - (- - y \<sqinter> x)"
    using 119 11069 61101 by metis
  have 61391: "\<And>x y . - (- x \<sqinter> - - y) = - (- x \<sqinter> y)"
    using 13 28269 61156 61229 61311 by metis
  have 61420: "\<And>x y . - (- - x \<sqinter> y) = - (- - y \<sqinter> x)"
    using 13 134 2191 61156 61311 by metis
  have 61454: "\<And>x y . - (x \<squnion> - (- y \<sqinter> - x)) = - y \<sqinter> - x"
    using 9 132 3133 61156 61162 by metis
  have 61648: "\<And>x y . - x \<sqinter> (x \<squnion> (- y \<sqinter> - - x)) = bot"
    using 1117 61163 by metis
  have 62434: "\<And>x y . - (- - x \<sqinter> y) \<sqinter> x = - y \<sqinter> x"
    using 43 61311 by metis
  have 63947: "\<And>x y . - (- x \<sqinter> y) \<sqinter> - (- y \<squnion> x) = bot"
    using 37513 61391 by metis
  have 64227: "\<And>x y . - (x \<squnion> (- y \<sqinter> - - x)) = - x"
    using 15 49 2138 52520 61648 by metis
  have 64239: "\<And>x y . - (x \<squnion> (- - x \<squnion> y)) = - (x \<squnion> y)"
    using 9 25 12407 64227 by metis
  have 64241: "\<And>x y . - (x \<squnion> (- - x \<sqinter> - y)) = - x"
    using 28485 64227 by metis
  have 64260: "\<And>x y . - (x \<squnion> - - (x \<sqinter> y)) = - x"
    using 420 64241 by metis
  have 64271: "\<And>x y . - (- x \<squnion> (y \<squnion> - - (y \<sqinter> x))) = - (- x \<squnion> y)"
    using 9 25 42 64260 by metis
  have 64281: "\<And>x y . - (- x \<squnion> y) = - (y \<squnion> - - ((top \<squnion> y) \<sqinter> - x))"
    using 9 25 157 2706 64260 by metis
  have 64282: "\<And>x y . - (x \<squnion> - - ((x \<squnion> top) \<sqinter> y)) = - (x \<squnion> - - y)"
    using 9 25 132 536 2810 28485 61311 64260 by metis
  have 65110: "\<And>x y . - ((- x \<sqinter> y) \<squnion> (- y \<squnion> x)) = bot"
    using 9 14 49 37513 63947 by metis
  have 65231: "\<And>x y . - (x \<squnion> ((- x \<sqinter> y) \<squnion> - y)) = bot"
    using 9 25 65110 by metis
  have 65585: "\<And>x y . - (x \<squnion> - y) = - - y \<sqinter> - x"
    using 61311 61454 64239 by metis
  have 65615: "\<And>x y . - x \<sqinter> - ((x \<squnion> top) \<sqinter> y) = - y \<sqinter> - x"
    using 132 28485 64282 65585 by metis
  have 65616: "\<And>x y . - (- x \<squnion> y) = - y \<sqinter> - ((top \<squnion> y) \<sqinter> - x)"
    using 132 28485 64281 65585 by metis
  have 65791: "\<And>x y . - x \<sqinter> - ((top \<squnion> x) \<sqinter> - y) = - - y \<sqinter> - x"
    using 89 132 12376 28485 64271 65585 65615 65616 by metis
  have 65933: "\<And>x y . - (- x \<squnion> y) = - - x \<sqinter> - y"
    using 65616 65791 by metis
  have 66082: "\<And>x y z . - (x \<squnion> (y \<squnion> - z)) = - - z \<sqinter> - (x \<squnion> y)"
    using 8 65585 by metis
  have 66204: "\<And>x y . - - x \<sqinter> - (y \<squnion> (- y \<sqinter> x)) = bot"
    using 65231 66082 by metis
  have 66281: "\<And>x y z . - (x \<squnion> (- y \<squnion> z)) = - - y \<sqinter> - (x \<squnion> z)"
    using 25 65933 by metis
  have 67527: "\<And>x y . - - (x \<squnion> (- x \<sqinter> y)) \<sqinter> y = y"
    using 14 49 62434 66204 by metis
  have 67762: "\<And>x y . - (- - x \<sqinter> (y \<squnion> (- y \<sqinter> x))) = - x"
    using 61420 67527 by metis
  have 68018: "\<And>x y z . - (x \<squnion> y) \<sqinter> (x \<squnion> (y \<sqinter> (z \<squnion> top))) = bot"
    using 8 83 1113 2320 by metis
  have 71989: "\<And>x y z . - (x \<squnion> (y \<sqinter> (z \<squnion> top))) = - (x \<squnion> y)"
    using 9 29 52533 67762 68018 by metis
  have 71997: "\<And>x y z . - ((x \<sqinter> (y \<squnion> top)) \<squnion> z) = - (x \<squnion> z)"
    using 17 2320 71989 by metis
  have 72090: "\<And>x y z . - (x \<squnion> ((x \<sqinter> y) \<squnion> z)) = - (x \<squnion> z)"
    using 10 14 705 71997 by metis
  have 72139: "\<And>x y . - (x \<squnion> y) = - x \<sqinter> - y"
    using 25 123 132 2138 65933 66281 72090 by metis
  show ?thesis
    using 72139 by metis
qed

lemma l15:
  "--(x \<squnion> y) = --x \<squnion> --y"
  by (simp add: l11 l12 l4)

lemma l13_var:
  "- - (- x \<sqinter> y) = - x \<sqinter> - - y"
proof -
  have 1: "\<And>x y . x \<le> y \<longleftrightarrow> x \<squnion> y = y"
    by (simp add: il_less_eq)
  have 4: "\<And>x y . \<not>(x \<le> y) \<or> x \<squnion> y = y"
    using 1 by metis
  have 5: "\<And>x y z . (x \<sqinter> y) \<squnion> (x \<sqinter> z) \<le> x \<sqinter> (y \<squnion> z)"
    by (simp add: il_sub_inf_right_isotone_var)
  have 6: "\<And>x y . - - x \<le> - (- x \<sqinter> y)"
    by (simp add: pad2)
  have 7: "\<And>x y z . x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
    by (simp add: il_associative)
  have 8: "\<And>x y z . (x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
    using 7 by metis
  have 9: "\<And>x y . x \<squnion> y = y \<squnion> x"
    by (simp add: il_commutative)
  have 10: "\<And>x . x \<squnion> bot = x"
    by (simp add: il_bot_unit)
  have 11: "\<And>x . x \<squnion> x = x"
    by simp
  have 12: "\<And>x y z . x \<sqinter> (y \<sqinter> z) = (x \<sqinter> y) \<sqinter> z"
    by (simp add: il_inf_associative)
  have 13: "\<And>x y z . (x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
    using 12 by metis
  have 14: "\<And>x . top \<sqinter> x = x"
    by simp
  have 15: "\<And>x . x \<sqinter> top = x"
    by simp
  have 16: "\<And>x y z . (x \<squnion> y) \<sqinter> z = (x \<sqinter> z) \<squnion> (y \<sqinter> z)"
    by (simp add: il_inf_right_dist_sup)
  have 17: "\<And>x y z . (x \<sqinter> y) \<squnion> (z \<sqinter> y) = (x \<squnion> z) \<sqinter> y"
    using 16 by metis
  have 19: "\<And>x . - x \<squnion> - - x = top"
    by simp
  have 20: "\<And>x . - x \<sqinter> x = bot"
    by (simp add: a_inf_complement_bot)
  have 22: "\<And>x y z . ((x \<sqinter> y) \<squnion> (x \<sqinter> z)) \<squnion> (x \<sqinter> (y \<squnion> z)) = x \<sqinter> (y \<squnion> z)"
    using 4 5 by metis
  have 23: "\<And>x y z . (x \<sqinter> (y \<squnion> z)) \<squnion> ((x \<sqinter> y) \<squnion> (x \<sqinter> z)) = x \<sqinter> (y \<squnion> z)"
    using 9 22 by metis
  have 24: "\<And>x y . - - x \<squnion> - (- x \<sqinter> y) = - (- x \<sqinter> y)"
    using 4 6 by metis
  have 25: "\<And>x y z . x \<squnion> (y \<squnion> z) = y \<squnion> (x \<squnion> z)"
    using 8 9 by metis
  have 26: "\<And>x y z . (x \<sqinter> y) \<squnion> ((x \<sqinter> z) \<squnion> (x \<sqinter> (y \<squnion> z))) = x \<sqinter> (y \<squnion> z)"
    using 9 23 25 by metis
  have 29: "\<And>x . bot \<squnion> x = x"
    using 9 10 by metis
  have 30: "\<And>x y . x \<squnion> (x \<squnion> y) = x \<squnion> y"
    using 8 11 by metis
  have 34: "\<And>u x y z . (x \<sqinter> (y \<sqinter> z)) \<squnion> (u \<sqinter> z) = ((x \<sqinter> y) \<squnion> u) \<sqinter> z"
    using 13 17 by metis
  have 35: "\<And>u x y z . (x \<sqinter> y) \<squnion> (z \<sqinter> (u \<sqinter> y)) = (x \<squnion> (z \<sqinter> u)) \<sqinter> y"
    using 13 17 by metis
  have 38: "\<And>x y . - x \<squnion> (- - x \<squnion> y) = top \<squnion> y"
    using 8 19 by metis
  have 41: "- top = bot"
    using 15 20 by metis
  have 42: "\<And>x y . (- x \<squnion> y) \<sqinter> x = y \<sqinter> x"
    using 17 20 29 by metis
  have 43: "\<And>x y . (x \<squnion> - y) \<sqinter> y = x \<sqinter> y"
    using 9 17 20 29 by metis
  have 45: "\<And>x . - bot \<squnion> - - x = - bot"
    using 9 20 24 by metis
  have 49: "- bot = top"
    using 19 29 41 by metis
  have 50: "\<And>x . top \<squnion> - - x = top"
    using 45 49 by metis
  have 62: "\<And>x y . x \<squnion> ((x \<sqinter> - y) \<squnion> (x \<sqinter> - - y)) = x"
    using 9 15 19 25 26 by metis
  have 65: "\<And>x y . (- (x \<squnion> y) \<sqinter> x) \<squnion> (- (x \<squnion> y) \<sqinter> y) = bot"
    using 9 20 26 29 by metis
  have 66: "\<And>x y z . (x \<sqinter> - - y) \<squnion> (x \<sqinter> - (- y \<sqinter> z)) = x \<sqinter> - (- y \<sqinter> z)"
    using 11 24 26 by metis
  have 69: "\<And>x y . x \<squnion> (x \<sqinter> - - y) = x"
    using 9 15 26 30 50 by metis
  have 81: "\<And>x . top \<squnion> - x = top"
    using 9 19 30 by metis
  have 88: "\<And>x y . x \<squnion> (- y \<sqinter> x) = x"
    using 14 17 81 by metis
  have 101: "\<And>x y z . x \<squnion> (y \<squnion> (x \<sqinter> - - z)) = y \<squnion> x"
    using 25 69 by metis
  have 103: "\<And>x y . x \<squnion> (x \<sqinter> - y) = x"
    using 9 62 101 by metis
  have 123: "\<And>x . - - x \<sqinter> x = x"
    using 14 19 42 by metis
  have 127: "\<And>x y . - - x \<sqinter> (x \<sqinter> y) = x \<sqinter> y"
    using 13 123 by metis
  have 130: "\<And>x . - x \<squnion> - - - x = - x"
    using 9 24 123 by metis
  have 132: "\<And>x . - - - x = - x"
    using 9 103 123 130 by metis
  have 136: "\<And>x y . (- x \<squnion> y) \<sqinter> - - x = y \<sqinter> - - x"
    using 42 132 by metis
  have 144: "\<And>x y z . ((- (x \<sqinter> y) \<sqinter> x) \<squnion> z) \<sqinter> y = z \<sqinter> y"
    using 20 29 34 by metis
  have 182: "\<And>x y z . (x \<squnion> (- - (y \<sqinter> z) \<sqinter> y)) \<sqinter> z = (x \<squnion> y) \<sqinter> z"
    using 17 35 123 by metis
  have 288: "\<And>x y . - x \<squnion> - (- x \<sqinter> y) = top"
    using 24 38 81 by metis
  have 315: "\<And>x y . - (- x \<sqinter> y) \<sqinter> x = x"
    using 14 42 288 by metis
  have 319: "\<And>x y . - x \<squnion> - - (- x \<sqinter> y) = - x"
    using 9 24 315 by metis
  have 387: "\<And>x y . - (x \<sqinter> y) \<sqinter> - x = - x"
    using 127 315 by metis
  have 405: "\<And>x y z . - (x \<sqinter> (y \<sqinter> z)) \<sqinter> - (x \<sqinter> y) = - (x \<sqinter> y)"
    using 13 387 by metis
  have 419: "\<And>x y . - x \<sqinter> - - (- x \<sqinter> y) = - - (- x \<sqinter> y)"
    using 315 387 by metis
  have 1091: "\<And>x y . - (x \<squnion> y) \<sqinter> x = bot"
    using 9 29 30 65 by metis
  have 1129: "\<And>x y z . (- (x \<squnion> y) \<squnion> z) \<sqinter> x = z \<sqinter> x"
    using 17 29 1091 by metis
  have 1155: "\<And>x y . - - x \<sqinter> - (- x \<sqinter> y) = - - x"
    using 66 103 123 132 by metis
  have 2097: "\<And>x y . - - (x \<squnion> y) \<sqinter> x = x"
    using 14 19 1129 by metis
  have 2124: "\<And>x y . - - (x \<squnion> y) \<sqinter> y = y"
    using 9 2097 by metis
  have 2137: "\<And>x y . - x \<squnion> - - (x \<squnion> y) = top"
    using 9 288 2097 by metis
  have 2201: "\<And>x y . - x \<squnion> - - (y \<squnion> x) = top"
    using 9 288 2124 by metis
  have 2343: "\<And>x y . - (- x \<sqinter> y) \<squnion> - - y = top"
    using 88 2201 by metis
  have 3022: "\<And>x y . - x \<squnion> - (- y \<sqinter> - x) = top"
    using 9 132 2343 by metis
  have 3133: "\<And>x y . - (- x \<sqinter> - y) \<sqinter> y = y"
    using 14 42 3022 by metis
  have 3134: "\<And>x y . - x \<sqinter> (- y \<sqinter> - x) = - y \<sqinter> - x"
    using 14 43 3022 by metis
  have 3961: "\<And>x y . - - (x \<squnion> y) \<sqinter> - - x = - - x"
    using 14 136 2137 by metis
  have 9413: "\<And>x y . - - (- x \<sqinter> y) \<sqinter> y = - x \<sqinter> y"
    using 9 103 182 319 by metis
  have 12370: "\<And>x y . - x \<sqinter> - (- - x \<sqinter> y) = - x"
    using 132 1155 by metis
  have 12376: "\<And>x y . - x \<sqinter> - (x \<sqinter> y) = - x"
    using 127 132 1155 by metis
  have 12383: "\<And>x y . - (x \<squnion> y) \<sqinter> - y = - (x \<squnion> y)"
    using 132 1155 2124 by metis
  have 12393: "\<And>x y . - - (- x \<sqinter> - y) = - x \<sqinter> - y"
    using 1155 3133 9413 by metis
  have 12639: "\<And>x y . - x \<sqinter> - (- y \<sqinter> x) = - x"
    using 88 12383 by metis
  have 24647: "\<And>x y . (- x \<sqinter> - y) \<squnion> - (- x \<sqinter> - y) = top"
    using 19 12393 by metis
  have 28338: "\<And>x y . - (- - (x \<sqinter> y) \<sqinter> x) = - (x \<sqinter> y)"
    using 123 405 12370 by metis
  have 28422: "\<And>x y . - (- x \<sqinter> - y) = - (- y \<sqinter> - x)"
    using 13 3134 12393 28338 by metis
  have 28485: "\<And>x y . - x \<sqinter> - y = - y \<sqinter> - x"
    using 2097 3961 12393 28422 by metis
  have 52421: "\<And>x y . - (- x \<sqinter> - (- x \<sqinter> y)) \<sqinter> y = y"
    using 14 144 24647 28485 by metis
  have 52520: "\<And>x y . - x \<sqinter> - (- x \<sqinter> y) = - x \<sqinter> - y"
    using 13 12376 12393 12639 28485 52421 by metis
  have 61156: "\<And>x y . - - (- x \<sqinter> y) = - x \<sqinter> - - y"
    using 419 52520 by metis
  show ?thesis
    using 61156 by metis
qed

text \<open>Theorem 25.1\<close>

subclass subset_boolean_algebra_2
proof
  show "\<And>x y z. x \<squnion> (y \<squnion> z) = x \<squnion> y \<squnion> z"
    by (simp add: il_associative)
  show "\<And>x y. x \<squnion> y = y \<squnion> x"
    by (simp add: il_commutative)
  show "\<And>x. x \<squnion> x = x"
    by simp
  show "\<And>x y. x \<squnion> - (y \<squnion> - y) = x"
    using il_bot_unit l12 l6 by auto
  show "\<And>x y. - (x \<squnion> y) = - (- - x \<squnion> - - y)"
    by (metis l15 l4)
  show "\<And>x y. - x \<squnion> - (- x \<squnion> y) = - x \<squnion> - y"
    by (smt l11 l15 il_inf_right_dist_sup il_unit_bot l6 l7)
qed

lemma aa_test:
  "p = --p \<Longrightarrow> test p"
  by (metis ppa_ppd.d_closed)

lemma test_aa_increasing:
  "test p \<Longrightarrow> p \<le> --p"
  by (simp add: ppa_ppd.d_increasing_sub_identity test_sub_identity)

lemma "test p \<Longrightarrow> - - (p \<sqinter> x) \<le> p" nitpick [expect=genuine] oops
lemma "test p \<Longrightarrow> --p \<le> p" nitpick [expect=genuine] oops

end

class pa_algebra = pa_semiring + minus +
  assumes pa_minus_def: "-x - -y = -(--x \<squnion> -y)"
begin

subclass subset_boolean_algebra_2_extended
proof
  show "bot = (THE x. \<forall>z. x = - (z \<squnion> - z))"
    using l12 l6 by auto
  thus "top = - (THE x. \<forall>z. x = - (z \<squnion> - z))"
    using l2 by blast
  show "\<And>x y. - x \<sqinter> - y = - (- - x \<squnion> - - y)"
    by (metis l12 l4)
  show "\<And>x y. - x - - y = - (- - x \<squnion> - y)"
    by (simp add: pa_minus_def)
  show "\<And>x y. (x \<le> y) = (x \<squnion> y = y)"
    by (simp add: il_less_eq)
  show "\<And>x y. (x < y) = (x \<squnion> y = y \<and> y \<squnion> x \<noteq> x)"
    by (simp add: il_less_eq less_le_not_le)
qed

lemma "\<And>x y. - (x \<sqinter> - - y) = - (x \<sqinter> y)" nitpick [expect=genuine] oops

end

subsection \<open>Antidomain Semirings\<close>

text \<open>Definition 24\<close>

class a_semiring = ppa_semiring +
  assumes ad3: "-(x \<sqinter> y) \<le> -(x \<sqinter> --y)"
begin

lemma l16:
  "- - x \<le> - (- x \<sqinter> y)"
proof -
  have 1: "\<And>x y . x \<le> y \<longleftrightarrow> x \<squnion> y = y"
    by (simp add: il_less_eq)
  have 3: "\<And>x y z . x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
    by (simp add: il_associative)
  have 4: "\<And>x y z . (x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
    using 3 by metis
  have 5: "\<And>x y . x \<squnion> y = y \<squnion> x"
    by (simp add: il_commutative)
  have 6: "\<And>x . x \<squnion> bot = x"
    by (simp add: il_bot_unit)
  have 7: "\<And>x . x \<squnion> x = x"
    by simp
  have 8: "\<And>x y . \<not>(x \<le> y) \<or> x \<squnion> y = y"
    using 1 by metis
  have 9: "\<And>x y . x \<le> y \<or> x \<squnion> y \<noteq> y"
    using 1 by metis
  have 10: "\<And>x y z . x \<sqinter> (y \<sqinter> z) = (x \<sqinter> y) \<sqinter> z"
    by (simp add: il_inf_associative)
  have 11: "\<And>x y z . (x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
    using 10 by metis
  have 12: "\<And>x . top \<sqinter> x = x"
    by simp
  have 13: "\<And>x . x \<sqinter> top = x"
    by simp
  have 14: "\<And>x y z . (x \<sqinter> y) \<squnion> (x \<sqinter> z) \<le> x \<sqinter> (y \<squnion> z)"
    by (simp add: il_sub_inf_right_isotone_var)
  have 15: "\<And>x y z . (x \<squnion> y) \<sqinter> z = (x \<sqinter> z) \<squnion> (y \<sqinter> z)"
    by (simp add: il_inf_right_dist_sup)
  have 16: "\<And>x y z . (x \<sqinter> y) \<squnion> (z \<sqinter> y) = (x \<squnion> z) \<sqinter> y"
    using 15 by metis
  have 17: "\<And>x . bot \<sqinter> x = bot"
    by simp
  have 18: "\<And>x . - x \<squnion> - - x = top"
    by simp
  have 19: "\<And>x . - x \<sqinter> x = bot"
    by (simp add: a_inf_complement_bot)
  have 20: "\<And>x y . - (x \<sqinter> y) \<le> - (x \<sqinter> - - y)"
    by (simp add: ad3)
  have 22: "\<And>x y z . x \<squnion> (y \<squnion> z) = y \<squnion> (x \<squnion> z)"
    using 4 5 by metis
  have 25: "\<And>x . bot \<squnion> x = x"
    using 5 6 by metis
  have 26: "\<And>x y . x \<squnion> (x \<squnion> y) = x \<squnion> y"
    using 4 7 by metis
  have 33: "\<And>x y z . (x \<sqinter> y) \<squnion> ((x \<sqinter> z) \<squnion> (x \<sqinter> (y \<squnion> z))) = x \<sqinter> (y \<squnion> z)"
    using 5 8 14 22 by metis
  have 47: "\<And>x y . - x \<squnion> (- - x \<squnion> y) = top \<squnion> y"
    using 4 18 by metis
  have 48: "\<And>x y . - - x \<squnion> (y \<squnion> - x) = y \<squnion> top"
    using 4 5 18 by metis
  have 51: "\<And>x y . - x \<sqinter> (x \<sqinter> y) = bot"
    using 11 17 19 by metis
  have 52: "- top = bot"
    using 13 19 by metis
  have 56: "\<And>x y . (- x \<squnion> y) \<sqinter> x = y \<sqinter> x"
    using 16 19 25 by metis
  have 57: "\<And>x y . (x \<squnion> - y) \<sqinter> y = x \<sqinter> y"
    using 5 16 19 25 by metis
  have 58: "\<And>x y . - (x \<sqinter> y) \<squnion> - (x \<sqinter> - - y) = - (x \<sqinter> - - y)"
    using 8 20 by metis
  have 60: "\<And>x . - x \<le> - - - x"
    using 12 20 by metis
  have 69: "- bot = top"
    using 18 25 52 by metis
  have 74: "\<And>x y . x \<le> x \<squnion> y"
    using 9 26 by metis
  have 78: "\<And>x . top \<squnion> - x = top"
    using 5 18 26 by metis
  have 80: "\<And>x y . x \<le> y \<squnion> x"
    using 5 74 by metis
  have 86: "\<And>x y z . x \<squnion> y \<le> x \<squnion> (z \<squnion> y)"
    using 22 80 by metis
  have 95: "\<And>x . - x \<squnion> - - - x = - - - x"
    using 8 60 by metis
  have 143: "\<And>x y . x \<squnion> (x \<sqinter> - y) = x"
    using 5 13 26 33 78 by metis
  have 370: "\<And>x y z . x \<squnion> (y \<sqinter> - z) \<le> x \<squnion> y"
    using 86 143 by metis
  have 907: "\<And>x . - x \<sqinter> - x = - x"
    using 12 18 57 by metis
  have 928: "\<And>x y . - x \<sqinter> (- x \<sqinter> y) = - x \<sqinter> y"
    using 11 907 by metis
  have 966: "\<And>x y . - (- x \<sqinter> - - (x \<sqinter> y)) = top"
    using 51 58 69 78 by metis
  have 1535: "\<And>x . - x \<squnion> - - - - x = top"
    using 47 78 95 by metis
  have 1630: "\<And>x y z . (x \<squnion> y) \<sqinter> - z \<le> (x \<sqinter> - z) \<squnion> y"
    using 16 370 by metis
  have 2422: "\<And>x . - x \<sqinter> - - - x = - - - x"
    using 12 57 1535 by metis
  have 6567: "\<And>x y . - x \<sqinter> - - (x \<sqinter> y) = bot"
    using 12 19 966 by metis
  have 18123: "\<And>x . - - - x = - x"
    using 95 143 2422 by metis
  have 26264: "\<And>x y . - x \<le> (- y \<sqinter> - x) \<squnion> - - y"
    using 12 18 1630 by metis
  have 26279: "\<And>x y . - - (x \<sqinter> y) \<le> - - x"
    using 25 6567 26264 by metis
  have 26307: "\<And>x y . - - (- x \<sqinter> y) \<le> - x"
    using 928 18123 26279 by metis
  have 26339: "\<And>x y . - x \<squnion> - - (- x \<sqinter> y) = - x"
    using 5 8 26307 by metis
  have 26564: "\<And>x y . - x \<squnion> - (- x \<sqinter> y) = top"
    using 5 48 78 18123 26339 by metis
  have 26682: "\<And>x y . - (- x \<sqinter> y) \<sqinter> x = x"
    using 12 56 26564 by metis
  have 26864: "\<And>x y . - - x \<le> - (- x \<sqinter> y)"
    using 18123 26279 26682 by metis
  show ?thesis
    using 26864 by metis
qed

text \<open>Theorem 25.2\<close>

subclass pa_semiring
proof
  show "\<And>x y. - - x \<le> - (- x \<sqinter> y)"
    by (rule l16)
qed

lemma l17:
  "-(x \<sqinter> y) = -(x \<sqinter> --y)"
  by (simp add: ad3 antisym l14)

lemma a_complement_inf_double_complement:
  "-(x \<sqinter> --y) = -(x \<sqinter> y)"
  using l17 by auto

sublocale a_d: d_semiring_var where d = "\<lambda>x . --x"
proof
  show "\<And>x y. - - (x \<sqinter> - - y) \<le> - - (x \<sqinter> y)"
    using l17 by auto
  show "- - bot = bot"
    by (simp add: l1 l2)
qed

lemma "test p \<Longrightarrow> - - (p \<sqinter> x) \<le> p"
  by (fact a_d.d2)

end

class a_algebra = a_semiring + minus +
  assumes a_minus_def: "-x - -y = -(--x \<squnion> -y)"
begin

subclass pa_algebra
proof
  show "\<And>x y. - x - - y = - (- - x \<squnion> - y)"
    by (simp add: a_minus_def)
qed

text \<open>Theorem 25.4\<close>

subclass subset_boolean_algebra_4_extended
proof
  show "\<And>x y z. x \<sqinter> (y \<sqinter> z) = x \<sqinter> y \<sqinter> z"
    by (simp add: il_inf_associative)
  show "\<And>x y z. (x \<squnion> y) \<sqinter> z = x \<sqinter> z \<squnion> y \<sqinter> z"
    by (simp add: il_inf_right_dist_sup)
  show "\<And>x. - x \<sqinter> x = bot"
    by (simp add: a_inf_complement_bot)
  show "\<And>x. top \<sqinter> x = x"
    by simp
  show "\<And>x y. - (x \<sqinter> - - y) = - (x \<sqinter> y)"
    using l17 by auto
  show "\<And>x. x \<sqinter> top = x"
    by simp
  show "\<And>x y z. x \<le> y \<Longrightarrow> z \<sqinter> x \<le> z \<sqinter> y"
    by (simp add: il_sub_inf_right_isotone)
qed

end

context subset_boolean_algebra_4_extended
begin

subclass il_semiring
proof
  show "\<And>x y z. x \<squnion> (y \<squnion> z) = x \<squnion> y \<squnion> z"
    by (simp add: sup_assoc)
  show "\<And>x y. x \<squnion> y = y \<squnion> x"
    by (simp add: sup_commute)
  show "\<And>x. x \<squnion> x = x"
    by simp
  show "\<And>x. x \<squnion> bot = x"
    by simp
  show "\<And>x y z. x \<sqinter> (y \<sqinter> z) = x \<sqinter> y \<sqinter> z"
    by (simp add: sba3_inf_associative)
  show "\<And>x y z. (x \<squnion> y) \<sqinter> z = x \<sqinter> z \<squnion> y \<sqinter> z"
    by (simp add: sba3_inf_right_dist_sup)
  show "\<And>x. top \<sqinter> x = x"
    by simp
  show "\<And>x. x \<sqinter> top = x"
    by simp
  show "\<And>x. bot \<sqinter> x = bot"
    by (simp add: inf_left_zero)
  show "\<And>x y z. x \<le> y \<Longrightarrow> z \<sqinter> x \<le> z \<sqinter> y"
    by (simp add: inf_right_isotone)
  show "\<And>x y. (x \<le> y) = (x \<squnion> y = y)"
    by (simp add: le_iff_sup)
  show "\<And>x y. (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_le_not_le)
qed

subclass a_semiring
proof
  show "\<And>x. - x \<sqinter> x = bot"
    by (simp add: sba3_inf_complement_bot)
  show "\<And>x. - x \<squnion> - - x = top"
    by simp
  show "\<And>x y. - (x \<sqinter> y) \<le> - (x \<sqinter> - - y)"
    by (simp add: sba3_complement_inf_double_complement)
qed

sublocale sba4_a: a_algebra
proof
  show "\<And>x y. - x - - y = - (- - x \<squnion> - y)"
    by (simp add: sub_minus_def)
qed

end

context stone_algebra
begin

text \<open>Theorem 25.3\<close>

subclass il_semiring
proof
  show "\<And>x y z. x \<squnion> (y \<squnion> z) = x \<squnion> y \<squnion> z"
    by (simp add: sup_assoc)
  show "\<And>x y. x \<squnion> y = y \<squnion> x"
    by (simp add: sup_commute)
  show "\<And>x. x \<squnion> x = x"
    by simp
  show "\<And>x. x \<squnion> bot = x"
    by simp
  show "\<And>x y z. x \<sqinter> (y \<sqinter> z) = x \<sqinter> y \<sqinter> z"
    by (simp add: inf.sup_monoid.add_assoc)
  show "\<And>x y z. (x \<squnion> y) \<sqinter> z = x \<sqinter> z \<squnion> y \<sqinter> z"
    by (simp add: inf_sup_distrib2)
  show "\<And>x. top \<sqinter> x = x"
    by simp
  show "\<And>x. x \<sqinter> top = x"
    by simp
  show "\<And>x. bot \<sqinter> x = bot"
    by simp
  show "\<And>x y z. x \<le> y \<Longrightarrow> z \<sqinter> x \<le> z \<sqinter> y"
    using inf.sup_right_isotone by blast
  show "\<And>x y. (x \<le> y) = (x \<squnion> y = y)"
    by (simp add: le_iff_sup)
  show "\<And>x y. (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_le_not_le)
qed

subclass a_semiring
proof
  show "\<And>x. - x \<sqinter> x = bot"
    by simp
  show "\<And>x. - x \<squnion> - - x = top"
    by simp
  show "\<And>x y. - (x \<sqinter> y) \<le> - (x \<sqinter> - - y)"
    by simp
qed

end

end

