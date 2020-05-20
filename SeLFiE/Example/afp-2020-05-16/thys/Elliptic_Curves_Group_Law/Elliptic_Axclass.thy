section \<open>Formalization using Axiomatic Type Classes\<close>

theory Elliptic_Axclass
imports "HOL-Decision_Procs.Reflective_Field"
begin

subsection \<open>Affine Coordinates\<close>

datatype 'a point = Infinity | Point 'a 'a

class ell_field = field +
  assumes two_not_zero: "2 \<noteq> 0"
begin

definition nonsingular :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "nonsingular a b = (4 * a ^ 3 + 27 * b ^ 2 \<noteq> 0)"

definition on_curve :: "'a \<Rightarrow> 'a \<Rightarrow> 'a point \<Rightarrow> bool" where
  "on_curve a b p = (case p of
       Infinity \<Rightarrow> True
     | Point x y \<Rightarrow> y ^ 2 = x ^ 3 + a * x + b)"

definition add :: "'a \<Rightarrow> 'a point \<Rightarrow> 'a point \<Rightarrow> 'a point" where
  "add a p\<^sub>1 p\<^sub>2 = (case p\<^sub>1 of
       Infinity \<Rightarrow> p\<^sub>2
     | Point x\<^sub>1 y\<^sub>1 \<Rightarrow> (case p\<^sub>2 of
         Infinity \<Rightarrow> p\<^sub>1
       | Point x\<^sub>2 y\<^sub>2 \<Rightarrow>
           if x\<^sub>1 = x\<^sub>2 then
             if y\<^sub>1 = - y\<^sub>2 then Infinity
             else
               let
                 l = (3 * x\<^sub>1 ^ 2 + a) / (2 * y\<^sub>1);
                 x\<^sub>3 = l ^ 2 - 2 * x\<^sub>1
               in
                 Point x\<^sub>3 (- y\<^sub>1 - l * (x\<^sub>3 - x\<^sub>1))
           else
             let
               l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1);
               x\<^sub>3 = l ^ 2 - x\<^sub>1 - x\<^sub>2
             in
               Point x\<^sub>3 (- y\<^sub>1 - l * (x\<^sub>3 - x\<^sub>1))))"

definition opp :: "'a point \<Rightarrow> 'a point" where
  "opp p = (case p of
       Infinity \<Rightarrow> Infinity
     | Point x y \<Rightarrow> Point x (- y))"

end

lemma on_curve_infinity [simp]: "on_curve a b Infinity"
  by (simp add: on_curve_def)

lemma opp_Infinity [simp]: "opp Infinity = Infinity"
  by (simp add: opp_def)

lemma opp_Point: "opp (Point x y) = Point x (- y)"
  by (simp add: opp_def)

lemma opp_opp: "opp (opp p) = p"
  by (simp add: opp_def split: point.split)

lemma opp_closed:
  "on_curve a b p \<Longrightarrow> on_curve a b (opp p)"
  by (auto simp add: on_curve_def opp_def power2_eq_square
    split: point.split)

lemma curve_elt_opp:
  assumes "p\<^sub>1 = Point x\<^sub>1 y\<^sub>1"
  and "p\<^sub>2 = Point x\<^sub>2 y\<^sub>2"
  and "on_curve a b p\<^sub>1"
  and "on_curve a b p\<^sub>2"
  and "x\<^sub>1 = x\<^sub>2"
  shows "p\<^sub>1 = p\<^sub>2 \<or> p\<^sub>1 = opp p\<^sub>2"
proof -
  from \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close> \<open>on_curve a b p\<^sub>1\<close>
  have "y\<^sub>1 ^ 2 = x\<^sub>1 ^ 3 + a * x\<^sub>1 + b"
    by (simp_all add: on_curve_def)
  moreover from \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close> \<open>on_curve a b p\<^sub>2\<close> \<open>x\<^sub>1 = x\<^sub>2\<close>
  have "x\<^sub>1 ^ 3 + a * x\<^sub>1 + b = y\<^sub>2 ^ 2"
    by (simp_all add: on_curve_def)
  ultimately have "y\<^sub>1 = y\<^sub>2 \<or> y\<^sub>1 = - y\<^sub>2"
    by (simp add: square_eq_iff power2_eq_square)
  with \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close> \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close> \<open>x\<^sub>1 = x\<^sub>2\<close> show ?thesis
    by (auto simp add: opp_def)
qed

lemma add_closed:
  assumes "on_curve a b p\<^sub>1" and "on_curve a b p\<^sub>2"
  shows "on_curve a b (add a p\<^sub>1 p\<^sub>2)"
proof (cases p\<^sub>1)
  case (Point x\<^sub>1 y\<^sub>1)
  note Point' = this
  show ?thesis
  proof (cases p\<^sub>2)
    case (Point x\<^sub>2 y\<^sub>2)
    show ?thesis
    proof (cases "x\<^sub>1 = x\<^sub>2")
      case True
      note True' = this
      show ?thesis
      proof (cases "y\<^sub>1 = - y\<^sub>2")
        case True
        with True' Point Point'
        show ?thesis
          by (simp add: on_curve_def add_def)
      next
        case False
        note on_curve1 = \<open>on_curve a b p\<^sub>1\<close> [simplified Point' on_curve_def True', simplified]
        from False True' Point Point' assms
        have "y\<^sub>1 \<noteq> 0" by (auto simp add: on_curve_def)
        with False True' Point Point' assms
        show ?thesis
          apply (simp add: on_curve_def add_def Let_def)
          apply (field on_curve1)
          apply (simp add: two_not_zero)
          done
      qed
    next
      case False
      note on_curve1 = \<open>on_curve a b p\<^sub>1\<close> [simplified Point' on_curve_def, simplified]
      note on_curve2 = \<open>on_curve a b p\<^sub>2\<close> [simplified Point on_curve_def, simplified]
      from assms show ?thesis
        apply (simp add: on_curve_def add_def Let_def False Point Point')
        apply (field on_curve1 on_curve2)
        apply (simp add: False [symmetric])
        done
    qed
  next
    case Infinity
    with Point \<open>on_curve a b p\<^sub>1\<close> show ?thesis
      by (simp add: add_def)
  qed
next
  case Infinity
  with \<open>on_curve a b p\<^sub>2\<close> show ?thesis
    by (simp add: add_def)
qed

lemma add_case [consumes 2, case_names InfL InfR Opp Tan Gen]:
  assumes p: "on_curve a b p"
  and q: "on_curve a b q"
  and R1: "\<And>p. P Infinity p p"
  and R2: "\<And>p. P p Infinity p"
  and R3: "\<And>p. on_curve a b p \<Longrightarrow> P p (opp p) Infinity"
  and R4: "\<And>p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 l.
    p\<^sub>1 = Point x\<^sub>1 y\<^sub>1 \<Longrightarrow> p\<^sub>2 = Point x\<^sub>2 y\<^sub>2 \<Longrightarrow>
    p\<^sub>2 = add a p\<^sub>1 p\<^sub>1 \<Longrightarrow> y\<^sub>1 \<noteq> 0 \<Longrightarrow>
    l = (3 * x\<^sub>1 ^ 2 + a) / (2 * y\<^sub>1) \<Longrightarrow>
    x\<^sub>2 = l ^ 2 - 2 * x\<^sub>1 \<Longrightarrow>
    y\<^sub>2 = - y\<^sub>1 - l * (x\<^sub>2 - x\<^sub>1) \<Longrightarrow>
    P p\<^sub>1 p\<^sub>1 p\<^sub>2"
  and R5: "\<And>p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 p\<^sub>3 x\<^sub>3 y\<^sub>3 l.
    p\<^sub>1 = Point x\<^sub>1 y\<^sub>1 \<Longrightarrow> p\<^sub>2 = Point x\<^sub>2 y\<^sub>2 \<Longrightarrow> p\<^sub>3 = Point x\<^sub>3 y\<^sub>3 \<Longrightarrow>
    p\<^sub>3 = add a p\<^sub>1 p\<^sub>2 \<Longrightarrow> x\<^sub>1 \<noteq> x\<^sub>2 \<Longrightarrow>
    l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1) \<Longrightarrow>
    x\<^sub>3 = l ^ 2 - x\<^sub>1 - x\<^sub>2 \<Longrightarrow>
    y\<^sub>3 = - y\<^sub>1 - l * (x\<^sub>3 - x\<^sub>1) \<Longrightarrow>
    P p\<^sub>1 p\<^sub>2 p\<^sub>3"
  shows "P p q (add a p q)"
proof (cases p)
  case Infinity
  then show ?thesis
    by (simp add: add_def R1)
next
  case (Point x\<^sub>1 y\<^sub>1)
  note Point' = this
  show ?thesis
  proof (cases q)
    case Infinity
    with Point show ?thesis
      by (simp add: add_def R2)
  next
    case (Point x\<^sub>2 y\<^sub>2)
    show ?thesis
    proof (cases "x\<^sub>1 = x\<^sub>2")
      case True
      note True' = this
      show ?thesis
      proof (cases "y\<^sub>1 = - y\<^sub>2")
        case True
        with p Point Point' True' R3 [of p] show ?thesis
          by (simp add: add_def opp_def)
      next
        case False
        from True' Point Point' p q have "(y\<^sub>1 - y\<^sub>2) * (y\<^sub>1 + y\<^sub>2) = 0"
          by (simp add: on_curve_def ring_distribs power2_eq_square)
        with False have "y\<^sub>1 = y\<^sub>2"
          by (simp add: eq_neg_iff_add_eq_0)
        with False True' Point Point' show ?thesis
          apply simp
          apply (rule R4)
          apply (auto simp add: add_def Let_def)
          done
      qed
    next
      case False
      with Point Point' show ?thesis
        apply -
        apply (rule R5)
        apply (auto simp add: add_def Let_def)
        done
    qed
  qed
qed

lemma eq_opp_is_zero: "((x::'a::ell_field) = - x) = (x = 0)"
proof
  assume "x = - x"
  have "2 * x = x + x" by simp
  also from \<open>x = - x\<close>
  have "\<dots> = - x + x" by simp
  also have "\<dots> = 0" by simp
  finally have "2 * x = 0" .
  with two_not_zero [where 'a='a] show "x = 0"
    by simp
qed simp

lemma add_casew [consumes 2, case_names InfL InfR Opp Gen]:
  assumes p: "on_curve a b p"
  and q: "on_curve a b q"
  and R1: "\<And>p. P Infinity p p"
  and R2: "\<And>p. P p Infinity p"
  and R3: "\<And>p. on_curve a b p \<Longrightarrow> P p (opp p) Infinity"
  and R4: "\<And>p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 p\<^sub>3 x\<^sub>3 y\<^sub>3 l.
    p\<^sub>1 = Point x\<^sub>1 y\<^sub>1 \<Longrightarrow> p\<^sub>2 = Point x\<^sub>2 y\<^sub>2 \<Longrightarrow> p\<^sub>3 = Point x\<^sub>3 y\<^sub>3 \<Longrightarrow>
    p\<^sub>3 = add a p\<^sub>1 p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<noteq> opp p\<^sub>2 \<Longrightarrow>
    x\<^sub>1 = x\<^sub>2 \<and> y\<^sub>1 = y\<^sub>2 \<and> l = (3 * x\<^sub>1 ^ 2 + a) / (2 * y\<^sub>1) \<or>
    x\<^sub>1 \<noteq> x\<^sub>2 \<and> l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1) \<Longrightarrow>
    x\<^sub>3 = l ^ 2 - x\<^sub>1 - x\<^sub>2 \<Longrightarrow>
    y\<^sub>3 = - y\<^sub>1 - l * (x\<^sub>3 - x\<^sub>1) \<Longrightarrow>
    P p\<^sub>1 p\<^sub>2 p\<^sub>3"
  shows "P p q (add a p q)"
  using p q
  apply (rule add_case)
  apply (rule R1)
  apply (rule R2)
  apply (rule R3)
  apply assumption
  apply (rule R4)
  apply assumption+
  apply (simp add: opp_def eq_opp_is_zero)
  apply simp
  apply simp
  apply simp
  apply (rule R4)
  apply assumption+
  apply (simp add: opp_def)
  apply simp
  apply assumption+
  done

definition
  "is_tangent p q = (p \<noteq> Infinity \<and> p = q \<and> p \<noteq> opp q)"

definition
  "is_generic p q =
     (p \<noteq> Infinity \<and> q \<noteq> Infinity \<and>
      p \<noteq> q \<and> p \<noteq> opp q)"

lemma diff_neq0:
  "(a::'a::ring) \<noteq> b \<Longrightarrow> a - b \<noteq> 0"
  "a \<noteq> b \<Longrightarrow> b - a \<noteq> 0"
  by simp_all

lemma minus2_not0: "(-2::'a::ell_field) \<noteq> 0"
  using two_not_zero [where 'a='a]
  by simp

lemmas [simp] = minus2_not0 [simplified]

declare two_not_zero [simplified, simp add]

lemma spec1_assoc:
  assumes p\<^sub>1: "on_curve a b p\<^sub>1"
  and p\<^sub>2: "on_curve a b p\<^sub>2"
  and p\<^sub>3: "on_curve a b p\<^sub>3"
  and "is_generic p\<^sub>1 p\<^sub>2"
  and "is_generic p\<^sub>2 p\<^sub>3"
  and "is_generic (add a p\<^sub>1 p\<^sub>2) p\<^sub>3"
  and "is_generic p\<^sub>1 (add a p\<^sub>2 p\<^sub>3)"
  shows "add a p\<^sub>1 (add a p\<^sub>2 p\<^sub>3) = add a (add a p\<^sub>1 p\<^sub>2) p\<^sub>3"
  using p\<^sub>1 p\<^sub>2 assms
proof (induct rule: add_case)
  case InfL
  show ?case by (simp add: add_def)
next
  case InfR
  show ?case by (simp add: add_def)
next
  case Opp
  then show ?case by (simp add: is_generic_def)
next
  case Tan
  then show ?case by (simp add: is_generic_def)
next
  case (Gen p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 p\<^sub>4 x\<^sub>4 y\<^sub>4 l)
  with \<open>on_curve a b p\<^sub>2\<close> \<open>on_curve a b p\<^sub>3\<close>
  show ?case
  proof (induct rule: add_case)
    case InfL
    then show ?case by (simp add: is_generic_def)
  next
    case InfR
    then show ?case by (simp add: is_generic_def)
  next
    case Opp
    then show ?case by (simp add: is_generic_def)
  next
    case Tan
    then show ?case by (simp add: is_generic_def)
  next
    case (Gen p\<^sub>2 x\<^sub>2' y\<^sub>2' p\<^sub>3 x\<^sub>3 y\<^sub>3 p\<^sub>5 x\<^sub>5 y\<^sub>5 l\<^sub>1)
    from \<open>on_curve a b p\<^sub>2\<close> \<open>on_curve a b p\<^sub>3\<close> \<open>p\<^sub>5 = add a p\<^sub>2 p\<^sub>3\<close>
    have "on_curve a b p\<^sub>5" by (simp add: add_closed)
    with \<open>on_curve a b p\<^sub>1\<close> show ?case using Gen [simplified \<open>p\<^sub>2 = Point x\<^sub>2' y\<^sub>2'\<close>]
    proof (induct rule: add_case)
      case InfL
      then show ?case by (simp add: is_generic_def)
    next
      case InfR
      then show ?case by (simp add: is_generic_def)
    next
      case (Opp p)
      from \<open>is_generic p (opp p)\<close>
      show ?case by (simp add: is_generic_def opp_opp)
    next
      case Tan
      then show ?case by (simp add: is_generic_def)
    next
      case (Gen p\<^sub>1 x\<^sub>1' y\<^sub>1' p\<^sub>5' x\<^sub>5' y\<^sub>5' p\<^sub>6 x\<^sub>6 y\<^sub>6 l\<^sub>2)
      from \<open>on_curve a b p\<^sub>1\<close> \<open>on_curve a b (Point x\<^sub>2' y\<^sub>2')\<close>
        \<open>p\<^sub>4 = add a p\<^sub>1 (Point x\<^sub>2' y\<^sub>2')\<close>
      have "on_curve a b p\<^sub>4" by (simp add: add_closed)
      then show ?case using \<open>on_curve a b p\<^sub>3\<close> Gen
      proof (induct rule: add_case)
        case InfL
        then show ?case by (simp add: is_generic_def)
      next
        case InfR
        then show ?case by (simp add: is_generic_def)
      next
        case (Opp p)
        from \<open>is_generic p (opp p)\<close>
        show ?case by (simp add: is_generic_def opp_opp)
      next
        case Tan
        then show ?case by (simp add: is_generic_def)
      next
        case (Gen p\<^sub>4' x\<^sub>4' y\<^sub>4' p\<^sub>3' x\<^sub>3' y\<^sub>3' p\<^sub>7 x\<^sub>7 y\<^sub>7 l\<^sub>3)
        from \<open>p\<^sub>4' = Point x\<^sub>4' y\<^sub>4'\<close> \<open>p\<^sub>4' = Point x\<^sub>4 y\<^sub>4\<close>
        have p\<^sub>4: "x\<^sub>4' = x\<^sub>4" "y\<^sub>4' = y\<^sub>4" by simp_all
        from \<open>p\<^sub>3' = Point x\<^sub>3' y\<^sub>3'\<close> \<open>p\<^sub>3' = Point x\<^sub>3 y\<^sub>3\<close>
        have p\<^sub>3: "x\<^sub>3' = x\<^sub>3" "y\<^sub>3' = y\<^sub>3" by simp_all
        from \<open>p\<^sub>1 = Point x\<^sub>1' y\<^sub>1'\<close> \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close>
        have p\<^sub>1: "x\<^sub>1' = x\<^sub>1" "y\<^sub>1' = y\<^sub>1" by simp_all
        from \<open>p\<^sub>5' = Point x\<^sub>5' y\<^sub>5'\<close> \<open>p\<^sub>5' = Point x\<^sub>5 y\<^sub>5\<close>
        have p\<^sub>5: "x\<^sub>5' = x\<^sub>5" "y\<^sub>5' = y\<^sub>5" by simp_all
        from \<open>Point x\<^sub>2' y\<^sub>2' = Point x\<^sub>2 y\<^sub>2\<close>
        have p\<^sub>2: "x\<^sub>2' = x\<^sub>2" "y\<^sub>2' = y\<^sub>2" by simp_all
        note ps = p\<^sub>1 p\<^sub>2 p\<^sub>3 p\<^sub>4 p\<^sub>5
        note ps' =
          \<open>on_curve a b p\<^sub>1\<close> [simplified \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close> on_curve_def, simplified]
          \<open>on_curve a b p\<^sub>2\<close> [simplified \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close> on_curve_def, simplified]
          \<open>on_curve a b p\<^sub>3\<close> [simplified \<open>p\<^sub>3 = Point x\<^sub>3 y\<^sub>3\<close> on_curve_def, simplified]
        show ?case
          apply (simp add: \<open>p\<^sub>6 = Point x\<^sub>6 y\<^sub>6\<close> \<open>p\<^sub>7 = Point x\<^sub>7 y\<^sub>7\<close>)
          apply (simp only: ps
            \<open>x\<^sub>6 = l\<^sub>2\<^sup>2 - x\<^sub>1' - x\<^sub>5'\<close> \<open>x\<^sub>7 = l\<^sub>3\<^sup>2 - x\<^sub>4' - x\<^sub>3'\<close>
            \<open>y\<^sub>6 = - y\<^sub>1' - l\<^sub>2 * (x\<^sub>6 - x\<^sub>1')\<close> \<open>y\<^sub>7 = - y\<^sub>4' - l\<^sub>3 * (x\<^sub>7 - x\<^sub>4')\<close>
            \<open>l\<^sub>2 = (y\<^sub>5' - y\<^sub>1') / (x\<^sub>5' - x\<^sub>1')\<close> \<open>l\<^sub>3 = (y\<^sub>3' - y\<^sub>4') / (x\<^sub>3' - x\<^sub>4')\<close>
            \<open>l\<^sub>1 = (y\<^sub>3 - y\<^sub>2') / (x\<^sub>3 - x\<^sub>2')\<close> \<open>l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)\<close>
            \<open>x\<^sub>5 = l\<^sub>1\<^sup>2 - x\<^sub>2' - x\<^sub>3\<close> \<open>y\<^sub>5 = - y\<^sub>2' - l\<^sub>1 * (x\<^sub>5 - x\<^sub>2')\<close>
            \<open>x\<^sub>4 = l\<^sup>2 - x\<^sub>1 - x\<^sub>2\<close> \<open>y\<^sub>4 = - y\<^sub>1 - l * (x\<^sub>4 - x\<^sub>1)\<close>)
          apply (rule conjI)
          apply (field ps')
          apply (rule conjI)
          apply (simp add: \<open>x\<^sub>2' \<noteq> x\<^sub>3\<close> [simplified \<open>x\<^sub>2' = x\<^sub>2\<close>, symmetric])
          apply (rule conjI)
          apply (rule notI)
          apply (ring (prems) ps'(1-2))
          apply (cut_tac \<open>x\<^sub>1' \<noteq> x\<^sub>5'\<close> [simplified \<open>x\<^sub>5' = x\<^sub>5\<close> \<open>x\<^sub>1' = x\<^sub>1\<close> \<open>x\<^sub>5 = l\<^sub>1\<^sup>2 - x\<^sub>2' - x\<^sub>3\<close>
            \<open>l\<^sub>1 = (y\<^sub>3 - y\<^sub>2') / (x\<^sub>3 - x\<^sub>2')\<close> \<open>y\<^sub>2' = y\<^sub>2\<close> \<open>x\<^sub>2' = x\<^sub>2\<close>])
          apply (erule notE)
          apply (rule sym)
          apply (field ps'(1-2))
          apply (simp add: \<open>x\<^sub>2' \<noteq> x\<^sub>3\<close> [simplified \<open>x\<^sub>2' = x\<^sub>2\<close>, symmetric])
          apply (rule conjI)
          apply (simp add: \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> [symmetric])
          apply (rule notI)
          apply (ring (prems) ps'(1-2))
          apply (cut_tac \<open>x\<^sub>4' \<noteq> x\<^sub>3'\<close> [simplified \<open>x\<^sub>4' = x\<^sub>4\<close> \<open>x\<^sub>3' = x\<^sub>3\<close> \<open>x\<^sub>4 = l\<^sup>2 - x\<^sub>1 - x\<^sub>2\<close>
            \<open>l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)\<close>])
          apply (erule notE)
          apply (rule sym)
          apply (field ps'(1-2))
          apply (simp add: \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> [symmetric])
          apply (field ps')
          apply (rule conjI)
          apply (rule notI)
          apply (ring (prems) ps'(1-2))
          apply (cut_tac \<open>x\<^sub>1' \<noteq> x\<^sub>5'\<close> [simplified \<open>x\<^sub>5' = x\<^sub>5\<close> \<open>x\<^sub>1' = x\<^sub>1\<close> \<open>x\<^sub>5 = l\<^sub>1\<^sup>2 - x\<^sub>2' - x\<^sub>3\<close>
            \<open>l\<^sub>1 = (y\<^sub>3 - y\<^sub>2') / (x\<^sub>3 - x\<^sub>2')\<close> \<open>y\<^sub>2' = y\<^sub>2\<close> \<open>x\<^sub>2' = x\<^sub>2\<close>])
          apply (erule notE)
          apply (rule sym)
          apply (field ps'(1-2))
          apply (simp add: \<open>x\<^sub>2' \<noteq> x\<^sub>3\<close> [simplified \<open>x\<^sub>2' = x\<^sub>2\<close>, symmetric])
          apply (rule conjI)
          apply (simp add: \<open>x\<^sub>2' \<noteq> x\<^sub>3\<close> [simplified \<open>x\<^sub>2' = x\<^sub>2\<close>, symmetric])
          apply (rule conjI)
          apply (rule notI)
          apply (ring (prems) ps'(1-2))
          apply (cut_tac \<open>x\<^sub>4' \<noteq> x\<^sub>3'\<close> [simplified \<open>x\<^sub>4' = x\<^sub>4\<close> \<open>x\<^sub>3' = x\<^sub>3\<close> \<open>x\<^sub>4 = l\<^sup>2 - x\<^sub>1 - x\<^sub>2\<close>
            \<open>l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)\<close>])
          apply (erule notE)
          apply (rule sym)
          apply (field ps'(1-2))
          apply (simp_all add: \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> [symmetric])
          done
      qed
    qed
  qed
qed

lemma spec2_assoc:
  assumes p\<^sub>1: "on_curve a b p\<^sub>1"
  and p\<^sub>2: "on_curve a b p\<^sub>2"
  and p\<^sub>3: "on_curve a b p\<^sub>3"
  and "is_generic p\<^sub>1 p\<^sub>2"
  and "is_tangent p\<^sub>2 p\<^sub>3"
  and "is_generic (add a p\<^sub>1 p\<^sub>2) p\<^sub>3"
  and "is_generic p\<^sub>1 (add a p\<^sub>2 p\<^sub>3)"
  shows "add a p\<^sub>1 (add a p\<^sub>2 p\<^sub>3) = add a (add a p\<^sub>1 p\<^sub>2) p\<^sub>3"
  using p\<^sub>1 p\<^sub>2 assms
proof (induct rule: add_case)
  case InfL
  show ?case by (simp add: add_def)
next
  case InfR
  show ?case by (simp add: add_def)
next
  case Opp
  then show ?case by (simp add: is_generic_def)
next
  case Tan
  then show ?case by (simp add: is_generic_def)
next
  case (Gen p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 p\<^sub>4 x\<^sub>4 y\<^sub>4 l)
  with \<open>on_curve a b p\<^sub>2\<close> \<open>on_curve a b p\<^sub>3\<close>
  show ?case
  proof (induct rule: add_case)
    case InfL
    then show ?case by (simp add: is_generic_def)
  next
    case InfR
    then show ?case by (simp add: is_generic_def)
  next
    case Opp
    then show ?case by (simp add: is_generic_def)
  next
    case (Tan p\<^sub>2 x\<^sub>2' y\<^sub>2' p\<^sub>5 x\<^sub>5 y\<^sub>5 l\<^sub>1)
    from \<open>on_curve a b p\<^sub>2\<close> \<open>p\<^sub>5 = add a p\<^sub>2 p\<^sub>2\<close>
    have "on_curve a b p\<^sub>5" by (simp add: add_closed)
    with \<open>on_curve a b p\<^sub>1\<close> show ?case using Tan
    proof (induct rule: add_case)
      case InfL
      then show ?case by (simp add: is_generic_def)
    next
      case InfR
      then show ?case by (simp add: is_generic_def)
    next
      case (Opp p)
      from \<open>is_generic p (opp p)\<close> \<open>on_curve a b p\<close>
      show ?case by (simp add: is_generic_def opp_opp)
    next
      case Tan
      then show ?case by (simp add: is_generic_def)
    next
      case (Gen p\<^sub>1 x\<^sub>1' y\<^sub>1' p\<^sub>5' x\<^sub>5' y\<^sub>5' p\<^sub>6 x\<^sub>6 y\<^sub>6 l\<^sub>2)
      from \<open>on_curve a b p\<^sub>1\<close> \<open>on_curve a b p\<^sub>2\<close> \<open>p\<^sub>4 = add a p\<^sub>1 p\<^sub>2\<close>
      have "on_curve a b p\<^sub>4" by (simp add: add_closed)
      then show ?case using \<open>on_curve a b p\<^sub>2\<close> Gen
      proof (induct rule: add_case)
        case InfL
        then show ?case by (simp add: is_generic_def)
      next
        case InfR
        then show ?case by (simp add: is_generic_def)
      next
        case (Opp p)
        from \<open>is_generic p (opp p)\<close>
        show ?case by (simp add: is_generic_def opp_opp)
      next
        case Tan
        then show ?case by (simp add: is_generic_def)
      next
        case (Gen p\<^sub>4' x\<^sub>4' y\<^sub>4' p\<^sub>3' x\<^sub>3' y\<^sub>3' p\<^sub>7 x\<^sub>7 y\<^sub>7 l\<^sub>3)
        from
          \<open>on_curve a b p\<^sub>1\<close> \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close>
          \<open>on_curve a b p\<^sub>2\<close> \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close>
        have
          y1: "y\<^sub>1 ^ 2 = x\<^sub>1 ^ 3 + a * x\<^sub>1 + b" and
          y2: "y\<^sub>2 ^ 2 = x\<^sub>2 ^ 3 + a * x\<^sub>2 + b"
          by (simp_all add: on_curve_def)
        from
          \<open>p\<^sub>5' = Point x\<^sub>5' y\<^sub>5'\<close>
          \<open>p\<^sub>5' = Point x\<^sub>5 y\<^sub>5\<close>
          \<open>p\<^sub>4' = Point x\<^sub>4' y\<^sub>4'\<close>
          \<open>p\<^sub>4' = Point x\<^sub>4 y\<^sub>4\<close>
          \<open>p\<^sub>3' = Point x\<^sub>2' y\<^sub>2'\<close>
          \<open>p\<^sub>3' = Point x\<^sub>2 y\<^sub>2\<close>
          \<open>p\<^sub>3' = Point x\<^sub>3' y\<^sub>3'\<close>
          \<open>p\<^sub>1 = Point x\<^sub>1' y\<^sub>1'\<close>
          \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close>
        have ps:
          "x\<^sub>5' = x\<^sub>5" "y\<^sub>5' = y\<^sub>5"
          "x\<^sub>4' = x\<^sub>4" "y\<^sub>4' = y\<^sub>4" "x\<^sub>3' = x\<^sub>2" "y\<^sub>3' = y\<^sub>2" "x\<^sub>2' = x\<^sub>2" "y\<^sub>2' = y\<^sub>2"
          "x\<^sub>1' = x\<^sub>1" "y\<^sub>1' = y\<^sub>1"
          by simp_all
        show ?case
          apply (simp add: \<open>p\<^sub>6 = Point x\<^sub>6 y\<^sub>6\<close> \<open>p\<^sub>7 = Point x\<^sub>7 y\<^sub>7\<close>)
          apply (simp only: ps
            \<open>x\<^sub>7 = l\<^sub>3 ^ 2 - x\<^sub>4' - x\<^sub>3'\<close>
            \<open>y\<^sub>7 = - y\<^sub>4' - l\<^sub>3 * (x\<^sub>7 - x\<^sub>4')\<close>
            \<open>l\<^sub>3 = (y\<^sub>3' - y\<^sub>4') / (x\<^sub>3' - x\<^sub>4')\<close>
            \<open>x\<^sub>6 = l\<^sub>2 ^ 2 - x\<^sub>1' - x\<^sub>5'\<close>
            \<open>y\<^sub>6 = - y\<^sub>1' - l\<^sub>2 * (x\<^sub>6 - x\<^sub>1')\<close>
            \<open>l\<^sub>2 = (y\<^sub>5' - y\<^sub>1') / (x\<^sub>5' - x\<^sub>1')\<close>
            \<open>x\<^sub>5 = l\<^sub>1 ^ 2 - 2 * x\<^sub>2'\<close>
            \<open>y\<^sub>5 = - y\<^sub>2' - l\<^sub>1 * (x\<^sub>5 - x\<^sub>2')\<close>
            \<open>l\<^sub>1 = (3 * x\<^sub>2' ^ 2 + a) / (2 * y\<^sub>2')\<close>
            \<open>x\<^sub>4 = l ^ 2 - x\<^sub>1 - x\<^sub>2\<close>
            \<open>y\<^sub>4 = - y\<^sub>1 - l * (x\<^sub>4 - x\<^sub>1)\<close>
            \<open>l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)\<close>)
          apply (rule conjI)
          apply (field y1 y2)
          apply (intro conjI)
          apply (simp add: \<open>y\<^sub>2' \<noteq> 0\<close> [simplified \<open>y\<^sub>2' = y\<^sub>2\<close>])
          apply (rule notI)
          apply (ring (prems) y1 y2)
          apply (rule notE [OF \<open>x\<^sub>1' \<noteq> x\<^sub>5'\<close> [simplified
            \<open>x\<^sub>5 = l\<^sub>1 ^ 2 - 2 * x\<^sub>2'\<close>
            \<open>l\<^sub>1 = (3 * x\<^sub>2' ^ 2 + a) / (2 * y\<^sub>2')\<close>
            \<open>x\<^sub>1' = x\<^sub>1\<close> \<open>x\<^sub>2' = x\<^sub>2\<close> \<open>y\<^sub>2' = y\<^sub>2\<close> \<open>x\<^sub>5' = x\<^sub>5\<close>]])
          apply (rule sym)
          apply (field y1 y2)
          apply (simp add: \<open>y\<^sub>2' \<noteq> 0\<close> [simplified \<open>y\<^sub>2' = y\<^sub>2\<close>])
          apply (simp add: \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> [symmetric])
          apply (rule notI)
          apply (ring (prems) y1 y2)
          apply (rule notE [OF \<open>x\<^sub>4' \<noteq> x\<^sub>3'\<close> [simplified
            \<open>x\<^sub>4 = l ^ 2 - x\<^sub>1 - x\<^sub>2\<close>
            \<open>l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)\<close>
            \<open>x\<^sub>4' = x\<^sub>4\<close> \<open>x\<^sub>3' = x\<^sub>2\<close>]])
          apply (rule sym)
          apply (field y1 y2)
          apply (simp add: \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> [symmetric])
          apply (field y1 y2)
          apply (intro conjI)
          apply (rule notI)
          apply (ring (prems) y1 y2)
          apply (rule notE [OF \<open>x\<^sub>1' \<noteq> x\<^sub>5'\<close> [simplified
            \<open>x\<^sub>5 = l\<^sub>1 ^ 2 - 2 * x\<^sub>2'\<close>
            \<open>l\<^sub>1 = (3 * x\<^sub>2' ^ 2 + a) / (2 * y\<^sub>2')\<close>
            \<open>x\<^sub>1' = x\<^sub>1\<close> \<open>x\<^sub>2' = x\<^sub>2\<close> \<open>y\<^sub>2' = y\<^sub>2\<close> \<open>x\<^sub>5' = x\<^sub>5\<close>]])
          apply (rule sym)
          apply (field y1 y2)
          apply (simp add: \<open>y\<^sub>2' \<noteq> 0\<close> [simplified \<open>y\<^sub>2' = y\<^sub>2\<close>])
          apply (simp add: \<open>y\<^sub>2' \<noteq> 0\<close> [simplified \<open>y\<^sub>2' = y\<^sub>2\<close>])
          apply (rule notI)
          apply (ring (prems) y1 y2)
          apply (rule notE [OF \<open>x\<^sub>4' \<noteq> x\<^sub>3'\<close> [simplified
            \<open>x\<^sub>4 = l ^ 2 - x\<^sub>1 - x\<^sub>2\<close>
            \<open>l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)\<close>
            \<open>x\<^sub>4' = x\<^sub>4\<close> \<open>x\<^sub>3' = x\<^sub>2\<close>]])
          apply (rule sym)
          apply (field y1 y2)
          apply (simp_all add: \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> [symmetric])
          done
      qed
    qed
  next
    case (Gen p\<^sub>3 x\<^sub>3 y\<^sub>3 p\<^sub>5 x\<^sub>5 y\<^sub>5 p\<^sub>6 x\<^sub>6 y\<^sub>6 l\<^sub>1)
    then show ?case by (simp add: is_tangent_def)
  qed
qed

lemma spec3_assoc:
  assumes p\<^sub>1: "on_curve a b p\<^sub>1"
  and p\<^sub>2: "on_curve a b p\<^sub>2"
  and p\<^sub>3: "on_curve a b p\<^sub>3"
  and "is_generic p\<^sub>1 p\<^sub>2"
  and "is_tangent p\<^sub>2 p\<^sub>3"
  and "is_generic (add a p\<^sub>1 p\<^sub>2) p\<^sub>3"
  and "is_tangent p\<^sub>1 (add a p\<^sub>2 p\<^sub>3)"
  shows "add a p\<^sub>1 (add a p\<^sub>2 p\<^sub>3) = add a (add a p\<^sub>1 p\<^sub>2) p\<^sub>3"
  using p\<^sub>1 p\<^sub>2 assms
proof (induct rule: add_case)
  case InfL
  then show ?case by (simp add: is_generic_def)
next
  case InfR
  then show ?case by (simp add: is_generic_def)
next
  case Opp
  then show ?case by (simp add: is_generic_def)
next
  case Tan
  then show ?case by (simp add: is_generic_def)
next
  case (Gen p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 p\<^sub>4 x\<^sub>4 y\<^sub>4 l)
  with \<open>on_curve a b p\<^sub>2\<close> \<open>on_curve a b p\<^sub>3\<close>
  show ?case
  proof (induct rule: add_case)
    case InfL
    then show ?case by (simp add: is_generic_def)
  next
    case InfR
    then show ?case by (simp add: is_generic_def)
  next
    case Opp
    then show ?case by (simp add: is_tangent_def opp_opp)
  next
    case (Tan p\<^sub>2 x\<^sub>2' y\<^sub>2' p\<^sub>5 x\<^sub>5 y\<^sub>5 l\<^sub>1)
    from \<open>on_curve a b p\<^sub>2\<close> \<open>p\<^sub>5 = add a p\<^sub>2 p\<^sub>2\<close>
    have "on_curve a b p\<^sub>5" by (simp add: add_closed)
    with \<open>on_curve a b p\<^sub>1\<close> show ?case using Tan
    proof (induct rule: add_case)
      case InfL
      then show ?case by (simp add: is_generic_def)
    next
      case InfR
      then show ?case by (simp add: is_generic_def)
    next
      case Opp
      then show ?case by (simp add: is_tangent_def opp_opp)
    next
      case (Tan p\<^sub>1 x\<^sub>1' y\<^sub>1' p\<^sub>6 x\<^sub>6 y\<^sub>6 l\<^sub>2)
      from \<open>on_curve a b p\<^sub>1\<close> \<open>on_curve a b p\<^sub>2\<close> \<open>p\<^sub>4 = add a p\<^sub>1 p\<^sub>2\<close>
      have "on_curve a b p\<^sub>4" by (simp add: add_closed)
      then show ?case using \<open>on_curve a b p\<^sub>2\<close> Tan
      proof (induct rule: add_case)
        case InfL
        then show ?case by (simp add: is_generic_def)
      next
        case InfR
        then show ?case by (simp add: is_generic_def)
      next
        case (Opp p)
        from \<open>is_generic p (opp p)\<close>
        show ?case by (simp add: is_generic_def opp_opp)
      next
        case Tan
        then show ?case by (simp add: is_generic_def)
      next
        case (Gen p\<^sub>4' x\<^sub>4' y\<^sub>4' p\<^sub>2' x\<^sub>2'' y\<^sub>2'' p\<^sub>7 x\<^sub>7 y\<^sub>7 l\<^sub>3)
        from
          \<open>on_curve a b p\<^sub>1\<close> \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close>
          \<open>on_curve a b p\<^sub>2\<close> \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close>
        have
          y1: "y\<^sub>1 ^ 2 = x\<^sub>1 ^ 3 + a * x\<^sub>1 + b" and
          y2: "y\<^sub>2 ^ 2 = x\<^sub>2 ^ 3 + a * x\<^sub>2 + b"
          by (simp_all add: on_curve_def)
        from
          \<open>p\<^sub>4' = Point x\<^sub>4' y\<^sub>4'\<close>
          \<open>p\<^sub>4' = Point x\<^sub>4 y\<^sub>4\<close>
          \<open>p\<^sub>2' = Point x\<^sub>2' y\<^sub>2'\<close>
          \<open>p\<^sub>2' = Point x\<^sub>2 y\<^sub>2\<close>
          \<open>p\<^sub>2' = Point x\<^sub>2'' y\<^sub>2''\<close>
          \<open>p\<^sub>1 = Point x\<^sub>1' y\<^sub>1'\<close>
          \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close>
          \<open>p\<^sub>1 = Point x\<^sub>5 y\<^sub>5\<close>
        have ps:
          "x\<^sub>4' = x\<^sub>4" "y\<^sub>4' = y\<^sub>4" "x\<^sub>2' = x\<^sub>2" "y\<^sub>2' = y\<^sub>2" "x\<^sub>2'' = x\<^sub>2" "y\<^sub>2'' = y\<^sub>2"
          "x\<^sub>1' = x\<^sub>5" "y\<^sub>1' = y\<^sub>5" "x\<^sub>1 = x\<^sub>5" "y\<^sub>1 = y\<^sub>5"
          by simp_all
        note qs =
          \<open>x\<^sub>7 = l\<^sub>3 ^ 2 - x\<^sub>4' - x\<^sub>2''\<close>
          \<open>y\<^sub>7 = - y\<^sub>4' - l\<^sub>3 * (x\<^sub>7 - x\<^sub>4')\<close>
          \<open>l\<^sub>3 = (y\<^sub>2'' - y\<^sub>4') / (x\<^sub>2'' - x\<^sub>4')\<close>
          \<open>x\<^sub>6 = l\<^sub>2 ^ 2 - 2 * x\<^sub>1'\<close>
          \<open>y\<^sub>6 = - y\<^sub>1' - l\<^sub>2 * (x\<^sub>6 - x\<^sub>1')\<close>
          \<open>x\<^sub>5 = l\<^sub>1 ^ 2 - 2 * x\<^sub>2'\<close>
          \<open>y\<^sub>5 = - y\<^sub>2' - l\<^sub>1 * (x\<^sub>5 - x\<^sub>2')\<close>
          \<open>l\<^sub>1 = (3 * x\<^sub>2' ^ 2 + a) / (2 * y\<^sub>2')\<close>
          \<open>l\<^sub>2 = (3 * x\<^sub>1' ^ 2 + a) / (2 * y\<^sub>1')\<close>
          \<open>x\<^sub>4 = l ^ 2 - x\<^sub>1 - x\<^sub>2\<close>
          \<open>y\<^sub>4 = - y\<^sub>1 - l * (x\<^sub>4 - x\<^sub>1)\<close>
          \<open>l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)\<close>
        from \<open>y\<^sub>2' \<noteq> 0\<close> \<open>y\<^sub>2' = y\<^sub>2\<close>
        have "2 * y\<^sub>2 \<noteq> 0" by simp
        show ?case
          apply (simp add: \<open>p\<^sub>6 = Point x\<^sub>6 y\<^sub>6\<close> \<open>p\<^sub>7 = Point x\<^sub>7 y\<^sub>7\<close>)
          apply (simp only: ps qs)
          apply (rule conjI)
          apply (field y2)
          apply (intro conjI)
          apply (rule notI)
          apply (ring (prems))
          apply (rule notE [OF \<open>y\<^sub>1' \<noteq> 0\<close>])
          apply (simp only: ps qs)
          apply field
          apply (rule \<open>2 * y\<^sub>2 \<noteq> 0\<close>)
          apply (rule notI)
          apply (ring (prems))
          apply (rule notE [OF \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close>])
          apply (rule sym)
          apply (simp only: ps qs)
          apply field
          apply (rule \<open>2 * y\<^sub>2 \<noteq> 0\<close>)
          apply (rule \<open>2 * y\<^sub>2 \<noteq> 0\<close>)
          apply (rule notI)
          apply (ring (prems))
          apply (rule notE [OF \<open>x\<^sub>4' \<noteq> x\<^sub>2''\<close>])
          apply (rule sym)
          apply (simp only: ps qs)
          apply field
          apply (intro conjI)
          apply (rule \<open>2 * y\<^sub>2 \<noteq> 0\<close>)
          apply (erule thin_rl)
          apply (rule notI)
          apply (ring (prems))
          apply (rule notE [OF \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close>])
          apply (rule sym)
          apply (simp only: ps qs)
          apply field
          apply (rule \<open>2 * y\<^sub>2 \<noteq> 0\<close>)
          apply (field y2)
          apply (intro conjI)
          apply (rule notI)
          apply (ring (prems))
          apply (rule notE [OF \<open>y\<^sub>1' \<noteq> 0\<close>])
          apply (simp only: ps qs)
          apply field
          apply (rule \<open>2 * y\<^sub>2 \<noteq> 0\<close>)
          apply (rule notI)
          apply (ring (prems))
          apply (rule notE [OF \<open>x\<^sub>4' \<noteq> x\<^sub>2''\<close>])
          apply (rule sym)
          apply (simp only: ps qs)
          apply field
          apply (erule thin_rl)
          apply (rule conjI)
          apply (rule \<open>2 * y\<^sub>2 \<noteq> 0\<close>)
          apply (rule notI)
          apply (ring (prems))
          apply (rule notE [OF \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close>])
          apply (rule sym)
          apply (simp only: ps qs)
          apply field
          apply (rule \<open>2 * y\<^sub>2 \<noteq> 0\<close>)
          apply (rule \<open>2 * y\<^sub>2 \<noteq> 0\<close>)
          apply (rule notI)
          apply (ring (prems))
          apply (rule notE [OF \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close>])
          apply (rule sym)
          apply (simp only: ps qs)
          apply field
          apply (rule \<open>2 * y\<^sub>2 \<noteq> 0\<close>)
          done
      qed
    next
      case Gen
      then show ?case by (simp add: is_tangent_def)
    qed
  next
    case Gen
    then show ?case by (simp add: is_tangent_def)
  qed
qed

lemma add_0_l: "add a Infinity p = p"
  by (simp add: add_def)

lemma add_0_r: "add a p Infinity = p"
  by (simp add: add_def split: point.split)

lemma add_opp: "on_curve a b p \<Longrightarrow> add a p (opp p) = Infinity"
  by (simp add: add_def opp_def on_curve_def split: point.split_asm)

lemma add_comm:
  assumes "on_curve a b p\<^sub>1" "on_curve a b p\<^sub>2"
  shows "add a p\<^sub>1 p\<^sub>2 = add a p\<^sub>2 p\<^sub>1"
proof (cases p\<^sub>1)
  case Infinity
  then show ?thesis by (simp add: add_0_l add_0_r)
next
  case (Point x\<^sub>1 y\<^sub>1)
  note Point' = this
  with \<open>on_curve a b p\<^sub>1\<close>
  have y1: "y\<^sub>1 ^ 2 = x\<^sub>1 ^ 3 + a * x\<^sub>1 + b"
    by (simp add: on_curve_def)
  show ?thesis
  proof (cases p\<^sub>2)
    case Infinity
    then show ?thesis by (simp add: add_0_l add_0_r)
  next
    case (Point x\<^sub>2 y\<^sub>2)
    with \<open>on_curve a b p\<^sub>2\<close>
    have y2: "y\<^sub>2 ^ 2 = x\<^sub>2 ^ 3 + a * x\<^sub>2 + b"
      by (simp add: on_curve_def)
    show ?thesis
    proof (cases "x\<^sub>1 = x\<^sub>2")
      case True
      show ?thesis
      proof (cases "y\<^sub>1 = - y\<^sub>2")
        case True
        with Point Point' \<open>x\<^sub>1 = x\<^sub>2\<close> show ?thesis
          by (simp add: add_def)
      next
        case False
        with y1 y2 [symmetric] \<open>x\<^sub>1 = x\<^sub>2\<close> Point Point'
        show ?thesis
          by (simp add: power2_eq_square square_eq_iff)
      qed
    next
      case False
      with Point Point' show ?thesis
        apply (simp add: add_def Let_def)
        apply (rule conjI)
        apply field
        apply simp
        apply field
        apply simp
        done
    qed
  qed
qed

lemma uniq_opp:
  assumes "add a p\<^sub>1 p\<^sub>2 = Infinity"
  shows "p\<^sub>2 = opp p\<^sub>1"
  using assms
  by (auto simp add: add_def opp_def Let_def
    split: point.split_asm if_split_asm)

lemma uniq_zero:
  assumes ab: "nonsingular a b"
  and p\<^sub>1: "on_curve a b p\<^sub>1"
  and p\<^sub>2: "on_curve a b p\<^sub>2"
  and add: "add a p\<^sub>1 p\<^sub>2 = p\<^sub>2"
  shows "p\<^sub>1 = Infinity"
  using p\<^sub>1 p\<^sub>2 assms
proof (induct rule: add_case)
  case InfL
  show ?case ..
next
  case InfR
  then show ?case by simp
next
  case Opp
  then show ?case by (simp add: opp_def split: point.split_asm)
next
  case (Tan p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 l)
  from \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close> \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close> \<open>p\<^sub>2 = p\<^sub>1\<close>
  have "x\<^sub>2 = x\<^sub>1" "y\<^sub>2 = y\<^sub>1" by simp_all
  with \<open>y\<^sub>2 = - y\<^sub>1 - l * (x\<^sub>2 - x\<^sub>1)\<close> \<open>y\<^sub>1 \<noteq> 0\<close>
  have "- y\<^sub>1 = y\<^sub>1" by simp
  with \<open>y\<^sub>1 \<noteq> 0\<close>
  show ?case by simp
next
  case (Gen p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 p\<^sub>3 x\<^sub>3 y\<^sub>3 l)
  then have y1: "y\<^sub>1 ^ 2 = x\<^sub>1 ^ 3 + a * x\<^sub>1 + b"
    and y2: "y\<^sub>2 ^ 2 = x\<^sub>2 ^ 3 + a * x\<^sub>2 + b"
    by (simp_all add: on_curve_def)
  from \<open>p\<^sub>3 = p\<^sub>2\<close> \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close> \<open>p\<^sub>3 = Point x\<^sub>3 y\<^sub>3\<close>
  have ps: "x\<^sub>3 = x\<^sub>2" "y\<^sub>3 = y\<^sub>2" by simp_all
  with \<open>y\<^sub>3 = - y\<^sub>1 - l * (x\<^sub>3 - x\<^sub>1)\<close>
  have "y\<^sub>2 = - y\<^sub>1 - l * (x\<^sub>2 - x\<^sub>1)" by simp
  also from \<open>l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)\<close> \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close>
  have "l * (x\<^sub>2 - x\<^sub>1) = y\<^sub>2 - y\<^sub>1"
    by simp
  also have "- y\<^sub>1 - (y\<^sub>2 - y\<^sub>1) = (- y\<^sub>1 + y\<^sub>1) + - y\<^sub>2"
    by simp
  finally have "y\<^sub>2 = 0" by simp
  with \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close> \<open>on_curve a b p\<^sub>2\<close>
  have x2: "x\<^sub>2 ^ 3 = - (a * x\<^sub>2 + b)"
    by (simp add: on_curve_def eq_neg_iff_add_eq_0 add.assoc del: minus_add_distrib)
  from \<open>x\<^sub>3 = l ^ 2 - x\<^sub>1 - x\<^sub>2\<close> \<open>x\<^sub>3 = x\<^sub>2\<close>
  have "l ^ 2 - x\<^sub>1 - x\<^sub>2 - x\<^sub>2 = x\<^sub>2 - x\<^sub>2" by simp
  then have "l ^ 2 - x\<^sub>1 - 2 * x\<^sub>2 = 0" by simp
  then have "x\<^sub>2 * (l ^ 2 - x\<^sub>1 - 2 * x\<^sub>2) = x\<^sub>2 * 0" by simp
  then have "(x\<^sub>2 - x\<^sub>1) * (2 * a * x\<^sub>2 + 3 * b) = 0"
    apply (simp only: \<open>l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)\<close> \<open>y\<^sub>2 = 0\<close>)
    apply (field (prems) y1 x2)
    apply (ring y1 x2)
    apply (simp add: \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> [symmetric])
    done
  with \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> have "2 * a * x\<^sub>2 + 3 * b = 0" by simp
  then have "2 * a * x\<^sub>2 = - (3 * b)"
    by (simp add: eq_neg_iff_add_eq_0)
  from y2 [symmetric] \<open>y\<^sub>2 = 0\<close>
  have "(- (2 * a)) ^ 3 * (x\<^sub>2 ^ 3 + a * x\<^sub>2 + b) = 0"
    by simp
  then have "b * (4 * a ^ 3 + 27 * b ^ 2) = 0"
    apply (ring (prems) \<open>2 * a * x\<^sub>2 = - (3 * b)\<close>)
    apply (ring \<open>2 * a * x\<^sub>2 = - (3 * b)\<close>)
    done
  with ab have "b = 0" by (simp add: nonsingular_def)
  with \<open>2 * a * x\<^sub>2 + 3 * b = 0\<close> ab
  have "x\<^sub>2 = 0" by (simp add: nonsingular_def)
  from \<open>l ^ 2 - x\<^sub>1 - 2 * x\<^sub>2 = 0\<close>
  show ?case
    apply (simp add: \<open>x\<^sub>2 = 0\<close> \<open>y\<^sub>2 = 0\<close> \<open>l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)\<close>)
    apply (field (prems) y1 \<open>b = 0\<close>)
    apply (insert ab \<open>b = 0\<close> \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> \<open>x\<^sub>2 = 0\<close>)
    apply (simp add: nonsingular_def)
    apply simp
    done
qed

lemma opp_add:
  assumes p\<^sub>1: "on_curve a b p\<^sub>1"
  and p\<^sub>2: "on_curve a b p\<^sub>2"
  shows "opp (add a p\<^sub>1 p\<^sub>2) = add a (opp p\<^sub>1) (opp p\<^sub>2)"
proof (cases p\<^sub>1)
  case Infinity
  then show ?thesis by (simp add: add_def opp_def)
next
  case (Point x\<^sub>1 y\<^sub>1)
  show ?thesis
  proof (cases p\<^sub>2)
    case Infinity
    with \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close> show ?thesis
      by (simp add: add_def opp_def)
  next
    case (Point x\<^sub>2 y\<^sub>2)
    with \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close> p\<^sub>1 p\<^sub>2
    have "x\<^sub>1 ^ 3 + a * x\<^sub>1 + b = y\<^sub>1 ^ 2"
      "x\<^sub>2 ^ 3 + a * x\<^sub>2 + b = y\<^sub>2 ^ 2"
      by (simp_all add: on_curve_def)
    with Point \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close> show ?thesis
      apply (cases "x\<^sub>1 = x\<^sub>2")
      apply (cases "y\<^sub>1 = - y\<^sub>2")
      apply (simp add: add_def opp_def Let_def)
      apply (simp add: add_def opp_def Let_def trans [OF minus_equation_iff eq_commute])
      apply (simp add: add_def opp_def Let_def)
      apply (rule conjI)
      apply field
      apply simp
      apply field
      apply simp
      done
  qed
qed

lemma compat_add_opp:
  assumes p\<^sub>1: "on_curve a b p\<^sub>1"
  and p\<^sub>2: "on_curve a b p\<^sub>2"
  and "add a p\<^sub>1 p\<^sub>2 = add a p\<^sub>1 (opp p\<^sub>2)"
  and "p\<^sub>1 \<noteq> opp p\<^sub>1"
  shows "p\<^sub>2 = opp p\<^sub>2"
  using p\<^sub>1 p\<^sub>2 assms
proof (induct rule: add_case)
  case InfL
  then show ?case by (simp add: add_0_l)
next
  case InfR
  then show ?case by (simp add: opp_def add_0_r)
next
  case (Opp p)
  then have "add a p p = Infinity" by (simp add: opp_opp)
  then have "p = opp p" by (rule uniq_opp)
  with \<open>p \<noteq> opp p\<close> show ?case ..
next
  case (Tan p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 l)
  then have "add a p\<^sub>1 p\<^sub>1 = Infinity"
    by (simp add: add_opp)
  then have "p\<^sub>1 = opp p\<^sub>1" by (rule uniq_opp)
  with \<open>p\<^sub>1 \<noteq> opp p\<^sub>1\<close> show ?case ..
next
  case (Gen p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 p\<^sub>3 x\<^sub>3 y\<^sub>3 l)
  have "(2::'a) * 2 \<noteq> 0"
    by (simp only: mult_eq_0_iff) simp
  then have "(4::'a) \<noteq> 0" by simp
  from Gen have "((- y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)) ^ 2 - x\<^sub>1 - x\<^sub>2 =
    ((y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)) ^ 2 - x\<^sub>1 - x\<^sub>2"
    by (simp add: add_def opp_def Let_def)
  then show ?case
    apply (field (prems))
    apply (insert \<open>p\<^sub>1 \<noteq> opp p\<^sub>1\<close>
      \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close> \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close> \<open>4 \<noteq> 0\<close>)[1]
    apply (simp add: opp_def eq_neg_iff_add_eq_0)
    apply (simp add: \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> [symmetric])
    done
qed

lemma compat_add_triple:
  assumes ab: "nonsingular a b"
  and p: "on_curve a b p"
  and "p \<noteq> opp p"
  and "add a p p \<noteq> opp p"
  shows "add a (add a p p) (opp p) = p"
  using add_closed [OF p p] opp_closed [OF p] assms
proof (induct "add a p p" "opp p" rule: add_case)
  case InfL
  from \<open>p \<noteq> opp p\<close> uniq_opp [OF \<open>Infinity = add a p p\<close> [symmetric]]
  show ?case ..
next
  case InfR
  then show ?case by (simp add: opp_def split: point.split_asm)
next
  case Opp
  then have "opp (opp (add a p p)) = opp (opp p)" by simp
  then have "add a p p = p" by (simp add: opp_opp)
  with uniq_zero [OF ab p p] \<open>p \<noteq> opp p\<close>
  show ?case by (simp add: opp_def)
next
  case Tan
  then show ?case by simp
next
  case (Gen x\<^sub>1 y\<^sub>1 x\<^sub>2 y\<^sub>2 p\<^sub>3 x\<^sub>3 y\<^sub>3 l)
  from \<open>opp p = Point x\<^sub>2 y\<^sub>2\<close>
  have "p = Point x\<^sub>2 (- y\<^sub>2)"
    by (auto simp add: opp_def split: point.split_asm)
  with \<open>add a p p = Point x\<^sub>1 y\<^sub>1\<close> [symmetric]
  obtain l' where l':
    "l' = (3 * x\<^sub>2 ^ 2 + a) / (2 * - y\<^sub>2)"
    and xy: "x\<^sub>1 = l' ^ 2 - 2 * x\<^sub>2"
    "y\<^sub>1 = - (- y\<^sub>2) - l' * (x\<^sub>1 - x\<^sub>2)"
    and y2: "- y\<^sub>2 \<noteq> - (- y\<^sub>2)"
    by (simp add: add_def Let_def split: if_split_asm)
  have "x\<^sub>3 = x\<^sub>2"
    apply (simp add: xy
      \<open>l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)\<close> \<open>x\<^sub>3 = l ^ 2 - x\<^sub>1 - x\<^sub>2\<close>)
    apply field
    apply (insert \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close>)
    apply (simp add: xy)
    done
  then have "p\<^sub>3 = p \<or> p\<^sub>3 = opp p"
    by (rule curve_elt_opp [OF \<open>p\<^sub>3 = Point x\<^sub>3 y\<^sub>3\<close> \<open>p = Point x\<^sub>2 (- y\<^sub>2)\<close>
      add_closed [OF add_closed [OF p p] opp_closed [OF p],
        folded \<open>p\<^sub>3 = add a (add a p p) (opp p)\<close>]
     \<open>on_curve a b p\<close>])
  then show ?case
  proof
    assume "p\<^sub>3 = p"
    with \<open>p\<^sub>3 = add a (add a p p) (opp p)\<close>
    show ?thesis by simp
  next
    assume "p\<^sub>3 = opp p"
    with \<open>p\<^sub>3 = add a (add a p p) (opp p)\<close>
    have "add a (add a p p) (opp p) = opp p" by simp
    with ab add_closed [OF p p] opp_closed [OF p]
    have "add a p p = Infinity" by (rule uniq_zero)
    with \<open>add a p p = Point x\<^sub>1 y\<^sub>1\<close> show ?thesis by simp
  qed
qed

lemma add_opp_double_opp:
  assumes ab: "nonsingular a b"
  and p\<^sub>1: "on_curve a b p\<^sub>1"
  and p\<^sub>2: "on_curve a b p\<^sub>2"
  and "add a p\<^sub>1 p\<^sub>2 = opp p\<^sub>1"
  shows "p\<^sub>2 = add a (opp p\<^sub>1) (opp p\<^sub>1)"
proof (cases "p\<^sub>1 = opp p\<^sub>1")
  case True
  with assms have "add a p\<^sub>2 p\<^sub>1 = p\<^sub>1" by (simp add: add_comm)
  with ab p\<^sub>2 p\<^sub>1 have "p\<^sub>2 = Infinity" by (rule uniq_zero)
  also from \<open>on_curve a b p\<^sub>1\<close> have "\<dots> = add a p\<^sub>1 (opp p\<^sub>1)"
    by (simp add: add_opp)
  also from True have "\<dots> = add a (opp p\<^sub>1) (opp p\<^sub>1)" by simp
  finally show ?thesis .
next
  case False
  from p\<^sub>1 p\<^sub>2 False assms show ?thesis
  proof (induct rule: add_case)
    case InfL
    then show ?case by simp
  next
    case InfR
    then show ?case by simp
  next
    case Opp
    then show ?case by (simp add: add_0_l)
  next
    case (Tan p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 l)
    from \<open>p\<^sub>2 = opp p\<^sub>1\<close> \<open>on_curve a b p\<^sub>1\<close>
    have "p\<^sub>1 = opp p\<^sub>2" by (simp add: opp_opp)
    also note \<open>p\<^sub>2 = add a p\<^sub>1 p\<^sub>1\<close>
    finally show ?case using \<open>on_curve a b p\<^sub>1\<close>
      by (simp add: opp_add)
  next
    case (Gen p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 p\<^sub>3 x\<^sub>3 y\<^sub>3 l)
    from \<open>on_curve a b p\<^sub>1\<close> \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close>
    have y\<^sub>1: "y\<^sub>1 ^ 2 = x\<^sub>1 ^ 3 + a * x\<^sub>1 + b"
      by (simp add: on_curve_def)
    from \<open>on_curve a b p\<^sub>2\<close> \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close>
    have y\<^sub>2: "y\<^sub>2 ^ 2 = x\<^sub>2 ^ 3 + a * x\<^sub>2 + b"
      by (simp add: on_curve_def)
    from \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close> \<open>p\<^sub>1 \<noteq> opp p\<^sub>1\<close>
    have "y\<^sub>1 \<noteq> 0"
      by (simp add: opp_Point)
    from Gen have "x\<^sub>1 = ((y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)) ^ 2 - x\<^sub>1 - x\<^sub>2"
      by (simp add: opp_Point)
    then have "2 * y\<^sub>2 * y\<^sub>1 = a * x\<^sub>2 + 3 * x\<^sub>2 * x\<^sub>1 ^ 2 + a * x\<^sub>1 -
      x\<^sub>1 ^ 3 + 2 * b"
      apply (field (prems) y\<^sub>1 y\<^sub>2)
      apply (field y\<^sub>1 y\<^sub>2)
      apply simp
      apply (simp add: \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> [symmetric])
      done
    then have "(x\<^sub>2 - (((3 * x\<^sub>1 ^ 2 + a) / (2 * (- y\<^sub>1))) ^ 2 -
      2 * x\<^sub>1)) * (x\<^sub>2 - x\<^sub>1) ^ 2 = 0"
      apply (drule_tac f="\<lambda>x. x ^ 2" in arg_cong)
      apply (field (prems) y\<^sub>1 y\<^sub>2)
      apply (field y\<^sub>1 y\<^sub>2)
      apply (simp_all add: \<open>y\<^sub>1 \<noteq> 0\<close>)
      done
    with \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close>
    have "x\<^sub>2 = ((3 * x\<^sub>1 ^ 2 + a) / (2 * (- y\<^sub>1))) ^ 2 - 2 * x\<^sub>1"
      by simp
    with \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close> _ \<open>on_curve a b p\<^sub>2\<close>
      add_closed [OF
        opp_closed [OF \<open>on_curve a b p\<^sub>1\<close>] opp_closed [OF \<open>on_curve a b p\<^sub>1\<close>]]
    have "p\<^sub>2 = add a (opp p\<^sub>1) (opp p\<^sub>1) \<or> p\<^sub>2 = opp (add a (opp p\<^sub>1) (opp p\<^sub>1))"
      apply (rule curve_elt_opp)
      apply (simp add: add_def opp_Point Let_def \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close> \<open>y\<^sub>1 \<noteq> 0\<close>)
      done
    then show ?case
    proof
      assume "p\<^sub>2 = opp (add a (opp p\<^sub>1) (opp p\<^sub>1))"
      with \<open>on_curve a b p\<^sub>1\<close>
      have "p\<^sub>2 = add a p\<^sub>1 p\<^sub>1"
        by (simp add: opp_add [of a b] opp_opp opp_closed)
      show ?case
      proof (cases "add a p\<^sub>1 p\<^sub>1 = opp p\<^sub>1")
        case True
        from \<open>on_curve a b p\<^sub>1\<close>
        show ?thesis
          apply (simp add: opp_add [symmetric] \<open>p\<^sub>2 = add a p\<^sub>1 p\<^sub>1\<close> True)
          apply (simp add: \<open>p\<^sub>3 = add a p\<^sub>1 p\<^sub>2\<close> [simplified \<open>p\<^sub>3 = opp p\<^sub>1\<close>])
          apply (simp add: \<open>p\<^sub>2 = add a p\<^sub>1 p\<^sub>1\<close> True add_opp)
          done
      next
        case False
        from \<open>on_curve a b p\<^sub>1\<close>
        have "add a p\<^sub>1 (opp p\<^sub>2) = opp (add a (add a p\<^sub>1 p\<^sub>1) (opp p\<^sub>1))"
          by (simp add: \<open>p\<^sub>2 = add a p\<^sub>1 p\<^sub>1\<close>
            opp_add [of a b] add_closed opp_closed opp_opp add_comm [of a b])
        with ab \<open>on_curve a b p\<^sub>1\<close> \<open>p\<^sub>1 \<noteq> opp p\<^sub>1\<close> False
        have "add a p\<^sub>1 (opp p\<^sub>2) = opp p\<^sub>1"
          by (simp add: compat_add_triple)
        with \<open>p\<^sub>3 = add a p\<^sub>1 p\<^sub>2\<close> \<open>p\<^sub>3 = opp p\<^sub>1\<close>
        have "add a p\<^sub>1 p\<^sub>2 = add a p\<^sub>1 (opp p\<^sub>2)" by simp
        with \<open>on_curve a b p\<^sub>1\<close> \<open>on_curve a b p\<^sub>2\<close>
        have "p\<^sub>2 = opp p\<^sub>2" using \<open>p\<^sub>1 \<noteq> opp p\<^sub>1\<close>
          by (rule compat_add_opp)
        with \<open>on_curve a b p\<^sub>1\<close> \<open>p\<^sub>2 = add a p\<^sub>1 p\<^sub>1\<close>
        show ?thesis by (simp add: opp_add)
      qed
    qed
  qed
qed

lemma cancel:
  assumes ab: "nonsingular a b"
  and p\<^sub>1: "on_curve a b p\<^sub>1"
  and p\<^sub>2: "on_curve a b p\<^sub>2"
  and p\<^sub>3: "on_curve a b p\<^sub>3"
  and eq: "add a p\<^sub>1 p\<^sub>2 = add a p\<^sub>1 p\<^sub>3"
  shows "p\<^sub>2 = p\<^sub>3"
  using p\<^sub>1 p\<^sub>2 p\<^sub>1 p\<^sub>2 eq
proof (induct rule: add_casew)
  case InfL
  then show ?case by (simp add: add_0_l)
next
  case (InfR p)
  with p\<^sub>3 have "add a p\<^sub>3 p = p" by (simp add: add_comm)
  with ab p\<^sub>3 \<open>on_curve a b p\<close>
  show ?case by (rule uniq_zero [symmetric])
next
  case (Opp p)
  from \<open>Infinity = add a p p\<^sub>3\<close> [symmetric]
  show ?case by (rule uniq_opp [symmetric])
next
  case (Gen p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 p\<^sub>4 x\<^sub>4 y\<^sub>4 l)
  from \<open>on_curve a b p\<^sub>1\<close> p\<^sub>3 \<open>on_curve a b p\<^sub>1\<close> p\<^sub>3 \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close>
    \<open>p\<^sub>4 = add a p\<^sub>1 p\<^sub>2\<close> \<open>p\<^sub>4 = add a p\<^sub>1 p\<^sub>3\<close> \<open>p\<^sub>1 \<noteq> opp p\<^sub>2\<close>
  show ?case
  proof (induct rule: add_casew)
    case InfL
    then show ?case by (simp add: add_0_l)
  next
    case (InfR p)
    with \<open>on_curve a b p\<^sub>2\<close>
    have "add a p\<^sub>2 p = p" by (simp add: add_comm)
    with ab \<open>on_curve a b p\<^sub>2\<close> \<open>on_curve a b p\<close>
    show ?case by (rule uniq_zero)
  next
    case (Opp p)
    then have "add a p p\<^sub>2 = Infinity" by simp
    then show ?case by (rule uniq_opp)
  next
    case (Gen p\<^sub>1 x\<^sub>1' y\<^sub>1' p\<^sub>3 x\<^sub>3 y\<^sub>3 p\<^sub>5 x\<^sub>5 y\<^sub>5 l')
    from \<open>p\<^sub>4 = p\<^sub>5\<close> \<open>p\<^sub>4 = Point x\<^sub>4 y\<^sub>4\<close> \<open>p\<^sub>5 = Point x\<^sub>5 y\<^sub>5\<close>
      \<open>p\<^sub>1 = Point x\<^sub>1' y\<^sub>1'\<close> \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close>
      \<open>y\<^sub>4 = - y\<^sub>1 - l * (x\<^sub>4 - x\<^sub>1)\<close> \<open>y\<^sub>5 = - y\<^sub>1' - l' * (x\<^sub>5 - x\<^sub>1')\<close>
    have "0 = - y\<^sub>1 - l * (x\<^sub>4 - x\<^sub>1) - (- y\<^sub>1 - l' * (x\<^sub>4 - x\<^sub>1))"
      by auto
    then have "l' = l \<or> x\<^sub>4 = x\<^sub>1" by auto
    then show ?case
    proof
      assume "l' = l"
      with \<open>p\<^sub>4 = p\<^sub>5\<close> \<open>p\<^sub>4 = Point x\<^sub>4 y\<^sub>4\<close> \<open>p\<^sub>5 = Point x\<^sub>5 y\<^sub>5\<close>
        \<open>p\<^sub>1 = Point x\<^sub>1' y\<^sub>1'\<close> \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close>
        \<open>x\<^sub>4 = l ^ 2 - x\<^sub>1 - x\<^sub>2\<close> \<open>x\<^sub>5 = l' ^ 2 - x\<^sub>1' - x\<^sub>3\<close>
      have "0 = l ^ 2 - x\<^sub>1 - x\<^sub>2 - (l ^ 2 - x\<^sub>1 - x\<^sub>3)"
        by simp
      then have "x\<^sub>2 = x\<^sub>3" by simp
      with \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close> \<open>p\<^sub>3 = Point x\<^sub>3 y\<^sub>3\<close> \<open>on_curve a b p\<^sub>2\<close> \<open>on_curve a b p\<^sub>3\<close>
      have "p\<^sub>2 = p\<^sub>3 \<or> p\<^sub>2 = opp p\<^sub>3" by (rule curve_elt_opp)
      then show ?case
      proof
        assume "p\<^sub>2 = opp p\<^sub>3"
        with \<open>on_curve a b p\<^sub>3\<close> have "opp p\<^sub>2 = p\<^sub>3"
          by (simp add: opp_opp)
        with \<open>p\<^sub>4 = p\<^sub>5\<close> \<open>p\<^sub>4 = add a p\<^sub>1 p\<^sub>2\<close> \<open>p\<^sub>5 = add a p\<^sub>1 p\<^sub>3\<close>
        have "add a p\<^sub>1 p\<^sub>2 = add a p\<^sub>1 (opp p\<^sub>2)" by simp
        show ?case
        proof (cases "p\<^sub>1 = opp p\<^sub>1")
          case True
          with \<open>p\<^sub>1 \<noteq> opp p\<^sub>2\<close> \<open>p\<^sub>1 \<noteq> opp p\<^sub>3\<close>
          have "p\<^sub>1 \<noteq> p\<^sub>2" "p\<^sub>1 \<noteq> p\<^sub>3" by auto
          with \<open>l' = l\<close> \<open>x\<^sub>1 = x\<^sub>2 \<and> _\<or> _\<close> \<open>x\<^sub>1' = x\<^sub>3 \<and> _ \<or> _\<close>
            \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close> \<open>p\<^sub>1 = Point x\<^sub>1' y\<^sub>1'\<close>
            \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close> \<open>p\<^sub>3 = Point x\<^sub>3 y\<^sub>3\<close>
            \<open>p\<^sub>2 = opp p\<^sub>3\<close>
          have eq: "(y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1) = (y\<^sub>3 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)" and "x\<^sub>1 \<noteq> x\<^sub>2"
            by (auto simp add: opp_Point)
          from eq have "y\<^sub>2 = y\<^sub>3"
            apply (field (prems))
            apply (simp_all add: \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> [symmetric])
            done
          with \<open>p\<^sub>2 = opp p\<^sub>3\<close> \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close> \<open>p\<^sub>3 = Point x\<^sub>3 y\<^sub>3\<close>
          show ?thesis by (simp add: opp_Point)
        next
          case False
          with \<open>on_curve a b p\<^sub>1\<close> \<open>on_curve a b p\<^sub>2\<close>
            \<open>add a p\<^sub>1 p\<^sub>2 = add a p\<^sub>1 (opp p\<^sub>2)\<close>
          have "p\<^sub>2 = opp p\<^sub>2" by (rule compat_add_opp)
          with \<open>opp p\<^sub>2 = p\<^sub>3\<close> show ?thesis by simp
        qed
      qed
    next
      assume "x\<^sub>4 = x\<^sub>1"
      with \<open>p\<^sub>4 = Point x\<^sub>4 y\<^sub>4\<close> [simplified \<open>p\<^sub>4 = add a p\<^sub>1 p\<^sub>2\<close>]
        \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close>
        add_closed [OF \<open>on_curve a b p\<^sub>1\<close> \<open>on_curve a b p\<^sub>2\<close>]
        \<open>on_curve a b p\<^sub>1\<close>
      have "add a p\<^sub>1 p\<^sub>2 = p\<^sub>1 \<or> add a p\<^sub>1 p\<^sub>2 = opp p\<^sub>1" by (rule curve_elt_opp)
      then show ?case
      proof
        assume "add a p\<^sub>1 p\<^sub>2 = p\<^sub>1"
        with \<open>on_curve a b p\<^sub>1\<close> \<open>on_curve a b p\<^sub>2\<close>
        have "add a p\<^sub>2 p\<^sub>1 = p\<^sub>1" by (simp add: add_comm)
        with ab \<open>on_curve a b p\<^sub>2\<close> \<open>on_curve a b p\<^sub>1\<close>
        have "p\<^sub>2 = Infinity" by (rule uniq_zero)
        moreover from \<open>add a p\<^sub>1 p\<^sub>2 = p\<^sub>1\<close>
          \<open>p\<^sub>4 = p\<^sub>5\<close> \<open>p\<^sub>4 = add a p\<^sub>1 p\<^sub>2\<close> \<open>p\<^sub>5 = add a p\<^sub>1 p\<^sub>3\<close>
          \<open>on_curve a b p\<^sub>1\<close> \<open>on_curve a b p\<^sub>3\<close>
        have "add a p\<^sub>3 p\<^sub>1 = p\<^sub>1" by (simp add: add_comm)
        with ab \<open>on_curve a b p\<^sub>3\<close> \<open>on_curve a b p\<^sub>1\<close>
        have "p\<^sub>3 = Infinity" by (rule uniq_zero)
        ultimately show ?case by simp
      next
        assume "add a p\<^sub>1 p\<^sub>2 = opp p\<^sub>1"
        with ab \<open>on_curve a b p\<^sub>1\<close> \<open>on_curve a b p\<^sub>2\<close>
        have "p\<^sub>2 = add a (opp p\<^sub>1) (opp p\<^sub>1)" by (rule add_opp_double_opp)
        moreover from \<open>add a p\<^sub>1 p\<^sub>2 = opp p\<^sub>1\<close>
          \<open>p\<^sub>4 = p\<^sub>5\<close> \<open>p\<^sub>4 = add a p\<^sub>1 p\<^sub>2\<close> \<open>p\<^sub>5 = add a p\<^sub>1 p\<^sub>3\<close>
        have "add a p\<^sub>1 p\<^sub>3 = opp p\<^sub>1" by simp
        with ab \<open>on_curve a b p\<^sub>1\<close> \<open>on_curve a b p\<^sub>3\<close>
        have "p\<^sub>3 = add a (opp p\<^sub>1) (opp p\<^sub>1)" by (rule add_opp_double_opp)
        ultimately show ?case by simp
      qed
    qed
  qed
qed

lemma add_minus_id:
  assumes ab: "nonsingular a b"
  and p\<^sub>1: "on_curve a b p\<^sub>1"
  and p\<^sub>2: "on_curve a b p\<^sub>2"
  shows "add a (add a p\<^sub>1 p\<^sub>2) (opp p\<^sub>2) = p\<^sub>1"
proof (cases "add a p\<^sub>1 p\<^sub>2 = opp p\<^sub>2")
  case True
  then have "add a (add a p\<^sub>1 p\<^sub>2) (opp p\<^sub>2) = add a (opp p\<^sub>2) (opp p\<^sub>2)"
    by simp
  also from p\<^sub>1 p\<^sub>2 True have "add a p\<^sub>2 p\<^sub>1 = opp p\<^sub>2"
    by (simp add: add_comm)
  with ab p\<^sub>2 p\<^sub>1 have "add a (opp p\<^sub>2) (opp p\<^sub>2) = p\<^sub>1"
    by (rule add_opp_double_opp [symmetric])
  finally show ?thesis .
next
  case False
  from p\<^sub>1 p\<^sub>2 p\<^sub>1 p\<^sub>2 False show ?thesis
  proof (induct rule: add_case)
    case InfL
    then show ?case by (simp add: add_opp)
  next
    case InfR
    show ?case by (simp add: add_0_r)
  next
    case Opp
    then show ?case by (simp add: opp_opp add_0_l)
  next
    case (Tan p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 l)
    note ab \<open>on_curve a b p\<^sub>1\<close>
    moreover from \<open>y\<^sub>1 \<noteq> 0\<close> \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close>
    have "p\<^sub>1 \<noteq> opp p\<^sub>1" by (simp add: opp_Point)
    moreover from \<open>p\<^sub>2 = add a p\<^sub>1 p\<^sub>1\<close> \<open>p\<^sub>2 \<noteq> opp p\<^sub>1\<close>
    have "add a p\<^sub>1 p\<^sub>1 \<noteq> opp p\<^sub>1" by simp
    ultimately have "add a (add a p\<^sub>1 p\<^sub>1) (opp p\<^sub>1) = p\<^sub>1"
      by (rule compat_add_triple)
    with \<open>p\<^sub>2 = add a p\<^sub>1 p\<^sub>1\<close> show ?case by simp
  next
    case (Gen p\<^sub>1 x\<^sub>1 y\<^sub>1 p\<^sub>2 x\<^sub>2 y\<^sub>2 p\<^sub>3 x\<^sub>3 y\<^sub>3 l)
    from \<open>p\<^sub>3 = add a p\<^sub>1 p\<^sub>2\<close> \<open>on_curve a b p\<^sub>2\<close>
    have "p\<^sub>3 = add a p\<^sub>1 (opp (opp p\<^sub>2))" by (simp add: opp_opp)
    with
      add_closed [OF \<open>on_curve a b p\<^sub>1\<close> \<open>on_curve a b p\<^sub>2\<close>,
        folded \<open>p\<^sub>3 = add a p\<^sub>1 p\<^sub>2\<close>]
      opp_closed [OF \<open>on_curve a b p\<^sub>2\<close>]
      opp_closed [OF \<open>on_curve a b p\<^sub>2\<close>]
      opp_opp [of p\<^sub>2]
      Gen
    show ?case
    proof (induct rule: add_case)
      case InfL
      then show ?case by simp
    next
      case InfR
      then show ?case by (simp add: add_0_r)
    next
      case (Opp p)
      from \<open>p = add a p\<^sub>1 (opp (opp p))\<close>
      have "add a p\<^sub>1 p = p" by (simp add: opp_opp)
      with ab \<open>on_curve a b p\<^sub>1\<close> \<open>on_curve a b p\<close>
      show ?case by (rule uniq_zero [symmetric])
    next
      case Tan
      then show ?case by simp
    next
      case (Gen p\<^sub>4 x\<^sub>4 y\<^sub>4 p\<^sub>5 x\<^sub>5 y\<^sub>5 p\<^sub>6 x\<^sub>6 y\<^sub>6 l')
      from \<open>on_curve a b p\<^sub>5\<close> \<open>opp p\<^sub>5 = p\<^sub>2\<close>
        \<open>p\<^sub>2 = Point x\<^sub>2 y\<^sub>2\<close> \<open>p\<^sub>5 = Point x\<^sub>5 y\<^sub>5\<close>
      have "y\<^sub>5 = - y\<^sub>2" "x\<^sub>5 = x\<^sub>2"
        by (auto simp add: opp_Point on_curve_def)
      from \<open>p\<^sub>4 = Point x\<^sub>3 y\<^sub>3\<close> \<open>p\<^sub>4 = Point x\<^sub>4 y\<^sub>4\<close>
      have "x\<^sub>4 = x\<^sub>3" "y\<^sub>4 = y\<^sub>3" by simp_all
      from \<open>x\<^sub>4 \<noteq> x\<^sub>5\<close> show ?case
        apply (simp add:
          \<open>y\<^sub>5 = - y\<^sub>2\<close> \<open>x\<^sub>5 = x\<^sub>2\<close>
          \<open>x\<^sub>4 = x\<^sub>3\<close> \<open>y\<^sub>4 = y\<^sub>3\<close>
          \<open>p\<^sub>6 = Point x\<^sub>6 y\<^sub>6\<close> \<open>p\<^sub>1 = Point x\<^sub>1 y\<^sub>1\<close>
          \<open>x\<^sub>6 = l' ^ 2 - x\<^sub>4 - x\<^sub>5\<close> \<open>y\<^sub>6 = - y\<^sub>4 - l' * (x\<^sub>6 - x\<^sub>4)\<close>
          \<open>l' = (y\<^sub>5 - y\<^sub>4) / (x\<^sub>5 - x\<^sub>4)\<close>
          \<open>x\<^sub>3 = l ^ 2 - x\<^sub>1 - x\<^sub>2\<close> \<open>y\<^sub>3 = - y\<^sub>1 - l * (x\<^sub>3 - x\<^sub>1)\<close>
          \<open>l = (y\<^sub>2 - y\<^sub>1) / (x\<^sub>2 - x\<^sub>1)\<close>)
        apply (rule conjI)
        apply field
        apply (rule conjI)
        apply (rule notI)
        apply (erule notE)
        apply (ring (prems))
        apply (rule sym)
        apply field
        apply (simp_all add: \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> [symmetric])
        apply field
        apply (rule conjI)
        apply (rule notI)
        apply (erule notE)
        apply (ring (prems))
        apply (rule sym)
        apply field
        apply (simp_all add: \<open>x\<^sub>1 \<noteq> x\<^sub>2\<close> [symmetric])
        done
    qed
  qed
qed

lemma add_shift_minus:
  assumes ab: "nonsingular a b"
  and p\<^sub>1: "on_curve a b p\<^sub>1"
  and p\<^sub>2: "on_curve a b p\<^sub>2"
  and p\<^sub>3: "on_curve a b p\<^sub>3"
  and eq: "add a p\<^sub>1 p\<^sub>2 = p\<^sub>3"
  shows "p\<^sub>1 = add a p\<^sub>3 (opp p\<^sub>2)"
proof -
  note eq
  also from add_minus_id [OF ab p\<^sub>3 opp_closed [OF p\<^sub>2]] p\<^sub>2
  have "p\<^sub>3 = add a (add a p\<^sub>3 (opp p\<^sub>2)) p\<^sub>2" by (simp add: opp_opp)
  finally have "add a p\<^sub>2 p\<^sub>1 = add a p\<^sub>2 (add a p\<^sub>3 (opp p\<^sub>2))"
    using p\<^sub>1 p\<^sub>2 p\<^sub>3
    by (simp add: add_comm [of a b] add_closed opp_closed)
  with ab p\<^sub>2 p\<^sub>1 add_closed [OF p\<^sub>3 opp_closed [OF p\<^sub>2]]
  show ?thesis by (rule cancel)
qed

lemma degen_assoc:
  assumes ab: "nonsingular a b"
  and p\<^sub>1: "on_curve a b p\<^sub>1"
  and p\<^sub>2: "on_curve a b p\<^sub>2"
  and p\<^sub>3: "on_curve a b p\<^sub>3"
  and H:
    "(p\<^sub>1 = Infinity \<or> p\<^sub>2 = Infinity \<or> p\<^sub>3 = Infinity) \<or>
     (p\<^sub>1 = opp p\<^sub>2 \<or> p\<^sub>2 = opp p\<^sub>3) \<or>
     (opp p\<^sub>1 = add a p\<^sub>2 p\<^sub>3 \<or> opp p\<^sub>3 = add a p\<^sub>1 p\<^sub>2)"
  shows "add a p\<^sub>1 (add a p\<^sub>2 p\<^sub>3) = add a (add a p\<^sub>1 p\<^sub>2) p\<^sub>3"
  using H
proof (elim disjE)
  assume "p\<^sub>1 = Infinity"
  then show ?thesis by (simp add: add_0_l)
next
  assume "p\<^sub>2 = Infinity"
  then show ?thesis by (simp add: add_0_l add_0_r)
next
  assume "p\<^sub>3 = Infinity"
  then show ?thesis by (simp add: add_0_r)
next
  assume "p\<^sub>1 = opp p\<^sub>2"
  from p\<^sub>2 p\<^sub>3
  have "add a (opp p\<^sub>2) (add a p\<^sub>2 p\<^sub>3) = add a (add a p\<^sub>3 p\<^sub>2) (opp p\<^sub>2)"
    by (simp add: add_comm [of a b] add_closed opp_closed)
  also from ab p\<^sub>3 p\<^sub>2 have "\<dots> = p\<^sub>3" by (rule add_minus_id)
  also have "\<dots> = add a Infinity p\<^sub>3" by (simp add: add_0_l)
  also from p\<^sub>2 have "\<dots> = add a (add a p\<^sub>2 (opp p\<^sub>2)) p\<^sub>3"
    by (simp add: add_opp)
  also from p\<^sub>2 have "\<dots> = add a (add a (opp p\<^sub>2) p\<^sub>2) p\<^sub>3"
    by (simp add: add_comm [of a b] opp_closed)
  finally show ?thesis using \<open>p\<^sub>1 = opp p\<^sub>2\<close> by simp
next
  assume "p\<^sub>2 = opp p\<^sub>3"
  from p\<^sub>3
  have "add a p\<^sub>1 (add a (opp p\<^sub>3) p\<^sub>3) = add a p\<^sub>1 (add a p\<^sub>3 (opp p\<^sub>3))"
    by (simp add: add_comm [of a b] opp_closed)
  also from ab p\<^sub>1 p\<^sub>3
  have "\<dots> = add a (add a p\<^sub>1 (opp p\<^sub>3)) (opp (opp p\<^sub>3))"
    by (simp add: add_opp add_minus_id add_0_r opp_closed)
  finally show ?thesis using p\<^sub>3 \<open>p\<^sub>2 = opp p\<^sub>3\<close>
    by (simp add: opp_opp)
next
  assume eq: "opp p\<^sub>1 = add a p\<^sub>2 p\<^sub>3"
  from eq [symmetric] p\<^sub>1
  have "add a p\<^sub>1 (add a p\<^sub>2 p\<^sub>3) = Infinity" by (simp add: add_opp)
  also from p\<^sub>3 have "\<dots> = add a p\<^sub>3 (opp p\<^sub>3)" by (simp add: add_opp)
  also from p\<^sub>3 have "\<dots> = add a (opp p\<^sub>3) p\<^sub>3"
    by (simp add: add_comm [of a b] opp_closed)
  also from ab p\<^sub>2 p\<^sub>3
  have "\<dots> = add a (add a (add a (opp p\<^sub>3) (opp p\<^sub>2)) (opp (opp p\<^sub>2))) p\<^sub>3"
    by (simp add: add_minus_id opp_closed)
  also from p\<^sub>2 p\<^sub>3
  have "\<dots> = add a (add a (add a (opp p\<^sub>2) (opp p\<^sub>3)) p\<^sub>2) p\<^sub>3"
    by (simp add: add_comm [of a b] opp_opp opp_closed)
  finally show ?thesis
    using opp_add [OF p\<^sub>2 p\<^sub>3] eq [symmetric] p\<^sub>1
    by (simp add: opp_opp)
next
  assume eq: "opp p\<^sub>3 = add a p\<^sub>1 p\<^sub>2"
  from opp_add [OF p\<^sub>1 p\<^sub>2] eq [symmetric] p\<^sub>3
  have "add a p\<^sub>1 (add a p\<^sub>2 p\<^sub>3) = add a p\<^sub>1 (add a p\<^sub>2 (add a (opp p\<^sub>1) (opp p\<^sub>2)))"
    by (simp add: opp_opp)
  also from p\<^sub>1 p\<^sub>2
  have "\<dots> = add a p\<^sub>1 (add a (add a (opp p\<^sub>1) (opp p\<^sub>2)) (opp (opp p\<^sub>2)))"
    by (simp add: add_comm [of a b] opp_opp add_closed opp_closed)
  also from ab p\<^sub>1 p\<^sub>2 have "\<dots> = Infinity"
    by (simp add: add_minus_id add_opp opp_closed)
  also from p\<^sub>3 have "\<dots> = add a p\<^sub>3 (opp p\<^sub>3)" by (simp add: add_opp)
  also from p\<^sub>3 have "\<dots> = add a (opp p\<^sub>3) p\<^sub>3"
    by (simp add: add_comm [of a b] opp_closed)
  finally show ?thesis using eq [symmetric] by simp
qed

lemma spec4_assoc:
  assumes ab: "nonsingular a b"
  and p\<^sub>1: "on_curve a b p\<^sub>1"
  and p\<^sub>2: "on_curve a b p\<^sub>2"
  shows "add a p\<^sub>1 (add a p\<^sub>2 p\<^sub>2) = add a (add a p\<^sub>1 p\<^sub>2) p\<^sub>2"
proof (cases "p\<^sub>1 = Infinity")
  case True
  from ab p\<^sub>1 p\<^sub>2 p\<^sub>2
  show ?thesis by (rule degen_assoc) (simp add: True)
next
  case False
  show ?thesis
  proof (cases "p\<^sub>2 = Infinity")
    case True
    from ab p\<^sub>1 p\<^sub>2 p\<^sub>2
    show ?thesis by (rule degen_assoc) (simp add: True)
  next
    case False
    show ?thesis
    proof (cases "p\<^sub>2 = opp p\<^sub>2")
      case True
      from ab p\<^sub>1 p\<^sub>2 p\<^sub>2
      show ?thesis by (rule degen_assoc) (simp add: True [symmetric])
    next
      case False
      show ?thesis
      proof (cases "p\<^sub>1 = opp p\<^sub>2")
        case True
        from ab p\<^sub>1 p\<^sub>2 p\<^sub>2
        show ?thesis by (rule degen_assoc) (simp add: True)
      next
        case False
        show ?thesis
        proof (cases "opp p\<^sub>1 = add a p\<^sub>2 p\<^sub>2")
          case True
          from ab p\<^sub>1 p\<^sub>2 p\<^sub>2
          show ?thesis by (rule degen_assoc) (simp add: True)
        next
          case False
          show ?thesis
          proof (cases "opp p\<^sub>2 = add a p\<^sub>1 p\<^sub>2")
            case True
            from ab p\<^sub>1 p\<^sub>2 p\<^sub>2
            show ?thesis by (rule degen_assoc) (simp add: True)
          next
            case False
            show ?thesis
            proof (cases "p\<^sub>1 = add a p\<^sub>2 p\<^sub>2")
              case True
              from p\<^sub>1 p\<^sub>2 \<open>p\<^sub>1 \<noteq> opp p\<^sub>2\<close> \<open>p\<^sub>2 \<noteq> opp p\<^sub>2\<close>
                \<open>opp p\<^sub>1 \<noteq> add a p\<^sub>2 p\<^sub>2\<close> \<open>opp p\<^sub>2 \<noteq> add a p\<^sub>1 p\<^sub>2\<close>
                \<open>p\<^sub>1 \<noteq> Infinity\<close> \<open>p\<^sub>2 \<noteq> Infinity\<close>
              show ?thesis
                apply (simp add: True)
                apply (rule spec3_assoc)
                apply (simp_all add: is_generic_def is_tangent_def)
                apply (rule notI)
                apply (drule uniq_zero [OF ab p\<^sub>2 p\<^sub>2])
                apply simp
                apply (intro conjI notI)
                apply (erule notE)
                apply (rule uniq_opp [of a])
                apply (simp add: add_comm [of a b] add_closed)
                apply (erule notE)
                apply (drule uniq_zero [OF ab add_closed [OF p\<^sub>2 p\<^sub>2] p\<^sub>2])
                apply simp
                done
            next
              case False
              show ?thesis
              proof (cases "p\<^sub>2 = add a p\<^sub>1 p\<^sub>2")
                case True
                from ab p\<^sub>1 p\<^sub>2 True [symmetric]
                have "p\<^sub>1 = Infinity" by (rule uniq_zero)
                then show ?thesis by (simp add: add_0_l)
              next
                case False
                show ?thesis
                proof (cases "p\<^sub>1 = p\<^sub>2")
                  case True
                  with p\<^sub>2 show ?thesis
                    by (simp add: add_comm [of a b] add_closed)
                next
                  case False
                  with p\<^sub>1 p\<^sub>2 \<open>p\<^sub>1 \<noteq> Infinity\<close> \<open>p\<^sub>2 \<noteq> Infinity\<close>
                    \<open>p\<^sub>1 \<noteq> opp p\<^sub>2\<close> \<open>p\<^sub>2 \<noteq> opp p\<^sub>2\<close>
                    \<open>p\<^sub>1 \<noteq> add a p\<^sub>2 p\<^sub>2\<close> \<open>p\<^sub>2 \<noteq> add a p\<^sub>1 p\<^sub>2\<close> \<open>opp p\<^sub>2 \<noteq> add a p\<^sub>1 p\<^sub>2\<close>
                  show ?thesis
                    apply (rule_tac spec2_assoc)
                    apply (simp_all add: is_generic_def is_tangent_def)
                    apply (rule notI)
                    apply (erule notE [of "p\<^sub>1 = opp p\<^sub>2"])
                    apply (rule uniq_opp [of a])
                    apply (simp add: add_comm)
                    apply (intro conjI notI)
                    apply (erule notE [of "p\<^sub>2 = opp p\<^sub>2"])
                    apply (rule uniq_opp)
                    apply assumption+
                    apply (rule notE [OF \<open>opp p\<^sub>1 \<noteq> add a p\<^sub>2 p\<^sub>2\<close>])
                    apply (simp add: opp_opp)
                    done
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma add_assoc:
  assumes ab: "nonsingular a b"
  and p\<^sub>1: "on_curve a b p\<^sub>1"
  and p\<^sub>2: "on_curve a b p\<^sub>2"
  and p\<^sub>3: "on_curve a b p\<^sub>3"
  shows "add a p\<^sub>1 (add a p\<^sub>2 p\<^sub>3) = add a (add a p\<^sub>1 p\<^sub>2) p\<^sub>3"
proof (cases "p\<^sub>1 = Infinity")
  case True
  from ab p\<^sub>1 p\<^sub>2 p\<^sub>3
  show ?thesis by (rule degen_assoc) (simp add: True)
next
  case False
  show ?thesis
  proof (cases "p\<^sub>2 = Infinity")
    case True
    from ab p\<^sub>1 p\<^sub>2 p\<^sub>3
    show ?thesis by (rule degen_assoc) (simp add: True)
  next
    case False
    show ?thesis
    proof (cases "p\<^sub>3 = Infinity")
      case True
      from ab p\<^sub>1 p\<^sub>2 p\<^sub>3
      show ?thesis by (rule degen_assoc) (simp add: True)
    next
      case False
      show ?thesis
      proof (cases "p\<^sub>1 = p\<^sub>2")
        case True
        from p\<^sub>2 p\<^sub>3
        have "add a p\<^sub>2 (add a p\<^sub>2 p\<^sub>3) = add a (add a p\<^sub>3 p\<^sub>2) p\<^sub>2"
          by (simp add: add_comm [of a b] add_closed)
        also from ab p\<^sub>3 p\<^sub>2 have "\<dots> = add a p\<^sub>3 (add a p\<^sub>2 p\<^sub>2)"
          by (simp add: spec4_assoc)
        also from p\<^sub>2 p\<^sub>3
        have "\<dots> = add a (add a p\<^sub>2 p\<^sub>2) p\<^sub>3"
          by (simp add: add_comm [of a b] add_closed)
        finally show ?thesis using True by simp
      next
        case False
        show ?thesis
        proof (cases "p\<^sub>1 = opp p\<^sub>2")
          case True
          from ab p\<^sub>1 p\<^sub>2 p\<^sub>3
          show ?thesis by (rule degen_assoc) (simp add: True)
        next
          case False
          show ?thesis
          proof (cases "p\<^sub>2 = p\<^sub>3")
            case True
            with ab p\<^sub>1 p\<^sub>3 show ?thesis
              by (simp add: spec4_assoc)
          next
            case False
            show ?thesis
            proof (cases "p\<^sub>2 = opp p\<^sub>3")
              case True
              from ab p\<^sub>1 p\<^sub>2 p\<^sub>3
              show ?thesis by (rule degen_assoc) (simp add: True)
            next
              case False
              show ?thesis
              proof (cases "opp p\<^sub>1 = add a p\<^sub>2 p\<^sub>3")
                case True
                from ab p\<^sub>1 p\<^sub>2 p\<^sub>3
                show ?thesis by (rule degen_assoc) (simp add: True)
              next
                case False
                show ?thesis
                proof (cases "opp p\<^sub>3 = add a p\<^sub>1 p\<^sub>2")
                  case True
                  from ab p\<^sub>1 p\<^sub>2 p\<^sub>3
                  show ?thesis by (rule degen_assoc) (simp add: True)
                next
                  case False
                  show ?thesis
                  proof (cases "p\<^sub>1 = add a p\<^sub>2 p\<^sub>3")
                    case True
                    with ab p\<^sub>2 p\<^sub>3 show ?thesis
                      apply simp
                      apply (rule cancel [OF ab opp_closed [OF p\<^sub>3]])
                      apply (simp_all add: add_closed)
                      apply (simp add: spec4_assoc add_closed opp_closed)
                      apply (simp add: add_comm [of a b "opp p\<^sub>3"]
                        add_closed opp_closed add_minus_id)
                      apply (simp add: add_comm [of a b] add_closed)
                      done
                  next
                    case False
                    show ?thesis
                    proof (cases "p\<^sub>3 = add a p\<^sub>1 p\<^sub>2")
                      case True
                      with ab p\<^sub>1 p\<^sub>2 show ?thesis
                        apply simp
                        apply (rule cancel [OF ab opp_closed [OF p\<^sub>1]])
                        apply (simp_all add: add_closed)
                        apply (simp add: spec4_assoc add_closed opp_closed)
                        apply (simp add: add_comm [of a b "opp p\<^sub>1"] add_comm [of a b p\<^sub>1]
                          add_closed opp_closed add_minus_id)
                        done
                    next
                      case False
                      with p\<^sub>1 p\<^sub>2 p\<^sub>3
                        \<open>p\<^sub>1 \<noteq> Infinity\<close> \<open>p\<^sub>2 \<noteq> Infinity\<close> \<open>p\<^sub>3 \<noteq> Infinity\<close>
                        \<open>p\<^sub>1 \<noteq> p\<^sub>2\<close> \<open>p\<^sub>1 \<noteq> opp p\<^sub>2\<close> \<open>p\<^sub>2 \<noteq> p\<^sub>3\<close> \<open>p\<^sub>2 \<noteq> opp p\<^sub>3\<close>
                        \<open>opp p\<^sub>3 \<noteq> add a p\<^sub>1 p\<^sub>2\<close> \<open>p\<^sub>1 \<noteq> add a p\<^sub>2 p\<^sub>3\<close>
                      show ?thesis
                        apply (rule_tac spec1_assoc [of a b])
                        apply (simp_all add: is_generic_def)
                        apply (rule notI)
                        apply (erule notE [of "p\<^sub>1 = opp p\<^sub>2"])
                        apply (rule uniq_opp [of a])
                        apply (simp add: add_comm)
                        apply (intro conjI notI)
                        apply (erule notE [of "p\<^sub>2 = opp p\<^sub>3"])
                        apply (rule uniq_opp [of a])
                        apply (simp add: add_comm)
                        apply (rule notE [OF \<open>opp p\<^sub>1 \<noteq> add a p\<^sub>2 p\<^sub>3\<close>])
                        apply (simp add: opp_opp)
                        done
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed
  
lemma add_comm':
  "nonsingular a b \<Longrightarrow>
   on_curve a b p\<^sub>1 \<Longrightarrow> on_curve a b p\<^sub>2 \<Longrightarrow> on_curve a b p\<^sub>3 \<Longrightarrow>
   add a p\<^sub>2 (add a p\<^sub>1 p\<^sub>3) = add a p\<^sub>1 (add a p\<^sub>2 p\<^sub>3)"
   by (simp add: add_assoc add_comm)

primrec (in ell_field) point_mult :: "'a \<Rightarrow> nat \<Rightarrow> 'a point \<Rightarrow> 'a point"
where
    "point_mult a 0 p = Infinity"
  | "point_mult a (Suc n) p = add a p (point_mult a n p)"

lemma point_mult_closed: "on_curve a b p \<Longrightarrow> on_curve a b (point_mult a n p)"
  by (induct n) (simp_all add: add_closed)

lemma point_mult_add:
  "on_curve a b p \<Longrightarrow> nonsingular a b \<Longrightarrow>
   point_mult a (m + n) p = add a (point_mult a m p) (point_mult a n p)"
  by (induct m) (simp_all add: add_assoc point_mult_closed add_0_l)

lemma point_mult_mult:
  "on_curve a b p \<Longrightarrow> nonsingular a b \<Longrightarrow>
   point_mult a (m * n) p = point_mult a n (point_mult a m p)"
   by (induct n) (simp_all add: point_mult_add)

lemma point_mult2_eq_double:
  "point_mult a 2 p = add a p p"
  by (simp add: numeral_2_eq_2 add_0_r)

subsection \<open>Projective Coordinates\<close>

type_synonym 'a ppoint = "'a \<times> 'a \<times> 'a"

context ell_field begin

definition pdouble :: "'a \<Rightarrow> 'a ppoint \<Rightarrow> 'a ppoint" where
  "pdouble a p =
     (let (x, y, z) = p
      in
        if z = 0 then p
        else
          let
            l = 2 * y * z;
            m = 3 * x ^ 2 + a * z ^ 2
          in
            (l * (m ^ 2 - 4 * x * y * l),
             m * (6 * x * y * l - m ^ 2) -
             2 * y ^ 2 * l ^ 2,
             l ^ 3))"

definition padd :: "'a \<Rightarrow> 'a ppoint \<Rightarrow> 'a ppoint \<Rightarrow> 'a ppoint" where
  "padd a p\<^sub>1 p\<^sub>2 =
     (let
        (x\<^sub>1, y\<^sub>1, z\<^sub>1) = p\<^sub>1;
        (x\<^sub>2, y\<^sub>2, z\<^sub>2) = p\<^sub>2
      in
        if z\<^sub>1 = 0 then p\<^sub>2
        else if z\<^sub>2 = 0 then p\<^sub>1
        else
          let
            d\<^sub>1 = x\<^sub>2 * z\<^sub>1;
            d\<^sub>2 = x\<^sub>1 * z\<^sub>2;
            l = d\<^sub>1 - d\<^sub>2;
            m = y\<^sub>2 * z\<^sub>1 - y\<^sub>1 * z\<^sub>2
          in
            if l = 0 then
              if m = 0 then pdouble a p\<^sub>1
              else (0, 0, 0)
            else
              let h = m ^ 2 * z\<^sub>1 * z\<^sub>2 - (d\<^sub>1 + d\<^sub>2) * l ^ 2
              in
                (l * h,
                 (d\<^sub>2 * l ^ 2 - h) * m - l ^ 3 * y\<^sub>1 * z\<^sub>2,
                 l ^ 3 * z\<^sub>1 * z\<^sub>2))"

definition make_affine :: "'a ppoint \<Rightarrow> 'a point" where
  "make_affine p =
     (let (x, y, z) = p
      in if z = 0 then Infinity else Point (x / z) (y / z))"

definition on_curvep :: "'a \<Rightarrow> 'a \<Rightarrow> 'a ppoint \<Rightarrow> bool" where
  "on_curvep a b = (\<lambda>(x, y, z). z \<noteq> 0 \<longrightarrow>
     y ^ 2 * z = x ^ 3 + a * x * z ^ 2 + b * z ^ 3)"

end

lemma on_curvep_infinity [simp]: "on_curvep a b (x, y, 0)"
  by (simp add: on_curvep_def)

lemma make_affine_infinity [simp]: "make_affine (x, y, 0) = Infinity"
  by (simp add: make_affine_def)

lemma on_curvep_iff_on_curve:
  "on_curvep a b p = on_curve a b (make_affine p)"
proof (induct p rule: prod_induct3)
  case (fields x y z)
  show "on_curvep a b (x, y, z) = on_curve a b (make_affine (x, y, z))"
  proof
    assume H: "on_curvep a b (x, y, z)"
    then have yz: "z \<noteq> 0 \<Longrightarrow> y ^ 2 * z = x ^ 3 + a * x * z ^ 2 + b * z ^ 3"
      by (simp_all add: on_curvep_def)
    show "on_curve a b (make_affine (x, y, z))"
    proof (cases "z = 0")
      case True
      then show ?thesis by (simp add: on_curve_def make_affine_def)
    next
      case False
      then show ?thesis
        apply (simp add: on_curve_def make_affine_def)
        apply (field yz [OF False])
        apply assumption
        done
    qed
  next
    assume H: "on_curve a b (make_affine (x, y, z))"
    show "on_curvep a b (x, y, z)"
    proof (cases "z = 0")
      case True
      then show ?thesis
        by (simp add: on_curvep_def)
    next
      case False
      from H show ?thesis
        apply (simp add: on_curve_def on_curvep_def make_affine_def False)
        apply (field (prems))
        apply field
        apply (simp_all add: False)
        done
    qed
  qed
qed

lemma pdouble_infinity [simp]: "pdouble a (x, y, 0) = (x, y, 0)"
  by (simp add: pdouble_def)

lemma padd_infinity_l [simp]: "padd a (x, y, 0) p = p"
  by (simp add: padd_def)

lemma pdouble_correct:
  "make_affine (pdouble a p) = add a (make_affine p) (make_affine p)"
proof (induct p rule: prod_induct3)
  case (fields x y z)
  then show ?case
    apply (auto simp add: add_def pdouble_def make_affine_def eq_opp_is_zero Let_def)
    apply field
    apply simp
    apply field
    apply simp
    done
qed

lemma padd_correct:
  assumes p\<^sub>1: "on_curvep a b p\<^sub>1" and p\<^sub>2: "on_curvep a b p\<^sub>2"
  shows "make_affine (padd a p\<^sub>1 p\<^sub>2) = add a (make_affine p\<^sub>1) (make_affine p\<^sub>2)"
  using p\<^sub>1
proof (induct p\<^sub>1 rule: prod_induct3)
  case (fields x\<^sub>1 y\<^sub>1 z\<^sub>1)
  note p\<^sub>1' = fields
  from p\<^sub>2 show ?case
  proof (induct p\<^sub>2 rule: prod_induct3)
    case (fields x\<^sub>2 y\<^sub>2 z\<^sub>2)
    then have
      yz\<^sub>2: "z\<^sub>2 \<noteq> 0 \<Longrightarrow> y\<^sub>2 ^ 2 * z\<^sub>2 * z\<^sub>1 ^ 3 =
        (x\<^sub>2 ^ 3 + a * x\<^sub>2 * z\<^sub>2 ^ 2 + b * z\<^sub>2 ^ 3) * z\<^sub>1 ^ 3"
      by (simp_all add: on_curvep_def)
    from p\<^sub>1' have
      yz\<^sub>1: "z\<^sub>1 \<noteq> 0 \<Longrightarrow> y\<^sub>1 ^ 2 * z\<^sub>1 * z\<^sub>2 ^ 3 =
        (x\<^sub>1 ^ 3 + a * x\<^sub>1 * z\<^sub>1 ^ 2 + b * z\<^sub>1 ^ 3) * z\<^sub>2 ^ 3"
      by (simp_all add: on_curvep_def)
    show ?case
    proof (cases "z\<^sub>1 = 0")
      case True
      then show ?thesis
        by (simp add: add_def padd_def make_affine_def)
    next
      case False
      show ?thesis
      proof (cases "z\<^sub>2 = 0")
        case True
        then show ?thesis
          by (simp add: add_def padd_def make_affine_def)
      next
        case False
        show ?thesis
        proof (cases "x\<^sub>2 * z\<^sub>1 - x\<^sub>1 * z\<^sub>2 = 0")
          case True
          note x = this
          then have x': "x\<^sub>2 * z\<^sub>1 = x\<^sub>1 * z\<^sub>2" by simp
          show ?thesis
          proof (cases "y\<^sub>2 * z\<^sub>1 - y\<^sub>1 * z\<^sub>2 = 0")
            case True
            then have y: "y\<^sub>2 * z\<^sub>1 = y\<^sub>1 * z\<^sub>2" by simp
            from \<open>z\<^sub>1 \<noteq> 0\<close> \<open>z\<^sub>2 \<noteq> 0\<close> x
            have "make_affine (x\<^sub>2, y\<^sub>2, z\<^sub>2) = make_affine (x\<^sub>1, y\<^sub>1, z\<^sub>1)"
              apply (simp add: make_affine_def)
              apply (rule conjI)
              apply (field x')
              apply simp
              apply (field y)
              apply simp
              done
            with True x \<open>z\<^sub>1 \<noteq> 0\<close> \<open>z\<^sub>2 \<noteq> 0\<close> p\<^sub>1' fields show ?thesis
              by (simp add: padd_def pdouble_correct)
          next
            case False
            have "y\<^sub>2 ^ 2 * z\<^sub>1 ^ 3 * z\<^sub>2 = y\<^sub>1 ^ 2 * z\<^sub>1 * z\<^sub>2 ^ 3"
              by (ring yz\<^sub>1 [OF \<open>z\<^sub>1 \<noteq> 0\<close>] yz\<^sub>2 [OF \<open>z\<^sub>2 \<noteq> 0\<close>] x')
            then have "y\<^sub>2 ^ 2 * z\<^sub>1 ^ 3 * z\<^sub>2 / z\<^sub>1 / z\<^sub>2 =
              y\<^sub>1 ^ 2 * z\<^sub>1 * z\<^sub>2 ^ 3 / z\<^sub>1 / z\<^sub>2"
              by simp
            then have "(y\<^sub>2 * z\<^sub>1) * (y\<^sub>2 * z\<^sub>1) = (y\<^sub>1 * z\<^sub>2) * (y\<^sub>1 * z\<^sub>2)"
              apply (field (prems))
              apply (field)
              apply (rule TrueI)
              apply (simp add: \<open>z\<^sub>1 \<noteq> 0\<close> \<open>z\<^sub>2 \<noteq> 0\<close>)
              done
            with False
            have y\<^sub>2z\<^sub>1: "y\<^sub>2 * z\<^sub>1 = - (y\<^sub>1 * z\<^sub>2)"
              by (simp add: square_eq_iff)
            from x False \<open>z\<^sub>1 \<noteq> 0\<close> \<open>z\<^sub>2 \<noteq> 0\<close> show ?thesis
              apply (simp add: padd_def add_def make_affine_def Let_def)
              apply (rule conjI)
              apply (rule impI)
              apply (field x')
              apply simp
              apply (field y\<^sub>2z\<^sub>1)
              apply simp
              done
          qed
        next
          case False
          then have "x\<^sub>1 / z\<^sub>1 \<noteq> x\<^sub>2 / z\<^sub>2"
            apply (rule_tac notI)
            apply (erule notE)
            apply (drule sym)
            apply (field (prems))
            apply ring
            apply (simp add: \<open>z\<^sub>1 \<noteq> 0\<close> \<open>z\<^sub>2 \<noteq> 0\<close>)
            done
          with False \<open>z\<^sub>1 \<noteq> 0\<close> \<open>z\<^sub>2 \<noteq> 0\<close>
          show ?thesis
            apply (auto simp add: padd_def add_def make_affine_def Let_def)
            apply field
            apply simp
            apply field
            apply simp
            done
        qed
      qed
    qed
  qed
qed

lemma pdouble_closed:
  "on_curvep a b p \<Longrightarrow> on_curvep a b (pdouble a p)"
  by (simp add: on_curvep_iff_on_curve pdouble_correct add_closed)

lemma padd_closed:
  "on_curvep a b p\<^sub>1 \<Longrightarrow> on_curvep a b p\<^sub>2 \<Longrightarrow> on_curvep a b (padd a p\<^sub>1 p\<^sub>2)"
  by (simp add: on_curvep_iff_on_curve padd_correct add_closed)

primrec (in ell_field) ppoint_mult :: "'a \<Rightarrow> nat \<Rightarrow> 'a ppoint \<Rightarrow> 'a ppoint"
where
    "ppoint_mult a 0 p = (0, 0, 0)"
  | "ppoint_mult a (Suc n) p = padd a p (ppoint_mult a n p)"

lemma ppoint_mult_closed [simp]:
  "on_curvep a b p \<Longrightarrow> on_curvep a b (ppoint_mult a n p)"
  by (induct n) (simp_all add: padd_closed)

lemma ppoint_mult_correct: "on_curvep a b p \<Longrightarrow>
  make_affine (ppoint_mult a n p) = point_mult a n (make_affine p)"
  by (induct n) (simp_all add: padd_correct)

context ell_field begin

definition proj_eq :: "'a ppoint \<Rightarrow> 'a ppoint \<Rightarrow> bool" where
  "proj_eq = (\<lambda>(x\<^sub>1, y\<^sub>1, z\<^sub>1) (x\<^sub>2, y\<^sub>2, z\<^sub>2).
     (z\<^sub>1 = 0) = (z\<^sub>2 = 0) \<and> x\<^sub>1 * z\<^sub>2 = x\<^sub>2 * z\<^sub>1 \<and> y\<^sub>1 * z\<^sub>2 = y\<^sub>2 * z\<^sub>1)"

end

lemma proj_eq_refl: "proj_eq p p"
  by (auto simp add: proj_eq_def)

lemma proj_eq_sym: "proj_eq p p' \<Longrightarrow> proj_eq p' p"
  by (auto simp add: proj_eq_def)

lemma proj_eq_trans:
  "in_carrierp p \<Longrightarrow> in_carrierp p' \<Longrightarrow> in_carrierp p'' \<Longrightarrow>
   proj_eq p p' \<Longrightarrow> proj_eq p' p'' \<Longrightarrow> proj_eq p p''"
proof (induct p rule: prod_induct3)
  case (fields x y z)
  then show ?case
  proof (induct p' rule: prod_induct3)
    case (fields x' y' z')
    then show ?case
    proof (induct p'' rule: prod_induct3)
      case (fields x'' y'' z'')
      then have
        z: "(z = 0) = (z' = 0)" "(z' = 0) = (z'' = 0)" and
        "x * z' * z'' = x' * z * z''"
        "y * z' * z'' = y' * z * z''"
        and xy:
        "x' * z'' = x'' * z'"
        "y' * z'' = y'' * z'"
        by (simp_all add: proj_eq_def)
      from \<open>x * z' * z'' = x' * z * z''\<close>
      have "(x * z'') * z' = (x'' * z) * z'"
        by (ring (prems) xy) (ring xy)
      moreover from \<open>y * z' * z'' = y' * z * z''\<close>
      have "(y * z'') * z' = (y'' * z) * z'"
        by (ring (prems) xy) (ring xy)
      ultimately show ?case using z
        by (auto simp add: proj_eq_def)
    qed
  qed
qed

lemma make_affine_proj_eq_iff:
  "proj_eq p p' = (make_affine p = make_affine p')"
proof (induct p rule: prod_induct3)
  case (fields x y z)
  then show ?case
  proof (induct p' rule: prod_induct3)
    case (fields x' y' z')
    show ?case
    proof
      assume "proj_eq (x, y, z) (x', y', z')"
      then have "(z = 0) = (z' = 0)"
        and xy: "x * z' = x' * z" "y * z' = y' * z"
        by (simp_all add: proj_eq_def)
      then show "make_affine (x, y, z) = make_affine (x', y', z')"
        apply (auto simp add: make_affine_def)
        apply (field xy)
        apply simp
        apply (field xy)
        apply simp
        done
    next
      assume H: "make_affine (x, y, z) = make_affine (x', y', z')"
      show "proj_eq (x, y, z) (x', y', z')"
      proof (cases "z = 0")
        case True
        with H have "z' = 0" by (simp add: make_affine_def split: if_split_asm)
        with True show ?thesis by (simp add: proj_eq_def)
      next
        case False
        with H have "z' \<noteq> 0" "x / z = x' / z'" "y / z = y' / z'"
          by (simp_all add: make_affine_def split: if_split_asm)
        from \<open>x / z = x' / z'\<close>
        have "x * z' = x' * z"
          apply (field (prems))
          apply field
          apply (simp_all add: \<open>z \<noteq> 0\<close> \<open>z' \<noteq> 0\<close>)
          done
        moreover from \<open>y / z = y' / z'\<close>
        have "y * z' = y' * z"
          apply (field (prems))
          apply field
          apply (simp_all add: \<open>z \<noteq> 0\<close> \<open>z' \<noteq> 0\<close>)
          done
        ultimately show ?thesis
          by (simp add: proj_eq_def \<open>z \<noteq> 0\<close> \<open>z' \<noteq> 0\<close>)
      qed
    qed
  qed
qed

lemma pdouble_proj_eq_cong:
  "proj_eq p p' \<Longrightarrow> proj_eq (pdouble a p) (pdouble a p')"
  by (simp add: make_affine_proj_eq_iff pdouble_correct)

lemma padd_proj_eq_cong:
  "on_curvep a b p\<^sub>1 \<Longrightarrow> on_curvep a b p\<^sub>1' \<Longrightarrow> on_curvep a b p\<^sub>2 \<Longrightarrow> on_curvep a b p\<^sub>2' \<Longrightarrow>
   proj_eq p\<^sub>1 p\<^sub>1' \<Longrightarrow> proj_eq p\<^sub>2 p\<^sub>2' \<Longrightarrow> proj_eq (padd a p\<^sub>1 p\<^sub>2) (padd a p\<^sub>1' p\<^sub>2')"
  by (simp add: make_affine_proj_eq_iff padd_correct)

end
