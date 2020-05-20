section\<open>Poincar\'e disc model types\<close>

text \<open>In this section we introduce datatypes that represent objects in the Poincar\'e disc model.
The types are defined as subtypes (e.g., the h-points are defined as elements of $\mathbb{C}P^1$
that lie within the unit disc). The functions on those types are defined by lifting the functions
defined on the carrier type (e.g., h-distance is defined by lifting the distance function defined
for elements of $\mathbb{C}P^1$).\<close>

theory Poincare
imports Poincare_Lines Poincare_Between Poincare_Distance Poincare_Circles
begin

(* ------------------------------------------------------------------ *)
subsection \<open>H-points\<close>
(* ------------------------------------------------------------------ *)

typedef p_point = "{z. z \<in> unit_disc}"
  using zero_in_unit_disc
  by (rule_tac x="0\<^sub>h" in exI, simp)

setup_lifting type_definition_p_point

text \<open>Point zero\<close>
lift_definition p_zero :: "p_point" is "0\<^sub>h"
  by (rule zero_in_unit_disc)

text \<open>Constructing h-points from complex numbers\<close>
lift_definition p_of_complex :: "complex \<Rightarrow> p_point" is "\<lambda> z. if cmod z < 1 then of_complex z else 0\<^sub>h"
  by auto

(* ------------------------------------------------------------------ *)
subsection \<open>H-lines\<close>
(* ------------------------------------------------------------------ *)

typedef p_line = "{H. is_poincare_line H}"
  by (rule_tac x="x_axis" in exI, simp)

setup_lifting type_definition_p_line

lift_definition p_incident :: "p_line \<Rightarrow> p_point \<Rightarrow> bool" is on_circline
  done

text \<open>Set of h-points on an h-line\<close>
definition p_points :: "p_line \<Rightarrow> p_point set" where
  "p_points l = {p. p_incident l p}"

text \<open>x-axis is an example of an h-line\<close>
lift_definition p_x_axis :: "p_line" is x_axis
  by simp

text \<open>Constructing the unique h-line from two h-points\<close>
lift_definition p_line :: "p_point \<Rightarrow> p_point \<Rightarrow> p_line" is poincare_line
proof-
  fix u v
  show "is_poincare_line (poincare_line u v)"
  proof (cases "u \<noteq> v")
    case True
    thus ?thesis
      by simp
  next
    text\<open>This branch must work only for formal reasons.\<close>
    case False
    thus ?thesis
      by (transfer, transfer, auto simp add: hermitean_def mat_adj_def mat_cnj_def split: if_split_asm)
  qed
qed

text \<open>Next we show how to lift some lemmas. This could be done for all the lemmas that we have
proved earlier, but we do not do that.\<close>

text \<open>If points are different then the constructed line contains the starting points\<close>
lemma p_on_line:
  assumes "z \<noteq> w"
  shows "p_incident (p_line z w) z"
        "p_incident (p_line z w) w"
  using assms
  by (transfer, simp)+

text \<open>There is a unique h-line passing trough the two different given h-points\<close>
lemma
  assumes "u \<noteq> v"
  shows "\<exists>! l. {u, v} \<subseteq> p_points l"
  using assms
  apply (rule_tac a="p_line u v" in ex1I, auto simp add: p_points_def p_on_line)
  apply (transfer, simp add: unique_poincare_line)
  done

text \<open>The unique h-line trough zero and a non-zero h-point on the x-axis is the x-axis\<close>
lemma
  assumes "p_zero \<in> p_points l" "u \<in> p_points l" "u \<noteq> p_zero" "u \<in> p_points p_x_axis"
  shows "l = p_x_axis"
  using assms
  unfolding p_points_def
  apply simp
  apply transfer
  using is_poincare_line_0_real_is_x_axis inf_notin_unit_disc
  unfolding circline_set_def
  by blast

(* ------------------------------------------------------------------ *)
subsection \<open>H-collinearity\<close>
(* ------------------------------------------------------------------ *)

lift_definition p_collinear :: "p_point set \<Rightarrow> bool" is poincare_collinear
  done

(* ------------------------------------------------------------------ *)
subsection \<open>H-isometries\<close>
(* ------------------------------------------------------------------ *)

text \<open>H-isometries are functions that map the unit disc onto itself\<close>
typedef p_isometry = "{f. unit_disc_fix_f f}"
  by (rule_tac x="id" in exI, simp add: unit_disc_fix_f_def, rule_tac x="id_moebius" in exI, simp)

setup_lifting type_definition_p_isometry

text \<open>Action of an h-isometry on an h-point\<close>
lift_definition p_isometry_pt :: "p_isometry \<Rightarrow> p_point \<Rightarrow> p_point" is "\<lambda> f p. f p"
  using unit_disc_fix_f_unit_disc
  by auto

text \<open>Action of an h-isometry on an h-line\<close>
lift_definition p_isometry_line :: "p_isometry \<Rightarrow> p_line \<Rightarrow> p_line" is "\<lambda> f l. unit_disc_fix_f_circline f l"
proof-
  fix f H
  assume "unit_disc_fix_f f" "is_poincare_line H"
  then obtain M where "unit_disc_fix M" and *: "f = moebius_pt M \<or> f = moebius_pt M \<circ> conjugate"
    unfolding unit_disc_fix_f_def
    by auto
  show "is_poincare_line (unit_disc_fix_f_circline f H)"
    using *
  proof
    assume "f = moebius_pt M"
    thus ?thesis
      using \<open>unit_disc_fix M\<close> \<open>is_poincare_line H\<close>
      using unit_disc_fix_f_circline_direct[of M f H]
      by auto
  next
    assume "f = moebius_pt M \<circ> conjugate"
    thus ?thesis
      using \<open>unit_disc_fix M\<close> \<open>is_poincare_line H\<close>
      using unit_disc_fix_f_circline_indirect[of M f H]
      by auto
  qed
qed

text \<open>An example lemma about h-isometries.\<close>

text \<open>H-isometries preserve h-collinearity\<close>
lemma p_collinear_p_isometry_pt [simp]: 
  shows "p_collinear (p_isometry_pt M ` A) \<longleftrightarrow> p_collinear A"
proof-
  have *: "\<forall> M A.  ((\<lambda>x. moebius_pt M (conjugate x)) ` A = moebius_pt M ` (conjugate ` A))"
    by auto
  show ?thesis
    by transfer (auto simp add: unit_disc_fix_f_def *)
qed

(* ------------------------------------------------------------------ *)
subsection \<open>H-distance and h-congruence\<close>
(* ------------------------------------------------------------------ *)

lift_definition p_dist :: "p_point \<Rightarrow> p_point \<Rightarrow> real" is poincare_distance
  done

definition p_congruent :: "p_point \<Rightarrow> p_point \<Rightarrow> p_point \<Rightarrow> p_point \<Rightarrow> bool" where
  [simp]: "p_congruent u v u' v' \<longleftrightarrow> p_dist u v = p_dist u' v'"

lemma
  assumes "p_dist u v = p_dist u' v'"
  assumes "p_dist v w = p_dist v' w'"
  assumes "p_dist u w = p_dist u' w'"
  shows "\<exists> f. p_isometry_pt f u = u' \<and> p_isometry_pt f v = v' \<and> p_isometry_pt f w = w'"
  using assms
  apply transfer
  using unit_disc_fix_f_congruent_triangles
  by auto

text\<open>We prove that unit disc equipped with Poincar\'e distance is a metric space, i.e. an
instantiation of @{term metric_space} locale.\<close>

instantiation p_point :: metric_space
begin
definition "dist_p_point = p_dist"
definition "(uniformity_p_point :: (p_point \<times> p_point) filter) = (INF e\<in>{0<..}. principal {(x, y). dist_class.dist x y < e})"
definition "open_p_point (U :: p_point set) = (\<forall> x \<in> U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"
instance
proof
  fix x y :: p_point
  show "(dist_class.dist x y = 0) = (x = y)"
    unfolding dist_p_point_def
    by (transfer, simp add: poincare_distance_eq_0_iff)
next
  fix x y z :: p_point
  show "dist_class.dist x y \<le> dist_class.dist x z + dist_class.dist y z"
    unfolding dist_p_point_def                 
    apply transfer
    using poincare_distance_triangle_inequality poincare_distance_sym
    by metis
qed (simp_all add: open_p_point_def uniformity_p_point_def)
end                                                                       

(* ------------------------------------------------------------------ *)
subsection \<open>H-betweennes\<close>
(* ------------------------------------------------------------------ *)

lift_definition p_between :: "p_point \<Rightarrow> p_point \<Rightarrow> p_point \<Rightarrow> bool" is poincare_between
  done

end                                                                                                  
