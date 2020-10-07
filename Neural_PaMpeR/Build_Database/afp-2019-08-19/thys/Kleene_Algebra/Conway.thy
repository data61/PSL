(* Title:      Conway Algebra
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Conway Algebras\<close>

theory Conway
  imports Dioid
begin

text \<open>
  We define a weak regular algebra which can serve as a common basis for Kleene algebra and demonic reginement algebra.
  It is closely related to an axiomatisation given by Conway~\cite{conway71regular}. 
\<close>

class dagger_op =
  fixes dagger :: "'a \<Rightarrow> 'a" ("_\<^sup>\<dagger>" [101] 100)

subsection\<open>Near Conway Algebras\<close>

class near_conway_base = near_dioid_one + dagger_op +
  assumes dagger_denest: "(x + y)\<^sup>\<dagger> = (x\<^sup>\<dagger> \<cdot> y)\<^sup>\<dagger> \<cdot> x\<^sup>\<dagger>"
  and dagger_prod_unfold [simp]: "1 + x \<cdot> (y \<cdot> x)\<^sup>\<dagger> \<cdot> y = (x \<cdot> y)\<^sup>\<dagger>"

begin

lemma dagger_unfoldl_eq [simp]: "1 + x \<cdot> x\<^sup>\<dagger> = x\<^sup>\<dagger>"
  by (metis dagger_prod_unfold mult_1_left mult_1_right)

lemma dagger_unfoldl: "1 + x \<cdot> x\<^sup>\<dagger> \<le> x\<^sup>\<dagger>"
  by auto

lemma dagger_unfoldr_eq [simp]: "1 + x\<^sup>\<dagger> \<cdot> x = x\<^sup>\<dagger>"
  by (metis dagger_prod_unfold mult_1_right mult_1_left)

lemma dagger_unfoldr: "1 + x\<^sup>\<dagger> \<cdot> x \<le> x\<^sup>\<dagger>"
  by auto

lemma dagger_unfoldl_distr [simp]: "y + x \<cdot> x\<^sup>\<dagger> \<cdot> y = x\<^sup>\<dagger> \<cdot> y"
  by (metis distrib_right' mult_1_left dagger_unfoldl_eq)

lemma dagger_unfoldr_distr [simp]: "y + x\<^sup>\<dagger> \<cdot> x \<cdot> y = x\<^sup>\<dagger> \<cdot> y"
  by (metis dagger_unfoldr_eq distrib_right' mult_1_left mult.assoc)

lemma dagger_refl: "1 \<le> x\<^sup>\<dagger>"
  using dagger_unfoldl local.join.sup.bounded_iff by blast

lemma dagger_plus_one [simp]: "1 + x\<^sup>\<dagger> = x\<^sup>\<dagger>"
  by (simp add: dagger_refl local.join.sup_absorb2)

lemma star_1l: "x \<cdot> x\<^sup>\<dagger> \<le> x\<^sup>\<dagger>"
  using dagger_unfoldl local.join.sup.bounded_iff by blast

lemma star_1r: "x\<^sup>\<dagger> \<cdot> x \<le> x\<^sup>\<dagger>"
  using dagger_unfoldr local.join.sup.bounded_iff by blast

lemma dagger_ext: "x \<le> x\<^sup>\<dagger>"
  by (metis dagger_unfoldl_distr local.join.sup.boundedE star_1r)

lemma dagger_trans_eq [simp]: "x\<^sup>\<dagger> \<cdot> x\<^sup>\<dagger> = x\<^sup>\<dagger>"
  by (metis dagger_unfoldr_eq local.dagger_denest local.join.sup.idem mult_assoc)

lemma dagger_subdist:  "x\<^sup>\<dagger> \<le> (x + y)\<^sup>\<dagger>"
  by (metis dagger_unfoldr_distr local.dagger_denest local.order_prop)

lemma dagger_subdist_var:  "x\<^sup>\<dagger> + y\<^sup>\<dagger> \<le> (x + y)\<^sup>\<dagger>"
  using dagger_subdist local.join.sup_commute by fastforce

lemma dagger_iso [intro]: "x \<le> y \<Longrightarrow> x\<^sup>\<dagger> \<le> y\<^sup>\<dagger>"
  by (metis less_eq_def dagger_subdist)

lemma star_square: "(x \<cdot> x)\<^sup>\<dagger> \<le> x\<^sup>\<dagger>"
  by (metis dagger_plus_one dagger_subdist dagger_trans_eq dagger_unfoldr_distr local.dagger_denest local.distrib_right' local.eq_iff  local.join.sup_commute local.less_eq_def  local.mult_onel mult_assoc)

lemma dagger_rtc1_eq [simp]: "1 + x + x\<^sup>\<dagger> \<cdot> x\<^sup>\<dagger> = x\<^sup>\<dagger>"
  by (simp add: local.dagger_ext local.dagger_refl local.join.sup_absorb2)

text \<open>Nitpick refutes the next lemmas.\<close>

lemma " y + y \<cdot> x\<^sup>\<dagger> \<cdot> x = y \<cdot> x\<^sup>\<dagger>"
(*nitpick [expect=genuine]*)
  oops

lemma "y \<cdot> x\<^sup>\<dagger> = y + y \<cdot> x \<cdot> x\<^sup>\<dagger>"
(*nitpick [expect=genuine]*)
  oops

lemma "(x + y)\<^sup>\<dagger> = x\<^sup>\<dagger> \<cdot> (y \<cdot> x\<^sup>\<dagger>)\<^sup>\<dagger>"
(*nitpick [expect=genuine]*)
  oops

lemma "(x\<^sup>\<dagger>)\<^sup>\<dagger> = x\<^sup>\<dagger>"
(*nitpick [expect=genuine]*)
oops

lemma "(1 + x)\<^sup>\<star> = x\<^sup>\<star>"
(*nitpick [expect = genuine]*)
oops

lemma "x\<^sup>\<dagger> \<cdot> x = x \<cdot> x\<^sup>\<dagger>"
(*nitpick [expect=genuine]*)
oops

end

subsection\<open>Pre-Conway Algebras\<close>

class pre_conway_base = near_conway_base + pre_dioid_one

begin

lemma dagger_subdist_var_3: "x\<^sup>\<dagger> \<cdot> y\<^sup>\<dagger> \<le> (x + y)\<^sup>\<dagger>"
  using local.dagger_subdist_var local.mult_isol_var by fastforce

lemma dagger_subdist_var_2: "x \<cdot> y \<le> (x + y)\<^sup>\<dagger>"
  by (meson dagger_subdist_var_3 local.dagger_ext local.mult_isol_var local.order.trans)

lemma dagger_sum_unfold [simp]: "x\<^sup>\<dagger> + x\<^sup>\<dagger> \<cdot> y \<cdot> (x + y)\<^sup>\<dagger> = (x + y)\<^sup>\<dagger>"
  by (metis local.dagger_denest local.dagger_unfoldl_distr mult_assoc)

end

subsection \<open>Conway Algebras\<close>

class conway_base = pre_conway_base + dioid_one

begin

lemma troeger: "(x + y)\<^sup>\<dagger> \<cdot> z = x\<^sup>\<dagger> \<cdot> (y \<cdot> (x + y)\<^sup>\<dagger> \<cdot> z + z)"
proof -
  have "(x + y)\<^sup>\<dagger> \<cdot> z = x\<^sup>\<dagger> \<cdot> z + x\<^sup>\<dagger> \<cdot> y \<cdot> (x + y)\<^sup>\<dagger> \<cdot> z"
    by (metis dagger_sum_unfold local.distrib_right')
  thus ?thesis
   by (metis add_commute local.distrib_left mult_assoc)
qed

lemma dagger_slide_var1: "x\<^sup>\<dagger> \<cdot> x \<le> x \<cdot> x\<^sup>\<dagger>"
  by (metis local.dagger_unfoldl_distr local.dagger_unfoldr_eq local.distrib_left local.eq_iff local.mult_1_right mult_assoc)

lemma dagger_slide_var1_eq: "x\<^sup>\<dagger> \<cdot> x = x \<cdot> x\<^sup>\<dagger>"
  by (metis local.dagger_unfoldl_distr local.dagger_unfoldr_eq local.distrib_left local.mult_1_right mult_assoc)

lemma dagger_slide_eq: "(x \<cdot> y)\<^sup>\<dagger> \<cdot> x = x \<cdot> (y \<cdot> x)\<^sup>\<dagger>"
proof -
  have "(x \<cdot> y)\<^sup>\<dagger> \<cdot> x = x + x \<cdot> (y \<cdot> x)\<^sup>\<dagger> \<cdot> y \<cdot> x"
    by (metis local.dagger_prod_unfold local.distrib_right' local.mult_onel)
  also have "... = x \<cdot> (1 + (y \<cdot> x)\<^sup>\<dagger> \<cdot> y \<cdot> x)"
    using local.distrib_left local.mult_1_right mult_assoc by presburger
  finally show ?thesis
    by (simp add: mult_assoc)
qed

end

subsection \<open>Conway Algebras with  Zero\<close>

class near_conway_base_zerol = near_conway_base + near_dioid_one_zerol

begin

lemma dagger_annil [simp]: "1 + x \<cdot> 0 = (x \<cdot> 0)\<^sup>\<dagger>"
  by (metis annil dagger_unfoldl_eq mult.assoc)

lemma zero_dagger [simp]: "0\<^sup>\<dagger> = 1"
  by (metis add_0_right annil dagger_annil)

end

class pre_conway_base_zerol = near_conway_base_zerol + pre_dioid

class conway_base_zerol = pre_conway_base_zerol + dioid

subclass (in pre_conway_base_zerol) pre_conway_base ..

subclass (in conway_base_zerol) conway_base ..

context conway_base_zerol
begin

lemma "z \<cdot> x \<le> y \<cdot> z \<Longrightarrow> z \<cdot> x\<^sup>\<dagger> \<le> y\<^sup>\<dagger> \<cdot> z"
(*nitpick [expect=genuine]*)
oops 

end

subsection \<open>Conway Algebras with Simulation\<close>

class near_conway = near_conway_base +
  assumes dagger_simr: "z \<cdot> x \<le> y \<cdot> z \<Longrightarrow> z \<cdot> x\<^sup>\<dagger> \<le> y\<^sup>\<dagger> \<cdot> z"

begin

lemma dagger_slide_var: "x \<cdot> (y \<cdot> x)\<^sup>\<dagger> \<le> (x \<cdot> y)\<^sup>\<dagger> \<cdot> x"
  by (metis eq_refl dagger_simr mult.assoc)

text \<open>Nitpick refutes the next lemma.\<close>

lemma dagger_slide: "x \<cdot> (y \<cdot> x)\<^sup>\<dagger> = (x \<cdot> y)\<^sup>\<dagger> \<cdot> x"
(*nitpick [expect=genuine]*)
  oops

text \<open>
  We say that $y$ preserves $x$ if $x \cdot y \cdot x = x \cdot y$ and $!x \cdot y \cdot !x = !x \cdot y$. This definition is taken
  from Solin~\cite{Solin11}. It is useful for program transformation.
\<close>
  
lemma preservation1: "x \<cdot> y \<le> x \<cdot> y \<cdot> x \<Longrightarrow> x \<cdot> y\<^sup>\<dagger> \<le> (x \<cdot> y + z)\<^sup>\<dagger> \<cdot> x"
proof -
  assume "x \<cdot> y \<le> x \<cdot> y \<cdot> x"
  hence "x \<cdot> y \<le> (x \<cdot> y + z) \<cdot> x"
    by (simp add: local.join.le_supI1)
  thus ?thesis
    by (simp add: local.dagger_simr)
qed

end

class near_conway_zerol = near_conway + near_dioid_one_zerol

class pre_conway = near_conway + pre_dioid_one

begin

subclass pre_conway_base ..

lemma dagger_slide: "x \<cdot> (y \<cdot> x)\<^sup>\<dagger> = (x \<cdot> y)\<^sup>\<dagger> \<cdot> x"
  by (metis add.commute dagger_prod_unfold join.sup_least mult_1_right mult.assoc subdistl dagger_slide_var dagger_unfoldl_distr antisym)

lemma dagger_denest2: "(x + y)\<^sup>\<dagger> = x\<^sup>\<dagger> \<cdot> (y \<cdot> x\<^sup>\<dagger>)\<^sup>\<dagger>"
  by (metis dagger_denest dagger_slide)

lemma preservation2: "y \<cdot> x \<le> y \<Longrightarrow> (x \<cdot> y)\<^sup>\<dagger> \<cdot> x \<le> x \<cdot> y\<^sup>\<dagger>"
  by (metis dagger_slide local.dagger_iso local.mult_isol)

lemma preservation1_eq: "x \<cdot> y \<le> x \<cdot> y \<cdot> x \<Longrightarrow> y \<cdot> x \<le> y \<Longrightarrow> (x \<cdot> y)\<^sup>\<dagger> \<cdot> x = x \<cdot> y\<^sup>\<dagger>"
  by (simp add: local.dagger_simr local.eq_iff preservation2)

end

class pre_conway_zerol = near_conway_zerol + pre_dioid_one_zerol

begin

subclass pre_conway ..

end

class conway = pre_conway + dioid_one

class conway_zerol = pre_conway + dioid_one_zerol

begin

subclass conway_base ..

text \<open>Nitpick refutes the next lemmas.\<close>

lemma "1 = 1\<^sup>\<dagger>"
(*nitpick [expect=genuine]*)
oops

lemma "(x\<^sup>\<dagger>)\<^sup>\<dagger> = x\<^sup>\<dagger>"
(*nitpick [expect=genuine]*)
oops

lemma dagger_denest_var [simp]: "(x + y)\<^sup>\<dagger> = (x\<^sup>\<dagger> \<cdot> y\<^sup>\<dagger>)\<^sup>\<dagger>"
(* nitpick [expect=genuine]*)
oops

lemma star2 [simp]: "(1 + x)\<^sup>\<dagger> = x\<^sup>\<dagger>"
(*nitpick [expect=genuine]*)
oops

end

end
