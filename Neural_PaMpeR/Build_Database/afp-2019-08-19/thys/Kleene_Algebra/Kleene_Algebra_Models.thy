(* Title:      Models of Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Models of Kleene Algebras\<close>

theory Kleene_Algebra_Models
imports Kleene_Algebra Dioid_Models
begin

text \<open>We now show that most of the models considered for dioids are
also Kleene algebras. Some of the dioid models cannot be expanded, for
instance max-plus and min-plus semirings, but we do not formalise this
fact. We also currently do not show that formal powerseries and
matrices form Kleene algebras.

The interpretation proofs for some of the following models are quite
similar. One could, perhaps, abstract out common reasoning in the
future.\<close>

subsection \<open>Preliminary Lemmas\<close>

text \<open>We first prove two induction-style statements for dioids that
are useful for establishing the full induction laws. In the future
these will live in a theory file on finite sums for Kleene
algebras.\<close>

context dioid_one_zero
begin

lemma power_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> (x ^ n) \<cdot> z \<le> y"
proof (induct n)
  case 0 show ?case
    using "0.prems" by auto
  case Suc thus ?case
    by (auto, metis mult.assoc mult_isol order_trans)
qed

lemma power_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> (x ^ n) \<le> y"
proof (induct n)
  case 0 show ?case
    using "0.prems" by auto
  case Suc
  {
    fix n
    assume "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x ^ n \<le> y"
      and "z + y \<cdot> x \<le> y"
    hence "z \<cdot> x ^ n \<le> y"
      by auto
    also have "z \<cdot> x ^ Suc n = z \<cdot> x \<cdot> x ^ n"
      by (metis mult.assoc power_Suc)
    moreover have "... = (z \<cdot> x ^ n) \<cdot> x"
      by (metis mult.assoc power_commutes)
    moreover have "... \<le> y \<cdot> x"
      by (metis calculation(1) mult_isor)
    moreover have "... \<le> y"
      using \<open>z + y \<cdot> x \<le> y\<close> by auto
    ultimately have "z \<cdot> x ^ Suc n \<le> y" by auto
  }
  thus ?case
    by (metis Suc)
qed

end (* dioid_one_zero *)


subsection \<open>The Powerset Kleene Algebra over a Monoid\<close>

text \<open>We now show that the powerset dioid forms a Kleene
algebra. The Kleene star is defined as in language theory.\<close>

lemma Un_0_Suc: "(\<Union>n. f n) = f 0 \<union> (\<Union>n. f (Suc n))"
by auto (metis not0_implies_Suc)

instantiation set :: (monoid_mult) kleene_algebra
begin

  definition star_def: "X\<^sup>\<star> = (\<Union>n. X ^ n)"

  lemma star_elim: "x \<in> X\<^sup>\<star> \<longleftrightarrow> (\<exists>k. x \<in> X ^ k)"
  by (simp add: star_def)

  lemma star_contl: "X \<cdot> Y\<^sup>\<star> = (\<Union>n. X \<cdot> Y ^ n)"
  by (auto simp add: star_elim c_prod_def)

  lemma star_contr: "X\<^sup>\<star> \<cdot> Y = (\<Union>n. X ^ n \<cdot> Y)"
  by (auto simp add: star_elim c_prod_def)

  instance
  proof
    fix X Y Z :: "'a set"
    show "1 + X \<cdot> X\<^sup>\<star> \<subseteq> X\<^sup>\<star>"
    proof -
      have "1 + X \<cdot> X\<^sup>\<star> = (X ^ 0) \<union> (\<Union>n. X ^ (Suc n))"
        by (auto simp add: star_def c_prod_def plus_set_def one_set_def)
      also have "... = (\<Union>n. X ^ n)"
        by (metis Un_0_Suc)
      also have "... = X\<^sup>\<star>"
        by (simp only: star_def)
      finally show ?thesis
        by (metis subset_refl)
    qed
  next
    fix X Y Z :: "'a set"
    assume hyp: "Z + X \<cdot> Y \<subseteq> Y"
    show  "X\<^sup>\<star> \<cdot> Z \<subseteq> Y"
      by (simp add: star_contr SUP_le_iff) (meson hyp dioid_one_zero_class.power_inductl)
  next
    fix X Y Z :: "'a set"
    assume hyp: "Z + Y \<cdot> X \<subseteq> Y"
    show  "Z \<cdot> X\<^sup>\<star> \<subseteq> Y"
      by (simp add: star_contl SUP_le_iff) (meson dioid_one_zero_class.power_inductr hyp) 
  qed

end (* instantiation *)


subsection \<open>Language Kleene Algebras\<close>

text \<open>We now specialise this fact to languages.\<close>

interpretation lan_kleene_algebra: kleene_algebra "(+)" "(\<cdot>)" "1::'a lan" "0" "(\<subseteq>)" "(\<subset>)" star ..


subsection \<open>Regular Languages\<close>

text \<open>{\ldots} and further to regular languages. For the sake of
simplicity we just copy in the axiomatisation of regular expressions
by Krauss and Nipkow~\cite{krauss12regular}.\<close>

datatype 'a rexp =
  Zero
| One
| Atom 'a
| Plus "'a rexp" "'a rexp"
| Times "'a rexp" "'a rexp"
| Star "'a rexp"

text \<open>The interpretation map that induces regular languages as the
images of regular expressions in the set of languages has also been
adapted from there.\<close>

fun lang :: "'a rexp \<Rightarrow> 'a lan" where
  "lang Zero = 0"  \<comment> \<open>{}\<close>
| "lang One = 1"  \<comment> \<open>{[]}\<close>
| "lang (Atom a) = {[a]}"
| "lang (Plus x y) = lang x + lang y"
| "lang (Times x y) = lang x \<cdot> lang y"
| "lang (Star x) = (lang x)\<^sup>\<star>"

typedef 'a reg_lan = "range lang :: 'a lan set"
  by auto

setup_lifting type_definition_reg_lan

instantiation reg_lan :: (type) kleene_algebra
begin

  lift_definition star_reg_lan :: "'a reg_lan \<Rightarrow> 'a reg_lan"
    is star
    by (metis (hide_lams, no_types) image_iff lang.simps(6) rangeI)

  lift_definition zero_reg_lan :: "'a reg_lan"
    is 0
    by (metis lang.simps(1) rangeI)

  lift_definition one_reg_lan :: "'a reg_lan"
    is 1
    by (metis lang.simps(2) rangeI)

  lift_definition less_eq_reg_lan :: "'a reg_lan \<Rightarrow> 'a reg_lan \<Rightarrow> bool"
    is less_eq .

  lift_definition less_reg_lan :: "'a reg_lan \<Rightarrow> 'a reg_lan \<Rightarrow> bool"
    is less .

  lift_definition plus_reg_lan :: "'a reg_lan \<Rightarrow> 'a reg_lan \<Rightarrow> 'a reg_lan"
    is plus
    by (metis (hide_lams, no_types) image_iff lang.simps(4) rangeI)

  lift_definition times_reg_lan :: "'a reg_lan \<Rightarrow> 'a reg_lan \<Rightarrow> 'a reg_lan"
    is times
    by (metis (hide_lams, no_types) image_iff lang.simps(5) rangeI)

  instance
  proof
    fix x y z :: "'a reg_lan"
    show "x + y + z = x + (y + z)"
      by transfer (metis join_semilattice_class.add_assoc')
    show "x + y = y + x"
      by transfer (metis join_semilattice_class.add_comm)
    show "x \<cdot> y \<cdot> z = x \<cdot> (y \<cdot> z)"
      by transfer (metis semigroup_mult_class.mult.assoc)
    show "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
      by transfer (metis semiring_class.distrib_right)
    show "1 \<cdot> x = x"
      by transfer (metis monoid_mult_class.mult_1_left)
    show "x \<cdot> 1 = x"
      by transfer (metis monoid_mult_class.mult_1_right)
    show "0 + x = x"
      by transfer (metis join_semilattice_zero_class.add_zero_l)
    show "0 \<cdot> x = 0"
      by transfer (metis ab_near_semiring_one_zerol_class.annil)
    show "x \<cdot> 0 = 0"
      by transfer (metis ab_near_semiring_one_zero_class.annir)
    show "x \<le> y \<longleftrightarrow> x + y = y"
      by transfer (metis plus_ord_class.less_eq_def)
    show "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
      by transfer (metis plus_ord_class.less_def)
    show "x + x = x"
      by transfer (metis join_semilattice_class.add_idem)
    show "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z"
      by transfer (metis semiring_class.distrib_left)
    show "z \<cdot> x \<le> z \<cdot> (x + y)"
      by transfer (metis pre_dioid_class.subdistl)
    show "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
      by transfer (metis star_unfoldl)
    show "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
      by transfer (metis star_inductl)
    show "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
      by transfer (metis star_inductr)
  qed

end  (* instantiation *)

interpretation reg_lan_kleene_algebra: kleene_algebra "(+)" "(\<cdot>)" "1::'a reg_lan" 0 "(\<le>)" "(<)" star ..


subsection \<open>Relation Kleene Algebras\<close>

text \<open>We now show that binary relations form Kleene algebras. While
we could have used the reflexive transitive closure operation as the
Kleene star, we prefer the equivalent definition of the star as the
sum of powers. This essentially allows us to copy previous proofs.\<close>

lemma power_is_relpow: "rel_dioid.power X n = X ^^ n"
proof (induct n)
  case 0 show ?case
    by (metis rel_dioid.power_0 relpow.simps(1))
  case Suc thus ?case
    by (metis rel_dioid.power_Suc2 relpow.simps(2))
qed

lemma rel_star_def: "X^* = (\<Union>n. rel_dioid.power X n)"
  by (simp add: power_is_relpow rtrancl_is_UN_relpow)

lemma rel_star_contl: "X O Y^* = (\<Union>n. X O rel_dioid.power Y n)"
by (metis rel_star_def relcomp_UNION_distrib)

lemma rel_star_contr: "X^* O Y = (\<Union>n. (rel_dioid.power X n) O Y)"
by (metis rel_star_def relcomp_UNION_distrib2)

interpretation rel_kleene_algebra: kleene_algebra "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl
proof
  fix x y z :: "'a rel"
  show "Id \<union> x O x\<^sup>* \<subseteq> x\<^sup>*"
    by (metis order_refl r_comp_rtrancl_eq rtrancl_unfold)
next
  fix x y z :: "'a rel"
  assume "z \<union> x O y \<subseteq> y"
  thus "x\<^sup>* O z \<subseteq> y"
    by (simp only: rel_star_contr, metis (lifting) SUP_le_iff rel_dioid.power_inductl)
next
  fix x y z :: "'a rel"
  assume "z \<union> y O x \<subseteq> y"
  thus "z O x\<^sup>* \<subseteq> y"
    by (simp only: rel_star_contl, metis (lifting) SUP_le_iff rel_dioid.power_inductr)
qed

subsection \<open>Trace Kleene Algebras\<close>

text \<open>Again, the proof that sets of traces form Kleene algebras
follows the same schema.\<close>

definition t_star :: "('p, 'a) trace set \<Rightarrow> ('p, 'a) trace set" where
  "t_star X \<equiv> \<Union>n. trace_dioid.power X n"

lemma t_star_elim: "x \<in> t_star X \<longleftrightarrow> (\<exists>n. x \<in> trace_dioid.power X n)"
  by (simp add: t_star_def)

lemma t_star_contl: "t_prod X (t_star Y) = (\<Union>n. t_prod X (trace_dioid.power Y n))"
  by (auto simp add: t_star_elim t_prod_def)

lemma t_star_contr: "t_prod (t_star X) Y = (\<Union>n. t_prod (trace_dioid.power X n) Y)"
  by (auto simp add: t_star_elim t_prod_def)

interpretation trace_kleene_algebra: kleene_algebra "(\<union>)" t_prod t_one t_zero "(\<subseteq>)" "(\<subset>)" t_star
proof
  fix X Y Z :: "('a, 'b) trace set"
  show "t_one \<union> t_prod X (t_star X) \<subseteq> t_star X"
    proof -
      have "t_one \<union> t_prod X (t_star X) = (trace_dioid.power X 0) \<union> (\<Union>n. trace_dioid.power X (Suc n))"
        by (auto simp add: t_star_def t_prod_def)
      also have "... = (\<Union>n. trace_dioid.power X n)"
        by (metis Un_0_Suc)
      also have "... = t_star X"
        by (metis t_star_def)
      finally show ?thesis
        by (metis subset_refl)
    qed
  show "Z \<union> t_prod X Y \<subseteq> Y \<Longrightarrow> t_prod (t_star X) Z \<subseteq> Y"
    by (simp only: ball_UNIV t_star_contr SUP_le_iff) (metis trace_dioid.power_inductl)
  show "Z \<union> t_prod Y X \<subseteq> Y \<Longrightarrow> t_prod Z (t_star X) \<subseteq> Y"
    by (simp only: ball_UNIV t_star_contl SUP_le_iff) (metis trace_dioid.power_inductr)
qed


subsection \<open>Path Kleene Algebras\<close>

text \<open>We start with paths that include the empty path.\<close>

definition p_star :: "'a path set \<Rightarrow> 'a path set" where
  "p_star X \<equiv> \<Union>n. path_dioid.power X n"

lemma p_star_elim: "x \<in> p_star X \<longleftrightarrow> (\<exists>n. x \<in> path_dioid.power X n)"
by (simp add: p_star_def)

lemma p_star_contl: "p_prod X (p_star Y) = (\<Union>n. p_prod X (path_dioid.power Y n))"
apply (auto simp add: p_prod_def p_star_elim)
   apply (metis p_fusion.simps(1))
  apply metis
 apply (metis p_fusion.simps(1) p_star_elim)
apply (metis p_star_elim)
done

lemma p_star_contr: "p_prod (p_star X) Y = (\<Union>n. p_prod (path_dioid.power X n) Y)"
apply (auto simp add: p_prod_def p_star_elim)
   apply (metis p_fusion.simps(1))
  apply metis
 apply (metis p_fusion.simps(1) p_star_elim)
apply (metis p_star_elim)
done

interpretation path_kleene_algebra: kleene_algebra "(\<union>)" p_prod p_one "{}" "(\<subseteq>)" "(\<subset>)" p_star
proof
  fix X Y Z :: "'a path set"
  show "p_one \<union> p_prod X (p_star X) \<subseteq> p_star X"
    proof -
      have "p_one \<union> p_prod X (p_star X) = (path_dioid.power X 0) \<union> (\<Union>n. path_dioid.power X (Suc n))"
        by (auto simp add: p_star_def p_prod_def)
      also have "... = (\<Union>n. path_dioid.power X n)"
        by (metis Un_0_Suc)
      also have "... = p_star X"
        by (metis p_star_def)
      finally show ?thesis
        by (metis subset_refl)
    qed
  show "Z \<union> p_prod X Y \<subseteq> Y \<Longrightarrow> p_prod (p_star X) Z \<subseteq> Y"
    by (simp only: ball_UNIV p_star_contr SUP_le_iff) (metis path_dioid.power_inductl)
  show "Z \<union> p_prod Y X \<subseteq> Y \<Longrightarrow> p_prod Z (p_star X) \<subseteq> Y"
    by (simp only: ball_UNIV p_star_contl SUP_le_iff) (metis path_dioid.power_inductr)
qed

text \<open>We now consider a notion of paths that does not include the
empty path.\<close>

definition pp_star :: "'a ppath set \<Rightarrow> 'a ppath set" where
  "pp_star X \<equiv> \<Union>n. ppath_dioid.power X n"

lemma pp_star_elim: "x \<in> pp_star X \<longleftrightarrow> (\<exists>n. x \<in> ppath_dioid.power X n)"
by (simp add: pp_star_def)

lemma pp_star_contl: "pp_prod X (pp_star Y) = (\<Union>n. pp_prod X (ppath_dioid.power Y n))"
by (auto simp add: pp_prod_def pp_star_elim)

lemma pp_star_contr: "pp_prod (pp_star X) Y = (\<Union>n. pp_prod (ppath_dioid.power X n) Y)"
by (auto simp add: pp_prod_def pp_star_elim)

interpretation ppath_kleene_algebra: kleene_algebra "(\<union>)" pp_prod pp_one "{}" "(\<subseteq>)" "(\<subset>)" pp_star
proof
  fix X Y Z :: "'a ppath set"
  show "pp_one \<union> pp_prod X (pp_star X) \<subseteq> pp_star X"
    proof -
      have "pp_one \<union> pp_prod X (pp_star X) = (ppath_dioid.power X 0) \<union> (\<Union>n. ppath_dioid.power X (Suc n))"
        by (auto simp add: pp_star_def pp_prod_def)
      also have "... = (\<Union>n. ppath_dioid.power X n)"
        by (metis Un_0_Suc)
      also have "... = pp_star X"
        by (metis pp_star_def)
      finally show ?thesis
        by (metis subset_refl)
    qed
  show "Z \<union> pp_prod X Y \<subseteq> Y \<Longrightarrow> pp_prod (pp_star X) Z \<subseteq> Y"
    by (simp only: ball_UNIV pp_star_contr SUP_le_iff) (metis ppath_dioid.power_inductl)
  show "Z \<union> pp_prod Y X \<subseteq> Y \<Longrightarrow> pp_prod Z (pp_star X) \<subseteq> Y"
    by (simp only: ball_UNIV pp_star_contl SUP_le_iff) (metis ppath_dioid.power_inductr)
qed


subsection \<open>The Distributive Lattice Kleene Algebra\<close>

text \<open>In the case of bounded distributive lattices, the star maps
all elements to to the maximal element.\<close>

definition (in bounded_distributive_lattice) bdl_star :: "'a \<Rightarrow> 'a" where
  "bdl_star x = top"

sublocale bounded_distributive_lattice \<subseteq> kleene_algebra sup inf top bot less_eq less bdl_star
proof
  fix x y z :: 'a
  show "sup top (inf x (bdl_star x)) \<le> bdl_star x"
    by (simp add: bdl_star_def)
  show "sup z (inf x y) \<le> y \<Longrightarrow> inf (bdl_star x) z \<le> y"
    by (simp add: bdl_star_def)
  show "sup z (inf y x) \<le> y \<Longrightarrow> inf z (bdl_star x) \<le> y"
    by (simp add: bdl_star_def)
qed


subsection \<open>The Min-Plus Kleene Algebra\<close>

text \<open>One cannot define a Kleene star for max-plus and min-plus
algebras that range over the real numbers. Here we define the star for
a min-plus algebra restricted to natural numbers and~$+\infty$. The
resulting Kleene algebra is commutative. Similar variants can be
obtained for max-plus algebras and other algebras ranging over the
positive or negative integers.\<close>

instantiation pnat :: commutative_kleene_algebra
begin

  definition star_pnat where
    "x\<^sup>\<star> \<equiv> (1::pnat)"

  instance
  proof
    fix x y z :: pnat
    show "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
      by (metis star_pnat_def zero_pnat_top)
    show "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
      by (simp add: star_pnat_def)
    show "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
      by (simp add: star_pnat_def)
    show "x \<cdot> y = y \<cdot> x"
      unfolding times_pnat_def by (cases x, cases y, simp_all)
  qed

end (* instantiation *)

end
