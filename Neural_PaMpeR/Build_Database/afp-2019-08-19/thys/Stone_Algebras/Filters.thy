(* Title:      Filters
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Filters\<close>

text \<open>
This theory develops filters based on orders, semilattices, lattices and distributive lattices.
We prove the ultrafilter lemma for orders with a least element.
We show the following structure theorems:
\begin{itemize}
\item The set of filters over a directed semilattice forms a lattice with a greatest element.
\item The set of filters over a bounded semilattice forms a bounded lattice.
\item The set of filters over a distributive lattice with a greatest element forms a bounded distributive lattice.
\end{itemize}
Another result is that in a distributive lattice ultrafilters are prime filters.
We also prove a lemma of Gr\"atzer and Schmidt about principal filters.

We apply these results in proving the construction theorem for Stone algebras (described in a separate theory).
See, for example, \cite{BalbesDwinger1974,Birkhoff1967,Blyth2005,DaveyPriestley2002,Graetzer1971} for further results about filters.
\<close>

theory Filters

imports Lattice_Basics

begin

subsection \<open>Orders\<close>

text \<open>
This section gives the basic definitions related to filters in terms of orders.
The main result is the ultrafilter lemma.
\<close>

context ord
begin

abbreviation down :: "'a \<Rightarrow> 'a set" ("\<down>_" [81] 80)
  where "\<down>x \<equiv> { y . y \<le> x }"

abbreviation down_set :: "'a set \<Rightarrow> 'a set" ("\<Down>_" [81] 80)
  where "\<Down>X \<equiv> { y . \<exists>x\<in>X . y \<le> x }"

abbreviation is_down_set :: "'a set \<Rightarrow> bool"
  where "is_down_set X \<equiv> \<forall>x\<in>X . \<forall>y . y \<le> x \<longrightarrow> y\<in>X"

abbreviation is_principal_down :: "'a set \<Rightarrow> bool"
  where "is_principal_down X \<equiv> \<exists>x . X = \<down>x"

abbreviation up :: "'a \<Rightarrow> 'a set" ("\<up>_" [81] 80)
  where "\<up>x \<equiv> { y . x \<le> y }"

abbreviation up_set :: "'a set \<Rightarrow> 'a set" ("\<Up>_" [81] 80)
  where "\<Up>X \<equiv> { y . \<exists>x\<in>X . x \<le> y }"

abbreviation is_up_set :: "'a set \<Rightarrow> bool"
  where "is_up_set X \<equiv> \<forall>x\<in>X . \<forall>y . x \<le> y \<longrightarrow> y\<in>X"

abbreviation is_principal_up :: "'a set \<Rightarrow> bool"
  where "is_principal_up X \<equiv> \<exists>x . X = \<up>x"

text \<open>
A filter is a non-empty, downward directed, up-closed set.
\<close>

definition filter :: "'a set \<Rightarrow> bool"
  where "filter F \<equiv> (F \<noteq> {}) \<and> (\<forall>x\<in>F . \<forall>y\<in>F . \<exists>z\<in>F . z \<le> x \<and> z \<le> y) \<and> is_up_set F"

abbreviation proper_filter :: "'a set \<Rightarrow> bool"
  where "proper_filter F \<equiv> filter F \<and> F \<noteq> UNIV"

abbreviation ultra_filter :: "'a set \<Rightarrow> bool"
  where "ultra_filter F \<equiv> proper_filter F \<and> (\<forall>G . proper_filter G \<and> F \<subseteq> G \<longrightarrow> F = G)"

end

context order
begin

lemma self_in_downset [simp]:
  "x \<in> \<down>x"
  by simp

lemma self_in_upset [simp]:
  "x \<in> \<up>x"
  by simp

lemma up_filter [simp]:
  "filter (\<up>x)"
  using filter_def order_lesseq_imp by auto

lemma up_set_up_set [simp]:
  "is_up_set (\<Up>X)"
  using order.trans by fastforce

lemma up_injective:
  "\<up>x = \<up>y \<Longrightarrow> x = y"
  using antisym by auto

lemma up_antitone:
  "x \<le> y \<longleftrightarrow> \<up>y \<subseteq> \<up>x"
  by auto

end

context order_bot
begin

lemma bot_in_downset [simp]:
  "bot \<in> \<down>x"
  by simp

lemma down_bot [simp]:
  "\<down>bot = {bot}"
  by (simp add: bot_unique)

lemma up_bot [simp]:
  "\<up>bot = UNIV"
  by simp

text \<open>
The following result is the ultrafilter lemma, generalised from \cite[10.17]{DaveyPriestley2002} to orders with a least element.
Its proof uses Isabelle/HOL's \<open>Zorn_Lemma\<close>, which requires closure under union of arbitrary (possibly empty) chains.
Actually, the proof does not use any of the underlying order properties except \<open>bot_least\<close>.
\<close>

lemma ultra_filter:
  assumes "proper_filter F"
    shows "\<exists>G . ultra_filter G \<and> F \<subseteq> G"
proof -
  let ?A = "{ G . (proper_filter G \<and> F \<subseteq> G) \<or> G = {} }"
  have "\<forall>C \<in> chains ?A . \<Union>C \<in> ?A"
  proof
    fix C :: "'a set set"
    let ?D = "C - {{}}"
    assume 1: "C \<in> chains ?A"
    hence 2: "\<forall>x\<in>\<Union>?D . \<exists>H\<in>?D . x \<in> H \<and> proper_filter H"
      using chainsD2 by fastforce
    have 3: "\<Union>?D = \<Union>C"
      by blast
    have "\<Union>?D \<in> ?A"
    proof (cases "?D = {}")
      assume "?D = {}"
      thus ?thesis
        by auto
    next
      assume 4: "?D \<noteq> {}"
      then obtain G where "G \<in> ?D"
        by auto
      hence 5: "F \<subseteq> \<Union>?D"
        using 1 chainsD2 by blast
      have 6: "is_up_set (\<Union>?D)"
      proof
        fix x
        assume "x \<in> \<Union>?D"
        then obtain H where "x \<in> H \<and> H \<in> ?D \<and> filter H"
          using 2 by auto
        thus "\<forall>y . x \<le> y \<longrightarrow> y\<in>\<Union>?D"
          using filter_def UnionI by fastforce
      qed
      have 7: "\<Union>?D \<noteq> UNIV"
      proof (rule ccontr)
        assume "\<not> \<Union>?D \<noteq> UNIV"
        then obtain H where "bot \<in> H \<and> proper_filter H"
          using 2 by blast
        thus False
          by (meson UNIV_I bot_least filter_def subsetI subset_antisym)
      qed
      {
        fix x y
        assume "x\<in>\<Union>?D \<and> y\<in>\<Union>?D"
        then obtain H I where 8: "x \<in> H \<and> H \<in> ?D \<and> filter H \<and> y \<in> I \<and> I \<in> ?D \<and> filter I"
          using 2 by metis
        have "\<exists>z\<in>\<Union>?D . z \<le> x \<and> z \<le> y"
        proof (cases "H \<subseteq> I")
          assume "H \<subseteq> I"
          hence "\<exists>z\<in>I . z \<le> x \<and> z \<le> y"
            using 8 by (metis subsetCE filter_def)
          thus ?thesis
            using 8 by (metis UnionI)
        next
          assume "\<not> (H \<subseteq> I)"
          hence "I \<subseteq> H"
            using 1 8 by (meson DiffE chainsD)
          hence "\<exists>z\<in>H . z \<le> x \<and> z \<le> y"
            using 8 by (metis subsetCE filter_def)
          thus ?thesis
            using 8 by (metis UnionI)
        qed
      }
      thus ?thesis
        using 4 5 6 7 filter_def by auto
    qed
    thus "\<Union>C \<in> ?A"
      using 3 by simp
  qed
  hence "\<exists>M\<in>?A . \<forall>X\<in>?A . M \<subseteq> X \<longrightarrow> X = M"
    by (rule Zorn_Lemma)
  then obtain M where 9: "M \<in> ?A \<and> (\<forall>X\<in>?A . M \<subseteq> X \<longrightarrow> X = M)"
    by auto
  hence 10: "M \<noteq> {}"
    using assms filter_def by auto
  {
    fix G
    assume 11: "proper_filter G \<and> M \<subseteq> G"
    hence "F \<subseteq> G"
      using 9 10 by blast
    hence "M = G"
      using 9 11 by auto
  }
  thus ?thesis
    using 9 10 by blast
qed

end

context order_top
begin

lemma down_top [simp]:
  "\<down>top = UNIV"
  by simp

lemma top_in_upset [simp]:
  "top \<in> \<up>x"
  by simp

lemma up_top [simp]:
  "\<up>top = {top}"
  by (simp add: top_unique)

lemma filter_top [simp]:
  "filter {top}"
  using filter_def top_unique by auto

lemma top_in_filter [simp]:
  "filter F \<Longrightarrow> top \<in> F"
  using filter_def by fastforce

end

text \<open>
The existence of proper filters and ultrafilters requires that the underlying order contains at least two elements.
\<close>

context non_trivial_order
begin

lemma proper_filter_exists:
  "\<exists>F . proper_filter F"
proof -
  from consistent obtain x y :: 'a where "x \<noteq> y"
    by auto
  hence "\<up>x \<noteq> UNIV \<or> \<up>y \<noteq> UNIV"
    using antisym by blast
  hence "proper_filter (\<up>x) \<or> proper_filter (\<up>y)"
    by simp
  thus ?thesis
    by blast
qed

end

context non_trivial_order_bot
begin

lemma ultra_filter_exists:
  "\<exists>F . ultra_filter F"
  using ultra_filter proper_filter_exists by blast

end

context non_trivial_bounded_order
begin

lemma proper_filter_top:
  "proper_filter {top}"
  using bot_not_top filter_top by blast

lemma ultra_filter_top:
  "\<exists>G . ultra_filter G \<and> top \<in> G"
  using ultra_filter proper_filter_top by fastforce

end

subsection \<open>Lattices\<close>

text \<open>
This section develops the lattice structure of filters based on a semilattice structure of the underlying order.
The main results are that filters over a directed semilattice form a lattice with a greatest element and that filters over a bounded semilattice form a bounded lattice.
\<close>

context semilattice_sup
begin

abbreviation prime_filter :: "'a set \<Rightarrow> bool"
  where "prime_filter F \<equiv> proper_filter F \<and> (\<forall>x y . x \<squnion> y \<in> F \<longrightarrow> x \<in> F \<or> y \<in> F)"

end

context semilattice_inf
begin

lemma filter_inf_closed:
  "filter F \<Longrightarrow> x \<in> F \<Longrightarrow> y \<in> F \<Longrightarrow> x \<sqinter> y \<in> F"
  by (meson filter_def inf.boundedI)

lemma filter_univ:
  "filter UNIV"
  by (meson UNIV_I UNIV_not_empty filter_def inf.cobounded1 inf.cobounded2)

text \<open>
The operation \<open>filter_sup\<close> is the join operation in the lattice of filters.
\<close>

abbreviation "filter_sup F G \<equiv> { z . \<exists>x\<in>F . \<exists>y\<in>G . x \<sqinter> y \<le> z }"

lemma filter_sup:
  assumes "filter F"
      and "filter G"
    shows "filter (filter_sup F G)"
proof -
  have "F \<noteq> {} \<and> G \<noteq> {}"
    using assms filter_def by blast
  hence 1: "filter_sup F G \<noteq> {}"
    by blast
  have 2: "\<forall>x\<in>filter_sup F G . \<forall>y\<in>filter_sup F G . \<exists>z\<in>filter_sup F G . z \<le> x \<and> z \<le> y"
  proof
    fix x
    assume "x\<in>filter_sup F G"
    then obtain t u where 3: "t \<in> F \<and> u \<in> G \<and> t \<sqinter> u \<le> x"
      by auto
    show "\<forall>y\<in>filter_sup F G . \<exists>z\<in>filter_sup F G . z \<le> x \<and> z \<le> y"
    proof
      fix y
      assume "y\<in>filter_sup F G"
      then obtain v w where 4: "v \<in> F \<and> w \<in> G \<and> v \<sqinter> w \<le> y"
        by auto
      let ?z = "(t \<sqinter> v) \<sqinter> (u \<sqinter> w)"
      have 5: "?z \<le> x \<and> ?z \<le> y"
        using 3 4 by (meson order.trans inf.cobounded1 inf.cobounded2 inf_mono)
      have "?z \<in> filter_sup F G"
        using assms 3 4 filter_inf_closed by blast
      thus "\<exists>z\<in>filter_sup F G . z \<le> x \<and> z \<le> y"
        using 5 by blast
    qed
  qed
  have "\<forall>x\<in>filter_sup F G . \<forall>y . x \<le> y \<longrightarrow> y \<in> filter_sup F G"
    using order_trans by blast
  thus ?thesis
    using 1 2 filter_def by presburger
qed

lemma filter_sup_left_upper_bound:
  assumes "filter G"
    shows "F \<subseteq> filter_sup F G"
proof -
  from assms obtain y where "y\<in>G"
    using all_not_in_conv filter_def by auto
  thus ?thesis
    using inf.cobounded1 by blast
qed

lemma filter_sup_symmetric:
  "filter_sup F G = filter_sup G F"
  using inf.commute by fastforce

lemma filter_sup_right_upper_bound:
  "filter F \<Longrightarrow> G \<subseteq> filter_sup F G"
  using filter_sup_symmetric filter_sup_left_upper_bound by simp

lemma filter_sup_least_upper_bound:
  assumes "filter H"
      and "F \<subseteq> H"
      and "G \<subseteq> H"
    shows "filter_sup F G \<subseteq> H"
proof
  fix x
  assume "x \<in> filter_sup F G"
  then obtain y z where 1: "y \<in> F \<and> z \<in> G \<and> y \<sqinter> z \<le> x"
    by auto
  hence "y \<in> H \<and> z \<in> H"
    using assms(2-3) by auto
  hence "y \<sqinter> z \<in> H"
    by (simp add: assms(1) filter_inf_closed)
  thus "x \<in> H"
    using 1 assms(1) filter_def by auto
qed

lemma filter_sup_left_isotone:
  "G \<subseteq> H \<Longrightarrow> filter_sup G F \<subseteq> filter_sup H F"
  by blast

lemma filter_sup_right_isotone:
  "G \<subseteq> H \<Longrightarrow> filter_sup F G \<subseteq> filter_sup F H"
  by blast

lemma filter_sup_right_isotone_var:
  "filter_sup F (G \<inter> H) \<subseteq> filter_sup F H"
  by blast

lemma up_dist_inf:
  "\<up>(x \<sqinter> y) = filter_sup (\<up>x) (\<up>y)"
proof
  show "\<up>(x \<sqinter> y) \<subseteq> filter_sup (\<up>x) (\<up>y)"
    by blast
next
  show "filter_sup (\<up>x) (\<up>y) \<subseteq> \<up>(x \<sqinter> y)"
  proof
    fix z
    assume "z \<in> filter_sup (\<up>x) (\<up>y)"
    then obtain u v where "u\<in>\<up>x \<and> v\<in>\<up>y \<and> u \<sqinter> v \<le> z"
      by auto
    hence "x \<sqinter> y \<le> z"
      using order.trans inf_mono by blast
    thus "z \<in> \<up>(x \<sqinter> y)"
      by blast
  qed
qed

text \<open>
The following result is part of \cite[Exercise 2.23]{DaveyPriestley2002}.
\<close>

lemma filter_inf_filter [simp]:
  assumes "filter F"
    shows "filter (\<Up>{ y . \<exists>z\<in>F . x \<sqinter> z = y})"
proof -
  let ?G = "\<Up>{ y . \<exists>z\<in>F . x \<sqinter> z = y}"
  have "F \<noteq> {}"
    using assms filter_def by simp
  hence 1: "?G \<noteq> {}"
    by blast
  have 2: "is_up_set ?G"
    by auto
  {
    fix y z
    assume "y \<in> ?G \<and> z \<in> ?G"
    then obtain v w where "v \<in> F \<and> w \<in> F \<and> x \<sqinter> v \<le> y \<and> x \<sqinter> w \<le> z"
      by auto
    hence "v \<sqinter> w \<in> F \<and> x \<sqinter> (v \<sqinter> w) \<le> y \<sqinter> z"
      by (meson assms filter_inf_closed order.trans inf.boundedI inf.cobounded1 inf.cobounded2)
    hence "\<exists>u\<in>?G . u \<le> y \<and> u \<le> z"
      by auto
  }
  hence "\<forall>x\<in>?G . \<forall>y\<in>?G . \<exists>z\<in>?G . z \<le> x \<and> z \<le> y"
    by auto
  thus ?thesis
    using 1 2 filter_def by presburger
qed

end

context directed_semilattice_inf
begin

text \<open>
Set intersection is the meet operation in the lattice of filters.
\<close>

lemma filter_inf:
  assumes "filter F"
      and "filter G"
    shows "filter (F \<inter> G)"
proof (unfold filter_def, intro conjI)
  from assms obtain x y where 1: "x\<in>F \<and> y\<in>G"
    using all_not_in_conv filter_def by auto
  from ub obtain z where "x \<le> z \<and> y \<le> z"
    by auto
  hence "z \<in> F \<inter> G"
    using 1 by (meson assms Int_iff filter_def)
  thus "F \<inter> G \<noteq> {}"
    by blast
next
  show "is_up_set (F \<inter> G)"
    by (meson assms Int_iff filter_def)
next
  show "\<forall>x\<in>F \<inter> G . \<forall>y\<in>F \<inter> G . \<exists>z\<in>F \<inter> G . z \<le> x \<and> z \<le> y"
    by (metis assms Int_iff filter_inf_closed inf.cobounded2 inf.commute)
qed

end

text \<open>
We introduce the following type of filters to instantiate the lattice classes and thereby inherit the results shown about lattices.
\<close>

typedef (overloaded) 'a filter = "{ F::'a::order set . filter F }"
  by (meson mem_Collect_eq up_filter)

lemma simp_filter [simp]:
  "filter (Rep_filter x)"
  using Rep_filter by simp

setup_lifting type_definition_filter

text \<open>
The set of filters over a directed semilattice forms a lattice with a greatest element.
\<close>

instantiation filter :: (directed_semilattice_inf) bounded_lattice_top
begin

lift_definition top_filter :: "'a filter" is UNIV
  by (simp add: filter_univ)

lift_definition sup_filter :: "'a filter \<Rightarrow> 'a filter \<Rightarrow> 'a filter" is filter_sup
  by (simp add: filter_sup)

lift_definition inf_filter :: "'a filter \<Rightarrow> 'a filter \<Rightarrow> 'a filter" is inter
  by (simp add: filter_inf)

lift_definition less_eq_filter :: "'a filter \<Rightarrow> 'a filter \<Rightarrow> bool" is subset_eq .

lift_definition less_filter :: "'a filter \<Rightarrow> 'a filter \<Rightarrow> bool" is subset .

instance
  apply intro_classes
  apply (simp add: less_eq_filter.rep_eq less_filter.rep_eq inf.less_le_not_le)
  apply (simp add: less_eq_filter.rep_eq)
  apply (simp add: less_eq_filter.rep_eq)
  apply (simp add: Rep_filter_inject less_eq_filter.rep_eq)
  apply (simp add: inf_filter.rep_eq less_eq_filter.rep_eq)
  apply (simp add: inf_filter.rep_eq less_eq_filter.rep_eq)
  apply (simp add: inf_filter.rep_eq less_eq_filter.rep_eq)
  apply (simp add: less_eq_filter.rep_eq filter_sup_left_upper_bound sup_filter.rep_eq)
  apply (simp add: less_eq_filter.rep_eq filter_sup_right_upper_bound sup_filter.rep_eq)
  apply (simp add: less_eq_filter.rep_eq filter_sup_least_upper_bound sup_filter.rep_eq)
  by (simp add: less_eq_filter.rep_eq top_filter.rep_eq)

end

context bounded_semilattice_inf_top
begin

abbreviation "filter_complements F G \<equiv> filter F \<and> filter G \<and> filter_sup F G = UNIV \<and> F \<inter> G = {top}"

end

text \<open>
The set of filters over a bounded semilattice forms a bounded lattice.
\<close>

instantiation filter :: (bounded_semilattice_inf_top) bounded_lattice
begin

lift_definition bot_filter :: "'a filter" is "{top}"
  by simp

instance
  by intro_classes (simp add: less_eq_filter.rep_eq bot_filter.rep_eq)

end

context lattice
begin

lemma up_dist_sup:
  "\<up>(x \<squnion> y) = \<up>x \<inter> \<up>y"
  by auto

end

text \<open>
For convenience, the following function injects principal filters into the filter type.
We cannot define it in the \<open>order\<close> class since the type filter requires the sort constraint \<open>order\<close> that is not available in the class.
The result of the function is a filter by lemma \<open>up_filter\<close>.
\<close>

abbreviation up_filter :: "'a::order \<Rightarrow> 'a filter"
  where "up_filter x \<equiv> Abs_filter (\<up>x)"

lemma up_filter_dist_inf:
  "up_filter ((x::'a::lattice) \<sqinter> y) = up_filter x \<squnion> up_filter y"
  by (simp add: eq_onp_def sup_filter.abs_eq up_dist_inf)

lemma up_filter_dist_sup:
  "up_filter ((x::'a::lattice) \<squnion> y) = up_filter x \<sqinter> up_filter y"
  by (metis eq_onp_def inf_filter.abs_eq up_dist_sup up_filter)

lemma up_filter_injective:
  "up_filter x = up_filter y \<Longrightarrow> x = y"
  by (metis Abs_filter_inject mem_Collect_eq up_filter up_injective)

lemma up_filter_antitone:
  "x \<le> y \<longleftrightarrow> up_filter y \<le> up_filter x"
  by (metis eq_onp_same_args less_eq_filter.abs_eq up_antitone up_filter)

text \<open>
The following definition applies a function to each element of a filter.
The subsequent lemma gives conditions under which the result of this application is a filter.
\<close>

abbreviation filter_map :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a filter \<Rightarrow> 'b filter"
  where "filter_map f F \<equiv> Abs_filter (f ` Rep_filter F)"

lemma filter_map_filter:
  assumes "mono f"
      and "\<forall>x y . f x \<le> y \<longrightarrow> (\<exists>z . x \<le> z \<and> y = f z)"
    shows "filter (f ` Rep_filter F)"
proof (unfold filter_def, intro conjI)
  show "f ` Rep_filter F \<noteq> {}"
    by (metis empty_is_image filter_def simp_filter)
next
  show "\<forall>x\<in>f ` Rep_filter F . \<forall>y\<in>f ` Rep_filter F . \<exists>z\<in>f ` Rep_filter F . z \<le> x \<and> z \<le> y"
  proof (intro ballI)
    fix x y
    assume "x \<in> f ` Rep_filter F" and "y \<in> f ` Rep_filter F"
    then obtain u v where 1: "x = f u \<and> u \<in> Rep_filter F \<and> y = f v \<and> v \<in> Rep_filter F"
      by auto
    then obtain w where "w \<le> u \<and> w \<le> v \<and> w \<in> Rep_filter F"
      by (meson filter_def simp_filter)
    thus "\<exists>z\<in>f ` Rep_filter F . z \<le> x \<and> z \<le> y"
      using 1 assms(1) mono_def rev_image_eqI by blast
  qed
next
  show "is_up_set (f ` Rep_filter F)"
  proof
    fix x
    assume "x \<in> f ` Rep_filter F"
    then obtain u where 1: "x = f u \<and> u \<in> Rep_filter F"
      by auto
    show "\<forall>y . x \<le> y \<longrightarrow> y \<in> f ` Rep_filter F"
    proof (rule allI, rule impI)
      fix y
      assume "x \<le> y"
      hence "f u \<le> y"
        using 1 by simp
      then obtain z where "u \<le> z \<and> y = f z"
        using assms(2) by auto
      thus "y \<in> f ` Rep_filter F"
        using 1 by (meson image_iff filter_def simp_filter)
    qed
  qed
qed

subsection \<open>Distributive Lattices\<close>

text \<open>
In this section we additionally assume that the underlying order forms a distributive lattice.
Then filters form a bounded distributive lattice if the underlying order has a greatest element.
Moreover ultrafilters are prime filters.
We also prove a lemma of Gr\"atzer and Schmidt about principal filters.
\<close>

context distrib_lattice
begin

lemma filter_sup_left_dist_inf:
  assumes "filter F"
      and "filter G"
      and "filter H"
    shows "filter_sup F (G \<inter> H) = filter_sup F G \<inter> filter_sup F H"
proof
  show "filter_sup F (G \<inter> H) \<subseteq> filter_sup F G \<inter> filter_sup F H"
    using filter_sup_right_isotone_var by blast
next
  show "filter_sup F G \<inter> filter_sup F H \<subseteq> filter_sup F (G \<inter> H)"
  proof
    fix x
    assume "x \<in> filter_sup F G \<inter> filter_sup F H"
    then obtain t u v w where 1: "t \<in> F \<and> u \<in> G \<and> v \<in> F \<and> w \<in> H \<and> t \<sqinter> u \<le> x \<and> v \<sqinter> w \<le> x"
      by auto
    let ?y = "t \<sqinter> v"
    let ?z = "u \<squnion> w"
    have 2: "?y \<in> F"
      using 1 by (simp add: assms(1) filter_inf_closed)
    have 3: "?z \<in> G \<inter> H"
      using 1 by (meson assms(2-3) Int_iff filter_def sup_ge1 sup_ge2)
    have "?y \<sqinter> ?z = (t \<sqinter> v \<sqinter> u) \<squnion> (t \<sqinter> v \<sqinter> w)"
      by (simp add: inf_sup_distrib1)
    also have "... \<le> (t \<sqinter> u) \<squnion> (v \<sqinter> w)"
      by (metis inf.cobounded1 inf.cobounded2 inf.left_idem inf_mono sup.mono)
    also have "... \<le> x"
      using 1 by (simp add: le_supI)
    finally show "x \<in> filter_sup F (G \<inter> H)"
      using 2 3 by blast
  qed
qed

lemma filter_inf_principal_rep:
  "F \<inter> G = \<up>z \<Longrightarrow> (\<exists>x\<in>F . \<exists>y\<in>G . z = x \<squnion> y)"
  by force

lemma filter_sup_principal_rep:
  assumes "filter F"
      and "filter G"
      and "filter_sup F G = \<up>z"
    shows "\<exists>x\<in>F . \<exists>y\<in>G . z = x \<sqinter> y"
proof -
  from assms(3) obtain x y where 1: "x\<in>F \<and> y\<in>G \<and> x \<sqinter> y \<le> z"
    using order_refl by blast
  hence 2: "x \<squnion> z \<in> F \<and> y \<squnion> z \<in> G"
    by (meson assms(1-2) sup_ge1 filter_def)
  have "(x \<squnion> z) \<sqinter> (y \<squnion> z) = z"
    using 1 sup_absorb2 sup_inf_distrib2 by fastforce
  thus ?thesis
    using 2 by force
qed

lemma inf_sup_principal_aux:
  assumes "filter F"
      and "filter G"
      and "is_principal_up (filter_sup F G)"
      and "is_principal_up (F \<inter> G)"
    shows "is_principal_up F"
proof -
  from assms(3-4) obtain x y where 1: "filter_sup F G = \<up>x \<and> F \<inter> G = \<up>y"
    by blast
  from filter_inf_principal_rep obtain t u where 2: "t\<in>F \<and> u\<in>G \<and> y = t \<squnion> u"
    using 1 by meson
  from filter_sup_principal_rep obtain v w where 3: "v\<in>F \<and> w\<in>G \<and> x = v \<sqinter> w"
    using 1 by (meson assms(1-2))
  have "t \<in> filter_sup F G \<and> u \<in> filter_sup F G"
    using 2 inf.cobounded1 inf.cobounded2 by blast
  hence "x \<le> t \<and> x \<le> u"
    using 1 by blast
  hence 4: "(t \<sqinter> v) \<sqinter> (u \<sqinter> w) = x"
    using 3 by (simp add: inf.absorb2 inf.assoc inf.left_commute)
  have "(t \<sqinter> v) \<squnion> (u \<sqinter> w) \<in> F \<and> (t \<sqinter> v) \<squnion> (u \<sqinter> w) \<in> G"
    using 2 3 by (metis (no_types, lifting) assms(1-2) filter_inf_closed sup.cobounded1 sup.cobounded2 filter_def)
  hence "y \<le> (t \<sqinter> v) \<squnion> (u \<sqinter> w)"
    using 1 Int_iff by blast
  hence 5: "(t \<sqinter> v) \<squnion> (u \<sqinter> w) = y"
    using 2 by (simp add: antisym inf.coboundedI1)
  have "F = \<up>(t \<sqinter> v)"
  proof
    show "F \<subseteq> \<up>(t \<sqinter> v)"
    proof
      fix z
      assume 6: "z \<in> F"
      hence "z \<in> filter_sup F G"
        using 2 inf.cobounded1 by blast
      hence "x \<le> z"
        using 1 by simp
      hence 7: "(t \<sqinter> v \<sqinter> z) \<sqinter> (u \<sqinter> w) = x"
        using 4 by (metis inf.absorb1 inf.assoc inf.commute)
      have "z \<squnion> u \<in> F \<and> z \<squnion> u \<in> G \<and> z \<squnion> w \<in> F \<and> z \<squnion> w \<in> G"
        using 2 3 6 by (meson assms(1-2) filter_def sup_ge1 sup_ge2)
      hence "y \<le> (z \<squnion> u) \<sqinter> (z \<squnion> w)"
        using 1 Int_iff filter_inf_closed by auto
      hence 8: "(t \<sqinter> v \<sqinter> z) \<squnion> (u \<sqinter> w) = y"
        using 5 by (metis inf.absorb1 sup.commute sup_inf_distrib2)
      have "t \<sqinter> v \<sqinter> z = t \<sqinter> v"
        using 4 5 7 8 relative_equality by blast
      thus "z \<in> \<up>(t \<sqinter> v)"
        by (simp add: inf.orderI)
    qed
  next
    show "\<up>(t \<sqinter> v) \<subseteq> F"
    proof
      fix z
      have 9: "t \<sqinter> v \<in> F"
        using 2 3 by (simp add: assms(1) filter_inf_closed)
      assume "z \<in> \<up>(t \<sqinter> v)"
      hence "t \<sqinter> v \<le> z" by simp
      thus "z \<in> F"
        using assms(1) 9 filter_def by auto
    qed
  qed
  thus ?thesis
    by blast
qed

text \<open>
The following result is \cite[Lemma II]{GraetzerSchmidt1958}.
If both join and meet of two filters are principal filters, both filters are principal filters.
\<close>

lemma inf_sup_principal:
  assumes "filter F"
      and "filter G"
      and "is_principal_up (filter_sup F G)"
      and "is_principal_up (F \<inter> G)"
    shows "is_principal_up F \<and> is_principal_up G"
proof -
  have "filter G \<and> filter F \<and> is_principal_up (filter_sup G F) \<and> is_principal_up (G \<inter> F)"
    by (simp add: assms Int_commute filter_sup_symmetric)
  thus ?thesis
    using assms(3) inf_sup_principal_aux by blast
qed

lemma filter_sup_absorb_inf: "filter F \<Longrightarrow> filter G \<Longrightarrow> filter_sup (F \<inter> G) G = G"
  by (simp add: filter_inf filter_sup_least_upper_bound filter_sup_left_upper_bound filter_sup_symmetric subset_antisym)

lemma filter_inf_absorb_sup: "filter F \<Longrightarrow> filter G \<Longrightarrow> filter_sup F G \<inter> G = G"
  apply (rule subset_antisym)
  apply simp
  by (simp add: filter_sup_right_upper_bound)

lemma filter_inf_right_dist_sup:
  assumes "filter F"
      and "filter G"
      and "filter H"
    shows "filter_sup F G \<inter> H = filter_sup (F \<inter> H) (G \<inter> H)"
proof -
  have "filter_sup (F \<inter> H) (G \<inter> H) = filter_sup (F \<inter> H) G \<inter> filter_sup (F \<inter> H) H"
    by (simp add: assms filter_sup_left_dist_inf filter_inf)
  also have "... = filter_sup (F \<inter> H) G \<inter> H"
    using assms(1,3) filter_sup_absorb_inf by simp
  also have "... = filter_sup F G \<inter> filter_sup G H \<inter> H"
    using assms filter_sup_left_dist_inf filter_sup_symmetric by simp
  also have "... = filter_sup F G \<inter> H"
    by (simp add: assms(2-3) filter_inf_absorb_sup semilattice_inf_class.inf_assoc)
  finally show ?thesis
    by simp
qed

text \<open>
The following result generalises \cite[10.11]{DaveyPriestley2002} to distributive lattices as remarked after that section.
\<close>

lemma ultra_filter_prime:
  assumes "ultra_filter F"
    shows "prime_filter F"
proof -
  {
    fix x y
    assume 1: "x \<squnion> y \<in> F \<and> x \<notin> F"
    let ?G = "\<Up>{ z . \<exists>w\<in>F . x \<sqinter> w = z }"
    have 2: "filter ?G"
      using assms filter_inf_filter by simp
    have "x \<in> ?G"
      using 1 by auto
    hence 3: "F \<noteq> ?G"
      using 1 by auto
    have "F \<subseteq> ?G"
      using inf_le2 order_trans by blast
    hence "?G = UNIV"
      using 2 3 assms by blast
    then obtain z where 4: "z \<in> F \<and> x \<sqinter> z \<le> y"
      by blast
    hence "y \<sqinter> z = (x \<squnion> y) \<sqinter> z"
      by (simp add: inf_sup_distrib2 sup_absorb2)
    also have "... \<in> F"
      using 1 4 assms filter_inf_closed by auto
    finally have "y \<in> F"
      using assms by (simp add: filter_def)
  }
  thus ?thesis
    using assms by blast
qed

end

context distrib_lattice_bot
begin

lemma prime_filter:
  "proper_filter F \<Longrightarrow> \<exists>G . prime_filter G \<and> F \<subseteq> G"
  by (metis ultra_filter ultra_filter_prime)

end

context distrib_lattice_top
begin

lemma complemented_filter_inf_principal:
  assumes "filter_complements F G"
    shows "is_principal_up (F \<inter> \<up>x)"
proof -
  have 1: "filter F \<and> filter G"
    by (simp add: assms)
  hence 2: "filter (F \<inter> \<up>x) \<and> filter (G \<inter> \<up>x)"
    by (simp add: filter_inf)
  have "(F \<inter> \<up>x) \<inter> (G \<inter> \<up>x) = {top}"
    using assms Int_assoc Int_insert_left_if1 inf_bot_left inf_sup_aci(3) top_in_upset inf.idem by auto
  hence 3: "is_principal_up ((F \<inter> \<up>x) \<inter> (G \<inter> \<up>x))"
    using up_top by blast
  have "filter_sup (F \<inter> \<up>x) (G \<inter> \<up>x) = filter_sup F G \<inter> \<up>x"
    using 1 filter_inf_right_dist_sup up_filter by auto
  also have "... = \<up>x"
    by (simp add: assms)
  finally have "is_principal_up (filter_sup (F \<inter> \<up>x) (G \<inter> \<up>x))"
    by auto
  thus ?thesis
    using 1 2 3 inf_sup_principal_aux by blast
qed

end

text \<open>
The set of filters over a distributive lattice with a greatest element forms a bounded distributive lattice.
\<close>

instantiation filter :: (distrib_lattice_top) bounded_distrib_lattice
begin

instance
proof
  fix x y z :: "'a filter"
  have "Rep_filter (x \<squnion> (y \<sqinter> z)) = filter_sup (Rep_filter x) (Rep_filter (y \<sqinter> z))"
    by (simp add: sup_filter.rep_eq)
  also have "... = filter_sup (Rep_filter x) (Rep_filter y \<inter> Rep_filter z)"
    by (simp add: inf_filter.rep_eq)
  also have "... = filter_sup (Rep_filter x) (Rep_filter y) \<inter> filter_sup (Rep_filter x) (Rep_filter z)"
    by (simp add: filter_sup_left_dist_inf)
  also have "... = Rep_filter (x \<squnion> y) \<inter> Rep_filter (x \<squnion> z)"
    by (simp add: sup_filter.rep_eq)
  also have "... = Rep_filter ((x \<squnion> y) \<sqinter> (x \<squnion> z))"
    by (simp add: inf_filter.rep_eq)
  finally show "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
    by (simp add: Rep_filter_inject)
qed

end

end

