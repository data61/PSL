(*
Title: Binary Multirelations
Author: Hitoshi Furusawa, Georg Struth
Maintainer: <g.struth at sheffield.ac.uk>
*)

section \<open>C-Algebras\<close>

theory C_Algebras
imports Kleene_Algebra.Dioid 
begin

no_notation
  times (infixl "\<cdot>" 70)

subsection \<open>C-Monoids\<close>

text \<open>We start with the c-monoid axioms. These can be found in Section~4 of~\cite{FurusawaS15a}.\<close>

class proto_monoid = 
  fixes s_id :: "'a" ("1\<^sub>\<sigma>")
  and s_prod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<cdot>" 80) 
  assumes s_prod_idl [simp]: "1\<^sub>\<sigma> \<cdot> x = x"
  and  s_prod_idr [simp]: "x \<cdot> 1\<^sub>\<sigma>  = x"

class proto_bi_monoid = proto_monoid +
  fixes c_id :: "'a" ("1\<^sub>\<pi>")
  and c_prod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<parallel>" 80) 
  assumes c_prod_idl [simp]: "1\<^sub>\<pi> \<parallel> x = x"
  and c_prod_assoc: "(x \<parallel> y) \<parallel> z = x \<parallel> (y \<parallel> z)"
  and c_prod_comm: "x \<parallel> y = y \<parallel> x" 

class c_monoid = proto_bi_monoid +
  assumes c1 [simp]: "(x \<cdot> 1\<^sub>\<pi>) \<parallel> x = x"
  and c2 [simp]: "((x \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>) \<cdot> y = (x \<cdot> 1\<^sub>\<pi>) \<parallel> y" 
  and c3: "(x \<parallel> y) \<cdot> 1\<^sub>\<pi> = (x \<cdot> 1\<^sub>\<pi>) \<parallel> (y \<cdot> 1\<^sub>\<pi>)"
  and c4: "(x \<cdot> y) \<cdot> 1\<^sub>\<pi> = x \<cdot> (y \<cdot> 1\<^sub>\<pi>)"
  and c5 [simp]: "1\<^sub>\<sigma> \<parallel> 1\<^sub>\<sigma> = 1\<^sub>\<sigma>"

begin

text \<open>Next we define domain explicitly as at the beginning of Section 4 in~\cite{FurusawaS15a} 
and start proving the algebraic facts from Section 4. Those involving concrete multirelations, such as Proposition 4.1,
are considered in the theory file for multirelations.\<close>

definition (in c_monoid) d :: "'a \<Rightarrow> 'a" where
  "d x = (x \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>" 

lemma c_prod_idr [simp]: "x \<parallel> 1\<^sub>\<pi> = x"
  by (simp add: local.c_prod_comm)

text \<open>We prove the retraction properties of Lemma 4.2.\<close>

lemma c_idem [simp]: "1\<^sub>\<pi> \<cdot> 1\<^sub>\<pi> = 1\<^sub>\<pi>"
  by (metis c_prod_idr local.c1)

lemma d_idem [simp]: "d (d x) = d x"
  by (simp add: local.d_def)

lemma p_id_idem: "(x \<cdot> 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi> = x \<cdot> 1\<^sub>\<pi>"
  by (simp add: local.c4)

text \<open>Lemma 4.3.\<close>

lemma c2_d: "d x \<cdot> y = (x \<cdot> 1\<^sub>\<pi>) \<parallel> y"
  by (simp add: local.d_def)

lemma cd_2_var: "d (x \<cdot> 1\<^sub>\<pi>) \<cdot> y = (x \<cdot> 1\<^sub>\<pi>) \<parallel> y"
  by (simp add: c2_d local.c4)

lemma dc_prop1 [simp]: "d x \<cdot> 1\<^sub>\<pi> = x \<cdot> 1\<^sub>\<pi>"
  by (simp add: c2_d)

lemma dc_prop2 [simp]: "d (x \<cdot> 1\<^sub>\<pi>) = d x"
  by (simp add: local.c4 local.d_def)

lemma ds_prop [simp]: "d x \<parallel> 1\<^sub>\<sigma> = d x"
  by (simp add: local.c_prod_assoc local.d_def)

lemma dc [simp]: "d 1\<^sub>\<pi> = 1\<^sub>\<sigma>"
  by (simp add: local.d_def)

text \<open>Part (5) of this Lemma has already been verified above. The next two statements 
verify the two algebraic properties mentioned in the proof of Proposition 4.4.\<close>

lemma dc_iso [simp]: "d (d x \<cdot> 1\<^sub>\<pi>) = d x"
  by simp

lemma cd_iso [simp]: "d (x \<cdot> 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi> = x \<cdot> 1\<^sub>\<pi>"
  by simp

text \<open>Proposition 4.5.\<close>

lemma d_conc6: "d (x \<parallel> y) = d x \<parallel> d y"
proof - 
  have "d (x \<parallel> y) = ((x \<parallel> y) \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>"
    by (simp add: local.d_def)
  also have "... = (x \<cdot> 1\<^sub>\<pi>) \<parallel> (y \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>"
    by (simp add: local.c3)
  finally show ?thesis
    by (metis ds_prop local.c_prod_assoc local.c_prod_comm local.d_def)
qed

lemma d_conc_s_prod_ax: "d x \<parallel> d y = d x \<cdot> d y"
proof - 
  have "d x \<parallel> d y = (x \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma> \<parallel> d y"
    using local.d_def by presburger
  also have "... = (x \<cdot> 1\<^sub>\<pi>) \<parallel> d y"
    using d_conc6 local.c3 local.c_prod_assoc local.d_def by auto
  also have "... = ((x \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>) \<cdot> d y"
    by simp
  finally show ?thesis
    using local.d_def by auto
qed

lemma d_rest_ax [simp]: "d x \<cdot> x = x"
  by (simp add: c2_d)

lemma d_loc_ax [simp]: "d (x \<cdot> d y) = d (x \<cdot> y)"
proof - 
  have "d (x \<cdot> d y) = (x \<cdot> d y \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>"
    by (simp add: local.d_def)
  also have "... = (x \<cdot> y \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>"
    by (simp add: local.c4)
  finally show ?thesis
    by (simp add: local.d_def)
qed

lemma d_exp_ax [simp]: "d (d x \<cdot> y) = d x \<cdot> d y"
proof -
  have "d (d x \<cdot> y) = d (d x \<cdot> d y)"
    by (simp add: d_conc6)
  also have "... = d (d (x \<parallel> y))"
    by (simp add: d_conc6 d_conc_s_prod_ax)
  also have "... = d (x \<parallel> y)"
    by simp
  finally show ?thesis
    by (simp add: d_conc6 d_conc_s_prod_ax)
qed

lemma d_comm_ax: "d x \<cdot> d y = d y \<cdot> d x"
proof -
  have "(d x) \<cdot> (d y) = d (x \<parallel> y)"
    by (simp add: d_conc6 d_conc_s_prod_ax)
  also have "... = d (y \<parallel> x)"
    using local.c_prod_comm by auto
  finally show ?thesis
    by (simp add: d_conc6 d_conc_s_prod_ax)
qed

lemma d_s_id_prop [simp]: "d 1\<^sub>\<sigma> = 1\<^sub>\<sigma>"
  using local.d_def by auto

text \<open>Next we verify the conditions of Proposition 4.6.\<close>

lemma d_s_prod_closed [simp]: "d (d x \<cdot> d y) = d x \<cdot> d y"
  by simp

lemma d_p_prod_closed [simp]: "d (d x \<parallel> d y) = d x \<parallel> d y"
  using c2_d d_conc6 by auto

lemma d_idem2 [simp]: "d x \<cdot> d x = d x"
  by (metis d_exp_ax d_rest_ax)

lemma d_assoc: "(d x \<cdot> d y) \<cdot> d z = d x \<cdot> (d y \<cdot> d z)"
proof -
  have "\<And>x y. d x \<cdot> d y = d (x \<parallel> y)"
    by (simp add: d_conc6 d_conc_s_prod_ax)
  thus ?thesis
    by (simp add: local.c_prod_assoc)
qed

lemma iso_1 [simp]: "(d x \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma> = d x"
  by (simp add: local.d_def)

text \<open>Lemma 4.7.\<close>

lemma x_c_par_idem [simp]: "(x \<cdot> 1\<^sub>\<pi>) \<parallel> (x \<cdot> 1\<^sub>\<pi>) = x \<cdot> 1\<^sub>\<pi>"
proof -
  have "(x \<cdot> 1\<^sub>\<pi>) \<parallel> (x \<cdot> 1\<^sub>\<pi>) = d x \<cdot> (x \<cdot> 1\<^sub>\<pi>)"
    using c2_d by auto
  also have "... = d (x \<cdot> 1\<^sub>\<pi>) \<cdot> (x \<cdot> 1\<^sub>\<pi>)"
    by simp
  finally show ?thesis
    using d_rest_ax by presburger
qed

lemma d_idem_par [simp]: "d x \<parallel> d x = d x "
  by (simp add: d_conc_s_prod_ax)

lemma d_inter_r: "d x \<cdot> (y \<parallel> z) = (d x \<cdot> y) \<parallel> (d x \<cdot> z)"
proof -
  have "(d x) \<cdot> (y \<parallel> z) = (x \<cdot> 1\<^sub>\<pi>) \<parallel> y \<parallel> z"
    using c2_d local.c_prod_assoc by auto
  also have "... = (x \<cdot> 1\<^sub>\<pi>) \<parallel> y \<parallel> (x \<cdot> 1\<^sub>\<pi>) \<parallel> z"
    using local.c_prod_assoc local.c_prod_comm by force
  finally show ?thesis
    by (simp add: c2_d local.c_prod_assoc)
qed

text \<open>Now we provide the counterexamples of Lemma 4.8.\<close>

lemma "(x \<parallel> y) \<cdot> d z = (x \<cdot> d z) \<parallel> (y \<cdot> d z)"
  nitpick
  oops

lemma "(x \<cdot> y) \<cdot> d z = x \<cdot> (y \<cdot> d z)"
  nitpick
  oops

lemma "1\<^sub>\<pi> \<cdot> x = 1\<^sub>\<pi>"
  nitpick
  oops

end

subsection \<open>C-Trioids\<close>

text \<open>We can now define the class of c-trioids and prove properties in this class. This covers 
the algebraic material of Section 5 in~\cite{FurusawaS15a}.\<close>

class proto_dioid = join_semilattice_zero + proto_monoid +
  assumes  s_prod_distr: "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
  and  s_prod_subdistl: "x \<cdot> y + x \<cdot> z \<le> x \<cdot> (y + z)"
  and  s_prod_annil [simp]: "0 \<cdot> x = 0"

begin

lemma s_prod_isol: "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"
  by (metis join.sup.boundedE order_prop s_prod_subdistl)

lemma s_prod_isor: "x \<le> y \<Longrightarrow> x \<cdot> z \<le> y \<cdot> z"
  using local.order_prop local.s_prod_distr by auto

end

class proto_trioid = proto_dioid + proto_bi_monoid +
  assumes  p_prod_distl: "x \<parallel> (y + z) = x \<parallel> y + x \<parallel> z"
  and  p_rpd_annir [simp]: "x \<parallel> 0 = 0"

sublocale proto_trioid \<subseteq> ab_semigroup_mult c_prod
proof
  fix x y z
  show  "x \<parallel> y \<parallel> z = x \<parallel> (y \<parallel> z)"
    by (rule c_prod_assoc)
  show "x \<parallel> y = y \<parallel> x"
    by (rule c_prod_comm)
qed

sublocale proto_trioid \<subseteq> dioid_one_zero "(+)" "(\<parallel>)" "1\<^sub>\<pi>" 0 "(\<le>)" "(<)"
proof
  fix x y z
  show "(x + y) \<parallel> z = x \<parallel> z + y \<parallel> z"
    by (simp add: local.c_prod_comm local.p_prod_distl)
  show "1\<^sub>\<pi> \<parallel> x = x"
    using local.c_prod_idl by blast
  show "x \<parallel> 1\<^sub>\<pi> = x"
    by (simp add: local.mult_commute)
  show "0 + x = x"
    by (rule add.left_neutral)
  show "0 \<parallel> x = 0"
    by (simp add: local.mult_commute)
  show "x \<parallel> 0 = 0"
    by (rule p_rpd_annir)
  show "x + x = x"
    by (rule add_idem)
  show "x \<parallel> (y + z) = x \<parallel> y + x \<parallel> z"
    by (rule p_prod_distl)
qed

class c_trioid = proto_trioid + c_monoid +
  assumes  c6: "x \<cdot> 1\<^sub>\<pi> \<le> 1\<^sub>\<pi>"

begin

text \<open>We show that every c-trioid is a c-monoid.\<close>

subclass c_monoid ..

subclass proto_trioid ..

lemma "1\<^sub>\<pi> \<cdot> 0 = 1\<^sub>\<pi>"
  nitpick
  oops

lemma zero_p_id_prop [simp]: "(x \<cdot> 0) \<cdot> 1\<^sub>\<pi> = x \<cdot> 0"
  by (simp add: local.c4)

text \<open>The following facts prove and refute properties related to sequential and parallel subidentities.\<close>

lemma d_subid: "d x = x \<Longrightarrow> x \<le> 1\<^sub>\<sigma>"
  by (metis local.c6 local.c_idem local.d_def local.dc local.mult_isor)

lemma "x \<le> 1\<^sub>\<sigma> \<Longrightarrow> d x = x"
  nitpick
  oops 

lemma p_id_term: "x \<cdot> 1\<^sub>\<pi> = x \<Longrightarrow> x \<le> 1\<^sub>\<pi>"
  by (metis local.c6)

lemma "x \<le> 1\<^sub>\<pi> \<Longrightarrow> x \<cdot> 1\<^sub>\<pi> = x"
  nitpick
  oops

text \<open>Proposition 5.1. is covered by the theory file on multirelations. 
We verify the remaining conditions in Proposition 5.2.\<close>

lemma dlp_ax: "x \<le> d x \<cdot> x"
  by simp

lemma d_add_ax: "d (x + y) = d x + d y"
proof -
  have "d (x + y) = ((x + y) \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>"
    using local.d_def by blast
  also have "... = (x \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma> + (y \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>"
    by (simp add: local.distrib_right local.s_prod_distr)
  finally show ?thesis
    by (simp add: local.d_def)
qed

lemma d_sub_id_ax: "d x \<le> 1\<^sub>\<sigma>"
proof - 
  have "d x = (x \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>"
    by (simp add: local.d_def)
  also have "... \<le> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<sigma>"
    using local.c6 local.mult_isor by blast
  finally show ?thesis
    by simp
qed

lemma d_zero_ax [simp]: "d 0 = 0"
  by (simp add: local.d_def)

text\<open>We verify the algebraic conditions in Proposition 5.3.\<close>

lemma d_absorb1 [simp]: "d x + (d x \<cdot> d y) = d x"
proof (rule antisym)
  have "d x + (d x \<cdot> d y) \<le> d x + (d x \<cdot> 1\<^sub>\<sigma>)"
    by (metis d_sub_id_ax c2_d d_def join.sup.bounded_iff join.sup.semilattice_axioms join.sup_ge1 s_prod_isol semilattice.idem)
  thus "d x + (d x \<cdot> d y) \<le> d x"
    by simp
  show "d x \<le> d x + ((d x) \<cdot> (d y))"
    using join.sup_ge1 by blast
qed

lemma d_absorb2 [simp]: "d x \<cdot> (d x + d y) = d x"
proof -
  have "x \<cdot> 1\<^sub>\<pi> \<parallel> d x = d x"
    by (metis local.c1 local.dc_prop1)
  thus ?thesis
  by (metis d_absorb1 local.c2_d local.p_prod_distl)
qed

lemma d_dist1: "d x \<cdot> (d y + d z) = d x \<cdot> d y + d x \<cdot> d z"
  by (simp add: local.c2_d local.p_prod_distl)

lemma d_dist2: "d x + (d y \<cdot> d z) = (d x + d y) \<cdot> (d x + d z)"
proof -
  have "(d x + d y) \<cdot> (d x + d z) = d x \<cdot> d x + d x \<cdot> d z + d y \<cdot> d x + d y \<cdot> d z"
    using add_assoc d_dist1 local.s_prod_distr by force
  also have "... = d x + d x \<cdot> d z + d x \<cdot> d y + d y \<cdot> d z"
    using local.d_comm_ax by auto
  finally show ?thesis
    by simp
qed

lemma d_add_prod_closed [simp]: "d (d x + d y) = d x + d y"
  by (simp add: d_add_ax)

text \<open>The following properties are not covered in the article.\<close>

lemma x_zero_prop: "(x \<cdot> 0) \<parallel> y = d (x \<cdot> 0) \<cdot> y"
  by (simp add: local.c2_d)

lemma cda_add_ax: "d ((x + y) \<cdot> z) = d (x \<cdot> z) + d (y \<cdot> z)"
  by (simp add: d_add_ax local.s_prod_distr)

lemma d_x_zero: "d (x \<cdot> 0) = (x \<cdot> 0) \<parallel> 1\<^sub>\<sigma>"
  by (simp add: x_zero_prop)

text \<open>Lemma 5.4 is verified below because its proofs are simplified by using facts from the next subsection.\<close>

subsection \<open>Results for Concurrent Dynamic Algebra\<close>

text \<open>The following proofs and refutation are related to Section 6 in~\cite{FurusawaS15a}. 
We do not consider those involving Kleene algebras in this section. We also do not introduce specific 
notation for diamond operators.\<close>

text \<open>First we prove Lemma 6.1. Part (1) and (3) have already been verified above. Part (2) and (4) require
additional assumptions which are present in the context of concurrent dynamic algebra~\cite{FurusawaS15b}. We
also present the counterexamples from Lemma 6.3.\<close>

lemma "(x \<cdot> y) \<cdot> d z = x \<cdot> (y \<cdot> d z)"
  nitpick
  oops

lemma "d((x \<cdot> y) \<cdot> z) = d (x \<cdot> d (y \<cdot> z))"
  nitpick 
  oops

lemma  cda_ax1: "(x \<cdot> y) \<cdot> d z = x \<cdot> (y \<cdot> d z) \<Longrightarrow> d((x \<cdot> y) \<cdot> z) = d (x \<cdot> d (y \<cdot> z))"
  by (metis local.d_loc_ax)

lemma d_inter: "(x \<parallel> y) \<cdot> d z = (x \<cdot> d z) \<parallel> (y \<cdot> d z)"
  nitpick
  oops

lemma "d ((x \<parallel> y) \<cdot> z) = d (x \<cdot> z) \<cdot> d (y \<cdot> z)"
  nitpick
  oops

lemma cda_ax2: 
assumes "(x \<parallel> y) \<cdot> d z = (x \<cdot> d z) \<parallel> (y \<cdot> d z)" 
shows "d ((x \<parallel> y) \<cdot> z) = d (x \<cdot> z) \<cdot> d (y \<cdot> z)"
  by (metis assms local.d_conc6 local.d_conc_s_prod_ax local.d_loc_ax)

text \<open>Next we present some results that do not feature in the article.\<close>

lemma "(x \<cdot> y) \<cdot> 0 = x \<cdot> (y \<cdot> 0)"
nitpick
oops

lemma d_x_zero_prop [simp]: "d (x \<cdot> 0) \<cdot> 1\<^sub>\<pi> = x \<cdot> 0"
  by simp

lemma "x \<le> 1\<^sub>\<sigma> \<and> y \<le> 1\<^sub>\<sigma> \<longrightarrow> x \<cdot> y = x \<parallel> y"
nitpick
oops

lemma "x \<cdot> (y \<parallel> z) \<le> (x \<cdot> y) \<parallel> (x \<cdot> z)"
nitpick
oops

lemma "x \<le> x \<parallel> x"
nitpick
oops

text \<open>Lemma 5.4\<close> 

lemma d_lb1: "d x \<cdot> d y \<le> d x"
  by (simp add: less_eq_def add_commute)

lemma d_lb2: "d x \<cdot> d y \<le> d y"
  using d_lb1 local.d_comm_ax by fastforce

lemma d_glb: "d z \<le> d x \<and> d z \<le> d y \<Longrightarrow> d z \<le> d x \<cdot> d y"
  by (simp add: d_dist2 local.less_eq_def)

lemma d_glb_iff: "d z \<le> d x \<and> d z \<le> d y \<longleftrightarrow> d z \<le> d x \<cdot> d y"
  using d_glb d_lb1 d_lb2 local.order_trans by blast

lemma x_zero_le_c: "x \<cdot> 0 \<le> 1\<^sub>\<pi>"
  by (simp add: p_id_term)

lemma p_subid_lb1: "(x \<cdot> 0) \<parallel> (y \<cdot> 0) \<le> x \<cdot> 0"
  using local.mult_isol x_zero_le_c by fastforce

lemma p_subid_lb2: "(x \<cdot> 0) \<parallel> (y \<cdot> 0) \<le> y \<cdot> 0"
  using local.mult_commute p_subid_lb1 by fastforce

lemma p_subid_idem [simp]: "(x \<cdot> 0) \<parallel> (x \<cdot> 0) = x \<cdot> 0"
  by (metis local.c1 zero_p_id_prop)

lemma p_subid_glb: "z \<cdot> 0 \<le> x \<cdot> 0 \<and> z \<cdot> 0 \<le> y \<cdot> 0 \<Longrightarrow> z \<cdot> 0 \<le> (x \<cdot> 0) \<parallel> (y \<cdot> 0)"
  using local.mult_isol_var by force

lemma p_subid_glb_iff: "z \<cdot> 0 \<le> x \<cdot> 0 \<and> z \<cdot> 0 \<le> y \<cdot> 0 \<longleftrightarrow> z \<cdot> 0 \<le> (x \<cdot> 0) \<parallel> (y \<cdot> 0)"
  using local.order_trans p_subid_glb p_subid_lb1 p_subid_lb2 by blast

lemma x_c_glb: "z \<cdot> 1\<^sub>\<pi> \<le> x \<cdot> 1\<^sub>\<pi> \<and> z \<cdot> 1\<^sub>\<pi> \<le> y \<cdot> 1\<^sub>\<pi> \<Longrightarrow> z \<cdot> 1\<^sub>\<pi> \<le> (x \<cdot> 1\<^sub>\<pi>) \<parallel> (y \<cdot> 1\<^sub>\<pi>)"
  using local.mult_isol_var by force

lemma x_c_lb1: "(x \<cdot> 1\<^sub>\<pi>) \<parallel> (y \<cdot> 1\<^sub>\<pi>) \<le> x \<cdot> 1\<^sub>\<pi>"
  using local.c6 local.mult_isol_var by force
 
lemma x_c_lb2: "(x \<cdot> 1\<^sub>\<pi>) \<parallel> (y \<cdot> 1\<^sub>\<pi>) \<le> y \<cdot> 1\<^sub>\<pi>"
  using local.mult_commute x_c_lb1 by fastforce

lemma x_c_glb_iff: "z \<cdot> 1\<^sub>\<pi> \<le> x \<cdot> 1\<^sub>\<pi> \<and> z \<cdot> 1\<^sub>\<pi> \<le> y \<cdot> 1\<^sub>\<pi> \<longleftrightarrow> z \<cdot> 1\<^sub>\<pi> \<le> (x \<cdot> 1\<^sub>\<pi>) \<parallel> (y \<cdot> 1\<^sub>\<pi>)"
  by (meson local.order.trans x_c_glb x_c_lb1 x_c_lb2)

end

subsection \<open>C-Lattices\<close>

text \<open>We can now define c-lattices and prove the results from Section 7 in~\cite{FurusawaS15a}.\<close>

class pbl_monoid = proto_trioid +
  fixes U :: 'a
  fixes meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)
  assumes U_def: "x \<le> U"
  and meet_assoc: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  and meet_comm: "x \<sqinter> y = y \<sqinter> x"
  and meet_idem [simp]: "x \<sqinter> x = x"
  and absorp1: "x \<sqinter> (x + y) = x"
  and absorp2: "x + (x \<sqinter> y) = x"

begin

sublocale lattice "(\<sqinter>)" "(\<le>)" "(<)" "(+)"
proof
  show a: "\<And>x y. x \<sqinter> y \<le> x"
    by (simp add: local.absorp2 local.less_eq_def add_commute)
  show b: " \<And>x y. x \<sqinter> y \<le> y"
    using a local.meet_comm by fastforce
  show " \<And>x y z. x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (metis b local.absorp1 local.less_eq_def local.meet_assoc)
qed

lemma meet_glb: "z \<le> x \<and> z \<le> y \<Longrightarrow> z \<le> x \<sqinter> y"
  by simp

lemma meet_prop:  "z \<le> x \<and> z \<le> y \<longleftrightarrow> z \<le> x \<sqinter> y"
  by simp

end

class pbdl_monoid = pbl_monoid +
  assumes lat_dist1: "x + (y \<sqinter> z) = (x + y) \<sqinter> (x + z)"

begin

lemma lat_dist2: "(x \<sqinter> y) + z = (x + z) \<sqinter> (y + z)"
  by (simp add: local.lat_dist1 add_commute)

lemma lat_dist3: "x \<sqinter> (y + z) = (x \<sqinter> y) + (x \<sqinter> z)"
proof -
  have "\<And>x y z. x \<sqinter> ((x + y) \<sqinter> z) = x \<sqinter> z"
    by (metis local.absorp1 local.meet_assoc)
  thus ?thesis
    using lat_dist2 local.absorp2 add_commute by force
qed

lemma lat_dist4: "(x + y) \<sqinter> z = (x \<sqinter> z) + (y \<sqinter> z)"
  using lat_dist3 local.meet_comm by auto
 
lemma d_equiv_prop: "(\<forall>z. z + x = z + y \<and> z \<sqinter> x = z \<sqinter> y) \<Longrightarrow> x = y"
  by (metis local.add_zerol)

end

text \<open>The symbol $\overline{1}_\pi$ from~\cite{FurusawaS15a} is written nc in this theory file.\<close>

class c_lattice =  pbdl_monoid +
  fixes nc :: "'a"
  assumes cl1 [simp]: "x \<cdot> 1\<^sub>\<pi> + x \<cdot> nc = x \<cdot> U"
  and  cl2 [simp]: "1\<^sub>\<pi> \<sqinter> (x + nc) = x \<cdot> 0"
  and cl3: "x \<cdot> (y \<parallel> z) \<le> (x \<cdot> y) \<parallel> (x \<cdot> z)"
  and cl4: "z \<parallel> z \<le> z \<Longrightarrow> (x \<parallel> y) \<cdot> z = (x \<cdot> z) \<parallel> (y \<cdot> z)"
  and cl5: "x \<cdot> (y \<cdot> (z \<cdot> 0)) = (x \<cdot> y) \<cdot> (z \<cdot> 0)"
  and cl6 [simp]: "(x \<cdot> 0) \<cdot> z = x \<cdot> 0"
  and cl7 [simp]: "1\<^sub>\<sigma> \<parallel> 1\<^sub>\<sigma> = 1\<^sub>\<sigma>"
  and cl8 [simp]: "((x \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>) \<cdot> y = (x \<cdot> 1\<^sub>\<pi>) \<parallel> y"
  and cl9 [simp]: "((x \<sqinter> 1\<^sub>\<sigma>) \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma> = x \<sqinter> 1\<^sub>\<sigma>"         
  and cl10:  "((x \<sqinter> nc) \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma> = 1\<^sub>\<sigma> \<sqinter> (x \<sqinter> nc) \<cdot> nc"   
  and cl11 [simp]: "((x \<sqinter> nc) \<cdot> 1\<^sub>\<pi>) \<parallel> nc = (x \<sqinter> nc) \<cdot> nc"

begin

text \<open>We show that every c-lattice is a c-trioid (Proposition 7.1) Proposition 7.2 is again 
covered by the theory for multirelations.\<close>

subclass c_trioid
  proof 
  fix x y 
  show "x \<cdot> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<sigma> \<cdot> y = x \<cdot> 1\<^sub>\<pi> \<parallel> y"
    by auto
  show "x \<parallel> y \<cdot> 1\<^sub>\<pi> = x \<cdot> 1\<^sub>\<pi> \<parallel> (y \<cdot> 1\<^sub>\<pi>)"
    by (simp add: local.cl4)
  show "x \<cdot> y \<cdot> 1\<^sub>\<pi> = x \<cdot> (y \<cdot> 1\<^sub>\<pi>)"
    by (metis local.absorp1 local.cl2 local.cl5)
  show "1\<^sub>\<sigma> \<parallel> 1\<^sub>\<sigma> = 1\<^sub>\<sigma>"
    by (meson local.cl7)
  show x: "x \<cdot> 1\<^sub>\<pi> \<le> 1\<^sub>\<pi>"
    by (metis local.absorp1 local.cl2 local.cl5 local.inf_le1 local.s_prod_idl)
  show "x \<cdot> 1\<^sub>\<pi> \<parallel> x = x"
    by (metis x local.eq_iff local.cl3 local.mult_1_right local.mult_commute local.mult_isol local.s_prod_idr)
qed

text \<open>First we verify the complementation conditions after the definition of c-lattices.\<close>

lemma c_nc_comp1 [simp]: "1\<^sub>\<pi> + nc = U"
  by (metis local.cl1 local.s_prod_idl)

lemma c_nc_comp2 [simp]: "1\<^sub>\<pi> \<sqinter> nc = 0"
  by (metis local.add_zero_l local.cl2 local.s_prod_annil)

lemma  c_0: "x \<sqinter> 1\<^sub>\<pi> = x \<cdot> 0"
  by (metis c_nc_comp2 local.add_zeror local.cl2 local.lat_dist3 local.meet_comm)

text \<open>Next we verify the conditions in Proposition 7.2.\<close>

lemma d_s_subid: "d x = x \<longleftrightarrow> x \<le> 1\<^sub>\<sigma>"
  by (metis local.cl9 local.d_def local.d_subid local.inf.absorb_iff1)

lemma term_p_subid: "x \<cdot> 1\<^sub>\<pi> = x \<longleftrightarrow> x \<le> 1\<^sub>\<pi>"
  by (metis c_0 local.cl6 local.inf.absorb_iff1 local.p_id_term)

lemma term_p_subid_var: "x \<cdot> 0 = x \<longleftrightarrow> x \<le> 1\<^sub>\<pi>"
  using c_0 local.inf.absorb_iff1 by auto

lemma vec_iff: "d x \<cdot> U = x \<longleftrightarrow> (x \<cdot> 1\<^sub>\<pi>) \<parallel> U = x"
  by (simp add: local.c2_d)

lemma nc_iff1: "x \<le> nc \<longleftrightarrow> x \<sqinter> 1\<^sub>\<pi> = 0"
proof 
  fix x 
  assume assm: "x \<le> nc"
  hence "x = x \<sqinter> nc"
    by (simp add: local.inf.absorb_iff1)
  hence "x \<sqinter> 1\<^sub>\<pi> = x \<sqinter> nc \<sqinter> 1\<^sub>\<pi>"
    by auto
  then show "x \<sqinter> 1\<^sub>\<pi> = 0"
    by (metis assm c_0 c_nc_comp2 local.cl2 local.less_eq_def)
next
  fix x
  assume assm: "x \<sqinter> 1\<^sub>\<pi> = 0"
  have  "x = (x \<sqinter> nc) + (x \<sqinter> 1\<^sub>\<pi>)"
    by (metis c_nc_comp1 local.U_def local.add_comm local.lat_dist3 local.inf.absorb_iff1)
  hence "x = x \<sqinter> nc"
    using assm by auto
  thus "x \<le> nc"
    using local.inf.absorb_iff1 by auto
qed

lemma nc_iff2: "x \<le> nc \<longleftrightarrow> x \<cdot> 0 = 0"
  using c_0 nc_iff1 by auto

text \<open>The results of Lemma 7.3 are again at the multirelational level. 
Hence we continue with Lemma 7.4.\<close>

lemma assoc_p_subid: "(x \<cdot> y) \<cdot> (z \<cdot> 1\<^sub>\<pi>) = x \<cdot> (y \<cdot> (z \<cdot> 1\<^sub>\<pi>))"
  by (metis c_0 local.c6 local.cl5 local.inf.absorb_iff1)

lemma zero_assoc3: "(x \<cdot> y) \<cdot> 0 = x \<cdot> (y \<cdot> 0)" 
  by (metis local.cl5 local.s_prod_annil)

lemma x_zero_interr: "(x \<cdot> 0) \<parallel> (y \<cdot> 0) = (x \<parallel> y) \<cdot> 0"
  by (simp add: local.cl4) 

lemma p_subid_interr: "(x \<cdot> z \<cdot> 1\<^sub>\<pi>) \<parallel> (y \<cdot> z \<cdot> 1\<^sub>\<pi>) = (x \<parallel> y) \<cdot> z \<cdot> 1\<^sub>\<pi>"
  by (simp add: local.c4 local.cl4)

lemma d_interr: "(x \<cdot> d z) \<parallel> (y \<cdot> d z) = (x \<parallel> y) \<cdot> d z"
  by (simp add: local.cl4)

lemma subidem_par: "x \<le> x \<parallel> x" 
proof -
  have "x = x \<cdot> 1\<^sub>\<sigma>"
    by auto
  also have "... = x \<cdot> (1\<^sub>\<sigma> \<parallel> 1\<^sub>\<sigma>)"
    by auto
  finally show ?thesis
    by (metis local.cl3 local.cl7)
qed

lemma meet_le_par: "x \<sqinter> y \<le> x \<parallel> y" 
proof -
  have "x \<sqinter> y = (x \<sqinter> y) \<sqinter> (x \<sqinter> y)"
    using local.meet_idem by presburger
  thus ?thesis
    using local.inf_le1 local.inf_le2 local.mult_isol_var local.order_trans subidem_par by blast
qed

text\<open>Next we verify Lemma 7.5 and prove some related properties.\<close>

lemma x_split [simp]: "(x \<sqinter> nc) + (x \<sqinter> 1\<^sub>\<pi>) = x"
proof - 
  have "x = x \<sqinter> U"
    using local.U_def local.inf.absorb_iff1 by auto
  also have "... = x \<sqinter> (nc + 1\<^sub>\<pi>)"
    by (simp add: add_commute)
  finally show ?thesis
    by (metis local.lat_dist3)
qed

lemma x_split_var [simp]: "(x \<sqinter> nc) + (x \<cdot> 0) = x"
  by (metis local.c_0 x_split)

lemma s_subid_closed [simp]: "x \<sqinter> nc \<sqinter> 1\<^sub>\<sigma> = x \<sqinter> 1\<^sub>\<sigma>"
proof -
  have "x \<sqinter> 1\<^sub>\<sigma> = ((x \<sqinter> nc) + (x \<sqinter> 1\<^sub>\<pi>)) \<sqinter> 1\<^sub>\<sigma>"
    using x_split by presburger
  also have "... = (x \<sqinter> nc \<sqinter> 1\<^sub>\<sigma>) + (x \<sqinter> 1\<^sub>\<pi> \<sqinter> 1\<^sub>\<sigma>)"
    by (simp add: local.lat_dist3 local.meet_comm)
  also have "... = (x \<sqinter> nc \<sqinter> 1\<^sub>\<sigma>) + (x \<sqinter> 0)"
    by (metis c_0 local.meet_assoc local.meet_comm local.s_prod_idl)
  finally show ?thesis
    by (metis local.absorp1 local.add_zeror local.lat_dist1 local.meet_comm)
qed

lemma sub_id_le_nc: "x \<sqinter> 1\<^sub>\<sigma> \<le> nc"
  by (metis local.inf.absorb_iff2 local.inf_left_commute local.meet_comm s_subid_closed)

 lemma s_x_c [simp]: "1\<^sub>\<sigma> \<sqinter> (x \<cdot> 1\<^sub>\<pi>) = 0"
proof -
  have "1\<^sub>\<sigma> \<sqinter> 1\<^sub>\<pi> = 0"
    using c_0 local.s_prod_idl by presburger
  hence "1\<^sub>\<sigma> \<sqinter> x \<cdot> 1\<^sub>\<pi> \<le> 0"
    using local.c6 local.inf_le1 local.inf_le2 local.meet_prop local.order.trans by blast
  thus ?thesis
    using local.less_eq_def local.no_trivial_inverse by blast
qed

lemma s_x_zero [simp]: "1\<^sub>\<sigma> \<sqinter> (x \<cdot> 0) = 0"
  by (metis local.cl6 s_x_c)

lemma c_nc [simp]: "(x \<cdot> 1\<^sub>\<pi>) \<sqinter> nc = 0"
proof -
  have "x \<cdot> 1\<^sub>\<pi> \<sqinter> nc \<le> 1\<^sub>\<pi>"
    by (meson local.c6 local.dual_order.trans local.inf_le1)
  thus ?thesis
    by (metis local.inf_le2 nc_iff2 term_p_subid_var)
qed

lemma zero_nc [simp]: "(x \<cdot> 0) \<sqinter> nc = 0"
  by (metis c_nc local.cl6)

lemma nc_zero [simp]: "(x \<sqinter> nc) \<cdot> 0 = 0"
  by (meson local.inf_le2 nc_iff2)

text \<open>Lemma 7.6.\<close>

lemma c_def [simp]: "U \<cdot> 0 = 1\<^sub>\<pi>"
  by (metis c_nc_comp1 c_0 local.absorp1 local.meet_comm)  

lemma c_x_prop [simp]: "1\<^sub>\<pi> \<cdot> x = 1\<^sub>\<pi>"
  using c_def local.cl6 by blast

lemma U_idem_s_prod [simp]: "U \<cdot> U = U"
  by (metis local.U_def local.eq_iff local.s_prod_idl local.s_prod_isor)
 
lemma U_idem_p_prod [simp]: "U \<parallel> U = U"
  using local.U_def local.eq_iff subidem_par by presburger

lemma U_c [simp]: "U \<cdot> 1\<^sub>\<pi> = 1\<^sub>\<pi>" 
  by (metis U_idem_s_prod local.c_def zero_assoc3)

lemma s_le_nc: "1\<^sub>\<sigma> \<le> nc" 
  by (metis local.meet_idem sub_id_le_nc)

lemma nc_c [simp]: "nc \<cdot> 1\<^sub>\<pi> = 1\<^sub>\<pi>"
proof (rule antisym)
  have "nc \<cdot> 1\<^sub>\<pi> = nc \<cdot> 1\<^sub>\<pi> \<cdot> 0"
    by (simp add: zero_assoc3)
  also have "... = nc \<cdot> 1\<^sub>\<pi> \<sqinter> 1\<^sub>\<pi>"
    by (simp add: c_0)
  finally show "nc \<cdot> 1\<^sub>\<pi> \<le> 1\<^sub>\<pi>"
    using local.c6 by blast
  show "1\<^sub>\<pi> \<le> nc \<cdot> 1\<^sub>\<pi>"
    using local.s_prod_isor s_le_nc by fastforce
qed

lemma nc_nc [simp]: "nc \<cdot> nc = nc"
proof -
  have "nc \<cdot> nc = (nc \<cdot> 1\<^sub>\<pi>) \<parallel> nc"
    by (metis local.cl11 local.meet_idem)
  thus ?thesis
    by simp
qed

lemma U_nc [simp]: "U \<cdot> nc = U"
proof -
  have "U \<cdot> nc = (1\<^sub>\<pi> + nc) \<cdot> nc"
    by force
  also have "... = 1\<^sub>\<pi> \<cdot> nc + nc \<cdot> nc"
    using local.s_prod_distr by blast
  also have "... = 1\<^sub>\<pi> + nc"
    by simp
  finally show ?thesis
    by auto
qed

lemma nc_U [simp]: "nc \<cdot> U = U"
proof -
  have "nc \<cdot> U = nc \<cdot> 1\<^sub>\<pi> + nc \<cdot> nc"
    using local.cl1 by presburger
  thus ?thesis
    by simp
qed

lemma nc_nc_par [simp]: "nc \<parallel> nc = nc"
proof -
  have "nc \<parallel> nc = (nc \<parallel> nc \<sqinter> nc)  + (nc \<parallel> nc) \<cdot> 0"
    by simp
  also have "... = nc  + (nc \<cdot> 0) \<parallel> (nc \<cdot> 0)"
    by (metis local.meet_comm local.inf.absorb_iff1 subidem_par x_zero_interr)
  also have "... = nc + 0 \<parallel> 0"
    by (metis local.absorp1 local.meet_comm nc_zero)
  finally show ?thesis
    by (metis add_commute local.add_zerol local.annil)
qed
                                       
lemma U_nc_par [simp]: "U \<parallel> nc = nc"
proof -
  have "U \<parallel> nc = nc \<parallel> nc + 1\<^sub>\<pi> \<parallel> nc"
    by (metis c_nc_comp1 local.add_comm local.distrib_right)
  also have "... = nc + nc"
    by force
  finally show ?thesis
    by simp
qed

text \<open>We prove Lemma 7.8 and related properties.\<close>

lemma x_y_split [simp]: "(x \<sqinter> nc) \<cdot> y + x \<cdot> 0 = x \<cdot> y"
  by (metis c_0 local.cl6 local.s_prod_distr x_split)

lemma x_y_prop: "1\<^sub>\<sigma> \<sqinter> (x \<sqinter> nc) \<cdot> y = 1\<^sub>\<sigma> \<sqinter> x \<cdot> y"
proof -
  have "1\<^sub>\<sigma> \<sqinter> x \<cdot> y = 1\<^sub>\<sigma> \<sqinter> ((x \<sqinter> nc) \<cdot> y + x \<cdot> 0)"
    using x_y_split by presburger
  also have "... = (1\<^sub>\<sigma> \<sqinter> (x \<sqinter> nc) \<cdot> y) + (1\<^sub>\<sigma> \<sqinter> x \<cdot> 0)"
    by (simp add: local.lat_dist3 add_commute)  
  finally show ?thesis
    by (metis local.add_zeror s_x_zero) 
qed

lemma s_nc_U: "1\<^sub>\<sigma> \<sqinter> x \<cdot> nc = 1\<^sub>\<sigma> \<sqinter> x \<cdot> U"
proof -
  have "1\<^sub>\<sigma> \<sqinter> x \<cdot> U = 1\<^sub>\<sigma> \<sqinter> (x \<cdot> nc + x \<cdot> 1\<^sub>\<pi>)"
    by (simp add: add_commute)
  also have "... = (1\<^sub>\<sigma> \<sqinter> x \<cdot> nc) + (1\<^sub>\<sigma> \<sqinter> x \<cdot> 1\<^sub>\<pi>)"
    using local.lat_dist3 by blast
  finally show ?thesis
    by (metis local.add_zeror s_x_c)
qed

lemma sid_le_nc_var:  "1\<^sub>\<sigma> \<sqinter> x \<le> 1\<^sub>\<sigma> \<sqinter> x \<parallel> nc"
proof -
  have "1\<^sub>\<sigma> \<sqinter> x = x \<sqinter> (1\<^sub>\<sigma> \<sqinter> nc)"
    by (metis (no_types) local.inf.absorb1 local.inf.commute s_le_nc)
  hence "1\<^sub>\<sigma> \<sqinter> x \<parallel> nc + 1\<^sub>\<sigma> \<sqinter> x = (x \<parallel> nc + x \<sqinter> nc) \<sqinter> 1\<^sub>\<sigma>"
    using local.inf.commute local.inf.left_commute local.lat_dist4 by auto
  thus ?thesis
    by (metis (no_types) local.inf.commute local.join.sup.absorb_iff1 meet_le_par)
qed

lemma s_nc_par_U: "1\<^sub>\<sigma> \<sqinter> x \<parallel> nc = 1\<^sub>\<sigma> \<sqinter> x \<parallel> U"
proof -
  have "1\<^sub>\<sigma> \<sqinter> x \<parallel> U = 1\<^sub>\<sigma> \<sqinter> (x \<parallel> nc + x)"
    by (metis c_nc_comp1 local.add_comm local.distrib_left local.mult_oner)
  also have "... = (1\<^sub>\<sigma> \<sqinter> x \<parallel> nc) + (x \<sqinter> 1\<^sub>\<sigma>)"
    by (metis local.lat_dist3 local.meet_comm)
  also have "... = 1\<^sub>\<sigma> \<sqinter> x \<parallel> nc"
    by (metis local.add_comm local.less_eq_def local.meet_comm sid_le_nc_var)
  finally show ?thesis
    by metis
qed

lemma x_c_nc_split: "(x \<cdot> 1\<^sub>\<pi>) \<parallel> nc = (x \<sqinter> nc) \<cdot> nc + (x \<cdot> 0) \<parallel> nc"
  by (metis local.cl11 local.mult_commute local.p_prod_distl x_y_split)

lemma x_c_U_split: "(x \<cdot> 1\<^sub>\<pi>) \<parallel> U = x \<cdot> U + (x \<cdot> 0) \<parallel> U" 
proof -
  have "x \<cdot> U + (x \<cdot> 0) \<parallel> U = (x \<sqinter> nc) \<cdot> U + (x \<cdot> 0) \<parallel> U"
    by (metis U_c U_idem_s_prod U_nc local.add_assoc' local.cl1 local.distrib_left local.mult_oner x_y_split)
  also have "... = (x \<sqinter> nc) \<cdot> nc + (x \<sqinter> nc) \<cdot> 1\<^sub>\<pi> + (x \<cdot> 0) \<parallel> nc + x \<cdot> 0"
    by (metis add_commute c_nc_comp1 local.cl1 local.combine_common_factor local.mult_1_right local.mult_commute)
  also have "... = (x \<cdot> 1\<^sub>\<pi>) \<parallel> nc + x \<cdot> 1\<^sub>\<pi>"
    by (metis local.add_ac(1) local.add_commute x_c_nc_split x_y_split)
  thus ?thesis
    by (metis c_nc_comp1 calculation local.add_comm local.distrib_left local.mult_oner)
qed

subsection \<open>Domain in C-Lattices\<close>

text \<open>We now prove variants of the domain axioms and verify the properties of Section 8 in~\cite{FurusawaS15a}.\<close>

lemma cl9_d [simp]: "d (x \<sqinter> 1\<^sub>\<sigma>) = x \<sqinter> 1\<^sub>\<sigma>"
  by (simp add: local.d_def)

lemma cl10_d: "d (x \<sqinter> nc) = 1\<^sub>\<sigma> \<sqinter> (x \<sqinter> nc) \<cdot> nc"
  using local.cl10 local.d_def by auto

lemma cl11_d [simp]: "d (x \<sqinter> nc) \<cdot> nc = (x \<sqinter> nc) \<cdot> nc"
  using local.c2_d by force

lemma cl10_d_var1: "d (x \<sqinter> nc) = 1\<^sub>\<sigma> \<sqinter> x \<cdot> nc"
  by (simp add: cl10_d x_y_prop)

lemma cl10_d_var2: "d (x \<sqinter> nc) = 1\<^sub>\<sigma> \<sqinter> (x \<sqinter> nc) \<cdot> U"
  by (simp add: cl10_d s_nc_U)

lemma cl10_d_var3: "d (x \<sqinter> nc) = 1\<^sub>\<sigma> \<sqinter> x \<cdot> U"
  by (simp add: cl10_d_var1 s_nc_U)

text \<open>We verify the remaining properties of Lemma 8.1.\<close>

lemma d_U [simp]: "d U = 1\<^sub>\<sigma>"
  by (simp add: local.d_def)

lemma d_nc [simp]: "d nc = 1\<^sub>\<sigma>"
  using local.d_def by auto
 
lemma alt_d_def_nc_nc: "d (x \<sqinter> nc) = 1\<^sub>\<sigma> \<sqinter> ((x \<sqinter> nc) \<cdot> 1\<^sub>\<pi>) \<parallel> nc"
  by (simp add: cl10_d_var1 x_y_prop)    

lemma alt_d_def_nc_U: "d (x \<sqinter> nc) = 1\<^sub>\<sigma> \<sqinter> ((x \<sqinter> nc) \<cdot> 1\<^sub>\<pi>) \<parallel> U"
  by (metis alt_d_def_nc_nc local.c2_d s_nc_U)

text \<open>We verify the identity before Lemma 8.2 of~\cite{FurusawaS15a} together with variants.\<close>

lemma d_def_split [simp]: "d (x \<sqinter> nc) + d (x \<cdot> 0) = d x"
  by (metis local.d_add_ax x_split_var)

lemma d_def_split_var [simp]: "d (x \<sqinter> nc) + (x \<cdot> 0) \<parallel> 1\<^sub>\<sigma> = d x"
  by (metis d_def_split local.d_x_zero)

lemma ax7 [simp]: "(1\<^sub>\<sigma> \<sqinter> x \<cdot> U) + (x \<cdot> 0) \<parallel> 1\<^sub>\<sigma> = d x"
  by (metis cl10_d_var3 d_def_split_var)

text \<open>Lemma 8.2.\<close>

lemma dom12_d: "d x = 1\<^sub>\<sigma> \<sqinter> (x \<cdot> 1\<^sub>\<pi>) \<parallel> nc"
proof -
  have "1\<^sub>\<sigma> \<sqinter> (x \<cdot> 1\<^sub>\<pi>) \<parallel> nc = 1\<^sub>\<sigma> \<sqinter> ((x \<sqinter> nc) \<cdot> 1\<^sub>\<pi> + x \<cdot> 0) \<parallel> nc"
    using x_y_split by presburger
  also have "... = (1\<^sub>\<sigma> \<sqinter> ((x \<sqinter> nc) \<cdot> 1\<^sub>\<pi>) \<parallel> nc) + (1\<^sub>\<sigma> \<sqinter> (x \<cdot> 0) \<parallel> nc)"
    by (simp add: local.lat_dist3 local.mult_commute local.p_prod_distl add_commute)
  also have "... = d (x \<sqinter> nc) + d (x \<cdot> 0)"
    by (metis add_commute c_0 cl10_d_var1 local.add_zerol local.annil local.c2_d local.d_def local.mult_commute local.mult_onel local.zero_p_id_prop x_split)
  finally show ?thesis
    by (metis d_def_split)
qed

lemma dom12_d_U: "d x = 1\<^sub>\<sigma> \<sqinter> (x \<cdot> 1\<^sub>\<pi>) \<parallel> U"
  by (simp add: dom12_d s_nc_par_U)

lemma dom_def_var: "d x = (x \<cdot> U \<sqinter> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>"
  by (simp add: c_0 local.d_def zero_assoc3)

text\<open>Lemma 8.3.\<close>

lemma ax5_d [simp]: "d (x \<sqinter> nc) \<cdot> U = (x \<sqinter> nc) \<cdot> U"
proof -
  have "d (x \<sqinter> nc) \<cdot> U = d (x \<sqinter> nc) \<cdot> nc + d (x \<sqinter> nc) \<cdot> 1\<^sub>\<pi>"
    using add_commute local.cl1 by presburger
  also have "... = (x \<sqinter> nc) \<cdot> nc + (x \<sqinter> nc) \<cdot> 1\<^sub>\<pi>"
    by simp
  finally show ?thesis
    by (simp add: add_commute)
qed

lemma ax5_0 [simp]: "d (x \<cdot> 0) \<cdot> U = (x \<cdot> 0) \<parallel> U"
  using local.x_zero_prop by presburger

lemma x_c_U_split2: "d x \<cdot> nc = (x \<sqinter> nc) \<cdot> nc + (x \<cdot> 0) \<parallel> nc"
  by (simp add: local.c2_d x_c_nc_split)

lemma x_c_U_split3: "d x \<cdot> U = (x \<sqinter> nc) \<cdot> U + (x \<cdot> 0) \<parallel> U"
  by (metis d_def_split local.s_prod_distr ax5_0 ax5_d)

lemma x_c_U_split_d: "d x \<cdot> U = x \<cdot> U + (x \<cdot> 0) \<parallel> U"
  using local.c2_d x_c_U_split by presburger 

lemma x_U_prop2: "x \<cdot> nc = d (x \<sqinter> nc) \<cdot> nc + x \<cdot> 0"
  by (metis local.c2_d local.cl11 x_y_split)

lemma x_U_prop3: "x \<cdot> U = d (x \<sqinter> nc) \<cdot> U + x \<cdot> 0"
  by (metis ax5_d x_y_split)

lemma d_x_nc [simp]: "d (x \<cdot> nc) = d x"
  using local.c4 local.d_def by auto

lemma d_x_U [simp]: "d (x \<cdot> U) = d x"
  by (simp add: local.c4 local.d_def)

text \<open>The next properties of domain are important, but do not feature in~\cite{FurusawaS15a}. 
Proofs can be found in~\cite{FurusawaS15b}.\<close>

lemma d_llp1: "d x \<le> d y \<Longrightarrow> x \<le> d y \<cdot> x"
  by (metis local.d_rest_ax local.s_prod_isor)

lemma d_llp2: "x \<le> d y \<cdot> x \<Longrightarrow> d x \<le> d y"
proof -
  assume a1: "x \<le> d y \<cdot> x"
  have "\<forall>x y. d (x \<parallel> y) = x \<cdot> 1\<^sub>\<pi> \<parallel> d y"
    using local.c2_d local.d_conc6 local.d_conc_s_prod_ax by presburger
  hence "d x \<le> d (y \<cdot> 1\<^sub>\<pi>)"
    using a1 by (metis (no_types) local.c2_d local.c6 local.c_prod_comm local.eq_iff local.mult_isol local.mult_oner)
  thus ?thesis
    by simp
qed

lemma demod1: "d (x \<cdot> y) \<le> d z \<Longrightarrow> x \<cdot> d y \<le> d z \<cdot> x"
proof -
  assume "d (x \<cdot> y) \<le> d z"
  hence "\<forall>v. x \<cdot> y \<cdot> 1\<^sub>\<pi> \<parallel> v \<le> z \<cdot> 1\<^sub>\<pi> \<parallel> v"
    by (metis (no_types) local.c2_d local.s_prod_isor)
  hence "\<forall>v. x \<cdot> (y \<cdot> 1\<^sub>\<pi> \<parallel> v) \<le> z \<cdot> 1\<^sub>\<pi> \<parallel> (x \<cdot> v)"
    by (metis local.c4 local.cl3 local.dual_order.trans)
  thus ?thesis
    by (metis local.c2_d local.s_prod_idr)
qed

lemma demod2: "x \<cdot> d y \<le> d z \<cdot> x \<Longrightarrow> d (x \<cdot> y) \<le> d z"
proof -
  assume "x \<cdot> d y \<le> d z \<cdot> x"
  hence "d (x \<cdot> y) \<le> d (d z \<cdot> x)"
    by (metis local.d_def local.d_loc_ax local.mult_isor local.s_prod_isor)
  thus ?thesis
    using local.d_conc6 local.d_conc_s_prod_ax local.d_glb_iff by fastforce
qed

subsection \<open>Structural Properties of C-Lattices\<close>

text \<open>Now we consider the results from Section 9 and 10 in~\cite{FurusawaS15a}. 
First we verify the conditions for Proposition 9.1.\<close>
      
lemma d_meet_closed [simp]: "d (d x \<sqinter> d y) = d x \<sqinter> d y"
  using d_s_subid local.d_sub_id_ax local.inf_le1 local.order_trans by blast

lemma d_s_prod_eq_meet: "d x \<cdot> d y = d x \<sqinter> d y" 
  apply (rule antisym)
  apply (metis local.d_lb1 local.d_lb2 local.meet_glb)
  by (metis d_meet_closed local.inf_le1 local.inf_le2 local.d_glb)

lemma d_p_prod_eq_meet: "d x \<parallel> d y = d x \<sqinter> d y"
  by (simp add: d_s_prod_eq_meet local.d_conc_s_prod_ax) 

lemma s_id_par_s_prod: "(x \<sqinter> 1\<^sub>\<sigma>) \<parallel> (y \<sqinter> 1\<^sub>\<sigma>) = (x \<sqinter> 1\<^sub>\<sigma>) \<cdot> (y \<sqinter> 1\<^sub>\<sigma>)" 
  by (metis cl9_d local.d_conc_s_prod_ax)

lemma s_id_par [simp]: "x \<sqinter> 1\<^sub>\<sigma> \<parallel> x \<sqinter> 1\<^sub>\<sigma> = x \<sqinter> 1\<^sub>\<sigma>"
  using local.meet_assoc local.meet_comm local.inf.absorb_iff1 meet_le_par by auto 

text \<open>We verify the remaining conditions in Proposition 9.2.\<close>

lemma p_subid_par_eq_meet: "(x \<cdot> 0) \<parallel> (y \<cdot> 0) = (x \<cdot> 0) \<sqinter> (y \<cdot> 0)"
  by (simp add: local.meet_glb local.order.antisym local.p_subid_lb1 local.p_subid_lb2 meet_le_par)

lemma p_subid_par_eq_meet_var: "(x \<cdot> 1\<^sub>\<pi>) \<parallel> (y \<cdot> 1\<^sub>\<pi>) = (x \<cdot> 1\<^sub>\<pi>) \<sqinter> (y \<cdot> 1\<^sub>\<pi>)"
  by (metis c_x_prop p_subid_par_eq_meet zero_assoc3) 

lemma x_zero_add_closed: "x \<cdot> 0 + y \<cdot> 0 = (x + y) \<cdot> 0"
  by (simp add: local.s_prod_distr)

lemma x_zero_meet_closed: "(x \<cdot> 0) \<sqinter> (y \<cdot> 0) = (x \<sqinter> y) \<cdot> 0"
  by (metis c_0 local.cl6 local.meet_assoc local.meet_comm)

text \<open>The following set of lemmas investigates the closure properties of vectors, including Lemma 9,3.\<close>

lemma U_par_zero [simp]: "(0 \<cdot> c) \<parallel> U = 0"
  by fastforce

lemma U_par_s_id [simp]: "(1\<^sub>\<sigma> \<cdot> 1\<^sub>\<pi>) \<parallel> U = U"
  by auto

lemma U_par_p_id [simp]: "(1\<^sub>\<pi> \<cdot> 1\<^sub>\<pi>) \<parallel> U = U"
  by auto

lemma U_par_nc [simp]: "(nc \<cdot> 1\<^sub>\<pi>) \<parallel> U = U"
  by auto

lemma d_add_var: "d x \<cdot> z + d y \<cdot> z = d (x + y) \<cdot> z"
  by (simp add: local.d_add_ax local.s_prod_distr)

lemma d_interr_U: "(d x \<cdot> U) \<parallel> (d y \<cdot> U) = d (x \<parallel> y) \<cdot> U"
  by (simp add: local.cl4 local.d_conc6)

lemma d_meet:
assumes "\<And> x y z. (x \<sqinter> y \<sqinter> 1\<^sub>\<sigma>) \<cdot> z = (x \<sqinter> 1\<^sub>\<sigma>) \<cdot> z \<sqinter> (y \<sqinter> 1\<^sub>\<sigma>) \<cdot> z"
shows "d x \<cdot> z \<sqinter> d y \<cdot> z = (d x \<sqinter> d y) \<cdot> z"
proof -
  have "(d x \<sqinter> d y) \<cdot> z = (d x \<sqinter> d y \<sqinter> 1\<^sub>\<sigma>) \<cdot> z"
    using local.d_sub_id_ax local.meet_assoc local.inf.absorb_iff1 by fastforce
  also have "... = (d x \<sqinter> 1\<^sub>\<sigma>) \<cdot> z \<sqinter> (d y \<sqinter> 1\<^sub>\<sigma>) \<cdot> z"
    using assms by auto
  finally show ?thesis
    by (metis local.d_sub_id_ax local.inf.absorb_iff1)
qed

text \<open>Proposition 9.4\<close>

lemma nc_zero_closed [simp]: "0 \<sqinter> nc = 0"
  by (simp add: local.inf.commute local.inf_absorb2)

lemma nc_s [simp]: "1\<^sub>\<sigma> \<sqinter> nc = 1\<^sub>\<sigma>"
  using local.inf.absorb_iff1 s_le_nc by blast

lemma nc_add_closed: "(x \<sqinter> nc) + (y \<sqinter> nc) = (x + y) \<sqinter> nc"
  using local.lat_dist4 by force

lemma nc_meet_closed: "(x \<sqinter> nc) \<sqinter> (y \<sqinter> nc) = x \<sqinter> y \<sqinter> nc"
  using local.meet_assoc local.meet_comm local.inf_le1 local.inf.absorb_iff1 by fastforce

lemma nc_scomp_closed: "((x \<sqinter> nc) \<cdot> (y \<sqinter> nc)) \<le> nc"
  by (simp add: c_0 nc_iff1 zero_assoc3)

lemma nc_scomp_closed_alt [simp]: "((x \<sqinter> nc) \<cdot> (y \<sqinter> nc)) \<sqinter> nc = (x \<sqinter> nc) \<cdot> (y \<sqinter> nc)"
  using local.inf.absorb_iff1 nc_scomp_closed by blast

lemma nc_ccomp_closed: "(x \<sqinter> nc) \<parallel> (y \<sqinter> nc) \<le>  nc"
proof -
  have "(x \<sqinter> nc) \<parallel> (y \<sqinter> nc) \<le> nc \<parallel> nc"
    by (meson local.inf_le2 local.mult_isol_var)
  thus ?thesis
    by auto
qed

lemma nc_ccomp_closed_alt [simp]: "(x \<parallel> (y \<sqinter> nc)) \<sqinter> nc = x \<parallel> (y \<sqinter> nc)"
  by (metis U_nc_par local.U_def local.inf_le2 local.mult_isol_var local.inf.absorb_iff1)

text \<open>Lemma 9.6.\<close>
 
lemma tarski_prod:
assumes "\<And>x. x \<sqinter> nc \<noteq> 0 \<Longrightarrow> nc \<cdot> ((x \<sqinter> nc) \<cdot> nc) = nc"
and "\<And>x y z. d x \<cdot> (y \<cdot> z) = (d x \<cdot> y) \<cdot> z"
shows "((x \<sqinter> nc) \<cdot> nc) \<cdot> ((y \<sqinter> nc) \<cdot> nc) = (if  (y \<sqinter> nc)  = 0 then 0 else (x \<sqinter> nc) \<cdot> nc)"
proof (cases "y \<sqinter> nc = 0")
  fix x y
  assume  assm: "y \<sqinter> nc = 0"
  show "(x \<sqinter> nc) \<cdot> nc \<cdot> ((y \<sqinter> nc) \<cdot> nc) = (if y \<sqinter> nc = 0 then 0 else (x \<sqinter> nc) \<cdot> nc)"
    by (metis assm c_0 local.cl6 local.meet_comm nc_zero zero_assoc3)
next
  fix x y
  assume assm: "y \<sqinter> nc \<noteq> 0"
  have "((x \<sqinter> nc) \<cdot> nc) \<cdot> ((y \<sqinter> nc) \<cdot> nc) = (d (x \<sqinter> nc) \<cdot> nc) \<cdot> ((y \<sqinter> nc) \<cdot> nc)"
    by simp
  also have "... = d (x \<sqinter> nc) \<cdot> (nc \<cdot> ((y \<sqinter> nc) \<cdot> nc))"
    by (simp add: assms(2))  
  also have "... = d (x \<sqinter> nc) \<cdot> nc"
    by (simp add: assm assms(1))
  finally show "(x \<sqinter> nc) \<cdot> nc \<cdot> ((y \<sqinter> nc) \<cdot> nc) = (if y \<sqinter> nc = 0 then 0 else (x \<sqinter> nc) \<cdot> nc)"
    by (simp add: assm)
qed

text \<open>We show the remaining conditions of Proposition 9.8.\<close>

lemma nc_prod_aux [simp]: "((x \<sqinter> nc) \<cdot> nc) \<cdot> nc = (x \<sqinter> nc) \<cdot> nc"
proof -
  have "((x \<sqinter> nc) \<cdot> nc) \<cdot> nc = (d (x \<sqinter> nc) \<cdot> nc) \<cdot> nc"
    by simp
  also have "... = d (x \<sqinter> nc) \<cdot> (nc \<cdot> nc)"
    by (metis cl11_d d_x_nc local.cl11 local.meet_idem nc_ccomp_closed_alt nc_nc)
  also have "... = d (x \<sqinter> nc) \<cdot> nc"
    by auto
  finally show ?thesis
    by simp
qed

lemma nc_vec_add_closed: "((x \<sqinter> nc) \<cdot> nc + (y \<sqinter> nc) \<cdot> nc) \<cdot> nc =  (x \<sqinter> nc) \<cdot> nc + (y \<sqinter> nc) \<cdot> nc"
  by (simp add: local.s_prod_distr)

lemma nc_vec_par_closed: "(((x \<sqinter> nc) \<cdot> nc) \<parallel> ((y \<sqinter> nc) \<cdot> nc)) \<cdot> nc =  ((x \<sqinter> nc) \<cdot> nc) \<parallel> ((y \<sqinter> nc) \<cdot> nc)"
  by (simp add: local.cl4)

lemma nc_vec_par_is_meet: 
assumes "\<And> x y z. (d x \<sqinter> d y) \<cdot> z = d x \<cdot> z \<sqinter> d y \<cdot> z"
shows "((x \<sqinter> nc) \<cdot> nc) \<parallel> ((y \<sqinter> nc) \<cdot> nc) = ((x \<sqinter> nc) \<cdot> nc) \<sqinter> ((y \<sqinter> nc) \<cdot> nc)" 
proof -
  have "((x \<sqinter> nc) \<cdot> nc) \<parallel> ((y \<sqinter> nc) \<cdot> nc) = (d (x \<sqinter> nc) \<cdot> nc) \<parallel> (d (y \<sqinter> nc) \<cdot> nc)"
    by auto
  also have "... = (d (x \<sqinter> nc) \<parallel> d (y \<sqinter> nc)) \<cdot> nc"
    by (simp add: local.cl4)
  also have "... = (d (x \<sqinter> nc) \<sqinter> d (y \<sqinter> nc)) \<cdot> nc"
    by (simp add: d_p_prod_eq_meet)
  finally show ?thesis
    by (simp add: assms)
qed

lemma nc_vec_meet_closed:
assumes "\<And> x y z. (d x \<sqinter> d y) \<cdot> z = d x \<cdot> z \<sqinter> d y \<cdot> z"
shows "((x \<sqinter> nc) \<cdot> nc \<sqinter> (y \<sqinter> nc) \<cdot> nc) \<cdot> nc =  (x \<sqinter> nc) \<cdot> nc \<sqinter> (y \<sqinter> nc) \<cdot> nc"
proof -
  have "((x \<sqinter> nc) \<cdot> nc \<sqinter> (y \<sqinter> nc) \<cdot> nc) \<cdot> nc = (((x \<sqinter> nc) \<cdot> nc) \<parallel> ((y \<sqinter> nc) \<cdot> nc)) \<cdot> nc"
    by (simp add: assms nc_vec_par_is_meet) 
  also have "... = ((x \<sqinter> nc) \<cdot> nc) \<parallel> ((y \<sqinter> nc) \<cdot> nc)"
    by (simp add: nc_vec_par_closed)
  finally show ?thesis
    by (simp add: assms nc_vec_par_is_meet)
qed

lemma nc_vec_seq_closed: 
assumes "\<And>x. x \<sqinter> nc \<noteq> 0 \<Longrightarrow> nc \<cdot> ((x \<sqinter> nc) \<cdot> nc) = nc"
and "\<And>x y z. d x \<cdot> (y \<cdot> z) = (d x \<cdot> y) \<cdot> z"
shows "(((x \<sqinter> nc) \<cdot> nc) \<cdot> ((y \<sqinter> nc) \<cdot> nc)) \<cdot> nc =  ((x \<sqinter> nc) \<cdot> nc) \<cdot> ((y \<sqinter> nc) \<cdot> nc)"
proof -
  have one : "y \<sqinter> nc = 0 \<Longrightarrow> (((x \<sqinter> nc) \<cdot> nc) \<cdot> ((y \<sqinter> nc) \<cdot> nc)) \<cdot> nc = ((x \<sqinter> nc) \<cdot> nc) \<cdot> ((y \<sqinter> nc) \<cdot> nc)"
    by simp
  have "y \<sqinter> nc \<noteq> 0 \<Longrightarrow> (((x \<sqinter> nc) \<cdot> nc) \<cdot> ((y \<sqinter> nc) \<cdot> nc)) \<cdot> nc = ((x \<sqinter> nc) \<cdot> nc) \<cdot> ((y \<sqinter> nc) \<cdot> nc)"
    by (simp add: assms(1) assms(2) tarski_prod)
  thus ?thesis
    using one by blast 
qed

text \<open>Proposition 10.1 and 10.2.\<close>

lemma iso3 [simp]: "d (d x \<cdot> U) = d x "
  by simp

lemma iso4 [simp]: "d ((x \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> U = (x \<cdot> 1\<^sub>\<pi>) \<parallel> U"
  by (simp add: local.c3 local.c4 vec_iff)

lemma iso5 [simp]:  "((x \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> 1\<^sub>\<pi> = x \<cdot> 1\<^sub>\<pi>"
  by (simp add: local.c3 local.c4)

lemma iso6 [simp]: "(((x \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> 1\<^sub>\<pi>) \<parallel> U = (x \<cdot> 1\<^sub>\<pi>) \<parallel> U"
  by simp

lemma iso3_sharp [simp]: "d (d (x \<sqinter> nc) \<cdot> nc) = d (x \<sqinter> nc)"
  using d_s_subid local.c4 local.d_def local.inf_le1 by auto

lemma iso4_sharp [simp]: "d ((x \<sqinter> nc) \<cdot> nc) \<cdot> nc = (x \<sqinter> nc) \<cdot> nc"
  by (simp add: local.c2_d local.c4)

lemma iso5_sharp [simp]: "(((x \<sqinter> nc) \<cdot> 1\<^sub>\<pi>) \<parallel> nc) \<cdot> 1\<^sub>\<pi> = (x \<sqinter> nc) \<cdot> 1\<^sub>\<pi>"
  by (simp add: local.c3 local.c4)

lemma iso6_sharp [simp]: "(((x \<sqinter> nc) \<cdot> nc) \<cdot> 1\<^sub>\<pi>) \<parallel> nc = (x \<sqinter> nc) \<cdot> nc"
  using local.c4 local.cl11 nc_c by presburger

text\<open>We verify Lemma 15.2 at this point, because it is helpful for the following proofs.\<close>

lemma uc_par_meet: "x \<parallel> U \<sqinter> y \<parallel> U = x \<parallel> U \<parallel> y \<parallel> U"
  apply (rule antisym)
  apply (metis local.c_prod_assoc meet_le_par)
  by (metis U_idem_p_prod local.U_def local.c_prod_assoc local.meet_prop local.mult.left_commute local.mult_double_iso)

lemma uc_unc [simp]: "x \<parallel> U \<parallel> x \<parallel> U = x \<parallel> U"
  by (metis local.meet_idem uc_par_meet)

lemma uc_interr: "(x \<parallel> y) \<cdot> (z \<parallel> U) = (x \<cdot> (z \<parallel> U)) \<parallel> (y \<cdot> (z \<parallel> U))"
proof -
  have "(z \<parallel> U) \<parallel> (z \<parallel> U) = z \<parallel> U"
    by (metis local.c_prod_assoc uc_unc)
  thus ?thesis
    by (simp add: local.cl4) 
qed

text\<open>We verify the remaining cases of Proposition 10.3.\<close>

lemma sc_hom_meet: "(d x \<sqinter> d y) \<cdot> 1\<^sub>\<pi> = (d x) \<cdot> 1\<^sub>\<pi> \<sqinter> (d y) \<cdot> 1\<^sub>\<pi>"
  by (metis d_p_prod_eq_meet local.c3 p_subid_par_eq_meet_var)

lemma sc_hom_seq: "(d x \<cdot> d y) \<cdot> 1\<^sub>\<pi> = (d x \<sqinter> d y) \<cdot> 1\<^sub>\<pi>"
  by (simp add: d_s_prod_eq_meet) 

lemma cs_hom_meet: "d (x \<cdot> 1\<^sub>\<pi> \<sqinter> y \<cdot> 1\<^sub>\<pi>)  = d (x \<cdot> 1\<^sub>\<pi>) \<sqinter> d (y \<cdot> 1\<^sub>\<pi>)"
  by (metis d_p_prod_eq_meet local.d_conc6 p_subid_par_eq_meet_var)

lemma sv_hom_meet: "(d x \<sqinter> d y) \<cdot> U = (d x) \<cdot> U \<sqinter> (d y) \<cdot> U"
proof -
  have "(d x \<sqinter> d y) \<cdot> U = ((d x) \<cdot> U) \<parallel> ((d y) \<cdot> U)"
    by (simp add: d_interr_U d_p_prod_eq_meet local.d_conc6)
  thus ?thesis
    by (simp add: local.c2_d local.c_prod_assoc uc_par_meet)   
qed 

lemma sv_hom_par: "(x \<parallel> y) \<cdot> U = (x \<cdot> U) \<parallel> (y \<cdot> U)"
  by (simp add: local.cl4)

lemma vs_hom_meet: "d (((x \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<sqinter> ((y \<cdot> 1\<^sub>\<pi>) \<parallel> U)) = d ((x \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<sqinter> d ((y \<cdot> 1\<^sub>\<pi>) \<parallel> U)"
proof -
  have f1: "\<And>x y. x \<cdot> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<sigma> \<sqinter> y \<cdot> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<sigma> = x \<parallel> y \<cdot> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<sigma>"
    using d_p_prod_eq_meet local.d_conc6 local.d_def by auto
  hence "\<And>x y. x \<cdot> 1\<^sub>\<pi> \<parallel> U \<sqinter> y \<cdot> 1\<^sub>\<pi> \<parallel> U = x \<parallel> y \<cdot> 1\<^sub>\<pi> \<parallel> U"
    using local.d_def sv_hom_meet by force
  thus ?thesis
    using f1 by (simp add: local.d_def)
qed

lemma cv_hom_meet: "(x \<cdot> 1\<^sub>\<pi> \<sqinter> y \<cdot> 1\<^sub>\<pi>) \<parallel> U = (x \<cdot> 1\<^sub>\<pi>) \<parallel> U \<sqinter> (y \<cdot> 1\<^sub>\<pi>) \<parallel> U"
proof -
  have "d (x \<parallel> y) \<cdot> U = x \<cdot> 1\<^sub>\<pi> \<parallel> U \<sqinter> y \<cdot> 1\<^sub>\<pi> \<parallel> U"
    by (simp add: d_p_prod_eq_meet local.c2_d local.d_conc6 sv_hom_meet)
  thus ?thesis
    using local.c2_d local.c3 p_subid_par_eq_meet_var by auto
qed

lemma cv_hom_par [simp]: " x \<parallel> U \<parallel> y \<parallel> U = (x \<parallel> y) \<parallel> U"
  by (metis U_idem_p_prod local.mult.left_commute local.mult_assoc)

lemma vc_hom_meet: "((x \<cdot> 1\<^sub>\<pi>) \<parallel> U \<sqinter> (y \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> 1\<^sub>\<pi> = ((x \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> 1\<^sub>\<pi> \<sqinter> ((y \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> 1\<^sub>\<pi>"
  by (metis cv_hom_meet iso5 local.c3 p_subid_par_eq_meet_var)

lemma vc_hom_seq: "(((x \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> ((y \<cdot> 1\<^sub>\<pi>) \<parallel> U)) \<cdot> 1\<^sub>\<pi> = (((x \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> 1\<^sub>\<pi>) \<cdot> (((y \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> 1\<^sub>\<pi>)"
proof - 
  have "(((x \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> ((y \<cdot> 1\<^sub>\<pi>) \<parallel> U)) \<cdot> 1\<^sub>\<pi> = ((x \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> (y \<cdot> 1\<^sub>\<pi>)"
    by (simp add: local.c4)
  also have "... = (x \<cdot> 1\<^sub>\<pi>) \<parallel> (U \<cdot> (y \<cdot> 1\<^sub>\<pi>))"
    by (metis assoc_p_subid local.cl8)
  also have "... = (x \<cdot> 1\<^sub>\<pi>) \<parallel> (nc \<cdot> (y \<cdot> 1\<^sub>\<pi>) + 1\<^sub>\<pi> \<cdot> (y \<cdot> 1\<^sub>\<pi>))"
    by (metis add_commute c_nc_comp1 local.s_prod_distr) 
  also have "... = (x \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<pi>"
    by (metis add_commute c_x_prop local.absorp2 local.c4 local.meet_comm local.mult_oner p_subid_par_eq_meet_var)
  thus ?thesis
    by (simp add: assoc_p_subid calculation)
qed

text \<open>Proposition 10.4.\<close>
  
lemma nsv_hom_meet: "(d x \<sqinter> d y) \<cdot> nc = (d x) \<cdot> nc \<sqinter> (d y) \<cdot> nc"
proof  (rule antisym)
  have   "(d x \<sqinter> d y) \<cdot> nc \<le> (d x) \<cdot> nc"
    by (simp add: local.s_prod_isor)
  hence   "(d x \<sqinter> d y) \<cdot> nc \<le> (d x) \<cdot> nc" 
    by blast
  thus "(d x \<sqinter> d y) \<cdot> nc \<le> (d x) \<cdot> nc \<sqinter> (d y) \<cdot> nc"
    by (simp add: local.s_prod_isor)
  have "(d x) \<cdot> nc \<sqinter> (d y) \<cdot> nc \<le> ((d x) \<cdot> nc) \<parallel> ((d y) \<cdot> nc)"
    by (simp add: meet_le_par)
  also have "... = (d x \<parallel> d y) \<cdot> nc"
    by (metis local.cl4 nc_nc_par subidem_par)
  finally show "(d x) \<cdot> nc \<sqinter> (d y) \<cdot> nc \<le> (d x \<sqinter> d y) \<cdot> nc"
    by (simp add: d_p_prod_eq_meet)
qed

lemma nsv_hom_par: "(x \<parallel> y) \<cdot> nc = (x \<cdot> nc) \<parallel> (y \<cdot> nc)"
  by (simp add: local.cl4)

lemma vec_p_prod_meet: "((x \<sqinter> nc) \<cdot> nc) \<parallel> ((y \<sqinter> nc) \<cdot> nc) = ((x \<sqinter> nc) \<cdot>  nc) \<sqinter> ((y \<sqinter> nc) \<cdot> nc)"
proof -
  have "((x \<sqinter> nc) \<cdot> nc) \<parallel> ((y \<sqinter> nc) \<cdot> nc) = (d (x \<sqinter> nc) \<cdot> nc) \<parallel> (d (y \<sqinter> nc) \<cdot> nc)"
    by (metis cl11_d)
  also have "... = (d (x \<sqinter> nc) \<parallel> d (y \<sqinter> nc)) \<cdot> nc"
    by (simp add: nsv_hom_par)
  also have "... = (d (x \<sqinter> nc) \<sqinter> d (y \<sqinter> nc)) \<cdot> nc"
    by (simp add: d_p_prod_eq_meet)
  also have "...  = (d (x \<sqinter> nc) \<cdot>  nc) \<sqinter> (d (y \<sqinter> nc) \<cdot> nc)"
    by (simp add: nsv_hom_meet)
  thus ?thesis
    by (simp add: calculation)
qed

lemma nvs_hom_meet: "d (((x \<sqinter> nc) \<cdot> nc) \<sqinter> ((y \<sqinter> nc) \<cdot> nc)) = d ((x \<sqinter> nc) \<cdot> nc) \<sqinter> d ((y \<sqinter> nc) \<cdot> nc)"
  by (metis d_p_prod_eq_meet local.d_conc6 vec_p_prod_meet)

lemma ncv_hom_meet: "(x \<cdot> 1\<^sub>\<pi> \<sqinter> y \<cdot> 1\<^sub>\<pi>) \<parallel> nc = (x \<cdot> 1\<^sub>\<pi>) \<parallel> nc \<sqinter> (y \<cdot> 1\<^sub>\<pi>) \<parallel> nc"
  by (metis d_p_prod_eq_meet local.c2_d local.c3 local.d_conc6 nsv_hom_meet p_subid_par_eq_meet_var)

lemma ncv_hom_par: "(x \<parallel> y) \<parallel> nc = x \<parallel> nc \<parallel> y \<parallel> nc"
  by (metis local.mult_assoc local.mult_commute nc_nc_par)

lemma nvc_hom_meet: "((x \<sqinter> nc) \<cdot>  nc \<sqinter> (y \<sqinter> nc) \<cdot> nc) \<cdot> 1\<^sub>\<pi> = ((x \<sqinter> nc) \<cdot>  nc) \<cdot> 1\<^sub>\<pi> \<sqinter> ((y \<sqinter> nc) \<cdot> nc) \<cdot> 1\<^sub>\<pi>"
  by (metis local.c3 p_subid_par_eq_meet_var vec_p_prod_meet)

subsection \<open>Terminal and Nonterminal Elements\<close>

text \<open>Now we define the projection functions on terminals and nonterminal parts and verify the properties
of Section 11 in~\cite{FurusawaS15a}.\<close>

definition tau :: "'a \<Rightarrow> 'a" ("\<tau>") where 
  "\<tau> x = x \<cdot> 0"

definition nu :: "'a \<Rightarrow> 'a" ("\<nu>") where 
  "\<nu> x = x \<sqinter> nc"

text \<open>Lemma 11.1.\<close>

lemma tau_int: "\<tau> x \<le> x"
  by (metis c_0 local.inf_le1 tau_def)

lemma nu_int: "\<nu> x \<le> x"
  by (simp add: nu_def)

lemma tau_ret [simp]: "\<tau> (\<tau> x) = \<tau> x"
  by (simp add: tau_def)

lemma nu_ret [simp]: "\<nu> (\<nu> x) = \<nu> x"
  by (simp add: local.meet_assoc nu_def)

lemma tau_iso: "x \<le> y \<Longrightarrow> \<tau> x \<le> \<tau> y"
  using local.order_prop local.s_prod_distr tau_def by auto

lemma nu_iso: "x \<le> y \<Longrightarrow> \<nu> x \<le> \<nu> y"
  using local.inf_mono nu_def by auto

text \<open>Lemma 11.2.\<close>

lemma tau_zero [simp]: "\<tau> 0 = 0"
  by (simp add: tau_def)

lemma nu_zero [simp]: "\<nu> 0 = 0"
  using nu_def by auto

lemma tau_s [simp]: "\<tau> 1\<^sub>\<sigma> = 0"
  using tau_def by auto

lemma nu_s [simp]: "\<nu> 1\<^sub>\<sigma> = 1\<^sub>\<sigma>"
  using nu_def by auto

lemma tau_c [simp]: "\<tau> 1\<^sub>\<pi> = 1\<^sub>\<pi>"
  using c_x_prop tau_def by presburger

lemma nu_c [simp]: "\<nu> 1\<^sub>\<pi> = 0"
  using c_nc_comp2 nu_def by presburger

lemma tau_nc [simp]: "\<tau> nc = 0"
  using nc_iff2 tau_def by auto

lemma nu_nc [simp]: "\<nu> nc = nc"
  using nu_def by auto

lemma tau_U [simp]: "\<tau> U = 1\<^sub>\<pi>"
  using c_def tau_def by presburger

lemma nu_U [simp]: "\<nu> U = nc"
  using local.U_def local.meet_comm local.inf.absorb_iff1 nu_def by fastforce

text \<open>Lemma 11.3.\<close>

lemma tau_add [simp]: "\<tau> (x + y) = \<tau> x + \<tau> y"
  by (simp add: tau_def x_zero_add_closed)

lemma nu_add [simp]: "\<nu> (x + y) = \<nu> x + \<nu> y"
  by (simp add: local.lat_dist3 local.meet_comm nu_def)

lemma tau_meet [simp]: "\<tau> (x \<sqinter> y) = \<tau> x \<sqinter> \<tau> y"
  using tau_def x_zero_meet_closed by auto

lemma nu_meet [simp]: "\<nu> (x \<sqinter> y) = \<nu> x \<sqinter> \<nu> y"
  using nc_meet_closed nu_def by auto

lemma tau_seq: "\<tau> (x \<cdot> y) = \<tau> x + \<nu> x \<cdot> \<tau> y"
  using local.add_comm nu_def tau_def x_y_split zero_assoc3 by presburger

lemma tau_par [simp]: "\<tau> (x \<parallel> y) = \<tau> x \<parallel> \<tau> y"
  using tau_def x_zero_interr by presburger

lemma nu_par_aux1: "x \<parallel> \<tau> y = d (\<tau> y) \<cdot> x"
  by (simp add: local.c2_d local.mult_commute tau_def)

lemma nu_par_aux2 [simp]: "\<nu> (\<nu> x \<parallel> \<nu> y) = \<nu> x \<parallel> \<nu> y"
  by (simp add: nu_def)

lemma nu_par_aux3 [simp]:  "\<nu> (\<nu> x \<parallel> \<tau> y) = \<nu> x \<parallel> \<tau> y"
  by (metis local.mult_commute nc_ccomp_closed_alt nu_def)

lemma nu_par_aux4 [simp]: "\<nu> (\<tau> x \<parallel> \<tau> y) = 0"
  by (metis nu_def tau_def tau_par zero_nc)

lemma nu_par: "\<nu> (x \<parallel> y) = d (\<tau> x) \<cdot> \<nu> y + d (\<tau> y) \<cdot> \<nu> x + \<nu> x \<parallel> \<nu> y"
proof -
  have "\<nu> (x \<parallel> y) = \<nu> (\<nu> x \<parallel> \<nu> y) + \<nu> (\<nu> x \<parallel> \<tau> y) + \<nu> (\<tau> x \<parallel> \<nu> y) + \<nu> (\<tau> x \<parallel> \<tau> y)"
    by (metis local.distrib_left local.distrib_right nu_add nu_def tau_def x_split_var join.sup.commute join.sup.left_commute)
  also have "\<nu> (x \<parallel> y) = \<nu> x \<parallel> \<nu> y  + \<nu> x \<parallel> \<tau> y + \<tau> x \<parallel> \<nu> y"
    by (simp add: calculation local.c_prod_comm)
  thus ?thesis
    using local.join.sup_assoc local.join.sup_commute local.mult_commute nu_par_aux1 by auto
qed

text \<open>Lemma 11.5.\<close>

lemma sprod_tau_nu: "x \<cdot> y = \<tau> x + \<nu> x \<cdot> y"
  by (metis local.add_comm nu_def tau_def x_y_split)

lemma pprod_tau_nu: "x \<parallel> y = \<nu> x \<parallel> \<nu> y + d (\<tau> x) \<cdot> \<nu> y + d (\<tau> y) \<cdot> \<nu> x + \<tau> x \<parallel> \<tau> y"
proof -
  have "x \<parallel> y = \<nu> (x \<parallel> y) + \<tau> (x \<parallel> y)"
    by (simp add: nu_def tau_def)
  also have "... = (d (\<tau> x) \<cdot> \<nu> y + d (\<tau> y) \<cdot> \<nu> x + \<nu> x \<parallel> \<nu> y) + \<tau> x \<parallel> \<tau> y"
    by (simp add: nu_par)
  thus ?thesis
    using add_assoc add_commute calculation by force
qed

text \<open>We now verify some additional properties which are not mentioned in the paper.\<close>

lemma tau_idem [simp]: "\<tau> x \<cdot> \<tau> x = \<tau> x"
  by (simp add: tau_def)

lemma tau_interr: "(x \<parallel> y) \<cdot> \<tau> z = (x \<cdot> \<tau> z) \<parallel> (y \<cdot> \<tau> z)"
  by (simp add: local.cl4 tau_def)

lemma tau_le_c: "\<tau> x \<le> 1\<^sub>\<pi>"
  by (simp add: local.x_zero_le_c tau_def)

lemma c_le_tauc: "1\<^sub>\<pi> \<le> \<tau> 1\<^sub>\<pi>"
  using local.eq_refl tau_c by presburger

lemma x_alpha_tau [simp]: "\<nu> x + \<tau> x = x"
  using nu_def tau_def x_split_var by presburger

lemma alpha_tau_zero [simp]: "\<nu> (\<tau> x) = 0"
  by (simp add: nu_def tau_def)

lemma tau_alpha_zero [simp]: "\<tau> (\<nu> x) = 0"
  by (simp add: nu_def tau_def)

lemma sprod_tau_nu_var [simp]: "\<nu> (\<nu> x \<cdot> y) = \<nu> (x \<cdot> y)"
proof -
  have "\<nu> (x \<cdot> y) = \<nu> (\<tau> x) + \<nu> (\<nu> x \<cdot> y)"
    by (metis nu_add sprod_tau_nu)
  thus ?thesis
    by simp
qed

lemma tau_s_prod [simp]: "\<tau> (x \<cdot> y) = x \<cdot> \<tau> y"
  by (simp add: tau_def zero_assoc3)

lemma alpha_fp: "\<nu> x = x \<longleftrightarrow> x \<cdot> 0 = 0"
  by (metis local.add_zeror tau_alpha_zero tau_def x_alpha_tau)

lemma alpha_prod_closed [simp]: "\<nu> (\<nu> x \<cdot> \<nu> y) = \<nu> x \<cdot> \<nu> y"
  by (simp add: nu_def)

lemma alpha_par_prod [simp]: "\<nu> (x \<parallel> \<nu> y) = x \<parallel> \<nu> y"
  by (simp add: nu_def)

lemma p_prod_tau_alpha: "x \<parallel> y = x \<parallel> \<nu> y + \<nu> x \<parallel> y + \<tau> x \<parallel> \<tau> y"
proof -
  have "x \<parallel> y = (\<nu> x + \<tau> x) \<parallel> (\<nu> y + \<tau> y)"
    using x_alpha_tau by simp
  also have "... = \<nu> x \<parallel> \<nu> y  + \<nu> x \<parallel> \<tau> y + \<tau> x \<parallel> \<nu> y + \<tau> x \<parallel> \<tau> y"
    by (metis add_commute local.combine_common_factor local.p_prod_distl)
  also have "... = (\<nu> x \<parallel> \<nu> y  + \<nu> x \<parallel> \<tau> y) + (\<nu> x  \<parallel> \<nu> y + \<tau> x \<parallel> \<nu> y) + \<tau> x \<parallel> \<tau> y"
    by (simp add: add_ac)
  thus ?thesis
    by (metis calculation local.add_comm local.distrib_left local.distrib_right x_alpha_tau)
qed

lemma p_prod_tau_alpha_var: "x \<parallel> y = x \<parallel> \<nu> y + \<nu> x \<parallel> y + \<tau> (x \<parallel> y)"
  by (metis p_prod_tau_alpha tau_par)

lemma alpha_par: "\<nu> (x \<parallel> y) = \<nu> x \<parallel> y + x \<parallel> \<nu> y"
proof -
  have  "\<nu> (x \<parallel> y) = \<nu> (x \<parallel> \<nu> y) + \<nu> (\<nu> x \<parallel> y) + \<nu> (\<tau> (x \<parallel> y))"
    by (metis nu_add p_prod_tau_alpha_var)
  thus ?thesis
    by (simp add: local.mult_commute add_ac)
qed

lemma alpha_tau [simp]: "\<nu> (x \<cdot> \<tau> y) = 0"
  by (metis alpha_tau_zero tau_s_prod)

lemma nu_par_prop: "\<nu> x = x \<Longrightarrow> \<nu> (x \<parallel> y) = x \<parallel> y"
  by (metis alpha_par_prod local.mult_commute)

lemma tau_seq_prop: "\<tau> x = x \<Longrightarrow> x \<cdot> y  = x"
  by (metis local.cl6 tau_def)

lemma tau_seq_prop2: "\<tau> y = y \<Longrightarrow> \<tau> (x \<cdot> y)  = x \<cdot> y"
  by auto

lemma d_nu: "\<nu> (d x \<cdot> y) = d x \<cdot> \<nu> y"
proof -
  have "\<nu> (d x \<cdot> y) = \<nu> ((x \<cdot> 1\<^sub>\<pi>) \<parallel> y)"
    by (simp add: local.c2_d)
  also have "... = d (\<tau> (x \<cdot> 1\<^sub>\<pi>)) \<cdot> \<nu> y + d (\<tau> y) \<cdot> \<nu> (x \<cdot> 1\<^sub>\<pi>) + \<nu> (x \<cdot> 1\<^sub>\<pi>) \<parallel> \<nu> y"
    by (simp add:  nu_par)
  thus ?thesis
    using alpha_par local.c2_d nu_def by force
qed

text \<open>Lemma 11.6 and 11.7.\<close>

lemma nu_ideal1: "\<lbrakk>\<nu> x = x; y \<le> x\<rbrakk> \<Longrightarrow> \<nu> y = y"
  by (metis local.meet_prop local.inf.absorb_iff1 nu_def)

lemma tau_ideal1: "\<lbrakk>\<tau> x = x; y \<le> x\<rbrakk> \<Longrightarrow> \<tau> y = y"
  by (metis local.dual_order.trans tau_def term_p_subid_var)

lemma nu_ideal2: "\<lbrakk>\<nu> x = x; \<nu> y = y\<rbrakk> \<Longrightarrow> \<nu> (x + y) = x + y"
  by (simp add: local.lat_dist3 local.meet_comm)

lemma tau_ideal2: "\<lbrakk>\<tau> x = x; \<tau> y = y\<rbrakk> \<Longrightarrow> \<tau> (x + y) = x + y"
  by simp

lemma tau_ideal3: "\<tau> x = x \<Longrightarrow> \<tau> (x \<cdot> y) = x \<cdot> y"
  by (simp add: tau_seq_prop)

text \<open>We prove the precongruence properties of Lemma 11.9.\<close>

lemma tau_add_precong: "\<tau> x \<le> \<tau> y \<Longrightarrow> \<tau> (x + z) \<le> \<tau> (y + z)"
proof -
  assume "\<tau> x \<le> \<tau> y"
  hence "(x + y) \<cdot> 0 = y \<cdot> 0" using local.less_eq_def local.s_prod_distr tau_def 
    by auto
  hence "(x + z + y) \<cdot> 0 = (y + z) \<cdot> 0" 
    by (metis (no_types) add_assoc add_commute local.s_prod_distr)
  thus "\<tau> (x + z) \<le> \<tau> (y + z)" using local.order_prop local.s_prod_distr tau_def
    by metis
qed

lemma tau_meet_precong: "\<tau> x \<le> \<tau> y \<Longrightarrow> \<tau> (x \<sqinter> z) \<le> \<tau> (y \<sqinter> z)"
proof -
  assume "\<tau> x \<le> \<tau> y"
  hence "\<And>z. (x \<sqinter> y \<sqinter> z) \<cdot> 0 = (x \<sqinter> z) \<cdot> 0"
    by (metis local.le_iff_inf tau_def x_zero_meet_closed)
  thus ?thesis
    using local.inf_left_commute local.le_iff_inf local.meet_comm tau_def x_zero_meet_closed by fastforce
qed
 
lemma tau_par_precong: "\<tau> x \<le> \<tau> y \<Longrightarrow> \<tau> (x \<parallel> z) \<le> \<tau> (y \<parallel> z)"
proof -
  assume "\<tau> x \<le> \<tau> y"
  hence "x \<parallel> z \<cdot> 0 \<le> y \<cdot> 0" 
    by (metis (no_types) local.dual_order.trans local.p_subid_lb1 tau_def tau_par)
  thus "\<tau> (x \<parallel> z) \<le> \<tau> (y \<parallel> z)"
    by (simp add: \<open>\<tau> x \<le> \<tau> y\<close> local.mult_isor) 
qed

lemma tau_seq_precongl: "\<tau> x \<le> \<tau> y \<Longrightarrow> \<tau> (z \<cdot> x) \<le> \<tau> (z \<cdot> y)"
  by (simp add: local.s_prod_isol)

lemma nu_add_precong: "\<nu> x \<le> \<nu> y \<Longrightarrow> \<nu> (x + z) \<le> \<nu> (y + z)"
proof -
  assume "\<nu> x \<le> \<nu> y"
  hence "\<nu> x = \<nu> x \<sqinter> \<nu> y"
    using local.inf.absorb_iff1 by auto
  hence "\<forall>a. \<nu> (x + a) = \<nu> (x + a) \<sqinter> \<nu> (y + a)"
    by (metis (no_types) local.lat_dist2 nu_add)
  thus ?thesis
    using local.inf.absorb_iff1 by presburger
qed

lemma nu_meet_precong: "\<nu> x \<le> \<nu> y \<Longrightarrow> \<nu> (x \<sqinter> z) \<le> \<nu> (y \<sqinter> z)"
proof -
  assume "\<nu> x \<le> \<nu> y"
  hence "\<nu> y = \<nu> x + \<nu> y"
    using local.less_eq_def by auto
  hence "\<nu> (y \<sqinter> z) = \<nu> (x \<sqinter> z) + \<nu> (y \<sqinter> z)"
    by (metis (no_types) local.lat_dist4 nu_meet)
  thus ?thesis
    using local.less_eq_def by presburger
qed

lemma nu_seq_precongr: "\<nu> x \<le> \<nu> y \<Longrightarrow> \<nu> (x \<cdot> z) \<le> \<nu> (y \<cdot> z)"
proof -
  assume a: "\<nu> x \<le> \<nu> y"
  have "\<nu> (x \<cdot> z) = \<nu> (\<nu> x \<cdot> z)"
    by simp
  also have "... \<le> \<nu> (\<nu> y \<cdot> z)"
    by (metis a local.less_eq_def local.s_prod_distr nu_iso)
  thus ?thesis
    by simp
qed

text\<open>We prove the congruence properties of Corollary~11.11.\<close>

definition tcg :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  where 
  "tcg x y = (\<tau> x \<le> \<tau> y \<and> \<tau> y \<le> \<tau> x)"

definition ncg :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  where 
  "ncg x y = (\<nu> x \<le> \<nu> y \<and> \<nu> y \<le> \<nu> x)"

lemma tcg_refl: "tcg x x"
  by (simp add: tcg_def)

lemma tcg_trans: "\<lbrakk>tcg x y; tcg y z\<rbrakk> \<Longrightarrow> tcg x z"
  using tcg_def by force

lemma tcg_sym: "tcg x y \<Longrightarrow> tcg y x"
  by (simp add: tcg_def)

lemma ncg_refl: "ncg x x"
  using ncg_def by blast

lemma ncg_trans: "\<lbrakk>ncg x y; ncg y z\<rbrakk> \<Longrightarrow> ncg x z"
  using ncg_def by force

lemma ncg_sym: "ncg x y \<Longrightarrow> ncg y x"
  using ncg_def by auto

lemma tcg_alt: "tcg x y = (\<tau> x = \<tau> y)"
  using tcg_def by auto

lemma ncg_alt: "ncg x y = (\<nu> x = \<nu> y)"
  by (simp add: local.eq_iff ncg_def)

lemma tcg_add: "\<tau> x = \<tau> y \<Longrightarrow> \<tau> (x + z) = \<tau> (y + z)"
  by simp

lemma tcg_meet: "\<tau> x = \<tau> y \<Longrightarrow> \<tau> (x \<sqinter> z) = \<tau> (y \<sqinter> z)"
  by simp

lemma tcg_par: "\<tau> x = \<tau> y \<Longrightarrow> \<tau> (x \<parallel> z) = \<tau> (y \<parallel> z)"
  by simp 

lemma tcg_seql: "\<tau> x = \<tau> y \<Longrightarrow> \<tau> (z \<cdot> x) = \<tau> (z \<cdot> y)"
  by simp

lemma ncg_add: "\<nu> x = \<nu> y \<Longrightarrow> \<nu> (x + z) = \<nu> (y + z)"
  by simp

lemma ncg_meet: "\<nu> x = \<nu> y \<Longrightarrow> \<nu> (x \<sqinter> z) = \<nu> (y \<sqinter> z)"
  by simp

lemma ncg_seqr: "\<nu> x = \<nu> y \<Longrightarrow> \<nu> (x \<cdot> z) = \<nu> (y \<cdot> z)"
  by (simp add: local.eq_iff nu_seq_precongr)

end

subsection \<open>Powers in C-Algebras\<close>

text \<open>We define the power functions from Section~6 in~\cite{FurusawaS15a} after Lemma~12.4.\<close>

context proto_dioid
begin

primrec p_power :: "'a  \<Rightarrow> nat \<Rightarrow> 'a"  where
 "p_power x 0       = 1\<^sub>\<sigma>" |
 "p_power x (Suc n) = x \<cdot> p_power x n"

primrec power_rd :: "'a  \<Rightarrow> nat \<Rightarrow> 'a"  where
 "power_rd x 0       = 0" |
 "power_rd x (Suc n) = 1\<^sub>\<sigma> + x \<cdot> power_rd x n"

primrec power_sq :: "'a  \<Rightarrow> nat \<Rightarrow> 'a"  where
 "power_sq x 0       = 1\<^sub>\<sigma>" |
 "power_sq x (Suc n) = 1\<^sub>\<sigma> + x \<cdot> power_sq x n"

text \<open>Lemma~12.5\<close>

lemma power_rd_chain: "power_rd x n \<le> power_rd x (n + 1)"
  by (induct n, simp, metis Suc_eq_plus1 local.add_comm local.add_iso local.s_prod_isol power_rd.simps(2))

lemma power_sq_chain: "power_sq x n \<le> power_sq x (n + 1)"
  by (induct n, clarsimp, metis Suc_eq_plus1 local.add_comm local.add_iso local.s_prod_isol power_sq.simps(2))

lemma pow_chain: "p_power (1\<^sub>\<sigma> + x) n \<le> p_power (1\<^sub>\<sigma> + x) (n + 1)"
  by (induct n, simp, metis Suc_eq_plus1 local.p_power.simps(2) local.s_prod_isol)

lemma pow_prop: "p_power (1\<^sub>\<sigma> + x) (n + 1) = 1\<^sub>\<sigma> + x \<cdot> p_power (1\<^sub>\<sigma> + x) n" 
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have f1: "p_power (1\<^sub>\<sigma> + x) (Suc n + 1) = 1\<^sub>\<sigma> + x \<cdot> p_power (1\<^sub>\<sigma> + x) n + x \<cdot> p_power (1\<^sub>\<sigma> + x) (n + 1)"
  proof -
    have "p_power (1\<^sub>\<sigma> + x) (Suc (n + 1)) = (1\<^sub>\<sigma> + x) \<cdot> p_power (1\<^sub>\<sigma> + x) (n + 1)"
      using local.p_power.simps(2) by blast
    also have "... = p_power (1\<^sub>\<sigma> + x) (n + 1) + x \<cdot> p_power (1\<^sub>\<sigma> + x) (n + 1)"
      by (metis local.s_prod_distr local.s_prod_idl)
    also have "... = 1\<^sub>\<sigma> + x \<cdot> p_power (1\<^sub>\<sigma> + x) n + x \<cdot> p_power (1\<^sub>\<sigma> + x) (n + 1)"
      using Suc.hyps by auto
    finally  show ?thesis
      by simp
  qed
  have "x \<cdot> p_power (1\<^sub>\<sigma> + x) (Suc n) = x \<cdot> p_power (1\<^sub>\<sigma> + x) n + x \<cdot> p_power (1\<^sub>\<sigma> + x) (n + 1)"
    using Suc_eq_plus1 local.less_eq_def local.s_prod_isol pow_chain by simp
  with f1 show ?case by (simp add: add_ac)
qed

text \<open>Next we verify facts from the proofs of Lemma~12.6.\<close>

lemma power_rd_le_sq: "power_rd x n \<le> power_sq x n"
  by (induct n, simp, simp add: local.join.le_supI2 local.s_prod_isol)

lemma power_sq_le_rd: "power_sq x n \<le> power_rd x (Suc n)"
  by (induct n, simp, simp add: local.join.le_supI2 local.s_prod_isol)

lemma power_sq_power: "power_sq x n = p_power (1\<^sub>\<sigma> + x) n"
  apply (induct n)
  apply (simp)
  using Suc_eq_plus1 pow_prop power_sq.simps(2) by simp

end

subsection \<open>C-Kleene Algebras\<close>

text \<open>The definition of c-Kleene algebra is slightly different from that in Section~6
of~\cite{FurusawaS15a}. It is used to prove properties from Section~6 and Section~12.\<close>

class c_kleene_algebra = c_lattice + star_op +
  assumes star_unfold: "1\<^sub>\<sigma> + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and star_induct: "1\<^sub>\<sigma> + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y"

begin

lemma star_irr: "1\<^sub>\<sigma> \<le> x\<^sup>\<star>"
  using local.star_unfold by auto

lemma star_unfold_part: "x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  using local.star_unfold by auto

lemma star_ext_aux: "x \<le> x \<cdot> x\<^sup>\<star>"
  using local.s_prod_isol star_irr by fastforce

lemma star_ext: "x \<le> x\<^sup>\<star>"
  using local.order_trans star_ext_aux star_unfold_part by blast

lemma star_co_trans: "x\<^sup>\<star> \<le>  x\<^sup>\<star> \<cdot> x\<^sup>\<star>"
  using local.s_prod_isol star_irr by fastforce

lemma star_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
proof -
  assume a1: "x \<le> y"
  have f2: "y \<cdot> y\<^sup>\<star> + y\<^sup>\<star> = y\<^sup>\<star>"
    by (meson local.less_eq_def star_unfold_part)
  have "x + y = y"
    using a1 by (meson local.less_eq_def)
  hence "x \<cdot> y\<^sup>\<star> + y\<^sup>\<star> = y\<^sup>\<star>"
    using f2 by (metis (no_types) local.add_assoc' local.s_prod_distr)
  thus ?thesis
    using local.add_assoc' local.less_eq_def local.star_induct star_irr by presburger
qed

lemma star_unfold_eq [simp]: "1\<^sub>\<sigma> + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
proof (rule antisym)
  show a: "1\<^sub>\<sigma> + x \<cdot> x\<^sup>\<star> \<le>  x\<^sup>\<star>"
    using local.star_unfold by blast
  have "1\<^sub>\<sigma> + x \<cdot> (1\<^sub>\<sigma> + x \<cdot> x\<^sup>\<star>) \<le> 1\<^sub>\<sigma> + x \<cdot> x\<^sup>\<star>"
    by (meson local.eq_refl local.join.sup_mono local.s_prod_isol local.star_unfold)
  thus "x\<^sup>\<star> \<le> 1\<^sub>\<sigma> + x \<cdot> x\<^sup>\<star>"
    by (simp add: local.star_induct)
qed

text \<open>Lemma 12.2.\<close>

lemma nu_star1:
assumes "\<And>x y z. x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z"
shows "x\<^sup>\<star> \<le> (\<nu> x)\<^sup>\<star> \<cdot> (1\<^sub>\<sigma> + \<tau> x)"
proof -
  have "1\<^sub>\<sigma> + x \<cdot> ((\<nu> x)\<^sup>\<star> \<cdot> (1\<^sub>\<sigma> + \<tau> x)) = 1\<^sub>\<sigma> + \<tau> x + \<nu> x \<cdot> ((\<nu> x)\<^sup>\<star> \<cdot> (1\<^sub>\<sigma> + \<tau> x))"
    by (metis add_assoc local.sprod_tau_nu)
  also have "... = (1\<^sub>\<sigma> + \<nu> x \<cdot> (\<nu> x)\<^sup>\<star>) \<cdot> (1\<^sub>\<sigma> + \<tau> x)"
    using assms local.s_prod_distr local.s_prod_idl by presburger
  also have "... \<le> (\<nu> x)\<^sup>\<star> \<cdot> (1\<^sub>\<sigma> + \<tau> x)"
    using local.s_prod_isor local.star_unfold by auto
  thus ?thesis
    by (simp add: calculation local.star_induct)
qed

lemma nu_star2: 
assumes "\<And>x. x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
shows "(\<nu> x)\<^sup>\<star> \<cdot> (1\<^sub>\<sigma> + \<tau> x) \<le> x\<^sup>\<star>"
proof -
  have "(\<nu> x)\<^sup>\<star> \<cdot> (1\<^sub>\<sigma> + \<tau> x) \<le> x\<^sup>\<star> \<cdot> (1\<^sub>\<sigma> + \<tau> x)"
    using local.nu_int local.s_prod_isor star_iso by blast
  also have "... \<le>  x\<^sup>\<star> \<cdot> (1\<^sub>\<sigma> + x)"
    using local.s_prod_isol local.join.sup_mono local.tau_int by blast
  also have "... \<le> x\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    by (simp add: local.s_prod_isol star_ext star_irr)
  finally show ?thesis
    using assms local.order_trans by blast
qed

lemma nu_star: 
assumes "\<And>x. x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
and "\<And>x y z. x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z"
shows "(\<nu> x)\<^sup>\<star> \<cdot> (1\<^sub>\<sigma> + \<tau> x) = x\<^sup>\<star>"
  by (simp add: assms(1) assms(2) local.dual_order.antisym nu_star1 nu_star2)

text \<open>Lemma 12.3.\<close>

lemma tau_star: "(\<tau> x)\<^sup>\<star> = 1\<^sub>\<sigma> + \<tau> x"
  by (metis local.cl6 local.tau_def star_unfold_eq)

lemma tau_star_var: 
assumes "\<And>x y z. x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z"
and "\<And>x. x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
shows "\<tau> (x\<^sup>\<star>) = (\<nu> x)\<^sup>\<star> \<cdot> \<tau> x"
  by (metis (no_types, lifting) assms(1) assms(2) local.add_0_right local.add_comm local.s_prod_distr local.s_prod_idl local.tau_def local.tau_zero nu_star)

lemma nu_star_sub: "(\<nu> x)\<^sup>\<star> \<le> \<nu> (x\<^sup>\<star>)"
  by (metis add_commute local.less_eq_def local.meet_prop local.nc_nc local.nu_def local.order.refl local.s_le_nc local.star_induct star_iso)

lemma nu_star_nu [simp]: "\<nu> ((\<nu> x)\<^sup>\<star>) = (\<nu> x)\<^sup>\<star>"
  using local.nu_ideal1 local.nu_ret nu_star_sub by blast

lemma nu_star_tau [simp]: "\<nu> ((\<tau> x)\<^sup>\<star>) = 1\<^sub>\<sigma>"
  using tau_star by fastforce

lemma tau_star_tau [simp]: "\<tau> ((\<tau> x)\<^sup>\<star>) = \<tau> x"
  using local.s_prod_distr tau_star by auto

lemma tau_star_nu [simp]: "\<tau> ((\<nu> x)\<^sup>\<star>) = 0"
  using local.alpha_fp local.tau_def nu_star_nu by presburger

text \<open>Finally we verify Lemma 6.2. Proofs can be found in~\cite{FurusawaS15b}.\<close>

lemma d_star_unfold [simp]: 
assumes "\<And>x y z. (x \<cdot> y) \<cdot> d z = x \<cdot> (y \<cdot> d z)"
shows "d y + d (x \<cdot> d (x\<^sup>\<star> \<cdot> y)) = d (x\<^sup>\<star> \<cdot> y)"
proof -
  have "d y + d (x \<cdot> d (x\<^sup>\<star> \<cdot> y)) = d y + d (x \<cdot> (x\<^sup>\<star> \<cdot> d y))"
    by (metis local.c4 local.d_def local.dc_prop1)
  moreover have "... =  d (1\<^sub>\<sigma> \<cdot> d y + (x \<cdot> (x\<^sup>\<star> \<cdot> d y)))"
    by (simp add: local.d_add_ax)
  moreover have "... =  d (1\<^sub>\<sigma> \<cdot> d y + (x \<cdot> x\<^sup>\<star>) \<cdot> d y)"
    by (simp add: assms)
  moreover have "... = d ((1\<^sub>\<sigma> + x \<cdot> x\<^sup>\<star>) \<cdot> d y)"
    using local.s_prod_distr by presburger
  ultimately show ?thesis
    by simp
qed

lemma d_star_sim1: 
assumes "\<And> x y z. d z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> d z \<le> y"
and "\<And> x y z. (x \<cdot> d y) \<cdot> z = x \<cdot> (d y \<cdot> z)"
and "\<And> x y z. (d x \<cdot> y) \<cdot> z = d x \<cdot> (y \<cdot> z)"
shows "x \<cdot> d z \<le> d z \<cdot> y \<Longrightarrow> x\<^sup>\<star> \<cdot> d z \<le> d z \<cdot> y\<^sup>\<star>"
proof -
fix x y z
assume a: "x \<cdot> d z \<le> d z \<cdot> y"
  have b: "x \<cdot> (d z \<cdot> y\<^sup>\<star>) \<le> d z \<cdot> (y \<cdot> y\<^sup>\<star>)"
    by (metis a assms(2) assms(3) local.s_prod_isor)
  hence "x \<cdot> (d z \<cdot> y\<^sup>\<star>) \<le> d z \<cdot> y\<^sup>\<star>"
  proof -
    have f1: "x \<cdot> (y\<^sup>\<star> \<parallel> (z \<cdot> 1\<^sub>\<pi>)) \<le> z \<cdot> 1\<^sub>\<pi> \<parallel> (y \<cdot> y\<^sup>\<star>)"
      using b local.c2_d local.mult_commute by auto
    have "\<exists>a. (a + z \<cdot> 1\<^sub>\<pi>) \<parallel> (y \<cdot> y\<^sup>\<star>) \<le> y\<^sup>\<star> \<parallel> (z \<cdot> 1\<^sub>\<pi>)"
      by (metis (no_types) local.eq_refl local.mult_commute local.mult_isol_var local.join.sup_idem star_unfold_part)
    hence "x \<cdot> (y\<^sup>\<star> \<parallel> (z \<cdot> 1\<^sub>\<pi>)) \<le> y\<^sup>\<star> \<parallel> (z \<cdot> 1\<^sub>\<pi>)"
      using f1 by (metis (no_types) local.distrib_right' local.dual_order.trans local.join.sup.cobounded2)
    thus ?thesis
      using local.c2_d local.mult_commute by auto
  qed
  hence "d z + x \<cdot> (d z \<cdot> y\<^sup>\<star>)\<le> d z \<cdot> y\<^sup>\<star>"
    using local.s_prod_isol star_irr by fastforce
  thus "x\<^sup>\<star> \<cdot> d z \<le> d z \<cdot> y\<^sup>\<star>" 
    using assms(1) by force
qed

lemma d_star_induct: 
assumes "\<And> x y z. d z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> d z \<le> y"
and "\<And> x y z. (x \<cdot> d y) \<cdot> z = x \<cdot> (d y \<cdot> z)"
and "\<And> x y z. (d x \<cdot> y) \<cdot> z = d x \<cdot> (y \<cdot> z)"
shows "d (x \<cdot> y) \<le> d y \<Longrightarrow> d (x\<^sup>\<star> \<cdot> y) \<le> d y"
proof -
  fix x y
  assume "d (x \<cdot> y) \<le> d y"
  hence  "x \<cdot> d y \<le> d y \<cdot> x"
    by (simp add: demod1)
  hence  "x\<^sup>\<star> \<cdot> d y \<le> d y \<cdot> x\<^sup>\<star>"
    using assms(1) assms(2) assms(3) d_star_sim1 by blast
  thus "d (x\<^sup>\<star> \<cdot> y) \<le> d y"
    by (simp add: demod2)
qed

end

subsection \<open>C-Omega Algebras\<close>

text \<open>These structures do not feature in~\cite{FurusawaS15a}, but in fact, 
many lemmas from Section 13 can be proved in this setting. The proto-quantales and c-quantales
using in~\cite{FurusawaS15a} provide a more expressive setting in which least and greatest fixpoints 
need not be postulated; they exists due to properties of sequential composition and addition over 
complete lattices.\<close>

class c_omega_algebra = c_kleene_algebra + omega_op +
  assumes om_unfold: "x\<^sup>\<omega> \<le> x \<cdot> x\<^sup>\<omega>"
  and om_coinduct: "y \<le> x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<omega>"

begin

text \<open>Lemma 13.4.\<close>

lemma om_unfold_eq [simp]: "x \<cdot> x\<^sup>\<omega> = x\<^sup>\<omega>"
  apply (rule antisym)
  using local.om_coinduct local.om_unfold local.s_prod_isol by auto

lemma om_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<omega> \<le> y\<^sup>\<omega>"
  by (metis local.om_coinduct local.s_prod_isor om_unfold_eq)
 
text \<open>Lemma 13.5.\<close>

lemma zero_om [simp]: "0\<^sup>\<omega> = 0"
  by (metis local.s_prod_annil om_unfold_eq)

lemma s_id_om [simp]: "1\<^sub>\<sigma>\<^sup>\<omega> = U"
  by (simp add: local.U_def local.eq_iff local.om_coinduct)

lemma p_id_om [simp]: "1\<^sub>\<pi>\<^sup>\<omega> = 1\<^sub>\<pi>"
  by (metis local.c_x_prop om_unfold_eq)

lemma nc_om [simp]: "nc\<^sup>\<omega> = U"
  using local.U_def local.eq_iff local.s_le_nc om_iso s_id_om by blast

lemma U_om [simp]: "U\<^sup>\<omega> = U"
  by (simp add: local.U_def local.eq_iff local.om_coinduct)

text \<open>Lemma 13.6.\<close>

lemma tau_om1: "\<tau> x \<le> \<tau> (x\<^sup>\<omega>)"
  using local.om_coinduct local.s_prod_isor local.tau_def local.tau_int by fastforce

lemma tau_om2 [simp]: "\<tau> x\<^sup>\<omega> = \<tau> x"
  by (metis local.cl6 local.tau_def om_unfold_eq)

lemma tau_om3: "(\<tau> x)\<^sup>\<omega> \<le> \<tau> (x\<^sup>\<omega>)"
  by (simp add: tau_om1)

text \<open>Lemma 13.7.\<close>

lemma om_nu_tau: "(\<nu> x)\<^sup>\<omega> + (\<nu> x)\<^sup>\<star> \<cdot> \<tau> x \<le> x\<^sup>\<omega>"
proof -
  have "(\<nu> x)\<^sup>\<omega> + (\<nu> x)\<^sup>\<star> \<cdot> \<tau> x = (\<nu> x)\<^sup>\<omega> + (1\<^sub>\<sigma> + \<nu> x \<cdot> (\<nu> x)\<^sup>\<star>) \<cdot> \<tau> x"
    by auto
  also have "... =  (\<nu> x)\<^sup>\<omega> + \<tau> x + \<nu> x \<cdot> (\<nu> x)\<^sup>\<star> \<cdot> \<tau> x"
    using add_assoc local.s_prod_distr local.s_prod_idl by presburger
  also have "... = \<tau> x + \<nu> x \<cdot> (\<nu> x)\<^sup>\<omega> + \<nu> x \<cdot> (\<nu> x)\<^sup>\<star> \<cdot> \<tau> x"
    by (simp add: add_ac)
  also have "... \<le> \<tau> x + \<nu> x \<cdot> ((\<nu> x)\<^sup>\<omega> + (\<nu> x)\<^sup>\<star> \<cdot> \<tau> x)"
    by (metis add_assoc local.cl5 local.lat_dist1 local.inf.absorb_iff1 local.s_prod_subdistl local.tau_def)
  also have "... = x \<cdot> ((\<nu> x)\<^sup>\<omega> + (\<nu> x)\<^sup>\<star> \<cdot> \<tau> x)"
    by (metis local.sprod_tau_nu)
  finally show ?thesis
    using local.om_coinduct by blast
qed

end

subsection \<open>C-Nabla Algebras\<close>

text \<open>Nabla-algebras provide yet another way of formalising non-terminating behaviour in Section 13.\<close>

class c_nabla_algebra = c_omega_algebra + 
  fixes nabla :: "'a \<Rightarrow> 'a" ("\<nabla>")
  assumes nabla_unfold: "\<nabla>  x \<le> d (x \<cdot> \<nabla> x)"
  and nabla_coinduct: "d y \<le> d (x \<cdot> y) \<Longrightarrow> d y \<le> \<nabla> x"

begin

lemma nabla_unfold_eq [simp]: "\<nabla> x = d (x \<cdot> \<nabla> x)"
proof (rule antisym)
  show "\<nabla> x \<le> d (x \<cdot> \<nabla> x)"
    using local.nabla_unfold by blast
  have "d (x \<cdot> \<nabla> x) \<le> d (x \<cdot> d (x \<cdot> \<nabla> x))"
    by (metis local.d_def local.mult_commute local.mult_isol local.nabla_unfold local.s_prod_isol local.s_prod_isor)
  also have "... = d (x \<cdot> (x \<cdot> \<nabla> x))"
    using local.d_loc_ax by blast
  finally show "d (x \<cdot> \<nabla> x) \<le> \<nabla> x"
    by (simp add: local.nabla_coinduct)  
qed

lemma nabla_le_s: "\<nabla> x \<le> 1\<^sub>\<sigma>"
  by (metis local.d_sub_id_ax nabla_unfold_eq)

lemma nabla_nu [simp]: "\<nu> (\<nabla> x) = \<nabla> x"
  using local.nu_ideal1 local.nu_s nabla_le_s by blast

 
text \<open>Proposition 13.9.\<close>

lemma nabla_omega_U: 
assumes "\<And>x y z. x \<cdot> (d y \<cdot> z) = (x \<cdot> d y ) \<cdot> z"
shows "(\<nu> x)\<^sup>\<omega> = \<nabla> (\<nu> x) \<cdot> U"
proof (rule antisym)
  have "d ((\<nu> x)\<^sup>\<omega>) \<le> \<nabla> (\<nu> x)"
    using local.nabla_coinduct local.om_unfold_eq local.order_refl by presburger
  hence "(\<nu> x)\<^sup>\<omega> \<le> \<nabla> (\<nu> x) \<cdot> (\<nu> x)\<^sup>\<omega>"
    using local.dlp_ax local.dual_order.trans local.s_prod_isor by blast
  thus "(\<nu> x)\<^sup>\<omega>  \<le> \<nabla> (\<nu> x) \<cdot> U"
    using local.U_def local.dual_order.trans local.s_prod_isol by blast
  have "\<nu> x \<cdot> (\<nabla> (\<nu> x) \<cdot> U) = (\<nu> x \<cdot> d (\<nabla> (\<nu> x))) \<cdot> U"
    by (metis assms local.d_s_subid nabla_le_s)
  also have "... = (\<nu> (\<nu> x \<cdot> \<nu> (\<nabla> (\<nu> x)))) \<cdot> U"
    by (metis local.d_s_subid nabla_le_s nabla_nu local.alpha_prod_closed)
  also have "... = d (\<nu> (\<nu> x \<cdot> \<nu> (\<nabla> (\<nu> x)))) \<cdot> U"
    using local.ax5_d local.nu_def by presburger 
  also have "... = d (\<nu> x \<cdot> \<nabla> (\<nu> x)) \<cdot> U"
    by (metis local.alpha_prod_closed nabla_nu) 
  finally show "\<nabla> (\<nu> x) \<cdot> U \<le> (\<nu> x)\<^sup>\<omega>"
    using local.nabla_unfold local.om_coinduct local.s_prod_isor by presburger
qed

text \<open>Corollary 13.10.\<close>

lemma nabla_omega_U_cor: 
assumes  "\<And>x y z. x \<cdot> (d y \<cdot> z) = (x \<cdot> d y ) \<cdot> z"
shows "\<nabla> (\<nu> x) \<cdot> U + (\<nu> x)\<^sup>\<star> \<cdot> \<tau> x \<le> x\<^sup>\<omega>"
  by (metis assms nabla_omega_U local.om_nu_tau)

text \<open>Lemma 13.11.\<close>

lemma nu_om_nu: 
assumes  "\<And>x y z. x \<cdot> (d y \<cdot> z) = (x \<cdot> d y ) \<cdot> z"
shows "\<nu> ((\<nu> x)\<^sup>\<omega>) = \<nabla> (\<nu> x) \<cdot> nc"
proof -
  have "\<nu> ((\<nu> x)\<^sup>\<omega>) = \<nu> (\<nabla> (\<nu> x) \<cdot> U)"
    using assms nabla_omega_U by presburger
  also have "... = \<nu> (d (\<nabla> (\<nu> x)) \<cdot> U)"
    by (metis local.d_s_subid nabla_le_s)
  also have "... = (\<nabla> (\<nu> x)) \<cdot> \<nu> U"
    by (metis local.d_nu local.d_s_subid nabla_le_s)
  finally show ?thesis
    using local.nu_U by presburger
qed

lemma tau_om_nu: 
assumes  "\<And>x y z. x \<cdot> (d y \<cdot> z) = (x \<cdot> d y ) \<cdot> z"
shows "\<tau> ((\<nu> x)\<^sup>\<omega>) = \<nabla> (\<nu> x) \<cdot> 1\<^sub>\<pi>"
proof -
  have "\<tau> ((\<nu> x)\<^sup>\<omega>) = \<tau> (\<nabla> (\<nu> x) \<cdot> U)"
    by (metis assms nabla_omega_U)
  also have "... = \<nabla> (\<nu> x) \<cdot> \<tau> U"
    using local.tau_s_prod by blast
  finally show ?thesis
    using local.tau_U by blast
qed

text \<open>Proposition 13.12.\<close>

lemma wf_eq_defl: "(\<forall>y. d y \<le> d (x \<cdot> y) \<longrightarrow> d y = 0) \<longleftrightarrow> (\<forall>y. y \<le> x \<cdot> y \<longrightarrow> y = 0)"
  apply standard
  apply (metis local.d_add_ax local.d_rest_ax local.less_eq_def local.s_prod_annil)
  by (metis local.c2_d local.c4 local.d_def local.mult_commute local.mult_onel local.p_rpd_annir local.s_prod_isor)

lemma defl_eq_om_trivial: "x\<^sup>\<omega> = 0 \<longleftrightarrow> (\<forall>y. y \<le> x \<cdot> y \<longrightarrow> y = 0)"
  using local.join.bot_unique local.om_coinduct by auto

lemma wf_eq_om_trivial: "x\<^sup>\<omega> = 0  \<longleftrightarrow> (\<forall>y. d y \<le> d (x \<cdot> y) \<longrightarrow> d y = 0)"
  by (simp add: defl_eq_om_trivial wf_eq_defl)

end

subsection \<open>Proto-Quantales\<close>

text \<open>Finally we define the class of proto-quantales and prove some of the 
remaining facts from the article. Full c-quantales, as defined there, are not needed
for these proofs.\<close>

class proto_quantale = complete_lattice + proto_monoid +
  assumes Sup_mult_distr: "Sup X \<cdot> y = Sup {x \<cdot> y | x. x \<in> X}"
  and isol: "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"

begin

sublocale pd?: proto_dioid "1\<^sub>\<sigma>" "(\<cdot>)" sup "(\<le>)" "(<)" "Sup {}"
proof
  show "\<And>x y. (x \<le> y) = (sup x y = y)"
    by (simp add: local.le_iff_sup)
  show "\<And>x y. (x < y) = (x \<le> y \<and> x \<noteq> y)"
    by (simp add: local.order.strict_iff_order)
  show "\<And>x y z. sup (sup x y) z = sup x (sup y z)"
    by (simp add: local.sup_assoc)
  show "\<And>x y. sup x y = sup y x"
    by (simp add: local.sup_commute)
  show "\<And>x. sup x x = x"
    by (simp add: insert_commute)
  show "\<And>x. sup (Sup {}) x = x"
    by simp
  show "\<And>x y z. sup (x \<cdot> y) (x \<cdot> z) \<le> x \<cdot> (sup y z)"
    by (simp add: local.isol)
  show " \<And>x. Sup {} \<cdot> x = Sup {}"
proof -
  fix x :: 'a
  have "\<forall>A a. {} \<noteq> A \<or> {} = {aa. \<exists>ab. (aa::'a) = ab \<cdot> a \<and> ab \<in> A}"
    by fastforce
  thus "Sup {} \<cdot> x = Sup {}"
    using local.Sup_mult_distr by presburger
qed
  show "\<And>x y z. (sup x y) \<cdot> z = sup (x \<cdot> z) (y \<cdot> z)"
  proof -
    fix x y z
    have "(sup x y) \<cdot> z = Sup {x,y} \<cdot> z"
      by simp
    moreover have "... = sup (x \<cdot> z) (y \<cdot> z)"
      by (subst Sup_mult_distr, rule Sup_eqI, auto)
    thus "(sup x y) \<cdot> z = sup (x \<cdot> z) (y \<cdot> z)"
      using calculation by presburger
  qed
qed

definition star_rd :: "'a \<Rightarrow> 'a" where
  "star_rd x = Sup {power_rd x i |i. i \<in> \<nat>}"

definition star_sq :: "'a \<Rightarrow> 'a" where
  "star_sq x = Sup {power_sq x i |i. i \<in> \<nat>}"

text \<open>Now we prove Lemma 12.6.\<close>

lemma star_rd_le_sq: "star_rd x \<le> star_sq x"
  apply (auto simp: star_rd_def star_sq_def)
  apply (rule Sup_mono)
  using pd.power_rd_le_sq by auto

lemma star_sq_le_rd: "star_sq x \<le> star_rd x"
  apply (auto simp: star_rd_def star_sq_def)
  apply (rule Sup_mono)
  apply auto
  by (metis Nats_1 Nats_add Suc_eq_plus1 local.Sup_empty pd.power_sq_le_rd)

lemma star_rd_sq: "star_rd x = star_sq x"
  by (simp add: local.dual_order.antisym star_rd_le_sq star_sq_le_rd)

lemma star_sq_power: "star_sq x = Sup {pd.p_power (sup 1\<^sub>\<sigma> x) i | i. i \<in> \<nat>}"
  by (auto simp: star_sq_def pd.power_sq_power [symmetric] intro: Sup_eqI)

text \<open>The following lemma should be somewhere close to complete lattices.\<close>

end

lemma mono_aux: "mono (\<lambda>y. sup (z:: 'a :: proto_quantale) (x \<cdot> y))"
  by (meson mono_def order_refl pd.s_prod_isol sup.mono)

lemma gfp_lfp_prop: "sup (gfp (\<lambda>(y :: 'a :: proto_quantale). x \<cdot> y)) (lfp (\<lambda>y. sup z (x \<cdot> y))) \<le> gfp (\<lambda>y. sup z  (x \<cdot> y))"
  apply (simp, rule conjI)
  apply (simp add: gfp_mono)
  by (simp add: lfp_le_gfp mono_aux)

end
