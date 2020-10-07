section \<open>Galois Connections and Fusion Theorems \label{S:galois}\<close>

theory Galois_Connections
imports Refinement_Lattice
begin

text \<open>
  The concept of Galois connections is introduced here to prove the fixed-point fusion lemmas. 
  The definition of Galois connections used is quite simple but encodes a lot of 
  information.
  The material in this section is largely based on the work of the Eindhoven
  Mathematics of Program Construction Group \cite{fixedpointcalculus1995}
  and the reader is referred to their work for a full explanation of this section.
\<close>

subsection \<open>Lower Galois connections\<close>

(* auxiliary lemma to prefer 2-element sets rather than disjunction *)
lemma Collect_2set [simp]:  "{F x |x. x = a \<or> x = b} = {F a, F b}"
  by auto

locale lower_galois_connections  
begin

definition
  l_adjoint :: "('a::refinement_lattice \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" ("_\<^sup>\<flat>" [201] 200)
where
  "(F\<^sup>\<flat>) x \<equiv> \<Sqinter>{y. x \<sqsubseteq> F y}"

lemma dist_inf_mono:
  assumes distF: "dist_over_inf F"
  shows "mono F"
proof
  fix x :: 'a and y :: 'a
  assume "x \<sqsubseteq> y"
  then have "F x = F (x \<sqinter> y)" by (simp add: le_iff_inf)
  also have "... = F x \<sqinter> F y"
  proof -
    from distF
    have "F (\<Sqinter>{x, y}) = \<Sqinter>{F x, F y}" by (drule_tac x = "{x, y}" in spec, simp)
    then show "F (x \<sqinter> y) = F x \<sqinter> F y" by simp
  qed
  finally show "F x \<sqsubseteq> F y" by (metis le_iff_inf)
qed

lemma l_cancellation: "dist_over_inf F \<Longrightarrow> x \<sqsubseteq> (F \<circ> F\<^sup>\<flat>) x"
proof -
  assume dist: "dist_over_inf F"

  define Y where "Y = {F y | y. x \<sqsubseteq> F y}"
  define X where "X = {x}"

  have "(\<forall> y \<in> Y. (\<exists> x \<in> X. x \<sqsubseteq> y))" using X_def Y_def CollectD singletonI by auto
  then have "\<Sqinter> X \<sqsubseteq> \<Sqinter> Y" by (simp add: Inf_mono) 
  then have "x \<sqsubseteq> \<Sqinter>{F y | y. x \<sqsubseteq> F y}" by (simp add: X_def Y_def) 
  then have "x \<sqsubseteq> F (\<Sqinter>{y. x \<sqsubseteq> F y})" by (simp add: dist le_INF_iff)
  thus ?thesis by (metis comp_def l_adjoint_def) 
qed

lemma l_galois_connection: "dist_over_inf F \<Longrightarrow> ((F\<^sup>\<flat>) x \<sqsubseteq> y) \<longleftrightarrow> (x \<sqsubseteq> F y)"
proof
  assume "x \<sqsubseteq> F y"
  then have "\<Sqinter>{y. x \<sqsubseteq> F y} \<sqsubseteq> y" by (simp add: Inf_lower) 
  thus "(F\<^sup>\<flat>) x \<sqsubseteq> y" by (metis l_adjoint_def) 
next
  assume dist: "dist_over_inf F" then have monoF: "mono F" by (simp add: dist_inf_mono)
  assume "(F\<^sup>\<flat>) x \<sqsubseteq> y" then have a: "F ((F\<^sup>\<flat>) x) \<sqsubseteq> F y" by (simp add: monoD monoF)
  have "x \<sqsubseteq> F ((F\<^sup>\<flat>) x)" using dist l_cancellation by simp
  thus "x \<sqsubseteq> F y" using a by auto
qed

lemma v_simple_fusion: "mono G \<Longrightarrow> \<forall>x. ((F \<circ> G) x \<sqsubseteq> (H \<circ> F) x) \<Longrightarrow> F (gfp G) \<sqsubseteq> gfp H"
  by (metis comp_eq_dest_lhs gfp_unfold gfp_upperbound)


subsection \<open>Greatest fixpoint fusion theorems\<close>

text \<open>
  Combining lower Galois connections and greatest fixed points allows 
  elegant proofs of the weak fusion lemmas. 
\<close>

theorem fusion_gfp_geq:
  assumes monoH: "mono H"
  and distribF: "dist_over_inf F"
  and comp_geq: "\<And>x. ((H \<circ> F) x \<sqsubseteq> (F \<circ> G) x)"
  shows "gfp H \<sqsubseteq> F (gfp G)"
proof -
  have "(gfp H) \<sqsubseteq> (F \<circ> F\<^sup>\<flat>) (gfp H)" using distribF l_cancellation by simp
  then have "H (gfp H) \<sqsubseteq> H ((F \<circ> F\<^sup>\<flat>) (gfp H))" by (simp add: monoD monoH) 
  then have "H (gfp H) \<sqsubseteq> F ((G \<circ> F\<^sup>\<flat>) (gfp H))" using comp_geq by (metis comp_def refine_trans) 
  then have "(F\<^sup>\<flat>) (H (gfp H)) \<sqsubseteq> (G \<circ> F\<^sup>\<flat>) (gfp H)" using distribF by (metis (mono_tags) l_galois_connection) 
  then have "(F\<^sup>\<flat>) (gfp H) \<sqsubseteq> (gfp G)" by (metis comp_apply gfp_unfold gfp_upperbound monoH) 
  thus "gfp H \<sqsubseteq> F (gfp G)" using distribF by (metis (mono_tags) l_galois_connection) 
qed

theorem fusion_gfp_eq: 
  assumes monoH: "mono H" and monoG: "mono G"
  and distF: "dist_over_inf F"
  and fgh_comp: "\<And>x. ((F \<circ> G) x = (H \<circ> F) x)"
  shows "F (gfp G) = gfp H"
proof (rule antisym)
  show "F (gfp G) \<sqsubseteq> (gfp H)" by (metis fgh_comp le_less v_simple_fusion monoG)
next
  have "\<And>x. ((H \<circ> F) x \<sqsubseteq> (F \<circ> G) x)" using fgh_comp by auto
  then show "gfp H \<sqsubseteq> F (gfp G)" using monoH distF fusion_gfp_geq by blast
qed

end

subsection \<open>Upper Galois connections\<close>

locale upper_galois_connections
begin

definition
  u_adjoint :: "('a::refinement_lattice \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" ("_\<^sup>#" [201] 200)
where
  "(F\<^sup>#) x \<equiv> \<Squnion>{y. F y \<sqsubseteq> x}"


lemma dist_sup_mono:
  assumes distF: "dist_over_sup F"
  shows "mono F"
proof
  fix x :: 'a and y :: 'a
  assume "x \<sqsubseteq> y"
  then have "F y = F (x \<squnion> y)" by (simp add: le_iff_sup)
  also have "... = F x \<squnion> F y"
  proof -
    from distF
    have "F (\<Squnion>{x, y}) = \<Squnion>{F x, F y}" by (drule_tac x = "{x, y}" in spec, simp)
    then show "F (x \<squnion> y) = F x \<squnion> F y" by simp
  qed
  finally show "F x \<sqsubseteq> F y" by (metis le_iff_sup)
qed

lemma u_cancellation: "dist_over_sup F \<Longrightarrow> (F \<circ> F\<^sup>#) x \<sqsubseteq> x"
proof -
  assume dist: "dist_over_sup F"
  define Y where "Y = {F y | y. F y \<sqsubseteq> x}"
  define X where "X = {x}"

  have "(\<forall> y \<in> Y. (\<exists> x \<in> X. y \<sqsubseteq> x))" using X_def Y_def CollectD singletonI by auto
  then have "\<Squnion> Y \<sqsubseteq> \<Squnion> X" by (simp add: Sup_mono)
  then have "\<Squnion>{F y | y. F y \<sqsubseteq> x} \<sqsubseteq> x" by (simp add: X_def Y_def) 
  then have "F (\<Squnion>{y. F y \<sqsubseteq> x}) \<sqsubseteq> x" using SUP_le_iff dist by fastforce
  thus ?thesis by (metis comp_def u_adjoint_def)
qed

lemma u_galois_connection: "dist_over_sup F \<Longrightarrow> (F x \<sqsubseteq> y) \<longleftrightarrow> (x \<sqsubseteq> (F\<^sup>#) y)"
proof
  assume dist: "dist_over_sup F" then have monoF: "mono F" by (simp add: dist_sup_mono)
  assume "x \<sqsubseteq> (F\<^sup>#) y" then have a: "F x \<sqsubseteq> F ((F\<^sup>#) y)" by (simp add: monoD monoF)
  have "F ((F\<^sup>#) y) \<sqsubseteq> y" using dist u_cancellation by simp
  thus "F x \<sqsubseteq> y" using a by auto
next
  assume "F x \<sqsubseteq> y"
  then have "x \<sqsubseteq> \<Squnion>{x. F x \<sqsubseteq> y}" by (simp add: Sup_upper)
  thus "x \<sqsubseteq> (F\<^sup>#) y" by (metis u_adjoint_def)
qed

lemma u_simple_fusion: "mono H \<Longrightarrow> \<forall>x. ((F \<circ> G) x \<sqsubseteq> (G \<circ> H) x) \<Longrightarrow> lfp F \<sqsubseteq> G (lfp H)"
  by (metis comp_def lfp_lowerbound lfp_unfold)

subsection \<open>Least fixpoint fusion theorems\<close>

text \<open>
  Combining upper Galois connections and least fixed points allows elegant proofs 
  of the strong fusion lemmas.
\<close>


theorem fusion_lfp_leq:
  assumes monoH: "mono H"
  and distribF: "dist_over_sup F"
  and comp_leq: "\<And>x. ((F \<circ> G) x \<sqsubseteq> (H \<circ> F) x)" 
  shows "F (lfp G) \<sqsubseteq> (lfp H)"
proof -
  have "((F \<circ> F\<^sup>#) (lfp H)) \<sqsubseteq> lfp H"  using distribF u_cancellation by simp
  then have "H ((F \<circ> F\<^sup>#) (lfp H)) \<sqsubseteq> H (lfp H)" by (simp add: monoD monoH)
  then have "F ((G \<circ> F\<^sup>#) (lfp H)) \<sqsubseteq> H (lfp H)" using comp_leq by (metis comp_def refine_trans) 
  then have "(G \<circ> F\<^sup>#) (lfp H) \<sqsubseteq> (F\<^sup>#) (H (lfp H))" using distribF by (metis (mono_tags) u_galois_connection)
  then have "(lfp G) \<sqsubseteq> (F\<^sup>#) (lfp H)" by (metis comp_def def_lfp_unfold lfp_lowerbound monoH)
  thus "F (lfp G) \<sqsubseteq> (lfp H)" using distribF by (metis (mono_tags) u_galois_connection)
qed


theorem fusion_lfp_eq: 
  assumes monoH: "mono H" and monoG: "mono G"
  and distF: "dist_over_sup F"
  and fgh_comp: "\<And>x. ((F \<circ> G) x = (H \<circ> F) x)" 
  shows "F (lfp G) = (lfp H)"
proof (rule antisym)
  show "lfp H \<sqsubseteq> F (lfp G)" by (metis monoG fgh_comp eq_iff upper_galois_connections.u_simple_fusion)
next
  have "\<And>x. (F \<circ> G) x \<sqsubseteq> (H \<circ> F) x" using fgh_comp by auto
  then show "F (lfp G) \<sqsubseteq> (lfp H)" using monoH distF fusion_lfp_leq by blast
qed


end
end

