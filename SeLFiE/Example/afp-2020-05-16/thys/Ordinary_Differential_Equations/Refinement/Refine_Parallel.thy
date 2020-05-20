theory
  Refine_Parallel
  imports
    "HOL-Library.Parallel"
    Ordinary_Differential_Equations.ODE_Auxiliarities
    "../Refinement/Autoref_Misc"
    "../Refinement/Weak_Set"
begin

context includes autoref_syntax begin

lemma dres_of_dress_impl:
  "nres_of (rec_list (dRETURN []) (\<lambda>x xs r. do { fx \<leftarrow> x; r \<leftarrow> r; dRETURN (fx # r)}) (Parallel.map f x)) \<le>
    nres_of_nress_impl (Parallel.map f' x)"
  if [refine_transfer]: "\<And>x. nres_of (f x) \<le> f' x"
  unfolding Parallel.map_def nres_of_nress_impl_map
  apply (induction x)
   apply (auto simp: )
  apply refine_transfer
  done
concrete_definition dres_of_dress_impl uses dres_of_dress_impl
lemmas [refine_transfer] = dres_of_dress_impl.refine

definition PAR_IMAGE::"('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c nres) \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'c) set nres" where
  "PAR_IMAGE P f X = do {
    xs \<leftarrow> list_spec X;
    fxs \<leftarrow>nres_of_nress (\<lambda>(x, y). P x y) (Parallel.map (\<lambda>x. do { y \<leftarrow> f x; RETURN (x, y)}) xs);
    RETURN (set fxs)
  }"

lemma [autoref_op_pat_def]: "PAR_IMAGE P \<equiv> OP (PAR_IMAGE P)" by auto
lemma [autoref_rules]: "(Parallel.map, Parallel.map) \<in> (A \<rightarrow> B) \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>B\<rangle>list_rel"
  unfolding Parallel.map_def
  by parametricity
schematic_goal PAR_IMAGE_nres:
  "(?r, PAR_IMAGE P $ f $ X) \<in> \<langle>\<langle>A\<times>\<^sub>rB\<rangle>list_wset_rel\<rangle>nres_rel"
  if [autoref_rules]: "(fi, f) \<in> A \<rightarrow> \<langle>B\<rangle>nres_rel" "(Xi, X) \<in> \<langle>A\<rangle>list_wset_rel"
  and [THEN PREFER_sv_D, relator_props]:
  "PREFER single_valued A"  "PREFER single_valued B"
  unfolding PAR_IMAGE_def
  including art
  by autoref
concrete_definition PAR_IMAGE_nres uses PAR_IMAGE_nres
lemma PAR_IMAGE_nres_impl_refine[autoref_rules]:
  "PREFER single_valued A \<Longrightarrow>
  PREFER single_valued B \<Longrightarrow>
  (\<lambda>fi Xi. PAR_IMAGE_nres fi Xi, PAR_IMAGE P)
    \<in> (A \<rightarrow> \<langle>B\<rangle>nres_rel) \<rightarrow> \<langle>A\<rangle>list_wset_rel \<rightarrow> \<langle>\<langle>A\<times>\<^sub>rB\<rangle>list_wset_rel\<rangle>nres_rel"
  using PAR_IMAGE_nres.refine by force
schematic_goal PAR_IMAGE_dres:
  assumes [refine_transfer]: "\<And>x. nres_of (f x) \<le> f' x"
  shows "nres_of (?f) \<le> PAR_IMAGE_nres f' X'"
  unfolding PAR_IMAGE_nres_def
  by refine_transfer
concrete_definition PAR_IMAGE_dres for f X' uses PAR_IMAGE_dres
lemmas [refine_transfer] = PAR_IMAGE_dres.refine

lemma nres_of_nress_Parallel_map_SPEC[le, refine_vcg]:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> SPEC (I x)"
  shows
    "nres_of_nress (\<lambda>(x, y). I x y) (Parallel.map (\<lambda>x. f x \<bind> (\<lambda>y. RETURN (x, y))) xs) \<le>
      SPEC (\<lambda>xrs. map fst xrs = xs \<and> (\<forall>(x, r) \<in> set xrs. I x r))"
  using assms
  apply (induction xs)
  subgoal by (simp add: )
  apply clarsimp
  apply (rule refine_vcg)
  subgoal for x xs
    apply (rule order_trans[of _ "SPEC (I x)"]) apply force
    apply (rule refine_vcg)
    apply (rule refine_vcg)
    apply (rule order_trans, assumption)
    apply refine_vcg
    done
  done

lemma PAR_IMAGE_SPEC[le, refine_vcg]:
  "PAR_IMAGE I f X \<le> SPEC (\<lambda>R. X = fst ` R \<and> (\<forall>(x,r) \<in> R. I x r))"
  if [le, refine_vcg]: "\<And>x. x \<in> X \<Longrightarrow> f x \<le> SPEC (I x)"
  unfolding PAR_IMAGE_def
  by refine_vcg

end

end