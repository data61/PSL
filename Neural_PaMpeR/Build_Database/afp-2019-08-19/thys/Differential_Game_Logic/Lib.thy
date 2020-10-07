theory "Lib"
imports
  Complex_Main
begin 
section \<open>Generic Mathematical Background Lemmas\<close>

lemma finite_subset [simp]: "finite M \<Longrightarrow> finite {x\<in>M. P x}"
  by simp

lemma finite_powerset [simp]: "finite M \<Longrightarrow> finite {S. S\<subseteq>M}"
  by simp

definition fst_proj:: "('a*'b) set \<Rightarrow> 'a set"
  where "fst_proj M \<equiv> {A. \<exists>B. (A,B)\<in>M}"

definition snd_proj:: "('a*'b) set \<Rightarrow> 'b set"
  where "snd_proj M \<equiv> {B. \<exists>A. (A,B)\<in>M}"

lemma fst_proj_mem [simp]: "(A \<in> fst_proj M) = (\<exists>B. (A,B)\<in>M)"
  unfolding fst_proj_def by auto
  
lemma snd_proj_mem [simp]: "(B \<in> snd_proj M) = (\<exists>A. (A,B)\<in>M)"
  unfolding snd_proj_def by auto

lemma fst_proj_prop: "\<forall>x\<in>fst_proj {(A,B)| A B. P A \<and> R A B}. P(x)"
  unfolding fst_proj_def by auto

lemma snd_proj_prop: "\<forall>x\<in>snd_proj {(A,B) | A B. P B \<and> R A B}. P(x)"
  unfolding snd_proj_def by auto

lemma map_cons: "map f (Cons x xs) = Cons (f x) (map f xs)"
  by (rule List.list.map)
lemma map_append: "map f (append xs ys) = append (map f xs) (map f ys)"
  by simp
  


text\<open>Lockstep induction schema for two simultaneous least fixpoints.
  If the successor step and supremum step of two least fixpoint inflations
  preserve a relation, then that relation holds of the two respective least fixpoints.\<close>

lemma lfp_lockstep_induct [case_names monof monog step union]:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
    and g :: "'b::complete_lattice \<Rightarrow> 'b"
  assumes monof: "mono f" 
    and monog: "mono g"
    and R_step: "\<And>A B. A \<le> lfp(f) \<Longrightarrow> B \<le> lfp(g) \<Longrightarrow> R A B \<Longrightarrow> R (f(A)) (g(B))"
    and R_Union: "\<And>M::('a*'b) set. (\<forall>(A,B)\<in>M. R A B) \<Longrightarrow> R (Sup (fst_proj M)) (Sup (snd_proj M))"
  shows "R (lfp f) (lfp g)"
proof-
  (*using idea of proof of "Inductive.thy:lfp_ordinal_induct"*)
  let ?M = "{(A,B). A \<le> lfp f \<and> B \<le> lfp g \<and> R A B}"
  from R_Union have supdoes: "R (Sup (fst_proj ?M)) (Sup (snd_proj ?M))" by simp
  also have "Sup (fst_proj ?M) = lfp f" and "Sup (snd_proj ?M) = lfp g"
  proof (rule antisym)
    show fle: "Sup (fst_proj ?M) \<le> lfp f"
      using fst_proj_prop Sup_le_iff by fastforce
    then have "f (Sup (fst_proj ?M)) \<le> f (lfp f)"
      by (rule monof [THEN monoD])
    then have fsup: "f (Sup (fst_proj ?M)) \<le> lfp f"
      using monof [THEN lfp_unfold] by simp

    have gle: "Sup (snd_proj ?M) \<le> lfp g"
      using snd_proj_prop Sup_le_iff by fastforce
    then have "g (Sup (snd_proj ?M)) \<le> g (lfp g)"
      by (rule monog [THEN monoD])
    then have gsup: "g (Sup (snd_proj ?M)) \<le> lfp g"
      using monog [THEN lfp_unfold] by simp

    from fsup and gsup have fgsup: "(f(Sup(fst_proj ?M)), g(Sup(snd_proj ?M))) \<in> ?M"
      using R_Union R_step Sup_le_iff
      using calculation fle gle by blast 

    from fgsup have "f (Sup (fst_proj ?M)) \<le> Sup (fst_proj ?M)"
      using Sup_upper by (metis (mono_tags, lifting) fst_proj_def mem_Collect_eq) 
    then show fge: "lfp f \<le> Sup (fst_proj ?M)"
      by (rule lfp_lowerbound)
    show "Sup (snd_proj ?M) = lfp g"
    proof (rule antisym)
      show "Sup (snd_proj ?M) \<le> lfp g" by (rule gle)
      from fgsup have "g (Sup (snd_proj ?M)) \<le> Sup (snd_proj ?M)"
        using Sup_upper by (metis (mono_tags, lifting) snd_proj_def mem_Collect_eq)
      then show gge: "lfp g \<le> Sup (snd_proj ?M)"
        by (rule lfp_lowerbound)
    qed
  qed
  then show ?thesis using supdoes by simp
qed


lemma sup_eq_all: "(\<And>A. (A\<in>M \<Longrightarrow> f(A)=g(A)))
  \<Longrightarrow> Sup {f(A) | A. A\<in>M} = Sup {g(A) | A. A\<in>M}"
  by metis

lemma sup_corr_eq_chain: "\<And>M::('a::complete_lattice*'a) set. (\<forall>(A,B)\<in>M. f(A)=g(B)) \<Longrightarrow> (Sup {f(A) | A. A\<in>fst_proj M} = Sup {g(B) | B. B\<in>snd_proj M})"
  by (metis (mono_tags, lifting) case_prod_conv fst_proj_mem snd_proj_mem)

end