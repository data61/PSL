(*  Title:       Lifting to Non-Ground Calculi of the Saturation Framework
 *  Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018-2020 *)

section \<open>Lifting to Non-ground Calculi\<close>

text \<open>The section 3.1 to 3.3 of the report are covered by the current section.
  Various forms of lifting are proven correct. These allow to obtain the dynamic
  refutational completeness of a non-ground calculus from the static refutational
  completeness of its ground counterpart.\<close>

theory Lifting_to_Non_Ground_Calculi
  imports
    Calculi
    Well_Quasi_Orders.Minimal_Elements
begin

subsection \<open>Standard Lifting\<close>

locale standard_lifting = Non_ground: inference_system Inf_F +
  Ground: calculus_with_red_crit Bot_G Inf_G entails_G Red_Inf_G Red_F_G
  for
    Bot_F :: \<open>'f set\<close> and
    Inf_F :: \<open>'f inference set\<close> and
    Bot_G :: \<open>'g set\<close> and
    Inf_G ::  \<open>'g inference set\<close> and
    entails_G ::  \<open>'g set  \<Rightarrow> 'g set  \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Red_Inf_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close>
  + fixes
    \<G>_F :: \<open>'f \<Rightarrow> 'g set\<close> and
    \<G>_Inf :: \<open>'f inference \<Rightarrow> 'g inference set option\<close>
  assumes
    Bot_F_not_empty: "Bot_F \<noteq> {}" and
    Bot_map_not_empty: \<open>B \<in> Bot_F \<Longrightarrow> \<G>_F B \<noteq> {}\<close> and
    Bot_map: \<open>B \<in> Bot_F \<Longrightarrow> \<G>_F B \<subseteq> Bot_G\<close> and
    Bot_cond: \<open>\<G>_F C \<inter> Bot_G \<noteq> {} \<longrightarrow> C \<in> Bot_F\<close> and
    inf_map: \<open>\<iota> \<in> Inf_F \<Longrightarrow> \<G>_Inf \<iota> \<noteq> None \<Longrightarrow> the (\<G>_Inf \<iota>) \<subseteq> Red_Inf_G (\<G>_F (concl_of \<iota>))\<close>
begin

abbreviation \<G>_set :: \<open>'f set \<Rightarrow> 'g set\<close> where
  \<open>\<G>_set N \<equiv> \<Union> (\<G>_F ` N)\<close>

lemma \<G>_subset: \<open>N1 \<subseteq> N2 \<Longrightarrow> \<G>_set N1 \<subseteq> \<G>_set N2\<close> by auto

definition entails_\<G>  :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix "\<Turnstile>\<G>" 50) where
  \<open>N1 \<Turnstile>\<G> N2 \<equiv> \<G>_set N1 \<Turnstile>G \<G>_set N2\<close>

lemma subs_Bot_G_entails:
  assumes
    not_empty: \<open>sB \<noteq> {}\<close> and
    in_bot: \<open>sB \<subseteq> Bot_G\<close>
  shows \<open>sB \<Turnstile>G N\<close>
proof -
  have \<open>\<exists>B. B \<in> sB\<close> using not_empty by auto
  then obtain B where B_in: \<open>B \<in> sB\<close> by auto
  then have r_trans: \<open>{B} \<Turnstile>G N\<close> using Ground.bot_implies_all in_bot by auto
  have l_trans: \<open>sB \<Turnstile>G {B}\<close> using B_in Ground.subset_entailed by auto
  then show ?thesis using r_trans Ground.entails_trans[of sB "{B}"] by auto
qed

(* lem:derived-consequence-relation *)
sublocale lifted_consequence_relation: consequence_relation
  where Bot=Bot_F and entails=entails_\<G>
proof
  show "Bot_F \<noteq> {}" using Bot_F_not_empty .
next
  show \<open>B\<in>Bot_F \<Longrightarrow> {B} \<Turnstile>\<G> N\<close> for B N
  proof -
    assume \<open>B \<in> Bot_F\<close>
    then show \<open>{B} \<Turnstile>\<G> N\<close>
      using Bot_map Ground.bot_implies_all[of _ "\<G>_set N"] subs_Bot_G_entails Bot_map_not_empty
      unfolding entails_\<G>_def
      by auto
  qed
next
  fix N1 N2 :: \<open>'f set\<close>
  assume
    \<open>N2 \<subseteq> N1\<close>
  then show \<open>N1 \<Turnstile>\<G> N2\<close> using entails_\<G>_def \<G>_subset Ground.subset_entailed by auto
next
  fix N1 N2
  assume
    N1_entails_C: \<open>\<forall>C \<in> N2. N1 \<Turnstile>\<G> {C}\<close>
  show \<open>N1 \<Turnstile>\<G> N2\<close> using Ground.all_formulas_entailed N1_entails_C entails_\<G>_def
    by (smt UN_E UN_I Ground.entail_set_all_formulas singletonI)
next
  fix N1 N2 N3
  assume
    \<open>N1 \<Turnstile>\<G> N2\<close> and \<open>N2 \<Turnstile>\<G> N3\<close>
  then show \<open>N1 \<Turnstile>\<G> N3\<close> using entails_\<G>_def Ground.entails_trans by blast
qed

end

subsection \<open>Strong Standard Lifting\<close>

(* rmk:strong-standard-lifting *)
locale strong_standard_lifting = Non_ground: inference_system Inf_F +
  Ground: calculus_with_red_crit Bot_G Inf_G entails_G Red_Inf_G Red_F_G
  for
    Bot_F :: \<open>'f set\<close> and
    Inf_F :: \<open>'f inference set\<close> and
    Bot_G :: \<open>'g set\<close> and
    Inf_G ::  \<open>'g inference set\<close> and
    entails_G ::  \<open>'g set  \<Rightarrow> 'g set  \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Red_Inf_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close>
  + fixes
    \<G>_F :: \<open>'f \<Rightarrow> 'g set\<close> and
    \<G>_Inf :: \<open>'f inference \<Rightarrow> 'g inference set option\<close>
  assumes
    Bot_F_not_empty: "Bot_F \<noteq> {}" and
    Bot_map_not_empty: \<open>B \<in> Bot_F \<Longrightarrow> \<G>_F B \<noteq> {}\<close> and
    Bot_map: \<open>B \<in> Bot_F \<Longrightarrow> \<G>_F B \<subseteq> Bot_G\<close> and
    Bot_cond: \<open>\<G>_F C \<inter> Bot_G \<noteq> {} \<longrightarrow> C \<in> Bot_F\<close> and
    strong_inf_map: \<open>\<iota> \<in> Inf_F \<Longrightarrow> \<G>_Inf \<iota> \<noteq> None \<Longrightarrow> concl_of ` (the (\<G>_Inf \<iota>)) \<subseteq> (\<G>_F (concl_of \<iota>))\<close> and
    inf_map_in_Inf: \<open>\<iota> \<in> Inf_F \<Longrightarrow> \<G>_Inf \<iota> \<noteq> None \<Longrightarrow> the (\<G>_Inf \<iota>) \<subseteq> Inf_G\<close>
begin

sublocale standard_lifting
proof
  show "Bot_F \<noteq> {}" using Bot_F_not_empty .
next
  fix B
  assume b_in: "B \<in> Bot_F"
  show "\<G>_F B \<noteq> {}" using Bot_map_not_empty[OF b_in] .
next
  fix B
  assume b_in: "B \<in> Bot_F"
  show "\<G>_F B \<subseteq> Bot_G" using Bot_map[OF b_in] .
next
  show "\<And>C. \<G>_F C \<inter> Bot_G \<noteq> {} \<longrightarrow> C \<in> Bot_F" using Bot_cond .
next
  fix \<iota>
  assume i_in: "\<iota> \<in> Inf_F" and
    some_g: "\<G>_Inf \<iota> \<noteq> None"
  show "the (\<G>_Inf \<iota>) \<subseteq> Red_Inf_G (\<G>_F (concl_of \<iota>))"
  proof
    fix \<iota>G
    assume ig_in1: "\<iota>G \<in> the (\<G>_Inf \<iota>)"
    then have ig_in2: "\<iota>G \<in> Inf_G" using inf_map_in_Inf[OF i_in some_g] by blast
    show "\<iota>G \<in> Red_Inf_G (\<G>_F (concl_of \<iota>))"
      using strong_inf_map[OF i_in some_g] Ground.Red_Inf_of_Inf_to_N[OF ig_in2]
        ig_in1 by blast
  qed
qed

end

subsection \<open>Lifting with a Family of Well-founded Orderings\<close>

locale lifting_with_wf_ordering_family =
  standard_lifting Bot_F Inf_F Bot_G Inf_G entails_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf
  for
    Bot_F :: \<open>'f set\<close> and
    Inf_F :: \<open>'f inference set\<close> and
    Bot_G :: \<open>'g set\<close> and
    entails_G :: \<open>'g set \<Rightarrow> 'g set \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Inf_G :: \<open>'g inference set\<close> and
    Red_Inf_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close> and
    \<G>_F :: "'f \<Rightarrow> 'g set" and
    \<G>_Inf :: "'f inference \<Rightarrow> 'g inference set option"
  + fixes
    Prec_F_g :: \<open>'g \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool\<close>
  assumes
    all_wf: "minimal_element (Prec_F_g g) UNIV"
begin

definition Red_Inf_\<G> :: "'f set \<Rightarrow> 'f inference set" where
  \<open>Red_Inf_\<G> N = {\<iota> \<in> Inf_F. (\<G>_Inf \<iota> \<noteq> None \<and> the (\<G>_Inf \<iota>) \<subseteq> Red_Inf_G (\<G>_set N))
    \<or> (\<G>_Inf \<iota> = None \<and> \<G>_F (concl_of \<iota>) \<subseteq> (\<G>_set N \<union> Red_F_G (\<G>_set N)))}\<close>

definition Red_F_\<G> :: "'f set \<Rightarrow> 'f set" where
  \<open>Red_F_\<G> N = {C. \<forall>D \<in> \<G>_F C. D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E \<in> N. Prec_F_g D E C \<and> D \<in> \<G>_F E)}\<close>

lemma Prec_trans:
  assumes
    \<open>Prec_F_g D A B\<close> and
    \<open>Prec_F_g D B C\<close>
  shows
    \<open>Prec_F_g D A C\<close>
  using minimal_element.po assms unfolding po_on_def transp_on_def by (smt UNIV_I all_wf)

lemma prop_nested_in_set: "D \<in> P C \<Longrightarrow> C \<in> {C. \<forall>D \<in> P C. A D \<or> B C D} \<Longrightarrow> A D \<or> B C D"
  by blast

(* lem:wolog-C'-nonredundant *)
lemma Red_F_\<G>_equiv_def:
  \<open>Red_F_\<G> N = {C. \<forall>Di \<in> \<G>_F C. Di \<in> Red_F_G (\<G>_set N) \<or>
    (\<exists>E \<in> (N - Red_F_\<G> N). Prec_F_g Di E C \<and> Di \<in> \<G>_F E)}\<close>
proof (rule;clarsimp)
  fix C D
  assume
    C_in: \<open>C \<in> Red_F_\<G> N\<close> and
    D_in: \<open>D \<in> \<G>_F C\<close> and
    not_sec_case: \<open>\<forall>E \<in> N - Red_F_\<G> N. Prec_F_g D E C \<longrightarrow> D \<notin> \<G>_F E\<close>
  have C_in_unfolded: "C \<in> {C. \<forall>Di \<in> \<G>_F C. Di \<in> Red_F_G (\<G>_set N) \<or>
    (\<exists>E\<in>N. Prec_F_g Di E C \<and> Di \<in> \<G>_F E)}"
    using C_in unfolding Red_F_\<G>_def .
  have neg_not_sec_case: \<open>\<not> (\<exists>E\<in>N - Red_F_\<G> N. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
    using not_sec_case by clarsimp
  have unfol_C_D: \<open>D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E\<in>N. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
    using prop_nested_in_set[of D \<G>_F C "\<lambda>x. x \<in> Red_F_G (\<Union> (\<G>_F ` N))"
      "\<lambda>x y. \<exists>E \<in> N. Prec_F_g y E x \<and> y \<in> \<G>_F E", OF D_in C_in_unfolded] by blast
  show \<open>D \<in> Red_F_G (\<G>_set N)\<close>
  proof (rule ccontr)
    assume contrad: \<open>D \<notin> Red_F_G (\<G>_set N)\<close>
    have non_empty: \<open>\<exists>E\<in>N. Prec_F_g D E C \<and> D \<in> \<G>_F E\<close> using contrad unfol_C_D by auto
    define B where \<open>B = {E \<in> N. Prec_F_g D E C \<and> D \<in> \<G>_F E}\<close>
    then have B_non_empty: \<open>B \<noteq> {}\<close> using non_empty by auto
    interpret minimal_element "Prec_F_g D" UNIV using all_wf[of D] .
    obtain F :: 'f where F: \<open>F = min_elt B\<close> by auto
    then have D_in_F: \<open>D \<in> \<G>_F F\<close> unfolding B_def using non_empty
      by (smt Sup_UNIV Sup_upper UNIV_I contra_subsetD empty_iff empty_subsetI mem_Collect_eq
        min_elt_mem unfol_C_D)
    have F_prec: \<open>Prec_F_g D F C\<close> using F min_elt_mem[of B, OF _ B_non_empty] unfolding B_def by auto
    have F_not_in: \<open>F \<notin> Red_F_\<G> N\<close>
    proof
      assume F_in: \<open>F \<in> Red_F_\<G> N\<close>
      have unfol_F_D: \<open>D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>G\<in>N. Prec_F_g D G F \<and> D \<in> \<G>_F G)\<close>
        using F_in D_in_F unfolding Red_F_\<G>_def by auto
      then have \<open>\<exists>G\<in>N. Prec_F_g D G F \<and> D \<in> \<G>_F G\<close> using contrad D_in unfolding Red_F_\<G>_def by auto
      then obtain G where G_in: \<open>G \<in> N\<close> and G_prec: \<open>Prec_F_g D G F\<close> and G_map: \<open>D \<in> \<G>_F G\<close> by auto
      have \<open>Prec_F_g D G C\<close> using G_prec F_prec Prec_trans by blast
      then have \<open>G \<in> B\<close> unfolding B_def using G_in G_map by auto
      then show \<open>False\<close> using F G_prec min_elt_minimal[of B G, OF _ B_non_empty] by auto
    qed
    have \<open>F \<in> N\<close> using F by (metis B_def B_non_empty mem_Collect_eq min_elt_mem top_greatest)
    then have \<open>F \<in> N - Red_F_\<G> N\<close> using F_not_in by auto
    then show \<open>False\<close>
      using D_in_F neg_not_sec_case F_prec by blast
  qed
next
  fix C
  assume only_if: \<open>\<forall>D\<in>\<G>_F C. D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E\<in>N - Red_F_\<G> N. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
  show \<open>C \<in> Red_F_\<G> N\<close> unfolding Red_F_\<G>_def using only_if by auto
qed

(* lem:lifting-main-technical *)
lemma not_red_map_in_map_not_red: \<open>\<G>_set N - Red_F_G (\<G>_set N) \<subseteq> \<G>_set (N - Red_F_\<G> N)\<close>
proof
  fix D
  assume
    D_hyp: \<open>D \<in> \<G>_set N - Red_F_G (\<G>_set N)\<close>
  interpret minimal_element "Prec_F_g D" UNIV using all_wf[of D] .
  have D_in: \<open>D \<in> \<G>_set N\<close> using D_hyp by blast
  have  D_not_in: \<open>D \<notin> Red_F_G (\<G>_set N)\<close> using D_hyp by blast
  have exist_C: \<open>\<exists>C. C \<in> N \<and> D \<in> \<G>_F C\<close> using D_in by auto
  define B where \<open>B = {C \<in> N. D \<in> \<G>_F C}\<close>
  obtain C where C: \<open>C = min_elt B\<close> by auto
  have C_in_N: \<open>C \<in> N\<close>
    using exist_C by (metis B_def C empty_iff mem_Collect_eq min_elt_mem top_greatest)
  have D_in_C: \<open>D \<in> \<G>_F C\<close>
    using exist_C by (metis B_def C empty_iff mem_Collect_eq min_elt_mem top_greatest)
  have C_not_in: \<open>C \<notin> Red_F_\<G> N\<close>
  proof
    assume C_in: \<open>C \<in> Red_F_\<G> N\<close>
    have \<open>D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E\<in>N. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
      using C_in D_in_C unfolding Red_F_\<G>_def by auto
    then show \<open>False\<close>
      proof
        assume \<open>D \<in> Red_F_G (\<G>_set N)\<close>
        then show \<open>False\<close> using D_not_in by simp
      next
        assume \<open>\<exists>E\<in>N. Prec_F_g D E C \<and> D \<in> \<G>_F E\<close>
        then show \<open>False\<close>
          using C by (metis (no_types, lifting) B_def UNIV_I empty_iff mem_Collect_eq
              min_elt_minimal top_greatest)
      qed
  qed
  show \<open>D \<in> \<G>_set (N - Red_F_\<G> N)\<close> using D_in_C C_not_in C_in_N by blast
qed

(* lem:nonredundant-entails-redundant *)
lemma Red_F_Bot_F: \<open>B \<in> Bot_F \<Longrightarrow> N \<Turnstile>\<G> {B} \<Longrightarrow> N - Red_F_\<G> N \<Turnstile>\<G> {B}\<close>
proof -
  fix B N
  assume
    B_in: \<open>B \<in> Bot_F\<close> and
    N_entails: \<open>N \<Turnstile>\<G> {B}\<close>
  then have to_bot: \<open>\<G>_set N - Red_F_G (\<G>_set N) \<Turnstile>G \<G>_F B\<close>
    using Ground.Red_F_Bot Bot_map unfolding entails_\<G>_def
      by (smt cSup_singleton Ground.entail_set_all_formulas image_insert image_is_empty subsetCE)
  have from_f: \<open>\<G>_set (N - Red_F_\<G> N) \<Turnstile>G \<G>_set N - Red_F_G (\<G>_set N)\<close>
    using Ground.subset_entailed[OF not_red_map_in_map_not_red] by blast
  then have \<open>\<G>_set (N - Red_F_\<G> N) \<Turnstile>G \<G>_F B\<close> using to_bot Ground.entails_trans by blast
  then show \<open>N - Red_F_\<G> N \<Turnstile>\<G> {B}\<close> using Bot_map unfolding entails_\<G>_def by simp
qed

(* lem:redundancy-monotonic-addition 1/2 *)
lemma Red_F_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> N'\<close>
  using Ground.Red_F_of_subset unfolding Red_F_\<G>_def by (smt Collect_mono \<G>_subset subset_iff)

(* lem:redundancy-monotonic-addition 2/2 *)
lemma Red_Inf_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_\<G> N \<subseteq> Red_Inf_\<G> N'\<close>
  using Collect_mono \<G>_subset subset_iff Ground.Red_Inf_of_subset unfolding Red_Inf_\<G>_def
  by (smt Ground.Red_F_of_subset Un_iff)

(* lem:redundancy-monotonic-deletion-forms *)
lemma Red_F_of_Red_F_subset_F: \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> (N - N')\<close>
proof
  fix N N' C
  assume
    N'_in_Red_F_N: \<open>N' \<subseteq> Red_F_\<G> N\<close> and
    C_in_red_F_N: \<open>C \<in> Red_F_\<G> N\<close>
  have lem8: \<open>\<forall>D \<in> \<G>_F C. D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E \<in> (N - Red_F_\<G> N). Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
    using Red_F_\<G>_equiv_def C_in_red_F_N by blast
  show \<open>C \<in> Red_F_\<G> (N - N')\<close> unfolding Red_F_\<G>_def
  proof (rule,rule)
    fix D
    assume \<open>D \<in> \<G>_F C\<close>
    then have \<open>D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E \<in> (N - Red_F_\<G> N). Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
      using lem8 by auto
    then show \<open>D \<in> Red_F_G (\<G>_set (N - N')) \<or> (\<exists>E\<in>N - N'. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
    proof
      assume \<open>D \<in> Red_F_G (\<G>_set N)\<close>
      then have \<open>D \<in> Red_F_G (\<G>_set N - Red_F_G (\<G>_set N))\<close>
        using Ground.Red_F_of_Red_F_subset[of "Red_F_G (\<G>_set N)" "\<G>_set N"] by auto
      then have \<open>D \<in> Red_F_G (\<G>_set (N - Red_F_\<G> N))\<close>
        using Ground.Red_F_of_subset[OF not_red_map_in_map_not_red[of N]] by auto
      then have \<open>D \<in> Red_F_G (\<G>_set (N - N'))\<close>
        using N'_in_Red_F_N \<G>_subset[of "N - Red_F_\<G> N" "N - N'"]
        by (smt DiffE DiffI Ground.Red_F_of_subset subsetCE subsetI)
      then show ?thesis by blast
    next
      assume \<open>\<exists>E\<in>N - Red_F_\<G> N. Prec_F_g D E C \<and> D \<in> \<G>_F E\<close>
      then obtain E where
        E_in: \<open>E\<in>N - Red_F_\<G> N\<close> and
        E_prec_C: \<open>Prec_F_g D E C\<close> and
        D_in: \<open>D \<in> \<G>_F E\<close>
        by auto
      have \<open>E \<in> N - N'\<close> using E_in N'_in_Red_F_N by blast
      then show ?thesis using E_prec_C D_in by blast
    qed
  qed
qed

(* lem:redundancy-monotonic-deletion-infs *)
lemma Red_Inf_of_Red_F_subset_F: \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_Inf_\<G> N \<subseteq> Red_Inf_\<G> (N - N') \<close>
proof
  fix N N' \<iota>
  assume
    N'_in_Red_F_N: \<open>N' \<subseteq> Red_F_\<G> N\<close> and
    i_in_Red_Inf_N: \<open>\<iota> \<in> Red_Inf_\<G> N\<close>
  have i_in: \<open>\<iota> \<in> Inf_F\<close> using i_in_Red_Inf_N unfolding Red_Inf_\<G>_def by blast
  {
    assume not_none: "\<G>_Inf \<iota> \<noteq> None"
    have \<open>\<forall>\<iota>' \<in> the (\<G>_Inf \<iota>). \<iota>' \<in> Red_Inf_G (\<G>_set N)\<close>
      using not_none i_in_Red_Inf_N unfolding Red_Inf_\<G>_def by auto
    then have \<open>\<forall>\<iota>' \<in> the (\<G>_Inf \<iota>). \<iota>' \<in> Red_Inf_G (\<G>_set N - Red_F_G (\<G>_set N))\<close>
      using not_none Ground.Red_Inf_of_Red_F_subset by blast
    then have ip_in_Red_Inf_G: \<open>\<forall>\<iota>' \<in> the (\<G>_Inf \<iota>). \<iota>' \<in> Red_Inf_G (\<G>_set (N - Red_F_\<G> N))\<close>
      using not_none Ground.Red_Inf_of_subset[OF not_red_map_in_map_not_red[of N]] by auto
    then have not_none_in: \<open>\<forall>\<iota>' \<in> the (\<G>_Inf \<iota>). \<iota>' \<in> Red_Inf_G (\<G>_set (N - N'))\<close>
      using not_none N'_in_Red_F_N
      by (meson Diff_mono Ground.Red_Inf_of_subset \<G>_subset subset_iff subset_refl)
    then have "the (\<G>_Inf \<iota>) \<subseteq> Red_Inf_G (\<G>_set (N - N'))" by blast
  }
  moreover {
    assume none: "\<G>_Inf \<iota> = None"
    have ground_concl_subs: "\<G>_F (concl_of \<iota>) \<subseteq> (\<G>_set N \<union> Red_F_G (\<G>_set N))"
      using none i_in_Red_Inf_N unfolding Red_Inf_\<G>_def by blast
    then have d_in_imp12: "D \<in> \<G>_F (concl_of \<iota>) \<Longrightarrow> D \<in> \<G>_set N - Red_F_G (\<G>_set N) \<or> D \<in> Red_F_G (\<G>_set N)"
      by blast
    have d_in_imp1: "D \<in> \<G>_set N - Red_F_G (\<G>_set N) \<Longrightarrow> D \<in> \<G>_set (N - N')"
      using not_red_map_in_map_not_red N'_in_Red_F_N by blast
    have d_in_imp_d_in: "D \<in> Red_F_G (\<G>_set N) \<Longrightarrow> D \<in> Red_F_G (\<G>_set N - Red_F_G (\<G>_set N))"
      using Ground.Red_F_of_Red_F_subset[of "Red_F_G (\<G>_set N)" "\<G>_set N"] by blast
    have g_subs1: "\<G>_set N - Red_F_G (\<G>_set N) \<subseteq> \<G>_set (N - Red_F_\<G> N)"
      using not_red_map_in_map_not_red unfolding Red_F_\<G>_def by auto
    have g_subs2: "\<G>_set (N - Red_F_\<G> N) \<subseteq> \<G>_set (N - N')"
      using N'_in_Red_F_N by blast
    have d_in_imp2: "D \<in> Red_F_G (\<G>_set N) \<Longrightarrow> D \<in> Red_F_G (\<G>_set (N - N'))"
      using Ground.Red_F_of_subset Ground.Red_F_of_subset[OF g_subs1]
        Ground.Red_F_of_subset[OF g_subs2] d_in_imp_d_in by blast
    have "\<G>_F (concl_of \<iota>) \<subseteq> (\<G>_set (N - N') \<union> Red_F_G (\<G>_set (N - N')))"
      using d_in_imp12 d_in_imp1 d_in_imp2
      by (smt Ground.Red_F_of_Red_F_subset Ground.Red_F_of_subset UnCI UnE Un_Diff_cancel2
        ground_concl_subs g_subs1 g_subs2 subset_iff)
  }
  ultimately show \<open>\<iota> \<in> Red_Inf_\<G> (N - N')\<close> using i_in unfolding Red_Inf_\<G>_def by auto
qed

(* lem:concl-contained-implies-red-inf *)
lemma Red_Inf_of_Inf_to_N_F:
  assumes
    i_in: \<open>\<iota> \<in> Inf_F\<close> and
    concl_i_in: \<open>concl_of \<iota> \<in> N\<close>
  shows
    \<open>\<iota> \<in> Red_Inf_\<G> N \<close>
proof -
  have \<open>\<iota> \<in> Inf_F \<Longrightarrow> \<G>_Inf \<iota> \<noteq> None \<Longrightarrow> the (\<G>_Inf \<iota>) \<subseteq> Red_Inf_G (\<G>_F (concl_of \<iota>))\<close> using inf_map by simp
  moreover have \<open>Red_Inf_G (\<G>_F (concl_of \<iota>)) \<subseteq> Red_Inf_G (\<G>_set N)\<close>
    using concl_i_in Ground.Red_Inf_of_subset by blast
  moreover have "\<iota> \<in> Inf_F \<Longrightarrow> \<G>_Inf \<iota> = None \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<G>_F (concl_of \<iota>) \<subseteq> \<G>_set N"
    by blast
  ultimately show ?thesis using i_in concl_i_in unfolding Red_Inf_\<G>_def by auto
qed

(* thm:FRedsqsubset-is-red-crit and also thm:lifted-red-crit if ordering empty *)
sublocale lifted_calculus_with_red_crit: calculus_with_red_crit
  where
    Bot = Bot_F and Inf = Inf_F and entails = entails_\<G> and
    Red_Inf = Red_Inf_\<G> and Red_F = Red_F_\<G>
proof
  fix B N N' \<iota>
  show \<open>Red_Inf_\<G> N \<subseteq> Inf_F\<close> unfolding Red_Inf_\<G>_def by blast
  show \<open>B \<in> Bot_F \<Longrightarrow> N \<Turnstile>\<G> {B} \<Longrightarrow> N - Red_F_\<G> N \<Turnstile>\<G> {B}\<close> using Red_F_Bot_F by simp
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> N'\<close> using Red_F_of_subset_F by simp
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_\<G> N \<subseteq> Red_Inf_\<G> N'\<close> using Red_Inf_of_subset_F by simp
  show \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> (N - N')\<close> using Red_F_of_Red_F_subset_F by simp
  show \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_Inf_\<G> N \<subseteq> Red_Inf_\<G> (N - N')\<close> using Red_Inf_of_Red_F_subset_F by simp
  show \<open>\<iota> \<in> Inf_F \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_Inf_\<G> N\<close> using Red_Inf_of_Inf_to_N_F by simp
qed

lemma lifted_calc_is_calc: "calculus_with_red_crit Bot_F Inf_F entails_\<G> Red_Inf_\<G> Red_F_\<G>"
  using lifted_calculus_with_red_crit.calculus_with_red_crit_axioms .

lemma grounded_inf_in_ground_inf: "\<iota> \<in> Inf_F \<Longrightarrow> \<G>_Inf \<iota> \<noteq> None \<Longrightarrow> the (\<G>_Inf \<iota>) \<subseteq> Inf_G"
  using inf_map Ground.Red_Inf_to_Inf by blast

(* lem:sat-wrt-finf *)
lemma sat_imp_ground_sat: "lifted_calculus_with_red_crit.saturated N \<Longrightarrow> Ground.Inf_from (\<G>_set N) \<subseteq>
  ({\<iota>. \<exists>\<iota>'\<in> Non_ground.Inf_from N. \<G>_Inf \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_Inf \<iota>')} \<union> Red_Inf_G (\<G>_set N)) \<Longrightarrow>
  Ground.saturated (\<G>_set N)"
proof -
  fix N
  assume
    sat_n: "lifted_calculus_with_red_crit.saturated N" and
    inf_grounded_in: "Ground.Inf_from (\<G>_set N) \<subseteq>
    ({\<iota>. \<exists>\<iota>'\<in> Non_ground.Inf_from N. \<G>_Inf \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_Inf \<iota>')} \<union> Red_Inf_G (\<G>_set N))"
  show "Ground.saturated (\<G>_set N)" unfolding Ground.saturated_def
  proof
    fix \<iota>
    assume i_in: "\<iota> \<in> Ground.Inf_from (\<G>_set N)"
    {
      assume "\<iota> \<in> {\<iota>. \<exists>\<iota>'\<in> Non_ground.Inf_from N. \<G>_Inf \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_Inf \<iota>')}"
      then obtain \<iota>' where "\<iota>'\<in> Non_ground.Inf_from N" "\<G>_Inf \<iota>' \<noteq> None" "\<iota> \<in> the (\<G>_Inf \<iota>')" by blast
      then have "\<iota> \<in> Red_Inf_G (\<G>_set N)"
        using Red_Inf_\<G>_def sat_n unfolding lifted_calculus_with_red_crit.saturated_def by auto
    }
    then show "\<iota> \<in> Red_Inf_G (\<G>_set N)" using inf_grounded_in i_in by blast
  qed
qed

(* thm:finf-complete *)
theorem stat_ref_comp_to_non_ground:
  assumes
    stat_ref_G: "static_refutational_complete_calculus Bot_G Inf_G entails_G Red_Inf_G Red_F_G" and
    sat_n_imp: "\<And>N. (lifted_calculus_with_red_crit.saturated N \<Longrightarrow> Ground.Inf_from (\<G>_set N) \<subseteq>
    ({\<iota>. \<exists>\<iota>'\<in> Non_ground.Inf_from N. \<G>_Inf \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_Inf \<iota>')} \<union> Red_Inf_G (\<G>_set N)))"
  shows
    "static_refutational_complete_calculus Bot_F Inf_F entails_\<G> Red_Inf_\<G> Red_F_\<G>"
proof
  fix B N
  assume
    b_in: "B \<in> Bot_F" and
    sat_n: "lifted_calculus_with_red_crit.saturated N" and
    n_entails_bot: "N \<Turnstile>\<G> {B}"
  have ground_n_entails: "\<G>_set N \<Turnstile>G \<G>_F B"
    using n_entails_bot unfolding entails_\<G>_def by simp
  then obtain BG where bg_in1: "BG \<in> \<G>_F B"
    using Bot_map_not_empty[OF b_in] by blast
  then have bg_in: "BG \<in> Bot_G"
    using Bot_map[OF b_in] by blast
  have ground_n_entails_bot: "\<G>_set N \<Turnstile>G {BG}"
    using ground_n_entails bg_in1 Ground.entail_set_all_formulas by blast
  have "Ground.Inf_from (\<G>_set N) \<subseteq>
    ({\<iota>. \<exists>\<iota>'\<in> Non_ground.Inf_from N. \<G>_Inf \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_Inf \<iota>')} \<union> Red_Inf_G (\<G>_set N))"
    using sat_n_imp[OF sat_n] .
  have "Ground.saturated (\<G>_set N)"
    using sat_imp_ground_sat[OF sat_n sat_n_imp[OF sat_n]] .
  then have "\<exists>BG'\<in>Bot_G. BG' \<in> (\<G>_set N)"
    using stat_ref_G Ground.calculus_with_red_crit_axioms bg_in ground_n_entails_bot
    unfolding static_refutational_complete_calculus_def static_refutational_complete_calculus_axioms_def
    by blast
  then show "\<exists>B'\<in> Bot_F. B' \<in> N"
    using bg_in Bot_cond Bot_map_not_empty Bot_cond by blast
qed

end

abbreviation Empty_Order where
  "Empty_Order C1 C2 \<equiv> False"

lemma any_to_empty_order_lifting:
  "lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F
    \<G>_Inf Prec_F_g \<Longrightarrow> lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G
    Red_F_G \<G>_F \<G>_Inf (\<lambda>g. Empty_Order)"
proof -
  fix Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf Prec_F_g
  assume lift: "lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G
    Red_F_G \<G>_F \<G>_Inf Prec_F_g"
  then interpret lift_g:
    lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F
      \<G>_Inf Prec_F_g
    by auto
  have empty_wf: "minimal_element ((\<lambda>g. Empty_Order) g) UNIV"
    by (simp add: lift_g.all_wf minimal_element.intro po_on_def transp_on_def wfp_on_def
      wfp_on_imp_irreflp_on)
  then show "lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G
    \<G>_F \<G>_Inf (\<lambda>g. Empty_Order)"
    by (simp add: empty_wf lift_g.standard_lifting_axioms
      lifting_with_wf_ordering_family_axioms.intro lifting_with_wf_ordering_family_def)
qed

locale lifting_equivalence_with_empty_order =
  any_order_lifting: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G
    Red_F_G \<G>_F \<G>_Inf Prec_F_g +
  empty_order_lifting: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G
    Red_F_G \<G>_F \<G>_Inf "\<lambda>g. Empty_Order"
  for
    \<G>_F :: \<open>'f \<Rightarrow> 'g set\<close> and
    \<G>_Inf :: \<open>'f inference \<Rightarrow> 'g inference set option\<close> and
    Bot_F :: \<open>'f set\<close> and
    Inf_F :: \<open>'f inference set\<close> and
    Bot_G :: \<open>'g set\<close> and
    Inf_G :: \<open>'g inference set\<close> and
    entails_G :: \<open>'g set \<Rightarrow> 'g set \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Red_Inf_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close> and
    Prec_F_g :: \<open>'g \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool\<close>

sublocale lifting_with_wf_ordering_family \<subseteq> lifting_equivalence_with_empty_order
proof
  show "po_on Empty_Order UNIV"
    unfolding po_on_def by (simp add: transp_onI wfp_on_imp_irreflp_on)
  show "wfp_on Empty_Order UNIV"
    unfolding wfp_on_def by simp
qed

context lifting_equivalence_with_empty_order
begin

(* lem:saturation-indep-of-sqsubset *)
lemma saturated_empty_order_equiv_saturated:
  "any_order_lifting.lifted_calculus_with_red_crit.saturated N =
    empty_order_lifting.lifted_calculus_with_red_crit.saturated N" by standard

(* lem:static-ref-compl-indep-of-sqsubset *)
lemma static_empty_order_equiv_static:
  "static_refutational_complete_calculus Bot_F Inf_F
    any_order_lifting.entails_\<G> empty_order_lifting.Red_Inf_\<G> empty_order_lifting.Red_F_\<G> =
    static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G>
      any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>"
  unfolding static_refutational_complete_calculus_def
  by (rule iffI) (standard,(standard)[],simp)+

(* thm:FRedsqsubset-is-dyn-ref-compl *)
theorem static_to_dynamic:
  "static_refutational_complete_calculus Bot_F Inf_F
    any_order_lifting.entails_\<G> empty_order_lifting.Red_Inf_\<G> empty_order_lifting.Red_F_\<G> =
    dynamic_refutational_complete_calculus Bot_F Inf_F
    any_order_lifting.entails_\<G> any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G> "
  (is "?static=?dynamic")
proof
  assume ?static
  then have static_general:
    "static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G>
      any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>" (is "?static_gen")
    using static_empty_order_equiv_static by simp
  interpret static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G>
    any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>
    using static_general .
  show "?dynamic" by standard
next
  assume dynamic_gen: ?dynamic
  interpret dynamic_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G>
    any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>
    using dynamic_gen .
  have "static_refutational_complete_calculus Bot_F Inf_F any_order_lifting.entails_\<G>
    any_order_lifting.Red_Inf_\<G> any_order_lifting.Red_F_\<G>"
    by standard
  then show "?static" using static_empty_order_equiv_static by simp
qed

end

subsection \<open>Lifting with a Family of Redundancy Criteria\<close>

locale standard_lifting_with_red_crit_family = Non_ground: inference_system Inf_F
  + Ground_family: calculus_with_red_crit_family Bot_G Inf_G Q entails_q Red_Inf_q Red_F_q
  for
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    Inf_G :: \<open>'g inference set\<close> and
    Q :: "'q itself" and
    entails_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g set \<Rightarrow> bool)" and
    Red_Inf_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g inference set)" and
    Red_F_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g set)"
  + fixes
    Bot_F :: "'f set" and
    \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" and
    \<G>_Inf_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set option" and
    Prec_F_g :: "'g \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool"
  assumes
    standard_lifting_family: "lifting_with_wf_ordering_family Bot_F Inf_F Bot_G (entails_q q)
      Inf_G (Red_Inf_q q) (Red_F_q q) (\<G>_F_q q) (\<G>_Inf_q q) Prec_F_g"
begin

definition \<G>_set_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'g set" where
  "\<G>_set_q q N \<equiv> \<Union> (\<G>_F_q q ` N)"

definition Red_Inf_\<G>_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f inference set" where
  "Red_Inf_\<G>_q q N = {\<iota> \<in> Inf_F. (\<G>_Inf_q q \<iota> \<noteq> None \<and> the (\<G>_Inf_q q \<iota>) \<subseteq> Red_Inf_q q (\<G>_set_q q N))
  \<or> (\<G>_Inf_q q \<iota> = None \<and> \<G>_F_q q (concl_of \<iota>) \<subseteq> (\<G>_set_q q N \<union> Red_F_q q (\<G>_set_q q N)))}"

definition Red_Inf_\<G>_Q :: "'f set \<Rightarrow> 'f inference set" where
  "Red_Inf_\<G>_Q N = \<Inter> {X N |X. X \<in> (Red_Inf_\<G>_q ` UNIV)}"

definition Red_F_\<G>_empty_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_empty_q q N = {C. \<forall>D \<in> \<G>_F_q q C. D \<in> Red_F_q q (\<G>_set_q q N) \<or>
    (\<exists>E \<in> N. Empty_Order E C \<and> D \<in> \<G>_F_q q E)}"

definition Red_F_\<G>_empty :: "'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_empty N = \<Inter> {X N |X. X \<in> (Red_F_\<G>_empty_q ` UNIV)}"

definition Red_F_\<G>_q_g :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_q_g q N = {C. \<forall>D \<in> \<G>_F_q q C. D \<in> Red_F_q q (\<G>_set_q q N) \<or> (\<exists>E \<in> N. Prec_F_g D E C \<and> D \<in> \<G>_F_q q E)}"

definition Red_F_\<G>_g :: "'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_g N = \<Inter> {X N |X. X \<in> (Red_F_\<G>_q_g ` UNIV)}"

definition entails_\<G>_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> bool" where
  "entails_\<G>_q q N1 N2 \<equiv> entails_q q (\<G>_set_q q N1) (\<G>_set_q q N2)"

definition entails_\<G>_Q :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>\<inter>" 50) where
  "entails_\<G>_Q N1 N2 \<equiv> \<forall>q. entails_\<G>_q q N1 N2"

lemma red_crit_lifting_family:
  "calculus_with_red_crit Bot_F Inf_F (entails_\<G>_q q) (Red_Inf_\<G>_q q) (Red_F_\<G>_q_g q)"
proof -
  fix q
  interpret wf_lift:
    lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q q" Inf_G "Red_Inf_q q" "Red_F_q q"
      "\<G>_F_q q" "\<G>_Inf_q q" Prec_F_g
    using standard_lifting_family .
  have "entails_\<G>_q q = wf_lift.entails_\<G>"
    unfolding entails_\<G>_q_def wf_lift.entails_\<G>_def \<G>_set_q_def by blast
  moreover have "Red_Inf_\<G>_q q = wf_lift.Red_Inf_\<G>"
    unfolding Red_Inf_\<G>_q_def \<G>_set_q_def wf_lift.Red_Inf_\<G>_def by blast
  moreover have "Red_F_\<G>_q_g q = wf_lift.Red_F_\<G>"
    unfolding Red_F_\<G>_q_g_def \<G>_set_q_def wf_lift.Red_F_\<G>_def by blast
  ultimately show "calculus_with_red_crit Bot_F Inf_F (entails_\<G>_q q) (Red_Inf_\<G>_q q) (Red_F_\<G>_q_g q)"
    using wf_lift.lifted_calculus_with_red_crit.calculus_with_red_crit_axioms by simp
qed

lemma red_crit_lifting_family_empty_ord:
  "calculus_with_red_crit Bot_F Inf_F (entails_\<G>_q q) (Red_Inf_\<G>_q q) (Red_F_\<G>_empty_q q)"
proof -
  fix q
  interpret wf_lift:
    lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q q" Inf_G "Red_Inf_q q" "Red_F_q q"
      "\<G>_F_q q" "\<G>_Inf_q q" Prec_F_g
    using standard_lifting_family .
  have "entails_\<G>_q q = wf_lift.entails_\<G>"
    unfolding entails_\<G>_q_def wf_lift.entails_\<G>_def \<G>_set_q_def by blast
  moreover have "Red_Inf_\<G>_q q = wf_lift.Red_Inf_\<G>"
    unfolding Red_Inf_\<G>_q_def \<G>_set_q_def wf_lift.Red_Inf_\<G>_def by blast
  moreover have "Red_F_\<G>_empty_q q = wf_lift.empty_order_lifting.Red_F_\<G>"
    unfolding Red_F_\<G>_empty_q_def \<G>_set_q_def wf_lift.empty_order_lifting.Red_F_\<G>_def by blast
  ultimately show "calculus_with_red_crit Bot_F Inf_F (entails_\<G>_q q) (Red_Inf_\<G>_q q) (Red_F_\<G>_empty_q q)"
    using wf_lift.empty_order_lifting.lifted_calculus_with_red_crit.calculus_with_red_crit_axioms
    by simp
qed

lemma cons_rel_fam_Q_lem: \<open>consequence_relation_family Bot_F entails_\<G>_q\<close>
proof
  show "Bot_F \<noteq> {}"
    using standard_lifting_family
    by (meson ex_in_conv lifting_with_wf_ordering_family.axioms(1) standard_lifting.Bot_F_not_empty)
next
  fix qi
  show "Bot_F \<noteq> {}"
    using standard_lifting_family
    by (meson ex_in_conv lifting_with_wf_ordering_family.axioms(1) standard_lifting.Bot_F_not_empty)
next
  fix qi B N1
  assume
    B_in: "B \<in> Bot_F"
  interpret lift: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q qi" Inf_G "Red_Inf_q qi"
    "Red_F_q qi" "\<G>_F_q qi" "\<G>_Inf_q qi" Prec_F_g
    by (rule standard_lifting_family)
  have "(entails_\<G>_q qi) = lift.entails_\<G>"
    unfolding entails_\<G>_q_def lift.entails_\<G>_def \<G>_set_q_def by simp
  then show "entails_\<G>_q qi {B} N1"
    using B_in lift.lifted_consequence_relation.bot_implies_all by auto
next
  fix qi and N2 N1::"'f set"
  assume
    N_incl: "N2 \<subseteq> N1"
  interpret lift: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q qi" Inf_G "Red_Inf_q qi"
   "Red_F_q qi" "\<G>_F_q qi" "\<G>_Inf_q qi" Prec_F_g
    by (rule standard_lifting_family)
  have "(entails_\<G>_q qi) = lift.entails_\<G>"
    unfolding entails_\<G>_q_def lift.entails_\<G>_def \<G>_set_q_def by simp
  then show "entails_\<G>_q qi N1 N2"
    using N_incl by (simp add: lift.lifted_consequence_relation.subset_entailed)
next
  fix qi N1 N2
  assume
    all_C: "\<forall>C\<in> N2. entails_\<G>_q qi N1 {C}"
  interpret lift: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q qi" Inf_G "Red_Inf_q qi"
    "Red_F_q qi" "\<G>_F_q qi" "\<G>_Inf_q qi" Prec_F_g
    by (rule standard_lifting_family)
  have "(entails_\<G>_q qi) = lift.entails_\<G>"
    unfolding entails_\<G>_q_def lift.entails_\<G>_def \<G>_set_q_def by simp
  then show "entails_\<G>_q qi N1 N2"
    using all_C lift.lifted_consequence_relation.all_formulas_entailed by presburger
next
  fix qi N1 N2 N3
  assume
    entails12: "entails_\<G>_q qi N1 N2" and
    entails23: "entails_\<G>_q qi N2 N3"
  interpret lift: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q qi" Inf_G "Red_Inf_q qi"
    "Red_F_q qi" "\<G>_F_q qi" "\<G>_Inf_q qi" Prec_F_g
    by (rule standard_lifting_family)
  have "(entails_\<G>_q qi) = lift.entails_\<G>"
    unfolding entails_\<G>_q_def lift.entails_\<G>_def \<G>_set_q_def by simp
  then show "entails_\<G>_q qi N1 N3"
    using entails12 entails23 lift.lifted_consequence_relation.entails_trans by presburger
qed

interpretation cons_rel_Q: consequence_relation Bot_F entails_\<G>_Q
proof -
  interpret cons_rel_fam: consequence_relation_family Bot_F Q entails_\<G>_q
    by (rule cons_rel_fam_Q_lem)
  have "consequence_relation_family.entails_Q entails_\<G>_q = entails_\<G>_Q"
    unfolding entails_\<G>_Q_def cons_rel_fam.entails_Q_def by (simp add: entails_\<G>_q_def)
  then show "consequence_relation Bot_F entails_\<G>_Q"
  using consequence_relation_family.intersect_cons_rel_family[OF cons_rel_fam_Q_lem] by simp
qed

sublocale lifted_calc_w_red_crit_family:
  calculus_with_red_crit_family Bot_F Inf_F Q entails_\<G>_q Red_Inf_\<G>_q Red_F_\<G>_q_g
  using cons_rel_fam_Q_lem red_crit_lifting_family
  by (simp add: calculus_with_red_crit_family.intro calculus_with_red_crit_family_axioms_def)

lemma lifted_calc_family_is_calc: "calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_g"
proof -
  have "lifted_calc_w_red_crit_family.entails_Q = entails_\<G>_Q"
    unfolding entails_\<G>_Q_def lifted_calc_w_red_crit_family.entails_Q_def by simp
  moreover have "lifted_calc_w_red_crit_family.Red_Inf_Q = Red_Inf_\<G>_Q"
    unfolding Red_Inf_\<G>_Q_def lifted_calc_w_red_crit_family.Red_Inf_Q_def by simp
  moreover have "lifted_calc_w_red_crit_family.Red_F_Q = Red_F_\<G>_g"
    unfolding Red_F_\<G>_g_def lifted_calc_w_red_crit_family.Red_F_Q_def by simp
  ultimately show "calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_g"
  using lifted_calc_w_red_crit_family.inter_red_crit by simp
qed

sublocale empty_ord_lifted_calc_w_red_crit_family:
  calculus_with_red_crit_family Bot_F Inf_F Q entails_\<G>_q Red_Inf_\<G>_q Red_F_\<G>_empty_q
  using cons_rel_fam_Q_lem red_crit_lifting_family_empty_ord
  by (simp add: calculus_with_red_crit_family.intro calculus_with_red_crit_family_axioms_def)

lemma inter_calc: "calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_empty"
proof -
  have "lifted_calc_w_red_crit_family.entails_Q = entails_\<G>_Q"
    unfolding entails_\<G>_Q_def lifted_calc_w_red_crit_family.entails_Q_def by simp
  moreover have "empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q = Red_Inf_\<G>_Q"
    unfolding Red_Inf_\<G>_Q_def lifted_calc_w_red_crit_family.Red_Inf_Q_def by simp
  moreover have "empty_ord_lifted_calc_w_red_crit_family.Red_F_Q = Red_F_\<G>_empty"
    unfolding Red_F_\<G>_empty_def empty_ord_lifted_calc_w_red_crit_family.Red_F_Q_def by simp
  ultimately show "calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_empty"
  using empty_ord_lifted_calc_w_red_crit_family.inter_red_crit by simp
qed

(* thm:intersect-finf-complete *)
theorem stat_ref_comp_to_non_ground_fam_inter:
  assumes
    stat_ref_G: "\<And>q. static_refutational_complete_calculus Bot_G Inf_G (entails_q q) (Red_Inf_q q) (Red_F_q q)" and
      sat_n_imp: "\<And>N. (empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated N \<Longrightarrow>
        \<exists>q. Ground_family.Inf_from (\<G>_set_q q N) \<subseteq>
        ({\<iota>. \<exists>\<iota>'\<in> Non_ground.Inf_from N. \<G>_Inf_q q \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_Inf_q q \<iota>')} \<union> Red_Inf_q q (\<G>_set_q q N)))"
  shows
    "static_refutational_complete_calculus Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_empty"
    using inter_calc
    unfolding static_refutational_complete_calculus_def static_refutational_complete_calculus_axioms_def
proof (standard, clarify)
  fix B N
  assume
    b_in: "B \<in> Bot_F" and
    sat_n: "calculus_with_red_crit.saturated Inf_F Red_Inf_\<G>_Q N" and
    entails_bot: "N \<Turnstile>\<inter> {B}"
  interpret calculus_with_red_crit Bot_F Inf_F entails_\<G>_Q Red_Inf_\<G>_Q Red_F_\<G>_empty
    using inter_calc by blast
  have "empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q = Red_Inf_\<G>_Q"
    unfolding Red_Inf_\<G>_Q_def lifted_calc_w_red_crit_family.Red_Inf_Q_def by simp
  then have empty_ord_sat_n: "empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated N"
    using sat_n
    unfolding saturated_def empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated_def
    by simp
  then obtain q where inf_subs: "Ground_family.Inf_from (\<G>_set_q q N) \<subseteq>
    ({\<iota>. \<exists>\<iota>'\<in> Non_ground.Inf_from N. \<G>_Inf_q q \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_Inf_q q \<iota>')} \<union> Red_Inf_q q (\<G>_set_q q N))"
    using sat_n_imp[of N] by blast
  interpret q_calc: calculus_with_red_crit Bot_F Inf_F "entails_\<G>_q q" "Red_Inf_\<G>_q q" "Red_F_\<G>_q_g q"
    using lifted_calc_w_red_crit_family.all_red_crit[of q] .
  have n_q_sat: "q_calc.saturated N" using lifted_calc_w_red_crit_family.sat_int_to_sat_q empty_ord_sat_n by simp
  interpret lifted_q_calc: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "entails_q q" Inf_G "Red_Inf_q q" "Red_F_q q" "\<G>_F_q q" "\<G>_Inf_q q"
    by (simp add: standard_lifting_family)
  have "lifted_q_calc.empty_order_lifting.lifted_calculus_with_red_crit.saturated N"
    using n_q_sat unfolding Red_Inf_\<G>_q_def \<G>_set_q_def lifted_q_calc.empty_order_lifting.Red_Inf_\<G>_def
      lifted_q_calc.lifted_calculus_with_red_crit.saturated_def q_calc.saturated_def by auto
  then have ground_sat_n: "lifted_q_calc.Ground.saturated (\<G>_set_q q N)"
    using lifted_q_calc.sat_imp_ground_sat[of N] inf_subs unfolding \<G>_set_q_def by blast
  have "entails_\<G>_q q N {B}" using entails_bot unfolding entails_\<G>_Q_def by simp
  then have ground_n_entails_bot: "entails_q q (\<G>_set_q q N) (\<G>_set_q q {B})" unfolding entails_\<G>_q_def .
  interpret static_refutational_complete_calculus Bot_G Inf_G "entails_q q" "Red_Inf_q q" "Red_F_q q"
    using stat_ref_G[of q] .
  obtain BG where bg_in: "BG \<in> \<G>_F_q q B"
    using lifted_q_calc.Bot_map_not_empty[OF b_in] by blast
  then have "BG \<in> Bot_G" using lifted_q_calc.Bot_map[OF b_in] by blast
  then have "\<exists>BG'\<in>Bot_G. BG' \<in> \<G>_set_q q N"
    using ground_sat_n ground_n_entails_bot static_refutational_complete[of BG, OF _ ground_sat_n]
      bg_in lifted_q_calc.Ground.entail_set_all_formulas[of "\<G>_set_q q N" "\<G>_set_q q {B}"] unfolding \<G>_set_q_def
    by simp
  then show "\<exists>B'\<in> Bot_F. B' \<in> N" using lifted_q_calc.Bot_cond unfolding \<G>_set_q_def by blast
qed

(* lem:intersect-saturation-indep-of-sqsubset *)
lemma sat_eq_sat_empty_order: "lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated N =
  empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated N "
  by simp

(* lem:intersect-static-ref-compl-indep-of-sqsubset *)
lemma static_empty_ord_inter_equiv_static_inter:
  "static_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    lifted_calc_w_red_crit_family.Red_Inf_Q lifted_calc_w_red_crit_family.Red_F_Q =
  static_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q empty_ord_lifted_calc_w_red_crit_family.Red_F_Q"
  unfolding static_refutational_complete_calculus_def
  by (simp add: empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.calculus_with_red_crit_axioms
    lifted_calc_w_red_crit_family.inter_red_crit_calculus.calculus_with_red_crit_axioms)

(* thm:intersect-static-ref-compl-is-dyn-ref-compl-with-order *)
theorem stat_eq_dyn_ref_comp_fam_inter: "static_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q empty_ord_lifted_calc_w_red_crit_family.Red_F_Q =
  dynamic_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    lifted_calc_w_red_crit_family.Red_Inf_Q lifted_calc_w_red_crit_family.Red_F_Q"  (is "?static=?dynamic")
proof
  assume ?static
  then have static_general: "static_refutational_complete_calculus Bot_F Inf_F
    lifted_calc_w_red_crit_family.entails_Q lifted_calc_w_red_crit_family.Red_Inf_Q
    lifted_calc_w_red_crit_family.Red_F_Q" (is "?static_gen")
    using static_empty_ord_inter_equiv_static_inter
    by simp
  interpret static_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    lifted_calc_w_red_crit_family.Red_Inf_Q lifted_calc_w_red_crit_family.Red_F_Q
    using static_general .
  show "?dynamic" by standard
next
  assume dynamic_gen: ?dynamic
  interpret dynamic_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    lifted_calc_w_red_crit_family.Red_Inf_Q lifted_calc_w_red_crit_family.Red_F_Q
    using dynamic_gen .
  have "static_refutational_complete_calculus Bot_F Inf_F lifted_calc_w_red_crit_family.entails_Q
    lifted_calc_w_red_crit_family.Red_Inf_Q lifted_calc_w_red_crit_family.Red_F_Q"
    by standard
  then show "?static" using static_empty_ord_inter_equiv_static_inter by simp
qed

end

end
