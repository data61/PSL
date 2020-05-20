section \<open>Chamber complexes\<close>

text \<open>
  Now we develop the basic theory of chamber complexes, including both thin and thick complexes.
  Some terminology: a maximal simplex is now called a chamber, and a chain (with respect to
  adjacency) of chambers is now called a gallery. A gallery in which no chamber appears more than
  once is called proper, and we use the prefix p as a naming convention to denote proper.
  Again, we remind the reader that some sources reserve the name gallery for (a slightly weaker
  notion of) what we are calling a proper gallery, using pregallery to denote an improper gallery.
\<close>

theory Chamber
imports Algebra Simplicial

begin

subsection \<open>Locale definition and basic facts\<close>

locale ChamberComplex = SimplicialComplex X
  for X :: "'a set set"
+ assumes simplex_in_max : "y\<in>X \<Longrightarrow> \<exists>x. maxsimp x \<and> y\<subseteq>x"
  and     maxsimp_connect: "\<lbrakk> x \<noteq> y; maxsimp x; maxsimp y \<rbrakk> \<Longrightarrow> 
                            \<exists>xs. maxsimpchain (x#xs@[y])"

context ChamberComplex
begin

abbreviation "chamber      \<equiv> maxsimp"
abbreviation "gallery      \<equiv> maxsimpchain"
abbreviation "pgallery     \<equiv> pmaxsimpchain"
abbreviation "min_gallery  \<equiv> min_maxsimpchain"
abbreviation "supchamber v \<equiv> (SOME C. chamber C \<and> v\<in>C)"

lemmas faces                     = faces
lemmas singleton_simplex         = singleton_simplex
lemmas chamberI                  = maxsimpI
lemmas chamberD_simplex          = maxsimpD_simplex
lemmas chamberD_maximal          = maxsimpD_maximal
lemmas finite_chamber            = finite_maxsimp
lemmas chamber_nempty            = maxsimp_nempty
lemmas chamber_vertices          = maxsimp_vertices
lemmas gallery_def               = maxsimpchain_def
lemmas gallery_snocI             = maxsimpchain_snocI
lemmas galleryD_chamber          = maxsimpchainD_maxsimp
lemmas galleryD_adj              = maxsimpchainD_adj
lemmas gallery_CConsI            = maxsimpchain_CConsI
lemmas gallery_Cons_reduce       = maxsimpchain_Cons_reduce
lemmas gallery_append_reduce1    = maxsimpchain_append_reduce1
lemmas gallery_append_reduce2    = maxsimpchain_append_reduce2
lemmas gallery_remdup_adj        = maxsimpchain_remdup_adj
lemmas gallery_obtain_pgallery   = maxsimpchain_obtain_pmaxsimpchain
lemmas pgallery_def              = pmaxsimpchain_def
lemmas pgalleryI_gallery         = pmaxsimpchainI_maxsimpchain
lemmas pgalleryD_chamber         = pmaxsimpchainD_maxsimp
lemmas pgalleryD_adj             = pmaxsimpchainD_adj
lemmas pgalleryD_distinct        = pmaxsimpchainD_distinct
lemmas pgallery_Cons_reduce      = pmaxsimpchain_Cons_reduce
lemmas pgallery_append_reduce1   = pmaxsimpchain_append_reduce1
lemmas pgallery                  = pmaxsimpchain
lemmas min_gallery_simps         = min_maxsimpchain.simps
lemmas min_galleryI_betw         = min_maxsimpchainI_betw
lemmas min_galleryI_betw_compare = min_maxsimpchainI_betw_compare
lemmas min_galleryD_min_betw     = min_maxsimpchainD_min_betw
lemmas min_galleryD_gallery      = min_maxsimpchainD_maxsimpchain
lemmas min_gallery_pgallery      = min_maxsimpchain_pmaxsimpchain
lemmas min_gallery_rev           = min_maxsimpchain_rev
lemmas min_gallery_adj           = min_maxsimpchain_adj
lemmas not_min_galleryI_betw     = not_min_maxsimpchainI_betw

lemmas min_gallery_betw_CCons_reduce =
  min_maxsimpchain_betw_CCons_reduce
lemmas min_gallery_betw_uniform_length =
  min_maxsimpchain_betw_uniform_length
lemmas vertex_set_int = vertex_set_int[OF ChamberComplex.axioms(1)]

lemma chamber_pconnect:
  "\<lbrakk> x \<noteq> y; chamber x; chamber y \<rbrakk> \<Longrightarrow> \<exists>xs. pgallery (x#xs@[y])"
  using maxsimp_connect[of x y] gallery_obtain_pgallery[of x y] by fast

lemma supchamberD:
  assumes "v\<in>\<Union>X"
  defines "C \<equiv> supchamber v"
  shows   "chamber C" "v\<in>C"
  using   assms simplex_in_max someI[of "\<lambda>C. chamber C \<and> v\<in>C"]
  by      auto

definition
  "ChamberSubcomplex Y \<equiv> Y \<subseteq> X \<and> ChamberComplex Y \<and>
    (\<forall>C. ChamberComplex.chamber Y C \<longrightarrow> chamber C)"

lemma ChamberSubcomplexI:
  assumes "Y\<subseteq>X" "ChamberComplex Y"
          "\<And>y. ChamberComplex.chamber Y y \<Longrightarrow> chamber y"
  shows   "ChamberSubcomplex Y"
  using   assms ChamberSubcomplex_def
  by      fast

lemma ChamberSubcomplexD_sub: "ChamberSubcomplex Y \<Longrightarrow> Y \<subseteq> X"
  using ChamberSubcomplex_def by fast

lemma ChamberSubcomplexD_complex:
  "ChamberSubcomplex Y \<Longrightarrow> ChamberComplex Y"
  unfolding ChamberSubcomplex_def by fast

lemma chambersub_imp_sub: "ChamberSubcomplex Y \<Longrightarrow> Subcomplex Y"
  using ChamberSubcomplex_def ChamberComplex.axioms(1) by fast

lemma chamber_in_subcomplex:
  "\<lbrakk> ChamberSubcomplex Y; C \<in> Y; chamber C \<rbrakk> \<Longrightarrow>
    ChamberComplex.chamber Y C"
  using chambersub_imp_sub max_in_subcomplex by simp

lemma subcomplex_chamber:
  "ChamberSubcomplex Y \<Longrightarrow> ChamberComplex.chamber Y C \<Longrightarrow> chamber C"
  unfolding ChamberSubcomplex_def by fast

lemma gallery_in_subcomplex:
  "\<lbrakk> ChamberSubcomplex Y; set ys \<subseteq> Y; gallery ys \<rbrakk> \<Longrightarrow>
    ChamberComplex.gallery Y ys"
  using chambersub_imp_sub maxsimpchain_in_subcomplex by simp

lemma subcomplex_gallery:
  "ChamberSubcomplex Y \<Longrightarrow> ChamberComplex.gallery Y Cs \<Longrightarrow> gallery Cs"
  using ChamberSubcomplex_def gallery_def ChamberComplex.gallery_def
  by    fastforce

lemma subcomplex_pgallery:
  "ChamberSubcomplex Y \<Longrightarrow> ChamberComplex.pgallery Y Cs \<Longrightarrow> pgallery Cs"
  using ChamberSubcomplex_def pgallery_def ChamberComplex.pgallery_def
  by    fastforce

lemma min_gallery_in_subcomplex:
  assumes "ChamberSubcomplex Y" "min_gallery Cs" "set Cs \<subseteq> Y"
  shows   "ChamberComplex.min_gallery Y Cs"
proof (cases Cs rule: list_cases_Cons_snoc)
  case Nil with assms(1) show ?thesis
    using ChamberSubcomplexD_complex ChamberComplex.min_gallery_simps(1)
    by    fast
next
  case Single with assms show ?thesis
    using min_galleryD_gallery galleryD_chamber chamber_in_subcomplex
          ChamberComplex.min_gallery_simps(2) ChamberSubcomplexD_complex
    by    force
next
  case (Cons_snoc C Ds D)
  with assms show ?thesis
    using ChamberSubcomplexD_complex min_gallery_pgallery
          pgalleryD_distinct[of "C#Ds@[D]"] pgallery
          gallery_in_subcomplex[of Y] subcomplex_gallery
          min_galleryD_min_betw
          ChamberComplex.min_galleryI_betw[of Y]
    by    force
qed

lemma chamber_card: "chamber C \<Longrightarrow> chamber D \<Longrightarrow> card C = card D"
  using maxsimp_connect[of C D] galleryD_adj adjacentchain_card
  by    (cases "C=D") auto

lemma chamber_facet_is_chamber_facet:
  "\<lbrakk> chamber C; chamber D; z\<lhd>C; z\<subseteq>D \<rbrakk> \<Longrightarrow> z\<lhd>D"
  using finite_chamber finite_facetrel_card chamber_card[of C]
  by    (fastforce intro: facetrelI_cardSuc)

lemma chamber_adj:
  assumes "chamber C" "D\<in>X" "C \<sim> D"
  shows   "chamber D"
proof-
  from assms(2) obtain B where B: "chamber B" "D\<subseteq>B"
    using simplex_in_max by fast
  with assms(1,3) show ?thesis
    using chamber_card[of B] adjacent_card finite_chamber card_subset_eq[of B D]
    by    force
qed

lemma chambers_share_facet:
  assumes "chamber C" "chamber (insert v z)" "z\<lhd>C"
  shows   "z\<lhd>insert v z"
proof (rule facetrelI)
  from assms show "v\<notin>z"
    using finite_chamber[of C] finite_chamber[of "insert v z"] card_insert_if[of z v]
    by    (auto simp add: finite_facetrel_card chamber_card)
qed simp

lemma adjacentset_chamber: "chamber C \<Longrightarrow> D\<in>adjacentset C \<Longrightarrow> chamber D"
  using adjacentset_def chamber_adj by fast

lemma chamber_shared_facet: "\<lbrakk> chamber C; z\<lhd>C; D\<in>X; z\<lhd>D \<rbrakk> \<Longrightarrow> chamber D"
  by (fast intro: chamber_adj adjacentI)

lemma adjacentset_conv_facetchambersets:
  assumes "X \<noteq> {{}}" "chamber C"
  shows   "adjacentset C = (\<Union>v\<in>C. {D\<in>X. C-{v}\<lhd>D})"
proof (rule seteqI)
  fix D assume D: "D \<in> adjacentset C"
  show "D \<in> (\<Union>v\<in>C. {D\<in>X. C-{v}\<lhd>D})"
  proof (cases "D=C")
    case True with assms
    have "C \<noteq> {}" and "C \<in> X"
      using chamber_nempty chamberD_simplex by auto
    with True assms show ?thesis
      using facetrel_diff_vertex by fastforce
  next
    case False
    from D have D': "C\<sim>D" using adjacentsetD_adj by fast
    with False obtain v where v: "v\<notin>D" "C = insert v (C\<inter>D)"
      using adjacent_int_decomp by fast
    hence "C-{v} = C\<inter>D" by auto
    with D' False have "C-{v} \<lhd> D" using adjacent_int_facet2 by auto
    with assms(2) D v(2) show ?thesis using adjacentset_def by fast
  qed
next
  from assms(2)
    show  "\<And>D. D \<in> (\<Union>v\<in>C. {E\<in>X. C-{v}\<lhd>E}) \<Longrightarrow>
            D \<in> adjacentset C"
    using     facetrel_diff_vertex adjacentI
    unfolding adjacentset_def
    by        fastforce
qed

end (* context ChamberComplex *)


subsection \<open>The system of chambers and distance between chambers\<close>

text \<open>
  We now examine the system of all chambers in more detail, and explore the distance function on
  this system provided by lengths of minimal galleries.
\<close>

context ChamberComplex
begin

definition chamber_system :: "'a set set"
  where "chamber_system \<equiv> {C. chamber C}"
abbreviation "\<C> \<equiv> chamber_system"

definition chamber_distance :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat"
  where "chamber_distance C D =
          (if C=D then 0 else
            Suc (length (ARG_MIN length Cs. gallery (C#Cs@[D]))))"

definition closest_supchamber :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "closest_supchamber F D =
          (ARG_MIN (\<lambda>C. chamber_distance C D) C.
            chamber C \<and> F\<subseteq>C)"

definition "face_distance F D \<equiv> chamber_distance (closest_supchamber F D) D"

lemma chamber_system_simplices: "\<C> \<subseteq> X"
  using chamberD_simplex unfolding chamber_system_def by fast

lemma gallery_chamber_system: "gallery Cs \<Longrightarrow> set Cs \<subseteq> \<C>"
  using galleryD_chamber chamber_system_def by fast

lemmas pgallery_chamber_system = gallery_chamber_system[OF pgallery]

lemma chamber_distance_le:
  "gallery (C#Cs@[D]) \<Longrightarrow> chamber_distance C D \<le> Suc (length Cs)"
  using chamber_distance_def
        arg_min_nat_le[of "\<lambda>Cs. gallery (C#Cs@[D])" _ length]
  by    auto

lemma min_gallery_betw_chamber_distance:
  "min_gallery (C#Cs@[D]) \<Longrightarrow> chamber_distance C D = Suc (length Cs)"
  using chamber_distance_def[of C D] is_arg_min_size[of length _ Cs] by auto

lemma min_galleryI_chamber_distance_betw:
  "gallery (C#Cs@[D]) \<Longrightarrow> Suc (length Cs) = chamber_distance C D \<Longrightarrow>
    min_gallery (C#Cs@[D])"
  using chamber_distance_def chamber_distance_le min_galleryI_betw[of C D]
  by    fastforce

lemma gallery_least_length:
  assumes "chamber C" "chamber D" "C\<noteq>D"
  defines "Cs \<equiv> ARG_MIN length Cs. gallery (C#Cs@[D])"
  shows   "gallery (C#Cs@[D])"
  using   assms maxsimp_connect[of C D] arg_min_natI
  by      fast
  
lemma min_gallery_least_length:
  assumes   "chamber C" "chamber D" "C\<noteq>D"
  defines   "Cs \<equiv> ARG_MIN length Cs. gallery (C#Cs@[D])"
  shows     "min_gallery (C#Cs@[D])"
  unfolding Cs_def
  using     assms gallery_least_length
  by        (blast intro: min_galleryI_betw arg_min_nat_le)

lemma pgallery_least_length:
  assumes "chamber C" "chamber D" "C\<noteq>D"
  defines "Cs \<equiv> ARG_MIN length Cs. gallery (C#Cs@[D])"
  shows   "pgallery (C#Cs@[D])"
  using   assms min_gallery_least_length min_gallery_pgallery
  by      fast

lemma closest_supchamberD:
  assumes   "F\<in>X" "chamber D"
  shows     "chamber (closest_supchamber F D)" "F \<subseteq> closest_supchamber F D"
  using     assms arg_min_natI[of "\<lambda>C. chamber C \<and> F\<subseteq>C" ] simplex_in_max[of F]
  unfolding closest_supchamber_def
  by        auto

lemma closest_supchamber_closest:
  "chamber C \<Longrightarrow> F\<subseteq>C \<Longrightarrow>
    chamber_distance (closest_supchamber F D) D \<le> chamber_distance C D"
  using arg_min_nat_le[of "\<lambda>C. chamber C \<and> F\<subseteq>C" C] closest_supchamber_def
  by simp

lemma face_distance_le:
  "chamber C \<Longrightarrow> F\<subseteq>C \<Longrightarrow> face_distance F D \<le> chamber_distance C D"
  unfolding face_distance_def closest_supchamber_def
  by (auto intro: arg_min_nat_le)

lemma face_distance_eq_0: "chamber C \<Longrightarrow> F\<subseteq>C \<Longrightarrow> face_distance F C = 0"
  using chamber_distance_def closest_supchamber_def face_distance_def
        arg_min_equality[
          of "\<lambda>C. chamber C \<and> F\<subseteq>C" C "\<lambda>D. chamber_distance D C"
        ]
  by simp

end (* context ChamberComplex *)


subsection \<open>Labelling a chamber complex\<close>

text \<open>
  A labelling of a chamber complex is a function on the vertex set so that each chamber is in
  bijective correspondence with the label set (chambers all have the same number of vertices).
\<close>

context ChamberComplex
begin

definition label_wrt :: "'b set \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool"
  where "label_wrt B f \<equiv> (\<forall>C\<in>\<C>. bij_betw f C B)"

lemma label_wrtD: "label_wrt B f \<Longrightarrow> C\<in>\<C> \<Longrightarrow> bij_betw f C B"
  using label_wrt_def by fast

lemma label_wrtD': "label_wrt B f \<Longrightarrow> chamber C \<Longrightarrow> bij_betw f C B"
  using label_wrt_def chamber_system_def by fast

lemma label_wrt_adjacent:
  assumes "label_wrt B f" "chamber C" "chamber D" "C\<sim>D" "v\<in>C-D" "w\<in>D-C"
  shows   "f v = f w"
proof-
  from assms(5) have "f`D = insert (f v) (f`(C\<inter>D))"
    using adjacent_conv_insert[OF assms(4), of v] label_wrtD'[OF assms(1,2)]
          label_wrtD'[OF assms(1,3)]
          bij_betw_imp_surj_on[of f]
    by    force
  with assms(6) show ?thesis
    using adjacent_sym[OF assms(4)] adjacent_conv_insert[of D C]
          inj_on_insert[of f w "C\<inter>D"]
          bij_betw_imp_inj_on[OF label_wrtD', OF assms(1,3)]
    by    (force simp add: Int_commute)
qed

lemma label_wrt_adjacent_shared_facet:
  "\<lbrakk> label_wrt B f; chamber (insert v z); chamber (insert w z); v\<notin>z; w\<notin>z \<rbrakk> \<Longrightarrow>
    f v = f w"
  by (auto intro: label_wrt_adjacent adjacentI facetrelI)

lemma label_wrt_elt_image: "label_wrt B f \<Longrightarrow> v\<in>\<Union>X \<Longrightarrow> f v \<in> B"
  using simplex_in_max label_wrtD' bij_betw_imp_surj_on by fast

end (* context ChamberComplex *)


subsection \<open>Morphisms of chamber complexes\<close>

text \<open>
  While any function on the vertex set of a simplicial complex can be considered a morphism of
  simplicial complexes onto its image, for chamber complexes we require the function send chambers
  onto chambers of the same cardinality in some chamber complex of the codomain.
\<close>

subsubsection \<open>Morphism locale and basic facts\<close>

locale ChamberComplexMorphism = domain: ChamberComplex X + codomain: ChamberComplex Y
  for     X :: "'a set set"
  and     Y :: "'b set set"
+ fixes   f :: "'a\<Rightarrow>'b"
  assumes chamber_map:  "domain.chamber C \<Longrightarrow> codomain.chamber (f`C)"
  and     dim_map    :  "domain.chamber C \<Longrightarrow> card (f`C) = card C"

lemma (in ChamberComplex) trivial_morphism:
  "ChamberComplexMorphism X X id"
  by unfold_locales auto

lemma (in ChamberComplex) inclusion_morphism:
  assumes "ChamberSubcomplex Y"
  shows   "ChamberComplexMorphism Y X id"
  by      (
            rule ChamberComplexMorphism.intro,
            rule ChamberSubcomplexD_complex,
            rule assms, unfold_locales
          )
          (auto simp add: subcomplex_chamber[OF assms])

context ChamberComplexMorphism
begin

lemmas domain_complex = domain.ChamberComplex_axioms
lemmas codomain_complex = codomain.ChamberComplex_axioms

lemmas simplicialcomplex_image = domain.map_is_simplicial_morph[of f]

lemma cong: "fun_eq_on g f (\<Union>X) \<Longrightarrow> ChamberComplexMorphism X Y g"
  using chamber_map domain.chamber_vertices fun_eq_on_im[of g f] dim_map
        domain.chamber_vertices
  by    unfold_locales auto

lemma comp:
  assumes "ChamberComplexMorphism Y Z g"
  shows   "ChamberComplexMorphism X Z (g\<circ>f)"
proof (
  rule ChamberComplexMorphism.intro, rule domain_complex,
  rule ChamberComplexMorphism.axioms(2), rule assms, unfold_locales
)
  fix C assume C: "domain.chamber C"
  from C show "SimplicialComplex.maxsimp Z ((g\<circ>f)`C)"
    using chamber_map ChamberComplexMorphism.chamber_map[OF assms]
    by    (force simp add: image_comp[THEN sym])
  from C show "card ((g \<circ> f)`C) = card C"
    using chamber_map dim_map ChamberComplexMorphism.dim_map[OF assms]
    by    (force simp add: image_comp[THEN sym])
qed

lemma restrict_domain:
  assumes "domain.ChamberSubcomplex W"
  shows   "ChamberComplexMorphism W Y f"
proof (
  rule ChamberComplexMorphism.intro, rule domain.ChamberSubcomplexD_complex,
  rule assms, rule codomain_complex, unfold_locales
)
  fix C assume "ChamberComplex.chamber W C"
  with assms show "codomain.chamber (f`C)" "card (f`C) = card C"
    using domain.subcomplex_chamber chamber_map dim_map by auto
qed

lemma restrict_codomain:
  assumes "codomain.ChamberSubcomplex Z" "f\<turnstile>X \<subseteq> Z"
  shows   "ChamberComplexMorphism X Z f"
proof (
  rule ChamberComplexMorphism.intro, rule domain_complex,
  rule codomain.ChamberSubcomplexD_complex,
  rule assms, unfold_locales
)
  fix C assume "domain.chamber C"
  with assms show "SimplicialComplex.maxsimp Z (f`C)" "card (f ` C) = card C"
    using domain.chamberD_simplex[of C] chamber_map
          codomain.chamber_in_subcomplex dim_map
    by    auto
qed

lemma inj_on_chamber: "domain.chamber C \<Longrightarrow> inj_on f C"
  using domain.finite_chamber dim_map by (fast intro: eq_card_imp_inj_on)

lemma bij_betw_chambers: "domain.chamber C \<Longrightarrow> bij_betw f C (f`C)"
  using inj_on_chamber by (fast intro: bij_betw_imageI)

lemma card_map: "x\<in>X \<Longrightarrow> card (f`x) = card x"
  using domain.simplex_in_max subset_inj_on[OF inj_on_chamber]
        domain.finite_simplex inj_on_iff_eq_card
  by    blast

lemma codim_map:
  assumes "domain.chamber C" "y \<subseteq> C"
  shows   "card (f`C - f`y) = card (C-y)"
  using   assms dim_map domain.chamberD_simplex domain.faces[of C y]
          domain.finite_simplex card_Diff_subset[of "f`y" "f`C"]
          card_map card_Diff_subset[of y C]
  by      auto

lemma simplex_map: "x\<in>X \<Longrightarrow> f`x\<in>Y"
  using chamber_map domain.simplex_in_max codomain.chamberD_simplex
        codomain.faces[of _ "f`x"]
  by    force

lemma simplices_map: "f\<turnstile>X \<subseteq> Y"
  using simplex_map by fast

lemma vertex_map: "x \<in> \<Union>X \<Longrightarrow> f x \<in> \<Union>Y"
  using simplex_map by fast

lemma facet_map: "domain.chamber C \<Longrightarrow> z\<lhd>C \<Longrightarrow> f`z \<lhd> f`C"
  using facetrel_subset facetrel_card codim_map[of C z]
  by    (fastforce intro: facetrelI_card)

lemma adj_int_im:
  assumes "domain.chamber C" "domain.chamber D" "C \<sim> D" "f`C \<noteq> f`D"
  shows   "(f`C \<inter> f`D) \<lhd> f`C"
proof (rule facetrelI_card)
  from assms(1,2) chamber_map have 1: "f`C \<subseteq> f`D \<Longrightarrow> f`C = f`D"
    using codomain.chamberD_simplex codomain.chamberD_maximal[of "f`C" "f`D"]
    by    simp
  thus "f ` C \<inter> f ` D \<subseteq> f ` C" by fast

  from assms(1) have "card (f`C - f`C \<inter> f`D) \<le> card (f`C - f`(C\<inter>D))"
    using domain.finite_chamber
          card_mono[of "f`C - f`(C\<inter>D)" "f`C - f`C \<inter> f`D"]
    by    fast
  moreover from assms(1,3,4) have "card (f`C - f`(C\<inter>D)) = 1"
    using codim_map[of C "C\<inter>D"] adjacent_int_facet1 facetrel_card
    by    fastforce
  ultimately have "card (f`C - f`C \<inter> f`D) \<le> 1" by simp
  moreover from 1 assms(1,4) have "card (f`C - f`C \<inter> f`D) \<noteq> 0"
    using domain.finite_chamber by auto
  ultimately show "card (f`C - f`C \<inter> f`D) = 1" by simp
qed

lemma adj_map':
  assumes "domain.chamber C" "domain.chamber D" "C \<sim> D" "f`C \<noteq> f`D"
  shows   "f`C \<sim> f`D"
  using   assms(3,4) adj_int_im[OF assms] adjacent_sym
          adj_int_im[OF assms(2) assms(1)]
  by      (auto simp add: Int_commute intro: adjacentI)

lemma adj_map:
  "\<lbrakk> domain.chamber C; domain.chamber D; C \<sim> D \<rbrakk> \<Longrightarrow> f`C \<sim> f`D"
  using adjacent_refl[of "f`C"] adj_map' empty_not_adjacent[of D] by fastforce

lemma chamber_vertex_outside_facet_image:
  assumes "v\<notin>z" "domain.chamber (insert v z)"
  shows   "f v \<notin> f`z"
proof-
  from assms(1) have "insert v z - z = {v}" by force
  with assms(2) show ?thesis using codim_map by fastforce
qed

lemma expand_codomain:
  assumes "ChamberComplex Z" "ChamberComplex.ChamberSubcomplex Z Y"
  shows   "ChamberComplexMorphism X Z f"
proof (
  rule ChamberComplexMorphism.intro, rule domain_complex, rule assms(1),
  unfold_locales
)
  from assms show
    "\<And>x. domain.chamber x \<Longrightarrow> SimplicialComplex.maxsimp Z (f ` x)"
    using chamber_map ChamberComplex.subcomplex_chamber by fast
qed (auto simp add: dim_map)

end (* context ChamberComplexMorphism *)

subsubsection \<open>Action on pregalleries and galleries\<close>

context ChamberComplexMorphism
begin

lemma gallery_map: "domain.gallery Cs \<Longrightarrow> codomain.gallery (f\<Turnstile>Cs)"
proof (induct Cs rule: list_induct_CCons)
  case (Single C) thus ?case
    using domain.galleryD_chamber chamber_map codomain.gallery_def by auto
next
  case (CCons B C Cs)
  have "codomain.gallery (f`B # f`C # f\<Turnstile>Cs)"
  proof (rule codomain.gallery_CConsI)
    from CCons(2) show "codomain.chamber (f ` B)"
      using domain.galleryD_chamber chamber_map by simp
    from CCons show "codomain.gallery (f`C # f\<Turnstile>Cs)"
      using domain.gallery_Cons_reduce by auto
    from CCons(2) show "f`B \<sim>  f`C"
      using domain.gallery_Cons_reduce[of B "C#Cs"] domain.galleryD_adj
            domain.galleryD_chamber adj_map
      by    fastforce
  qed
  thus ?case by simp
qed (simp add: codomain.maxsimpchain_def)

lemma gallery_betw_map:
  "domain.gallery (C#Cs@[D]) \<Longrightarrow> codomain.gallery (f`C # f\<Turnstile>Cs @ [f`D])"
  using gallery_map by fastforce

end (* context ChamberComplexMorphism *)


subsubsection \<open>Properties of the image\<close>

context ChamberComplexMorphism
begin

lemma subcomplex_image: "codomain.Subcomplex (f\<turnstile>X)"
  using simplicialcomplex_image simplex_map by fast

lemmas chamber_in_image = codomain.max_in_subcomplex[OF subcomplex_image]

lemma maxsimp_map_into_image:
  assumes "domain.chamber x"
  shows   "SimplicialComplex.maxsimp (f\<turnstile>X) (f`x)"
proof (
  rule SimplicialComplex.maxsimpI, rule simplicialcomplex_image, rule imageI,
  rule domain.chamberD_simplex, rule assms
)
  from assms show "\<And>z. z\<in>f\<turnstile>X \<Longrightarrow> f`x \<subseteq> z \<Longrightarrow> z = f`x"
    using chamber_map[of x] simplex_map codomain.chamberD_maximal[of "f`x"]
    by    blast
qed

lemma maxsimp_preimage:
  assumes "C\<in>X" "SimplicialComplex.maxsimp (f\<turnstile>X) (f`C)"
  shows "domain.chamber C"
proof-
  from assms(1) obtain D where D: "domain.chamber D" "C\<subseteq>D"
    using domain.simplex_in_max by fast
  have "C=D"
  proof (rule card_subset_eq)
    from D(1) show "finite D" using domain.finite_chamber by fast
    with assms D show "card C = card D"
      using domain.chamberD_simplex simplicialcomplex_image
            SimplicialComplex.maxsimpD_maximal[of "f\<turnstile>X" "f`C" "f`D"]
            card_mono[of D C] domain.finite_simplex card_image_le[of C f] dim_map
      by    force
  qed (rule D(2))
  with D(1) show ?thesis by fast
qed

lemma chamber_preimage:
  "C\<in>X \<Longrightarrow> codomain.chamber (f`C) \<Longrightarrow> domain.chamber C"
  using chamber_in_image maxsimp_preimage by simp

lemma chambercomplex_image: "ChamberComplex (f\<turnstile>X)"
proof (intro_locales, rule simplicialcomplex_image, unfold_locales)
  show "\<And>y. y\<in>f\<turnstile>X \<Longrightarrow> \<exists>x. SimplicialComplex.maxsimp (f\<turnstile>X) x \<and> y \<subseteq> x"
    using domain.simplex_in_max maxsimp_map_into_image by fast
next
  fix x y
  assume xy:  "x\<noteq>y" "SimplicialComplex.maxsimp (f\<turnstile>X) x"
              "SimplicialComplex.maxsimp (f\<turnstile>X) y"
  from xy(2,3) obtain zx zy where zxy: "zx\<in>X" "x = f`zx" "zy\<in>X" "y = f`zy "
    using SimplicialComplex.maxsimpD_simplex[OF simplicialcomplex_image, of x]
          SimplicialComplex.maxsimpD_simplex[OF simplicialcomplex_image, of y]
    by    fast
  with xy obtain ws where ws: "domain.gallery (zx#ws@[zy])"
    using maxsimp_preimage domain.maxsimp_connect[of zx zy] by auto
  with ws zxy(2,4) have "SimplicialComplex.maxsimpchain (f\<turnstile>X) (x#(f\<Turnstile>ws)@[y])"
    using gallery_map[of "zx#ws@[zy]"] domain.galleryD_chamber
          domain.chamberD_simplex codomain.galleryD_chamber
          codomain.max_in_subcomplex[OF subcomplex_image]
          codomain.galleryD_adj
          SimplicialComplex.maxsimpchain_def[OF simplicialcomplex_image]
    by    auto
  thus "\<exists>xs. SimplicialComplex.maxsimpchain (f\<turnstile>X) (x#xs@[y])" by fast
qed

lemma chambersubcomplex_image: "codomain.ChamberSubcomplex (f\<turnstile>X)"
  using simplices_map chambercomplex_image ChamberComplex.chamberD_simplex
        chambercomplex_image maxsimp_preimage chamber_map
  by    (force intro: codomain.ChamberSubcomplexI)

lemma restrict_codomain_to_image: "ChamberComplexMorphism X (f\<turnstile>X) f"
  using restrict_codomain chambersubcomplex_image by fast

end (* context ChamberComplexMorphism *)


subsubsection \<open>Action on the chamber system\<close>

context ChamberComplexMorphism
begin

lemma chamber_system_into: "f\<turnstile>domain.\<C> \<subseteq> codomain.\<C>"
  using chamber_map domain.chamber_system_def codomain.chamber_system_def
  by    auto

lemma chamber_system_image: "f\<turnstile>domain.\<C> = codomain.\<C> \<inter> (f\<turnstile>X)"
proof
  show "f\<turnstile>domain.\<C> \<subseteq> codomain.\<C> \<inter> (f\<turnstile>X)"
    using chamber_system_into domain.chamber_system_simplices by fast
  show "f\<turnstile>domain.\<C> \<supseteq> codomain.\<C> \<inter> (f\<turnstile>X)"
  proof
    fix D assume "D \<in> codomain.\<C> \<inter> (f\<turnstile>X)"
    hence "\<exists>C. domain.chamber C \<and> f`C = D"
      using codomain.chamber_system_def chamber_preimage by fast
    thus "D \<in> f\<turnstile>domain.\<C>" using domain.chamber_system_def by auto
  qed
qed

lemma image_chamber_system: "ChamberComplex.\<C> (f\<turnstile>X) = f \<turnstile> domain.\<C>"
  using ChamberComplex.chamber_system_def codomain.subcomplex_chamber
        ChamberComplex.chamberD_simplex chambercomplex_image
        chambersubcomplex_image chamber_system_image
        codomain.chamber_in_subcomplex codomain.chamber_system_def
  by    auto

lemma image_chamber_system_image:
  "ChamberComplex.\<C> (f\<turnstile>X) = codomain.\<C> \<inter> (f\<turnstile>X)"
  using image_chamber_system chamber_system_image by simp

lemma face_distance_eq_chamber_distance_map:
  assumes "domain.chamber C" "domain.chamber D" "C\<noteq>D" "z\<subseteq>C"
          "codomain.face_distance (f`z) (f`D) = domain.face_distance z D"
          "domain.face_distance z D = domain.chamber_distance C D"
  shows   "codomain.face_distance (f`z) (f`D) =
            codomain.chamber_distance (f`C) (f`D)"
  using   assms codomain.face_distance_le[of "f`C" "f`z" "f`D"] chamber_map
          codomain.chamber_distance_le
          gallery_betw_map[OF domain.gallery_least_length, of C D]
          domain.chamber_distance_def
  by      force

lemma face_distance_eq_chamber_distance_min_gallery_betw_map:
  assumes "domain.chamber C" "domain.chamber D" "C\<noteq>D" "z\<subseteq>C"
          "codomain.face_distance (f`z) (f`D) = domain.face_distance z D"
          "domain.face_distance z D = domain.chamber_distance C D"
          "domain.min_gallery (C#Cs@[D])"
  shows   "codomain.min_gallery (f\<Turnstile>(C#Cs@[D]))"
  using   assms face_distance_eq_chamber_distance_map[of C D z]
          gallery_map[OF domain.min_galleryD_gallery, OF assms(7)]
          domain.min_gallery_betw_chamber_distance[OF assms(7)] 
          codomain.min_galleryI_chamber_distance_betw[of "f`C" "f\<Turnstile>Cs" "f`D"]
  by      auto

end (* context ChamberComplexMorphism *)


subsubsection \<open>Isomorphisms\<close>

locale ChamberComplexIsomorphism = ChamberComplexMorphism X Y f
  for X  :: "'a set set"
  and Y  :: "'b set set"
  and f  :: "'a\<Rightarrow>'b"
+ assumes bij_betw_vertices: "bij_betw f (\<Union>X) (\<Union>Y)"
  and     surj_simplex_map : "f\<turnstile>X = Y"

lemma (in ChamberComplexIsomorphism) inj: "inj_on f (\<Union>X)"
  using bij_betw_vertices bij_betw_def by fast

sublocale ChamberComplexIsomorphism < SimplicialComplexIsomorphism
  using inj by (unfold_locales) fast

lemma (in ChamberComplex) trivial_isomorphism:
  "ChamberComplexIsomorphism X X id"
  using trivial_morphism bij_betw_id
  by    unfold_locales (auto intro: ChamberComplexIsomorphism.intro)

lemma (in ChamberComplexMorphism) isoI_inverse:
  assumes "ChamberComplexMorphism Y X g"
          "fixespointwise (g\<circ>f) (\<Union>X)" "fixespointwise (f\<circ>g) (\<Union>Y)"
  shows   "ChamberComplexIsomorphism X Y f"
proof (rule ChamberComplexIsomorphism.intro)
  show "ChamberComplexMorphism X Y f" ..
  show "ChamberComplexIsomorphism_axioms X Y f"
  proof
    from assms show "bij_betw f (\<Union>X) (\<Union>Y)"
      using vertex_map ChamberComplexMorphism.vertex_map
            comps_fixpointwise_imp_bij_betw[of f "\<Union>X" "\<Union>Y" g]
      by    fast
    show "f\<turnstile>X = Y"
    proof (rule order.antisym, rule simplices_map, rule subsetI)
      fix y assume "y\<in>Y"
      moreover hence "(f\<circ>g) ` y \<in> f\<turnstile>X"
        using ChamberComplexMorphism.simplex_map[OF assms(1)]
        by    (simp add: image_comp[THEN sym])
      ultimately show "y \<in> f\<turnstile>X" 
        using fixespointwise_subset[OF assms(3), of y] fixespointwise_im by fastforce
    qed
  qed
qed

context ChamberComplexIsomorphism
begin

lemmas domain_complex   = domain_complex
lemmas chamber_map      = chamber_map
lemmas dim_map          = dim_map
lemmas gallery_map      = gallery_map
lemmas simplex_map      = simplex_map
lemmas chamber_preimage = chamber_preimage

lemma chamber_morphism: "ChamberComplexMorphism X Y f" ..

lemma pgallery_map: "domain.pgallery Cs \<Longrightarrow> codomain.pgallery (f\<Turnstile>Cs)"
  using pmaxsimpchain_map surj_simplex_map by simp

lemma iso_cong:
  assumes "fun_eq_on g f (\<Union>X)"
  shows   "ChamberComplexIsomorphism X Y g"
proof (
  rule ChamberComplexIsomorphism.intro, rule cong, rule assms,
  unfold_locales
)
  from assms show "bij_betw g (\<Union>X) (\<Union>Y)"
    using bij_betw_vertices fun_eq_on_bij_betw by blast
  show "g \<turnstile> X = Y" using setsetmapim_cong[OF assms] surj_simplex_map by simp
qed

lemma iso_comp:
  assumes "ChamberComplexIsomorphism Y Z g"
  shows   "ChamberComplexIsomorphism X Z (g\<circ>f)"
  by      (
            rule ChamberComplexIsomorphism.intro, rule comp,
            rule ChamberComplexIsomorphism.axioms(1),
            rule assms, unfold_locales, rule bij_betw_trans,
            rule bij_betw_vertices,
            rule ChamberComplexIsomorphism.bij_betw_vertices,
            rule assms
          )
          (simp add:
            setsetmapim_comp surj_simplex_map assms
            ChamberComplexIsomorphism.surj_simplex_map
          )

lemma inj_on_chamber_system: "inj_on ((`) f) domain.\<C>"
proof (rule inj_onI)
  fix C D show "\<lbrakk> C \<in> domain.\<C>; D \<in> domain.\<C>; f`C = f`D \<rbrakk> \<Longrightarrow> C=D"
    using domain.chamber_system_def domain.chamber_pconnect[of C D]
          pgallery_map codomain.pgalleryD_distinct
    by    fastforce
qed

lemma inv: "ChamberComplexIsomorphism Y X (the_inv_into (\<Union>X) f)"
proof
  show "bij_betw (the_inv_into (\<Union>X) f) (\<Union>Y) (\<Union>X)"
    using bij_betw_vertices bij_betw_the_inv_into by fast
  show 4: "(the_inv_into (\<Union>X) f) \<turnstile> Y = X"
    using bij_betw_imp_inj_on[OF bij_betw_vertices] surj_simplex_map
          setsetmapim_the_inv_into
    by    force
next
  fix C assume C: "codomain.chamber C"
  hence C': "C\<in>f\<turnstile>X" using codomain.chamberD_simplex surj_simplex_map by fast
  show "domain.chamber (the_inv_into (\<Union>X) f ` C)"
  proof (rule domain.chamberI)
    from C' obtain D where "D\<in>X" "the_inv_into (\<Union>X) f ` C = D"
      using the_inv_into_f_im_f_im[OF inj] by blast
    thus "the_inv_into (\<Union>X) f ` C \<in> X" by simp
    fix z assume z: "z\<in>X" "the_inv_into (\<Union>X) f ` C \<subseteq> z"
    with C have "f`z = C"
      using C' f_im_the_inv_into_f_im[OF inj, of C] surj_simplex_map
            codomain.chamberD_maximal[of C "f`z"]
      by    blast
    with z(1) show "z = the_inv_into (\<Union>X) f ` C"
      using the_inv_into_f_im_f_im[OF inj] by auto
  qed
  from C show "card (the_inv_into (\<Union>X) f ` C) = card C"
    using C' codomain.finite_chamber
          subset_inj_on[OF inj_on_the_inv_into, OF inj, of C]
    by    (fast intro: inj_on_iff_eq_card[THEN iffD1])
qed

lemma chamber_distance_map:
  assumes "domain.chamber C" "domain.chamber D"
  shows   "codomain.chamber_distance (f`C) (f`D) =
            domain.chamber_distance C D"
proof (cases "f`C=f`D")
  case True
  moreover with assms have "C=D"
    using inj_onD[OF inj_on_chamber_system] domain.chamber_system_def
    by    simp
  ultimately show ?thesis
    using domain.chamber_distance_def codomain.chamber_distance_def by simp
next  
  case False
  define Cs Ds where "Cs = (ARG_MIN length Cs. domain.gallery (C#Cs@[D]))"
    and "Ds = (ARG_MIN length Ds. codomain.gallery (f`C # Ds @ [f`D]))"
  from assms False Cs_def have "codomain.gallery (f`C # f\<Turnstile>Cs @ [f`D])"
    using gallery_map domain.maxsimp_connect[of C D]
          arg_min_natI[of "\<lambda>Cs. domain.gallery (C#Cs@[D])"]
    by    fastforce
  moreover from assms Cs_def
    have  "\<And>Es. codomain.gallery (f`C # Es @ [f`D]) \<Longrightarrow>
            length (f\<Turnstile>Cs) \<le> length Es"
    using ChamberComplexIsomorphism.gallery_map[OF inv]
          the_inv_into_f_im_f_im[OF inj, of C] the_inv_into_f_im_f_im[OF inj, of D]
          domain.chamberD_simplex[of C] domain.chamberD_simplex[of D]
          domain.maxsimp_connect[of C D]
          arg_min_nat_le[of "\<lambda>Cs. domain.gallery (C#Cs@[D])" _ length]
    by    force
  ultimately have "length Ds = length (f\<Turnstile>Cs)"
    unfolding Ds_def by (fast intro: arg_min_equality)
  with False Cs_def Ds_def show ?thesis
    using domain.chamber_distance_def codomain.chamber_distance_def by auto
qed

lemma face_distance_map:
  assumes "domain.chamber C" "F\<in>X"
  shows   "codomain.face_distance (f`F) (f`C) = domain.face_distance F C"
proof-
  define D D' invf where "D = domain.closest_supchamber F C"
    and "D' = codomain.closest_supchamber (f`F) (f`C)"
    and "invf = the_inv_into (\<Union>X) f"

  from assms D_def D'_def invf_def have chambers:
    "codomain.chamber (f`C)" "domain.chamber D" "codomain.chamber D'"
    "codomain.chamber (f`D)" "domain.chamber (invf`D')"
    using domain.closest_supchamberD(1) simplex_map
          codomain.closest_supchamberD(1) chamber_map
          ChamberComplexIsomorphism.chamber_map[OF inv]
    by    auto

  have "codomain.chamber_distance D' (f`C) \<le> domain.chamber_distance D C"
  proof-
    from assms D_def D'_def
      have  "codomain.chamber_distance D' (f`C) \<le>
              codomain.chamber_distance (f`D) (f`C)"
      using chambers(4) domain.closest_supchamberD(2)
            codomain.closest_supchamber_def
      by    (fastforce intro: arg_min_nat_le)
    with assms D_def D'_def show ?thesis
      using chambers(2) chamber_distance_map by simp
  qed
  moreover
    have "domain.chamber_distance D C \<le> codomain.chamber_distance D' (f`C)"
  proof-
    from assms D'_def have "invf`f`F \<subseteq> invf`D'"
      using chambers(1) simplex_map codomain.closest_supchamberD(2) by fast
    with assms(2) invf_def have "F \<subseteq> invf`D'"
      using the_inv_into_f_im_f_im[OF inj, of F] by fastforce
    with D_def
      have  "domain.chamber_distance D C \<le>
              domain.chamber_distance (invf ` D') C"
      using chambers(5) domain.closest_supchamber_def
      by    (auto intro: arg_min_nat_le)
    with assms(1) invf_def show ?thesis
      using chambers(3,5) surj_simplex_map codomain.chamberD_simplex
            f_im_the_inv_into_f_im[OF inj, of D']
            chamber_distance_map[of "invf`D'" C]
      by    fastforce
  qed
  ultimately show ?thesis
    using D_def D'_def domain.face_distance_def codomain.face_distance_def
    by    simp
qed

end (* context ChamberComplexIsomorphism *)

subsubsection \<open>Endomorphisms\<close>

locale ChamberComplexEndomorphism = ChamberComplexMorphism X X f
  for X :: "'a set set"
  and f :: "'a\<Rightarrow>'a"
+ assumes trivial_outside : "v\<notin>\<Union>X \<Longrightarrow> f v = v"
  \<comment> \<open>to facilitate uniqueness arguments\<close>

lemma (in ChamberComplex) trivial_endomorphism:
  "ChamberComplexEndomorphism X id"
  by  (
        rule ChamberComplexEndomorphism.intro, rule trivial_morphism,
        unfold_locales
      )
      simp

context ChamberComplexEndomorphism
begin

abbreviation "ChamberSubcomplex \<equiv> domain.ChamberSubcomplex"
abbreviation "Subcomplex \<equiv> domain.Subcomplex"
abbreviation "chamber \<equiv> domain.chamber"
abbreviation "gallery \<equiv> domain.gallery"
abbreviation "\<C> \<equiv> domain.chamber_system"
abbreviation "label_wrt \<equiv> domain.label_wrt"

lemmas dim_map                 = dim_map
lemmas simplex_map             = simplex_map
lemmas vertex_map              = vertex_map
lemmas chamber_map             = chamber_map
lemmas adj_map                 = adj_map
lemmas facet_map               = facet_map
lemmas bij_betw_chambers       = bij_betw_chambers
lemmas chamber_system_into     = chamber_system_into
lemmas chamber_system_image    = chamber_system_image
lemmas image_chamber_system    = image_chamber_system
lemmas chambercomplex_image    = chambercomplex_image
lemmas chambersubcomplex_image = chambersubcomplex_image

lemmas face_distance_eq_chamber_distance_map =
  face_distance_eq_chamber_distance_map
lemmas face_distance_eq_chamber_distance_min_gallery_betw_map =
  face_distance_eq_chamber_distance_min_gallery_betw_map
lemmas facedist_chdist_mingal_btwmap =
  face_distance_eq_chamber_distance_min_gallery_betw_map

lemmas trivial_endomorphism     = domain.trivial_endomorphism
lemmas finite_simplices         = domain.finite_simplices
lemmas faces                    = domain.faces
lemmas maxsimp_connect          = domain.maxsimp_connect
lemmas simplex_in_max           = domain.simplex_in_max
lemmas chamberD_simplex         = domain.chamberD_simplex
lemmas chamber_system_def       = domain.chamber_system_def
lemmas chamber_system_simplices = domain.chamber_system_simplices
lemmas galleryD_chamber         = domain.galleryD_chamber
lemmas galleryD_adj             = domain.galleryD_adj
lemmas gallery_append_reduce1   = domain.gallery_append_reduce1
lemmas gallery_Cons_reduce      = domain.gallery_Cons_reduce
lemmas gallery_chamber_system   = domain.gallery_chamber_system
lemmas label_wrtD               = domain.label_wrtD
lemmas label_wrt_adjacent       = domain.label_wrt_adjacent

lemma endo_comp:
  assumes "ChamberComplexEndomorphism X g"
  shows   "ChamberComplexEndomorphism X (g\<circ>f)"
proof (rule ChamberComplexEndomorphism.intro)
  from assms show "ChamberComplexMorphism X X (g\<circ>f)"
    using comp ChamberComplexEndomorphism.axioms by fast
  from assms show "ChamberComplexEndomorphism_axioms X (g\<circ>f)"
    using trivial_outside ChamberComplexEndomorphism.trivial_outside
    by    unfold_locales auto
qed

lemma restrict_endo:
  assumes "ChamberSubcomplex Y" "f\<turnstile>Y \<subseteq> Y"
  shows   "ChamberComplexEndomorphism Y (restrict1 f (\<Union>Y))"
proof (rule ChamberComplexEndomorphism.intro)
  from assms show "ChamberComplexMorphism Y Y (restrict1 f (\<Union>Y))"
    using ChamberComplexMorphism.cong[of Y Y]
          ChamberComplexMorphism.restrict_codomain
          restrict_domain fun_eq_on_restrict1
    by    fast
  show "ChamberComplexEndomorphism_axioms Y (restrict1 f (\<Union>Y))"
    by unfold_locales simp
qed

lemma funpower_endomorphism:
  "ChamberComplexEndomorphism X (f^^n)"
proof (induct n)
  case 0 show ?case using trivial_endomorphism subst[of id] by fastforce
next
  case (Suc m)
  hence "ChamberComplexEndomorphism X (f^^m \<circ> f)"
    using endo_comp by auto
  moreover have "f^^m \<circ> f = f^^(Suc m)"
    by (simp add: funpow_Suc_right[THEN sym])
  ultimately show ?case
    using subst[of _ _ "\<lambda>f. ChamberComplexEndomorphism X f"] by fast
qed

end (* context ChamberComplexEndomorphism *)

lemma (in ChamberComplex) fold_chamber_complex_endomorph_list:
  "\<forall>x\<in>set xs. ChamberComplexEndomorphism X (f x) \<Longrightarrow>
    ChamberComplexEndomorphism X (fold f xs)"
proof (induct xs)
  case Nil show ?case using trivial_endomorphism subst[of id] by fastforce
next
  case (Cons x xs)
  hence "ChamberComplexEndomorphism X (fold f xs \<circ> f x)"
    using ChamberComplexEndomorphism.endo_comp by auto
  moreover have "fold f xs \<circ> f x = fold f (x#xs)" by simp
  ultimately show ?case
    using subst[of _ _ "\<lambda>f. ChamberComplexEndomorphism X f"] by fast
qed

context ChamberComplexEndomorphism
begin

lemma split_gallery:
  "\<lbrakk> C\<in>f\<turnstile>\<C>; D\<in>\<C>-f\<turnstile>\<C>; gallery (C#Cs@[D]) \<rbrakk> \<Longrightarrow>
    \<exists>As A B Bs. A\<in>f\<turnstile>\<C> \<and> B\<in>\<C>-f\<turnstile>\<C> \<and> C#Cs@[D] = As@A#B#Bs"
proof (induct Cs arbitrary: C)
  case Nil
  define As :: "'a set list" where "As = []"
  hence "C#[]@[D] = As@C#D#As" by simp
  with Nil(1,2) show ?case by auto
next
  case (Cons E Es)
  show ?case
  proof (cases "E\<in>f\<turnstile>\<C>")
    case True
    from Cons(4) have "gallery (E#Es@[D])"
      using gallery_Cons_reduce by simp
    with True obtain As A B Bs
      where 1: "A\<in>f\<turnstile>\<C>" "B\<in>\<C>-f\<turnstile>\<C>" "E#Es@[D] = As@A#B#Bs"
      using Cons(1)[of E] Cons(3)
      by    blast
    from 1(3) have "C#(E#Es)@[D] = (C#As)@A#B#Bs" by simp
    with 1(1,2) show ?thesis by blast
  next
    case False
    hence "E\<in>\<C>-f\<turnstile>\<C>" using gallery_chamber_system[OF Cons(4)] by simp
    moreover have "C#(E#Es)@[D] = []@C#E#(Es@[D])" by simp
    ultimately show ?thesis using Cons(2) by blast
  qed
qed

lemma respects_labels_adjacent:
  assumes "label_wrt B \<phi>" "chamber C" "chamber D" "C\<sim>D" "\<forall>v\<in>C. \<phi> (f v) = \<phi> v"
  shows   "\<forall>v\<in>D. \<phi> (f v) = \<phi> v"
proof (cases "C=D")
  case False have CD: "C\<noteq>D" by fact
  with assms(4) obtain w where w: "w\<notin>D" "C = insert w (C\<inter>D)"
    using adjacent_int_decomp by fast
  with assms(2) have fC: "f w \<notin> f`(C\<inter>D)" "f`C = insert (f w) (f`(C\<inter>D))"
    using chamber_vertex_outside_facet_image[of w "C\<inter>D"] by auto
  show ?thesis
  proof
    fix v assume v: "v\<in>D"
    show "\<phi> (f v) = \<phi> v"
    proof (cases "v\<in>C")
      case False
      with assms(3,4) v have fD: "f v \<notin> f`(D\<inter>C)" "f`D = insert (f v) (f`(D\<inter>C))"
        using adjacent_sym[of C D] adjacent_conv_insert[of D C v]
              chamber_vertex_outside_facet_image[of v "D\<inter>C"]
        by    auto
      have "\<phi> (f v) = \<phi> (f w)"
      proof (cases "f`C=f`D")
        case True
        with fC fD have "f v = f w" by (auto simp add: Int_commute)
        thus ?thesis by simp
      next
        case False
        from assms(2-4) have "chamber (f`C)" "chamber (f`D)" and fCfD: "f`C\<sim>f`D"
          using chamber_map adj_map by auto
        moreover from assms(4) fC fCfD False have "f w \<in> f`C - f`D"
          using adjacent_to_adjacent_int[of C D f] by auto
        ultimately show ?thesis
          using assms(4) fD fCfD False adjacent_sym
                adjacent_to_adjacent_int[of D C f]
                label_wrt_adjacent[OF assms(1), of "f`C" "f`D" "f w" "f v", THEN sym]
          by    auto
      qed
      with False v w assms(5) show ?thesis
        using label_wrt_adjacent[OF assms(1-4), of w v, THEN sym] by fastforce
    qed (simp add: assms(5))
  qed
qed (simp add: assms(5))

lemma respects_labels_gallery:
  assumes "label_wrt B \<phi>" "\<forall>v\<in>C. \<phi> (f v) = \<phi> v"
  shows   "gallery (C#Cs@[D]) \<Longrightarrow> \<forall>v\<in>D. \<phi> (f v) = \<phi> v"
proof (induct Cs arbitrary: D rule: rev_induct)
  case Nil with assms(2) show ?case
    using galleryD_chamber galleryD_adj
          respects_labels_adjacent[OF assms(1), of C D]
    by    force
next
  case (snoc E Es)
  with assms(2) show ?case
    using gallery_append_reduce1[of "C#Es@[E]"] galleryD_chamber galleryD_adj
          binrelchain_append_reduce2[of adjacent "C#Es" "[E,D]"]
          respects_labels_adjacent[OF assms(1), of E D]
    by    force
qed

lemma respect_label_fix_chamber_imp_fun_eq_on:
  assumes label  :  "label_wrt B \<phi>"
  and     chamber:  "chamber C" "f`C = g`C"
  and     respect:  "\<forall>v\<in>C. \<phi> (f v) = \<phi> v" "\<forall>v\<in>C. \<phi> (g v) = \<phi> v"
  shows   "fun_eq_on f g C"
proof (rule fun_eq_onI)
  fix v assume "v\<in>C"
  moreover with respect have "\<phi> (f v) = \<phi> (g v)" by simp
  ultimately show "f v = g v"
    using label chamber chamber_map chamber_system_def label_wrtD[of B \<phi> "f`C"]
          bij_betw_imp_inj_on[of \<phi>] inj_onD
    by    fastforce
qed

lemmas respects_label_fixes_chamber_imp_fixespointwise =
  respect_label_fix_chamber_imp_fun_eq_on[of _ _ _ id, simplified]

end (* context ChamberComplexEndomorphism *)

subsubsection \<open>Automorphisms\<close>

locale ChamberComplexAutomorphism = ChamberComplexIsomorphism X X f
  for X :: "'a set set"
  and f :: "'a\<Rightarrow>'a"
+ assumes trivial_outside : "v\<notin>\<Union>X \<Longrightarrow> f v = v"
  \<comment> \<open>to facilitate uniqueness arguments\<close>

sublocale ChamberComplexAutomorphism < ChamberComplexEndomorphism
  using trivial_outside by unfold_locales fast

lemma (in ChamberComplex) trivial_automorphism:
  "ChamberComplexAutomorphism X id"
  using trivial_isomorphism
  by    unfold_locales (auto intro: ChamberComplexAutomorphism.intro)

context ChamberComplexAutomorphism
begin

lemmas facet_map         = facet_map
lemmas chamber_map       = chamber_map
lemmas chamber_morphism  = chamber_morphism
lemmas bij_betw_vertices = bij_betw_vertices
lemmas surj_simplex_map  = surj_simplex_map

lemma bij: "bij f"
proof (rule bijI)
  show "inj f"
  proof (rule injI)
    fix x y assume "f x = f y" thus "x = y"
      using bij_betw_imp_inj_on[OF bij_betw_vertices] inj_onD[of f "\<Union>X" x y]
            vertex_map trivial_outside
      by    (cases "x\<in>\<Union>X" "y\<in>\<Union>X" rule: two_cases) auto
  qed
  show "surj f" unfolding surj_def
  proof
    fix y show "\<exists>x. y = f x"
      using bij_betw_imp_surj_on[OF bij_betw_vertices]
            trivial_outside[THEN sym, of y]
      by    (cases "y\<in>\<Union>X") auto
  qed
qed

lemma comp:
  assumes "ChamberComplexAutomorphism X g"
  shows   "ChamberComplexAutomorphism X (g\<circ>f)"
proof (
  rule ChamberComplexAutomorphism.intro,
  rule ChamberComplexIsomorphism.intro,
  rule ChamberComplexMorphism.comp
)
  from assms show "ChamberComplexMorphism X X g"
    using ChamberComplexAutomorphism.chamber_morphism by fast
  show "ChamberComplexIsomorphism_axioms X X (g \<circ> f)"
  proof
    from assms show "bij_betw (g\<circ>f) (\<Union>X) (\<Union>X)"
      using bij_betw_vertices ChamberComplexAutomorphism.bij_betw_vertices
            bij_betw_trans
      by    fast
    from assms show "(g\<circ>f) \<turnstile> X = X"
      using surj_simplex_map ChamberComplexAutomorphism.surj_simplex_map 
      by    (force simp add: setsetmapim_comp)
  qed
  show "ChamberComplexAutomorphism_axioms X (g \<circ> f)"
    using trivial_outside ChamberComplexAutomorphism.trivial_outside[OF assms]
    by    unfold_locales auto
qed unfold_locales

lemma equality:
  assumes "ChamberComplexAutomorphism X g" "fun_eq_on f g (\<Union>X)"
  shows   "f = g"
proof
  fix x show "f x = g x"
    using trivial_outside fun_eq_onD[OF assms(2)] 
          ChamberComplexAutomorphism.trivial_outside[OF assms(1)]
    by    force
qed

end (* context ChamberComplexAutomorphism *)

subsubsection \<open>Retractions\<close>

text \<open>A retraction of a chamber complex is an endomorphism that is the identity on its image.\<close>

locale ChamberComplexRetraction = ChamberComplexEndomorphism X f
  for X :: "'a set set"
  and f :: "'a\<Rightarrow>'a"
+ assumes retraction: "v\<in>\<Union>X \<Longrightarrow> f (f v) = f v"
begin

lemmas simplex_map = simplex_map
lemmas chamber_map = chamber_map
lemmas gallery_map = gallery_map

lemma vertex_retraction: "v\<in>f`(\<Union>X) \<Longrightarrow> f v = v"
  using retraction by fast

lemma simplex_retraction1: "x\<in>f\<turnstile>X \<Longrightarrow> fixespointwise f x"
  using retraction fixespointwiseI[of x f] by auto

lemma simplex_retraction2: "x\<in>f\<turnstile>X \<Longrightarrow> f`x = x"
  using retraction retraction[THEN sym] by blast

lemma chamber_retraction1: "C\<in>f\<turnstile>\<C> \<Longrightarrow> fixespointwise f C"
  using chamber_system_simplices simplex_retraction1 by auto

lemma chamber_retraction2: "C\<in>f\<turnstile>\<C> \<Longrightarrow> f`C = C"
  using chamber_system_simplices simplex_retraction2[of C] by auto

lemma respects_labels:
  assumes "label_wrt B \<phi>" "v\<in>(\<Union>X)"
  shows   "\<phi> (f v) = \<phi> v"
proof-
  from assms(2) obtain C where "chamber C" "v\<in>C" using simplex_in_max by fast
  thus ?thesis
    using chamber_retraction1[of C] chamber_system_def chamber_map
          maxsimp_connect[of "f`C" C] chamber_retraction1[of "f`C"]
          respects_labels_gallery[OF assms(1), THEN bspec, of "f`C" _ C v]
    by    (force simp add: fixespointwiseD)
qed

end (* context ChamberComplexRetraction *)

subsubsection \<open>Foldings of chamber complexes\<close>

text \<open>
  A folding of a chamber complex is a retraction that literally folds the complex in half, in that
  each chamber in the image is the image of precisely two chambers: itself (since a folding is a
  retraction) and a unique chamber outside the image.
\<close>

paragraph \<open>Locale definition\<close>

text \<open>
  Here we define the locale and collect some lemmas inherited from the
  @{const ChamberComplexRetraction} locale.
\<close>

locale ChamberComplexFolding = ChamberComplexRetraction X f
  for X :: "'a set set"
  and f :: "'a\<Rightarrow>'a"
+ assumes folding:
    "chamber C \<Longrightarrow> C\<in>f\<turnstile>X \<Longrightarrow>
      \<exists>!D. chamber D \<and> D\<notin>f\<turnstile>X \<and> f`D = C"
begin

lemmas folding_ex          = ex1_implies_ex[OF folding]
lemmas chamber_system_into = chamber_system_into
lemmas gallery_map         = gallery_map
lemmas chamber_retraction1 = chamber_retraction1
lemmas chamber_retraction2 = chamber_retraction2

end (* context ChamberComplexFolding *)

paragraph \<open>Decomposition into half chamber systems and half apartments\<close>

text \<open>
  Here we describe how a folding splits the chamber system of the complex into its image and the
  complement of its image. The chamber subcomplex consisting of all simplices contained in a
  chamber of a given half of the chamber system is called a half-apartment.
\<close>

context ChamberComplexFolding
begin

definition opp_half_apartment :: "'a set set"
  where "opp_half_apartment \<equiv> {x\<in>X. \<exists>C\<in>\<C>-f\<turnstile>\<C>. x\<subseteq>C}"
abbreviation "Y \<equiv> opp_half_apartment"

lemma opp_half_apartment_subset_complex: "Y\<subseteq>X"
  using opp_half_apartment_def by fast

lemma simplicialcomplex_opp_half_apartment: "SimplicialComplex Y"
proof
  show "\<forall>x\<in>Y. finite x"
    using opp_half_apartment_subset_complex finite_simplices by fast
next
  fix x y assume "x\<in>Y" "y\<subseteq>x" thus "y\<in>Y"
    using     opp_half_apartment_subset_complex faces[of x y]
    unfolding opp_half_apartment_def
    by        auto
qed

lemma subcomplex_opp_half_apartment: "Subcomplex Y"
  using opp_half_apartment_subset_complex simplicialcomplex_opp_half_apartment
  by    fast

lemma opp_half_apartmentI: "\<lbrakk> x\<in>X; C\<in>\<C>-f\<turnstile>\<C>; x\<subseteq>C \<rbrakk> \<Longrightarrow> x\<in>Y"
  using opp_half_apartment_def by auto

lemma opp_chambers_subset_opp_half_apartment: "\<C>-f\<turnstile>\<C> \<subseteq> Y"
proof
  fix C assume "C \<in> \<C>-f\<turnstile>\<C>"
  thus "C \<in> Y" using chamber_system_simplices opp_half_apartmentI by auto
qed

lemma maxsimp_in_opp_half_apartment:
  assumes "SimplicialComplex.maxsimp Y C"
  shows   "C \<in> \<C>-f\<turnstile>\<C>"
proof-
  from assms obtain D where D: "D\<in>\<C>-f\<turnstile>\<C>" "C\<subseteq>D"
    using SimplicialComplex.maxsimpD_simplex[
            OF simplicialcomplex_opp_half_apartment, of C
          ]
          opp_half_apartment_def
    by    auto
  with assms show ?thesis
    using opp_chambers_subset_opp_half_apartment 
          SimplicialComplex.maxsimpD_maximal[
            OF simplicialcomplex_opp_half_apartment
          ]
    by    force
qed

lemma chamber_in_opp_half_apartment:
  "SimplicialComplex.maxsimp Y C \<Longrightarrow> chamber C"
  using maxsimp_in_opp_half_apartment chamber_system_def by fast

end (* context ChamberComplexFolding *)

paragraph \<open>Mapping between half chamber systems for foldings\<close>

text \<open>
  Since each chamber in the image of the folding is the image of a unique chamber in the complement
  of the image, we obtain well-defined functions from one half chamber system to the other.
\<close>

context ChamberComplexFolding
begin

abbreviation "opp_chamber C \<equiv> THE D. D\<in>\<C>-f\<turnstile>\<C> \<and> f`D = C"
abbreviation "flop C \<equiv> if C \<in> f\<turnstile>\<C> then opp_chamber C else f`C"

lemma inj_on_opp_chambers':
  assumes "chamber C" "C\<notin>f\<turnstile>X" "chamber D" "D\<notin>f\<turnstile>X" "f`C = f`D"
  shows   "C=D"
proof-
  from assms(1) folding have ex1: "\<exists>!B. chamber B \<and> B\<notin>f\<turnstile>X \<and> f`B = f`C"
    using chamberD_simplex chamber_map by auto
  from assms show ?thesis using ex1_unique[OF ex1, of C D] by blast
qed  

lemma inj_on_opp_chambers'':
  "\<lbrakk> C \<in> \<C>-f\<turnstile>\<C>; D \<in> \<C>-f\<turnstile>\<C>; f`C = f`D \<rbrakk> \<Longrightarrow> C=D"
  using chamber_system_def chamber_system_image inj_on_opp_chambers' by auto

lemma inj_on_opp_chambers: "inj_on ((`) f) (\<C>-f\<turnstile>\<C>)"
  using inj_on_opp_chambers'' inj_onI[of "\<C>-f\<turnstile>\<C>" "(`) f"] by fast

lemma opp_chambers_surj: "f\<turnstile>(\<C>-(f\<turnstile>\<C>)) = f\<turnstile>\<C>"
proof (rule seteqI)
  fix D assume D: "D \<in> f\<turnstile>\<C>"
  from this obtain B where "chamber B" "B\<notin>f\<turnstile>X" "f`B = D"
    using chamber_system_def chamber_map chamberD_simplex folding_ex[of D]
    by    auto
  thus "D \<in> f\<turnstile>(\<C> - f\<turnstile>\<C>)"
    using chamber_system_image chamber_system_def by auto
qed fast

lemma opp_chambers_bij: "bij_betw ((`) f) (\<C>-(f\<turnstile>\<C>)) (f\<turnstile>\<C>)"
  using inj_on_opp_chambers opp_chambers_surj bij_betw_def[of "(`) f"] by auto

lemma folding':
  assumes "C\<in>f\<turnstile>\<C>"
  shows   "\<exists>!D\<in>\<C>-f\<turnstile>\<C>. f`D = C"
proof (rule ex_ex1I)
  from assms show "\<exists>D. D \<in> \<C>-f\<turnstile>\<C> \<and> f`D = C"
    using chamber_system_image chamber_system_def folding_ex[of C] by auto
next
  fix B D assume "B \<in> \<C>-f\<turnstile>\<C> \<and> f`B = C" "D \<in> \<C>-f\<turnstile>\<C> \<and> f`D = C"
  with assms show "B=D"
    using chamber_system_def chamber_system_image chamber_map
          chamberD_simplex ex1_unique[OF folding, of C B D]
    by    auto
qed

lemma opp_chambers_distinct_map:
  "set Cs \<subseteq> \<C>-f\<turnstile>\<C> \<Longrightarrow> distinct Cs \<Longrightarrow> distinct (f\<Turnstile>Cs)"
  using distinct_map subset_inj_on[OF inj_on_opp_chambers] by auto

lemma opp_chamberD1: "C\<in>f\<turnstile>\<C> \<Longrightarrow> opp_chamber C \<in> \<C>-f\<turnstile>\<C>"
    using theI'[OF folding'] by simp

lemma opp_chamberD2: "C\<in>f\<turnstile>\<C> \<Longrightarrow> f`(opp_chamber C) = C"
  using theI'[OF folding'] by simp

lemma opp_chamber_reverse: "C\<in>\<C>-f\<turnstile>\<C> \<Longrightarrow> opp_chamber (f`C) = C"
  using the1_equality[OF folding'] by simp

lemma f_opp_chamber_list:
  "set Cs \<subseteq> f\<turnstile>\<C> \<Longrightarrow> f\<Turnstile>(map opp_chamber Cs) = Cs"
  using opp_chamberD2 by (induct Cs) auto

lemma flop_chamber: "chamber C \<Longrightarrow> chamber (flop C)"
  using chamber_map opp_chamberD1 chamber_system_def by auto

end (* context ChamberComplexFolding *)




subsection \<open>Thin chamber complexes\<close>

text \<open>
  A thin chamber complex is one in which every facet is a facet in exactly two chambers. Slightly
  more generally, we first consider the case of a chamber complex in which every facet is a facet
  of at most two chambers. One of the main results obtained at this point is the so-called standard
  uniqueness argument, which essentially states that two morphisms on a thin chamber complex that
  agree on a particular chamber must in fact agree on the entire complex. Following that, foldings
  of thin chamber complexes are investigated. In particular, we are interested in pairs of opposed
  foldings.
\<close>

subsubsection \<open>Locales and basic facts\<close>

locale ThinishChamberComplex = ChamberComplex X
  for X :: "'a set set"
+ assumes thinish:
  "\<lbrakk> chamber C; z\<lhd>C; \<exists>D\<in>X-{C}. z\<lhd>D \<rbrakk> \<Longrightarrow> \<exists>!D\<in>X-{C}. z\<lhd>D"
  \<comment> \<open>being adjacent to a chamber, such a @{term D} would also be a chamber (see lemma
@{text "chamber_adj"})\<close>
begin

lemma facet_unique_other_chamber:
  "\<lbrakk> chamber B; z\<lhd>B; chamber C; z\<lhd>C; chamber D; z\<lhd>D; C\<noteq>B; D\<noteq>B \<rbrakk>
    \<Longrightarrow> C=D"
  using chamberD_simplex bex1_equality[OF thinish, OF _ _ bexI, of B z C C D]
  by    auto

lemma finite_adjacentset:
  assumes "chamber C"
  shows   "finite (adjacentset C)"
proof (cases "X = {{}}")
  case True thus ?thesis using adjacentset_def by simp
next
  case False
  moreover have "finite (\<Union>v\<in>C. {D\<in>X. C-{v}\<lhd>D})"
  proof
    from assms show "finite C" using finite_chamber by simp
  next
    fix v assume "v\<in>C"
    with assms have Cv: "C-{v}\<lhd>C"
      using chamberD_simplex facetrel_diff_vertex by fast
    with assms have C: "C\<in>{D\<in>X. C-{v}\<lhd>D}"
      using chamberD_simplex by fast
    show "finite {D\<in>X. C-{v}\<lhd>D}"
    proof (cases "{D\<in>X. C-{v}\<lhd>D} - {C} = {}")
      case True
      hence 1: "{D\<in>X. C-{v}\<lhd>D} = {C}" using C by auto
      show ?thesis using ssubst[OF 1, of finite] by simp
    next
      case False
      from this obtain D where D: "D\<in>X-{C}" "C-{v}\<lhd>D" by fast
      with assms have 2: "{D\<in>X. C-{v}\<lhd>D} \<subseteq> {C,D}"
        using Cv chamber_shared_facet[of C] facet_unique_other_chamber[of C _ D]
        by    fastforce
      show ?thesis using finite_subset[OF 2] by simp
    qed
  qed
  ultimately show ?thesis
    using assms adjacentset_conv_facetchambersets by simp
qed

lemma label_wrt_eq_on_adjacent_vertex:
  fixes   v v' :: 'a
  and     z z' :: "'a set"
  defines D : "D \<equiv> insert v z"
  and     D': "D' \<equiv> insert v' z'"
  assumes label   : "label_wrt B f" "f v = f v'"
  and     chambers: "chamber C" "chamber D" "chamber D'" "z\<lhd>C" "z'\<lhd>C" "D\<noteq>C" "D'\<noteq>C" 
  shows   "D = D'"
proof (
  rule facet_unique_other_chamber, rule chambers(1), rule chambers(4),
  rule chambers(2)
)
  from D D' chambers(1-5) have z: "z\<lhd>D" and z': "z'\<lhd>D'"
    using chambers_share_facet by auto
  show "z\<lhd>D" by fact

  from chambers(4,5) obtain w w'
    where w : "w \<notin> z " "C = insert w  z"
    and   w': "w'\<notin> z'" "C = insert w' z'"
    unfolding facetrel_def
    by        fastforce
  from w' D' chambers(1,3) have "f`z' = f`C - {f v'}"
    using z' label_wrtD'[OF label(1), of C] bij_betw_imp_inj_on[of f C]
          facetrel_complement_vertex[of z']
          label_wrt_adjacent_shared_facet[OF label(1), of v']
    by    simp
  moreover from w D chambers(1,2) have "f`z = f`C - {f v}"
    using z label_wrtD'[OF label(1), of C] bij_betw_imp_inj_on[of f C]
          facetrel_complement_vertex[of z]
          label_wrt_adjacent_shared_facet[OF label(1), of v]
    by    simp
  ultimately show "z\<lhd>D'"
    using z' chambers(1,4,5) label(2) facetrel_subset
          label_wrtD'[OF label(1), of C]
          bij_betw_imp_inj_on[of f] inj_on_eq_image[of f C z' z]
    by    force
qed (rule chambers(3), rule chambers(6), rule chambers(7))

lemma face_distance_eq_chamber_distance_compare_other_chamber:
  assumes   "chamber C" "chamber D" "z\<lhd>C" "z\<lhd>D" "C\<noteq>D"
            "chamber_distance C E \<le> chamber_distance D E"
  shows     "face_distance z E = chamber_distance C E"
  unfolding face_distance_def closest_supchamber_def
proof (
  rule arg_min_equality, rule conjI, rule assms(1), rule facetrel_subset,
  rule assms(3)
)
  from assms
    show  "\<And>B. chamber B \<and> z \<subseteq> B \<Longrightarrow>
            chamber_distance C E \<le> chamber_distance B E"
    using chamber_facet_is_chamber_facet facet_unique_other_chamber
    by    blast
qed

end (* context ThinishChamberComplex *)

lemma (in ChamberComplexIsomorphism) thinish_image_shared_facet:
  assumes dom:  "domain.chamber C" "domain.chamber D" "z\<lhd>C" "z\<lhd>D" "C\<noteq>D"
  and     cod:  "ThinishChamberComplex Y" "codomain.chamber D'" "f`z \<lhd> D'"
                "D' \<noteq> f`C"
  shows   "f`D = D'"
proof (rule ThinishChamberComplex.facet_unique_other_chamber, rule cod(1))
  from dom(1,2) show "codomain.chamber (f`C)" "codomain.chamber (f`D)"
    using chamber_map by auto
  from dom show "f`z \<lhd> f`C" "f`z \<lhd> f`D" using facet_map by auto
  from dom have "domain.pgallery [C,D]"
    using domain.pgallery_def adjacentI by fastforce
  hence "codomain.pgallery [f`C,f`D]" using pgallery_map[of "[C,D]"] by simp
  thus "f`D \<noteq> f`C" using codomain.pgalleryD_distinct by fastforce
qed (rule cod(2), rule cod(3), rule cod(4))

locale ThinChamberComplex = ChamberComplex X
  for X :: "'a set set"
+ assumes thin:  "chamber C \<Longrightarrow> z\<lhd>C \<Longrightarrow> \<exists>!D\<in>X-{C}. z\<lhd>D"

sublocale ThinChamberComplex < ThinishChamberComplex
  using thin by unfold_locales simp

context ThinChamberComplex
begin

lemma thinish: "ThinishChamberComplex X" ..

lemmas face_distance_eq_chamber_distance_compare_other_chamber =
  face_distance_eq_chamber_distance_compare_other_chamber

abbreviation "the_adj_chamber C z \<equiv> THE D. D\<in>X-{C} \<and> z \<lhd> D"

lemma the_adj_chamber_simplex:
  "chamber C \<Longrightarrow> z \<lhd> C \<Longrightarrow> the_adj_chamber C z \<in> X"
  using theI'[OF thin] by fast

lemma the_adj_chamber_facet: "chamber C \<Longrightarrow> z\<lhd>C \<Longrightarrow> z \<lhd> the_adj_chamber C z"
  using theI'[OF thin] by fast

lemma the_adj_chamber_is_adjacent:
  "chamber C \<Longrightarrow> z\<lhd>C \<Longrightarrow> C \<sim> the_adj_chamber C z"
  using the_adj_chamber_facet by (auto intro: adjacentI)
  
lemma the_adj_chamber:
  "chamber C \<Longrightarrow> z \<lhd> C \<Longrightarrow> chamber (the_adj_chamber C z)"
  using the_adj_chamber_simplex the_adj_chamber_is_adjacent
  by    (fast intro: chamber_adj)

lemma the_adj_chamber_neq:
  "chamber C \<Longrightarrow> z \<lhd> C \<Longrightarrow> the_adj_chamber C z \<noteq> C"
  using theI'[OF thin] by fast

lemma the_adj_chamber_adjacentset:
  "chamber C \<Longrightarrow> z\<lhd>C \<Longrightarrow> the_adj_chamber C z \<in> adjacentset C"
  using adjacentset_def the_adj_chamber_simplex the_adj_chamber_is_adjacent
  by    fast

end (* context ThinChamberComplex *)

lemmas (in ChamberComplexIsomorphism) thin_image_shared_facet =
  thinish_image_shared_facet[OF _ _ _ _ _ ThinChamberComplex.thinish]

subsubsection \<open>The standard uniqueness argument for chamber morphisms of thin chamber complexes\<close>

context ThinishChamberComplex
begin

lemma standard_uniqueness_dbl:
  assumes morph   : "ChamberComplexMorphism W X f"
                    "ChamberComplexMorphism W X g"
  and     chambers: "ChamberComplex.chamber W C"
                    "ChamberComplex.chamber W D"
                    "C\<sim>D" "f`D \<noteq> f`C" "g`D \<noteq> g`C" "chamber (g`D)"
  and     funeq   : "fun_eq_on f g C"
  shows "fun_eq_on f g D"
proof (rule fun_eq_onI)
  fix v assume v: "v\<in>D"
  show "f v = g v"
  proof (cases "v\<in>C")
    case True with funeq show ?thesis using fun_eq_onD by fast
  next
    case False
    define F G where "F = f`C \<inter> f`D" and "G = g`C \<inter> g`D"

    from morph(1) chambers(1-4) have 1: "f`C \<sim> f`D"
      using ChamberComplexMorphism.adj_map' by fast
    with F_def chambers(4) have F_facet: "F\<lhd>f`C" "F\<lhd>f`D"
      using adjacent_int_facet1[of "f`C"] adjacent_int_facet2[of "f`C"] by auto

    from F_def G_def chambers have "G = F"
      using ChamberComplexMorphism.adj_map'[OF morph(2)]
            adjacent_to_adjacent_int[of C D g] 1
            adjacent_to_adjacent_int[of C D f] funeq fun_eq_on_im[of f g]
      by    force
    with G_def morph(2) chambers have F_facet': "F\<lhd>g`D"
      using ChamberComplexMorphism.adj_map' adjacent_int_facet2 by blast
    with chambers(1,2,4,5) have 2: "g`D = f`D"
      using ChamberComplexMorphism.chamber_map[OF morph(1)] F_facet
            ChamberComplexMorphism.chamber_map[OF morph(2)]
            fun_eq_on_im[OF funeq]
            facet_unique_other_chamber[of "f`C" F "g`D" "f`D"]
      by    auto
    from chambers(3) v False have 3: "D = insert v (D\<inter>C)"
      using adjacent_sym adjacent_conv_insert by fast
    from chambers(4) obtain w where w: "w \<notin> f`C" "w \<in> f`D"
      using adjacent_int_decomp[OF adjacent_sym, OF 1] by blast
    with 3 have "w = f v" by fast
    moreover from 2 w(2) obtain v' where "v'\<in>D" "w = g v'" by auto
    ultimately show ?thesis
      using w(1) 3 funeq by (fastforce simp add: fun_eq_on_im)
  qed
qed

lemma standard_uniqueness_pgallery_betw:
  assumes morph   : "ChamberComplexMorphism W X f"
                    "ChamberComplexMorphism W X g"
  and     chambers: "fun_eq_on f g C" "ChamberComplex.gallery W (C#Cs@[D])"
                    "pgallery (f\<Turnstile>(C#Cs@[D]))" "pgallery (g\<Turnstile>(C#Cs@[D]))"
  shows   "fun_eq_on f g D"
proof-
  from morph(1) have W: "ChamberComplex W"
    using ChamberComplexMorphism.domain_complex by fast
  have "\<lbrakk> fun_eq_on f g C; ChamberComplex.gallery W (C#Cs@[D]);
          pgallery (f\<Turnstile>(C#Cs@[D])); pgallery (g\<Turnstile>(C#Cs@[D])) \<rbrakk> \<Longrightarrow>
          fun_eq_on f g D"
  proof (induct Cs arbitrary: C)
    case Nil from assms Nil(1) show ?case
      using ChamberComplex.galleryD_chamber[OF W Nil(2)]
            ChamberComplex.galleryD_adj[OF W Nil(2)]
            pgalleryD_distinct[OF Nil(3)] pgalleryD_distinct[OF Nil(4)]
            pgalleryD_chamber[OF Nil(4)] standard_uniqueness_dbl[of W f g C D]
      by    auto
  next
    case (Cons B Bs)
    have "fun_eq_on f g B"
    proof (rule standard_uniqueness_dbl, rule morph(1), rule morph(2))
      show "ChamberComplex.chamber W C" "ChamberComplex.chamber W B" "C\<sim>B"
        using ChamberComplex.galleryD_chamber[OF W Cons(3)]
              ChamberComplex.galleryD_adj[OF W Cons(3)]
        by    auto
      show "f`B \<noteq> f`C" using pgalleryD_distinct[OF Cons(4)] by fastforce
      show "g`B \<noteq> g`C" using pgalleryD_distinct[OF Cons(5)] by fastforce
      show "chamber (g`B)" using pgalleryD_chamber[OF Cons(5)] by fastforce
    qed (rule Cons(2))
    with Cons(1,3-5) show ?case
      using ChamberComplex.gallery_Cons_reduce[OF W, of C "B#Bs@[D]"]
            pgallery_Cons_reduce[of "f`C" "f\<Turnstile>(B#Bs@[D])"]
            pgallery_Cons_reduce[of "g`C" "g\<Turnstile>(B#Bs@[D])"]
      by    force
  qed
  with chambers show ?thesis by simp
qed

lemma standard_uniqueness:
  assumes morph   : "ChamberComplexMorphism W X f"
                    "ChamberComplexMorphism W X g"
  and     chamber : "ChamberComplex.chamber W C" "fun_eq_on f g C"
  and     map_gals:
    "\<And>Cs. ChamberComplex.min_gallery W (C#Cs) \<Longrightarrow> pgallery (f\<Turnstile>(C#Cs))"
    "\<And>Cs. ChamberComplex.min_gallery W (C#Cs) \<Longrightarrow> pgallery (g\<Turnstile>(C#Cs))"
  shows   "fun_eq_on f g (\<Union>W)"
proof (rule fun_eq_onI)
  from morph(1) have W: "ChamberComplex W"
    using ChamberComplexMorphism.axioms(1) by fast
  fix v assume "v \<in> \<Union>W"
  from this obtain D where "ChamberComplex.chamber W D" "v\<in>D"
    using ChamberComplex.simplex_in_max[OF W] by auto
  moreover define Cs where "Cs = (ARG_MIN length Cs. ChamberComplex.gallery W (C#Cs@[D]))"
  ultimately show "f v = g v"
    using chamber map_gals[of "Cs@[D]"]
          ChamberComplex.gallery_least_length[OF W]
          ChamberComplex.min_gallery_least_length[OF W]
          standard_uniqueness_pgallery_betw[OF morph(1,2) chamber(2), of Cs]
          fun_eq_onD[of f g D]
    by    (cases "D=C") auto
qed

lemma standard_uniqueness_isomorphs:
  assumes "ChamberComplexIsomorphism W X f"
          "ChamberComplexIsomorphism W X g"
          "ChamberComplex.chamber W C" "fun_eq_on f g C"
  shows   "fun_eq_on f g (\<Union>W)"
  using   assms ChamberComplexIsomorphism.chamber_morphism
          ChamberComplexIsomorphism.domain_complex
          ChamberComplex.min_gallery_pgallery
          ChamberComplexIsomorphism.pgallery_map
  by      (blast intro: standard_uniqueness)

lemma standard_uniqueness_automorphs:
  assumes "ChamberComplexAutomorphism X f"
          "ChamberComplexAutomorphism X g"
          "chamber C" "fun_eq_on f g C"
  shows   "f=g"
  using   assms ChamberComplexAutomorphism.equality
          standard_uniqueness_isomorphs
          ChamberComplexAutomorphism.axioms(1)
  by      blast
  

end (* context ThinishChamberComplex *)

context ThinChamberComplex
begin

lemmas standard_uniqueness               = standard_uniqueness
lemmas standard_uniqueness_isomorphs     = standard_uniqueness_isomorphs
lemmas standard_uniqueness_pgallery_betw = standard_uniqueness_pgallery_betw

end (* context ThinChamberComplex *)


subsection \<open>Foldings of thin chamber complexes\<close>

subsubsection \<open>Locale definition and basic facts\<close>

locale ThinishChamberComplexFolding =
  ThinishChamberComplex X + folding: ChamberComplexFolding X f
  for X :: "'a set set"
  and f :: "'a\<Rightarrow>'a"
begin

abbreviation "opp_chamber \<equiv> folding.opp_chamber"

lemma adjacent_half_chamber_system_image:
  assumes chambers: "C \<in> f\<turnstile>\<C>" "D \<in> \<C>-f\<turnstile>\<C>"
  and     adjacent: "C\<sim>D"
  shows   "f`D = C"
proof-
  from adjacent obtain z where z: "z\<lhd>C" "z\<lhd>D" using adjacent_def by fast
  moreover from z(1) chambers(1) have fz: "f`z = z"
    using facetrel_subset[of z C] chamber_system_simplices
          folding.simplicialcomplex_image
          SimplicialComplex.faces[of "f\<turnstile>X" C z]
          folding.simplex_retraction2[of z]
    by    auto
  moreover from chambers have "f`D \<noteq> D" "C\<noteq>D" by auto
  ultimately show ?thesis
    using chambers chamber_system_def folding.chamber_map
          folding.facet_map[of D z]
          facet_unique_other_chamber[of D z "f`D" C]
    by    force
qed

lemma adjacent_half_chamber_system_image_reverse:
  "\<lbrakk> C \<in> f\<turnstile>\<C>; D \<in> \<C>-f\<turnstile>\<C>; C\<sim>D \<rbrakk> \<Longrightarrow> opp_chamber C = D"
  using adjacent_half_chamber_system_image[of C D]
        the1_equality[OF folding.folding']
  by    fastforce

lemma chamber_image_closer:
  assumes "D\<in>\<C>-f\<turnstile>\<C>" "B\<in>f\<turnstile>\<C>" "B\<noteq>f`D" "gallery (B#Ds@[D])"
  shows   "\<exists>Cs. gallery (B#Cs@[f`D]) \<and> length Cs < length Ds"
proof-
  from assms(1,2,4) obtain As A E Es
    where split: "A\<in>f\<turnstile>\<C>" "E\<in>\<C>-f\<turnstile>\<C>" "B#Ds@[D] = As@A#E#Es"
    using folding.split_gallery[of B D Ds]
    by    blast
  from assms(4) split(3) have "A\<sim>E"
    using gallery_append_reduce2[of As "A#E#Es"] galleryD_adj[of "A#E#Es"]
    by    simp
  with assms(2) split(1,2)
    have  fB: "f`B = B" and fA: "f`A = A" and fE: "f`E = A"
    using folding.chamber_retraction2 adjacent_half_chamber_system_image[of A E]
    by    auto
  show "\<exists>Cs. gallery (B#Cs@[f`D]) \<and> length Cs < length Ds"
  proof (cases As)
    case Nil have As: "As = []" by fact
    show ?thesis
    proof (cases Es rule: rev_cases)
      case Nil with split(3) As assms(3) fE show ?thesis by simp
    next
      case (snoc Fs F)
      with assms(4) split(3) As fE
        have  "Ds = E#Fs" "gallery (B # f\<Turnstile>Fs @ [f`D])"
        using fB folding.gallery_map[of "B#E#Fs@[D]"] gallery_Cons_reduce
        by    auto
      thus ?thesis by auto
    qed
  next
    case (Cons H Hs)
    show ?thesis
    proof (cases Es rule: rev_cases)
      case Nil
      with assms(4) Cons split(3)
        have  decomp: "Ds = Hs@[A]" "D=E" "gallery (B#Hs@[A,D])"
        by    auto
      from decomp(2,3) fB fA fE have "gallery (B # f\<Turnstile>Hs @ [f`D])"
        using folding.gallery_map gallery_append_reduce1[of "B # f\<Turnstile>Hs @ [f`D]"]
        by    force
      with decomp(1) show ?thesis by auto
    next
      case (snoc Fs F)
      with split(3) Cons assms(4) fB fA fE
        have  decomp: "Ds = Hs@A#E#Fs" "gallery (B # f\<Turnstile>(Hs@A#Fs) @ [f`D])"
        using folding.gallery_map[of "B#Hs@A#E#Fs@[D]"]
              gallery_remdup_adj[of "B#f\<Turnstile>Hs" A "f\<Turnstile>Fs@[f`D]"]
        by    auto
      from decomp(1) have "length (f\<Turnstile>(Hs@A#Fs)) < length Ds" by simp
      with decomp(2) show ?thesis by blast
    qed
  qed
qed

lemma chamber_image_subset:
  assumes D: "D\<in>\<C>-f\<turnstile>\<C>"
  defines C: "C \<equiv> f`D"
  defines "closerToC \<equiv> {B\<in>\<C>. chamber_distance B C < chamber_distance B D}"
  shows   "f\<turnstile>\<C> \<subseteq> closerToC"
proof
  fix B assume B: "B\<in>f\<turnstile>\<C>"
  hence B': "B\<in>\<C>" using folding.chamber_system_into by fast
  show "B \<in> closerToC"
  proof (cases "B=C")
    case True with B D closerToC_def show ?thesis
      using B' chamber_distance_def by auto
  next
    case False
    define Ds where "Ds = (ARG_MIN length Ds. gallery (B#Ds@[D]))"
    with B C D False closerToC_def show ?thesis
      using chamber_system_def folding.chamber_map gallery_least_length[of B D]
            chamber_image_closer[of D B Ds]
            chamber_distance_le chamber_distance_def[of B D]
      by    fastforce
  qed
qed

lemma gallery_double_cross_not_minimal_Cons1:
  "\<lbrakk> B\<in>f\<turnstile>\<C>; C\<in>\<C>-f\<turnstile>\<C>; D\<in>f\<turnstile>\<C>; gallery (B#C#Cs@[D]) \<rbrakk> \<Longrightarrow>
    \<not> min_gallery (B#C#Cs@[D])"
  using galleryD_adj[of "B#C#Cs@[D]"]
        adjacent_half_chamber_system_image[of B C]
        folding.gallery_map[of "B#C#Cs@[D]"]
        gallery_Cons_reduce[of B "B # f\<Turnstile>Cs @ [D]"]
        is_arg_minD2[of length "(\<lambda>Ds. maxsimpchain (B#Ds@[D]))" _ "f\<Turnstile>Cs"]
        min_maxsimpchain.simps(3)[of B "C#Cs" D]
  by(simp add: folding.chamber_retraction2)(meson impossible_Cons not_less)

lemma gallery_double_cross_not_minimal1:
  "\<lbrakk> B\<in>f\<turnstile>\<C>; C\<in>\<C>-f\<turnstile>\<C>; D\<in>f\<turnstile>\<C>; gallery (B#Bs@C#Cs@[D]) \<rbrakk> \<Longrightarrow>
    \<not> min_gallery (B#Bs@C#Cs@[D])"
proof (induct Bs arbitrary: B)
  case Nil thus ?case using gallery_double_cross_not_minimal_Cons1 by simp
next
  case (Cons E Es)
  show ?case
  proof (cases "E\<in>f\<turnstile>\<C>")
    case True
    with Cons(1,3-5) show ?thesis
      using gallery_Cons_reduce[of B "E#Es@C#Cs@[D]"]
            min_gallery_betw_CCons_reduce[of B E "Es@C#Cs" D]
      by    auto
  next
    case False with Cons(2,4,5) show ?thesis
      using gallery_chamber_system
            gallery_double_cross_not_minimal_Cons1[of B E D "Es@C#Cs"]
      by    force
  qed
qed

end (* ThinishChamberComplexFolding *)

locale ThinChamberComplexFolding =
  ThinChamberComplex X + folding: ChamberComplexFolding X f
  for X :: "'a set set"
  and f :: "'a\<Rightarrow>'a"

sublocale ThinChamberComplexFolding < ThinishChamberComplexFolding ..

context ThinChamberComplexFolding
begin

abbreviation "flop \<equiv> folding.flop"

lemmas adjacent_half_chamber_system_image = adjacent_half_chamber_system_image
lemmas gallery_double_cross_not_minimal1  = gallery_double_cross_not_minimal1
lemmas gallery_double_cross_not_minimal_Cons1 =
  gallery_double_cross_not_minimal_Cons1

lemma adjacent_preimage:
  assumes chambers: "C \<in> \<C>-f\<turnstile>\<C>" "D \<in> \<C>-f\<turnstile>\<C>"
  and     adjacent: "f`C \<sim> f`D"
  shows "C \<sim> D"
proof (cases "f`C=f`D")
  case True
  with chambers show "C \<sim> D"
    using folding.inj_on_opp_chambers''[of C D] adjacent_refl[of C] by auto
next
  case False
  from chambers have CD: "chamber C" "chamber D"
    using chamber_system_def by auto
  hence ch_fCD: "chamber (f`C)" "chamber (f`D)"
    using chamber_system_def folding.chamber_map by auto
  from adjacent obtain z where z: "z \<lhd> f`C" "z \<lhd> f`D"
    using adjacent_def by fast
  from chambers(1) z(1) obtain y where y: "y \<lhd> C" "f`y = z"
    using chamber_system_def folding.inj_on_chamber[of C]
          inj_on_pullback_facet[of f C z]
    by    auto
  define B where "B = the_adj_chamber C y"
  with CD(1) y(1) have B: "chamber B" "y\<lhd>B" "B\<noteq>C"
    using the_adj_chamber the_adj_chamber_facet the_adj_chamber_neq by auto
  have "f`B \<noteq> f`C"
  proof (cases "B \<in> f\<turnstile>\<C>")
    case False with chambers(1) show ?thesis
      using B(1,3) chamber_system_def folding.inj_on_opp_chambers''[of B]
      by    auto
  next
    case True show ?thesis
    proof
      assume fB_fC: "f`B = f`C"
      with True have "B = f`C" using folding.chamber_retraction2 by auto
      with z(1) y(2) B(2) chambers(1) have "y = z"
        using facetrel_subset[of y B] chamber_system_def chamberD_simplex face_im
              folding.simplex_retraction2[of y]
        by    force
      with chambers y(1) z(2) have "f`D = B"
        using CD(1) ch_fCD(2) B facet_unique_other_chamber[of C y] by auto
      with z(2) chambers fB_fC False show False
        using folding.chamber_retraction2 by force
    qed
  qed
  with False z y(2) have fB_fD: "f`B = f`D"
    using ch_fCD B(1,2) folding.chamber_map folding.facet_map
          facet_unique_other_chamber[of "f`C" z]
    by    force
  have "B = D"
  proof (cases "B \<in> f\<turnstile>\<C>")
    case False
    with B(1) chambers(2) show ?thesis
      using chamber_system_def fB_fD folding.inj_on_opp_chambers'' by simp
  next
    case True
    with fB_fD have "B = f`D" using folding.chamber_retraction2 by auto
    moreover with z(1) y(2) B(2) chambers(2) have "y = z"
      using facetrel_subset[of y B] chamber_system_def chamberD_simplex face_im
            folding.simplex_retraction2[of y]
      by    force
    ultimately show ?thesis
      using CD y(1) B ch_fCD(1) z(1) False chambers(1)
            facet_unique_other_chamber[of B y C "f`C"]
      by    auto
  qed
  with y(1) B(2) show ?thesis using adjacentI by fast
qed

lemma adjacent_opp_chamber:
  "\<lbrakk> C\<in>f\<turnstile>\<C>; D\<in>f\<turnstile>\<C>; C\<sim>D \<rbrakk> \<Longrightarrow> opp_chamber C \<sim> opp_chamber D"
  using folding.opp_chamberD1 folding.opp_chamberD2 adjacent_preimage by simp

lemma adjacentchain_preimage: 
  "set Cs \<subseteq> \<C>-f\<turnstile>\<C> \<Longrightarrow> adjacentchain (f\<Turnstile>Cs) \<Longrightarrow> adjacentchain Cs"
  using adjacent_preimage by (induct Cs rule: list_induct_CCons) auto

lemma gallery_preimage: "set Cs \<subseteq> \<C>-f\<turnstile>\<C> \<Longrightarrow> gallery (f\<Turnstile>Cs) \<Longrightarrow> gallery Cs"
  using galleryD_adj adjacentchain_preimage chamber_system_def gallery_def
  by    fast

lemma chambercomplex_opp_half_apartment: "ChamberComplex folding.Y"
proof (intro_locales, rule folding.simplicialcomplex_opp_half_apartment, unfold_locales)
  define Y where "Y = folding.Y"
  fix y assume "y\<in>Y" 
  with Y_def obtain C where "C\<in>\<C>-f\<turnstile>\<C>" "y\<subseteq>C"
    using folding.opp_half_apartment_def by auto
  with Y_def show "\<exists>x. SimplicialComplex.maxsimp Y x \<and> y \<subseteq> x"
    using folding.subcomplex_opp_half_apartment
          folding.opp_chambers_subset_opp_half_apartment
          chamber_system_def max_in_subcomplex[of Y]
    by    force
next
  define Y where "Y = folding.Y"
  fix C D
  assume CD:  "SimplicialComplex.maxsimp Y C" "SimplicialComplex.maxsimp Y D"
              "C\<noteq>D"
  from CD(1,2) Y_def have CD': "C \<in> \<C>-f\<turnstile>\<C>" "D \<in> \<C>-f\<turnstile>\<C>"
    using folding.maxsimp_in_opp_half_apartment by auto
  with CD(3) obtain Ds
    where Ds: "ChamberComplex.gallery (f\<turnstile>X) ((f`C)#Ds@[f`D])"
    using folding.inj_on_opp_chambers''[of C D] chamber_system_def
          folding.maxsimp_map_into_image folding.chambercomplex_image
          ChamberComplex.maxsimp_connect[of "f\<turnstile>X" "f`C" "f`D"]
    by    auto
  define Cs where "Cs = map opp_chamber Ds"
  from Ds have Ds': "gallery ((f`C)#Ds@[f`D])"
    using folding.chambersubcomplex_image subcomplex_gallery by fast
  with Ds have Ds'': "set Ds \<subseteq> f\<turnstile>\<C>"
    using folding.chambercomplex_image folding.chamber_system_image
          ChamberComplex.galleryD_chamber ChamberComplex.chamberD_simplex
          gallery_chamber_system
    by    fastforce
  have *: "set Cs \<subseteq> \<C>-f\<turnstile>\<C>"
  proof
    fix B assume "B \<in> set Cs"
    with Cs_def obtain A where "A\<in>set Ds" "B = opp_chamber A" by auto
    with Ds'' show "B \<in> \<C>-f\<turnstile>\<C>" using folding.opp_chamberD1[of A] by auto
  qed
  moreover from Cs_def CD' Ds' Ds'' * have "gallery (C#Cs@[D])"
    using folding.f_opp_chamber_list gallery_preimage[of "C#Cs@[D]"] by simp
  ultimately show "\<exists>Cs. SimplicialComplex.maxsimpchain Y (C # Cs @ [D])"
    using Y_def CD' folding.subcomplex_opp_half_apartment
          folding.opp_chambers_subset_opp_half_apartment
          maxsimpchain_in_subcomplex[of Y "C#Cs@[D]"]
    by    fastforce
qed

lemma flop_adj:
  assumes "chamber C" "chamber D" "C\<sim>D"
  shows   "flop C \<sim> flop D"
proof (cases "C\<in>f\<turnstile>\<C>" "D\<in>f\<turnstile>\<C>" rule: two_cases)
  case both
  with assms(3) show ?thesis using adjacent_opp_chamber by simp
next
  case one
  with assms(2,3) show ?thesis
    using chamber_system_def adjacent_half_chamber_system_image[of C]
          adjacent_half_chamber_system_image_reverse adjacent_sym
    by    simp
next
  case other
  with assms(1) show ?thesis
    using chamber_system_def adjacent_sym[OF assms(3)]
          adjacent_half_chamber_system_image[of D] 
          adjacent_half_chamber_system_image_reverse
    by    auto
qed (simp add: assms folding.adj_map)

lemma flop_gallery: "gallery Cs \<Longrightarrow> gallery (map flop Cs)"
proof (induct Cs rule: list_induct_CCons)
  case (CCons B C Cs)
  have "gallery (flop B # (flop C) # map flop Cs)"
  proof (rule gallery_CConsI)
    from CCons(2) show "chamber (flop B)"
      using galleryD_chamber folding.flop_chamber by simp
    from CCons(1) show "gallery (flop C # map flop Cs)"
      using gallery_Cons_reduce[OF CCons(2)] by simp
    from CCons(2) show "flop B \<sim> flop C"
      using galleryD_chamber galleryD_adj flop_adj[of B C] by fastforce
  qed
  thus ?case by simp
qed (auto simp add: galleryD_chamber folding.flop_chamber gallery_def)

lemma morphism_half_apartments: "ChamberComplexMorphism folding.Y (f\<turnstile>X) f"
proof (
  rule ChamberComplexMorphism.intro, rule chambercomplex_opp_half_apartment,
  rule folding.chambercomplex_image, unfold_locales
)
  show
    "\<And>C. SimplicialComplex.maxsimp folding.Y C \<Longrightarrow>
      SimplicialComplex.maxsimp (f\<turnstile>X) (f`C)"
    "\<And>C. SimplicialComplex.maxsimp folding.Y C \<Longrightarrow> card (f`C) = card C"
    using folding.chamber_in_opp_half_apartment folding.chamber_map
          folding.chambersubcomplex_image chamber_in_subcomplex
          chamberD_simplex folding.dim_map
    by    auto
qed

lemma chamber_image_complement_closer:
  "\<lbrakk> D\<in>\<C>-f\<turnstile>\<C>; B\<in>\<C>-f\<turnstile>\<C>; B\<noteq>D; gallery (B#Cs@[f`D]) \<rbrakk> \<Longrightarrow>
      \<exists>Ds. gallery (B#Ds@[D]) \<and> length Ds < length Cs"
  using flop_gallery chamber_image_closer[of D "f`B" "map flop Cs"]
        folding.opp_chamber_reverse folding.inj_on_opp_chambers''[of B D]
  by    force

lemma chamber_image_complement_subset:
  assumes D: "D\<in>\<C>-f\<turnstile>\<C>"
  defines C: "C \<equiv> f`D"
  defines "closerToD \<equiv> {B\<in>\<C>. chamber_distance B D < chamber_distance B C}"
  shows   "\<C>-f\<turnstile>\<C> \<subseteq> closerToD"
proof
  fix B assume B: "B\<in>\<C>-f\<turnstile>\<C>"
  show "B \<in> closerToD"
  proof (cases "B=D")
    case True with B C closerToD_def show ?thesis
      using chamber_distance_def by auto
  next
    case False
    define Cs where "Cs = (ARG_MIN length Cs. gallery (B#Cs@[C]))"
    with B C D False closerToD_def show ?thesis
      using chamber_system_def folding.chamber_map[of D]
            gallery_least_length[of B C] chamber_distance_le
            chamber_image_complement_closer[of D B Cs]
            chamber_distance_def[of B C]
      by    fastforce
  qed
qed

lemma chamber_image_and_complement:
  assumes D: "D\<in>\<C>-f\<turnstile>\<C>"
  defines C: "C \<equiv> f`D"
  defines "closerToC \<equiv> {B\<in>\<C>. chamber_distance B C < chamber_distance B D}"
  and     "closerToD \<equiv> {B\<in>\<C>. chamber_distance B D < chamber_distance B C}"
  shows "f\<turnstile>\<C> = closerToC" "\<C>-f\<turnstile>\<C> = closerToD"
proof-
  from closerToC_def closerToD_def have "closerToC \<inter> closerToD = {}" by auto
  moreover from C D closerToC_def closerToD_def
    have "\<C> = f \<turnstile> \<C> \<union> (\<C>-f\<turnstile>\<C>)" "closerToC \<subseteq> \<C>" "closerToD \<subseteq> \<C>"
    using folding.chamber_system_into
    by    auto
  moreover from assms have "f\<turnstile>\<C> \<subseteq> closerToC" "\<C>-f\<turnstile>\<C> \<subseteq> closerToD"
    using chamber_image_subset chamber_image_complement_subset by auto
  ultimately show "f\<turnstile>\<C> = closerToC" "\<C>-f\<turnstile>\<C> = closerToD"
    using set_decomp_subset[of \<C> "f\<turnstile>\<C>"] set_decomp_subset[of \<C> "\<C>-f\<turnstile>\<C>"] by auto
qed

end (* context ThinChamberComplexFolding *)

subsubsection \<open>Pairs of opposed foldings\<close>

text \<open>
  A pair of foldings of a thin chamber complex are opposed or opposite if there is a corresponding
  pair of adjacent chambers, where each folding sends its corresponding chamber to the other
  chamber.
\<close>

locale OpposedThinChamberComplexFoldings =
  ThinChamberComplex X
+ folding_f: ChamberComplexFolding X f
+ folding_g: ChamberComplexFolding X g
  for X :: "'a set set"
  and f :: "'a\<Rightarrow>'a"
  and g :: "'a\<Rightarrow>'a"
+ fixes C0 :: "'a set"
  assumes chambers: "chamber C0" "C0\<sim>g`C0" "C0\<noteq>g`C0" "f`g`C0 = C0"
begin

abbreviation "D0 \<equiv> g`C0"

lemmas chamber_D0 = folding_g.chamber_map[OF chambers(1)]

lemma ThinChamberComplexFolding_f: "ThinChamberComplexFolding X f" ..
lemma ThinChamberComplexFolding_g: "ThinChamberComplexFolding X g" ..

lemmas foldf = ThinChamberComplexFolding_f
lemmas foldg = ThinChamberComplexFolding_g

lemma fg_symmetric: "OpposedThinChamberComplexFoldings X g f D0"
  using chambers(2-4) chamber_D0 adjacent_sym by unfold_locales auto

lemma basechambers_half_chamber_systems: "C0\<in>f\<turnstile>\<C>" "D0\<in>g\<turnstile>\<C>"
  using chambers(1,4) chamber_D0 chamber_system_def by auto

lemmas basech_halfchsys =
  basechambers_half_chamber_systems

lemma f_trivial_C0: "v\<in>C0 \<Longrightarrow> f v = v"
  using chambers(4) chamber_D0 chamberD_simplex[of D0]
        folding_f.vertex_retraction
  by    fast

lemmas g_trivial_D0 =
  OpposedThinChamberComplexFoldings.f_trivial_C0[OF fg_symmetric]

lemma double_fold_D0:
  assumes "v \<in> D0 - C0"
  shows   "g (f v) = v"
proof-
  from assms chambers(2) have 1: "D0 = insert v (C0\<inter>D0)"
    using adjacent_sym adjacent_conv_insert by fast
  hence "f`D0 = insert (f v) (f`(C0\<inter>D0))" by fast
  moreover have "f`(C0\<inter>D0) = C0\<inter>D0" using f_trivial_C0 by force
  ultimately have "C0 = insert (f v) (C0\<inter>D0)" using chambers(4) by simp
  hence "g`C0 = insert (g (f v)) (g`(C0\<inter>D0))" by force
  moreover have "g`(C0\<inter>D0) = C0\<inter>D0"
    using g_trivial_D0 fixespointwise_im[of g D0 "C0\<inter>D0"]
    by    (fastforce intro: fixespointwiseI)
  ultimately have "D0 = insert (g (f v)) (C0\<inter>D0)" by simp
  with assms show ?thesis using 1 by force
qed

lemmas double_fold_C0 =
  OpposedThinChamberComplexFoldings.double_fold_D0[OF fg_symmetric]

lemma flopped_half_chamber_systems_fg: "\<C>-f\<turnstile>\<C> = g\<turnstile>\<C>"
proof-
  from chambers(1,3,4) have "D0\<in>\<C>-f\<turnstile>\<C>" "C0\<in>\<C>-g\<turnstile>\<C>"
    using chamber_system_def chamber_D0 folding_f.chamber_retraction2[of D0]
          folding_g.chamber_retraction2[of C0]
    by    auto
  with chambers(2,4) show ?thesis
    using ThinChamberComplexFolding.chamber_image_and_complement[
            OF ThinChamberComplexFolding_g, of C0
          ]
          ThinChamberComplexFolding.chamber_image_and_complement[
            OF ThinChamberComplexFolding_f, of D0
          ]
          adjacent_sym[of C0 D0]
    by    force
qed

lemmas flopped_half_chamber_systems_gf =
  OpposedThinChamberComplexFoldings.flopped_half_chamber_systems_fg[
    OF fg_symmetric
  ]

lemma flopped_half_apartments_fg: "folding_f.opp_half_apartment = g\<turnstile>X"
proof (rule seteqI)
  fix a assume "a \<in> folding_f.Y"
  from this obtain C where "C\<in>g\<turnstile>\<C>" "a\<subseteq>C"
    using folding_f.opp_half_apartment_def flopped_half_chamber_systems_fg by auto
  thus "a\<in>g\<turnstile>X"
    using chamber_system_simplices
          ChamberComplex.faces[OF folding_g.chambercomplex_image, of C]
    by    auto
next
  fix b assume b: "b \<in> g\<turnstile>X"
  from this obtain C where C: "C\<in>\<C>" "b \<subseteq> g`C"
    using simplex_in_max chamber_system_def by fast
  from C(1) have "g`C \<in> g\<turnstile>\<C>" by fast
  hence "g`C \<in> \<C>-f\<turnstile>\<C>" using flopped_half_chamber_systems_fg by simp
  with C(2) have "\<exists>C\<in>\<C>-f\<turnstile>\<C>. b\<subseteq>C" by auto
  moreover from b have "b\<in>X" using folding_g.simplex_map by fast
  ultimately show "b \<in> folding_f.Y"
    unfolding folding_f.opp_half_apartment_def by simp
qed

lemmas flopped_half_apartments_gf =
  OpposedThinChamberComplexFoldings.flopped_half_apartments_fg[
    OF fg_symmetric
  ]

lemma vertex_set_split: "\<Union>X = f`(\<Union>X) \<union> g`(\<Union>X)"
\<comment> \<open>@{term f} and @{term g} will both be the identity on the intersection\<close>
proof
  show "\<Union>X \<supseteq> f`(\<Union>X) \<union> g`(\<Union>X)"
    using folding_f.simplex_map folding_g.simplex_map by auto
  show "\<Union>X \<subseteq> f`(\<Union>X) \<union> g`(\<Union>X)"
  proof
    fix a assume "a\<in>\<Union>X"
    from this obtain C where C: "chamber C" "a\<in>C"
      using simplex_in_max by fast
    from C(1) have "C\<in>f\<turnstile>\<C> \<or> C\<in>g\<turnstile>\<C>"
      using chamber_system_def flopped_half_chamber_systems_fg by auto
    with C(2) show "a \<in> (f`\<Union>X) \<union> (g`\<Union>X)"
      using chamber_system_simplices by fast
  qed
qed

lemma half_chamber_system_disjoint_union:
  "\<C> = f\<turnstile>\<C> \<union> g\<turnstile>\<C>" "(f\<turnstile>\<C>) \<inter> (g\<turnstile>\<C>) = {}"
  using folding_f.chamber_system_into
        flopped_half_chamber_systems_fg[THEN sym]
  by    auto

lemmas halfchsys_decomp =
  half_chamber_system_disjoint_union

lemma chamber_in_other_half_fg: "chamber C \<Longrightarrow> C\<notin>f\<turnstile>\<C> \<Longrightarrow> C\<in>g\<turnstile>\<C>"
  using chamber_system_def half_chamber_system_disjoint_union(1) by blast

lemma adjacent_half_chamber_system_image_fg:
  "C\<in>f\<turnstile>\<C> \<Longrightarrow> D\<in>g\<turnstile>\<C> \<Longrightarrow> C\<sim>D \<Longrightarrow> f`D = C"
  using ThinChamberComplexFolding.adjacent_half_chamber_system_image[
          OF ThinChamberComplexFolding_f
        ]
  by    (simp add: flopped_half_chamber_systems_fg)

lemmas adjacent_half_chamber_system_image_gf =
  OpposedThinChamberComplexFoldings.adjacent_half_chamber_system_image_fg[
    OF fg_symmetric
  ]

lemmas adjhalfchsys_image_gf =
  adjacent_half_chamber_system_image_gf

lemma switch_basechamber:
  assumes "C\<in>f\<turnstile>\<C>" "C\<sim>g`C"
  shows   "OpposedThinChamberComplexFoldings X f g C"
proof
  from assms(1) have "C\<in>\<C>-g\<turnstile>\<C>" using flopped_half_chamber_systems_gf by simp
  with assms show "chamber C" "C \<noteq> g`C" "f`g`C = C"
    using chamber_system_def adjacent_half_chamber_system_image_fg[of C "g`C"]
    by    auto
qed (rule assms(2))

lemma unique_half_chamber_system_f:
  assumes "OpposedThinChamberComplexFoldings X f' g' C0" "g'`C0 = D0"
  shows   "f'\<turnstile>\<C> = f\<turnstile>\<C>"
proof-
  have 1: "OpposedThinChamberComplexFoldings X f g' C0"
  proof (rule OpposedThinChamberComplexFoldings.intro)
    show "ChamberComplexFolding X f" "ThinChamberComplex X" ..
    from assms(1) show "ChamberComplexFolding X g'"
      using OpposedThinChamberComplexFoldings.axioms(3) by fastforce
    from assms(2) chambers
      show  "OpposedThinChamberComplexFoldings_axioms X f g' C0"
      by    unfold_locales auto
  qed
  define a b where "a = f'\<turnstile>\<C>" and "b = f\<turnstile>\<C>"
  hence "a\<subseteq>\<C>" "b\<subseteq>\<C>" "\<C>-a = \<C>-b"
    using OpposedThinChamberComplexFoldings.axioms(2)[OF assms(1)]
          OpposedThinChamberComplexFoldings.axioms(2)[OF 1]
          ChamberComplexFolding.chamber_system_into[of X f]
          ChamberComplexFolding.chamber_system_into[of X f']
          OpposedThinChamberComplexFoldings.flopped_half_chamber_systems_fg[
            OF assms(1)
          ]
          OpposedThinChamberComplexFoldings.flopped_half_chamber_systems_fg[
            OF 1
          ]
    by    auto
  hence "a=b" by fast
  with a_def b_def show ?thesis by simp
qed

lemma unique_half_chamber_system_g:
  "OpposedThinChamberComplexFoldings X f' g' C0 \<Longrightarrow> g'`C0 = D0 \<Longrightarrow>
    g'\<turnstile>\<C> = g\<turnstile>\<C>"
  using unique_half_chamber_system_f flopped_half_chamber_systems_fg
        OpposedThinChamberComplexFoldings.flopped_half_chamber_systems_fg[
          of X f' g'
        ]
  by    simp

lemma split_gallery_fg:
  "\<lbrakk> C\<in>f\<turnstile>\<C>; D\<in>g\<turnstile>\<C>; gallery (C#Cs@[D]) \<rbrakk> \<Longrightarrow>
    \<exists>As A B Bs. A\<in>f\<turnstile>\<C> \<and> B\<in>g\<turnstile>\<C> \<and> C#Cs@[D] = As@A#B#Bs"
  using folding_f.split_gallery flopped_half_chamber_systems_fg by simp

lemmas split_gallery_gf =
  OpposedThinChamberComplexFoldings.split_gallery_fg[OF fg_symmetric]

end (* context OpposedThinChamberComplexFoldings *)

subsubsection \<open>The automorphism induced by a pair of opposed foldings\<close>

text \<open>
  Recall that a folding of a chamber complex is a special kind of chamber complex retraction, and
  so is the identity on its image. Hence a pair of opposed foldings will be the identity on the
  intersection of their images and so we can stitch them together to create an automorphism of the
  chamber complex, by allowing each folding to act on the complement of its image.
  This automorphism will be of order two, and will be the unique automorphism of the chamber
  complex that fixes pointwise the facet shared by the pair of adjacent chambers associated to the
  opposed foldings.
\<close>

context OpposedThinChamberComplexFoldings
begin

definition induced_automorphism :: "'a\<Rightarrow>'a"
  where "induced_automorphism v \<equiv>
          if v\<in>f`(\<Union>X) then g v else if v\<in>g`(\<Union>X) then f v else v"
\<comment> \<open>@{term f} and @{term g} will both be the identity on the intersection of their images\<close>
abbreviation "\<s> \<equiv> induced_automorphism"

lemma induced_automorphism_fg_symmetric:
  "\<s> = OpposedThinChamberComplexFoldings.\<s> X g f"
  by  (auto simp add:
        folding_f.vertex_retraction folding_g.vertex_retraction
        induced_automorphism_def
        OpposedThinChamberComplexFoldings.induced_automorphism_def[
          OF fg_symmetric
        ]
      )

lemma induced_automorphism_on_simplices_fg: "x\<in>f\<turnstile>X \<Longrightarrow> v\<in>x \<Longrightarrow> \<s> v = g v"
  using induced_automorphism_def by auto

lemma induced_automorphism_eq_foldings_on_chambers_fg:
  "C\<in>f\<turnstile>\<C> \<Longrightarrow> fun_eq_on \<s> g C"
  using chamber_system_simplices induced_automorphism_on_simplices_fg[of C]
  by    (fast intro: fun_eq_onI)

lemmas indaut_eq_foldch_fg =
  induced_automorphism_eq_foldings_on_chambers_fg

lemma induced_automorphism_eq_foldings_on_chambers_gf:
  "C\<in>g\<turnstile>\<C> \<Longrightarrow> fun_eq_on \<s> f C"
  by  (auto simp add:
        OpposedThinChamberComplexFoldings.indaut_eq_foldch_fg[
          OF fg_symmetric
        ]
        induced_automorphism_fg_symmetric
      )

lemma induced_automorphism_on_chamber_vertices_f:
  "chamber C \<Longrightarrow> v\<in>C \<Longrightarrow> \<s> v = (if C\<in>f\<turnstile>\<C> then g v else f v)"
  using chamber_system_def induced_automorphism_eq_foldings_on_chambers_fg
        induced_automorphism_eq_foldings_on_chambers_gf
        flopped_half_chamber_systems_fg[THEN sym]
        fun_eq_onD[of \<s> g C] fun_eq_onD[of \<s> f C]
  by    auto

lemma induced_automorphism_simplex_image:
  "C\<in>f\<turnstile>\<C> \<Longrightarrow> x\<subseteq>C \<Longrightarrow> \<s>`x = g`x" "C\<in>g\<turnstile>\<C> \<Longrightarrow> x\<subseteq>C \<Longrightarrow> \<s>`x = f`x"
  using fun_eq_on_im[of \<s> g C] fun_eq_on_im[of \<s> f C]
        induced_automorphism_eq_foldings_on_chambers_fg
        induced_automorphism_eq_foldings_on_chambers_gf
  by    auto

lemma induced_automorphism_chamber_list_image_fg:
  "set Cs \<subseteq> f\<turnstile>\<C> \<Longrightarrow> \<s>\<Turnstile>Cs = g\<Turnstile>Cs"
proof (induct Cs)
  case (Cons C Cs) thus ?case
    using induced_automorphism_simplex_image(1)[of C] by simp
qed simp

lemma induced_automorphism_chamber_image_fg:
  "chamber C \<Longrightarrow> \<s>`C = (if C\<in>f\<turnstile>\<C> then g`C else f`C)"
  using chamber_system_def induced_automorphism_simplex_image
        flopped_half_chamber_systems_fg[THEN sym]
  by    auto

lemma induced_automorphism_C0: "\<s>`C0 = D0"
  using chambers(1,4) basechambers_half_chamber_systems(1)
        induced_automorphism_chamber_image_fg
  by    auto

lemma induced_automorphism_fixespointwise_C0_int_D0:
  "fixespointwise \<s> (C0\<inter>D0)"
  using fun_eq_on_trans[of \<s> g] fun_eq_on_subset[of \<s> g C0]
        fixespointwise_subset[of g D0]
        induced_automorphism_eq_foldings_on_chambers_fg
        basechambers_half_chamber_systems
        folding_g.chamber_retraction1 
  by    auto

lemmas indaut_fixes_fundfacet =
  induced_automorphism_fixespointwise_C0_int_D0

lemma induced_automorphism_adjacent_half_chamber_system_image_fg:
  "\<lbrakk> C\<in>f\<turnstile>\<C>; D\<in>g\<turnstile>\<C>; C\<sim>D \<rbrakk> \<Longrightarrow> \<s>`D = C"
  using adjacent_half_chamber_system_image_fg[of C D]
        induced_automorphism_simplex_image(2)
  by    auto

lemmas indaut_adj_halfchsys_im_fg =
  induced_automorphism_adjacent_half_chamber_system_image_fg

lemma induced_automorphism_chamber_map: "chamber C \<Longrightarrow> chamber (\<s>`C)"
  using induced_automorphism_chamber_image_fg folding_f.chamber_map
        folding_g.chamber_map
  by    auto

lemmas indaut_chmap = induced_automorphism_chamber_map

lemma induced_automorphism_ntrivial: "\<s> \<noteq> id"
proof
  assume \<s>: "\<s> = id"
  from chambers(2,3) obtain v where v: "v \<notin> D0" "C0 = insert v (C0\<inter>D0)"
    using adjacent_int_decomp[of C0 D0] by fast
  from chambers(4) \<s> v(2) have gv: "g v = v"
    using chamberD_simplex[OF chamber_D0]
          induced_automorphism_on_simplices_fg[of C0 v, THEN sym]
    by    auto
  have "g`C0 = C0"
  proof (rule seteqI)
    from v(2) gv show "\<And>x. x\<in>C0 \<Longrightarrow> x\<in>g`C0" using g_trivial_D0 by force
  next
    fix x assume "x\<in>g`C0"
    from this obtain y where y: "y\<in>C0" "x = g y" by fast
    moreover from y(1) v(2) gv have "g y = y"
      using g_trivial_D0[of y] by (cases "y=v") auto
    ultimately show "x\<in>C0" using y by simp
  qed
  with chambers(3) show False by fast
qed

lemma induced_automorphism_bij_between_half_chamber_systems_f:
  "bij_betw ((`) \<s>) (\<C>-f\<turnstile>\<C>) (f\<turnstile>\<C>)"
  using induced_automorphism_simplex_image(2)
        flopped_half_chamber_systems_fg
        folding_f.opp_chambers_bij bij_betw_cong[of "\<C>-f\<turnstile>\<C>" "(`) \<s>"]
  by    auto

lemmas indaut_bij_btw_halfchsys_f =
  induced_automorphism_bij_between_half_chamber_systems_f

lemma induced_automorphism_bij_between_half_chamber_systems_g:
  "bij_betw ((`) \<s>) (\<C>-g\<turnstile>\<C>) (g\<turnstile>\<C>)"
  using induced_automorphism_fg_symmetric
        OpposedThinChamberComplexFoldings.indaut_bij_btw_halfchsys_f[
          OF fg_symmetric
        ]
  by    simp

lemma induced_automorphism_halfmorphism_fopp_to_fimage:
  "ChamberComplexMorphism folding_f.opp_half_apartment (f\<turnstile>X) \<s>"
proof (
  rule ChamberComplexMorphism.cong,
  rule ThinChamberComplexFolding.morphism_half_apartments,
  rule ThinChamberComplexFolding_f, rule fun_eq_onI
)
  show "\<And>v. v \<in> \<Union>folding_f.Y \<Longrightarrow> \<s> v = f v"
    using folding_f.opp_half_apartment_def chamber_system_simplices
    by    (force simp add:
            flopped_half_chamber_systems_fg
            induced_automorphism_fg_symmetric
            OpposedThinChamberComplexFoldings.induced_automorphism_def[
              OF fg_symmetric
            ]
          )
qed

lemmas indaut_halfmorph_fopp_fim =
  induced_automorphism_halfmorphism_fopp_to_fimage

lemma induced_automorphism_half_chamber_system_gallery_map_f:
  "set Cs \<subseteq> f\<turnstile>\<C> \<Longrightarrow> gallery Cs \<Longrightarrow> gallery (\<s>\<Turnstile>Cs)"
  using folding_g.gallery_map[of Cs]
        induced_automorphism_chamber_list_image_fg[THEN sym]
  by    auto

lemma induced_automorphism_half_chamber_system_pgallery_map_f:
  "set Cs \<subseteq> f\<turnstile>\<C> \<Longrightarrow> pgallery Cs \<Longrightarrow> pgallery (\<s>\<Turnstile>Cs)"
  using induced_automorphism_half_chamber_system_gallery_map_f pgallery
        flopped_half_chamber_systems_gf pgalleryD_distinct
        folding_g.opp_chambers_distinct_map
        induced_automorphism_chamber_list_image_fg[THEN sym]
  by    (auto intro: pgalleryI_gallery)

lemmas indaut_halfchsys_pgal_map_f =
  induced_automorphism_half_chamber_system_pgallery_map_f

lemma induced_automorphism_half_chamber_system_pgallery_map_g:
  "set Cs \<subseteq> g\<turnstile>\<C> \<Longrightarrow> pgallery Cs \<Longrightarrow> pgallery (\<s>\<Turnstile>Cs)"
  using induced_automorphism_fg_symmetric
        OpposedThinChamberComplexFoldings.indaut_halfchsys_pgal_map_f[
          OF fg_symmetric
        ]
  by    simp

lemma induced_automorphism_halfmorphism_fimage_to_fopp:
  "ChamberComplexMorphism (f\<turnstile>X) folding_f.opp_half_apartment \<s>"
  using OpposedThinChamberComplexFoldings.indaut_halfmorph_fopp_fim[
          OF fg_symmetric
        ]
  by    (auto simp add:
          flopped_half_apartments_gf flopped_half_apartments_fg
          induced_automorphism_fg_symmetric
        )

lemma induced_automorphism_selfcomp_halfmorphism_f:
  "ChamberComplexMorphism (f\<turnstile>X) (f\<turnstile>X) (\<s>\<circ>\<s>)"
  using induced_automorphism_halfmorphism_fimage_to_fopp
        induced_automorphism_halfmorphism_fopp_to_fimage
  by    (auto intro: ChamberComplexMorphism.comp)

lemma induced_automorphism_selfcomp_halftrivial_f: "fixespointwise (\<s>\<circ>\<s>) (\<Union>(f\<turnstile>X))"
proof (
  rule standard_uniqueness, rule ChamberComplexMorphism.expand_codomain,
  rule induced_automorphism_selfcomp_halfmorphism_f
)
  show "ChamberComplexMorphism (f\<turnstile>X) X id"
    using folding_f.chambersubcomplex_image inclusion_morphism by fast
  show "SimplicialComplex.maxsimp (f\<turnstile>X) C0"
    using chambers(1,4) chamberD_simplex[OF chamber_D0]
          chamber_in_subcomplex[OF folding_f.chambersubcomplex_image, of C0]
    by    auto
  show "fixespointwise (\<s>\<circ>\<s>) C0"
  proof (rule fixespointwiseI)
    fix v assume v: "v\<in>C0"
    with chambers(4) have "v\<in>f`(\<Union>X)"
      using chamber_D0 chamberD_simplex by fast
    hence 1: "\<s> v = g v" using induced_automorphism_def by simp
    show "(\<s>\<circ>\<s>) v = id v"
    proof (cases "v\<in>D0")
      case True with v show ?thesis using 1 g_trivial_D0 by simp
    next
      case False
      from v chambers(1,4) have "\<s> (g v) = f (g v)"
        using chamberD_simplex induced_automorphism_fg_symmetric
              OpposedThinChamberComplexFoldings.induced_automorphism_def[
                OF fg_symmetric, of "g v"
              ]
        by    force
      with v False chambers(4) show ?thesis using double_fold_C0 1 by simp
    qed
  qed
next
  fix Cs assume "ChamberComplex.min_gallery (f\<turnstile>X) (C0#Cs)"
  hence Cs: "ChamberComplex.pgallery (f\<turnstile>X) (C0#Cs)"
    using ChamberComplex.min_gallery_pgallery folding_f.chambercomplex_image
    by    fast
  hence pCs: "pgallery (C0#Cs)"
    using folding_f.chambersubcomplex_image subcomplex_pgallery by auto
  thus "pgallery (id\<Turnstile>(C0#Cs))" by simp
  have set_Cs: "set (C0#Cs) \<subseteq> f\<turnstile>\<C>"
    using Cs pCs folding_f.chambersubcomplex_image
          ChamberSubcomplexD_complex ChamberComplex.pgalleryD_chamber
          ChamberComplex.chamberD_simplex pgallery_chamber_system
          folding_f.chamber_system_image
    by    fastforce
  hence "pgallery (\<s>\<Turnstile>(C0#Cs))"
    using pCs induced_automorphism_half_chamber_system_pgallery_map_f[of "C0#Cs"]
    by    auto
  moreover have "set (\<s>\<Turnstile>(C0#Cs)) \<subseteq> g\<turnstile>\<C>"
  proof-
    have "set (\<s>\<Turnstile>(C0#Cs)) \<subseteq> \<s>\<turnstile>(\<C>-g\<turnstile>\<C>)"
      using set_Cs flopped_half_chamber_systems_gf by auto
    thus ?thesis
      using bij_betw_imp_surj_on[
              OF induced_automorphism_bij_between_half_chamber_systems_g
            ]
      by    simp
  qed
  ultimately have "pgallery (\<s>\<Turnstile>(\<s>\<Turnstile>(C0#Cs)))"
    using induced_automorphism_half_chamber_system_pgallery_map_g[
            of "\<s>\<Turnstile>(C0#Cs)"
          ]
    by    auto
  thus "pgallery ((\<s>\<circ>\<s>)\<Turnstile>(C0#Cs))"
    using ssubst[OF setlistmapim_comp, of pgallery, of \<s> \<s> "C0#Cs"] by fast
qed (unfold_locales, rule folding_f.chambersubcomplex_image)

lemmas indaut_selfcomp_halftriv_f =
  induced_automorphism_selfcomp_halftrivial_f

lemma induced_automorphism_selfcomp_halftrivial_g: "fixespointwise (\<s>\<circ>\<s>) (\<Union>(g\<turnstile>X))"
  using induced_automorphism_fg_symmetric
        OpposedThinChamberComplexFoldings.indaut_selfcomp_halftriv_f[
          OF fg_symmetric
        ]
  by    simp

lemma induced_automorphism_trivial_outside:
  assumes "v\<notin>\<Union>X"
  shows   "\<s> v = v"
proof-
  from assms have "v \<notin> f`(\<Union>X) \<and> v \<notin> g`(\<Union>X)" using vertex_set_split by fast
  thus "\<s> v = v" using induced_automorphism_def by simp
qed

lemma induced_automorphism_morphism: "ChamberComplexEndomorphism X \<s>"
proof (unfold_locales, rule induced_automorphism_chamber_map, simp)
  fix C assume "chamber C"
  thus "card (\<s>`C) = card C"
    using induced_automorphism_chamber_image_fg folding_f.dim_map
          folding_g.dim_map
          flopped_half_chamber_systems_fg[THEN sym]
    by    (cases "C\<in>f\<turnstile>\<C>") auto
qed (rule induced_automorphism_trivial_outside)

lemmas indaut_morph = induced_automorphism_morphism

lemma induced_automorphism_morphism_order2: "\<s>\<circ>\<s> = id"
proof
  fix v
  show "(\<s>\<circ>\<s>) v = id v"
  proof (cases "v\<in>f`(\<Union>X)" "v\<in>g`(\<Union>X)" rule: two_cases)
    case both
    from both(1) show ?thesis
      using induced_automorphism_selfcomp_halftrivial_f fixespointwiseD[of "\<s>\<circ>\<s>"]
      by    auto
  next
    case one thus ?thesis
      using induced_automorphism_selfcomp_halftrivial_f fixespointwiseD[of "\<s>\<circ>\<s>"]
      by    fastforce
  next
    case other thus ?thesis
      using induced_automorphism_selfcomp_halftrivial_g fixespointwiseD[of "\<s>\<circ>\<s>"]
      by    fastforce
  qed (simp add: induced_automorphism_def)
qed

lemmas indaut_order2 = induced_automorphism_morphism_order2

lemmas induced_automorphism_bij =
  o_bij[OF
    induced_automorphism_morphism_order2
    induced_automorphism_morphism_order2
  ]

lemma induced_automorphism_surj_on_vertexset: "\<s>`(\<Union>X) = \<Union>X"
proof
  show "\<s>`(\<Union>X) \<subseteq> \<Union>X"
    using induced_automorphism_morphism
          ChamberComplexEndomorphism.vertex_map
    by    fast
  hence "(\<s>\<circ>\<s>)`(\<Union>X) \<subseteq> \<s>`(\<Union>X)" by fastforce
  thus "\<Union>X \<subseteq> \<s>`(\<Union>X)" using induced_automorphism_morphism_order2 by simp
qed

lemma induced_automorphism_bij_betw_vertexset: "bij_betw \<s> (\<Union>X) (\<Union>X)"
  using induced_automorphism_bij induced_automorphism_surj_on_vertexset 
  by    (auto intro: bij_betw_subset)

lemma induced_automorphism_surj_on_simplices: "\<s>\<turnstile>X = X"
proof
  show "\<s>\<turnstile>X \<subseteq> X"
    using induced_automorphism_morphism
          ChamberComplexEndomorphism.simplex_map
    by    fast
  hence "\<s>\<turnstile>(\<s>\<turnstile>X) \<subseteq> \<s>\<turnstile>X" by auto
  thus "X \<subseteq> \<s>\<turnstile>X"
    by  (simp add:
          setsetmapim_comp[THEN sym] induced_automorphism_morphism_order2
        )
qed

lemma induced_automorphism_automorphism:
  "ChamberComplexAutomorphism X \<s>"
  using induced_automorphism_chamber_map
        ChamberComplexEndomorphism.dim_map
        induced_automorphism_morphism
        induced_automorphism_bij_betw_vertexset
        induced_automorphism_surj_on_simplices
        induced_automorphism_trivial_outside
  by    (intro_locales, unfold_locales, fast)

lemmas indaut_aut = induced_automorphism_automorphism

lemma induced_automorphism_unique_automorphism':
  assumes "ChamberComplexAutomorphism X s" "s\<noteq>id" "fixespointwise s (C0\<inter>D0)"
  shows   "fun_eq_on s \<s> C0"
proof (rule fun_eq_on_subset_and_diff_imp_eq_on)
  from assms(3) show "fun_eq_on s \<s> (C0\<inter>D0)"
    using induced_automorphism_fixespointwise_C0_int_D0
          fixespointwise2_imp_eq_on
    by    fast
  show "fun_eq_on s \<s> (C0 - (C0\<inter>D0))"
  proof (rule fun_eq_onI)
    fix v assume v: "v \<in> C0 - C0\<inter>D0"
    with chambers(2) have C0_insert: "C0 = insert v (C0\<inter>D0)"
      using adjacent_conv_insert by fast
    hence "s`C0 = insert (s v) (s`(C0\<inter>D0))" "\<s>`C0 = insert (\<s> v) (\<s>`(C0\<inter>D0))"
      by auto
    with assms(3)
      have  insert: "s`C0 = insert (s v) (C0\<inter>D0)" "D0 = insert (\<s> v) (C0\<inter>D0)"
      using basechambers_half_chamber_systems
            induced_automorphism_fixespointwise_C0_int_D0
            induced_automorphism_simplex_image(1)
      by    (auto simp add: fixespointwise_im)

    from chambers(2,3) have C0D0_C0: "(C0\<inter>D0) \<lhd> C0"
      using adjacent_int_facet1 by fast
    with assms(1) chambers(1) have "s`(C0\<inter>D0) \<lhd> s`C0"
      using ChamberComplexAutomorphism.facet_map by fast
    with assms(3) have C0D0_sC0: "(C0\<inter>D0) \<lhd> s`C0"
      by (simp add: fixespointwise_im)
    hence sv_nin_C0D0: "s v \<notin> C0\<inter>D0" using insert(1) facetrel_psubset by auto

    from assms(1) chambers(1) have "chamber (s`C0)"
      using ChamberComplexAutomorphism.chamber_map by fast
    moreover from chambers(2,3) have C0D0_D0: "(C0\<inter>D0) \<lhd> D0"
      using adjacent_sym adjacent_int_facet1 by (fastforce simp add: Int_commute)
    ultimately have "s`C0 = C0 \<or> s`C0 = D0"
      using chambers(1,3) chamber_D0 C0D0_C0 C0D0_sC0
            facet_unique_other_chamber[of "s`C0" "C0\<inter>D0" C0 D0]
      by    auto
    moreover have "\<not> s`C0 = C0"
    proof
      assume sC0: "s`C0 = C0"
      have "s = id"
      proof (
        rule standard_uniqueness_automorphs, rule assms(1),
        rule trivial_automorphism, rule chambers(1),
        rule fixespointwise_subset_and_diff_imp_eq_on,
        rule Int_lower1, rule assms(3), rule fixespointwiseI
      )
        fix a assume "a \<in> C0-(C0\<inter>D0)"
        with v have "a = v" using C0_insert by fast
        with sC0 show "s a = id a" using C0_insert sv_nin_C0D0 by auto
      qed
      with assms(1,2) show False by fast
    qed
    ultimately have sC0_D0: "s`C0 = D0" by fast

    have "\<s> v \<notin> C0\<inter>D0" using insert(2) C0D0_D0 facetrel_psubset by force
    thus "s v = \<s> v" using insert sC0_D0 sv_nin_C0D0 by auto
  qed
qed simp

lemma induced_automorphism_unique_automorphism:
  "\<lbrakk> ChamberComplexAutomorphism X s; s\<noteq>id; fixespointwise s (C0\<inter>D0) \<rbrakk>
    \<Longrightarrow> s = \<s>"
  using chambers(1) induced_automorphism_unique_automorphism'
        standard_uniqueness_automorphs induced_automorphism_automorphism
  by    fastforce

lemmas indaut_uniq_aut =
  induced_automorphism_unique_automorphism

lemma induced_automorphism_unique:
  "OpposedThinChamberComplexFoldings X f' g' C0 \<Longrightarrow> g'`C0 = g`C0 \<Longrightarrow>
    OpposedThinChamberComplexFoldings.induced_automorphism X f' g' = \<s>"
  using induced_automorphism_automorphism induced_automorphism_ntrivial
        induced_automorphism_fixespointwise_C0_int_D0
  by    (auto intro:
          OpposedThinChamberComplexFoldings.indaut_uniq_aut[
            THEN sym
          ]
        )

lemma induced_automorphism_sym:
  "OpposedThinChamberComplexFoldings.induced_automorphism X g f = \<s>"
  using OpposedThinChamberComplexFoldings.indaut_aut[
          OF fg_symmetric
        ]
        OpposedThinChamberComplexFoldings.induced_automorphism_ntrivial[
          OF fg_symmetric
        ]
        OpposedThinChamberComplexFoldings.indaut_fixes_fundfacet[
          OF fg_symmetric
        ]
        induced_automorphism_unique_automorphism
  by    (simp add: chambers(4) Int_commute)

lemma induced_automorphism_respects_labels:
  assumes "label_wrt B \<phi>" "v\<in>(\<Union>X)"
  shows   "\<phi> (\<s> v) = \<phi> v"
proof-
  from assms(2) obtain C where "chamber C" "v\<in>C" using simplex_in_max by fast
  with assms show ?thesis
    by  (simp add:
          induced_automorphism_on_chamber_vertices_f folding_f.respects_labels
          folding_g.respects_labels
        )
qed

lemmas indaut_resplabels =
  induced_automorphism_respects_labels

end (* context OpposedThinChamberComplexFoldings *)

subsubsection \<open>Walls\<close>

text \<open>
  A pair of opposed foldings of a thin chamber complex defines a decomposition of the chamber
  system into the two disjoint chamber system images. Call such a decomposition a wall, as we image
  that disjointness erects a wall between the two half chamber systems. By considering the
  collection of all possible opposed folding pairs, and their associated walls, we can obtain
  information about minimality of galleries by considering the walls they cross.
\<close>

context ThinChamberComplex
begin

definition foldpairs :: "(('a\<Rightarrow>'a) \<times> ('a\<Rightarrow>'a)) set"
  where "foldpairs \<equiv> {(f,g). \<exists>C. OpposedThinChamberComplexFoldings X f g C}"

abbreviation "walls \<equiv> \<Union>(f,g)\<in>foldpairs. {{f\<turnstile>\<C>,g\<turnstile>\<C>}}"
abbreviation "the_wall_betw C D \<equiv>
              THE_default {} (\<lambda>H. H\<in>walls \<and> separated_by H C D)"

definition walls_betw :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set set set"
  where "walls_betw C D \<equiv> {H\<in>walls. separated_by H C D}"

fun wall_crossings :: "'a set list \<Rightarrow> 'a set set set list"
  where "wall_crossings [] = []"
  |     "wall_crossings [C] = []"
  |     "wall_crossings (B#C#Cs) = the_wall_betw B C # wall_crossings (C#Cs)"

lemma foldpairs_sym: "(f,g)\<in>foldpairs \<Longrightarrow> (g,f)\<in>foldpairs"
  using foldpairs_def OpposedThinChamberComplexFoldings.fg_symmetric by fastforce

lemma not_self_separated_by_wall: "H\<in>walls \<Longrightarrow> \<not> separated_by H C C"
  using foldpairs_def OpposedThinChamberComplexFoldings.halfchsys_decomp(2)
        not_self_separated_by_disjoint
  by    force

lemma the_wall_betw_nempty:
  assumes "the_wall_betw C D \<noteq> {}"
  shows   "the_wall_betw C D \<in> walls" "separated_by (the_wall_betw C D) C D"
proof-
  from assms have 1: "\<exists>!H'\<in>walls. separated_by H' C D"
    using THE_default_none[of "\<lambda>H. H\<in>walls \<and> separated_by H C D" "{}"] by fast
  show "the_wall_betw C D \<in> walls" "separated_by (the_wall_betw C D) C D"
    using THE_defaultI'[OF 1] by auto
qed

lemma the_wall_betw_self_empty: "the_wall_betw C C = {}"
proof-
  {
    assume *: "the_wall_betw C C \<noteq> {}"
    then obtain f g
      where "(f,g)\<in>foldpairs" "the_wall_betw C C = {f\<turnstile>\<C>,g\<turnstile>\<C>}"
      using the_wall_betw_nempty(1)[of C C]
      by    blast
    with * have False
      using the_wall_betw_nempty(2)[of C C] foldpairs_def
            OpposedThinChamberComplexFoldings.halfchsys_decomp(2)[
              of X
            ]
            not_self_separated_by_disjoint[of "f\<turnstile>\<C>" "g\<turnstile>\<C>"]
      by    auto
  }
  thus ?thesis by fast
qed

lemma length_wall_crossings: "length (wall_crossings Cs) = length Cs - 1"
  by (induct Cs rule: list_induct_CCons) auto

lemma wall_crossings_snoc:
  "wall_crossings (Cs@[D,E]) = wall_crossings (Cs@[D]) @ [the_wall_betw D E]"
  by (induct Cs rule: list_induct_CCons) auto

lemma wall_crossings_are_walls:
  "H\<in>set (wall_crossings Cs) \<Longrightarrow> H\<noteq>{} \<Longrightarrow> H\<in>walls"
proof (induct Cs arbitrary: H rule: list_induct_CCons)
  case (CCons B C Cs) thus ?case
    using the_wall_betw_nempty(1)
    by    (cases "H\<in>set (wall_crossings (C#Cs))") auto
qed auto

lemma in_set_wall_crossings_decomp:
  "H\<in>set (wall_crossings Cs) \<Longrightarrow>
    \<exists>As A B Bs. Cs = As@[A,B]@Bs \<and> H = the_wall_betw A B"
proof (induct Cs rule: list_induct_CCons)
  case (CCons C D Ds)
  show ?case
  proof (cases "H \<in> set (wall_crossings (D#Ds))")
    case True
    with CCons(1) obtain As A B Bs
      where "C#(D#Ds) = (C#As)@[A,B]@Bs" "H = the_wall_betw A B"
      by    fastforce
    thus ?thesis by fast
  next
    case False
    with CCons(2) have "C#(D#Ds) = []@[C,D]@Ds" "H = the_wall_betw C D"
      by auto
    thus ?thesis by fast
  qed
qed auto

end (* context ThinChamberComplex *)

context OpposedThinChamberComplexFoldings
begin

lemma foldpair: "(f,g)\<in>foldpairs"
  unfolding foldpairs_def
proof-
  have "OpposedThinChamberComplexFoldings X f g C0" ..
  thus "(f, g) \<in> {(f, g).
          \<exists>C. OpposedThinChamberComplexFoldings X f g C}"
    by fast
qed

lemma separated_by_this_wall_fg:
  "separated_by {f\<turnstile>\<C>,g\<turnstile>\<C>} C D \<Longrightarrow> C\<in>f\<turnstile>\<C> \<Longrightarrow> D\<in>g\<turnstile>\<C>"
  using separated_by_disjoint[
          OF _ half_chamber_system_disjoint_union(2), of C D
        ]
  by    fast

lemmas separated_by_this_wall_gf =
  OpposedThinChamberComplexFoldings.separated_by_this_wall_fg[
    OF fg_symmetric
  ]

lemma induced_automorphism_this_wall_vertex:
  assumes "C\<in>f\<turnstile>\<C>" "D\<in>g\<turnstile>\<C>" "v\<in>C\<inter>D"
  shows   "\<s> v = v"
proof-
  from assms have "\<s> v = g v" 
    using chamber_system_simplices induced_automorphism_on_simplices_fg
    by    auto
  with assms(2,3) show "\<s> v = v"
    using chamber_system_simplices folding_g.retraction by auto
qed

lemmas indaut_wallvertex =
  induced_automorphism_this_wall_vertex

lemma unique_wall:
  assumes opp'    : "OpposedThinChamberComplexFoldings X f' g' C'"
  and     chambers: "A\<in>f\<turnstile>\<C>" "A\<in>f'\<turnstile>\<C>" "B\<in>g\<turnstile>\<C>" "B\<in>g'\<turnstile>\<C>" "A\<sim>B"
  shows   "{f\<turnstile>\<C>,g\<turnstile>\<C>} = {f'\<turnstile>\<C>,g'\<turnstile>\<C>}"
proof-
  from chambers have B: "B=g`A" "B=g'`A"
    using adjacent_sym[of A B] adjacent_half_chamber_system_image_gf
          OpposedThinChamberComplexFoldings.adjhalfchsys_image_gf[
            OF opp'
          ]
    by    auto
  with chambers(1,2,5)
    have  A : "OpposedThinChamberComplexFoldings X f g A"
    and   A': "OpposedThinChamberComplexFoldings X f' g' A"
    using switch_basechamber[of A]
          OpposedThinChamberComplexFoldings.switch_basechamber[
            OF opp', of A
          ]
    by    auto
  with B show ?thesis
    using OpposedThinChamberComplexFoldings.unique_half_chamber_system_f[
            OF A A'
          ]
          OpposedThinChamberComplexFoldings.unique_half_chamber_system_g[
            OF A A'
          ]
    by    auto
qed

end (* context OpposedThinChamberComplexFoldings *)

context ThinChamberComplex
begin

lemma separated_by_wall_ex_foldpair:
  assumes "H\<in>walls" "separated_by H C D"
  shows   "\<exists>(f,g)\<in>foldpairs. H = {f\<turnstile>\<C>,g\<turnstile>\<C>} \<and> C\<in>f\<turnstile>\<C> \<and> D\<in>g\<turnstile>\<C>"
proof-
  from assms(1) obtain f g where fg: "(f,g)\<in>foldpairs" "H = {f\<turnstile>\<C>,g\<turnstile>\<C>}" by auto
  show ?thesis
  proof (cases "C\<in>f\<turnstile>\<C>")
    case True
    moreover with fg assms(2) have "D\<in>g\<turnstile>\<C>"
      using foldpairs_def
            OpposedThinChamberComplexFoldings.separated_by_this_wall_fg[
              of X f g _ C D
            ]
      by    auto
    ultimately show ?thesis using fg by auto
  next
    case False with assms(2) fg show ?thesis
      using foldpairs_sym[of f g] separated_by_in_other[of "f\<turnstile>\<C>" "g\<turnstile>\<C>" C D] by auto
  qed
qed

lemma not_separated_by_wall_ex_foldpair:
  assumes chambers: "chamber C" "chamber D"
  and     wall    : "H\<in>walls" "\<not> separated_by H C D"
  shows   "\<exists>(f,g)\<in>foldpairs. H = {f\<turnstile>\<C>,g\<turnstile>\<C>} \<and> C\<in>f\<turnstile>\<C> \<and> D\<in>f\<turnstile>\<C>"
proof-
  from wall(1) obtain f g where fg: "(f,g)\<in>foldpairs" "H = {f\<turnstile>\<C>,g\<turnstile>\<C>}" by auto
  from fg(1) obtain A where A: "OpposedThinChamberComplexFoldings X f g A"
    using foldpairs_def by fast
  from chambers have chambers': "C\<in>f\<turnstile>\<C> \<or> C\<in>g\<turnstile>\<C>" "D\<in>f\<turnstile>\<C> \<or> D\<in>g\<turnstile>\<C>"
    using chamber_system_def
          OpposedThinChamberComplexFoldings.halfchsys_decomp(1)[
            OF A
          ]
    by    auto
  show ?thesis
  proof (cases "C\<in>f\<turnstile>\<C>")
    case True
    moreover with chambers'(2) fg(2) wall(2) have "D\<in>f\<turnstile>\<C>"
      unfolding separated_by_def by auto
    ultimately show ?thesis using fg by auto
  next
    case False
    with chambers'(1) have "C\<in>g\<turnstile>\<C>" by simp
    moreover with chambers'(2) fg(2) wall(2) have "D\<in>g\<turnstile>\<C>"
      using insert_commute[of "f\<turnstile>\<C>" "g\<turnstile>\<C>" "{}"] unfolding separated_by_def by auto
    ultimately show ?thesis using fg foldpairs_sym[of f g] by auto
  qed
qed

lemma adj_wall_imp_ex1_wall:
  assumes adj : "C\<sim>D"
  and     wall: "H0\<in>walls" "separated_by H0 C D"
  shows "\<exists>!H\<in>walls. separated_by H C D"
proof (rule ex1I, rule conjI, rule wall(1), rule wall(2))
  fix H assume H: "H\<in>walls \<and> separated_by H C D"
  from this obtain f g
    where fg: "(f,g)\<in>foldpairs" "H={f\<turnstile>\<C>,g\<turnstile>\<C>}" "C\<in>f\<turnstile>\<C>" "D\<in>g\<turnstile>\<C>"
    using separated_by_wall_ex_foldpair[of H C D]
    by    auto
  from wall obtain f0 g0
    where f0g0: "(f0,g0)\<in>foldpairs" "H0={f0\<turnstile>\<C>,g0\<turnstile>\<C>}" "C\<in>f0\<turnstile>\<C>" "D\<in>g0\<turnstile>\<C>"
    using separated_by_wall_ex_foldpair[of H0 C D]
    by    auto
  from fg(1) f0g0(1) obtain A A0
    where A : "OpposedThinChamberComplexFoldings X f  g  A"
    and   A0: "OpposedThinChamberComplexFoldings X f0 g0 A0"
    using foldpairs_def
    by    auto
  from fg(2-4) f0g0(2-4) adj show "H = H0"
    using OpposedThinChamberComplexFoldings.unique_wall[OF A0 A] by auto
qed

end (* context ThinChamberComplex *)

context OpposedThinChamberComplexFoldings
begin

lemma this_wall_betwI:
  assumes "C\<in>f\<turnstile>\<C>" "D\<in>g\<turnstile>\<C>" "C\<sim>D"
  shows   "the_wall_betw C D = {f\<turnstile>\<C>,g\<turnstile>\<C>}"
proof (rule THE_default1_equality, rule adj_wall_imp_ex1_wall)
  have "OpposedThinChamberComplexFoldings X f g C0" ..
  thus "{f\<turnstile>\<C>,g\<turnstile>\<C>}\<in>walls" using foldpairs_def by auto
  moreover from assms(1,2) show "separated_by {f\<turnstile>\<C>,g\<turnstile>\<C>} C D"
    by (auto intro: separated_byI)
  ultimately show "{f\<turnstile>\<C>,g\<turnstile>\<C>}\<in>walls \<and> separated_by {f\<turnstile>\<C>,g\<turnstile>\<C>} C D" by simp
qed (rule assms(3))

lemma this_wall_betw_basechambers:
  "the_wall_betw C0 D0 = {f\<turnstile>\<C>,g\<turnstile>\<C>}"
  using basechambers_half_chamber_systems chambers(2) this_wall_betwI by auto

lemma this_wall_in_crossingsI_fg:
  defines H: "H \<equiv> {f\<turnstile>\<C>,g\<turnstile>\<C>}"
  assumes D: "D\<in>g\<turnstile>\<C>"
  shows   "C\<in>f\<turnstile>\<C> \<Longrightarrow> gallery (C#Cs@[D]) \<Longrightarrow> H \<in> set (wall_crossings (C#Cs@[D]))"
proof (induct Cs arbitrary: C)
  case Nil
  from Nil(1) assms have "H\<in>walls" "separated_by H C D"
    using foldpair by (auto intro: separated_byI)
  thus ?case
    using galleryD_adj[OF Nil(2)]
          THE_default1_equality[OF adj_wall_imp_ex1_wall]
    by    auto
next
  case (Cons B Bs)
  show ?case
  proof (cases "B\<in>f\<turnstile>\<C>")
    case True with Cons(1,3) show ?thesis using gallery_Cons_reduce by simp
  next
    case False
    with Cons(2,3) H have "H\<in>walls" "separated_by H C B"
      using galleryD_chamber[OF Cons(3)] chamber_in_other_half_fg[of B] foldpair
      by    (auto intro: separated_byI)
    thus ?thesis
      using galleryD_adj[OF Cons(3)]
            THE_default1_equality[OF adj_wall_imp_ex1_wall]
      by    auto
  qed
qed

end (* context OpposedThinChamberComplexFoldings *)

lemma (in ThinChamberComplex) walls_betw_subset_wall_crossings:
  assumes "gallery (C#Cs@[D])"
  shows   "walls_betw C D \<subseteq> set (wall_crossings (C#Cs@[D]))"
proof
  fix H assume "H \<in> walls_betw C D"
  hence H: "H\<in>walls" "separated_by H C D" using walls_betw_def by auto
  from this obtain f g
    where fg: "(f,g)\<in>foldpairs" "H = {f\<turnstile>\<C>,g\<turnstile>\<C>}" "C\<in>f\<turnstile>\<C>" "D\<in>g\<turnstile>\<C>"
    using separated_by_wall_ex_foldpair[of H C D]
    by    auto
  from fg(1) obtain Z where Z: "OpposedThinChamberComplexFoldings X f g Z"
    using foldpairs_def by fast
  from assms H(2) fg(2-4) show "H \<in> set (wall_crossings (C#Cs@[D]))"
    using OpposedThinChamberComplexFoldings.this_wall_in_crossingsI_fg[OF Z]
    by    auto
qed

context OpposedThinChamberComplexFoldings
begin

lemma same_side_this_wall_wall_crossings_not_distinct_f:
  "gallery (C#Cs@[D]) \<Longrightarrow> C\<in>f\<turnstile>\<C> \<Longrightarrow> D\<in>f\<turnstile>\<C> \<Longrightarrow>
    {f\<turnstile>\<C>,g\<turnstile>\<C>}\<in>set (wall_crossings (C#Cs@[D])) \<Longrightarrow>
    \<not> distinct (wall_crossings (C#Cs@[D]))"
proof (induct Cs arbitrary: C)
  case Nil
  hence "{f\<turnstile>\<C>,g\<turnstile>\<C>} = the_wall_betw C D" by simp
  moreover hence "the_wall_betw C D \<noteq> {}" by fast
  ultimately show ?case
    using Nil(2,3) the_wall_betw_nempty(2) separated_by_this_wall_fg[of C D]
          half_chamber_system_disjoint_union(2)
    by    auto
next
  case (Cons E Es)
  show ?case
  proof
    assume 1: "distinct (wall_crossings (C # (E # Es) @ [D]))"
    show False
    proof (
      cases "E\<in>f\<turnstile>\<C>" "{f\<turnstile>\<C>,g\<turnstile>\<C>} \<in> set (wall_crossings (E#Es@[D]))"
      rule: two_cases
    )
      case both with Cons(1,2,4) 1 show False
        using gallery_Cons_reduce by simp
    next
      case one
      from one(2) Cons(5) have "{f\<turnstile>\<C>,g\<turnstile>\<C>} = the_wall_betw C E" by simp
      moreover hence "the_wall_betw C E \<noteq> {}" by fast
      ultimately show False
        using Cons(3) one(1) the_wall_betw_nempty(2)
              separated_by_this_wall_fg[of C E]
              half_chamber_system_disjoint_union(2)
        by    auto
    next
      case other with Cons(3) show False
        using 1 galleryD_chamber[OF Cons(2)] galleryD_adj[OF Cons(2)] 
              chamber_in_other_half_fg this_wall_betwI
        by    force
    next
      case neither
      from Cons(2) neither(1) have "E\<in>g\<turnstile>\<C>"
        using galleryD_chamber chamber_in_other_half_fg by auto
      with Cons(4) have "separated_by {g\<turnstile>\<C>,f\<turnstile>\<C>} E D"
        by (blast intro: separated_byI)
      hence "{f\<turnstile>\<C>,g\<turnstile>\<C>} \<in> walls_betw E D"
        using foldpair walls_betw_def by (auto simp add: insert_commute)
      with neither(2) show False
        using gallery_Cons_reduce[OF Cons(2)] walls_betw_subset_wall_crossings
        by    auto
    qed
  qed
qed

lemmas sside_wcrossings_ndistinct_f =
  same_side_this_wall_wall_crossings_not_distinct_f

lemma separated_by_this_wall_chain3_fg:
  assumes "B\<in>f\<turnstile>\<C>" "chamber C" "chamber D"
          "separated_by {f\<turnstile>\<C>,g\<turnstile>\<C>} B C" "separated_by {f\<turnstile>\<C>,g\<turnstile>\<C>} C D"
  shows   "C\<in>g\<turnstile>\<C>" "D\<in>f\<turnstile>\<C>"
  using   assms separated_by_this_wall_fg separated_by_this_wall_gf
  by      (auto simp add: insert_commute)

lemmas sepwall_chain3_fg =
  separated_by_this_wall_chain3_fg

end (* context OpposedThinChamberComplexFoldings *)

context ThinChamberComplex
begin

lemma wall_crossings_min_gallery_betwI:
  assumes "gallery (C#Cs@[D])"
          "distinct (wall_crossings (C#Cs@[D]))"
          "\<forall>H\<in>set (wall_crossings (C#Cs@[D])). separated_by H C D"
  shows   "min_gallery (C#Cs@[D])"
proof (rule min_galleryI_betw)
  obtain B Bs where BBs: "Cs@[D] = B#Bs" using snoc_conv_cons by fast
  define H where "H = the_wall_betw C B"
  with BBs assms(3) have 1: "separated_by H C D" by simp
  show "C\<noteq>D"
  proof (cases "H={}")
    case True thus ?thesis
      using 1 unfolding separated_by_def by simp
  next
    case False
    with H_def have "H \<in> walls" using the_wall_betw_nempty(1) by simp
    from this obtain f g
      where fg: "(f,g)\<in>foldpairs" "H = {f\<turnstile>\<C>,g\<turnstile>\<C>}" "C\<in>f\<turnstile>\<C>" "D\<in>g\<turnstile>\<C>"
      using 1 separated_by_wall_ex_foldpair[of H C D]
      by    auto
    thus ?thesis 
      using foldpairs_def 
            OpposedThinChamberComplexFoldings.halfchsys_decomp(2)[
              of X f g
            ]
      by    auto
  qed
next
  fix Ds assume Ds: "gallery (C # Ds @ [D])"
  have "Suc (length Cs) = card (walls_betw C D)"
  proof-
    from assms(1,3) have "set (wall_crossings (C#Cs@[D])) = walls_betw C D"
      using     separated_by_not_empty wall_crossings_are_walls[of _ "C#Cs@[D]"]
                walls_betw_def
                walls_betw_subset_wall_crossings[OF assms(1)]
      unfolding separated_by_def
      by        auto
    with assms(2) show ?thesis
      using distinct_card[THEN sym] length_wall_crossings by fastforce
  qed
  moreover have "card (walls_betw C D) \<le> Suc (length Ds)"
  proof-
    from Ds have "card (walls_betw C D) \<le> card (set (wall_crossings (C#Ds@[D])))"
      using walls_betw_subset_wall_crossings finite_set card_mono by force
    also have "\<dots> \<le> length (wall_crossings (C#Ds@[D]))"
      using card_length by auto
    finally show ?thesis using length_wall_crossings by simp
  qed
  ultimately show "length Cs \<le> length Ds" by simp
qed (rule assms(1))

lemma ex_nonseparating_wall_imp_wall_crossings_not_distinct:
  assumes gal : "gallery (C#Cs@[D])"
  and     wall: "H\<in>set (wall_crossings (C#Cs@[D]))" "H\<noteq>{}"
                "\<not> separated_by H C D"
  shows   "\<not> distinct (wall_crossings (C#Cs@[D]))"
proof-
  from assms obtain f g
    where fg: "(f,g)\<in>foldpairs" "H = {f\<turnstile>\<C>,g\<turnstile>\<C>}" "C\<in>f\<turnstile>\<C>" "D\<in>f\<turnstile>\<C>"
    using wall_crossings_are_walls[of H]
          not_separated_by_wall_ex_foldpair[of C D H]
          galleryD_chamber
    by    auto
  from fg(1) obtain Z where Z: "OpposedThinChamberComplexFoldings X f g Z"
    using foldpairs_def by fast
  from wall fg(2-4) show ?thesis
    using OpposedThinChamberComplexFoldings.sside_wcrossings_ndistinct_f [
            OF Z gal
          ]
    by    blast
qed

lemma not_min_gallery_double_crosses_wall:
  assumes "gallery Cs" "\<not> min_gallery Cs" "{} \<notin> set (wall_crossings Cs)"
  shows   "\<not> distinct (wall_crossings Cs)"
proof (cases Cs rule: list_cases_Cons_snoc)
  case Nil with assms(2) show ?thesis by simp
next
  case Single with assms(1,2) show ?thesis using galleryD_chamber by simp
next
  case (Cons_snoc B Bs C)
  show ?thesis
  proof (cases "B=C")
    case True show ?thesis
    proof (cases Bs)
      case Nil with True Cons_snoc assms(3) show ?thesis
        using the_wall_betw_self_empty by simp
    next
      case (Cons E Es)
      define H where "H = the_wall_betw B E"
      with Cons have *: "H \<in> set (wall_crossings (B#Bs@[C]))" by simp
      moreover from assms(3) Cons_snoc * have "H \<noteq> {}" by fast
      ultimately show ?thesis
        using assms(1) Cons_snoc Cons True H_def
              the_wall_betw_nempty(1)[of B E] not_self_separated_by_wall[of H B]
              ex_nonseparating_wall_imp_wall_crossings_not_distinct[of B Bs C H]
        by    fast
    qed
  next
    case False
    with assms Cons_snoc
      have  1: "\<not> distinct (wall_crossings Cs) \<or>
              \<not> (\<forall>H\<in>set (wall_crossings Cs). separated_by H B C)"
      using wall_crossings_min_gallery_betwI
      by    force
    moreover {
      assume "\<not> (\<forall>H\<in>set (wall_crossings Cs). separated_by H B C)"
      from this obtain H
        where H: "H\<in>set (wall_crossings Cs)" "\<not> separated_by H B C"
        by    auto
      moreover from H(1) assms(3) have "H\<noteq>{}" by fast
      ultimately have ?thesis
        using assms(1) Cons_snoc
              ex_nonseparating_wall_imp_wall_crossings_not_distinct
        by    simp
    }
    ultimately show ?thesis by fast
  qed
qed

lemma not_distinct_crossings_split_gallery:
  "\<lbrakk> gallery Cs; {} \<notin> set (wall_crossings Cs); \<not> distinct (wall_crossings Cs) \<rbrakk> \<Longrightarrow>
    \<exists>f g As A B Bs E F Fs.
      (f,g)\<in>foldpairs \<and> A\<in>f\<turnstile>\<C> \<and> B\<in>g\<turnstile>\<C> \<and> E\<in>g\<turnstile>\<C> \<and> F\<in>f\<turnstile>\<C> \<and>
      ( Cs = As@[A,B,F]@Fs \<or> Cs = As@[A,B]@Bs@[E,F]@Fs )"
proof (induct Cs rule: list_induct_CCons)
  case (CCons C J Js)
  show ?case
  proof (cases "distinct (wall_crossings (J#Js))")
    case False
    moreover from CCons(2) have "gallery (J#Js)"
      using gallery_Cons_reduce by simp
    moreover from CCons(3) have "{} \<notin> set (wall_crossings (J#Js))" by simp
    ultimately obtain f g As A B Bs E F Fs where split:
      "(f,g)\<in>foldpairs" "A\<in>f\<turnstile>\<C>" "B\<in>g\<turnstile>\<C>" "E\<in>g\<turnstile>\<C>" "F\<in>f\<turnstile>\<C>"
      "J#Js = As@[A,B,F]@Fs \<or> J#Js = As@[A,B]@Bs@[E,F]@Fs"
      using CCons(1)
      by    blast
    from split(6)
      have "C#J#Js = (C#As)@[A,B,F]@Fs \<or>
              C#J#Js = (C#As)@[A,B]@Bs@[E,F]@Fs"
      by   simp
    with split(1-5) show ?thesis by blast
  next
    case True
    define H where "H = the_wall_betw C J"
    with True CCons(4) have "H\<in>set (wall_crossings (J#Js))" by simp
    from this obtain Bs E F Fs
      where split1: "J#Js = Bs@[E,F]@Fs" "H = the_wall_betw E F"
      using in_set_wall_crossings_decomp
      by    fast
    from H_def split1(2) CCons(3)
      have  Hwall: "H \<in> walls" "separated_by H C J" "separated_by H E F"
      using the_wall_betw_nempty[of C J] the_wall_betw_nempty[of E F]
      by    auto
    from Hwall(1,2) obtain f g
      where fg: "(f,g)\<in>foldpairs" "H={f\<turnstile>\<C>,g\<turnstile>\<C>}" "C\<in>f\<turnstile>\<C>" "J\<in>g\<turnstile>\<C>"
      using separated_by_wall_ex_foldpair[of H C J]
      by    auto
    from fg(1) obtain Z
      where Z: "OpposedThinChamberComplexFoldings X f g Z"
      using foldpairs_def
      by    fast
    show ?thesis
    proof (cases Bs)
      case Nil
      with CCons(2) Hwall(2,3) fg(2-4) split1(1)
        have "F\<in>f\<turnstile>\<C>" "C#J#Js = []@[C,J,F]@Fs"
        using galleryD_chamber 
              OpposedThinChamberComplexFoldings.sepwall_chain3_fg(2)[
                OF Z, of C J F
              ]
        by    auto
      with fg(1,3,4) show ?thesis by blast
    next
      case (Cons K Ks) have Bs: "Bs = K#Ks" by fact
      show ?thesis
      proof (cases "E\<in>f\<turnstile>\<C>")
        case True
        from CCons(2) split1(1) Bs have "gallery (J#Ks@[E])"
          using gallery_Cons_reduce[of C "J#Ks@E#F#Fs"]
                gallery_append_reduce1[of "J#Ks@[E]" "F#Fs"]
          by    simp
        with fg(4) True obtain Ls L M Ms
          where LsLMMs: "L\<in>g\<turnstile>\<C>" "M\<in>f\<turnstile>\<C>" "J#Ks@[E] = Ls@L#M#Ms"
          using OpposedThinChamberComplexFoldings.split_gallery_gf[
                  OF Z, of J E Ks
                ]
          by    blast
        show ?thesis
        proof (cases Ls)
          case Nil
          with split1(1) Bs LsLMMs(3)
            have "C#J#Js = []@[C,J,M]@(Ms@F#Fs)"
            by   simp
          with fg(1,3,4) LsLMMs(2) show ?thesis by blast
        next
          case (Cons N Ns)
          with split1(1) Bs LsLMMs(3)
            have "C#J#Js = []@[C,J]@Ns@[L,M]@(Ms@F#Fs)"
            by   simp
          with fg(1,3,4) LsLMMs(1,2) show ?thesis by blast
        qed
      next
        case False
        with Hwall(2,3) fg(2) split1(1) Cons
          have  "E\<in>g\<turnstile>\<C>" "F\<in>f\<turnstile>\<C>" "C#J#Js = []@[C,J]@Ks@[E,F]@Fs"
          using OpposedThinChamberComplexFoldings.separated_by_this_wall_fg[
                  OF Z
                ]
                separated_by_in_other[of "f\<turnstile>\<C>" "g\<turnstile>\<C>"]
          by    auto
        with fg(1,3,4) show ?thesis by blast
      qed
    qed
  qed
qed auto

lemma not_min_gallery_double_split:
  "\<lbrakk> gallery Cs; \<not> min_gallery Cs; {} \<notin> set (wall_crossings Cs) \<rbrakk> \<Longrightarrow>
    \<exists>f g As A B Bs E F Fs.
      (f,g)\<in>foldpairs \<and> A\<in>f\<turnstile>\<C> \<and> B\<in>g\<turnstile>\<C> \<and> E\<in>g\<turnstile>\<C> \<and> F\<in>f\<turnstile>\<C> \<and>
      ( Cs = As@[A,B,F]@Fs \<or> Cs = As@[A,B]@Bs@[E,F]@Fs )"
  using not_min_gallery_double_crosses_wall not_distinct_crossings_split_gallery
  by    simp

end (* context ThinChamberComplex *)


subsection \<open>Thin chamber complexes with many foldings\<close>

text \<open>
  Here we begin to examine thin chamber complexes in which every pair of adjacent chambers affords a
  pair of opposed foldings of the complex. This condition will ultimately be shown to be sufficient
  to ensure that a thin chamber complex is isomorphic to some Coxeter complex.
\<close>

subsubsection \<open>Locale definition and basic facts\<close>

locale ThinChamberComplexManyFoldings = ThinChamberComplex X
  for   X  :: "'a set set"
+ fixes C0 :: "'a set"
  assumes fundchamber: "chamber C0"
  and     ex_walls   :
    "\<lbrakk> chamber C; chamber D; C\<sim>D; C\<noteq>D \<rbrakk> \<Longrightarrow>
      \<exists>f g. OpposedThinChamberComplexFoldings X f g C \<and> D=g`C"

lemma (in ThinChamberComplex) ThinChamberComplexManyFoldingsI:
  assumes "chamber C0"
  and     "\<And>C D. \<lbrakk> chamber C; chamber D; C\<sim>D; C\<noteq>D \<rbrakk> \<Longrightarrow>
            \<exists>f g. OpposedThinChamberComplexFoldings X f g C \<and> D=g`C"
  shows   "ThinChamberComplexManyFoldings X C0"
  using   assms
  by      (intro_locales, unfold_locales, fast)

lemma (in ThinChamberComplexManyFoldings) wall_crossings_subset_walls_betw:
  assumes "min_gallery (C#Cs@[D])"
  shows   "set (wall_crossings (C#Cs@[D])) \<subseteq> walls_betw C D"
proof
  fix H assume "H \<in> set (wall_crossings (C#Cs@[D]))"
  from this obtain As A B Bs
    where H: "C#Cs@[D] = As@[A,B]@Bs" "H=the_wall_betw A B" 
    using in_set_wall_crossings_decomp
    by    blast
  from assms have pgal: "pgallery (C#Cs@[D])"
    using min_gallery_pgallery by fast
  with H(1) obtain f g
    where fg: "OpposedThinChamberComplexFoldings X f g A" "B=g`A"
    using pgalleryD_chamber pgalleryD_adj
          binrelchain_append_reduce2[of adjacent As "[A,B]@Bs"]
          pgalleryD_distinct[of "As@[A,B]@Bs"] ex_walls[of A B]
    by    auto
  from H(2) fg have H': "A\<in>f\<turnstile>\<C>" "B\<in>g\<turnstile>\<C>" "H = {f\<turnstile>\<C>,g\<turnstile>\<C>}" "H\<in>walls"
    using OpposedThinChamberComplexFoldings.basech_halfchsys[
            OF fg(1)
          ]
          OpposedThinChamberComplexFoldings.chambers(2)[OF fg(1)]
          OpposedThinChamberComplexFoldings.this_wall_betwI[OF fg(1)]
          foldpairs_def
    by    auto
  have CD: "C \<in> f\<turnstile>\<C> \<union> g\<turnstile>\<C>" "D \<in> f\<turnstile>\<C> \<union> g\<turnstile>\<C>"
    using pgal pgalleryD_chamber chamber_system_def
          OpposedThinChamberComplexFoldings.halfchsys_decomp(1)[
            OF fg(1)
          ]
    by    auto
  show "H \<in> walls_betw C D"
  proof (cases Bs As rule: two_lists_cases_snoc_Cons')
    case both_Nil with H show ?thesis
      using H'(3) the_wall_betw_nempty[of A B] unfolding walls_betw_def by force
  next
    case (Nil1 E Es)
    show ?thesis
    proof (cases "C\<in>f\<turnstile>\<C>")
      case True
      with Nil1 H(1) have "separated_by H C D"
        using H'(2,3) by (auto intro: separated_byI)
      thus ?thesis using H'(4) unfolding walls_betw_def by simp
    next
      case False with assms Nil1 H(1) show ?thesis
        using OpposedThinChamberComplexFoldings.foldg[
                OF fg(1)
              ]
              CD(1) H'(1,2) pgal pgallery
              OpposedThinChamberComplexFoldings.flopped_half_chamber_systems_gf[
                OF fg(1)
              ]
              ThinChamberComplexFolding.gallery_double_cross_not_minimal1[
                of X g E A B Es "[]"
              ]
        by    force
    qed
  next
    case (Nil2 Fs F)
    show ?thesis
    proof (cases "D\<in>f\<turnstile>\<C>")
      case True
      with assms Nil2 H(1) show ?thesis
        using OpposedThinChamberComplexFoldings.foldf[
                OF fg(1)
              ]
              H'(1,2) pgal pgallery
              OpposedThinChamberComplexFoldings.flopped_half_chamber_systems_fg[
                OF fg(1)
              ]
              ThinChamberComplexFolding.gallery_double_cross_not_minimal_Cons1[
                of X f
              ]
        by    force
    next
      case False with Nil2 H(1) have "separated_by H C D"
        using CD(2) H'(1,3) by (auto intro: separated_byI)
      thus ?thesis using H'(4) unfolding walls_betw_def by simp
    qed
  next
    case (snoc_Cons Fs F E Es) show ?thesis
    proof (cases "C\<in>f\<turnstile>\<C>" "D\<in>g\<turnstile>\<C>" rule: two_cases)
      case both thus ?thesis
        using H'(3,4) walls_betw_def unfolding separated_by_def by auto
    next
      case one
      with snoc_Cons assms H(1) show ?thesis
        using OpposedThinChamberComplexFoldings.foldf[
                OF fg(1)
              ]
              CD(2) H'(2) pgal pgallery
              OpposedThinChamberComplexFoldings.flopped_half_chamber_systems_fg[
                OF fg(1)
              ]
              ThinChamberComplexFolding.gallery_double_cross_not_minimal1[
                of X f C B D "Es@[A]"
              ]
        by    fastforce
    next
      case other
      with snoc_Cons assms H(1) show ?thesis
        using OpposedThinChamberComplexFoldings.ThinChamberComplexFolding_g[
                OF fg(1)
              ]
              CD(1) H'(1) pgal pgallery
              OpposedThinChamberComplexFoldings.flopped_half_chamber_systems_gf[
                OF fg(1)
              ]
              ThinChamberComplexFolding.gallery_double_cross_not_minimal1[
                of X g E A F Es "B#Fs"
              ]
        by    force
    next
      case neither
      hence "separated_by {g\<turnstile>\<C>,f\<turnstile>\<C>} C D" using CD by (auto intro: separated_byI)
      thus ?thesis
        using H'(3,4) walls_betw_def by (auto simp add: insert_commute)
    qed
  qed
qed

subsubsection \<open>The group of automorphisms\<close>

text \<open>
  Recall that a pair of opposed foldings of a thin chamber complex can be stitched together to form
  an automorphism of the complex. Choosing an arbitrary chamber in the complex to act as a sort of
  centre of the complex (referred to as the fundamental chamber), we consider the group (under
  composition) generated by the automorphisms afforded by the chambers adjacent to the fundamental
  chamber via the pairs of opposed foldings that we have assumed to exist.
\<close>

context ThinChamberComplexManyFoldings
begin

definition fundfoldpairs :: "(('a\<Rightarrow>'a)\<times>('a\<Rightarrow>'a)) set"
  where "fundfoldpairs \<equiv> {(f,g). OpposedThinChamberComplexFoldings X f g C0}"

abbreviation "fundadjset \<equiv> adjacentset C0 - {C0}"

abbreviation induced_automorph :: "('a\<Rightarrow>'a) \<Rightarrow> ('a\<Rightarrow>'a) \<Rightarrow> ('a\<Rightarrow>'a)"
  where "induced_automorph f g \<equiv>
          OpposedThinChamberComplexFoldings.induced_automorphism X f g"

abbreviation Abs_induced_automorph :: "('a\<Rightarrow>'a) \<Rightarrow> ('a\<Rightarrow>'a) \<Rightarrow> 'a permutation"
  where "Abs_induced_automorph f g \<equiv> Abs_permutation (induced_automorph f g)"

abbreviation "S \<equiv> \<Union>(f,g)\<in>fundfoldpairs. {Abs_induced_automorph f g}"
abbreviation "W \<equiv> \<langle>S\<rangle>"

lemma fundfoldpairs_induced_autormorph_bij:
  "(f,g) \<in> fundfoldpairs \<Longrightarrow> bij (induced_automorph f g)"
  using     OpposedThinChamberComplexFoldings.induced_automorphism_bij
  unfolding fundfoldpairs_def
  by        fast

lemmas permutation_conv_induced_automorph =
  Abs_permutation_inverse[OF CollectI, OF fundfoldpairs_induced_autormorph_bij]

lemma fundfoldpairs_induced_autormorph_order2:
  "(f,g) \<in> fundfoldpairs \<Longrightarrow> induced_automorph f g \<circ> induced_automorph f g = id"
  using     OpposedThinChamberComplexFoldings.indaut_order2
  unfolding fundfoldpairs_def
  by        fast

lemma fundfoldpairs_induced_autormorph_ntrivial:
  "(f,g) \<in> fundfoldpairs \<Longrightarrow> induced_automorph f g \<noteq> id"
  using     OpposedThinChamberComplexFoldings.induced_automorphism_ntrivial
  unfolding fundfoldpairs_def
  by        fast

lemma fundfoldpairs_fundchamber_image:
  "(f,g)\<in>fundfoldpairs \<Longrightarrow> Abs_induced_automorph f g `\<rightarrow> C0 = g`C0"
  using fundfoldpairs_def
  by    (simp add:
          permutation_conv_induced_automorph
          OpposedThinChamberComplexFoldings.induced_automorphism_C0
        )

lemma fundfoldpair_fundchamber_in_half_chamber_system_f:
  "(f,g)\<in>fundfoldpairs \<Longrightarrow> C0\<in>f\<turnstile>\<C>"
  using fundfoldpairs_def
        OpposedThinChamberComplexFoldings.basech_halfchsys(1)
  by    fast

lemma fundfoldpair_unique_half_chamber_system_f:
  assumes "(f,g)\<in>fundfoldpairs" "(f',g')\<in>fundfoldpairs"
          "Abs_induced_automorph f' g' = Abs_induced_automorph f g"
  shows   "f'\<turnstile>\<C> = f\<turnstile>\<C>"
proof-
  from assms have "g'`C0 = g`C0"
    using fundfoldpairs_fundchamber_image[OF assms(1)]
          fundfoldpairs_fundchamber_image[OF assms(2)]
    by    simp
  with assms show "f'\<turnstile>\<C> = f\<turnstile>\<C>"
    using fundfoldpairs_def
          OpposedThinChamberComplexFoldings.unique_half_chamber_system_f[
            of X f g C0 f' g'
          ]
    by    auto
qed

lemma fundfoldpair_unique_half_chamber_systems_chamber_ng_f:
  assumes "(f,g)\<in>fundfoldpairs" "(f',g')\<in>fundfoldpairs"
          "Abs_induced_automorph f' g' = Abs_induced_automorph f g"
          "chamber C" "C\<notin>g\<turnstile>\<C>"
  shows   "C\<in>f'\<turnstile>\<C>"
  using assms(1,3-5) fundfoldpairs_def chamber_system_def
        OpposedThinChamberComplexFoldings.flopped_half_chamber_systems_gf[
          THEN sym
        ]
        fundfoldpair_unique_half_chamber_system_f[OF assms(1,2)]
  by    fastforce

lemma the_wall_betw_adj_fundchamber:
  "(f,g)\<in>fundfoldpairs \<Longrightarrow>
    the_wall_betw C0 (Abs_induced_automorph f g `\<rightarrow> C0) = {f\<turnstile>\<C>,g\<turnstile>\<C>}"
  using fundfoldpairs_def
        OpposedThinChamberComplexFoldings.this_wall_betw_basechambers
        OpposedThinChamberComplexFoldings.induced_automorphism_C0
  by    (fastforce simp add: permutation_conv_induced_automorph)

lemma zero_notin_S: "0\<notin>S"
proof
  assume "0\<in>S"
  from this obtain f g
    where "(f,g)\<in>fundfoldpairs" "0 = Abs_induced_automorph f g"
    by    fast
  thus False
    using Abs_permutation_inject[of id "induced_automorph f g"]
          bij_id fundfoldpairs_induced_autormorph_bij
          fundfoldpairs_induced_autormorph_ntrivial
    by    (force simp add: zero_permutation.abs_eq)
qed

lemma S_order2_add: "s\<in>S \<Longrightarrow> s + s = 0"
  using fundfoldpairs_induced_autormorph_bij zero_permutation.abs_eq
  by    (fastforce simp add:
          plus_permutation_abs_eq fundfoldpairs_induced_autormorph_order2
        )

lemma S_add_order2:
  assumes "s\<in>S"
  shows   "add_order s = 2"
proof (rule add_order_equality)
  from assms show "s+^2 = 0" using S_order2_add by (simp add: nataction_2)
next
  fix m assume "0 < m" "s+^m = 0"
  with assms show "2 \<le> m" using zero_notin_S by (cases "m=1") auto
qed simp

lemmas S_uminus = minus_unique[OF S_order2_add]

lemma S_sym: "uminus ` S \<subseteq> S"
  using S_uminus by auto

lemmas sum_list_S_in_W  = sum_list_lists_in_genby_sym[OF S_sym]
lemmas W_conv_sum_lists = genby_sym_eq_sum_lists[OF S_sym]

lemma S_endomorphism:
  "s\<in>S \<Longrightarrow> ChamberComplexEndomorphism X (permutation s)"
  using fundfoldpairs_def
        OpposedThinChamberComplexFoldings.induced_automorphism_morphism
  by    (fastforce simp add: permutation_conv_induced_automorph)

lemma S_list_endomorphism:
  "ss\<in>lists S \<Longrightarrow> ChamberComplexEndomorphism X (permutation (sum_list ss))"
  by  (induct ss)
      (auto simp add:
        zero_permutation.rep_eq trivial_endomorphism plus_permutation.rep_eq
        S_endomorphism ChamberComplexEndomorphism.endo_comp
      )

lemma W_endomorphism:
  "w\<in>W \<Longrightarrow> ChamberComplexEndomorphism X (permutation w)"
  using W_conv_sum_lists S_list_endomorphism by auto

lemma S_automorphism:
  "s\<in>S \<Longrightarrow> ChamberComplexAutomorphism X (permutation s)"
  using fundfoldpairs_def
        OpposedThinChamberComplexFoldings.induced_automorphism_automorphism
  by    (fastforce simp add: permutation_conv_induced_automorph)

lemma S_list_automorphism:
  "ss\<in>lists S \<Longrightarrow> ChamberComplexAutomorphism X (permutation (sum_list ss))"
  by  (induct ss)
      (auto simp add:
        zero_permutation.rep_eq trivial_automorphism plus_permutation.rep_eq
        S_automorphism ChamberComplexAutomorphism.comp
      )

lemma W_automorphism:
  "w\<in>W \<Longrightarrow> ChamberComplexAutomorphism X (permutation w)"
  using W_conv_sum_lists S_list_automorphism by auto

lemma S_respects_labels: "\<lbrakk> label_wrt B \<phi>; s\<in>S; v\<in>(\<Union>X) \<rbrakk> \<Longrightarrow> \<phi> (s \<rightarrow> v) = \<phi> v"
  using fundfoldpairs_def
        OpposedThinChamberComplexFoldings.indaut_resplabels[
          of X _ _ C0 B \<phi> v
        ]
  by    (auto simp add: permutation_conv_induced_automorph)

lemma S_list_respects_labels:
  "\<lbrakk> label_wrt B \<phi>; ss\<in>lists S; v\<in>(\<Union>X) \<rbrakk> \<Longrightarrow> \<phi> (sum_list ss \<rightarrow> v) = \<phi> v"
  using S_endomorphism ChamberComplexEndomorphism.vertex_map[of X]
  by    (induct ss arbitrary: v rule: rev_induct)
        (auto simp add:
          plus_permutation.rep_eq S_respects_labels zero_permutation.rep_eq
        )

lemma W_respects_labels:
  "\<lbrakk> label_wrt B \<phi>; w\<in>W; v\<in>(\<Union>X) \<rbrakk> \<Longrightarrow> \<phi> (w\<rightarrow>v) = \<phi> v"
  using W_conv_sum_lists S_list_respects_labels[of B \<phi> _ v] by auto

end (* context ThinChamberComplexManyFoldings *)

subsubsection \<open>Action of the group of automorphisms on the chamber system\<close>

text \<open>
  Now we examine the action of the group @{term W} on the chamber system. In particular, we show
  that the action is transitive.
\<close>


context ThinChamberComplexManyFoldings
begin

lemma fundchamber_S_chamber: "s\<in>S \<Longrightarrow> chamber (s`\<rightarrow>C0)"
  using fundfoldpairs_def
  by    (fastforce simp add: 
          fundfoldpairs_fundchamber_image
          OpposedThinChamberComplexFoldings.chamber_D0
        )

lemma fundchamber_W_image_chamber:
  "w\<in>W \<Longrightarrow> chamber (w`\<rightarrow>C0)"
  using fundchamber W_endomorphism
        ChamberComplexEndomorphism.chamber_map
  by    auto

lemma fundchamber_S_adjacent: "s\<in>S \<Longrightarrow> C0 \<sim> (s`\<rightarrow>C0)"
  using fundfoldpairs_def
  by    (auto simp add:
          fundfoldpairs_fundchamber_image
          OpposedThinChamberComplexFoldings.chambers(2)
        )

lemma fundchamber_WS_image_adjacent:
  "w\<in>W \<Longrightarrow> s\<in>S \<Longrightarrow> (w`\<rightarrow>C0) \<sim> ((w+s)`\<rightarrow>C0)"
  using fundchamber fundchamber_S_adjacent fundchamber_S_chamber
        W_endomorphism
        ChamberComplexEndomorphism.adj_map[of X "permutation w" C0 "s`\<rightarrow>C0"]
  by    (auto simp add: image_comp plus_permutation.rep_eq)

lemma fundchamber_S_image_neq_fundchamber: "s\<in>S \<Longrightarrow> s`\<rightarrow>C0 \<noteq> C0"
  using fundfoldpairs_def OpposedThinChamberComplexFoldings.chambers(3)
  by    (fastforce simp add: fundfoldpairs_fundchamber_image)

lemma fundchamber_next_WS_image_neq:
  assumes "s\<in>S"
  shows   "(w+s) `\<rightarrow> C0 \<noteq> w `\<rightarrow> C0"
proof
  assume "(w+s) `\<rightarrow> C0 = w `\<rightarrow> C0"
  with assms show False
    using fundchamber_S_image_neq_fundchamber[of s]
    by    (auto simp add: plus_permutation.rep_eq image_comp permutation_eq_image)
qed

lemma fundchamber_S_fundadjset: "s\<in>S \<Longrightarrow> s`\<rightarrow>C0 \<in> fundadjset"
  using fundchamber_S_adjacent fundchamber_S_image_neq_fundchamber
        fundchamber_S_chamber chamberD_simplex adjacentset_def
  by    simp

lemma fundadjset_eq_S_image: "D\<in>fundadjset \<Longrightarrow> \<exists>s\<in>S. D = s`\<rightarrow>C0"
  using fundchamber adjacentsetD_adj adjacentset_chamber ex_walls[of C0 D]
        fundfoldpairs_def fundfoldpairs_fundchamber_image
  by    blast

lemma S_fixespointwise_fundchamber_image_int:
  assumes "s\<in>S"
  shows   "fixespointwise ((\<rightarrow>) s) (C0\<inter>s`\<rightarrow>C0)"
proof-
  from assms(1) obtain f g
    where fg: "(f,g)\<in>fundfoldpairs" "s = Abs_induced_automorph f g"
    by    fast
  show ?thesis
  proof (rule fixespointwise_cong)
    from fg show "fun_eq_on ((\<rightarrow>) s) (induced_automorph f g) (C0\<inter>s`\<rightarrow>C0)"
      using permutation_conv_induced_automorph fun_eq_onI by fastforce
    from fg show "fixespointwise (induced_automorph f g) (C0\<inter>s`\<rightarrow>C0)"
      using fundfoldpairs_fundchamber_image fundfoldpairs_def
            OpposedThinChamberComplexFoldings.indaut_fixes_fundfacet
      by    auto
  qed
qed

lemma S_fixes_fundchamber_image_int:
  "s\<in>S \<Longrightarrow> s`\<rightarrow>(C0\<inter>s`\<rightarrow>C0) = C0\<inter>s`\<rightarrow>C0"
  using fixespointwise_im[OF S_fixespointwise_fundchamber_image_int] by simp

lemma fundfacets:
  assumes "s\<in>S"
  shows   "C0\<inter>s`\<rightarrow>C0 \<lhd> C0" "C0\<inter>s`\<rightarrow>C0 \<lhd> s`\<rightarrow>C0"
  using   assms fundchamber_S_adjacent[of s]
          fundchamber_S_image_neq_fundchamber[of s]
          adjacent_int_facet1[of C0] adjacent_int_facet2[of C0]
  by      auto

lemma fundadjset_ex1_eq_S_image:
  assumes "D\<in>fundadjset"
  shows   "\<exists>!s\<in>S. D = s`\<rightarrow>C0"
proof (rule ex_ex1I)
  from assms show "\<exists>s. s\<in>S \<and> D = s `\<rightarrow> C0"
    using fundadjset_eq_S_image by fast
next
  fix s t assume "s\<in>S \<and> D = s`\<rightarrow>C0" "t\<in>S \<and> D = t`\<rightarrow>C0"
  hence s: "s\<in>S" "D = s`\<rightarrow>C0"
    and t: "t\<in>S" "D = t`\<rightarrow>C0"
    by  auto
  from s(1) t(1) obtain f g f' g'
    where "(f,g)\<in>fundfoldpairs" "s = Abs_induced_automorph f  g"
    and   "(f',g')\<in>fundfoldpairs" "t = Abs_induced_automorph f' g'"
    by    auto
  with s(2) t(2) show "s=t"
      using fundfoldpairs_def fundfoldpairs_fundchamber_image
            OpposedThinChamberComplexFoldings.induced_automorphism_unique[
              of X f' g' C0 f g
            ]
      by    auto
qed

lemma fundchamber_S_image_inj_on: "inj_on (\<lambda>s. s`\<rightarrow>C0) S"
proof (rule inj_onI)
  fix s t assume "s\<in>S" "t\<in>S" "s`\<rightarrow>C0 = t`\<rightarrow>C0" thus "s=t"
    using fundchamber_S_fundadjset
          bex1_equality[OF fundadjset_ex1_eq_S_image, of "s`\<rightarrow>C0" s t]
    by    simp
qed

lemma S_list_image_gallery:
  "ss\<in>lists S \<Longrightarrow> gallery (map (\<lambda>w. w`\<rightarrow>C0) (sums ss))"
proof (induct ss rule: list_induct_ssnoc)
  case (Single s) thus ?case
    using fundchamber fundchamber_S_chamber fundchamber_S_adjacent
          gallery_def
    by    (fastforce simp add: zero_permutation.rep_eq)
next
  case (ssnoc ss s t)
  define Cs D E where "Cs = map (\<lambda>w. w `\<rightarrow> C0) (sums ss)"
    and "D = sum_list (ss@[s]) `\<rightarrow> C0"
    and "E = sum_list (ss@[s,t]) `\<rightarrow> C0"
  with ssnoc have "gallery (Cs@[D,E])"
    using sum_list_S_in_W[of "ss@[s,t]"] sum_list_S_in_W[of "ss@[s]"]
          fundchamber_W_image_chamber
          fundchamber_WS_image_adjacent[of "sum_list (ss@[s])" t]
          sum_list_append[of "ss@[s]" "[t]"]
    by    (auto intro: gallery_snocI simp add: sums_snoc)
  with Cs_def D_def E_def show ?case using sums_snoc[of "ss@[s]" t] by (simp add: sums_snoc)
qed (auto simp add: gallery_def fundchamber zero_permutation.rep_eq)

lemma pgallery_last_eq_W_image:
  "pgallery (C0#Cs@[C]) \<Longrightarrow> \<exists>w\<in>W. C = w`\<rightarrow>C0"
proof (induct Cs arbitrary: C rule: rev_induct)
  case Nil
  hence "C\<in>fundadjset"
    using pgallery_def chamberD_simplex adjacentset_def by fastforce
  from this obtain s where "s\<in>S" "C = s`\<rightarrow>C0"
    using fundadjset_eq_S_image[of C] by auto
  thus ?case using genby_genset_closed[of s S] by fast
next
  case (snoc D Ds)
  have DC: "chamber D" "chamber C" "D\<sim>C" "D\<noteq>C"
    using pgallery_def snoc(2)
          binrelchain_append_reduce2[of adjacent "C0#Ds" "[D,C]"]
    by    auto
  from snoc obtain w where w: "w\<in>W" "D = w`\<rightarrow>C0"
    using pgallery_append_reduce1[of "C0#Ds@[D]" "[C]"] by force
  from w(2) have "(-w)`\<rightarrow>D = C0"
    by  (simp add:
          image_comp plus_permutation.rep_eq[THEN sym]
          zero_permutation.rep_eq
        )
  with DC w(1) have "C0 \<sim> (-w)`\<rightarrow>C" "C0 \<noteq> (-w)`\<rightarrow>C" "(-w)`\<rightarrow>C \<in> X"
    using genby_uminus_closed W_endomorphism[of "-w"]
          ChamberComplexEndomorphism.adj_map[of X _ D C]
          permutation_eq_image[of "-w" D] chamberD_simplex[of C]
          ChamberComplexEndomorphism.simplex_map[of X "permutation (-w)" C]
    by    auto
  hence "(-w)`\<rightarrow>C \<in> fundadjset" using adjacentset_def by fast
  from this obtain s where s: "s\<in>S" "(-w)`\<rightarrow>C = s`\<rightarrow>C0"
    using fundadjset_eq_S_image by force
  from s(2) have
    "(permutation w \<circ> permutation (-w))`C = (permutation w \<circ> permutation s)`C0"
    by (simp add: image_comp[THEN sym])
  hence "C = (w+s)`\<rightarrow>C0"
    by (simp add: plus_permutation.rep_eq[THEN sym] zero_permutation.rep_eq)
  with w(1) s(1) show ?case
    using genby_genset_closed[of s S] genby_add_closed by blast
qed

lemma chamber_eq_W_image:
  assumes "chamber C"
  shows   "\<exists>w\<in>W. C = w`\<rightarrow>C0"
proof (cases "C=C0")
  case True
  hence "0\<in>W" "C = 0`\<rightarrow>C0"
    using genby_0_closed by (auto simp add: zero_permutation.rep_eq)
  thus ?thesis by fast
next  
  case False with assms show ?thesis
    using fundchamber chamber_pconnect pgallery_last_eq_W_image by blast
qed

lemma S_list_image_crosses_walls:
  "ss \<in> lists S \<Longrightarrow> {} \<notin> set (wall_crossings (map (\<lambda>w. w`\<rightarrow>C0) (sums ss)))"
proof (induct ss rule: list_induct_ssnoc)
  case (Single s) thus ?case
    using fundchamber fundchamber_S_chamber fundchamber_S_adjacent
          fundchamber_S_image_neq_fundchamber[of s] ex_walls[of C0 "s`\<rightarrow>C0"]
          OpposedThinChamberComplexFoldings.this_wall_betw_basechambers
    by    (force simp add: zero_permutation.rep_eq)
next
  case (ssnoc ss s t)
  moreover
  define A B where "A = sum_list (ss@[s]) `\<rightarrow> C0" and "B = sum_list (ss@[s,t]) `\<rightarrow> C0"
  moreover from ssnoc(2) A_def B_def obtain f g
    where "OpposedThinChamberComplexFoldings X f g A" "B=g`A"
    using sum_list_S_in_W[of "ss@[s]"] sum_list_S_in_W[of "ss@[s,t]"]
          fundchamber_W_image_chamber sum_list_append[of "ss@[s]" "[t]"]
          fundchamber_next_WS_image_neq[of t "sum_list (ss@[s])"]
          fundchamber_WS_image_adjacent[of "sum_list (ss@[s])" t]
          ex_walls[of A B]
    by    auto
  ultimately show ?case
    using OpposedThinChamberComplexFoldings.this_wall_betw_basechambers
          sums_snoc[of "ss@[s]" t]
    by    (force simp add: sums_snoc wall_crossings_snoc)
qed (simp add: zero_permutation.rep_eq)

end (* context ThinChamberComplexManyFoldings *)

subsubsection \<open>A labelling by the vertices of the fundamental chamber\<close>

text \<open>
  Here we show that by repeatedly applying the composition of all the elements in the collection
  @{term S} of fundamental automorphisms, we can retract the entire chamber complex onto the
  fundamental chamber. This retraction provides a means of labelling the chamber complex, using the
  vertices of the fundamental chamber as labels.
\<close>

context ThinChamberComplexManyFoldings
begin

definition Spair :: "'a permutation \<Rightarrow> ('a\<Rightarrow>'a)\<times>('a\<Rightarrow>'a)"
  where "Spair s \<equiv>
          SOME fg. fg \<in> fundfoldpairs \<and> s = case_prod Abs_induced_automorph fg"

lemma Spair_fundfoldpair: "s\<in>S \<Longrightarrow> Spair s \<in> fundfoldpairs"
  using Spair_def
        someI_ex[of
          "\<lambda>fg. fg \<in> fundfoldpairs \<and>
            s = case_prod Abs_induced_automorph fg"
        ]
  by    auto

lemma Spair_induced_automorph:
  "s\<in>S \<Longrightarrow> s = case_prod Abs_induced_automorph (Spair s)"
  using Spair_def
        someI_ex[of
          "\<lambda>fg. fg \<in> fundfoldpairs \<and>
            s = case_prod Abs_induced_automorph fg"
        ]
  by    auto

lemma S_list_pgallery_decomp1:
  assumes ss: "set ss = S" and gal: "Cs\<noteq>[]" "pgallery (C0#Cs)"
  shows   "\<exists>s\<in>set ss. \<exists>C\<in>set Cs. \<forall>(f,g)\<in>fundfoldpairs.
            s = Abs_induced_automorph f g \<longrightarrow> C \<in> g\<turnstile>\<C>"
proof (cases Cs)
  case (Cons D Ds)
  with gal(2) have "D\<in>fundadjset"
    using pgallery_def chamberD_simplex adjacentset_def by fastforce
  from this obtain s where s: "s\<in>S" "D = s`\<rightarrow>C0"
    using fundadjset_eq_S_image by blast
  from s(2) have
    "\<forall>(f,g)\<in>fundfoldpairs. s = Abs_induced_automorph f g \<longrightarrow> D\<in>g\<turnstile>\<C>"
    using fundfoldpairs_def fundfoldpairs_fundchamber_image 
          OpposedThinChamberComplexFoldings.basechambers_half_chamber_systems(2)
    by    auto
  with s(1) ss Cons show ?thesis by auto
qed (simp add: gal(1))

lemma S_list_pgallery_decomp2:
  assumes "set ss = S" "Cs\<noteq>[]" "pgallery (C0#Cs)"
  shows
    "\<exists>rs s ts. ss = rs@s#ts \<and>
      (\<exists>C\<in>set Cs. \<forall>(f,g)\<in>fundfoldpairs.
        s = Abs_induced_automorph f g \<longrightarrow> C \<in> g\<turnstile>\<C>) \<and>
        (\<forall>r\<in>set rs. \<forall>C\<in>set Cs. \<forall>(f,g)\<in>fundfoldpairs.
          r = Abs_induced_automorph f g \<longrightarrow> C\<in>f\<turnstile>\<C>)"
proof-
  from assms obtain rs s ts  where rs_s_ts:
    "ss = rs@s#ts"
    "\<exists>C\<in>set Cs. \<forall>(f,g)\<in>fundfoldpairs.
      s = Abs_induced_automorph f g \<longrightarrow> C \<in> g\<turnstile>\<C>"
    "\<forall>r\<in>set rs. \<forall>C\<in>set Cs.
      \<not> (\<forall>(f,g)\<in>fundfoldpairs. r = Abs_induced_automorph f g \<longrightarrow> C \<in> g\<turnstile>\<C>)"
    using split_list_first_prop[OF S_list_pgallery_decomp1, of ss Cs]
    by    auto
  have "\<forall>r\<in>set rs. \<forall>C\<in>set Cs. \<forall>(f,g)\<in>fundfoldpairs.
          r = Abs_induced_automorph f g \<longrightarrow> C\<in>f\<turnstile>\<C>"
  proof (rule ballI, rule ballI, rule prod_ballI, rule impI)
    fix r C f g
    assume  "r \<in> set rs" "C \<in> set Cs" "(f,g)\<in>fundfoldpairs"
            "r = Abs_induced_automorph f g"
    with rs_s_ts(3) assms(3) show "C\<in>f\<turnstile>\<C>"
      using pgalleryD_chamber
            fundfoldpair_unique_half_chamber_systems_chamber_ng_f[
              of _ _ f g C
            ]
      by    fastforce
  qed
  with rs_s_ts(1,2) show ?thesis by auto
qed

lemma S_list_pgallery_decomp3:
  assumes "set ss = S" "Cs\<noteq>[]" "pgallery (C0#Cs)"
  shows
    "\<exists>rs s ts As B Bs. ss = rs@s#ts \<and> Cs = As@B#Bs \<and>
      (\<forall>(f,g)\<in>fundfoldpairs. s = Abs_induced_automorph f g \<longrightarrow> B\<in>g\<turnstile>\<C>) \<and>
      (\<forall>A\<in>set As. \<forall>(f,g)\<in>fundfoldpairs.
        s = Abs_induced_automorph f g \<longrightarrow> A\<in>f\<turnstile>\<C>) \<and>
      (\<forall>r\<in>set rs. \<forall>C\<in>set Cs. \<forall>(f,g)\<in>fundfoldpairs.
        r = Abs_induced_automorph f g \<longrightarrow> C\<in>f\<turnstile>\<C>)"
proof-
  from assms obtain rs s ts where rs_s_ts:
    "ss = rs@s#ts"
    "\<exists>B\<in>set Cs. \<forall>(f,g)\<in>fundfoldpairs. s = Abs_induced_automorph f g \<longrightarrow> B \<in> g\<turnstile>\<C>"
    "\<forall>r\<in>set rs. \<forall>B\<in>set Cs. \<forall>(f,g)\<in>fundfoldpairs.
      r = Abs_induced_automorph f g \<longrightarrow> B\<in>f\<turnstile>\<C>"
    using S_list_pgallery_decomp2[of ss Cs]
    by    auto
  obtain As B Bs where As_B_Bs:
    "Cs = As@B#Bs"
    "\<forall>(f,g)\<in>fundfoldpairs. s = Abs_induced_automorph f g \<longrightarrow> B \<in> g\<turnstile>\<C>"
    "\<forall>A\<in>set As. \<exists>(f,g)\<in>fundfoldpairs. s = Abs_induced_automorph f g \<and> A\<notin>g\<turnstile>\<C>"
    using split_list_first_prop[OF rs_s_ts(2)]
    by    fastforce
  from As_B_Bs(1,3) assms(3)
    have "\<forall>A\<in>set As. \<forall>(f,g)\<in>fundfoldpairs.
          s = Abs_induced_automorph f g \<longrightarrow> A\<in>f\<turnstile>\<C>"
      using pgalleryD_chamber
            fundfoldpair_unique_half_chamber_systems_chamber_ng_f
      by    auto
  with rs_s_ts(1,3) As_B_Bs(1,2) show ?thesis by fast
qed

lemma fundfold_trivial_f\<C>:
  "r\<in>S \<Longrightarrow> \<forall>(f,g)\<in>fundfoldpairs. r = Abs_induced_automorph f g \<longrightarrow> C\<in>f\<turnstile>\<C> \<Longrightarrow>
    fst (Spair r) ` C = C"
  using Spair_fundfoldpair[of r] Spair_induced_automorph[of r] fundfoldpairs_def
        OpposedThinChamberComplexFoldings.axioms(2)[
          of X "fst (Spair r)" "snd (Spair r)" C0
        ]
        ChamberComplexFolding.chamber_retraction2[of X "fst (Spair r)" C]
  by    fastforce

lemma fundfold_comp_trivial_f\<C>:
  "set rs \<subseteq> S \<Longrightarrow>
    \<forall>r\<in>set rs. \<forall>(f,g)\<in>fundfoldpairs.
      r = Abs_induced_automorph f g \<longrightarrow> C\<in>f\<turnstile>\<C> \<Longrightarrow>
    fold fst (map Spair rs) ` C = C"
proof (induct rs)
  case (Cons r rs)
  have "fold fst (map Spair (r#rs)) ` C =
          fold fst (map Spair rs) ` fst (Spair r) ` C"
    by (simp add: image_comp)
  also from Cons have "\<dots> = C" by (simp add: fundfold_trivial_f\<C>)
  finally show ?case by fast
qed simp

lemma fundfold_trivial_f\<C>_list:
  "r\<in>S \<Longrightarrow>
    \<forall>C\<in>set Cs. \<forall>(f,g)\<in>fundfoldpairs.
      r = Abs_induced_automorph f g \<longrightarrow> C\<in>f\<turnstile>\<C> \<Longrightarrow>
    fst (Spair r) \<Turnstile> Cs = Cs"
  using fundfold_trivial_f\<C> by (induct Cs) auto

lemma fundfold_comp_trivial_f\<C>_list:
  "set rs \<subseteq> S \<Longrightarrow>
    \<forall>r\<in>set rs. \<forall>C\<in>set Cs. \<forall>(f,g)\<in>fundfoldpairs.
      r = Abs_induced_automorph f g \<longrightarrow> C\<in>f\<turnstile>\<C> \<Longrightarrow>
    fold fst (map Spair rs) \<Turnstile> Cs = Cs"
proof (induct rs Cs rule: list_induct2')
  case (4 r rs C Cs)
  from 4(3)
    have  r: "\<forall>D\<in>set (C#Cs). \<forall>(f,g)\<in>fundfoldpairs.
              r = Abs_induced_automorph f g \<longrightarrow> D\<in>f\<turnstile>\<C>"
    by    simp
  from 4(2)
    have  "fold fst (map Spair (r#rs)) \<Turnstile> (C#Cs) =
            map ((`) (fold fst (map Spair rs))) (fst (Spair r) \<Turnstile> (C#Cs))"
    by    (auto simp add: image_comp)
  also from 4 have "\<dots> = C#Cs"
    using fundfold_trivial_f\<C>_list[of r "C#Cs"]
    by    (simp add: fundfold_comp_trivial_f\<C>)
  finally show ?case by fast
qed auto

lemma fundfold_gallery_map:
  "s\<in>S \<Longrightarrow> gallery Cs \<Longrightarrow> gallery (fst (Spair s) \<Turnstile> Cs)"
  using Spair_fundfoldpair fundfoldpairs_def
        OpposedThinChamberComplexFoldings.axioms(2)
        ChamberComplexFolding.gallery_map[of X "fst (Spair s)"]
  by    fastforce

lemma fundfold_comp_gallery_map:
  assumes pregal: "gallery Cs"
  shows   "set ss \<subseteq> S \<Longrightarrow> gallery (fold fst (map Spair ss) \<Turnstile> Cs)"
proof (induct ss rule: rev_induct)
  case (snoc s ss)
  hence 1: "gallery (fst (Spair s) \<Turnstile> (fold fst (map Spair ss) \<Turnstile> Cs))"
    using fundfold_gallery_map by fastforce
  have 2: "fst (Spair s) \<Turnstile> (fold fst (map Spair ss) \<Turnstile> Cs) =
            fold fst (map Spair (ss@[s])) \<Turnstile> Cs"
    by (simp add: image_comp)
  show ?case using 1 subst[OF 2, of gallery, OF 1] by fast
qed (simp add: pregal galleryD_adj)

lemma fundfold_comp_pgallery_ex_funpow:
  assumes ss: "set ss = S"
  shows   "pgallery (C0#Cs@[C]) \<Longrightarrow>
            \<exists>n. (fold fst (map Spair ss) ^^ n) ` C = C0"
proof (induct Cs arbitrary: C rule: length_induct)
  fix Cs C
  assume step  :  "\<forall>ys. length ys < length Cs \<longrightarrow>
                    (\<forall>x. pgallery (C0 # ys @ [x]) \<longrightarrow>
                    (\<exists>n. (fold fst (map Spair ss) ^^ n) ` x = C0))"
    and  set_up:  "pgallery (C0#Cs@[C])"
  from ss set_up obtain rs s ts As B Bs where decomps:
    "ss = rs@s#ts" "Cs@[C] = As@B#Bs"
    "\<forall>(f,g)\<in>fundfoldpairs. s = Abs_induced_automorph f g \<longrightarrow> B\<in>g\<turnstile>\<C>"
    "\<forall>A\<in>set As. \<forall>(f,g)\<in>fundfoldpairs. s = Abs_induced_automorph f g \<longrightarrow> A\<in>f\<turnstile>\<C>"
    "\<forall>r\<in>set rs. \<forall>D\<in>set (Cs@[C]). \<forall>(f,g)\<in>fundfoldpairs.
      r = Abs_induced_automorph f g \<longrightarrow> D\<in>f\<turnstile>\<C>"
    using S_list_pgallery_decomp3[of ss "Cs@[C]"]
    by    fastforce
  obtain Es E where EsE: "C0#As = Es@[E]" using cons_conv_snoc by fast

  have EsE_s_f\<C>:
    "\<forall>A\<in>set (Es@[E]). \<forall>(f,g)\<in>fundfoldpairs.
      s = Abs_induced_automorph f g \<longrightarrow> A\<in>f\<turnstile>\<C>"
  proof (rule ballI)
    fix A assume "A\<in>set (Es@[E])"
    with EsE decomps(4)
      show  "\<forall>(f, g)\<in>fundfoldpairs. s = Abs_induced_automorph f g \<longrightarrow> A \<in> f \<turnstile> \<C>"
      using fundfoldpair_fundchamber_in_half_chamber_system_f
            set_ConsD[of A C0 As]
      by    auto
  qed
  moreover from decomps(2) EsE
    have  decomp2: "C0#Cs@[C] = Es@E#B#Bs"
    by    simp
  moreover from ss decomps(1) have "s\<in>S" by auto
  ultimately have sB: "fst (Spair s) ` B = E"
    using set_up decomps(3) Spair_fundfoldpair[of s]
          Spair_induced_automorph[of s] fundfoldpairs_def
          pgalleryD_adj
          binrelchain_append_reduce2[of adjacent Es "E#B#Bs"]
          OpposedThinChamberComplexFoldings.adjacent_half_chamber_system_image_fg[
            of X "fst (Spair s)" "snd (Spair s)" C0 E B
          ]
    by    auto

  show "\<exists>n. (fold fst (map Spair ss) ^^ n) ` C = C0"
  proof (cases "Es=[] \<and> Bs = []")
    case True
    from decomps(5) have
      "\<forall>r\<in>set rs. \<forall>(f,g)\<in>fundfoldpairs. r = Abs_induced_automorph f g \<longrightarrow> C\<in>f\<turnstile>\<C>"
      by auto
    with decomps(1) ss
      have  "fold fst (map Spair ss) ` C = fold fst (map Spair ts) ` fst (Spair s) ` C"
      using fundfold_comp_trivial_f\<C>[of rs C]
      by    (fastforce simp add: image_comp[THEN sym])
    moreover
      have  "\<forall>r\<in>set ts. \<forall>(f,g)\<in>fundfoldpairs.
              r = Abs_induced_automorph f g \<longrightarrow> C0\<in>f\<turnstile>\<C>"
      using fundfoldpair_fundchamber_in_half_chamber_system_f
      by    fast
    ultimately have "(fold fst (map Spair ss) ^^ 1) ` C = C0"
      using True decomps(1,2) ss EsE sB fundfold_comp_trivial_f\<C>[of ts C0]
            fundfold_comp_trivial_f\<C>[of ts C0]
      by    fastforce
    thus ?thesis by fast
  next
    case False have EsBs: "\<not> (Es = [] \<and> Bs = [])" by fact
    show ?thesis
    proof (cases "fold fst (map Spair ss) ` C = C0")
      case True
      hence "(fold fst (map Spair ss) ^^ 1) ` C = C0" by simp
      thus ?thesis by fast
    next
      case False
      from decomps(5) have C0CsC_rs_f\<C>:
        "\<forall>r\<in>set rs. \<forall>D\<in>set (C0#Cs@[C]). \<forall>(f,g)\<in>fundfoldpairs. 
          r = Abs_induced_automorph f g \<longrightarrow> D\<in>f\<turnstile>\<C>"
        using fundfoldpair_fundchamber_in_half_chamber_system_f
        by    auto
      from decomps(1)
        have  "fold fst (map Spair (rs@[s])) \<Turnstile> (C0#Cs@[C]) =
                fst (Spair s) \<Turnstile> (fold fst (map Spair rs) \<Turnstile> (C0#Cs@[C]))"
        by    (simp add: image_comp)
      also from ss decomps(1)
        have  "\<dots> =  fst (Spair s) \<Turnstile> (C0#Cs@[C])"
        using C0CsC_rs_f\<C> fundfold_comp_trivial_f\<C>_list[of rs "C0#Cs@[C]"]
        by    fastforce
      also from decomp2 have "\<dots> =  fst (Spair s) \<Turnstile> (Es@E#B#Bs)"
        by (simp add: image_comp)
      finally
        have  "fold fst (map Spair (rs@[s])) \<Turnstile> (C0#Cs@[C]) =
                Es @ E # E # fst (Spair s) \<Turnstile> Bs"
        using decomps(1) ss sB EsE_s_f\<C> fundfold_trivial_f\<C>_list[of s "Es@[E]"]
        by    fastforce
      with set_up ss decomps(1)
        have  gal: "gallery (Es @ E # fst (Spair s) \<Turnstile> Bs)"
        using pgallery fundfold_comp_gallery_map[of _ "rs@[s]"]
              gallery_remdup_adj[of Es E "fst (Spair s) \<Turnstile> Bs"]
        by    fastforce

      from EsBs decomp2 EsE
        have  "\<exists>Zs. length Zs < length Cs \<and>
                Es @ E # fst (Spair s) \<Turnstile> Bs = C0 # Zs @ [fst (Spair s) ` C]"
        using sB
        by    (cases Bs Es rule: two_lists_cases_snoc_Cons') auto
      from this obtain Zs where Zs:
        "length Zs < length Cs"
        "Es @ E # fst (Spair s) \<Turnstile> Bs = C0 # Zs @ [fst (Spair s) ` C]"
        by fast
      define Ys where "Ys = fold fst (map Spair ts) \<Turnstile> Zs"
      with Zs(2) have
        "fold fst (map Spair ts) \<Turnstile> (Es @ E # fst (Spair s) \<Turnstile> Bs) =
          fold fst (map Spair ts) ` C0 # Ys @ [fold fst (map Spair (s#ts)) ` C]"
         by (simp add: image_comp)
      moreover
        have  "\<forall>r\<in>set ts. \<forall>(f,g)\<in>fundfoldpairs.
                r = Abs_induced_automorph f g \<longrightarrow> C0\<in>f\<turnstile>\<C>"
        using fundfoldpair_fundchamber_in_half_chamber_system_f
        by    fast
      ultimately have
        "fold fst (map Spair ts) \<Turnstile> (Es @ E # fst (Spair s) \<Turnstile> Bs) =
          C0 # Ys @ [fold fst (map Spair (s#ts)) ` fold fst (map Spair rs) ` C]"
        using decomps(1) ss C0CsC_rs_f\<C> fundfold_comp_trivial_f\<C>[of ts C0]
              fundfold_comp_trivial_f\<C>[of rs C]
        by    fastforce
      with decomps(1) ss obtain Xs where Xs:
        "length Xs \<le> length Ys"
        "pgallery (C0 # Xs @ [fold fst (map Spair ss) ` C])"
        using gal fundfold_comp_gallery_map[of "Es @ E # fst (Spair s) \<Turnstile> Bs" ts]
              gallery_obtain_pgallery[OF False[THEN not_sym]]
        by    (fastforce simp add: image_comp)
      from Ys_def Xs(1) Zs(1) have "length Xs < length Cs" by simp
      with Xs(2) obtain n where "(fold fst (map Spair ss) ^^ (Suc n)) ` C = C0"
        using step by (force simp add: image_comp funpow_Suc_right[THEN sym])
      thus ?thesis by fast
    qed
  qed

qed

lemma fundfold_comp_chamber_ex_funpow:
  assumes ss: "set ss = S" and C: "chamber C"
  shows   "\<exists>n. (fold fst (map Spair ss) ^^ n) ` C = C0"
proof (cases "C=C0")
  case True
  hence "(fold fst (map Spair ss) ^^ 0) ` C = C0" by simp
  thus ?thesis by fast
next
  case False with fundchamber assms show ?thesis
    using chamber_pconnect[of C0 C] fundfold_comp_pgallery_ex_funpow
    by    fastforce
qed

lemma fundfold_comp_fixespointwise_C0:
  assumes "set ss \<subseteq> S"
  shows   "fixespointwise (fold fst (map Spair ss)) C0"
proof (rule fold_fixespointwise, rule ballI)
  fix fg assume "fg \<in> set (map Spair ss)"
  from this obtain s where "s\<in>set ss" "fg = Spair s" by auto
  with assms
    have  fg': "OpposedThinChamberComplexFoldings X (fst fg) (snd fg) C0"
    using Spair_fundfoldpair fundfoldpairs_def
    by    fastforce
  show "fixespointwise (fst fg) C0"
    using OpposedThinChamberComplexFoldings.axioms(2)[OF fg']
          OpposedThinChamberComplexFoldings.chamber_D0[OF fg']
          OpposedThinChamberComplexFoldings.chambers(4)[OF fg']
          chamber_system_def
          ChamberComplexFolding.chamber_retraction1[of X "fst fg" C0]
    by    auto
qed

lemma fundfold_comp_endomorphism:
  assumes "set ss \<subseteq> S"
  shows   "ChamberComplexEndomorphism X (fold fst (map Spair ss))"
proof (rule fold_chamber_complex_endomorph_list, rule ballI)
  fix fg assume fg: "fg \<in>set (map Spair ss)"
  from this obtain s where "s\<in>set ss" "fg = Spair s" by auto
  with assms show "ChamberComplexEndomorphism X (fst fg)"
    using     Spair_fundfoldpair
              OpposedThinChamberComplexFoldings.axioms(2)[of X]
              ChamberComplexFolding.axioms(1)[of X]
              ChamberComplexRetraction.axioms(1)[of X]
    unfolding fundfoldpairs_def
    by        fastforce
qed

lemma finite_S: "finite S"
  using fundchamber_S_fundadjset fundchamber finite_adjacentset
  by    (blast intro: inj_on_finite fundchamber_S_image_inj_on)

lemma ex_label_retraction: "\<exists>\<phi>. label_wrt C0 \<phi> \<and> fixespointwise \<phi> C0"
proof-
  obtain ss where ss: "set ss = S" using finite_S finite_list by fastforce

  define fgs where "fgs = map Spair ss"
  \<comment> \<open>for @{term "fg \<in> set fgs"}, have @{term "(fst fg) ` D = C0"} for some @{term "D \<in> fundajdset"}\<close>

  define \<psi> where "\<psi> = fold fst fgs" (* \<psi> = fn \<circ> \<dots> \<circ> f1 *)
  define vdist where "vdist v = (LEAST n. (\<psi>^^n) v \<in> C0)" for v
  define \<phi> where "\<phi> v = (\<psi>^^(vdist v)) v" for v

  have "label_wrt C0 \<phi>"
    unfolding label_wrt_def
  proof
    fix C assume C: "C\<in>\<C>"
    show "bij_betw \<phi> C C0"
    proof-
      from \<psi>_def fgs_def ss C obtain m where m: "(\<psi>^^m)`C = C0"
        using chamber_system_def fundfold_comp_chamber_ex_funpow by fastforce
      have "\<And>v. v\<in>C \<Longrightarrow> (\<psi>^^m) v = \<phi> v"
      proof-
        fix v assume v: "v\<in>C"
        define n where "n = (LEAST n. (\<psi>^^n) v \<in> C0)"
        from v m \<phi>_def vdist_def n_def have "m \<ge> n" "\<phi> v \<in> C0"
          using Least_le[of "\<lambda>n. (\<psi>^^n) v \<in> C0" m]
                LeastI_ex[of "\<lambda>n. (\<psi>^^n) v \<in> C0"]
          by    auto
        then show "(\<psi>^^m) v = \<phi> v"
          using ss \<psi>_def fgs_def \<phi>_def vdist_def n_def funpow_add[of "m-n" n \<psi>]
                fundfold_comp_fixespointwise_C0
                funpower_fixespointwise fixespointwiseD
          by    fastforce
      qed
      with C m ss \<psi>_def fgs_def show ?thesis
        using chamber_system_def fundchamber fundfold_comp_endomorphism
              ChamberComplexEndomorphism.funpower_endomorphism[of X]
              ChamberComplexEndomorphism.bij_betw_chambers[of X]
              bij_betw_cong[of C "\<psi>^^m" \<phi> C0]
        by    fastforce
    qed
  qed
  moreover from vdist_def \<phi>_def have "fixespointwise \<phi> C0"
    using Least_eq_0 by (fastforce intro: fixespointwiseI)
  ultimately show ?thesis by fast
qed

lemma ex_label_map: "\<exists>\<phi>. label_wrt C0 \<phi>"
  using ex_label_retraction by fast

end (* context ThinChamberComplexManyFoldings *)

subsubsection \<open>More on the action of the group of automorphisms on chambers\<close>

text \<open>
  Recall that we have already verified that @{term W} acts transitively on the chamber system. We
  now use the labelling of the chamber complex examined in the previous section to show that this
  action is simply transitive.
\<close>

context ThinChamberComplexManyFoldings
begin

lemma fundchamber_W_image_ker:
  assumes "w\<in>W" "w`\<rightarrow>C0 = C0"
  shows   "w = 0"
proof-
  obtain \<phi> where \<phi>: "label_wrt C0 \<phi>" using ex_label_map by fast
  have "fixespointwise (permutation w) C0"
    using W_respects_labels[OF \<phi> assms(1)] chamberD_simplex[OF fundchamber]
          ChamberComplexEndomorphism.respects_label_fixes_chamber_imp_fixespointwise[
            OF W_endomorphism, OF assms(1) \<phi> fundchamber assms(2)
          ]
    by    fast
  with assms(1) show ?thesis
    using fundchamber W_automorphism trivial_automorphism
          standard_uniqueness_automorphs
          permutation_inject[of w 0]
    by    (auto simp add: zero_permutation.rep_eq)
qed

lemma fundchamber_W_image_inj_on:
  "inj_on (\<lambda>w. w`\<rightarrow>C0) W"
proof (rule inj_onI)
  fix w w' assume ww': "w\<in>W" "w'\<in>W" "w`\<rightarrow>C0 = w'`\<rightarrow>C0"
  from ww'(3) have "(-w')`\<rightarrow>w`\<rightarrow>C0 = (-w')`\<rightarrow>w'`\<rightarrow>C0" by simp
  with ww'(1,2) show "w = w'"
    using fundchamber_W_image_ker[of "-w'+w"] add.assoc[of w' "-w'" w]
    by    (simp add:
            image_comp plus_permutation.rep_eq[THEN sym]
            zero_permutation.rep_eq genby_uminus_add_closed
          )
qed

end (* context ThinChamberComplexManyFoldings *)

subsubsection \<open>A bijection between the fundamental chamber and the set of generating automorphisms\<close>

text \<open>
  Removing a single vertex from the fundamental chamber determines a facet, a facet in the
  fundamental chamber determines an adjacent chamber (since our complex is thin), and a chamber
  adjacent to the fundamental chamber determines an automorphism (via some pair of opposed foldings)
  in our generating set @{term S}. Here we show that this correspondence is bijective.
\<close>

context ThinChamberComplexManyFoldings
begin

definition fundantivertex :: "'a permutation \<Rightarrow> 'a"
  where "fundantivertex s \<equiv> (THE v. v \<in> C0-s`\<rightarrow>C0)"

abbreviation "fundantipermutation \<equiv> the_inv_into S fundantivertex"

lemma fundantivertex: "s\<in>S \<Longrightarrow> fundantivertex s \<in> C0-s`\<rightarrow>C0"
  using fundchamber_S_adjacent[of s]
        fundchamber_S_image_neq_fundchamber[of s]
        fundantivertex_def[of s] theI'[OF adj_antivertex]
  by    auto

lemma fundantivertex_fundchamber_decomp:
  "s\<in>S \<Longrightarrow> C0 = insert (fundantivertex s) (C0\<inter>s`\<rightarrow>C0)"
  using fundchamber_S_adjacent[of s]
        fundchamber_S_image_neq_fundchamber[of s]
        fundantivertex[of s] adjacent_conv_insert[of C0]
  by    auto

lemma fundantivertex_unstable:
  "s\<in>S \<Longrightarrow> s \<rightarrow> fundantivertex s \<noteq> fundantivertex s"
    using fundantivertex_fundchamber_decomp[of s]
          image_insert[of "(\<rightarrow>) s" "fundantivertex s" "C0\<inter>s`\<rightarrow>C0"]
          S_fixes_fundchamber_image_int fundchamber_S_image_neq_fundchamber
    by    fastforce

lemma fundantivertex_inj_on: "inj_on fundantivertex S"
proof (rule inj_onI)
  fix s t assume st: "s\<in>S" "t\<in>S" "fundantivertex s = fundantivertex t"
  hence "insert (fundantivertex s) (C0\<inter>s`\<rightarrow>C0) =
          insert (fundantivertex s) (C0\<inter>t`\<rightarrow>C0)"
    using fundantivertex_fundchamber_decomp[of s]
          fundantivertex_fundchamber_decomp[of t]
    by    auto
  moreover from st
    have  "fundantivertex s \<notin> C0\<inter>s`\<rightarrow>C0" "fundantivertex s \<notin> C0\<inter>t`\<rightarrow>C0"
    using fundantivertex[of s] fundantivertex[of t]
    by    auto
  ultimately have "C0\<inter>s`\<rightarrow>C0 = C0\<inter>t`\<rightarrow>C0"
    using insert_subset_equality[of "fundantivertex s"] by simp
  with st(1,2) show "s=t"
    using fundchamber fundchamber_S_chamber[of s] fundchamber_S_chamber[of t]
          fundfacets[of s] fundfacets(2)[of t]
          fundchamber_S_image_neq_fundchamber[of s]
          fundchamber_S_image_neq_fundchamber[of t]
          facet_unique_other_chamber[of C0 "C0\<inter>s`\<rightarrow>C0" "s`\<rightarrow>C0" "t`\<rightarrow>C0"]
          genby_genset_closed[of _ S]
          inj_onD[OF fundchamber_W_image_inj_on, of s t]
    by    auto
qed

lemma fundantivertex_surj_on: "fundantivertex ` S = C0"
proof (rule seteqI)
  show "\<And>v. v \<in> fundantivertex ` S \<Longrightarrow> v\<in>C0" using fundantivertex by fast
next
  fix v assume v: "v\<in>C0"
  define D where "D = the_adj_chamber C0 (C0-{v})"
  with v have "D\<in>fundadjset"
    using fundchamber facetrel_diff_vertex the_adj_chamber_adjacentset
          the_adj_chamber_neq
    by    fastforce
  from this obtain s where s: "s\<in>S" "D = s`\<rightarrow>C0"
    using fundadjset_eq_S_image by blast
  with v D_def [abs_def] have "fundantivertex s = v"
    using     fundchamber fundchamber_S_adjacent
              fundchamber_S_image_neq_fundchamber[of s]
              facetrel_diff_vertex[of v C0]
              the_adj_chamber_facet facetrel_def[of "C0-{v}" D]
    unfolding fundantivertex_def
    by        (force intro: the1_equality[OF adj_antivertex])
  with s(1) show "v \<in> fundantivertex ` S" by fast
qed

lemma fundantivertex_bij_betw: "bij_betw fundantivertex S C0"
  unfolding bij_betw_def
  using     fundantivertex_inj_on fundantivertex_surj_on
  by        fast

lemma card_S_fundchamber: "card S = card C0"
  using bij_betw_same_card[OF fundantivertex_bij_betw] by fast

lemma card_S_chamber:
  "chamber C \<Longrightarrow> card C = card S"
  using fundchamber chamber_card[of C0 C] card_S_fundchamber by auto

lemma fundantipermutation1:
  "v\<in>C0 \<Longrightarrow> fundantipermutation v \<in> S"
  using fundantivertex_surj_on the_inv_into_into[OF fundantivertex_inj_on] by blast
  
end (* context ThinChamberComplexManyFoldings *)




subsection \<open>Thick chamber complexes\<close>

text \<open>
  A thick chamber complex is one in which every facet is a facet of at least three chambers.
\<close>

locale ThickChamberComplex = ChamberComplex X
  for X :: "'a set set"
+ assumes thick:
    "chamber C \<Longrightarrow> z\<lhd>C \<Longrightarrow>
      \<exists>D E. D\<in>X-{C} \<and> z\<lhd>D \<and> E\<in>X-{C,D} \<and> z\<lhd>E"
begin

definition some_third_chamber :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "some_third_chamber C D z \<equiv> SOME E. E\<in>X-{C,D} \<and> z\<lhd>E"

lemma facet_ex_third_chamber: "chamber C \<Longrightarrow> z\<lhd>C \<Longrightarrow> \<exists>E\<in>X-{C,D}. z\<lhd>E"
  using thick[of C z] by auto

lemma some_third_chamberD_facet:
  "chamber C \<Longrightarrow> z\<lhd>C \<Longrightarrow> z \<lhd> some_third_chamber C D z"
  using facet_ex_third_chamber[of C z D] someI_ex[of "\<lambda>E. E\<in>X-{C,D} \<and> z\<lhd>E"]
        some_third_chamber_def
  by    auto
  
lemma some_third_chamberD_simplex:
  "chamber C \<Longrightarrow> z\<lhd>C \<Longrightarrow> some_third_chamber C D z \<in> X"
  using facet_ex_third_chamber[of C z D] someI_ex[of "\<lambda>E. E\<in>X-{C,D} \<and> z\<lhd>E"]
        some_third_chamber_def
  by    auto

lemma some_third_chamberD_adj:
  "chamber C \<Longrightarrow> z\<lhd>C \<Longrightarrow> C \<sim> some_third_chamber C D z"
  using some_third_chamberD_facet by (fast intro: adjacentI)

lemma chamber_some_third_chamber:
  "chamber C \<Longrightarrow> z\<lhd>C \<Longrightarrow> chamber (some_third_chamber C D z)"
  using chamber_adj some_third_chamberD_simplex some_third_chamberD_adj
  by    fast

lemma some_third_chamberD_ne:
  assumes "chamber C" "z\<lhd>C"
  shows   "some_third_chamber C D z \<noteq> C" "some_third_chamber C D z \<noteq> D"
  using   assms facet_ex_third_chamber[of C z D]
          someI_ex[of "\<lambda>E. E\<in>X-{C,D} \<and> z\<lhd>E"] some_third_chamber_def
  by      auto

end (* context ThickChamberComplex *)

end (* theory *)
