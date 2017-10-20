section {* Buildings *}

text {*
  In this section we collect the axioms for a (thick) building in a locale, and prove that
  apartments in a building are uniformly Coxeter.
*}

theory Building
imports Coxeter

begin

subsection {* Apartment systems *}

text {*
  First we describe and explore the basic structure of apartment systems. An apartment system is a
  collection of isomorphic thin chamber subcomplexes with certain intersection properties.
*}

subsubsection {* Locale and basic facts *}

locale ChamberComplexWithApartmentSystem = ChamberComplex X
  for   X :: "'a set set"
+ fixes \<A> :: "'a set set set"
  assumes subcomplexes         :  "A\<in>\<A> \<Longrightarrow> ChamberSubcomplex A"
  and     thincomplexes        :  "A\<in>\<A> \<Longrightarrow> ThinChamberComplex A"
  and     no_trivial_apartments:  "{}\<notin>\<A>"
  and     containtwo           : 
    "chamber C \<Longrightarrow> chamber D \<Longrightarrow> \<exists>A\<in>\<A>. C\<in>A \<and> D\<in>A"
  and     intersecttwo         :
    "\<lbrakk> A\<in>\<A>; A'\<in>\<A>; x\<in>A\<inter>A'; C\<in>A\<inter>A'; chamber C \<rbrakk> \<Longrightarrow>
      \<exists>f. ChamberComplexIsomorphism A A' f \<and> fixespointwise f x \<and>
        fixespointwise f C"
begin

lemmas complexes                = ChamberSubcomplexD_complex [OF subcomplexes]
lemmas apartment_simplices      = ChamberSubcomplexD_sub     [OF subcomplexes]
lemmas chamber_in_apartment     = chamber_in_subcomplex      [OF subcomplexes]
lemmas apartment_chamber        = subcomplex_chamber         [OF subcomplexes]
lemmas gallery_in_apartment     = gallery_in_subcomplex      [OF subcomplexes]
lemmas apartment_gallery        = subcomplex_gallery         [OF subcomplexes]
lemmas min_gallery_in_apartment = min_gallery_in_subcomplex  [OF subcomplexes]

lemmas apartment_simplex_in_max =
  ChamberComplex.simplex_in_max [OF complexes]

lemmas apartment_faces =
  ChamberComplex.faces [OF complexes]

lemmas apartment_chamber_system_def =
  ChamberComplex.chamber_system_def [OF complexes]

lemmas apartment_chamberD_simplex =
  ChamberComplex.chamberD_simplex [OF complexes]

lemmas apartment_chamber_distance_def =
  ChamberComplex.chamber_distance_def [OF complexes]

lemmas apartment_galleryD_chamber =
  ChamberComplex.galleryD_chamber [OF complexes]

lemmas apartment_gallery_least_length =
  ChamberComplex.gallery_least_length [OF complexes]

lemmas apartment_min_galleryD_gallery =
  ChamberComplex.min_galleryD_gallery [OF complexes]

lemmas apartment_min_gallery_pgallery =
  ChamberComplex.min_gallery_pgallery [OF complexes]

lemmas apartment_trivial_morphism =
  ChamberComplex.trivial_morphism [OF complexes]

lemmas apartment_chamber_system_simplices =
  ChamberComplex.chamber_system_simplices [OF complexes]

lemmas apartment_min_gallery_least_length =
  ChamberComplex.min_gallery_least_length [OF complexes]

lemmas apartment_vertex_set_int =
  ChamberComplex.vertex_set_int[OF complexes complexes]

lemmas apartment_standard_uniqueness_pgallery_betw =
  ThinChamberComplex.standard_uniqueness_pgallery_betw[OF thincomplexes]

lemmas apartment_standard_uniqueness =
  ThinChamberComplex.standard_uniqueness[OF thincomplexes]

lemmas apartment_standard_uniqueness_isomorphs =
  ThinChamberComplex.standard_uniqueness_isomorphs[OF thincomplexes]

abbreviation "supapartment C D \<equiv> (SOME A. A\<in>\<A> \<and> C\<in>A \<and> D\<in>A)"

lemma supapartmentD:
  assumes CD: "chamber C" "chamber D"
  defines A : "A \<equiv> supapartment C D"
  shows   "A\<in>\<A>" "C\<in>A" "D\<in>A"
proof-
  from CD have 1: "\<exists>A. A\<in>\<A> \<and> C\<in>A \<and> D\<in>A" using containtwo by fast
  from A show "A\<in>\<A>" "C\<in>A" "D\<in>A" using someI_ex[OF 1] by auto
qed

lemma iso_fixespointwise_chamber_in_int_apartments:
  assumes apartments: "A \<in> \<A>" "A' \<in> \<A>"
  and     chamber   : "chamber C" "C\<in>A\<inter>A'"
  and     iso       : "ChamberComplexIsomorphism A A' f" "fixespointwise f C"
  shows "fixespointwise f (\<Union>(A\<inter>A'))"
proof (rule fixespointwiseI)
  fix v assume "v \<in> \<Union>(A \<inter> A')"
  from this obtain x where x: "x \<in> A\<inter>A'" "v \<in> x" by fast
  from apartments x(1) chamber intersecttwo[of A A'] obtain g
    where g:  "ChamberComplexIsomorphism A A' g"
              "fixespointwise g x" "fixespointwise g C"
    by    force
  from assms g(1,3) have "fun_eq_on f g (\<Union>A)"
    using chamber_in_apartment 
    by    (auto intro:
            apartment_standard_uniqueness_isomorphs
            fixespointwise2_imp_eq_on
          )
  with x g(2) show "f v = id v" using fixespointwiseD fun_eq_onD by force
qed

lemma strong_intersecttwo:
  "\<lbrakk> A\<in>\<A>; A'\<in>\<A>; chamber C; C \<in> A\<inter>A' \<rbrakk> \<Longrightarrow>
    \<exists>f. ChamberComplexIsomorphism A A' f \<and> fixespointwise f (\<Union>(A\<inter>A'))"
  using intersecttwo[of A A']
        iso_fixespointwise_chamber_in_int_apartments[of A A' C]
  by    force

end (* context ChamberComplexWithApartmentSystem *)

subsubsection {* Isomorphisms between apartments *}

text {*
  By standard uniqueness, the isomorphism between overlapping apartments guaranteed by the axiom
  @{text "intersecttwo"} is unique.
*}

context ChamberComplexWithApartmentSystem
begin

lemma ex1_apartment_iso:
  assumes "A\<in>\<A>" "A'\<in>\<A>" "chamber C" "C\<in>A\<inter>A'"
  shows   "\<exists>!f. ChamberComplexIsomorphism A A' f \<and>
            fixespointwise f (\<Union>(A\<inter>A')) \<and> fixespointwise f (-\<Union>A)"
--{* The third clause in the conjunction is to facilitate uniqueness. *}
proof (rule ex_ex1I)
  from assms obtain f
    where f: "ChamberComplexIsomorphism A A' f" "fixespointwise f (\<Union>(A\<inter>A'))"
    using strong_intersecttwo
    by    fast
  def f' \<equiv> "restrict1 f (\<Union>A)"
  from f(1) f'_def have "ChamberComplexIsomorphism A A' f'"
    by (fastforce intro: ChamberComplexIsomorphism.iso_cong fun_eq_onI)
  moreover from f(2) f'_def have "fixespointwise f' (\<Union>(A\<inter>A'))"
    using fun_eq_onI[of "\<Union>(A\<inter>A')" f' f]
    by    (fastforce intro: fixespointwise_cong)
  moreover from f'_def have "fixespointwise f' (-\<Union>A)"
    by (auto intro: fixespointwiseI)
  ultimately
    show  "\<exists>f. ChamberComplexIsomorphism A A' f \<and>
            fixespointwise f (\<Union>(A\<inter>A')) \<and> fixespointwise f (-\<Union>A)"
    by    fast
next
  fix f g
  assume  "ChamberComplexIsomorphism A A' f \<and>
            fixespointwise f (\<Union>(A \<inter> A')) \<and> fixespointwise f (-\<Union>A)"
          "ChamberComplexIsomorphism A A' g \<and>
            fixespointwise g (\<Union>(A \<inter> A')) \<and> fixespointwise g (-\<Union>A)"
  with assms show "f=g"
    using chamber_in_apartment fixespointwise2_imp_eq_on[of f C g] fun_eq_on_cong
          fixespointwise_subset[of f "\<Union>(A\<inter>A')" C]
          fixespointwise_subset[of g "\<Union>(A\<inter>A')" C]
          apartment_standard_uniqueness_isomorphs
    by    (blast intro: fun_eq_on_set_and_comp_imp_eq)
qed

definition the_apartment_iso :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> ('a\<Rightarrow>'a)"
  where "the_apartment_iso A A' \<equiv>
          (THE f. ChamberComplexIsomorphism A A' f \<and>
            fixespointwise f (\<Union>(A\<inter>A')) \<and> fixespointwise f (-\<Union>A))"

lemma the_apartment_isoD:
  assumes   "A\<in>\<A>" "A'\<in>\<A>" "chamber C" "C\<in>A\<inter>A'"
  defines   "f \<equiv> the_apartment_iso A A'"
  shows     "ChamberComplexIsomorphism A A' f" "fixespointwise f (\<Union>(A\<inter>A'))"
            "fixespointwise f (-\<Union>A)"
  using     assms theI'[OF ex1_apartment_iso]
  unfolding the_apartment_iso_def
  by        auto

lemmas the_apartment_iso_apartment_chamber_map =
  ChamberComplexIsomorphism.chamber_map [OF the_apartment_isoD(1)]
  
lemmas the_apartment_iso_apartment_simplex_map =
  ChamberComplexIsomorphism.simplex_map [OF the_apartment_isoD(1)]
  

lemma the_apartment_iso_chamber_map:
  "\<lbrakk> A\<in>\<A>; B\<in>\<A>; chamber C; C\<in>A\<inter>B; chamber D; D\<in>A \<rbrakk> \<Longrightarrow>
    chamber (the_apartment_iso A B ` D)"
  using chamber_in_apartment[of A] apartment_chamber
        the_apartment_iso_apartment_chamber_map
  by    auto

lemma the_apartment_iso_comp:
  assumes apartments: "A\<in>\<A>" "A'\<in>\<A>" "A''\<in>\<A>"
  and     chamber   : "chamber C" "C\<in>A\<inter>A'\<inter>A''"
  defines "f \<equiv> the_apartment_iso A A'"
  and     "g \<equiv> the_apartment_iso A' A''"
  and     "h \<equiv> the_apartment_iso A A''"
  defines "gf \<equiv> restrict1 (g\<circ>f) (\<Union>A)"
  shows   "h = gf"
proof (
  rule fun_eq_on_set_and_comp_imp_eq,
  rule apartment_standard_uniqueness_isomorphs, rule apartments(3)
)
  from gf_def have gf_cong1: "fun_eq_on gf (g\<circ>f) (\<Union>A)"
    by (fastforce intro: fun_eq_onI)
  from gf_def have gf_cong2: "fixespointwise gf (-\<Union>A)"
    by (auto intro: fixespointwiseI)

  from apartments(1,3) chamber h_def
    show  "ChamberComplexIsomorphism A A'' h"
    using the_apartment_isoD(1)
    by    fast
  from apartments chamber f_def g_def
    show  "ChamberComplexIsomorphism A A'' gf"
    using ChamberComplexIsomorphism.iso_cong[OF _ gf_cong1]
          ChamberComplexIsomorphism.iso_comp the_apartment_isoD(1)
    by    blast
  from apartments(1) chamber show "ChamberComplex.chamber A C"
    using chamber_in_apartment by fast
  show "fun_eq_on h gf C"
  proof (rule fixespointwise2_imp_eq_on)
    from assms(1,3) chamber h_def show "fixespointwise h C"
      using fixespointwise_subset the_apartment_isoD(2) by blast
    have "fun_eq_on gf (g\<circ>f) (\<Union>(A\<inter>A'\<inter>A''))"
      using fun_eq_on_subset[OF gf_cong1, of "\<Union>(A\<inter>A'\<inter>A'')"] by fast
    moreover from f_def g_def apartments chamber
      have  "fixespointwise (g\<circ>f) (\<Union>(A\<inter>A'\<inter>A''))"
      using fixespointwise_comp[of f "\<Union>(A\<inter>A'\<inter>A'')" g]
            fixespointwise_subset[
              OF the_apartment_isoD(2), of _ _ C "\<Union>(A\<inter>A'\<inter>A'')"
            ]
      by    auto
    ultimately have "fixespointwise gf (\<Union>(A\<inter>A'\<inter>A''))"
      using fixespointwise_cong[of gf "g\<circ>f"] by fast
    with chamber(2) show "fixespointwise gf C"
      using fixespointwise_subset by auto
  qed
  from h_def apartments(1,3) chamber show "fun_eq_on h gf (- \<Union>A)"
    using the_apartment_isoD(3) gf_cong2 by (auto intro: fun_eq_on_cong)
qed

lemma the_apartment_iso_int_im:
  assumes   "A\<in>\<A>" "A'\<in>\<A>" "chamber C" "C\<in>A\<inter>A'" "x\<in>A\<inter>A'"
  defines   "f \<equiv> the_apartment_iso A A'"
  shows     "f`x = x"
  using     assms the_apartment_isoD(2) fixespointwise_im[of f "\<Union>(A\<inter>A')" x]
  by        fast

end (* context ChamberComplexWithApartmentSystem *)

subsubsection {* Retractions onto apartments *}

text {*
  Since the isomorphism between overlapping apartments is the identity on their intersection,
  starting with a fixed chamber in a fixed apartment, we can construct a retraction onto that
  apartment as follows. Given a vertex in the complex, that vertex is contained a chamber, and
  that chamber lies in a common apartment with the fixed chamber. We then apply to the vertex the
  apartment isomorphism from that common apartment to the fixed apartment. It turns out that the
  image of the vertex does not depend on the containing chamber and apartment chosen, and so
  since the isomorphisms between apartments used are unique, such a retraction onto an apartment
  is canonical.
*}

context ChamberComplexWithApartmentSystem
begin

definition canonical_retraction :: "'a set set \<Rightarrow> 'a set \<Rightarrow> ('a\<Rightarrow>'a)"
  where "canonical_retraction A C =
          restrict1 (\<lambda>v. the_apartment_iso (supapartment (supchamber v) C) A v)
            (\<Union>X)"

lemma canonical_retraction_retraction:
  assumes "A\<in>\<A>" "chamber C" "C\<in>A" "v\<in>\<Union>A"
  shows   "canonical_retraction A C v = v"
proof-
  def D: D \<equiv> "supchamber v"
  def B: B \<equiv> "supapartment D C"
  from D assms(1,4) have D_facts: "chamber D" "v\<in>D"
    using apartment_simplices supchamberD[of v] by auto
  from B assms(2) have B_facts: "B\<in>\<A>" "D\<in>B" "C\<in>B"
    using D_facts(1) supapartmentD[of D C] by auto
  from assms(1,4) have "v\<in>\<Union>(B\<inter>A)"
    using D_facts(2) B_facts(1,2) apartment_vertex_set_int by fast
  with assms(1-3) D B show ?thesis
    using canonical_retraction_def B_facts(1,3) fixespointwiseD[of _ "\<Union>(B\<inter>A)" v]
          the_apartment_isoD(2)[of B A C]
    by    simp
qed

lemma canonical_retraction_simplex_retraction1:
  "\<lbrakk> A\<in>\<A>; chamber C; C\<in>A; a\<in>A \<rbrakk> \<Longrightarrow>
    fixespointwise (canonical_retraction A C) a"
  using canonical_retraction_retraction by (force intro: fixespointwiseI)

lemma canonical_retraction_simplex_retraction2:
  "\<lbrakk> A\<in>\<A>; chamber C; C\<in>A; a\<in>A \<rbrakk> \<Longrightarrow> canonical_retraction A C ` a = a"
  using canonical_retraction_simplex_retraction1 fixespointwise_im[of _ a a] by simp

lemma canonical_retraction_uniform:
  assumes apartments: "A\<in>\<A>" "B\<in>\<A>"
  and     chambers  : "chamber C" "C\<in>A\<inter>B"
  shows   "fun_eq_on (canonical_retraction A C) (the_apartment_iso B A) (\<Union>B)"
proof (rule fun_eq_onI)
  fix v assume v: "v\<in>\<Union>B"
  def D': D' \<equiv> "supchamber v"
  def B': B' \<equiv> "supapartment D' C"
  def g : g  \<equiv> "the_apartment_iso B' A"
  and f : f  \<equiv> "the_apartment_iso B B'"
  and h : h  \<equiv> "the_apartment_iso B A"
  from D' v apartments(2) have D'_facts: "chamber D'" "v\<in>D'"
    using apartment_simplices supchamberD[of v] by auto
  from B' chambers(1) have B'_facts: "B'\<in>\<A>" "D'\<in>B'" "C\<in>B'" 
    using D'_facts(1) supapartmentD[of D' C] by auto
  from f apartments(2) chambers have "fixespointwise f (\<Union>(B \<inter> B'))"
    using B'_facts(1,3) the_apartment_isoD(2)[of B B' C] by fast
  moreover from v apartments(2) have "v\<in>\<Union>(B\<inter>B')"
    using D'_facts(2) B'_facts(1,2) apartment_vertex_set_int by fast
  ultimately show "canonical_retraction A C v = h v"
    using D' B' g f h v apartments chambers fixespointwiseD[of f "\<Union>(B\<inter>B')" v]
          canonical_retraction_def apartment_simplices[of B] B'_facts(1,3)
          the_apartment_iso_comp[of B B' A C]
    by    auto
qed

lemma canonical_retraction_uniform_im:
  "\<lbrakk> A\<in>\<A>; B\<in>\<A>; chamber C; C\<in>A\<inter>B; x\<in>B \<rbrakk> \<Longrightarrow>
    canonical_retraction A C ` x = the_apartment_iso B A ` x"
  using canonical_retraction_uniform fun_eq_on_im[of _ _ _ x] by fast

lemma canonical_retraction_simplex_im:
  assumes "A\<in>\<A>" "chamber C" "C\<in>A"
  shows   "canonical_retraction A C \<turnstile> X = A"
proof (rule seteqI)
  fix y assume "y \<in> canonical_retraction A C \<turnstile> X"
  from this obtain x where x: "x\<in>X" "y = canonical_retraction A C ` x" by fast
  from x(1) obtain D where D: "chamber D" "x\<subseteq>D" using simplex_in_max by fast
  from assms(2) D(1) obtain B where "B\<in>\<A>" "D\<in>B" "C\<in>B"
    using containtwo by fast
  with assms D(2) x(2) show "y\<in>A"
    using the_apartment_isoD(1)[of B A]
          ChamberComplexIsomorphism.surj_simplex_map
          canonical_retraction_uniform_im apartment_faces[of B D x]
    by    fastforce
next
  fix a assume "a\<in>A"
  with assms show "a \<in> canonical_retraction A C \<turnstile> X"
    using canonical_retraction_simplex_retraction2[of A C a, THEN sym]
          apartment_simplices
    by    fast
qed

lemma canonical_retraction_vertex_im:
  "\<lbrakk> A\<in>\<A>; chamber C; C\<in>A \<rbrakk> \<Longrightarrow> canonical_retraction A C ` \<Union>X = \<Union>A"
  using singleton_simplex ChamberComplex.singleton_simplex complexes
        canonical_retraction_simplex_im[of A C]
  by    blast

lemma canonical_retraction:
  assumes "A\<in>\<A>" "chamber C" "C\<in>A"
  shows "ChamberComplexRetraction X (canonical_retraction A C)"
proof
  fix D assume "chamber D"
  with assms
    show  "chamber (canonical_retraction A C ` D)"
          "card (canonical_retraction A C ` D) = card D"
    using containtwo[of C D] canonical_retraction_uniform_im
          the_apartment_iso_chamber_map chamber_in_apartment
          ChamberComplexIsomorphism.dim_map[OF the_apartment_isoD(1)]
    by    auto
next
  fix v from assms
    show  "v\<in>\<Union>X \<Longrightarrow> canonical_retraction A C (canonical_retraction A C v) =
              canonical_retraction A C v"
    using canonical_retraction_retraction canonical_retraction_vertex_im
    by    fast
qed (simp add: canonical_retraction_def)

lemma canonical_retraction_comp_endomorphism:
  "\<lbrakk> A\<in>\<A>; B\<in>\<A>; chamber C; chamber D; C\<in>A; D\<in>B \<rbrakk> \<Longrightarrow>
    ChamberComplexEndomorphism X
      (canonical_retraction A C \<circ> canonical_retraction B D)"
  using canonical_retraction[of A C] canonical_retraction[of B D]
        ChamberComplexRetraction.axioms(1)
        ChamberComplexEndomorphism.endo_comp
  by    fast

lemma canonical_retraction_comp_simplex_im_subset:
  "\<lbrakk> A\<in>\<A>; B\<in>\<A>; chamber C; chamber D; C\<in>A; D\<in>B \<rbrakk> \<Longrightarrow>
      (canonical_retraction A C \<circ> canonical_retraction B D) \<turnstile> X \<subseteq> A"
  using canonical_retraction[of B D] ChamberComplexRetraction.simplex_map
        canonical_retraction_simplex_im[of A C]
  by    (force simp add: image_comp[THEN sym])

lemma canonical_retraction_comp_apartment_endomorphism:
  "\<lbrakk> A\<in>\<A>; B\<in>\<A>; chamber C; chamber D; C\<in>A; D\<in>B \<rbrakk> \<Longrightarrow>
    ChamberComplexEndomorphism A
      (restrict1 (canonical_retraction A C \<circ> canonical_retraction B D) (\<Union>A))"
  using ChamberComplexEndomorphism.restrict_endo[of X _ A]
        canonical_retraction_comp_endomorphism[of A B C D] subcomplexes[of A]
        canonical_retraction_comp_simplex_im_subset[of A B C D]
        apartment_simplices[of A]
  by    auto

end (* context ChamberComplexWithApartmentSystem *)


subsubsection {* Distances in apartments *}

text {*
  Here we examine distances between chambers and between a facet and a chamber, especially with
  respect to canonical retractions onto an apartment. Note that a distance measured within an
  apartment is equal to the distance measured between the same objects in the wider chamber
  complex. In other words, the shortest distance between chambers can always be achieved within an
  apartment.
*}

context ChamberComplexWithApartmentSystem
begin

lemma apartment_chamber_distance:
  assumes "A\<in>\<A>" "chamber C" "chamber D" "C\<in>A" "D\<in>A"
  shows   "ChamberComplex.chamber_distance A C D = chamber_distance C D"
proof (cases "C=D")
  case True with assms(1) show ?thesis
    using apartment_chamber_distance_def chamber_distance_def by simp
next
  case False
  def Cs \<equiv> "ARG_MIN length Cs. ChamberComplex.gallery A (C#Cs@[D])"
  and Ds \<equiv> "ARG_MIN length Ds. gallery (C#Ds@[D])"
  and f \<equiv> "canonical_retraction A C"

  from assms(2,3) False Ds_def have 1: "gallery (C#Ds@[D])"
    using gallery_least_length by fast
  with assms(1,2,4,5) f_def have "gallery (C # f\<Turnstile>Ds @ [D])"
    using canonical_retraction ChamberComplexRetraction.gallery_map[of X]
          canonical_retraction_simplex_retraction2
    by    fastforce
  moreover from f_def assms(1,2,4) have "set (f\<Turnstile>Ds) \<subseteq> A"
    using 1 galleryD_chamber chamberD_simplex
          canonical_retraction_simplex_im[of A C]
    by    auto
  ultimately have "ChamberComplex.gallery A (C # f\<Turnstile>Ds @ [D])"
    using assms(1,4,5) gallery_in_apartment by simp
  with assms(1) Ds_def False
    have  "ChamberComplex.chamber_distance A C D \<le> chamber_distance C D"
    using ChamberComplex.chamber_distance_le[OF complexes]
          chamber_distance_def
    by    force
  moreover from assms False Cs_def
    have  "chamber_distance C D \<le> ChamberComplex.chamber_distance A C D"
    using chamber_in_apartment apartment_gallery_least_length
          subcomplex_gallery[OF subcomplexes]
          chamber_distance_le apartment_chamber_distance_def
    by    simp
  ultimately show ?thesis by simp
qed

lemma apartment_min_gallery:
  assumes "A\<in>\<A>" "ChamberComplex.min_gallery A Cs"
  shows   "min_gallery Cs"
proof (cases Cs rule: list_cases_Cons_snoc)
  case Single with assms show ?thesis
    using apartment_min_galleryD_gallery apartment_gallery galleryD_chamber
    by    fastforce
next
  case (Cons_snoc C Ds D)
  moreover with assms have "min_gallery (C#Ds@[D])"
    using apartment_min_galleryD_gallery[of A Cs] apartment_gallery[of A Cs]
          apartment_galleryD_chamber apartment_chamberD_simplex
          ChamberComplex.min_gallery_betw_chamber_distance[
            OF complexes, of A C Ds D
          ]
          galleryD_chamber apartment_chamber_distance
          min_galleryI_chamber_distance_betw
    by    auto
  ultimately show ?thesis by fast
qed simp

lemma apartment_face_distance:
  assumes "A\<in>\<A>" "chamber C" "C\<in>A" "F\<in>A"
  shows   "ChamberComplex.face_distance A F C = face_distance F C"
proof-
  def D  \<equiv> "closest_supchamber F C"
  and D' \<equiv> "ChamberComplex.closest_supchamber A F C"

  from assms D'_def have chamber_D': "ChamberComplex.chamber A D'"
    using chamber_in_apartment ChamberComplex.closest_supchamberD(1)
          complexes
    by    fast
  with assms(1,2,4) D_def have chambers: "chamber D" "chamber D'"
    using closest_supchamberD(1)[of F C] apartment_chamber
          apartment_simplices
    by    auto
  from assms(1-3)
    have  1: "ChamberComplex.chamber_distance A D' C = chamber_distance D' C"
    using chamber_D' chambers(2) apartment_chamberD_simplex
          apartment_chamber_distance
    by    fastforce
  from assms D_def D'_def have F_DD': "F\<subseteq>D" "F\<subseteq>D'"
    using apartment_simplices[of A] closest_supchamberD(2) chamber_in_apartment
          ChamberComplex.closest_supchamberD(2)[OF complexes]
    by    auto

  from assms(2) obtain B where "B\<in>\<A>" "C\<in>B" "D\<in>B"
    using chambers(1) containtwo by fast
  moreover with assms have "the_apartment_iso B A ` F = F"
    using F_DD'(1) apartment_faces the_apartment_iso_int_im by force
  moreover have "the_apartment_iso B A ` F \<subseteq> the_apartment_iso B A ` D"
    using F_DD'(1) by fast
  ultimately have "chamber_distance D C \<ge> chamber_distance D' C"
    using assms(1-3) D'_def 1 chambers(1) apartment_chamber_distance[of B]
          chamber_in_apartment[of B D] chamber_in_apartment[of B C]
          ChamberComplexIsomorphism.chamber_map[
            OF the_apartment_isoD(1), of B A
          ]
          ChamberComplex.closest_supchamber_closest[ 
            OF complexes, of A "the_apartment_iso B A ` D" F C
          ]
          ChamberComplexIsomorphism.chamber_distance_map[
            OF the_apartment_isoD(1), of B A C
          ]
          the_apartment_iso_int_im[of B A C C]
    by    force
  moreover from assms D_def
    have  "chamber_distance D C \<le> chamber_distance D' C"
    using closest_supchamber_closest chambers(2) F_DD'(2)
    by    simp
  ultimately show ?thesis
    using assms(1) D_def D'_def face_distance_def 1
          ChamberComplex.face_distance_def[OF complexes]
    by    simp

qed

lemma apartment_face_distance_eq_chamber_distance_compare_other_chamber:
  assumes "A\<in>\<A>" "chamber C" "chamber D" "chamber E" "C\<in>A" "D\<in>A" "E\<in>A"
          "z\<lhd>C" "z\<lhd>D" "C\<noteq>D" "chamber_distance C E \<le> chamber_distance D E"
  shows   "face_distance z E = chamber_distance C E"
  using   assms apartment_chamber_distance apartment_face_distance
          facetrel_subset[of z C] apartment_faces[of A C z] chamber_in_apartment
          ThinChamberComplex.face_distance_eq_chamber_distance_compare_other_chamber[
            OF thincomplexes, of A C D z E
          ]
  by      auto

lemma canonical_retraction_face_distance_map:
  assumes "A\<in>\<A>" "chamber C" "chamber D" "C\<in>A" "F\<subseteq>C"
  shows   "face_distance F (canonical_retraction A C ` D) = face_distance F D"
proof-
  from assms(2,3) obtain B where B: "B\<in>\<A>" "C\<in>B" "D\<in>B"
    using containtwo by fast
  with assms show ?thesis
    using apartment_faces[of A C F] apartment_faces[of B C F]
          apartment_face_distance chamber_in_apartment the_apartment_iso_int_im
          the_apartment_iso_chamber_map the_apartment_iso_apartment_simplex_map
          apartment_face_distance canonical_retraction_uniform_im
          ChamberComplexIsomorphism.face_distance_map[
            OF the_apartment_isoD(1), of B A C D F
          ]
    by    simp
qed

end (* context ChamberComplexWithApartmentSystem *)

subsubsection {* Special situation: a triangle of apartments and chambers *}

text {*
  To facilitate proving that apartments in buildings have sufficient foldings to be Coxeter, we
  explore the situation of three chambers sharing a common facet, along with three apartments, each
  of which contains two of the chambers. A folding of one of the apartments is
  constructed by composing two apartment retractions, and by symmetry we automatically obtain an
  opposed folding.
*}

locale ChamberComplexApartmentSystemTriangle =
  ChamberComplexWithApartmentSystem X \<A>
  for X :: "'a set set"
  and \<A> :: "'a set set set"
+ fixes A B B' :: "'a set set"
  and   C D E z :: "'a set"
  assumes apartments   : "A\<in>\<A>" "B\<in>\<A>" "B'\<in>\<A>"
  and     chambers     : "chamber C" "chamber D" "chamber E"
  and     facet        : "z\<lhd>C" "z\<lhd>D" "z\<lhd>E"
  and     in_apartments: "C\<in>A\<inter>B" "D\<in>A\<inter>B'" "E\<in>B\<inter>B'"
  and     chambers_ne  : "D\<noteq>C" "E\<noteq>D" "C\<noteq>E"
begin

abbreviation "fold_A \<equiv> canonical_retraction A D \<circ> canonical_retraction B C"
abbreviation "res_fold_A \<equiv> restrict1 fold_A (\<Union>A)"
abbreviation "opp_fold_A \<equiv> canonical_retraction A C \<circ> canonical_retraction B' D"
abbreviation "res_opp_fold_A \<equiv> restrict1 opp_fold_A (\<Union>A)"

lemma rotate: "ChamberComplexApartmentSystemTriangle X \<A> B' A B D E C z"
  using apartments chambers facet in_apartments chambers_ne
  by    unfold_locales auto

lemma reflect: "ChamberComplexApartmentSystemTriangle X \<A> A B' B D C E z"
  using apartments chambers facet in_apartments chambers_ne
  by    unfold_locales auto

lemma facet_in_chambers: "z\<subseteq>C" "z\<subseteq>D" "z\<subseteq>E"
  using facet facetrel_subset by auto

lemma A_chambers:
  "ChamberComplex.chamber A C" "ChamberComplex.chamber A D"
  using apartments(1) chambers(1,2) in_apartments(1,2) chamber_in_apartment
  by    auto

lemma res_fold_A_A_chamber_image:
  "ChamberComplex.chamber A F \<Longrightarrow> res_fold_A ` F = fold_A ` F"
  using apartments(1) apartment_chamberD_simplex restrict1_image
  by    fastforce

lemma the_apartment_iso_middle_im: "the_apartment_iso A B ` D = E"
proof (rule ChamberComplexIsomorphism.thin_image_shared_facet)
  from apartments(1,2) chambers(1) in_apartments(1)
    show  "ChamberComplexIsomorphism A B (the_apartment_iso A B)"
    using the_apartment_isoD(1)
    by    fast
  from apartments(2) chambers(3) in_apartments(3)
    show  "ChamberComplex.chamber B E" "ThinChamberComplex B"
    using chamber_in_apartment thincomplexes
    by    auto
  from apartments(1,2) in_apartments(1) have "z \<in> A\<inter>B"
    using facet_in_chambers(1) apartment_faces by fastforce
  with apartments(1,2) chambers(1) in_apartments(1) chambers_ne(3) facet(3)
    show  "the_apartment_iso A B ` z \<lhd> E" "E \<noteq> the_apartment_iso A B ` C"
    using the_apartment_iso_int_im
    by    auto
qed (
  rule A_chambers(1), rule A_chambers(2), rule facet(1), rule facet(2),
  rule chambers_ne(1)[THEN not_sym]
)

lemma inside_canonical_retraction_chamber_images:
  "canonical_retraction B C ` C = C" 
  "canonical_retraction B C ` D = E"
  "canonical_retraction B C ` E = E"
  using apartments(1,2) chambers(1,2) in_apartments
        canonical_retraction_simplex_retraction2[of B C C]
        canonical_retraction_uniform_im the_apartment_iso_middle_im
        canonical_retraction_simplex_retraction2
  by    auto

lemmas in_canretract_chimages =
  inside_canonical_retraction_chamber_images

lemma outside_canonical_retraction_chamber_images:
  "canonical_retraction A D ` C = C"
  "canonical_retraction A D ` D = D"
  "canonical_retraction A D ` E = C"
  using ChamberComplexApartmentSystemTriangle.in_canretract_chimages[
          OF rotate
        ]
  by    auto

lemma fold_A_chamber_images:
  "fold_A ` C = C" "fold_A ` D = C" "fold_A ` E = C"
  using inside_canonical_retraction_chamber_images
        outside_canonical_retraction_chamber_images
        image_comp[of "canonical_retraction A D" "canonical_retraction B C" C]
        image_comp[of "canonical_retraction A D" "canonical_retraction B C" D]
        image_comp[of "canonical_retraction A D" "canonical_retraction B C" E]
  by    auto

lemmas opp_fold_A_chamber_images =
  ChamberComplexApartmentSystemTriangle.fold_A_chamber_images[OF reflect]

lemma res_fold_A_chamber_images: "res_fold_A ` C = C" "res_fold_A ` D = C"
  using in_apartments(1,2) fold_A_chamber_images(1,2)
        res_fold_A_A_chamber_image A_chambers(1,2)
  by    auto

lemmas res_opp_fold_A_chamber_images =
  ChamberComplexApartmentSystemTriangle.res_fold_A_chamber_images[OF reflect]

lemma fold_A_fixespointwise1: "fixespointwise fold_A C"
  using apartments(1,2) chambers(1,2) in_apartments(1,2)
        canonical_retraction_simplex_retraction1
  by    (auto intro: fixespointwise_comp)

lemmas opp_fold_A_fixespointwise2 =
  ChamberComplexApartmentSystemTriangle.fold_A_fixespointwise1[OF reflect]

lemma fold_A_facet_im: "fold_A ` z = z"
  using facet_in_chambers(1) fixespointwise_im[OF fold_A_fixespointwise1] by simp

lemma fold_A_endo_X: "ChamberComplexEndomorphism X fold_A"
  using apartments(1,2) chambers(1,2) in_apartments(1,2)
        canonical_retraction_comp_endomorphism
  by    fast

lemma res_fold_A_endo_A: "ChamberComplexEndomorphism A res_fold_A"
  using apartments(1,2) chambers(1,2) in_apartments(1,2)
        canonical_retraction_comp_apartment_endomorphism
  by    fast

lemmas opp_res_fold_A_endo_A =
  ChamberComplexApartmentSystemTriangle.res_fold_A_endo_A[OF reflect]

lemma fold_A_morph_A_A: "ChamberComplexMorphism A A fold_A"
  using ChamberComplexEndomorphism.axioms(1)[OF res_fold_A_endo_A]
        ChamberComplexMorphism.cong fun_eq_on_sym[OF fun_eq_on_restrict1]
  by    fast

lemmas opp_fold_A_morph_A_A =
  ChamberComplexApartmentSystemTriangle.fold_A_morph_A_A[OF reflect]

lemma res_fold_A_A_im_fold_A_A_im: "res_fold_A  \<turnstile> A = fold_A  \<turnstile> A"
  using setsetmapim_restrict1[of A A fold_A] by simp

lemmas res_opp_fold_A_A_im_opp_fold_A_A_im =
  ChamberComplexApartmentSystemTriangle.res_fold_A_A_im_fold_A_A_im[
    OF reflect
  ]

lemma res_fold_A_\<C>_A_im_fold_A_\<C>_A_im:
  "res_fold_A  \<turnstile> (ChamberComplex.chamber_system A) =
    fold_A  \<turnstile> (ChamberComplex.chamber_system A)"
  using setsetmapim_restrict1[of "(ChamberComplex.chamber_system A)" A]
        apartments(1) apartment_chamber_system_simplices
  by    blast

lemmas res_opp_fold_A_\<C>_A_im_opp_fold_A_\<C>_A_im =
  ChamberComplexApartmentSystemTriangle.res_fold_A_\<C>_A_im_fold_A_\<C>_A_im[
    OF reflect
  ]

lemma chambercomplex_fold_A_im: "ChamberComplex (fold_A \<turnstile> A)"
  using ChamberComplexMorphism.chambercomplex_image[OF fold_A_morph_A_A]
  by    simp

lemmas chambercomplex_opp_fold_A_im =
  ChamberComplexApartmentSystemTriangle.chambercomplex_fold_A_im[
    OF reflect
  ]

lemma chambersubcomplex_fold_A_im:
  "ChamberComplex.ChamberSubcomplex A (fold_A \<turnstile> A)"
  using ChamberComplexMorphism.chambersubcomplex_image[OF fold_A_morph_A_A]
  by    simp

lemmas chambersubcomplex_opp_fold_A_im =
  ChamberComplexApartmentSystemTriangle.chambersubcomplex_fold_A_im[
    OF reflect
  ]

lemma fold_A_facet_distance_map:
  "chamber F \<Longrightarrow> face_distance z (fold_A`F) = face_distance z F"
  using apartments(1,2) chambers in_apartments(1,2) facet_in_chambers(1,2)
        ChamberComplexRetraction.chamber_map[
          OF canonical_retraction, of B C F
        ]
        canonical_retraction_face_distance_map[of A D "canonical_retraction B C ` F"]
        canonical_retraction_face_distance_map
  by    (simp add: image_comp)

lemma fold_A_min_gallery_betw_map:
  assumes "chamber F" "chamber G" "z\<subseteq>F"
          "face_distance z G = chamber_distance F G" "min_gallery (F#Fs@[G])"
  shows   "min_gallery (fold_A\<Turnstile>(F#Fs@[G]))"
  using   assms fold_A_facet_im fold_A_facet_distance_map
          ChamberComplexEndomorphism.facedist_chdist_mingal_btwmap[
            OF fold_A_endo_X, of F G z
          ]
  by      force

lemma fold_A_chamber_system_image_fixespointwise':
  defines \<C>_A : "\<C>_A  \<equiv> ChamberComplex.\<C> A"
  defines f\<C>_A: "f\<C>_A \<equiv> {F\<in>\<C>_A. face_distance z F = chamber_distance C F}"
  assumes F   : "F\<in>f\<C>_A"
  shows   "fixespointwise fold_A F"
proof-
  show ?thesis
  proof (cases "F=C")
    case True thus ?thesis
      using fold_A_fixespointwise1 fixespointwise_restrict1 by fast
  next
    case False
    from apartments(1) assms
      have  Achamber_F: "ChamberComplex.chamber A F"
      using complexes ChamberComplex.chamber_system_def
      by    fast
    def Fs \<equiv> "ARG_MIN length Fs. ChamberComplex.gallery A (C#Fs@[F])"
    show ?thesis
    proof (rule apartment_standard_uniqueness_pgallery_betw, rule apartments(1))
      show "ChamberComplexMorphism A A fold_A"
        using fold_A_morph_A_A by fast
      from apartments(1) show "ChamberComplexMorphism A A id"
        using apartment_trivial_morphism by fast
      show "fixespointwise fold_A C"
        using fold_A_fixespointwise1 fixespointwise_restrict1 by fast
     
      from apartments(1) False Fs_def
        show  1: "ChamberComplex.gallery A (C#Fs@[F])"
        using A_chambers(1) Achamber_F apartment_gallery_least_length
        by    fast

      from False Fs_def apartments(1) have mingal: "min_gallery (C # Fs @ [F])"
        using A_chambers(1) Achamber_F apartment_min_gallery
              apartment_min_gallery_least_length
        by    fast

      from apartments(1) have set_A: "set (C#Fs@[F]) \<subseteq> A"
        using 1 apartment_galleryD_chamber apartment_chamberD_simplex
        by    fast
      with apartments(1) have "set (fold_A \<Turnstile> (C#Fs@[F])) \<subseteq> A"
        using ChamberComplexMorphism.simplex_map[OF fold_A_morph_A_A]
        by    auto
      with f\<C>_A F show "ChamberComplex.pgallery A (fold_A \<Turnstile> (C#Fs@[F]))"
        using chambers(1) apartments(1) apartment_chamber Achamber_F
              facet_in_chambers(1) mingal
              fold_A_min_gallery_betw_map[of C F] min_gallery_in_apartment
              apartment_min_gallery_pgallery
        by    auto
      from apartments(1) False Fs_def
        show  "ChamberComplex.pgallery A (id \<Turnstile> (C#Fs@[F]))"
        using A_chambers(1) Achamber_F
              ChamberComplex.pgallery_least_length[OF complexes]
        by    auto
    qed
  qed
qed

lemma fold_A_chamber_system_image:
  defines \<C>_A : "\<C>_A \<equiv> ChamberComplex.\<C> A"
  defines f\<C>_A: "f\<C>_A \<equiv> {F\<in>\<C>_A. face_distance z F = chamber_distance C F}"
  shows   "fold_A \<turnstile> \<C>_A = f\<C>_A"
proof (rule seteqI)
  fix F assume F: "F \<in> fold_A \<turnstile> \<C>_A"
  with \<C>_A have "F\<in>\<C>_A"
    using ChamberComplexMorphism.chamber_system_into[OF fold_A_morph_A_A]
    by    fast
  moreover have "face_distance z F = chamber_distance C F"
  proof (cases "F=C")
    case False have F_ne_C: "F\<noteq>C" by fact
    from F obtain G where G: "G\<in>\<C>_A" "F = fold_A ` G" by fast
    with \<C>_A apartments(1) have G': "chamber G" "G\<in>A"
      using apartment_chamber_system_def complexes apartment_chamber
            apartment_chamberD_simplex
      by    auto
    show ?thesis
    proof (cases "chamber_distance C G \<le> chamber_distance D G")
      case True thus "face_distance z F = chamber_distance C F"
        using apartments(1) chambers(1,2) in_apartments(1,2) facet(1,2)
              chambers_ne(1) F_ne_C G(2) G' fold_A_chamber_images(1)
              facet_in_chambers(1) fold_A_facet_distance_map
              fold_A_facet_im
              apartment_face_distance_eq_chamber_distance_compare_other_chamber[
                of A C D G z
              ]
              ChamberComplexEndomorphism.face_distance_eq_chamber_distance_map[
                OF fold_A_endo_X, of C G z
              ]
        by    auto
    next
      case False thus "face_distance z F = chamber_distance C F"
        using apartments(1) chambers(1,2) in_apartments(1,2) facet(1,2)
              chambers_ne(1) F_ne_C G(2) G' fold_A_chamber_images(2)
              facet_in_chambers(2) fold_A_facet_distance_map fold_A_facet_im
              apartment_face_distance_eq_chamber_distance_compare_other_chamber[
                of A D C G z
              ]
              ChamberComplexEndomorphism.face_distance_eq_chamber_distance_map[
                OF fold_A_endo_X, of D G z
              ]
        by    auto
    qed
  qed (simp add:
        chambers(1) facet_in_chambers(1) face_distance_eq_0 chamber_distance_def
      )
  ultimately show "F\<in>f\<C>_A" using f\<C>_A by fast
next
  from \<C>_A f\<C>_A show "\<And>F. F\<in>f\<C>_A \<Longrightarrow> F\<in>fold_A \<turnstile> \<C>_A"
    using fold_A_chamber_system_image_fixespointwise' fixespointwise_im by blast
qed

lemmas opp_fold_A_chamber_system_image =
  ChamberComplexApartmentSystemTriangle.fold_A_chamber_system_image[
    OF reflect
  ]

lemma fold_A_chamber_system_image_fixespointwise:
  "F \<in> ChamberComplex.\<C> A \<Longrightarrow> fixespointwise fold_A (fold_A`F)"
  using fold_A_chamber_system_image
        fold_A_chamber_system_image_fixespointwise'[of "fold_A`F"]
  by    auto

lemmas fold_A_chsys_imfix = fold_A_chamber_system_image_fixespointwise

lemmas opp_fold_A_chamber_system_image_fixespointwise =
  ChamberComplexApartmentSystemTriangle.fold_A_chsys_imfix[
    OF reflect
  ]

lemma chamber_in_fold_A_im:
  "chamber F \<Longrightarrow> F \<in> fold_A \<turnstile> A \<Longrightarrow> F \<in> fold_A \<turnstile> ChamberComplex.\<C> A"
  using apartments(1)
        ChamberComplexMorphism.chamber_system_image[OF fold_A_morph_A_A]
        ChamberComplexMorphism.simplex_map[OF fold_A_morph_A_A]
        chamber_in_apartment apartment_chamber_system_def
  by    fastforce

lemmas chamber_in_opp_fold_A_im =
  ChamberComplexApartmentSystemTriangle.chamber_in_fold_A_im[OF reflect]

lemma simplex_in_fold_A_im_image:
  assumes "x \<in> fold_A \<turnstile> A"
  shows   "fold_A ` x = x"
proof-
  from assms apartments(1) obtain C
    where "C \<in> ChamberComplex.\<C> A" "x \<subseteq> fold_A`C"
    using apartment_simplex_in_max apartment_chamber_system_def
    by    fast
  thus ?thesis
    using fold_A_chamber_system_image_fixespointwise fixespointwise_im
    by    blast
qed

lemma chamber1_notin_rfold_im: "C \<notin> opp_fold_A \<turnstile> A"
  using chambers(1,2) facet(1,2) chambers_ne(1) facet_in_chambers(1)
        min_gallery_adj adjacentI[of z] face_distance_eq_0
        min_gallery_betw_chamber_distance[of D "[]" C]
        chamber_in_opp_fold_A_im[of C] opp_fold_A_chamber_system_image
  by    auto

lemma fold_A_min_gallery_from1_map:
  "\<lbrakk> chamber F; F \<in> fold_A \<turnstile> A; min_gallery (C#Fs@[F]) \<rbrakk> \<Longrightarrow>
    min_gallery (C # fold_A \<Turnstile> Fs @ [F])"
  using chambers(1) chamber_in_fold_A_im fold_A_chamber_system_image
        facet_in_chambers(1) fold_A_min_gallery_betw_map[of C F]
        fold_A_chamber_images(1) simplex_in_fold_A_im_image
  by    simp

lemma fold_A_min_gallery_from2_map:
  "\<lbrakk> chamber F; F \<in> opp_fold_A \<turnstile> A; min_gallery (D#Fs@[F]) \<rbrakk> \<Longrightarrow>
    min_gallery (C # fold_A \<Turnstile> (Fs@[F]))"
  using chambers(2) facet_in_chambers(2) chamber_in_opp_fold_A_im
        opp_fold_A_chamber_system_image fold_A_chamber_images(2)
        fold_A_min_gallery_betw_map[of D F Fs] 
  by    simp

lemma fold_A_min_gallery_to2_map:
  assumes "chamber F" "F \<in> opp_fold_A \<turnstile> A" "min_gallery (F#Fs@[D])"
  shows   "min_gallery (fold_A \<Turnstile> (F#Fs) @ [C])"
  using   assms(1,2) min_gallery_rev[of "C # fold_A \<Turnstile> (rev Fs @ [F])"]
          min_gallery_rev[OF assms(3)] fold_A_min_gallery_from2_map[of F "rev Fs"]
          fold_A_chamber_images(2)
  by      (simp add: rev_map[THEN sym])

lemmas opp_fold_A_min_gallery_from1_map =
  ChamberComplexApartmentSystemTriangle.fold_A_min_gallery_from2_map[
    OF reflect
  ]

lemmas opp_fold_A_min_gallery_to1_map =
  ChamberComplexApartmentSystemTriangle.fold_A_min_gallery_to2_map[
    OF reflect
  ]

lemma closer_to_chamber1_not_in_rfold_im_chamber_system:
  assumes "chamber_distance C F \<le> chamber_distance D F"
  shows   "F \<notin> ChamberComplex.\<C> (opp_fold_A \<turnstile> A)"
proof
  assume "F \<in> ChamberComplex.\<C> (opp_fold_A \<turnstile> A)"
  hence F: "F \<in> res_opp_fold_A \<turnstile> ChamberComplex.\<C> A"
    using res_opp_fold_A_A_im_opp_fold_A_A_im
          ChamberComplexEndomorphism.image_chamber_system[
            OF opp_res_fold_A_endo_A
          ]
    by    simp
  hence F': "F \<in> opp_fold_A \<turnstile> ChamberComplex.\<C> A"
    using res_opp_fold_A_\<C>_A_im_opp_fold_A_\<C>_A_im by simp
  from apartments(1) have Achamber_F: "ChamberComplex.chamber A F"
    using F apartment_chamber_system_def[of A]
          ChamberComplexEndomorphism.chamber_system_image[
            OF opp_res_fold_A_endo_A
          ]
    by    auto
  from apartments(1) have F_ne_C: "F\<noteq>C"
    using F' apartment_chamber_system_simplices[of A] chamber1_notin_rfold_im
    by    auto
  have "fixespointwise opp_fold_A C"
  proof (rule apartment_standard_uniqueness_pgallery_betw, rule apartments(1))
    show "ChamberComplexMorphism A A opp_fold_A"
      using opp_fold_A_morph_A_A by fast
    from apartments(1) show "ChamberComplexMorphism A A id"
      using apartment_trivial_morphism by fast
    show "fixespointwise opp_fold_A F"
      using F' opp_fold_A_chamber_system_image_fixespointwise by fast
    def Fs \<equiv> "ARG_MIN length Fs. ChamberComplex.gallery A (F#Fs@[C])"
    with apartments(1)
      have  mingal: "ChamberComplex.min_gallery A (F#Fs@[C])"
      using A_chambers(1) Achamber_F F_ne_C
            apartment_min_gallery_least_length[of A F C]
      by    fast
    with apartments(1)
      show  5: "ChamberComplex.gallery A (F#Fs@[C])"
      and   "ChamberComplex.pgallery A (id \<Turnstile> (F#Fs@[C]))"
      using apartment_min_galleryD_gallery apartment_min_gallery_pgallery
      by    auto
    have "min_gallery (opp_fold_A \<Turnstile> (F#Fs) @ [D])"
    proof (rule opp_fold_A_min_gallery_to1_map)
      from apartments(1) show "chamber F"
        using Achamber_F apartment_chamber by fast
      from assms have  "F \<in> fold_A \<turnstile> ChamberComplex.\<C> A"
        using apartments(1) chambers(1,2) in_apartments(1,2) facet(1,2)
              chambers_ne(1) Achamber_F apartment_chamber
              apartment_chamberD_simplex
              apartment_face_distance_eq_chamber_distance_compare_other_chamber
              apartment_chamber_system_def fold_A_chamber_system_image
              apartment_chamber_system_simplices
        by    simp
      with apartments(1) show "F \<in> fold_A \<turnstile> A"
        using apartment_chamber_system_simplices[of A] by auto
      from apartments(1) show "min_gallery (F # Fs @ [C])"
        using mingal apartment_min_gallery by fast
    qed
    hence "min_gallery (opp_fold_A \<Turnstile> (F#Fs@[C]))"
      using opp_fold_A_chamber_images(2) by simp
    moreover from apartments(1) have "set (opp_fold_A \<Turnstile> (F#Fs@[C])) \<subseteq> A"
      using 5 apartment_galleryD_chamber[of A]
            apartment_chamberD_simplex[of A]
            ChamberComplexMorphism.simplex_map[OF opp_fold_A_morph_A_A]
      by    auto
    ultimately have "ChamberComplex.min_gallery A (opp_fold_A \<Turnstile> (F#Fs@[C]))"
      using apartments(1) min_gallery_in_apartment by fast
    with apartments(1)
      show  "ChamberComplex.pgallery A (opp_fold_A \<Turnstile> (F#Fs@[C]))"
      using apartment_min_gallery_pgallery
      by    fast
  qed
  hence "opp_fold_A ` C = C" using fixespointwise_im by fast
  with chambers_ne(1) show False using opp_fold_A_chamber_images(2) by fast
qed

lemmas clsrch1_nin_rfold_im_chsys =
  closer_to_chamber1_not_in_rfold_im_chamber_system

lemmas closer_to_chamber2_not_in_fold_im_chamber_system =
  ChamberComplexApartmentSystemTriangle.clsrch1_nin_rfold_im_chsys[
    OF reflect
  ]

lemma fold_A_opp_fold_A_chamber_systems:
  "ChamberComplex.\<C> A =
    (ChamberComplex.\<C> (fold_A \<turnstile> A)) \<union> (ChamberComplex.\<C> (opp_fold_A \<turnstile> A))"
  "(ChamberComplex.\<C> (fold_A \<turnstile> A)) \<inter> (ChamberComplex.\<C> (opp_fold_A \<turnstile> A)) =
    {}"
proof (rule seteqI)
  fix F assume F: "F \<in> ChamberComplex.\<C> A"
  with apartments(1) have F': "ChamberComplex.chamber A F" "F\<in>A"
    using apartment_chamber_system_def apartment_chamber_system_simplices
          apartment_chamber
    by    auto
  from F'(1) apartments(1) have F'': "chamber F"
    using apartment_chamber by auto
  show "F \<in> (ChamberComplex.\<C> (fold_A \<turnstile> A)) \<union>
          (ChamberComplex.\<C> (opp_fold_A \<turnstile> A))"
  proof (cases "chamber_distance C F \<le> chamber_distance D F")
    case True thus ?thesis
      using apartments(1) chambers(1,2) in_apartments(1,2) facet(1,2)
            chambers_ne(1) F F'(2) F'' fold_A_chamber_system_image
            apartment_face_distance_eq_chamber_distance_compare_other_chamber
            ChamberComplexMorphism.image_chamber_system[OF fold_A_morph_A_A]
      by    simp
  next
    case False thus ?thesis
      using apartments(1) chambers(1,2) in_apartments(1,2) facet(1,2)
            chambers_ne(1) F F'(2) F'' opp_fold_A_chamber_system_image
            apartment_face_distance_eq_chamber_distance_compare_other_chamber
            ChamberComplexMorphism.image_chamber_system[OF opp_fold_A_morph_A_A]
      by    simp
  qed
next
  fix F
  assume F: "F \<in> (ChamberComplex.\<C> (fold_A \<turnstile> A)) \<union>
              (ChamberComplex.\<C> (opp_fold_A \<turnstile> A))"
  thus "F \<in> ChamberComplex.\<C> A"
    using ChamberComplexMorphism.image_chamber_system_image[
            OF fold_A_morph_A_A
          ]
          ChamberComplexMorphism.image_chamber_system_image[
            OF opp_fold_A_morph_A_A
          ]
    by    fast
next
  show "(ChamberComplex.\<C> (fold_A \<turnstile> A)) \<inter>
          (ChamberComplex.\<C> (opp_fold_A \<turnstile> A)) = {}"
    using closer_to_chamber1_not_in_rfold_im_chamber_system
          closer_to_chamber2_not_in_fold_im_chamber_system
    by    force
qed

lemma fold_A_im_min_gallery':
  assumes "ChamberComplex.min_gallery (fold_A \<turnstile> A) (C#Cs)"
  shows   "ChamberComplex.min_gallery A (C#Cs)"
proof (cases Cs rule: rev_cases)
  case Nil with apartments(1) show ?thesis
    using A_chambers(1) ChamberComplex.min_gallery_simps(2)[OF complexes]
    by    simp
next
  case (snoc Fs F)
  from assms snoc apartments(1)
    have  ch: "\<forall>H\<in>set (C#Fs@[F]). ChamberComplex.chamber A H"
    using ChamberComplex.min_galleryD_gallery
          ChamberComplex.galleryD_chamber
          chambercomplex_fold_A_im
          ChamberComplex.subcomplex_chamber[OF complexes]
          chambersubcomplex_fold_A_im
    by    fastforce
  with apartments(1) have ch_F: "chamber F" using apartment_chamber by simp
  have "ChamberComplex.min_gallery A (C#Fs@[F])"
  proof (
    rule ChamberComplex.min_galleryI_betw_compare, rule complexes,
    rule apartments(1)
  )
    def Gs \<equiv> "ARG_MIN length Gs. ChamberComplex.gallery A (C#Gs@[F])"
    from assms snoc show "C\<noteq>F"
      using ChamberComplex.min_gallery_pgallery
            ChamberComplex.pgalleryD_distinct
            chambercomplex_fold_A_im
      by    fastforce
    with chambers(1) apartments(1) assms snoc Gs_def
      show 3: "ChamberComplex.min_gallery A (C#Gs@[F])"
      using ch apartment_min_gallery_least_length
      by    simp
    from assms snoc apartments(1)
      show  "ChamberComplex.gallery A (C#Fs@[F])"
      using ch ChamberComplex.min_galleryD_gallery
            ChamberComplex.galleryD_adj
            chambercomplex_fold_A_im
            ChamberComplex.gallery_def[OF complexes]
      by    fastforce
    show "length Fs = length Gs"
    proof-
      from apartments(1) have set_gal: "set (C#Gs@[F]) \<subseteq> A"
        using 3 apartment_min_galleryD_gallery apartment_galleryD_chamber
              apartment_chamberD_simplex
        by    fast
      from assms snoc have F_in: "F \<in> fold_A \<turnstile> A"
        using ChamberComplex.min_galleryD_gallery
              ChamberComplex.galleryD_chamber
              ChamberComplex.chamberD_simplex chambercomplex_fold_A_im
        by    fastforce
      with apartments(1) have "min_gallery (C # fold_A \<Turnstile> Gs @ [F])"
        using ch_F 3 apartment_min_gallery fold_A_min_gallery_from1_map by fast
      moreover have "set (fold_A \<Turnstile> (C#Gs@[F])) \<subseteq> A"
        using set_gal
              ChamberComplexMorphism.simplex_map[OF fold_A_morph_A_A]
        by    auto
      ultimately have "ChamberComplex.min_gallery A (C # fold_A \<Turnstile> Gs @ [F])"
        using apartments(1) F_in min_gallery_in_apartment
              fold_A_chamber_images(1) fold_A_chamber_system_image_fixespointwise
              simplex_in_fold_A_im_image
        by    simp
      moreover have "set (fold_A \<Turnstile> (C#Gs@[F])) \<subseteq> fold_A \<turnstile> A"
        using set_gal by auto
      ultimately show ?thesis
        using assms snoc apartments(1) F_in fold_A_chamber_images(1)
              simplex_in_fold_A_im_image
              ChamberComplex.min_gallery_in_subcomplex[
                OF complexes, OF _ chambersubcomplex_fold_A_im
              ]
              ChamberComplex.min_gallery_betw_uniform_length[ 
                OF chambercomplex_fold_A_im, of C "fold_A \<Turnstile> Gs" F Fs
              ]
        by    simp
    qed
  qed
  with snoc show ?thesis by fast
qed

lemma fold_A_im_min_gallery:
  "ChamberComplex.min_gallery (fold_A \<turnstile> A) (C#Cs) \<Longrightarrow> min_gallery (C#Cs)"
  using apartments(1) fold_A_im_min_gallery' apartment_min_gallery by fast

lemma fold_A_comp_fixespointwise:
  "fixespointwise (fold_A \<circ> opp_fold_A) (\<Union> (fold_A \<turnstile> A))"
proof (rule apartment_standard_uniqueness, rule apartments(1))

  have "fun_eq_on (fold_A \<circ> opp_fold_A) (res_fold_A \<circ> res_opp_fold_A) (\<Union>A)"
    using ChamberComplexEndomorphism.vertex_map[OF opp_res_fold_A_endo_A]
          fun_eq_onI[of "\<Union>A" "fold_A \<circ> opp_fold_A"]
    by    auto
  thus "ChamberComplexMorphism (fold_A \<turnstile> A) A (fold_A \<circ> opp_fold_A)"
    using ChamberComplexEndomorphism.endo_comp[
            OF opp_res_fold_A_endo_A res_fold_A_endo_A
          ]
          ChamberComplexEndomorphism.axioms(1)
          ChamberComplexMorphism.cong
          ChamberComplexMorphism.restrict_domain
          chambersubcomplex_fold_A_im
    by    fast

  from apartments(1) show "ChamberComplexMorphism (fold_A \<turnstile> A) A id"
    using ChamberComplexMorphism.restrict_domain apartment_trivial_morphism
          chambersubcomplex_fold_A_im
    by    fast

  from apartments(1) show "ChamberComplex.chamber (fold_A \<turnstile> A) C"
    using A_chambers(1) apartment_chamberD_simplex fold_A_chamber_images(1)
          ChamberComplex.chamber_in_subcomplex[
            OF complexes, OF _ chambersubcomplex_fold_A_im, of C
          ]
    by    fast

  show "fixespointwise (fold_A \<circ> opp_fold_A) C"
  proof-
    from facet(1) obtain v where v: "v\<notin>z" "C = insert v z"
      using facetrel_def[of z C] by fast
    have "fixespointwise (fold_A \<circ> opp_fold_A) (insert v z)"
    proof (rule fixespointwise_insert, rule fixespointwise_comp)
      show "fixespointwise opp_fold_A z"
        using facet_in_chambers(2) fixespointwise_subset[of opp_fold_A D z]
              opp_fold_A_fixespointwise2
        by    fast
      show "fixespointwise fold_A z"
        using facet_in_chambers(1) fixespointwise_subset[of fold_A C z]
              fold_A_fixespointwise1
        by    fast
      have "(fold_A \<circ> opp_fold_A) ` C = C"
        using fold_A_chamber_images(2) opp_fold_A_chamber_images(2) 
        by    (simp add: image_comp[THEN sym])
      with v(2) show "(fold_A \<circ> opp_fold_A) ` (insert v z) = insert v z" by simp
    qed
    with v(2) show ?thesis by fast
  qed

  show "\<And>Cs. ChamberComplex.min_gallery (fold_A \<turnstile> A) (C # Cs) \<Longrightarrow>
          ChamberComplex.pgallery A ((fold_A \<circ> opp_fold_A) \<Turnstile> (C # Cs))"
  proof-
    fix Cs assume Cs: "ChamberComplex.min_gallery (fold_A \<turnstile> A) (C # Cs)"
    show "ChamberComplex.pgallery A ((fold_A \<circ> opp_fold_A) \<Turnstile> (C # Cs))"
    proof (cases Cs rule: rev_cases)
      case Nil with apartments(1) show ?thesis
        using fold_A_chamber_images(2) opp_fold_A_chamber_images(2)
              A_chambers(1) ChamberComplex.pgallery_def[OF complexes]
        by    (auto simp add: image_comp[THEN sym])
    next
      case (snoc Fs F)
      from Cs snoc apartments(1)
        have  F: "F \<in> fold_A \<turnstile> A" "ChamberComplex.chamber A F"
        using ChamberComplex.min_galleryD_gallery[
                OF chambercomplex_fold_A_im
              ]
              ChamberComplex.galleryD_chamber[
                OF chambercomplex_fold_A_im, of "C#Fs@[F]"
              ]
              ChamberComplex.chamberD_simplex[OF chambercomplex_fold_A_im]
              ChamberComplex.subcomplex_chamber[
                OF complexes, OF _ chambersubcomplex_fold_A_im
              ]
        by    auto
      from F(2) apartments(1) have F': "chamber F"
        using apartment_chamber by fast
      with F(1) apartments(1)
        have  zF_CF: "face_distance z F = chamber_distance C F"
        using chamber_in_fold_A_im[of F] fold_A_chamber_system_image
        by    auto
      have "min_gallery (C # fold_A \<Turnstile> (opp_fold_A \<Turnstile> Fs @ [opp_fold_A ` F]))"
      proof (rule fold_A_min_gallery_from2_map)
        from Cs snoc
          have  Cs': "ChamberComplex.gallery (fold_A \<turnstile> A) (C#Fs@[F])"
          using ChamberComplex.min_galleryD_gallery chambercomplex_fold_A_im
          by    fastforce
        with apartments(1) have chF: "ChamberComplex.chamber A F"
          using ChamberComplex.galleryD_chamber chambercomplex_fold_A_im
                ChamberComplex.subcomplex_chamber[OF complexes]
                chambersubcomplex_fold_A_im
          by    fastforce
        with apartments(1) show  "chamber (opp_fold_A ` F)"
          using ChamberComplexMorphism.chamber_map opp_fold_A_morph_A_A
                apartment_chamber
          by    fast
        from apartments(1) show "opp_fold_A ` F \<in> opp_fold_A \<turnstile> A"
          using chF ChamberComplex.chamberD_simplex complexes by fast
        from Cs snoc apartments(1)
          show  "min_gallery (D # opp_fold_A \<Turnstile> Fs @ [opp_fold_A ` F])"
          using chF Cs' opp_fold_A_min_gallery_from1_map apartment_chamber
                ChamberComplex.chamberD_simplex
                ChamberComplex.galleryD_chamber
                chambercomplex_fold_A_im fold_A_im_min_gallery
          by    fastforce
      qed
      with snoc have "min_gallery (fold_A \<Turnstile> (opp_fold_A \<Turnstile> (C#Cs)))"
        using fold_A_chamber_images(2) opp_fold_A_chamber_images(2) by simp
      with Cs apartments(1)
        have  "ChamberComplex.min_gallery A
                (fold_A \<Turnstile> (opp_fold_A \<Turnstile> (C#Cs)))"
        using ChamberComplex.min_galleryD_gallery[
                OF chambercomplex_fold_A_im, of "C#Cs"
              ]
              ChamberComplex.galleryD_chamber[
                OF chambercomplex_fold_A_im, of "C#Cs"
              ]
              ChamberComplex.subcomplex_chamber[
                OF complexes, OF _ chambersubcomplex_fold_A_im
              ]
              apartment_chamberD_simplex
              ChamberComplexMorphism.simplex_map[OF opp_fold_A_morph_A_A]
              ChamberComplexMorphism.simplex_map[OF fold_A_morph_A_A]
        by    (force intro: min_gallery_in_apartment)
      with apartments(1)
        have  "ChamberComplex.pgallery A (fold_A \<Turnstile> (opp_fold_A \<Turnstile> (C#Cs)))"
        using apartment_min_gallery_pgallery
        by    fast
      thus ?thesis
        using ssubst[
                OF setlistmapim_comp, of "\<lambda>Cs. ChamberComplex.pgallery A Cs"
              ]
        by    fast
    qed
  qed

  from apartments(1)
    show  "\<And>Cs. ChamberComplex.min_gallery (fold_A \<turnstile> A) Cs \<Longrightarrow>
            ChamberComplex.pgallery A (id \<Turnstile> Cs)"
    using chambersubcomplex_fold_A_im
          ChamberComplex.min_gallery_pgallery[OF chambercomplex_fold_A_im]
          ChamberComplex.subcomplex_pgallery[OF complexes, of A "fold_A \<turnstile> A"]
    by    simp

qed

lemmas opp_fold_A_comp_fixespointwise =
  ChamberComplexApartmentSystemTriangle.fold_A_comp_fixespointwise[OF reflect]

lemma fold_A_fold:
  "ChamberComplexIsomorphism (opp_fold_A \<turnstile> A) (fold_A \<turnstile> A) fold_A"
proof (rule ChamberComplexMorphism.isoI_inverse)
  show "ChamberComplexMorphism (opp_fold_A \<turnstile> A) (fold_A \<turnstile> A) fold_A"
    using ChamberComplexMorphism.restrict_domain
          ChamberComplexMorphism.restrict_codomain_to_image
          ChamberComplexMorphism.cong fun_eq_on_sym[OF fun_eq_on_restrict1]
          ChamberComplexEndomorphism.axioms(1) res_fold_A_endo_A
          chambersubcomplex_opp_fold_A_im
    by    fast
  show "ChamberComplexMorphism (fold_A \<turnstile> A) (opp_fold_A \<turnstile> A) opp_fold_A"
    using ChamberComplexMorphism.restrict_domain
          ChamberComplexMorphism.restrict_codomain_to_image
          ChamberComplexMorphism.cong fun_eq_on_sym[OF fun_eq_on_restrict1]
          ChamberComplexEndomorphism.axioms(1) opp_res_fold_A_endo_A
          chambersubcomplex_fold_A_im
    by    fast
qed (rule opp_fold_A_comp_fixespointwise, rule fold_A_comp_fixespointwise)

lemma res_fold_A: "ChamberComplexFolding A res_fold_A"
proof (rule ChamberComplexFolding.intro)

  have "ChamberComplexEndomorphism A (res_fold_A)"
    using res_fold_A_endo_A by fast
  thus "ChamberComplexRetraction A (res_fold_A)"
  proof (rule ChamberComplexRetraction.intro, unfold_locales)
    fix v assume "v\<in>\<Union>A"
    moreover with apartments(1) obtain C
      where "C \<in> ChamberComplex.\<C> A" "v\<in>C"
      using apartment_simplex_in_max apartment_chamber_system_def
      by    fast
    ultimately show "res_fold_A (res_fold_A v) = res_fold_A v"
      using fold_A_chamber_system_image_fixespointwise fixespointwiseD
      by    fastforce
  qed

  show "ChamberComplexFolding_axioms A res_fold_A"
  proof
    fix F assume F: "ChamberComplex.chamber A F" "F \<in> res_fold_A \<turnstile> A"
    from F(2) have F': "F \<in> fold_A \<turnstile> A"
      using setsetmapim_restrict1[of A A fold_A] by simp
    hence "F \<in> fold_A \<turnstile> (opp_fold_A \<turnstile> A)"
      using ChamberComplexIsomorphism.surj_simplex_map[OF fold_A_fold]
      by    simp
    from this obtain G where G: "G \<in> opp_fold_A \<turnstile> A" "F = fold_A ` G" by auto
    with F(1) F' apartments(1)
      have  G': "ChamberComplex.chamber A G"
                "G \<in> ChamberComplex.\<C> (opp_fold_A \<turnstile> A)"
      using ChamberComplex.chamber_in_subcomplex[OF complexes]
            chambersubcomplex_fold_A_im
            ChamberComplexIsomorphism.chamber_preimage[OF fold_A_fold, of G]
            ChamberComplex.subcomplex_chamber[
              OF complexes, OF apartments(1) chambersubcomplex_opp_fold_A_im
            ]
            ChamberComplex.chamber_system_def[
              OF chambercomplex_opp_fold_A_im
            ]
      by    auto

    from apartments(1) G(2)
      have  1: "\<And>H. ChamberComplex.chamber A H \<and> H \<notin> fold_A \<turnstile> A \<and>
                fold_A ` H = F \<Longrightarrow> H=G"
      using G'(2) apartment_chamber_system_def[of A]
            fold_A_opp_fold_A_chamber_systems(1)
            chambercomplex_fold_A_im ChamberComplex.chamber_system_def
            ChamberComplex.chamberD_simplex
            inj_onD[
              OF ChamberComplexIsomorphism.inj_on_chamber_system,
              OF fold_A_fold
            ]
      by    blast
    with apartments(1)
      have  "\<And>H. ChamberComplex.chamber A H \<and> H \<notin> res_fold_A \<turnstile> A \<and>
              res_fold_A ` H = F \<Longrightarrow> H=G"
      using 1 res_fold_A_A_chamber_image apartment_chamberD_simplex
            res_fold_A_A_im_fold_A_A_im
      by    auto
    moreover from apartments(1) have "G \<notin> res_fold_A \<turnstile> A"
      using G'
            ChamberComplex.chamber_system_def[OF chambercomplex_fold_A_im]
            ChamberComplex.chamber_in_subcomplex[
              OF complexes, OF _ chambersubcomplex_fold_A_im
            ]
            fold_A_opp_fold_A_chamber_systems(2) res_fold_A_A_im_fold_A_A_im
      by    auto
    ultimately
      show  "\<exists>!G. ChamberComplex.chamber A G \<and> G \<notin> res_fold_A \<turnstile> A \<and>
              res_fold_A ` G = F"
      using G'(1) G(2) res_fold_A_A_chamber_image ex1I[of _ G]
      by    force
  qed

qed

lemmas opp_res_fold_A =
  ChamberComplexApartmentSystemTriangle.res_fold_A[OF reflect]

end (* context ChamberComplexApartmentSystemTriangle *)

subsection {* Building locale and basic lemmas *}

text {* 
  Finally, we define a (thick) building to be a thick chamber complex with a system of apartments.
*}

locale Building = ChamberComplexWithApartmentSystem X \<A>
  for X :: "'a set set"
  and \<A> :: "'a set set set"
+ assumes thick: "ThickChamberComplex X"
begin

abbreviation "some_third_chamber \<equiv>
                ThickChamberComplex.some_third_chamber X"

lemmas some_third_chamberD_facet =
  ThickChamberComplex.some_third_chamberD_facet [OF thick]

lemmas some_third_chamberD_ne =
  ThickChamberComplex.some_third_chamberD_ne [OF thick]

lemmas chamber_some_third_chamber =
  ThickChamberComplex.chamber_some_third_chamber [OF thick]

end (* context Building *)

subsection {* Apartments are uniformly Coxeter *}

text {*
  Using the assumption of thickness, we may use the special situation
  @{const ChamberComplexApartmentSystemTriangle} to verify that apartments have enough pairs of
  opposed foldings to ensure that they are isomorphic to a Coxeter complex. Since the apartments
  are all isomorphic, they are uniformly isomorphic to a single Coxeter complex.
*}

context Building
begin

lemma apartments_have_many_foldings1:
  assumes "A\<in>\<A>" "chamber C" "chamber D" "C\<sim>D" "C\<noteq>D" "C\<in>A" "D\<in>A"
  defines "E \<equiv> some_third_chamber C D (C\<inter>D)"
  defines "B  \<equiv> supapartment C E"
  and     "B' \<equiv> supapartment D E"
  defines "f \<equiv> restrict1 (canonical_retraction A D \<circ> canonical_retraction B  C)
            (\<Union>A)"
  and     "g \<equiv> restrict1 (canonical_retraction A C \<circ> canonical_retraction B' D)
            (\<Union>A)"
  shows   "f`D = C" "ChamberComplexFolding A f"
          "g`C = D" "ChamberComplexFolding A g"
proof-
  from assms have 1:
    "ChamberComplexApartmentSystemTriangle X \<A> A B B' C D E (C\<inter>D)"
    using adjacent_int_facet1[of C D] adjacent_int_facet2[of C D]
          some_third_chamberD_facet chamber_some_third_chamber
          some_third_chamberD_ne[of C "C\<inter>D" D] supapartmentD
    by    unfold_locales auto
  from f_def g_def
    show  "ChamberComplexFolding A f" "ChamberComplexFolding A g"
          "f`D = C" "g`C = D" 
    using ChamberComplexApartmentSystemTriangle.res_fold_A [OF 1]
          ChamberComplexApartmentSystemTriangle.opp_res_fold_A[OF 1]
          ChamberComplexApartmentSystemTriangle.res_fold_A_chamber_images(2)[
            OF 1
          ]
          ChamberComplexApartmentSystemTriangle.res_opp_fold_A_chamber_images(2)[
            OF 1
          ]
    by    auto
qed

lemma apartments_have_many_foldings2:
  assumes "A\<in>\<A>" "chamber C" "chamber D" "C\<sim>D" "C\<noteq>D" "C\<in>A" "D\<in>A"
  defines "E \<equiv> some_third_chamber C D (C\<inter>D)"
  defines "B  \<equiv> supapartment C E"
  and     "B' \<equiv> supapartment D E"
  defines "f \<equiv> restrict1 (canonical_retraction A D \<circ> canonical_retraction B  C)
            (\<Union>A)"
  and     "g \<equiv> restrict1 (canonical_retraction A C \<circ> canonical_retraction B' D)
            (\<Union>A)"
  shows   "OpposedThinChamberComplexFoldings A f g C"
proof (rule OpposedThinChamberComplexFoldings.intro)
  from assms show "ChamberComplexFolding A f" "ChamberComplexFolding A g"
    using apartments_have_many_foldings1(2,4)[of A C D] by auto
  show "OpposedThinChamberComplexFoldings_axioms A f g C"
  proof (
    unfold_locales, rule chamber_in_apartment, rule assms(1), rule assms(6),
    rule assms(2)
  )
    from assms(1-7) E_def B_def B'_def g_def f_def
      have  gC: "g`C = D"
      and   fD: "f`D = C"
      using apartments_have_many_foldings1(1)[of A C D]
            apartments_have_many_foldings1(3)[of A C D]
      by    auto
    with assms(4,5) show "C \<sim> g`C" "C \<noteq> g`C" "f`g`C = C" by auto
  qed
qed (rule thincomplexes, rule assms(1))

lemma apartments_have_many_foldings3:
  assumes "A\<in>\<A>" "chamber C" "chamber D" "C\<sim>D" "C\<noteq>D" "C\<in>A" "D\<in>A"
  shows   "\<exists>f g. OpposedThinChamberComplexFoldings A f g C \<and> D=g`C"
proof
  def E \<equiv> "some_third_chamber C D (C\<inter>D)"
  def B \<equiv> "supapartment C E"
  def f \<equiv> "restrict1 (canonical_retraction A D \<circ> canonical_retraction B C) (\<Union>A)"
  show "\<exists>g. OpposedThinChamberComplexFoldings A f g C \<and> D = g ` C"
  proof
    def B' \<equiv> "supapartment D E"
    def g \<equiv> "restrict1 (canonical_retraction A C \<circ> canonical_retraction B' D) (\<Union>A)"
    from assms E_def B_def f_def B'_def g_def
      show  "OpposedThinChamberComplexFoldings A f g C \<and> D = g`C"
      using apartments_have_many_foldings1(3)[of A C D]
            apartments_have_many_foldings2
      by    auto
  qed
qed

lemma apartments_have_many_foldings:
  assumes "A\<in>\<A>" "C\<in>A" "chamber C"
  shows   "ThinChamberComplexManyFoldings A C"
proof (
  rule ThinChamberComplex.ThinChamberComplexManyFoldingsI,
  rule thincomplexes, rule assms(1), rule chamber_in_apartment,
  rule assms(1), rule assms(2), rule assms(3)
)
  from assms(1)
    show "\<And>C D. ChamberComplex.chamber A C \<Longrightarrow>
            ChamberComplex.chamber A D \<Longrightarrow> C\<sim>D \<Longrightarrow>
            C\<noteq>D \<Longrightarrow>
            \<exists>f g. OpposedThinChamberComplexFoldings A f g C \<and> D = g ` C"
    using apartments_have_many_foldings3 apartment_chamber
          apartment_chamberD_simplex
    by    simp
qed

theorem apartments_are_coxeter:
  "A\<in>\<A> \<Longrightarrow> \<exists>S::'a permutation set. (
    CoxeterComplex S \<and>
    (\<exists>\<psi>. ChamberComplexIsomorphism A (CoxeterComplex.TheComplex S) \<psi>)
  )"
  using no_trivial_apartments apartment_simplex_in_max[of A]
        apartment_chamberD_simplex[of A] apartment_chamber[of A]
        apartments_have_many_foldings[of A]
        ThinChamberComplexManyFoldings.ex_iso_to_coxeter_complex[of A]
  by    fastforce

corollary apartments_are_uniformly_coxeter:
  assumes "X\<noteq>{}"
  shows   "\<exists>S::'a permutation set. CoxeterComplex S \<and>
            (\<forall>A\<in>\<A>. \<exists>\<psi>.
              ChamberComplexIsomorphism A (CoxeterComplex.TheComplex S) \<psi>
            )"
proof-
  from assms obtain C where C: "chamber C" using simplex_in_max by fast
  from this obtain A where A: "A\<in>\<A>" "C\<in>A" using containtwo by fast
  from A(1) obtain S :: "'a permutation set" and \<psi>
    where S: "CoxeterComplex S"
    and   \<psi>: "ChamberComplexIsomorphism A (CoxeterComplex.TheComplex S) \<psi>"
    using apartments_are_coxeter
    by    fast
  have "\<forall>B\<in>\<A>. \<exists>\<phi>.
        ChamberComplexIsomorphism B (CoxeterComplex.TheComplex S) \<phi>"
  proof
    fix B assume B: "B\<in>\<A>"
    hence "B\<noteq>{}" using no_trivial_apartments by fast
    with B obtain C' where C': "chamber C'" "C'\<in>B"
      using apartment_simplex_in_max apartment_chamberD_simplex
            apartment_chamber[OF B]
      by    force
    from C C'(1) obtain B' where "B'\<in>\<A>" "C\<in>B'" "C'\<in>B'"
      using containtwo by fast
    with A B C C' \<psi>
      show  "\<exists>\<phi>. ChamberComplexIsomorphism B
              (CoxeterComplex.TheComplex S) \<phi>"
      using strong_intersecttwo
            ChamberComplexIsomorphism.iso_comp[of B' A _ _ \<psi>]
            ChamberComplexIsomorphism.iso_comp[of B B']
      by    blast
  qed
  with S show ?thesis by auto
qed

end (* context Building *)

end (* theory *)
