(*  Title:       NaturalTransformation
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter NaturalTransformation

theory NaturalTransformation
imports Functor
begin

  section "Definition of a Natural Transformation"
    
  text\<open>
    As is the case for functors, the ``object-free'' definition of category
    makes it possible to view natural transformations as functions on arrows.
    In particular, a natural transformation between functors
    @{term F} and @{term G} from @{term A} to @{term B} can be represented by
    the map that takes each arrow @{term f} of @{term A} to the diagonal of the
    square in @{term B} corresponding to the transformation of @{term "F f"}
    to @{term "G f"}.  The images of the identities of @{term A} under this
    map are the usual components of the natural transformation.
    This representation exhibits natural transformations as a kind of generalization
    of functors, and in fact we can directly identify functors with identity
    natural transformations.
    However, functors are still necessary to state the defining conditions for
    a natural transformation, as the domain and codomain of a natural transformation
    cannot be recovered from the map on arrows that represents it.

    Like functors, natural transformations preserve arrows and map non-arrows to null.
    Natural transformations also ``preserve'' domain and codomain, but in a more general
    sense than functors. The naturality conditions, which express the two ways of factoring
    the diagonal of a commuting square, are degenerate in the case of an identity transformation.
\<close>

  locale natural_transformation =
    A: category A +
    B: category B + 
    F: "functor" A B F +
    G: "functor" A B G
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'a \<Rightarrow> 'b"
  and \<tau> :: "'a \<Rightarrow> 'b" +
  assumes is_extensional: "\<not>A.arr f \<Longrightarrow> \<tau> f = B.null"
  and preserves_dom [iff]: "A.arr f \<Longrightarrow> B.dom (\<tau> f) = F (A.dom f)"
  and preserves_cod [iff]: "A.arr f \<Longrightarrow> B.cod (\<tau> f) = G (A.cod f)"
  and is_natural_1 [iff]: "A.arr f \<Longrightarrow> G f \<cdot>\<^sub>B \<tau> (A.dom f) = \<tau> f"
  and is_natural_2 [iff]: "A.arr f \<Longrightarrow> \<tau> (A.cod f) \<cdot>\<^sub>B F f = \<tau> f"
  begin

    lemma naturality:
    assumes "A.arr f"
    shows "\<tau> (A.cod f) \<cdot>\<^sub>B F f = G f \<cdot>\<^sub>B \<tau> (A.dom f)"
      using assms is_natural_1 is_natural_2 by simp

    text\<open>
      The following fact for natural transformations provides us with the same advantages
      as the corresponding fact for functors.
\<close>

    lemma preserves_reflects_arr [iff]:
    shows "B.arr (\<tau> f) \<longleftrightarrow> A.arr f"
      using is_extensional A.arr_cod_iff_arr B.arr_cod_iff_arr preserves_cod by force

    lemma preserves_hom [intro]:
    assumes "\<guillemotleft>f : a \<rightarrow>\<^sub>A b\<guillemotright>"
    shows "\<guillemotleft>\<tau> f : F a \<rightarrow>\<^sub>B G b\<guillemotright>"
      using assms
      by (metis A.in_homE B.arr_cod_iff_arr B.in_homI G.preserves_arr G.preserves_cod
          preserves_cod preserves_dom)

    lemma preserves_comp_1:
    assumes "A.seq f' f"
    shows "\<tau> (f' \<cdot>\<^sub>A f) = G f' \<cdot>\<^sub>B \<tau> f"
      using assms
      by (metis A.seqE A.dom_comp B.comp_assoc G.preserves_comp is_natural_1)

    lemma preserves_comp_2:
    assumes "A.seq f' f"
    shows "\<tau> (f' \<cdot>\<^sub>A f) = \<tau> f' \<cdot>\<^sub>B F f"
      using assms
      by (metis A.arr_cod_iff_arr A.cod_comp B.comp_assoc F.preserves_comp is_natural_2)

    text\<open>
      A natural transformation that also happens to be a functor is equal to
      its own domain and codomain.
\<close>

    lemma functor_implies_equals_dom:
    assumes "functor A B \<tau>"
    shows "F = \<tau>"
    proof
      interpret \<tau>: "functor" A B \<tau> using assms by auto
      fix f
      show "F f = \<tau> f"
        using assms
        by (metis A.dom_cod B.comp_cod_arr F.is_extensional F.preserves_arr F.preserves_cod
            \<tau>.preserves_dom is_extensional is_natural_2 preserves_dom)
    qed

    lemma functor_implies_equals_cod:
    assumes "functor A B \<tau>"
    shows "G = \<tau>"
    proof
      interpret \<tau>: "functor" A B \<tau> using assms by auto
      fix f
      show "G f = \<tau> f"
        using assms
        by (metis A.cod_dom B.comp_arr_dom F.preserves_arr G.is_extensional G.preserves_arr
            G.preserves_dom B.cod_dom functor_implies_equals_dom is_extensional
            is_natural_1 preserves_cod preserves_dom)
    qed
          
  end

  section "Components of a Natural Transformation"

  text\<open>
    The values taken by a natural transformation on identities are the \emph{components}
    of the transformation.  We have the following basic technique for proving two natural
    transformations equal: show that they have the same components.
\<close>

  lemma eqI:
  assumes "natural_transformation A B F G \<sigma>" and "natural_transformation A B F G \<sigma>'"
  and "\<And>a. partial_magma.ide A a \<Longrightarrow> \<sigma> a = \<sigma>' a"
  shows "\<sigma> = \<sigma>'"
  proof -
    interpret A: category A using assms(1) natural_transformation_def by blast
    interpret \<sigma>: natural_transformation A B F G \<sigma> using assms(1) by auto
    interpret \<sigma>': natural_transformation A B F G \<sigma>' using assms(2) by auto
    have "\<And>f. \<sigma> f = \<sigma>' f"
      using assms(3) \<sigma>.is_natural_2 \<sigma>'.is_natural_2 \<sigma>.is_extensional \<sigma>'.is_extensional A.ide_cod
      by metis
    thus ?thesis by auto
  qed

  text\<open>
    As equality of natural transformations is determined by equality of components,
    a natural transformation may be uniquely defined by specifying its components.
    The extension to all arrows is given by @{prop is_natural_1} or equivalently
    by @{prop is_natural_2}.
\<close>

  locale transformation_by_components =
    A: category A +
    B: category B + 
    F: "functor" A B F +
    G: "functor" A B G
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'a \<Rightarrow> 'b"
  and t :: "'a \<Rightarrow> 'b" +
  assumes maps_ide_in_hom [intro]: "A.ide a \<Longrightarrow> \<guillemotleft>t a : F a \<rightarrow>\<^sub>B G a\<guillemotright>"
  and is_natural: "A.arr f \<Longrightarrow> t (A.cod f) \<cdot>\<^sub>B F f = G f \<cdot>\<^sub>B t (A.dom f)"
  begin

    definition map
    where "map f = (if A.arr f then t (A.cod f) \<cdot>\<^sub>B F f else B.null)"

    lemma map_simp_ide [simp]:
    assumes "A.ide a"
    shows "map a = t a"
      using assms map_def B.comp_arr_dom [of "t a"] maps_ide_in_hom by fastforce

    lemma is_natural_transformation:
    shows "natural_transformation A B F G map"
      using map_def is_natural
      apply (unfold_locales, simp_all)
         apply (metis A.ide_dom B.dom_comp B.seqI
                      G.preserves_arr G.preserves_dom B.in_homE maps_ide_in_hom)
        apply (metis A.ide_dom B.arrI B.cod_comp B.in_homE B.seqI
                     G.preserves_arr G.preserves_cod G.preserves_dom maps_ide_in_hom)
       apply (metis A.ide_dom B.comp_arr_dom B.in_homE maps_ide_in_hom)
      by (metis B.comp_assoc A.comp_cod_arr F.preserves_comp)

  end

  sublocale transformation_by_components \<subseteq> natural_transformation A B F G map
    using is_natural_transformation by auto

  lemma transformation_by_components_idem [simp]:
  assumes "natural_transformation A B F G \<tau>"
  shows "transformation_by_components.map A B F \<tau> = \<tau>"
  proof -
    interpret \<tau>: natural_transformation A B F G \<tau> using assms by blast
    interpret \<tau>': transformation_by_components A B F G \<tau>
      by (unfold_locales, auto) 
    show ?thesis
      using assms \<tau>'.map_simp_ide \<tau>'.is_natural_transformation eqI by blast
  qed

  section "Functors as Natural Transformations"

  text\<open>
    A functor is a special case of a natural transformation, in the sense that the same map
    that defines the functor also defines an identity natural transformation.
\<close>

  lemma functor_is_transformation [simp]:
  assumes "functor A B F"
  shows "natural_transformation A B F F F"
  proof -
    interpret "functor" A B F using assms by auto
    show "natural_transformation A B F F F"
      using is_extensional B.comp_arr_dom B.comp_cod_arr by (unfold_locales, simp_all)
  qed

  sublocale "functor" \<subseteq> natural_transformation A B F F F
    by (simp add: functor_axioms)

  section "Constant Natural Transformations"

  text\<open>
    A constant natural transformation is one whose components are all the same arrow.
\<close>

  locale constant_transformation =
    A: category A +
    B: category B +
    F: constant_functor A B "B.dom g" +
    G: constant_functor A B "B.cod g"
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and g :: 'b +
  assumes value_is_arr: "B.arr g"
  begin

    definition map
    where "map f \<equiv> if A.arr f then g else B.null"

    lemma map_simp [simp]:
    assumes "A.arr f"
    shows "map f = g"
      using assms map_def by auto

    lemma is_natural_transformation:
    shows "natural_transformation A B F.map G.map map"
      apply unfold_locales
      using map_def value_is_arr B.comp_arr_dom B.comp_cod_arr by auto

    lemma is_functor_if_value_is_ide:
    assumes "B.ide g"
    shows "functor A B map"
      apply unfold_locales using assms map_def by auto

  end

  sublocale constant_transformation \<subseteq> natural_transformation A B F.map G.map map
    using is_natural_transformation by auto

  context constant_transformation
  begin

    lemma equals_dom_if_value_is_ide:
    assumes "B.ide g"
    shows "map = F.map"
      using assms functor_implies_equals_dom is_functor_if_value_is_ide by auto

    lemma equals_cod_if_value_is_ide:
    assumes "B.ide g"
    shows "map = G.map"
      using assms functor_implies_equals_dom is_functor_if_value_is_ide by auto

  end

  section "Vertical Composition"

  text\<open>
    Vertical composition is a way of composing natural transformations \<open>\<sigma>: F \<rightarrow> G\<close>
    and \<open>\<tau>: G \<rightarrow> H\<close>, between parallel functors @{term F}, @{term G}, and @{term H}
    to obtain a natural transformation from @{term F} to @{term H}.
    The composite is traditionally denoted by \<open>\<tau> o \<sigma>\<close>, however in the present
    setting this notation is misleading because it is horizontal composite, rather than
    vertical composite, that coincides with composition of natural transformations as
    functions on arrows.
\<close>

  locale vertical_composite =
    A: category A +
    B: category B +
    F: "functor" A B F +
    G: "functor" A B G +
    H: "functor" A B H +
    \<sigma>: natural_transformation A B F G \<sigma> +
    \<tau>: natural_transformation A B G H \<tau>
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'a \<Rightarrow> 'b"
  and H :: "'a \<Rightarrow> 'b"
  and \<sigma> :: "'a \<Rightarrow> 'b"
  and \<tau> :: "'a \<Rightarrow> 'b"
  begin

    text\<open>
      Vertical composition takes an arrow @{term "A.in_hom a b f"} to an arrow in
      @{term "B.hom (F a) (G b)"}, which we can obtain by forming either of
      the composites @{term "B (\<tau> b) (\<sigma> f)"} or @{term "B (\<tau> f) (\<sigma> a)"}, which are
      equal to each other.
\<close>

    definition map
    where "map f = (if A.arr f then \<tau> (A.cod f) \<cdot>\<^sub>B \<sigma> f else B.null)"

    lemma map_seq:
    assumes "A.arr f"
    shows "B.seq (\<tau> (A.cod f)) (\<sigma> f)"
      using assms by auto

    lemma map_simp_ide:
    assumes "A.ide a"
    shows "map a = \<tau> a \<cdot>\<^sub>B \<sigma> a"
      using assms map_def by auto

    lemma map_simp_1:
    assumes "A.arr f"
    shows "map f = \<tau> (A.cod f) \<cdot>\<^sub>B \<sigma> f"
      using assms by (simp add: map_def)

    lemma map_simp_2:
    assumes "A.arr f"
    shows "map f = \<tau> f \<cdot>\<^sub>B \<sigma> (A.dom f)"
      using assms
      by (metis B.comp_assoc \<sigma>.is_natural_2 \<sigma>.naturality \<tau>.is_natural_1 \<tau>.naturality map_simp_1)

    lemma is_natural_transformation:
    shows "natural_transformation A B F H map"
      using map_def map_simp_1 map_simp_2 map_seq B.comp_assoc
      apply (unfold_locales, simp_all)
      by (metis B.comp_assoc \<tau>.is_natural_1)

  end

  sublocale vertical_composite \<subseteq> natural_transformation A B F H map
    using is_natural_transformation by auto

  text\<open>
    Functors are the identities for vertical composition.
\<close>

  lemma vcomp_ide_dom [simp]:
  assumes "natural_transformation A B F G \<tau>"
  shows "vertical_composite.map A B F \<tau> = \<tau>"
    using assms apply (intro eqI)
      apply auto[2]
     apply (meson functor_is_transformation natural_transformation_def vertical_composite.intro
                  vertical_composite.is_natural_transformation)
  proof -
    fix a :: 'a
    have "vertical_composite A B F F G F \<tau>"
      by (meson assms functor_is_transformation natural_transformation.axioms(1)
                natural_transformation.axioms(2) natural_transformation.axioms(3)
                natural_transformation.axioms(4) vertical_composite.intro)
    thus "vertical_composite.map A B F \<tau> a = \<tau> a"
      using assms natural_transformation.is_extensional natural_transformation.is_natural_2
            vertical_composite.map_def
      by fastforce
  qed
    
  lemma vcomp_ide_cod [simp]:
  assumes "natural_transformation A B F G \<tau>"
  shows "vertical_composite.map A B \<tau> G = \<tau>"
    using assms apply (intro eqI)
      apply auto[2]
     apply (meson functor_is_transformation natural_transformation_def vertical_composite.intro
                  vertical_composite.is_natural_transformation)
  proof -
    fix a :: 'a
    assume a: "partial_magma.ide A a"
    interpret Go\<tau>: vertical_composite A B F G G \<tau> G
      by (meson assms functor_is_transformation natural_transformation.axioms(1)
                natural_transformation.axioms(2) natural_transformation.axioms(3)
                natural_transformation.axioms(4) vertical_composite.intro)
    show "vertical_composite.map A B \<tau> G a = \<tau> a"
      using assms a natural_transformation.is_extensional natural_transformation.is_natural_1
            Go\<tau>.map_simp_ide [of a] Go\<tau>.B.comp_cod_arr
      by simp
  qed

  text\<open>
    Vertical composition is associative.
\<close>

  lemma vcomp_assoc [simp]:
  assumes "natural_transformation A B F G \<rho>"
  and "natural_transformation A B G H \<sigma>"
  and "natural_transformation A B H K \<tau>"
  shows "vertical_composite.map A B (vertical_composite.map A B \<rho> \<sigma>) \<tau>
            = vertical_composite.map A B \<rho> (vertical_composite.map A B \<sigma> \<tau>)"
  proof -
    interpret A: category A
      using assms(1) natural_transformation_def functor_def by blast
    interpret B: category B
      using assms(1) natural_transformation_def functor_def by blast
    interpret \<rho>: natural_transformation A B F G \<rho> using assms(1) by auto
    interpret \<sigma>: natural_transformation A B G H \<sigma> using assms(2) by auto
    interpret \<tau>: natural_transformation A B H K \<tau> using assms(3) by auto
    interpret \<rho>\<sigma>: vertical_composite A B F G H \<rho> \<sigma> ..
    interpret \<sigma>\<tau>: vertical_composite A B G H K \<sigma> \<tau> ..
    interpret \<rho>_\<sigma>\<tau>: vertical_composite A B F G K \<rho> \<sigma>\<tau>.map ..
    interpret \<rho>\<sigma>_\<tau>: vertical_composite A B F H K \<rho>\<sigma>.map \<tau> ..
    show ?thesis
      using \<rho>\<sigma>_\<tau>.is_natural_transformation \<rho>_\<sigma>\<tau>.natural_transformation_axioms
      apply (intro eqI, simp_all)
      using \<rho>\<sigma>.map_simp_ide \<rho>\<sigma>_\<tau>.map_simp_ide \<rho>_\<sigma>\<tau>.map_simp_ide \<sigma>\<tau>.map_simp_ide B.comp_assoc
      by force
  qed

  section "Natural Isomorphisms"

  text\<open>
    A natural isomorphism is a natural transformation each of whose components
    is an isomorphism.  Equivalently, a natural isomorphism is a natural transformation
    that is invertible with respect to vertical composition.
\<close>

  locale natural_isomorphism = natural_transformation A B F G \<tau>
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'a \<Rightarrow> 'b"
  and \<tau> :: "'a \<Rightarrow> 'b" +
  assumes components_are_iso [simp]: "A.ide a \<Longrightarrow> B.iso (\<tau> a)"
  begin

    text \<open>
      Natural isomorphisms preserve isomorphisms, in the sense that the sides of
      of the naturality square determined by an isomorphism are all isomorphisms,
      so the diagonal is, as well.
\<close>

    lemma preserves_iso:
    assumes "A.iso f"
    shows "B.iso (\<tau> f)"
      using assms
      by (metis A.ide_dom A.iso_is_arr B.isos_compose G.preserves_iso components_are_iso
          is_natural_2 naturality preserves_reflects_arr)

  end

  text \<open>
    Since the function that represents a functor is formally identical to the function
    that represents the corresponding identity natural transformation, no additional locale
    is needed for identity natural transformations.  However, an identity natural transformation
    is also a natural isomorphism, so it is useful for @{locale functor} to inherit from the
    @{locale natural_isomorphism} locale.
\<close>

  sublocale "functor" \<subseteq> natural_isomorphism A B F F F
    apply unfold_locales
    using preserves_ide B.ide_is_iso by simp

  definition naturally_isomorphic
  where "naturally_isomorphic A B F G = (\<exists>\<tau>. natural_isomorphism A B F G \<tau>)"

  lemma naturally_isomorphic_respects_full_functor:
  assumes "naturally_isomorphic A B F G"
  and "full_functor A B F"
  shows "full_functor A B G"
  proof -
    obtain \<phi> where \<phi>: "natural_isomorphism A B F G \<phi>"
      using assms naturally_isomorphic_def by blast
    interpret \<phi>: natural_isomorphism A B F G \<phi>
      using \<phi> by auto
    interpret \<phi>.F: full_functor A B F
      using assms by auto
    write A (infixr "\<cdot>\<^sub>A" 55)
    write B (infixr "\<cdot>\<^sub>B" 55)
    write \<phi>.A.in_hom ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>A _\<guillemotright>")
    write \<phi>.B.in_hom ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")
    show "full_functor A B G"
    proof
      fix a a' g
      assume a': "\<phi>.A.ide a'" and a: "\<phi>.A.ide a"
      and g: "\<guillemotleft>g : G a' \<rightarrow>\<^sub>B G a\<guillemotright>"
      show "\<exists>f. \<guillemotleft>f : a' \<rightarrow>\<^sub>A a\<guillemotright> \<and> G f = g"
      proof -
        let ?g' = "\<phi>.B.inv (\<phi> a) \<cdot>\<^sub>B g \<cdot>\<^sub>B \<phi> a'"
        have g': "\<guillemotleft>?g' : F a' \<rightarrow>\<^sub>B F a\<guillemotright>"
          using a a' g \<phi>.preserves_hom \<phi>.components_are_iso \<phi>.B.inv_in_hom by force
        obtain f' where f': "\<guillemotleft>f' : a' \<rightarrow>\<^sub>A a\<guillemotright> \<and> F f' = ?g'"
          using a a' g' \<phi>.F.is_full [of a a' ?g'] by blast
        moreover have "G f' = g"
        proof -
          have "G f' = \<phi> a \<cdot>\<^sub>B ?g' \<cdot>\<^sub>B \<phi>.B.inv (\<phi> a')"
          proof -
            have "\<phi>.B.seq (\<phi> a) (F f')"
              using a f' by (metis \<phi>.A.in_homE \<phi>.is_natural_2 \<phi>.preserves_reflects_arr)
            moreover have "G f' \<cdot>\<^sub>B \<phi> a' = \<phi> a \<cdot>\<^sub>B F f'"
              using a a' f' \<phi>.naturality [of f'] by force
            ultimately show ?thesis
              using a a' f' \<phi>.components_are_iso \<phi>.B.invert_side_of_triangle(2)
              by (metis \<phi>.B.comp_assoc)
          qed
          also have "... = (\<phi> a \<cdot>\<^sub>B \<phi>.B.inv (\<phi> a)) \<cdot>\<^sub>B g \<cdot>\<^sub>B \<phi> a' \<cdot>\<^sub>B \<phi>.B.inv (\<phi> a')"
            using \<phi>.B.comp_assoc by auto
          also have "... = g"
            using a a' g \<phi>.B.comp_arr_dom \<phi>.B.comp_cod_arr \<phi>.B.comp_arr_inv \<phi>.B.comp_inv_arr
                  \<phi>.B.inv_is_inverse
            by auto
          finally show ?thesis by blast
        qed
        ultimately show ?thesis by auto
      qed
    qed
  qed

  lemma naturally_isomorphic_respects_faithful_functor:
  assumes "naturally_isomorphic A B F G"
  and "faithful_functor A B F"
  shows "faithful_functor A B G"
  proof -
    obtain \<phi> where \<phi>: "natural_isomorphism A B F G \<phi>"
      using assms naturally_isomorphic_def by blast
    interpret \<phi>: natural_isomorphism A B F G \<phi>
      using \<phi> by auto
    interpret \<phi>.F: faithful_functor A B F
      using assms by auto
    write A (infixr "\<cdot>\<^sub>A" 55)
    write B (infixr "\<cdot>\<^sub>B" 55)
    write \<phi>.A.in_hom ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>A _\<guillemotright>")
    write \<phi>.B.in_hom ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")
    show "faithful_functor A B G"
    proof
      fix \<mu> \<mu>'
      assume par: "\<phi>.A.par \<mu> \<mu>'" and eq: "G \<mu> = G \<mu>'"
      show "\<mu> = \<mu>'"
      proof -
        have "\<phi> (\<phi>.A.cod \<mu>) \<cdot>\<^sub>B F \<mu> = \<phi> (\<phi>.A.cod \<mu>) \<cdot>\<^sub>B F \<mu>'"
          using par eq \<phi>.naturality by metis
        moreover have "\<phi>.B.mono (\<phi> (\<phi>.A.cod \<mu>))"
          using par \<phi>.components_are_iso \<phi>.B.iso_is_section \<phi>.B.section_is_mono by auto
        ultimately have "F \<mu> = F \<mu>'"
          using par \<phi>.B.monoE [of "\<phi> (\<phi>.A.cod \<mu>)" "F \<mu>" "F \<mu>'"] by auto
        thus "\<mu> = \<mu>'"
          using par \<phi>.F.is_faithful by blast
      qed
    qed
  qed

  locale inverse_transformation =
    A: category A +
    B: category B +
    F: "functor" A B F +
    G: "functor" A B G +
    \<tau>: natural_isomorphism A B F G \<tau>
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'a \<Rightarrow> 'b"
  and \<tau> :: "'a \<Rightarrow> 'b"
  begin

    interpretation \<tau>': transformation_by_components A B G F "\<lambda>a. B.inv (\<tau> a)"
    proof
      fix f :: 'a
      show "A.ide f \<Longrightarrow> \<guillemotleft>B.inv (\<tau> f) : G f \<rightarrow>\<^sub>B F f\<guillemotright>"
        using B.inv_in_hom \<tau>.components_are_iso A.ide_in_hom by blast
      show "A.arr f \<Longrightarrow> B.inv (\<tau> (A.cod f)) \<cdot>\<^sub>B G f = F f \<cdot>\<^sub>B B.inv (\<tau> (A.dom f))"
        by (metis A.ide_cod A.ide_dom B.invert_opposite_sides_of_square \<tau>.components_are_iso
            \<tau>.is_natural_2 \<tau>.naturality \<tau>.preserves_reflects_arr)
    qed

    definition map
    where "map = \<tau>'.map"

    lemma map_ide_simp [simp]:
    assumes "A.ide a"
    shows "map a = B.inv (\<tau> a)"
      using assms map_def by fastforce

    lemma map_simp:
    assumes "A.arr f"
    shows "map f = B.inv (\<tau> (A.cod f)) \<cdot>\<^sub>B G f"
      using assms map_def by (simp add: \<tau>'.map_def)

    lemma is_natural_transformation:
    shows "natural_transformation A B G F map"
      by (simp add: \<tau>'.natural_transformation_axioms map_def)

    lemma inverts_components:
    assumes "A.ide a"
    shows "B.inverse_arrows (\<tau> a) (map a)"
      using assms \<tau>.components_are_iso B.ide_is_iso B.inv_is_inverse B.inverse_arrows_def map_def
      by (metis \<tau>'.map_simp_ide)

  end

  sublocale inverse_transformation \<subseteq> natural_transformation A B G F map
    using is_natural_transformation by auto

  sublocale inverse_transformation \<subseteq> natural_isomorphism A B G F map
    by (meson B.category_axioms B.iso_def category.inverse_arrows_sym inverts_components
              natural_isomorphism.intro natural_isomorphism_axioms.intro
              natural_transformation_axioms)

  lemma inverse_inverse_transformation [simp]:
  assumes "natural_isomorphism A B F G \<tau>"
  shows "inverse_transformation.map A B F (inverse_transformation.map A B G \<tau>) = \<tau>"
  proof -
    interpret \<tau>: natural_isomorphism A B F G \<tau>
      using assms by auto
    interpret \<tau>': inverse_transformation A B F G \<tau> ..
    interpret \<tau>'': inverse_transformation A B G F \<tau>'.map ..
    show "\<tau>''.map = \<tau>"
      using \<tau>.natural_transformation_axioms \<tau>''.natural_transformation_axioms   
      by (intro eqI, auto)
  qed

  locale inverse_transformations =
    A: category A +
    B: category B +
    F: "functor" A B F +
    G: "functor" A B G +
    \<tau>: natural_transformation A B F G \<tau> +
    \<tau>': natural_transformation A B G F \<tau>'
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'a \<Rightarrow> 'b"
  and \<tau> :: "'a \<Rightarrow> 'b"
  and \<tau>' :: "'a \<Rightarrow> 'b" +
  assumes inv: "A.ide a \<Longrightarrow> B.inverse_arrows (\<tau> a) (\<tau>' a)"

  sublocale inverse_transformations \<subseteq> natural_isomorphism A B F G \<tau>
    by (meson B.category_axioms \<tau>.natural_transformation_axioms B.iso_def inv
              natural_isomorphism.intro natural_isomorphism_axioms.intro)
  sublocale inverse_transformations \<subseteq> natural_isomorphism A B G F \<tau>'
    by (meson category.inverse_arrows_sym category.iso_def inverse_transformations_axioms
              inverse_transformations_axioms_def inverse_transformations_def
              natural_isomorphism.intro natural_isomorphism_axioms.intro)

  lemma inverse_transformations_sym:
  assumes "inverse_transformations A B F G \<sigma> \<sigma>'"
  shows "inverse_transformations A B G F \<sigma>' \<sigma>"
    using assms
    by (simp add: category.inverse_arrows_sym inverse_transformations_axioms_def
                  inverse_transformations_def)

  lemma inverse_transformations_inverse:
  assumes "inverse_transformations A B F G \<sigma> \<sigma>'"
  shows "vertical_composite.map A B \<sigma> \<sigma>' = F"
  and "vertical_composite.map A B \<sigma>' \<sigma> = G"
  proof -
    interpret A: category A
      using assms(1) inverse_transformations_def natural_transformation_def by blast
    interpret inv: inverse_transformations A B F G \<sigma> \<sigma>' using assms by auto
    interpret \<sigma>\<sigma>': vertical_composite A B F G F \<sigma> \<sigma>' ..
    show "vertical_composite.map A B \<sigma> \<sigma>' = F"
      using \<sigma>\<sigma>'.is_natural_transformation inv.F.natural_transformation_axioms
      apply (intro eqI, simp_all)
      by (auto simp add: \<sigma>\<sigma>'.map_simp_ide inv.B.comp_inv_arr inv.inv)
    interpret inv': inverse_transformations A B G F \<sigma>' \<sigma>
      using assms inverse_transformations_sym by blast
    interpret \<sigma>'\<sigma>: vertical_composite A B G F G \<sigma>' \<sigma> ..
    show "vertical_composite.map A B \<sigma>' \<sigma> = G"
      using \<sigma>'\<sigma>.is_natural_transformation inv.G.natural_transformation_axioms
      apply (intro eqI, simp_all)
      by (auto simp add: \<sigma>'\<sigma>.map_simp_ide inv'.inv inv.B.comp_inv_arr)
  qed

  lemma inverse_transformations_compose:
  assumes "inverse_transformations A B F G \<sigma> \<sigma>'"
  and "inverse_transformations A B G H \<tau> \<tau>'"
  shows "inverse_transformations A B F H (vertical_composite.map A B \<sigma> \<tau>)
                                         (vertical_composite.map A B \<tau>' \<sigma>')"
  proof -
    interpret A: category A using assms(1) inverse_transformations_def by blast
    interpret B: category B using assms(1) inverse_transformations_def by blast
    interpret \<sigma>\<sigma>': inverse_transformations A B F G \<sigma> \<sigma>' using assms(1) by auto
    interpret \<tau>\<tau>': inverse_transformations A B G H \<tau> \<tau>' using assms(2) by auto
    interpret \<sigma>\<tau>: vertical_composite A B F G H \<sigma> \<tau> ..
    interpret \<tau>'\<sigma>': vertical_composite A B H G F \<tau>' \<sigma>' ..
    show ?thesis
      using B.inverse_arrows_compose \<sigma>\<sigma>'.inv \<sigma>\<tau>.map_simp_ide \<tau>'\<sigma>'.map_simp_ide \<tau>\<tau>'.inv
      by (unfold_locales, auto)
  qed

  lemma vertical_composite_iso_inverse [simp]:
  assumes "natural_isomorphism A B F G \<tau>"
  shows "vertical_composite.map A B \<tau> (inverse_transformation.map A B G \<tau>) = F"
  proof -
    interpret \<tau>: natural_isomorphism A B F G \<tau> using assms by auto
    interpret \<tau>': inverse_transformation A B F G \<tau> ..
    interpret \<tau>\<tau>': vertical_composite A B F G F \<tau> \<tau>'.map ..
    show ?thesis
      using \<tau>\<tau>'.is_natural_transformation \<tau>.F.natural_transformation_axioms \<tau>'.inverts_components
      apply (intro eqI, simp_all)
      by (auto simp add: \<tau>.B.comp_inv_arr \<tau>\<tau>'.map_simp_ide)
  qed

  lemma vertical_composite_inverse_iso [simp]:
  assumes "natural_isomorphism A B F G \<tau>"
  shows "vertical_composite.map A B (inverse_transformation.map A B G \<tau>) \<tau> = G"
  proof -
    interpret \<tau>: natural_isomorphism A B F G \<tau> using assms by auto
    interpret \<tau>': inverse_transformation A B F G \<tau> ..
    interpret \<tau>'\<tau>: vertical_composite A B G F G \<tau>'.map \<tau> ..    
    show ?thesis
      using \<tau>'\<tau>.is_natural_transformation \<tau>.G.natural_transformation_axioms \<tau>'.inverts_components
            \<tau>'\<tau>.map_simp_ide
      apply (intro eqI, auto) by fastforce
  qed

  lemma natural_isomorphisms_compose:
  assumes "natural_isomorphism A B F G \<sigma>" and "natural_isomorphism A B G H \<tau>"
  shows "natural_isomorphism A B F H (vertical_composite.map A B \<sigma> \<tau>)"
  proof -
    interpret A: category A
      using assms(1) natural_isomorphism_def natural_transformation_def by blast
    interpret B: category B
      using assms(1) natural_isomorphism_def natural_transformation_def by blast
    interpret \<sigma>: natural_isomorphism A B F G \<sigma> using assms(1) by auto
    interpret \<tau>: natural_isomorphism A B G H \<tau> using assms(2) by auto
    interpret \<sigma>\<tau>: vertical_composite A B F G H \<sigma> \<tau> ..
    interpret natural_isomorphism A B F H \<sigma>\<tau>.map
      using \<sigma>\<tau>.map_simp_ide by (unfold_locales, auto)
    show ?thesis ..
  qed

  lemma naturally_isomorphic_reflexive:
  assumes "functor A B F"
  shows "naturally_isomorphic A B F F"
  proof -
    interpret F: "functor" A B F using assms by auto
    have "natural_isomorphism A B F F F" ..
    thus ?thesis using naturally_isomorphic_def by blast
  qed

  lemma naturally_isomorphic_symmetric:
  assumes "naturally_isomorphic A B F G"
  shows "naturally_isomorphic A B G F"
  proof -
    obtain \<phi> where \<phi>: "natural_isomorphism A B F G \<phi>"
      using assms naturally_isomorphic_def by blast
    interpret \<phi>: natural_isomorphism A B F G \<phi>
      using \<phi> by auto
    interpret \<psi>: inverse_transformation A B F G \<phi> ..
    have "natural_isomorphism A B G F \<psi>.map" ..
    thus ?thesis using naturally_isomorphic_def by blast
  qed

  lemma naturally_isomorphic_transitive:
  assumes "naturally_isomorphic A B F G"
  and "naturally_isomorphic A B G H"
  shows "naturally_isomorphic A B F H"
  proof -
    obtain \<phi> where \<phi>: "natural_isomorphism A B F G \<phi>"
      using assms naturally_isomorphic_def by blast
    interpret \<phi>: natural_isomorphism A B F G \<phi>
      using \<phi> by auto
    obtain \<psi> where \<psi>: "natural_isomorphism A B G H \<psi>"
      using assms naturally_isomorphic_def by blast
    interpret \<psi>: natural_isomorphism A B G H \<psi>
      using \<psi> by auto
    interpret \<psi>\<phi>: vertical_composite A B F G H \<phi> \<psi> ..
    have "natural_isomorphism A B F H \<psi>\<phi>.map"
      using \<phi> \<psi> natural_isomorphisms_compose by blast
    thus ?thesis
      using naturally_isomorphic_def by blast
  qed

  section "Horizontal Composition"

  text\<open>
    Horizontal composition is a way of composing parallel natural transformations
    @{term \<sigma>} from @{term F} to @{term G} and @{term \<tau>} from @{term H} to @{term K},
    where functors @{term F} and @{term G} map @{term A} to @{term B} and
    @{term H} and @{term K} map @{term B} to @{term C}, to obtain a natural transformation
    from @{term "H o F"} to @{term "K o G"}.
\<close>

  locale horizontal_composite =
    A: category A +
    B: category B +
    C: category C +
    F: "functor" A B F +
    G: "functor" A B G +
    H: "functor" B C H +
    K: "functor" B C K +
    \<sigma>: natural_transformation A B F G \<sigma> +
    \<tau>: natural_transformation B C H K \<tau>
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and C :: "'c comp"      (infixr "\<cdot>\<^sub>C" 55)
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'a \<Rightarrow> 'b"
  and H :: "'b \<Rightarrow> 'c"
  and K :: "'b \<Rightarrow> 'c"
  and \<sigma> :: "'a \<Rightarrow> 'b"
  and \<tau> :: "'b \<Rightarrow> 'c"
  begin

    no_notation C.in_hom ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    notation C.in_hom ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>") 

    abbreviation map
    where "map \<equiv> \<tau> o \<sigma>"

    lemma is_natural_transformation:
    shows "natural_transformation A C (H o F) (K o G) map"
    proof -
      interpret HF: composite_functor A B C F H ..
      interpret KG: composite_functor A B C G K ..
      show "natural_transformation A C (H o F) (K o G) (\<tau> o \<sigma>)"
        using \<sigma>.is_extensional \<tau>.is_extensional
        apply (unfold_locales, auto)
         apply (metis \<sigma>.is_natural_1 \<sigma>.preserves_reflects_arr \<tau>.preserves_comp_1)
        by (metis \<sigma>.is_natural_2 \<sigma>.preserves_reflects_arr \<tau>.preserves_comp_2)
    qed

  end

  sublocale horizontal_composite \<subseteq> natural_transformation A C "H o F" "K o G" "\<tau> o \<sigma>"
    using is_natural_transformation by auto

  context horizontal_composite
  begin

    interpretation KF: composite_functor A B C F K ..
    interpretation HG: composite_functor A B C G H ..
    interpretation \<tau>F: horizontal_composite A B C F F H K F \<tau> ..
    interpretation \<tau>G: horizontal_composite A B C G G H K G \<tau> ..
    interpretation H\<sigma>: horizontal_composite A B C F G H H \<sigma> H ..
    interpretation K\<sigma>: horizontal_composite A B C F G K K \<sigma> K ..
    interpretation K\<sigma>_\<tau>F: vertical_composite A C "H o F" "K o F" "K o G" "\<tau> o F" "K o \<sigma>" ..
    interpretation \<tau>G_H\<sigma>: vertical_composite A C "H o F" "H o G" "K o G" "H o \<sigma>" "\<tau> o G" ..

    lemma map_simp_1:
    assumes "A.arr f"
    shows "(\<tau> o \<sigma>) f = K\<sigma>_\<tau>F.map f"
      using assms
      by (metis K\<sigma>_\<tau>F.map_simp_1 \<sigma>.is_natural_2 \<sigma>.preserves_reflects_arr \<tau>.preserves_comp_1
                comp_apply)

    lemma map_simp_2:
    assumes "A.arr f"
    shows "(\<tau> o \<sigma>) f = \<tau>G_H\<sigma>.map f"
      using assms
      by (metis \<sigma>.is_natural_1 \<sigma>.preserves_reflects_arr \<tau>.preserves_comp_2 \<tau>G_H\<sigma>.map_simp_2
                comp_apply)

  end

  lemma hcomp_ide_dom [simp]:
  assumes "natural_transformation A B F G \<tau>"
  shows "\<tau> o (identity_functor.map A) = \<tau>"
  proof -
    interpret \<tau>: natural_transformation A B F G \<tau> using assms by auto
    show "\<tau> o \<tau>.A.map = \<tau>"
      using \<tau>.A.map_def \<tau>.is_extensional by fastforce
  qed

  lemma hcomp_ide_cod [simp]:
  assumes "natural_transformation A B F G \<tau>"
  shows "(identity_functor.map B) o \<tau> = \<tau>"
  proof -
    interpret \<tau>: natural_transformation A B F G \<tau> using assms by auto
    show "\<tau>.B.map o \<tau> = \<tau>"
      using \<tau>.B.map_def \<tau>.is_extensional by auto
  qed

  text\<open>
    Horizontal composition of a functor with a vertical composite.
\<close>

  lemma hcomp_functor_vcomp:
  assumes "functor A B F"
  and "natural_transformation B C H K \<tau>"
  and "natural_transformation B C K L \<tau>'"
  shows "(vertical_composite.map B C \<tau> \<tau>') o F = vertical_composite.map A C (\<tau> o F) (\<tau>' o F)"
  proof -
    interpret F: "functor" A B F using assms(1) by auto
    interpret \<tau>: natural_transformation B C H K \<tau> using assms(2) by auto
    interpret \<tau>': natural_transformation B C K L \<tau>' using assms(3) by auto
    interpret HF: composite_functor A B C F H ..
    interpret KF: composite_functor A B C F K ..
    interpret LF: composite_functor A B C F L ..
    interpret \<tau>F: horizontal_composite A B C F F H K F \<tau> ..
    interpret \<tau>'F: horizontal_composite A B C F F K L F \<tau>' ..
    interpret \<tau>'o\<tau>: vertical_composite B C H K L \<tau> \<tau>' ..
    interpret \<tau>'o\<tau>_F: horizontal_composite A B C F F H L F \<tau>'o\<tau>.map ..
    interpret \<tau>'Fo\<tau>F: vertical_composite A C "H o F" "K o F" "L o F" "\<tau> o F" "\<tau>' o F" ..
    show ?thesis
      using \<tau>'Fo\<tau>F.map_def \<tau>'o\<tau>.map_def \<tau>'o\<tau>_F.is_extensional by auto
  qed

  text\<open>
    Horizontal composition of a vertical composite with a functor.
\<close>

  lemma hcomp_vcomp_functor:
  assumes "functor B C K"
  and "natural_transformation A B F G \<tau>"
  and "natural_transformation A B G H \<tau>'"
  shows "K o (vertical_composite.map A B \<tau> \<tau>') = vertical_composite.map A C (K o \<tau>) (K o \<tau>')"
  proof -
    interpret K: "functor" B C K using assms(1) by auto
    interpret \<tau>: natural_transformation A B F G \<tau> using assms(2) by auto
    interpret \<tau>': natural_transformation A B G H \<tau>' using assms(3) by auto
    interpret KF: composite_functor A B C F K ..
    interpret KG: composite_functor A B C G K ..
    interpret KH: composite_functor A B C H K ..
    interpret \<tau>'o\<tau>: vertical_composite A B F G H \<tau> \<tau>' ..
    interpret K\<tau>: horizontal_composite A B C F G K K \<tau> K ..
    interpret K\<tau>': horizontal_composite A B C G H K K \<tau>' K ..
    interpret K_\<tau>'o\<tau>: horizontal_composite A B C F H K K \<tau>'o\<tau>.map K ..
    interpret K\<tau>'oK\<tau>: vertical_composite A C "K o F" "K o G" "K o H" "K o \<tau>" "K o \<tau>'" ..
    show "K o \<tau>'o\<tau>.map = K\<tau>'oK\<tau>.map"
      using K\<tau>'oK\<tau>.map_def \<tau>'o\<tau>.map_def K_\<tau>'o\<tau>.is_extensional K\<tau>'oK\<tau>.map_simp_1 \<tau>'o\<tau>.map_simp_1
      by auto
  qed

  text\<open>
    The interchange law for horizontal and vertical composition.
\<close>

  lemma interchange:
  assumes "natural_transformation B C F G \<sigma>"
  and "natural_transformation C D H K \<tau>"
  shows "horizontal_composite.map \<sigma> \<tau> = vertical_composite.map B D (H o \<sigma>) (\<tau> o G)"
  and "horizontal_composite.map \<sigma> \<tau> = vertical_composite.map B D (\<tau> o F) (K o \<sigma>)"
  proof -
    interpret \<sigma>: natural_transformation B C F G \<sigma>
       using assms(1) by auto
    interpret \<tau>: natural_transformation C D H K \<tau>
       using assms(2) by auto
    interpret \<tau>\<sigma>: horizontal_composite B C D F G H K \<sigma> \<tau> ..
    interpret H\<sigma>: horizontal_composite B C D F G H H \<sigma> H ..
    interpret K\<sigma>: horizontal_composite B C D F G K K \<sigma> K ..
    interpret \<tau>G: horizontal_composite B C D G G H K G \<tau> ..
    interpret \<tau>F: horizontal_composite B C D F F H K F \<tau> ..
    interpret \<tau>GoH\<sigma>: vertical_composite B D "H o F" "H o G" "K o G" "H o \<sigma>" "\<tau> o G" ..
    interpret K\<sigma>o\<tau>F: vertical_composite B D "H o F" "K o F" "K o G" "\<tau> o F" "K o \<sigma>" ..
    show "\<tau>\<sigma>.map = \<tau>GoH\<sigma>.map"
      using \<tau>\<sigma>.map_simp_2 \<tau>\<sigma>.natural_transformation_axioms \<tau>GoH\<sigma>.natural_transformation_axioms
      by (intro eqI, auto)
    show "\<tau>\<sigma>.map = K\<sigma>o\<tau>F.map"
      using \<tau>\<sigma>.map_simp_1 \<tau>\<sigma>.natural_transformation_axioms K\<sigma>o\<tau>F.natural_transformation_axioms
      by (intro eqI, auto)
  qed

end


