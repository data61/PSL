(*  Title:       EquivalenceOfCategories
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2017
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Equivalence of Categories"

text \<open>
  In this chapter we define the notions of equivalence and adjoint equivalence of categories
  and establish some properties of functors that are part of an equivalence.
\<close>

theory EquivalenceOfCategories
imports Adjunction
begin
  locale equivalence_of_categories =
    C: category C +
    D: category D +
    F: "functor" D C F +
    G: "functor" C D G +
    \<eta>: natural_isomorphism D D D.map "G o F" \<eta> +
    \<epsilon>: natural_isomorphism C C "F o G" C.map \<epsilon>
  for C :: "'c comp"     (infixr "\<cdot>\<^sub>C" 55)
  and D :: "'d comp"     (infixr "\<cdot>\<^sub>D" 55)
  and F :: "'d \<Rightarrow> 'c"
  and G :: "'c \<Rightarrow> 'd"
  and \<eta> :: "'d \<Rightarrow> 'd"
  and \<epsilon> :: "'c \<Rightarrow> 'c"
  begin

    notation C.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")
    notation D.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>")

    lemma C_arr_expansion:
    assumes "C.arr f"
    shows "\<epsilon> (C.cod f) \<cdot>\<^sub>C F (G f) \<cdot>\<^sub>C C.inv (\<epsilon> (C.dom f)) = f"
    and "C.inv (\<epsilon> (C.cod f)) \<cdot>\<^sub>C f \<cdot>\<^sub>C \<epsilon> (C.dom f) = F (G f)"
    proof -
      have \<epsilon>_dom: "C.inverse_arrows (\<epsilon> (C.dom f)) (C.inv (\<epsilon> (C.dom f)))"
        using assms C.inv_is_inverse by auto
      have \<epsilon>_cod: "C.inverse_arrows (\<epsilon> (C.cod f)) (C.inv (\<epsilon> (C.cod f)))"
        using assms C.inv_is_inverse by auto
      have "\<epsilon> (C.cod f) \<cdot>\<^sub>C F (G f) \<cdot>\<^sub>C C.inv (\<epsilon> (C.dom f)) =
            (\<epsilon> (C.cod f) \<cdot>\<^sub>C F (G f)) \<cdot>\<^sub>C C.inv (\<epsilon> (C.dom f))"
        using C.comp_assoc by force
      also have 1: "... = (f \<cdot>\<^sub>C \<epsilon> (C.dom f)) \<cdot>\<^sub>C C.inv (\<epsilon> (C.dom f))"
        using assms \<epsilon>.naturality by simp
      also have 2: "... = f"
        using assms \<epsilon>_dom C.comp_arr_inv C.comp_arr_dom C.comp_assoc by force
      finally show "\<epsilon> (C.cod f) \<cdot>\<^sub>C F (G f) \<cdot>\<^sub>C C.inv (\<epsilon> (C.dom f)) = f" by blast
      show "C.inv (\<epsilon> (C.cod f)) \<cdot>\<^sub>C f \<cdot>\<^sub>C \<epsilon> (C.dom f) = F (G f)"
        using assms 1 2 \<epsilon>_dom \<epsilon>_cod C.invert_side_of_triangle C.isoI C.iso_inv_iso
        by metis
    qed

    lemma G_is_faithful:
    shows "faithful_functor C D G"
    proof
      fix f f'
      assume par: "C.par f f'" and eq: "G f = G f'"
      show "f = f'"
      proof -
        have "C.inv (\<epsilon> (C.cod f)) \<in> C.hom (C.cod f) (F (G (C.cod f))) \<and>
              C.iso (C.inv (\<epsilon> (C.cod f)))"
          using par C.iso_inv_iso by auto
        moreover have 1: "\<epsilon> (C.dom f) \<in> C.hom (F (G (C.dom f))) (C.dom f) \<and>
                          C.iso (\<epsilon> (C.dom f))"
          using par by auto
        ultimately have 2: "f \<cdot>\<^sub>C \<epsilon> (C.dom f) = f' \<cdot>\<^sub>C \<epsilon> (C.dom f)"
          using par C_arr_expansion eq C.iso_is_section C.section_is_mono
          by (metis C_arr_expansion(1) eq)
        show ?thesis
        proof -
          have "C.epi (\<epsilon> (C.dom f))"
            using 1 par C.iso_is_retraction C.retraction_is_epi by blast
          thus ?thesis using 2 par by auto
        qed
      qed
    qed

    lemma G_is_essentially_surjective:
    shows "essentially_surjective_functor C D G"
    proof
      fix b
      assume b: "D.ide b"
      have "C.ide (F b) \<and> D.isomorphic (G (F b)) b"
      proof
        show "C.ide (F b)" using b by simp
        show "D.isomorphic (G (F b)) b"
        proof (unfold D.isomorphic_def)
          have "\<guillemotleft>D.inv (\<eta> b) : G (F b) \<rightarrow>\<^sub>D b\<guillemotright> \<and> D.iso (D.inv (\<eta> b))"
            using b D.iso_inv_iso by auto
          thus "\<exists>f. \<guillemotleft>f : G (F b) \<rightarrow>\<^sub>D b\<guillemotright> \<and> D.iso f" by blast
        qed
      qed
      thus "\<exists>a. C.ide a \<and> D.isomorphic (G a) b"
        by blast
    qed

    interpretation \<epsilon>_inv: inverse_transformation C C "F o G" C.map \<epsilon> ..
    interpretation \<eta>_inv: inverse_transformation D D D.map "G o F" \<eta> ..
    interpretation GF: equivalence_of_categories D C G F \<epsilon>_inv.map \<eta>_inv.map ..

    lemma F_is_faithful:
    shows "faithful_functor D C F"
      using GF.G_is_faithful by simp

    lemma F_is_essentially_surjective:
    shows "essentially_surjective_functor D C F"
      using GF.G_is_essentially_surjective by simp

    lemma G_is_full:
    shows "full_functor C D G"
    proof
      fix a a' g
      assume a: "C.ide a" and a': "C.ide a'"
      assume g: "\<guillemotleft>g : G a \<rightarrow>\<^sub>D G a'\<guillemotright>"
      show "\<exists>f. \<guillemotleft>f : a \<rightarrow>\<^sub>C a'\<guillemotright> \<and> G f = g"
      proof
        have \<epsilon>a: "C.inverse_arrows (\<epsilon> a) (C.inv (\<epsilon> a))"
          using a C.inv_is_inverse by auto
        have \<epsilon>a': "C.inverse_arrows (\<epsilon> a') (C.inv (\<epsilon> a'))"
          using a' C.inv_is_inverse by auto
        let ?f = "\<epsilon> a' \<cdot>\<^sub>C F g \<cdot>\<^sub>C C.inv (\<epsilon> a)"
        have f: "\<guillemotleft>?f : a \<rightarrow>\<^sub>C a'\<guillemotright>"
          using a a' g \<epsilon>a \<epsilon>a' \<epsilon>.preserves_hom [of a' a' a'] \<epsilon>_inv.preserves_hom [of a a a]
          by fastforce
        moreover have "G ?f = g"
        proof -
          interpret F: faithful_functor D C F
            using F_is_faithful by auto
          have "F (G ?f) = F g"
          proof -
            have "F (G ?f) = C.inv (\<epsilon> a') \<cdot>\<^sub>C ?f \<cdot>\<^sub>C \<epsilon> a"
              using f C_arr_expansion(2) [of "?f"] by auto
            also have "... = (C.inv (\<epsilon> a') \<cdot>\<^sub>C \<epsilon> a') \<cdot>\<^sub>C F g \<cdot>\<^sub>C C.inv (\<epsilon> a) \<cdot>\<^sub>C \<epsilon> a"
              using a a' f g C.comp_assoc by fastforce
            also have "... = F g"
              using a a' g \<epsilon>a \<epsilon>a' C.comp_inv_arr C.comp_arr_dom C.comp_cod_arr by auto
            finally show ?thesis by blast
          qed
          moreover have "D.par (G (\<epsilon> a' \<cdot>\<^sub>C F g \<cdot>\<^sub>C C.inv (\<epsilon> a))) g"
            using f g by fastforce
          ultimately show ?thesis using f g F.is_faithful by blast
        qed
        ultimately show "\<guillemotleft>?f : a \<rightarrow>\<^sub>C a'\<guillemotright> \<and> G ?f = g" by blast
      qed
    qed

  end

  (* I'm not sure why I had to close and re-open the context here in order to
   * get the G_is_full fact in the interpretation GF. *)

  context equivalence_of_categories
  begin

    interpretation \<epsilon>_inv: inverse_transformation C C "F o G" C.map \<epsilon> ..
    interpretation \<eta>_inv: inverse_transformation D D D.map "G o F" \<eta> ..
    interpretation GF: equivalence_of_categories D C G F \<epsilon>_inv.map \<eta>_inv.map ..

    lemma F_is_full:
    shows "full_functor D C F"
      using GF.G_is_full by simp

  end

  text \<open>
    Traditionally the term "equivalence of categories" is also used for a functor
    that is part of an equivalence of categories.  However, it seems best to use
    that term for a situation in which all of the structure of an equivalence is
    explicitly given, and to have a different term for one of the functors involved.
\<close>

  locale equivalence_functor =
    C: category C +
    D: category D +
    "functor" C D G
  for C :: "'c comp"     (infixr "\<cdot>\<^sub>C" 55)
  and D :: "'d comp"     (infixr "\<cdot>\<^sub>D" 55)
  and G :: "'c \<Rightarrow> 'd" +
  assumes induces_equivalence: "\<exists>F \<eta> \<epsilon>. equivalence_of_categories C D F G \<eta> \<epsilon>"
  begin

    notation C.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")
    notation D.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>")

  end

  sublocale equivalence_of_categories \<subseteq> equivalence_functor C D G
    using equivalence_of_categories_axioms by (unfold_locales, blast)

  text \<open>
    An equivalence functor is fully faithful and essentially surjective.
\<close>

  sublocale equivalence_functor \<subseteq> fully_faithful_functor C D G
  proof -
    obtain F \<eta> \<epsilon> where 1: "equivalence_of_categories C D F G \<eta> \<epsilon>"
      using induces_equivalence by blast
    interpret equivalence_of_categories C D F G \<eta> \<epsilon>
      using 1 by auto
    show "fully_faithful_functor C D G"
      using G_is_full G_is_faithful fully_faithful_functor.intro by auto
  qed

  sublocale equivalence_functor \<subseteq> essentially_surjective_functor C D G
  proof -
    obtain F \<eta> \<epsilon> where 1: "equivalence_of_categories C D F G \<eta> \<epsilon>"
      using induces_equivalence by blast
    interpret equivalence_of_categories C D F G \<eta> \<epsilon>
      using 1 by auto
    show "essentially_surjective_functor C D G"
      using G_is_essentially_surjective by auto
  qed

  text \<open>
    A special case of an equivalence functor is an endofunctor \<open>F\<close> equipped with
    a natural isomorphism from \<open>F\<close> to the identity functor.
\<close>

  context endofunctor
  begin

    lemma isomorphic_to_identity_is_equivalence:
    assumes "natural_isomorphism A A F A.map \<phi>"
    shows "equivalence_functor A A F"
    proof -
      interpret \<phi>: natural_isomorphism A A F A.map \<phi>
         using assms by auto
      interpret \<phi>': inverse_transformation A A F A.map \<phi> ..
      interpret F\<phi>': natural_isomorphism A A F "F o F" "F o \<phi>'.map"
      proof -
        interpret \<tau>: horizontal_composite A A A A.map F F F \<phi>'.map F ..
        interpret F\<phi>': natural_transformation A A F "F o F" "F o \<phi>'.map"
          using comp_identity_functor functor_axioms \<tau>.natural_transformation_axioms by simp
        show "natural_isomorphism A A F (F o F) (F o \<phi>'.map)"
          apply unfold_locales
          using \<phi>'.components_are_iso by fastforce
      qed
      interpret F\<phi>'o\<phi>': vertical_composite A A A.map F "F o F" \<phi>'.map "F o \<phi>'.map" ..
      interpret F\<phi>'o\<phi>': natural_isomorphism A A A.map "F o F" F\<phi>'o\<phi>'.map
        using \<phi>'.natural_isomorphism_axioms F\<phi>'.natural_isomorphism_axioms
              natural_isomorphisms_compose
        by fast
      interpret inv_F\<phi>'o\<phi>': inverse_transformation A A A.map "F o F" F\<phi>'o\<phi>'.map ..
      interpret F: equivalence_of_categories A A F F F\<phi>'o\<phi>'.map inv_F\<phi>'o\<phi>'.map ..
      show ?thesis ..
    qed

  end

  text \<open>
    An adjoint equivalence is an equivalence of categories that is also an adjunction.
\<close>

  locale adjoint_equivalence =
    unit_counit_adjunction C D F G \<eta> \<epsilon> +
    \<eta>: natural_isomorphism D D D.map "G o F" \<eta> +
    \<epsilon>: natural_isomorphism C C "F o G" C.map \<epsilon>
  for C :: "'c comp"     (infixr "\<cdot>\<^sub>C" 55)
  and D :: "'d comp"     (infixr "\<cdot>\<^sub>D" 55)
  and F :: "'d \<Rightarrow> 'c"
  and G :: "'c \<Rightarrow> 'd"
  and \<eta> :: "'d \<Rightarrow> 'd"
  and \<epsilon> :: "'c \<Rightarrow> 'c"

  text \<open>
    An adjoint equivalence is clearly an equivalence of categories.
\<close>

  sublocale adjoint_equivalence \<subseteq> equivalence_of_categories ..

  context adjoint_equivalence
  begin

    text \<open>
      The triangle identities for an adjunction reduce to inverse relations when
      \<open>\<eta>\<close> and \<open>\<epsilon>\<close> are natural isomorphisms.
\<close>

    lemma triangle_G':
    assumes "C.ide a"
    shows "D.inverse_arrows (\<eta> (G a)) (G (\<epsilon> a))"
    proof
      show "D.ide (G (\<epsilon> a) \<cdot>\<^sub>D \<eta> (G a))"
        using assms triangle_G G\<epsilon>o\<eta>G.map_simp_ide by fastforce
      thus "D.ide (\<eta> (G a) \<cdot>\<^sub>D G (\<epsilon> a))"
        using assms D.section_retraction_of_iso [of "G (\<epsilon> a)" "\<eta> (G a)"] by auto
    qed

    lemma triangle_F':
    assumes "D.ide b"
    shows "C.inverse_arrows (F (\<eta> b)) (\<epsilon> (F b))"
    proof
     show "C.ide (\<epsilon> (F b) \<cdot>\<^sub>C F (\<eta> b))"
        using assms triangle_F \<epsilon>FoF\<eta>.map_simp_ide by auto
      thus "C.ide (F (\<eta> b) \<cdot>\<^sub>C \<epsilon> (F b))"
        using assms C.section_retraction_of_iso [of "\<epsilon> (F b)" "F (\<eta> b)"] by auto
    qed

    text \<open>
      An adjoint equivalence can be dualized by interchanging the two functors and inverting
      the natural isomorphisms.  This is somewhat awkward to prove, but probably useful to have
      done it once and for all.
\<close>

    lemma dual_equivalence:
    assumes "adjoint_equivalence C D F G \<eta> \<epsilon>"
    shows "adjoint_equivalence D C G F (inverse_transformation.map C C (C.map) \<epsilon>)
                                       (inverse_transformation.map D D (G o F) \<eta>)"
    proof -
      interpret adjoint_equivalence C D F G \<eta> \<epsilon> using assms by auto
      interpret \<epsilon>': inverse_transformation C C "F o G" C.map \<epsilon> ..
      interpret \<eta>': inverse_transformation D D D.map "G o F" \<eta> ..
      have 1: "G o (F o G) = (G o F) o G \<and> F o (G o F) = (F o G) o F" by auto
      interpret G\<epsilon>': natural_transformation C D G "(G o F) o G" "G o \<epsilon>'.map"
      proof -
        interpret G\<epsilon>': horizontal_composite C C D C.map "F o G" G G \<epsilon>'.map G ..
        show "natural_transformation C D G ((G o F) o G) (G o \<epsilon>'.map)"
          using 1 G\<epsilon>'.natural_transformation_axioms G.natural_transformation_axioms by auto
      qed
      interpret \<eta>'G: natural_transformation C D "(G o F) o G" G "\<eta>'.map o G"
      proof -
        interpret \<eta>'G: horizontal_composite C D D G G "G o F" D.map G \<eta>'.map ..
        show "natural_transformation C D ((G o F) o G) G (\<eta>'.map o G)"
          using 1 \<eta>'G.natural_transformation_axioms G.natural_transformation_axioms by auto
      qed
      interpret \<epsilon>'F: natural_transformation D C F "((F o G) o F)" "\<epsilon>'.map o F"
      proof -
        interpret \<epsilon>'F: horizontal_composite D C C F F C.map "F o G" F \<epsilon>'.map ..
        show "natural_transformation D C F ((F o G) o F) (\<epsilon>'.map o F)"
          using 1 \<epsilon>'F.natural_transformation_axioms F.natural_transformation_axioms by auto
      qed
      interpret F\<eta>': natural_transformation D C "(F o G) o F" F "F o \<eta>'.map"
      proof -
        interpret F\<eta>': horizontal_composite D D C "G o F" D.map F F \<eta>'.map F ..
        show "natural_transformation D C ((F o G) o F) F (F o \<eta>'.map)"
          using 1 F\<eta>'.natural_transformation_axioms F.natural_transformation_axioms by auto
      qed
      interpret F\<eta>'o\<epsilon>'F: vertical_composite D C F "(F o G) o F" F "\<epsilon>'.map o F" "F o \<eta>'.map" ..
      interpret \<eta>'GoG\<epsilon>': vertical_composite C D G "G o F o G" G "G o \<epsilon>'.map" "\<eta>'.map o G" ..
      show ?thesis
      proof
        show "\<eta>'GoG\<epsilon>'.map = G"
        proof (intro NaturalTransformation.eqI)
          show "natural_transformation C D G G G"
            using G.natural_transformation_axioms by auto
          show "natural_transformation C D G G \<eta>'GoG\<epsilon>'.map"
            using \<eta>'GoG\<epsilon>'.natural_transformation_axioms by auto
          show "\<And>a. C.ide a \<Longrightarrow> \<eta>'GoG\<epsilon>'.map a = G a"
          proof -
            fix a
            assume a: "C.ide a"
            show "\<eta>'GoG\<epsilon>'.map a = G a"
              using a \<eta>'GoG\<epsilon>'.map_simp_ide triangle_G'
                    \<eta>.components_are_iso \<epsilon>.components_are_iso G.preserves_ide
                    \<eta>'.inverts_components \<epsilon>'.inverts_components
                    D.inverse_unique G.preserves_inverse_arrows G\<epsilon>o\<eta>G.map_simp_ide
                    D.inverse_arrows_sym triangle_G
              by (metis o_apply)
          qed
        qed
        show "F\<eta>'o\<epsilon>'F.map = F"
        proof (intro NaturalTransformation.eqI)
          show "natural_transformation D C F F F"
            using F.natural_transformation_axioms by auto
          show "natural_transformation D C F F F\<eta>'o\<epsilon>'F.map"
            using F\<eta>'o\<epsilon>'F.natural_transformation_axioms by auto
          show "\<And>b. D.ide b \<Longrightarrow> F\<eta>'o\<epsilon>'F.map b = F b"
          proof -
            fix b
            assume b: "D.ide b"
            show "F\<eta>'o\<epsilon>'F.map b = F b"
              using b F\<eta>'o\<epsilon>'F.map_simp_ide \<epsilon>FoF\<eta>.map_simp_ide triangle_F triangle_F'
                    \<eta>.components_are_iso \<epsilon>.components_are_iso G.preserves_ide
                    \<eta>'.inverts_components \<epsilon>'.inverts_components F.preserves_ide
                    C.inverse_unique F.preserves_inverse_arrows C.inverse_arrows_sym
              by (metis o_apply)
          qed
        qed
      qed
    qed

  end

  text \<open>
    Every fully faithful and essentially surjective functor underlies an adjoint equivalence.
    To prove this without repeating things that were already proved in @{theory Category3.Adjunction},
    we first show that a fully faithful and essentially surjective functor is a left adjoint
    functor, and then we show that if the left adjoint in a unit-counit adjunction is
    fully faithful and essentially surjective, then the unit and counit are natural isomorphisms;
    hence the adjunction is in fact an adjoint equivalence.
\<close>

  locale fully_faithful_and_essentially_surjective_functor =
    C: category C +
    D: category D +
    fully_faithful_functor D C F +
    essentially_surjective_functor D C F
    for C :: "'c comp"     (infixr "\<cdot>\<^sub>C" 55)
    and D :: "'d comp"     (infixr "\<cdot>\<^sub>D" 55)
    and F :: "'d \<Rightarrow> 'c"
  begin

    notation C.in_hom      ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")
    notation D.in_hom      ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>")

    lemma is_left_adjoint_functor:
    shows "left_adjoint_functor D C F"
    proof
      fix y
      assume y: "C.ide y"
      let ?x = "SOME x. D.ide x \<and> (\<exists>e. C.iso e \<and> \<guillemotleft>e : F x \<rightarrow>\<^sub>C y\<guillemotright>)"
      let ?e = "SOME e. C.iso e \<and> \<guillemotleft>e : F ?x \<rightarrow>\<^sub>C y\<guillemotright>"
      have "\<exists>x e. C.iso e \<and> terminal_arrow_from_functor D C F x y e"
      proof -
        have "\<exists>x. C.iso ?e \<and> terminal_arrow_from_functor D C F x y ?e"
        proof -
          have x: "D.ide ?x \<and> (\<exists>e. C.iso e \<and> \<guillemotleft>e : F ?x \<rightarrow>\<^sub>C y\<guillemotright>)"
          proof -
            obtain x where x: "D.ide x \<and> C.isomorphic (F x) y"
              using y essentially_surjective D.isomorphic_def by blast
            obtain e where e: "C.iso e \<and> \<guillemotleft>e : F x \<rightarrow>\<^sub>C y\<guillemotright>"
              using y x by auto
            hence "\<exists>x. D.ide x \<and> (\<exists>e. C.iso e \<and> \<guillemotleft>e : F x \<rightarrow>\<^sub>C y\<guillemotright>)"
              using x by auto
            thus "D.ide ?x \<and> (\<exists>e. C.iso e \<and> \<guillemotleft>e : F ?x \<rightarrow>\<^sub>C y\<guillemotright>)"
              using someI_ex [of "\<lambda>x. D.ide x \<and> (\<exists>e. C.iso e \<and> \<guillemotleft>e : F x \<rightarrow>\<^sub>C y\<guillemotright>)"] by blast
          qed
          hence e: "C.iso ?e \<and> \<guillemotleft>?e : F ?x \<rightarrow>\<^sub>C y\<guillemotright>"
            using someI_ex [of "\<lambda>e. C.iso e \<and> \<guillemotleft>e : F ?x \<rightarrow>\<^sub>C y\<guillemotright>"] by blast
          interpret arrow_from_functor D C F ?x y ?e
            using x e by (unfold_locales, simp)
          interpret terminal_arrow_from_functor D C F ?x y ?e
          proof
            fix x' f
            assume 1: "arrow_from_functor D C F x' y f"
            interpret f: arrow_from_functor D C F x' y f
              using 1 by simp
            have f: "\<guillemotleft>f: F x' \<rightarrow>\<^sub>C y\<guillemotright>"
              by (meson f.arrow)
            show "\<exists>!g. is_coext x' f g"
            proof
              let ?g = "SOME g. \<guillemotleft>g : x' \<rightarrow>\<^sub>D ?x\<guillemotright> \<and> F g = C.inv ?e \<cdot>\<^sub>C f"
              have g: "\<guillemotleft>?g : x' \<rightarrow>\<^sub>D ?x\<guillemotright> \<and> F ?g = C.inv ?e \<cdot>\<^sub>C f"
              proof -
                have "\<exists>g. \<guillemotleft>g : x' \<rightarrow>\<^sub>D ?x\<guillemotright> \<and> F g = C.inv ?e \<cdot>\<^sub>C f"
                  using f e x f.arrow
                  by (meson C.comp_in_homI C.inv_in_hom is_full)
                thus ?thesis
                  using someI_ex [of "\<lambda>g. \<guillemotleft>g : x' \<rightarrow>\<^sub>D ?x\<guillemotright> \<and> F g = C.inv ?e \<cdot>\<^sub>C f"] by blast
              qed
              show 1: "is_coext x' f ?g"
              proof -
                have "\<guillemotleft>?g : x' \<rightarrow>\<^sub>D ?x\<guillemotright>"
                  using g by simp
                moreover have "?e \<cdot>\<^sub>C F ?g = f"
                proof -
                  have "?e \<cdot>\<^sub>C F ?g = ?e \<cdot>\<^sub>C C.inv ?e \<cdot>\<^sub>C f"
                    using g by simp
                  also have "... = (?e \<cdot>\<^sub>C C.inv ?e) \<cdot>\<^sub>C f"
                    using e f C.inv_in_hom by (metis C.comp_assoc)
                  also have "... = f"
                  proof -
                    have "?e \<cdot>\<^sub>C C.inv ?e = y"
                      using e C.comp_arr_inv [of ?e] C.inv_is_inverse by auto
                    thus ?thesis
                      using f C.comp_cod_arr by auto
                  qed
                  finally show ?thesis by blast
                qed
                ultimately show ?thesis
                  unfolding is_coext_def by simp
              qed
              show "\<And>g'. is_coext x' f g' \<Longrightarrow> g' = ?g"
              proof -
                fix g'
                assume g': "is_coext x' f g'"
                have 2: "\<guillemotleft>g' : x' \<rightarrow>\<^sub>D ?x\<guillemotright> \<and> ?e \<cdot>\<^sub>C F g' = f" using g' is_coext_def by simp
                have 3: "\<guillemotleft>?g : x' \<rightarrow>\<^sub>D ?x\<guillemotright> \<and> ?e \<cdot>\<^sub>C F ?g = f" using 1 is_coext_def by simp
                have "F g' = F ?g"
                  using e 2 3 C.iso_is_section C.section_is_mono C.monoE by blast
                moreover have "D.par g' ?g"
                  using 2 3 by fastforce
                ultimately show "g' = ?g"
                  using is_faithful [of g' ?g] by simp
              qed
            qed
          qed
          show ?thesis
            using e terminal_arrow_from_functor_axioms by auto
        qed
        thus ?thesis by auto
      qed
      thus "\<exists>x e. terminal_arrow_from_functor D C F x y e" by blast
    qed

    lemma is_equivalence_functor:
    shows "equivalence_functor D C F"
    proof
      interpret left_adjoint_functor D C F
        using is_left_adjoint_functor by blast
      interpret equivalence_of_categories C D F G \<eta> \<epsilon>
      proof
        show 1: "\<And>a. C.ide a \<Longrightarrow> C.iso (\<epsilon> a)"
        proof -
          fix a
          assume a: "C.ide a"
          interpret \<epsilon>a: terminal_arrow_from_functor D C F "G a" a "\<epsilon> a"
            using a \<phi>\<psi>.has_terminal_arrows_from_functor [of a] by blast
          have "C.retraction (\<epsilon> a)"
          proof -
            obtain b \<phi> where \<phi>: "D.ide b \<and> C.iso \<phi> \<and> \<guillemotleft>\<phi>: F b \<rightarrow>\<^sub>C a\<guillemotright>"
              using a essentially_surjective by blast
            interpret \<phi>: arrow_from_functor D C F b a \<phi>
              using \<phi> by (unfold_locales, simp)
            let ?g = "\<epsilon>a.the_coext b \<phi>"
            have 1: "\<guillemotleft>?g : b \<rightarrow>\<^sub>D G a\<guillemotright> \<and> \<epsilon> a \<cdot>\<^sub>C F ?g = \<phi>"
              using \<phi>.arrow_from_functor_axioms \<epsilon>a.the_coext_prop [of b \<phi>] by simp
            have "a = (\<epsilon> a \<cdot>\<^sub>C F ?g) \<cdot>\<^sub>C C.inv \<phi>"
              using a 1 \<phi> C.comp_cod_arr \<epsilon>.preserves_hom [of a a a]
                    C.invert_side_of_triangle(2) [of "\<epsilon> a \<cdot>\<^sub>C F ?g" a \<phi>]
               by auto
            also have "... = \<epsilon> a \<cdot>\<^sub>C F ?g \<cdot>\<^sub>C C.inv \<phi>"
            proof -
              have "C.seq (\<epsilon> a) (F ?g)"
                using a 1 \<epsilon>.preserves_hom [of a a a] by fastforce
              moreover have "C.seq (F ?g) (C.inv \<phi>)"
                using a 1 \<phi> C.inv_in_hom [of \<phi> "F b" a] by blast
              ultimately show ?thesis using C.comp_assoc by auto
            qed
            finally have "\<exists>f. C.ide (\<epsilon> a \<cdot>\<^sub>C f)"
              using a by metis
            thus ?thesis
              unfolding C.retraction_def by blast
          qed
          moreover have "C.mono (\<epsilon> a)"
          proof
            show "C.arr (\<epsilon> a)"
              using a by simp
            show "\<And>f f'. C.seq (\<epsilon> a) f \<and> C.seq (\<epsilon> a) f' \<and> \<epsilon> a \<cdot>\<^sub>C f = \<epsilon> a \<cdot>\<^sub>C f' \<Longrightarrow> f = f'"
            proof -
              fix f f'
              assume ff': "C.seq (\<epsilon> a) f \<and> C.seq (\<epsilon> a) f' \<and> \<epsilon> a \<cdot>\<^sub>C f = \<epsilon> a \<cdot>\<^sub>C f'"
              have f: "\<guillemotleft>f : C.dom f \<rightarrow>\<^sub>C F (G a)\<guillemotright>"
                using a ff' \<epsilon>.preserves_hom [of a a a] by fastforce
              have f': "\<guillemotleft>f' : C.dom f' \<rightarrow>\<^sub>C F (G a)\<guillemotright>"
                using a ff' \<epsilon>.preserves_hom [of a a a] by fastforce
              have par: "C.par f f'"
                using f f' ff' C.dom_comp [of "\<epsilon> a" f] by force
              obtain b' \<phi> where \<phi>: "D.ide b' \<and> C.iso \<phi> \<and> \<guillemotleft>\<phi>: F b' \<rightarrow>\<^sub>C C.dom f\<guillemotright>"
                using par essentially_surjective C.ide_dom [of f] by blast
              have 1: "\<epsilon> a \<cdot>\<^sub>C f \<cdot>\<^sub>C \<phi> = \<epsilon> a \<cdot>\<^sub>C f' \<cdot>\<^sub>C \<phi>"
              proof -
                have "\<epsilon> a \<cdot>\<^sub>C f \<cdot>\<^sub>C \<phi> = (\<epsilon> a \<cdot>\<^sub>C f) \<cdot>\<^sub>C \<phi>"
                proof -
                  have "C.seq f \<phi>" using par \<phi> by auto
                  moreover have "C.seq (\<epsilon> a) f" using ff' by blast
                  ultimately show ?thesis using C.comp_assoc by auto
                qed
                also have "... = (\<epsilon> a \<cdot>\<^sub>C f') \<cdot>\<^sub>C \<phi>"
                  using ff' by argo
                also have "... = \<epsilon> a \<cdot>\<^sub>C f' \<cdot>\<^sub>C \<phi>"
                proof -
                  have "C.seq f' \<phi>" using par \<phi> by auto
                  moreover have "C.seq (\<epsilon> a) f'" using ff' by blast
                  ultimately show ?thesis using C.comp_assoc by auto
                qed
                finally show ?thesis by blast
              qed
              obtain g where g: "\<guillemotleft>g : b' \<rightarrow>\<^sub>D G a\<guillemotright> \<and> F g = f \<cdot>\<^sub>C \<phi>"
                using a f \<phi> is_full [of "G a" b' "f \<cdot>\<^sub>C \<phi>"] by auto
              obtain g' where g': "\<guillemotleft>g' : b' \<rightarrow>\<^sub>D G a\<guillemotright> \<and> F g' = f' \<cdot>\<^sub>C \<phi>"
                using a f' par \<phi> is_full [of "G a" b' "f' \<cdot>\<^sub>C \<phi>"] by auto
              interpret f\<phi>: arrow_from_functor D C F b' a "\<epsilon> a \<cdot>\<^sub>C f \<cdot>\<^sub>C \<phi>"
                using a \<phi> f \<epsilon>.preserves_hom [of a a a]
                by (unfold_locales, fastforce)
              interpret f'\<phi>: arrow_from_functor D C F b' a "\<epsilon> a \<cdot>\<^sub>C f' \<cdot>\<^sub>C \<phi>"
                using a \<phi> f' par \<epsilon>.preserves_hom [of a a a]
                by (unfold_locales, fastforce)
              have "\<epsilon>a.is_coext b' (\<epsilon> a \<cdot>\<^sub>C f \<cdot>\<^sub>C \<phi>) g"
                unfolding \<epsilon>a.is_coext_def using g 1 by auto
              moreover have "\<epsilon>a.is_coext b' (\<epsilon> a \<cdot>\<^sub>C f' \<cdot>\<^sub>C \<phi>) g'"
                unfolding \<epsilon>a.is_coext_def using g' 1 by auto
              ultimately have "g = g'"
                using 1 f\<phi>.arrow_from_functor_axioms f'\<phi>.arrow_from_functor_axioms
                      \<epsilon>a.the_coext_unique [of b' "\<epsilon> a \<cdot>\<^sub>C f \<cdot>\<^sub>C \<phi>" g]
                      \<epsilon>a.the_coext_unique [of b' "\<epsilon> a \<cdot>\<^sub>C f' \<cdot>\<^sub>C \<phi>" g']
                by auto
              hence "f \<cdot>\<^sub>C \<phi> = f' \<cdot>\<^sub>C \<phi>"
                using g g' is_faithful by argo
              thus "f = f'"
                using \<phi> f f' par C.iso_is_retraction C.retraction_is_epi
                      C.epiE [of \<phi> f f']
                by auto
            qed
          qed
          ultimately show "C.iso (\<epsilon> a)"
            using C.iso_iff_mono_and_retraction by simp
        qed
        interpret \<epsilon>: natural_isomorphism C C "F o G" C.map \<epsilon>
          using 1 by (unfold_locales, auto)
        interpret \<epsilon>F: natural_isomorphism D C "F o G o F" F "\<epsilon>F.map"
          using \<epsilon>.components_are_iso by (unfold_locales, simp)
        show "\<And>a. D.ide a \<Longrightarrow> D.iso (\<eta> a)"
        proof -
          fix a
          assume a: "D.ide a"
          have 1: "C.iso (\<epsilon>F.map a)"
            using a \<epsilon>.components_are_iso by simp
          moreover have "\<epsilon>F.map a \<cdot>\<^sub>C F\<eta>.map a = F a"
            using a \<eta>\<epsilon>.triangle_F \<epsilon>FoF\<eta>.map_simp_ide by simp
          ultimately have "C.inverse_arrows (\<epsilon>F.map a) (F\<eta>.map a)"
            using a C.section_retraction_of_iso by simp
          hence "C.iso (F\<eta>.map a)"
            using C.iso_inv_iso by blast
          thus "D.iso (\<eta> a)"
            using a reflects_iso [of "\<eta> a"] by fastforce
        qed
      qed
      (*
       * Uggh, I should have started with "right_adjoint_functor C D G" so that the
       * following would come out right.  Instead, another step is needed to dualize.
       * TODO: Maybe re-work this later.
       *)
      interpret adjoint_equivalence C D F G \<eta> \<epsilon> ..
      interpret \<epsilon>': inverse_transformation C C "F o G" C.map \<epsilon> ..
      interpret \<eta>': inverse_transformation D D D.map "G o F" \<eta> ..
      interpret E: adjoint_equivalence D C G F \<epsilon>'.map \<eta>'.map
        using adjoint_equivalence_axioms dual_equivalence by blast
      have "equivalence_of_categories D C G F \<epsilon>'.map \<eta>'.map" ..
      thus "\<exists>G \<eta> \<epsilon>. equivalence_of_categories D C G F \<eta> \<epsilon>" by blast
    qed

  end

  sublocale fully_faithful_and_essentially_surjective_functor \<subseteq> equivalence_functor D C F
    using is_equivalence_functor by blast

end
