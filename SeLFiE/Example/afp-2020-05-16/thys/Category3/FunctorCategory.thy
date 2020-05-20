(*  Title:       FunctorCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter FunctorCategory

theory FunctorCategory
imports ConcreteCategory BinaryFunctor
begin

  text\<open>
    The functor category \<open>[A, B]\<close> is the category whose objects are functors
    from @{term A} to @{term B} and whose arrows correspond to natural transformations
    between these functors.
\<close>

  section "Construction"

  text\<open>
    Since the arrows of a functor category cannot (in the context of the present development)
    be directly identified with natural transformations, but rather only with natural
    transformations that have been equipped with their domain and codomain functors,
    and since there is no natural value to serve as @{term null},
    we use the general-purpose construction given by @{locale concrete_category} to define
    this category.
\<close>

  locale functor_category =
    A: category A +
    B: category B
  for A :: "'a comp"     (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"     (infixr "\<cdot>\<^sub>B" 55)
  begin

    notation A.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>A _\<guillemotright>")
    notation B.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")

    type_synonym ('aa, 'bb) arr = "('aa \<Rightarrow> 'bb, 'aa \<Rightarrow> 'bb) concrete_category.arr"

    sublocale concrete_category \<open>Collect (functor A B)\<close>
      \<open>\<lambda>F G. Collect (natural_transformation A B F G)\<close> \<open>\<lambda>F. F\<close>
      \<open>\<lambda>F G H \<tau> \<sigma>. vertical_composite.map A B \<sigma> \<tau>\<close>
      using vcomp_assoc
      apply (unfold_locales, simp_all)
    proof -
      fix F G H \<sigma> \<tau>
      assume F: "functor (\<cdot>\<^sub>A) (\<cdot>\<^sub>B) F"
      assume G: "functor (\<cdot>\<^sub>A) (\<cdot>\<^sub>B) G"
      assume H: "functor (\<cdot>\<^sub>A) (\<cdot>\<^sub>B) H"
      assume \<sigma>: "natural_transformation (\<cdot>\<^sub>A) (\<cdot>\<^sub>B) F G \<sigma>"
      assume \<tau>: "natural_transformation (\<cdot>\<^sub>A) (\<cdot>\<^sub>B) G H \<tau>"
      interpret F: "functor" A B F using F by simp
      interpret G: "functor" A B G using G by simp
      interpret H: "functor" A B H using H by simp
      interpret \<sigma>: natural_transformation A B F G \<sigma>
        using \<sigma> by simp
      interpret \<tau>: natural_transformation A B G H \<tau>
        using \<tau> by simp
      interpret \<tau>\<sigma>: vertical_composite A B F G H \<sigma> \<tau>
        ..
      show "natural_transformation (\<cdot>\<^sub>A) (\<cdot>\<^sub>B) F H (vertical_composite.map (\<cdot>\<^sub>A) (\<cdot>\<^sub>B) \<sigma> \<tau>)"
        using \<tau>\<sigma>.map_def \<tau>\<sigma>.is_natural_transformation by simp
    qed

    abbreviation comp      (infixr "\<cdot>" 55)
    where "comp \<equiv> COMP"
    notation in_hom        ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    lemma arrI [intro]:
    assumes "f \<noteq> null" and "natural_transformation A B (Dom f) (Cod f) (Map f)"
    shows "arr f"
      using assms arr_char null_char
      by (simp add: natural_transformation_def)

    lemma arrE [elim]:
    assumes "arr f"
    and "f \<noteq> null \<Longrightarrow> natural_transformation A B (Dom f) (Cod f) (Map f) \<Longrightarrow> T"
    shows T
      using assms arr_char null_char by simp

    lemma arr_MkArr [iff]:
    shows "arr (MkArr F G \<tau>) \<longleftrightarrow> natural_transformation A B F G \<tau>"
      using arr_char null_char arr_MkArr natural_transformation_def by fastforce

    lemma ide_char [iff]:
    shows "ide t \<longleftrightarrow> t \<noteq> null \<and> functor A B (Map t) \<and> Dom t = Map t \<and> Cod t = Map t"
      using ide_char null_char by fastforce

  end

  section "Additional Properties"

  text\<open>
    In this section some additional facts are proved, which make it easier to
    work with the @{term "functor_category"} locale.
\<close>

  context functor_category
  begin

    lemma Map_comp [simp]:
    assumes "seq t' t" and "A.seq a' a"
    shows "Map (t' \<cdot> t) (a' \<cdot>\<^sub>A a) = Map t' a' \<cdot>\<^sub>B Map t a"
    proof -
      interpret t: natural_transformation A B \<open>Dom t\<close> \<open>Cod t\<close> \<open>Map t\<close>
        using assms(1) arr_char seq_char by blast
      interpret t': natural_transformation A B \<open>Cod t\<close> \<open>Cod t'\<close> \<open>Map t'\<close>
        using assms(1) arr_char seq_char by force 
      interpret t'ot: vertical_composite A B \<open>Dom t\<close> \<open>Cod t\<close> \<open>Cod t'\<close> \<open>Map t\<close> \<open>Map t'\<close> ..
      show ?thesis
      proof -
        have "Map (t' \<cdot> t) = t'ot.map"
          using assms(1) seq_char t'ot.natural_transformation_axioms by simp
        thus ?thesis
          using assms(2) t'ot.map_simp_2 t'.preserves_comp_2 B.comp_assoc by auto
      qed
    qed

    lemma Map_comp':
    assumes "seq t' t"
    shows "Map (t' \<cdot> t) = vertical_composite.map A B (Map t) (Map t')"
    proof -
      interpret t: natural_transformation A B \<open>Dom t\<close> \<open>Cod t\<close> \<open>Map t\<close>
        using assms(1) arr_char seq_char by blast
      interpret t': natural_transformation A B \<open>Cod t\<close> \<open>Cod t'\<close> \<open>Map t'\<close>
        using assms(1) arr_char seq_char by force 
      interpret t'ot: vertical_composite A B \<open>Dom t\<close> \<open>Cod t\<close> \<open>Cod t'\<close> \<open>Map t\<close> \<open>Map t'\<close> ..
      show ?thesis
        using assms(1) seq_char t'ot.natural_transformation_axioms by simp
    qed

    lemma MkArr_eqI [intro]:
    assumes "arr (MkArr F G \<tau>)"
    and "F = F'" and "G = G'" and "\<tau> = \<tau>'"
    shows "MkArr F G \<tau> = MkArr F' G' \<tau>'"
      using assms arr_eqI by simp

    lemma MkArr_eqI' [intro]:
    assumes "arr (MkArr F G \<tau>)" and "\<tau> = \<tau>'"
    shows "MkArr F G \<tau> = MkArr F G \<tau>'"
      using assms arr_eqI by simp

    lemma iso_char [iff]:
    shows "iso t \<longleftrightarrow> t \<noteq> null \<and> natural_isomorphism A B (Dom t) (Cod t) (Map t)"
    proof
      assume t: "iso t"
      show "t \<noteq> null \<and> natural_isomorphism A B (Dom t) (Cod t) (Map t)"
      proof
        show "t \<noteq> null" using t arr_char iso_is_arr by auto
        from t obtain t' where t': "inverse_arrows t t'" by blast
        interpret \<tau>: natural_transformation A B \<open>Dom t\<close> \<open>Cod t\<close> \<open>Map t\<close>
          using t arr_char iso_is_arr by auto
        interpret \<tau>': natural_transformation A B \<open>Cod t\<close> \<open>Dom t\<close> \<open>Map t'\<close>
          using t' arr_char dom_char seq_char
          by (metis arrE ide_compE inverse_arrowsE)
        interpret \<tau>'o\<tau>: vertical_composite A B \<open>Dom t\<close> \<open>Cod t\<close> \<open>Dom t\<close> \<open>Map t\<close> \<open>Map t'\<close> ..
        interpret \<tau>o\<tau>': vertical_composite A B \<open>Cod t\<close> \<open>Dom t\<close> \<open>Cod t\<close> \<open>Map t'\<close> \<open>Map t\<close> ..
        show "natural_isomorphism A B (Dom t) (Cod t) (Map t)"
        proof
          fix a
          assume a: "A.ide a"
          show "B.iso (Map t a)"
          proof
            have 1: "\<tau>'o\<tau>.map = Dom t \<and> \<tau>o\<tau>'.map = Cod t"
              using t t'
              by (metis (no_types, lifting) Map_dom concrete_category.Map_comp
                  concrete_category_axioms ide_compE inverse_arrowsE seq_char)
            show "B.inverse_arrows (Map t a) (Map t' a)"
              using a 1 \<tau>o\<tau>'.map_simp_ide \<tau>'o\<tau>.map_simp_ide \<tau>.F.preserves_ide \<tau>.G.preserves_ide
              by auto
          qed
        qed
      qed
      next
      assume t: "t \<noteq> null \<and> natural_isomorphism A B (Dom t) (Cod t) (Map t)"
      show "iso t"
      proof
        interpret \<tau>: natural_isomorphism A B \<open>Dom t\<close> \<open>Cod t\<close> \<open>Map t\<close>
          using t by auto
        interpret \<tau>': inverse_transformation A B \<open>Dom t\<close> \<open>Cod t\<close> \<open>Map t\<close> ..
        have 1: "vertical_composite.map A B (Map t) \<tau>'.map = Dom t \<and>
                 vertical_composite.map A B \<tau>'.map (Map t) = Cod t"
          using \<tau>.natural_isomorphism_axioms vertical_composite_inverse_iso
                vertical_composite_iso_inverse
          by blast
        show "inverse_arrows t (MkArr (Cod t) (Dom t) (\<tau>'.map))"
        proof
          show 2: "ide (MkArr (Cod t) (Dom t) \<tau>'.map \<cdot> t)"
            using t 1
            by (metis (no_types, lifting) MkArr_Map MkIde_Dom \<tau>'.natural_transformation_axioms
                \<tau>.natural_transformation_axioms arrI arr_MkArr comp_MkArr ide_dom)
          show "ide (t \<cdot> MkArr (Cod t) (Dom t) \<tau>'.map)"
            using t 1 2
            by (metis Map.simps(1) \<tau>'.natural_transformation_axioms arr_MkArr comp_char
                dom_MkArr dom_comp ide_char' ide_compE)
        qed
      qed
    qed

  end

  section "Evaluation Functor"

  text\<open>
    This section defines the evaluation map that applies an arrow of the functor
    category \<open>[A, B]\<close> to an arrow of @{term A} to obtain an arrow of @{term B}
    and shows that it is functorial.
\<close>

  locale evaluation_functor =
    A: category A +
    B: category B +
    A_B: functor_category A B +
    A_BxA: product_category A_B.comp A
  for A :: "'a comp"          (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"          (infixr "\<cdot>\<^sub>B" 55)
  begin

    notation A_B.comp         (infixr "\<cdot>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]" 55)
    notation A_BxA.comp       (infixr "\<cdot>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]\<^sub>x\<^sub>A" 55)
    notation A_B.in_hom       ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>] _\<guillemotright>")
    notation A_BxA.in_hom     ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]\<^sub>x\<^sub>A _\<guillemotright>")

    definition map
    where "map Fg \<equiv> if A_BxA.arr Fg then A_B.Map (fst Fg) (snd Fg) else B.null"

    lemma map_simp:
    assumes "A_BxA.arr Fg"
    shows "map Fg = A_B.Map(fst Fg) (snd Fg)"
      using assms map_def by auto

    lemma is_functor:
    shows "functor A_BxA.comp B map"
    proof
      show "\<And>Fg. \<not> A_BxA.arr Fg \<Longrightarrow> map Fg = B.null"
        using map_def by auto
      fix Fg
      assume Fg: "A_BxA.arr Fg"
      let ?F = "fst Fg" and ?g = "snd Fg"
      have F: "A_B.arr ?F" using Fg by auto
      have g: "A.arr ?g" using Fg by auto
      have DomF: "A_B.Dom ?F = A_B.Map (A_B.dom ?F)" using F by simp
      have CodF: "A_B.Cod ?F = A_B.Map (A_B.cod ?F)" using F by simp
      interpret F: natural_transformation A B \<open>A_B.Dom ?F\<close> \<open>A_B.Cod ?F\<close> \<open>A_B.Map ?F\<close>
        using Fg A_B.arr_char [of ?F] by blast
      show "B.arr (map Fg)" using Fg map_def by auto
      show "B.dom (map Fg) = map (A_BxA.dom Fg)"
        using g Fg map_def DomF
        by (metis (no_types, lifting) A_BxA.arr_dom A_BxA.dom_simp F.preserves_dom
            fst_conv snd_conv)
      show "B.cod (map Fg) = map (A_BxA.cod Fg)"
        using g Fg map_def CodF
        by (metis (no_types, lifting) A_BxA.arr_cod A_BxA.cod_simp F.preserves_cod
            fst_conv snd_conv)
      next
      fix Fg Fg'
      assume 1: "A_BxA.seq Fg' Fg"
      let ?F = "fst Fg" and ?g = "snd Fg"
      let ?F' = "fst Fg'" and ?g' = "snd Fg'"
      have F': "A_B.arr ?F'" using 1 A_BxA.seqE by blast
      have CodF: "A_B.Cod ?F = A_B.Map (A_B.cod ?F)"
        using 1 by (metis A_B.Map_cod A_B.seqE A_BxA.seqE)
      have DomF': "A_B.Dom ?F' = A_B.Map (A_B.dom ?F')"
        using F' by simp
      have seq_F'F: "A_B.seq ?F' ?F" using 1 by blast
      have seq_g'g: "A.seq ?g' ?g" using 1 by blast
      interpret F: natural_transformation A B \<open>A_B.Dom ?F\<close> \<open>A_B.Cod ?F\<close> \<open>A_B.Map ?F\<close>
        using 1 A_B.arr_char by blast
      interpret F': natural_transformation A B \<open>A_B.Cod ?F\<close> \<open>A_B.Cod ?F'\<close> \<open>A_B.Map ?F'\<close>
        using 1 A_B.arr_char seq_F'F CodF DomF' A_B.seqE
        by (metis mem_Collect_eq)
      interpret F'oF: vertical_composite A B \<open>A_B.Dom ?F\<close> \<open>A_B.Cod ?F\<close> \<open>A_B.Cod ?F'\<close>
                                             \<open>A_B.Map ?F\<close> \<open>A_B.Map ?F'\<close> ..
      show "map (Fg' \<cdot>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]\<^sub>x\<^sub>A Fg) = map Fg' \<cdot>\<^sub>B map Fg"
        unfolding map_def
        using 1 seq_F'F seq_g'g by auto
    qed

  end

  sublocale evaluation_functor \<subseteq> "functor" A_BxA.comp B map
    using is_functor by auto
  sublocale evaluation_functor \<subseteq> binary_functor A_B.comp A B map ..

  section "Currying"

  text\<open>
    This section defines the notion of currying of a natural transformation
    between binary functors, to obtain a natural transformation between
    functors into a functor category, along with the inverse operation of uncurrying.
    We have only proved here what is needed to establish the results
    in theory \<open>Limit\<close> about limits in functor categories and have not
    attempted to fully develop the functoriality and naturality properties of
    these notions.
\<close>

  locale currying =
  A1: category A1 +
  A2: category A2 +
  B: category B
  for A1 :: "'a1 comp"           (infixr "\<cdot>\<^sub>A\<^sub>1" 55)
  and A2 :: "'a2 comp"           (infixr "\<cdot>\<^sub>A\<^sub>2" 55)
  and B :: "'b comp"             (infixr "\<cdot>\<^sub>B" 55)
  begin

    interpretation A1xA2: product_category A1 A2 ..
    interpretation A2_B: functor_category A2 B ..
    interpretation A2_BxA2: product_category A2_B.comp A2 ..
    interpretation E: evaluation_functor A2 B ..

    notation A1xA2.comp          (infixr "\<cdot>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2" 55)
    notation A2_B.comp           (infixr "\<cdot>\<^sub>[\<^sub>A\<^sub>2,\<^sub>B\<^sub>]" 55)
    notation A2_BxA2.comp        (infixr "\<cdot>\<^sub>[\<^sub>A\<^sub>2\<^sub>,\<^sub>B\<^sub>]\<^sub>x\<^sub>A\<^sub>2" 55)
    notation A1xA2.in_hom        ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2 _\<guillemotright>")
    notation A2_B.in_hom         ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>[\<^sub>A\<^sub>2\<^sub>,\<^sub>B\<^sub>] _\<guillemotright>")
    notation A2_BxA2.in_hom      ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>[\<^sub>A\<^sub>2\<^sub>,\<^sub>B\<^sub>]\<^sub>x\<^sub>A\<^sub>2 _\<guillemotright>")

    text\<open>
      A proper definition for @{term curry} requires that it be parametrized by
      binary functors @{term F} and @{term G} that are the domain and codomain
      of the natural transformations to which it is being applied.
      Similar parameters are not needed in the case of @{term uncurry}.
\<close>

    definition curry :: "('a1 \<times> 'a2 \<Rightarrow> 'b) \<Rightarrow> ('a1 \<times> 'a2 \<Rightarrow> 'b) \<Rightarrow> ('a1 \<times> 'a2 \<Rightarrow> 'b)
                           \<Rightarrow> 'a1 \<Rightarrow> ('a2, 'b) A2_B.arr"
    where "curry F G \<tau> f1 = (if A1.arr f1 then
                               A2_B.MkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                          (\<lambda>f2. \<tau> (f1, f2))
                             else A2_B.null)"

    definition uncurry :: "('a1 \<Rightarrow> ('a2, 'b) A2_B.arr) \<Rightarrow> 'a1 \<times> 'a2 \<Rightarrow> 'b"
    where "uncurry \<tau> f \<equiv> if A1xA2.arr f then E.map (\<tau> (fst f), snd f) else B.null"

    lemma curry_simp:
    assumes "A1.arr f1"
    shows "curry F G \<tau> f1 = A2_B.MkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                       (\<lambda>f2. \<tau> (f1, f2))"
      using assms curry_def by auto

    lemma uncurry_simp:
    assumes "A1xA2.arr f"
    shows "uncurry \<tau> f = E.map (\<tau> (fst f), snd f)"
      using assms uncurry_def by auto

    lemma curry_in_hom:
    assumes f1: "A1.arr f1"
    and "natural_transformation A1xA2.comp B F G \<tau>"
    shows "\<guillemotleft>curry F G \<tau> f1 : curry F F F (A1.dom f1) \<rightarrow>\<^sub>[\<^sub>A\<^sub>2\<^sub>,\<^sub>B\<^sub>] curry G G G (A1.cod f1)\<guillemotright>"
    proof -
      interpret \<tau>: natural_transformation A1xA2.comp B F G \<tau> using assms by auto
      show ?thesis
      proof -
        interpret F_dom_f1: "functor" A2 B \<open>\<lambda>f2. F (A1.dom f1, f2)\<close>
          using f1 \<tau>.F.is_extensional apply (unfold_locales, simp_all)
          by (metis A1xA2.comp_char A1.arr_dom_iff_arr A1.comp_arr_dom A1.dom_dom
                    A1xA2.seqI \<tau>.F.preserves_comp_2 fst_conv snd_conv)
        interpret G_cod_f1: "functor" A2 B \<open>\<lambda>f2. G (A1.cod f1, f2)\<close>
          using f1 \<tau>.G.is_extensional A1.arr_cod_iff_arr
          apply (unfold_locales, simp_all)
          using A1xA2.comp_char A1.arr_cod_iff_arr A1.comp_cod_arr
          by (metis A1.cod_cod A1xA2.seqI \<tau>.G.preserves_comp_2 fst_conv snd_conv)
        have "natural_transformation A2 B (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                          (\<lambda>f2. \<tau> (f1, f2))"
          using f1 \<tau>.is_extensional apply (unfold_locales, simp_all)
        proof -
          fix f2
          assume f2: "A2.arr f2"
          show "G (A1.cod f1, f2) \<cdot>\<^sub>B \<tau> (f1, A2.dom f2) = \<tau> (f1, f2)"
            using f1 f2 \<tau>.preserves_comp_1 [of "(A1.cod f1, f2)" "(f1, A2.dom f2)"]
                  A1.comp_cod_arr A2.comp_arr_dom
            by simp
          show "\<tau> (f1, A2.cod f2) \<cdot>\<^sub>B F (A1.dom f1, f2) = \<tau> (f1, f2)"
            using f1 f2 \<tau>.preserves_comp_2 [of "(f1, A2.cod f2)" "(A1.dom f1, f2)"]
                  A1.comp_arr_dom A2.comp_cod_arr
            by simp
        qed
        thus ?thesis
          using f1 curry_simp by auto
      qed
    qed

    lemma curry_preserves_functors:
    assumes "functor A1xA2.comp B F"
    shows "functor A1 A2_B.comp (curry F F F)"
    proof -
      interpret F: "functor" A1xA2.comp B F using assms by auto
      interpret F: binary_functor A1 A2 B F ..
      show ?thesis
        using curry_def F.fixing_arr_gives_natural_transformation_1
              A2_B.comp_char F.preserves_comp_1 curry_simp A2_B.seq_char
        apply unfold_locales by auto
    qed

    lemma curry_preserves_transformations:
    assumes "natural_transformation A1xA2.comp B F G \<tau>"
    shows "natural_transformation A1 A2_B.comp (curry F F F) (curry G G G) (curry F G \<tau>)"
    proof -
      interpret \<tau>: natural_transformation A1xA2.comp B F G \<tau> using assms by auto
      interpret \<tau>: binary_functor_transformation A1 A2 B F G \<tau> ..
      interpret curry_F: "functor" A1 A2_B.comp \<open>curry F F F\<close>
        using curry_preserves_functors \<tau>.F.functor_axioms by simp
      interpret curry_G: "functor" A1 A2_B.comp \<open>curry G G G\<close>
        using curry_preserves_functors \<tau>.G.functor_axioms by simp
      show ?thesis
      proof
        show "\<And>f2. \<not> A1.arr f2 \<Longrightarrow> curry F G \<tau> f2 = A2_B.null"
          using curry_def by simp
        fix f1
        assume f1: "A1.arr f1"
        show "A2_B.dom (curry F G \<tau> f1) = curry F F F (A1.dom f1)"
          using assms f1 curry_in_hom by blast
        show "A2_B.cod (curry F G \<tau> f1) = curry G G G (A1.cod f1)"
          using assms f1 curry_in_hom by blast
        show "curry G G G f1 \<cdot>\<^sub>[\<^sub>A\<^sub>2,\<^sub>B\<^sub>] curry F G \<tau> (A1.dom f1) = curry F G \<tau> f1"
        proof -
          interpret \<tau>_dom_f1: natural_transformation A2 B \<open>\<lambda>f2. F (A1.dom f1, f2)\<close>
                                \<open>\<lambda>f2. G (A1.dom f1, f2)\<close> \<open>\<lambda>f2. \<tau> (A1.dom f1, f2)\<close>
            using assms f1 curry_in_hom A1.ide_dom \<tau>.fixing_ide_gives_natural_transformation_1
            by blast
          interpret G_f1: natural_transformation A2 B
                                \<open>\<lambda>f2. G (A1.dom f1, f2)\<close> \<open>\<lambda>f2. G (A1.cod f1, f2)\<close> \<open>\<lambda>f2. G (f1, f2)\<close>
            using f1 \<tau>.G.fixing_arr_gives_natural_transformation_1 by simp
          interpret G_f1o\<tau>_dom_f1: vertical_composite A2 B
                                     \<open>\<lambda>f2. F (A1.dom f1, f2)\<close> \<open>\<lambda>f2. G (A1.dom f1, f2)\<close>
                                     \<open>\<lambda>f2. G (A1.cod f1, f2)\<close>
                                     \<open>\<lambda>f2. \<tau> (A1.dom f1, f2)\<close> \<open>\<lambda>f2. G (f1, f2)\<close> ..
          have "curry G G G f1 \<cdot>\<^sub>[\<^sub>A\<^sub>2,\<^sub>B\<^sub>] curry F G \<tau> (A1.dom f1)
                  = A2_B.MkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2)) G_f1o\<tau>_dom_f1.map"
          proof -
            have "A2_B.seq (curry G G G f1) (curry F G \<tau> (A1.dom f1))"
              using f1 curry_in_hom [of "A1.dom f1"] \<tau>.natural_transformation_axioms by force
            thus ?thesis
              using f1 curry_simp A2_B.comp_char [of "curry G G G f1" "curry F G \<tau> (A1.dom f1)"]
              by simp
          qed
          also have "... = A2_B.MkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                      (\<lambda>f2. \<tau> (f1, f2))"
          proof (intro A2_B.MkArr_eqI)
            show "(\<lambda>f2. F (A1.dom f1, f2)) = (\<lambda>f2. F (A1.dom f1, f2))" by simp
            show "(\<lambda>f2. G (A1.cod f1, f2)) = (\<lambda>f2. G (A1.cod f1, f2))" by simp
            show "A2_B.arr (A2_B.MkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                       G_f1o\<tau>_dom_f1.map)"
              using G_f1o\<tau>_dom_f1.natural_transformation_axioms by blast
            show "G_f1o\<tau>_dom_f1.map = (\<lambda>f2. \<tau> (f1, f2))"
            proof
              fix f2
              have "\<not>A2.arr f2 \<Longrightarrow> G_f1o\<tau>_dom_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
                using f1 G_f1o\<tau>_dom_f1.is_extensional \<tau>.is_extensional by simp
              moreover have "A2.arr f2 \<Longrightarrow> G_f1o\<tau>_dom_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
              proof -
                interpret \<tau>_f1: natural_transformation A2 B \<open>\<lambda>f2. F (A1.dom f1, f2)\<close>
                                  \<open>\<lambda>f2. G (A1.cod f1, f2)\<close> \<open>\<lambda>f2. \<tau> (f1, f2)\<close>
                  using assms f1 curry_in_hom [of f1] curry_simp by auto
                fix f2
                assume f2: "A2.arr f2"
                show "G_f1o\<tau>_dom_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
                  using f1 f2 G_f1o\<tau>_dom_f1.map_simp_2 B.comp_assoc \<tau>.is_natural_1
                  by fastforce
              qed
              ultimately show "G_f1o\<tau>_dom_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2" by blast
            qed
          qed
          also have "... = curry F G \<tau> f1" using f1 curry_def by simp
          finally show ?thesis by blast
        qed
        show "curry F G \<tau> (A1.cod f1) \<cdot>\<^sub>[\<^sub>A\<^sub>2,\<^sub>B\<^sub>] curry F F F f1 = curry F G \<tau> f1"
        proof -
          interpret \<tau>_cod_f1: natural_transformation A2 B \<open>\<lambda>f2. F (A1.cod f1, f2)\<close>
                                \<open>\<lambda>f2. G (A1.cod f1, f2)\<close> \<open>\<lambda>f2. \<tau> (A1.cod f1, f2)\<close>
            using assms f1 curry_in_hom A1.ide_cod \<tau>.fixing_ide_gives_natural_transformation_1
            by blast
          interpret F_f1: natural_transformation A2 B
                                \<open>\<lambda>f2. F (A1.dom f1, f2)\<close> \<open>\<lambda>f2. F (A1.cod f1, f2)\<close> \<open>\<lambda>f2. F (f1, f2)\<close>
            using f1 \<tau>.F.fixing_arr_gives_natural_transformation_1 by simp
          interpret \<tau>_cod_f1oF_f1: vertical_composite A2 B
                                     \<open>\<lambda>f2. F (A1.dom f1, f2)\<close> \<open>\<lambda>f2. F (A1.cod f1, f2)\<close>
                                     \<open>\<lambda>f2. G (A1.cod f1, f2)\<close>
                                     \<open>\<lambda>f2. F (f1, f2)\<close> \<open>\<lambda>f2. \<tau> (A1.cod f1, f2)\<close> ..
          have "curry F G \<tau> (A1.cod f1) \<cdot>\<^sub>[\<^sub>A\<^sub>2,\<^sub>B\<^sub>] curry F F F f1
                  = A2_B.MkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2)) \<tau>_cod_f1oF_f1.map"
          proof -
            have
                 "curry F F F f1 =
                    A2_B.MkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. F (A1.cod f1, f2))
                               (\<lambda>f2. F (f1, f2)) \<and>
                  \<guillemotleft>curry F F F f1 : curry F F F (A1.dom f1) \<rightarrow>\<^sub>[\<^sub>A\<^sub>2\<^sub>,\<^sub>B\<^sub>] curry F F F (A1.cod f1)\<guillemotright>"
              using f1 curry_F.preserves_hom curry_simp by blast
            moreover have
                 "curry F G \<tau> (A1.dom f1) =
                    A2_B.MkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.dom f1, f2))
                               (\<lambda>f2. \<tau> (A1.dom f1, f2)) \<and>
                    \<guillemotleft>curry F G \<tau> (A1.cod f1) :
                       curry F F F (A1.cod f1) \<rightarrow>\<^sub>[\<^sub>A\<^sub>2\<^sub>,\<^sub>B\<^sub>] curry G G G (A1.cod f1)\<guillemotright>"
              using assms f1 curry_in_hom [of "A1.cod f1"] curry_def A1.arr_cod_iff_arr by simp
            ultimately show ?thesis
              using f1 curry_def by fastforce
          qed
          also have "... = A2_B.MkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                      (\<lambda>f2. \<tau> (f1, f2))"
          proof (intro A2_B.MkArr_eqI)
            show "(\<lambda>f2. F (A1.dom f1, f2)) = (\<lambda>f2. F (A1.dom f1, f2))" by simp
            show "(\<lambda>f2. G (A1.cod f1, f2)) = (\<lambda>f2. G (A1.cod f1, f2))" by simp
            show "A2_B.arr (A2_B.MkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                       \<tau>_cod_f1oF_f1.map)"
              using \<tau>_cod_f1oF_f1.natural_transformation_axioms by blast
            show "\<tau>_cod_f1oF_f1.map = (\<lambda>f2. \<tau> (f1, f2))"
            proof
              fix f2
              have "\<not>A2.arr f2 \<Longrightarrow> \<tau>_cod_f1oF_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
                using f1 by (simp add: \<tau>.is_extensional \<tau>_cod_f1oF_f1.is_extensional)
              moreover have "A2.arr f2 \<Longrightarrow> \<tau>_cod_f1oF_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
              proof -
                interpret \<tau>_f1: natural_transformation A2 B \<open>\<lambda>f2. F (A1.dom f1, f2)\<close>
                                  \<open>\<lambda>f2. G (A1.cod f1, f2)\<close> \<open>\<lambda>f2. \<tau> (f1, f2)\<close>
                  using assms f1 curry_in_hom [of f1] curry_simp by auto
                fix f2
                assume f2: "A2.arr f2"
                show "\<tau>_cod_f1oF_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
                  using f1 f2 \<tau>_cod_f1oF_f1.map_simp_1 B.comp_assoc \<tau>.is_natural_2
                  by fastforce
              qed
              ultimately show "\<tau>_cod_f1oF_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2" by blast
            qed
          qed
          also have "... = curry F G \<tau> f1" using f1 curry_def by simp
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma uncurry_preserves_functors:
    assumes "functor A1 A2_B.comp F"
    shows "functor A1xA2.comp B (uncurry F)"
    proof -
      interpret F: "functor" A1 A2_B.comp F using assms by auto
      show ?thesis
        using uncurry_def
        apply (unfold_locales)
            apply auto[4]
      proof -
        fix f g :: "'a1 * 'a2"
        let ?f1 = "fst f"
        let ?f2 = "snd f"
        let ?g1 = "fst g"
        let ?g2 = "snd g"
        assume fg: "A1xA2.seq g f"
        have f: "A1xA2.arr f" using fg A1xA2.seqE by blast
        have f1: "A1.arr ?f1" using f by auto
        have f2: "A2.arr ?f2" using f by auto
        have g: "\<guillemotleft>g : A1xA2.cod f \<rightarrow>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2 A1xA2.cod g\<guillemotright>"
          using fg A1xA2.dom_char A1xA2.cod_char
          by (elim A1xA2.seqE, intro A1xA2.in_homI, auto)
        let ?g1 = "fst g"
        let ?g2 = "snd g"
        have g1: "\<guillemotleft>?g1 : A1.cod ?f1 \<rightarrow>\<^sub>A\<^sub>1 A1.cod ?g1\<guillemotright>"
          using f g by (intro A1.in_homI, auto)
        have g2: "\<guillemotleft>?g2 : A2.cod ?f2 \<rightarrow>\<^sub>A\<^sub>2 A2.cod ?g2\<guillemotright>"
          using f g by (intro A2.in_homI, auto)
        interpret Ff1: natural_transformation A2 B \<open>A2_B.Dom (F ?f1)\<close> \<open>A2_B.Cod (F ?f1)\<close>
                                                   \<open>A2_B.Map (F ?f1)\<close>
          using f A2_B.arr_char [of "F ?f1"] by auto
        interpret Fg1: natural_transformation A2 B \<open>A2_B.Cod (F ?f1)\<close> \<open>A2_B.Cod (F ?g1)\<close>
                                                   \<open>A2_B.Map (F ?g1)\<close>
          using f1 g1 A2_B.arr_char F.preserves_arr
                A2_B.Map_dom [of "F ?g1"] A2_B.Map_cod [of "F ?f1"]
          by fastforce
        interpret Fg1oFf1: vertical_composite A2 B
                              \<open>A2_B.Dom (F ?f1)\<close> \<open>A2_B.Cod (F ?f1)\<close> \<open>A2_B.Cod (F ?g1)\<close>
                              \<open>A2_B.Map (F ?f1)\<close> \<open>A2_B.Map (F ?g1)\<close> ..
        show "uncurry F (g \<cdot>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2 f) = uncurry F g \<cdot>\<^sub>B uncurry F f"
          using f1 g1 g2 g2 f g fg E.map_simp uncurry_def by auto
      qed
    qed

    lemma uncurry_preserves_transformations:
    assumes "natural_transformation A1 A2_B.comp F G \<tau>"
    shows "natural_transformation A1xA2.comp B (uncurry F) (uncurry G) (uncurry \<tau>)"
    proof -
      interpret \<tau>: natural_transformation A1 A2_B.comp F G \<tau> using assms by auto
      interpret "functor" A1xA2.comp B \<open>uncurry F\<close>
        using \<tau>.F.functor_axioms uncurry_preserves_functors by blast
      interpret "functor" A1xA2.comp B \<open>uncurry G\<close>
        using \<tau>.G.functor_axioms uncurry_preserves_functors by blast
      show ?thesis
      proof
        fix f
        show "\<not> A1xA2.arr f \<Longrightarrow> uncurry \<tau> f = B.null"
          using uncurry_def by auto
        assume f: "A1xA2.arr f"
        let ?f1 = "fst f"
        let ?f2 = "snd f"
        show "B.dom (uncurry \<tau> f) = uncurry F (A1xA2.dom f)"
          using f uncurry_def by simp
        show "B.cod (uncurry \<tau> f) = uncurry G (A1xA2.cod f)"
          using f uncurry_def by simp
        show "uncurry G f \<cdot>\<^sub>B uncurry \<tau> (A1xA2.dom f) = uncurry \<tau> f"
          using f uncurry_def \<tau>.is_natural_1 A2_BxA2.seq_char A2.comp_arr_dom
                E.preserves_comp [of "(G (fst f), snd f)" "(\<tau> (A1.dom (fst f)), A2.dom (snd f))"]
          by auto
        show "uncurry \<tau> (A1xA2.cod f) \<cdot>\<^sub>B uncurry F f = uncurry \<tau> f"
        proof -
          have 1: "A1.arr ?f1 \<and> A1.arr (fst (A1.cod ?f1, A2.cod ?f2)) \<and>
                   A1.cod ?f1 = A1.dom (fst (A1.cod ?f1, A2.cod ?f2)) \<and>
                   A2.seq (snd (A1.cod ?f1, A2.cod ?f2)) ?f2"
            using f A1.arr_cod_iff_arr A2.arr_cod_iff_arr by auto
          hence 2:
              "?f2 = A2 (snd (\<tau> (fst (A1xA2.cod f)), snd (A1xA2.cod f))) (snd (F ?f1, ?f2))"
            using f A2.comp_cod_arr by simp
          have "A2_B.arr (\<tau> ?f1)" using 1 by force
          thus ?thesis
            unfolding uncurry_def E.map_def
            using f 1 2
            apply simp
            by (metis (no_types, lifting) A2_B.Map_comp \<open>A2_B.arr (\<tau> (fst f))\<close> \<tau>.is_natural_2)

        qed
      qed
    qed

    lemma uncurry_curry:
    assumes "natural_transformation A1xA2.comp B F G \<tau>"
    shows "uncurry (curry F G \<tau>) = \<tau>"
    proof
      interpret \<tau>: natural_transformation A1xA2.comp B F G \<tau> using assms by auto
      interpret curry_\<tau>: natural_transformation A1 A2_B.comp \<open>curry F F F\<close> \<open>curry G G G\<close>
                                                             \<open>curry F G \<tau>\<close>
        using assms curry_preserves_transformations by auto
      fix f
      have "\<not>A1xA2.arr f \<Longrightarrow> uncurry (curry F G \<tau>) f = \<tau> f"
        using curry_def uncurry_def \<tau>.is_extensional by auto
      moreover have "A1xA2.arr f \<Longrightarrow> uncurry (curry F G \<tau>) f = \<tau> f"
      proof -
        assume f: "A1xA2.arr f"
        have 1: "A2_B.Map (curry F G \<tau> (fst f)) (snd f) = \<tau> (fst f, snd f)"
          using f A1xA2.arr_char curry_def by simp
        thus "uncurry (curry F G \<tau>) f = \<tau> f"
          unfolding uncurry_def E.map_def
          using f 1 A1xA2.arr_char [of f] by simp
      qed
      ultimately show "uncurry (curry F G \<tau>) f = \<tau> f" by blast
    qed

    lemma curry_uncurry:
    assumes "functor A1 A2_B.comp F" and "functor A1 A2_B.comp G"
    and "natural_transformation A1 A2_B.comp F G \<tau>"
    shows "curry (uncurry F) (uncurry G) (uncurry \<tau>) = \<tau>"
    proof
      interpret F: "functor" A1 A2_B.comp F using assms(1) by auto
      interpret G: "functor" A1 A2_B.comp G using assms(2) by auto
      interpret \<tau>: natural_transformation A1 A2_B.comp F G \<tau> using assms(3) by auto
      interpret uncurry_F: "functor" A1xA2.comp B \<open>uncurry F\<close>
        using F.functor_axioms uncurry_preserves_functors by auto
      interpret uncurry_G: "functor" A1xA2.comp B \<open>uncurry G\<close>
        using G.functor_axioms uncurry_preserves_functors by auto
      fix f1
      have "\<not>A1.arr f1 \<Longrightarrow> curry (uncurry F) (uncurry G) (uncurry \<tau>) f1 = \<tau> f1"
        using curry_def uncurry_def \<tau>.is_extensional by simp
      moreover have "A1.arr f1 \<Longrightarrow> curry (uncurry F) (uncurry G) (uncurry \<tau>) f1 = \<tau> f1"
      proof -
        assume f1: "A1.arr f1"
        interpret uncurry_\<tau>:
            natural_transformation A1xA2.comp B \<open>uncurry F\<close> \<open>uncurry G\<close> \<open>uncurry \<tau>\<close>
          using \<tau>.natural_transformation_axioms uncurry_preserves_transformations [of F G \<tau>]
          by simp
        have "curry (uncurry F) (uncurry G) (uncurry \<tau>) f1 =
                A2_B.MkArr (\<lambda>f2. uncurry F (A1.dom f1, f2)) (\<lambda>f2. uncurry G (A1.cod f1, f2))
                           (\<lambda>f2. uncurry \<tau> (f1, f2))"
          using f1 curry_def by simp
        also have "... = A2_B.MkArr (\<lambda>f2. uncurry F (A1.dom f1, f2))
                                    (\<lambda>f2. uncurry G (A1.cod f1, f2))
                                    (\<lambda>f2. E.map (\<tau> f1, f2))"
        proof -
          have "(\<lambda>f2. uncurry \<tau> (f1, f2)) = (\<lambda>f2. E.map (\<tau> f1, f2))"
            using f1 uncurry_def E.is_extensional by auto
          thus ?thesis by simp
        qed
        also have "... = \<tau> f1"
        proof -
          have "A2_B.Dom (\<tau> f1) = (\<lambda>f2. uncurry F (A1.dom f1, f2))"
          proof -
            have "A2_B.Dom (\<tau> f1) = A2_B.Map (A2_B.dom (\<tau> f1))"
              using f1 A2_B.ide_char A2_B.Map_dom A2_B.dom_char by auto
            also have "... = A2_B.Map (F (A1.dom f1))"
              using f1 by simp
            also have "... = (\<lambda>f2. uncurry F (A1.dom f1, f2))"
            proof
              fix f2
              interpret F_dom_f1: "functor" A2 B \<open>A2_B.Map (F (A1.dom f1))\<close>
                using f1 A2_B.ide_char F.preserves_ide by simp
              show "A2_B.Map (F (A1.dom f1)) f2 = uncurry F (A1.dom f1, f2)"
                using f1 uncurry_def E.map_simp F_dom_f1.is_extensional by auto
            qed
            finally show ?thesis by auto
          qed
          moreover have "A2_B.Cod (\<tau> f1) = (\<lambda>f2. uncurry G (A1.cod f1, f2))"
          proof -
            have "A2_B.Cod (\<tau> f1) = A2_B.Map (A2_B.cod (\<tau> f1))"
              using f1 A2_B.ide_char A2_B.Map_cod A2_B.cod_char by auto
            also have "... = A2_B.Map (G (A1.cod f1))"
              using f1 by simp
            also have "... = (\<lambda>f2. uncurry G (A1.cod f1, f2))"
            proof
              fix f2
              interpret G_cod_f1: "functor" A2 B \<open>A2_B.Map (G (A1.cod f1))\<close>
                using f1 A2_B.ide_char G.preserves_ide by simp
              show "A2_B.Map (G (A1.cod f1)) f2 = uncurry G (A1.cod f1, f2)"
                using f1 uncurry_def E.map_simp G_cod_f1.is_extensional by auto
            qed
            finally show ?thesis by auto
          qed
          moreover have "A2_B.Map (\<tau> f1) = (\<lambda>f2. E.map (\<tau> f1, f2))"
          proof
            fix f2
            have "\<not>A2.arr f2 \<Longrightarrow> A2_B.Map (\<tau> f1) f2 = (\<lambda>f2. E.map (\<tau> f1, f2)) f2"
              using f1 A2_B.arrE \<tau>.preserves_reflects_arr natural_transformation.is_extensional
              by (metis (no_types, lifting) E.fixing_arr_gives_natural_transformation_1)
            moreover have "A2.arr f2 \<Longrightarrow> A2_B.Map (\<tau> f1) f2 = (\<lambda>f2. E.map (\<tau> f1, f2)) f2"
              using f1 E.map_simp by fastforce
            ultimately show "A2_B.Map (\<tau> f1) f2 = (\<lambda>f2. E.map (\<tau> f1, f2)) f2" by blast
          qed
          ultimately show ?thesis
            using f1 A2_B.MkArr_Map \<tau>.preserves_reflects_arr by metis
        qed
        finally show ?thesis by auto
      qed
      ultimately show "curry (uncurry F) (uncurry G) (uncurry \<tau>) f1 = \<tau> f1" by blast
    qed

  end

  locale curried_functor =
     currying A1 A2 B +
     A1xA2: product_category A1 A2 +
     A2_B: functor_category A2 B +
     F: binary_functor A1 A2 B F
  for A1 :: "'a1 comp"         (infixr "\<cdot>\<^sub>A\<^sub>1" 55)
  and A2 :: "'a2 comp"         (infixr "\<cdot>\<^sub>A\<^sub>2" 55)
  and B :: "'b comp"           (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a1 * 'a2 \<Rightarrow> 'b"
  begin

    notation A1xA2.comp        (infixr "\<cdot>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2" 55)
    notation A2_B.comp         (infixr "\<cdot>\<^sub>[\<^sub>A\<^sub>2,\<^sub>B\<^sub>]" 55)
    notation A1xA2.in_hom      ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2 _\<guillemotright>")
    notation A2_B.in_hom       ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>[\<^sub>A\<^sub>2\<^sub>,\<^sub>B\<^sub>] _\<guillemotright>")

    definition map
    where "map \<equiv> curry F F F"

    lemma map_simp [simp]:
    assumes "A1.arr f1"
    shows "map f1 =
           A2_B.MkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. F (A1.cod f1, f2)) (\<lambda>f2. F (f1, f2))"
      using assms map_def curry_simp by auto

    lemma is_functor:
    shows "functor A1 A2_B.comp map"
      using F.functor_axioms map_def curry_preserves_functors by simp

  end

  sublocale curried_functor \<subseteq> "functor" A1 A2_B.comp map
    using is_functor by auto

  locale curried_functor' =
     A1: category A1 +
     A2: category A2 +
     A1xA2: product_category A1 A2 +
     currying A2 A1 B +
     F: binary_functor A1 A2 B F +
     A1_B: functor_category A1 B
  for A1 :: "'a1 comp"         (infixr "\<cdot>\<^sub>A\<^sub>1" 55)
  and A2 :: "'a2 comp"         (infixr "\<cdot>\<^sub>A\<^sub>2" 55)
  and B :: "'b comp"           (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a1 * 'a2 \<Rightarrow> 'b"
  begin

    notation A1xA2.comp        (infixr "\<cdot>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2" 55)
    notation A1_B.comp         (infixr "\<cdot>\<^sub>[\<^sub>A\<^sub>1,\<^sub>B\<^sub>]" 55)
    notation A1xA2.in_hom      ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2 _\<guillemotright>")
    notation A1_B.in_hom       ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>[\<^sub>A\<^sub>1\<^sub>,\<^sub>B\<^sub>] _\<guillemotright>")

    definition map
    where "map \<equiv> curry F.sym F.sym F.sym"

    lemma map_simp [simp]:
    assumes "A2.arr f2"
    shows "map f2 =
           A1_B.MkArr (\<lambda>f1. F (f1, A2.dom f2)) (\<lambda>f1. F (f1, A2.cod f2)) (\<lambda>f1. F (f1, f2))"
      using assms map_def curry_simp by simp

    lemma is_functor:
    shows "functor A2 A1_B.comp map"
    proof -
      interpret A2xA1: product_category A2 A1 ..
      interpret F': binary_functor A2 A1 B F.sym
        using F.sym_is_binary_functor by simp
      have "functor A2xA1.comp B F.sym" ..
      thus ?thesis using map_def curry_preserves_functors by simp
    qed

  end

  sublocale curried_functor' \<subseteq> "functor" A2 A1_B.comp map
    using is_functor by auto

end

