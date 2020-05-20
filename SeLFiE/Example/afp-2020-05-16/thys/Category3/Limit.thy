(*  Title:       Limit
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter Limit

theory Limit
imports FreeCategory DiscreteCategory Adjunction
begin

  text\<open>
    This theory defines the notion of limit in terms of diagrams and cones and relates
    it to the concept of a representation of a functor.  The diagonal functor associated
    with a diagram shape @{term J} is defined and it is shown that a right adjoint to
    the diagonal functor gives limits of shape @{term J} and that a category has limits
    of shape @{term J} if and only if the diagonal functor is a left adjoint functor.
    Products and equalizers are defined as special cases of limits, and it is shown
    that a category with equalizers has limits of shape @{term J} if it has products
    indexed by the sets of objects and arrows of @{term J}.
    The existence of limits in a set category is investigated, and it is shown that
    every set category has equalizers and that a set category @{term S} has @{term I}-indexed
    products if and only if the universe of @{term S} ``admits @{term I}-indexed tupling.''
    The existence of limits in functor categories is also developed, showing that
    limits in functor categories are ``determined pointwise'' and that a functor category
    @{term "[A, B]"} has limits of shape @{term J} if @{term B} does.
    Finally, it is shown that the Yoneda functor preserves limits.

    This theory concerns itself only with limits; I have made no attempt to consider colimits.
    Although it would be possible to rework the entire development in dual form,
    it is possible that there is a more efficient way to dualize at least parts of it without
    repeating all the work.  This is something that deserves further thought.
\<close>

  section "Representations of Functors"

  text\<open>
    A representation of a contravariant functor \<open>F: Cop \<rightarrow> S\<close>, where @{term S}
    is a set category that is the target of a hom-functor for @{term C}, consists of
    an object @{term a} of @{term C} and a natural isomorphism @{term "\<Phi>: Y a \<rightarrow> F"},
    where \<open>Y: C \<rightarrow> [Cop, S]\<close> is the Yoneda functor.
\<close>

  locale representation_of_functor =
    C: category C +
    Cop: dual_category C +
    S: set_category S +
    F: "functor" Cop.comp S F +
    Hom: hom_functor C S \<phi> +
    Ya: yoneda_functor_fixed_object C S \<phi> a +
    natural_isomorphism Cop.comp S \<open>Ya.Y a\<close> F \<Phi>
  for C :: "'c comp"      (infixr "\<cdot>" 55)
  and S :: "'s comp"      (infixr "\<cdot>\<^sub>S" 55)
  and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
  and F :: "'c \<Rightarrow> 's"
  and a :: 'c
  and \<Phi> :: "'c \<Rightarrow> 's"
  begin

     abbreviation Y where "Y \<equiv> Ya.Y"
     abbreviation \<psi> where "\<psi> \<equiv> Hom.\<psi>"

  end

  text\<open>
    Two representations of the same functor are uniquely isomorphic.
\<close>

  locale two_representations_one_functor =
    C: category C +
    Cop: dual_category C +
    S: set_category S +
    F: set_valued_functor Cop.comp S F +
    yoneda_functor C S \<phi> +
    Ya: yoneda_functor_fixed_object C S \<phi> a +
    Ya': yoneda_functor_fixed_object C S \<phi> a' +
    \<Phi>: representation_of_functor C S \<phi> F a \<Phi> +
    \<Phi>': representation_of_functor C S \<phi> F a' \<Phi>'
  for C :: "'c comp"      (infixr "\<cdot>" 55)
  and S :: "'s comp"      (infixr "\<cdot>\<^sub>S" 55)
  and F :: "'c \<Rightarrow> 's"
  and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
  and a :: 'c
  and \<Phi> :: "'c \<Rightarrow> 's"
  and a' :: 'c
  and \<Phi>' :: "'c \<Rightarrow> 's"
  begin

    interpretation \<Psi>: inverse_transformation Cop.comp S \<open>Y a\<close> F \<Phi> ..
    interpretation \<Psi>': inverse_transformation Cop.comp S \<open>Y a'\<close> F \<Phi>' ..
    interpretation \<Phi>\<Psi>': vertical_composite Cop.comp S \<open>Y a\<close> F \<open>Y a'\<close> \<Phi> \<Psi>'.map ..
    interpretation \<Phi>'\<Psi>: vertical_composite Cop.comp S \<open>Y a'\<close> F \<open>Y a\<close> \<Phi>' \<Psi>.map ..

    lemma are_uniquely_isomorphic:
      shows "\<exists>!\<phi>. \<guillemotleft>\<phi> : a \<rightarrow> a'\<guillemotright> \<and> C.iso \<phi> \<and> map \<phi> = Cop_S.MkArr (Y a) (Y a') \<Phi>\<Psi>'.map"
    proof -
      have "natural_isomorphism Cop.comp S (Y a) F \<Phi>" ..
      moreover have "natural_isomorphism Cop.comp S F (Y a') \<Psi>'.map" ..
      ultimately have 1: "natural_isomorphism Cop.comp S (Y a) (Y a') \<Phi>\<Psi>'.map"
        using NaturalTransformation.natural_isomorphisms_compose by blast
      interpret \<Phi>\<Psi>': natural_isomorphism Cop.comp S \<open>Y a\<close> \<open>Y a'\<close> \<Phi>\<Psi>'.map
        using 1 by auto

      have "natural_isomorphism Cop.comp S (Y a') F \<Phi>'" ..
      moreover have "natural_isomorphism Cop.comp S F (Y a) \<Psi>.map" ..
      ultimately have 2: "natural_isomorphism Cop.comp S (Y a') (Y a) \<Phi>'\<Psi>.map"
        using NaturalTransformation.natural_isomorphisms_compose by blast
      interpret \<Phi>'\<Psi>: natural_isomorphism Cop.comp S \<open>Y a'\<close> \<open>Y a\<close> \<Phi>'\<Psi>.map
        using 2 by auto

      interpret \<Phi>\<Psi>'_\<Phi>'\<Psi>: inverse_transformations Cop.comp S \<open>Y a\<close> \<open>Y a'\<close> \<Phi>\<Psi>'.map \<Phi>'\<Psi>.map
      proof
        fix x
        assume X: "Cop.ide x"
        show "S.inverse_arrows (\<Phi>\<Psi>'.map x) (\<Phi>'\<Psi>.map x)"
        proof
          have 1: "S.arr (\<Phi>\<Psi>'.map x) \<and> \<Phi>\<Psi>'.map x = \<Psi>'.map x \<cdot>\<^sub>S \<Phi> x"
            using X \<Phi>\<Psi>'.preserves_reflects_arr [of x]
            by (simp add: \<Phi>\<Psi>'.map_simp_2)
          have 2: "S.arr (\<Phi>'\<Psi>.map x) \<and> \<Phi>'\<Psi>.map x = \<Psi>.map x \<cdot>\<^sub>S \<Phi>' x"
            using X \<Phi>'\<Psi>.preserves_reflects_arr [of x]
            by (simp add: \<Phi>'\<Psi>.map_simp_1)
          show "S.ide (\<Phi>\<Psi>'.map x \<cdot>\<^sub>S \<Phi>'\<Psi>.map x)"
            using 1 2 X \<Psi>.is_natural_2 \<Psi>'.inverts_components \<Psi>.inverts_components
            by (metis S.inverse_arrows_def S.inverse_arrows_compose)
          show "S.ide (\<Phi>'\<Psi>.map x \<cdot>\<^sub>S \<Phi>\<Psi>'.map x)"
            using 1 2 X \<Psi>'.inverts_components \<Psi>.inverts_components
            by (metis S.inverse_arrows_def S.inverse_arrows_compose)
        qed
      qed

      have "Cop_S.inverse_arrows (Cop_S.MkArr (Y a) (Y a') \<Phi>\<Psi>'.map)
                                 (Cop_S.MkArr (Y a') (Y a) \<Phi>'\<Psi>.map)"
      proof -
        have Ya: "functor Cop.comp S (Y a)" ..
        have Ya': "functor Cop.comp S (Y a')" ..
        have \<Phi>\<Psi>': "natural_transformation Cop.comp S (Y a) (Y a') \<Phi>\<Psi>'.map" ..
        have \<Phi>'\<Psi>: "natural_transformation Cop.comp S (Y a') (Y a) \<Phi>'\<Psi>.map" ..
        show ?thesis
        proof (intro Cop_S.inverse_arrowsI)
          have 0: "inverse_transformations Cop.comp S (Y a) (Y a') \<Phi>\<Psi>'.map \<Phi>'\<Psi>.map" ..
          have 1: "Cop_S.antipar (Cop_S.MkArr (Y a) (Y a') \<Phi>\<Psi>'.map)
                                 (Cop_S.MkArr (Y a') (Y a) \<Phi>'\<Psi>.map)"
            using Ya Ya' \<Phi>\<Psi>' \<Phi>'\<Psi> Cop_S.dom_char Cop_S.cod_char Cop_S.seqI
                  Cop_S.arr_MkArr Cop_S.cod_MkArr Cop_S.dom_MkArr
            by presburger
          show "Cop_S.ide (Cop_S.comp (Cop_S.MkArr (Y a) (Y a') \<Phi>\<Psi>'.map)
                                      (Cop_S.MkArr (Y a') (Y a) \<Phi>'\<Psi>.map))"
            using 0 1 NaturalTransformation.inverse_transformations_inverse(2) Cop_S.comp_MkArr
            by (metis Cop_S.cod_MkArr Cop_S.ide_char' Cop_S.seqE)
          show "Cop_S.ide (Cop_S.comp (Cop_S.MkArr (Y a') (Y a) \<Phi>'\<Psi>.map)
                                      (Cop_S.MkArr (Y a) (Y a') \<Phi>\<Psi>'.map))"
            using 0 1 NaturalTransformation.inverse_transformations_inverse(1) Cop_S.comp_MkArr
            by (metis Cop_S.cod_MkArr Cop_S.ide_char' Cop_S.seqE)
        qed
      qed
      hence 3: "Cop_S.iso (Cop_S.MkArr (Y a) (Y a') \<Phi>\<Psi>'.map)" using Cop_S.isoI by blast
      hence "Cop_S.arr (Cop_S.MkArr (Y a) (Y a') \<Phi>\<Psi>'.map)" using Cop_S.iso_is_arr by blast
      hence "Cop_S.in_hom (Cop_S.MkArr (Y a) (Y a') \<Phi>\<Psi>'.map) (map a) (map a')"
        using Ya.ide_a Ya'.ide_a Cop_S.dom_char Cop_S.cod_char by auto
      hence "\<exists>f. \<guillemotleft>f : a \<rightarrow> a'\<guillemotright> \<and> map f = Cop_S.MkArr (Y a) (Y a') \<Phi>\<Psi>'.map"
        using Ya.ide_a Ya'.ide_a is_full Y_def Cop_S.iso_is_arr full_functor.is_full
        by auto     
      from this obtain \<phi>
        where \<phi>: "\<guillemotleft>\<phi> : a \<rightarrow> a'\<guillemotright> \<and> map \<phi> = Cop_S.MkArr (Y a) (Y a') \<Phi>\<Psi>'.map"
        by blast
      from \<phi> have "C.iso \<phi>"
        using 3 reflects_iso [of \<phi> a a'] by simp
      hence EX: "\<exists>\<phi>. \<guillemotleft>\<phi> : a \<rightarrow> a'\<guillemotright> \<and> C.iso \<phi> \<and> map \<phi> = Cop_S.MkArr (Y a) (Y a') \<Phi>\<Psi>'.map"
        using \<phi> by blast
      have
        UN: "\<And>\<phi>'. \<guillemotleft>\<phi>' : a \<rightarrow> a'\<guillemotright> \<and> map \<phi>' = Cop_S.MkArr (Y a) (Y a') \<Phi>\<Psi>'.map \<Longrightarrow> \<phi>' = \<phi>"
      proof -
        fix \<phi>'
        assume \<phi>': "\<guillemotleft>\<phi>' : a \<rightarrow> a'\<guillemotright> \<and> map \<phi>' = Cop_S.MkArr (Y a) (Y a') \<Phi>\<Psi>'.map"
        have "C.par \<phi> \<phi>' \<and> map \<phi> = map \<phi>'" using \<phi> \<phi>' by auto
        thus "\<phi>' = \<phi>" using is_faithful by fast
      qed
      from EX UN show ?thesis by auto
    qed

  end

  section "Diagrams and Cones"

  text\<open>
    A \emph{diagram} in a category @{term C} is a functor \<open>D: J \<rightarrow> C\<close>.
    We refer to the category @{term J} as the diagram \emph{shape}.
    Note that in the usual expositions of category theory that use set theory
    as their foundations, the shape @{term J} of a diagram is required to be
    a ``small'' category, where smallness means that the collection of objects
    of @{term J}, as well as each of the ``homs,'' is a set.
    However, in HOL there is no class of all sets, so it is not meaningful
    to speak of @{term J} as ``small'' in any kind of absolute sense.
    There is likely a meaningful notion of smallness of @{term J}
    \emph{relative to} @{term C} (the result below that states that a set
    category has @{term I}-indexed products if and only if its universe
    ``admits @{term I}-indexed tuples'' is suggestive of how this might
    be defined), but I haven't fully explored this idea at present.
\<close>

  locale diagram =
    C: category C +
    J: category J +
    "functor" J C D
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and C :: "'c comp"      (infixr "\<cdot>" 55)
  and D :: "'j \<Rightarrow> 'c"
  begin

    notation J.in_hom ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>J _\<guillemotright>")

  end
 
  lemma comp_diagram_functor:
  assumes "diagram J C D" and "functor J' J F"
  shows "diagram J' C (D o F)"
    by (meson assms(1) assms(2) diagram_def functor.axioms(1) functor_comp)
    
  text\<open>
    A \emph{cone} over a diagram \<open>D: J \<rightarrow> C\<close> is a natural transformation
    from a constant functor to @{term D}.  The value of the constant functor is
    the \emph{apex} of the cone.
\<close>

  locale cone =
    C: category C +
    J: category J +
    D: diagram J C D +
    A: constant_functor J C a +
    natural_transformation J C A.map D \<chi>
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and C :: "'c comp"      (infixr "\<cdot>" 55)
  and D :: "'j \<Rightarrow> 'c"
  and a :: 'c
  and \<chi> :: "'j \<Rightarrow> 'c"
  begin

    lemma ide_apex:
    shows "C.ide a"
      using A.value_is_ide by auto

    lemma component_in_hom:
    assumes "J.arr j"
    shows "\<guillemotleft>\<chi> j : a \<rightarrow> D (J.cod j)\<guillemotright>"
      using assms by auto

  end

  text\<open>
    A cone over diagram @{term D} is transformed into a cone over diagram @{term "D o F"}
    by pre-composing with @{term F}.
\<close>

  lemma comp_cone_functor:
  assumes "cone J C D a \<chi>" and "functor J' J F"
  shows "cone J' C (D o F) a (\<chi> o F)"
  proof -
    interpret \<chi>: cone J C D a \<chi> using assms(1) by auto
    interpret F: "functor" J' J F using assms(2) by auto
    interpret A': constant_functor J' C a
      apply unfold_locales using \<chi>.A.value_is_ide by auto
    have 1: "\<chi>.A.map o F = A'.map"
      using \<chi>.A.map_def A'.map_def \<chi>.J.not_arr_null by auto
    interpret \<chi>': natural_transformation J' C A'.map \<open>D o F\<close> \<open>\<chi> o F\<close>
      using 1 horizontal_composite F.natural_transformation_axioms
            \<chi>.natural_transformation_axioms
      by fastforce
    show "cone J' C (D o F) a (\<chi> o F)" ..
  qed

  text\<open>
    A cone over diagram @{term D} can be transformed into a cone over a diagram @{term D'}
    by post-composing with a natural transformation from @{term D} to @{term D'}.
\<close>

  lemma vcomp_transformation_cone:
  assumes "cone J C D a \<chi>"
  and "natural_transformation J C D D' \<tau>"
  shows "cone J C D' a (vertical_composite.map J C \<chi> \<tau>)"
  proof -
    interpret \<chi>: cone J C D a \<chi> using assms(1) by auto
    interpret \<tau>: natural_transformation J C D D' \<tau> using assms(2) by auto
    interpret \<tau>o\<chi>: vertical_composite J C \<chi>.A.map D D' \<chi> \<tau> ..
    interpret \<tau>o\<chi>: cone J C D' a \<tau>o\<chi>.map ..
    show ?thesis ..
  qed

  context "functor"
  begin

    lemma preserves_diagrams:
    fixes J :: "'j comp"
    assumes "diagram J A D"
    shows "diagram J B (F o D)"
    proof -
      interpret D: diagram J A D using assms by auto
      interpret FoD: composite_functor J A B D F ..
      show "diagram J B (F o D)" ..
    qed

    lemma preserves_cones:
    fixes J :: "'j comp"
    assumes "cone J A D a \<chi>"
    shows "cone J B (F o D) (F a) (F o \<chi>)"
    proof -
      interpret \<chi>: cone J A D a \<chi> using assms by auto
      interpret Fa: constant_functor J B \<open>F a\<close>
        apply unfold_locales using \<chi>.ide_apex by auto
      have 1: "F o \<chi>.A.map = Fa.map"
      proof
        fix f
        show "(F \<circ> \<chi>.A.map) f = Fa.map f"
          using is_extensional Fa.is_extensional \<chi>.A.is_extensional
          by (cases "\<chi>.J.arr f", simp_all)
      qed
      interpret \<chi>': natural_transformation J B Fa.map \<open>F o D\<close> \<open>F o \<chi>\<close>
        using 1 horizontal_composite \<chi>.natural_transformation_axioms
              natural_transformation_axioms
        by fastforce
      show "cone J B (F o D) (F a) (F o \<chi>)" ..
    qed

  end

  context diagram
  begin

    abbreviation cone
    where "cone a \<chi> \<equiv> Limit.cone J C D a \<chi>"

    abbreviation cones :: "'c \<Rightarrow> ('j \<Rightarrow> 'c) set"
    where "cones a \<equiv> { \<chi>. cone a \<chi> }"

    text\<open>
      An arrow @{term "f \<in> C.hom a' a"} induces by composition a transformation from
      cones with apex @{term a} to cones with apex @{term a'}.  This transformation
      is functorial in @{term f}.
\<close>

    abbreviation cones_map :: "'c \<Rightarrow> ('j \<Rightarrow> 'c) \<Rightarrow> ('j \<Rightarrow> 'c)"
    where "cones_map f \<equiv> (\<lambda>\<chi> \<in> cones (C.cod f). \<lambda>j. if J.arr j then \<chi> j \<cdot> f else C.null)"

    lemma cones_map_mapsto:
    assumes "C.arr f"
    shows "cones_map f \<in>
             extensional (cones (C.cod f)) \<inter> (cones (C.cod f) \<rightarrow> cones (C.dom f))"
    proof
      show "cones_map f \<in> extensional (cones (C.cod f))" by blast
      show "cones_map f \<in> cones (C.cod f) \<rightarrow> cones (C.dom f)"
      proof
        fix \<chi>
        assume "\<chi> \<in> cones (C.cod f)"
        hence \<chi>: "cone (C.cod f) \<chi>" by auto
        interpret \<chi>: cone J C D \<open>C.cod f\<close> \<chi> using \<chi> by auto
        interpret B: constant_functor J C \<open>C.dom f\<close>
          apply unfold_locales using assms by auto
        have "cone (C.dom f) (\<lambda>j. if J.arr j then \<chi> j \<cdot> f else C.null)"
          using assms B.value_is_ide \<chi>.is_natural_1 \<chi>.is_natural_2
          apply (unfold_locales, auto)
          using \<chi>.is_natural_1
           apply (metis C.comp_assoc)
          using \<chi>.is_natural_2 C.comp_arr_dom
          by (metis J.arr_cod_iff_arr J.cod_cod C.comp_assoc)
        thus "(\<lambda>j. if J.arr j then \<chi> j \<cdot> f else C.null) \<in> cones (C.dom f)" by auto
      qed
    qed

    lemma cones_map_ide:
    assumes "\<chi> \<in> cones a"
    shows "cones_map a \<chi> = \<chi>"
    proof -
      interpret \<chi>: cone J C D a \<chi> using assms by auto
      show ?thesis
      proof
        fix j
        show "cones_map a \<chi> j = \<chi> j"
          using assms \<chi>.A.value_is_ide \<chi>.preserves_hom C.comp_arr_dom \<chi>.is_extensional
          by (cases "J.arr j", auto)
      qed
    qed

    lemma cones_map_comp:
    assumes "C.seq f g"
    shows "cones_map (f \<cdot> g) = restrict (cones_map g o cones_map f) (cones (C.cod f))"
    proof (intro restr_eqI)
      show "cones (C.cod (f \<cdot> g)) = cones (C.cod f)" using assms by simp
      show "\<And>\<chi>. \<chi> \<in> cones (C.cod (f \<cdot> g)) \<Longrightarrow>
                  (\<lambda>j. if J.arr j then \<chi> j \<cdot> f \<cdot> g else C.null) = (cones_map g o cones_map f) \<chi>"
      proof -
        fix \<chi>
        assume \<chi>: "\<chi> \<in> cones (C.cod (f \<cdot> g))"
        show "(\<lambda>j. if J.arr j then \<chi> j \<cdot> f \<cdot> g else C.null) = (cones_map g o cones_map f) \<chi>"
        proof -
          have "((cones_map g) o (cones_map f)) \<chi> = cones_map g (cones_map f \<chi>)"
            by force
          also have "... = (\<lambda>j. if J.arr j then
                              (\<lambda>j. if J.arr j then \<chi> j \<cdot> f else C.null) j \<cdot> g else C.null)"
          proof
            fix j
            have "cone (C.dom f) (cones_map f \<chi>)"
              using assms \<chi> cones_map_mapsto by (elim C.seqE, force)
            thus "cones_map g (cones_map f \<chi>) j =
                  (if J.arr j then C (if J.arr j then \<chi> j \<cdot> f else C.null) g else C.null)"
              using \<chi> assms by auto
          qed
          also have "... = (\<lambda>j. if J.arr j then \<chi> j \<cdot> f \<cdot> g else C.null)"
          proof -
            have "\<And>j. J.arr j \<Longrightarrow> (\<chi> j \<cdot> f) \<cdot> g = \<chi> j \<cdot> f \<cdot> g"
            proof -
              interpret \<chi>: cone J C D \<open>C.cod f\<close> \<chi> using assms \<chi> by auto
              fix j
              assume j: "J.arr j"
              show "(\<chi> j \<cdot> f) \<cdot> g = \<chi> j \<cdot> f \<cdot> g"
                using assms C.comp_assoc by simp
            qed
            thus ?thesis by auto
          qed
          finally show ?thesis by auto
        qed
      qed
    qed

  end

  text\<open>
    Changing the apex of a cone by pre-composing with an arrow @{term f} commutes
    with changing the diagram of a cone by post-composing with a natural transformation.
\<close>

  lemma cones_map_vcomp:
  assumes "diagram J C D" and "diagram J C D'"
  and "natural_transformation J C D D' \<tau>"
  and "cone J C D a \<chi>"
  and f: "partial_magma.in_hom C f a' a"
  shows "diagram.cones_map J C D' f (vertical_composite.map J C \<chi> \<tau>)
           = vertical_composite.map J C (diagram.cones_map J C D f \<chi>) \<tau>"
  proof -
    interpret D: diagram J C D using assms(1) by auto
    interpret D': diagram J C D' using assms(2) by auto
    interpret \<tau>: natural_transformation J C D D' \<tau> using assms(3) by auto
    interpret \<chi>: cone J C D a \<chi> using assms(4) by auto
    interpret \<tau>o\<chi>: vertical_composite J C \<chi>.A.map D D' \<chi> \<tau> ..
    interpret \<tau>o\<chi>: cone J C D' a \<tau>o\<chi>.map ..
    interpret \<chi>f: cone J C D a' \<open>D.cones_map f \<chi>\<close>
      using f \<chi>.cone_axioms D.cones_map_mapsto by blast
    interpret \<tau>o\<chi>f: vertical_composite J C \<chi>f.A.map D D' \<open>D.cones_map f \<chi>\<close> \<tau> ..
    interpret \<tau>o\<chi>_f: cone J C D' a' \<open>D'.cones_map f \<tau>o\<chi>.map\<close>
      using f \<tau>o\<chi>.cone_axioms D'.cones_map_mapsto [of f] by blast
    write C (infixr "\<cdot>" 55)
    show "D'.cones_map f \<tau>o\<chi>.map = \<tau>o\<chi>f.map"
    proof (intro NaturalTransformation.eqI)
      show "natural_transformation J C \<chi>f.A.map D' (D'.cones_map f \<tau>o\<chi>.map)" ..
      show "natural_transformation J C \<chi>f.A.map D' \<tau>o\<chi>f.map" ..
      show "\<And>j. D.J.ide j \<Longrightarrow> D'.cones_map f \<tau>o\<chi>.map j = \<tau>o\<chi>f.map j"
      proof -
        fix j
        assume j: "D.J.ide j"
        have "D'.cones_map f \<tau>o\<chi>.map j = \<tau>o\<chi>.map j \<cdot> f"
          using f \<tau>o\<chi>.cone_axioms \<tau>o\<chi>.map_simp_2 \<tau>o\<chi>.is_extensional by auto
        also have "... = (\<tau> j \<cdot> \<chi> (D.J.dom j)) \<cdot> f"
          using j \<tau>o\<chi>.map_simp_2 by simp
        also have "... = \<tau> j \<cdot> \<chi> (D.J.dom j) \<cdot> f"
          using D.C.comp_assoc by simp
        also have "... = \<tau>o\<chi>f.map j"
          using j f \<chi>.cone_axioms \<tau>o\<chi>f.map_simp_2 by auto
        finally show "D'.cones_map f \<tau>o\<chi>.map j = \<tau>o\<chi>f.map j" by auto
      qed
    qed
  qed

  text\<open>
    Given a diagram @{term D}, we can construct a contravariant set-valued functor,
    which takes each object @{term a} of @{term C} to the set of cones over @{term D}
    with apex @{term a}, and takes each arrow @{term f} of @{term C} to the function
    on cones over @{term D} induced by pre-composition with @{term f}.
    For this, we need to introduce a set category @{term S} whose universe is large
    enough to contain all the cones over @{term D}, and we need to have an explicit
    correspondence between cones and elements of the universe of @{term S}.
    A set category @{term S} equipped with an injective mapping
    @{term_type "\<iota> :: ('j => 'c) => 's"} serves this purpose.
\<close>
  locale cones_functor =
    C: category C +
    Cop: dual_category C +
    J: category J +
    D: diagram J C D +
    S: concrete_set_category S UNIV \<iota>
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and C :: "'c comp"      (infixr "\<cdot>" 55)
  and D :: "'j \<Rightarrow> 'c"
  and S :: "'s comp"      (infixr "\<cdot>\<^sub>S" 55)
  and \<iota> :: "('j \<Rightarrow> 'c) \<Rightarrow> 's"
  begin

    notation S.in_hom     ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>S _\<guillemotright>")

    abbreviation \<o> where "\<o> \<equiv> S.\<o>"

    definition map :: "'c \<Rightarrow> 's"
    where "map = (\<lambda>f. if C.arr f then
                        S.mkArr (\<iota> ` D.cones (C.cod f)) (\<iota> ` D.cones (C.dom f))
                                (\<iota> o D.cones_map f o \<o>)
                      else S.null)"

    lemma map_simp [simp]:
    assumes "C.arr f"
    shows "map f = S.mkArr (\<iota> ` D.cones (C.cod f)) (\<iota> ` D.cones (C.dom f))
                           (\<iota> o D.cones_map f o \<o>)"
      using assms map_def by auto

    lemma arr_map:
    assumes "C.arr f"
    shows "S.arr (map f)"
    proof -
      have "\<iota> o D.cones_map f o \<o> \<in> \<iota> ` D.cones (C.cod f) \<rightarrow> \<iota> ` D.cones (C.dom f)"
        using assms D.cones_map_mapsto by force
      thus ?thesis using assms S.\<iota>_mapsto by auto
    qed

    lemma map_ide:
    assumes "C.ide a"
    shows "map a = S.mkIde (\<iota> ` D.cones a)"
    proof -
      have "map a = S.mkArr (\<iota> ` D.cones a) (\<iota> ` D.cones a) (\<iota> o D.cones_map a o \<o>)"
        using assms map_simp by force
      also have "... = S.mkArr (\<iota> ` D.cones a) (\<iota> ` D.cones a) (\<lambda>x. x)"
        using S.\<iota>_mapsto D.cones_map_ide by force
      also have "... = S.mkIde (\<iota> ` D.cones a)"
        using assms S.mkIde_as_mkArr S.\<iota>_mapsto by blast
      finally show ?thesis by auto
    qed

    lemma map_preserves_dom:
    assumes "Cop.arr f"
    shows "map (Cop.dom f) = S.dom (map f)"
      using assms arr_map map_ide by auto

    lemma map_preserves_cod:
    assumes "Cop.arr f"
    shows "map (Cop.cod f) = S.cod (map f)"
      using assms arr_map map_ide by auto

    lemma map_preserves_comp:
    assumes "Cop.seq g f"
    shows "map (g \<cdot>\<^sup>o\<^sup>p f) = map g \<cdot>\<^sub>S map f"
    proof -
      have 0: "S.seq (map g) (map f)"
        using assms arr_map [of f] arr_map [of g] map_simp
        by (intro S.seqI, auto)
      have "map (g \<cdot>\<^sup>o\<^sup>p f) = S.mkArr (\<iota> ` D.cones (C.cod f)) (\<iota> ` D.cones (C.dom g))
                                   ((\<iota> o D.cones_map g o \<o>) o (\<iota> o D.cones_map f o \<o>))"
      proof -
        have 1: "S.arr (map (g \<cdot>\<^sup>o\<^sup>p f))"
          using assms arr_map [of "C f g"] by simp
        have "map (g \<cdot>\<^sup>o\<^sup>p f) = S.mkArr (\<iota> ` D.cones (C.cod f)) (\<iota> ` D.cones (C.dom g))
                                     (\<iota> o D.cones_map (C f g) o \<o>)"
          using assms map_simp [of "C f g"] by simp
        also have "... = S.mkArr (\<iota> ` D.cones (C.cod f)) (\<iota> ` D.cones (C.dom g))
                                 ((\<iota> o D.cones_map g o \<o>) o (\<iota> o D.cones_map f o \<o>))"
          using assms 1 calculation D.cones_map_mapsto D.cones_map_comp by auto
        finally show ?thesis by blast
      qed
      also have "... = map g \<cdot>\<^sub>S map f"
        using assms 0 by (elim S.seqE, auto)
      finally show ?thesis by auto
    qed

    lemma is_functor:
    shows "functor Cop.comp S map"
      apply (unfold_locales)
      using map_def arr_map map_preserves_dom map_preserves_cod map_preserves_comp
      by auto
    
  end

  sublocale cones_functor \<subseteq> "functor" Cop.comp S map using is_functor by auto
  sublocale cones_functor \<subseteq> set_valued_functor Cop.comp S map ..

  section Limits

  subsection "Limit Cones"

  text\<open>
    A \emph{limit cone} for a diagram @{term D} is a cone @{term \<chi>} over @{term D}
    with the universal property that any other cone @{term \<chi>'} over the diagram @{term D}
    factors uniquely through @{term \<chi>}.
\<close>

  locale limit_cone =
    C: category C +
    J: category J +
    D: diagram J C D +
    cone J C D a \<chi>
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and C :: "'c comp"      (infixr "\<cdot>" 55)
  and D :: "'j \<Rightarrow> 'c"
  and a :: 'c
  and \<chi> :: "'j \<Rightarrow> 'c" +
  assumes is_universal: "cone J C D a' \<chi>' \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = \<chi>'"
  begin

    definition induced_arrow :: "'c \<Rightarrow> ('j \<Rightarrow> 'c) \<Rightarrow> 'c"
    where "induced_arrow a' \<chi>' = (THE f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = \<chi>')"

    lemma induced_arrowI:
    assumes \<chi>': "\<chi>' \<in> D.cones a'"
    shows "\<guillemotleft>induced_arrow a' \<chi>' : a' \<rightarrow> a\<guillemotright>"
    and "D.cones_map (induced_arrow a' \<chi>') \<chi> = \<chi>'"
    proof -
      have "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = \<chi>'"
        using assms \<chi>' is_universal by simp
      hence 1: "\<guillemotleft>induced_arrow a' \<chi>' : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map (induced_arrow a' \<chi>') \<chi> = \<chi>'"
        using theI' [of "\<lambda>f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = \<chi>'"] induced_arrow_def
        by presburger
      show "\<guillemotleft>induced_arrow a' \<chi>' : a' \<rightarrow> a\<guillemotright>" using 1 by simp
      show "D.cones_map (induced_arrow a' \<chi>') \<chi> = \<chi>'" using 1 by simp
    qed

    lemma cones_map_induced_arrow:
    shows "induced_arrow a' \<in> D.cones a' \<rightarrow> C.hom a' a"
    and "\<And>\<chi>'. \<chi>' \<in> D.cones a' \<Longrightarrow> D.cones_map (induced_arrow a' \<chi>') \<chi> = \<chi>'"
      using induced_arrowI by auto

    lemma induced_arrow_cones_map:
    assumes "C.ide a'"
    shows "(\<lambda>f. D.cones_map f \<chi>) \<in> C.hom a' a \<rightarrow> D.cones a'"
    and "\<And>f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<Longrightarrow> induced_arrow a' (D.cones_map f \<chi>) = f"
    proof -
      have a': "C.ide a'" using assms by (simp add: cone.ide_apex)
      have cone_\<chi>: "cone J C D a \<chi>" ..
      show "(\<lambda>f. D.cones_map f \<chi>) \<in> C.hom a' a \<rightarrow> D.cones a'"
        using cone_\<chi> D.cones_map_mapsto by blast
      fix f
      assume f: "\<guillemotleft>f : a' \<rightarrow> a\<guillemotright>"
      show "induced_arrow a' (D.cones_map f \<chi>) = f"
      proof -
        have "D.cones_map f \<chi> \<in> D.cones a'"
          using f cone_\<chi> D.cones_map_mapsto by blast
        hence "\<exists>!f'. \<guillemotleft>f' : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f' \<chi> = D.cones_map f \<chi>"
          using assms is_universal by auto
        thus ?thesis
          using f induced_arrow_def
                the1_equality [of "\<lambda>f'. \<guillemotleft>f' : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f' \<chi> = D.cones_map f \<chi>"]
          by presburger
      qed
    qed

    text\<open>
      For a limit cone @{term \<chi>} with apex @{term a}, for each object @{term a'} the
      hom-set @{term "C.hom a' a"} is in bijective correspondence with the set of cones
      with apex @{term a'}.
\<close>

    lemma bij_betw_hom_and_cones:
    assumes "C.ide a'"
    shows "bij_betw (\<lambda>f. D.cones_map f \<chi>) (C.hom a' a) (D.cones a')"
    proof (intro bij_betwI)
      show "(\<lambda>f. D.cones_map f \<chi>) \<in> C.hom a' a \<rightarrow> D.cones a'"
        using assms induced_arrow_cones_map by blast
      show "induced_arrow a' \<in> D.cones a' \<rightarrow> C.hom a' a"
        using assms cones_map_induced_arrow by blast
      show "\<And>f. f \<in> C.hom a' a \<Longrightarrow> induced_arrow a' (D.cones_map f \<chi>) = f"
        using assms induced_arrow_cones_map by blast
      show "\<And>\<chi>'. \<chi>' \<in> D.cones a' \<Longrightarrow> D.cones_map (induced_arrow a' \<chi>') \<chi> = \<chi>'"
        using assms cones_map_induced_arrow by blast
    qed

    lemma induced_arrow_eqI:
    assumes "D.cone a' \<chi>'" and "\<guillemotleft>f : a' \<rightarrow> a\<guillemotright>" and "D.cones_map f \<chi> = \<chi>'"
    shows "induced_arrow a' \<chi>' = f"
      using assms is_universal induced_arrow_def
            the1_equality [of "\<lambda>f. f \<in> C.hom a' a \<and> D.cones_map f \<chi> = \<chi>'" f]
      by simp

    lemma induced_arrow_self:
    shows "induced_arrow a \<chi> = a"
    proof -
      have "\<guillemotleft>a : a \<rightarrow> a\<guillemotright> \<and> D.cones_map a \<chi> = \<chi>"
        using ide_apex cone_axioms D.cones_map_ide by force
      thus ?thesis using induced_arrow_eqI cone_axioms by auto
    qed

  end

  context diagram
  begin

    abbreviation limit_cone
    where "limit_cone a \<chi> \<equiv> Limit.limit_cone J C D a \<chi>"

    text\<open>
      A diagram @{term D} has object @{term a} as a limit if @{term a} is the apex
      of some limit cone over @{term D}.
\<close>

    abbreviation has_as_limit :: "'c \<Rightarrow> bool"
    where "has_as_limit a \<equiv> (\<exists>\<chi>. limit_cone a \<chi>)"

    abbreviation has_limit
    where "has_limit \<equiv> (\<exists>a \<chi>. limit_cone a \<chi>)"

    definition some_limit :: 'c
    where "some_limit = (SOME a. \<exists>\<chi>. limit_cone a \<chi>)"

    definition some_limit_cone :: "'j \<Rightarrow> 'c"
    where "some_limit_cone = (SOME \<chi>. limit_cone some_limit \<chi>)"

    lemma limit_cone_some_limit_cone:
    assumes has_limit
    shows "limit_cone some_limit some_limit_cone"
    proof -
      have "\<exists>a. has_as_limit a" using assms by simp
      hence "has_as_limit some_limit"
        using some_limit_def someI_ex [of "\<lambda>a. \<exists>\<chi>. limit_cone a \<chi>"] by simp
      thus "limit_cone some_limit some_limit_cone"
        using assms some_limit_cone_def someI_ex [of "\<lambda>\<chi>. limit_cone some_limit \<chi>"]
        by simp
    qed

    lemma ex_limitE:
    assumes "\<exists>a. has_as_limit a"
    obtains a \<chi> where "limit_cone a \<chi>"
      using assms someI_ex by blast

  end

  subsection "Limits by Representation"

  text\<open>
    A limit for a diagram D can also be given by a representation \<open>(a, \<Phi>)\<close>
    of the cones functor.
\<close>

  locale representation_of_cones_functor =
    C: category C +
    Cop: dual_category C +
    J: category J +
    D: diagram J C D +
    S: concrete_set_category S UNIV \<iota> +
    Cones: cones_functor J C D S \<iota> +
    Hom: hom_functor C S \<phi> +
    representation_of_functor C S \<phi> Cones.map a \<Phi>
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and C :: "'c comp"      (infixr "\<cdot>" 55)
  and D :: "'j \<Rightarrow> 'c"
  and S :: "'s comp"      (infixr "\<cdot>\<^sub>S" 55)
  and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
  and \<iota> :: "('j \<Rightarrow> 'c) \<Rightarrow> 's"
  and a :: 'c
  and \<Phi> :: "'c \<Rightarrow> 's"

  subsection "Putting it all Together"

  text\<open>
    A ``limit situation'' combines and connects the ways of presenting a limit.
\<close>

  locale limit_situation =
    C: category C +
    Cop: dual_category C +
    J: category J +
    D: diagram J C D +
    S: concrete_set_category S UNIV \<iota> +
    Cones: cones_functor J C D S \<iota> +
    Hom: hom_functor C S \<phi> +
    \<Phi>: representation_of_functor C S \<phi> Cones.map a \<Phi> +
    \<chi>: limit_cone J C D a \<chi>
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and C :: "'c comp"      (infixr "\<cdot>" 55)
  and D :: "'j \<Rightarrow> 'c"
  and S :: "'s comp"      (infixr "\<cdot>\<^sub>S" 55)
  and \<phi> :: "'c * 'c \<Rightarrow> 'c \<Rightarrow> 's"
  and \<iota> :: "('j \<Rightarrow> 'c) \<Rightarrow> 's"
  and a :: 'c
  and \<Phi> :: "'c \<Rightarrow> 's"
  and \<chi> :: "'j \<Rightarrow> 'c" +
  assumes \<chi>_in_terms_of_\<Phi>: "\<chi> = S.\<o> (S.Fun (\<Phi> a) (\<phi> (a, a) a))"
  and \<Phi>_in_terms_of_\<chi>:
     "Cop.ide a' \<Longrightarrow> \<Phi> a' = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a')
                                    (\<lambda>x. \<iota> (D.cones_map (Hom.\<psi> (a', a) x) \<chi>))"

  text (in limit_situation) \<open>
    The assumption @{prop \<chi>_in_terms_of_\<Phi>} states that the universal cone @{term \<chi>} is obtained
    by applying the function @{term "S.Fun (\<Phi> a)"} to the identity @{term a} of
    @{term[source=true] C} (after taking into account the necessary coercions).
\<close>

  text (in limit_situation) \<open>
    The assumption @{prop \<Phi>_in_terms_of_\<chi>} states that the component of @{term \<Phi>} at @{term a'}
    is the arrow of @{term[source=true] S} corresponding to the function that takes an arrow
    @{term "f \<in> C.hom a' a"} and produces the cone with vertex @{term a'} obtained
    by transforming the universal cone @{term \<chi>} by @{term f}.
\<close>

  subsection "Limit Cones Induce Limit Situations"

  text\<open>
    To obtain a limit situation from a limit cone, we need to introduce a set category
    that is large enough to contain the hom-sets of @{term C} as well as the cones
    over @{term D}.  We use the category of @{typ "('c + ('j \<Rightarrow> 'c))"}-sets for this.
\<close>

  context limit_cone
  begin

    interpretation Cop: dual_category C ..
    interpretation CopxC: product_category Cop.comp C ..
    interpretation S: set_category \<open>SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) setcat.arr comp\<close>
      using SetCat.is_set_category by auto

    interpretation S: concrete_set_category \<open>SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) setcat.arr comp\<close>
                                            UNIV \<open>UP o Inr\<close>
      apply unfold_locales
      using UP_mapsto
       apply auto[1]
      using inj_UP inj_Inr inj_compose
      by metis

    notation SetCat.comp      (infixr "\<cdot>\<^sub>S" 55)

    interpretation Cones: cones_functor J C D \<open>SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) setcat.arr comp\<close>
                                        \<open>UP o Inr\<close> ..

    interpretation Hom: hom_functor C \<open>SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) setcat.arr comp\<close>
                                      \<open>\<lambda>_. UP o Inl\<close>
      apply (unfold_locales)
      using UP_mapsto
       apply auto[1]
      using SetCat.inj_UP injD inj_onI inj_Inl inj_compose
      by (metis (no_types, lifting))

    interpretation Y: yoneda_functor C \<open>SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) setcat.arr comp\<close>
                                     \<open>\<lambda>_. UP o Inl\<close> ..
    interpretation Ya: yoneda_functor_fixed_object
                         C \<open>SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) setcat.arr comp\<close>
                         \<open>\<lambda>_. UP o Inl\<close> a
      apply (unfold_locales) using ide_apex by auto

    abbreviation inl :: "'c \<Rightarrow> 'c + ('j \<Rightarrow> 'c)" where "inl \<equiv> Inl"
    abbreviation inr :: "('j \<Rightarrow> 'c) \<Rightarrow> 'c + ('j \<Rightarrow> 'c)" where "inr \<equiv> Inr"
    abbreviation \<iota> where "\<iota> \<equiv> UP o inr"
    abbreviation \<o> where "\<o> \<equiv> Cones.\<o>"
    abbreviation \<phi> where "\<phi> \<equiv> \<lambda>_. UP o inl"
    abbreviation \<psi> where "\<psi> \<equiv> Hom.\<psi>"
    abbreviation Y where "Y \<equiv> Y.Y"

    lemma Ya_ide:
    assumes a': "C.ide a'"
    shows "Y a a' = S.mkIde (Hom.set (a', a))"
      using assms ide_apex Y.Y_simp Hom.map_ide by simp

    lemma Ya_arr:
    assumes g: "C.arr g"
    shows "Y a g = S.mkArr (Hom.set (C.cod g, a)) (Hom.set (C.dom g, a))
                           (\<phi> (C.dom g, a) o Cop.comp g o \<psi> (C.cod g, a))"
      using ide_apex g Y.Y_ide_arr [of a g "C.dom g" "C.cod g"] by auto

    lemma cone_\<chi> [simp]:
    shows "\<chi> \<in> D.cones a"
      using cone_axioms by simp
    
    text\<open>
      For each object @{term a'} of @{term[source=true] C} we have a function mapping
      @{term "C.hom a' a"} to the set of cones over @{term D} with apex @{term a'},
      which takes @{term "f \<in> C.hom a' a"} to \<open>\<chi>f\<close>, where \<open>\<chi>f\<close> is the cone obtained by
      composing @{term \<chi>} with @{term f} (after accounting for coercions to and from the
      universe of @{term S}).  The corresponding arrows of @{term S} are the
      components of a natural isomorphism from @{term "Y a"} to \<open>Cones\<close>.
\<close>

    definition \<Phi>o :: "'c \<Rightarrow> ('c + ('j \<Rightarrow> 'c)) setcat.arr"
    where
      "\<Phi>o a' = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') (\<lambda>x. \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>))"

    lemma \<Phi>o_in_hom:
    assumes a': "C.ide a'"
    shows "\<guillemotleft>\<Phi>o a' : S.mkIde (Hom.set (a', a)) \<rightarrow>\<^sub>S S.mkIde (\<iota> ` D.cones a')\<guillemotright>"
    proof -
      have " \<guillemotleft>S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') (\<lambda>x. \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)) :
                 S.mkIde (Hom.set (a', a)) \<rightarrow>\<^sub>S S.mkIde (\<iota> ` D.cones a')\<guillemotright>"
      proof -
        have "(\<lambda>x. \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)) \<in> Hom.set (a', a) \<rightarrow> \<iota> ` D.cones a'"
        proof
          fix x
          assume x: "x \<in> Hom.set (a', a)"
          hence "\<guillemotleft>\<psi> (a', a) x : a' \<rightarrow> a\<guillemotright>"
            using ide_apex a' Hom.\<psi>_mapsto by auto
          hence "D.cones_map (\<psi> (a', a) x) \<chi> \<in> D.cones a'"
            using ide_apex a' x D.cones_map_mapsto cone_\<chi> by force
          thus "\<iota> (D.cones_map (\<psi> (a', a) x) \<chi>) \<in> \<iota> ` D.cones a'" by simp
        qed
        moreover have "Hom.set (a', a) \<subseteq> S.Univ"
          using ide_apex a' Hom.set_subset_Univ by auto
        moreover have "\<iota> ` D.cones a' \<subseteq> S.Univ"
          using UP_mapsto by auto
        ultimately show ?thesis using S.mkArr_in_hom by simp
      qed
      thus ?thesis using \<Phi>o_def [of a'] by auto
    qed

    interpretation \<Phi>: transformation_by_components
                        Cop.comp SetCat.comp \<open>Y a\<close> Cones.map \<Phi>o
    proof
      fix a'
      assume A': "Cop.ide a'"
      show "\<guillemotleft>\<Phi>o a' : Y a a' \<rightarrow>\<^sub>S Cones.map a'\<guillemotright>"
        using A' Ya_ide \<Phi>o_in_hom Cones.map_ide by auto
      next
      fix g
      assume g: "Cop.arr g"
      show "\<Phi>o (Cop.cod g) \<cdot>\<^sub>S Y a g = Cones.map g \<cdot>\<^sub>S \<Phi>o (Cop.dom g)"
      proof -
        let ?A = "Hom.set (C.cod g, a)"
        let ?B = "Hom.set (C.dom g, a)"
        let ?B' = "\<iota> ` D.cones (C.cod g)"
        let ?C = "\<iota> ` D.cones (C.dom g)"
        let ?F = "\<phi> (C.dom g, a) o Cop.comp g o \<psi> (C.cod g, a)"
        let ?F' = "\<iota> o D.cones_map g o \<o>"
        let ?G = "\<lambda>x. \<iota> (D.cones_map (\<psi> (C.dom g, a) x) \<chi>)"
        let ?G' = "\<lambda>x. \<iota> (D.cones_map (\<psi> (C.cod g, a) x) \<chi>)"
        have "S.arr (Y a g) \<and> Y a g = S.mkArr ?A ?B ?F"
          using ide_apex g Ya.preserves_arr Ya_arr by fastforce
        moreover have "S.arr (\<Phi>o (Cop.cod g))"
          using g \<Phi>o_in_hom [of "Cop.cod g"] by auto
        moreover have "\<Phi>o (Cop.cod g) = S.mkArr ?B ?C ?G"
          using g \<Phi>o_def [of "C.dom g"] by auto
        moreover have "S.seq (\<Phi>o (Cop.cod g)) (Y a g)"
          using ide_apex g \<Phi>o_in_hom [of "Cop.cod g"] by auto
        ultimately have 1: "S.seq (\<Phi>o (Cop.cod g)) (Y a g) \<and>
                            \<Phi>o (Cop.cod g) \<cdot>\<^sub>S Y a g = S.mkArr ?A ?C (?G o ?F)"
          using S.comp_mkArr [of ?A ?B ?F ?C ?G] by argo

        have "Cones.map g = S.mkArr (\<iota> ` D.cones (C.cod g)) (\<iota> ` D.cones (C.dom g)) ?F'"
          using g Cones.map_simp by fastforce
        moreover have "\<Phi>o (Cop.dom g) = S.mkArr ?A ?B' ?G'"
          using g \<Phi>o_def by fastforce
        moreover have "S.seq (Cones.map g) (\<Phi>o (Cop.dom g))"
          using g Cones.preserves_hom [of g "C.cod g" "C.dom g"] \<Phi>o_in_hom [of "Cop.dom g"]
          by force
        ultimately have
          2: "S.seq (Cones.map g) (\<Phi>o (Cop.dom g)) \<and>
              Cones.map g \<cdot>\<^sub>S \<Phi>o (Cop.dom g) = S.mkArr ?A ?C (?F' o ?G')"
          using S.seqI' [of "\<Phi>o (Cop.dom g)" "Cones.map g"] by force

        have "\<Phi>o (Cop.cod g) \<cdot>\<^sub>S Y a g = S.mkArr ?A ?C (?G o ?F)"
          using 1 by auto
        also have "... = S.mkArr ?A ?C (?F' o ?G')"
        proof (intro S.mkArr_eqI')
          show "S.arr (S.mkArr ?A ?C (?G o ?F))" using 1 by force
          show "\<And>x. x \<in> ?A \<Longrightarrow> (?G o ?F) x = (?F' o ?G') x"
          proof -
            fix x
            assume x: "x \<in> ?A"
            hence 1: "\<guillemotleft>\<psi> (C.cod g, a) x : C.cod g \<rightarrow> a\<guillemotright>"
              using ide_apex g Hom.\<psi>_mapsto [of "C.cod g" a] by auto
            have "(?G o ?F) x = \<iota> (D.cones_map (\<psi> (C.dom g, a)
                                  (\<phi> (C.dom g, a) (\<psi> (C.cod g, a) x \<cdot> g))) \<chi>)"
            proof - (* Why is it so balky with this proof? *)
              have "(?G o ?F) x = ?G (?F x)" by simp
              also have "... = \<iota> (D.cones_map (\<psi> (C.dom g, a)
                                     (\<phi> (C.dom g, a) (\<psi> (C.cod g, a) x \<cdot> g))) \<chi>)"
              proof -
                have "?F x = \<phi> (C.dom g, a) (\<psi> (C.cod g, a) x \<cdot> g)" by simp
                thus ?thesis by presburger (* presburger 5ms, metis 797ms! Why? *)
              qed
              finally show ?thesis by auto
            qed
            also have "... = \<iota> (D.cones_map (\<psi> (C.cod g, a) x \<cdot> g) \<chi>)"
            proof -
              have "\<guillemotleft>\<psi> (C.cod g, a) x \<cdot> g : C.dom g \<rightarrow> a\<guillemotright>" using g 1 by auto
              thus ?thesis using Hom.\<psi>_\<phi> by presburger
            qed
            also have "... = \<iota> (D.cones_map g (D.cones_map (\<psi> (C.cod g, a) x) \<chi>))"
              using g x 1 cone_\<chi> D.cones_map_comp [of "\<psi> (C.cod g, a) x" g] by fastforce
            also have "... = \<iota> (D.cones_map g (\<o> (\<iota> (D.cones_map (\<psi> (C.cod g, a) x) \<chi>))))"
              using 1 cone_\<chi> D.cones_map_mapsto S.\<o>_\<iota> by simp
            also have "... = (?F' o ?G') x" by simp
            finally show "(?G o ?F) x = (?F' o ?G') x" by auto
          qed
        qed
        also have "... = Cones.map g \<cdot>\<^sub>S \<Phi>o (Cop.dom g)"
          using 2 by auto
       finally show ?thesis by auto
      qed
    qed

    interpretation \<Phi>: set_valued_transformation
                        Cop.comp SetCat.comp \<open>Y a\<close> Cones.map \<Phi>.map ..
                                            
    interpretation \<Phi>: natural_isomorphism Cop.comp SetCat.comp \<open>Y a\<close> Cones.map \<Phi>.map
    proof
      fix a'
      assume a': "Cop.ide a'"
      show "S.iso (\<Phi>.map a')"
      proof -
        let ?F = "\<lambda>x. \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
        have bij: "bij_betw ?F (Hom.set (a', a)) (\<iota> ` D.cones a')"
        proof -
          have "\<And>x x'. \<lbrakk> x \<in> Hom.set (a', a); x' \<in> Hom.set (a', a);
                         \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x') \<chi>) \<rbrakk>
                            \<Longrightarrow> x = x'"
          proof -
            fix x x'
            assume x: "x \<in> Hom.set (a', a)" and x': "x' \<in> Hom.set (a', a)"
            and xx': "\<iota> (D.cones_map (\<psi> (a', a) x) \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x') \<chi>)"
            have \<psi>x: "\<guillemotleft>\<psi> (a', a) x : a' \<rightarrow> a\<guillemotright>" using x ide_apex a' Hom.\<psi>_mapsto by auto
            have \<psi>x': "\<guillemotleft>\<psi> (a', a) x' : a' \<rightarrow> a\<guillemotright>" using x' ide_apex a' Hom.\<psi>_mapsto by auto
            have 1: "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> \<iota> (D.cones_map f \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
            proof -
              have "D.cones_map (\<psi> (a', a) x) \<chi> \<in> D.cones a'"
                using \<psi>x a' cone_\<chi> D.cones_map_mapsto by force
              hence 2: "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = D.cones_map (\<psi> (a', a) x) \<chi>"
                using a' is_universal by simp
              show "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> \<iota> (D.cones_map f \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
              proof -
                have "\<And>f. \<iota> (D.cones_map f \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)
                             \<longleftrightarrow> D.cones_map f \<chi> = D.cones_map (\<psi> (a', a) x) \<chi>"
                proof -
                  fix f :: 'c
                  have "D.cones_map f \<chi> = D.cones_map (\<psi> (a', a) x) \<chi>
                           \<longrightarrow> \<iota> (D.cones_map f \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
                    by simp
                  thus "(\<iota> (D.cones_map f \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>))
                            = (D.cones_map f \<chi> = D.cones_map (\<psi> (a', a) x) \<chi>)"
                    by (meson S.inj_\<iota> injD)
                qed
                thus ?thesis using 2 by auto
              qed
            qed
            have 2: "\<exists>!x''. x'' \<in> Hom.set (a', a) \<and>
                            \<iota> (D.cones_map (\<psi> (a', a) x'') \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
            proof -
              from 1 obtain f'' where
                  f'': "\<guillemotleft>f'' : a' \<rightarrow> a\<guillemotright> \<and> \<iota> (D.cones_map f'' \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
                by blast
              have "\<phi> (a', a) f'' \<in> Hom.set (a', a) \<and>
                    \<iota> (D.cones_map (\<psi> (a', a) (\<phi> (a', a) f'')) \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
              proof
                show "\<phi> (a', a) f'' \<in> Hom.set (a', a)" using f'' Hom.set_def by auto
                show "\<iota> (D.cones_map (\<psi> (a', a) (\<phi> (a', a) f'')) \<chi>) =
                         \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
                  using f'' Hom.\<psi>_\<phi> by presburger
              qed
              moreover have
                 "\<And>x''. x'' \<in> Hom.set (a', a) \<and>
                         \<iota> (D.cones_map (\<psi> (a', a) x'') \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)
                             \<Longrightarrow> x'' = \<phi> (a', a) f''"
              proof -
                fix x''
                assume x'': "x'' \<in> Hom.set (a', a) \<and>
                             \<iota> (D.cones_map (\<psi> (a', a) x'') \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
                hence "\<guillemotleft>\<psi> (a', a) x'' : a' \<rightarrow> a\<guillemotright> \<and>
                       \<iota> (D.cones_map (\<psi> (a', a) x'') \<chi>) = \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
                  using ide_apex a' Hom.set_def Hom.\<psi>_mapsto [of a' a] by auto
                hence "\<phi> (a', a) (\<psi> (a', a) x'') = \<phi> (a', a) f''"
                  using 1 f'' by auto
                thus "x'' = \<phi> (a', a) f''"
                  using ide_apex a' x'' Hom.\<phi>_\<psi> by simp
              qed
              ultimately show ?thesis
                using ex1I [of "\<lambda>x'. x' \<in> Hom.set (a', a) \<and>
                                     \<iota> (D.cones_map (\<psi> (a', a) x') \<chi>) =
                                        \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
                               "\<phi> (a', a) f''"]
                by simp
            qed
            thus "x = x'" using x x' xx' by auto
          qed
          hence "inj_on ?F (Hom.set (a', a))"
            using inj_onI [of "Hom.set (a', a)" ?F] by auto 
          moreover have "?F ` Hom.set (a', a) = \<iota> ` D.cones a'"
          proof
            show "?F ` Hom.set (a', a) \<subseteq> \<iota> ` D.cones a'"
            proof
              fix X'
              assume X': "X' \<in> ?F ` Hom.set (a', a)"
              from this obtain x' where x': "x' \<in> Hom.set (a', a) \<and> ?F x' = X'" by blast
              show "X' \<in> \<iota> ` D.cones a'"
              proof -
                have "X' = \<iota> (D.cones_map (\<psi> (a', a) x') \<chi>)" using x' by blast
                hence "X' = \<iota> (D.cones_map (\<psi> (a', a) x') \<chi>)" using x' by force
                moreover have "\<guillemotleft>\<psi> (a', a) x' : a' \<rightarrow> a\<guillemotright>"
                  using ide_apex a' x' Hom.set_def Hom.\<psi>_\<phi> by auto
                ultimately show ?thesis
                  using x' cone_\<chi> D.cones_map_mapsto by force
              qed
            qed
            show "\<iota> ` D.cones a' \<subseteq> ?F ` Hom.set (a', a)"
            proof
              fix X'
              assume X': "X' \<in> \<iota> ` D.cones a'"
              hence "\<o> X' \<in> \<o> ` \<iota> ` D.cones a'" by simp
              with S.\<o>_\<iota> have "\<o> X' \<in> D.cones a'"
                by auto
              hence "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = \<o> X'"
                using a' is_universal by simp
              from this obtain f where "\<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = \<o> X'"
                by auto
              hence f: "\<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> \<iota> (D.cones_map f \<chi>) = X'"
                using X' S.\<iota>_\<o> by auto
              have "X' = ?F (\<phi> (a', a) f)"
                using f Hom.\<psi>_\<phi> by presburger
              thus "X' \<in> ?F ` Hom.set (a', a)"
                using f Hom.set_def by force
            qed
          qed
          ultimately show ?thesis
            using bij_betw_def [of ?F "Hom.set (a', a)" "\<iota> ` D.cones a'"] inj_on_def by auto
        qed
        let ?f = "S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') ?F"
        have iso: "S.iso ?f"
        proof -
          have "?F \<in> Hom.set (a', a) \<rightarrow> \<iota> ` D.cones a'"
            using bij bij_betw_imp_funcset by fast
          hence "S.arr ?f"
            using ide_apex a' Hom.set_subset_Univ S.\<iota>_mapsto S.arr_mkArr by auto
          thus ?thesis using bij S.iso_char by fastforce
        qed
        moreover have "?f = \<Phi>.map a'"
          using a' \<Phi>o_def by force
        finally show ?thesis by auto
      qed
    qed

    interpretation R: representation_of_functor
                         C \<open>SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) setcat.arr comp\<close>
                         \<phi> Cones.map a \<Phi>.map ..

    lemma \<chi>_in_terms_of_\<Phi>:
    shows "\<chi> = \<o> (\<Phi>.FUN a (\<phi> (a, a) a))"
    proof -
      have "\<Phi>.FUN a (\<phi> (a, a) a) = 
              (\<lambda>x \<in> Hom.set (a, a). \<iota> (D.cones_map (\<psi> (a, a) x) \<chi>)) (\<phi> (a, a) a)"
        using ide_apex S.Fun_mkArr \<Phi>.map_simp_ide \<Phi>o_def \<Phi>.preserves_reflects_arr [of a]
        by simp
      also have "... = \<iota> (D.cones_map a \<chi>)"
      proof -
        have "\<phi> (a, a) a \<in> Hom.set (a, a)"
          using ide_apex Hom.\<phi>_mapsto by fastforce
        hence "(\<lambda>x \<in> Hom.set (a, a). \<iota> (D.cones_map (\<psi> (a, a) x) \<chi>)) (\<phi> (a, a) a)
                  = \<iota> (D.cones_map (\<psi> (a, a) (\<phi> (a, a) a)) \<chi>)"
          using restrict_apply' [of "\<phi> (a, a) a" "Hom.set (a, a)"] by blast
        also have "... = \<iota> (D.cones_map a \<chi>)"
        proof -
          have "\<psi> (a, a) (\<phi> (a, a) a) = a"
            using ide_apex Hom.\<psi>_\<phi> [of a a a] by fastforce
          thus ?thesis by metis
        qed
        finally show ?thesis by auto
      qed
      finally have "\<Phi>.FUN a (\<phi> (a, a) a) = \<iota> (D.cones_map a \<chi>)" by auto
      also have "... = \<iota> \<chi>"
        using ide_apex D.cones_map_ide [of \<chi> a] cone_\<chi> by simp
      finally have "\<Phi>.FUN a (\<phi> (a, a) a) = \<iota> \<chi>" by blast
      hence "\<o> (\<Phi>.FUN a (\<phi> (a, a) a)) = \<o> (\<iota> \<chi>)" by simp
      thus ?thesis using cone_\<chi> S.\<o>_\<iota> by simp
    qed

    abbreviation Hom
    where "Hom \<equiv> Hom.map"

    abbreviation \<Phi>
    where "\<Phi> \<equiv> \<Phi>.map"

    lemma induces_limit_situation:
    shows "limit_situation J C D (SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) setcat.arr comp) \<phi> \<iota> a \<Phi> \<chi>"
    proof
      show "\<chi> = \<o> (\<Phi>.FUN a (\<phi> (a, a) a))" using \<chi>_in_terms_of_\<Phi> by auto
      fix a'
      show "Cop.ide a' \<Longrightarrow> \<Phi>.map a' = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a')
                                              (\<lambda>x. \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>))"
        using \<Phi>.map_simp_ide \<Phi>o_def [of a'] by force
    qed

    no_notation SetCat.comp      (infixr "\<cdot>\<^sub>S" 55)

  end

  sublocale limit_cone \<subseteq> limit_situation J C D "SetCat.comp :: ('c + ('j \<Rightarrow> 'c)) setcat.arr comp"
                                         \<phi> \<iota> a \<Phi> \<chi>
    using induces_limit_situation by auto

  subsection "Representations of the Cones Functor Induce Limit Situations"

  context representation_of_cones_functor
  begin

    interpretation \<Phi>: set_valued_transformation Cop.comp S \<open>Y a\<close> Cones.map \<Phi> ..
    interpretation \<Psi>: inverse_transformation Cop.comp S \<open>Y a\<close> Cones.map \<Phi> ..
    interpretation \<Psi>: set_valued_transformation Cop.comp S Cones.map \<open>Y a\<close> \<Psi>.map ..

    abbreviation \<o>
    where "\<o> \<equiv> Cones.\<o>"

    abbreviation \<chi>
    where "\<chi> \<equiv> \<o> (S.Fun (\<Phi> a) (\<phi> (a, a) a))"

    lemma Cones_SET_eq_\<iota>_img_cones:
    assumes "C.ide a'"
    shows "Cones.SET a' = \<iota> ` D.cones a'"
    proof -
      have "\<iota> ` D.cones a' \<subseteq> S.Univ" using S.\<iota>_mapsto by auto
      thus ?thesis using assms Cones.map_ide by auto
    qed

    lemma \<iota>\<chi>:
    shows "\<iota> \<chi> = S.Fun (\<Phi> a) (\<phi> (a, a) a)"
    proof -
      have "S.Fun (\<Phi> a) (\<phi> (a, a) a) \<in> Cones.SET a"
        using Ya.ide_a Hom.\<phi>_mapsto S.Fun_mapsto [of "\<Phi> a"] Hom.set_map by fastforce
      thus ?thesis
        using Ya.ide_a Cones_SET_eq_\<iota>_img_cones by auto
    qed

    interpretation \<chi>: cone J C D a \<chi>
    proof -
      have "\<iota> \<chi> \<in> \<iota> ` D.cones a"
        using Ya.ide_a \<iota>\<chi> S.Fun_mapsto [of "\<Phi> a"] Hom.\<phi>_mapsto Hom.set_map
              Cones_SET_eq_\<iota>_img_cones by fastforce
      thus "D.cone a \<chi>"
        by (metis S.\<o>_\<iota> UNIV_I imageE mem_Collect_eq)
    qed

    lemma cone_\<chi>:
    shows "D.cone a \<chi>" ..

    lemma \<Phi>_FUN_simp:
    assumes a': "C.ide a'" and x: "x \<in> Hom.set (a', a)"
    shows "\<Phi>.FUN a' x = Cones.FUN (\<psi> (a', a) x) (\<iota> \<chi>)"
    proof -
      have \<psi>x: "\<guillemotleft>\<psi> (a', a) x : a' \<rightarrow> a\<guillemotright>"
        using Ya.ide_a a' x Hom.\<psi>_mapsto by blast
      have \<phi>a: "\<phi> (a, a) a \<in> Hom.set (a, a)" using Ya.ide_a Hom.\<phi>_mapsto by fastforce
      have "\<Phi>.FUN a' x = (\<Phi>.FUN a' o Ya.FUN (\<psi> (a', a) x)) (\<phi> (a, a) a)"
      proof -
        have "\<phi> (a', a) (a \<cdot> \<psi> (a', a) x) = x"
          using Ya.ide_a a' x \<psi>x Hom.\<phi>_\<psi> C.comp_cod_arr by fastforce
        moreover have "S.arr (S.mkArr (Hom.set (a, a)) (Hom.set (a', a))
                             (\<phi> (a', a) \<circ> Cop.comp (\<psi> (a', a) x) \<circ> \<psi> (a, a)))"
          using Ya.ide_a a' Hom.set_subset_Univ Hom.\<psi>_mapsto [of a a] Hom.\<phi>_mapsto \<psi>x
          by force
        ultimately show ?thesis
          using Ya.ide_a a' x Ya.Y_ide_arr \<psi>x \<phi>a C.ide_in_hom by auto
      qed
      also have "... = (Cones.FUN (\<psi> (a', a) x) o \<Phi>.FUN a) (\<phi> (a, a) a)"
      proof -
        have "(\<Phi>.FUN a' o Ya.FUN (\<psi> (a', a) x)) (\<phi> (a, a) a)
                = S.Fun (\<Phi> a' \<cdot>\<^sub>S Y a (\<psi> (a', a) x)) (\<phi> (a, a) a)"
          using \<psi>x a' \<phi>a Ya.ide_a Ya.map_simp Hom.set_map by (elim C.in_homE, auto)
        also have "... = S.Fun (S (Cones.map (\<psi> (a', a) x)) (\<Phi> a)) (\<phi> (a, a) a)"
          using \<psi>x is_natural_1 [of "\<psi> (a', a) x"] is_natural_2 [of "\<psi> (a', a) x"] by auto
        also have "... = (Cones.FUN (\<psi> (a', a) x) o \<Phi>.FUN a) (\<phi> (a, a) a)"
        proof -
          have "S.seq (Cones.map (\<psi> (a', a) x)) (\<Phi> a)"
            using Ya.ide_a \<psi>x Cones.map_preserves_dom [of "\<psi> (a', a) x"]
            apply (intro S.seqI)
              apply auto[2]
            by fastforce
          thus ?thesis
            using Ya.ide_a \<phi>a Hom.set_map by auto
        qed
        finally show ?thesis by simp
      qed
      also have "... = Cones.FUN (\<psi> (a', a) x) (\<iota> \<chi>)" using \<iota>\<chi> by simp
      finally show ?thesis by auto
    qed

    lemma \<chi>_is_universal:
    assumes "D.cone a' \<chi>'"
    shows "\<guillemotleft>\<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>')) : a' \<rightarrow> a\<guillemotright>"
    and "D.cones_map (\<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>'))) \<chi> = \<chi>'"
    and "\<lbrakk> \<guillemotleft>f' : a' \<rightarrow> a\<guillemotright>; D.cones_map f' \<chi> = \<chi>' \<rbrakk> \<Longrightarrow> f' = \<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>'))"
    proof -
      interpret \<chi>': cone J C D a' \<chi>' using assms by auto
      have a': "C.ide a'" using \<chi>'.ide_apex by simp
      have \<iota>\<chi>': "\<iota> \<chi>' \<in> Cones.SET a'" using assms a' Cones_SET_eq_\<iota>_img_cones by auto
      let ?f = "\<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>'))"
      have A: "\<Psi>.FUN a' (\<iota> \<chi>') \<in> Hom.set (a', a)"
      proof -
        have "\<Psi>.FUN a' \<in> Cones.SET a' \<rightarrow> Ya.SET a'"
          using a' \<Psi>.preserves_hom [of a' a' a'] S.Fun_mapsto [of "\<Psi>.map a'"] by fastforce
        thus ?thesis using a' \<iota>\<chi>' Ya.ide_a Hom.set_map by auto
      qed
      show f: "\<guillemotleft>?f : a' \<rightarrow> a\<guillemotright>" using A a' Ya.ide_a Hom.\<psi>_mapsto [of a' a] by auto
      have E: "\<And>f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<Longrightarrow> Cones.FUN f (\<iota> \<chi>) = \<Phi>.FUN a' (\<phi> (a', a) f)"
      proof -
        fix f
        assume f: "\<guillemotleft>f : a' \<rightarrow> a\<guillemotright>"
        have "\<phi> (a', a) f \<in> Hom.set (a', a)"
          using a' Ya.ide_a f Hom.\<phi>_mapsto by auto
        thus "Cones.FUN f (\<iota> \<chi>) = \<Phi>.FUN a' (\<phi> (a', a) f)"
          using a' f \<Phi>_FUN_simp by simp
      qed
      have I: "\<Phi>.FUN a' (\<Psi>.FUN a' (\<iota> \<chi>')) = \<iota> \<chi>'"
      proof -
        have "\<Phi>.FUN a' (\<Psi>.FUN a' (\<iota> \<chi>')) =
              compose (\<Psi>.DOM a') (\<Phi>.FUN a') (\<Psi>.FUN a') (\<iota> \<chi>')"
          using a' \<iota>\<chi>' Cones.map_ide \<Psi>.preserves_hom [of a' a' a'] by force
        also have "... = (\<lambda>x \<in> \<Psi>.DOM a'. x) (\<iota> \<chi>')"
          using a' \<Psi>.inverts_components S.inverse_arrows_char by force
        also have "... = \<iota> \<chi>'"
          using a' \<iota>\<chi>' Cones.map_ide \<Psi>.preserves_hom [of a' a' a'] by force
        finally show ?thesis by auto
      qed
      show f\<chi>: "D.cones_map ?f \<chi> = \<chi>'"
      proof -
        have "D.cones_map ?f \<chi> = (\<o> o Cones.FUN ?f o \<iota>) \<chi>"
          using f Cones.preserves_arr [of ?f] cone_\<chi>
          by (cases "D.cone a \<chi>", auto)
        also have "... = \<chi>'"
           using f Ya.ide_a a' A E I by auto
        finally show ?thesis by auto
      qed
      show "\<lbrakk> \<guillemotleft>f' : a' \<rightarrow> a\<guillemotright>; D.cones_map f' \<chi> = \<chi>' \<rbrakk> \<Longrightarrow> f' = ?f"
      proof -
        assume f': "\<guillemotleft>f' : a' \<rightarrow> a\<guillemotright>" and f'\<chi>: "D.cones_map f' \<chi> = \<chi>'"
        show "f' = ?f"
        proof -
          have 1: "\<phi> (a', a) f' \<in> Hom.set (a', a) \<and> \<phi> (a', a) ?f \<in> Hom.set (a', a)"
            using Ya.ide_a a' f f' Hom.\<phi>_mapsto by auto
          have "S.iso (\<Phi> a')" using \<chi>'.ide_apex components_are_iso by auto
          hence 2: "S.arr (\<Phi> a') \<and> bij_betw (\<Phi>.FUN a') (Hom.set (a', a)) (Cones.SET a')"
            using Ya.ide_a a' S.iso_char Hom.set_map by auto
          have "\<Phi>.FUN a' (\<phi> (a', a) f') = \<Phi>.FUN a' (\<phi> (a', a) ?f)"
          proof -
            have "\<Phi>.FUN a' (\<phi> (a', a) ?f) = \<iota> \<chi>'"
              using A I Hom.\<phi>_\<psi> Ya.ide_a a' by simp
            also have "... = Cones.FUN f' (\<iota> \<chi>)"
              using f f' A E cone_\<chi> Cones.preserves_arr f\<chi> f'\<chi> by (elim C.in_homE, auto)
            also have "... = \<Phi>.FUN a' (\<phi> (a', a) f')"
              using f' E by simp
            finally show ?thesis by argo
          qed
          moreover have "inj_on (\<Phi>.FUN a') (Hom.set (a', a))"
            using 2 bij_betw_imp_inj_on by blast
          ultimately have 3: "\<phi> (a', a) f' = \<phi> (a', a) ?f"
            using 1 inj_on_def [of "\<Phi>.FUN a'" "Hom.set (a', a)"] by blast
          show ?thesis
          proof -
            have "f' = \<psi> (a', a) (\<phi> (a', a) f')"
              using Ya.ide_a a' f' Hom.\<psi>_\<phi> by simp
            also have "... = \<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>'))"
              using Ya.ide_a a' Hom.\<psi>_\<phi> A 3 by simp
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

    interpretation \<chi>: limit_cone J C D a \<chi>
    proof
      show "\<And>a' \<chi>'. D.cone a' \<chi>' \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = \<chi>'"
      proof -
        fix a' \<chi>'
        assume 1: "D.cone a' \<chi>'"
        show "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = \<chi>'"
        proof
          show "\<guillemotleft>\<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>')) : a' \<rightarrow> a\<guillemotright> \<and>
                D.cones_map (\<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>'))) \<chi> = \<chi>'"
            using 1 \<chi>_is_universal by blast
          show "\<And>f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = \<chi>' \<Longrightarrow> f = \<psi> (a', a) (\<Psi>.FUN a' (\<iota> \<chi>'))"
            using 1 \<chi>_is_universal by blast
        qed
      qed
    qed

    lemma \<chi>_is_limit_cone:
    shows "D.limit_cone a \<chi>" ..

    lemma induces_limit_situation:
    shows "limit_situation J C D S \<phi> \<iota> a \<Phi> \<chi>"
    proof
      show "\<chi> = \<chi>" by simp
      fix a'
      assume a': "Cop.ide a'"
      let ?F = "\<lambda>x. \<iota> (D.cones_map (\<psi> (a', a) x) \<chi>)"
      show "\<Phi> a' = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') ?F"
      proof -
        have 1: "\<guillemotleft>\<Phi> a' : S.mkIde (Hom.set (a', a)) \<rightarrow>\<^sub>S S.mkIde (\<iota> ` D.cones a')\<guillemotright>"
          using a' Cones.map_ide Ya.ide_a by auto
        moreover have "\<Phi>.DOM a' = Hom.set (a', a)"
          using 1 Hom.set_subset_Univ a' Ya.ide_a by (elim S.in_homE, auto)
        moreover have "\<Phi>.COD a' = \<iota> ` D.cones a'"
          using a' Cones_SET_eq_\<iota>_img_cones by fastforce
        ultimately have 2: "\<Phi> a' = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') (\<Phi>.FUN a')"
          using S.mkArr_Fun [of "\<Phi> a'"] by fastforce
        also have "... = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') ?F"
        proof
          show "S.arr (S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') (\<Phi>.FUN a'))"
            using 1 2 by auto
          show "\<And>x. x \<in> Hom.set (a', a) \<Longrightarrow> \<Phi>.FUN a' x = ?F x"
          proof -
            fix x
            assume x: "x \<in> Hom.set (a', a)"
            hence \<psi>x: "\<guillemotleft>\<psi> (a', a) x : a' \<rightarrow> a\<guillemotright>"
              using a' Ya.ide_a Hom.\<psi>_mapsto by auto
            show "\<Phi>.FUN a' x = ?F x"
            proof -
              have "\<Phi>.FUN a' x = Cones.FUN (\<psi> (a', a) x) (\<iota> \<chi>)"
                using a' x \<Phi>_FUN_simp by simp
              also have "... = restrict (\<iota> o D.cones_map (\<psi> (a', a) x) o \<o>) (\<iota> ` D.cones a) (\<iota> \<chi>)"
                using \<psi>x Cones.map_simp Cones.preserves_arr [of "\<psi> (a', a) x"] S.Fun_mkArr
                by (elim C.in_homE, auto)
              also have "... = ?F x" using cone_\<chi> by simp
              ultimately show ?thesis by simp
            qed
          qed
        qed
        finally show "\<Phi> a' = S.mkArr (Hom.set (a', a)) (\<iota> ` D.cones a') ?F" by auto
      qed
    qed

  end

  sublocale representation_of_cones_functor \<subseteq> limit_situation J C D S \<phi> \<iota> a \<Phi> \<chi>
    using induces_limit_situation by auto

  section "Categories with Limits"

  context category
  begin

    text\<open>
      A category @{term[source=true] C} has limits of shape @{term J} if every diagram of shape
      @{term J} admits a limit cone.
\<close>

    definition has_limits_of_shape
    where "has_limits_of_shape J \<equiv> \<forall>D. diagram J C D \<longrightarrow> (\<exists>a \<chi>. limit_cone J C D a \<chi>)"

    text\<open>
      A category has limits at a type @{typ 'j} if it has limits of shape @{term J}
      for every category @{term J} whose arrows are of type @{typ 'j}.
\<close>

    definition has_limits
    where "has_limits (_ :: 'j) \<equiv> \<forall>J :: 'j comp. category J \<longrightarrow> has_limits_of_shape J"

    lemma has_limits_preserved_by_isomorphism:
    assumes "has_limits_of_shape J" and "isomorphic_categories J J'"
    shows "has_limits_of_shape J'"
    proof -
      interpret J: category J
        using assms(2) isomorphic_categories_def isomorphic_categories_axioms_def by auto
      interpret J': category J'
        using assms(2) isomorphic_categories_def isomorphic_categories_axioms_def by auto
      from assms(2) obtain \<phi> \<psi> where IF: "inverse_functors J J' \<phi> \<psi>"
        using isomorphic_categories_def isomorphic_categories_axioms_def by blast
      interpret IF: inverse_functors J J' \<phi> \<psi> using IF by auto
      have \<psi>\<phi>: "\<psi> o \<phi> = J.map" using IF.inv by metis
      have \<phi>\<psi>: "\<phi> o \<psi> = J'.map" using IF.inv' by metis
      have "\<And>D'. diagram J' C D' \<Longrightarrow> \<exists>a \<chi>. limit_cone J' C D' a \<chi>"
      proof -
        fix D'
        assume D': "diagram J' C D'"
        interpret D': diagram J' C D' using D' by auto
        interpret D: composite_functor J J' C \<phi> D' ..
        interpret D: diagram J C \<open>D' o \<phi>\<close> ..
        have D: "diagram J C (D' o \<phi>)" ..
        from assms(1) obtain a \<chi> where \<chi>: "D.limit_cone a \<chi>"
          using D has_limits_of_shape_def by blast
        interpret \<chi>: limit_cone J C \<open>D' o \<phi>\<close> a \<chi> using \<chi> by auto
        interpret A': constant_functor J' C a
          using \<chi>.ide_apex by (unfold_locales, auto)
        have \<chi>o\<psi>: "cone J' C (D' o \<phi> o \<psi>) a (\<chi> o \<psi>)"
          using comp_cone_functor IF.G.functor_axioms \<chi>.cone_axioms by fastforce
        hence \<chi>o\<psi>: "cone J' C D' a (\<chi> o \<psi>)"
          using \<phi>\<psi> by (metis D'.functor_axioms Fun.comp_assoc comp_functor_identity)
        interpret \<chi>o\<psi>: cone J' C D' a \<open>\<chi> o \<psi>\<close> using \<chi>o\<psi> by auto
        interpret \<chi>o\<psi>: limit_cone J' C D' a \<open>\<chi> o \<psi>\<close>
        proof
          fix a' \<chi>'
          assume \<chi>': "D'.cone a' \<chi>'"
          interpret \<chi>': cone J' C D' a' \<chi>' using \<chi>' by auto
          have \<chi>'o\<phi>: "cone J C (D' o \<phi>) a' (\<chi>' o \<phi>)"
            using \<chi>' comp_cone_functor IF.F.functor_axioms by fastforce
          interpret \<chi>'o\<phi>: cone J C \<open>D' o \<phi>\<close> a' \<open>\<chi>' o \<phi>\<close> using \<chi>'o\<phi> by auto
          have "cone J C (D' o \<phi>) a' (\<chi>' o \<phi>)" ..
          hence 1: "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = \<chi>' o \<phi>"
            using \<chi>.is_universal by simp
          show "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D'.cones_map f (\<chi> o \<psi>) = \<chi>'"
          proof
            let ?f = "THE f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = \<chi>' o \<phi>"
            have f: "\<guillemotleft>?f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map ?f \<chi> = \<chi>' o \<phi>"
              using 1 theI' [of "\<lambda>f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = \<chi>' o \<phi>"] by blast
            have f_in_hom: "\<guillemotleft>?f : a' \<rightarrow> a\<guillemotright>" using f by blast
            have "D'.cones_map ?f (\<chi> o \<psi>) = \<chi>'"
            proof
              fix j'
              have "\<not>J'.arr j' \<Longrightarrow> D'.cones_map ?f (\<chi> o \<psi>) j' = \<chi>' j'"
              proof -
                assume j': "\<not>J'.arr j'"
                have "D'.cones_map ?f (\<chi> o \<psi>) j' = null"
                  using j' f_in_hom \<chi>o\<psi> by fastforce
                thus ?thesis
                  using j' \<chi>'.is_extensional by simp
              qed
              moreover have "J'.arr j' \<Longrightarrow> D'.cones_map ?f (\<chi> o \<psi>) j' = \<chi>' j'"
              proof -
                assume j': "J'.arr j'"
                have "D'.cones_map ?f (\<chi> o \<psi>) j' = \<chi> (\<psi> j') \<cdot> ?f"
                  using j' f \<chi>o\<psi> by fastforce
                also have "... = D.cones_map ?f \<chi> (\<psi> j')"
                  using j' f_in_hom \<chi> \<chi>.cone_\<chi> by fastforce
                also have "... = \<chi>' j'"
                  using j' f \<chi> \<phi>\<psi> Fun.comp_def J'.map_simp by metis
                finally show "D'.cones_map ?f (\<chi> o \<psi>) j' = \<chi>' j'" by auto
              qed
              ultimately show "D'.cones_map ?f (\<chi> o \<psi>) j' = \<chi>' j'" by blast
            qed
            thus "\<guillemotleft>?f : a' \<rightarrow> a\<guillemotright> \<and> D'.cones_map ?f (\<chi> o \<psi>) = \<chi>'" using f by auto
            fix f'
            assume f': "\<guillemotleft>f' : a' \<rightarrow> a\<guillemotright> \<and> D'.cones_map f' (\<chi> o \<psi>) = \<chi>'"
            have "D.cones_map f' \<chi> = \<chi>' o \<phi>"
            proof
              fix j
              have "\<not>J.arr j \<Longrightarrow> D.cones_map f' \<chi> j = (\<chi>' o \<phi>) j"
                using f' \<chi> \<chi>'o\<phi>.is_extensional \<chi>.cone_\<chi> mem_Collect_eq restrict_apply by auto
              moreover have "J.arr j \<Longrightarrow> D.cones_map f' \<chi> j = (\<chi>' o \<phi>) j"
              proof -
                assume j: "J.arr j"
                have "D.cones_map f' \<chi> j = C (\<chi> j) f'"
                  using j f' \<chi>.cone_\<chi> by auto
                also have "... = C ((\<chi> o \<psi>) (\<phi> j)) f'"
                  using j f' \<psi>\<phi> by (metis comp_apply J.map_simp)
                also have "... = D'.cones_map f' (\<chi> o \<psi>) (\<phi> j)"
                  using j f' \<chi>o\<psi> by fastforce
                also have "... = (\<chi>' o \<phi>) j"
                  using j f' by auto
                finally show "D.cones_map f' \<chi> j = (\<chi>' o \<phi>) j" by auto
              qed
              ultimately show "D.cones_map f' \<chi> j = (\<chi>' o \<phi>) j" by blast
            qed
            hence "\<guillemotleft>f' : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f' \<chi> = \<chi>' o \<phi>"
              using f' by auto
            moreover have "\<And>P x x'. (\<exists>!x. P x) \<and> P x \<and> P x' \<Longrightarrow> x = x'"
              by auto
            ultimately show "f' = ?f" using 1 f by blast
          qed
        qed
        have "limit_cone J' C D' a (\<chi> o \<psi>)" ..
        thus "\<exists>a \<chi>. limit_cone J' C D' a \<chi>" by blast
      qed
      thus ?thesis using has_limits_of_shape_def by auto
    qed

  end

  subsection "Diagonal Functors"

  text\<open>
    The existence of limits can also be expressed in terms of adjunctions: a category @{term C}
    has limits of shape @{term J} if the diagonal functor taking each object @{term a}
    in @{term C} to the constant-@{term a} diagram and each arrow \<open>f \<in> C.hom a a'\<close>
    to the constant-@{term f} natural transformation between diagrams is a left adjoint functor.
\<close>

  locale diagonal_functor =
    C: category C +
    J: category J +
    J_C: functor_category J C
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and C :: "'c comp"      (infixr "\<cdot>" 55)
  begin

    notation J.in_hom     ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>J _\<guillemotright>")
    notation J_C.comp     (infixr "\<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>]" 55)
    notation J_C.in_hom   ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] _\<guillemotright>")

    definition map :: "'c \<Rightarrow> ('j, 'c) J_C.arr"
    where "map f = (if C.arr f then J_C.MkArr (constant_functor.map J C (C.dom f))
                                              (constant_functor.map J C (C.cod f))
                                              (constant_transformation.map J C f)
                               else J_C.null)"

    lemma is_functor:
    shows "functor C J_C.comp map"
    proof
      fix f
      show "\<not> C.arr f \<Longrightarrow> local.map f = J_C.null"
        using map_def by simp
      assume f: "C.arr f"
      interpret Dom_f: constant_functor J C \<open>C.dom f\<close>
        using f by (unfold_locales, auto)
      interpret Cod_f: constant_functor J C \<open>C.cod f\<close>
        using f by (unfold_locales, auto)
      interpret Fun_f: constant_transformation J C f
        using f by (unfold_locales, auto)
      show 1: "J_C.arr (map f)"
        using f map_def by (simp add: Fun_f.natural_transformation_axioms)
      show "J_C.dom (map f) = map (C.dom f)"
      proof -
        have "constant_transformation J C (C.dom f)"
          apply unfold_locales using f by auto
        hence "constant_transformation.map J C (C.dom f) = Dom_f.map"
          using Dom_f.map_def constant_transformation.map_def [of J C "C.dom f"] by auto
        thus ?thesis using f 1 by (simp add: map_def J_C.dom_char)
      qed
      show "J_C.cod (map f) = map (C.cod f)"
      proof -
        have "constant_transformation J C (C.cod f)"
          apply unfold_locales using f by auto
        hence "constant_transformation.map J C (C.cod f) = Cod_f.map"
          using Cod_f.map_def constant_transformation.map_def [of J C "C.cod f"] by auto
        thus ?thesis using f 1 by (simp add: map_def J_C.cod_char)
      qed
      next
      fix f g
      assume g: "C.seq g f"
      have f: "C.arr f" using g by auto
      interpret Dom_f: constant_functor J C \<open>C.dom f\<close>
        using f by (unfold_locales, auto)
      interpret Cod_f: constant_functor J C \<open>C.cod f\<close>
        using f by (unfold_locales, auto)
      interpret Fun_f: constant_transformation J C f
        using f by (unfold_locales, auto)
      interpret Cod_g: constant_functor J C \<open>C.cod g\<close>
        using g by (unfold_locales, auto)
      interpret Fun_g: constant_transformation J C g
        using g by (unfold_locales, auto)
      interpret Fun_g: natural_transformation J C Cod_f.map Cod_g.map Fun_g.map
        apply unfold_locales
        using f g C.seqE [of g f] C.comp_arr_dom C.comp_cod_arr Fun_g.is_extensional by auto
      interpret Fun_fg: vertical_composite
                          J C Dom_f.map Cod_f.map Cod_g.map Fun_f.map Fun_g.map ..
      have 1: "J_C.arr (map f)"
        using f map_def by (simp add: Fun_f.natural_transformation_axioms)
      show "map (g \<cdot> f) = map g \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map f"
      proof -
        have "map (C g f) = J_C.MkArr Dom_f.map Cod_g.map
                                      (constant_transformation.map J C (C g f))"
          using f g map_def by simp
        also have "... = J_C.MkArr Dom_f.map Cod_g.map (\<lambda>j. if J.arr j then C g f else C.null)"
        proof -
          have "constant_transformation J C (g \<cdot> f)"
            apply unfold_locales using g by auto
          thus ?thesis using constant_transformation.map_def by metis
        qed
        also have "... = J_C.comp (J_C.MkArr Cod_f.map Cod_g.map Fun_g.map)
                                  (J_C.MkArr Dom_f.map Cod_f.map Fun_f.map)"
        proof -
          have "J_C.MkArr Cod_f.map Cod_g.map Fun_g.map \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>]
                J_C.MkArr Dom_f.map Cod_f.map Fun_f.map
                  = J_C.MkArr Dom_f.map Cod_g.map Fun_fg.map"
            using J_C.comp_char J_C.comp_MkArr Fun_f.natural_transformation_axioms
                  Fun_g.natural_transformation_axioms
            by blast
          also have "... = J_C.MkArr Dom_f.map Cod_g.map
                                     (\<lambda>j. if J.arr j then g \<cdot> f else C.null)"
          proof -
            have "Fun_fg.map = (\<lambda>j. if J.arr j then g \<cdot> f else C.null)"
              using 1 f g Fun_fg.map_def by auto
            thus ?thesis by auto
          qed
          finally show ?thesis by auto
        qed
        also have "... = map g \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map f"
          using f g map_def by fastforce
        finally show ?thesis by auto
      qed
    qed

  end

  sublocale diagonal_functor \<subseteq> "functor" C J_C.comp map
    using is_functor by auto

  context diagonal_functor
  begin

    text\<open>
      The objects of @{term J_C} correspond bijectively to diagrams of shape @{term J}
      in @{term C}.
\<close>

    lemma ide_determines_diagram:
    assumes "J_C.ide d"
    shows "diagram J C (J_C.Map d)" and "J_C.MkIde (J_C.Map d) = d"
    proof -
      interpret \<delta>: natural_transformation J C \<open>J_C.Map d\<close> \<open>J_C.Map d\<close> \<open>J_C.Map d\<close>
        using assms J_C.ide_char J_C.arr_MkArr by fastforce
      interpret D: "functor" J C \<open>J_C.Map d\<close> ..
      show "diagram J C (J_C.Map d)" ..
      show "J_C.MkIde (J_C.Map d) = d"
        using assms J_C.ide_char by (metis J_C.ideD(1) J_C.MkArr_Map)
    qed

    lemma diagram_determines_ide:
    assumes "diagram J C D"
    shows "J_C.ide (J_C.MkIde D)" and "J_C.Map (J_C.MkIde D) = D"
    proof -
      interpret D: diagram J C D using assms by auto
      show "J_C.ide (J_C.MkIde D)" using J_C.ide_char
        using D.functor_axioms J_C.ide_MkIde by auto
      thus "J_C.Map (J_C.MkIde D) = D"
        using J_C.in_homE by simp
    qed

    lemma bij_betw_ide_diagram:
    shows "bij_betw J_C.Map (Collect J_C.ide) (Collect (diagram J C))"
    proof (intro bij_betwI)
      show "J_C.Map \<in> Collect J_C.ide \<rightarrow> Collect (diagram J C)"
        using ide_determines_diagram by blast
      show "J_C.MkIde \<in> Collect (diagram J C) \<rightarrow> Collect J_C.ide"
        using diagram_determines_ide by blast
      show "\<And>d. d \<in> Collect J_C.ide \<Longrightarrow> J_C.MkIde (J_C.Map d) = d"
        using ide_determines_diagram by blast
      show "\<And>D. D \<in> Collect (diagram J C) \<Longrightarrow> J_C.Map (J_C.MkIde D) = D"
        using diagram_determines_ide by blast
    qed

    text\<open>
      Arrows from from the diagonal functor correspond bijectively to cones.
\<close>

    lemma arrow_determines_cone:
    assumes "J_C.ide d" and "arrow_from_functor C J_C.comp map a d x"
    shows "cone J C (J_C.Map d) a (J_C.Map x)"
    and "J_C.MkArr (constant_functor.map J C a) (J_C.Map d) (J_C.Map x) = x"
    proof -
      interpret D: diagram J C \<open>J_C.Map d\<close>
        using assms ide_determines_diagram by auto
      interpret x: arrow_from_functor C J_C.comp map a d x
        using assms by auto
      interpret A: constant_functor J C a
        using x.arrow by (unfold_locales, auto)
      interpret \<alpha>: constant_transformation J C a
        using x.arrow by (unfold_locales, auto)
      have Dom_x: "J_C.Dom x = A.map"
      proof -
        have "J_C.dom x = map a" using x.arrow by blast
        hence "J_C.Map (J_C.dom x) = J_C.Map (map a)" by simp
        hence "J_C.Dom x = J_C.Map (map a)"
          using A.value_is_ide x.arrow J_C.in_homE by (metis J_C.Map_dom)
        moreover have "J_C.Map (map a) = \<alpha>.map"
          using A.value_is_ide preserves_ide map_def by simp
        ultimately show ?thesis using \<alpha>.map_def A.map_def by auto
      qed
      have Cod_x: "J_C.Cod x = J_C.Map d"
        using x.arrow by auto
      interpret \<chi>: natural_transformation J C A.map \<open>J_C.Map d\<close> \<open>J_C.Map x\<close>
        using x.arrow J_C.arr_char [of x] Dom_x Cod_x by force
      show "D.cone a (J_C.Map x)" ..
      show "J_C.MkArr A.map (J_C.Map d) (J_C.Map x) = x"
        using x.arrow Dom_x Cod_x \<chi>.natural_transformation_axioms
        by (intro J_C.arr_eqI, auto)
    qed

    lemma cone_determines_arrow:
    assumes "J_C.ide d" and "cone J C (J_C.Map d) a \<chi>"
    shows "arrow_from_functor C J_C.comp map a d
             (J_C.MkArr (constant_functor.map J C a) (J_C.Map d) \<chi>)"
    and "J_C.Map (J_C.MkArr (constant_functor.map J C a) (J_C.Map d) \<chi>) = \<chi>"
    proof -
       interpret \<chi>: cone J C \<open>J_C.Map d\<close> a \<chi> using assms(2) by auto
       let ?x = "J_C.MkArr \<chi>.A.map (J_C.Map d) \<chi>"
       interpret x: arrow_from_functor C J_C.comp map a d ?x
       proof
         have "\<guillemotleft>J_C.MkArr \<chi>.A.map (J_C.Map d) \<chi> :
                  J_C.MkIde \<chi>.A.map \<rightarrow>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] J_C.MkIde (J_C.Map d)\<guillemotright>"
           using \<chi>.natural_transformation_axioms by auto
         moreover have "J_C.MkIde \<chi>.A.map = map a"
           using \<chi>.A.value_is_ide map_def \<chi>.A.map_def C.ide_char
           by (metis (no_types, lifting) J_C.dom_MkArr preserves_arr preserves_dom)
         moreover have "J_C.MkIde (J_C.Map d) = d"
           using assms ide_determines_diagram(2) by simp
         ultimately show "C.ide a \<and> \<guillemotleft>J_C.MkArr \<chi>.A.map (J_C.Map d) \<chi> : map a \<rightarrow>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] d\<guillemotright>"
           using \<chi>.A.value_is_ide by simp
       qed
       show "arrow_from_functor C J_C.comp map a d ?x" ..
       show "J_C.Map (J_C.MkArr (constant_functor.map J C a) (J_C.Map d) \<chi>) = \<chi>"
         by (simp add: \<chi>.natural_transformation_axioms)
    qed

    text\<open>
      Transforming a cone by composing at the apex with an arrow @{term g} corresponds,
      via the preceding bijections, to composition in \<open>[J, C]\<close> with the image of @{term g}
      under the diagonal functor.
\<close>

    lemma cones_map_is_composition:
    assumes "\<guillemotleft>g : a' \<rightarrow> a\<guillemotright>" and "cone J C D a \<chi>"
    shows "J_C.MkArr (constant_functor.map J C a') D (diagram.cones_map J C D g \<chi>)
             = J_C.MkArr (constant_functor.map J C a) D \<chi> \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map g"
    proof -
      interpret A: constant_transformation J C a
        using assms(1) by (unfold_locales, auto)
      interpret \<chi>: cone J C D a \<chi> using assms(2) by auto
      have cone_\<chi>: "cone J C D a \<chi>" ..
      interpret A': constant_transformation J C a'
        using assms(1) by (unfold_locales, auto)
      let ?\<chi>' = "\<chi>.D.cones_map g \<chi>"
      interpret \<chi>': cone J C D a' ?\<chi>'
        using assms(1) cone_\<chi> \<chi>.D.cones_map_mapsto by blast
      let ?x = "J_C.MkArr \<chi>.A.map D \<chi>"
      let ?x' = "J_C.MkArr \<chi>'.A.map D ?\<chi>'"
      show "?x' = J_C.comp ?x (map g)"
      proof (intro J_C.arr_eqI)
        have x: "J_C.arr ?x"
          using \<chi>.natural_transformation_axioms J_C.arr_char [of ?x] by simp
        show x': "J_C.arr ?x'"
          using \<chi>'.natural_transformation_axioms J_C.arr_char [of ?x'] by simp
        have 3: "\<guillemotleft>?x : map a \<rightarrow>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] J_C.MkIde D\<guillemotright>"
        proof -
          have 1: "map a = J_C.MkIde A.map"
            using \<chi>.ide_apex A.equals_dom_if_value_is_ide A.equals_cod_if_value_is_ide map_def
            by auto
          have "J_C.arr ?x" using x by blast
          moreover have "J_C.dom ?x = map a"
            using x J_C.dom_char 1 x \<chi>.ide_apex A.equals_dom_if_value_is_ide \<chi>.D.functor_axioms
                    J_C.ide_char
            by auto
          moreover have "J_C.cod ?x = J_C.MkIde D" using x J_C.cod_char by auto
          ultimately show ?thesis by fast
        qed
        have 4: "\<guillemotleft>?x' : map a' \<rightarrow>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] J_C.MkIde D\<guillemotright>"
        proof -
          have 1: "map a' = J_C.MkIde A'.map"
            using \<chi>'.ide_apex A'.equals_dom_if_value_is_ide A'.equals_cod_if_value_is_ide map_def
            by auto
          have "J_C.arr ?x'" using x' by blast
          moreover have "J_C.dom ?x' = map a'"
            using x' J_C.dom_char 1 x' \<chi>'.ide_apex A'.equals_dom_if_value_is_ide \<chi>.D.functor_axioms
                    J_C.ide_char
            by force
          moreover have "J_C.cod ?x' = J_C.MkIde D" using x' J_C.cod_char by auto
          ultimately show ?thesis by fast
        qed
        have seq_xg: "J_C.seq ?x (map g)"
          using assms(1) 3 preserves_hom [of g] by (intro J_C.seqI', auto)
        show 2: "J_C.seq ?x (map g)"
          using seq_xg J_C.seqI' by blast
        show "J_C.Dom ?x' = J_C.Dom (?x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map g)"
        proof -
          have "J_C.Dom ?x' = J_C.Dom (J_C.dom ?x')"
            using x' J_C.Dom_dom by simp
          also have "... = J_C.Dom (map a')"
            using 4 by force
          also have "... = J_C.Dom (J_C.dom (?x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map g))"
            using assms(1) 2 by auto
          also have "... = J_C.Dom (?x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map g)"
            using seq_xg J_C.Dom_dom J_C.seqI' by blast
          finally show ?thesis by auto
        qed
        show "J_C.Cod ?x' = J_C.Cod (?x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map g)"
        proof -
          have "J_C.Cod ?x' = J_C.Cod (J_C.cod ?x')"
            using x' J_C.Cod_cod by simp
          also have "... = J_C.Cod (J_C.MkIde D)"
            using 4 by force
          also have "... = J_C.Cod (J_C.cod (?x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map g))"
            using 2 3 J_C.cod_comp J_C.in_homE by metis
          also have "... = J_C.Cod (?x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map g)"
            using seq_xg J_C.Cod_cod J_C.seqI' by blast
          finally show ?thesis by auto
        qed
        show "J_C.Map ?x' = J_C.Map (?x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map g)"
        proof -
          interpret g: constant_transformation J C g
            apply unfold_locales using assms(1) by auto
          interpret \<chi>og: vertical_composite J C A'.map \<chi>.A.map D g.map \<chi>
            using assms(1) C.comp_arr_dom C.comp_cod_arr A'.is_extensional g.is_extensional
            apply (unfold_locales, auto)
            by (elim J.seqE, auto)
          have "J_C.Map (?x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map g) = \<chi>og.map"
            using assms(1) 2 J_C.comp_char map_def by auto
          also have "... = J_C.Map ?x'"
            using x' \<chi>og.map_def J_C.arr_char [of ?x'] natural_transformation.is_extensional
                  assms(1) cone_\<chi> \<chi>og.map_simp_2
            by fastforce
          finally show ?thesis by auto
        qed
      qed
    qed

    text\<open>
      Coextension along an arrow from a functor is equivalent to a transformation of cones.
\<close>

    lemma coextension_iff_cones_map:
    assumes x: "arrow_from_functor C J_C.comp map a d x"
    and g: "\<guillemotleft>g : a' \<rightarrow> a\<guillemotright>"
    and x': "\<guillemotleft>x' : map a' \<rightarrow>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] d\<guillemotright>"
    shows "arrow_from_functor.is_coext C J_C.comp map a x a' x' g
              \<longleftrightarrow> J_C.Map x' = diagram.cones_map J C (J_C.Map d) g (J_C.Map x)"
    proof -
      interpret x: arrow_from_functor C J_C.comp map a d x
        using assms by auto
      interpret A': constant_functor J C a'
        using assms(2) by (unfold_locales, auto)
      have x': "arrow_from_functor C J_C.comp map a' d x'"
        using A'.value_is_ide assms(3) by (unfold_locales, blast)
      have d: "J_C.ide d" using J_C.ide_cod x.arrow by blast
      let ?D = "J_C.Map d"
      let ?\<chi> = "J_C.Map x"
      let ?\<chi>' = "J_C.Map x'"
      interpret D: diagram J C ?D
        using ide_determines_diagram J_C.ide_cod x.arrow by blast
      interpret \<chi>: cone J C ?D a ?\<chi>
        using assms(1) d arrow_determines_cone by simp
      interpret \<gamma>: constant_transformation J C g
        using g \<chi>.ide_apex by (unfold_locales, auto)
      interpret \<chi>og: vertical_composite J C A'.map \<chi>.A.map ?D \<gamma>.map ?\<chi>
        using g C.comp_arr_dom C.comp_cod_arr \<gamma>.is_extensional by (unfold_locales, auto)
      show ?thesis
      proof
        assume 0: "x.is_coext a' x' g"
        show "?\<chi>' = D.cones_map g ?\<chi>"
        proof -
          have 1: "x' = x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map g"
            using 0 x.is_coext_def by blast
          hence "?\<chi>' = J_C.Map x'"
            using 0 x.is_coext_def by fast
          moreover have "... = D.cones_map g ?\<chi>"
          proof -
            have "J_C.MkArr A'.map (J_C.Map d) (D.cones_map g (J_C.Map x)) = x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map g"
              using d g cones_map_is_composition arrow_determines_cone(2) \<chi>.cone_axioms
                    x.arrow_from_functor_axioms
              by auto
            hence f1: "J_C.MkArr A'.map (J_C.Map d) (D.cones_map g (J_C.Map x)) = x'"
              by (metis 1)
            have "J_C.arr (J_C.MkArr A'.map (J_C.Map d) (D.cones_map g (J_C.Map x)))"
              using 1 d g cones_map_is_composition preserves_arr arrow_determines_cone(2)
                    \<chi>.cone_axioms x.arrow_from_functor_axioms assms(3)
              by auto
            thus ?thesis
              using f1 by auto
          qed
          ultimately show ?thesis by blast
        qed
        next
        assume X': "?\<chi>' = D.cones_map g ?\<chi>"
        show "x.is_coext a' x' g"
        proof -
          have 4: "J_C.seq x (map g)"
            using g x.arrow mem_Collect_eq preserves_arr preserves_cod
            by (elim C.in_homE, auto)
          hence 1: "x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] map g =
                   J_C.MkArr (J_C.Dom (map g)) (J_C.Cod x)
                             (vertical_composite.map J C (J_C.Map (map g)) ?\<chi>)"
            using J_C.comp_char [of x "map g"] by simp
          have 2: "vertical_composite.map J C (J_C.Map (map g)) ?\<chi> = \<chi>og.map"
            by (simp add: map_def \<gamma>.value_is_arr \<gamma>.natural_transformation_axioms)
          have 3: "... = D.cones_map g ?\<chi>"
            using g \<chi>og.map_simp_2 \<chi>.cone_axioms \<chi>og.is_extensional by auto
          have "J_C.MkArr A'.map ?D ?\<chi>' = J_C.comp x (map g)"
          proof -
            have f1: "A'.map = J_C.Dom (map g)"
              using \<gamma>.natural_transformation_axioms map_def g by auto
            have "J_C.Map d = J_C.Cod x"
              using x.arrow by auto
            thus ?thesis using f1 X' 1 2 3 by argo
          qed
          moreover have "J_C.MkArr A'.map ?D ?\<chi>' = x'"
            using d x' arrow_determines_cone by blast
          ultimately show ?thesis
            using g x.is_coext_def by simp
        qed
      qed
    qed

  end

  locale right_adjoint_to_diagonal_functor =
    C: category C +
    J: category J +
    J_C: functor_category J C +
    \<Delta>: diagonal_functor J C +
    "functor" J_C.comp C G +
    Adj: meta_adjunction J_C.comp C \<Delta>.map G \<phi> \<psi>
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and C :: "'c comp"      (infixr "\<cdot>" 55)
  and G :: "('j, 'c) functor_category.arr \<Rightarrow> 'c"
  and \<phi> :: "'c \<Rightarrow> ('j, 'c) functor_category.arr \<Rightarrow> 'c"
  and \<psi> :: "('j, 'c) functor_category.arr \<Rightarrow> 'c \<Rightarrow> ('j, 'c) functor_category.arr" +
  assumes adjoint: "adjoint_functors J_C.comp C \<Delta>.map G"
  begin

    text\<open>
      A right adjoint @{term G} to a diagonal functor maps each object @{term d} of
      \<open>[J, C]\<close> (corresponding to a diagram @{term D} of shape @{term J} in @{term C}
      to an object of @{term C}.  This object is the limit object, and the component at @{term d}
      of the counit of the adjunction determines the limit cone.
\<close>

    lemma gives_limit_cones:
    assumes "diagram J C D"
    shows "limit_cone J C D (G (J_C.MkIde D)) (J_C.Map (Adj.\<epsilon> (J_C.MkIde D)))"
    proof -
      interpret D: diagram J C D using assms by auto
      let ?d = "J_C.MkIde D"
      let ?a = "G ?d"
      let ?x = "Adj.\<epsilon> ?d"
      let ?\<chi> = "J_C.Map ?x"
      have "diagram J C D" ..
      hence 1: "J_C.ide ?d" using \<Delta>.diagram_determines_ide by auto
      hence 2: "J_C.Map (J_C.MkIde D) = D"
        using assms 1 J_C.in_homE \<Delta>.diagram_determines_ide(2) by simp
      interpret x: terminal_arrow_from_functor C J_C.comp \<Delta>.map ?a ?d ?x
        apply unfold_locales
         apply (metis (no_types, lifting) "1" preserves_ide Adj.\<epsilon>_in_terms_of_\<psi>
                Adj.\<epsilon>o_def Adj.\<epsilon>o_in_hom)
        by (metis 1 Adj.has_terminal_arrows_from_functor(1)
                  terminal_arrow_from_functor.is_terminal)
      have 3: "arrow_from_functor C J_C.comp \<Delta>.map ?a ?d ?x" ..
      interpret \<chi>: cone J C D ?a ?\<chi>
        using 1 2 3 \<Delta>.arrow_determines_cone [of ?d] by auto
      have cone_\<chi>: "D.cone ?a ?\<chi>" ..
      interpret \<chi>: limit_cone J C D ?a ?\<chi>
      proof
        fix a' \<chi>'
        assume cone_\<chi>': "D.cone a' \<chi>'"
        interpret \<chi>': cone J C D a' \<chi>' using cone_\<chi>' by auto
        let ?x' = "J_C.MkArr \<chi>'.A.map D \<chi>'"
        interpret x': arrow_from_functor C J_C.comp \<Delta>.map a' ?d ?x'
          using 1 2 by (metis \<Delta>.cone_determines_arrow(1) cone_\<chi>')
        have "arrow_from_functor C J_C.comp \<Delta>.map a' ?d ?x'" ..
        hence 4: "\<exists>!g. x.is_coext a' ?x' g"
          using x.is_terminal by simp
        have 5: "\<And>g. \<guillemotleft>g : a' \<rightarrow>\<^sub>C ?a\<guillemotright> \<Longrightarrow> x.is_coext a' ?x' g \<longleftrightarrow> D.cones_map g ?\<chi> = \<chi>'"
        proof -
          fix g
          assume g: "\<guillemotleft>g : a' \<rightarrow>\<^sub>C ?a\<guillemotright>"
          show "x.is_coext a' ?x' g \<longleftrightarrow> D.cones_map g ?\<chi> = \<chi>'"
          proof -
            have "\<guillemotleft>?x' : \<Delta>.map a' \<rightarrow>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] ?d\<guillemotright>"
              using x'.arrow by simp
            thus ?thesis
              using 3 g \<Delta>.coextension_iff_cones_map [of ?a ?d]
              by (metis (no_types, lifting) 1 2 \<Delta>.cone_determines_arrow(2) cone_\<chi>')
          qed
        qed
        have 6: "\<And>g. x.is_coext a' ?x' g \<Longrightarrow> \<guillemotleft>g : a' \<rightarrow>\<^sub>C ?a\<guillemotright>"
          using x.is_coext_def by simp
        show "\<exists>!g. \<guillemotleft>g : a' \<rightarrow>\<^sub>C ?a\<guillemotright> \<and> D.cones_map g ?\<chi> = \<chi>'"
        proof -
          have "\<exists>g. \<guillemotleft>g : a' \<rightarrow>\<^sub>C ?a\<guillemotright> \<and> D.cones_map g ?\<chi> = \<chi>'"
            using 4 5 6 by meson
          thus ?thesis
            using 4 5 6 by blast
        qed
      qed
      show "D.limit_cone ?a ?\<chi>" ..
    qed

    corollary gives_limits:
    assumes "diagram J C D"
    shows "diagram.has_as_limit J C D (G (J_C.MkIde D))"
      using assms gives_limit_cones by fastforce

  end

  lemma (in category) has_limits_iff_left_adjoint_diagonal:
  assumes "category J"
  shows "has_limits_of_shape J \<longleftrightarrow>
           left_adjoint_functor C (functor_category.comp J C) (diagonal_functor.map J C)"
  proof -
    interpret J: category J using assms by auto
    interpret J_C: functor_category J C ..
    interpret \<Delta>: diagonal_functor J C ..
    show ?thesis
    proof
      assume A: "left_adjoint_functor C J_C.comp \<Delta>.map"
      interpret \<Delta>: left_adjoint_functor C J_C.comp \<Delta>.map using A by auto
      interpret Adj: meta_adjunction J_C.comp C \<Delta>.map \<Delta>.G \<Delta>.\<phi> \<Delta>.\<psi>
        using \<Delta>.induces_meta_adjunction by auto
      have "meta_adjunction J_C.comp C \<Delta>.map \<Delta>.G \<Delta>.\<phi> \<Delta>.\<psi>" ..
      hence 1: "adjoint_functors J_C.comp C \<Delta>.map \<Delta>.G"
        using adjoint_functors_def by blast
      interpret G: right_adjoint_to_diagonal_functor J C \<Delta>.G \<Delta>.\<phi> \<Delta>.\<psi>
        using 1 by (unfold_locales, auto)
      have "\<And>D. diagram J C D \<Longrightarrow> \<exists>a. diagram.has_as_limit J C D a"
        using A G.gives_limits by blast
      hence "\<And>D. diagram J C D \<Longrightarrow> \<exists>a \<chi>. limit_cone J C D a \<chi>"
        by metis
      thus "has_limits_of_shape J" using has_limits_of_shape_def by blast
      next
      text\<open>
        If @{term "has_limits J"}, then every diagram @{term D} from @{term J} to
        @{term[source=true] C} has a limit cone.
        This means that, for every object @{term d} of the functor category
        \<open>[J, C]\<close>, there exists an object @{term a} of @{term C} and a terminal arrow from
        \<open>\<Delta> a\<close> to @{term d} in \<open>[J, C]\<close>.  The terminal arrow is given by the
        limit cone.
\<close>
      assume A: "has_limits_of_shape J"
      show "left_adjoint_functor C J_C.comp \<Delta>.map"
      proof
        fix d
        assume D: "J_C.ide d"
        interpret D: diagram J C \<open>J_C.Map d\<close>
          using D \<Delta>.ide_determines_diagram by auto
        let ?D = "J_C.Map d"
        have "diagram J C (J_C.Map d)" ..
        from this obtain a \<chi> where limit: "limit_cone J C ?D a \<chi>"
          using A has_limits_of_shape_def by blast
        interpret A: constant_functor J C a
          using limit by (simp add: Limit.cone_def limit_cone_def)
        interpret \<chi>: limit_cone J C ?D a \<chi> using limit by auto
        have cone_\<chi>: "cone J C ?D a \<chi>" ..
        let ?x = "J_C.MkArr A.map ?D \<chi>"
        interpret x: arrow_from_functor C J_C.comp \<Delta>.map a d ?x
          using D cone_\<chi> \<Delta>.cone_determines_arrow by auto
        have "terminal_arrow_from_functor C J_C.comp \<Delta>.map a d ?x"
        proof
          show "\<And>a' x'. arrow_from_functor C J_C.comp \<Delta>.map a' d x' \<Longrightarrow> \<exists>!g. x.is_coext a' x' g"
          proof -
            fix a' x'
            assume x': "arrow_from_functor C J_C.comp \<Delta>.map a' d x'"
            interpret x': arrow_from_functor C J_C.comp \<Delta>.map a' d x' using x' by auto
            interpret A': constant_functor J C a'
              by (unfold_locales, simp add: x'.arrow)
            let ?\<chi>' = "J_C.Map x'"
            interpret \<chi>': cone J C ?D a' ?\<chi>'
              using D x' \<Delta>.arrow_determines_cone by auto
            have cone_\<chi>': "cone J C ?D a' ?\<chi>'" ..
            let ?g = "\<chi>.induced_arrow a' ?\<chi>'"
            show "\<exists>!g. x.is_coext a' x' g"
            proof
              show "x.is_coext a' x' ?g"
              proof (unfold x.is_coext_def)
                have 1: "\<guillemotleft>?g : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map ?g \<chi> = ?\<chi>'"
                  using \<chi>.induced_arrow_def \<chi>.is_universal cone_\<chi>'
                        theI' [of "\<lambda>f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<chi> = ?\<chi>'"]
                  by presburger
                hence 2: "x' = ?x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] \<Delta>.map ?g"
                proof -
                  have "x' = J_C.MkArr A'.map ?D ?\<chi>'"
                    using D \<Delta>.arrow_determines_cone(2) x'.arrow_from_functor_axioms by auto
                  thus ?thesis
                    using 1 cone_\<chi> \<Delta>.cones_map_is_composition [of ?g a' a ?D \<chi>] by simp
                qed
                show "\<guillemotleft>?g : a' \<rightarrow> a\<guillemotright> \<and> x' = ?x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] \<Delta>.map ?g"
                  using 1 2 by auto
              qed
              next
              fix g
              assume X: "x.is_coext a' x' g"
              show "g = ?g"
              proof -
                have "\<guillemotleft>g : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map g \<chi> = ?\<chi>'"
                proof
                  show G: "\<guillemotleft>g : a' \<rightarrow> a\<guillemotright>" using X x.is_coext_def by blast
                  show "D.cones_map g \<chi> = ?\<chi>'"
                  proof -
                    have "?\<chi>' = J_C.Map (?x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] \<Delta>.map g)"
                      using X x.is_coext_def [of a' x' g] by fast
                    also have "... = D.cones_map g \<chi>"
                    proof -
                      interpret map_g: constant_transformation J C g
                        using G by (unfold_locales, auto)
                      interpret \<chi>': vertical_composite J C
                                      map_g.F.map A.map \<open>\<chi>.\<Phi>.Ya.Cop_S.Map d\<close>
                                      map_g.map \<chi>
                      proof (intro_locales)
                        have "map_g.G.map = A.map"
                          using G by blast
                        thus "natural_transformation_axioms J (\<cdot>) map_g.F.map A.map map_g.map"
                          using map_g.natural_transformation_axioms
                          by (simp add: natural_transformation_def)
                      qed
                      have "J_C.Map (?x \<cdot>\<^sub>[\<^sub>J\<^sub>,\<^sub>C\<^sub>] \<Delta>.map g) = vertical_composite.map J C map_g.map \<chi>"
                      proof -
                        have "J_C.seq ?x (\<Delta>.map g)"
                          using G x.arrow by auto
                        thus ?thesis
                          using G \<Delta>.map_def J_C.Map_comp' [of ?x "\<Delta>.map g"] by auto
                      qed
                      also have "... = D.cones_map g \<chi>"
                        using G cone_\<chi> \<chi>'.map_def map_g.map_def \<chi>.is_natural_2 \<chi>'.map_simp_2
                        by auto
                      finally show ?thesis by blast
                    qed
                    finally show ?thesis by auto
                  qed
                qed
                thus ?thesis
                  using cone_\<chi>' \<chi>.is_universal \<chi>.induced_arrow_def
                        theI_unique [of "\<lambda>g. \<guillemotleft>g : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map g \<chi> = ?\<chi>'" g]
                  by presburger
              qed
            qed
          qed
        qed
        thus "\<exists>a x. terminal_arrow_from_functor C J_C.comp \<Delta>.map a d x" by auto
      qed
    qed
  qed

  section "Right Adjoint Functors Preserve Limits"

  context right_adjoint_functor
  begin

    lemma preserves_limits:
    fixes J :: "'j comp"
    assumes "diagram J C E" and "diagram.has_as_limit J C E a"
    shows "diagram.has_as_limit J D (G o E) (G a)"
    proof -
      text\<open>
        From the assumption that @{term E} has a limit, obtain a limit cone @{term \<chi>}.
\<close>
      interpret J: category J using assms(1) diagram_def by auto
      interpret E: diagram J C E using assms(1) by auto
      from assms(2) obtain \<chi> where \<chi>: "limit_cone J C E a \<chi>" by auto
      interpret \<chi>: limit_cone J C E a \<chi> using \<chi> by auto
      have a: "C.ide a" using \<chi>.ide_apex by auto
      text\<open>
        Form the @{term E}-image \<open>GE\<close> of the diagram @{term E}.
\<close>
      interpret GE: composite_functor J C D E G ..
      interpret GE: diagram J D GE.map ..
      text\<open>Let \<open>G\<chi>\<close> be the @{term G}-image of the cone @{term \<chi>},
             and note that it is a cone over \<open>GE\<close>.\<close>
      let ?G\<chi> = "G o \<chi>"
      interpret G\<chi>: cone J D GE.map \<open>G a\<close> ?G\<chi>
        using \<chi>.cone_axioms preserves_cones by blast
      text\<open>
        Claim that \<open>G\<chi>\<close> is a limit cone for diagram \<open>GE\<close>.
\<close>
      interpret G\<chi>: limit_cone J D GE.map \<open>G a\<close> ?G\<chi>
      proof
        text \<open>
          Let @{term \<kappa>} be an arbitrary cone over \<open>GE\<close>.
\<close>
        fix b \<kappa>
        assume \<kappa>: "GE.cone b \<kappa>"
        interpret \<kappa>: cone J D GE.map b \<kappa> using \<kappa> by auto
        interpret Fb: constant_functor J C \<open>F b\<close>
          apply unfold_locales
          by (meson F_is_functor \<kappa>.ide_apex functor.preserves_ide)
        interpret Adj: meta_adjunction C D F G \<phi> \<psi>
          using induces_meta_adjunction by auto
        text\<open>
          For each arrow @{term j} of @{term J}, let @{term "\<chi>' j"} be defined to be
          the adjunct of @{term "\<chi> j"}.  We claim that @{term \<chi>'} is a cone over @{term E}.
\<close>
        let ?\<chi>' = "\<lambda>j. if J.arr j then Adj.\<epsilon> (C.cod (E j)) \<cdot>\<^sub>C F (\<kappa> j) else C.null"
        have cone_\<chi>': "E.cone (F b) ?\<chi>'"
        proof
          show "\<And>j. \<not>J.arr j \<Longrightarrow> ?\<chi>' j = C.null" by simp
          fix j
          assume j: "J.arr j"
          show "C.dom (?\<chi>' j) = Fb.map (J.dom j)" using j \<psi>_in_hom by simp
          show "C.cod (?\<chi>' j) = E (J.cod j)" using j \<psi>_in_hom by simp
          show "E j \<cdot>\<^sub>C ?\<chi>' (J.dom j) = ?\<chi>' j"
          proof -
            have "E j \<cdot>\<^sub>C ?\<chi>' (J.dom j) = (E j \<cdot>\<^sub>C Adj.\<epsilon> (E (J.dom j))) \<cdot>\<^sub>C F (\<kappa> (J.dom j))"
              using j C.comp_assoc by simp
            also have "... = Adj.\<epsilon> (E (J.cod j)) \<cdot>\<^sub>C F (\<kappa> j)"
            proof -
              have "(E j \<cdot>\<^sub>C Adj.\<epsilon> (E (J.dom j))) \<cdot>\<^sub>C F (\<kappa> (J.dom j))
                       = (Adj.\<epsilon> (C.cod (E j)) \<cdot>\<^sub>C Adj.FG.map (E j)) \<cdot>\<^sub>C F (\<kappa> (J.dom j))"
                using j Adj.\<epsilon>.naturality [of "E j"] by fastforce
              also have "... = Adj.\<epsilon> (C.cod (E j)) \<cdot>\<^sub>C Adj.FG.map (E j) \<cdot>\<^sub>C F (\<kappa> (J.dom j))"
                using C.comp_assoc by simp
              also have "... = Adj.\<epsilon> (E (J.cod j)) \<cdot>\<^sub>C F (\<kappa> j)"
              proof -
                have "Adj.FG.map (E j) \<cdot>\<^sub>C F (\<kappa> (J.dom j)) = F (GE.map j \<cdot>\<^sub>D \<kappa> (J.dom j))"
                  using j by simp
                hence "Adj.FG.map (E j) \<cdot>\<^sub>C F (\<kappa> (J.dom j)) = F (\<kappa> j)"
                  using j \<kappa>.is_natural_1 by metis
                thus ?thesis using j by simp
              qed
              finally show ?thesis by auto
            qed
            also have "... = ?\<chi>' j"
              using j by simp
            finally show ?thesis by auto
          qed
          show "?\<chi>' (J.cod j) \<cdot>\<^sub>C Fb.map j = ?\<chi>' j"
          proof -
            have "?\<chi>' (J.cod j) \<cdot>\<^sub>C Fb.map j = Adj.\<epsilon> (E (J.cod j)) \<cdot>\<^sub>C F (\<kappa> (J.cod j))"
              using j Fb.value_is_ide Adj.\<epsilon>.preserves_hom C.comp_arr_dom [of "F (\<kappa> (J.cod j))"]
                    C.comp_assoc
              by simp
            also have "... = Adj.\<epsilon> (E (J.cod j)) \<cdot>\<^sub>C F (\<kappa> j)"
              using j \<kappa>.is_natural_1 \<kappa>.is_natural_2 Adj.\<epsilon>.naturality J.arr_cod_iff_arr
              by (metis J.cod_cod \<kappa>.A.map_simp)
            also have "... = ?\<chi>' j" using j by simp
            finally show ?thesis by auto
          qed
        qed
        text\<open>
          Using the universal property of the limit cone @{term \<chi>}, obtain the unique arrow
          @{term f} that transforms @{term \<chi>} into @{term \<chi>'}.
\<close>
        from this \<chi>.is_universal [of "F b" ?\<chi>'] obtain f
          where f: "\<guillemotleft>f : F b \<rightarrow>\<^sub>C a\<guillemotright> \<and> E.cones_map f \<chi> = ?\<chi>'"
          by auto
        text\<open>
          Let @{term g} be the adjunct of @{term f}, and show that @{term g} transforms
          @{term G\<chi>} into @{term \<kappa>}.
\<close>
        let ?g = "G f \<cdot>\<^sub>D Adj.\<eta> b"
        have 1: "\<guillemotleft>?g : b \<rightarrow>\<^sub>D G a\<guillemotright>" using f \<kappa>.ide_apex by fastforce
        moreover have "GE.cones_map ?g ?G\<chi> = \<kappa>"
        proof
          fix j
          have "\<not>J.arr j \<Longrightarrow> GE.cones_map ?g ?G\<chi> j = \<kappa> j"
            using 1 G\<chi>.cone_axioms \<kappa>.is_extensional by auto
          moreover have "J.arr j \<Longrightarrow> GE.cones_map ?g ?G\<chi> j = \<kappa> j"
          proof -
            fix j
            assume j: "J.arr j"
            have "GE.cones_map ?g ?G\<chi> j = G (\<chi> j) \<cdot>\<^sub>D ?g"
              using j 1 G\<chi>.cone_axioms mem_Collect_eq restrict_apply by auto
            also have "... = G (\<chi> j \<cdot>\<^sub>C f) \<cdot>\<^sub>D Adj.\<eta> b"
              using j f \<chi>.preserves_hom [of j "J.dom j" "J.cod j"] D.comp_assoc by fastforce
            also have "... = G (E.cones_map f \<chi> j) \<cdot>\<^sub>D Adj.\<eta> b"
            proof -
              have "\<chi> j \<cdot>\<^sub>C f = Adj.\<epsilon> (C.cod (E j)) \<cdot>\<^sub>C F (\<kappa> j)"
              proof -
                have "E.cone (C.cod f) \<chi>"
                  using f \<chi>.cone_axioms by blast
                hence "\<chi> j \<cdot>\<^sub>C f = E.cones_map f \<chi> j"
                  using \<chi>.is_extensional by simp
                also have "... = Adj.\<epsilon> (C.cod (E j)) \<cdot>\<^sub>C F (\<kappa> j)"
                  using j f by simp
                finally show ?thesis by blast
              qed
              thus ?thesis
                using f mem_Collect_eq restrict_apply Adj.F.is_extensional by simp
            qed
            also have "... = (G (Adj.\<epsilon> (C.cod (E j))) \<cdot>\<^sub>D Adj.\<eta> (D.cod (GE.map j))) \<cdot>\<^sub>D \<kappa> j"
              using j f Adj.\<eta>.naturality [of "\<kappa> j"] D.comp_assoc by auto
            also have "... = D.cod (\<kappa> j) \<cdot>\<^sub>D \<kappa> j"
              using j Adj.\<eta>\<epsilon>.triangle_G Adj.\<epsilon>_in_terms_of_\<psi> Adj.\<epsilon>o_def
                      Adj.\<eta>_in_terms_of_\<phi> Adj.\<eta>o_def Adj.unit_counit_G
              by fastforce
            also have "... = \<kappa> j"
              using j D.comp_cod_arr by simp
            finally show "GE.cones_map ?g ?G\<chi> j = \<kappa> j" by metis
          qed
          ultimately show "GE.cones_map ?g ?G\<chi> j = \<kappa> j" by auto
        qed
        ultimately have "\<guillemotleft>?g : b \<rightarrow>\<^sub>D G a\<guillemotright> \<and> GE.cones_map ?g ?G\<chi> = \<kappa>" by auto
        text\<open>
          It remains to be shown that @{term g} is the unique such arrow.
          Given any @{term g'} that transforms @{term G\<chi>} into @{term \<kappa>},
          its adjunct transforms @{term \<chi>} into @{term \<chi>'}.
          The adjunct of @{term g'} is therefore equal to @{term f},
          which implies @{term g'} = @{term g}.
\<close>
        moreover have "\<And>g'. \<guillemotleft>g' : b \<rightarrow>\<^sub>D G a\<guillemotright> \<and> GE.cones_map g' ?G\<chi> = \<kappa> \<Longrightarrow> g' = ?g"
        proof -
          fix g'
          assume g': "\<guillemotleft>g' : b \<rightarrow>\<^sub>D G a\<guillemotright> \<and> GE.cones_map g' ?G\<chi> = \<kappa>"
          have 1: "\<guillemotleft>\<psi> a g' : F b \<rightarrow>\<^sub>C a\<guillemotright>"
            using g' a \<psi>_in_hom by simp
          have 2: "E.cones_map (\<psi> a g') \<chi> = ?\<chi>'"
          proof
            fix j
            have "\<not>J.arr j \<Longrightarrow> E.cones_map (\<psi> a g') \<chi> j = ?\<chi>' j"
              using 1 \<chi>.cone_axioms by auto
            moreover have "J.arr j \<Longrightarrow> E.cones_map (\<psi> a g') \<chi> j = ?\<chi>' j"
            proof -
              fix j
              assume j: "J.arr j"
              have "E.cones_map (\<psi> a g') \<chi> j = \<chi> j \<cdot>\<^sub>C \<psi> a g'"
                using 1 \<chi>.cone_axioms \<chi>.is_extensional by auto
              also have "... = (\<chi> j \<cdot>\<^sub>C Adj.\<epsilon> a) \<cdot>\<^sub>C F g'"
                using j a g' Adj.\<psi>_in_terms_of_\<epsilon> C.comp_assoc Adj.\<epsilon>_def by auto
              also have "... = (Adj.\<epsilon> (C.cod (E j)) \<cdot>\<^sub>C F (G (\<chi> j))) \<cdot>\<^sub>C F g'"
                using j a g' Adj.\<epsilon>.naturality [of "\<chi> j"] by simp
              also have "... = Adj.\<epsilon> (C.cod (E j)) \<cdot>\<^sub>C F (\<kappa> j)"
                using j a g' G\<chi>.cone_axioms C.comp_assoc by auto
              finally show "E.cones_map (\<psi> a g') \<chi> j = ?\<chi>' j" by (simp add: j)
            qed
            ultimately show "E.cones_map (\<psi> a g') \<chi> j = ?\<chi>' j" by auto
          qed
          have "\<psi> a g' = f"
          proof -
            have "\<exists>!f. \<guillemotleft>f : F b \<rightarrow>\<^sub>C a\<guillemotright> \<and> E.cones_map f \<chi> = ?\<chi>'"
              using cone_\<chi>' \<chi>.is_universal by simp
            moreover have "\<guillemotleft>\<psi> a g' : F b \<rightarrow>\<^sub>C a\<guillemotright> \<and> E.cones_map (\<psi> a g') \<chi> = ?\<chi>'"
              using 1 2 by simp
            ultimately show ?thesis
              using ex1E [of "\<lambda>f. \<guillemotleft>f : F b \<rightarrow>\<^sub>C a\<guillemotright> \<and> E.cones_map f \<chi> = ?\<chi>'" "\<psi> a g' = f"]
              using 1 2 Adj.\<epsilon>.is_extensional C.comp_null(2) C.ex_un_null \<chi>.cone_axioms f
                    mem_Collect_eq restrict_apply
              by blast
          qed
          hence "\<phi> b (\<psi> a g') = \<phi> b f" by auto
          hence "g' = \<phi> b f" using \<chi>.ide_apex g' by (simp add: \<phi>_\<psi>)
          moreover have "?g = \<phi> b f" using f Adj.\<phi>_in_terms_of_\<eta> \<kappa>.ide_apex Adj.\<eta>_def by auto
          ultimately show "g' = ?g" by argo
        qed
        ultimately show "\<exists>!g. \<guillemotleft>g : b \<rightarrow>\<^sub>D G a\<guillemotright> \<and> GE.cones_map g ?G\<chi> = \<kappa>" by blast
      qed
      have "GE.limit_cone (G a) ?G\<chi>" ..
      thus ?thesis by auto
    qed

  end

  section "Special Kinds of Limits"

  subsection "Terminal Objects"

  text\<open>
   An object of a category @{term C} is a terminal object if and only if it is a limit of the
   empty diagram in @{term C}.
\<close>

  locale empty_diagram =
    diagram J C D
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and C :: "'c comp"      (infixr "\<cdot>" 55)
  and D :: "'j \<Rightarrow> 'c" +
  assumes is_empty: "\<not>J.arr j"
  begin

    lemma has_as_limit_iff_terminal:
    shows "has_as_limit a \<longleftrightarrow> C.terminal a"
    proof
      assume a: "has_as_limit a"
      show "C.terminal a"
      proof
        have "\<exists>\<chi>. limit_cone a \<chi>" using a by auto
        from this obtain \<chi> where \<chi>: "limit_cone a \<chi>" by blast
        interpret \<chi>: limit_cone J C D a \<chi> using \<chi> by auto
        have cone_\<chi>: "cone a \<chi>" ..
        show "C.ide a" using \<chi>.ide_apex by auto
        have 1: "\<chi> = (\<lambda>j. C.null)" using is_empty \<chi>.is_extensional by auto
        show "\<And>a'. C.ide a' \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright>"
        proof -
          fix a'
          assume a': "C.ide a'"
          interpret A': constant_functor J C a'
            apply unfold_locales using a' by auto
          let ?\<chi>' = "\<lambda>j. C.null"
          have cone_\<chi>': "cone a' ?\<chi>'"
            using a' is_empty apply unfold_locales by auto
          hence "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> cones_map f \<chi> = ?\<chi>'"
            using \<chi>.is_universal by force
          moreover have "\<And>f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<Longrightarrow> cones_map f \<chi> = ?\<chi>'"
            using 1 cone_\<chi> by auto
          ultimately show "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright>" by blast
        qed
      qed
      next
      assume a: "C.terminal a"
      show "has_as_limit a"
      proof -
        let ?\<chi> = "\<lambda>j. C.null"
        have "C.ide a" using a C.terminal_def by simp
        interpret A: constant_functor J C a
          apply unfold_locales using \<open>C.ide a\<close> by simp
        interpret \<chi>: cone J C D a ?\<chi>
          using \<open>C.ide a\<close> is_empty by (unfold_locales, auto)
        have cone_\<chi>: "cone a ?\<chi>" .. 
        have 1: "\<And>a' \<chi>'. cone a' \<chi>' \<Longrightarrow> \<chi>' = (\<lambda>j. C.null)"
        proof -
          fix a' \<chi>'
          assume \<chi>': "cone a' \<chi>'"
          interpret \<chi>': cone J C D a' \<chi>' using \<chi>' by auto
          show "\<chi>' = (\<lambda>j. C.null)"
            using is_empty \<chi>'.is_extensional by metis
        qed
        have "limit_cone a ?\<chi>"
        proof
          fix a' \<chi>'
          assume \<chi>': "cone a' \<chi>'"
          have 2: "\<chi>' = (\<lambda>j. C.null)" using 1 \<chi>' by simp
          interpret \<chi>': cone J C D a' \<chi>' using \<chi>' by auto
          have "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright>" using a C.terminal_def \<chi>'.ide_apex by simp
          moreover have "\<And>f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<Longrightarrow> cones_map f ?\<chi> = \<chi>'"
           using 1 2 cones_map_mapsto cone_\<chi> \<chi>'.cone_axioms mem_Collect_eq by blast
          ultimately show "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> cones_map f (\<lambda>j. C.null) = \<chi>'"
            by blast
        qed
        thus ?thesis by auto
      qed
    qed

  end

  subsection "Products"

  text\<open>
    A \emph{product} in a category @{term C} is a limit of a discrete diagram in @{term C}.
\<close>

  locale discrete_diagram =
    J: category J +
    diagram J C D
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and C :: "'c comp"      (infixr "\<cdot>" 55)
  and D :: "'j \<Rightarrow> 'c" +
  assumes is_discrete: "J.arr = J.ide"
  begin

    abbreviation mkCone
    where "mkCone F \<equiv> (\<lambda>j. if J.arr j then F j else C.null)"

    lemma cone_mkCone:
    assumes "C.ide a" and "\<And>j. J.arr j \<Longrightarrow> \<guillemotleft>F j : a \<rightarrow> D j\<guillemotright>"
    shows "cone a (mkCone F)"
    proof -
      interpret A: constant_functor J C a
        apply unfold_locales using assms(1) by auto
      show "cone a (mkCone F)"
        using assms(2) is_discrete
        apply unfold_locales
            apply auto
         apply (metis C.in_homE C.comp_cod_arr)
        using C.comp_arr_ide by fastforce
    qed

    lemma mkCone_cone:
    assumes "cone a \<pi>"
    shows "mkCone \<pi> = \<pi>"
    proof -
      interpret \<pi>: cone J C D a \<pi>
        using assms by auto
      show "mkCone \<pi> = \<pi>" using \<pi>.is_extensional by auto
    qed

  end

  text\<open>
    The following locale defines a discrete diagram in a category @{term C},
    given an index set @{term I} and a function @{term D} mapping @{term I}
    to objects of @{term C}.  Here we obtain the diagram shape @{term J}
    using a discrete category construction that allows us to directly identify
    the objects of @{term J} with the elements of @{term I}, however this construction
    can only be applied in case the set @{term I} is not the universe of its
    element type.
\<close>

  locale discrete_diagram_from_map =
    J: discrete_category I null +
    C: category C
  for I :: "'i set"
  and C :: "'c comp"      (infixr "\<cdot>" 55)
  and D :: "'i \<Rightarrow> 'c"
  and null :: 'i +
  assumes maps_to_ide: "i \<in> I \<Longrightarrow> C.ide (D i)"
  begin

    definition map
    where "map j \<equiv> if J.arr j then D j else C.null"

  end

  sublocale discrete_diagram_from_map \<subseteq> discrete_diagram J.comp C map
    using map_def maps_to_ide J.arr_char J.Null_not_in_Obj J.null_char
    by (unfold_locales, auto)

  locale product_cone =
    J: category J +
    C: category C +
    D: discrete_diagram J C D +
    limit_cone J C D a \<pi>
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and C :: "'c comp"      (infixr "\<cdot>" 55)
  and D :: "'j \<Rightarrow> 'c"
  and a :: 'c
  and \<pi> :: "'j \<Rightarrow> 'c"
  begin

    lemma is_cone:
    shows "D.cone a \<pi>" ..

    text\<open>
      The following versions of @{prop is_universal} and @{prop induced_arrowI}
      from the \<open>limit_cone\<close> locale are specialized to the case in which the
      underlying diagram is a product diagram.
\<close>

    lemma is_universal':
    assumes "C.ide b" and "\<And>j. J.arr j \<Longrightarrow> \<guillemotleft>F j: b \<rightarrow> D j\<guillemotright>"
    shows "\<exists>!f. \<guillemotleft>f : b \<rightarrow> a\<guillemotright> \<and> (\<forall>j. J.arr j \<longrightarrow> \<pi> j \<cdot> f = F j)"
    proof -
      let ?\<chi> = "D.mkCone F"
      interpret B: constant_functor J C b
        apply unfold_locales using assms(1) by auto
      have cone_\<chi>: "D.cone b ?\<chi>"
        using assms D.is_discrete
        apply unfold_locales
            apply auto
         apply (meson C.comp_ide_arr C.ide_in_hom C.seqI' D.preserves_ide)
        using C.comp_arr_dom by blast
      interpret \<chi>: cone J C D b ?\<chi> using cone_\<chi> by auto
      have "\<exists>!f. \<guillemotleft>f : b \<rightarrow> a\<guillemotright> \<and> D.cones_map f \<pi> = ?\<chi>"
        using cone_\<chi> is_universal by force
      moreover have
           "\<And>f. \<guillemotleft>f : b \<rightarrow> a\<guillemotright> \<Longrightarrow> D.cones_map f \<pi> = ?\<chi> \<longleftrightarrow> (\<forall>j. J.arr j \<longrightarrow> \<pi> j \<cdot> f = F j)"
      proof -
        fix f
        assume f: "\<guillemotleft>f : b \<rightarrow> a\<guillemotright>"
        show "D.cones_map f \<pi> = ?\<chi> \<longleftrightarrow> (\<forall>j. J.arr j \<longrightarrow> \<pi> j \<cdot> f = F j)"
        proof
          assume 1: "D.cones_map f \<pi> = ?\<chi>"
          show "\<forall>j. J.arr j \<longrightarrow> \<pi> j \<cdot> f = F j"
          proof -
            have "\<And>j. J.arr j \<Longrightarrow> \<pi> j \<cdot> f = F j"
            proof -
              fix j
              assume j: "J.arr j"
              have "\<pi> j \<cdot> f = D.cones_map f \<pi> j"
                using j f cone_axioms by force
              also have "... = F j" using j 1 by simp
              finally show "\<pi> j \<cdot> f = F j" by auto
            qed
            thus ?thesis by auto
          qed
          next
          assume 1: "\<forall>j. J.arr j \<longrightarrow> \<pi> j \<cdot> f = F j"
          show "D.cones_map f \<pi> = ?\<chi>"
            using 1 f is_cone \<chi>.is_extensional D.is_discrete is_cone cone_\<chi> by auto
        qed
      qed
      ultimately show ?thesis by blast
    qed

    abbreviation induced_arrow' :: "'c \<Rightarrow> ('j \<Rightarrow> 'c) \<Rightarrow> 'c"
    where "induced_arrow' b F \<equiv> induced_arrow b (D.mkCone F)"

    lemma induced_arrowI':
    assumes "C.ide b" and "\<And>j. J.arr j \<Longrightarrow> \<guillemotleft>F j : b \<rightarrow> D j\<guillemotright>"
    shows "\<And>j. J.arr j \<Longrightarrow> \<pi> j \<cdot> induced_arrow' b F = F j"
    proof -
      interpret B: constant_functor J C b
        apply unfold_locales using assms(1) by auto
      interpret \<chi>: cone J C D b \<open>D.mkCone F\<close>
        using assms D.cone_mkCone by blast
      have cone_\<chi>: "D.cone b (D.mkCone F)" ..
      hence 1: "D.cones_map (induced_arrow' b F) \<pi> = D.mkCone F"
        using induced_arrowI by blast
      fix j
      assume j: "J.arr j"
      have "\<pi> j \<cdot> induced_arrow' b F = D.cones_map (induced_arrow' b F) \<pi> j"
        using induced_arrowI(1) cone_\<chi> is_cone is_extensional by force
      also have "... = F j"
        using j 1 by auto
      finally show "\<pi> j \<cdot> induced_arrow' b F = F j"
        by auto
    qed

  end

  context discrete_diagram
  begin

    lemma product_coneI:
    assumes "limit_cone a \<pi>" 
    shows "product_cone J C D a \<pi>"
    proof -
      interpret L: limit_cone J C D a \<pi>
        using assms by auto
      show "product_cone J C D a \<pi>" ..
    qed

  end

  context category
  begin

    definition has_as_product
    where "has_as_product J D a \<equiv> (\<exists>\<pi>. product_cone J C D a \<pi>)"

    text\<open>
      A category has @{term I}-indexed products for an @{typ 'i}-set @{term I}
      if every @{term I}-indexed discrete diagram has a product.
      In order to reap the benefits of being able to directly identify the elements
      of a set I with the objects of discrete category it generates (thereby avoiding
      the use of coercion maps), it is necessary to assume that @{term "I \<noteq> UNIV"}.
      If we want to assert that a category has products indexed by the universe of
      some type @{typ 'i}, we have to pass to a larger type, such as @{typ "'i option"}.
\<close>

    definition has_products
    where "has_products (I :: 'i set) \<equiv>
             I \<noteq> UNIV \<and>
             (\<forall>J D. discrete_diagram J C D \<and> Collect (partial_magma.arr J) = I
                      \<longrightarrow> (\<exists>a. has_as_product J D a))"

    lemma ex_productE:
    assumes "\<exists>a. has_as_product J D a"
    obtains a \<pi> where "product_cone J C D a \<pi>"
      using assms has_as_product_def someI_ex [of "\<lambda>a. has_as_product J D a"] by metis

    lemma has_products_if_has_limits:
    assumes "has_limits (undefined :: 'j)" and "I \<noteq> (UNIV :: 'j set)"
    shows "has_products I"
    proof -
      have "\<And>J D. \<lbrakk> discrete_diagram J C D; Collect (partial_magma.arr J) = I \<rbrakk>
                   \<Longrightarrow> (\<exists>a. has_as_product J D a)"
      proof -
        fix J :: "'j comp" and D
        assume D: "discrete_diagram J C D"
        interpret J: category J
          using D discrete_diagram.axioms by auto
        interpret D: discrete_diagram J C D
          using D by auto
        assume J: "Collect J.arr = I"
        obtain a \<pi> where \<pi>: "D.limit_cone a \<pi>"
          using assms(1) J has_limits_def has_limits_of_shape_def [of J]
                D.diagram_axioms J.category_axioms
          by metis
        have "product_cone J C D a \<pi>"
          using \<pi> D.product_coneI by auto
        hence "has_as_product J D a"
          using has_as_product_def by blast
        thus "\<exists>a. has_as_product J D a"
          by auto
      qed
      thus ?thesis
        unfolding has_products_def using assms(2) by auto
    qed

  end

  subsection "Equalizers"

  text\<open>
    An \emph{equalizer} in a category @{term C} is a limit of a parallel pair
    of arrows in @{term C}.
\<close>

  locale parallel_pair_diagram =
    J: parallel_pair +
    C: category C
  for C :: "'c comp"      (infixr "\<cdot>" 55)
  and f0 :: 'c
  and f1 :: 'c +
  assumes is_parallel: "C.par f0 f1"
  begin

    no_notation J.comp   (infixr "\<cdot>" 55)
    notation J.comp      (infixr "\<cdot>\<^sub>J" 55)

    definition map
    where "map \<equiv> (\<lambda>j. if j = J.Zero then C.dom f0
                       else if j = J.One then C.cod f0
                       else if j = J.j0 then f0
                       else if j = J.j1 then f1
                       else C.null)"

    lemma map_simp:
    shows "map J.Zero = C.dom f0"
    and "map J.One = C.cod f0"
    and "map J.j0 = f0"
    and "map J.j1 = f1"
    proof -
      show "map J.Zero = C.dom f0"
        using map_def by metis
      show "map J.One = C.cod f0"
        using map_def J.Zero_not_eq_One by metis
      show "map J.j0 = f0"
        using map_def J.Zero_not_eq_j0 J.One_not_eq_j0 by metis
      show "map J.j1 = f1"
        using map_def J.Zero_not_eq_j1 J.One_not_eq_j1 J.j0_not_eq_j1 by metis
    qed

  end

  sublocale parallel_pair_diagram \<subseteq> diagram J.comp C map
    apply unfold_locales
        apply (simp add: J.arr_char map_def)
    using map_def is_parallel J.arr_char J.cod_simp J.dom_simp
       apply auto[2]
  proof -
    show 1: "\<And>j. J.arr j \<Longrightarrow> C.cod (map j) = map (J.cod j)"
    proof -
      fix j
      assume j: "J.arr j"
      show "C.cod (map j) = map (J.cod j)"
      proof -
        have "j = J.Zero \<or> j = J.One \<Longrightarrow> ?thesis" using is_parallel map_def by auto
        moreover have "j = J.j0 \<or> j = J.j1 \<Longrightarrow> ?thesis"
          using is_parallel map_def J.Zero_not_eq_j0 J.One_not_eq_j0 J.Zero_not_eq_One
                J.Zero_not_eq_j1 J.One_not_eq_j1 J.Zero_not_eq_One J.cod_simp
          by presburger
        ultimately show ?thesis using j J.arr_char by fast
      qed
    qed
    next
    fix j j'
    assume jj': "J.seq j' j"
    show "map (j' \<cdot>\<^sub>J j) = map j' \<cdot> map j"
    proof -
      have 1: "(j = J.Zero \<and> j' \<noteq> J.One) \<or> (j \<noteq> J.Zero \<and> j' = J.One)"
        using jj' J.seq_char by blast
      moreover have "j = J.Zero \<and> j' \<noteq> J.One \<Longrightarrow> ?thesis"
        using jj' map_def is_parallel J.arr_char J.cod_simp J.dom_simp J.seq_char
        by (metis (no_types, lifting) C.arr_dom_iff_arr C.comp_arr_dom C.dom_dom
            J.comp_arr_dom)
      moreover have "j \<noteq> J.Zero \<and> j' = J.One \<Longrightarrow> ?thesis"
        using jj' J.ide_char map_def J.Zero_not_eq_One is_parallel
        by (metis (no_types, lifting) C.arr_cod_iff_arr C.comp_arr_dom C.comp_cod_arr
            C.comp_ide_arr C.ext C.ide_cod J.comp_simp(2))
      ultimately show ?thesis by blast
    qed
  qed

  context parallel_pair_diagram
  begin

    definition mkCone
    where "mkCone e \<equiv> \<lambda>j. if J.arr j then if j = J.Zero then e else f0 \<cdot> e else C.null"

    abbreviation is_equalized_by
    where "is_equalized_by e \<equiv> C.seq f0 e \<and> f0 \<cdot> e = f1 \<cdot> e"

    abbreviation has_as_equalizer
    where "has_as_equalizer e \<equiv> limit_cone (C.dom e) (mkCone e)"

    lemma cone_mkCone:
    assumes "is_equalized_by e"
    shows "cone (C.dom e) (mkCone e)"
    proof -
      interpret E: constant_functor J.comp C \<open>C.dom e\<close>
        apply unfold_locales using assms by auto
      show "cone (C.dom e) (mkCone e)"
        using assms mkCone_def apply unfold_locales
            apply auto[2]
        using C.dom_comp C.seqE C.cod_comp J.Zero_not_eq_One J.arr_char' J.cod_char map_def
          apply (metis (no_types, lifting) C.not_arr_null parallel_pair.cod_simp(1) preserves_arr)
      proof -
        fix j
        assume j: "J.arr j"
        show "map j \<cdot> mkCone e (J.dom j) = mkCone e j"
        proof -
          have 1: "\<forall>a. if a = J.Zero then map a = C.dom f0
                        else if a = J.One then map a = C.cod f0
                        else if a = J.j0 then map a = f0
                        else if a = J.j1 then map a = f1
                        else map a = C.null"
            using map_def by auto
          hence 2: "map j = f1 \<or> j = J.One \<or> j = J.Zero \<or> j = J.j0"
            using j parallel_pair.arr_char by meson
          have "j = J.Zero \<or> map j \<cdot> mkCone e (J.dom j) = mkCone e j"
            using assms j 1 2 mkCone_def C.cod_comp
            by (metis (no_types, lifting) C.comp_cod_arr J.arr_char J.dom_simp(2-4) is_parallel)
          thus ?thesis
            using assms 1 j
            by (metis (no_types, lifting) C.comp_cod_arr C.seqE mkCone_def J.dom_simp(1))
        qed
        next
        show "\<And>j. J.arr j \<Longrightarrow> mkCone e (J.cod j) \<cdot> E.map j = mkCone e j"
        proof -
          fix j
          assume j: "J.arr j"
          have "J.cod j = J.Zero \<Longrightarrow> mkCone e (J.cod j) \<cdot> E.map j = mkCone e j"
            unfolding mkCone_def
            using assms j J.arr_char J.cod_char C.comp_arr_dom mkCone_def J.Zero_not_eq_One
            by (metis (no_types, lifting) C.seqE E.map_simp)
          moreover have "J.cod j \<noteq> J.Zero \<Longrightarrow> mkCone e (J.cod j) \<cdot> E.map j = mkCone e j"
            unfolding mkCone_def
            using assms j C.comp_arr_dom by auto
          ultimately show "mkCone e (J.cod j) \<cdot> E.map j = mkCone e j" by blast
        qed
      qed
    qed

    lemma is_equalized_by_cone:
    assumes "cone a \<chi>"
    shows "is_equalized_by (\<chi> (J.Zero))"
    proof -
      interpret \<chi>: cone J.comp C map a \<chi>
        using assms by auto
      show ?thesis
        using assms J.arr_char J.dom_char J.cod_char
              J.One_not_eq_j0 J.One_not_eq_j1 J.Zero_not_eq_j0 J.Zero_not_eq_j1 J.j0_not_eq_j1
        by (metis (no_types, lifting) Limit.cone_def \<chi>.is_natural_1 \<chi>.naturality
            \<chi>.preserves_reflects_arr constant_functor.map_simp map_simp(3) map_simp(4))
    qed

    lemma mkCone_cone:
    assumes "cone a \<chi>"
    shows "mkCone (\<chi> J.Zero) = \<chi>"
    proof -
      interpret \<chi>: cone J.comp C map a \<chi>
        using assms by auto
      have 1: "is_equalized_by (\<chi> J.Zero)"
        using assms is_equalized_by_cone by blast
      show ?thesis
      proof
        fix j
        have "j = J.Zero \<Longrightarrow> mkCone (\<chi> J.Zero) j = \<chi> j"
          using mkCone_def \<chi>.is_extensional by simp
        moreover have "j = J.One \<or> j = J.j0 \<or> j = J.j1 \<Longrightarrow> mkCone (\<chi> J.Zero) j = \<chi> j"
          using J.arr_char J.cod_char J.dom_char J.seq_char mkCone_def
                \<chi>.is_natural_1 \<chi>.is_natural_2 \<chi>.A.map_simp map_def
          by (metis (no_types, lifting) J.Zero_not_eq_j0 J.dom_simp(2))
        ultimately have "J.arr j \<Longrightarrow> mkCone (\<chi> J.Zero) j = \<chi> j"
          using J.arr_char by auto
        thus "mkCone (\<chi> J.Zero) j = \<chi> j"
          using mkCone_def \<chi>.is_extensional by fastforce
      qed
    qed

  end

  locale equalizer_cone =
    J: parallel_pair +
    C: category C +
    D: parallel_pair_diagram C f0 f1 +
    limit_cone J.comp C D.map "C.dom e" "D.mkCone e"
  for C :: "'c comp"      (infixr "\<cdot>" 55)
  and f0 :: 'c
  and f1 :: 'c
  and e :: 'c
  begin

    lemma equalizes:
    shows "D.is_equalized_by e"
    proof
      show 1: "C.seq f0 e"
      proof (intro C.seqI)
        show "C.arr e" using ide_apex C.arr_dom_iff_arr by fastforce
        show "C.arr f0"
          using D.map_simp D.preserves_arr J.arr_char by metis
        show "C.dom f0 = C.cod e"
          using J.arr_char J.ide_char D.mkCone_def D.map_simp preserves_cod [of J.Zero]
          by auto
      qed
      hence 2: "C.seq f1 e"
        using D.is_parallel by fastforce
      show "f0 \<cdot> e = f1 \<cdot> e"
        using D.map_simp D.mkCone_def J.arr_char naturality [of J.j0] naturality [of J.j1]
        by force
    qed

    lemma is_universal':
    assumes "D.is_equalized_by e'"
    shows "\<exists>!h. \<guillemotleft>h : C.dom e' \<rightarrow> C.dom e\<guillemotright> \<and> e \<cdot> h = e'"
    proof -
      have "D.cone (C.dom e') (D.mkCone e')"
        using assms D.cone_mkCone by blast
      moreover have 0: "D.cone (C.dom e) (D.mkCone e)" ..
      ultimately have 1: "\<exists>!h. \<guillemotleft>h : C.dom e' \<rightarrow> C.dom e\<guillemotright> \<and>
                               D.cones_map h (D.mkCone e) = D.mkCone e'"
        using is_universal [of "C.dom e'" "D.mkCone e'"] by auto
      have 2: "\<And>h. \<guillemotleft>h : C.dom e' \<rightarrow> C.dom e\<guillemotright> \<Longrightarrow>
                    D.cones_map h (D.mkCone e) = D.mkCone e' \<longleftrightarrow> e \<cdot> h = e'"
      proof -
        fix h
        assume h: "\<guillemotleft>h : C.dom e' \<rightarrow> C.dom e\<guillemotright>"
        show "D.cones_map h (D.mkCone e) = D.mkCone e' \<longleftrightarrow> e \<cdot> h = e'"
        proof
          assume 3: "D.cones_map h (D.mkCone e) = D.mkCone e'"
          show "e \<cdot> h = e'"
          proof -
            have "e' = D.mkCone e' J.Zero"
              using D.mkCone_def J.arr_char by simp
            also have "... = D.cones_map h (D.mkCone e) J.Zero"
              using 3 by simp
            also have "... = e \<cdot> h"
              using 0 h D.mkCone_def J.arr_char by auto
            finally show ?thesis by auto
          qed
          next
          assume e': "e \<cdot> h = e'"
          show "D.cones_map h (D.mkCone e) = D.mkCone e'"
          proof
            fix j
            have "\<not>J.arr j \<Longrightarrow> D.cones_map h (D.mkCone e) j = D.mkCone e' j"
              using h cone_axioms D.mkCone_def by auto
            moreover have "j = J.Zero \<Longrightarrow> D.cones_map h (D.mkCone e) j = D.mkCone e' j"
              using h e' cone_\<chi> D.mkCone_def J.arr_char [of J.Zero] by force
            moreover have
                "J.arr j \<and> j \<noteq> J.Zero \<Longrightarrow> D.cones_map h (D.mkCone e) j = D.mkCone e' j"
            proof -
              assume j: "J.arr j \<and> j \<noteq> J.Zero"
              have "D.cones_map h (D.mkCone e) j = C (D.mkCone e j) h"
                using j h equalizes D.mkCone_def D.cone_mkCone J.arr_char
                      J.Zero_not_eq_One J.Zero_not_eq_j0 J.Zero_not_eq_j1
                by auto
              also have "... = (f0 \<cdot> e) \<cdot> h"
                using j D.mkCone_def J.arr_char J.Zero_not_eq_One J.Zero_not_eq_j0
                      J.Zero_not_eq_j1
                by auto
              also have "... = f0 \<cdot> e \<cdot> h"
                using h equalizes C.comp_assoc by blast
              also have "... = D.mkCone e' j"
                using j e' h equalizes D.mkCone_def J.arr_char [of J.One] J.Zero_not_eq_One
                by auto
              finally show ?thesis by auto
            qed
            ultimately show "D.cones_map h (D.mkCone e) j = D.mkCone e' j" by blast
          qed
        qed
      qed
      thus ?thesis using 1 by blast
    qed

    lemma induced_arrowI':
    assumes "D.is_equalized_by e'"
    shows "\<guillemotleft>induced_arrow (C.dom e') (D.mkCone e') : C.dom e' \<rightarrow> C.dom e\<guillemotright>"
    and "e \<cdot> induced_arrow (C.dom e') (D.mkCone e') = e'"
    proof -
      interpret A': constant_functor J.comp C \<open>C.dom e'\<close>
        using assms by (unfold_locales, auto)
      have cone: "D.cone (C.dom e') (D.mkCone e')"
        using assms D.cone_mkCone [of e'] by blast
      have "e \<cdot> induced_arrow (C.dom e') (D.mkCone e') =
              D.cones_map (induced_arrow (C.dom e') (D.mkCone e')) (D.mkCone e) J.Zero"
        using cone induced_arrowI(1) D.mkCone_def J.arr_char cone_\<chi> by force
      also have "... = e'"
      proof -
        have
            "D.cones_map (induced_arrow (C.dom e') (D.mkCone e')) (D.mkCone e) = D.mkCone e'"
          using cone induced_arrowI by blast
        thus ?thesis
          using J.arr_char D.mkCone_def by simp
      qed
      finally have 1: "e \<cdot> induced_arrow (C.dom e') (D.mkCone e') = e'"
        by auto
      show "\<guillemotleft>induced_arrow (C.dom e') (D.mkCone e') : C.dom e' \<rightarrow> C.dom e\<guillemotright>"
        using 1 cone induced_arrowI by simp
      show "e \<cdot> induced_arrow (C.dom e') (D.mkCone e') = e'"
        using 1 cone induced_arrowI by simp
    qed

  end

  context category
  begin

    definition has_as_equalizer
    where "has_as_equalizer f0 f1 e \<equiv> par f0 f1 \<and> parallel_pair_diagram.has_as_equalizer C f0 f1 e"

    definition has_equalizers
    where "has_equalizers = (\<forall>f0 f1. par f0 f1 \<longrightarrow> (\<exists>e. has_as_equalizer f0 f1 e))"

  end

  section "Limits by Products and Equalizers"
 
  text\<open>
    A category with equalizers has limits of shape @{term J} if it has products
    indexed by the set of arrows of @{term J} and the set of objects of @{term J}.
    The proof is patterned after \cite{MacLane}, Theorem 2, page 109:
    \begin{quotation}
       ``The limit of \<open>F: J \<rightarrow> C\<close> is the equalizer \<open>e\<close>
       of \<open>f, g: \<Pi>\<^sub>i F\<^sub>i \<rightarrow> \<Pi>\<^sub>u F\<^sub>c\<^sub>o\<^sub>d \<^sub>u (u \<in> arr J, i \<in> J)\<close>
       where \<open>p\<^sub>u f = p\<^sub>c\<^sub>o\<^sub>d \<^sub>u\<close>, \<open>p\<^sub>u g = F\<^sub>u o p\<^sub>d\<^sub>o\<^sub>m \<^sub>u\<close>;
       the limiting cone \<open>\<mu>\<close> is \<open>\<mu>\<^sub>j = p\<^sub>j e\<close>, for \<open>j \<in> J\<close>.''
    \end{quotation}
\<close>

  locale category_with_equalizers =
    category C
  for C :: "'c comp"      (infixr "\<cdot>" 55) +
  assumes has_equalizers: "has_equalizers"
  begin

    lemma has_limits_if_has_products:
    fixes J :: "'j comp"  (infixr "\<cdot>\<^sub>J" 55)
    assumes "category J" and "has_products (Collect (partial_magma.ide J))"
    and "has_products (Collect (partial_magma.arr J))"
    shows "has_limits_of_shape J"
    proof (unfold has_limits_of_shape_def)
      interpret J: category J using assms(1) by auto
      have "\<And>D. diagram J C D \<Longrightarrow> (\<exists>a \<chi>. limit_cone J C D a \<chi>)"
      proof -
        fix D
        assume D: "diagram J C D"
        interpret D: diagram J C D using D by auto

        text\<open>
          First, construct the two required products and their cones.
\<close>
        interpret Obj: discrete_category \<open>Collect J.ide\<close> J.null
          using J.not_arr_null J.ideD(1) mem_Collect_eq by (unfold_locales, blast)
        interpret \<Delta>o: discrete_diagram_from_map \<open>Collect J.ide\<close> C D J.null
          using D.preserves_ide by (unfold_locales, auto)
        have "\<exists>p. has_as_product Obj.comp \<Delta>o.map p"
          using assms(2) \<Delta>o.diagram_axioms has_products_def Obj.arr_char
          by (metis (no_types, lifting) Collect_cong \<Delta>o.discrete_diagram_axioms mem_Collect_eq)
        from this obtain \<Pi>o \<pi>o where \<pi>o: "product_cone Obj.comp C \<Delta>o.map \<Pi>o \<pi>o"
           using ex_productE [of Obj.comp \<Delta>o.map] by auto
        interpret \<pi>o: product_cone Obj.comp C \<Delta>o.map \<Pi>o \<pi>o using \<pi>o by auto
        have \<pi>o_in_hom: "\<And>j. Obj.arr j \<Longrightarrow> \<guillemotleft>\<pi>o j : \<Pi>o \<rightarrow> D j\<guillemotright>"
          using \<pi>o.preserves_dom \<pi>o.preserves_cod \<Delta>o.map_def by auto

        interpret Arr: discrete_category \<open>Collect J.arr\<close> J.null
          using J.not_arr_null by (unfold_locales, blast)
        interpret \<Delta>a: discrete_diagram_from_map \<open>Collect J.arr\<close> C \<open>D o J.cod\<close> J.null
          by (unfold_locales, auto)
        have "\<exists>p. has_as_product Arr.comp \<Delta>a.map p"
          using assms(3) has_products_def [of "Collect J.arr"] \<Delta>a.discrete_diagram_axioms
          by blast
        from this obtain \<Pi>a \<pi>a where \<pi>a: "product_cone Arr.comp C \<Delta>a.map \<Pi>a \<pi>a"
          using ex_productE [of Arr.comp \<Delta>a.map] by auto
        interpret \<pi>a: product_cone Arr.comp C \<Delta>a.map \<Pi>a \<pi>a using \<pi>a by auto
        have \<pi>a_in_hom: "\<And>j. Arr.arr j \<Longrightarrow> \<guillemotleft>\<pi>a j : \<Pi>a \<rightarrow> D (J.cod j)\<guillemotright>"
          using \<pi>a.preserves_cod \<pi>a.preserves_dom \<Delta>a.map_def by auto

        text\<open>
           Next, construct a parallel pair of arrows \<open>f, g: \<Pi>o \<rightarrow> \<Pi>a\<close>
           that expresses the commutativity constraints imposed by the diagram.
\<close>
        interpret \<Pi>o: constant_functor Arr.comp C \<Pi>o
          using \<pi>o.ide_apex by (unfold_locales, auto)
        let ?\<chi> = "\<lambda>j. if Arr.arr j then \<pi>o (J.cod j) else null"
        interpret \<chi>: cone Arr.comp C \<Delta>a.map \<Pi>o ?\<chi>
          using \<pi>o.ide_apex \<pi>o_in_hom \<Delta>a.map_def \<Delta>o.map_def \<Delta>o.is_discrete \<pi>o.is_natural_2
                comp_cod_arr
          by (unfold_locales, auto)

        let ?f = "\<pi>a.induced_arrow \<Pi>o ?\<chi>"
        have f_in_hom: "\<guillemotleft>?f : \<Pi>o \<rightarrow> \<Pi>a\<guillemotright>"
          using \<chi>.cone_axioms \<pi>a.induced_arrowI by blast
        have f_map: "\<Delta>a.cones_map ?f \<pi>a = ?\<chi>"
          using \<chi>.cone_axioms \<pi>a.induced_arrowI by blast
        have ff: "\<And>j. J.arr j \<Longrightarrow> \<pi>a j \<cdot> ?f = \<pi>o (J.cod j)"
        proof -
          fix j
          assume j: "J.arr j"
          have "\<pi>a j \<cdot> ?f = \<Delta>a.cones_map ?f \<pi>a j"
            using f_in_hom \<pi>a.is_cone \<pi>a.is_extensional by auto
          also have "... = \<pi>o (J.cod j)"
            using j f_map by fastforce
          finally show "\<pi>a j \<cdot> ?f = \<pi>o (J.cod j)" by auto
        qed

        let ?\<chi>' = "\<lambda>j. if Arr.arr j then D j \<cdot> \<pi>o (J.dom j) else null"
        interpret \<chi>': cone Arr.comp C \<Delta>a.map \<Pi>o ?\<chi>'
          using \<pi>o.ide_apex \<pi>o_in_hom \<Delta>o.map_def \<Delta>a.map_def comp_arr_dom comp_cod_arr
          by (unfold_locales, auto)
        let ?g = "\<pi>a.induced_arrow \<Pi>o ?\<chi>'"
        have g_in_hom: "\<guillemotleft>?g : \<Pi>o \<rightarrow> \<Pi>a\<guillemotright>"
          using \<chi>'.cone_axioms \<pi>a.induced_arrowI by blast
        have g_map: "\<Delta>a.cones_map ?g \<pi>a = ?\<chi>'"
          using \<chi>'.cone_axioms \<pi>a.induced_arrowI by blast
        have gg: "\<And>j. J.arr j \<Longrightarrow> \<pi>a j \<cdot> ?g = D j \<cdot> \<pi>o (J.dom j)"
        proof -
          fix j
          assume j: "J.arr j"
          have "\<pi>a j \<cdot> ?g = \<Delta>a.cones_map ?g \<pi>a j"
            using g_in_hom \<pi>a.is_cone \<pi>a.is_extensional by force
          also have "... = D j \<cdot> \<pi>o (J.dom j)"
            using j g_map by fastforce
          finally show "\<pi>a j \<cdot> ?g = D j \<cdot> \<pi>o (J.dom j)" by auto
        qed

        interpret PP: parallel_pair_diagram C ?f ?g
          using f_in_hom g_in_hom
          by (elim in_homE, unfold_locales, auto)

        from PP.is_parallel obtain e where equ: "PP.has_as_equalizer e"
          using has_equalizers has_equalizers_def has_as_equalizer_def by blast
        interpret EQU: limit_cone PP.J.comp C PP.map \<open>dom e\<close> \<open>PP.mkCone e\<close>
          using equ by auto
        interpret EQU: equalizer_cone C ?f ?g e ..

        text\<open>
          An arrow @{term h} with @{term "cod h = \<Pi>o"} equalizes @{term f} and @{term g}
          if and only if it satisfies the commutativity condition required for a cone over
          @{term D}.
\<close>
        have E: "\<And>h. \<guillemotleft>h : dom h \<rightarrow> \<Pi>o\<guillemotright> \<Longrightarrow>
                   ?f \<cdot> h = ?g \<cdot> h \<longleftrightarrow> (\<forall>j. J.arr j \<longrightarrow> ?\<chi> j \<cdot> h = ?\<chi>' j \<cdot> h)"
        proof
          fix h
          assume h: "\<guillemotleft>h : dom h \<rightarrow> \<Pi>o\<guillemotright>"
          show "?f \<cdot> h = ?g \<cdot> h \<Longrightarrow> \<forall>j. J.arr j \<longrightarrow> ?\<chi> j \<cdot> h = ?\<chi>' j \<cdot> h"
          proof -
            assume E: "?f \<cdot> h = ?g \<cdot> h"
            have "\<And>j. J.arr j \<Longrightarrow> ?\<chi> j \<cdot> h = ?\<chi>' j \<cdot> h"
            proof -
              fix j
              assume j: "J.arr j"
              have "?\<chi> j \<cdot> h = \<Delta>a.cones_map ?f \<pi>a j \<cdot> h"
                using j f_map by fastforce
              also have "... = \<pi>a j \<cdot> ?f \<cdot> h"
                using j f_in_hom \<Delta>a.map_def \<pi>a.cone_\<chi> comp_assoc by auto
              also have "... = \<pi>a j \<cdot> ?g \<cdot> h"
                using j E by simp
              also have "... = \<Delta>a.cones_map ?g \<pi>a j \<cdot> h"
                using j g_in_hom \<Delta>a.map_def \<pi>a.cone_\<chi> comp_assoc by auto
              also have "... = ?\<chi>' j \<cdot> h"
                using j g_map by force
              finally show "?\<chi> j \<cdot> h = ?\<chi>' j \<cdot> h" by auto
            qed
            thus "\<forall>j. J.arr j \<longrightarrow> ?\<chi> j \<cdot> h = ?\<chi>' j \<cdot> h" by blast
          qed
          show "\<forall>j. J.arr j \<longrightarrow> ?\<chi> j \<cdot> h = ?\<chi>' j \<cdot> h \<Longrightarrow> ?f \<cdot> h = ?g \<cdot> h"
          proof -
            assume 1: "\<forall>j. J.arr j \<longrightarrow> ?\<chi> j \<cdot> h = ?\<chi>' j \<cdot> h"
            have 2: "\<And>j. j \<in> Collect J.arr \<Longrightarrow> \<pi>a j \<cdot> ?f \<cdot> h = \<pi>a j \<cdot> ?g \<cdot> h"
            proof -
              fix j
              assume j: "j \<in> Collect J.arr"
              have "\<pi>a j \<cdot> ?f \<cdot> h = (\<pi>a j \<cdot> ?f) \<cdot> h"
                using comp_assoc by simp
              also have "... = ?\<chi> j \<cdot> h"
              proof -
                have "\<pi>a j \<cdot> ?f = \<Delta>a.cones_map ?f \<pi>a j"
                  using j f_in_hom \<pi>a.cone_axioms \<Delta>a.map_def \<pi>a.cone_\<chi> by auto
                thus ?thesis using f_map by fastforce
              qed
              also have "... = ?\<chi>' j \<cdot> h"
                using 1 j by auto
              also have "... = (\<pi>a j \<cdot> ?g) \<cdot> h"
              proof -
                have "\<pi>a j \<cdot> ?g = \<Delta>a.cones_map ?g \<pi>a j"
                  using j g_in_hom \<pi>a.cone_axioms \<Delta>a.map_def \<pi>a.cone_\<chi> by auto
                thus ?thesis using g_map by simp
              qed
              also have "... = \<pi>a j \<cdot> ?g \<cdot> h"
                using comp_assoc by simp
              finally show "\<pi>a j \<cdot> ?f \<cdot> h = \<pi>a j \<cdot> ?g \<cdot> h"
                by auto
            qed
            show "C ?f h = C ?g h"
            proof -
              have "\<And>j. Arr.arr j \<Longrightarrow> \<guillemotleft>\<pi>a j \<cdot> ?f \<cdot> h : dom h \<rightarrow> \<Delta>a.map j\<guillemotright>"
                using f_in_hom h \<pi>a_in_hom by (elim in_homE, auto)
              hence 3: "\<exists>!k. \<guillemotleft>k : dom h \<rightarrow> \<Pi>a\<guillemotright> \<and> (\<forall>j. Arr.arr j \<longrightarrow> \<pi>a j \<cdot> k = \<pi>a j \<cdot> ?f \<cdot> h)"
                using h \<pi>a \<pi>a.is_universal' [of "dom h" "\<lambda>j. \<pi>a j \<cdot> ?f \<cdot> h"] \<Delta>a.map_def
                      ide_dom [of h]
                by blast
              have 4: "\<And>P x x'. \<exists>!k. P k x \<Longrightarrow> P x x \<Longrightarrow> P x' x \<Longrightarrow> x' = x" by auto
              let ?P = "\<lambda> k x. \<guillemotleft>k : dom h \<rightarrow> \<Pi>a\<guillemotright> \<and>
                               (\<forall>j. j \<in> Collect J.arr \<longrightarrow> \<pi>a j \<cdot> k = \<pi>a j \<cdot> x)"
              have "?P (?g \<cdot> h) (?g \<cdot> h)"
                using g_in_hom h by force
              moreover have "?P (?f \<cdot> h) (?g \<cdot> h)"
                using 2 f_in_hom g_in_hom h by force
              ultimately show ?thesis
                using 3 4 [of ?P "?f \<cdot> h" "?g \<cdot> h"] by auto
            qed
          qed
        qed
        have E': "\<And>e. \<guillemotleft>e : dom e \<rightarrow> \<Pi>o\<guillemotright> \<Longrightarrow>
                   ?f \<cdot> e = ?g \<cdot> e \<longleftrightarrow>
                   (\<forall>j. J.arr j \<longrightarrow>
                           (D (J.cod j) \<cdot> \<pi>o (J.cod j) \<cdot> e) \<cdot> dom e = D j \<cdot> \<pi>o (J.dom j) \<cdot> e)"
        proof -
          have 1: "\<And>e j. \<guillemotleft>e : dom e \<rightarrow> \<Pi>o\<guillemotright> \<Longrightarrow> J.arr j \<Longrightarrow>
                          ?\<chi> j \<cdot> e = (D (J.cod j) \<cdot> \<pi>o (J.cod j) \<cdot> e) \<cdot> dom e"
          proof -
            fix e j
            assume e: "\<guillemotleft>e : dom e \<rightarrow> \<Pi>o\<guillemotright>"
            assume j: "J.arr j"
            have "\<guillemotleft>\<pi>o (J.cod j) \<cdot> e : dom e \<rightarrow> D (J.cod j)\<guillemotright>"
              using e j \<pi>o_in_hom by auto
            thus "?\<chi> j \<cdot> e = (D (J.cod j) \<cdot> \<pi>o (J.cod j) \<cdot> e) \<cdot> dom e"
              using j comp_arr_dom comp_cod_arr by (elim in_homE, auto)
          qed
          have 2: "\<And>e j. \<guillemotleft>e : dom e \<rightarrow> \<Pi>o\<guillemotright> \<Longrightarrow> J.arr j \<Longrightarrow> ?\<chi>' j \<cdot> e = D j \<cdot> \<pi>o (J.dom j) \<cdot> e"
          proof -
            fix e j
            assume e: "\<guillemotleft>e : dom e \<rightarrow> \<Pi>o\<guillemotright>"
            assume j: "J.arr j"
            show "?\<chi>' j \<cdot> e = D j \<cdot> \<pi>o (J.dom j) \<cdot> e"
              using j comp_assoc by fastforce
          qed
          show "\<And>e. \<guillemotleft>e : dom e \<rightarrow> \<Pi>o\<guillemotright> \<Longrightarrow>
                   ?f \<cdot> e = ?g \<cdot> e \<longleftrightarrow>
                     (\<forall>j. J.arr j \<longrightarrow>
                           (D (J.cod j) \<cdot> \<pi>o (J.cod j) \<cdot> e) \<cdot> dom e = D j \<cdot> \<pi>o (J.dom j) \<cdot> e)"
            using 1 2 E by presburger
        qed
        text\<open>
          The composites of @{term e} with the projections from the product @{term \<Pi>o}
          determine a limit cone @{term \<mu>} for @{term D}.  The component of @{term \<mu>}
          at an object @{term j} of @{term[source=true] J} is the composite @{term "C (\<pi>o j) e"}.
          However, we need to extend @{term \<mu>} to all arrows @{term j} of @{term[source=true] J},
          so the correct definition is @{term "\<mu> j = C (D j) (C (\<pi>o (J.dom j)) e)"}.
\<close>
        have e_in_hom: "\<guillemotleft>e : dom e \<rightarrow> \<Pi>o\<guillemotright>"
          using EQU.equalizes f_in_hom in_homI
          by (metis (no_types, lifting) seqE in_homE)
        have e_map: "C ?f e = C ?g e"
          using EQU.equalizes f_in_hom in_homI by fastforce
        interpret domE: constant_functor J C \<open>dom e\<close>
          using e_in_hom by (unfold_locales, auto)
        let ?\<mu> = "\<lambda>j. if J.arr j then D j \<cdot> \<pi>o (J.dom j) \<cdot> e else null"
        have \<mu>: "\<And>j. J.arr j \<Longrightarrow> \<guillemotleft>?\<mu> j : dom e \<rightarrow> D (J.cod j)\<guillemotright>"
        proof -
          fix j
          assume j: "J.arr j"
          show "\<guillemotleft>?\<mu> j : dom e \<rightarrow> D (J.cod j)\<guillemotright>"
            using j e_in_hom \<pi>o_in_hom [of "J.dom j"] by auto
        qed
        interpret \<mu>: cone J C D \<open>dom e\<close> ?\<mu>
          apply unfold_locales
              apply simp
        proof -
          fix j
          assume j: "J.arr j"
          show "dom (?\<mu> j) = domE.map (J.dom j)" using j \<mu> domE.map_simp by force
          show "cod (?\<mu> j) = D (J.cod j)" using j \<mu> D.preserves_cod by blast
          show "D j \<cdot> ?\<mu> (J.dom j) = ?\<mu> j"
            using j \<mu> [of "J.dom j"] comp_cod_arr apply simp
            by (elim in_homE, auto)
          show "?\<mu> (J.cod j) \<cdot> domE.map j = ?\<mu> j"
            using j e_map E' by (simp add: e_in_hom)
        qed
        text\<open>
          If @{term \<tau>} is any cone over @{term D} then @{term \<tau>} restricts to a cone over
          @{term \<Delta>o} for which the induced arrow to @{term \<Pi>o} equalizes @{term f} and @{term g}.
\<close>
        have R: "\<And>a \<tau>. cone J C D a \<tau> \<Longrightarrow>
                        cone Obj.comp C \<Delta>o.map a (\<Delta>o.mkCone \<tau>) \<and>
                        ?f \<cdot> \<pi>o.induced_arrow a (\<Delta>o.mkCone \<tau>)
                           = ?g \<cdot> \<pi>o.induced_arrow a (\<Delta>o.mkCone \<tau>)"
        proof -
          fix a \<tau>
          assume cone_\<tau>: "cone J C D a \<tau>"
          interpret \<tau>: cone J C D a \<tau> using cone_\<tau> by auto
          interpret A: constant_functor Obj.comp C a
            using \<tau>.ide_apex by (unfold_locales, auto)
          interpret \<tau>o: cone Obj.comp C \<Delta>o.map a \<open>\<Delta>o.mkCone \<tau>\<close>
            using A.value_is_ide \<Delta>o.map_def comp_cod_arr comp_arr_dom
            by (unfold_locales, auto)
          let ?e = "\<pi>o.induced_arrow a (\<Delta>o.mkCone \<tau>)"
          have mkCone_\<tau>: "\<Delta>o.mkCone \<tau> \<in> \<Delta>o.cones a"
          proof -
            have "\<And>j. Obj.arr j \<Longrightarrow> \<guillemotleft>\<tau> j : a \<rightarrow> \<Delta>o.map j\<guillemotright>"
              using Obj.arr_char \<tau>.A.map_def \<Delta>o.map_def by force
            thus ?thesis
              using \<tau>.ide_apex \<Delta>o.cone_mkCone by simp
          qed
          have e: "\<guillemotleft>?e : a \<rightarrow> \<Pi>o\<guillemotright>"
            using mkCone_\<tau> \<pi>o.induced_arrowI by simp
          have ee: "\<And>j. J.ide j \<Longrightarrow> \<pi>o j \<cdot> ?e = \<tau> j"
          proof -
            fix j
            assume j: "J.ide j"
            have "\<pi>o j \<cdot> ?e = \<Delta>o.cones_map ?e \<pi>o j"
              using j e \<pi>o.cone_axioms by force
            also have "... = \<Delta>o.mkCone \<tau> j"
              using j mkCone_\<tau> \<pi>o.induced_arrowI [of "\<Delta>o.mkCone \<tau>" a] by fastforce
            also have "... = \<tau> j"
              using j by simp
            finally show "\<pi>o j \<cdot> ?e = \<tau> j" by auto
          qed
          have "\<And>j. J.arr j \<Longrightarrow>
                      (D (J.cod j) \<cdot> \<pi>o (J.cod j) \<cdot> ?e) \<cdot> dom ?e = D j \<cdot> \<pi>o (J.dom j) \<cdot> ?e"
          proof -
            fix j
            assume j: "J.arr j"
            have 1: "\<guillemotleft>\<pi>o (J.cod j) : \<Pi>o \<rightarrow> D (J.cod j)\<guillemotright>" using j \<pi>o_in_hom by simp
            have 2: "(D (J.cod j) \<cdot> \<pi>o (J.cod j) \<cdot> ?e) \<cdot> dom ?e
                        = D (J.cod j) \<cdot> \<pi>o (J.cod j) \<cdot> ?e"
            proof -
              have "seq (D (J.cod j)) (\<pi>o (J.cod j))"
                using j 1 by auto
              moreover have "seq (\<pi>o (J.cod j)) ?e"
                using j e by fastforce
              ultimately show ?thesis using comp_arr_dom by auto
            qed
            also have 3: "... = \<pi>o (J.cod j) \<cdot> ?e"
              using j e 1 comp_cod_arr by (elim in_homE, auto)
            also have "... = D j \<cdot> \<pi>o (J.dom j) \<cdot> ?e"
              using j e ee 2 3 \<tau>.naturality \<tau>.A.map_simp \<tau>.ide_apex comp_cod_arr by auto
            finally show "(D (J.cod j) \<cdot> \<pi>o (J.cod j) \<cdot> ?e) \<cdot> dom ?e = D j \<cdot> \<pi>o (J.dom j) \<cdot> ?e"
              by auto
          qed
          hence "C ?f ?e = C ?g ?e"
            using E' \<pi>o.induced_arrowI \<tau>o.cone_axioms mem_Collect_eq by blast
          thus "cone Obj.comp C \<Delta>o.map a (\<Delta>o.mkCone \<tau>) \<and> C ?f ?e = C ?g ?e"
            using \<tau>o.cone_axioms by auto
        qed
        text\<open>
          Finally, show that @{term \<mu>} is a limit cone.
\<close>
        interpret \<mu>: limit_cone J C D \<open>dom e\<close> ?\<mu>
        proof
          fix a \<tau>
          assume cone_\<tau>: "cone J C D a \<tau>"
          interpret \<tau>: cone J C D a \<tau> using cone_\<tau> by auto
          interpret A: constant_functor Obj.comp C a
            apply unfold_locales using \<tau>.ide_apex by auto
          have cone_\<tau>o: "cone Obj.comp C \<Delta>o.map a (\<Delta>o.mkCone \<tau>)"
            using A.value_is_ide \<Delta>o.map_def D.preserves_ide comp_cod_arr comp_arr_dom
                  \<tau>.preserves_hom
            by (unfold_locales, auto)
          show "\<exists>!h. \<guillemotleft>h : a \<rightarrow> dom e\<guillemotright> \<and> D.cones_map h ?\<mu> = \<tau>"
          proof
            let ?e' = "\<pi>o.induced_arrow a (\<Delta>o.mkCone \<tau>)"
            have e'_in_hom: "\<guillemotleft>?e' : a \<rightarrow> \<Pi>o\<guillemotright>"
              using cone_\<tau> R \<pi>o.induced_arrowI by auto
            have e'_map: "?f \<cdot> ?e' = ?g \<cdot> ?e' \<and> \<Delta>o.cones_map ?e' \<pi>o = \<Delta>o.mkCone \<tau>"
              using cone_\<tau> R \<pi>o.induced_arrowI [of "\<Delta>o.mkCone \<tau>" a] by auto
            have equ: "PP.is_equalized_by ?e'"
              using e'_map e'_in_hom f_in_hom seqI' by blast
            let ?h = "EQU.induced_arrow a (PP.mkCone ?e')"
            have h_in_hom: "\<guillemotleft>?h : a \<rightarrow> dom e\<guillemotright>"
              using EQU.induced_arrowI PP.cone_mkCone [of ?e'] e'_in_hom equ by fastforce
            have h_map: "PP.cones_map ?h (PP.mkCone e) = PP.mkCone ?e'"
              using EQU.induced_arrowI [of "PP.mkCone ?e'" a] PP.cone_mkCone [of ?e']
                    e'_in_hom equ
              by fastforce
            have 3: "D.cones_map ?h ?\<mu> = \<tau>"
            proof
              fix j
              have "\<not>J.arr j \<Longrightarrow> D.cones_map ?h ?\<mu> j = \<tau> j"
                using h_in_hom \<mu>.cone_axioms cone_\<tau> \<tau>.is_extensional by force
              moreover have "J.arr j \<Longrightarrow> D.cones_map ?h ?\<mu> j = \<tau> j"
              proof -
                fix j
                assume j: "J.arr j"
                have 1: "\<guillemotleft>\<pi>o (J.dom j) \<cdot> e : dom e \<rightarrow> D (J.dom j)\<guillemotright>"
                  using j e_in_hom \<pi>o_in_hom [of "J.dom j"] by auto
                have "D.cones_map ?h ?\<mu> j = ?\<mu> j \<cdot> ?h"
                  using h_in_hom j \<mu>.cone_axioms by auto
                also have "... = D j \<cdot> (\<pi>o (J.dom j) \<cdot> e) \<cdot> ?h"
                  using j comp_assoc by simp
                also have "... = D j \<cdot> \<tau> (J.dom j)"
                proof -
                  have "(\<pi>o (J.dom j) \<cdot> e) \<cdot> ?h = \<tau> (J.dom j)"
                  proof -
                    have "(\<pi>o (J.dom j) \<cdot> e) \<cdot> ?h = \<pi>o (J.dom j) \<cdot> e \<cdot> ?h"
                      using j 1 e_in_hom h_in_hom \<pi>o arrI comp_assoc by auto
                    also have "... = \<pi>o (J.dom j) \<cdot> ?e'"
                      using equ e'_in_hom EQU.induced_arrowI' [of ?e']
                      by (elim in_homE, auto)
                    also have "... = \<Delta>o.cones_map ?e' \<pi>o (J.dom j)"
                      using j e'_in_hom \<pi>o.cone_axioms by (elim in_homE, auto)
                    also have "... = \<tau> (J.dom j)"
                      using j e'_map by simp
                    finally show ?thesis by auto
                  qed
                  thus ?thesis by simp
                qed
                also have "... = \<tau> j"
                  using j \<tau>.is_natural_1 by simp
                finally show "D.cones_map ?h ?\<mu> j = \<tau> j" by auto
              qed
              ultimately show "D.cones_map ?h ?\<mu> j = \<tau> j" by auto
            qed
            show "\<guillemotleft>?h : a \<rightarrow> dom e\<guillemotright> \<and> D.cones_map ?h ?\<mu> = \<tau>"
              using h_in_hom 3 by simp
            show "\<And>h'. \<guillemotleft>h' : a \<rightarrow> dom e\<guillemotright> \<and> D.cones_map h' ?\<mu> = \<tau> \<Longrightarrow> h' = ?h"
            proof -
              fix h'
              assume h': "\<guillemotleft>h' : a \<rightarrow> dom e\<guillemotright> \<and> D.cones_map h' ?\<mu> = \<tau>"
              have h'_in_hom: "\<guillemotleft>h' : a \<rightarrow> dom e\<guillemotright>" using h' by simp
              have h'_map: "D.cones_map h' ?\<mu> = \<tau>" using h' by simp
              show "h' = ?h"
              proof -
                have 1: "\<guillemotleft>e \<cdot> h' : a \<rightarrow> \<Pi>o\<guillemotright> \<and> ?f \<cdot> e \<cdot> h' = ?g \<cdot> e \<cdot> h' \<and>
                         \<Delta>o.cones_map (C e h') \<pi>o = \<Delta>o.mkCone \<tau>"
                proof -
                  have 2: "\<guillemotleft>e \<cdot> h' : a \<rightarrow> \<Pi>o\<guillemotright>" using h'_in_hom e_in_hom by auto
                  moreover have "?f \<cdot> e \<cdot> h' = ?g \<cdot> e \<cdot> h'"
                  proof -
                    have "?f \<cdot> e \<cdot> h' = (?f \<cdot> e) \<cdot> h'"
                      using comp_assoc by auto
                    also have "... = ?g \<cdot> e \<cdot> h'"
                      using EQU.equalizes comp_assoc by auto
                    finally show ?thesis by auto
                  qed
                  moreover have "\<Delta>o.cones_map (e \<cdot> h') \<pi>o = \<Delta>o.mkCone \<tau>"
                  proof
                    have "\<Delta>o.cones_map (e \<cdot> h') \<pi>o = \<Delta>o.cones_map h' (\<Delta>o.cones_map e \<pi>o)"
                      using \<pi>o.cone_axioms e_in_hom h'_in_hom \<Delta>o.cones_map_comp [of e h']
                      by fastforce
                    fix j
                    have "\<not>Obj.arr j \<Longrightarrow> \<Delta>o.cones_map (e \<cdot> h') \<pi>o j = \<Delta>o.mkCone \<tau> j"
                      using 2 e_in_hom h'_in_hom \<pi>o.cone_axioms by auto
                    moreover have "Obj.arr j \<Longrightarrow> \<Delta>o.cones_map (e \<cdot> h') \<pi>o j = \<Delta>o.mkCone \<tau> j"
                    proof -
                      assume j: "Obj.arr j"
                      have "\<Delta>o.cones_map (e \<cdot> h') \<pi>o j = \<pi>o j \<cdot> e \<cdot> h'"
                        using 2 j \<pi>o.cone_axioms by auto
                      also have "... = (\<pi>o j \<cdot> e) \<cdot> h'"
                        using comp_assoc by auto
                      also have "... = \<Delta>o.mkCone ?\<mu> j \<cdot> h'"
                        using j e_in_hom \<pi>o_in_hom comp_ide_arr [of "D j" "\<pi>o j \<cdot> e"]
                        by fastforce
                      also have "... = \<Delta>o.mkCone \<tau> j"
                        using j h' \<mu>.cone_axioms mem_Collect_eq by auto
                      finally show "\<Delta>o.cones_map (e \<cdot> h') \<pi>o j = \<Delta>o.mkCone \<tau> j" by auto
                    qed
                    ultimately show "\<Delta>o.cones_map (e \<cdot> h') \<pi>o j = \<Delta>o.mkCone \<tau> j" by auto
                  qed
                  ultimately show ?thesis by auto
                qed
                have "\<guillemotleft>e \<cdot> h' : a \<rightarrow> \<Pi>o\<guillemotright>" using 1 by simp
                moreover have "e \<cdot> h' = ?e'"
                  using 1 cone_\<tau>o e'_in_hom e'_map \<pi>o.is_universal \<pi>o by blast
                ultimately show "h' = ?h"
                  using 1 h'_in_hom h'_map EQU.is_universal' [of "e \<cdot> h'"]
                        EQU.induced_arrowI' [of ?e'] equ
                  by (elim in_homE, auto)
              qed
            qed
          qed
        qed
        have "limit_cone J C D (dom e) ?\<mu>" ..
        thus "\<exists>a \<mu>. limit_cone J C D a \<mu>" by auto
      qed
      thus "\<forall>D. diagram J C D \<longrightarrow> (\<exists>a \<mu>. limit_cone J C D a \<mu>)" by blast
    qed

  end

  section "Limits in a Set Category"

  text\<open>
    In this section, we consider the special case of limits in a set category.
\<close>

  locale diagram_in_set_category =
    J: category J +
    S: set_category S +
    diagram J S D
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and S :: "'s comp"      (infixr "\<cdot>" 55)
  and D :: "'j \<Rightarrow> 's"
  begin

    notation S.in_hom ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    text\<open>
      An object @{term a} of a set category @{term[source=true] S} is a limit of a diagram in
      @{term[source=true] S} if and only if there is a bijection between the set
      @{term "S.hom S.unity a"} of points of @{term a} and the set of cones over the diagram
      that have apex @{term S.unity}.
\<close>

    lemma limits_are_sets_of_cones:
    shows "has_as_limit a \<longleftrightarrow> S.ide a \<and> (\<exists>\<phi>. bij_betw \<phi> (S.hom S.unity a) (cones S.unity))"
    proof
      text\<open>
        If \<open>has_limit a\<close>, then by the universal property of the limit cone,
        composition in @{term[source=true] S} yields a bijection between @{term "S.hom S.unity a"}
        and @{term "cones S.unity"}.
\<close>
      assume a: "has_as_limit a"
      hence "S.ide a"
        using limit_cone_def cone.ide_apex by metis
      from a obtain \<chi> where \<chi>: "limit_cone a \<chi>" by auto
      interpret \<chi>: limit_cone J S D a \<chi> using \<chi> by auto
      have "bij_betw (\<lambda>f. cones_map f \<chi>) (S.hom S.unity a) (cones S.unity)"
        using \<chi>.bij_betw_hom_and_cones S.ide_unity by simp
      thus "S.ide a \<and> (\<exists>\<phi>. bij_betw \<phi> (S.hom S.unity a) (cones S.unity))"
        using \<open>S.ide a\<close> by blast
      next
      text\<open>
        Conversely, an arbitrary bijection @{term \<phi>} between @{term "S.hom S.unity a"}
        and cones unity extends pointwise to a natural bijection @{term "\<Phi> a'"} between
        @{term "S.hom a' a"} and @{term "cones a'"}, showing that @{term a} is a limit.

        In more detail, the hypotheses give us a correspondence between points of @{term a}
        and cones with apex @{term "S.unity"}.  We extend this to a correspondence between
        functions to @{term a} and general cones, with each arrow from @{term a'} to @{term a}
        determining a cone with apex @{term a'}.  If @{term "f \<in> hom a' a"} then composition
        with @{term f} takes each point @{term y} of @{term a'} to the point @{term "S f y"}
        of @{term a}.  To this we may apply the given bijection @{term \<phi>} to obtain
        @{term "\<phi> (S f y) \<in> cones S.unity"}.  The component @{term "\<phi> (S f y) j"} at @{term j}
        of this cone is a point of @{term "S.cod (D j)"}.  Thus, @{term "f \<in> hom a' a"} determines
        a cone @{term \<chi>f} with apex @{term a'} whose component at @{term j} is the
        unique arrow @{term "\<chi>f j"} of @{term[source=true] S} such that
        @{term "\<chi>f j \<in> hom a' (cod (D j))"} and @{term "S (\<chi>f j) y = \<phi> (S f y) j"}
        for all points @{term y} of @{term a'}.
        The cone @{term \<chi>a} corresponding to @{term "a \<in> S.hom a a"} is then a limit cone.
\<close>
      assume a: "S.ide a \<and> (\<exists>\<phi>. bij_betw \<phi> (S.hom S.unity a) (cones S.unity))"
      hence ide_a: "S.ide a" by auto
      show "has_as_limit a"
      proof -
        from a obtain \<phi> where \<phi>: "bij_betw \<phi> (S.hom S.unity a) (cones S.unity)" by blast
        have X: "\<And>f j y. \<lbrakk> \<guillemotleft>f : S.dom f \<rightarrow> a\<guillemotright>; J.arr j; \<guillemotleft>y : S.unity \<rightarrow> S.dom f\<guillemotright> \<rbrakk>
                                \<Longrightarrow> \<guillemotleft>\<phi> (f \<cdot> y) j : S.unity \<rightarrow> S.cod (D j)\<guillemotright>"
        proof -
          fix f j y
          assume f: "\<guillemotleft>f : S.dom f \<rightarrow> a\<guillemotright>" and j: "J.arr j" and y: "\<guillemotleft>y : S.unity \<rightarrow> S.dom f\<guillemotright>"
          interpret \<chi>: cone J S D S.unity \<open>\<phi> (S f y)\<close>
            using f y \<phi> bij_betw_imp_funcset funcset_mem by blast
          show "\<guillemotleft>\<phi> (f \<cdot> y) j : S.unity \<rightarrow> S.cod (D j)\<guillemotright>" using j by auto
        qed
        text\<open>
          We want to define the component @{term "\<chi>j \<in> S.hom (S.dom f) (S.cod (D j))"}
          at @{term j} of a cone by specifying how it acts by composition on points
          @{term "y \<in> S.hom S.unity (S.dom f)"}.  We can do this because @{term[source=true] S}
          is a set category.
\<close>
        let ?P = "\<lambda>f j \<chi>j. \<guillemotleft>\<chi>j : S.dom f \<rightarrow> S.cod (D j)\<guillemotright> \<and>
                           (\<forall>y. \<guillemotleft>y : S.unity \<rightarrow> S.dom f\<guillemotright> \<longrightarrow> \<chi>j \<cdot> y = \<phi> (f \<cdot> y) j)"
        let ?\<chi> = "\<lambda>f j. if J.arr j then (THE \<chi>j. ?P f j \<chi>j) else S.null"
        have \<chi>: "\<And>f j. \<lbrakk> \<guillemotleft>f : S.dom f \<rightarrow> a\<guillemotright>; J.arr j \<rbrakk> \<Longrightarrow> ?P f j (?\<chi> f j)"
        proof -
          fix b f j
          assume f: "\<guillemotleft>f : S.dom f \<rightarrow> a\<guillemotright>" and j: "J.arr j"
          interpret B: constant_functor J S \<open>S.dom f\<close>
            using f by (unfold_locales, auto)
          have "(\<lambda>y. \<phi> (f \<cdot> y) j) \<in> S.hom S.unity (S.dom f) \<rightarrow> S.hom S.unity (S.cod (D j))"
            using f j X Pi_I' by simp
          hence "\<exists>!\<chi>j. ?P f j \<chi>j"
            using f j S.fun_complete' [of "S.dom f" "S.cod (D j)" "\<lambda>y. \<phi> (f \<cdot> y) j"]
            by (elim S.in_homE, auto)
          thus "?P f j (?\<chi> f j)" using j theI' [of "?P f j"] by simp
        qed
        text\<open>
          The arrows @{term "\<chi> f j"} are in fact the components of a cone with apex
          @{term "S.dom f"}.
\<close>
        have cone: "\<And>f. \<guillemotleft>f : S.dom f \<rightarrow> a\<guillemotright> \<Longrightarrow> cone (S.dom f) (?\<chi> f)"
        proof -
          fix f
          assume f: "\<guillemotleft>f : S.dom f \<rightarrow> a\<guillemotright>"
          interpret B: constant_functor J S \<open>S.dom f\<close>
            using f by (unfold_locales, auto)
          show "cone (S.dom f) (?\<chi> f)"
          proof
            show "\<And>j. \<not>J.arr j \<Longrightarrow> ?\<chi> f j = S.null" by simp
            fix j
            assume j: "J.arr j"
            have 0: "\<guillemotleft>?\<chi> f j : S.dom f \<rightarrow> S.cod (D j)\<guillemotright>" using f j \<chi> by simp
            show "S.dom (?\<chi> f j) = B.map (J.dom j)" using f j \<chi> by auto
            show "S.cod (?\<chi> f j) = D (J.cod j)" using f j \<chi> by auto
            have par1: "S.par (D j \<cdot> ?\<chi> f (J.dom j)) (?\<chi> f j)"
              using f j 0 \<chi> [of f "J.dom j"] by (elim S.in_homE, auto)
            have par2: "S.par (?\<chi> f (J.cod j) \<cdot> B.map j) (?\<chi> f j)"
              using f j 0 \<chi> [of f "J.cod j"] by (elim S.in_homE, auto)
            have nat: "\<And>y. \<guillemotleft>y : S.unity \<rightarrow> S.dom f\<guillemotright> \<Longrightarrow>
                              (D j \<cdot> ?\<chi> f (J.dom j)) \<cdot> y = ?\<chi> f j \<cdot> y \<and>
                              (?\<chi> f (J.cod j) \<cdot> B.map j) \<cdot> y = ?\<chi> f j \<cdot> y"
            proof -
              fix y
              assume y: "\<guillemotleft>y : S.unity \<rightarrow> S.dom f\<guillemotright>"
              show "(D j \<cdot> ?\<chi> f (J.dom j)) \<cdot> y = ?\<chi> f j \<cdot> y \<and>
                    (?\<chi> f (J.cod j) \<cdot> B.map j) \<cdot> y = ?\<chi> f j \<cdot> y"
              proof
                have 1: "\<phi> (f \<cdot> y) \<in> cones S.unity"
                  using f y \<phi> bij_betw_imp_funcset PiE
                        S.seqI S.cod_comp S.dom_comp mem_Collect_eq
                  by fastforce
                interpret \<chi>: cone J S D S.unity \<open>\<phi> (f \<cdot> y)\<close>
                  using 1 by simp
                have "(D j \<cdot> ?\<chi> f (J.dom j)) \<cdot> y = D j \<cdot> ?\<chi> f (J.dom j) \<cdot> y"
                  using S.comp_assoc by simp
                also have "... = D j \<cdot> \<phi> (f \<cdot> y) (J.dom j)"
                  using f y \<chi> \<chi>.is_extensional by simp
                also have "... = \<phi> (f \<cdot> y) j" using j by auto
                also have "... = ?\<chi> f j \<cdot> y"
                  using f j y \<chi> by force
                finally show "(D j \<cdot> ?\<chi> f (J.dom j)) \<cdot> y = ?\<chi> f j \<cdot> y" by auto
                have "(?\<chi> f (J.cod j) \<cdot> B.map j) \<cdot> y = ?\<chi> f (J.cod j) \<cdot> y"
                  using j B.map_simp par2 B.value_is_ide S.comp_arr_ide
                  by (metis (no_types, lifting))
                also have "... = \<phi> (f \<cdot> y) (J.cod j)"
                  using f y \<chi> \<chi>.is_extensional by simp
                also have "... = \<phi> (f \<cdot> y) j"
                  using j \<chi>.is_natural_2
                  by (metis J.arr_cod \<chi>.A.map_simp J.cod_cod)
                also have "... = ?\<chi> f j \<cdot> y"
                  using f y \<chi> \<chi>.is_extensional by simp
                finally show "(?\<chi> f (J.cod j) \<cdot> B.map j) \<cdot> y = ?\<chi> f j \<cdot> y" by auto
              qed
            qed
            show "D j \<cdot> ?\<chi> f (J.dom j) = ?\<chi> f j"
              using par1 nat 0
              apply (intro S.arr_eqI' [of "D j \<cdot> ?\<chi> f (J.dom j)" "?\<chi> f j"])
               apply force
              by auto
            show "?\<chi> f (J.cod j) \<cdot> B.map j = ?\<chi> f j"
              using par2 nat 0 f j \<chi>
              apply (intro S.arr_eqI' [of "?\<chi> f (J.cod j) \<cdot> B.map j" "?\<chi> f j"])
               apply force
              by (metis (no_types, lifting) S.in_homE)
          qed
        qed
        interpret \<chi>a: cone J S D a \<open>?\<chi> a\<close> using a cone [of a] by fastforce
        text\<open>
          Finally, show that \<open>\<chi> a\<close> is a limit cone.
\<close>
        interpret \<chi>a: limit_cone J S D a \<open>?\<chi> a\<close>
        proof
          fix a' \<chi>'
          assume cone_\<chi>': "cone a' \<chi>'"
          interpret \<chi>': cone J S D a' \<chi>' using cone_\<chi>' by auto
          show "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and> cones_map f (?\<chi> a) = \<chi>'"
          proof
            let ?\<psi> = "inv_into (S.hom S.unity a) \<phi>"
            have \<psi>: "?\<psi> \<in> cones S.unity \<rightarrow> S.hom S.unity a"
              using \<phi> bij_betw_inv_into bij_betwE by blast
            let ?P = "\<lambda>f. \<guillemotleft>f : a' \<rightarrow> a\<guillemotright> \<and>
                          (\<forall>y. y \<in> S.hom S.unity a' \<longrightarrow> f \<cdot> y = ?\<psi> (cones_map y \<chi>'))"
            have 1: "\<exists>!f. ?P f"
            proof -
              have "(\<lambda>y. ?\<psi> (cones_map y \<chi>')) \<in> S.hom S.unity a' \<rightarrow> S.hom S.unity a"
              proof
                fix x
                assume "x \<in> S.hom S.unity a'"
                hence "\<guillemotleft>x : S.unity \<rightarrow> a'\<guillemotright>" by simp
                hence "cones_map x \<in> cones a' \<rightarrow> cones S.unity"
                  using cones_map_mapsto [of x] by (elim S.in_homE, auto)
                hence "cones_map x \<chi>' \<in> cones S.unity"
                  using cone_\<chi>' by blast
                thus "?\<psi> (cones_map x \<chi>') \<in> S.hom S.unity a"
                  using \<psi> by auto
              qed
              thus ?thesis
                using S.fun_complete' a \<chi>'.ide_apex by simp
            qed
            let ?f = "THE f. ?P f"
            have f: "?P ?f" using 1 theI' [of ?P] by simp
            have f_in_hom: "\<guillemotleft>?f : a' \<rightarrow> a\<guillemotright>" using f by simp
            have f_map: "cones_map ?f (?\<chi> a) = \<chi>'"
            proof -
              have 1: "cone a' (cones_map ?f (?\<chi> a))"
              proof -
                have "cones_map ?f \<in> cones a \<rightarrow> cones a'"
                  using f_in_hom cones_map_mapsto [of ?f] by (elim S.in_homE, auto)
                hence "cones_map ?f (?\<chi> a) \<in> cones a'"
                  using \<chi>a.cone_axioms by blast
                thus ?thesis by simp
              qed
              interpret f\<chi>a: cone J S D a' \<open>cones_map ?f (?\<chi> a)\<close>
                using 1 by simp
              show ?thesis
              proof
                fix j
                have "\<not>J.arr j \<Longrightarrow> cones_map ?f (?\<chi> a) j = \<chi>' j"
                  using 1 \<chi>'.is_extensional f\<chi>a.is_extensional by presburger
                moreover have "J.arr j \<Longrightarrow> cones_map ?f (?\<chi> a) j = \<chi>' j"
                proof -
                  assume j: "J.arr j"
                  show "cones_map ?f (?\<chi> a) j = \<chi>' j"
                  proof (intro S.arr_eqI' [of "cones_map ?f (?\<chi> a) j" "\<chi>' j"])
                    show par: "S.par (cones_map ?f (?\<chi> a) j) (\<chi>' j)"
                      using j \<chi>'.preserves_cod \<chi>'.preserves_dom \<chi>'.preserves_reflects_arr
                            f\<chi>a.preserves_cod f\<chi>a.preserves_dom f\<chi>a.preserves_reflects_arr
                      by presburger
                    fix y
                    assume "\<guillemotleft>y : S.unity \<rightarrow> S.dom (cones_map ?f (?\<chi> a) j)\<guillemotright>"
                    hence y: "\<guillemotleft>y : S.unity \<rightarrow> a'\<guillemotright>"
                      using j f\<chi>a.preserves_dom by simp
                    have 1: "\<guillemotleft>?\<chi> a j : a \<rightarrow> D (J.cod j)\<guillemotright>"
                      using j \<chi>a.preserves_hom by force
                    have 2: "\<guillemotleft>?f \<cdot> y : S.unity \<rightarrow> a\<guillemotright>"
                      using f_in_hom y by blast
                    have "cones_map ?f (?\<chi> a) j \<cdot> y = (?\<chi> a j \<cdot> ?f) \<cdot> y"
                    proof -
                      have "S.cod ?f = a" using f_in_hom by blast
                      thus ?thesis using j \<chi>a.cone_axioms by simp
                    qed
                    also have "... = ?\<chi> a j \<cdot> ?f \<cdot> y"
                      using 1 j y f_in_hom S.comp_assoc S.seqI' by blast
                    also have "... = \<phi> (a \<cdot> ?f \<cdot> y) j"
                      using 1 2 ide_a f j y \<chi> [of a] by (simp add: S.ide_in_hom)
                    also have "... = \<phi> (?f \<cdot> y) j"
                      using a 2 y S.comp_cod_arr by (elim S.in_homE, auto)
                    also have "... = \<phi> (?\<psi> (cones_map y \<chi>')) j"
                      using j y f by simp
                    also have "... = cones_map y \<chi>' j"
                    proof -
                      have "cones_map y \<chi>' \<in> cones S.unity"
                        using cone_\<chi>' y cones_map_mapsto by force
                      hence "\<phi> (?\<psi> (cones_map y \<chi>')) = cones_map y \<chi>'"
                        using \<phi> bij_betw_inv_into_right [of \<phi>] by simp
                      thus ?thesis by auto
                    qed
                    also have "... = \<chi>' j \<cdot> y"
                      using cone_\<chi>' j y by auto
                    finally show "cones_map ?f (?\<chi> a) j \<cdot> y = \<chi>' j \<cdot> y"
                      by auto
                  qed
                qed
                ultimately show "cones_map ?f (?\<chi> a) j = \<chi>' j" by blast
              qed
            qed
            show "\<guillemotleft>?f : a' \<rightarrow> a\<guillemotright> \<and> cones_map ?f (?\<chi> a) = \<chi>'"
              using f_in_hom f_map by simp
            show "\<And>f'. \<guillemotleft>f' : a' \<rightarrow> a\<guillemotright> \<and> cones_map f' (?\<chi> a) = \<chi>' \<Longrightarrow> f' = ?f"
            proof -
              fix f'
              assume f': "\<guillemotleft>f' : a' \<rightarrow> a\<guillemotright> \<and> cones_map f' (?\<chi> a) = \<chi>'"
              have f'_in_hom: "\<guillemotleft>f' : a' \<rightarrow> a\<guillemotright>" using f' by simp
              have f'_map: "cones_map f' (?\<chi> a) = \<chi>'" using f' by simp
              show "f' = ?f"
              proof (intro S.arr_eqI' [of f' ?f])
                show "S.par f' ?f"
                  using f_in_hom f'_in_hom by (elim S.in_homE, auto)
                show "\<And>y'. \<guillemotleft>y' : S.unity \<rightarrow> S.dom f'\<guillemotright> \<Longrightarrow> f' \<cdot> y' = ?f \<cdot> y'"
                proof -
                  fix y'
                  assume y': "\<guillemotleft>y' : S.unity \<rightarrow> S.dom f'\<guillemotright>"
                  have 0: "\<phi> (f' \<cdot> y') = cones_map y' \<chi>'"
                  proof
                    fix j
                    have 1: "\<guillemotleft>f' \<cdot> y' : S.unity \<rightarrow> a\<guillemotright>" using f'_in_hom y' by auto
                    hence 2: "\<phi> (f' \<cdot> y') \<in> cones S.unity"
                      using \<phi> bij_betw_imp_funcset [of \<phi> "S.hom S.unity a" "cones S.unity"]
                      by auto
                    interpret \<chi>'': cone J S D S.unity \<open>\<phi> (f' \<cdot> y')\<close> using 2 by auto
                    have "\<not>J.arr j \<Longrightarrow> \<phi> (f' \<cdot> y') j = cones_map y' \<chi>' j"
                      using f' y' cone_\<chi>' \<chi>''.is_extensional mem_Collect_eq restrict_apply
                      by (elim S.in_homE, auto)
                    moreover have "J.arr j \<Longrightarrow> \<phi> (f' \<cdot> y') j = cones_map y' \<chi>' j"
                    proof -
                      assume j: "J.arr j"
                      have 3: "\<guillemotleft>?\<chi> a j : a \<rightarrow> D (J.cod j)\<guillemotright>"
                        using j \<chi>a.preserves_hom by force
                      have "\<phi> (f' \<cdot> y') j = \<phi> (a \<cdot> f' \<cdot> y') j"
                        using a f' y' j S.comp_cod_arr by (elim S.in_homE, auto)
                      also have "... = ?\<chi> a j \<cdot> f' \<cdot> y'"
                        using 1 3 \<chi> [of a] a f' y' j by fastforce
                      also have "... = (?\<chi> a j \<cdot> f') \<cdot> y'"
                        using S.comp_assoc by simp
                      also have "... = cones_map f' (?\<chi> a) j \<cdot> y'"
                        using f' y' j \<chi>a.cone_axioms by auto
                      also have "... = \<chi>' j \<cdot> y'"
                        using f' by blast
                      also have "... = cones_map y' \<chi>' j"
                        using y' j cone_\<chi>' f' mem_Collect_eq restrict_apply by force
                      finally show "\<phi> (f' \<cdot> y') j = cones_map y' \<chi>' j" by auto
                    qed
                    ultimately show "\<phi> (f' \<cdot> y') j = cones_map y' \<chi>' j" by auto
                  qed
                  hence "f' \<cdot> y' = ?\<psi> (cones_map y' \<chi>')"
                    using \<phi> f'_in_hom y' S.comp_in_homI
                          bij_betw_inv_into_left [of \<phi> "S.hom S.unity a" "cones S.unity" "f' \<cdot> y'"]
                    by (elim S.in_homE, auto)
                  moreover have "?f \<cdot> y' = ?\<psi> (cones_map y' \<chi>')"
                    using \<phi> 0 1 f f_in_hom f'_in_hom y' S.comp_in_homI
                          bij_betw_inv_into_left [of \<phi> "S.hom S.unity a" "cones S.unity" "?f \<cdot> y'"]
                    by (elim S.in_homE, auto)
                  ultimately show "f' \<cdot> y' = ?f \<cdot> y'" by auto
                qed
              qed
            qed
          qed
        qed
        have "limit_cone a (?\<chi> a)" ..
        thus ?thesis by auto
      qed
    qed

  end

  context set_category
  begin

    text\<open>
      A set category has an equalizer for any parallel pair of arrows.
\<close>

    lemma has_equalizers:
    shows "has_equalizers"
    proof (unfold has_equalizers_def)
      have "\<And>f0 f1. par f0 f1 \<Longrightarrow> \<exists>e. has_as_equalizer f0 f1 e"
      proof -
        fix f0 f1
        assume par: "par f0 f1"
        interpret J: parallel_pair .
        interpret PP: parallel_pair_diagram S f0 f1
          apply unfold_locales using par by auto
        interpret PP: diagram_in_set_category J.comp S PP.map ..
        text\<open>
          Let @{term a} be the object corresponding to the set of all images of equalizing points
          of @{term "dom f0"}, and let @{term e} be the inclusion of @{term a} in @{term "dom f0"}.
\<close>
        let ?a = "mkIde (img ` {e. e \<in> hom unity (dom f0) \<and> f0 \<cdot> e = f1 \<cdot> e})"
        have "{e. e \<in> hom unity (dom f0) \<and> f0 \<cdot> e = f1 \<cdot> e} \<subseteq> hom unity (dom f0)"
          by auto
        hence 1: "img ` {e. e \<in> hom unity (dom f0) \<and> f0 \<cdot> e = f1 \<cdot> e} \<subseteq> Univ"
          using img_point_in_Univ by auto
        have ide_a: "ide ?a" using 1 by auto
        have set_a: "set ?a = img ` {e. e \<in> hom unity (dom f0) \<and> f0 \<cdot> e = f1 \<cdot> e}"
          using 1 by simp
        have incl_in_a: "incl_in ?a (dom f0)"
        proof -
          have "ide (dom f0)"
            using PP.is_parallel by simp
          moreover have "set ?a \<subseteq> set (dom f0)"
          proof -
            have "set ?a = img ` {e. e \<in> hom unity (dom f0) \<and> f0 \<cdot> e = f1 \<cdot> e}"
              using img_point_in_Univ set_a by blast
            thus ?thesis
              using imageE img_point_elem_set mem_Collect_eq subsetI by auto
          qed
          ultimately show ?thesis
            using incl_in_def \<open>ide ?a\<close> by simp
        qed
        text\<open>
          Then @{term "set a"} is in bijective correspondence with @{term "PP.cones unity"}.
\<close>
        let ?\<phi> = "\<lambda>t. PP.mkCone (mkPoint (dom f0) t)"
        let ?\<psi> = "\<lambda>\<chi>. img (\<chi> (J.Zero))"
        have bij: "bij_betw ?\<phi> (set ?a) (PP.cones unity)"
        proof (intro bij_betwI)
          show "?\<phi> \<in> set ?a \<rightarrow> PP.cones unity"
          proof
            fix t
            assume t: "t \<in> set ?a"
            hence 1: "t \<in> img ` {e. e \<in> hom unity (dom f0) \<and> f0 \<cdot> e = f1 \<cdot> e}"
              using set_a by blast
            then have 2: "mkPoint (dom f0) t \<in> hom unity (dom f0)"
              using mkPoint_in_hom imageE mem_Collect_eq mkPoint_img(2) by auto
            with 1 have 3: "mkPoint (dom f0) t \<in> {e. e \<in> hom unity (dom f0) \<and> f0 \<cdot> e = f1 \<cdot> e}"
              using mkPoint_img(2) by auto
            then have "PP.is_equalized_by (mkPoint (dom f0) t)"
              using CollectD par by fastforce
            thus "PP.mkCone (mkPoint (dom f0) t) \<in> PP.cones unity"
              using 2 PP.cone_mkCone [of "mkPoint (dom f0) t"] by auto
          qed
          show "?\<psi> \<in> PP.cones unity \<rightarrow> set ?a"
          proof
            fix \<chi>
            assume \<chi>: "\<chi> \<in> PP.cones unity"
            interpret \<chi>: cone J.comp S PP.map unity \<chi> using \<chi> by auto
            have "\<chi> (J.Zero) \<in> hom unity (dom f0) \<and> f0 \<cdot> \<chi> (J.Zero) = f1 \<cdot> \<chi> (J.Zero)"
              using \<chi> PP.map_def PP.is_equalized_by_cone J.arr_char by auto
            hence "img (\<chi> (J.Zero)) \<in> set ?a"
              using set_a by simp
            thus "?\<psi> \<chi> \<in> set ?a" by blast
          qed
          show "\<And>t. t \<in> set ?a \<Longrightarrow> ?\<psi> (?\<phi> t) = t"
            using set_a J.arr_char PP.mkCone_def imageE mem_Collect_eq mkPoint_img(2)
            by auto
          show "\<And>\<chi>. \<chi> \<in> PP.cones unity \<Longrightarrow> ?\<phi> (?\<psi> \<chi>) = \<chi>"
          proof -
            fix \<chi>
            assume \<chi>: "\<chi> \<in> PP.cones unity"
            interpret \<chi>: cone J.comp S PP.map unity \<chi> using \<chi> by auto
            have 1: "\<chi> (J.Zero) \<in> hom unity (dom f0) \<and> f0 \<cdot> \<chi> (J.Zero) = f1 \<cdot> \<chi> (J.Zero)"
              using \<chi> PP.map_def PP.is_equalized_by_cone J.arr_char by auto
            hence "img (\<chi> (J.Zero)) \<in> set ?a"
              using set_a by simp
            hence "img (\<chi> (J.Zero)) \<in> set (dom f0)"
              using incl_in_a incl_in_def by auto
            hence "mkPoint (dom f0) (img (\<chi> J.Zero)) = \<chi> J.Zero"
              using 1 mkPoint_img(2) by blast
            hence "?\<phi> (?\<psi> \<chi>) = PP.mkCone (\<chi> J.Zero)" by simp
            also have "... = \<chi>"
              using \<chi> PP.mkCone_cone by simp
            finally show "?\<phi> (?\<psi> \<chi>) = \<chi>" by auto
          qed
        qed
        text\<open>
          It follows that @{term a} is a limit of \<open>PP\<close>, and that the limit cone gives an
          equalizer of @{term f0} and @{term f1}.
\<close>
        have "\<exists>\<mu>. bij_betw \<mu> (hom unity ?a) (set ?a)"
          using bij_betw_points_and_set ide_a by auto
        from this obtain \<mu> where \<mu>: "bij_betw \<mu> (hom unity ?a) (set ?a)" by blast
        have "bij_betw (?\<phi> o \<mu>) (hom unity ?a) (PP.cones unity)"
          using bij \<mu> bij_betw_comp_iff by blast
        hence "\<exists>\<phi>. bij_betw \<phi> (hom unity ?a) (PP.cones unity)" by auto
        hence "PP.has_as_limit ?a"
          using ide_a PP.limits_are_sets_of_cones by simp
        from this obtain \<epsilon> where \<epsilon>: "limit_cone J.comp S PP.map ?a \<epsilon>" by auto
        interpret \<epsilon>: limit_cone J.comp S PP.map ?a \<epsilon> using \<epsilon> by auto
        have "PP.mkCone (\<epsilon> (J.Zero)) = \<epsilon>"
          using \<epsilon> PP.mkCone_cone \<epsilon>.cone_axioms by simp
        moreover have "dom (\<epsilon> (J.Zero)) = ?a"
          using J.ide_char \<epsilon>.preserves_hom \<epsilon>.A.map_def by simp
        ultimately have "PP.has_as_equalizer (\<epsilon> J.Zero)"
          using \<epsilon> by simp
        thus "\<exists>e. has_as_equalizer f0 f1 e"
          using par has_as_equalizer_def by auto   
      qed
      thus "\<forall>f0 f1. par f0 f1 \<longrightarrow> (\<exists>e. has_as_equalizer f0 f1 e)" by auto
    qed

  end

  sublocale set_category \<subseteq> category_with_equalizers S
    apply unfold_locales using has_equalizers by auto

  context set_category
  begin

    text\<open>
      The aim of the next results is to characterize the conditions under which a set
      category has products.  In a traditional development of category theory,
      one shows that the category \textbf{Set} of \emph{all} sets has all small
      (\emph{i.e.}~set-indexed) products.  In the present context we do not have a
      category of \emph{all} sets, but rather only a category of all sets with
      elements at a particular type.  Clearly, we cannot expect such a category
      to have products indexed by arbitrarily large sets.  The existence of
      @{term I}-indexed products in a set category @{term[source=true] S} implies that the universe
      \<open>S.Univ\<close> of @{term[source=true] S} must be large enough to admit the formation of
      @{term I}-tuples of its elements.  Conversely, for a set category @{term[source=true] S}
      the ability to form @{term I}-tuples in @{term Univ} implies that
      @{term[source=true] S} has @{term I}-indexed products.  Below we make this precise by
      defining the notion of when a set category @{term[source=true] S}
      ``admits @{term I}-indexed tupling'' and we show that @{term[source=true] S}
      has @{term I}-indexed products if and only if it admits @{term I}-indexed tupling.

      The definition of ``@{term[source=true] S} admits @{term I}-indexed tupling'' says that
      there is an injective map, from the space of extensional functions from
      @{term I} to @{term Univ}, to @{term Univ}.  However for a convenient
      statement and proof of the desired result, the definition of extensional
      function from theory @{theory "HOL-Library.FuncSet"} needs to be modified.
      The theory @{theory "HOL-Library.FuncSet"} uses the definite, but arbitrarily chosen value
      @{term undefined} as the value to be assumed by an extensional function outside
      of its domain.  In the context of the \<open>set_category\<close>, though, it is
      more natural to use \<open>S.unity\<close>, which is guaranteed to be an element of the
      universe of @{term[source=true] S}, for this purpose.  Doing things that way makes it
      simpler to establish a bijective correspondence between cones over @{term D} with apex
      @{term unity} and the set of extensional functions @{term d} that map
      each arrow @{term j} of @{term J} to an element @{term "d j"} of @{term "set (D j)"}.
      Possibly it makes sense to go back and make this change in \<open>set_category\<close>,
      but that would mean completely abandoning @{theory "HOL-Library.FuncSet"} and essentially
      introducing a duplicate version for use with \<open>set_category\<close>.
      As a compromise, what I have done here is to locally redefine the few notions from
      @{theory "HOL-Library.FuncSet"} that I need in order to prove the next set of results.
\<close>

    definition extensional
    where "extensional A \<equiv> {f. \<forall>x. x \<notin> A \<longrightarrow> f x = unity}"

    abbreviation PiE
    where "PiE A B \<equiv> Pi A B \<inter> extensional A"

    abbreviation restrict
    where "restrict f A \<equiv> \<lambda>x. if x \<in> A then f x else unity"

    lemma extensionalI [intro]:
    assumes "\<And>x. x \<notin> A \<Longrightarrow> f x = unity"
    shows "f \<in> extensional A"
      using assms extensional_def by auto

    lemma extensional_arb:
    assumes "f \<in> extensional A" and "x \<notin> A"
    shows "f x = unity"
      using assms extensional_def by fast

    lemma extensional_monotone:
    assumes "A \<subseteq> B"
    shows "extensional A \<subseteq> extensional B"
    proof
      fix f
      assume f: "f \<in> extensional A"
      have 1: "\<forall>x. x \<notin> A \<longrightarrow> f x = unity" using f extensional_def by fast
      hence "\<forall>x. x \<notin> B \<longrightarrow> f x = unity" using assms by auto
      thus "f \<in> extensional B" using extensional_def by blast
    qed

    lemma PiE_mono: "(\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x) \<Longrightarrow> PiE A B \<subseteq> PiE A C"
      by auto

  end

  locale discrete_diagram_in_set_category =
    S: set_category S +
    discrete_diagram J S D +
    diagram_in_set_category J S D
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and S :: "'s comp"      (infixr "\<cdot>" 55)
  and D :: "'j \<Rightarrow> 's"
  begin

    text\<open>
      For @{term D} a discrete diagram in a set category, there is a bijective correspondence
      between cones over @{term D} with apex unity and the set of extensional functions @{term d}
      that map each arrow @{term j} of @{term[source=true] J} to an element of
      @{term "S.set (D j)"}.
\<close>

    abbreviation I
    where "I \<equiv> Collect J.arr"

    definition funToCone
    where "funToCone F \<equiv> \<lambda>j. if J.arr j then S.mkPoint (D j) (F j) else S.null"

    definition coneToFun
    where "coneToFun \<chi> \<equiv> \<lambda>j. if J.arr j then S.img (\<chi> j) else S.unity"

    lemma funToCone_mapsto:
    shows "funToCone \<in> S.PiE I (S.set o D) \<rightarrow> cones S.unity"
    proof
      fix F
      assume F: "F \<in> S.PiE I (S.set o D)"
      interpret U: constant_functor J S S.unity
        apply unfold_locales using S.ide_unity by auto
      have 1: "S.ide (S.mkIde S.Univ)" by simp
      have "cone S.unity (funToCone F)"
      proof
        show "\<And>j. \<not>J.arr j \<Longrightarrow> funToCone F j = S.null"
          using funToCone_def by simp
        fix j
        assume j: "J.arr j"
        have "funToCone F j = S.mkPoint (D j) (F j)"
          using j funToCone_def by simp
        moreover have "... \<in> S.hom S.unity (D j)"
          using F j is_discrete S.img_mkPoint(1) [of "D j"] by force
        ultimately have 2: "funToCone F j \<in> S.hom S.unity (D j)" by auto
        show 3: "S.dom (funToCone F j) = U.map (J.dom j)"
          using 2 j U.map_simp by auto
        show 4: "S.cod (funToCone F j) = D (J.cod j)"
          using 2 j is_discrete by auto
        show "D j \<cdot> funToCone F (J.dom j) = funToCone F j"
          using 2 j is_discrete S.comp_cod_arr by auto
        show "funToCone F (J.cod j) \<cdot> (U.map j) = funToCone F j"
          using 3 j is_discrete U.map_simp S.arr_dom_iff_arr S.comp_arr_dom U.preserves_arr
          by (metis J.ide_char)
      qed
      thus "funToCone F \<in> cones S.unity" by auto
    qed

    lemma coneToFun_mapsto:
    shows "coneToFun \<in> cones S.unity \<rightarrow> S.PiE I (S.set o D)"
    proof
      fix \<chi>
      assume \<chi>: "\<chi> \<in> cones S.unity"
      interpret \<chi>: cone J S D S.unity \<chi> using \<chi> by auto
      show "coneToFun \<chi> \<in> S.PiE I (S.set o D)"
      proof
        show "coneToFun \<chi> \<in> Pi I (S.set o D)"
          using S.mkPoint_img(1) coneToFun_def is_discrete \<chi>.component_in_hom
          by (simp add: S.img_point_elem_set restrict_apply')
        show "coneToFun \<chi> \<in> S.extensional I"
        proof
          fix x
          show "x \<notin> I \<Longrightarrow> coneToFun \<chi> x = S.unity"
            using coneToFun_def by simp
        qed
      qed
    qed

    lemma funToCone_coneToFun:
    assumes "\<chi> \<in> cones S.unity"
    shows "funToCone (coneToFun \<chi>) = \<chi>"
    proof
      interpret \<chi>: cone J S D S.unity \<chi> using assms by auto
      fix j
      have "\<not>J.arr j \<Longrightarrow> funToCone (coneToFun \<chi>) j = \<chi> j"
        using funToCone_def \<chi>.is_extensional by simp
      moreover have "J.arr j \<Longrightarrow> funToCone (coneToFun \<chi>) j = \<chi> j"
        using funToCone_def coneToFun_def S.mkPoint_img(2) is_discrete \<chi>.component_in_hom
        by auto
      ultimately show "funToCone (coneToFun \<chi>) j = \<chi> j" by blast
    qed

    lemma coneToFun_funToCone:
    assumes "F \<in> S.PiE I (S.set o D)"
    shows "coneToFun (funToCone F) = F"
    proof
      fix i
      have "i \<notin> I \<Longrightarrow> coneToFun (funToCone F) i = F i"
        using assms coneToFun_def S.extensional_arb [of F I i] by auto
      moreover have "i \<in> I \<Longrightarrow> coneToFun (funToCone F) i = F i"
      proof -
        assume i: "i \<in> I"
        have "coneToFun (funToCone F) i = S.img (funToCone F i)"
          using i coneToFun_def by simp
        also have "... = S.img (S.mkPoint (D i) (F i))"
          using i funToCone_def by auto
        also have "... = F i"
          using assms i is_discrete S.img_mkPoint(2) by force
        finally show "coneToFun (funToCone F) i = F i" by auto
      qed
      ultimately show "coneToFun (funToCone F) i = F i" by auto
    qed

    lemma bij_coneToFun:
    shows "bij_betw coneToFun (cones S.unity) (S.PiE I (S.set o D))"
      using coneToFun_mapsto funToCone_mapsto funToCone_coneToFun coneToFun_funToCone
            bij_betwI
      by blast

    lemma bij_funToCone:
    shows "bij_betw funToCone (S.PiE I (S.set o D)) (cones S.unity)"
      using coneToFun_mapsto funToCone_mapsto funToCone_coneToFun coneToFun_funToCone
            bij_betwI
      by blast
 
  end

  context set_category
  begin

    text\<open>
      A set category admits @{term I}-indexed tupling if there is an injective map that takes
      each extensional function from @{term I} to @{term Univ} to an element of @{term Univ}.
\<close>

    definition admits_tupling
    where "admits_tupling I \<equiv> \<exists>\<pi>. \<pi> \<in> PiE I (\<lambda>_. Univ) \<rightarrow> Univ \<and> inj_on \<pi> (PiE I (\<lambda>_. Univ))"

    lemma admits_tupling_monotone:
    assumes "admits_tupling I" and "I' \<subseteq> I"
    shows "admits_tupling I'"
    proof -
      from assms(1) obtain \<pi>
      where \<pi>: "\<pi> \<in> PiE I (\<lambda>_. Univ) \<rightarrow> Univ \<and> inj_on \<pi> (PiE I (\<lambda>_. Univ))"
        using admits_tupling_def by metis
      have "\<pi> \<in> PiE I' (\<lambda>_. Univ) \<rightarrow> Univ"
      proof
        fix f
        assume f: "f \<in> PiE I' (\<lambda>_. Univ)"
        have "f \<in> PiE I (\<lambda>_. Univ)"
          using assms(2) f extensional_def [of I'] terminal_unity extensional_monotone by auto
        thus "\<pi> f \<in> Univ" using \<pi> by auto
      qed
      moreover have "inj_on \<pi> (PiE I' (\<lambda>_. Univ))"
      proof -
        have 1: "\<And>F A A'. inj_on F A \<and> A' \<subseteq> A \<Longrightarrow> inj_on F A'"
          using subset_inj_on by blast
        moreover have "PiE I' (\<lambda>_. Univ) \<subseteq> PiE I (\<lambda>_. Univ)"
          using assms(2) extensional_def [of I'] terminal_unity by auto
        ultimately show ?thesis using \<pi> assms(2) by blast
      qed
      ultimately show ?thesis using admits_tupling_def by metis
    qed

    lemma has_products_iff_admits_tupling:
    fixes I :: "'i set"
    shows "has_products I \<longleftrightarrow> I \<noteq> UNIV \<and> admits_tupling I"
    proof
      text\<open>
        If @{term[source=true] S} has @{term I}-indexed products, then for every @{term I}-indexed
        discrete diagram @{term D} in @{term[source=true] S} there is an object @{term \<Pi>D}
        of @{term[source=true] S} whose points are in bijective correspondence with the set of
        cones over @{term D} with apex @{term unity}.  In particular this is true for
        the diagram @{term D} that assigns to each element of @{term I} the
        ``universal object'' @{term "mkIde Univ"}.
\<close>
      assume has_products: "has_products I"
      have I: "I \<noteq> UNIV" using has_products has_products_def by auto
      interpret J: discrete_category I \<open>SOME x. x \<notin> I\<close>
        using I someI_ex [of "\<lambda>x. x \<notin> I"] by (unfold_locales, auto)
      let ?D = "\<lambda>i. mkIde Univ"
      interpret D: discrete_diagram_from_map I S ?D \<open>SOME j. j \<notin> I\<close>
        using J.not_arr_null J.arr_char
        by (unfold_locales, auto)
      interpret D: discrete_diagram_in_set_category J.comp S D.map ..
      have "discrete_diagram J.comp S D.map" ..
      from this obtain \<Pi>D \<chi> where \<chi>: "product_cone J.comp S D.map \<Pi>D \<chi>"
        using has_products has_products_def [of I] ex_productE [of "J.comp" D.map]
              D.diagram_axioms
        by blast
      interpret \<chi>: product_cone J.comp S D.map \<Pi>D \<chi>
        using \<chi> by auto
      have "D.has_as_limit \<Pi>D"
        using \<chi>.limit_cone_axioms by auto
      hence \<Pi>D: "ide \<Pi>D \<and> (\<exists>\<phi>. bij_betw \<phi> (hom unity \<Pi>D) (D.cones unity))"
        using D.limits_are_sets_of_cones by simp
      from this obtain \<phi> where \<phi>: "bij_betw \<phi> (hom unity \<Pi>D) (D.cones unity)"
        by blast
      have \<phi>': "inv_into (hom unity \<Pi>D) \<phi> \<in> D.cones unity \<rightarrow> hom unity \<Pi>D \<and>
                inj_on (inv_into (hom unity \<Pi>D) \<phi>) (D.cones unity)"
        using \<phi> bij_betw_inv_into bij_betw_imp_inj_on bij_betw_imp_funcset by blast
      let ?\<pi> = "img o (inv_into (hom unity \<Pi>D) \<phi>) o D.funToCone"
      have 1: "D.funToCone \<in> PiE I (set o D.map) \<rightarrow> D.cones unity"
        using D.funToCone_mapsto extensional_def [of I] by auto
      have 2: "inv_into (hom unity \<Pi>D) \<phi> \<in> D.cones unity \<rightarrow> hom unity \<Pi>D"
        using \<phi>' by auto
      have 3: "img \<in> hom unity \<Pi>D \<rightarrow> Univ"
        using img_point_in_Univ by blast
      have 4: "inj_on D.funToCone (PiE I (set o D.map))"
      proof -
        have "D.I = I" by auto
        thus ?thesis
          using D.bij_funToCone bij_betw_imp_inj_on by auto
      qed
      have 5: "inj_on (inv_into (hom unity \<Pi>D) \<phi>) (D.cones unity)"
        using \<phi>' by auto
      have 6: "inj_on img (hom unity \<Pi>D)"
        using \<Pi>D bij_betw_points_and_set bij_betw_imp_inj_on [of img "hom unity \<Pi>D" "set \<Pi>D"]
        by simp
      have "?\<pi> \<in> PiE I (set o D.map) \<rightarrow> Univ"
        using 1 2 3 by force
      moreover have "inj_on ?\<pi> (PiE I (set o D.map))"
      proof -
        have 7: "\<And>A B C D F G H. F \<in> A \<rightarrow> B \<and> G \<in> B \<rightarrow> C \<and> H \<in> C \<rightarrow> D
                      \<and> inj_on F A \<and> inj_on G B \<and> inj_on H C
                    \<Longrightarrow> inj_on (H o G o F) A"
        proof (intro inj_onI)
          fix A :: "'a set" and B :: "'b set" and C :: "'c set" and D :: "'d set"
          and F :: "'a \<Rightarrow> 'b" and G :: "'b \<Rightarrow> 'c" and H :: "'c \<Rightarrow> 'd"
          assume a1: "F \<in> A \<rightarrow> B \<and> G \<in> B \<rightarrow> C \<and> H \<in> C \<rightarrow> D \<and>
                      inj_on F A \<and> inj_on G B \<and> inj_on H C"
          fix a a'
          assume a: "a \<in> A" and a': "a' \<in> A" and eq: "(H o G o F) a = (H o G o F) a'"
          have "H (G (F a)) = H (G (F a'))" using eq by simp
          moreover have "G (F a) \<in> C \<and> G (F a') \<in> C" using a a' a1 by auto
          ultimately have "G (F a) = G (F a')" using a1 inj_onD by metis
          moreover have "F a \<in> B \<and> F a' \<in> B" using a a' a1 by auto
          ultimately have "F a = F a'" using a1 inj_onD by metis
          thus "a = a'" using a a' a1 inj_onD by metis
        qed
        show ?thesis
          using 1 2 3 4 5 6 7 [of D.funToCone "PiE I (set o D.map)" "D.cones unity"
                                  "inv_into (hom unity \<Pi>D) \<phi>" "hom unity \<Pi>D"
                                  img Univ]
          by fastforce
      qed
      moreover have "PiE I (set o D.map) = PiE I (\<lambda>x. Univ)"
      proof -
        have "\<And>i. i \<in> I \<Longrightarrow> (set o D.map) i = Univ"
          using J.arr_char D.map_def by simp
        thus ?thesis by blast
      qed
      ultimately have "?\<pi> \<in> (PiE I (\<lambda>x. Univ)) \<rightarrow> Univ \<and> inj_on ?\<pi> (PiE I (\<lambda>x. Univ))"
        by auto
      thus "I \<noteq> UNIV \<and> admits_tupling I"
        using I admits_tupling_def by auto
      next
      assume ex_\<pi>: "I \<noteq> UNIV \<and> admits_tupling I"
      show "has_products I"
      proof (unfold has_products_def)
        from ex_\<pi> obtain \<pi>
        where \<pi>: "\<pi> \<in> (PiE I (\<lambda>x. Univ)) \<rightarrow> Univ \<and> inj_on \<pi> (PiE I (\<lambda>x. Univ))"
          using admits_tupling_def by metis
        text\<open>
          Given an @{term I}-indexed discrete diagram @{term D}, obtain the object @{term \<Pi>D}
          of @{term[source=true] S} corresponding to the set @{term "\<pi> ` PiE I D"} of all
          @{term "\<pi> d"} where \<open>d \<in> d \<in> J \<rightarrow>\<^sub>E Univ\<close> and @{term "d i \<in> D i"}
          for all @{term "i \<in> I"}.
          The elements of @{term \<Pi>D} are in bijective correspondence with the set of cones
          over @{term D}, hence @{term \<Pi>D} is a limit of @{term D}.
\<close>
        have "\<And>J D. discrete_diagram J S D \<and> Collect (partial_magma.arr J) = I
                 \<Longrightarrow> \<exists>\<Pi>D. has_as_product J D \<Pi>D"
        proof
          fix J :: "'i comp" and D
          assume D: "discrete_diagram J S D \<and> Collect (partial_magma.arr J) = I"
          interpret J: category J
            using D discrete_diagram.axioms(1) by blast
          interpret D: discrete_diagram J S D
            using D by simp
          interpret D: discrete_diagram_in_set_category J S D ..
          let ?\<Pi>D = "mkIde (\<pi> ` PiE I (set o D))"
          have 0: "ide ?\<Pi>D"
          proof -
            have "set o D \<in> I \<rightarrow> Pow Univ"
              using Pow_iff incl_in_def o_apply elem_set_implies_incl_in
                    set_subset_Univ subsetI
              by (metis (mono_tags, lifting) Pi_I')
            hence "\<pi> ` PiE I (set o D) \<subseteq> Univ"
              using \<pi> by blast
            thus ?thesis using \<pi> ide_mkIde by simp
          qed
          hence set_\<Pi>D: "\<pi> ` PiE I (set o D) = set ?\<Pi>D"
            using 0 ide_in_hom by auto
          text\<open>
            The elements of @{term \<Pi>D} are all values of the form @{term "\<pi> d"},
            where @{term d} satisfies @{term "d i \<in> set (D i)"} for all @{term "i \<in> I"}.
            Such @{term d} correspond bijectively to cones.
            Since @{term \<pi>} is injective, the values @{term "\<pi> d"} correspond bijectively to cones.
\<close>
          let ?\<phi> = "mkPoint ?\<Pi>D o \<pi> o D.coneToFun"
          let ?\<phi>' = "D.funToCone o inv_into (PiE I (set o D)) \<pi> o img"
          have 1: "\<pi> \<in> PiE I (set o D) \<rightarrow> set ?\<Pi>D \<and> inj_on \<pi> (PiE I (set o D))"
          proof -
            have "PiE I (set o D) \<subseteq> PiE I (\<lambda>x. Univ)"
              using set_subset_Univ elem_set_implies_incl_in elem_set_implies_set_eq_singleton
                    incl_in_def PiE_mono
              by (metis comp_apply subsetI)
            thus ?thesis using \<pi> subset_inj_on set_\<Pi>D Pi_I' imageI by fastforce
          qed
          have 2: "inv_into (PiE I (set o D)) \<pi> \<in> set ?\<Pi>D \<rightarrow> PiE I (set o D)"
          proof
            fix y
            assume y: "y \<in> set ?\<Pi>D"
            have "y \<in> \<pi> ` (PiE I (set o D))" using y set_\<Pi>D by auto
            thus "inv_into (PiE I (set o D)) \<pi> y \<in> PiE I (set o D)"
              using inv_into_into [of y \<pi> "PiE I (set o D)"] by simp
          qed
          have 3: "\<And>x. x \<in> set ?\<Pi>D \<Longrightarrow> \<pi> (inv_into (PiE I (set o D)) \<pi> x) = x"
            using set_\<Pi>D by (simp add: f_inv_into_f)
          have 4: "\<And>d. d \<in> PiE I (set o D) \<Longrightarrow> inv_into (PiE I (set o D)) \<pi> (\<pi> d) = d"
            using 1 by auto
          have 5: "D.I = I"
            using D by auto
          have "bij_betw ?\<phi> (D.cones unity) (hom unity ?\<Pi>D)"
          proof (intro bij_betwI)
            show "?\<phi> \<in> D.cones unity \<rightarrow> hom unity ?\<Pi>D"
            proof
              fix \<chi>
              assume \<chi>: "\<chi> \<in> D.cones unity"
              show "?\<phi> \<chi> \<in> hom unity ?\<Pi>D"
                using \<chi> 0 1 5 D.coneToFun_mapsto mkPoint_in_hom [of ?\<Pi>D]
                by (simp, blast)
            qed
            show "?\<phi>' \<in> hom unity ?\<Pi>D \<rightarrow> D.cones unity"
            proof
              fix x
              assume x: "x \<in> hom unity ?\<Pi>D"
              hence "img x \<in> set ?\<Pi>D"
                using img_point_elem_set by blast
              hence "inv_into (PiE I (set o D)) \<pi> (img x) \<in> Pi I (set \<circ> D) \<inter> local.extensional I"
                using 2 by blast
              thus "?\<phi>' x \<in> D.cones unity"
                using 5 D.funToCone_mapsto by auto
            qed
            show "\<And>x. x \<in> hom unity ?\<Pi>D \<Longrightarrow> ?\<phi> (?\<phi>' x) = x"
            proof -
              fix x
              assume x: "x \<in> hom unity ?\<Pi>D"
              show "?\<phi> (?\<phi>' x) = x"
              proof -
                have "D.coneToFun (D.funToCone (inv_into (PiE I (set o D)) \<pi> (img x)))
                          = inv_into (PiE I (set o D)) \<pi> (img x)"
                  using x 1 5 img_point_elem_set set_\<Pi>D D.coneToFun_funToCone by force
                hence "\<pi> (D.coneToFun (D.funToCone (inv_into (PiE I (set o D)) \<pi> (img x))))
                          = img x"
                  using x 3 img_point_elem_set set_\<Pi>D by force
                thus ?thesis using x 0 mkPoint_img by auto
              qed
            qed
            show "\<And>\<chi>. \<chi> \<in> D.cones unity \<Longrightarrow> ?\<phi>' (?\<phi> \<chi>) = \<chi>"
            proof -
              fix \<chi>
              assume \<chi>: "\<chi> \<in> D.cones unity"
              show "?\<phi>' (?\<phi> \<chi>) = \<chi>"
              proof -
                have "img (mkPoint ?\<Pi>D (\<pi> (D.coneToFun \<chi>))) = \<pi> (D.coneToFun \<chi>)"
                  using \<chi> 0 1 5 D.coneToFun_mapsto img_mkPoint(2) by blast
                hence "inv_into (PiE I (set o D)) \<pi> (img (mkPoint ?\<Pi>D (\<pi> (D.coneToFun \<chi>))))
                         = D.coneToFun \<chi>"
                  using \<chi> D.coneToFun_mapsto 4 5 by (metis PiE)
                hence "D.funToCone (inv_into (PiE I (set o D)) \<pi>
                                             (img (mkPoint ?\<Pi>D (\<pi> (D.coneToFun \<chi>)))))
                         = \<chi>"
                  using \<chi> D.funToCone_coneToFun by auto
                thus ?thesis by auto
              qed
            qed
          qed
          hence "bij_betw (inv_into (D.cones unity) ?\<phi>) (hom unity ?\<Pi>D) (D.cones unity)"
            using bij_betw_inv_into by blast
          hence "\<exists>\<phi>. bij_betw \<phi> (hom unity ?\<Pi>D) (D.cones unity)" by blast
          hence "D.has_as_limit ?\<Pi>D"
            using \<open>ide ?\<Pi>D\<close> D.limits_are_sets_of_cones by simp
          from this obtain \<chi> where \<chi>: "limit_cone J S D ?\<Pi>D \<chi>" by blast
          interpret \<chi>: limit_cone J S D ?\<Pi>D \<chi> using \<chi> by auto
          interpret P: product_cone J S D ?\<Pi>D \<chi>
            using \<chi> D.product_coneI by blast
          have "product_cone J S D ?\<Pi>D \<chi>" ..
          thus "has_as_product J D ?\<Pi>D"
            using has_as_product_def by auto
        qed
        thus "I \<noteq> UNIV \<and>
              (\<forall>J D. discrete_diagram J S D \<and> Collect (partial_magma.arr J) = I
                  \<longrightarrow> (\<exists>\<Pi>D. has_as_product J D \<Pi>D))"
          using ex_\<pi> by blast
      qed
    qed

    text\<open>
      Characterization of the completeness properties enjoyed by a set category:
      A set category @{term[source=true] S} has all limits at a type @{typ 'j},
      if and only if @{term[source=true] S} admits @{term I}-indexed tupling
      for all @{typ 'j}-sets @{term I} such that @{term "I \<noteq> UNIV"}.
\<close>

    theorem has_limits_iff_admits_tupling:
    shows "has_limits (undefined :: 'j) \<longleftrightarrow> (\<forall>I :: 'j set. I \<noteq> UNIV \<longrightarrow> admits_tupling I)"
    proof
      assume has_limits: "has_limits (undefined :: 'j)"
      show "\<forall>I :: 'j set. I \<noteq> UNIV \<longrightarrow> admits_tupling I"
        using has_limits has_products_if_has_limits has_products_iff_admits_tupling by blast
      next
      assume admits_tupling: "\<forall>I :: 'j set. I \<noteq> UNIV \<longrightarrow> admits_tupling I"
      show "has_limits (undefined :: 'j)"
      proof -
        have 1: "\<And>I :: 'j set. I \<noteq> UNIV \<Longrightarrow> has_products I"
          using admits_tupling has_products_iff_admits_tupling by auto
        have "\<And>J :: 'j comp. category J \<Longrightarrow> has_products (Collect (partial_magma.arr J))"
        proof -
          fix J :: "'j comp"
          assume J: "category J"
          interpret J: category J using J by auto
          have "Collect J.arr \<noteq> UNIV" using J.not_arr_null by blast
          thus "has_products (Collect J.arr)"
            using 1 by simp
        qed
        hence "\<And>J :: 'j comp. category J \<Longrightarrow> has_limits_of_shape J"
        proof -
          fix J :: "'j comp"
          assume J: "category J"
          interpret J: category J using J by auto
          show "has_limits_of_shape J"
          proof -
            have "Collect J.arr \<noteq> UNIV" using J.not_arr_null by fast
            moreover have "Collect J.ide \<noteq> UNIV" using J.not_arr_null by blast
            ultimately show ?thesis
              using 1 has_limits_if_has_products J.category_axioms by metis
          qed
        qed
        thus "has_limits (undefined :: 'j)"
          using has_limits_def by metis
      qed
    qed

  end

  section "Limits in Functor Categories"

  text\<open>
    In this section, we consider the special case of limits in functor categories,
    with the objective of showing that limits in a functor category \<open>[A, B]\<close>
    are given pointwise, and that \<open>[A, B]\<close> has all limits that @{term B} has.
\<close>

  locale parametrized_diagram =
    J: category J +
    A: category A +
    B: category B +
    JxA: product_category J A +
    binary_functor J A B D
  for J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and D :: "'j * 'a \<Rightarrow> 'b"
  begin

    (* Notation for A.in_hom and B.in_hom is being inherited, but from where? *)
    notation J.in_hom     ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>J _\<guillemotright>")
    notation JxA.comp     (infixr "\<cdot>\<^sub>J\<^sub>x\<^sub>A" 55)
    notation JxA.in_hom   ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>J\<^sub>x\<^sub>A _\<guillemotright>")

    text\<open>
      A choice of limit cone for each diagram \<open>D (-, a)\<close>, where @{term a}
      is an object of @{term[source=true] A}, extends to a functor \<open>L: A \<rightarrow> B\<close>,
      where the action of @{term L} on arrows of @{term[source=true] A} is determined by
      universality.
\<close>

    abbreviation L
    where "L \<equiv> \<lambda>l \<chi>. \<lambda>a. if A.arr a then
                            limit_cone.induced_arrow J B (\<lambda>j. D (j, A.cod a))
                              (l (A.cod a)) (\<chi> (A.cod a))
                              (l (A.dom a)) (vertical_composite.map J B
                                               (\<chi> (A.dom a)) (\<lambda>j. D (j, a)))
                          else B.null"

    abbreviation P
    where "P \<equiv> \<lambda>l \<chi>. \<lambda>a f. \<guillemotleft>f : l (A.dom a) \<rightarrow>\<^sub>B l (A.cod a)\<guillemotright> \<and>
                           diagram.cones_map J B (\<lambda>j. D (j, A.cod a)) f (\<chi> (A.cod a)) =
                           vertical_composite.map J B (\<chi> (A.dom a)) (\<lambda>j. D (j, a))"

    lemma L_arr:
    assumes "\<forall>a. A.ide a \<longrightarrow> limit_cone J B (\<lambda>j. D (j, a)) (l a) (\<chi> a)"
    shows "\<And>a. A.arr a \<Longrightarrow> (\<exists>!f. P l \<chi> a f) \<and> P l \<chi> a (L l \<chi> a)"
    proof
      fix a
      assume a: "A.arr a"
      interpret \<chi>_dom_a: limit_cone J B \<open>\<lambda>j. D (j, A.dom a)\<close> \<open>l (A.dom a)\<close> \<open>\<chi> (A.dom a)\<close>
        using a assms by auto
      interpret \<chi>_cod_a: limit_cone J B \<open>\<lambda>j. D (j, A.cod a)\<close> \<open>l (A.cod a)\<close> \<open>\<chi> (A.cod a)\<close>
        using a assms by auto
      interpret Da: natural_transformation J B \<open>\<lambda>j. D (j, A.dom a)\<close> \<open>\<lambda>j. D (j, A.cod a)\<close>
                                               \<open>\<lambda>j. D (j, a)\<close>
        using a fixing_arr_gives_natural_transformation_2 by simp
      interpret Dao\<chi>_dom_a: vertical_composite J B
                              \<chi>_dom_a.A.map \<open>\<lambda>j. D (j, A.dom a)\<close> \<open>\<lambda>j. D (j, A.cod a)\<close>
                              \<open>\<chi> (A.dom a)\<close> \<open>\<lambda>j. D (j, a)\<close> ..
      interpret Dao\<chi>_dom_a: cone J B \<open>\<lambda>j. D (j, A.cod a)\<close> \<open>l (A.dom a)\<close> Dao\<chi>_dom_a.map ..
      show "P l \<chi> a (L l \<chi> a)"
        using a Dao\<chi>_dom_a.cone_axioms
              \<chi>_cod_a.induced_arrowI [of Dao\<chi>_dom_a.map "l (A.dom a)"]
        by auto
      show "\<exists>!f. P l \<chi> a f"
        using \<chi>_cod_a.is_universal Dao\<chi>_dom_a.cone_axioms by blast
    qed

    lemma L_ide:
    assumes "\<forall>a. A.ide a \<longrightarrow> limit_cone J B (\<lambda>j. D (j, a)) (l a) (\<chi> a)"
    shows "\<And>a. A.ide a \<Longrightarrow> L l \<chi> a = l a"
    proof -
      let ?L = "L l \<chi>"
      let ?P = "P l \<chi>"
      fix a
      assume a: "A.ide a"
      interpret \<chi>a: limit_cone J B \<open>\<lambda>j. D (j, a)\<close> \<open>l a\<close> \<open>\<chi> a\<close> using a assms by auto
      have Pa: "?P a = (\<lambda>f. f \<in> B.hom (l a) (l a) \<and>
                            diagram.cones_map J B (\<lambda>j. D (j, a)) f (\<chi> a) = \<chi> a)"
        using a vcomp_ide_dom \<chi>a.natural_transformation_axioms by simp
      have "?P a (?L a)" using assms a L_arr [of l \<chi> a] by fastforce
      moreover have "?P a (l a)"
      proof -
        have "?P a (l a) \<longleftrightarrow> l a \<in> B.hom (l a) (l a) \<and> \<chi>a.D.cones_map (l a) (\<chi> a) = \<chi> a"
          using Pa by meson
        thus ?thesis
          using a \<chi>a.ide_apex \<chi>a.cone_axioms \<chi>a.D.cones_map_ide [of "\<chi> a" "l a"] by force
      qed
      moreover have "\<exists>!f. ?P a f"
        using a Pa \<chi>a.is_universal \<chi>a.cone_axioms by force
      ultimately show "?L a = l a" by blast
    qed

    lemma chosen_limits_induce_functor:
    assumes "\<forall>a. A.ide a \<longrightarrow> limit_cone J B (\<lambda>j. D (j, a)) (l a) (\<chi> a)"
    shows "functor A B (L l \<chi>)"
    proof -
      let ?L = "L l \<chi>"
      let ?P = "\<lambda>a. \<lambda>f. \<guillemotleft>f : l (A.dom a) \<rightarrow>\<^sub>B l (A.cod a)\<guillemotright> \<and>
                        diagram.cones_map J B (\<lambda>j. D (j, A.cod a)) f (\<chi> (A.cod a))
                             = vertical_composite.map J B (\<chi> (A.dom a)) (\<lambda>j. D (j, a))"
      interpret L: "functor" A B ?L
        apply unfold_locales
        using assms L_arr [of l] L_ide
            apply auto[4]
      proof -
        fix a' a
        assume 1: "A.arr (A a' a)"
        have a: "A.arr a" using 1 by auto
        have a': "\<guillemotleft>a' : A.cod a \<rightarrow>\<^sub>A A.cod a'\<guillemotright>" using 1 by auto
        have a'a: "A.seq a' a" using 1 by auto
        interpret \<chi>_dom_a: limit_cone J B \<open>\<lambda>j. D (j, A.dom a)\<close> \<open>l (A.dom a)\<close> \<open>\<chi> (A.dom a)\<close>
          using a assms by auto
        interpret \<chi>_cod_a: limit_cone J B \<open>\<lambda>j. D (j, A.cod a)\<close> \<open>l (A.cod a)\<close> \<open>\<chi> (A.cod a)\<close>
          using a'a assms by auto
        interpret \<chi>_dom_a'a: limit_cone J B \<open>\<lambda>j. D (j, A.dom (a' \<cdot>\<^sub>A a))\<close> \<open>l (A.dom (a' \<cdot>\<^sub>A a))\<close>
                                            \<open>\<chi> (A.dom (a' \<cdot>\<^sub>A a))\<close>
          using a'a assms by auto
        interpret \<chi>_cod_a'a: limit_cone J B \<open>\<lambda>j. D (j, A.cod (a' \<cdot>\<^sub>A a))\<close> \<open>l (A.cod (a' \<cdot>\<^sub>A a))\<close>
                                            \<open>\<chi> (A.cod (a' \<cdot>\<^sub>A a))\<close>
          using a'a assms by auto
        interpret Da: natural_transformation J B \<open>\<lambda>j. D (j, A.dom a)\<close> \<open>\<lambda>j. D (j, A.cod a)\<close>
                                                 \<open>\<lambda>j. D (j, a)\<close>
          using a fixing_arr_gives_natural_transformation_2 by simp
        interpret Da': natural_transformation J B \<open>\<lambda>j. D (j, A.cod a)\<close> \<open>\<lambda>j. D (j, A.cod (a' \<cdot>\<^sub>A a))\<close>
                                                  \<open>\<lambda>j. D (j, a')\<close>
          using a a'a fixing_arr_gives_natural_transformation_2 by fastforce
        interpret Da'o\<chi>_cod_a: vertical_composite J B
                                 \<chi>_cod_a.A.map \<open>\<lambda>j. D (j, A.cod a)\<close> \<open>\<lambda>j. D (j, A.cod (a' \<cdot>\<^sub>A a))\<close>
                                 \<open>\<chi> (A.cod a)\<close> \<open>\<lambda>j. D (j, a')\<close>..
        interpret Da'o\<chi>_cod_a: cone J B \<open>\<lambda>j. D (j, A.cod (a' \<cdot>\<^sub>A a))\<close> \<open>l (A.cod a)\<close> Da'o\<chi>_cod_a.map ..
        interpret Da'a: natural_transformation J B
                          \<open>\<lambda>j. D (j, A.dom (a' \<cdot>\<^sub>A a))\<close> \<open>\<lambda>j. D (j, A.cod (a' \<cdot>\<^sub>A a))\<close>
                          \<open>\<lambda>j. D (j, a' \<cdot>\<^sub>A a)\<close>
          using a'a fixing_arr_gives_natural_transformation_2 [of "a' \<cdot>\<^sub>A a"] by auto
        interpret Da'ao\<chi>_dom_a'a:
            vertical_composite J B \<chi>_dom_a'a.A.map \<open>\<lambda>j. D (j, A.dom (a' \<cdot>\<^sub>A a))\<close>
                                   \<open>\<lambda>j. D (j, A.cod (a' \<cdot>\<^sub>A a))\<close> \<open>\<chi> (A.dom (a' \<cdot>\<^sub>A a))\<close>
                                   \<open>\<lambda>j. D (j, a' \<cdot>\<^sub>A a)\<close> ..
        interpret Da'ao\<chi>_dom_a'a: cone J B \<open>\<lambda>j. D (j, A.cod (a' \<cdot>\<^sub>A a))\<close>
                                       \<open>l (A.dom (a' \<cdot>\<^sub>A a))\<close> Da'ao\<chi>_dom_a'a.map ..
        show "?L (a' \<cdot>\<^sub>A a) = ?L a' \<cdot>\<^sub>B ?L a"
        proof -
          have "?P (a' \<cdot>\<^sub>A a) (?L (a' \<cdot>\<^sub>A a))" using assms a'a L_arr [of l \<chi> "a' \<cdot>\<^sub>A a"] by fastforce
          moreover have "?P (a' \<cdot>\<^sub>A a) (?L a' \<cdot>\<^sub>B ?L a)"
          proof
            have La: "\<guillemotleft>?L a : l (A.dom a) \<rightarrow>\<^sub>B l (A.cod a)\<guillemotright>"
              using assms a L_arr by fast
            moreover have La': "\<guillemotleft>?L a' : l (A.cod a) \<rightarrow>\<^sub>B l (A.cod a')\<guillemotright>"
              using assms a a' L_arr [of l \<chi> a'] by auto
            ultimately have seq: "B.seq (?L a') (?L a)" by (elim B.in_homE, auto)
            thus La'_La: "\<guillemotleft>?L a' \<cdot>\<^sub>B ?L a : l (A.dom (a' \<cdot>\<^sub>A a)) \<rightarrow>\<^sub>B l (A.cod (a' \<cdot>\<^sub>A a))\<guillemotright>"
              using a a' 1 La La' by (intro B.comp_in_homI, auto)
            show "\<chi>_cod_a'a.D.cones_map (?L a' \<cdot>\<^sub>B ?L a) (\<chi> (A.cod (a' \<cdot>\<^sub>A a)))
                    = Da'ao\<chi>_dom_a'a.map"
            proof -
              have "\<chi>_cod_a'a.D.cones_map (?L a' \<cdot>\<^sub>B ?L a) (\<chi> (A.cod (a' \<cdot>\<^sub>A a)))
                       = (\<chi>_cod_a'a.D.cones_map (?L a) o \<chi>_cod_a'a.D.cones_map (?L a'))
                           (\<chi> (A.cod a'))"
              proof -
                have "\<chi>_cod_a'a.D.cones_map (?L a' \<cdot>\<^sub>B ?L a) (\<chi> (A.cod (a' \<cdot>\<^sub>A a))) =
                      restrict (\<chi>_cod_a'a.D.cones_map (?L a) \<circ> \<chi>_cod_a'a.D.cones_map (?L a'))
                               (\<chi>_cod_a'a.D.cones (B.cod (?L a')))
                               (\<chi> (A.cod (a' \<cdot>\<^sub>A a)))"
                  using seq \<chi>_cod_a'a.cone_axioms \<chi>_cod_a'a.D.cones_map_comp [of "?L a'" "?L a"]
                  by argo
                also have "... = (\<chi>_cod_a'a.D.cones_map (?L a) o \<chi>_cod_a'a.D.cones_map (?L a'))
                                 (\<chi> (A.cod a'))"
                proof -
                  have "\<chi> (A.cod a') \<in> \<chi>_cod_a'a.D.cones (l (A.cod a'))"
                    using \<chi>_cod_a'a.cone_axioms a'a by simp
                  moreover have "B.cod (?L a') = l (A.cod a')"
                    using assms a' L_arr [of l] by auto
                  ultimately show ?thesis
                    using a' a'a by simp
                qed
                finally show ?thesis by blast
              qed
              also have "... = \<chi>_cod_a'a.D.cones_map (?L a)
                                   (\<chi>_cod_a'a.D.cones_map (?L a') (\<chi> (A.cod a')))"
                  by simp
              also have "... = \<chi>_cod_a'a.D.cones_map (?L a) Da'o\<chi>_cod_a.map"
              proof -
                have "?P a' (?L a')" using assms a' L_arr [of l \<chi> a'] by fast
                moreover have
                    "?P a' = (\<lambda>f. f \<in> B.hom (l (A.cod a)) (l (A.cod a')) \<and>
                                  \<chi>_cod_a'a.D.cones_map f (\<chi> (A.cod a')) = Da'o\<chi>_cod_a.map)"
                  using a'a by force
                ultimately show ?thesis using a'a by force
              qed
              also have "... = vertical_composite.map J B
                                 (\<chi>_cod_a.D.cones_map (?L a) (\<chi> (A.cod a)))
                                 (\<lambda>j. D (j, a'))"
                using assms \<chi>_cod_a.D.diagram_axioms \<chi>_cod_a'a.D.diagram_axioms
                      Da'.natural_transformation_axioms \<chi>_cod_a.cone_axioms La
                      cones_map_vcomp [of J B "\<lambda>j. D (j, A.cod a)" "\<lambda>j. D (j, A.cod (a' \<cdot>\<^sub>A a))"
                                          "\<lambda>j. D (j, a')" "l (A.cod a)" "\<chi> (A.cod a)"
                                          "?L a" "l (A.dom a)"]
                by blast
              also have "... = vertical_composite.map J B
                                 (vertical_composite.map J B (\<chi> (A.dom a)) (\<lambda>j. D (j, a)))
                                 (\<lambda>j. D (j, a'))"
                using assms a L_arr by presburger
              also have "... = vertical_composite.map J B (\<chi> (A.dom a))
                                 (vertical_composite.map J B (\<lambda>j. D (j, a)) (\<lambda>j. D (j, a')))"
                using a'a Da.natural_transformation_axioms Da'.natural_transformation_axioms
                      \<chi>_dom_a.natural_transformation_axioms
                      vcomp_assoc [of J B \<chi>_dom_a.A.map "\<lambda>j. D (j, A.dom a)" "\<chi> (A.dom a)"
                                      "\<lambda>j. D (j, A.cod a)" "\<lambda>j. D (j, a)"
                                      "\<lambda>j. D (j, A.cod a')" "\<lambda>j. D (j, a')"]
                by auto
              also have
                  "... = vertical_composite.map J B (\<chi> (A.dom (a' \<cdot>\<^sub>A a))) (\<lambda>j. D (j, a' \<cdot>\<^sub>A a))"
                using a'a preserves_comp_2 by simp
              finally show ?thesis by auto
            qed
          qed
          moreover have "\<exists>!f. ?P (a' \<cdot>\<^sub>A a) f"
            using \<chi>_cod_a'a.is_universal
                    [of "l (A.dom (a' \<cdot>\<^sub>A a))"
                        "vertical_composite.map J B (\<chi> (A.dom (a' \<cdot>\<^sub>A a))) (\<lambda>j. D (j, a' \<cdot>\<^sub>A a))"]
                  Da'ao\<chi>_dom_a'a.cone_axioms
            by fast
          ultimately show ?thesis by blast
        qed
      qed
      show ?thesis ..
    qed

  end

  locale diagram_in_functor_category =
    A: category A +
    B: category B +
    A_B: functor_category A B +
    diagram J A_B.comp D
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and J :: "'j comp"      (infixr "\<cdot>\<^sub>J" 55)
  and D :: "'j \<Rightarrow> ('a, 'b) functor_category.arr"
  begin

    interpretation JxA: product_category J A ..
    interpretation A_BxA: product_category A_B.comp A ..
    interpretation E: evaluation_functor A B ..
    interpretation Curry: currying J A B ..

    notation JxA.comp     (infixr "\<cdot>\<^sub>J\<^sub>x\<^sub>A" 55)
    notation JxA.in_hom   ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>J\<^sub>x\<^sub>A _\<guillemotright>")

    text\<open>
      Evaluation of a functor or natural transformation from @{term[source=true] J}
      to \<open>[A, B]\<close> at an arrow @{term a} of @{term[source=true] A}.
\<close>

    abbreviation at
    where "at a \<tau> \<equiv> \<lambda>j. Curry.uncurry \<tau> (j, a)"

    lemma at_simp:
    assumes "A.arr a" and "J.arr j" and "A_B.arr (\<tau> j)"
    shows "at a \<tau> j = A_B.Map (\<tau> j) a"
      using assms Curry.uncurry_def E.map_simp by simp

    lemma functor_at_ide_is_functor:
    assumes "functor J A_B.comp F" and "A.ide a"
    shows "functor J B (at a F)"
    proof -
      interpret uncurry_F: "functor" JxA.comp B \<open>Curry.uncurry F\<close>
        using assms(1) Curry.uncurry_preserves_functors by simp
      interpret uncurry_F: binary_functor J A B \<open>Curry.uncurry F\<close> ..
      show ?thesis using assms(2) uncurry_F.fixing_ide_gives_functor_2 by simp
    qed

    lemma functor_at_arr_is_transformation:
    assumes "functor J A_B.comp F" and "A.arr a"
    shows "natural_transformation J B (at (A.dom a) F) (at (A.cod a) F) (at a F)"
    proof -
      interpret uncurry_F: "functor" JxA.comp B \<open>Curry.uncurry F\<close>
        using assms(1) Curry.uncurry_preserves_functors by simp
      interpret uncurry_F: binary_functor J A B \<open>Curry.uncurry F\<close> ..
      show ?thesis
        using assms(2) uncurry_F.fixing_arr_gives_natural_transformation_2 by simp
    qed

    lemma transformation_at_ide_is_transformation:
    assumes "natural_transformation J A_B.comp F G \<tau>" and "A.ide a"
    shows "natural_transformation J B (at a F) (at a G) (at a \<tau>)"
    proof -
      interpret \<tau>: natural_transformation J A_B.comp F G \<tau> using assms(1) by auto
      interpret uncurry_F: "functor" JxA.comp B \<open>Curry.uncurry F\<close>
        using Curry.uncurry_preserves_functors \<tau>.F.functor_axioms by simp
      interpret uncurry_f: binary_functor J A B \<open>Curry.uncurry F\<close> ..
      interpret uncurry_G: "functor" JxA.comp B \<open>Curry.uncurry G\<close>
        using Curry.uncurry_preserves_functors \<tau>.G.functor_axioms by simp
      interpret uncurry_G: binary_functor J A B \<open>Curry.uncurry G\<close> ..
      interpret uncurry_\<tau>: natural_transformation
                             JxA.comp B \<open>Curry.uncurry F\<close> \<open>Curry.uncurry G\<close> \<open>Curry.uncurry \<tau>\<close>
        using Curry.uncurry_preserves_transformations \<tau>.natural_transformation_axioms
        by simp
      interpret uncurry_\<tau>: binary_functor_transformation J A B
                            \<open>Curry.uncurry F\<close> \<open>Curry.uncurry G\<close> \<open>Curry.uncurry \<tau>\<close> ..
      show ?thesis
        using assms(2) uncurry_\<tau>.fixing_ide_gives_natural_transformation_2 by simp
    qed

    lemma constant_at_ide_is_constant:
    assumes "cone x \<chi>" and a: "A.ide a"
    shows "at a (constant_functor.map J A_B.comp x) =
           constant_functor.map J B (A_B.Map x a)"
    proof -
      interpret \<chi>: cone J A_B.comp D x \<chi> using assms(1) by auto
      have x: "A_B.ide x" using \<chi>.ide_apex by auto
      interpret Fun_x: "functor" A B \<open>A_B.Map x\<close>
        using x A_B.ide_char by simp
      interpret Da: "functor" J B \<open>at a D\<close>
        using a functor_at_ide_is_functor functor_axioms by blast
      interpret Da: diagram J B \<open>at a D\<close> ..
      interpret Xa: constant_functor J B \<open>A_B.Map x a\<close>
        using a Fun_x.preserves_ide [of a] by (unfold_locales, simp)
      show "at a \<chi>.A.map = Xa.map"
        using a x Curry.uncurry_def E.map_def Xa.is_extensional by auto
    qed

    lemma at_ide_is_diagram:
    assumes a: "A.ide a"
    shows "diagram J B (at a D)"
    proof -
      interpret Da: "functor" J B "at a D"
        using a functor_at_ide_is_functor functor_axioms by simp
      show ?thesis ..
    qed

    lemma cone_at_ide_is_cone:
    assumes "cone x \<chi>" and a: "A.ide a"
    shows "diagram.cone J B (at a D) (A_B.Map x a) (at a \<chi>)"
    proof -
      interpret \<chi>: cone J A_B.comp D x \<chi> using assms(1) by auto
      have x: "A_B.ide x" using \<chi>.ide_apex by auto
      interpret Fun_x: "functor" A B \<open>A_B.Map x\<close>
        using x A_B.ide_char by simp
      interpret Da: diagram J B \<open>at a D\<close> using a at_ide_is_diagram by auto
      interpret Xa: constant_functor J B \<open>A_B.Map x a\<close>
        using a by (unfold_locales, simp)
      interpret \<chi>a: natural_transformation J B Xa.map \<open>at a D\<close> \<open>at a \<chi>\<close>
        using assms(1) x a transformation_at_ide_is_transformation \<chi>.natural_transformation_axioms
              constant_at_ide_is_constant
        by fastforce
      interpret \<chi>a: cone J B \<open>at a D\<close> \<open>A_B.Map x a\<close> \<open>at a \<chi>\<close> ..
      show cone_\<chi>a: "Da.cone (A_B.Map x a) (at a \<chi>)" ..
    qed

    lemma at_preserves_comp:
    assumes "A.seq a' a"
    shows "at (A a' a) D = vertical_composite.map J B (at a D) (at a' D)"
    proof -
      interpret Da: natural_transformation J B \<open>at (A.dom a) D\<close> \<open>at (A.cod a) D\<close> \<open>at a D\<close>
        using assms functor_at_arr_is_transformation functor_axioms by blast
      interpret Da': natural_transformation J B \<open>at (A.cod a) D\<close> \<open>at (A.cod a') D\<close> \<open>at a' D\<close>
        using assms functor_at_arr_is_transformation [of D a'] functor_axioms by fastforce
      interpret Da'oDa: vertical_composite J B \<open>at (A.dom a) D\<close> \<open>at (A.cod a) D\<close> \<open>at (A.cod a') D\<close>
                                               \<open>at a D\<close> \<open>at a' D\<close> ..
      interpret Da'a: natural_transformation J B \<open>at (A.dom a) D\<close> \<open>at (A.cod a') D\<close> \<open>at (a' \<cdot>\<^sub>A a) D\<close>
        using assms functor_at_arr_is_transformation [of D "a' \<cdot>\<^sub>A a"] functor_axioms by simp
      show "at (a' \<cdot>\<^sub>A a) D = Da'oDa.map"
      proof (intro NaturalTransformation.eqI)
        show "natural_transformation J B (at (A.dom a) D) (at (A.cod a') D) Da'oDa.map" ..
        show "natural_transformation J B (at (A.dom a) D) (at (A.cod a') D) (at (a' \<cdot>\<^sub>A a) D)" ..
        show "\<And>j. J.ide j \<Longrightarrow> at (a' \<cdot>\<^sub>A a) D j = Da'oDa.map j"
        proof -
          fix j
          assume j: "J.ide j"
          interpret Dj: "functor" A B \<open>A_B.Map (D j)\<close>
            using j preserves_ide A_B.ide_char by simp
          show "at (a' \<cdot>\<^sub>A a) D j = Da'oDa.map j"
            using assms j Dj.preserves_comp at_simp Da'oDa.map_simp_ide by auto
        qed
      qed
    qed

    lemma cones_map_pointwise:
    assumes "cone x \<chi>" and "cone x' \<chi>'"
    and f: "f \<in> A_B.hom x' x"
    shows "cones_map f \<chi> = \<chi>' \<longleftrightarrow>
             (\<forall>a. A.ide a \<longrightarrow> diagram.cones_map J B (at a D) (A_B.Map f a) (at a \<chi>) = at a \<chi>')"
    proof
      interpret \<chi>: cone J A_B.comp D x \<chi> using assms(1) by auto
      interpret \<chi>': cone J A_B.comp D x' \<chi>' using assms(2) by auto
      have x: "A_B.ide x" using \<chi>.ide_apex by auto
      have x': "A_B.ide x'" using \<chi>'.ide_apex by auto
      interpret \<chi>f: cone J A_B.comp D x' \<open>cones_map f \<chi>\<close>
        using x' f assms(1) cones_map_mapsto by blast
      interpret Fun_x: "functor" A B \<open>A_B.Map x\<close> using x A_B.ide_char by simp
      interpret Fun_x': "functor" A B \<open>A_B.Map x'\<close> using x' A_B.ide_char by simp
      show "cones_map f \<chi> = \<chi>' \<Longrightarrow>
              (\<forall>a. A.ide a \<longrightarrow> diagram.cones_map J B (at a D) (A_B.Map f a) (at a \<chi>) = at a \<chi>')"
      proof -
        assume \<chi>': "cones_map f \<chi> = \<chi>'"
        have "\<And>a. A.ide a \<Longrightarrow> diagram.cones_map J B (at a D) (A_B.Map f a) (at a \<chi>) = at a \<chi>'"
        proof -
          fix a
          assume a: "A.ide a"
          interpret Da: diagram J B \<open>at a D\<close> using a at_ide_is_diagram by auto
          interpret \<chi>a: cone J B \<open>at a D\<close> \<open>A_B.Map x a\<close> \<open>at a \<chi>\<close>
            using a assms(1) cone_at_ide_is_cone by simp
          interpret \<chi>'a: cone J B \<open>at a D\<close> \<open>A_B.Map x' a\<close> \<open>at a \<chi>'\<close>
            using a assms(2) cone_at_ide_is_cone by simp
          have 1: "\<guillemotleft>A_B.Map f a : A_B.Map x' a \<rightarrow>\<^sub>B A_B.Map x a\<guillemotright>"
            using f a A_B.arr_char A_B.Map_cod A_B.Map_dom mem_Collect_eq
                  natural_transformation.preserves_hom A.ide_in_hom
            by (metis (no_types, lifting) A_B.in_homE)
          interpret \<chi>fa: cone J B \<open>at a D\<close> \<open>A_B.Map x' a\<close> \<open>Da.cones_map (A_B.Map f a) (at a \<chi>)\<close>
            using 1 \<chi>a.cone_axioms Da.cones_map_mapsto by force
          show "Da.cones_map (A_B.Map f a) (at a \<chi>) = at a \<chi>'"
          proof
            fix j
            have "\<not>J.arr j \<Longrightarrow> Da.cones_map (A_B.Map f a) (at a \<chi>) j = at a \<chi>' j"
              using \<chi>'a.is_extensional \<chi>fa.is_extensional [of j] by simp
            moreover have "J.arr j \<Longrightarrow> Da.cones_map (A_B.Map f a) (at a \<chi>) j = at a \<chi>' j"
              using a f 1 \<chi>.cone_axioms \<chi>a.cone_axioms at_simp apply simp
              apply (elim A_B.in_homE B.in_homE, auto)
              using \<chi>' \<chi>.A.map_simp A_B.Map_comp [of "\<chi> j" f a a] by auto
            ultimately show "Da.cones_map (A_B.Map f a) (at a \<chi>) j = at a \<chi>' j" by blast
          qed
        qed
        thus "\<forall>a. A.ide a \<longrightarrow> diagram.cones_map J B (at a D) (A_B.Map f a) (at a \<chi>) = at a \<chi>'"
          by simp
      qed
      show "\<forall>a. A.ide a \<longrightarrow> diagram.cones_map J B (at a D) (A_B.Map f a) (at a \<chi>) = at a \<chi>'
              \<Longrightarrow> cones_map f \<chi> = \<chi>'"
      proof -
        assume A:
            "\<forall>a. A.ide a \<longrightarrow> diagram.cones_map J B (at a D) (A_B.Map f a) (at a \<chi>) = at a \<chi>'"
        show "cones_map f \<chi> = \<chi>'"
        proof (intro NaturalTransformation.eqI)
          show "natural_transformation J A_B.comp \<chi>'.A.map D (cones_map f \<chi>)" ..
          show "natural_transformation J A_B.comp \<chi>'.A.map D \<chi>'" ..
          show "\<And>j. J.ide j \<Longrightarrow> cones_map f \<chi> j = \<chi>' j"
          proof (intro A_B.arr_eqI)
            fix j
            assume j: "J.ide j"
            show 1: "A_B.arr (cones_map f \<chi> j)"
              using j \<chi>f.preserves_reflects_arr by simp
            show "A_B.arr (\<chi>' j)" using j by auto
            have Dom_\<chi>f_j: "A_B.Dom (cones_map f \<chi> j) = A_B.Map x'"
              using x' j 1 A_B.Map_dom \<chi>'.A.map_simp [of "J.dom j"] \<chi>f.preserves_dom J.ide_in_hom
              by (metis (no_types, lifting) J.ideD(2) \<chi>f.preserves_reflects_arr)
            also have Dom_\<chi>'_j: "... = A_B.Dom (\<chi>' j)"
              using x' j A_B.Map_dom [of "\<chi>' j"] \<chi>'.preserves_hom \<chi>'.A.map_simp by simp
            finally show "A_B.Dom (cones_map f \<chi> j) = A_B.Dom (\<chi>' j)" by auto
            have Cod_\<chi>f_j: "A_B.Cod (cones_map f \<chi> j) = A_B.Map (D (J.cod j))"
              using j A_B.Map_cod [of "cones_map f \<chi> j"] A_B.cod_char J.ide_in_hom
                    \<chi>f.preserves_hom [of j "J.dom j" "J.cod j"]
              by (metis (no_types, lifting) "1" J.ideD(1) \<chi>f.preserves_cod)
            also have Cod_\<chi>'_j: "... = A_B.Cod (\<chi>' j)"
              using j A_B.Map_cod [of "\<chi>' j"] \<chi>'.preserves_hom by simp
            finally show "A_B.Cod (cones_map f \<chi> j) = A_B.Cod (\<chi>' j)" by auto
            show "A_B.Map (cones_map f \<chi> j) = A_B.Map (\<chi>' j)"
            proof (intro NaturalTransformation.eqI)
              interpret \<chi>fj: natural_transformation A B \<open>A_B.Map x'\<close> \<open>A_B.Map (D (J.cod j))\<close>
                                                    \<open>A_B.Map (cones_map f \<chi> j)\<close>
                using j \<chi>f.preserves_reflects_arr A_B.arr_char [of "cones_map f \<chi> j"]
                      Dom_\<chi>f_j Cod_\<chi>f_j
                by simp
              show "natural_transformation A B (A_B.Map x') (A_B.Map (D (J.cod j)))
                                           (A_B.Map (cones_map f \<chi> j))" ..
              interpret \<chi>'j: natural_transformation A B \<open>A_B.Map x'\<close> \<open>A_B.Map (D (J.cod j))\<close>
                                                   \<open>A_B.Map (\<chi>' j)\<close>
                using j A_B.arr_char [of "\<chi>' j"] Dom_\<chi>'_j Cod_\<chi>'_j by simp
              show "natural_transformation A B (A_B.Map x') (A_B.Map (D (J.cod j)))
                                           (A_B.Map (\<chi>' j))" ..
              show "\<And>a. A.ide a \<Longrightarrow> A_B.Map (cones_map f \<chi> j) a = A_B.Map (\<chi>' j) a"
              proof -
                fix a
                assume a: "A.ide a"
                interpret Da: diagram J B \<open>at a D\<close> using a at_ide_is_diagram by auto
                have cone_\<chi>a: "Da.cone (A_B.Map x a) (at a \<chi>)"
                  using a assms(1) cone_at_ide_is_cone by simp
                interpret \<chi>a: cone J B \<open>at a D\<close> \<open>A_B.Map x a\<close> \<open>at a \<chi>\<close>
                  using cone_\<chi>a by auto
                interpret Fun_f: natural_transformation A B \<open>A_B.Dom f\<close> \<open>A_B.Cod f\<close> \<open>A_B.Map f\<close>
                  using f A_B.arr_char by fast
                have fa: "A_B.Map f a \<in> B.hom (A_B.Map x' a) (A_B.Map x a)"
                  using a f Fun_f.preserves_hom A.ide_in_hom by auto
                have "A_B.Map (cones_map f \<chi> j) a = Da.cones_map (A_B.Map f a) (at a \<chi>) j"
                proof -
                  have "A_B.Map (cones_map f \<chi> j) a = A_B.Map (A_B.comp (\<chi> j) f) a"
                    using assms(1) f \<chi>.is_extensional by auto
                  also have "... = B (A_B.Map (\<chi> j) a) (A_B.Map f a)"
                    using f j a \<chi>.preserves_hom A.ide_in_hom J.ide_in_hom A_B.Map_comp
                          \<chi>.A.map_simp
                    by (metis (no_types, lifting) A.comp_ide_self A.ideD(1) A_B.seqI'
                        J.ideD(1) mem_Collect_eq)
                  also have "... = Da.cones_map (A_B.Map f a) (at a \<chi>) j"
                    using j a cone_\<chi>a fa Curry.uncurry_def E.map_simp by auto
                  finally show ?thesis by auto
                qed
                also have "... = at a \<chi>' j" using j a A by simp
                also have "... = A_B.Map (\<chi>' j) a"
                  using j Curry.uncurry_def E.map_simp \<chi>'j.is_extensional by simp
                finally show "A_B.Map (cones_map f \<chi> j) a = A_B.Map (\<chi>' j) a" by auto
              qed
            qed
          qed
        qed
      qed
    qed
       
    text\<open>
      If @{term \<chi>} is a cone with apex @{term a} over @{term D}, then @{term \<chi>}
      is a limit cone if, for each object @{term x} of @{term X}, the cone obtained
      by evaluating @{term \<chi>} at @{term x} is a limit cone with apex @{term "A_B.Map a x"}
      for the diagram in @{term C} obtained by evaluating @{term D} at @{term x}.
\<close>

    lemma cone_is_limit_if_pointwise_limit:
    assumes cone_\<chi>: "cone x \<chi>"
    and "\<forall>a. A.ide a \<longrightarrow> diagram.limit_cone J B (at a D) (A_B.Map x a) (at a \<chi>)"
    shows "limit_cone x \<chi>"
    proof -
      interpret \<chi>: cone J A_B.comp D x \<chi> using assms by auto
      have x: "A_B.ide x" using \<chi>.ide_apex by auto
      show "limit_cone x \<chi>"
      proof
        fix x' \<chi>'
        assume cone_\<chi>': "cone x' \<chi>'"
        interpret \<chi>': cone J A_B.comp D x' \<chi>' using cone_\<chi>' by auto
        have x': "A_B.ide x'" using \<chi>'.ide_apex by auto
        text\<open>
          The universality of the limit cone \<open>at a \<chi>\<close> yields, for each object
          \<open>a\<close> of \<open>A\<close>, a unique arrow \<open>fa\<close> that transforms
          \<open>at a \<chi>\<close> to \<open>at a \<chi>'\<close>.
\<close>
        have EU: "\<And>a. A.ide a \<Longrightarrow>
                        \<exists>!fa. fa \<in> B.hom (A_B.Map x' a) (A_B.Map x a) \<and>
                                   diagram.cones_map J B (at a D) fa (at a \<chi>) = at a \<chi>'"
        proof -
          fix a
          assume a: "A.ide a"
          interpret Da: diagram J B \<open>at a D\<close> using a at_ide_is_diagram by auto
          interpret \<chi>a: limit_cone J B \<open>at a D\<close> \<open>A_B.Map x a\<close> \<open>at a \<chi>\<close>
            using assms(2) a by auto
          interpret \<chi>'a: cone J B \<open>at a D\<close> \<open>A_B.Map x' a\<close> \<open>at a \<chi>'\<close>
            using a cone_\<chi>' cone_at_ide_is_cone by auto
          have "Da.cone (A_B.Map x' a) (at a \<chi>')" ..
          thus "\<exists>!fa. fa \<in> B.hom (A_B.Map x' a) (A_B.Map x a) \<and>
                      Da.cones_map fa (at a \<chi>) = at a \<chi>'"
            using \<chi>a.is_universal by simp
        qed
        text\<open>
          Our objective is to show the existence of a unique arrow \<open>f\<close> that transforms
          \<open>\<chi>\<close> into \<open>\<chi>'\<close>.  We obtain \<open>f\<close> by bundling the arrows \<open>fa\<close>
          of \<open>C\<close> and proving that this yields a natural transformation from \<open>X\<close>
          to \<open>C\<close>, hence an arrow of \<open>[X, C]\<close>.
\<close>
        show "\<exists>!f. \<guillemotleft>f : x' \<rightarrow>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>] x\<guillemotright> \<and> cones_map f \<chi> = \<chi>'"
        proof
          let ?P = "\<lambda>a fa. \<guillemotleft>fa : A_B.Map x' a \<rightarrow>\<^sub>B A_B.Map x a\<guillemotright> \<and>
                           diagram.cones_map J B (at a D) fa (at a \<chi>) = at a \<chi>'"
          have AaPa: "\<And>a. A.ide a \<Longrightarrow> ?P a (THE fa. ?P a fa)"
          proof -
            fix a
            assume a: "A.ide a"
            have "\<exists>!fa. ?P a fa" using a EU by simp
            thus "?P a (THE fa. ?P a fa)" using a theI' [of "?P a"] by fastforce
          qed
          have AaPa_in_hom:
              "\<And>a. A.ide a \<Longrightarrow> \<guillemotleft>THE fa. ?P a fa : A_B.Map x' a \<rightarrow>\<^sub>B A_B.Map x a\<guillemotright>"
            using AaPa by blast
          have AaPa_map:
                  "\<And>a. A.ide a \<Longrightarrow>
                       diagram.cones_map J B (at a D) (THE fa. ?P a fa) (at a \<chi>) = at a \<chi>'"
            using AaPa by blast
          let ?Fun_f = "\<lambda>a. if A.ide a then (THE fa. ?P a fa) else B.null"
          interpret Fun_x: "functor" A B \<open>\<lambda>a. A_B.Map x a\<close>
            using x A_B.ide_char by simp
          interpret Fun_x': "functor" A B \<open>\<lambda>a. A_B.Map x' a\<close>
            using x' A_B.ide_char by simp
          text\<open>
            The arrows \<open>Fun_f a\<close> are the components of a natural transformation.
            It is more work to verify the naturality than it seems like it ought to be.
\<close>
          interpret \<phi>: transformation_by_components A B
                         \<open>\<lambda>a. A_B.Map x' a\<close> \<open>\<lambda>a. A_B.Map x a\<close> ?Fun_f
          proof
            fix a
            assume a: "A.ide a"
            show "\<guillemotleft>?Fun_f a : A_B.Map x' a \<rightarrow>\<^sub>B A_B.Map x a\<guillemotright>" using a AaPa by simp
            next
            fix a
            assume a: "A.arr a"
            text\<open>
\newcommand\xdom{\mathop{\rm dom}}
\newcommand\xcod{\mathop{\rm cod}}
$$\xymatrix{
  {x_{\xdom a}} \drtwocell\omit{\omit(A)} \ar[d]_{\chi_{\xdom a}} \ar[r]^{x_a} & {x_{\xcod a}}
     \ar[d]^{\chi_{\xcod a}} \\
  {D_{\xdom a}} \ar[r]^{D_a} & {D_{\xcod a}} \\
  {x'_{\xdom a}} \urtwocell\omit{\omit(B)} \ar@/^5em/[uu]^{f_{\xdom a}}_{\hspace{1em}(C)} \ar[u]^{\chi'_{\xdom a}}
     \ar[r]_{x'_a} & {x'_{\xcod a}} \ar[u]_{x'_{\xcod a}} \ar@/_5em/[uu]_{f_{\xcod a}}
}$$
\<close>
            let ?x_dom_a = "A_B.Map x (A.dom a)"
            let ?x_cod_a = "A_B.Map x (A.cod a)"
            let ?x_a = "A_B.Map x a"
            have x_a: "\<guillemotleft>?x_a : ?x_dom_a \<rightarrow>\<^sub>B ?x_cod_a\<guillemotright>"
              using a x A_B.ide_char by auto
            have x_dom_a: "B.ide ?x_dom_a" using a by simp
            have x_cod_a: "B.ide ?x_cod_a" using a by simp
            let ?x'_dom_a = "A_B.Map x' (A.dom a)"
            let ?x'_cod_a = "A_B.Map x' (A.cod a)"
            let ?x'_a = "A_B.Map x' a"
            have x'_a: "\<guillemotleft>?x'_a : ?x'_dom_a \<rightarrow>\<^sub>B ?x'_cod_a\<guillemotright>"
              using a x' A_B.ide_char by auto
            have x'_dom_a: "B.ide ?x'_dom_a" using a by simp
            have x'_cod_a: "B.ide ?x'_cod_a" using a by simp
            let ?f_dom_a = "?Fun_f (A.dom a)"
            let ?f_cod_a = "?Fun_f (A.cod a)"
            have f_dom_a: "\<guillemotleft>?f_dom_a : ?x'_dom_a \<rightarrow>\<^sub>B ?x_dom_a\<guillemotright>" using a AaPa by simp
            have f_cod_a: "\<guillemotleft>?f_cod_a : ?x'_cod_a \<rightarrow>\<^sub>B ?x_cod_a\<guillemotright>" using a AaPa by simp
            interpret D_dom_a: diagram J B \<open>at (A.dom a) D\<close> using a at_ide_is_diagram by simp
            interpret D_cod_a: diagram J B \<open>at (A.cod a) D\<close> using a at_ide_is_diagram by simp
            interpret Da: natural_transformation J B \<open>at (A.dom a) D\<close> \<open>at (A.cod a) D\<close> \<open>at a D\<close>
              using a functor_axioms functor_at_arr_is_transformation by simp
            interpret \<chi>_dom_a: limit_cone J B \<open>at (A.dom a) D\<close> \<open>A_B.Map x (A.dom a)\<close>
                                              \<open>at (A.dom a) \<chi>\<close>
              using assms(2) a by auto
            interpret \<chi>_cod_a: limit_cone J B \<open>at (A.cod a) D\<close> \<open>A_B.Map x (A.cod a)\<close>
                                              \<open>at (A.cod a) \<chi>\<close>
              using assms(2) a by auto
            interpret \<chi>'_dom_a: cone J B \<open>at (A.dom a) D\<close> \<open>A_B.Map x' (A.dom a)\<close> \<open>at (A.dom a) \<chi>'\<close>
              using a cone_\<chi>' cone_at_ide_is_cone by auto
            interpret \<chi>'_cod_a: cone J B \<open>at (A.cod a) D\<close> \<open>A_B.Map x' (A.cod a)\<close> \<open>at (A.cod a) \<chi>'\<close>
              using a cone_\<chi>' cone_at_ide_is_cone by auto
            text\<open>
              Now construct cones with apexes \<open>x_dom_a\<close> and \<open>x'_dom_a\<close>
              over @{term "at (A.cod a) D"} by forming the vertical composites of
              @{term "at (A.dom a) \<chi>"} and @{term "at (A.cod a) \<chi>'"} with the natural
              transformation @{term "at a D"}.
\<close>
            interpret Dao\<chi>_dom_a: vertical_composite J B
                                    \<chi>_dom_a.A.map \<open>at (A.dom a) D\<close> \<open>at (A.cod a) D\<close>
                                    \<open>at (A.dom a) \<chi>\<close> \<open>at a D\<close> ..
            interpret Dao\<chi>_dom_a: cone J B \<open>at (A.cod a) D\<close> ?x_dom_a Dao\<chi>_dom_a.map
              using \<chi>_dom_a.cone_axioms Da.natural_transformation_axioms vcomp_transformation_cone
              by metis
            interpret Dao\<chi>'_dom_a: vertical_composite J B
                                     \<chi>'_dom_a.A.map \<open>at (A.dom a) D\<close> \<open>at (A.cod a) D\<close>
                                     \<open>at (A.dom a) \<chi>'\<close> \<open>at a D\<close> ..
            interpret Dao\<chi>'_dom_a: cone J B \<open>at (A.cod a) D\<close> ?x'_dom_a Dao\<chi>'_dom_a.map
              using \<chi>'_dom_a.cone_axioms Da.natural_transformation_axioms vcomp_transformation_cone
              by metis
            have Dao\<chi>_dom_a: "D_cod_a.cone ?x_dom_a Dao\<chi>_dom_a.map" ..
            have Dao\<chi>'_dom_a: "D_cod_a.cone ?x'_dom_a Dao\<chi>'_dom_a.map" ..
            text\<open>
              These cones are also obtained by transforming the cones @{term "at (A.cod a) \<chi>"}
              and @{term "at (A.cod a) \<chi>'"} by \<open>x_a\<close> and \<open>x'_a\<close>, respectively.
\<close>
            have A: "Dao\<chi>_dom_a.map = D_cod_a.cones_map ?x_a (at (A.cod a) \<chi>)"
            proof
              fix j
              have "\<not>J.arr j \<Longrightarrow> Dao\<chi>_dom_a.map j = D_cod_a.cones_map ?x_a (at (A.cod a) \<chi>) j"
                using Dao\<chi>_dom_a.is_extensional \<chi>_cod_a.cone_axioms x_a by force
              moreover have
                   "J.arr j \<Longrightarrow> Dao\<chi>_dom_a.map j = D_cod_a.cones_map ?x_a (at (A.cod a) \<chi>) j"
              proof -
                assume j: "J.arr j"
                have "Dao\<chi>_dom_a.map j = at a D j \<cdot>\<^sub>B at (A.dom a) \<chi> (J.dom j)"
                  using j Dao\<chi>_dom_a.map_simp_2 by simp
                also have "... = A_B.Map (D j) a \<cdot>\<^sub>B A_B.Map (\<chi> (J.dom j)) (A.dom a)"
                  using a j at_simp by simp
                also have "... = A_B.Map (A_B.comp (D j) (\<chi> (J.dom j))) a"
                  using a j A_B.Map_comp
                  by (metis (no_types, lifting) A.comp_arr_dom \<chi>.is_natural_1
                      \<chi>.preserves_reflects_arr)
                also have "... = A_B.Map (A_B.comp (\<chi> (J.cod j)) (\<chi>.A.map j)) a"
                  using a j \<chi>.naturality by simp
                also have "... = A_B.Map (\<chi> (J.cod j)) (A.cod a) \<cdot>\<^sub>B A_B.Map x a"
                  using a j x A_B.Map_comp
                  by (metis (no_types, lifting) A.comp_cod_arr \<chi>.A.map_simp \<chi>.is_natural_2
                            \<chi>.preserves_reflects_arr)
                also have "... = at (A.cod a) \<chi> (J.cod j) \<cdot>\<^sub>B A_B.Map x a"
                  using a j at_simp by simp
                also have "... = at (A.cod a) \<chi> j \<cdot>\<^sub>B A_B.Map x a"
                  using a j \<chi>_cod_a.is_natural_2 \<chi>_cod_a.A.map_simp
                  by (metis J.arr_cod_iff_arr J.cod_cod)
                also have "... = D_cod_a.cones_map ?x_a (at (A.cod a) \<chi>) j"
                  using a j x \<chi>_cod_a.cone_axioms preserves_cod by simp
                finally show ?thesis by blast
              qed
              ultimately show "Dao\<chi>_dom_a.map j = D_cod_a.cones_map ?x_a (at (A.cod a) \<chi>) j"
                by blast
            qed
            have B: "Dao\<chi>'_dom_a.map = D_cod_a.cones_map ?x'_a (at (A.cod a) \<chi>')"
            proof
              fix j
              have
                  "\<not>J.arr j \<Longrightarrow> Dao\<chi>'_dom_a.map j = D_cod_a.cones_map ?x'_a (at (A.cod a) \<chi>') j"
                using Dao\<chi>'_dom_a.is_extensional \<chi>'_cod_a.cone_axioms x'_a by force
              moreover have
                  "J.arr j \<Longrightarrow> Dao\<chi>'_dom_a.map j = D_cod_a.cones_map ?x'_a (at (A.cod a) \<chi>') j"
              proof -
                assume j: "J.arr j"
                have "Dao\<chi>'_dom_a.map j = at a D j \<cdot>\<^sub>B at (A.dom a) \<chi>' (J.dom j)"
                  using j Dao\<chi>'_dom_a.map_simp_2 by simp
                also have "... = A_B.Map (D j) a \<cdot>\<^sub>B A_B.Map (\<chi>' (J.dom j)) (A.dom a)"
                  using a j at_simp by simp
                also have "... = A_B.Map (A_B.comp (D j) (\<chi>' (J.dom j))) a"
                  using a j A_B.Map_comp
                  by (metis (no_types, lifting) A.comp_arr_dom \<chi>'.is_natural_1
                      \<chi>'.preserves_reflects_arr)
                also have "... = A_B.Map (A_B.comp (\<chi>' (J.cod j)) (\<chi>'.A.map j)) a"
                  using a j \<chi>'.naturality by simp
                also have "... = A_B.Map (\<chi>' (J.cod j)) (A.cod a) \<cdot>\<^sub>B A_B.Map x' a"
                  using a j x' A_B.Map_comp
                  by (metis (no_types, lifting) A.comp_cod_arr \<chi>'.A.map_simp \<chi>'.is_natural_2
                            \<chi>'.preserves_reflects_arr)
                also have "... = at (A.cod a) \<chi>' (J.cod j) \<cdot>\<^sub>B A_B.Map x' a"
                  using a j at_simp by simp
                also have "... = at (A.cod a) \<chi>' j \<cdot>\<^sub>B A_B.Map x' a"
                  using a j \<chi>'_cod_a.is_natural_2 \<chi>'_cod_a.A.map_simp
                  by (metis J.arr_cod_iff_arr J.cod_cod)
                also have "... = D_cod_a.cones_map ?x'_a (at (A.cod a) \<chi>') j"
                  using a j x' \<chi>'_cod_a.cone_axioms preserves_cod by simp
                finally show ?thesis by blast
              qed
              ultimately show
                  "Dao\<chi>'_dom_a.map j = D_cod_a.cones_map ?x'_a (at (A.cod a) \<chi>') j"
                by blast
            qed
            text\<open>
              Next, we show that \<open>f_dom_a\<close>, which is the unique arrow that transforms
              \<open>\<chi>_dom_a\<close> into \<open>\<chi>'_dom_a\<close>, is also the unique arrow that transforms
              \<open>Dao\<chi>_dom_a\<close> into \<open>Dao\<chi>'_dom_a\<close>.
\<close>
            have C: "D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map = Dao\<chi>'_dom_a.map"
            proof (intro NaturalTransformation.eqI)
              show "natural_transformation
                      J B \<chi>'_dom_a.A.map (at (A.cod a) D) Dao\<chi>'_dom_a.map" ..
              show "natural_transformation J B \<chi>'_dom_a.A.map (at (A.cod a) D)
                      (D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map)"
              proof -
                interpret \<kappa>: cone J B \<open>at (A.cod a) D\<close> ?x'_dom_a
                                  \<open>D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map\<close>
                proof -
                  have 1: "\<And>b b' f. \<lbrakk> f \<in> B.hom b' b; D_cod_a.cone b Dao\<chi>_dom_a.map \<rbrakk>
                                     \<Longrightarrow> D_cod_a.cone b' (D_cod_a.cones_map f Dao\<chi>_dom_a.map)"
                    using D_cod_a.cones_map_mapsto by blast
                  have "D_cod_a.cone ?x_dom_a Dao\<chi>_dom_a.map" ..
                  thus "D_cod_a.cone ?x'_dom_a (D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map)"
                    using f_dom_a 1 by simp
                qed
                show ?thesis ..
              qed
              show "\<And>j. J.ide j \<Longrightarrow>
                          D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map j = Dao\<chi>'_dom_a.map j"
              proof -
                fix j
                assume j: "J.ide j"
                have "D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map j =
                      Dao\<chi>_dom_a.map j \<cdot>\<^sub>B ?f_dom_a"
                  using j f_dom_a Dao\<chi>_dom_a.cone_axioms
                  by (elim B.in_homE, auto)
                also have "... = (at a D j \<cdot>\<^sub>B at (A.dom a) \<chi> j) \<cdot>\<^sub>B ?f_dom_a"
                  using j Dao\<chi>_dom_a.map_simp_ide by simp
                also have "... = at a D j \<cdot>\<^sub>B at (A.dom a) \<chi> j \<cdot>\<^sub>B ?f_dom_a"
                  using B.comp_assoc by simp
                also have "... = at a D j \<cdot>\<^sub>B D_dom_a.cones_map ?f_dom_a (at (A.dom a) \<chi>) j"
                  using j \<chi>_dom_a.cone_axioms f_dom_a
                  by (elim B.in_homE, auto)
                also have "... = at a D j \<cdot>\<^sub>B at (A.dom a) \<chi>' j"
                  using a AaPa A.ide_dom by presburger
                also have "... = Dao\<chi>'_dom_a.map j"
                  using j Dao\<chi>'_dom_a.map_simp_ide by simp
                finally show
                    "D_cod_a.cones_map ?f_dom_a Dao\<chi>_dom_a.map j = Dao\<chi>'_dom_a.map j"
                  by auto
              qed
            qed
            text\<open>
              Naturality amounts to showing that \<open>C f_cod_a x'_a = C x_a f_dom_a\<close>.
              To do this, we show that both arrows transform @{term "at (A.cod a) \<chi>"}
              into \<open>Dao\<chi>'_cod_a\<close>, thus they are equal by the universality of
              @{term "at (A.cod a) \<chi>"}.
\<close>
            have "\<exists>!fa. \<guillemotleft>fa : ?x'_dom_a \<rightarrow>\<^sub>B ?x_cod_a\<guillemotright> \<and>
                        D_cod_a.cones_map fa (at (A.cod a) \<chi>) = Dao\<chi>'_dom_a.map"
              using Dao\<chi>'_dom_a.cone_axioms a \<chi>_cod_a.is_universal [of ?x'_dom_a Dao\<chi>'_dom_a.map]
              by fast
            moreover have
                 "?f_cod_a \<cdot>\<^sub>B ?x'_a \<in> B.hom ?x'_dom_a ?x_cod_a \<and>
                  D_cod_a.cones_map (?f_cod_a \<cdot>\<^sub>B ?x'_a) (at (A.cod a) \<chi>) = Dao\<chi>'_dom_a.map"
            proof
              show "?f_cod_a \<cdot>\<^sub>B ?x'_a \<in> B.hom ?x'_dom_a ?x_cod_a"
                using f_cod_a x'_a by blast
              show "D_cod_a.cones_map (?f_cod_a \<cdot>\<^sub>B ?x'_a) (at (A.cod a) \<chi>) = Dao\<chi>'_dom_a.map"
              proof -
                have 1: "B.arr (?f_cod_a \<cdot>\<^sub>B ?x'_a)"
                  using f_cod_a x'_a by (elim B.in_homE, auto)
                hence "D_cod_a.cones_map (?f_cod_a \<cdot>\<^sub>B ?x'_a) (at (A.cod a) \<chi>)
                         = restrict (D_cod_a.cones_map ?x'_a o D_cod_a.cones_map ?f_cod_a)
                                    (D_cod_a.cones (?x_cod_a))
                                    (at (A.cod a) \<chi>)"
                  using D_cod_a.cones_map_comp [of ?f_cod_a ?x'_a] f_cod_a
                  by (elim B.in_homE, auto)
                also have "... = D_cod_a.cones_map ?x'_a
                                   (D_cod_a.cones_map ?f_cod_a (at (A.cod a) \<chi>))"
                  using \<chi>_cod_a.cone_axioms by simp
                also have "... = Dao\<chi>'_dom_a.map"
                  using a B AaPa_map A.ide_cod by presburger
                finally show ?thesis by auto
              qed
            qed
            moreover have
                 "?x_a \<cdot>\<^sub>B ?f_dom_a \<in> B.hom ?x'_dom_a ?x_cod_a \<and>
                  D_cod_a.cones_map (?x_a \<cdot>\<^sub>B ?f_dom_a) (at (A.cod a) \<chi>) = Dao\<chi>'_dom_a.map"
            proof
              show "?x_a \<cdot>\<^sub>B ?f_dom_a \<in> B.hom ?x'_dom_a ?x_cod_a"
                using f_dom_a x_a by blast
              show "D_cod_a.cones_map (?x_a \<cdot>\<^sub>B ?f_dom_a) (at (A.cod a) \<chi>) = Dao\<chi>'_dom_a.map"
              proof -
                have
                    "D_cod_a.cones (B.cod (A_B.Map x a)) = D_cod_a.cones (A_B.Map x (A.cod a))"
                  using a x by simp
                moreover have "B.seq ?x_a ?f_dom_a"
                  using f_dom_a x_a by (elim B.in_homE, auto)
                ultimately have
                     "D_cod_a.cones_map (?x_a \<cdot>\<^sub>B ?f_dom_a) (at (A.cod a) \<chi>)
                         = restrict (D_cod_a.cones_map ?f_dom_a o D_cod_a.cones_map ?x_a)
                                    (D_cod_a.cones (?x_cod_a))
                                    (at (A.cod a) \<chi>)"
                  using D_cod_a.cones_map_comp [of ?x_a ?f_dom_a] x_a by argo
                also have "... = D_cod_a.cones_map ?f_dom_a
                                   (D_cod_a.cones_map ?x_a (at (A.cod a) \<chi>))"
                  using \<chi>_cod_a.cone_axioms by simp
                also have "... = Dao\<chi>'_dom_a.map"
                  using A C a AaPa by argo
                finally show ?thesis by blast
              qed
            qed
            ultimately show "?f_cod_a \<cdot>\<^sub>B ?x'_a = ?x_a \<cdot>\<^sub>B ?f_dom_a"
              using a \<chi>_cod_a.is_universal by blast
          qed
          text\<open>
            The arrow from @{term x'} to @{term x} in \<open>[A, B]\<close> determined by
            the natural transformation \<open>\<phi>\<close> transforms @{term \<chi>} into @{term \<chi>'}.
            Moreover, it is the unique such arrow, since the components of \<open>\<phi>\<close>
            are each determined by universality.
\<close>
          let ?f = "A_B.MkArr (\<lambda>a. A_B.Map x' a) (\<lambda>a. A_B.Map x a) \<phi>.map"
          have f_in_hom: "?f \<in> A_B.hom x' x"
          proof -
            have arr_f: "A_B.arr ?f"
              using x' x A_B.arr_MkArr \<phi>.natural_transformation_axioms by simp
            moreover have "A_B.MkIde (\<lambda>a. A_B.Map x a) = x"
              using x A_B.ide_char A_B.MkArr_Map A_B.in_homE A_B.ide_in_hom by metis
            moreover have "A_B.MkIde (\<lambda>a. A_B.Map x' a) = x'"
              using x' A_B.ide_char A_B.MkArr_Map A_B.in_homE A_B.ide_in_hom by metis
            ultimately show ?thesis
              using A_B.dom_char A_B.cod_char by auto
          qed
          have Fun_f: "\<And>a. A.ide a \<Longrightarrow> A_B.Map ?f a = (THE fa. ?P a fa)"
            using f_in_hom \<phi>.map_simp_ide by fastforce
          have cones_map_f: "cones_map ?f \<chi> = \<chi>'"
            using AaPa Fun_f at_ide_is_diagram assms(2) x x' cone_\<chi> cone_\<chi>' f_in_hom Fun_f
                  cones_map_pointwise
            by presburger
          show "\<guillemotleft>?f : x' \<rightarrow>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>] x\<guillemotright> \<and> cones_map ?f \<chi> = \<chi>'" using f_in_hom cones_map_f by auto
          show "\<And>f'. \<guillemotleft>f' : x' \<rightarrow>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>] x\<guillemotright> \<and> cones_map f' \<chi> = \<chi>' \<Longrightarrow> f' = ?f"
          proof -
            fix f'
            assume f': "\<guillemotleft>f' : x' \<rightarrow>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>] x\<guillemotright> \<and> cones_map f' \<chi> = \<chi>'"
            have 0: "\<And>a. A.ide a \<Longrightarrow>
                           diagram.cones_map J B (at a D) (A_B.Map f' a) (at a \<chi>) = at a \<chi>'"
              using f' cone_\<chi> cone_\<chi>' cones_map_pointwise by blast
            have "f' = A_B.MkArr (A_B.Dom f') (A_B.Cod f') (A_B.Map f')"
              using f' A_B.MkArr_Map by auto
            also have "... = ?f"
            proof (intro A_B.MkArr_eqI)
              show "A_B.arr (A_B.MkArr (A_B.Dom f') (A_B.Cod f') (A_B.Map f'))"
                using f' calculation by blast
              show 1: "A_B.Dom f' = A_B.Map x'" using f' A_B.Map_dom by auto
              show 2: "A_B.Cod f' = A_B.Map x" using f' A_B.Map_cod by auto
              show "A_B.Map f' = \<phi>.map"
              proof (intro NaturalTransformation.eqI)
                show "natural_transformation A B (A_B.Map x') (A_B.Map x) \<phi>.map" ..
                show "natural_transformation A B (A_B.Map x') (A_B.Map x) (A_B.Map f')"
                  using f' 1 2 A_B.arr_char [of f'] by auto
                show "\<And>a. A.ide a \<Longrightarrow> A_B.Map f' a = \<phi>.map a"
                proof -
                  fix a
                  assume a: "A.ide a"
                  interpret Da: diagram J B \<open>at a D\<close> using a at_ide_is_diagram by auto
                  interpret Fun_f': natural_transformation A B \<open>A_B.Dom f'\<close> \<open>A_B.Cod f'\<close>
                                                           \<open>A_B.Map f'\<close>
                    using f' A_B.arr_char by fast
                  have "A_B.Map f' a \<in> B.hom (A_B.Map x' a) (A_B.Map x a)"
                    using a f' Fun_f'.preserves_hom A.ide_in_hom by auto
                  hence "?P a (A_B.Map f' a)" using a 0 [of a] by simp
                  moreover have "?P a (\<phi>.map a)"
                    using a \<phi>.map_simp_ide Fun_f AaPa by presburger
                  ultimately show "A_B.Map f' a = \<phi>.map a" using a EU by blast
                qed
              qed
            qed
            finally show "f' = ?f" by auto
          qed
        qed
      qed
    qed

  end

  context functor_category
  begin

    text\<open>
      A functor category \<open>[A, B]\<close> has limits of shape @{term[source=true] J}
      whenever @{term B} has limits of shape @{term[source=true] J}.
\<close>

    lemma has_limits_of_shape_if_target_does:
    assumes "category (J :: 'j comp)"
    and "B.has_limits_of_shape J"
    shows "has_limits_of_shape J"
    proof (unfold has_limits_of_shape_def)
      have "\<And>D. diagram J comp D \<Longrightarrow> (\<exists>x \<chi>. limit_cone J comp D x \<chi>)"
      proof -
        fix D
        assume D: "diagram J comp D"
        interpret J: category J using assms(1) by auto
        interpret JxA: product_category J A ..
        interpret D: diagram J comp D using D by auto
        interpret D: diagram_in_functor_category A B J D ..
        interpret Curry: currying J A B ..
        text\<open>
          Given diagram @{term D} in \<open>[A, B]\<close>, choose for each object \<open>a\<close>
          of \<open>A\<close> a limit cone \<open>(la, \<chi>a)\<close> for \<open>at a D\<close> in \<open>B\<close>.
\<close>
        let ?l = "\<lambda>a. diagram.some_limit J B (D.at a D)"
        let ?\<chi> = "\<lambda>a. diagram.some_limit_cone J B (D.at a D)"
        have l\<chi>: "\<And>a. A.ide a \<Longrightarrow> diagram.limit_cone J B (D.at a D) (?l a) (?\<chi> a)"
        proof -
          fix a
          assume a: "A.ide a"
          interpret Da: diagram J B \<open>D.at a D\<close>
            using a D.at_ide_is_diagram by blast
          show "limit_cone J B (D.at a D) (?l a) (?\<chi> a)"
            using assms(2) B.has_limits_of_shape_def Da.diagram_axioms
                  Da.limit_cone_some_limit_cone
            by auto
        qed
        text\<open>
          The choice of limit cones induces a limit functor from \<open>A\<close> to \<open>B\<close>.
\<close>
        interpret uncurry_D: diagram JxA.comp B "Curry.uncurry D"
        proof -
          interpret "functor" JxA.comp B \<open>Curry.uncurry D\<close>
            using D.functor_axioms Curry.uncurry_preserves_functors by simp
          interpret binary_functor J A B \<open>Curry.uncurry D\<close> ..
          show "diagram JxA.comp B (Curry.uncurry D)" ..
        qed
        interpret uncurry_D: parametrized_diagram J A B \<open>Curry.uncurry D\<close> ..
        let ?L = "uncurry_D.L ?l ?\<chi>"
        let ?P = "uncurry_D.P ?l ?\<chi>"
        interpret L: "functor" A B ?L
          using l\<chi> uncurry_D.chosen_limits_induce_functor [of ?l ?\<chi>] by simp
        have L_ide: "\<And>a. A.ide a \<Longrightarrow> ?L a = ?l a"
          using uncurry_D.L_ide [of ?l ?\<chi>] l\<chi> by blast
        have L_arr: "\<And>a. A.arr a \<Longrightarrow> (\<exists>!f. ?P a f) \<and> ?P a (?L a)"
          using uncurry_D.L_arr [of ?l ?\<chi>] l\<chi> by blast
        have L_arr_in_hom: "\<And>a. A.arr a \<Longrightarrow> \<guillemotleft>?L a : ?l (A.dom a) \<rightarrow>\<^sub>B ?l (A.cod a)\<guillemotright>"
          using L_arr by blast
        have L_map: "\<And>a. A.arr a \<Longrightarrow> uncurry_D.P ?l ?\<chi> a (uncurry_D.L ?l ?\<chi> a)"
          using L_arr by blast
        text\<open>
          The functor \<open>L\<close> extends to a functor \<open>L'\<close> from \<open>JxA\<close>
          to \<open>B\<close> that is constant on \<open>J\<close>.
\<close>
        let ?L' = "\<lambda>ja. if JxA.arr ja then ?L (snd ja) else B.null"
        let ?P' = "\<lambda>ja. ?P (snd ja)"
        interpret L': "functor" JxA.comp B ?L'
          apply unfold_locales
          using L.preserves_arr L.preserves_dom L.preserves_cod
              apply auto[4]
          using L.preserves_comp JxA.comp_char by (elim JxA.seqE, auto)
        have "\<And>ja. JxA.arr ja \<Longrightarrow> (\<exists>!f. ?P' ja f) \<and> ?P' ja (?L' ja)"
        proof -
          fix ja
          assume ja: "JxA.arr ja"
          have "A.arr (snd ja)" using ja by blast
          thus "(\<exists>!f. ?P' ja f) \<and> ?P' ja (?L' ja)"
            using ja L_arr by presburger
        qed
        hence L'_arr: "\<And>ja. JxA.arr ja \<Longrightarrow> ?P' ja (?L' ja)" by blast
        have L'_arr_in_hom:
             "\<And>ja. JxA.arr ja \<Longrightarrow> \<guillemotleft>?L' ja : ?l (A.dom (snd ja)) \<rightarrow>\<^sub>B ?l (A.cod (snd ja))\<guillemotright>"
          using L'_arr by simp
        have L'_ide: "\<And>ja. \<lbrakk> J.arr (fst ja); A.ide (snd ja) \<rbrakk> \<Longrightarrow> ?L' ja = ?l (snd ja)"
          using L_ide l\<chi> by force
        have L'_arr_map:
             "\<And>ja. JxA.arr ja \<Longrightarrow> uncurry_D.P ?l ?\<chi> (snd ja) (uncurry_D.L ?l ?\<chi> (snd ja))"
           using L'_arr by presburger
        text\<open>
          The map that takes an object \<open>(j, a)\<close> of \<open>JxA\<close> to the component
          \<open>\<chi> a j\<close> of the limit cone \<open>\<chi> a\<close> is a natural transformation
          from \<open>L\<close> to uncurry \<open>D\<close>.
\<close>
        let ?\<chi>' = "\<lambda>ja. ?\<chi> (snd ja) (fst ja)"
        interpret \<chi>': transformation_by_components JxA.comp B ?L' \<open>Curry.uncurry D\<close> ?\<chi>'
        proof
          fix ja
          assume ja: "JxA.ide ja"
          let ?j = "fst ja"
          let ?a = "snd ja"
          interpret \<chi>a: limit_cone J B \<open>D.at ?a D\<close> \<open>?l ?a\<close> \<open>?\<chi> ?a\<close>
            using ja l\<chi> by blast
          show "\<guillemotleft>?\<chi>' ja : ?L' ja \<rightarrow>\<^sub>B Curry.uncurry D ja\<guillemotright>"
            using ja L'_ide [of ja] by force
          next
          fix ja
          assume ja: "JxA.arr ja"
          let ?j = "fst ja"
          let ?a = "snd ja"
          have j: "J.arr ?j" using ja by simp
          have a: "A.arr ?a" using ja by simp
          interpret D_dom_a: diagram J B \<open>D.at (A.dom ?a) D\<close>
            using a D.at_ide_is_diagram by auto
          interpret D_cod_a: diagram J B \<open>D.at (A.cod ?a) D\<close>
            using a D.at_ide_is_diagram by auto
          interpret Da: natural_transformation J B \<open>D.at (A.dom ?a) D\<close> \<open>D.at (A.cod ?a) D\<close>
                                                   \<open>D.at ?a D\<close>
            using a D.functor_axioms D.functor_at_arr_is_transformation by simp
          interpret \<chi>_dom_a: limit_cone J B \<open>D.at (A.dom ?a) D\<close> \<open>?l (A.dom ?a)\<close> \<open>?\<chi> (A.dom ?a)\<close>
            using a l\<chi> by simp
          interpret \<chi>_cod_a: limit_cone J B \<open>D.at (A.cod ?a) D\<close> \<open>?l (A.cod ?a)\<close> \<open>?\<chi> (A.cod ?a)\<close>
            using a l\<chi> by simp
          interpret Dao\<chi>_dom_a: vertical_composite J B
                                  \<chi>_dom_a.A.map \<open>D.at (A.dom ?a) D\<close> \<open>D.at (A.cod ?a) D\<close>
                                  \<open>?\<chi> (A.dom ?a)\<close> \<open>D.at ?a D\<close> ..
          interpret Dao\<chi>_dom_a: cone J B \<open>D.at (A.cod ?a) D\<close> \<open>?l (A.dom ?a)\<close> Dao\<chi>_dom_a.map ..
          show "?\<chi>' (JxA.cod ja) \<cdot>\<^sub>B ?L' ja = B (Curry.uncurry D ja) (?\<chi>' (JxA.dom ja))"
          proof -
            have "?\<chi>' (JxA.cod ja) \<cdot>\<^sub>B ?L' ja = ?\<chi> (A.cod ?a) (J.cod ?j) \<cdot>\<^sub>B ?L' ja"
              using ja by fastforce
            also have "... = D_cod_a.cones_map (?L' ja) (?\<chi> (A.cod ?a)) (J.cod ?j)"
              using ja L'_arr_map [of ja] \<chi>_cod_a.cone_axioms by auto
            also have "... = Dao\<chi>_dom_a.map (J.cod ?j)"
              using ja \<chi>_cod_a.induced_arrowI Dao\<chi>_dom_a.cone_axioms L'_arr by presburger
            also have "... = D.at ?a D (J.cod ?j) \<cdot>\<^sub>B D_dom_a.some_limit_cone (J.cod ?j)"
              using ja Dao\<chi>_dom_a.map_simp_ide by fastforce
            also have "... = D.at ?a D (J.cod ?j) \<cdot>\<^sub>B D.at (A.dom ?a) D ?j \<cdot>\<^sub>B ?\<chi>' (JxA.dom ja)"
              using ja \<chi>_dom_a.naturality \<chi>_dom_a.ide_apex apply simp
              by (metis B.comp_arr_ide \<chi>_dom_a.preserves_reflects_arr)
            also have "... = (D.at ?a D (J.cod ?j) \<cdot>\<^sub>B D.at (A.dom ?a) D ?j) \<cdot>\<^sub>B ?\<chi>' (JxA.dom ja)"
            proof -
              have "B.seq (D.at ?a D (J.cod ?j)) (D.at (A.dom ?a) D ?j)"
                using j ja by auto
              moreover have "B.seq (D.at (A.dom ?a) D ?j) (?\<chi>' (JxA.dom ja))"
                using j ja by fastforce
              ultimately show ?thesis using B.comp_assoc by force
            qed
            also have "... = B (D.at ?a D ?j) (?\<chi>' (JxA.dom ja))"
            proof -
              have "D.at ?a D (J.cod ?j) \<cdot>\<^sub>B D.at (A.dom ?a) D ?j =
                      Map (D (J.cod ?j)) ?a \<cdot>\<^sub>B Map (D ?j) (A.dom ?a)"
                using ja D.at_simp by auto
              also have "... = Map (comp (D (J.cod ?j)) (D ?j)) (?a \<cdot>\<^sub>A A.dom ?a)"
                using ja Map_comp D.preserves_hom
                by (metis (mono_tags, lifting) A.comp_arr_dom D.natural_transformation_axioms
                    D.preserves_arr a j natural_transformation.is_natural_2)
              also have "... = D.at ?a D ?j"
                using ja D.at_simp dom_char A.comp_arr_dom by force
              finally show ?thesis by auto
           qed
           also have "... = Curry.uncurry D ja \<cdot>\<^sub>B ?\<chi>' (JxA.dom ja)"
             using Curry.uncurry_def by simp
           finally show ?thesis by auto
         qed
       qed
       text\<open>
         Since \<open>\<chi>'\<close> is constant on \<open>J\<close>, \<open>curry \<chi>'\<close> is a cone over \<open>D\<close>.
\<close>
       interpret constL: constant_functor J comp \<open>MkIde ?L\<close>
       proof
         show "ide (MkIde ?L)"
           using L.natural_transformation_axioms MkArr_in_hom ide_in_hom L.functor_axioms
           by blast
       qed
       (* TODO: This seems a little too involved. *)
       have curry_L': "constL.map = Curry.curry ?L' ?L' ?L'"
       proof
         fix j
         have "\<not>J.arr j \<Longrightarrow> constL.map j = Curry.curry ?L' ?L' ?L' j"
           using Curry.curry_def constL.is_extensional by simp
         moreover have "J.arr j \<Longrightarrow> constL.map j = Curry.curry ?L' ?L' ?L' j"
         proof -
           assume j: "J.arr j"
           show "constL.map j = Curry.curry ?L' ?L' ?L' j"
           proof -
             have "constL.map j = MkIde ?L" using j constL.map_simp by simp
             moreover have "... = MkArr ?L ?L ?L" by simp
             moreover have "... = MkArr (\<lambda>a. ?L' (J.dom j, a)) (\<lambda>a. ?L' (J.cod j, a))
                                        (\<lambda>a. ?L' (j, a))"
               using j constL.value_is_ide in_homE ide_in_hom by (intro MkArr_eqI, auto)
             moreover have "... = Curry.curry ?L' ?L' ?L' j"
               using j Curry.curry_def by auto
             ultimately show ?thesis by force
           qed
         qed
         ultimately show "constL.map j = Curry.curry ?L' ?L' ?L' j" by blast
       qed
       hence uncurry_constL: "Curry.uncurry constL.map = ?L'"
         using L'.natural_transformation_axioms Curry.uncurry_curry by simp
       interpret curry_\<chi>': natural_transformation J comp constL.map D
                             \<open>Curry.curry ?L' (Curry.uncurry D) \<chi>'.map\<close>
       proof -
         have 1: "Curry.curry (Curry.uncurry D) (Curry.uncurry D) (Curry.uncurry D) = D"
           using Curry.curry_uncurry D.functor_axioms D.natural_transformation_axioms
           by blast
         thus "natural_transformation J comp constL.map D
                 (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map)"
           using Curry.curry_preserves_transformations curry_L' \<chi>'.natural_transformation_axioms
           by force
       qed
       interpret curry_\<chi>': cone J comp D \<open>MkIde ?L\<close> \<open>Curry.curry ?L' (Curry.uncurry D) \<chi>'.map\<close> ..
       text\<open>
         The value of \<open>curry_\<chi>'\<close> at each object \<open>a\<close> of \<open>A\<close> is the
         limit cone \<open>\<chi> a\<close>, hence \<open>curry_\<chi>'\<close> is a limit cone.
\<close>
       have 1: "\<And>a. A.ide a \<Longrightarrow> D.at a (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map) = ?\<chi> a"
       proof -
         fix a
         assume a: "A.ide a"
         have "D.at a (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map) =
                 (\<lambda>j. Curry.uncurry (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map) (j, a))"
           using a by simp
         moreover have "... = (\<lambda>j. \<chi>'.map (j, a))"
           using a Curry.uncurry_curry \<chi>'.natural_transformation_axioms by simp
         moreover have "... = ?\<chi> a"
         proof (intro NaturalTransformation.eqI)
           interpret \<chi>a: limit_cone J B \<open>D.at a D\<close> \<open>?l a\<close> \<open>?\<chi> a\<close> using a l\<chi> by simp
           interpret \<chi>': binary_functor_transformation J A B ?L' \<open>Curry.uncurry D\<close> \<chi>'.map ..
           show "natural_transformation J B \<chi>a.A.map (D.at a D) (?\<chi> a)" ..
           show "natural_transformation J B \<chi>a.A.map (D.at a D) (\<lambda>j. \<chi>'.map (j, a))"
           proof -
             have "\<chi>a.A.map = (\<lambda>j. ?L' (j, a))"
               using a \<chi>a.A.map_def L'_ide by auto
             thus ?thesis
               using a \<chi>'.fixing_ide_gives_natural_transformation_2 by simp
           qed
           fix j
           assume j: "J.ide j"
           show "\<chi>'.map (j, a) = ?\<chi> a j"
             using a j \<chi>'.map_simp_ide by simp
         qed
         ultimately show "D.at a (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map) = ?\<chi> a" by simp
       qed
       hence 2: "\<And>a. A.ide a \<Longrightarrow> diagram.limit_cone J B (D.at a D) (?l a)
                                (D.at a (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map))"
         using l\<chi> by simp
       hence "limit_cone J comp D (MkIde ?L) (Curry.curry ?L' (Curry.uncurry D) \<chi>'.map)"
       proof -
         have "\<And>a. A.ide a \<Longrightarrow> Map (MkIde ?L) a = ?l a"
           using L.functor_axioms L_ide by simp
         thus ?thesis
           using 1 2 curry_\<chi>'.cone_axioms curry_L' D.cone_is_limit_if_pointwise_limit by simp
       qed
       thus "\<exists>x \<chi>. limit_cone J comp D x \<chi>" by blast
     qed
     thus "\<forall>D. diagram J comp D \<longrightarrow> (\<exists>x \<chi>. limit_cone J comp D x \<chi>)" by blast
    qed

    lemma has_limits_if_target_does:
    assumes "B.has_limits (undefined :: 'j)"
    shows "has_limits (undefined :: 'j)"
      using assms B.has_limits_def has_limits_def has_limits_of_shape_if_target_does by fast

  end

  section "The Yoneda Functor Preserves Limits"

  text\<open>
    In this section, we show that the Yoneda functor from \<open>C\<close> to \<open>[Cop, S]\<close>
    preserves limits.
\<close>

  context yoneda_functor
  begin

    lemma preserves_limits:
    fixes J :: "'j comp"
    assumes "diagram J C D" and "diagram.has_as_limit J C D a"
    shows "diagram.has_as_limit J Cop_S.comp (map o D) (map a)"
    proof -
      text\<open>
        The basic idea of the proof is as follows:
        If \<open>\<chi>\<close> is a limit cone in \<open>C\<close>, then for every object \<open>a'\<close>
        of \<open>Cop\<close> the evaluation of \<open>Y o \<chi>\<close> at \<open>a'\<close> is a limit cone
        in \<open>S\<close>.  By the results on limits in functor categories,
        this implies that \<open>Y o \<chi>\<close> is a limit cone in \<open>[Cop, S]\<close>.
\<close>
      interpret J: category J using assms(1) diagram_def by auto
      interpret D: diagram J C D using assms(1) by auto
      from assms(2) obtain \<chi> where \<chi>: "D.limit_cone a \<chi>" by blast
      interpret \<chi>: limit_cone J C D a \<chi> using \<chi> by auto
      have a: "C.ide a" using \<chi>.ide_apex by auto
      interpret YoD: diagram J Cop_S.comp \<open>map o D\<close>
        using D.diagram_axioms functor_axioms preserves_diagrams [of J D] by simp
      interpret YoD: diagram_in_functor_category Cop.comp S J \<open>map o D\<close> ..
      interpret Yo\<chi>: cone J Cop_S.comp \<open>map o D\<close> \<open>map a\<close> \<open>map o \<chi>\<close>
        using \<chi>.cone_axioms preserves_cones by blast
      have "\<And>a'. C.ide a' \<Longrightarrow>
                   limit_cone J S (YoD.at a' (map o D))
                                  (Cop_S.Map (map a) a') (YoD.at a' (map o \<chi>))"
      proof -
        fix a'
        assume a': "C.ide a'"
        interpret A': constant_functor J C a'
          using a' by (unfold_locales, auto)
        interpret YoD_a': diagram J S \<open>YoD.at a' (map o D)\<close>
          using a' YoD.at_ide_is_diagram by simp
        interpret Yo\<chi>_a': cone J S \<open>YoD.at a' (map o D)\<close>
                                   \<open>Cop_S.Map (map a) a'\<close> \<open>YoD.at a' (map o \<chi>)\<close>
          using a' YoD.cone_at_ide_is_cone Yo\<chi>.cone_axioms by fastforce
        have eval_at_ide: "\<And>j. J.ide j \<Longrightarrow> YoD.at a' (map \<circ> D) j = Hom.map (a', D j)"
        proof -
          fix j
          assume j: "J.ide j"
          have "YoD.at a' (map \<circ> D) j = Cop_S.Map (map (D j)) a'"
            using a' j YoD.at_simp YoD.preserves_arr [of j] by auto
          also have "... = Y (D j) a'" using Y_def by simp
          also have "... = Hom.map (a', D j)" using a' j D.preserves_arr by simp
          finally show "YoD.at a' (map \<circ> D) j = Hom.map (a', D j)" by auto
        qed
        have eval_at_arr: "\<And>j. J.arr j \<Longrightarrow> YoD.at a' (map \<circ> \<chi>) j = Hom.map (a', \<chi> j)"
        proof -
          fix j
          assume j: "J.arr j"
          have "YoD.at a' (map \<circ> \<chi>) j = Cop_S.Map ((map o \<chi>) j) a'"
            using a' j YoD.at_simp [of a' j "map o \<chi>"] preserves_arr by fastforce
          also have "... = Y (\<chi> j) a'" using Y_def by simp
            also have "... = Hom.map (a', \<chi> j)" using a' j by simp
          finally show "YoD.at a' (map \<circ> \<chi>) j = Hom.map (a', \<chi> j)" by auto
        qed
        have Fun_map_a_a': "Cop_S.Map (map a) a' = Hom.map (a', a)"
          using a a' map_simp preserves_arr [of a] by simp
        show "limit_cone J S (YoD.at a' (map o D))
                             (Cop_S.Map (map a) a') (YoD.at a' (map o \<chi>))"
        proof
          fix x \<sigma>
          assume \<sigma>: "YoD_a'.cone x \<sigma>"
          interpret \<sigma>: cone J S \<open>YoD.at a' (map o D)\<close> x \<sigma> using \<sigma> by auto
          have x: "S.ide x" using \<sigma>.ide_apex by simp
          text\<open>
            For each object \<open>j\<close> of \<open>J\<close>, the component \<open>\<sigma> j\<close>
            is an arrow in \<open>S.hom x (Hom.map (a', D j))\<close>.
            Each element \<open>e \<in> S.set x\<close> therefore determines an arrow
            \<open>\<psi> (a', D j) (S.Fun (\<sigma> j) e) \<in> C.hom a' (D j)\<close>.
            These arrows are the components of a cone \<open>\<kappa> e\<close> over @{term D}
            with apex @{term a'}.
\<close>
          have \<sigma>j: "\<And>j. J.ide j \<Longrightarrow> \<guillemotleft>\<sigma> j : x \<rightarrow>\<^sub>S Hom.map (a', D j)\<guillemotright>"
            using eval_at_ide \<sigma>.preserves_hom J.ide_in_hom by force
          have \<kappa>: "\<And>e. e \<in> S.set x \<Longrightarrow>
                        transformation_by_components
                          J C A'.map D (\<lambda>j. \<psi> (a', D j) (S.Fun (\<sigma> j) e))"
          proof -
            fix e
            assume e: "e \<in> S.set x"
            show "transformation_by_components J C A'.map D (\<lambda>j. \<psi> (a', D j) (S.Fun (\<sigma> j) e))"
            proof
              fix j
              assume j: "J.ide j"
              show "\<guillemotleft>\<psi> (a', D j) (S.Fun (\<sigma> j) e) : A'.map j \<rightarrow> D j\<guillemotright>"
                using e j S.Fun_mapsto [of "\<sigma> j"] A'.preserves_ide Hom.set_map eval_at_ide
                      Hom.\<psi>_mapsto [of "A'.map j" "D j"]
                by force
              next
              fix j
              assume j: "J.arr j"
              show "\<psi> (a', D (J.cod j)) (S.Fun (\<sigma> (J.cod j)) e) \<cdot> A'.map j =
                    D j \<cdot> \<psi> (a', D (J.dom j)) (S.Fun (\<sigma> (J.dom j)) e)"
              proof -
                have 1: "Y (D j) a' = 
                          S.mkArr (Hom.set (a', D (J.dom j))) (Hom.set (a', D (J.cod j)))
                                  (\<phi> (a', D (J.cod j)) \<circ> C (D j) \<circ> \<psi> (a', D (J.dom j)))"
                  using j a' D.preserves_hom
                        Y_arr_ide [of a' "D j" "D (J.dom j)" "D (J.cod j)"]
                  by blast
                have "\<psi> (a', D (J.cod j)) (S.Fun (\<sigma> (J.cod j)) e) \<cdot> A'.map j =
                      \<psi> (a', D (J.cod j)) (S.Fun (\<sigma> (J.cod j)) e) \<cdot> a'"
                  using A'.map_simp j by simp
                also have "... = \<psi> (a', D (J.cod j)) (S.Fun (\<sigma> (J.cod j)) e)"
                proof -
                  have "\<psi> (a', D (J.cod j)) (S.Fun (\<sigma> (J.cod j)) e) \<in> C.hom a' (D (J.cod j))"
                    using a' e j Hom.\<psi>_mapsto [of "A'.map j" "D (J.cod j)"] A'.map_simp
                          S.Fun_mapsto [of "\<sigma> (J.cod j)"] Hom.set_map eval_at_ide
                    by auto
                  thus ?thesis
                    using C.comp_arr_dom by fastforce
                qed
                also have "... = \<psi> (a', D (J.cod j)) (S.Fun (Y (D j) a') (S.Fun (\<sigma> (J.dom j)) e))"
                proof -
                  have "S.Fun (Y (D j) a') (S.Fun (\<sigma> (J.dom j)) e) =
                        (S.Fun (Y (D j) a') o S.Fun (\<sigma> (J.dom j))) e"
                    by simp
                  also have "... = S.Fun (Y (D j) a' \<cdot>\<^sub>S \<sigma> (J.dom j)) e"
                    using a' e j Y_arr_ide(1) S.in_homE \<sigma>j eval_at_ide S.Fun_comp by force
                  also have "... = S.Fun (\<sigma> (J.cod j)) e"
                    using a' j x \<sigma>.is_natural_2 \<sigma>.A.map_simp S.comp_arr_dom J.arr_cod_iff_arr
                          J.cod_cod YoD.preserves_arr \<sigma>.is_natural_1 YoD.at_simp
                    by auto
                  finally have
                      "S.Fun (Y (D j) a') (S.Fun (\<sigma> (J.dom j)) e) = S.Fun (\<sigma> (J.cod j)) e"
                    by auto
                  thus ?thesis by simp
                qed
                also have "... = D j \<cdot> \<psi> (a', D (J.dom j)) (S.Fun (\<sigma> (J.dom j)) e)"
                proof -
                  have "e \<in> S.Dom (\<sigma> (J.dom j))"
                    using e j by simp
                  hence "S.Fun (\<sigma> (J.dom j)) e \<in> S.Cod (\<sigma> (J.dom j))"
                    using e j S.Fun_mapsto [of "\<sigma> (J.dom j)"] by auto
                  hence 2: "S.Fun (\<sigma> (J.dom j)) e \<in> Hom.set (a', D (J.dom j))"
                  proof -
                    have "YoD.at a' (map \<circ> D) (J.dom j) = S.mkIde (Hom.set (a', D (J.dom j)))"
                      using a' j YoD.at_simp by (simp add: eval_at_ide)
                    moreover have "S.Cod (\<sigma> (J.dom j)) = Hom.set (a', D (J.dom j))"
                      using a' e j Hom.set_map YoD.at_simp eval_at_ide by simp
                    ultimately show ?thesis
                      using a' e j \<sigma>j S.Fun_mapsto [of "\<sigma> (J.dom j)"] Hom.set_map
                      by auto
                  qed
                  hence "S.Fun (Y (D j) a') (S.Fun (\<sigma> (J.dom j)) e) =
                         \<phi> (a', D (J.cod j)) (D j \<cdot> \<psi> (a', D (J.dom j)) (S.Fun (\<sigma> (J.dom j)) e))"
                  proof -
                    have "S.Fun (\<sigma> (J.dom j)) e \<in> Hom.set (a', D (J.dom j))"
                      using a' e j \<sigma>j S.Fun_mapsto [of "\<sigma> (J.dom j)"] Hom.set_map
                      by (auto simp add: eval_at_ide)
                    hence "C.arr (\<psi> (a', D (J.dom j)) (S.Fun (\<sigma> (J.dom j)) e)) \<and>
                           C.dom (\<psi> (a', D (J.dom j)) (S.Fun (\<sigma> (J.dom j)) e)) = a'"
                      using a' j Hom.\<psi>_mapsto [of a' "D (J.dom j)"] by auto
                    thus ?thesis
                      using a' e j 2 Hom.Fun_map C.comp_arr_dom by force
                  qed
                  moreover have "D j \<cdot> \<psi> (a', D (J.dom j)) (S.Fun (\<sigma> (J.dom j)) e)
                                   \<in> C.hom a' (D (J.cod j))"
                  proof -
                    have "\<psi> (a', D (J.dom j)) (S.Fun (\<sigma> (J.dom j)) e) \<in> C.hom a' (D (J.dom j))"
                      using a' e j Hom.\<psi>_mapsto [of a' "D (J.dom j)"] eval_at_ide
                            S.Fun_mapsto [of "\<sigma> (J.dom j)"] Hom.set_map
                      by auto
                    thus ?thesis using j D.preserves_hom by blast
                  qed
                  ultimately show ?thesis using a' j Hom.\<psi>_\<phi> by simp
                qed
                finally show ?thesis by auto
              qed
            qed
          qed
          let ?\<kappa> = "\<lambda>e. transformation_by_components.map J C A'.map
                          (\<lambda>j. \<psi> (a', D j) (S.Fun (\<sigma> j) e))"
          have cone_\<kappa>e: "\<And>e. e \<in> S.set x \<Longrightarrow> D.cone a' (?\<kappa> e)"
          proof -
            fix e
            assume e: "e \<in> S.set x"
            interpret \<kappa>e: transformation_by_components J C A'.map D
                            \<open>\<lambda>j. \<psi> (a', D j) (S.Fun (\<sigma> j) e)\<close>
              using e \<kappa> by blast
            show "D.cone a' (?\<kappa> e)" ..
          qed
          text\<open>
            Since \<open>\<kappa> e\<close> is a cone for each element \<open>e\<close> of \<open>S.set x\<close>,
            by the universal property of the limit cone \<open>\<chi>\<close> there is a unique arrow
            \<open>fe \<in> C.hom a' a\<close> that transforms \<open>\<chi>\<close> to \<open>\<kappa> e\<close>.
\<close>
          have ex_fe: "\<And>e. e \<in> S.set x \<Longrightarrow> \<exists>!fe. \<guillemotleft>fe : a' \<rightarrow> a\<guillemotright> \<and> D.cones_map fe \<chi> = ?\<kappa> e"
            using cone_\<kappa>e \<chi>.is_universal by simp
          text\<open>
            The map taking \<open>e \<in> S.set x\<close> to \<open>fe \<in> C.hom a' a\<close>
            determines an arrow \<open>f \<in> S.hom x (Hom (a', a))\<close> that
            transforms the cone obtained by evaluating \<open>Y o \<chi>\<close> at \<open>a'\<close>
            to the cone \<open>\<sigma>\<close>.
\<close>
          let ?f = "S.mkArr (S.set x) (Hom.set (a', a))
                            (\<lambda>e. \<phi> (a', a) (\<chi>.induced_arrow a' (?\<kappa> e)))"
          have 0: "(\<lambda>e. \<phi> (a', a) (\<chi>.induced_arrow a' (?\<kappa> e))) \<in> S.set x \<rightarrow> Hom.set (a', a)"
          proof
            fix e
            assume e: "e \<in> S.set x"
            interpret \<kappa>e: cone J C D a' \<open>?\<kappa> e\<close> using e cone_\<kappa>e by simp
            have "\<chi>.induced_arrow a' (?\<kappa> e) \<in> C.hom a' a"
              using a a' e ex_fe \<chi>.induced_arrowI \<kappa>e.cone_axioms by simp
            thus "\<phi> (a', a) (\<chi>.induced_arrow a' (?\<kappa> e)) \<in> Hom.set (a', a)"
              using a a' Hom.\<phi>_mapsto by auto
          qed
          hence f: "\<guillemotleft>?f : x \<rightarrow>\<^sub>S Hom.map (a', a)\<guillemotright>"
            using a a' x \<sigma>.ide_apex S.mkArr_in_hom [of "S.set x" "Hom.set (a', a)"]
                  Hom.set_subset_Univ
            by simp
          have "YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)) = \<sigma>"
          proof (intro NaturalTransformation.eqI)
            show "natural_transformation J S \<sigma>.A.map (YoD.at a' (map o D)) \<sigma>"
              using \<sigma>.natural_transformation_axioms by auto
            have 1: "S.cod ?f = Cop_S.Map (map a) a'"
              using f Fun_map_a_a' by force
            interpret YoD_a'of: cone J S \<open>YoD.at a' (map o D)\<close> x
                                     \<open>YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>))\<close>
            proof -
              have "YoD_a'.cone (S.cod ?f) (YoD.at a' (map o \<chi>))"
                using a a' f Yo\<chi>_a'.cone_axioms preserves_arr [of a] by auto
              hence "YoD_a'.cone (S.dom ?f) (YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)))"
                using f YoD_a'.cones_map_mapsto S.arrI by blast
              thus "cone J S (YoD.at a' (map o D)) x
                                        (YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)))"
                using f by auto
            qed
            show "natural_transformation J S \<sigma>.A.map (YoD.at a' (map o D))
                                         (YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)))" ..
            fix j
            assume j: "J.ide j"
            have "YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)) j = YoD.at a' (map o \<chi>) j \<cdot>\<^sub>S ?f"
              using f j Fun_map_a_a' Yo\<chi>_a'.cone_axioms by fastforce
            also have "... = \<sigma> j"
            proof (intro S.arr_eqI)
              show "S.par (YoD.at a' (map o \<chi>) j \<cdot>\<^sub>S ?f) (\<sigma> j)"
                using 1 f j x YoD_a'.preserves_hom by fastforce
              show "S.Fun (YoD.at a' (map o \<chi>) j \<cdot>\<^sub>S ?f) = S.Fun (\<sigma> j)"
              proof
                fix e
                have "e \<notin> S.set x \<Longrightarrow> S.Fun (YoD.at a' (map o \<chi>) j \<cdot>\<^sub>S ?f) e = S.Fun (\<sigma> j) e"
                proof -
                  assume e: "e \<notin> S.set x"
                  have "S.Fun (YoD.at a' (map o \<chi>) j \<cdot>\<^sub>S ?f) e = undefined"
                    using 1 e f j x S.Fun_mapsto by fastforce
                  also have "... = S.Fun (\<sigma> j) e"
                  proof -
                    have "\<guillemotleft>\<sigma> j : x \<rightarrow>\<^sub>S YoD.at a' (map \<circ> D) (J.cod j)\<guillemotright>"
                      using j \<sigma>.A.map_simp by force
                    thus ?thesis
                      using e j S.Fun_mapsto [of "\<sigma> j"] extensional_arb [of "S.Fun (\<sigma> j)"]
                      by fastforce
                  qed
                  finally show ?thesis by auto
                qed
                moreover have "e \<in> S.set x \<Longrightarrow>
                                  S.Fun (YoD.at a' (map o \<chi>) j \<cdot>\<^sub>S ?f) e = S.Fun (\<sigma> j) e"
                proof -
                  assume e: "e \<in> S.set x"
                  interpret \<kappa>e: transformation_by_components J C A'.map D
                                  \<open>\<lambda>j. \<psi> (a', D j) (S.Fun (\<sigma> j) e)\<close>
                    using e \<kappa> by blast
                  interpret \<kappa>e: cone J C D a' \<open>?\<kappa> e\<close> using e cone_\<kappa>e by simp
                  have induced_arrow: "\<chi>.induced_arrow a' (?\<kappa> e) \<in> C.hom a' a"
                    using a a' e ex_fe \<chi>.induced_arrowI \<kappa>e.cone_axioms by simp
                  have "S.Fun (YoD.at a' (map o \<chi>) j \<cdot>\<^sub>S ?f) e =
                          restrict (S.Fun (YoD.at a' (map o \<chi>) j) o S.Fun ?f) (S.set x) e"
                    using 1 e f j S.Fun_comp YoD_a'.preserves_hom by force
                  also have "... = (\<phi> (a', D j) o C (\<chi> j) o \<psi> (a', a)) (S.Fun ?f e)"
                    using j a' f e Hom.map_simp_2 S.Fun_mkArr Hom.preserves_arr [of "(a', \<chi> j)"]
                          eval_at_arr
                    by (elim S.in_homE, auto)
                  also have "... = (\<phi> (a', D j) o C (\<chi> j) o \<psi> (a', a))
                                     (\<phi> (a', a) (\<chi>.induced_arrow a' (?\<kappa> e)))"
                    using e f S.Fun_mkArr by fastforce
                  also have "... = \<phi> (a', D j) (D.cones_map (\<chi>.induced_arrow a' (?\<kappa> e)) \<chi> j)"
                      using a a' e j 0 Hom.\<psi>_\<phi> induced_arrow \<chi>.cone_axioms
                      by auto
                  also have "... = \<phi> (a', D j) (?\<kappa> e j)"
                    using \<chi>.induced_arrowI \<kappa>e.cone_axioms by fastforce
                  also have "... = \<phi> (a', D j) (\<psi> (a', D j) (S.Fun (\<sigma> j) e))"
                    using j \<kappa>e.map_def [of j] by simp
                  also have "... = S.Fun (\<sigma> j) e"
                  proof -
                    have "S.Fun (\<sigma> j) e \<in> Hom.set (a', D j)"
                      using a' e j S.Fun_mapsto [of "\<sigma> j"] eval_at_ide Hom.set_map by auto
                    thus ?thesis
                      using a' j Hom.\<phi>_\<psi> C.ide_in_hom J.ide_in_hom by blast
                  qed
                  finally show "S.Fun (YoD.at a' (map o \<chi>) j \<cdot>\<^sub>S ?f) e = S.Fun (\<sigma> j) e"
                    by auto
                qed
                ultimately show "S.Fun (YoD.at a' (map o \<chi>) j \<cdot>\<^sub>S ?f) e = S.Fun (\<sigma> j) e"
                  by auto
              qed
            qed
            finally show "YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)) j = \<sigma> j" by auto
          qed
          hence ff: "?f \<in> S.hom x (Hom.map (a', a)) \<and>
                     YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)) = \<sigma>"
            using f by auto
          text\<open>
            Any other arrow \<open>f' \<in> S.hom x (Hom.map (a', a))\<close> that
            transforms the cone obtained by evaluating \<open>Y o \<chi>\<close> at @{term a'}
            to the cone @{term \<sigma>}, must equal \<open>f\<close>, showing that \<open>f\<close>
            is unique.
\<close>
          moreover have "\<And>f'. \<guillemotleft>f' : x \<rightarrow>\<^sub>S Hom.map (a', a)\<guillemotright> \<and>
                              YoD_a'.cones_map f' (YoD.at a' (map o \<chi>)) = \<sigma>
                                \<Longrightarrow> f' = ?f"
          proof -
            fix f'
            assume f': "\<guillemotleft>f' : x \<rightarrow>\<^sub>S Hom.map (a', a)\<guillemotright> \<and>
                        YoD_a'.cones_map f' (YoD.at a' (map o \<chi>)) = \<sigma>"
            show "f' = ?f"
            proof (intro S.arr_eqI)
              show par: "S.par f' ?f" using f f' by (elim S.in_homE, auto)
              show "S.Fun f' = S.Fun ?f"
              proof
                fix e
                have "e \<notin> S.set x \<Longrightarrow> S.Fun f' e = S.Fun ?f e"
                  using f f' x S.Fun_mapsto extensional_arb by fastforce
                moreover have "e \<in> S.set x \<Longrightarrow> S.Fun f' e = S.Fun ?f e"
                proof -
                  assume e: "e \<in> S.set x"
                  have 1: "\<guillemotleft>\<psi> (a', a) (S.Fun f' e) : a' \<rightarrow> a\<guillemotright>"
                  proof -
                    have "S.Fun f' e \<in> S.Cod f'"
                      using a a' e f' S.Fun_mapsto by auto
                    hence "S.Fun f' e \<in> Hom.set (a', a)"
                      using a a' f' Hom.set_map by auto
                    thus ?thesis
                      using a a' e f' S.Fun_mapsto Hom.\<psi>_mapsto Hom.set_map by blast
                  qed
                  have 2: "\<guillemotleft>\<psi> (a', a) (S.Fun ?f e) : a' \<rightarrow> a\<guillemotright>"
                  proof -
                    have "S.Fun ?f e \<in> S.Cod ?f"
                      using a a' e f S.Fun_mapsto by force
                    hence "S.Fun ?f e \<in> Hom.set (a', a)"
                      using a a' f Hom.set_map by auto
                    thus ?thesis
                      using a a' e f' S.Fun_mapsto Hom.\<psi>_mapsto Hom.set_map by blast
                  qed
                  interpret \<chi>ofe: cone J C D a' \<open>D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi>\<close>
                  proof -
                    have "D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<in> D.cones a \<rightarrow> D.cones a'"
                      using 2 D.cones_map_mapsto [of "\<psi> (a', a) (S.Fun ?f e)"]
                      by (elim C.in_homE, auto)
                    thus "cone J C D a' (D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi>)"
                      using \<chi>.cone_axioms by blast
                  qed
                  have f'e: "S.Fun f' e \<in> Hom.set (a', a)"
                    using a a' e f' x S.Fun_mapsto [of f'] Hom.set_map by fastforce
                  have fe: "S.Fun ?f e \<in> Hom.set (a', a)"
                    using e f by (elim S.in_homE, auto)
                  have A: "\<And>h j. h \<in> C.hom a' a \<Longrightarrow> J.arr j \<Longrightarrow>
                                   S.Fun (YoD.at a' (map o \<chi>) j) (\<phi> (a', a) h)
                                     = \<phi> (a', D (J.cod j)) (\<chi> j \<cdot> h)"
                  proof -
                    fix h j
                    assume j: "J.arr j"
                    assume h: "h \<in> C.hom a' a"
                    have "S.Fun (YoD.at a' (map o \<chi>) j) = S.Fun (Y (\<chi> j) a')"
                      using a' j YoD.at_simp Y_def Yo\<chi>.preserves_reflects_arr [of j]
                      by simp
                    also have "... = restrict (\<phi> (a', D (J.cod j)) \<circ> C (\<chi> j) \<circ> \<psi> (a', a))
                                              (Hom.set (a', a))"
                    proof -
                      have "S.arr (Y (\<chi> j) a') \<and>
                            Y (\<chi> j) a' = S.mkArr (Hom.set (a', a)) (Hom.set (a', D (J.cod j)))
                                                 (\<phi> (a', D (J.cod j)) \<circ> C (\<chi> j) \<circ> \<psi> (a', a))"
                        using a' j \<chi>.preserves_hom [of j "J.dom j" "J.cod j"]
                              Y_arr_ide [of a' "\<chi> j" a "D (J.cod j)"] \<chi>.A.map_simp
                        by auto
                      thus ?thesis
                        using S.Fun_mkArr by metis
                    qed
                    finally have "S.Fun (YoD.at a' (map o \<chi>) j)
                                    = restrict (\<phi> (a', D (J.cod j)) \<circ> C (\<chi> j) \<circ> \<psi> (a', a))
                                               (Hom.set (a', a))"
                      by auto
                    hence "S.Fun (YoD.at a' (map o \<chi>) j) (\<phi> (a', a) h)
                              = (\<phi> (a', D (J.cod j)) \<circ> C (\<chi> j) \<circ> \<psi> (a', a)) (\<phi> (a', a) h)"
                      using a a' h Hom.\<phi>_mapsto by auto
                    also have "... = \<phi> (a', D (J.cod j)) (\<chi> j \<cdot> h)"
                      using a a' h Hom.\<psi>_\<phi> by simp
                    finally show "S.Fun (YoD.at a' (map o \<chi>) j) (\<phi> (a', a) h)
                                    = \<phi> (a', D (J.cod j)) (\<chi> j \<cdot> h)"
                      by auto
                  qed
                  have "D.cones_map (\<psi> (a', a) (S.Fun f' e)) \<chi> =
                        D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi>"
                  proof
                    fix j
                    have "\<not>J.arr j \<Longrightarrow> D.cones_map (\<psi> (a', a) (S.Fun f' e)) \<chi> j =
                                       D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi> j"
                      using 1 2 \<chi>.cone_axioms by (elim C.in_homE, auto)
                    moreover have "J.arr j \<Longrightarrow> D.cones_map (\<psi> (a', a) (S.Fun f' e)) \<chi> j =
                                               D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi> j"
                    proof -
                      assume j: "J.arr j"
                      have 3: "S.Fun (YoD.at a' (map o \<chi>) j) (S.Fun f' e) = S.Fun (\<sigma> j) e"
                        using Fun_map_a_a' a a' j f' e x Yo\<chi>_a'.A.map_simp eval_at_ide
                              Yo\<chi>_a'.cone_axioms
                        by auto
                      have 4: "S.Fun (YoD.at a' (map o \<chi>) j) (S.Fun ?f e) = S.Fun (\<sigma> j) e"
                      proof -
                        have "S.Fun (YoD.at a' (map o \<chi>) j) (S.Fun ?f e)
                                = (S.Fun (YoD.at a' (map o \<chi>) j) o S.Fun ?f) e"
                          by simp
                        also have "... = S.Fun (YoD.at a' (map o \<chi>) j \<cdot>\<^sub>S ?f) e"
                          using Fun_map_a_a' a a' j f e x Yo\<chi>_a'.A.map_simp eval_at_ide
                          by auto
                        also have "... = S.Fun (\<sigma> j) e"
                        proof -
                          have "YoD.at a' (map o \<chi>) j \<cdot>\<^sub>S ?f =
                                YoD_a'.cones_map ?f (YoD.at a' (map o \<chi>)) j"
                            using j f Yo\<chi>_a'.cone_axioms Fun_map_a_a' by auto
                          thus ?thesis using j ff by argo
                        qed
                        finally show ?thesis by auto
                      qed
                      have "D.cones_map (\<psi> (a', a) (S.Fun f' e)) \<chi> j =
                              \<chi> j \<cdot> \<psi> (a', a) (S.Fun f' e)"
                        using j 1 \<chi>.cone_axioms by auto
                      also have "... = \<psi> (a', D (J.cod j)) (S.Fun (\<sigma> j) e)"
                      proof -
                        have "\<psi> (a', D (J.cod j)) (S.Fun (YoD.at a' (map o \<chi>) j) (S.Fun f' e)) =
                                \<psi> (a', D (J.cod j))
                                  (\<phi> (a', D (J.cod j)) (\<chi> j \<cdot> \<psi> (a', a) (S.Fun f' e)))"
                          using j a a' f'e A Hom.\<phi>_\<psi> Hom.\<psi>_mapsto by force
                        moreover have "\<chi> j \<cdot> \<psi> (a', a) (S.Fun f' e) \<in> C.hom a' (D (J.cod j))"
                          using a a' j f'e Hom.\<psi>_mapsto \<chi>.preserves_hom [of j "J.dom j" "J.cod j"]
                                \<chi>.A.map_simp
                          by auto
                        ultimately show ?thesis
                          using a a' 3 4 Hom.\<psi>_\<phi> by auto
                      qed
                      also have "... = \<chi> j \<cdot> \<psi> (a', a) (S.Fun ?f e)"
                      proof -
                        have "S.Fun (YoD.at a' (map o \<chi>) j) (S.Fun ?f e) =
                                \<phi> (a', D (J.cod j)) (\<chi> j \<cdot> \<psi> (a', a) (S.Fun ?f e))"
                          using j a a' fe A [of "\<psi> (a', a) (S.Fun ?f e)" j] Hom.\<phi>_\<psi> Hom.\<psi>_mapsto
                          by auto
                        hence "\<psi> (a', D (J.cod j)) (S.Fun (YoD.at a' (map o \<chi>) j) (S.Fun ?f e)) =
                                \<psi> (a', D (J.cod j))
                                  (\<phi> (a', D (J.cod j)) (\<chi> j \<cdot> \<psi> (a', a) (S.Fun ?f e)))"
                          by simp
                        moreover have "\<chi> j \<cdot> \<psi> (a', a) (S.Fun ?f e) \<in> C.hom a' (D (J.cod j))"
                          using a a' j fe Hom.\<psi>_mapsto \<chi>.preserves_hom [of j "J.dom j" "J.cod j"]
                                \<chi>.A.map_simp
                          by auto
                        ultimately show ?thesis
                          using a a' 3 4 Hom.\<psi>_\<phi> by auto
                      qed
                      also have "... = D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi> j"
                        using j 2 \<chi>.cone_axioms by force
                      finally show "D.cones_map (\<psi> (a', a) (S.Fun f' e)) \<chi> j =
                                    D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi> j"
                        by auto
                    qed
                    ultimately show "D.cones_map (\<psi> (a', a) (S.Fun f' e)) \<chi> j =
                                     D.cones_map (\<psi> (a', a) (S.Fun ?f e)) \<chi> j"
                      by auto
                  qed
                  hence "\<psi> (a', a) (S.Fun f' e) = \<psi> (a', a) (S.Fun ?f e)"
                    using 1 2 \<chi>ofe.cone_axioms \<chi>.cone_axioms \<chi>.is_universal by blast
                  hence "\<phi> (a', a) (\<psi> (a', a) (S.Fun f' e)) = \<phi> (a', a) (\<psi> (a', a) (S.Fun ?f e))"
                    by simp
                  thus "S.Fun f' e = S.Fun ?f e"
                    using a a' fe f'e Hom.\<phi>_\<psi> by force
                qed
                ultimately show "S.Fun f' e = S.Fun ?f e" by auto
              qed
            qed
          qed
          ultimately have "\<exists>!f. \<guillemotleft>f : x \<rightarrow>\<^sub>S Hom.map (a', a)\<guillemotright> \<and>
                                YoD_a'.cones_map f (YoD.at a' (map o \<chi>)) = \<sigma>"
            using ex1I [of "\<lambda>f. S.in_hom x (Hom.map (a', a)) f \<and>
                                YoD_a'.cones_map f (YoD.at a' (map o \<chi>)) = \<sigma>"]
            by blast
          thus "\<exists>!f. \<guillemotleft>f : x \<rightarrow>\<^sub>S Cop_S.Map (map a) a'\<guillemotright> \<and>
                     YoD_a'.cones_map f (YoD.at a' (map o \<chi>)) = \<sigma>"
            using a a' Y_def [of a] by simp
        qed
      qed
      thus "YoD.has_as_limit (map a)"
        using YoD.cone_is_limit_if_pointwise_limit Yo\<chi>.cone_axioms by auto
    qed

  end

end
