(*  Title:       CategoryWithPullbacks
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Category with Pullbacks"

theory CategoryWithPullbacks
imports Category3.Limit
begin

text \<open>
  In this section, we give a traditional definition of pullbacks in a category as
  limits of cospan diagrams and we define a locale \<open>category_with_pullbacks\<close> that
  is satisfied by categories in which every cospan diagram has a limit.
  These definitions build on the general definition of limit that we gave in
  @{theory Category3.Limit}.  We then define a locale \<open>elementary_category_with_pullbacks\<close>
  that axiomatizes categories equipped with chosen functions that assign to each cospan
  a corresponding span of ``projections'', which enjoy the familiar universal property
  of a pullback.  After developing consequences of the axioms, we prove that the two
  locales are in agreement, in the sense that every interpretation of
  \<open>category_with_pullbacks\<close> extends to an interpretation of
  \<open>elementary_category_with_pullbacks\<close>, and conversely, the underlying category of
  an interpretation of \<open>elementary_category_with_pullbacks\<close> always yields an interpretation
  of \<open>category_with_pullbacks\<close>.
\<close>

  subsection "Commutative Squares"

  context category
  begin

    text \<open>
      The following provides some useful technology for working with commutative squares.
    \<close>
    
    definition commutative_square
    where "commutative_square f g h k \<equiv> cospan f g \<and> span h k \<and> dom f = cod h \<and> f \<cdot> h = g \<cdot> k"

    lemma commutative_squareI [intro, simp]:
    assumes "cospan f g" and "span h k" and "dom f = cod h" and "f \<cdot> h = g \<cdot> k"
    shows "commutative_square f g h k"
      using assms commutative_square_def by auto

    lemma commutative_squareE [elim]:
    assumes "commutative_square f g h k"
    and "\<lbrakk> arr f; arr g; arr h; arr k; cod f = cod g; dom h = dom k; dom f = cod h;
           dom g = cod k; f \<cdot> h = g \<cdot> k \<rbrakk> \<Longrightarrow> T"
    shows T
      using assms commutative_square_def
      by (metis (mono_tags, lifting) seqE seqI)

    lemma commutative_square_comp_arr:
    assumes "commutative_square f g h k" and "seq h l"
    shows "commutative_square f g (h \<cdot> l) (k \<cdot> l)"
      using assms
      apply (elim commutative_squareE, intro commutative_squareI, auto)
      using comp_assoc by metis

    lemma arr_comp_commutative_square:
    assumes "commutative_square f g h k" and "seq l f"
    shows "commutative_square (l \<cdot> f) (l \<cdot> g) h k"
      using assms comp_assoc
      by (elim commutative_squareE, intro commutative_squareI, auto)

  end

  subsection "Cospan Diagrams"

  (* TODO: Rework the ugly development of equalizers into this form. *)

  text \<open>
    The ``shape'' of a cospan diagram is a category having two non-identity arrows
    with distinct domains and a common codomain.
  \<close>

  locale cospan_shape
  begin

    datatype Arr = Null | AA | BB | TT | AT | BT

    fun comp
    where "comp AA AA = AA"
        | "comp AT AA = AT"
        | "comp TT AT = AT"
        | "comp BB BB = BB"
        | "comp BT BB = BT"
        | "comp TT BT = BT"
        | "comp TT TT = TT"
        | "comp _ _ = Null"

    interpretation partial_magma comp
    proof
      show "\<exists>!n. \<forall>f. comp n f = n \<and> comp f n = n"
      proof
        show "\<forall>f. comp Null f = Null \<and> comp f Null = Null" by simp
        show "\<And>n. \<forall>f. comp n f = n \<and> comp f n = n \<Longrightarrow> n = Null"
          by (metis comp.simps(8))
      qed
    qed

    lemma null_char:
    shows "null = Null"
    proof -
      have "\<forall>f. comp Null f = Null \<and> comp f Null = Null" by simp
      thus ?thesis
        using null_def ex_un_null theI [of "\<lambda>n. \<forall>f. comp n f = n \<and> comp f n = n"]
        by (metis partial_magma.comp_null(2) partial_magma_axioms)
    qed

    lemma ide_char:
    shows "ide f \<longleftrightarrow> f = AA \<or> f = BB \<or> f = TT"
    proof
      show "ide f \<Longrightarrow> f = AA \<or> f = BB \<or> f = TT"
        using ide_def null_char by (cases f, simp_all)
      show "f = AA \<or> f = BB \<or> f = TT \<Longrightarrow> ide f"
      proof -
        have 1: "\<And>f g. f = AA \<or> f = BB \<or> f = TT \<Longrightarrow>
                       comp f f \<noteq> Null \<and>
                       (comp g f \<noteq> Null \<longrightarrow> comp g f = g) \<and>
                       (comp f g \<noteq> Null \<longrightarrow> comp f g = g)"
        proof -
          fix f g
          show "f = AA \<or> f = BB \<or> f = TT \<Longrightarrow>
                  comp f f \<noteq> Null \<and>
                  (comp g f \<noteq> Null \<longrightarrow> comp g f = g) \<and>
                  (comp f g \<noteq> Null \<longrightarrow> comp f g = g)"
            by (cases f; cases g, auto)
        qed
        assume f: "f = AA \<or> f = BB \<or> f = TT"
        show "ide f"
          using f 1 ide_def null_char by simp
      qed
    qed

    fun Dom
    where "Dom AA = AA"
        | "Dom BB = BB"
        | "Dom TT = TT"
        | "Dom AT = AA"
        | "Dom BT = BB"
        | "Dom _ = Null"

    fun Cod
    where "Cod AA = AA"
        | "Cod BB = BB"
        | "Cod TT = TT"
        | "Cod AT = TT"
        | "Cod BT = TT"
        | "Cod _ = Null"

    lemma domains_char':
    shows "domains f = (if f = Null then {} else {Dom f})"
    proof (cases "f = Null")
      show "f = Null \<Longrightarrow> ?thesis"
        using domains_null null_char by auto
      show "f \<noteq> Null \<Longrightarrow> ?thesis"
      proof -
        assume f: "f \<noteq> Null"
        have "Dom f \<in> domains f"
          using f domains_def ide_char null_char by (cases f, auto)
        moreover have "\<And>a. a \<in> domains f \<Longrightarrow> a = Dom f"
          using f domains_def ide_char null_char by (cases f, auto)
        ultimately have "domains f = {Dom f}" by blast
        thus ?thesis using f by simp
      qed
    qed

    lemma codomains_char':
    shows "codomains f = (if f = Null then {} else {Cod f})"
    proof (cases "f = Null")
      show "f = Null \<Longrightarrow> ?thesis"
        using codomains_null null_char by auto
      show "f \<noteq> Null \<Longrightarrow> ?thesis"
      proof -
        assume f: "f \<noteq> Null"
        have "Cod f \<in> codomains f"
          using f codomains_def ide_char null_char by (cases f, auto)
        moreover have "\<And>a. a \<in> codomains f \<Longrightarrow> a = Cod f"
          using f codomains_def ide_char null_char by (cases f, auto)
        ultimately have "codomains f = {Cod f}" by blast
        thus ?thesis using f by simp
      qed
    qed

    lemma arr_char:
    shows "arr f \<longleftrightarrow> f \<noteq> Null"
      using arr_def domains_char' codomains_char' by simp

    lemma seq_char:
    shows "seq g f \<longleftrightarrow> (f = AA \<and> (g = AA \<or> g = AT)) \<or>
                       (f = BB \<and> (g = BB \<or> g = BT)) \<or>
                       (f = AT \<and> g = TT) \<or>
                       (f = BT \<and> g = TT) \<or>
                       (f = TT \<and> g = TT)"
      using arr_char null_char
      by (cases f; cases g, simp_all)

    interpretation category comp
    proof
      show "\<And>g f. comp g f \<noteq> null \<Longrightarrow> seq g f"
        using null_char arr_char seq_char by simp
      show "\<And>f. (domains f \<noteq> {}) = (codomains f \<noteq> {})"
        using domains_char' codomains_char' by auto
      show "\<And>h g f. seq h g \<Longrightarrow> seq (comp h g) f \<Longrightarrow> seq g f"
      proof -
        fix f g h
        show "seq h g \<Longrightarrow> seq (comp h g) f \<Longrightarrow> seq g f"
          using seq_char arr_char
          by (cases g; cases h; simp_all)
      qed
      show "\<And>h g f. seq h (comp g f) \<Longrightarrow> seq g f \<Longrightarrow> seq h g"
      proof -
        fix f g h
        show "seq h (comp g f) \<Longrightarrow> seq g f \<Longrightarrow> seq h g"
          using seq_char arr_char
          by (cases f; cases g; simp_all)
      qed
      show "\<And>g f h. seq g f \<Longrightarrow> seq h g \<Longrightarrow> seq (comp h g) f"
      proof -
        fix f g h
        show "seq g f \<Longrightarrow> seq h g \<Longrightarrow> seq (comp h g) f"
          using seq_char arr_char
          by (cases f; simp_all; cases g; simp_all; cases h; auto)
      qed
      show "\<And>g f h. seq g f \<Longrightarrow> seq h g \<Longrightarrow> comp (comp h g) f = comp h (comp g f)"
      proof -
        fix f g h
        show "seq g f \<Longrightarrow> seq h g \<Longrightarrow> comp (comp h g) f = comp h (comp g f)"
          using seq_char
          by (cases f; simp_all; cases g; simp_all; cases h; auto)
      qed
    qed

    lemma is_category:
    shows "category comp"
      ..

    (*
     * TODO: The statement of domains_char and codomains_char in Category should be corrected
     * so that they are true characterizations that cover the case of null.
     *)

    lemma dom_char:
    shows "dom = Dom"
      using dom_def domains_char domains_char' null_char by auto

    lemma cod_char:
    shows "cod = Cod"
      using cod_def codomains_char codomains_char' null_char by auto

  end

  sublocale cospan_shape \<subseteq> category comp
    using is_category by auto

  locale cospan_diagram =
    J: cospan_shape +
    C: category C
  for C :: "'c comp"      (infixr "\<cdot>" 55)
  and f0 :: 'c
  and f1 :: 'c +
  assumes is_cospan: "C.cospan f0 f1"
  begin

    no_notation J.comp   (infixr "\<cdot>" 55)
    notation J.comp      (infixr "\<cdot>\<^sub>J" 55)

    fun map
    where "map J.AA = C.dom f0"
        | "map J.BB = C.dom f1"
        | "map J.TT = C.cod f0"
        | "map J.AT = f0"
        | "map J.BT = f1"
        | "map _ = C.null"

  end

  sublocale cospan_diagram \<subseteq> diagram J.comp C map
  proof
    show "\<And>f. \<not> J.arr f \<Longrightarrow> map f = C.null"
      using J.arr_char by simp
    fix f
    assume f: "J.arr f"
    show "C.arr (map f)"
      using f J.arr_char is_cospan by (cases f, simp_all)
    show "C.dom (map f) = map (J.dom f)"
      using f J.arr_char J.dom_char is_cospan by (cases f, simp_all)
    show "C.cod (map f) = map (J.cod f)"
      using f J.arr_char J.cod_char is_cospan by (cases f, simp_all)
    next
    fix f g
    assume fg: "J.seq g f"
    show "map (g \<cdot>\<^sub>J f) = map g \<cdot> map f"
      using fg J.seq_char J.null_char J.not_arr_null is_cospan
      apply (cases f; cases g, simp_all)
      using C.comp_arr_dom C.comp_cod_arr by auto
  qed

  subsection "Category with Pullbacks"

  text \<open>
    A \emph{pullback} in a category @{term C} is a limit of a cospan diagram in @{term C}.
  \<close>

  context cospan_diagram
  begin

    definition mkCone
    where "mkCone p0 p1 \<equiv> \<lambda>j. if j = J.AA then p0
                               else if j = J.BB then p1
                               else if j = J.AT then f0 \<cdot> p0
                               else if j = J.BT then f1 \<cdot> p1
                               else if j = J.TT then f0 \<cdot> p0
                               else C.null"

    abbreviation is_rendered_commutative_by
    where "is_rendered_commutative_by p0 p1 \<equiv> C.seq f0 p0 \<and> f0 \<cdot> p0 = f1 \<cdot> p1"

    abbreviation has_as_pullback
    where "has_as_pullback p0 p1 \<equiv> limit_cone (C.dom p0) (mkCone p0 p1)"

    lemma cone_mkCone:
    assumes "is_rendered_commutative_by p0 p1"
    shows "cone (C.dom p0) (mkCone p0 p1)"
    proof -
      interpret E: constant_functor J.comp C \<open>C.dom p0\<close>
        apply unfold_locales using assms by auto
      show "cone (C.dom p0) (mkCone p0 p1)"
      proof
        fix f
        show "\<not> J.arr f \<Longrightarrow> mkCone p0 p1 f = C.null"
          using mkCone_def J.arr_char by simp
        assume f: "J.arr f"
        show "C.dom (mkCone p0 p1 f) = E.map (J.dom f)"
          using assms f mkCone_def J.arr_char J.dom_char
          apply (cases f, simp_all)
             apply (metis C.dom_comp)
            apply (metis C.dom_comp)
           apply (metis C.dom_comp)
          by (metis C.dom_comp)
        show "C.cod (mkCone p0 p1 f) = map (J.cod f)"
          using assms f mkCone_def J.arr_char J.cod_char is_cospan
          by (cases f, auto)
        show "map f \<cdot> mkCone p0 p1 (J.dom f) = mkCone p0 p1 f"
          using assms f mkCone_def J.arr_char J.dom_char C.comp_ide_arr is_cospan
          by (cases f, auto)
        show "mkCone p0 p1 (J.cod f) \<cdot> E.map f = mkCone p0 p1 f"
          using assms f mkCone_def J.arr_char J.cod_char C.comp_arr_dom
          apply (cases f, auto)
             apply (metis C.dom_comp C.seqE)
            apply (metis C.dom_comp)
           apply (metis C.dom_comp)
          by (metis C.dom_comp)
      qed
    qed

    lemma is_rendered_commutative_by_cone:
    assumes "cone a \<chi>"
    shows "is_rendered_commutative_by (\<chi> J.AA) (\<chi> J.BB)"
    proof -
      interpret \<chi>: cone J.comp C map a \<chi>
        using assms by auto
      show ?thesis
      proof
        show "C.seq f0 (\<chi> J.AA)"
          by (metis C.seqI J.category_axioms J.cod_char J.seq_char \<chi>.preserves_cod
              \<chi>.preserves_reflects_arr category.seqE cospan_diagram.is_cospan
              cospan_diagram_axioms cospan_shape.Cod.simps(1) map.simps(1))
        show "f0 \<cdot> \<chi> J.AA = f1 \<cdot> \<chi> J.BB"
          by (metis J.cod_char J.dom_char \<chi>.A.map_simp \<chi>.naturality
              cospan_shape.Cod.simps(4-5) cospan_shape.Dom.simps(4-5)
              cospan_shape.comp.simps(2,5) cospan_shape.seq_char
              map.simps(4-5))
      qed
    qed

    lemma mkCone_cone:
    assumes "cone a \<chi>"
    shows "mkCone (\<chi> J.AA) (\<chi> J.BB) = \<chi>"
    proof -
      interpret \<chi>: cone J.comp C map a \<chi>
        using assms by auto
      have 1: "is_rendered_commutative_by (\<chi> J.AA) (\<chi> J.BB)"
        using assms is_rendered_commutative_by_cone by blast
      interpret mkCone_\<chi>: cone J.comp C map \<open>C.dom (\<chi> J.AA)\<close> \<open>mkCone (\<chi> J.AA) (\<chi> J.BB)\<close>
        using assms cone_mkCone 1 by auto
      show ?thesis
      proof -
        have "\<And>j. j = J.AA \<Longrightarrow> mkCone (\<chi> J.AA) (\<chi> J.BB) j = \<chi> j"
          using mkCone_def \<chi>.is_extensional by simp
        moreover have "\<And>j. j = J.BB \<Longrightarrow> mkCone (\<chi> J.AA) (\<chi> J.BB) j = \<chi> j"
          using mkCone_def \<chi>.is_extensional by simp
        moreover have "\<And>j. j = J.TT \<Longrightarrow> mkCone (\<chi> J.AA) (\<chi> J.BB) j = \<chi> j"
          using 1 mkCone_def \<chi>.is_extensional \<chi>.A.map_simp \<chi>.preserves_comp_1
                cospan_shape.seq_char
          by (metis J.Arr.distinct(14) J.Arr.distinct(20) J.category_axioms \<chi>.is_natural_2
              category.seqE cospan_shape.Arr.distinct(25) cospan_shape.Arr.distinct(27)
              cospan_shape.comp.simps(5) map.simps(5))
        ultimately have "\<And>j. J.ide j \<Longrightarrow> mkCone (\<chi> J.AA) (\<chi> J.BB) j = \<chi> j"
          using J.ide_char by auto
        thus "mkCone (\<chi> J.AA) (\<chi> J.BB) = \<chi>"
          using mkCone_def NaturalTransformation.eqI [of J.comp C]
                \<chi>.natural_transformation_axioms mkCone_\<chi>.natural_transformation_axioms
                J.ide_char
          by simp
      qed
    qed

  end

  locale pullback_cone =
    J: cospan_shape +
    C: category C +
    D: cospan_diagram C f0 f1 +
    limit_cone J.comp C D.map \<open>C.dom p0\<close> \<open>D.mkCone p0 p1\<close>
  for C :: "'c comp"      (infixr "\<cdot>" 55)
  and f0 :: 'c
  and f1 :: 'c
  and p0 :: 'c
  and p1 :: 'c
  begin

    (* TODO: Equalizer should be simplifiable in the same way. *)
    lemma renders_commutative:
    shows "D.is_rendered_commutative_by p0 p1"
      using D.mkCone_def D.cospan_diagram_axioms cone_axioms
            cospan_diagram.is_rendered_commutative_by_cone
      by fastforce

    lemma is_universal':
    assumes "D.is_rendered_commutative_by p0' p1'"
    shows "\<exists>!h. \<guillemotleft>h : C.dom p0' \<rightarrow> C.dom p0\<guillemotright> \<and> p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
    proof -
      have "D.cone (C.dom p0') (D.mkCone p0' p1')"
        using assms D.cone_mkCone by blast
      hence 1: "\<exists>!h. \<guillemotleft>h : C.dom p0' \<rightarrow> C.dom p0\<guillemotright> \<and>
                     D.cones_map h (D.mkCone p0 p1) = D.mkCone p0' p1'"
        using is_universal [of "C.dom p0'" "D.mkCone p0' p1'"] by simp
      have 2: "\<And>h. \<guillemotleft>h : C.dom p0' \<rightarrow> C.dom p0\<guillemotright> \<Longrightarrow>
                    D.cones_map h (D.mkCone p0 p1) = D.mkCone p0' p1' \<longleftrightarrow>
                    p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
      proof -
        fix h
        assume h: "\<guillemotleft>h : C.dom p0' \<rightarrow> C.dom p0\<guillemotright>"
        show "D.cones_map h (D.mkCone p0 p1) = D.mkCone p0' p1' \<longleftrightarrow>
              p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
        proof
          assume 3: "D.cones_map h (D.mkCone p0 p1) = D.mkCone p0' p1'"
          show "p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
          proof
            show "p0 \<cdot> h = p0'"
            proof -
              have "p0' = D.mkCone p0' p1' J.AA"
                using D.mkCone_def J.arr_char by simp
              also have "... = D.cones_map h (D.mkCone p0 p1) J.AA"
                using 3 by simp
              also have "... = p0 \<cdot> h"
                using h D.mkCone_def J.arr_char cone_\<chi> by auto
              finally show ?thesis by auto
            qed
            show "p1 \<cdot> h = p1'"
            proof -
              have "p1' = D.mkCone p0' p1' J.BB"
                using D.mkCone_def J.arr_char by simp
              also have "... = D.cones_map h (D.mkCone p0 p1) J.BB"
                using 3 by simp
              also have "... = p1 \<cdot> h"
                using h D.mkCone_def J.arr_char cone_\<chi> by auto
              finally show ?thesis by auto
            qed
          qed
          next
          assume 4: "p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
          show "D.cones_map h (D.mkCone p0 p1) = D.mkCone p0' p1'"
          proof
            fix j
            have "\<not> J.arr j \<Longrightarrow> D.cones_map h (D.mkCone p0 p1) j = D.mkCone p0' p1' j"
              using h cone_axioms D.mkCone_def J.arr_char by auto
            moreover have "J.arr j \<Longrightarrow>
                           D.cones_map h (D.mkCone p0 p1) j = D.mkCone p0' p1' j"
              using assms h 4 cone_\<chi> D.mkCone_def J.arr_char [of J.AT] renders_commutative
                    C.comp_assoc
              by fastforce
            ultimately show "D.cones_map h (D.mkCone p0 p1) j = D.mkCone p0' p1' j"
              using J.arr_char J.Dom.cases by blast
          qed
        qed
      qed
      thus ?thesis using 1 by blast
    qed

    lemma induced_arrowI':
    assumes "D.is_rendered_commutative_by p0' p1'"
    shows "\<guillemotleft>induced_arrow (C.dom p0') (D.mkCone p0' p1') : C.dom p0' \<rightarrow> C.dom p0\<guillemotright>"
    and "p0 \<cdot> induced_arrow (C.dom p0') (D.mkCone p0' p1') = p0'"
    and "p1 \<cdot> induced_arrow (C.dom p1') (D.mkCone p0' p1') = p1'"
    proof -
      interpret A': constant_functor J.comp C \<open>C.dom p0'\<close>
        using assms by (unfold_locales, auto)
      have cone: "D.cone (C.dom p0') (D.mkCone p0' p1')"
        using assms D.cone_mkCone [of p0' p1'] by blast
      show 1: "p0 \<cdot> induced_arrow (C.dom p0') (D.mkCone p0' p1') = p0'"
      proof -
        have "p0 \<cdot> induced_arrow (C.dom p0') (D.mkCone p0' p1') =
                D.cones_map (induced_arrow (C.dom p0') (D.mkCone p0' p1'))
                            (D.mkCone p0 p1) J.AA"
          using cone induced_arrowI(1) D.mkCone_def J.arr_char cone_\<chi> by force
        also have "... = p0'"
        proof -
          have "D.cones_map (induced_arrow (C.dom p0') (D.mkCone p0' p1'))
                            (D.mkCone p0 p1) =
                D.mkCone p0' p1'"
            using cone induced_arrowI by blast
          thus ?thesis
            using J.arr_char D.mkCone_def by simp
        qed
        finally show ?thesis by auto
      qed
      show 2: "p1 \<cdot> induced_arrow (C.dom p1') (D.mkCone p0' p1') = p1'"
      proof -
        have "p1 \<cdot> induced_arrow (C.dom p1') (D.mkCone p0' p1') =
                D.cones_map (induced_arrow (C.dom p0') (D.mkCone p0' p1'))
                            (D.mkCone p0 p1) J.BB"
        proof -
          have "C.dom p0' = C.dom p1'"
            using assms by (metis C.dom_comp)
          thus ?thesis
            using cone induced_arrowI(1) D.mkCone_def J.arr_char cone_\<chi> by force
        qed
        also have "... = p1'"
        proof -
          have "D.cones_map (induced_arrow (C.dom p0') (D.mkCone p0' p1'))
                            (D.mkCone p0 p1) =
                D.mkCone p0' p1'"
            using cone induced_arrowI by blast
          thus ?thesis
            using J.arr_char D.mkCone_def by simp
        qed
        finally show ?thesis by auto
      qed
      show "\<guillemotleft>induced_arrow (C.dom p0') (D.mkCone p0' p1') : C.dom p0' \<rightarrow> C.dom p0\<guillemotright>"
        using 1 cone induced_arrowI by simp
    qed

  end

  context category
  begin

    definition has_as_pullback
    where "has_as_pullback f0 f1 p0 p1 \<equiv>
           cospan f0 f1 \<and> cospan_diagram.has_as_pullback C f0 f1 p0 p1"

    definition has_pullbacks
    where "has_pullbacks = (\<forall>f0 f1. cospan f0 f1 \<longrightarrow> (\<exists>p0 p1. has_as_pullback f0 f1 p0 p1))"

  end

  locale category_with_pullbacks =
    category +
  assumes has_pullbacks: has_pullbacks

  subsection "Elementary Category with Pullbacks"

  text \<open>
    An \emph{elementary category with pullbacks} is a category equipped with a specific
    way of mapping each cospan to a span such that the resulting square commutes and
    such that the span is universal for that property.  It is useful to assume that the
    functions mapping a cospan to the two projections of the pullback, are extensional;
    that is, they yield @{term null} when applied to arguments that do not form a cospan.
  \<close>

  locale elementary_category_with_pullbacks =
    category C
  for C :: "'a comp"                              (infixr "\<cdot>" 55)
  and prj0 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"                    ("\<p>\<^sub>0[_, _]")
  and prj1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"                    ("\<p>\<^sub>1[_, _]") +
  assumes prj0_ext: "\<not> cospan f g \<Longrightarrow> \<p>\<^sub>0[f, g] = null"
  and prj1_ext: "\<not> cospan f g \<Longrightarrow> \<p>\<^sub>1[f, g] = null"
  and pullback_commutes [intro]: "cospan f g \<Longrightarrow> commutative_square f g \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]"
  and universal: "commutative_square f g h k \<Longrightarrow> \<exists>!l. \<p>\<^sub>1[f, g] \<cdot> l = h \<and> \<p>\<^sub>0[f, g] \<cdot> l = k"
  begin

    lemma pullback_commutes':
    assumes "cospan f g"
    shows "f \<cdot> \<p>\<^sub>1[f, g] = g \<cdot> \<p>\<^sub>0[f, g]"
      using assms commutative_square_def by blast

    lemma prj0_in_hom':
    assumes "cospan f g"
    shows "\<guillemotleft>\<p>\<^sub>0[f, g] : dom \<p>\<^sub>0[f, g] \<rightarrow> dom g\<guillemotright>"
      using assms pullback_commutes
      by (metis category.commutative_squareE category_axioms in_homI)

    lemma prj1_in_hom':
    assumes "cospan f g"
    shows "\<guillemotleft>\<p>\<^sub>1[f, g] : dom \<p>\<^sub>0[f, g] \<rightarrow> dom f\<guillemotright>"
      using assms pullback_commutes
      by (metis category.commutative_squareE category_axioms in_homI)

    text \<open>
      The following gives us a notation for the common domain of the two projections
      of a pullback.
    \<close>

    definition pbdom        (infix "\<down>\<down>" 51)
    where "f \<down>\<down> g \<equiv> dom \<p>\<^sub>0[f, g]"

    lemma pbdom_in_hom [intro]:
    assumes "cospan f g"
    shows "\<guillemotleft>f \<down>\<down> g : f \<down>\<down> g \<rightarrow> f \<down>\<down> g\<guillemotright>"
      unfolding pbdom_def
      using assms prj0_in_hom'
      by (metis arr_dom_iff_arr arr_iff_in_hom cod_dom dom_dom in_homE)

    lemma ide_pbdom [simp]:
    assumes "cospan f g"
    shows "ide (f \<down>\<down> g)"
      using assms ide_in_hom by auto[1]

    lemma prj0_in_hom [intro, simp]:
    assumes "cospan f g" and "a = f \<down>\<down> g" and "b = dom g"
    shows "\<guillemotleft>\<p>\<^sub>0[f, g] : a \<rightarrow> b\<guillemotright>"
      unfolding pbdom_def
      using assms prj0_in_hom' by (simp add: pbdom_def)

    lemma prj1_in_hom [intro, simp]:
    assumes "cospan f g" and "a = f \<down>\<down> g" and "b = dom f"
    shows "\<guillemotleft>\<p>\<^sub>1[f, g] : a \<rightarrow> b\<guillemotright>"
      unfolding pbdom_def
      using assms prj1_in_hom' by (simp add: pbdom_def)

    lemma prj0_simps [simp]:
    assumes "cospan f g"
    shows "arr \<p>\<^sub>0[f, g]" and "dom \<p>\<^sub>0[f, g] = f \<down>\<down> g" and "cod \<p>\<^sub>0[f, g] = dom g"
      using assms prj0_in_hom by (blast, blast, blast)

    lemma prj0_simps_arr [iff]:
    shows "arr \<p>\<^sub>0[f, g] \<longleftrightarrow> cospan f g"
    proof
      show "cospan f g \<Longrightarrow> arr \<p>\<^sub>0[f, g]"
        using prj0_in_hom by auto
      show "arr \<p>\<^sub>0[f, g] \<Longrightarrow> cospan f g"
        using prj0_ext not_arr_null by metis
    qed

    lemma prj1_simps [simp]:
    assumes "cospan f g"
    shows "arr \<p>\<^sub>1[f, g]" and "dom \<p>\<^sub>1[f, g] = f \<down>\<down> g" and "cod \<p>\<^sub>1[f, g] = dom f"
      using assms prj1_in_hom by (blast, blast, blast)

    lemma prj1_simps_arr [iff]:
    shows "arr \<p>\<^sub>1[f, g] \<longleftrightarrow> cospan f g"
    proof
      show "cospan f g \<Longrightarrow> arr \<p>\<^sub>1[f, g]"
        using prj1_in_hom by auto
      show "arr \<p>\<^sub>1[f, g] \<Longrightarrow> cospan f g"
        using prj1_ext not_arr_null by metis
    qed

    lemma span_prj:
    assumes "cospan f g"
    shows "span \<p>\<^sub>0[f, g] \<p>\<^sub>1[f, g]"
      using assms by simp

    text \<open>
      We introduce a notation for tupling, which produces the induced arrow into a pullback.
      In our notation, the ``$0$-side'', which we regard as the input, occurs on the right,
      and the ``$1$-side'', which we regard as the output, occurs on the left.
    \<close>

    definition tuple         ("\<langle>_ \<lbrakk>_, _\<rbrakk> _\<rangle>")
    where "\<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<equiv> if commutative_square f g h k then
                           THE l. \<p>\<^sub>0[f, g] \<cdot> l = k \<and> \<p>\<^sub>1[f, g] \<cdot> l = h
                         else null"

    lemma tuple_in_hom [intro]:
    assumes "commutative_square f g h k"
    shows "\<guillemotleft>\<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> : dom h \<rightarrow> f \<down>\<down> g\<guillemotright>"
    proof
      have 1: "\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = k \<and> \<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = h"
        unfolding tuple_def
        using assms universal theI [of "\<lambda>l. \<p>\<^sub>0[f, g] \<cdot> l = k \<and> \<p>\<^sub>1[f, g] \<cdot> l = h"]
        apply simp
        by meson
      show "arr \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle>"
        using assms 1
        apply (elim commutative_squareE)
        by (metis (no_types, lifting) seqE)
      show "dom \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = dom h"
        using assms 1
        apply (elim commutative_squareE)
        by (metis (no_types, lifting) dom_comp)
      show "cod \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = f \<down>\<down> g"
        unfolding pbdom_def
        using assms 1
        apply (elim commutative_squareE)
        by (metis seqE)
    qed

    lemma tuple_is_extensional:
    assumes "\<not> commutative_square f g h k"
    shows "\<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = null"
      unfolding tuple_def
      using assms by simp

    lemma tuple_simps [simp]:
    assumes "commutative_square f g h k"
    shows "arr \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle>" and "dom \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = dom h" and "cod \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = f \<down>\<down> g"
      using assms tuple_in_hom apply blast
      using assms tuple_in_hom apply blast
      using assms tuple_in_hom by blast

    lemma prj_tuple [simp]:
    assumes "commutative_square f g h k"
    shows "\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = k" and "\<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = h"
    proof -
      have 1: "\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = k \<and> \<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = h"
        unfolding tuple_def
        using assms universal theI [of "\<lambda>l. \<p>\<^sub>0[f, g] \<cdot> l = k \<and> \<p>\<^sub>1[f, g] \<cdot> l = h"]
        apply simp
        by meson
      show "\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = k" using 1 by simp
      show "\<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> = h" using 1 by simp
    qed

    lemma tuple_prj:
    assumes "cospan f g" and "seq \<p>\<^sub>1[f, g] h"
    shows "\<langle>\<p>\<^sub>1[f, g] \<cdot> h \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g] \<cdot> h\<rangle> = h"
    proof -
      have 1: "commutative_square f g (\<p>\<^sub>1[f, g] \<cdot> h) (\<p>\<^sub>0[f, g] \<cdot> h)"
        using assms pullback_commutes
        by (simp add: commutative_square_comp_arr)
      have "\<p>\<^sub>0[f, g] \<cdot> \<langle>\<p>\<^sub>1[f, g] \<cdot> h \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g] \<cdot> h\<rangle> = \<p>\<^sub>0[f, g] \<cdot> h"
        using assms 1 by simp
      moreover have "\<p>\<^sub>1[f, g] \<cdot> \<langle>\<p>\<^sub>1[f, g] \<cdot> h \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g] \<cdot> h\<rangle> = \<p>\<^sub>1[f, g] \<cdot> h"
        using assms 1 by simp
      ultimately show ?thesis
        unfolding tuple_def
        using assms 1 universal [of f g "\<p>\<^sub>1[f, g] \<cdot> h" "\<p>\<^sub>0[f, g] \<cdot> h"]
              theI_unique [of "\<lambda>l. \<p>\<^sub>0[f, g] \<cdot> l = \<p>\<^sub>0[f, g] \<cdot> h \<and> \<p>\<^sub>1[f, g] \<cdot> l = \<p>\<^sub>1[f, g] \<cdot> h" h]
        by auto
    qed

    lemma tuple_prj_spc [simp]:
    assumes "cospan f g"
    shows "\<langle>\<p>\<^sub>1[f, g] \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g]\<rangle> = f \<down>\<down> g"
    proof -
      have "\<langle>\<p>\<^sub>1[f, g] \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g]\<rangle> = \<langle>\<p>\<^sub>1[f, g] \<cdot> (f \<down>\<down> g) \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g] \<cdot> (f \<down>\<down> g)\<rangle>"
        using assms comp_arr_dom by simp
      thus ?thesis
        using assms tuple_prj by simp
    qed

    lemma prj_joint_monic:
    assumes "cospan f g" and "seq \<p>\<^sub>1[f, g] h" and "seq \<p>\<^sub>1[f, g] h'"
    and "\<p>\<^sub>0[f, g] \<cdot> h = \<p>\<^sub>0[f, g] \<cdot> h'" and "\<p>\<^sub>1[f, g] \<cdot> h = \<p>\<^sub>1[f, g] \<cdot> h'"
    shows "h = h'"
    proof -
      have "h = \<langle>\<p>\<^sub>1[f, g] \<cdot> h \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g] \<cdot> h\<rangle>"
        using assms tuple_prj [of f g h] by simp
      also have "... = \<langle>\<p>\<^sub>1[f, g] \<cdot> h' \<lbrakk>f, g\<rbrakk> \<p>\<^sub>0[f, g] \<cdot> h'\<rangle>"
        using assms by simp
      also have "... = h'"
        using assms tuple_prj [of f g h'] by simp
      finally show ?thesis by blast
    qed

    text \<open>
      The pullback of an identity along an arbitrary arrow is an isomorphism.
    \<close>

    lemma iso_pullback_ide:
    assumes "cospan \<mu> \<nu>" and "ide \<mu>"
    shows "iso \<p>\<^sub>0[\<mu>, \<nu>]"
    proof -
      have "inverse_arrows \<p>\<^sub>0[\<mu>, \<nu>] \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle>"
      proof
        show 1: "ide (\<p>\<^sub>0[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle>)"
        proof -
          have "commutative_square \<mu> \<nu> \<nu> (dom \<nu>)"
            using assms comp_arr_dom comp_cod_arr by auto
          hence "\<p>\<^sub>0[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> = dom \<nu>"
            using assms prj_tuple(1) [of \<mu> \<nu> \<nu> "dom \<nu>"] by simp
          thus ?thesis
            using assms by simp
        qed
        show "ide (\<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>])"
        proof -
          have "\<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>] = (\<mu> \<down>\<down> \<nu>)"
          proof -
            have "\<p>\<^sub>0[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>] = \<p>\<^sub>0[\<mu>, \<nu>] \<cdot> (\<mu> \<down>\<down> \<nu>)"
            proof -
              have "\<p>\<^sub>0[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>] = (\<p>\<^sub>0[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle>) \<cdot> \<p>\<^sub>0[\<mu>, \<nu>]"
                using assms 1 comp_reduce by blast
              also have "... = dom \<nu> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>]"
              proof -
                have "commutative_square \<mu> \<nu> \<nu> (dom \<nu>)"
                  using assms comp_arr_dom comp_cod_arr by auto
                thus ?thesis
                  using assms prj_tuple(1) [of \<mu> \<nu> \<nu> "dom \<nu>"] by simp
              qed
              also have "... = \<p>\<^sub>0[\<mu>, \<nu>] \<cdot> (\<mu> \<down>\<down> \<nu>)"
                using assms prj0_in_hom [of \<mu> \<nu>] pullback_commutes comp_arr_dom comp_cod_arr
                by (metis in_homE)
              finally show ?thesis by blast
            qed
            moreover have "\<p>\<^sub>1[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>] = \<p>\<^sub>1[\<mu>, \<nu>] \<cdot> (\<mu> \<down>\<down> \<nu>)"
            proof -
              have "\<p>\<^sub>1[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>] = (\<p>\<^sub>1[\<mu>, \<nu>] \<cdot> \<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle>) \<cdot> \<p>\<^sub>0[\<mu>, \<nu>]"
                by (simp add: assms(2) local.comp_assoc)
              also have "... = \<nu> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>]"
              proof -
                have "commutative_square \<mu> \<nu> \<nu> (dom \<nu>)"
                  using assms comp_arr_dom comp_cod_arr by auto
                thus ?thesis
                  using assms prj_tuple(2) [of \<mu> \<nu> \<nu> "dom \<nu>"] by simp
              qed
              also have "... = \<mu> \<cdot> \<p>\<^sub>1[\<mu>, \<nu>]"
                using assms pullback_commutes
                by (simp add: commutative_square_def)
              also have "... = \<p>\<^sub>1[\<mu>, \<nu>] \<cdot> (\<mu> \<down>\<down> \<nu>)"
                using assms comp_arr_dom comp_cod_arr pullback_commutes by simp
              finally show ?thesis by simp
            qed
            ultimately show ?thesis
              using assms prj0_in_hom prj1_in_hom
                    prj_joint_monic [of \<mu> \<nu> "\<langle>\<nu> \<lbrakk>\<mu>, \<nu>\<rbrakk> dom \<nu>\<rangle> \<cdot> \<p>\<^sub>0[\<mu>, \<nu>]" "\<mu> \<down>\<down> \<nu>"]
              by (metis comp_arr_dom prj1_simps(1) prj1_simps(2))
          qed
          thus ?thesis
            using assms prj0_in_hom [of \<mu> \<nu>] ide_dom [of "\<p>\<^sub>1[\<mu>, \<nu>]"] by auto
        qed
      qed
      thus ?thesis by auto
    qed

    lemma comp_tuple_arr:
    assumes "commutative_square f g h k" and "seq h l"
    shows "\<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l = \<langle>h \<cdot> l \<lbrakk>f, g\<rbrakk> k \<cdot> l\<rangle>"
    proof -
      have "\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l = \<p>\<^sub>0[f, g] \<cdot> \<langle>h \<cdot> l \<lbrakk>f, g\<rbrakk> k \<cdot> l\<rangle>"
      proof -
        have "\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l = (\<p>\<^sub>0[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle>) \<cdot> l"
          using comp_assoc by simp
        also have "... = k \<cdot> l"
          using assms prj_tuple(1) by auto
        also have "... = \<p>\<^sub>0[f, g] \<cdot> \<langle>h \<cdot> l \<lbrakk>f, g\<rbrakk> k \<cdot> l\<rangle>"
        proof -
          have 1: "commutative_square f g (h \<cdot> l) (k \<cdot> l)"
            using assms commutative_square_comp_arr by auto
          show ?thesis
            using assms by (metis "1" prj_tuple(1))
        qed
        finally show ?thesis by blast
      qed
      moreover have "\<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l = \<p>\<^sub>1[f, g] \<cdot> \<langle>h \<cdot> l \<lbrakk>f, g\<rbrakk> k \<cdot> l\<rangle>"
      proof -
        have "\<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l = (\<p>\<^sub>1[f, g] \<cdot> \<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle>) \<cdot> l"
          using comp_assoc by simp
        also have "... = h \<cdot> l"
          using assms prj_tuple(2) by auto
        also have "... = \<p>\<^sub>1[f, g] \<cdot> \<langle>h \<cdot> l \<lbrakk>f, g\<rbrakk> k \<cdot> l\<rangle>"
        proof -
          have 1: "commutative_square f g (h \<cdot> l) (k \<cdot> l)"
            using assms commutative_square_comp_arr by blast
          show ?thesis
            using assms by (metis "1" prj_tuple(2))
        qed
        finally show ?thesis by blast
      qed
      moreover have "seq \<p>\<^sub>1[f, g] (\<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l)"
        using assms tuple_in_hom [of f h g k] prj1_in_hom
        by (intro seqI, elim seqE, auto, fastforce)
      moreover have "seq \<p>\<^sub>1[f, g] \<langle>h \<cdot> l \<lbrakk>f, g\<rbrakk> k \<cdot> l\<rangle>"
        using assms tuple_in_hom [of f "h \<cdot> l" g "k \<cdot> l"]
        using calculation(2) calculation(3) by auto
      ultimately show ?thesis
        using assms prj_joint_monic [of f g "\<langle>h \<lbrakk>f, g\<rbrakk> k\<rangle> \<cdot> l" "\<langle>h \<cdot> l \<lbrakk>f, g\<rbrakk> k \<cdot> l\<rangle>"]
        by auto
    qed

    lemma pullback_arr_cod:
    assumes "arr f"
    shows "inverse_arrows \<p>\<^sub>1[f, cod f] \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle>"
    and "inverse_arrows \<p>\<^sub>0[cod f, f] \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle>"
    proof -
      show "inverse_arrows \<p>\<^sub>1[f, cod f] \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle>"
      proof
        have 1: "commutative_square f (cod f) (dom f) f"
          using assms comp_arr_dom comp_cod_arr by auto
        show "ide (\<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f])"
        proof -
          have "\<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f] = f \<down>\<down> cod f"
          proof -
            have "\<p>\<^sub>0[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f] = \<p>\<^sub>0[f, cod f] \<cdot> (f \<down>\<down> cod f)"
            proof -
              have "\<p>\<^sub>0[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f] =
                    (\<p>\<^sub>0[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle>) \<cdot> \<p>\<^sub>1[f, cod f]"
                using comp_assoc by simp
              also have "... = f \<cdot> \<p>\<^sub>1[f, cod f]"
                using assms 1 prj_tuple(1) [of f "dom f" "cod f" f] by simp
              also have "... = \<p>\<^sub>0[f, cod f] \<cdot> (f \<down>\<down> cod f)"
                using assms 1 pullback_commutes [of f "cod f"] comp_arr_dom comp_cod_arr
                by (metis commutative_squareE pbdom_def)
              finally show ?thesis by blast
            qed
            moreover
            have "\<p>\<^sub>1[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f] = \<p>\<^sub>1[f, cod f] \<cdot> (f \<down>\<down> cod f)"
            proof -
              have "\<p>\<^sub>1[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f] =
                    (\<p>\<^sub>1[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle>) \<cdot> \<p>\<^sub>1[f, cod f]"
              proof -
                have "seq \<p>\<^sub>1[f, cod f] \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle>"
                  using assms 1 prj1_in_hom [of f "cod f"]
                        tuple_in_hom [of f "dom f" "cod f" f]
                  by auto
                moreover have "seq \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<p>\<^sub>1[f, cod f]"
                  using assms 1 prj1_in_hom [of f "cod f"]
                        tuple_in_hom [of f "dom f" "cod f" f]
                  by auto
                ultimately show ?thesis using comp_assoc by simp
              qed
              also have "... = dom f \<cdot> \<p>\<^sub>1[f, cod f]"
                using assms 1 prj_tuple(2) [of f "dom f" "cod f" f] by simp
              also have "... = \<p>\<^sub>1[f, cod f] \<cdot> (f \<down>\<down> cod f)"
                using assms comp_arr_dom comp_cod_arr by simp
              finally show ?thesis by blast
            qed
            ultimately show ?thesis
              using assms
                    prj_joint_monic
                      [of f "cod f" "\<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> \<cdot> \<p>\<^sub>1[f, cod f]" "f \<down>\<down> cod f"]
              by simp
          qed
          thus ?thesis
            using assms arr_cod cod_cod ide_dom prj1_simps_arr by simp
        qed
        show "ide (\<p>\<^sub>1[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle>)"
        proof -
          have "\<p>\<^sub>1[f, cod f] \<cdot> \<langle>dom f \<lbrakk>f, cod f\<rbrakk> f\<rangle> = dom f"
            using assms 1 by simp
          thus ?thesis using assms by simp
        qed
      qed

      show "inverse_arrows \<p>\<^sub>0[cod f, f] \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle>"
      proof
        have 1: "commutative_square (cod f) f f (dom f)"
          using assms comp_arr_dom comp_cod_arr by auto
        show "ide (\<p>\<^sub>0[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle>)"
        proof -
          have "\<p>\<^sub>0[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> = dom f"
            using assms 1 prj_tuple(1) [of "cod f" f f "dom f"] by blast
          thus ?thesis using assms by simp
        qed
        show "ide (\<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f])"
        proof -
          have "\<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f] = cod f \<down>\<down> f"
          proof -
            have "\<p>\<^sub>0[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f] = \<p>\<^sub>0[cod f, f] \<cdot> (cod f \<down>\<down> f)"
            proof -
              have "\<p>\<^sub>0[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f] =
                    (\<p>\<^sub>0[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle>) \<cdot> \<p>\<^sub>0[cod f, f]"
                using assms
                by (metis (no_types, lifting) category.ext category_axioms comp_reduce
                    match_1 match_2 seqE)
              also have "... = dom f \<cdot> \<p>\<^sub>0[cod f, f]"
                using assms 1 prj_tuple(1) [of "cod f" f f "dom f"] by simp
              also have "... = \<p>\<^sub>0[cod f, f] \<cdot> (cod f \<down>\<down> f)"
                using assms comp_arr_dom comp_cod_arr by simp
              finally show ?thesis
                using prj0_in_hom by blast
            qed
            moreover
            have "\<p>\<^sub>1[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f] = \<p>\<^sub>1[cod f, f] \<cdot> (cod f \<down>\<down> f)"
            proof -
              have "\<p>\<^sub>1[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f] =
                    (\<p>\<^sub>1[cod f, f] \<cdot> \<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle>) \<cdot> \<p>\<^sub>0[cod f, f]"
                using comp_assoc by simp
              also have "... = f \<cdot> \<p>\<^sub>0[cod f, f]"
                using assms 1 prj_tuple(2) [of "cod f" f f "dom f"] by simp
              also have "... = \<p>\<^sub>1[cod f, f] \<cdot> (cod f \<down>\<down> f)"
                using assms 1 pullback_commutes [of "cod f" f] comp_arr_dom comp_cod_arr
                by (metis (mono_tags, lifting) commutative_squareE pbdom_def)
              finally show ?thesis by blast
            qed
            ultimately show ?thesis
              using assms prj_joint_monic [of "cod f" f "\<langle>f \<lbrakk>cod f, f\<rbrakk> dom f\<rangle> \<cdot> \<p>\<^sub>0[cod f, f]"]
              by simp
          qed
          thus ?thesis using assms by simp
        qed
      qed
    qed

    text \<open>
      The pullback of a monomorphism along itself is automatically symmetric: the left
      and right projections are equal.
    \<close>

    lemma pullback_mono_self:
    assumes "mono f"
    shows "\<p>\<^sub>0[f, f] = \<p>\<^sub>1[f, f]"
    proof -
      have "f \<cdot> \<p>\<^sub>0[f, f] = f \<cdot> \<p>\<^sub>1[f, f]"
        using assms pullback_commutes [of f f]
        by (metis commutative_squareE mono_implies_arr)
      thus ?thesis
        using assms monoE [of f "\<p>\<^sub>1[f, f]" "\<p>\<^sub>0[f, f]"]
        by (metis mono_implies_arr prj0_simps(1) prj0_simps(3) seqI)
    qed

    lemma pullback_iso_self:
    assumes "iso f"
    shows "\<p>\<^sub>0[f, f] = \<p>\<^sub>1[f, f]"
      using assms pullback_mono_self iso_is_section section_is_mono by simp

    lemma pullback_ide_self [simp]:
    assumes "ide a"
    shows "\<p>\<^sub>0[a, a] = \<p>\<^sub>1[a, a]"
      using assms pullback_iso_self ide_is_iso by blast

  end

  subsection "Agreement between the Definitions"

  text \<open>
    It is very easy to write locale assumptions that have unintended consequences
    or that are even inconsistent.  So, to keep ourselves honest, we don't just accept the
    definition of ``elementary category with pullbacks'', but in fact we formally establish
    the sense in which it agrees with our standard definition of ``category with pullbacks'',
    which is given in terms of limit cones.
    This is extra work, but it ensures that we didn't make a mistake.
  \<close>

  context category_with_pullbacks
  begin

    definition prj1
    where "prj1 f g \<equiv> if cospan f g then
                         fst (SOME x. cospan_diagram.has_as_pullback C f g (fst x) (snd x))
                       else null"

    definition prj0
    where "prj0 f g \<equiv> if cospan f g then
                         snd (SOME x. cospan_diagram.has_as_pullback C f g (fst x) (snd x))
                       else null"

    lemma prj_yields_pullback:
    assumes "cospan f g"
    shows "cospan_diagram.has_as_pullback C f g (prj1 f g) (prj0 f g)"
    proof -
      have "\<exists>x. cospan_diagram.has_as_pullback C f g (fst x) (snd x)"
      proof -
        obtain p0 p1 where "cospan_diagram.has_as_pullback C f g p0 p1"
          using assms has_pullbacks has_pullbacks_def has_as_pullback_def by metis
        hence "cospan_diagram.has_as_pullback C f g (fst (p0, p1)) (snd (p0, p1))"
          by simp
        thus ?thesis by blast
      qed
      thus ?thesis
        using assms has_pullbacks has_pullbacks_def prj0_def prj1_def
              someI_ex [of "\<lambda>x. cospan_diagram.has_as_pullback C f g (fst x) (snd x)"]
        by simp
    qed

    interpretation elementary_category_with_pullbacks C prj0 prj1
    proof
      show "\<And>f g. \<not> cospan f g \<Longrightarrow> prj0 f g = null"
        using prj0_def by auto
      show "\<And>f g. \<not> cospan f g \<Longrightarrow> prj1 f g = null"
        using prj1_def by auto
      show "\<And>f g. cospan f g \<Longrightarrow> commutative_square f g (prj1 f g) (prj0 f g)"
      proof
        fix f g
        assume fg: "cospan f g"
        show "cospan f g" by fact
        interpret J: cospan_shape .
        interpret D: cospan_diagram C f g
          using fg by (unfold_locales, auto)
        let ?\<chi> = "D.mkCone (prj1 f g) (prj0 f g)"
        interpret \<chi>: limit_cone J.comp C D.map \<open>dom (prj1 f g)\<close> ?\<chi>
          using fg prj_yields_pullback by auto
        have 1: "prj1 f g = ?\<chi> J.AA \<and> prj0 f g = ?\<chi> J.BB"
          using D.mkCone_def by simp
        show "span (prj1 f g) (prj0 f g)"
        proof -
          have "arr (prj1 f g) \<and> arr (prj0 f g)"
            using 1 J.arr_char
            by (metis J.seqE \<chi>.preserves_reflects_arr cospan_shape.seq_char)
          moreover have "dom (prj1 f g) = dom (prj0 f g)"
            using 1
            by (metis D.is_rendered_commutative_by_cone D.map.simps(4) D.map.simps(5) J.seqE
                \<chi>.cone_axioms \<chi>.preserves_comp_1 \<chi>.preserves_dom cospan_shape.comp.simps(2)
                cospan_shape.comp.simps(5) cospan_shape.seq_char)
          ultimately show ?thesis by simp
        qed
        show "dom f = cod (prj1 f g)"
          using 1 \<chi>.preserves_cod [of J.BB] J.cod_char D.mkCone_def [of "prj1 f g" "prj0 f g"]
          by (metis D.map.simps(1) D.preserves_cod J.seqE \<chi>.preserves_cod cod_dom
              cospan_shape.seq_char fg)
        show "f \<cdot> prj1 f g = g \<cdot> prj0 f g"
          using 1 fg D.is_rendered_commutative_by_cone \<chi>.cone_axioms by force
      qed
      show "\<And>f g h k. commutative_square f g h k \<Longrightarrow> \<exists>!l. prj1 f g \<cdot> l = h \<and> prj0 f g \<cdot> l = k"
      proof -
        fix f g h k
        assume fghk: "commutative_square f g h k"
        interpret J: cospan_shape .
        interpret D: cospan_diagram C f g
          using fghk by (unfold_locales, auto)
        let ?\<chi> = "D.mkCone (prj1 f g) (prj0 f g)"
        interpret \<chi>: limit_cone J.comp C D.map \<open>dom (prj1 f g)\<close> ?\<chi>
          using fghk prj_yields_pullback by auto
        interpret \<chi>: pullback_cone C f g \<open>prj1 f g\<close> \<open>prj0 f g\<close> ..
        have 1: "prj1 f g = ?\<chi> J.AA \<and> prj0 f g = ?\<chi> J.BB"
          using D.mkCone_def by simp
        show "\<exists>!l. prj1 f g \<cdot> l = h \<and> prj0 f g \<cdot> l = k"
        proof
          let ?l = "SOME l. prj1 f g \<cdot> l = h \<and> prj0 f g \<cdot> l = k"
          show "prj1 f g \<cdot> ?l = h \<and> prj0 f g \<cdot> ?l = k"
             using fghk \<chi>.is_universal' [of h k] \<chi>.renders_commutative
                   someI_ex [of "\<lambda>l. prj1 f g \<cdot> l = h \<and> prj0 f g \<cdot> l = k"]
             by blast
          thus "\<And>l. prj1 f g \<cdot> l = h \<and> prj0 f g \<cdot> l = k \<Longrightarrow> l = ?l"
            using fghk \<chi>.is_universal' [of h k] \<chi>.renders_commutative
            by (metis (no_types, lifting) \<chi>.limit_cone_axioms category.in_homI category.seqE
                commutative_squareE dom_comp limit_cone_def seqI)
        qed
      qed
    qed

    proposition extends_to_elementary_category_with_pullbacks:
    shows "elementary_category_with_pullbacks C prj0 prj1"
      ..

  end

  context elementary_category_with_pullbacks
  begin

    interpretation category_with_pullbacks C
    proof
      show "has_pullbacks"
      proof (unfold has_pullbacks_def)
        have "\<And>f g. cospan f g \<Longrightarrow> \<exists>p0 p1. has_as_pullback f g p0 p1"
        proof -
          fix f g
          assume fg: "cospan f g"
          interpret J: cospan_shape .
          interpret D: cospan_diagram C f g
            using fg by (unfold_locales, auto)
          have 2: "D.is_rendered_commutative_by \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]"
            using fg pullback_commutes' by simp
          let ?\<chi> = "D.mkCone \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]"
          interpret \<chi>: cone J.comp C D.map \<open>dom \<p>\<^sub>1[f, g]\<close> ?\<chi>
            using D.cone_mkCone 2 by auto
          interpret \<chi>: limit_cone J.comp C D.map \<open>dom \<p>\<^sub>1[f, g]\<close> ?\<chi>
          proof
            fix a' \<chi>'
            assume \<chi>': "D.cone a' \<chi>'"
            interpret \<chi>': cone J.comp C D.map a' \<chi>'
              using \<chi>' by simp
            have 3: "commutative_square f g (\<chi>' J.AA) (\<chi>' J.BB)"
            proof
              show "cospan f g" by fact
              show "span (\<chi>' J.AA) (\<chi>' J.BB)"
                by (simp add: J.ide_char)
              show "dom f = cod (\<chi>' J.AA)"
                using \<open>span (\<chi>' J.AA) (\<chi>' J.BB)\<close> J.cod_char by auto
              show "f \<cdot> \<chi>' J.AA = g \<cdot> \<chi>' J.BB"
                using D.is_rendered_commutative_by_cone \<chi>'.cone_axioms by blast
            qed
            show "\<exists>!h. \<guillemotleft>h : a' \<rightarrow> dom \<p>\<^sub>1[f, g]\<guillemotright> \<and>
                       D.cones_map h (D.mkCone \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]) = \<chi>'"
            proof
              let ?h = "\<langle>\<chi>' J.AA \<lbrakk>f, g\<rbrakk> \<chi>' J.BB\<rangle>"
              show h': "\<guillemotleft>?h : a' \<rightarrow> dom \<p>\<^sub>1[f, g]\<guillemotright> \<and>
                        D.cones_map ?h (D.mkCone \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]) = \<chi>'"
              proof
                show h: "\<guillemotleft>?h : a' \<rightarrow> dom \<p>\<^sub>1[f, g]\<guillemotright>"
                  using fg 3 by fastforce
                show "D.cones_map ?h (D.mkCone \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]) = \<chi>'"
                proof -
                  have "D.mkCone \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g] \<in> D.cones (cod \<langle>\<chi>' J.AA \<lbrakk>f, g\<rbrakk> \<chi>' J.BB\<rangle>)"
                    using fg h D.cone_mkCone D.is_rendered_commutative_by_cone
                          \<chi>.cone_axioms
                    by auto
                  hence 4: "D.cones_map ?h (D.mkCone \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]) \<in> D.cones a'"
                    using fg h D.cones_map_mapsto [of ?h] by blast
                  interpret \<chi>'h: cone J.comp C D.map a'
                                   \<open>D.cones_map ?h (D.mkCone \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g])\<close>
                    using 4 by simp
                  show ?thesis
                  proof -
                    have "\<And>j. J.ide j \<Longrightarrow> D.cones_map ?h (D.mkCone \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]) j = \<chi>' j"
                    proof -
                      fix j
                      show "J.ide j \<Longrightarrow> D.cones_map ?h (D.mkCone \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]) j = \<chi>' j"
                        using fg h 3 J.ide_char D.mkCone_def [of "\<p>\<^sub>1[f, g]" "\<p>\<^sub>0[f, g]"]
                              \<chi>.cone_axioms
                        apply (cases j, simp_all)
                        by (metis D.map.simps(4) J.dom_eqI
                            \<chi>'.A.constant_functor_axioms \<chi>'.is_natural_1 \<chi>'.naturality
                            J.seqE constant_functor.map_simp cospan_shape.comp.simps(3)
                            cospan_shape.comp.simps(7) cospan_shape.seq_char
                            prj_tuple(2) comp_assoc)
                    qed
                    thus ?thesis
                      using NaturalTransformation.eqI
                            \<chi>'.natural_transformation_axioms \<chi>'h.natural_transformation_axioms
                      by blast
                  qed
                qed
              qed
              show "\<And>h. \<guillemotleft>h : a' \<rightarrow> dom \<p>\<^sub>1[f, g]\<guillemotright> \<and>
                        D.cones_map h (D.mkCone \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]) = \<chi>' \<Longrightarrow>
                          h = ?h"
              proof -
                fix h
                assume 1: "\<guillemotleft>h : a' \<rightarrow> dom \<p>\<^sub>1[f, g]\<guillemotright> \<and>
                        D.cones_map h (D.mkCone \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]) = \<chi>'"
                hence 2: "cod h = dom \<p>\<^sub>1[f, g]" using 1 by auto
                show "h = ?h"
                proof -
                  have "\<p>\<^sub>0[f, g] \<cdot> h = \<p>\<^sub>0[f, g] \<cdot> ?h"
                    using 1 3 fg J.arr_char \<chi>.cone_axioms J.Arr.distinct(11) D.mkCone_def
                    by auto
                  moreover have "\<p>\<^sub>1[f, g] \<cdot> h = \<p>\<^sub>1[f, g] \<cdot> ?h"
                    using 1 3 fg J.arr_char \<chi>.cone_axioms J.Arr.distinct(11) D.mkCone_def
                    by auto
                  ultimately show ?thesis
                    using fg 1 h' prj_joint_monic by blast
                qed
              qed
            qed
          qed
          have "has_as_pullback f g \<p>\<^sub>1[f, g] \<p>\<^sub>0[f, g]"
            using fg has_as_pullback_def \<chi>.limit_cone_axioms by blast
          thus "\<exists>p0 p1. has_as_pullback f g p0 p1"
            by blast
        qed
        thus "\<forall>f g. cospan f g \<longrightarrow> (\<exists>p0 p1. has_as_pullback f g p0 p1)"
          by simp
      qed
    qed

    proposition is_category_with_pullbacks:
    shows "category_with_pullbacks C"
      ..

  end

  sublocale elementary_category_with_pullbacks \<subseteq> category_with_pullbacks
    using is_category_with_pullbacks by auto

end

