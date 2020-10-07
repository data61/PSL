(*  Title:       FunctorCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter FunctorCategory

theory FunctorCategory
imports Category AbstractedCategory BinaryFunctor
begin

  text\<open>
    The functor category \<open>[A, B]\<close> is the category whose objects are functors
    from @{term A} to @{term B} and whose arrows correspond to natural transformations
    between these functors.
    Since the arrows of a functor category cannot (in the context of the present development)
    be directly identified with natural transformations, but rather only with natural
    transformations that have been equipped with their domain and codomain functors,
    and since there is no natural value to serve as @{term null},
    the construction here is a bit more involved than most of the other constructions
    on categories we have defined so far.
    What we do first is to construct a ``classical category'' whose objects are
    functors and whose arrows are natural transformations.  Then, we extract from this
    construction a partial composition using the standard result proved in the
    \<open>classical_category\<close> locale.  The effect of this standard result is to define
    arrows of the resulting category to be triples that consist of natural transformations
    equipped with their domain and codomain functors, injected into an option type
    in order to provide a value to be used as @{term null}.
    We then use the \<open>abstracted_category\<close> locale to lift the resulting category to an
    opaque arrow type, to avoid the possibility of a client of this theory inadvertently
    depending on the details of the concrete construction.
    Finally, we define a set of constructors for the opaque arrow type and characterize the
    resulting category in terms of these constructors so that the details of the concrete
    construction are no longer required and only the constructors and associated facts need
    be used.
\<close>

  section "Construction"

  text\<open>
    In this section a construction for functor categories is given.
    For convenience, we proceed indirectly, by way of the \<open>classical_category\<close> locale,
    though the construction could also have been done directly.
    Some auxiliary definitions are involved, but these are declared ``private'' and in
    the end what is exported is an opaque arrow type, a partial composition operation on
    this arrow type defining the category, functions for constructing and destructing arrows,
    and facts that characterize the basic notions (domain, codomain, \emph{etc.}) in terms
    of these functions.
\<close>

  locale functor_category =
    A: category A +
    B: category B
  for A :: "'a comp"     (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"     (infixr "\<cdot>\<^sub>B" 55)
  begin

    notation A.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>A _\<guillemotright>")
    notation B.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")

    context begin

      text\<open>
        First, we construct a ``classical category'' whose objects are functors and
        whose arrows are triples \<open>(\<tau>, (F, G))\<close>, where \<open>F\<close> and \<open>G\<close>
        are functors and \<open>\<tau>\<close> is a natural transformation from \<open>F\<close> to \<open>G\<close>.
\<close>

      private abbreviation Dom'
      where "Dom' t \<equiv> fst (snd t)"

      private abbreviation Cod'
      where "Cod' t \<equiv> snd (snd t)"

      private abbreviation Fun'
      where "Fun' t \<equiv> fst t"

      private definition Obj'
      where "Obj' F \<equiv> functor A B F"

      private definition Arr'
      where "Arr' t \<equiv> natural_transformation A B (Dom' t) (Cod' t) (Fun' t)"

      private abbreviation Id'
      where "Id' F \<equiv> (F, (F, F))"

      private definition Comp'
      where "Comp' t s \<equiv> (vertical_composite.map A B (Fun' s) (Fun' t), (Dom' s, Cod' t))"

      interpretation CC: classical_category Obj' Arr' Dom' Cod' Id' Comp'
      proof
        fix F
        assume F: "Obj' F"
        show "Arr' (Id' F)"
          using F Arr'_def Obj'_def functor_is_transformation by simp
        show "Dom' (Id' F) = F" using F by (metis fst_conv snd_conv)
        show "Cod' (Id' F) = F" using F by (metis snd_conv)
        next
        fix t
        assume t: "Arr' t"
        interpret \<tau>: natural_transformation A B "Dom' t" "Cod' t" "Fun' t"
          using t Arr'_def by blast
        show "Obj' (Dom' t)" unfolding Obj'_def ..
        show "Obj' (Cod' t)" unfolding Obj'_def ..
        show "Comp' t (Id' (Dom' t)) = t"
          by (metis Comp'_def \<tau>.natural_transformation_axioms fst_conv prod.collapse snd_conv
                    vcomp_ide_dom)
        show "Comp' (Id' (Cod' t)) t = t"
          by (metis (no_types, lifting) Comp'_def \<tau>.natural_transformation_axioms fst_conv
                    prod.collapse snd_conv vcomp_ide_cod)
        fix s
        assume s: "Arr' s"
        and st: "Cod' s = Dom' t"
        show "Arr' (Comp' t s)"
        proof -
          interpret \<sigma>: natural_transformation A B "Dom' s" "Cod' s" "Fun' s"
            using s Arr'_def by blast
          interpret VC: vertical_composite A B "Dom' s" "Cod' s" "Cod' t" "Fun' s" "Fun' t"
            using s t st Arr'_def Obj'_def
            by (simp add: natural_transformation_def vertical_composite.intro)
          have "natural_transformation A B (Dom' s) (Cod' t) (Fun' (Comp' t s))"
            using VC.is_natural_transformation Comp'_def by (metis fst_conv)
          thus ?thesis using s t st Arr'_def Comp'_def by (metis fst_conv snd_conv)
        qed
        show "Dom' (Comp' t s) = Dom' s"
          using Comp'_def fst_conv snd_conv by metis
        show "Cod' (Comp' t s) = Cod' t"
          using Comp'_def snd_conv by metis
        fix r
        assume r: "Arr' r"
        and rs: "Cod' r = Dom' s"
        show "Comp' (Comp' t s) r = Comp' t (Comp' s r)"
          unfolding Comp'_def
          using r s t rs st Arr'_def by auto
      qed

      private lemma CC_is_classical_category:
      shows "classical_category Obj' Arr' Dom' Cod' Id' Comp'" ..

      text\<open>
        At this point, @{term CC.comp} is a partial composition that defines a category.
        The arrow type for this category is @{typ "(('a \<Rightarrow> 'b) \<times> ('a \<Rightarrow> 'b) \<times> ('a \<Rightarrow> 'b)) option"},
        because the definition of @{term CC.comp} introduces an option type to provide
        a value to be used as @{term null}.  We next define a corresponding opaque arrow type.
\<close>

      typedef ('c, 'd) arr = "UNIV :: (('c \<Rightarrow> 'd) * ('c \<Rightarrow> 'd) * ('c \<Rightarrow> 'd)) option set" ..

      text\<open>
        The category defined by @{term CC.comp} is then lifted to the opaque arrow type.
\<close>

      interpretation AC: abstracted_category CC.comp Abs_arr Rep_arr UNIV
        using Rep_arr_inverse Abs_arr_inverse apply unfold_locales by auto

      text\<open>
        The function @{term AC.comp} is now the partial composition that defines the
        desired category.
\<close>

      definition comp :: "('a, 'b) arr comp"     (infixr "\<cdot>" 55)
      where "comp \<equiv> AC.comp"

      lemma is_category:
      shows "category comp"
        using AC.category_axioms comp_def by auto

      interpretation category comp
        using is_category by auto

      notation in_hom                            ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

      text\<open>
        We introduce a constructor \<open>mkArr\<close> for building an arrow from two
        functors and a natural transformation.
\<close>

      definition mkArr :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) arr"
      where "mkArr F G \<tau> \<equiv> (if natural_transformation A B F G \<tau>
                            then Abs_arr (Some (\<tau>, (F, G))) else null)"

      abbreviation mkIde
      where "mkIde F \<equiv> mkArr F F F"

      text\<open>
        Destructors @{term Dom}, @{term Cod}, and @{term Fun} extract the components
        of an arrow.
\<close>

      definition Dom :: "('a, 'b) arr \<Rightarrow> 'a \<Rightarrow> 'b"
      where "Dom t \<equiv> Dom' (the (Rep_arr t))"

      definition Cod :: "('a, 'b) arr \<Rightarrow> 'a \<Rightarrow> 'b"
      where "Cod t \<equiv> Cod' (the (Rep_arr t))"

      definition Fun :: "('a, 'b) arr \<Rightarrow> 'a \<Rightarrow> 'b"
      where "Fun t \<equiv> Fun' (the (Rep_arr t))"

      text\<open>
        Finally, we prove a set of facts that characterize the basic categorical notions
        in terms of the constructors and destructors.  These are the facts that will
        be exported.
\<close>

      lemma null_char:
      shows "null = Abs_arr None"
        using comp_def AC.null_char CC.null_char by simp

      lemma arr_char:
      shows "arr f \<longleftrightarrow> f \<noteq> null \<and> natural_transformation A B (Dom f) (Cod f) (Fun f)"
        using comp_def not_arr_null Dom_def Cod_def Fun_def null_char AC.arr_char CC.arr_char
              Arr'_def Rep_arr_inverse
        by metis

      lemma arrI [intro]:
      assumes "f \<noteq> null" and "natural_transformation A B (Dom f) (Cod f) (Fun f)"
      shows "arr f"
        using assms arr_char by blast

      lemma arrE [elim]:
      assumes "arr f"
      and "f \<noteq> null \<Longrightarrow> natural_transformation A B (Dom f) (Cod f) (Fun f) \<Longrightarrow> T"
      shows T
        using assms arr_char by simp

      lemma dom_char:
      shows "dom f = (if arr f then mkIde (Dom f) else null)"
        using comp_def mkArr_def Dom_def arr_char null_char AC.arr_char AC.dom_char CC.dom_char
              functor_is_transformation natural_transformation_def
        by (metis (no_types, lifting))

      lemma dom_simp:
      assumes "arr t"
      shows "dom t = mkIde (Dom t)"
       using assms dom_char by auto

      lemma cod_char:
      shows "cod f = (if arr f then mkIde (Cod f) else null)"
        using comp_def mkArr_def Cod_def arr_char null_char AC.arr_char AC.cod_char CC.cod_char
              functor_is_transformation natural_transformation_def
        by (metis (no_types, lifting))

      lemma cod_simp:
      assumes "arr t"
      shows "cod t = mkIde (Cod t)"
        using assms cod_char by auto

      lemma arr_mkArr [iff]:
      shows "arr (mkArr F G \<tau>) \<longleftrightarrow> natural_transformation A B F G \<tau>"
        using mkArr_def arr_char null_char Dom_def Cod_def Fun_def Abs_arr_inverse
              UNIV_I fst_conv snd_conv option.sel
        by (metis option.distinct(1))

      lemma Dom_mkArr [simp]:
      assumes "arr (mkArr F G \<tau>)"
      shows "Dom (mkArr F G \<tau>) = F"
        using assms arr_char mkArr_def Dom_def Abs_arr_inverse
        by (metis UNIV_I fst_conv option.sel snd_conv)

      lemma Cod_mkArr [simp]:
      assumes "arr (mkArr F G \<tau>)"
      shows "Cod (mkArr F G \<tau>) = G"
        using assms arr_char mkArr_def Cod_def Abs_arr_inverse
        by (metis UNIV_I option.sel snd_conv)

      lemma Fun_mkArr [simp]:
      assumes "arr (mkArr F G \<tau>)"
      shows "Fun (mkArr F G \<tau>) = \<tau>"
        using assms arr_char mkArr_def Fun_def Abs_arr_inverse
        by (metis UNIV_I fst_conv option.sel)

      lemma mkArr_Fun:
      assumes "arr t"
      shows "mkArr (Dom t) (Cod t) (Fun t) = t"
        using assms arr_char mkArr_def
        by (metis Cod_def Dom_def Fun_def Rep_arr_inverse null_char option.collapse prod.collapse)

      lemma seq_char:
      shows "seq g f \<longleftrightarrow> arr f \<and> arr g \<and> Cod f = Dom g"
      proof
        assume gf: "seq g f"
        have f: "arr f" using gf by auto
        moreover have g: "arr g" using gf by auto
        moreover have "Cod f = Dom g"
        proof -
          have "Cod f = Cod (dom g)"
            using f gf cod_char arr_cod_iff_arr [of f] by auto
          also have "... = Dom g"
            using g dom_char ide_dom Cod_mkArr by (metis arr_dom)
          finally show ?thesis by simp
        qed
        ultimately show "arr f \<and> arr g \<and> Cod f = Dom g" by blast
        next
        assume fg: "arr f \<and> arr g \<and> Cod f = Dom g"
        show "seq g f"
          using fg dom_char cod_char by auto
      qed

      lemma comp_char:
      shows "g \<cdot> f = (if seq g f then
                        mkArr (Dom f) (Cod g) (vertical_composite.map A B (Fun f) (Fun g))
                      else null)"
      proof -
        have "\<not>seq g f \<Longrightarrow> g \<cdot> f = null"
          using comp_def AC.comp_char ext by fastforce
        moreover have
          "seq g f \<Longrightarrow>
           g \<cdot> f = mkArr (Dom f) (Cod g) (vertical_composite.map A B (Fun f) (Fun g))"
        proof -
          assume gf: "seq g f"
          interpret Fun_f: natural_transformation A B "Dom f" "Cod f" "Fun f"
            using gf arr_char by blast
          interpret Fun_g: natural_transformation A B "Cod f" "Cod g" "Fun g"
            using gf arr_char seq_char by simp
          interpret Fun_goFun_f: vertical_composite A B "Dom f" "Cod f" "Cod g" "Fun f" "Fun g" ..
          show ?thesis
            using gf comp_def AC.comp_char seqI' CC.comp_def arr_char null_char
                  Dom_def Cod_def Fun_def mkArr_def Fun_goFun_f.natural_transformation_axioms
            by (metis (no_types, lifting) Comp'_def)
        qed
        ultimately show ?thesis by auto
      qed

      lemma comp_simp:
      assumes "seq t s"
      shows "t \<cdot> s = mkArr (Dom s) (Cod t) (vertical_composite.map A B (Fun s) (Fun t))"
        using assms comp_char seq_char by auto

      lemma ide_char [iff]:
      shows "ide t \<longleftrightarrow> t \<noteq> null \<and> functor A B (Fun t) \<and> Dom t = Fun t \<and> Cod t = Fun t"
      proof
        show "ide t \<Longrightarrow> t \<noteq> null \<and> functor A B (Fun t) \<and> Dom t = Fun t \<and> Cod t = Fun t"
        proof -
          assume t: "ide t"
          have 1: "t = mkIde (Dom t) \<and> t = mkIde (Cod t)"
            using t mkArr_Fun Cod_mkArr dom_simp cod_simp
            by (metis ideD(1) ideD(2))
          hence 2: "Dom t = Fun t \<and> Cod t = Fun t"
            using t 1 Fun_mkArr [of "Dom t" "Dom t" "Dom t"] Fun_mkArr [of "Cod t" "Cod t" "Cod t"]
            by auto
          have 3: "functor A B (Fun t)"
            using t 2 arr_char [of t] natural_transformation_def by force
          show "t \<noteq> null \<and> functor A B (Fun t) \<and> Dom t = Fun t \<and> Cod t = Fun t"
            using t 1 2 3 ideD(1) not_arr_null by blast
        qed
        show "t \<noteq> null \<and> functor A B (Fun t) \<and> Dom t = Fun t \<and> Cod t = Fun t \<Longrightarrow> ide t"
          using arr_char dom_simp mkArr_Fun [of t] ide_dom [of t] by simp
      qed

    end

  end

  sublocale functor_category \<subseteq> category comp
    using is_category by auto

  section "Additional Properties"

  text\<open>
    In this section some additional facts are proved, which make it easier to
    work with the @{term "functor_category"} locale.
\<close>

  context functor_category
  begin

    lemma ide_mkIde [simp]:
    assumes "functor A B F"
    shows "ide (mkIde F)"
      using assms
      by (metis Cod_mkArr Dom_mkArr Fun_mkArr arr_mkArr functor_is_transformation
                ide_char not_arr_null)

    lemma Dom_ide:
    assumes "ide a"
    shows "Dom a = Fun a"
      using assms Dom_def Fun_def ide_char by blast

    lemma Cod_ide:
    assumes "ide a"
    shows "Cod a = Fun a"
      using assms Cod_def Fun_def ide_char by blast

    lemma Dom_dom [simp]:
    assumes "arr f"
    shows "Dom (dom f) = Dom f"
      using assms dom_simp Dom_mkArr arr_dom_iff_arr by metis

    lemma Cod_dom [simp]:
    assumes "arr f"
    shows "Cod (dom f) = Dom f"
      using assms dom_simp Cod_mkArr arr_dom_iff_arr by metis

    lemma Dom_cod [simp]:
    assumes "arr f"
    shows "Dom (cod f) = Cod f"
      using assms cod_simp Dom_mkArr arr_cod_iff_arr by metis

    lemma Cod_cod [simp]:
    assumes "arr f"
    shows "Cod (cod f) = Cod f"
      using assms cod_simp Cod_mkArr arr_cod_iff_arr by metis

    lemma Fun_dom [simp]:
    assumes "arr t"
    shows "Fun (dom t) = Dom t"
      using assms ide_dom by auto

    lemma Fun_cod [simp]:
    assumes "arr t"
    shows "Fun (cod t) = Cod t"
      using assms ide_cod by auto

    lemma Fun_comp [simp]:
    assumes "seq t' t" and "A.seq a' a"
    shows "Fun (t' \<cdot> t) (a' \<cdot>\<^sub>A a) = Fun t' a' \<cdot>\<^sub>B Fun t a"
    proof -
      interpret t: natural_transformation A B "Dom t" "Cod t" "Fun t"
        using assms(1) arr_char seq_char by blast
      interpret t': natural_transformation A B "Cod t" "Cod t'" "Fun t'"
        using assms(1) arr_char seq_char by auto
      interpret t'ot: vertical_composite A B "Dom t" "Cod t" "Cod t'" "Fun t" "Fun t'" ..
      show ?thesis
      proof -
        have "Fun (t' \<cdot> t) = t'ot.map"
          using assms(1) seq_char comp_simp t'ot.natural_transformation_axioms by simp
        thus ?thesis
          using assms(2) t'ot.map_simp_2 t'.preserves_comp_2 B.comp_assoc by auto
      qed
    qed

    lemma arr_eqI:
    assumes "arr t" and "arr t'" and "Dom t = Dom t'" and "Cod t = Cod t'" and "Fun t = Fun t'"
    shows "t = t'"
      using assms mkArr_Fun by metis

    lemma mkArr_eqI [intro]:
    assumes "arr (mkArr F G \<tau>)"
    and "F = F'" and "G = G'" and "\<tau> = \<tau>'"
    shows "mkArr F G \<tau> = mkArr F' G' \<tau>'"
      using assms arr_eqI by simp

    lemma mkArr_eqI' [intro]:
    assumes "arr (mkArr F G \<tau>)" and "\<tau> = \<tau>'"
    shows "mkArr F G \<tau> = mkArr F G \<tau>'"
      using assms arr_eqI by simp

    lemma comp_mkArr [simp]:
    assumes "arr (mkArr F G \<sigma>)" and "arr (mkArr G H \<tau>)"
    shows "mkArr G H \<tau> \<cdot> mkArr F G \<sigma> = mkArr F H (vertical_composite.map A B \<sigma> \<tau>)"
      using assms mkArr_Fun dom_simp cod_simp comp_char seq_char by simp

    lemma mkArr_in_hom:
    assumes "natural_transformation A B F G \<tau>"
    shows "\<guillemotleft>mkArr F G \<tau> : mkIde F \<rightarrow> mkIde G\<guillemotright>"
      using assms dom_simp cod_simp by fastforce

    lemma iso_char [iff]:
    shows "iso t \<longleftrightarrow> t \<noteq> null \<and> natural_isomorphism A B (Dom t) (Cod t) (Fun t)"
    proof
      assume t: "iso t"
      show "t \<noteq> null \<and> natural_isomorphism A B (Dom t) (Cod t) (Fun t)"
      proof
        show "t \<noteq> null" using t arr_char iso_is_arr by auto
        from t obtain t' where t': "inverse_arrows t t'" by blast
        interpret \<tau>: natural_transformation A B "Dom t" "Cod t" "Fun t"
          using t arr_char iso_is_arr by auto
        interpret \<tau>': natural_transformation A B "Cod t" "Dom t" "Fun t'"
          using t' arr_char dom_char seq_char
          by (metis (no_types, lifting) comp_char ide_char inverse_arrowsE)
        interpret \<tau>'o\<tau>: vertical_composite A B "Dom t" "Cod t" "Dom t" "Fun t" "Fun t'" ..
        interpret \<tau>o\<tau>': vertical_composite A B "Cod t" "Dom t" "Cod t" "Fun t'" "Fun t" ..
        show "natural_isomorphism A B (Dom t) (Cod t) (Fun t)"
        proof
          fix a
          assume a: "A.ide a"
          show "B.iso (Fun t a)"
          proof
            have 1: "\<tau>'o\<tau>.map = Dom t \<and> \<tau>o\<tau>'.map = Cod t"
              using t t'
              by (metis Fun_cod Fun_mkArr comp_simp seq_char ide_compE inverse_arrowsE)
            show "B.inverse_arrows (Fun t a) (Fun t' a)"
              using a 1 \<tau>o\<tau>'.map_simp_ide \<tau>'o\<tau>.map_simp_ide \<tau>.F.preserves_ide \<tau>.G.preserves_ide
              by auto
          qed
        qed
      qed
      next
      assume t: "t \<noteq> null \<and> natural_isomorphism A B (Dom t) (Cod t) (Fun t)"
      show "iso t"
      proof
        interpret \<tau>: natural_isomorphism A B "Dom t" "Cod t" "Fun t"
          using t by auto
        interpret \<tau>': inverse_transformation A B "Dom t" "Cod t" "Fun t" ..
        have 1: "vertical_composite.map A B (Fun t) \<tau>'.map = Dom t \<and>
                 vertical_composite.map A B \<tau>'.map (Fun t) = Cod t"
          using \<tau>.natural_isomorphism_axioms vertical_composite_inverse_iso
                vertical_composite_iso_inverse
          by blast
        show "inverse_arrows t (mkArr (Cod t) (Dom t) (\<tau>'.map))"
        proof
          show "ide (mkArr (Cod t) (Dom t) \<tau>'.map \<cdot> t)"
            using t 1
            by (metis \<tau>'.natural_transformation_axioms \<tau>.F.functor_axioms
                      \<tau>.natural_transformation_axioms arr_mkArr arrI
                      comp_mkArr ide_mkIde mkArr_Fun)
          show "ide (t \<cdot> mkArr (Cod t) (Dom t) \<tau>'.map)"
            using t 1
            by (metis \<tau>'.natural_transformation_axioms \<tau>.G.functor_axioms
                      \<tau>.natural_transformation_axioms arr_mkArr arrI
                      comp_mkArr ide_mkIde mkArr_Fun)
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
    where "map Fg \<equiv> if A_BxA.arr Fg then A_B.Fun (fst Fg) (snd Fg) else B.null"

    lemma map_simp:
    assumes "A_BxA.arr Fg"
    shows "map Fg = A_B.Fun (fst Fg) (snd Fg)"
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
      have DomF: "A_B.Dom ?F = A_B.Fun (A_B.dom ?F)" using F A_B.Fun_dom by simp
      have CodF: "A_B.Cod ?F = A_B.Fun (A_B.cod ?F)" using F A_B.Fun_cod by simp
      interpret F: natural_transformation A B "A_B.Dom ?F" "A_B.Cod ?F" "A_B.Fun ?F"
        using Fg A_B.arr_char [of ?F] by blast
      show "B.arr (map Fg)" using Fg map_def by auto
      show "B.dom (map Fg) = map (A_BxA.dom Fg)"
        using Fg map_def DomF
        by (metis A_BxA.arr_dom_iff_arr A_BxA.dom_simp F.preserves_dom fst_conv g snd_conv)
      show "B.cod (map Fg) = map (A_BxA.cod Fg)"
        using Fg map_def CodF
       by (metis A_BxA.arr_cod_iff_arr A_BxA.cod_simp F.preserves_cod fst_conv g snd_conv)
      next
      fix Fg Fg'
      assume 1: "A_BxA.seq Fg' Fg"
      let ?F = "fst Fg" and ?g = "snd Fg"
      let ?F' = "fst Fg'" and ?g' = "snd Fg'"
      have F': "A_B.arr ?F'" using 1 A_BxA.seqE by blast
      have CodF: "A_B.Cod ?F = A_B.Fun (A_B.cod ?F)"
        using 1 A_B.Fun_cod by fastforce
      have DomF': "A_B.Dom ?F' = A_B.Fun (A_B.dom ?F')"
        using F' A_B.Fun_dom by simp
      have seq_F'F: "A_B.seq ?F' ?F" using 1 by blast
      have seq_g'g: "A.seq ?g' ?g" using 1 by blast
      interpret F: natural_transformation A B "A_B.Dom ?F" "A_B.Cod ?F" "A_B.Fun ?F"
        using 1 A_B.arr_char by blast
      interpret F': natural_transformation A B "A_B.Cod ?F" "A_B.Cod ?F'" "A_B.Fun ?F'"
        using 1 seq_F'F CodF DomF' A_B.arr_char A_B.seqE by metis
      interpret F'oF: vertical_composite A B "A_B.Dom ?F" "A_B.Cod ?F" "A_B.Cod ?F'"
                                             "A_B.Fun ?F" "A_B.Fun ?F'" ..
      show "map (Fg' \<cdot>\<^sub>[\<^sub>A\<^sub>,\<^sub>B\<^sub>]\<^sub>x\<^sub>A Fg) = map Fg' \<cdot>\<^sub>B map Fg"
        unfolding map_def A_B.Fun_def
        using 1 seq_F'F seq_g'g A_B.Fun_comp A_B.Fun_def A_BxA.comp_def
        by (elim A_B.seqE, auto)
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
                               A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                          (\<lambda>f2. \<tau> (f1, f2))
                             else A2_B.null)"

    definition uncurry :: "('a1 \<Rightarrow> ('a2, 'b) A2_B.arr) \<Rightarrow> 'a1 \<times> 'a2 \<Rightarrow> 'b"
    where "uncurry \<tau> f \<equiv> if A1xA2.arr f then E.map (\<tau> (fst f), snd f) else B.null"

    lemma curry_simp:
    assumes "A1.arr f1"
    shows "curry F G \<tau> f1 = A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
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
        interpret F_dom_f1: "functor" A2 B "\<lambda>f2. F (A1.dom f1, f2)"
          using f1 \<tau>.F.is_extensional apply (unfold_locales, simp_all)
          by (metis A1xA2.comp_char A1.arr_dom_iff_arr A1.comp_arr_dom A1.dom_dom
                    A1xA2.seqI \<tau>.F.preserves_comp_2 fst_conv snd_conv)
        interpret G_cod_f1: "functor" A2 B "\<lambda>f2. G (A1.cod f1, f2)"
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
          using f1 A2_B.arr_mkArr A2_B.dom_simp A2_B.cod_simp curry_simp
                A1.arr_dom_iff_arr A1.arr_cod_iff_arr
          by auto
      qed
    qed

    lemma curry_preserves_functors:
    assumes "functor A1xA2.comp B F"
    shows "functor A1 A2_B.comp (curry F F F)"
    proof -
      interpret F: "functor" A1xA2.comp B F using assms by auto
      interpret F: binary_functor A1 A2 B F ..
      show ?thesis
        using curry_def F.fixing_arr_gives_natural_transformation_1 A2_B.dom_simp A2_B.cod_simp
              A2_B.comp_char F.preserves_comp_1 curry_simp A2_B.comp_simp A2_B.seq_char
              A1.arr_cod_iff_arr
        apply unfold_locales by auto
    qed

    lemma curry_preserves_transformations:
    assumes "natural_transformation A1xA2.comp B F G \<tau>"
    shows "natural_transformation A1 A2_B.comp (curry F F F) (curry G G G) (curry F G \<tau>)"
    proof -
      interpret \<tau>: natural_transformation A1xA2.comp B F G \<tau> using assms by auto
      interpret \<tau>: binary_functor_transformation A1 A2 B F G \<tau> ..
      interpret curry_F: "functor" A1 A2_B.comp "curry F F F"
        using curry_preserves_functors \<tau>.F.functor_axioms by simp
      interpret curry_G: "functor" A1 A2_B.comp "curry G G G"
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
          interpret \<tau>_dom_f1: natural_transformation A2 B "\<lambda>f2. F (A1.dom f1, f2)"
                                "\<lambda>f2. G (A1.dom f1, f2)" "\<lambda>f2. \<tau> (A1.dom f1, f2)"
            using assms f1 curry_in_hom A2_B.arr_mkArr A1.ide_dom
                  \<tau>.fixing_ide_gives_natural_transformation_1
            by blast
          interpret G_f1: natural_transformation A2 B
                                "\<lambda>f2. G (A1.dom f1, f2)" "\<lambda>f2. G (A1.cod f1, f2)" "\<lambda>f2. G (f1, f2)"
            using f1 \<tau>.G.fixing_arr_gives_natural_transformation_1 by simp
          interpret G_f1o\<tau>_dom_f1: vertical_composite A2 B
                                     "\<lambda>f2. F (A1.dom f1, f2)" "\<lambda>f2. G (A1.dom f1, f2)"
                                     "\<lambda>f2. G (A1.cod f1, f2)"
                                     "\<lambda>f2. \<tau> (A1.dom f1, f2)" "\<lambda>f2. G (f1, f2)" ..
          have "curry G G G f1 \<cdot>\<^sub>[\<^sub>A\<^sub>2,\<^sub>B\<^sub>] curry F G \<tau> (A1.dom f1)
                  = A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2)) G_f1o\<tau>_dom_f1.map"
          proof -
            have "A2_B.seq (curry G G G f1) (curry F G \<tau> (A1.dom f1))"
              using f1 curry_in_hom [of "A1.dom f1"] \<tau>.natural_transformation_axioms by force
            thus ?thesis
              using curry_simp A2_B.comp_simp [of "curry G G G f1" "curry F G \<tau> (A1.dom f1)"]
              by (metis A1.arr_dom_iff_arr A1.dom_dom A2_B.Cod_mkArr A2_B.Dom_mkArr
                        A2_B.Fun_mkArr A2_B.seqE f1)
          qed
          also have "... = A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                      (\<lambda>f2. \<tau> (f1, f2))"
          proof (intro A2_B.mkArr_eqI)
            show "(\<lambda>f2. F (A1.dom f1, f2)) = (\<lambda>f2. F (A1.dom f1, f2))" by simp
            show "(\<lambda>f2. G (A1.cod f1, f2)) = (\<lambda>f2. G (A1.cod f1, f2))" by simp
            show "A2_B.arr (A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                       G_f1o\<tau>_dom_f1.map)"
              using A2_B.arr_mkArr G_f1o\<tau>_dom_f1.natural_transformation_axioms by blast
            show "G_f1o\<tau>_dom_f1.map = (\<lambda>f2. \<tau> (f1, f2))"
            proof
              fix f2
              have "\<not>A2.arr f2 \<Longrightarrow> G_f1o\<tau>_dom_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
                using f1 G_f1o\<tau>_dom_f1.is_extensional \<tau>.is_extensional by simp
              moreover have "A2.arr f2 \<Longrightarrow> G_f1o\<tau>_dom_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
              proof -
                interpret \<tau>_f1: natural_transformation A2 B "\<lambda>f2. F (A1.dom f1, f2)"
                                  "\<lambda>f2. G (A1.cod f1, f2)" "\<lambda>f2. \<tau> (f1, f2)"
                  using assms f1 curry_in_hom [of f1] A2_B.arr_mkArr curry_simp by auto
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
          interpret \<tau>_cod_f1: natural_transformation A2 B "\<lambda>f2. F (A1.cod f1, f2)"
                                "\<lambda>f2. G (A1.cod f1, f2)" "\<lambda>f2. \<tau> (A1.cod f1, f2)"
            using assms f1 curry_in_hom A2_B.arr_mkArr A1.ide_cod
                  \<tau>.fixing_ide_gives_natural_transformation_1
            by blast
          interpret F_f1: natural_transformation A2 B
                                "\<lambda>f2. F (A1.dom f1, f2)" "\<lambda>f2. F (A1.cod f1, f2)" "\<lambda>f2. F (f1, f2)"
            using f1 \<tau>.F.fixing_arr_gives_natural_transformation_1 by simp
          interpret \<tau>_cod_f1oF_f1: vertical_composite A2 B
                                     "\<lambda>f2. F (A1.dom f1, f2)" "\<lambda>f2. F (A1.cod f1, f2)"
                                     "\<lambda>f2. G (A1.cod f1, f2)"
                                     "\<lambda>f2. F (f1, f2)" "\<lambda>f2. \<tau> (A1.cod f1, f2)" ..
          have "curry F G \<tau> (A1.cod f1) \<cdot>\<^sub>[\<^sub>A\<^sub>2,\<^sub>B\<^sub>] curry F F F f1
                  = A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2)) \<tau>_cod_f1oF_f1.map"
          proof -
            have
                 "curry F F F f1 =
                    A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. F (A1.cod f1, f2))
                                       (\<lambda>f2. F (f1, f2)) \<and>
                  \<guillemotleft>curry F F F f1 : curry F F F (A1.dom f1) \<rightarrow>\<^sub>[\<^sub>A\<^sub>2\<^sub>,\<^sub>B\<^sub>] curry F F F (A1.cod f1)\<guillemotright>"
              using f1 curry_F.preserves_hom curry_simp by blast
            moreover have
                 "curry F G \<tau> (A1.dom f1) =
                    A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.dom f1, f2))
                               (\<lambda>f2. \<tau> (A1.dom f1, f2)) \<and>
                    \<guillemotleft>curry F G \<tau> (A1.cod f1) :
                       curry F F F (A1.cod f1) \<rightarrow>\<^sub>[\<^sub>A\<^sub>2\<^sub>,\<^sub>B\<^sub>] curry G G G (A1.cod f1)\<guillemotright>"
              using assms f1 curry_in_hom [of "A1.cod f1"] curry_def A1.arr_cod_iff_arr by simp
            ultimately show ?thesis
              using f1 curry_def A2_B.comp_mkArr by fastforce
          qed
          also have "... = A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                      (\<lambda>f2. \<tau> (f1, f2))"
          proof (intro A2_B.mkArr_eqI)
            show "(\<lambda>f2. F (A1.dom f1, f2)) = (\<lambda>f2. F (A1.dom f1, f2))" by simp
            show "(\<lambda>f2. G (A1.cod f1, f2)) = (\<lambda>f2. G (A1.cod f1, f2))" by simp
            show "A2_B.arr (A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. G (A1.cod f1, f2))
                                       \<tau>_cod_f1oF_f1.map)"
              using A2_B.arr_mkArr \<tau>_cod_f1oF_f1.natural_transformation_axioms by blast
            show "\<tau>_cod_f1oF_f1.map = (\<lambda>f2. \<tau> (f1, f2))"
            proof
              fix f2
              have "\<not>A2.arr f2 \<Longrightarrow> \<tau>_cod_f1oF_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
                using f1 by (simp add: \<tau>.is_extensional \<tau>_cod_f1oF_f1.is_extensional)
              moreover have "A2.arr f2 \<Longrightarrow> \<tau>_cod_f1oF_f1.map f2 = (\<lambda>f2. \<tau> (f1, f2)) f2"
              proof -
                interpret \<tau>_f1: natural_transformation A2 B "\<lambda>f2. F (A1.dom f1, f2)"
                                  "\<lambda>f2. G (A1.cod f1, f2)" "\<lambda>f2. \<tau> (f1, f2)"
                  using assms f1 curry_in_hom [of f1] A2_B.arr_mkArr curry_simp by auto
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
        interpret Ff1: natural_transformation A2 B "A2_B.Dom (F ?f1)" "A2_B.Cod (F ?f1)"
                                                   "A2_B.Fun (F ?f1)"
          using f A2_B.arr_char [of "F ?f1"] by auto
        interpret Fg1: natural_transformation A2 B "A2_B.Cod (F ?f1)" "A2_B.Cod (F ?g1)"
                                                    "A2_B.Fun (F ?g1)"
          using f1 g1 A2_B.arr_char F.preserves_arr
                A2_B.Fun_dom [of "F ?g1"] A2_B.Fun_cod [of "F ?f1"]
          by fastforce
        interpret Fg1oFf1: vertical_composite A2 B
                              "A2_B.Dom (F ?f1)" "A2_B.Cod (F ?f1)" "A2_B.Cod (F ?g1)"
                              "A2_B.Fun (F ?f1)" "A2_B.Fun (F ?g1)" ..
        show "uncurry F (g \<cdot>\<^sub>A\<^sub>1\<^sub>x\<^sub>A\<^sub>2 f) = uncurry F g \<cdot>\<^sub>B uncurry F f"
          using f1 g1 g2 g2 f g fg E.map_simp uncurry_def by auto
      qed
    qed

    lemma uncurry_preserves_transformations:
    assumes "natural_transformation A1 A2_B.comp F G \<tau>"
    shows "natural_transformation A1xA2.comp B (uncurry F) (uncurry G) (uncurry \<tau>)"
    proof -
      interpret \<tau>: natural_transformation A1 A2_B.comp F G \<tau> using assms by auto
      interpret "functor" A1xA2.comp B "uncurry F"
        using \<tau>.F.functor_axioms uncurry_preserves_functors by blast
      interpret "functor" A1xA2.comp B "uncurry G"
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
            using f 1 2 uncurry_def \<tau>.is_natural_2 [of ?f1] A1xA2.cod_simp A2.seqE
                  A1xA2.arr_cod_iff_arr A2_BxA2.comp_char
            by (metis (no_types) A2_BxA2.seqI E.preserves_comp fst_conv)
        qed
      qed
    qed

    lemma uncurry_curry:
    assumes "natural_transformation A1xA2.comp B F G \<tau>"
    shows "uncurry (curry F G \<tau>) = \<tau>"
    proof
      interpret \<tau>: natural_transformation A1xA2.comp B F G \<tau> using assms by auto
      interpret curry_\<tau>: natural_transformation A1 A2_B.comp "curry F F F" "curry G G G"
                                                             "curry F G \<tau>"
        using assms curry_preserves_transformations by auto
      fix f
      have "\<not>A1xA2.arr f \<Longrightarrow> uncurry (curry F G \<tau>) f = \<tau> f"
        using curry_def uncurry_def \<tau>.is_extensional by auto
      moreover have "A1xA2.arr f \<Longrightarrow> uncurry (curry F G \<tau>) f = \<tau> f"
        unfolding uncurry_def using A1xA2.arr_char E.map_simp
        by (metis A2_B.Fun_mkArr A2_BxA2.arr_char curry_\<tau>.preserves_reflects_arr fst_conv
            curry_def prod.collapse snd_conv)
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
      interpret uncurry_F: "functor" A1xA2.comp B "uncurry F"
        using F.functor_axioms uncurry_preserves_functors by auto
      interpret uncurry_G: "functor" A1xA2.comp B "uncurry G"
        using G.functor_axioms uncurry_preserves_functors by auto
      fix f1
      have "\<not>A1.arr f1 \<Longrightarrow> curry (uncurry F) (uncurry G) (uncurry \<tau>) f1 = \<tau> f1"
        using curry_def uncurry_def \<tau>.is_extensional by simp
      moreover have "A1.arr f1 \<Longrightarrow> curry (uncurry F) (uncurry G) (uncurry \<tau>) f1 = \<tau> f1"
      proof -
        assume f1: "A1.arr f1"
        interpret uncurry_\<tau>:
            natural_transformation A1xA2.comp B "uncurry F" "uncurry G" "uncurry \<tau>"
          using \<tau>.natural_transformation_axioms uncurry_preserves_transformations [of F G \<tau>]
          by simp
        have "curry (uncurry F) (uncurry G) (uncurry \<tau>) f1 =
                A2_B.mkArr (\<lambda>f2. uncurry F (A1.dom f1, f2)) (\<lambda>f2. uncurry G (A1.cod f1, f2))
                           (\<lambda>f2. uncurry \<tau> (f1, f2))"
          using f1 curry_def by simp
        also have "... = A2_B.mkArr (\<lambda>f2. uncurry F (A1.dom f1, f2))
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
            have "A2_B.Dom (\<tau> f1) = A2_B.Fun (A2_B.dom (\<tau> f1))"
              using f1 A2_B.ide_char A2_B.Fun_dom A2_B.dom_simp by auto
            also have "... = A2_B.Fun (F (A1.dom f1))"
              using f1 by simp
            also have "... = (\<lambda>f2. uncurry F (A1.dom f1, f2))"
            proof
              fix f2
              interpret F_dom_f1: "functor" A2 B "A2_B.Fun (F (A1.dom f1))"
                using f1 A2_B.ide_char F.preserves_ide by simp
              show "A2_B.Fun (F (A1.dom f1)) f2 = uncurry F (A1.dom f1, f2)"
                using f1 uncurry_def E.map_simp F_dom_f1.is_extensional by auto
            qed
            finally show ?thesis by auto
          qed
          moreover have "A2_B.Cod (\<tau> f1) = (\<lambda>f2. uncurry G (A1.cod f1, f2))"
          proof -
            have "A2_B.Cod (\<tau> f1) = A2_B.Fun (A2_B.cod (\<tau> f1))"
              using f1 A2_B.ide_char A2_B.Fun_cod A2_B.cod_simp by auto
            also have "... = A2_B.Fun (G (A1.cod f1))"
              using f1 by simp
            also have "... = (\<lambda>f2. uncurry G (A1.cod f1, f2))"
            proof
              fix f2
              interpret G_cod_f1: "functor" A2 B "A2_B.Fun (G (A1.cod f1))"
                using f1 A2_B.ide_char G.preserves_ide by simp
              show "A2_B.Fun (G (A1.cod f1)) f2 = uncurry G (A1.cod f1, f2)"
                using f1 uncurry_def E.map_simp G_cod_f1.is_extensional by auto
            qed
            finally show ?thesis by auto
          qed
          moreover have "A2_B.Fun (\<tau> f1) = (\<lambda>f2. E.map (\<tau> f1, f2))"
          proof
            fix f2
            have "\<not>A2.arr f2 \<Longrightarrow> A2_B.Fun (\<tau> f1) f2 = (\<lambda>f2. E.map (\<tau> f1, f2)) f2"
              using f1 E.is_extensional A2_B.arr_char \<tau>.preserves_reflects_arr
                    natural_transformation.is_extensional E.map_def
              by (metis (no_types, lifting) prod.sel(1) prod.sel(2))
            moreover have "A2.arr f2 \<Longrightarrow> A2_B.Fun (\<tau> f1) f2 = (\<lambda>f2. E.map (\<tau> f1, f2)) f2"
              using f1 E.map_simp by fastforce
            ultimately show "A2_B.Fun (\<tau> f1) f2 = (\<lambda>f2. E.map (\<tau> f1, f2)) f2" by blast
          qed
          ultimately show ?thesis
            using A2_B.mkArr_Fun f1 \<tau>.preserves_reflects_arr by metis
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
           A2_B.mkArr (\<lambda>f2. F (A1.dom f1, f2)) (\<lambda>f2. F (A1.cod f1, f2)) (\<lambda>f2. F (f1, f2))"
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
           A1_B.mkArr (\<lambda>f1. F (f1, A2.dom f2)) (\<lambda>f1. F (f1, A2.cod f2)) (\<lambda>f1. F (f1, f2))"
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

