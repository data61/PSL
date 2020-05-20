(*  Title:       Bicategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

theory Bicategory
imports Prebicategory Category3.Subcategory Category3.DiscreteCategory
        MonoidalCategory.MonoidalCategory
begin

  section "Bicategories"

  text \<open>
    A \emph{bicategory} is a (vertical) category that has been equipped with
    a horizontal composition, an associativity natural isomorphism,
    and for each object a ``unit isomorphism'', such that horizontal
    composition on the left by target and on the right by source are
    fully faithful endofunctors of the vertical category, and such that
    the usual pentagon coherence condition holds for the associativity.
  \<close>

  locale bicategory =
    horizontal_composition V H src trg +
    VxVxV: product_category V VxV.comp +
    VVV: subcategory VxVxV.comp \<open>\<lambda>\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> VV.arr (snd \<tau>\<mu>\<nu>) \<and>
                                       src (fst \<tau>\<mu>\<nu>) = trg (fst (snd \<tau>\<mu>\<nu>))\<close> +
    HoHV: "functor" VVV.comp V HoHV +
    HoVH: "functor" VVV.comp V HoVH +
    \<alpha>: natural_isomorphism VVV.comp V HoHV HoVH
         \<open>\<lambda>\<mu>\<nu>\<tau>. \<a> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>))\<close> +
    L: fully_faithful_functor V V L +
    R: fully_faithful_functor V V R
  for V :: "'a comp"                 (infixr "\<cdot>" 55)
  and H :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"          (infixr "\<star>" 53)
  and \<a> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"     ("\<a>[_, _, _]")
  and \<i> :: "'a \<Rightarrow> 'a"                 ("\<i>[_]")
  and src :: "'a \<Rightarrow> 'a"
  and trg :: "'a \<Rightarrow> 'a" +
  assumes unit_in_vhom: "obj a \<Longrightarrow> \<guillemotleft>\<i>[a] : a \<star> a \<Rightarrow> a\<guillemotright>"
  and iso_unit: "obj a \<Longrightarrow> iso \<i>[a]"
  and pentagon: "\<lbrakk> ide f; ide g; ide h; ide k; src f = trg g; src g = trg h; src h = trg k \<rbrakk> \<Longrightarrow>
                   (f \<star> \<a> g h k) \<cdot> \<a> f (g \<star> h) k \<cdot> (\<a> f g h \<star> k) = \<a> f g (h \<star> k) \<cdot> \<a> (f \<star> g) h k"
  begin
    (*
     * TODO: the mapping \<i> is not currently assumed to be extensional.
     * It might be best in the long run if it were.
     *)

    definition \<alpha>
    where "\<alpha> \<mu>\<nu>\<tau> \<equiv> \<a> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>))"

    lemma assoc_in_hom':
    assumes "arr \<mu>" and "arr \<nu>" and "arr \<tau>" and "src \<mu> = trg \<nu>" and "src \<nu> = trg \<tau>"
    shows "in_hhom \<a>[\<mu>, \<nu>, \<tau>] (src \<tau>) (trg \<mu>)"
    and "\<guillemotleft>\<a>[\<mu>, \<nu>, \<tau>] : (dom \<mu> \<star> dom \<nu>) \<star> dom \<tau> \<Rightarrow> cod \<mu> \<star> cod \<nu> \<star> cod \<tau>\<guillemotright>"
    proof -
      show "\<guillemotleft>\<a>[\<mu>, \<nu>, \<tau>] : (dom \<mu> \<star> dom \<nu>) \<star> dom \<tau> \<Rightarrow> cod \<mu> \<star> cod \<nu> \<star> cod \<tau>\<guillemotright>"
      proof -
        have 1: "VVV.in_hom (\<mu>, \<nu>, \<tau>) (dom \<mu>, dom \<nu>, dom \<tau>) (cod \<mu>, cod \<nu>, cod \<tau>)"
          using assms VVV.in_hom_char VVV.arr_char VV.arr_char by auto
        have "\<guillemotleft>\<a>[\<mu>, \<nu>, \<tau>] : HoHV (dom \<mu>, dom \<nu>, dom \<tau>) \<Rightarrow> HoVH (cod \<mu>, cod \<nu>, cod \<tau>)\<guillemotright>"
          using 1 \<alpha>.preserves_hom by auto
        moreover have "HoHV (dom \<mu>, dom \<nu>, dom \<tau>) = (dom \<mu> \<star> dom \<nu>) \<star> dom \<tau>"
          using 1 HoHV_def by (simp add: VVV.in_hom_char)
        moreover have "HoVH (cod \<mu>, cod \<nu>, cod \<tau>) = cod \<mu> \<star> cod \<nu> \<star> cod \<tau>"
          using 1 HoVH_def by (simp add: VVV.in_hom_char)
        ultimately show ?thesis by simp
      qed
      thus "in_hhom \<a>[\<mu>, \<nu>, \<tau>] (src \<tau>) (trg \<mu>)"
        using assms src_cod trg_cod vconn_implies_hpar(1) vconn_implies_hpar(2) by auto
    qed

    lemma assoc_is_natural_1:
    assumes "arr \<mu>" and "arr \<nu>" and "arr \<tau>" and "src \<mu> = trg \<nu>" and "src \<nu> = trg \<tau>"
    shows "\<a>[\<mu>, \<nu>, \<tau>] = (\<mu> \<star> \<nu> \<star> \<tau>) \<cdot> \<a>[dom \<mu>, dom \<nu>, dom \<tau>]"
      using assms \<alpha>.is_natural_1 [of "(\<mu>, \<nu>, \<tau>)"] VVV.arr_char VV.arr_char VVV.dom_char
            HoVH_def src_dom trg_dom
      by simp

    lemma assoc_is_natural_2:
    assumes "arr \<mu>" and "arr \<nu>" and "arr \<tau>" and "src \<mu> = trg \<nu>" and "src \<nu> = trg \<tau>"
    shows "\<a>[\<mu>, \<nu>, \<tau>] = \<a>[cod \<mu>, cod \<nu>, cod \<tau>] \<cdot> ((\<mu> \<star> \<nu>) \<star> \<tau>)"
      using assms \<alpha>.is_natural_2 [of "(\<mu>, \<nu>, \<tau>)"] VVV.arr_char VV.arr_char VVV.cod_char
            HoHV_def src_dom trg_dom
      by simp

    lemma assoc_naturality:
    assumes "arr \<mu>" and "arr \<nu>" and "arr \<tau>" and "src \<mu> = trg \<nu>" and "src \<nu> = trg \<tau>"
    shows "\<a>[cod \<mu>, cod \<nu>, cod \<tau>] \<cdot> ((\<mu> \<star> \<nu>) \<star> \<tau>) = (\<mu> \<star> \<nu> \<star> \<tau>) \<cdot> \<a>[dom \<mu>, dom \<nu>, dom \<tau>]"
      using assms \<alpha>.naturality VVV.arr_char VV.arr_char HoVH_def HoHV_def
            VVV.dom_char VVV.cod_char
      by auto

    lemma assoc_in_hom [intro]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "in_hhom \<a>[f, g, h] (src h) (trg f)"
    and "\<guillemotleft>\<a>[f, g, h] : (dom f \<star> dom g) \<star> dom h \<Rightarrow> cod f \<star> cod g \<star> cod h\<guillemotright>"
      using assms assoc_in_hom' apply auto[1]
      using assms assoc_in_hom' ideD(1) by metis

    lemma assoc_simps [simp]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "arr \<a>[f, g, h]"
    and "src \<a>[f, g, h] = src h" and "trg \<a>[f, g, h] = trg f"
    and "dom \<a>[f, g, h] = (dom f \<star> dom g) \<star> dom h"
    and "cod \<a>[f, g, h] = cod f \<star> cod g \<star> cod h"
      using assms assoc_in_hom apply auto
      using assoc_in_hom(1) by auto

    lemma iso_assoc [intro, simp]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "iso \<a>[f, g, h]"
      using assms \<alpha>.components_are_iso [of "(f, g, h)"] VVV.ide_char VVV.arr_char VV.arr_char
      by simp

  end

  subsection "Categories Induce Bicategories"

  text \<open>
    In this section we show that a category becomes a bicategory if we take the vertical
    composition to be discrete, we take the composition of the category as the
    horizontal composition, and we take the vertical domain and codomain as \<open>src\<close> and \<open>trg\<close>.
  \<close>

  (*
   * It is helpful to make a few local definitions here, but I don't want them to
   * clutter the category locale.  Using a context and private definitions does not
   * work as expected.  So we have to define a new locale just for the present purpose.
   *)
  locale category_as_bicategory = category
  begin

    interpretation V: discrete_category \<open>Collect arr\<close> null
      using not_arr_null by (unfold_locales, blast)

    abbreviation V
    where "V \<equiv> V.comp"

    interpretation src: "functor" V V dom
      using V.null_char
      by (unfold_locales, simp add: has_domain_iff_arr dom_def, auto)
    interpretation trg: "functor" V V cod
      using V.null_char
      by (unfold_locales, simp add: has_codomain_iff_arr cod_def, auto)

    interpretation H: horizontal_homs V dom cod
      by (unfold_locales, auto)

    interpretation VxV: product_category V V ..
    interpretation VV: subcategory VxV.comp
                          \<open>\<lambda>\<mu>\<nu>. V.arr (fst \<mu>\<nu>) \<and> V.arr (snd \<mu>\<nu>) \<and> dom (fst \<mu>\<nu>) = cod (snd \<mu>\<nu>)\<close>
      using H.subcategory_VV by auto
    interpretation VxVxV: product_category V VxV.comp ..
    interpretation VVV: subcategory VxVxV.comp \<open>\<lambda>\<tau>\<mu>\<nu>. V.arr (fst \<tau>\<mu>\<nu>) \<and>
                          VV.arr (snd \<tau>\<mu>\<nu>) \<and> dom (fst \<tau>\<mu>\<nu>) = cod (fst (snd \<tau>\<mu>\<nu>))\<close>
      using H.subcategory_VVV by auto

    interpretation H: "functor" VV.comp V \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<cdot> snd \<mu>\<nu>\<close>
      apply (unfold_locales)
      using VV.arr_char V.null_char ext
          apply force
      using VV.arr_char V.null_char VV.dom_char VV.cod_char
         apply auto[3]
    proof -
      show "\<And>g f. VV.seq g f \<Longrightarrow>
                   fst (VV.comp g f) \<cdot> snd (VV.comp g f) = V (fst g \<cdot> snd g) (fst f \<cdot> snd f)"
      proof -
        have 0: "\<And>f. VV.arr f \<Longrightarrow> V.arr (fst f \<cdot> snd f)"
          using VV.arr_char by auto
        have 1: "\<And>f g. V.seq g f \<Longrightarrow> V.ide f \<and> g = f"
          using V.arr_char V.dom_char V.cod_char V.not_arr_null by force
        have 2: "\<And>f g. VxV.seq g f \<Longrightarrow> VxV.ide f \<and> g = f"
          using 1 VxV.seq_char by (metis VxV.dom_eqI VxV.ide_Ide)
        fix f g
        assume fg: "VV.seq g f"
        have 3: "VV.ide f \<and> f = g"
          using fg 2 VV.seq_char VV.ide_char by blast
        show "fst (VV.comp g f) \<cdot> snd (VV.comp g f) = V (fst g \<cdot> snd g) (fst f \<cdot> snd f)"
          using fg 0 1 3 VV.comp_char VV.arr_char VV.ide_char V.arr_char V.comp_char
                VV.comp_arr_ide
          by (metis (no_types, lifting))
      qed
    qed

    interpretation H: horizontal_composition V C dom cod
      by (unfold_locales, auto)

    interpretation H.HoHV: "functor" VVV.comp V H.HoHV
      using H.functor_HoHV by blast
    interpretation H.HoVH: "functor" VVV.comp V H.HoVH
      using H.functor_HoVH by blast

    abbreviation \<a>
    where "\<a> f g h \<equiv> f \<cdot> g \<cdot> h"

    interpretation \<alpha>: natural_isomorphism VVV.comp V H.HoHV H.HoVH
                        \<open>\<lambda>\<mu>\<nu>\<tau>. \<a> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>))\<close>
      apply unfold_locales
      using V.null_char ext
           apply fastforce
      using H.HoHV_def H.HoVH_def VVV.arr_char VV.arr_char VVV.dom_char VV.dom_char
            VVV.cod_char VV.cod_char VVV.ide_char comp_assoc
      by auto

    interpretation endofunctor V H.L
        using H.endofunctor_L by auto
    interpretation endofunctor V H.R
      using H.endofunctor_R by auto

    interpretation fully_faithful_functor V V H.R
      using comp_arr_dom by (unfold_locales, auto)
    interpretation fully_faithful_functor V V H.L
      using comp_cod_arr by (unfold_locales, auto)

    abbreviation \<i>
    where "\<i> \<equiv> \<lambda>x. x"

    proposition induces_bicategory:
    shows "bicategory V C \<a> \<i> dom cod"
      apply (unfold_locales, auto simp add: comp_assoc)
      using comp_arr_dom by fastforce

  end

  subsection "Monoidal Categories induce Bicategories"

  text \<open>
    In this section we show that our definition of bicategory directly generalizes our
    definition of monoidal category:
    a monoidal category becomes a bicategory when equipped with the constant-\<open>\<I>\<close> functors
    as src and trg and \<open>\<iota>\<close> as the unit isomorphism from \<open>\<I> \<otimes> \<I>\<close> to \<open>\<I>\<close>.
    There is a slight mismatch because the bicategory locale assumes that the associator
    is given in curried form, whereas for monoidal categories it is given in tupled form.
    Ultimately, the monoidal category locale should be revised to also use curried form,
    which ends up being more convenient in most situations.
  \<close>

  context monoidal_category
  begin

    interpretation I: constant_functor C C \<I>
      using \<iota>_in_hom by unfold_locales auto
    interpretation HH: horizontal_homs C I.map I.map
      by unfold_locales auto
    interpretation CC': subcategory CC.comp \<open>\<lambda>\<mu>\<nu>. arr (fst \<mu>\<nu>) \<and> arr (snd \<mu>\<nu>) \<and>
                                                  I.map (fst \<mu>\<nu>) = I.map (snd \<mu>\<nu>)\<close>
      using HH.subcategory_VV by auto
    interpretation CCC': subcategory CCC.comp \<open>\<lambda>\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> CC'.arr (snd \<tau>\<mu>\<nu>) \<and>
                                                     I.map (fst \<tau>\<mu>\<nu>) = I.map (fst (snd \<tau>\<mu>\<nu>))\<close>
      using HH.subcategory_VVV by simp

    lemma CC'_eq_CC:
    shows "CC.comp = CC'.comp"
    proof -
      have "\<And>g f. CC.comp g f = CC'.comp g f"
      proof -
        fix f g
        show "CC.comp g f = CC'.comp g f"
        proof -
          have "CC.seq g f \<Longrightarrow> CC.comp g f = CC'.comp g f"
            using CC'.comp_char CC'.arr_char CC.seq_char
            by (elim CC.seqE seqE, simp)
          moreover have "\<not> CC.seq g f \<Longrightarrow> CC.comp g f = CC'.comp g f"
            using CC'.seq_char CC'.ext CC'.null_char CC.ext
            by (metis (no_types, lifting))
          ultimately show ?thesis by blast
        qed
      qed
      thus ?thesis by blast
    qed

    lemma CCC'_eq_CCC:
    shows "CCC.comp = CCC'.comp"
    proof -
      have "\<And>g f. CCC.comp g f = CCC'.comp g f"
      proof -
        fix f g
        show "CCC.comp g f = CCC'.comp g f"
        proof -
          have "CCC.seq g f \<Longrightarrow> CCC.comp g f = CCC'.comp g f"
            using CCC'.comp_char CCC'.arr_char CCC.seq_char CC'.arr_char
            by (elim CCC.seqE CC.seqE seqE, simp)
          moreover have "\<not> CCC.seq g f \<Longrightarrow> CCC.comp g f = CCC'.comp g f"
            using CCC'.seq_char CCC'.ext CCC'.null_char CCC.ext
            by (metis (no_types, lifting))
          ultimately show ?thesis by blast
        qed
      qed
      thus ?thesis by blast
    qed

    interpretation H: "functor" CC'.comp C \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<otimes> snd \<mu>\<nu>\<close>
      using CC'_eq_CC T.functor_axioms by simp
    interpretation H: horizontal_composition C tensor I.map I.map
      by (unfold_locales, simp_all)

    lemma HoHV_eq_ToTC:
    shows "H.HoHV = T.ToTC"
      using H.HoHV_def T.ToTC_def CCC'_eq_CCC by presburger

    interpretation HoHV: "functor" CCC'.comp C H.HoHV
      using T.functor_ToTC HoHV_eq_ToTC CCC'_eq_CCC by argo

    lemma HoVH_eq_ToCT:
    shows "H.HoVH = T.ToCT"
      using H.HoVH_def T.ToCT_def CCC'_eq_CCC by presburger

    interpretation HoVH: "functor" CCC'.comp C H.HoVH
      using T.functor_ToCT HoVH_eq_ToCT CCC'_eq_CCC by argo

    interpretation \<alpha>: natural_isomorphism CCC'.comp C H.HoHV H.HoVH \<alpha>
      using \<alpha>.natural_isomorphism_axioms CCC'_eq_CCC HoHV_eq_ToTC HoVH_eq_ToCT
      by simp

    lemma R'_eq_R:
    shows "H.R = R"
      using H.is_extensional CC'_eq_CC CC.arr_char by force

    lemma L'_eq_L:
    shows "H.L = L"
      using H.is_extensional CC'_eq_CC CC.arr_char by force

    interpretation R': fully_faithful_functor C C H.R
      using R'_eq_R R.fully_faithful_functor_axioms unity_def by auto
    interpretation L': fully_faithful_functor C C H.L
      using L'_eq_L L.fully_faithful_functor_axioms unity_def by auto

    lemma obj_char:
    shows "HH.obj a \<longleftrightarrow> a = \<I>"
      using HH.obj_def \<iota>_in_hom by fastforce

    proposition induces_bicategory:
    shows "bicategory C tensor (\<lambda>\<mu> \<nu> \<tau>. \<alpha> (\<mu>, \<nu>, \<tau>)) (\<lambda>_. \<iota>) I.map I.map"
      using obj_char \<iota>_in_hom \<iota>_is_iso pentagon \<alpha>.is_extensional \<alpha>.is_natural_1 \<alpha>.is_natural_2
      by (unfold_locales, simp_all)

  end

  subsection "Prebicategories Extend to Bicategories"

  text \<open>
    In this section, we show that a prebicategory with homs and units extends to a bicategory.
    The main work is to show that the endofunctors \<open>L\<close> and \<open>R\<close> are fully faithful.
    We take the left and right unitor isomorphisms, which were obtained via local
    constructions in the left and right hom-subcategories defined by a specified
    weak unit, and show that in the presence of the chosen sources and targets they
    are the components of a global natural isomorphisms \<open>\<ll>\<close> and \<open>\<rr>\<close> from the endofunctors
    \<open>L\<close> and \<open>R\<close> to the identity functor.  A consequence is that functors \<open>L\<close> and \<open>R\<close> are
    endo-equivalences, hence fully faithful.
  \<close>

  context prebicategory_with_homs
  begin

    text \<open>
      Once it is equipped with a particular choice of source and target for each arrow,
      a prebicategory determines a horizontal composition.
    \<close>

    lemma induces_horizontal_composition:
    shows "horizontal_composition V H src trg"
    proof -
      interpret VxV: product_category V V ..
      interpret VV: subcategory VxV.comp \<open>\<lambda>\<mu>\<nu>. arr (fst \<mu>\<nu>) \<and> arr (snd \<mu>\<nu>) \<and>
                                               src (fst \<mu>\<nu>) = trg (snd \<mu>\<nu>)\<close>
        using subcategory_VV by argo
      interpret VxVxV: product_category V VxV.comp ..
      interpret VVV: subcategory VxVxV.comp
                          \<open>\<lambda>\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> VV.arr (snd \<tau>\<mu>\<nu>) \<and>
                                 src (fst \<tau>\<mu>\<nu>) = trg (fst (snd \<tau>\<mu>\<nu>))\<close>
        using subcategory_VVV by blast
      interpret H: "functor" VV.comp V \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu>\<close>
      proof -
        have "VV.comp = VoV.comp"
          using composable_char\<^sub>P\<^sub>B\<^sub>H by meson
        thus "functor VV.comp V (\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu>)"
          using functor_axioms by argo
      qed
      show "horizontal_composition V H src trg"
        using src_hcomp' trg_hcomp' composable_char\<^sub>P\<^sub>B\<^sub>H not_arr_null
        by (unfold_locales; metis)
    qed

  end

  sublocale prebicategory_with_homs \<subseteq> horizontal_composition V H src trg
    using induces_horizontal_composition by auto

  locale prebicategory_with_homs_and_units =
    prebicategory_with_units +
    prebicategory_with_homs
  begin

    no_notation in_hom                ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    text \<open>
      The next definitions extend the left and right unitors that were defined locally with
      respect to a particular weak unit, to globally defined versions using the chosen
      source and target for each arrow.
    \<close>

    definition lunit  ("\<l>[_]")
    where "lunit f \<equiv> left_hom_with_unit.lunit V H \<a> \<i>[trg f] (trg f) f"

    definition runit  ("\<r>[_]")
    where "runit f \<equiv> right_hom_with_unit.runit V H \<a> \<i>[src f] (src f) f"

    lemma lunit_in_hom:
    assumes "ide f"
    shows "\<guillemotleft>\<l>[f] : src f \<rightarrow>\<^sub>W\<^sub>C trg f\<guillemotright>" and "\<guillemotleft>\<l>[f] : trg f \<star> f \<Rightarrow> f\<guillemotright>"
    proof -
      interpret Left: subcategory V \<open>left (trg f)\<close>
        using assms left_hom_is_subcategory by simp
      interpret Left: left_hom_with_unit V H \<a> \<open>\<i>[trg f]\<close> \<open>trg f\<close>
        using assms obj_is_weak_unit iso_unit\<^sub>P\<^sub>B\<^sub>U by (unfold_locales, auto)
      have 0: "Left.ide f"
        using assms Left.ide_char Left.arr_char left_def composable_char\<^sub>P\<^sub>B\<^sub>H by auto
      show 1: "\<guillemotleft>\<l>[f] : trg f \<star> f \<Rightarrow> f\<guillemotright>"
        unfolding lunit_def
        using assms 0 Left.lunit_char(1) Left.hom_char H\<^sub>L_def by auto
      show "\<guillemotleft>\<l>[f] : src f \<rightarrow>\<^sub>W\<^sub>C trg f\<guillemotright>"
        using 1 src_cod trg_cod src_in_sources trg_in_targets
        by (metis arrI vconn_implies_hpar)
    qed

    lemma runit_in_hom:
    assumes "ide f"
    shows "\<guillemotleft>\<r>[f] : src f \<rightarrow>\<^sub>W\<^sub>C trg f\<guillemotright>" and "\<guillemotleft>\<r>[f] : f \<star> src f \<Rightarrow> f\<guillemotright>"
    proof -
      interpret Right: subcategory V \<open>right (src f)\<close>
        using assms right_hom_is_subcategory weak_unit_self_composable by force
      interpret Right: right_hom_with_unit V H \<a> \<open>\<i>[src f]\<close> \<open>src f\<close>
        using assms obj_is_weak_unit iso_unit\<^sub>P\<^sub>B\<^sub>U by (unfold_locales, auto)
      have 0: "Right.ide f"
        using assms Right.ide_char Right.arr_char right_def composable_char\<^sub>P\<^sub>B\<^sub>H by auto
      show 1: "\<guillemotleft>\<r>[f] : f \<star> src f \<Rightarrow> f\<guillemotright>"
        unfolding runit_def
        using assms 0 Right.runit_char(1) Right.hom_char H\<^sub>R_def by auto
      show "\<guillemotleft>\<r>[f] : src f \<rightarrow>\<^sub>W\<^sub>C trg f\<guillemotright>"
        using 1 src_cod trg_cod src_in_sources trg_in_targets
        by (metis arrI vconn_implies_hpar)
    qed

    text \<open>
      The characterization of the locally defined unitors yields a corresponding characterization
      of the globally defined versions, by plugging in the chosen source or target for each
      arrow for the unspecified weak unit in the the local versions.
    \<close>

    lemma lunit_char:
    assumes "ide f"
    shows "\<guillemotleft>\<l>[f] : src f \<rightarrow>\<^sub>W\<^sub>C trg f\<guillemotright>" and "\<guillemotleft>\<l>[f] : trg f \<star> f \<Rightarrow> f\<guillemotright>"
    and "trg f \<star> \<l>[f] = (\<i>[trg f] \<star> f) \<cdot> inv \<a>[trg f, trg f, f]"
    and "\<exists>!\<mu>. \<guillemotleft>\<mu> : trg f \<star> f \<Rightarrow> f\<guillemotright> \<and> trg f \<star> \<mu> = (\<i>[trg f] \<star> f) \<cdot> inv \<a>[trg f, trg f, f]"
    proof -
      let ?a = "src f" and ?b = "trg f"
      interpret Left: subcategory V \<open>left ?b\<close>
        using assms left_hom_is_subcategory weak_unit_self_composable by force
      interpret Left: left_hom_with_unit V H \<a> \<open>\<i>[?b]\<close> ?b
        using assms obj_is_weak_unit iso_unit\<^sub>P\<^sub>B\<^sub>U by (unfold_locales, auto)
      have 0: "Left.ide f"
        using assms Left.ide_char Left.arr_char left_def composable_char\<^sub>P\<^sub>B\<^sub>H by auto
      show "\<guillemotleft>\<l>[f] : src f \<rightarrow>\<^sub>W\<^sub>C trg f\<guillemotright>"
        using assms lunit_in_hom by simp
      show A: "\<guillemotleft>\<l>[f] : trg f \<star> f \<Rightarrow> f\<guillemotright>"
        using assms lunit_in_hom by simp
      show B: "?b \<star> \<l>[f] = (\<i>[?b] \<star> f) \<cdot> inv \<a>[?b, ?b, f]"
        unfolding lunit_def using 0 Left.lunit_char(2) H\<^sub>L_def
        by (metis Left.comp_simp Left.characteristic_iso(1-2) Left.seqI')
      show "\<exists>!\<mu>. \<guillemotleft>\<mu> : trg f \<star> f \<Rightarrow> f\<guillemotright> \<and> trg f \<star> \<mu> = (\<i>[?b] \<star> f) \<cdot> inv \<a>[?b, ?b, f]"
      proof -
        have 1: "hom (trg f \<star> f) f = Left.hom (Left.L f) f"
        proof
          have 1: "Left.L f = ?b \<star> f"
          using 0 H\<^sub>L_def by simp
          show "Left.hom (Left.L f) f \<subseteq> hom (?b \<star> f) f"
            using assms Left.hom_char [of "?b \<star> f" f] H\<^sub>L_def by simp
          show "hom (?b \<star> f) f \<subseteq> Left.hom (Left.L f) f"
            using assms 1 ide_in_hom composable_char\<^sub>P\<^sub>B\<^sub>H hom_connected left_def
                  Left.hom_char
            by auto
        qed
        let ?P = "\<lambda>\<mu>. Left.in_hom \<mu> (Left.L f) f"
        let ?P' = "\<lambda>\<mu>. \<guillemotleft>\<mu> : ?b \<star> f \<Rightarrow> f\<guillemotright>"
        let ?Q = "\<lambda>\<mu>. Left.L \<mu> = (\<i>[?b] \<star> f) \<cdot> (inv \<a>[?b, ?b, f])"
        let ?R = "\<lambda>\<mu>. ?b \<star> \<mu> = (\<i>[?b] \<star> f) \<cdot> (inv \<a>[?b, ?b, f])"
        have 2: "?P = ?P'"
          using 0 1 H\<^sub>L_def Left.hom_char by blast
        moreover have "\<forall>\<mu>. ?P \<mu> \<longrightarrow> (?Q \<mu> \<longleftrightarrow> ?R \<mu>)"
          using 2 Left.lunit_eqI H\<^sub>L_def by presburger
        moreover have "(\<exists>!\<mu>. ?P \<mu> \<and> ?Q \<mu>)"
          using 0 2 A B Left.lunit_char(3) Left.ide_char Left.arr_char
          by (metis (no_types, lifting) Left.lunit_char(2) calculation(2) lunit_def)
        ultimately show ?thesis by metis
      qed
    qed

    lemma runit_char:
    assumes "ide f"
    shows "\<guillemotleft>\<r>[f] : src f \<rightarrow>\<^sub>W\<^sub>C trg f\<guillemotright>" and "\<guillemotleft>\<r>[f] : f \<star> src f \<Rightarrow> f\<guillemotright>"
    and "\<r>[f] \<star> src f = (f \<star> \<i>[src f]) \<cdot> \<a>[f, src f, src f]"
    and "\<exists>!\<mu>. \<guillemotleft>\<mu> : f \<star> src f \<Rightarrow> f\<guillemotright> \<and> \<mu> \<star> src f = (f \<star> \<i>[src f]) \<cdot> \<a>[f, src f, src f]"
    proof -
      let ?a = "src f" and ?b = "trg f"
      interpret Right: subcategory V \<open>right ?a\<close>
        using assms right_hom_is_subcategory weak_unit_self_composable by force
      interpret Right: right_hom_with_unit V H \<a> \<open>\<i>[?a]\<close> ?a
        using assms obj_is_weak_unit iso_unit\<^sub>P\<^sub>B\<^sub>U by (unfold_locales, auto)
      have 0: "Right.ide f"
        using assms Right.ide_char Right.arr_char right_def composable_char\<^sub>P\<^sub>B\<^sub>H by auto
      show "\<guillemotleft>\<r>[f] : src f \<rightarrow>\<^sub>W\<^sub>C trg f\<guillemotright>"
        using assms runit_in_hom by simp
      show A: "\<guillemotleft>\<r>[f] : f \<star> src f \<Rightarrow> f\<guillemotright>"
        using assms runit_in_hom by simp
      show B: "\<r>[f] \<star> ?a = (f \<star> \<i>[?a]) \<cdot> \<a>[f, ?a, ?a]"
        unfolding runit_def using 0 Right.runit_char(2) H\<^sub>R_def
        using Right.comp_simp Right.characteristic_iso(4) Right.iso_is_arr by auto
      show "\<exists>!\<mu>. \<guillemotleft>\<mu> : f \<star> src f \<Rightarrow> f\<guillemotright> \<and> \<mu> \<star> ?a = (f \<star> \<i>[?a]) \<cdot> \<a>[f, ?a, ?a]"
      proof -
        have 1: "hom (f \<star> ?a) f = Right.hom (Right.R f) f"
        proof
          have 1: "Right.R f = f \<star> ?a"
          using 0 H\<^sub>R_def by simp
          show "Right.hom (Right.R f) f \<subseteq> hom (f \<star> ?a) f"
            using assms Right.hom_char [of "f \<star> ?a" f] H\<^sub>R_def by simp
          show "hom (f \<star> ?a) f \<subseteq> Right.hom (Right.R f) f"
            using assms 1 ide_in_hom composable_char\<^sub>P\<^sub>B\<^sub>H hom_connected right_def
                  Right.hom_char
            by auto
        qed
        let ?P = "\<lambda>\<mu>. Right.in_hom \<mu> (Right.R f) f"
        let ?P' = "\<lambda>\<mu>. \<guillemotleft>\<mu> : f \<star> ?a \<Rightarrow> f\<guillemotright>"
        let ?Q = "\<lambda>\<mu>. Right.R \<mu> = (f \<star> \<i>[?a]) \<cdot> \<a>[f, ?a, ?a]"
        let ?R = "\<lambda>\<mu>. \<mu> \<star> ?a = (f \<star> \<i>[?a]) \<cdot> \<a>[f, ?a, ?a]"
        have 2: "?P = ?P'"
          using 0 1 H\<^sub>R_def Right.hom_char by blast
        moreover have "\<forall>\<mu>. ?P \<mu> \<longrightarrow> (?Q \<mu> \<longleftrightarrow> ?R \<mu>)"
          using 2 Right.runit_eqI H\<^sub>R_def by presburger
        moreover have "(\<exists>!\<mu>. ?P \<mu> \<and> ?Q \<mu>)"
          using 0 2 A B Right.runit_char(3) Right.ide_char Right.arr_char
          by (metis (no_types, lifting) Right.runit_char(2) calculation(2) runit_def)
        ultimately show ?thesis by metis
      qed
    qed

    lemma lunit_eqI:
    assumes "ide f" and "\<guillemotleft>\<mu> : trg f \<star> f \<Rightarrow> f\<guillemotright>"
    and "trg f \<star> \<mu> = (\<i>[trg f] \<star> f) \<cdot> (inv \<a>[trg f, trg f, f])"
    shows "\<mu> = \<l>[f]"
      using assms lunit_char(2-4) by blast

    lemma runit_eqI:
    assumes "ide f" and "\<guillemotleft>\<mu> : f \<star> src f \<Rightarrow> f\<guillemotright>"
    and "\<mu> \<star> src f = (f \<star> \<i>[src f]) \<cdot> \<a>[f, src f, src f]"
    shows "\<mu> = \<r>[f]"
      using assms runit_char(2-4) by blast

    lemma iso_lunit:
    assumes "ide f"
    shows "iso \<l>[f]"
    proof -
      let ?b = "trg f"
      interpret Left: subcategory V \<open>left ?b\<close>
        using assms left_hom_is_subcategory weak_unit_self_composable by force
      interpret Left: left_hom_with_unit V H \<a> \<open>\<i>[?b]\<close> ?b
        using assms obj_is_weak_unit iso_unit\<^sub>P\<^sub>B\<^sub>U by (unfold_locales, auto)
      show ?thesis
      proof -
        have 0: "Left.ide f"
          using assms Left.ide_char Left.arr_char left_def composable_char\<^sub>P\<^sub>B\<^sub>H by auto
        thus ?thesis
          unfolding lunit_def using Left.iso_lunit Left.iso_char by blast
      qed
    qed

    lemma iso_runit:
    assumes "ide f"
    shows "iso \<r>[f]"
    proof -
      let ?a = "src f"
      interpret Right: subcategory V \<open>right ?a\<close>
        using assms right_hom_is_subcategory weak_unit_self_composable by force
      interpret Right: right_hom_with_unit V H \<a> \<open>\<i>[?a]\<close> ?a
        using assms obj_is_weak_unit iso_unit\<^sub>P\<^sub>B\<^sub>U by (unfold_locales, auto)
      show ?thesis
      proof -
        have 0: "Right.ide f"
          using assms Right.ide_char Right.arr_char right_def composable_char\<^sub>P\<^sub>B\<^sub>H by auto
        thus ?thesis
          unfolding runit_def using Right.iso_runit Right.iso_char by blast
      qed
    qed

    lemma lunit_naturality:
    assumes "arr \<mu>"
    shows "\<mu> \<cdot> \<l>[dom \<mu>] = \<l>[cod \<mu>] \<cdot> (trg \<mu> \<star> \<mu>)"
    proof -
      let ?a = "src \<mu>" and ?b = "trg \<mu>"
      interpret Left: subcategory V \<open>left ?b\<close>
        using assms obj_trg left_hom_is_subcategory weak_unit_self_composable by force
      interpret Left: left_hom_with_unit V H \<a> \<open>\<i>[?b]\<close> ?b
        using assms obj_is_weak_unit iso_unit\<^sub>P\<^sub>B\<^sub>U by (unfold_locales, auto)
      interpret Left.L: endofunctor \<open>Left ?b\<close> Left.L
        using assms endofunctor_H\<^sub>L [of ?b] weak_unit_self_composable obj_trg obj_is_weak_unit
        by blast
      have 1: "Left.in_hom \<mu> (dom \<mu>) (cod \<mu>)"
        using assms Left.hom_char Left.arr_char left_def composable_char\<^sub>P\<^sub>B\<^sub>H obj_trg by auto
      have 2: "Left.in_hom \<l>[Left.dom \<mu>] (?b \<star> dom \<mu>) (dom \<mu>)"
        unfolding lunit_def
        using assms 1 Left.in_hom_char trg_dom Left.lunit_char(1) H\<^sub>L_def
              Left.arr_char Left.dom_char Left.ide_dom
        by force
      have 3: "Left.in_hom \<l>[Left.cod \<mu>] (?b \<star> cod \<mu>) (cod \<mu>)"
        unfolding lunit_def
        using assms 1 Left.in_hom_char trg_cod Left.lunit_char(1) H\<^sub>L_def
              Left.cod_char Left.ide_cod
        by force
      have 4: "Left.in_hom (Left.L \<mu>) (?b \<star> dom \<mu>) (?b \<star> cod \<mu>)"
        using 1 Left.L.preserves_hom [of \<mu> "dom \<mu>" "cod \<mu>"] H\<^sub>L_def by auto
      show ?thesis
      proof -
        have "\<mu> \<cdot> \<l>[dom \<mu>] = Left.comp \<mu> \<l>[Left.dom \<mu>]"
          using 1 2 Left.comp_simp by fastforce
        also have "... = Left.comp \<mu> (Left.lunit (Left.dom \<mu>))"
          using assms 1 lunit_def by auto
        also have "... = Left.comp (Left.lunit (Left.cod \<mu>)) (Left.L \<mu>)"
          using 1 Left.lunit_naturality by auto
        also have "... = Left.comp (lunit (Left.cod \<mu>)) (Left.L \<mu>)"
          using assms 1 lunit_def by auto
        also have "... = \<l>[cod \<mu>] \<cdot> Left.L \<mu>"
          using 1 3 4 Left.comp_char Left.cod_char Left.in_hom_char by auto
        also have "... = \<l>[cod \<mu>] \<cdot> (trg \<mu> \<star> \<mu>)"
          using 1 by (simp add: H\<^sub>L_def)
        finally show ?thesis by simp
      qed
    qed

    lemma runit_naturality:
    assumes "arr \<mu>"
    shows "\<mu> \<cdot> \<r>[dom \<mu>] = \<r>[cod \<mu>] \<cdot> (\<mu> \<star> src \<mu>)"
    proof -
      let ?a = "src \<mu>" and ?b = "trg \<mu>"
      interpret Right: subcategory V \<open>right ?a\<close>
        using assms right_hom_is_subcategory weak_unit_self_composable by force
      interpret Right: right_hom_with_unit V H \<a> \<open>\<i>[?a]\<close> ?a
        using assms obj_is_weak_unit iso_unit\<^sub>P\<^sub>B\<^sub>U by (unfold_locales, auto)
      interpret Right.R: endofunctor \<open>Right ?a\<close> Right.R
        using assms endofunctor_H\<^sub>R [of ?a] weak_unit_self_composable obj_src obj_is_weak_unit
        by blast
      have 1: "Right.in_hom \<mu> (dom \<mu>) (cod \<mu>)"
        using assms Right.hom_char Right.arr_char right_def composable_char\<^sub>P\<^sub>B\<^sub>H by auto
      have 2: "Right.in_hom \<r>[Right.dom \<mu>] (dom \<mu> \<star> ?a) (dom \<mu>)"
        unfolding runit_def
        using 1 Right.in_hom_char trg_dom Right.runit_char(1) [of "Right.dom \<mu>"] H\<^sub>R_def
              Right.arr_char Right.dom_char Right.ide_dom assms
        by force
      have 3: "\<r>[Right.cod \<mu>] \<in> Right.hom (cod \<mu> \<star> ?a) (cod \<mu>)"
        unfolding runit_def
        using 1 Right.in_hom_char trg_cod Right.runit_char(1) [of "Right.cod \<mu>"] H\<^sub>R_def
              Right.cod_char Right.ide_cod assms
        by force
      have 4: "Right.R \<mu> \<in> Right.hom (dom \<mu> \<star> ?a) (cod \<mu> \<star> ?a)"
        using 1 Right.R.preserves_hom [of \<mu> "dom \<mu>" "cod \<mu>"] H\<^sub>R_def by auto
      show ?thesis
      proof -
        have "\<mu> \<cdot> \<r>[dom \<mu>] = Right.comp \<mu> \<r>[Right.dom \<mu>]"
          by (metis 1 2 Right.comp_char Right.in_homE Right.seqI' Right.seq_char)
        also have "... = Right.comp \<mu> (Right.runit (Right.dom \<mu>))"
          using assms 1 src_dom trg_dom Right.hom_char runit_def by auto
        also have "... = Right.comp (Right.runit (Right.cod \<mu>)) (Right.R \<mu>)"
          using 1 Right.runit_naturality by auto
        also have "... = Right.comp (runit (Right.cod \<mu>)) (Right.R \<mu>)"
          using assms 1 runit_def by auto
        also have "... = \<r>[cod \<mu>] \<cdot> Right.R \<mu>"
          using 1 3 4 Right.comp_char Right.cod_char Right.in_hom_char by auto
        also have "... = \<r>[cod \<mu>] \<cdot> (\<mu> \<star> ?a)"
          using 1 by (simp add: H\<^sub>R_def)
        finally show ?thesis by simp
      qed
    qed

    interpretation L: endofunctor V L
      using endofunctor_L by auto
    interpretation \<ll>: transformation_by_components V V L map lunit
      using lunit_in_hom lunit_naturality by unfold_locales auto
    interpretation \<ll>: natural_isomorphism V V L map \<ll>.map
      using iso_lunit by unfold_locales auto

    lemma natural_isomorphism_\<ll>:
    shows "natural_isomorphism V V L map \<ll>.map"
      ..

    interpretation L: equivalence_functor V V L
      using L.isomorphic_to_identity_is_equivalence \<ll>.natural_isomorphism_axioms by simp

    lemma equivalence_functor_L:
    shows "equivalence_functor V V L"
      ..

    lemma lunit_commutes_with_L:
    assumes "ide f"
    shows "\<l>[L f] = L \<l>[f]"
    proof -
      have "seq \<l>[f] (L \<l>[f])"
        using assms lunit_char(2) L.preserves_hom by fastforce
      moreover have "seq \<l>[f] \<l>[L f]"
        using assms lunit_char(2) lunit_char(2) [of "L f"] L.preserves_ide by auto
      ultimately show ?thesis
        using assms lunit_char(2) [of f] lunit_naturality [of "\<l>[f]"] iso_lunit
              iso_is_section section_is_mono monoE [of "\<l>[f]" "L \<l>[f]" "\<l>[L f]"]
        by auto
    qed

    interpretation R: endofunctor V R
      using endofunctor_R by auto
    interpretation \<rr>: transformation_by_components V V R map runit
      using runit_in_hom runit_naturality by unfold_locales auto
    interpretation \<rr>: natural_isomorphism V V R map \<rr>.map
      using iso_runit by unfold_locales auto

    lemma natural_isomorphism_\<rr>:
    shows "natural_isomorphism V V R map \<rr>.map"
      ..

    interpretation R: equivalence_functor V V R
      using R.isomorphic_to_identity_is_equivalence \<rr>.natural_isomorphism_axioms by simp

    lemma equivalence_functor_R:
    shows "equivalence_functor V V R"
      ..

    lemma runit_commutes_with_R:
    assumes "ide f"
    shows "\<r>[R f] = R \<r>[f]"
    proof -
      have "seq \<r>[f] (R \<r>[f])"
        using assms runit_char(2) R.preserves_hom by fastforce
      moreover have "seq \<r>[f] \<r>[R f]"
        using assms runit_char(2) runit_char(2) [of "R f"] R.preserves_ide by auto
      ultimately show ?thesis
        using assms runit_char(2) [of f] runit_naturality [of "\<r>[f]"] iso_runit
              iso_is_section section_is_mono monoE [of "\<r>[f]" "R \<r>[f]" "\<r>[R f]"]
        by auto
    qed

    interpretation VxVxV: product_category V VxV.comp ..
    interpretation VVV: subcategory VxVxV.comp
                            \<open>\<lambda>\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> VV.arr (snd \<tau>\<mu>\<nu>) \<and>
                                   src (fst \<tau>\<mu>\<nu>) = trg (fst (snd \<tau>\<mu>\<nu>))\<close>
      using subcategory_VVV by blast
    interpretation HoHV: "functor" VVV.comp V HoHV
      using functor_HoHV by blast
    interpretation HoVH: "functor" VVV.comp V HoVH
      using functor_HoVH by blast

    definition \<alpha>
    where "\<alpha> \<mu> \<nu> \<tau> \<equiv> if VVV.arr (\<mu>, \<nu>, \<tau>) then
                        (\<mu> \<star> \<nu> \<star> \<tau>) \<cdot> \<a>[dom \<mu>, dom \<nu>, dom \<tau>]
                      else null"

    lemma \<alpha>_ide_simp [simp]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "\<alpha> f g h = \<a>[f, g, h]"
    proof -
      have "\<alpha> f g h = (f \<star> g \<star> h) \<cdot> \<a>[dom f, dom g, dom h]"
        using assms \<alpha>_def VVV.arr_char [of "(f, g, h)"] by auto
      also have "... = (f \<star> g \<star> h) \<cdot> \<a>[f, g, h]"
        using assms by simp
      also have "... = \<a>[f, g, h]"
        using assms \<alpha>_def assoc_in_hom\<^sub>A\<^sub>W\<^sub>C hcomp_in_hom\<^sub>P\<^sub>B\<^sub>H VVV.arr_char VoV.arr_char
              comp_cod_arr composable_char\<^sub>P\<^sub>B\<^sub>H
        by auto
      finally show ?thesis by simp
    qed

    (* TODO: Figure out how this got reinstated. *)
    no_notation in_hom      ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    lemma natural_isomorphism_\<alpha>:
    shows "natural_isomorphism VVV.comp V HoHV HoVH
             (\<lambda>\<mu>\<nu>\<tau>. \<alpha> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>)))"
    proof -
      interpret \<alpha>: transformation_by_components VVV.comp V HoHV HoVH
                     \<open>\<lambda>f. \<a>[fst f, fst (snd f), snd (snd f)]\<close>
      proof
        show 1: "\<And>x. VVV.ide x \<Longrightarrow> \<guillemotleft>\<a>[fst x, fst (snd x), snd (snd x)] : HoHV x \<Rightarrow> HoVH x\<guillemotright>"
        proof -
          fix x
          assume x: "VVV.ide x"
          show "\<guillemotleft>\<a>[fst x, fst (snd x), snd (snd x)] : HoHV x \<Rightarrow> HoVH x\<guillemotright>"
          proof -
            have "ide (fst x) \<and> ide (fst (snd x)) \<and> ide (snd (snd x)) \<and>
                  fst x \<star> fst (snd x) \<noteq> null \<and> fst (snd x) \<star> snd (snd x) \<noteq> null"
              using x VVV.ide_char VVV.arr_char VV.arr_char composable_char\<^sub>P\<^sub>B\<^sub>H by simp
            hence "\<a>[fst x, fst (snd x), snd (snd x)]
                     \<in> hom ((fst x \<star> fst (snd x)) \<star> snd (snd x))
                             (fst x \<star> fst (snd x) \<star> snd (snd x))"
              using x assoc_in_hom\<^sub>A\<^sub>W\<^sub>C by simp
            thus ?thesis
              unfolding HoHV_def HoVH_def
              using x VVV.ideD(1) by simp
          qed
        qed
        show "\<And>f. VVV.arr f \<Longrightarrow>
                   \<a>[fst (VVV.cod f), fst (snd (VVV.cod f)), snd (snd (VVV.cod f))] \<cdot> HoHV f =
                   HoVH f \<cdot> \<a>[fst (VVV.dom f), fst (snd (VVV.dom f)), snd (snd (VVV.dom f))]"
          unfolding HoHV_def HoVH_def
          using assoc_naturality\<^sub>A\<^sub>W\<^sub>C VVV.arr_char VV.arr_char VVV.dom_char VVV.cod_char
                composable_char\<^sub>P\<^sub>B\<^sub>H
          by simp
      qed
      interpret \<alpha>: natural_isomorphism VVV.comp V HoHV HoVH \<alpha>.map
      proof
        fix f
        assume f: "VVV.ide f"
        show "iso (\<alpha>.map f)"
        proof -
          have "fst f \<star> fst (snd f) \<noteq> null \<and> fst (snd f) \<star> snd (snd f) \<noteq> null"
            using f VVV.ideD(1) VVV.arr_char [of f] VV.arr_char composable_char\<^sub>P\<^sub>B\<^sub>H by auto
          thus ?thesis
            using f \<alpha>.map_simp_ide iso_assoc\<^sub>A\<^sub>W\<^sub>C VVV.ide_char VVV.arr_char by simp
        qed
      qed
      have "(\<lambda>\<mu>\<nu>\<tau>. \<alpha> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>))) = \<alpha>.map"
      proof
        fix \<mu>\<nu>\<tau>
        have "\<not> VVV.arr \<mu>\<nu>\<tau> \<Longrightarrow> \<alpha> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>)) = \<alpha>.map \<mu>\<nu>\<tau>"
          using \<alpha>_def \<alpha>.map_def by simp
        moreover have "VVV.arr \<mu>\<nu>\<tau> \<Longrightarrow>
                         \<alpha> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>)) = \<alpha>.map \<mu>\<nu>\<tau>"
        proof -
          assume \<mu>\<nu>\<tau>: "VVV.arr \<mu>\<nu>\<tau>"
          have "\<alpha> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>)) =
                (fst \<mu>\<nu>\<tau> \<star> fst (snd \<mu>\<nu>\<tau>) \<star> snd (snd \<mu>\<nu>\<tau>)) \<cdot>
                  \<a>[dom (fst \<mu>\<nu>\<tau>), dom (fst (snd \<mu>\<nu>\<tau>)), dom (snd (snd \<mu>\<nu>\<tau>))]"
            using \<mu>\<nu>\<tau> \<alpha>_def by simp
          also have "... = \<a>[cod (fst \<mu>\<nu>\<tau>), cod (fst (snd \<mu>\<nu>\<tau>)), cod (snd (snd \<mu>\<nu>\<tau>))] \<cdot>
                             ((fst \<mu>\<nu>\<tau> \<star> fst (snd \<mu>\<nu>\<tau>)) \<star> snd (snd \<mu>\<nu>\<tau>))"
            using \<mu>\<nu>\<tau> HoHV_def HoVH_def VVV.arr_char VV.arr_char assoc_naturality\<^sub>A\<^sub>W\<^sub>C
                  composable_char\<^sub>P\<^sub>B\<^sub>H
            by simp
          also have "... =
                     \<a>[fst (VVV.cod \<mu>\<nu>\<tau>), fst (snd (VVV.cod \<mu>\<nu>\<tau>)), snd (snd (VVV.cod \<mu>\<nu>\<tau>))] \<cdot>
                       ((fst \<mu>\<nu>\<tau> \<star> fst (snd \<mu>\<nu>\<tau>)) \<star> snd (snd \<mu>\<nu>\<tau>))"
            using \<mu>\<nu>\<tau> VVV.arr_char VVV.cod_char VV.arr_char by simp
          also have "... = \<alpha>.map \<mu>\<nu>\<tau>"
            using \<mu>\<nu>\<tau> \<alpha>.map_def HoHV_def composable_char\<^sub>P\<^sub>B\<^sub>H by auto
          finally show ?thesis by blast
        qed
        ultimately show "\<alpha> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>)) = \<alpha>.map \<mu>\<nu>\<tau>" by blast
      qed
      thus ?thesis using \<alpha>.natural_isomorphism_axioms by simp
    qed

    proposition induces_bicategory:
    shows "bicategory V H \<alpha> \<i> src trg"
    proof -
      interpret VxVxV: product_category V VxV.comp ..
      interpret VoVoV: subcategory VxVxV.comp
                       \<open>\<lambda>\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> VV.arr (snd \<tau>\<mu>\<nu>) \<and>
                              src (fst \<tau>\<mu>\<nu>) = trg (fst (snd \<tau>\<mu>\<nu>))\<close>
        using subcategory_VVV by blast
      interpret HoHV: "functor" VVV.comp V HoHV
        using functor_HoHV by blast
      interpret HoVH: "functor" VVV.comp V HoVH
        using functor_HoVH by blast
      interpret \<alpha>: natural_isomorphism VVV.comp V HoHV HoVH
                     \<open>\<lambda>\<mu>\<nu>\<tau>. \<alpha> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>))\<close>
        using natural_isomorphism_\<alpha> by blast
      interpret L: equivalence_functor V V L
        using equivalence_functor_L by blast
      interpret R: equivalence_functor V V R
        using equivalence_functor_R by blast
      show "bicategory V H \<alpha> \<i> src trg"
      proof
        show "\<And>a. obj a \<Longrightarrow> \<guillemotleft>\<i>[a] : a \<star> a \<Rightarrow> a\<guillemotright>"
          using obj_is_weak_unit unit_in_vhom\<^sub>P\<^sub>B\<^sub>U by blast
        show "\<And>a. obj a \<Longrightarrow> iso \<i>[a]"
          using obj_is_weak_unit iso_unit\<^sub>P\<^sub>B\<^sub>U by blast
        show "\<And>f g h k. \<lbrakk> ide f; ide g; ide h; ide k;
                          src f = trg g; src g = trg h; src h = trg k \<rbrakk> \<Longrightarrow>
                          (f \<star> \<alpha> g h k) \<cdot> \<alpha> f (g \<star> h) k \<cdot> (\<alpha> f g h \<star> k) =
                          \<alpha> f g (h \<star> k) \<cdot> \<alpha> (f \<star> g) h k"
        proof -
          fix f g h k
          assume f: "ide f" and g: "ide g" and h: "ide h" and k: "ide k"
          and fg: "src f = trg g" and gh: "src g = trg h" and hk: "src h = trg k"
          have "sources f \<inter> targets g \<noteq> {}"
            using f g fg src_in_sources [of f] trg_in_targets ideD(1) by auto
          moreover have "sources g \<inter> targets h \<noteq> {}"
            using g h gh src_in_sources [of g] trg_in_targets ideD(1) by auto
          moreover have "sources h \<inter> targets k \<noteq> {}"
            using h k hk src_in_sources [of h] trg_in_targets ideD(1) by auto
          moreover have "\<alpha> f g h = \<a>[f, g, h] \<and> \<alpha> g h k = \<a>[g, h, k]"
            using f g h k fg gh hk \<alpha>_ide_simp by simp
          moreover have "\<alpha> f (g \<star> h) k = \<a>[f, g \<star> h, k] \<and> \<alpha> f g (h \<star> k) = \<a>[f, g, h \<star> k] \<and>
                         \<alpha> (f \<star> g) h k = \<a>[f \<star> g, h, k]"
            using f g h k fg gh hk \<alpha>_ide_simp preserves_ide hcomp_in_hom\<^sub>P\<^sub>B\<^sub>H(1) by simp
          ultimately show "(f \<star> \<alpha> g h k) \<cdot> \<alpha> f (g \<star> h) k \<cdot> (\<alpha> f g h \<star> k) =
                           \<alpha> f g (h \<star> k) \<cdot> \<alpha> (f \<star> g) h k"
            using f g h k fg gh hk pentagon\<^sub>A\<^sub>W\<^sub>C [of f g h k] \<alpha>_ide_simp by presburger
        qed
      qed
    qed

  end

  text \<open>
    The following is the main result of this development:
    Every prebicategory extends to a bicategory, by making an arbitrary choice of
    representatives of each isomorphism class of weak units and using that to
    define the source and target mappings, and then choosing an arbitrary isomorphism
    in \<open>hom (a \<star> a) a\<close> for each weak unit \<open>a\<close>.
  \<close>

  context prebicategory
  begin

    interpretation prebicategory_with_homs V H \<a> some_src some_trg
      using extends_to_prebicategory_with_homs by auto

    interpretation prebicategory_with_units V H \<a> some_unit
      using extends_to_prebicategory_with_units by auto

    interpretation prebicategory_with_homs_and_units V H \<a> some_unit some_src some_trg ..

    theorem extends_to_bicategory:
    shows "bicategory V H \<alpha> some_unit some_src some_trg"
      using induces_bicategory by simp

  end

  section "Bicategories as Prebicategories"

  subsection "Bicategories are Prebicategories"

  text \<open>
    In this section we show that a bicategory determines a prebicategory with homs,
    whose weak units are exactly those arrows that are isomorphic to their chosen source,
    or equivalently, to their chosen target.
    Moreover, the notion of horizontal composability, which in a bicategory is determined
    by the coincidence of chosen sources and targets, agrees with the version defined
    for the induced weak composition in terms of nonempty intersections of source and
    target sets, which is not dependent on any arbitrary choices.
  \<close>

  context bicategory
  begin

    (* TODO: Why does this get re-introduced? *)
    no_notation in_hom        ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    interpretation \<alpha>': inverse_transformation VVV.comp V HoHV HoVH
                         \<open>\<lambda>\<mu>\<nu>\<tau>. \<a> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>))\<close> ..

    abbreviation \<alpha>'
    where "\<alpha>' \<equiv> \<alpha>'.map"

    definition \<a>'  ("\<a>\<^sup>-\<^sup>1[_, _, _]")
    where "\<a>\<^sup>-\<^sup>1[\<mu>, \<nu>, \<tau>] \<equiv> \<alpha>'.map (\<mu>, \<nu>, \<tau>)"

    lemma assoc'_in_hom':
    assumes "arr \<mu>" and "arr \<nu>" and "arr \<tau>" and "src \<mu> = trg \<nu>" and "src \<nu> = trg \<tau>"
    shows "in_hhom \<a>\<^sup>-\<^sup>1[\<mu>, \<nu>, \<tau>] (src \<tau>) (trg \<mu>)"
    and "\<guillemotleft>\<a>\<^sup>-\<^sup>1[\<mu>, \<nu>, \<tau>] : dom \<mu> \<star> dom \<nu> \<star> dom \<tau> \<Rightarrow> (cod \<mu> \<star> cod \<nu>) \<star> cod \<tau>\<guillemotright>"
    proof -
      show "\<guillemotleft>\<a>\<^sup>-\<^sup>1[\<mu>, \<nu>, \<tau>] : dom \<mu> \<star> dom \<nu> \<star> dom \<tau> \<Rightarrow> (cod \<mu> \<star> cod \<nu>) \<star> cod \<tau>\<guillemotright>"
      proof -
        have 1: "VVV.in_hom (\<mu>, \<nu>, \<tau>) (dom \<mu>, dom \<nu>, dom \<tau>) (cod \<mu>, cod \<nu>, cod \<tau>)"
          using assms VVV.in_hom_char VVV.arr_char VV.arr_char by auto
        have "\<guillemotleft>\<a>\<^sup>-\<^sup>1[\<mu>, \<nu>, \<tau>] : HoVH (dom \<mu>, dom \<nu>, dom \<tau>) \<Rightarrow> HoHV (cod \<mu>, cod \<nu>, cod \<tau>)\<guillemotright>"
          using 1 \<a>'_def \<alpha>'.preserves_hom by auto
        moreover have "HoVH (dom \<mu>, dom \<nu>, dom \<tau>) = dom \<mu> \<star> dom \<nu> \<star> dom \<tau>"
          using 1 HoVH_def by (simp add: VVV.in_hom_char)
        moreover have "HoHV (cod \<mu>, cod \<nu>, cod \<tau>) = (cod \<mu> \<star> cod \<nu>) \<star> cod \<tau>"
          using 1 HoHV_def by (simp add: VVV.in_hom_char)
        ultimately show ?thesis by simp
      qed
      thus "in_hhom \<a>\<^sup>-\<^sup>1[\<mu>, \<nu>, \<tau>] (src \<tau>) (trg \<mu>)"
        using assms vconn_implies_hpar(1) vconn_implies_hpar(2) by auto
    qed

    lemma assoc'_is_natural_1:
    assumes "arr \<mu>" and "arr \<nu>" and "arr \<tau>" and "src \<mu> = trg \<nu>" and "src \<nu> = trg \<tau>"
    shows "\<a>\<^sup>-\<^sup>1[\<mu>, \<nu>, \<tau>] = ((\<mu> \<star> \<nu>) \<star> \<tau>) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<mu>, dom \<nu>, dom \<tau>]"
      using assms \<alpha>'.is_natural_1 [of "(\<mu>, \<nu>, \<tau>)"] VVV.arr_char VV.arr_char
            VVV.dom_char HoHV_def src_dom trg_dom \<a>'_def
      by simp

    lemma assoc'_is_natural_2:
    assumes "arr \<mu>" and "arr \<nu>" and "arr \<tau>" and "src \<mu> = trg \<nu>" and "src \<nu> = trg \<tau>"
    shows "\<a>\<^sup>-\<^sup>1[\<mu>, \<nu>, \<tau>] = \<a>\<^sup>-\<^sup>1[cod \<mu>, cod \<nu>, cod \<tau>] \<cdot> (\<mu> \<star> \<nu> \<star> \<tau>)"
      using assms \<alpha>'.is_natural_2 [of "(\<mu>, \<nu>, \<tau>)"] VVV.arr_char VV.arr_char
            VVV.cod_char HoVH_def src_dom trg_dom \<a>'_def
      by simp

    lemma assoc'_naturality:
    assumes "arr \<mu>" and "arr \<nu>" and "arr \<tau>" and "src \<mu> = trg \<nu>" and "src \<nu> = trg \<tau>"
    shows "\<a>\<^sup>-\<^sup>1[cod \<mu>, cod \<nu>, cod \<tau>] \<cdot> (\<mu> \<star> \<nu> \<star> \<tau>) = ((\<mu> \<star> \<nu>) \<star> \<tau>) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<mu>, dom \<nu>, dom \<tau>]"
      using assms assoc'_is_natural_1 assoc'_is_natural_2 by metis

    lemma assoc'_in_hom [intro]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "in_hhom \<a>\<^sup>-\<^sup>1[f, g, h] (src h) (trg f)"
    and "\<guillemotleft>\<a>\<^sup>-\<^sup>1[f, g, h] : dom f \<star> dom g \<star> dom h \<Rightarrow> (cod f \<star> cod g) \<star> cod h\<guillemotright>"
      using assms assoc'_in_hom'(1-2) ideD(1) by meson+

    lemma assoc'_simps [simp]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "arr \<a>\<^sup>-\<^sup>1[f, g, h]"
    and "src \<a>\<^sup>-\<^sup>1[f, g, h] = src h" and "trg \<a>\<^sup>-\<^sup>1[f, g, h] = trg f"
    and "dom \<a>\<^sup>-\<^sup>1[f, g, h] = dom f \<star> dom g \<star> dom h"
    and "cod \<a>\<^sup>-\<^sup>1[f, g, h] = (cod f \<star> cod g) \<star> cod h"
      using assms assoc'_in_hom by blast+

    lemma assoc'_eq_inv_assoc [simp]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "\<a>\<^sup>-\<^sup>1[f, g, h] = inv \<a>[f, g, h]"
      using assms VVV.ide_char VVV.arr_char VV.ide_char VV.arr_char \<alpha>'.map_ide_simp
            \<a>'_def
      by auto

    lemma inverse_assoc_assoc' [intro]:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "inverse_arrows \<a>[f, g, h] \<a>\<^sup>-\<^sup>1[f, g, h]"
      using assms VVV.ide_char VVV.arr_char VV.ide_char VV.arr_char \<alpha>'.map_ide_simp
            \<alpha>'.inverts_components \<a>'_def
      by auto

    lemma iso_assoc' [intro, simp]:
    assumes "ide f" and "ide g" and "ide h"
    and "src f = trg g" and "src g = trg h"
    shows "iso \<a>\<^sup>-\<^sup>1[f, g, h]"
      using assms iso_inv_iso by simp

    lemma comp_assoc_assoc' [simp]:
    assumes "ide f" and "ide g" and "ide h"
    and "src f = trg g" and "src g = trg h"
    shows "\<a>[f, g, h] \<cdot> \<a>\<^sup>-\<^sup>1[f, g, h] = f \<star> g \<star> h"
    and "\<a>\<^sup>-\<^sup>1[f, g, h] \<cdot> \<a>[f, g, h] = (f \<star> g) \<star> h"
      using assms comp_arr_inv' comp_inv_arr' by auto

    lemma unit_in_hom [intro, simp]:
    assumes "obj a"
    shows "\<guillemotleft>\<i>[a] : a \<rightarrow> a\<guillemotright>" and "\<guillemotleft>\<i>[a] : a \<star> a \<Rightarrow> a\<guillemotright>"
    proof -
      show "\<guillemotleft>\<i>[a] : a \<star> a \<Rightarrow> a\<guillemotright>"
        using assms unit_in_vhom by simp
      thus "\<guillemotleft>\<i>[a] : a \<rightarrow> a\<guillemotright>"
        using assms src_cod trg_cod by fastforce
    qed

    interpretation weak_composition V H
      using is_weak_composition by auto

    lemma seq_if_composable:
    assumes "\<nu> \<star> \<mu> \<noteq> null"
    shows "src \<nu> = trg \<mu>"
      using assms H.is_extensional [of "(\<nu>, \<mu>)"] VV.arr_char by auto

    lemma obj_self_composable:
    assumes "obj a"
    shows "a \<star> a \<noteq> null"
    and "isomorphic (a \<star> a) a"
    proof -
      show 1: "isomorphic (a \<star> a) a"
        using assms unit_in_hom iso_unit isomorphic_def by blast
      obtain \<phi> where \<phi>: "iso \<phi> \<and> \<guillemotleft>\<phi> : a \<star> a \<Rightarrow> a\<guillemotright>"
        using 1 isomorphic_def by blast
      have "ide (a \<star> a)" using 1 \<phi> ide_dom [of \<phi>] by fastforce
      thus "a \<star> a \<noteq> null" using ideD(1) not_arr_null by metis
    qed

    lemma obj_is_weak_unit:
    assumes "obj a"
    shows "weak_unit a"
    proof -
      interpret Left_a: subcategory V \<open>left a\<close>
        using assms left_hom_is_subcategory by force
      interpret Right_a: subcategory V \<open>right a\<close>
        using assms right_hom_is_subcategory by force

      text \<open>
        We know that \<open>H\<^sub>L a\<close> is fully faithful as a global endofunctor,
        but the definition of weak unit involves its restriction to a
        subcategory.  So we have to verify that the restriction
        is also a fully faithful functor.
      \<close>

      interpret La: endofunctor \<open>Left a\<close> \<open>H\<^sub>L a\<close>
        using assms obj_self_composable endofunctor_H\<^sub>L [of a] by force
      interpret La: fully_faithful_functor \<open>Left a\<close> \<open>Left a\<close> \<open>H\<^sub>L a\<close>
      proof
        show "\<And>f f'. Left_a.par f f' \<Longrightarrow> H\<^sub>L a f = H\<^sub>L a f' \<Longrightarrow> f = f'"
        proof -
          fix \<mu> \<mu>'
          assume par: "Left_a.par \<mu> \<mu>'"
          assume eq: "H\<^sub>L a \<mu> = H\<^sub>L a \<mu>'"
          have 1: "par \<mu> \<mu>'"
            using par Left_a.arr_char Left_a.dom_char Left_a.cod_char left_def
                  composable_implies_arr null_agreement
            by metis
          moreover have "L \<mu> = L \<mu>'"
            using par eq H\<^sub>L_def Left_a.arr_char left_def preserves_arr
                  assms 1 seq_if_composable [of a \<mu>] not_arr_null seq_if_composable [of a \<mu>']
            by auto
          ultimately show "\<mu> = \<mu>'"
            using L.is_faithful by blast
        qed
        show "\<And>f g \<mu>. \<lbrakk> Left_a.ide f; Left_a.ide g; Left_a.in_hom \<mu> (H\<^sub>L a f) (H\<^sub>L a g) \<rbrakk> \<Longrightarrow>
                        \<exists>\<nu>. Left_a.in_hom \<nu> f g \<and> H\<^sub>L a \<nu> = \<mu>"
        proof -
          fix f g \<mu>
          assume f: "Left_a.ide f" and g: "Left_a.ide g"
          and \<mu>: "Left_a.in_hom \<mu> (H\<^sub>L a f) (H\<^sub>L a g)"
          have 1: "a = trg f \<and> a = trg g"
            using assms f g Left_a.ide_char Left_a.arr_char left_def seq_if_composable [of a f]
                  seq_if_composable [of a g]
            by auto
          show "\<exists>\<nu>. Left_a.in_hom \<nu> f g \<and> H\<^sub>L a \<nu> = \<mu>"
          proof -
            have 2: "\<exists>\<nu>. \<guillemotleft>\<nu> : f \<Rightarrow> g\<guillemotright> \<and> L \<nu> = \<mu>"
              using f g \<mu> 1 Left_a.ide_char H\<^sub>L_def L.preserves_reflects_arr Left_a.arr_char
                    Left_a.in_hom_char L.is_full
              by force
            obtain \<nu> where \<nu>: "\<guillemotleft>\<nu> : f \<Rightarrow> g\<guillemotright> \<and> L \<nu> = \<mu>"
              using 2 by blast
            have "Left_a.arr \<nu>"
              using \<nu> 1 trg_dom Left_a.arr_char left_def hseq_char' by fastforce
            moreover have "H\<^sub>L a \<nu> = \<mu>"
              using \<nu> 1 trg_dom H\<^sub>L_def by auto
            ultimately show ?thesis
              using \<nu> by force
          qed
        qed
      qed
      interpret Ra: endofunctor \<open>Right a\<close> \<open>H\<^sub>R a\<close>
        using assms obj_self_composable endofunctor_H\<^sub>R [of a] by force
      interpret Ra: fully_faithful_functor \<open>Right a\<close> \<open>Right a\<close> \<open>H\<^sub>R a\<close>
      proof
        show "\<And>f f'. Right_a.par f f' \<Longrightarrow> H\<^sub>R a f = H\<^sub>R a f' \<Longrightarrow> f = f'"
        proof -
          fix \<mu> \<mu>'
          assume par: "Right_a.par \<mu> \<mu>'"
          assume eq: "H\<^sub>R a \<mu> = H\<^sub>R a \<mu>'"
          have 1: "par \<mu> \<mu>'"
            using par Right_a.arr_char Right_a.dom_char Right_a.cod_char right_def
                  composable_implies_arr null_agreement
            by metis
          moreover have "R \<mu> = R \<mu>'"
            using par eq H\<^sub>R_def Right_a.arr_char right_def preserves_arr
                  assms 1 seq_if_composable [of \<mu> a] not_arr_null seq_if_composable [of \<mu>' a]
            by auto
          ultimately show "\<mu> = \<mu>'"
            using R.is_faithful by blast
        qed
        show "\<And>f g \<mu>. \<lbrakk> Right_a.ide f; Right_a.ide g; Right_a.in_hom \<mu> (H\<^sub>R a f) (H\<^sub>R a g) \<rbrakk> \<Longrightarrow>
                        \<exists>\<nu>. Right_a.in_hom \<nu> f g \<and> H\<^sub>R a \<nu> = \<mu>"
        proof -
          fix f g \<mu>
          assume f: "Right_a.ide f" and g: "Right_a.ide g"
          and \<mu>: "Right_a.in_hom \<mu> (H\<^sub>R a f) (H\<^sub>R a g)"
          have 1: "a = src f \<and> a = src g"
            using assms f g Right_a.ide_char Right_a.arr_char right_def seq_if_composable
            by auto
          show "\<exists>\<nu>. Right_a.in_hom \<nu> f g \<and> H\<^sub>R a \<nu> = \<mu>"
          proof -
            have 2: "\<exists>\<nu>. \<guillemotleft>\<nu> : f \<Rightarrow> g\<guillemotright> \<and> R \<nu> = \<mu>"
              using f g \<mu> 1 Right_a.ide_char H\<^sub>R_def R.preserves_reflects_arr Right_a.arr_char
                    Right_a.in_hom_char R.is_full
              by force
            obtain \<nu> where \<nu>: "\<guillemotleft>\<nu> : f \<Rightarrow> g\<guillemotright> \<and> R \<nu> = \<mu>"
              using 2 by blast
            have "Right_a.arr \<nu>"
              using \<nu> 1 src_dom Right_a.arr_char right_def hseq_char' by fastforce
            moreover have "H\<^sub>R a \<nu> = \<mu>"
              using \<nu> 1 src_dom H\<^sub>R_def by auto
            ultimately show ?thesis
              using \<nu> by force
          qed
        qed
      qed
      have "isomorphic (a \<star> a) a \<and> a \<star> a \<noteq> null"
        using assms obj_self_composable unit_in_hom iso_unit isomorphic_def by blast
      thus ?thesis
        using La.fully_faithful_functor_axioms Ra.fully_faithful_functor_axioms weak_unit_def
        by blast
    qed

    lemma src_in_sources:
    assumes "arr \<mu>"
    shows "src \<mu> \<in> sources \<mu>"
      using assms obj_is_weak_unit R.preserves_arr hseq_char' by auto

    lemma trg_in_targets:
    assumes "arr \<mu>"
    shows "trg \<mu> \<in> targets \<mu>"
      using assms obj_is_weak_unit L.preserves_arr hseq_char' by auto

    lemma weak_unit_cancel_left:
    assumes "weak_unit a" and "ide f" and "ide g"
    and "a \<star> f \<cong> a \<star> g"
    shows "f \<cong> g"
    proof -
      have 0: "ide a"
        using assms weak_unit_def by force
      interpret Left_a: subcategory V \<open>left a\<close>
        using 0 left_hom_is_subcategory by simp
      interpret Left_a: left_hom V H a
        using assms by unfold_locales auto
      interpret La: fully_faithful_functor \<open>Left a\<close> \<open>Left a\<close> \<open>H\<^sub>L a\<close>
        using assms weak_unit_def by fast
      obtain \<phi> where \<phi>: "iso \<phi> \<and> \<guillemotleft>\<phi> : a \<star> f \<Rightarrow> a \<star> g\<guillemotright>"
        using assms by blast
      have 1: "Left_a.iso \<phi> \<and> Left_a.in_hom \<phi> (a \<star> f) (a \<star> g)"
      proof
        have "a \<star> \<phi> \<noteq> null"
        proof -
          have "a \<star> dom \<phi> \<noteq> null"
            using assms \<phi> weak_unit_self_composable
            by (metis arr_dom_iff_arr hseq_char' in_homE match_4)
          thus ?thesis
            using hom_connected by simp
        qed
        thus "Left_a.in_hom \<phi> (a \<star> f) (a \<star> g)"
          using \<phi> Left_a.hom_char left_def by auto
        thus "Left_a.iso \<phi>"
          using \<phi> Left_a.iso_char by auto
      qed
      hence 2: "Left_a.ide (a \<star> f) \<and> Left_a.ide (a \<star> g)"
        using Left_a.ide_dom [of \<phi>] Left_a.ide_cod [of \<phi>] by auto
      hence 3: "Left_a.ide f \<and> Left_a.ide g"
        by (metis Left_a.ideI Left_a.ide_def Left_a.null_char assms(2) assms(3) left_def)
      obtain \<psi> where \<psi>: "\<psi> \<in> Left_a.hom f g \<and> a \<star> \<psi> = \<phi>"
        using assms 1 2 3 La.is_full [of g f \<phi>] H\<^sub>L_def by auto
      have "Left_a.iso \<psi>"
        using \<psi> 1 H\<^sub>L_def La.reflects_iso by auto
      hence "iso \<psi> \<and> \<guillemotleft>\<psi> : f \<Rightarrow> g\<guillemotright>"
        using \<psi> Left_a.iso_char Left_a.in_hom_char by auto
      thus ?thesis by auto
    qed

    lemma weak_unit_cancel_right:
    assumes "weak_unit a" and "ide f" and "ide g"
    and "f \<star> a \<cong> g \<star> a"
    shows "f \<cong> g"
    proof -
      have 0: "ide a"
        using assms weak_unit_def by force
      interpret Right_a: subcategory V \<open>right a\<close>
        using 0 right_hom_is_subcategory by simp
      interpret Right_a: right_hom V H a
        using assms by unfold_locales auto
      interpret R: fully_faithful_functor \<open>Right a\<close> \<open>Right a\<close> \<open>H\<^sub>R a\<close>
        using assms weak_unit_def by fast
      obtain \<phi> where \<phi>: "iso \<phi> \<and> in_hom \<phi> (f \<star> a) (g \<star> a)"
        using assms by blast
      have 1: "Right_a.iso \<phi> \<and> \<phi> \<in> Right_a.hom (f \<star> a) (g \<star> a)"
      proof
        have "\<phi> \<star> a \<noteq> null"
        proof -
          have "dom \<phi> \<star> a \<noteq> null"
            using assms \<phi> weak_unit_self_composable
            by (metis arr_dom_iff_arr hseq_char' in_homE match_3)
          thus ?thesis
            using hom_connected by simp
        qed
        thus "\<phi> \<in> Right_a.hom (f \<star> a) (g \<star> a)"
          using \<phi> Right_a.hom_char right_def by simp
        thus "Right_a.iso \<phi>"
          using \<phi> Right_a.iso_char by auto
      qed
      hence 2: "Right_a.ide (f \<star> a) \<and> Right_a.ide (g \<star> a)"
        using Right_a.ide_dom [of \<phi>] Right_a.ide_cod [of \<phi>] by auto
      hence 3: "Right_a.ide f \<and> Right_a.ide g"
        using assms Right_a.ide_char Right_a.arr_char right_def Right_a.ide_def Right_a.null_char
        by metis
      obtain \<psi> where \<psi>: "\<psi> \<in> Right_a.hom f g \<and> \<psi> \<star> a = \<phi>"
        using assms 1 2 3 R.is_full [of g f \<phi>] H\<^sub>R_def by auto
      have "Right_a.iso \<psi>"
        using \<psi> 1 H\<^sub>R_def R.reflects_iso by auto
      hence "iso \<psi> \<and> \<guillemotleft>\<psi> : f \<Rightarrow> g\<guillemotright>"
        using \<psi> Right_a.iso_char Right_a.in_hom_char by auto
      thus ?thesis by auto
    qed

    text \<open>
      All sources of an arrow ({\em i.e.}~weak units composable on the right with that arrow)
      are isomorphic to the chosen source, and similarly for targets.  That these statements
      hold was somewhat surprising to me.
    \<close>

    lemma source_iso_src:
    assumes "arr \<mu>" and "a \<in> sources \<mu>"
    shows "a \<cong> src \<mu>"
    proof -
      have 0: "ide a"
        using assms weak_unit_def by force
      have 1: "src a = trg a"
        using assms ide_dom sources_def weak_unit_iff_self_target seq_if_composable
        by simp
      obtain \<phi> where \<phi>: "iso \<phi> \<and> \<guillemotleft>\<phi> : a \<star> a \<Rightarrow> a\<guillemotright>"
        using assms weak_unit_def by blast
      have "a \<star> src a \<cong> src a \<star> src a"
      proof -
        have "src a \<cong> src a \<star> src a"
          using 0 obj_is_weak_unit weak_unit_def isomorphic_symmetric by auto
        moreover have "a \<star> src a \<cong> src a"
        proof -
          have "a \<star> a \<star> src a \<cong> a \<star> src a"
          proof -
            have "iso (\<phi> \<star> src a) \<and> \<guillemotleft>\<phi> \<star> src a : (a \<star> a) \<star> src a \<Rightarrow> a \<star> src a\<guillemotright>"
              using 0 1 \<phi> ide_in_hom(2) by auto
            moreover have "iso \<a>\<^sup>-\<^sup>1[a, a, src a] \<and>
                           \<guillemotleft>\<a>\<^sup>-\<^sup>1[a, a, src a] :  a \<star> a \<star> src a \<Rightarrow> (a \<star> a) \<star> src a\<guillemotright>"
              using 0 1 iso_assoc' by force
            ultimately show ?thesis
              using isos_compose isomorphic_def by auto
          qed
          thus ?thesis
            using assms 0 weak_unit_cancel_left by auto
        qed
        ultimately show ?thesis
          using isomorphic_transitive by meson
      qed
      hence "a \<cong> src a"
        using 0 weak_unit_cancel_right [of "src a" a "src a"] obj_is_weak_unit by auto
      thus ?thesis using assms seq_if_composable 1 by auto
    qed

    lemma target_iso_trg:
    assumes "arr \<mu>" and "b \<in> targets \<mu>"
    shows "b \<cong> trg \<mu>"
    proof -
      have 0: "ide b"
        using assms weak_unit_def by force
      have 1: "trg \<mu> = src b"
        using assms seq_if_composable by auto
      obtain \<phi> where \<phi>: "iso \<phi> \<and> \<guillemotleft>\<phi> : b \<star> b \<Rightarrow> b\<guillemotright>"
        using assms weak_unit_def by blast
      have "trg b \<star> b \<cong> trg b \<star> trg b"
      proof -
        have "trg b \<cong> trg b \<star> trg b"
          using 0 obj_is_weak_unit weak_unit_def isomorphic_symmetric by auto
        moreover have "trg b \<star> b \<cong> trg b"
        proof -
          have "(trg b \<star> b) \<star> b \<cong> trg b \<star> b"
          proof -
            have "iso (trg b \<star> \<phi>) \<and> \<guillemotleft>trg b \<star> \<phi> : trg b \<star> b \<star> b \<Rightarrow> trg b \<star> b\<guillemotright>"
              using assms 0 1 \<phi> ide_in_hom(2) targetsD(1)
              apply (intro conjI hcomp_in_vhom) by auto
            moreover have "iso \<a>[trg b, b, b] \<and>
                           \<guillemotleft>\<a>[trg b, b, b] : (trg b \<star> b) \<star> b \<Rightarrow> trg b \<star> b \<star> b\<guillemotright>"
              using assms(2) 0 1 seq_if_composable targetsD(1-2) by auto
            ultimately show ?thesis
              using isos_compose isomorphic_def by auto
          qed
          thus ?thesis
            using assms 0 weak_unit_cancel_right by auto
        qed
        ultimately show ?thesis
          using isomorphic_transitive by meson
      qed
      hence "b \<cong> trg b"
        using 0 weak_unit_cancel_left [of "trg b" b "trg b"] obj_is_weak_unit by simp
      thus ?thesis
        using assms 0 1 seq_if_composable weak_unit_iff_self_source targetsD(1-2) source_iso_src
        by simp
    qed

    lemma is_weak_composition_with_homs:
    shows "weak_composition_with_homs V H src trg"
      using src_in_sources trg_in_targets seq_if_composable composable_implies_arr
      by (unfold_locales, simp_all)

    interpretation weak_composition_with_homs V H src trg
      using is_weak_composition_with_homs by auto

    text \<open>
      In a bicategory, the notion of composability defined in terms of
      the chosen sources and targets coincides with the version defined
      for a weak composition, which does not involve particular choices.
    \<close>

    lemma connected_iff_seq:
    assumes "arr \<mu>" and "arr \<nu>"
    shows "sources \<nu> \<inter> targets \<mu> \<noteq> {} \<longleftrightarrow> src \<nu> = trg \<mu>"
    proof
      show "src \<nu> = trg \<mu> \<Longrightarrow> sources \<nu> \<inter> targets \<mu> \<noteq> {}"
        using assms src_in_sources [of \<nu>] trg_in_targets [of \<mu>] by auto
      show "sources \<nu> \<inter> targets \<mu> \<noteq> {} \<Longrightarrow> src \<nu> = trg \<mu>"
      proof -
        assume 1: "sources \<nu> \<inter> targets \<mu> \<noteq> {}"
        obtain a where a: "a \<in> sources \<nu> \<inter> targets \<mu>"
          using assms 1 by blast
        have \<mu>: "arr \<mu>"
          using a composable_implies_arr by auto
        have \<nu>: "arr \<nu>"
          using a composable_implies_arr by auto
        have 1: "\<And>a'. a' \<in> sources \<nu> \<Longrightarrow> src a' = src a \<and> trg a' = trg a"
        proof
          fix a'
          assume a': "a' \<in> sources \<nu>"
          have 1: "a' \<cong> a"
            using a a' \<nu> src_dom sources_dom source_iso_src isomorphic_transitive
                  isomorphic_symmetric
            by (meson IntD1)
          obtain \<phi> where \<phi>: "iso \<phi> \<and> \<phi> \<in> hom a' a"
            using 1 by auto
          show "src a' = src a"
            using \<phi> src_dom src_cod by auto
          show "trg a' = trg a"
            using \<phi> trg_dom trg_cod by auto
        qed
        have 2: "\<And>a'. a' \<in> targets \<mu> \<Longrightarrow> src a' = src a \<and> trg a' = trg a"
        proof
          fix a'
          assume a': "a' \<in> targets \<mu>"
          have 1: "a' \<cong> a"
            using a a' \<mu> trg_dom targets_dom target_iso_trg isomorphic_transitive
                  isomorphic_symmetric
            by (meson IntD2)
          obtain \<phi> where \<phi>: "iso \<phi> \<and> \<phi> \<in> hom a' a"
            using 1 by auto
          show "src a' = src a"
            using \<phi> src_dom src_cod by auto
          show "trg a' = trg a"
            using \<phi> trg_dom trg_cod by auto
        qed
        have "src \<nu> = src (src \<nu>)" using \<nu> by simp
        also have "... = src (trg \<mu>)"
          using \<nu> 1 [of "src \<nu>"] src_in_sources a weak_unit_self_composable seq_if_composable
          by auto
        also have "... = trg (trg \<mu>)" using \<mu> by simp
        also have "... = trg \<mu>" using \<mu> by simp
        finally show "src \<nu> = trg \<mu>" by blast
      qed
    qed

    lemma is_associative_weak_composition:
    shows "associative_weak_composition V H \<a>"
    proof -
      have 1: "\<And>\<nu> \<mu>. \<nu> \<star> \<mu> \<noteq> null \<Longrightarrow> src \<nu> = trg \<mu>"
        using H.is_extensional VV.arr_char by force
      show "associative_weak_composition V H \<a>"
      proof
        show "\<And>f g h. ide f \<Longrightarrow> ide g \<Longrightarrow> ide h \<Longrightarrow> f \<star> g \<noteq> null \<Longrightarrow> g \<star> h \<noteq> null \<Longrightarrow>
                      \<guillemotleft>\<a>[f, g, h] : (f \<star> g) \<star> h \<Rightarrow> f \<star> g \<star> h\<guillemotright>"
          using 1 by auto
        show "\<And>f g h. ide f \<Longrightarrow> ide g \<Longrightarrow> ide h \<Longrightarrow> f \<star> g \<noteq> null \<Longrightarrow> g \<star> h \<noteq> null \<Longrightarrow>
                      iso \<a>[f, g, h]"
          using 1 iso_assoc by presburger
        show "\<And>\<tau> \<mu> \<nu>. \<tau> \<star> \<mu> \<noteq> null \<Longrightarrow> \<mu> \<star> \<nu> \<noteq> null \<Longrightarrow>
                      \<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> ((\<tau> \<star> \<mu>) \<star> \<nu>) = (\<tau> \<star> \<mu> \<star> \<nu>) \<cdot> \<a>[dom \<tau>, dom \<mu>, dom \<nu>]"
           using 1 assoc_naturality hseq_char hseq_char' by metis
        show "\<And>f g h k. ide f \<Longrightarrow> ide g \<Longrightarrow> ide h \<Longrightarrow> ide k \<Longrightarrow>
                         sources f \<inter> targets g \<noteq> {} \<Longrightarrow>
                         sources g \<inter> targets h \<noteq> {} \<Longrightarrow>
                         sources h \<inter> targets k \<noteq> {} \<Longrightarrow>
                        (f \<star> \<a>[g, h, k]) \<cdot> \<a>[f, g \<star> h, k] \<cdot> (\<a>[f, g, h] \<star> k) =
                        \<a>[f, g, h \<star> k] \<cdot> \<a>[f \<star> g, h, k]"
           using 1 connected_iff_seq pentagon ideD(1) by auto
      qed
    qed

    interpretation associative_weak_composition V H \<a>
      using is_associative_weak_composition by auto

    theorem is_prebicategory:
    shows "prebicategory V H \<a>"
      using src_in_sources trg_in_targets by (unfold_locales, auto)

    interpretation prebicategory V H \<a>
      using is_prebicategory by auto

    corollary is_prebicategory_with_homs:
    shows "prebicategory_with_homs V H \<a> src trg"
      ..

    interpretation prebicategory_with_homs V H \<a> src trg
      using is_prebicategory_with_homs by auto

    text \<open>
      In a bicategory, an arrow is a weak unit if and only if it is
      isomorphic to its chosen source (or to its chosen target).
    \<close>

    lemma weak_unit_char:
    shows "weak_unit a \<longleftrightarrow> a \<cong> src a"
    and "weak_unit a \<longleftrightarrow> a \<cong> trg a"
    proof -
      show "weak_unit a \<longleftrightarrow> a \<cong> src a"
        using isomorphism_respects_weak_units isomorphic_symmetric
        by (meson ideD(1) isomorphic_implies_ide(2) obj_is_weak_unit obj_src source_iso_src
            weak_unit_iff_self_source weak_unit_self_composable(1))
      show "weak_unit a \<longleftrightarrow> a \<cong> trg a"
        using isomorphism_respects_weak_units isomorphic_symmetric
        by (metis \<open>weak_unit a = isomorphic a (src a)\<close> ideD(1) isomorphic_implies_hpar(3)
            isomorphic_implies_ide(1) src_trg target_iso_trg weak_unit_iff_self_target)
    qed
        
    interpretation H: partial_magma H
      using is_partial_magma by auto

    text \<open>
      Every arrow with respect to horizontal composition is also an arrow with respect
      to vertical composition.  The converse is not necessarily true.
    \<close>

    lemma harr_is_varr:
    assumes "H.arr \<mu>"
    shows "arr \<mu>"
    proof -
      have "H.domains \<mu> \<noteq> {} \<Longrightarrow> arr \<mu>"
      proof -
        assume 1: "H.domains \<mu> \<noteq> {}"
        obtain a where a: "H.ide a \<and> \<mu> \<star> a \<noteq> null"
          using 1 H.domains_def by auto
        show "arr \<mu>"
          using a hseq_char' H.ide_def by blast
      qed
      moreover have "H.codomains \<mu> \<noteq> {} \<Longrightarrow> arr \<mu>"
      proof -
        assume 1: "H.codomains \<mu> \<noteq> {}"
        obtain a where a: "H.ide a \<and> a \<star> \<mu> \<noteq> null"
          using 1 H.codomains_def by auto
        show "arr \<mu>"
          using a hseq_char' ide_def by blast
      qed
      ultimately show ?thesis using assms H.arr_def by auto
    qed

    text \<open>
      An identity for horizontal composition is also an identity for vertical composition.
    \<close>

    lemma horizontal_identity_is_ide:
    assumes "H.ide \<mu>"
    shows "ide \<mu>"
    proof -
      have \<mu>: "arr \<mu>"
        using assms H.ide_def composable_implies_arr(2) by auto
      hence 1: "\<mu> \<star> dom \<mu> \<noteq> null"
        using assms hom_connected H.ide_def by auto
      have "\<mu> \<star> dom \<mu> = dom \<mu>"
        using assms 1 H.ide_def by simp
      moreover have "\<mu> \<star> dom \<mu> = \<mu>"
        using assms 1 H.ide_def [of \<mu>] null_agreement
        by (metis \<mu> cod_cod cod_dom hcomp_simps\<^sub>W\<^sub>C(3) ideD(2) ide_char' paste_1)
      ultimately have "dom \<mu> = \<mu>"
        by simp
      thus ?thesis
        using \<mu> by (metis ide_dom)
    qed

    text \<open>
      Every identity for horizontal composition is a weak unit.
    \<close>

    lemma horizontal_identity_is_weak_unit:
    assumes "H.ide \<mu>"
    shows "weak_unit \<mu>"
      using assms weak_unit_char
      by (metis H.ide_def comp_target_ide horizontal_identity_is_ide ideD(1)
          isomorphism_respects_weak_units null_agreement targetsD(2-3) trg_in_targets)

  end

  subsection "Vertically Discrete Bicategories are Categories"

  text \<open>
    In this section we show that if a bicategory is discrete with respect to vertical
    composition, then it is a category with respect to horizontal composition.
    To obtain this result, we need to establish that the set of arrows for the horizontal
    composition coincides with the set of arrows for the vertical composition.
    This is not true for a general bicategory, and even with the assumption that the
    vertical category is discrete it is not immediately obvious from the definitions.
    The issue is that the notion ``arrow'' for the horizontal composition is defined
    in terms of the existence of ``domains'' and ``codomains'' with respect to that
    composition, whereas the axioms for a bicategory only relate the notion ``arrow''
    for the vertical category to the existence of sources and targets with respect
    to the horizontal composition.
    So we have to establish that, under the assumption of vertical discreteness,
    sources coincide with domains and targets coincide with codomains.
    We also need the fact that horizontal identities are weak units, which previously
    required some effort to show.
  \<close>

  locale vertically_discrete_bicategory =
    bicategory +
  assumes vertically_discrete: "ide = arr"
  begin

    interpretation prebicategory_with_homs V H \<a> src trg
      using is_prebicategory_with_homs by auto

    interpretation H: partial_magma H
      using is_partial_magma(1) by auto

    lemma weak_unit_is_horizontal_identity:
    assumes "weak_unit a"
    shows "H.ide a"
    proof -
      have "a \<star> a \<noteq> H.null"
        using assms by simp
      moreover have "\<And>f. f \<star> a \<noteq> H.null \<Longrightarrow> f \<star> a = f"
      proof -
        fix f
        assume "f \<star> a \<noteq> H.null"
        hence "f \<star> a \<cong> f"
          using assms comp_ide_source composable_implies_arr(2) sourcesI vertically_discrete
          by auto
        thus "f \<star> a = f"
          using vertically_discrete isomorphic_def by auto
      qed
      moreover have "\<And>f. a \<star> f \<noteq> H.null \<Longrightarrow> a \<star> f = f"
      proof -
        fix f
        assume "a \<star> f \<noteq> H.null"
        hence "a \<star> f \<cong> f"
          using assms comp_target_ide composable_implies_arr(1) targetsI vertically_discrete
          by auto
        thus "a \<star> f = f"
          using vertically_discrete isomorphic_def by auto
      qed
      ultimately show "H.ide a"
        using H.ide_def by simp
    qed

    lemma sources_eq_domains:
    shows "sources \<mu> = H.domains \<mu>"
      using weak_unit_is_horizontal_identity H.domains_def sources_def
            horizontal_identity_is_weak_unit
      by auto

    lemma targets_eq_codomains:
    shows "targets \<mu> = H.codomains \<mu>"
      using weak_unit_is_horizontal_identity H.codomains_def targets_def
            horizontal_identity_is_weak_unit
      by auto

    lemma arr_agreement:
    shows "arr = H.arr"
      using arr_def H.arr_def arr_iff_has_src arr_iff_has_trg
            sources_eq_domains targets_eq_codomains
      by auto

    interpretation H: category H
    proof
      show "\<And>g f. g \<star> f \<noteq> H.null \<Longrightarrow> H.seq g f"
        using arr_agreement hcomp_simps\<^sub>W\<^sub>C(1) by auto
      show "\<And>f. (H.domains f \<noteq> {}) = (H.codomains f \<noteq> {})"
        using sources_eq_domains targets_eq_codomains arr_iff_has_src arr_iff_has_trg
        by simp
      fix f g h
      show "H.seq h g \<Longrightarrow> H.seq (h \<star> g) f \<Longrightarrow> H.seq g f"
        using null_agreement arr_agreement H.not_arr_null preserves_arr VoV.arr_char
        by (metis hseq_char' match_1)
      show "H.seq h (g \<star> f) \<Longrightarrow> H.seq g f \<Longrightarrow> H.seq h g"
        using null_agreement arr_agreement H.not_arr_null preserves_arr VoV.arr_char
        by (metis hseq_char' match_2)
      show "H.seq g f \<Longrightarrow> H.seq h g \<Longrightarrow> H.seq (h \<star> g) f"
        using arr_agreement match_3 hseq_char(1) by auto
      show "H.seq g f \<Longrightarrow> H.seq h g \<Longrightarrow> (h \<star> g) \<star> f = h \<star> g \<star> f"
      proof -
        assume hg: "H.seq h g"
        assume gf: "H.seq g f"
        have "iso \<a>[h, g, f] \<and> \<guillemotleft>\<a>[h, g, f] : (h \<star> g) \<star> f \<Rightarrow> h \<star> g \<star> f\<guillemotright>"
          using hg gf vertically_discrete arr_agreement hseq_char assoc_in_hom iso_assoc
          by auto
        thus ?thesis
          using arr_agreement vertically_discrete by auto
      qed
    qed

    proposition is_category:
    shows "category H"
      ..

  end

  subsection "Obtaining the Unitors"

  text \<open>
    We now want to exploit the construction of unitors in a prebicategory with units,
    to obtain left and right unitors in a bicategory.  However, a bicategory is not
    \emph{a priori} a prebicategory with units, because a bicategory only assigns unit
    isomorphisms to each \emph{object}, not to each weak unit.  In order to apply the results
    about prebicategories with units to a bicategory, we first need to extend the bicategory to
    a prebicategory with units, by extending the mapping \<open>\<iota>\<close>, which provides a unit isomorphism
    for each object, to a mapping that assigns a unit isomorphism to all weak units.
    This extension can be made in an arbitrary way, as the values chosen for
    non-objects ultimately do not affect the components of the unitors at objects.
  \<close>

  context bicategory
  begin

    interpretation prebicategory V H \<a>
      using is_prebicategory by auto

    definition \<i>'
    where "\<i>' a \<equiv> SOME \<phi>. iso \<phi> \<and> \<phi> \<in> hom (a \<star> a) a \<and> (obj a \<longrightarrow> \<phi> = \<i>[a])"

    lemma \<i>'_extends_\<i>:
    assumes "weak_unit a"
    shows "iso (\<i>' a)" and "\<guillemotleft>\<i>' a : a \<star> a \<Rightarrow> a\<guillemotright>" and "obj a \<Longrightarrow> \<i>' a = \<i>[a]"
    proof -
      let ?P = "\<lambda>a \<phi>. iso \<phi> \<and> \<guillemotleft>\<phi> : a \<star> a \<Rightarrow> a\<guillemotright> \<and> (obj a \<longrightarrow> \<phi> = \<i>[a])"
      have "\<exists>\<phi>. ?P a \<phi>"
        using assms unit_in_hom iso_unit weak_unit_def isomorphic_def by blast
      hence 1: "?P a (\<i>' a)"
        using \<i>'_def someI_ex [of "?P a"] by simp
      show "iso (\<i>' a)" using 1 by simp
      show "\<guillemotleft>\<i>' a : a \<star> a \<Rightarrow> a\<guillemotright>" using 1 by simp
      show "obj a \<Longrightarrow> \<i>' a = \<i>[a]" using 1 by simp
    qed

    proposition extends_to_prebicategory_with_units:
    shows "prebicategory_with_units V H \<a> \<i>'"
      using \<i>'_extends_\<i> by unfold_locales auto

    interpretation PB: prebicategory_with_units V H \<a> \<i>'
      using extends_to_prebicategory_with_units by auto
    interpretation PB: prebicategory_with_homs V H \<a> src trg
      using is_prebicategory_with_homs by auto
    interpretation PB: prebicategory_with_homs_and_units V H \<a> \<i>' src trg ..

    proposition extends_to_prebicategory_with_homs_and_units:
    shows "prebicategory_with_homs_and_units V H \<a> \<i>' src trg"
      ..

    definition lunit                 ("\<l>[_]")
    where "\<l>[a] \<equiv> PB.lunit a"

    definition runit                 ("\<r>[_]")
    where "\<r>[a] \<equiv> PB.runit a"

    abbreviation lunit'              ("\<l>\<^sup>-\<^sup>1[_]")
    where "\<l>\<^sup>-\<^sup>1[a] \<equiv> inv \<l>[a]"

    abbreviation runit'              ("\<r>\<^sup>-\<^sup>1[_]")
    where "\<r>\<^sup>-\<^sup>1[a] \<equiv> inv \<r>[a]"

    text \<open>
      \sloppypar
      The characterizations of the left and right unitors that we obtain from locale
      @{locale prebicategory_with_homs_and_units} mention the arbitarily chosen extension \<open>\<i>'\<close>,
      rather than the given \<open>\<i>\<close>.  We want ``native versions'' for the present context.
    \<close>

    lemma lunit_char:
    assumes "ide f"
    shows "\<guillemotleft>\<l>[f] : L f \<Rightarrow> f\<guillemotright>" and "L \<l>[f] = (\<i>[trg f] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[trg f, trg f, f]"
    and "\<exists>!\<mu>. \<guillemotleft>\<mu> : L f \<Rightarrow> f\<guillemotright> \<and> L \<mu> = (\<i>[trg f] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[trg f, trg f, f]"
    proof -
      have 1: "trg (PB.lunit f) = trg f"
        using assms PB.lunit_char [of f] vconn_implies_hpar(2) vconn_implies_hpar(4)
        by metis
      show "\<guillemotleft>\<l>[f] : L f \<Rightarrow> f\<guillemotright>"
        unfolding lunit_def
        using assms PB.lunit_char by simp
      show "L \<l>[f] = (\<i>[trg f] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[trg f, trg f, f]"
        unfolding lunit_def
        using assms 1 PB.lunit_char obj_is_weak_unit \<i>'_extends_\<i> by simp
      let ?P = "\<lambda>\<mu>. \<guillemotleft>\<mu> : L f \<Rightarrow> f\<guillemotright> \<and> L \<mu> = (\<i>[trg f] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[trg f, trg f, f]"
      have "?P = (\<lambda>\<mu>. \<guillemotleft>\<mu> : trg f \<star> f \<Rightarrow> f\<guillemotright> \<and>
                      trg f \<star> \<mu> = (\<i>' (trg f) \<star> f) \<cdot> inv \<a>[trg f, trg f, f])"
      proof -
        have "\<And>\<mu>. \<guillemotleft>\<mu> : L f \<Rightarrow> f\<guillemotright> \<longleftrightarrow> \<guillemotleft>\<mu> : trg f \<star> f \<Rightarrow> f\<guillemotright>"
          using assms by simp
        moreover have "\<And>\<mu>. \<guillemotleft>\<mu> : L f \<Rightarrow> f\<guillemotright> \<Longrightarrow>
                            L \<mu> = (\<i>[trg f] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[trg f, trg f, f] \<longleftrightarrow>
                            trg f \<star> \<mu> = (\<i>' (trg f) \<star> f) \<cdot> inv \<a>[trg f, trg f, f]"
          using calculation obj_is_weak_unit \<i>'_extends_\<i> by auto
        ultimately show ?thesis by blast
      qed
      thus "\<exists>!\<mu>. \<guillemotleft>\<mu> : L f \<Rightarrow> f\<guillemotright> \<and> L \<mu> = (\<i>[trg f] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[trg f, trg f, f]"
        using assms PB.lunit_char by simp
    qed

    lemma lunit_in_hom [intro]:
    assumes "ide f"
    shows "\<guillemotleft>\<l>[f] : src f \<rightarrow> trg f\<guillemotright>" and "\<guillemotleft>\<l>[f] : trg f \<star> f \<Rightarrow> f\<guillemotright>"
    proof -
      show "\<guillemotleft>\<l>[f] : trg f \<star> f \<Rightarrow> f\<guillemotright>"
        using assms lunit_char by auto
      thus "\<guillemotleft>\<l>[f] : src f \<rightarrow> trg f\<guillemotright>"
        using src_cod trg_cod by fastforce
    qed

    lemma lunit_in_vhom [simp]:
    assumes "ide f" and "trg f = b"
    shows "\<guillemotleft>\<l>[f] : b \<star> f \<Rightarrow> f\<guillemotright>"
      using assms by auto

    lemma lunit_simps [simp]:
    assumes "ide f"
    shows "arr \<l>[f]" and "src \<l>[f] = src f" and "trg \<l>[f] = trg f"
    and "dom \<l>[f] = trg f \<star> f" and "cod \<l>[f] = f"
      using assms lunit_in_hom
          apply auto
      using assms lunit_in_hom
       apply blast
      using assms lunit_in_hom
      by blast

    lemma runit_char:
    assumes "ide f"
    shows "\<guillemotleft>\<r>[f] : R f \<Rightarrow> f\<guillemotright>" and "R \<r>[f] = (f \<star> \<i>[src f]) \<cdot> \<a>[f, src f, src f]"
    and "\<exists>!\<mu>. \<guillemotleft>\<mu> : R f \<Rightarrow> f\<guillemotright> \<and> R \<mu> = (f \<star> \<i>[src f]) \<cdot> \<a>[f, src f, src f]"
    proof -
      have 1: "src (PB.runit f) = src f"
        using assms PB.runit_char [of f] vconn_implies_hpar(1) vconn_implies_hpar(3)
        by metis
      show "\<guillemotleft>\<r>[f] : R f \<Rightarrow> f\<guillemotright>"
        unfolding runit_def
        using assms PB.runit_char by simp
      show "R \<r>[f] = (f \<star> \<i>[src f]) \<cdot> \<a>[f, src f, src f]"
        unfolding runit_def
        using assms 1 PB.runit_char obj_is_weak_unit \<i>'_extends_\<i> by simp
      let ?P = "\<lambda>\<mu>. \<guillemotleft>\<mu> : R f \<Rightarrow> f\<guillemotright> \<and> R \<mu> = (f \<star> \<i>[src f]) \<cdot> \<a>[f, src f, src f]"
      have "?P = (\<lambda>\<mu>. \<guillemotleft>\<mu> : f \<star> src f \<Rightarrow> f\<guillemotright> \<and>
                      \<mu> \<star> src f = (f \<star> \<i>' (src f)) \<cdot>  \<a>[f, src f, src f])"
      proof -
        have "\<And>\<mu>. \<guillemotleft>\<mu> : R f \<Rightarrow> f\<guillemotright> \<longleftrightarrow> \<guillemotleft>\<mu> : f \<star> src f \<Rightarrow> f\<guillemotright>"
          using assms by simp
        moreover have "\<And>\<mu>. \<guillemotleft>\<mu> : R f \<Rightarrow> f\<guillemotright> \<Longrightarrow>
                            R \<mu> = (f \<star> \<i>[src f]) \<cdot> \<a>[f, src f, src f] \<longleftrightarrow>
                            \<mu> \<star> src f = (f \<star> \<i>' (src f)) \<cdot>  \<a>[f, src f, src f]"
          using calculation obj_is_weak_unit \<i>'_extends_\<i> by auto
        ultimately show ?thesis by blast
      qed
      thus "\<exists>!\<mu>. \<guillemotleft>\<mu> : R f \<Rightarrow> f\<guillemotright> \<and> R \<mu> = (f \<star> \<i>[src f]) \<cdot> \<a>[f, src f, src f]"
        using assms PB.runit_char by simp
    qed

    lemma runit_in_hom [intro]:
    assumes "ide f"
    shows "\<guillemotleft>\<r>[f] : src f \<rightarrow> trg f\<guillemotright>" and "\<guillemotleft>\<r>[f] : f \<star> src f \<Rightarrow> f\<guillemotright>"
    proof -
      show "\<guillemotleft>\<r>[f] : f \<star> src f \<Rightarrow> f\<guillemotright>"
        using assms runit_char by auto
      thus "\<guillemotleft>\<r>[f] : src f \<rightarrow> trg f\<guillemotright>"
        using src_cod trg_cod by fastforce
    qed

    lemma runit_in_vhom [simp]:
    assumes "ide f" and "src f = a"
    shows "\<guillemotleft>\<r>[f] : f \<star> a \<Rightarrow> f\<guillemotright>"
      using assms by auto

    lemma runit_simps [simp]:
    assumes "ide f"
    shows "arr \<r>[f]" and "src \<r>[f] = src f" and "trg \<r>[f] = trg f"
    and "dom \<r>[f] = f \<star> src f" and "cod \<r>[f] = f"
      using assms runit_in_hom
          apply auto
      using assms runit_in_hom
       apply blast
      using assms runit_in_hom
      by blast

    lemma lunit_eqI:
    assumes "ide f" and "\<guillemotleft>\<mu> : trg f \<star> f \<Rightarrow> f\<guillemotright>"
    and "trg f \<star> \<mu> = (\<i>[trg f] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[trg f, trg f, f]"
    shows "\<mu> = \<l>[f]"
      unfolding lunit_def
      using assms PB.lunit_eqI \<i>'_extends_\<i> trg.preserves_ide obj_is_weak_unit by simp

    lemma runit_eqI:
    assumes "ide f" and "\<guillemotleft>\<mu> : f \<star> src f \<Rightarrow> f\<guillemotright>"
    and "\<mu> \<star> src f = (f \<star> \<i>[src f]) \<cdot> \<a>[f, src f, src f]"
    shows "\<mu> = \<r>[f]"
      unfolding runit_def
      using assms PB.runit_eqI \<i>'_extends_\<i> src.preserves_ide obj_is_weak_unit by simp

    lemma lunit_naturality:
    assumes "arr \<mu>"
    shows "\<mu> \<cdot> \<l>[dom \<mu>] = \<l>[cod \<mu>] \<cdot> (trg \<mu> \<star> \<mu>)"
      unfolding lunit_def
      using assms PB.lunit_naturality by auto

    lemma runit_naturality:
    assumes "arr \<mu>"
    shows "\<mu> \<cdot> \<r>[dom \<mu>] = \<r>[cod \<mu>] \<cdot> (\<mu> \<star> src \<mu>)"
      unfolding runit_def
      using assms PB.runit_naturality by auto

    lemma iso_lunit [simp]:
    assumes "ide f"
    shows "iso \<l>[f]"
      unfolding lunit_def
      using assms PB.iso_lunit by blast

    lemma iso_runit [simp]:
    assumes "ide f"
    shows "iso \<r>[f]"
      unfolding runit_def
      using assms PB.iso_runit by blast

    lemma iso_lunit' [simp]:
    assumes "ide f"
    shows "iso \<l>\<^sup>-\<^sup>1[f]"
      using assms iso_lunit iso_inv_iso by blast

    lemma iso_runit' [simp]:
    assumes "ide f"
    shows "iso \<r>\<^sup>-\<^sup>1[f]"
      using assms iso_runit iso_inv_iso by blast

    lemma lunit'_in_hom [intro]:
    assumes "ide f"
    shows "\<guillemotleft>\<l>\<^sup>-\<^sup>1[f] : src f \<rightarrow> trg f\<guillemotright>" and "\<guillemotleft>\<l>\<^sup>-\<^sup>1[f] : f \<Rightarrow> trg f \<star> f\<guillemotright>"
    proof -
      show "\<guillemotleft>\<l>\<^sup>-\<^sup>1[f] : f \<Rightarrow> trg f \<star> f\<guillemotright>"
        using assms lunit_char iso_lunit by simp
      thus "\<guillemotleft>\<l>\<^sup>-\<^sup>1[f] : src f \<rightarrow> trg f\<guillemotright>"
        using assms src_dom trg_dom by simp
    qed

    lemma lunit'_in_vhom [simp]:
    assumes "ide f" and "trg f = b"
    shows "\<guillemotleft>\<l>\<^sup>-\<^sup>1[f] : f \<Rightarrow> b \<star> f\<guillemotright>"
      using assms by auto

    lemma lunit'_simps [simp]:
    assumes "ide f"
    shows "arr \<l>\<^sup>-\<^sup>1[f]" and "src \<l>\<^sup>-\<^sup>1[f] = src f" and "trg \<l>\<^sup>-\<^sup>1[f] = trg f"
    and "dom \<l>\<^sup>-\<^sup>1[f] = f" and "cod \<l>\<^sup>-\<^sup>1[f] = trg f \<star> f"
      using assms lunit'_in_hom by auto

    lemma runit'_in_hom [intro]:
    assumes "ide f"
    shows "\<guillemotleft>\<r>\<^sup>-\<^sup>1[f] : src f \<rightarrow> trg f\<guillemotright>" and "\<guillemotleft>\<r>\<^sup>-\<^sup>1[f] : f \<Rightarrow> f \<star> src f\<guillemotright>"
    proof -
      show "\<guillemotleft>\<r>\<^sup>-\<^sup>1[f] : f \<Rightarrow> f \<star> src f\<guillemotright>"
        using assms runit_char iso_runit by simp
      thus "\<guillemotleft>\<r>\<^sup>-\<^sup>1[f] : src f \<rightarrow> trg f\<guillemotright>"
        using src_dom trg_dom
        by (simp add: assms)
    qed

    lemma runit'_in_vhom [simp]:
    assumes "ide f" and "src f = a"
    shows "\<guillemotleft>\<r>\<^sup>-\<^sup>1[f] : f \<Rightarrow> f \<star> a\<guillemotright>"
      using assms by auto

    lemma runit'_simps [simp]:
    assumes "ide f"
    shows "arr \<r>\<^sup>-\<^sup>1[f]" and "src \<r>\<^sup>-\<^sup>1[f] = src f" and "trg \<r>\<^sup>-\<^sup>1[f] = trg f"
    and "dom \<r>\<^sup>-\<^sup>1[f] = f" and "cod \<r>\<^sup>-\<^sup>1[f] = f \<star> src f"
      using assms runit'_in_hom by auto

    interpretation L: endofunctor V L ..
    interpretation \<ll>: transformation_by_components V V L map lunit
      using lunit_in_hom lunit_naturality by unfold_locales auto
    interpretation \<ll>: natural_isomorphism V V L map \<ll>.map
      using iso_lunit by (unfold_locales, auto)

    lemma natural_isomorphism_\<ll>:
    shows "natural_isomorphism V V L map \<ll>.map"
      ..

    abbreviation \<ll>
    where "\<ll> \<equiv> \<ll>.map"

    lemma \<ll>_ide_simp:
    assumes "ide f"
    shows "\<ll> f = \<l>[f]"
      using assms by simp

    interpretation L: equivalence_functor V V L
      using L.isomorphic_to_identity_is_equivalence \<ll>.natural_isomorphism_axioms by simp

    lemma equivalence_functor_L:
    shows "equivalence_functor V V L"
      ..

    lemma lunit_commutes_with_L:
    assumes "ide f"
    shows "\<l>[L f] = L \<l>[f]"
      unfolding lunit_def
      using assms PB.lunit_commutes_with_L by blast

    interpretation R: endofunctor V R ..
    interpretation \<rr>: transformation_by_components V V R map runit
      using runit_in_hom runit_naturality by unfold_locales auto
    interpretation \<rr>: natural_isomorphism V V R map \<rr>.map
      using iso_runit by (unfold_locales, auto)

    lemma natural_isomorphism_\<rr>:
    shows "natural_isomorphism V V R map \<rr>.map"
      ..

    abbreviation \<rr>
    where "\<rr> \<equiv> \<rr>.map"

    lemma \<rr>_ide_simp:
    assumes "ide f"
    shows "\<rr> f = \<r>[f]"
      using assms by simp

    interpretation R: equivalence_functor V V R
      using R.isomorphic_to_identity_is_equivalence \<rr>.natural_isomorphism_axioms by simp

    lemma equivalence_functor_R:
    shows "equivalence_functor V V R"
      ..

    lemma runit_commutes_with_R:
    assumes "ide f"
    shows "\<r>[R f] = R \<r>[f]"
      unfolding runit_def
      using assms PB.runit_commutes_with_R by blast

    lemma lunit'_naturality:
    assumes "arr \<mu>"
    shows "(trg \<mu> \<star> \<mu>) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu>] = \<l>\<^sup>-\<^sup>1[cod \<mu>] \<cdot> \<mu>"
      using assms iso_lunit lunit_naturality invert_opposite_sides_of_square L.preserves_arr
            L.preserves_cod arr_cod ide_cod ide_dom lunit_simps(1) lunit_simps(4) seqI
      by presburger

    lemma runit'_naturality:
    assumes "arr \<mu>"
    shows "(\<mu> \<star> src \<mu>) \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>] = \<r>\<^sup>-\<^sup>1[cod \<mu>] \<cdot> \<mu>"
      using assms iso_runit runit_naturality invert_opposite_sides_of_square R.preserves_arr
            R.preserves_cod arr_cod ide_cod ide_dom runit_simps(1) runit_simps(4) seqI
      by presburger

  end

  subsection "Further Properties of Bicategories"

  text \<open>
    Here we derive further properties of bicategories, now that we
    have the unitors at our disposal.  This section generalizes the corresponding
    development in theory @{theory MonoidalCategory.MonoidalCategory},
    which has some diagrams to illustrate the longer calculations.
    The present section also includes some additional facts that are now nontrivial
    due to the partiality of horizontal composition.
  \<close>

  context bicategory
  begin

    lemma unit_simps [simp]:
    assumes "obj a"
    shows "arr \<i>[a]" and "src \<i>[a] = a" and "trg \<i>[a] = a"
    and "dom \<i>[a] = a \<star> a" and "cod \<i>[a] = a"
      using assms unit_in_hom by blast+

    lemma triangle:
    assumes "ide f" and "ide g" and "src g = trg f"
    shows "(g \<star> \<l>[f]) \<cdot> \<a>[g, src g, f] = \<r>[g] \<star> f"
    proof -
      let ?b = "src g"
      have *: "(g \<star> \<l>[?b \<star> f]) \<cdot> \<a>[g, ?b, ?b \<star> f] = \<r>[g] \<star> ?b \<star> f"
      proof -
        have 1: "((g \<star> \<l>[?b \<star> f]) \<cdot> \<a>[g, ?b, ?b \<star> f]) \<cdot> \<a>[g \<star> ?b, ?b, f]
                    = (\<r>[g] \<star> ?b \<star> f) \<cdot> \<a>[g \<star> ?b, ?b, f]"
        proof -
          have "((g \<star> \<l>[?b \<star> f]) \<cdot> \<a>[g, ?b, ?b \<star> f]) \<cdot> \<a>[g \<star> ?b, ?b, f]
                  = (g \<star> \<l>[?b \<star> f]) \<cdot> \<a>[g, ?b, ?b \<star> f] \<cdot> \<a>[g \<star> ?b, ?b, f]"
            using HoVH_def HoHV_def comp_assoc by auto
          also have
              "... = (g \<star> \<l>[?b \<star> f]) \<cdot> (g \<star> \<a>[?b, ?b, f]) \<cdot> \<a>[g, ?b \<star> ?b, f] \<cdot> (\<a>[g, ?b, ?b] \<star> f)"
            using assms pentagon by force
          also have
              "... = ((g \<star> \<l>[?b \<star> f]) \<cdot> (g \<star> \<a>[?b, ?b, f])) \<cdot> \<a>[g, ?b \<star> ?b, f] \<cdot> (\<a>[g, ?b, ?b] \<star> f)"
            using assms assoc_in_hom HoVH_def HoHV_def comp_assoc by auto
          also have
              "... = ((g \<star> ?b \<star> \<l>[f]) \<cdot> (g \<star> \<a>[?b, ?b, f])) \<cdot> \<a>[g, ?b \<star> ?b, f] \<cdot> (\<a>[g, ?b, ?b] \<star> f)"
            using assms lunit_commutes_with_L lunit_in_hom by force
          also have "... = ((g \<star> (\<i>[?b] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[?b, ?b, f]) \<cdot> (g \<star> \<a>[?b, ?b, f]))
                             \<cdot> \<a>[g, ?b \<star> ?b, f] \<cdot> (\<a>[g, ?b, ?b] \<star> f)"
            using assms lunit_char(2) by force
          also have "... = (g \<star> ((\<i>[?b] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[?b, ?b, f]) \<cdot> \<a>[?b, ?b, f])
                             \<cdot> \<a>[g, ?b \<star> ?b, f] \<cdot> (\<a>[g, ?b, ?b] \<star> f)"
            using assms interchange [of g g "(\<i>[?b] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[?b, ?b, f]" "\<a>[?b, ?b, f]"]
            by auto
          also have "... = ((g \<star> \<i>[?b] \<star> f) \<cdot> \<a>[g, ?b \<star> ?b, f]) \<cdot> (\<a>[g, ?b, ?b] \<star> f)"
            using assms comp_arr_dom comp_assoc_assoc' comp_assoc by auto
          also have "... = (\<a>[g, ?b, f] \<cdot> ((g \<star> \<i>[?b]) \<star> f)) \<cdot> (\<a>[g, ?b, ?b] \<star> f)"
            using assms assoc_naturality [of g "\<i>[?b]" f] by simp
          also have "... = \<a>[g, ?b, f] \<cdot> ((g \<star> \<i>[?b]) \<cdot> \<a>[g, ?b, ?b] \<star> f)"
            using assms interchange [of "g \<star> \<i>[?b]" "\<a>[g, ?b, ?b]" f f] comp_assoc by simp
          also have "... = \<a>[g, ?b, f] \<cdot> ((\<r>[g] \<star> ?b) \<star> f)"
            using assms runit_char(2) by force
          also have "... = (\<r>[g] \<star> ?b \<star> f) \<cdot> \<a>[g \<star> ?b, ?b, f]"
            using assms assoc_naturality [of "\<r>[g]" ?b f] by auto
          finally show ?thesis by blast
        qed
        show "(g \<star> \<l>[?b \<star> f]) \<cdot> \<a>[g, ?b, ?b \<star> f] = \<r>[g] \<star> ?b \<star> f"
        proof -
          have "epi \<a>[g \<star> ?b, ?b, f]"
            using assms preserves_ide iso_assoc iso_is_retraction retraction_is_epi by force
          thus ?thesis
            using assms 1 by auto
        qed
      qed
      have "(g \<star> \<l>[f]) \<cdot> \<a>[g, ?b, f] = ((g \<star> \<l>[f]) \<cdot> (g \<star> \<l>[?b \<star> f]) \<cdot> (g \<star> ?b \<star> \<l>\<^sup>-\<^sup>1[f])) \<cdot>
                                     (g \<star> ?b \<star> \<l>[f]) \<cdot> \<a>[g, ?b, ?b \<star> f] \<cdot> ((g \<star> ?b) \<star> \<l>\<^sup>-\<^sup>1[f])"
      proof -
        have "\<a>[g, ?b, f] = (g \<star> ?b \<star> \<l>[f]) \<cdot> \<a>[g, ?b, ?b \<star> f] \<cdot> ((g \<star> ?b) \<star> \<l>\<^sup>-\<^sup>1[f])"
        proof -
          have "\<a>[g, ?b, f] = (g \<star> ?b \<star> f) \<cdot> \<a>[g, ?b, f]"
            using assms comp_cod_arr by simp
          have "\<a>[g, ?b, f] = ((g \<star> ?b \<star> \<l>[f]) \<cdot> (g \<star> ?b \<star> \<l>\<^sup>-\<^sup>1[f])) \<cdot> \<a>[g, ?b, f]"
            using assms comp_cod_arr comp_arr_inv' whisker_left [of g]
                  whisker_left [of ?b "\<l>[f]" "\<l>\<^sup>-\<^sup>1[f]"]
            by simp
          also have "... = (g \<star> ?b \<star> \<l>[f]) \<cdot> \<a>[g, ?b, ?b \<star> f] \<cdot> ((g \<star> ?b) \<star> \<l>\<^sup>-\<^sup>1[f])"
            using assms iso_lunit assoc_naturality [of g ?b "\<l>\<^sup>-\<^sup>1[f]"] comp_assoc by force
          finally show ?thesis by blast
        qed
        moreover have "g \<star> \<l>[f] = (g \<star> \<l>[f]) \<cdot> (g \<star> \<l>[?b \<star> f]) \<cdot> (g \<star> ?b \<star> \<l>\<^sup>-\<^sup>1[f])"
        proof -
          have "(g \<star> \<l>[?b \<star> f]) \<cdot> (g \<star> ?b \<star> \<l>\<^sup>-\<^sup>1[f]) = g \<star> ?b \<star> f"
          proof -
            have "(g \<star> \<l>[?b \<star> f]) \<cdot> (g \<star> ?b \<star> \<l>\<^sup>-\<^sup>1[f]) = (g \<star> ?b \<star> \<l>[f]) \<cdot> (g \<star> ?b \<star> \<l>\<^sup>-\<^sup>1[f])"
              using assms lunit_in_hom lunit_commutes_with_L by simp
            also have "... = g \<star> ?b \<star> f"
              using assms comp_arr_inv' whisker_left [of g] whisker_left [of ?b "\<l>[f]" "\<l>\<^sup>-\<^sup>1[f]"]
              by simp
            finally show ?thesis by blast
          qed
          thus ?thesis
            using assms comp_arr_dom by auto
        qed
        ultimately show ?thesis by simp
      qed
      also have "... = (g \<star> \<l>[f]) \<cdot> (g \<star> \<l>[?b \<star> f]) \<cdot> ((g \<star> ?b \<star> \<l>\<^sup>-\<^sup>1[f]) \<cdot> (g \<star> ?b \<star> \<l>[f])) \<cdot>
                       \<a>[g, ?b, ?b \<star> f] \<cdot> ((g \<star> ?b) \<star> \<l>\<^sup>-\<^sup>1[f])"
        using comp_assoc by simp
      also have "... = (g \<star> \<l>[f]) \<cdot> (g \<star> \<l>[?b \<star> f]) \<cdot> ((g \<star> ?b \<star> (?b \<star> f)) \<cdot>
                       \<a>[g, ?b, ?b \<star> f]) \<cdot> ((g \<star> ?b) \<star> \<l>\<^sup>-\<^sup>1[f])"
        using assms iso_lunit comp_inv_arr' interchange [of g g "?b \<star> \<l>\<^sup>-\<^sup>1[f]" "?b \<star> \<l>[f]"]
              interchange [of ?b ?b "\<l>\<^sup>-\<^sup>1[f]" "\<l>[f]"] comp_assoc
        by auto
      also have "... = (g \<star> \<l>[f]) \<cdot> ((g \<star> \<l>[?b \<star> f]) \<cdot> \<a>[g, ?b, ?b \<star> f]) \<cdot> ((g \<star> ?b) \<star> \<l>\<^sup>-\<^sup>1[f])"
        using assms comp_cod_arr comp_assoc by auto
      also have "... = \<r>[g] \<star> f"
      proof -
        have "\<r>[g] \<star> f = (g \<star> \<l>[f]) \<cdot> (\<r>[g] \<star> ?b \<star> f) \<cdot> ((g \<star> ?b) \<star> \<l>\<^sup>-\<^sup>1[f])"
        proof -
          have "(g \<star> \<l>[f]) \<cdot> (\<r>[g] \<star> ?b \<star> f) \<cdot> ((g \<star> ?b) \<star> \<l>\<^sup>-\<^sup>1[f])
                  = (g \<star> \<l>[f]) \<cdot> (\<r>[g] \<cdot> (g \<star> ?b) \<star> (?b \<star> f) \<cdot> \<l>\<^sup>-\<^sup>1[f])"
            using assms iso_lunit interchange [of "\<r>[g]" "g \<star> ?b" "?b \<star> f" "\<l>\<^sup>-\<^sup>1[f]"]
            by force
          also have "... = (g \<star> \<l>[f]) \<cdot> (\<r>[g] \<star> \<l>\<^sup>-\<^sup>1[f])"
            using assms comp_arr_dom comp_cod_arr by simp
          also have "... = \<r>[g] \<star> \<l>[f] \<cdot> \<l>\<^sup>-\<^sup>1[f]"
            using assms interchange [of g "\<r>[g]" "\<l>[f]" "\<l>\<^sup>-\<^sup>1[f]"] comp_cod_arr
            by simp
          also have "... = \<r>[g] \<star> f"
            using assms iso_lunit comp_arr_inv' by simp
          finally show ?thesis by argo
        qed
        thus ?thesis using assms * by argo
      qed
      finally show ?thesis by blast
    qed

    lemma lunit_hcomp_gen:
    assumes "ide f" and "ide g" and "ide h"
    and "src f = trg g" and "src g = trg h"
    shows "(f \<star> \<l>[g \<star> h]) \<cdot> (f \<star> \<a>[trg g, g, h]) = f \<star> \<l>[g] \<star> h"
    proof -
      have "((f \<star> \<l>[g \<star> h]) \<cdot> (f \<star> \<a>[trg g, g, h])) \<cdot> \<a>[f, trg g \<star> g, h] \<cdot> (\<a>[f, trg g, g] \<star> h) =
            (f \<star> (\<l>[g] \<star> h)) \<cdot> \<a>[f, trg g \<star> g, h] \<cdot> (\<a>[f, trg g, g] \<star> h)"
      proof -
        have "((f \<star> \<l>[g \<star> h]) \<cdot> (f \<star> \<a>[trg g, g, h])) \<cdot> (\<a>[f, trg g \<star> g, h] \<cdot> (\<a>[f, trg g, g] \<star> h)) =
              ((f \<star> \<l>[g \<star> h]) \<cdot> \<a>[f, trg g, g \<star> h]) \<cdot> \<a>[f \<star> trg g, g, h]"
          using assms pentagon comp_assoc by simp
        also have "... = (\<r>[f] \<star> (g \<star> h)) \<cdot> \<a>[f \<star> trg g, g, h]"
          using assms triangle [of "g \<star> h" f] by auto
        also have "... = \<a>[f, g, h] \<cdot> ((\<r>[f] \<star> g) \<star> h)"
          using assms assoc_naturality [of "\<r>[f]" g h] by simp
        also have "... = (\<a>[f, g, h] \<cdot> ((f \<star> \<l>[g]) \<star> h)) \<cdot> (\<a>[f, trg g, g] \<star> h)"
          using assms triangle interchange [of "f \<star> \<l>[g]" "\<a>[f, trg g, g]" h h] comp_assoc
          by auto
        also have "... = (f \<star> (\<l>[g] \<star> h)) \<cdot> (\<a>[f, trg g \<star> g, h] \<cdot> (\<a>[f, trg g, g] \<star> h))"
          using assms assoc_naturality [of f "\<l>[g]" h] comp_assoc by simp
        finally show ?thesis by blast
      qed
      moreover have "iso (\<a>[f, trg g \<star> g, h] \<cdot> (\<a>[f, trg g, g] \<star> h))"
        using assms iso_assoc isos_compose by simp
      ultimately show ?thesis
        using assms iso_is_retraction retraction_is_epi
              epiE [of "\<a>[f, trg g \<star> g, h] \<cdot> (\<a>[f, trg g, g] \<star> h)"
                         "(f \<star> \<l>[g \<star> h]) \<cdot> (f \<star> \<a>[trg g, g, h])" "f \<star> \<l>[g] \<star> h"]
         by auto
    qed

    lemma lunit_hcomp:
    assumes "ide f" and "ide g" and "src f = trg g"
    shows "\<l>[f \<star> g] \<cdot> \<a>[trg f, f, g] = \<l>[f] \<star> g"
    and "\<a>\<^sup>-\<^sup>1[trg f, f, g] \<cdot> \<l>\<^sup>-\<^sup>1[f \<star> g] = \<l>\<^sup>-\<^sup>1[f] \<star> g"
    and "\<l>[f \<star> g] = (\<l>[f] \<star> g) \<cdot> \<a>\<^sup>-\<^sup>1[trg f, f, g]"
    and "\<l>\<^sup>-\<^sup>1[f \<star> g] = \<a>[trg f, f, g] \<cdot> (\<l>\<^sup>-\<^sup>1[f] \<star> g)"
    proof -
      show 1: "\<l>[f \<star> g] \<cdot> \<a>[trg f, f, g] = \<l>[f] \<star> g"
      proof -
        have "L (\<l>[f \<star> g] \<cdot> \<a>[trg f, f, g]) = L (\<l>[f] \<star> g)"
          using assms interchange [of "trg f" "trg f" "\<l>[f \<star> g]" "\<a>[trg f, f, g]"] lunit_hcomp_gen
          by fastforce
        thus ?thesis
          using assms L.is_faithful [of "\<l>[f \<star> g] \<cdot> \<a>[trg f, f, g]" "\<l>[f] \<star> g"] by force
      qed
      show "\<a>\<^sup>-\<^sup>1[trg f, f, g] \<cdot> \<l>\<^sup>-\<^sup>1[f \<star> g] = \<l>\<^sup>-\<^sup>1[f] \<star> g"
      proof -
        have "\<a>\<^sup>-\<^sup>1[trg f, f, g] \<cdot> \<l>\<^sup>-\<^sup>1[f \<star> g] = inv (\<l>[f \<star> g] \<cdot> \<a>[trg f, f, g])"
          using assms by (simp add: inv_comp)
        also have "... = inv (\<l>[f] \<star> g)"
          using 1 by simp
        also have "... = \<l>\<^sup>-\<^sup>1[f] \<star> g"
          using assms by simp
        finally show ?thesis by simp
      qed
      show 2: "\<l>[f \<star> g] = (\<l>[f] \<star> g) \<cdot> \<a>\<^sup>-\<^sup>1[trg f, f, g]"
        using assms 1 invert_side_of_triangle(2) by auto
      show "\<l>\<^sup>-\<^sup>1[f \<star> g] = \<a>[trg f, f, g] \<cdot> (\<l>\<^sup>-\<^sup>1[f] \<star> g)"
      proof -
        have "\<l>\<^sup>-\<^sup>1[f \<star> g] = inv ((\<l>[f] \<star> g) \<cdot> \<a>\<^sup>-\<^sup>1[trg f, f, g])"
          using 2 by simp
        also have "... = \<a>[trg f, f, g] \<cdot> inv (\<l>[f] \<star> g)"
          using assms inv_comp iso_inv_iso by simp
        also have "... = \<a>[trg f, f, g] \<cdot> (\<l>\<^sup>-\<^sup>1[f] \<star> g)"
          using assms by simp
        finally show ?thesis by simp
      qed
    qed

    lemma runit_hcomp_gen:
    assumes "ide f" and "ide g" and "ide h"
    and "src f = trg g" and "src g = trg h"
    shows "\<r>[f \<star> g] \<star> h = ((f \<star> \<r>[g]) \<star> h) \<cdot> (\<a>[f, g, src g] \<star> h)"
    proof -
      have "\<r>[f \<star> g] \<star> h = ((f \<star> g) \<star> \<l>[h]) \<cdot> \<a>[f \<star> g, src g, h]"
        using assms triangle by simp
      also have "... = (\<a>\<^sup>-\<^sup>1[f, g, h] \<cdot> (f \<star> g \<star> \<l>[h]) \<cdot> \<a>[f, g, src g \<star> h]) \<cdot> \<a>[f \<star> g, src g, h]"
        using assms assoc_naturality [of f g "\<l>[h]"] invert_side_of_triangle(1)
        by simp
      also have "... = \<a>\<^sup>-\<^sup>1[f, g, h] \<cdot> (f \<star> g \<star> \<l>[h]) \<cdot> \<a>[f, g, src g \<star> h] \<cdot> \<a>[f \<star> g, src g, h]"
        using comp_assoc by simp
      also have "... = (\<a>\<^sup>-\<^sup>1[f, g, h] \<cdot> (f \<star> (\<r>[g] \<star> h))) \<cdot> (f \<star> \<a>\<^sup>-\<^sup>1[g, src g, h]) \<cdot>
                       \<a>[f, g, src g \<star> h] \<cdot> \<a>[f \<star> g, src g, h]"
        using assms interchange [of f f] triangle comp_assoc
              invert_side_of_triangle(2) [of "\<r>[g] \<star> h" "g \<star> \<l>[h]" "\<a>[g, src g, h]"]
        by simp
      also have "... = ((f \<star> \<r>[g]) \<star> h) \<cdot> \<a>\<^sup>-\<^sup>1[f, g \<star> src g, h] \<cdot> (f \<star> \<a>\<^sup>-\<^sup>1[g, src g, h]) \<cdot>
                       \<a>[f, g, src g \<star> h] \<cdot> \<a>[f \<star> g, src g, h]"
        using assms assoc'_naturality [of f "\<r>[g]" h] comp_assoc by simp
      also have "... = ((f \<star> \<r>[g]) \<star> h) \<cdot> (\<a>[f, g, src g] \<star> h)"
        using assms pentagon [of f g "src g" h] iso_assoc inv_hcomp
              invert_side_of_triangle(1)
                [of "\<a>[f, g, src g \<star> h] \<cdot> \<a>[f \<star> g, src g, h]" "f \<star> \<a>[g, src g, h]"
                    "\<a>[f, g \<star> src g, h] \<cdot> (\<a>[f, g, src g] \<star> h)"]
              invert_side_of_triangle(1)
                [of "(f \<star> \<a>\<^sup>-\<^sup>1[g, src g, h]) \<cdot> \<a>[f, g, src g \<star> h] \<cdot> \<a>[f \<star> g, src g, h]"
                    "\<a>[f, g \<star> src g, h]" "\<a>[f, g, src g] \<star> h"]
        by auto
      finally show ?thesis by blast
    qed

    lemma runit_hcomp:
    assumes "ide f" and "ide g" and "src f = trg g"
    shows "\<r>[f \<star> g] = (f \<star> \<r>[g]) \<cdot> \<a>[f, g, src g]"
    and "\<r>\<^sup>-\<^sup>1[f \<star> g] = \<a>\<^sup>-\<^sup>1[f, g, src g] \<cdot> (f \<star> \<r>\<^sup>-\<^sup>1[g])"
    and "\<r>[f \<star> g] \<cdot> \<a>\<^sup>-\<^sup>1[f, g, src g] = f \<star> \<r>[g]"
    and "\<a>[f, g, src g] \<cdot> \<r>\<^sup>-\<^sup>1[f \<star> g] = f \<star> \<r>\<^sup>-\<^sup>1[g]"
    proof -
      show 1: "\<r>[f \<star> g] = (f \<star> \<r>[g]) \<cdot> \<a>[f, g, src g]"
        using assms interchange [of "f \<star> \<r>[g]" "\<a>[f, g, src g]" "src g" "src g"]
              runit_hcomp_gen [of f g "src g"]
              R.is_faithful [of "(f \<star> \<r>[g]) \<cdot> (\<a>[f, g, src g])" "\<r>[f \<star> g]"]
        by simp
      show "\<r>\<^sup>-\<^sup>1[f \<star> g] = \<a>\<^sup>-\<^sup>1[f, g, src g] \<cdot> (f \<star> \<r>\<^sup>-\<^sup>1[g])"
        using assms 1 inv_comp inv_hcomp by auto
      show 2: "\<r>[f \<star> g] \<cdot> \<a>\<^sup>-\<^sup>1[f, g, src g] = f \<star> \<r>[g]"
        using assms 1 comp_arr_dom comp_cod_arr comp_assoc hseqI' comp_assoc_assoc' by auto
      show "\<a>[f, g, src g] \<cdot> \<r>\<^sup>-\<^sup>1[f \<star> g] = f \<star> \<r>\<^sup>-\<^sup>1[g]"
      proof -
        have "\<a>[f, g, src g] \<cdot> \<r>\<^sup>-\<^sup>1[f \<star> g] = inv (\<r>[f \<star> g] \<cdot> \<a>\<^sup>-\<^sup>1[f, g, src g])"
          using assms inv_comp iso_inv_iso by simp
        also have "... = inv (f \<star> \<r>[g])"
          using 2 by simp
        also have "... = f \<star> \<r>\<^sup>-\<^sup>1[g]"
          using assms inv_hcomp [of f "\<r>[g]"] by simp
        finally show ?thesis by simp
      qed
    qed

    lemma unitor_coincidence:
    assumes "obj a"
    shows "\<l>[a] = \<i>[a]" and "\<r>[a] = \<i>[a]"
    proof -
      have "R \<l>[a] = R \<i>[a] \<and> R \<r>[a] = R \<i>[a]"
      proof -
        have "R \<l>[a] = (a \<star> \<l>[a]) \<cdot> \<a>[a, a, a]"
          using assms lunit_hcomp [of a a] lunit_commutes_with_L [of a] by auto
        moreover have "(a \<star> \<l>[a]) \<cdot> \<a>[a, a, a] = R \<r>[a]"
          using assms triangle [of a a] by auto
        moreover have "(a \<star> \<l>[a]) \<cdot> \<a>[a, a, a] = R \<i>[a]"
        proof -
          have "(a \<star> \<l>[a]) \<cdot> \<a>[a, a, a] = ((\<i>[a] \<star> a) \<cdot> \<a>\<^sup>-\<^sup>1[a, a, a]) \<cdot> \<a>[a, a, a]"
            using assms lunit_char(2) by force
          also have "... = R \<i>[a]"
            using assms comp_arr_dom comp_assoc comp_assoc_assoc'
            apply (elim objE)
            by (simp add: assms)
          finally show ?thesis by blast
        qed
        ultimately show ?thesis by argo
      qed
      moreover have "par \<l>[a] \<i>[a] \<and> par \<r>[a] \<i>[a]"
        using assms by auto
      ultimately have 1: "\<l>[a] = \<i>[a] \<and> \<r>[a] = \<i>[a]"
        using R.is_faithful by blast
      show "\<l>[a] = \<i>[a]" using 1 by auto
      show "\<r>[a] = \<i>[a]" using 1 by auto
    qed

    lemma unit_triangle:
    assumes "obj a"
    shows "\<i>[a] \<star> a = (a \<star> \<i>[a]) \<cdot> \<a>[a, a, a]"
    and "(\<i>[a] \<star> a) \<cdot> \<a>\<^sup>-\<^sup>1[a, a, a] = a \<star> \<i>[a]"
    proof -
      show 1: "\<i>[a] \<star> a = (a \<star> \<i>[a]) \<cdot> \<a>[a, a, a]"
        using assms triangle [of a a] unitor_coincidence by auto
      show "(\<i>[a] \<star> a) \<cdot> \<a>\<^sup>-\<^sup>1[a, a, a] = a \<star> \<i>[a]"
        using assms 1 invert_side_of_triangle(2) [of "\<i>[a] \<star> a" "a \<star> \<i>[a]" "\<a>[a, a, a]"]
              assoc'_eq_inv_assoc
        by (metis hseqI' iso_assoc objE obj_def' unit_simps(1) unit_simps(2))
    qed

    lemma hcomp_arr_obj:
    assumes "arr \<mu>" and "obj a" and "src \<mu> = a"
    shows "\<mu> \<star> a = \<r>\<^sup>-\<^sup>1[cod \<mu>] \<cdot> \<mu> \<cdot> \<r>[dom \<mu>]"
    and "\<r>[cod \<mu>] \<cdot> (\<mu> \<star> a) \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>] = \<mu>"
    proof -
      show "\<mu> \<star> a = \<r>\<^sup>-\<^sup>1[cod \<mu>] \<cdot> \<mu> \<cdot> \<r>[dom \<mu>]"
        using assms iso_runit runit_naturality comp_cod_arr
        by (metis ide_cod ide_dom invert_side_of_triangle(1) runit_simps(1) runit_simps(5) seqI)
      show "\<r>[cod \<mu>] \<cdot> (\<mu> \<star> a) \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>] = \<mu>"
        using assms iso_runit runit_naturality [of \<mu>] comp_cod_arr
        by (metis ide_dom invert_side_of_triangle(2) comp_assoc runit_simps(1)
            runit_simps(5) seqI)
    qed

    lemma hcomp_obj_arr:
    assumes "arr \<mu>" and "obj b" and "b = trg \<mu>"
    shows "b \<star> \<mu> = \<l>\<^sup>-\<^sup>1[cod \<mu>] \<cdot> \<mu> \<cdot> \<l>[dom \<mu>]"
    and "\<l>[cod \<mu>] \<cdot> (b \<star> \<mu>) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu>] = \<mu>"
    proof -
      show "b \<star> \<mu> = \<l>\<^sup>-\<^sup>1[cod \<mu>] \<cdot> \<mu> \<cdot> \<l>[dom \<mu>]"
        using assms iso_lunit lunit_naturality comp_cod_arr
        by (metis ide_cod ide_dom invert_side_of_triangle(1) lunit_simps(1) lunit_simps(5) seqI)
      show "\<l>[cod \<mu>] \<cdot> (b \<star> \<mu>) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu>] = \<mu>"
        using assms iso_lunit lunit_naturality [of \<mu>] comp_cod_arr
        by (metis ide_dom invert_side_of_triangle(2) comp_assoc lunit_simps(1)
            lunit_simps(5) seqI)
    qed

    lemma hcomp_reassoc:
    assumes "arr \<tau>" and "arr \<mu>" and "arr \<nu>"
    and "src \<tau> = trg \<mu>" and "src \<mu> = trg \<nu>"
    shows "(\<tau> \<star> \<mu>) \<star> \<nu> = \<a>\<^sup>-\<^sup>1[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> (\<tau> \<star> \<mu> \<star> \<nu>) \<cdot> \<a>[dom \<tau>, dom \<mu>, dom \<nu>]"
    and "\<tau> \<star> \<mu> \<star> \<nu> = \<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> ((\<tau> \<star> \<mu>) \<star> \<nu>) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<tau>, dom \<mu>, dom \<nu>]"
    proof -
      show "(\<tau> \<star> \<mu>) \<star> \<nu> = \<a>\<^sup>-\<^sup>1[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> (\<tau> \<star> \<mu> \<star> \<nu>) \<cdot> \<a>[dom \<tau>, dom \<mu>, dom \<nu>]"
      proof -
        have "(\<tau> \<star> \<mu>) \<star> \<nu> = (\<a>\<^sup>-\<^sup>1[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> \<a>[cod \<tau>, cod \<mu>, cod \<nu>]) \<cdot> ((\<tau> \<star> \<mu>) \<star> \<nu>)"
          using assms comp_assoc_assoc'(2) comp_cod_arr by simp
        also have "... = \<a>\<^sup>-\<^sup>1[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> \<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> ((\<tau> \<star> \<mu>) \<star> \<nu>)"
          using comp_assoc by simp
        also have "... = \<a>\<^sup>-\<^sup>1[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> (\<tau> \<star> \<mu> \<star> \<nu>) \<cdot> \<a>[dom \<tau>, dom \<mu>, dom \<nu>]"
          using assms assoc_naturality by simp
        finally show ?thesis by simp
      qed
      show "\<tau> \<star> \<mu> \<star> \<nu> = \<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> ((\<tau> \<star> \<mu>) \<star> \<nu>) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<tau>, dom \<mu>, dom \<nu>]"
      proof -
        have "\<tau> \<star> \<mu> \<star> \<nu> = (\<tau> \<star> \<mu> \<star> \<nu>) \<cdot> \<a>[dom \<tau>, dom \<mu>, dom \<nu>] \<cdot> \<a>\<^sup>-\<^sup>1[dom \<tau>, dom \<mu>, dom \<nu>]"
          using assms comp_assoc_assoc'(1) comp_arr_dom by simp
        also have "... = ((\<tau> \<star> \<mu> \<star> \<nu>) \<cdot> \<a>[dom \<tau>, dom \<mu>, dom \<nu>]) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<tau>, dom \<mu>, dom \<nu>]"
          using comp_assoc by simp
        also have "... = (\<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> ((\<tau> \<star> \<mu>) \<star> \<nu>)) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<tau>, dom \<mu>, dom \<nu>]"
          using assms assoc_naturality by simp
        also have "... = \<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> ((\<tau> \<star> \<mu>) \<star> \<nu>) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<tau>, dom \<mu>, dom \<nu>]"
          using comp_assoc by simp
        finally show ?thesis by simp
      qed
    qed

    lemma triangle':
    assumes "ide f" and "ide g" and "src f = trg g"
    shows "(f \<star> \<l>[g]) = (\<r>[f] \<star> g) \<cdot> \<a>\<^sup>-\<^sup>1[f, src f, g]"
    proof -
      have "(\<r>[f] \<star> g) \<cdot> \<a>\<^sup>-\<^sup>1[f, src f, g] = ((f \<star> \<l>[g]) \<cdot> \<a>[f, src f, g]) \<cdot> \<a>\<^sup>-\<^sup>1[f, src f, g]"
        using assms triangle by auto
      also have "... = (f \<star> \<l>[g])"
        using assms comp_arr_dom comp_assoc comp_assoc_assoc' by auto
      finally show ?thesis by auto
    qed

    lemma pentagon':
    assumes "ide f" and "ide g" and "ide h" and "ide k"
    and "src f = trg g" and "src g = trg h" and "src h = trg k"
    shows "((\<a>\<^sup>-\<^sup>1[f, g, h] \<star> k) \<cdot> \<a>\<^sup>-\<^sup>1[f, g \<star> h, k]) \<cdot> (f \<star> \<a>\<^sup>-\<^sup>1[g, h, k])
              = \<a>\<^sup>-\<^sup>1[f \<star> g, h, k] \<cdot> \<a>\<^sup>-\<^sup>1[f, g, h \<star> k]"
    proof -
      have "((\<a>\<^sup>-\<^sup>1[f, g, h] \<star> k) \<cdot> \<a>\<^sup>-\<^sup>1[f, g \<star> h, k]) \<cdot> (f \<star> \<a>\<^sup>-\<^sup>1[g, h, k])
              = inv ((f \<star> \<a>[g, h, k]) \<cdot> (\<a>[f, g \<star> h, k] \<cdot> (\<a>[f, g, h] \<star> k)))"
      proof -
        have "inv ((f \<star> \<a>[g, h, k]) \<cdot> (\<a>[f, g \<star> h, k] \<cdot> (\<a>[f, g, h] \<star> k))) =
              inv (\<a>[f, g \<star> h, k] \<cdot> (\<a>[f, g, h] \<star> k)) \<cdot> inv (f \<star> \<a>[g, h, k])"
          using assms inv_comp [of "\<a>[f, g \<star> h, k] \<cdot> (\<a>[f, g, h] \<star> k)" "f \<star> \<a>[g, h, k]"]
          by force
        also have "... = (inv (\<a>[f, g, h] \<star> k) \<cdot> inv \<a>[f, g \<star> h, k]) \<cdot> inv (f \<star> \<a>[g, h, k])"
          using assms iso_assoc inv_comp by simp
        also have "... = ((\<a>\<^sup>-\<^sup>1[f, g, h] \<star> k) \<cdot> \<a>\<^sup>-\<^sup>1[f, g \<star> h, k]) \<cdot> (f \<star> \<a>\<^sup>-\<^sup>1[g, h, k])"
          using assms inv_hcomp by simp
        finally show ?thesis by simp
      qed
      also have "... = inv (\<a>[f, g, h \<star> k] \<cdot> \<a>[f \<star> g, h, k])"
        using assms pentagon by simp
      also have "... = \<a>\<^sup>-\<^sup>1[f \<star> g, h, k] \<cdot> \<a>\<^sup>-\<^sup>1[f, g, h \<star> k]"
        using assms inv_comp by simp
      finally show ?thesis by auto
    qed

  end

  text \<open>
    The following convenience locale extends @{locale bicategory} by pre-interpreting
    the various functors and natural transformations.
  \<close>

  locale extended_bicategory =
    bicategory +
    L: equivalence_functor V V L +
    R: equivalence_functor V V R +
    \<alpha>: natural_isomorphism VVV.comp V HoHV HoVH
          \<open>\<lambda>\<mu>\<nu>\<tau>. \<a> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>))\<close> +
    \<alpha>': inverse_transformation VVV.comp V HoHV HoVH
          \<open>\<lambda>\<mu>\<nu>\<tau>. \<a> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>))\<close> +
    \<ll>: natural_isomorphism V V L map \<ll> +
    \<ll>': inverse_transformation V V L map \<ll> +
    \<rr>: natural_isomorphism V V R map \<rr> +
    \<rr>': inverse_transformation V V R map \<rr>

  sublocale bicategory \<subseteq> extended_bicategory V H \<a> \<i> src trg
  proof -
    interpret L: equivalence_functor V V L using equivalence_functor_L by auto
    interpret R: equivalence_functor V V R using equivalence_functor_R by auto
    interpret \<alpha>': inverse_transformation VVV.comp V HoHV HoVH
                    \<open>\<lambda>\<mu>\<nu>\<tau>. \<a> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>))\<close> ..
    interpret \<ll>: natural_isomorphism V V L map \<ll> using natural_isomorphism_\<ll> by auto
    interpret \<ll>': inverse_transformation V V L map \<ll> ..
    interpret \<rr>: natural_isomorphism V V R map \<rr> using natural_isomorphism_\<rr> by auto
    interpret \<rr>': inverse_transformation V V R map \<rr> ..
    interpret extended_bicategory V H \<a> \<i> src trg ..
    show "extended_bicategory V H \<a> \<i> src trg" ..
  qed

end
