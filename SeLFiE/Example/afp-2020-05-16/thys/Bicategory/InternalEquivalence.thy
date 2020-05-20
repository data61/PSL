(*  Title:       InternalEquivalence
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Internal Equivalences"

theory InternalEquivalence
imports Bicategory
begin

  text \<open>
    An \emph{internal equivalence} in a bicategory consists of antiparallel 1-cells \<open>f\<close> and \<open>g\<close>
    together with invertible 2-cells \<open>\<guillemotleft>\<eta> : src f \<Rightarrow> g \<star> f\<guillemotright>\<close> and \<open>\<guillemotleft>\<epsilon> : f \<star> g \<Rightarrow> src g\<guillemotright>\<close>.
    Objects in a bicategory are said to be \emph{equivalent} if they are connected by an
    internal equivalence.
    In this section we formalize the definition of internal equivalence and the related notions
    ``equivalence map'' and ``equivalent objects'', and we establish some basic facts about
    these notions.
  \<close>

  subsection "Definition of Equivalence"

  text \<open>
    The following locale is defined to prove some basic facts about an equivalence
    (or an adjunction) in a bicategory that are ``syntactic'' in the sense that they depend
    only on the configuration (source, target, domain, codomain) of the arrows
    involved and not on further properties such as the triangle identities (for adjunctions)
    or assumptions about invertibility (for equivalences).  Proofs about adjunctions and
    equivalences become more automatic once we have introduction and simplification rules in
    place about this syntax.
  \<close>

  locale adjunction_data_in_bicategory =
     bicategory +
  fixes f :: 'a
  and g :: 'a
  and \<eta> :: 'a
  and \<epsilon> :: 'a
  assumes ide_left [simp]: "ide f"
  and ide_right [simp]: "ide g"
  and unit_in_vhom: "\<guillemotleft>\<eta> : src f \<Rightarrow> g \<star> f\<guillemotright>"
  and counit_in_vhom: "\<guillemotleft>\<epsilon> : f \<star> g \<Rightarrow> src g\<guillemotright>"
  begin

    (*
     * TODO: It is difficult to orient the following equations to make them useful as
     * default simplifications, so they have to be cited explicitly where they are used.
     *)
    lemma antipar (*[simp]*):
    shows "trg g = src f" and "src g = trg f"
      apply (metis counit_in_vhom ideD(1) ide_right iso_is_arr not_arr_null
                   seq_if_composable src.components_are_iso trg.is_extensional trg_src
                   vconn_implies_hpar(4))
      by (metis horizontal_homs.vconn_implies_hpar(4) horizontal_homs_axioms ideD(1)
                ide_left iso_is_arr not_arr_null seq_if_composable src.components_are_iso
                trg.is_extensional trg_src unit_in_vhom)

    lemma counit_in_hom [intro]:
    shows "\<guillemotleft>\<epsilon> : trg f \<rightarrow> trg f\<guillemotright>" and "\<guillemotleft>\<epsilon> : f \<star> g \<Rightarrow> trg f\<guillemotright>"
      using counit_in_vhom vconn_implies_hpar antipar by auto

    lemma unit_in_hom [intro]:
    shows "\<guillemotleft>\<eta> : src f \<rightarrow> src f\<guillemotright>" and "\<guillemotleft>\<eta> : src f \<Rightarrow> g \<star> f\<guillemotright>"
      using unit_in_vhom vconn_implies_hpar antipar by auto

    lemma unit_simps [simp]:
    shows "arr \<eta>" and "dom \<eta> = src f" and "cod \<eta> = g \<star> f"
    and "src \<eta> = src f" and "trg \<eta> = src f"
      using unit_in_hom antipar by auto

    lemma counit_simps [simp]:
    shows "arr \<epsilon>" and "dom \<epsilon> = f \<star> g" and "cod \<epsilon> = trg f"
    and "src \<epsilon> = trg f" and "trg \<epsilon> = trg f"
      using counit_in_hom antipar by auto

    text \<open>
      The expressions found in the triangle identities for an adjunction come up
      relatively frequently, so it is useful to have established some basic facts
      about them, even if the triangle identities themselves have not actually been
      introduced as assumptions in the current context.
    \<close>

    lemma triangle_in_hom:
    shows "\<guillemotleft>(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) : f \<star> src f \<Rightarrow> trg f \<star> f\<guillemotright>"
    and "\<guillemotleft>(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) : trg g \<star> g \<Rightarrow> g \<star> src g\<guillemotright>"
    and "\<guillemotleft>\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] : f \<Rightarrow> f\<guillemotright>"
    and "\<guillemotleft>\<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] : g \<Rightarrow> g\<guillemotright>"
      using antipar by auto

    lemma triangle_equiv_form:
    shows "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<longleftrightarrow>
           \<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] = f"
    and "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g] \<longleftrightarrow>
         \<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] = g"
    proof -
      show "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<longleftrightarrow>
            \<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] = f"
      proof
        assume 1: "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
        have "\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] =
              \<l>[f] \<cdot> ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) \<cdot> \<r>\<^sup>-\<^sup>1[f]"
          using comp_assoc by simp
        also have "... = \<l>[f] \<cdot> (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]) \<cdot> \<r>\<^sup>-\<^sup>1[f]"
          using 1 by simp
        also have "... = f"
          using comp_assoc comp_arr_inv' comp_inv_arr' iso_lunit iso_runit
                comp_arr_dom comp_cod_arr
          by simp
        finally show "\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] = f"
          by simp
        next
        assume 2: "\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] = f"
        have "\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] = \<l>\<^sup>-\<^sup>1[f] \<cdot> f \<cdot> \<r>[f]"
          using comp_cod_arr by simp
        also have "... = (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<l>[f]) \<cdot> ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) \<cdot> (\<r>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f])"
          using 2 comp_assoc by (metis (no_types, lifting))
        also have "... = (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)"
          using comp_arr_inv' comp_inv_arr' iso_lunit iso_runit comp_arr_dom comp_cod_arr
                hseqI' antipar
          by (metis ide_left in_homE lunit_simps(4) runit_simps(4) triangle_in_hom(1))
        finally show "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
          by simp
      qed
      show "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g] \<longleftrightarrow>
            \<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] = g"
      proof
        assume 1: "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
        have "\<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] =
              \<r>[g] \<cdot> ((g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)) \<cdot> \<l>\<^sup>-\<^sup>1[g]"
          using comp_assoc by simp
        also have "... = \<r>[g] \<cdot> (\<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]) \<cdot> \<l>\<^sup>-\<^sup>1[g]"
          using 1 by simp
        also have "... = g"
          using comp_assoc comp_arr_inv' comp_inv_arr' iso_lunit iso_runit
                comp_arr_dom comp_cod_arr
          by simp
        finally show "\<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] = g"
          by simp
        next
        assume 2: "\<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] = g"
        have "\<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g] = \<r>\<^sup>-\<^sup>1[g] \<cdot> g \<cdot> \<l>[g]"
          using comp_cod_arr by simp
        also have "... = \<r>\<^sup>-\<^sup>1[g] \<cdot> (\<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g]) \<cdot> \<l>[g]"
          using 2 by simp
        also have "... = (\<r>\<^sup>-\<^sup>1[g] \<cdot> \<r>[g]) \<cdot> ((g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)) \<cdot> (\<l>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g])"
          using comp_assoc by simp
        also have "... = (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)"
          using comp_arr_inv' comp_inv_arr' iso_lunit iso_runit comp_arr_dom comp_cod_arr
                hseqI' antipar
          by (metis ide_right in_homE lunit_simps(4) runit_simps(4) triangle_in_hom(2))
        finally show "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
          by simp
      qed
    qed

  end

  locale equivalence_in_bicategory =
    adjunction_data_in_bicategory +
  assumes unit_is_iso [simp]: "iso \<eta>"
  and counit_is_iso [simp]: "iso \<epsilon>"
  begin

    lemma dual_equivalence:
    shows "equivalence_in_bicategory V H \<a> \<i> src trg g f (inv \<epsilon>) (inv \<eta>)"
      using iso_inv_iso antipar
      apply unfold_locales by auto

  end

  subsection "Equivalence Maps"

  text \<open>
    We will use the term \emph{equivalence pair} to refer to 1-cells \<open>f\<close> and \<open>g\<close> that are
    part of an internal equivalence, and the term \emph{equivalence map} to refer to a 1-cell
    that is part of an equivalence pair.
  \<close>

  context bicategory
  begin

    definition equivalence_pair
    where "equivalence_pair f g \<equiv> \<exists>\<phi> \<psi>. equivalence_in_bicategory V H \<a> \<i> src trg f g \<phi> \<psi>"

    lemma equivalence_pair_symmetric:
    assumes "equivalence_pair f g"
    shows "equivalence_pair g f"
      using assms equivalence_in_bicategory.dual_equivalence equivalence_pair_def by fastforce

    definition equivalence_map
    where "equivalence_map f \<equiv> \<exists>g \<eta> \<epsilon>. equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"

    lemma equivalence_mapI:
    assumes "ide f" and "ide g" and "src g = trg f" and "trg g = src f"
    and "isomorphic (src f) (g \<star> f)" and "isomorphic (f \<star> g) (trg f)"
    shows "equivalence_map f"
    proof -
      obtain \<eta> where \<eta>: "\<guillemotleft>\<eta> : src f \<Rightarrow> g \<star> f\<guillemotright> \<and> iso \<eta>"
        using assms isomorphic_def by auto
      obtain \<epsilon> where \<epsilon>: "\<guillemotleft>\<epsilon> : f \<star> g \<Rightarrow> trg f\<guillemotright> \<and> iso \<epsilon>"
        using assms isomorphic_def by auto
      have "equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using assms \<eta> \<epsilon> by (unfold_locales, auto)
      thus ?thesis
        using equivalence_map_def by auto
    qed

    lemma equivalence_map_is_ide:
    assumes "equivalence_map f"
    shows "ide f"
      using assms adjunction_data_in_bicategory.ide_left equivalence_in_bicategory_def
            equivalence_map_def
      by fastforce

    lemma obj_is_equivalence_map:
    assumes "obj a"
    shows "equivalence_map a"
      using assms
      by (metis equivalence_mapI isomorphic_symmetric objE obj_self_composable(2))

    lemma equivalence_respects_iso:
    assumes "equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
    and "\<guillemotleft>\<phi> : f \<Rightarrow> f'\<guillemotright>" and "iso \<phi>" and "\<guillemotleft>\<psi> : g \<Rightarrow> g'\<guillemotright>" and "iso \<psi>"
    shows "equivalence_in_bicategory V H \<a> \<i> src trg f' g'
              ((g' \<star> \<phi>) \<cdot> (\<psi> \<star> f) \<cdot> \<eta>) (\<epsilon> \<cdot> (inv \<phi> \<star> g) \<cdot> (f' \<star> inv \<psi>))"
    proof -
      interpret E: equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using assms by auto
      show ?thesis
      proof
        show f': "ide f'" using assms by auto
        show g': "ide g'" using assms by auto
        show 1: "\<guillemotleft>(g' \<star> \<phi>) \<cdot> (\<psi> \<star> f) \<cdot> \<eta> : src f' \<Rightarrow> g' \<star> f'\<guillemotright>"
          using assms f' g' E.unit_in_hom E.antipar(2) vconn_implies_hpar(3)
         apply (intro comp_in_homI, auto)
          by (intro hcomp_in_vhom, auto)
        show "iso ((g' \<star> \<phi>) \<cdot> (\<psi> \<star> f) \<cdot> \<eta>)"
          using assms 1 g' vconn_implies_hpar(3) E.antipar(2) iso_hcomp
          by (intro isos_compose, auto)
        show 1: "\<guillemotleft>\<epsilon> \<cdot> (inv \<phi> \<star> g) \<cdot> (f' \<star> inv \<psi>) : f' \<star> g' \<Rightarrow> src g'\<guillemotright>"
          using assms f' ide_in_hom(2) vconn_implies_hpar(3-4) E.antipar(1-2)
          by (intro comp_in_homI, auto)
        show "iso (\<epsilon> \<cdot> (inv \<phi> \<star> g) \<cdot> (f' \<star> inv \<psi>))"
          using assms 1 isos_compose
          by (metis E.counit_is_iso E.ide_right arrI f' hseqE ide_is_iso iso_hcomp
              iso_inv_iso seqE)
      qed
    qed

    lemma equivalence_map_preserved_by_iso:
    assumes "equivalence_map f" and "f \<cong> f'"
    shows "equivalence_map f'"
    proof -
      obtain g \<eta> \<epsilon> where E: "equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using assms equivalence_map_def by auto
      interpret E: equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using E by auto
      obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : f \<Rightarrow> f'\<guillemotright> \<and> iso \<phi>"
        using assms isomorphic_def isomorphic_symmetric by blast
      have "equivalence_in_bicategory V H \<a> \<i> src trg f' g
              ((g \<star> \<phi>) \<cdot> (g \<star> f) \<cdot> \<eta>) (\<epsilon> \<cdot> (inv \<phi> \<star> g) \<cdot> (f' \<star> inv g))"
        using E \<phi> equivalence_respects_iso [of f g \<eta> \<epsilon> \<phi> f' g g] by fastforce
      thus ?thesis
        using equivalence_map_def by auto
    qed

    lemma equivalence_preserved_by_iso_right:
    assumes "equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
    and "\<guillemotleft>\<phi> : g \<Rightarrow> g'\<guillemotright>" and "iso \<phi>"
    shows "equivalence_in_bicategory V H \<a> \<i> src trg f g' ((\<phi> \<star> f) \<cdot> \<eta>) (\<epsilon> \<cdot> (f \<star> inv \<phi>))"
    proof
      interpret E: equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using assms by auto
      show "ide f" by simp
      show "ide g'"
        using assms(2) isomorphic_def by auto
      show "\<guillemotleft>(\<phi> \<star> f) \<cdot> \<eta> : src f \<Rightarrow> g' \<star> f\<guillemotright>"
        using assms E.antipar(2) E.ide_left by blast
      show "\<guillemotleft>\<epsilon> \<cdot> (f \<star> inv \<phi>) : f \<star> g' \<Rightarrow> src g'\<guillemotright>"
        using assms vconn_implies_hpar(3-4) E.counit_in_vhom E.antipar(1) ide_in_hom(2)
        by (intro comp_in_homI, auto)
      show "iso ((\<phi> \<star> f) \<cdot> \<eta>)"
        using assms E.antipar isos_compose by auto
      show "iso (\<epsilon> \<cdot> (f \<star> inv \<phi>))"
        using assms E.antipar isos_compose iso_inv_iso by auto
    qed

    lemma equivalence_preserved_by_iso_left:
    assumes "equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
    and "\<guillemotleft>\<phi> : f \<Rightarrow> f'\<guillemotright>" and "iso \<phi>"
    shows "equivalence_in_bicategory V H \<a> \<i> src trg f' g ((g \<star> \<phi>) \<cdot> \<eta>) (\<epsilon> \<cdot> (inv \<phi> \<star> g))"
    proof
      interpret E: equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using assms by auto
      show "ide f'"
        using assms by auto
      show "ide g"
        by simp
      show "\<guillemotleft>(g \<star> \<phi>) \<cdot> \<eta> : src f' \<Rightarrow> g \<star> f'\<guillemotright>"
        using assms E.unit_in_hom E.antipar by auto
      show "\<guillemotleft>\<epsilon> \<cdot> (inv \<phi> \<star> g) : f' \<star> g \<Rightarrow> src g\<guillemotright>"
        using assms E.counit_in_hom E.antipar ide_in_hom(2) vconn_implies_hpar(3) by auto
      show "iso ((g \<star> \<phi>) \<cdot> \<eta>)"
        using assms E.antipar isos_compose by auto
      show "iso (\<epsilon> \<cdot> (inv \<phi> \<star> g))"
        using assms E.antipar isos_compose iso_inv_iso by auto
    qed

  end

  subsection "Composing Equivalences"

  locale composite_equivalence_in_bicategory =
    bicategory V H \<a> \<i> src trg +
    fg: equivalence_in_bicategory V H \<a> \<i> src trg f g \<zeta> \<xi> +
    hk: equivalence_in_bicategory V H \<a> \<i> src trg h k \<sigma> \<tau>
  for V :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"        (infixr "\<cdot>" 55)
  and H :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"        (infixr "\<star>" 53)
  and \<a> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("\<a>[_, _, _]")
  and \<i> :: "'a \<Rightarrow> 'a"              ("\<i>[_]")
  and src :: "'a \<Rightarrow> 'a"
  and trg :: "'a \<Rightarrow> 'a"
  and f :: "'a"
  and g :: "'a"
  and \<zeta> :: "'a"
  and \<xi> :: "'a"
  and h :: "'a"
  and k :: "'a"
  and \<sigma> :: "'a"
  and \<tau> :: "'a" +
  assumes composable: "src h = trg f"
  begin

    abbreviation \<eta>
    where "\<eta> \<equiv> \<a>\<^sup>-\<^sup>1[g, k, h \<star> f] \<cdot> (g \<star> \<a>[k, h, f]) \<cdot> (g \<star> \<sigma> \<star> f) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[f]) \<cdot> \<zeta>"

    abbreviation \<epsilon>
    where "\<epsilon> \<equiv> \<tau> \<cdot> (h \<star> \<l>[k]) \<cdot> (h \<star> \<xi> \<star> k) \<cdot> (h \<star> \<a>\<^sup>-\<^sup>1[f, g, k]) \<cdot> \<a>[h, f, g \<star> k]"

    interpretation adjunction_data_in_bicategory V H \<a> \<i> src trg \<open>h \<star> f\<close> \<open>g \<star> k\<close> \<eta> \<epsilon>
    proof
      show "ide (h \<star> f)"
        using composable by simp
      show "ide (g \<star> k)"
        using fg.antipar hk.antipar composable by simp
      show "\<guillemotleft>\<eta> : src (h \<star> f) \<Rightarrow> (g \<star> k) \<star> h \<star> f\<guillemotright>"
        using fg.antipar hk.antipar composable by fastforce
      show "\<guillemotleft>\<epsilon> : (h \<star> f) \<star> g \<star> k \<Rightarrow> src (g \<star> k)\<guillemotright>"
        using fg.antipar hk.antipar composable by fastforce
    qed

    interpretation equivalence_in_bicategory V H \<a> \<i> src trg \<open>h \<star> f\<close> \<open>g \<star> k\<close> \<eta> \<epsilon>
    proof
      show "iso \<eta>"
        using fg.antipar hk.antipar composable fg.unit_is_iso hk.unit_is_iso iso_hcomp
              iso_lunit' hseq_char iso_inv_iso
        by (intro isos_compose, auto)
      show "iso \<epsilon>"
        using fg.antipar hk.antipar composable fg.counit_is_iso hk.counit_is_iso iso_hcomp
              iso_lunit hseq_char iso_inv_iso
        by (intro isos_compose, auto)
    qed

    lemma is_equivalence:
    shows "equivalence_in_bicategory V H \<a> \<i> src trg (h \<star> f) (g \<star> k) \<eta> \<epsilon>"
      ..

  end

  sublocale composite_equivalence_in_bicategory \<subseteq>
              equivalence_in_bicategory V H \<a> \<i> src trg \<open>h \<star> f\<close> \<open>g \<star> k\<close> \<eta> \<epsilon>
    using is_equivalence by simp

  context bicategory
  begin

    lemma equivalence_maps_compose:
    assumes "equivalence_map f" and "equivalence_map f'" and "src f' = trg f"
    shows "equivalence_map (f' \<star> f)"
    proof -
      obtain g \<phi> \<psi> where fg: "equivalence_in_bicategory V H \<a> \<i> src trg f g \<phi> \<psi>"
        using assms(1) equivalence_map_def by auto
      interpret fg: equivalence_in_bicategory V H \<a> \<i> src trg f g \<phi> \<psi>
        using fg by auto
      obtain g' \<phi>' \<psi>' where f'g': "equivalence_in_bicategory V H \<a> \<i> src trg f' g' \<phi>' \<psi>'"
        using assms(2) equivalence_map_def by auto
      interpret f'g': equivalence_in_bicategory V H \<a> \<i> src trg f' g' \<phi>' \<psi>'
        using f'g' by auto
      interpret composite_equivalence_in_bicategory V H \<a> \<i> src trg f g \<phi> \<psi> f' g' \<phi>' \<psi>'
        using assms(3) by (unfold_locales, auto)
      show ?thesis
        using equivalence_map_def equivalence_in_bicategory_axioms by auto
    qed

  end

  subsection "Equivalent Objects"

  context bicategory
  begin

    definition equivalent_objects
    where "equivalent_objects a b \<equiv> \<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> equivalence_map f"

    lemma equivalent_objects_reflexive:
    assumes "obj a"
    shows "equivalent_objects a a"
      using assms
      by (metis equivalent_objects_def ide_in_hom(1) objE obj_is_equivalence_map)

    lemma equivalent_objects_symmetric:
    assumes "equivalent_objects a b"
    shows "equivalent_objects b a"
    proof -
      obtain f where f: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> equivalence_map f"
        using assms equivalent_objects_def by auto
      obtain g \<eta> \<epsilon> where E: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using f equivalence_map_def by blast
      interpret E: equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using E by auto
      have E': "equivalence_in_bicategory V H \<a> \<i> src trg g f (inv \<epsilon>) (inv \<eta>)"
        using E.unit_in_hom E.unit_is_iso E.counit_in_hom E.counit_is_iso iso_inv_iso E.antipar
        by (unfold_locales, auto)
      moreover have "\<guillemotleft>g : b \<rightarrow> a\<guillemotright>"
        using E E.antipar by auto
      ultimately show ?thesis
        using assms E' equivalent_objects_def equivalence_map_def by auto
    qed

    lemma equivalent_objects_transitive [trans]:
    assumes "equivalent_objects a b" and "equivalent_objects b c"
    shows "equivalent_objects a c"
    proof -
      obtain f where f: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> equivalence_map f"
        using assms equivalent_objects_def by auto
      obtain g \<eta> \<epsilon> where E: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using f equivalence_map_def by blast
      interpret E: equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using E by auto
      obtain h where h: "\<guillemotleft>h : b \<rightarrow> c\<guillemotright> \<and> equivalence_map h"
        using assms equivalent_objects_def by auto
      obtain k \<mu> \<nu> where E': "\<guillemotleft>h : b \<rightarrow> c\<guillemotright> \<and> equivalence_in_bicategory V H \<a> \<i> src trg h k \<mu> \<nu>"
        using h equivalence_map_def by blast
      interpret E': equivalence_in_bicategory V H \<a> \<i> src trg h k \<mu> \<nu>
        using E' by auto
      interpret EE': composite_equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon> h k \<mu> \<nu>
        using E E' by (unfold_locales, blast)
      show ?thesis
        using E E' EE'.is_equivalence equivalent_objects_def equivalence_map_def by auto
    qed

  end

  subsection "Transporting Arrows along Equivalences"

  text \<open>
    We show in this section that transporting the arrows of one hom-category to another
    along connecting equivalence maps yields an equivalence of categories.
    This is useful, because it seems otherwise hard to establish that the transporting
    functor is full.
  \<close>

  locale two_equivalences_in_bicategory =
    bicategory V H \<a> \<i> src trg +
    e\<^sub>0: equivalence_in_bicategory V H \<a> \<i> src trg e\<^sub>0 d\<^sub>0 \<eta>\<^sub>0 \<epsilon>\<^sub>0 +
    e\<^sub>1: equivalence_in_bicategory V H \<a> \<i> src trg e\<^sub>1 d\<^sub>1 \<eta>\<^sub>1 \<epsilon>\<^sub>1
  for V :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"       (infixr "\<cdot>" 55)
  and H :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"       (infixr "\<star>" 53)
  and \<a> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<a>[_, _, _]")
  and \<i> :: "'a \<Rightarrow> 'a"             ("\<i>[_]")
  and src :: "'a \<Rightarrow> 'a"
  and trg :: "'a \<Rightarrow> 'a"
  and e\<^sub>0 :: "'a"
  and d\<^sub>0 :: "'a"
  and \<eta>\<^sub>0 :: "'a"
  and \<epsilon>\<^sub>0 :: "'a"
  and e\<^sub>1 :: "'a"
  and d\<^sub>1 :: "'a"
  and \<eta>\<^sub>1 :: "'a"
  and \<epsilon>\<^sub>1 :: "'a"
  begin

    interpretation hom: subcategory V \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>\<close>
      using hhom_is_subcategory by simp

    (* TODO: The preceding interpretation somehow brings in unwanted notation. *)
    no_notation in_hom        ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    interpretation hom': subcategory V \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>\<close>
      using hhom_is_subcategory by simp

    no_notation in_hom        ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    abbreviation (input) F
    where "F \<equiv> \<lambda>\<mu>. e\<^sub>1 \<star> \<mu> \<star> d\<^sub>0"

    interpretation F: "functor" hom.comp hom'.comp F
    proof
      show 1: "\<And>f. hom.arr f \<Longrightarrow> hom'.arr (e\<^sub>1 \<star> f \<star> d\<^sub>0)"
        using hom.arr_char hom'.arr_char in_hhom_def e\<^sub>0.antipar(1-2) by simp
      show "\<And>f. \<not> hom.arr f \<Longrightarrow> e\<^sub>1 \<star> f \<star> d\<^sub>0 = hom'.null"
        using 1 hom.arr_char hom'.null_char in_hhom_def
        by (metis e\<^sub>0.antipar(1) hseqE hseq_char' hcomp_simps(2))
      show "\<And>f. hom.arr f \<Longrightarrow> hom'.dom (e\<^sub>1 \<star> f \<star> d\<^sub>0) = e\<^sub>1 \<star> hom.dom f \<star> d\<^sub>0"
        using hom.arr_char hom.dom_char hom'.arr_char hom'.dom_char
        by (metis 1 hcomp_simps(3) e\<^sub>0.ide_right e\<^sub>1.ide_left hom'.inclusion hseq_char ide_char)
      show "\<And>f. hom.arr f \<Longrightarrow> hom'.cod (e\<^sub>1 \<star> f \<star> d\<^sub>0) = e\<^sub>1 \<star> hom.cod f \<star> d\<^sub>0"
        using hom.arr_char hom.cod_char hom'.arr_char hom'.cod_char
        by (metis 1 hcomp_simps(4) e\<^sub>0.ide_right e\<^sub>1.ide_left hom'.inclusion hseq_char ide_char)
      show "\<And>g f. hom.seq g f \<Longrightarrow>
                   e\<^sub>1 \<star> hom.comp g f \<star> d\<^sub>0 = hom'.comp (e\<^sub>1 \<star> g \<star> d\<^sub>0) (e\<^sub>1 \<star> f \<star> d\<^sub>0)"
        using 1 hom.seq_char hom.arr_char hom.comp_char hom'.arr_char hom'.comp_char
              whisker_left [of e\<^sub>1] whisker_right [of d\<^sub>0]
        apply auto
         apply (metis hseq_char seqE src_vcomp)
        by (metis hseq_char hseq_char')
    qed

    abbreviation (input) G
    where "G \<equiv> \<lambda>\<mu>'. d\<^sub>1 \<star> \<mu>' \<star> e\<^sub>0"
    
    interpretation G: "functor" hom'.comp hom.comp G
    proof
      show 1: "\<And>f. hom'.arr f \<Longrightarrow> hom.arr (d\<^sub>1 \<star> f \<star> e\<^sub>0)"
        using hom.arr_char hom'.arr_char in_hhom_def e\<^sub>1.antipar(1) e\<^sub>1.antipar(2)
        by simp
      show "\<And>f. \<not> hom'.arr f \<Longrightarrow> d\<^sub>1 \<star> f \<star> e\<^sub>0 = hom.null"
        using 1 hom.arr_char hom'.null_char in_hhom_def
        by (metis e\<^sub>1.antipar(2) hom'.arrI hom.null_char hseqE hseq_char' hcomp_simps(2))
      show "\<And>f. hom'.arr f \<Longrightarrow> hom.dom (d\<^sub>1 \<star> f \<star> e\<^sub>0) = d\<^sub>1 \<star> hom'.dom f \<star> e\<^sub>0"
        using 1 hom.arr_char hom.dom_char hom'.arr_char hom'.dom_char
        by (metis hcomp_simps(3) e\<^sub>0.ide_left e\<^sub>1.ide_right hom.inclusion hseq_char ide_char)
      show "\<And>f. hom'.arr f \<Longrightarrow> hom.cod (d\<^sub>1 \<star> f \<star> e\<^sub>0) = d\<^sub>1 \<star> hom'.cod f \<star> e\<^sub>0"
        using 1 hom.arr_char hom.cod_char hom'.arr_char hom'.cod_char
        by (metis hcomp_simps(4) e\<^sub>0.ide_left e\<^sub>1.ide_right hom.inclusion hseq_char ide_char)
      show "\<And>g f. hom'.seq g f \<Longrightarrow>
                   d\<^sub>1 \<star> hom'.comp g f \<star> e\<^sub>0 = hom.comp (d\<^sub>1 \<star> g \<star> e\<^sub>0) (d\<^sub>1 \<star> f \<star> e\<^sub>0)"
        using 1 hom'.seq_char hom'.arr_char hom'.comp_char hom.arr_char hom.comp_char
              whisker_left [of d\<^sub>1] whisker_right [of e\<^sub>0]
        apply auto
         apply (metis hseq_char seqE src_vcomp)
        by (metis hseq_char hseq_char')
    qed

    interpretation GF: composite_functor hom.comp hom'.comp hom.comp F G ..
    interpretation FG: composite_functor hom'.comp hom.comp hom'.comp G F ..

    abbreviation (input) \<phi>\<^sub>0
    where "\<phi>\<^sub>0 f \<equiv> (d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, f \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (f \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                    ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[f, d\<^sub>0, e\<^sub>0]) \<cdot> (\<eta>\<^sub>1 \<star> f \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[f \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[f]"

    lemma \<phi>\<^sub>0_in_hom:
    assumes "\<guillemotleft>f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>" and "ide f"
    shows "\<guillemotleft>\<phi>\<^sub>0 f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
    and "\<guillemotleft>\<phi>\<^sub>0 f : f \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> f \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
    proof -
      show "\<guillemotleft>\<phi>\<^sub>0 f : f \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> f \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
        using assms e\<^sub>0.antipar e\<^sub>1.antipar by fastforce
      thus "\<guillemotleft>\<phi>\<^sub>0 f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
        using assms src_dom [of "\<phi>\<^sub>0 f"] trg_dom [of "\<phi>\<^sub>0 f"]
        by (metis arrI dom_comp in_hhom_def runit'_simps(4) seqE)
    qed

    lemma iso_\<phi>\<^sub>0:
    assumes "\<guillemotleft>f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>" and "ide f"
    shows "iso (\<phi>\<^sub>0 f)"
      using assms iso_lunit' iso_runit' e\<^sub>0.antipar e\<^sub>1.antipar
      apply (intro isos_compose)
                apply auto
      by fastforce+

    interpretation \<phi>: transformation_by_components hom.comp hom.comp hom.map \<open>G o F\<close> \<phi>\<^sub>0
    proof
      fix f
      assume f: "hom.ide f"
      show "hom.in_hom (\<phi>\<^sub>0 f) (hom.map f) (GF.map f)"
      proof (unfold hom.in_hom_char, intro conjI)
        show "hom.arr (hom.map f)"
          using f by simp
        show "hom.arr (GF.map f)"
          using f by simp
        show "hom.arr (\<phi>\<^sub>0 f)"
          using f hom.ide_char hom.arr_char \<phi>\<^sub>0_in_hom by simp
        show "\<guillemotleft>\<phi>\<^sub>0 f : hom.map f \<Rightarrow> GF.map f\<guillemotright>"
          using f hom.ide_char hom.arr_char hom'.ide_char hom'.arr_char F.preserves_arr
                \<phi>\<^sub>0_in_hom
          by auto
      qed
      next
      fix \<mu>
      assume \<mu>: "hom.arr \<mu>"
      show "hom.comp (\<phi>\<^sub>0 (hom.cod \<mu>)) (hom.map \<mu>) =
            hom.comp (GF.map \<mu>) (\<phi>\<^sub>0 (hom.dom \<mu>))"
      proof -
        have "hom.comp (\<phi>\<^sub>0 (hom.cod \<mu>)) (hom.map \<mu>) = \<phi>\<^sub>0 (cod \<mu>) \<cdot> \<mu>"
        proof -
          have "hom.map \<mu> = \<mu>"
            using \<mu> by simp
          moreover have "\<phi>\<^sub>0 (hom.cod \<mu>) = \<phi>\<^sub>0 (cod \<mu>)"
            using \<mu> hom.arr_char hom.cod_char by simp
          moreover have "hom.arr (\<phi>\<^sub>0 (cod \<mu>))"
            using \<mu> hom.arr_char \<phi>\<^sub>0_in_hom [of "cod \<mu>"]
            by (metis hom.arr_cod hom.cod_simp ide_cod in_hhom_def)
          moreover have "seq (\<phi>\<^sub>0 (cod \<mu>)) \<mu>"
          proof
            show 1: "\<guillemotleft>\<mu> : dom \<mu> \<Rightarrow> cod \<mu>\<guillemotright>"
              using \<mu> hom.arr_char by auto
            show "\<guillemotleft>\<phi>\<^sub>0 (cod \<mu>) : cod \<mu> \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
              using \<mu> hom.arr_char \<phi>\<^sub>0_in_hom
              by (metis 1 arrI hom.arr_cod hom.cod_simp ide_cod)
          qed
          ultimately show ?thesis
            using \<mu> hom.comp_char by simp
        qed
        also have "... = (d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot> (\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0) \<cdot>
                           \<l>\<^sup>-\<^sup>1[cod \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[cod \<mu>] \<cdot> \<mu>"
          using \<mu> hom.arr_char comp_assoc by auto
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot> (\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0) \<cdot>
                           \<l>\<^sup>-\<^sup>1[cod \<mu> \<star> src e\<^sub>0] \<cdot> (\<mu> \<star> src e\<^sub>0)) \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using \<mu> hom.arr_char runit'_naturality [of \<mu>] comp_assoc by auto
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot> (\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0) \<cdot>
                           (src e\<^sub>1 \<star> \<mu> \<star> src e\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0]) \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using \<mu> hom.arr_char lunit'_naturality [of "\<mu> \<star> src e\<^sub>0"] by force
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot> (\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0) \<cdot>
                           (src e\<^sub>1 \<star> \<mu> \<star> src e\<^sub>0)) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using comp_assoc by simp
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot> ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<mu> \<star> d\<^sub>0 \<star> e\<^sub>0)) \<cdot>
                           (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
        proof -
          have "(\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0) \<cdot> (src e\<^sub>1 \<star> \<mu> \<star> src e\<^sub>0) = \<eta>\<^sub>1 \<star> \<mu> \<star> \<eta>\<^sub>0"
            using \<mu> hom.arr_char comp_arr_dom comp_cod_arr
                  interchange [of \<eta>\<^sub>1 "src e\<^sub>1" "cod \<mu> \<star> \<eta>\<^sub>0" "\<mu> \<star> src e\<^sub>0"]
                  interchange [of "cod \<mu>" \<mu> \<eta>\<^sub>0 "src e\<^sub>0"]
            by (metis e\<^sub>0.unit_in_hom(1) e\<^sub>0.unit_simps(2) e\<^sub>1.unit_simps(1) e\<^sub>1.unit_simps(2)
                hseqI' in_hhom_def)
          also have "... = ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<mu> \<star> d\<^sub>0 \<star> e\<^sub>0) \<cdot> (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0)"
          proof -
            have "\<eta>\<^sub>1 \<star> \<mu> \<star> \<eta>\<^sub>0 = (d\<^sub>1 \<star> e\<^sub>1) \<cdot> \<eta>\<^sub>1 \<star> \<mu> \<cdot> dom \<mu> \<star> (d\<^sub>0 \<star> e\<^sub>0) \<cdot> \<eta>\<^sub>0"
              using \<mu> hom.arr_char comp_arr_dom comp_cod_arr by auto
            also have "... = (d\<^sub>1 \<star> e\<^sub>1) \<cdot> \<eta>\<^sub>1 \<star> (\<mu> \<star> d\<^sub>0 \<star> e\<^sub>0) \<cdot> (dom \<mu> \<star> \<eta>\<^sub>0)"
              using \<mu> hom.arr_char comp_cod_arr
                    interchange [of \<mu> "dom \<mu>" "d\<^sub>0 \<star> e\<^sub>0" \<eta>\<^sub>0]
              by auto
            also have "... = ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<mu> \<star> d\<^sub>0 \<star> e\<^sub>0) \<cdot> (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0)"
              using \<mu> hom.arr_char comp_arr_dom comp_cod_arr
                    interchange [of "d\<^sub>1 \<star> e\<^sub>1" \<eta>\<^sub>1 "\<mu> \<star> d\<^sub>0 \<star> e\<^sub>0" "dom \<mu> \<star> \<eta>\<^sub>0"]
                    interchange [of \<mu> "dom \<mu>" "d\<^sub>0 \<star> e\<^sub>0" \<eta>\<^sub>0]
              by (metis e\<^sub>0.unit_in_hom(1) e\<^sub>0.unit_simps(1) e\<^sub>0.unit_simps(3) e\<^sub>1.unit_simps(1)
                  e\<^sub>1.unit_simps(3) hom.inclusion hseqI)
            finally show ?thesis by simp
          qed
          finally have "(\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0) \<cdot> (src e\<^sub>1 \<star> \<mu> \<star> src e\<^sub>0) =
                          ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<mu> \<star> d\<^sub>0 \<star> e\<^sub>0) \<cdot> (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0)"
            by simp
          thus ?thesis
            using comp_assoc by simp
        qed
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> (\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0) \<cdot> ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[dom \<mu>, d\<^sub>0, e\<^sub>0])) \<cdot>
                           (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using \<mu> hom.arr_char e\<^sub>0.antipar e\<^sub>1.antipar assoc'_naturality [of \<mu> d\<^sub>0 e\<^sub>0]
                whisker_left [of "d\<^sub>1 \<star> e\<^sub>1" "\<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0]" "\<mu> \<star> d\<^sub>0 \<star> e\<^sub>0"]
                whisker_left [of "d\<^sub>1 \<star> e\<^sub>1" "(\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0" "\<a>\<^sup>-\<^sup>1[dom \<mu>, d\<^sub>0, e\<^sub>0]"]
          by auto
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> (\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0)) \<cdot> ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[dom \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot>
                           (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using comp_assoc by simp
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> (d\<^sub>1 \<star> e\<^sub>1 \<star> (\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0) \<cdot>
                           \<a>[d\<^sub>1, e\<^sub>1, (dom \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0]) \<cdot> ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[dom \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot>
                           (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using \<mu> hom.arr_char e\<^sub>0.antipar e\<^sub>1.antipar
                assoc_naturality [of d\<^sub>1 e\<^sub>1 "(\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0"]
          by auto
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> (d\<^sub>1 \<star> e\<^sub>1 \<star> (\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0)) \<cdot>
                           \<a>[d\<^sub>1, e\<^sub>1, (dom \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot> ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[dom \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot>
                           (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using comp_assoc by simp
        also have "... = ((d\<^sub>1 \<star> (e\<^sub>1 \<star> \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0) \<cdot> (d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, dom \<mu> \<star> d\<^sub>0, e\<^sub>0])) \<cdot> 
                           \<a>[d\<^sub>1, e\<^sub>1, (dom \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot> ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[dom \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot>
                           (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using \<mu> hom.arr_char e\<^sub>0.antipar e\<^sub>1.antipar
                assoc'_naturality [of e\<^sub>1 "\<mu> \<star> d\<^sub>0" e\<^sub>0]
                whisker_left [of d\<^sub>1 "\<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]" "e\<^sub>1 \<star> (\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0"]
                whisker_left [of d\<^sub>1 "(e\<^sub>1 \<star> \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0" "\<a>\<^sup>-\<^sup>1[e\<^sub>1, dom \<mu> \<star> d\<^sub>0, e\<^sub>0]"]
          by auto
        also have "... = hom.comp (GF.map \<mu>) (\<phi>\<^sub>0 (hom.dom \<mu>))"
        proof -
          have "hom.arr (GF.map \<mu>)"
            using \<mu> by blast
          moreover have "hom.arr (\<phi>\<^sub>0 (hom.dom \<mu>))"
            using \<mu> hom.arr_char hom.in_hom_char \<phi>\<^sub>0_in_hom(1) hom.dom_closed hom.dom_simp
                  hom.inclusion ide_dom
            by metis
          moreover have "seq (GF.map \<mu>) (\<phi>\<^sub>0 (hom.dom \<mu>))"
          proof
            show "\<guillemotleft>\<phi>\<^sub>0 (hom.dom \<mu>) : dom \<mu> \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> dom \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
              using \<mu> hom.arr_char hom.dom_char hom.in_hom_char \<phi>\<^sub>0_in_hom hom.dom_closed
                    hom.dom_simp hom.inclusion ide_dom
              by metis
            show "\<guillemotleft>GF.map \<mu> : d\<^sub>1 \<star> (e\<^sub>1 \<star> dom \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0 \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
              using \<mu> hom.arr_char hom'.arr_char F.preserves_arr
              apply simp
              apply (intro hcomp_in_vhom)
              by (auto simp add: e\<^sub>0.antipar e\<^sub>1.antipar in_hhom_def)
          qed
          ultimately show ?thesis
            using \<mu> hom.comp_char comp_assoc by auto
        qed
        finally show ?thesis by blast
      qed
    qed

    lemma transformation_by_components_\<phi>\<^sub>0:
    shows "transformation_by_components hom.comp hom.comp hom.map (G o F) \<phi>\<^sub>0"
      ..

    interpretation \<phi>: natural_isomorphism hom.comp hom.comp hom.map \<open>G o F\<close> \<phi>.map
    proof
      fix f 
      assume "hom.ide f"
      hence f: "ide f \<and> \<guillemotleft>f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
        using hom.ide_char hom.arr_char by simp
      show "hom.iso (\<phi>.map f)"
      proof (unfold hom.iso_char hom.arr_char, intro conjI)
        show "iso (\<phi>.map f)"
          using f iso_\<phi>\<^sub>0 \<phi>.map_simp_ide hom.ide_char hom.arr_char by simp
        moreover show "\<guillemotleft>\<phi>.map f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
          using f hom.ide_char hom.arr_char by blast
        ultimately show "\<guillemotleft>inv (\<phi>.map f) : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
          by auto
      qed
    qed

    lemma natural_isomorphism_\<phi>:
    shows "natural_isomorphism hom.comp hom.comp hom.map (G o F) \<phi>.map"
      ..

    definition \<phi>
    where "\<phi> \<equiv> \<phi>.map"

    lemma \<phi>_ide_simp:
    assumes "\<guillemotleft>f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>" and "ide f"
    shows "\<phi> f = \<phi>\<^sub>0 f"
      unfolding \<phi>_def
      using assms hom.ide_char hom.arr_char by simp

    lemma \<phi>_components_are_iso:
    assumes "\<guillemotleft>f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>" and "ide f"
    shows "iso (\<phi> f)"
      using assms \<phi>_def \<phi>.components_are_iso hom.ide_char hom.arr_char hom.iso_char
      by simp

    lemma \<phi>_eq:
    shows "\<phi> = (\<lambda>\<mu>. if \<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright> then \<phi>\<^sub>0 (cod \<mu>) \<cdot> \<mu> else null)"
    proof
      fix \<mu>
      have "\<not> \<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright> \<Longrightarrow> \<phi>.map \<mu> = null"
        using hom.comp_char hom.null_char hom.arr_char
        by (simp add: \<phi>.is_extensional)
      moreover have "\<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright> \<Longrightarrow> \<phi>.map \<mu> = \<phi>\<^sub>0 (cod \<mu>) \<cdot> \<mu>"
        unfolding \<phi>.map_def
        apply auto
        using hom.comp_char hom.arr_char
        apply simp
        by (metis (no_types, lifting) \<phi>\<^sub>0_in_hom(1) hom.cod_closed hom.inclusion ide_cod local.ext)
      ultimately show "\<phi> \<mu> = (if \<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright> then \<phi>\<^sub>0 (cod \<mu>) \<cdot> \<mu> else null)"
        unfolding \<phi>_def by auto
    qed

    lemma \<phi>_in_hom [intro]:
    assumes "\<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
    shows "\<guillemotleft>\<phi> \<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
    and "\<guillemotleft>\<phi> \<mu> : dom \<mu> \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
    proof -
      show "\<guillemotleft>\<phi> \<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
        using assms \<phi>_eq \<phi>_def hom.arr_char \<phi>.preserves_reflects_arr by presburger
      show "\<guillemotleft>\<phi> \<mu> : dom \<mu> \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
        unfolding \<phi>_eq
        using assms apply simp
        apply (intro comp_in_homI)
              apply auto
      proof -
        show "\<guillemotleft>\<r>\<^sup>-\<^sup>1[cod \<mu>] : cod \<mu> \<Rightarrow> cod \<mu> \<star> src e\<^sub>0\<guillemotright>"
          using assms by auto
        show "\<guillemotleft>\<l>\<^sup>-\<^sup>1[cod \<mu> \<star> src e\<^sub>0] : cod \<mu> \<star> src e\<^sub>0 \<Rightarrow> src e\<^sub>1 \<star> cod \<mu> \<star> src e\<^sub>0\<guillemotright>"
          using assms by auto
        show "\<guillemotleft>\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0 : src e\<^sub>1 \<star> cod \<mu> \<star> src e\<^sub>0 \<Rightarrow> (d\<^sub>1 \<star> e\<^sub>1) \<star> cod \<mu> \<star> (d\<^sub>0 \<star> e\<^sub>0)\<guillemotright>"
          using assms e\<^sub>0.unit_in_hom(2) e\<^sub>1.unit_in_hom(2)
          apply (intro hcomp_in_vhom)
              apply auto
          by fastforce
        show "\<guillemotleft>(d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0] :
                 (d\<^sub>1 \<star> e\<^sub>1) \<star> cod \<mu> \<star> d\<^sub>0 \<star> e\<^sub>0 \<Rightarrow> (d\<^sub>1 \<star> e\<^sub>1) \<star> (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
          using assms assoc'_in_hom e\<^sub>0.antipar(1-2) e\<^sub>1.antipar(2)
          apply (intro hcomp_in_vhom) by auto
        show "\<guillemotleft>\<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] :
                (d\<^sub>1 \<star> e\<^sub>1) \<star> (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0 \<Rightarrow> d\<^sub>1 \<star> e\<^sub>1 \<star> (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
          using assms assoc_in_hom e\<^sub>0.antipar(1-2) e\<^sub>1.antipar(2) by auto
        show "\<guillemotleft>d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0] :
                 d\<^sub>1 \<star> e\<^sub>1 \<star> (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0 \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
          using assms assoc'_in_hom [of "d\<^sub>1" "e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0" "e\<^sub>0"]
                e\<^sub>0.antipar(1-2) e\<^sub>1.antipar(1-2)
          apply (intro hcomp_in_vhom)
            apply auto
          by fastforce
      qed
    qed

    lemma \<phi>_simps [simp]:
    assumes "\<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
    shows "arr (\<phi> \<mu>)"
    and "src (\<phi> \<mu>) = src e\<^sub>0" and "trg (\<phi> \<mu>) = src e\<^sub>1"
    and "dom (\<phi> \<mu>) = dom \<mu>" and "cod (\<phi> \<mu>) = d\<^sub>1 \<star> (e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0"
      using assms \<phi>_in_hom by auto

    interpretation d\<^sub>0: equivalence_in_bicategory V H \<a> \<i> src trg d\<^sub>0 e\<^sub>0 \<open>inv \<epsilon>\<^sub>0\<close> \<open>inv \<eta>\<^sub>0\<close>
      using e\<^sub>0.dual_equivalence by simp
    interpretation d\<^sub>1: equivalence_in_bicategory V H \<a> \<i> src trg d\<^sub>1 e\<^sub>1 \<open>inv \<epsilon>\<^sub>1\<close> \<open>inv \<eta>\<^sub>1\<close>
      using e\<^sub>1.dual_equivalence by simp
    interpretation d\<^sub>0e\<^sub>0: two_equivalences_in_bicategory V H \<a> \<i> src trg
                           d\<^sub>0 e\<^sub>0 \<open>inv \<epsilon>\<^sub>0\<close> \<open>inv \<eta>\<^sub>0\<close> d\<^sub>1 e\<^sub>1 \<open>inv \<epsilon>\<^sub>1\<close> \<open>inv \<eta>\<^sub>1\<close>
      ..

    interpretation \<psi>: inverse_transformation hom'.comp hom'.comp hom'.map \<open>F o G\<close> d\<^sub>0e\<^sub>0.\<phi>
    proof -
      interpret \<psi>': natural_isomorphism hom'.comp hom'.comp hom'.map \<open>F o G\<close> d\<^sub>0e\<^sub>0.\<phi>
        using d\<^sub>0e\<^sub>0.natural_isomorphism_\<phi> e\<^sub>0.antipar e\<^sub>1.antipar d\<^sub>0e\<^sub>0.\<phi>_eq d\<^sub>0e\<^sub>0.\<phi>_def by metis
      show "inverse_transformation hom'.comp hom'.comp hom'.map (F o G) d\<^sub>0e\<^sub>0.\<phi>"
        ..
    qed

    definition \<psi>
    where "\<psi> \<equiv> \<psi>.map"

    lemma \<psi>_ide_simp:
    assumes "\<guillemotleft>f': trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>" and "ide f'"
    shows "\<psi> f' = \<r>[f'] \<cdot> \<l>[f' \<star> trg e\<^sub>0] \<cdot> (\<epsilon>\<^sub>1 \<star> f' \<star> \<epsilon>\<^sub>0) \<cdot> ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>[f', e\<^sub>0, d\<^sub>0]) \<cdot>
                    \<a>\<^sup>-\<^sup>1[e\<^sub>1, d\<^sub>1, (f' \<star> e\<^sub>0) \<star> d\<^sub>0] \<cdot> (e\<^sub>1 \<star> \<a>[d\<^sub>1, f' \<star> e\<^sub>0, d\<^sub>0])"
    proof -
      have "hom'.ide f'"
        using assms hom'.ide_char hom'.arr_char by simp
      hence "\<psi>.map f' = hom'.inv (d\<^sub>0e\<^sub>0.\<phi> f')"
        using assms by simp
      also have "... = inv (d\<^sub>0e\<^sub>0.\<phi> f')"
        using hom'.inv_char \<open>hom'.ide f'\<close> by simp
      also have "... = inv (d\<^sub>0e\<^sub>0.\<phi>\<^sub>0 f')"
        using assms e\<^sub>0.antipar e\<^sub>1.antipar d\<^sub>0e\<^sub>0.\<phi>_eq d\<^sub>0e\<^sub>0.\<phi>_ide_simp [of f'] by simp
      also have "... = ((((inv \<r>\<^sup>-\<^sup>1[f'] \<cdot> inv \<l>\<^sup>-\<^sup>1[f' \<star> trg e\<^sub>0]) \<cdot> inv (inv \<epsilon>\<^sub>1 \<star> f' \<star> inv \<epsilon>\<^sub>0)) \<cdot>
                         inv ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[f', e\<^sub>0, d\<^sub>0])) \<cdot> inv \<a>[e\<^sub>1, d\<^sub>1, (f' \<star> e\<^sub>0) \<star> d\<^sub>0]) \<cdot>
                         inv (e\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[d\<^sub>1, f' \<star> e\<^sub>0, d\<^sub>0])"
      proof -
        text \<open>There has to be a better way to do this.\<close>
        have 1: "\<And>A B C D E F.
                 \<lbrakk> iso A; iso B; iso C; iso D; iso E; iso F;
                   arr (((((A \<cdot> B) \<cdot> C) \<cdot> D) \<cdot> E) \<cdot> F) \<rbrakk> \<Longrightarrow>
                 inv (((((A \<cdot> B) \<cdot> C) \<cdot> D) \<cdot> E) \<cdot> F) =
                 inv F \<cdot> inv E \<cdot> inv D \<cdot> inv C \<cdot> inv B \<cdot> inv A"
          using inv_comp isos_compose seqE by metis
        have "arr (d\<^sub>0e\<^sub>0.\<phi>\<^sub>0 f')"
          using assms e\<^sub>0.antipar(2) e\<^sub>1.antipar(2) d\<^sub>0e\<^sub>0.iso_\<phi>\<^sub>0 [of f'] iso_is_arr by simp
        moreover have "iso \<r>\<^sup>-\<^sup>1[f']"
          using assms iso_runit' by simp
        moreover have "iso \<l>\<^sup>-\<^sup>1[f' \<star> trg e\<^sub>0]"
          using assms iso_lunit' by auto
        moreover have "iso (inv \<epsilon>\<^sub>1 \<star> f' \<star> inv \<epsilon>\<^sub>0)"
          using assms e\<^sub>0.antipar(2) e\<^sub>1.antipar(2) in_hhom_def by simp
        moreover have "iso ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[f', e\<^sub>0, d\<^sub>0])"
          using assms e\<^sub>0.antipar e\<^sub>1.antipar(1) e\<^sub>1.antipar(2) in_hhom_def iso_hcomp
          by (metis calculation(1) e\<^sub>0.ide_left e\<^sub>0.ide_right e\<^sub>1.ide_left e\<^sub>1.ide_right hseqE
              ide_is_iso iso_assoc' seqE)
        moreover have "iso \<a>[e\<^sub>1, d\<^sub>1, (f' \<star> e\<^sub>0) \<star> d\<^sub>0]"
          using assms e\<^sub>0.antipar e\<^sub>1.antipar by auto
        moreover have "iso (e\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[d\<^sub>1, f' \<star> e\<^sub>0, d\<^sub>0])"
          using assms e\<^sub>0.antipar e\<^sub>1.antipar
          by (metis calculation(1) e\<^sub>0.ide_left e\<^sub>0.ide_right e\<^sub>1.ide_left e\<^sub>1.ide_right
              iso_hcomp ide_hcomp hseqE ideD(1) ide_is_iso in_hhomE iso_assoc'
              seqE hcomp_simps(1-2))
        ultimately show ?thesis
          using 1 [of "e\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[d\<^sub>1, f' \<star> e\<^sub>0, d\<^sub>0]" "\<a>[e\<^sub>1, d\<^sub>1, (f' \<star> e\<^sub>0) \<star> d\<^sub>0]"
                      "(e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[f', e\<^sub>0, d\<^sub>0]" "inv \<epsilon>\<^sub>1 \<star> f' \<star> inv \<epsilon>\<^sub>0" "\<l>\<^sup>-\<^sup>1[f' \<star> trg e\<^sub>0]" "\<r>\<^sup>-\<^sup>1[f']"]
                comp_assoc
          by (metis e\<^sub>0.antipar(2))
      qed
      also have "... = inv \<r>\<^sup>-\<^sup>1[f'] \<cdot> inv \<l>\<^sup>-\<^sup>1[f' \<star> trg e\<^sub>0] \<cdot> inv (inv \<epsilon>\<^sub>1 \<star> f' \<star> inv \<epsilon>\<^sub>0) \<cdot>
                         inv ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[f', e\<^sub>0, d\<^sub>0]) \<cdot> inv \<a>[e\<^sub>1, d\<^sub>1, (f' \<star> e\<^sub>0) \<star> d\<^sub>0] \<cdot>
                         inv (e\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[d\<^sub>1, f' \<star> e\<^sub>0, d\<^sub>0])"
        using comp_assoc by simp
      also have "... = \<r>[f'] \<cdot> \<l>[f' \<star> trg e\<^sub>0] \<cdot> (\<epsilon>\<^sub>1 \<star> f' \<star> \<epsilon>\<^sub>0) \<cdot> ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>[f', e\<^sub>0, d\<^sub>0]) \<cdot>
                         \<a>\<^sup>-\<^sup>1[e\<^sub>1, d\<^sub>1, (f' \<star> e\<^sub>0) \<star> d\<^sub>0] \<cdot> (e\<^sub>1 \<star> \<a>[d\<^sub>1, f' \<star> e\<^sub>0, d\<^sub>0])"
      proof -
        have "inv \<r>\<^sup>-\<^sup>1[f'] = \<r>[f']"
          using assms inv_inv iso_runit by blast
        moreover have "inv \<l>\<^sup>-\<^sup>1[f' \<star> trg e\<^sub>0] = \<l>[f' \<star> trg e\<^sub>0]"
          using assms inv_inv iso_lunit by auto
        moreover have "inv (inv \<epsilon>\<^sub>1 \<star> f' \<star> inv \<epsilon>\<^sub>0) = \<epsilon>\<^sub>1 \<star> f' \<star> \<epsilon>\<^sub>0"
        proof -
          have "src (inv \<epsilon>\<^sub>1) = trg f'"
            using assms(1) e\<^sub>1.antipar(2) by auto
          moreover have "src f' = trg (inv \<epsilon>\<^sub>0)"
            using assms(1) e\<^sub>0.antipar(2) by auto
          ultimately show ?thesis
            using assms(2) e\<^sub>0.counit_is_iso e\<^sub>1.counit_is_iso by simp
        qed
        ultimately show ?thesis
          using assms e\<^sub>0.antipar e\<^sub>1.antipar iso_inv_iso by auto
      qed
      finally show ?thesis
        using \<psi>_def by simp
    qed

    lemma \<psi>_components_are_iso:
    assumes "\<guillemotleft>f' : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>" and "ide f'"
    shows "iso (\<psi> f')"
      using assms \<psi>_def \<psi>.components_are_iso hom'.ide_char hom'.arr_char hom'.iso_char
      by simp

    lemma \<psi>_eq:
    shows "\<psi> = (\<lambda>\<mu>'. if \<guillemotleft>\<mu>': trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright> then
                          \<mu>' \<cdot> \<r>[dom \<mu>'] \<cdot> \<l>[dom \<mu>' \<star> trg e\<^sub>0] \<cdot> (\<epsilon>\<^sub>1 \<star> dom \<mu>' \<star> \<epsilon>\<^sub>0) \<cdot>
                            ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>[dom \<mu>', e\<^sub>0, d\<^sub>0]) \<cdot> \<a>\<^sup>-\<^sup>1[e\<^sub>1, d\<^sub>1, (dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0] \<cdot>
                            (e\<^sub>1 \<star> \<a>[d\<^sub>1, dom \<mu>' \<star> e\<^sub>0, d\<^sub>0])
                     else null)"
    proof
      fix \<mu>'
      have "\<not> \<guillemotleft>\<mu>': trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright> \<Longrightarrow> \<psi>.map \<mu>' = null"
        using \<psi>.is_extensional hom'.arr_char hom'.null_char by simp
      moreover have "\<guillemotleft>\<mu>': trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright> \<Longrightarrow>
                     \<psi>.map \<mu>' = \<mu>' \<cdot> \<r>[dom \<mu>'] \<cdot> \<l>[dom \<mu>' \<star> trg e\<^sub>0] \<cdot> (\<epsilon>\<^sub>1 \<star> dom \<mu>' \<star> \<epsilon>\<^sub>0) \<cdot>
                                  ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>[dom \<mu>', e\<^sub>0, d\<^sub>0]) \<cdot> \<a>\<^sup>-\<^sup>1[e\<^sub>1, d\<^sub>1, (dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0] \<cdot>
                                  (e\<^sub>1 \<star> \<a>[d\<^sub>1, dom \<mu>' \<star> e\<^sub>0, d\<^sub>0])"
      proof -
        assume \<mu>': "\<guillemotleft>\<mu>': trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>"
        have "\<guillemotleft>\<psi>.map (dom \<mu>') : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>"
          using \<mu>' hom'.arr_char hom'.dom_closed by auto
        moreover have "seq \<mu>' (\<psi>.map (dom \<mu>'))"
        proof -
          have "hom'.seq \<mu>' (\<psi>.map (dom \<mu>'))"
            using \<mu>' \<psi>.preserves_cod hom'.arrI
            apply (intro hom'.seqI) by auto
          thus ?thesis
            using hom'.seq_char by blast
        qed
        ultimately show ?thesis
          using \<mu>' \<psi>.is_natural_1 [of \<mu>'] hom'.comp_char hom'.arr_char hom'.dom_closed
                \<psi>_ide_simp [of "dom \<mu>'"]
          apply auto
          by (metis \<psi>_def hom'.inclusion ide_dom)
      qed
      ultimately show "\<psi> \<mu>' = (if \<guillemotleft>\<mu>' : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright> then
                                  \<mu>' \<cdot> \<r>[dom \<mu>'] \<cdot> \<l>[dom \<mu>' \<star> trg e\<^sub>0] \<cdot> (\<epsilon>\<^sub>1 \<star> dom \<mu>' \<star> \<epsilon>\<^sub>0) \<cdot>
                                    ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>[dom \<mu>', e\<^sub>0, d\<^sub>0]) \<cdot>
                                    \<a>\<^sup>-\<^sup>1[e\<^sub>1, d\<^sub>1, (dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0] \<cdot>
                                    (e\<^sub>1 \<star> \<a>[d\<^sub>1, dom \<mu>' \<star> e\<^sub>0, d\<^sub>0])
                               else null)"
        unfolding \<psi>_def by argo
    qed

    lemma \<psi>_in_hom [intro]:
    assumes "\<guillemotleft>\<mu>' : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>"
    shows "\<guillemotleft>\<psi> \<mu>' : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>"
    and "\<guillemotleft>\<psi> \<mu>' : e\<^sub>1 \<star> (d\<^sub>1 \<star> dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0 \<Rightarrow> cod \<mu>'\<guillemotright>"
    proof -
      have 0: "\<psi> \<mu>' = \<psi>.map \<mu>'"
        using \<psi>_def by auto
      hence 1: "hom'.arr (\<psi> \<mu>')"
        using assms hom'.arr_char \<psi>.preserves_reflects_arr by auto
      show "\<guillemotleft>\<psi> \<mu>' : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>"
        using 1 hom'.arr_char by blast
      show "\<guillemotleft>\<psi> \<mu>' : e\<^sub>1 \<star> (d\<^sub>1 \<star> dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0 \<Rightarrow> cod \<mu>'\<guillemotright>"
        using assms 0 1 \<psi>.preserves_hom hom'.in_hom_char hom'.arr_char
              e\<^sub>0.antipar e\<^sub>1.antipar \<psi>.preserves_dom \<psi>.preserves_cod hom'.dom_char
        apply (intro in_homI)
          apply auto[1]
      proof -
        show "dom (\<psi> \<mu>') = e\<^sub>1 \<star> (d\<^sub>1 \<star> dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0"
        proof -
          have "hom'.dom (\<psi> \<mu>') = FG.map (hom'.dom \<mu>')"
            using assms 0 \<psi>.preserves_dom hom'.arr_char
            by (metis (no_types, lifting))
          thus ?thesis
            using assms 0 1 hom.arr_char hom'.arr_char hom'.dom_char G.preserves_arr
                  hom'.dom_closed
            by auto
        qed
        show "cod (\<psi> \<mu>') = cod \<mu>'"
        proof -
          have "hom'.cod (\<psi> \<mu>') = cod \<mu>'"
            using assms 0 \<psi>.preserves_cod hom'.arr_char by auto
          thus ?thesis
            using assms 0 1 hom'.arr_char hom'.cod_char G.preserves_arr hom'.cod_closed by auto
        qed
      qed
    qed

    lemma \<psi>_simps [simp]:
    assumes "\<guillemotleft>\<mu>' : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>"
    shows "arr (\<psi> \<mu>')"
    and "src (\<psi> \<mu>') = trg e\<^sub>0" and "trg (\<psi> \<mu>') = trg e\<^sub>1"
    and "dom (\<psi> \<mu>') = e\<^sub>1 \<star> (d\<^sub>1 \<star> dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0" and "cod (\<psi> \<mu>') = cod \<mu>'"
      using assms \<psi>_in_hom by auto

    interpretation equivalence_of_categories hom'.comp hom.comp F G \<phi> \<psi>
    proof -
      interpret \<phi>: natural_isomorphism hom.comp hom.comp hom.map \<open>G o F\<close> \<phi>
        using \<phi>.natural_isomorphism_axioms \<phi>_def by simp
      interpret \<psi>: natural_isomorphism hom'.comp hom'.comp \<open>F o G\<close> hom'.map \<psi>
        using \<psi>.natural_isomorphism_axioms \<psi>_def by simp
      show "equivalence_of_categories hom'.comp hom.comp F G \<phi> \<psi>"
        ..
    qed

    lemma induces_equivalence_of_hom_categories:
    shows "equivalence_of_categories hom'.comp hom.comp F G \<phi> \<psi>"
      ..

    lemma equivalence_functor_F:
    shows "equivalence_functor hom.comp hom'.comp F"
    proof -
      interpret \<phi>': inverse_transformation hom.comp hom.comp hom.map \<open>G o F\<close> \<phi> ..
      interpret \<psi>': inverse_transformation hom'.comp hom'.comp \<open>F o G\<close> hom'.map \<psi> ..
      interpret E: equivalence_of_categories hom.comp hom'.comp G F \<psi>'.map \<phi>'.map ..
      show ?thesis
        using E.equivalence_functor_axioms by simp
    qed

    lemma equivalence_functor_G:
    shows "equivalence_functor hom'.comp hom.comp G"
      using equivalence_functor_axioms by simp

  end

  context bicategory
  begin

    text \<open>
      We now use the just-established equivalence of hom-categories to prove some cancellation
      laws for equivalence maps.  It is relatively straightforward to prove these results
      directly, without using the just-established equivalence, but the proofs are somewhat
      longer that way.
    \<close>

    lemma equivalence_cancel_left:
    assumes "equivalence_map e"
    and "par \<mu> \<mu>'" and "src e = trg \<mu>" and "e \<star> \<mu> = e \<star> \<mu>'"
    shows "\<mu> = \<mu>'"
    proof -
      obtain d \<eta> \<epsilon> where d\<eta>\<epsilon>: "equivalence_in_bicategory V H \<a> \<i> src trg e d \<eta> \<epsilon>"
        using assms equivalence_map_def by auto
      interpret e: equivalence_in_bicategory V H \<a> \<i> src trg e d \<eta> \<epsilon>
        using d\<eta>\<epsilon> by simp
      interpret i: equivalence_in_bicategory V H \<a> \<i> src trg
                     \<open>src \<mu>\<close> \<open>src \<mu>\<close> \<open>inv \<i>[src \<mu>]\<close> \<open>\<i>[src \<mu>]\<close>
        using assms iso_inv_iso iso_unit obj_src
        apply unfold_locales by simp_all
      interpret two_equivalences_in_bicategory V H \<a> \<i> src trg
                     \<open>src \<mu>\<close> \<open>src \<mu>\<close> \<open>inv \<i>[src \<mu>]\<close> \<open>\<i>[src \<mu>]\<close> e d \<eta> \<epsilon>
        ..
      interpret hom: subcategory V \<open>\<lambda>\<mu>'. in_hhom \<mu>' (src (src \<mu>)) (src e)\<close>
        using hhom_is_subcategory by blast
      interpret hom': subcategory V \<open>\<lambda>\<mu>'. in_hhom \<mu>' (trg (src \<mu>)) (trg e)\<close>
        using hhom_is_subcategory by blast
      interpret F: equivalence_functor hom.comp hom'.comp \<open>\<lambda>\<mu>'. e \<star> \<mu>' \<star> src \<mu>\<close>
        using equivalence_functor_F by simp
      have "F \<mu> = F \<mu>'"
        using assms hom.arr_char
        apply simp
        by (metis e.ide_left hcomp_reassoc(2) i.ide_right ideD(1) src_dom trg_dom trg_src)
      moreover have "hom.par \<mu> \<mu>'"
        using assms hom.arr_char hom.dom_char hom.cod_char
        by (metis (no_types, lifting) in_hhomI src_dom src_src trg_dom)
      ultimately show "\<mu> = \<mu>'"
        using F.is_faithful by blast
    qed
      
    lemma equivalence_cancel_right:
    assumes "equivalence_map e"
    and "par \<mu> \<mu>'" and "src \<mu> = trg e" and "\<mu> \<star> e = \<mu>' \<star> e"
    shows "\<mu> = \<mu>'"
    proof -
      obtain d \<eta> \<epsilon> where d\<eta>\<epsilon>: "equivalence_in_bicategory V H \<a> \<i> src trg e d \<eta> \<epsilon>"
        using assms equivalence_map_def by auto
      interpret e: equivalence_in_bicategory V H \<a> \<i> src trg e d \<eta> \<epsilon>
        using d\<eta>\<epsilon> by simp
      interpret i: equivalence_in_bicategory V H \<a> \<i> src trg
                     \<open>trg \<mu>\<close> \<open>trg \<mu>\<close> \<open>inv \<i>[trg \<mu>]\<close> \<open>\<i>[trg \<mu>]\<close>
        using assms iso_inv_iso iso_unit obj_src
        apply unfold_locales by simp_all
      interpret two_equivalences_in_bicategory V H \<a> \<i> src trg
                      e d \<eta> \<epsilon> \<open>trg \<mu>\<close> \<open>trg \<mu>\<close> \<open>inv \<i>[trg \<mu>]\<close> \<open>\<i>[trg \<mu>]\<close>
        ..
      interpret hom: subcategory V \<open>\<lambda>\<mu>'. in_hhom \<mu>' (trg e) (trg (trg \<mu>))\<close>
        using hhom_is_subcategory by blast
      interpret hom': subcategory V \<open>\<lambda>\<mu>'. in_hhom \<mu>' (src e) (src (trg \<mu>))\<close>
        using hhom_is_subcategory by blast
      interpret G: equivalence_functor hom.comp hom'.comp \<open>\<lambda>\<mu>'. trg \<mu> \<star> \<mu>' \<star> e\<close>
        using equivalence_functor_G by simp
      have "G \<mu> = G \<mu>'"
        using assms hom.arr_char by simp
      moreover have "hom.par \<mu> \<mu>'"
        using assms hom.arr_char hom.dom_char hom.cod_char
        by (metis (no_types, lifting) in_hhomI src_dom trg_dom trg_trg)
      ultimately show "\<mu> = \<mu>'"
        using G.is_faithful by blast
    qed

  end

end

