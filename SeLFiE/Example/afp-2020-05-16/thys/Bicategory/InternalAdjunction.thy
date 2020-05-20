(*  Title:       InternalAdjunction
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Adjunctions in a Bicategory"

theory InternalAdjunction
imports CanonicalIsos Strictness
begin

  text \<open>
    An \emph{internal adjunction} in a bicategory is a four-tuple \<open>(f, g, \<eta>, \<epsilon>)\<close>,
    where \<open>f\<close> and \<open>g\<close> are antiparallel 1-cells and \<open>\<guillemotleft>\<eta> : src f \<Rightarrow> g \<star> f\<guillemotright>\<close> and
    \<open>\<guillemotleft>\<epsilon> : f \<star> g \<Rightarrow> src g\<guillemotright>\<close> are 2-cells, such that the familiar ``triangle''
    (or ``zig-zag'') identities are satisfied.  We state the triangle identities
    in two equivalent forms, each of which is convenient in certain situations.
  \<close>

  locale adjunction_in_bicategory =
    adjunction_data_in_bicategory +
  assumes triangle_left: "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
  and triangle_right: "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
  begin

    lemma triangle_left':
    shows "\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] = f"
      using triangle_left triangle_equiv_form by simp

    lemma triangle_right':
    shows "\<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] = g"
      using triangle_right triangle_equiv_form by simp

  end

  text \<open>
    Internal adjunctions have a number of properties, which we now develop,
    that generalize those of ordinary adjunctions involving functors and
    natural transformations.
  \<close>

  context bicategory
  begin

    lemma adjunction_unit_determines_counit:
    assumes "adjunction_in_bicategory (\<cdot>) (\<star>) \<a> \<i> src trg f g \<eta> \<epsilon>"
    and "adjunction_in_bicategory (\<cdot>) (\<star>) \<a> \<i> src trg f g \<eta> \<epsilon>'"
    shows "\<epsilon> = \<epsilon>'"
    proof -
      interpret E: adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using assms(1) by auto
      interpret E': adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>'
        using assms(2) by auto
      text \<open>
        Note that since we want to prove the the result for an arbitrary bicategory,
        not just in for a strict bicategory, the calculation is a little more involved
        than one might expect from a treatment that suppresses canonical isomorphisms.
      \<close>
      have "\<epsilon> \<cdot> \<r>[f \<star> g] = \<r>[trg f] \<cdot> (\<epsilon> \<star> trg f)"
        using runit_naturality [of \<epsilon>] by simp
      have 1: "\<r>[f \<star> g] = (f \<star> \<r>[g]) \<cdot> \<a>[f, g, src g]"
        using E.antipar runit_hcomp by simp

      have "\<epsilon> = \<epsilon> \<cdot> (f \<star> \<r>[g] \<cdot> (g \<star> \<epsilon>') \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g])"
        using E'.triangle_right' comp_arr_dom by simp
      also have "... = \<epsilon> \<cdot> (f \<star> \<r>[g]) \<cdot> (f \<star> g \<star> \<epsilon>') \<cdot> (f \<star> \<a>[g, f, g]) \<cdot> (f \<star> \<eta> \<star> g) \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[g])"
        using E.antipar whisker_left by simp
      also have "... = \<epsilon> \<cdot> ((f \<star> \<r>[g]) \<cdot> (f \<star> g \<star> \<epsilon>')) \<cdot> (f \<star> \<a>[g, f, g]) \<cdot> (f \<star> \<eta> \<star> g) \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[g])"
        using comp_assoc by simp
      also have "... = \<epsilon> \<cdot> \<r>[f \<star> g] \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, src g] \<cdot> (f \<star> g \<star> \<epsilon>')) \<cdot>
                         (f \<star> \<a>[g, f, g]) \<cdot> (f \<star> \<eta> \<star> g) \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[g])"
      proof -
        have "f \<star> \<r>[g] = \<r>[f \<star> g] \<cdot> \<a>\<^sup>-\<^sup>1[f, g, src g]"
          using E.antipar(1) runit_hcomp(3) by auto
        thus ?thesis
          using comp_assoc by simp
      qed
      also have "... = (\<epsilon> \<cdot> \<r>[f \<star> g]) \<cdot> ((f \<star> g) \<star> \<epsilon>') \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f \<star> g] \<cdot>
                         (f \<star> \<a>[g, f, g]) \<cdot> (f \<star> \<eta> \<star> g) \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[g])"
          using E.antipar E'.counit_in_hom assoc'_naturality [of f g \<epsilon>'] comp_assoc by simp
      also have "... = \<r>[trg f] \<cdot> ((\<epsilon> \<star> trg f) \<cdot> ((f \<star> g) \<star> \<epsilon>')) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f \<star> g] \<cdot>
                         (f \<star> \<a>[g, f, g]) \<cdot> (f \<star> \<eta> \<star> g) \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[g])"
        using E.antipar E.counit_in_hom runit_naturality [of \<epsilon>] comp_assoc by simp
      also have "... = (\<l>[src g] \<cdot> (src g \<star> \<epsilon>')) \<cdot> (\<epsilon> \<star> f \<star> g) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f \<star> g] \<cdot>
                         (f \<star> \<a>[g, f, g]) \<cdot> (f \<star> \<eta> \<star> g) \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[g])"
      proof -
        have "(\<epsilon> \<star> trg f) \<cdot> ((f \<star> g) \<star> \<epsilon>') = (src g \<star> \<epsilon>') \<cdot> (\<epsilon> \<star> f \<star> g)"
          using E.antipar interchange E.counit_in_hom comp_arr_dom comp_cod_arr
          by (metis E'.counit_simps(1-3) E.counit_simps(1-3))
        thus ?thesis
          using E.antipar comp_assoc unitor_coincidence by simp
      qed
      also have "... = \<epsilon>' \<cdot> \<l>[f \<star> g] \<cdot> (\<epsilon> \<star> f \<star> g) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f \<star> g] \<cdot>
                         (f \<star> \<a>[g, f, g]) \<cdot> (f \<star> \<eta> \<star> g) \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[g])"
      proof -
        have "\<l>[src g] \<cdot> (src g \<star> \<epsilon>') = \<epsilon>' \<cdot> \<l>[f \<star> g]"
          using E.antipar lunit_naturality [of \<epsilon>'] by simp
        thus ?thesis
          using comp_assoc by simp
      qed
      also have "... = \<epsilon>' \<cdot> (\<l>[f] \<star> g) \<cdot> (\<a>\<^sup>-\<^sup>1[trg f, f, g] \<cdot> (\<epsilon> \<star> f \<star> g)) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f \<star> g] \<cdot>
                         (f \<star> \<a>[g, f, g]) \<cdot> (f \<star> \<eta> \<star> g) \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[g])"
        using E.antipar lunit_hcomp comp_assoc by simp
      also have "... = \<epsilon>' \<cdot> (\<l>[f] \<star> g) \<cdot> ((\<epsilon> \<star> f) \<star> g) \<cdot> (\<a>\<^sup>-\<^sup>1[f \<star> g, f, g] \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f \<star> g] \<cdot>
                         (f \<star> \<a>[g, f, g])) \<cdot> (f \<star> \<eta> \<star> g) \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[g])"
        using E.antipar assoc'_naturality [of \<epsilon> f g] comp_assoc by simp
      also have "... = \<epsilon>' \<cdot> (\<l>[f] \<star> g) \<cdot> ((\<epsilon> \<star> f) \<star> g) \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, f] \<star> g) \<cdot>
                         (\<a>\<^sup>-\<^sup>1[f, g \<star> f, g] \<cdot> (f \<star> \<eta> \<star> g)) \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[g])"
      proof -
        have "\<a>\<^sup>-\<^sup>1[f \<star> g, f, g] \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f \<star> g] \<cdot> (f \<star> \<a>[g, f, g]) =
              (\<a>\<^sup>-\<^sup>1[f, g, f] \<star> g) \<cdot> \<a>\<^sup>-\<^sup>1[f, g \<star> f, g]"
          using 1 E.antipar iso_assoc' iso_inv_iso pentagon' comp_assoc
                invert_side_of_triangle(2)
                  [of "\<a>\<^sup>-\<^sup>1[f \<star> g, f, g] \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f \<star> g]"
                      "(\<a>\<^sup>-\<^sup>1[f, g, f] \<star> g) \<cdot> \<a>\<^sup>-\<^sup>1[f, g \<star> f, g]" "f \<star> \<a>\<^sup>-\<^sup>1[g, f, g]"]
          by simp
        thus ?thesis
          using comp_assoc by simp
      qed
      also have "... = \<epsilon>' \<cdot> (\<l>[f] \<star> g) \<cdot> ((\<epsilon> \<star> f) \<star> g) \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, f] \<star> g) \<cdot>
                         ((f \<star> \<eta>) \<star> g) \<cdot> \<a>\<^sup>-\<^sup>1[f, trg g, g] \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[g])"
        using E.antipar assoc'_naturality [of f \<eta> g] comp_assoc by simp
      also have "... = \<epsilon>' \<cdot> (\<l>[f] \<star> g) \<cdot> ((\<epsilon> \<star> f) \<star> g) \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, f] \<star> g) \<cdot>
                         ((f \<star> \<eta>) \<star> g) \<cdot> (\<r>\<^sup>-\<^sup>1[f] \<star> g)"
      proof -
        have "\<a>\<^sup>-\<^sup>1[f, trg g, g] \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[g]) = \<r>\<^sup>-\<^sup>1[f] \<star> g"
        proof -
          have "\<r>\<^sup>-\<^sup>1[f] \<star> g = inv (\<r>[f] \<star> g)"
            using E.antipar by simp
          also have "... = inv ((f \<star> \<l>[g]) \<cdot> \<a>[f, trg g, g])"
            using E.antipar by (simp add: triangle)
          also have "... = \<a>\<^sup>-\<^sup>1[f, trg g, g] \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[g])"
            using E.antipar inv_comp by simp
          finally show ?thesis by simp
        qed
        thus ?thesis by simp
      qed
      also have "... = \<epsilon>' \<cdot> (\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] \<star> g)"
        using E.antipar whisker_right by simp
      also have "... = \<epsilon>'"
        using E.triangle_left' comp_arr_dom by simp
      finally show ?thesis by simp
    qed

  end

  subsection "Adjoint Transpose"

  context adjunction_in_bicategory
  begin

    interpretation E: self_evaluation_map V H \<a> \<i> src trg ..
    notation E.eval ("\<lbrace>_\<rbrace>")

    text \<open>
      Just as for an ordinary adjunction between categories, an adjunction in a bicategory
      determines bijections between hom-sets.  There are two versions of this relationship:
      depending on whether the transposition is occurring on the left (\emph{i.e.}~``output'')
      side or the right (\emph{i.e.}~``input'') side.
    \<close>

    definition trnl\<^sub>\<eta>
    where "trnl\<^sub>\<eta> v \<mu> \<equiv> (g \<star> \<mu>) \<cdot> \<a>[g, f, v] \<cdot> (\<eta> \<star> v) \<cdot> \<l>\<^sup>-\<^sup>1[v]"

    definition trnl\<^sub>\<epsilon>
    where "trnl\<^sub>\<epsilon> u \<nu> \<equiv> \<l>[u] \<cdot> (\<epsilon> \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, u] \<cdot> (f \<star> \<nu>)"

    lemma adjoint_transpose_left:
    assumes "ide u" and "ide v" and "src f = trg v" and "src g = trg u"
    shows "trnl\<^sub>\<eta> v \<in> hom (f \<star> v) u \<rightarrow> hom v (g \<star> u)"
    and "trnl\<^sub>\<epsilon> u \<in> hom v (g \<star> u) \<rightarrow> hom (f \<star> v) u"
    and "\<guillemotleft>\<mu> : f \<star> v \<Rightarrow> u\<guillemotright> \<Longrightarrow> trnl\<^sub>\<epsilon> u (trnl\<^sub>\<eta> v \<mu>) = \<mu>"
    and "\<guillemotleft>\<nu> : v \<Rightarrow> g \<star> u\<guillemotright> \<Longrightarrow> trnl\<^sub>\<eta> v (trnl\<^sub>\<epsilon> u \<nu>) = \<nu>"
    and "bij_betw (trnl\<^sub>\<eta> v) (hom (f \<star> v) u) (hom v (g \<star> u))"
    and "bij_betw (trnl\<^sub>\<epsilon> u) (hom v (g \<star> u)) (hom (f \<star> v) u)"
    proof -
      show A: "trnl\<^sub>\<eta> v \<in> hom (f \<star> v) u \<rightarrow> hom v (g \<star> u)"
        using assms antipar trnl\<^sub>\<eta>_def by fastforce
      show B: "trnl\<^sub>\<epsilon> u \<in> hom v (g \<star> u) \<rightarrow> hom (f \<star> v) u"
        using assms antipar trnl\<^sub>\<epsilon>_def by fastforce
      show C: "\<And>\<mu>. \<guillemotleft>\<mu> : f \<star> v \<Rightarrow> u\<guillemotright> \<Longrightarrow> trnl\<^sub>\<epsilon> u (trnl\<^sub>\<eta> v \<mu>) = \<mu>"
      proof -
        fix \<mu>
        assume \<mu>: "\<guillemotleft>\<mu> : f \<star> v \<Rightarrow> u\<guillemotright>"
        have "trnl\<^sub>\<epsilon> u (trnl\<^sub>\<eta> v \<mu>) =
              \<l>[u] \<cdot> (\<epsilon> \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, u] \<cdot> (f \<star> (g \<star> \<mu>) \<cdot> \<a>[g, f, v] \<cdot> (\<eta> \<star> v) \<cdot> \<l>\<^sup>-\<^sup>1[v])"
          using trnl\<^sub>\<eta>_def trnl\<^sub>\<epsilon>_def by simp
        also have "... = \<l>[u] \<cdot> (\<epsilon> \<star> u) \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, u] \<cdot> (f \<star> g \<star> \<mu>)) \<cdot> (f \<star> \<a>[g, f, v]) \<cdot>
                           (f \<star> \<eta> \<star> v) \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[v])"
          using assms \<mu> antipar whisker_left comp_assoc by auto
        also have "... = \<l>[u] \<cdot> ((\<epsilon> \<star> u) \<cdot> ((f \<star> g) \<star> \<mu>)) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f \<star> v] \<cdot> (f \<star> \<a>[g, f, v]) \<cdot>
                           (f \<star> \<eta> \<star> v) \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[v])"
          using assms \<mu> antipar assoc'_naturality [of f g \<mu>] comp_assoc by fastforce
        also have "... = \<l>[u] \<cdot> (trg u \<star> \<mu>) \<cdot>
                           (\<epsilon> \<star> f \<star> v) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f \<star> v] \<cdot> (f \<star> \<a>[g, f, v]) \<cdot>
                             (f \<star> \<eta> \<star> v) \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[v])"
        proof -
          have "(\<epsilon> \<star> u) \<cdot> ((f \<star> g) \<star> \<mu>) = (trg u \<star> \<mu>) \<cdot> (\<epsilon> \<star> f \<star> v)"
            using assms \<mu> antipar comp_cod_arr comp_arr_dom
                  interchange [of "trg u" \<epsilon> \<mu> "f \<star> v"] interchange [of \<epsilon> "f \<star> g" u \<mu>]
            by auto
          thus ?thesis
            using comp_assoc by simp
        qed
        also have "... = \<l>[u] \<cdot> (trg u \<star> \<mu>) \<cdot> \<a>[trg f, f, v] \<cdot> 
                           ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<star> v) \<cdot>
                             \<a>\<^sup>-\<^sup>1[f, trg v, v] \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[v])"
        proof -
          have 1: "(\<epsilon> \<star> f \<star> v) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f \<star> v] \<cdot> (f \<star> \<a>[g, f, v]) \<cdot> (f \<star> \<eta> \<star> v) =
                   \<a>[trg f, f, v] \<cdot> ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<star> v) \<cdot> \<a>\<^sup>-\<^sup>1[f, trg v, v]"
          proof -
            have "(\<epsilon> \<star> f \<star> v) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f \<star> v] \<cdot> (f \<star> \<a>[g, f, v]) \<cdot> (f \<star> \<eta> \<star> v) =
                   (\<epsilon> \<star> f \<star> v) \<cdot>
                     \<a>[f \<star> g, f, v] \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, f] \<star> v) \<cdot> \<a>\<^sup>-\<^sup>1[f, g \<star> f, v] \<cdot>
                       (f \<star> \<eta> \<star> v)"
            proof -
              have "(\<epsilon> \<star> f \<star> v) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f \<star> v] \<cdot> (f \<star> \<a>[g, f, v]) \<cdot> (f \<star> \<eta> \<star> v) =
                    (\<epsilon> \<star> f \<star> v) \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, f \<star> v] \<cdot> (f \<star> \<a>[g, f, v])) \<cdot> (f \<star> \<eta> \<star> v)"
                using comp_assoc by simp
              also have "... = (\<epsilon> \<star> f \<star> v) \<cdot>
                                 \<a>[f \<star> g, f, v] \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, f] \<star> v) \<cdot> \<a>\<^sup>-\<^sup>1[f, g \<star> f, v] \<cdot>
                                   (f \<star> \<eta> \<star> v)"
              proof -
                have "\<a>\<^sup>-\<^sup>1[f, g, f \<star> v] \<cdot> (f \<star> \<a>[g, f, v]) =
                       \<a>[f \<star> g, f, v] \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, f] \<star> v) \<cdot> \<a>\<^sup>-\<^sup>1[f, g \<star> f, v]"
                  using assms antipar canI_associator_0 whisker_can_left_0 whisker_can_right_0
                        canI_associator_hcomp(1-3)
                  by simp
                thus ?thesis
                  using comp_assoc by simp
              qed
              finally show ?thesis by blast
            qed
            also have "... = ((\<epsilon> \<star> f \<star> v) \<cdot> \<a>[f \<star> g, f, v]) \<cdot>
                               (\<a>\<^sup>-\<^sup>1[f, g, f] \<star> v) \<cdot> ((f \<star> \<eta>) \<star> v) \<cdot>
                                 \<a>\<^sup>-\<^sup>1[f, trg v, v]"
              using assms \<mu> antipar assoc'_naturality [of f \<eta> v] comp_assoc by simp
            also have "... = (\<a>[trg f, f, v] \<cdot> ((\<epsilon> \<star> f) \<star> v)) \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, f] \<star> v) \<cdot> ((f \<star> \<eta>) \<star> v) \<cdot>
                                 \<a>\<^sup>-\<^sup>1[f, trg v, v]"
              using assms \<mu> antipar assoc_naturality [of \<epsilon> f v] by simp
            also have "... = \<a>[trg f, f, v] \<cdot>
                               (((\<epsilon> \<star> f) \<star> v) \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, f] \<star> v) \<cdot> ((f \<star> \<eta>) \<star> v)) \<cdot>
                                 \<a>\<^sup>-\<^sup>1[f, trg v, v]"
              using comp_assoc by simp
            also have "... = \<a>[trg f, f, v] \<cdot> ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<star> v) \<cdot> \<a>\<^sup>-\<^sup>1[f, trg v, v]"
              using assms \<mu> antipar whisker_right by simp
            finally show ?thesis by simp
          qed
          show ?thesis
            using 1 comp_assoc by metis
        qed
        also have "... = \<l>[u] \<cdot> (trg u \<star> \<mu>) \<cdot>
                           \<a>[trg f, f, v] \<cdot> (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<star> v) \<cdot> \<a>\<^sup>-\<^sup>1[f, trg v, v] \<cdot> (f \<star> \<l>\<^sup>-\<^sup>1[v])"
          using assms \<mu> antipar triangle_left by simp
        also have "... = \<l>[u] \<cdot> (trg u \<star> \<mu>) \<cdot> can (\<^bold>\<langle>trg u\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>v\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>v\<^bold>\<rangle>)"
          using assms \<mu> antipar canI_unitor_0 canI_associator_1
                canI_associator_1(1-2) [of f v] whisker_can_right_0 whisker_can_left_0
          by simp
        also have "... = \<l>[u] \<cdot> (trg u \<star> \<mu>) \<cdot> \<l>\<^sup>-\<^sup>1[f \<star> v]"
          unfolding can_def using assms antipar comp_arr_dom comp_cod_arr \<ll>_ide_simp
          by simp
        also have "... = (\<l>[u] \<cdot> \<l>\<^sup>-\<^sup>1[u]) \<cdot> \<mu>"
          using assms \<mu> lunit'_naturality [of \<mu>] comp_assoc by auto
        also have "... = \<mu>"
          using assms \<mu> comp_cod_arr iso_lunit comp_arr_inv inv_is_inverse by auto
        finally show "trnl\<^sub>\<epsilon> u (trnl\<^sub>\<eta> v \<mu>) = \<mu>" by simp
      qed
      show D: "\<And>\<nu>. \<guillemotleft>\<nu> : v \<Rightarrow> g \<star> u\<guillemotright> \<Longrightarrow> trnl\<^sub>\<eta> v (trnl\<^sub>\<epsilon> u \<nu>) = \<nu>"
      proof -
        fix \<nu>
        assume \<nu>: "\<guillemotleft>\<nu> : v \<Rightarrow> g \<star> u\<guillemotright>"
        have "trnl\<^sub>\<eta> v (trnl\<^sub>\<epsilon> u \<nu>) =
              (g \<star> \<l>[u] \<cdot> (\<epsilon> \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, u] \<cdot> (f \<star> \<nu>)) \<cdot> \<a>[g, f, v] \<cdot> (\<eta> \<star> v) \<cdot> \<l>\<^sup>-\<^sup>1[v]"
          using trnl\<^sub>\<eta>_def trnl\<^sub>\<epsilon>_def by simp
        also have "... = (g \<star> \<l>[u]) \<cdot> (g \<star> \<epsilon> \<star> u) \<cdot> (g \<star> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot> (g \<star> f \<star> \<nu>) \<cdot>
                           \<a>[g, f, v] \<cdot> (\<eta> \<star> v) \<cdot> \<l>\<^sup>-\<^sup>1[v]"
          using assms \<nu> antipar interchange [of g "g \<cdot> g \<cdot> g"] comp_assoc by auto
        also have "... = ((g \<star> \<l>[u]) \<cdot> (g \<star> \<epsilon> \<star> u) \<cdot> (g \<star> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot>
                           \<a>[g, f, g \<star> u] \<cdot> (\<eta> \<star> g \<star> u)) \<cdot> (trg v \<star> \<nu>) \<cdot> \<l>\<^sup>-\<^sup>1[v]"
        proof -
          have "(g \<star> f \<star> \<nu>) \<cdot> \<a>[g, f, v] \<cdot> (\<eta> \<star> v) \<cdot> \<l>\<^sup>-\<^sup>1[v] =
                \<a>[g, f, g \<star> u] \<cdot> (\<eta> \<star> g \<star> u) \<cdot> (trg v \<star> \<nu>) \<cdot> \<l>\<^sup>-\<^sup>1[v]"
          proof -
            have "(g \<star> f \<star> \<nu>) \<cdot> \<a>[g, f, v] \<cdot> (\<eta> \<star> v) \<cdot> \<l>\<^sup>-\<^sup>1[v] =
                  \<a>[g, f, g \<star> u] \<cdot> ((g \<star> f) \<star> \<nu>) \<cdot> (\<eta> \<star> v) \<cdot> \<l>\<^sup>-\<^sup>1[v]"
            proof -
              have "(g \<star> f \<star> \<nu>) \<cdot> \<a>[g, f, v] = \<a>[g, f, g \<star> u] \<cdot> ((g \<star> f) \<star> \<nu>)"
                using assms \<nu> antipar assoc_naturality [of g f \<nu>] by auto
              thus ?thesis
                using assms comp_assoc by metis
            qed
            also have "... = \<a>[g, f, g \<star> u] \<cdot> (\<eta> \<star> g \<star> u) \<cdot> (trg v \<star> \<nu>) \<cdot> \<l>\<^sup>-\<^sup>1[v]"
            proof -
              have "((g \<star> f) \<star> \<nu>) \<cdot> (\<eta> \<star> v) = (\<eta> \<star> g \<star> u) \<cdot> (trg v \<star> \<nu>)"
                using assms \<nu> antipar comp_arr_dom comp_cod_arr
                      interchange [of "g \<star> f" \<eta> \<nu> v] interchange [of \<eta> "trg v" "g \<star> u" \<nu>]
                by auto
              thus ?thesis
                using comp_assoc by metis
            qed
            finally show ?thesis by blast
          qed
          thus ?thesis using comp_assoc by simp
        qed
        also have "... = \<l>[g \<star> u] \<cdot> (trg v \<star> \<nu>) \<cdot> \<l>\<^sup>-\<^sup>1[v]"
        proof -
          have "(g \<star> \<l>[u]) \<cdot> (g \<star> \<epsilon> \<star> u) \<cdot> (g \<star> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot> \<a>[g, f, g \<star> u] \<cdot> (\<eta> \<star> g \<star> u) =
                \<l>[g \<star> u]"
          proof -
            have "(g \<star> \<l>[u]) \<cdot> (g \<star> \<epsilon> \<star> u) \<cdot> (g \<star> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot> \<a>[g, f, g \<star> u] \<cdot> (\<eta> \<star> g \<star> u) =
                  (g \<star> \<l>[u]) \<cdot> \<a>[g, trg u, u] \<cdot>
                     ((g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<star> u) \<cdot>
                        \<a>\<^sup>-\<^sup>1[trg v, g, u]"
            proof -
              have "(g \<star> \<l>[u]) \<cdot> (g \<star> \<epsilon> \<star> u) \<cdot> (g \<star> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot> \<a>[g, f, g \<star> u] \<cdot> (\<eta> \<star> g \<star> u) =
                    (g \<star> \<l>[u]) \<cdot> (g \<star> \<epsilon> \<star> u) \<cdot> (g \<star> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot> \<a>[g, f, g \<star> u] \<cdot>
                       ((\<eta> \<star> g \<star> u) \<cdot> \<a>[trg v, g, u]) \<cdot> \<a>\<^sup>-\<^sup>1[trg v, g, u]"
                using assms antipar comp_arr_dom comp_assoc comp_assoc_assoc'(1) by simp
              also have "... = (g \<star> \<l>[u]) \<cdot> (g \<star> \<epsilon> \<star> u) \<cdot> (g \<star> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot> \<a>[g, f, g \<star> u] \<cdot>
                                 (\<a>[g \<star> f, g, u] \<cdot> ((\<eta> \<star> g) \<star> u)) \<cdot> \<a>\<^sup>-\<^sup>1[trg v, g, u]"
                using assms antipar assoc_naturality [of \<eta> g u] by simp
              also have "... = (g \<star> \<l>[u]) \<cdot> (g \<star> \<epsilon> \<star> u) \<cdot>
                                 ((g \<star> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot> \<a>[g, f, g \<star> u] \<cdot> \<a>[g \<star> f, g, u]) \<cdot>
                                   ((\<eta> \<star> g) \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[trg v, g, u]"
                using comp_assoc by simp
              also have "... = (g \<star> \<l>[u]) \<cdot> ((\<a>[g, trg u, u] \<cdot> \<a>\<^sup>-\<^sup>1[g, trg u, u]) \<cdot> (g \<star> \<epsilon> \<star> u)) \<cdot>
                                 ((g \<star> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot> \<a>[g, f, g \<star> u] \<cdot> \<a>[g \<star> f, g, u]) \<cdot>
                                   ((\<eta> \<star> g) \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[trg v, g, u]"
              proof -
                have "(\<a>[g, trg u, u] \<cdot> \<a>\<^sup>-\<^sup>1[g, trg u, u]) \<cdot> (g \<star> \<epsilon> \<star> u) = g \<star> \<epsilon> \<star> u"
                  using assms antipar comp_cod_arr comp_assoc_assoc'(1) by simp
                thus ?thesis
                  using comp_assoc by simp
              qed
              also have "... = (g \<star> \<l>[u]) \<cdot> \<a>[g, trg u, u] \<cdot> (\<a>\<^sup>-\<^sup>1[g, trg u, u] \<cdot> (g \<star> \<epsilon> \<star> u)) \<cdot>
                                 (g \<star> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot> \<a>[g, f, g \<star> u] \<cdot> \<a>[g \<star> f, g, u] \<cdot>
                                   ((\<eta> \<star> g) \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[trg v, g, u]"
                using comp_assoc by simp
              also have "... = (g \<star> \<l>[u]) \<cdot> \<a>[g, trg u, u] \<cdot> (((g \<star> \<epsilon>) \<star> u) \<cdot> (\<a>\<^sup>-\<^sup>1[g, f \<star> g, u] \<cdot>
                                 (g \<star> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot> \<a>[g, f, g \<star> u] \<cdot> \<a>[g \<star> f, g, u]) \<cdot>
                                   ((\<eta> \<star> g) \<star> u)) \<cdot> \<a>\<^sup>-\<^sup>1[trg v, g, u]"
                using assms antipar assoc'_naturality [of g \<epsilon> u] comp_assoc by simp
              also have "... = (g \<star> \<l>[u]) \<cdot> \<a>[g, trg u, u] \<cdot>
                                 ((g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<star> u) \<cdot>
                                   \<a>\<^sup>-\<^sup>1[trg v, g, u]"
              proof -
                have "\<a>\<^sup>-\<^sup>1[g, f \<star> g, u] \<cdot> (g \<star> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot> \<a>[g, f, g \<star> u] \<cdot> \<a>[g \<star> f, g, u] =
                      \<a>[g, f, g] \<star> u"
                  using assms antipar canI_associator_0 whisker_can_left_0 whisker_can_right_0
                        canI_associator_hcomp
                  by simp
                hence "((g \<star> \<epsilon>) \<star> u) \<cdot>
                          (\<a>\<^sup>-\<^sup>1[g, f \<star> g, u] \<cdot> (g \<star> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot> \<a>[g, f, g \<star> u] \<cdot> \<a>[g \<star> f, g, u]) \<cdot>
                             ((\<eta> \<star> g) \<star> u) =
                       (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<star> u"
                  using assms antipar whisker_right by simp
                thus ?thesis by simp
              qed
              finally show ?thesis by blast
            qed
            also have "... = (g \<star> \<l>[u]) \<cdot> \<a>[g, trg u, u] \<cdot> (\<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g] \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[trg g, g, u]"
              using assms antipar triangle_right by simp
            also have "... = can (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>u\<^bold>\<rangle>) (\<^bold>\<langle>trg g\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>u\<^bold>\<rangle>)"
            proof -
              have "(g \<star> \<l>[u]) \<cdot> \<a>[g, trg u, u] \<cdot> (\<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g] \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[trg g, g, u] =
                    ((g \<star> \<l>[u]) \<cdot> \<a>[g, trg u, u] \<cdot> (\<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g] \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[trg g, g, u])"
                using comp_assoc by simp
              moreover have "... = can (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>u\<^bold>\<rangle>) (\<^bold>\<langle>trg g\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>u\<^bold>\<rangle>)"
                using assms antipar canI_unitor_0 canI_associator_1 [of g u] inv_can
                  whisker_can_left_0 whisker_can_right_0
                by simp
              ultimately show ?thesis by simp
            qed
            also have "... = \<l>[g \<star> u]"
              unfolding can_def using assms comp_arr_dom comp_cod_arr \<ll>_ide_simp by simp
            finally show ?thesis by simp
          qed
          thus ?thesis by simp
        qed
        also have "... = (\<l>[g \<star> u] \<cdot> \<l>\<^sup>-\<^sup>1[g \<star> u]) \<cdot> \<nu>"
          using assms \<nu> lunit'_naturality comp_assoc by auto
        also have "... = \<nu>"
          using assms \<nu> comp_cod_arr iso_lunit comp_arr_inv inv_is_inverse by auto
        finally show "trnl\<^sub>\<eta> v (trnl\<^sub>\<epsilon> u \<nu>) = \<nu>" by simp
      qed
      show "bij_betw (trnl\<^sub>\<eta> v) (hom (f \<star> v) u) (hom v (g \<star> u))"
        using A B C D by (intro bij_betwI, auto)
      show "bij_betw (trnl\<^sub>\<epsilon> u) (hom v (g \<star> u)) (hom (f \<star> v) u)"
        using A B C D by (intro bij_betwI, auto)
    qed

    lemma trnl\<^sub>\<epsilon>_comp:
    assumes "ide u" and "seq \<mu> \<nu>" and "src f = trg \<mu>"
    shows "trnl\<^sub>\<epsilon> u (\<mu> \<cdot> \<nu>) = trnl\<^sub>\<epsilon> u \<mu> \<cdot> (f \<star> \<nu>)"
      using assms trnl\<^sub>\<epsilon>_def whisker_left [of f \<mu> \<nu>] comp_assoc by auto

    definition trnr\<^sub>\<eta>
    where "trnr\<^sub>\<eta> v \<mu> \<equiv> (\<mu> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[v, g, f] \<cdot> (v \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[v]"

    definition trnr\<^sub>\<epsilon>
    where "trnr\<^sub>\<epsilon> u \<nu> \<equiv> \<r>[u] \<cdot> (u \<star> \<epsilon>) \<cdot> \<a>[u, f, g] \<cdot> (\<nu> \<star> g)"

    lemma adjoint_transpose_right:
    assumes "ide u" and "ide v" and "src v = trg g" and "src u = trg f"
    shows "trnr\<^sub>\<eta> v \<in> hom (v \<star> g) u \<rightarrow> hom v (u \<star> f)"
    and "trnr\<^sub>\<epsilon> u \<in> hom v (u \<star> f) \<rightarrow> hom (v \<star> g) u"
    and "\<guillemotleft>\<mu> : v \<star> g \<Rightarrow> u\<guillemotright> \<Longrightarrow> trnr\<^sub>\<epsilon> u (trnr\<^sub>\<eta> v \<mu>) = \<mu>"
    and "\<guillemotleft>\<nu> : v \<Rightarrow> u \<star> f\<guillemotright> \<Longrightarrow> trnr\<^sub>\<eta> v (trnr\<^sub>\<epsilon> u \<nu>) = \<nu>"
    and "bij_betw (trnr\<^sub>\<eta> v) (hom (v \<star> g) u) (hom v (u \<star> f))"
    and "bij_betw (trnr\<^sub>\<epsilon> u) (hom v (u \<star> f)) (hom (v \<star> g) u)"
    proof -
      show A: "trnr\<^sub>\<eta> v \<in> hom (v \<star> g) u \<rightarrow> hom v (u \<star> f)"
        using assms antipar trnr\<^sub>\<eta>_def by fastforce
      show B: "trnr\<^sub>\<epsilon> u \<in> hom v (u \<star> f) \<rightarrow> hom (v \<star> g) u"
        using assms antipar trnr\<^sub>\<epsilon>_def by fastforce
      show C: "\<And>\<mu>. \<guillemotleft>\<mu> : v \<star> g \<Rightarrow> u\<guillemotright> \<Longrightarrow> trnr\<^sub>\<epsilon> u (trnr\<^sub>\<eta> v \<mu>) = \<mu>"
      proof -
        fix \<mu>
        assume \<mu>: "\<guillemotleft>\<mu> : v \<star> g \<Rightarrow> u\<guillemotright>"
        have "trnr\<^sub>\<epsilon> u (trnr\<^sub>\<eta> v \<mu>) =
              \<r>[u] \<cdot> (u \<star> \<epsilon>) \<cdot> \<a>[u, f, g] \<cdot> ((\<mu> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[v, g, f] \<cdot> (v \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[v] \<star> g)"
          unfolding trnr\<^sub>\<epsilon>_def trnr\<^sub>\<eta>_def by simp
        also have "... = \<r>[u] \<cdot> (u \<star> \<epsilon>) \<cdot> (\<a>[u, f, g] \<cdot> ((\<mu> \<star> f) \<star> g)) \<cdot>
                           (\<a>\<^sup>-\<^sup>1[v, g, f] \<star> g) \<cdot> ((v \<star> \<eta>) \<star> g) \<cdot> (\<r>\<^sup>-\<^sup>1[v] \<star> g)"
          using assms \<mu> antipar whisker_right comp_assoc by auto
        also have "... = \<r>[u] \<cdot> (u \<star> \<epsilon>) \<cdot> ((\<mu> \<star> f \<star> g) \<cdot> \<a>[v \<star> g, f, g]) \<cdot>
                           (\<a>\<^sup>-\<^sup>1[v, g, f] \<star> g) \<cdot> ((v \<star> \<eta>) \<star> g) \<cdot> (\<r>\<^sup>-\<^sup>1[v] \<star> g)"
          using assms \<mu> antipar assoc_naturality [of \<mu> f g] by auto
        also have "... = \<r>[u] \<cdot> ((u \<star> \<epsilon>) \<cdot> (\<mu> \<star> f \<star> g)) \<cdot> \<a>[v \<star> g, f, g] \<cdot>
                           (\<a>\<^sup>-\<^sup>1[v, g, f] \<star> g) \<cdot> ((v \<star> \<eta>) \<star> g) \<cdot> (\<r>\<^sup>-\<^sup>1[v] \<star> g)"
          using comp_assoc by auto
        also have "... = \<r>[u] \<cdot> (\<mu> \<star> src u) \<cdot> ((v \<star> g) \<star> \<epsilon>) \<cdot> \<a>[v \<star> g, f, g] \<cdot>
                           (\<a>\<^sup>-\<^sup>1[v, g, f] \<star> g) \<cdot> ((v \<star> \<eta>) \<star> g) \<cdot> (\<r>\<^sup>-\<^sup>1[v] \<star> g)"
        proof -
          have "(u \<star> \<epsilon>) \<cdot> (\<mu> \<star> f \<star> g) = (\<mu> \<star> src u) \<cdot> ((v \<star> g) \<star> \<epsilon>)"
            using assms \<mu> antipar comp_arr_dom comp_cod_arr
                  interchange [of \<mu> "v \<star> g" "src u" \<epsilon>] interchange [of u \<mu> \<epsilon> "f \<star> g"]
            by auto
          thus ?thesis
            using comp_assoc by simp
        qed
        also have "... = \<r>[u] \<cdot> (\<mu> \<star> src u) \<cdot>
                           (((v \<star> g) \<star> \<epsilon>) \<cdot> \<a>[v \<star> g, f, g] \<cdot> (\<a>\<^sup>-\<^sup>1[v, g, f] \<star> g) \<cdot> ((v \<star> \<eta>) \<star> g)) \<cdot>
                             (\<r>\<^sup>-\<^sup>1[v] \<star> g)"
          using comp_assoc by simp
        also have "... = \<r>[u] \<cdot> (\<mu> \<star> src u) \<cdot>
                           (\<a>\<^sup>-\<^sup>1[v, g, src u] \<cdot> (v \<star> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)) \<cdot>
                             \<a>[v, src v, g]) \<cdot> (\<r>\<^sup>-\<^sup>1[v] \<star> g)"
        proof -
          have "((v \<star> g) \<star> \<epsilon>) \<cdot> \<a>[v \<star> g, f, g] \<cdot> (\<a>\<^sup>-\<^sup>1[v, g, f] \<star> g) \<cdot> ((v \<star> \<eta>) \<star> g) =
                  \<a>\<^sup>-\<^sup>1[v, g, src u] \<cdot> (v \<star> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)) \<cdot> \<a>[v, src v, g]"
          proof -
            have "((v \<star> g) \<star> \<epsilon>) \<cdot> \<a>[v \<star> g, f, g] \<cdot> (\<a>\<^sup>-\<^sup>1[v, g, f] \<star> g) \<cdot> ((v \<star> \<eta>) \<star> g) =
                    ((\<a>\<^sup>-\<^sup>1[v, g, src u] \<cdot> \<a>[v, g, src u]) \<cdot> ((v \<star> g) \<star> \<epsilon>)) \<cdot>
                      \<a>[v \<star> g, f, g] \<cdot> (\<a>\<^sup>-\<^sup>1[v, g, f] \<star> g) \<cdot> ((v \<star> \<eta>) \<star> g)"
            proof -
              have "arr v \<and> dom v = v \<and> cod v = v"
                using assms(2) ide_char by blast
              moreover have "arr g \<and> dom g = g \<and> cod g = g"
                using ide_right ide_char by blast
              ultimately show ?thesis
                by (metis (no_types) antipar(2) assms(3-4) assoc_naturality
                    counit_simps(1,3,5) hcomp_reassoc(1) comp_assoc)
            qed
            also have "... = \<a>\<^sup>-\<^sup>1[v, g, src u] \<cdot> (\<a>[v, g, src u] \<cdot> ((v \<star> g) \<star> \<epsilon>)) \<cdot>
                               \<a>[v \<star> g, f, g] \<cdot> (\<a>\<^sup>-\<^sup>1[v, g, f] \<star> g) \<cdot> ((v \<star> \<eta>) \<star> g)"
              using comp_assoc by simp
            also have "... = \<a>\<^sup>-\<^sup>1[v, g, src u] \<cdot> ((v \<star> g \<star> \<epsilon>) \<cdot> \<a>[v, g, f \<star> g]) \<cdot>
                               \<a>[v \<star> g, f, g] \<cdot> (\<a>\<^sup>-\<^sup>1[v, g, f] \<star> g) \<cdot>
                                 (\<a>\<^sup>-\<^sup>1[v, g \<star> f, g] \<cdot> \<a>[v, g \<star> f, g]) \<cdot> ((v \<star> \<eta>) \<star> g)"
            proof -
              have "\<a>[v, g, src u] \<cdot> ((v \<star> g) \<star> \<epsilon>) = (v \<star> g \<star> \<epsilon>) \<cdot> \<a>[v, g, f \<star> g]"
                using assms antipar assoc_naturality [of v g \<epsilon>] by simp
              moreover have "(\<a>\<^sup>-\<^sup>1[v, g \<star> f, g] \<cdot> \<a>[v, g \<star> f, g]) \<cdot> ((v \<star> \<eta>) \<star> g) = (v \<star> \<eta>) \<star> g"
                using assms antipar comp_cod_arr comp_assoc_assoc'(2) by simp
              ultimately show ?thesis by simp
            qed
            also have "... = \<a>\<^sup>-\<^sup>1[v, g, src u] \<cdot> (v \<star> g \<star> \<epsilon>) \<cdot>
                               \<a>[v, g, f \<star> g] \<cdot> \<a>[v \<star> g, f, g] \<cdot> (\<a>\<^sup>-\<^sup>1[v, g, f] \<star> g) \<cdot>
                                 \<a>\<^sup>-\<^sup>1[v, g \<star> f, g] \<cdot> \<a>[v, g \<star> f, g] \<cdot> ((v \<star> \<eta>) \<star> g)"
              using comp_assoc by simp
            also have "... = \<a>\<^sup>-\<^sup>1[v, g, src u] \<cdot> ((v \<star> g \<star> \<epsilon>) \<cdot>
                               (\<a>[v, g, f \<star> g] \<cdot> \<a>[v \<star> g, f, g] \<cdot> (\<a>\<^sup>-\<^sup>1[v, g, f] \<star> g) \<cdot>
                                 \<a>\<^sup>-\<^sup>1[v, g \<star> f, g]) \<cdot> (v \<star> \<eta> \<star> g)) \<cdot> \<a>[v, src v, g]"
              using assms antipar assoc_naturality [of v \<eta> g] comp_assoc by simp
            also have "... = \<a>\<^sup>-\<^sup>1[v, g, src u] \<cdot>
                               ((v \<star> g \<star> \<epsilon>) \<cdot> (v \<star> \<a>[g, f, g]) \<cdot> (v \<star> \<eta> \<star> g)) \<cdot>
                                 \<a>[v, src v, g]"
            proof -
              have "\<a>[v, g, f \<star> g] \<cdot> \<a>[v \<star> g, f, g] \<cdot> (\<a>\<^sup>-\<^sup>1[v, g, f] \<star> g) \<cdot> \<a>\<^sup>-\<^sup>1[v, g \<star> f, g] =
                    v \<star> \<a>[g, f, g]"
                using assms antipar canI_associator_0 canI_associator_hcomp
                      whisker_can_left_0 whisker_can_right_0
                by simp
              thus ?thesis
                using assms antipar whisker_left by simp
            qed
            also have "... = \<a>\<^sup>-\<^sup>1[v, g, src u] \<cdot>
                               (v \<star> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)) \<cdot>
                                 \<a>[v, src v, g]"
              using assms antipar whisker_left by simp
            finally show ?thesis by simp
          qed
          thus ?thesis by auto
        qed
        also have "... = \<r>[u] \<cdot> (\<mu> \<star> src u) \<cdot>
                          \<a>\<^sup>-\<^sup>1[v, g, src u] \<cdot> (v \<star> \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]) \<cdot>
                            \<a>[v, src v, g] \<cdot> (\<r>\<^sup>-\<^sup>1[v] \<star> g)"
              using triangle_right comp_assoc by simp
        also have "... = \<r>[u] \<cdot> (\<mu> \<star> src u) \<cdot> \<r>\<^sup>-\<^sup>1[v \<star> g]"
        proof -
          have "\<a>\<^sup>-\<^sup>1[v, g, src u] \<cdot> (v \<star> \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]) \<cdot> \<a>[v, src v, g] \<cdot> (\<r>\<^sup>-\<^sup>1[v] \<star> g) = \<r>\<^sup>-\<^sup>1[v \<star> g]"
          proof -
            have "\<a>\<^sup>-\<^sup>1[v, g, src u] \<cdot> (v \<star> \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]) \<cdot> \<a>[v, src v, g] \<cdot> (\<r>\<^sup>-\<^sup>1[v] \<star> g) =
                  \<a>\<^sup>-\<^sup>1[v, g, trg f] \<cdot> can (\<^bold>\<langle>v\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src g\<^bold>\<rangle>\<^sub>0) (\<^bold>\<langle>v\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>)"
              using assms canI_unitor_0 canI_associator_1(2-3) whisker_can_left_0(1)
                whisker_can_right_0
              by simp
            also have "... = \<a>\<^sup>-\<^sup>1[v, g, src g] \<cdot> can (\<^bold>\<langle>v\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src g\<^bold>\<rangle>\<^sub>0) (\<^bold>\<langle>v\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>)"
              using antipar by simp
            (* TODO: There should be an alternate version of whisker_can_left for this. *)
            also have "... = \<a>\<^sup>-\<^sup>1[v, g, src g] \<cdot> (v \<star> can (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src g\<^bold>\<rangle>\<^sub>0) \<^bold>\<langle>g\<^bold>\<rangle>)"
              using assms canI_unitor_0(2) whisker_can_left_0 by simp
            also have "... = \<a>\<^sup>-\<^sup>1[v, g, src g] \<cdot> (v \<star> \<r>\<^sup>-\<^sup>1[g])"
              using assms canI_unitor_0(2) by simp
            also have "... = \<r>\<^sup>-\<^sup>1[v \<star> g]"
              using assms runit_hcomp(2) by simp
            finally have "\<a>\<^sup>-\<^sup>1[v, g, src u] \<cdot> (v \<star> \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]) \<cdot> \<a>[v, src v, g] \<cdot> (\<r>\<^sup>-\<^sup>1[v] \<star> g) =
                          \<r>\<^sup>-\<^sup>1[v \<star> g]"
              by simp
            thus ?thesis by simp
          qed
          thus ?thesis by simp
        qed
        also have "... = (\<r>[u] \<cdot> \<r>\<^sup>-\<^sup>1[u]) \<cdot> \<mu>"
          using assms \<mu> runit'_naturality [of \<mu>] comp_assoc by auto
        also have "... = \<mu>"
          using \<mu> comp_cod_arr iso_runit inv_is_inverse comp_arr_inv by auto
        finally show "trnr\<^sub>\<epsilon> u (trnr\<^sub>\<eta> v \<mu>) = \<mu>" by simp
      qed
      show D: "\<And>\<nu>. \<guillemotleft>\<nu> : v \<Rightarrow> u \<star> f\<guillemotright> \<Longrightarrow> trnr\<^sub>\<eta> v (trnr\<^sub>\<epsilon> u \<nu>) = \<nu>"
      proof -
        fix \<nu>
        assume \<nu>: "\<guillemotleft>\<nu> : v \<Rightarrow> u \<star> f\<guillemotright>"
        have "trnr\<^sub>\<eta> v (trnr\<^sub>\<epsilon> u \<nu>) =
              (\<r>[u] \<cdot> (u \<star> \<epsilon>) \<cdot> \<a>[u, f, g] \<cdot> (\<nu> \<star> g) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[v, g, f] \<cdot> (v \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[v]"
          unfolding trnr\<^sub>\<eta>_def trnr\<^sub>\<epsilon>_def by simp
        also have "... = (\<r>[u] \<star> f) \<cdot> ((u \<star> \<epsilon>) \<star> f) \<cdot> (\<a>[u, f, g] \<star> f) \<cdot>
                          (((\<nu> \<star> g) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[v, g, f]) \<cdot> (v \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[v]"
          using assms \<nu> antipar whisker_right comp_assoc by auto
        also have "... = (\<r>[u] \<star> f) \<cdot> ((u \<star> \<epsilon>) \<star> f) \<cdot> (\<a>[u, f, g] \<star> f) \<cdot>
                          (\<a>\<^sup>-\<^sup>1[u \<star> f, g, f] \<cdot> (\<nu> \<star> g \<star> f)) \<cdot> (v \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[v]"
          using assms \<nu> antipar assoc'_naturality [of \<nu> g f] by auto
        also have "... = (\<r>[u] \<star> f) \<cdot> ((u \<star> \<epsilon>) \<star> f) \<cdot> (\<a>[u, f, g] \<star> f) \<cdot>
                          \<a>\<^sup>-\<^sup>1[u \<star> f, g, f] \<cdot> ((\<nu> \<star> g \<star> f) \<cdot> (v \<star> \<eta>)) \<cdot> \<r>\<^sup>-\<^sup>1[v]"
          using comp_assoc by simp
        also have "... = (\<r>[u] \<star> f) \<cdot> ((u \<star> \<epsilon>) \<star> f) \<cdot> (\<a>[u, f, g] \<star> f) \<cdot>
                          \<a>\<^sup>-\<^sup>1[u \<star> f, g, f] \<cdot> (((u \<star> f) \<star> \<eta>) \<cdot> (\<nu> \<star> src v)) \<cdot> \<r>\<^sup>-\<^sup>1[v]"
        proof -
          have "(\<nu> \<star> g \<star> f) \<cdot> (v \<star> \<eta>) = ((u \<star> f) \<star> \<eta>) \<cdot> (\<nu> \<star> src v)"
            using assms \<nu> antipar interchange [of "u \<star> f" \<nu> \<eta> "src v"]
                  interchange [of \<nu> v "g \<star> f" \<eta>] comp_arr_dom comp_cod_arr
            by auto
          thus ?thesis by simp
        qed
        also have "... = ((\<r>[u] \<star> f) \<cdot> ((u \<star> \<epsilon>) \<star> f) \<cdot>
                           ((\<a>[u, f, g] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[u \<star> f, g, f]) \<cdot>
                             ((u \<star> f) \<star> \<eta>)) \<cdot> (\<nu> \<star> src v) \<cdot> \<r>\<^sup>-\<^sup>1[v]"
          using comp_assoc by simp
        also have "... = ((\<r>[u] \<star> f) \<cdot> ((u \<star> \<epsilon>) \<star> f) \<cdot>
                           (\<a>\<^sup>-\<^sup>1[u, f \<star> g, f] \<cdot> (u \<star> \<a>\<^sup>-\<^sup>1[f, g, f]) \<cdot> \<a>[u, f, g \<star> f]) \<cdot>
                             ((u \<star> f) \<star> \<eta>)) \<cdot> (\<nu> \<star> src v) \<cdot> \<r>\<^sup>-\<^sup>1[v]"
          using assms antipar canI_associator_hcomp canI_associator_0 whisker_can_left_0
                whisker_can_right_0
          by simp
        also have "... = ((\<r>[u] \<star> f) \<cdot> (((u \<star> \<epsilon>) \<star> f) \<cdot>
                           \<a>\<^sup>-\<^sup>1[u, f \<star> g, f]) \<cdot> (u \<star> \<a>\<^sup>-\<^sup>1[f, g, f]) \<cdot> (\<a>[u, f, g \<star> f]) \<cdot>
                             ((u \<star> f) \<star> \<eta>)) \<cdot> (\<nu> \<star> src v) \<cdot> \<r>\<^sup>-\<^sup>1[v]"
          using comp_assoc by simp
        also have "... = ((\<r>[u] \<star> f) \<cdot> (\<a>\<^sup>-\<^sup>1[u, src u, f] \<cdot> (u \<star> \<epsilon> \<star> f)) \<cdot>
                           (u \<star> \<a>\<^sup>-\<^sup>1[f, g, f]) \<cdot> ((u \<star> f \<star> \<eta>) \<cdot> \<a>[u, f, src f])) \<cdot>
                             (\<nu> \<star> src v) \<cdot> \<r>\<^sup>-\<^sup>1[v]"
          using assms antipar assoc'_naturality [of u \<epsilon> f] assoc_naturality [of u f \<eta>]
          by auto
        also have "... = (\<r>[u] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[u, src u, f] \<cdot>
                           ((u \<star> \<epsilon> \<star> f) \<cdot> (u \<star> \<a>\<^sup>-\<^sup>1[f, g, f]) \<cdot> (u \<star> f \<star> \<eta>)) \<cdot> \<a>[u, f, src f] \<cdot>
                             (\<nu> \<star> src v) \<cdot> \<r>\<^sup>-\<^sup>1[v]"
          using comp_assoc by simp
        also have "... = (\<r>[u] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[u, src u, f] \<cdot>
                           (u \<star> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) \<cdot> \<a>[u, f, src f] \<cdot>
                             (\<nu> \<star> src v) \<cdot> \<r>\<^sup>-\<^sup>1[v]"
          using assms antipar whisker_left by auto
        also have "... = ((\<r>[u] \<star> f) \<cdot> (\<a>\<^sup>-\<^sup>1[u, src u, f] \<cdot> (u \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]) \<cdot> \<a>[u, f, src f])) \<cdot>
                           (\<nu> \<star> src v) \<cdot> \<r>\<^sup>-\<^sup>1[v]"
          using assms antipar triangle_left comp_assoc by simp
        also have "... = \<r>[u \<star> f] \<cdot> (\<nu> \<star> src v) \<cdot> \<r>\<^sup>-\<^sup>1[v]"
        proof -
          have "(\<r>[u] \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[u, src u, f] \<cdot> (u \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]) \<cdot> \<a>[u, f, src f] =
                ((u \<star> \<l>[f]) \<cdot> (\<a>[u, src u, f] \<cdot> \<a>\<^sup>-\<^sup>1[u, src u, f])) \<cdot>
                  (u \<star> \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]) \<cdot> \<a>[u, f, src f]"
            using assms ide_left ide_right antipar triangle comp_assoc by metis
          also have "... = (u \<star> \<r>[f]) \<cdot> \<a>[u, f, src f]"
            using assms antipar canI_associator_1 canI_unitor_0 whisker_can_left_0
                  whisker_can_right_0 canI_associator_1
            by simp
          also have "... = \<r>[u \<star> f]"
            using assms antipar runit_hcomp by simp
          finally show ?thesis by simp
        qed
        also have "... = (\<r>[u \<star> f] \<cdot> \<r>\<^sup>-\<^sup>1[u \<star> f]) \<cdot> \<nu>"
          using assms \<nu> runit'_naturality [of \<nu>] comp_assoc by auto
        also have "... = \<nu>"
          using assms \<nu> comp_cod_arr comp_arr_inv inv_is_inverse iso_runit by auto
        finally show "trnr\<^sub>\<eta> v (trnr\<^sub>\<epsilon> u \<nu>) = \<nu>" by auto
      qed
      show "bij_betw (trnr\<^sub>\<eta> v) (hom (v \<star> g) u) (hom v (u \<star> f))"
        using A B C D by (intro bij_betwI, auto)
      show "bij_betw (trnr\<^sub>\<epsilon> u) (hom v (u \<star> f)) (hom (v \<star> g) u)"
        using A B C D by (intro bij_betwI, auto)
    qed

    lemma trnr\<^sub>\<eta>_comp:
    assumes "ide v" and "seq \<mu> \<nu>" and "src \<mu> = trg f"
    shows "trnr\<^sub>\<eta> v (\<mu> \<cdot> \<nu>) = (\<mu> \<star> f) \<cdot> trnr\<^sub>\<eta> v \<nu>"
      using assms trnr\<^sub>\<eta>_def whisker_right comp_assoc by auto

  end

  text \<open>
    It is useful to have at hand the simpler versions of the preceding results that
    hold in a normal bicategory and in a strict bicategory.
  \<close>

  locale adjunction_in_normal_bicategory =
    normal_bicategory +
    adjunction_in_bicategory
  begin

    lemma triangle_left:
    shows "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = f"
      using triangle_left strict_lunit strict_runit by simp

    lemma triangle_right:
    shows "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = g"
      using triangle_right strict_lunit strict_runit by simp

    lemma trnr\<^sub>\<eta>_eq:
    assumes "ide u" and "ide v"
    and "src v = trg g" and "src u = trg f"
    and "\<mu> \<in> hom (v \<star> g) u"
    shows "trnr\<^sub>\<eta> v \<mu> = (\<mu> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[v, g, f] \<cdot> (v \<star> \<eta>)"
      unfolding trnr\<^sub>\<eta>_def
      using assms antipar strict_runit' comp_arr_ide [of "\<r>\<^sup>-\<^sup>1[v]" "v \<star> \<eta>"] hcomp_arr_obj
      by auto

    lemma trnr\<^sub>\<epsilon>_eq:
    assumes "ide u" and "ide v"
    and "src v = trg g" and "src u = trg f"
    and "\<nu> \<in> hom v (u \<star> f)"
    shows "trnr\<^sub>\<epsilon> u \<nu> = (u \<star> \<epsilon>) \<cdot> \<a>[u, f, g] \<cdot> (\<nu> \<star> g)"
      unfolding trnr\<^sub>\<epsilon>_def
      using assms antipar strict_runit comp_ide_arr hcomp_arr_obj by auto

    lemma trnl\<^sub>\<eta>_eq:
    assumes "ide u" and "ide v"
    and "src f = trg v" and "src g = trg u"
    and "\<mu> \<in> hom (f \<star> v) u"
    shows "trnl\<^sub>\<eta> v \<mu> = (g \<star> \<mu>) \<cdot> \<a>[g, f, v] \<cdot> (\<eta> \<star> v)"
      using assms trnl\<^sub>\<eta>_def antipar strict_lunit comp_arr_dom hcomp_obj_arr by auto

    lemma trnl\<^sub>\<epsilon>_eq:
    assumes "ide u" and "ide v"
    and "src f = trg v" and "src g = trg u"
    and "\<nu> \<in> hom v (g \<star> u)"
    shows "trnl\<^sub>\<epsilon> u \<nu> = (\<epsilon> \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, u] \<cdot> (f \<star> \<nu>)"
      using assms trnl\<^sub>\<epsilon>_def antipar strict_lunit comp_cod_arr hcomp_obj_arr by auto

  end

  locale adjunction_in_strict_bicategory =
    strict_bicategory +
    adjunction_in_normal_bicategory
  begin

    lemma triangle_left:
    shows "(\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>) = f"
      using ide_left ide_right antipar triangle_left strict_assoc' comp_cod_arr
      by (metis dom_eqI ideD(1) seqE)

    lemma triangle_right:
    shows "(g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g) = g"
      using ide_left ide_right antipar triangle_right strict_assoc comp_cod_arr
      by (metis ideD(1) ideD(2) seqE)

    lemma trnr\<^sub>\<eta>_eq:
    assumes "ide u" and "ide v"
    and "src v = trg g" and "src u = trg f"
    and "\<mu> \<in> hom (v \<star> g) u"
    shows "trnr\<^sub>\<eta> v \<mu> = (\<mu> \<star> f) \<cdot> (v \<star> \<eta>)"
    proof -
      have "trnr\<^sub>\<eta> v \<mu> = (\<mu> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[v, g, f] \<cdot> (v \<star> \<eta>)"
        using assms trnr\<^sub>\<eta>_eq [of u v \<mu>] by simp
      also have "... = (\<mu> \<star> f) \<cdot> (v \<star> \<eta>)"
      proof -
        have "\<a>\<^sup>-\<^sup>1[v, g, f] \<cdot> (v \<star> \<eta>) = (v \<star> \<eta>)"
        proof -
          have "ide \<a>\<^sup>-\<^sup>1[v, g, f]"
            using assms antipar strict_assoc' by simp
          moreover have "seq \<a>\<^sup>-\<^sup>1[v, g, f] (v \<star> \<eta>)"
            using assms antipar by simp
          ultimately show ?thesis
            using comp_ide_arr by simp
        qed
        thus ?thesis by simp
      qed
      finally show ?thesis by simp
    qed

    lemma trnr\<^sub>\<epsilon>_eq:
    assumes "ide u" and "ide v"
    and "src v = trg g" and "src u = trg f"
    and "\<nu> \<in> hom v (u \<star> f)"
    shows "trnr\<^sub>\<epsilon> u \<nu> = (u \<star> \<epsilon>) \<cdot> (\<nu> \<star> g)"
    proof -
      have "trnr\<^sub>\<epsilon> u \<nu> = (u \<star> \<epsilon>) \<cdot> \<a>[u, f, g] \<cdot> (\<nu> \<star> g)"
        using assms trnr\<^sub>\<epsilon>_eq [of u v \<nu>] by simp
      also have "... = (u \<star> \<epsilon>) \<cdot> (\<nu> \<star> g)"
      proof -
        have "\<a>[u, f, g] \<cdot> (\<nu> \<star> g) = (\<nu> \<star> g)"
        proof -
          have "ide \<a>[u, f, g]"
            using assms antipar strict_assoc by simp
          moreover have "seq \<a>[u, f, g] (\<nu> \<star> g)"
            using assms antipar by force
          ultimately show ?thesis
            using comp_ide_arr by simp
        qed
        thus ?thesis by simp
      qed
      finally show ?thesis by simp
    qed

    lemma trnl\<^sub>\<eta>_eq:
    assumes "ide u" and "ide v"
    and "src f = trg v" and "src g = trg u"
    and "\<mu> \<in> hom (f \<star> v) u"
    shows "trnl\<^sub>\<eta> v \<mu> = (g \<star> \<mu>) \<cdot> (\<eta> \<star> v)"
    proof -
      have "trnl\<^sub>\<eta> v \<mu> = (g \<star> \<mu>) \<cdot> \<a>[g, f, v] \<cdot> (\<eta> \<star> v)"
        using assms trnl\<^sub>\<eta>_eq [of u v \<mu>] by simp
      also have "... = (g \<star> \<mu>) \<cdot> (\<eta> \<star> v)"
      proof -
        have "seq \<a>[g, f, v] (\<eta> \<star> v)"
          using assms antipar unit_in_hom by simp
        thus ?thesis
          using assms antipar trnl\<^sub>\<eta>_eq strict_assoc comp_ide_arr [of "\<a>[g, f, v]" "\<eta> \<star> v"]
          by simp
      qed
      finally show ?thesis by blast
    qed

    lemma trnl\<^sub>\<epsilon>_eq:
    assumes "ide u" and "ide v"
    and "src f = trg v" and "src g = trg u"
    and "\<nu> \<in> hom v (g \<star> u)"
    shows "trnl\<^sub>\<epsilon> u \<nu> = (\<epsilon> \<star> u) \<cdot> (f \<star> \<nu>)"
    proof -
      have "trnl\<^sub>\<epsilon> u \<nu> = (\<epsilon> \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, u] \<cdot> (f \<star> \<nu>)"
        using assms trnl\<^sub>\<epsilon>_eq [of u v \<nu>] by simp
      also have "... = ((\<epsilon> \<star> u) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, u]) \<cdot> (f \<star> \<nu>)"
        using comp_assoc by simp
      also have "... = (\<epsilon> \<star> u) \<cdot> (f \<star> \<nu>)"
      proof -
        have "seq (\<epsilon> \<star> u) \<a>\<^sup>-\<^sup>1[f, g, u]"
          using assms antipar unit_in_hom by simp
        thus ?thesis
          using assms antipar trnl\<^sub>\<epsilon>_eq strict_assoc' comp_arr_ide ide_left ide_right
          by metis
      qed
      finally show ?thesis by simp
    qed

  end

  subsection "Preservation Properties for Adjunctions"

  text \<open>
    Here we show that adjunctions are preserved under isomorphisms of the
    left and right adjoints.
  \<close>

  context bicategory
  begin

    interpretation E: self_evaluation_map V H \<a> \<i> src trg ..
    notation E.eval ("\<lbrace>_\<rbrace>")

    definition adjoint_pair
    where "adjoint_pair f g \<equiv> \<exists>\<eta> \<epsilon>. adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"

    (* These would normally be called "maps", but that name is too heavily used already. *)
    abbreviation is_left_adjoint
    where "is_left_adjoint f \<equiv> \<exists>g. adjoint_pair f g"

    abbreviation is_right_adjoint
    where "is_right_adjoint g \<equiv> \<exists>f. adjoint_pair f g"

    lemma adjoint_pair_antipar:
    assumes "adjoint_pair f g"
    shows "ide f" and "ide g" and "src f = trg g" and "src g = trg f"
    proof -
      obtain \<eta> \<epsilon> where A: "adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using assms adjoint_pair_def by auto
      interpret A: adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using A by auto
      show "ide f" by simp
      show "ide g" by simp
      show "src f = trg g" using A.antipar by simp
      show "src g = trg f" using A.antipar by simp
    qed

    lemma left_adjoint_is_ide:
    assumes "is_left_adjoint f"
    shows "ide f"
      using assms adjoint_pair_antipar by auto

    lemma right_adjoint_is_ide:
    assumes "is_right_adjoint f"
    shows "ide f"
      using assms adjoint_pair_antipar by auto

    lemma adjunction_preserved_by_iso_right:
    assumes "adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
    and "\<guillemotleft>\<phi> : g \<Rightarrow> g'\<guillemotright>" and "iso \<phi>"
    shows "adjunction_in_bicategory V H \<a> \<i> src trg f g' ((\<phi> \<star> f) \<cdot> \<eta>) (\<epsilon> \<cdot> (f \<star> inv \<phi>))"
    proof
      interpret A: adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using assms by auto
      show "ide f" by simp
      show "ide g'"
        using assms(2) isomorphic_def by auto
      show "\<guillemotleft>(\<phi> \<star> f) \<cdot> \<eta> : src f \<Rightarrow> g' \<star> f\<guillemotright>"
        using assms A.antipar by fastforce
      show "\<guillemotleft>\<epsilon> \<cdot> (f \<star> inv \<phi>) : f \<star> g' \<Rightarrow> src g'\<guillemotright>"
      proof
        show "\<guillemotleft>f \<star> inv \<phi> : f \<star> g' \<Rightarrow> f \<star> g\<guillemotright>"
          using assms A.antipar by (intro hcomp_in_vhom, auto)
        show "\<guillemotleft>\<epsilon> : f \<star> g \<Rightarrow> src g'\<guillemotright>"
          using assms A.counit_in_hom A.antipar by auto
      qed
      show "(\<epsilon> \<cdot> (f \<star> inv \<phi>) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g', f] \<cdot> (f \<star> (\<phi> \<star> f) \<cdot> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
      proof -
        have "(\<epsilon> \<cdot> (f \<star> inv \<phi>) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g', f] \<cdot> (f \<star> (\<phi> \<star> f) \<cdot> \<eta>) =
              (\<epsilon> \<star> f) \<cdot> (((f \<star> inv \<phi>) \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g', f]) \<cdot> (f \<star> \<phi> \<star> f) \<cdot> (f \<star> \<eta>)"
          using assms A.antipar whisker_right whisker_left comp_assoc by auto
        also have "... = (\<epsilon> \<star> f) \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> inv \<phi> \<star> f)) \<cdot> (f \<star> \<phi> \<star> f) \<cdot> (f \<star> \<eta>)"
          using assms A.antipar assoc'_naturality [of f "inv \<phi>" f] by auto
        also have "... = (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> ((f \<star> inv \<phi> \<star> f) \<cdot> (f \<star> \<phi> \<star> f)) \<cdot> (f \<star> \<eta>)"
          using comp_assoc by simp
        also have "... = (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> g \<star> f) \<cdot> (f \<star> \<eta>)"
          using assms A.antipar comp_inv_arr inv_is_inverse whisker_left
                whisker_right [of f "inv \<phi>" \<phi>]
          by auto
        also have "... = (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)"
          using assms A.antipar comp_cod_arr by simp
        also have "... = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
          using A.triangle_left by simp
        finally show ?thesis by simp
      qed
      show "(g' \<star> \<epsilon> \<cdot> (f \<star> inv \<phi>)) \<cdot> \<a>[g', f, g'] \<cdot> ((\<phi> \<star> f) \<cdot> \<eta> \<star> g') = \<r>\<^sup>-\<^sup>1[g'] \<cdot> \<l>[g']"
      proof -
        have "(g' \<star> \<epsilon> \<cdot> (f \<star> inv \<phi>)) \<cdot> \<a>[g', f, g'] \<cdot> ((\<phi> \<star> f) \<cdot> \<eta> \<star> g') =
              (g' \<star> \<epsilon>) \<cdot> ((g' \<star> f \<star> inv \<phi>) \<cdot> \<a>[g', f, g']) \<cdot> ((\<phi> \<star> f) \<star> g') \<cdot> (\<eta> \<star> g')"
            using assms A.antipar whisker_left whisker_right comp_assoc by auto
        also have "... = (g' \<star> \<epsilon>) \<cdot> (\<a>[g', f, g] \<cdot> ((g' \<star> f) \<star> inv \<phi>)) \<cdot> ((\<phi> \<star> f) \<star> g') \<cdot> (\<eta> \<star> g')"
          using assms A.antipar assoc_naturality [of g' f "inv \<phi>"] by auto
        also have "... = (g' \<star> \<epsilon>) \<cdot> \<a>[g', f, g] \<cdot> (((g' \<star> f) \<star> inv \<phi>) \<cdot> ((\<phi> \<star> f) \<star> g')) \<cdot> (\<eta> \<star> g')"
          using comp_assoc by simp
        also have "... = (g' \<star> \<epsilon>) \<cdot> (\<a>[g', f, g] \<cdot> ((\<phi> \<star> f) \<star> g)) \<cdot> ((g \<star> f) \<star> inv \<phi>) \<cdot> (\<eta> \<star> g')"
        proof -
          have "((g' \<star> f) \<star> inv \<phi>) \<cdot> ((\<phi> \<star> f) \<star> g') = (\<phi> \<star> f) \<star> inv \<phi>"
            using assms A.antipar comp_arr_dom comp_cod_arr
                  interchange [of "g' \<star> f" "\<phi> \<star> f" "inv \<phi>" g']
            by auto
          also have "... = ((\<phi> \<star> f) \<star> g) \<cdot> ((g \<star> f) \<star> inv \<phi>)"
            using assms A.antipar comp_arr_dom comp_cod_arr
                  interchange [of "\<phi> \<star> f" "g \<star> f" g "inv \<phi>"]
            by auto
          finally show ?thesis
            using comp_assoc by simp
        qed
        also have "... = ((g' \<star> \<epsilon>) \<cdot> (\<phi> \<star> f \<star> g)) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> (trg g \<star> inv \<phi>)"
        proof -
          have "\<a>[g', f, g] \<cdot> ((\<phi> \<star> f) \<star> g) = (\<phi> \<star> f \<star> g) \<cdot> \<a>[g, f, g]"
            using assms A.antipar assoc_naturality [of \<phi> f g] by auto
          moreover have "((g \<star> f) \<star> inv \<phi>) \<cdot> (\<eta> \<star> g') = (\<eta> \<star> g) \<cdot> (trg g \<star> inv \<phi>)"
            using assms A.antipar comp_arr_dom comp_cod_arr
                  interchange [of "g \<star> f" \<eta> "inv \<phi>" g'] interchange [of \<eta> "trg g" g "inv \<phi>"]
            by auto
          ultimately show ?thesis
            using comp_assoc by simp
        qed
        also have "... = ((\<phi> \<star> src g) \<cdot> (g \<star> \<epsilon>)) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> (trg g \<star> inv \<phi>)"
          using assms A.antipar comp_arr_dom comp_cod_arr
                interchange [of g' \<phi> \<epsilon> "f \<star> g"] interchange [of \<phi> g "src g" \<epsilon>]
            by auto
        also have "... = (\<phi> \<star> src g) \<cdot> ((g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)) \<cdot> (trg g \<star> inv \<phi>)"
          using comp_assoc by simp
        also have "... = ((\<phi> \<star> src g) \<cdot> \<r>\<^sup>-\<^sup>1[g]) \<cdot> \<l>[g] \<cdot> (trg g \<star> inv \<phi>)"
          using assms A.antipar A.triangle_right comp_cod_arr comp_assoc
          by simp
        also have "... = (\<r>\<^sup>-\<^sup>1[g'] \<cdot> \<phi>) \<cdot> inv \<phi> \<cdot> \<l>[g']"
          using assms A.antipar runit'_naturality [of \<phi>] lunit_naturality [of "inv \<phi>"]
          by auto
        also have "... = \<r>\<^sup>-\<^sup>1[g'] \<cdot> (\<phi> \<cdot> inv \<phi>) \<cdot> \<l>[g']"
          using comp_assoc by simp
        also have "... = \<r>\<^sup>-\<^sup>1[g'] \<cdot> \<l>[g']"
          using assms comp_cod_arr comp_arr_inv' by auto
        finally show ?thesis by simp
      qed
    qed

    lemma adjunction_preserved_by_iso_left:
    assumes "adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
    and "\<guillemotleft>\<phi> : f \<Rightarrow> f'\<guillemotright>" and "iso \<phi>"
    shows "adjunction_in_bicategory V H \<a> \<i> src trg f' g ((g \<star> \<phi>) \<cdot> \<eta>) (\<epsilon> \<cdot> (inv \<phi> \<star> g))"
    proof
      interpret A: adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using assms by auto
      show "ide g" by simp
      show "ide f'"
        using assms(2) isomorphic_def by auto
      show "\<guillemotleft>(g \<star> \<phi>) \<cdot> \<eta> : src f' \<Rightarrow> g \<star> f'\<guillemotright>"
      proof
        show "\<guillemotleft>\<eta> : src f' \<Rightarrow> g \<star> f\<guillemotright>"
          using assms A.unit_in_hom by auto
        show "\<guillemotleft>g \<star> \<phi> : g \<star> f \<Rightarrow> g \<star> f'\<guillemotright>"
          using assms A.antipar by fastforce
      qed
      show "\<guillemotleft>\<epsilon> \<cdot> (inv \<phi> \<star> g) : f' \<star> g \<Rightarrow> src g\<guillemotright>"
      proof
        show "\<guillemotleft>inv \<phi> \<star> g : f' \<star> g \<Rightarrow> f \<star> g\<guillemotright>"
          using assms A.antipar by (intro hcomp_in_vhom, auto)
        show "\<guillemotleft>\<epsilon> : f \<star> g \<Rightarrow> src g\<guillemotright>"
          using assms A.antipar by auto
      qed
      show "(g \<star> \<epsilon> \<cdot> (inv \<phi> \<star> g)) \<cdot> \<a>[g, f', g] \<cdot> ((g \<star> \<phi>) \<cdot> \<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
      proof -
        have "(g \<star> \<epsilon> \<cdot> (inv \<phi> \<star> g)) \<cdot> \<a>[g, f', g] \<cdot> ((g \<star> \<phi>) \<cdot> \<eta> \<star> g) =
              (g \<star> \<epsilon>) \<cdot> ((g \<star> inv \<phi> \<star> g) \<cdot> \<a>[g, f', g]) \<cdot> ((g \<star> \<phi>) \<star> g) \<cdot> (\<eta> \<star> g)"
          using assms A.antipar whisker_left whisker_right comp_assoc by auto
        also have "... = (g \<star> \<epsilon>) \<cdot> (\<a>[g, f, g] \<cdot> ((g \<star> inv \<phi>) \<star> g)) \<cdot> ((g \<star> \<phi>) \<star> g) \<cdot> (\<eta> \<star> g)"
          using assms A.antipar assoc_naturality [of g "inv \<phi>" g] by auto
        also have "... = (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (((g \<star> inv \<phi>) \<star> g) \<cdot> ((g \<star> \<phi>) \<star> g)) \<cdot> (\<eta> \<star> g)"
          using comp_assoc by simp
        also have "... = (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> ((g \<star> f) \<star> g) \<cdot> (\<eta> \<star> g)"
          using assms A.antipar comp_inv_arr inv_is_inverse whisker_right
                whisker_left [of g "inv \<phi>" \<phi>]
          by auto
        also have "... = (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)"
          using assms A.antipar comp_cod_arr by simp
        also have "... = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
          using A.triangle_right by simp
        finally show ?thesis by simp
      qed
      show "(\<epsilon> \<cdot> (inv \<phi> \<star> g) \<star> f') \<cdot> \<a>\<^sup>-\<^sup>1[f', g, f'] \<cdot> (f' \<star> (g \<star> \<phi>) \<cdot> \<eta>) = \<l>\<^sup>-\<^sup>1[f'] \<cdot> \<r>[f']"
      proof -
        have "(\<epsilon> \<cdot> (inv \<phi> \<star> g) \<star> f') \<cdot> \<a>\<^sup>-\<^sup>1[f', g, f'] \<cdot> (f' \<star> (g \<star> \<phi>) \<cdot> \<eta>) =
              (\<epsilon> \<star> f') \<cdot> (((inv \<phi> \<star> g) \<star> f') \<cdot> \<a>\<^sup>-\<^sup>1[f', g, f']) \<cdot> (f' \<star> g \<star> \<phi>) \<cdot> (f' \<star> \<eta>)"
          using assms A.antipar whisker_right whisker_left comp_assoc
          by auto
        also have "... = (\<epsilon> \<star> f') \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, f'] \<cdot> (inv \<phi> \<star> g \<star> f')) \<cdot> (f' \<star> g \<star> \<phi>) \<cdot> (f' \<star> \<eta>)"
          using assms A.antipar assoc'_naturality [of "inv \<phi>" g f'] by auto
        also have "... = (\<epsilon> \<star> f') \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f'] \<cdot> ((inv \<phi> \<star> g \<star> f') \<cdot> (f' \<star> g \<star> \<phi>)) \<cdot> (f' \<star> \<eta>)"
          using comp_assoc by simp
        also have "... = (\<epsilon> \<star> f') \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, f'] \<cdot> (f \<star> g \<star> \<phi>)) \<cdot> (inv \<phi> \<star> g \<star> f) \<cdot> (f' \<star> \<eta>)"
        proof -
          have "(inv \<phi> \<star> g \<star> f') \<cdot> (f' \<star> g \<star> \<phi>) = (f \<star> g \<star> \<phi>) \<cdot> (inv \<phi> \<star> g \<star> f)"
            using assms(2-3) A.antipar comp_arr_dom comp_cod_arr
                  interchange [of "inv \<phi>" f' "g \<star> f'" "g \<star> \<phi>"]
                  interchange [of f "inv \<phi>" "g \<star> \<phi>" "g \<star> f"]
            by auto
          thus ?thesis
            using comp_assoc by simp
        qed
        also have "... = ((\<epsilon> \<star> f') \<cdot> ((f \<star> g) \<star> \<phi>)) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> (inv \<phi> \<star> src f)"
        proof -
          have "\<a>\<^sup>-\<^sup>1[f, g, f'] \<cdot> (f \<star> g \<star> \<phi>) = ((f \<star> g) \<star> \<phi>) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f]"
            using assms A.antipar assoc'_naturality [of f g \<phi>] by auto
          moreover have "(inv \<phi> \<star> g \<star> f) \<cdot> (f' \<star> \<eta>) = (f \<star> \<eta>) \<cdot> (inv \<phi> \<star> src f)"
            using assms A.antipar comp_arr_dom comp_cod_arr
                  interchange [of "inv \<phi>" f' "g \<star> f" \<eta>] interchange [of f "inv \<phi>" \<eta> "src f"]
            by auto
          ultimately show ?thesis
            using comp_assoc by simp
        qed
        also have "... = ((trg f \<star> \<phi>) \<cdot> (\<epsilon> \<star> f)) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> (inv \<phi> \<star> src f)"
          using assms A.antipar comp_arr_dom comp_cod_arr
                interchange [of \<epsilon> "f \<star> g" f' \<phi>] interchange [of "trg f" \<epsilon> \<phi> f]
          by (metis A.counit_simps(1) A.counit_simps(2) A.counit_simps(3) in_homE)
        also have "... = (trg f \<star> \<phi>) \<cdot> ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) \<cdot> (inv \<phi> \<star> src f)"
          using comp_assoc by simp
        also have "... = ((trg f \<star> \<phi>) \<cdot> \<l>\<^sup>-\<^sup>1[f]) \<cdot> \<r>[f] \<cdot> (inv \<phi> \<star> src f)"
          using assms A.antipar A.triangle_left comp_cod_arr comp_assoc
          by simp
        also have "... = (\<l>\<^sup>-\<^sup>1[f'] \<cdot> \<phi>) \<cdot> inv \<phi> \<cdot> \<r>[f']"
          using assms A.antipar lunit'_naturality runit_naturality [of "inv \<phi>"] by auto
        also have "... = \<l>\<^sup>-\<^sup>1[f'] \<cdot> (\<phi> \<cdot> inv \<phi>) \<cdot> \<r>[f']"
          using comp_assoc by simp
        also have "... =  \<l>\<^sup>-\<^sup>1[f'] \<cdot> \<r>[f']"
          using assms comp_cod_arr comp_arr_inv inv_is_inverse by auto
        finally show ?thesis by simp
      qed
    qed

    lemma adjoint_pair_preserved_by_iso:
    assumes "adjoint_pair f g"
    and "\<guillemotleft>\<phi> : f \<Rightarrow> f'\<guillemotright>" and "iso \<phi>"
    and "\<guillemotleft>\<psi> : g \<Rightarrow> g'\<guillemotright>" and "iso \<psi>"
    shows "adjoint_pair f' g'"
    proof -
      obtain \<eta> \<epsilon> where A: "adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using assms adjoint_pair_def by auto
      have "adjunction_in_bicategory V H \<a> \<i> src trg f g' ((\<psi> \<star> f) \<cdot> \<eta>) (\<epsilon> \<cdot> (f \<star> inv \<psi>))"
        using assms A adjunction_preserved_by_iso_right by blast
      hence "adjunction_in_bicategory V H \<a> \<i> src trg f' g'
               ((g' \<star> \<phi>) \<cdot> (\<psi> \<star> f) \<cdot> \<eta>) ((\<epsilon> \<cdot> (f \<star> inv \<psi>)) \<cdot> (inv \<phi> \<star> g'))"
        using assms adjunction_preserved_by_iso_left by blast
      thus ?thesis using adjoint_pair_def by auto
    qed

    lemma left_adjoint_preserved_by_iso:
    assumes "is_left_adjoint f"
    and "\<guillemotleft>\<phi> : f \<Rightarrow> f'\<guillemotright>" and "iso \<phi>"
    shows "is_left_adjoint f'"
    proof -
      obtain g where g: "adjoint_pair f g"
        using assms by auto
      have "adjoint_pair f' g"
        using assms g adjoint_pair_preserved_by_iso [of f g \<phi> f' g g]
              adjoint_pair_antipar [of f g]
        by auto
      thus ?thesis by auto
    qed

    lemma right_adjoint_preserved_by_iso:
    assumes "is_right_adjoint g"
    and "\<guillemotleft>\<phi> : g \<Rightarrow> g'\<guillemotright>" and "iso \<phi>"
    shows "is_right_adjoint g'"
    proof -
      obtain f where f: "adjoint_pair f g"
        using assms by auto
      have "adjoint_pair f g'"
        using assms f adjoint_pair_preserved_by_iso [of f g f f \<phi> g']
              adjoint_pair_antipar [of f g]
        by auto
      thus ?thesis by auto
    qed

    lemma left_adjoint_preserved_by_iso':
    assumes "is_left_adjoint f" and "f \<cong> f'"
    shows "is_left_adjoint f'"
      using assms isomorphic_def left_adjoint_preserved_by_iso by blast

    lemma right_adjoint_preserved_by_iso':
    assumes "is_right_adjoint g" and "g \<cong> g'"
    shows "is_right_adjoint g'"
      using assms isomorphic_def right_adjoint_preserved_by_iso by blast

    lemma obj_self_adjunction:
    assumes "obj a"
    shows "adjunction_in_bicategory V H \<a> \<i> src trg a a \<l>\<^sup>-\<^sup>1[a] \<r>[a]"
    proof
      show 1: "ide a"
        using assms by auto
      show "\<guillemotleft>\<l>\<^sup>-\<^sup>1[a] : src a \<Rightarrow> a \<star> a\<guillemotright>"
        using assms 1 by auto
      show "\<guillemotleft>\<r>[a] : a \<star> a \<Rightarrow> src a\<guillemotright>"
        using assms 1 by fastforce
      show "(\<r>[a] \<star> a) \<cdot> \<a>\<^sup>-\<^sup>1[a, a, a] \<cdot> (a \<star> \<l>\<^sup>-\<^sup>1[a]) = \<l>\<^sup>-\<^sup>1[a] \<cdot> \<r>[a]"
        using assms 1 canI_unitor_1 canI_associator_1(2) canI_associator_3
              whisker_can_right_1 whisker_can_left_1 can_Ide_self obj_simps
        by simp
      show "(a \<star> \<r>[a]) \<cdot> \<a>[a, a, a] \<cdot> (\<l>\<^sup>-\<^sup>1[a] \<star> a) = \<r>\<^sup>-\<^sup>1[a] \<cdot> \<l>[a]"
        using assms 1 canI_unitor_1 canI_associator_1(2) canI_associator_3
              whisker_can_right_1 whisker_can_left_1 can_Ide_self
        by simp
    qed

    lemma obj_is_self_adjoint:
    assumes "obj a"
    shows "adjoint_pair a a" and "is_left_adjoint a" and "is_right_adjoint a"
      using assms obj_self_adjunction adjoint_pair_def by auto

  end

  subsection "Pseudofunctors and Adjunctions"

  context pseudofunctor
  begin

    lemma preserves_adjunction:
    assumes "adjunction_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>"
    shows "adjunction_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F f) (F g)
             (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))
             (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
    proof -
      interpret adjunction_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>
        using assms by auto
      interpret A: adjunction_data_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                     \<open>F f\<close> \<open>F g\<close> \<open>D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)\<close>
                     \<open>D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)\<close>
        using adjunction_data_in_bicategory_axioms preserves_adjunction_data by auto
      show "adjunction_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F f) (F g)
              (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))
              (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
      proof
        show "(D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F f] \<cdot>\<^sub>D
                (F f \<star>\<^sub>D D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)) =
              D.lunit' (F f) \<cdot>\<^sub>D \<r>\<^sub>D[F f]"
        proof -
          have 1: "D.iso (\<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, f)))"
            using antipar C.VV.ide_char C.VV.arr_char D.iso_is_arr FF_def
            by (intro D.isos_compose D.seqI, simp_all)
          have "(D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F f] \<cdot>\<^sub>D
                    (F f \<star>\<^sub>D D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)) =
                 (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                   (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, f)) \<cdot>\<^sub>D
                   F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>D
                   \<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, f)) \<cdot>\<^sub>D
                   (F f \<star>\<^sub>D D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))"
          proof -
            have "\<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F f] =
                  (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, f)) \<cdot>\<^sub>D F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>D
                    \<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, f))"
            proof -
              have "\<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F f] \<cdot>\<^sub>D D.inv (\<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, f))) =
                    D.inv (F \<a>\<^sub>C[f, g, f] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, f) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F f))"
              proof -
                have "D.inv (\<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F f]) =
                      D.inv (F \<a>\<^sub>C[f, g, f] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, f) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F f))"
                  using antipar assoc_coherence by simp
                moreover
                have "D.inv (\<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F f]) =
                      \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F f] \<cdot>\<^sub>D D.inv (\<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, f)))"
                proof -
                  have "D.seq (\<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, f))) \<a>\<^sub>D[F f, F g, F f]"
                    using antipar by fastforce
                  thus ?thesis
                    using 1 antipar D.comp_assoc
                          D.inv_comp [of "\<a>\<^sub>D[F f, F g, F f]" "\<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, f))"]
                    by auto
                qed
                ultimately show ?thesis by simp
              qed
              moreover have 2: "D.iso (F \<a>\<^sub>C[f, g, f] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, f) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F f))"
                using antipar D.isos_compose C.VV.ide_char C.VV.arr_char \<Phi>_simps(4)
                by simp
              ultimately have "\<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F f] =
                               D.inv (F \<a>\<^sub>C[f, g, f] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, f) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F f)) \<cdot>\<^sub>D
                                 (\<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, f)))"
                using 1 2 antipar D.invert_side_of_triangle(2) D.inv_inv D.iso_inv_iso D.arr_inv
                by metis
              moreover have "D.inv (F \<a>\<^sub>C[f, g, f] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, f) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F f)) =
                             (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, f)) \<cdot>\<^sub>D F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f]"
              proof -
                have "D.inv (F \<a>\<^sub>C[f, g, f] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, f) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F f)) =
                       D.inv (\<Phi> (f \<star>\<^sub>C g, f) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F f)) \<cdot>\<^sub>D F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f]"
                  using antipar D.isos_compose C.VV.arr_char \<Phi>_simps(4)
                        preserves_inv D.inv_comp
                  by simp
                also have "... = (D.inv (\<Phi> (f, g) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, f))) \<cdot>\<^sub>D
                                 F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f]"
                  using antipar D.inv_comp C.VV.ide_char C.VV.arr_char \<Phi>_simps(4)
                  by simp
                also have "... = ((D.inv (\<Phi> (f, g)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, f))) \<cdot>\<^sub>D
                                 F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f]"
                  using antipar C.VV.ide_char C.VV.arr_char by simp
                also have "... = (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, f)) \<cdot>\<^sub>D
                                 F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f]"
                  using D.comp_assoc by simp
                finally show ?thesis by simp
              qed
              ultimately show ?thesis
                using D.comp_assoc by simp
            qed
            thus ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<star>\<^sub>D F f) \<cdot>\<^sub>D
                             D.inv (\<Phi> (f \<star>\<^sub>C g, f)) \<cdot>\<^sub>D
                             F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>D
                             \<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D
                             (F f \<star>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))"
          proof -
            have "... = ((D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F f)) \<cdot>\<^sub>D
                          (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, f)) \<cdot>\<^sub>D
                          F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>D
                          \<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, f)) \<cdot>\<^sub>D
                          ((F f \<star>\<^sub>D D.inv (\<Phi> (g, f))) \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)))"
            proof -
              have "D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g) \<star>\<^sub>D F f =
                    (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F f)"
                using ide_left ide_right antipar D.whisker_right \<Psi>_char(2)
                by (metis A.counit_simps(1) A.ide_left D.comp_assoc)
              moreover have "F f \<star>\<^sub>D D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f) =
                             (F f \<star>\<^sub>D D.inv (\<Phi> (g, f))) \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))"
                using antipar \<Psi>_char(2) D.whisker_left by simp
              ultimately show ?thesis by simp
            qed
            also have "... = (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<star>\<^sub>D F f) \<cdot>\<^sub>D
                               (((\<Phi> (f, g) \<star>\<^sub>D F f) \<cdot>\<^sub>D (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F f)) \<cdot>\<^sub>D
                               D.inv (\<Phi> (f \<star>\<^sub>C g, f))) \<cdot>\<^sub>D F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>D \<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D
                               (((F f \<star>\<^sub>D \<Phi> (g, f)) \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv (\<Phi> (g, f)))) \<cdot>\<^sub>D
                               (F f \<star>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)))"
              using D.comp_assoc by simp
            also have "... = (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<star>\<^sub>D F f) \<cdot>\<^sub>D
                             D.inv (\<Phi> (f \<star>\<^sub>C g, f)) \<cdot>\<^sub>D
                             F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>D
                             \<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D
                             (F f \<star>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))"
            proof -
              have "((F f \<star>\<^sub>D \<Phi> (g, f)) \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv (\<Phi> (g, f)))) \<cdot>\<^sub>D
                      (F f \<star>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)) =
                    F f \<star>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)"
              proof -
                have "(F f \<star>\<^sub>D \<Phi> (g, f)) \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv (\<Phi> (g, f))) = F f \<star>\<^sub>D F (g \<star>\<^sub>C f)"
                  using antipar \<Psi>_char(2) D.comp_arr_inv D.inv_is_inverse
                        D.whisker_left [of "F f" "\<Phi> (g, f)" "D.inv (\<Phi> (g, f))"]
                  by simp
                moreover have "D.seq (F f \<star>\<^sub>D F (g \<star>\<^sub>C f)) (F f \<star>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))"
                  using antipar by fastforce
                ultimately show ?thesis
                  using D.comp_cod_arr by auto
              qed
              moreover have "((\<Phi> (f, g) \<star>\<^sub>D F f) \<cdot>\<^sub>D (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F f)) \<cdot>\<^sub>D
                               D.inv (\<Phi> (f \<star>\<^sub>C g, f)) =
                             D.inv (\<Phi> (f \<star>\<^sub>C g, f))"
                using antipar D.comp_arr_inv D.inv_is_inverse D.comp_cod_arr
                      D.whisker_right [of "F f" "\<Phi> (f, g)" "D.inv (\<Phi> (f, g))"]
                by simp
              ultimately show ?thesis by simp
            qed
            finally show ?thesis by simp
          qed
          also have "... = (D.inv (\<Psi> (trg\<^sub>C f)) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                             D.inv (\<Phi> (trg\<^sub>C f, f)) \<cdot>\<^sub>D F (\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>D
                             ((\<Phi> (f \<star>\<^sub>C g, f) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, f))) \<cdot>\<^sub>D
                                F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f]) \<cdot>\<^sub>D
                             ((\<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D D.inv (\<Phi> (f, g \<star>\<^sub>C f))) \<cdot>\<^sub>D F (f \<star>\<^sub>C \<eta>)) \<cdot>\<^sub>D
                             \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f))"
          proof -
            have "(D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<star>\<^sub>D F f) \<cdot>\<^sub>D
                    D.inv (\<Phi> (f \<star>\<^sub>C g, f)) \<cdot>\<^sub>D
                    F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>D
                    \<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D
                    (F f \<star>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)) =
                  ((D.inv (\<Psi> (trg\<^sub>C f)) \<star>\<^sub>D F f) \<cdot>\<^sub>D (F \<epsilon> \<star>\<^sub>D F f)) \<cdot>\<^sub>D
                    D.inv (\<Phi> (f \<star>\<^sub>C g, f)) \<cdot>\<^sub>D
                    F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>D
                    \<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D
                    ((F f \<star>\<^sub>D F \<eta>) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f)))"
                using antipar D.comp_assoc D.whisker_left D.whisker_right \<Psi>_char(2)
                by simp
            moreover have "F \<epsilon> \<star>\<^sub>D F f = D.inv (\<Phi> (trg\<^sub>C f, f)) \<cdot>\<^sub>D F (\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, f)"
              using antipar \<Phi>.naturality [of "(\<epsilon>, f)"] C.VV.arr_char FF_def
                    D.invert_side_of_triangle(1)
              by simp
            moreover have "F f \<star>\<^sub>D F \<eta> = D.inv (\<Phi> (f, g \<star>\<^sub>C f)) \<cdot>\<^sub>D F (f \<star>\<^sub>C \<eta>) \<cdot>\<^sub>D \<Phi> (f, src\<^sub>C f)"
              using antipar \<Phi>.naturality [of "(f, \<eta>)"] C.VV.arr_char FF_def
                    D.invert_side_of_triangle(1)
              by simp
            ultimately show ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = ((D.inv (\<Psi> (trg\<^sub>C f)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C f, f))) \<cdot>\<^sub>D
                             (F (\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>D F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>D F (f \<star>\<^sub>C \<eta>)) \<cdot>\<^sub>D
                             \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f))"
            using antipar D.comp_arr_inv' D.comp_cod_arr D.comp_assoc by simp
          also have "... = D.inv (\<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f)) \<cdot>\<^sub>D
                             F ((\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>C \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>C (f \<star>\<^sub>C \<eta>)) \<cdot>\<^sub>D
                             \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f))"
          proof -
            have "(D.inv (\<Psi> (trg\<^sub>C f)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C f, f)) =
                  D.inv (\<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f))"
            proof -
              have "D.iso (\<Phi> (trg\<^sub>C f, f))"
                using antipar by simp
              moreover have "D.iso (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f)"
                using antipar \<Psi>_char(2) by simp
              moreover have "D.seq (\<Phi> (trg\<^sub>C f, f)) (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f)"
                using antipar D.iso_is_arr calculation(2)
                apply (intro D.seqI D.hseqI) by auto
              ultimately show ?thesis
                using antipar D.inv_comp \<Psi>_char(2) by simp
            qed
            moreover have "F (\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>D F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>D F (f \<star>\<^sub>C \<eta>) =
                           F ((\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>C \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>C (f \<star>\<^sub>C \<eta>))"
              using antipar by simp
            ultimately show ?thesis by simp
          qed
          also have "... = (D.lunit' (F f) \<cdot>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D
                             F (C.lunit' f \<cdot>\<^sub>C \<r>\<^sub>C[f]) \<cdot>\<^sub>D
                             (D.inv (F \<r>\<^sub>C[f]) \<cdot>\<^sub>D \<r>\<^sub>D[F f])"
          proof -
            have "F ((\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>C \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>C (f \<star>\<^sub>C \<eta>)) = F (C.lunit' f \<cdot>\<^sub>C \<r>\<^sub>C[f])"
              using triangle_left by simp
            moreover have "D.inv (\<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f)) =
                           D.lunit' (F f) \<cdot>\<^sub>D F \<l>\<^sub>C[f]"
            proof -
              have 0: "D.iso (\<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f))"
                using \<Psi>_char(2)
                apply (intro D.isos_compose D.seqI) by auto
              show ?thesis
              proof -
                have 1: "D.iso (F \<l>\<^sub>C[f])"
                  using C.iso_lunit preserves_iso by auto
                moreover have "D.iso (F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f))"
                  by (metis (no_types) A.ide_left D.iso_lunit ide_left lunit_coherence)
                moreover have "D.inv (D.inv (F \<l>\<^sub>C[f])) = F \<l>\<^sub>C[f]"
                  using 1 D.inv_inv by blast
                ultimately show ?thesis
                  by (metis 0 D.inv_comp D.invert_side_of_triangle(2) D.iso_inv_iso
                      D.iso_is_arr ide_left lunit_coherence)
              qed
            qed
            moreover have "\<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Psi> (src\<^sub>C f)) = D.inv (F \<r>\<^sub>C[f]) \<cdot>\<^sub>D \<r>\<^sub>D[F f]"
              using ide_left runit_coherence preserves_iso C.iso_runit D.invert_side_of_triangle(1)
              by (metis A.ide_left D.runit_simps(1))
            ultimately show ?thesis by simp
          qed
          also have "... = D.lunit' (F f) \<cdot>\<^sub>D
                             ((F \<l>\<^sub>C[f] \<cdot>\<^sub>D F (C.lunit' f)) \<cdot>\<^sub>D (F \<r>\<^sub>C[f] \<cdot>\<^sub>D D.inv (F \<r>\<^sub>C[f]))) \<cdot>\<^sub>D
                             \<r>\<^sub>D[F f]"
            using D.comp_assoc by simp
          also have "... = D.lunit' (F f) \<cdot>\<^sub>D \<r>\<^sub>D[F f]"
            using D.comp_cod_arr C.iso_runit C.iso_lunit preserves_iso D.comp_arr_inv'
                  preserves_inv
            by force
          finally show ?thesis by blast
        qed
        show "(F g \<star>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D
                \<a>\<^sub>D[F g, F f, F g] \<cdot>\<^sub>D (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f) \<star>\<^sub>D F g) =
              D.runit' (F g) \<cdot>\<^sub>D \<l>\<^sub>D[F g]"
        proof -
          have "\<a>\<^sub>D[F g, F f, F g] =
                D.inv (\<Phi> (g, f \<star>\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Phi> (f, g))) \<cdot>\<^sub>D
                  F \<a>\<^sub>C[g, f, g] \<cdot>\<^sub>D \<Phi> (g \<star>\<^sub>C f, g) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D F g)"
          proof -
            have "D.iso (\<Phi> (g, f \<star>\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Phi> (f, g)))"
              using antipar D.iso_is_arr
              apply (intro D.isos_compose, auto)
              by (metis C.iso_assoc D.comp_assoc D.seqE ide_left ide_right
                  preserves_assoc(1) preserves_iso)
            have "F \<a>\<^sub>C[g, f, g] \<cdot>\<^sub>D \<Phi> (g \<star>\<^sub>C f, g) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D F g) =
                   \<Phi> (g, f \<star>\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D \<a>\<^sub>D[F g, F f, F g]"
              using antipar assoc_coherence by simp
            moreover have "D.seq (F \<a>\<^sub>C[g, f, g]) (\<Phi> (g \<star>\<^sub>C f, g) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D F g))"
            proof (intro D.seqI)
              show 1: "D.hseq (\<Phi> (g, f)) (F g)"
                using antipar C.VV.arr_char by simp
              show "D.arr (\<Phi> (g \<star>\<^sub>C f, g))"
                using antipar C.VV.arr_char by simp
              show "D.dom (\<Phi> (g \<star>\<^sub>C f, g)) = D.cod (\<Phi> (g, f) \<star>\<^sub>D F g)"
              proof -
                have "D.iso (\<Phi> (g, f) \<star>\<^sub>D F g)"
                  using antipar by simp
                moreover have "D.iso (\<Phi> (g \<star>\<^sub>C f, g))"
                  using antipar by simp
                ultimately show ?thesis
                  by (metis C.iso_assoc D.comp_assoc D.iso_is_arr D.seqE
                      \<open>F \<a>\<^sub>C[g, f, g] \<cdot>\<^sub>D \<Phi> (g \<star>\<^sub>C f, g) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D F g) =
                       \<Phi> (g, f \<star>\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D \<a>\<^sub>D[F g, F f, F g]\<close>
                      antipar(1) antipar(2) ide_left ide_right preserves_assoc(1) preserves_iso)
              qed
              show "D.arr (F \<a>\<^sub>C[g, f, g])"
                using antipar by simp
              show "D.dom (F \<a>\<^sub>C[g, f, g]) = D.cod (\<Phi> (g \<star>\<^sub>C f, g) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D F g))"
              proof -
                have "D.iso (\<Phi> (g, f) \<star>\<^sub>D F g)"
                  using antipar by simp
                moreover have "D.seq (\<Phi> (g \<star>\<^sub>C f, g)) (\<Phi> (g, f) \<star>\<^sub>D F g)"
                  using antipar D.iso_is_arr
                  apply (intro D.seqI) by auto
                ultimately show ?thesis
                  using antipar by simp
              qed
            qed
            ultimately show ?thesis
              using \<open>D.iso (\<Phi> (g, f \<star>\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Phi> (f, g)))\<close> D.invert_side_of_triangle(1)
                    D.comp_assoc
              by auto
            qed
            hence "(F g \<star>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D
                     \<a>\<^sub>D[F g, F f, F g] \<cdot>\<^sub>D
                     (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f) \<star>\<^sub>D F g) =
                   (F g \<star>\<^sub>D (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon>) \<cdot>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D
                     D.inv (\<Phi> (g, f \<star>\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Phi> (f, g))) \<cdot>\<^sub>D
                     F \<a>\<^sub>C[g, f, g] \<cdot>\<^sub>D
                     \<Phi> (g \<star>\<^sub>C f, g) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D F g) \<cdot>\<^sub>D
                     (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f) \<star>\<^sub>D F g)"
              using D.comp_assoc by simp
            also have "... = ((F g \<star>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon>) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Phi> (f, g))) \<cdot>\<^sub>D
                               D.inv (\<Phi> (g, f \<star>\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Phi> (f, g))) \<cdot>\<^sub>D
                               F \<a>\<^sub>C[g, f, g] \<cdot>\<^sub>D \<Phi> (g \<star>\<^sub>C f, g) \<cdot>\<^sub>D
                               (\<Phi> (g, f) \<star>\<^sub>D F g) \<cdot>\<^sub>D ((D.inv (\<Phi> (g, f)) \<star>\<^sub>D F g) \<cdot>\<^sub>D
                               (F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f) \<star>\<^sub>D F g))"
            proof -
              have "F g \<star>\<^sub>D (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon>) \<cdot>\<^sub>D \<Phi> (f, g) =
                    (F g \<star>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon>) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Phi> (f, g))"
              proof -
                have "D.seq (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon>) (\<Phi> (f, g))"
                  using antipar D.comp_assoc by simp
                thus ?thesis
                  using antipar D.whisker_left by simp
              qed
              moreover have "D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f) \<star>\<^sub>D F g =
                             (D.inv (\<Phi> (g, f)) \<star>\<^sub>D F g) \<cdot>\<^sub>D (F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f) \<star>\<^sub>D F g)"
                using antipar D.whisker_right by simp
              ultimately show ?thesis
                using D.comp_assoc by simp
           qed
           also have "... = (F g \<star>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon>) \<cdot>\<^sub>D
                              (((F g \<star>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D D.inv (F g \<star>\<^sub>D \<Phi> (f, g))) \<cdot>\<^sub>D
                              D.inv (\<Phi> (g, f \<star>\<^sub>C g))) \<cdot>\<^sub>D F \<a>\<^sub>C[g, f, g] \<cdot>\<^sub>D \<Phi> (g \<star>\<^sub>C f, g) \<cdot>\<^sub>D
                              ((\<Phi> (g, f) \<star>\<^sub>D F g) \<cdot>\<^sub>D (D.inv (\<Phi> (g, f)) \<star>\<^sub>D F g)) \<cdot>\<^sub>D
                              (F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f) \<star>\<^sub>D F g)"
           proof -
             have "D.inv (\<Phi> (g, f \<star>\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Phi> (f, g))) =
                   D.inv (F g \<star>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D D.inv (\<Phi> (g, f \<star>\<^sub>C g))"
             proof -
              have "D.iso (\<Phi> (g, f \<star>\<^sub>C g))"
                using antipar by simp
              moreover have "D.iso (F g \<star>\<^sub>D \<Phi> (f, g))"
                using antipar by simp
              moreover have "D.seq (\<Phi> (g, f \<star>\<^sub>C g)) (F g \<star>\<^sub>D \<Phi> (f, g))"
                using antipar \<Phi>_in_hom A.ide_right D.iso_is_arr
                apply (intro D.seqI D.hseqI) by auto
              ultimately show ?thesis
                using antipar D.inv_comp by simp
            qed
            thus ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = (F g \<star>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon>) \<cdot>\<^sub>D
                             D.inv (\<Phi> (g, f \<star>\<^sub>C g)) \<cdot>\<^sub>D F \<a>\<^sub>C[g, f, g] \<cdot>\<^sub>D \<Phi> (g \<star>\<^sub>C f, g) \<cdot>\<^sub>D
                             (F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f) \<star>\<^sub>D F g)"
          proof -
            have "((\<Phi> (g, f) \<star>\<^sub>D F g) \<cdot>\<^sub>D (D.inv (\<Phi> (g, f)) \<star>\<^sub>D F g)) \<cdot>\<^sub>D
                    (F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f) \<star>\<^sub>D F g) =
                  (F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f) \<star>\<^sub>D F g)"
            proof -
              have "(\<Phi> (g, f) \<star>\<^sub>D F g) \<cdot>\<^sub>D (D.inv (\<Phi> (g, f)) \<star>\<^sub>D F g) = F (g \<star>\<^sub>C f) \<star>\<^sub>D F g"
                using antipar D.comp_arr_inv'
                      D.whisker_right [of "F g" "\<Phi> (g, f)" "D.inv (\<Phi> (g, f))"]
                by simp
              thus ?thesis
                using antipar D.comp_cod_arr D.whisker_right by simp
            qed
            moreover have "((F g \<star>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D D.inv (F g \<star>\<^sub>D \<Phi> (f, g))) \<cdot>\<^sub>D
                             D.inv (\<Phi> (g, f \<star>\<^sub>C g)) =
                           D.inv (\<Phi> (g, f \<star>\<^sub>C g))"
              using antipar D.comp_arr_inv' D.comp_cod_arr
                    D.whisker_left [of "F g" "\<Phi> (f, g)" "D.inv (\<Phi> (f, g))"]
              by simp
            ultimately show ?thesis by simp
          qed
          also have "... = (F g \<star>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f))) \<cdot>\<^sub>D
                             ((F g \<star>\<^sub>D F \<epsilon>) \<cdot>\<^sub>D D.inv (\<Phi> (g, f \<star>\<^sub>C g))) \<cdot>\<^sub>D
                             F \<a>\<^sub>C[g, f, g] \<cdot>\<^sub>D
                             (\<Phi> (g \<star>\<^sub>C f, g) \<cdot>\<^sub>D (F \<eta> \<star>\<^sub>D F g)) \<cdot>\<^sub>D
                             (\<Psi> (src\<^sub>C f) \<star>\<^sub>D F g)"
            using antipar D.whisker_left D.whisker_right \<Psi>_char(2) D.comp_assoc by simp
          also have "... = (F g \<star>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g)) \<cdot>\<^sub>D
                             (F (g \<star>\<^sub>C \<epsilon>) \<cdot>\<^sub>D F \<a>\<^sub>C[g, f, g] \<cdot>\<^sub>D F (\<eta> \<star>\<^sub>C g)) \<cdot>\<^sub>D
                             \<Phi> (trg\<^sub>C g, g) \<cdot>\<^sub>D (\<Psi> (src\<^sub>C f) \<star>\<^sub>D F g)"
          proof -
            have "(F g \<star>\<^sub>D F \<epsilon>) \<cdot>\<^sub>D D.inv (\<Phi> (g, f \<star>\<^sub>C g)) = D.inv (\<Phi> (g, src\<^sub>C g)) \<cdot>\<^sub>D F (g \<star>\<^sub>C \<epsilon>)"
              using antipar C.VV.arr_char \<Phi>.naturality [of "(g, \<epsilon>)"] FF_def 
                    D.invert_opposite_sides_of_square
              by simp
            moreover have "\<Phi> (g \<star>\<^sub>C f, g) \<cdot>\<^sub>D (F \<eta> \<star>\<^sub>D F g) = F (\<eta> \<star>\<^sub>C g) \<cdot>\<^sub>D \<Phi> (trg\<^sub>C g, g)"
              using antipar C.VV.arr_char \<Phi>.naturality [of "(\<eta>, g)"] FF_def by simp
            ultimately show ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = ((F g \<star>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g)) \<cdot>\<^sub>D
                             F (C.runit' g)) \<cdot>\<^sub>D (F \<l>\<^sub>C[g] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C g, g) \<cdot>\<^sub>D (\<Psi> (src\<^sub>C f) \<star>\<^sub>D F g))"
          proof -
            have "F (g \<star>\<^sub>C \<epsilon>) \<cdot>\<^sub>D F \<a>\<^sub>C[g, f, g] \<cdot>\<^sub>D F (\<eta> \<star>\<^sub>C g) = F (C.runit' g) \<cdot>\<^sub>D F \<l>\<^sub>C[g]"
              using ide_left ide_right antipar triangle_right
              by (metis C.comp_in_homE C.seqI' preserves_comp triangle_in_hom(2))
            thus ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = D.runit' (F g) \<cdot>\<^sub>D \<l>\<^sub>D[F g]"
          proof -
            have "D.inv \<r>\<^sub>D[F g] =
                  (F g \<star>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g)) \<cdot>\<^sub>D F (C.runit' g)"
            proof -
              have "D.runit' (F g) = D.inv (F \<r>\<^sub>C[g] \<cdot>\<^sub>D \<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g)))"
                using runit_coherence by simp
              also have
                "... = (F g \<star>\<^sub>D D.inv (\<Psi> (trg\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g)) \<cdot>\<^sub>D F (C.runit' g)"
              proof -
                have "D.inv (F \<r>\<^sub>C[g] \<cdot>\<^sub>D \<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g))) =
                       D.inv (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g)) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g)) \<cdot>\<^sub>D F (C.runit' g)"
                proof -
                  have "D.iso (F \<r>\<^sub>C[g])"
                    using preserves_iso by simp
                  moreover have 1: "D.iso (\<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g)))"
                    using preserves_iso \<Psi>_char(2) D.arrI D.seqE ide_right runit_coherence
                    by (intro D.isos_compose D.seqI, auto)
                  moreover have "D.seq (F \<r>\<^sub>C[g]) (\<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g)))"
                    using ide_right A.ide_right D.runit_simps(1) runit_coherence by metis
                  ultimately have "D.inv (F \<r>\<^sub>C[g] \<cdot>\<^sub>D \<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g))) =
                                   D.inv (\<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g))) \<cdot>\<^sub>D F (C.runit' g)"
                    using C.iso_runit preserves_inv D.inv_comp by simp
                  moreover have "D.inv (\<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g))) =
                                 D.inv (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g)) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g))"
                  proof -
                    have "D.seq (\<Phi> (g, src\<^sub>C g)) (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g))"
                      using 1 antipar preserves_iso \<Psi>_char(2) by fast
                      (*
                       * TODO: The fact that auto cannot do this step is probably what is blocking
                       * the whole thing from being done by auto.
                       *)
                    thus ?thesis
                      using 1 antipar preserves_iso \<Psi>_char(2) D.inv_comp by auto
                  qed
                  ultimately show ?thesis
                    using D.comp_assoc by simp
                qed
                thus ?thesis
                  using antipar \<Psi>_char(2) preserves_iso by simp
              qed
              finally show ?thesis by simp
            qed
            thus ?thesis
              using antipar lunit_coherence by simp
          qed
          finally show ?thesis by simp
        qed
      qed
    qed

    lemma preserves_adjoint_pair:
    assumes "C.adjoint_pair f g"
    shows "D.adjoint_pair (F f) (F g)"
      using assms C.adjoint_pair_def D.adjoint_pair_def preserves_adjunction by blast

    lemma preserves_left_adjoint:
    assumes "C.is_left_adjoint f"
    shows "D.is_left_adjoint (F f)"
      using assms preserves_adjoint_pair by auto

    lemma preserves_right_adjoint:
    assumes "C.is_right_adjoint g"
    shows "D.is_right_adjoint (F g)"
      using assms preserves_adjoint_pair by auto

  end

  context equivalence_pseudofunctor
  begin

    lemma reflects_adjunction:
    assumes "C.ide f" and "C.ide g"
    and "\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright>" and "\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright>"
    and "adjunction_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F f) (F g)
           (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))
           (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
    shows "adjunction_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>"
    proof -
      let ?\<eta>' = "D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)"
      let ?\<epsilon>' = "D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)"
      interpret A': adjunction_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>F f\<close> \<open>F g\<close> ?\<eta>' ?\<epsilon>'
        using assms(5) by auto
      interpret A: adjunction_data_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>
        using assms(1-4) by (unfold_locales, auto)
      show ?thesis
      proof
        show "(\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>C \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>C (f \<star>\<^sub>C \<eta>) = \<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>C \<r>\<^sub>C[f]"
        proof -
          have 1: "C.par ((\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>C \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>C (f \<star>\<^sub>C \<eta>)) (\<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>C \<r>\<^sub>C[f])"
            using assms A.antipar by simp
          moreover have "F ((\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>C \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>C (f \<star>\<^sub>C \<eta>)) = F (\<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>C \<r>\<^sub>C[f])"
          proof -
            have "F ((\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>C \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>C (f \<star>\<^sub>C \<eta>)) =
                  F (\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>D F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>D F (f \<star>\<^sub>C \<eta>)"
              using 1 by auto
            also have "... =
                       (F (\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, f)) \<cdot>\<^sub>D
                         (\<Phi> (f, g) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F f] \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv (\<Phi> (g, f))) \<cdot>\<^sub>D
                         (D.inv (\<Phi> (f, g \<star>\<^sub>C f)) \<cdot>\<^sub>D F (f \<star>\<^sub>C \<eta>))"
              using assms A.antipar preserves_assoc(2) D.comp_assoc by auto
            also have "... = \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D ((F \<epsilon> \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F f)) \<cdot>\<^sub>D
                               \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F f] \<cdot>\<^sub>D
                               ((F f \<star>\<^sub>D D.inv (\<Phi> (g, f))) \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<eta>)) \<cdot>\<^sub>D
                               D.inv (\<Phi> (f, src\<^sub>C f))"
            proof -
              have "F (\<epsilon> \<star>\<^sub>C f) \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, f) = \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (F \<epsilon> \<star>\<^sub>D F f)"
                using assms \<Phi>.naturality [of "(\<epsilon>, f)"] FF_def C.VV.arr_char by simp
              moreover have "D.inv (\<Phi> (f, g \<star>\<^sub>C f)) \<cdot>\<^sub>D F (f \<star>\<^sub>C \<eta>) =
                             (F f \<star>\<^sub>D F \<eta>) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f))"
              proof -
                have "F (f \<star>\<^sub>C \<eta>) \<cdot>\<^sub>D \<Phi> (f, src\<^sub>C f) = \<Phi> (f, g \<star>\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D F \<eta>)"
                  using assms \<Phi>.naturality [of "(f, \<eta>)"] FF_def C.VV.arr_char A.antipar
                  by simp
                thus ?thesis
                  using assms A.antipar \<Phi>_components_are_iso C.VV.arr_char \<Phi>_in_hom
                        FF_def
                        D.invert_opposite_sides_of_square
                          [of "\<Phi> (f, g \<star>\<^sub>C f)" "F f \<star>\<^sub>D F \<eta>" "F (f \<star>\<^sub>C \<eta>)" "\<Phi> (f, src\<^sub>C f)"]
                  by fastforce
              qed
              ultimately show ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                               \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F f] \<cdot>\<^sub>D
                               (F f \<star>\<^sub>D D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta>) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f))"
              using assms A.antipar \<Phi>_in_hom A.ide_left A.ide_right A'.ide_left A'.ide_right
                    D.whisker_left [of "F f" "D.inv (\<Phi> (g, f))" "F \<eta>"]
                    D.whisker_right [of "F f" "F \<epsilon>" "\<Phi> (f, g)"]
              by (metis A'.counit_in_vhom A'.unit_simps(1)D.arrI D.comp_assoc
                  D.src.preserves_reflects_arr D.src_vcomp D.vseq_implies_hpar(1) \<Phi>_simps(2))
            also have "... = \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<cdot>\<^sub>D ?\<epsilon>' \<star>\<^sub>D F f) \<cdot>\<^sub>D
                               \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F f] \<cdot>\<^sub>D
                               (F f \<star>\<^sub>D ?\<eta>' \<cdot>\<^sub>D D.inv (\<Psi> (src\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f))"
            proof -
              have "F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g) = \<Psi> (trg\<^sub>C f) \<cdot>\<^sub>D ?\<epsilon>'"
              proof -
                have "D.iso (\<Psi> (trg\<^sub>C f))"
                  using A.ide_left C.ideD(1) \<Psi>_char(2) by blast
                thus ?thesis
                  by (metis A'.counit_simps(1) D.comp_assoc D.comp_cod_arr D.inv_is_inverse
                      D.seqE D.comp_arr_inv)
              qed
              moreover have "D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> = ?\<eta>' \<cdot>\<^sub>D D.inv (\<Psi> (src\<^sub>C f))"
                using assms(2) \<Psi>_char D.comp_arr_inv D.inv_is_inverse D.comp_assoc D.comp_cod_arr
                by (metis A'.unit_simps(1) A.antipar(1) C.ideD(1) C.obj_trg
                    D.invert_side_of_triangle(2))
              ultimately show ?thesis by simp
            qed
            also have "... = \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D ((\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                               (?\<epsilon>' \<star>\<^sub>D F f)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F f] \<cdot>\<^sub>D ((F f \<star>\<^sub>D ?\<eta>') \<cdot>\<^sub>D
                               (F f \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C f)))) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f))"
              using assms A.antipar A'.antipar \<Psi>_char D.whisker_left D.whisker_right
              by simp
            also have "... = \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                               ((?\<epsilon>' \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F f] \<cdot>\<^sub>D (F f \<star>\<^sub>D ?\<eta>')) \<cdot>\<^sub>D
                               (F f \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f))"
              using D.comp_assoc by simp
            also have "... = (\<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C f) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f]) \<cdot>\<^sub>D
                               \<r>\<^sub>D[F f] \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f))"
              using A'.triangle_left D.comp_assoc by simp
            also have "... = F \<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>D F \<r>\<^sub>C[f]"
              using assms A.antipar preserves_lunit(2) preserves_runit(1) by simp
            also have "... = F (\<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>C \<r>\<^sub>C[f])"
              using assms by simp
            finally show ?thesis by simp
          qed
          ultimately show ?thesis
            using is_faithful by blast
        qed
        show "(g \<star>\<^sub>C \<epsilon>) \<cdot>\<^sub>C \<a>\<^sub>C[g, f, g] \<cdot>\<^sub>C (\<eta> \<star>\<^sub>C g) = \<r>\<^sub>C\<^sup>-\<^sup>1[g] \<cdot>\<^sub>C \<l>\<^sub>C[g]"
        proof -
          have 1: "C.par ((g \<star>\<^sub>C \<epsilon>) \<cdot>\<^sub>C \<a>\<^sub>C g f g \<cdot>\<^sub>C (\<eta> \<star>\<^sub>C g)) (\<r>\<^sub>C\<^sup>-\<^sup>1[g] \<cdot>\<^sub>C \<l>\<^sub>C[g])"
            using assms A.antipar by auto
          moreover have "F ((g \<star>\<^sub>C \<epsilon>) \<cdot>\<^sub>C \<a>\<^sub>C[g, f, g] \<cdot>\<^sub>C (\<eta> \<star>\<^sub>C g)) = F (\<r>\<^sub>C\<^sup>-\<^sup>1[g] \<cdot>\<^sub>C \<l>\<^sub>C[g])"
          proof -
            have "F ((g \<star>\<^sub>C \<epsilon>) \<cdot>\<^sub>C \<a>\<^sub>C g f g \<cdot>\<^sub>C (\<eta> \<star>\<^sub>C g)) =
                  F (g \<star>\<^sub>C \<epsilon>) \<cdot>\<^sub>D F \<a>\<^sub>C[g, f, g] \<cdot>\<^sub>D F (\<eta> \<star>\<^sub>C g)"
              using 1 by auto
            also have "... = (F (g \<star>\<^sub>C \<epsilon>) \<cdot>\<^sub>D \<Phi> (g, f \<star>\<^sub>C g)) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D
                             \<a>\<^sub>D[F g, F f, F g] \<cdot>\<^sub>D
                             (D.inv (\<Phi> (g, f)) \<star>\<^sub>D F g) \<cdot>\<^sub>D (D.inv (\<Phi> (g \<star>\<^sub>C f, g)) \<cdot>\<^sub>D F (\<eta> \<star>\<^sub>C g))"
              using assms A.antipar preserves_assoc(1) [of g f g] D.comp_assoc by auto
            also have "... = \<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D ((F g \<star>\<^sub>D F \<epsilon>) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Phi> (f, g))) \<cdot>\<^sub>D
                             \<a>\<^sub>D[F g, F f, F g] \<cdot>\<^sub>D
                             ((D.inv (\<Phi> (g, f)) \<star>\<^sub>D F g) \<cdot>\<^sub>D (F \<eta> \<star>\<^sub>D F g)) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g))"
            proof -
              have "F (g \<star>\<^sub>C \<epsilon>) \<cdot>\<^sub>D \<Phi> (g, f \<star>\<^sub>C g) = \<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D F \<epsilon>)"
                using assms \<Phi>.naturality [of "(g, \<epsilon>)"] FF_def C.VV.arr_char by auto
              moreover have "D.inv (\<Phi> (g \<star>\<^sub>C f, g)) \<cdot>\<^sub>D F (\<eta> \<star>\<^sub>C g) =
                             (F \<eta> \<star>\<^sub>D F g) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g))"
              proof -
                have "F (\<eta> \<star>\<^sub>C g) \<cdot>\<^sub>D \<Phi> (trg\<^sub>C g, g) = \<Phi> (g \<star>\<^sub>C f, g) \<cdot>\<^sub>D (F \<eta> \<star>\<^sub>D F g)"
                  using assms \<Phi>.naturality [of "(\<eta>, g)"] FF_def C.VV.arr_char A.antipar
                  by auto
                thus ?thesis
                  using assms A.antipar \<Phi>_components_are_iso C.VV.arr_char FF_def
                        D.invert_opposite_sides_of_square
                          [of "\<Phi> (g \<star>\<^sub>C f, g)" "F \<eta> \<star>\<^sub>D F g" "F (\<eta> \<star>\<^sub>C g)" "\<Phi> (trg\<^sub>C g, g)"]
                  by fastforce
              qed
              ultimately show ?thesis
                using D.comp_assoc by simp
            qed
            also have " ... = \<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D
                              \<a>\<^sub>D[F g, F f, F g] \<cdot>\<^sub>D
                              (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<star>\<^sub>D F g) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g))"
            proof -
              have "(F g \<star>\<^sub>D F \<epsilon>) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Phi> (f, g)) = F g \<star>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)"
                using assms A.antipar D.whisker_left
                by (metis A'.counit_simps(1) A'.ide_right D.seqE)
              moreover have "(D.inv (\<Phi> (g, f)) \<star>\<^sub>D F g) \<cdot>\<^sub>D (F \<eta> \<star>\<^sub>D F g) =
                             D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<star>\<^sub>D F g"
                using assms A.antipar D.whisker_right by simp
              ultimately show ?thesis by simp
            qed
            also have "... = \<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (trg\<^sub>C f) \<cdot>\<^sub>D ?\<epsilon>') \<cdot>\<^sub>D
                             \<a>\<^sub>D[F g, F f, F g] \<cdot>\<^sub>D
                             (?\<eta>' \<cdot>\<^sub>D D.inv (\<Psi> (src\<^sub>C f)) \<star>\<^sub>D F g) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g))"
            proof -
              have "F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g) = \<Psi> (trg\<^sub>C f) \<cdot>\<^sub>D ?\<epsilon>'"
                using \<Psi>_char D.comp_arr_inv D.inv_is_inverse D.comp_assoc D.comp_cod_arr
                by (metis A'.counit_simps(1) C.ideD(1) C.obj_trg D.seqE assms(1))
              moreover have "D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> = ?\<eta>' \<cdot>\<^sub>D D.inv (\<Psi> (src\<^sub>C f))"
                using \<Psi>_char D.comp_arr_inv D.inv_is_inverse D.comp_assoc D.comp_cod_arr
                by (metis A'.unit_simps(1) A.unit_simps(1) A.unit_simps(5)
                    C.obj_trg D.invert_side_of_triangle(2))
              ultimately show ?thesis by simp
            qed
            also have "... = \<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D
                             ((F g \<star>\<^sub>D ?\<epsilon>') \<cdot>\<^sub>D \<a>\<^sub>D[F g, F f, F g] \<cdot>\<^sub>D (?\<eta>' \<star>\<^sub>D F g)) \<cdot>\<^sub>D
                             (D.inv (\<Psi> (src\<^sub>C f)) \<star>\<^sub>D F g) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g))"
              using assms A.antipar \<Psi>_char D.whisker_left D.whisker_right D.comp_assoc
              by simp
            also have "... = \<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F g] \<cdot>\<^sub>D
                             \<l>\<^sub>D[F g] \<cdot>\<^sub>D (D.inv (\<Psi> (src\<^sub>C f)) \<star>\<^sub>D F g) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g))"
              using A'.triangle_right D.comp_assoc by simp
            also have "... = F \<r>\<^sub>C\<^sup>-\<^sup>1[g] \<cdot>\<^sub>D F \<l>\<^sub>C[g]"
                using assms A.antipar preserves_lunit(1) preserves_runit(2) D.comp_assoc
                by simp
            also have "... = F (\<r>\<^sub>C\<^sup>-\<^sup>1[g] \<cdot>\<^sub>C \<l>\<^sub>C[g])"
              using assms by simp
            finally show ?thesis by simp
          qed
          ultimately show ?thesis
            using is_faithful by blast
        qed
      qed
    qed

    lemma reflects_adjoint_pair:
    assumes "C.ide f" and "C.ide g"
    and "src\<^sub>C f = trg\<^sub>C g" and "src\<^sub>C g = trg\<^sub>C f"
    and "D.adjoint_pair (F f) (F g)"
    shows "C.adjoint_pair f g"
    proof -
      obtain \<eta>' \<epsilon>' where A': "adjunction_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F f) (F g) \<eta>' \<epsilon>'"
        using assms D.adjoint_pair_def by auto
      interpret A': adjunction_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>F f\<close> \<open>F g\<close> \<eta>' \<epsilon>'
        using A' by auto
      have 1: "\<guillemotleft>\<Phi> (g, f) \<cdot>\<^sub>D \<eta>' \<cdot>\<^sub>D D.inv (\<Psi> (src\<^sub>C f)) : F (src\<^sub>C f) \<Rightarrow>\<^sub>D F (g \<star>\<^sub>C f)\<guillemotright>"
        using assms \<Psi>_char [of "src\<^sub>C f"] A'.unit_in_hom
        by (intro D.comp_in_homI, auto)
      have 2: "\<guillemotleft>\<Psi> (trg\<^sub>C f) \<cdot>\<^sub>D \<epsilon>' \<cdot>\<^sub>D D.inv (\<Phi> (f, g)): F (f \<star>\<^sub>C g) \<Rightarrow>\<^sub>D F (trg\<^sub>C f)\<guillemotright>"
        using assms \<Phi>_in_hom [of f g] \<Psi>_char [of "trg\<^sub>C f"] A'.counit_in_hom
        by (intro D.comp_in_homI, auto)
      obtain \<eta> where \<eta>: "\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright> \<and>
                         F \<eta> = \<Phi> (g, f) \<cdot>\<^sub>D \<eta>' \<cdot>\<^sub>D D.inv (\<Psi> (src\<^sub>C f))"
        using assms 1 A'.unit_in_hom \<Phi>_in_hom locally_full by fastforce
      have \<eta>': "\<eta>' = D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f)"
        using assms 1 \<eta> \<Phi>_in_hom \<Phi>.components_are_iso C.VV.ide_char C.VV.arr_char D.iso_inv_iso
              \<Phi>_components_are_iso \<Psi>_char(2)
              D.invert_side_of_triangle(1) [of "F \<eta>" "\<Phi> (g, f)" "\<eta>' \<cdot>\<^sub>D D.inv (\<Psi> (src\<^sub>C f))"]
              D.invert_side_of_triangle(2) [of "D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta>" \<eta>' "D.inv (\<Psi> (src\<^sub>C f))"]
        by (metis (no_types, lifting) C.ideD(1) C.obj_trg D.arrI D.comp_assoc D.inv_inv)
      obtain \<epsilon> where \<epsilon>: "\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C trg\<^sub>C f\<guillemotright> \<and>
                         F \<epsilon> = \<Psi> (trg\<^sub>C f) \<cdot>\<^sub>D \<epsilon>' \<cdot>\<^sub>D D.inv (\<Phi> (f, g))"
        using assms 2 A'.counit_in_hom \<Phi>_in_hom locally_full by fastforce
      have \<epsilon>': "\<epsilon>' = D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)"
        using assms 2 \<epsilon> \<Phi>_in_hom \<Phi>.components_are_iso C.VV.ide_char C.VV.arr_char D.iso_inv_iso
              \<Psi>_char(2) D.comp_assoc
              D.invert_side_of_triangle(1) [of "F \<epsilon>" "\<Psi> (trg\<^sub>C f)" "\<epsilon>' \<cdot>\<^sub>D D.inv (\<Phi> (f, g))"]
              D.invert_side_of_triangle(2) [of "D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon>" \<epsilon>' "D.inv (\<Phi> (f, g))"]
        by (metis (no_types, lifting) C.arrI C.ideD(1) C.obj_trg D.inv_inv \<Phi>_components_are_iso
            preserves_arr)
      have "adjunction_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F f) (F g)
              (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D \<Psi> (src\<^sub>C f))                          
              (D.inv (\<Psi> (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
        using A'.adjunction_in_bicategory_axioms \<eta>' \<epsilon>' by simp
      hence "adjunction_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>"
        using assms \<eta> \<epsilon> reflects_adjunction by simp
      thus ?thesis
        using C.adjoint_pair_def by auto
    qed

    lemma reflects_left_adjoint:
    assumes "C.ide f" and "D.is_left_adjoint (F f)"
    shows "C.is_left_adjoint f"
    proof -
      obtain g' where g': "D.adjoint_pair (F f) g'"
        using assms D.adjoint_pair_def by auto
      obtain g where g: "\<guillemotleft>g : trg\<^sub>C f \<rightarrow>\<^sub>C src\<^sub>C f\<guillemotright> \<and> C.ide g \<and> D.isomorphic (F g) g'"
        using assms g' locally_essentially_surjective [of "trg\<^sub>C f" "src\<^sub>C f" g']
              D.adjoint_pair_antipar [of "F f" g']
        by auto
      obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : g' \<Rightarrow>\<^sub>D F g\<guillemotright> \<and> D.iso \<phi>"
        using g D.isomorphic_def D.isomorphic_symmetric by metis
      have "D.adjoint_pair (F f) (F g)"
        using assms g g' \<phi> D.adjoint_pair_preserved_by_iso [of "F f" g' "F f" "F f" \<phi> "F g"]
        by auto
      thus ?thesis
        using assms g reflects_adjoint_pair [of f g] D.adjoint_pair_antipar C.in_hhom_def
        by auto
    qed      

    lemma reflects_right_adjoint:
    assumes "C.ide g" and "D.is_right_adjoint (F g)"
    shows "C.is_right_adjoint g"
    proof -
      obtain f' where f': "D.adjoint_pair f' (F g)"
        using assms D.adjoint_pair_def by auto
      obtain f where f: "\<guillemotleft>f : trg\<^sub>C g \<rightarrow>\<^sub>C src\<^sub>C g\<guillemotright> \<and> C.ide f \<and> D.isomorphic (F f) f'"
        using assms f' locally_essentially_surjective [of "trg\<^sub>C g" "src\<^sub>C g" f']
              D.adjoint_pair_antipar [of f' "F g"]
        by auto
      obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : f' \<Rightarrow>\<^sub>D F f\<guillemotright> \<and> D.iso \<phi>"
        using f D.isomorphic_def D.isomorphic_symmetric by metis
      have "D.adjoint_pair (F f) (F g)"
        using assms f f' \<phi> D.adjoint_pair_preserved_by_iso [of f' "F g" \<phi> "F f" "F g" "F g"]
        by auto
      thus ?thesis
        using assms f reflects_adjoint_pair [of f g] D.adjoint_pair_antipar C.in_hhom_def
        by auto
    qed      

  end

  subsection "Composition of Adjunctions"

  text \<open>
    We first consider the strict case, then extend to all bicategories using strictification.
  \<close>

  locale composite_adjunction_in_strict_bicategory =
    strict_bicategory V H \<a> \<i> src trg +
    fg: adjunction_in_strict_bicategory V H \<a> \<i> src trg f g \<zeta> \<xi> +
    hk: adjunction_in_strict_bicategory V H \<a> \<i> src trg h k \<sigma> \<tau>
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
    where "\<eta> \<equiv> (g \<star> \<sigma> \<star> f) \<cdot> \<zeta>"

    abbreviation \<epsilon>
    where "\<epsilon> \<equiv> \<tau> \<cdot> (h \<star> \<xi> \<star> k)"

    interpretation adjunction_data_in_bicategory V H \<a> \<i> src trg \<open>h \<star> f\<close> \<open>g \<star> k\<close> \<eta> \<epsilon>
    proof
      show "ide (h \<star> f)"
        using composable by simp
      show "ide (g \<star> k)"
        using fg.antipar hk.antipar composable by simp
      show "\<guillemotleft>\<eta> : src (h \<star> f) \<Rightarrow> (g \<star> k) \<star> h \<star> f\<guillemotright>"
      proof
        show "\<guillemotleft>\<zeta> : src (h \<star> f) \<Rightarrow> g \<star> f\<guillemotright>"
          using fg.antipar hk.antipar composable \<open>ide (h \<star> f)\<close> by auto
        show "\<guillemotleft>g \<star> \<sigma> \<star> f : g \<star> f \<Rightarrow> (g \<star> k) \<star> h \<star> f\<guillemotright>"
        proof -
          have "\<guillemotleft>g \<star> \<sigma> \<star> f : g \<star> trg f \<star> f \<Rightarrow> g \<star> (k \<star> h) \<star> f\<guillemotright>"
            using fg.antipar hk.antipar composable hk.unit_in_hom
            apply (intro hcomp_in_vhom) by auto
          thus ?thesis
            using hcomp_obj_arr hcomp_assoc by fastforce
        qed
      qed
      show "\<guillemotleft>\<epsilon> : (h \<star> f) \<star> g \<star> k \<Rightarrow> src (g \<star> k)\<guillemotright>"
      proof
        show "\<guillemotleft>h \<star> \<xi> \<star> k : (h \<star> f) \<star> g \<star> k \<Rightarrow> h \<star> k\<guillemotright>"
        proof -
          have "\<guillemotleft>h \<star> \<xi> \<star> k : h \<star> (f \<star> g) \<star> k \<Rightarrow> h \<star> trg f \<star> k\<guillemotright>"
            using composable fg.antipar(1-2) hk.antipar(1) by fastforce
          thus ?thesis
            using fg.antipar hk.antipar composable hk.unit_in_hom hcomp_obj_arr hcomp_assoc
            by simp
        qed
        show "\<guillemotleft>\<tau> : h \<star> k \<Rightarrow> src (g \<star> k)\<guillemotright>"
          using fg.antipar hk.antipar composable hk.unit_in_hom by auto
      qed
    qed

    sublocale adjunction_in_strict_bicategory V H \<a> \<i> src trg \<open>h \<star> f\<close> \<open>g \<star> k\<close> \<eta> \<epsilon>
    proof
      show "(\<epsilon> \<star> h \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[h \<star> f, g \<star> k, h \<star> f] \<cdot> ((h \<star> f) \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[h \<star> f] \<cdot> \<r>[h \<star> f]"
      proof -
        have "(\<epsilon> \<star> h \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[h \<star> f, g \<star> k, h \<star> f] \<cdot> ((h \<star> f) \<star> \<eta>) =
              (\<tau> \<cdot> (h \<star> \<xi> \<star> k) \<star> h \<star> f) \<cdot> ((h \<star> f) \<star> (g \<star> \<sigma> \<star> f) \<cdot> \<zeta>)"
          using fg.antipar hk.antipar composable strict_assoc comp_ide_arr
                ide_left ide_right antipar(1) antipar(2)
          by (metis arrI seqE strict_assoc' triangle_in_hom(1))
        also have "... = (\<tau> \<star> h \<star> f) \<cdot> ((h \<star> \<xi> \<star> (k \<star> h) \<star> f) \<cdot> (h \<star> (f \<star> g) \<star> \<sigma> \<star> f)) \<cdot> (h \<star> f \<star> \<zeta>)"
          using fg.antipar hk.antipar composable whisker_left [of "h \<star> f"] whisker_right
            comp_assoc hcomp_assoc
          by simp
        also have "... = (\<tau> \<star> h \<star> f) \<cdot> (h \<star> (\<xi> \<star> (k \<star> h)) \<cdot> ((f \<star> g) \<star> \<sigma>) \<star> f) \<cdot> (h \<star> f \<star> \<zeta>)"
          using fg.antipar hk.antipar composable whisker_left whisker_right hcomp_assoc
          by simp
        also have "... = (\<tau> \<star> h \<star> f) \<cdot> (h \<star> (trg f \<star> \<sigma>) \<cdot> (\<xi> \<star> trg f) \<star> f) \<cdot> (h \<star> f \<star> \<zeta>)"
          using fg.antipar hk.antipar composable comp_arr_dom comp_cod_arr
                interchange [of \<xi> "f \<star> g" "k \<star> h" \<sigma>] interchange [of "trg f" \<xi> \<sigma> "trg f"]
          by (metis fg.counit_simps(1) fg.counit_simps(2) fg.counit_simps(3)
              hk.unit_simps(1) hk.unit_simps(2) hk.unit_simps(3))
        also have "... = (\<tau> \<star> h \<star> f) \<cdot> (h \<star> \<sigma> \<cdot> \<xi> \<star> f) \<cdot> (h \<star> f \<star> \<zeta>)"
          using fg.antipar hk.antipar composable hcomp_obj_arr hcomp_arr_obj
          by (metis fg.counit_simps(1) fg.counit_simps(4) hk.unit_simps(1) hk.unit_simps(5)
              obj_src)
        also have "... = ((\<tau> \<star> h \<star> f) \<cdot> (h \<star> \<sigma> \<star> f)) \<cdot> ((h \<star> \<xi> \<star> f) \<cdot> (h \<star> f \<star> \<zeta>))"
          using fg.antipar hk.antipar composable whisker_left whisker_right comp_assoc
          by simp
        also have "... = ((\<tau> \<star> h) \<cdot> (h \<star> \<sigma>) \<star> f) \<cdot> (h \<star> (\<xi> \<star> f) \<cdot> (f \<star> \<zeta>))"
          using fg.antipar hk.antipar composable whisker_left whisker_right hcomp_assoc
          by simp
        also have "... = h \<star> f"
          using fg.antipar hk.antipar composable fg.triangle_left hk.triangle_left
          by simp
        also have "... = \<l>\<^sup>-\<^sup>1[h \<star> f] \<cdot> \<r>[h \<star> f]"
          using fg.antipar hk.antipar composable strict_lunit' strict_runit by simp
        finally show ?thesis by simp
      qed
      show "((g \<star> k) \<star> \<epsilon>) \<cdot> \<a>[g \<star> k, h \<star> f, g \<star> k] \<cdot> (\<eta> \<star> g \<star> k) = \<r>\<^sup>-\<^sup>1[g \<star> k] \<cdot> \<l>[g \<star> k]"
      proof -
        have "((g \<star> k) \<star> \<epsilon>) \<cdot> \<a>[g \<star> k, h \<star> f, g \<star> k] \<cdot> (\<eta> \<star> g \<star> k) =
              ((g \<star> k) \<star> \<tau> \<cdot> (h \<star> \<xi> \<star> k)) \<cdot> ((g \<star> \<sigma> \<star> f) \<cdot> \<zeta> \<star> g \<star> k)"
          using fg.antipar hk.antipar composable strict_assoc comp_ide_arr
                ide_left ide_right
          by (metis antipar(1) antipar(2) arrI seqE triangle_in_hom(2))
        also have "... = (g \<star> k \<star> \<tau>) \<cdot> ((g \<star> (k \<star> h) \<star> \<xi> \<star> k) \<cdot> (g \<star> \<sigma> \<star> (f \<star> g) \<star> k)) \<cdot> (\<zeta> \<star> g \<star> k)"
          using fg.antipar hk.antipar composable whisker_left [of "g \<star> k"] whisker_right
            comp_assoc hcomp_assoc
          by simp
        also have "... = (g \<star> k \<star> \<tau>) \<cdot> (g \<star> ((k \<star> h) \<star> \<xi>) \<cdot> (\<sigma> \<star> f \<star> g) \<star> k) \<cdot> (\<zeta> \<star> g \<star> k)"
            using fg.antipar hk.antipar composable whisker_left whisker_right hcomp_assoc
            by simp
        also have "... = (g \<star> k \<star> \<tau>) \<cdot> (g \<star> (\<sigma> \<star> src g) \<cdot> (src g \<star> \<xi>) \<star> k) \<cdot> (\<zeta> \<star> g \<star> k)"
          using fg.antipar hk.antipar composable interchange [of "k \<star> h" \<sigma> \<xi> "f \<star> g"]
                interchange [of \<sigma> "src g" "src g" \<xi>] comp_arr_dom comp_cod_arr
          by (metis fg.counit_simps(1) fg.counit_simps(2) fg.counit_simps(3)
              hk.unit_simps(1) hk.unit_simps(2) hk.unit_simps(3))
        also have "... = (g \<star> k \<star> \<tau>) \<cdot> (g \<star> \<sigma> \<cdot> \<xi> \<star> k) \<cdot> (\<zeta> \<star> g \<star> k)"
          using fg.antipar hk.antipar composable hcomp_obj_arr [of "src g" \<xi>]
                hcomp_arr_obj [of \<sigma> "src g"]
          by simp
        also have "... = ((g \<star> k \<star> \<tau>) \<cdot> (g \<star> \<sigma> \<star> k)) \<cdot> (g \<star> \<xi> \<star> k) \<cdot> (\<zeta> \<star> g \<star> k)"
          using fg.antipar hk.antipar composable whisker_left whisker_right comp_assoc
          by simp
        also have "... = (g \<star> (k \<star> \<tau>) \<cdot> (\<sigma> \<star> k)) \<cdot> ((g \<star> \<xi>) \<cdot> (\<zeta> \<star> g) \<star> k)"
          using fg.antipar hk.antipar composable whisker_left whisker_right hcomp_assoc
          by simp
        also have "... = g \<star> k"
          using fg.antipar hk.antipar composable fg.triangle_right hk.triangle_right
          by simp
        also have "... = \<r>\<^sup>-\<^sup>1[g \<star> k] \<cdot> \<l>[g \<star> k]"
          using fg.antipar hk.antipar composable strict_lunit strict_runit' by simp
        finally show ?thesis by simp
      qed
    qed

    lemma is_adjunction_in_strict_bicategory:
    shows "adjunction_in_strict_bicategory V H \<a> \<i> src trg (h \<star> f) (g \<star> k) \<eta> \<epsilon>"
      ..

  end

  context strict_bicategory
  begin

    lemma left_adjoints_compose:
    assumes "is_left_adjoint f" and "is_left_adjoint f'" and "src f' = trg f"
    shows "is_left_adjoint (f' \<star> f)"
    proof -
      obtain g \<eta> \<epsilon> where fg: "adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using assms adjoint_pair_def by auto
      interpret fg: adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using fg by auto
      obtain g' \<eta>' \<epsilon>' where f'g': "adjunction_in_bicategory V H \<a> \<i> src trg f' g' \<eta>' \<epsilon>'"
        using assms adjoint_pair_def by auto
      interpret f'g': adjunction_in_bicategory V H \<a> \<i> src trg f' g' \<eta>' \<epsilon>'
        using f'g' by auto
      interpret f'fgg': composite_adjunction_in_strict_bicategory V H \<a> \<i> src trg
                          f g \<eta> \<epsilon> f' g' \<eta>' \<epsilon>'
        using assms apply unfold_locales by simp
      have "adjoint_pair (f' \<star> f) (g \<star> g')"
        using adjoint_pair_def f'fgg'.adjunction_in_bicategory_axioms by auto
      thus ?thesis by auto
    qed

    lemma right_adjoints_compose:
    assumes "is_right_adjoint g" and "is_right_adjoint g'" and "src g = trg g'"
    shows "is_right_adjoint (g \<star> g')"
    proof -
      obtain f \<eta> \<epsilon> where fg: "adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using assms adjoint_pair_def by auto
      interpret fg: adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using fg by auto
      obtain f' \<eta>' \<epsilon>' where f'g': "adjunction_in_bicategory V H \<a> \<i> src trg f' g' \<eta>' \<epsilon>'"
        using assms adjoint_pair_def by auto
      interpret f'g': adjunction_in_bicategory V H \<a> \<i> src trg f' g' \<eta>' \<epsilon>'
        using f'g' by auto
      interpret f'fgg': composite_adjunction_in_strict_bicategory V H \<a> \<i> src trg
                          f g \<eta> \<epsilon> f' g' \<eta>' \<epsilon>'
        using assms fg.antipar f'g'.antipar apply unfold_locales by simp
      have "adjoint_pair (f' \<star> f) (g \<star> g')"
        using adjoint_pair_def f'fgg'.adjunction_in_bicategory_axioms by auto
      thus ?thesis by auto
    qed

  end

  text \<open>
    We now use strictification to extend the preceding results to an arbitrary bicategory.
    We only prove that ``left adjoints compose'' and ``right adjoints compose'';
    I did not work out formulas for the unit and counit of the composite adjunction in the
    non-strict case.
  \<close>

  context bicategory
  begin

    interpretation S: strictified_bicategory V H \<a> \<i> src trg ..

    notation S.vcomp  (infixr "\<cdot>\<^sub>S" 55)
    notation S.hcomp  (infixr "\<star>\<^sub>S" 53)
    notation S.in_hom  ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>S _\<guillemotright>")
    notation S.in_hhom  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>S _\<guillemotright>")

    interpretation UP: fully_faithful_functor V S.vcomp S.UP
      using S.UP_is_fully_faithful_functor by auto
    interpretation UP: equivalence_pseudofunctor V H \<a> \<i> src trg
                          S.vcomp S.hcomp S.\<a> S.\<i> S.src S.trg S.UP S.\<Phi>
      using S.UP_is_equivalence_pseudofunctor by auto

    lemma left_adjoints_compose:
    assumes "is_left_adjoint f" and "is_left_adjoint f'" and "src f = trg f'"
    shows "is_left_adjoint (f \<star> f')"
    proof -
      have "S.is_left_adjoint (S.UP f) \<and> S.is_left_adjoint (S.UP f')"
        using assms UP.preserves_left_adjoint by simp
      moreover have "S.src (S.UP f) = S.trg (S.UP f')"
        using assms left_adjoint_is_ide by simp
      ultimately have "S.is_left_adjoint (S.hcomp (S.UP f) (S.UP f'))"
        using S.left_adjoints_compose by simp
      moreover have "S.isomorphic (S.hcomp (S.UP f) (S.UP f')) (S.UP (f \<star> f'))"
      proof -
        have "\<guillemotleft>S.\<Phi> (f, f') : S.hcomp (S.UP f) (S.UP f') \<Rightarrow>\<^sub>S S.UP (f \<star> f')\<guillemotright>"
          using assms left_adjoint_is_ide UP.\<Phi>_in_hom by simp
        moreover have "S.iso (S.\<Phi> (f, f'))"
          using assms left_adjoint_is_ide by simp
        ultimately show ?thesis
          using S.isomorphic_def by blast
      qed
      ultimately have "S.is_left_adjoint (S.UP (f \<star> f'))"
        using S.left_adjoint_preserved_by_iso S.isomorphic_def by blast
      thus "is_left_adjoint (f \<star> f')"
        using assms left_adjoint_is_ide UP.reflects_left_adjoint by simp
    qed

    lemma right_adjoints_compose:
    assumes "is_right_adjoint g" and "is_right_adjoint g'" and "src g' = trg g"
    shows "is_right_adjoint (g' \<star> g)"
    proof -
      have "S.is_right_adjoint (S.UP g) \<and> S.is_right_adjoint (S.UP g')"
        using assms UP.preserves_right_adjoint by simp
      moreover have "S.src (S.UP g') = S.trg (S.UP g)"
        using assms right_adjoint_is_ide by simp
      ultimately have "S.is_right_adjoint (S.hcomp (S.UP g') (S.UP g))"
        using S.right_adjoints_compose by simp
      moreover have "S.isomorphic (S.hcomp (S.UP g') (S.UP g)) (S.UP (g' \<star> g))"
      proof -
        have "\<guillemotleft>S.\<Phi> (g', g) : S.hcomp (S.UP g') (S.UP g) \<Rightarrow>\<^sub>S S.UP (g' \<star> g)\<guillemotright>"
          using assms right_adjoint_is_ide UP.\<Phi>_in_hom by simp
        moreover have "S.iso (S.\<Phi> (g', g))"
          using assms right_adjoint_is_ide by simp
        ultimately show ?thesis
          using S.isomorphic_def by blast
      qed
      ultimately have "S.is_right_adjoint (S.UP (g' \<star> g))"
        using S.right_adjoint_preserved_by_iso S.isomorphic_def by blast
      thus "is_right_adjoint (g' \<star> g)"
        using assms right_adjoint_is_ide UP.reflects_right_adjoint by simp
    qed

  end

  subsection "Choosing Right Adjoints"

  text \<open>
    It will be useful in various situations to suppose that we have made a choice of
    right adjoint for each left adjoint ({\it i.e.} each ``map'') in a bicategory.
  \<close>

  locale chosen_right_adjoints =
    bicategory
  begin

    (* Global notation is evil! *)
    no_notation Transitive_Closure.rtrancl  ("(_\<^sup>*)" [1000] 999)

    definition some_right_adjoint  ("_\<^sup>*" [1000] 1000)
    where "f\<^sup>* \<equiv> SOME g. adjoint_pair f g"

    definition some_unit
    where "some_unit f \<equiv> SOME \<eta>. \<exists>\<epsilon>. adjunction_in_bicategory V H \<a> \<i> src trg f f\<^sup>* \<eta> \<epsilon>"

    definition some_counit
    where "some_counit f \<equiv>
           SOME \<epsilon>. adjunction_in_bicategory V H \<a> \<i> src trg f f\<^sup>* (some_unit f) \<epsilon>"

    lemma left_adjoint_extends_to_adjunction:
    assumes "is_left_adjoint f"
    shows "adjunction_in_bicategory V H \<a> \<i> src trg f f\<^sup>* (some_unit f) (some_counit f)"
      using assms some_right_adjoint_def adjoint_pair_def some_unit_def some_counit_def
            someI_ex [of "\<lambda>g. adjoint_pair f g"]
            someI_ex [of "\<lambda>\<eta>. \<exists>\<epsilon>. adjunction_in_bicategory V H \<a> \<i> src trg f f\<^sup>* \<eta> \<epsilon>"]
            someI_ex [of "\<lambda>\<epsilon>. adjunction_in_bicategory V H \<a> \<i> src trg f f\<^sup>* (some_unit f) \<epsilon>"]
      by auto

    lemma left_adjoint_extends_to_adjoint_pair:
    assumes "is_left_adjoint f"
    shows "adjoint_pair f f\<^sup>*"
      using assms adjoint_pair_def left_adjoint_extends_to_adjunction by blast

    lemma right_adjoint_in_hom [intro]:
    assumes "is_left_adjoint f"
    shows "\<guillemotleft>f\<^sup>* : trg f \<rightarrow> src f\<guillemotright>"
    and "\<guillemotleft>f\<^sup>* : f\<^sup>* \<Rightarrow> f\<^sup>*\<guillemotright>"
      using assms left_adjoint_extends_to_adjoint_pair adjoint_pair_antipar [of f "f\<^sup>*"]
      by auto

    lemma right_adjoint_simps [simp]:
    assumes "is_left_adjoint f"
    shows "ide f\<^sup>*"
    and "src f\<^sup>* = trg f" and "trg f\<^sup>* = src f"
    and "dom f\<^sup>* = f\<^sup>*" and "cod f\<^sup>* = f\<^sup>*"
      using assms right_adjoint_in_hom left_adjoint_extends_to_adjoint_pair apply auto
      using assms right_adjoint_is_ide [of "f\<^sup>*"] by blast

  end

  locale map_in_bicategory =
    bicategory + chosen_right_adjoints +
  fixes f :: 'a
  assumes is_map: "is_left_adjoint f"
  begin

    abbreviation \<eta>
      where "\<eta> \<equiv> some_unit f"

    abbreviation \<epsilon>
      where "\<epsilon> \<equiv> some_counit f"

    sublocale adjunction_in_bicategory V H \<a> \<i> src trg f \<open>f\<^sup>*\<close> \<eta> \<epsilon>
      using is_map left_adjoint_extends_to_adjunction by simp

  end

  subsection "Equivalences Refine to Adjoint Equivalences"

  text \<open>
    In this section, we show that, just as an equivalence between categories can always
    be refined to an adjoint equivalence, an internal equivalence in a bicategory can also
    always be so refined.
    The proof, which follows that of Theorem 3.3 from \cite{nlab-adjoint-equivalence},
    makes use of the fact that if an internal equivalence satisfies one of the triangle
    identities, then it also satisfies the other.
  \<close>

  locale adjoint_equivalence_in_bicategory =
    equivalence_in_bicategory +
    adjunction_in_bicategory
  begin

    lemma dual_adjoint_equivalence:
    shows "adjoint_equivalence_in_bicategory V H \<a> \<i> src trg g f (inv \<epsilon>) (inv \<eta>)"
    proof -
      interpret gf: equivalence_in_bicategory V H \<a> \<i> src trg g f \<open>inv \<epsilon>\<close> \<open>inv \<eta>\<close>
        using dual_equivalence by simp
      show ?thesis
      proof
        show "(inv \<eta> \<star> g) \<cdot> \<a>\<^sup>-\<^sup>1[g, f, g] \<cdot> (g \<star> inv \<epsilon>) = \<l>\<^sup>-\<^sup>1[g] \<cdot> \<r>[g]"
        proof -
          have "(inv \<eta> \<star> g) \<cdot> \<a>\<^sup>-\<^sup>1[g, f, g] \<cdot> (g \<star> inv \<epsilon>) =
                inv ((g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g))"
            using antipar inv_comp iso_inv_iso isos_compose comp_assoc by simp
          also have "... = inv (\<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g])"
            using triangle_right by simp
          also have "... = \<l>\<^sup>-\<^sup>1[g] \<cdot> \<r>[g]"
            using iso_inv_iso inv_comp by simp
          finally show ?thesis
            by blast
        qed
        show "(f \<star> inv \<eta>) \<cdot> \<a>[f, g, f] \<cdot> (inv \<epsilon> \<star> f) = \<r>\<^sup>-\<^sup>1[f] \<cdot> \<l>[f]"
        proof -
          have "(f \<star> inv \<eta>) \<cdot> \<a>[f, g, f] \<cdot> (inv \<epsilon> \<star> f) =
                inv ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>))"
            using antipar inv_comp iso_inv_iso isos_compose comp_assoc by simp
          also have "... = inv (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f])"
            using triangle_left by simp
          also have "... = \<r>\<^sup>-\<^sup>1[f] \<cdot> \<l>[f]"
            using iso_inv_iso inv_comp by simp
          finally show ?thesis by blast
        qed
      qed
    qed

  end

  context strict_bicategory
  begin

    lemma equivalence_refines_to_adjoint_equivalence:
    assumes "equivalence_map f" and "\<guillemotleft>g : trg f \<rightarrow> src f\<guillemotright>" and "ide g"
    and "\<guillemotleft>\<eta> : src f \<Rightarrow> g \<star> f\<guillemotright>" and "iso \<eta>"
    shows "\<exists>!\<epsilon>. adjoint_equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
    proof -
      obtain g' \<eta>' \<epsilon>' where E': "equivalence_in_bicategory V H \<a> \<i> src trg f g' \<eta>' \<epsilon>'"
        using assms equivalence_map_def by auto
      interpret E': equivalence_in_bicategory V H \<a> \<i> src trg f g' \<eta>' \<epsilon>'
        using E' by auto
      let ?a = "src f" and ?b = "trg f"
      (* TODO: in_homE cannot be applied automatically to a conjunction.  Must break down! *)
      have f_in_hhom: "\<guillemotleft>f : ?a \<rightarrow> ?b\<guillemotright>" and ide_f: "ide f"
        using assms equivalence_map_def by auto
      have g_in_hhom: "\<guillemotleft>g : ?b \<rightarrow> ?a\<guillemotright>" and ide_g: "ide g"
        using assms by auto
      have g'_in_hhom: "\<guillemotleft>g' : ?b \<rightarrow> ?a\<guillemotright>" and ide_g': "ide g'"
        using assms f_in_hhom E'.antipar by auto
      have \<eta>_in_hom: "\<guillemotleft>\<eta> : ?a \<Rightarrow> g \<star> f\<guillemotright>" and iso_\<eta>: "iso \<eta>"
        using assms by auto
      have a: "obj ?a" and b: "obj ?b"
        using f_in_hhom by auto
      have \<eta>_in_hhom: "\<guillemotleft>\<eta> : ?a \<rightarrow> ?a\<guillemotright>"
        using a src_dom trg_dom \<eta>_in_hom by fastforce
      text \<open>
        The following is quoted from \cite{nlab-adjoint-equivalence}:
        \begin{quotation}
          ``Since \<open>g \<cong> gfg' \<cong> g'\<close>, the isomorphism \<open>fg' \<cong> 1\<close> also induces an isomorphism \<open>fg \<cong> 1\<close>,
          which we denote \<open>\<xi>\<close>.  Now \<open>\<eta>\<close> and \<open>\<xi>\<close> may not satisfy the zigzag identities, but if we
          define \<open>\<epsilon>\<close> by \<open>\<xi> \<cdot> (f \<star> \<eta>\<^sup>-\<^sup>1) \<cdot> (f \<star> g \<star> \<xi>\<^sup>-\<^sup>1) : f \<star> g \<Rightarrow> 1\<close>, then we can verify,
          using string diagram notation as above,
          that \<open>\<epsilon>\<close> satisfies one zigzag identity, and hence (by the previous lemma) also the other.

          Finally, if \<open>\<epsilon>': fg \<Rightarrow> 1\<close> is any other isomorphism satisfying the zigzag identities
          with \<open>\<eta>\<close>, then we have:
          \[
              \<open>\<epsilon>' = \<epsilon>' \<cdot> (\<epsilon> f g) \<cdot> (f \<eta> g) = \<epsilon> \<cdot> (f g \<epsilon>') \<cdot> (f \<eta> g) = \<epsilon>\<close>
          \]
          using the interchange law and two zigzag identities.  This shows uniqueness.''
        \end{quotation}
      \<close>
      have 1: "isomorphic g g'"
      proof -
        have "isomorphic g (g \<star> ?b)"
          using assms hcomp_arr_obj isomorphic_reflexive by auto
        also have "isomorphic ... (g \<star> f \<star> g')"
          using assms f_in_hhom g_in_hhom g'_in_hhom E'.counit_in_vhom E'.counit_is_iso
                isomorphic_def hcomp_ide_isomorphic isomorphic_symmetric
          by (metis E'.counit_simps(5) in_hhomE trg_trg)
        also have "isomorphic ... (?a \<star> g')"
          using assms f_in_hhom g_in_hhom g'_in_hhom ide_g' E'.unit_in_vhom E'.unit_is_iso
                isomorphic_def hcomp_isomorphic_ide isomorphic_symmetric
          by (metis hcomp_assoc hcomp_isomorphic_ide in_hhomE src_src)
        also have "isomorphic ... g'"
          using assms
          by (simp add: E'.antipar(1) hcomp_obj_arr isomorphic_reflexive)
        finally show ?thesis by blast
      qed
      moreover have "isomorphic (f \<star> g') ?b"
        using E'.counit_is_iso isomorphicI [of \<epsilon>'] by auto
      hence 2: "isomorphic (f \<star> g) ?b"
        using assms 1 ide_f hcomp_ide_isomorphic [of f g g'] isomorphic_transitive
              isomorphic_symmetric
        by (metis in_hhomE)
      obtain \<xi> where \<xi>: "\<guillemotleft>\<xi> : f \<star> g \<Rightarrow> ?b\<guillemotright> \<and> iso \<xi>"
        using 2 by auto
      have \<xi>_in_hom: "\<guillemotleft>\<xi> : f \<star> g \<Rightarrow> ?b\<guillemotright>" and iso_\<xi>: "iso \<xi>"
        using \<xi> by auto
      have \<xi>_in_hhom: "\<guillemotleft>\<xi> : ?b \<rightarrow> ?b\<guillemotright>"
        using b src_cod trg_cod \<xi>_in_hom by fastforce
      text \<open>
        At the time of this writing, the definition of \<open>\<epsilon>\<close> given on nLab
        \cite{nlab-adjoint-equivalence} had an apparent typo:
        the expression \<open>f \<star> g \<star> \<xi>\<^sup>-\<^sup>1\<close> should read \<open>\<xi>\<^sup>-\<^sup>1 \<star> f \<star> g\<close>, as we have used here.
      \<close>
      let ?\<epsilon> = "\<xi> \<cdot> (f \<star> inv \<eta> \<star> g) \<cdot> (inv \<xi> \<star> f \<star> g)"
      have \<epsilon>_in_hom: "\<guillemotleft>?\<epsilon> : f \<star> g \<Rightarrow> ?b\<guillemotright>"
      proof -
        have "\<guillemotleft>f \<star> inv \<eta> \<star> g : f \<star> g \<star> f \<star> g \<Rightarrow> f \<star> g\<guillemotright>"
        proof -
          have "\<guillemotleft>inv \<eta> : g \<star> f \<Rightarrow> ?a\<guillemotright>"
            using \<eta>_in_hom iso_\<eta> by auto
          hence "\<guillemotleft>f \<star> inv \<eta> \<star> g : f \<star> (g \<star> f) \<star> g \<Rightarrow> f \<star> ?a \<star> g\<guillemotright>"
            using assms by (intro hcomp_in_vhom, auto)
          hence "\<guillemotleft>f \<star> inv \<eta> \<star> g : f \<star> (g \<star> f) \<star> g \<Rightarrow> f \<star> g\<guillemotright>"
            using assms f_in_hhom hcomp_obj_arr by (metis in_hhomE)
          moreover have "f \<star> (g \<star> f) \<star> g = f \<star> g \<star> f \<star> g"
            using hcomp_assoc by simp
          ultimately show ?thesis by simp
        qed
        moreover have "\<guillemotleft>inv \<xi> \<star> f \<star> g : f \<star> g \<Rightarrow> f \<star> g \<star> f \<star> g\<guillemotright>"
        proof -
          have "\<guillemotleft>inv \<xi> \<star> f \<star> g : ?b \<star> f \<star> g \<Rightarrow> (f \<star> g) \<star> f \<star> g\<guillemotright>"
            using assms \<xi>_in_hom iso_\<xi> by (intro hcomp_in_vhom, auto)
          moreover have "(f \<star> g) \<star> f \<star> g = f \<star> g \<star> f \<star> g"
            using hcomp_assoc by simp
          moreover have "?b \<star> f \<star> g = f \<star> g"
            using f_in_hhom g_in_hhom b hcomp_obj_arr [of ?b "f \<star> g"] by fastforce
          ultimately show ?thesis by simp
        qed
        ultimately show "\<guillemotleft>?\<epsilon> : f \<star> g \<Rightarrow> ?b\<guillemotright>"
          using \<xi>_in_hom by blast
      qed
      have "iso ?\<epsilon>"
        using f_in_hhom g_in_hhom \<eta>_in_hhom ide_f ide_g \<eta>_in_hom iso_\<eta> \<xi>_in_hhom \<xi>_in_hom iso_\<xi>
              iso_inv_iso isos_compose
        by (metis \<epsilon>_in_hom arrI hseqE ide_is_iso iso_hcomp seqE)
      have 4: "\<guillemotleft>inv \<xi> \<star> f : ?b \<star> f \<Rightarrow> f \<star> g \<star> f\<guillemotright>"
      proof -
        have "\<guillemotleft>inv \<xi> \<star> f : ?b \<star> f \<Rightarrow> (f \<star> g) \<star> f\<guillemotright>"
          using \<xi>_in_hom iso_\<xi> f_in_hhom
          by (intro hcomp_in_vhom, auto)
        thus ?thesis
          using hcomp_assoc by simp
      qed
      text \<open>
        First show \<open>?\<epsilon>\<close> and \<open>\<eta>\<close> satisfy the ``left'' triangle identity.
      \<close>
      have triangle_left: "(?\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>) = f"
      proof -
        have "(?\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>) = (\<xi> \<star> f) \<cdot> (f \<star> inv \<eta> \<star> g \<star> f) \<cdot> (inv \<xi> \<star> f \<star> g \<star> f) \<cdot> (?b \<star> f \<star> \<eta>)"
        proof -
          have "f \<star> \<eta> = ?b \<star> f \<star> \<eta>"
            using b \<eta>_in_hhom hcomp_obj_arr [of ?b "f \<star> \<eta>"] by fastforce
          moreover have "\<xi> \<cdot> (f \<star> inv \<eta> \<star> g) \<cdot> (inv \<xi> \<star> f \<star> g) \<star> f =
                         (\<xi> \<star> f) \<cdot> ((f \<star> inv \<eta> \<star> g) \<star> f) \<cdot> ((inv \<xi> \<star> f \<star> g) \<star> f)"
            using ide_f ide_g \<xi>_in_hhom \<xi>_in_hom iso_\<xi> \<eta>_in_hhom \<eta>_in_hom iso_\<eta> whisker_right
            by (metis \<epsilon>_in_hom arrI in_hhomE seqE)
          moreover have "... = (\<xi> \<star> f) \<cdot> (f \<star> inv \<eta> \<star> g \<star> f) \<cdot> (inv \<xi> \<star> f \<star> g \<star> f)"
            using hcomp_assoc by simp
          ultimately show ?thesis
            using comp_assoc by simp
        qed
        also have "... = (\<xi> \<star> f) \<cdot> ((f \<star> inv \<eta> \<star> g \<star> f) \<cdot> (f \<star> g \<star> f \<star> \<eta>)) \<cdot> (inv \<xi> \<star> f)"
        proof -
          have "((inv \<xi> \<star> f) \<star> (g \<star> f)) \<cdot> ((?b \<star> f) \<star> \<eta>) = (inv \<xi> \<star> f) \<cdot> (?b \<star> f) \<star> (g \<star> f) \<cdot> \<eta>"
          proof -
            have "seq (inv \<xi> \<star> f) (?b \<star> f)"
              using a b 4 ide_f ide_g \<xi>_in_hhom \<xi>_in_hom iso_\<xi> \<eta>_in_hhom \<eta>_in_hom iso_\<eta>
              by blast
            moreover have "seq (g \<star> f) \<eta>"
              using f_in_hhom g_in_hhom ide_g ide_f \<eta>_in_hom by fast
            ultimately show ?thesis
              using interchange [of "inv \<xi> \<star> f" "?b \<star> f" "g \<star> f" \<eta>] by simp
          qed
          also have "... = inv \<xi> \<star> f \<star> \<eta>"
          proof -
            have "(inv \<xi> \<star> f) \<cdot> (?b \<star> f) = inv \<xi> \<star> f"
              using 4 comp_arr_dom by auto
            moreover have "(g \<star> f) \<cdot> \<eta> = \<eta>"
              using \<eta>_in_hom comp_cod_arr by auto
            ultimately show ?thesis
              using hcomp_assoc by simp
          qed
          also have "... = (f \<star> g) \<cdot> inv \<xi> \<star> (f \<star> \<eta>) \<cdot> (f \<star> ?a)"
          proof -
            have "(f \<star> g) \<cdot> inv \<xi> = inv \<xi>"
              using \<xi>_in_hom iso_\<xi> comp_cod_arr by auto
            moreover have "(f \<star> \<eta>) \<cdot> (f \<star> ?a) = f \<star> \<eta>"
            proof -
              have "\<guillemotleft>f \<star> \<eta> : f \<star> ?a \<Rightarrow> f \<star> g \<star> f\<guillemotright>"
                using \<eta>_in_hom by fastforce
              thus ?thesis
                using comp_arr_dom by blast
            qed
            ultimately show ?thesis by argo
          qed
          also have "... = ((f \<star> g) \<star> (f \<star> \<eta>)) \<cdot> (inv \<xi> \<star> (f \<star> ?a))"
          proof -
            have "seq (f \<star> g) (inv \<xi>)"
              using \<xi>_in_hom iso_\<xi> comp_cod_arr by auto
            moreover have "seq (f \<star> \<eta>) (f \<star> ?a)"
              using f_in_hhom \<eta>_in_hom by force
            ultimately show ?thesis
              using interchange by simp
          qed
          also have "... = (f \<star> g \<star> f \<star> \<eta>) \<cdot> (inv \<xi> \<star> f)"
            using hcomp_arr_obj hcomp_assoc by auto
          finally have "((inv \<xi> \<star> f) \<star> (g \<star> f)) \<cdot> ((?b \<star> f) \<star> \<eta>) = (f \<star> g \<star> f \<star> \<eta>) \<cdot> (inv \<xi> \<star> f)"
            by simp
          thus ?thesis
            using comp_assoc hcomp_assoc by simp
        qed
        also have "... = (\<xi> \<star> f) \<cdot> ((f \<star> ?a \<star> \<eta>) \<cdot> (f \<star> inv \<eta> \<star> ?a)) \<cdot> (inv \<xi> \<star> f)"
        proof -
          have "(f \<star> inv \<eta> \<star> g \<star> f) \<cdot> (f \<star> (g \<star> f) \<star> \<eta>) = f \<star> (inv \<eta> \<star> g \<star> f) \<cdot> ((g \<star> f) \<star> \<eta>)"
          proof -
            have "seq ((inv \<eta> \<star> g) \<star> f) ((g \<star> f) \<star> \<eta>)"
            proof -
              have "seq (inv \<eta> \<star> g \<star> f) ((g \<star> f) \<star> \<eta>)"
                using f_in_hhom ide_f g_in_hhom ide_g \<eta>_in_hhom \<eta>_in_hom iso_\<eta>
                apply (intro seqI)
                  apply blast
                 apply blast
                by fastforce
              thus ?thesis
                using hcomp_assoc by simp
            qed
            hence "(f \<star> (inv \<eta> \<star> g) \<star> f) \<cdot> (f \<star> (g \<star> f) \<star> \<eta>) =
                             f \<star> ((inv \<eta> \<star> g) \<star> f) \<cdot> ((g \<star> f) \<star> \<eta>)"
              using whisker_left by simp
            thus ?thesis
              using hcomp_assoc by simp
          qed
          also have "... = f \<star> (?a \<star> \<eta>) \<cdot> (inv \<eta> \<star> ?a)"
          proof -
            have "(inv \<eta> \<star> g \<star> f) \<cdot> ((g \<star> f) \<star> \<eta>) = (?a \<star> \<eta>) \<cdot> (inv \<eta> \<star> ?a)"
            proof -
              have "(inv \<eta> \<star> g \<star> f) \<cdot> ((g \<star> f) \<star> \<eta>) = inv \<eta> \<cdot> (g \<star> f) \<star> (g \<star> f) \<cdot> \<eta>"
              proof -
                have "seq (inv \<eta>) (g \<star> f)"
                  using g_in_hhom ide_g \<eta>_in_hom iso_\<eta> by force                  
                moreover have "seq (g \<star> f) \<eta>"
                  using g_in_hhom ide_g \<eta>_in_hom by fastforce
                ultimately show ?thesis
                  using interchange by fastforce
              qed
              also have "... = inv \<eta> \<star> \<eta>"
                using \<eta>_in_hom iso_\<eta> comp_arr_dom comp_cod_arr by auto
              also have "... = ?a \<cdot> inv \<eta> \<star> \<eta> \<cdot> ?a"
                using \<eta>_in_hom iso_\<eta> comp_arr_dom comp_cod_arr by auto
              also have "... = (?a \<star> \<eta>) \<cdot> (inv \<eta> \<star> ?a)"
              proof -
                have "seq ?a (inv \<eta>)"
                  using a \<eta>_in_hom iso_\<eta> ideD [of ?a] by (elim objE, auto)
                moreover have "seq \<eta> ?a"
                  using a \<eta>_in_hom by fastforce
                ultimately show ?thesis
                  using interchange by blast
              qed
              finally show ?thesis by simp
            qed
            thus ?thesis by argo
          qed
          also have "... = (f \<star> ?a \<star> \<eta>) \<cdot> (f \<star> inv \<eta> \<star> ?a)"
          proof -
            have "seq (?a \<star> \<eta>) (inv \<eta> \<star> ?a)"
            proof (intro seqI')
              show "\<guillemotleft>inv \<eta> \<star> ?a : (g \<star> f) \<star> ?a \<Rightarrow> ?a \<star> ?a\<guillemotright>"
                using a g_in_hhom \<eta>_in_hom iso_\<eta> hseqI ide_f ide_g
                apply (elim in_homE in_hhomE, intro hcomp_in_vhom)
                by auto
              show "\<guillemotleft>?a \<star> \<eta> : ?a \<star> ?a \<Rightarrow> ?a \<star> g \<star> f\<guillemotright>"
                using a \<eta>_in_hom hseqI by (intro hcomp_in_vhom, auto)
            qed
            thus ?thesis
              using whisker_left by simp
          qed
          finally show ?thesis
            using hcomp_assoc by simp
        qed
        also have "... = (\<xi> \<star> f) \<cdot> ((f \<star> \<eta>) \<cdot> (f \<star> inv \<eta>)) \<cdot> (inv \<xi> \<star> f)"
          using a \<eta>_in_hhom iso_\<eta> hcomp_obj_arr [of ?a \<eta>] hcomp_arr_obj [of "inv \<eta>" ?a] by auto
        also have "... = (\<xi> \<star> f) \<cdot> (inv \<xi> \<star> f)"
        proof -
          have "(f \<star> \<eta>) \<cdot> (f \<star> inv \<eta>) = f \<star> \<eta> \<cdot> inv \<eta>"
            using \<eta>_in_hhom iso_\<eta> whisker_left inv_in_hom by auto
          moreover have "f \<star> \<eta> \<cdot> inv \<eta> = f \<star> g \<star> f"
            using \<eta>_in_hom iso_\<eta> comp_arr_inv inv_is_inverse by auto
          moreover have "(f \<star> g \<star> f) \<cdot> (inv \<xi> \<star> f) = inv \<xi> \<star> f"
          proof -
            have "\<guillemotleft>inv \<xi> \<star> f : ?b \<star> f \<Rightarrow> f \<star> g \<star> f\<guillemotright>"
            proof -
              have "\<guillemotleft>inv \<xi> \<star> f : ?b \<star> f \<Rightarrow> (f \<star> g) \<star> f\<guillemotright>"
                using \<xi>_in_hom iso_\<xi> by (intro hcomp_in_vhom, auto)
              thus ?thesis
                using hcomp_assoc by simp
            qed
            moreover have "f \<star> g \<star> f = cod (inv \<xi> \<star> f)"
              using \<xi>_in_hhom iso_\<xi> hcomp_assoc calculation by auto
            ultimately show ?thesis
              using comp_cod_arr by auto
          qed
          ultimately show ?thesis by simp
        qed
        also have "... = ?b \<star> f"
        proof -
          have "(\<xi> \<star> f) \<cdot> (inv \<xi> \<star> f) = \<xi> \<cdot> inv \<xi> \<star> f"
            using \<xi>_in_hhom iso_\<xi> whisker_right by auto
          moreover have "\<xi> \<cdot> inv \<xi> = ?b"
            using \<xi>_in_hom iso_\<xi> comp_arr_inv inv_is_inverse by auto
          ultimately show ?thesis by simp
        qed
        also have "... = f"
          using hcomp_obj_arr by auto
        finally show ?thesis by blast
      qed

      (* TODO: Putting this earlier breaks some steps in the proof. *)
      interpret E: equivalence_in_strict_bicategory V H \<a> \<i> src trg f g \<eta> ?\<epsilon>
        using ide_g \<eta>_in_hom \<epsilon>_in_hom g_in_hhom `iso \<eta>` `iso ?\<epsilon>`
        by (unfold_locales, auto)

      text \<open>
        Apply ``triangle left if and only iff right'' to show the ``right'' triangle identity.
      \<close>
      have triangle_right: "((g \<star> \<xi> \<cdot> (f \<star> inv \<eta> \<star> g) \<cdot> (inv \<xi> \<star> f \<star> g)) \<cdot> (\<eta> \<star> g) = g)"
        using triangle_left E.triangle_left_iff_right by simp

      text \<open>
        Use the two triangle identities to establish an adjoint equivalence and show that
        there is only one choice for the counit.
      \<close>
      show "\<exists>!\<epsilon>. adjoint_equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
      proof -
        have "adjoint_equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> ?\<epsilon>"
        proof
          show "(?\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
          proof -
            have "(?\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = (?\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>)"
            proof -
              have "seq \<a>\<^sup>-\<^sup>1[f, g, f] (f \<star> \<eta>)"
                using E.antipar
                by (intro seqI, auto)
              hence "\<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = f \<star> \<eta>"
                using ide_f ide_g E.antipar triangle_right strict_assoc' comp_ide_arr
                by presburger
              thus ?thesis by simp
            qed
            also have "... = f"
              using triangle_left by simp
            also have "... = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
              using strict_lunit strict_runit by simp
            finally show ?thesis by simp
          qed
          show "(g \<star> ?\<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
          proof -
            have "(g \<star> ?\<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = (g \<star> ?\<epsilon>) \<cdot> (\<eta> \<star> g)"
            proof -
              have "seq \<a>[g, f, g] (\<eta> \<star> g)"
                using E.antipar
                by (intro seqI, auto)
              hence "\<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<eta> \<star> g"
                using ide_f ide_g E.antipar triangle_right strict_assoc comp_ide_arr
                by presburger
              thus ?thesis by simp
            qed
            also have "... = g"
              using triangle_right by simp
            also have "... = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
              using strict_lunit strict_runit by simp
            finally show ?thesis by blast
          qed
        qed
        moreover have "\<And>\<epsilon> \<epsilon>'. \<lbrakk> adjoint_equivalence_in_bicategory (\<cdot>) (\<star>) \<a> \<i> src trg f g \<eta> \<epsilon>;
                                adjoint_equivalence_in_bicategory (\<cdot>) (\<star>) \<a> \<i> src trg f g \<eta> \<epsilon>' \<rbrakk>
                                   \<Longrightarrow> \<epsilon> = \<epsilon>'"
          using adjunction_unit_determines_counit
          by (meson adjoint_equivalence_in_bicategory.axioms(2))
        ultimately show ?thesis by auto
      qed
    qed

  end

  text \<open>
    We now apply strictification to generalize the preceding result to an arbitrary bicategory.
  \<close>

  context bicategory
  begin

    interpretation S: strictified_bicategory V H \<a> \<i> src trg ..

    notation S.vcomp  (infixr "\<cdot>\<^sub>S" 55)
    notation S.hcomp  (infixr "\<star>\<^sub>S" 53)
    notation S.in_hom  ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>S _\<guillemotright>")
    notation S.in_hhom  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>S _\<guillemotright>")

    interpretation UP: fully_faithful_functor V S.vcomp S.UP
      using S.UP_is_fully_faithful_functor by auto
    interpretation UP: equivalence_pseudofunctor V H \<a> \<i> src trg
                          S.vcomp S.hcomp S.\<a> S.\<i> S.src S.trg S.UP S.\<Phi>
      using S.UP_is_equivalence_pseudofunctor by auto
    interpretation UP: pseudofunctor_into_strict_bicategory V H \<a> \<i> src trg
                          S.vcomp S.hcomp S.\<a> S.\<i> S.src S.trg S.UP S.\<Phi>
      ..

    lemma equivalence_refines_to_adjoint_equivalence:
    assumes "equivalence_map f" and "\<guillemotleft>g : trg f \<rightarrow> src f\<guillemotright>" and "ide g"
    and "\<guillemotleft>\<eta> : src f \<Rightarrow> g \<star> f\<guillemotright>" and "iso \<eta>"
    shows "\<exists>!\<epsilon>. adjoint_equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
    proof -
      text \<open>
        To unpack the consequences of the assumptions, we need to obtain an
        interpretation of @{locale equivalence_in_bicategory}, even though we don't
        need the associated data other than \<open>f\<close>, \<open>a\<close>, and \<open>b\<close>.
      \<close>
      obtain g' \<phi> \<psi> where E: "equivalence_in_bicategory V H \<a> \<i> src trg f g' \<phi> \<psi>"
        using assms equivalence_map_def by auto
      interpret E: equivalence_in_bicategory V H \<a> \<i> src trg f g' \<phi> \<psi>
        using E by auto
      let ?a = "src f" and ?b = "trg f"
      have ide_f: "ide f" by simp
      have f_in_hhom: "\<guillemotleft>f : ?a \<rightarrow> ?b\<guillemotright>" by simp
      have a: "obj ?a" and b: "obj ?b" by auto
      have 1: "S.equivalence_map (S.UP f)"
        using assms UP.preserves_equivalence_maps by simp
      let ?\<eta>' = "S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<cdot>\<^sub>S UP.\<Psi> ?a"
      have 2: "\<guillemotleft>S.UP \<eta> : S.UP ?a \<Rightarrow>\<^sub>S S.UP (g \<star> f)\<guillemotright>"
        using assms UP.preserves_hom [of \<eta> "src f" "g \<star> f"] by auto
      have 4: "\<guillemotleft>?\<eta>' : UP.map\<^sub>0 ?a \<Rightarrow>\<^sub>S S.UP g \<star>\<^sub>S S.UP f\<guillemotright> \<and> S.iso ?\<eta>'"
      proof (intro S.comp_in_homI conjI)
        have 3: "S.iso (S.\<Phi> (g, f))"
          using assms UP.\<Phi>_components_are_iso by auto
        show "\<guillemotleft>S.inv (S.\<Phi> (g, f)) : S.UP (g \<star> f) \<Rightarrow>\<^sub>S S.UP g \<star>\<^sub>S S.UP f\<guillemotright>"
          using assms 3 UP.\<Phi>_in_hom(2) [of g f] UP.FF_def by auto
        moreover show "\<guillemotleft>UP.\<Psi> ?a : UP.map\<^sub>0 ?a \<Rightarrow>\<^sub>S S.UP ?a\<guillemotright>" by auto
        moreover show "\<guillemotleft>S.UP \<eta> : S.UP ?a \<Rightarrow>\<^sub>S S.UP (g \<star> f)\<guillemotright>"
          using 2 by simp
        ultimately show "S.iso (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<cdot>\<^sub>S UP.\<Psi> ?a)"
          using assms 3 a UP.\<Psi>_char(2) S.iso_inv_iso
          apply (intro S.isos_compose) by auto
      qed
      have ex_un_\<xi>': "\<exists>!\<xi>'. adjoint_equivalence_in_bicategory S.vcomp S.hcomp S.\<a> S.\<i> S.src S.trg
                               (S.UP f) (S.UP g) ?\<eta>' \<xi>'"
      proof -
        have "\<guillemotleft>S.UP g : S.trg (S.UP f) \<rightarrow>\<^sub>S S.src (S.UP f)\<guillemotright>"
          using assms(2) by auto
        moreover have "S.ide (S.UP g)"
          by (simp add: assms(3))
        ultimately show ?thesis
          using 1 4 S.equivalence_refines_to_adjoint_equivalence S.UP_map\<^sub>0_obj by simp
      qed
      obtain \<xi>' where \<xi>': "adjoint_equivalence_in_bicategory S.vcomp S.hcomp S.\<a> S.\<i> S.src S.trg
                             (S.UP f) (S.UP g) ?\<eta>' \<xi>'"
        using ex_un_\<xi>' by auto
      interpret E': adjoint_equivalence_in_bicategory S.vcomp S.hcomp S.\<a> S.\<i> S.src S.trg
                      \<open>S.UP f\<close> \<open>S.UP g\<close> ?\<eta>' \<xi>'
        using \<xi>' by auto
      let ?\<epsilon>' = "UP.\<Psi> ?b \<cdot>\<^sub>S \<xi>' \<cdot>\<^sub>S S.inv (S.\<Phi> (f, g))"
      have \<epsilon>': "\<guillemotleft>?\<epsilon>' : S.UP (f \<star> g) \<Rightarrow>\<^sub>S S.UP ?b\<guillemotright>"
        using assms(2-3) S.UP_map\<^sub>0_obj apply (intro S.in_homI) by auto
      have ex_un_\<epsilon>: "\<exists>!\<epsilon>. \<guillemotleft>\<epsilon> : f \<star> g \<Rightarrow> ?b\<guillemotright> \<and> S.UP \<epsilon> = ?\<epsilon>'"
      proof -
        have "\<exists>\<epsilon>. \<guillemotleft>\<epsilon> : f \<star> g \<Rightarrow> ?b\<guillemotright> \<and> S.UP \<epsilon> = ?\<epsilon>'"
        proof -
          have "src (f \<star> g) = src ?b \<and> trg (f \<star> g) = trg ?b"
          proof -
            have "arr (f \<star> g)"
              using assms(2) f_in_hhom by blast
            thus ?thesis
              using assms(2) f_in_hhom by (elim hseqE, auto)
          qed
          moreover have "ide (f \<star> g)"
            using assms(2-3) by auto
          ultimately show ?thesis
            using \<epsilon>' UP.locally_full by auto
        qed
        moreover have
          "\<And>\<mu> \<nu>. \<lbrakk> \<guillemotleft>\<mu> : f \<star> g \<Rightarrow> ?b\<guillemotright>; S.UP \<mu> = ?\<epsilon>'; \<guillemotleft>\<nu> : f \<star> g \<Rightarrow> ?b\<guillemotright>; S.UP \<nu> = ?\<epsilon>' \<rbrakk>
                     \<Longrightarrow> \<mu> = \<nu>"
        proof -
          fix \<mu> \<nu>
          assume \<mu>: "\<guillemotleft>\<mu> : f \<star> g \<Rightarrow> ?b\<guillemotright>" and \<nu>: "\<guillemotleft>\<nu> : f \<star> g \<Rightarrow> ?b\<guillemotright>"
          and 1: "S.UP \<mu> = ?\<epsilon>'" and 2: "S.UP \<nu> = ?\<epsilon>'"
          have "par \<mu> \<nu>"
            using \<mu> \<nu> by fastforce
          thus "\<mu> = \<nu>"
            using 1 2 UP.is_faithful [of \<mu> \<nu>] by simp
        qed
        ultimately show ?thesis by auto
      qed
      have iso_\<epsilon>': "S.iso ?\<epsilon>'"
      proof (intro S.isos_compose)
        show "S.iso (S.inv (S.\<Phi> (f, g)))"
          using assms UP.\<Phi>_components_are_iso S.iso_inv_iso by auto
        show "S.iso \<xi>'"
          using E'.counit_is_iso by blast
        show "S.iso (UP.\<Psi> ?b)"
          using b UP.\<Psi>_char(2) by simp
        show "S.seq (UP.\<Psi> ?b) (\<xi>' \<cdot>\<^sub>S S.inv (S.\<Phi> (f, g)))"
        proof (intro S.seqI')
          show "\<guillemotleft>UP.\<Psi> ?b : UP.map\<^sub>0 ?b \<Rightarrow>\<^sub>S S.UP ?b\<guillemotright>"
            using b UP.\<Psi>_char by simp
          show "\<guillemotleft>\<xi>' \<cdot>\<^sub>S S.inv (S.\<Phi> (f, g)) : S.UP (f \<star> g) \<Rightarrow>\<^sub>S UP.map\<^sub>0 ?b\<guillemotright>"
            using assms UP.\<Phi>_components_are_iso VV.arr_char S.\<Phi>_in_hom [of "(f, g)"]
                  E'.counit_in_hom S.UP_map\<^sub>0_obj
            apply (intro S.comp_in_homI) by auto
        qed
        thus "S.seq \<xi>' (S.inv (S.\<Phi> (f, g)))" by auto
      qed
      obtain \<epsilon> where \<epsilon>: "\<guillemotleft>\<epsilon> : f \<star> g \<Rightarrow> ?b\<guillemotright> \<and> S.UP \<epsilon> = ?\<epsilon>'"
        using ex_un_\<epsilon> by auto
      interpret E'': equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using assms(1,3-5)
        apply unfold_locales
             apply simp_all
        using assms(2) \<epsilon>
         apply auto[1]
        using \<epsilon> iso_\<epsilon>' UP.reflects_iso [of \<epsilon>]
        by auto
      interpret E'': adjoint_equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
      proof
        show "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
        proof -
          have "S.UP ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) =
                S.\<Phi> (trg f, f) \<cdot>\<^sub>S (S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                  (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
            using E''.UP_triangle(3) by simp
          also have
            "... = S.\<Phi> (trg f, f) \<cdot>\<^sub>S (UP.\<Psi> ?b \<cdot>\<^sub>S \<xi>' \<cdot>\<^sub>S S.inv (S.\<Phi> (f, g)) \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                     (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
            using \<epsilon> S.comp_assoc by simp
          also have "... = S.\<Phi> (trg f, f) \<cdot>\<^sub>S (UP.\<Psi> ?b \<cdot>\<^sub>S \<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                             (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
          proof -
            have "\<xi>' \<cdot>\<^sub>S S.inv (S.\<Phi> (f, g)) \<cdot>\<^sub>S S.\<Phi> (f, g) = \<xi>'"
            proof -
              have "S.iso (S.\<Phi> (f, g))"
                using assms by auto
              moreover have "S.dom (S.\<Phi> (f, g)) = S.UP f \<star>\<^sub>S S.UP g"
                using assms by auto
              ultimately have "S.inv (S.\<Phi> (f, g)) \<cdot>\<^sub>S S.\<Phi> (f, g) = S.UP f \<star>\<^sub>S S.UP g"
                using S.comp_inv_arr' by simp
              thus ?thesis
                using S.comp_arr_dom E'.counit_in_hom(2) by simp
            qed
            thus ?thesis by argo
          qed
          also have
            "... = S.\<Phi> (trg f, f) \<cdot>\<^sub>S (UP.\<Psi> ?b \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                     ((\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f))) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.UP \<eta>)) \<cdot>\<^sub>S
                     S.inv (S.\<Phi> (f, src f))"
          proof -
            have "UP.\<Psi> ?b \<cdot>\<^sub>S \<xi>' \<star>\<^sub>S S.UP f = (UP.\<Psi> ?b \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S (\<xi>' \<star>\<^sub>S S.UP f)"
              using assms b UP.\<Psi>_char S.whisker_right S.UP_map\<^sub>0_obj by auto
            moreover have "S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> =
                           (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f))) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.UP \<eta>)"
              using assms S.whisker_left S.comp_assoc by auto
            ultimately show ?thesis
              using S.comp_assoc by simp
          qed
          also have "... = (S.\<Phi> (trg f, f) \<cdot>\<^sub>S (UP.\<Psi> ?b \<star>\<^sub>S S.UP f)) \<cdot>\<^sub>S
                             (S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> (src f))) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
          proof -
            have "(\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f))) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.UP \<eta>) =
                  (S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> (src f)))"
            proof -
              have "(S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f))) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.UP \<eta>) =
                      S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>"
                using assms S.whisker_left by auto
              hence "((\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f))) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.UP \<eta>)) =
                     ((\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>))"
                by simp
              also have "... = ((\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S S.\<a>' (S.UP f) (S.UP g) (S.UP f)) \<cdot>\<^sub>S
                                 (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>)"
              proof -
                have "(\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S S.\<a>' (S.UP f) (S.UP g) (S.UP f) = \<xi>' \<star>\<^sub>S S.UP f"
                proof -
                  have "\<guillemotleft>\<xi>' \<star>\<^sub>S S.UP f :
                          (S.UP f \<star>\<^sub>S S.UP g) \<star>\<^sub>S S.UP f \<Rightarrow>\<^sub>S S.trg (S.UP f) \<star>\<^sub>S S.UP f\<guillemotright>"
                    using assms by (intro S.hcomp_in_vhom, auto)
                  moreover have "\<guillemotleft>S.\<a>' (S.UP f) (S.UP g) (S.UP f) :
                                    S.UP f \<star>\<^sub>S S.UP g \<star>\<^sub>S S.UP f \<Rightarrow>\<^sub>S (S.UP f \<star>\<^sub>S S.UP g) \<star>\<^sub>S S.UP f\<guillemotright>"
                    using assms S.assoc'_in_hom by auto
                  ultimately show ?thesis
                    using assms S.strict_assoc' S.iso_assoc S.hcomp_assoc E'.antipar
                          S.comp_arr_ide S.seqI'
                    by (metis (no_types, lifting) E'.ide_left E'.ide_right)
                qed
                thus ?thesis
                  using S.comp_assoc by simp
              qed
              also have "... = ((\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S S.\<a>' (S.UP f) (S.UP g) (S.UP f) \<cdot>\<^sub>S
                                 (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>))"
                using S.comp_assoc by simp
              also have "... = (S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> (src f)))"
              proof -
                have "(\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S S.\<a>' (S.UP f) (S.UP g) (S.UP f) \<cdot>\<^sub>S
                        (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) =
                      (S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> (src f)))"
                proof -
                  have "(\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S S.\<a>' (S.UP f) (S.UP g) (S.UP f) \<cdot>\<^sub>S
                          (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) \<cdot>\<^sub>S
                          (S.UP f \<star>\<^sub>S UP.\<Psi> ?a) =
                        S.lunit' (S.UP f) \<cdot>\<^sub>S S.runit (S.UP f)"
                  proof -
                    have "(\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S S.\<a>' (S.UP f) (S.UP g) (S.UP f) \<cdot>\<^sub>S
                            (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) \<cdot>\<^sub>S
                            (S.UP f \<star>\<^sub>S UP.\<Psi> ?a) =
                          (\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S S.\<a>' (S.UP f) (S.UP g) (S.UP f) \<cdot>\<^sub>S
                            (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<cdot>\<^sub>S UP.\<Psi> ?a)"
                    proof -
                      have "S.seq (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) (UP.\<Psi> ?a)"
                        using assms UP.\<Psi>_char UP.\<Phi>_components_are_iso
                              E'.unit_simps(1) S.comp_assoc
                        by presburger 
                      hence "(S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S UP.\<Psi> ?a) =
                             S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<cdot>\<^sub>S UP.\<Psi> ?a"
                        using assms UP.\<Psi>_char UP.\<Phi>_components_are_iso S.comp_assoc
                              S.whisker_left [of "S.UP f" "S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>" "UP.\<Psi> ?a"]
                        by simp
                      thus ?thesis by simp
                    qed
                    thus ?thesis
                      using assms E'.triangle_left UP.\<Phi>_components_are_iso UP.\<Psi>_char
                      by argo
                  qed
                  also have "... = S.UP f"
                    using S.strict_lunit' S.strict_runit by simp
                  finally have 1: "((\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S S.\<a>' (S.UP f) (S.UP g) (S.UP f) \<cdot>\<^sub>S
                                     (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>)) \<cdot>\<^sub>S
                                     (S.UP f \<star>\<^sub>S UP.\<Psi> ?a) = S.UP f"
                    using S.comp_assoc by simp
                  have "(\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S S.\<a>' (S.UP f) (S.UP g) (S.UP f) \<cdot>\<^sub>S
                           (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) =
                         S.UP f \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> ?a))"
                  proof -
                    have "S.arr (S.UP f)"
                      using assms by simp
                    moreover have "S.iso (S.UP f \<star>\<^sub>S UP.\<Psi> ?a)"
                      using assms UP.\<Psi>_char S.UP_map\<^sub>0_obj by auto
                    moreover have "S.inv (S.UP f \<star>\<^sub>S UP.\<Psi> ?a) = S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> ?a)"
                      using assms a UP.\<Psi>_char S.UP_map\<^sub>0_obj by auto
                    ultimately show ?thesis
                      using assms 1 UP.\<Psi>_char UP.\<Phi>_components_are_iso
                            S.invert_side_of_triangle(2)
                              [of "S.UP f" "(\<xi>' \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S S.\<a>' (S.UP f) (S.UP g) (S.UP f) \<cdot>\<^sub>S
                                              (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>)"
                                  "S.UP f \<star>\<^sub>S UP.\<Psi> ?a"]
                      by presburger
                  qed
                  also have "... = S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> ?a)"
                  proof -
                    have "\<guillemotleft>S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> ?a) :
                             S.UP f \<star>\<^sub>S S.UP ?a \<Rightarrow>\<^sub>S S.UP f \<star>\<^sub>S UP.map\<^sub>0 ?a\<guillemotright>"
                      using assms ide_f f_in_hhom UP.\<Psi>_char [of ?a] S.inv_in_hom
                      apply (intro S.hcomp_in_vhom)
                        apply auto[1]
                       apply blast
                      by auto
                    moreover have "S.UP f \<star>\<^sub>S UP.map\<^sub>0 ?a = S.UP f"
                      using a S.hcomp_arr_obj S.UP_map\<^sub>0_obj by auto
                    finally show ?thesis
                      using S.comp_cod_arr by blast
                  qed
                  finally show ?thesis by auto
                qed
                thus ?thesis
                  using S.comp_assoc by simp
              qed
              finally show ?thesis by simp
            qed
            thus ?thesis
              using S.comp_assoc by simp
          qed
          also have "... = S.UP \<l>\<^sup>-\<^sup>1[f] \<cdot>\<^sub>S S.UP \<r>[f]"
          proof -
             have "S.\<Phi> (trg f, f) \<cdot>\<^sub>S (UP.\<Psi> ?b \<star>\<^sub>S S.UP f) = S.UP \<l>\<^sup>-\<^sup>1[f]"
             proof -
               have "S.UP f = S.UP \<l>[f] \<cdot>\<^sub>S S.\<Phi> (trg f, f) \<cdot>\<^sub>S (UP.\<Psi> (trg f) \<star>\<^sub>S S.UP f)"
                 using UP.lunit_coherence iso_lunit S.strict_lunit by simp
               thus ?thesis
                 using UP.image_of_unitor(3) ide_f by presburger
             qed
             moreover have "(S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> (src f))) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f)) =
                            S.UP \<r>[f]"
             proof -
               have "S.UP \<r>[f] \<cdot>\<^sub>S S.\<Phi> (f, src f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S UP.\<Psi> (src f)) = S.UP f"
                 using UP.runit_coherence [of f] S.strict_runit by simp
               moreover have "S.iso (S.\<Phi> (f, src f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S UP.\<Psi> (src f)))"
                 using UP.\<Psi>_char UP.\<Phi>_components_are_iso VV.arr_char S.UP_map\<^sub>0_obj
                 apply (intro S.isos_compose S.seqI)
                 by simp_all
               ultimately have
                 "S.UP \<r>[f] = S.UP f \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S UP.\<Psi> (src f)))"
                 using S.invert_side_of_triangle(2)
                         [of "S.UP f" "S.UP \<r>[f]" "S.\<Phi> (f, src f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S UP.\<Psi> (src f))"]
                       ideD(1) ide_f by blast
               thus ?thesis
                 using ide_f UP.image_of_unitor(2) [of f] by argo
             qed
             ultimately show ?thesis
               using S.comp_assoc by simp
          qed
          also have "... = S.UP (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f])"
            by simp
          finally have "S.UP ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) = S.UP (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f])"
            by simp
          moreover have "par ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f])"
          proof -
            have "\<guillemotleft>(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) : f \<star> src f \<Rightarrow> trg f \<star> f\<guillemotright>"
              using E''.triangle_in_hom(1) by simp
            moreover have "\<guillemotleft>\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] : f \<star> src f \<Rightarrow> trg f \<star> f\<guillemotright>" by auto
            ultimately show ?thesis
              by (metis in_homE)
          qed
          ultimately show ?thesis
            using UP.is_faithful by blast
        qed
        thus "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
          using E''.triangle_left_implies_right by simp
      qed
      show ?thesis
        using E''.adjoint_equivalence_in_bicategory_axioms E''.adjunction_in_bicategory_axioms
             adjunction_unit_determines_counit adjoint_equivalence_in_bicategory_def
        by metis
    qed

    lemma equivalence_map_extends_to_adjoint_equivalence:
    assumes "equivalence_map f"
    shows "\<exists>g \<eta> \<epsilon>. adjoint_equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
    proof -
      obtain g \<eta> \<epsilon>' where E: "equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>'"
        using assms equivalence_map_def by auto
      interpret E: equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>'
        using E by auto
      obtain \<epsilon> where A: "adjoint_equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using assms equivalence_refines_to_adjoint_equivalence [of f g \<eta>]
              E.antipar E.unit_is_iso E.unit_in_hom by auto
      show ?thesis
        using E A by blast
    qed

  end

  subsection "Uniqueness of Adjoints"

  text \<open>
    Left and right adjoints determine each other up to isomorphism.
  \<close>

  context strict_bicategory
  begin

    lemma left_adjoint_determines_right_up_to_iso:
    assumes "adjoint_pair f g" and "adjoint_pair f g'"
    shows "g \<cong> g'"
    proof -
      obtain \<eta> \<epsilon> where A: "adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using assms adjoint_pair_def by auto
      interpret A: adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using A by auto
      interpret A: adjunction_in_strict_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon> ..
      obtain \<eta>' \<epsilon>' where A': "adjunction_in_bicategory V H \<a> \<i> src trg f g' \<eta>' \<epsilon>'"
        using assms adjoint_pair_def by auto
      interpret A': adjunction_in_bicategory V H \<a> \<i> src trg f g' \<eta>' \<epsilon>'
        using A' by auto
      interpret A': adjunction_in_strict_bicategory V H \<a> \<i> src trg f g' \<eta>' \<epsilon>' ..
      let ?\<phi> = "A'.trnl\<^sub>\<eta> g \<epsilon>"
      have "\<guillemotleft>?\<phi>: g \<Rightarrow> g'\<guillemotright>"
        using A'.trnl\<^sub>\<eta>_eq A'.adjoint_transpose_left(1) [of "trg f" g] A.antipar A'.antipar
              hcomp_arr_obj
        by auto
      moreover have "iso ?\<phi>"
      proof (intro isoI)
        let ?\<psi> = "A.trnl\<^sub>\<eta> g' \<epsilon>'"
        show "inverse_arrows ?\<phi> ?\<psi>"
        proof
          show "ide (?\<phi> \<cdot> ?\<psi>)"
          proof -
            have 1: "ide (trg f) \<and> trg (trg f) = trg f"
              by simp
            have "?\<phi> \<cdot> ?\<psi> = (g' \<star> \<epsilon>) \<cdot> ((\<eta>' \<star> g) \<cdot> (g \<star> \<epsilon>')) \<cdot> (\<eta> \<star> g')"
              using 1 A.antipar A'.antipar A.trnl\<^sub>\<eta>_eq [of "trg f" g' \<epsilon>']
                    A'.trnl\<^sub>\<eta>_eq [of "trg f" g \<epsilon>] comp_assoc A.counit_in_hom A'.counit_in_hom
              by simp
            also have "... = ((g' \<star> \<epsilon>) \<cdot> (g' \<star> f \<star> g \<star> \<epsilon>')) \<cdot> ((\<eta>' \<star> g \<star> f \<star> g') \<cdot> (\<eta> \<star> g'))"
            proof -
              have "(\<eta>' \<star> g) \<cdot> (g \<star> \<epsilon>') = (\<eta>' \<star> g \<star> trg f) \<cdot> (src f \<star> g \<star> \<epsilon>')"
                using A.antipar A'.antipar hcomp_arr_obj hcomp_obj_arr [of "src f" "g \<star> \<epsilon>'"]
                      hseqI'
                by (metis A'.counit_simps(1) A'.counit_simps(5) A.ide_right ideD(1)
                    obj_trg trg_hcomp)
              also have "... = \<eta>' \<star> g \<star> \<epsilon>'"
                using A.antipar A'.antipar interchange [of \<eta>' "src f" "g \<star> trg f" "g \<star> \<epsilon>'"]
                      whisker_left comp_arr_dom comp_cod_arr
                by simp
              also have "... = ((g' \<star> f) \<star> g \<star> \<epsilon>') \<cdot> (\<eta>' \<star> g \<star> (f \<star> g'))"
                using A.ide_left A.ide_right A'.ide_right A.antipar A'.antipar
                      A'.unit_in_hom A'.counit_in_hom interchange whisker_left
                      comp_arr_dom comp_cod_arr
                by (metis A'.counit_simps(1-2,5) A'.unit_simps(1,3) hseqI' ide_char)
              also have "... = (g' \<star> f \<star> g \<star> \<epsilon>') \<cdot> (\<eta>' \<star> g \<star> f \<star> g')"
                using hcomp_assoc by simp
              finally show ?thesis
                using comp_assoc by simp
            qed
            also have "... = (g' \<star> \<epsilon>') \<cdot> ((g' \<star> (\<epsilon> \<star> f) \<star> g') \<cdot> (g' \<star> (f \<star> \<eta>) \<star> g')) \<cdot> (\<eta>' \<star> g')"
            proof -
              have "(g' \<star> \<epsilon>) \<cdot> (g' \<star> f \<star> g \<star> \<epsilon>') = (g' \<star> \<epsilon>') \<cdot> (g' \<star> \<epsilon> \<star> f \<star> g')"
              proof -
                have "(g' \<star> \<epsilon>) \<cdot> (g' \<star> f \<star> g \<star> \<epsilon>') = g' \<star> \<epsilon> \<star> \<epsilon>'"
                proof -
                  have "\<epsilon> \<cdot> (f \<star> g \<star> \<epsilon>') = \<epsilon> \<star> \<epsilon>'"
                    using A.ide_left A.ide_right A.antipar A'.antipar hcomp_arr_obj comp_arr_dom
                      comp_cod_arr interchange obj_src trg_src
                    by (metis A'.counit_simps(1,3) A.counit_simps(1-2,4) hcomp_assoc)
                  thus ?thesis
                    using A.antipar A'.antipar whisker_left [of g' \<epsilon> "f \<star> g \<star> \<epsilon>'"]
                    by (simp add: hcomp_assoc)
                qed
                also have "... = (g' \<star> \<epsilon>') \<cdot> (g' \<star> \<epsilon> \<star> f \<star> g')"
                proof -
                  have "\<epsilon> \<star> \<epsilon>' = \<epsilon>' \<cdot> (\<epsilon> \<star> f \<star> g')"
                    using A.ide_left A.ide_right A'.ide_right A.antipar A'.antipar
                          hcomp_obj_arr hcomp_arr_obj comp_arr_dom comp_cod_arr interchange
                          obj_src trg_src
                    by (metis A'.counit_simps(1-2,5) A.counit_simps(1,3-4) arr_cod
                        not_arr_null seq_if_composable)
                  thus ?thesis
                    using A.ide_left A.ide_right A'.ide_right A.antipar A'.antipar
                          whisker_left
                    by (metis A'.counit_simps(1,5) A.counit_simps(1,4) hseqI')
                qed
                finally show ?thesis by simp
              qed
              moreover have "(\<eta>' \<star> g \<star> f \<star> g') \<cdot> (\<eta> \<star> g') = (g' \<star> f \<star> \<eta> \<star> g') \<cdot> (\<eta>' \<star> g')"
              proof -
                have "(\<eta>' \<star> g \<star> f \<star> g') \<cdot> (\<eta> \<star> g') = \<eta>' \<star> \<eta> \<star> g'"
                proof -
                  have "(\<eta>' \<star> g \<star> f) \<cdot> \<eta> = \<eta>' \<star> \<eta>"
                    using A.ide_left A.ide_right A.antipar A'.antipar A'.unit_in_hom hcomp_arr_obj
                          interchange comp_arr_dom comp_cod_arr
                    by (metis A'.unit_simps(1-2,4) A.unit_simps(1,3,5) hcomp_obj_arr obj_trg)
                  thus ?thesis
                    using A.antipar A'.antipar whisker_right [of g' "\<eta>' \<star> g \<star> f" \<eta>]
                    by (simp add: hcomp_assoc)
                qed
                also have "... = (g' \<star> f \<star> \<eta> \<star> g') \<cdot> (\<eta>' \<star> g')"
                proof -
                  have "\<eta>' \<star> \<eta> = (g' \<star> f \<star> \<eta>) \<cdot> \<eta>'"
                    using A.ide_left A.ide_right A.antipar A'.antipar A'.unit_in_hom hcomp_arr_obj
                          comp_arr_dom comp_cod_arr hcomp_assoc interchange
                    by (metis A'.unit_simps(1,3-4) A.unit_simps(1-2) obj_src)
                  thus ?thesis
                    using A.ide_left A.ide_right A.antipar A'.antipar A'.unit_in_hom hcomp_arr_obj
                          whisker_right [of g' "g' \<star> f \<star> \<eta>" \<eta>']
                    by (metis A'.ide_right A'.unit_simps(1,4) A.unit_simps(1,5)
                        hseqI' hcomp_assoc)
                qed
                finally show ?thesis by simp
              qed
              ultimately show ?thesis
                using comp_assoc hcomp_assoc by simp
            qed
            also have "... = (g' \<star> \<epsilon>') \<cdot> ((g' \<star> f) \<star> g') \<cdot> (\<eta>' \<star> g')"
            proof -
              have "(g' \<star> (\<epsilon> \<star> f) \<star> g') \<cdot> (g' \<star> (f \<star> \<eta>) \<star> g') = g' \<star> f \<star> g'"
              proof -
                have "(g' \<star> (\<epsilon> \<star> f) \<star> g') \<cdot> (g' \<star> (f \<star> \<eta>) \<star> g') =
                      g' \<star> ((\<epsilon> \<star> f) \<star> g') \<cdot> ((f \<star> \<eta>) \<star> g')"
                  using A.ide_left A.ide_right A.antipar A'.antipar A'.unit_in_hom
                        A'.counit_in_hom whisker_left [of g' "(\<epsilon> \<star> f) \<star> g'" "(f \<star> \<eta>) \<star> g'"]
                  by (metis A'.ide_right A.triangle_left hseqI' ideD(1) whisker_right)
                also have "... = g' \<star> (\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>) \<star> g'"
                  using A.antipar A'.antipar whisker_right [of g' "\<epsilon> \<star> f" "f \<star> \<eta>"]
                  by (simp add: A.triangle_left)
                also have "... = g' \<star> f \<star> g'"
                  using A.triangle_left by simp
                finally show ?thesis by simp
              qed
              thus ?thesis
                using hcomp_assoc by simp
            qed
            also have "... = (g' \<star> \<epsilon>') \<cdot> (\<eta>' \<star> g')"
              using A.antipar A'.antipar A'.unit_in_hom A'.counit_in_hom comp_cod_arr
              by (metis A'.ide_right A'.triangle_in_hom(2) A.ide_left arrI assoc_is_natural_2
                  ide_char seqE strict_assoc)
            also have "... = g'"
              using A'.triangle_right by simp
            finally have "?\<phi> \<cdot> ?\<psi> = g'" by simp
            thus ?thesis by simp
          qed
          show "ide (?\<psi> \<cdot> ?\<phi>)"
          proof -
            have 1: "ide (trg f) \<and> trg (trg f) = trg f"
              by simp
            have "?\<psi> \<cdot> ?\<phi> = (g \<star> \<epsilon>') \<cdot> ((\<eta> \<star> g') \<cdot> (g' \<star> \<epsilon>)) \<cdot> (\<eta>' \<star> g)"
              using A.antipar A'.antipar A'.trnl\<^sub>\<eta>_eq [of "trg f" g \<epsilon>]
                    A.trnl\<^sub>\<eta>_eq [of "trg f" g' \<epsilon>'] comp_assoc A.counit_in_hom A'.counit_in_hom
              by simp
            also have "... = ((g \<star> \<epsilon>') \<cdot> (g \<star> f \<star> g' \<star> \<epsilon>)) \<cdot> ((\<eta> \<star> g' \<star> f \<star> g) \<cdot> (\<eta>' \<star> g))"
            proof -
              have "(\<eta> \<star> g') \<cdot> (g' \<star> \<epsilon>) = (\<eta> \<star> g' \<star> trg f) \<cdot> (src f \<star> g' \<star> \<epsilon>)"
                using A.antipar A'.antipar hcomp_arr_obj hcomp_obj_arr hseqI'
                by (metis A'.ide_right A.unit_simps(1,4) hcomp_assoc hcomp_obj_arr
                    ideD(1) obj_src)
              also have "... = \<eta> \<star> g' \<star> \<epsilon>"
                using A.ide_left A.ide_right A'.ide_right A.antipar A'.antipar A.unit_in_hom
                      A.counit_in_hom interchange
                by (metis "1" A.counit_simps(5) A.unit_simps(4) hseqI' ide_def ide_in_hom(2)
                    not_arr_null seqI' src.preserves_ide)
              also have "... = ((g \<star> f) \<star> g' \<star> \<epsilon>) \<cdot> (\<eta> \<star> g' \<star> (f \<star> g))"
                using A'.ide_right A'.antipar interchange ide_char comp_arr_dom comp_cod_arr hseqI'
                by (metis A.counit_simps(1-2,5) A.unit_simps(1,3))
              also have "... = (g \<star> f \<star> g' \<star> \<epsilon>) \<cdot> (\<eta> \<star> g' \<star> f \<star> g)"
                using hcomp_assoc by simp
              finally show ?thesis
                using comp_assoc by simp
            qed
            also have "... = (g \<star> \<epsilon>) \<cdot> ((g \<star> (\<epsilon>' \<star> f) \<star> g) \<cdot> (g \<star> (f \<star> \<eta>') \<star> g)) \<cdot> (\<eta> \<star> g)"
            proof -
              have "(g \<star> \<epsilon>') \<cdot> (g \<star> f \<star> g' \<star> \<epsilon>) = (g \<star> \<epsilon>) \<cdot> (g \<star> \<epsilon>' \<star> f \<star> g)"
              proof -
                have "(g \<star> \<epsilon>') \<cdot> (g \<star> f \<star> g' \<star> \<epsilon>) = g \<star> \<epsilon>' \<star> \<epsilon>"
                proof -
                  have "\<epsilon>' \<cdot> (f \<star> g' \<star> \<epsilon>) = \<epsilon>' \<star> \<epsilon>"
                    using A.ide_left A.ide_right A'.ide_right A.antipar A'.antipar hcomp_arr_obj
                          comp_arr_dom comp_cod_arr interchange obj_src trg_src hcomp_assoc
                    by (metis A.counit_simps(1,3) A'.counit_simps(1-2,4))
                  thus ?thesis
                    using A.antipar A'.antipar whisker_left [of g \<epsilon>' "f \<star> g' \<star> \<epsilon>"]
                    by (simp add: hcomp_assoc)
                qed
                also have "... = (g \<star> \<epsilon>) \<cdot> (g \<star> \<epsilon>' \<star> f \<star> g)"
                proof -
                  have "\<epsilon>' \<star> \<epsilon> = \<epsilon> \<cdot> (\<epsilon>' \<star> f \<star> g)"
                    using A.ide_left A.ide_right A'.ide_right A.antipar A'.antipar hcomp_obj_arr
                          hcomp_arr_obj comp_arr_dom comp_cod_arr interchange obj_src trg_src
                    by (metis A.counit_simps(1-2,5) A'.counit_simps(1,3-4)
                        arr_cod not_arr_null seq_if_composable)
                  thus ?thesis
                    using A.ide_left A.ide_right A'.ide_right A.antipar A'.antipar
                          whisker_left
                    by (metis A.counit_simps(1,5) A'.counit_simps(1,4) hseqI')
                qed
                finally show ?thesis by simp
              qed
              moreover have "(\<eta> \<star> g' \<star> f \<star> g) \<cdot> (\<eta>' \<star> g) = (g \<star> f \<star> \<eta>' \<star> g) \<cdot> (\<eta> \<star> g)"
              proof -
                have "(\<eta> \<star> g' \<star> f \<star> g) \<cdot> (\<eta>' \<star> g) = \<eta> \<star> \<eta>' \<star> g"
                proof -
                  have "(\<eta> \<star> g' \<star> f) \<cdot> \<eta>' = \<eta> \<star> \<eta>'"
                    using A.antipar A'.antipar A.unit_in_hom hcomp_arr_obj
                          comp_arr_dom comp_cod_arr hcomp_obj_arr interchange
                    by (metis A'.unit_simps(1,3,5) A.unit_simps(1-2,4) obj_trg)
                  thus ?thesis
                    using A.antipar A'.antipar whisker_right [of g "\<eta> \<star> g' \<star> f" \<eta>']
                    by (simp add: hcomp_assoc)
                qed
                also have "... = ((g \<star> f) \<star> \<eta>' \<star> g) \<cdot> (\<eta> \<star> src f \<star> g)"
                  using A.ide_left A.ide_right A'.ide_right A.antipar A'.antipar A.unit_in_hom
                        A'.unit_in_hom comp_arr_dom comp_cod_arr interchange
                  by (metis A'.unit_simps(1-2,4) A.unit_simps(1,3) hseqI' ide_char)
                also have "... = (g \<star> f \<star> \<eta>' \<star> g) \<cdot> (\<eta> \<star> g)"
                  using A.antipar A'.antipar hcomp_assoc
                  by (simp add: hcomp_obj_arr)
                finally show ?thesis by simp
              qed
              ultimately show ?thesis
                using comp_assoc hcomp_assoc by simp
            qed
            also have "... = (g \<star> \<epsilon>) \<cdot> ((g \<star> f) \<star> g) \<cdot> (\<eta> \<star> g)"
            proof -
              have "(g \<star> (\<epsilon>' \<star> f) \<star> g) \<cdot> (g \<star> (f \<star> \<eta>') \<star> g) = g \<star> f \<star> g"
              proof -
                have "(g \<star> (\<epsilon>' \<star> f) \<star> g) \<cdot> (g \<star> (f \<star> \<eta>') \<star> g) =
                      g \<star> ((\<epsilon>' \<star> f) \<star> g) \<cdot> ((f \<star> \<eta>') \<star> g)"
                  using A.ide_left A.ide_right A'.ide_right A.antipar A'.antipar A.unit_in_hom
                        A.counit_in_hom whisker_left
                  by (metis A'.triangle_left hseqI' ideD(1) whisker_right)
                also have "... = g \<star> (\<epsilon>' \<star> f) \<cdot> (f \<star> \<eta>') \<star> g"
                  using A.antipar A'.antipar whisker_right [of g "\<epsilon>' \<star> f" "f \<star> \<eta>'"]
                  by (simp add: A'.triangle_left)
                also have "... = g \<star> f \<star> g"
                  using A'.triangle_left by simp
                finally show ?thesis by simp
              qed
              thus ?thesis
                using hcomp_assoc by simp
            qed
            also have "... = (g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g)"
              using A.antipar A'.antipar A.unit_in_hom A.counit_in_hom comp_cod_arr
              by (metis A.ide_left A.ide_right A.triangle_in_hom(2) arrI assoc_is_natural_2
                  ide_char seqE strict_assoc)
            also have "... = g"
              using A.triangle_right by simp
            finally have "?\<psi> \<cdot> ?\<phi> = g" by simp
            moreover have "ide g"
              by simp
            ultimately show ?thesis by simp
          qed
        qed
      qed
      ultimately show ?thesis
        using isomorphic_def by auto
    qed

  end

  text \<open>
    We now use strictification to extend to arbitrary bicategories.
  \<close>

  context bicategory
  begin

    interpretation S: strictified_bicategory V H \<a> \<i> src trg ..

    notation S.vcomp  (infixr "\<cdot>\<^sub>S" 55)
    notation S.hcomp  (infixr "\<star>\<^sub>S" 53)
    notation S.in_hom  ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>S _\<guillemotright>")
    notation S.in_hhom  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>S _\<guillemotright>")

    interpretation UP: equivalence_pseudofunctor V H \<a> \<i> src trg
                          S.vcomp S.hcomp S.\<a> S.\<i> S.src S.trg S.UP S.\<Phi>
      using S.UP_is_equivalence_pseudofunctor by auto
    interpretation UP: pseudofunctor_into_strict_bicategory V H \<a> \<i> src trg
                          S.vcomp S.hcomp S.\<a> S.\<i> S.src S.trg S.UP S.\<Phi>
      ..
    interpretation UP: fully_faithful_functor V S.vcomp S.UP
      using S.UP_is_fully_faithful_functor by auto

    lemma left_adjoint_determines_right_up_to_iso:
    assumes "adjoint_pair f g" and "adjoint_pair f g'"
    shows "g \<cong> g'"
    proof -
      have 0: "ide g \<and> ide g'"
        using assms adjoint_pair_def adjunction_in_bicategory_def
              adjunction_data_in_bicategory_def adjunction_data_in_bicategory_axioms_def
        by metis
      have 1: "S.adjoint_pair (S.UP f) (S.UP g) \<and> S.adjoint_pair (S.UP f) (S.UP g')"
        using assms UP.preserves_adjoint_pair by simp
      obtain \<nu> where \<nu>: "\<guillemotleft>\<nu> : S.UP g \<Rightarrow>\<^sub>S S.UP g'\<guillemotright> \<and> S.iso \<nu>"
        using 1 S.left_adjoint_determines_right_up_to_iso S.isomorphic_def by blast
      obtain \<mu> where \<mu>: "\<guillemotleft>\<mu> : g \<Rightarrow> g'\<guillemotright> \<and> S.UP \<mu> = \<nu>"
        using 0 \<nu> UP.is_full [of g' g \<nu>] by auto
      have "\<guillemotleft>\<mu> : g \<Rightarrow> g'\<guillemotright> \<and> iso \<mu>"
        using \<mu> \<nu> UP.reflects_iso by auto
      thus ?thesis
        using isomorphic_def by auto
    qed

    lemma right_adjoint_determines_left_up_to_iso:
    assumes "adjoint_pair f g" and "adjoint_pair f' g"
    shows "f \<cong> f'"
    proof -
      obtain \<eta> \<epsilon> where A: "adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using assms adjoint_pair_def by auto
      interpret A: adjunction_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using A by auto
      obtain \<eta>' \<epsilon>' where A': "adjunction_in_bicategory V H \<a> \<i> src trg f' g \<eta>' \<epsilon>'"
        using assms adjoint_pair_def by auto
      interpret A': adjunction_in_bicategory V H \<a> \<i> src trg f' g \<eta>' \<epsilon>'
        using A' by auto
      interpret Cop: op_bicategory V H \<a> \<i> src trg ..
      interpret Aop: adjunction_in_bicategory V Cop.H Cop.\<a> \<i> Cop.src Cop.trg g f \<eta> \<epsilon>
        using A.antipar A.triangle_left A.triangle_right Cop.assoc_ide_simp
              Cop.lunit_ide_simp Cop.runit_ide_simp
        by (unfold_locales, auto)
      interpret Aop': adjunction_in_bicategory V Cop.H Cop.\<a> \<i> Cop.src Cop.trg g f' \<eta>' \<epsilon>'
        using A'.antipar A'.triangle_left A'.triangle_right Cop.assoc_ide_simp
              Cop.lunit_ide_simp Cop.runit_ide_simp
        by (unfold_locales, auto)
      show ?thesis
        using Aop.adjunction_in_bicategory_axioms Aop'.adjunction_in_bicategory_axioms
              Cop.left_adjoint_determines_right_up_to_iso Cop.adjoint_pair_def
        by blast
    qed

  end

  context chosen_right_adjoints
  begin

    lemma isomorphic_to_left_adjoint_implies_isomorphic_right_adjoint:
    assumes "is_left_adjoint f" and "f \<cong> h"
    shows "f\<^sup>* \<cong> h\<^sup>*"
    proof -
      have 1: "adjoint_pair f f\<^sup>*"
        using assms left_adjoint_extends_to_adjoint_pair by blast
      moreover have "adjoint_pair h f\<^sup>*"
        using assms 1 adjoint_pair_preserved_by_iso isomorphic_symmetric isomorphic_reflexive
        by (meson isomorphic_def right_adjoint_simps(1))
      thus ?thesis
        using left_adjoint_determines_right_up_to_iso left_adjoint_extends_to_adjoint_pair
        by blast
    qed

  end

  context bicategory
  begin

    lemma equivalence_is_adjoint:
    assumes "equivalence_map f"
    shows equivalence_is_left_adjoint: "is_left_adjoint f"
    and equivalence_is_right_adjoint: "is_right_adjoint f"
    proof -
      obtain g \<eta> \<epsilon> where fg: "adjoint_equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using assms equivalence_map_extends_to_adjoint_equivalence by blast
      interpret fg: adjoint_equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using fg by simp
      interpret gf: adjoint_equivalence_in_bicategory V H \<a> \<i> src trg g f \<open>inv \<epsilon>\<close> \<open>inv \<eta>\<close>
        using fg.dual_adjoint_equivalence by simp
      show "is_left_adjoint f"
        using fg.adjunction_in_bicategory_axioms adjoint_pair_def by auto
      show "is_right_adjoint f"
        using gf.adjunction_in_bicategory_axioms adjoint_pair_def by auto
    qed

    lemma right_adjoint_to_equivalence_is_equivalence:
    assumes "equivalence_map f" and "adjoint_pair f g"
    shows "equivalence_map g"
    proof -
      obtain \<eta> \<epsilon> where fg: "adjunction_in_bicategory (\<cdot>) (\<star>) \<a> \<i> src trg f g \<eta> \<epsilon>"
        using assms adjoint_pair_def by auto
      interpret fg: adjunction_in_bicategory \<open>(\<cdot>)\<close> \<open>(\<star>)\<close> \<a> \<i> src trg f g \<eta> \<epsilon>
        using fg by simp
      obtain g' \<phi> \<psi> where fg': "equivalence_in_bicategory (\<cdot>) (\<star>) \<a> \<i> src trg f g' \<phi> \<psi>"
        using assms equivalence_map_def by auto
      interpret fg': equivalence_in_bicategory \<open>(\<cdot>)\<close> \<open>(\<star>)\<close> \<a> \<i> src trg f g' \<phi> \<psi>
        using fg' by auto
      obtain \<psi>' where \<psi>': "adjoint_equivalence_in_bicategory (\<cdot>) (\<star>) \<a> \<i> src trg f g' \<phi> \<psi>'"
        using assms equivalence_refines_to_adjoint_equivalence [of f g' \<phi>]
              fg'.antipar fg'.unit_in_hom fg'.unit_is_iso
        by auto
      interpret \<psi>': adjoint_equivalence_in_bicategory \<open>(\<cdot>)\<close> \<open>(\<star>)\<close> \<a> \<i> src trg f g' \<phi> \<psi>'
        using \<psi>' by simp
      have 1: "g \<cong> g'"
        using fg.adjunction_in_bicategory_axioms \<psi>'.adjunction_in_bicategory_axioms
              left_adjoint_determines_right_up_to_iso adjoint_pair_def
        by blast
      obtain \<gamma> where \<gamma>: "\<guillemotleft>\<gamma> : g' \<Rightarrow> g\<guillemotright> \<and> iso \<gamma>"
        using 1 isomorphic_def isomorphic_symmetric by metis
      have "equivalence_in_bicategory (\<cdot>) (\<star>) \<a> \<i> src trg f g ((\<gamma> \<star> f) \<cdot> \<phi>) (\<psi>' \<cdot> (f \<star> inv \<gamma>))"
        using \<gamma> equivalence_preserved_by_iso_right \<psi>'.equivalence_in_bicategory_axioms by simp
      hence "equivalence_pair f g"
        using equivalence_pair_def by auto
      thus ?thesis
        using equivalence_pair_symmetric equivalence_pair_def equivalence_map_def by blast
    qed

    lemma left_adjoint_to_equivalence_is_equivalence:
    assumes "equivalence_map f" and "adjoint_pair g f"
    shows "equivalence_map g"
    proof -
      obtain \<eta> \<epsilon> where gf: "adjunction_in_bicategory (\<cdot>) (\<star>) \<a> \<i> src trg g f \<eta> \<epsilon>"
        using assms adjoint_pair_def by auto
      interpret gf: adjunction_in_bicategory \<open>(\<cdot>)\<close> \<open>(\<star>)\<close> \<a> \<i> src trg g f \<eta> \<epsilon>
        using gf by simp
      obtain g' where 1: "equivalence_pair g' f"
        using assms equivalence_map_def equivalence_pair_def equivalence_pair_symmetric
        by blast
      obtain \<phi> \<psi> where g'f: "equivalence_in_bicategory (\<cdot>) (\<star>) \<a> \<i> src trg g' f \<phi> \<psi>"
        using assms 1 equivalence_pair_def by auto
      interpret g'f: equivalence_in_bicategory \<open>(\<cdot>)\<close> \<open>(\<star>)\<close> \<a> \<i> src trg g' f \<phi> \<psi>
        using g'f by auto
      obtain \<psi>' where \<psi>': "adjoint_equivalence_in_bicategory (\<cdot>) (\<star>) \<a> \<i> src trg g' f \<phi> \<psi>'"
        using assms 1 equivalence_refines_to_adjoint_equivalence [of g' f \<phi>]
              g'f.antipar g'f.unit_in_hom g'f.unit_is_iso equivalence_pair_def
              equivalence_map_def
        by auto
      interpret \<psi>': adjoint_equivalence_in_bicategory \<open>(\<cdot>)\<close> \<open>(\<star>)\<close> \<a> \<i> src trg g' f \<phi> \<psi>'
        using \<psi>' by simp
      have 1: "g \<cong> g'"
        using gf.adjunction_in_bicategory_axioms \<psi>'.adjunction_in_bicategory_axioms
              right_adjoint_determines_left_up_to_iso adjoint_pair_def
        by blast
      obtain \<gamma> where \<gamma>: "\<guillemotleft>\<gamma> : g' \<Rightarrow> g\<guillemotright> \<and> iso \<gamma>"
        using 1 isomorphic_def isomorphic_symmetric by metis
      have "equivalence_in_bicategory (\<cdot>) (\<star>) \<a> \<i> src trg g f ((f \<star> \<gamma>) \<cdot> \<phi>) (\<psi>' \<cdot> (inv \<gamma> \<star> f))"
        using \<gamma> equivalence_preserved_by_iso_left \<psi>'.equivalence_in_bicategory_axioms by simp
      hence "equivalence_pair g f"
        using equivalence_pair_def by auto
      thus ?thesis
        using equivalence_pair_symmetric equivalence_pair_def equivalence_map_def by blast
    qed

    lemma equivalence_pair_is_adjoint_pair:
    assumes "equivalence_pair f g"
    shows "adjoint_pair f g"
    proof -
      obtain \<eta> \<epsilon> where \<eta>\<epsilon>: "equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using assms equivalence_pair_def by auto
      interpret \<eta>\<epsilon>: equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using \<eta>\<epsilon> by auto
      obtain \<epsilon>' where \<eta>\<epsilon>': "adjoint_equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>'"
        using \<eta>\<epsilon> equivalence_map_def \<eta>\<epsilon>.antipar \<eta>\<epsilon>.unit_in_hom \<eta>\<epsilon>.unit_is_iso
              \<eta>\<epsilon>.ide_right equivalence_refines_to_adjoint_equivalence [of f g \<eta>]
        by force
      interpret \<eta>\<epsilon>': adjoint_equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>'
        using \<eta>\<epsilon>' by auto
      show ?thesis
        using \<eta>\<epsilon>' adjoint_pair_def \<eta>\<epsilon>'.adjunction_in_bicategory_axioms by auto
    qed

    lemma equivalence_pair_isomorphic_right:
    assumes "equivalence_pair f g"
    shows "equivalence_pair f g' \<longleftrightarrow> g \<cong> g'"
    proof
      show "g \<cong> g' \<Longrightarrow> equivalence_pair f g'"
        using assms equivalence_pair_def isomorphic_def equivalence_preserved_by_iso_right
        by metis
      assume g': "equivalence_pair f g'"
      show "g \<cong> g'"
        using assms g' equivalence_pair_is_adjoint_pair left_adjoint_determines_right_up_to_iso
        by blast
    qed

    lemma equivalence_pair_isomorphic_left:
    assumes "equivalence_pair f g"
    shows "equivalence_pair f' g \<longleftrightarrow> f \<cong> f'"
    proof
      show "f \<cong> f' \<Longrightarrow> equivalence_pair f' g"
        using assms equivalence_pair_def isomorphic_def equivalence_preserved_by_iso_left
        by metis
      assume f': "equivalence_pair f' g"
      show "f \<cong> f'"
        using assms f' equivalence_pair_is_adjoint_pair right_adjoint_determines_left_up_to_iso
        by blast
    qed      

  end

end
