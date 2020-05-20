(*  Title:       CanonicalIsomorphisms
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Canonical Isomorphisms"

text \<open>
  In this section we develop some technology for working with canonical isomorphisms in a bicategory,
  which permits them to be specified simply by giving syntactic terms that evaluate to the
  domain and codomain, rather than often-cumbersome formulas expressed in terms of unitors and
  associators.
\<close>

theory CanonicalIsos
imports Coherence
begin

  context bicategory
  begin

    interpretation bicategorical_language ..
    interpretation E: self_evaluation_map V H \<a> \<i> src trg ..
    notation E.eval ("\<lbrace>_\<rbrace>")

    text \<open>
      The next definition defines \<open>can u t\<close>, which denotes the unique canonical isomorphism
      from \<open>\<lbrace>t\<rbrace>\<close> to \<open>\<lbrace>u\<rbrace>\<close>.  The ordering of the arguments of \<open>can\<close> has been chosen to be the
      opposite of what was used for \<open>hom\<close>.  Having the arguments to \<open>can\<close> this way makes it easier
      to see at a glance when canonical isomorphisms are composable.  It could probably be argued
      that \<open>hom\<close> should have been defined this way as well, but that choice is somewhat
      well-entrenched by now and the argument for \<open>can\<close> is stronger, as it denotes an arrow and
      therefore appears in expressions composed with other arrows, rather than just as a hypothesis
      or conclusion.
    \<close>

    definition can
    where "can u t \<equiv> \<lbrace>Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace>"

    subsection "Basic Properties"

    text \<open>
      The following develop basic properties of \<open>can\<close>.
    \<close>

    lemma can_in_hom [intro]:
    assumes "Ide t" and "Ide u" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
    shows "\<guillemotleft>can u t : \<lbrace>t\<rbrace> \<Rightarrow> \<lbrace>u\<rbrace>\<guillemotright>"
    proof -
      let ?v = "Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>"
      have 1: "Can ?v \<and> Dom ?v = t \<and> Cod ?v = u"
        using assms red_in_Hom Can_red Inv_in_Hom Can_Inv(1) by simp
      show "\<guillemotleft>can u t : \<lbrace>t\<rbrace> \<Rightarrow> \<lbrace>u\<rbrace>\<guillemotright>"
        unfolding can_def using 1 E.eval_in_hom Can_implies_Arr
        by (metis (no_types, lifting))
    qed

    lemma can_simps [simp]:
    assumes "Ide t" and "Ide u" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
    shows "arr (can u t)" and "dom (can u t) = \<lbrace>t\<rbrace>" and "cod (can u t) = \<lbrace>u\<rbrace>"
      using assms can_in_hom by auto

    lemma inverse_arrows_can:
    assumes "Ide t" and "Ide u" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
    shows "iso (can u t)" and "inverse_arrows (can u t) (can t u)"
    proof -
      let ?v = "Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>"
      have 1: "Can ?v \<and> Dom ?v = t \<and> Cod ?v = u"
        using assms red_in_Hom Can_red Inv_in_Hom Can_Inv(1) by simp
      show "iso (can u t)"
        unfolding can_def using 1 E.iso_eval_Can by blast
      show "inverse_arrows (can u t) (can t u)"
      proof (unfold can_def)
        show "inverse_arrows \<lbrace>Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace> \<lbrace>Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>\<rbrace>"
        proof
          show "ide (\<lbrace>Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>\<rbrace>)"
          proof -
            have "\<lbrace>Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>\<rbrace> = \<lbrace>(Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>) \<^bold>\<cdot> (Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>)\<rbrace>"
              by simp
            also have "... = \<lbrace>u\<rbrace>"
            proof (intro E.eval_eqI)
              show 2: "VPar ((Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>) \<^bold>\<cdot> Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>) u"
                using assms 1 red_in_Hom Inv_in_Hom Ide_implies_Can Can_Inv Can_implies_Arr
                      Can_red(1)
                by (simp add: Dom_Ide Cod_Ide)
              show "\<^bold>\<lfloor>(Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>) \<^bold>\<cdot> Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
              proof -
                have 3: "Can (Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>)"
                  using Arr.simps(4) Can.simps(4) Can_Inv(1) Can_red(1) 2 assms(1) assms(2)
                  by presburger
                have "VSeq (Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>) (Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>)"
                  using 2 Arr.simps(4) by blast
                hence "Can (Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>) \<and> Can (Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>) \<and>
                       Dom (Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>) = Cod (Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>)"
                  using 3 1 by metis
                thus ?thesis
                  by (metis (no_types) 2 Can.simps(4) Nmlize_Dom Dom_Ide Ide_Nmlize_Can
                      assms(2))
              qed
            qed
            finally have "\<lbrace>Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>\<rbrace> = \<lbrace>u\<rbrace>"
              by blast
            moreover have "ide \<lbrace>u\<rbrace>"
              using assms E.ide_eval_Ide by simp
            ultimately show ?thesis by simp
          qed
          show "ide (\<lbrace>Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace>)"
          proof -
            have "\<lbrace>Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace> = \<lbrace>(Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>) \<^bold>\<cdot> (Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>)\<rbrace>"
              by simp
            also have "... = \<lbrace>t\<rbrace>"
            proof (intro E.eval_eqI)
              show 2: "VPar ((Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>) \<^bold>\<cdot> Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>) t"
                using assms 1 red_in_Hom Inv_in_Hom Ide_implies_Can Can_Inv Can_implies_Arr
                      Can_red(1)
                by (simp add: Dom_Ide Cod_Ide)
              show "\<^bold>\<lfloor>(Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>) \<^bold>\<cdot> Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
                using assms 1 2
                by (metis (full_types) Arr.simps(4) Can.simps(4) Can_Inv(1) Can_red(1)
                    Nml_Nmlize(4) Dom_Ide Ide_Nmlize_Can)
            qed
            finally have "\<lbrace>Inv (t\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace> = \<lbrace>t\<rbrace>"
              by blast
            moreover have "ide \<lbrace>t\<rbrace>"
              using assms E.ide_eval_Ide by simp
            ultimately show ?thesis by simp
          qed
        qed
      qed
    qed

    lemma inv_can [simp]:
    assumes "Ide t" and "Ide u" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
    shows "inv (can u t) = can t u"
      using assms inverse_arrows_can by (simp add: inverse_unique)

    lemma vcomp_can [simp]:
    assumes "Ide t" and "Ide u" and "Ide v" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>" and "\<^bold>\<lfloor>u\<^bold>\<rfloor> = \<^bold>\<lfloor>v\<^bold>\<rfloor>"
    shows "can v u \<cdot> can u t = can v t"
    proof (unfold can_def)
      have "\<lbrace>Inv (v\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace> = \<lbrace>(Inv (v\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>) \<^bold>\<cdot> (Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>)\<rbrace>"
        using assms by simp
      also have "... = \<lbrace>Inv (v\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace>"
      proof (intro E.eval_eqI)
        show "VPar ((Inv (v\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>) \<^bold>\<cdot> Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>) (Inv (v\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>)"
          using assms red_in_Hom Inv_in_Hom Ide_implies_Can
          by (simp add: Can_red(1))
        show "\<^bold>\<lfloor>(Inv (v\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>) \<^bold>\<cdot> Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<^bold>\<rfloor> = \<^bold>\<lfloor>Inv (v\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<^bold>\<rfloor>"
          using assms Can_red(1) Nml_Nmlize(1) Nmlize_Inv Ide_Nmlize_Can
              Ide_implies_Can \<open>VPar ((Inv (v\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>) \<^bold>\<cdot> Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>) (Inv (v\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>)\<close>
          apply simp
          by (metis red_simps(4) Nmlize_red Dom_Cod VcompNml_Nml_Dom)
      qed
      finally show "\<lbrace>Inv (v\<^bold>\<down>) \<^bold>\<cdot> u\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace> = \<lbrace>Inv (v\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace>"
        by blast
    qed

    lemma hcomp_can [simp]:
    assumes "Ide t" and "Ide u" and "Ide v" and "Ide w" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>" and "\<^bold>\<lfloor>v\<^bold>\<rfloor> = \<^bold>\<lfloor>w\<^bold>\<rfloor>"
    and "Src t = Trg v" and "Src u = Trg w"
    shows "can u t \<star> can w v = can (u \<^bold>\<star> w) (t \<^bold>\<star> v)"
    proof (unfold can_def)
      have "\<lbrace>Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Inv (w\<^bold>\<down>) \<^bold>\<cdot> v\<^bold>\<down>\<rbrace> = \<lbrace>(Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>) \<^bold>\<star> (Inv (w\<^bold>\<down>) \<^bold>\<cdot> v\<^bold>\<down>)\<rbrace>"
        using assms by simp
      also have "... = \<lbrace>Inv ((u \<^bold>\<star> w)\<^bold>\<down>) \<^bold>\<cdot> (t \<^bold>\<star> v)\<^bold>\<down>\<rbrace>"
      proof (intro E.eval_eqI)
        show "VPar (Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down> \<^bold>\<star> Inv (w\<^bold>\<down>) \<^bold>\<cdot> v\<^bold>\<down>) (Inv ((u \<^bold>\<star> w)\<^bold>\<down>) \<^bold>\<cdot> (t \<^bold>\<star> v)\<^bold>\<down>)"
        proof -
          have "Arr (Inv ((u \<^bold>\<star> w)\<^bold>\<down>) \<^bold>\<cdot> (t \<^bold>\<star> v)\<^bold>\<down>)"
          proof -
            have "Ide (u \<^bold>\<star> w)"
              using assms by simp
            hence "Can ((u \<^bold>\<star> w)\<^bold>\<down>)"
              using assms Can_red by blast
            thus ?thesis
              using assms Can.simps(4) Can_Inv(1) Dom_Inv Can_implies_Arr Can_red(1)
                    red_simps(4) Nmlize.simps(3) Ide.simps(3)
              by presburger
          qed
          moreover have "Arr (Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down> \<^bold>\<star> Inv (w\<^bold>\<down>) \<^bold>\<cdot> v\<^bold>\<down>)"
            using assms red_in_Hom Inv_in_Hom Ide_implies_Can
            by (simp add: Can_red(1))
          moreover have "Dom (Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down> \<^bold>\<star> Inv (w\<^bold>\<down>) \<^bold>\<cdot> v\<^bold>\<down>) =
                         Dom (Inv ((u \<^bold>\<star> w)\<^bold>\<down>) \<^bold>\<cdot> (t \<^bold>\<star> v)\<^bold>\<down>)"
            using assms red_in_Hom Inv_in_Hom Ide_implies_Can
            by (metis (no_types, lifting) Nml_HcompD(3-4) Dom.simps(3-4) red.simps(3)
                red_Nml)
          moreover have "Cod (Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down> \<^bold>\<star> Inv (w\<^bold>\<down>) \<^bold>\<cdot> v\<^bold>\<down>) =
                         Cod (Inv ((u \<^bold>\<star> w)\<^bold>\<down>) \<^bold>\<cdot> (t \<^bold>\<star> v)\<^bold>\<down>)"
            using assms red_in_Hom Inv_in_Hom Ide_implies_Can red_Nml
            by (simp add: Can_red(1) Cod_Ide)
          ultimately show ?thesis by simp
        qed
        show "\<^bold>\<lfloor>Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down> \<^bold>\<star> Inv (w\<^bold>\<down>) \<^bold>\<cdot> v\<^bold>\<down>\<^bold>\<rfloor> = \<^bold>\<lfloor>Inv ((u \<^bold>\<star> w)\<^bold>\<down>) \<^bold>\<cdot> (t \<^bold>\<star> v)\<^bold>\<down>\<^bold>\<rfloor>"
          using assms Inv_in_Hom Ide_implies_Can Nmlize_Inv Ide_Nmlize_Can Can_red
                red2_Nml
          apply auto
          using VcompNml_HcompNml [of u w u w]
             apply (metis red_simps(4) Nml_HcompD(3-4) Nmlize_Nml red_simps(3) red_Nml)
            apply (metis Nml_HcompD(3-4) Nmlize.simps(3) Nmlize_Nml
              red_simps(3) Ide.simps(3) VcompNml_Nml_Dom red_Nml)
           apply (metis Can_red2(1) red_simps(4) Nml_HcompD(3-4) Nmlize.simps(3)
              Nmlize_Nml VcompNml_Cod_Nml red_Nml)
          using red2_Nml Nmlize_red2 Can_red2(1) Nmlize_Hcomp Dom_Ide Ide_implies_Arr
            VcompNml_Nml_Dom Nml_Nmlize(1) Nml_Nmlize(2) Nml_Nmlize(3)
            Nmlize.simps(3)
          by metis
      qed
      finally show "\<lbrace>Inv (u\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Inv (w\<^bold>\<down>) \<^bold>\<cdot> v\<^bold>\<down>\<rbrace> = \<lbrace>Inv ((u \<^bold>\<star> w)\<^bold>\<down>) \<^bold>\<cdot> (t \<^bold>\<star> v)\<^bold>\<down>\<rbrace>"
        by blast
    qed

    subsection "Introduction Rules"

    text \<open>
      To make the \<open>can\<close> notation useful, we need a way to introduce it.
      This is a bit tedious, because in general there can multiple \<open>can\<close>
      notations for the same isomorphism, and we have to use the right ones in the
      right contexts, otherwise we won't be able to compose them properly.
      Thankfully, we don't need the inverse versions of the theorems below,
      as they are easily provable from the non-inverse versions using \<open>inv_can\<close>.
    \<close>

    lemma canI_unitor_0:
    assumes "ide f"
    shows "\<l>[f] = can \<^bold>\<langle>f\<^bold>\<rangle> (\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>)"
    and "\<r>[f] = can \<^bold>\<langle>f\<^bold>\<rangle> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0)"
    proof -
      have "can \<^bold>\<langle>f\<^bold>\<rangle> (\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) = \<lbrace>\<^bold>\<l>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>]\<rbrace>"
        unfolding can_def using assms by (intro E.eval_eqI, simp_all)
      thus 1: "\<l>[f] = can \<^bold>\<langle>f\<^bold>\<rangle> (\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>)"
        using assms by (simp add: \<ll>_ide_simp)
      have "can \<^bold>\<langle>f\<^bold>\<rangle> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) = \<lbrace>\<^bold>\<r>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>]\<rbrace>"
        unfolding can_def using assms by (intro E.eval_eqI, simp_all)
      thus "\<r>[f] = can \<^bold>\<langle>f\<^bold>\<rangle> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0)"
        using assms by (simp add: \<rr>_ide_simp)
    qed

    lemma canI_unitor_1:
    assumes "obj a"
    shows "\<l>[a] = can \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 (\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0)"
    and "\<r>[a] = can \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 (\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0)"
    proof -
      have "can \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 (\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0) = \<lbrace>\<^bold>\<l>\<^bold>[\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0\<^bold>]\<rbrace>"
        unfolding can_def using assms by (intro E.eval_eqI, simp_all)
      thus 1: "\<l>[a] = can \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 (\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0)"
        using assms by (auto simp add: \<ll>_ide_simp)
      have "can \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 (\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0) = \<lbrace>\<^bold>\<r>\<^bold>[\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0\<^bold>]\<rbrace>"
        unfolding can_def using assms by (intro E.eval_eqI, simp_all)
      thus "\<r>[a] = can \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 (\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0)"
        using assms by (auto simp add: \<rr>_ide_simp)
    qed

    lemma canI_associator_0:
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "\<a>[f, g, h] = can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>)"
    proof -
      have "can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) = \<lbrace>\<^bold>\<a>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>h\<^bold>\<rangle>\<^bold>]\<rbrace>"
        unfolding can_def using assms by (intro E.eval_eqI, simp_all)
      thus "\<a>[f, g, h] = can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>)"
        using assms by (simp add: \<alpha>_def)
    qed

    lemma canI_associator_1:
    assumes "ide f" and "ide g" and "src f = trg g"
    shows "\<a>[trg f, f, g] = can (\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) ((\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>)"
    and "\<a>[f, src f, g] = can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>)"
    and "\<a>[f, g, src g] = can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src g\<^bold>\<rangle>\<^sub>0) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>src g\<^bold>\<rangle>\<^sub>0)"
    proof -
      show "\<a>[trg f, f, g] = can (\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) ((\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>)"
      proof -
        have "can (\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) ((\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) = \<lbrace>\<^bold>\<a>\<^bold>[\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>\<^bold>]\<rbrace>"
          unfolding can_def using assms by (intro E.eval_eqI, simp_all)
        thus ?thesis
          using assms \<alpha>_def by simp
      qed
      show "\<a>[f, src f, g] = can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>)"
      proof -
        have "can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) = \<lbrace>\<^bold>\<a>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>g\<^bold>\<rangle>\<^bold>]\<rbrace>"
          unfolding can_def using assms by (intro E.eval_eqI, simp_all)
        thus ?thesis
          using assms \<alpha>_def by simp
      qed
      show "\<a>[f, g, src g] = can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src g\<^bold>\<rangle>\<^sub>0) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>src g\<^bold>\<rangle>\<^sub>0)"
      proof -
        have "can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src g\<^bold>\<rangle>\<^sub>0) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>src g\<^bold>\<rangle>\<^sub>0) = \<lbrace>\<^bold>\<a>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>src g\<^bold>\<rangle>\<^sub>0\<^bold>]\<rbrace>"
          unfolding can_def using assms by (intro E.eval_eqI, simp_all)
        thus ?thesis
          using assms \<alpha>_def by simp
      qed
    qed

    lemma canI_associator_2:
    assumes "ide f"
    shows "\<a>[trg f, trg f, f] = can (\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) ((\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0) \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>)"
    and "\<a>[trg f, f, src f] = can (\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) ((\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0)"
    and "\<a>[f, src f, src f] = can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0)"
    proof -
      show "\<a>[trg f, trg f, f] = can (\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) ((\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0) \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>)"
      proof -
        have "can (\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) ((\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0) \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) = \<lbrace>\<^bold>\<a>\<^bold>[\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>f\<^bold>\<rangle>\<^bold>]\<rbrace>"
          unfolding can_def using assms by (intro E.eval_eqI, simp_all)
        thus ?thesis
          using assms \<alpha>_def by simp
      qed
      show "\<a>[trg f, f, src f] = can (\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) ((\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0)"
      proof -
        have "can (\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) ((\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) = \<lbrace>\<^bold>\<a>\<^bold>[\<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0\<^bold>]\<rbrace>"
          unfolding can_def using assms by (intro E.eval_eqI, simp_all)
        thus ?thesis
          using assms \<alpha>_def by simp
      qed
      show "\<a>[f, src f, src f] = can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0)"
      proof -
        have "can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) \<^bold>\<star> \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0) =
              \<lbrace>\<^bold>\<a>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>src f\<^bold>\<rangle>\<^sub>0\<^bold>]\<rbrace>"
          unfolding can_def using assms by (intro E.eval_eqI, simp_all)
        thus ?thesis
          using assms \<alpha>_def by simp
      qed
    qed

    lemma canI_associator_3:
    assumes "obj a"
    shows "\<a>[a, a, a] = can (\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0) ((\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0) \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0)"
    proof -
      have "can (\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0) ((\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0) \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0) = \<lbrace>\<^bold>\<a>\<^bold>[\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0\<^bold>]\<rbrace>"
        unfolding can_def using assms by (intro E.eval_eqI, simp_all)
      thus ?thesis
        using assms \<alpha>_def by auto
    qed

    lemma canI_associator_hcomp:
    assumes "ide f" and "ide g" and "ide h" and "ide k"
    and "src f = trg g" and "src g = trg h" and "src h = trg k"
    shows "\<a>[f \<star> g, h, k] = can ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>) (((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>)"
    and "\<a>[f, g \<star> h, k] = can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>)) \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>)"
    and "\<a>[f, g, h \<star> k] = can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>)"
    proof -
      show "\<a>[f \<star> g, h, k] = can ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>) (((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>)"
      proof -
        have "can ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>) (((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>) =
              (((f \<star> g) \<star> h \<star> k) \<cdot> (\<a>\<^sup>-\<^sup>1[f, g, h \<star> k] \<cdot> (f \<star> g \<star> h \<star> k)) \<cdot> (f \<star> g \<star> h \<star> k)) \<cdot>
                ((f \<star> g \<star> h \<star> k) \<cdot> (f \<star> (g \<star> h \<star> k) \<cdot> (g \<star> h \<star> k) \<cdot> \<a>[g, h, k]) \<cdot> \<a>[f, g \<star> h, k]) \<cdot>
                  (((f \<star> g \<star> h) \<cdot> (f \<star> g \<star> h) \<cdot> \<a>[f, g, h]) \<cdot> ((f \<star> g) \<star> h) \<star> k)"
          unfolding can_def using assms \<alpha>_def \<a>'_def \<alpha>'.map_ide_simp by simp
        also have "... = \<a>\<^sup>-\<^sup>1[f, g, h \<star> k] \<cdot> (f \<star> \<a>[g, h, k]) \<cdot> \<a>[f, g \<star> h, k] \<cdot> (\<a>[f, g, h] \<star> k)"
          using assms comp_arr_dom comp_cod_arr comp_assoc by simp
        also have "... = \<a>[f \<star> g, h, k]"
          using assms pentagon [of f g h k] invert_side_of_triangle(1) \<alpha>_def \<alpha>'.map_ide_simp
                assoc_simps(1,4-5) ideD(1) iso_assoc preserves_ide seqI
          by simp
        finally show ?thesis by simp
      qed
      show "\<a>[f, g \<star> h, k] = can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>)) \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>)"
      proof -
        have "can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>)) \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>) =
              ((f \<star> ((g \<star> h) \<star> k) \<cdot> (\<a>\<^sup>-\<^sup>1[g, h, k] \<cdot> (g \<star> h \<star> k)) \<cdot> (g \<star> h \<star> k)) \<cdot> (f \<star> g \<star> h \<star> k)) \<cdot>
                ((f \<star> g \<star> h \<star> k) \<cdot> (f \<star> (g \<star> h \<star> k) \<cdot> (g \<star> h \<star> k) \<cdot> \<a>[g, h, k]) \<cdot> \<a>[f, g \<star> h, k]) \<cdot>
                  ((f \<star> g \<star> h) \<star> k)"
          unfolding can_def using assms \<alpha>_def \<alpha>'.map_ide_simp \<a>'_def by simp
        also have "... = ((f \<star> \<a>\<^sup>-\<^sup>1[g, h, k]) \<cdot> (f \<star> \<a>[g, h, k])) \<cdot> \<a>[f, g \<star> h, k]"
          using assms comp_arr_dom comp_cod_arr comp_assoc by simp
        also have "... = \<a>[f, g \<star> h, k]"
          using assms comp_cod_arr whisker_left [of f "\<a>\<^sup>-\<^sup>1[g, h, k]" "\<a>[g, h, k]"]
                comp_assoc_assoc'
          by simp
        finally show ?thesis by simp
      qed
      show "\<a>[f, g, h \<star> k] = can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>)"
      proof -
        have "can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>) ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>k\<^bold>\<rangle>) =
              (f \<star> g \<star> h \<star> k) \<cdot> ((f \<star> g \<star> h \<star> k) \<cdot> (f \<star> g \<star> h \<star> k) \<cdot> \<a>[f, g, h \<star> k]) \<cdot> ((f \<star> g) \<star> h \<star> k)"
          unfolding can_def using assms \<alpha>_def \<alpha>'.map_ide_simp by simp
        also have "... = \<a>[f, g, h \<star> k]"
          using assms comp_arr_dom comp_cod_arr by simp
        finally show ?thesis by simp
      qed
    qed

    subsection "Rules for Eliminating `can'"

    text \<open>
      The following rules are used for replacing \<open>can\<close> in an expression by terms expressed
      using unit and associativity isomorphisms.  They are not really expressed in the form
      of elimination rules, so the names are perhaps a bit misleading.  They are typically
      applied as simplifications.
    \<close>

    lemma canE_unitor:
    assumes "Ide f"
    shows "can f (f \<^bold>\<star> Src f) = \<r>[\<lbrace>f\<rbrace>]"
    and "can f (Trg f \<^bold>\<star> f) = \<l>[\<lbrace>f\<rbrace>]"
    and "can (f \<^bold>\<star> Src f) f = \<r>\<^sup>-\<^sup>1[\<lbrace>f\<rbrace>]"
    and "can (Trg f \<^bold>\<star> f) f = \<l>\<^sup>-\<^sup>1[\<lbrace>f\<rbrace>]"
    proof -
      show 1: "can f (f \<^bold>\<star> Src f) = \<r>[\<lbrace>f\<rbrace>]"
      proof -
        have f: "\<not>Nml (f \<^bold>\<star> Src f)"
          using assms Nml_HcompD(5) is_Prim0_Src by blast
        have "can f (f \<^bold>\<star> Src f) = \<lbrace>Inv (f\<^bold>\<down>) \<^bold>\<cdot> (\<^bold>\<lfloor>f\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Src f\<^bold>\<rfloor>) \<^bold>\<cdot> (f\<^bold>\<down> \<^bold>\<star> Src f\<^bold>\<down>)\<rbrace>"
          using assms f can_def by simp
        also have "... = \<lbrace>\<^bold>\<r>\<^bold>[f\<^bold>]\<rbrace>"
        proof (intro E.eval_eqI)
          show "VPar (Inv (f\<^bold>\<down>) \<^bold>\<cdot> (\<^bold>\<lfloor>f\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Src f\<^bold>\<rfloor>) \<^bold>\<cdot> (f\<^bold>\<down> \<^bold>\<star> Src f\<^bold>\<down>)) \<^bold>\<r>\<^bold>[f\<^bold>]"
            using assms Nmlize_in_Hom red_in_Hom red2_in_Hom Inv_in_Hom Can_red Can_implies_Arr
                  Nml_Nmlize(1) Ide_implies_Can Nml_Src Nml_implies_Arr
                  HcompNml_Nml_Src Ide_Cod
            apply (simp add: Dom_Ide Cod_Ide)
            apply (intro conjI)
          proof -
            assume f: "Ide f"
            have 1: "Nml (Src f)"
            proof -
              have "Ide (Src f)"
                using f by simp
              thus ?thesis
                using f Obj_Src Nml_Nmlize(1) Nmlize_Src(2) Ide_implies_Arr
                by metis
            qed
            show "Arr (\<^bold>\<lfloor>f\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Src f\<^bold>\<rfloor>)"
              using f 1 Can_red2 Ide_Nmlize_Ide Nml_Nmlize by simp
            show "Dom (\<^bold>\<lfloor>f\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Src f\<^bold>\<rfloor>) = \<^bold>\<lfloor>f\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>Src f\<^bold>\<rfloor>"
              using f 1 Nml_Nmlize red2_in_Hom Ide_Nmlize_Ide by auto
            show "\<^bold>\<lfloor>f\<^bold>\<rfloor> = Cod (\<^bold>\<lfloor>f\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Src f\<^bold>\<rfloor>)"
            proof -
              have "Src \<^bold>\<lfloor>f\<^bold>\<rfloor> = Trg \<^bold>\<lfloor>Src f\<^bold>\<rfloor>"
                using f Nml_Nmlize by simp
              moreover have "\<^bold>\<lfloor>\<^bold>\<lfloor>f\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>Src f\<^bold>\<rfloor>\<^bold>\<rfloor> = \<^bold>\<lfloor>f\<^bold>\<rfloor>"
                using f 1 Nml_Nmlize Nmlize_Src HcompNml_Nml_Src Nml_Src
                by (auto simp add: HcompNml_Nml_Obj)
              thus ?thesis
                using f 1 Obj_Src red2_in_Hom [of "\<^bold>\<lfloor>f\<^bold>\<rfloor>" "\<^bold>\<lfloor>Src f\<^bold>\<rfloor>"] HcompNml_Nml_Src
                      Nml_Nmlize Ide_Nmlize_Ide
                by auto
            qed
          qed
          show "\<^bold>\<lfloor>Inv (f\<^bold>\<down>) \<^bold>\<cdot> (\<^bold>\<lfloor>f\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Src f\<^bold>\<rfloor>) \<^bold>\<cdot> (f\<^bold>\<down> \<^bold>\<star> Src f\<^bold>\<down>)\<^bold>\<rfloor> = \<^bold>\<lfloor>\<^bold>\<r>\<^bold>[f\<^bold>]\<^bold>\<rfloor>"
            using assms f HcompNml_Nml_Src Nml_Nmlize Can_red Nmlize_Hcomp
                  Nmlize_Inv Nmlize_Src(1) Nmlize_red Nmlize_red2
                  Ide_Nmlize_Can VcompNml_Nml_Ide red_Src
            apply (simp add: HcompNml_Nml_Obj)
          proof -
            assume f: "Ide f"
            have "\<^bold>\<lfloor>\<^bold>\<lfloor>f\<^bold>\<rfloor> \<^bold>\<Down> Src f\<^bold>\<rfloor> = \<^bold>\<lfloor>f\<^bold>\<rfloor>"
            proof -
              have "Obj (Src f)"
                using f Obj_Src by simp
              thus ?thesis
                using f apply (cases "Src f")
                by (simp_all add: Nml_Nmlize(1) Nml_Nmlize(2) Ide_Nmlize_Ide)
            qed
            thus "\<^bold>\<lfloor>f\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<lfloor>f\<^bold>\<rfloor> \<^bold>\<Down> Src f\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>f\<^bold>\<rfloor> = \<^bold>\<lfloor>f\<^bold>\<rfloor>"
              by (metis Cod_Inv Can_red(1) Cod.simps(4) Nmlize.simps(4)
                  Nmlize.simps(7) Nmlize_Vcomp_Cod_Arr red_simps(3)
                  \<open>VPar (Inv (f\<^bold>\<down>) \<^bold>\<cdot> (\<^bold>\<lfloor>f\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Src f\<^bold>\<rfloor>) \<^bold>\<cdot> (f\<^bold>\<down> \<^bold>\<star> Src f\<^bold>\<down>)) \<^bold>\<r>\<^bold>[f\<^bold>]\<close> f)
          qed
        qed
        also have "... = \<r>[\<lbrace>f\<rbrace>]"
          using assms E.eval_Runit_Ide by blast
        finally show ?thesis by simp
      qed
      show 2: "can f (Trg f \<^bold>\<star> f) = \<l>[\<lbrace>f\<rbrace>]"
      proof -
        have f: "\<not>Nml (Trg f \<^bold>\<star> f)"
          using assms by (metis Nml.simps(4) Nml_HcompD(6))
        have "can f (Trg f \<^bold>\<star> f) = \<lbrace>Inv (f\<^bold>\<down>) \<^bold>\<cdot> (\<^bold>\<lfloor>Trg f\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>f\<^bold>\<rfloor>) \<^bold>\<cdot> (Trg f\<^bold>\<down> \<^bold>\<star> f\<^bold>\<down>)\<rbrace>"
          using assms f can_def by simp
        also have "... = \<lbrace>\<^bold>\<l>\<^bold>[f\<^bold>]\<rbrace>"
        proof (intro E.eval_eqI)
          show "VPar (Inv (f\<^bold>\<down>) \<^bold>\<cdot> (\<^bold>\<lfloor>Trg f\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>f\<^bold>\<rfloor>) \<^bold>\<cdot> (Trg f\<^bold>\<down> \<^bold>\<star> f\<^bold>\<down>)) \<^bold>\<l>\<^bold>[f\<^bold>]"
            using assms Nmlize_in_Hom red_in_Hom red2_in_Hom Inv_in_Hom Can_red Can_implies_Arr
                  Nml_Nmlize(1) Ide_implies_Can Nml_Trg Nml_implies_Arr
                  HcompNml_Trg_Nml Ide_Cod Nmlize_Trg(1)
            apply (simp add: Dom_Ide Cod_Ide)
            apply (intro conjI)
          proof -
            assume f: "Ide f"
            have 1: "Nml (Trg f)"
            proof -
              have "Ide (Trg f)"
                using f by simp
              thus ?thesis
                using f Obj_Trg Nml_Nmlize(1) Nmlize_Trg(2) Ide_implies_Arr
                by metis
            qed
            show "Arr (Trg f \<^bold>\<Down> \<^bold>\<lfloor>f\<^bold>\<rfloor>)"
              using f 1 Can_red2 Ide_Nmlize_Ide Nml_Nmlize(1,3) by simp
            show "Dom (Trg f \<^bold>\<Down> \<^bold>\<lfloor>f\<^bold>\<rfloor>) = Trg f \<^bold>\<star> \<^bold>\<lfloor>f\<^bold>\<rfloor>"
              using f Obj_Trg 1 Nml_Nmlize(1,3) red2_in_Hom Ide_Nmlize_Ide by auto
            show "\<^bold>\<lfloor>f\<^bold>\<rfloor> = Cod (Trg f \<^bold>\<Down> \<^bold>\<lfloor>f\<^bold>\<rfloor>)"
            proof -
              have "Src (Trg f) = Trg \<^bold>\<lfloor>f\<^bold>\<rfloor>"
                using f Nml_Nmlize(3) by simp
              thus ?thesis
                using f 1 Obj_Trg HcompNml_Trg_Nml Nml_Nmlize(1) Ide_Nmlize_Ide by auto
            qed
          qed
          show "\<^bold>\<lfloor>Inv (f\<^bold>\<down>) \<^bold>\<cdot> (\<^bold>\<lfloor>Trg f\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>f\<^bold>\<rfloor>) \<^bold>\<cdot> (Trg f\<^bold>\<down> \<^bold>\<star> f\<^bold>\<down>)\<^bold>\<rfloor> = \<^bold>\<lfloor>\<^bold>\<l>\<^bold>[f\<^bold>]\<^bold>\<rfloor>"
            using assms f HcompNml_Nml_Src Nml_Nmlize Can_red Nmlize_Hcomp
                  Nmlize_Inv Nmlize_Trg(1) Nmlize_red Nmlize_red2
                  Ide_Nmlize_Can VcompNml_Nml_Ide red_Trg
            apply (simp add: HcompNml_Obj_Nml)
          proof -
            assume f: "Ide f"
            have "\<^bold>\<lfloor>Trg f \<^bold>\<Down> \<^bold>\<lfloor>f\<^bold>\<rfloor>\<^bold>\<rfloor> = \<^bold>\<lfloor>f\<^bold>\<rfloor>"
            proof -
              have "Obj (Trg f)"
                using f Obj_Trg by simp
              thus ?thesis
                using f apply (cases "Trg f")
                by (simp_all add: Nml_Nmlize(1) Nml_Nmlize(2) Ide_Nmlize_Ide)
            qed
            thus "\<^bold>\<lfloor>f\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Trg f \<^bold>\<Down> \<^bold>\<lfloor>f\<^bold>\<rfloor>\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>f\<^bold>\<rfloor> = \<^bold>\<lfloor>f\<^bold>\<rfloor>"
              by (metis Cod_Inv Can_red(1) Cod.simps(4) Nmlize.simps(4)
                  Nmlize.simps(5) Nmlize_Vcomp_Cod_Arr red_simps(3)
                  \<open>VPar (Inv (f\<^bold>\<down>) \<^bold>\<cdot> (\<^bold>\<lfloor>Trg f\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>f\<^bold>\<rfloor>) \<^bold>\<cdot> (Trg f\<^bold>\<down> \<^bold>\<star> f\<^bold>\<down>)) \<^bold>\<l>\<^bold>[f\<^bold>]\<close> f)
          qed
        qed
        also have "... = \<l>[\<lbrace>f\<rbrace>]"
          using assms E.eval_Lunit_Ide by blast
        finally show ?thesis by simp
      qed
      show "can (f \<^bold>\<star> Src f) f = \<r>\<^sup>-\<^sup>1[\<lbrace>f\<rbrace>]"
        using assms 1 inv_can inv_inv
        by (metis (no_types, lifting) Nml_Nmlize(1) Nmlize.simps(3)
            Nmlize_Src(1) HcompNml_Nml_Src Ide.simps(3) Ide_implies_Arr
            Obj_Src Obj_implies_Ide Trg_Src)
      show "can (Trg f \<^bold>\<star> f) f = \<l>\<^sup>-\<^sup>1[\<lbrace>f\<rbrace>]"
        using assms 2 inv_can inv_inv
        by (metis (no_types, lifting) Nml_Nmlize(1) Nmlize.simps(3)
            Nmlize_Trg(1) HcompNml_Trg_Nml Ide.simps(3) Ide_implies_Arr
            Obj_Trg Obj_implies_Ide Src_Trg)
    qed

    lemma canE_associator:
    assumes "Ide f" and "Ide g" and "Ide h" and "Src f = Trg g" and "Src g = Trg h"
    shows "can (f \<^bold>\<star> g \<^bold>\<star> h) ((f \<^bold>\<star> g) \<^bold>\<star> h) = \<a>[\<lbrace>f\<rbrace>, \<lbrace>g\<rbrace>, \<lbrace>h\<rbrace>]"
    and "can ((f \<^bold>\<star> g) \<^bold>\<star> h) (f \<^bold>\<star> g \<^bold>\<star> h) = \<a>\<^sup>-\<^sup>1[\<lbrace>f\<rbrace>, \<lbrace>g\<rbrace>, \<lbrace>h\<rbrace>]"
    proof -
      show "can (f \<^bold>\<star> g \<^bold>\<star> h) ((f \<^bold>\<star> g) \<^bold>\<star> h) = \<a>[\<lbrace>f\<rbrace>, \<lbrace>g\<rbrace>, \<lbrace>h\<rbrace>]"
      proof -
        have "can (f \<^bold>\<star> g \<^bold>\<star> h) ((f \<^bold>\<star> g) \<^bold>\<star> h) = \<lbrace>Inv ((f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> ((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>\<rbrace>"
          using can_def by simp
        also have "... = \<lbrace>\<^bold>\<a>\<^bold>[f, g, h\<^bold>]\<rbrace>"
        proof (intro E.eval_eqI)
          have 1: "Inv ((f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> ((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down> \<in> VHom ((f \<^bold>\<star> g) \<^bold>\<star> h) (f \<^bold>\<star> g \<^bold>\<star> h)"
            using assms Inv_in_Hom [of "(f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>"] Can_red [of "f \<^bold>\<star> g \<^bold>\<star> h"]
                  red_in_Hom [of "f \<^bold>\<star> g \<^bold>\<star> h"] red_in_Hom [of "(f \<^bold>\<star> g) \<^bold>\<star> h"]
                  Nmlize_Hcomp_Hcomp Nmlize_Hcomp_Hcomp'
                  Ide_implies_Arr Nml_HcompNml Nmlize_Nml Ide_HcompNml
            by auto
          show par: "VPar (Inv ((f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> ((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<a>\<^bold>[f, g, h\<^bold>]"
            using assms 1 Inv_in_Hom red_in_Hom Ide_in_Hom by simp
          show "\<^bold>\<lfloor>Inv ((f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> ((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>\<^bold>\<rfloor> = \<^bold>\<lfloor>\<^bold>\<a>\<^bold>[f, g, h\<^bold>]\<^bold>\<rfloor>"
          proof -
            have "\<^bold>\<lfloor>Inv ((f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> ((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>\<^bold>\<rfloor> = Dom \<^bold>\<lfloor>Inv ((f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> ((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>\<^bold>\<rfloor>"
            proof -
              have "Can (Inv ((f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> ((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>)"
                (* Here presburger depends on par being at the end, not after assms. *)
                using assms Nmlize_Inv Can_Inv
                      Arr.simps(10) Arr.simps(4) Can.simps(4) Can_red(1) Ide.simps(3)
                      Src.simps(3) Trg.simps(3) par
                by presburger
              hence "Ide \<^bold>\<lfloor>Inv ((f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> ((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>\<^bold>\<rfloor>"
                using Ide_Nmlize_Can by blast
              thus ?thesis
                using Ide_in_Hom Dom_Ide by presburger
            qed
            also have 6: "... = \<^bold>\<lfloor>(f \<^bold>\<star> g) \<^bold>\<star> h\<^bold>\<rfloor>"
              using 1 Nmlize_Dom [of "Inv ((f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> ((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>"]
              by (metis (mono_tags, lifting) mem_Collect_eq)
            also have 5: "... = Dom \<^bold>\<lfloor>\<^bold>\<a>\<^bold>[f, g, h\<^bold>]\<^bold>\<rfloor>"
              using assms 6 par Nmlize_Dom Nml_Nmlize(4) by metis
            also have "... = \<^bold>\<lfloor>\<^bold>\<a>\<^bold>[f, g, h\<^bold>]\<^bold>\<rfloor>"
              using assms 5 Ide_in_Hom by auto
            finally show ?thesis by simp
          qed
        qed
        also have "... = \<a>[\<lbrace>f\<rbrace>, \<lbrace>g\<rbrace>, \<lbrace>h\<rbrace>]"
          using assms E.eval_Assoc_Ide \<alpha>_def by fastforce
        finally show ?thesis by simp
      qed
      show "can ((f \<^bold>\<star> g) \<^bold>\<star> h) (f \<^bold>\<star> g \<^bold>\<star> h) = \<a>\<^sup>-\<^sup>1[\<lbrace>f\<rbrace>, \<lbrace>g\<rbrace>, \<lbrace>h\<rbrace>]"
      proof -
        have "can ((f \<^bold>\<star> g) \<^bold>\<star> h) (f \<^bold>\<star> g \<^bold>\<star> h) = \<lbrace>Inv (((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> (f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>\<rbrace>"
          using can_def by simp
        also have "... = \<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[f, g, h\<^bold>]\<rbrace>"
        proof (intro E.eval_eqI)
          have 1: "Inv (((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> (f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down> \<in> VHom (f \<^bold>\<star> g \<^bold>\<star> h) ((f \<^bold>\<star> g) \<^bold>\<star> h)"
            using assms Inv_in_Hom [of "((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>"] Can_red [of "(f \<^bold>\<star> g) \<^bold>\<star> h"]
                  red_in_Hom [of "(f \<^bold>\<star> g) \<^bold>\<star> h"] red_in_Hom [of "f \<^bold>\<star> g \<^bold>\<star> h"]
                  Nmlize_Hcomp_Hcomp Nmlize_Hcomp_Hcomp'
                  Ide_implies_Arr Nml_HcompNml Nmlize_Nml Ide_HcompNml
            by auto
          show par: "VPar (Inv (((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> (f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[f, g, h\<^bold>]"
            using assms 1 Inv_in_Hom red_in_Hom Ide_in_Hom by simp
          show "\<^bold>\<lfloor>Inv (((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> (f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>\<^bold>\<rfloor> = \<^bold>\<lfloor>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[f, g, h\<^bold>]\<^bold>\<rfloor>"
          proof -
            have "\<^bold>\<lfloor>Inv (((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> (f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>\<^bold>\<rfloor> = Dom \<^bold>\<lfloor>Inv (((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> (f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>\<^bold>\<rfloor>"
            proof -
              have "Can (Inv (((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> (f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>)"
                using assms Nmlize_Inv Can_Inv
                      Arr.simps(10) Arr.simps(4) Can.simps(4) Can_red(1) Ide.simps(3)
                      Src.simps(3) Trg.simps(3) par
                by presburger
              hence "Ide \<^bold>\<lfloor>Inv (((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> (f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>\<^bold>\<rfloor>"
                using Ide_Nmlize_Can by blast
              thus ?thesis
                using Ide_in_Hom Dom_Ide by presburger
            qed
            also have 6: "... = \<^bold>\<lfloor>f \<^bold>\<star> g \<^bold>\<star> h\<^bold>\<rfloor>"
              using 1 Nmlize_Dom [of "Inv (((f \<^bold>\<star> g) \<^bold>\<star> h)\<^bold>\<down>) \<^bold>\<cdot> (f \<^bold>\<star> g \<^bold>\<star> h)\<^bold>\<down>"]
              by (metis (mono_tags, lifting) mem_Collect_eq)
            also have 5: "... = Dom \<^bold>\<lfloor>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[f, g, h\<^bold>]\<^bold>\<rfloor>"
              using assms 6 par Nmlize_Dom Nml_Nmlize(4) by metis
            also have "... = \<^bold>\<lfloor>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[f, g, h\<^bold>]\<^bold>\<rfloor>"
              using assms 5 Ide_in_Hom by auto
            finally show ?thesis by simp
          qed
        qed
        also have "... = \<a>\<^sup>-\<^sup>1[\<lbrace>f\<rbrace>, \<lbrace>g\<rbrace>, \<lbrace>h\<rbrace>]"
          using assms E.eval_Assoc'_Ide by fastforce
        finally show ?thesis by simp
      qed
    qed

    lemma can_Ide_self:
    assumes "Ide t"
    shows "can t t = \<lbrace>t\<rbrace>"
    proof (unfold can_def)
      show "\<lbrace>Inv (t\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<rbrace> = \<lbrace>t\<rbrace>"
      proof (intro E.eval_eqI)
        show "VPar (Inv (t\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>) t"
          using assms red_in_Hom Inv_in_Hom Ide_implies_Can Can_Inv Can_red(1) Ide_in_Hom(2)
          by auto
        show "\<^bold>\<lfloor>Inv (t\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
          using assms red_in_Hom Inv_in_Hom Ide_implies_Can Cod_Inv
          by (metis (mono_tags, lifting) Can_red(1) Nml_Nmlize(1) Nmlize.simps(4)
              Nmlize_Inv Ide_Nmlize_Ide Nmlize_red Inv_Ide VcompNml_Ide_Nml
              \<open>VPar (Inv (t\<^bold>\<down>) \<^bold>\<cdot> t\<^bold>\<down>) t\<close>)
      qed
    qed

    subsection "Rules for Whiskering"

    lemma whisker_can_right_0:
    assumes "Ide t" and "Ide u" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>" and "ide f" and "Src t = \<^bold>\<langle>trg f\<^bold>\<rangle>\<^sub>0"
    shows "can u t \<star> f = can (u \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) (t \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>)"
    proof -
      have "f = can \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<langle>f\<^bold>\<rangle>"
        using assms can_Ide_self by simp
      thus ?thesis
        using assms Ide_implies_Arr hcomp_can
        by (metis Nml_Nmlize(2) Ide.simps(2) Trg.simps(2))
    qed

    lemma whisker_can_right_1:
    assumes "Ide t" and "Ide u" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>" and "obj a" and "Src t = \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0"
    shows "can u t \<star> a = can (u \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0) (t \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0)"
    proof -
      have "a = can \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0"
        using assms can_Ide_self by auto
      thus ?thesis
        using assms Ide_implies_Arr hcomp_can
        by (metis Nml_Nmlize(2) Ide.simps(1) Trg.simps(1))
    qed

    lemma whisker_can_left_0:
    assumes "Ide t" and "Ide u" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>" and "ide g" and "Trg t = \<^bold>\<langle>src g\<^bold>\<rangle>\<^sub>0"
    shows "g \<star> can u t = can (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> u) (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> t)"
    proof -
      have "g = can \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<langle>g\<^bold>\<rangle>"
        using assms can_Ide_self by simp
      thus ?thesis
        using assms Ide_implies_Arr hcomp_can
        by (metis Nml_Nmlize(3) Ide.simps(2) Src.simps(2))
    qed

    lemma whisker_can_left_1:
    assumes "Ide t" and "Ide u" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>" and "obj b" and "Trg t = \<^bold>\<langle>b\<^bold>\<rangle>\<^sub>0"
    shows "b \<star> can u t = can (\<^bold>\<langle>b\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> u) (\<^bold>\<langle>b\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> t)"
    proof -
      have "b = can \<^bold>\<langle>b\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>b\<^bold>\<rangle>\<^sub>0"
        using assms can_Ide_self by auto
      thus ?thesis
        using assms Ide_implies_Arr hcomp_can
        by (metis Nml_Nmlize(3) Ide.simps(1) Src.simps(1))
    qed

  end

end
