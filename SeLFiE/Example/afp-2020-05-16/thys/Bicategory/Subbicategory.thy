(*  Title:       Subbicategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Sub-Bicategories"

text \<open>
  In this section we give a construction of a sub-bicategory in terms of a predicate
  on the arrows of an ambient bicategory that has certain closure properties with respect
  to that bicategory.  While the construction given here is likely to be of general use,
  it is not the most general sub-bicategory construction that one could imagine,
  because it requires that the sub-bicategory actually contain the unit and associativity
  isomorphisms of the ambient bicategory.  Our main motivation for including this construction
  here is to apply it to exploit the fact that the sub-bicategory of endo-arrows of a fixed
  object is a monoidal category, which will enable us to transfer to bicategories a result
  about unit isomorphisms in monoidal categories.  
\<close>

theory Subbicategory
imports Bicategory
begin

  subsection "Construction"

  locale subbicategory =
    B: bicategory V H \<a>\<^sub>B \<i> src\<^sub>B trg\<^sub>B +
    subcategory V Arr
  for V :: "'a comp"                 (infixr "\<cdot>\<^sub>B" 55)
  and H :: "'a comp"                 (infixr "\<star>\<^sub>B" 55)
  and \<a>\<^sub>B :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"    ("\<a>\<^sub>B[_, _, _]")
  and \<i> :: "'a \<Rightarrow> 'a"                 ("\<i>[_]")
  and src\<^sub>B :: "'a \<Rightarrow> 'a"
  and trg\<^sub>B :: "'a \<Rightarrow> 'a"
  and Arr :: "'a \<Rightarrow> bool" +
  assumes src_closed: "Arr f \<Longrightarrow> Arr (src\<^sub>B f)"
  and trg_closed: "Arr f \<Longrightarrow> Arr (trg\<^sub>B f)"
  and hcomp_closed: "\<lbrakk> Arr f; Arr g; trg\<^sub>B f = src\<^sub>B g \<rbrakk> \<Longrightarrow> Arr (g \<star>\<^sub>B f)"
  and assoc_closed: "\<lbrakk> Arr f \<and> B.ide f; Arr g \<and> B.ide g; Arr h \<and> B.ide h;
                       src\<^sub>B f = trg\<^sub>B g; src\<^sub>B g = trg\<^sub>B h \<rbrakk> \<Longrightarrow> Arr (\<a>\<^sub>B f g h)"
  and assoc'_closed: "\<lbrakk> Arr f \<and> B.ide f; Arr g \<and> B.ide g; Arr h \<and> B.ide h;
                       src\<^sub>B f = trg\<^sub>B g; src\<^sub>B g = trg\<^sub>B h \<rbrakk> \<Longrightarrow> Arr (B.inv (\<a>\<^sub>B f g h))"
  and lunit_closed: "\<lbrakk> Arr f; B.ide f \<rbrakk> \<Longrightarrow> Arr (B.\<ll> f)"
  and lunit'_closed: "\<lbrakk> Arr f; B.ide f \<rbrakk> \<Longrightarrow> Arr (B.inv (B.\<ll> f))"
  and runit_closed: "\<lbrakk> Arr f; B.ide f \<rbrakk> \<Longrightarrow> Arr (B.\<rr> f)"
  and runit'_closed: "\<lbrakk> Arr f; B.ide f \<rbrakk> \<Longrightarrow> Arr (B.inv (B.\<rr> f))"
  begin

    notation B.in_hom           ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>B _\<guillemotright>")

    notation comp               (infixr "\<cdot>" 55)

    definition hcomp            (infixr "\<star>" 53)
    where "g \<star> f = (if Arr f \<and> Arr g \<and> trg\<^sub>B f = src\<^sub>B g then g \<star>\<^sub>B f else null)"

    definition src
    where "src \<mu> = (if Arr \<mu> then src\<^sub>B \<mu> else null)"

    definition trg
    where "trg \<mu> = (if Arr \<mu> then trg\<^sub>B \<mu> else null)"

    interpretation src: endofunctor \<open>(\<cdot>)\<close> src
      using src_def null_char inclusion arr_char src_closed trg_closed dom_closed cod_closed
      apply unfold_locales
          apply auto[4]
      by (metis B.src.preserves_comp_2 comp_char seq_char)

    interpretation trg: endofunctor \<open>(\<cdot>)\<close> trg
      using trg_def null_char inclusion arr_char src_closed trg_closed dom_closed cod_closed
      apply unfold_locales
          apply auto[4]
      by (metis B.trg.preserves_comp_2 comp_char seq_char)

    interpretation horizontal_homs \<open>(\<cdot>)\<close> src trg
      using src_def trg_def src.preserves_arr trg.preserves_arr null_char ide_char arr_char
            inclusion
      by (unfold_locales, simp_all)

    interpretation VxV: product_category \<open>(\<cdot>)\<close> \<open>(\<cdot>)\<close> ..
    interpretation VV: subcategory VxV.comp
        \<open>\<lambda>\<mu>\<nu>. arr (fst \<mu>\<nu>) \<and> arr (snd \<mu>\<nu>) \<and> src (fst \<mu>\<nu>) = trg (snd \<mu>\<nu>)\<close>
      using subcategory_VV by auto

    interpretation "functor" VV.comp \<open>(\<cdot>)\<close> \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu>\<close>
      using hcomp_def VV.arr_char src_def trg_def arr_char hcomp_closed dom_char cod_char
            VV.dom_char VV.cod_char
      apply unfold_locales
          apply auto[2]
    proof -
      fix f
      assume f: "VV.arr f"
      show "dom (fst f \<star> snd f) = fst (VV.dom f) \<star> snd (VV.dom f)"
      proof -
        have "dom (fst f \<star> snd f) = B.dom (fst f) \<star>\<^sub>B B.dom (snd f)"
        proof -
          have "dom (fst f \<star> snd f) = B.dom (fst f \<star> snd f)"
            using f dom_char
            by (simp add: arrI hcomp_closed hcomp_def)
          also have "... = B.dom (fst f) \<star>\<^sub>B B.dom (snd f)"
            using f
            by (metis (no_types, lifting) B.hcomp_simps(3) B.hseqI' VV.arrE arrE hcomp_def
                inclusion src_def trg_def)
          finally show ?thesis by blast
        qed
        also have "... = fst (VV.dom f) \<star> snd (VV.dom f)"
           using f VV.arr_char VV.dom_char arr_char hcomp_def B.seq_if_composable dom_closed
           by (simp, metis)
        finally show ?thesis by simp
      qed
      show "cod (fst f \<star> snd f) = fst (VV.cod f) \<star> snd (VV.cod f)"
      proof -
        have "cod (fst f \<star> snd f) = B.cod (fst f) \<star>\<^sub>B B.cod (snd f)"
          using f VV.arr_char arr_char cod_char hcomp_def src_def trg_def
                src_closed trg_closed hcomp_closed inclusion B.hseq_char arrE
          by auto
        also have "... = fst (VV.cod f) \<star> snd (VV.cod f)"
           using f VV.arr_char VV.cod_char arr_char hcomp_def B.seq_if_composable cod_closed
           by (simp, metis)
        finally show ?thesis by simp
      qed
      next
      fix f g
      assume fg: "VV.seq g f"
      show "fst (VV.comp g f) \<star> snd (VV.comp g f) = (fst g \<star> snd g) \<cdot> (fst f \<star> snd f)"
      proof -
        have "fst (VV.comp g f) \<star> snd (VV.comp g f) = fst g \<cdot> fst f \<star> snd g \<cdot> snd f"
          using fg VV.seq_char VV.comp_char VxV.comp_char VxV.not_Arr_Null
          by (metis (no_types, lifting) VxV.seqE prod.sel(1) prod.sel(2))
        also have "... = (fst g \<cdot>\<^sub>B fst f) \<star>\<^sub>B (snd g \<cdot>\<^sub>B snd f)"
          using fg comp_char hcomp_def VV.seq_char inclusion arr_char seq_char B.hseq_char
          by (metis (no_types, lifting) B.hseq_char' VxV.seq_char null_char)
        also have 1: "... = (fst g \<star>\<^sub>B snd g) \<cdot>\<^sub>B (fst f \<star>\<^sub>B snd f)"
        proof -
          have "src\<^sub>B (fst g) = trg\<^sub>B (snd g)"
            by (metis (no_types, lifting) VV.arrE VV.seq_char arr_char fg src_def trg_def)
          thus ?thesis
            using fg VV.seq_char VV.arr_char arr_char seq_char inclusion B.interchange
            by (meson VxV.seqE)
        qed
        also have "... = (fst g \<star> snd g) \<cdot> (fst f \<star> snd f)"
          using fg comp_char hcomp_def VV.seq_char VV.arr_char arr_char seq_char inclusion
                B.hseq_char' hcomp_closed src_def trg_def
          by (metis (no_types, lifting) 1)
        finally show ?thesis by auto
      qed
    qed

    interpretation horizontal_composition \<open>(\<cdot>)\<close> \<open>(\<star>)\<close> src trg
      using arr_char src_def trg_def src_closed trg_closed
      apply (unfold_locales)
      using hcomp_def inclusion not_arr_null by auto

    interpretation VxVxV: product_category \<open>(\<cdot>)\<close> VxV.comp ..
    interpretation VVV: subcategory VxVxV.comp
                          \<open>\<lambda>\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> VV.arr (snd \<tau>\<mu>\<nu>) \<and>
                          src (fst \<tau>\<mu>\<nu>) = trg (fst (snd \<tau>\<mu>\<nu>))\<close>
      using subcategory_VVV by auto

    interpretation HoHV: "functor" VVV.comp \<open>(\<cdot>)\<close> HoHV
      using functor_HoHV by auto
    interpretation HoVH: "functor" VVV.comp \<open>(\<cdot>)\<close> HoVH
      using functor_HoVH by auto

    abbreviation \<a>
    where "\<a> \<mu> \<nu> \<tau> \<equiv> if VVV.arr (\<mu>, \<nu>, \<tau>) then \<a>\<^sub>B \<mu> \<nu> \<tau> else null"

    abbreviation (input) \<alpha>\<^sub>S\<^sub>B
    where "\<alpha>\<^sub>S\<^sub>B \<mu>\<nu>\<tau> \<equiv> \<a> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>))"

    lemma assoc_closed':
    assumes "VVV.arr \<mu>\<nu>\<tau>"
    shows "Arr (\<alpha>\<^sub>S\<^sub>B \<mu>\<nu>\<tau>)"
    proof -
      have 1: "B.VVV.arr \<mu>\<nu>\<tau>"
        using assms VVV.arr_char VV.arr_char B.VVV.arr_char B.VV.arr_char arr_char
              src_def trg_def inclusion
        by auto
      show "Arr (\<alpha>\<^sub>S\<^sub>B \<mu>\<nu>\<tau>)"
      proof -
        have "Arr (\<alpha>\<^sub>S\<^sub>B \<mu>\<nu>\<tau>) =
              Arr ((fst \<mu>\<nu>\<tau> \<star>\<^sub>B fst (snd \<mu>\<nu>\<tau>) \<star>\<^sub>B snd (snd \<mu>\<nu>\<tau>)) \<cdot>\<^sub>B \<alpha>\<^sub>S\<^sub>B (B.VVV.dom \<mu>\<nu>\<tau>))"
          using assms B.\<alpha>_def 1 B.VVV.arr_char B.VV.arr_char B.VVV.dom_char B.VV.dom_char
                B.assoc_is_natural_1 [of "fst \<mu>\<nu>\<tau>" "fst (snd \<mu>\<nu>\<tau>)" "snd (snd \<mu>\<nu>\<tau>)"]
                VV.arr_char VVV.arr_char arr_dom src_dom trg_dom
          by auto
        also have "..."
        proof (intro comp_closed)
          show "Arr (fst \<mu>\<nu>\<tau> \<star>\<^sub>B fst (snd \<mu>\<nu>\<tau>) \<star>\<^sub>B snd (snd \<mu>\<nu>\<tau>))"
            using assms 1 B.VVV.arr_char B.VV.arr_char hcomp_closed
            by (metis (no_types, lifting) B.H.preserves_reflects_arr B.trg_hcomp
                VV.arr_char VVV.arrE arr_char)
          show "B.cod (\<a> (fst (B.VVV.dom \<mu>\<nu>\<tau>)) (fst (snd (B.VVV.dom \<mu>\<nu>\<tau>)))
                      (snd (snd (B.VVV.dom \<mu>\<nu>\<tau>)))) =
                B.dom (fst \<mu>\<nu>\<tau> \<star>\<^sub>B fst (snd \<mu>\<nu>\<tau>) \<star>\<^sub>B snd (snd \<mu>\<nu>\<tau>))"
            using assms 1 VVV.arr_char VV.arr_char B.VxVxV.dom_char
            apply simp
            by (metis (no_types, lifting) B.VV.arr_char B.VVV.arrE B.\<alpha>.preserves_reflects_arr
                B.assoc_is_natural_1 B.seqE arr_dom dom_char src_dom trg_dom)
          show "Arr (\<a> (fst (B.VVV.dom \<mu>\<nu>\<tau>)) (fst (snd (B.VVV.dom \<mu>\<nu>\<tau>)))
                    (snd (snd (B.VVV.dom \<mu>\<nu>\<tau>))))"
          proof -
            have "VVV.arr (B.VVV.dom \<mu>\<nu>\<tau>)"
              using 1 B.VVV.dom_char B.VVV.arr_char B.VV.arr_char VVV.arr_char VV.arr_char
              apply simp
              by (metis (no_types, lifting) VVV.arrE arr_dom assms dom_simp src_dom trg_dom)
            moreover have "Arr (\<a>\<^sub>B (B.dom (fst \<mu>\<nu>\<tau>)) (B.dom (fst (snd \<mu>\<nu>\<tau>)))
                               (B.dom (snd (snd \<mu>\<nu>\<tau>))))"
            proof -
              have "B.VVV.ide (B.VVV.dom \<mu>\<nu>\<tau>)"
                using 1 B.VVV.ide_dom by blast
              thus ?thesis
                using assms B.\<alpha>_def B.VVV.arr_char B.VV.arr_char B.VVV.ide_char B.VV.ide_char
                      dom_closed assoc_closed
                by (metis (no_types, lifting) "1" B.ide_dom B.src_dom B.trg_dom VV.arr_char
                    VVV.arrE arr_char)
            qed
            ultimately show ?thesis
              using 1 B.VVV.ide_dom assoc_closed B.VVV.dom_char
              apply simp
              by (metis (no_types, lifting) B.VV.arr_char B.VVV.arrE B.VVV.inclusion
                  B.VxV.dom_char B.VxVxV.arrE B.VxVxV.dom_char prod.sel(1) prod.sel(2))
          qed
        qed
        finally show ?thesis by blast
      qed
    qed

    lemma lunit_closed':
    assumes "Arr f"
    shows "Arr (B.\<ll> f)"
    proof -
      have 1: "arr f \<and> arr (B.\<ll> (B.dom f))"
        using assms arr_char lunit_closed dom_closed B.ide_dom inclusion by simp
      moreover have "B.dom f = B.cod (B.\<ll> (B.dom f))"
        using 1 arr_char B.\<ll>.preserves_cod inclusion by simp
      moreover have "B.\<ll> f = f \<cdot> B.\<ll> (B.dom f)"
        using assms 1 B.\<ll>.is_natural_1 inclusion comp_char arr_char by simp
      ultimately show ?thesis
        using arr_char comp_closed cod_char seqI by auto
    qed
      
    lemma runit_closed':
    assumes "Arr f"
    shows "Arr (B.\<rr> f)"
    proof -
      have 1: "arr f \<and> arr (B.\<rr> (B.dom f))"
        using assms arr_char runit_closed dom_closed B.ide_dom inclusion
        by simp
      moreover have "B.dom f = B.cod (B.\<rr> (B.dom f))"
        using 1 arr_char B.\<ll>.preserves_cod inclusion by simp
      moreover have "B.\<rr> f = f \<cdot> B.\<rr> (B.dom f)"
        using assms 1 B.\<rr>.is_natural_1 inclusion comp_char arr_char by simp
      ultimately show ?thesis
        using arr_char comp_closed cod_char seqI by auto
    qed

    interpretation natural_isomorphism VVV.comp \<open>(\<cdot>)\<close> HoHV HoVH \<alpha>\<^sub>S\<^sub>B
    proof
      fix \<mu>\<nu>\<tau>
      show "\<not> VVV.arr \<mu>\<nu>\<tau> \<Longrightarrow> \<alpha>\<^sub>S\<^sub>B \<mu>\<nu>\<tau> = null"
        by simp
      assume \<mu>\<nu>\<tau>: "VVV.arr \<mu>\<nu>\<tau>"
      have 1: "B.VVV.arr \<mu>\<nu>\<tau>"
        using \<mu>\<nu>\<tau> VVV.arr_char VV.arr_char B.VVV.arr_char B.VV.arr_char arr_char
              src_def trg_def inclusion
        by auto
      show "dom (\<alpha>\<^sub>S\<^sub>B \<mu>\<nu>\<tau>) = HoHV (VVV.dom \<mu>\<nu>\<tau>)"
      proof -
        have "dom (\<alpha>\<^sub>S\<^sub>B \<mu>\<nu>\<tau>) = B.HoHV (B.VVV.dom \<mu>\<nu>\<tau>)"
          using \<mu>\<nu>\<tau> 1 arr_char VVV.arr_char VV.arr_char B.VVV.arr_char B.VV.arr_char
                B.\<alpha>_def assoc_closed'
          by simp
        also have "... = HoHV (VVV.dom \<mu>\<nu>\<tau>)"
        proof -
          have "HoHV (VVV.dom \<mu>\<nu>\<tau>) = HoHV (VxVxV.dom \<mu>\<nu>\<tau>)"
            using \<mu>\<nu>\<tau> VVV.dom_char VV.arr_char src_def trg_def VVV.arr_char
            by simp
          also have "... = B.HoHV (B.VVV.dom \<mu>\<nu>\<tau>)"
             using \<mu>\<nu>\<tau> VVV.dom_char VVV.arr_char VV.arr_char src_def trg_def
                   HoHV_def B.HoHV_def arr_char B.VVV.arr_char B.VVV.dom_char B.VV.arr_char
                   dom_closed hcomp_closed hcomp_def inclusion
             by auto
          finally show ?thesis by simp
        qed
        finally show ?thesis by simp
      qed
      show "cod (\<alpha>\<^sub>S\<^sub>B \<mu>\<nu>\<tau>) = HoVH (VVV.cod \<mu>\<nu>\<tau>)"
      proof -
        have "cod (\<alpha>\<^sub>S\<^sub>B \<mu>\<nu>\<tau>) = B.HoVH (B.VVV.cod \<mu>\<nu>\<tau>)"
          using \<mu>\<nu>\<tau> 1 arr_char VVV.arr_char VV.arr_char B.VVV.arr_char B.VV.arr_char
                B.\<alpha>_def assoc_closed'
          by simp
        also have "... = HoVH (VVV.cod \<mu>\<nu>\<tau>)"
        proof -
          have "HoVH (VVV.cod \<mu>\<nu>\<tau>) = HoVH (VxVxV.cod \<mu>\<nu>\<tau>)"
            using \<mu>\<nu>\<tau> VVV.cod_char VV.arr_char src_def trg_def VVV.arr_char
            by simp
          also have "... = B.HoVH (B.VVV.cod \<mu>\<nu>\<tau>)"
            using \<mu>\<nu>\<tau> VVV.cod_char VV.arr_char src_def trg_def VVV.arr_char
                  HoVH_def B.HoVH_def arr_char B.VVV.arr_char B.VVV.cod_char B.VV.arr_char
                  cod_closed hcomp_closed hcomp_def inclusion
            by simp
          finally show ?thesis by simp
        qed
        finally show ?thesis by simp
      qed
      have 3: "Arr (fst \<mu>\<nu>\<tau>) \<and> Arr (fst (snd \<mu>\<nu>\<tau>)) \<and> Arr (snd (snd \<mu>\<nu>\<tau>)) \<and>
               src\<^sub>B (fst \<mu>\<nu>\<tau>) = trg\<^sub>B (fst (snd \<mu>\<nu>\<tau>)) \<and>
               src\<^sub>B (fst (snd \<mu>\<nu>\<tau>)) = trg\<^sub>B (snd (snd \<mu>\<nu>\<tau>))"
        using \<mu>\<nu>\<tau> VVV.arr_char VV.arr_char src_def trg_def arr_char by auto
      show "HoVH \<mu>\<nu>\<tau> \<cdot> \<alpha>\<^sub>S\<^sub>B (VVV.dom \<mu>\<nu>\<tau>) = \<alpha>\<^sub>S\<^sub>B \<mu>\<nu>\<tau>"
      proof -
        have "\<alpha>\<^sub>S\<^sub>B \<mu>\<nu>\<tau> = (fst \<mu>\<nu>\<tau> \<star>\<^sub>B fst (snd \<mu>\<nu>\<tau>) \<star>\<^sub>B snd (snd \<mu>\<nu>\<tau>)) \<cdot>\<^sub>B
                           \<a>\<^sub>B (B.dom (fst \<mu>\<nu>\<tau>)) (B.dom (fst (snd \<mu>\<nu>\<tau>))) (B.dom (snd (snd \<mu>\<nu>\<tau>)))"
          using 3 inclusion B.assoc_is_natural_1 [of "fst \<mu>\<nu>\<tau>" "fst (snd \<mu>\<nu>\<tau>)" "snd (snd \<mu>\<nu>\<tau>)"]
          by (simp add: \<mu>\<nu>\<tau>)
        also have "... = (fst \<mu>\<nu>\<tau> \<star> fst (snd \<mu>\<nu>\<tau>) \<star> snd (snd \<mu>\<nu>\<tau>)) \<cdot>
                           \<a>\<^sub>B (dom (fst \<mu>\<nu>\<tau>)) (dom (fst (snd \<mu>\<nu>\<tau>))) (dom (snd (snd \<mu>\<nu>\<tau>)))"
          using 1 3 \<mu>\<nu>\<tau> hcomp_closed assoc_closed dom_closed hcomp_def comp_def inclusion
            comp_char dom_char VVV.arr_char VV.arr_char
          apply simp
          using B.hcomp_simps(2-3) by presburger
        also have "... = HoVH \<mu>\<nu>\<tau> \<cdot> \<alpha>\<^sub>S\<^sub>B (VVV.dom \<mu>\<nu>\<tau>)"
          using \<mu>\<nu>\<tau> B.\<alpha>_def HoVH_def VVV.dom_char VV.dom_char VxVxV.dom_char
          apply simp
          by (metis (no_types, lifting) VV.arr_char VVV.arrE VVV.arr_dom VxV.dom_char
              dom_simp)
        finally show ?thesis by argo
      qed
      show "\<alpha>\<^sub>S\<^sub>B (VVV.cod \<mu>\<nu>\<tau>) \<cdot> HoHV \<mu>\<nu>\<tau> = \<alpha>\<^sub>S\<^sub>B \<mu>\<nu>\<tau>"
      proof -
        have "\<alpha>\<^sub>S\<^sub>B \<mu>\<nu>\<tau> =
              \<a>\<^sub>B (B.cod (fst \<mu>\<nu>\<tau>)) (B.cod (fst (snd \<mu>\<nu>\<tau>))) (B.cod (snd (snd \<mu>\<nu>\<tau>))) \<cdot>\<^sub>B
                (fst \<mu>\<nu>\<tau> \<star>\<^sub>B fst (snd \<mu>\<nu>\<tau>)) \<star>\<^sub>B snd (snd \<mu>\<nu>\<tau>)"
          using 3 inclusion B.assoc_is_natural_2 [of "fst \<mu>\<nu>\<tau>" "fst (snd \<mu>\<nu>\<tau>)" "snd (snd \<mu>\<nu>\<tau>)"]
          by (simp add: \<mu>\<nu>\<tau>)
        also have "... = \<a>\<^sub>B (cod (fst \<mu>\<nu>\<tau>)) (cod (fst (snd \<mu>\<nu>\<tau>))) (cod (snd (snd \<mu>\<nu>\<tau>))) \<cdot>
                           ((fst \<mu>\<nu>\<tau> \<star> fst (snd \<mu>\<nu>\<tau>)) \<star> snd (snd \<mu>\<nu>\<tau>)) "
          using 1 3 \<mu>\<nu>\<tau> hcomp_closed assoc_closed cod_closed hcomp_def comp_def inclusion
            comp_char cod_char VVV.arr_char VV.arr_char
          by simp
        also have "... = \<alpha>\<^sub>S\<^sub>B (VVV.cod \<mu>\<nu>\<tau>) \<cdot> HoHV \<mu>\<nu>\<tau>"
          using \<mu>\<nu>\<tau> B.\<alpha>_def HoHV_def VVV.cod_char VV.cod_char VxVxV.cod_char
                VVV.arr_char VV.arr_char arr_cod src_cod trg_cod
          by simp
        finally show ?thesis by argo
      qed
      next
      fix fgh
      assume fgh: "VVV.ide fgh"
      show "iso (\<alpha>\<^sub>S\<^sub>B fgh)"
      proof -
        have 1: "B.arr (fst (snd fgh)) \<and> B.arr (snd (snd fgh)) \<and>
                   src\<^sub>B (fst (snd fgh)) = trg\<^sub>B (snd (snd fgh)) \<and>
                   src\<^sub>B (fst fgh) = trg\<^sub>B (fst (snd fgh))"
          using fgh VVV.ide_char VVV.arr_char VV.arr_char src_def trg_def
                arr_char inclusion
          by auto
        have 2: "B.ide (fst fgh) \<and> B.ide (fst (snd fgh)) \<and> B.ide (snd (snd fgh))"
          using fgh VVV.ide_char ide_char by blast
        have "\<alpha>\<^sub>S\<^sub>B fgh = \<a>\<^sub>B (fst fgh) (fst (snd fgh)) (snd (snd fgh))"
          using fgh B.\<alpha>_def by simp
        moreover have "B.VVV.ide fgh"
          using fgh 1 2 VVV.ide_char B.VVV.ide_char VVV.arr_char B.VVV.arr_char
                src_def trg_def inclusion arr_char B.VV.arr_char
          by simp
        moreover have "Arr (\<a>\<^sub>B (fst fgh) (fst (snd fgh)) (snd (snd fgh)))"
          using fgh 1 VVV.ide_char VVV.arr_char VV.arr_char src_def trg_def
                arr_char assoc_closed' B.\<alpha>_def
          by simp
        moreover have "Arr (B.inv (\<a>\<^sub>B (fst fgh) (fst (snd fgh)) (snd (snd fgh))))"
          using fgh 1 VVV.ide_char VVV.arr_char VV.arr_char src_def trg_def
                arr_char assoc'_closed
          by (simp add: VVV.arr_char "2" B.VVV.ide_char calculation(2))
        ultimately show ?thesis
          using fgh iso_char B.\<alpha>.components_are_iso by auto
      qed
    qed

    interpretation L: endofunctor \<open>(\<cdot>)\<close> L
      using endofunctor_L by auto
    interpretation R: endofunctor \<open>(\<cdot>)\<close> R
      using endofunctor_R by auto

    interpretation L: faithful_functor \<open>(\<cdot>)\<close> \<open>(\<cdot>)\<close> L
    proof
      fix f f'
      assume par: "par f f'"
      assume eq: "L f = L f'"
      have "B.par f f'"
        using par inclusion arr_char by fastforce
      moreover have "B.L f = B.L f'"
      proof -
        have "\<forall>a. Arr a \<longrightarrow> B.arr a"
          by (simp add: inclusion)
        moreover have 1: "\<forall>a. arr a \<longrightarrow> (if arr a then hseq (trg a) a else arr null)"
          using L.preserves_arr by presburger
        moreover have "Arr f \<and> Arr (trg f) \<and> trg\<^sub>B f = src\<^sub>B (trg f)"
          by (meson 1 hcomp_def hseq_char' par)
        ultimately show ?thesis
          by (metis (no_types) eq hcomp_def hseq_char' par trg_def)
      qed
      ultimately show "f = f'"
        using B.L.is_faithful by blast
    qed
    interpretation L: full_functor \<open>(\<cdot>)\<close> \<open>(\<cdot>)\<close> L
    proof
      fix f f' \<nu>
      assume f: "ide f" and f': "ide f'" and \<nu>: "\<guillemotleft>\<nu> : L f \<Rightarrow> L f'\<guillemotright>"
      have 1: "L f = trg\<^sub>B f \<star>\<^sub>B f \<and> L f' = trg\<^sub>B f' \<star>\<^sub>B f'"
        using f f' hcomp_def trg_def arr_char ide_char trg_closed by simp
      have 2: "\<guillemotleft>\<nu> : trg\<^sub>B f \<star>\<^sub>B f \<Rightarrow>\<^sub>B trg\<^sub>B f' \<star>\<^sub>B f'\<guillemotright>"
        using 1 f f' \<nu> hcomp_def trg_def src_def inclusion
              dom_char cod_char hseq_char' arr_char ide_char trg_closed null_char
        by (simp add: arr_char in_hom_char)
      show "\<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow> f'\<guillemotright> \<and> L \<mu> = \<nu>"
      proof -
        let ?\<mu> = "B.\<ll> f' \<cdot>\<^sub>B \<nu> \<cdot>\<^sub>B B.inv (B.\<ll> f)"
        have \<mu>: "\<guillemotleft>?\<mu> : f \<Rightarrow> f'\<guillemotright> \<and> \<guillemotleft>?\<mu> : f \<Rightarrow>\<^sub>B f'\<guillemotright>"
        proof -
          have "\<guillemotleft>?\<mu> : f \<Rightarrow>\<^sub>B f'\<guillemotright>"
            using f f' \<nu> 2 B.\<ll>_ide_simp lunit'_closed lunit_closed' ide_char by auto
          thus ?thesis
            using f f' \<nu> in_hom_char arr_char comp_closed ide_char
                  lunit'_closed lunit_closed
            by (metis (no_types, lifting) B.arrI B.seqE in_homE)
        qed
        have \<mu>_eq: "?\<mu> = B.\<ll> f' \<cdot> \<nu> \<cdot> B.inv (B.\<ll> f)"
        proof -
          have "?\<mu> = B.\<ll> f' \<cdot> \<nu> \<cdot>\<^sub>B B.inv (B.\<ll> f)"
            using f f' \<nu> \<mu> arr_char inclusion comp_char comp_closed ide_char
                 lunit'_closed lunit_closed
            by (metis (no_types, lifting) B.seqE in_homE)
          also have "... = B.\<ll> f' \<cdot> \<nu> \<cdot> B.inv (B.\<ll> f)"
            using f f' \<nu> \<mu> arr_char inclusion comp_char comp_closed ide_char
                  lunit'_closed lunit_closed
            by (metis (no_types, lifting) B.seqE in_homE)
          finally show ?thesis by simp
        qed
        have "L ?\<mu> = \<nu>"
        proof -
          have "L ?\<mu> = trg\<^sub>B ?\<mu> \<star>\<^sub>B ?\<mu>"
            using \<mu> \<mu>_eq hcomp_def trg_def inclusion arr_char trg_closed by auto
          also have "... = (trg\<^sub>B ?\<mu> \<star>\<^sub>B ?\<mu>) \<cdot>\<^sub>B (B.inv (B.\<ll> f) \<cdot>\<^sub>B B.\<ll> f)"
          proof -
            have "B.inv (B.\<ll> f) \<cdot>\<^sub>B B.\<ll> f = trg\<^sub>B f \<star>\<^sub>B f"
              using f ide_char B.comp_inv_arr B.inv_is_inverse by auto
            moreover have "B.dom (trg\<^sub>B ?\<mu> \<star>\<^sub>B ?\<mu>) = trg\<^sub>B f \<star>\<^sub>B f"
              using f \<mu> \<mu>_eq ide_char arr_char B.trg_dom [of ?\<mu>] by fastforce
            ultimately show ?thesis
              using \<mu> \<mu>_eq B.comp_arr_dom in_hom_char by auto
          qed
          also have "... = ((trg\<^sub>B ?\<mu> \<star>\<^sub>B ?\<mu>) \<cdot>\<^sub>B B.inv (B.\<ll> f)) \<cdot>\<^sub>B B.\<ll> f"
            using B.comp_assoc by simp
          also have "... = (B.inv (B.\<ll> f') \<cdot>\<^sub>B ?\<mu>) \<cdot>\<^sub>B B.\<ll> f"
            using \<mu> \<mu>_eq B.\<ll>'.naturality [of ?\<mu>] by auto
          also have "... = (B.inv (B.\<ll> f') \<cdot>\<^sub>B B.\<ll> f') \<cdot>\<^sub>B \<nu> \<cdot>\<^sub>B (B.inv (B.\<ll> f) \<cdot>\<^sub>B B.\<ll> f)"
            using \<mu> \<mu>_eq arr_char arrI comp_simp B.comp_assoc by metis
          also have "... = \<nu>"
            using f f' \<nu> 2 B.comp_arr_dom B.comp_cod_arr ide_char
                  B.\<ll>.components_are_iso B.\<ll>_ide_simp B.comp_inv_arr'
            by auto
          finally show ?thesis by blast
        qed
        thus ?thesis
          using \<mu> by auto
      qed
    qed

    interpretation R: faithful_functor \<open>(\<cdot>)\<close> \<open>(\<cdot>)\<close> R
    proof
      fix f f'
      assume par: "par f f'"
      assume eq: "R f = R f'"
      have "B.par f f'"
        using par inclusion arr_char by fastforce
      moreover have "B.R f = B.R f'"
      proof -
        have "\<forall>a. Arr a \<longrightarrow> B.arr a"
          by (simp add: inclusion)
        moreover have 1: "\<forall>a. arr a \<longrightarrow> (if arr a then hseq a (src a) else arr null)"
          using R.preserves_arr by presburger
        moreover have "Arr f \<and> Arr (src f) \<and> trg\<^sub>B (src f) = src\<^sub>B f"
          by (meson 1 hcomp_def hseq_char' par)
        ultimately show ?thesis
          by (metis (no_types) eq hcomp_def hseq_char' par src_def)
      qed
      ultimately show "f = f'"
        using B.R.is_faithful by blast
    qed
    interpretation R: full_functor \<open>(\<cdot>)\<close> \<open>(\<cdot>)\<close> R
    proof
      fix f f' \<nu>
      assume f: "ide f" and f': "ide f'" and \<nu>: "\<guillemotleft>\<nu> : R f \<Rightarrow> R f'\<guillemotright>"
      have 1: "R f = f \<star>\<^sub>B src\<^sub>B f \<and> R f' = f' \<star>\<^sub>B src\<^sub>B f'"
        using f f' hcomp_def src_def arr_char ide_char src_closed by simp
      have 2: "\<guillemotleft>\<nu> : f \<star>\<^sub>B src\<^sub>B f \<Rightarrow>\<^sub>B f' \<star>\<^sub>B src\<^sub>B f'\<guillemotright>"
        using 1 f f' \<nu> hcomp_def trg_def src_def inclusion
              dom_char cod_char hseq_char' arr_char ide_char trg_closed null_char
        by (simp add: arr_char in_hom_char)
      show "\<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow> f'\<guillemotright> \<and> R \<mu> = \<nu>"
      proof -
        let ?\<mu> = "B.\<rr> f' \<cdot>\<^sub>B \<nu> \<cdot>\<^sub>B B.inv (B.\<rr> f)"
        have \<mu>: "\<guillemotleft>?\<mu> : f \<Rightarrow> f'\<guillemotright> \<and> \<guillemotleft>?\<mu> : f \<Rightarrow>\<^sub>B f'\<guillemotright>"
        proof -
          have "\<guillemotleft>?\<mu> : f \<Rightarrow>\<^sub>B f'\<guillemotright>"
            using f f' \<nu> 2 B.\<rr>_ide_simp runit'_closed runit_closed' ide_char by auto
          thus ?thesis
            using f f' \<nu> in_hom_char [of ?\<mu> f f'] arr_char comp_closed ide_char
                  runit'_closed runit_closed
            apply auto
            by fastforce
        qed
        have \<mu>_eq: "?\<mu> = B.\<rr> f' \<cdot> \<nu> \<cdot> B.inv (B.\<rr> f)"
        proof -
          have "?\<mu> = B.\<rr> f' \<cdot> \<nu> \<cdot>\<^sub>B B.inv (B.\<rr> f)"
            using f f' \<nu> \<mu> arr_char inclusion comp_char comp_closed ide_char
                 runit'_closed runit_closed
            by (metis (no_types, lifting) B.seqE in_homE)
          also have "... = B.\<rr> f' \<cdot> \<nu> \<cdot> B.inv (B.\<rr> f)"
            using f f' \<nu> \<mu> arr_char inclusion comp_char comp_closed ide_char
                  runit'_closed runit_closed
            by (metis (no_types, lifting) B.arrI B.comp_in_homE in_hom_char)
          finally show ?thesis by simp
        qed
        have "R ?\<mu> = \<nu>"
        proof -
          have "R ?\<mu> = ?\<mu> \<star>\<^sub>B src\<^sub>B ?\<mu>"
            using \<mu> \<mu>_eq hcomp_def src_def inclusion arr_char src_closed by auto
          also have "... = (?\<mu> \<star>\<^sub>B src\<^sub>B ?\<mu>) \<cdot>\<^sub>B (B.inv (B.\<rr> f) \<cdot>\<^sub>B B.\<rr> f)"
          proof -
            have "B.inv (B.\<rr> f) \<cdot>\<^sub>B B.\<rr> f = f \<star>\<^sub>B src\<^sub>B f"
              using f ide_char B.comp_inv_arr B.inv_is_inverse by auto
            moreover have "B.dom (?\<mu> \<star>\<^sub>B src\<^sub>B ?\<mu>) = f \<star>\<^sub>B src\<^sub>B f"
              using f \<mu> \<mu>_eq ide_char arr_char B.src_dom [of ?\<mu>] by fastforce
            ultimately show ?thesis
              using \<mu> \<mu>_eq B.comp_arr_dom in_hom_char by auto
          qed
          also have "... = ((?\<mu> \<star>\<^sub>B src\<^sub>B ?\<mu>) \<cdot>\<^sub>B B.inv (B.\<rr> f)) \<cdot>\<^sub>B B.\<rr> f"
            using B.comp_assoc by simp
          also have "... = (B.inv (B.\<rr> f') \<cdot>\<^sub>B ?\<mu>) \<cdot>\<^sub>B B.\<rr> f"
            using \<mu> \<mu>_eq B.\<rr>'.naturality [of ?\<mu>] by auto
          also have "... = (B.inv (B.\<rr> f') \<cdot>\<^sub>B B.\<rr> f') \<cdot>\<^sub>B \<nu> \<cdot>\<^sub>B (B.inv (B.\<rr> f) \<cdot>\<^sub>B B.\<rr> f)"
            using \<mu> \<mu>_eq arr_char arrI comp_simp B.comp_assoc by metis
          also have "... = \<nu>"
            using f f' \<nu> 2 B.comp_arr_dom B.comp_cod_arr ide_char
                  B.\<ll>.components_are_iso B.\<ll>_ide_simp B.comp_inv_arr'
            by auto
          finally show ?thesis by blast
        qed
        thus ?thesis
          using \<mu> by blast
      qed
    qed

    interpretation bicategory \<open>(\<cdot>)\<close> \<open>(\<star>)\<close> \<a> \<i> src trg
    proof
      show "\<And>a. obj a \<Longrightarrow> \<guillemotleft>\<i> a : a \<star> a \<rightarrow> a\<guillemotright>"
      proof -
        fix a
        assume a: "obj a"
        have 1: "trg\<^sub>B a = src\<^sub>B a"
          using a obj_def src_def trg_def B.obj_def arr_char
          by (metis horizontal_homs.objE horizontal_homs_axioms)
        have 2: "Arr (\<i> a)"
          using a 1 obj_def src_def trg_def in_hom_char B.unit_in_hom
                arr_char hcomp_def B.obj_def ide_char objE hcomp_closed
          by (metis (no_types, lifting) B.\<ll>_ide_simp B.unitor_coincidence(1) inclusion lunit_closed)
        show "\<guillemotleft>\<i> a : a \<star> a \<rightarrow> a\<guillemotright>"
          using a 1 2 obj_def src_def trg_def in_hom_char B.unit_in_hom
                arr_char hcomp_def B.obj_def ide_char hcomp_closed
          apply (elim objE) by auto
      qed
      show "\<And>a. obj a \<Longrightarrow> iso (\<i> a)"
      proof -
        fix a
        assume a: "obj a"
        have 1: "trg\<^sub>B a = src\<^sub>B a"
          using a obj_def src_def trg_def B.obj_def arr_char
          by (metis horizontal_homs.objE horizontal_homs_axioms)
        have 2: "Arr (\<i> a)"
          using a 1 obj_def src_def trg_def in_hom_char B.unit_in_hom
                arr_char hcomp_def B.obj_def ide_char objE hcomp_closed
          by (metis (no_types, lifting) B.\<ll>_ide_simp B.unitor_coincidence(1) inclusion lunit_closed)
        have "iso (B.\<ll> a)"
          using a 2 obj_def B.iso_unit iso_char arr_char lunit_closed lunit'_closed B.iso_lunit
          apply simp
          by (metis (no_types, lifting) B.\<ll>.components_are_iso B.ide_src inclusion src_def)
        thus "iso (\<i> a)"
          using a 2 obj_def B.iso_unit iso_char arr_char B.unitor_coincidence
          apply simp
          by (metis (no_types, lifting) B.\<ll>_ide_simp B.ide_src B.obj_src inclusion src_def)
      qed
      show "\<And>f g h k. \<lbrakk> ide f; ide g; ide h; ide k;
                        src f = trg g; src g = trg h; src h = trg k \<rbrakk> \<Longrightarrow>
                           (f \<star> \<a> g h k) \<cdot> \<a> f (g \<star> h) k \<cdot> (\<a> f g h \<star> k) =
                           \<a> f g (h \<star> k) \<cdot> \<a> (f \<star> g) h k"
        using B.pentagon VVV.arr_char VV.arr_char hcomp_def assoc_closed arr_char comp_char
              hcomp_closed comp_closed ide_char inclusion src_def trg_def
        by simp       
    qed

    proposition is_bicategory:
    shows "bicategory (\<cdot>) (\<star>) \<a> \<i> src trg"
      ..

    lemma obj_char:
    shows "obj a \<longleftrightarrow> Arr a \<and> B.obj a"
      using obj_def src_def arr_char
      by (simp add: B.obj_def inclusion)

  end

  sublocale subbicategory \<subseteq> bicategory \<open>(\<cdot>)\<close> \<open>(\<star>)\<close> \<a> \<i> src trg
    using is_bicategory by auto

  subsection "The Sub-bicategory of Endo-arrows of an Object"

  text \<open>
    We now consider the sub-bicategory consisting of all arrows having the same
    object \<open>a\<close> both as their source and their target and we show that the resulting structure
    is a monoidal category.  We actually prove a slightly more general result,
    in which the unit of the monoidal category is taken to be an arbitrary isomorphism
    \<open>\<guillemotleft>\<omega> : w \<star>\<^sub>B w \<Rightarrow> w\<guillemotright>\<close> with \<open>w\<close> isomorphic to \<open>a\<close>, rather than the particular choice
    \<open>\<guillemotleft>\<i>[a] : a \<star>\<^sub>B a \<Rightarrow> a\<guillemotright>\<close> made by the ambient bicategory.
  \<close>

  locale subbicategory_at_object =
    B: bicategory V H \<a>\<^sub>B \<i> src\<^sub>B trg\<^sub>B +
    subbicategory V H \<a>\<^sub>B \<i> src\<^sub>B trg\<^sub>B \<open>\<lambda>\<mu>. B.arr \<mu> \<and> src\<^sub>B \<mu> = a \<and> trg\<^sub>B \<mu> = a\<close>
  for V :: "'a comp"                 (infixr "\<cdot>\<^sub>B" 55)
  and H :: "'a comp"                 (infixr "\<star>\<^sub>B" 55)
  and \<a>\<^sub>B :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"    ("\<a>\<^sub>B[_, _, _]")
  and \<i> :: "'a \<Rightarrow> 'a"                 ("\<i>[_]")
  and src\<^sub>B :: "'a \<Rightarrow> 'a"
  and trg\<^sub>B :: "'a \<Rightarrow> 'a"
  and a :: "'a"
  and w :: "'a"
  and \<omega> :: "'a" +
  assumes obj_a: "B.obj a"
  and isomorphic_a_w: "B.isomorphic a w"
  and \<omega>_in_vhom: "\<guillemotleft>\<omega> : w \<star>\<^sub>B w \<Rightarrow> w\<guillemotright>"
  and \<omega>_is_iso: "B.iso \<omega>"
  begin

    notation hcomp  (infixr "\<star>" 53)

    lemma arr_simps:
    assumes "arr \<mu>"
    shows "src \<mu> = a" and "trg \<mu> = a"
      apply (metis (no_types, lifting) arrE assms src_def)
      by (metis (no_types, lifting) arrE assms trg_def)

    lemma \<omega>_simps [simp]:
    shows "arr \<omega>"
    and "src \<omega> = a" and "trg \<omega> = a"
    and "dom \<omega> = w \<star>\<^sub>B w" and "cod \<omega> = w"
      using isomorphic_a_w \<omega>_in_vhom in_hom_char arr_simps by auto

    lemma ide_w:
    shows "B.ide w"
      using isomorphic_a_w B.isomorphic_def by auto

    lemma w_simps [simp]:
    shows "ide w" and "B.ide w"
    and "src w = a" and "trg w = a" and "src\<^sub>B w = a" and "trg\<^sub>B w = a"
    and "dom w = w" and "cod w = w"
    proof -
      show w: "ide w"
        using \<omega>_in_vhom ide_cod by blast
      show "B.ide w"
        using w ide_char by simp
      obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : a \<Rightarrow>\<^sub>B w\<guillemotright> \<and> B.iso \<phi>"
        using isomorphic_a_w B.isomorphic_def by auto
      show "src\<^sub>B w = a"
        using obj_a w \<phi> B.src_cod by force
      show "trg\<^sub>B w = a"
        using obj_a w \<phi> B.src_cod by force
      show "src w = a"
        using `src\<^sub>B w = a` ide_w src_def
        by (simp add: \<open>trg\<^sub>B w = a\<close>)
      show "trg w = a"
        using `src\<^sub>B w = a` ide_w trg_def
        by (simp add: \<open>trg\<^sub>B w = a\<close>)
      show "dom w = w"
        using w by simp
      show "cod w = w"
        using w by simp
    qed

    lemma VxV_arr_eq_VV_arr:
    shows "VxV.arr f \<longleftrightarrow> VV.arr f"
      using inclusion VxV.arr_char VV.arr_char arr_char src_def trg_def
      by auto

    lemma VxV_comp_eq_VV_comp:
    shows "VxV.comp = VV.comp"
    proof -
      have "\<And>f g. VxV.comp f g = VV.comp f g"
      proof -
        fix f g
        show "VxV.comp f g = VV.comp f g"
          unfolding VV.comp_def
          using VxV.comp_char arr_simps(1) arr_simps(2)
          apply (cases "seq (fst f) (fst g)", cases "seq (snd f) (snd g)")
            apply (elim seqE)
          by auto
      qed
      thus ?thesis by blast
    qed

    lemma VxVxV_arr_eq_VVV_arr:
    shows "VxVxV.arr f \<longleftrightarrow> VVV.arr f"
      using VVV.arr_char VV.arr_char src_def trg_def inclusion arr_char
      by auto

    lemma VxVxV_comp_eq_VVV_comp:
    shows "VxVxV.comp = VVV.comp"
    proof -
      have "\<And>f g. VxVxV.comp f g = VVV.comp f g"
      proof -
        fix f g
        show "VxVxV.comp f g = VVV.comp f g"
        proof (cases "VxVxV.seq f g")
          assume 1: "\<not> VxVxV.seq f g"
          have "VxVxV.comp f g = VxVxV.null"
            using 1 VxVxV.ext by blast
          also have "... = (null, null, null)"
            using VxVxV.null_char VxV.null_char by simp
          also have "... = VVV.null"
            using VVV.null_char VV.null_char by simp
          also have "... = VVV.comp f g"
          proof -
            have "\<not> VVV.seq f g"
              using 1 VVV.seq_char by blast
            thus ?thesis
              by (metis (no_types, lifting) VVV.ext)
          qed
          finally show ?thesis by simp
          next
          assume 1: "VxVxV.seq f g"
          have 2: "B.arr (fst f) \<and> B.arr (fst (snd f)) \<and> B.arr (snd (snd f)) \<and>
                src\<^sub>B (fst f) = a \<and> src\<^sub>B (fst (snd f)) = a \<and> src\<^sub>B (snd (snd f)) = a \<and>
                trg\<^sub>B (fst f) = a \<and> trg\<^sub>B (fst (snd f)) = a \<and> trg\<^sub>B (snd (snd f)) = a"
            using 1 VxVxV.seq_char VxV.seq_char arr_char by blast
          have 3: "B.arr (fst g) \<and> B.arr (fst (snd g)) \<and> B.arr (snd (snd g)) \<and>
                   src\<^sub>B (fst g) = a \<and> src\<^sub>B (fst (snd g)) = a \<and> src\<^sub>B (snd (snd g)) = a \<and>
                   trg\<^sub>B (fst g) = a \<and> trg\<^sub>B (fst (snd g)) = a \<and> trg\<^sub>B (snd (snd g)) = a"
            using 1 VxVxV.seq_char VxV.seq_char arr_char by blast
          have 4: "B.seq (fst f) (fst g) \<and> B.seq (fst (snd f)) (fst (snd g)) \<and>
                   B.seq (snd (snd f)) (snd (snd g))"
            using 1 VxVxV.seq_char VxV.seq_char seq_char by blast
          have 5: "VxVxV.comp f g =
                   (fst f \<cdot> fst g, fst (snd f) \<cdot> fst (snd g), snd (snd f) \<cdot> snd (snd g))"
            using 1 2 3 4 VxVxV.seqE VxVxV.comp_char VxV.comp_char seq_char arr_char
            by (metis (no_types, lifting)) 
          also have "... = VVV.comp f g"
            using 1 VVV.comp_char VVV.arr_char VV.arr_char
            apply simp
            using 2 3 5 arrI arr_simps(1) arr_simps(2) by presburger
          finally show ?thesis by blast
        qed
      qed
      thus ?thesis by blast
    qed
 
    interpretation H: "functor" VxV.comp \<open>(\<cdot>)\<close> \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu>\<close>
      using H.functor_axioms hcomp_def VxV_comp_eq_VV_comp by simp

    interpretation H: binary_endofunctor \<open>(\<cdot>)\<close> \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu>\<close> ..

    lemma HoHV_eq_ToTC:
    shows "HoHV = H.ToTC"
      using HoHV_def H.ToTC_def VVV.arr_char VV.arr_char src_def trg_def inclusion arr_char
      by auto

    lemma HoVH_eq_ToCT:
    shows "HoVH = H.ToCT"
      using HoVH_def H.ToCT_def VVV.arr_char VV.arr_char src_def trg_def inclusion arr_char
      by auto

    interpretation ToTC: "functor" VxVxV.comp \<open>(\<cdot>)\<close> H.ToTC
      using HoHV_eq_ToTC VxVxV_comp_eq_VVV_comp HoHV.functor_axioms by simp
    interpretation ToCT: "functor" VxVxV.comp \<open>(\<cdot>)\<close> H.ToCT
      using HoVH_eq_ToCT VxVxV_comp_eq_VVV_comp HoVH.functor_axioms by simp

    interpretation \<alpha>: natural_isomorphism VxVxV.comp \<open>(\<cdot>)\<close> H.ToTC H.ToCT \<alpha>
      unfolding \<alpha>_def
      using \<alpha>.natural_isomorphism_axioms HoHV_eq_ToTC HoVH_eq_ToCT \<alpha>_def
            VxVxV_comp_eq_VVV_comp
      by simp

    interpretation L: endofunctor \<open>(\<cdot>)\<close> \<open>\<lambda>f. fst (w, f) \<star> snd (w, f)\<close>
    proof
      fix f
      show "\<not> arr f \<Longrightarrow> fst (w, f) \<star> snd (w, f) = null"
        using arr_char hcomp_def by auto
      assume f: "arr f"
      show "hseq (fst (w, f)) (snd (w, f))"
        using f hseq_char arr_char src_def trg_def \<omega>_in_vhom cod_char by simp
      show "dom (fst (w, f) \<star> snd (w, f)) = fst (w, dom f) \<star> snd (w, dom f)"
        using f arr_char hcomp_def by simp
      show "cod (fst (w, f) \<star> snd (w, f)) = fst (w, cod f) \<star> snd (w, cod f)"
        using f arr_char hcomp_def by simp
      next
      fix f g
      assume fg: "seq g f"
      show "fst (w, g \<cdot> f) \<star> snd (w, g \<cdot> f) = (fst (w, g) \<star> snd (w, g)) \<cdot> (fst (w, f) \<star> snd (w, f))"
        by (simp add: fg whisker_left)
    qed

    interpretation L': equivalence_functor \<open>(\<cdot>)\<close> \<open>(\<cdot>)\<close> \<open>\<lambda>f. fst (w, f) \<star> snd (w, f)\<close>
    proof -
      obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : w \<Rightarrow>\<^sub>B a\<guillemotright> \<and> B.iso \<phi>"
        using isomorphic_a_w B.isomorphic_symmetric by force
      have "\<guillemotleft>\<phi> : w \<Rightarrow> a\<guillemotright>"
        using \<phi> in_hom_char
        by (metis (no_types, lifting) B.in_homE B.src_cod B.src_src B.trg_cod B.trg_trg
            \<omega>_in_vhom arr_char arr_cod cod_simp)
      hence \<phi>: "\<guillemotleft>\<phi> : w \<Rightarrow>\<^sub>B a\<guillemotright> \<and> B.iso \<phi> \<and> \<guillemotleft>\<phi> : w \<Rightarrow> a\<guillemotright> \<and> iso \<phi>"
        using \<phi> iso_char arr_char by auto
      interpret \<l>: natural_isomorphism \<open>(\<cdot>)\<close> \<open>(\<cdot>)\<close>
                     \<open>\<lambda>f. fst (w, f) \<star> snd (w, f)\<close> map \<open>\<lambda>f. \<ll> f \<cdot> (\<phi> \<star> dom f)\<close>
      proof
        fix \<mu>
        show "\<not> arr \<mu> \<Longrightarrow> \<ll> \<mu> \<cdot> (\<phi> \<star> dom \<mu>) = null"
          using \<phi> arr_char dom_char ext
          apply simp
          using comp_null(2) hcomp_def by fastforce
        assume \<mu>: "arr \<mu>"
        have 0: "in_hhom (dom \<mu>) a a"
          using \<mu> arr_char src_dom trg_dom src_def trg_def by simp
        have 1: "in_hhom \<phi> a a"
          using \<phi> arr_char src_dom trg_dom src_def trg_def by auto
        have 2: "hseq \<phi> (B.dom \<mu>)"
          using \<mu> 0 1 by auto
        have 3: "seq (\<ll> \<mu>) (\<phi> \<star> dom \<mu>)"
        proof (intro seqI')
          show "\<guillemotleft>\<phi> \<star> dom \<mu> : w \<star> dom \<mu> \<Rightarrow> a \<star> dom \<mu>\<guillemotright>"
            by (metis (no_types, lifting) 0 \<mu> \<phi> hcomp_in_vhom ide_dom ide_in_hom(2)
                in_hhom_def w_simps(3))
          show "\<guillemotleft>\<ll> \<mu> : a \<star> dom \<mu> \<Rightarrow> cod \<mu>\<guillemotright>"
            using \<mu> 2 \<ll>.preserves_hom [of \<mu> "dom \<mu>" "cod \<mu>"] arr_simps(2) arr_cod by fastforce
        qed
        show "dom (\<ll> \<mu> \<cdot> (\<phi> \<star> dom \<mu>)) = fst (w, dom \<mu>) \<star> snd (w, dom \<mu>)"
        proof -
          have "dom (\<ll> \<mu> \<cdot> (\<phi> \<star> dom \<mu>)) = dom \<phi> \<star> dom \<mu>"
            using \<mu> 3 hcomp_simps(3) dom_comp dom_dom
            apply (elim seqE) by auto
          also have "... = fst (w, dom \<mu>) \<star> snd (w, dom \<mu>)"
            using \<omega>_in_vhom \<phi>
            by (metis (no_types, lifting) in_homE prod.sel(1) prod.sel(2))
          finally show ?thesis by simp
        qed
        show "cod (\<ll> \<mu> \<cdot> (\<phi> \<star> dom \<mu>)) = map (cod \<mu>)"
        proof -
          have "seq (\<ll> \<mu>) (\<phi> \<star> dom \<mu>)"
            using 3 by simp
          hence "cod (\<ll> \<mu> \<cdot> (\<phi> \<star> dom \<mu>)) = cod (\<ll> \<mu>)"
            using cod_comp by blast
          also have "... = map (cod \<mu>)"
            using \<mu> by blast
          finally show ?thesis by blast
        qed
        show "map \<mu> \<cdot> \<ll> (dom \<mu>) \<cdot> (\<phi> \<star> dom (dom \<mu>)) = \<ll> \<mu> \<cdot> (\<phi> \<star> dom \<mu>)"
        proof -
          (*
           * TODO: The automatic simplification of dom to B.dom prevents the application
           * of dom_dom here.
           *)
          have "map \<mu> \<cdot> \<ll> (dom \<mu>) \<cdot> (\<phi> \<star> dom (dom \<mu>)) =
                (map \<mu> \<cdot> \<ll> (dom \<mu>)) \<cdot> (\<phi> \<star> dom (dom \<mu>))"
            using comp_assoc by simp
          also have "... = (map \<mu> \<cdot> \<ll> (dom \<mu>)) \<cdot> (\<phi> \<star> dom \<mu>)"
            using \<mu> dom_dom by simp
          also have "... = \<ll> \<mu> \<cdot> (\<phi> \<star> dom \<mu>)"
            using \<mu> \<phi> \<ll>.is_natural_1 by auto
          finally show ?thesis by blast
        qed
        show "(\<ll> (cod \<mu>) \<cdot> (\<phi> \<star> dom (cod \<mu>))) \<cdot> (fst (w, \<mu>) \<star> snd (w, \<mu>)) = \<ll> \<mu> \<cdot> (\<phi> \<star> dom \<mu>)"
        proof -
          have "(\<ll> (cod \<mu>) \<cdot> (\<phi> \<star> dom (cod \<mu>))) \<cdot> (fst (w, \<mu>) \<star> snd (w, \<mu>)) =
                (\<ll> (cod \<mu>) \<cdot> (\<phi> \<star> B.cod \<mu>)) \<cdot> (w \<star> \<mu>)"
            using \<mu> \<phi> dom_char arr_char \<omega>_in_vhom by simp
          also have "... = \<ll> (cod \<mu>) \<cdot> (\<phi> \<cdot> w \<star> B.cod \<mu> \<cdot> \<mu>)"
          proof -
            have "seq \<phi> w"
              using \<phi> \<omega>_in_vhom w_simps(1) by blast
            moreover have 2: "seq (B.cod \<mu>) \<mu>"
              using \<mu> seq_char by (simp add: comp_cod_arr)
            moreover have "src \<phi> = trg (B.cod \<mu>)"
              using \<mu> \<phi> 2
              by (metis (no_types, lifting) arr_simps(2) seqE vconn_implies_hpar(1) w_simps(3))
            ultimately show ?thesis
              using interchange comp_assoc by simp
          qed
          also have "... = \<ll> (cod \<mu>) \<cdot> (\<phi> \<star> \<mu>)"
            using \<mu> \<phi> \<omega>_in_vhom comp_arr_dom comp_cod_arr cod_simp
            apply (elim conjE in_homE) by auto
          also have "... = (\<ll> (cod \<mu>) \<cdot> (cod \<phi> \<star> \<mu>)) \<cdot> (\<phi> \<star> dom \<mu>)"
          proof -
            have "seq (cod \<phi>) \<phi>"
              using \<phi> arr_cod_iff_arr dom_cod iso_is_arr seqI by presburger
            moreover have "seq \<mu> (dom \<mu>)"
              using \<mu> by (simp add: comp_arr_dom)
            moreover have "src (cod \<phi>) = trg \<mu>"
              using \<mu> \<phi> arr_cod arr_simps(1-2) iso_is_arr by auto
            ultimately show ?thesis
              using \<mu> \<phi> interchange [of "cod \<phi>" \<phi> \<mu> "dom \<mu>"] comp_assoc
              by (simp add: comp_arr_dom comp_cod_arr iso_is_arr)
          qed
          also have "... = \<ll> \<mu> \<cdot> (\<phi> \<star> dom \<mu>)"
          proof -
            have "L \<mu> = cod \<phi> \<star> \<mu>"
              using \<mu> \<phi> arr_simps(2) in_homE by auto
            hence "\<ll> (cod \<mu>) \<cdot> (cod \<phi> \<star> \<mu>) = \<ll> \<mu>"
              using \<mu> \<ll>.is_natural_2 [of \<mu>] by simp
            thus ?thesis by simp
          qed
          finally show ?thesis by simp
        qed
        next
        show "\<And>f. ide f \<Longrightarrow> iso (\<ll> f \<cdot> (\<phi> \<star> dom f))"
        proof -
          fix f
          assume f: "ide f"
          have "iso (\<ll> f)"
            using f iso_lunit by simp
          moreover have "iso (\<phi> \<star> dom f)"
            using \<phi> f src_def trg_def ide_char arr_char
            apply (intro iso_hcomp, simp_all)
            by (metis (no_types, lifting) in_homE)
          moreover have "seq (\<ll> f) (\<phi> \<star> dom f)"
          proof (intro seqI')
            show " \<guillemotleft>\<ll> f : a \<star> f \<Rightarrow> f\<guillemotright>"
              using f lunit_in_hom(2) \<ll>_ide_simp ide_char arr_char trg_def by simp
            show "\<guillemotleft>\<phi> \<star> dom f : w \<star> f \<Rightarrow> a \<star> f\<guillemotright>"
              using \<phi> f ide_char arr_char hcomp_def src_def trg_def obj_a ide_in_hom
                    in_hom_char
              by (intro hcomp_in_vhom, auto)
          qed
          ultimately show "iso (\<ll> f \<cdot> (\<phi> \<star> dom f))"
            using isos_compose by simp
        qed
      qed
      show "equivalence_functor (\<cdot>) (\<cdot>) (\<lambda>f. fst (w, f) \<star> snd (w, f))"
        using \<l>.natural_isomorphism_axioms L.isomorphic_to_identity_is_equivalence by simp
    qed
    interpretation L: equivalence_functor \<open>(\<cdot>)\<close> \<open>(\<cdot>)\<close> \<open>\<lambda>f. fst (cod \<omega>, f) \<star> snd (cod \<omega>, f)\<close>
    proof -
      have "(\<lambda>f. fst (cod \<omega>, f) \<star> snd (cod \<omega>, f)) = (\<lambda>f. fst (w, f) \<star> snd (w, f))"
        using \<omega>_in_vhom by simp
      thus "equivalence_functor (\<cdot>) (\<cdot>) (\<lambda>f. fst (cod \<omega>, f) \<star> snd (cod \<omega>, f))"
        using L'.equivalence_functor_axioms by simp
    qed

    interpretation R: endofunctor \<open>(\<cdot>)\<close> \<open>\<lambda>f. fst (f, w) \<star> snd (f, w)\<close>
    proof
      fix f
      show "\<not> arr f \<Longrightarrow> fst (f, w) \<star> snd (f, w) = null"
        using arr_char hcomp_def by auto
      assume f: "arr f"
      show "hseq (fst (f, w)) (snd (f, w))"
        using f hseq_char arr_char src_def trg_def \<omega>_in_vhom cod_char isomorphic_a_w
              B.isomorphic_def in_hom_char
        by simp
      show "dom (fst (f, w) \<star> snd (f, w)) = fst (dom f, w) \<star> snd (dom f, w)"
        using f arr_char dom_char cod_char hcomp_def \<omega>_in_vhom by simp
      show "cod (fst (f, w) \<star> snd (f, w)) = fst (cod f, w) \<star> snd (cod f, w)"
        using f arr_char dom_char cod_char hcomp_def \<omega>_in_vhom by simp
      next
      fix f g
      assume fg: "seq g f"
      have 1: "a \<cdot>\<^sub>B a = a"
        using obj_a by auto
      show "fst (g \<cdot> f, w) \<star> snd (g \<cdot> f, w) = (fst (g, w) \<star> snd (g, w)) \<cdot> (fst (f, w) \<star> snd (f, w))"
        by (simp add: fg whisker_right)
    qed

    interpretation R': equivalence_functor \<open>(\<cdot>)\<close> \<open>(\<cdot>)\<close> \<open>\<lambda>f. fst (f, w) \<star> snd (f, w)\<close>
    proof -
      obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : w \<Rightarrow>\<^sub>B a\<guillemotright> \<and> B.iso \<phi>"
        using isomorphic_a_w B.isomorphic_symmetric by force
      have "\<guillemotleft>\<phi> : w \<Rightarrow> a\<guillemotright>"
        using \<phi> in_hom_char
        by (metis (no_types, lifting) B.in_homE B.src_cod B.src_src B.trg_cod B.trg_trg
            \<omega>_in_vhom arr_char arr_cod cod_simp)
      hence \<phi>: "\<guillemotleft>\<phi> : w \<Rightarrow>\<^sub>B a\<guillemotright> \<and> B.iso \<phi> \<and> \<guillemotleft>\<phi> : w \<Rightarrow> a\<guillemotright> \<and> iso \<phi>"
        using \<phi> iso_char arr_char by auto
      interpret \<r>: natural_isomorphism comp comp
                     \<open>\<lambda>f. fst (f, w) \<star> snd (f, w)\<close> map \<open>\<lambda>f. \<rr> f \<cdot> (dom f \<star> \<phi>)\<close>
      proof
        fix \<mu>
        show "\<not> arr \<mu> \<Longrightarrow> \<rr> \<mu> \<cdot> (dom \<mu> \<star> \<phi>) = null"
          using \<phi> arr_char dom_char ext
          apply simp
          using comp_null(2) hcomp_def by fastforce
        assume \<mu>: "arr \<mu>"
        have 0: "in_hhom (dom \<mu>) a a"
          using \<mu> arr_char src_dom trg_dom src_def trg_def by simp
        have 1: "in_hhom \<phi> a a"
          using \<phi> arr_char src_dom trg_dom src_def trg_def by auto
        have 2: "hseq (B.dom \<mu>) \<phi>"
          using \<mu> 0 1 by auto
        have 3: "seq (\<rr> \<mu>) (dom \<mu> \<star> \<phi>)"
        proof (intro seqI')
          show "\<guillemotleft>dom \<mu> \<star> \<phi> : dom \<mu> \<star> w \<Rightarrow> dom \<mu> \<star> a\<guillemotright>"
            by (metis (no_types, lifting) "0" "1" \<mu> \<phi> hcomp_in_vhom hseqI hseq_char
                ide_dom ide_in_hom(2) vconn_implies_hpar(2))
          show "\<guillemotleft>\<rr> \<mu> : dom \<mu> \<star> a \<Rightarrow> cod \<mu>\<guillemotright>"
            using \<mu> 2 \<rr>.preserves_hom [of \<mu> "dom \<mu>" "cod \<mu>"] arr_simps(2) arr_cod by fastforce
        qed
        show "dom (\<rr> \<mu> \<cdot> (dom \<mu> \<star> \<phi>)) = fst (dom \<mu>, w) \<star> snd (dom \<mu>, w)"
        proof -
          have "dom (\<rr> \<mu> \<cdot> (dom \<mu> \<star> \<phi>)) = dom \<mu> \<star> dom \<phi>"
            using \<mu> 3 hcomp_simps(3) dom_comp dom_dom
            apply (elim seqE) by auto
          also have "... = fst (dom \<mu>, w) \<star> snd (dom \<mu>, w)"
            using \<omega>_in_vhom \<phi>
            by (metis (no_types, lifting) in_homE prod.sel(1) prod.sel(2))
          finally show ?thesis by simp
        qed
        show "cod (\<rr> \<mu> \<cdot> (dom \<mu> \<star> \<phi>)) = map (cod \<mu>)"
        proof -
          have "seq (\<rr> \<mu>) (dom \<mu> \<star> \<phi>)"
            using 3 by simp
          hence "cod (\<rr> \<mu> \<cdot> (dom \<mu> \<star> \<phi>)) = cod (\<rr> \<mu>)"
            using cod_comp by blast
          also have "... = map (cod \<mu>)"
            using \<mu> by blast
          finally show ?thesis by blast
        qed
        show "map \<mu> \<cdot> \<rr> (dom \<mu>) \<cdot> (dom (dom \<mu>) \<star> \<phi>) = \<rr> \<mu> \<cdot> (dom \<mu> \<star> \<phi>)"
        proof -
          have "map \<mu> \<cdot> \<rr> (dom \<mu>) \<cdot> (dom (dom \<mu>) \<star> \<phi>) =
                (map \<mu> \<cdot> \<rr> (dom \<mu>)) \<cdot> (dom (dom \<mu>) \<star> \<phi>)"
            using comp_assoc by simp
          also have "... = (map \<mu> \<cdot> \<rr> (dom \<mu>)) \<cdot> (dom \<mu> \<star> \<phi>)"
            using \<mu> dom_dom by simp
          also have "... = \<rr> \<mu> \<cdot> (dom \<mu> \<star> \<phi>)"
            using \<mu> \<phi> \<rr>.is_natural_1 by auto
          finally show ?thesis by blast
        qed
        show "(\<rr> (cod \<mu>) \<cdot> (dom (cod \<mu>) \<star> \<phi>)) \<cdot> (fst (\<mu>, w) \<star> snd (\<mu>, w)) = \<rr> \<mu> \<cdot> (dom \<mu> \<star> \<phi>)"
        proof -
          have "(\<rr> (cod \<mu>) \<cdot> (dom (cod \<mu>) \<star> \<phi>)) \<cdot> (fst (\<mu>, w) \<star> snd (\<mu>, w)) =
                (\<rr> (cod \<mu>) \<cdot> (B.cod \<mu> \<star> \<phi>)) \<cdot> (\<mu> \<star> w)"
            using \<mu> \<phi> dom_char arr_char \<omega>_in_vhom by simp
          also have "... = \<rr> (cod \<mu>) \<cdot> (B.cod \<mu> \<cdot> \<mu> \<star> \<phi> \<cdot> w)"
          proof -
            have 2: "seq \<phi> w"
              using \<phi> \<omega>_in_vhom w_simps(1) by blast
            moreover have "seq (B.cod \<mu>) \<mu>"
              using \<mu> seq_char by (simp add: comp_cod_arr)
            moreover have "src (B.cod \<mu>) = trg \<phi>"
              using \<mu> \<phi> 2
              by (metis (no_types, lifting) arrE cod_closed src_def vseq_implies_hpar(2)
                  w_simps(4))
            ultimately show ?thesis
              using interchange comp_assoc by simp
          qed
          also have "... = \<rr> (cod \<mu>) \<cdot> (\<mu> \<star> \<phi>)"
            using \<mu> \<phi> \<omega>_in_vhom comp_arr_dom comp_cod_arr cod_simp
            apply (elim conjE in_homE) by auto
          also have "... = (\<rr> (cod \<mu>) \<cdot> (\<mu> \<star> cod \<phi>)) \<cdot> (dom \<mu> \<star> \<phi>)"
          proof -
            have "(\<mu> \<star> cod \<phi>) \<cdot> (dom \<mu> \<star> \<phi>) = \<mu> \<star> \<phi>"
            proof -
              have "seq \<mu> (dom \<mu>)"
                using \<mu> by (simp add: comp_arr_dom)
              moreover have "seq (cod \<phi>) \<phi>"
                using \<phi> iso_is_arr arr_cod dom_cod by auto
              moreover have "src \<mu> = trg (cod \<phi>)"
                using \<mu> \<phi> 2
                by (metis (no_types, lifting) arr_simps(1) arr_simps(2) calculation(2) seqE)
              ultimately show ?thesis
                using \<mu> \<phi> iso_is_arr comp_arr_dom comp_cod_arr
                      interchange [of \<mu> "dom \<mu>" "cod \<phi>" \<phi>]
                by simp
            qed
            thus ?thesis
              using comp_assoc by simp
          qed
          also have "... = \<rr> \<mu> \<cdot> (dom \<mu> \<star> \<phi>)"
          proof -
            have "\<mu> \<star> cod \<phi> = R \<mu>"
              using \<mu> \<phi> arr_simps(1) in_homE by auto
            hence "\<rr> (cod \<mu>) \<cdot> (\<mu> \<star> cod \<phi>) = \<rr> \<mu>"
              using \<mu> \<phi> \<rr>.is_natural_2 by simp
            thus ?thesis by simp
          qed
          finally show ?thesis by simp
        qed
        next
        show "\<And>f. ide f \<Longrightarrow> iso (\<rr> f \<cdot> (dom f \<star> \<phi>))"
        proof -
          fix f
          assume f: "ide f"
          have 1: "iso (\<rr> f)"
            using f iso_lunit by simp
          moreover have 2: "iso (dom f \<star> \<phi>)"
            using \<phi> f src_def trg_def ide_char arr_char
            apply (intro iso_hcomp, simp_all)
            by (metis (no_types, lifting) in_homE)
          moreover have "seq (\<rr> f) (dom f \<star> \<phi>)"
          proof (intro seqI')
            show "\<guillemotleft>\<rr> f : f \<star> a \<Rightarrow> f\<guillemotright>"
              using f runit_in_hom(2) \<rr>_ide_simp ide_char arr_char src_def by simp
            show "\<guillemotleft>dom f \<star> \<phi> : f \<star> w \<Rightarrow> f \<star> a\<guillemotright>"
              using \<phi> f ide_char arr_char hcomp_def src_def trg_def obj_a ide_in_hom
                    in_hom_char
              by (intro hcomp_in_vhom, auto)
          qed
          ultimately show "iso (\<rr> f \<cdot> (dom f \<star> \<phi>))"
            using isos_compose by simp
         qed
      qed
      show "equivalence_functor (\<cdot>) (\<cdot>) (\<lambda>f. fst (f, w) \<star> snd (f, w))"
        using \<r>.natural_isomorphism_axioms R.isomorphic_to_identity_is_equivalence by simp
    qed
    interpretation R: equivalence_functor \<open>(\<cdot>)\<close> \<open>(\<cdot>)\<close> \<open>\<lambda>f. fst (f, cod \<omega>) \<star> snd (f, cod \<omega>)\<close>
    proof -
      have "(\<lambda>f. fst (f, cod \<omega>) \<star> snd (f, cod \<omega>)) = (\<lambda>f. fst (f, w) \<star> snd (f, w))"
        using \<omega>_in_vhom by simp
      thus "equivalence_functor (\<cdot>) (\<cdot>) (\<lambda>f. fst (f, cod \<omega>) \<star> snd (f, cod \<omega>))"
        using R'.equivalence_functor_axioms by simp
    qed

    interpretation M: monoidal_category \<open>(\<cdot>)\<close> \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu>\<close> \<alpha> \<omega>
    proof
      show "\<guillemotleft>\<omega> : fst (cod \<omega>, cod \<omega>) \<star> snd (cod \<omega>, cod \<omega>) \<Rightarrow> cod \<omega>\<guillemotright>"
        using \<omega>_in_vhom hcomp_def arr_char by auto
      show "iso \<omega>"
        using \<omega>_is_iso iso_char arr_char inv_char \<omega>_in_vhom by auto
      show "\<And>f g h k. \<lbrakk> ide f; ide g; ide h; ide k \<rbrakk> \<Longrightarrow>
                       (fst (f, \<alpha> (g, h, k)) \<star> snd (f, \<alpha> (g, h, k))) \<cdot>
                         \<alpha> (f, hcomp (fst (g, h)) (snd (g, h)), k) \<cdot>
                         (fst (\<alpha> (f, g, h), k) \<star> snd (\<alpha> (f, g, h), k)) =
                       \<alpha> (f, g, fst (h, k) \<star> snd (h, k)) \<cdot> \<alpha> (fst (f, g) \<star> snd (f, g), h, k)"
      proof -
        fix f g h k
        assume f: "ide f" and g: "ide g" and h: "ide h" and k: "ide k"
        have 1: "VVV.arr (f, g, h) \<and> VVV.arr (g, h, k)"
          using f g h k VVV.arr_char VV.arr_char src_def trg_def ide_char arr_char
          by simp
        have 2: "VVV.arr (f, g \<star> h, k)"
          using f g h k 1 HoHV_def VVV.arr_char VV.arr_char src_def trg_def ide_char arr_char
                VxV.arrI VxVxV.arrI VxVxV_comp_eq_VVV_comp hseqI'
          by auto
        have 3: "VVV.arr (f, g, h \<star> k)"
          using f g h k 1 VVV.arr_char VV.arr_char src_def trg_def ide_char arr_char
                VxV.arrI VxVxV.arrI VxVxV_comp_eq_VVV_comp H.preserves_reflects_arr hseqI'
          by auto
        have 4: "VVV.arr (f \<star> g, h, k)"
          using f g h k VVV.arr_char VV.arr_char src_def trg_def ide_char arr_char hseq_char
                VxV.arrI VxVxV.arrI VxVxV_comp_eq_VVV_comp
          by force
        have "(fst (f, \<alpha> (g, h, k)) \<star> snd (f, \<alpha> (g, h, k))) \<cdot>
                \<alpha> (f, fst (g, h) \<star> snd (g, h), k) \<cdot>
                (fst (\<alpha> (f, g, h), k) \<star> snd (\<alpha> (f, g, h), k)) =
              (f \<star> \<a>\<^sub>B[g, h, k]) \<cdot> \<a>\<^sub>B[f, g \<star> h, k] \<cdot> (\<a>\<^sub>B[f, g, h] \<star> k)"
          unfolding \<alpha>_def by (simp add: 1 2)
        also have "... = (f \<star>\<^sub>B \<a>\<^sub>B g h k) \<cdot> \<a>\<^sub>B f (g \<star>\<^sub>B h) k \<cdot> (\<a>\<^sub>B f g h \<star>\<^sub>B k)"
          unfolding hcomp_def
          using f g h k src_def trg_def arr_char
          using assoc_closed ide_char by auto
        also have "... = (f \<star>\<^sub>B \<a>\<^sub>B g h k) \<cdot>\<^sub>B \<a>\<^sub>B f (g \<star>\<^sub>B h) k \<cdot>\<^sub>B (\<a>\<^sub>B f g h \<star>\<^sub>B k)"
        proof -
          have "arr (f \<star>\<^sub>B \<a>\<^sub>B g h k)"
            using ide_char arr_char assoc_closed f g h hcomp_closed k by simp
          moreover have "arr (\<a>\<^sub>B f (g \<star>\<^sub>B h) k)"
            using ide_char arr_char assoc_closed f g h hcomp_closed k by simp
          moreover have "arr (\<a>\<^sub>B f g h \<star>\<^sub>B k)"
            using ide_char arr_char assoc_closed f g h hcomp_closed k by simp
          moreover have "arr (\<a>\<^sub>B f (g \<star>\<^sub>B h) k \<cdot>\<^sub>B (\<a>\<^sub>B f g h \<star>\<^sub>B k))"
            unfolding arr_char
            apply (intro conjI)
            using ide_char arr_char assoc_closed f g h hcomp_closed k B.HoHV_def B.HoVH_def
            apply (intro B.seqI)
                apply simp_all
          proof -
            have 1: "B.arr (\<a>\<^sub>B f (g \<star>\<^sub>B h) k \<cdot>\<^sub>B \<a>\<^sub>B f g h \<star>\<^sub>B k)"
              using f g h k ide_char arr_char B.HoHV_def B.HoVH_def
              apply (intro B.seqI)
              by auto
            show "src\<^sub>B (\<a>\<^sub>B f (g \<star>\<^sub>B h) k \<cdot>\<^sub>B \<a>\<^sub>B f g h \<star>\<^sub>B k) = a"
              using 1 f g h k arr_char B.src_vcomp B.vseq_implies_hpar(1) by fastforce
            show "trg\<^sub>B (\<a>\<^sub>B f (g \<star>\<^sub>B h) k \<cdot>\<^sub>B \<a>\<^sub>B f g h \<star>\<^sub>B k) = a"
              using "1" arr_char calculation(2-3) by auto
          qed
          ultimately show ?thesis
            using B.ext comp_char by (metis (no_types, lifting))
        qed
        also have "... = \<a>\<^sub>B f g (h \<star>\<^sub>B k) \<cdot>\<^sub>B \<a>\<^sub>B (f \<star>\<^sub>B g) h k"
          using f g h k src_def trg_def arr_char ide_char B.pentagon
          using "4" \<alpha>_def hcomp_def by auto
        also have "... = \<a>\<^sub>B f g (h \<star>\<^sub>B k) \<cdot> \<a>\<^sub>B (f \<star>\<^sub>B g) h k"
        proof -
          have "arr (\<a>\<^sub>B (f \<star>\<^sub>B g) h k)"
            using ide_char arr_char assoc_closed f g h hcomp_closed k by simp
          moreover have "arr (\<a>\<^sub>B f g (h \<star>\<^sub>B k))"
            using ide_char arr_char assoc_closed f g h hcomp_closed k by fastforce
          ultimately show ?thesis
            using B.ext comp_char by auto
        qed
        also have "... = \<a>\<^sub>B[f, g, fst (h, k) \<star> snd (h, k)] \<cdot> \<a>\<^sub>B[fst (f, g) \<star> snd (f, g), h, k]"
          unfolding hcomp_def
          using f g h k src_def trg_def arr_char ide_char by simp
        also have "... = \<alpha> (f, g, fst (h, k) \<star> snd (h, k)) \<cdot> \<alpha> (fst (f, g) \<star> snd (f, g), h, k)"
          unfolding \<alpha>_def using 1 2 3 4 by simp
        finally show "(fst (f, \<alpha> (g, h, k)) \<star> snd (f, \<alpha> (g, h, k))) \<cdot>
                        \<alpha> (f, fst (g, h) \<star> snd (g, h), k) \<cdot>
                        (fst (\<alpha> (f, g, h), k) \<star> snd (\<alpha> (f, g, h), k)) =
                      \<alpha> (f, g, fst (h, k) \<star> snd (h, k)) \<cdot> \<alpha> (fst (f, g) \<star> snd (f, g), h, k)"
          by simp
      qed
    qed

    proposition is_monoidal_category:
    shows "monoidal_category (\<cdot>) (\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu>) \<alpha> \<omega>"
      ..

  end

  text \<open>
    In a bicategory, the ``objects'' are essentially arbitrarily chosen representatives
    of their isomorphism classes.  Choosing any other representatives results in an
    equivalent structure.  Each object \<open>a\<close> is additionally equipped with an arbitrarily chosen
    unit isomorphism \<open>\<guillemotleft>\<iota> : a \<star> a \<Rightarrow> a\<guillemotright>\<close>.  For any \<open>(a, \<iota>)\<close> and \<open>(a', \<iota>')\<close>,
    where \<open>a\<close> and \<open>a'\<close> are isomorphic to the same object, there exists a unique isomorphism
    \<open>\<guillemotleft>\<psi>: a \<Rightarrow> a'\<guillemotright>\<close> that is compatible with the chosen unit isomorphisms \<open>\<iota>\<close> and \<open>\<iota>'\<close>.
    We have already proved this property for monoidal categories, which are bicategories
    with just one ``object''.  Here we use that already-proven property to establish its
    generalization to arbitary bicategories, by exploiting the fact that if \<open>a\<close> is an object
    in a bicategory, then the sub-bicategory consisting of all \<open>\<mu>\<close> such that
    \<open>src \<mu> = a = trg \<mu>\<close>, is a monoidal category.

    At some point it would potentially be nicer to transfer the proof for monoidal
    categories to obtain a direct, ``native'' proof of this fact for bicategories.
  \<close>

  lemma (in bicategory) unit_unique_upto_unique_iso:
  assumes "obj a"
  and "isomorphic a w"
  and "\<guillemotleft>\<omega> : w \<star> w \<Rightarrow> w\<guillemotright>"
  and "iso \<omega>"
  shows "\<exists>!\<psi>. \<guillemotleft>\<psi> : a \<Rightarrow> w\<guillemotright> \<and> iso \<psi> \<and> \<psi> \<cdot> \<i>[a] = \<omega> \<cdot> (\<psi> \<star> \<psi>)"
  proof -
    have \<omega>_in_hhom: "\<guillemotleft>\<omega> : a \<rightarrow> a\<guillemotright>"
      using assms
      apply (intro in_hhomI)
        apply auto
       apply (metis src_cod in_homE isomorphic_implies_hpar(3) objE)
      by (metis trg_cod in_homE isomorphic_implies_hpar(4) objE)
    interpret S: subbicategory V H \<a> \<i> src trg \<open>\<lambda>\<mu>. arr \<mu> \<and> src \<mu> = a \<and> trg \<mu> = a\<close>
      using assms iso_unit in_homE isoE isomorphicE VVV.arr_char VV.arr_char
      apply unfold_locales
                 apply auto[7]
    proof
      fix f g h
      assume f: "(arr f \<and> src f = a \<and> trg f = a) \<and> ide f"
      and g: "(arr g \<and> src g = a \<and> trg g = a) \<and> ide g"
      and h: "(arr h \<and> src h = a \<and> trg h = a) \<and> ide h"
      and fg: "src f = trg g" and gh: "src g = trg h"
      show "arr (\<a>[f, g, h])"
        using assms f g h fg gh by auto
      show "src (\<a>[f, g, h]) = a \<and> trg (\<a>[f, g, h]) = a"
        using assms f g h fg gh by auto
      show "arr (inv (\<a>[f, g, h])) \<and> src (inv (\<a>[f, g, h])) = a \<and> trg (inv (\<a>[f, g, h])) = a"
        using assms f g h fg gh \<alpha>.preserves_hom src_dom trg_dom by simp
      next
      fix f
      assume f: "arr f \<and> src f = a \<and> trg f = a"
      assume ide_left: "ide f"
      show "arr (\<ll> f) \<and> src (\<ll> f) = a \<and> trg (\<ll> f) = a"
        using f assms(1) \<ll>.preserves_hom src_cod [of "\<ll> f"] trg_cod [of "\<ll> f"] by simp
      show "arr (inv (\<ll> f)) \<and> src (inv (\<ll> f)) = a \<and> trg (inv (\<ll> f)) = a"
        using f ide_left assms(1) \<ll>'.preserves_hom src_dom [of "\<ll>'.map f"] trg_dom [of "\<ll>'.map f"]
        by simp
      show "arr (\<rr> f) \<and> src (\<rr> f) = a \<and> trg (\<rr> f) = a"
        using f assms(1) \<rr>.preserves_hom src_cod [of "\<rr> f"] trg_cod [of "\<rr> f"] by simp
      show "arr (inv (\<rr> f)) \<and> src (inv (\<rr> f)) = a \<and> trg (inv (\<rr> f)) = a"
        using f ide_left assms(1) \<rr>'.preserves_hom src_dom [of "\<rr>'.map f"] trg_dom [of "\<rr>'.map f"]
        by simp
    qed
    interpret S: subbicategory_at_object V H \<a> \<i> src trg a a \<open>\<i>[a]\<close>
    proof
      show "obj a" by fact
      show "isomorphic a a"
        using assms(1) isomorphic_reflexive by blast
      show "S.in_hom \<i>[a] (a \<star> a) a"
        by (metis (no_types, lifting) S.hcomp_def S.obj_char S.unit_in_vhom assms(1)
              obj_def obj_self_composable(1) seq_if_composable)
      show "iso \<i>[a]"
        using assms iso_unit by simp
    qed
    interpret S\<^sub>\<omega>: subbicategory_at_object V H \<a> \<i> src trg a w \<omega>
    proof
      show "obj a" by fact
      show "iso \<omega>" by fact
      show "isomorphic a w"
        using assms by simp
      show "S.in_hom \<omega> (w \<star> w) w"
        using assms S.arr_char S.dom_char S.cod_char \<omega>_in_hhom
        by (intro S.in_homI, auto)
    qed
    interpret M: monoidal_category S.comp \<open>\<lambda>\<mu>\<nu>. S.hcomp (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close> S.\<alpha> \<open>\<i>[a]\<close>
      using S.is_monoidal_category by simp
    interpret M\<^sub>\<omega>: monoidal_category S.comp \<open>\<lambda>\<mu>\<nu>. S.hcomp (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close> S.\<alpha> \<omega>
      using S\<^sub>\<omega>.is_monoidal_category by simp
    interpret M: monoidal_category_with_alternate_unit
                   S.comp \<open>\<lambda>\<mu>\<nu>. S.hcomp (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close> S.\<alpha> \<open>\<i>[a]\<close> \<omega> ..
    have 1: "M\<^sub>\<omega>.unity = w"
      using assms M\<^sub>\<omega>.unity_def S.cod_char S.arr_char
      by (metis (no_types, lifting) S.in_homE S\<^sub>\<omega>.\<omega>_in_vhom)
    have 2: "M.unity = a"
      using assms M.unity_def S.cod_char S.arr_char by simp
    have "\<exists>!\<psi>. S.in_hom \<psi> a w \<and> S.iso \<psi> \<and> S.comp \<psi> \<i>[a] = S.comp \<omega> (M.tensor \<psi> \<psi>)"
      using assms 1 2 M.unit_unique_upto_unique_iso M.unity_def M\<^sub>\<omega>.unity_def S.cod_char
      by simp
    show "\<exists>!\<psi>. \<guillemotleft>\<psi> : a \<Rightarrow> w\<guillemotright> \<and> iso \<psi> \<and> \<psi> \<cdot> \<i>[a] = \<omega> \<cdot> (\<psi> \<star> \<psi>)"
    proof -
      have 1: "\<And>\<psi>. S.in_hom \<psi> a w \<longleftrightarrow> \<guillemotleft>\<psi> : a \<Rightarrow> w\<guillemotright>"
        using assms S.in_hom_char S.arr_char
        by (metis (no_types, lifting) S.ideD(1) S.w_simps(1) S\<^sub>\<omega>.w_simps(1) in_homE
            src_dom trg_dom)
      moreover have "\<And>\<psi>. S.in_hom \<psi> a w \<Longrightarrow> S.iso \<psi> \<longleftrightarrow> iso \<psi>"
        using assms S.in_hom_char S.arr_char S.iso_char by auto
      moreover have "\<And>\<psi>. S.in_hom \<psi> a w \<Longrightarrow> M.tensor \<psi> \<psi> = \<psi> \<star> \<psi>"
        using assms S.in_hom_char S.arr_char S.hcomp_def by simp
      moreover have "\<And>\<psi>. S.in_hom \<psi> a w \<Longrightarrow> S.comp \<psi> \<i>[a] = \<psi> \<cdot> \<i>[a]"
        using assms S.in_hom_char S.comp_char by auto
      moreover have "\<And>\<psi>. S.in_hom \<psi> a w \<Longrightarrow> S.comp \<omega> (M.tensor \<psi> \<psi>) = \<omega> \<cdot> (\<psi> \<star> \<psi>)"
        using assms S.in_hom_char S.arr_char S.hcomp_def S.comp_char S.dom_char S.cod_char
        by (metis (no_types, lifting) M\<^sub>\<omega>.arr_tensor S\<^sub>\<omega>.\<omega>_simps(1) calculation(3) ext)
      ultimately show ?thesis
        by (metis (no_types, lifting) M.unit_unique_upto_unique_iso M.unity_def M\<^sub>\<omega>.unity_def
            S.\<omega>_in_vhom S.in_homE S\<^sub>\<omega>.\<omega>_in_vhom)
    qed
  qed

end
