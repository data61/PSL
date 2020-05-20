(*  Title:       EpiMonoIso
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter EpiMonoIso

theory EpiMonoIso
imports Category
begin

  text\<open>
    This theory defines and develops properties of epimorphisms, monomorphisms,
    isomorphisms, sections, and retractions.
\<close>

  context category
  begin

     definition epi
     where "epi f = (arr f \<and> inj_on (\<lambda>g. g \<cdot> f) {g. seq g f})"

     definition mono
     where "mono f = (arr f \<and> inj_on (\<lambda>g. f \<cdot> g) {g. seq f g})"

     lemma epiI [intro]:
     assumes "arr f" and "\<And>g g'. seq g f \<and> seq g' f \<and> g \<cdot> f = g' \<cdot> f \<Longrightarrow> g = g'"
     shows "epi f"
       using assms epi_def inj_on_def by blast

     lemma epi_implies_arr:
     assumes "epi f"
     shows "arr f"
       using assms epi_def by auto

     lemma epiE [elim]:
     assumes "epi f"
     and "seq g f" and "seq g' f" and "g \<cdot> f = g' \<cdot> f"
     shows "g = g'"
       using assms unfolding epi_def inj_on_def by blast
       
     lemma monoI [intro]:
     assumes "arr g" and "\<And>f f'. seq g f \<and> seq g f' \<and> g \<cdot> f = g \<cdot> f' \<Longrightarrow> f = f'"
     shows "mono g"
       using assms mono_def inj_on_def by blast

     lemma mono_implies_arr:
     assumes "mono f"
     shows "arr f"
       using assms mono_def by auto
       
     lemma monoE [elim]:
     assumes "mono g"
     and "seq g f" and "seq g f'" and "g \<cdot> f = g \<cdot> f'"
     shows "f' = f"
       using assms unfolding mono_def inj_on_def by blast

     definition inverse_arrows
     where "inverse_arrows f g \<equiv> ide (g \<cdot> f) \<and> ide (f \<cdot> g)"

     lemma inverse_arrowsI [intro]:
     assumes "ide (g \<cdot> f)" and "ide (f \<cdot> g)"
     shows "inverse_arrows f g"
       using assms inverse_arrows_def by blast

     lemma inverse_arrowsE [elim]:
     assumes "inverse_arrows f g"
     and "\<lbrakk> ide (g \<cdot> f); ide (f \<cdot> g) \<rbrakk> \<Longrightarrow> T"
     shows "T"
       using assms inverse_arrows_def by blast

     lemma inverse_arrows_sym:
       shows "inverse_arrows f g \<longleftrightarrow> inverse_arrows g f"
       using inverse_arrows_def by auto

     lemma ide_self_inverse:
     assumes "ide a"
     shows "inverse_arrows a a"
       using assms by auto

     lemma inverse_arrow_unique:
     assumes "inverse_arrows f g" and "inverse_arrows f g'"
     shows "g = g'"
       using assms apply (elim inverse_arrowsE)
       by (metis comp_cod_arr ide_compE comp_assoc seqE)

     lemma inverse_arrows_compose:
     assumes "seq g f" and "inverse_arrows f f'" and "inverse_arrows g g'"
     shows "inverse_arrows (g \<cdot> f) (f' \<cdot> g')"
       using assms apply (elim inverse_arrowsE, intro inverse_arrowsI)
        apply (metis seqE comp_arr_dom ide_compE comp_assoc)
       by (metis seqE comp_arr_dom ide_compE comp_assoc)

     definition "section"
     where "section f \<equiv> \<exists>g. ide (g \<cdot> f)"

     lemma sectionI [intro]:
     assumes "ide (g \<cdot> f)"
     shows "section f"
       using assms section_def by auto

     lemma sectionE [elim]:
     assumes "section f"
     obtains g where "ide (g \<cdot> f)"
       using assms section_def by blast

     definition retraction
     where "retraction g \<equiv> \<exists>f. ide (g \<cdot> f)"

     lemma retractionI [intro]:
     assumes "ide (g \<cdot> f)"
     shows "retraction g"
       using assms retraction_def by auto

     lemma retractionE [elim]:
     assumes "retraction g"
     obtains f where "ide (g \<cdot> f)"
       using assms retraction_def by blast
       
     lemma section_is_mono:
     assumes "section g"
     shows "mono g"
     proof
       show "arr g" using assms section_def by blast
       from assms obtain h where h: "ide (h \<cdot> g)" by blast
       have hg: "seq h g" using h by auto
       fix f f'
       assume "seq g f \<and> seq g f' \<and> g \<cdot> f = g \<cdot> f'"
       thus "f = f'"
         using hg h ide_compE seqE comp_assoc comp_cod_arr by metis
     qed

     lemma retraction_is_epi:
     assumes "retraction g"
     shows "epi g"
     proof
       show "arr g" using assms retraction_def by blast
       from assms obtain f where f: "ide (g \<cdot> f)" by blast
       have gf: "seq g f" using f by auto
       fix h h'
       assume "seq h g \<and> seq h' g \<and> h \<cdot> g = h' \<cdot> g"
       thus "h = h'"
         using gf f ide_compE seqE comp_assoc comp_arr_dom by metis
     qed

     lemma section_retraction_compose:
     assumes "ide (e \<cdot> m)" and "ide (e' \<cdot> m')" and "seq m' m"
     shows "ide ((e \<cdot> e') \<cdot> (m' \<cdot> m))"
       using assms seqI seqE ide_compE comp_assoc comp_arr_dom by metis

     lemma sections_compose [intro]:
     assumes "section m" and "section m'" and "seq m' m"
     shows "section (m' \<cdot> m)"
       using assms section_def section_retraction_compose by metis

     lemma retractions_compose [intro]:
     assumes "retraction e" and "retraction e'" and "seq e' e"
     shows "retraction (e' \<cdot> e)"
     proof -
       from assms(1-2) obtain m m'
       where *: "ide (e \<cdot> m) \<and> ide (e' \<cdot> m')"
         using retraction_def by auto
       hence "seq m m'"
         using assms(3) by (metis seqE seqI ide_compE)
       with * show ?thesis
         using section_retraction_compose retractionI by blast
     qed
       
     lemma monos_compose [intro]:
     assumes "mono m" and "mono m'" and "seq m' m"
     shows "mono (m' \<cdot> m)"
     proof -
       have "inj_on (\<lambda>f. (m' \<cdot> m) \<cdot> f) {f. seq (m' \<cdot> m) f}"
         unfolding inj_on_def
         using assms
         by (metis CollectD seqE monoE comp_assoc)
       thus ?thesis using assms(3) mono_def by force
     qed           

     lemma epis_compose [intro]:
     assumes "epi e" and "epi e'" and "seq e' e"
     shows "epi (e' \<cdot> e)"
     proof -
       have "inj_on (\<lambda>g. g \<cdot> (e' \<cdot> e)) {g. seq g (e' \<cdot> e)}"
         unfolding inj_on_def
         using assms by (metis CollectD epiE match_2 comp_assoc)
       thus ?thesis using assms(3) epi_def by force
     qed           

     definition iso
     where "iso f \<equiv> \<exists>g. inverse_arrows f g"

     lemma isoI [intro]:
     assumes "inverse_arrows f g"
     shows "iso f"
       using assms iso_def by auto

     lemma isoE [elim]:
     assumes "iso f"
     obtains g where "inverse_arrows f g"
       using assms iso_def by blast

     lemma ide_is_iso [simp]:
     assumes "ide a"
     shows "iso a"
       using assms ide_self_inverse by auto

     lemma iso_is_arr:
     assumes "iso f"
     shows "arr f"
       using assms by blast

     lemma iso_is_section:
     assumes "iso f"
     shows "section f"
       using assms inverse_arrows_def by blast

     lemma iso_is_retraction:
     assumes "iso f"
     shows "retraction f"
       using assms inverse_arrows_def by blast

    lemma iso_iff_mono_and_retraction:
    shows "iso f \<longleftrightarrow> mono f \<and> retraction f"
    proof
      show "iso f \<Longrightarrow> mono f \<and> retraction f"
        by (simp add: iso_is_retraction iso_is_section section_is_mono)
      show "mono f \<and> retraction f \<Longrightarrow> iso f"
      proof -
        assume f: "mono f \<and> retraction f"
        from f obtain g where g: "ide (f \<cdot> g)" by blast
        have "inverse_arrows f g"
          using f g comp_arr_dom comp_cod_arr comp_assoc inverse_arrowsI
          by (metis ide_char' ide_compE monoE mono_implies_arr)
        thus "iso f" by auto
      qed
    qed

    lemma iso_iff_section_and_epi:
    shows "iso f \<longleftrightarrow> section f \<and> epi f"
    proof
      show "iso f \<Longrightarrow> section f \<and> epi f"
        by (simp add: iso_is_retraction iso_is_section retraction_is_epi)
      show "section f \<and> epi f \<Longrightarrow> iso f"
      proof -
        assume f: "section f \<and> epi f"
        from f obtain g where g: "ide (g \<cdot> f)" by blast
        have "inverse_arrows f g"
          using f g comp_arr_dom comp_cod_arr epi_implies_arr
                comp_assoc ide_compE inverse_arrowsI epiE ide_char'
          by metis
        thus "iso f" by auto
      qed
    qed

    lemma iso_iff_section_and_retraction:
    shows "iso f \<longleftrightarrow> section f \<and> retraction f"
      using iso_is_retraction iso_is_section iso_iff_mono_and_retraction section_is_mono
      by auto

    lemma isos_compose [intro]:
    assumes "iso f" and "iso f'" and "seq f' f"
    shows "iso (f' \<cdot> f)"
    proof -
      from assms(1) obtain g where g: "inverse_arrows f g" by blast
      from assms(2) obtain g' where g': "inverse_arrows f' g'" by blast
      have "inverse_arrows (f' \<cdot> f) (g \<cdot> g')"
        using assms g g inverse_arrowsI inverse_arrowsE section_retraction_compose
        by (simp add: g' inverse_arrows_compose)
      thus ?thesis using iso_def by auto
    qed

    definition isomorphic
    where "isomorphic a a' = (\<exists>f. \<guillemotleft>f : a \<rightarrow> a'\<guillemotright> \<and> iso f)"

    lemma isomorphicI [intro]:
    assumes "iso f"
    shows "isomorphic (dom f) (cod f)"
      using assms isomorphic_def iso_is_arr by blast

    lemma isomorphicE [elim]:
    assumes "isomorphic a a'"
    obtains f where "\<guillemotleft>f : a \<rightarrow> a'\<guillemotright> \<and> iso f"
      using assms isomorphic_def by meson

    definition inv
    where "inv f = (SOME g. inverse_arrows f g)"

    lemma inv_is_inverse:
    assumes "iso f"
    shows "inverse_arrows f (inv f)"
      using assms inv_def someI [of "inverse_arrows f"] by auto

    lemma iso_inv_iso:
    assumes "iso f"
    shows "iso (inv f)"
      using assms inv_is_inverse inverse_arrows_sym by blast

    lemma inverse_unique:
    assumes "inverse_arrows f g"
    shows "inv f = g"
      using assms inv_is_inverse inverse_arrow_unique isoI by auto

    lemma inv_ide [simp]:
    assumes "ide a"
    shows "inv a = a"
      using assms by (simp add: inverse_arrowsI inverse_unique)

    lemma inv_inv [simp]:
    assumes "iso f"
    shows "inv (inv f) = f"
      using assms inverse_arrows_sym inverse_unique by blast

    lemma comp_arr_inv:
    assumes "inverse_arrows f g"
    shows "f \<cdot> g = dom g"
      using assms by auto

    lemma comp_inv_arr:
    assumes "inverse_arrows f g"
    shows "g \<cdot> f = dom f"
      using assms by auto

    lemma comp_arr_inv':
    assumes "iso f"
    shows "f \<cdot> inv f = cod f"
      using assms inv_is_inverse by blast

    lemma comp_inv_arr':
    assumes "iso f"
    shows "inv f \<cdot> f = dom f"
      using assms inv_is_inverse by blast

    lemma inv_in_hom [simp]:
    assumes "iso f" and "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
    shows "\<guillemotleft>inv f : b \<rightarrow> a\<guillemotright>"
      using assms inv_is_inverse seqE inverse_arrowsE
      by (metis ide_compE in_homE in_homI)

    lemma arr_inv [simp]:
    assumes "iso f"
    shows "arr (inv f)"
      using assms inv_in_hom by blast

    lemma dom_inv [simp]:
    assumes "iso f"
    shows "dom (inv f) = cod f"
      using assms inv_in_hom by blast

    lemma cod_inv [simp]:
    assumes "iso f"
    shows "cod (inv f) = dom f"
      using assms inv_in_hom by blast

    lemma inv_comp:
    assumes "iso f" and "iso g" and "seq g f"
    shows "inv (g \<cdot> f) = inv f \<cdot> inv g"
      using assms inv_is_inverse inverse_unique inverse_arrows_compose inverse_arrows_def
      by meson

    lemma isomorphic_reflexive:
    assumes "ide f"
    shows "isomorphic f f"
      unfolding isomorphic_def
      using assms ide_is_iso ide_in_hom by blast

    lemma isomorphic_symmetric:
    assumes "isomorphic f g"
    shows "isomorphic g f"
      using assms iso_inv_iso inv_in_hom by blast

    lemma isomorphic_transitive [trans]:
    assumes "isomorphic f g" and "isomorphic g h"
    shows "isomorphic f h"
      using assms isomorphic_def isos_compose by auto

    text \<open>
      A section or retraction of an isomorphism is in fact an inverse.
\<close>

    lemma section_retraction_of_iso:
    assumes "iso f"
    shows "ide (g \<cdot> f) \<Longrightarrow> inverse_arrows f g"
    and "ide (f \<cdot> g) \<Longrightarrow> inverse_arrows f g"
    proof -
      show "ide (g \<cdot> f) \<Longrightarrow> inverse_arrows f g"
        using assms
        by (metis comp_inv_arr' epiE ide_compE inv_is_inverse iso_iff_section_and_epi)
      show "ide (f \<cdot> g) \<Longrightarrow> inverse_arrows f g"
        using assms
        by (metis ide_compE comp_arr_inv' inv_is_inverse iso_iff_mono_and_retraction monoE)
    qed

    text \<open>
      A situation that occurs frequently is that we have a commuting triangle,
      but we need the triangle obtained by inverting one side that is an isomorphism.
      The following fact streamlines this derivation.
\<close>

    lemma invert_side_of_triangle:
    assumes "arr h" and "f \<cdot> g = h"
    shows "iso f \<Longrightarrow> seq (inv f) h \<and> g = inv f \<cdot> h"
    and "iso g \<Longrightarrow> seq h (inv g) \<and> f = h \<cdot> inv g"
    proof -
      show "iso f \<Longrightarrow> seq (inv f) h \<and> g = inv f \<cdot> h"
        by (metis assms seqE inv_is_inverse comp_cod_arr comp_inv_arr comp_assoc)
      show "iso g \<Longrightarrow> seq h (inv g) \<and> f = h \<cdot> inv g"
        by (metis assms seqE inv_is_inverse comp_arr_dom comp_arr_inv dom_inv comp_assoc)
    qed

    text \<open>
      A similar situation is where we have a commuting square and we want to
      invert two opposite sides.
\<close>

    lemma invert_opposite_sides_of_square:
    assumes "seq f g" and "f \<cdot> g = h \<cdot> k"
    shows "\<lbrakk> iso f; iso k \<rbrakk> \<Longrightarrow> seq g (inv k) \<and> seq (inv f) h \<and> g \<cdot> inv k = inv f \<cdot> h"
      by (metis assms invert_side_of_triangle comp_assoc)

  end

end


