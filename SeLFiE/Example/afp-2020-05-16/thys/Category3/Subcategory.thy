(*  Title:       Subcategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2017
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Subcategory"

  text\<open>
    In this chapter we give a construction of the subcategory of a category
    defined by a predicate on arrows subject to closure conditions.  The arrows of
    the subcategory are directly identified with the arrows of the ambient category.
    We also define the related notions of full subcategory and inclusion functor.
\<close>

theory Subcategory
imports Functor
begin

  locale subcategory =
    C: category C
    for C :: "'a comp"      (infixr "\<cdot>\<^sub>C" 55)
    and Arr :: "'a \<Rightarrow> bool" +
    assumes inclusion: "Arr f \<Longrightarrow> C.arr f"
    and dom_closed: "Arr f \<Longrightarrow> Arr (C.dom f)"
    and cod_closed: "Arr f \<Longrightarrow> Arr (C.cod f)"
    and comp_closed: "\<lbrakk> Arr f; Arr g; C.cod f = C.dom g \<rbrakk> \<Longrightarrow> Arr (g \<cdot>\<^sub>C f)"
  begin

    no_notation C.in_hom    ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    notation C.in_hom       ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")

    definition comp         (infixr "\<cdot>" 55)
    where "g \<cdot> f = (if Arr f \<and> Arr g \<and> C.cod f = C.dom g then g \<cdot>\<^sub>C f else C.null)"

    interpretation partial_magma comp
    proof
      show "\<exists>!n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n"
      proof
        show 1: "\<forall>f. C.null \<cdot> f = C.null \<and> f \<cdot> C.null = C.null"
          by (metis C.comp_null(1) C.ex_un_null comp_def)
        show "\<And>n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n \<Longrightarrow> n = C.null"
          using 1 C.ex_un_null by metis
      qed
    qed

    lemma null_char [simp]:
    shows "null = C.null"
    proof -
      have "\<forall>f. C.null \<cdot> f = C.null \<and> f \<cdot> C.null = C.null"
        by (metis C.comp_null(1) C.ex_un_null comp_def)
      thus ?thesis using ex_un_null by (metis comp_null(2))
    qed

    lemma ideI:
    assumes "Arr a" and "C.ide a"
    shows "ide a"
      unfolding ide_def
      using assms null_char C.ide_def comp_def by auto

    lemma Arr_iff_dom_in_domain:
    shows "Arr f \<longleftrightarrow> C.dom f \<in> domains f"
    proof
      show "C.dom f \<in> domains f \<Longrightarrow> Arr f"
        using domains_def comp_def ide_def by fastforce
      show "Arr f \<Longrightarrow> C.dom f \<in> domains f"
      proof -
        assume f: "Arr f"
        have "ide (C.dom f)"
          using f inclusion C.dom_in_domains C.has_domain_iff_arr C.domains_def
                dom_closed ideI
          by auto
        moreover have "f \<cdot> C.dom f \<noteq> null"
          using f comp_def dom_closed null_char inclusion C.comp_arr_dom by force
        ultimately show ?thesis
          using domains_def by simp
      qed
    qed

    lemma Arr_iff_cod_in_codomain:
    shows "Arr f \<longleftrightarrow> C.cod f \<in> codomains f"
    proof
      show "C.cod f \<in> codomains f \<Longrightarrow> Arr f"
        using codomains_def comp_def ide_def by fastforce
      show "Arr f \<Longrightarrow> C.cod f \<in> codomains f"
      proof -
        assume f: "Arr f"
        have "ide (C.cod f)"
          using f inclusion C.cod_in_codomains C.has_codomain_iff_arr C.codomains_def
                cod_closed ideI
          by auto
        moreover have "C.cod f \<cdot> f \<noteq> null"
          using f comp_def cod_closed null_char inclusion C.comp_cod_arr by force
        ultimately show ?thesis
          using codomains_def by simp
      qed
    qed

    lemma arr_char:
    shows "arr f \<longleftrightarrow> Arr f"
    proof
      show "Arr f \<Longrightarrow> arr f"
        using arr_def comp_def Arr_iff_dom_in_domain Arr_iff_cod_in_codomain by auto
      show "arr f \<Longrightarrow> Arr f"
      proof -
        assume f: "arr f"
        obtain a where a: "a \<in> domains f \<or> a \<in> codomains f"
          using f arr_def by auto
        have "f \<cdot> a \<noteq> C.null \<or> a \<cdot> f \<noteq> C.null"
          using a domains_def codomains_def null_char by auto
        thus "Arr f"
          using comp_def by metis
      qed
    qed

    lemma arrI [intro]:
    assumes "Arr f"
    shows "arr f"
      using assms arr_char by simp

    lemma arrE [elim]:
    assumes "arr f"
    shows "Arr f"
      using assms arr_char by simp

    interpretation category comp
      using comp_def null_char inclusion comp_closed dom_closed cod_closed
      apply unfold_locales
           apply auto[1]
          apply (metis Arr_iff_dom_in_domain Arr_iff_cod_in_codomain arr_char arr_def emptyE)
    proof -
      fix f g h
      assume gf: "seq g f" and hg: "seq h g"
      show 1: "seq (h \<cdot> g) f"
        using gf hg inclusion comp_closed comp_def by auto
      show "(h \<cdot> g) \<cdot> f = h \<cdot> g \<cdot> f"
        using gf hg 1 C.not_arr_null inclusion comp_def arr_char
        by (metis (full_types) C.cod_comp C.comp_assoc)
      next
      fix f g h
      assume hg: "seq h g" and hgf: "seq (h \<cdot> g) f"
      show "seq g f"
        using hg hgf comp_def null_char inclusion arr_char comp_closed
        by (metis (full_types) C.dom_comp)
      next
      fix f g h
      assume hgf: "seq h (g \<cdot> f)" and gf: "seq g f"
      show "seq h g"
        using hgf gf comp_def null_char arr_char comp_closed
        by (metis C.seqE C.ext C.match_2)
    qed

    theorem is_category:
    shows "category comp" ..

    notation in_hom     ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    lemma dom_simp [simp]:
    assumes "arr f"
    shows "dom f = C.dom f"
    proof -
      have "ide (C.dom f)"
        using assms ideI
        by (meson C.ide_dom arr_char dom_closed inclusion)
      moreover have "f \<cdot> C.dom f \<noteq> null"
        using assms inclusion comp_def null_char dom_closed not_arr_null C.comp_arr_dom arr_char
        by auto
      ultimately show ?thesis
        using dom_eqI ext by blast
    qed

    lemma dom_char:
    shows "dom f = (if arr f then C.dom f else C.null)"
      using dom_simp dom_def arr_def arr_char by auto

    lemma cod_simp [simp]:
    assumes "arr f"
    shows "cod f = C.cod f"
    proof -
      have "ide (C.cod f)"
        using assms ideI
        by (meson C.ide_cod arr_char cod_closed inclusion)
      moreover have "C.cod f \<cdot> f \<noteq> null"
        using assms inclusion comp_def null_char cod_closed not_arr_null C.comp_cod_arr arr_char
        by auto
      ultimately show ?thesis
        using cod_eqI ext by blast
    qed

    lemma cod_char:
    shows "cod f = (if arr f then C.cod f else C.null)"
      using cod_simp cod_def arr_def by auto

    lemma in_hom_char:
    shows "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<longleftrightarrow> arr a \<and> arr b \<and> arr f \<and> \<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright>"
      using inclusion arr_char cod_closed dom_closed
      by (metis C.arr_iff_in_hom C.in_homE arr_iff_in_hom cod_simp dom_simp in_homE)

    lemma ide_char:
    shows "ide a \<longleftrightarrow> arr a \<and> C.ide a"
      using ide_in_hom C.ide_in_hom in_hom_char by simp

    lemma seq_char:
    shows "seq g f \<longleftrightarrow> arr f \<and> arr g \<and> C.seq g f"
    proof
      show "arr f \<and> arr g \<and> C.seq g f \<Longrightarrow> seq g f"
        using arr_char dom_char cod_char by (intro seqI, auto)
      show "seq g f \<Longrightarrow> arr f \<and> arr g \<and> C.seq g f"
        apply (elim seqE, auto)
        using inclusion arr_char by auto
    qed

    lemma hom_char:
    shows "hom a b = C.hom a b \<inter> Collect Arr"
    proof
      show "hom a b \<subseteq> C.hom a b \<inter> Collect Arr"
        using in_hom_char by auto
      show "C.hom a b \<inter> Collect Arr \<subseteq> hom a b"
        using arr_char dom_char cod_char by force
    qed

    lemma comp_char:
    shows "g \<cdot> f = (if arr f \<and> arr g \<and> C.seq g f then g \<cdot>\<^sub>C f else C.null)"
      using arr_char comp_def comp_closed C.ext by force

    lemma comp_simp:
    assumes "seq g f"
    shows "g \<cdot> f = g \<cdot>\<^sub>C f"
      using assms comp_char seq_char by metis

    lemma inclusion_preserves_inverse:
    assumes "inverse_arrows f g"
    shows "C.inverse_arrows f g"
      using assms ide_char comp_simp arr_char
      by (intro C.inverse_arrowsI, auto)

    lemma iso_char:
    shows "iso f \<longleftrightarrow> C.iso f \<and> arr f \<and> arr (C.inv f)"
    proof
      assume f: "iso f"
      show "C.iso f \<and> arr f \<and> arr (C.inv f)"
      proof -
        have 1: "inverse_arrows f (inv f)"
          using f inv_is_inverse by auto
        have 2: "C.inverse_arrows f (inv f)"
          using 1 inclusion_preserves_inverse by blast
        moreover have "arr (inv f)"
          using 1 iso_is_arr iso_inv_iso by blast
        moreover have "inv f = C.inv f"
          using 1 2 C.inv_is_inverse C.inverse_arrow_unique by blast
        ultimately show ?thesis using f 2 iso_is_arr by auto
      qed
      next
      assume f: "C.iso f \<and> arr f \<and> arr (C.inv f)"
      show "iso f"
      proof
        have 1: "C.inverse_arrows f (C.inv f)"
          using f C.inv_is_inverse by blast
        show "inverse_arrows f (C.inv f)"
        proof
          have 2: "C.inv f \<cdot> f = C.inv f \<cdot>\<^sub>C f \<and> f \<cdot> C.inv f = f \<cdot>\<^sub>C C.inv f"
            using f 1 comp_char by fastforce
          have 3: "antipar f (C.inv f)"
            using f C.seqE seqI by simp
          show "ide (C.inv f \<cdot> f)"
            using 1 2 3 ide_char apply (elim C.inverse_arrowsE) by simp
          show "ide (f \<cdot> C.inv f)"
            using 1 2 3 ide_char apply (elim C.inverse_arrowsE) by simp
        qed
      qed
    qed

    lemma inv_char:
    assumes "iso f"
    shows "inv f = C.inv f"
    proof -
      have "C.inverse_arrows f (inv f)"
      proof
        have 1: "inverse_arrows f (inv f)"
          using assms iso_char inv_is_inverse by blast
        show "C.ide (inv f \<cdot>\<^sub>C f)"
        proof -
          have "inv f \<cdot> f = inv f \<cdot>\<^sub>C f"
            using assms 1 inv_in_hom iso_char [of f] comp_char [of "inv f" f] seq_char by auto
          thus ?thesis
            using 1 ide_char arr_char by force
        qed
        show "C.ide (f \<cdot>\<^sub>C inv f)"
        proof -
          have "f \<cdot> inv f = f \<cdot>\<^sub>C inv f"
            using assms 1 inv_in_hom iso_char [of f] comp_char [of f "inv f"] seq_char by auto
          thus ?thesis
            using 1 ide_char arr_char by force
        qed
      qed
      thus ?thesis using C.inverse_arrow_unique C.inv_is_inverse by blast
    qed

  end

  sublocale subcategory \<subseteq> category comp
    using is_category by auto

  section "Full Subcategory"

  locale full_subcategory =
    C: category C
    for C :: "'a comp"
    and Ide :: "'a \<Rightarrow> bool" +
    assumes inclusion: "Ide f \<Longrightarrow> C.ide f"

  sublocale full_subcategory \<subseteq> subcategory C "\<lambda>f. C.arr f \<and> Ide (C.dom f) \<and> Ide (C.cod f)"
      by (unfold_locales; simp)

  context full_subcategory
  begin

    text \<open>
      Isomorphisms in a full subcategory are inherited from the ambient category.
\<close>

    lemma iso_char:
    shows "iso f \<longleftrightarrow> arr f \<and> C.iso f"
    proof
      assume f: "iso f"
      obtain g where g: "inverse_arrows f g" using f by blast
      show "arr f \<and> C.iso f"
      proof -
        have "C.inverse_arrows f g"
          using g apply (elim inverse_arrowsE, intro C.inverse_arrowsI)
          using comp_simp ide_char arr_char by auto
        thus ?thesis
          using f iso_is_arr by blast
      qed
      next
      assume f: "arr f \<and> C.iso f"
      obtain g where g: "C.inverse_arrows f g" using f by blast
      have "inverse_arrows f g"
      proof
        show "ide (comp g f)"
          using f g
          by (metis (no_types, lifting) C.seqE C.ide_compE C.inverse_arrowsE
              arr_char dom_simp ide_dom comp_def)
        show "ide (comp f g)"
          using f g C.inverse_arrows_sym [of f g]
          by (metis (no_types, lifting) C.seqE C.ide_compE C.inverse_arrowsE
              arr_char dom_simp ide_dom comp_def)
      qed
      thus "iso f" by auto
    qed

  end

  section "Inclusion Functor"

  text \<open>
    If \<open>S\<close> is a subcategory of \<open>C\<close>, then there is an inclusion functor
    from \<open>S\<close> to \<open>C\<close>.  Inclusion functors are faithful embeddings.
\<close>

  locale inclusion_functor =
    C: category C +
    S: subcategory C Arr
  for C :: "'a comp"
  and Arr :: "'a \<Rightarrow> bool"
  begin

    interpretation "functor" S.comp C S.map
      using S.map_def S.arr_char S.inclusion S.dom_char S.cod_char
            S.dom_closed S.cod_closed S.comp_closed S.arr_char S.comp_char
      apply unfold_locales
          apply auto[4]
      by (elim S.seqE, auto)

    lemma is_functor:
    shows "functor S.comp C S.map" ..

    interpretation faithful_functor S.comp C S.map
      apply unfold_locales by simp

    lemma is_faithful_functor:
    shows "faithful_functor S.comp C S.map" ..

    interpretation embedding_functor S.comp C S.map
      apply unfold_locales by simp

    lemma is_embedding_functor:
    shows "embedding_functor S.comp C S.map" ..

  end

  sublocale inclusion_functor \<subseteq> faithful_functor S.comp C S.map
    using is_faithful_functor by auto
  sublocale inclusion_functor \<subseteq> embedding_functor S.comp C S.map
    using is_embedding_functor by auto

  text \<open>
    The inclusion of a full subcategory is a special case.
    Such functors are fully faithful.
\<close>

  locale full_inclusion_functor =
    C: category C +
    S: full_subcategory C Ide
  for C :: "'a comp"
  and Ide :: "'a \<Rightarrow> bool"

  sublocale full_inclusion_functor \<subseteq>
              inclusion_functor C "\<lambda>f. C.arr f \<and> Ide (C.dom f) \<and> Ide (C.cod f)" ..

  context full_inclusion_functor
  begin

    interpretation full_functor S.comp C S.map
      apply unfold_locales
      using S.ide_in_hom
      by (metis (no_types, lifting) C.in_homE S.arr_char S.in_hom_char S.map_simp)

    lemma is_full_functor:
    shows "full_functor S.comp C S.map" ..

  end

  sublocale full_inclusion_functor \<subseteq> full_functor S.comp C S.map
    using is_full_functor by auto
  sublocale full_inclusion_functor \<subseteq> fully_faithful_functor S.comp C S.map ..

end
