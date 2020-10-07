(*  Title:       ProductCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter ProductCategory

theory ProductCategory
imports Category EpiMonoIso
begin

  text\<open>
    This theory defines the product of two categories @{term C1} and @{term C2},
    which is the category @{term C} whose arrows are ordered pairs consisting of an
    arrow of @{term C1} and an arrow of @{term C2}, with composition defined
    componentwise.  As the ordered pair \<open>(C1.null, C2.null)\<close> is available
    to serve as \<open>C.null\<close>, we may directly identify the arrows of the product
    category @{term C} with ordered pairs, leaving the type of arrows of @{term C}
    transparent.
\<close>

  type_synonym ('a1, 'a2) arr = "'a1 * 'a2"

  locale product_category =
    C1: category C1 +
    C2: category C2
  for C1 :: "'a1 comp"      (infixr "\<cdot>\<^sub>1" 55)
  and C2 :: "'a2 comp"      (infixr "\<cdot>\<^sub>2" 55)
  begin

    notation C1.in_hom      ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>1 _\<guillemotright>")
    notation C2.in_hom      ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>2 _\<guillemotright>")

    abbreviation (input) Null :: "('a1, 'a2) arr"
    where "Null \<equiv> (C1.null, C2.null)"

    abbreviation (input) Arr :: "('a1, 'a2) arr \<Rightarrow> bool"
    where "Arr f \<equiv> C1.arr (fst f) \<and> C2.arr (snd f)"

    abbreviation (input) Ide :: "('a1, 'a2) arr \<Rightarrow> bool"
    where "Ide f \<equiv> C1.ide (fst f) \<and> C2.ide (snd f)"

    abbreviation (input) Dom :: "('a1, 'a2) arr \<Rightarrow> ('a1, 'a2) arr"
    where "Dom f \<equiv> (if Arr f then (C1.dom (fst f), C2.dom (snd f)) else Null)"

    abbreviation (input) Cod :: "('a1, 'a2) arr \<Rightarrow> ('a1, 'a2) arr"
    where "Cod f \<equiv> (if Arr f then (C1.cod (fst f), C2.cod (snd f)) else Null)"

    definition comp :: "('a1, 'a2) arr \<Rightarrow> ('a1, 'a2) arr \<Rightarrow> ('a1, 'a2) arr"
    where "comp g f = (if Arr f \<and> Arr g \<and> Cod f = Dom g then
                         (C1 (fst g) (fst f), C2 (snd g) (snd f))
                       else Null)"

    notation comp      (infixr "\<cdot>" 55)

    lemma not_Arr_Null:
    shows "\<not>Arr Null"
      by simp

    interpretation partial_magma comp
    proof
      show "\<exists>!n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n"
      proof
        let ?P = "\<lambda>n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n"
        show 1: "?P Null" using comp_def not_Arr_Null by metis
        thus "\<And>n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n \<Longrightarrow> n = Null" by metis
      qed
    qed

    notation in_hom  ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    lemma null_char [simp]:
    shows "null = Null"
    proof -
      let ?P = "\<lambda>n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n"
      have "?P Null" using comp_def not_Arr_Null by metis
      thus ?thesis
        unfolding null_def using the1_equality [of ?P Null] ex_un_null by blast
    qed

    lemma ide_Ide:
    assumes "Ide a"
    shows "ide a"
      unfolding ide_def comp_def null_char
      using assms C1.not_arr_null C1.ide_in_hom C1.comp_arr_dom C1.comp_cod_arr
            C2.comp_arr_dom C2.comp_cod_arr
      by auto

    lemma has_domain_char:
    shows "domains f \<noteq> {} \<longleftrightarrow> Arr f"
    proof
      show "domains f \<noteq> {} \<Longrightarrow> Arr f"
        unfolding domains_def comp_def null_char by (auto; metis)
      assume f: "Arr f"
      show "domains f \<noteq> {}"
      proof -
        have "ide (Dom f) \<and> comp f (Dom f) \<noteq> null"
          using f comp_def ide_Ide C1.comp_arr_dom C1.arr_dom_iff_arr C2.arr_dom_iff_arr
          by auto
        thus ?thesis using domains_def by blast
      qed
    qed

    lemma has_codomain_char:
    shows "codomains f \<noteq> {} \<longleftrightarrow> Arr f"
    proof
      show "codomains f \<noteq> {} \<Longrightarrow> Arr f"
        unfolding codomains_def comp_def null_char by (auto; metis)
      assume f: "Arr f"
      show "codomains f \<noteq> {}"
      proof -
        have "ide (Cod f) \<and> comp (Cod f) f \<noteq> null"
          using f comp_def ide_Ide C1.comp_cod_arr C1.arr_cod_iff_arr C2.arr_cod_iff_arr
          by auto
        thus ?thesis using codomains_def by blast
      qed
    qed

    lemma arr_char [iff]:
    shows "arr f \<longleftrightarrow> Arr f"
      using has_domain_char has_codomain_char arr_def by simp

    lemma arrI [intro]:
    assumes "C1.arr f1" and "C2.arr f2"
    shows "arr (f1, f2)"
      using assms by simp

    lemma arrE:
    assumes "arr f"
    and "C1.arr (fst f) \<and> C2.arr (snd f) \<Longrightarrow> T"
    shows "T"
      using assms by auto

    lemma seqI [intro]:
    assumes "C1.seq g1 f1 \<and> C2.seq g2 f2"
    shows "seq (g1, g2) (f1, f2)"
      using assms comp_def by auto

    lemma seqE [elim]:
    assumes "seq g f"
    and "C1.seq (fst g) (fst f) \<Longrightarrow> C2.seq (snd g) (snd f) \<Longrightarrow> T"
    shows "T"
      using assms comp_def
      by (metis (no_types, lifting) C1.seqI C2.seqI Pair_inject not_arr_null null_char)

    lemma seq_char [iff]:
    shows "seq g f \<longleftrightarrow> C1.seq (fst g) (fst f) \<and> C2.seq (snd g) (snd f)"
      using comp_def by auto

    lemma Dom_comp:
    assumes "seq g f"
    shows "Dom (g \<cdot> f) = Dom f"
      using assms comp_def
      apply (cases "C1.arr (fst g)"; cases "C1.arr (fst f)";
             cases "C2.arr (snd f)"; cases "C2.arr (snd g)"; simp_all)
      by auto

    lemma Cod_comp:
    assumes "seq g f"
    shows "Cod (g \<cdot> f) = Cod g"
      using assms comp_def
      apply (cases "C1.arr (fst f)"; cases "C2.arr (snd f)";
             cases "C1.arr (fst g)"; cases "C2.arr (snd g)"; simp_all)
      by auto

    theorem is_category:
    shows "category comp"
    proof
      fix f
      show "(domains f \<noteq> {}) = (codomains f \<noteq> {})"
        using has_domain_char has_codomain_char by simp
      fix g
      show "g \<cdot> f \<noteq> null \<Longrightarrow> seq g f"
        using comp_def seq_char by (metis C1.seqI C2.seqI Pair_inject null_char)
      fix h
      show "seq h g \<Longrightarrow> seq (h \<cdot> g) f \<Longrightarrow> seq g f"
        using comp_def null_char seq_char by (elim seqE C1.seqE C2.seqE, simp)
      show "seq h (g \<cdot> f) \<Longrightarrow> seq g f \<Longrightarrow> seq h g"
        using comp_def null_char seq_char by (elim seqE C1.seqE C2.seqE, simp)
      show "seq g f \<Longrightarrow> seq h g \<Longrightarrow> seq (h \<cdot> g) f"
        using comp_def null_char seq_char by (elim seqE C1.seqE C2.seqE, simp)
      show "seq g f \<Longrightarrow> seq h g \<Longrightarrow> (h \<cdot> g) \<cdot> f = h \<cdot> g \<cdot> f"
        using comp_def null_char seq_char C1.comp_assoc C2.comp_assoc comp_assoc
        by (elim seqE C1.seqE C2.seqE, simp)
    qed

  end

  sublocale product_category \<subseteq> category comp
    using is_category comp_def by auto

  context product_category
  begin

    lemma dom_char:
    shows "dom f = Dom f"
    proof (cases "Arr f")
      show "\<not>Arr f \<Longrightarrow> dom f = Dom f"
        unfolding dom_def using has_domain_char by auto
      show "Arr f \<Longrightarrow> dom f = Dom f"
        using ide_Ide apply (intro dom_eqI, simp)
        using seq_char comp_def C1.arr_dom_iff_arr C2.arr_dom_iff_arr by auto
    qed

    lemma dom_simp [simp]:
    assumes "arr f"
    shows "dom f = (C1.dom (fst f), C2.dom (snd f))"
      using assms dom_char by auto

    lemma cod_char:
    shows "cod f = Cod f"
    proof (cases "Arr f")
      show "\<not>Arr f \<Longrightarrow> cod f = Cod f"
        unfolding cod_def using has_codomain_char by auto
      show "Arr f \<Longrightarrow> cod f = Cod f"
        using ide_Ide seqI apply (intro cod_eqI, simp)
        using seq_char comp_def C1.arr_cod_iff_arr C2.arr_cod_iff_arr by auto
    qed

    lemma cod_simp [simp]:
    assumes "arr f"
    shows "cod f = (C1.cod (fst f), C2.cod (snd f))"
      using assms cod_char by auto

    lemma in_homI [intro, simp]:
    assumes "\<guillemotleft>fst f: fst a \<rightarrow>\<^sub>1 fst b\<guillemotright>" and "\<guillemotleft>snd f: snd a \<rightarrow>\<^sub>2 snd b\<guillemotright>"
    shows "\<guillemotleft>f: a \<rightarrow> b\<guillemotright>"
      using assms by fastforce

    lemma in_homE [elim]:
    assumes "\<guillemotleft>f: a \<rightarrow> b\<guillemotright>"
    and "\<guillemotleft>fst f: fst a \<rightarrow>\<^sub>1 fst b\<guillemotright> \<Longrightarrow> \<guillemotleft>snd f: snd a \<rightarrow>\<^sub>2 snd b\<guillemotright> \<Longrightarrow> T"
    shows "T"
      using assms
      by (metis C1.in_homI C2.in_homI arr_char cod_simp dom_simp fst_conv in_homE snd_conv)

    lemma ide_char [iff]:
    shows "ide f \<longleftrightarrow> Ide f"
      using ide_in_hom C1.ide_in_hom C2.ide_in_hom by blast

    lemma comp_char:
    shows "g \<cdot> f = (if C1.arr (C1 (fst g) (fst f)) \<and> C2.arr (C2 (snd g) (snd f)) then
                       (C1 (fst g) (fst f), C2 (snd g) (snd f))
                    else Null)"
      using comp_def by auto

    lemma comp_simp [simp]:
    assumes "C1.seq (fst g) (fst f)" and "C2.seq (snd g) (snd f)"
    shows "g \<cdot> f = (fst g \<cdot>\<^sub>1 fst f, snd g \<cdot>\<^sub>2 snd f)"
      using assms comp_char by simp

    lemma iso_char [iff]:
    shows "iso f \<longleftrightarrow> C1.iso (fst f) \<and> C2.iso (snd f)"
    proof
      assume f: "iso f"
      obtain g where g: "inverse_arrows f g" using f by auto
      have 1: "ide (g \<cdot> f) \<and> ide (f \<cdot> g)"
        using f g by (simp add: inverse_arrows_def)
      have "g \<cdot> f = (fst g \<cdot>\<^sub>1 fst f, snd g \<cdot>\<^sub>2 snd f) \<and> f \<cdot> g = (fst f \<cdot>\<^sub>1 fst g, snd f \<cdot>\<^sub>2 snd g)"
        using 1 comp_char arr_char by (meson ideD(1) seq_char)
      hence "C1.ide (fst g \<cdot>\<^sub>1 fst f) \<and> C2.ide (snd g \<cdot>\<^sub>2 snd f) \<and>
             C1.ide (fst f \<cdot>\<^sub>1 fst g) \<and> C2.ide (snd f \<cdot>\<^sub>2 snd g)"
        using 1 ide_char by simp
      hence "C1.inverse_arrows (fst f) (fst g) \<and> C2.inverse_arrows (snd f) (snd g)"
        by auto
      thus "C1.iso (fst f) \<and> C2.iso (snd f)" by auto
      next
      assume f: "C1.iso (fst f) \<and> C2.iso (snd f)"
      obtain g1 where g1: "C1.inverse_arrows (fst f) g1" using f by blast
      obtain g2 where g2: "C2.inverse_arrows (snd f) g2" using f by blast
      have "C1.ide (g1 \<cdot>\<^sub>1 fst f) \<and> C2.ide (g2 \<cdot>\<^sub>2 snd f) \<and>
            C1.ide (fst f \<cdot>\<^sub>1 g1) \<and> C2.ide (snd f \<cdot>\<^sub>2 g2)"
        using g1 g2 ide_char by force
      hence "inverse_arrows f (g1, g2)"
        using f g1 g2 ide_char comp_char by (intro inverse_arrowsI, auto)
      thus "iso f" by auto
    qed

    lemma isoI [intro, simp]:
    assumes "C1.iso (fst f)" and "C2.iso (snd f)"
    shows "iso f"
      using assms by simp

    lemma isoD:
    assumes "iso f"
    shows "C1.iso (fst f)" and "C2.iso (snd f)"
      using assms by auto

    lemma inv_simp [simp]:
    assumes "iso f"
    shows "inv f = (C1.inv (fst f), C2.inv (snd f))"
    proof -
      have "inverse_arrows f (C1.inv (fst f), C2.inv (snd f))"
      proof
        have 1: "C1.inverse_arrows (fst f) (C1.inv (fst f))"
          using assms iso_char C1.inv_is_inverse by simp
        have 2: "C2.inverse_arrows (snd f) (C2.inv (snd f))"
          using assms iso_char C2.inv_is_inverse by simp
        show "ide ((C1.inv (fst f), C2.inv (snd f)) \<cdot> f)"
          using 1 2 ide_char comp_char by auto
        show "ide (f \<cdot> (C1.inv (fst f), C2.inv (snd f)))"
          using 1 2 ide_char comp_char by auto
      qed
      thus ?thesis using inverse_unique by auto
    qed

  end

end

