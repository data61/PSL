(*  Title:       AbstractedCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter AbstractedCategory

theory AbstractedCategory
imports Category
begin

  text\<open>
    The locale defined here allows us to lift a category to a different arrow
    type via an abstraction map.  It is used to obtain categories with opaque
    arrow types, by first defining the category on the concrete representation type,
    then lifting the composition to the abstract type.  I apply this technique
    in several places to avoid the possibility of ``contaminating'' theories
    with specific details about a particular construction on categories.
    The construction of functor categories is a good example of this.
\<close>

  locale abstracted_category =
    C: category C
  for C :: "'c comp"   (infixr "\<cdot>\<^sub>C" 55)
  and A :: "'c \<Rightarrow> 'a"
  and R :: "'a \<Rightarrow> 'c"
  and S :: "'c set" +
  assumes abs_rep: "A (R f) = f"
  and rep_abs: "x \<in> S \<Longrightarrow> R (A x) = x"
  and rep_in_domain: "R f \<in> S"
  and domain_closed: "C.arr x \<or> x = C.null \<Longrightarrow> x \<in> S"
  begin

    definition comp    (infixr "\<cdot>" 55)
    where "g \<cdot> f \<equiv> if C.arr (R g \<cdot>\<^sub>C R f) then A (R g \<cdot>\<^sub>C R f) else A C.null"

    interpretation partial_magma comp
    proof
      show "\<exists>!n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n"
      proof
        show "\<forall>f. A C.null \<cdot> f = A C.null \<and> f \<cdot> A C.null = A C.null"
          unfolding comp_def using rep_abs domain_closed by auto
        show "\<And>n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n \<Longrightarrow> n = A C.null"
          unfolding comp_def using rep_abs domain_closed C.comp_null(1) by metis
      qed
    qed

    notation in_hom ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    lemma null_char:
    shows "null = A C.null"
      using domain_closed rep_abs
      by (metis (no_types, lifting) C.comp_null(2) comp_def comp_null(1))

    lemma abs_preserves_ide:
    shows "C.ide f \<Longrightarrow> ide (A f)"
    proof -
      have "C.ide f \<Longrightarrow> A f \<cdot> A f \<noteq> null"
        using comp_def null_char rep_abs abs_rep domain_closed
        by (metis C.ideD(1) C.comp_ide_self C.not_arr_null)
      thus "C.ide f \<Longrightarrow> ide (A f)"
        unfolding ide_def
        using comp_def null_char rep_abs abs_rep domain_closed C.comp_arr_dom C.comp_cod_arr
        by fastforce
    qed

    lemma has_domain_char':
    shows "domains f \<noteq> {} \<longleftrightarrow> C.domains (R f) \<noteq> {}"
    proof
      assume f: "domains f \<noteq> {}"
      show "C.domains (R f) \<noteq> {}"
        using f unfolding domains_def C.domains_def comp_def null_char apply auto
        by (metis C.seqE C.cod_in_codomains C.comp_arr_dom C.has_codomain_iff_arr
            C.self_domain_iff_ide C.domains_char C.domains_comp C.domains_null C.codomains_char)
      next
      assume f: "C.domains (R f) \<noteq> {}"
      obtain a where a: "a \<in> C.domains (R f)" using f by blast
      have "A a \<in> domains f"
      proof -
        have "ide (A a)"
          using a abs_preserves_ide C.domains_def by simp
        moreover have "comp f (A a) \<noteq> null"
          using a
          unfolding comp_def C.domains_def null_char
          using domain_closed rep_abs C.in_homE C.ext by (simp, metis)
        ultimately show ?thesis using domains_def by blast
      qed
      thus "domains f \<noteq> {}" by auto
    qed

    lemma has_codomain_char':
    shows "codomains f \<noteq> {} \<longleftrightarrow> C.codomains (R f) \<noteq> {}"
    proof
      assume f: "codomains f \<noteq> {}"
      show "C.codomains (R f) \<noteq> {}"
        using f unfolding codomains_def C.codomains_def comp_def null_char apply auto
        by (metis (no_types, lifting) C.seqE C.cod_in_codomains C.comp_cod_arr
            C.has_codomain_iff_arr C.not_arr_null C.self_domain_iff_ide C.domains_char
            C.codomains_char)
      next
      assume f: "C.codomains (R f) \<noteq> {}"
      obtain b where b: "b \<in> C.codomains (R f)" using f by blast
      have "A b \<in> codomains f"
      proof -
        have "ide (A b)"
          using b abs_preserves_ide C.codomains_def by simp
        moreover have "comp (A b) f \<noteq> null"
          using b
          unfolding comp_def C.codomains_def null_char
          using domain_closed rep_abs C.in_homE C.ext by (simp, metis)
        ultimately show ?thesis using codomains_def by blast
      qed
      thus "codomains f \<noteq> {}" by auto
    qed

    lemma arr_char:
    shows "arr f \<longleftrightarrow> C.arr (R f)"
      using comp_def null_char arr_def C.arr_def has_domain_char' has_codomain_char' by simp

    lemma is_category:
    shows "category comp"
    proof
      fix f g h
      show 0: "g \<cdot> f \<noteq> null \<Longrightarrow> seq g f"
        unfolding arr_def
        using domain_closed rep_abs has_domain_char' has_codomain_char' null_char
        by (auto simp add: C.has_domain_iff_arr comp_def)
      show "(domains f \<noteq> {}) = (codomains f \<noteq> {})"
        using has_domain_char' has_codomain_char' C.has_domain_iff_arr C.has_codomain_iff_arr
        by simp
      show "seq h g \<Longrightarrow> seq (h \<cdot> g) f \<Longrightarrow> seq g f"
        using comp_def arr_char rep_abs domain_closed
        by (metis C.seqE C.seqI C.dom_comp)
      show "seq h (g \<cdot> f) \<Longrightarrow> seq g f \<Longrightarrow> seq h g"
        using comp_def arr_char rep_abs domain_closed
        by (metis (full_types) C.compatible_iff_seq C.codomains_comp)
      show "seq g f \<Longrightarrow> seq h g \<Longrightarrow> seq (h \<cdot> g) f"
        using comp_def arr_char rep_abs domain_closed
        by (metis (full_types) C.compatible_iff_seq C.domains_comp)
      show "seq g f \<Longrightarrow> seq h g \<Longrightarrow> (h \<cdot> g) \<cdot> f = h \<cdot> g \<cdot> f"
        using comp_def rep_abs domain_closed C.comp_assoc by fastforce
    qed

  end

  sublocale abstracted_category \<subseteq> category comp
    using is_category by auto

  context abstracted_category
  begin

    lemma has_domain_char:
    shows "domains f \<noteq> {} \<longleftrightarrow> C.arr (R f)"
      using has_domain_char' by (simp add: C.arr_def C.has_domain_iff_has_codomain)
     
    lemma has_cod_char:
    shows "codomains f \<noteq> {} \<longleftrightarrow> C.arr (R f)"
      using has_codomain_char' by (simp add: C.arr_def C.has_domain_iff_has_codomain)

    lemma dom_char:
    shows "dom f = (if arr f then A (C.dom (R f)) else null)"
      using arr_char abs_preserves_ide has_domain_iff_arr dom_def
            domain_closed comp_def rep_abs C.arr_dom_iff_arr
      apply (cases "arr f")
       by (intro dom_eqI, simp_all)

    lemma cod_char:
    shows "cod f = (if arr f then A (C.cod (R f)) else null)"
      using arr_char abs_preserves_ide has_codomain_iff_arr cod_def
            domain_closed comp_def rep_abs C.arr_cod_iff_arr
      apply (cases "arr f")
       by (intro cod_eqI, simp_all)

    lemma ide_char:
    shows "ide a \<longleftrightarrow> C.ide (R a)"
     using arr_char dom_char domain_closed abs_rep rep_abs abs_preserves_ide
     by (metis C.arr_dom C.ide_char' ide_char)

    lemma comp_char:
    shows "g \<cdot> f = (if seq g f then A (R g \<cdot>\<^sub>C R f) else null)"
      using arr_char dom_char cod_char comp_def null_char seqI' not_arr_null
      by (simp add: domain_closed rep_abs)

  end

end
