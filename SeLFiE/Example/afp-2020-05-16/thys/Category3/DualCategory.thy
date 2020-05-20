(*  Title:       DualCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter DualCategory

theory DualCategory
imports Category
begin

  text\<open>
    The locale defined here constructs the dual (opposite) of a category.
    The arrows of the dual category are directly identified with the arrows of
    the given category and simplification rules are introduced that automatically
    eliminate notions defined for the dual category in favor of the corresponding
    notions on the original category.  This makes it easy to use the dual of
    a category in the same context as the category itself, without having to
    worry about whether an arrow belongs to the category or its dual.
\<close>
    
  locale dual_category =
    C: category C
  for C :: "'a comp"     (infixr "\<cdot>" 55)
  begin

    definition comp      (infixr "\<cdot>\<^sup>o\<^sup>p" 55)
    where "g \<cdot>\<^sup>o\<^sup>p f \<equiv> f \<cdot> g"

    lemma comp_char [simp]:
    shows "g \<cdot>\<^sup>o\<^sup>p f = f \<cdot> g"
      using comp_def by auto

    interpretation partial_magma comp
      apply unfold_locales using comp_def C.ex_un_null by metis

    notation in_hom ("\<guillemotleft>_ : _ \<leftarrow> _\<guillemotright>")

    lemma null_char [simp]:
    shows "null = C.null"
      by (metis C.comp_null(2) comp_null(2) comp_def)

    lemma ide_char [simp]:
    shows "ide a \<longleftrightarrow> C.ide a"
      unfolding ide_def C.ide_def by auto

    lemma domains_char:
    shows "domains f = C.codomains f"
      using C.codomains_def domains_def ide_char by auto

    lemma codomains_char:
    shows "codomains f = C.domains f"
      using C.domains_def codomains_def ide_char by auto

    interpretation category comp
      using C.has_domain_iff_arr C.has_codomain_iff_arr domains_char codomains_char null_char
            comp_def C.match_4 C.ext arr_def C.comp_assoc
      apply (unfold_locales, auto)
      using C.match_2 by metis

    lemma is_category:
    shows "category comp" ..

  end

  sublocale dual_category \<subseteq> category comp
    using is_category by auto

  context dual_category
  begin

    lemma dom_char [simp]:
    shows "dom f = C.cod f"
      by (simp add: C.cod_def dom_def domains_char)

    lemma cod_char [simp]:
    shows "cod f = C.dom f"
      by (simp add: C.dom_def cod_def codomains_char)

    lemma arr_char [simp]:
    shows "arr f \<longleftrightarrow> C.arr f"
      using C.has_codomain_iff_arr has_domain_iff_arr domains_char by auto

    lemma hom_char [simp]:
    shows "in_hom f b a \<longleftrightarrow> C.in_hom f a b"
      by force

    lemma seq_char [simp]:
    shows "seq g f = C.seq f g"
      by simp

  end

end

