(*  Title:       Functor
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter Functor

theory Functor
imports Category ConcreteCategory DualCategory InitialTerminal
begin

  text\<open>
    One advantage of the ``object-free'' definition of category is that a functor
    from category \<open>A\<close> to category \<open>B\<close> is simply a function from the type
    of arrows of \<open>A\<close> to the type of arrows of \<open>B\<close> that satisfies certain
    conditions: namely, that arrows are mapped to arrows, non-arrows are mapped to
    \<open>null\<close>, and domains, codomains, and composition of arrows are preserved.
\<close>

  locale "functor" =
    A: category A +
    B: category B
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a \<Rightarrow> 'b" +
  assumes is_extensional: "\<not>A.arr f \<Longrightarrow> F f = B.null"
  and preserves_arr: "A.arr f \<Longrightarrow> B.arr (F f)"
  and preserves_dom [iff]: "A.arr f \<Longrightarrow> B.dom (F f) = F (A.dom f)"
  and preserves_cod [iff]: "A.arr f \<Longrightarrow> B.cod (F f) = F (A.cod f)"
  and preserves_comp [iff]: "A.seq g f \<Longrightarrow> F (g \<cdot>\<^sub>A f) = F g \<cdot>\<^sub>B F f"
  begin

    notation A.in_hom     ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>A _\<guillemotright>")
    notation B.in_hom     ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")

    lemma preserves_hom [intro]:
    assumes "\<guillemotleft>f : a \<rightarrow>\<^sub>A b\<guillemotright>"
    shows "\<guillemotleft>F f : F a \<rightarrow>\<^sub>B F b\<guillemotright>"
      using assms B.in_homI
      by (metis A.in_homE preserves_arr preserves_cod preserves_dom)

    text\<open>
      The following, which is made possible through the presence of \<open>null\<close>,
      allows us to infer that the subterm @{term f} denotes an arrow if the
      term @{term "F f"} denotes an arrow.  This is very useful, because otherwise
      doing anything with @{term f} would require a separate proof that it is an arrow
      by some other means.
\<close>

    lemma preserves_reflects_arr [iff]:
    shows "B.arr (F f) \<longleftrightarrow> A.arr f"
      using preserves_arr is_extensional B.not_arr_null by metis

    lemma preserves_seq [intro]:
    assumes "A.seq g f"
    shows "B.seq (F g) (F f)"
      using assms by auto

    lemma preserves_ide [simp]:
    assumes "A.ide a"
    shows "B.ide (F a)"
      using assms A.ide_in_hom B.ide_in_hom by auto

    lemma preserves_iso [simp]:
    assumes "A.iso f"
    shows "B.iso (F f)"
      using assms A.inverse_arrowsE
      apply (elim A.isoE A.inverse_arrowsE A.seqE A.ide_compE)
      by (metis A.arr_dom_iff_arr B.ide_dom B.inverse_arrows_def B.isoI preserves_arr
                preserves_comp preserves_dom)

    lemma preserves_section_retraction:
    assumes "A.ide (A e m)"
    shows "B.ide (B (F e) (F m))"
      using assms by (metis A.ide_compE preserves_comp preserves_ide)

    lemma preserves_section:
    assumes "A.section m"
    shows "B.section (F m)"
      using assms preserves_section_retraction by blast

    lemma preserves_retraction:
    assumes "A.retraction e"
    shows "B.retraction (F e)"
      using assms preserves_section_retraction by blast

    lemma preserves_inverse_arrows:
    assumes "A.inverse_arrows f g"
    shows "B.inverse_arrows (F f) (F g)"
      using assms A.inverse_arrows_def B.inverse_arrows_def preserves_section_retraction
      by simp

    lemma preserves_inv:
    assumes "A.iso f"
    shows "F (A.inv f) = B.inv (F f)"
      using assms preserves_inverse_arrows A.inv_is_inverse B.inv_is_inverse
            B.inverse_arrow_unique
      by blast

  end

  locale endofunctor =
    "functor" A A F
  for A :: "'a comp"     (infixr "\<cdot>" 55)
  and F :: "'a \<Rightarrow> 'a"

  locale faithful_functor = "functor" A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b" +
  assumes is_faithful: "\<lbrakk> A.par f f'; F f = F f' \<rbrakk> \<Longrightarrow> f = f'"
  begin

    lemma locally_reflects_ide:
    assumes "\<guillemotleft>f : a \<rightarrow>\<^sub>A a\<guillemotright>" and "B.ide (F f)"
    shows "A.ide f"
      using assms is_faithful
      by (metis A.arr_dom_iff_arr A.cod_dom A.dom_dom A.in_homE B.comp_ide_self
          B.ide_self_inverse B.comp_arr_inv A.ide_cod preserves_dom)

  end

  locale full_functor = "functor" A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b" +
  assumes is_full: "\<lbrakk> A.ide a; A.ide a'; \<guillemotleft>g : F a' \<rightarrow>\<^sub>B F a\<guillemotright> \<rbrakk> \<Longrightarrow> \<exists>f. \<guillemotleft>f : a' \<rightarrow>\<^sub>A a\<guillemotright> \<and> F f = g"

  locale fully_faithful_functor =
    faithful_functor A B F +
    full_functor A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b"
  begin

    lemma reflects_iso:
    assumes "\<guillemotleft>f : a' \<rightarrow>\<^sub>A a\<guillemotright>" and "B.iso (F f)"
    shows "A.iso f"
    proof -
      from assms obtain g' where g': "B.inverse_arrows (F f) g'" by blast
      have 1: "\<guillemotleft>g' : F a \<rightarrow>\<^sub>B F a'\<guillemotright>"
        using assms g' by (metis B.inv_in_hom B.inverse_unique preserves_hom)
      from this obtain g where g: "\<guillemotleft>g : a \<rightarrow>\<^sub>A a'\<guillemotright> \<and> F g = g'"
        using assms(1) is_full by (metis A.arrI A.ide_cod A.ide_dom A.in_homE)
      have "A.inverse_arrows f g"
        using assms 1 g g' A.inverse_arrowsI
        by (metis A.arr_iff_in_hom A.dom_comp A.in_homE A.seqI' B.inverse_arrowsE
            A.cod_comp locally_reflects_ide preserves_comp)
      thus ?thesis by auto
    qed

  end

  locale embedding_functor = "functor" A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b" +
  assumes is_embedding: "\<lbrakk> A.arr f; A.arr f'; F f = F f' \<rbrakk> \<Longrightarrow> f = f'"

  sublocale embedding_functor \<subseteq> faithful_functor
    using is_embedding by (unfold_locales, blast)

  context embedding_functor
  begin

    lemma reflects_ide:
    assumes "B.ide (F f)"
    shows "A.ide f"
      using assms is_embedding A.ide_in_hom B.ide_in_hom
      by (metis A.in_homE B.in_homE A.ide_cod preserves_cod preserves_reflects_arr)

  end

  locale full_embedding_functor =
    embedding_functor A B F +
    full_functor A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b"

  locale essentially_surjective_functor = "functor" +
  assumes essentially_surjective: "\<And>b. B.ide b \<Longrightarrow> \<exists>a. A.ide a \<and> B.isomorphic (F a) b"

  locale constant_functor =
    A: category A +
    B: category B
  for A :: "'a comp"
  and B :: "'b comp"
  and b :: 'b +
  assumes value_is_ide: "B.ide b"
  begin

    definition map
    where "map f = (if A.arr f then b else B.null)"

    lemma map_simp [simp]:
    assumes "A.arr f"
    shows "map f = b"
      using assms map_def by auto

    lemma is_functor:
    shows "functor A B map"
      using map_def value_is_ide by (unfold_locales, auto)
      
  end

  sublocale constant_functor \<subseteq> "functor" A B map
    using is_functor by auto

  locale identity_functor =
    C: category C
    for C :: "'a comp"
  begin

    definition map :: "'a \<Rightarrow> 'a"
    where "map f = (if C.arr f then f else C.null)"

    lemma map_simp [simp]:
    assumes "C.arr f"
    shows "map f = f"
      using assms map_def by simp

    lemma is_functor:
    shows "functor C C map"
      using C.arr_dom_iff_arr C.arr_cod_iff_arr
      by (unfold_locales; auto simp add: map_def)

  end

  sublocale identity_functor \<subseteq> "functor" C C map
    using is_functor by auto

  text \<open>
    It is convenient to have an easy way to obtain from a category the identity functor
    on that category. The following declaration causes the definitions and facts from the
    @{locale identity_functor} locale to be inherited by the @{locale category} locale,
    including the function @{term map} on arrows that represents the identity functor.
    This makes it generally unnecessary to give explicit interpretations of
    @{locale identity_functor}.
\<close>

  sublocale category \<subseteq> identity_functor C ..

  text\<open>
    Composition of functors coincides with function composition, thanks to the
    magic of \<open>null\<close>.
\<close>

  lemma functor_comp:
  assumes "functor A B F" and "functor B C G"
  shows "functor A C (G o F)"
  proof -
    interpret F: "functor" A B F using assms(1) by auto
    interpret G: "functor" B C G using assms(2) by auto
    show "functor A C (G o F)"
      using F.preserves_arr F.is_extensional G.is_extensional by (unfold_locales, auto)
  qed

  locale composite_functor =
    F: "functor" A B F +
    G: "functor" B C G
  for A :: "'a comp"
  and B :: "'b comp"
  and C :: "'c comp"
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'b \<Rightarrow> 'c"
  begin

    abbreviation map
    where "map \<equiv> G o F"

  end

  sublocale composite_functor \<subseteq> "functor" A C "G o F"
    using functor_comp F.functor_axioms G.functor_axioms by blast

  lemma comp_functor_identity [simp]:
  assumes "functor A B F"
  shows "F o identity_functor.map A = F"
  proof
    interpret "functor" A B F using assms by blast
    show "\<And>x. (F o A.map) x = F x"
      using A.map_def is_extensional by simp
  qed

  lemma comp_identity_functor [simp]:
  assumes "functor A B F"
  shows "identity_functor.map B o F = F"
  proof
    interpret "functor" A B F using assms by blast
    show "\<And>x. (B.map o F) x = F x"
      using B.map_def by (metis comp_apply is_extensional preserves_arr)
  qed

  locale inverse_functors =
    A: category A +
    B: category B +
    F: "functor" A B F +
    G: "functor" B A G
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'b \<Rightarrow> 'a" +
  assumes inv: "G o F = identity_functor.map A"
  and inv': "F o G = identity_functor.map B"

  locale isomorphic_categories =
    A: category A +
    B: category B
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55) +
  assumes iso: "\<exists>F G. inverse_functors A B F G"

  sublocale inverse_functors \<subseteq> isomorphic_categories A B
    using inverse_functors_axioms by (unfold_locales, auto)
  
  lemma inverse_functors_sym:
  assumes "inverse_functors A B F G"
  shows "inverse_functors B A G F"
  proof -
    interpret inverse_functors A B F G using assms by auto
    show ?thesis using inv inv' by (unfold_locales, auto)
  qed
  
  text \<open>
    Inverse functors uniquely determine each other.
\<close>

  lemma inverse_functor_unique:
  assumes "inverse_functors C D F G" and "inverse_functors C D F G'"
  shows "G = G'"
  proof -
    interpret FG: inverse_functors C D F G using assms(1) by auto
    interpret FG': inverse_functors C D F G' using assms(2) by auto
    show "G = G'"
      using FG.G.is_extensional FG'.G.is_extensional FG'.inv FG.inv'
      by (metis FG'.G.functor_axioms FG.G.functor_axioms comp_assoc comp_identity_functor
                comp_functor_identity)
  qed

  lemma inverse_functor_unique':
  assumes "inverse_functors C D F G" and "inverse_functors C D F' G"
  shows "F = F'"
    using assms inverse_functors_sym inverse_functor_unique by blast

  locale invertible_functor =
    A: category A +
    B: category B +
    F: "functor" A B F
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a \<Rightarrow> 'b" +
  assumes invertible: "\<exists>G. inverse_functors A B F G"
  begin

    lemma has_unique_inverse:
    shows "\<exists>!G. inverse_functors A B F G"
      using invertible inverse_functor_unique by blast

    definition inv
    where "inv \<equiv> THE G. inverse_functors A B F G"

    interpretation inverse_functors A B F inv
      using inv_def has_unique_inverse theI' [of "\<lambda>G. inverse_functors A B F G"]
      by simp

    lemma inv_is_inverse:
    shows "inverse_functors A B F inv" ..
  
    lemma preserves_terminal:
    assumes "A.terminal a"
    shows "B.terminal (F a)"
    proof
      show 0: "B.ide (F a)" using assms F.preserves_ide A.terminal_def by blast
      fix b :: 'b
      assume b: "B.ide b"
      show "\<exists>!g. \<guillemotleft>g : b \<rightarrow>\<^sub>B F a\<guillemotright>"
      proof
        let ?G = "SOME G. inverse_functors A B F G"
        from invertible have G: "inverse_functors A B F ?G"
          using someI_ex [of "\<lambda>G. inverse_functors A B F G"] by fast
        interpret inverse_functors A B F ?G using G by auto
        let ?P = "\<lambda>f. \<guillemotleft>f : ?G b \<rightarrow>\<^sub>A a\<guillemotright>"
        have 1: "\<exists>!f. ?P f" using assms b A.terminal_def G.preserves_ide by simp
        hence 2: "?P (THE f. ?P f)" by (metis (no_types, lifting) theI')
        thus "\<guillemotleft>F (THE f. ?P f) : b \<rightarrow>\<^sub>B F a\<guillemotright>"
          using b apply (elim A.in_homE, intro B.in_homI, auto)
          using B.ideD(1) B.map_simp comp_def inv' by metis
        hence 3: "\<guillemotleft>(THE f. ?P f) : ?G b \<rightarrow>\<^sub>A a\<guillemotright>"
          using assms 2 b G by simp
        fix g :: 'b
        assume g: "\<guillemotleft>g : b \<rightarrow>\<^sub>B F a\<guillemotright>"
        have "?G (F a) = a"
          using assms(1) A.terminal_def inv A.map_simp
          by (metis 0 F.preserves_reflects_arr B.ideD(1) comp_apply)
        hence "\<guillemotleft>?G g : ?G b \<rightarrow>\<^sub>A a\<guillemotright>"
          using assms(1) g A.terminal_def inv G.preserves_hom [of b "F a" g]
          by (elim B.in_homE, auto)
        hence "?G g = (THE f. ?P f)" using assms 1 3 A.terminal_def by blast
        thus "g = F (THE f. ?P f)"
          using inv' g by (metis B.in_homE B.map_simp comp_def)
      qed
    qed
  
  end

  sublocale invertible_functor \<subseteq> inverse_functors A B F inv
    using inv_is_inverse by simp

  text \<open>
    We now prove the result, advertised earlier in theory \<open>ConcreteCategory\<close>,
    that any category is in fact isomorphic to the concrete category formed from it in
    the obvious way.
  \<close>

  context category
  begin

    interpretation CC: concrete_category \<open>Collect ide\<close> hom id \<open>\<lambda>C B A g f. g \<cdot> f\<close>
      using comp_arr_dom comp_cod_arr comp_assoc
      by (unfold_locales, auto)

    interpretation F: "functor" C CC.COMP
                       \<open>\<lambda>f. if arr f then CC.MkArr (dom f) (cod f) f else CC.null\<close>
      by (unfold_locales, auto simp add: in_homI)

    interpretation G: "functor" CC.COMP C \<open>\<lambda>F. if CC.arr F then CC.Map F else null\<close>
      using CC.Map_in_Hom CC.seq_char
      by (unfold_locales, auto)

    interpretation FG: inverse_functors C CC.COMP
                       \<open>\<lambda>f. if arr f then CC.MkArr (dom f) (cod f) f else CC.null\<close>
                       \<open>\<lambda>F. if CC.arr F then CC.Map F else null\<close>
    proof
      show "(\<lambda>F. if CC.arr F then CC.Map F else null) \<circ>
              (\<lambda>f. if arr f then CC.MkArr (dom f) (cod f) f else CC.null) =
            map"
        using CC.arr_char map_def by fastforce
      show "(\<lambda>f. if arr f then CC.MkArr (dom f) (cod f) f else CC.null) \<circ>
              (\<lambda>F. if CC.arr F then CC.Map F else null) =
            CC.map"
        using CC.MkArr_Map G.preserves_arr G.preserves_cod G.preserves_dom
              CC.is_extensional
        by auto
    qed

    interpretation isomorphic_categories C CC.COMP ..

    theorem is_isomorphic_to_concrete_category:
    shows "isomorphic_categories C CC.COMP"
      ..

  end

  locale dual_functor =
    F: "functor" A B F +
    Aop: dual_category A +
    Bop: dual_category B
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a \<Rightarrow> 'b"
  begin

    notation Aop.comp     (infixr "\<cdot>\<^sub>A\<^sup>o\<^sup>p" 55)
    notation Bop.comp     (infixr "\<cdot>\<^sub>B\<^sup>o\<^sup>p" 55)

    definition map
    where "map \<equiv> F"

    lemma map_simp [simp]:
    shows "map f = F f"
      by (simp add: map_def)

    lemma is_functor:
    shows "functor Aop.comp Bop.comp map"
      using F.is_extensional by (unfold_locales, auto)

  end

  sublocale invertible_functor \<subseteq> inverse_functors A B F inv
    using inv_is_inverse by simp

   sublocale dual_functor \<subseteq> "functor" Aop.comp Bop.comp map
    using is_functor by auto

end

