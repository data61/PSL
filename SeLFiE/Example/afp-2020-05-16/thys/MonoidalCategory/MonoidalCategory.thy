(*  Title:       MonoidalCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2017
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Monoidal Category"

text_raw\<open>
\label{monoidal-category-chap}
\<close>

text \<open>
  In this theory, we define the notion ``monoidal category,'' and develop consequences of
  the definition.  The main result is a proof of MacLane's coherence theorem.
\<close>
    
theory MonoidalCategory
imports Category3.EquivalenceOfCategories
begin

  section "Monoidal Category"

  text \<open>
    A typical textbook presentation defines a monoidal category to be a category @{term C}
    equipped with (among other things) a binary ``tensor product'' functor \<open>\<otimes>: C \<times> C \<rightarrow> C\<close>
    and an ``associativity'' natural isomorphism \<open>\<alpha>\<close>, whose components are isomorphisms
    \<open>\<alpha> (a, b, c): (a \<otimes> b) \<otimes> c \<rightarrow> a \<otimes> (b \<otimes> c)\<close> for objects \<open>a\<close>, \<open>b\<close>,
    and \<open>c\<close> of \<open>C\<close>.  This way of saying things avoids an explicit definition of
    the functors that are the domain and codomain of \<open>\<alpha>\<close> and, in particular, what category
    serves as the domain of these functors.  The domain category is in fact the product
    category \<open>C \<times> C \<times> C\<close> and the domain and codomain of \<open>\<alpha>\<close> are the functors
    \<open>T o (T \<times> C): C \<times> C \<times> C \<rightarrow> C\<close> and \<open>T o (C \<times> T): C \<times> C \<times> C \<rightarrow> C\<close>.
    In a formal development, though, we can't gloss over the fact that
    \<open>C \<times> C \<times> C\<close> has to mean either \<open>C \<times> (C \<times> C)\<close> or \<open>(C \<times> C) \<times> C\<close>,
    which are not formally identical, and that associativities are somehow involved in the
    definitions of the functors \<open>T o (T \<times> C)\<close> and \<open>T o (C \<times> T)\<close>.
    Here we define the \<open>binary_endofunctor\<close> locale to codify our choices about what
    \<open>C \<times> C \<times> C\<close>, \<open>T o (T \<times> C)\<close>, and \<open>T o (C \<times> T)\<close> actually mean.
    In particular, we choose \<open>C \<times> C \<times> C\<close> to be \<open>C \<times> (C \<times> C)\<close> and define the
    functors \<open>T o (T \<times> C)\<close>, and \<open>T o (C \<times> T)\<close> accordingly.
\<close>

  locale binary_endofunctor =
    C: category C +
    CC: product_category C C +
    CCC: product_category C CC.comp +
    binary_functor C C C T
  for C :: "'a comp"      (infixr "\<cdot>" 55)
  and T :: "'a * 'a \<Rightarrow> 'a"
  begin

    definition ToTC
    where "ToTC f \<equiv> if CCC.arr f then T (T (fst f, fst (snd f)), snd (snd f)) else C.null"

    lemma functor_ToTC:
    shows "functor CCC.comp C ToTC"
      using ToTC_def apply unfold_locales
          apply auto[4]
    proof -
      fix f g
      assume gf: "CCC.seq g f"
      show "ToTC (CCC.comp g f) = ToTC g \<cdot> ToTC f"
        using gf unfolding CCC.seq_char CC.seq_char ToTC_def apply auto
        apply (elim C.seqE, auto)
        by (metis C.seqI CC.comp_simp CC.seqI fst_conv preserves_comp preserves_seq snd_conv)
    qed

    lemma ToTC_simp [simp]:
    assumes "C.arr f" and "C.arr g" and "C.arr h"
    shows "ToTC (f, g, h) = T (T (f, g), h)"
      using assms ToTC_def CCC.arr_char by simp

    definition ToCT
    where "ToCT f \<equiv> if CCC.arr f then T (fst f, T (fst (snd f), snd (snd f))) else C.null"

    lemma functor_ToCT:
    shows "functor CCC.comp C ToCT"
      using ToCT_def apply unfold_locales
        apply auto[4]
    proof -
      fix f g
      assume gf: "CCC.seq g f"
      show "ToCT (CCC.comp g f) = ToCT g \<cdot> ToCT f "
        using gf unfolding CCC.seq_char CC.seq_char ToCT_def apply auto
        apply (elim C.seqE, auto)
      by (metis C.seqI CC.comp_simp CC.seqI fst_conv preserves_comp preserves_seq snd_conv)
    qed

    lemma ToCT_simp [simp]:
    assumes "C.arr f" and "C.arr g" and "C.arr h"
    shows "ToCT (f, g, h) = T (f, T (g, h))"
      using assms ToCT_def CCC.arr_char by simp

  end

  text \<open>
    Our primary definition for ``monoidal category'' follows the somewhat non-traditional
    development in \cite{Etingof15}.  There a monoidal category is defined to be a category
    \<open>C\<close> equipped with a binary \emph{tensor product} functor \<open>T: C \<times> C \<rightarrow> C\<close>,
    an \emph{associativity isomorphism}, which is a natural isomorphism
    \<open>\<alpha>: T o (T \<times> C) \<rightarrow> T o (C \<times> T)\<close>, a \emph{unit object} \<open>\<I>\<close> of \<open>C\<close>,
    and an isomorphism \<open>\<iota>: T (\<I>, \<I>) \<rightarrow> \<I>\<close>, subject to two axioms:
    the \emph{pentagon axiom}, which expresses the commutativity of certain pentagonal diagrams
    involving components of \<open>\<alpha>\<close>, and the left and right \emph{unit axioms}, which state
    that the endofunctors \<open>T (\<I>, -)\<close> and \<open>T (-, \<I>)\<close> are equivalences of categories.
    This definition is formalized in the \<open>monoidal_category\<close> locale.

    In more traditional developments, the definition of monoidal category involves additional
    left and right \emph{unitor} isomorphisms \<open>\<lambda>\<close> and \<open>\<rho>\<close> and associated axioms
    involving their components.
    However, as is shown in \cite{Etingof15} and formalized here, the unitors are uniquely
    determined by \<open>\<alpha>\<close> and their values \<open>\<lambda>(\<I>)\<close> and \<open>\<rho>(\<I>)\<close> at \<open>\<I>\<close>,
    which coincide.  Treating \<open>\<lambda>\<close> and \<open>\<rho>\<close> as defined notions results in a more
    economical basic definition of monoidal category that requires less data to be given,
    and has a similar effect on the definition of ``monoidal functor.''
    Moreover, in the context of the formalization of categories that we use here,
    the unit object \<open>\<I>\<close> also need not be given separately, as it can be obtained as the
    codomain of the isomorphism \<open>\<iota>\<close>.
\<close>

  locale monoidal_category =
    category C +
    CC: product_category C C +
    CCC: product_category C CC.comp +
    T: binary_endofunctor C T +
    \<alpha>: natural_isomorphism CCC.comp C T.ToTC T.ToCT \<alpha> +
    L: equivalence_functor C C "\<lambda>f. T (cod \<iota>, f)" +
    R: equivalence_functor C C "\<lambda>f. T (f, cod \<iota>)"
  for C :: "'a comp"       (infixr "\<cdot>" 55)
  and T :: "'a * 'a \<Rightarrow> 'a"
  and \<alpha> :: "'a * 'a * 'a \<Rightarrow> 'a"
  and \<iota> :: 'a +
  assumes \<iota>_in_hom': "\<guillemotleft>\<iota> : T (cod \<iota>, cod \<iota>) \<rightarrow> cod \<iota>\<guillemotright>"
  and \<iota>_is_iso: "iso \<iota>"
  and pentagon: "\<lbrakk> ide a; ide b; ide c; ide d \<rbrakk> \<Longrightarrow>
                 T (a, \<alpha> (b, c, d)) \<cdot> \<alpha> (a, T (b, c), d) \<cdot> T (\<alpha> (a, b, c), d) =
                 \<alpha> (a, b, T (c, d)) \<cdot> \<alpha> (T (a, b), c, d)"
  begin

    text\<open>
      We now define helpful notation and abbreviations to improve readability.
      We did not define and use the notation \<open>\<otimes>\<close> for the tensor product
      in the definition of the locale because to define \<open>\<otimes>\<close> as a binary
      operator requires that it be in curried form, whereas for \<open>T\<close>
      to be a binary functor requires that it take a pair as its argument.
\<close>

    definition unity :: 'a ("\<I>")
    where "unity \<equiv> cod \<iota>"

    abbreviation L :: "'a \<Rightarrow> 'a"
    where "L f \<equiv> T (\<I>, f)"

    abbreviation R :: "'a \<Rightarrow> 'a"
    where "R f \<equiv> T (f, \<I>)"

    abbreviation tensor      (infixr "\<otimes>" 53)
    where "f \<otimes> g \<equiv> T (f, g)"

    abbreviation assoc       ("\<a>[_, _, _]")
    where "\<a>[a, b, c] \<equiv> \<alpha> (a, b, c)"

    text\<open>
      In HOL we can just give the definitions of the left and right unitors ``up front''
      without any preliminary work.  Later we will have to show that these definitions
      have the right properties.  The next two definitions define the values of the
      unitors when applied to identities; that is, their components as natural transformations.
\<close>

    definition lunit ("\<l>[_]")
    where "lunit a \<equiv> THE f. \<guillemotleft>f : \<I> \<otimes> a \<rightarrow> a\<guillemotright> \<and> \<I> \<otimes> f = (\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a]"

    definition runit ("\<r>[_]")
    where "runit a \<equiv> THE f. \<guillemotleft>f : a \<otimes> \<I> \<rightarrow> a\<guillemotright> \<and> f \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"

    text\<open>
      The next two definitions extend the unitors to all arrows, not just identities.
      Unfortunately, the traditional symbol \<open>\<lambda>\<close> for the left unitor is already
      reserved for a higher purpose, so we have to make do with a poor substitute.
\<close>

    abbreviation \<ll>
    where "\<ll> f \<equiv> if arr f then f \<cdot> \<l>[dom f] else null"

    abbreviation \<rho>
    where "\<rho> f \<equiv> if arr f then f \<cdot> \<r>[dom f] else null"

    text\<open>
      We now embark upon a development of the consequences of the monoidal category axioms.
      One of our objectives is to be able to show that an interpretation of the
      \<open>monoidal_category\<close> locale induces an interpretation of a locale corresponding
      to a more traditional definition of monoidal category.
      Another is to obtain the facts we need to prove the coherence theorem.
\<close>

    lemma \<iota>_in_hom [intro]:
    shows "\<guillemotleft>\<iota> : \<I> \<otimes> \<I> \<rightarrow> \<I>\<guillemotright>"
      using unity_def \<iota>_in_hom' by force

    lemma ide_unity [simp]:
    shows "ide \<I>"
      using \<iota>_in_hom unity_def by auto

    lemma tensor_in_hom [simp]:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>g : c \<rightarrow> d\<guillemotright>"
    shows "\<guillemotleft>f \<otimes> g : a \<otimes> c \<rightarrow> b \<otimes> d\<guillemotright>"
      using assms T.preserves_hom CC.arr_char by simp

    lemma arr_tensor [simp]:
    assumes "arr f" and "arr g"
    shows "arr (f \<otimes> g)"
      using assms by simp

    lemma dom_tensor [simp]:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>g : c \<rightarrow> d\<guillemotright>"
    shows "dom (f \<otimes> g) = a \<otimes> c"
      using assms by fastforce

    lemma cod_tensor [simp]:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>g : c \<rightarrow> d\<guillemotright>"
    shows "cod (f \<otimes> g) = b \<otimes> d"
      using assms by fastforce

    lemma tensor_preserves_ide [simp]:
    assumes "ide a" and "ide b"
    shows "ide (a \<otimes> b)"
      using assms T.preserves_ide CC.ide_char by simp

    lemma tensor_preserves_iso [simp]:
    assumes "iso f" and "iso g"
    shows "iso (f \<otimes> g)"
      using assms by simp

    lemma inv_tensor [simp]:
    assumes "iso f" and "iso g"
    shows "inv (f \<otimes> g) = inv f \<otimes> inv g"
      using assms T.preserves_inv by auto

    lemma interchange:
    assumes "seq h g" and "seq h' g'"
    shows "(h \<otimes> h') \<cdot> (g \<otimes> g') = h \<cdot> g \<otimes> h' \<cdot> g'"
      using assms T.preserves_comp [of "(h, h')" "(g, g')"] by simp

    lemma \<alpha>_simp:
    assumes "arr f" and "arr g" and "arr h"
    shows "\<alpha> (f, g, h) = (f \<otimes> g \<otimes> h) \<cdot> \<a>[dom f, dom g, dom h]"
      using assms \<alpha>.is_natural_1 [of "(f, g, h)"] by simp

    lemma assoc_in_hom [intro]:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<guillemotleft>\<a>[a, b, c] : (a \<otimes> b) \<otimes> c \<rightarrow> a \<otimes> b \<otimes> c\<guillemotright>"
      using assms CCC.in_homE by auto

    lemma arr_assoc [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "arr \<a>[a, b, c]"
      using assms assoc_in_hom by simp

    lemma dom_assoc [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "dom \<a>[a, b, c] = (a \<otimes> b) \<otimes> c"
      using assms assoc_in_hom by simp

    lemma cod_assoc [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "cod \<a>[a, b, c] = a \<otimes> b \<otimes> c"
      using assms assoc_in_hom by simp

    lemma assoc_naturality:
    assumes "arr f0" and "arr f1" and "arr f2"
    shows "\<a>[cod f0, cod f1, cod f2] \<cdot> ((f0 \<otimes> f1) \<otimes> f2) =
           (f0 \<otimes> f1 \<otimes> f2) \<cdot> \<a>[dom f0, dom f1, dom f2]"
      using assms \<alpha>.naturality by auto

    lemma iso_assoc [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "iso \<a>[a, b, c]"
      using assms \<alpha>.preserves_iso by simp

    text\<open>
      The next result uses the fact that the functor \<open>L\<close> is an equivalence
      (and hence faithful) to show the existence of a unique solution to the characteristic
      equation used in the definition of a component @{term "\<l>[a]"} of the left unitor.
      It follows that @{term "\<l>[a]"}, as given by our definition using definite description,
      satisfies this characteristic equation and is therefore uniquely determined by
      by \<open>\<otimes>\<close>, @{term \<alpha>}, and \<open>\<iota>\<close>.
\<close>

    lemma lunit_char:
    assumes "ide a"
    shows "\<guillemotleft>\<l>[a] : \<I> \<otimes> a \<rightarrow> a\<guillemotright>" and "\<I> \<otimes> \<l>[a] = (\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a]"
    and "\<exists>!f. \<guillemotleft>f : \<I> \<otimes> a \<rightarrow> a\<guillemotright> \<and> \<I> \<otimes> f = (\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a]"
    proof -
      obtain F \<eta> \<epsilon> where L: "equivalence_of_categories C C F (\<lambda>f. \<I> \<otimes> f) \<eta> \<epsilon>"
        using L.induces_equivalence unity_def by auto
      interpret L: equivalence_of_categories C C F \<open>\<lambda>f. \<I> \<otimes> f\<close> \<eta> \<epsilon>
        using L by auto
      let ?P = "\<lambda>f. \<guillemotleft>f : \<I> \<otimes> a \<rightarrow> a\<guillemotright> \<and> \<I> \<otimes> f = (\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a]"
      have "\<guillemotleft>(\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a] : \<I> \<otimes> \<I> \<otimes> a \<rightarrow> \<I> \<otimes> a\<guillemotright>"
      proof
        show "\<guillemotleft>\<iota> \<otimes> a : (\<I> \<otimes> \<I>) \<otimes> a \<rightarrow> \<I> \<otimes> a\<guillemotright>"
          using assms ide_in_hom by (intro tensor_in_hom, auto)
        show "\<guillemotleft>inv \<a>[\<I>, \<I>, a] : \<I> \<otimes> \<I> \<otimes> a \<rightarrow> (\<I> \<otimes> \<I>) \<otimes> a\<guillemotright>"
          using assms by auto
      qed
      moreover have "ide (\<I> \<otimes> a)" using assms by simp
      ultimately have "\<exists>f. ?P f"
        using assms L.is_full by blast
      moreover have "\<And>f f'. ?P f \<Longrightarrow> ?P f' \<Longrightarrow> f = f'"
      proof -
        fix f f'
        assume f: "?P f" and f': "?P f'"
        have "par f f'" using f f' by force
        show "f = f'" using f f' L.is_faithful [of f f'] by force
      qed
      ultimately show "\<exists>!f. ?P f" by blast
      hence 1: "?P \<l>[a]"
        unfolding lunit_def using theI' [of ?P] by auto
      show "\<guillemotleft>\<l>[a] : \<I> \<otimes> a \<rightarrow> a\<guillemotright>" using 1 by fast
      show "\<I> \<otimes> \<l>[a] = (\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a]" using 1 by fast
    qed

    lemma \<ll>_ide_simp:
    assumes "ide a"
    shows "\<ll> a = \<l>[a]"
      using assms lunit_char comp_cod_arr ide_in_hom by (metis in_homE)

    lemma lunit_in_hom [intro]:
    assumes "ide a"
    shows "\<guillemotleft>\<l>[a] : \<I> \<otimes> a \<rightarrow> a\<guillemotright>"
      using assms lunit_char(1) by blast

    lemma arr_lunit [simp]:
    assumes "ide a"
    shows "arr \<l>[a]"
      using assms lunit_in_hom by auto

    lemma dom_lunit [simp]:
    assumes "ide a"
    shows "dom \<l>[a] = \<I> \<otimes> a"
      using assms lunit_in_hom by auto

    lemma cod_lunit [simp]:
    assumes "ide a"
    shows "cod \<l>[a] = a"
      using assms lunit_in_hom by auto

    text\<open>
      As the right-hand side of the characteristic equation for @{term "\<I> \<otimes> \<l>[a]"}
      is an isomorphism, and the equivalence functor \<open>L\<close> reflects isomorphisms,
      it follows that @{term "\<l>[a]"} is an isomorphism.
\<close>

    lemma iso_lunit [simp]:
    assumes "ide a"
    shows "iso \<l>[a]"
      using assms lunit_char(2) \<iota>_is_iso ide_unity isos_compose iso_assoc iso_inv_iso
            \<iota>_in_hom L.reflects_iso arr_lunit arr_tensor ideD(1) ide_is_iso lunit_in_hom
            tensor_preserves_iso unity_def
      by metis

    text\<open>
      To prove that an arrow @{term f} is equal to @{term "\<l>[a]"} we need only show
      that it is parallel to @{term "\<l>[a]"} and that @{term "\<I> \<otimes> f"} satisfies the same
      characteristic equation as @{term "\<I> \<otimes> \<l>[a]"} does.
\<close>

    lemma lunit_eqI:
    assumes "\<guillemotleft>f : \<I> \<otimes> a \<rightarrow> a\<guillemotright>" and "\<I> \<otimes> f = (\<iota> \<otimes> a) \<cdot> inv \<a>[\<I>, \<I>, a]"
    shows "f = \<l>[a]"
    proof -
      have "ide a" using assms(1) by auto
      thus ?thesis
        using assms lunit_char the1_equality by blast
    qed

    text\<open>
      The next facts establish the corresponding results for the components of the
      right unitor.
\<close>

    lemma runit_char:
    assumes "ide a"
    shows "\<guillemotleft>\<r>[a] : a \<otimes> \<I> \<rightarrow> a\<guillemotright>" and "\<r>[a] \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"
    and "\<exists>!f. \<guillemotleft>f : a \<otimes> \<I> \<rightarrow> a\<guillemotright> \<and> f \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"
    proof -
      obtain F \<eta> \<epsilon> where R: "equivalence_of_categories C C F (\<lambda>f. f \<otimes> \<I>) \<eta> \<epsilon>"
        using R.induces_equivalence \<iota>_in_hom by auto
      interpret R: equivalence_of_categories C C F \<open>\<lambda>f. f \<otimes> \<I>\<close> \<eta> \<epsilon>
        using R by auto
      let ?P = "\<lambda>f. \<guillemotleft>f : a \<otimes> \<I> \<rightarrow> a\<guillemotright> \<and> f \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"
      have "\<guillemotleft>(a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>] : (a \<otimes> \<I>) \<otimes> \<I> \<rightarrow> a \<otimes> \<I>\<guillemotright>"
        using assms by fastforce
      moreover have "ide (a \<otimes> \<I>)" using assms by simp
      ultimately have "\<exists>f. ?P f"
        using assms R.is_full [of a "a \<otimes> \<I>" "(a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"] by blast
      moreover have "\<And>f f'. ?P f \<Longrightarrow> ?P f' \<Longrightarrow> f = f'"
      proof -
        fix f f'
        assume f: "?P f" and f': "?P f'"
        have "par f f'" using f f' by force
        show "f = f'" using f f' R.is_faithful [of f f'] by force
      qed
      ultimately show "\<exists>!f. ?P f" by blast
      hence 1: "?P \<r>[a]" unfolding runit_def using theI' [of ?P] by fast
      show "\<guillemotleft>\<r>[a] : a \<otimes> \<I> \<rightarrow> a\<guillemotright>" using 1 by fast
      show "\<r>[a] \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]" using 1 by fast
    qed

    lemma \<rho>_ide_simp:
    assumes "ide a"
    shows "\<rho> a = \<r>[a]"
      using assms runit_char [of a] comp_cod_arr by auto

    lemma runit_in_hom [intro]:
    assumes "ide a"
    shows "\<guillemotleft>\<r>[a] : a \<otimes> \<I> \<rightarrow> a\<guillemotright>"
      using assms runit_char(1) by blast

    lemma arr_runit [simp]:
    assumes "ide a"
    shows "arr \<r>[a]"
      using assms runit_in_hom by blast

    lemma dom_runit [simp]:
    assumes "ide a"
    shows "dom \<r>[a] = a \<otimes> \<I>"
      using assms runit_in_hom by blast

    lemma cod_runit [simp]:
    assumes "ide a"
    shows "cod \<r>[a] = a"
      using assms runit_in_hom by blast

    lemma runit_eqI:
    assumes "\<guillemotleft>f : a \<otimes> \<I> \<rightarrow> a\<guillemotright>" and "f \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"
    shows "f = \<r>[a]"
    proof -
      have "ide a" using assms(1) by auto
      thus ?thesis
        using assms runit_char the1_equality by blast
    qed

    lemma iso_runit [simp]:
    assumes "ide a"
    shows "iso \<r>[a]"
      using assms \<iota>_is_iso iso_inv_iso isos_compose ide_is_iso R.preserves_reflects_arr
            arrI ide_unity iso_assoc runit_char tensor_preserves_iso R.reflects_iso
            unity_def
      by metis

    text\<open>
      We can now show that the components of the left and right unitors have the
      naturality properties required of a natural transformation.
\<close>

    lemma lunit_naturality:
    assumes "arr f"
    shows "\<l>[cod f] \<cdot> (\<I> \<otimes> f) = f \<cdot> \<l>[dom f]"
    proof -
      interpret \<alpha>': inverse_transformation CCC.comp C T.ToTC T.ToCT \<alpha> ..
      have par: "par (\<l>[cod f] \<cdot> (\<I> \<otimes> f)) (f \<cdot> \<l>[dom f])"
        using assms by simp
      moreover have "\<I> \<otimes> \<l>[cod f] \<cdot> (\<I> \<otimes> f) = \<I> \<otimes> f \<cdot> \<l>[dom f]"
      proof -
        have "\<I> \<otimes> \<l>[cod f] \<cdot> (\<I> \<otimes> f) = ((\<iota> \<otimes> cod f) \<cdot> ((\<I> \<otimes> \<I>) \<otimes> f)) \<cdot> inv \<a>[\<I>, \<I>, dom f]"
          using assms interchange [of \<I> \<I> "\<I> \<otimes> f" "\<l>[cod f]"] lunit_char(2) \<iota>_in_hom unity_def
                \<alpha>'.naturality [of "(\<I>, \<I>, f)"] comp_assoc
          by auto
        also have "... = ((\<I> \<otimes> f) \<cdot> (\<iota> \<otimes> dom f)) \<cdot> inv \<a>[\<I>, \<I>, dom f]"
          using assms interchange comp_arr_dom comp_cod_arr \<iota>_in_hom by auto
        also have "... = (\<I> \<otimes> f) \<cdot> (\<I> \<otimes> \<l>[dom f])"
          using assms \<iota>_in_hom lunit_char(2) comp_assoc by auto
        also have "... = \<I> \<otimes> f \<cdot> \<l>[dom f]"
          using assms interchange by simp
        finally show ?thesis by blast
      qed
      ultimately show "\<l>[cod f] \<cdot> (\<I> \<otimes> f) = f \<cdot> \<l>[dom f]"
        using L.is_faithful unity_def by metis
    qed

    lemma runit_naturality:
    assumes "arr f"
    shows "\<r>[cod f] \<cdot> (f \<otimes> \<I>) = f \<cdot> \<r>[dom f]"
    proof -
      have "par (\<r>[cod f] \<cdot> (f \<otimes> \<I>)) (f \<cdot> \<r>[dom f])"
        using assms by force
      moreover have "\<r>[cod f] \<cdot> (f \<otimes> \<I>) \<otimes> \<I> = f \<cdot> \<r>[dom f] \<otimes> \<I>"
      proof -
        have "\<r>[cod f] \<cdot> (f \<otimes> \<I>) \<otimes> \<I> = (cod f \<otimes> \<iota>) \<cdot> \<a>[cod f, \<I>, \<I>] \<cdot> ((f \<otimes> \<I>) \<otimes> \<I>)"
          using assms interchange [of \<I> \<I> "\<I> \<otimes> f" "\<r>[cod f]"] runit_char(2) \<iota>_in_hom unity_def
                comp_assoc
          by auto
        also have "... = (cod f \<otimes> \<iota>) \<cdot> (f \<otimes> \<I> \<otimes> \<I>) \<cdot>  \<a>[dom f, \<I>, \<I>]"
          using assms \<alpha>.naturality [of "(f, \<I>, \<I>)"] by auto
        also have "... = ((cod f \<otimes> \<iota>) \<cdot> (f \<otimes> \<I> \<otimes> \<I>)) \<cdot> \<a>[dom f, \<I>, \<I>]"
          using comp_assoc by simp
        also have "... = ((f \<otimes> \<I>) \<cdot> (dom f \<otimes> \<iota>)) \<cdot> \<a>[dom f, \<I>, \<I>]"
          using assms \<iota>_in_hom interchange comp_arr_dom comp_cod_arr by auto
        also have "... = (f \<otimes> \<I>) \<cdot> (\<r>[dom f] \<otimes> \<I>)"
          using assms runit_char comp_assoc by auto
        also have "... = f \<cdot> \<r>[dom f] \<otimes> \<I>"
          using assms interchange by simp
        finally show ?thesis by blast
      qed
      ultimately show "\<r>[cod f] \<cdot> (f \<otimes> \<I>) = f \<cdot> \<r>[dom f]"
        using R.is_faithful unity_def by metis
    qed

  end

  text\<open>
    The following locale is an extension of @{locale monoidal_category} that has the
    unitors and their inverses, as well as the inverse to the associator,
    conveniently pre-interpreted.
\<close>

  locale extended_monoidal_category =
    monoidal_category +
    \<alpha>': inverse_transformation CCC.comp C T.ToTC T.ToCT \<alpha> +
    \<ll>: natural_isomorphism C C L map \<ll> +
    \<ll>': inverse_transformation C C L map \<ll> +
    \<rho>: natural_isomorphism C C R map \<rho> +
    \<rho>': inverse_transformation C C R map \<rho>

  text\<open>
    Next we show that an interpretation of @{locale monoidal_category} extends to an
    interpretation of @{locale extended_monoidal_category} and we arrange for the former
    locale to inherit from the latter.
\<close>

  context monoidal_category
  begin

    interpretation \<alpha>': inverse_transformation CCC.comp C T.ToTC T.ToCT \<alpha> ..

    interpretation \<ll>: natural_transformation C C L map \<ll>
    proof -
      interpret \<ll>: transformation_by_components C C L map \<open>\<lambda>a. \<l>[a]\<close>
        using lunit_in_hom lunit_naturality unity_def \<iota>_in_hom' L.is_extensional
        by (unfold_locales, auto)
      have "\<ll>.map = \<ll>"
        using \<ll>.is_natural_1 \<ll>.is_extensional by auto
      thus "natural_transformation C C L map \<ll>"
        using \<ll>.natural_transformation_axioms by auto
    qed

    interpretation \<ll>: natural_isomorphism C C L map \<ll>
      apply unfold_locales
      using iso_lunit \<ll>_ide_simp by simp

    interpretation \<rho>: natural_transformation C C R map \<rho>
    proof -
      interpret \<rho>: transformation_by_components C C R map \<open>\<lambda>a. \<r>[a]\<close>
        using runit_naturality unity_def \<iota>_in_hom' R.is_extensional
        by (unfold_locales, auto)
      have "\<rho>.map = \<rho>"
        using \<rho>.is_natural_1 \<rho>.is_extensional by auto
      thus "natural_transformation C C R map \<rho>"
        using \<rho>.natural_transformation_axioms by auto
    qed

    interpretation \<rho>: natural_isomorphism C C R map \<rho>
      apply unfold_locales
      using \<rho>_ide_simp by simp

    lemma induces_extended_monoidal_category:
    shows "extended_monoidal_category C T \<alpha> \<iota>" ..

  end

  sublocale monoidal_category \<subseteq> extended_monoidal_category
    using induces_extended_monoidal_category by auto

  context monoidal_category
  begin

    abbreviation \<alpha>'
    where "\<alpha>' \<equiv> \<alpha>'.map"

    lemma natural_isomorphism_\<alpha>':
    shows "natural_isomorphism CCC.comp C T.ToCT T.ToTC \<alpha>'" ..

    abbreviation assoc' ("\<a>\<^sup>-\<^sup>1[_, _, _]")
    where "\<a>\<^sup>-\<^sup>1[a, b, c] \<equiv> inv \<a>[a, b, c]"

    lemma \<alpha>'_ide_simp:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<alpha>' (a, b, c) = \<a>\<^sup>-\<^sup>1[a, b, c]"
      using assms \<alpha>'.inverts_components inverse_unique by force

    lemma \<alpha>'_simp:
    assumes "arr f" and "arr g" and "arr h"
    shows "\<alpha>' (f, g, h) = ((f \<otimes> g) \<otimes> h) \<cdot> \<a>\<^sup>-\<^sup>1[dom f, dom g, dom h]"
      using assms T.ToTC_simp \<alpha>'.is_natural_1 \<alpha>'_ide_simp by force

    lemma assoc_inv:
    assumes "ide a" and "ide b" and "ide c"
    shows "inverse_arrows \<a>[a, b, c] \<a>\<^sup>-\<^sup>1[a, b, c]"
      using assms inv_is_inverse by simp

    lemma assoc'_in_hom [intro]:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<guillemotleft>\<a>\<^sup>-\<^sup>1[a, b, c] : a \<otimes> b \<otimes> c \<rightarrow> (a \<otimes> b) \<otimes> c\<guillemotright>"
      using assms by auto

    lemma arr_assoc' [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "arr \<a>\<^sup>-\<^sup>1[a, b, c]"
      using assms by simp

    lemma dom_assoc' [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "dom \<a>\<^sup>-\<^sup>1[a, b, c] = a \<otimes> b \<otimes> c"
      using assms by simp

    lemma cod_assoc' [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "cod \<a>\<^sup>-\<^sup>1[a, b, c] = (a \<otimes> b) \<otimes> c"
      using assms by simp

    lemma comp_assoc_assoc' [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<a>[a, b, c] \<cdot> \<a>\<^sup>-\<^sup>1[a, b, c] = a \<otimes> (b \<otimes> c)"
    and "\<a>\<^sup>-\<^sup>1[a, b, c] \<cdot> \<a>[a, b, c] = (a \<otimes> b) \<otimes> c"
      using assms assoc_inv comp_arr_inv comp_inv_arr by auto

    lemma assoc'_naturality:
    assumes "arr f0" and "arr f1" and "arr f2"
    shows "((f0 \<otimes> f1) \<otimes> f2) \<cdot> \<a>\<^sup>-\<^sup>1[dom f0, dom f1, dom f2] =
           \<a>\<^sup>-\<^sup>1[cod f0, cod f1, cod f2] \<cdot> (f0 \<otimes> f1 \<otimes> f2)"
      using assms \<alpha>'.naturality by auto

    abbreviation \<ll>'
    where "\<ll>' \<equiv> \<ll>'.map"

    abbreviation lunit'                ("\<l>\<^sup>-\<^sup>1[_]")
    where "\<l>\<^sup>-\<^sup>1[a] \<equiv> inv \<l>[a]"

    lemma \<ll>'_ide_simp:
    assumes "ide a"
    shows "\<ll>'.map a = \<l>\<^sup>-\<^sup>1[a]"
      using assms \<ll>'.inverts_components \<ll>_ide_simp inverse_unique by force

    lemma lunit_inv:
    assumes "ide a"
    shows "inverse_arrows \<l>[a] \<l>\<^sup>-\<^sup>1[a]"
      using assms inv_is_inverse by simp

    lemma lunit'_in_hom [intro]:
    assumes "ide a"
    shows "\<guillemotleft>\<l>\<^sup>-\<^sup>1[a] : a \<rightarrow> \<I> \<otimes> a\<guillemotright>"
      using assms by auto

    lemma comp_lunit_lunit' [simp]:
    assumes "ide a"
    shows "\<l>[a] \<cdot> \<l>\<^sup>-\<^sup>1[a] = a"
    and "\<l>\<^sup>-\<^sup>1[a] \<cdot> \<l>[a] = \<I> \<otimes> a"
    proof -
      show "\<l>[a] \<cdot> \<l>\<^sup>-\<^sup>1[a] = a"
        using assms comp_arr_inv lunit_inv by fastforce
      show "\<l>\<^sup>-\<^sup>1[a] \<cdot> \<l>[a] = \<I> \<otimes> a"
        using assms comp_arr_inv lunit_inv by fastforce
    qed

    lemma lunit'_naturality:
    assumes "arr f"
    shows "(\<I> \<otimes> f) \<cdot> \<l>\<^sup>-\<^sup>1[dom f] = \<l>\<^sup>-\<^sup>1[cod f] \<cdot> f"
      using assms \<ll>'.naturality \<ll>'_ide_simp by simp

    abbreviation \<rho>'
    where "\<rho>' \<equiv> \<rho>'.map"

    abbreviation runit' ("\<r>\<^sup>-\<^sup>1[_]")
    where "\<r>\<^sup>-\<^sup>1[a] \<equiv> inv \<r>[a]"

    lemma \<rho>'_ide_simp:
    assumes "ide a"
    shows "\<rho>'.map a = \<r>\<^sup>-\<^sup>1[a]"
      using assms \<rho>'.inverts_components \<rho>_ide_simp inverse_unique by auto

    lemma runit_inv:
    assumes "ide a"
    shows "inverse_arrows \<r>[a] \<r>\<^sup>-\<^sup>1[a]"
      using assms inv_is_inverse by simp

    lemma runit'_in_hom [intro]:
    assumes "ide a"
    shows "\<guillemotleft>\<r>\<^sup>-\<^sup>1[a] : a \<rightarrow> a \<otimes> \<I>\<guillemotright>"
      using assms by auto

    lemma comp_runit_runit' [simp]:
    assumes "ide a"
    shows "\<r>[a] \<cdot> \<r>\<^sup>-\<^sup>1[a] = a"
    and "\<r>\<^sup>-\<^sup>1[a] \<cdot> \<r>[a] = a \<otimes> \<I>"
    proof -
      show "\<r>[a] \<cdot> \<r>\<^sup>-\<^sup>1[a] = a"
        using assms runit_inv by fastforce
      show "\<r>\<^sup>-\<^sup>1[a] \<cdot> \<r>[a] = a \<otimes> \<I>"
        using assms runit_inv by fastforce
    qed

    lemma runit'_naturality:
    assumes "arr f"
    shows "(f \<otimes> \<I>) \<cdot> \<r>\<^sup>-\<^sup>1[dom f] = \<r>\<^sup>-\<^sup>1[cod f] \<cdot> f"
      using assms \<rho>'.naturality \<rho>'_ide_simp by simp

    lemma lunit_commutes_with_L:
    assumes "ide a"
    shows "\<l>[\<I> \<otimes> a] = \<I> \<otimes> \<l>[a]"
      using assms lunit_naturality lunit_in_hom iso_lunit iso_is_section
            section_is_mono monoE L.preserves_ide arrI cod_lunit dom_lunit seqI
            unity_def
      by metis

    lemma runit_commutes_with_R:
    assumes "ide a"
    shows "\<r>[a \<otimes> \<I>] = \<r>[a] \<otimes> \<I>"
      using assms runit_naturality runit_in_hom iso_runit iso_is_section
            section_is_mono monoE R.preserves_ide arrI cod_runit dom_runit seqI
            unity_def
      by metis

    text\<open>
      The components of the left and right unitors are related via a ``triangle''
      diagram that also involves the associator.
      The proof follows \cite{Etingof15}, Proposition 2.2.3.
\<close>

    lemma triangle:
    assumes "ide a" and "ide b"
    shows "(a \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, b] = \<r>[a] \<otimes> b"
    proof -
      text\<open>
        We show that the lower left triangle in the following diagram commutes.
\<close>
      text\<open>
$$\xymatrix{
  {@{term "((a \<otimes> \<I>) \<otimes> \<I>) \<otimes> b"}}
     \ar[rrrr]^{\scriptsize @{term "\<a>[a, \<I>, \<I>] \<otimes> b"}}
     \ar[ddd]_{\scriptsize @{term "\<a>[a \<otimes> \<I>, \<I>, b]"}}
     \ar[drr]_{\scriptsize @{term "(\<r>[a] \<otimes> \<I>) \<otimes> b"}}
  && &&
  {@{term "(a \<otimes> (\<I> \<otimes> \<I>)) \<otimes> b"}}
     \ar[dll]^{\scriptsize @{term "(a \<otimes> \<iota>) \<otimes> b"}}
     \ar[ddd]^{\scriptsize @{term "\<a>[a, \<I> \<otimes> \<I>, b]"}} \\
  && {@{term "(a \<otimes> \<I>) \<otimes> b"}}
      \ar[d]^{\scriptsize @{term "\<a>[a, \<I>, b]"}} \\
  && {@{term "a \<otimes> \<I> \<otimes> b"}}  \\
  {@{term "(a \<otimes> \<I>) \<otimes> \<I> \<otimes> b"}}
      \ar[urr]^{\scriptsize @{term "\<r>[a] \<otimes> \<I> \<otimes> b"}}
      \ar[drr]_{\scriptsize @{term "\<a>[a, \<I>, \<I> \<otimes> b]"}}
  && &&
  {@{term "a \<otimes> (\<I> \<otimes> \<I>) \<otimes> b"}}
      \ar[ull]_{\scriptsize @{term "a \<otimes> \<iota> \<otimes> b"}}
      \ar[dll]^{\scriptsize @{term "a \<otimes> \<a>[\<I>, \<I>, b]"}}  \\
  && {@{term "a \<otimes> \<I> \<otimes> \<I> \<otimes> b"}}
      \ar[uu]^{\scriptsize @{term "a \<otimes> \<l>[\<I> \<otimes> b]"}}
}$$
\<close>
      have *: "(a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b] = \<r>[a] \<otimes> \<I> \<otimes> b"
      proof -
        have 1: "((a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b]) \<cdot> \<a>[a \<otimes> \<I>, \<I>, b]
                    = (\<r>[a] \<otimes> \<I> \<otimes> b) \<cdot> \<a>[a \<otimes> \<I>, \<I>, b]"
        proof -
          have "((a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b]) \<cdot> \<a>[a \<otimes> \<I>, \<I>, b] =
                ((a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> (a \<otimes> \<a>[\<I>, \<I>, b])) \<cdot> \<a>[a, \<I> \<otimes> \<I>, b] \<cdot> (\<a>[a, \<I>, \<I>] \<otimes> b)"
            using assms pentagon comp_assoc by auto
          also have "... = (a \<otimes> ((\<I> \<otimes> \<l>[b]) \<cdot> \<a>[\<I>, \<I>, b])) \<cdot> \<a>[a, \<I> \<otimes> \<I>, b] \<cdot> (\<a>[a, \<I>, \<I>] \<otimes> b)"
            using assms interchange lunit_commutes_with_L by simp
          also have "... = ((a \<otimes> (\<iota> \<otimes> b)) \<cdot> \<a>[a, \<I> \<otimes> \<I>, b]) \<cdot> (\<a>[a, \<I>, \<I>] \<otimes> b)"
            using assms lunit_char \<iota>_in_hom comp_arr_dom comp_assoc by auto
          also have "... = (\<a>[a, \<I>, b] \<cdot> ((a \<otimes> \<iota>) \<otimes> b)) \<cdot> (\<a>[a, \<I>, \<I>] \<otimes> b)"
            using assms \<iota>_in_hom assoc_naturality [of a \<iota> b] by fastforce
          also have "... = \<a>[a, \<I>, b] \<cdot> ((\<r>[a] \<otimes> \<I>) \<otimes> b)"
            using assms \<iota>_in_hom interchange runit_char(2) comp_assoc by auto
          also have "... = (\<r>[a] \<otimes> \<I> \<otimes> b) \<cdot> \<a>[a \<otimes> \<I>, \<I>, b]"
            using assms assoc_naturality [of "\<r>[a]" \<I> b] by simp
          finally show ?thesis by blast
        qed
        show ?thesis
        proof -
          have "epi \<a>[a \<otimes> \<I>, \<I>, b]"
            using assms iso_assoc iso_is_retraction retraction_is_epi by simp
          thus ?thesis
            using 1 assms epiE [of "\<a>[a \<otimes> \<I>, \<I>, b]" "(a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b]"]
            by fastforce
        qed
      qed
      text\<open>
         In \cite{Etingof15} it merely states that the preceding result suffices
         ``because any object of \<open>C\<close> is isomorphic to one of the form @{term "\<I> \<otimes> b"}.''
         However, it seems a little bit more involved than that to formally transport the
         equation \<open>(*)\<close> along the isomorphism @{term "\<l>[b]"} from @{term "\<I> \<otimes> b"}
         to @{term b}.
\<close>
      have "(a \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, b] = ((a \<otimes> \<l>[b]) \<cdot> (a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> (a \<otimes> \<I> \<otimes> \<l>\<^sup>-\<^sup>1[b])) \<cdot>
                                     (a \<otimes> \<I> \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b] \<cdot> ((a \<otimes> \<I>) \<otimes> \<l>\<^sup>-\<^sup>1[b])"
      proof -
        have "\<a>[a, \<I>, b] = (a \<otimes> \<I> \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b] \<cdot> ((a \<otimes> \<I>) \<otimes> \<l>\<^sup>-\<^sup>1[b])"
        proof -
          have "(a \<otimes> \<I> \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b] \<cdot> ((a \<otimes> \<I>) \<otimes> \<l>\<^sup>-\<^sup>1[b])
                  = ((a \<otimes> \<I> \<otimes> \<l>[b]) \<cdot> (a \<otimes> \<I> \<otimes> \<l>\<^sup>-\<^sup>1[b])) \<cdot> \<a>[a, \<I>, b]"
            using assms assoc_naturality [of a \<I> "\<l>\<^sup>-\<^sup>1[b]"] comp_assoc by simp
          also have "... = \<a>[a, \<I>, b]"
            using assms inv_is_inverse interchange comp_cod_arr by simp
          finally show ?thesis by auto
        qed
        moreover have "a \<otimes> \<l>[b] = (a \<otimes> \<l>[b]) \<cdot> (a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> (a \<otimes> \<I> \<otimes> \<l>\<^sup>-\<^sup>1[b])"
          using assms lunit_commutes_with_L comp_arr_dom interchange by auto
        ultimately show ?thesis by argo
      qed
      also have "... = (a \<otimes> \<l>[b]) \<cdot> (a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> ((a \<otimes> \<I> \<otimes> \<l>\<^sup>-\<^sup>1[b]) \<cdot> (a \<otimes> \<I> \<otimes> \<l>[b])) \<cdot>
                       \<a>[a, \<I>, \<I> \<otimes> b] \<cdot> ((a \<otimes> \<I>) \<otimes> \<l>\<^sup>-\<^sup>1[b])"
        using assms comp_assoc by auto
      also have "... = (a \<otimes> \<l>[b]) \<cdot> ((a \<otimes> \<l>[\<I> \<otimes> b]) \<cdot> \<a>[a, \<I>, \<I> \<otimes> b]) \<cdot> ((a \<otimes> \<I>) \<otimes> \<l>\<^sup>-\<^sup>1[b])"
        using assms interchange comp_cod_arr comp_assoc by auto
      also have "... = \<r>[a] \<otimes> b"
        using assms * interchange runit_char(1) comp_arr_dom comp_cod_arr by auto
      finally show ?thesis by blast
    qed

    lemma lunit_tensor_gen:
    assumes "ide a" and "ide b" and "ide c"
    shows "(a \<otimes> \<l>[b \<otimes> c]) \<cdot> (a \<otimes> \<a>[\<I>, b, c]) = a \<otimes> \<l>[b] \<otimes> c"
    proof -
      text\<open>
        We show that the lower right triangle in the following diagram commutes.
\<close>
      text\<open>
$$\xymatrix{
  {@{term "((a \<otimes> \<I>) \<otimes> b) \<otimes> c"}}
     \ar[rrrr]^{\scriptsize @{term "\<a>[a, \<I>, b] \<otimes> c"}}
     \ar[ddd]_{\scriptsize @{term "\<a>[a \<otimes> \<I>, b, c]"}}
     \ar[drr]_{\scriptsize @{term "\<r>[a] \<otimes> b \<otimes> c"}}
  && &&
  {@{term "(a \<otimes> (\<I> \<otimes> b)) \<otimes> c"}}
     \ar[dll]^{\scriptsize @{term "(a \<otimes> \<l>[b]) \<otimes> c"}}
     \ar[ddd]^{\scriptsize @{term "\<a>[a, \<I> \<otimes> b, c]"}} \\
  && {@{term "(a \<otimes> b) \<otimes> c"}}
      \ar[d]^{\scriptsize @{term "\<a>[a, b, c]"}}    \\
  && {@{term "a \<otimes> b \<otimes> c"}}        \\
  {@{term "(a \<otimes> \<I>) \<otimes> b \<otimes> c"}}
      \ar[urr]^{\scriptsize @{term "\<r>[a] \<otimes> b \<otimes> c"}}
      \ar[drr]_{\scriptsize @{term "\<a>[a, \<I>, b \<otimes> c]"}}
  && &&
  {@{term "a \<otimes> (\<I> \<otimes> b) \<otimes> c"}}
      \ar[ull]_{\scriptsize @{term "a \<otimes> \<l>[b] \<otimes> c"}}
      \ar[dll]^{\scriptsize @{term "a \<otimes> \<a>[\<I>, b, c]"}}  \\
  && {@{term "a \<otimes> \<I> \<otimes> b \<otimes> c"}}
      \ar[uu]^{\scriptsize @{term "a \<otimes> \<l>[b \<otimes> c]"}}
}$$
\<close>
      have "((a \<otimes> \<l>[b \<otimes> c]) \<cdot> (a \<otimes> \<a>[\<I>, b, c])) \<cdot> (\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c)) =
            ((a \<otimes> \<l>[b \<otimes> c]) \<cdot> \<a>[a, \<I>, b \<otimes> c]) \<cdot> \<a>[a \<otimes> \<I>, b, c]"
        using assms pentagon comp_assoc by simp
      also have "... = (\<r>[a] \<otimes> (b \<otimes> c)) \<cdot> \<a>[a \<otimes> \<I>, b, c]"
        using assms triangle by auto
      also have "... = \<a>[a, b, c] \<cdot> ((\<r>[a] \<otimes> b) \<otimes> c)"
        using assms assoc_naturality [of "\<r>[a]" b c] by auto
      also have "... = (\<a>[a, b, c] \<cdot> ((a \<otimes> \<l>[b]) \<otimes> c)) \<cdot> (\<a>[a, \<I>, b] \<otimes> c)"
        using assms triangle interchange comp_assoc by auto
      also have "... = (a \<otimes> (\<l>[b] \<otimes> c)) \<cdot> (\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c))"
        using assms assoc_naturality [of a "\<l>[b]" c] comp_assoc by auto
      finally have 1: "((a \<otimes> \<l>[b \<otimes> c]) \<cdot> (a \<otimes> \<a>[\<I>, b, c])) \<cdot> \<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c)
                        = (a \<otimes> (\<l>[b] \<otimes> c)) \<cdot> \<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c)"
        by blast
      text\<open>
        The result follows by cancelling the isomorphism
        @{term "\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c)"}
\<close>
      have 2: "iso (\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c))"
        using assms isos_compose by simp
      moreover have
          "seq ((a \<otimes> \<l>[b \<otimes> c]) \<cdot> (a \<otimes> \<a>[\<I>, b, c])) (\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c))"
        using assms by auto
      moreover have "seq (a \<otimes> (\<l>[b] \<otimes> c)) (\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c))"
        using assms by auto
      ultimately show ?thesis
        using 1 2 assms iso_is_retraction retraction_is_epi
              epiE [of "\<a>[a, \<I> \<otimes> b, c] \<cdot> (\<a>[a, \<I>, b] \<otimes> c)"
                       "(a \<otimes> \<l>[b \<otimes> c]) \<cdot> (a \<otimes> \<a>[\<I>, b, c])" "a \<otimes> \<l>[b] \<otimes> c"]
        by auto
    qed

    text\<open>
      The following result is quoted without proof as Theorem 7 of \cite{Kelly64} where it is
      attributed to MacLane \cite{MacLane63}.  It also appears as \cite{MacLane71},
      Exercise 1, page 161.  I did not succeed within a few hours to construct a proof following
      MacLane's hint.  The proof below is based on \cite{Etingof15}, Proposition 2.2.4.
\<close>

    lemma lunit_tensor':
    assumes "ide a" and "ide b"
    shows "\<l>[a \<otimes> b] \<cdot> \<a>[\<I>, a, b] = \<l>[a] \<otimes> b"
    proof -
      have "\<I> \<otimes> (\<l>[a \<otimes> b] \<cdot> \<a>[\<I>, a, b]) = \<I> \<otimes> (\<l>[a] \<otimes> b)"
        using assms interchange [of \<I> \<I>] lunit_tensor_gen by simp
      moreover have "par (\<l>[a \<otimes> b] \<cdot> \<a>[\<I>, a, b]) (\<l>[a] \<otimes> b)"
        using assms by simp
      ultimately show ?thesis
        using assms L.is_faithful [of "\<l>[a \<otimes> b] \<cdot> \<a>[\<I>, a, b]" "\<l>[a] \<otimes> b"] unity_def by simp
    qed

    lemma lunit_tensor:
    assumes "ide a" and "ide b"
    shows "\<l>[a \<otimes> b] = (\<l>[a] \<otimes> b) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, a, b]"
      using assms lunit_tensor' invert_side_of_triangle by simp

    text\<open>
      We next show the corresponding result for the right unitor.
\<close>
      
    lemma runit_tensor_gen:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<r>[a \<otimes> b] \<otimes> c = ((a \<otimes> \<r>[b]) \<otimes> c) \<cdot> (\<a>[a, b, \<I>] \<otimes> c)"
    proof -
      text\<open>
        We show that the upper right triangle in the following diagram commutes.
\<close>
      text\<open>
$$\xymatrix{
  && {@{term "((a \<otimes> b) \<otimes> \<I>) \<otimes> c"}}
     \ar[dll]_{\scriptsize @{term "\<a>[a \<otimes> b, \<I>, c]"}}
     \ar[dd]^{\scriptsize @{term "\<r>[a \<otimes> b] \<otimes> c"}}
     \ar[drr]^{\scriptsize @{term "\<a>[a, b, \<I>] \<otimes> c"}} \\
  {@{term "(a \<otimes> b) \<otimes> \<I> \<otimes> c"}}
     \ar[ddd]_{\scriptsize @{term "\<a>[a, b, \<I> \<otimes> c]"}}
     \ar[drr]_{\scriptsize @{term "(a \<otimes> b) \<otimes> \<l>[c]"}}
  && &&
  {@{term "(a \<otimes> b \<otimes> \<I>) \<otimes> c"}}
     \ar[dll]^{\scriptsize @{term "(a \<otimes> \<r>[b]) \<otimes> c"}}
     \ar[ddd]^{\scriptsize @{term "\<a>[a, b \<otimes> \<I>, c]"}} \\
  && {@{term "(a \<otimes> b) \<otimes> c"}}
     \ar[d]^{\scriptsize @{term "\<a>[a, b, c]"}}     \\
  && {@{term "a \<otimes> b \<otimes> c"}}        \\
  {@{term "a \<otimes> b \<otimes> \<I> \<otimes> c"}}
     \ar[urr]^{\scriptsize @{term "a \<otimes> b \<otimes> \<l>[c]"}}
  && &&
  {@{term "a \<otimes> (b \<otimes> \<I>) \<otimes> c"}}
     \ar[llll]^{\scriptsize @{term "a \<otimes> \<a>[b, \<I>, c]"}}
     \ar[ull]_{\scriptsize @{term "a \<otimes> \<r>[b] \<otimes> c"}}
}$$
\<close>
      have "\<r>[a \<otimes> b] \<otimes> c = ((a \<otimes> b) \<otimes> \<l>[c]) \<cdot> \<a>[a \<otimes> b, \<I>, c]"
        using assms triangle by simp
      also have "... = (\<a>\<^sup>-\<^sup>1[a, b, c] \<cdot> (a \<otimes> b \<otimes> \<l>[c]) \<cdot> \<a>[a, b, \<I> \<otimes> c]) \<cdot> \<a>[a \<otimes> b, \<I>, c]"
        using assms assoc_naturality [of a b "\<l>[c]"] comp_arr_dom comp_cod_arr
              invert_side_of_triangle(1)
        by force
      also have "... = \<a>\<^sup>-\<^sup>1[a, b, c] \<cdot> (a \<otimes> b \<otimes> \<l>[c]) \<cdot> \<a>[a, b, \<I> \<otimes> c] \<cdot> \<a>[a \<otimes> b, \<I>, c]"
        using comp_assoc by force
      also have "... = \<a>\<^sup>-\<^sup>1[a, b, c] \<cdot> ((a \<otimes> (\<r>[b] \<otimes> c)) \<cdot> (a \<otimes> \<a>\<^sup>-\<^sup>1[b, \<I>, c])) \<cdot>
                       \<a>[a, b, \<I> \<otimes> c] \<cdot> \<a>[a \<otimes> b, \<I>, c]"
        using assms triangle [of b c] interchange invert_side_of_triangle(2) by force
      also have "... = (((a \<otimes> \<r>[b]) \<otimes> c) \<cdot> \<a>\<^sup>-\<^sup>1[a, b \<otimes> \<I>, c]) \<cdot> (a \<otimes> \<a>\<^sup>-\<^sup>1[b, \<I>, c]) \<cdot>
                       \<a>[a, b, \<I> \<otimes> c] \<cdot> \<a>[a \<otimes> b, \<I>, c]"
        using assms assoc'_naturality [of a "\<r>[b]" c] comp_assoc by force
      also have "... = ((a \<otimes> \<r>[b]) \<otimes> c) \<cdot> \<a>\<^sup>-\<^sup>1[a, b \<otimes> \<I>, c] \<cdot> (a \<otimes> \<a>\<^sup>-\<^sup>1[b, \<I>, c]) \<cdot>
                       \<a>[a, b, \<I> \<otimes> c] \<cdot> \<a>[a \<otimes> b, \<I>, c]"
        using comp_assoc by simp
      also have "... = ((a \<otimes> \<r>[b]) \<otimes> c) \<cdot> (\<a>[a, b, \<I>] \<otimes> c)"
        using assms pentagon invert_side_of_triangle(1)
              invert_side_of_triangle(1)
                [of "\<a>[a, b, \<I> \<otimes> c] \<cdot> \<a>[a \<otimes> b, \<I>, c]" "a \<otimes> \<a>[b, \<I>, c]"
                    "\<a>[a, b \<otimes> \<I>, c] \<cdot> (\<a>[a, b, \<I>] \<otimes> c)"]
        by force
      finally show ?thesis by blast
    qed

    lemma runit_tensor:
    assumes "ide a" and "ide b"
    shows "\<r>[a \<otimes> b] = (a \<otimes> \<r>[b]) \<cdot> \<a>[a, b, \<I>]"
    proof -
      have "((a \<otimes> \<r>[b]) \<cdot> \<a>[a, b, \<I>]) \<otimes> \<I> = \<r>[a \<otimes> b] \<otimes> \<I>"
        using assms interchange [of \<I> \<I>] runit_tensor_gen by simp
      moreover have "par ((a \<otimes> \<r>[b]) \<cdot> \<a>[a, b, \<I>]) \<r>[a \<otimes> b]"
        using assms by simp
      ultimately show ?thesis
        using assms R.is_faithful [of "(a \<otimes> \<r>[b]) \<cdot> (\<a>[a, b, \<I>])" "\<r>[a \<otimes> b]"] unity_def
        by argo
    qed

    lemma runit_tensor':
    assumes "ide a" and "ide b"
    shows "\<r>[a \<otimes> b] \<cdot> \<a>\<^sup>-\<^sup>1[a, b, \<I>] = a \<otimes> \<r>[b]"
      using assms runit_tensor invert_side_of_triangle by force

    text \<open>
      Sometimes inverted forms of the triangle and pentagon axioms are useful.
\<close>

    lemma triangle':
    assumes "ide a" and "ide b"
    shows "(a \<otimes> \<l>[b]) = (\<r>[a] \<otimes> b) \<cdot> \<a>\<^sup>-\<^sup>1[a, \<I>, b]"
    proof -
      have "(\<r>[a] \<otimes> b) \<cdot> \<a>\<^sup>-\<^sup>1[a, \<I>, b] = ((a \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, b]) \<cdot> \<a>\<^sup>-\<^sup>1[a, \<I>, b]"
          using assms triangle by auto
      also have "... = (a \<otimes> \<l>[b])"
        using assms comp_arr_dom comp_assoc by auto
      finally show ?thesis by auto
    qed

    lemma pentagon':
    assumes "ide a" and "ide b" and "ide c" and "ide d"
    shows "((\<a>\<^sup>-\<^sup>1[a, b, c] \<otimes> d) \<cdot> \<a>\<^sup>-\<^sup>1[a, b \<otimes> c, d]) \<cdot> (a \<otimes> \<a>\<^sup>-\<^sup>1[b, c, d])
              = \<a>\<^sup>-\<^sup>1[a \<otimes> b, c, d] \<cdot> \<a>\<^sup>-\<^sup>1[a, b, c \<otimes> d]"
    proof -
      have "((\<a>\<^sup>-\<^sup>1[a, b, c] \<otimes> d) \<cdot> \<a>\<^sup>-\<^sup>1[a, b \<otimes> c, d]) \<cdot> (a \<otimes> \<a>\<^sup>-\<^sup>1[b, c, d])
              = inv ((a \<otimes> \<a>[b, c, d]) \<cdot> (\<a>[a, b \<otimes> c, d] \<cdot> (\<a>[a, b, c] \<otimes> d)))"
        using assms isos_compose inv_comp by simp
      also have "... = inv (\<a>[a, b, c \<otimes> d] \<cdot> \<a>[a \<otimes> b, c, d])"
        using assms pentagon by auto
      also have "... = \<a>\<^sup>-\<^sup>1[a \<otimes> b, c, d] \<cdot> \<a>\<^sup>-\<^sup>1[a, b, c \<otimes> d]"
        using assms inv_comp by simp
      finally show ?thesis by auto
    qed

    text\<open>
      The following non-obvious fact is Corollary 2.2.5 from \cite{Etingof15}.
      The statement that @{term "\<l>[\<I>] = \<r>[\<I>]"} is Theorem 6 from \cite{Kelly64}.
      MacLane \cite{MacLane71} does not show this, but assumes it as an axiom.
\<close>

    lemma unitor_coincidence:
    shows "\<l>[\<I>] = \<iota>" and "\<r>[\<I>] = \<iota>"
    proof -
      have "\<l>[\<I>] \<otimes> \<I> = (\<I> \<otimes> \<l>[\<I>]) \<cdot> \<a>[\<I>, \<I>, \<I>]"
        using lunit_tensor' [of \<I> \<I>] lunit_commutes_with_L [of \<I>] by simp
      moreover have "\<r>[\<I>] \<otimes> \<I> = (\<I> \<otimes> \<l>[\<I>]) \<cdot> \<a>[\<I>, \<I>, \<I>]"
        using triangle [of \<I> \<I>] by simp
      moreover have "\<iota> \<otimes> \<I> = (\<I> \<otimes> \<l>[\<I>]) \<cdot> \<a>[\<I>, \<I>, \<I>]"
        using lunit_char comp_arr_dom \<iota>_in_hom comp_assoc by auto
      ultimately have "\<l>[\<I>] \<otimes> \<I> = \<iota> \<otimes> \<I> \<and> \<r>[\<I>] \<otimes> \<I> = \<iota> \<otimes> \<I>"
        by argo
      moreover have "par \<l>[\<I>] \<iota> \<and> par \<r>[\<I>] \<iota>"
        using \<iota>_in_hom by force
      ultimately have 1: "\<l>[\<I>] = \<iota> \<and> \<r>[\<I>] = \<iota>"
        using R.is_faithful unity_def by metis
      show "\<l>[\<I>] = \<iota>" using 1 by auto
      show "\<r>[\<I>] = \<iota>" using 1 by auto
    qed

    lemma \<iota>_triangle:
    shows "\<iota> \<otimes> \<I> = (\<I> \<otimes> \<iota>) \<cdot> \<a>[\<I>, \<I>, \<I>]"
    and "(\<iota> \<otimes> \<I>) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>] = \<I> \<otimes> \<iota>"
      using triangle [of \<I> \<I>] triangle' [of \<I> \<I>] unitor_coincidence by auto

    text\<open>
      The only isomorphism that commutes with @{term \<iota>} is @{term \<I>}.
\<close>

    lemma iso_commuting_with_\<iota>_equals_\<I>:
    assumes "\<guillemotleft>f : \<I> \<rightarrow> \<I>\<guillemotright>" and "iso f" and "f \<cdot> \<iota> = \<iota> \<cdot> (f \<otimes> f)"
    shows "f = \<I>"
    proof -
      have 1: "f \<otimes> f = f \<otimes> \<I>"
      proof -
        have "f \<otimes> f = (inv \<iota> \<cdot> \<iota>) \<cdot> (f \<otimes> f)"
          using assms \<iota>_in_hom \<iota>_is_iso inv_is_inverse comp_inv_arr comp_cod_arr [of "f \<otimes> f"]
          by force
        also have "... = (inv \<iota> \<cdot> f) \<cdot> \<iota>"
          using assms \<iota>_is_iso inv_is_inverse comp_assoc by force
        also have "... = ((f \<otimes> \<I>) \<cdot> inv \<iota>) \<cdot> \<iota>"
          using assms unitor_coincidence runit'_naturality [of f] by auto
        also have "... = (f \<otimes> \<I>) \<cdot> (inv \<iota> \<cdot> \<iota>)"
          using comp_assoc by force
        also have "... = f \<otimes> \<I>"
          using assms \<iota>_in_hom \<iota>_is_iso inv_is_inverse comp_inv_arr
                comp_arr_dom [of "f \<otimes> \<I>" "\<I> \<otimes> \<I>"]
          by force
        finally show ?thesis by blast
      qed
      moreover have "(f \<otimes> f) \<cdot> (inv f \<otimes> \<I>) = \<I> \<otimes> f \<and> (f \<otimes> \<I>) \<cdot> (inv f \<otimes> \<I>) = \<I> \<otimes> \<I>"
        using assms interchange comp_arr_inv inv_is_inverse comp_arr_dom by auto
      ultimately have "\<I> \<otimes> f = \<I> \<otimes> \<I>" by metis
      moreover have "par f \<I>"
        using assms by auto
      ultimately have "f = \<I>"
        using L.is_faithful unity_def by metis
      thus ?thesis using 1 by blast
    qed

  end

  text\<open>
    We now show that the unit \<open>\<iota>\<close> of a monoidal category is unique up to a unique
    isomorphism (Proposition 2.2.6 of \cite{Etingof15}).
\<close>

  locale monoidal_category_with_alternate_unit =
    monoidal_category C T \<alpha> \<iota> +
    C\<^sub>1: monoidal_category C T \<alpha> \<iota>\<^sub>1
  for C :: "'a comp"      (infixr "\<cdot>" 55)
  and T :: "'a * 'a \<Rightarrow> 'a"
  and \<alpha> :: "'a * 'a * 'a \<Rightarrow> 'a"
  and \<iota> :: 'a
  and \<iota>\<^sub>1 :: 'a
  begin

    no_notation C\<^sub>1.tensor (infixr "\<otimes>" 53)
    no_notation C\<^sub>1.unity  ("\<I>")
    no_notation C\<^sub>1.lunit  ("\<l>[_]")
    no_notation C\<^sub>1.runit  ("\<r>[_]")
    no_notation C\<^sub>1.assoc  ("\<a>[_, _, _]")
    no_notation C\<^sub>1.assoc' ("\<a>\<^sup>-\<^sup>1[_, _, _]")

    notation C\<^sub>1.tensor    (infixr "\<otimes>\<^sub>1" 53)
    notation C\<^sub>1.unity     ("\<I>\<^sub>1")
    notation C\<^sub>1.lunit     ("\<l>\<^sub>1[_]")
    notation C\<^sub>1.runit     ("\<r>\<^sub>1[_]")
    notation C\<^sub>1.assoc     ("\<a>\<^sub>1[_, _, _]")
    notation C\<^sub>1.assoc'    ("\<a>\<^sub>1\<^sup>-\<^sup>1[_, _, _]")

    definition i
    where "i \<equiv> \<l>[\<I>\<^sub>1] \<cdot> inv \<r>\<^sub>1[\<I>]"

    lemma iso_i:
    shows "\<guillemotleft>i : \<I> \<rightarrow> \<I>\<^sub>1\<guillemotright>" and "iso i"
    proof -
      show "\<guillemotleft>i : \<I> \<rightarrow> \<I>\<^sub>1\<guillemotright>"
        using C\<^sub>1.iso_runit inv_in_hom i_def by auto
      show "iso i"
        using iso_lunit C\<^sub>1.iso_runit iso_inv_iso isos_compose i_def by simp
    qed

    text\<open>
      The following is Exercise 2.2.7 of \cite{Etingof15}.
\<close>

    lemma i_maps_\<iota>_to_\<iota>\<^sub>1:
    shows "i \<cdot> \<iota> = \<iota>\<^sub>1 \<cdot> (i \<otimes> i)"
    proof -
      have 1: "inv \<r>\<^sub>1[\<I>] \<cdot> \<iota> = (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]) \<cdot> (inv \<r>\<^sub>1[\<I>] \<otimes> inv \<r>\<^sub>1[\<I>])"
      proof -
        have "\<iota> \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<r>\<^sub>1[\<I>]) = \<r>\<^sub>1[\<I>] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1])"
        proof -
          text \<open>
$$\xymatrix{
  && {@{term[source=true] "(\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<I> \<otimes> \<I>\<^sub>1"}}
     \ar[dddll]_{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<r>\<^sub>1[\<I>]"}}
     \ar[dd]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1"}}
     \ar[dddrr]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]"}}
  \\
  \\
  && {@{term[source=true] "\<I> \<otimes> \<I> \<otimes> \<I>\<^sub>1"}}
     \ar[dll]^{\scriptsize @{term[source=true] "\<I> \<otimes> \<r>\<^sub>1[\<I>]"}}
     \ar[drr]_{\scriptsize @{term[source=true] "\<I> \<otimes> \<l>[\<I>\<^sub>1]"}}
     \ar[dd]^{\scriptsize @{term[source=true] "\<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>\<^sub>1]"}}
  \\
  {@{term[source=true] "\<I> \<otimes> \<I>"}}
     \ar[dddrr]_{\scriptsize @{term[source=true] "\<iota>"}}
  &&
  &&
  {@{term[source=true] "\<I> \<otimes> \<I>\<^sub>1"}}
     \ar[dddll]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>]"}}
  \\
  && {@{ term[source=true] "(\<I> \<otimes> \<I>) \<otimes> \<I>\<^sub>1"}}
     \ar[ull]_{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I> \<otimes> \<I>]"}}
     \ar[urr]^{\scriptsize @{term[source=true] "\<iota> \<otimes> \<I>"}}
  \\
  \\
  && {@{term[source=true] "\<I>"}}
}$$
\<close>
          have "\<iota> \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<r>\<^sub>1[\<I>]) = \<iota> \<cdot> (\<I> \<otimes> \<r>\<^sub>1[\<I>]) \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1)"
            using interchange comp_cod_arr comp_arr_dom by simp
          also have "... = \<iota> \<cdot> (\<r>\<^sub>1[\<I> \<otimes> \<I>] \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>\<^sub>1]) \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1)"
            using C\<^sub>1.runit_tensor' by auto
          also have "... = (\<iota> \<cdot> \<r>\<^sub>1[\<I> \<otimes> \<I>]) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>\<^sub>1] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1)"
            using comp_assoc by auto
          also have "... = (\<r>\<^sub>1[\<I>] \<cdot> (\<iota> \<otimes> \<I>\<^sub>1)) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>\<^sub>1] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1)"
            using C\<^sub>1.runit_naturality [of \<iota>] \<iota>_in_hom by fastforce
          also have "... = \<r>\<^sub>1[\<I>] \<cdot> ((\<iota> \<otimes> \<I>\<^sub>1) \<cdot> \<a>\<^sup>-\<^sup>1[\<I>, \<I>, \<I>\<^sub>1]) \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1)"
            using comp_assoc by auto
          also have "... = \<r>\<^sub>1[\<I>] \<cdot> (\<I> \<otimes> \<l>[\<I>\<^sub>1]) \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I> \<otimes> \<I>\<^sub>1)"
            using lunit_tensor lunit_commutes_with_L unitor_coincidence by simp
          also have "... = \<r>\<^sub>1[\<I>] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1])"
            using interchange comp_arr_dom comp_cod_arr by simp
          finally show ?thesis by blast
        qed
        moreover have "seq \<iota> (\<r>\<^sub>1[\<I>] \<otimes> \<r>\<^sub>1[\<I>]) \<and> seq \<r>\<^sub>1[\<I>] (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1])"
          using \<iota>_in_hom by fastforce
        moreover have "iso \<r>\<^sub>1[\<I>] \<and> iso (\<r>\<^sub>1[\<I>] \<otimes> \<r>\<^sub>1[\<I>])"
          using C\<^sub>1.iso_runit tensor_preserves_iso by force
        ultimately show ?thesis
          using invert_opposite_sides_of_square inv_tensor by metis
      qed
      have 2: "\<l>[\<I>\<^sub>1] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]) = \<iota>\<^sub>1 \<cdot> (\<l>[\<I>\<^sub>1] \<otimes> \<l>[\<I>\<^sub>1])"
      proof -
        text \<open>
$$\xymatrix{
  && {@{term[source=true] "(\<I> \<otimes> \<I>\<^sub>1) \<otimes> (\<I> \<otimes> \<I>\<^sub>1)"}}
     \ar[dddll]_{\scriptsize @{term[source=true] "\<l>[\<I>\<^sub>1] \<otimes> \<l>[\<I>\<^sub>1]"}}
     \ar[dd]^{\scriptsize @{term[source=true] "(\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1]"}}
     \ar[dddrr]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]"}}
  \\
  \\
  && {@{term[source=true] "(\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<I>\<^sub>1"}}
     \ar[dll]^{\scriptsize @{term[source=true] "\<l>[\<I>\<^sub>1] \<otimes> \<I>\<^sub>1"}}
     \ar[drr]_{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<I>\<^sub>1"}}
     \ar[dd]^{\scriptsize @{term[source=true] "\<a>[\<I>, \<I>\<^sub>1, \<I>\<^sub>1]"}}
  \\
  {@{term[source=true] "\<I>\<^sub>1 \<otimes> \<I>\<^sub>1"}}
     \ar[dddrr]_{\scriptsize @{term[source=true] "\<iota>\<^sub>1"}}
  &&
  &&
  {@{term[source=true] "\<I> \<otimes> \<I>\<^sub>1"}}
     \ar[dddll]^{\scriptsize @{term[source=true] "\<l>[\<I>\<^sub>1]"}}
  \\
  && {@{term[source=true] "\<I> \<otimes> \<I>\<^sub>1 \<otimes> \<I>\<^sub>1"}}
     \ar[ull]_{\scriptsize @{term[source=true] "\<l>[\<I>\<^sub>1 \<otimes> \<I>\<^sub>1]"}}
     \ar[urr]^{\scriptsize @{term[source=true] "\<I> \<otimes> \<iota>\<^sub>1"}}
  \\
  \\
  && {@{term[source=true] "\<I>\<^sub>1"}}
}$$
\<close>
        have "\<l>[\<I>\<^sub>1] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]) = \<l>[\<I>\<^sub>1] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<I>\<^sub>1) \<cdot> ((\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1])"
          using interchange comp_arr_dom comp_cod_arr by force
        also have "... = \<l>[\<I>\<^sub>1] \<cdot> ((\<I> \<otimes> \<iota>\<^sub>1) \<cdot> \<a>[\<I>, \<I>\<^sub>1, \<I>\<^sub>1]) \<cdot> ((\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1])"
          using C\<^sub>1.runit_tensor C\<^sub>1.unitor_coincidence C\<^sub>1.runit_commutes_with_R by simp
        also have "... = (\<l>[\<I>\<^sub>1] \<cdot> (\<I> \<otimes> \<iota>\<^sub>1)) \<cdot> \<a>[\<I>, \<I>\<^sub>1, \<I>\<^sub>1] \<cdot> ((\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1])"
          using comp_assoc by fastforce
        also have "... = (\<iota>\<^sub>1 \<cdot> \<l>[\<I>\<^sub>1 \<otimes> \<I>\<^sub>1]) \<cdot> \<a>[\<I>, \<I>\<^sub>1, \<I>\<^sub>1] \<cdot> ((\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1])"
          using lunit_naturality [of \<iota>\<^sub>1] C\<^sub>1.\<iota>_in_hom lunit_commutes_with_L by fastforce
        also have "... = \<iota>\<^sub>1 \<cdot> (\<l>[\<I>\<^sub>1 \<otimes> \<I>\<^sub>1] \<cdot> \<a>[\<I>, \<I>\<^sub>1, \<I>\<^sub>1]) \<cdot> ((\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1])"
          using comp_assoc by force
        also have "... = \<iota>\<^sub>1 \<cdot> (\<l>[\<I>\<^sub>1] \<otimes> \<I>\<^sub>1) \<cdot> ((\<I> \<otimes> \<I>\<^sub>1) \<otimes> \<l>[\<I>\<^sub>1])"
          using lunit_tensor' by auto
        also have "... = \<iota>\<^sub>1 \<cdot> (\<l>[\<I>\<^sub>1] \<otimes> \<l>[\<I>\<^sub>1])"
          using interchange comp_arr_dom comp_cod_arr by simp
        finally show ?thesis by blast
      qed
      show ?thesis
      proof -
        text \<open>
$$\xymatrix{
  {@{term[source=true] "\<I>\<^sub>1 \<otimes> \<I>\<^sub>1"}}
     \ar[dd]_{\scriptsize @{term "\<iota>\<^sub>1"}}
  &&
  {@{term[source=true] "(\<I> \<otimes> \<I>\<^sub>1) \<otimes> (\<I> \<otimes> \<I>\<^sub>1)"}}
     \ar[ll]_{\scriptsize @{term[source=true] "\<l>[\<I>\<^sub>1] \<otimes> \<l>[\<I>\<^sub>1]"}}
     \ar[dd]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1]"}}
     \ar[rr]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>] \<otimes> \<r>\<^sub>1[\<I>]"}}
  &&
  {@{term[source=true] "\<I>\<^sub>1 \<otimes> \<I>\<^sub>1"}}
     \ar[dd]^{\scriptsize @{term[source=true] "\<iota>"}}
  \\
  \\
  {@{term[source=true] "\<I>\<^sub>1"}}
  &&
  {@{term[source=true] "\<I> \<otimes> \<I>\<^sub>1"}}
     \ar[ll]_{\scriptsize @{term[source=true] "\<l>[\<I>\<^sub>1]"}}
     \ar[rr]^{\scriptsize @{term[source=true] "\<r>\<^sub>1[\<I>]"}}
  &&
  {@{term[source=true] "\<I>"}}
}$$
\<close>
        have "i \<cdot> \<iota> = \<l>[\<I>\<^sub>1] \<cdot> inv \<r>\<^sub>1[\<I>] \<cdot> \<iota>"
          using i_def comp_assoc by auto
        also have "... = (\<l>[\<I>\<^sub>1] \<cdot> (\<r>\<^sub>1[\<I>] \<otimes> \<l>[\<I>\<^sub>1])) \<cdot> (inv \<r>\<^sub>1[\<I>] \<otimes> inv \<r>\<^sub>1[\<I>])"
          using 1 comp_assoc by simp
        also have "... = \<iota>\<^sub>1 \<cdot> (\<l>[\<I>\<^sub>1] \<otimes> \<l>[\<I>\<^sub>1]) \<cdot> (inv \<r>\<^sub>1[\<I>] \<otimes> inv \<r>\<^sub>1[\<I>])"
          using 2 comp_assoc by fastforce
        also have "... = \<iota>\<^sub>1 \<cdot> (i \<otimes> i)"
          using interchange i_def by simp
        finally show ?thesis by blast
      qed
    qed

    lemma inv_i_iso_\<iota>:
    assumes "\<guillemotleft>f : \<I> \<rightarrow> \<I>\<^sub>1\<guillemotright>" and "iso f" and "f \<cdot> \<iota> = \<iota>\<^sub>1 \<cdot> (f \<otimes> f)"
    shows "\<guillemotleft>inv i \<cdot> f : \<I> \<rightarrow> \<I>\<guillemotright>" and "iso (inv i \<cdot> f)"
    and "(inv i \<cdot> f) \<cdot> \<iota> = \<iota> \<cdot> (inv i \<cdot> f \<otimes> inv i \<cdot> f)"
    proof -
      show 1: "\<guillemotleft>inv i \<cdot> f : \<I> \<rightarrow> \<I>\<guillemotright>"
        using assms iso_i inv_in_hom by blast
      show "iso (inv i \<cdot> f)"
        using assms 1 iso_i inv_in_hom iso_inv_iso
        by (intro isos_compose, auto)
      show "(inv i \<cdot> f) \<cdot> \<iota> = \<iota> \<cdot> (inv i \<cdot> f \<otimes> inv i \<cdot> f)"
      proof -
        have "(inv i \<cdot> f) \<cdot> \<iota> = (inv i \<cdot> \<iota>\<^sub>1) \<cdot> (f \<otimes> f)"
          using assms iso_i comp_assoc by auto
        also have "... = (\<iota> \<cdot> (inv i \<otimes> inv i)) \<cdot> (f \<otimes> f)"
          using assms iso_i invert_opposite_sides_of_square
                inv_tensor \<iota>_in_hom C\<^sub>1.\<iota>_in_hom tensor_in_hom tensor_preserves_iso
                inv_in_hom i_maps_\<iota>_to_\<iota>\<^sub>1 unity_def seqI'
          by metis
        also have "... = \<iota> \<cdot> (inv i \<cdot> f \<otimes> inv i \<cdot> f)"
          using assms 1 iso_i interchange comp_assoc by fastforce
        finally show ?thesis by blast
      qed
    qed

    lemma unit_unique_upto_unique_iso:
    shows "\<exists>!f. \<guillemotleft>f : \<I> \<rightarrow> \<I>\<^sub>1\<guillemotright> \<and> iso f \<and> f \<cdot> \<iota> = \<iota>\<^sub>1 \<cdot> (f \<otimes> f)"
    proof
      show "\<guillemotleft>i : \<I> \<rightarrow> \<I>\<^sub>1\<guillemotright> \<and> iso i \<and> i \<cdot> \<iota> = \<iota>\<^sub>1 \<cdot> (i \<otimes> i)"
        using iso_i i_maps_\<iota>_to_\<iota>\<^sub>1 by auto
      show "\<And>f. \<guillemotleft>f : \<I> \<rightarrow> \<I>\<^sub>1\<guillemotright> \<and> iso f \<and> f \<cdot> \<iota> = \<iota>\<^sub>1 \<cdot> (f \<otimes> f) \<Longrightarrow> f = i"
      proof -
        fix f
        assume f: "\<guillemotleft>f : \<I> \<rightarrow> \<I>\<^sub>1\<guillemotright> \<and> iso f \<and> f \<cdot> \<iota> = \<iota>\<^sub>1 \<cdot> (f \<otimes> f)"
        have "inv i \<cdot> f = \<I>"
          using f inv_i_iso_\<iota> iso_commuting_with_\<iota>_equals_\<I> by blast
        hence "ide (C (inv i) f)"
          using iso_i iso_inv_iso inv_in_hom by simp
        thus "f = i"
          using section_retraction_of_iso(2) [of "inv i" f] inverse_arrow_unique inv_is_inverse
                inv_inv iso_inv_iso iso_i
          by blast
      qed
    qed

  end

  section "Elementary Monoidal Category"

  text\<open>
    Although the economy of data assumed by @{locale monoidal_category} is useful for general
    results, to establish interpretations it is more convenient to work with a traditional
    definition of monoidal category.  The following locale provides such a definition.
    It permits a monoidal category to be specified by giving the tensor product and the
    components of the associator and unitors, which are required only to satisfy elementary
    conditions that imply functoriality and naturality, without having to worry about
    extensionality or formal interpretations for the various functors and natural transformations.
\<close>

  locale elementary_monoidal_category =
    category C
  for C :: "'a comp"                  (infixr "\<cdot>" 55)
  and tensor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"       (infixr "\<otimes>" 53)
  and unity :: 'a                      ("\<I>")
  and lunit :: "'a \<Rightarrow> 'a"              ("\<l>[_]")
  and runit :: "'a \<Rightarrow> 'a"              ("\<r>[_]")
  and assoc :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("\<a>[_, _, _]") +
  assumes ide_unity [simp]: "ide \<I>"
  and iso_lunit: "ide a \<Longrightarrow> iso \<l>[a]"
  and iso_runit: "ide a \<Longrightarrow> iso \<r>[a]"
  and iso_assoc: "\<lbrakk> ide a; ide b; ide c \<rbrakk> \<Longrightarrow> iso \<a>[a, b, c]"
  and tensor_in_hom [simp]: "\<lbrakk> \<guillemotleft>f : a \<rightarrow> b\<guillemotright>; \<guillemotleft>g : c \<rightarrow> d\<guillemotright> \<rbrakk> \<Longrightarrow> \<guillemotleft>f \<otimes> g : a \<otimes> c \<rightarrow> b \<otimes> d\<guillemotright>"
  and tensor_preserves_ide: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> ide (a \<otimes> b)"
  and interchange: "\<lbrakk> seq g f; seq g' f' \<rbrakk> \<Longrightarrow> (g \<otimes> g') \<cdot> (f \<otimes> f') = g \<cdot> f \<otimes> g' \<cdot> f'"
  and lunit_in_hom [simp]: "ide a \<Longrightarrow> \<guillemotleft>\<l>[a] : \<I> \<otimes> a \<rightarrow> a\<guillemotright>"
  and lunit_naturality: "arr f \<Longrightarrow> \<l>[cod f] \<cdot> (\<I> \<otimes> f) = f \<cdot> \<l>[dom f]"
  and runit_in_hom [simp]: "ide a \<Longrightarrow> \<guillemotleft>\<r>[a] : a \<otimes> \<I> \<rightarrow> a\<guillemotright>"
  and runit_naturality: "arr f \<Longrightarrow> \<r>[cod f] \<cdot> (f \<otimes> \<I>) = f \<cdot> \<r>[dom f]"
  and assoc_in_hom [simp]:
      "\<lbrakk> ide a; ide b; ide c \<rbrakk> \<Longrightarrow> \<guillemotleft>\<a>[a, b, c] : (a \<otimes> b) \<otimes> c \<rightarrow> a \<otimes> b \<otimes> c\<guillemotright>"
  and assoc_naturality:
      "\<lbrakk> arr f0; arr f1; arr f2 \<rbrakk> \<Longrightarrow> \<a>[cod f0, cod f1, cod f2] \<cdot> ((f0 \<otimes> f1) \<otimes> f2)
                                        = (f0 \<otimes> (f1 \<otimes> f2)) \<cdot> \<a>[dom f0, dom f1, dom f2]"
  and triangle: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> (a \<otimes> \<l>[b]) \<cdot> \<a>[a, \<I>, b] = \<r>[a] \<otimes> b"
  and pentagon: "\<lbrakk> ide a; ide b; ide c; ide d \<rbrakk> \<Longrightarrow>
                   (a \<otimes> \<a>[b, c, d]) \<cdot> \<a>[a, b \<otimes> c, d] \<cdot> (\<a>[a, b, c] \<otimes> d)
                     = \<a>[a, b, c \<otimes> d] \<cdot> \<a>[a \<otimes> b, c, d]"

  text\<open>
    An interpretation for the \<open>monoidal_category\<close> locale readily induces an
    interpretation for the \<open>elementary_monoidal_category\<close> locale.
\<close>
      
  context monoidal_category
  begin

    lemma induces_elementary_monoidal_category:
      shows "elementary_monoidal_category C tensor \<I> lunit runit assoc"
        using \<iota>_in_hom iso_assoc tensor_preserves_ide assoc_in_hom tensor_in_hom
              assoc_naturality lunit_naturality runit_naturality lunit_in_hom runit_in_hom
              iso_lunit iso_runit interchange pentagon triangle
        apply unfold_locales by auto

  end

  context elementary_monoidal_category
  begin

    interpretation CC: product_category C C ..
    interpretation CCC: product_category C CC.comp ..

    text\<open>
      To avoid name clashes between the @{locale monoidal_category} and
      @{locale elementary_monoidal_category} locales, some constants for which definitions
      are needed here are given separate names from the versions in @{locale monoidal_category}.
      We eventually show that the locally defined versions are equal to their counterparts
      in @{locale monoidal_category}.
\<close>
      
    definition T\<^sub>E\<^sub>M\<^sub>C :: "'a * 'a \<Rightarrow> 'a"
    where "T\<^sub>E\<^sub>M\<^sub>C f \<equiv> if CC.arr f then (fst f \<otimes> snd f) else null"

    lemma T_simp [simp]:
    assumes "arr f" and "arr g"
    shows "T\<^sub>E\<^sub>M\<^sub>C (f, g) = f \<otimes> g"
      using assms T\<^sub>E\<^sub>M\<^sub>C_def by simp

    lemma arr_tensor [simp]:
    assumes "arr f" and "arr g"
    shows "arr (f \<otimes> g)"
      using assms tensor_in_hom by blast

    lemma dom_tensor [simp]:
    assumes "arr f" and "arr g"
    shows "dom (f \<otimes> g) = dom f \<otimes> dom g"
      using assms tensor_in_hom by blast

    lemma cod_tensor [simp]:
    assumes "arr f" and "arr g"
    shows "cod (f \<otimes> g) = cod f \<otimes> cod g"
      using assms tensor_in_hom by blast

    definition L\<^sub>E\<^sub>M\<^sub>C
    where "L\<^sub>E\<^sub>M\<^sub>C \<equiv> \<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (\<I>, f)"

    definition R\<^sub>E\<^sub>M\<^sub>C :: "'a \<Rightarrow> 'a"
    where "R\<^sub>E\<^sub>M\<^sub>C \<equiv> \<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (f, \<I>)"

    definition \<alpha>
    where "\<alpha> f \<equiv> if CCC.arr f then (fst f \<otimes> (fst (snd f) \<otimes> snd (snd f))) \<cdot>
                                   \<a>[dom (fst f), dom (fst (snd f)), dom (snd (snd f))]
                  else null"

    lemma \<alpha>_ide_simp [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<alpha> (a, b, c) = \<a>[a, b, c]"
      unfolding \<alpha>_def using assms assoc_in_hom comp_cod_arr
      by (metis CC.arrI CCC.arrI fst_conv ide_char in_homE snd_conv)

    lemma arr_assoc [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "arr \<a>[a, b, c]"
      using assms assoc_in_hom by blast

    lemma dom_assoc [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "dom \<a>[a, b, c] = (a \<otimes> b) \<otimes> c"
      using assms assoc_in_hom by blast

    lemma cod_assoc [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "cod \<a>[a, b, c] = a \<otimes> b \<otimes> c"
      using assms assoc_in_hom by blast
      
    definition \<ll>\<^sub>E\<^sub>M\<^sub>C
    where "\<ll>\<^sub>E\<^sub>M\<^sub>C f \<equiv> if arr f then f \<cdot> \<l>[dom f] else null"

    lemma arr_lunit [simp]:
    assumes "ide a"
    shows "arr \<l>[a]"
      using assms lunit_in_hom by blast

    lemma dom_lunit [simp]:
    assumes "ide a"
    shows "dom \<l>[a] = \<I> \<otimes> a"
      using assms lunit_in_hom by blast

    lemma cod_lunit [simp]:
    assumes "ide a"
    shows "cod \<l>[a] = a"
      using assms lunit_in_hom by blast

    definition \<rho>\<^sub>E\<^sub>M\<^sub>C
    where "\<rho>\<^sub>E\<^sub>M\<^sub>C f \<equiv> if arr f then f \<cdot> \<r>[dom f] else null"

    lemma arr_runit [simp]:
    assumes "ide a"
    shows "arr \<r>[a]"
      using assms runit_in_hom by blast

    lemma dom_runit [simp]:
    assumes "ide a"
    shows "dom \<r>[a] = a \<otimes> \<I>"
      using assms runit_in_hom by blast

    lemma cod_runit [simp]:
    assumes "ide a"
    shows "cod \<r>[a] = a"
      using assms runit_in_hom by blast

    interpretation T: binary_endofunctor C T\<^sub>E\<^sub>M\<^sub>C
      using tensor_in_hom interchange T\<^sub>E\<^sub>M\<^sub>C_def
      apply unfold_locales
          apply auto[4]
      by (elim CC.seqE, auto)

    lemma binary_endofunctor_T:
    shows "binary_endofunctor C T\<^sub>E\<^sub>M\<^sub>C" ..

    interpretation ToTC: "functor" CCC.comp C T.ToTC
      using T.functor_ToTC by auto

    interpretation ToCT: "functor" CCC.comp C T.ToCT
      using T.functor_ToCT by auto

    interpretation L: "functor" C C L\<^sub>E\<^sub>M\<^sub>C
      using T.fixing_ide_gives_functor_1 L\<^sub>E\<^sub>M\<^sub>C_def by auto

    lemma functor_L:
    shows "functor C C L\<^sub>E\<^sub>M\<^sub>C" ..

    interpretation R: "functor" C C R\<^sub>E\<^sub>M\<^sub>C
      using T.fixing_ide_gives_functor_2 R\<^sub>E\<^sub>M\<^sub>C_def by auto

    lemma functor_R:
    shows "functor C C R\<^sub>E\<^sub>M\<^sub>C" ..
        
    interpretation \<alpha>: natural_isomorphism CCC.comp C T.ToTC T.ToCT \<alpha>
    proof -
      interpret \<alpha>: transformation_by_components CCC.comp C T.ToTC T.ToCT \<alpha>
        apply unfold_locales
        unfolding \<alpha>_def T.ToTC_def T.ToCT_def T\<^sub>E\<^sub>M\<^sub>C_def
        using comp_arr_dom comp_cod_arr assoc_naturality
        by simp_all
      interpret \<alpha>: natural_isomorphism CCC.comp C T.ToTC T.ToCT \<alpha>.map
        using iso_assoc \<alpha>.map_simp_ide assoc_in_hom tensor_preserves_ide \<alpha>_def
        by (unfold_locales, auto)
      have "\<alpha> = \<alpha>.map"
        using assoc_naturality \<alpha>_def comp_cod_arr T.ToTC_def T\<^sub>E\<^sub>M\<^sub>C_def \<alpha>.map_def by auto
      thus "natural_isomorphism CCC.comp C T.ToTC T.ToCT \<alpha>"
        using \<alpha>.natural_isomorphism_axioms by simp
    qed

    lemma natural_isomorphism_\<alpha>:
    shows "natural_isomorphism CCC.comp C T.ToTC T.ToCT \<alpha>" ..

    interpretation \<alpha>': inverse_transformation CCC.comp C T.ToTC T.ToCT \<alpha> ..

    interpretation \<ll>: natural_isomorphism C C L\<^sub>E\<^sub>M\<^sub>C map \<ll>\<^sub>E\<^sub>M\<^sub>C
    proof -
      interpret \<ll>: transformation_by_components C C L\<^sub>E\<^sub>M\<^sub>C map \<open>\<lambda>a. \<l>[a]\<close>
        using lunit_naturality L\<^sub>E\<^sub>M\<^sub>C_def by (unfold_locales, auto)
      interpret \<ll>: natural_isomorphism C C L\<^sub>E\<^sub>M\<^sub>C map \<ll>.map
        using iso_lunit by (unfold_locales, simp)
      have "\<ll>.map = \<ll>\<^sub>E\<^sub>M\<^sub>C"
        using \<ll>.map_def lunit_naturality \<ll>\<^sub>E\<^sub>M\<^sub>C_def L\<^sub>E\<^sub>M\<^sub>C_def by fastforce
      thus "natural_isomorphism C C L\<^sub>E\<^sub>M\<^sub>C map \<ll>\<^sub>E\<^sub>M\<^sub>C"
        using \<ll>.natural_isomorphism_axioms by force
    qed

    lemma natural_isomorphism_\<ll>:
    shows "natural_isomorphism C C L\<^sub>E\<^sub>M\<^sub>C map \<ll>\<^sub>E\<^sub>M\<^sub>C" ..

    interpretation \<ll>': inverse_transformation C C L\<^sub>E\<^sub>M\<^sub>C map \<ll>\<^sub>E\<^sub>M\<^sub>C ..

    interpretation \<rho>: natural_isomorphism C C R\<^sub>E\<^sub>M\<^sub>C map \<rho>\<^sub>E\<^sub>M\<^sub>C
    proof -
      interpret \<rho>: transformation_by_components C C R\<^sub>E\<^sub>M\<^sub>C map \<open>\<lambda>a. \<r>[a]\<close>
        using runit_naturality R\<^sub>E\<^sub>M\<^sub>C_def by (unfold_locales, auto)
      interpret \<rho>: natural_isomorphism C C R\<^sub>E\<^sub>M\<^sub>C map \<rho>.map
        using iso_runit \<rho>.map_simp_ide by (unfold_locales, simp)
      have "\<rho>\<^sub>E\<^sub>M\<^sub>C = \<rho>.map"
        using \<rho>.map_def runit_naturality T_simp \<rho>\<^sub>E\<^sub>M\<^sub>C_def R\<^sub>E\<^sub>M\<^sub>C_def by fastforce
      thus "natural_isomorphism C C R\<^sub>E\<^sub>M\<^sub>C map \<rho>\<^sub>E\<^sub>M\<^sub>C"
        using \<rho>.natural_isomorphism_axioms by force
    qed

    lemma natural_isomorphism_\<rho>:
    shows "natural_isomorphism C C R\<^sub>E\<^sub>M\<^sub>C map \<rho>\<^sub>E\<^sub>M\<^sub>C" ..

    interpretation \<rho>': inverse_transformation C C R\<^sub>E\<^sub>M\<^sub>C map \<rho>\<^sub>E\<^sub>M\<^sub>C ..

    text\<open>
      The endofunctors @{term L\<^sub>E\<^sub>M\<^sub>C} and @{term R\<^sub>E\<^sub>M\<^sub>C} are equivalence functors,
      due to the existence of the unitors.
\<close>

    lemma L_is_equivalence_functor:
    shows "equivalence_functor C C L\<^sub>E\<^sub>M\<^sub>C"
    proof -
      interpret endofunctor C L\<^sub>E\<^sub>M\<^sub>C ..
      show ?thesis
        using isomorphic_to_identity_is_equivalence \<ll>.natural_isomorphism_axioms by simp
    qed

    interpretation L: equivalence_functor C C L\<^sub>E\<^sub>M\<^sub>C
      using L_is_equivalence_functor by auto

    lemma R_is_equivalence_functor:
    shows "equivalence_functor C C R\<^sub>E\<^sub>M\<^sub>C"
    proof -
      interpret endofunctor C R\<^sub>E\<^sub>M\<^sub>C ..
      show ?thesis
        using isomorphic_to_identity_is_equivalence \<rho>.natural_isomorphism_axioms by simp
    qed

    interpretation R: equivalence_functor C C R\<^sub>E\<^sub>M\<^sub>C
      using R_is_equivalence_functor by auto

    text\<open>
      To complete an interpretation of the @{locale "monoidal_category"} locale,
      we define @{term "\<iota> \<equiv> \<l>[\<I>]"}.
      We could also have chosen @{term "\<iota> \<equiv> \<rho>[\<I>]"} as the two are equal, though to prove
      that requires some work yet.
\<close>

    definition \<iota>
    where "\<iota> \<equiv> \<l>[\<I>]"

    lemma \<iota>_in_hom:
    shows "\<guillemotleft>\<iota> : \<I> \<otimes> \<I> \<rightarrow> \<I>\<guillemotright>"
      using lunit_in_hom \<iota>_def by simp

    lemma induces_monoidal_category:
    shows "monoidal_category C T\<^sub>E\<^sub>M\<^sub>C \<alpha> \<iota>"
    proof -
      interpret L: equivalence_functor C C \<open>\<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (cod \<iota>, f)\<close>
      proof -
        have "L\<^sub>E\<^sub>M\<^sub>C = (\<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (cod \<iota>, f))" using \<iota>_in_hom L\<^sub>E\<^sub>M\<^sub>C_def by auto
        thus "equivalence_functor C C (\<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (cod \<iota>, f))"
          using L.equivalence_functor_axioms T\<^sub>E\<^sub>M\<^sub>C_def L\<^sub>E\<^sub>M\<^sub>C_def by simp
      qed
      interpret R: equivalence_functor C C \<open>\<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (f, cod \<iota>)\<close>
      proof -
        have "R\<^sub>E\<^sub>M\<^sub>C = (\<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (f, cod \<iota>))" using \<iota>_in_hom R\<^sub>E\<^sub>M\<^sub>C_def by auto
        thus "equivalence_functor C C (\<lambda>f. T\<^sub>E\<^sub>M\<^sub>C (f, cod \<iota>))"
          using R.equivalence_functor_axioms T\<^sub>E\<^sub>M\<^sub>C_def R\<^sub>E\<^sub>M\<^sub>C_def by simp
      qed
      show ?thesis
      proof
        show "\<guillemotleft>\<iota> : T\<^sub>E\<^sub>M\<^sub>C (cod \<iota>, cod \<iota>) \<rightarrow> cod \<iota>\<guillemotright>" using \<iota>_in_hom by fastforce
        show "iso \<iota>" using iso_lunit \<iota>_def by simp
        show "\<And>a b c d. \<lbrakk> ide a; ide b; ide c; ide d \<rbrakk> \<Longrightarrow>
                        T\<^sub>E\<^sub>M\<^sub>C (a, \<alpha> (b, c, d)) \<cdot> \<alpha> (a, T\<^sub>E\<^sub>M\<^sub>C (b, c), d) \<cdot> T\<^sub>E\<^sub>M\<^sub>C (\<alpha> (a, b, c), d)
                          = \<alpha> (a, b, T\<^sub>E\<^sub>M\<^sub>C (c, d)) \<cdot> \<alpha> (T\<^sub>E\<^sub>M\<^sub>C (a, b), c, d)"
          using pentagon tensor_preserves_ide by simp
      qed
    qed

    interpretation MC: monoidal_category C T\<^sub>E\<^sub>M\<^sub>C \<alpha> \<iota>
      using induces_monoidal_category by auto

    text\<open>
      We now show that the notions defined in the interpretation \<open>MC\<close> agree with their
      counterparts in the present locale.  These facts are needed if we define an
      interpretation for the @{locale elementary_monoidal_category} locale, use it to
      obtain the induced interpretation for @{locale monoidal_category}, and then want to
      transfer facts obtained in the induced interpretation back to the original one.
\<close>

    lemma \<I>_agreement:
    shows "\<I> = MC.unity"
      using \<iota>_in_hom MC.unity_def by auto

    lemma L\<^sub>E\<^sub>M\<^sub>C_agreement:
    shows "L\<^sub>E\<^sub>M\<^sub>C = MC.L"
      using \<iota>_in_hom L\<^sub>E\<^sub>M\<^sub>C_def MC.unity_def by auto

    lemma R\<^sub>E\<^sub>M\<^sub>C_agreement:
    shows "R\<^sub>E\<^sub>M\<^sub>C = MC.R"
      using \<iota>_in_hom R\<^sub>E\<^sub>M\<^sub>C_def MC.unity_def by auto

    text\<open>
      We wish to show that the components of the unitors @{term MC.\<ll>} and @{term MC.\<rho>}
      defined in the induced interpretation \<open>MC\<close> agree with those given by the
      parameters @{term lunit} and @{term runit} to the present locale.  To avoid a lengthy
      development that repeats work already done in the @{locale monoidal_category} locale,
      we establish the agreement in a special case and then use the properties already
      shown for \<open>MC\<close> to prove the general case.  In particular, we first show that
      @{term "\<l>[\<I>] = MC.lunit MC.unity"} and @{term "\<r>[\<I>] = MC.runit MC.unity"},
      from which it follows by facts already proved for @{term MC} that both are equal to @{term \<iota>}.
      We then show that for an arbitrary identity @{term a} the arrows @{term "\<l>[a]"}
      and @{term "\<r>[a]"} satisfy the equations that uniquely characterize the components
      @{term "MC.lunit a"} and @{term "MC.runit a"}, respectively, and are therefore equal
      to those components.
\<close>
      
    lemma unitor_coincidence\<^sub>E\<^sub>M\<^sub>C:
    shows "\<l>[\<I>] = \<iota>" and "\<r>[\<I>] = \<iota>"
    proof -
      have "\<r>[\<I>] = MC.runit MC.unity"
      proof (intro MC.runit_eqI)
        show "\<guillemotleft>\<r>[\<I>] : MC.tensor MC.unity MC.unity \<rightarrow> MC.unity\<guillemotright>"
          using runit_in_hom \<iota>_in_hom MC.unity_def by auto
        show "MC.tensor \<r>[\<I>] MC.unity
                = MC.tensor MC.unity \<iota> \<cdot> MC.assoc MC.unity MC.unity MC.unity"
          using T\<^sub>E\<^sub>M\<^sub>C_def \<iota>_in_hom \<iota>_def triangle MC.unity_def
          by (elim in_homE, auto)
      qed
      moreover have "\<l>[\<I>] = MC.lunit MC.unity"
      proof (intro MC.lunit_eqI)
        show "\<guillemotleft>\<l>[\<I>] : MC.tensor MC.unity MC.unity \<rightarrow> MC.unity\<guillemotright>"
          using lunit_in_hom [of \<I>] \<iota>_in_hom MC.unity_def by auto
        show "MC.tensor MC.unity \<l>[\<I>]
                = MC.tensor \<iota> MC.unity \<cdot> MC.assoc' MC.unity MC.unity MC.unity"
          using T\<^sub>E\<^sub>M\<^sub>C_def lunit_in_hom \<iota>_in_hom \<iota>_def MC.\<iota>_triangle by argo
      qed
      moreover have "MC.lunit MC.unity = \<iota> \<and> MC.runit MC.unity = \<iota>"
        using MC.unitor_coincidence by simp
      ultimately have 1: "\<l>[\<I>] = \<iota> \<and> \<r>[\<I>] = \<iota>" by simp
      show "\<l>[\<I>] = \<iota>" using 1 by simp
      show "\<r>[\<I>] = \<iota>" using 1 by simp
    qed

    lemma lunit_char\<^sub>E\<^sub>M\<^sub>C:
    assumes "ide a"
    shows "\<I> \<otimes> \<l>[a] = (\<iota> \<otimes> a) \<cdot> MC.assoc' MC.unity MC.unity a"
    proof -
      have "(\<r>[\<I>] \<otimes> a) \<cdot> MC.assoc' MC.unity MC.unity a
                = ((\<I> \<otimes> \<l>[a]) \<cdot> \<a>[\<I>, \<I>, a]) \<cdot> MC.assoc' MC.unity MC.unity a"
        using assms triangle by simp
      also have "... = \<I> \<otimes> \<l>[a]"
        using assms MC.assoc_inv comp_arr_inv \<I>_agreement iso_assoc comp_arr_dom comp_assoc
        by auto
      finally have "\<I> \<otimes> \<l>[a] = (\<r>[\<I>] \<otimes> a) \<cdot> MC.assoc' MC.unity MC.unity a" by argo
      thus "\<I> \<otimes> \<l>[a] = (\<iota> \<otimes> a) \<cdot> MC.assoc' MC.unity MC.unity a"
        using unitor_coincidence\<^sub>E\<^sub>M\<^sub>C by auto
    qed
    
    lemma runit_char\<^sub>E\<^sub>M\<^sub>C:
    assumes "ide a"
    shows "\<r>[a] \<otimes> \<I> = (a \<otimes> \<iota>) \<cdot> \<a>[a, \<I>, \<I>]"
      using assms triangle \<iota>_def by simp

    lemma \<ll>\<^sub>E\<^sub>M\<^sub>C_agreement:
    shows "\<ll>\<^sub>E\<^sub>M\<^sub>C = MC.\<ll>"
    proof
      fix f
      have "\<not> arr f \<Longrightarrow> \<ll>\<^sub>E\<^sub>M\<^sub>C f = MC.\<ll> f" by (simp add: \<ll>\<^sub>E\<^sub>M\<^sub>C_def)
      moreover have "arr f \<Longrightarrow> \<ll>\<^sub>E\<^sub>M\<^sub>C f = MC.\<ll> f"
      proof -
        have "\<And>a. ide a \<Longrightarrow> \<l>[a] = MC.lunit a"
          using \<I>_agreement T\<^sub>E\<^sub>M\<^sub>C_def lunit_char\<^sub>E\<^sub>M\<^sub>C \<iota>_in_hom
          by (intro MC.lunit_eqI, auto)
        thus ?thesis using \<ll>\<^sub>E\<^sub>M\<^sub>C_def by force
      qed
      ultimately show "\<ll>\<^sub>E\<^sub>M\<^sub>C f = MC.\<ll> f" by blast
    qed

    lemma \<rho>\<^sub>E\<^sub>M\<^sub>C_agreement:
    shows "\<rho>\<^sub>E\<^sub>M\<^sub>C = MC.\<rho>"
    proof
      fix f
      have "\<not> arr f \<Longrightarrow> \<rho>\<^sub>E\<^sub>M\<^sub>C f = MC.\<rho> f" by (simp add: \<rho>\<^sub>E\<^sub>M\<^sub>C_def)
      moreover have "arr f \<Longrightarrow> \<rho>\<^sub>E\<^sub>M\<^sub>C f = MC.\<rho> f"
      proof -
        have "\<And>a. ide a \<Longrightarrow> \<r>[a] = MC.runit a"
          using \<I>_agreement T\<^sub>E\<^sub>M\<^sub>C_def runit_char\<^sub>E\<^sub>M\<^sub>C \<iota>_in_hom
          by (intro MC.runit_eqI, auto)
        thus ?thesis using \<rho>\<^sub>E\<^sub>M\<^sub>C_def by force
      qed
      ultimately show "\<rho>\<^sub>E\<^sub>M\<^sub>C f = MC.\<rho> f" by blast
    qed

    lemma assoc_agreement:
    assumes "ide a" and "ide b" and "ide c"
    shows "MC.assoc a b c = \<a>[a, b, c]"
      using assms \<alpha>_ide_simp by auto

    lemma lunit_agreement:
    assumes "ide a"
    shows "MC.lunit a = \<l>[a]"
    proof -
      have "MC.lunit a = \<ll>\<^sub>E\<^sub>M\<^sub>C a"
        using assms comp_cod_arr \<ll>\<^sub>E\<^sub>M\<^sub>C_agreement by simp
      also have "... = \<l>[a]"
        using assms \<ll>\<^sub>E\<^sub>M\<^sub>C_def comp_cod_arr by simp
      finally show ?thesis by simp
    qed

    lemma runit_agreement:
    assumes "ide a"
    shows "MC.runit a = \<r>[a]"
    proof -
      have "MC.runit a = \<rho>\<^sub>E\<^sub>M\<^sub>C a"
        using assms comp_cod_arr \<rho>\<^sub>E\<^sub>M\<^sub>C_agreement by simp
      also have "... = \<r>[a]"
        using assms \<rho>\<^sub>E\<^sub>M\<^sub>C_def comp_cod_arr by simp
      finally show ?thesis by simp
    qed

  end

  section "Strict Monoidal Category"

  text\<open>
    A monoidal category is \emph{strict} if the components of the associator and unitors
    are all identities.
\<close>
      
  locale strict_monoidal_category =
    monoidal_category +
  assumes strict_assoc: "\<lbrakk> ide a0; ide a1; ide a2 \<rbrakk> \<Longrightarrow> ide \<a>[a0, a1, a2]"
  and strict_lunit: "ide a \<Longrightarrow> \<l>[a] = a"
  and strict_runit: "ide a \<Longrightarrow> \<r>[a] = a"
  begin

    lemma strict_unit:
    shows "\<iota> = \<I>"
      using strict_lunit unitor_coincidence(1) by auto

    lemma tensor_assoc [simp]:
    assumes "arr f0" and "arr f1" and "arr f2"
    shows "(f0 \<otimes> f1) \<otimes> f2 = f0 \<otimes> f1 \<otimes> f2"
    proof -
      have "(f0 \<otimes> f1) \<otimes> f2 = \<a>[cod f0, cod f1, cod f2] \<cdot> ((f0 \<otimes> f1) \<otimes> f2)"
        using assms assoc_in_hom [of "cod f0" "cod f1" "cod f2"] strict_assoc comp_cod_arr
        by auto
      also have "... = (f0 \<otimes> f1 \<otimes> f2) \<cdot> \<a>[dom f0, dom f1, dom f2]"
        using assms assoc_naturality by simp
      also have "... = f0 \<otimes> f1 \<otimes> f2"
        using assms assoc_in_hom [of "dom f0" "dom f1" "dom f2"] strict_assoc comp_arr_dom
        by auto
      finally show ?thesis by simp
    qed

  end

  section "Opposite Monoidal Category"

  text\<open>
    The \emph{opposite} of a monoidal category has the same underlying category, but the
    arguments to the tensor product are reversed and the associator is inverted and its
    arguments reversed.
\<close>
      
  locale opposite_monoidal_category =
    C: monoidal_category C T\<^sub>C \<alpha>\<^sub>C \<iota>
  for C :: "'a comp"      (infixr "\<cdot>" 55)
  and T\<^sub>C :: "'a * 'a \<Rightarrow> 'a"
  and \<alpha>\<^sub>C :: "'a * 'a * 'a \<Rightarrow> 'a"
  and \<iota> :: 'a
  begin

    abbreviation T
    where "T f \<equiv> T\<^sub>C (snd f, fst f)"

    abbreviation \<alpha>
    where "\<alpha> f \<equiv> C.\<alpha>' (snd (snd f), fst (snd f), fst f)"

  end

  sublocale opposite_monoidal_category \<subseteq> monoidal_category C T \<alpha> \<iota>
  proof -
    interpret T: binary_endofunctor C T
      using C.T.is_extensional C.CC.seq_char C.interchange by (unfold_locales, auto)
    interpret ToTC: "functor" C.CCC.comp C T.ToTC
      using T.functor_ToTC by auto
    interpret ToCT: "functor" C.CCC.comp C T.ToCT
      using T.functor_ToCT by auto
    interpret \<alpha>: natural_transformation C.CCC.comp C T.ToTC T.ToCT \<alpha>
      using C.\<alpha>'.is_extensional C.CCC.dom_char C.CCC.cod_char T.ToTC_def T.ToCT_def
            C.\<alpha>'_simp C.\<alpha>'.naturality
      by (unfold_locales, auto)
    interpret \<alpha>: natural_isomorphism C.CCC.comp C T.ToTC T.ToCT \<alpha>
      using C.\<alpha>'.components_are_iso by (unfold_locales, simp)
    interpret L: equivalence_functor C C \<open>\<lambda>f. T (C.cod \<iota>, f)\<close>
      using C.R.equivalence_functor_axioms by simp
    interpret R: equivalence_functor C C \<open>\<lambda>f. T (f, C.cod \<iota>)\<close>
      using C.L.equivalence_functor_axioms by simp
    show "monoidal_category C T \<alpha> \<iota>"
      using C.\<iota>_in_hom C.\<iota>_is_iso C.unity_def C.pentagon' C.comp_assoc
      by (unfold_locales, auto)
  qed

  context opposite_monoidal_category
  begin

    lemma lunit_simp:
    assumes "C.ide a"
    shows "lunit a = C.runit a"
      using assms lunit_char C.iso_assoc by (intro C.runit_eqI, auto)

    lemma runit_simp:
    assumes "C.ide a"
    shows "runit a = C.lunit a"
      using assms runit_char C.iso_assoc by (intro C.lunit_eqI, auto)

  end

  section "Monoidal Language"

  text\<open>
    In this section we assume that a category @{term C} is given, and we define a
    formal syntax of terms constructed from arrows of @{term C} using function symbols
    that correspond to unity, composition, tensor, the associator and its formal inverse,
    and the left and right unitors and their formal inverses.
    We will use this syntax to state and prove the coherence theorem and then to construct
    the free monoidal category generated by @{term C}.
\<close>

  locale monoidal_language =
    C: category C
    for C :: "'a comp"                     (infixr "\<cdot>" 55)
  begin

    datatype (discs_sels) 't "term" =
      Prim 't                              ("\<^bold>\<langle>_\<^bold>\<rangle>")
    | Unity                                ("\<^bold>\<I>")
    | Tensor "'t term" "'t term"           (infixr "\<^bold>\<otimes>" 53)
    | Comp "'t term" "'t term"             (infixr "\<^bold>\<cdot>" 55)
    | Lunit "'t term"                      ("\<^bold>\<l>\<^bold>[_\<^bold>]")
    | Lunit' "'t term"                     ("\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[_\<^bold>]")
    | Runit "'t term"                      ("\<^bold>\<r>\<^bold>[_\<^bold>]")
    | Runit' "'t term"                     ("\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[_\<^bold>]")
    | Assoc "'t term" "'t term" "'t term"  ("\<^bold>\<a>\<^bold>[_, _, _\<^bold>]")
    | Assoc' "'t term" "'t term" "'t term" ("\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[_, _, _\<^bold>]")

    lemma not_is_Tensor_Unity:
    shows "\<not> is_Tensor Unity"
      by simp

    text\<open>
      We define formal domain and codomain functions on terms.
\<close>

    primrec Dom :: "'a term \<Rightarrow> 'a term"
    where "Dom \<^bold>\<langle>f\<^bold>\<rangle> = \<^bold>\<langle>C.dom f\<^bold>\<rangle>"
        | "Dom \<^bold>\<I> = \<^bold>\<I>"
        | "Dom (t \<^bold>\<otimes> u) = (Dom t \<^bold>\<otimes> Dom u)"
        | "Dom (t \<^bold>\<cdot> u) = Dom u"
        | "Dom \<^bold>\<l>\<^bold>[t\<^bold>] = (\<^bold>\<I> \<^bold>\<otimes> Dom t)"
        | "Dom \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Dom t"
        | "Dom \<^bold>\<r>\<^bold>[t\<^bold>] = (Dom t \<^bold>\<otimes> \<^bold>\<I>)"
        | "Dom \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Dom t"
        | "Dom \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = ((Dom t \<^bold>\<otimes> Dom u) \<^bold>\<otimes> Dom v)"
        | "Dom \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = (Dom t \<^bold>\<otimes> (Dom u \<^bold>\<otimes> Dom v))"

    primrec Cod :: "'a term \<Rightarrow> 'a term"
    where "Cod \<^bold>\<langle>f\<^bold>\<rangle> = \<^bold>\<langle>C.cod f\<^bold>\<rangle>"
        | "Cod \<^bold>\<I> = \<^bold>\<I>"
        | "Cod (t \<^bold>\<otimes> u) = (Cod t \<^bold>\<otimes> Cod u)"
        | "Cod (t \<^bold>\<cdot> u) = Cod t"
        | "Cod \<^bold>\<l>\<^bold>[t\<^bold>] = Cod t"
        | "Cod \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = (\<^bold>\<I> \<^bold>\<otimes> Cod t)"
        | "Cod \<^bold>\<r>\<^bold>[t\<^bold>] = Cod t"
        | "Cod \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = (Cod t \<^bold>\<otimes> \<^bold>\<I>)"
        | "Cod \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = (Cod t \<^bold>\<otimes> (Cod u \<^bold>\<otimes> Cod v))"
        | "Cod \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = ((Cod t \<^bold>\<otimes> Cod u) \<^bold>\<otimes> Cod v)"

    text\<open>
      A term is a ``formal arrow'' if it is constructed from arrows of @{term[source=true] C}
      in such a way that composition is applied only to formally composable pairs of terms.
\<close>

    primrec Arr :: "'a term \<Rightarrow> bool"
    where "Arr \<^bold>\<langle>f\<^bold>\<rangle> = C.arr f"
        | "Arr \<^bold>\<I> = True"
        | "Arr (t \<^bold>\<otimes> u) = (Arr t \<and> Arr u)"
        | "Arr (t \<^bold>\<cdot> u) = (Arr t \<and> Arr u \<and> Dom t = Cod u)"
        | "Arr \<^bold>\<l>\<^bold>[t\<^bold>] = Arr t"
        | "Arr \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Arr t"
        | "Arr \<^bold>\<r>\<^bold>[t\<^bold>] = Arr t"
        | "Arr \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Arr t"
        | "Arr \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = (Arr t \<and> Arr u \<and> Arr v)"
        | "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = (Arr t \<and> Arr u \<and> Arr v)"

    abbreviation Par :: "'a term \<Rightarrow> 'a term \<Rightarrow> bool"
    where "Par t u \<equiv> Arr t \<and> Arr u \<and> Dom t = Dom u \<and> Cod t = Cod u"

    abbreviation Seq :: "'a term \<Rightarrow> 'a term \<Rightarrow> bool"
    where "Seq t u \<equiv> Arr t \<and> Arr u \<and> Dom t = Cod u"

    abbreviation Hom :: "'a term \<Rightarrow> 'a term \<Rightarrow> 'a term set"
    where "Hom a b \<equiv> { t. Arr t \<and> Dom t = a \<and> Cod t = b }"

    text\<open>
      A term is a ``formal identity'' if it is constructed from identity arrows of
      @{term[source=true] C} and @{term "\<^bold>\<I>"} using only the \<open>\<^bold>\<otimes>\<close> operator.
\<close>

    primrec Ide :: "'a term \<Rightarrow> bool"
    where "Ide \<^bold>\<langle>f\<^bold>\<rangle> = C.ide f"
        | "Ide \<^bold>\<I> = True"
        | "Ide (t \<^bold>\<otimes> u) = (Ide t \<and> Ide u)"
        | "Ide (t \<^bold>\<cdot> u) = False"
        | "Ide \<^bold>\<l>\<^bold>[t\<^bold>] = False"
        | "Ide \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = False"
        | "Ide \<^bold>\<r>\<^bold>[t\<^bold>] = False"
        | "Ide \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = False"
        | "Ide \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = False"
        | "Ide \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = False"

    lemma Ide_implies_Arr [simp]:
    shows "Ide t \<Longrightarrow> Arr t"
      by (induct t) auto

    lemma Arr_implies_Ide_Dom [elim]:
    shows "Arr t \<Longrightarrow> Ide (Dom t)"
      by (induct t) auto

    lemma Arr_implies_Ide_Cod [elim]:
    shows "Arr t \<Longrightarrow> Ide (Cod t)"
      by (induct t) auto

    lemma Ide_in_Hom [simp]:
    shows "Ide t \<Longrightarrow> t \<in> Hom t t"
      by (induct t) auto

    text\<open>
      A formal arrow is ``canonical'' if the only arrows of @{term[source=true] C} used in its
      construction are identities.
\<close>

    primrec Can :: "'a term \<Rightarrow> bool"
    where "Can \<^bold>\<langle>f\<^bold>\<rangle> = C.ide f"
        | "Can \<^bold>\<I> = True"
        | "Can (t \<^bold>\<otimes> u) = (Can t \<and> Can u)"
        | "Can (t \<^bold>\<cdot> u) = (Can t \<and> Can u \<and> Dom t = Cod u)"
        | "Can \<^bold>\<l>\<^bold>[t\<^bold>] = Can t"
        | "Can \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Can t"
        | "Can \<^bold>\<r>\<^bold>[t\<^bold>] = Can t"
        | "Can \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Can t"
        | "Can \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = (Can t \<and> Can u \<and> Can v)"
        | "Can \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = (Can t \<and> Can u \<and> Can v)"

    lemma Ide_implies_Can:
    shows "Ide t \<Longrightarrow> Can t"
      by (induct t) auto

    lemma Can_implies_Arr:
    shows "Can t \<Longrightarrow> Arr t"
      by (induct t) auto

    text\<open>
      We next define the formal inverse of a term.
      This is only sensible for formal arrows built using only isomorphisms of
      @{term[source=true] C}; in particular, for canonical formal arrows.
\<close>

    primrec Inv :: "'a term \<Rightarrow> 'a term"
    where "Inv \<^bold>\<langle>f\<^bold>\<rangle> = \<^bold>\<langle>C.inv f\<^bold>\<rangle>"
        | "Inv \<^bold>\<I> = \<^bold>\<I>"
        | "Inv (t \<^bold>\<otimes> u) = (Inv t \<^bold>\<otimes> Inv u)"
        | "Inv (t \<^bold>\<cdot> u) = (Inv u \<^bold>\<cdot> Inv t)"
        | "Inv \<^bold>\<l>\<^bold>[t\<^bold>] = \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Inv t\<^bold>]"
        | "Inv \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = \<^bold>\<l>\<^bold>[Inv t\<^bold>]"
        | "Inv \<^bold>\<r>\<^bold>[t\<^bold>] = \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Inv t\<^bold>]"
        | "Inv \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = \<^bold>\<r>\<^bold>[Inv t\<^bold>]"
        | "Inv \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Inv t, Inv u, Inv v\<^bold>]"
        | "Inv \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = \<^bold>\<a>\<^bold>[Inv t, Inv u, Inv v\<^bold>]"

    lemma Inv_preserves_Ide:
    shows "Ide t \<Longrightarrow> Ide (Inv t)"
      by (induct t) auto

    lemma Inv_preserves_Can:
    assumes "Can t"
    shows "Can (Inv t)" and "Dom (Inv t) = Cod t" and "Cod (Inv t) = Dom t"
    proof -
      have 0: "Can t \<Longrightarrow> Can (Inv t) \<and> Dom (Inv t) = Cod t \<and> Cod (Inv t) = Dom t"
        by (induct t) auto
      show "Can (Inv t)" using assms 0 by blast
      show "Dom (Inv t) = Cod t" using assms 0 by blast
      show "Cod (Inv t) = Dom t" using assms 0 by blast
    qed

    lemma Inv_in_Hom [simp]:
    assumes "Can t"
    shows "Inv t \<in> Hom (Cod t) (Dom t)"
      using assms Inv_preserves_Can Can_implies_Arr by simp

    lemma Inv_Ide [simp]:
    assumes "Ide a"
    shows "Inv a = a"
      using assms by (induct a) auto

    lemma Inv_Inv [simp]:
    assumes "Can t"
    shows "Inv (Inv t) = t"
      using assms by (induct t) auto

    text\<open>
      We call a term ``diagonal'' if it is either @{term "\<^bold>\<I>"} or it is constructed from
      arrows of @{term[source=true] C} using only the \<open>\<^bold>\<otimes>\<close> operator associated to the right.
      Essentially, such terms are lists of arrows of @{term[source=true] C}, where @{term "\<^bold>\<I>"}
      represents the empty list and \<open>\<^bold>\<otimes>\<close> is used as the list constructor.
      We call them ``diagonal'' because terms can regarded as defining ``interconnection matrices''
      of arrows connecting ``inputs'' to ``outputs'', and from this point of view diagonal
      terms correspond to diagonal matrices.  The matrix point of view is suggestive for the
      extension of the results presented here to the symmetric monoidal and cartesian monoidal
      cases.
\<close>

    fun Diag :: "'a term \<Rightarrow> bool"
    where "Diag \<^bold>\<I> = True"
        | "Diag \<^bold>\<langle>f\<^bold>\<rangle> = C.arr f"
        | "Diag (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> u) = (C.arr f \<and> Diag u \<and> u \<noteq> \<^bold>\<I>)"
        | "Diag _ = False"

    lemma Diag_TensorE:
    assumes "Diag (Tensor t u)"
    shows "\<^bold>\<langle>un_Prim t\<^bold>\<rangle> = t" and "C.arr (un_Prim t)" and "Diag t" and "Diag u" and "u \<noteq> \<^bold>\<I>"
    proof -
      have 1: "t = \<^bold>\<langle>un_Prim t\<^bold>\<rangle> \<and> C.arr (un_Prim t) \<and> Diag t \<and> Diag u \<and> u \<noteq> \<^bold>\<I>"
        using assms by (cases t; simp; cases u; simp)
      show "\<^bold>\<langle>un_Prim t\<^bold>\<rangle> = t" using 1 by simp
      show "C.arr (un_Prim t)" using 1 by simp
      show "Diag t" using 1 by simp
      show "Diag u" using 1 by simp
      show "u \<noteq> \<^bold>\<I>" using 1 by simp
    qed

    lemma Diag_implies_Arr [elim]:
    shows "Diag t \<Longrightarrow> Arr t"
      apply (induct t, simp_all)
      by (simp add: Diag_TensorE)

    lemma Dom_preserves_Diag [elim]:
    shows "Diag t \<Longrightarrow> Diag (Dom t)"
    apply (induct t, simp_all)
    proof -
      fix u v
      assume I2: "Diag v \<Longrightarrow> Diag (Dom v)"
      assume uv: "Diag (u \<^bold>\<otimes> v)"
      show "Diag (Dom u \<^bold>\<otimes> Dom v)"
      proof -
        have 1: "is_Prim (Dom u) \<and> C.arr (un_Prim (Dom u)) \<and>
                 Dom u = \<^bold>\<langle>C.dom (un_Prim u)\<^bold>\<rangle>"
          using uv by (cases u; simp; cases v, simp_all)
        have 2: "Diag v \<and> v \<noteq> \<^bold>\<I> \<and> \<not> is_Comp v \<and> \<not> is_Lunit' v \<and> \<not> is_Runit' v"
          using uv by (cases u; simp; cases v, simp_all)
        have "Diag (Dom v) \<and> Dom v \<noteq> \<^bold>\<I>"
          using 2 I2 by (cases v, simp_all)
        thus ?thesis using 1 by force
      qed
    qed
    
    lemma Cod_preserves_Diag [elim]:
    shows "Diag t \<Longrightarrow> Diag (Cod t)"
    apply (induct t, simp_all)
    proof -
      fix u v
      assume I2: "Diag v \<Longrightarrow> Diag (Cod v)"
      assume uv: "Diag (u \<^bold>\<otimes> v)"
      show "Diag (Cod u \<^bold>\<otimes> Cod v)"
      proof -
        have 1: "is_Prim (Cod u) \<and> C.arr (un_Prim (Cod u)) \<and> Cod u = \<^bold>\<langle>C.cod (un_Prim u)\<^bold>\<rangle>"
          using uv by (cases u; simp; cases v; simp)
        have 2: "Diag v \<and> v \<noteq> \<^bold>\<I> \<and> \<not> is_Comp v \<and> \<not> is_Lunit' v \<and> \<not> is_Runit' v"
          using uv by (cases u; simp; cases v; simp)
        have "Diag (Cod v) \<and> Cod v \<noteq> \<^bold>\<I>"
          using I2 2 by (cases v, simp_all)
        thus ?thesis using 1 by force
      qed
    qed

    lemma Inv_preserves_Diag:
    assumes "Can t" and "Diag t"
    shows "Diag (Inv t)"
    proof -
      have "Can t \<and> Diag t \<Longrightarrow> Diag (Inv t)"
        apply (induct t, simp_all)
        by (metis (no_types, lifting) Can.simps(1) Inv.simps(1) Inv.simps(2) Diag.simps(3)
            Inv_Inv Diag_TensorE(1) C.inv_ide)
      thus ?thesis using assms by blast
    qed

    text\<open>
      The following function defines the ``dimension'' of a term,
      which is the number of arrows of @{term C} it contains.
      For diagonal terms, this is just the length of the term when regarded as a list
      of arrows of @{term C}.
      Alternatively, if a term is regarded as defining an interconnection matrix,
      then the dimension is the number of inputs (or outputs).
\<close>

    primrec dim :: "'a term \<Rightarrow> nat"
    where "dim \<^bold>\<langle>f\<^bold>\<rangle> = 1"
        | "dim \<^bold>\<I> = 0"
        | "dim (t \<^bold>\<otimes> u) = (dim t + dim u)"
        | "dim (t \<^bold>\<cdot> u) = dim t"
        | "dim \<^bold>\<l>\<^bold>[t\<^bold>] = dim t"
        | "dim \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = dim t"
        | "dim \<^bold>\<r>\<^bold>[t\<^bold>] = dim t"
        | "dim \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = dim t"
        | "dim \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = dim t + dim u + dim v"
        | "dim \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = dim t + dim u + dim v"

    text\<open>
      The following function defines a tensor product for diagonal terms.
      If terms are regarded as lists, this is just list concatenation.
      If terms are regarded as matrices, this corresponds to constructing a block
      diagonal matrix.
\<close>

    fun TensorDiag      (infixr "\<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor>" 53)
    where "\<^bold>\<I> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = u"
        | "t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<I> = t"
        | "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> u"
        | "(t \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
        | "t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = undefined"

    lemma TensorDiag_Prim [simp]:
    assumes "t \<noteq> \<^bold>\<I>"
    shows "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> t = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> t"
      using assms by (cases t, simp_all)

    lemma TensorDiag_term_Unity [simp]:
    shows "t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<I> = t"
      by (cases "t = \<^bold>\<I>"; cases t, simp_all)

    lemma TensorDiag_Diag:
    assumes "Diag (t \<^bold>\<otimes> u)"
    shows "t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = t \<^bold>\<otimes> u"
      using assms TensorDiag_Prim by (cases t, simp_all)

    lemma TensorDiag_preserves_Diag:
    assumes "Diag t" and "Diag u"
    shows "Diag (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
    and "Dom (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Dom t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u"
    and "Cod (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Cod t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
    proof -
      have 0: "\<And>u. \<lbrakk> Diag t; Diag u \<rbrakk> \<Longrightarrow>
                     Diag (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<and> Dom (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Dom t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u \<and>
                                       Cod (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Cod t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
      apply (induct t, simp_all)
      proof -
        fix f :: 'a and u :: "'a term"
        assume f: "C.arr f"
        assume u: "Diag u"
        show "Diag (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<and> Dom (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = \<^bold>\<langle>C.dom f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u \<and>
                                 Cod (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = \<^bold>\<langle>C.cod f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
          using u f by (cases u, simp_all)
        next
        fix u v w
        assume I1: "\<And>u. Diag v \<Longrightarrow> Diag u \<Longrightarrow> Diag (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<and>
                                              Dom (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Dom v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u \<and>
                                              Cod (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Cod v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
        assume I2: "\<And>u. Diag w \<Longrightarrow>  Diag u \<Longrightarrow> Diag (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<and>
                                               Dom (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u \<and>
                                               Cod (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
        assume vw: "Diag (v \<^bold>\<otimes> w)"
        assume u: "Diag u"
        show "Diag ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<and>
              Dom ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = (Dom v \<^bold>\<otimes> Dom w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u \<and>
              Cod ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = (Cod v \<^bold>\<otimes> Cod w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
        proof -
          have v: "v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<and> Diag v"
            using vw Diag_implies_Arr Diag_TensorE [of v w] by force
          have w: "Diag w"
            using vw by (simp add: Diag_TensorE)
          have "u = \<^bold>\<I> \<Longrightarrow> ?thesis" by (simp add: vw)
          moreover have "u \<noteq> \<^bold>\<I> \<Longrightarrow> ?thesis"
            using u v w I1 I2 Dom_preserves_Diag [of u] Cod_preserves_Diag [of u]
            by (cases u, simp_all)
          ultimately show ?thesis by blast
        qed
      qed
      show "Diag (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) " using assms 0 by blast
      show "Dom (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Dom t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u" using assms 0 by blast
      show "Cod (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Cod t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u" using assms 0 by blast
    qed

    lemma TensorDiag_in_Hom:
    assumes "Diag t" and "Diag u"
    shows "t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u \<in> Hom (Dom t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u) (Cod t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u)"
      using assms TensorDiag_preserves_Diag Diag_implies_Arr by simp

    lemma Dom_TensorDiag:
    assumes "Diag t" and "Diag u"
    shows "Dom (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Dom t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u"
      using assms TensorDiag_preserves_Diag(2) by simp

    lemma Cod_TensorDiag:
    assumes "Diag t" and "Diag u"
    shows "Cod (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Cod t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u"
      using assms TensorDiag_preserves_Diag(3) by simp

    lemma not_is_Tensor_TensorDiagE:
    assumes "\<not> is_Tensor (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)" and "Diag t" and "Diag u"
    and "t \<noteq> \<^bold>\<I>" and "u \<noteq> \<^bold>\<I>"
    shows "False"
    proof -
      have "\<lbrakk> \<not> is_Tensor (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u); Diag t; Diag u; t \<noteq> \<^bold>\<I>; u \<noteq> \<^bold>\<I> \<rbrakk> \<Longrightarrow> False"
      apply (induct t, simp_all)
      proof -
        fix v w
        assume I2: "\<not> is_Tensor (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<Longrightarrow> Diag w \<Longrightarrow> w \<noteq> \<^bold>\<I> \<Longrightarrow> False"
        assume 1: "\<not> is_Tensor ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
        assume vw: "Diag (v \<^bold>\<otimes> w)"
        assume u: "Diag u"
        assume 2: "u \<noteq> \<^bold>\<I>"
        show "False"
        proof -
          have v: "v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle>"
            using vw Diag_TensorE [of v w] by force
          have w: "Diag w \<and> w \<noteq> \<^bold>\<I>"
            using vw Diag_TensorE [of v w] by simp
          have "(v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = v \<^bold>\<otimes> (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
          proof -
            have "(v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
              using u 2 by (cases u, simp_all)
            also have "... = v \<^bold>\<otimes> (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
              using u v w I2 TensorDiag_Prim not_is_Tensor_Unity by metis
            finally show ?thesis by simp
          qed
          thus ?thesis using 1 by simp
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma TensorDiag_assoc:
    assumes "Diag t" and "Diag u" and "Diag v"
    shows "(t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
    proof -
      have "\<And>n t u v. \<lbrakk> dim t = n; Diag t; Diag u; Diag v \<rbrakk> \<Longrightarrow>
                        (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
      proof -
        fix n
        show "\<And>t u v. \<lbrakk> dim t = n; Diag t; Diag u; Diag v \<rbrakk> \<Longrightarrow>
                        (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
        proof (induction n rule: nat_less_induct)
          fix n :: nat and t :: "'a term" and u v
          assume I: "\<forall>m<n. \<forall>t u v. dim t = m \<longrightarrow> Diag t \<longrightarrow> Diag u \<longrightarrow> Diag v \<longrightarrow>
                                   (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
          assume dim: "dim t = n"
          assume t: "Diag t"
          assume u: "Diag u"
          assume v: "Diag v"
          show "(t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
          proof -
            have "t = \<^bold>\<I> \<Longrightarrow> ?thesis" by simp
            moreover have "u = \<^bold>\<I> \<Longrightarrow> ?thesis" by simp
            moreover have "v = \<^bold>\<I> \<Longrightarrow> ?thesis" by simp
            moreover have "t \<noteq> \<^bold>\<I> \<and> u \<noteq> \<^bold>\<I> \<and> v \<noteq> \<^bold>\<I> \<and> is_Prim t \<Longrightarrow> ?thesis"
              using v by (cases t, simp_all, cases u, simp_all; cases v, simp_all)
            moreover have "t \<noteq> \<^bold>\<I> \<and> u \<noteq> \<^bold>\<I> \<and> v \<noteq> \<^bold>\<I> \<and> is_Tensor t \<Longrightarrow> ?thesis"
            proof (cases t; simp)
              fix w :: "'a term" and x :: "'a term"
              assume 1: "u \<noteq> \<^bold>\<I> \<and> v \<noteq> \<^bold>\<I>"
              assume 2: "t = (w \<^bold>\<otimes> x)"
              show "((w \<^bold>\<otimes> x) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = (w \<^bold>\<otimes> x) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
              proof -
                have w: "w = \<^bold>\<langle>un_Prim w\<^bold>\<rangle>"
                  using t 1 2 Diag_TensorE [of w x] by auto
                have x: "Diag x"
                  using t w 1 2 by (cases w, simp_all)
                have "((w \<^bold>\<otimes> x) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = (w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (x \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v"
                  using u v w x 1 2 by (cases u, simp_all)
                also have "... = (w \<^bold>\<otimes> (x \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v"
                  using t w u 1 2 TensorDiag_Prim not_is_Tensor_TensorDiagE Diag_TensorE
                        not_is_Tensor_Unity
                  by metis
                also have "... = w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> ((x \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
                  using u v w x 1 by (cases u, simp_all; cases v, simp_all)
                also have "... = w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (x \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v))"
                proof -
                  have "dim x < dim t"
                    using w 2 by (cases w, simp_all)
                  thus ?thesis 
                    using u v x dim I by simp
                qed
                also have "... = (w \<^bold>\<otimes> x) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
                proof -
                  have 3: "is_Tensor (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
                    using u v 1 not_is_Tensor_TensorDiagE by auto
                  obtain u' :: "'a term" and v' where uv': "u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v = u' \<^bold>\<otimes> v'"
                    using 3 is_Tensor_def by blast
                  thus ?thesis by simp
                qed
                finally show ?thesis by simp
              qed
            qed
            moreover have "t = \<^bold>\<I> \<or> is_Prim t \<or> is_Tensor t"
              using t by (cases t, simp_all)
            ultimately show ?thesis by blast
          qed
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma TensorDiag_preserves_Ide:
    assumes "Ide t" and "Ide u" and "Diag t" and "Diag u"
    shows "Ide (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
      using assms
      by (metis (mono_tags, lifting) Arr_implies_Ide_Dom Ide_in_Hom Diag_implies_Arr
          TensorDiag_preserves_Diag(1) TensorDiag_preserves_Diag(2) mem_Collect_eq)

    lemma TensorDiag_preserves_Can:
    assumes "Can t" and "Can u" and "Diag t" and "Diag u"
    shows "Can (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
    proof -
      have "\<And>u. \<lbrakk> Can t \<and> Diag t; Can u \<and> Diag u \<rbrakk> \<Longrightarrow> Can (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
      proof (induct t; simp)
        show "\<And>x u. C.ide x \<and> C.arr x \<Longrightarrow> Can u \<and> Diag u \<Longrightarrow> Can (\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
          by (metis Ide.simps(1) Ide.simps(2) Ide_implies_Can Diag.simps(2) TensorDiag_Prim
                    TensorDiag_preserves_Ide Can.simps(3))
        show "\<And>t1 t2 u. (\<And>u. Diag t1 \<Longrightarrow> Can u \<and> Diag u \<Longrightarrow> Can (t1 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)) \<Longrightarrow>
                         (\<And>u. Diag t2 \<Longrightarrow> Can u \<and> Diag u \<Longrightarrow> Can (t2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)) \<Longrightarrow>
                         Can t1 \<and> Can t2 \<and> Diag (t1 \<^bold>\<otimes> t2) \<Longrightarrow> Can u \<and> Diag u \<Longrightarrow>
                         Can ((t1 \<^bold>\<otimes> t2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
          by (metis Diag_TensorE(3) Diag_TensorE(4) TensorDiag_Diag TensorDiag_assoc
                    TensorDiag_preserves_Diag(1))
      qed
      thus ?thesis using assms by blast
    qed

    lemma Inv_TensorDiag:
    assumes "Can t" and "Can u" and "Diag t" and "Diag u"
    shows "Inv (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Inv t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv u"
    proof -
      have "\<And>u. \<lbrakk> Can t \<and> Diag t; Can u \<and> Diag u \<rbrakk> \<Longrightarrow> Inv (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = Inv t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv u"
      proof (induct t, simp_all)
        fix f u
        assume f: "C.ide f \<and> C.arr f"
        assume u: "Can u \<and> Diag u"
        show "Inv (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv u"
          using f u by (cases u, simp_all)
        next
        fix t u v
        assume I1: "\<And>v. \<lbrakk> Diag t; Can v \<and> Diag v \<rbrakk> \<Longrightarrow> Inv (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v) = Inv t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv v"
        assume I2: "\<And>v. \<lbrakk> Diag u; Can v \<and> Diag v \<rbrakk> \<Longrightarrow> Inv (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v) = Inv u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv v"
        assume tu: "Can t \<and> Can u \<and> Diag (t \<^bold>\<otimes> u)"
        have t: "Can t \<and> Diag t"
          using tu Diag_TensorE [of t u] by force
        have u: "Can u \<and> Diag u"
          using t tu by (cases t, simp_all)
        assume v: "Can v \<and> Diag v"
        show "Inv ((t \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v) = (Inv t \<^bold>\<otimes> Inv u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv v"
        proof -
          have "v = Unity \<Longrightarrow> ?thesis" by simp
          moreover have "v \<noteq> Unity \<Longrightarrow> ?thesis"
          proof -
            assume 1: "v \<noteq> Unity"
            have "Inv ((t \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v) = Inv (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v))"
              using 1 by (cases v, simp_all)
            also have "... = Inv t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv (u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> v)"
              using t u v I1 TensorDiag_preserves_Diag TensorDiag_preserves_Can
                    Inv_preserves_Diag Inv_preserves_Can
              by simp
            also have "... = Inv t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (Inv u \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv v)"
              using t u v I2 TensorDiag_preserves_Diag TensorDiag_preserves_Can
                    Inv_preserves_Diag Inv_preserves_Can
              by simp
            also have "... = (Inv t \<^bold>\<otimes> Inv u) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv v"
              using v 1 by (cases v, simp_all)
            finally show ?thesis by blast
          qed
          ultimately show ?thesis by blast
        qed
      qed
      thus ?thesis using assms by blast
    qed

    text\<open>
      The following function defines composition for compatible diagonal terms,
      by ``pushing the composition down'' to arrows of \<open>C\<close>.
\<close>

    fun CompDiag :: "'a term \<Rightarrow> 'a term \<Rightarrow> 'a term"      (infixr "\<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor>" 55)
    where "\<^bold>\<I> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u = u"
        | "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<langle>g\<^bold>\<rangle> = \<^bold>\<langle>f \<cdot> g\<^bold>\<rangle>"
        | "(u \<^bold>\<otimes> v) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (w \<^bold>\<otimes> x) = (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w \<^bold>\<otimes> v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x)"
        | "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<I> = t"
        | "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> _ = undefined \<^bold>\<cdot> undefined"

    text\<open>
      Note that the last clause above is not relevant to diagonal terms.
      We have chosen a provably non-diagonal value in order to validate associativity.
\<close>

    lemma CompDiag_preserves_Diag:
    assumes "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "Diag (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)"
    and "Dom (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u"
    and "Cod (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod t"
    proof -
      have 0: "\<And>u. \<lbrakk> Diag t; Diag u; Dom t = Cod u \<rbrakk> \<Longrightarrow>
                     Diag (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<and> Dom (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u \<and> Cod (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod t"
      proof (induct t, simp_all add: Diag_TensorE)
        fix f u
        assume f: "C.arr f"
        assume u: "Diag u"
        assume 1: "\<^bold>\<langle>C.dom f\<^bold>\<rangle> = Cod u"
        show "Diag (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<and> Dom (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u \<and> Cod (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = \<^bold>\<langle>C.cod f\<^bold>\<rangle>"
          using f u 1 by (cases u, simp_all)
        next
        fix u v w
        assume I2: "\<And>u. \<lbrakk> Diag u; Dom w = Cod u \<rbrakk> \<Longrightarrow>
                          Diag (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<and> Dom (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u \<and> Cod (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod w"
        assume vw: "Diag (v \<^bold>\<otimes> w)"
        have v: "Diag v"
          using vw Diag_TensorE [of v w] by force
        have w: "Diag w"
          using vw Diag_TensorE [of v w] by force
        assume u: "Diag u"
        assume 1: "(Dom v \<^bold>\<otimes> Dom w) = Cod u"
        show "Diag ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<and> Dom ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u \<and>
                                     Cod ((v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod v \<^bold>\<otimes> Cod w"
          using u v w 1
        proof (cases u, simp_all)
          fix x y
          assume 2: "u = Tensor x y"
          have 4: "is_Prim x \<and> x = \<^bold>\<langle>un_Prim x\<^bold>\<rangle> \<and> C.arr (un_Prim x) \<and> Diag y \<and> y \<noteq> \<^bold>\<I>"
            using u 2 by (cases x, cases y, simp_all)
          have 5: "is_Prim v \<and> v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<and> C.arr (un_Prim v) \<and> Diag w \<and> w \<noteq> \<^bold>\<I>"
            using v w vw by (cases v, simp_all)
          have 6: "C.dom (un_Prim v) = C.cod (un_Prim x) \<and> Dom w = Cod y"
            using 1 2 4 5 apply (cases u, simp_all)
            by (metis Cod.simps(1) Dom.simps(1) term.simps(1))
          have "(v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u = \<^bold>\<langle>un_Prim v \<cdot> un_Prim x\<^bold>\<rangle> \<^bold>\<otimes> w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y"
            using 2 4 5 6 CompDiag.simps(2) [of "un_Prim v" "un_Prim x"] by simp
          moreover have "Diag (\<^bold>\<langle>un_Prim v \<cdot> un_Prim x\<^bold>\<rangle> \<^bold>\<otimes> w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y)"
          proof -
            have "Diag (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y)"
              using I2 4 5 6 by simp
            thus ?thesis
              using 4 5 6 Diag.simps(3) [of "un_Prim v \<cdot> un_Prim x" "(w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y)"]
              by (cases w; cases y) auto
          qed
          ultimately show "Diag (v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x \<^bold>\<otimes> w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y) \<and>
                           Dom (v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x) = Dom x \<and> Dom (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y) = Dom y \<and>
                           Cod (v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x) = Cod v \<and> Cod (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y) = Cod w"
            using 4 5 6 I2
            by (metis (full_types) C.cod_comp C.dom_comp Cod.simps(1) CompDiag.simps(2)
                Dom.simps(1) C.seqI)
        qed
      qed
      show "Diag (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)" using assms 0 by blast
      show "Dom (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u" using assms 0 by blast
      show "Cod (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod t" using assms 0 by blast
    qed

    lemma CompDiag_in_Hom:
    assumes "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u \<in> Hom (Dom u) (Cod t)"
      using assms CompDiag_preserves_Diag Diag_implies_Arr by simp

    lemma Dom_CompDiag:
    assumes "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "Dom (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u"
      using assms CompDiag_preserves_Diag(2) by simp

    lemma Cod_CompDiag:
    assumes "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "Cod (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod t"
      using assms CompDiag_preserves_Diag(3) by simp

    lemma CompDiag_Cod_Diag [simp]:
    assumes "Diag t"
    shows "Cod t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> t = t"
    proof -
      have "Diag t \<Longrightarrow> Cod t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> t = t"
        using C.comp_cod_arr
        apply (induct t, auto)
        by (auto simp add: Diag_TensorE)
      thus ?thesis using assms by blast
    qed

    lemma CompDiag_Diag_Dom [simp]:
    assumes "Diag t"
    shows "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Dom t = t"
    proof -
      have "Diag t \<Longrightarrow> t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Dom t = t"
        using C.comp_arr_dom
        apply (induct t, auto)
        by (auto simp add: Diag_TensorE)
      thus ?thesis using assms by blast
    qed

    lemma CompDiag_Ide_Diag [simp]:
    assumes "Diag t" and "Ide a" and "Dom a = Cod t"
    shows "a \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> t = t"
      using assms Ide_in_Hom by simp

    lemma CompDiag_Diag_Ide [simp]:
    assumes "Diag t" and "Ide a" and "Dom t = Cod a"
    shows "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> a = t"
      using assms Ide_in_Hom by auto

    lemma CompDiag_assoc:
    assumes "Diag t" and "Diag u" and "Diag v"
    and "Dom t = Cod u" and "Dom u = Cod v"
    shows "(t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
    proof -
      have "\<And>u v. \<lbrakk> Diag t; Diag u; Diag v; Dom t = Cod u; Dom u = Cod v \<rbrakk> \<Longrightarrow>
                    (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
      proof (induct t, simp_all)
        fix f u v
        assume f: "C.arr f"
        assume u: "Diag u"
        assume v: "Diag v"
        assume 1: "\<^bold>\<langle>C.dom f\<^bold>\<rangle> = Cod u"
        assume 2: "Dom u = Cod v"
        show "(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
          using C.comp_assoc by (cases u, simp_all; cases v, simp_all)
        next
        fix u v w x
        assume I1: "\<And>u v. \<lbrakk> Diag w; Diag u; Diag v; Dom w = Cod u; Dom u = Cod v \<rbrakk> \<Longrightarrow>
                            (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        assume I2: "\<And>u v. \<lbrakk> Diag x; Diag u; Diag v; Dom x = Cod u; Dom u = Cod v \<rbrakk> \<Longrightarrow>
                            (x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        assume wx: "Diag (w \<^bold>\<otimes> x)"
        assume u: "Diag u"
        assume v: "Diag v"
        assume 1: "(Dom w \<^bold>\<otimes> Dom x) = Cod u"
        assume 2: "Dom u = Cod v"
        show "((w \<^bold>\<otimes> x) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = (w \<^bold>\<otimes> x) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v"
        proof -
          have w: "Diag w"
            using wx Diag_TensorE by blast
          have x: "Diag x"
            using wx Diag_TensorE by blast
          have "is_Tensor u"
            using u 1 by (cases u) simp_all
          thus ?thesis
            using u v apply (cases u, simp_all, cases v, simp_all)
          proof -
            fix u1 u2 v1 v2
            assume 3: "u = (u1 \<^bold>\<otimes> u2)"
            assume 4: "v = (v1 \<^bold>\<otimes> v2)"
            show "(w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u1) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1 = w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1 \<and>
                  (x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u2) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2 = x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2"
            proof -
              have "Diag u1 \<and> Diag u2"
                using u 3 Diag_TensorE by blast
              moreover have "Diag v1 \<and> Diag v2"
                using v 4 Diag_TensorE by blast
              ultimately show ?thesis using w x I1 I2 1 2 3 4 by simp
            qed
          qed
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma CompDiag_preserves_Ide:
    assumes "Ide t" and "Ide u" and "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "Ide (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)"
    proof -
      have "\<And>u. \<lbrakk> Ide t; Ide u; Diag t; Diag u; Dom t = Cod u \<rbrakk> \<Longrightarrow> Ide (CompDiag t u)"
        by (induct t; simp)
      thus ?thesis using assms by blast
    qed

    lemma CompDiag_preserves_Can:
    assumes "Can t" and "Can u" and "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "Can (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)"
    proof -
      have "\<And>u. \<lbrakk> Can t \<and> Diag t; Can u \<and> Diag u; Dom t = Cod u \<rbrakk> \<Longrightarrow> Can (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)"
      proof (induct t, simp_all)
        fix t u v
        assume I1: "\<And>v. \<lbrakk> Diag t; Can v \<and> Diag v; Dom t = Cod v \<rbrakk> \<Longrightarrow> Can (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        assume I2: "\<And>v. \<lbrakk> Diag u; Can v \<and> Diag v; Dom u = Cod v \<rbrakk> \<Longrightarrow> Can (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        assume tu: "Can t \<and> Can u \<and> Diag (t \<^bold>\<otimes> u)"
        have t: "Can t \<and> Diag t"
          using tu Diag_TensorE by blast
        have u: "Can u \<and> Diag u"
          using tu Diag_TensorE by blast
        assume v: "Can v \<and> Diag v"
        assume 1: "(Dom t \<^bold>\<otimes> Dom u) = Cod v"
        show "Can ((t \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        proof -
          have 2: "(Dom t \<^bold>\<otimes> Dom u) = Cod v" using 1 by simp
          show ?thesis
            using v 2
          proof (cases v; simp)
            fix w x
            assume wx: "v = (w \<^bold>\<otimes> x)"
            have "Can w \<and> Diag w" using v wx Diag_TensorE [of w x] by auto
            moreover have "Can x \<and> Diag x" using v wx Diag_TensorE [of w x] by auto
            moreover have "Dom t = Cod w" using 2 wx by simp
            moreover have ux: "Dom u = Cod x" using 2 wx by simp
            ultimately show "Can (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w) \<and> Can (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x)"
              using t u I1 I2 by simp
          qed
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma Inv_CompDiag:
    assumes "Can t" and "Can u" and "Diag t" and "Diag u" and "Dom t = Cod u"
    shows "Inv (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv t"
    proof -
      have "\<And>u. \<lbrakk> Can t \<and> Diag t; Can u \<and> Diag u; Dom t = Cod u \<rbrakk> \<Longrightarrow>
              Inv (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv t"
      proof (induct t, simp_all)
        show "\<And>x u. \<lbrakk> C.ide x \<and> C.arr x; Can u \<and> Diag u; \<^bold>\<langle>x\<^bold>\<rangle> = Cod u \<rbrakk> \<Longrightarrow>
                      Inv u = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv (Cod u)"
          by (metis CompDiag_Diag_Dom Inv_Ide Inv_preserves_Can(2) Inv_preserves_Diag
                    Ide.simps(1))
        show "\<And>u. Can u \<and> Diag u \<Longrightarrow> \<^bold>\<I> = Cod u \<Longrightarrow> Inv u = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<I>"
          by (simp add: Inv_preserves_Can(2) Inv_preserves_Diag)
        fix t u v
        assume tu: "Can t \<and> Can u \<and> Diag (t \<^bold>\<otimes> u)"
        have t: "Can t \<and> Diag t"
          using tu Diag_TensorE by blast
        have u: "Can u \<and> Diag u"
          using tu Diag_TensorE by blast
        assume I1: "\<And>v. \<lbrakk> Diag t; Can v \<and> Diag v; Dom t = Cod v \<rbrakk> \<Longrightarrow>
                          Inv (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) = Inv v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv t"
        assume I2: "\<And>v. \<lbrakk> Diag u; Can v \<and> Diag v; Dom u = Cod v \<rbrakk> \<Longrightarrow>
                          Inv (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) = Inv v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv u"
        assume v: "Can v \<and> Diag v"
        assume 1: "(Dom t \<^bold>\<otimes> Dom u) = Cod v"
        show "Inv ((t \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) = Inv v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (Inv t \<^bold>\<otimes> Inv u)"
          using v 1
        proof (cases v, simp_all)
          fix w x
          assume wx: "v = (w \<^bold>\<otimes> x)"
          have "Can w \<and> Diag w" using v wx Diag_TensorE [of w x] by auto
          moreover have "Can x \<and> Diag x" using v wx Diag_TensorE [of w x] by auto
          moreover have "Dom t = Cod w" using wx 1 by simp
          moreover have "Dom u = Cod x" using wx 1 by simp
          ultimately show "Inv (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w) = Inv w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv t \<and>
                           Inv (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x) = Inv x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv u"
            using t u I1 I2 by simp
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma Can_and_Diag_implies_Ide:
    assumes "Can t" and "Diag t"
    shows "Ide t"
    proof -
      have "\<lbrakk> Can t; Diag t \<rbrakk> \<Longrightarrow> Ide t"
        apply (induct t, simp_all)
        by (simp add: Diag_TensorE)
      thus ?thesis using assms by blast
    qed

    lemma CompDiag_Can_Inv [simp]:
    assumes "Can t" and "Diag t"
    shows "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv t = Cod t"
      using assms Can_and_Diag_implies_Ide Ide_in_Hom by simp
      
    lemma CompDiag_Inv_Can [simp]:
    assumes "Can t" and "Diag t"
    shows "Inv t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> t = Dom t"
      using assms Can_and_Diag_implies_Ide Ide_in_Hom by simp

    text\<open>
      The next fact is a syntactic version of the interchange law, for diagonal terms.
\<close>

    lemma CompDiag_TensorDiag:
    assumes "Diag t" and "Diag u" and "Diag v" and "Diag w"
    and "Seq t v" and "Seq u w"
    shows "(t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
    proof -
      have "\<And>u v w. \<lbrakk> Diag t; Diag u; Diag v; Diag w; Seq t v; Seq u w \<rbrakk> \<Longrightarrow>
                      (t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
      proof (induct t, simp_all)
        fix u v w
        assume u: "Diag u"
        assume v: "Diag v"
        assume w: "Diag w"
        assume uw: "Seq u w"
        show "Arr v \<and> \<^bold>\<I> = Cod v \<Longrightarrow> u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
          using u v w uw by (cases v) simp_all
        show "\<And>f. \<lbrakk> C.arr f; Arr v \<and> \<^bold>\<langle>C.dom f\<^bold>\<rangle> = Cod v \<rbrakk> \<Longrightarrow>
                    (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
        proof -
          fix f
          assume f: "C.arr f"
          assume 1: "Arr v \<and> \<^bold>\<langle>C.dom f\<^bold>\<rangle> = Cod v"
          show "(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
          proof -
            have 2: "v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<and> C.arr (un_Prim v)" using v 1 by (cases v) simp_all
            have "u = \<^bold>\<I> \<Longrightarrow> ?thesis"
              using v w uw 1 2 Cod.simps(3) CompDiag_Cod_Diag Dom.simps(2)
                    TensorDiag_Prim TensorDiag_term_Unity TensorDiag_preserves_Diag(3)
              by (cases w) simp_all
            moreover have "u \<noteq> \<^bold>\<I> \<Longrightarrow> ?thesis"
            proof -
              assume 3: "u \<noteq> \<^bold>\<I>"
              hence 4: "w \<noteq> \<^bold>\<I>" using u w uw by (cases u, simp_all; cases w, simp_all)
              have "(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<otimes> w)"
              proof -
                have "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> u"
                  using u f 3 TensorDiag_Diag by (cases u) simp_all
                moreover have "v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w = v \<^bold>\<otimes> w"
                  using w 2 4 TensorDiag_Diag by (cases v, simp_all; cases w, simp_all)
                ultimately show ?thesis by simp
              qed
              also have 5: "... = (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<otimes> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)" by simp
              also have "... = (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
                using f u w uw 1 2 3 4 5
                      TensorDiag_Diag TensorDiag_Prim TensorDiag_preserves_Diag(1)
                      CompDiag_preserves_Diag(1)
                by (metis Cod.simps(3) Dom.simps(1) Dom.simps(3) Diag.simps(2))
              finally show ?thesis by blast
            qed
            ultimately show ?thesis by blast
          qed
        qed
        fix t1 t2
        assume I2: "\<And>u v w. \<lbrakk> Diag t2; Diag u; Diag v; Diag w;
                              Arr v \<and> Dom t2 = Cod v; Seq u w \<rbrakk> \<Longrightarrow>
                              (t2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
        assume t12: "Diag (t1 \<^bold>\<otimes> t2)"
        have t1: "t1 = \<^bold>\<langle>un_Prim t1\<^bold>\<rangle> \<and> C.arr (un_Prim t1) \<and> Diag t1"
          using t12 by (cases t1) simp_all
        have t2: "Diag t2 \<and> t2 \<noteq> \<^bold>\<I>"
          using t12 by (cases t1) simp_all
        assume 1: "Arr t1 \<and> Arr t2 \<and> Arr v \<and> Dom t1 \<^bold>\<otimes> Dom t2 = Cod v"
        show "((t1 \<^bold>\<otimes> t2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) = ((t1 \<^bold>\<otimes> t2) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
        proof -
          have "u = \<^bold>\<I> \<Longrightarrow> ?thesis"
            using w uw TensorDiag_term_Unity CompDiag_Cod_Diag by (cases w) simp_all
          moreover have "u \<noteq> \<^bold>\<I> \<Longrightarrow> ?thesis"
          proof -
            assume u': "u \<noteq> \<^bold>\<I>"
            hence w': "w \<noteq> \<^bold>\<I>" using u w uw by (cases u; simp; cases w; simp)
            show ?thesis
              using 1 v
            proof (cases v, simp_all)
              fix v1 v2
              assume v12: "v = Tensor v1 v2"
              have v1: "v1 = \<^bold>\<langle>un_Prim v1\<^bold>\<rangle> \<and> C.arr (un_Prim v1) \<and> Diag v1"
                using v v12 by (cases v1) simp_all
              have v2: "Diag v2 \<and> v2 \<noteq> \<^bold>\<I>"
                using v v12 by (cases v1) simp_all
              have 2: "v = (\<^bold>\<langle>un_Prim v1\<^bold>\<rangle> \<^bold>\<otimes> v2)"
                using v1 v12 by simp
              show "((t1 \<^bold>\<otimes> t2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> ((v1 \<^bold>\<otimes> v2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w)
                      = ((t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<otimes> (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2)) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
              proof -
                have 3: "(t1 \<^bold>\<otimes> t2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u = t1 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (t2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
                  using u u' by (cases u) simp_all
                have 4: "v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w = v1 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (v2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w)"
                  using v w v1 v2 2 TensorDiag_assoc TensorDiag_Diag by metis
                have "((t1 \<^bold>\<otimes> t2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> ((v1 \<^bold>\<otimes> v2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w)
                        = (t1 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (t2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v1 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (v2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w))"
                  using 3 4 v12 by simp
                also have "... = (t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> ((t2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w))"
                proof -
                  have "is_Tensor (t2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u)"
                    using t2 u u' not_is_Tensor_TensorDiagE by auto
                  moreover have "is_Tensor (v2 \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w)"
                    using v2 v12 w w' not_is_Tensor_TensorDiagE by auto
                  ultimately show ?thesis
                    using u u' v w t1 v1 t12 v12 TensorDiag_Prim not_is_Tensor_Unity
                    by (metis (no_types, lifting) CompDiag.simps(2) CompDiag.simps(3)
                        is_Tensor_def)
                qed
                also have "... = (t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
                  using u w uw t2 v2 1 2 Diag_implies_Arr I2 by fastforce
                also have "... = ((t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<otimes> (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2)) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
                proof -
                  have "u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w \<noteq> Unity"
                  proof -
                    have "Arr v1 \<and> \<^bold>\<langle>C.dom (un_Prim t1)\<^bold>\<rangle> = Cod v1"
                      using t1 v1 1 2 by (cases t1, auto)
                    thus ?thesis
                      using t1 t2 v1 v2 u w uw u' CompDiag_preserves_Diag
                            TensorDiag_preserves_Diag TensorDiag_Prim
                      by (metis (mono_tags, lifting) Cod.simps(2) Cod.simps(3)
                          TensorDiag.simps(2) term.distinct(3))
                  qed
                  hence "((t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<otimes> (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2)) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)
                           = (t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> ((t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w))"
                    by (cases "u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w") simp_all
                  thus ?thesis by argo
                qed
                finally show ?thesis by blast
              qed
            qed
          qed
          ultimately show ?thesis by blast
        qed
      qed
      thus ?thesis using assms by blast
    qed

    text\<open>
      The following function reduces an arrow to diagonal form.
      The precise relationship between a term and its diagonalization is developed below.
\<close>

    fun Diagonalize :: "'a term \<Rightarrow> 'a term"   ("\<^bold>\<lfloor>_\<^bold>\<rfloor>")
    where "\<^bold>\<lfloor>\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>\<rfloor> = \<^bold>\<langle>f\<^bold>\<rangle>"
        | "\<^bold>\<lfloor>\<^bold>\<I>\<^bold>\<rfloor> = \<^bold>\<I>"
        | "\<^bold>\<lfloor>t \<^bold>\<otimes> u\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>t \<^bold>\<cdot> u\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<l>\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<r>\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = (\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>)"

    lemma Diag_Diagonalize:
    assumes "Arr t"
    shows "Diag \<^bold>\<lfloor>t\<^bold>\<rfloor>" and "Dom \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor>" and "Cod \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>"
    proof -
      have 0: "Arr t \<Longrightarrow> Diag \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> Dom \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<and> Cod \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>"
        using TensorDiag_preserves_Diag CompDiag_preserves_Diag TensorDiag_assoc
        apply (induct t)
                 apply auto
         apply (metis (full_types))
        by (metis (full_types))
      show "Diag \<^bold>\<lfloor>t\<^bold>\<rfloor>" using assms 0 by blast
      show "Dom \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor>" using assms 0 by blast
      show "Cod \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>" using assms 0 by blast
    qed

    lemma Diagonalize_in_Hom:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>t\<^bold>\<rfloor> \<in> Hom \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>"
      using assms Diag_Diagonalize Diag_implies_Arr by blast

    lemma Diagonalize_Dom:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> = Dom \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms Diagonalize_in_Hom by simp

    lemma Diagonalize_Cod:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> = Cod \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms Diagonalize_in_Hom by simp

    lemma Diagonalize_preserves_Ide:
    assumes "Ide a"
    shows "Ide \<^bold>\<lfloor>a\<^bold>\<rfloor>"
    proof -
      have "Ide a \<Longrightarrow> Ide \<^bold>\<lfloor>a\<^bold>\<rfloor>"
        using Ide_implies_Arr TensorDiag_preserves_Ide Diag_Diagonalize
        by (induct a) simp_all
      thus ?thesis using assms by blast
    qed

    text\<open>
      The diagonalizations of canonical arrows are identities.
\<close>

    lemma Ide_Diagonalize_Can:
    assumes "Can t"
    shows "Ide \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      have "Can t \<Longrightarrow> Ide \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        using Can_implies_Arr TensorDiag_preserves_Ide Diag_Diagonalize CompDiag_preserves_Ide
              TensorDiag_preserves_Diag
        by (induct t) auto
      thus ?thesis using assms by blast
    qed

    lemma Diagonalize_preserves_Can:
    assumes "Can t"
    shows "Can \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms Ide_Diagonalize_Can Ide_implies_Can by auto

    lemma Diagonalize_Diag [simp]:
    assumes "Diag t"
    shows "\<^bold>\<lfloor>t\<^bold>\<rfloor> = t"
    proof -
      have "Diag t \<Longrightarrow> \<^bold>\<lfloor>t\<^bold>\<rfloor> = t"
        apply (induct t, simp_all)
        using TensorDiag_Prim Diag_TensorE by metis
      thus ?thesis using assms by blast
    qed

    lemma Diagonalize_Diagonalize [simp]:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms Diag_Diagonalize Diagonalize_Diag by blast

    lemma Diagonalize_Tensor:
    assumes "Arr t" and "Arr u"
    shows "\<^bold>\<lfloor>t \<^bold>\<otimes> u\<^bold>\<rfloor> = \<^bold>\<lfloor>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<otimes> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<^bold>\<rfloor>"
      using assms Diagonalize_Diagonalize by simp

    lemma Diagonalize_Tensor_Unity_Arr [simp]:
    assumes "Arr u"
    shows "\<^bold>\<lfloor>\<^bold>\<I> \<^bold>\<otimes> u\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
      using assms by simp

    lemma Diagonalize_Tensor_Arr_Unity [simp]:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>t \<^bold>\<otimes> \<^bold>\<I>\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms by simp

    lemma Diagonalize_Tensor_Prim_Arr [simp]:
    assumes "arr f" and "Arr u" and "\<^bold>\<lfloor>u\<^bold>\<rfloor> \<noteq> Unity"
    shows "\<^bold>\<lfloor>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> u\<^bold>\<rfloor> = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> \<^bold>\<lfloor>u\<^bold>\<rfloor>"
      using assms by simp

    lemma Diagonalize_Tensor_Tensor:
    assumes "Arr t" and "Arr u" and "Arr v"
    shows "\<^bold>\<lfloor>(t \<^bold>\<otimes> u) \<^bold>\<otimes> v\<^bold>\<rfloor> = \<^bold>\<lfloor>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<otimes> (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<otimes> \<^bold>\<lfloor>v\<^bold>\<rfloor>)\<^bold>\<rfloor>"
      using assms Diag_Diagonalize Diagonalize_Diagonalize by (simp add: TensorDiag_assoc)

    lemma Diagonalize_Comp_Cod_Arr:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>Cod t \<^bold>\<cdot> t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      have "Arr t \<Longrightarrow> \<^bold>\<lfloor>Cod t \<^bold>\<cdot> t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        using C.comp_cod_arr
        apply (induct t, simp_all)
        using CompDiag_TensorDiag Arr_implies_Ide_Cod Ide_in_Hom Diag_Diagonalize
              Diagonalize_in_Hom
           apply simp
        using CompDiag_preserves_Diag CompDiag_Cod_Diag Diag_Diagonalize
          apply metis
        using CompDiag_TensorDiag Arr_implies_Ide_Cod Ide_in_Hom TensorDiag_in_Hom
              TensorDiag_preserves_Diag Diag_Diagonalize Diagonalize_in_Hom TensorDiag_assoc
        by simp_all
      thus ?thesis using assms by blast
    qed

    lemma Diagonalize_Comp_Arr_Dom:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>t \<^bold>\<cdot> Dom t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      have "Arr t \<Longrightarrow> \<^bold>\<lfloor>t \<^bold>\<cdot> Dom t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        using C.comp_arr_dom
        apply (induct t, simp_all)
        using CompDiag_TensorDiag Arr_implies_Ide_Dom Ide_in_Hom Diag_Diagonalize
              Diagonalize_in_Hom
           apply simp
        using CompDiag_preserves_Diag CompDiag_Diag_Dom Diag_Diagonalize
          apply metis
        using CompDiag_TensorDiag Arr_implies_Ide_Dom Ide_in_Hom TensorDiag_in_Hom
              TensorDiag_preserves_Diag Diag_Diagonalize Diagonalize_in_Hom TensorDiag_assoc
        by simp_all
      thus ?thesis using assms by blast
    qed

    lemma Diagonalize_Inv:
    assumes "Can t"
    shows "\<^bold>\<lfloor>Inv t\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      have "Can t \<Longrightarrow> \<^bold>\<lfloor>Inv t\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      proof (induct t, simp_all)
        fix u v
        assume I1: "\<^bold>\<lfloor>Inv u\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>u\<^bold>\<rfloor>"
        assume I2: "\<^bold>\<lfloor>Inv v\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>v\<^bold>\<rfloor>"
        show "Can u \<and> Can v \<Longrightarrow> Inv \<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>v\<^bold>\<rfloor> = Inv (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>)"
          using Inv_TensorDiag Diag_Diagonalize Can_implies_Arr Diagonalize_preserves_Can
                I1 I2
          by simp
        show "Can u \<and> Can v \<and> Dom u = Cod v \<Longrightarrow> Inv \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>u\<^bold>\<rfloor> = Inv (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>)"
          using Inv_CompDiag Diag_Diagonalize Can_implies_Arr Diagonalize_in_Hom
                Diagonalize_preserves_Can I1 I2
          by simp
        fix w
        assume I3: "\<^bold>\<lfloor>Inv w\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>w\<^bold>\<rfloor>"
        assume uvw: "Can u \<and> Can v \<and> Can w"
        show "Inv \<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (Inv \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>w\<^bold>\<rfloor>) = Inv ((\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>)"
          using uvw I1 I2 I3
                Inv_TensorDiag Diag_Diagonalize Can_implies_Arr Diagonalize_preserves_Can
                TensorDiag_preserves_Diag TensorDiag_preserves_Can TensorDiag_assoc
          by simp
        show "(Inv \<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>v\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>w\<^bold>\<rfloor> = Inv (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>))"
          using uvw I1 I2 I3
                Inv_TensorDiag Diag_Diagonalize Can_implies_Arr Diagonalize_preserves_Can
                TensorDiag_preserves_Diag TensorDiag_preserves_Can
          apply simp
          using TensorDiag_assoc [of "\<^bold>\<lfloor>u\<^bold>\<rfloor>" "\<^bold>\<lfloor>v\<^bold>\<rfloor>" "\<^bold>\<lfloor>w\<^bold>\<rfloor>"] by metis
      qed
      thus ?thesis using assms by blast
    qed

    text\<open>
      Our next objective is to begin making the connection, to be completed in a
      subsequent section, between arrows and their diagonalizations.
      To summarize, an arrow @{term t} and its diagonalization @{term "\<^bold>\<lfloor>t\<^bold>\<rfloor>"} are opposite sides
      of a square whose other sides are certain canonical terms
      \<open>Dom t\<^bold>\<down> \<in> Hom (Dom t) \<^bold>\<lfloor>Dom t\<^bold>\<rfloor>\<close> and \<open>Cod t\<^bold>\<down> \<in> Hom (Cod t) \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>\<close>,
      where \<open>Dom t\<^bold>\<down>\<close> and \<open>Cod t\<^bold>\<down>\<close> are defined by the function \<open>red\<close>
      below.  The coherence theorem amounts to the statement that every such square commutes
      when the formal terms involved are evaluated in the evident way in any monoidal category.

      Function \<open>red\<close> defined below takes an identity term @{term a} to a canonical arrow
      \<open>a\<^bold>\<down> \<in> Hom a \<^bold>\<lfloor>a\<^bold>\<rfloor>\<close>.  The auxiliary function \<open>red2\<close> takes a pair @{term "(a, b)"}
      of diagonal identity terms and produces a canonical arrow
      \<open>a \<^bold>\<Down> b \<in> Hom (a \<^bold>\<otimes> b) \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor>\<close>.
      The canonical arrow \<open>a\<^bold>\<down>\<close> amounts to a ``parallel innermost reduction''
      from @{term a} to @{term "\<^bold>\<lfloor>a\<^bold>\<rfloor>"}, where the reduction steps are canonical arrows
      that involve the unitors and associator only in their uninverted forms.
      In general, a parallel innermost reduction from @{term a} will not be unique:
      at some points there is a choice available between left and right unitors
      and at other points there are choices between unitors and associators.
      These choices are inessential, and the ordering of the clauses in the function definitions
      below resolves them in an arbitrary way.  What is more important is having chosen an
      innermost reduction, which is what allows us to write these definitions in structurally
      recursive form.

      The essence of coherence is that the axioms for a monoidal category allow us to
      prove that any reduction from @{term a} to @{term "\<^bold>\<lfloor>a\<^bold>\<rfloor>"} is equivalent
      (under evaluation of terms) to a parallel innermost reduction.
      The problematic cases are terms of the form @{term "((a \<^bold>\<otimes> b) \<^bold>\<otimes> c) \<^bold>\<otimes> d"},
      which present a choice between an inner and outer reduction that lead to terms
      with different structures.  It is of course the pentagon axiom that ensures the
      confluence (under evaluation) of the two resulting paths.

      Although simple in appearance, the structurally recursive definitions below were
      difficult to get right even after I started to understand what I was doing.
      I wish I could have just written them down straightaway.  If so, then I could have
      avoided laboriously constructing and then throwing away thousands of lines of proof
      text that used a non-structural, ``operational'' approach to defining a reduction
      from @{term a} to @{term "\<^bold>\<lfloor>a\<^bold>\<rfloor>"}.
\<close>

    fun red2                       (infixr "\<^bold>\<Down>" 53)
    where "\<^bold>\<I> \<^bold>\<Down> a = \<^bold>\<l>\<^bold>[a\<^bold>]"
        | "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> \<^bold>\<I> = \<^bold>\<r>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>]"
        | "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> a = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> a"
        | "(a \<^bold>\<otimes> b) \<^bold>\<Down> \<^bold>\<I> = \<^bold>\<r>\<^bold>[a \<^bold>\<otimes> b\<^bold>]"
        | "(a \<^bold>\<otimes> b) \<^bold>\<Down> c = (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) \<^bold>\<cdot> (a \<^bold>\<otimes> (b \<^bold>\<Down> c)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[a, b, c\<^bold>]"
        | "a \<^bold>\<Down> b = undefined"

    fun red                         ("_\<^bold>\<down>" [56] 56)
    where "\<^bold>\<I>\<^bold>\<down> = \<^bold>\<I>"
        | "\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>\<down> = \<^bold>\<langle>f\<^bold>\<rangle>"
        | "(a \<^bold>\<otimes> b)\<^bold>\<down> = (if Diag (a \<^bold>\<otimes> b) then a \<^bold>\<otimes> b else (\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>) \<^bold>\<cdot> (a\<^bold>\<down> \<^bold>\<otimes> b\<^bold>\<down>))"
        | "a\<^bold>\<down> = undefined"

    lemma red_Diag [simp]:
    assumes "Diag a"
    shows "a\<^bold>\<down> = a"
      using assms by (cases a) simp_all

    lemma red2_Diag:
    assumes "Diag (a \<^bold>\<otimes> b)"
    shows "a \<^bold>\<Down> b = a \<^bold>\<otimes> b"
    proof -
      have a: "a = \<^bold>\<langle>un_Prim a\<^bold>\<rangle>"
        using assms Diag_TensorE by metis
      have b: "Diag b \<and> b \<noteq> \<^bold>\<I>"
        using assms Diag_TensorE by metis
      show ?thesis using a b
        apply (cases b)
          apply simp_all
         apply (metis red2.simps(3))
        by (metis red2.simps(4))
    qed

    lemma Can_red2:
    assumes "Ide a" and "Diag a" and "Ide b" and "Diag b"
    shows "Can (a \<^bold>\<Down> b)"
    and "a \<^bold>\<Down> b \<in> Hom (a \<^bold>\<otimes> b) \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor>"
    proof -
      have 0: "\<And>b. \<lbrakk> Ide a \<and> Diag a; Ide b \<and> Diag b \<rbrakk> \<Longrightarrow>
                     Can (a \<^bold>\<Down> b) \<and> a \<^bold>\<Down> b \<in> Hom (a \<^bold>\<otimes> b) \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor>"
      proof (induct a, simp_all)
        fix b
        show "Ide b \<and> Diag b \<Longrightarrow> Can b \<and> Dom b = b \<and> Cod b = b"
          using Ide_implies_Can Ide_in_Hom Diagonalize_Diag by auto
        fix f
        show "\<lbrakk> C.ide f \<and> C.arr f; Ide b \<and> Diag b \<rbrakk> \<Longrightarrow>
                Can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b) \<and> Arr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b) \<and> Dom (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b) = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> b \<and>
                                                Cod (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b) = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b"
          using Ide_implies_Can Ide_in_Hom by (cases b; auto)
        next
        fix a b c
        assume ab: "Ide a \<and> Ide b \<and> Diag (Tensor a b)"
        assume c: "Ide c \<and> Diag c"
        assume I1: "\<And>c. \<lbrakk> Diag a; Ide c \<and> Diag c \<rbrakk> \<Longrightarrow>
                          Can (a \<^bold>\<Down> c) \<and> Arr (a \<^bold>\<Down> c) \<and> Dom (a \<^bold>\<Down> c) = a \<^bold>\<otimes> c \<and>
                                                       Cod (a \<^bold>\<Down> c) = a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c"
        assume I2: "\<And>c. \<lbrakk> Diag b; Ide c \<and> Diag c \<rbrakk> \<Longrightarrow>
                          Can (b \<^bold>\<Down> c) \<and> Arr (b \<^bold>\<Down> c) \<and> Dom (b \<^bold>\<Down> c) = b \<^bold>\<otimes> c \<and>
                                                       Cod (b \<^bold>\<Down> c) = b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c"
        show "Can ((a \<^bold>\<otimes> b) \<^bold>\<Down> c) \<and> Arr ((a \<^bold>\<otimes> b) \<^bold>\<Down> c) \<and>
              Dom ((a \<^bold>\<otimes> b) \<^bold>\<Down> c) = (a \<^bold>\<otimes> b) \<^bold>\<otimes> c \<and>
              Cod ((a \<^bold>\<otimes> b) \<^bold>\<Down> c) = (\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>b\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c"
        proof -
          have a: "Diag a \<and> Ide a"
            using ab Diag_TensorE by blast
          have b: "Diag b \<and> Ide b"
            using ab Diag_TensorE by blast
          have "c = \<^bold>\<I> \<Longrightarrow> ?thesis"
          proof -
            assume 1: "c = \<^bold>\<I>"
            have 2: "(a \<^bold>\<otimes> b) \<^bold>\<Down> c = \<^bold>\<r>\<^bold>[a \<^bold>\<otimes> b\<^bold>]"
              using 1 by simp
            have 3: "Can (a \<^bold>\<Down> b) \<and> Arr (a \<^bold>\<Down> b) \<and> Dom (a \<^bold>\<Down> b) = a \<^bold>\<otimes> b \<and> Cod (a \<^bold>\<Down> b) = a \<^bold>\<otimes> b"
              using a b ab 1 2 I1 Diagonalize_Diag Diagonalize.simps(3) by metis
            hence 4: "Seq (a \<^bold>\<Down> b) \<^bold>\<r>\<^bold>[a \<^bold>\<otimes> b\<^bold>]"
              using ab
              by (metis (mono_tags, lifting) Arr.simps(7) Cod.simps(3) Cod.simps(7)
                  Diag_implies_Arr Ide_in_Hom mem_Collect_eq)
            have "Can ((a \<^bold>\<otimes> b) \<^bold>\<Down> c)"
              using 1 2 3 4 ab by (simp add: Ide_implies_Can)
            moreover have "Dom ((a \<^bold>\<otimes> b) \<^bold>\<Down> c) = (a \<^bold>\<otimes> b) \<^bold>\<otimes> c"
              using 1 2 3 4 a b ab I1 Ide_in_Hom TensorDiag_preserves_Diag by simp
            moreover have "Cod ((a \<^bold>\<otimes> b) \<^bold>\<Down> c) = \<^bold>\<lfloor>(a \<^bold>\<otimes> b) \<^bold>\<otimes> c\<^bold>\<rfloor>"
             using 1 2 3 4 ab using Diagonalize_Diag by fastforce
            ultimately show ?thesis using Can_implies_Arr by (simp add: 1 ab)
          qed
          moreover have "c \<noteq> \<^bold>\<I> \<Longrightarrow> ?thesis"
          proof -
            assume 1: "c \<noteq> \<^bold>\<I>"
            have 2: "(a \<^bold>\<otimes> b) \<^bold>\<Down> c = (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) \<^bold>\<cdot> (a \<^bold>\<otimes> b \<^bold>\<Down> c) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[a, b, c\<^bold>]"
              using 1 a b ab c by (cases c; simp)
            have 3: "Can (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) \<and> Dom (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) = a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor> \<and>
                                          Cod (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) = \<^bold>\<lfloor>a \<^bold>\<otimes> (b \<^bold>\<otimes> c)\<^bold>\<rfloor>"
            proof -
              have "Can (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) \<and> Dom (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) = a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor> \<and>
                                         Cod (a \<^bold>\<Down> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>) = \<^bold>\<lfloor>a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>\<^bold>\<rfloor>"
                using a c ab 1 2 I1 Diag_implies_Arr Diag_Diagonalize(1)
                      Diagonalize_preserves_Ide TensorDiag_preserves_Ide
                      TensorDiag_preserves_Diag(1)
                by auto
              moreover have "\<^bold>\<lfloor>a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>\<^bold>\<rfloor> = \<^bold>\<lfloor>a \<^bold>\<otimes> (b \<^bold>\<otimes> c)\<^bold>\<rfloor>"
                using ab c Diagonalize_Tensor Diagonalize_Diagonalize Diag_implies_Arr
                by (metis Arr.simps(3) Diagonalize.simps(3))
              ultimately show ?thesis by metis
            qed
            have 4: "Can (b \<^bold>\<Down> c) \<and> Dom (b \<^bold>\<Down> c) = b \<^bold>\<otimes> c \<and> Cod (b \<^bold>\<Down> c) = \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>"
              using b c ab 1 2 I2 by simp
            hence "Can (a \<^bold>\<otimes> (b \<^bold>\<Down> c)) \<and> Dom (a \<^bold>\<otimes> (b \<^bold>\<Down> c)) = a \<^bold>\<otimes> (b \<^bold>\<otimes> c) \<and>
                                        Cod (a \<^bold>\<otimes> (b \<^bold>\<Down> c)) = a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>"
              using ab Ide_implies_Can Ide_in_Hom by force
            moreover have "\<^bold>\<lfloor>a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>\<^bold>\<rfloor> = \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>"
            proof -
              have "\<^bold>\<lfloor>a \<^bold>\<otimes> \<^bold>\<lfloor>b \<^bold>\<otimes> c\<^bold>\<rfloor>\<^bold>\<rfloor> = a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)"
                using a b c 4
                by (metis Arr_implies_Ide_Dom Can_implies_Arr Ide_implies_Arr
                    Diag_Diagonalize(1) Diagonalize.simps(3) Diagonalize_Diag)
              also have "... = (a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c"
                using a b ab c TensorDiag_assoc by metis
              also have "... = \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>"
                using a b c by (metis Diagonalize.simps(3) Diagonalize_Diag)
              finally show ?thesis by blast
            qed
            moreover have "Can \<^bold>\<a>\<^bold>[a, b, c\<^bold>] \<and> Dom \<^bold>\<a>\<^bold>[a, b, c\<^bold>] = (a \<^bold>\<otimes> b) \<^bold>\<otimes> c \<and>
                                            Cod \<^bold>\<a>\<^bold>[a, b, c\<^bold>] = a \<^bold>\<otimes> (b \<^bold>\<otimes> c)"
              using ab c Ide_implies_Can Ide_in_Hom by auto
            ultimately show ?thesis
              using ab c 2 3 4 Diag_implies_Arr Diagonalize_Diagonalize Ide_implies_Can
                    Diagonalize_Diag Arr_implies_Ide_Dom Can_implies_Arr
              by (metis Can.simps(4) Cod.simps(4) Dom.simps(4) Diagonalize.simps(3))
          qed
          ultimately show ?thesis by blast
        qed
      qed
      show "Can (a \<^bold>\<Down> b)" using assms 0 by blast
      show "a \<^bold>\<Down> b \<in> Hom (a \<^bold>\<otimes> b) \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor>" using 0 assms by blast
    qed

    lemma red2_in_Hom:
    assumes "Ide a" and "Diag a" and "Ide b" and "Diag b"
    shows "a \<^bold>\<Down> b \<in> Hom (a \<^bold>\<otimes> b) \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor>"
      using assms Can_red2 Can_implies_Arr by simp

    lemma Can_red:
    assumes "Ide a"
    shows "Can (a\<^bold>\<down>)" and "a\<^bold>\<down> \<in> Hom a \<^bold>\<lfloor>a\<^bold>\<rfloor>"
    proof -
      have 0: "Ide a \<Longrightarrow> Can (a\<^bold>\<down>) \<and> a\<^bold>\<down> \<in> Hom a \<^bold>\<lfloor>a\<^bold>\<rfloor>"
      proof (induct a, simp_all)
        fix b c
        assume b: "Can (b\<^bold>\<down>) \<and> Arr (b\<^bold>\<down>) \<and> Dom (b\<^bold>\<down>) = b \<and> Cod (b\<^bold>\<down>) = \<^bold>\<lfloor>b\<^bold>\<rfloor>"
        assume c: "Can (c\<^bold>\<down>) \<and> Arr (c\<^bold>\<down>) \<and> Dom (c\<^bold>\<down>) = c \<and> Cod (c\<^bold>\<down>) = \<^bold>\<lfloor>c\<^bold>\<rfloor>"
        assume bc: "Ide b \<and> Ide c"
        show "(Diag (b \<^bold>\<otimes> c) \<longrightarrow>
                 Can b \<and> Can c \<and> Dom b = b \<and> Dom c = c \<and> Cod b \<^bold>\<otimes> Cod c = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>) \<and>
              (\<not> Diag (b \<^bold>\<otimes> c) \<longrightarrow>
                 Can (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) \<and> Dom (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<otimes> \<^bold>\<lfloor>c\<^bold>\<rfloor> \<and> Arr (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) \<and>
                 Dom (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<otimes> \<^bold>\<lfloor>c\<^bold>\<rfloor> \<and> Cod (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>)"
        proof
          show "Diag (b \<^bold>\<otimes> c) \<longrightarrow>
                  Can b \<and> Can c \<and> Dom b = b \<and> Dom c = c \<and> Cod b \<^bold>\<otimes> Cod c = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>"
            using bc Diag_TensorE Ide_implies_Can Inv_preserves_Can(2)
                  CompDiag_Ide_Diag Inv_Ide Diagonalize.simps(3) Diagonalize_Diag
            by (metis CompDiag_Inv_Can)
          show "\<not> Diag (b \<^bold>\<otimes> c) \<longrightarrow>
                  Can (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) \<and> Dom (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<otimes> \<^bold>\<lfloor>c\<^bold>\<rfloor> \<and> Arr (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) \<and>
                                    Dom (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<otimes> \<^bold>\<lfloor>c\<^bold>\<rfloor> \<and> Cod (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>) = \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>"
            using b c bc Ide_in_Hom Ide_implies_Can Diagonalize_Diag Can_red2 Diag_Diagonalize
                  Ide_implies_Arr Diagonalize_Tensor Diagonalize_preserves_Ide
                  TensorDiag_preserves_Diag TensorDiag_preserves_Ide
                  TensorDiag_preserves_Can
            by (cases b) simp_all
        qed
      qed
      show "Can (a\<^bold>\<down>)" using assms 0 by blast
      show "a\<^bold>\<down> \<in> Hom a \<^bold>\<lfloor>a\<^bold>\<rfloor>" using assms 0 by blast
    qed

    lemma red_in_Hom:
    assumes "Ide a"
    shows "a\<^bold>\<down> \<in> Hom a \<^bold>\<lfloor>a\<^bold>\<rfloor>"
      using assms Can_red Can_implies_Arr by simp

    lemma Diagonalize_red [simp]:
    assumes "Ide a"
    shows "\<^bold>\<lfloor>a\<^bold>\<down>\<^bold>\<rfloor> = \<^bold>\<lfloor>a\<^bold>\<rfloor>"
      using assms Can_red Ide_Diagonalize_Can Diagonalize_in_Hom Ide_in_Hom by fastforce

    lemma Diagonalize_red2 [simp]:
    assumes "Ide a" and "Ide b" and "Diag a" and "Diag b"
    shows "\<^bold>\<lfloor>a \<^bold>\<Down> b\<^bold>\<rfloor> = \<^bold>\<lfloor>a \<^bold>\<otimes> b\<^bold>\<rfloor>"
      using assms Can_red2 Ide_Diagonalize_Can Diagonalize_in_Hom [of "a \<^bold>\<Down> b"]
            red2_in_Hom Ide_in_Hom
      by simp

  end

  section "Coherence"

  text\<open>
    If @{term D} is a monoidal category, then a functor \<open>V: C \<rightarrow> D\<close> extends
    in an evident way to an evaluation map that interprets each formal arrow of the
    monoidal language of @{term C} as an arrow of @{term D}.
\<close>

  locale evaluation_map =
    monoidal_language C +
    monoidal_category D T \<alpha> \<iota> +
    V: "functor" C D V
  for C :: "'c comp"                  (infixr "\<cdot>\<^sub>C" 55)
  and D :: "'d comp"                  (infixr "\<cdot>" 55)
  and T :: "'d * 'd \<Rightarrow> 'd"
  and \<alpha> :: "'d * 'd * 'd \<Rightarrow> 'd"
  and \<iota> :: 'd
  and V :: "'c \<Rightarrow> 'd"
  begin

    no_notation C.in_hom               ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    notation unity                     ("\<I>")
    notation runit                     ("\<r>[_]")
    notation lunit                     ("\<l>[_]")
    notation assoc'                    ("\<a>\<^sup>-\<^sup>1[_, _, _]")
    notation runit'                    ("\<r>\<^sup>-\<^sup>1[_]")
    notation lunit'                    ("\<l>\<^sup>-\<^sup>1[_]")

    primrec eval :: "'c term \<Rightarrow> 'd"    ("\<lbrace>_\<rbrace>")
    where "\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle>\<rbrace> = V f"
        | "\<lbrace>\<^bold>\<I>\<rbrace> = \<I>"
        | "\<lbrace>t \<^bold>\<otimes> u\<rbrace> = \<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace>"
        | "\<lbrace>t \<^bold>\<cdot> u\<rbrace> = \<lbrace>t\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
        | "\<lbrace>\<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace> = \<ll> \<lbrace>t\<rbrace>"
        | "\<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = \<ll>' \<lbrace>t\<rbrace>"
        | "\<lbrace>\<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> = \<rho> \<lbrace>t\<rbrace>"
        | "\<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = \<rho>' \<lbrace>t\<rbrace>"
        | "\<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> = \<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"
        | "\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = \<alpha>' (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"

    text\<open>
      Identity terms evaluate to identities of \<open>D\<close> and evaluation preserves
      domain and codomain.
\<close>

    lemma ide_eval_Ide [simp]:
    shows "Ide t \<Longrightarrow> ide \<lbrace>t\<rbrace>"
      by (induct t, auto)

    lemma eval_in_hom:
    shows "Arr t \<Longrightarrow> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
      apply (induct t)
               apply auto[4]
          apply fastforce
    proof -
      fix t u v
      assume I: "Arr t \<Longrightarrow> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
      show "Arr \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> \<guillemotleft>\<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> : \<lbrace>Dom \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> \<rightarrow> \<lbrace>Cod \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>\<guillemotright>"
        using I arr_dom_iff_arr [of "\<lbrace>t\<rbrace>"] by force
      show "Arr \<^bold>\<r>\<^bold>[t\<^bold>] \<Longrightarrow> \<guillemotleft>\<lbrace>\<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> : \<lbrace>Dom \<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> \<rightarrow> \<lbrace>Cod \<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace>\<guillemotright>"
        using I arr_cod_iff_arr [of "\<lbrace>t\<rbrace>"] by force
      show "Arr \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> \<guillemotleft>\<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> : \<lbrace>Dom \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> \<rightarrow> \<lbrace>Cod \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>\<guillemotright>"
        using I arr_dom_iff_arr [of "\<lbrace>t\<rbrace>"] by force
      assume I1: "Arr t \<Longrightarrow> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
      assume I2: "Arr u \<Longrightarrow> \<guillemotleft>\<lbrace>u\<rbrace> : \<lbrace>Dom u\<rbrace> \<rightarrow> \<lbrace>Cod u\<rbrace>\<guillemotright>"
      assume I3: "Arr v \<Longrightarrow> \<guillemotleft>\<lbrace>v\<rbrace> : \<lbrace>Dom v\<rbrace> \<rightarrow> \<lbrace>Cod v\<rbrace>\<guillemotright>"
      show "Arr \<^bold>\<a>\<^bold>[t, u, v\<^bold>] \<Longrightarrow> \<guillemotleft>\<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> : \<lbrace>Dom \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> \<rightarrow> \<lbrace>Cod \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace>\<guillemotright>"
      proof -
        assume 1: "Arr \<^bold>\<a>\<^bold>[t, u, v\<^bold>]"
        have t: "\<guillemotleft>\<lbrace>t\<rbrace> : dom \<lbrace>t\<rbrace> \<rightarrow> cod \<lbrace>t\<rbrace>\<guillemotright>" using 1 I1 by auto
        have u: "\<guillemotleft>\<lbrace>u\<rbrace> : dom \<lbrace>u\<rbrace> \<rightarrow> cod \<lbrace>u\<rbrace>\<guillemotright>" using 1 I2 by auto
        have v: "\<guillemotleft>\<lbrace>v\<rbrace> : dom \<lbrace>v\<rbrace> \<rightarrow> cod \<lbrace>v\<rbrace>\<guillemotright>" using 1 I3 by auto
        have "\<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> = (\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace> \<otimes> \<lbrace>v\<rbrace>) \<cdot> \<a>[dom \<lbrace>t\<rbrace>, dom \<lbrace>u\<rbrace>, dom \<lbrace>v\<rbrace>]"
          using t u v \<alpha>_simp [of "\<lbrace>t\<rbrace>" "\<lbrace>u\<rbrace>" "\<lbrace>v\<rbrace>"] by auto
        moreover have "\<guillemotleft>(\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace> \<otimes> \<lbrace>v\<rbrace>) \<cdot> \<a>[dom \<lbrace>t\<rbrace>, dom \<lbrace>u\<rbrace>, dom \<lbrace>v\<rbrace>] :
                         (dom \<lbrace>t\<rbrace> \<otimes> dom \<lbrace>u\<rbrace>) \<otimes> dom \<lbrace>v\<rbrace> \<rightarrow> cod \<lbrace>t\<rbrace> \<otimes> cod \<lbrace>u\<rbrace> \<otimes> cod \<lbrace>v\<rbrace>\<guillemotright>"
          using t u v by (elim in_homE, auto)
        moreover have "\<lbrace>Dom t\<rbrace> = dom \<lbrace>t\<rbrace> \<and> \<lbrace>Dom u\<rbrace> = dom \<lbrace>u\<rbrace> \<and> \<lbrace>Dom v\<rbrace> = dom \<lbrace>v\<rbrace> \<and>
                       \<lbrace>Cod t\<rbrace> = cod \<lbrace>t\<rbrace> \<and> \<lbrace>Cod u\<rbrace> = cod \<lbrace>u\<rbrace> \<and> \<lbrace>Cod v\<rbrace> = cod \<lbrace>v\<rbrace>"
          using 1 I1 I2 I3 by auto
        ultimately show "\<guillemotleft>\<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> : \<lbrace>Dom \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> \<rightarrow> \<lbrace>Cod \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace>\<guillemotright>"
          by simp
      qed
      show "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] \<Longrightarrow>  \<guillemotleft>\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> : \<lbrace>Dom \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> \<rightarrow> \<lbrace>Cod \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace>\<guillemotright>"
       proof -
        assume 1: "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]"
        have t: "\<guillemotleft>\<lbrace>t\<rbrace> : dom \<lbrace>t\<rbrace> \<rightarrow> cod \<lbrace>t\<rbrace>\<guillemotright>" using 1 I1 by auto
        have u: "\<guillemotleft>\<lbrace>u\<rbrace> : dom \<lbrace>u\<rbrace> \<rightarrow> cod \<lbrace>u\<rbrace>\<guillemotright>" using 1 I2 by auto
        have v: "\<guillemotleft>\<lbrace>v\<rbrace> : dom \<lbrace>v\<rbrace> \<rightarrow> cod \<lbrace>v\<rbrace>\<guillemotright>" using 1 I3 by auto
        have "\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = ((\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace>) \<otimes> \<lbrace>v\<rbrace>) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<lbrace>t\<rbrace>, dom \<lbrace>u\<rbrace>, dom \<lbrace>v\<rbrace>]"
          using 1 I1 I2 I3 \<alpha>'_simp [of "\<lbrace>t\<rbrace>" "\<lbrace>u\<rbrace>" "\<lbrace>v\<rbrace>"] by auto
        moreover have "\<guillemotleft>((\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace>) \<otimes> \<lbrace>v\<rbrace>) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<lbrace>t\<rbrace>, dom \<lbrace>u\<rbrace>, dom \<lbrace>v\<rbrace>] :
                          dom \<lbrace>t\<rbrace> \<otimes> dom \<lbrace>u\<rbrace> \<otimes> dom \<lbrace>v\<rbrace> \<rightarrow> (cod \<lbrace>t\<rbrace> \<otimes> cod \<lbrace>u\<rbrace>) \<otimes> cod \<lbrace>v\<rbrace>\<guillemotright>"
          using t u v assoc'_in_hom [of "dom \<lbrace>t\<rbrace>" "dom \<lbrace>u\<rbrace>" "dom \<lbrace>v\<rbrace>"]
          by (elim in_homE, auto)
        moreover have "\<lbrace>Dom t\<rbrace> = dom \<lbrace>t\<rbrace> \<and> \<lbrace>Dom u\<rbrace> = dom \<lbrace>u\<rbrace> \<and> \<lbrace>Dom v\<rbrace> = dom \<lbrace>v\<rbrace> \<and>
                       \<lbrace>Cod t\<rbrace> = cod \<lbrace>t\<rbrace> \<and> \<lbrace>Cod u\<rbrace> = cod \<lbrace>u\<rbrace> \<and> \<lbrace>Cod v\<rbrace> = cod \<lbrace>v\<rbrace>"
          using 1 I1 I2 I3 by auto
        ultimately show " \<guillemotleft>\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> : \<lbrace>Dom \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> \<rightarrow> \<lbrace>Cod \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace>\<guillemotright>"
          by simp
      qed
    qed

    lemma arr_eval [simp]:
    assumes "Arr f"
    shows "arr \<lbrace>f\<rbrace>"
      using assms eval_in_hom by auto

    lemma dom_eval [simp]:
    assumes "Arr f"
    shows "dom \<lbrace>f\<rbrace> = \<lbrace>Dom f\<rbrace>"
      using assms eval_in_hom by auto
      
    lemma cod_eval [simp]:
    assumes "Arr f"
    shows "cod \<lbrace>f\<rbrace> = \<lbrace>Cod f\<rbrace>"
      using assms eval_in_hom by auto
      
    lemma eval_Prim [simp]:
    assumes "C.arr f"
    shows "\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle>\<rbrace> = V f"
      by simp

    lemma eval_Tensor [simp]:
    assumes "Arr t" and "Arr u"
    shows "\<lbrace>t \<^bold>\<otimes> u\<rbrace> = \<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace>"
      using assms eval_in_hom by auto

    lemma eval_Comp [simp]:
    assumes "Arr t" and "Arr u" and "Dom t = Cod u"
    shows " \<lbrace>t \<^bold>\<cdot> u\<rbrace> = \<lbrace>t\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
      using assms by simp

    lemma eval_Lunit [simp]:
    assumes "Arr t"
    shows "\<lbrace>\<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace> = \<l>[\<lbrace>Cod t\<rbrace>] \<cdot> (\<I> \<otimes> \<lbrace>t\<rbrace>)"
      using assms lunit_naturality [of "\<lbrace>t\<rbrace>"] by simp

    lemma eval_Lunit' [simp]:
    assumes "Arr t"
    shows "\<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = \<l>\<^sup>-\<^sup>1[\<lbrace>Cod t\<rbrace>] \<cdot> \<lbrace>t\<rbrace>"
      using assms lunit'_naturality [of "\<lbrace>t\<rbrace>"] \<ll>'.map_simp [of "\<lbrace>t\<rbrace>"] \<ll>_ide_simp
            Arr_implies_Ide_Cod
      by simp

    lemma eval_Runit [simp]:
    assumes "Arr t"
    shows "\<lbrace>\<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> = \<r>[\<lbrace>Cod t\<rbrace>] \<cdot> (\<lbrace>t\<rbrace> \<otimes> \<I>)"
      using assms runit_naturality [of "\<lbrace>t\<rbrace>"] by simp

    lemma eval_Runit' [simp]:
    assumes "Arr t"
    shows "\<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = \<r>\<^sup>-\<^sup>1[\<lbrace>Cod t\<rbrace>] \<cdot> \<lbrace>t\<rbrace>"
      using assms runit'_naturality [of "\<lbrace>t\<rbrace>"] \<rho>'.map_simp [of "\<lbrace>t\<rbrace>"] \<rho>_ide_simp
            Arr_implies_Ide_Cod
      by simp

    lemma eval_Assoc [simp]:
    assumes "Arr t" and "Arr u" and "Arr v"
    shows "\<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> = \<a>[cod \<lbrace>t\<rbrace>, cod \<lbrace>u\<rbrace>, cod \<lbrace>v\<rbrace>] \<cdot> ((\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace>) \<otimes> \<lbrace>v\<rbrace>)"
      using assms \<alpha>.is_natural_2 [of "(\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"] by auto

    lemma eval_Assoc' [simp]:
    assumes "Arr t" and "Arr u" and "Arr v"
    shows "\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = \<a>\<^sup>-\<^sup>1[cod \<lbrace>t\<rbrace>, cod \<lbrace>u\<rbrace>, cod \<lbrace>v\<rbrace>] \<cdot> (\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace> \<otimes> \<lbrace>v\<rbrace>)"
      using assms \<alpha>'_simp [of "\<lbrace>t\<rbrace>" "\<lbrace>u\<rbrace>" "\<lbrace>v\<rbrace>"] assoc'_naturality [of "\<lbrace>t\<rbrace>" "\<lbrace>u\<rbrace>" "\<lbrace>v\<rbrace>"]
      by simp

    text\<open>
      The following are conveniences for the case of identity arguments
      to avoid having to get rid of the extra identities that are introduced by
      the general formulas above.
\<close>

    lemma eval_Lunit_Ide [simp]:
    assumes "Ide a"
    shows "\<lbrace>\<^bold>\<l>\<^bold>[a\<^bold>]\<rbrace> = \<l>[\<lbrace>a\<rbrace>]"
      using assms comp_cod_arr by simp

    lemma eval_Lunit'_Ide [simp]:
    assumes "Ide a"
    shows "\<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[a\<^bold>]\<rbrace> = \<l>\<^sup>-\<^sup>1[\<lbrace>a\<rbrace>]"
      using assms comp_cod_arr by simp

    lemma eval_Runit_Ide [simp]:
    assumes "Ide a"
    shows "\<lbrace>\<^bold>\<r>\<^bold>[a\<^bold>]\<rbrace> = \<r>[\<lbrace>a\<rbrace>]"
      using assms comp_cod_arr by simp

    lemma eval_Runit'_Ide [simp]:
    assumes "Ide a"
    shows "\<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[a\<^bold>]\<rbrace> = \<r>\<^sup>-\<^sup>1[\<lbrace>a\<rbrace>]"
      using assms comp_cod_arr by simp

    lemma eval_Assoc_Ide [simp]:
    assumes "Ide a" and "Ide b" and "Ide c"
    shows "\<lbrace>\<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<rbrace> = \<a>[\<lbrace>a\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
      using assms by simp

    lemma eval_Assoc'_Ide [simp]:
    assumes "Ide a" and "Ide b" and "Ide c"
    shows "\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[a, b, c\<^bold>]\<rbrace> = \<a>\<^sup>-\<^sup>1[\<lbrace>a\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
      using assms \<alpha>'_ide_simp by simp

    text\<open>
      Canonical arrows evaluate to isomorphisms in \<open>D\<close>, and formal inverses evaluate
      to inverses in \<open>D\<close>.
\<close>

    lemma iso_eval_Can:
    shows "Can t \<Longrightarrow> iso \<lbrace>t\<rbrace>"
      using Can_implies_Arr iso_is_arr \<ll>'.preserves_iso \<rho>'.preserves_iso
            \<alpha>.preserves_iso \<alpha>'.preserves_iso Arr_implies_Ide_Dom Arr_implies_Ide_Cod
      by (induct t, auto)

    lemma eval_Inv_Can:
    shows "Can t \<Longrightarrow> \<lbrace>Inv t\<rbrace> = inv \<lbrace>t\<rbrace>"
      apply (induct t)
      using iso_eval_Can inv_comp Can_implies_Arr
               apply auto[4]
    proof -
      fix t
      assume I: "Can t \<Longrightarrow> \<lbrace>Inv t\<rbrace> = inv \<lbrace>t\<rbrace>"
      show "Can \<^bold>\<l>\<^bold>[t\<^bold>] \<Longrightarrow> \<lbrace>Inv \<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace> = inv \<lbrace>\<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace>"
        using I \<ll>'.is_natural_2 [of "inv \<lbrace>t\<rbrace>"] iso_eval_Can \<ll>_ide_simp iso_is_arr
             comp_cod_arr inv_comp
        by simp
      show "Can \<^bold>\<r>\<^bold>[t\<^bold>] \<Longrightarrow> \<lbrace>Inv \<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> = inv \<lbrace>\<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace>"
        using I \<rho>'.is_natural_2 [of "inv \<lbrace>t\<rbrace>"] iso_eval_Can \<rho>_ide_simp iso_is_arr
              comp_cod_arr inv_comp
        by simp
      show "Can \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> \<lbrace>Inv \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = inv \<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>"
      proof -
        assume t: "Can \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
        hence 1: "iso \<lbrace>t\<rbrace>" using iso_eval_Can by simp
        have "inv \<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = inv (\<ll>' \<lbrace>t\<rbrace>)"
          using t by simp
        also have "... = inv (\<l>\<^sup>-\<^sup>1[cod \<lbrace>t\<rbrace>] \<cdot> \<lbrace>t\<rbrace>)"
          using 1 \<ll>'.is_natural_2 [of "\<lbrace>t\<rbrace>"] \<ll>'_ide_simp iso_is_arr by auto
        also have "... = \<lbrace>Inv \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>"
          using t I 1 iso_inv_iso iso_is_arr inv_comp by auto
        finally show ?thesis by simp
      qed
      show "Can \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> \<lbrace>Inv \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = inv \<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>"
      proof -
        assume t: "Can \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
        hence 1: "iso \<lbrace>t\<rbrace>" using iso_eval_Can by simp
        have "inv \<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = inv (\<rho>' \<lbrace>t\<rbrace>)"
          using t by simp
        also have "... = inv (\<r>\<^sup>-\<^sup>1[cod \<lbrace>t\<rbrace>] \<cdot> \<lbrace>t\<rbrace>)"
          using 1 \<rho>'.is_natural_2 [of "\<lbrace>t\<rbrace>"] \<rho>'_ide_simp iso_is_arr by auto
        also have "... = \<lbrace>Inv \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>"
          using t I 1 iso_inv_iso iso_is_arr inv_comp by auto
        finally show ?thesis by simp
      qed
      next
      fix t u v
      assume I1: "Can t \<Longrightarrow> \<lbrace>Inv t\<rbrace> = inv \<lbrace>t\<rbrace>"
      assume I2: "Can u \<Longrightarrow> \<lbrace>Inv u\<rbrace> = inv \<lbrace>u\<rbrace>"
      assume I3: "Can v \<Longrightarrow> \<lbrace>Inv v\<rbrace> = inv \<lbrace>v\<rbrace>"
      show "Can \<^bold>\<a>\<^bold>[t, u, v\<^bold>] \<Longrightarrow> \<lbrace>Inv \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> = inv \<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace>"
      proof -
        assume tuv: "Can \<^bold>\<a>\<^bold>[t, u, v\<^bold>]"
        have t: "iso \<lbrace>t\<rbrace>" using tuv iso_eval_Can by auto
        have u: "iso \<lbrace>u\<rbrace>" using tuv iso_eval_Can by auto
        have v: "iso \<lbrace>v\<rbrace>" using tuv iso_eval_Can by auto
        have "\<lbrace>Inv \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> = \<alpha>' (inv \<lbrace>t\<rbrace>, inv \<lbrace>u\<rbrace>, inv \<lbrace>v\<rbrace>)"
          using tuv I1 I2 I3 by simp
        also have "... = inv (\<a>[cod \<lbrace>t\<rbrace>, cod \<lbrace>u\<rbrace>, cod \<lbrace>v\<rbrace>] \<cdot> ((\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace>) \<otimes> \<lbrace>v\<rbrace>))"
          using t u v \<alpha>'_simp iso_is_arr iso_inv_iso inv_comp inv_inv by auto
        also have "... = inv ((\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace> \<otimes> \<lbrace>v\<rbrace>) \<cdot> \<a>[dom \<lbrace>t\<rbrace>, dom \<lbrace>u\<rbrace>, dom \<lbrace>v\<rbrace>])"
          using t u v iso_is_arr assoc_naturality by simp
        also have "... = inv \<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace>"
          using t u v iso_is_arr \<alpha>_simp [of "\<lbrace>t\<rbrace>" "\<lbrace>u\<rbrace>" "\<lbrace>v\<rbrace>"] by simp
        finally show ?thesis by simp
      qed
      show "Can \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] \<Longrightarrow> \<lbrace>Inv \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = inv \<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace>"
      proof -
        assume tuv: "Can \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]"
        have t: "iso \<lbrace>t\<rbrace>" using tuv iso_eval_Can by auto
        have u: "iso \<lbrace>u\<rbrace>" using tuv iso_eval_Can by auto
        have v: "iso \<lbrace>v\<rbrace>" using tuv iso_eval_Can by auto
        have "\<lbrace>Inv \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = \<alpha> (inv \<lbrace>t\<rbrace>, inv \<lbrace>u\<rbrace>, inv \<lbrace>v\<rbrace>)"
          using tuv I1 I2 I3 by simp
        also have "... = (inv \<lbrace>t\<rbrace> \<otimes> inv \<lbrace>u\<rbrace> \<otimes> inv \<lbrace>v\<rbrace>) \<cdot> \<a>[cod \<lbrace>t\<rbrace>, cod \<lbrace>u\<rbrace>, cod \<lbrace>v\<rbrace>]"
          using t u v iso_is_arr \<alpha>_simp [of "inv \<lbrace>t\<rbrace>" "inv \<lbrace>u\<rbrace>" "inv \<lbrace>v\<rbrace>"] by simp
        also have "... = inv (\<a>\<^sup>-\<^sup>1[cod \<lbrace>t\<rbrace>, cod \<lbrace>u\<rbrace>, cod \<lbrace>v\<rbrace>] \<cdot> (\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace> \<otimes> \<lbrace>v\<rbrace>))"
          using t u v iso_is_arr iso_inv_iso inv_inv inv_comp by auto
        also have "... = inv (((\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace>) \<otimes> \<lbrace>v\<rbrace>) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<lbrace>t\<rbrace>, dom \<lbrace>u\<rbrace>, dom \<lbrace>v\<rbrace>])"
          using t u v iso_is_arr assoc'_naturality by simp
        also have "... = inv \<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace>"
          using t u v iso_is_arr \<alpha>'_simp by auto
        finally show ?thesis by blast
      qed
    qed

    text\<open>
      The operation \<open>\<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor>\<close> evaluates to composition in \<open>D\<close>.
\<close>

    lemma eval_CompDiag:
    assumes "Diag t" and "Diag u" and "Seq t u"
    shows "\<lbrace>t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<rbrace> = \<lbrace>t\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
    proof -
      have "\<And>u. \<lbrakk> Diag t; Diag u; Seq t u \<rbrakk> \<Longrightarrow> \<lbrace>t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<rbrace> = \<lbrace>t\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
        using eval_in_hom comp_cod_arr
      proof (induct t, simp_all)
        fix u f
        assume u: "Diag u"
        assume f: "C.arr f"
        assume 1: "Arr u \<and> \<^bold>\<langle>C.dom f\<^bold>\<rangle> = Cod u"
        show "\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<rbrace> = V f \<cdot> \<lbrace>u\<rbrace>"
          using f u 1 preserves_comp_2 by (cases u; simp)
        next
        fix u v w
        assume I1: "\<And>u. \<lbrakk> Diag v; Diag u; Arr u \<and> Dom v = Cod u \<rbrakk> \<Longrightarrow>
                         \<lbrace>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<rbrace> = \<lbrace>v\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
        assume I2: "\<And>u. \<lbrakk> Diag w; Diag u; Arr u \<and> Dom w = Cod u \<rbrakk> \<Longrightarrow>
                         \<lbrace>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<rbrace> = \<lbrace>w\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
        assume vw: "Diag (Tensor v w)"
        have v: "Diag v \<and> v = Prim (un_Prim v)"
          using vw by (simp add: Diag_TensorE)
        have w: "Diag w"
          using vw by (simp add: Diag_TensorE)
        assume u: "Diag u"
        assume 1: "Arr v \<and> Arr w \<and> Arr u \<and> Dom v \<^bold>\<otimes> Dom w = Cod u"
        show "\<lbrace>(v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<rbrace> = (\<lbrace>v\<rbrace> \<otimes> \<lbrace>w\<rbrace>) \<cdot> \<lbrace>u\<rbrace>"
          using u 1 eval_in_hom CompDiag_in_Hom
        proof (cases u, simp_all)
          fix x y
          assume 3: "u = x \<^bold>\<otimes> y"
          assume 4: "Arr v \<and> Arr w \<and> Dom v = Cod x \<and> Dom w = Cod y"
          have x: "Diag x"
            using u 1 3 Diag_TensorE [of x y] by simp
          have y: "Diag y"
            using u x 1 3 Diag_TensorE [of x y] by simp
          show "\<lbrace>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x\<rbrace> \<otimes> \<lbrace>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y\<rbrace> = (\<lbrace>v\<rbrace> \<otimes> \<lbrace>w\<rbrace>) \<cdot> (\<lbrace>x\<rbrace> \<otimes> \<lbrace>y\<rbrace>)"
            using v w x y 4 I1 I2 CompDiag_in_Hom eval_in_hom Diag_implies_Arr interchange
            by auto
        qed
      qed
      thus ?thesis using assms by blast
    qed

    text\<open>
      For identity terms @{term a} and @{term b}, the reduction @{term "(a \<^bold>\<otimes> b)\<^bold>\<down>"}
      factors (under evaluation in \<open>D\<close>) into the parallel reduction @{term "a\<^bold>\<down> \<^bold>\<otimes> b\<^bold>\<down>"},
      followed by a reduction of its codomain @{term "\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>"}.
\<close>

    lemma eval_red_Tensor:
    assumes "Ide a" and "Ide b"
    shows "\<lbrace>(a \<^bold>\<otimes> b)\<^bold>\<down>\<rbrace> = \<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>a\<^bold>\<down>\<rbrace> \<otimes> \<lbrace>b\<^bold>\<down>\<rbrace>)"
    proof -
      have "Diag (a \<^bold>\<otimes> b) \<Longrightarrow> ?thesis"
        using assms Can_red2 Ide_implies_Arr red_Diag
              Diagonalize_Diag red2_Diag Can_implies_Arr iso_eval_Can iso_is_arr
        apply simp
        using Diag_TensorE eval_Tensor Diagonalize_Diag Diag_implies_Arr red_Diag
              tensor_preserves_ide ide_eval_Ide dom_eval comp_arr_dom
        by metis
      moreover have "\<not> Diag (a \<^bold>\<otimes> b) \<Longrightarrow> ?thesis"
        using assms Can_red2 by (simp add: Can_red(1) iso_eval_Can)
      ultimately show ?thesis by blast
    qed

    lemma eval_red2_Diag_Unity:
    assumes "Ide a" and "Diag a"
    shows "\<lbrace>a \<^bold>\<Down> \<^bold>\<I>\<rbrace> = \<r>[\<lbrace>a\<rbrace>]"
      using assms tensor_preserves_ide \<rho>_ide_simp unitor_coincidence \<iota>_in_hom comp_cod_arr
      by (cases a, auto)

    text\<open>
      Define a formal arrow t to be ``coherent'' if the square formed by @{term t}, @{term "\<^bold>\<lfloor>t\<^bold>\<rfloor>"}
      and the reductions @{term "Dom t\<^bold>\<down>"} and @{term "Cod t\<^bold>\<down>"} commutes under evaluation
      in \<open>D\<close>.  We will show that all formal arrows are coherent.
      Since the diagonalizations of canonical arrows are identities, a corollary is that parallel
      canonical arrows have equal evaluations.
\<close>

    abbreviation coherent
    where "coherent t \<equiv> \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t\<rbrace> = \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>"

    text\<open>
      Diagonal arrows are coherent, since for such arrows @{term t} the reductions
      @{term "Dom t\<^bold>\<down>"} and @{term "Cod t\<^bold>\<down>"} are identities.
\<close>

    lemma Diag_implies_coherent:
    assumes "Diag t"
    shows "coherent t"
      using assms Diag_implies_Arr Arr_implies_Ide_Dom Arr_implies_Ide_Cod
            Dom_preserves_Diag Cod_preserves_Diag Diagonalize_Diag red_Diag
            comp_arr_dom comp_cod_arr
      by simp

    text\<open>
      The evaluation of a coherent arrow @{term t} has a canonical factorization in \<open>D\<close>
      into the evaluations of a reduction @{term "Dom t\<^bold>\<down>"}, diagonalization @{term "\<^bold>\<lfloor>t\<^bold>\<rfloor>"},
      and inverse reduction @{term "Inv (Cod t\<^bold>\<down>)"}.
      This will later allow us to use the term @{term "Inv (Cod t\<^bold>\<down>) \<^bold>\<cdot> \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<cdot> Dom t\<^bold>\<down>"}
      as a normal form for @{term t}.
\<close>

    lemma canonical_factorization:
    assumes "Arr t"
    shows "coherent t \<longleftrightarrow> \<lbrace>t\<rbrace> = inv \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>"
    proof
      assume 1: "coherent t"
      have "inv \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace> = inv \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t\<rbrace>"
        using 1 by simp
      also have "... = (inv \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Cod t\<^bold>\<down>\<rbrace>) \<cdot> \<lbrace>t\<rbrace>"
        using comp_assoc by simp
      also have "... = \<lbrace>t\<rbrace>"
        using assms 1 red_in_Hom inv_in_hom Arr_implies_Ide_Cod Can_red iso_eval_Can
              comp_cod_arr Ide_in_Hom inv_is_inverse
        by (simp add: comp_inv_arr)
      finally show "\<lbrace>t\<rbrace> = inv \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>" by simp
      next
      assume 1: "\<lbrace>t\<rbrace> = inv \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>"
      hence "\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t\<rbrace> = \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> inv \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>" by simp
      also have "... = (\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> inv \<lbrace>Cod t\<^bold>\<down>\<rbrace>) \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>"
        using comp_assoc by simp
      also have "... = \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>"
        using assms 1 red_in_Hom Arr_implies_Ide_Cod Can_red iso_eval_Can inv_is_inverse
              Diagonalize_in_Hom comp_arr_inv comp_cod_arr Arr_implies_Ide_Dom Diagonalize_in_Hom
        by auto
      finally show "coherent t" by blast
    qed

    text\<open>
      A canonical arrow is coherent if and only if its formal inverse is.
\<close>

    lemma Can_implies_coherent_iff_coherent_Inv:
    assumes "Can t"
    shows "coherent t \<longleftrightarrow> coherent (Inv t)"
    proof
      have 1: "\<And>t. Can t \<Longrightarrow> coherent t \<Longrightarrow> coherent (Inv t)"
      proof -
        fix t
        assume "Can t"
        hence t: "Can t \<and> Arr t \<and> Ide (Dom t) \<and> Ide (Cod t) \<and>
                  arr \<lbrace>t\<rbrace> \<and> iso \<lbrace>t\<rbrace> \<and> inverse_arrows \<lbrace>t\<rbrace> (inv \<lbrace>t\<rbrace>) \<and>
                  Can \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> Arr \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> arr \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<and> iso \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<and> \<^bold>\<lfloor>t\<^bold>\<rfloor> \<in> Hom \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<and>
                  inverse_arrows \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> (inv \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>) \<and> Inv t \<in> Hom (Cod t) (Dom t)"
          using assms Can_implies_Arr Arr_implies_Ide_Dom Arr_implies_Ide_Cod iso_eval_Can
                inv_is_inverse Diagonalize_in_Hom Diagonalize_preserves_Can Inv_in_Hom
          by simp
        assume coh: "coherent t"
        have "\<lbrace>Cod (Inv t)\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Inv t\<rbrace> = (inv \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>) \<cdot> \<lbrace>Cod (Inv t)\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Inv t\<rbrace>"
          using t coh red_in_Hom comp_cod_arr Can_implies_Arr Can_red(1) Inv_preserves_Can(1)
                Inv_preserves_Can(3) canonical_factorization comp_inv_arr iso_eval_Can iso_is_arr
          by auto
        also have "... = inv \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t\<rbrace>) \<cdot> inv \<lbrace>t\<rbrace>"
          using t eval_Inv_Can coh comp_assoc by auto
        also have "... = \<lbrace>\<^bold>\<lfloor>Inv t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom (Inv t)\<^bold>\<down>\<rbrace>"
          using t Diagonalize_Inv eval_Inv_Can comp_arr_inv red_in_Hom comp_arr_dom comp_assoc
          by auto
        finally show "coherent (Inv t)" by blast
      qed
      show "coherent t \<Longrightarrow> coherent (Inv t)" using assms 1 by simp
      show "coherent (Inv t) \<Longrightarrow> coherent t"
      proof -
        assume "coherent (Inv t)"
        hence "coherent (Inv (Inv t))"
          using assms 1 Inv_preserves_Can by blast
        thus ?thesis using assms by simp
      qed
    qed

    text\<open>
      Some special cases of coherence are readily dispatched.
\<close>

    lemma coherent_Unity:
    shows "coherent \<^bold>\<I>"
      by simp

    lemma coherent_Prim:
    assumes "Arr \<^bold>\<langle>f\<^bold>\<rangle>"
    shows "coherent \<^bold>\<langle>f\<^bold>\<rangle>"
      using assms by simp

    lemma coherent_Lunit_Ide:
    assumes "Ide a"
    shows "coherent \<^bold>\<l>\<^bold>[a\<^bold>]"
    proof -
      have a: "Ide a \<and> Arr a \<and> Dom a = a \<and> Cod a = a \<and>
               ide \<lbrace>a\<rbrace> \<and> ide \<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace> \<and> \<lbrace>a\<^bold>\<down>\<rbrace> \<in> hom \<lbrace>a\<rbrace> \<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace>"
        using assms Ide_implies_Arr Ide_in_Hom Diagonalize_preserves_Ide red_in_Hom by auto
      thus ?thesis
        using a lunit_naturality [of "\<lbrace>a\<^bold>\<down>\<rbrace>"] comp_cod_arr by auto
    qed
      
    lemma coherent_Runit_Ide:
    assumes "Ide a"
    shows "coherent \<^bold>\<r>\<^bold>[a\<^bold>]"
    proof -
      have a: "Ide a \<and> Arr a \<and> Dom a = a \<and> Cod a = a \<and>
               ide \<lbrace>a\<rbrace> \<and> ide \<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace> \<and> \<lbrace>a\<^bold>\<down>\<rbrace> \<in> hom \<lbrace>a\<rbrace> \<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace>"
        using assms Ide_implies_Arr Ide_in_Hom Diagonalize_preserves_Ide red_in_Hom
        by auto
      have "\<lbrace>Cod \<^bold>\<r>\<^bold>[a\<^bold>]\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>\<^bold>\<r>\<^bold>[a\<^bold>]\<rbrace> = \<lbrace>a\<^bold>\<down>\<rbrace> \<cdot> \<r>[\<lbrace>a\<rbrace>]"
        using a runit_in_hom comp_cod_arr by simp
      also have "... = \<r>[\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace>] \<cdot> (\<lbrace>a\<^bold>\<down>\<rbrace> \<otimes> \<I>)"
        using a eval_Runit runit_naturality [of "\<lbrace>red a\<rbrace>"] by auto
      also have "... = \<lbrace>\<^bold>\<lfloor>\<^bold>\<r>\<^bold>[a\<^bold>]\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom \<^bold>\<r>\<^bold>[a\<^bold>]\<^bold>\<down>\<rbrace>"
      proof -
        have "\<not> Diag (a \<^bold>\<otimes> \<^bold>\<I>)" by (cases a; simp)
        thus ?thesis
          using a comp_cod_arr red2_in_Hom eval_red2_Diag_Unity Diag_Diagonalize
                Diagonalize_preserves_Ide
          by auto
      qed
      finally show ?thesis by blast
    qed

    lemma coherent_Lunit'_Ide:
    assumes "Ide a"
    shows "coherent \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[a\<^bold>]"
      using assms Ide_implies_Can coherent_Lunit_Ide
            Can_implies_coherent_iff_coherent_Inv [of "Lunit a"] by simp

    lemma coherent_Runit'_Ide:
    assumes "Ide a"
    shows "coherent \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[a\<^bold>]"
      using assms Ide_implies_Can coherent_Runit_Ide
            Can_implies_coherent_iff_coherent_Inv [of "Runit a"] by simp

    text\<open>
      To go further, we need the next result, which is in some sense the crux of coherence:
      For diagonal identities @{term a}, @{term b}, and @{term c},
      the reduction @{term "((a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c) \<^bold>\<cdot> ((a \<^bold>\<Down> b) \<^bold>\<otimes> c)"} from @{term "(a \<^bold>\<otimes> b) \<^bold>\<otimes> c"}
      that first reduces the subterm @{term "a \<^bold>\<otimes> b"} and then reduces the result,
      is equivalent under evaluation in \<open>D\<close> to the reduction that first
      applies the associator @{term "\<^bold>\<a>\<^bold>[a, b, c\<^bold>]"} and then applies the reduction
      @{term "(a \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)) \<^bold>\<cdot> (a \<^bold>\<otimes> (b \<^bold>\<Down> c))"} from @{term "a \<^bold>\<otimes> (b \<^bold>\<otimes> c)"}.
      The triangle and pentagon axioms are used in the proof.
\<close>

    lemma coherence_key_fact:
    assumes "Ide a \<and> Diag a" and "Ide b \<and> Diag b" and "Ide c \<and> Diag c"
    shows "\<lbrace>(a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>a \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)
             = (\<lbrace>a \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<rbrace> \<cdot> (\<lbrace>a\<rbrace> \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>a\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
    proof -
      have "b = \<^bold>\<I> \<Longrightarrow> ?thesis"
        using assms not_is_Tensor_TensorDiagE eval_red2_Diag_Unity triangle
              comp_cod_arr comp_assoc
        by simp
        text \<open>The triangle is used!\<close>
      moreover have "c = \<^bold>\<I> \<Longrightarrow> ?thesis"
        using assms TensorDiag_preserves_Diag TensorDiag_preserves_Ide
              not_is_Tensor_TensorDiagE eval_red2_Diag_Unity
              red2_in_Hom runit_tensor runit_naturality [of "\<lbrace>a \<^bold>\<Down> b\<rbrace>"] comp_assoc
        by simp
      moreover have "\<lbrakk> b \<noteq> \<^bold>\<I>; c \<noteq> \<^bold>\<I> \<rbrakk> \<Longrightarrow> ?thesis"
      proof -
        assume b': "b \<noteq> \<^bold>\<I>"
        hence b: "Ide b \<and> Diag b \<and> Arr b \<and> b \<noteq> \<^bold>\<I> \<and>
                  ide \<lbrace>b\<rbrace> \<and> arr \<lbrace>b\<rbrace> \<and> \<^bold>\<lfloor>b\<^bold>\<rfloor> = b \<and> b\<^bold>\<down> = b \<and> Dom b = b \<and> Cod b = b"
          using assms Diagonalize_preserves_Ide Ide_in_Hom by simp
        assume c': "c \<noteq> \<^bold>\<I>"
        hence c: "Ide c \<and> Diag c \<and> Arr c \<and> c \<noteq> \<^bold>\<I> \<and>
                  ide \<lbrace>c\<rbrace> \<and> arr \<lbrace>c\<rbrace> \<and> \<^bold>\<lfloor>c\<^bold>\<rfloor> = c \<and> c\<^bold>\<down> = c \<and> Dom c = c \<and> Cod c = c"
          using assms Diagonalize_preserves_Ide Ide_in_Hom by simp
        have "\<And>a. Ide a \<and> Diag a \<Longrightarrow>
                   \<lbrace>(a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>a \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)
                      = (\<lbrace>a \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<rbrace> \<cdot> (\<lbrace>a\<rbrace> \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>a\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
        proof -
          fix a :: "'c term"
          show "Ide a \<and> Diag a \<Longrightarrow>
                \<lbrace>(a \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>a \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)
                   = (\<lbrace>a \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<rbrace> \<cdot> (\<lbrace>a\<rbrace> \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>a\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
            apply (induct a)
            using b c TensorDiag_in_Hom apply simp_all
          proof -
            show "\<lbrace>b \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>b\<rbrace> \<cdot> \<l>[\<lbrace>b\<rbrace>] \<otimes> \<lbrace>c\<rbrace>)
                    = ((\<lbrace>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace> \<cdot> \<l>[\<lbrace>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace>]) \<cdot> (\<I> \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<I>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
            proof -
              have "\<lbrace>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace> \<cdot> (\<l>[\<lbrace>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace>] \<cdot> (\<I> \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<I>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>] =
                    \<lbrace>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace> \<cdot> (\<lbrace>b \<^bold>\<Down> c\<rbrace> \<cdot> \<l>[\<lbrace>b\<rbrace> \<otimes> \<lbrace>c\<rbrace>])  \<cdot> \<a>[\<I>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                using b c red2_in_Hom lunit_naturality [of "\<lbrace>b \<^bold>\<Down> c\<rbrace>"] by simp
              thus ?thesis
                using b c red2_in_Hom lunit_tensor comp_arr_dom comp_cod_arr comp_assoc by simp
            qed
            show "\<And>f. C.ide f \<and> C.arr f \<Longrightarrow>
                       \<lbrace>(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)
                         = (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<rbrace> \<cdot> (V f \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[V f, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
            proof -
              fix f
              assume f: "C.ide f \<and> C.arr f"
              show "\<lbrace>(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)
                      = (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<rbrace> \<cdot> (V f \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[V f, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
              proof -
                have "\<lbrace>(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<otimes> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)
                        = ((V f \<otimes> \<lbrace>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (V f \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>) \<cdot> \<a>[V f, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]) \<cdot>
                          ((V f \<otimes> \<lbrace>b\<rbrace>) \<otimes> \<lbrace>c\<rbrace>)"
                proof -
                  have "\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b\<rbrace> = V f \<otimes> \<lbrace>b\<rbrace>"
                    using assms f b c red2_Diag by simp
                  moreover have "\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace> = V f \<otimes> \<lbrace>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace>"
                  proof -
                    have "is_Tensor (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)"
                      using assms b c not_is_Tensor_TensorDiagE by blast
                    thus ?thesis
                      using assms f b c red2_Diag TensorDiag_preserves_Diag(1)
                      by (cases "b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c"; simp)
                  qed
                  ultimately show ?thesis
                    using assms b c by (cases c, simp_all)
                qed
                also have "... = ((V f \<otimes> \<lbrace>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (V f \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[V f, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                  using b c f TensorDiag_in_Hom red2_in_Hom comp_arr_dom comp_cod_arr
                  by simp
                also have "... = (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<rbrace> \<cdot> (V f \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[V f, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                    using b c f Ide_implies_Arr TensorDiag_preserves_Ide not_is_Tensor_TensorDiagE
                    by (cases "b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c", simp_all; blast)
                finally show ?thesis by blast
              qed
            qed
            fix d e
            assume I: "Diag e \<Longrightarrow> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>e \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)
                                    = (\<lbrace>e \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace> \<cdot> (\<lbrace>e\<rbrace> \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
            assume de: "Ide d \<and> Ide e \<and> Diag (d \<^bold>\<otimes> e)"
            show "\<lbrace>((d \<^bold>\<otimes> e) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>(d \<^bold>\<otimes> e) \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)
                    = (\<lbrace>(d \<^bold>\<otimes> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<rbrace> \<cdot> ((\<lbrace>d\<rbrace> \<otimes> \<lbrace>e\<rbrace>) \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>d\<rbrace> \<otimes> \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
            proof -
              let ?f = "un_Prim d"
              have "is_Prim d"
                using de by (cases d, simp_all)
              hence "d = \<^bold>\<langle>?f\<^bold>\<rangle> \<and> C.ide ?f"
                using de by (cases d, simp_all)
              hence d: "Ide d \<and> Arr d \<and> Dom d = d \<and> Cod d = d \<and> Diag d \<and>
                        d = \<^bold>\<langle>?f\<^bold>\<rangle> \<and> C.ide ?f \<and> ide \<lbrace>d\<rbrace> \<and> arr \<lbrace>d\<rbrace>"
                using de ide_eval_Ide Ide_implies_Arr Diag_Diagonalize(1) Ide_in_Hom
                      Diag_TensorE [of d e]
                by simp
              have "Diag e \<and> e \<noteq> \<^bold>\<I>"
                using de Diag_TensorE by metis
              hence e: "Ide e \<and> Arr e \<and> Dom e = e \<and> Cod e = e \<and> Diag e \<and>
                        e \<noteq> \<^bold>\<I> \<and> ide \<lbrace>e\<rbrace> \<and> arr \<lbrace>e\<rbrace>"
                using de Ide_in_Hom by simp
              have 1: "is_Tensor (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<and> is_Tensor (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c) \<and> is_Tensor (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))"
                using b c e de not_is_Tensor_TensorDiagE TensorDiag_preserves_Diag
                      not_is_Tensor_TensorDiagE [of e "b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c"]
                by auto
              have "\<lbrace>((d \<^bold>\<otimes> e) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>(d \<^bold>\<otimes> e) \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)
                      = ((\<lbrace>d\<rbrace> \<otimes> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<otimes> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>) \<cdot>
                         \<a>[\<lbrace>d\<rbrace>, \<lbrace>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<rbrace>, \<lbrace>c\<rbrace>]) \<cdot>
                        ((\<lbrace>d\<rbrace> \<otimes> \<lbrace>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<otimes> \<lbrace>e \<^bold>\<Down> b\<rbrace>) \<cdot> \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<otimes> \<lbrace>c\<rbrace>)"
              proof -
                have "\<lbrace>((d \<^bold>\<otimes> e) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>
                         = (\<lbrace>d\<rbrace> \<otimes> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<otimes> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>) \<cdot>
                           \<a>[\<lbrace>d\<rbrace>, \<lbrace>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<rbrace>, \<lbrace>c\<rbrace>]"
                proof -
                  have "((d \<^bold>\<otimes> e) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c = (d \<^bold>\<otimes> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b)) \<^bold>\<Down> c"
                    using b c d e de 1 TensorDiag_Diag TensorDiag_preserves_Diag TensorDiag_assoc
                          TensorDiag_Prim not_is_Tensor_Unity
                    by metis
                  also have "... = (d \<^bold>\<Down> (\<^bold>\<lfloor>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)) \<^bold>\<cdot> (d \<^bold>\<otimes> ((e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c)) \<^bold>\<cdot>
                                   \<^bold>\<a>\<^bold>[d, e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b, c\<^bold>]"
                    using c d 1 by (cases c) simp_all
                  also have "... = (d \<^bold>\<otimes> ((e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)) \<^bold>\<cdot> (d \<^bold>\<otimes> ((e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c)) \<^bold>\<cdot>
                                   \<^bold>\<a>\<^bold>[d, e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b, c\<^bold>]"
                    using b c d e 1 TensorDiag_preserves_Diag Diagonalize_Diag
                          red2_Diag TensorDiag_assoc
                    by (cases "e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c", simp_all, cases d, simp_all)
                  finally show ?thesis
                    using b c d e TensorDiag_in_Hom red2_in_Hom TensorDiag_preserves_Diag
                          TensorDiag_preserves_Ide
                    by simp
                qed
                moreover have "\<lbrace>(d \<^bold>\<otimes> e) \<^bold>\<Down> b\<rbrace>
                                 = (\<lbrace>d\<rbrace> \<otimes> \<lbrace>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<otimes> \<lbrace>e \<^bold>\<Down> b\<rbrace>) \<cdot> \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>]"
                proof -
                  have "(d \<^bold>\<otimes> e) \<^bold>\<Down> b = (d \<^bold>\<Down> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b)) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> b)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[d, e, b\<^bold>]"
                      using b c d e de 1 TensorDiag_Prim Diagonalize_Diag
                      by (cases b) simp_all
                  also have "... = (d \<^bold>\<otimes> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b)) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> b)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[d, e, b\<^bold>]"
                    using b c d e de 1 TensorDiag_Diag TensorDiag_preserves_Diag
                    by (cases "e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b", simp_all, cases d, simp_all)
                  finally have "(d \<^bold>\<otimes> e) \<^bold>\<Down> b = (d \<^bold>\<otimes> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b)) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> b)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[d, e, b\<^bold>]"
                    by simp
                  thus ?thesis using b d e eval_in_hom TensorDiag_in_Hom red2_in_Hom by simp
                qed
                ultimately show ?thesis by argo
              qed
              also have "... = (\<lbrace>d\<rbrace> \<otimes> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>) \<cdot> \<a>[\<lbrace>d\<rbrace>, \<lbrace>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<rbrace>, \<lbrace>c\<rbrace>] \<cdot>
                               ((\<lbrace>d\<rbrace> \<otimes> \<lbrace>e \<^bold>\<Down> b\<rbrace>) \<otimes> \<lbrace>c\<rbrace>) \<cdot> (\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<otimes> \<lbrace>c\<rbrace>)"
                using b c d e red2_in_Hom TensorDiag_preserves_Ide
                      TensorDiag_preserves_Diag interchange comp_cod_arr comp_assoc
                by simp
              also have "... = (\<lbrace>d\<rbrace> \<otimes> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<otimes> (\<lbrace>e \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)) \<cdot>
                               \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace> \<otimes> \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>] \<cdot> (\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<otimes> \<lbrace>c\<rbrace>)"
                using b c d e TensorDiag_in_Hom red2_in_Hom TensorDiag_preserves_Ide
                      TensorDiag_preserves_Diag assoc_naturality [of "\<lbrace>d\<rbrace>" "\<lbrace>e \<^bold>\<Down> b\<rbrace>" "\<lbrace>c\<rbrace>"]
                      comp_permute [of "\<a>[\<lbrace>d\<rbrace>, \<lbrace>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b\<rbrace>, \<lbrace>c\<rbrace>]" "(\<lbrace>d\<rbrace> \<otimes> \<lbrace>e \<^bold>\<Down> b\<rbrace>) \<otimes> \<lbrace>c\<rbrace>"
                                       "\<lbrace>d\<rbrace> \<otimes> (\<lbrace>e \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)" "\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace> \<otimes> \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"]
                by simp
              also have "... = (\<lbrace>d\<rbrace> \<otimes> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>e \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)) \<cdot>
                               \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace> \<otimes> \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>] \<cdot> (\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<otimes> \<lbrace>c\<rbrace>)"
                using b c d e TensorDiag_in_Hom red2_in_Hom TensorDiag_preserves_Ide
                      TensorDiag_preserves_Diag interchange
                      comp_reduce [of "\<lbrace>d\<rbrace> \<otimes> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>"
                                      "\<lbrace>d\<rbrace> \<otimes> (\<lbrace>e \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)"
                                      "\<lbrace>d\<rbrace> \<otimes> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>e \<^bold>\<Down> b\<rbrace> \<otimes> \<lbrace>c\<rbrace>)"
                                      "\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace> \<otimes> \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>] \<cdot> (\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<otimes> \<lbrace>c\<rbrace>)"]
                 by simp
              also have "... = (((\<lbrace>d\<rbrace> \<otimes> \<lbrace>e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<otimes> \<lbrace>e\<rbrace> \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot>
                                (\<lbrace>d\<rbrace> \<otimes> \<a>[\<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>])) \<cdot>
                               \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace> \<otimes> \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>] \<cdot> (\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<otimes> \<lbrace>c\<rbrace>)"
                using b c d e I TensorDiag_in_Hom red2_in_Hom TensorDiag_preserves_Ide
                      TensorDiag_preserves_Diag interchange
                by simp
              also have "... = ((\<lbrace>d\<rbrace> \<otimes> \<lbrace>e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<otimes> (\<lbrace>e\<rbrace> \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>))) \<cdot>
                                 \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace> \<otimes> \<lbrace>c\<rbrace>] \<cdot> \<a>[\<lbrace>d\<rbrace> \<otimes> \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                using b c d e comp_assoc red2_in_Hom TensorDiag_in_Hom ide_eval_Ide
                      TensorDiag_preserves_Diag tensor_preserves_ide TensorDiag_preserves_Ide
                      pentagon
                by simp
              text \<open>The pentagon is used!\<close>
              also have "... = (((\<lbrace>d\<rbrace> \<otimes> \<lbrace>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<otimes> \<lbrace>e \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace>) \<cdot>
                                 \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace>]) \<cdot> ((\<lbrace>d\<rbrace> \<otimes> \<lbrace>e\<rbrace>) \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot>
                               \<a>[\<lbrace>d\<rbrace> \<otimes> \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                using b c d e 1 red2_in_Hom TensorDiag_preserves_Ide
                      TensorDiag_preserves_Diag assoc_naturality [of "\<lbrace>d\<rbrace>" "\<lbrace>e\<rbrace>" "\<lbrace>b \<^bold>\<Down> c\<rbrace>"]
                      comp_cod_arr comp_assoc
                by simp
              also have "... = (\<lbrace>(d \<^bold>\<otimes> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<rbrace> \<cdot> ((\<lbrace>d\<rbrace> \<otimes> \<lbrace>e\<rbrace>) \<otimes> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot>
                               \<a>[\<lbrace>d\<rbrace> \<otimes> \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
              proof -
                have "\<lbrace>(d \<^bold>\<otimes> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<rbrace>
                           = (\<lbrace>d\<rbrace> \<otimes> \<lbrace>e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<otimes> \<lbrace>e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)\<rbrace>) \<cdot>
                              \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<rbrace>]"
                proof -
                  have "(d \<^bold>\<otimes> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)
                          = (d \<^bold>\<Down> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<^bold>\<rfloor>)) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[d, e, b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<^bold>]"
                    using b c e not_is_Tensor_TensorDiagE
                    by (cases "b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c") auto
                  also have "... = (d \<^bold>\<Down> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot>
                                   \<^bold>\<a>\<^bold>[d, e, b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<^bold>]"
                    using b c d e 1 TensorDiag_preserves_Diag Diagonalize_Diag by simp
                  also have "... = (d \<^bold>\<otimes> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot>
                                   \<^bold>\<a>\<^bold>[d, e, b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<^bold>]"
                    using b c d e 1 TensorDiag_preserves_Diag(1) red2_Diag not_is_Tensor_Unity
                    by (cases d, simp_all, cases "e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c", simp_all)
                  finally have "(d \<^bold>\<otimes> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c)
                                  = (d \<^bold>\<otimes> (e \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot> (d \<^bold>\<otimes> (e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c))) \<^bold>\<cdot>
                                    \<^bold>\<a>\<^bold>[d, e, b \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> c\<^bold>]"
                    by blast
                  thus ?thesis
                    using b c d e red2_in_Hom TensorDiag_in_Hom TensorDiag_preserves_Diag
                          TensorDiag_preserves_Ide
                    by simp
                qed
                thus ?thesis using d e b c by simp
              qed
              finally show ?thesis by simp
            qed
          qed
        qed
        thus ?thesis using assms(1) by blast
      qed
      ultimately show ?thesis by blast
    qed

    lemma coherent_Assoc_Ide:
    assumes "Ide a" and "Ide b" and "Ide c"
    shows "coherent \<^bold>\<a>\<^bold>[a, b, c\<^bold>]"
    proof -
      have a: "Ide a \<and> Arr a \<and> Dom a = a \<and> Cod a = a \<and>
               ide \<lbrace>a\<rbrace> \<and> ide \<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace> \<and> \<guillemotleft>\<lbrace>a\<^bold>\<down>\<rbrace> : \<lbrace>a\<rbrace> \<rightarrow> \<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace>\<guillemotright>"
        using assms Ide_implies_Arr Ide_in_Hom Diagonalize_preserves_Ide red_in_Hom by auto
      have b: "Ide b \<and> Arr b \<and> Dom b = b \<and> Cod b = b \<and>
               ide \<lbrace>b\<rbrace> \<and> ide \<lbrace>\<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace> \<and> \<guillemotleft>\<lbrace>b\<^bold>\<down>\<rbrace> : \<lbrace>b\<rbrace> \<rightarrow> \<lbrace>\<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace>\<guillemotright>"
        using assms Ide_implies_Arr Ide_in_Hom Diagonalize_preserves_Ide red_in_Hom by auto
      have c: "Ide c \<and> Arr c \<and> Dom c = c \<and> Cod c = c \<and>
               ide \<lbrace>c\<rbrace> \<and> ide \<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace> \<and> \<guillemotleft>\<lbrace>c\<^bold>\<down>\<rbrace> : \<lbrace>c\<rbrace> \<rightarrow> \<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>\<guillemotright>"
        using assms Ide_implies_Arr Ide_in_Hom Diagonalize_preserves_Ide red_in_Hom by auto
      have "\<lbrace>Cod \<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>\<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<rbrace>
              = (\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>)\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace> \<otimes> (\<lbrace>\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>)) \<cdot>
                 (\<lbrace>a\<^bold>\<down>\<rbrace> \<otimes> \<lbrace>b\<^bold>\<down>\<rbrace> \<otimes> \<lbrace>c\<^bold>\<down>\<rbrace>)) \<cdot> \<a>[\<lbrace>a\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
        using a b c red_in_Hom red2_in_Hom Diagonalize_in_Hom Diag_Diagonalize
              Diagonalize_preserves_Ide interchange Ide_in_Hom eval_red_Tensor
              comp_cod_arr [of "\<lbrace>a\<^bold>\<down>\<rbrace>"]
        by simp
      also have "... = ((\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>)\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace> \<otimes> \<lbrace>\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>)) \<cdot>
                        \<a>[\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace>, \<lbrace>\<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace>, \<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>]) \<cdot> ((\<lbrace>a\<^bold>\<down>\<rbrace> \<otimes> \<lbrace>b\<^bold>\<down>\<rbrace>) \<otimes> \<lbrace>c\<^bold>\<down>\<rbrace>)"
        using a b c red_in_Hom Diag_Diagonalize TensorDiag_preserves_Diag
               assoc_naturality [of "\<lbrace>a\<^bold>\<down>\<rbrace>" "\<lbrace>b\<^bold>\<down>\<rbrace>" "\<lbrace>c\<^bold>\<down>\<rbrace>"] comp_assoc
         by simp
      also have "... = (\<lbrace>(\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>b\<^bold>\<rfloor>) \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace> \<otimes> \<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>)) \<cdot>
                       ((\<lbrace>a\<^bold>\<down>\<rbrace> \<otimes> \<lbrace>b\<^bold>\<down>\<rbrace>) \<otimes> \<lbrace>c\<^bold>\<down>\<rbrace>)"
        using a b c Diag_Diagonalize Diagonalize_preserves_Ide coherence_key_fact by simp
      also have "... = \<lbrace>\<^bold>\<lfloor>\<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom \<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<^bold>\<down>\<rbrace>"
        using a b c red_in_Hom red2_in_Hom TensorDiag_preserves_Diag
              Diagonalize_preserves_Ide TensorDiag_preserves_Ide Diag_Diagonalize interchange
              eval_red_Tensor TensorDiag_assoc comp_cod_arr [of "\<lbrace>c\<^bold>\<down>\<rbrace>"]
              comp_cod_arr [of "\<lbrace>(\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>b\<^bold>\<rfloor>) \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>a\<^bold>\<down>\<rbrace> \<otimes> \<lbrace>b\<^bold>\<down>\<rbrace>) \<otimes> \<lbrace>c\<^bold>\<down>\<rbrace>)"]
              comp_assoc
        by simp
      finally show ?thesis by blast
    qed

    lemma coherent_Assoc'_Ide:
    assumes "Ide a" and "Ide b" and "Ide c"
    shows "coherent \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[a, b, c\<^bold>]"
    proof -
      have "Can \<^bold>\<a>\<^bold>[a, b, c\<^bold>]" using assms Ide_implies_Can by simp
      moreover have "\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[a, b, c\<^bold>] = Inv \<^bold>\<a>\<^bold>[a, b, c\<^bold>]"
        using assms Inv_Ide by simp
      ultimately show ?thesis
        using assms Ide_implies_Can coherent_Assoc_Ide Inv_Ide
              Can_implies_coherent_iff_coherent_Inv
        by metis
    qed

    text\<open>
      The next lemma implies coherence for the special case of a term that is the tensor
      of two diagonal arrows.
\<close>

    lemma eval_red2_naturality:
    assumes "Diag t" and "Diag u"
    shows "\<lbrace>Cod t \<^bold>\<Down> Cod u\<rbrace> \<cdot> (\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace>) = \<lbrace>t \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>Dom t \<^bold>\<Down> Dom u\<rbrace>"
    proof -
      have *: "\<And>t u. Diag (t \<^bold>\<otimes> u) \<Longrightarrow> arr \<lbrace>t\<rbrace> \<and> arr \<lbrace>u\<rbrace>"
        using Diag_implies_Arr by force
      have "t = \<^bold>\<I> \<Longrightarrow> ?thesis"
        using assms Diag_implies_Arr lunit_naturality [of "\<lbrace>u\<rbrace>"]
              Arr_implies_Ide_Dom Arr_implies_Ide_Cod comp_cod_arr
        by simp
      moreover have "t \<noteq> \<^bold>\<I> \<and> u = \<^bold>\<I> \<Longrightarrow> ?thesis"
        using assms Arr_implies_Ide_Dom Arr_implies_Ide_Cod
              Diag_implies_Arr Dom_preserves_Diag Cod_preserves_Diag
              eval_red2_Diag_Unity runit_naturality [of "\<lbrace>t\<rbrace>"]
        by simp
      moreover have "t \<noteq> \<^bold>\<I> \<and> u \<noteq> \<^bold>\<I> \<Longrightarrow> ?thesis"
        using assms * Arr_implies_Ide_Dom Arr_implies_Ide_Cod
              Diag_implies_Arr Dom_preserves_Diag Cod_preserves_Diag
        apply (induct t, simp_all)
      proof -
        fix f
        assume f: "C.arr f"
        assume "u \<noteq> \<^bold>\<I>"
        hence u: "u \<noteq> \<^bold>\<I> \<and>
                  Diag u \<and> Diag (Dom u) \<and> Diag (Cod u) \<and> Ide (Dom u) \<and> Ide (Cod u) \<and>
                  arr \<lbrace>u\<rbrace> \<and> arr \<lbrace>Dom u\<rbrace> \<and> arr \<lbrace>Cod u\<rbrace> \<and> ide \<lbrace>Dom u\<rbrace> \<and> ide \<lbrace>Cod u\<rbrace>"
          using assms(2) Diag_implies_Arr Dom_preserves_Diag Cod_preserves_Diag
                Arr_implies_Ide_Dom Arr_implies_Ide_Cod
          by simp
        hence 1: "Dom u \<noteq> \<^bold>\<I> \<and> Cod u \<noteq> \<^bold>\<I>" using u by (cases u, simp_all)
        show "\<lbrace>\<^bold>\<langle>C.cod f\<^bold>\<rangle> \<^bold>\<Down> Cod u\<rbrace> \<cdot> (V f \<otimes> \<lbrace>u\<rbrace>) = (V f \<otimes> \<lbrace>u\<rbrace>) \<cdot> \<lbrace>\<^bold>\<langle>C.dom f\<^bold>\<rangle> \<^bold>\<Down> Dom u\<rbrace>"
          using f u 1 Diag_implies_Arr red2_Diag comp_arr_dom comp_cod_arr by simp
        next
        fix v w
        assume I2: "\<lbrakk> w \<noteq> Unity; Diag w \<rbrakk> \<Longrightarrow>
                      \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace> \<cdot> (\<lbrace>w\<rbrace> \<otimes> \<lbrace>u\<rbrace>) = \<lbrace>w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>"
        assume "u \<noteq> \<^bold>\<I>"
        hence u: "u \<noteq> \<^bold>\<I> \<and> Arr u \<and> Arr (Dom u) \<and> Arr (Cod u) \<and>
                  Diag u \<and> Diag (Dom u) \<and> Diag (Cod u) \<and> Ide (Dom u) \<and> Ide (Cod u) \<and>
                  arr \<lbrace>u\<rbrace> \<and> arr \<lbrace>Dom u\<rbrace> \<and> arr \<lbrace>Cod u\<rbrace> \<and> ide \<lbrace>Dom u\<rbrace> \<and> ide \<lbrace>Cod u\<rbrace>"
          using assms(2) Diag_implies_Arr Dom_preserves_Diag Cod_preserves_Diag
                Arr_implies_Ide_Dom Arr_implies_Ide_Cod
          by simp
        assume vw: "Diag (v \<^bold>\<otimes> w)"
        let ?f = "un_Prim v"
        have "v = \<^bold>\<langle>?f\<^bold>\<rangle> \<and> C.arr ?f"
          using vw by (metis Diag_TensorE(1) Diag_TensorE(2))
        hence "Arr v \<and> v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<and> C.arr ?f \<and> Diag v" by (cases v; simp)
        hence v: "v = \<^bold>\<langle>?f\<^bold>\<rangle> \<and> C.arr ?f \<and> Arr v \<and> Ide (Dom v) \<and> Ide (Cod v) \<and> Diag v \<and>
                  Diag (Dom v) \<and> arr \<lbrace>v\<rbrace> \<and> arr \<lbrace>Dom v\<rbrace> \<and> arr \<lbrace>Cod v\<rbrace> \<and>
                  ide \<lbrace>Dom v\<rbrace> \<and> ide \<lbrace>Cod v\<rbrace>"
          by (cases v, simp_all)
        have "Diag w \<and> w \<noteq> \<^bold>\<I>"
          using vw v by (metis Diag.simps(3))
        hence w: "w \<noteq> \<^bold>\<I> \<and> Arr w \<and> Arr (Dom w) \<and> Arr (Cod w) \<and>
                  Diag w \<and> Diag (Dom w) \<and> Diag (Cod w) \<and>
                  Ide (Dom w) \<and> Ide (Cod w) \<and>
                  arr \<lbrace>w\<rbrace> \<and> arr \<lbrace>Dom w\<rbrace> \<and> arr \<lbrace>Cod w\<rbrace> \<and> ide \<lbrace>Dom w\<rbrace> \<and> ide \<lbrace>Cod w\<rbrace>"
          using vw * Diag_implies_Arr Dom_preserves_Diag Cod_preserves_Diag Arr_implies_Ide_Dom
                Arr_implies_Ide_Cod ide_eval_Ide Ide_implies_Arr Ide_in_Hom
          by simp
        show "\<lbrace>(Cod v \<^bold>\<otimes> Cod w) \<^bold>\<Down> Cod u\<rbrace> \<cdot> ((\<lbrace>v\<rbrace> \<otimes> \<lbrace>w\<rbrace>) \<otimes> \<lbrace>u\<rbrace>)
                = \<lbrace>(v \<^bold>\<otimes> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>(Dom v \<^bold>\<otimes> Dom w) \<^bold>\<Down> Dom u\<rbrace>"
        proof -
          have u': "Dom u \<noteq> \<^bold>\<I> \<and> Cod u \<noteq> \<^bold>\<I>" using u by (cases u) simp_all
          have w':  "Dom w \<noteq> \<^bold>\<I> \<and> Cod w \<noteq> \<^bold>\<I>" using w by (cases w) simp_all
          have D: "Diag (Dom v \<^bold>\<otimes> (Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u))"
          proof -
            have "Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u \<noteq> \<^bold>\<I>"
              using u u' w w' not_is_Tensor_TensorDiagE by blast
            moreover have "Diag (Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u)"
              using u w TensorDiag_preserves_Diag by simp
            moreover have "Dom v = \<^bold>\<langle>C.dom ?f\<^bold>\<rangle>"
              using v by (cases v, simp_all)
            ultimately show ?thesis
              using u v w TensorDiag_preserves_Diag by auto
          qed
          have C: "Diag (Cod v \<^bold>\<otimes> (Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u))"
          proof -
            have "Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u \<noteq> \<^bold>\<I>"
              using u u' w w' not_is_Tensor_TensorDiagE by blast
            moreover have "Diag (Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u)"
              using u w TensorDiag_preserves_Diag by simp
            moreover have "Cod v = \<^bold>\<langle>C.cod ?f\<^bold>\<rangle>"
              using v by (cases v, simp_all)
            ultimately show ?thesis
              using u v w by (cases "Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u", simp_all)
          qed
          have "\<lbrace>(Cod v \<^bold>\<otimes> Cod w) \<^bold>\<Down> Cod u\<rbrace> \<cdot> ((\<lbrace>v\<rbrace> \<otimes> \<lbrace>w\<rbrace>) \<otimes> \<lbrace>u\<rbrace>)
                  = (\<lbrace>Cod v \<^bold>\<Down> (Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u)\<rbrace> \<cdot> (\<lbrace>Cod v\<rbrace> \<otimes> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>) \<cdot>
                    \<a>[\<lbrace>Cod v\<rbrace>, \<lbrace>Cod w\<rbrace>, \<lbrace>Cod u\<rbrace>]) \<cdot> ((\<lbrace>v\<rbrace> \<otimes> \<lbrace>w\<rbrace>) \<otimes> \<lbrace>u\<rbrace>)"
          proof -
            have "(Cod v \<^bold>\<otimes> Cod w) \<^bold>\<Down> Cod u
                    = (Cod v \<^bold>\<Down> (Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>)) \<^bold>\<cdot> (Cod v \<^bold>\<otimes> Cod w \<^bold>\<Down> Cod u) \<^bold>\<cdot>
                      \<^bold>\<a>\<^bold>[Cod v, Cod w, Cod u\<^bold>]"
              using u v w by (cases u, simp_all)
            hence "\<lbrace>(Cod v \<^bold>\<otimes> Cod w) \<^bold>\<Down> Cod u\<rbrace>
                     = \<lbrace>Cod v \<^bold>\<Down> (Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u)\<rbrace> \<cdot> (\<lbrace>Cod v\<rbrace> \<otimes> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>) \<cdot>
                       \<a>[\<lbrace>Cod v\<rbrace>, \<lbrace>Cod w\<rbrace>, \<lbrace>Cod u\<rbrace>]"
              using u v w by simp
            thus ?thesis by argo
          qed
          also have "... = ((\<lbrace>Cod v\<rbrace> \<otimes> \<lbrace>Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u\<rbrace>) \<cdot> (\<lbrace>Cod v\<rbrace> \<otimes> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>) \<cdot>
                            \<a>[\<lbrace>Cod v\<rbrace>, \<lbrace>Cod w\<rbrace>, \<lbrace>Cod u\<rbrace>]) \<cdot> ((\<lbrace>v\<rbrace> \<otimes> \<lbrace>w\<rbrace>) \<otimes> \<lbrace>u\<rbrace>)"
            using u v w C red2_Diag by simp
          also have "... = ((\<lbrace>Cod v\<rbrace> \<otimes> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>) \<cdot> \<a>[\<lbrace>Cod v\<rbrace>, \<lbrace>Cod w\<rbrace>, \<lbrace>Cod u\<rbrace>]) \<cdot>
                           ((\<lbrace>v\<rbrace> \<otimes> \<lbrace>w\<rbrace>) \<otimes> \<lbrace>u\<rbrace>)"
          proof -
            have "(\<lbrace>Cod v\<rbrace> \<otimes> \<lbrace>Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u\<rbrace>) \<cdot> (\<lbrace>Cod v\<rbrace> \<otimes> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>)
                     = \<lbrace>Cod v\<rbrace> \<otimes> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>"
              using u v w comp_cod_arr red2_in_Hom by simp
            moreover have
                "seq (\<lbrace>Cod v\<rbrace> \<otimes> \<lbrace>Cod w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Cod u\<rbrace>) (\<lbrace>Cod v\<rbrace> \<otimes> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>)"
              using u v w red2_in_Hom TensorDiag_in_Hom Ide_in_Hom by simp
            moreover have "seq (\<lbrace>Cod v\<rbrace> \<otimes> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>) \<a>[\<lbrace>Cod v\<rbrace>, \<lbrace>Cod w\<rbrace>, \<lbrace>Cod u\<rbrace>]"
              using u v w red2_in_Hom by simp
            ultimately show ?thesis
              using u v w comp_reduce by presburger
          qed
          also have
            "... = (\<lbrace>v\<rbrace> \<otimes> \<lbrace>w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot> \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
            using u v w I2 red2_in_Hom TensorDiag_in_Hom interchange comp_reduce
                  assoc_naturality [of "\<lbrace>v\<rbrace>" "\<lbrace>w\<rbrace>" "\<lbrace>u\<rbrace>"] comp_cod_arr comp_assoc
            by simp
          also have "... = (\<lbrace>v\<rbrace> \<otimes> \<lbrace>w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<rbrace>) \<cdot> (\<lbrace>Dom v\<rbrace> \<otimes> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot>
                           \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
            using u v w red2_in_Hom TensorDiag_in_Hom interchange comp_reduce comp_arr_dom
            by simp
          also have "... = \<lbrace>v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<rbrace> \<cdot> (\<lbrace>Dom v\<rbrace> \<otimes> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot>
                           \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
            using u u' v w not_is_Tensor_TensorDiagE TensorDiag_Prim [of "w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u" ?f]
            by force
          also have "... = \<lbrace>v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>Dom v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u\<rbrace> \<cdot>
                          (\<lbrace>Dom v\<rbrace> \<otimes> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot> \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
          proof -
            have
              "\<lbrace>v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<rbrace> \<cdot> (\<lbrace>Dom v\<rbrace> \<otimes> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot> \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>] =
               (\<lbrace>v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>Dom v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u\<rbrace>) \<cdot>
               (\<lbrace>Dom v\<rbrace> \<otimes> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot> \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
              using u v w comp_arr_dom TensorDiag_in_Hom TensorDiag_preserves_Diag by simp
            also have "... = \<lbrace>v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>Dom v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u\<rbrace> \<cdot>
                            (\<lbrace>Dom v\<rbrace> \<otimes> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot> \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
              using comp_assoc by simp
            finally show ?thesis by blast
          qed
          also have "... = \<lbrace>(v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> w) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>(Dom v \<^bold>\<otimes> Dom w) \<^bold>\<Down> Dom u\<rbrace>"
          proof -
            have
              "\<lbrace>(Dom v \<^bold>\<otimes> Dom w) \<^bold>\<Down> Dom u\<rbrace>
                     = \<lbrace>Dom v \<^bold>\<Down> (Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u)\<rbrace> \<cdot> (\<lbrace>Dom v\<rbrace> \<otimes> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot>
                       \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
            proof -
              have "(Dom v \<^bold>\<otimes> Dom w) \<^bold>\<Down> Dom u
                       = (Dom v \<^bold>\<Down> (Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom u\<^bold>\<rfloor>)) \<^bold>\<cdot> (Dom v \<^bold>\<otimes> (Dom w \<^bold>\<Down> Dom u)) \<^bold>\<cdot>
                         \<^bold>\<a>\<^bold>[Dom v, Dom w, Dom u\<^bold>]"
                using u u' v w red2_in_Hom TensorDiag_in_Hom tensor_in_hom Ide_in_Hom
                by (cases u, simp_all)
              thus ?thesis
                using u v w red2_in_Hom by simp
            qed
            also have
              "... = \<lbrace>Dom v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u\<rbrace> \<cdot> (\<lbrace>Dom v\<rbrace> \<otimes> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot>
                             \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
              using D TensorDiag_Diag red2_Diag by simp
            finally have
              "\<lbrace>(Dom v \<^bold>\<otimes> Dom w) \<^bold>\<Down> Dom u\<rbrace>
                   = \<lbrace>Dom v \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> Dom u\<rbrace> \<cdot> (\<lbrace>Dom v\<rbrace> \<otimes> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot>
                     \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
              by blast
            thus ?thesis
              using assms v w TensorDiag_assoc by auto
          qed
          finally show ?thesis
            using vw TensorDiag_Diag by simp
        qed
      qed
      ultimately show ?thesis by blast
    qed

    lemma Tensor_preserves_coherent:
    assumes "Arr t" and "Arr u" and "coherent t" and "coherent u"
    shows "coherent (t \<^bold>\<otimes> u)"
    proof -
      have t: "Arr t \<and> Ide (Dom t) \<and> Ide (Cod t) \<and> Ide \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<and>
               arr \<lbrace>t\<rbrace> \<and> arr \<lbrace>Dom t\<rbrace> \<and> ide \<lbrace>Dom t\<rbrace> \<and> arr \<lbrace>Cod t\<rbrace> \<and> ide \<lbrace>Cod t\<rbrace>"
        using assms Arr_implies_Ide_Dom Arr_implies_Ide_Cod Diagonalize_preserves_Ide
        by auto
      have u: "Arr u \<and> Ide (Dom u) \<and> Ide (Cod u) \<and> Ide \<^bold>\<lfloor>Dom u\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>Cod u\<^bold>\<rfloor> \<and>
               arr \<lbrace>u\<rbrace> \<and> arr \<lbrace>Dom u\<rbrace> \<and> ide \<lbrace>Dom u\<rbrace> \<and> arr \<lbrace>Cod u\<rbrace> \<and> ide \<lbrace>Cod u\<rbrace>"
        using assms Arr_implies_Ide_Dom Arr_implies_Ide_Cod Diagonalize_preserves_Ide
        by auto
      have "\<lbrace>Cod (t \<^bold>\<otimes> u)\<^bold>\<down>\<rbrace> \<cdot> (\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace>)
              = (\<lbrace>\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<otimes> \<lbrace>Cod u\<^bold>\<down>\<rbrace>)) \<cdot> (\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace>)"
        using t u eval_red_Tensor by simp
      also have "... = \<lbrace>\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<otimes> \<lbrace>Cod u\<^bold>\<down>\<rbrace>) \<cdot> (\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace>)"
        using comp_assoc by simp
      also have "... = \<lbrace>\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<otimes> \<lbrace>\<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace>) \<cdot> (\<lbrace>Dom t\<^bold>\<down>\<rbrace> \<otimes> \<lbrace>Dom u\<^bold>\<down>\<rbrace>)"
        using assms t u Diagonalize_in_Hom red_in_Hom interchange by simp
      also have "... = (\<lbrace>\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<otimes> \<lbrace>\<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace>)) \<cdot> (\<lbrace>Dom t\<^bold>\<down>\<rbrace> \<otimes> \<lbrace>Dom u\<^bold>\<down>\<rbrace>)"
        using comp_assoc by simp
      also have "... = (\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Dom u\<^bold>\<rfloor>\<rbrace>) \<cdot> (\<lbrace>Dom t\<^bold>\<down>\<rbrace> \<otimes> \<lbrace>Dom u\<^bold>\<down>\<rbrace>)"
        using assms t u Diag_Diagonalize Diagonalize_in_Hom
              eval_red2_naturality [of "Diagonalize t" "Diagonalize u"]
        by simp
      also have "... = \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Dom u\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>Dom t\<^bold>\<down>\<rbrace> \<otimes> \<lbrace>Dom u\<^bold>\<down>\<rbrace>)"
        using comp_assoc by simp
      also have "... = \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>(Dom t \<^bold>\<otimes> Dom u)\<^bold>\<down>\<rbrace>"
        using t u eval_red_Tensor by simp
      finally have "\<lbrace>Cod (t \<^bold>\<otimes> u)\<^bold>\<down>\<rbrace> \<cdot> (\<lbrace>t\<rbrace> \<otimes> \<lbrace>u\<rbrace>) = \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>(Dom t \<^bold>\<otimes> Dom u)\<^bold>\<down>\<rbrace>"
        by blast
      thus ?thesis using t u by simp
    qed

    lemma Comp_preserves_coherent:
    assumes "Arr t" and "Arr u" and "Dom t = Cod u"
    and "coherent t" and "coherent u"
    shows "coherent (t \<^bold>\<cdot> u)"
    proof -
      have t: "Arr t \<and> Ide (Dom t) \<and> Ide (Cod t) \<and> Ide \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<and>
               arr \<lbrace>t\<rbrace> \<and> arr \<lbrace>Dom t\<rbrace> \<and> ide \<lbrace>Dom t\<rbrace> \<and> arr \<lbrace>Cod t\<rbrace> \<and> ide \<lbrace>Cod t\<rbrace>"
        using assms Arr_implies_Ide_Dom Arr_implies_Ide_Cod Diagonalize_preserves_Ide
        by auto
      have u: "Arr u \<and> Ide (Dom u) \<and> Ide (Cod u) \<and> Ide \<^bold>\<lfloor>Dom u\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>Cod u\<^bold>\<rfloor> \<and>
               arr \<lbrace>u\<rbrace> \<and> arr \<lbrace>Dom u\<rbrace> \<and> ide \<lbrace>Dom u\<rbrace> \<and> arr \<lbrace>Cod u\<rbrace> \<and> ide \<lbrace>Cod u\<rbrace>"
        using assms Arr_implies_Ide_Dom Arr_implies_Ide_Cod Diagonalize_preserves_Ide
        by auto
      have "\<lbrace>Cod (t \<^bold>\<cdot> u)\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t \<^bold>\<cdot> u\<rbrace> = \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
        using t u by simp
      also have "... = (\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t\<rbrace>) \<cdot> \<lbrace>u\<rbrace>"
      proof -
        (* TODO: I still haven't figured out how to do this without spoon-feeding it. *)
        have "seq \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<lbrace>t\<rbrace>"
          using assms t red_in_Hom by (intro seqI, auto)
        moreover have "seq \<lbrace>t\<rbrace> \<lbrace>u\<rbrace>"
          using assms t u by auto
        ultimately show ?thesis using comp_assoc by auto
      qed
      also have "... = \<lbrace>\<^bold>\<lfloor>t \<^bold>\<cdot> u\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom (t \<^bold>\<cdot> u)\<^bold>\<down>\<rbrace>"
        using t u assms red_in_Hom Diag_Diagonalize comp_assoc
        by (simp add: Diag_implies_Arr eval_CompDiag)
      finally show "coherent (t \<^bold>\<cdot> u)" by blast
    qed

    text\<open>
      The main result: ``Every formal arrow is coherent.''
\<close>

    theorem coherence:
    assumes "Arr t"
    shows "coherent t"
    proof -
      have "Arr t \<Longrightarrow> coherent t"
      proof (induct t)
        fix u v
        show "\<lbrakk> Arr u \<Longrightarrow> coherent u; Arr v \<Longrightarrow> coherent v \<rbrakk> \<Longrightarrow> Arr (u \<^bold>\<otimes> v)
                  \<Longrightarrow> coherent (u \<^bold>\<otimes> v)"
          using Tensor_preserves_coherent by simp
        show "\<lbrakk> Arr u \<Longrightarrow> coherent u; Arr v \<Longrightarrow> coherent v \<rbrakk> \<Longrightarrow> Arr (u \<^bold>\<cdot> v)
                  \<Longrightarrow> coherent (u \<^bold>\<cdot> v)"
          using Comp_preserves_coherent by simp
        next
        show "coherent \<^bold>\<I>" by simp
        fix f
        show "Arr \<^bold>\<langle>f\<^bold>\<rangle> \<Longrightarrow> coherent \<^bold>\<langle>f\<^bold>\<rangle>" by simp
        next
        fix t
        assume I: "Arr t \<Longrightarrow> coherent t"
        show Lunit: "Arr \<^bold>\<l>\<^bold>[t\<^bold>] \<Longrightarrow> coherent \<^bold>\<l>\<^bold>[t\<^bold>]"
          using I Arr_implies_Ide_Dom coherent_Lunit_Ide Ide_in_Hom Ide_implies_Arr
                Comp_preserves_coherent [of t "\<^bold>\<l>\<^bold>[Dom t\<^bold>]"] Diagonalize_Comp_Arr_Dom \<ll>_ide_simp
          by auto
        show Runit: "Arr \<^bold>\<r>\<^bold>[t\<^bold>] \<Longrightarrow> coherent \<^bold>\<r>\<^bold>[t\<^bold>]"
          using I Arr_implies_Ide_Dom coherent_Runit_Ide Ide_in_Hom Ide_implies_Arr
                Comp_preserves_coherent [of t "\<^bold>\<r>\<^bold>[Dom t\<^bold>]"] Diagonalize_Comp_Arr_Dom \<rho>_ide_simp
          by auto
        show "Arr \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> coherent \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
        proof -
          assume "Arr \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
          hence t: "Arr t" by simp
          have "coherent (\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t)"
            using t I Arr_implies_Ide_Cod coherent_Lunit'_Ide Ide_in_Hom
                  Comp_preserves_coherent [of "\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>]" t]
            by fastforce
          thus ?thesis
            using t Arr_implies_Ide_Cod Ide_implies_Arr Ide_in_Hom Diagonalize_Comp_Cod_Arr
                  eval_in_hom \<ll>'.is_natural_2 [of "\<lbrace>t\<rbrace>"]
            by force
        qed
        show "Arr \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> coherent \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
        proof -
          assume "Arr \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
          hence t: "Arr t" by simp
          have "coherent (\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t)"
            using t I Arr_implies_Ide_Cod coherent_Runit'_Ide Ide_in_Hom
                  Comp_preserves_coherent [of "\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>]" t]
            by fastforce
          thus ?thesis
            using t Arr_implies_Ide_Cod Ide_implies_Arr Ide_in_Hom Diagonalize_Comp_Cod_Arr
                  eval_in_hom \<rho>'.is_natural_2 [of "\<lbrace>t\<rbrace>"]
            by force
        qed
        next
        fix t u v
        assume I1: "Arr t \<Longrightarrow> coherent t"
        assume I2: "Arr u \<Longrightarrow> coherent u"
        assume I3: "Arr v \<Longrightarrow> coherent v"
        show "Arr \<^bold>\<a>\<^bold>[t, u, v\<^bold>] \<Longrightarrow> coherent \<^bold>\<a>\<^bold>[t, u, v\<^bold>]"
        proof -
          assume tuv: "Arr \<^bold>\<a>\<^bold>[t, u, v\<^bold>]"
          have t: "Arr t" using tuv by simp
          have u: "Arr u" using tuv by simp
          have v: "Arr v" using tuv by simp
          have "coherent ((t \<^bold>\<otimes> u \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>])"
          proof -
            have "Arr (t \<^bold>\<otimes> u \<^bold>\<otimes> v) \<and> coherent (t \<^bold>\<otimes> u \<^bold>\<otimes> v)"
            proof
              have 1: "Arr t \<and> coherent t" using t I1 by simp
              have 2: "Arr (u \<^bold>\<otimes> v) \<and> coherent (u \<^bold>\<otimes> v)"
                using u v I2 I3 Tensor_preserves_coherent by force
              show "Arr (t \<^bold>\<otimes> u \<^bold>\<otimes> v) " using 1 2 by simp
              show "coherent (t \<^bold>\<otimes> u \<^bold>\<otimes> v)"
                using 1 2 Tensor_preserves_coherent by blast
            qed
            moreover have "Arr \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v Arr_implies_Ide_Dom by simp
            moreover have "coherent \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v Arr_implies_Ide_Dom coherent_Assoc_Ide by blast
            moreover have "Dom (t \<^bold>\<otimes> u \<^bold>\<otimes> v) = Cod \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v Arr_implies_Ide_Dom Ide_in_Hom by simp
            ultimately show ?thesis
              using t u v Arr_implies_Ide_Dom Ide_implies_Arr
                    Comp_preserves_coherent [of "t \<^bold>\<otimes> u \<^bold>\<otimes> v" "\<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]"]
              by blast
          qed
          moreover have "Par \<^bold>\<a>\<^bold>[t, u, v\<^bold>] ((t \<^bold>\<otimes> u \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>])"
            using t u v Arr_implies_Ide_Dom Ide_implies_Arr Ide_in_Hom by simp
          moreover have "\<^bold>\<lfloor>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>(t \<^bold>\<otimes> u \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]\<^bold>\<rfloor>"
          proof -
            have "(\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>
                     = (\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> ((\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom u\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom v\<^bold>\<rfloor>)"
            proof -
              have 1: "Diag \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> Diag \<^bold>\<lfloor>u\<^bold>\<rfloor> \<and> Diag \<^bold>\<lfloor>v\<^bold>\<rfloor> \<and>
                       Dom \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<and> Dom \<^bold>\<lfloor>u\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom u\<^bold>\<rfloor> \<and> Dom \<^bold>\<lfloor>v\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom v\<^bold>\<rfloor>"
                using t u v Diag_Diagonalize by blast
              moreover have "Diag (\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>)"
                using 1 TensorDiag_preserves_Diag(1) by blast
              moreover have "\<And>t. Arr t \<Longrightarrow> \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
                using t Diagonalize_Comp_Arr_Dom by simp
              moreover have "Dom \<^bold>\<lfloor>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor>"
                using Diag_Diagonalize tuv by blast
              ultimately show ?thesis
                using t u v tuv 1 TensorDiag_assoc TensorDiag_preserves_Diag(2)
                by (metis (no_types) Diagonalize.simps(9))
            qed
            thus ?thesis
              using t u v Diagonalize_Comp_Arr_Dom CompDiag_TensorDiag Diag_Diagonalize
              by simp
          qed
          moreover have "\<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> = \<lbrace>(t \<^bold>\<otimes> u \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]\<rbrace>"
            using t u v Arr_implies_Ide_Dom Ide_implies_Arr \<alpha>_simp [of "\<lbrace>t\<rbrace>" "\<lbrace>u\<rbrace>" "\<lbrace>v\<rbrace>"]
            by simp
          ultimately show "coherent \<^bold>\<a>\<^bold>[t, u, v\<^bold>]" by argo
        qed
        show "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] \<Longrightarrow> coherent \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]"
        proof -
          assume tuv: "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]"
          have t: "Arr t" using tuv by simp
          have u: "Arr u" using tuv by simp
          have v: "Arr v" using tuv by simp
          have "coherent (((t \<^bold>\<otimes> u) \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>])"
          proof -
            have "Arr ((t \<^bold>\<otimes> u) \<^bold>\<otimes> v) \<and> coherent ((t \<^bold>\<otimes> u) \<^bold>\<otimes> v)"
            proof
              have 1: "Arr v \<and> coherent v" using v I3 by simp
              have 2: "Arr (t \<^bold>\<otimes> u) \<and> coherent (t \<^bold>\<otimes> u)"
                using t u I1 I2 Tensor_preserves_coherent by force
              show "Arr ((t \<^bold>\<otimes> u) \<^bold>\<otimes> v)" using 1 2 by simp
              show "coherent ((t \<^bold>\<otimes> u) \<^bold>\<otimes> v)"
                using 1 2 Tensor_preserves_coherent by blast
            qed
            moreover have "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v Arr_implies_Ide_Dom by simp
            moreover have "coherent \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v Arr_implies_Ide_Dom coherent_Assoc'_Ide by blast
            moreover have "Dom ((t \<^bold>\<otimes> u) \<^bold>\<otimes> v) = Cod \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v Arr_implies_Ide_Dom Ide_in_Hom by simp
            ultimately show ?thesis
              using t u v Arr_implies_Ide_Dom Ide_implies_Arr
                    Comp_preserves_coherent [of "((t \<^bold>\<otimes> u) \<^bold>\<otimes> v)" "\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]"]
              by metis
          qed
          moreover have "Par \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] (((t \<^bold>\<otimes> u) \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>])"
            using t u v Arr_implies_Ide_Dom Ide_implies_Arr Ide_in_Hom by simp
          moreover have "\<^bold>\<lfloor>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>((t \<^bold>\<otimes> u) \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]\<^bold>\<rfloor>"
            using t u v Diagonalize_Comp_Arr_Dom CompDiag_TensorDiag Diag_Diagonalize
                  TensorDiag_assoc TensorDiag_preserves_Diag TensorDiag_in_Hom
                  CompDiag_Diag_Dom [of "(\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<otimes>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>"]
            by simp
          moreover have "\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = \<lbrace>((t \<^bold>\<otimes> u) \<^bold>\<otimes> v) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]\<rbrace>"
            using t u v Arr_implies_Ide_Dom Ide_implies_Arr eval_in_hom comp_cod_arr
                  \<alpha>'.is_natural_1 \<alpha>'_simp
            by simp
          ultimately show "coherent \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]" by argo
        qed
      qed
      thus ?thesis using assms by blast
    qed

    text\<open>
      MacLane \cite{MacLane71} says: ``A coherence theorem asserts `Every diagram commutes',''
      but that is somewhat misleading.  A coherence theorem provides some kind of hopefully
      useful way of distinguishing diagrams that definitely commute from diagrams that might not.
      The next result expresses coherence for monoidal categories in this way.
      As the hypotheses can be verified algorithmically (using the functions @{term Dom},
      @{term Cod}, @{term Arr}, and @{term Diagonalize}) if we are given an oracle for equality
      of arrows in \<open>C\<close>, the result provides a decision procedure, relative to \<open>C\<close>,
      for the word problem for the free monoidal category generated by \<open>C\<close>.
\<close>

    corollary eval_eqI:
    assumes "Par t u" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
    shows "\<lbrace>t\<rbrace> = \<lbrace>u\<rbrace>"
      using assms coherence canonical_factorization by simp

    text\<open>
      Our final corollary expresses coherence in a more ``MacLane-like'' fashion:
      parallel canonical arrows are equivalent under evaluation.
\<close>

    corollary maclane_coherence:
    assumes "Par t u" and "Can t" and "Can u"
    shows "\<lbrace>t\<rbrace> = \<lbrace>u\<rbrace>"
    proof (intro eval_eqI)
      show "Par t u" by fact
      show "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
      proof -
        have "Ide \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>u\<^bold>\<rfloor> \<and> Par \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>"
          using assms eval_eqI Ide_Diagonalize_Can Diagonalize_in_Hom by simp
        thus ?thesis using Ide_in_Hom by auto
      qed
    qed

  end

end

