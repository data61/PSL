(*  Title:       PreBicategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

  text \<open>
    The objective of this section is to construct a formalization of bicategories that is
    compatible with our previous formulation of categories \cite{Category3-AFP}
    and that permits us to carry over unchanged as much of the work done on categories as possible.
    For these reasons, we conceive of a bicategory in what might be regarded as a somewhat
    unusual fashion.  Rather than a traditional development, which would typically define
    a bicategory to be essentially ``a `category' whose homs themselves have the structure
    of categories,'' here we regard a bicategory as ``a (vertical) category that has been
    equipped with a suitable (horizontal) weak composition.''  Stated another way, we think
    of a bicategory as a generalization of a monoidal category in which the tensor product is
    a partial operation, rather than a total one.  Our definition of bicategory can thus
    be summarized as follows: a bicategory is a (vertical) category that has been equipped
    with idempotent endofunctors \<open>src\<close> and \<open>trg\<close> that assign to each arrow its ``source''
    and ``target'' subject to certain commutativity constraints,
    a partial binary operation \<open>\<star>\<close> of horizontal composition that is suitably functorial on
    the ``hom-categories'' determined by the assignment of sources and targets,
    ``associativity'' isomorphisms \<open>\<guillemotleft>\<a>[f, g, h] : (f \<star> g) \<star> h \<Rightarrow> f \<star> (g \<star> h)\<guillemotright>\<close> for each horizontally
    composable triple of vertical identities \<open>f\<close>, \<open>g\<close>, \<open>h\<close>, subject to the usual naturality
    and coherence conditions, and for each ``object'' \<open>a\<close> (defined to be an arrow that is
    its own source and target) a ``unit isomorphism'' \<open>\<guillemotleft>\<i>[a] : a \<star> a \<Rightarrow> a\<guillemotright>\<close>.
    As is the case for monoidal categories, the unit isomorphisms and associator isomorphisms
    together enable a canonical definition of left and right ``unit'' isomorphisms
    \<open>\<guillemotleft>\<l>[f] : a \<star> f \<Rightarrow> f\<guillemotright>\<close> and \<open>\<guillemotleft>\<r>[f] : f \<star> a \<Rightarrow> f\<guillemotright>\<close> when \<open>f\<close> is a vertical identity
    horizontally composable on the left or right by \<open>a\<close>, and it can be shown that these are
    the components of natural transformations.

    The definition of bicategory just sketched shares with a more traditional version the
    requirement that assignments of source and target are given as basic data, and these
    assignments determine horizontal composability in the sense that arrows \<open>\<mu>\<close> and \<open>\<nu>\<close>
    are composable if the chosen source of \<open>\<mu>\<close> coincides with the chosen target of \<open>\<nu>\<close>.
    Thus it appears, at least on its face, that composability of arrows depends on an assignment
    of sources and targets.  We are interested in establishing whether this is essential or
    whether bicategories can be formalized in a completely ``object-free'' fashion.

    It turns out that we can obtain such an object-free formalization through a rather direct
    generalization of the approach we used in the formalization of categories.
    Specifically, we define a \emph{weak composition} to be a partial binary operation \<open>\<star>\<close>
    on the arrow type of a ``vertical'' category \<open>V\<close>, such that the domain of definition of this
    operation is itself a category (of ``horizontally composable pairs of arrows''),
    the operation is functorial, and it is subject to certain matching conditions which include
    those satisfied by a category.
    From the axioms for a weak composition we can prove the existence of ``hom-categories'',
    which are subcategories of \<open>V\<close> consisting of arrows horizontally composable on the
    left or right by a specified vertical identity.
    A \emph{weak unit} is defined to be a vertical identity \<open>a\<close> such that \<open>a \<star> a \<cong> a\<close>
    and is such that the mappings \<open>a \<star> \<hyphen>\<close> and \<open>\<hyphen> \<star> a\<close> are fully faithful endofunctors
    of the subcategories of \<open>V\<close> consisting of the arrows for which they are defined.
    We define the \emph{sources} of an arrow \<open>\<mu>\<close> to be the weak units that are horizontally
    composable with \<open>\<mu>\<close> on the right, and the \emph{targets} of \<open>\<mu>\<close> to be the weak units
    that are horizontally composable with \<open>\<mu>\<close> on the left.
    An \emph{associative weak composition} is defined to be a weak composition that is equipped
    with ``associator'' isomorphisms \<open>\<guillemotleft>\<a>[f, g, h] : (f \<star> g) \<star> h \<Rightarrow> f \<star> (g \<star> h)\<guillemotright>\<close> for horizontally
    composable vertical identities \<open>f\<close>, \<open>g\<close>, \<open>h\<close>, subject to the usual naturality and coherence
    conditions.
    A \emph{prebicategory} is defined to be an associative weak composition for which every
    arrow has a source and a target.  We show that the sets of sources and targets of each
    arrow in a prebicategory is an isomorphism class of weak units, and that horizontal
    composability of arrows \<open>\<mu>\<close> and \<open>\<nu>\<close> is characterized by the set of sources of \<open>\<mu>\<close> being
    equal to the set of targets of \<open>\<nu>\<close>.

    We show that prebicategories are essentially ``bicategories without objects''.
    Given a prebicategory, we may choose an arbitrary representative of each
    isomorphism class of weak units and declare these to be ``objects''
    (this is analogous to choosing a particular unit object in a monoidal category).
    For each object we may choose a particular \emph{unit isomorphism} \<open>\<guillemotleft>\<i>[a] : a \<star> a \<Rightarrow> a\<guillemotright>\<close>.
    This choice, together with the associator isomorphisms, enables a canonical definition
    of left and right unit isomorphisms \<open>\<guillemotleft>\<l>[f] : a \<star> f \<Rightarrow> f\<guillemotright>\<close> and \<open>\<guillemotleft>\<r>[f] : f \<star> a \<Rightarrow> f\<guillemotright>\<close>
    when \<open>f\<close> is a vertical identity horizontally composable on the left or right by \<open>a\<close>,
    and it can be shown that these are the components of natural isomorphisms.
    We may then define ``the source'' of an arrow to be the chosen representative of the
    set of its sources and ``the target'' to be the chosen representative of the set of its
    targets.  We show that the resulting structure is a bicategory, in which horizontal
    composability as given by the weak composition coincides with the ``syntactic'' version
    determined by the chosen sources and targets.
    Conversely, a bicategory determines a prebicategory, essentially by forgetting
    the sources, targets and unit isomorphisms.
    These results make it clear that the assignment of sources and targets to arrows in
    a bicategory is basically a convenience and that horizontal composability of arrows
    is not dependent on a particular choice.
\<close>

theory Prebicategory
imports Category3.EquivalenceOfCategories Category3.Subcategory IsomorphismClass
begin

  section "Weak Composition"

  text \<open>
    In this section we define a locale \<open>weak_composition\<close>, which formalizes a functorial
    operation of ``horizontal'' composition defined on an underlying ``vertical'' category.
    The definition is expressed without the presumption of the existence of any sort
    of ``objects'' that determine horizontal composability.  Rather, just as we did
    in showing that the @{locale partial_magma} locale supported the definition of ``identity
    arrow'' as a kind of unit for vertical composition which ultimately served as a basis
    for the definition of ``domain'' and ``codomain'' of an arrow, here we show that the
    \<open>weak_composition\<close> locale supports a definition of \emph{weak unit} for horizontal
    composition which can ultimately be used to define the \emph{sources} and \emph{targets}
    of an arrow with respect to horizontal composition.
    In particular, the definition of weak composition involves axioms that relate horizontal
    and vertical composability.  As a consequence of these axioms, for any fixed arrow \<open>\<mu>\<close>,
    the sets of arrows horizontally composable on the left and on the right with \<open>\<mu>\<close>
    form subcategories with respect to vertical composition.  We define the
    sources of \<open>\<mu>\<close> to be the weak units that are composable with \<open>\<mu>\<close> on the right,
    and the targets of \<open>\<mu>\<close> to be the weak units that are composable with \<open>\<mu>\<close>
    on the left.  Weak units are then characterized as arrows that are members
    of the set of their own sources (or, equivalently, of their own targets).
  \<close>

  subsection "Definition"

  locale weak_composition =
    category V +
    VxV: product_category V V +
    VoV: subcategory VxV.comp \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu> \<noteq> null\<close> +
    "functor" VoV.comp V \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu>\<close>
  for V :: "'a comp"         (infixr "\<cdot>" 55)
  and H :: "'a comp"         (infixr "\<star>" 53) +
  assumes left_connected: "seq \<nu> \<nu>' \<Longrightarrow> \<nu> \<star> \<mu> \<noteq> null \<longleftrightarrow> \<nu>' \<star> \<mu> \<noteq> null"
  and right_connected: "seq \<mu> \<mu>' \<Longrightarrow> \<nu> \<star> \<mu> \<noteq> null \<longleftrightarrow> \<nu> \<star> \<mu>' \<noteq> null"
  and match_1: "\<lbrakk> \<nu> \<star> \<mu> \<noteq> null; (\<nu> \<star> \<mu>) \<star> \<tau> \<noteq> null \<rbrakk> \<Longrightarrow> \<mu> \<star> \<tau> \<noteq> null"
  and match_2: "\<lbrakk> \<nu> \<star> (\<mu> \<star> \<tau>) \<noteq> null; \<mu> \<star> \<tau> \<noteq> null \<rbrakk> \<Longrightarrow> \<nu> \<star> \<mu> \<noteq> null"
  and match_3: "\<lbrakk> \<mu> \<star> \<tau> \<noteq> null; \<nu> \<star> \<mu> \<noteq> null \<rbrakk> \<Longrightarrow> (\<nu> \<star> \<mu>) \<star> \<tau> \<noteq> null"
  and match_4: "\<lbrakk> \<mu> \<star> \<tau> \<noteq> null; \<nu> \<star> \<mu> \<noteq> null \<rbrakk> \<Longrightarrow> \<nu> \<star> (\<mu> \<star> \<tau>) \<noteq> null"
  begin

    text \<open>
      We think of the arrows of the vertical category as ``2-cells'' and the vertical identities
      as ``1-cells''.  In the formal development, the predicate @{term arr} (``arrow'')
      will have its normal meaning with respect to the vertical composition, hence @{term "arr \<mu>"}
      will mean, essentially, ``\<open>\<mu>\<close> is a 2-cell''.  This is somewhat unfortunate, as it is
      traditional when discussing bicategories to use the term ``arrow'' to refer to the 1-cells.
      However, we are trying to carry over all the formalism that we have already developed for
      categories and apply it to bicategories with as little change and redundancy as possible.
      It becomes too confusing to try to repurpose the name @{term arr} to mean @{term ide} and
      to introduce a replacement for the name @{term arr}, so we will simply tolerate the
      situation.  In informal text, we will prefer the terms ``2-cell'' and ``1-cell'' over
      (vertical) ``arrow'' and ``identity'' when there is a chance for confusion.

      We do, however, make the following adjustments in notation for @{term in_hom} so that
      it is distinguished from the notion @{term in_hhom} (``in horizontal hom'') to be
      introduced subsequently.
    \<close>

    no_notation in_hom      ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    notation in_hom         ("\<guillemotleft>_ : _ \<Rightarrow> _\<guillemotright>")

    lemma is_partial_magma:
    shows "partial_magma H"
    proof
      show "\<exists>!n. \<forall>f. n \<star> f = n \<and> f \<star> n = n"
      proof
        show 1: "\<forall>f. null \<star> f = null \<and> f \<star> null = null"
          using is_extensional VoV.inclusion VoV.arr_char by force
        show "\<And>n. \<forall>f. n \<star> f = n \<and> f \<star> n = n \<Longrightarrow> n = null"
          using 1 VoV.arr_char is_extensional not_arr_null by metis
      qed
    qed

    interpretation H: partial_magma H
      using is_partial_magma by auto

    text \<open>
      Either \<open>match_1\<close> or \<open>match_2\<close> seems essential for the next result, which states
      that the nulls for the horizontal and vertical compositions coincide.
    \<close>

    lemma null_agreement [simp]:
    shows "H.null = null"
      by (metis VoV.inclusion VxV.not_arr_null match_1 H.comp_null(1))

    lemma composable_implies_arr:
    assumes "\<nu> \<star> \<mu> \<noteq> null"
    shows "arr \<mu>" and "arr \<nu>"
      using assms is_extensional VoV.arr_char VoV.inclusion by auto

    lemma hcomp_null [simp]:
    shows "null \<star> \<mu> = null" and "\<mu> \<star> null = null"
      using H.comp_null by auto

    lemma hcomp_simps\<^sub>W\<^sub>C [simp]:
    assumes "\<nu> \<star> \<mu> \<noteq> null"
    shows "arr (\<nu> \<star> \<mu>)" and "dom (\<nu> \<star> \<mu>) = dom \<nu> \<star> dom \<mu>" and "cod (\<nu> \<star> \<mu>) = cod \<nu> \<star> cod \<mu>"
      using assms preserves_arr preserves_dom preserves_cod VoV.arr_char VoV.inclusion
      by force+

    lemma ide_hcomp\<^sub>W\<^sub>C [simp]:
    assumes "ide f" and "ide g" and "g \<star> f \<noteq> null"
    shows "ide (g \<star> f)"
      using assms preserves_ide VoV.ide_char by force

    lemma hcomp_in_hom\<^sub>W\<^sub>C [intro]:
    assumes "\<nu> \<star> \<mu> \<noteq> null"
    shows "\<guillemotleft>\<nu> \<star> \<mu> : dom \<nu> \<star> dom \<mu> \<Rightarrow> cod \<nu> \<star> cod \<mu>\<guillemotright>"
      using assms by auto

    text \<open>
      Horizontal composability of arrows is determined by horizontal composability of
      their domains and codomains (defined with respect to vertical composition).
    \<close>

    lemma hom_connected:
    shows "\<nu> \<star> \<mu> \<noteq> null \<longleftrightarrow> dom \<nu> \<star> \<mu> \<noteq> null"
    and "\<nu> \<star> \<mu> \<noteq> null \<longleftrightarrow> \<nu> \<star> dom \<mu> \<noteq> null"
    and "\<nu> \<star> \<mu> \<noteq> null \<longleftrightarrow> cod \<nu> \<star> \<mu> \<noteq> null"
    and "\<nu> \<star> \<mu> \<noteq> null \<longleftrightarrow> \<nu> \<star> cod \<mu> \<noteq> null"
    proof -
      show "\<nu> \<star> \<mu> \<noteq> null \<longleftrightarrow> dom \<nu> \<star> \<mu> \<noteq> null"
        using left_connected [of \<nu> "dom \<nu>" \<mu>] composable_implies_arr arr_dom_iff_arr by force
      show "\<nu> \<star> \<mu> \<noteq> null \<longleftrightarrow> cod \<nu> \<star> \<mu> \<noteq> null"
        using left_connected [of  "cod \<nu>" \<nu> \<mu>] composable_implies_arr arr_cod_iff_arr by force
      show "\<nu> \<star> \<mu> \<noteq> null \<longleftrightarrow> \<nu> \<star> dom \<mu> \<noteq> null"
        using right_connected [of \<mu> "dom \<mu>" \<nu>] composable_implies_arr arr_dom_iff_arr by force
      show "\<nu> \<star> \<mu> \<noteq> null \<longleftrightarrow> \<nu> \<star> cod \<mu> \<noteq> null"
        using right_connected [of "cod \<mu>" \<mu> \<nu>] composable_implies_arr arr_cod_iff_arr by force
    qed

    lemma isomorphic_implies_equicomposable:
    assumes "f \<cong> g"
    shows "\<tau> \<star> f \<noteq> null \<longleftrightarrow> \<tau> \<star> g \<noteq> null"
    and "f \<star> \<sigma> \<noteq> null \<longleftrightarrow> g \<star> \<sigma> \<noteq> null"
      using assms isomorphic_def hom_connected by auto

    lemma interchange:
    assumes "seq \<nu> \<mu>" and "seq \<tau> \<sigma>"
    shows "(\<nu> \<cdot> \<mu>) \<star> (\<tau> \<cdot> \<sigma>) = (\<nu> \<star> \<tau>) \<cdot> (\<mu> \<star> \<sigma>)"
    proof -
      have "\<mu> \<star> \<sigma> = null \<Longrightarrow> ?thesis"
        by (metis assms comp_null(2) dom_comp hom_connected(1-2))
      moreover have "\<mu> \<star> \<sigma> \<noteq> null \<Longrightarrow> ?thesis"
      proof -
        assume \<mu>\<sigma>: "\<mu> \<star> \<sigma> \<noteq> null"
        have 1: "VoV.arr (\<mu>, \<sigma>)"
          using \<mu>\<sigma> VoV.arr_char by auto
        have \<nu>\<tau>: "(\<nu>, \<tau>) \<in> VoV.hom (VoV.cod (\<mu>, \<sigma>)) (VoV.cod (\<nu>, \<tau>))"
        proof -
          have "VoV.arr (\<nu>, \<tau>)"
            using assms 1 hom_connected VoV.arr_char
            by (elim seqE, auto, metis)
          thus ?thesis
            using assms \<mu>\<sigma> VoV.dom_char VoV.cod_char by fastforce
        qed
        show ?thesis
        proof -
          have "VoV.seq (\<nu>, \<tau>) (\<mu>, \<sigma>)"
            using assms 1 \<mu>\<sigma> \<nu>\<tau> VoV.seqI by blast
          thus ?thesis
            using assms 1 \<mu>\<sigma> \<nu>\<tau> VoV.comp_char preserves_comp [of "(\<nu>, \<tau>)" "(\<mu>, \<sigma>)"] VoV.seqI
            by fastforce
        qed
      qed
      ultimately show ?thesis by blast
    qed

    lemma paste_1:
    shows "\<nu> \<star> \<mu> = (cod \<nu> \<star> \<mu>) \<cdot> (\<nu> \<star> dom \<mu>)"
      using interchange composable_implies_arr comp_arr_dom comp_cod_arr
            hom_connected(2-3)
      by (metis comp_null(2))

    lemma paste_2:
    shows "\<nu> \<star> \<mu> = (\<nu> \<star> cod \<mu>) \<cdot> (dom \<nu> \<star> \<mu>)"
      using interchange composable_implies_arr comp_arr_dom comp_cod_arr
            hom_connected(1,4)
      by (metis comp_null(2))

    lemma whisker_left:
    assumes "seq \<nu> \<mu>" and "ide f"
    shows "f \<star> (\<nu> \<cdot> \<mu>) = (f \<star> \<nu>) \<cdot> (f \<star> \<mu>)"
      using assms interchange [of f f \<nu> \<mu>] hom_connected by auto

    lemma whisker_right:
    assumes "seq \<nu> \<mu>" and "ide f"
    shows "(\<nu> \<cdot> \<mu>) \<star> f = (\<nu> \<star> f) \<cdot> (\<mu> \<star> f)"
      using assms interchange [of \<nu> \<mu> f f] hom_connected by auto

    subsection "Hom-Subcategories"

    definition left
    where "left \<tau> \<equiv> \<lambda>\<mu>. \<tau> \<star> \<mu> \<noteq> null"

    definition right
    where "right \<sigma> \<equiv> \<lambda>\<mu>. \<mu> \<star> \<sigma> \<noteq> null"

    lemma right_iff_left:
    shows "right \<sigma> \<tau> \<longleftrightarrow> left \<tau> \<sigma>"
      using right_def left_def by simp

    lemma left_respects_isomorphic:
    assumes "f \<cong> g"
    shows "left f = left g"
      using assms isomorphic_implies_equicomposable left_def by auto

    lemma right_respects_isomorphic:
    assumes "f \<cong> g"
    shows "right f = right g"
      using assms isomorphic_implies_equicomposable right_def by auto

    lemma left_iff_left_inv:
    assumes "iso \<mu>"
    shows "left \<tau> \<mu> \<longleftrightarrow> left \<tau> (inv \<mu>)"
      using assms left_def inv_in_hom hom_connected(2) hom_connected(4) [of \<tau> "inv \<mu>"]
      by auto
        
    lemma right_iff_right_inv:
    assumes "iso \<mu>"
    shows "right \<sigma> \<mu> \<longleftrightarrow> right \<sigma> (inv \<mu>)"
      using assms right_def inv_in_hom hom_connected(1) hom_connected(3) [of "inv \<mu>" \<sigma>]
      by auto

    lemma left_hom_is_subcategory:
    assumes "arr \<mu>"
    shows "subcategory V (left \<mu>)"
    proof (unfold left_def, unfold_locales)
      show "\<And>f. \<mu> \<star> f \<noteq> null \<Longrightarrow> arr f" using composable_implies_arr by simp
      show "\<And>f. \<mu> \<star> f \<noteq> null \<Longrightarrow> \<mu> \<star> dom f \<noteq> null" using hom_connected(2) by simp
      show "\<And>f. \<mu> \<star> f \<noteq> null \<Longrightarrow> \<mu> \<star> cod f \<noteq> null" using hom_connected(4) by auto
      show "\<And>f g. \<lbrakk> \<mu> \<star> f \<noteq> null; \<mu> \<star> g \<noteq> null; cod f = dom g \<rbrakk> \<Longrightarrow> \<mu> \<star> (g \<cdot> f) \<noteq> null"
      proof -
        fix f g
        assume f: "\<mu> \<star> f \<noteq> null" and g: "\<mu> \<star> g \<noteq> null" and fg: "cod f = dom g"
        show "\<mu> \<star> (g \<cdot> f) \<noteq> null"
          using f g fg composable_implies_arr hom_connected(2) [of \<mu> "g \<cdot> f"] hom_connected(2)
          by simp
      qed
    qed

    lemma right_hom_is_subcategory:
    assumes "arr \<mu>"
    shows "subcategory V (right \<mu>)"
    proof (unfold right_def, unfold_locales)
      show "\<And>f. f \<star> \<mu> \<noteq> null \<Longrightarrow> arr f" using composable_implies_arr by simp
      show "\<And>f. f \<star> \<mu> \<noteq> null \<Longrightarrow> dom f \<star> \<mu> \<noteq> null" using hom_connected(1) by auto
      show "\<And>f. f \<star> \<mu> \<noteq> null \<Longrightarrow> cod f \<star> \<mu> \<noteq> null" using hom_connected(3) by auto
      show "\<And>f g. \<lbrakk> f \<star> \<mu> \<noteq> null; g \<star> \<mu> \<noteq> null; cod f = dom g \<rbrakk> \<Longrightarrow> (g \<cdot> f) \<star> \<mu> \<noteq> null"
      proof -
        fix f g
        assume f: "f \<star> \<mu> \<noteq> null" and g: "g \<star> \<mu> \<noteq> null" and fg: "cod f = dom g"
        show "(g \<cdot> f) \<star> \<mu> \<noteq> null"
          using f g fg composable_implies_arr hom_connected(1) [of "g \<cdot> f" \<mu>] hom_connected(1)
          by simp
      qed
    qed

    abbreviation Left
    where "Left a \<equiv> subcategory.comp V (left a)"

    abbreviation Right
    where "Right a \<equiv> subcategory.comp V (right a)"

    text \<open>
      We define operations of composition on the left or right with a fixed 1-cell,
      and show that such operations are functorial in case that 1-cell is
      horizontally self-composable.
    \<close>

    definition H\<^sub>L
    where "H\<^sub>L g \<equiv> \<lambda>\<mu>. g \<star> \<mu>"

    definition H\<^sub>R
    where "H\<^sub>R f \<equiv> \<lambda>\<mu>. \<mu> \<star> f"

    (* TODO: Why do the following fail when I use @{thm ...} *)
    text \<open>
      Note that \<open>match_3\<close> and \<open>match_4\<close> are required for the next results.
    \<close>

    lemma endofunctor_H\<^sub>L:
    assumes "ide g" and "g \<star> g \<noteq> null"
    shows "endofunctor (Left g) (H\<^sub>L g)"
    proof -
      interpret L: subcategory V \<open>left g\<close> using assms left_hom_is_subcategory by simp
      have *: "\<And>\<mu>. L.arr \<mu> \<Longrightarrow> H\<^sub>L g \<mu> = g \<star> \<mu>"
        using assms H\<^sub>L_def by simp
      have preserves_arr: "\<And>\<mu>. L.arr \<mu> \<Longrightarrow> L.arr (H\<^sub>L g \<mu>)"
        using assms * L.arr_char left_def match_4 by force
      show "endofunctor L.comp (H\<^sub>L g)"
      proof
        show "\<And>\<mu>. \<not> L.arr \<mu> \<Longrightarrow> H\<^sub>L g \<mu> = L.null"
          using assms L.arr_char L.null_char left_def H\<^sub>L_def by fastforce
        show "\<And>\<mu>. L.arr \<mu> \<Longrightarrow> L.arr (H\<^sub>L g \<mu>)" by fact
        fix \<mu>
        assume "L.arr \<mu>"
        hence \<mu>: "L.arr \<mu> \<and> arr \<mu> \<and> g \<star> \<mu> \<noteq> null"
          using assms L.arr_char composable_implies_arr left_def by metis
        show "L.dom (H\<^sub>L g \<mu>) = H\<^sub>L g (L.dom \<mu>)"
          using assms \<mu> * L.arr_char L.dom_char preserves_arr hom_connected(2) left_def
          by simp
        show "L.cod (H\<^sub>L g \<mu>) = H\<^sub>L g (L.cod \<mu>)"
          using assms \<mu> * L.arr_char L.cod_char preserves_arr hom_connected(4) left_def
          by simp
        next
        fix \<mu> \<nu>
        assume \<mu>\<nu>: "L.seq \<nu> \<mu>"
        have \<mu>: "L.arr \<mu>"
          using \<mu>\<nu> by (elim L.seqE, auto)
        have \<nu>: "L.arr \<nu> \<and> arr \<nu> \<and> in_hom \<nu> (L.cod \<mu>) (L.cod \<nu>) \<and> left g \<nu> \<and> g \<star> \<nu> \<noteq> null"
        proof -
          have 1: "L.in_hom \<nu> (L.cod \<mu>) (L.cod \<nu>)"
            using \<mu>\<nu> by (elim L.seqE, auto)
          hence "arr \<nu> \<and> left g \<nu>"
            using L.hom_char by blast
          thus ?thesis
            using assms 1 left_def by fastforce
        qed
        show "H\<^sub>L g (L.comp \<nu> \<mu>) = L.comp (H\<^sub>L g \<nu>) (H\<^sub>L g \<mu>)"
        proof -
          have "H\<^sub>L g (L.comp \<nu> \<mu>) = g \<star> (\<nu> \<cdot> \<mu>)"
            using \<mu> \<nu> H\<^sub>L_def L.comp_def L.arr_char by fastforce
          also have "... = (g \<star> \<nu>) \<cdot> (g \<star> \<mu>)"
            using assms \<mu> \<nu> L.inclusion whisker_left L.arr_char by fastforce
          also have "... = L.comp (H\<^sub>L g \<nu>) (H\<^sub>L g \<mu>)"
            using assms \<mu>\<nu> \<mu> \<nu> * preserves_arr L.arr_char L.dom_char L.cod_char L.comp_char
                  L.inclusion H\<^sub>L_def left_def
            by auto
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma endofunctor_H\<^sub>R:
    assumes "ide f" and "f \<star> f \<noteq> null"
    shows "endofunctor (Right f) (H\<^sub>R f)"
    proof -
      interpret R: subcategory V \<open>right f\<close> using assms right_hom_is_subcategory by simp
      have *: "\<And>\<mu>. R.arr \<mu> \<Longrightarrow> H\<^sub>R f \<mu> = \<mu> \<star> f"
        using assms H\<^sub>R_def by simp
      have preserves_arr: "\<And>\<mu>. R.arr \<mu> \<Longrightarrow> R.arr (H\<^sub>R f \<mu>)"
        using assms * R.arr_char right_def match_3 by force
      show "endofunctor R.comp (H\<^sub>R f)"
      proof
        show "\<And>\<mu>. \<not> R.arr \<mu> \<Longrightarrow> H\<^sub>R f \<mu> = R.null"
          using assms R.arr_char R.null_char right_def H\<^sub>R_def by fastforce
        show "\<And>\<mu>. R.arr \<mu> \<Longrightarrow> R.arr (H\<^sub>R f \<mu>)" by fact
        fix \<mu>
        assume "R.arr \<mu>"
        hence \<mu>: "R.arr \<mu> \<and> arr \<mu> \<and> \<mu> \<star> f \<noteq> null"
          using assms R.arr_char composable_implies_arr right_def by simp
        show "R.dom (H\<^sub>R f \<mu>) = H\<^sub>R f (R.dom \<mu>)"
          using assms \<mu> * R.arr_char R.dom_char preserves_arr hom_connected(1) right_def
          by simp
        show "R.cod (H\<^sub>R f \<mu>) = H\<^sub>R f (R.cod \<mu>)"
          using assms \<mu> * R.arr_char R.cod_char preserves_arr hom_connected(3) right_def
          by simp
        next
        fix \<mu> \<nu>
        assume \<mu>\<nu>: "R.seq \<nu> \<mu>"
        have \<mu>: "R.arr \<mu>"
          using \<mu>\<nu> by (elim R.seqE, auto)
        have \<nu>: "R.arr \<nu> \<and> arr \<nu> \<and> in_hom \<nu> (R.cod \<mu>) (R.cod \<nu>) \<and> right f \<nu> \<and> \<nu> \<star> f \<noteq> null"
        proof -
          have 1: "R.in_hom \<nu> (R.cod \<mu>) (R.cod \<nu>)"
            using \<mu>\<nu> by (elim R.seqE, auto)
          hence "arr \<nu> \<and> right f \<nu>"
            using R.hom_char by blast
          thus ?thesis
            using assms 1 right_def by fastforce
        qed
        show "H\<^sub>R f (R.comp \<nu> \<mu>) = R.comp (H\<^sub>R f \<nu>) (H\<^sub>R f \<mu>)"
        proof -
          have "H\<^sub>R f (R.comp \<nu> \<mu>) = (\<nu> \<cdot> \<mu>) \<star> f"
            using \<mu> \<nu> H\<^sub>R_def R.comp_def R.arr_char by fastforce
          also have "... = (\<nu> \<star> f) \<cdot> (\<mu> \<star> f)"
            using assms \<mu> \<nu> R.inclusion whisker_right R.arr_char by fastforce
          also have "... = R.comp (H\<^sub>R f \<nu>) (H\<^sub>R f \<mu>)"
            using assms \<mu>\<nu> \<mu> \<nu> * preserves_arr R.arr_char R.dom_char R.cod_char R.comp_char
                  R.inclusion H\<^sub>R_def right_def
            by auto
          finally show ?thesis by blast
        qed
      qed
    qed

  end

  locale left_hom =
    weak_composition V H +
    S: subcategory V \<open>left \<omega>\<close>
  for V :: "'a comp"                  (infixr "\<cdot>" 55)
  and H :: "'a comp"                  (infixr "\<star>" 53)
  and \<omega> :: 'a +
  assumes arr_\<omega>: "arr \<omega>"
  begin

    no_notation in_hom      ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    notation in_hom         ("\<guillemotleft>_ : _ \<Rightarrow> _\<guillemotright>")
    notation S.comp         (infixr "\<cdot>\<^sub>S" 55)
    notation S.in_hom       ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>S _\<guillemotright>")

    lemma right_hcomp_closed [simp]:
    assumes "\<guillemotleft>\<mu> : x \<Rightarrow>\<^sub>S y\<guillemotright>" and "\<guillemotleft>\<nu> : c \<Rightarrow> d\<guillemotright>" and "\<mu> \<star> \<nu> \<noteq> null"
    shows "\<guillemotleft>\<mu> \<star> \<nu> : x \<star> c \<Rightarrow>\<^sub>S y \<star> d\<guillemotright>"
    proof
      show 1: "S.arr (\<mu> \<star> \<nu>)"
        using assms arr_\<omega> S.arr_char left_def match_4
        by (elim S.in_homE, meson)
      show "S.dom (\<mu> \<star> \<nu>) = x \<star> c"
        using assms 1 by force
      show "S.cod (\<mu> \<star> \<nu>) = y \<star> d"
        using assms 1 by force
    qed

    lemma interchange:
    assumes "S.seq \<nu> \<mu>" and "S.seq \<tau> \<sigma>" and "\<mu> \<star> \<sigma> \<noteq> null"
    shows "(\<nu> \<cdot>\<^sub>S \<mu>) \<star> (\<tau> \<cdot>\<^sub>S \<sigma>) = (\<nu> \<star> \<tau>) \<cdot>\<^sub>S (\<mu> \<star> \<sigma>)"
    proof -
      have 1: "\<nu> \<star> \<tau> \<noteq> null"
        using assms hom_connected(1) [of \<nu> \<sigma>] hom_connected(2) [of \<nu> \<tau>] hom_connected(3-4)
        by force
      have "(\<nu> \<cdot>\<^sub>S \<mu>) \<star> (\<tau> \<cdot>\<^sub>S \<sigma>) = (\<nu> \<cdot> \<mu>) \<star> (\<tau> \<cdot> \<sigma>)"
        using assms S.comp_char S.seq_char by metis
      also have "... = (\<nu> \<star> \<tau>) \<cdot> (\<mu> \<star> \<sigma>)"
        using assms interchange S.seq_char S.arr_char by simp
      also have "... = (\<nu> \<star> \<tau>) \<cdot>\<^sub>S (\<mu> \<star> \<sigma>)"
      proof -
        have "S.arr (\<nu> \<star> \<tau>)"
        proof -
          have "\<guillemotleft>\<tau> : dom \<tau> \<Rightarrow> cod \<tau>\<guillemotright>"
            using assms S.in_hom_char by blast
          thus ?thesis
            using assms 1 right_hcomp_closed by blast
        qed
        moreover have "S.arr (\<mu> \<star> \<sigma>)"
        proof -
          have "\<guillemotleft>\<sigma> : dom \<sigma> \<Rightarrow> cod \<sigma>\<guillemotright>"
            using assms S.in_hom_char by blast
          thus ?thesis
            using assms right_hcomp_closed [of \<mu> "dom \<mu>" "cod \<mu>" \<sigma> "dom \<sigma>" "cod \<sigma>"] by fastforce
        qed
        moreover have "seq (\<nu> \<star> \<tau>) (\<mu> \<star> \<sigma>)"
          using assms 1 S.in_hom_char
          by (metis (full_types) S.seq_char hcomp_simps\<^sub>W\<^sub>C(1-3) seqE seqI)
        ultimately show ?thesis
          using S.comp_char by auto
      qed
      finally show ?thesis by blast
    qed

    lemma inv_char:
    assumes "S.arr \<phi>" and "iso \<phi>"
    shows "S.inverse_arrows \<phi> (inv \<phi>)"
    and "S.inv \<phi> = inv \<phi>"
    proof -
      have 1: "S.arr (inv \<phi>)"
      proof -
        have "S.arr \<phi>" using assms by auto
        hence "\<omega> \<star> \<phi> \<noteq> null"
          using S.arr_char left_def by simp
        hence "\<omega> \<star> cod \<phi> \<noteq> null"
          using hom_connected(4) by blast
        hence "\<omega> \<star> dom (inv \<phi>) \<noteq> null"
          using assms S.iso_char by simp
        hence "\<omega> \<star> inv \<phi> \<noteq> null"
          using hom_connected by blast
        thus "S.arr (inv \<phi>)"
          using S.arr_char left_def by force
      qed
      show "S.inv \<phi> = inv \<phi>"
        using assms 1 S.inv_char S.iso_char by blast
      thus "S.inverse_arrows \<phi> (inv \<phi>)"
        using assms 1 S.iso_char S.inv_is_inverse by metis
    qed

    lemma iso_char:
    assumes "S.arr \<phi>"
    shows "S.iso \<phi> \<longleftrightarrow> iso \<phi>"
      using assms S.iso_char inv_char by auto

  end

  locale right_hom =
    weak_composition V H +
    S: subcategory V \<open>right \<omega>\<close>
  for V :: "'a comp"        (infixr "\<cdot>" 55)
  and H :: "'a comp"        (infixr "\<star>" 53)
  and \<omega> :: 'a +
  assumes arr_\<omega>: "arr \<omega>"
  begin

    no_notation in_hom      ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    notation in_hom         ("\<guillemotleft>_ : _ \<Rightarrow> _\<guillemotright>")
    notation S.comp         (infixr "\<cdot>\<^sub>S" 55)
    notation S.in_hom       ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>S _\<guillemotright>")

    lemma left_hcomp_closed [simp]:
    assumes "\<guillemotleft>\<mu> : x \<Rightarrow>\<^sub>S y\<guillemotright>" and "\<guillemotleft>\<nu> : c \<Rightarrow> d\<guillemotright>" and "\<nu> \<star> \<mu> \<noteq> null"
    shows "\<guillemotleft>\<nu> \<star> \<mu> : c \<star> x \<Rightarrow>\<^sub>S d \<star> y\<guillemotright>"
    proof
      show 1: "S.arr (\<nu> \<star> \<mu>)"
        using assms arr_\<omega> S.arr_char right_def match_3
        by (elim S.in_homE, meson)
      show "S.dom (\<nu> \<star> \<mu>) = c \<star> x"
        using assms 1 by force
      show "S.cod (\<nu> \<star> \<mu>) = d \<star> y"
        using assms 1 by force
    qed

    lemma interchange:
    assumes "S.seq \<nu> \<mu>" and "S.seq \<tau> \<sigma>" and "\<mu> \<star> \<sigma> \<noteq> null"
    shows "(\<nu> \<cdot>\<^sub>S \<mu>) \<star> (\<tau> \<cdot>\<^sub>S \<sigma>) = (\<nu> \<star> \<tau>) \<cdot>\<^sub>S (\<mu> \<star> \<sigma>)"
    proof -
      have 1: "\<nu> \<star> \<tau> \<noteq> null"
        using assms hom_connected(1) [of \<nu> \<sigma>] hom_connected(2) [of \<nu> \<tau>] hom_connected(3-4)
        by fastforce
      have "(\<nu> \<cdot>\<^sub>S \<mu>) \<star> (\<tau> \<cdot>\<^sub>S \<sigma>) = (\<nu> \<cdot> \<mu>) \<star> (\<tau> \<cdot> \<sigma>)"
        using assms S.comp_char S.seq_char by metis
      also have "... = (\<nu> \<star> \<tau>) \<cdot> (\<mu> \<star> \<sigma>)"
        using assms interchange S.seq_char S.arr_char by simp
      also have "... = (\<nu> \<star> \<tau>) \<cdot>\<^sub>S (\<mu> \<star> \<sigma>)"
      proof -
        have "S.arr (\<nu> \<star> \<tau>)"
        proof -
          have "\<guillemotleft>\<nu> : dom \<nu> \<Rightarrow> cod \<nu>\<guillemotright>"
            using assms S.in_hom_char by blast
          thus ?thesis
            using assms 1 left_hcomp_closed by blast
        qed
        moreover have "S.arr (\<mu> \<star> \<sigma>)"
        proof -
          have "\<guillemotleft>\<mu> : dom \<mu> \<Rightarrow> cod \<mu>\<guillemotright>"
            using assms S.in_hom_char by blast
          thus ?thesis
            using assms left_hcomp_closed [of \<sigma> "dom \<sigma>" "cod \<sigma>" \<mu> "dom \<mu>" "cod \<mu>"]
            by fastforce
        qed
        moreover have "seq (\<nu> \<star> \<tau>) (\<mu> \<star> \<sigma>)"
          using assms 1 S.in_hom_char
          by (metis (full_types) S.seq_char hcomp_simps\<^sub>W\<^sub>C(1-3) seqE seqI)
        ultimately show ?thesis
          using S.comp_char by auto
      qed
      finally show ?thesis by blast
    qed

    lemma inv_char:
    assumes "S.arr \<phi>" and "iso \<phi>"
    shows "S.inverse_arrows \<phi> (inv \<phi>)"
    and "S.inv \<phi> = inv \<phi>"
    proof -
      have 1: "S.arr (inv \<phi>)"
      proof -
        have "S.arr \<phi>" using assms by auto
        hence "\<phi> \<star> \<omega> \<noteq> null"
          using S.arr_char right_def by simp
        hence "cod \<phi> \<star> \<omega> \<noteq> null"
          using hom_connected(3) by blast
        hence "dom (inv \<phi>) \<star> \<omega> \<noteq> null"
          using assms S.iso_char by simp
        hence "inv \<phi> \<star> \<omega> \<noteq> null"
          using hom_connected(1) by blast
        thus ?thesis
          using S.arr_char right_def by force
      qed
      show "S.inv \<phi> = inv \<phi>"
        using assms 1 S.inv_char S.iso_char by blast
      thus "S.inverse_arrows \<phi> (inv \<phi>)"
        using assms 1 S.iso_char S.inv_is_inverse by metis
    qed

    lemma iso_char:
    assumes "S.arr \<phi>"
    shows "S.iso \<phi> \<longleftrightarrow> iso \<phi>"
      using assms S.iso_char inv_char by auto

  end

  subsection "Weak Units"

  text \<open>
    We now define a \emph{weak unit} to be an arrow \<open>a\<close> such that:
    \begin{enumerate}
    \item  \<open>a \<star> a\<close> is isomorphic to \<open>a\<close>
           (and hence \<open>a\<close> is a horizontally self-composable 1-cell).
    \item  Horizontal composition on the left with \<open>a\<close> is a fully faithful endofunctor of the
           subcategory of arrows that are composable on the left with \<open>a\<close>.
    \item  Horizontal composition on the right with \<open>a\<close> is fully faithful endofunctor of the
           subcategory of arrows that are composable on the right with \<open>a\<close>.
    \end{enumerate}
  \<close>

  context weak_composition
  begin

    definition weak_unit :: "'a \<Rightarrow> bool"
    where "weak_unit a \<equiv> a \<star> a \<cong> a \<and>
                         fully_faithful_functor (Left a) (Left a) (H\<^sub>L a) \<and>
                         fully_faithful_functor (Right a) (Right a) (H\<^sub>R a)"

    lemma weak_unit_self_composable [simp]:
    assumes "weak_unit a"
    shows "ide a" and "ide (a \<star> a)" and "a \<star> a \<noteq> null"
    proof -
      obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : a \<star> a \<Rightarrow> a\<guillemotright> \<and> iso \<phi>"
        using assms weak_unit_def isomorphic_def by blast
      have 1: "arr \<phi>" using \<phi> by blast
      show "ide a" using \<phi> ide_cod by blast
      thus "ide (a \<star> a)" using \<phi> ide_dom by force
      thus "a \<star> a \<noteq> null" using not_arr_null ideD(1) by metis
    qed

    lemma weak_unit_self_right:
    assumes "weak_unit a"
    shows "right a a"
      using assms weak_unit_self_composable right_def by simp

    lemma weak_unit_self_left:
    assumes "weak_unit a"
    shows "left a a"
      using assms weak_unit_self_composable left_def by simp

    lemma weak_unit_in_vhom:
    assumes "weak_unit a"
    shows "\<guillemotleft>a : a \<Rightarrow> a\<guillemotright>"
      using assms weak_unit_self_composable left_def by auto

    text \<open>
      If \<open>a\<close> is a weak unit, then there exists a ``unit isomorphism'' \<open>\<guillemotleft>\<iota> : a \<star> a \<Rightarrow> a\<guillemotright>\<close>.
      It need not be unique, but we may choose one arbitrarily.
    \<close>

    definition some_unit
    where "some_unit a \<equiv> SOME \<iota>. iso \<iota> \<and> \<guillemotleft>\<iota> : a \<star> a \<Rightarrow> a\<guillemotright>"

    lemma iso_some_unit:
    assumes "weak_unit a"
    shows "iso (some_unit a)"
    and "\<guillemotleft>some_unit a : a \<star> a \<Rightarrow> a\<guillemotright>"
    proof -
      let ?P = "\<lambda>\<iota>. iso \<iota> \<and> \<guillemotleft>\<iota> : a \<star> a \<Rightarrow> a\<guillemotright>"
      have "\<exists>\<iota>. ?P \<iota>"
        using assms weak_unit_def by auto
      hence 1: "?P (some_unit a)"
        using someI_ex [of ?P] some_unit_def by simp
      show "iso (some_unit a)" using 1 by blast
      show "\<guillemotleft>some_unit a : a \<star> a \<Rightarrow> a\<guillemotright>" using 1 by blast
    qed

    text \<open>
      The \emph{sources} of an arbitrary arrow \<open>\<mu>\<close> are the weak units that are composable with \<open>\<mu>\<close>
      on the right.  Similarly, the \emph{targets} of \<open>\<mu>\<close> are the weak units that are composable
      with \<open>\<mu>\<close> on the left.
    \<close>

    definition sources
    where "sources \<mu> \<equiv> {a. weak_unit a \<and> \<mu> \<star> a \<noteq> null}"

    lemma sourcesI [intro]:
    assumes "weak_unit a" and "\<mu> \<star> a \<noteq> null"
    shows "a \<in> sources \<mu>"
      using assms sources_def by blast

    lemma sourcesD [dest]:
    assumes "a \<in> sources \<mu>"
    shows "ide a" and "weak_unit a" and "\<mu> \<star> a \<noteq> null"
      using assms sources_def by auto

    definition targets
    where "targets \<mu> \<equiv> {b. weak_unit b \<and> b \<star> \<mu> \<noteq> null}"

    lemma targetsI [intro]:
    assumes "weak_unit b" and "b \<star> \<mu> \<noteq> null"
    shows "b \<in> targets \<mu>"
      using assms targets_def by blast

    lemma targetsD [dest]:
    assumes "b \<in> targets \<mu>"
    shows "ide b" and "weak_unit b" and "b \<star> \<mu> \<noteq> null"
      using assms targets_def by auto

    lemma sources_dom [simp]:
    assumes "arr \<mu>"
    shows "sources (dom \<mu>) = sources \<mu>"
      using assms hom_connected(1) by blast

    lemma sources_cod [simp]:
    assumes "arr \<mu>"
    shows "sources (cod \<mu>) = sources \<mu>"
      using assms hom_connected(3) by blast

    lemma targets_dom [simp]:
    assumes "arr \<mu>"
    shows "targets (dom \<mu>) = targets \<mu>"
      using assms hom_connected(2) by blast

    lemma targets_cod [simp]:
    assumes "arr \<mu>"
    shows "targets (cod \<mu>) = targets \<mu>"
      using assms hom_connected(4) by blast

    lemma weak_unit_iff_self_source:
    shows "weak_unit a \<longleftrightarrow> a \<in> sources a"
      using weak_unit_self_composable by auto

    lemma weak_unit_iff_self_target:
    shows "weak_unit b \<longleftrightarrow> b \<in> targets b"
      using weak_unit_self_composable by auto

    abbreviation (input) in_hhom\<^sub>W\<^sub>C  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>W\<^sub>C _\<guillemotright>")
    where "in_hhom\<^sub>W\<^sub>C \<mu> f g \<equiv> arr \<mu> \<and> f \<in> sources \<mu> \<and> g \<in> targets \<mu>"

    lemma sources_hcomp:
    assumes "\<nu> \<star> \<mu> \<noteq> null"
    shows "sources (\<nu> \<star> \<mu>) = sources \<mu>"
      using assms match_1 match_3 null_agreement by blast

    lemma targets_hcomp:
    assumes "\<nu> \<star> \<mu> \<noteq> null"
    shows "targets (\<nu> \<star> \<mu>) = targets \<nu>"
      using assms match_2 match_4 null_agreement by blast

    lemma H\<^sub>R_preserved_along_iso:
    assumes "weak_unit a" and "a \<cong> a'"
    shows "endofunctor (Right a) (H\<^sub>R a')"
    proof -
      have a: "ide a \<and> weak_unit a" using assms isomorphic_def by auto
      have a': "ide a'" using assms isomorphic_def by auto
      (* TODO: The following interpretation re-introduces unwanted notation for "in_hom" *)
      interpret R: subcategory V \<open>right a\<close> using a right_hom_is_subcategory by simp
      have *: "\<And>\<mu>. R.arr \<mu> \<Longrightarrow> H\<^sub>R a' \<mu> = \<mu> \<star> a'"
        using assms H\<^sub>R_def by simp
      have preserves_arr: "\<And>\<mu>. R.arr \<mu> \<Longrightarrow> R.arr (H\<^sub>R a' \<mu>)"
        using assms a' * R.arr_char right_def weak_unit_def weak_unit_self_composable
              isomorphic_implies_equicomposable R.ide_char match_3 hcomp_simps\<^sub>W\<^sub>C(1)
              null_agreement
        by metis
      show "endofunctor R.comp (H\<^sub>R a')"
      proof
        show "\<And>\<mu>. \<not> R.arr \<mu> \<Longrightarrow> H\<^sub>R a' \<mu> = R.null"
          using assms R.arr_char R.null_char right_def H\<^sub>R_def null_agreement
                right_respects_isomorphic
          by metis
        fix \<mu>
        assume "R.arr \<mu>"
        hence \<mu>: "R.arr \<mu> \<and> arr \<mu> \<and> right a \<mu> \<and> right a' \<mu> \<and> \<mu> \<star> a \<noteq> null \<and> \<mu> \<star> a' \<noteq> null"
          using assms R.arr_char right_respects_isomorphic composable_implies_arr null_agreement
                right_def
          by metis
        show "R.arr (H\<^sub>R a' \<mu>)" using \<mu> preserves_arr by blast
        show "R.dom (H\<^sub>R a' \<mu>) = H\<^sub>R a' (R.dom \<mu>)"
          using a' \<mu> * R.arr_char R.dom_char preserves_arr hom_connected(1) right_def
          by simp
        show "R.cod (H\<^sub>R a' \<mu>) = H\<^sub>R a' (R.cod \<mu>)"
          using a' \<mu> * R.arr_char R.cod_char preserves_arr hom_connected(3) right_def
          by simp
        next
        fix \<mu> \<nu>
        assume \<mu>\<nu>: "R.seq \<nu> \<mu>"
        have "R.arr \<mu>"
          using \<mu>\<nu> by (elim R.seqE, auto)
        hence \<mu>: "R.arr \<mu> \<and> arr \<mu> \<and> right a \<mu> \<and> right a' \<mu> \<and> \<mu> \<star> a \<noteq> null \<and> \<mu> \<star> a' \<noteq> null"
          using assms R.arr_char right_respects_isomorphic composable_implies_arr null_agreement
                right_def
          by metis
        have "\<nu> \<in> R.hom (R.cod \<mu>) (R.cod \<nu>)"
          using \<mu>\<nu> by (elim R.seqE, auto)
        hence "\<guillemotleft>\<nu> : R.cod \<mu> \<Rightarrow> R.cod \<nu>\<guillemotright> \<and> arr \<nu> \<and> \<nu> \<in> Collect (right a)"
          using R.hom_char by blast
        hence \<nu>: "\<guillemotleft>\<nu> : R.cod \<mu> \<rightarrow> R.cod \<nu>\<guillemotright> \<and> arr \<nu> \<and>
                  right a \<nu> \<and> H \<nu> a \<noteq> null \<and> right a' \<nu> \<and> H \<nu> a' \<noteq> null"
          using assms right_def right_respects_isomorphic isomorphic_implies_equicomposable
          by simp
        show "H\<^sub>R a' (R.comp \<nu> \<mu>) = R.comp (H\<^sub>R a' \<nu>) (H\<^sub>R a' \<mu>)"
        proof -
          have 1: "R.arr (H\<^sub>R a' \<nu>)"
            using \<nu> preserves_arr by blast
          have 2: "seq (\<nu> \<star> a') (\<mu> \<star> a')"
            using a' \<mu> \<nu> R.arr_char R.inclusion R.dom_char R.cod_char
                   isomorphic_implies_equicomposable
            by auto
          show ?thesis
          proof -
            have "H\<^sub>R a' (R.comp \<nu> \<mu>) = (\<nu> \<cdot> \<mu>) \<star> a'"
              using \<mu> \<nu> H\<^sub>R_def R.comp_def by fastforce
            also have "... = (\<nu> \<star> a') \<cdot> (\<mu> \<star> a')"
            proof -
              have "seq \<nu> \<mu>"
                using \<mu> \<nu> \<mu>\<nu> by (elim R.seqE, auto)
              thus ?thesis
                using a' \<nu> whisker_right right_def by blast
            qed
            also have "... = R.comp (H\<^sub>R a' \<nu>) (H\<^sub>R a' \<mu>)"
              using assms \<mu> 1 2 preserves_arr R.comp_char R.inclusion H\<^sub>R_def by auto
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

    lemma H\<^sub>L_preserved_along_iso:
    assumes "weak_unit a" and "a \<cong> a'"
    shows "endofunctor (Left a) (H\<^sub>L a')"
    proof -
      have a: "ide a \<and> weak_unit a" using assms isomorphic_def by auto
      have a': "ide a'" using assms isomorphic_def by auto
      (* TODO: The following interpretation re-introduces unwanted notation for "in_hom" *)
      interpret L: subcategory V \<open>left a\<close> using a left_hom_is_subcategory by simp
      have *: "\<And>\<mu>. L.arr \<mu> \<Longrightarrow> H\<^sub>L a' \<mu> = a' \<star> \<mu>"
        using assms H\<^sub>L_def by simp
      have preserves_arr: "\<And>\<mu>. L.arr \<mu> \<Longrightarrow> L.arr (H\<^sub>L a' \<mu>)"
        using assms a' * L.arr_char left_def weak_unit_def weak_unit_self_composable
              isomorphic_implies_equicomposable L.ide_char match_4 hcomp_simps\<^sub>W\<^sub>C(1)
              null_agreement
        by metis
      show "endofunctor L.comp (H\<^sub>L a')"
      proof
        show "\<And>\<mu>. \<not> L.arr \<mu> \<Longrightarrow> H\<^sub>L a' \<mu> = L.null"
          using assms L.arr_char L.null_char left_def H\<^sub>L_def null_agreement
                left_respects_isomorphic
          by metis
        fix \<mu>
        assume "L.arr \<mu>"
        hence \<mu>: "L.arr \<mu> \<and> arr \<mu> \<and> left a \<mu> \<and> left a' \<mu> \<and> a \<star> \<mu> \<noteq> null \<and> a' \<star> \<mu> \<noteq> null"
          using assms L.arr_char left_respects_isomorphic composable_implies_arr null_agreement
                left_def
          by metis
        show "L.arr (H\<^sub>L a' \<mu>)" using \<mu> preserves_arr by blast
        show "L.dom (H\<^sub>L a' \<mu>) = H\<^sub>L a' (L.dom \<mu>)"
          using a' \<mu> * L.arr_char L.dom_char preserves_arr hom_connected(2) left_def
          by simp
        show "L.cod (H\<^sub>L a' \<mu>) = H\<^sub>L a' (L.cod \<mu>)"
          using a' \<mu> * L.arr_char L.cod_char preserves_arr hom_connected(4) left_def
          by simp
        next
        fix \<mu> \<nu>
        assume \<mu>\<nu>: "L.seq \<nu> \<mu>"
        have "L.arr \<mu>"
          using \<mu>\<nu> by (elim L.seqE, auto)
        hence \<mu>: "L.arr \<mu> \<and> arr \<mu> \<and> left a \<mu> \<and> left a' \<mu> \<and> a \<star> \<mu> \<noteq> null \<and> a' \<star> \<mu> \<noteq> null"
          using assms L.arr_char left_respects_isomorphic composable_implies_arr null_agreement
                left_def
          by metis
        have "L.in_hom \<nu> (L.cod \<mu>) (L.cod \<nu>)"
          using \<mu>\<nu> by (elim L.seqE, auto)
        hence "\<guillemotleft>\<nu> : L.cod \<mu> \<Rightarrow> L.cod \<nu>\<guillemotright> \<and> arr \<nu> \<and> \<nu> \<in> Collect (left a)"
          using L.hom_char by blast
        hence \<nu>: "\<guillemotleft>\<nu> : L.cod \<mu> \<Rightarrow> L.cod \<nu>\<guillemotright> \<and> arr \<nu> \<and>
                  left a \<nu> \<and> a \<star> \<nu> \<noteq> null \<and> left a' \<nu> \<and> a' \<star> \<nu> \<noteq> null"
          using assms left_def left_respects_isomorphic isomorphic_implies_equicomposable
          by simp
        show "H\<^sub>L a' (L.comp \<nu> \<mu>) = L.comp (H\<^sub>L a' \<nu>) (H\<^sub>L a' \<mu>)"
        proof -
          have 1: "L.arr (H\<^sub>L a' \<nu>)"
            using \<nu> preserves_arr by blast
          have 2: "seq (a' \<star> \<nu>) (a' \<star> \<mu>)"
            using a' \<mu> \<nu> L.arr_char L.inclusion L.dom_char L.cod_char
                  isomorphic_implies_equicomposable
            by auto
          have "H\<^sub>L a' (L.comp \<nu> \<mu>) = a' \<star> (\<nu> \<cdot> \<mu>)"
            using \<mu> \<nu> H\<^sub>L_def L.comp_def by fastforce
          also have "... = (a' \<star> \<nu>) \<cdot> (a' \<star> \<mu>)"
          proof -
            have "seq \<nu> \<mu>"
              using \<mu> \<nu> \<mu>\<nu> by (elim L.seqE, auto)
            thus ?thesis
              using a' \<nu> whisker_left right_def by blast
          qed
          also have "... = L.comp (H\<^sub>L a' \<nu>) (H\<^sub>L a' \<mu>)"
            using assms \<mu> 1 2 preserves_arr L.comp_char L.inclusion H\<^sub>L_def by auto
          finally show ?thesis by blast
        qed
      qed
    qed

  end

  subsection "Regularity"

  text \<open>
    We call a weak composition \emph{regular} if \<open>f \<star> a \<cong> f\<close> whenever \<open>a\<close> is a source of
    1-cell \<open>f\<close>, and \<open>b \<star> f \<cong> f\<close> whenever \<open>b\<close> is a target of \<open>f\<close>.  A consequence of regularity
    is that horizontal composability of 2-cells is fully determined by their sets of
    sources and targets.
  \<close>

  locale regular_weak_composition =
    weak_composition +
  assumes comp_ide_source: "\<lbrakk> a \<in> sources f; ide f \<rbrakk> \<Longrightarrow> f \<star> a \<cong> f"
  and comp_target_ide: "\<lbrakk> b \<in> targets f; ide f \<rbrakk> \<Longrightarrow> b \<star> f \<cong> f"
  begin

    lemma sources_determine_composability:
    assumes "a \<in> sources \<tau>"
    shows "\<tau> \<star> \<mu> \<noteq> null \<longleftrightarrow> a \<star> \<mu> \<noteq> null"
    proof -
      have *: "\<And>\<tau>. ide \<tau> \<and> a \<in> sources \<tau> \<Longrightarrow> \<tau> \<star> \<mu> \<noteq> null \<longleftrightarrow> a \<star> \<mu> \<noteq> null"
      proof -
        fix \<tau>
        assume \<tau>: "ide \<tau> \<and> a \<in> sources \<tau>"
        show "\<tau> \<star> \<mu> \<noteq> null \<longleftrightarrow> a \<star> \<mu> \<noteq> null"
        proof
          assume \<mu>: "\<tau> \<star> \<mu> \<noteq> null"
          show "a \<star> \<mu> \<noteq> null"
            using assms \<mu> \<tau> comp_ide_source isomorphic_implies_equicomposable match_1
            by blast
          next
          assume \<mu>: "a \<star> \<mu> \<noteq> null"
          show "\<tau> \<star> \<mu> \<noteq> null"
            using assms \<mu> \<tau> comp_ide_source isomorphic_implies_equicomposable match_3
            by blast
        qed
      qed
      show ?thesis
      proof -
        have "arr \<tau>" using assms composable_implies_arr by auto
        thus ?thesis
          using assms * [of "dom \<tau>"] hom_connected(1) by auto
      qed
    qed

    lemma targets_determine_composability:
    assumes "b \<in> targets \<mu>"
    shows "\<tau> \<star> \<mu> \<noteq> null \<longleftrightarrow> \<tau> \<star> b \<noteq> null"
    proof -
      have *: "\<And>\<mu>. ide \<mu> \<and> b \<in> targets \<mu> \<Longrightarrow> \<tau> \<star> \<mu> \<noteq> null \<longleftrightarrow> \<tau> \<star> b \<noteq> null"
      proof -
        fix \<mu>
        assume \<mu>: "ide \<mu> \<and> b \<in> targets \<mu>"
        show "\<tau> \<star> \<mu> \<noteq> null \<longleftrightarrow> \<tau> \<star> b \<noteq> null"
        proof
          assume \<tau>: "\<tau> \<star> \<mu> \<noteq> null"
          show "\<tau> \<star> b \<noteq> null"
            using assms \<mu> \<tau> comp_target_ide isomorphic_implies_equicomposable match_2
            by blast
          next
          assume \<tau>: "\<tau> \<star> b \<noteq> null"
          show "\<tau> \<star> \<mu> \<noteq> null"
            using assms \<mu> \<tau>  comp_target_ide isomorphic_implies_equicomposable match_4
            by blast
        qed
      qed
      show ?thesis
      proof -
        have "arr \<mu>" using assms composable_implies_arr by auto
        thus ?thesis
          using assms * [of "dom \<mu>"] hom_connected(2) by auto
      qed
    qed

    lemma composable_if_connected:
    assumes "sources \<nu> \<inter> targets \<mu> \<noteq> {}"
    shows "\<nu> \<star> \<mu> \<noteq> null"
      using assms targets_determine_composability by blast

    lemma connected_if_composable:
    assumes "\<nu> \<star> \<mu> \<noteq> null"
    shows "sources \<nu> = targets \<mu>"
      using assms sources_determine_composability targets_determine_composability by blast

    lemma iso_hcomp\<^sub>R\<^sub>W\<^sub>C:
    assumes "iso \<mu>" and "iso \<nu>" and "sources \<nu> \<inter> targets \<mu> \<noteq> {}"
    shows "iso (\<nu> \<star> \<mu>)"
    and "inverse_arrows (\<nu> \<star> \<mu>) (inv \<nu> \<star> inv \<mu>)"
    proof -
      have \<mu>: "arr \<mu> \<and> \<guillemotleft>\<mu> : dom \<mu> \<Rightarrow> cod \<mu>\<guillemotright> \<and>
               iso \<mu> \<and> \<guillemotleft>inv \<mu> : cod \<mu> \<Rightarrow> dom \<mu>\<guillemotright>"
        using assms inv_in_hom arr_iff_in_hom iso_is_arr by auto
      have \<nu>: "arr \<nu> \<and> \<guillemotleft>\<nu> : dom \<nu> \<Rightarrow> cod \<nu>\<guillemotright> \<and>
               iso \<nu> \<and> \<guillemotleft>inv \<nu> : cod \<nu> \<Rightarrow> dom \<nu>\<guillemotright>"
        using assms inv_in_hom by blast
      have 1: "sources (inv \<nu>) \<inter> targets (inv \<mu>) \<noteq> {}"
      proof -
        have "sources (inv \<nu>) \<inter> targets (inv \<mu>) = sources \<nu> \<inter> targets \<mu>"
        proof -
          have "sources (inv \<nu>) \<inter> targets (inv \<mu>)
                  = sources (cod (inv \<nu>)) \<inter> targets (cod (inv \<mu>))"
            using assms \<mu> \<nu> sources_cod targets_cod arr_inv by presburger
          also have "... = sources (dom \<nu>) \<inter> targets (dom \<mu>)"
            using \<mu> \<nu> by simp
          also have "... = sources \<nu> \<inter> targets \<mu>"
            using \<mu> \<nu> sources_dom targets_dom by simp
          finally show ?thesis by blast
        qed
        thus ?thesis using assms by simp
      qed
      show "inverse_arrows (\<nu> \<star> \<mu>) (inv \<nu> \<star> inv \<mu>)"
      proof
        have "(inv \<nu> \<star> inv \<mu>) \<cdot> (\<nu> \<star> \<mu>) = dom \<nu> \<star> dom \<mu>"
          using assms \<mu> \<nu> inv_in_hom inv_is_inverse comp_inv_arr
                interchange [of "inv \<nu>" \<nu> "inv \<mu>" \<mu>] composable_if_connected
          by simp
        moreover have "ide (dom \<nu> \<star> dom \<mu>)"
          using assms \<mu> \<nu> ide_hcomp\<^sub>W\<^sub>C composable_if_connected sources_dom targets_dom
          by auto
        ultimately show "ide ((inv \<nu> \<star> inv \<mu>) \<cdot> (\<nu> \<star> \<mu>))"
          by presburger
        have "(\<nu> \<star> \<mu>) \<cdot> (inv \<nu> \<star> inv \<mu>) = cod \<nu> \<star> cod \<mu>"
          using assms 1 \<mu> \<nu> inv_in_hom inv_is_inverse comp_arr_inv
                interchange [of \<nu> "inv \<nu>" \<mu> "inv \<mu>"] composable_if_connected
          by simp
        moreover have "ide (cod \<nu> \<star> cod \<mu>)"
          using assms \<mu> \<nu> ide_hcomp\<^sub>W\<^sub>C composable_if_connected sources_cod targets_cod
          by auto
        ultimately show "ide ((\<nu> \<star> \<mu>) \<cdot> (inv \<nu> \<star> inv \<mu>))"
          by presburger
      qed
      thus "iso (\<nu> \<star> \<mu>)" by auto
    qed

    lemma inv_hcomp\<^sub>R\<^sub>W\<^sub>C:
    assumes "iso \<mu>" and "iso \<nu>" and "sources \<nu> \<inter> targets \<mu> \<noteq> {}"
    shows "inv (\<nu> \<star> \<mu>) = inv \<nu> \<star> inv \<mu>"
      using assms iso_hcomp\<^sub>R\<^sub>W\<^sub>C(2) [of \<mu> \<nu>] inverse_arrow_unique [of "H \<nu> \<mu>"] inv_is_inverse
      by auto

  end

  subsection "Associativity"

  text \<open>
    An \emph{associative weak composition} consists of a weak composition that has been
    equipped with an \emph{associator} isomorphism: \<open>\<guillemotleft>\<a>[f, g, h] : (f \<star> g) \<star> h \<Rightarrow> f \<star> g \<star> h\<guillemotright>\<close>
    for each composable triple \<open>(f, g, h)\<close> of 1-cells, subject to naturality and
    coherence conditions.
  \<close>

  locale associative_weak_composition =
    weak_composition +
  fixes \<a> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"    ("\<a>[_, _, _]")
  assumes assoc_in_vhom\<^sub>A\<^sub>W\<^sub>C:
           "\<lbrakk> ide f; ide g; ide h; f \<star> g \<noteq> null; g \<star> h \<noteq> null \<rbrakk> \<Longrightarrow>
              \<guillemotleft>\<a>[f, g, h] : (f \<star> g) \<star> h \<Rightarrow> f \<star> g \<star> h\<guillemotright>"
  and assoc_naturality\<^sub>A\<^sub>W\<^sub>C:
           "\<lbrakk> \<tau> \<star> \<mu> \<noteq> null; \<mu> \<star> \<nu> \<noteq> null \<rbrakk> \<Longrightarrow>
              \<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> ((\<tau> \<star> \<mu>) \<star> \<nu>) = (\<tau> \<star> \<mu> \<star> \<nu>) \<cdot> \<a>[dom \<tau>, dom \<mu>, dom \<nu>]"
  and iso_assoc\<^sub>A\<^sub>W\<^sub>C: "\<lbrakk> ide f; ide g; ide h; f \<star> g \<noteq> null; g \<star> h \<noteq> null \<rbrakk> \<Longrightarrow> iso \<a>[f, g, h]"
  and pentagon\<^sub>A\<^sub>W\<^sub>C:
           "\<lbrakk> ide f; ide g; ide h; ide k; sources f \<inter> targets g \<noteq> {};
              sources g \<inter> targets h \<noteq> {}; sources h \<inter> targets k \<noteq> {} \<rbrakk> \<Longrightarrow>
              (f \<star> \<a>[g, h, k]) \<cdot> \<a>[f, g \<star> h, k] \<cdot> (\<a>[f, g, h] \<star> k) = \<a>[f, g, h \<star> k] \<cdot> \<a>[f \<star> g, h, k]"
  begin

    lemma assoc_in_hom\<^sub>A\<^sub>W\<^sub>C:
    assumes "ide f" and "ide g" and "ide h"
    and "f \<star> g \<noteq> null" and "g \<star> h \<noteq> null"
    shows "sources \<a>[f, g, h] = sources h" and "targets \<a>[f, g, h] = targets f"
    and "\<guillemotleft>\<a>[f, g, h] : (f \<star> g) \<star> h \<Rightarrow> f \<star> g \<star> h\<guillemotright>"
    proof -
      show 1: "\<guillemotleft>\<a>[f, g, h] : (f \<star> g) \<star> h \<Rightarrow> f \<star> g \<star> h\<guillemotright>"
        using assms assoc_in_vhom\<^sub>A\<^sub>W\<^sub>C by simp
      show "sources \<a>[f, g, h] = sources h"
        using assms 1 sources_dom [of "\<a>[f, g, h]"] sources_hcomp match_3
        by (elim in_homE, auto)
      show "targets \<a>[f, g, h] = targets f"
        using assms 1 targets_cod [of "\<a>[f, g, h]"] targets_hcomp match_4
        by (elim in_homE, auto)
    qed

    lemma assoc_simps\<^sub>A\<^sub>W\<^sub>C [simp]:
    assumes "ide f" and "ide g" and "ide h"
    and "f \<star> g \<noteq> null" and "g \<star> h \<noteq> null"
    shows "arr \<a>[f, g, h]"
    and "dom \<a>[f, g, h] = (f \<star> g) \<star> h"
    and "cod \<a>[f, g, h] = f \<star> g \<star> h"
    proof -
      have 1: "\<guillemotleft>\<a>[f, g, h] : (f \<star> g) \<star> h \<Rightarrow> f \<star> g \<star> h\<guillemotright>"
        using assms assoc_in_hom\<^sub>A\<^sub>W\<^sub>C by auto
      show "arr \<a>[f, g, h]" using 1 by auto
      show "dom \<a>[f, g, h] = (f \<star> g) \<star> h" using 1 by auto
      show "cod \<a>[f, g, h] = f \<star> g \<star> h" using 1 by auto
    qed

    lemma assoc'_in_hom\<^sub>A\<^sub>W\<^sub>C:
    assumes "ide f" and "ide g" and "ide h"
    and "f \<star> g \<noteq> null" and "g \<star> h \<noteq> null"
    shows "sources (inv \<a>[f, g, h]) = sources h" and "targets (inv \<a>[f, g, h]) = targets f"
    and "\<guillemotleft>inv \<a>[f, g, h] :  f \<star> g \<star> h \<Rightarrow> (f \<star> g) \<star> h\<guillemotright>"
    proof -
      show 1: "\<guillemotleft>inv \<a>[f, g, h] :  f \<star> g \<star> h \<Rightarrow> (f \<star> g) \<star> h\<guillemotright>"
        using assms assoc_in_hom\<^sub>A\<^sub>W\<^sub>C iso_assoc\<^sub>A\<^sub>W\<^sub>C inv_in_hom by auto
      show "sources (inv \<a>[f, g, h]) = sources h"
        using assms 1 sources_hcomp [of "f \<star> g" h] sources_cod match_3 null_agreement
        by (elim in_homE, metis)
      show "targets (inv \<a>[f, g, h]) = targets f"
        using assms 1 targets_hcomp [of f "g \<star> h"] targets_dom match_4 null_agreement
        by (elim in_homE, metis)
    qed

    lemma assoc'_simps\<^sub>A\<^sub>W\<^sub>C [simp]:
    assumes "ide f" and "ide g" and "ide h"
    and "f \<star> g \<noteq> null" and "g \<star> h \<noteq> null"
    shows "arr (inv \<a>[f, g, h])"
    and "dom (inv \<a>[f, g, h]) = f \<star> g \<star> h"
    and "cod (inv \<a>[f, g, h]) = (f \<star> g) \<star> h"
    proof -
      have 1: "\<guillemotleft>inv \<a>[f, g, h] : f \<star> g \<star> h \<Rightarrow> (f \<star> g) \<star> h\<guillemotright>"
        using assms assoc'_in_hom\<^sub>A\<^sub>W\<^sub>C by auto
      show "arr (inv \<a>[f, g, h])" using 1 by auto
      show "dom (inv \<a>[f, g, h]) = f \<star> g \<star> h" using 1 by auto
      show "cod (inv \<a>[f, g, h]) = (f \<star> g) \<star> h" using 1 by auto
    qed

    lemma assoc'_naturality\<^sub>A\<^sub>W\<^sub>C:
    assumes "\<tau> \<star> \<mu> \<noteq> null" and "\<mu> \<star> \<nu> \<noteq> null"
    shows "inv \<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> (\<tau> \<star> \<mu> \<star> \<nu>) = ((\<tau> \<star> \<mu>) \<star> \<nu>) \<cdot> inv \<a>[dom \<tau>, dom \<mu>, dom \<nu>]"
    proof -
      have \<tau>\<mu>\<nu>: "arr \<tau> \<and> arr \<mu> \<and> arr \<nu>"
        using assms composable_implies_arr by simp
      have 0: "dom \<tau> \<star> dom \<mu> \<noteq> null \<and> dom \<mu> \<star> dom \<nu> \<noteq> null \<and>
               cod \<tau> \<star> cod \<mu> \<noteq> null \<and> cod \<mu> \<star> cod \<nu> \<noteq> null"
        using assms \<tau>\<mu>\<nu> hom_connected by simp
      have 1: "\<guillemotleft>\<tau> \<star> \<mu> \<star> \<nu> : dom \<tau> \<star> dom \<mu> \<star> dom \<nu> \<Rightarrow> cod \<tau> \<star> cod \<mu> \<star> cod \<nu>\<guillemotright>"
        using assms match_4 by auto
      have 2: "\<guillemotleft>(\<tau> \<star> \<mu>) \<star> \<nu> : (dom \<tau> \<star> dom \<mu>) \<star> dom \<nu> \<Rightarrow> (cod \<tau> \<star> cod \<mu>) \<star> cod \<nu>\<guillemotright>"
        using assms match_3 by auto
      have "(inv \<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> (\<tau> \<star> \<mu> \<star> \<nu>)) \<cdot> \<a>[dom \<tau>, dom \<mu>, dom \<nu>] = (\<tau> \<star> \<mu>) \<star> \<nu>"
      proof -
        have "(\<tau> \<star> \<mu>) \<star> \<nu> = (inv \<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> \<a>[cod \<tau>, cod \<mu>, cod \<nu>]) \<cdot> ((\<tau> \<star> \<mu>) \<star> \<nu>)"
          using 0 2 \<tau>\<mu>\<nu> assoc_in_hom\<^sub>A\<^sub>W\<^sub>C iso_assoc\<^sub>A\<^sub>W\<^sub>C comp_inv_arr inv_is_inverse comp_cod_arr
          by auto
        also have "... = inv \<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> \<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> ((\<tau> \<star> \<mu>) \<star> \<nu>)"
          using comp_assoc by auto
        also have "... = inv \<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> (\<tau> \<star> \<mu> \<star> \<nu>) \<cdot> \<a>[dom \<tau>, dom \<mu>, dom \<nu>]"
          using assms \<tau>\<mu>\<nu> 0 2 assoc_naturality\<^sub>A\<^sub>W\<^sub>C by presburger
        also have "... = (inv \<a>[cod \<tau>, cod \<mu>, cod \<nu>] \<cdot> (\<tau> \<star> \<mu> \<star> \<nu>)) \<cdot> \<a>[dom \<tau>, dom \<mu>, dom \<nu>]"
          using comp_assoc by auto
        finally show ?thesis by argo
      qed
      thus ?thesis
        using 0 1 2 \<tau>\<mu>\<nu> iso_assoc\<^sub>A\<^sub>W\<^sub>C assoc'_in_hom\<^sub>A\<^sub>W\<^sub>C inv_in_hom invert_side_of_triangle(2)
        by auto
      qed

  end

  subsection "Unitors"

  text \<open>
    For an associative weak composition with a chosen unit isomorphism \<open>\<iota> : a \<star> a \<Rightarrow> a\<close>,
    where \<open>a\<close> is a weak unit, horizontal composition on the right by \<open>a\<close> is a fully faithful
    endofunctor \<open>R\<close> of the subcategory of arrows composable on the right with \<open>a\<close>, and is
    consequently an endo-equivalence of that subcategory.  This equivalence, together with the
    associator isomorphisms and unit isomorphism \<open>\<iota>\<close>, canonically associate, with each
    identity arrow \<open>f\<close> composable on the right with \<open>a\<close>, a \emph{right unit} isomorphism
    \<open>\<guillemotleft>\<r>[f] : f \<star> a \<Rightarrow> f\<guillemotright>\<close>.  These isomorphisms are the components of a natural isomorphism
    from \<open>R\<close> to the identity functor.
  \<close>

  locale right_hom_with_unit =
    associative_weak_composition V H \<a> +
    right_hom V H a
  for V :: "'a comp"                  (infixr "\<cdot>" 55)
  and H :: "'a comp"                  (infixr "\<star>" 53)
  and \<a> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"      ("\<a>[_, _, _]")
  and \<iota> :: 'a
  and a :: 'a +
  assumes weak_unit_a: "weak_unit a"
  and \<iota>_in_hom: "\<guillemotleft>\<iota> : a \<star> a \<Rightarrow> a\<guillemotright>"
  and iso_\<iota>: "iso \<iota>"
  begin

    abbreviation R
    where "R \<equiv> H\<^sub>R a"

    interpretation R: endofunctor S.comp R
      using weak_unit_a weak_unit_self_composable endofunctor_H\<^sub>R by simp
    interpretation R: fully_faithful_functor S.comp S.comp R
      using weak_unit_a weak_unit_def by simp

    lemma fully_faithful_functor_R:
    shows "fully_faithful_functor S.comp S.comp R"
      ..

    definition runit  ("\<r>[_]")
    where "runit f \<equiv> THE \<mu>. \<guillemotleft>\<mu> : R f \<Rightarrow>\<^sub>S f\<guillemotright> \<and> R \<mu> = (f \<star> \<iota>) \<cdot>\<^sub>S \<a>[f, a, a]"

    lemma iso_unit:
    shows "S.iso \<iota>" and "\<guillemotleft>\<iota> : a \<star> a \<Rightarrow>\<^sub>S a\<guillemotright>"
    proof -
      show "\<guillemotleft>\<iota> : a \<star> a \<Rightarrow>\<^sub>S a\<guillemotright>"
      proof -
        have a: "weak_unit a \<and> S.ide a"
          using weak_unit_a S.ide_char S.arr_char right_def weak_unit_self_composable
          by metis
        moreover have "S.arr (a \<star> a)"
          using a S.ideD(1) R.preserves_arr H\<^sub>R_def by auto
        ultimately show ?thesis
          using a S.in_hom_char S.arr_char right_def \<iota>_in_hom
          by (metis S.ideD(1) hom_connected(3) in_homE)
      qed
      thus "S.iso \<iota>"
        using iso_\<iota> iso_char by blast
    qed

    lemma characteristic_iso:
    assumes "S.ide f"
    shows "\<guillemotleft>\<a>[f, a, a] : (f \<star> a) \<star> a \<Rightarrow>\<^sub>S f \<star> a \<star> a\<guillemotright>"
    and "\<guillemotleft>f \<star> \<iota> : f \<star> a \<star> a \<Rightarrow>\<^sub>S f \<star> a\<guillemotright>"
    and "\<guillemotleft>(f \<star> \<iota>) \<cdot>\<^sub>S \<a>[f, a, a] : R (R f) \<Rightarrow>\<^sub>S R f\<guillemotright>"
    and "S.iso ((f \<star> \<iota>) \<cdot>\<^sub>S \<a>[f, a, a])"
    proof -
      have f: "S.ide f \<and> ide f"
        using assms S.ide_char by simp
      have a: "weak_unit a \<and> ide a \<and> S.ide a"
        using weak_unit_a S.ide_char weak_unit_def S.arr_char right_def
              weak_unit_self_composable
        by metis
      have fa: "f \<star> a \<noteq> null \<and> (f \<star> a) \<star> a \<noteq> null \<and> ((f \<star> a) \<star> a) \<star> a \<noteq> null"
      proof -
        have "S.arr (f \<star> a) \<and> S.arr ((f \<star> a) \<star> a) \<and> S.arr (((f \<star> a) \<star> a) \<star> a)"
          using assms S.ideD(1) R.preserves_arr H\<^sub>R_def by auto
        thus ?thesis
          using S.not_arr_null by fastforce
      qed
      have aa: "a \<star> a \<noteq> null"
        using a S.ideD(1) R.preserves_arr H\<^sub>R_def S.not_arr_null by auto
      have ia_a: "\<iota> \<star> a \<noteq> null"
        using weak_unit_a hom_connected(3) weak_unit_self_composable \<iota>_in_hom by blast
      have f_ia: "f \<star> \<iota> \<noteq> null"
        using assms S.ide_char right_def S.arr_char hom_connected(4) \<iota>_in_hom by auto
      show assoc_in_hom: "\<guillemotleft>\<a>[f, a, a] : (f \<star> a) \<star> a \<Rightarrow>\<^sub>S f \<star> a \<star> a\<guillemotright>"
        using a f fa hom_connected(1) [of "\<a>[f, a, a]" a] S.arr_char right_def
              match_3 match_4 S.in_hom_char
        by auto
      show 1: "\<guillemotleft>f \<star> \<iota> : f \<star> a \<star> a \<Rightarrow>\<^sub>S f \<star> a\<guillemotright>"
        using a f fa iso_unit
        by (simp add: f_ia ide_in_hom)
      moreover have "S.iso (f \<star> \<iota>)"
        using a f fa f_ia 1 VoV.arr_char VxV.inv_simp
              inv_in_hom hom_connected(2) [of f "inv \<iota>"] VoV.arr_char VoV.iso_char
              preserves_iso iso_char iso_\<iota>
        by auto
      ultimately have unit_part: "\<guillemotleft>f \<star> \<iota> : f \<star> a \<star> a \<Rightarrow>\<^sub>S f \<star> a\<guillemotright> \<and> S.iso (f \<star> \<iota>)"
        by blast
      show "S.iso ((f \<star> \<iota>) \<cdot>\<^sub>S \<a>[f, a, a])"
        using assms a f fa aa hom_connected(1) [of "\<a>[f, a, a]" a] right_def
              iso_assoc\<^sub>A\<^sub>W\<^sub>C iso_char S.arr_char unit_part assoc_in_hom isos_compose
        using S.isos_compose S.seqI' by auto
      show "\<guillemotleft>(f \<star> \<iota>) \<cdot>\<^sub>S \<a>[f, a, a] : R (R f) \<Rightarrow>\<^sub>S R f\<guillemotright>"
        unfolding H\<^sub>R_def using unit_part assoc_in_hom by blast
    qed

    lemma runit_char:
    assumes "S.ide f"
    shows "\<guillemotleft>\<r>[f] : R f \<Rightarrow>\<^sub>S f\<guillemotright>" and "R \<r>[f] = (f \<star> \<iota>) \<cdot>\<^sub>S \<a>[f, a, a]"
    and "\<exists>!\<mu>. \<guillemotleft>\<mu> : R f \<Rightarrow>\<^sub>S f\<guillemotright> \<and> R \<mu> = (f \<star> \<iota>) \<cdot>\<^sub>S \<a>[f, a, a]"
    proof -
      let ?P = "\<lambda>\<mu>. \<guillemotleft>\<mu> : R f \<Rightarrow>\<^sub>S f\<guillemotright> \<and> R \<mu> = (f \<star> \<iota>) \<cdot>\<^sub>S \<a>[f, a, a]"
      show "\<exists>!\<mu>. ?P \<mu>"
      proof -
        have "\<exists>\<mu>. ?P \<mu>"
        proof -
          have 1: "S.ide f"
            using assms S.ide_char S.arr_char by simp
          moreover have "S.ide (R f)"
            using 1 R.preserves_ide by simp
          ultimately show ?thesis
            using assms characteristic_iso(3) R.is_full by blast
        qed
        moreover have "\<forall>\<mu> \<mu>'. ?P \<mu> \<and> ?P \<mu>' \<longrightarrow> \<mu> = \<mu>'"
        proof
          fix \<mu>
          show "\<forall>\<mu>'. ?P \<mu> \<and> ?P \<mu>' \<longrightarrow> \<mu> = \<mu>'"
            using R.is_faithful [of \<mu>] by fastforce
        qed
        ultimately show ?thesis by blast
      qed
      hence "?P (THE \<mu>. ?P \<mu>)"
        using theI' [of ?P] by fastforce
      hence 1: "?P \<r>[f]"
        unfolding runit_def by blast
      show "\<guillemotleft>\<r>[f] : R f \<Rightarrow>\<^sub>S f\<guillemotright>" using 1 by fast
      show "R \<r>[f] = (f \<star> \<iota>) \<cdot>\<^sub>S \<a>[f, a, a]" using 1 by fast
    qed

    lemma iso_runit:
    assumes "S.ide f"
    shows "S.iso \<r>[f]"
      using assms characteristic_iso(4) runit_char R.reflects_iso by metis

    lemma runit_eqI:
    assumes "\<guillemotleft>f : a \<Rightarrow>\<^sub>S b\<guillemotright>" and "\<guillemotleft>\<mu> : R f \<Rightarrow>\<^sub>S f\<guillemotright>"
    and "R \<mu> = ((f \<star> \<iota>) \<cdot>\<^sub>S \<a>[f, a, a])"
    shows "\<mu> = \<r>[f]"
    proof -
      have "S.ide f" using assms(2) S.ide_cod by auto
      thus ?thesis using assms runit_char [of f] by auto
    qed

    lemma runit_naturality:
    assumes "S.arr \<mu>"
    shows "\<r>[S.cod \<mu>] \<cdot>\<^sub>S R \<mu> = \<mu> \<cdot>\<^sub>S \<r>[S.dom \<mu>]"
    proof -
      have 1: "\<guillemotleft>\<r>[S.cod \<mu>] \<cdot>\<^sub>S R \<mu> : R (S.dom \<mu>) \<Rightarrow>\<^sub>S S.cod \<mu>\<guillemotright>"
        using assms runit_char(1) S.ide_cod by blast
      have 2: "S.par (\<r>[S.cod \<mu>] \<cdot>\<^sub>S R \<mu>) (\<mu> \<cdot>\<^sub>S \<r>[S.dom \<mu>])"
      proof -
        have "\<guillemotleft>\<mu> \<cdot>\<^sub>S \<r>[S.dom \<mu>] : R (S.dom \<mu>) \<Rightarrow>\<^sub>S S.cod \<mu>\<guillemotright>"
          using assms S.ide_dom runit_char(1) by blast
        thus ?thesis using 1 by (elim S.in_homE, auto)
      qed
      moreover have "R (\<r>[S.cod \<mu>] \<cdot>\<^sub>S R \<mu>) = R (\<mu> \<cdot>\<^sub>S \<r>[S.dom \<mu>])"
      proof -
        have 3: "\<guillemotleft>\<mu> \<star> a \<star> a : S.dom \<mu> \<star> a \<star> a \<Rightarrow>\<^sub>S S.cod \<mu> \<star> a \<star> a\<guillemotright>"
          using assms weak_unit_a R.preserves_hom H\<^sub>R_def S.arr_iff_in_hom S.arr_char
          by (metis match_4 weak_unit_in_vhom weak_unit_self_right S.in_hom_char
              left_hcomp_closed S.not_arr_null S.null_char)
        have 4: "R (\<r>[S.cod \<mu>] \<cdot>\<^sub>S R \<mu>) = R \<r>[S.cod \<mu>] \<cdot>\<^sub>S R (R \<mu>)"
          using assms 1 R.preserves_comp_2 by blast
        also have 5: "... = ((S.cod \<mu> \<star> \<iota>) \<cdot>\<^sub>S \<a>[S.cod \<mu>, a, a]) \<cdot>\<^sub>S ((\<mu> \<star> a) \<star> a)"
          using assms R.preserves_arr runit_char S.ide_cod H\<^sub>R_def by auto
        also have 6: "... = (S.cod \<mu> \<star> \<iota>) \<cdot>\<^sub>S \<a>[S.cod \<mu>, a, a] \<cdot>\<^sub>S ((\<mu> \<star> a) \<star> a)"
          using assms S.comp_assoc by simp
        also have "... = (S.cod \<mu> \<star> \<iota>) \<cdot>\<^sub>S (\<mu> \<star> a \<star> a) \<cdot>\<^sub>S \<a>[S.dom \<mu>, a, a]"
        proof -
          have "(\<mu> \<star> a \<star> a) \<cdot>\<^sub>S \<a>[S.dom \<mu>, a, a] = \<a>[S.cod \<mu>, a, a] \<cdot>\<^sub>S ((\<mu> \<star> a) \<star> a)"
          proof -
            have "(\<mu> \<star> a \<star> a) \<cdot>\<^sub>S \<a>[S.dom \<mu>, a, a] = (\<mu> \<star> a \<star> a) \<cdot> \<a>[S.dom \<mu>, a, a]"
              using assms 3 S.ide_dom characteristic_iso(1) S.in_hom_char
                    S.comp_char [of "\<mu> \<star> a \<star> a" "\<a>[S.dom \<mu>, a, a]"]
              by fastforce
            also have "... = \<a>[S.cod \<mu>, a, a] \<cdot> ((\<mu> \<star> a) \<star> a)"
            proof -
              have "\<mu> \<star> a \<noteq> null"
                using assms S.arr_char right_def by simp
              thus ?thesis
                using assms weak_unit_a assoc_naturality\<^sub>A\<^sub>W\<^sub>C [of \<mu> a a] by fastforce
            qed
            also have "... = \<a>[S.cod \<mu>, a, a] \<cdot>\<^sub>S ((\<mu> \<star> a) \<star> a)"
              using S.in_hom_char S.comp_char
              by (metis 2 4 5 6 R.preserves_arr S.seq_char)
            finally show ?thesis by blast
          qed
         thus ?thesis by argo
        qed
        also have "... = ((S.cod \<mu> \<star> \<iota>) \<cdot>\<^sub>S (\<mu> \<star> a \<star> a)) \<cdot>\<^sub>S \<a>[S.dom \<mu>, a, a]"
          using S.comp_assoc by auto
        also have "... = ((\<mu> \<star> a) \<cdot>\<^sub>S (S.dom \<mu> \<star> \<iota>)) \<cdot>\<^sub>S \<a>[S.dom \<mu>, a, a]"
        proof -
          have "\<mu> \<star> a \<star> a \<noteq> null"
            using 3 S.not_arr_null by (elim S.in_homE, auto)
          moreover have "S.dom \<mu> \<star> \<iota> \<noteq> null"
            using assms S.not_arr_null
            by (metis S.dom_char \<iota>_in_hom calculation hom_connected(1-2) in_homE)
          ultimately have "(S.cod \<mu> \<star> \<iota>) \<cdot>\<^sub>S (\<mu> \<star> a \<star> a) = (\<mu> \<star> a) \<cdot>\<^sub>S (S.dom \<mu> \<star> \<iota>)"
            using assms weak_unit_a iso_unit S.comp_arr_dom S.comp_cod_arr
                  interchange [of "S.cod \<mu>" \<mu> \<iota> "a \<star> a"] interchange [of \<mu> "S.dom \<mu>" a \<iota>]
            by auto
          thus ?thesis by argo
        qed
        also have "... = (\<mu> \<star> a) \<cdot>\<^sub>S (S.dom \<mu> \<star> \<iota>) \<cdot>\<^sub>S \<a>[S.dom \<mu>, a, a]"
          using S.comp_assoc by auto
        also have "... = R \<mu> \<cdot>\<^sub>S R \<r>[S.dom \<mu>]"
          using assms runit_char(2) S.ide_dom H\<^sub>R_def by auto
        also have "... = R (\<mu> \<cdot>\<^sub>S \<r>[S.dom \<mu>])"
          using assms S.arr_iff_in_hom [of \<mu>] runit_char(1) S.ide_dom by fastforce
        finally show ?thesis by blast
      qed
      ultimately show "\<r>[S.cod \<mu>] \<cdot>\<^sub>S (R \<mu>) = \<mu> \<cdot>\<^sub>S \<r>[S.dom \<mu>]"
        using R.is_faithful by blast
    qed

    abbreviation \<rr>
    where "\<rr> \<mu> \<equiv> if S.arr \<mu> then \<mu> \<cdot>\<^sub>S \<r>[S.dom \<mu>] else null"

    interpretation \<rr>: natural_transformation S.comp S.comp R S.map \<rr>
    proof -
      interpret \<rr>: transformation_by_components S.comp S.comp R S.map runit
        using runit_char(1) runit_naturality by (unfold_locales, simp_all)
      have "\<rr>.map = \<rr>"
        using \<rr>.is_extensional \<rr>.map_def \<rr>.naturality \<rr>.map_simp_ide S.ide_dom S.ide_cod
              S.map_def
        by auto
      thus "natural_transformation S.comp S.comp R S.map \<rr>"
        using \<rr>.natural_transformation_axioms by auto
    qed

    lemma natural_transformation_\<rr>:
    shows "natural_transformation S.comp S.comp R S.map \<rr>" ..

    interpretation \<rr>: natural_isomorphism S.comp S.comp R S.map \<rr>
      using S.ide_is_iso iso_runit runit_char(1) S.isos_compose
      by (unfold_locales, force)

    lemma natural_isomorphism_\<rr>:
    shows "natural_isomorphism S.comp S.comp R S.map \<rr>" ..

    interpretation R: equivalence_functor S.comp S.comp R
      using natural_isomorphism_\<rr> R.isomorphic_to_identity_is_equivalence by blast

    lemma equivalence_functor_R:
    shows "equivalence_functor S.comp S.comp R"
      ..

    lemma runit_commutes_with_R:
    assumes "S.ide f"
    shows "\<r>[R f] = R \<r>[f]"
    proof -
      have "S.seq \<r>[f] (R \<r>[f])"
        using assms runit_char(1) R.preserves_hom [of "\<r>[f]" "R f" f] by fastforce
      moreover have "S.seq \<r>[f] \<r>[R f]"
        using assms runit_char(1) [of f] runit_char(1) [of "R f"] by auto
      ultimately show ?thesis
        using assms runit_char(1) runit_naturality [of "\<r>[f]"] iso_runit S.iso_is_section
              S.section_is_mono S.monoE [of "\<r>[f]" "R \<r>[f]" "\<r>[R f]"]
        by force
    qed

  end

  text \<open>
    Symmetric results hold for the subcategory of all arrows composable on the left with
    a specified weak unit \<open>b\<close>.  This yields the \emph{left unitors}.
  \<close>

  locale left_hom_with_unit =
    associative_weak_composition V H \<a> +
    left_hom V H b
  for V :: "'a comp"                  (infixr "\<cdot>" 55)
  and H :: "'a comp"                  (infixr "\<star>" 53)
  and \<a> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"      ("\<a>[_, _, _]")
  and \<iota> :: 'a
  and b :: 'a +
  assumes weak_unit_b: "weak_unit b"
  and \<iota>_in_hom: "\<guillemotleft>\<iota> : b \<star> b \<Rightarrow> b\<guillemotright>"
  and iso_\<iota>: "iso \<iota>"
  begin

    abbreviation L
    where "L \<equiv> H\<^sub>L b"

    interpretation L: endofunctor S.comp L
      using weak_unit_b weak_unit_self_composable endofunctor_H\<^sub>L by simp
    interpretation L: fully_faithful_functor S.comp S.comp L
      using weak_unit_b weak_unit_def by simp

    lemma fully_faithful_functor_L:
    shows "fully_faithful_functor S.comp S.comp L"
      ..

    definition lunit  ("\<l>[_]")
    where "lunit f \<equiv> THE \<mu>. \<guillemotleft>\<mu> : L f \<Rightarrow>\<^sub>S f\<guillemotright> \<and> L \<mu> = (\<iota> \<star> f) \<cdot>\<^sub>S (inv \<a>[b, b, f])"

    lemma iso_unit:
    shows "S.iso \<iota>" and "\<guillemotleft>\<iota> : b \<star> b \<Rightarrow>\<^sub>S b\<guillemotright>"
    proof -
      show "\<guillemotleft>\<iota> : b \<star> b \<Rightarrow>\<^sub>S b\<guillemotright>"
      proof -
        have b: "weak_unit b \<and> S.ide b"
          using weak_unit_b S.ide_char S.arr_char left_def weak_unit_self_composable
          by metis
        moreover have "S.arr (b \<star> b)"
          using b S.ideD(1) L.preserves_arr H\<^sub>L_def by auto
        ultimately show ?thesis
          using b S.in_hom_char S.arr_char left_def \<iota>_in_hom
          by (metis S.ideD(1) hom_connected(4) in_homE)
      qed
      thus "S.iso \<iota>"
        using iso_\<iota> iso_char by blast
    qed

    lemma characteristic_iso:
    assumes "S.ide f"
    shows "\<guillemotleft>inv \<a>[b, b, f] :  b \<star> b \<star> f \<Rightarrow>\<^sub>S (b \<star> b) \<star> f\<guillemotright>"
    and "\<guillemotleft>\<iota> \<star> f : (b \<star> b) \<star> f \<Rightarrow>\<^sub>S b \<star> f\<guillemotright>"
    and "\<guillemotleft>(\<iota> \<star> f) \<cdot>\<^sub>S inv \<a>[b, b, f] : L (L f) \<Rightarrow>\<^sub>S L f\<guillemotright>"
    and "S.iso ((\<iota> \<star> f) \<cdot>\<^sub>S inv \<a>[b, b, f])"
    proof -
      have f: "S.ide f \<and> ide f"
        using assms S.ide_char by simp
      have b: "weak_unit b \<and> ide b \<and> S.ide b"
        using weak_unit_b S.ide_char weak_unit_def S.arr_char left_def
              weak_unit_self_composable
        by metis
      have bf: "b \<star> f \<noteq> null \<and> b \<star> b \<star> b \<star> f \<noteq> null"
      proof -
        have "S.arr (b \<star> f) \<and> S.arr (b \<star> b \<star> f) \<and> S.arr (b \<star> b \<star> b \<star> f)"
          using assms S.ideD(1) L.preserves_arr H\<^sub>L_def by auto
        thus ?thesis
          using S.not_arr_null by fastforce
      qed
      have bb: "b \<star> b \<noteq> null"
      proof -
        have "S.arr (b \<star> b)"
          using b S.ideD(1) L.preserves_arr H\<^sub>L_def by auto
        thus ?thesis
          using S.not_arr_null by fastforce
      qed
      have b_ib: "b \<star> \<iota> \<noteq> null"
        using weak_unit_b hom_connected(4) weak_unit_self_composable \<iota>_in_hom by blast
      have ib_f: "\<iota> \<star> f \<noteq> null"
        using assms S.ide_char left_def S.arr_char hom_connected(3) \<iota>_in_hom
        by auto
      show assoc_in_hom: "\<guillemotleft>inv \<a>[b, b, f] : b \<star> b \<star> f \<Rightarrow>\<^sub>S (b \<star> b) \<star> f\<guillemotright>"
        using b f bf bb hom_connected(2) [of b "inv \<a>[b, b, f]"] left_def
        by (metis S.arrI S.cod_closed S.in_hom_char assoc'_in_hom\<^sub>A\<^sub>W\<^sub>C(3) assoc'_simps\<^sub>A\<^sub>W\<^sub>C(2-3))
      show 1: "\<guillemotleft>\<iota> \<star> f : (b \<star> b) \<star> f \<Rightarrow>\<^sub>S b \<star> f\<guillemotright>"
        using b f bf by (simp add: ib_f ide_in_hom iso_unit(2))
      moreover have "S.iso (\<iota> \<star> f)"
        using b f bf ib_f 1 VoV.arr_char VxV.inv_simp
              inv_in_hom hom_connected(1) [of "inv \<iota>" f] VoV.arr_char VoV.iso_char
              preserves_iso iso_char iso_\<iota>
        by auto
      ultimately have unit_part: "\<guillemotleft>\<iota> \<star> f : (b \<star> b) \<star> f \<Rightarrow>\<^sub>S b \<star> f\<guillemotright> \<and> S.iso (\<iota> \<star> f)"
        by blast
      show "S.iso ((\<iota> \<star> f) \<cdot>\<^sub>S inv \<a>[b, b, f])"
      proof -
        have "S.iso (inv \<a>[b, b, f])"
          using assms b f bf bb hom_connected(2) [of b "inv \<a>[b, b, f]"] left_def
               iso_assoc\<^sub>A\<^sub>W\<^sub>C iso_inv_iso iso_char S.arr_char left_def
          by simp 
        thus ?thesis       
          using unit_part assoc_in_hom isos_compose by blast
      qed
      show "\<guillemotleft>(\<iota> \<star> f) \<cdot>\<^sub>S inv \<a>[b, b, f] : L (L f) \<Rightarrow>\<^sub>S L f\<guillemotright>"
        unfolding H\<^sub>L_def using unit_part assoc_in_hom by blast
    qed

    lemma lunit_char:
    assumes "S.ide f"
    shows "\<guillemotleft>\<l>[f] : L f \<Rightarrow>\<^sub>S f\<guillemotright>" and "L \<l>[f] = (\<iota> \<star> f) \<cdot>\<^sub>S inv \<a>[b, b, f]"
    and "\<exists>!\<mu>. \<guillemotleft>\<mu> : L f \<Rightarrow>\<^sub>S f\<guillemotright> \<and> L \<mu> = (\<iota> \<star> f) \<cdot>\<^sub>S inv \<a>[b, b, f]"
    proof -
      let ?P = "\<lambda>\<mu>. \<guillemotleft>\<mu> : L f \<Rightarrow>\<^sub>S f\<guillemotright> \<and> L \<mu> = (\<iota> \<star> f) \<cdot>\<^sub>S inv \<a>[b, b, f]"
      show "\<exists>!\<mu>. ?P \<mu>"
      proof -
        have "\<exists>\<mu>. ?P \<mu>"
        proof -
          have 1: "S.ide f"
            using assms S.ide_char S.arr_char by simp
          moreover have "S.ide (L f)"
            using 1 L.preserves_ide by simp
          ultimately show ?thesis
            using assms characteristic_iso(3) L.is_full by blast
        qed
        moreover have "\<forall>\<mu> \<mu>'. ?P \<mu> \<and> ?P \<mu>' \<longrightarrow> \<mu> = \<mu>'"
        proof
          fix \<mu>
          show "\<forall>\<mu>'. ?P \<mu> \<and> ?P \<mu>' \<longrightarrow> \<mu> = \<mu>'"
              using L.is_faithful [of \<mu>] by fastforce
        qed
        ultimately show ?thesis by blast
      qed
      hence "?P (THE \<mu>. ?P \<mu>)"
        using theI' [of ?P] by fastforce
      hence 1: "?P \<l>[f]"
        unfolding lunit_def by blast
      show "\<guillemotleft>\<l>[f] : L f \<Rightarrow>\<^sub>S f\<guillemotright>" using 1 by fast
      show "L \<l>[f] = (\<iota> \<star> f) \<cdot>\<^sub>S inv \<a>[b, b, f]" using 1 by fast
    qed

    lemma iso_lunit:
    assumes "S.ide f"
    shows "S.iso \<l>[f]"
      using assms characteristic_iso(4) lunit_char L.reflects_iso by metis

    lemma lunit_eqI:
    assumes "\<guillemotleft>f : a \<Rightarrow>\<^sub>S b\<guillemotright>" and "\<guillemotleft>\<mu> : L f \<Rightarrow>\<^sub>S f\<guillemotright>"
    and "L \<mu> = ((\<iota> \<star> f) \<cdot>\<^sub>S inv \<a>[b, b, f])"
    shows "\<mu> = \<l>[f]"
    proof -
      have "S.ide f" using assms(2) S.ide_cod by auto
      thus ?thesis using assms lunit_char [of f] by auto
    qed

    lemma lunit_naturality:
    assumes "S.arr \<mu>"
    shows "\<l>[S.cod \<mu>] \<cdot>\<^sub>S L \<mu> = \<mu> \<cdot>\<^sub>S \<l>[S.dom \<mu>]"
    proof -
      have 1: "\<guillemotleft>\<l>[S.cod \<mu>] \<cdot>\<^sub>S L \<mu> : L (S.dom \<mu>) \<Rightarrow>\<^sub>S S.cod \<mu>\<guillemotright>"
        using assms lunit_char(1) [of "S.cod \<mu>"] S.ide_cod by blast
      have "S.par (\<l>[S.cod \<mu>] \<cdot>\<^sub>S L \<mu>) (\<mu> \<cdot>\<^sub>S \<l>[S.dom \<mu>])"
      proof -
        have "\<guillemotleft>\<mu> \<cdot>\<^sub>S \<l>[S.dom \<mu>] : L (S.dom \<mu>) \<Rightarrow>\<^sub>S S.cod \<mu>\<guillemotright>"
          using assms S.ide_dom lunit_char(1) by blast
        thus ?thesis using 1 by (elim S.in_homE, auto)
      qed
      moreover have "L (\<l>[S.cod \<mu>] \<cdot>\<^sub>S L \<mu>) = L (\<mu> \<cdot>\<^sub>S \<l>[S.dom \<mu>])"
      proof -
        have 2: "\<guillemotleft>b \<star> b \<star> \<mu> : b \<star> b \<star> S.dom \<mu> \<Rightarrow>\<^sub>S b \<star> b \<star> S.cod \<mu>\<guillemotright>"
          using assms weak_unit_b L.preserves_hom H\<^sub>L_def S.arr_iff_in_hom [of \<mu>] S.arr_char
          by simp
        have 3: "\<guillemotleft>(b \<star> b) \<star> \<mu> : (b \<star> b) \<star> S.dom \<mu> \<Rightarrow>\<^sub>S (b \<star> b) \<star> S.cod \<mu>\<guillemotright>"
          using assms weak_unit_b L.preserves_hom H\<^sub>L_def S.arr_iff_in_hom S.arr_char
          by (metis match_3 weak_unit_in_vhom weak_unit_self_left S.in_hom_char
              S.not_arr_null S.null_char right_hcomp_closed)

        have "L (\<l>[S.cod \<mu>] \<cdot>\<^sub>S L \<mu>) = L \<l>[S.cod \<mu>] \<cdot>\<^sub>S L (L \<mu>)"
          using assms 1 L.preserves_comp_2 by blast
        also have "... = ((\<iota> \<star> S.cod \<mu>) \<cdot>\<^sub>S inv \<a>[b, b, S.cod \<mu>]) \<cdot>\<^sub>S (b \<star> b \<star> \<mu>)"
          using assms L.preserves_arr lunit_char S.ide_cod H\<^sub>L_def by auto
        also have "... = (\<iota> \<star> S.cod \<mu>) \<cdot>\<^sub>S inv \<a>[b, b, S.cod \<mu>] \<cdot>\<^sub>S (b \<star> b \<star> \<mu>)"
          using S.comp_assoc by auto
        also have "... = (\<iota> \<star> S.cod \<mu>) \<cdot>\<^sub>S ((b \<star> b) \<star> \<mu>) \<cdot>\<^sub>S inv \<a>[b, b, S.dom \<mu>]"
        proof -
          have "inv \<a>[b, b, S.cod \<mu>] \<cdot>\<^sub>S (b \<star> b \<star> \<mu>) = ((b \<star> b) \<star> \<mu>) \<cdot>\<^sub>S inv \<a>[b, b, S.dom \<mu>]"
          proof -
            have "((b \<star> b) \<star> \<mu>) \<cdot>\<^sub>S inv \<a>[b, b, S.dom \<mu>] = ((b \<star> b) \<star> \<mu>) \<cdot> inv \<a>[b, b, S.dom \<mu>]"
              using assms 3 S.in_hom_char S.comp_char [of "(b \<star> b) \<star> \<mu>" "inv \<a>[b, b, S.dom \<mu>]"]
              by (metis S.ide_dom characteristic_iso(1) ext)
            also have "... = inv \<a>[b, b, S.cod \<mu>] \<cdot> (b \<star> b \<star> \<mu>)"
            proof -
              have "b \<star> \<mu> \<noteq> null"
                using assms S.arr_char left_def by simp
              thus ?thesis
                using assms weak_unit_b assoc'_naturality\<^sub>A\<^sub>W\<^sub>C [of b b \<mu>] by fastforce
            qed
            also have "... = inv \<a>[b, b, S.cod \<mu>] \<cdot>\<^sub>S (b \<star> b \<star> \<mu>)"
              using assms 2 S.in_hom_char S.comp_char
              by (metis S.comp_simp S.ide_cod S.seqI' characteristic_iso(1))
            finally show ?thesis by argo
          qed
         thus ?thesis by argo
        qed
        also have "... = ((\<iota> \<star> S.cod \<mu>) \<cdot>\<^sub>S ((b \<star> b) \<star> \<mu>)) \<cdot>\<^sub>S inv \<a>[b, b, S.dom \<mu>]"
          using S.comp_assoc by auto
        also have "... = ((b \<star> \<mu>) \<cdot>\<^sub>S (\<iota> \<star> S.dom \<mu>)) \<cdot>\<^sub>S inv \<a>[b, b, S.dom \<mu>]"
        proof -
          have "(b \<star> b) \<star> \<mu> \<noteq> null"
            using 3 S.not_arr_null by (elim S.in_homE, auto)
          moreover have "\<iota> \<star> S.dom \<mu> \<noteq> null"
            using assms S.not_arr_null
            by (metis S.dom_char \<iota>_in_hom calculation hom_connected(1-2) in_homE)
          ultimately have "(\<iota> \<star> S.cod \<mu>) \<cdot>\<^sub>S ((b \<star> b) \<star> \<mu>) = (b \<star> \<mu>) \<cdot>\<^sub>S (\<iota> \<star> S.dom \<mu>)"
            using assms weak_unit_b iso_unit S.comp_arr_dom S.comp_cod_arr
                  interchange [of \<iota> "b \<star> b" "S.cod \<mu>" \<mu> ] interchange [of b \<iota> \<mu> "S.dom \<mu>"]
            by auto
          thus ?thesis by argo
        qed
        also have "... = (b \<star> \<mu>) \<cdot>\<^sub>S (\<iota> \<star> S.dom \<mu>) \<cdot>\<^sub>S inv \<a>[b, b, S.dom \<mu>]"
          using S.comp_assoc by auto
        also have "... = L \<mu> \<cdot>\<^sub>S L \<l>[S.dom \<mu>]"
          using assms lunit_char(2) S.ide_dom H\<^sub>L_def by auto
        also have "... = L (\<mu> \<cdot>\<^sub>S \<l>[S.dom \<mu>])"
          using assms S.arr_iff_in_hom [of \<mu>] lunit_char(1) S.ide_dom S.seqI
          by fastforce
        finally show ?thesis by blast
      qed
      ultimately show "\<l>[S.cod \<mu>] \<cdot>\<^sub>S L \<mu> = \<mu> \<cdot>\<^sub>S \<l>[S.dom \<mu>]"
        using L.is_faithful by blast
    qed

    abbreviation \<ll>
    where "\<ll> \<mu> \<equiv> if S.arr \<mu> then \<mu> \<cdot>\<^sub>S \<l>[S.dom \<mu>] else null"

    interpretation \<ll>: natural_transformation S.comp S.comp L S.map \<ll>
    proof -
      interpret \<ll>: transformation_by_components S.comp S.comp L S.map lunit
        using lunit_char(1) lunit_naturality by (unfold_locales, simp_all)
      have "\<ll>.map = \<ll>"
        using \<ll>.is_extensional \<ll>.map_def \<ll>.naturality \<ll>.map_simp_ide S.ide_dom S.ide_cod
              S.map_def
        by auto
      thus "natural_transformation S.comp S.comp L S.map \<ll>"
        using \<ll>.natural_transformation_axioms by auto
    qed

    lemma natural_transformation_\<ll>:
    shows "natural_transformation S.comp S.comp L S.map \<ll>" ..

    interpretation \<ll>: natural_isomorphism S.comp S.comp L S.map \<ll>
      using S.ide_is_iso iso_lunit lunit_char(1) S.isos_compose
      by (unfold_locales, force)

    lemma natural_isomorphism_\<ll>:
    shows "natural_isomorphism S.comp S.comp L S.map \<ll>" ..

    interpretation L: equivalence_functor S.comp S.comp L
      using natural_isomorphism_\<ll> L.isomorphic_to_identity_is_equivalence by blast

    lemma equivalence_functor_L:
    shows "equivalence_functor S.comp S.comp L"
      ..

    lemma lunit_commutes_with_L:
    assumes "S.ide f"
    shows "\<l>[L f] = L \<l>[f]"
    proof -
      have "S.seq \<l>[f] (L \<l>[f])"
        using assms lunit_char(1) L.preserves_hom [of "\<l>[f]" "L f" f] by fastforce
      moreover have "S.seq \<l>[f] \<l>[L f]"
        using assms lunit_char(1) [of f] lunit_char(1) [of "L f"] by auto
      ultimately show ?thesis
        using assms lunit_char(1) lunit_naturality [of "\<l>[f]"] iso_lunit S.iso_is_section
              S.section_is_mono S.monoE [of "\<l>[f]" "L \<l>[f]" "\<l>[L f]"]
        by force
    qed

  end

  subsection "Prebicategories"

  text \<open>
    A \emph{prebicategory} is an associative weak composition satisfying the additional assumption
    that every arrow has a source and a target.
  \<close>

  locale prebicategory =
    associative_weak_composition +
  assumes arr_has_source: "arr \<mu> \<Longrightarrow> sources \<mu> \<noteq> {}"
  and arr_has_target: "arr \<mu> \<Longrightarrow> targets \<mu> \<noteq> {}"
  begin

    lemma arr_iff_has_src:
    shows "arr \<mu> \<longleftrightarrow> sources \<mu> \<noteq> {}"
      using arr_has_source composable_implies_arr by auto

    lemma arr_iff_has_trg:
    shows "arr \<mu> \<longleftrightarrow> targets \<mu> \<noteq> {}"
      using arr_has_target composable_implies_arr by auto

  end

  text \<open>
    The horizontal composition of a prebicategory is regular.
  \<close>

  sublocale prebicategory \<subseteq> regular_weak_composition V H
  proof
    show "\<And>a f. a \<in> sources f \<Longrightarrow> ide f \<Longrightarrow> f \<star> a \<cong> f"
    proof -
      fix a f
      assume a: "a \<in> sources f" and f: "ide f"
      interpret Right_a: subcategory V \<open>right a\<close>
        using a right_hom_is_subcategory weak_unit_self_composable by force
      interpret Right_a: right_hom_with_unit V H \<a> \<open>some_unit a\<close> a
        using a iso_some_unit by (unfold_locales, auto)
      show "f \<star> a \<cong> f"
      proof -
        have "Right_a.ide f"
          using a f Right_a.ide_char Right_a.arr_char right_def by auto
        hence "Right_a.iso (Right_a.runit f) \<and> (Right_a.runit f) \<in> Right_a.hom (f \<star> a) f"
          using Right_a.iso_runit Right_a.runit_char(1) H\<^sub>R_def by simp
        hence "iso (Right_a.runit f) \<and> (Right_a.runit f) \<in> hom (f \<star> a) f"
          using Right_a.iso_char Right_a.hom_char by auto
        thus ?thesis using f isomorphic_def by auto
      qed
    qed
    show "\<And>b f. b \<in> targets f \<Longrightarrow> ide f \<Longrightarrow> b \<star> f \<cong> f"
    proof -
      fix b f
      assume b: "b \<in> targets f" and f: "ide f"
      interpret Left_b: subcategory V \<open>left b\<close>
        using b left_hom_is_subcategory weak_unit_self_composable by force
      interpret Left_b: left_hom_with_unit V H \<a> \<open>some_unit b\<close> b
        using b iso_some_unit by (unfold_locales, auto)
      show "b \<star> f \<cong> f"
      proof -
        have "Left_b.ide f"
          using b f Left_b.ide_char Left_b.arr_char left_def by auto
        hence "Left_b.iso (Left_b.lunit f) \<and> (Left_b.lunit f) \<in> Left_b.hom (b \<star> f) f"
          using b f Left_b.iso_lunit Left_b.lunit_char(1) H\<^sub>L_def by simp
        hence "iso (Left_b.lunit f) \<and> (Left_b.lunit f) \<in> hom (b \<star> f) f"
          using Left_b.iso_char Left_b.hom_char by auto
        thus ?thesis using isomorphic_def by auto
      qed
    qed
  qed

  text \<open>
    The regularity allows us to show that, in a prebicategory, all sources of
    a given arrow are isomorphic, and similarly for targets.
  \<close>

  context prebicategory
  begin

    lemma sources_are_isomorphic:
    assumes "a \<in> sources \<mu>" and "a' \<in> sources \<mu>"
    shows "a \<cong> a'"
    proof -
      have \<mu>: "arr \<mu>" using assms composable_implies_arr by auto
      have 0: "\<And>f. \<lbrakk> ide f; a \<in> sources f; a' \<in> sources f \<rbrakk> \<Longrightarrow> a \<cong> a'"
      proof -
        fix f
        assume f: "ide f" and a: "a \<in> sources f" and a': "a' \<in> sources f"
        have 1: "a \<star> a' \<noteq> null"
          using a a' f \<mu> assms(1) sources_determine_composability sourcesD(2-3) by meson
        have 2: "a \<in> targets a' \<and> a' \<in> sources a"
          using assms 1 by blast
        show "a \<cong> a'"
          using a a' 1 2 comp_ide_source comp_target_ide [of a a']
                weak_unit_self_composable(1) [of a] weak_unit_self_composable(1) [of a']
                isomorphic_transitive isomorphic_symmetric
          by blast
      qed
      have "ide (dom \<mu>) \<and> a \<in> sources (dom \<mu>) \<and> a' \<in> sources (dom \<mu>)"
        using assms \<mu> sources_dom by auto
      thus ?thesis using 0 by auto
    qed
      
    lemma targets_are_isomorphic:
    assumes "b \<in> targets \<mu>" and "b' \<in> targets \<mu>"
    shows "b \<cong> b'"
    proof -
      have \<mu>: "arr \<mu>" using assms composable_implies_arr by auto
      have 0: "\<And>f. \<lbrakk> ide f; b \<in> targets f; b' \<in> targets f \<rbrakk> \<Longrightarrow> b \<cong> b'"
      proof -
        fix f
        assume f: "ide f" and b: "b \<in> targets f" and b': "b' \<in> targets f"
        have 1: "b \<star> b' \<noteq> null"
          using b b' f \<mu> assms(1) targets_determine_composability targetsD(2-3) by meson
        have 2: "b \<in> targets b' \<and> b' \<in> sources b"
          using assms 1 by blast
        show "b \<cong> b'"
          using b b' 1 2 comp_ide_source comp_target_ide [of b b']
                weak_unit_self_composable(1) [of b] weak_unit_self_composable(1) [of b']
                isomorphic_transitive isomorphic_symmetric
          by blast
      qed
      have "ide (dom \<mu>) \<and> b \<in> targets (dom \<mu>) \<and> b' \<in> targets (dom \<mu>)"
        using assms \<mu> targets_dom [of \<mu>] by auto
      thus ?thesis using 0 by auto
    qed

    text \<open>
      In fact, we now show that the sets of sources and targets of a 2-cell are
      isomorphism-closed, and hence are isomorphism classes.
      We first show that the notion ``weak unit'' is preserved under isomorphism.
    \<close>

    interpretation H: partial_magma H
      using is_partial_magma by auto

    lemma isomorphism_respects_weak_units:
    assumes "weak_unit a" and "a \<cong> a'"
    shows "weak_unit a'"
    proof -
      obtain \<phi> where \<phi>: "iso \<phi> \<and> \<guillemotleft>\<phi> : a \<Rightarrow> a'\<guillemotright>"
        using assms by auto
      interpret Left_a: subcategory V \<open>left a\<close>
        using assms left_hom_is_subcategory by fastforce
      interpret Left_a: left_hom_with_unit V H \<a> \<open>some_unit a\<close> a
        using assms iso_some_unit
        apply unfold_locales by auto
      interpret Right_a: subcategory V "right a"
        using assms right_hom_is_subcategory by fastforce
      interpret Right_a: right_hom_with_unit V H \<a> \<open>some_unit a\<close> a
        using assms iso_some_unit
        apply unfold_locales by auto
      have a': "ide a' \<and> a \<star> a' \<noteq> null \<and> a' \<star> a \<noteq> null \<and> a' \<star> a' \<noteq> null \<and>
                \<phi> \<star> a' \<noteq> null \<and> Left_a.ide a'"
        using assms \<phi> weak_unit_self_composable hom_connected
              Left_a.ide_char Left_a.arr_char left_def
        apply auto
            apply (meson weak_unit_self_composable(3) isomorphic_implies_equicomposable)
           apply (meson weak_unit_self_composable(3) isomorphic_implies_equicomposable)
          apply (meson weak_unit_self_composable(3) isomorphic_implies_equicomposable)
         apply (metis weak_unit_self_composable(3) in_homE)
        by (meson weak_unit_self_composable(3) isomorphic_implies_equicomposable)
      have iso: "a' \<star> a' \<cong> a'"
      proof -
        have 1: "Right a' = Right a"
          using assms right_respects_isomorphic by simp
        interpret Right_a': subcategory V \<open>right a'\<close>
          using assms right_hom_is_subcategory by fastforce
        (* TODO: The previous interpretation brings in unwanted notation for in_hom. *)
        interpret Ra': endofunctor \<open>Right a'\<close> \<open>H\<^sub>R a'\<close>
          using assms a' endofunctor_H\<^sub>R by auto
        let ?\<psi> = "Left_a.lunit a' \<cdot> inv (\<phi> \<star> a')"
        have "iso ?\<psi> \<and> \<guillemotleft>?\<psi> : a' \<star> a' \<Rightarrow> a'\<guillemotright>"
        proof -
          have "iso (Left_a.lunit a') \<and> \<guillemotleft>Left_a.lunit a' : a \<star> a' \<Rightarrow> a'\<guillemotright>"
            using a' Left_a.lunit_char(1) Left_a.iso_lunit Left_a.iso_char
                  Left_a.in_hom_char H\<^sub>L_def
            by auto
          moreover have "iso (\<phi> \<star> a') \<and> \<guillemotleft>\<phi> \<star> a' : a \<star> a' \<Rightarrow> a' \<star> a'\<guillemotright>"
          proof -
            have 1: "Right_a'.iso \<phi> \<and> \<phi> \<in> Right_a'.hom (Right_a'.dom \<phi>) (Right_a'.cod \<phi>)"
              using a' \<phi> Right_a'.iso_char Right_a'.arr_char right_def right_iff_right_inv
                    Right_a'.arr_iff_in_hom [of \<phi>]
              by simp
            have "Right_a'.iso (H\<^sub>R a' \<phi>) \<and>
                  Right_a'.in_hom (H\<^sub>R a' \<phi>) (H\<^sub>R a' (Right_a'.dom \<phi>)) (H\<^sub>R a' (Right_a'.cod \<phi>))"
              using \<phi> 1 Ra'.preserves_iso Ra'.preserves_hom Right_a'.iso_char
                    Ra'.preserves_dom Ra'.preserves_cod Right_a'.arr_iff_in_hom [of "H\<^sub>R a' \<phi>"]
              by simp
            thus ?thesis
              using \<phi> 1 Right_a'.in_hom_char Right_a'.iso_char H\<^sub>R_def by auto
          qed
          ultimately show ?thesis
            using isos_compose iso_inv_iso inv_in_hom by blast
        qed
        thus ?thesis using isomorphic_def by auto
      qed
      text \<open>
        We show that horizontal composition on the left and right by @{term a'}
        is naturally isomorphic to the identity functor.  This follows from the fact
        that if @{term a} is isomorphic to @{term a'}, then horizontal composition with @{term a}
        is naturally isomorphic to horizontal composition with @{term a'}, hence the latter is
        naturally isomorphic to the identity if the former is.
        This is conceptually simple, but there are tedious composability details to handle.
      \<close>  
      have 1: "Left a' = Left a \<and> Right a' = Right a"
        using assms left_respects_isomorphic right_respects_isomorphic by simp
      interpret L: fully_faithful_functor \<open>Left a\<close> \<open>Left a\<close> \<open>H\<^sub>L a\<close>
        using assms weak_unit_def by simp
      interpret L': endofunctor \<open>Left a\<close> \<open>H\<^sub>L a'\<close>
        using a' 1 endofunctor_H\<^sub>L [of a'] by auto
      interpret \<Phi>: natural_isomorphism \<open>Left a\<close> \<open>Left a\<close> \<open>H\<^sub>L a\<close> \<open>H\<^sub>L a'\<close> \<open>H\<^sub>L \<phi>\<close>
      proof
        fix \<mu>
        show "\<not> Left_a.arr \<mu> \<Longrightarrow> H\<^sub>L \<phi> \<mu> = Left_a.null"
          using left_def \<phi> H\<^sub>L_def hom_connected(1) Left_a.null_char null_agreement
                Left_a.arr_char
          by auto
        assume "Left_a.arr \<mu>"
        hence \<mu>: "Left_a.arr \<mu> \<and> arr \<mu> \<and> a \<star> \<mu> \<noteq> null"
          using Left_a.arr_char left_def composable_implies_arr by simp
        have 2: "\<phi> \<star> \<mu> \<noteq> null"
          using assms \<phi> \<mu> Left_a.arr_char left_def hom_connected by auto
        show "Left_a.dom (H\<^sub>L \<phi> \<mu>) = H\<^sub>L a (Left_a.dom \<mu>)"
          using assms 2 \<phi> \<mu> Left_a.arr_char left_def hom_connected(2) [of a \<phi>]
                weak_unit_self_composable match_4 Left_a.dom_char H\<^sub>L_def by auto
        show "Left_a.cod (H\<^sub>L \<phi> \<mu>) = H\<^sub>L a' (Left_a.cod \<mu>)"
          using assms 2 \<phi> \<mu> Left_a.arr_char left_def hom_connected(2) [of a \<phi>]
                weak_unit_self_composable match_4 Left_a.cod_char H\<^sub>L_def
          by auto
        show "Left_a.comp (H\<^sub>L a' \<mu>) (H\<^sub>L \<phi> (Left_a.dom \<mu>)) = H\<^sub>L \<phi> \<mu>"
        proof -
          have "Left_a.comp (H\<^sub>L a' \<mu>) (H\<^sub>L \<phi> (Left_a.dom \<mu>)) =
                Left_a.comp (a' \<star> \<mu>) (\<phi> \<star> dom \<mu>)"
            using assms 1 2 \<phi> \<mu> Left_a.dom_char left_def H\<^sub>L_def by simp
          also have "... = (a' \<star> \<mu>) \<cdot> (\<phi> \<star> dom \<mu>)"
          proof -
            have "Left_a.seq (a' \<star> \<mu>) (\<phi> \<star> dom \<mu>)"
            proof (intro Left_a.seqI)
              show 3: "Left_a.arr (\<phi> \<star> dom \<mu>)"
                using assms 2 \<phi> \<mu> Left_a.arr_char left_def
                by (metis H\<^sub>L_def L'.preserves_arr hcomp_simps\<^sub>W\<^sub>C(1) in_homE right_connected
                    paste_1)
              show 4: "Left_a.arr (a' \<star> \<mu>)"
                using \<mu> H\<^sub>L_def L'.preserves_arr by auto
              show "Left_a.dom (a' \<star> \<mu>) = Left_a.cod (\<phi> \<star> dom \<mu>)"
                using a' \<phi> \<mu> 2 3 4 Left_a.dom_char Left_a.cod_char
                by (metis Left_a.seqE Left_a.seq_char hcomp_simps\<^sub>W\<^sub>C(1) in_homE paste_1)
            qed
            thus ?thesis using Left_a.comp_char Left_a.arr_char left_def by auto
          qed
          also have "... = a' \<cdot> \<phi> \<star> \<mu> \<cdot> dom \<mu>"
            using a' \<phi> \<mu> interchange hom_connected by auto
          also have "... = \<phi> \<star> \<mu>"
            using \<phi> \<mu> comp_arr_dom comp_cod_arr by auto
          finally show ?thesis using H\<^sub>L_def by simp
        qed
        show "Left_a.comp (H\<^sub>L \<phi> (Left_a.cod \<mu>)) (Left_a.L \<mu>) = H\<^sub>L \<phi> \<mu>"
        proof -
          have "Left_a.comp (H\<^sub>L \<phi> (Left_a.cod \<mu>)) (Left_a.L \<mu>) = Left_a.comp (\<phi> \<star> cod \<mu>) (a \<star> \<mu>)"
            using assms 1 2 \<phi> \<mu> Left_a.cod_char left_def H\<^sub>L_def by simp
          also have "... = (\<phi> \<star> cod \<mu>) \<cdot> (a \<star> \<mu>)"
          proof -
            have "Left_a.seq (\<phi> \<star> cod \<mu>) (a \<star> \<mu>)"
            proof (intro Left_a.seqI)
              show 3: "Left_a.arr (\<phi> \<star> cod \<mu>)"
                using \<phi> \<mu> 2 Left_a.arr_char left_def
                by (metis (no_types, lifting) H\<^sub>L_def L.preserves_arr hcomp_simps\<^sub>W\<^sub>C(1)
                    in_homE right_connected paste_2)
              show 4: "Left_a.arr (a \<star> \<mu>)"
                using assms \<mu> Left_a.arr_char left_def
                using H\<^sub>L_def L.preserves_arr by auto
              show "Left_a.dom (\<phi> \<star> cod \<mu>) = Left_a.cod (a \<star> \<mu>)"
                using assms \<phi> \<mu> 2 3 4 Left_a.dom_char Left_a.cod_char
                by (metis Left_a.seqE Left_a.seq_char hcomp_simps\<^sub>W\<^sub>C(1) in_homE paste_2)
            qed
            thus ?thesis using Left_a.comp_char Left_a.arr_char left_def by auto
          qed
          also have "... = \<phi> \<cdot> a \<star> cod \<mu> \<cdot> \<mu>"
            using \<phi> \<mu> interchange hom_connected by auto
          also have "... = \<phi> \<star> \<mu>"
            using \<phi> \<mu> comp_arr_dom comp_cod_arr by auto
          finally show ?thesis using H\<^sub>L_def by simp
        qed
        next
        fix \<mu>
        assume \<mu>: "Left_a.ide \<mu>"
        have 1: "\<phi> \<star> \<mu> \<noteq> null"
          using assms \<phi> \<mu> Left_a.ide_char Left_a.arr_char left_def hom_connected by auto
        show "Left_a.iso (H\<^sub>L \<phi> \<mu>)"
        proof -
          have "iso (\<phi> \<star> \<mu>)"
          proof -
            have "a \<in> sources \<phi> \<inter> targets \<mu>"
              using assms \<phi> \<mu> 1 hom_connected weak_unit_self_composable
                    Left_a.ide_char Left_a.arr_char left_def connected_if_composable
              by auto
            thus ?thesis
              using \<phi> \<mu> Left_a.ide_char ide_is_iso iso_hcomp\<^sub>R\<^sub>W\<^sub>C(1) by blast
          qed
          moreover have "left a (\<phi> \<star> \<mu>)"
            using assms 1 \<phi> weak_unit_self_composable hom_connected(2) [of a \<phi>]
                  left_def match_4 null_agreement
            by auto
          ultimately show ?thesis
            using Left_a.iso_char Left_a.arr_char left_iff_left_inv Left_a.inv_char H\<^sub>L_def
            by simp
        qed
      qed
      interpret L': equivalence_functor \<open>Left a'\<close> \<open>Left a'\<close> \<open>H\<^sub>L a'\<close>
      proof -
        have "naturally_isomorphic (Left a) (Left a) (H\<^sub>L a) Left_a.map"
          using assms Left_a.natural_isomorphism_\<ll> naturally_isomorphic_def by blast
        moreover have "naturally_isomorphic (Left a) (Left a) (H\<^sub>L a) (H\<^sub>L a')"
          using naturally_isomorphic_def \<Phi>.natural_isomorphism_axioms by blast
        ultimately have "naturally_isomorphic (Left a) (Left a) (H\<^sub>L a')
                                              (identity_functor.map (Left a))"
          using naturally_isomorphic_symmetric naturally_isomorphic_transitive by fast
        hence "naturally_isomorphic (Left a') (Left a') (H\<^sub>L a') (identity_functor.map (Left a'))"
          using 1 by auto
        thus "equivalence_functor (Left a') (Left a') (H\<^sub>L a')"
          using 1 L'.isomorphic_to_identity_is_equivalence naturally_isomorphic_def by fastforce
      qed

      text \<open>
        Now we do the same for \<open>R'\<close>.
      \<close>
      interpret R: fully_faithful_functor \<open>Right a\<close> \<open>Right a\<close> \<open>H\<^sub>R a\<close>
        using assms weak_unit_def by simp
      interpret R': endofunctor \<open>Right a\<close> \<open>H\<^sub>R a'\<close>
        using a' 1 endofunctor_H\<^sub>R [of a'] by auto
      interpret \<Psi>: natural_isomorphism \<open>Right a\<close> \<open>Right a\<close> \<open>H\<^sub>R a\<close> \<open>H\<^sub>R a'\<close> \<open>H\<^sub>R \<phi>\<close>
      proof
        fix \<mu>
        show "\<not> Right_a.arr \<mu> \<Longrightarrow> H\<^sub>R \<phi> \<mu> = Right_a.null"
          using right_def \<phi> H\<^sub>R_def hom_connected Right_a.null_char Right_a.arr_char
          by auto
        assume "Right_a.arr \<mu>"
        hence \<mu>: "Right_a.arr \<mu> \<and> arr \<mu> \<and> \<mu> \<star> a \<noteq> null"
          using Right_a.arr_char right_def composable_implies_arr by simp
        have 2: "\<mu> \<star> \<phi> \<noteq> null"
          using assms \<phi> \<mu> Right_a.arr_char right_def hom_connected by auto
        show "Right_a.dom (H\<^sub>R \<phi> \<mu>) = H\<^sub>R a (Right_a.dom \<mu>)"
          using assms 2 \<phi> \<mu> Right_a.arr_char right_def hom_connected(1) [of \<phi> a]
                weak_unit_self_composable match_3 Right_a.dom_char H\<^sub>R_def
          by auto
        show "Right_a.cod (H\<^sub>R \<phi> \<mu>) = H\<^sub>R a' (Right_a.cod \<mu>)"
          using assms 2 a' \<phi> \<mu> Right_a.arr_char right_def hom_connected(3) [of \<phi> a]
                weak_unit_self_composable match_3 Right_a.cod_char H\<^sub>R_def
          by auto
        show "Right_a.comp (H\<^sub>R a' \<mu>) (H\<^sub>R \<phi> (Right_a.dom \<mu>)) = H\<^sub>R \<phi> \<mu>"
        proof -
          have "Right_a.comp (H\<^sub>R a' \<mu>) (H\<^sub>R \<phi> (Right_a.dom \<mu>)) =
                Right_a.comp (\<mu> \<star> a') (dom \<mu> \<star> \<phi>)"
            using assms 1 2 \<phi> \<mu> Right_a.dom_char right_def H\<^sub>R_def by simp
          also have "... = (\<mu> \<star> a') \<cdot> (dom \<mu> \<star> \<phi>)"
          proof -
            have "Right_a.seq (\<mu> \<star> a') (dom \<mu> \<star> \<phi>)"
            proof (intro Right_a.seqI)
              show 3: "Right_a.arr (dom \<mu> \<star> \<phi>)"
                using assms 2 \<phi> \<mu> Right_a.arr_char right_def
                by (metis H\<^sub>R_def R'.preserves_arr hcomp_simps\<^sub>W\<^sub>C(1) in_homE left_connected
                          paste_2)
              show 4: "Right_a.arr (\<mu> \<star> a')"
                using \<mu> H\<^sub>R_def R'.preserves_arr by auto
              show "Right_a.dom (\<mu> \<star> a') = Right_a.cod (dom \<mu> \<star> \<phi>)"
                using a' \<phi> \<mu> 2 3 4 Right_a.dom_char Right_a.cod_char
                by (metis Right_a.seqE Right_a.seq_char hcomp_simps\<^sub>W\<^sub>C(1) in_homE paste_2)
            qed
            thus ?thesis using Right_a.comp_char Right_a.arr_char right_def by auto
          qed
          also have "... = \<mu> \<cdot> dom \<mu> \<star> a' \<cdot> \<phi>"
            using a' \<phi> \<mu> interchange hom_connected by auto
          also have "... = \<mu> \<star> \<phi>"
            using \<phi> \<mu> comp_arr_dom comp_cod_arr by auto
          finally show ?thesis using H\<^sub>R_def by simp
        qed
        show "Right_a.comp (H\<^sub>R \<phi> (Right_a.cod \<mu>)) (Right_a.R \<mu>) = H\<^sub>R \<phi> \<mu>"
        proof -
          have "Right_a.comp (H\<^sub>R \<phi> (Right_a.cod \<mu>)) (Right_a.R \<mu>)
                  = Right_a.comp (cod \<mu> \<star> \<phi>) (\<mu> \<star> a)"
            using assms 1 2 \<phi> \<mu> Right_a.cod_char right_def H\<^sub>R_def by simp
          also have "... = (cod \<mu> \<star> \<phi>) \<cdot> (\<mu> \<star> a)"
          proof -
            have "Right_a.seq (cod \<mu> \<star> \<phi>) (\<mu> \<star> a)"
            proof (intro Right_a.seqI)
              show 3: "Right_a.arr (cod \<mu> \<star> \<phi>)"
                using \<phi> \<mu> 2 Right_a.arr_char right_def
                by (metis (no_types, lifting) H\<^sub>R_def R.preserves_arr hcomp_simps\<^sub>W\<^sub>C(1)
                    in_homE left_connected paste_1)
              show 4: "Right_a.arr (\<mu> \<star> a)"
                using assms \<mu> Right_a.arr_char right_def
                using H\<^sub>R_def R.preserves_arr by auto
              show "Right_a.dom (cod \<mu> \<star> \<phi>) = Right_a.cod (\<mu> \<star> a)"
                using assms \<phi> \<mu> 2 3 4 Right_a.dom_char Right_a.cod_char
                by (metis Right_a.seqE Right_a.seq_char hcomp_simps\<^sub>W\<^sub>C(1) in_homE paste_1)
            qed
            thus ?thesis using Right_a.comp_char Right_a.arr_char right_def by auto
          qed
          also have "... = cod \<mu> \<cdot> \<mu> \<star> \<phi> \<cdot> a"
            using \<phi> \<mu> interchange hom_connected by auto
          also have "... = \<mu> \<star> \<phi>"
            using \<phi> \<mu> comp_arr_dom comp_cod_arr by auto
          finally show ?thesis using H\<^sub>R_def by simp
        qed
        next
        fix \<mu>
        assume \<mu>: "Right_a.ide \<mu>"
        have 1: "\<mu> \<star> \<phi> \<noteq> null"
          using assms \<phi> \<mu> Right_a.ide_char Right_a.arr_char right_def hom_connected by auto
        show "Right_a.iso (H\<^sub>R \<phi> \<mu>)"
        proof -
          have "iso (\<mu> \<star> \<phi>)"
          proof -
            have "a \<in> targets \<phi> \<inter> sources \<mu>"
              using assms \<phi> \<mu> 1 hom_connected weak_unit_self_composable
                    Right_a.ide_char Right_a.arr_char right_def connected_if_composable
              by (metis (full_types) IntI targetsI)
            thus ?thesis
              using \<phi> \<mu> Right_a.ide_char ide_is_iso iso_hcomp\<^sub>R\<^sub>W\<^sub>C(1) by blast
          qed
          moreover have "right a (\<mu> \<star> \<phi>)"
            using assms 1 \<phi> weak_unit_self_composable hom_connected(1) [of \<phi> a]
                  right_def match_3 null_agreement
            by auto
          ultimately show ?thesis
            using Right_a.iso_char Right_a.arr_char right_iff_right_inv
                  Right_a.inv_char H\<^sub>R_def
            by simp
        qed
      qed
      interpret R': equivalence_functor \<open>Right a'\<close> \<open>Right a'\<close> \<open>H\<^sub>R a'\<close>
      proof -
        have "naturally_isomorphic (Right a) (Right a) (H\<^sub>R a) Right_a.map"
          using assms Right_a.natural_isomorphism_\<rr> naturally_isomorphic_def by blast
        moreover have "naturally_isomorphic (Right a) (Right a) (H\<^sub>R a) (H\<^sub>R a')"
          using naturally_isomorphic_def \<Psi>.natural_isomorphism_axioms by blast
        ultimately have "naturally_isomorphic (Right a) (Right a) (H\<^sub>R a') Right_a.map"
          using naturally_isomorphic_symmetric naturally_isomorphic_transitive by fast
        hence "naturally_isomorphic (Right a') (Right a') (H\<^sub>R a') 
                 (identity_functor.map (Right a'))"
          using 1 by auto
        thus "equivalence_functor (Right a') (Right a') (H\<^sub>R a')"
          using 1 R'.isomorphic_to_identity_is_equivalence naturally_isomorphic_def
          by fastforce
      qed

      show "weak_unit a'"
        using weak_unit_def iso L'.fully_faithful_functor_axioms R'.fully_faithful_functor_axioms
        by blast
    qed

    lemma sources_iso_closed:
    assumes "a \<in> sources \<mu>" and "a \<cong> a'"
    shows "a' \<in> sources \<mu>"
      using assms isomorphism_respects_weak_units isomorphic_implies_equicomposable
      by blast

    lemma targets_iso_closed:
    assumes "a \<in> targets \<mu>" and "a \<cong> a'"
    shows "a' \<in> targets \<mu>"
      using assms isomorphism_respects_weak_units isomorphic_implies_equicomposable
      by blast

    lemma sources_eqI:
    assumes "sources \<mu> \<inter> sources \<nu> \<noteq> {}"
    shows "sources \<mu> = sources \<nu>"
      using assms sources_iso_closed sources_are_isomorphic by blast

    lemma targets_eqI:
    assumes "targets \<mu> \<inter> targets \<nu> \<noteq> {}"
    shows "targets \<mu> = targets \<nu>"
      using assms targets_iso_closed targets_are_isomorphic by blast

    text \<open>
      The sets of sources and targets of a weak unit are isomorphism classes.
    \<close>

    lemma sources_char:
    assumes "weak_unit a"
    shows "sources a = {x. x \<cong> a}"
      using assms sources_iso_closed weak_unit_iff_self_source sources_are_isomorphic
            isomorphic_symmetric
      by blast

    lemma targets_char:
    assumes "weak_unit a"
    shows "targets a = {x. x \<cong> a}"
      using assms targets_iso_closed weak_unit_iff_self_target targets_are_isomorphic
            isomorphic_symmetric
      by blast

  end

  section "Horizontal Homs"

  text \<open>
    Here we define a locale that axiomatizes a (vertical) category \<open>V\<close> that has been
    punctuated into ``horizontal homs'' by the choice of idempotent endofunctors \<open>src\<close> and \<open>trg\<close>
    that assign a specific ``source'' and ``target'' 1-cell to each of its arrows.
    The functors \<open>src\<close> and \<open>trg\<close> are also subject to further conditions that constrain how
    they commute with each other.
  \<close>

  locale horizontal_homs =
    category V +
    src: endofunctor V src +
    trg: endofunctor V trg
  for V :: "'a comp"      (infixr "\<cdot>" 55)
  and src :: "'a \<Rightarrow> 'a"
  and trg :: "'a \<Rightarrow> 'a" +
  assumes ide_src [simp]: "arr \<mu> \<Longrightarrow> ide (src \<mu>)"
  and ide_trg [simp]: "arr \<mu> \<Longrightarrow> ide (trg \<mu>)"
  and src_src [simp]: "arr \<mu> \<Longrightarrow> src (src \<mu>) = src \<mu>"
  and trg_trg [simp]: "arr \<mu> \<Longrightarrow> trg (trg \<mu>) = trg \<mu>"
  and trg_src [simp]: "arr \<mu> \<Longrightarrow> trg (src \<mu>) = src \<mu>"
  and src_trg [simp]: "arr \<mu> \<Longrightarrow> src (trg \<mu>) = trg \<mu>"
  begin

    no_notation in_hom        ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    notation in_hom           ("\<guillemotleft>_ : _ \<Rightarrow> _\<guillemotright>")

    text \<open>
      We define an \emph{object} to be an arrow that is its own source
      (or equivalently, its own target).
    \<close>

    definition obj
    where "obj a \<equiv> arr a \<and> src a = a"

    lemma obj_def':
    shows "obj a \<longleftrightarrow> arr a \<and> trg a = a"
      using trg_src src_trg obj_def by metis

    lemma objE [elim]:
    assumes "obj a" and "\<lbrakk> ide a; src a = a; trg a = a \<rbrakk> \<Longrightarrow> T"
    shows T
    proof -
      have "ide a" using assms obj_def ide_src by metis
      moreover have "src a = a" using assms obj_def by simp
      moreover have "trg a = a" using assms obj_def' by simp
      ultimately show ?thesis using assms by simp
    qed

    (* TODO: Can't add "arr a" or "ide a" due to looping. *)
    lemma obj_simps (* [simp] *):
    assumes "obj a"
    shows "src a = a" and "trg a = a"
      using assms by auto

    lemma obj_src [intro, simp]:
    assumes "arr \<mu>"
    shows "obj (src \<mu>)"
      using assms obj_def by auto

    lemma obj_trg [intro, simp]:
    assumes "arr \<mu>"
    shows "obj (trg \<mu>)"
      using assms obj_def by auto

    definition in_hhom  ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    where "in_hhom \<mu> a b \<equiv> arr \<mu> \<and> src \<mu> = a \<and> trg \<mu> = b"

    abbreviation hhom
    where "hhom a b \<equiv> {\<mu>. \<guillemotleft>\<mu> : a \<rightarrow> b\<guillemotright>}"

    abbreviation (input) hseq\<^sub>H\<^sub>H
    where "hseq\<^sub>H\<^sub>H \<equiv> \<lambda>\<mu> \<nu>. arr \<mu> \<and> arr \<nu> \<and> src \<mu> = trg \<nu>"

    lemma in_hhomI [intro, simp]:
    assumes "arr \<mu>" and "src \<mu> = a" and "trg \<mu> = b"
    shows "\<guillemotleft>\<mu> : a \<rightarrow> b\<guillemotright>"
      using assms in_hhom_def by auto

    lemma in_hhomE [elim]:
    assumes "\<guillemotleft>\<mu> : a \<rightarrow> b\<guillemotright>"
    and "\<lbrakk> arr \<mu>; obj a; obj b; src \<mu> = a; trg \<mu> = b \<rbrakk> \<Longrightarrow> T"
    shows "T"
      using assms in_hhom_def by auto

    (*
     * TODO: I tried removing the second assertion here, thinking that it should already
     * be covered by the category locale, but in fact it breaks some proofs in
     * SpanBicategory that ought to be trivial.  So it seems that the presence of
     * this introduction rule adds something, and I should consider whether this rule
     * should be added to the category locale.
     *)
    lemma ide_in_hom [intro]:
    assumes "ide f"
    shows "\<guillemotleft>f : src f \<rightarrow> trg f\<guillemotright>" and "\<guillemotleft>f : f \<Rightarrow> f\<guillemotright>"
      using assms by auto

    lemma src_dom [simp]:
    assumes "arr \<mu>"
    shows "src (dom \<mu>) = src \<mu>"
      using assms src.preserves_dom [of \<mu>] by simp

    lemma src_cod [simp]:
    assumes "arr \<mu>"
    shows "src (cod \<mu>) = src \<mu>"
      using assms src.preserves_cod [of \<mu>] by simp

    lemma trg_dom [simp]:
    assumes "arr \<mu>"
    shows "trg (dom \<mu>) = trg \<mu>"
      using assms trg.preserves_dom [of \<mu>] by simp

    lemma trg_cod [simp]:
    assumes "arr \<mu>"
    shows "trg (cod \<mu>) = trg \<mu>"
      using assms trg.preserves_cod [of \<mu>] by simp

    (*
     * TODO: In theory, the following simps should already be available from the fact
     * that src and trg are endofunctors.  But they seem not to get used.
     *)
    lemma dom_src [simp]:
    assumes "arr \<mu>"
    shows "dom (src \<mu>) = src \<mu>"
      using assms by simp

    lemma cod_src [simp]:
    assumes "arr \<mu>"
    shows "cod (src \<mu>) = src \<mu>"
      using assms by simp

    lemma dom_trg [simp]:
    assumes "arr \<mu>"
    shows "dom (trg \<mu>) = trg \<mu>"
      using assms by simp

    lemma cod_trg [simp]:
    assumes "arr \<mu>"
    shows "cod (trg \<mu>) = trg \<mu>"
      using assms by simp

    lemma vcomp_in_hhom [intro, simp]:
    assumes "seq \<nu> \<mu>" and "src \<nu> = a" and "trg \<nu> = b"
    shows "\<guillemotleft>\<nu> \<cdot> \<mu> : a \<rightarrow> b\<guillemotright>"
      using assms src_cod [of "\<nu> \<cdot> \<mu>"] trg_cod [of "\<nu> \<cdot> \<mu>"] by auto

    lemma src_vcomp [simp]:
    assumes "seq \<nu> \<mu>"
    shows "src (\<nu> \<cdot> \<mu>) = src \<nu>"
      using assms src_cod [of "\<nu> \<cdot> \<mu>"] by auto

    lemma trg_vcomp [simp]:
    assumes "seq \<nu> \<mu>"
    shows "trg (\<nu> \<cdot> \<mu>) = trg \<nu>"
      using assms trg_cod [of "\<nu> \<cdot> \<mu>"] by auto

    lemma vseq_implies_hpar:
    assumes "seq \<nu> \<mu>"
    shows "src \<nu> = src \<mu>" and "trg \<nu> = trg \<mu>"
      using assms src_dom [of "\<nu> \<cdot> \<mu>"] trg_dom [of "\<nu> \<cdot> \<mu>"] src_cod [of "\<nu> \<cdot> \<mu>"]
            trg_cod [of "\<nu> \<cdot> \<mu>"]
      by auto

    lemma vconn_implies_hpar:
    assumes "\<guillemotleft>\<mu> : f \<Rightarrow> g\<guillemotright>"
    shows "src \<mu> = src f" and "trg \<mu> = trg f" and "src g = src f" and "trg g = trg f"
      using assms by auto

    lemma src_inv [simp]:
    assumes "iso \<mu>"
    shows "src (inv \<mu>) = src \<mu>"
      using assms inv_in_hom iso_is_arr src_dom src_cod iso_inv_iso dom_inv by metis

    lemma trg_inv [simp]:
    assumes "iso \<mu>"
    shows "trg (inv \<mu>) = trg \<mu>"
      using assms inv_in_hom iso_is_arr trg_dom trg_cod iso_inv_iso cod_inv by metis

    lemma inv_in_hhom [intro, simp]:
    assumes "iso \<mu>" and "src \<mu> = a" and "trg \<mu> = b"
    shows "\<guillemotleft>inv \<mu> : a \<rightarrow> b\<guillemotright>"
      using assms iso_is_arr by simp

    lemma hhom_is_subcategory:
    shows "subcategory V (\<lambda>\<mu>. \<guillemotleft>\<mu> : a \<rightarrow> b\<guillemotright>)"
      using src_dom trg_dom src_cod trg_cod by (unfold_locales, auto)

    lemma isomorphic_objects_are_equal:
    assumes "obj a" and "obj b" and "a \<cong> b"
    shows "a = b"
      using assms isomorphic_def
      by (metis arr_inv dom_inv in_homE objE src_dom src_inv)


    text \<open>
      Having the functors \<open>src\<close> and \<open>trg\<close> allows us to form categories VV and VVV
      of formally horizontally composable pairs and triples of arrows.
    \<close>

    interpretation VxV: product_category V V ..
    interpretation VV: subcategory VxV.comp \<open>\<lambda>\<mu>\<nu>. hseq\<^sub>H\<^sub>H (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close>
      by (unfold_locales, auto)

    lemma subcategory_VV:
    shows "subcategory VxV.comp (\<lambda>\<mu>\<nu>. hseq\<^sub>H\<^sub>H (fst \<mu>\<nu>) (snd \<mu>\<nu>))"
      ..

    interpretation VxVxV: product_category V VxV.comp ..
    interpretation VVV: subcategory VxVxV.comp
                            \<open>\<lambda>\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> VV.arr (snd \<tau>\<mu>\<nu>) \<and>
                                   src (fst \<tau>\<mu>\<nu>) = trg (fst (snd \<tau>\<mu>\<nu>))\<close>
      using VV.arr_char
      by (unfold_locales, auto)

    lemma subcategory_VVV:
    shows "subcategory VxVxV.comp
             (\<lambda>\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> VV.arr (snd \<tau>\<mu>\<nu>) \<and>
                    src (fst \<tau>\<mu>\<nu>) = trg (fst (snd \<tau>\<mu>\<nu>)))"
      ..

  end

  subsection "Prebicategories with Homs"

  text \<open>
    A \emph{weak composition with homs} consists of a weak composition that is
    equipped with horizontal homs in such a way that the chosen source and
    target of each 2-cell \<open>\<mu>\<close> in fact lie in the set of sources and targets,
    respectively, of \<open>\<mu>\<close>, such that horizontal composition respects the
    chosen sources and targets, and such that if 2-cells \<open>\<mu>\<close> and \<open>\<nu>\<close> are
    horizontally composable, then the chosen target of \<open>\<mu>\<close> coincides with
    the chosen source of \<open>\<nu>\<close>.
  \<close>

  locale weak_composition_with_homs =
    weak_composition +
    horizontal_homs +
  assumes src_in_sources: "arr \<mu> \<Longrightarrow> src \<mu> \<in> sources \<mu>"
  and trg_in_targets: "arr \<mu> \<Longrightarrow> trg \<mu> \<in> targets \<mu>"
  and src_hcomp': "\<nu> \<star> \<mu> \<noteq> null \<Longrightarrow> src (\<nu> \<star> \<mu>) = src \<mu>"
  and trg_hcomp': "\<nu> \<star> \<mu> \<noteq> null \<Longrightarrow> trg (\<nu> \<star> \<mu>) = trg \<nu>"
  and seq_if_composable: "\<nu> \<star> \<mu> \<noteq> null \<Longrightarrow> src \<nu> = trg \<mu>"

  locale prebicategory_with_homs =
    prebicategory +
    weak_composition_with_homs
  begin

    lemma composable_char\<^sub>P\<^sub>B\<^sub>H:
    shows "\<nu> \<star> \<mu> \<noteq> null \<longleftrightarrow> arr \<mu> \<and> arr \<nu> \<and> src \<nu> = trg \<mu>"
    proof
      show "arr \<mu> \<and> arr \<nu> \<and> src \<nu> = trg \<mu> \<Longrightarrow> \<nu> \<star> \<mu> \<noteq> null"
        using trg_in_targets src_in_sources composable_if_connected
        by (metis sourcesD(3) targets_determine_composability)
      show "\<nu> \<star> \<mu> \<noteq> null \<Longrightarrow> arr \<mu> \<and> arr \<nu> \<and> src \<nu> = trg \<mu>"
        using seq_if_composable composable_implies_arr by auto
    qed

    lemma hcomp_in_hom\<^sub>P\<^sub>B\<^sub>H:
    assumes "\<guillemotleft>\<mu> : a \<rightarrow>\<^sub>W\<^sub>C b\<guillemotright>" and "\<guillemotleft>\<nu> : b \<rightarrow>\<^sub>W\<^sub>C c\<guillemotright>"
    shows "\<guillemotleft>\<nu> \<star> \<mu> : a \<rightarrow>\<^sub>W\<^sub>C c\<guillemotright>"
    and "\<guillemotleft>\<nu> \<star> \<mu> : dom \<nu> \<star> dom \<mu> \<Rightarrow> cod \<nu> \<star> cod \<mu>\<guillemotright>"
    proof -
      show "\<guillemotleft>\<nu> \<star> \<mu> : a \<rightarrow>\<^sub>W\<^sub>C c\<guillemotright>"
        using assms sources_determine_composability sources_hcomp targets_hcomp by auto
      thus "\<guillemotleft>\<nu> \<star> \<mu> : dom \<nu> \<star> dom \<mu> \<Rightarrow> cod \<nu> \<star> cod \<mu>\<guillemotright>"
        using assms by auto
    qed

    text \<open>
      In a prebicategory with homs, if \<open>a\<close> is an object (i.e. \<open>src a = a\<close> and \<open>trg a = a\<close>),
      then \<open>a\<close> is a weak unit.  The converse need not hold: there can be weak units that the
      \<open>src\<close> and \<open>trg\<close> mappings send to other 1-cells in the same isomorphism class.
    \<close>

    lemma obj_is_weak_unit:
    assumes "obj a"
    shows "weak_unit a"
    proof -
      have "a \<in> sources a"
        using assms objE src_in_sources ideD(1) by metis
      thus ?thesis by auto
    qed

  end

  subsection "Choosing Homs"

  text \<open>
    Every prebicategory extends to a prebicategory with homs, by choosing an arbitrary
    representative of each isomorphism class of weak units to serve as an object.
    ``The source'' of a 2-cell is defined to be the chosen representative of the set of
     all its sources (which is an isomorphism class), and similarly for ``the target''.
  \<close>

  context prebicategory
  begin

    definition rep
    where "rep f \<equiv> SOME f'. f' \<in> { f'. f \<cong> f' }"

    definition some_src
    where "some_src \<mu> \<equiv> if arr \<mu> then rep (SOME a. a \<in> sources \<mu>) else null"

    definition some_trg
    where "some_trg \<mu> \<equiv> if arr \<mu> then rep (SOME b. b \<in> targets \<mu>) else null"

    lemma isomorphic_ide_rep:
    assumes "ide f"
    shows "f \<cong> rep f"
    proof -
      have "\<exists>f'. f' \<in> { f'. f \<cong> f' }"
        using assms isomorphic_reflexive by blast
      thus ?thesis using rep_def someI_ex by simp
    qed

    lemma rep_rep:
    assumes "ide f"
    shows "rep (rep f) = rep f"
    proof -
      have "rep f \<in> { f'. f \<cong> f' }"
        using assms isomorphic_ide_rep by simp
      have "{ f'. f \<cong> f' } = { f'. rep f \<cong> f' }"
      proof -
        have "\<And>f'. f \<cong> f' \<longleftrightarrow> rep f \<cong> f'"
        proof
          fix f'
          assume f': "f \<cong> f'"
          show "rep f \<cong> f'"
          proof -
            obtain \<phi> where \<phi>: "\<phi> \<in> hom f f' \<and> iso \<phi>"
              using f' by auto
            obtain \<psi> where \<psi>: "\<psi> \<in> hom f (rep f) \<and> iso \<psi>"
              using assms isomorphic_ide_rep by blast
            have "inv \<psi> \<in> hom (rep f) f \<and> iso (inv \<psi>)"
              using \<psi> iso_inv_iso inv_in_hom by simp
            hence "iso (V \<phi> (inv \<psi>)) \<and> V \<phi> (inv \<psi>) \<in> hom (rep f) f'"
              using \<phi> isos_compose by auto
            thus ?thesis using isomorphic_def by auto
          qed
          next
          fix f'
          assume f': "rep f \<cong> f'"
          show "f \<cong> f'"
            using assms f' isomorphic_ide_rep isos_compose isomorphic_def by blast
        qed
        thus ?thesis by auto
      qed
      hence "rep (rep f) = (SOME f'. f' \<in> { f'. f \<cong> f' })"
        using assms rep_def by fastforce
      also have "... = rep f"
        using assms rep_def by simp
      finally show ?thesis by simp
    qed

    lemma some_src_in_sources:
    assumes "arr \<mu>"
    shows "some_src \<mu> \<in> sources \<mu>"
    proof -
      have 1: "(SOME a. a \<in> sources \<mu>) \<in> sources \<mu>"
        using assms arr_iff_has_src someI_ex [of "\<lambda>a. a \<in> sources \<mu>"] by blast
      moreover have "ide (SOME a. a \<in> sources \<mu>)"
        using 1 weak_unit_self_composable by auto
      ultimately show ?thesis
        using assms 1 some_src_def
              sources_iso_closed [of "SOME a. a \<in> sources \<mu>" \<mu>]
              isomorphic_ide_rep [of "SOME a. a \<in> sources \<mu>"]
        by metis
    qed

    lemma some_trg_in_targets:
    assumes "arr \<mu>"
    shows "some_trg \<mu> \<in> targets \<mu>"
    proof -
      have 1: "(SOME a. a \<in> targets \<mu>) \<in> targets \<mu>"
        using assms arr_iff_has_trg someI_ex [of "\<lambda>a. a \<in> targets \<mu>"] by blast
      moreover have "ide (SOME a. a \<in> targets \<mu>)"
        using 1 weak_unit_self_composable by auto
      ultimately show ?thesis
        using assms 1 some_trg_def
              targets_iso_closed [of "SOME a. a \<in> targets \<mu>" \<mu>]
              isomorphic_ide_rep [of "SOME a. a \<in> targets \<mu>"]
        by presburger
    qed

    lemma some_src_dom:
    assumes "arr \<mu>"
    shows "some_src (dom \<mu>) = some_src \<mu>"
      using assms some_src_def sources_dom by simp

    lemma some_src_cod:
    assumes "arr \<mu>"
    shows "some_src (cod \<mu>) = some_src \<mu>"
      using assms some_src_def sources_cod by simp

    lemma some_trg_dom:
    assumes "arr \<mu>"
    shows "some_trg (dom \<mu>) = some_trg \<mu>"
      using assms some_trg_def targets_dom by simp

    lemma some_trg_cod:
    assumes "arr \<mu>"
    shows "some_trg (cod \<mu>) = some_trg \<mu>"
      using assms some_trg_def targets_cod by simp

    lemma ide_some_src:
    assumes "arr \<mu>"
    shows "ide (some_src \<mu>)"
      using assms some_src_in_sources weak_unit_self_composable by blast

    lemma ide_some_trg:
    assumes "arr \<mu>"
    shows "ide (some_trg \<mu>)"
      using assms some_trg_in_targets weak_unit_self_composable by blast

    lemma some_src_composable:
    assumes "arr \<tau>"
    shows "\<tau> \<star> \<mu> \<noteq> null \<longleftrightarrow> some_src \<tau> \<star> \<mu> \<noteq> null"
      using assms some_src_in_sources sources_determine_composability by blast

    lemma some_trg_composable:
    assumes "arr \<sigma>"
    shows "\<mu> \<star> \<sigma> \<noteq> null \<longleftrightarrow> \<mu> \<star> some_trg \<sigma> \<noteq> null"
      using assms some_trg_in_targets targets_determine_composability by blast

    lemma sources_some_src:
    assumes "arr \<mu>"
    shows "sources (some_src \<mu>) = sources \<mu>"
      using assms sources_determine_composability some_src_in_sources by blast

    lemma targets_some_trg:
    assumes "arr \<mu>"
    shows "targets (some_trg \<mu>) = targets \<mu>"
      using assms targets_determine_composability some_trg_in_targets by blast

    lemma src_some_src:
    assumes "arr \<mu>"
    shows "some_src (some_src \<mu>) = some_src \<mu>"
      using assms some_src_def ide_some_src sources_some_src by force

    lemma trg_some_trg:
    assumes "arr \<mu>"
    shows "some_trg (some_trg \<mu>) = some_trg \<mu>"
      using assms some_trg_def ide_some_trg targets_some_trg by force

    lemma sources_char':
    assumes "arr \<mu>"
    shows "a \<in> sources \<mu> \<longleftrightarrow> some_src \<mu> \<cong> a"
      using assms some_src_in_sources sources_iso_closed sources_are_isomorphic by meson

    lemma targets_char':
    assumes "arr \<mu>"
    shows "a \<in> targets \<mu> \<longleftrightarrow> some_trg \<mu> \<cong> a"
      using assms some_trg_in_targets targets_iso_closed targets_are_isomorphic by blast

    text \<open>
      An arbitrary choice of sources and targets in a prebicategory results in a notion of
      formal composability that coincides with the actual horizontal composability
      of the prebicategory.
    \<close>

    lemma composable_char\<^sub>P\<^sub>B:
    shows "\<tau> \<star> \<sigma> \<noteq> null \<longleftrightarrow> arr \<sigma> \<and> arr \<tau> \<and> some_src \<tau> = some_trg \<sigma>"
    proof
        assume \<sigma>\<tau>: "\<tau> \<star> \<sigma> \<noteq> null"
        show "arr \<sigma> \<and> arr \<tau> \<and> some_src \<tau> = some_trg \<sigma>"
          using \<sigma>\<tau> composable_implies_arr connected_if_composable some_src_def some_trg_def
          by force
        next
        assume \<sigma>\<tau>: "arr \<sigma> \<and> arr \<tau> \<and> some_src \<tau> = some_trg \<sigma>"
        show "\<tau> \<star> \<sigma> \<noteq> null"
          using \<sigma>\<tau> some_src_in_sources some_trg_composable by force
    qed

    text \<open>
      A 1-cell is its own source if and only if it is its own target.
    \<close>

    lemma self_src_iff_self_trg:
    assumes "ide a"
    shows "a = some_src a \<longleftrightarrow> a = some_trg a"
    proof
      assume a: "a = some_src a"
      have "weak_unit a \<and> a \<star> a \<noteq> null"
        using assms a some_src_in_sources [of a] by force
      thus "a = some_trg a" using a composable_char\<^sub>P\<^sub>B by simp
      next
      assume a: "a = some_trg a"
      have "weak_unit a \<and> a \<star> a \<noteq> null"
        using assms a some_trg_in_targets [of a] by force
      thus "a = some_src a" using a composable_char\<^sub>P\<^sub>B by simp
    qed

    lemma some_trg_some_src:
    assumes "arr \<mu>"
    shows "some_trg (some_src \<mu>) = some_src \<mu>"
      using assms ide_some_src some_src_def some_trg_def some_src_in_sources sources_char
            targets_char sources_some_src
      by force

    lemma src_some_trg:
    assumes "arr \<mu>"
    shows "some_src (some_trg \<mu>) = some_trg \<mu>"
      using assms ide_some_trg some_src_def some_trg_def some_trg_in_targets sources_char
            targets_char targets_some_trg
      by force

    lemma some_src_eqI:
    assumes "a \<in> sources \<mu>" and "some_src a = a"
    shows "some_src \<mu> = a"
    proof -
      have 1: "arr \<mu> \<and> arr a" using assms composable_implies_arr by auto
      have "some_src \<mu> = rep (SOME x. x \<in> sources \<mu>)"
        using assms 1 some_src_def by simp
      also have "... = rep (SOME x. some_src \<mu> \<cong> x)"
        using assms 1 sources_char' by simp
      also have "... = rep (SOME x. some_src a \<cong> x)"
        using assms 1 some_src_in_sources sources_are_isomorphic
              isomorphic_symmetric isomorphic_transitive
        by metis
      also have "... = rep (SOME x. x \<in> sources a)"
        using assms 1 sources_char' by auto
      also have "... = some_src a"
        using assms 1 some_src_def by simp
      also have "... = a"
        using assms by auto
      finally show ?thesis by simp
    qed

    lemma some_trg_eqI:
    assumes "b \<in> targets \<mu>" and "some_trg b = b"
    shows "some_trg \<mu> = b"
    proof -
      have 1: "arr \<mu> \<and> arr b" using assms composable_implies_arr by auto
      have "some_trg \<mu> = rep (SOME x. x \<in> targets \<mu>)"
        using assms 1 some_trg_def by simp
      also have "... = rep (SOME x. some_trg \<mu> \<cong> x)"
        using assms 1 targets_char' by simp
      also have "... = rep (SOME x. some_trg b \<cong> x)"
        using assms 1 some_trg_in_targets targets_are_isomorphic
              isomorphic_symmetric isomorphic_transitive
        by metis
      also have "... = rep (SOME x. x \<in> targets b)"
        using assms 1 targets_char' by auto
      also have "... = some_trg b"
        using assms 1 some_trg_def by simp
      also have "... = b"
        using assms by auto
      finally show ?thesis by simp
    qed

    lemma some_src_comp:
    assumes "\<tau> \<star> \<sigma> \<noteq> null"
    shows "some_src (\<tau> \<star> \<sigma>) = some_src \<sigma>"
    proof (intro some_src_eqI [of "some_src \<sigma>" "\<tau> \<star> \<sigma>"])
      show "some_src (some_src \<sigma>) = some_src \<sigma>"
        using assms src_some_src composable_implies_arr by simp
      show "some_src \<sigma> \<in> sources (H \<tau> \<sigma>)"
        using assms some_src_in_sources composable_char\<^sub>P\<^sub>B match_3 [of \<sigma> "some_src \<sigma>"]
        by (simp add: sources_hcomp)
    qed

    lemma some_trg_comp:
    assumes "\<tau> \<star> \<sigma> \<noteq> null"
    shows "some_trg (\<tau> \<star> \<sigma>) = some_trg \<tau>"
    proof (intro some_trg_eqI [of "some_trg \<tau>" "\<tau> \<star> \<sigma>"])
      show "some_trg (some_trg \<tau>) = some_trg \<tau>"
        using assms trg_some_trg composable_implies_arr by simp
      show "some_trg \<tau> \<in> targets (H \<tau> \<sigma>)"
        using assms some_trg_in_targets composable_char\<^sub>P\<^sub>B match_4 [of \<tau> \<sigma> "some_trg \<tau>"]
        by (simp add: targets_hcomp)
    qed

    text \<open>
      The mappings that take an arrow to its chosen source or target are endofunctors
      of the vertical category, which commute with each other in the manner required
      for horizontal homs.
    \<close>

    interpretation S: endofunctor V some_src
      apply unfold_locales
           using some_src_def apply simp
          using ide_some_src apply simp
        using some_src_dom ide_some_src apply simp
       using some_src_cod ide_some_src apply simp
    proof -
      fix \<nu> \<mu>
      assume \<mu>\<nu>: "seq \<nu> \<mu>"
      show "some_src (\<nu> \<cdot> \<mu>) = some_src \<nu> \<cdot> some_src \<mu>"
        using \<mu>\<nu> some_src_dom [of "\<nu> \<cdot> \<mu>"] some_src_dom some_src_cod [of "\<nu> \<cdot> \<mu>"]
              some_src_cod ide_some_src
        by auto
    qed

    interpretation T: endofunctor V some_trg
      apply unfold_locales
          using some_trg_def apply simp
         using ide_some_trg apply simp
        using some_trg_dom ide_some_trg apply simp
       using some_trg_cod ide_some_trg apply simp
    proof -
      fix \<nu> \<mu>
      assume \<mu>\<nu>: "seq \<nu> \<mu>"
      show "some_trg (\<nu> \<cdot> \<mu>) = some_trg \<nu> \<cdot> some_trg \<mu>"
        using \<mu>\<nu> some_trg_dom [of "\<nu> \<cdot> \<mu>"] some_trg_dom some_trg_cod [of "\<nu> \<cdot> \<mu>"]
              some_trg_cod ide_some_trg
        by auto
    qed

    interpretation weak_composition_with_homs V H some_src some_trg
      apply unfold_locales
      using some_src_in_sources some_trg_in_targets
            src_some_src trg_some_trg src_some_trg some_trg_some_src
            some_src_comp some_trg_comp composable_char\<^sub>P\<^sub>B ide_some_src ide_some_trg
      by simp_all

    proposition extends_to_weak_composition_with_homs:
    shows "weak_composition_with_homs V H some_src some_trg"
      ..

    proposition extends_to_prebicategory_with_homs:
    shows "prebicategory_with_homs V H \<a> some_src some_trg"
      ..

  end

  subsection "Choosing Units"

  text \<open>
    A \emph{prebicategory with units} is a prebicategory equipped with a choice,
    for each weak unit \<open>a\<close>, of a ``unit isomorphism'' \<open>\<guillemotleft>\<i>[a] : a \<star> a \<Rightarrow> a\<guillemotright>\<close>.
  \<close>

  locale prebicategory_with_units =
    prebicategory V H \<a> +
    weak_composition V H
  for V :: "'a comp"                  (infixr "\<cdot>" 55)
  and H :: "'a comp"                  (infixr "\<star>" 53)
  and \<a> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"      ("\<a>[_, _, _]")
  and \<i> :: "'a \<Rightarrow> 'a"                  ("\<i>[_]") +
  assumes unit_in_vhom\<^sub>P\<^sub>B\<^sub>U: "weak_unit a \<Longrightarrow> \<guillemotleft>\<i>[a] : a \<star> a \<Rightarrow> a\<guillemotright>"
  and iso_unit\<^sub>P\<^sub>B\<^sub>U: "weak_unit a \<Longrightarrow> iso \<i>[a]"
  begin

    lemma unit_in_hom\<^sub>P\<^sub>B\<^sub>U:
    assumes "weak_unit a"
    shows "\<guillemotleft>\<i>[a] : a \<rightarrow>\<^sub>W\<^sub>C a\<guillemotright>" and "\<guillemotleft>\<i>[a] : a \<star> a \<Rightarrow> a\<guillemotright>"
    proof -
      show 1: "\<guillemotleft>\<i>[a] : a \<star> a \<Rightarrow> a\<guillemotright>"
        using assms unit_in_vhom\<^sub>P\<^sub>B\<^sub>U by auto
      show "\<guillemotleft>\<i>[a] : a \<rightarrow>\<^sub>W\<^sub>C a\<guillemotright>"
        using assms 1 weak_unit_iff_self_source weak_unit_iff_self_target
              sources_cod [of "\<i>[a]"] targets_cod [of "\<i>[a]"]
        by (elim in_homE, auto)
    qed

    lemma unit_simps [simp]:
    assumes "weak_unit a"
    shows "arr \<i>[a]" and "dom \<i>[a] = a \<star> a" and "cod \<i>[a] = a"
      using assms unit_in_vhom\<^sub>P\<^sub>B\<^sub>U by auto

  end

  text \<open>
    Every prebicategory extends to a prebicategory with units, simply by choosing the
    unit isomorphisms arbitrarily.
  \<close>

  context prebicategory
  begin

    proposition extends_to_prebicategory_with_units:
    shows "prebicategory_with_units V H \<a> some_unit"
      using iso_some_unit by (unfold_locales, auto)

  end

  subsection "Horizontal Composition"

  text \<open>
    The following locale axiomatizes a (vertical) category \<open>V\<close> with horizontal homs,
    which in addition has been equipped with a functorial operation \<open>H\<close> of
    horizontal composition from \<open>VV\<close> to \<open>V\<close>, assumed to preserve source and target.
  \<close>

  locale horizontal_composition =
    horizontal_homs V src trg +
    VxV: product_category V V +
    VV: subcategory VxV.comp \<open>\<lambda>\<mu>\<nu>. hseq\<^sub>H\<^sub>H (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close> +
    H: "functor" VV.comp V \<open>\<lambda>\<mu>\<nu>. H (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close>
  for V :: "'a comp"          (infixr "\<cdot>" 55)
  and H :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixr "\<star>" 53)
  and src :: "'a \<Rightarrow> 'a"
  and trg :: "'a \<Rightarrow> 'a" +
  assumes src_hcomp: "arr (\<mu> \<star> \<nu>) \<Longrightarrow> src (\<mu> \<star> \<nu>) = src \<nu>"
  and trg_hcomp: "arr (\<mu> \<star> \<nu>) \<Longrightarrow> trg (\<mu> \<star> \<nu>) = trg \<mu>"
  begin
    (* TODO: Why does this get re-introduced? *)
    no_notation in_hom        ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    text \<open>
      \<open>H\<close> is a partial magma, which shares its null with \<open>V\<close>.
    \<close>

    lemma is_partial_magma:
    shows "partial_magma H" and "partial_magma.null H = null"
    proof -
      have 1: "\<forall>f. null \<star> f = null \<and> f \<star> null = null"
        using H.is_extensional VV.arr_char not_arr_null by auto
      interpret H: partial_magma H
      proof
        show "\<exists>!n. \<forall>f. n \<star> f = n \<and> f \<star> n = n"
        proof
          show "\<forall>f. null \<star> f = null \<and> f \<star> null = null" by fact
          show "\<And>n. \<forall>f. n \<star> f = n \<and> f \<star> n = n \<Longrightarrow> n = null"
            using 1 VV.arr_char H.is_extensional not_arr_null by metis
        qed
      qed
      show "partial_magma H" ..
      show "H.null = null"
        using 1 H.null_def the1_equality [of "\<lambda>n. \<forall>f. n \<star> f = n \<and> f \<star> n = n"]
        by metis
    qed

    text \<open>
      \textbf{Note:} The following is ``almost'' \<open>H.seq\<close>, but for that we would need
      \<open>H.arr = V.arr\<close>.
      This would be unreasonable to expect, in general, as the definition of \<open>H.arr\<close> is based
      on ``strict'' units rather than weak units.
      Later we will show that we do have \<open>H.arr = V.arr\<close> if the vertical category is discrete.
    \<close>

    abbreviation hseq
    where "hseq \<nu> \<mu> \<equiv> arr (\<nu> \<star> \<mu>)"

    lemma hseq_char:
    shows "hseq \<nu> \<mu> \<longleftrightarrow> arr \<mu> \<and> arr \<nu> \<and> src \<nu> = trg \<mu>"
    proof -
      have "hseq \<nu> \<mu> \<longleftrightarrow> VV.arr (\<nu>, \<mu>)"
        using H.is_extensional H.preserves_arr by force
      also have "... \<longleftrightarrow> arr \<mu> \<and> arr \<nu> \<and> src \<nu> = trg \<mu>"
        using VV.arr_char by force
      finally show ?thesis by blast
    qed

    lemma hseq_char':
    shows "hseq \<nu> \<mu> \<longleftrightarrow> \<nu> \<star> \<mu> \<noteq> null"
      using VV.arr_char H.preserves_arr H.is_extensional hseq_char [of \<nu> \<mu>] by auto

    lemma hseqI' [simp]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<nu> = trg \<mu>"
    shows "hseq \<nu> \<mu>"
      using assms hseq_char by simp

    lemma hseqI [intro]:
    assumes "\<guillemotleft>\<mu> : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>\<nu> : b \<rightarrow> c\<guillemotright>"
    shows "hseq \<nu> \<mu>"
      using assms hseq_char by auto

    lemma hseqE [elim]:
    assumes "hseq \<nu> \<mu>"
    and "arr \<mu> \<Longrightarrow> arr \<nu> \<Longrightarrow> src \<nu> = trg \<mu> \<Longrightarrow> T"
    shows "T"
      using assms hseq_char by simp

    lemma hcomp_simps [simp]:
    assumes "hseq \<nu> \<mu>"
    shows "src (\<nu> \<star> \<mu>) = src \<mu>" and "trg (\<nu> \<star> \<mu>) = trg \<nu>"
    and "dom (\<nu> \<star> \<mu>) = dom \<nu> \<star> dom \<mu>" and "cod (\<nu> \<star> \<mu>) = cod \<nu> \<star> cod \<mu>"
      using assms VV.arr_char src_hcomp apply blast
      using assms VV.arr_char trg_hcomp apply blast
      using assms VV.arr_char H.preserves_dom apply force
      using assms VV.arr_char H.preserves_cod by force

    lemma ide_hcomp [intro, simp]:
    assumes "ide \<nu>" and "ide \<mu>" and "src \<nu> = trg \<mu>"
    shows "ide (\<nu> \<star> \<mu>)"
      using assms VV.ide_char VV.arr_char H.preserves_ide [of "(\<nu>, \<mu>)"] by auto

    lemma hcomp_in_hhom [intro]:
    assumes "\<guillemotleft>\<mu> : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>\<nu> : b \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>\<nu> \<star> \<mu> : a \<rightarrow> c\<guillemotright>"
      using assms hseq_char by fastforce

    lemma hcomp_in_hhom' (* [simp] *):
    assumes "arr \<mu>" and "arr \<nu>" and "src \<mu> = a" and "trg \<nu> = c" and "src \<nu> = trg \<mu>"
    shows "\<guillemotleft>\<nu> \<star> \<mu> : a \<rightarrow> c\<guillemotright>"
      using assms hseq_char by fastforce

    lemma hcomp_in_hhomE [elim]:
    assumes "\<guillemotleft>\<nu> \<star> \<mu> : a \<rightarrow> c\<guillemotright>"
    and "\<lbrakk> arr \<mu>; arr \<nu>; src \<nu> = trg \<mu>; src \<mu> = a; trg \<nu> = c \<rbrakk> \<Longrightarrow> T"
    shows T
      using assms in_hhom_def by fastforce

    lemma hcomp_in_vhom [intro]:
    assumes "\<guillemotleft>\<mu> : f \<Rightarrow> g\<guillemotright>" and "\<guillemotleft>\<nu> : h \<Rightarrow> k\<guillemotright>" and "src h = trg f"
    shows "\<guillemotleft>\<nu> \<star> \<mu> : h \<star> f \<Rightarrow> k \<star> g\<guillemotright>"
      using assms by fastforce

    lemma hcomp_in_vhom' [simp]:
    assumes "hseq \<nu> \<mu>"
    and "dom \<mu> = f" and "dom \<nu> = h" and "cod \<mu> = g" and "cod \<nu> = k"
    assumes "\<guillemotleft>\<mu> : f \<Rightarrow> g\<guillemotright>" and "\<guillemotleft>\<nu> : h \<Rightarrow> k\<guillemotright>" and "src h = trg f"
    shows "\<guillemotleft>\<nu> \<star> \<mu> : h \<star> f \<Rightarrow> k \<star> g\<guillemotright>"
      using assms by fastforce

    lemma hcomp_in_vhomE [elim]:
    assumes "\<guillemotleft>\<nu> \<star> \<mu> : f \<Rightarrow> g\<guillemotright>"
    and "\<lbrakk> arr \<mu>; arr \<nu>; src \<nu> = trg \<mu>; src \<mu> = src f; src \<mu> = src g;
           trg \<nu> = trg f; trg \<nu> = trg g \<rbrakk> \<Longrightarrow> T"
    shows T
      using assms in_hom_def
      by (metis in_homE hseqE src_cod src_dom src_hcomp trg_cod trg_dom trg_hcomp)

    text \<open>
      A horizontal composition yields a weak composition by simply forgetting
      the \<open>src\<close> and \<open>trg\<close> functors.
    \<close>

    lemma match_1:
    assumes "\<nu> \<star> \<mu> \<noteq> null" and "(\<nu> \<star> \<mu>) \<star> \<tau> \<noteq> null"
    shows "\<mu> \<star> \<tau> \<noteq> null"
      using assms H.is_extensional not_arr_null VV.arr_char hseq_char hseq_char' by auto

    lemma match_2:
    assumes "\<nu> \<star> (\<mu> \<star> \<tau>) \<noteq> null" and "\<mu> \<star> \<tau> \<noteq> null"
    shows "\<nu> \<star> \<mu> \<noteq> null"
      using assms H.is_extensional not_arr_null VV.arr_char hseq_char hseq_char' by auto

    lemma match_3:
    assumes "\<mu> \<star> \<tau> \<noteq> null" and "\<nu> \<star> \<mu> \<noteq> null"
    shows "(\<nu> \<star> \<mu>) \<star> \<tau> \<noteq> null"
      using assms H.is_extensional not_arr_null VV.arr_char hseq_char hseq_char' by auto

    lemma match_4:
    assumes "\<mu> \<star> \<tau> \<noteq> null" and "\<nu> \<star> \<mu> \<noteq> null"
    shows "\<nu> \<star> (\<mu> \<star> \<tau>) \<noteq> null"
      using assms H.is_extensional not_arr_null VV.arr_char hseq_char hseq_char' by auto

    lemma left_connected:
    assumes "seq \<nu> \<nu>'"
    shows "\<nu> \<star> \<mu> \<noteq> null \<longleftrightarrow> \<nu>' \<star> \<mu> \<noteq> null"
      using assms H.is_extensional not_arr_null VV.arr_char hseq_char'
      by (metis hseq_char seqE vseq_implies_hpar(1))

    lemma right_connected:
    assumes "seq \<mu> \<mu>'"
    shows "H \<nu> \<mu> \<noteq> null \<longleftrightarrow> H \<nu> \<mu>' \<noteq> null"
      using assms H.is_extensional not_arr_null VV.arr_char hseq_char'
      by (metis hseq_char seqE vseq_implies_hpar(2))

    proposition is_weak_composition:
    shows "weak_composition V H"
    proof -
      have 1: "(\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu> \<noteq> null)
                 = (\<lambda>\<mu>\<nu>. arr (fst \<mu>\<nu>) \<and> arr (snd \<mu>\<nu>) \<and> src (fst \<mu>\<nu>) = trg (snd \<mu>\<nu>))"
        using hseq_char' by auto
      interpret VoV: subcategory VxV.comp \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu> \<noteq> null\<close>
        using 1 VV.subcategory_axioms by simp
      interpret H: "functor" VoV.comp V \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu>\<close>
        using H.functor_axioms 1 by simp
      show ?thesis
        using match_1 match_2 match_3 match_4 left_connected right_connected
        by (unfold_locales, metis)
    qed

    interpretation weak_composition V H
      using is_weak_composition by auto

     text \<open>
      It can be shown that \<open>arr ((\<nu> \<cdot> \<mu>) \<star> (\<tau> \<cdot> \<sigma>)) \<Longrightarrow> (\<nu> \<cdot> \<mu>) \<star> (\<tau> \<cdot> \<sigma>) = (\<nu> \<star> \<tau>) \<cdot> (\<mu> \<star> \<sigma>)\<close>.
      However, we do not have \<open>arr ((\<nu> \<star> \<tau>) \<cdot> (\<mu> \<star> \<sigma>)) \<Longrightarrow> (\<nu> \<cdot> \<mu>) \<star> (\<tau> \<cdot> \<sigma>) = (\<nu> \<star> \<tau>) \<cdot> (\<mu> \<star> \<sigma>)\<close>,
      because it does not follow from \<open>arr ((\<nu> \<star> \<tau>) \<cdot> (\<mu> \<star> \<sigma>))\<close> that \<open>dom \<nu> = cod \<mu>\<close>
      and \<open>dom \<tau> = cod \<sigma>\<close>, only that \<open>dom \<nu> \<star> dom \<tau> = cod \<mu> \<star> cod \<sigma>\<close>.
      So we don't get interchange unconditionally.
    \<close>

    lemma interchange:
    assumes "seq \<nu> \<mu>" and "seq \<tau> \<sigma>"
    shows "(\<nu> \<cdot> \<mu>) \<star> (\<tau> \<cdot> \<sigma>) = (\<nu> \<star> \<tau>) \<cdot> (\<mu> \<star> \<sigma>)"
      using assms interchange by simp

    lemma whisker_right:
    assumes "ide f" and "seq \<nu> \<mu>"
    shows "(\<nu> \<cdot> \<mu>) \<star> f = (\<nu> \<star> f) \<cdot> (\<mu> \<star> f)"
      using assms whisker_right by simp

    lemma whisker_left:
    assumes "ide f" and "seq \<nu> \<mu>"
    shows "f \<star> (\<nu> \<cdot> \<mu>) = (f \<star> \<nu>) \<cdot> (f \<star> \<mu>)"
      using assms whisker_left by simp

    lemma inverse_arrows_hcomp:
    assumes "iso \<mu>" and "iso \<nu>" and "src \<nu> = trg \<mu>"
    shows "inverse_arrows (\<nu> \<star> \<mu>) (inv \<nu> \<star> inv \<mu>)"
    proof -
      show "inverse_arrows (\<nu> \<star> \<mu>) (inv \<nu> \<star> inv \<mu>)"
      proof
        show "ide ((inv \<nu> \<star> inv \<mu>) \<cdot> (\<nu> \<star> \<mu>))"
        proof -
          have "(inv \<nu> \<star> inv \<mu>) \<cdot> (\<nu> \<star> \<mu>) = dom \<nu> \<star> dom \<mu>"
            using assms interchange iso_is_arr comp_inv_arr'
            by (metis arr_dom)
          thus ?thesis
            using assms iso_is_arr by simp
        qed
        show "ide ((\<nu> \<star> \<mu>) \<cdot> (inv \<nu> \<star> inv \<mu>))"
        proof -
          have "(\<nu> \<star> \<mu>) \<cdot> (inv \<nu> \<star> inv \<mu>) = cod \<nu> \<star> cod \<mu>"
            using assms interchange iso_is_arr comp_arr_inv'
            by (metis arr_cod)
          thus ?thesis
            using assms iso_is_arr by simp
        qed
      qed
    qed

    lemma iso_hcomp [intro, simp]:
    assumes "iso \<mu>" and "iso \<nu>" and "src \<nu> = trg \<mu>"
    shows "iso (\<nu> \<star> \<mu>)"
      using assms inverse_arrows_hcomp by auto

    lemma isomorphic_implies_ide:
    assumes "f \<cong> g"
    shows "ide f" and "ide g"
      using assms isomorphic_def by auto

    lemma hcomp_ide_isomorphic:
    assumes "ide f" and "g \<cong> h" and "src f = trg g"
    shows "f \<star> g \<cong> f \<star> h"
    proof -
      obtain \<mu> where \<mu>: "iso \<mu> \<and> \<guillemotleft>\<mu> : g \<Rightarrow> h\<guillemotright>"
        using assms isomorphic_def by auto
      have "iso (f \<star> \<mu>) \<and> \<guillemotleft>f \<star> \<mu> : f \<star> g \<Rightarrow> f \<star> h\<guillemotright>"
        using assms \<mu> iso_hcomp by auto
      thus ?thesis
        using isomorphic_def by auto
    qed

    lemma hcomp_isomorphic_ide:
    assumes "f \<cong> g" and "ide h" and "src f = trg h"
    shows "f \<star> h \<cong> g \<star> h"
    proof -
      obtain \<mu> where \<mu>: "iso \<mu> \<and> \<guillemotleft>\<mu> : f \<Rightarrow> g\<guillemotright>"
        using assms isomorphic_def by auto
      have "iso (\<mu> \<star> h) \<and> \<guillemotleft>\<mu> \<star> h : f \<star> h \<Rightarrow> g \<star> h\<guillemotright>"
        using assms \<mu> iso_hcomp by auto
      thus ?thesis
        using isomorphic_def by auto
    qed

    lemma isomorphic_implies_hpar:
    assumes "f \<cong> f'"
    shows "ide f" and "ide f'" and "src f = src f'" and "trg f = trg f'"
      using assms isomorphic_def by auto

    lemma inv_hcomp [simp]:
    assumes "iso \<nu>" and "iso \<mu>" and "src \<nu> = trg \<mu>"
    shows "inv (\<nu> \<star> \<mu>) = inv \<nu> \<star> inv \<mu>"
      using assms inverse_arrow_unique [of "\<nu> \<star> \<mu>"] inv_is_inverse inverse_arrows_hcomp
      by auto

    interpretation VxVxV: product_category V VxV.comp ..
    interpretation VVV: subcategory VxVxV.comp
                          \<open>\<lambda>\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> VV.arr (snd \<tau>\<mu>\<nu>) \<and>
                                 src (fst \<tau>\<mu>\<nu>) = trg (fst (snd \<tau>\<mu>\<nu>))\<close>
      using subcategory_VVV by auto

    text \<open>
      The following define the two ways of using horizontal composition to compose three arrows.
    \<close>

    definition HoHV
    where "HoHV \<mu> \<equiv> if VVV.arr \<mu> then (fst \<mu> \<star> fst (snd \<mu>)) \<star> snd (snd \<mu>) else null"

    definition HoVH
    where "HoVH \<mu> \<equiv> if VVV.arr \<mu> then fst \<mu> \<star> fst (snd \<mu>) \<star> snd (snd \<mu>) else null"

    lemma functor_HoHV:
    shows "functor VVV.comp V HoHV"
      apply unfold_locales
      using VVV.arr_char VV.arr_char VVV.dom_char VVV.cod_char VVV.comp_char HoHV_def
          apply auto[4]
    proof -
      fix f g
      assume fg: "VVV.seq g f"
      show "HoHV (VVV.comp g f) = HoHV g \<cdot> HoHV f"
      proof -
        have "VxVxV.comp g f =
              (fst g \<cdot> fst f, fst (snd g) \<cdot> fst (snd f), snd (snd g) \<cdot> snd (snd f))"
          using fg VVV.seq_char VVV.arr_char VV.arr_char VxVxV.comp_char VxV.comp_char
          by (metis (no_types, lifting) VxV.seqE VxVxV.seqE)
        hence "HoHV (VVV.comp g f) =
              (fst g \<cdot> fst f \<star> fst (snd g) \<cdot> fst (snd f)) \<star> snd (snd g) \<cdot> snd (snd f)"
          using HoHV_def VVV.comp_simp fg by auto
        also have "... = ((fst g \<star> fst (snd g)) \<star> snd (snd g)) \<cdot>
                           ((fst f \<star> fst (snd f)) \<star> snd (snd f))"
          using fg VVV.seq_char VVV.arr_char VV.arr_char interchange
          by (metis (no_types, lifting) VxV.seqE VxVxV.seqE hseqI' src_vcomp trg_vcomp)
        also have "... = HoHV g \<cdot> HoHV f"
          using HoHV_def fg by auto
        finally show ?thesis by simp
      qed
    qed

    lemma functor_HoVH:
    shows "functor VVV.comp V HoVH"
      apply unfold_locales
      using VVV.arr_char VV.arr_char VVV.dom_char VVV.cod_char VVV.comp_char
            HoHV_def HoVH_def
          apply auto[4]
    proof -
      fix f g
      assume fg: "VVV.seq g f"
      show "HoVH (VVV.comp g f) = HoVH g \<cdot> HoVH f"
      proof -
        have "VxVxV.comp g f =
              (fst g \<cdot> fst f, fst (snd g) \<cdot> fst (snd f), snd (snd g) \<cdot> snd (snd f))"
          using fg VVV.seq_char VVV.arr_char VV.arr_char VxVxV.comp_char VxV.comp_char
          by (metis (no_types, lifting) VxV.seqE VxVxV.seqE)
        hence "HoVH (VVV.comp g f) =
              fst g \<cdot> fst f \<star> fst (snd g) \<cdot> fst (snd f) \<star> snd (snd g) \<cdot> snd (snd f)"
          using HoVH_def VVV.comp_simp fg by auto
        also have "... = (fst g \<star> fst (snd g) \<star> snd (snd g)) \<cdot>
                           (fst f \<star> fst (snd f) \<star> snd (snd f))"
          using fg VVV.seq_char VVV.arr_char VV.arr_char interchange
          by (metis (no_types, lifting) VxV.seqE VxVxV.seqE hseqI' src_vcomp trg_vcomp)
        also have "... = HoVH g \<cdot> HoVH f"
          using fg VVV.seq_char VVV.arr_char HoVH_def VVV.comp_char VV.arr_char
          by (metis (no_types, lifting))
        finally show ?thesis by simp
      qed
    qed

    text \<open>
      The following define horizontal composition of an arrow on the left by its target
      and on the right by its source.
    \<close>

    abbreviation L
    where "L \<equiv> \<lambda>\<mu>. if arr \<mu> then trg \<mu> \<star> \<mu> else null"

    abbreviation R
    where "R \<equiv> \<lambda>\<mu>. if arr \<mu> then \<mu> \<star> src \<mu> else null"

    lemma endofunctor_L:
    shows "endofunctor V L"
      using vseq_implies_hpar(2) whisker_left
      by (unfold_locales, auto)

    lemma endofunctor_R:
    shows "endofunctor V R"
      using vseq_implies_hpar(1) whisker_right
      by (unfold_locales, auto)

  end

end
