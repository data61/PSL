(*  Title:       Coherence
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Coherence"

theory Coherence
imports Bicategory
begin

 text \<open>
   \sloppypar
   In this section, we generalize to bicategories the proof of the Coherence Theorem
   that we previously gave for monoidal categories
   (see \<open>MonoidalCategory.evaluation_map.coherence\<close> in @{session MonoidalCategory}).
   As was the case for the previous proof, the current proof takes a syntactic approach.
   First we define a formal ``bicategorical language'' of terms constructed using
   syntactic operators that correspond to the various operations (vertical and horizontal
   composition, associators and unitors) found in a bicategory.
   Terms of the language are classified as formal ``arrows'', ``identities'', or ``objects''
   according to the syntactic operators used in their formation.
   A class of terms called ``canonical'' is also defined in this way.
   Functions that map ``arrows'' to their ``domain'' and ``codomain'', and to their
   ``source'' and ``target'' are defined by recursion on the structure of terms.
   Next, we define a notion of ``normal form'' for terms in this language and we
   give a recursive definition of a function that maps terms to their normal forms.
   Normalization moves vertical composition inside of horizontal composition and
   ``flattens'' horizontal composition by associating all horizontal compositions to the right.
   In addition, normalization deletes from a term any horizontal composites involving an arrow
   and its source or target, replacing such composites by just the arrow itself.
   We then define a ``reduction function'' that maps each identity term \<open>t\<close> to a
   ``canonical'' term \<open>t\<^bold>\<down>\<close> that connects \<open>t\<close> with its normal form.  The definition of reduction
   is also recursive, but it is somewhat more complex than normalization in that it
   involves two mutually recursive functions: one that applies to any identity term
   and another that applies only to terms that are the horizontal composite
   of two identity terms.

   The next step is to define an ``evaluation function'' that evaluates terms in a given
   bicategory (which is left as an unspecified parameter).  We show that evaluation respects
   bicategorical structure:
   the domain, codomain, source, and target mappings on terms correspond under evaluation
   to the actual domain, codomain, source and target mappings on the given bicategory,
   the vertical and horizontal composition on terms correspond to the actual vertical
   and horizontal composition of the bicategory, and unit and associativity terms evaluate
   to the actual unit and associativity isomorphisms of the bicategory.
   In addition, ``object terms'' evaluate to objects (\emph{i.e.}~0-cells),
   ``identity terms'' evaluate to identities (\emph{i.e.}~1-cells),
   ``arrow terms'' evaluate to arrows (\emph{i.e.}~2-cells), and ``canonical terms'' evaluate
   to canonical isomorphisms.
   A term is defined to be ``coherent'' if, roughly speaking, it is a formal arrow
   whose evaluation commutes with the evaluations of the reductions to normal form of
   its domain and codomain.
   We then prove the Coherence Theorem, expressed in the form: ``every arrow is coherent.''
   This implies a more classical version of the Coherence Theorem, which says that:
   ``syntactically parallel arrows with the same normal form have equal evaluations''.
  \<close>

  subsection "Bicategorical Language"

    text \<open>
      For the most part, the definition of the ``bicategorical language'' of terms is
      a straightforward generalization of the ``monoidal language'' that we used for
      monoidal categories.
      Some modifications are required, however, due to the fact that horizontal composition
      in a bicategory is a partial operation, whereas the the tensor product in a monoidal
      category is well-defined for all pairs of arrows.
      One difference is that we have found it necessary to introduce a new class of primitive
      terms whose elements represent ``formal objects'', so that there is some way to
      identify the source and target of what would otherwise be an empty horizontal composite.
      This was not an issue for monoidal categories, because the totality of horizontal
      composition meant that there was no need for syntactically defined sources and targets.
      Another difference is what we have chosen for the ``generators'' of the language
      and how they are used to form primitive terms.  For monoidal categories,
      we supposed that we were given a category \<open>C\<close> and the syntax contained a constructor
      to form a primitive term corresponding to each arrow of \<open>C\<close>.
      We assumed a category as the given data, rather than something less structured,
      such as a graph, because we were primarily interested in the tensor product and
      the associators and unitors, and were relatively uninterested in the strictly
      associative and unital composition of the underlying category.
      For bicategories, we also take the vertical composition as given for the same
      reasons; however, this is not yet sufficient due to the fact that horizontal
      composition in a bicategory is a partial operation, in contrast to the tensor
      product in a monoidal category, which is defined for all pairs of arrows.
      To deal with this issue, for bicategories we assume that source and target
      mappings are also given, so that the given data forms a category with
      ``horizontal homs''.  The given source and target mappings are extended to all terms
      and used to define when two terms are ``formally horizontally composable''.
  \<close>

  locale bicategorical_language =
    category V +
    horizontal_homs V src trg
    for V :: "'a comp"                       (infixr "\<cdot>" 55)
    and src :: "'a \<Rightarrow> 'a"
    and trg :: "'a \<Rightarrow> 'a"
  begin

    text \<open>
      Constructor \<open>Prim\<^sub>0\<close> is used to construct ``formal objects'' and \<open>Prim\<close> is used to
      construct primitive terms that are not formal objects.
    \<close>

    datatype (discs_sels) 't "term" =
      Prim\<^sub>0 't                             ("\<^bold>\<langle>_\<^bold>\<rangle>\<^sub>0")
    | Prim 't                              ("\<^bold>\<langle>_\<^bold>\<rangle>")
    | Hcomp "'t term" "'t term"            (infixr "\<^bold>\<star>" 53)
    | Vcomp "'t term" "'t term"            (infixr "\<^bold>\<cdot>" 55)
    | Lunit "'t term"                      ("\<^bold>\<l>\<^bold>[_\<^bold>]")
    | Lunit' "'t term"                     ("\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[_\<^bold>]")
    | Runit "'t term"                      ("\<^bold>\<r>\<^bold>[_\<^bold>]")
    | Runit' "'t term"                     ("\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[_\<^bold>]")
    | Assoc "'t term" "'t term" "'t term"  ("\<^bold>\<a>\<^bold>[_, _, _\<^bold>]")
    | Assoc' "'t term" "'t term" "'t term" ("\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[_, _, _\<^bold>]")

    text \<open>
      We define formal domain, codomain, source, and target functions on terms.
    \<close>

    primrec Src :: "'a term \<Rightarrow> 'a term"
    where "Src \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0"
        | "Src \<^bold>\<langle>\<mu>\<^bold>\<rangle> = \<^bold>\<langle>src \<mu>\<^bold>\<rangle>\<^sub>0"
        | "Src (t \<^bold>\<star> u) = Src u"
        | "Src (t \<^bold>\<cdot> u) = Src t"
        | "Src \<^bold>\<l>\<^bold>[t\<^bold>] = Src t"
        | "Src \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Src t"
        | "Src \<^bold>\<r>\<^bold>[t\<^bold>] = Src t"
        | "Src \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Src t"
        | "Src \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = Src v"
        | "Src \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = Src v"

    primrec Trg :: "'a term \<Rightarrow> 'a term"
    where "Trg \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0"
        | "Trg \<^bold>\<langle>\<mu>\<^bold>\<rangle> = \<^bold>\<langle>trg \<mu>\<^bold>\<rangle>\<^sub>0"
        | "Trg (t \<^bold>\<star> u) = Trg t"
        | "Trg (t \<^bold>\<cdot> u) = Trg t"
        | "Trg \<^bold>\<l>\<^bold>[t\<^bold>] = Trg t"
        | "Trg \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Trg t"
        | "Trg \<^bold>\<r>\<^bold>[t\<^bold>] = Trg t"
        | "Trg \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Trg t"
        | "Trg \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = Trg t"
        | "Trg \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = Trg t"

    primrec Dom :: "'a term \<Rightarrow> 'a term"
    where "Dom \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0"
        | "Dom \<^bold>\<langle>\<mu>\<^bold>\<rangle> = \<^bold>\<langle>dom \<mu>\<^bold>\<rangle>"
        | "Dom (t \<^bold>\<star> u) = Dom t \<^bold>\<star> Dom u"
        | "Dom (t \<^bold>\<cdot> u) = Dom u"
        | "Dom \<^bold>\<l>\<^bold>[t\<^bold>] = Trg t \<^bold>\<star> Dom t"
        | "Dom \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Dom t"
        | "Dom \<^bold>\<r>\<^bold>[t\<^bold>] = Dom t \<^bold>\<star> Src t"
        | "Dom \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Dom t"
        | "Dom \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = (Dom t \<^bold>\<star> Dom u) \<^bold>\<star> Dom v"
        | "Dom \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = Dom t \<^bold>\<star> (Dom u \<^bold>\<star> Dom v)"

    primrec Cod :: "'a term \<Rightarrow> 'a term"
    where "Cod \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0"
        | "Cod \<^bold>\<langle>\<mu>\<^bold>\<rangle> = \<^bold>\<langle>cod \<mu>\<^bold>\<rangle>"
        | "Cod (t \<^bold>\<star> u) = Cod t \<^bold>\<star> Cod u"
        | "Cod (t \<^bold>\<cdot> u) = Cod t"
        | "Cod \<^bold>\<l>\<^bold>[t\<^bold>] = Cod t"
        | "Cod \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Trg t \<^bold>\<star> Cod t"
        | "Cod \<^bold>\<r>\<^bold>[t\<^bold>] = Cod t"
        | "Cod \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Cod t \<^bold>\<star> Src t"
        | "Cod \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = Cod t \<^bold>\<star> (Cod u \<^bold>\<star> Cod v)"
        | "Cod \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = (Cod t \<^bold>\<star> Cod u) \<^bold>\<star> Cod v"

    text \<open>
      A term is a ``formal arrow'' if it is constructed from primitive arrows in such a way
      that horizontal and vertical composition are applied only to formally composable pairs
      of terms.  The definitions of ``formal identity'' and ``formal object'' follow a
      similar pattern.
    \<close>

    primrec Arr :: "'a term \<Rightarrow> bool"
    where "Arr \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = obj \<mu>"
        | "Arr \<^bold>\<langle>\<mu>\<^bold>\<rangle> = arr \<mu>"
        | "Arr (t \<^bold>\<star> u) = (Arr t \<and> Arr u \<and> Src t = Trg u)"
        | "Arr (t \<^bold>\<cdot> u) = (Arr t \<and> Arr u \<and> Dom t = Cod u)"
        | "Arr \<^bold>\<l>\<^bold>[t\<^bold>] = Arr t"
        | "Arr \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Arr t"
        | "Arr \<^bold>\<r>\<^bold>[t\<^bold>] = Arr t"
        | "Arr \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Arr t"
        | "Arr \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = (Arr t \<and> Arr u \<and> Arr v \<and> Src t = Trg u \<and> Src u = Trg v)"
        | "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = (Arr t \<and> Arr u \<and> Arr v \<and> Src t = Trg u \<and> Src u = Trg v)"

    primrec Ide :: "'a term \<Rightarrow> bool"
    where "Ide \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = obj \<mu>"
        | "Ide \<^bold>\<langle>\<mu>\<^bold>\<rangle> = ide \<mu>"
        | "Ide (t \<^bold>\<star> u) = (Ide t \<and> Ide u \<and> Src t = Trg u)"
        | "Ide (t \<^bold>\<cdot> u) = False"
        | "Ide \<^bold>\<l>\<^bold>[t\<^bold>] = False"
        | "Ide \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = False"
        | "Ide \<^bold>\<r>\<^bold>[t\<^bold>] = False"
        | "Ide \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = False"
        | "Ide \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = False"
        | "Ide \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = False"

    primrec Obj :: "'a term \<Rightarrow> bool"
    where "Obj \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = obj \<mu>"
        | "Obj \<^bold>\<langle>\<mu>\<^bold>\<rangle> = False"
        | "Obj (t \<^bold>\<star> u) = False"
        | "Obj (t \<^bold>\<cdot> u) = False"
        | "Obj \<^bold>\<l>\<^bold>[t\<^bold>] = False"
        | "Obj \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = False"
        | "Obj \<^bold>\<r>\<^bold>[t\<^bold>] = False"
        | "Obj \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = False"
        | "Obj \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = False"
        | "Obj \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = False"

    abbreviation HSeq :: "'a term \<Rightarrow> 'a term \<Rightarrow> bool"
    where "HSeq t u \<equiv> Arr t \<and> Arr u \<and> Src t = Trg u"

    abbreviation VSeq :: "'a term \<Rightarrow> 'a term \<Rightarrow> bool"
    where "VSeq t u \<equiv> Arr t \<and> Arr u \<and> Dom t = Cod u"

    abbreviation HPar :: "'a term => 'a term \<Rightarrow> bool"
    where "HPar t u \<equiv> Arr t \<and> Arr u \<and> Src t = Src u \<and> Trg t = Trg u"

    abbreviation VPar :: "'a term => 'a term \<Rightarrow> bool"
    where "VPar t u \<equiv> Arr t \<and> Arr u \<and> Dom t = Dom u \<and> Cod t = Cod u"

    abbreviation HHom :: "'a term \<Rightarrow> 'a term \<Rightarrow> 'a term set"
    where "HHom a b \<equiv> { t. Arr t \<and> Src t = a \<and> Trg t = b }"

    abbreviation VHom :: "'a term \<Rightarrow> 'a term \<Rightarrow> 'a term set"
    where "VHom f g \<equiv> { t. Arr t \<and> Dom t = f \<and> Cod t = g }"

    lemma is_Prim0_Src:
    shows "is_Prim\<^sub>0 (Src t)"
      by (induct t; simp)

    lemma is_Prim0_Trg:
    shows "is_Prim\<^sub>0 (Trg t)"
      by (induct t; simp)

    lemma Src_Src [simp]:
    shows "Arr t \<Longrightarrow> Src (Src t) = Src t"
      by (induct t) auto

    lemma Trg_Trg [simp]:
    shows "Arr t \<Longrightarrow> Trg (Trg t) = Trg t"
      by (induct t) auto

    lemma Src_Trg [simp]:
    shows "Arr t \<Longrightarrow> Src (Trg t) = Trg t"
      by (induct t) auto

    lemma Trg_Src [simp]:
    shows "Arr t \<Longrightarrow> Trg (Src t) = Src t"
      by (induct t) auto

    lemma Dom_Src [simp]:
    shows "Arr t \<Longrightarrow> Dom (Src t) = Src t"
      by (induct t) auto

    lemma Dom_Trg [simp]:
    shows "Arr t \<Longrightarrow> Dom (Trg t) = Trg t"
      by (induct t) auto

    lemma Cod_Src [simp]:
    shows "Arr t \<Longrightarrow> Cod (Src t) = Src t"
      by (induct t) auto

    lemma Cod_Trg [simp]:
    shows "Arr t \<Longrightarrow> Cod (Trg t) = Trg t"
      by (induct t) auto

    lemma Src_Dom_Cod:
    shows "Arr t \<Longrightarrow> Src (Dom t) = Src t \<and> Src (Cod t) = Src t"
       using src_dom src_cod by (induct t) auto

    lemma Src_Dom [simp]:
    shows "Arr t \<Longrightarrow> Src (Dom t) = Src t"
      using Src_Dom_Cod by blast

    lemma Src_Cod [simp]:
    shows "Arr t \<Longrightarrow> Src (Cod t) = Src t"
      using Src_Dom_Cod by blast

    lemma Trg_Dom_Cod:
    shows "Arr t \<Longrightarrow> Trg (Dom t) = Trg t \<and> Trg (Cod t) = Trg t"
       using trg_dom trg_cod by (induct t) auto

    lemma Trg_Dom [simp]:
    shows "Arr t \<Longrightarrow> Trg (Dom t) = Trg t"
      using Trg_Dom_Cod by blast

    lemma Trg_Cod [simp]:
    shows "Arr t \<Longrightarrow> Trg (Cod t) = Trg t"
      using Trg_Dom_Cod by blast

    lemma VSeq_implies_HPar:
    shows "VSeq t u \<Longrightarrow> HPar t u"
      using Src_Dom [of t] Src_Cod [of u] Trg_Dom [of t] Trg_Cod [of u] by auto

    lemma Dom_Dom [simp]:
    shows "Arr t \<Longrightarrow> Dom (Dom t) = Dom t"
      by (induct t, auto)

    lemma Cod_Cod [simp]:
    shows "Arr t \<Longrightarrow> Cod (Cod t) = Cod t"
      by (induct t, auto)

    lemma Dom_Cod [simp]:
    shows "Arr t \<Longrightarrow> Dom (Cod t) = Cod t"
      by (induct t, auto)

    lemma Cod_Dom [simp]:
    shows "Arr t \<Longrightarrow> Cod (Dom t) = Dom t"
      by (induct t, auto)
      
    lemma Obj_implies_Ide [simp]:
    shows "Obj t \<Longrightarrow> Ide t"
      by (induct t) auto

    lemma Ide_implies_Arr [simp]:
    shows "Ide t \<Longrightarrow> Arr t"
      by (induct t, auto)

    lemma Dom_Ide:
    shows "Ide t \<Longrightarrow> Dom t = t"
      by (induct t, auto)

    lemma Cod_Ide:
    shows "Ide t \<Longrightarrow> Cod t = t"
      by (induct t, auto)

    lemma Obj_Src [simp]:
    shows "Arr t \<Longrightarrow> Obj (Src t)"
      by (induct t) auto

    lemma Obj_Trg [simp]:
    shows "Arr t \<Longrightarrow> Obj (Trg t)"
      by (induct t) auto

    lemma Ide_Dom [simp]:
    shows "Arr t \<Longrightarrow> Ide (Dom t)"
      by (induct t, auto)

    lemma Ide_Cod [simp]:
    shows "Arr t \<Longrightarrow> Ide (Cod t)"
      by (induct t, auto)

    lemma Arr_in_Hom:
    assumes "Arr t"
    shows "t \<in> HHom (Src t) (Trg t)" and "t \<in> VHom (Dom t) (Cod t)"
    proof -
      have 1: "Arr t \<Longrightarrow> t \<in> HHom (Src t) (Trg t) \<and> t \<in> VHom (Dom t) (Cod t)"
        by (induct t, auto)
      show "t \<in> HHom (Src t) (Trg t)" using assms 1 by simp
      show "t \<in> VHom (Dom t) (Cod t)" using assms 1 by simp
    qed

    lemma Ide_in_Hom:
    assumes "Ide t"
    shows "t \<in> HHom (Src t) (Trg t)" and "t \<in> VHom t t"
    proof -
      have 1: "Ide t \<Longrightarrow> t \<in> HHom (Src t) (Trg t) \<and> t \<in> VHom t t"
        by (induct t, auto)
      show "t \<in> HHom (Src t) (Trg t)" using assms 1 by simp
      show "t \<in> VHom t t" using assms 1 by simp
    qed

    lemma Obj_in_Hom:
    assumes "Obj t"
    shows "t \<in> HHom t t" and "t \<in> VHom t t"
    proof -
      have 1: "Obj t \<Longrightarrow> t \<in> HHom t t \<and> t \<in> VHom t t"
        by (induct t, auto)
      show "t \<in> HHom t t" using assms 1 by simp
      show "t \<in> VHom t t" using assms 1 by simp
    qed

    text \<open>
      A formal arrow is ``canonical'' if the only primitive arrows used in its construction
      are objects and identities.
    \<close>

    primrec Can :: "'a term \<Rightarrow> bool"
    where "Can \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = obj \<mu>"
        | "Can \<^bold>\<langle>\<mu>\<^bold>\<rangle> = ide \<mu>"
        | "Can (t \<^bold>\<star> u) = (Can t \<and> Can u \<and> Src t = Trg u)"
        | "Can (t \<^bold>\<cdot> u) = (Can t \<and> Can u \<and> Dom t = Cod u)"
        | "Can \<^bold>\<l>\<^bold>[t\<^bold>] = Can t"
        | "Can \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Can t"
        | "Can \<^bold>\<r>\<^bold>[t\<^bold>] = Can t"
        | "Can \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = Can t"
        | "Can \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = (Can t \<and> Can u \<and> Can v \<and> Src t = Trg u \<and> Src u = Trg v)"
        | "Can \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = (Can t \<and> Can u \<and> Can v \<and> Src t = Trg u \<and> Src u = Trg v)"

    lemma Ide_implies_Can:
    shows "Ide t \<Longrightarrow> Can t"
      by (induct t, auto)

    lemma Can_implies_Arr:
    shows "Can t \<Longrightarrow> Arr t"
      by (induct t, auto)

    text \<open>
      Canonical arrows can be formally inverted.
    \<close>

    primrec Inv :: "'a term \<Rightarrow> 'a term"
    where "Inv \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0"
        | "Inv \<^bold>\<langle>\<mu>\<^bold>\<rangle> = \<^bold>\<langle>inv \<mu>\<^bold>\<rangle>"
        | "Inv (t \<^bold>\<star> u) = (Inv t \<^bold>\<star> Inv u)"
        | "Inv (t \<^bold>\<cdot> u) = (Inv u \<^bold>\<cdot> Inv t)"
        | "Inv \<^bold>\<l>\<^bold>[t\<^bold>] = \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Inv t\<^bold>]"
        | "Inv \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = \<^bold>\<l>\<^bold>[Inv t\<^bold>]"
        | "Inv \<^bold>\<r>\<^bold>[t\<^bold>] = \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Inv t\<^bold>]"
        | "Inv \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = \<^bold>\<r>\<^bold>[Inv t\<^bold>]"
        | "Inv \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Inv t, Inv u, Inv v\<^bold>]"
        | "Inv \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = \<^bold>\<a>\<^bold>[Inv t, Inv u, Inv v\<^bold>]"

    lemma Src_Inv [simp]:
    shows "Can t \<Longrightarrow> Src (Inv t) = Src t"
      using Can_implies_Arr VSeq_implies_HPar
      apply (induct t, auto)
      by metis

    lemma Trg_Inv [simp]:
    shows "Can t \<Longrightarrow> Trg (Inv t) = Trg t"
      using Can_implies_Arr VSeq_implies_HPar 
      apply (induct t, auto)
      by metis

    lemma Dom_Inv [simp]:
    shows "Can t \<Longrightarrow> Dom (Inv t) = Cod t"
      by (induct t, auto)

    lemma Cod_Inv [simp]:
    shows "Can t \<Longrightarrow> Cod (Inv t) = Dom t"
      by (induct t, auto)

    lemma Inv_preserves_Ide:
    shows "Ide t \<Longrightarrow> Ide (Inv t)"
      using Ide_implies_Can by (induct t, auto)

    lemma Can_Inv [simp]:
    shows "Can t \<Longrightarrow> Can (Inv t)"
      by (induct t, auto)

    lemma Inv_in_Hom [intro]:
    assumes "Can t"
    shows "Inv t \<in> HHom (Src t) (Trg t)" and "Inv t \<in> VHom (Cod t) (Dom t)"
      using assms Can_Inv Can_implies_Arr by simp_all

    lemma Inv_Ide [simp]:
    assumes "Ide a"
    shows "Inv a = a"
      using assms by (induct a, auto)

    lemma Inv_Inv [simp]:
    assumes "Can t"
    shows "Inv (Inv t) = t"
      using assms by (induct t, auto)

    subsection "Normal Terms"

    text \<open>
      We call a term ``normal'' if it is either a formal object or it is constructed from
      primitive arrows using only horizontal composition associated to the right.
      Essentially, such terms are (typed) composable sequences of arrows of @{term V},
      where the empty list is represented by a formal object and \<open>\<^bold>\<star>\<close> is used as
      the list constructor.
    \<close>

    fun Nml :: "'a term \<Rightarrow> bool"
    where "Nml \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = obj \<mu>"
        | "Nml \<^bold>\<langle>\<mu>\<^bold>\<rangle> = arr \<mu>"
        | "Nml (\<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<star> u) = (arr \<nu> \<and> Nml u \<and> \<not> is_Prim\<^sub>0 u \<and> \<^bold>\<langle>src \<nu>\<^bold>\<rangle>\<^sub>0 = Trg u)"
        | "Nml _ = False"

    lemma Nml_HcompD:
    assumes "Nml (t \<^bold>\<star> u)"
    shows "\<^bold>\<langle>un_Prim t\<^bold>\<rangle> = t" and "arr (un_Prim t)" and "Nml t" and "Nml u"
    and "\<not> is_Prim\<^sub>0 u" and "\<^bold>\<langle>src (un_Prim t)\<^bold>\<rangle>\<^sub>0 = Trg u" and "Src t = Trg u"
    proof -
      have 1: "t = \<^bold>\<langle>un_Prim t\<^bold>\<rangle> \<and> arr (un_Prim t) \<and> Nml t \<and> Nml u \<and> \<not> is_Prim\<^sub>0 u \<and>
               \<^bold>\<langle>src (un_Prim t)\<^bold>\<rangle>\<^sub>0 = Trg u"
        using assms by (cases t; simp; cases u; simp)
      show "\<^bold>\<langle>un_Prim t\<^bold>\<rangle> = t" using 1 by simp
      show "arr (un_Prim t)" using 1 by simp
      show "Nml t" using 1 by simp
      show "Nml u" using 1 by simp
      show "\<not> is_Prim\<^sub>0 u" using 1 by simp
      show "\<^bold>\<langle>src (un_Prim t)\<^bold>\<rangle>\<^sub>0 = Trg u" using 1 by simp
      show "Src t = Trg u"
        using assms
        apply (cases t) by simp_all
    qed

    lemma Nml_implies_Arr:
    shows "Nml t \<Longrightarrow> Arr t"
      apply (induct t, auto)
      using Nml_HcompD by simp_all

    lemma Nml_Src [simp]:
    shows "Nml t \<Longrightarrow> Nml (Src t)"
      apply (induct t, simp_all)
      using Nml_HcompD by metis

    lemma Nml_Trg [simp]:
    shows "Nml t \<Longrightarrow> Nml (Trg t)"
      apply (induct t, simp_all)
      using Nml_HcompD by metis

    lemma Nml_Dom [simp]:
    shows "Nml t \<Longrightarrow> Nml (Dom t)"
    proof (induct t, simp_all add: Nml_HcompD)
      fix u v
      assume I1: "Nml (Dom u)"
      assume I2: "Nml (Dom v)"
      assume uv: "Nml (u \<^bold>\<star> v)"
      show "Nml (Dom u \<^bold>\<star> Dom v)"
      proof -
        have 1: "is_Prim (Dom u) \<and> arr (un_Prim (Dom u)) \<and> Dom u = \<^bold>\<langle>dom (un_Prim u)\<^bold>\<rangle>"
          using uv by (cases u; simp; cases v, simp_all)
        have 2: "Nml v \<and> \<not> is_Prim\<^sub>0 v \<and> \<not> is_Vcomp v \<and> \<not> is_Lunit' v \<and> \<not> is_Runit' v"
          using uv by (cases u, simp_all; cases v, simp_all)
        have "arr (dom (un_Prim u))"
          using 1 by fastforce
        moreover have "Nml (Dom v) \<and> \<not> is_Prim\<^sub>0 v"
          using 2 I2 by (cases v, simp_all)
        moreover have "\<^bold>\<langle>src (dom (un_Prim u))\<^bold>\<rangle>\<^sub>0 = Trg (Dom v)"
        proof -
          have "Trg (Dom v) = Src (Dom u)"
            using uv Nml_implies_Arr by fastforce
          also have "... = \<^bold>\<langle>src (dom (un_Prim u))\<^bold>\<rangle>\<^sub>0"
            using 1 by fastforce
          finally show ?thesis by argo
        qed
        moreover have "\<not> is_Prim\<^sub>0 (Dom v)"
          using 2 by (cases v, simp_all)
        ultimately show ?thesis using 1 2 by simp
      qed
    qed
    
    lemma Nml_Cod [simp]:
    shows "Nml t \<Longrightarrow> Nml (Cod t)"
    proof (induct t, simp_all add: Nml_HcompD)
      fix u v
      assume I1: "Nml (Cod u)"
      assume I2: "Nml (Cod v)"
      assume uv: "Nml (u \<^bold>\<star> v)"
      show "Nml (Cod u \<^bold>\<star> Cod v)"
      proof -
        have 1: "is_Prim (Cod u) \<and> arr (un_Prim (Cod u)) \<and> Cod u = \<^bold>\<langle>cod (un_Prim u)\<^bold>\<rangle>"
          using uv by (cases u; simp; cases v, simp_all)
        have 2: "Nml v \<and> \<not> is_Prim\<^sub>0 v \<and> \<not> is_Vcomp v \<and> \<not> is_Lunit' v \<and> \<not> is_Runit' v"
          using uv by (cases u; simp; cases v, simp_all)
        have "arr (cod (un_Prim u))"
          using 1 by fastforce
        moreover have "Nml (Cod v) \<and> \<not> is_Prim\<^sub>0 v"
          using 2 I2 by (cases v, simp_all)
        moreover have "\<^bold>\<langle>src (cod (un_Prim u))\<^bold>\<rangle>\<^sub>0 = Trg (Cod v)"
        proof -
          have "Trg (Cod v) = Src (Cod u)"
            using uv Nml_implies_Arr by fastforce
          also have "... = \<^bold>\<langle>src (cod (un_Prim u))\<^bold>\<rangle>\<^sub>0"
            using 1 by fastforce
          finally show ?thesis by argo
        qed
        moreover have "\<not> is_Prim\<^sub>0 (Cod v)"
          using 2 by (cases v; simp)
        ultimately show ?thesis using 1 2 by simp
      qed
    qed
    
    lemma Nml_Inv [simp]:
    assumes "Can t" and "Nml t"
    shows "Nml (Inv t)"
    proof -
      have "Can t \<and> Nml t \<Longrightarrow> Nml (Inv t)"
        apply (induct t, simp_all)
      proof -
        fix u v
        assume I1: "Nml u \<Longrightarrow> Nml (Inv u)"
        assume I2: "Nml v \<Longrightarrow> Nml (Inv v)"
        assume uv: "Can u \<and> Can v \<and> Src u = Trg v \<and> Nml (u \<^bold>\<star> v)"
        show "Nml (Inv u \<^bold>\<star> Inv v)"
        proof -
          have u: "Arr u \<and> Can u" using uv Can_implies_Arr by blast
          have v: "Arr v \<and> Can v" using uv Can_implies_Arr by blast
          have 1: "\<^bold>\<langle>un_Prim u\<^bold>\<rangle> = u \<and> ide (un_Prim u) \<and> Nml u \<and> Nml v \<and> \<not> is_Prim\<^sub>0 v \<and>
                   \<^bold>\<langle>src (un_Prim u)\<^bold>\<rangle>\<^sub>0 = Trg v"
            using uv Nml_HcompD [of u v] apply simp
            using uv by (cases u, simp_all)
          have 2: "\<^bold>\<langle>un_Prim (Inv u)\<^bold>\<rangle> = Inv u \<and> arr (un_Prim (Inv u)) \<and> Nml (Inv u)"
            using 1 by (cases u; simp)
          moreover have "Nml (Inv v) \<and> \<not> is_Prim\<^sub>0 (Inv v)"
            using 1 I2 by (cases v, simp_all)
          moreover have "\<^bold>\<langle>src (un_Prim (Inv u))\<^bold>\<rangle>\<^sub>0 = Trg (Inv v)"
            using 1 2 v by (cases u, simp_all)
          ultimately show ?thesis
            by (cases u, simp_all)
        qed
      qed
      thus ?thesis using assms by blast
    qed

    text \<open>
      The following function defines a horizontal composition for normal terms.
      If such terms are regarded as lists, this is just (typed) list concatenation.
    \<close>

    fun HcompNml  (infixr "\<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor>" 53)
    where "\<^bold>\<langle>\<nu>\<^bold>\<rangle>\<^sub>0 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u = u"
        | "t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = t"
        | "\<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u = \<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<star> u"
        | "(t \<^bold>\<star> u) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v)"
        | "t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u = undefined"

    lemma HcompNml_Prim [simp]:
    assumes "\<not> is_Prim\<^sub>0 t"
    shows "\<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> t = \<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<star> t"
      using assms by (cases t, simp_all)

    lemma HcompNml_term_Prim\<^sub>0 [simp]:
    assumes "Src t = Trg \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0"
    shows "t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = t"
      using assms by (cases t, simp_all)

    lemma HcompNml_Nml:
    assumes "Nml (t \<^bold>\<star> u)"
    shows "t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u = t \<^bold>\<star> u"
      using assms HcompNml_Prim by (metis Nml_HcompD(1) Nml_HcompD(5))

    lemma Nml_HcompNml:
    assumes "Nml t" and "Nml u" and "Src t = Trg u"
    shows "Nml (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
    and "Dom (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Dom t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u"
    and "Cod (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Cod t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u"
    and "Src (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Src u"
    and "Trg (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Trg t"
    proof -
      have 0: "\<And>u. \<lbrakk> Nml t; Nml u; Src t = Trg u \<rbrakk> \<Longrightarrow>
                     Nml (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<and> Dom (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Dom t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u \<and>
                                      Cod (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Cod t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u \<and>
                                      Src (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Src u \<and> Trg (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Trg t"
      proof (induct t, simp_all add: Nml_HcompD(1-4))
        fix \<nu> :: 'a and u :: "'a term"
        assume \<nu>: "arr \<nu>"
        assume u: "Nml u"
        assume 1: "\<^bold>\<langle>src \<nu>\<^bold>\<rangle>\<^sub>0 = Trg u"
        show "Nml (\<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<and> Dom (\<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = \<^bold>\<langle>dom \<nu>\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u \<and>
                                 Cod (\<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = \<^bold>\<langle>cod \<nu>\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u \<and>
                                 Src (\<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Src u \<and> Trg (\<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = \<^bold>\<langle>trg \<nu>\<^bold>\<rangle>\<^sub>0"
          using u \<nu> 1 by (cases u, simp_all)
        next
        fix u v w
        assume I1: "\<And>x. Nml x \<Longrightarrow> Src v = Trg x \<Longrightarrow>
                         Nml (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> x) \<and> Dom (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> x) = Dom v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom x \<and>
                                          Cod (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> x) = Cod v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod x \<and>
                                          Src (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> x) = Src x \<and> Trg (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> x) = Trg v"
        assume I2: "\<And>x. Nml x \<Longrightarrow> Trg u = Trg x \<Longrightarrow>
                         Nml (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> x) \<and> Dom (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> x) = Dom w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom x \<and>
                                          Cod (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> x) = Cod w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod x \<and>
                                          Src (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> x) = Src x \<and> Trg (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> x) = Trg w"
        assume vw: "Nml (v \<^bold>\<star> w)"
        assume u: "Nml u"
        assume wu: "Src w = Trg u"
        show "Nml ((v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<and>
              Dom ((v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = (Dom v \<^bold>\<star> Dom w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u \<and>
              Cod ((v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = (Cod v \<^bold>\<star> Cod w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u \<and>
              Src ((v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Src u \<and> Trg ((v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Trg v"
        proof -
          have v: "v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<and> Nml v"
            using vw Nml_implies_Arr Nml_HcompD by metis
          have w: "Nml w \<and> \<not> is_Prim\<^sub>0 w \<and> \<^bold>\<langle>src (un_Prim v)\<^bold>\<rangle>\<^sub>0 = Trg w"
            using vw by (simp add: Nml_HcompD)
          have "is_Prim\<^sub>0 u \<Longrightarrow> ?thesis" by (cases u; simp add: vw wu)
          moreover have "\<not> is_Prim\<^sub>0 u \<Longrightarrow> ?thesis"
          proof -
            assume 1: "\<not> is_Prim\<^sub>0 u"
            have "Src v = Trg (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
              using u v w I2 [of u] by (cases v, simp_all)
            hence "Nml (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<and>
                   Dom (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Dom v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<and>
                   Cod (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Cod v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<and>
                   Src (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Src u \<and> Trg (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Trg v"
              using u v w I1 [of "w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u"] I2 [of u] by argo
            moreover have "v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u = (v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u"
              using 1 by (cases u, simp_all)
            moreover have "(Dom v \<^bold>\<star> Dom w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u = Dom v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
              using v w u vw 1 I2 Nml_Dom HcompNml_Prim Nml_HcompD(1) Nml_HcompD(5)
              by (cases u, simp_all)
            moreover have "(Cod v \<^bold>\<star> Cod w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u = Cod v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
              using v w u vw 1 I2 Nml_HcompD(1) Nml_HcompD(5) HcompNml_Prim
              by (cases u, simp_all)
            ultimately show ?thesis
              by argo
          qed
          ultimately show ?thesis by blast
        qed
        next
        fix a u
        assume a: "obj a"
        assume u: "Nml u"
        assume au: "\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 = Trg u"
        show "Nml (Trg u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<and>
              Dom (Trg u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Dom (Trg u) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u \<and>
              Cod (Trg u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Cod (Trg u) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u \<and>
              Src (Trg u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Src u \<and> Trg (Trg u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Trg (Trg u)"
          using au
          by (metis Cod.simps(1) Dom.simps(1) HcompNml.simps(1) Trg.simps(1) u)
      qed
      show "Nml (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) " using assms 0 by blast
      show "Dom (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Dom t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u" using assms 0 by blast
      show "Cod (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Cod t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u" using assms 0 by blast
      show "Src (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Src u" using assms 0 by blast
      show "Trg (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Trg t" using assms 0 by blast
    qed

    lemma HcompNml_in_Hom [intro]:
    assumes "Nml t" and "Nml u" and "Src t = Trg u"
    shows "t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u \<in> HHom (Src u) (Trg t)"
    and "t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u \<in> VHom (Dom t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u) (Cod t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u)"
      using assms Nml_HcompNml Nml_implies_Arr by auto

    lemma Src_HcompNml:
    assumes "Nml t" and "Nml u" and "Src t = Trg u"
    shows "Src (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Src u"
      using assms Nml_HcompNml(4) by simp

    lemma Trg_HcompNml:
    assumes "Nml t" and "Nml u" and "Src t = Trg u"
    shows "Trg (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Trg t"
      using assms Nml_HcompNml(5) by simp

    lemma Dom_HcompNml:
    assumes "Nml t" and "Nml u" and "Src t = Trg u"
    shows "Dom (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Dom t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u"
      using assms Nml_HcompNml(2) by simp

    lemma Cod_HcompNml:
    assumes "Nml t" and "Nml u" and "Src t = Trg u"
    shows "Cod (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Cod t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u"
      using assms Nml_HcompNml(3) by simp

    lemma is_Hcomp_HcompNml:
    assumes "Nml t" and "Nml u" and "Src t = Trg u"
    and "\<not> is_Prim\<^sub>0 t" and "\<not> is_Prim\<^sub>0 u"
    shows "is_Hcomp (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
    proof -
      have "\<lbrakk> \<not> is_Hcomp (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u); Nml t; Nml u; Src t = Trg u; \<not> is_Prim\<^sub>0 t; \<not> is_Prim\<^sub>0 u \<rbrakk>
                \<Longrightarrow> False"
      proof (induct t, simp_all add: Nml_HcompD)
        fix a
        assume a: "obj a"
        assume u: "Nml u"
        assume 1: "\<not> is_Hcomp u"
        assume 2: "\<not> is_Prim\<^sub>0 (Trg u)"
        show "False"
          using u 1 2 by (cases u; simp)
        next
        fix v w
        assume I2: "\<not> is_Hcomp (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<Longrightarrow> False"
        assume vw: "Nml (v \<^bold>\<star> w)"
        assume u: "Nml u"
        assume 1: "\<not> is_Hcomp ((v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
        assume 2: "\<not> is_Prim\<^sub>0 u"
        assume 3: "Src w = Trg u"
        show "False"
        proof -
          have v: "v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle>"
            using vw Nml_HcompD by force
          have w: "Nml w \<and> \<not> is_Prim\<^sub>0 w \<and> \<^bold>\<langle>src (un_Prim v)\<^bold>\<rangle>\<^sub>0 = Trg w"
            using vw Nml_HcompD [of v w] by blast
          have "(v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u = v \<^bold>\<star> (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
          proof -
            have "(v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
              using u v 2 by (cases u, simp_all)
            also have "... = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<^bold>\<star> (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
              using u w I2 by fastforce
            also have "... = v \<^bold>\<star> (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
              using v by simp
            finally show ?thesis by simp
          qed
          thus ?thesis using 1 by simp
        qed
      qed
      thus ?thesis using assms by blast
    qed

    text \<open>
      The following function defines the ``dimension'' of a term,
      which is the number of inputs (or outputs) when the term is regarded as an
      interconnection matrix.
      For normal terms, this is just the length of the term when regarded as a list
      of arrows of @{term C}.
      This function is used as a ranking of terms in the subsequent associativity proof.
    \<close>

    primrec dim :: "'a term \<Rightarrow> nat"
    where "dim \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = 0"
        | "dim \<^bold>\<langle>\<mu>\<^bold>\<rangle> = 1"
        | "dim (t \<^bold>\<star> u) = (dim t + dim u)"
        | "dim (t \<^bold>\<cdot> u) = dim t"
        | "dim \<^bold>\<l>\<^bold>[t\<^bold>] = dim t"
        | "dim \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = dim t"
        | "dim \<^bold>\<r>\<^bold>[t\<^bold>] = dim t"
        | "dim \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] = dim t"
        | "dim \<^bold>\<a>\<^bold>[t, u, v\<^bold>] = dim t + dim u + dim v"
        | "dim \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] = dim t + dim u + dim v"

    lemma HcompNml_assoc:
    assumes "Nml t" and "Nml u" and "Nml v" and "Src t = Trg u" and "Src u = Trg v"
    shows "(t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v)"
    proof -
      have "\<And>n t u v. \<lbrakk> dim t = n; Nml t; Nml u; Nml v; Src t = Trg u; Src u = Trg v \<rbrakk> \<Longrightarrow>
                        (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v)"
      proof -
        fix n
        show "\<And>t u v. \<lbrakk> dim t = n; Nml t; Nml u; Nml v; Src t = Trg u; Src u = Trg v \<rbrakk> \<Longrightarrow>
                        (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v)"
        proof (induction n rule: nat_less_induct)
          fix n :: nat and t :: "'a term" and u v
          assume I: "\<forall>m<n. \<forall>t u v. dim t = m \<longrightarrow> Nml t \<longrightarrow> Nml u \<longrightarrow> Nml v \<longrightarrow>
                                   Src t = Trg u \<longrightarrow> Src u = Trg v \<longrightarrow>
                                   (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v)"
          assume dim: "dim t = n"
          assume t: "Nml t"
          assume u: "Nml u"
          assume v: "Nml v"
          assume tu: "Src t = Trg u"
          assume uv: "Src u = Trg v"
          show "(t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v)"
          proof -
            have "is_Prim\<^sub>0 t \<Longrightarrow> ?thesis" by (cases t; simp)
            moreover have "\<not>is_Prim\<^sub>0 t \<Longrightarrow> is_Prim\<^sub>0 u \<Longrightarrow> ?thesis"
              by (cases t; simp; cases u; simp)
            moreover have "\<not> is_Prim\<^sub>0 t \<Longrightarrow> \<not> is_Prim\<^sub>0 u \<Longrightarrow> is_Prim\<^sub>0 v \<Longrightarrow> ?thesis"
            proof -
              assume 1: "\<not> is_Prim\<^sub>0 t"
              assume 2: "\<not> is_Prim\<^sub>0 u"
              assume 3: "is_Prim\<^sub>0 v"
              have "\<not>is_Prim\<^sub>0 (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
                using 1 2 t u tu is_Hcomp_HcompNml [of t u]
                by (cases t, simp, cases u, auto)
              thus ?thesis
                using 1 2 3 tu uv by (cases v, simp, cases "t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u", simp_all)
            qed
            moreover have "\<not>is_Prim\<^sub>0 t \<and> \<not> is_Prim\<^sub>0 u \<and> \<not> is_Prim\<^sub>0 v \<and> is_Prim t \<Longrightarrow> ?thesis"
              using v by (cases t, simp_all, cases u, simp_all; cases v, simp_all)
            moreover have "\<not>is_Prim\<^sub>0 t \<and> \<not> is_Prim\<^sub>0 u \<and> \<not> is_Prim\<^sub>0 v \<and> is_Hcomp t \<Longrightarrow> ?thesis"
            proof (cases t, simp_all)
              fix w :: "'a term" and x :: "'a term"
              assume 1: " \<not> is_Prim\<^sub>0 u \<and> \<not> is_Prim\<^sub>0 v"
              assume 2: "t = (w \<^bold>\<star> x)"
              show "((w \<^bold>\<star> x) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v = (w \<^bold>\<star> x) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v)"
              proof -
                have w: "w = \<^bold>\<langle>un_Prim w\<^bold>\<rangle>"
                  using t 1 2 Nml_HcompD by auto
                have x: "Nml x"
                  using t w 1 2 by (metis Nml.simps(3))
                have "((w \<^bold>\<star> x) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v = (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (x \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v"
                  using u v w x 1 2 by (cases u, simp_all)
                also have "... = (w \<^bold>\<star> (x \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v"
                  using t w u 1 2 HcompNml_Prim is_Hcomp_HcompNml Nml_HcompD
                  by (metis Src.simps(3) term.distinct_disc(3) tu)
                also have "... = w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> ((x \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v)"
                  using u v w x 1 by (cases u, simp_all; cases v, simp_all)
                also have "... = w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (x \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v))"
                proof -
                  have "dim x < dim t"
                    using 2 w by (cases w; simp)
                  moreover have "Src x = Trg u \<and> Src u = Trg v"
                    using tu uv 2 by auto
                  ultimately show ?thesis 
                    using u v x dim I by simp
                qed
                also have "... = (w \<^bold>\<star> x) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v)"
                proof -
                  have 3: "is_Hcomp (u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v)"
                    using u v uv 1 is_Hcomp_HcompNml by auto
                  obtain u' :: "'a term" and v' where uv': "u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v = u' \<^bold>\<star> v'"
                    using 3 is_Hcomp_def by blast
                  thus ?thesis by simp
                qed
                finally show ?thesis by simp
              qed
            qed
            moreover have "is_Prim\<^sub>0 t \<or> is_Prim t \<or> is_Hcomp t"
              using t by (cases t, simp_all)
            ultimately show ?thesis by blast
          qed
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma HcompNml_Trg_Nml:
    assumes "Nml t"
    shows "Trg t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> t = t"
    proof -
      have "Nml t \<Longrightarrow> Trg t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> t = t"
      proof (induct t, simp_all add: Nml_HcompD)
        fix u v
        assume uv: "Nml (u \<^bold>\<star> v)"
        assume I1: "Trg u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u = u"
        have 1: "Nml u \<and> Nml v \<and> Src u = Trg v"
          using uv Nml_HcompD by blast
        have 2: "Trg (u \<^bold>\<star> v) = Trg u"
          using uv by auto
        show "Trg u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u \<^bold>\<star> v = u \<^bold>\<star> v"
        proof -
          have "Trg u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u \<^bold>\<star> v = Trg u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v"
            using uv HcompNml_Nml by simp
          also have "... = (Trg u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v"
            using 1 2 HcompNml_assoc Src_Trg Nml_Trg Nml_implies_Arr by simp
          also have "... = u \<^bold>\<star> v"
            using I1 uv HcompNml_Nml by simp
          finally show ?thesis by simp
        qed
      qed
      thus ?thesis using assms by simp
    qed

    lemma HcompNml_Nml_Src:
    assumes "Nml t"
    shows "t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Src t = t"
    proof -
      have "Nml t \<Longrightarrow> t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Src t = t"
      proof (induct t, simp_all add: Nml_HcompD)
        fix u v
        assume uv: "Nml (u \<^bold>\<star> v)"
        assume I2: "v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Src v = v"
        have 1: "Nml u \<and> Nml v \<and> Src u = Trg v"
          using uv Nml_HcompD by blast
        have 2: "Src (u \<^bold>\<star> v) = Src v"
          using uv Trg_HcompNml by auto
        show "(u \<^bold>\<star> v) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Src v = u \<^bold>\<star> v"
        proof -
          have "(u \<^bold>\<star> v) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Src v = (u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Src v"
            using uv HcompNml_Nml by simp
          also have "... = u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Src v)"
            using 1 2 HcompNml_assoc Trg_Src Nml_Src Nml_implies_Arr by simp
          also have "... = u \<^bold>\<star> v"
            using I2 uv HcompNml_Nml by simp
          finally show ?thesis by simp
        qed
      qed
      thus ?thesis using assms by simp
    qed

    lemma HcompNml_Obj_Nml:
    assumes "Obj t" and "Nml u" and "Src t = Trg u"
    shows "t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u = u"
      using assms by (cases t, simp_all add: HcompNml_Trg_Nml)

    lemma HcompNml_Nml_Obj:
    assumes "Nml t" and "Obj u" and "Src t = Trg u"
    shows "t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u = t"
      using assms by (cases u, simp_all)

    lemma Ide_HcompNml:
    assumes "Ide t" and "Ide u" and "Nml t" and "Nml u" and "Src t = Trg u"
    shows "Ide (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
      using assms
      by (metis (mono_tags, lifting) Nml_HcompNml(1) Nml_implies_Arr Dom_HcompNml
          Ide_Dom Ide_in_Hom(2) mem_Collect_eq)

    lemma Can_HcompNml:
    assumes "Can t" and "Can u" and "Nml t" and "Nml u" and "Src t = Trg u"
    shows "Can (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
    proof -
      have "\<And>u. \<lbrakk> Can t \<and> Nml t; Can u \<and> Nml u; Src t = Trg u \<rbrakk> \<Longrightarrow> Can (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
      proof (induct t, simp_all add: HcompNml_Trg_Nml HcompNml_Nml_Src)
        show "\<And>x u. ide x \<and> arr x \<Longrightarrow> Can u \<and> Nml u \<Longrightarrow> \<^bold>\<langle>src x\<^bold>\<rangle>\<^sub>0 = Trg u \<Longrightarrow> Can (\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
          by (metis Ide.simps(1-2) Ide_implies_Can Can.simps(3) Nml.elims(2)
              Nml.simps(2) HcompNml.simps(12) HcompNml_Prim Ide_HcompNml
              Src.simps(2) term.disc(2))
        show "\<And>v w u.
                 (\<And>u. Nml v \<Longrightarrow> Can u \<and> Nml u \<Longrightarrow> Trg w = Trg u \<Longrightarrow> Can (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)) \<Longrightarrow>
                 (\<And>ua. Nml w \<Longrightarrow> Can ua \<and> Nml ua \<Longrightarrow> Trg u = Trg ua \<Longrightarrow> Can (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> ua)) \<Longrightarrow>
                 Can v \<and> Can w \<and> Src v = Trg w \<and> Nml (v \<^bold>\<star> w) \<Longrightarrow>
                 Can u \<and> Nml u \<Longrightarrow> Src w = Trg u \<Longrightarrow> Can ((v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
          by (metis Nml_HcompD(3-4) HcompNml_Nml Nml_HcompNml(1)
              HcompNml_assoc Trg_HcompNml)
      qed
      thus ?thesis using assms by blast
    qed

    lemma Inv_HcompNml:
    assumes "Can t" and "Can u" and "Nml t" and "Nml u" and "Src t = Trg u"
    shows "Inv (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Inv t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv u"
    proof -
      have "\<And>u. \<lbrakk> Can t \<and> Nml t; Can u \<and> Nml u; Src t = Trg u \<rbrakk>
                   \<Longrightarrow> Inv (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Inv t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv u"
      proof (induct t, simp_all add: HcompNml_Trg_Nml HcompNml_Nml_Src)
        show "\<And>x u. \<lbrakk> obj x; Can u \<and> Nml u; \<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0 = Trg u \<rbrakk> \<Longrightarrow> Inv u = Inv (Trg u) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv u"
          by (metis HcompNml.simps(1) Inv.simps(1))
        show "\<And>x u. ide x \<and> arr x \<Longrightarrow> Can u \<and> Nml u \<Longrightarrow> \<^bold>\<langle>src x\<^bold>\<rangle>\<^sub>0 = Trg u \<Longrightarrow>  
                    Inv (\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = \<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv u"
          by (metis Ide.simps(2) HcompNml.simps(2) HcompNml_Prim Inv.simps(1,3)
                    Inv_Ide Inv_Inv is_Prim\<^sub>0_def)
        fix v w u
        assume I1: "\<And>x. Nml v \<Longrightarrow> Can x \<and> Nml x \<Longrightarrow> Trg w = Trg x \<Longrightarrow>
                        Inv (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> x) = Inv v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv x"
        assume I2: "\<And>x. Nml w \<Longrightarrow> Can x \<and> Nml x \<Longrightarrow> Trg u = Trg x \<Longrightarrow>
                              Inv (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> x) = Inv w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv x"
        assume vw: "Can v \<and> Can w \<and> Src v = Trg w \<and> Nml (v \<^bold>\<star> w)"
        assume wu: "Src w = Trg u"
        assume u: "Can u \<and> Nml u"
        have v: "Can v \<and> Nml v"
          using vw Nml_HcompD by blast
        have w: "Can w \<and> Nml w"
          using v vw by (cases v, simp_all)
        show "Inv ((v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = (Inv v \<^bold>\<star> Inv w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv u"
        proof -
          have "is_Prim\<^sub>0 u \<Longrightarrow> ?thesis"
            apply (cases u) by simp_all
          moreover have "\<not> is_Prim\<^sub>0 u \<Longrightarrow> ?thesis"
          proof -
            assume 1: "\<not> is_Prim\<^sub>0 u"
            have "Inv ((v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) = Inv (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u))"
              using 1 by (cases u, simp_all)
            also have "... = Inv v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv (w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
              using u v w vw wu I1 Nml_HcompNml Can_HcompNml Nml_Inv Can_Inv
              by simp
            also have "... = Inv v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (Inv w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv u)"
              using u v w I2 Nml_HcompNml by simp
            also have "... = (Inv v \<^bold>\<star> Inv w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv u"
              using v 1 by (cases u, simp_all)
            finally show ?thesis by blast
          qed
          ultimately show ?thesis by blast
        qed
      qed
      thus ?thesis using assms by blast
    qed

    text \<open>
       The following function defines vertical composition for compatible normal terms,
       by ``pushing the composition down'' to arrows of @{text V}.
    \<close>

    fun VcompNml :: "'a term \<Rightarrow> 'a term \<Rightarrow> 'a term"  (infixr "\<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor>" 55)
    where "\<^bold>\<langle>\<nu>\<^bold>\<rangle>\<^sub>0 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u = u"
        | "\<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<langle>\<mu>\<^bold>\<rangle> = \<^bold>\<langle>\<nu> \<cdot> \<mu>\<^bold>\<rangle>"
        | "(u \<^bold>\<star> v) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (w \<^bold>\<star> x) = (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w \<^bold>\<star> v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x)"
        | "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = t"
        | "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> _ = undefined \<^bold>\<cdot> undefined"

    text \<open>
      Note that the last clause above is not relevant to normal terms.
      We have chosen a provably non-normal value in order to validate associativity.
    \<close>

    lemma Nml_VcompNml:
    assumes "Nml t" and "Nml u" and "Dom t = Cod u"
    shows "Nml (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)"
    and "Dom (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u"
    and "Cod (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod t"
    proof -
      have 0: "\<And>u. \<lbrakk> Nml t; Nml u; Dom t = Cod u \<rbrakk> \<Longrightarrow>
                     Nml (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<and> Dom (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u \<and> Cod (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod t"
      proof (induct t, simp_all add: Nml_HcompD)
        show "\<And>x u. obj x \<Longrightarrow> Nml u \<Longrightarrow> \<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0 = Cod u \<Longrightarrow>
                     Nml (Cod u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<and> Dom (Cod u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u \<and>
                     Cod (Cod u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod (Cod u)"
          by (metis Cod.simps(1) VcompNml.simps(1))
        fix \<nu> u
        assume \<nu>: "arr \<nu>"
        assume u: "Nml u"
        assume 1: "\<^bold>\<langle>dom \<nu>\<^bold>\<rangle> = Cod u"
        show "Nml (\<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<and> Dom (\<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u \<and> Cod (\<^bold>\<langle>\<nu>\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = \<^bold>\<langle>cod \<nu>\<^bold>\<rangle>"
          using \<nu> u 1 by (cases u, simp_all)
        next
        fix u v w
        assume I2: "\<And>u. \<lbrakk> Nml u; Dom w = Cod u \<rbrakk> \<Longrightarrow>
                          Nml (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<and> Dom (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u \<and> Cod (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod w"
        assume vw: "Nml (v \<^bold>\<star> w)"
        have v: "Nml v"
          using vw Nml_HcompD by force
        have w: "Nml w"
          using vw Nml_HcompD by force
        assume u: "Nml u"
        assume 1: "(Dom v \<^bold>\<star> Dom w) = Cod u"
        show "Nml ((v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<and> Dom ((v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u \<and>
                                     Cod ((v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod v \<^bold>\<star> Cod w"
          using u v w 1
        proof (cases u, simp_all)
          fix x y
          assume 2: "u = x \<^bold>\<star> y"
          have 4: "is_Prim x \<and> x = \<^bold>\<langle>un_Prim x\<^bold>\<rangle> \<and> arr (un_Prim x) \<and> Nml y \<and> \<not> is_Prim\<^sub>0 y"
            using u 2 by (cases x, cases y, simp_all)
          have 5: "is_Prim v \<and> v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<and> arr (un_Prim v) \<and> Nml w \<and> \<not> is_Prim\<^sub>0 w"
            using v w vw by (cases v, simp_all)
          have 6: "dom (un_Prim v) = cod (un_Prim x) \<and> Dom w = Cod y"
          proof -
            have "\<^bold>\<langle>src (un_Prim v)\<^bold>\<rangle>\<^sub>0 = Trg w" using vw Nml_HcompD [of v w] by simp
            thus "dom (un_Prim v) = cod (un_Prim x) \<and> Dom w = Cod y"
              using 1 2 4 5 apply (cases u, simp_all)
              by (metis Cod.simps(2) Dom.simps(2) term.simps(2))
          qed
          have "(v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u = \<^bold>\<langle>un_Prim v \<cdot> un_Prim x\<^bold>\<rangle> \<^bold>\<star> w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y"
            using 2 4 5 6 VcompNml.simps(2) [of "un_Prim v" "un_Prim x"] by simp
          moreover have "Nml (\<^bold>\<langle>un_Prim v \<cdot> un_Prim x\<^bold>\<rangle> \<^bold>\<star> w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y)"
          proof -
            have "Nml (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y)"
              using I2 4 5 6 by simp
            moreover have "\<not> is_Prim\<^sub>0 (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y)"
              using vw 4 5 6 I2 Nml_Cod Nml_HcompD(5) is_Prim\<^sub>0_def
              by (metis Cod.simps(1) Cod.simps(3))
            moreover have "\<^bold>\<langle>src (un_Prim v \<cdot> un_Prim x)\<^bold>\<rangle>\<^sub>0 = Trg (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y)"
              using vw 4 5 6 I2 Nml_HcompD(6) Nml_implies_Arr
                    src.is_natural_1 src.preserves_comp_2 Trg_Cod src_cod
              by (metis seqI)
            ultimately show ?thesis
              using 4 5 6 Nml.simps(3) [of "un_Prim v \<cdot> un_Prim x" "(w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y)"]
              by simp
          qed
          ultimately show "Nml (v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x \<^bold>\<star> w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y) \<and>
                           Dom (v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x) = Dom x \<and> Dom (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y) = Dom y \<and>
                           Cod (v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x) = Cod v \<and> Cod (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y) = Cod w"
            using 4 5 6 I2
            by (metis (no_types, lifting) Cod.simps(2) Dom.simps(2) VcompNml.simps(2)
                cod_comp dom_comp seqI)
        qed
      qed
      show "Nml (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)" using assms 0 by blast
      show "Dom (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u" using assms 0 by blast
      show "Cod (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod t" using assms 0 by blast
    qed

    lemma VcompNml_in_Hom [intro]:
    assumes "Nml t" and "Nml u" and "Dom t = Cod u"
    shows "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u \<in> HHom (Src u) (Trg u)" and "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u \<in> VHom (Dom u) (Cod t)"
    proof -
      show 1: "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u \<in> VHom (Dom u) (Cod t)"
        using assms Nml_VcompNml Nml_implies_Arr by simp
      show "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u \<in> HHom (Src u) (Trg u)"
        using assms 1 Src_Dom Trg_Dom Nml_implies_Arr by fastforce
    qed

    lemma Src_VcompNml:
    assumes "Nml t" and "Nml u" and "Dom t = Cod u"
    shows "Src (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Src u"
      using assms VcompNml_in_Hom by simp

    lemma Trg_VcompNml:
    assumes "Nml t" and "Nml u" and "Dom t = Cod u"
    shows "Trg (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Trg u"
      using assms VcompNml_in_Hom by simp

    lemma Dom_VcompNml:
    assumes "Nml t" and "Nml u" and "Dom t = Cod u"
    shows "Dom (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Dom u"
      using assms Nml_VcompNml(2) by simp

    lemma Cod_VcompNml:
    assumes "Nml t" and "Nml u" and "Dom t = Cod u"
    shows "Cod (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Cod t"
      using assms Nml_VcompNml(3) by simp

    lemma VcompNml_Cod_Nml [simp]:
    assumes "Nml t"
    shows "VcompNml (Cod t) t = t"
    proof -
      have "Nml t \<Longrightarrow> Cod t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> t = t"
        apply (induct t)
        by (auto simp add: Nml_HcompD comp_cod_arr)
      thus ?thesis using assms by blast
    qed

    lemma VcompNml_Nml_Dom [simp]:
    assumes "Nml t"
    shows "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (Dom t) = t"
    proof -
      have "Nml t \<Longrightarrow> t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Dom t = t"
        apply (induct t) by (auto simp add: Nml_HcompD comp_arr_dom)
      thus ?thesis using assms by blast
    qed

    lemma VcompNml_Ide_Nml [simp]:
    assumes "Nml t" and "Ide a" and "Dom a = Cod t"
    shows "a \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> t = t"
      using assms Ide_in_Hom by simp

    lemma VcompNml_Nml_Ide [simp]:
    assumes "Nml t" and "Ide a" and "Dom t = Cod a"
    shows "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> a = t"
      using assms Ide_in_Hom by auto

    lemma VcompNml_assoc:
    assumes "Nml t" and "Nml u" and "Nml v"
    and "Dom t = Cod u" and "Dom u = Cod v"
    shows "(t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
    proof -
      have "\<And>u v. \<lbrakk> Nml t; Nml u; Nml v; Dom t = Cod u; Dom u = Cod v \<rbrakk> \<Longrightarrow>
                    (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
      proof (induct t, simp_all)
        show "\<And>x u v. obj x \<Longrightarrow> Nml u \<Longrightarrow> Nml v \<Longrightarrow> \<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0 = Cod u \<Longrightarrow> Dom u = Cod v \<Longrightarrow>
                       u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = Cod u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v"
          by (metis VcompNml.simps(1))
        fix f u v
        assume f: "arr f"
        assume u: "Nml u"
        assume v: "Nml v"
        assume 1: "\<^bold>\<langle>dom f\<^bold>\<rangle> = Cod u"
        assume 2: "Dom u = Cod v"
        show "(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
          using u v f 1 2 comp_assoc
          apply (cases u)
                   apply simp_all
          apply (cases v)
          by simp_all
        next
        fix u v w x
        assume I1: "\<And>u v. \<lbrakk> Nml w; Nml u; Nml v; Dom w = Cod u; Dom u = Cod v \<rbrakk> \<Longrightarrow>
                            (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        assume I2: "\<And>u v. \<lbrakk> Nml x; Nml u; Nml v; Dom x = Cod u; Dom u = Cod v \<rbrakk> \<Longrightarrow>
                            (x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        assume wx: "Nml (w \<^bold>\<star> x)"
        assume u: "Nml u"
        assume v: "Nml v"
        assume 1: "(Dom w \<^bold>\<star> Dom x) = Cod u"
        assume 2: "Dom u = Cod v"
        show "((w \<^bold>\<star> x) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v = (w \<^bold>\<star> x) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v"
        proof -
          have w: "Nml w"
            using wx Nml_HcompD by blast
          have x: "Nml x"
            using wx Nml_HcompD by blast
          have "is_Hcomp u"
            using u 1 by (cases u) simp_all
          thus ?thesis
            using u v apply (cases u, simp_all, cases v, simp_all)
          proof -
            fix u1 u2 v1 v2
            assume 3: "u = (u1 \<^bold>\<star> u2)"
            assume 4: "v = (v1 \<^bold>\<star> v2)"
            show "(w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u1) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1 = w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1 \<and>
                  (x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u2) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2 = x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2"
            proof -
              have "Nml u1 \<and> Nml u2"
                using u 3 Nml_HcompD by blast
              moreover have "Nml v1 \<and> Nml v2"
                using v 4 Nml_HcompD by blast
              ultimately show ?thesis using w x I1 I2 1 2 3 4 by simp
            qed
          qed
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma Ide_VcompNml:
    assumes "Ide t" and "Ide u" and "Nml t" and "Nml u" and "Dom t = Cod u"
    shows "Ide (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)"
    proof -
      have "\<And>u. \<lbrakk> Ide t; Ide u; Nml t; Nml u; Dom t = Cod u \<rbrakk> \<Longrightarrow> Ide (VcompNml t u)"
        by (induct t, simp_all)
      thus ?thesis using assms by blast
    qed

    lemma Can_VcompNml:
    assumes "Can t" and "Can u" and "Nml t" and "Nml u" and "Dom t = Cod u"
    shows "Can (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)"
    proof -
      have "\<And>u. \<lbrakk> Can t \<and> Nml t; Can u \<and> Nml u; Dom t = Cod u \<rbrakk> \<Longrightarrow> Can (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u)"
      proof (induct t, simp_all)
        fix t u v
        assume I1: "\<And>v. \<lbrakk> Nml t; Can v \<and> Nml v; Dom t = Cod v \<rbrakk> \<Longrightarrow> Can (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        assume I2: "\<And>v. \<lbrakk> Nml u; Can v \<and> Nml v; Dom u = Cod v \<rbrakk> \<Longrightarrow> Can (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        assume tu: "Can t \<and> Can u \<and> Src t = Trg u \<and> Nml (t \<^bold>\<star> u)"
        have t: "Can t \<and> Nml t"
          using tu Nml_HcompD by blast
        have u: "Can u \<and> Nml u"
          using tu Nml_HcompD by blast
        assume v: "Can v \<and> Nml v"
        assume 1: "(Dom t \<^bold>\<star> Dom u) = Cod v"
        show "Can ((t \<^bold>\<star> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v)"
        proof -
          have 2: "(Dom t \<^bold>\<star> Dom u) = Cod v" using 1 by simp
          show ?thesis
            using v 2
          proof (cases v; simp)
            fix w x
            assume wx: "v = (w \<^bold>\<star> x)"
            have "Can w \<and> Nml w" using v wx Nml_HcompD Can.simps(3) by blast
            moreover have "Can x \<and> Nml x" using v wx Nml_HcompD Can.simps(3) by blast
            moreover have "Dom t = Cod w" using 2 wx by simp
            moreover have ux: "Dom u = Cod x" using 2 wx by simp
            ultimately show "Can (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w) \<and> Can (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x) \<and> Src (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w) = Trg (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x)"
              using t u v tu wx I1 I2
              by (metis Nml_HcompD(7) Src_VcompNml Trg_VcompNml)
          qed
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma Inv_VcompNml:
    assumes "Can t" and "Can u" and "Nml t" and "Nml u" and "Dom t = Cod u"
    shows "Inv (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv t"
    proof -
      have "\<And>u. \<lbrakk> Can t \<and> Nml t; Can u \<and> Nml u; Dom t = Cod u \<rbrakk> \<Longrightarrow>
              Inv (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv t"
      proof (induct t, simp_all)
        show "\<And>x u. \<lbrakk> obj x; Can u \<and> Nml u; \<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0 = Cod u \<rbrakk> \<Longrightarrow> Inv u = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv (Cod u)"
          by (simp add: Can_implies_Arr)
        show "\<And>x u. \<lbrakk> ide x \<and> arr x; Can u \<and> Nml u; \<^bold>\<langle>x\<^bold>\<rangle> = Cod u \<rbrakk> \<Longrightarrow>
                      Inv u = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv (Cod u)"
          by (simp add: Can_implies_Arr)
        fix v w u
        assume vw: "Can v \<and> Can w \<and> Src v = Trg w \<and> Nml (v \<^bold>\<star> w)"
        have v: "Can v \<and> Nml w"
          using vw Nml_HcompD by blast
        have w: "Can w \<and> Nml w"
          using vw Nml_HcompD by blast
        assume I1: "\<And>x. \<lbrakk> Nml v; Can x \<and> Nml x; Dom v = Cod x \<rbrakk> \<Longrightarrow>
                          Inv (v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x) = Inv x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv v"
        assume I2: "\<And>x. \<lbrakk> Nml w; Can x \<and> Nml x; Dom w = Cod x \<rbrakk> \<Longrightarrow>
                          Inv (w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x) = Inv x \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv w"
        assume u: "Can u \<and> Nml u"
        assume 1: "(Dom v \<^bold>\<star> Dom w) = Cod u"
        show "Inv ((v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (Inv v \<^bold>\<star> Inv w)"
          using v 1
        proof (cases w, simp_all)
          show "\<And>\<mu>. obj \<mu> \<Longrightarrow> Dom v \<^bold>\<star> \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 = Cod u \<Longrightarrow> w = \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0 \<Longrightarrow> Can v \<Longrightarrow>
                     Inv ((v \<^bold>\<star> \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (Inv v \<^bold>\<star> \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0)"
            using Nml_HcompD(5) is_Prim\<^sub>0_def vw by blast
          show "\<And>\<mu>. arr \<mu> \<Longrightarrow> Dom v \<^bold>\<star> \<^bold>\<langle>dom \<mu>\<^bold>\<rangle> = Cod u \<Longrightarrow> w = \<^bold>\<langle>\<mu>\<^bold>\<rangle> \<Longrightarrow> Can v \<Longrightarrow>
                     Inv ((v \<^bold>\<star> \<^bold>\<langle>\<mu>\<^bold>\<rangle>) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (Inv v \<^bold>\<star> \<^bold>\<langle>inv \<mu>\<^bold>\<rangle>)"
            by (metis Ide.simps(2) Can.simps(2) Nml_HcompD(1) Dom.simps(2) Inv_Ide
                      Dom_Inv Nml_Inv ideD(2) inv_ide VcompNml_Cod_Nml VcompNml_Nml_Dom
                      u vw)
          show "\<And>y z. Nml (y \<^bold>\<star> z) \<Longrightarrow> Dom v \<^bold>\<star> Dom y \<^bold>\<star> Dom z = Cod u \<Longrightarrow>
                           w = y \<^bold>\<star> z \<Longrightarrow> Can v \<Longrightarrow>
                          Inv ((v \<^bold>\<star> y \<^bold>\<star> z) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (Inv v \<^bold>\<star> Inv y \<^bold>\<star> Inv z)"
          proof -
            fix y z
            assume 2: "Nml (y \<^bold>\<star> z)"
            assume yz: "w = y \<^bold>\<star> z"
            show "Inv ((v \<^bold>\<star> y \<^bold>\<star> z) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u) = Inv u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (Inv v \<^bold>\<star> Inv y \<^bold>\<star> Inv z)"
              using u vw yz I1 I2 1 2 VcompNml_Nml_Ide
              apply (cases u)
                       apply simp_all
              by (metis Nml_HcompD(3-4))
          qed
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma Can_and_Nml_implies_Ide:
    assumes "Can t" and "Nml t"
    shows "Ide t"
    proof -
      have "\<lbrakk> Can t; Nml t \<rbrakk> \<Longrightarrow> Ide t"
        apply (induct t) by (simp_all add: Nml_HcompD)
      thus ?thesis using assms by blast
    qed

    lemma VcompNml_Can_Inv [simp]:
    assumes "Can t" and "Nml t"
    shows "t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv t = Cod t"
      using assms Can_and_Nml_implies_Ide Ide_in_Hom by simp
      
    lemma VcompNml_Inv_Can [simp]:
    assumes "Can t" and "Nml t"
    shows "Inv t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> t = Dom t"
      using assms Can_and_Nml_implies_Ide Ide_in_Hom by simp

    text \<open>
      The next fact is a syntactic version of the interchange law, for normal terms.
    \<close>

    lemma VcompNml_HcompNml:
    assumes "Nml t" and "Nml u" and "Nml v" and "Nml w"
    and "VSeq t v" and "VSeq u w" and "Src v = Trg w"
    shows "(t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w) = (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
    proof -
      have "\<And>u v w. \<lbrakk> Nml t; Nml u; Nml v; Nml w; VSeq t v; VSeq u w;
                      Src t = Trg u; Src v = Trg w \<rbrakk> \<Longrightarrow>
                      (t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w) = (t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
      proof (induct t, simp_all)
        fix u v w x
        assume u: "Nml u"
        assume v: "Nml v"
        assume w: "Nml w"
        assume uw: "VSeq u w"
        show "\<And>x. Arr v \<and> \<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0 = Cod v \<Longrightarrow> (Cod v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w) = v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w"
          using u v w uw by (cases v) simp_all
        show "\<And>x. \<lbrakk> arr x; Arr v \<and> \<^bold>\<langle>dom x\<^bold>\<rangle> = Cod v; \<^bold>\<langle>src x\<^bold>\<rangle>\<^sub>0 = Trg u; Src v = Trg w \<rbrakk> \<Longrightarrow>
                  (\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w) = \<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w"
        proof -
          fix x
          assume x: "arr x"
          assume 1: "Arr v \<and> \<^bold>\<langle>dom x\<^bold>\<rangle> = Cod v"
          assume tu: "\<^bold>\<langle>src x\<^bold>\<rangle>\<^sub>0 = Trg u"
          assume vw: "Src v = Trg w"
          show "(\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w) = \<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w"
          proof -
            have 2: "v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<and> arr (un_Prim v)" using v 1 by (cases v) simp_all
            have "is_Prim\<^sub>0 u \<Longrightarrow> ?thesis"
              using u v w x tu uw vw 1 2 Cod.simps(3) VcompNml_Cod_Nml Dom.simps(2)
                    HcompNml_Prim HcompNml_term_Prim\<^sub>0 Nml_HcompNml(3) HcompNml_Trg_Nml
              apply (cases u, simp_all)
              by (cases w, simp_all add: Src_VcompNml)
            moreover have "\<not> is_Prim\<^sub>0 u \<Longrightarrow> ?thesis"
            proof -
              assume 3: "\<not> is_Prim\<^sub>0 u"
              hence 4: "\<not> is_Prim\<^sub>0 w" using u w uw by (cases u, simp_all; cases w, simp_all)
              have "(\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w) = (\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<star> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<star> w)"
              proof -
                have "\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u = \<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<star> u"
                  using u x 3 HcompNml_Nml by (cases u, simp_all)
                moreover have "v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w = v \<^bold>\<star> w"
                  using w 2 4 HcompNml_Nml by (cases v, simp_all; cases w, simp_all)
                ultimately show ?thesis by simp
              qed
              also have 5: "... = (\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<star> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)" by simp
              also have "... = (\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
                using x u w uw vw 1 2 3 4 5
                      HcompNml_Nml HcompNml_Prim Nml_HcompNml(1)
                by (metis Cod.simps(3) Nml.simps(3) Dom.simps(2) Dom.simps(3)
                    Nml_VcompNml(1) tu v)
              finally show ?thesis by blast
            qed
            ultimately show ?thesis by blast
          qed
        qed
        fix t1 t2
        assume t12: "Nml (t1 \<^bold>\<star> t2)"
        assume I1: "\<And>u v w. \<lbrakk> Nml t1; Nml u; Nml v; Nml w;
                              Arr v \<and> Dom t1 = Cod v; VSeq u w;
                              Trg t2 = Trg u; Src v = Trg w \<rbrakk> \<Longrightarrow>
                              (t1 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w) = t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w"
        assume I2: "\<And>u' v w. \<lbrakk> Nml t2; Nml u'; Nml v; Nml w;
                               Arr v \<and> Dom t2 = Cod v; VSeq u' w;
                               Trg u = Trg u'; Src v = Trg w \<rbrakk> \<Longrightarrow>
                              (t2 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u') \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w) = (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u' \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
        have t1: "t1 = \<^bold>\<langle>un_Prim t1\<^bold>\<rangle> \<and> arr (un_Prim t1) \<and> Nml t1"
          using t12 by (cases t1, simp_all)
        have t2: "Nml t2 \<and> \<not>is_Prim\<^sub>0 t2"
          using t12 by (cases t1, simp_all)
        assume vw: "Src v = Trg w"
        assume tu: "Src t2 = Trg u"
        assume 1: "Arr t1 \<and> Arr t2 \<and> Src t1 = Trg t2 \<and> Arr v \<and> (Dom t1 \<^bold>\<star> Dom t2) = Cod v"
        show "((t1 \<^bold>\<star> t2) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w) = (t1 \<^bold>\<star> t2) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w"
        proof -
          have "is_Prim\<^sub>0 u \<Longrightarrow> ?thesis"
            using u v w uw tu vw t12 I1 I2 1 Obj_Src
            apply (cases u, simp_all)
            by (cases w, simp_all add: Src_VcompNml)
          moreover have "\<not> is_Prim\<^sub>0 u \<Longrightarrow> ?thesis"
          proof -
            assume u': "\<not> is_Prim\<^sub>0 u"
            hence w': "\<not> is_Prim\<^sub>0 w" using u w uw by (cases u, simp_all; cases w, simp_all)
            show ?thesis
              using 1 v
            proof (cases v, simp_all)
              fix v1 v2
              assume v12: "v = v1 \<^bold>\<star> v2"
              have v1: "v1 =  \<^bold>\<langle>un_Prim v1\<^bold>\<rangle> \<and> arr (un_Prim v1) \<and> Nml v1"
                using v v12 by (cases v1, simp_all)
              have v2: "Nml v2 \<and> \<not> is_Prim\<^sub>0 v2"
                using v v12 by (cases v1, simp_all)
              have 2: "v = (\<^bold>\<langle>un_Prim v1\<^bold>\<rangle> \<^bold>\<star> v2)"
                using v1 v12 by simp
              show "((t1 \<^bold>\<star> t2) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> ((v1 \<^bold>\<star> v2) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w) = (t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1 \<^bold>\<star> t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w"
              proof -
                have 3: "(t1 \<^bold>\<star> t2) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u = t1 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (t2 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
                  using u u' by (cases u, simp_all)
                have 4: "v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w = v1 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v2 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w"
                proof -
                  have "Src v1 = Trg v2"
                    using v v12 1 Arr.simps(3) Nml_HcompD(7) by blast
                  moreover have "Src v2 = Trg w"
                    using v v12 vw by simp
                  ultimately show ?thesis
                    using v w v1 v2 v12 2 HcompNml_assoc [of v1 v2 w] HcompNml_Nml by metis
                qed
                have "((t1 \<^bold>\<star> t2) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> ((v1 \<^bold>\<star> v2) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w)
                        = (t1 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (t2 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v1 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (v2 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w))"
                  using 3 4 v12 by simp
                also have "... = (t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> ((t2 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (v2 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w))"
                proof -
                  have "is_Hcomp (t2 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u)"
                    using t2 u u' tu is_Hcomp_HcompNml by auto
                  moreover have "is_Hcomp (v2 \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w)"
                    using v2 v12 w w' vw is_Hcomp_HcompNml by auto
                  ultimately show ?thesis
                    using u u' v w t1 v1 t12 v12 HcompNml_Prim
                    by (metis VcompNml.simps(2) VcompNml.simps(3) is_Hcomp_def
                        term.distinct_disc(3))
                qed
                also have "... = (t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
                  using u w tu uw vw t2 v2 1 2 Nml_implies_Arr I2 by auto
                also have "... = ((t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<star> (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2)) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
                proof -
                  have "\<not>is_Prim\<^sub>0 (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)"
                    using u w u' w' by (cases u, simp_all; cases w, simp_all)
                  hence "((t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<star> (t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2)) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w)
                           = (t1 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v1) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> ((t2 \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> v2) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w))"
                    by (cases "u \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> w") simp_all
                  thus ?thesis by presburger
                qed
                finally show ?thesis by blast
              qed
            qed
          qed
          ultimately show ?thesis by blast
        qed
      qed
      moreover have "Src t = Trg u"
        using assms Src_Dom Trg_Dom Src_Cod Trg_Cod Nml_implies_Arr by metis
      ultimately show ?thesis using assms by simp
    qed

    text \<open>
      The following function reduces a formal arrow to normal form.
    \<close>

    fun Nmlize :: "'a term \<Rightarrow> 'a term"   ("\<^bold>\<lfloor>_\<^bold>\<rfloor>")
    where "\<^bold>\<lfloor>\<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0\<^bold>\<rfloor> = \<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^sub>0"
        | "\<^bold>\<lfloor>\<^bold>\<langle>\<mu>\<^bold>\<rangle>\<^bold>\<rfloor> = \<^bold>\<langle>\<mu>\<^bold>\<rangle>"
        | "\<^bold>\<lfloor>t \<^bold>\<star> u\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>t \<^bold>\<cdot> u\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<l>\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<r>\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = (\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>"
        | "\<^bold>\<lfloor>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>)"

    lemma Nml_Nmlize:
    assumes "Arr t"
    shows "Nml \<^bold>\<lfloor>t\<^bold>\<rfloor>" and "Src \<^bold>\<lfloor>t\<^bold>\<rfloor> = Src t" and "Trg \<^bold>\<lfloor>t\<^bold>\<rfloor> = Trg t"
    and "Dom \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor>" and "Cod \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>"
    proof -
      have 0: "Arr t \<Longrightarrow> Nml \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> Src \<^bold>\<lfloor>t\<^bold>\<rfloor> = Src t \<and> Trg \<^bold>\<lfloor>t\<^bold>\<rfloor> = Trg t \<and>
                                     Dom \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<and> Cod \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>"
        using Nml_HcompNml Nml_VcompNml HcompNml_assoc
              Src_VcompNml Trg_VcompNml VSeq_implies_HPar
        apply (induct t)
                 apply auto
      proof -
        fix t
        assume 1: "Arr t"
        assume 2: "Nml \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        assume 3: "Src \<^bold>\<lfloor>t\<^bold>\<rfloor> = Src t"
        assume 4: "Trg \<^bold>\<lfloor>t\<^bold>\<rfloor> = Trg t"
        assume 5: "Dom \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor>"
        assume 6: "Cod \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>"
        have 7: "Nml \<^bold>\<lfloor>Dom t\<^bold>\<rfloor>"
          using 2 5 Nml_Dom by fastforce
        have 8: "Trg \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Trg t\<^bold>\<rfloor>"
          using 1 2 4 Nml_Trg Obj_Trg
          by (metis Nml.elims(2) Nmlize.simps(1) Nmlize.simps(2) Obj.simps(3))
        have 9: "Nml \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>"
          using 2 6 Nml_Cod by fastforce
        have 10: "Src \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Src t\<^bold>\<rfloor>"
          using 1 2 3 Nml_Src Obj_Src
          by (metis Nml.elims(2) Nmlize.simps(1) Nmlize.simps(2) Obj.simps(3))
        show "\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> = \<^bold>\<lfloor>Trg t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t\<^bold>\<rfloor>"
          using 2 5 7 8 Nml_implies_Arr Trg_Dom HcompNml_Trg_Nml by metis
        show "\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> = \<^bold>\<lfloor>Trg t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>"
          using 2 6 8 9 Nml_implies_Arr Trg_Cod HcompNml_Trg_Nml by metis
        show "\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Src t\<^bold>\<rfloor>"
          using 2 5 7 10 Nml_implies_Arr Src_Dom HcompNml_Nml_Src by metis
        show "\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Src t\<^bold>\<rfloor>"
          using 2 6 9 10 Nml_implies_Arr Src_Cod HcompNml_Nml_Src by metis
        next
        fix t1 t2 t3
        assume "Nml \<^bold>\<lfloor>t1\<^bold>\<rfloor>" and "Nml \<^bold>\<lfloor>t2\<^bold>\<rfloor>" and "Nml \<^bold>\<lfloor>t3\<^bold>\<rfloor>"
        assume "Src t1 = Trg t2" and "Src t2 = Trg t3"
        assume "Src \<^bold>\<lfloor>t1\<^bold>\<rfloor> = Trg t2" and "Src \<^bold>\<lfloor>t2\<^bold>\<rfloor> = Trg t3"
        assume "Trg \<^bold>\<lfloor>t1\<^bold>\<rfloor> = Trg t1" and "Trg \<^bold>\<lfloor>t2\<^bold>\<rfloor> = Trg t2" and "Trg \<^bold>\<lfloor>t3\<^bold>\<rfloor> = Trg t3"
        assume "Dom \<^bold>\<lfloor>t1\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t1\<^bold>\<rfloor>" and "Cod \<^bold>\<lfloor>t1\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t1\<^bold>\<rfloor>" and "Dom \<^bold>\<lfloor>t2\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t2\<^bold>\<rfloor>"
        and "Cod \<^bold>\<lfloor>t2\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t2\<^bold>\<rfloor>" and "Dom \<^bold>\<lfloor>t3\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t3\<^bold>\<rfloor>" and "Cod \<^bold>\<lfloor>t3\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t3\<^bold>\<rfloor>"
        show "\<^bold>\<lfloor>Dom t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t3\<^bold>\<rfloor> =
              (\<^bold>\<lfloor>Dom t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t2\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t3\<^bold>\<rfloor>"
          using Nml_Dom Nml_implies_Arr Src_Dom Trg_Dom
                HcompNml_assoc [of "\<^bold>\<lfloor>Dom t1\<^bold>\<rfloor>" "\<^bold>\<lfloor>Dom t2\<^bold>\<rfloor>" "\<^bold>\<lfloor>Dom t3\<^bold>\<rfloor>"]
                \<open>Nml \<^bold>\<lfloor>t1\<^bold>\<rfloor>\<close> \<open>Nml \<^bold>\<lfloor>t2\<^bold>\<rfloor>\<close> \<open>Nml \<^bold>\<lfloor>t3\<^bold>\<rfloor>\<close>
                \<open>Dom \<^bold>\<lfloor>t1\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t1\<^bold>\<rfloor>\<close> \<open>Dom \<^bold>\<lfloor>t2\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t2\<^bold>\<rfloor>\<close> \<open>Dom \<^bold>\<lfloor>t3\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t3\<^bold>\<rfloor>\<close>
                \<open>Src \<^bold>\<lfloor>t1\<^bold>\<rfloor> = Trg t2\<close> \<open>Trg \<^bold>\<lfloor>t2\<^bold>\<rfloor> = Trg t2\<close>
                \<open>Src \<^bold>\<lfloor>t2\<^bold>\<rfloor> = Trg t3\<close> \<open>Trg \<^bold>\<lfloor>t3\<^bold>\<rfloor> = Trg t3\<close>
          by metis
        show "\<^bold>\<lfloor>Cod t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t3\<^bold>\<rfloor> = (\<^bold>\<lfloor>Cod t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t2\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t3\<^bold>\<rfloor>"
          using Nml_Cod Nml_implies_Arr Src_Cod Trg_Cod
                HcompNml_assoc [of "\<^bold>\<lfloor>Cod t1\<^bold>\<rfloor>" "\<^bold>\<lfloor>Cod t2\<^bold>\<rfloor>" "\<^bold>\<lfloor>Cod t3\<^bold>\<rfloor>"]
                \<open>Nml \<^bold>\<lfloor>t1\<^bold>\<rfloor>\<close> \<open>Nml \<^bold>\<lfloor>t2\<^bold>\<rfloor>\<close> \<open>Nml \<^bold>\<lfloor>t3\<^bold>\<rfloor>\<close>
                \<open>Cod \<^bold>\<lfloor>t1\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t1\<^bold>\<rfloor>\<close> \<open>Cod \<^bold>\<lfloor>t2\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t2\<^bold>\<rfloor>\<close> \<open>Cod \<^bold>\<lfloor>t3\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t3\<^bold>\<rfloor>\<close>
                \<open>Src \<^bold>\<lfloor>t1\<^bold>\<rfloor> = Trg t2\<close> \<open>Trg \<^bold>\<lfloor>t2\<^bold>\<rfloor> = Trg t2\<close>
                \<open>Src \<^bold>\<lfloor>t2\<^bold>\<rfloor> = Trg t3\<close> \<open>Trg \<^bold>\<lfloor>t3\<^bold>\<rfloor> = Trg t3\<close>
          by metis
      qed
      show "Nml \<^bold>\<lfloor>t\<^bold>\<rfloor>" using assms 0 by blast
      show "Src \<^bold>\<lfloor>t\<^bold>\<rfloor> = Src t" using assms 0 by blast
      show "Trg \<^bold>\<lfloor>t\<^bold>\<rfloor> = Trg t" using assms 0 by blast
      show "Dom \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor>" using assms 0 by blast
      show "Cod \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>" using assms 0 by blast
    qed

    lemma Nmlize_in_Hom [intro]:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>t\<^bold>\<rfloor> \<in> HHom (Src t) (Trg t)" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> \<in> VHom \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>"
      using assms Nml_Nmlize Nml_implies_Arr by auto

    lemma Nmlize_Src:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>Src t\<^bold>\<rfloor> = Src \<^bold>\<lfloor>t\<^bold>\<rfloor>" and "\<^bold>\<lfloor>Src t\<^bold>\<rfloor> = Src t"
    proof -
      have 1: "Obj (Src t)"
        using assms by simp
      obtain a where a: "obj a \<and> Src t = \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0"
        using 1 by (cases "Src t", simp_all)
      show "\<^bold>\<lfloor>Src t\<^bold>\<rfloor> = Src t"
        using a by simp
      thus "\<^bold>\<lfloor>Src t\<^bold>\<rfloor> = Src \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        using assms Nmlize_in_Hom by simp
    qed

    lemma Nmlize_Trg:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>Trg t\<^bold>\<rfloor> = Trg \<^bold>\<lfloor>t\<^bold>\<rfloor>" and "\<^bold>\<lfloor>Trg t\<^bold>\<rfloor> = Trg t"
    proof -
      have 1: "Obj (Trg t)"
        using assms by simp
      obtain a where a: "obj a \<and> Trg t = \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0"
        using 1 by (cases "Trg t", simp_all)
      show "\<^bold>\<lfloor>Trg t\<^bold>\<rfloor> = Trg t"
        using a by simp
      thus "\<^bold>\<lfloor>Trg t\<^bold>\<rfloor> = Trg \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        using assms Nmlize_in_Hom by simp
    qed

    lemma Nmlize_Dom:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> = Dom \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms Nmlize_in_Hom by simp

    lemma Nmlize_Cod:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> = Cod \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms Nmlize_in_Hom by simp

    lemma Ide_Nmlize_Ide:
    assumes "Ide t"
    shows "Ide \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      have "Ide t \<Longrightarrow> Ide \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        using Ide_HcompNml Nml_Nmlize
        by (induct t, simp_all)
      thus ?thesis using assms by blast
    qed

    lemma Ide_Nmlize_Can:
    assumes "Can t"
    shows "Ide \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      have "Can t \<Longrightarrow> Ide \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        using Can_implies_Arr Ide_HcompNml Nml_Nmlize Ide_VcompNml Nml_HcompNml
        apply (induct t, auto simp add: Dom_Ide Cod_Ide)
        by (metis Ide_VcompNml)
      thus ?thesis using assms by blast
    qed

    lemma Can_Nmlize_Can:
    assumes "Can t"
    shows "Can \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms Ide_Nmlize_Can Ide_implies_Can by auto

    lemma Nmlize_Nml [simp]:
    assumes "Nml t"
    shows "\<^bold>\<lfloor>t\<^bold>\<rfloor> = t"
    proof -
      have "Nml t \<Longrightarrow> \<^bold>\<lfloor>t\<^bold>\<rfloor> = t"
        apply (induct t, simp_all)
        using HcompNml_Prim Nml_HcompD by metis
      thus ?thesis using assms by blast
    qed

    lemma Nmlize_Nmlize [simp]:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms Nml_Nmlize Nmlize_Nml by blast

    lemma Nmlize_Hcomp:
    assumes "Arr t" and "Arr u"
    shows "\<^bold>\<lfloor>t \<^bold>\<star> u\<^bold>\<rfloor> = \<^bold>\<lfloor>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<^bold>\<rfloor>"
      using assms Nmlize_Nmlize by simp

    lemma Nmlize_Hcomp_Obj_Arr [simp]:
    assumes "Arr u"
    shows "\<^bold>\<lfloor>\<^bold>\<langle>b\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> u\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
      using assms by simp

    lemma Nmlize_Hcomp_Arr_Obj [simp]:
    assumes "Arr t" and "Src t = \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0"
    shows "\<^bold>\<lfloor>t \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms HcompNml_Nml_Src Nmlize_in_Hom by simp

    lemma Nmlize_Hcomp_Prim_Arr [simp]:
    assumes "Arr u" and "\<not> is_Prim\<^sub>0 \<^bold>\<lfloor>u\<^bold>\<rfloor>"
    shows "\<^bold>\<lfloor>\<^bold>\<langle>\<mu>\<^bold>\<rangle> \<^bold>\<star> u\<^bold>\<rfloor> = \<^bold>\<langle>\<mu>\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<lfloor>u\<^bold>\<rfloor>"
      using assms by simp

    lemma Nmlize_Hcomp_Hcomp:
    assumes "Arr t" and "Arr u" and "Arr v" and "Src t = Trg u" and "Src u = Trg v"
    shows "\<^bold>\<lfloor>(t \<^bold>\<star> u) \<^bold>\<star> v\<^bold>\<rfloor> = \<^bold>\<lfloor>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<star> (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>v\<^bold>\<rfloor>)\<^bold>\<rfloor>"
      using assms Nml_Nmlize Nmlize_Nmlize by (simp add: HcompNml_assoc)

    lemma Nmlize_Hcomp_Hcomp':
    assumes "Arr t" and "Arr u" and "Arr v" and "Src t = Trg u" and "Src u = Trg v"
    shows "\<^bold>\<lfloor>t \<^bold>\<star> u \<^bold>\<star> v\<^bold>\<rfloor> = \<^bold>\<lfloor>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>v\<^bold>\<rfloor>\<^bold>\<rfloor>"
      using assms Nml_Nmlize Nmlize_Nmlize by (simp add: HcompNml_assoc)

    lemma Nmlize_Vcomp_Cod_Arr:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>Cod t \<^bold>\<cdot> t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      have "Arr t \<Longrightarrow> \<^bold>\<lfloor>Cod t \<^bold>\<cdot> t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      proof (induct t, simp_all)
        show "\<And>x. arr x \<Longrightarrow> cod x \<cdot> x = x"
          using comp_cod_arr by blast
        fix t1 t2
        show "\<And>t1 t2. \<^bold>\<lfloor>Cod t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t1\<^bold>\<rfloor> = \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<Longrightarrow> \<^bold>\<lfloor>Cod t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor> = \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<Longrightarrow> HSeq t1 t2 \<Longrightarrow>
                      (\<^bold>\<lfloor>Cod t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t2\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (\<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor>) = \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor>"
          using VcompNml_HcompNml Ide_Cod Nml_Nmlize Nmlize_in_Hom
          by simp
        show "\<^bold>\<lfloor>Cod t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t1\<^bold>\<rfloor> = \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<Longrightarrow> \<^bold>\<lfloor>Cod t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor> = \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<Longrightarrow> VSeq t1 t2 \<Longrightarrow>
              \<^bold>\<lfloor>Cod t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor> = \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor>"
          using VcompNml_assoc [of "\<^bold>\<lfloor>Cod t1\<^bold>\<rfloor>" "\<^bold>\<lfloor>t1\<^bold>\<rfloor>" "\<^bold>\<lfloor>t2\<^bold>\<rfloor>"] Ide_Cod
                Nml_Nmlize
          by simp
        next
        show "\<And>t. \<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor> \<Longrightarrow> Arr t \<Longrightarrow> (\<^bold>\<lfloor>Trg t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
          by (metis Arr.simps(6) Cod.simps(6) Nmlize.simps(3) Nmlize.simps(6)
              Nmlize_Cod)
        show "\<And>t. \<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor> \<Longrightarrow> Arr t \<Longrightarrow> (\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Src t\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
          by (simp add: Nml_Nmlize(1) Nml_Nmlize(2) Nmlize_Src(2) HcompNml_Nml_Obj)
        show "\<And>t1 t2 t3. \<^bold>\<lfloor>Cod t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t1\<^bold>\<rfloor> = \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<Longrightarrow> \<^bold>\<lfloor>Cod t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor> = \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<Longrightarrow>
                          \<^bold>\<lfloor>Cod t3\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t3\<^bold>\<rfloor> = \<^bold>\<lfloor>t3\<^bold>\<rfloor> \<Longrightarrow>
                          Arr t1 \<and> Arr t2 \<and> Arr t3 \<and> Src t1 = Trg t2 \<and> Src t2 = Trg t3 \<Longrightarrow>
                         (\<^bold>\<lfloor>Cod t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t3\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> ((\<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t3\<^bold>\<rfloor>) =
                         (\<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t3\<^bold>\<rfloor>"
          using VcompNml_HcompNml Ide_Cod HcompNml_in_Hom Nml_HcompNml
                Nml_Nmlize Nmlize_in_Hom HcompNml_assoc
          by simp
        show "\<And>t1 t2 t3. \<^bold>\<lfloor>Cod t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t1\<^bold>\<rfloor> = \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<Longrightarrow> \<^bold>\<lfloor>Cod t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor> = \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<Longrightarrow>
                          \<^bold>\<lfloor>Cod t3\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t3\<^bold>\<rfloor> = \<^bold>\<lfloor>t3\<^bold>\<rfloor> \<Longrightarrow>
                          Arr t1 \<and> Arr t2 \<and> Arr t3 \<and> Src t1 = Trg t2 \<and> Src t2 = Trg t3 \<Longrightarrow>
                          ((\<^bold>\<lfloor>Cod t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t2\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t3\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (\<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t3\<^bold>\<rfloor>) =
                          \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t3\<^bold>\<rfloor>"
          using VcompNml_HcompNml Ide_Cod HcompNml_in_Hom Nml_HcompNml
                Nml_Nmlize Nmlize_in_Hom HcompNml_assoc
          by simp
      qed
      thus ?thesis using assms by blast
    qed

    lemma Nmlize_Vcomp_Arr_Dom:
    assumes "Arr t"
    shows "\<^bold>\<lfloor>t \<^bold>\<cdot> Dom t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      have "Arr t \<Longrightarrow> \<^bold>\<lfloor>t \<^bold>\<cdot> Dom t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      proof (induct t, simp_all)
        show "\<And>x. arr x \<Longrightarrow> x \<cdot> local.dom x = x"
          using comp_arr_dom by blast
        fix t1 t2
        show "\<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t1\<^bold>\<rfloor> = \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<Longrightarrow> \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t2\<^bold>\<rfloor> = \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<Longrightarrow> HSeq t1 t2 \<Longrightarrow>
              (\<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (\<^bold>\<lfloor>Dom t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t2\<^bold>\<rfloor>) = \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor>"
          using VcompNml_HcompNml Ide_Dom HcompNml_in_Hom Nml_HcompNml
                Nml_Nmlize Nmlize_in_Hom HcompNml_assoc
          by simp
        show "\<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t2\<^bold>\<rfloor> = \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<Longrightarrow> \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t2\<^bold>\<rfloor> = \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<Longrightarrow> VSeq t1 t2 \<Longrightarrow>
              (\<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t2\<^bold>\<rfloor> = \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor>"
          using VcompNml_assoc [of "\<^bold>\<lfloor>t1\<^bold>\<rfloor>" "\<^bold>\<lfloor>t2\<^bold>\<rfloor>" "\<^bold>\<lfloor>Dom t2\<^bold>\<rfloor>"] Ide_Dom Nml_Nmlize
          by simp
        next
        show "\<And>t. \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor> \<Longrightarrow> Arr t \<Longrightarrow> \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (\<^bold>\<lfloor>Trg t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t\<^bold>\<rfloor>) = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
          by (simp add: Nml_Nmlize(1) Nml_Nmlize(3) Nmlize_Trg(2)
              HcompNml_Obj_Nml bicategorical_language.Ide_Dom
              bicategorical_language_axioms)
        show "\<And>t. \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor> \<Longrightarrow> Arr t \<Longrightarrow> \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Src t\<^bold>\<rfloor>) = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
          by (simp add: Nml_Nmlize(1) Nml_Nmlize(2) Nmlize_Src(2) HcompNml_Nml_Obj)
        show "\<And>t1 t2 t3. \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t1\<^bold>\<rfloor> = \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<Longrightarrow> \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t2\<^bold>\<rfloor> = \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<Longrightarrow>
                          \<^bold>\<lfloor>t3\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t3\<^bold>\<rfloor> = \<^bold>\<lfloor>t3\<^bold>\<rfloor> \<Longrightarrow>
                          Arr t1 \<and> Arr t2 \<and> Arr t3 \<and> Src t1 = Trg t2 \<and> Src t2 = Trg t3 \<Longrightarrow>
                          ((\<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t3\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> ((\<^bold>\<lfloor>Dom t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t2\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t3\<^bold>\<rfloor>) =
                          (\<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t3\<^bold>\<rfloor>"
          using VcompNml_HcompNml Ide_Dom HcompNml_in_Hom Nml_HcompNml
                Nml_Nmlize Nmlize_in_Hom HcompNml_assoc
          by simp
        show "\<And>t1 t2 t3. \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t1\<^bold>\<rfloor> = \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<Longrightarrow> \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t2\<^bold>\<rfloor> = \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<Longrightarrow>
                          \<^bold>\<lfloor>t3\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t3\<^bold>\<rfloor> = \<^bold>\<lfloor>t3\<^bold>\<rfloor> \<Longrightarrow>
                          Arr t1 \<and> Arr t2 \<and> Arr t3 \<and> Src t1 = Trg t2 \<and> Src t2 = Trg t3 \<Longrightarrow>
                          (\<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t3\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> (\<^bold>\<lfloor>Dom t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t3\<^bold>\<rfloor>) =
                          \<^bold>\<lfloor>t1\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t2\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>t3\<^bold>\<rfloor>"
          using VcompNml_HcompNml Ide_Dom HcompNml_in_Hom Nml_HcompNml
                Nml_Nmlize Nmlize_in_Hom HcompNml_assoc
          by simp
      qed
      thus ?thesis using assms by blast
    qed

    lemma Nmlize_Inv:
    assumes "Can t"
    shows "\<^bold>\<lfloor>Inv t\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      have "Can t \<Longrightarrow> \<^bold>\<lfloor>Inv t\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      proof (induct t, simp_all)
        fix u v
        assume I1: "\<^bold>\<lfloor>Inv u\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>u\<^bold>\<rfloor>"
        assume I2: "\<^bold>\<lfloor>Inv v\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>v\<^bold>\<rfloor>"
        show "Can u \<and> Can v \<and> Src u = Trg v \<Longrightarrow> Inv \<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>v\<^bold>\<rfloor> = Inv (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>)"
          using Inv_HcompNml Nml_Nmlize Can_implies_Arr Can_Nmlize_Can
                I1 I2
          by simp
        show "Can u \<and> Can v \<and> Dom u = Cod v \<Longrightarrow> Inv \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>u\<^bold>\<rfloor> = Inv (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>)"
          using Inv_VcompNml Nml_Nmlize Can_implies_Arr Nmlize_in_Hom Can_Nmlize_Can
                I1 I2
          by simp
        fix w
        assume I3: "\<^bold>\<lfloor>Inv w\<^bold>\<rfloor> = Inv \<^bold>\<lfloor>w\<^bold>\<rfloor>"
        assume uvw: "Can u \<and> Can v \<and> Can w \<and> Src u = Trg v \<and> Src v = Trg w"
        show "Inv \<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (Inv \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>w\<^bold>\<rfloor>) = Inv ((\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>)"
          using uvw I1 I2 I3
                Inv_HcompNml Nml_Nmlize Can_implies_Arr Can_Nmlize_Can
                Nml_HcompNml Can_HcompNml HcompNml_assoc
          by simp
        show "(Inv \<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>v\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Inv \<^bold>\<lfloor>w\<^bold>\<rfloor> = Inv (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>))"
          using uvw I1 I2 I3
                Inv_HcompNml Nml_Nmlize Can_implies_Arr Can_Nmlize_Can
                Nml_HcompNml Can_HcompNml HcompNml_assoc Can_Inv
          by simp
      qed
      thus ?thesis using assms by blast
    qed

    subsection "Reductions"

    text \<open>
      Function \<open>red\<close> defined below takes a formal identity @{term t} to a canonical arrow
      \<open>f\<^bold>\<down> \<in> Hom f \<^bold>\<lfloor>f\<^bold>\<rfloor>\<close>.  The auxiliary function \<open>red2\<close> takes a pair @{term "(f, g)"}
      of normalized formal identities and produces a canonical arrow
      \<open>f \<^bold>\<Down> g \<in> Hom (f \<^bold>\<star> g) \<^bold>\<lfloor>f \<^bold>\<star> g\<^bold>\<rfloor>\<close>.
    \<close>

    fun red2                       (infixr "\<^bold>\<Down>" 53)
    where "\<^bold>\<langle>b\<^bold>\<rangle>\<^sub>0 \<^bold>\<Down> u = \<^bold>\<l>\<^bold>[u\<^bold>]"
        | "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 = \<^bold>\<r>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>]"
        | "\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> u = \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> u"
        | "(t \<^bold>\<star> u) \<^bold>\<Down> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 = \<^bold>\<r>\<^bold>[t \<^bold>\<star> u\<^bold>]"
        | "(t \<^bold>\<star> u) \<^bold>\<Down> v = (t \<^bold>\<Down> \<^bold>\<lfloor>u \<^bold>\<star> v\<^bold>\<rfloor>) \<^bold>\<cdot> (t \<^bold>\<star> (u \<^bold>\<Down> v)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[t, u, v\<^bold>]"
        | "t \<^bold>\<Down> u = undefined"

    fun red                         ("_\<^bold>\<down>" [56] 56)
    where "\<^bold>\<langle>f\<^bold>\<rangle>\<^sub>0\<^bold>\<down> = \<^bold>\<langle>f\<^bold>\<rangle>\<^sub>0"
        | "\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>\<down> = \<^bold>\<langle>f\<^bold>\<rangle>"
        | "(t \<^bold>\<star> u)\<^bold>\<down> = (if Nml (t \<^bold>\<star> u) then t \<^bold>\<star> u else (\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>u\<^bold>\<rfloor>) \<^bold>\<cdot> (t\<^bold>\<down> \<^bold>\<star> u\<^bold>\<down>))"
        | "t\<^bold>\<down> = undefined"

    lemma red_Nml [simp]:
    assumes "Nml a"
    shows "a\<^bold>\<down> = a"
      using assms by (cases a, simp_all)

    lemma red2_Nml:
    assumes "Nml (a \<^bold>\<star> b)"
    shows "a \<^bold>\<Down> b = a \<^bold>\<star> b"
    proof -
      have a: "a = \<^bold>\<langle>un_Prim a\<^bold>\<rangle>"
        using assms Nml_HcompD by metis
      have b: "Nml b \<and> \<not> is_Prim\<^sub>0 b"
        using assms Nml_HcompD by metis
      show ?thesis using a b
        apply (cases b)
          apply simp_all
         apply (metis red2.simps(3))
        by (metis red2.simps(4))
    qed

    lemma Can_red2:
    assumes "Ide a" and "Nml a" and "Ide b" and "Nml b" and "Src a = Trg b"
    shows "Can (a \<^bold>\<Down> b)"
    and "a \<^bold>\<Down> b \<in> VHom (a \<^bold>\<star> b) \<^bold>\<lfloor>a \<^bold>\<star> b\<^bold>\<rfloor>"
    proof -
      have 0: "\<And>b. \<lbrakk> Ide a \<and> Nml a; Ide b \<and> Nml b; Src a = Trg b \<rbrakk> \<Longrightarrow>
                     Can (a \<^bold>\<Down> b) \<and> a \<^bold>\<Down> b \<in> VHom (a \<^bold>\<star> b) \<^bold>\<lfloor>a \<^bold>\<star> b\<^bold>\<rfloor>"
      proof (induct a, simp_all add: HcompNml_Nml_Src HcompNml_Trg_Nml)
        fix x b
        show "Ide b \<and> Nml b \<Longrightarrow> Can (Trg b \<^bold>\<Down> b) \<and> Arr (Trg b \<^bold>\<Down> b) \<and>
                                 Dom (Trg b \<^bold>\<Down> b) = Trg b \<^bold>\<star> b \<and> Cod (Trg b \<^bold>\<Down> b) = b"
          using Ide_implies_Can Ide_in_Hom Nmlize_Nml
          apply (cases b, simp_all)
        proof -
          fix u v
          assume uv: "Ide u \<and> Ide v \<and> Src u = Trg v \<and> Nml (u \<^bold>\<star> v)"
          show "Can (Trg u \<^bold>\<Down> (u \<^bold>\<star> v)) \<and> Arr (Trg u \<^bold>\<Down> (u \<^bold>\<star> v)) \<and>
                Dom (Trg u \<^bold>\<Down> (u \<^bold>\<star> v)) = Trg u \<^bold>\<star> u \<^bold>\<star> v \<and>
                Cod (Trg u \<^bold>\<Down> (u \<^bold>\<star> v)) = u \<^bold>\<star> v"
            using uv Ide_implies_Can Can_implies_Arr Ide_in_Hom
            by (cases u, simp_all)
        qed
        show "ide x \<and> arr x \<Longrightarrow> Ide b \<and> Nml b \<Longrightarrow> \<^bold>\<langle>src x\<^bold>\<rangle>\<^sub>0 = Trg b \<Longrightarrow>
              Can (\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<Down> b) \<and> Arr (\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<Down> b) \<and> Dom (\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<Down> b) = \<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<star> b \<and> Cod (\<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<Down> b) =
              \<^bold>\<langle>x\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b"
            using Ide_implies_Can Can_implies_Arr Nmlize_Nml Ide_in_Hom
            by (cases b, simp_all)
        next
        fix u v w
        assume uv: "Ide u \<and> Ide v \<and> Src u = Trg v \<and> Nml (u \<^bold>\<star> v)"
        assume vw: "Src v = Trg w"
        assume w: "Ide w \<and> Nml w"
        assume I1: "\<And>w. \<lbrakk> Nml u; Ide w \<and> Nml w; Trg v = Trg w \<rbrakk> \<Longrightarrow>
                          Can (u \<^bold>\<Down> w) \<and> Arr (u \<^bold>\<Down> w) \<and>
                          Dom (u \<^bold>\<Down> w) = u \<^bold>\<star> w \<and> Cod (u \<^bold>\<Down> w) = u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w"
        assume I2: "\<And>x. \<lbrakk> Nml v; Ide x \<and> Nml x; Trg w = Trg x \<rbrakk> \<Longrightarrow>
                          Can (v \<^bold>\<Down> x) \<and> Arr (v \<^bold>\<Down> x) \<and>
                          Dom (v \<^bold>\<Down> x) = v \<^bold>\<star> x \<and> Cod (v \<^bold>\<Down> x) = v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> x"
        show "Can ((u \<^bold>\<star> v) \<^bold>\<Down> w) \<and> Arr ((u \<^bold>\<star> v) \<^bold>\<Down> w) \<and>
              Dom ((u \<^bold>\<star> v) \<^bold>\<Down> w) = (u \<^bold>\<star> v) \<^bold>\<star> w \<and>
              Cod ((u \<^bold>\<star> v) \<^bold>\<Down> w) = (\<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w"
        proof -
          have u: "Nml u \<and> Ide u"
            using uv Nml_HcompD by blast
          have v: "Nml v \<and> Ide v"
            using uv Nml_HcompD by blast
          have "is_Prim\<^sub>0 w \<Longrightarrow> ?thesis"
          proof -
            assume 1: "is_Prim\<^sub>0 w"
            have 2: "(u \<^bold>\<star> v) \<^bold>\<Down> w = \<^bold>\<r>\<^bold>[u \<^bold>\<star> v\<^bold>]"
              using 1 by (cases w, simp_all)
            have 3: "Can (u \<^bold>\<Down> v) \<and> Arr (u \<^bold>\<Down> v) \<and> Dom (u \<^bold>\<Down> v) = u \<^bold>\<star> v \<and> Cod (u \<^bold>\<Down> v) = u \<^bold>\<star> v"
              using u v uv 1 2 I1 Nmlize_Nml Nmlize.simps(3) by metis
            hence 4: "VSeq (u \<^bold>\<Down> v) \<^bold>\<r>\<^bold>[u \<^bold>\<star> v\<^bold>]"
              using uv
              by (metis (mono_tags, lifting) Arr.simps(7) Cod.simps(3) Cod.simps(7)
                  Nml_implies_Arr Ide_in_Hom(2) mem_Collect_eq)
            have "Can ((u \<^bold>\<star> v) \<^bold>\<Down> w)"
              using 1 2 3 4 uv by (simp add: Ide_implies_Can)
            moreover have "Dom ((u \<^bold>\<star> v) \<^bold>\<Down> w) = (u \<^bold>\<star> v) \<^bold>\<star> w"
              using 1 2 3 4 u v w uv vw I1 Ide_in_Hom Nml_HcompNml Ide_in_Hom
              apply (cases w) by simp_all
            moreover have "Cod ((u \<^bold>\<star> v) \<^bold>\<Down> w) = \<^bold>\<lfloor>(u \<^bold>\<star> v) \<^bold>\<star> w\<^bold>\<rfloor>"
              using 1 2 3 4 uv
              using Nmlize_Nml apply (cases w, simp_all)
              by (metis Nmlize.simps(3) Nmlize_Nml HcompNml.simps(3))
            ultimately show ?thesis using w Can_implies_Arr by (simp add: 1 uv)
          qed
          moreover have "\<not> is_Prim\<^sub>0 w \<Longrightarrow> ?thesis"
          proof -
            assume 1: "\<not> is_Prim\<^sub>0 w"
            have 2: "(u \<^bold>\<star> v) \<^bold>\<Down> w = (u \<^bold>\<Down> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor>) \<^bold>\<cdot> (u \<^bold>\<star> v \<^bold>\<Down> w) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[u, v, w\<^bold>]"
              using 1 u v uv w by (cases w; simp)
            have 3: "Can (u \<^bold>\<Down> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor>) \<and> Dom (u \<^bold>\<Down> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor>) = u \<^bold>\<star> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor> \<and>
                                         Cod (u \<^bold>\<Down> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor>) = \<^bold>\<lfloor>u \<^bold>\<star> (v \<^bold>\<star> w)\<^bold>\<rfloor>"
            proof -
              have "Can (u \<^bold>\<Down> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor>) \<and> Dom (u \<^bold>\<Down> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor>) = u \<^bold>\<star> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor> \<and>
                                        Cod (u \<^bold>\<Down> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor>) = u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor>"
                using w uv Ide_HcompNml Nml_HcompNml(1)
                apply (cases u, simp_all)
                using u v vw I1 Nmlize_in_Hom(1) [of "v \<^bold>\<star> w"] Nml_Nmlize Ide_Nmlize_Ide
                by simp
              moreover have "u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor> = \<^bold>\<lfloor>u \<^bold>\<star> (v \<^bold>\<star> w)\<^bold>\<rfloor>"
                using uv u w Nmlize_Hcomp Nmlize_Nmlize Nml_implies_Arr by simp
              ultimately show ?thesis by presburger
            qed
            have 4: "Can (v \<^bold>\<Down> w) \<and> Dom (v \<^bold>\<Down> w) = v \<^bold>\<star> w \<and> Cod (v \<^bold>\<Down> w) = \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor>"
              using v w vw 1 2 I2 by simp
            hence 5: "Src (v \<^bold>\<Down> w) = Src w \<and> Trg (v \<^bold>\<Down> w) = Trg v"
              using Src_Dom Trg_Dom Can_implies_Arr by fastforce
            have "Can (u \<^bold>\<star> (v \<^bold>\<Down> w)) \<and> Dom (u \<^bold>\<star> (v \<^bold>\<Down> w)) = u \<^bold>\<star> (v \<^bold>\<star> w) \<and>
                                       Cod (u \<^bold>\<star> (v \<^bold>\<Down> w)) = u \<^bold>\<star> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor>"
              using u uv vw 4 5 Ide_implies_Can Ide_in_Hom by simp
            moreover have "\<^bold>\<lfloor>u \<^bold>\<star> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor>\<^bold>\<rfloor> = \<^bold>\<lfloor>u \<^bold>\<star> v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>"
            proof -
              have "\<^bold>\<lfloor>u \<^bold>\<star> \<^bold>\<lfloor>v \<^bold>\<star> w\<^bold>\<rfloor>\<^bold>\<rfloor> = u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w)"
                using u v w 4
                by (metis Ide_Dom Can_implies_Arr Ide_implies_Arr
                    Nml_Nmlize(1) Nmlize.simps(3) Nmlize_Nml)
              also have "... = (u \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> v) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w"
                using u v w uv vw HcompNml_assoc by metis
              also have "... = \<^bold>\<lfloor>u \<^bold>\<star> v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>"
                using u v w by (metis Nmlize.simps(3) Nmlize_Nml)
              finally show ?thesis by blast
            qed
            moreover have "Can \<^bold>\<a>\<^bold>[u, v, w\<^bold>] \<and> Dom \<^bold>\<a>\<^bold>[u, v, w\<^bold>] = (u \<^bold>\<star> v) \<^bold>\<star> w \<and>
                                            Cod \<^bold>\<a>\<^bold>[u, v, w\<^bold>] = u \<^bold>\<star> (v \<^bold>\<star> w)"
              using uv vw w Ide_implies_Can Ide_in_Hom by auto
            ultimately show ?thesis
              using uv w 2 3 4 Nml_implies_Arr Nmlize_Nmlize Ide_implies_Can
                    Nmlize_Nml Ide_Dom Can_implies_Arr
              by (metis Can.simps(4) Cod.simps(4) Dom.simps(4) Nmlize.simps(3))
          qed
          ultimately show ?thesis by blast
        qed
      qed
      show "Can (a \<^bold>\<Down> b)" using assms 0 by blast
      show "a \<^bold>\<Down> b \<in> VHom (a \<^bold>\<star> b) \<^bold>\<lfloor>a \<^bold>\<star> b\<^bold>\<rfloor>" using 0 assms by blast
    qed

    lemma red2_in_Hom [intro]:
    assumes "Ide u" and "Nml u" and "Ide v" and "Nml v" and "Src u = Trg v"
    shows "u \<^bold>\<Down> v \<in> HHom (Src v) (Trg u)" and "u \<^bold>\<Down> v \<in> VHom (u \<^bold>\<star> v) \<^bold>\<lfloor>u \<^bold>\<star> v\<^bold>\<rfloor>"
    proof -
      show 1: "u \<^bold>\<Down> v \<in> VHom (u \<^bold>\<star> v) \<^bold>\<lfloor>u \<^bold>\<star> v\<^bold>\<rfloor>"
        using assms Can_red2 Can_implies_Arr by simp
      show "u \<^bold>\<Down> v \<in> HHom (Src v) (Trg u)"
        using assms 1 Src_Dom [of "u \<^bold>\<Down> v"] Trg_Dom [of "u \<^bold>\<Down> v"] Can_red2 Can_implies_Arr by simp
    qed

    lemma red2_simps [simp]:
    assumes "Ide u" and "Nml u" and "Ide v" and "Nml v" and "Src u = Trg v"
    shows "Src (u \<^bold>\<Down> v) = Src v" and "Trg (u \<^bold>\<Down> v) = Trg u"
    and "Dom (u \<^bold>\<Down> v) = u \<^bold>\<star> v" and "Cod (u \<^bold>\<Down> v) = \<^bold>\<lfloor>u \<^bold>\<star> v\<^bold>\<rfloor>"
      using assms red2_in_Hom by auto

    lemma Can_red:
    assumes "Ide u"
    shows "Can (u\<^bold>\<down>)" and "u\<^bold>\<down> \<in> VHom u \<^bold>\<lfloor>u\<^bold>\<rfloor>"
    proof -
      have 0: "Ide u \<Longrightarrow> Can (u\<^bold>\<down>) \<and> u\<^bold>\<down> \<in> VHom u \<^bold>\<lfloor>u\<^bold>\<rfloor>"
      proof (induct u, simp_all add: Dom_Ide Cod_Ide)
        fix v w
        assume v: "Can (v\<^bold>\<down>) \<and> Arr (v\<^bold>\<down>) \<and> Dom (v\<^bold>\<down>) = v \<and> Cod (v\<^bold>\<down>) = \<^bold>\<lfloor>v\<^bold>\<rfloor>"
        assume w: "Can (w\<^bold>\<down>) \<and> Arr (w\<^bold>\<down>) \<and> Dom (w\<^bold>\<down>) = w \<and> Cod (w\<^bold>\<down>) = \<^bold>\<lfloor>w\<^bold>\<rfloor>"
        assume vw: "Ide v \<and> Ide w \<and> Src v = Trg w"
        show "(Nml (v \<^bold>\<star> w) \<longrightarrow>
                 Can v \<and> Can w \<and> v \<^bold>\<star> w = \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>) \<and>
              (\<not> Nml (v \<^bold>\<star> w) \<longrightarrow>
                 Can (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) \<and> Src (v\<^bold>\<down>) = Trg (w\<^bold>\<down>) \<and>
                 Dom (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) = \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>w\<^bold>\<rfloor> \<and> Arr (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) \<and> Src (v\<^bold>\<down>) = Trg (w\<^bold>\<down>) \<and>
                 Dom (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) = \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>w\<^bold>\<rfloor> \<and> Cod (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) = \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>)"
        proof
          show "Nml (v \<^bold>\<star> w) \<longrightarrow>
                  Can v \<and> Can w \<and> v \<^bold>\<star> w = \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>"
            using vw Nml_HcompD Ide_implies_Can Dom_Inv VcompNml_Ide_Nml Inv_Ide
                  Nmlize.simps(3) Nmlize_Nml
            by metis
          show "\<not> Nml (v \<^bold>\<star> w) \<longrightarrow>
                  Can (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) \<and> Src (v\<^bold>\<down>) = Trg (w\<^bold>\<down>) \<and>
                  Dom (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) = \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>w\<^bold>\<rfloor> \<and> Arr (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) \<and> Src (v\<^bold>\<down>) = Trg (w\<^bold>\<down>) \<and>
                  Dom (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) = \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>w\<^bold>\<rfloor> \<and> Cod (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) = \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>"
          proof
            assume 1: "\<not> Nml (v \<^bold>\<star> w)"
            have "Can (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>)"
              using v w vw Can_red2 Nml_Nmlize Ide_Nmlize_Ide Nml_HcompNml Ide_HcompNml
              by simp
            moreover have "Src (v\<^bold>\<down>) = Trg (w\<^bold>\<down>)"
              using v w vw Src_Dom Trg_Dom by metis
            moreover have "Dom (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) = \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>w\<^bold>\<rfloor> \<and> Cod (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) = \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>"
              using v w vw Can_red2 Nml_Nmlize Ide_Nmlize_Ide by simp
            ultimately show "Can (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) \<and> Src (v\<^bold>\<down>) = Trg (w\<^bold>\<down>) \<and>
                             Dom (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) = \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>w\<^bold>\<rfloor> \<and> Arr (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) \<and>
                             Src (v\<^bold>\<down>) = Trg (w\<^bold>\<down>) \<and> Dom (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) = \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>w\<^bold>\<rfloor> \<and>
                             Cod (\<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>w\<^bold>\<rfloor>) = \<^bold>\<lfloor>v\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>w\<^bold>\<rfloor>"
              using Can_implies_Arr by blast
          qed
        qed
      qed
      show "Can (u\<^bold>\<down>)" using assms 0 by blast
      show "u\<^bold>\<down> \<in> VHom u \<^bold>\<lfloor>u\<^bold>\<rfloor>" using assms 0 by blast
    qed

    lemma red_in_Hom [intro]:
    assumes "Ide t"
    shows "t\<^bold>\<down> \<in> HHom (Src t) (Trg t)" and "t\<^bold>\<down> \<in> VHom t \<^bold>\<lfloor>t\<^bold>\<rfloor>"
    proof -
      show 1: "t\<^bold>\<down> \<in> VHom t \<^bold>\<lfloor>t\<^bold>\<rfloor>"
        using assms Can_red Can_implies_Arr by simp
      show "t\<^bold>\<down> \<in> HHom (Src t) (Trg t)"
        using assms 1 Src_Dom [of "t\<^bold>\<down>"] Trg_Dom [of "t\<^bold>\<down>"] Can_red Can_implies_Arr by simp
    qed

    lemma red_simps [simp]:
    assumes "Ide t"
    shows "Src (t\<^bold>\<down>) = Src t" and "Trg (t\<^bold>\<down>) = Trg t"
    and "Dom (t\<^bold>\<down>) = t" and "Cod (t\<^bold>\<down>) = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms red_in_Hom by auto

    lemma red_Src:
    assumes "Ide t"
    shows "Src t\<^bold>\<down> = Src t"
      using assms is_Prim0_Src [of t]
      by (cases "Src t", simp_all)

    lemma red_Trg:
    assumes "Ide t"
    shows "Trg t\<^bold>\<down> = Trg t"
      using assms is_Prim0_Trg [of t]
      by (cases "Trg t", simp_all)

    lemma Nmlize_red [simp]:
    assumes "Ide t"
    shows "\<^bold>\<lfloor>t\<^bold>\<down>\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
      using assms Can_red Ide_Nmlize_Can Nmlize_in_Hom Ide_in_Hom by fastforce

    lemma Nmlize_red2 [simp]:
    assumes "Ide t" and "Ide u" and "Nml t" and "Nml u" and "Src t = Trg u"
    shows "\<^bold>\<lfloor>t \<^bold>\<Down> u\<^bold>\<rfloor> = \<^bold>\<lfloor>t \<^bold>\<star> u\<^bold>\<rfloor>"
      using assms Can_red2 Ide_Nmlize_Can Nmlize_in_Hom [of "t \<^bold>\<Down> u"] red2_in_Hom Ide_in_Hom
      by simp

  end

  subsection "Evaluation"

  text \<open>
    The following locale is concerned with the evaluation of terms of the bicategorical
    language determined by \<open>C\<close>, \<open>src\<^sub>C\<close>, and \<open>trg\<^sub>C\<close> in a bicategory \<open>(V, H, \<a>, \<i>, src, trg)\<close>,
    given a source and target-preserving functor from \<open>C\<close> to \<open>V\<close>.
  \<close>

  locale evaluation_map =
    C: horizontal_homs C src\<^sub>C trg\<^sub>C +
    bicategorical_language C src\<^sub>C trg\<^sub>C +
    bicategory V H \<a> \<i> src trg +
    E: "functor" C V E
    for C :: "'c comp"                   (infixr "\<cdot>\<^sub>C" 55)
    and src\<^sub>C :: "'c \<Rightarrow> 'c"
    and trg\<^sub>C :: "'c \<Rightarrow> 'c"
    and V :: "'b comp"                   (infixr "\<cdot>" 55)
    and H :: "'b comp"                   (infixr "\<star>" 53)
    and \<a> :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"       ("\<a>[_, _, _]")
    and \<i> :: "'b \<Rightarrow> 'b"                   ("\<i>[_]")
    and src :: "'b \<Rightarrow> 'b"
    and trg :: "'b \<Rightarrow> 'b"
    and E :: "'c \<Rightarrow> 'b" +
    assumes preserves_src: "E (src\<^sub>C x) = src (E x)"
    and preserves_trg: "E (trg\<^sub>C x) = trg (E x)"
  begin

    (* TODO: Figure out why this notation has to be reinstated. *)
    notation Nmlize  ("\<^bold>\<lfloor>_\<^bold>\<rfloor>")
    notation HcompNml    (infixr "\<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor>" 53)
    notation VcompNml    (infixr "\<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor>" 55)
    notation red          ("_\<^bold>\<down>" [56] 56)
    notation red2         (infixr "\<^bold>\<Down>" 53)

    primrec eval :: "'c term \<Rightarrow> 'b"    ("\<lbrace>_\<rbrace>")
    where "\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle>\<^sub>0\<rbrace> = E f"
        | "\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle>\<rbrace> = E f"
        | "\<lbrace>t \<^bold>\<star> u\<rbrace> = \<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace>"
        | "\<lbrace>t \<^bold>\<cdot> u\<rbrace> = \<lbrace>t\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
        | "\<lbrace>\<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace> = \<ll> \<lbrace>t\<rbrace>"
        | "\<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = \<ll>'.map \<lbrace>t\<rbrace>"
        | "\<lbrace>\<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> = \<rr> \<lbrace>t\<rbrace>"
        | "\<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = \<rr>'.map \<lbrace>t\<rbrace>"
        | "\<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> = \<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"
        | "\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = \<alpha>'.map (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"

    lemma preserves_obj:
    assumes "C.obj a"
    shows "obj (E a)"
    proof (unfold obj_def)
      show "arr (E a) \<and> src (E a) = E a"
      proof
        show "arr (E a)" using assms C.obj_def by simp
        have "src (E a) = E (src\<^sub>C a)"
           using assms preserves_src by metis
        also have "... = E a"
           using assms C.obj_def by simp
        finally show "src (E a) = E a" by simp
      qed
    qed

    lemma eval_in_hom':
    shows "Arr t \<Longrightarrow> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
    proof (induct t)
      show "\<And>x. Arr \<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0 \<Longrightarrow>
                 \<guillemotleft>\<lbrace>\<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0\<rbrace> : \<lbrace>Src \<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0\<rbrace> \<rightarrow> \<lbrace>Trg \<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>\<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0\<rbrace> : \<lbrace>Dom \<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0\<rbrace> \<Rightarrow> \<lbrace>Cod \<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0\<rbrace>\<guillemotright>"
        apply (simp add: preserves_src preserves_trg)
        using preserves_src preserves_trg C.objE
        by (metis (full_types) C.obj_def' E.preserves_arr E.preserves_ide in_hhom_def
            ide_in_hom(2))
      show "\<And>x. Arr \<^bold>\<langle>x\<^bold>\<rangle> \<Longrightarrow>
                \<guillemotleft>\<lbrace>\<^bold>\<langle>x\<^bold>\<rangle>\<rbrace> : \<lbrace>Src \<^bold>\<langle>x\<^bold>\<rangle>\<rbrace> \<rightarrow> \<lbrace>Trg \<^bold>\<langle>x\<^bold>\<rangle>\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>\<^bold>\<langle>x\<^bold>\<rangle>\<rbrace> : \<lbrace>Dom \<^bold>\<langle>x\<^bold>\<rangle>\<rbrace> \<Rightarrow> \<lbrace>Cod \<^bold>\<langle>x\<^bold>\<rangle>\<rbrace>\<guillemotright>"
        by (auto simp add: preserves_src preserves_trg)
      show "\<And>t1 t2.
              (Arr t1 \<Longrightarrow> \<guillemotleft>\<lbrace>t1\<rbrace> : \<lbrace>Src t1\<rbrace> \<rightarrow> \<lbrace>Trg t1\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t1\<rbrace> : \<lbrace>Dom t1\<rbrace> \<Rightarrow> \<lbrace>Cod t1\<rbrace>\<guillemotright>) \<Longrightarrow>
              (Arr t2 \<Longrightarrow> \<guillemotleft>\<lbrace>t2\<rbrace> : \<lbrace>Src t2\<rbrace> \<rightarrow> \<lbrace>Trg t2\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t2\<rbrace> : \<lbrace>Dom t2\<rbrace> \<Rightarrow> \<lbrace>Cod t2\<rbrace>\<guillemotright>) \<Longrightarrow>
              Arr (t1 \<^bold>\<star> t2) \<Longrightarrow>
              \<guillemotleft>\<lbrace>t1 \<^bold>\<star> t2\<rbrace> : \<lbrace>Src (t1 \<^bold>\<star> t2)\<rbrace> \<rightarrow> \<lbrace>Trg (t1 \<^bold>\<star> t2)\<rbrace>\<guillemotright> \<and>
              \<guillemotleft>\<lbrace>t1 \<^bold>\<star> t2\<rbrace> : \<lbrace>Dom (t1 \<^bold>\<star> t2)\<rbrace> \<Rightarrow> \<lbrace>Cod (t1 \<^bold>\<star> t2)\<rbrace>\<guillemotright>"
        using hcomp_in_hhom in_hhom_def vconn_implies_hpar(1) vconn_implies_hpar(2) by auto
      show "\<And>t1 t2.
              (Arr t1 \<Longrightarrow> \<guillemotleft>\<lbrace>t1\<rbrace> : \<lbrace>Src t1\<rbrace> \<rightarrow> \<lbrace>Trg t1\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t1\<rbrace> : \<lbrace>Dom t1\<rbrace> \<Rightarrow> \<lbrace>Cod t1\<rbrace>\<guillemotright>) \<Longrightarrow>
              (Arr t2 \<Longrightarrow> \<guillemotleft>\<lbrace>t2\<rbrace> : \<lbrace>Src t2\<rbrace> \<rightarrow> \<lbrace>Trg t2\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t2\<rbrace> : \<lbrace>Dom t2\<rbrace> \<Rightarrow> \<lbrace>Cod t2\<rbrace>\<guillemotright>) \<Longrightarrow>
              Arr (t1 \<^bold>\<cdot> t2) \<Longrightarrow>
              \<guillemotleft>\<lbrace>t1 \<^bold>\<cdot> t2\<rbrace> : \<lbrace>Src (t1 \<^bold>\<cdot> t2)\<rbrace> \<rightarrow> \<lbrace>Trg (t1 \<^bold>\<cdot> t2)\<rbrace>\<guillemotright> \<and>
              \<guillemotleft>\<lbrace>t1 \<^bold>\<cdot> t2\<rbrace> : \<lbrace>Dom (t1 \<^bold>\<cdot> t2)\<rbrace> \<Rightarrow> \<lbrace>Cod (t1 \<^bold>\<cdot> t2)\<rbrace>\<guillemotright>"
        using VSeq_implies_HPar seqI' by auto
      show "\<And>t. (Arr t \<Longrightarrow> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>) \<Longrightarrow>
                Arr \<^bold>\<l>\<^bold>[t\<^bold>] \<Longrightarrow>
                \<guillemotleft>\<lbrace>\<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace> : \<lbrace>Src \<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace> \<rightarrow> \<lbrace>Trg \<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>\<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace> : \<lbrace>Dom \<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace> \<Rightarrow> \<lbrace>Cod \<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace>\<guillemotright>"
      proof (simp add: preserves_src preserves_trg)
        fix t
        assume t: "\<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
        assume 1: "Arr t"
        show "\<guillemotleft>\<ll> \<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<ll> \<lbrace>t\<rbrace> : \<lbrace>Trg t\<rbrace> \<star> \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
        proof -
          have "src (\<ll> \<lbrace>t\<rbrace>) = \<lbrace>Src t\<rbrace>"
            using t 1
            by (metis (no_types, lifting) \<ll>.preserves_cod \<ll>.preserves_reflects_arr arr_cod
                in_hhomE map_simp src_cod)
          moreover have "trg (\<ll> \<lbrace>t\<rbrace>) = \<lbrace>Trg t\<rbrace>"
            using t 1
            by (metis (no_types, lifting) \<ll>.preserves_cod \<ll>.preserves_reflects_arr arr_cod
                in_hhomE map_simp trg_cod)
          moreover have "\<guillemotleft>\<ll> \<lbrace>t\<rbrace> : \<lbrace>Trg t\<rbrace> \<star> \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
            using t 1
            apply (elim conjE in_hhomE)
            by (intro in_homI, auto)
          ultimately show ?thesis by auto
        qed
      qed
      show "\<And>t. (Arr t \<Longrightarrow> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>) \<Longrightarrow>
                Arr \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow>
                \<guillemotleft>\<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> : \<lbrace>Src \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> \<rightarrow> \<lbrace>Trg \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>\<guillemotright> \<and>
                \<guillemotleft>\<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> : \<lbrace>Dom \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> \<Rightarrow> \<lbrace>Cod \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>\<guillemotright>"
      proof (simp add: preserves_src preserves_trg)
        fix t
        assume t: "\<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
        assume 1: "Arr t"
        show "\<guillemotleft>\<ll>'.map \<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and>
              \<guillemotleft>\<ll>'.map \<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Trg t\<rbrace> \<star> \<lbrace>Cod t\<rbrace>\<guillemotright>"
        proof -
          have "src (\<ll>'.map \<lbrace>t\<rbrace>) = \<lbrace>Src t\<rbrace>"
            using t 1 \<ll>'.preserves_dom arr_dom map_simp \<ll>'.preserves_reflects_arr src_dom
            by (metis (no_types, lifting) in_hhomE)
          moreover have "trg (\<ll>'.map \<lbrace>t\<rbrace>) = \<lbrace>Trg t\<rbrace>"
            using t 1 \<ll>'.preserves_dom arr_dom map_simp \<ll>'.preserves_reflects_arr trg_dom
            by (metis (no_types, lifting) in_hhomE)
          moreover have "\<guillemotleft>\<ll>'.map \<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Trg t\<rbrace> \<star> \<lbrace>Cod t\<rbrace>\<guillemotright>"
            using t 1 \<ll>'.preserves_hom
            apply (intro in_homI)
              apply auto[1]
             apply fastforce
            by fastforce
          ultimately show ?thesis by blast
        qed
      qed
      show "\<And>t. (Arr t \<Longrightarrow> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>) \<Longrightarrow>
                 Arr \<^bold>\<r>\<^bold>[t\<^bold>] \<Longrightarrow>
                 \<guillemotleft>\<lbrace>\<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> : \<lbrace>Src \<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> \<rightarrow> \<lbrace>Trg \<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>\<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> : \<lbrace>Dom \<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> \<Rightarrow> \<lbrace>Cod \<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace>\<guillemotright>"
      proof (simp add: preserves_src preserves_trg)
        fix t
        assume t: "\<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
        assume 1: "Arr t"
        show "\<guillemotleft>\<rr> \<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<rr> \<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<star> \<lbrace>Src t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
        proof -
          have "src (\<rr> \<lbrace>t\<rbrace>) = \<lbrace>Src t\<rbrace>"
            using t 1 \<rr>.preserves_cod arr_cod map_simp \<rr>.preserves_reflects_arr src_cod
            by (metis (no_types, lifting) in_hhomE)
          moreover have "trg (\<rr> \<lbrace>t\<rbrace>) = \<lbrace>Trg t\<rbrace>"
            using t 1 \<rr>.preserves_cod arr_cod map_simp \<rr>.preserves_reflects_arr trg_cod
            by (metis (no_types, lifting) in_hhomE)
          moreover have "\<guillemotleft>\<rr> \<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<star> \<lbrace>Src t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
            using t 1 by force
          ultimately show ?thesis by blast
        qed
      qed
      show "\<And>t. (Arr t \<Longrightarrow> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>) \<Longrightarrow>
                 Arr \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow>
                 \<guillemotleft>\<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> : \<lbrace>Src \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> \<rightarrow> \<lbrace>Trg \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>\<guillemotright> \<and>
                 \<guillemotleft>\<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> : \<lbrace>Dom \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> \<Rightarrow> \<lbrace>Cod \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>\<guillemotright>"
      proof (simp add: preserves_src preserves_trg)
        fix t
        assume t: "\<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
        assume 1: "Arr t"
        show "\<guillemotleft>\<rr>'.map \<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and>
              \<guillemotleft>\<rr>'.map \<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace> \<star> \<lbrace>Src t\<rbrace>\<guillemotright>"
        proof -
          have "src (\<rr>'.map \<lbrace>t\<rbrace>) = \<lbrace>Src t\<rbrace>"
            using t 1 \<rr>'.preserves_dom arr_dom map_simp \<rr>'.preserves_reflects_arr src_dom
            by (metis (no_types, lifting) in_hhomE)
          moreover have "trg (\<rr>'.map \<lbrace>t\<rbrace>) = \<lbrace>Trg t\<rbrace>"
            using t 1 \<rr>'.preserves_dom arr_dom map_simp \<rr>'.preserves_reflects_arr trg_dom
            by (metis (no_types, lifting) in_hhomE)
          moreover have "\<guillemotleft>\<rr>'.map \<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace> \<star> \<lbrace>Src t\<rbrace>\<guillemotright>"
            using t 1 src_cod arr_cod \<rr>'.preserves_hom [of "\<lbrace>t\<rbrace>" "\<lbrace>Dom t\<rbrace>" "\<lbrace>Cod t\<rbrace>"]
            apply (elim conjE in_hhomE)
            by (intro in_homI, auto)
          ultimately show ?thesis by blast
        qed
      qed
      show "\<And>t u v.
            (Arr t \<Longrightarrow> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>) \<Longrightarrow>
            (Arr u \<Longrightarrow> \<guillemotleft>\<lbrace>u\<rbrace> : \<lbrace>Src u\<rbrace> \<rightarrow> \<lbrace>Trg u\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>u\<rbrace> : \<lbrace>Dom u\<rbrace> \<Rightarrow> \<lbrace>Cod u\<rbrace>\<guillemotright>) \<Longrightarrow>
            (Arr v \<Longrightarrow> \<guillemotleft>\<lbrace>v\<rbrace> : \<lbrace>Src v\<rbrace> \<rightarrow> \<lbrace>Trg v\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>v\<rbrace> : \<lbrace>Dom v\<rbrace> \<Rightarrow> \<lbrace>Cod v\<rbrace>\<guillemotright>) \<Longrightarrow>
            Arr \<^bold>\<a>\<^bold>[t, u, v\<^bold>] \<Longrightarrow>
            \<guillemotleft>\<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> : \<lbrace>Src \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> \<rightarrow> \<lbrace>Trg \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace>\<guillemotright> \<and>
            \<guillemotleft>\<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> : \<lbrace>Dom \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> \<Rightarrow> \<lbrace>Cod \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace>\<guillemotright>"
      proof (simp add: preserves_src preserves_trg)
        fix t u v
        assume t: "\<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Trg u\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
        assume u: "\<guillemotleft>\<lbrace>u\<rbrace> : \<lbrace>Trg v\<rbrace> \<rightarrow> \<lbrace>Trg u\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>u\<rbrace> : \<lbrace>Dom u\<rbrace> \<Rightarrow> \<lbrace>Cod u\<rbrace>\<guillemotright>"
        assume v: "\<guillemotleft>\<lbrace>v\<rbrace> : \<lbrace>Src v\<rbrace> \<rightarrow> \<lbrace>Trg v\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>v\<rbrace> : \<lbrace>Dom v\<rbrace> \<Rightarrow> \<lbrace>Cod v\<rbrace>\<guillemotright>"
        assume tuv: "Arr t \<and> Arr u \<and> Arr v \<and> Src t = Trg u \<and> Src u = Trg v"
        show "\<guillemotleft>\<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>) : \<lbrace>Src v\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and>
              \<guillemotleft>\<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>) :
                 (\<lbrace>Dom t\<rbrace> \<star> \<lbrace>Dom u\<rbrace>) \<star> \<lbrace>Dom v\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace> \<star> \<lbrace>Cod u\<rbrace> \<star> \<lbrace>Cod v\<rbrace>\<guillemotright>"
        proof -
          have 1: "VVV.in_hom (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)
                                (\<lbrace>Dom t\<rbrace>, \<lbrace>Dom u\<rbrace>, \<lbrace>Dom v\<rbrace>) (\<lbrace>Cod t\<rbrace>, \<lbrace>Cod u\<rbrace>, \<lbrace>Cod v\<rbrace>)"
          proof -
            have "(\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>) \<in>
                    VxVxV.hom (\<lbrace>Dom t\<rbrace>, \<lbrace>Dom u\<rbrace>, \<lbrace>Dom v\<rbrace>) (\<lbrace>Cod t\<rbrace>, \<lbrace>Cod u\<rbrace>, \<lbrace>Cod v\<rbrace>)"
              using t u v tuv by simp
            moreover have "(\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>) \<in>
                             {\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> VV.arr (snd \<tau>\<mu>\<nu>) \<and> 
                                   src (fst \<tau>\<mu>\<nu>) = trg (fst (snd \<tau>\<mu>\<nu>))}"
              using t u v tuv by fastforce
            ultimately show ?thesis
              using VVV.hom_char [of "(\<lbrace>Dom t\<rbrace>, \<lbrace>Dom u\<rbrace>, \<lbrace>Dom v\<rbrace>)" "(\<lbrace>Cod t\<rbrace>, \<lbrace>Cod u\<rbrace>, \<lbrace>Cod v\<rbrace>)"]
              by blast
          qed
          have 4: "VVV.arr (\<lbrace>Dom t\<rbrace>, \<lbrace>Dom u\<rbrace>, \<lbrace>Dom v\<rbrace>)"
            using 1 VVV.ide_dom apply (elim VVV.in_homE) by force
          have 5: "VVV.arr (\<lbrace>Cod t\<rbrace>, \<lbrace>Cod u\<rbrace>, \<lbrace>Cod v\<rbrace>)"
            using 1 VVV.ide_cod apply (elim VVV.in_homE) by force
          have 2: "\<guillemotleft>\<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>) :
                      (\<lbrace>Dom t\<rbrace> \<star> \<lbrace>Dom u\<rbrace>) \<star> \<lbrace>Dom v\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace> \<star> \<lbrace>Cod u\<rbrace> \<star> \<lbrace>Cod v\<rbrace>\<guillemotright>"
            using 1 4 5 HoHV_def HoVH_def \<alpha>_def
                  \<alpha>.preserves_hom [of "(\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)" "(\<lbrace>Dom t\<rbrace>, \<lbrace>Dom u\<rbrace>, \<lbrace>Dom v\<rbrace>)"
                                      "(\<lbrace>Cod t\<rbrace>, \<lbrace>Cod u\<rbrace>, \<lbrace>Cod v\<rbrace>)"]
            by simp
          have 3: "\<guillemotleft>\<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>) : \<lbrace>Src v\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright>"
          proof
            show "arr (\<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>))"
              using 2 by auto
            show "src (\<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)) = \<lbrace>Src v\<rbrace>"
            proof -
              have "src (\<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)) = src ((\<lbrace>Dom t\<rbrace> \<star> \<lbrace>Dom u\<rbrace>) \<star> \<lbrace>Dom v\<rbrace>)"
                using 2 src_dom [of "\<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"] by fastforce
              also have "... = src \<lbrace>Dom v\<rbrace>"
                using 4 VVV.arr_char VV.arr_char by simp
              also have "... = src (dom \<lbrace>v\<rbrace>)"
                using v by auto
              also have "... = \<lbrace>Src v\<rbrace>"
                using v by auto
              finally show ?thesis by auto
            qed
            show "trg (\<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)) = \<lbrace>Trg t\<rbrace>"
            proof -
              have "trg (\<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)) = trg ((\<lbrace>Dom t\<rbrace> \<star> \<lbrace>Dom u\<rbrace>) \<star> \<lbrace>Dom v\<rbrace>)"
                using 2 trg_dom [of "\<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"] by fastforce
              also have "... = trg \<lbrace>Dom t\<rbrace>"
                using 4 VVV.arr_char VV.arr_char by simp
              also have "... = trg (dom \<lbrace>t\<rbrace>)"
                using t by auto
              also have "... = \<lbrace>Trg t\<rbrace>"
                using t by auto
              finally show ?thesis by auto
            qed
          qed
          show ?thesis using 2 3 by simp
        qed
      qed
      show "\<And>t u v.
            (Arr t \<Longrightarrow> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>) \<Longrightarrow>
            (Arr u \<Longrightarrow> \<guillemotleft>\<lbrace>u\<rbrace> : \<lbrace>Src u\<rbrace> \<rightarrow> \<lbrace>Trg u\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>u\<rbrace> : \<lbrace>Dom u\<rbrace> \<Rightarrow> \<lbrace>Cod u\<rbrace>\<guillemotright>) \<Longrightarrow>
            (Arr v \<Longrightarrow> \<guillemotleft>\<lbrace>v\<rbrace> : \<lbrace>Src v\<rbrace> \<rightarrow> \<lbrace>Trg v\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>v\<rbrace> : \<lbrace>Dom v\<rbrace> \<Rightarrow> \<lbrace>Cod v\<rbrace>\<guillemotright>) \<Longrightarrow>
            Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] \<Longrightarrow>
            \<guillemotleft>\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> : \<lbrace>Src \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> \<rightarrow> \<lbrace>Trg \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace>\<guillemotright> \<and>
            \<guillemotleft>\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> : \<lbrace>Dom \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> \<Rightarrow> \<lbrace>Cod \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace>\<guillemotright>"
      proof (simp add: preserves_src preserves_trg)
        fix t u v
        assume t: "\<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Trg u\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
        assume u: "\<guillemotleft>\<lbrace>u\<rbrace> : \<lbrace>Trg v\<rbrace> \<rightarrow> \<lbrace>Trg u\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>u\<rbrace> : \<lbrace>Dom u\<rbrace> \<Rightarrow> \<lbrace>Cod u\<rbrace>\<guillemotright>"
        assume v: "\<guillemotleft>\<lbrace>v\<rbrace> : \<lbrace>Src v\<rbrace> \<rightarrow> \<lbrace>Trg v\<rbrace>\<guillemotright> \<and> \<guillemotleft>\<lbrace>v\<rbrace> : \<lbrace>Dom v\<rbrace> \<Rightarrow> \<lbrace>Cod v\<rbrace>\<guillemotright>"
        assume tuv: "Arr t \<and> Arr u \<and> Arr v \<and> Src t = Trg u \<and> Src u = Trg v"
        show "\<guillemotleft>\<alpha>'.map (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>) : \<lbrace>Src v\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright> \<and>
              \<guillemotleft>\<alpha>'.map (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>) :
                 \<lbrace>Dom t\<rbrace> \<star> \<lbrace>Dom u\<rbrace> \<star> \<lbrace>Dom v\<rbrace> \<Rightarrow> (\<lbrace>Cod t\<rbrace> \<star> \<lbrace>Cod u\<rbrace>) \<star> \<lbrace>Cod v\<rbrace>\<guillemotright>"
        proof -
          have 1: "VVV.in_hom (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)
                                (\<lbrace>Dom t\<rbrace>, \<lbrace>Dom u\<rbrace>, \<lbrace>Dom v\<rbrace>) (\<lbrace>Cod t\<rbrace>, \<lbrace>Cod u\<rbrace>, \<lbrace>Cod v\<rbrace>)"
            using t u v tuv VVV.hom_char VVV.arr_char VV.arr_char VVV.dom_char VVV.cod_char
            apply (elim conjE in_hhomE in_homE)
            apply (intro VVV.in_homI)
            by simp_all
          have 4: "VVV.arr (\<lbrace>Dom t\<rbrace>, \<lbrace>Dom u\<rbrace>, \<lbrace>Dom v\<rbrace>)"
            using "1" VVV.in_hom_char by blast
          have 5: "VVV.arr (\<lbrace>Cod t\<rbrace>, \<lbrace>Cod u\<rbrace>, \<lbrace>Cod v\<rbrace>)"
            using "1" VVV.in_hom_char by blast
          have 2: "\<guillemotleft>\<alpha>'.map (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>) :
                      \<lbrace>Dom t\<rbrace> \<star> \<lbrace>Dom u\<rbrace> \<star> \<lbrace>Dom v\<rbrace> \<Rightarrow> (\<lbrace>Cod t\<rbrace> \<star> \<lbrace>Cod u\<rbrace>) \<star> \<lbrace>Cod v\<rbrace>\<guillemotright>"
            using 1 4 5 HoHV_def HoVH_def \<alpha>'.map_def
                  \<alpha>'.preserves_hom [of "(\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)" "(\<lbrace>Dom t\<rbrace>, \<lbrace>Dom u\<rbrace>, \<lbrace>Dom v\<rbrace>)"
                                       "(\<lbrace>Cod t\<rbrace>, \<lbrace>Cod u\<rbrace>, \<lbrace>Cod v\<rbrace>)"]
            by simp
          have 3: "\<guillemotleft>\<alpha>'.map (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>) : \<lbrace>Src v\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright>"
          proof
            show "arr (\<alpha>'.map (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>))"
              using 2 by auto
            show "src (\<alpha>'.map (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)) = \<lbrace>Src v\<rbrace>"
            proof -
              have "src (\<alpha>'.map (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)) = src (\<lbrace>Dom t\<rbrace> \<star> \<lbrace>Dom u\<rbrace> \<star> \<lbrace>Dom v\<rbrace>)"
                using 2 src_dom [of "\<alpha>'.map (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"] by auto
              also have "... = src \<lbrace>Dom v\<rbrace>"
                using 4 VVV.arr_char VV.arr_char by simp
              also have "... = src (dom \<lbrace>v\<rbrace>)"
                using v by auto
              also have "... = \<lbrace>Src v\<rbrace>"
                using v by auto
              finally show ?thesis by auto
            qed
            show "trg (\<alpha>'.map (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)) = \<lbrace>Trg t\<rbrace>"
            proof -
              have "trg (\<alpha>'.map (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)) = trg (\<lbrace>Dom t\<rbrace> \<star> \<lbrace>Dom u\<rbrace> \<star> \<lbrace>Dom v\<rbrace>)"
                using 2 trg_dom [of "\<alpha>'.map (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"] by auto
              also have "... = trg \<lbrace>Dom t\<rbrace>"
                using 4 VVV.arr_char VV.arr_char hseqI' by simp
              also have "... = trg (dom \<lbrace>t\<rbrace>)"
                using t by auto
              also have "... = \<lbrace>Trg t\<rbrace>"
                using t by auto
              finally show ?thesis by auto
            qed
          qed
          show ?thesis using 2 3 by simp
        qed
      qed
    qed

    lemma eval_in_hom [intro]:
    assumes "Arr t"
    shows "\<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Src t\<rbrace> \<rightarrow> \<lbrace>Trg t\<rbrace>\<guillemotright>" and "\<guillemotleft>\<lbrace>t\<rbrace> : \<lbrace>Dom t\<rbrace> \<Rightarrow> \<lbrace>Cod t\<rbrace>\<guillemotright>"
      using assms eval_in_hom' by simp_all

    (*
     * TODO: It seems to me that the natural useful orientation of these facts is syntax
     * to semantics.  However, having this as the default makes it impossible to do various
     * proofs by simp alone.  This has to be sorted out.  For right now, I am going to include
     * both versions, which will have to be explicitly invoked where needed.
     *)
    lemma eval_simps:
    assumes "Arr f"
    shows "arr \<lbrace>f\<rbrace>" and "\<lbrace>Src f\<rbrace> = src \<lbrace>f\<rbrace>" and "\<lbrace>Trg f\<rbrace> = trg \<lbrace>f\<rbrace>"
    and "\<lbrace>Dom f\<rbrace> = dom \<lbrace>f\<rbrace>" and "\<lbrace>Cod f\<rbrace> = cod \<lbrace>f\<rbrace>"
      using assms eval_in_hom [of f] by auto

    lemma eval_simps':
    assumes "Arr f"
    shows "arr \<lbrace>f\<rbrace>" and "src \<lbrace>f\<rbrace> = \<lbrace>Src f\<rbrace>" and "trg \<lbrace>f\<rbrace> = \<lbrace>Trg f\<rbrace>"
    and "dom \<lbrace>f\<rbrace> = \<lbrace>Dom f\<rbrace>" and "cod \<lbrace>f\<rbrace> = \<lbrace>Cod f\<rbrace>"
      using assms eval_in_hom by auto

    lemma obj_eval_Obj:
    shows "Obj t \<Longrightarrow> obj \<lbrace>t\<rbrace>"
      apply (induct t)
      using obj_def C.obj_def preserves_src apply auto
      by metis

    lemma ide_eval_Ide:
    shows "Ide t \<Longrightarrow> ide \<lbrace>t\<rbrace>"
      by (induct t, auto simp add: eval_simps')

    lemma arr_eval_Arr [simp]:
    assumes "Arr t"
    shows "arr \<lbrace>t\<rbrace>"
      using assms by (simp add: eval_simps')

    (*
     * TODO: The next few results want eval_simps oriented from syntax to semantics.
     *)

    lemma eval_Lunit [simp]:
    assumes "Arr t"
    shows "\<lbrace>\<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace> = \<l>[\<lbrace>Cod t\<rbrace>] \<cdot> (trg \<lbrace>t\<rbrace> \<star> \<lbrace>t\<rbrace>)"
      using assms \<ll>.is_natural_2 \<ll>_ide_simp by (simp add: eval_simps)

    lemma eval_Lunit' [simp]:
    assumes "Arr t"
    shows "\<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = \<l>\<^sup>-\<^sup>1[\<lbrace>Cod t\<rbrace>] \<cdot> \<lbrace>t\<rbrace>"
      using assms \<ll>'.is_natural_2 \<ll>_ide_simp by (simp add: eval_simps)

    lemma eval_Runit [simp]:
    assumes "Arr t"
    shows "\<lbrace>\<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> = \<r>[\<lbrace>Cod t\<rbrace>] \<cdot> (\<lbrace>t\<rbrace> \<star> src \<lbrace>t\<rbrace>)"
      using assms \<rr>.is_natural_2 \<rr>_ide_simp by (simp add: eval_simps)

    lemma eval_Runit' [simp]:
    assumes "Arr t"
    shows "\<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = \<r>\<^sup>-\<^sup>1[\<lbrace>Cod t\<rbrace>] \<cdot> \<lbrace>t\<rbrace>"
      using assms \<rr>'.is_natural_2 \<rr>_ide_simp by (simp add: eval_simps)

    lemma eval_Assoc [simp]:
    assumes "Arr t" and "Arr u" and "Arr v" and "Src t = Trg u" and "Src u = Trg v"
    shows "\<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> = \<alpha> (cod \<lbrace>t\<rbrace>, cod \<lbrace>u\<rbrace>, cod \<lbrace>v\<rbrace>) \<cdot> ((\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace>) \<star> \<lbrace>v\<rbrace>)"
    proof -
      have "\<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> = \<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)" by simp
      also have "... = \<alpha> (VVV.cod (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)) \<cdot> HoHV (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"
        using assms \<alpha>.is_natural_2 [of "(\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"] VVV.arr_char VVV.cod_char
              \<alpha>.is_extensional \<alpha>_def
        by auto
      also have "... = \<alpha> (cod \<lbrace>t\<rbrace>, cod \<lbrace>u\<rbrace>, cod \<lbrace>v\<rbrace>) \<cdot> ((\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace>) \<star> \<lbrace>v\<rbrace>)"
        unfolding HoHV_def \<alpha>_def
        using assms VVV.arr_char VV.arr_char VVV.cod_char \<alpha>.is_extensional
        by auto
      finally show ?thesis by simp
    qed

    lemma eval_Assoc' [simp]:
    assumes "Arr t" and "Arr u" and "Arr v" and "Src t = Trg u" and "Src u = Trg v"
    shows "\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = \<a>\<^sup>-\<^sup>1[cod \<lbrace>t\<rbrace>, cod \<lbrace>u\<rbrace>, cod \<lbrace>v\<rbrace>] \<cdot> (\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace> \<star> \<lbrace>v\<rbrace>)"
    proof -
      have "\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = \<alpha>'.map (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)" by simp
      also have "... = \<alpha>'.map (VVV.cod (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)) \<cdot> HoVH (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"
        using assms \<alpha>'.is_natural_2 [of "(\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"] VVV.arr_char VVV.cod_char
              \<alpha>'.is_extensional
        by simp
      also have "... = \<alpha>'.map (cod \<lbrace>t\<rbrace>, cod \<lbrace>u\<rbrace>, cod \<lbrace>v\<rbrace>) \<cdot> (\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace> \<star> \<lbrace>v\<rbrace>)"
        unfolding HoVH_def
        using assms VVV.arr_char VV.arr_char VVV.cod_char \<alpha>'.is_extensional
        apply simp
        by (metis (no_types, lifting) comp_null(2) hseq_char hseq_char' hcomp_simps(2))
      finally show ?thesis
        using \<a>'_def by simp
    qed

    lemma eval_Lunit_Ide [simp]:
    assumes "Ide t"
    shows "\<lbrace>\<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace> = \<l>[\<lbrace>t\<rbrace>]"
      using assms \<ll>_ide_simp ide_eval_Ide by simp

    lemma eval_Lunit'_Ide [simp]:
    assumes "Ide t"
    shows "\<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = \<l>\<^sup>-\<^sup>1[\<lbrace>t\<rbrace>]"
      using assms \<ll>_ide_simp ide_eval_Ide by simp

    lemma eval_Runit_Ide [simp]:
    assumes "Ide t"
    shows "\<lbrace>\<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> = \<r>[\<lbrace>t\<rbrace>]"
      using assms \<rr>_ide_simp ide_eval_Ide by simp

    lemma eval_Runit'_Ide [simp]:
    assumes "Ide t"
    shows "\<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = \<r>\<^sup>-\<^sup>1[\<lbrace>t\<rbrace>]"
      using assms \<rr>_ide_simp ide_eval_Ide by simp

    lemma eval_Assoc_Ide [simp]:
    assumes "Ide t" and "Ide u" and "Ide v" and "Src t = Trg u" and "Src u = Trg v"
    shows "\<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> = \<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"
      using assms by simp

    lemma eval_Assoc'_Ide [simp]:
    assumes "Ide t" and "Ide u" and "Ide v" and "Src t = Trg u" and "Src u = Trg v"
    shows "\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = \<a>\<^sup>-\<^sup>1[\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>]"
      using assms \<a>'_def by simp

    lemma iso_eval_Can:
    shows "Can t \<Longrightarrow> iso \<lbrace>t\<rbrace>"
    proof (induct t; simp add: fsts.intros snds.intros)
      show "\<And>x. C.obj x \<Longrightarrow> iso (E x)" by auto
      show "\<And>t1 t2. \<lbrakk> iso \<lbrace>t1\<rbrace>; iso \<lbrace>t2\<rbrace>; Can t1 \<and> Can t2 \<and> Src t1 = Trg t2 \<rbrakk> \<Longrightarrow>
                      iso (\<lbrace>t1\<rbrace> \<star> \<lbrace>t2\<rbrace>)"
        using Can_implies_Arr by (simp add: eval_simps')
      show "\<And>t1 t2. \<lbrakk> iso \<lbrace>t1\<rbrace>; iso \<lbrace>t2\<rbrace>; Can t1 \<and> Can t2 \<and> Dom t1 = Cod t2 \<rbrakk> \<Longrightarrow>
                      iso (\<lbrace>t1\<rbrace> \<cdot> \<lbrace>t2\<rbrace>)"
        using Can_implies_Arr isos_compose by (simp add: eval_simps')
      show "\<And>t. \<lbrakk> iso \<lbrace>t\<rbrace>; Can t \<rbrakk> \<Longrightarrow> iso (\<ll> \<lbrace>t\<rbrace>)"
        using \<ll>.preserves_iso by auto
      show "\<And>t. \<lbrakk> iso \<lbrace>t\<rbrace>; Can t \<rbrakk> \<Longrightarrow> iso (\<ll>'.map \<lbrace>t\<rbrace>)"
        using \<ll>'.preserves_iso by simp
      show "\<And>t. \<lbrakk> iso \<lbrace>t\<rbrace>; Can t \<rbrakk> \<Longrightarrow> iso (\<rr> \<lbrace>t\<rbrace>)"
        using \<rr>.preserves_iso by auto
      show "\<And>t. \<lbrakk> iso \<lbrace>t\<rbrace>; Can t \<rbrakk> \<Longrightarrow> iso (\<rr>'.map \<lbrace>t\<rbrace>)"
        using \<rr>'.preserves_iso by simp
      fix t1 t2 t3
      assume t1: "iso \<lbrace>t1\<rbrace>" and t2: "iso \<lbrace>t2\<rbrace>" and t3: "iso \<lbrace>t3\<rbrace>"
      assume 1: "Can t1 \<and> Can t2 \<and> Can t3 \<and> Src t1 = Trg t2 \<and> Src t2 = Trg t3"
      have 2: "VVV.iso (\<lbrace>t1\<rbrace>, \<lbrace>t2\<rbrace>, \<lbrace>t3\<rbrace>)"
      proof -
        have 3: "VxVxV.iso (\<lbrace>t1\<rbrace>, \<lbrace>t2\<rbrace>, \<lbrace>t3\<rbrace>)"
          using t1 t2 t3 Can_implies_Arr VxVxV.iso_char VxV.iso_char by simp
        moreover have "VVV.arr (VxVxV.inv (\<lbrace>t1\<rbrace>, \<lbrace>t2\<rbrace>, \<lbrace>t3\<rbrace>))"
        proof -
          have "VxVxV.inv (\<lbrace>t1\<rbrace>, \<lbrace>t2\<rbrace>, \<lbrace>t3\<rbrace>) = (inv \<lbrace>t1\<rbrace>, inv \<lbrace>t2\<rbrace>, inv \<lbrace>t3\<rbrace>)"
            using t1 t2 t3 3 by simp
          thus ?thesis
            using t1 t2 t3 1 Can_implies_Arr VVV.arr_char VV.arr_char
            by (simp add: eval_simps')
        qed
        ultimately show ?thesis
          using t1 t2 t3 1 Can_implies_Arr VVV.iso_char VVV.arr_char
          by (auto simp add: eval_simps')
      qed
      show "iso (\<alpha> (\<lbrace>t1\<rbrace>, \<lbrace>t2\<rbrace>, \<lbrace>t3\<rbrace>))"
        using 2 \<alpha>_def \<alpha>.preserves_iso by auto
      show "iso (\<alpha>'.map (\<lbrace>t1\<rbrace>, \<lbrace>t2\<rbrace>, \<lbrace>t3\<rbrace>))"
        using 2 \<alpha>'.preserves_iso by simp
    qed

    lemma eval_Inv_Can:
    shows "Can t \<Longrightarrow> \<lbrace>Inv t\<rbrace> = inv \<lbrace>t\<rbrace>"
    proof (induct t)
      show "\<And>x. Can \<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0 \<Longrightarrow> \<lbrace>Inv \<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0\<rbrace> = inv \<lbrace>\<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0\<rbrace>" by auto
      show "\<And>x. Can \<^bold>\<langle>x\<^bold>\<rangle> \<Longrightarrow> \<lbrace>Inv \<^bold>\<langle>x\<^bold>\<rangle>\<rbrace> = inv \<lbrace>\<^bold>\<langle>x\<^bold>\<rangle>\<rbrace>" by simp
      show "\<And>t1 t2. (Can t1 \<Longrightarrow> \<lbrace>Inv t1\<rbrace> = inv \<lbrace>t1\<rbrace>) \<Longrightarrow>
                    (Can t2 \<Longrightarrow> \<lbrace>Inv t2\<rbrace> = inv \<lbrace>t2\<rbrace>) \<Longrightarrow>
                     Can (t1 \<^bold>\<star> t2) \<Longrightarrow> \<lbrace>Inv (t1 \<^bold>\<star> t2)\<rbrace> = inv \<lbrace>t1 \<^bold>\<star> t2\<rbrace>"
        using iso_eval_Can Can_implies_Arr
        by (simp add: eval_simps')
      show "\<And>t1 t2. (Can t1 \<Longrightarrow> \<lbrace>Inv t1\<rbrace> = inv \<lbrace>t1\<rbrace>) \<Longrightarrow>
                    (Can t2 \<Longrightarrow> \<lbrace>Inv t2\<rbrace> = inv \<lbrace>t2\<rbrace>) \<Longrightarrow>
                     Can (t1 \<^bold>\<cdot> t2) \<Longrightarrow> \<lbrace>Inv (t1 \<^bold>\<cdot> t2)\<rbrace> = inv \<lbrace>t1 \<^bold>\<cdot> t2\<rbrace>"
        using iso_eval_Can inv_comp Can_implies_Arr
        by (simp add: eval_simps')
      fix t
      assume I: "Can t \<Longrightarrow> \<lbrace>Inv t\<rbrace> = inv \<lbrace>t\<rbrace>"
      show "Can \<^bold>\<l>\<^bold>[t\<^bold>] \<Longrightarrow> \<lbrace>Inv \<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace> = inv \<lbrace>\<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace>"
      proof -
        assume t: "Can \<^bold>\<l>\<^bold>[t\<^bold>]"
        have "\<lbrace>Inv \<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace> = \<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Inv t\<^bold>]\<rbrace>" by simp
        also have "... = \<ll>'.map (inv \<lbrace>t\<rbrace>)"
          using t I by simp
        also have "... = \<ll>'.map (cod (inv \<lbrace>t\<rbrace>)) \<cdot> inv \<lbrace>t\<rbrace>"
          using t \<ll>'.is_natural_2 iso_inv_iso iso_eval_Can iso_is_arr
          by (metis (no_types, lifting) Can.simps(5) map_simp)
        also have "... = inv (\<lbrace>t\<rbrace> \<cdot> \<ll> (dom \<lbrace>t\<rbrace>))"
        proof -
          have 1: "iso \<lbrace>t\<rbrace>" using t iso_eval_Can by simp
          moreover have "iso (\<ll> (dom \<lbrace>t\<rbrace>))"
            using t 1 \<ll>.components_are_iso ide_dom by blast
          moreover have "seq \<lbrace>t\<rbrace> (\<ll> (dom \<lbrace>t\<rbrace>))"
            using t 1 iso_is_arr by auto
          ultimately show ?thesis
            using t 1 inv_comp by auto
        qed
        also have "... = inv \<lbrace>\<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace>"
          using t iso_eval_Can \<ll>_ide_simp lunit_naturality Can_implies_Arr eval_Lunit
          by (auto simp add: eval_simps)
        finally show ?thesis by blast
      qed
      show "Can \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> \<lbrace>Inv \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = inv \<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>"
      proof -
        assume t: "Can (Lunit' t)"
        have "\<lbrace>Inv (Lunit' t)\<rbrace> = \<lbrace>Lunit (Inv t)\<rbrace>" by simp
        also have "... = \<ll> (inv \<lbrace>t\<rbrace>)"
          using t I by simp
        also have "... = inv \<lbrace>t\<rbrace> \<cdot> \<ll> (dom (inv \<lbrace>t\<rbrace>))"
          using t \<ll>.is_natural_1 iso_inv_iso iso_eval_Can iso_is_arr
          by (metis (no_types, lifting) Can.simps(6) map_simp)
        also have "... = inv (\<ll>'.map (cod \<lbrace>t\<rbrace>) \<cdot> \<lbrace>t\<rbrace>)"
        proof -
          have 1: "iso \<lbrace>t\<rbrace>" using t iso_eval_Can by simp
          moreover have "iso (\<ll>'.map (cod \<lbrace>t\<rbrace>))"
            using t 1 \<ll>'.components_are_iso ide_cod by blast
          moreover have "seq (\<ll>'.map (cod \<lbrace>t\<rbrace>)) \<lbrace>t\<rbrace>"
            using t 1 iso_is_arr by auto
          ultimately show ?thesis
            using t 1 inv_comp by auto
        qed
        also have "... = inv \<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>"
          using t \<ll>'.is_natural_2 iso_eval_Can iso_is_arr by force
        finally show ?thesis by auto
      qed
      show "Can \<^bold>\<r>\<^bold>[t\<^bold>] \<Longrightarrow> \<lbrace>Inv \<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> = inv \<lbrace>\<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace>"
      proof -
        assume t: "Can \<^bold>\<r>\<^bold>[t\<^bold>]"
        have "\<lbrace>Inv \<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> = \<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Inv t\<^bold>]\<rbrace>" by simp
        also have "... = \<rr>'.map (inv \<lbrace>t\<rbrace>)"
          using t I by simp
        also have "... = \<rr>'.map (cod (inv \<lbrace>t\<rbrace>)) \<cdot> inv \<lbrace>t\<rbrace>"
          using t \<rr>'.is_natural_2 map_simp iso_inv_iso iso_eval_Can iso_is_arr
          by (metis (no_types, lifting) Can.simps(7))
        also have "... = inv (\<lbrace>t\<rbrace> \<cdot> \<rr> (dom \<lbrace>t\<rbrace>))"
        proof -
          have 1: "iso \<lbrace>t\<rbrace>" using t iso_eval_Can by simp
          moreover have "iso (\<rr> (dom \<lbrace>t\<rbrace>))"
            using t 1 \<rr>.components_are_iso ide_dom by blast
          moreover have "seq \<lbrace>t\<rbrace> (\<rr> (dom \<lbrace>t\<rbrace>))"
            using t 1 iso_is_arr by simp
          ultimately show ?thesis
            using t 1 inv_comp by auto
        qed
        also have "... = inv \<lbrace>\<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace>"
          using t \<rr>_ide_simp iso_eval_Can runit_naturality Can_implies_Arr eval_Runit
          by (auto simp add: eval_simps)
        finally show ?thesis by blast
      qed
      show "Can \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> \<lbrace>Inv \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = inv \<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>"
      proof -
        assume t: "Can \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
        have "\<lbrace>Inv \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = \<lbrace>\<^bold>\<r>\<^bold>[Inv t\<^bold>]\<rbrace>"
          by simp
        also have "... = \<rr> (inv \<lbrace>t\<rbrace>)"
          using t I by simp
        also have "... = inv \<lbrace>t\<rbrace> \<cdot> \<rr> (dom (inv \<lbrace>t\<rbrace>))"
          using t \<rr>.is_natural_1 map_simp iso_inv_iso iso_eval_Can iso_is_arr
          by (metis (no_types, lifting) Can.simps(8))
        also have "... = inv (\<rr>'.map (cod \<lbrace>t\<rbrace>) \<cdot> \<lbrace>t\<rbrace>)"
        proof -
          have 1: "iso \<lbrace>t\<rbrace>" using t iso_eval_Can by simp
          moreover have "iso (\<rr>'.map (cod \<lbrace>t\<rbrace>))"
            using t 1 \<rr>'.components_are_iso ide_cod by blast
          moreover have "seq (\<rr>'.map (cod \<lbrace>t\<rbrace>)) \<lbrace>t\<rbrace>"
            using t 1 iso_is_arr by auto
          ultimately show ?thesis
            using t 1 inv_comp by auto
        qed
        also have "... = inv \<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace>"
          using t \<rr>'.is_natural_2 iso_eval_Can iso_is_arr by auto
        finally show ?thesis by auto
      qed
      next
      fix t u v
      assume I1: "Can t \<Longrightarrow> \<lbrace>Inv t\<rbrace> = inv \<lbrace>t\<rbrace>"
      assume I2: "Can u \<Longrightarrow> \<lbrace>Inv u\<rbrace> = inv \<lbrace>u\<rbrace>"
      assume I3: "Can v \<Longrightarrow> \<lbrace>Inv v\<rbrace> = inv \<lbrace>v\<rbrace>"
      show "Can \<^bold>\<a>\<^bold>[t, u, v\<^bold>] \<Longrightarrow> \<lbrace>Inv \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> = inv \<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace>"
      proof -
        assume "Can \<^bold>\<a>\<^bold>[t, u, v\<^bold>]"
        hence tuv: "Can t \<and> Can u \<and> Can v \<and> Src t = Trg u \<and> Src u = Trg v" by simp
        have "\<lbrace>Inv \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> = \<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Inv t, Inv u, Inv v\<^bold>]\<rbrace>" by simp
        also have "... = \<a>\<^sup>-\<^sup>1[dom \<lbrace>t\<rbrace>, dom \<lbrace>u\<rbrace>, dom \<lbrace>v\<rbrace>] \<cdot> (inv \<lbrace>t\<rbrace> \<star> inv \<lbrace>u\<rbrace> \<star> inv \<lbrace>v\<rbrace>)"
          using tuv I1 I2 I3 eval_in_hom \<alpha>'.map_ide_simp inv_in_hom iso_eval_Can assoc'_naturality
                Can_implies_Arr Src_Inv Trg_Inv eval_Assoc' Dom_Inv Can_Inv cod_inv
          by presburger
        also have "... = inv ((\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace> \<star> \<lbrace>v\<rbrace>) \<cdot> \<alpha> (dom \<lbrace>t\<rbrace>, dom \<lbrace>u\<rbrace>, dom \<lbrace>v\<rbrace>))"
          using tuv iso_eval_Can Can_implies_Arr eval_simps'(2) eval_simps'(3) \<alpha>_def
          by (simp add: inv_comp)
        also have "... = inv (\<alpha> (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>))"
          using tuv Can_implies_Arr \<alpha>_def
          by (metis assoc_is_natural_1 arr_eval_Arr eval_simps'(2) eval_simps'(3) fst_conv snd_conv)
        also have "... = inv \<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace>" by simp
        finally show ?thesis by blast
      qed
      show "Can \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] \<Longrightarrow> \<lbrace>Inv \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = inv \<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace>"
      proof -
        assume tuv: "Can \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]"
        have t: "Can t" using tuv by simp
        have u: "Can u" using tuv by simp
        have v: "Can v" using tuv by simp
        have "\<lbrace>Inv \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = \<lbrace>\<^bold>\<a>\<^bold>[Inv t, Inv u, Inv v\<^bold>]\<rbrace>" by simp
        also have "... = (inv \<lbrace>t\<rbrace> \<star> inv \<lbrace>u\<rbrace> \<star> inv \<lbrace>v\<rbrace>) \<cdot> \<alpha> (cod \<lbrace>t\<rbrace>, cod \<lbrace>u\<rbrace>, cod \<lbrace>v\<rbrace>)"
          using \<alpha>_def tuv I1 I2 I3 iso_eval_Can Can_implies_Arr eval_simps'(2) eval_simps'(3)
          apply simp
          using assoc_is_natural_1 arr_inv dom_inv src_inv trg_inv by presburger
        also have "... = inv (\<a>\<^sup>-\<^sup>1[cod \<lbrace>t\<rbrace>, cod \<lbrace>u\<rbrace>, cod \<lbrace>v\<rbrace>] \<cdot> (\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace> \<star> \<lbrace>v\<rbrace>))"
          using tuv inv_comp [of "\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace> \<star> \<lbrace>v\<rbrace>" "\<a>\<^sup>-\<^sup>1[cod \<lbrace>t\<rbrace>, cod \<lbrace>u\<rbrace>, cod \<lbrace>v\<rbrace>]"]
                Can_implies_Arr inv_inv iso_assoc iso_inv_iso \<alpha>_def
          by (simp add: eval_simps'(2) eval_simps'(3) iso_eval_Can)
        also have 1: "... = inv (((\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace>) \<star> \<lbrace>v\<rbrace>) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<lbrace>t\<rbrace>, dom \<lbrace>u\<rbrace>, dom \<lbrace>v\<rbrace>])"
          using tuv assoc'_naturality [of "\<lbrace>t\<rbrace>" "\<lbrace>u\<rbrace>" "\<lbrace>v\<rbrace>"] Can_implies_Arr
                eval_simps'(2) eval_simps'(3)
          by simp
        also have "... = inv \<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace>"
          using tuv 1 Can_implies_Arr eval_Assoc' by auto
        finally show ?thesis by blast
      qed
    qed

    lemma eval_VcompNml:
    assumes "Nml t" and "Nml u" and "VSeq t u"
    shows "\<lbrace>t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<rbrace> = \<lbrace>t\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
    proof -
      have "\<And>u. \<lbrakk> Nml t; Nml u; VSeq t u \<rbrakk> \<Longrightarrow> \<lbrace>t \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<rbrace> = \<lbrace>t\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
      proof (induct t, simp_all add: eval_simps)
        fix u a
        assume u: "Nml u"
        assume 1: "Arr u \<and> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 = Cod u"
        show "\<lbrace>u\<rbrace> = cod \<lbrace>u\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
          using 1 comp_cod_arr by simp
        next
        fix u f
        assume u: "Nml u"
        assume f: "C.arr f"
        assume 1: "Arr u \<and> \<^bold>\<langle>C.dom f\<^bold>\<rangle> = Cod u"
        show "\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<rbrace> = E f \<cdot> \<lbrace>u\<rbrace>"
          using f u 1 preserves_comp_2 by (cases u; simp)
        next
        fix u v w
        assume I1: "\<And>u. \<lbrakk> Nml v; Nml u; Arr u \<and> Dom v = Cod u \<rbrakk> \<Longrightarrow> \<lbrace>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<rbrace> = \<lbrace>v\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
        assume I2: "\<And>u. \<lbrakk> Nml w; Nml u; Arr u \<and> Dom w = Cod u \<rbrakk> \<Longrightarrow> \<lbrace>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<rbrace> = \<lbrace>w\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
        assume vw: "Nml (v \<^bold>\<star> w)"
        have v: "Nml v \<and> v = Prim (un_Prim v)"
          using vw by (simp add: Nml_HcompD)
        have w: "Nml w"
          using vw by (simp add: Nml_HcompD)
        assume u: "Nml u"
        assume 1: "Arr v \<and> Arr w \<and> Src v = Trg w \<and> Arr u \<and> Dom v \<^bold>\<star> Dom w = Cod u"
        show "\<lbrace>(v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> u\<rbrace> = (\<lbrace>v\<rbrace> \<star> \<lbrace>w\<rbrace>) \<cdot> \<lbrace>u\<rbrace>"
          using u 1 HcompNml_in_Hom apply (cases u, simp_all)
        proof -
          fix x y
          assume 3: "u = x \<^bold>\<star> y"
          have x: "Nml x"
            using u 1 3 Nml_HcompD by simp
          have y: "Nml y"
            using u x 1 3 Nml_HcompD by simp
          assume 4: "Arr v \<and> Arr w \<and> Src v = Trg w \<and> Dom v = Cod x \<and> Dom w = Cod y"
          have "\<lbrace>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x\<rbrace> \<star> \<lbrace>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y\<rbrace> = \<lbrace>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x \<^bold>\<star> w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y\<rbrace>"
            using v w x y 4 HcompNml_in_Hom by simp
          moreover have "... = \<lbrace>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x\<rbrace> \<star> \<lbrace>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y\<rbrace>" by simp
          moreover have "... = \<lbrace>v\<rbrace> \<cdot> \<lbrace>x\<rbrace> \<star> \<lbrace>w\<rbrace> \<cdot> \<lbrace>y\<rbrace>"
            using v w x y 4 I1 [of x] I2 [of y] Nml_implies_Arr by simp
          moreover have "... = (\<lbrace>v\<rbrace> \<star> \<lbrace>w\<rbrace>) \<cdot> (\<lbrace>x\<rbrace> \<star> \<lbrace>y\<rbrace>)"
            using v w x y 4 Nml_implies_Arr interchange [of "\<lbrace>v\<rbrace>" "\<lbrace>x\<rbrace>" "\<lbrace>w\<rbrace>" "\<lbrace>y\<rbrace>"]
            by (simp add: eval_simps')
          ultimately have "\<lbrace>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x\<rbrace> \<star> \<lbrace>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y\<rbrace> = (\<lbrace>v\<rbrace> \<star> \<lbrace>w\<rbrace>) \<cdot> (\<lbrace>x\<rbrace> \<star> \<lbrace>y\<rbrace>)" by presburger
          moreover have "arr \<lbrace>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x\<rbrace> \<and> arr \<lbrace>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y\<rbrace>"
            using v w x y 4 VcompNml_in_Hom by simp
          ultimately show "\<lbrace>v \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> x\<rbrace> \<star> \<lbrace>w \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> y\<rbrace> = (\<lbrace>v\<rbrace> \<star> \<lbrace>w\<rbrace>) \<cdot> (\<lbrace>x\<rbrace> \<star> \<lbrace>y\<rbrace>)"
            by simp
        qed
      qed
      thus ?thesis using assms by blast
    qed

    lemma eval_red_Hcomp:
    assumes "Ide a" and "Ide b"
    shows "\<lbrace>(a \<^bold>\<star> b)\<^bold>\<down>\<rbrace> = \<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>a\<^bold>\<down>\<rbrace> \<star> \<lbrace>b\<^bold>\<down>\<rbrace>)"
    proof -
      have "Nml (a \<^bold>\<star> b) \<Longrightarrow> ?thesis"
      proof -
        assume 1: "Nml (a \<^bold>\<star> b)"
        hence 2: "Nml a \<and> Nml b \<and> Src a = Trg b"
          using Nml_HcompD(3-4,7) by simp
        have "\<lbrace>(a \<^bold>\<star> b)\<^bold>\<down>\<rbrace> = \<lbrace>a\<rbrace> \<star> \<lbrace>b\<rbrace>"
          using 1 Nml_HcompD by simp
        also have "... = \<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>a\<^bold>\<down>\<rbrace> \<star> \<lbrace>b\<^bold>\<down>\<rbrace>)"
          using assms 1 2 ide_eval_Ide Nmlize_in_Hom red2_Nml Nmlize_Nml
          by (simp add: eval_simps')
        finally show ?thesis by simp
      qed
      moreover have "\<not> Nml (a \<^bold>\<star> b) \<Longrightarrow> ?thesis"
        using assms Can_red2 by (simp add: Can_red(1) iso_eval_Can)
      ultimately show ?thesis by blast
    qed

    (* TODO: Would the following still be useful if \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 is replaced by Src t? *)
    lemma eval_red2_Nml_Prim\<^sub>0:
    assumes "Ide t" and "Nml t" and "Src t = \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0"
    shows "\<lbrace>t \<^bold>\<Down> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0\<rbrace> = \<r>[\<lbrace>t\<rbrace>]"
      using assms \<rr>_ide_simp
      apply (cases t)
               apply simp_all
    proof -
      show "C.obj a \<Longrightarrow> t = \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<Longrightarrow> \<ll> (E a) = \<r>[E a]"
        using unitor_coincidence obj_eval_Obj [of t] \<ll>_ide_simp by auto
      show "\<And>b c. Ide b \<and> Ide c \<and> Src b = Trg c \<Longrightarrow> \<rr> (\<lbrace>b\<rbrace> \<star> \<lbrace>c\<rbrace>) = \<r>[\<lbrace>b\<rbrace> \<star> \<lbrace>c\<rbrace>]"
        using \<rr>_ide_simp by (simp add: eval_simps' ide_eval_Ide)
    qed

  end

  text \<open>
    Most of the time when we interpret the @{locale evaluation_map} locale, we are evaluating
    terms formed from the arrows in a bicategory as arrows of the bicategory itself.
    The following locale streamlines that use case.
  \<close>

  locale self_evaluation_map =
    bicategory
  begin

    sublocale bicategorical_language V src trg ..

    sublocale evaluation_map V src trg V H \<a> \<i> src trg \<open>\<lambda>\<mu>. if arr \<mu> then \<mu> else null\<close>
      using src.is_extensional trg.is_extensional
      by (unfold_locales, auto)

    notation eval ("\<lbrace>_\<rbrace>")
    notation Nmlize ("\<^bold>\<lfloor>_\<^bold>\<rfloor>")

  end

  subsection "Coherence"

  text \<open>
    We define an individual term to be \emph{coherent} if it commutes, up to evaluation,
    with the reductions of its domain and codomain.  We then formulate the coherence theorem
    as the statement ``every formal arrow is coherent''.  Because reductions evaluate
    to isomorphisms, this implies the standard version of coherence, which says that
    ``parallel canonical terms have equal evaluations''.
  \<close>

  context evaluation_map
  begin

    abbreviation coherent
    where "coherent t \<equiv> \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t\<rbrace> = \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>"

    lemma Nml_implies_coherent:
    assumes "Nml t"
    shows "coherent t"
      using assms Nml_implies_Arr Ide_Dom Ide_Cod Nml_Dom Nml_Cod Nmlize_Nml red_Nml
      by (metis Dom_Cod VcompNml_Cod_Nml arr_eval_Arr comp_arr_dom eval_VcompNml
          eval_simps(4))

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
        using assms red_in_Hom Ide_Cod Can_red iso_eval_Can comp_cod_arr
        by (simp add: comp_inv_arr' eval_simps'(4) eval_simps'(5))
      finally show "\<lbrace>t\<rbrace> = inv \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>"
        by presburger
      next
      assume 1: "\<lbrace>t\<rbrace> = inv \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>"
      hence "\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t\<rbrace> = \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> inv \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>" by simp
      also have "... = (\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> inv \<lbrace>Cod t\<^bold>\<down>\<rbrace>) \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>"
        using comp_assoc by simp
      also have "... = \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>"
      proof -
        have "\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> inv \<lbrace>Cod t\<^bold>\<down>\<rbrace> = cod \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>"
          using assms red_in_Hom Ide_Cod Can_red iso_eval_Can
                inv_is_inverse Nmlize_in_Hom comp_arr_inv
          by (simp add: eval_simps')
        thus ?thesis
          using assms red_in_Hom Ide_Cod Can_red iso_eval_Can
                Ide_Dom Nmlize_in_Hom comp_cod_arr
          by (auto simp add: eval_simps')
      qed
      finally show "coherent t" by blast
    qed

    lemma coherent_iff_coherent_Inv:
    assumes "Can t"
    shows "coherent t \<longleftrightarrow> coherent (Inv t)"
    proof
      have 1: "\<And>t. Can t \<Longrightarrow> coherent t \<Longrightarrow> coherent (Inv t)"
      proof -
        fix t
        assume "Can t"
        hence t: "Can t \<and> Arr t \<and> Ide (Dom t) \<and> Ide (Cod t) \<and>
                  arr \<lbrace>t\<rbrace> \<and> iso \<lbrace>t\<rbrace> \<and> inverse_arrows \<lbrace>t\<rbrace> (inv \<lbrace>t\<rbrace>) \<and>
                  Can \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> Arr \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> arr \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<and> iso \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<and> \<^bold>\<lfloor>t\<^bold>\<rfloor> \<in> VHom \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<and>
                  inverse_arrows \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> (inv \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>) \<and> Inv t \<in> VHom (Cod t) (Dom t)"
          using assms Can_implies_Arr Ide_Dom Ide_Cod iso_eval_Can inv_is_inverse
                Nmlize_in_Hom Can_Nmlize_Can Inv_in_Hom
          by simp
        assume coh: "coherent t"
        have "\<lbrace>Cod (Inv t)\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Inv t\<rbrace> = (inv \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>) \<cdot> \<lbrace>Cod (Inv t)\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Inv t\<rbrace>"
          using t comp_inv_arr red_in_Hom
                comp_cod_arr [of "\<lbrace>Cod (Inv t)\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>Inv t\<rbrace>" "inv \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>"]
          by (auto simp add: eval_simps')
        also have "... = inv \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace> \<cdot> inv \<lbrace>t\<rbrace>"
          using t eval_Inv_Can comp_assoc by auto
        also have "... = inv \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom t\<^bold>\<down>\<rbrace>) \<cdot> inv \<lbrace>t\<rbrace>"
          using comp_assoc by simp
        also have "... = inv \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t\<rbrace>) \<cdot> inv \<lbrace>t\<rbrace>"
          using t coh by simp
        also have "... = inv \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t\<rbrace> \<cdot> inv \<lbrace>t\<rbrace>"
          using comp_assoc by simp
        also have "... = \<lbrace>\<^bold>\<lfloor>Inv t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom (Inv t)\<^bold>\<down>\<rbrace>"
        proof -
          have "\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t\<rbrace> \<cdot> inv \<lbrace>t\<rbrace> = \<lbrace>Dom (Inv t)\<^bold>\<down>\<rbrace>"
            using t eval_Inv_Can red_in_Hom comp_arr_inv comp_arr_dom
            by (simp add: eval_simps')
          thus ?thesis
            using t Nmlize_Inv eval_Inv_Can by simp
        qed
        finally show "coherent (Inv t)" by blast
      qed
      show "coherent t \<Longrightarrow> coherent (Inv t)" using assms 1 by simp
      show "coherent (Inv t) \<Longrightarrow> coherent t"
      proof -
        assume "coherent (Inv t)"
        hence "coherent (Inv (Inv t))"
          using assms 1 Can_Inv by blast
        thus ?thesis using assms by simp
      qed
    qed

    text \<open>
      The next two facts are trivially proved by the simplifier, so formal named facts
      are not really necessary, but we include them for logical completeness of the
      following development, which proves coherence by structural induction.
    \<close>

    lemma coherent_Prim\<^sub>0:
    assumes "C.obj a"
    shows "coherent \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0"
      by simp

    lemma coherent_Prim:
    assumes "Arr \<^bold>\<langle>f\<^bold>\<rangle>"
    shows "coherent \<^bold>\<langle>f\<^bold>\<rangle>"
      using assms by simp

    lemma coherent_Lunit_Ide:
    assumes "Ide t"
    shows "coherent \<^bold>\<l>\<^bold>[t\<^bold>]"
    proof -
      have t: "Ide t \<and> Arr t \<and> Dom t = t \<and> Cod t = t \<and>
               ide \<lbrace>t\<rbrace> \<and> ide \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<and> \<lbrace>t\<^bold>\<down>\<rbrace> \<in> hom \<lbrace>t\<rbrace> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>"
        using assms Ide_in_Hom Ide_Nmlize_Ide
              red_in_Hom eval_in_hom ide_eval_Ide
        by force
      have 1: "Obj (Trg t)" using t by auto
      have "\<lbrace>Cod \<^bold>\<l>\<^bold>[t\<^bold>]\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>\<^bold>\<l>\<^bold>[t\<^bold>]\<rbrace> = \<l>[\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>] \<cdot> (\<lbrace>Trg t\<rbrace> \<star> \<lbrace>t\<^bold>\<down>\<rbrace>)"
        using t \<ll>_ide_simp lunit_naturality [of "\<lbrace>t\<^bold>\<down>\<rbrace>"] red_in_Hom
        by (simp add: eval_simps')
      also have "... = \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<l>[\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>] \<cdot> (\<lbrace>Trg t\<rbrace> \<star> \<lbrace>t\<^bold>\<down>\<rbrace>)"
         using t 1 lunit_in_hom Nmlize_in_Hom ide_eval_Ide red_in_Hom comp_cod_arr
         by (auto simp add: eval_simps')
      also have "... = \<lbrace>\<^bold>\<lfloor>\<^bold>\<l>\<^bold>[t\<^bold>]\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom \<^bold>\<l>\<^bold>[t\<^bold>]\<^bold>\<down>\<rbrace>"
        using 1 t Nml_Trg \<ll>_ide_simp by (cases "Trg t"; simp)
      finally show ?thesis by simp
    qed
      
    text \<open>
      Unlike many of the other results, the next one was not quite so straightforward to adapt
      from @{session \<open>MonoidalCategory\<close>}.
    \<close>

    lemma coherent_Runit_Ide:
    assumes "Ide t"
    shows "coherent \<^bold>\<r>\<^bold>[t\<^bold>]"
    proof -
      have t: "Ide t \<and> Arr t \<and> Dom t = t \<and> Cod t = t \<and>
               ide \<lbrace>t\<rbrace> \<and> ide \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<and> \<lbrace>t\<^bold>\<down>\<rbrace> \<in> hom \<lbrace>t\<rbrace> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>"
        using assms Ide_in_Hom Ide_Nmlize_Ide
              red_in_Hom eval_in_hom ide_eval_Ide
        by force
      have "\<lbrace>Cod \<^bold>\<r>\<^bold>[t\<^bold>]\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>\<^bold>\<r>\<^bold>[t\<^bold>]\<rbrace> = \<r>[\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>] \<cdot> (\<lbrace>t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Src t\<rbrace>)"
        using t \<rr>_ide_simp red_in_Hom runit_naturality [of "\<lbrace>t\<^bold>\<down>\<rbrace>"]
        by (simp add: eval_simps')
      also have "... = \<lbrace>\<^bold>\<lfloor>\<^bold>\<r>\<^bold>[t\<^bold>]\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom \<^bold>\<r>\<^bold>[t\<^bold>]\<^bold>\<down>\<rbrace>"
      proof -
         have "\<lbrace>\<^bold>\<lfloor>\<^bold>\<r>\<^bold>[t\<^bold>]\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom \<^bold>\<r>\<^bold>[t\<^bold>]\<^bold>\<down>\<rbrace> = \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Src t\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Src t\<^bold>\<down>\<rbrace>)"
           using t by (cases t; simp; cases "Src t"; simp)
         also have "... = (\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Src t\<^bold>\<rfloor>\<rbrace>) \<cdot> (\<lbrace>t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Src t\<^bold>\<down>\<rbrace>)"
         proof -
           have "\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<in> hom \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>"
             using t Nmlize_in_Hom by auto
           moreover have "\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Src t\<^bold>\<rfloor>\<rbrace> \<in> hom (\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<star> \<lbrace>Src t\<rbrace>) \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>"
           proof -
             have "\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Src t\<^bold>\<rfloor>\<rbrace> \<in> hom \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>Src t\<^bold>\<rfloor>\<rbrace> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>"
             proof -
               have "Src \<^bold>\<lfloor>t\<^bold>\<rfloor> = Trg \<^bold>\<lfloor>Src t\<^bold>\<rfloor> \<and> \<^bold>\<lfloor>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<star> \<^bold>\<lfloor>Src t\<^bold>\<rfloor>\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
                 using t Nmlize_Src Nml_Nmlize HcompNml_Nml_Src [of "\<^bold>\<lfloor>t\<^bold>\<rfloor>"]
                 by simp
               thus ?thesis
                 using t Ide_Nmlize_Ide Nml_Nmlize Obj_Src red2_in_Hom(2)
                 by (auto simp add: eval_simps')
             qed
             thus ?thesis using t Nmlize_in_Hom Nmlize_Src by simp
           qed
           moreover have "\<lbrace>t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Src t\<^bold>\<down>\<rbrace> \<in> hom (\<lbrace>t\<rbrace> \<star> \<lbrace>Src t\<rbrace>) (\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<star> \<lbrace>Src t\<rbrace>)"
             using t red_in_Hom red_Src Obj_Src eval_simps'
             by (simp add: ide_eval_Ide ide_in_hom(2))
           ultimately show ?thesis using comp_assoc by fastforce
         qed
         also have "... = \<r>[\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>] \<cdot> (\<lbrace>t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Src t\<^bold>\<down>\<rbrace>)"
         proof -
           have "\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Src t\<^bold>\<rfloor>\<rbrace> = \<r>[\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>]"
           proof -
             have "Nml \<^bold>\<lfloor>t\<^bold>\<rfloor>" using t Nml_Nmlize by blast
             moreover have "is_Prim\<^sub>0 \<^bold>\<lfloor>Src t\<^bold>\<rfloor>"
               using t is_Prim0_Src Nmlize_Src by presburger
             ultimately show ?thesis
               apply (cases "\<^bold>\<lfloor>t\<^bold>\<rfloor>"; simp; cases "\<^bold>\<lfloor>Src t\<^bold>\<rfloor>"; simp)
               using t unitor_coincidence \<ll>_ide_simp \<rr>_ide_simp Nmlize_in_Hom
                 apply simp_all
               using t is_Prim0_Src
               apply (cases "\<^bold>\<lfloor>t\<^bold>\<rfloor>"; simp)
               using t Nmlize_Src unitor_coincidence preserves_obj by simp
           qed
           moreover have "\<r>[\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>] \<in> hom (\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<star> \<lbrace>Src t\<rbrace>) \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>"
             using t Nmlize_in_Hom by (auto simp add: eval_simps'(2))
           ultimately show ?thesis
             using comp_cod_arr [of "\<r>[\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>]"] by fastforce
         qed
         also have "... = \<r>[\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>] \<cdot> (\<lbrace>t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Src t\<rbrace>)"
           using t red_Src by auto
         finally show ?thesis by argo
      qed
      finally show ?thesis by blast
    qed

    lemma coherent_Lunit'_Ide:
    assumes "Ide a"
    shows "coherent \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[a\<^bold>]"
      using assms Ide_implies_Can coherent_Lunit_Ide
            coherent_iff_coherent_Inv [of "Lunit a"]
      by simp

    lemma coherent_Runit'_Ide:
    assumes "Ide a"
    shows "coherent \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[a\<^bold>]"
      using assms Ide_implies_Can coherent_Runit_Ide
            coherent_iff_coherent_Inv [of "Runit a"]
      by simp

    lemma red2_Nml_Src:
    assumes "Ide t" and "Nml t"
    shows "\<lbrace>t \<^bold>\<Down> Src t\<rbrace> = \<r>[\<lbrace>t\<rbrace>]"
      using assms eval_red2_Nml_Prim\<^sub>0 is_Prim0_Src [of t]
      by (cases "Src t"; simp)

    lemma red2_Trg_Nml:
    assumes "Ide t" and "Nml t"
    shows "\<lbrace>Trg t \<^bold>\<Down> t\<rbrace> = \<l>[\<lbrace>t\<rbrace>]"
      using assms is_Prim0_Trg [of t] \<ll>_ide_simp ide_eval_Ide
      by (cases "Trg t"; simp)

    lemma coherence_key_fact:
    assumes "Ide a \<and> Nml a" and "Ide b \<and> Nml b" and "Ide c \<and> Nml c"
    and "Src a = Trg b" and "Src b = Trg c"
    shows "\<lbrace>(a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>a \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>) =
           (\<lbrace>a \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace> \<cdot> (\<lbrace>a\<rbrace> \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>a\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
    proof -
      have "is_Prim\<^sub>0 b \<Longrightarrow> ?thesis"
      proof -
        assume b: "is_Prim\<^sub>0 b"
        have "\<lbrace>a \<^bold>\<Down> c\<rbrace> \<cdot> (\<r>[\<lbrace>a\<rbrace>] \<star> \<lbrace>c\<rbrace>) = (\<lbrace>a \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>a\<rbrace> \<star> \<l>[\<lbrace>c\<rbrace>])) \<cdot> \<a>[\<lbrace>a\<rbrace>, \<lbrace>Trg c\<rbrace>, \<lbrace>c\<rbrace>]"
        proof -
          have "Src b = Trg b"
            using b by (cases b; simp)
          thus ?thesis
            using assms triangle [of "\<lbrace>c\<rbrace>" "\<lbrace>a\<rbrace>"] ide_eval_Ide comp_assoc
            by (simp add: eval_simps')
        qed
        thus ?thesis
          using assms b HcompNml_Nml_Src [of a] HcompNml_Trg_Nml red2_Nml_Src [of a]
                red2_Trg_Nml
          by (cases b, simp_all)
      qed
      moreover have "\<lbrakk> \<not> is_Prim\<^sub>0 b; is_Prim\<^sub>0 c \<rbrakk> \<Longrightarrow> ?thesis"
      proof -
        assume b: "\<not> is_Prim\<^sub>0 b"
        assume c: "is_Prim\<^sub>0 c"
        have "\<lbrace>(a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>a \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>) = \<lbrace>(a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> Src b\<rbrace> \<cdot> (\<lbrace>a \<^bold>\<Down> b\<rbrace> \<star> src \<lbrace>b\<rbrace>)"
          using assms b c by (cases c, simp_all add: eval_simps')
        also have "... = \<r>[\<lbrace>a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b\<rbrace>] \<cdot> (\<lbrace>a \<^bold>\<Down> b\<rbrace> \<star> src \<lbrace>b\<rbrace>)"
          using assms red2_Nml_Src [of "a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b"] Nml_HcompNml(1) Src_HcompNml Ide_HcompNml
          by simp
        also have "... = \<lbrace>a \<^bold>\<Down> b\<rbrace> \<cdot> \<r>[\<lbrace>a\<rbrace> \<star> \<lbrace>b\<rbrace>]"
        proof -
          have "\<guillemotleft>\<lbrace>a \<^bold>\<Down> b\<rbrace> : \<lbrace>a\<rbrace> \<star> \<lbrace>b\<rbrace> \<Rightarrow> \<lbrace>a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b\<rbrace>\<guillemotright>"
            using assms red2_in_Hom eval_in_hom [of "a \<^bold>\<Down> b"] by simp
          thus ?thesis
            using assms runit_naturality [of "\<lbrace>a \<^bold>\<Down> b\<rbrace>"] arr_dom in_homE src_dom src_hcomp
                  hcomp_simps(1)
            by (elim in_homE, metis)
        qed
        also have "... = (\<lbrace>a \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace> \<cdot> (\<lbrace>a\<rbrace> \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>a\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
        proof -
          have "(\<lbrace>a \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace> \<cdot> (\<lbrace>a\<rbrace> \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>a\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>] =
                             (\<lbrace>a \<^bold>\<Down> b\<rbrace> \<cdot> (\<lbrace>a\<rbrace> \<star> \<r>[\<lbrace>b\<rbrace>])) \<cdot> \<a>[\<lbrace>a\<rbrace>, \<lbrace>b\<rbrace>, src \<lbrace>b\<rbrace>]"
            using assms c red2_Nml_Src [of b]
            by (cases c, simp_all add: eval_simps')
          thus ?thesis
            using assms runit_hcomp ide_eval_Ide comp_assoc
            by (simp add: eval_simps')
        qed
        finally show ?thesis by blast
      qed
      moreover have "\<lbrakk> \<not> is_Prim\<^sub>0 b; \<not> is_Prim\<^sub>0 c \<rbrakk> \<Longrightarrow> ?thesis"
      proof -
        assume b': "\<not> is_Prim\<^sub>0 b"
        hence b: "Ide b \<and> Nml b \<and> Arr b \<and> \<not> is_Prim\<^sub>0 b \<and>
                  ide \<lbrace>b\<rbrace> \<and> arr \<lbrace>b\<rbrace> \<and> \<^bold>\<lfloor>b\<^bold>\<rfloor> = b \<and> b\<^bold>\<down> = b \<and> Dom b = b \<and> Cod b = b"
          using assms Ide_Nmlize_Ide Ide_in_Hom ide_eval_Ide by simp
        assume c': "\<not> is_Prim\<^sub>0 c"
        hence c: "Ide c \<and> Nml c \<and> Arr c \<and> \<not> is_Prim\<^sub>0 c \<and>
                  ide \<lbrace>c\<rbrace> \<and> arr \<lbrace>c\<rbrace> \<and> \<^bold>\<lfloor>c\<^bold>\<rfloor> = c \<and> c\<^bold>\<down> = c \<and> Dom c = c \<and> Cod c = c"
          using assms Ide_Nmlize_Ide Ide_in_Hom ide_eval_Ide by simp
        have "\<And>a. Ide a \<and> Nml a \<and> Src a = Trg b \<Longrightarrow>
                   \<lbrace>(a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>a \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>)
                      = (\<lbrace>a \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace> \<cdot> (\<lbrace>a\<rbrace> \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>a\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
        proof -
          fix a :: "'c term"
          show "Ide a \<and> Nml a \<and> Src a = Trg b \<Longrightarrow>
                \<lbrace>(a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>a \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>)
                   = (\<lbrace>a \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace> \<cdot> (\<lbrace>a\<rbrace> \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>a\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
            apply (induct a)
            using b c HcompNml_in_Hom
                     apply (simp_all add: HcompNml_Nml_Src HcompNml_Trg_Nml)
          proof -
            fix f
            assume f: "C.ide f \<and> C.arr f \<and> \<^bold>\<langle>src\<^sub>C f\<^bold>\<rangle>\<^sub>0 = Trg b"
            show "\<lbrace>(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>) =
                    (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace> \<cdot> (E f \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[E f, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
            proof -
              have "\<lbrace>(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>) =
                      ((E f \<star> \<lbrace>b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (E f \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>) \<cdot> \<a>[E f, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]) \<cdot>
                      ((E f \<star> \<lbrace>b\<rbrace>) \<star> \<lbrace>c\<rbrace>)"
              proof -
                have "((E f \<star> \<lbrace>b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (E f \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>) \<cdot> \<a>[E f, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]) \<cdot>
                      ((E f \<star> \<lbrace>b\<rbrace>) \<star> \<lbrace>c\<rbrace>) =
                      ((E f \<star> \<lbrace>b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (E f \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>) \<cdot> \<a>[E f, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]) \<cdot>
                      (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>)"
                  using f b red2_Nml by simp
                also have "... = (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace> \<cdot> (E f \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>) \<cdot> \<a>[E f, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]) \<cdot>
                                 (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>)"
                proof -
                  have "\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace> = E f \<star> \<lbrace>b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>"
                    using assms(5) b c is_Hcomp_HcompNml red2_Nml Nml_HcompNml(1)
                          is_Hcomp_def
                    by (metis eval.simps(2) eval.simps(3) red2.simps(4))
                  thus ?thesis by argo
                qed
                also have "... = \<lbrace>(\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>)"
                  using b c \<alpha>_def by (cases c, simp_all)
                finally show ?thesis by argo
              qed
              also have "... = ((E f \<star> \<lbrace>b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (E f \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[E f, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
              proof -
                have "src (E f) = trg \<lbrace>b\<rbrace>"
                  using b f preserves_src
                  by (cases "Trg b", auto simp add: eval_simps')
                thus ?thesis
                  using assms b c f comp_arr_dom comp_assoc
                  by (auto simp add: eval_simps')
              qed
              also have "... = (\<lbrace>\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace> \<cdot> (E f \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[E f, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                using assms f b c Ide_HcompNml HcompNml_Prim Nml_HcompNml
                      is_Hcomp_HcompNml [of b c] \<alpha>_def
                by (cases "b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c", simp_all)
              finally show ?thesis by blast
            qed
            next
            fix x
            assume x: "C.obj x \<and> \<^bold>\<langle>x\<^bold>\<rangle>\<^sub>0 = Trg b"
            show "\<lbrace>b \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>Trg b \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>) =
                  (\<lbrace>Trg b \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace> \<cdot> (\<lbrace>Trg b\<rbrace> \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>Trg b\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
            proof -
              have 1: "Trg (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c) = Trg b"
                using assms b c Trg_HcompNml by blast
              have 2: "\<lbrace>Trg b \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace> = \<l>[\<lbrace>b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>]"
                using assms b c 1 Nml_HcompNml red2_Trg_Nml [of "b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c"] Ide_HcompNml
                by simp
              have "\<lbrace>b \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>Trg b \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>) = \<lbrace>b \<^bold>\<Down> c\<rbrace> \<cdot> (\<l>[\<lbrace>b\<rbrace>] \<star> \<lbrace>c\<rbrace>)"
                using b c 1 2 HcompNml_Trg_Nml red2_Trg_Nml Trg_HcompNml by simp
              also have "... = \<lbrace>b \<^bold>\<Down> c\<rbrace> \<cdot> \<l>[\<lbrace>b\<rbrace> \<star> \<lbrace>c\<rbrace>] \<cdot> \<a>[\<lbrace>Trg b\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                using assms b c lunit_hcomp [of "\<lbrace>b\<rbrace>" "\<lbrace>c\<rbrace>"]
                by (metis (no_types, lifting) eval_simps'(3) eval_simps(2))
              also have "... = (\<lbrace>b \<^bold>\<Down> c\<rbrace> \<cdot> \<l>[\<lbrace>b\<rbrace> \<star> \<lbrace>c\<rbrace>]) \<cdot> \<a>[\<lbrace>Trg b\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                using comp_assoc by simp
              also have "... = (\<l>[\<lbrace>b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>] \<cdot> (\<lbrace>Trg b\<rbrace> \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>Trg b\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                using assms b c lunit_naturality [of "\<lbrace>b \<^bold>\<Down> c\<rbrace>"] red2_in_Hom
                by (simp add: eval_simps')
              also have "... = (\<lbrace>Trg b \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace> \<cdot> (\<lbrace>Trg b\<rbrace> \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>Trg b\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                using b c 1 2 HcompNml_Trg_Nml red2_Trg_Nml Trg_HcompNml comp_assoc
                by simp
              finally show ?thesis
                by blast
            qed
            next
            fix d e
            assume I: "Nml e \<Longrightarrow> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>e \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>)
                                    = (\<lbrace>e \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace> \<cdot> (\<lbrace>e\<rbrace> \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
            assume de: "Ide d \<and> Ide e \<and> Src d = Trg e \<and> Nml (d \<^bold>\<star> e) \<and> Src e = Trg b"
            show "\<lbrace>((d \<^bold>\<star> e) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>(d \<^bold>\<star> e) \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>)
                    = (\<lbrace>(d \<^bold>\<star> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace> \<cdot> ((\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace>) \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
            proof -
              let ?f = "un_Prim d"
              have "is_Prim d"
                using de Nml_HcompD
                by (metis term.disc(12))
              hence "d = \<^bold>\<langle>?f\<^bold>\<rangle> \<and> C.ide ?f"
                using de by (cases d; simp)
              hence d: "Ide d \<and> Arr d \<and> Dom d = d \<and> Cod d = d \<and> Nml d \<and>
                        d = \<^bold>\<langle>?f\<^bold>\<rangle> \<and> C.ide ?f \<and> ide \<lbrace>d\<rbrace> \<and> arr \<lbrace>d\<rbrace>"
                using de ide_eval_Ide Nml_Nmlize(1) Ide_in_Hom Nml_HcompD [of d e]
                by simp
              have "Nml e \<and> \<not> is_Prim\<^sub>0 e"
                using de Nml_HcompD by metis
              hence e: "Ide e \<and> Arr e \<and> Dom e = e \<and> Cod e = e \<and> Nml e \<and>
                        \<not> is_Prim\<^sub>0 e \<and> ide \<lbrace>e\<rbrace> \<and> arr \<lbrace>e\<rbrace>"
                using de Ide_in_Hom ide_eval_Ide by simp
              have 1: "is_Hcomp (e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<and> is_Hcomp (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c) \<and> is_Hcomp (e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)"
                using assms b c e de is_Hcomp_HcompNml [of e b] Nml_HcompNml
                      is_Hcomp_HcompNml [of b c] is_Hcomp_HcompNml [of e "b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c"]
                by auto
              have eb: "Src e = Trg b"
                using assms b c e de by argo
              have bc: "Src b = Trg c"
                using assms b c by simp
              have 4: "is_Hcomp ((e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)"
                using assms b c e eb de 1 is_Hcomp_HcompNml [of e b]
                      is_Hcomp_HcompNml [of "e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b" c] is_Hcomp_HcompNml [of e b]
                      Nml_HcompNml(1) [of e b] Src_HcompNml
                by auto
              have "\<lbrace>((d \<^bold>\<star> e) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace> \<cdot> (\<lbrace>(d \<^bold>\<star> e) \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>)
                      = ((\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>) \<cdot>
                         \<a>[\<lbrace>d\<rbrace>, \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b\<rbrace>, \<lbrace>c\<rbrace>]) \<cdot>
                        ((\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> b\<rbrace>) \<cdot> \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<star> \<lbrace>c\<rbrace>)"
              proof -
                have "\<lbrace>((d \<^bold>\<star> e) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>
                         = (\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>) \<cdot>
                           \<a>[\<lbrace>d\<rbrace>, \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b\<rbrace>, \<lbrace>c\<rbrace>]"
                proof -
                  have "((d \<^bold>\<star> e) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c = (d \<^bold>\<star> (e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b)) \<^bold>\<Down> c"
                    using b c d e de 1 HcompNml_Nml Nml_HcompNml HcompNml_assoc
                          HcompNml_Prim
                    by (metis term.distinct_disc(4))
                  also have "... = (d \<^bold>\<Down> ((e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)) \<^bold>\<cdot> (d \<^bold>\<star> ((e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c)) \<^bold>\<cdot>
                                   \<^bold>\<a>\<^bold>[d, e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b, c\<^bold>]"
                    using b c d e de 1 Nml_HcompNml Nmlize_Nml
                    by (cases c, simp_all)
                  also have "... = (d \<^bold>\<star> ((e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)) \<^bold>\<cdot> (d \<^bold>\<star> ((e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c)) \<^bold>\<cdot>
                                   \<^bold>\<a>\<^bold>[d, e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b, c\<^bold>]"
                    using d 4
                    apply (cases d, simp_all)
                    by (cases "(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c", simp_all)
                  finally show ?thesis
                    using b c d e HcompNml_in_Hom red2_in_Hom
                          Nml_HcompNml Ide_HcompNml \<alpha>_def
                    by simp
                qed
                moreover have "\<lbrace>(d \<^bold>\<star> e) \<^bold>\<Down> b\<rbrace>
                                 = (\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> b\<rbrace>) \<cdot> \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>]"
                proof -
                  have "(d \<^bold>\<star> e) \<^bold>\<Down> b = (d \<^bold>\<Down> (e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b)) \<^bold>\<cdot> (d \<^bold>\<star> (e \<^bold>\<Down> b)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[d, e, b\<^bold>]"
                      using b c d e de 1 HcompNml_Prim Nmlize_Nml
                      by (cases b, simp_all)
                  also have "... = (d \<^bold>\<star> (e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b)) \<^bold>\<cdot> (d \<^bold>\<star> (e \<^bold>\<Down> b)) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[d, e, b\<^bold>]"
                    using b c d e de 1 HcompNml_Nml Nml_HcompNml
                    apply (cases d, simp_all)
                    by (cases "e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b", simp_all)
                  finally show ?thesis
                    using b d e HcompNml_in_Hom red2_in_Hom \<alpha>_def by simp
                qed
                ultimately show ?thesis by argo
              qed
              also have "... = ((\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>) \<cdot> \<a>[\<lbrace>d\<rbrace>, \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b\<rbrace>, \<lbrace>c\<rbrace>]) \<cdot>
                               ((\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> b\<rbrace>) \<star> \<lbrace>c\<rbrace>) \<cdot> (\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<star> \<lbrace>c\<rbrace>)"
              proof -
                have "(\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> b\<rbrace>) \<cdot> \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<star> \<lbrace>c\<rbrace>
                        = ((\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> b\<rbrace>) \<star> \<lbrace>c\<rbrace>) \<cdot> (\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<star> \<lbrace>c\<rbrace>)"
                  using assms b c d e de eb HcompNml_in_Hom red2_in_Hom comp_cod_arr
                        Ide_HcompNml Nml_HcompNml comp_assoc
                        interchange [of "\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> b\<rbrace>" "\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>]" "\<lbrace>c\<rbrace>" "\<lbrace>c\<rbrace>"]
                  by (auto simp add: eval_simps')
                moreover have "(\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>) \<cdot>
                                 \<a>[\<lbrace>d\<rbrace>, \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b\<rbrace>, \<lbrace>c\<rbrace>] =
                               (\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>) \<cdot> \<a>[\<lbrace>d\<rbrace>, \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b\<rbrace>, \<lbrace>c\<rbrace>]"
                proof -
                  have "(\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>) \<cdot>
                                   \<a>[\<lbrace>d\<rbrace>, \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b\<rbrace>, \<lbrace>c\<rbrace>] =
                                   ((\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>)) \<cdot>
                                   \<a>[\<lbrace>d\<rbrace>, \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b\<rbrace>, \<lbrace>c\<rbrace>]"
                    using comp_assoc by simp
                  thus ?thesis
                    using assms b c d e de eb HcompNml_in_Hom red2_in_Hom
                          Ide_HcompNml Nml_HcompNml comp_cod_arr
                    by (simp add: eval_simps')
                qed
                ultimately show ?thesis by argo
              qed
              also have "... = (\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> (\<lbrace>e \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>)) \<cdot>
                               \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace> \<star> \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>] \<cdot> (\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<star> \<lbrace>c\<rbrace>)"
                using assms b c d e de HcompNml_in_Hom red2_in_Hom
                      Ide_HcompNml Nml_HcompNml ide_eval_Ide
                      assoc_naturality [of "\<lbrace>d\<rbrace>" "\<lbrace>e \<^bold>\<Down> b\<rbrace>" "\<lbrace>c\<rbrace>"]
                      comp_permute [of "\<a>[\<lbrace>d\<rbrace>, \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b\<rbrace>, \<lbrace>c\<rbrace>]" "(\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> b\<rbrace>) \<star> \<lbrace>c\<rbrace>"
                                       "\<lbrace>d\<rbrace> \<star> (\<lbrace>e \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>)" "\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace> \<star> \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"]
                      comp_assoc
                by (simp add: eval_simps')
              also have "... = ((\<lbrace>d\<rbrace> \<star> \<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> (\<lbrace>e \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>))) \<cdot>
                               \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace> \<star> \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>] \<cdot> (\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<star> \<lbrace>c\<rbrace>)"
                using comp_assoc by simp
              also have "... = (((\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace> \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot>
                                (\<lbrace>d\<rbrace> \<star> \<a>[\<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>])) \<cdot>
                               \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace> \<star> \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>] \<cdot> (\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<star> \<lbrace>c\<rbrace>)"
                using assms b c d e de eb I HcompNml_in_Hom red2_in_Hom
                      Ide_HcompNml Nml_HcompNml whisker_left [of "\<lbrace>d\<rbrace>"]
                      interchange [of "\<lbrace>d\<rbrace>" "\<lbrace>d\<rbrace>" "\<lbrace>(e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b) \<^bold>\<Down> c\<rbrace>" "\<lbrace>e \<^bold>\<Down> b\<rbrace> \<star> \<lbrace>c\<rbrace>"]
                by (auto simp add: eval_simps')
              also have "... = ((\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace> \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot>
                               ((\<lbrace>d\<rbrace> \<star> \<a>[\<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]) \<cdot>
                                \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace> \<star> \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>] \<cdot> (\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>] \<star> \<lbrace>c\<rbrace>))"
                using comp_assoc by simp
              also have "... = ((\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> (\<lbrace>e\<rbrace> \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>))) \<cdot>
                               \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace> \<star> \<lbrace>c\<rbrace>] \<cdot> \<a>[\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                using assms b c d e de pentagon
                by (simp add: eval_simps')
              also have "... = (\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace>) \<cdot>
                               ((\<lbrace>d\<rbrace> \<star> (\<lbrace>e\<rbrace> \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot> \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace> \<star> \<lbrace>c\<rbrace>]) \<cdot>
                               \<a>[\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                using comp_assoc by simp
              also have "... = ((\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>)) \<cdot>
                               (\<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>] \<cdot> ((\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace>) \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot>
                               \<a>[\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                using assms d e de HcompNml_in_Hom red2_in_Hom Ide_HcompNml Nml_HcompNml
                      assoc_naturality [of "\<lbrace>d\<rbrace>" "\<lbrace>e\<rbrace>" "\<lbrace>b \<^bold>\<Down> c\<rbrace>"] comp_cod_arr [of "\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>"]
                by (simp add: eval_simps')
              also have "... = ((\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>) \<cdot>
                                \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>]) \<cdot>
                               ((\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace>) \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>) \<cdot> \<a>[\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                using comp_assoc by simp
              also have "... = \<lbrace>(d \<^bold>\<star> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace> \<cdot> ((\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace>) \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>) \<cdot>
                               \<a>[\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
              proof -
                have "\<lbrace>(d \<^bold>\<star> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace>
                         = (\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace>) \<cdot> (\<lbrace>d\<rbrace> \<star> \<lbrace>e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace>) \<cdot>
                           \<a>[\<lbrace>d\<rbrace>, \<lbrace>e\<rbrace>, \<lbrace>b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<rbrace>]"
                proof -
                  have "(d \<^bold>\<star> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)
                          = (d \<^bold>\<Down> (e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<^bold>\<rfloor>)) \<^bold>\<cdot> (d \<^bold>\<star> (e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c))) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[d, e, b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<^bold>]"
                    using e 1 by (cases "b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c") auto
                  also have "... = (d \<^bold>\<Down> (e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c))) \<^bold>\<cdot> (d \<^bold>\<star> (e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c))) \<^bold>\<cdot>
                                   \<^bold>\<a>\<^bold>[d, e, b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<^bold>]"
                    using assms Nml_HcompNml Nmlize_Nml by simp
                  also have "... = (d \<^bold>\<star> (e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c))) \<^bold>\<cdot> (d \<^bold>\<star> (e \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c))) \<^bold>\<cdot>
                                   \<^bold>\<a>\<^bold>[d, e, b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c\<^bold>]"
                    using d 1
                    apply (cases "e \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c", simp_all)
                    by (cases d, simp_all)
                  finally show ?thesis
                    using \<alpha>_def by simp
                qed
                thus ?thesis by simp
              qed
              also have "... = (\<lbrace>(d \<^bold>\<star> e) \<^bold>\<Down> (b \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> c)\<rbrace> \<cdot> ((\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace>) \<star> \<lbrace>b \<^bold>\<Down> c\<rbrace>)) \<cdot>
                               \<a>[\<lbrace>d\<rbrace> \<star> \<lbrace>e\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
                 using comp_assoc by simp
              finally show ?thesis by auto
            qed
          qed
        qed
        thus ?thesis using assms(1,4) by blast
      qed
      ultimately show ?thesis by blast
    qed

    lemma coherent_Assoc_Ide:
    assumes "Ide a" and "Ide b" and "Ide c" and "Src a = Trg b" and "Src b = Trg c"
    shows "coherent \<^bold>\<a>\<^bold>[a, b, c\<^bold>]"
    proof -
      have a: "Ide a \<and> Arr a \<and> Dom a = a \<and> Cod a = a \<and>
               ide \<lbrace>a\<rbrace> \<and> ide \<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace> \<and> \<lbrace>a\<^bold>\<down>\<rbrace> \<in> hom \<lbrace>a\<rbrace> \<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace>"
        using assms Ide_in_Hom Ide_Nmlize_Ide ide_eval_Ide red_in_Hom eval_in_hom(2)
        by force
      have b: "Ide b \<and> Arr b \<and> Dom b = b \<and> Cod b = b \<and>
               ide \<lbrace>b\<rbrace> \<and> ide \<lbrace>\<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace> \<and> \<lbrace>b\<^bold>\<down>\<rbrace> \<in> hom \<lbrace>b\<rbrace> \<lbrace>\<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace>"
        using assms Ide_in_Hom Ide_Nmlize_Ide ide_eval_Ide red_in_Hom(2)
              eval_in_hom(2) [of "b\<^bold>\<down>"]
        by auto
      have c: "Ide c \<and> Arr c \<and> Dom c = c \<and> Cod c = c \<and>
               ide \<lbrace>c\<rbrace> \<and> ide \<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace> \<and> \<lbrace>c\<^bold>\<down>\<rbrace> \<in> hom \<lbrace>c\<rbrace> \<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>"
        using assms Ide_in_Hom Ide_Nmlize_Ide red_in_Hom eval_in_hom(2) [of "c\<^bold>\<down>"]
              ide_eval_Ide
        by auto
      have "\<lbrace>Cod \<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>\<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<rbrace>
              = (\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>)\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace> \<star> \<lbrace>\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>) \<cdot> (\<lbrace>a\<^bold>\<down>\<rbrace> \<star> \<lbrace>b\<^bold>\<down>\<rbrace> \<star> \<lbrace>c\<^bold>\<down>\<rbrace>)) \<cdot>
                \<a>[\<lbrace>a\<rbrace>, \<lbrace>b\<rbrace>, \<lbrace>c\<rbrace>]"
        using assms a b c red_in_Hom red2_in_Hom Nml_Nmlize Ide_Nmlize_Ide
              \<alpha>_def eval_red_Hcomp interchange [of "\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace>" "\<lbrace>a\<^bold>\<down>\<rbrace>"] comp_cod_arr [of "\<lbrace>a\<^bold>\<down>\<rbrace>"]
        by (simp add: eval_simps')
      also have "... = ((\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> (\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>)\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace> \<star> \<lbrace>\<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>)) \<cdot> \<a>[\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor>\<rbrace>, \<lbrace>\<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace>, \<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>]) \<cdot>
                       ((\<lbrace>a\<^bold>\<down>\<rbrace> \<star> \<lbrace>b\<^bold>\<down>\<rbrace>) \<star> \<lbrace>c\<^bold>\<down>\<rbrace>)"
        using assms red_in_Hom Ide_HcompNml assoc_naturality [of "\<lbrace>a\<^bold>\<down>\<rbrace>" "\<lbrace>b\<^bold>\<down>\<rbrace>" "\<lbrace>c\<^bold>\<down>\<rbrace>"] comp_assoc
        by (simp add: eval_simps')
      also have "... = (\<lbrace>(\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>b\<^bold>\<rfloor>) \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace> \<star> \<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>)) \<cdot> ((\<lbrace>a\<^bold>\<down>\<rbrace> \<star> \<lbrace>b\<^bold>\<down>\<rbrace>) \<star> \<lbrace>c\<^bold>\<down>\<rbrace>)"
        using assms Nml_Nmlize Ide_Nmlize_Ide coherence_key_fact by simp
      also have "... = \<lbrace>\<^bold>\<lfloor>\<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom \<^bold>\<a>\<^bold>[a, b, c\<^bold>]\<^bold>\<down>\<rbrace>"
        using assms a b c red_in_Hom red2_in_Hom Ide_Nmlize_Ide
              Nml_Nmlize eval_red_Hcomp HcompNml_assoc
              interchange [of "\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace>" "\<lbrace>a\<^bold>\<down>\<rbrace> \<star> \<lbrace>b\<^bold>\<down>\<rbrace>" "\<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>" "\<lbrace>c\<^bold>\<down>\<rbrace>"]
              comp_cod_arr [of "\<lbrace>c\<^bold>\<down>\<rbrace>" "\<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>"]
        apply (simp add: eval_simps')
      proof -
        have "seq \<lbrace>(\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>b\<^bold>\<rfloor>) \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace> ((\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace> \<star> \<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>) \<cdot> ((\<lbrace>a\<^bold>\<down>\<rbrace> \<star> \<lbrace>b\<^bold>\<down>\<rbrace>) \<star> \<lbrace>c\<^bold>\<down>\<rbrace>))"
          using assms c red_in_Hom red2_in_Hom Nml_HcompNml Ide_Nmlize_Ide Ide_HcompNml
                Nml_Nmlize
          by (simp_all add: eval_simps')
        moreover have
            "cod (\<lbrace>(\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>b\<^bold>\<rfloor>) \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace> \<star> \<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>) \<cdot> ((\<lbrace>a\<^bold>\<down>\<rbrace> \<star> \<lbrace>b\<^bold>\<down>\<rbrace>) \<star> \<lbrace>c\<^bold>\<down>\<rbrace>)) =
             \<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>"
          using assms c red_in_Hom red2_in_Hom Nml_HcompNml Ide_Nmlize_Ide Ide_HcompNml
                Nml_Nmlize HcompNml_assoc
          by (simp add: eval_simps')
        ultimately
        show "(\<lbrace>(\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>b\<^bold>\<rfloor>) \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace> \<star> \<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>)) \<cdot> ((\<lbrace>a\<^bold>\<down>\<rbrace> \<star> \<lbrace>b\<^bold>\<down>\<rbrace>) \<star> \<lbrace>c\<^bold>\<down>\<rbrace>) =
              \<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>b\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace> \<cdot>
                \<lbrace>(\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>b\<^bold>\<rfloor>) \<^bold>\<Down> \<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>a\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>b\<^bold>\<rfloor>\<rbrace> \<star> \<lbrace>\<^bold>\<lfloor>c\<^bold>\<rfloor>\<rbrace>) \<cdot> ((\<lbrace>a\<^bold>\<down>\<rbrace> \<star> \<lbrace>b\<^bold>\<down>\<rbrace>) \<star> \<lbrace>c\<^bold>\<down>\<rbrace>)"
         using comp_cod_arr comp_assoc by simp
       qed
       finally show ?thesis by blast
    qed

    lemma coherent_Assoc'_Ide:
    assumes "Ide a" and "Ide b" and "Ide c" and "Src a = Trg b" and "Src b = Trg c"
    shows "coherent \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[a, b, c\<^bold>]"
        using assms Ide_implies_Can coherent_Assoc_Ide Inv_Ide coherent_iff_coherent_Inv
              Can.simps(10) Inv.simps(10)
        by presburger

    lemma eval_red2_naturality:
    assumes "Nml t" and "Nml u" and "Src t = Trg u"
    shows "\<lbrace>Cod t \<^bold>\<Down> Cod u\<rbrace> \<cdot> (\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace>) = \<lbrace>t \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>Dom t \<^bold>\<Down> Dom u\<rbrace>"
    proof -
      have *: "\<And>t u. Nml (t \<^bold>\<star> u) \<Longrightarrow> arr \<lbrace>t\<rbrace> \<and> arr \<lbrace>u\<rbrace>"
        using Nml_implies_Arr Nml_HcompD by simp
      have "is_Prim\<^sub>0 t \<Longrightarrow> ?thesis"
        using assms Nml_implies_Arr is_Prim0_Trg \<ll>.naturality [of "\<lbrace>u\<rbrace>"]
        by (cases t, simp_all add: eval_simps', cases "Trg t", simp_all)
      moreover have "\<not> is_Prim\<^sub>0 t \<and> is_Prim\<^sub>0 u \<Longrightarrow> ?thesis"
        using assms Nml_implies_Arr eval_red2_Nml_Prim\<^sub>0 runit_naturality [of "\<lbrace>t\<rbrace>"]
        by (cases u, simp_all add: eval_simps')
      moreover have "\<not> is_Prim\<^sub>0 t \<and> \<not> is_Prim\<^sub>0 u \<Longrightarrow> ?thesis"
        using assms * Nml_implies_Arr
        apply (induct t, simp_all)
      proof -
        fix f
        assume f: "C.arr f"
        assume "\<not> is_Prim\<^sub>0 u"
        hence u: "\<not> is_Prim\<^sub>0 u \<and>
                  Nml u \<and> Nml (Dom u) \<and> Nml (Cod u) \<and> Ide (Dom u) \<and> Ide (Cod u) \<and>
                  arr \<lbrace>u\<rbrace> \<and> arr \<lbrace>Dom u\<rbrace> \<and> arr \<lbrace>Cod u\<rbrace> \<and> ide \<lbrace>Dom u\<rbrace> \<and> ide \<lbrace>Cod u\<rbrace>"
          using assms(2) Nml_implies_Arr ide_eval_Ide by simp
        hence 1: "\<not> is_Prim\<^sub>0 (Dom u) \<and> \<not> is_Prim\<^sub>0 (Cod u)"
          using u by (cases u, simp_all)
        assume "\<^bold>\<langle>src\<^sub>C f\<^bold>\<rangle>\<^sub>0 = Trg u"
        hence "\<lbrace>\<^bold>\<langle>src\<^sub>C f\<^bold>\<rangle>\<^sub>0\<rbrace> = \<lbrace>Trg u\<rbrace>" by simp
        hence fu: "src (E f) = trg \<lbrace>u\<rbrace>"
          using f u preserves_src Nml_implies_Arr
          by (simp add: eval_simps')
        show "\<lbrace>\<^bold>\<langle>C.cod f\<^bold>\<rangle> \<^bold>\<Down> Cod u\<rbrace> \<cdot> (E f \<star> \<lbrace>u\<rbrace>) = (E f \<star> \<lbrace>u\<rbrace>) \<cdot> \<lbrace>\<^bold>\<langle>C.dom f\<^bold>\<rangle> \<^bold>\<Down> Dom u\<rbrace>"
        proof -
          have "\<lbrace>\<^bold>\<langle>C.cod f\<^bold>\<rangle> \<^bold>\<Down> Cod u\<rbrace> = E (C.cod f) \<star> cod \<lbrace>u\<rbrace>"
            using f u 1 Nml_implies_Arr
            by (cases "Cod u", simp_all add: eval_simps')
          moreover have "\<lbrace>\<^bold>\<langle>C.dom f\<^bold>\<rangle> \<^bold>\<Down> Dom u\<rbrace> = E (C.dom f) \<star> dom \<lbrace>u\<rbrace>"
            using f u 1 Nml_implies_Arr
            by (cases "Dom u", simp_all add: eval_simps')
          moreover have "\<guillemotleft>E f \<star> \<lbrace>u\<rbrace> : E (C.dom f) \<star> \<lbrace>Dom u\<rbrace> \<Rightarrow> E (C.cod f) \<star> \<lbrace>Cod u\<rbrace>\<guillemotright>"
            using f u fu Nml_implies_Arr
            apply (intro hcomp_in_vhom)
              apply auto
            by (metis C.src_dom eval_simps(4) preserves_src trg_dom u)
          ultimately show ?thesis
            using f u comp_arr_dom comp_cod_arr
            by (simp add: fu)
        qed
        next
        fix v w
        assume I2: "\<lbrakk> \<not> is_Prim\<^sub>0 w; Nml w \<rbrakk> \<Longrightarrow>
                      \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace> \<cdot> (\<lbrace>w\<rbrace> \<star> \<lbrace>u\<rbrace>) = \<lbrace>w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>"
        assume "\<not> is_Prim\<^sub>0 u"
        hence u: "\<not> is_Prim\<^sub>0 u \<and> Arr u \<and> Arr (Dom u) \<and> Arr (Cod u) \<and>
                  Nml u \<and> Nml (Dom u) \<and> Nml (Cod u) \<and> Ide (Dom u) \<and> Ide (Cod u) \<and>
                  arr \<lbrace>u\<rbrace> \<and> arr \<lbrace>Dom u\<rbrace> \<and> arr \<lbrace>Cod u\<rbrace> \<and> ide \<lbrace>Dom u\<rbrace> \<and> ide \<lbrace>Cod u\<rbrace>"
          using assms(2) Nml_implies_Arr ide_eval_Ide by simp
        assume vw: "Nml (v \<^bold>\<star> w)"
        assume wu: "Src w = Trg u"
        let ?f = "un_Prim v"
        have "v = \<^bold>\<langle>?f\<^bold>\<rangle> \<and> C.arr ?f"
          using vw by (metis Nml_HcompD(1) Nml_HcompD(2))
        hence "Arr v \<and> v = \<^bold>\<langle>un_Prim v\<^bold>\<rangle> \<and> C.arr ?f \<and> Nml v" by (cases v; simp)
        hence v: "v = \<^bold>\<langle>?f\<^bold>\<rangle> \<and> C.arr ?f \<and> Arr v \<and> Arr (Dom v) \<and> Arr (Cod v) \<and> Nml v \<and>
                  Nml (Dom v) \<and> Nml (Cod v) \<and>
                  arr \<lbrace>v\<rbrace> \<and> arr \<lbrace>Dom v\<rbrace> \<and> arr \<lbrace>Cod v\<rbrace> \<and> ide \<lbrace>Dom v\<rbrace> \<and> ide \<lbrace>Cod v\<rbrace>"
          using vw * by (cases v, simp_all)
        have "Nml w \<and> \<not> is_Prim\<^sub>0 w"
          using vw v by (metis Nml.simps(3))
        hence w: "\<not> is_Prim\<^sub>0 w \<and> Arr w \<and> Arr (Dom w) \<and> Arr (Cod w) \<and>
                  Nml w \<and> Nml (Dom w) \<and> Nml (Cod w) \<and>
                  Ide (Dom w) \<and> Ide (Cod w) \<and>
                  arr \<lbrace>w\<rbrace> \<and> arr \<lbrace>Dom w\<rbrace> \<and> arr \<lbrace>Cod w\<rbrace> \<and> ide \<lbrace>Dom w\<rbrace> \<and> ide \<lbrace>Cod w\<rbrace>"
          using vw * Nml_implies_Arr ide_eval_Ide by simp
        have u': "\<not> is_Prim\<^sub>0 (Dom u) \<and> \<not> is_Prim\<^sub>0 (Cod u)"
          using u by (cases u, simp_all)
        have w':  "\<not> is_Prim\<^sub>0 (Dom w) \<and> \<not> is_Prim\<^sub>0 (Cod w)"
          using w by (cases w, simp_all)
        have vw': "Src v = Trg w"
          using vw Nml_HcompD(7) by simp
        have X: "Nml (Dom v \<^bold>\<star> (Dom w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u))"
          using u u' v w w' wu vw is_Hcomp_HcompNml Nml_HcompNml
          apply (cases v, simp_all)
          apply (cases "Dom w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u", simp_all)
          apply (cases "Dom v", simp_all)
          by (metis Src_Dom Trg_Dom term.disc(21))
        have Y: "Nml (Cod v \<^bold>\<star> (Cod w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u))"
          using u u' w w' wu vw is_Hcomp_HcompNml Nml_HcompNml
          apply (cases v, simp_all)
          apply (cases "Cod w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u", simp_all)
          apply (cases "Cod v", simp_all)
          by (metis Src_Cod Trg_Cod term.disc(21))
        show "\<lbrace>(Cod v \<^bold>\<star> Cod w) \<^bold>\<Down> Cod u\<rbrace> \<cdot> ((\<lbrace>v\<rbrace> \<star> \<lbrace>w\<rbrace>) \<star> \<lbrace>u\<rbrace>)
                = \<lbrace>(v \<^bold>\<star> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>(Dom v \<^bold>\<star> Dom w) \<^bold>\<Down> Dom u\<rbrace>"
        proof -
          have "\<lbrace>(Cod v \<^bold>\<star> Cod w) \<^bold>\<Down> Cod u\<rbrace> \<cdot> ((\<lbrace>v\<rbrace> \<star> \<lbrace>w\<rbrace>) \<star> \<lbrace>u\<rbrace>)
                  = (\<lbrace>Cod v \<^bold>\<Down> (Cod w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u)\<rbrace> \<cdot> (\<lbrace>Cod v\<rbrace> \<star> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>) \<cdot>
                    \<a>[\<lbrace>Cod v\<rbrace>, \<lbrace>Cod w\<rbrace>, \<lbrace>Cod u\<rbrace>]) \<cdot> ((\<lbrace>v\<rbrace> \<star> \<lbrace>w\<rbrace>) \<star> \<lbrace>u\<rbrace>)"
          proof -
            have "(Cod v \<^bold>\<star> Cod w) \<^bold>\<Down> Cod u
                    = (Cod v \<^bold>\<Down> (Cod w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>)) \<^bold>\<cdot> (Cod v \<^bold>\<star> Cod w \<^bold>\<Down> Cod u) \<^bold>\<cdot>
                      \<^bold>\<a>\<^bold>[Cod v, Cod w, Cod u\<^bold>]"
              using u v w by (cases u, simp_all)
            hence "\<lbrace>(Cod v \<^bold>\<star> Cod w) \<^bold>\<Down> Cod u\<rbrace>
                     = \<lbrace>Cod v \<^bold>\<Down> (Cod w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u)\<rbrace> \<cdot> (\<lbrace>Cod v\<rbrace> \<star> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>) \<cdot>
                       \<a>[\<lbrace>Cod v\<rbrace>, \<lbrace>Cod w\<rbrace>, \<lbrace>Cod u\<rbrace>]"
              using u v w \<alpha>_def by simp
            thus ?thesis by presburger
          qed
          also have "... = ((\<lbrace>Cod v\<rbrace> \<star> \<lbrace>Cod w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod u\<rbrace>) \<cdot> (\<lbrace>Cod v\<rbrace> \<star> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>) \<cdot>
                            \<a>[\<lbrace>Cod v\<rbrace>, \<lbrace>Cod w\<rbrace>, \<lbrace>Cod u\<rbrace>]) \<cdot> ((\<lbrace>v\<rbrace> \<star> \<lbrace>w\<rbrace>) \<star> \<lbrace>u\<rbrace>)"
            using u v w Y red2_Nml by simp
          also have "... = ((\<lbrace>Cod v\<rbrace> \<star> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>) \<cdot> \<a>[\<lbrace>Cod v\<rbrace>, \<lbrace>Cod w\<rbrace>, \<lbrace>Cod u\<rbrace>]) \<cdot>
                           ((\<lbrace>v\<rbrace> \<star> \<lbrace>w\<rbrace>) \<star> \<lbrace>u\<rbrace>)"
            using u v w vw' wu comp_cod_arr red2_in_Hom HcompNml_in_Hom comp_reduce
           by (simp add: eval_simps')
          also have "... = (\<lbrace>Cod v\<rbrace> \<star> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>) \<cdot> \<a>[\<lbrace>Cod v\<rbrace>, \<lbrace>Cod w\<rbrace>, \<lbrace>Cod u\<rbrace>] \<cdot>
                           ((\<lbrace>v\<rbrace> \<star> \<lbrace>w\<rbrace>) \<star> \<lbrace>u\<rbrace>)"
            using comp_assoc by simp
          also have "... = (\<lbrace>Cod v\<rbrace> \<star> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>) \<cdot> (\<lbrace>v\<rbrace> \<star> \<lbrace>w\<rbrace> \<star> \<lbrace>u\<rbrace>) \<cdot>
                           \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
            using u v w vw' wu assoc_naturality [of "\<lbrace>v\<rbrace>" "\<lbrace>w\<rbrace>" "\<lbrace>u\<rbrace>"]
            by (simp add: eval_simps')
          also have "... = ((\<lbrace>Cod v\<rbrace> \<star> \<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>) \<cdot> (\<lbrace>v\<rbrace> \<star> \<lbrace>w\<rbrace> \<star> \<lbrace>u\<rbrace>)) \<cdot>
                           \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
            using comp_assoc by simp
          also have
            "... = (\<lbrace>v\<rbrace> \<star> \<lbrace>w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot> \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
            using v w u vw' wu I2 red2_in_Hom HcompNml_in_Hom comp_cod_arr
                  interchange [of "\<lbrace>Cod v\<rbrace>" "\<lbrace>v\<rbrace>" "\<lbrace>Cod w \<^bold>\<Down> Cod u\<rbrace>" "\<lbrace>w\<rbrace> \<star> \<lbrace>u\<rbrace>"]
            by (simp add: eval_simps')
          also have "... = ((\<lbrace>v\<rbrace> \<star> \<lbrace>w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u\<rbrace>) \<cdot> (\<lbrace>Dom v\<rbrace> \<star> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>)) \<cdot>
                           \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
            using v w u vw' wu red2_in_Hom HcompNml_in_Hom comp_arr_dom
                  interchange [of "\<lbrace>v\<rbrace>" "\<lbrace>Dom v\<rbrace>" "\<lbrace>w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u\<rbrace>" "\<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>"]
            by (simp add: eval_simps')
          also have "... = (\<lbrace>v\<rbrace> \<star> \<lbrace>w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u\<rbrace>) \<cdot> (\<lbrace>Dom v\<rbrace> \<star> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot>
                           \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
            using comp_assoc by simp
          also have "... = \<lbrace>v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u\<rbrace> \<cdot> (\<lbrace>Dom v\<rbrace> \<star> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot>
                           \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
            using u u' v w vw' wu is_Hcomp_HcompNml HcompNml_Prim [of "w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u" ?f]
            by force
          also have "... = \<lbrace>v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>Dom v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u\<rbrace> \<cdot>
                          (\<lbrace>Dom v\<rbrace> \<star> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot> \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
          proof -
            have "\<lbrace>v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u\<rbrace> \<cdot> (\<lbrace>Dom v\<rbrace> \<star> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot>
                    \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>] =
                  (\<lbrace>v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>Dom v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u\<rbrace>) \<cdot>
                    (\<lbrace>Dom v\<rbrace> \<star> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot> \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
              using u v w vw' wu comp_arr_dom Nml_HcompNml HcompNml_in_Hom
              by (simp add: eval_simps')
            also have "... = \<lbrace>v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>Dom v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u\<rbrace> \<cdot>
                               (\<lbrace>Dom v\<rbrace> \<star> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot> \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
              using comp_assoc by simp
            finally show ?thesis by blast
          qed
          also have "... = \<lbrace>(v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> w) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> u\<rbrace> \<cdot> \<lbrace>(Dom v \<^bold>\<star> Dom w) \<^bold>\<Down> Dom u\<rbrace>"
          proof -
            have "(Dom v \<^bold>\<star> Dom w) \<^bold>\<Down> Dom u
                     = (Dom v \<^bold>\<Down> (Dom w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom u\<^bold>\<rfloor>)) \<^bold>\<cdot> (Dom v \<^bold>\<star> (Dom w \<^bold>\<Down> Dom u)) \<^bold>\<cdot>
                       \<^bold>\<a>\<^bold>[Dom v, Dom w, Dom u\<^bold>]"
              using u u' v w vw' wu by (cases u, simp_all)
            hence
              "\<lbrace>(Dom v \<^bold>\<star> Dom w) \<^bold>\<Down> Dom u\<rbrace>
                     = \<lbrace>Dom v \<^bold>\<Down> (Dom w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u)\<rbrace> \<cdot> (\<lbrace>Dom v\<rbrace> \<star> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot>
                       \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
              using u v w \<alpha>_def by simp
            also have
              "... = \<lbrace>Dom v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u\<rbrace> \<cdot> (\<lbrace>Dom v\<rbrace> \<star> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot>
                             \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
              using X HcompNml_Nml red2_Nml by presburger
            finally have
              "\<lbrace>(Dom v \<^bold>\<star> Dom w) \<^bold>\<Down> Dom u\<rbrace>
                   = \<lbrace>Dom v \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom w \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom u\<rbrace> \<cdot> (\<lbrace>Dom v\<rbrace> \<star> \<lbrace>Dom w \<^bold>\<Down> Dom u\<rbrace>) \<cdot>
                     \<a>[\<lbrace>Dom v\<rbrace>, \<lbrace>Dom w\<rbrace>, \<lbrace>Dom u\<rbrace>]"
              by blast
            thus ?thesis
              using assms v w vw' wu HcompNml_assoc by presburger
          qed
          finally show ?thesis
            using vw HcompNml_Nml by simp
        qed
      qed
      ultimately show ?thesis by blast
    qed

    lemma coherent_Hcomp:
    assumes "Arr t" and "Arr u" and "Src t = Trg u" and "coherent t" and "coherent u"
    shows "coherent (t \<^bold>\<star> u)"
    proof -
      have t: "Arr t \<and> Ide (Dom t) \<and> Ide (Cod t) \<and> Ide \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<and>
               arr \<lbrace>t\<rbrace> \<and> arr \<lbrace>Dom t\<rbrace> \<and> ide \<lbrace>Dom t\<rbrace> \<and> arr \<lbrace>Cod t\<rbrace> \<and> ide \<lbrace>Cod t\<rbrace>"
        using assms Ide_Nmlize_Ide ide_eval_Ide by auto
      have u: "Arr u \<and> Ide (Dom u) \<and> Ide (Cod u) \<and> Ide \<^bold>\<lfloor>Dom u\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>Cod u\<^bold>\<rfloor> \<and>
               arr \<lbrace>u\<rbrace> \<and> arr \<lbrace>Dom u\<rbrace> \<and> ide \<lbrace>Dom u\<rbrace> \<and> arr \<lbrace>Cod u\<rbrace> \<and> ide \<lbrace>Cod u\<rbrace>"
        using assms Ide_Nmlize_Ide ide_eval_Ide by auto
      have "\<lbrace>Cod (t \<^bold>\<star> u)\<^bold>\<down>\<rbrace> \<cdot> (\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace>)
              = (\<lbrace>\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Cod u\<^bold>\<down>\<rbrace>)) \<cdot> (\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace>)"
        using t u eval_red_Hcomp by simp
      also have "... = \<lbrace>\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Cod u\<^bold>\<down>\<rbrace>) \<cdot> (\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace>)"
        using comp_assoc by simp
      also have "... = \<lbrace>\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<star> \<lbrace>\<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace>) \<cdot> (\<lbrace>Dom t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Dom u\<^bold>\<down>\<rbrace>)"
        using assms t u Nmlize_in_Hom red_in_Hom
              interchange [of "\<lbrace>Cod t\<^bold>\<down>\<rbrace>" "\<lbrace>t\<rbrace>" "\<lbrace>Cod u\<^bold>\<down>\<rbrace>" "\<lbrace>u\<rbrace>"]
              interchange [of "\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>" "\<lbrace>Dom t\<^bold>\<down>\<rbrace>" "\<lbrace>\<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace>" "\<lbrace>Dom u\<^bold>\<down>\<rbrace>"]
        by (simp add: eval_simps')
      also have "... = (\<lbrace>\<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Cod u\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace> \<star> \<lbrace>\<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace>)) \<cdot> (\<lbrace>Dom t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Dom u\<^bold>\<down>\<rbrace>)"
        using comp_assoc by simp
      also have "... = (\<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Dom u\<^bold>\<rfloor>\<rbrace>) \<cdot> (\<lbrace>Dom t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Dom u\<^bold>\<down>\<rbrace>)"
        using assms t u Nml_Nmlize Nmlize_in_Hom
              eval_red2_naturality [of "Nmlize t" "Nmlize u"]
        by simp
      also have "... = \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<Down> \<^bold>\<lfloor>Dom u\<^bold>\<rfloor>\<rbrace> \<cdot> (\<lbrace>Dom t\<^bold>\<down>\<rbrace> \<star> \<lbrace>Dom u\<^bold>\<down>\<rbrace>)"
        using comp_assoc by simp
      also have "... = \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>(Dom t \<^bold>\<star> Dom u)\<^bold>\<down>\<rbrace>"
        using t u eval_red_Hcomp by simp
      finally have "\<lbrace>Cod (t \<^bold>\<star> u)\<^bold>\<down>\<rbrace> \<cdot> (\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace>) = \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>(Dom t \<^bold>\<star> Dom u)\<^bold>\<down>\<rbrace>"
        by blast
      thus ?thesis using t u by simp
    qed

    lemma coherent_Vcomp:
    assumes "Arr t" and "Arr u" and "Dom t = Cod u"
    and "coherent t" and "coherent u"
    shows "coherent (t \<^bold>\<cdot> u)"
    proof -
      have t: "Arr t \<and> Ide (Dom t) \<and> Ide (Cod t) \<and> Ide \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>Cod t\<^bold>\<rfloor> \<and>
               arr \<lbrace>t\<rbrace> \<and> arr \<lbrace>Dom t\<rbrace> \<and> ide \<lbrace>Dom t\<rbrace> \<and> arr \<lbrace>Cod t\<rbrace> \<and> ide \<lbrace>Cod t\<rbrace>"
        using assms Ide_Nmlize_Ide ide_eval_Ide by auto
      have u: "Arr u \<and> Ide (Dom u) \<and> Ide (Cod u) \<and> Ide \<^bold>\<lfloor>Dom u\<^bold>\<rfloor> \<and> Ide \<^bold>\<lfloor>Cod u\<^bold>\<rfloor> \<and>
               arr \<lbrace>u\<rbrace> \<and> arr \<lbrace>Dom u\<rbrace> \<and> ide \<lbrace>Dom u\<rbrace> \<and> arr \<lbrace>Cod u\<rbrace> \<and> ide \<lbrace>Cod u\<rbrace>"
        using assms Ide_Nmlize_Ide ide_eval_Ide by auto
      have "\<lbrace>Cod (t \<^bold>\<cdot> u)\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t \<^bold>\<cdot> u\<rbrace> = \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t\<rbrace> \<cdot> \<lbrace>u\<rbrace>"
        using t u by simp
      also have "... = (\<lbrace>Cod t\<^bold>\<down>\<rbrace> \<cdot> \<lbrace>t\<rbrace>) \<cdot> \<lbrace>u\<rbrace>"
      proof -
        have "seq \<lbrace>Cod t\<^bold>\<down>\<rbrace> \<lbrace>t\<rbrace>"
          using assms t red_in_Hom
          by (intro seqI, auto simp add: eval_simps')
        moreover have "seq \<lbrace>t\<rbrace> \<lbrace>u\<rbrace>"
          using assms t u by (auto simp add: eval_simps')
        ultimately show ?thesis
          using comp_assoc by auto
      qed
      also have "... = \<lbrace>\<^bold>\<lfloor>t \<^bold>\<cdot> u\<^bold>\<rfloor>\<rbrace> \<cdot> \<lbrace>Dom (t \<^bold>\<cdot> u)\<^bold>\<down>\<rbrace>"
        using t u assms red_in_Hom Nml_Nmlize comp_assoc
        by (simp add: eval_simps' Nml_implies_Arr eval_VcompNml)
      finally show "coherent (t \<^bold>\<cdot> u)" by blast
    qed

    text \<open>
      The main result: ``Every formal arrow is coherent.''
    \<close>

    theorem coherence:
    assumes "Arr t"
    shows "coherent t"
    proof -
      have "Arr t \<Longrightarrow> coherent t"
      proof (induct t)
        show "\<And>a. Arr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<Longrightarrow> coherent \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0" by simp
        show "\<And>\<mu>. Arr \<^bold>\<langle>\<mu>\<^bold>\<rangle> \<Longrightarrow> coherent \<^bold>\<langle>\<mu>\<^bold>\<rangle>" by simp
        fix u v
        show "\<lbrakk> Arr u \<Longrightarrow> coherent u; Arr v \<Longrightarrow> coherent v \<rbrakk> \<Longrightarrow> Arr (u \<^bold>\<star> v)
                  \<Longrightarrow> coherent (u \<^bold>\<star> v)"
          using coherent_Hcomp by simp
        show "\<lbrakk> Arr u \<Longrightarrow> coherent u; Arr v \<Longrightarrow> coherent v \<rbrakk> \<Longrightarrow> Arr (u \<^bold>\<cdot> v)
                  \<Longrightarrow> coherent (u \<^bold>\<cdot> v)"
          using coherent_Vcomp by simp
        next
        fix t
        assume I: "Arr t \<Longrightarrow> coherent t"
        show Lunit: "Arr \<^bold>\<l>\<^bold>[t\<^bold>] \<Longrightarrow> coherent \<^bold>\<l>\<^bold>[t\<^bold>]"
          using I Ide_Dom coherent_Lunit_Ide Ide_in_Hom
                coherent_Vcomp [of t "\<^bold>\<l>\<^bold>[Dom t\<^bold>]"] Nmlize_Vcomp_Arr_Dom
                eval_in_hom \<ll>.is_natural_1 [of "\<lbrace>t\<rbrace>"]
          by force
        show Runit: "Arr \<^bold>\<r>\<^bold>[t\<^bold>] \<Longrightarrow> coherent \<^bold>\<r>\<^bold>[t\<^bold>]"
          using I Ide_Dom coherent_Runit_Ide Ide_in_Hom ide_eval_Ide
                coherent_Vcomp [of t "\<^bold>\<r>\<^bold>[Dom t\<^bold>]"] Nmlize_Vcomp_Arr_Dom \<rr>_ide_simp
                eval_in_hom \<rr>.is_natural_1 [of "\<lbrace>t\<rbrace>"]
          by force
        show "Arr \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> coherent \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
        proof -
          assume "Arr \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
          hence t: "Arr t" by simp
          have "coherent (\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t)"
            using t I Ide_Cod coherent_Lunit'_Ide Ide_in_Hom coherent_Vcomp [of "\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>]" t]
                  Arr.simps(6) Dom.simps(6) Dom_Cod Ide_implies_Arr
            by presburger
          moreover have "\<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = \<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t\<rbrace>"
            using t \<ll>'.is_natural_2 [of "\<lbrace>t\<rbrace>"]
            by (simp add: eval_simps(5))
          ultimately show ?thesis
            using t Nmlize_Vcomp_Cod_Arr by simp
        qed
        show "Arr \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>] \<Longrightarrow> coherent \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
        proof -
          assume "Arr \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]"
          hence t: "Arr t" by simp
          have "coherent (\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t)"
            using t I Ide_Cod coherent_Runit'_Ide Ide_in_Hom coherent_Vcomp [of "\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>]" t]
                  Arr.simps(8) Dom.simps(8) Dom_Cod Ide_implies_Arr
            by presburger
          moreover have "\<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[t\<^bold>]\<rbrace> = \<lbrace>\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[Cod t\<^bold>] \<^bold>\<cdot> t\<rbrace>"
            using t \<rr>'.is_natural_2 [of "\<lbrace>t\<rbrace>"]
            by (simp add: eval_simps(5))
          ultimately show ?thesis
            using t Nmlize_Vcomp_Cod_Arr by simp
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
          have tu: "Src t = Trg u" using tuv by simp
          have uv: "Src u = Trg v" using tuv by simp
          have "coherent ((t \<^bold>\<star> u \<^bold>\<star> v) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>])"
          proof -
            have "Arr (t \<^bold>\<star> u \<^bold>\<star> v) \<and> coherent (t \<^bold>\<star> u \<^bold>\<star> v)"
              using t u v tu uv tuv I1 I2 I3 coherent_Hcomp Arr.simps(3) Trg.simps(3)
              by presburger
            moreover have "Arr \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v tu uv Ide_Dom by simp
            moreover have "coherent \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v tu uv Src_Dom Trg_Dom Ide_Dom coherent_Assoc_Ide by metis
            moreover have "Dom (t \<^bold>\<star> u \<^bold>\<star> v) = Cod \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v by simp
            ultimately show ?thesis
              using t u v coherent_Vcomp by blast
          qed
          moreover have "VPar \<^bold>\<a>\<^bold>[t, u, v\<^bold>] ((t \<^bold>\<star> u \<^bold>\<star> v) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>])"
            using t u v tu uv Ide_Dom by simp
          moreover have "\<^bold>\<lfloor>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>(t \<^bold>\<star> u \<^bold>\<star>  v) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]\<^bold>\<rfloor>"
          proof -
            have "(\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>
                     = (\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> ((\<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom u\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom v\<^bold>\<rfloor>)"
            proof -
              have 1: "Nml \<^bold>\<lfloor>t\<^bold>\<rfloor> \<and> Nml \<^bold>\<lfloor>u\<^bold>\<rfloor> \<and> Nml \<^bold>\<lfloor>v\<^bold>\<rfloor> \<and>
                       Dom \<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> \<and> Dom \<^bold>\<lfloor>u\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom u\<^bold>\<rfloor> \<and> Dom \<^bold>\<lfloor>v\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom v\<^bold>\<rfloor>"
                using t u v Nml_Nmlize by blast
              moreover have "Nml (\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>)"
                using 1 t u tu Nmlize_Src Nmlize_Trg Nml_HcompNml(1)
                by presburger
              moreover have "\<And>t. Arr t \<Longrightarrow> \<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<cdot>\<^bold>\<rfloor> \<^bold>\<lfloor>Dom t\<^bold>\<rfloor> = \<^bold>\<lfloor>t\<^bold>\<rfloor>"
                using t Nmlize_Vcomp_Arr_Dom by simp
              moreover have "Dom \<^bold>\<lfloor>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom \<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor>"
                using Nml_Nmlize tuv by blast
              ultimately show ?thesis
                using t u v tu uv tuv 1 HcompNml_assoc Nml_HcompNml
                      Nml_Nmlize VcompNml_Nml_Dom [of "(\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>"]
                by auto
            qed
            thus ?thesis
              using t u v Nmlize_Vcomp_Arr_Dom VcompNml_HcompNml Nml_Nmlize
              by simp
          qed
          moreover have "\<lbrace>\<^bold>\<a>\<^bold>[t, u, v\<^bold>]\<rbrace> = \<lbrace>(t \<^bold>\<star> u \<^bold>\<star> v) \<^bold>\<cdot> \<^bold>\<a>\<^bold>[Dom t, Dom u, Dom v\<^bold>]\<rbrace>"
            using t u v tu uv Ide_Dom comp_cod_arr ide_eval_Ide \<alpha>_def
            apply (simp add: eval_simps')
            using assoc_is_natural_1 arr_eval_Arr eval_simps'(2-4) by presburger
          ultimately show "coherent \<^bold>\<a>\<^bold>[t, u, v\<^bold>]" by argo
        qed
        show "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] \<Longrightarrow> coherent \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]"
        proof -
          assume tuv: "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]"
          have t: "Arr t" using tuv by simp
          have u: "Arr u" using tuv by simp
          have v: "Arr v" using tuv by simp
          have tu: "Src t = Trg u" using tuv by simp
          have uv: "Src u = Trg v" using tuv by simp
          have "coherent (((t \<^bold>\<star> u) \<^bold>\<star> v) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>])"
          proof -
            have "Arr ((t \<^bold>\<star> u) \<^bold>\<star> v) \<and> coherent ((t \<^bold>\<star> u) \<^bold>\<star> v)"
              using t u v tu uv tuv I1 I2 I3 coherent_Hcomp Arr.simps(3) Src.simps(3)
              by presburger
            moreover have "Arr \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v tu uv Ide_Dom by simp
            moreover have "coherent \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v tu uv Src_Dom Trg_Dom Ide_Dom coherent_Assoc'_Ide
              by metis
            moreover have "Dom ((t \<^bold>\<star> u) \<^bold>\<star> v) = Cod \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]"
              using t u v by simp
            ultimately show ?thesis
              using t u v coherent_Vcomp by metis
          qed
          moreover have "VPar \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>] (((t \<^bold>\<star> u) \<^bold>\<star> v) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>])"
            using t u v tu uv Ide_Dom by simp
          moreover have "\<^bold>\<lfloor>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<^bold>\<rfloor> = \<^bold>\<lfloor>((t \<^bold>\<star> u) \<^bold>\<star> v) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]\<^bold>\<rfloor>"
            using t u v tu uv Nmlize_Vcomp_Arr_Dom VcompNml_HcompNml Nml_Nmlize
                  HcompNml_assoc Nml_HcompNml HcompNml_in_Hom
                  VcompNml_Nml_Dom [of "(\<^bold>\<lfloor>t\<^bold>\<rfloor> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>u\<^bold>\<rfloor>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> \<^bold>\<lfloor>v\<^bold>\<rfloor>"]
            by simp
          moreover have "\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = \<lbrace>((t \<^bold>\<star> u) \<^bold>\<star> v) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]\<rbrace>"
          proof -
            have 1: "VVV.arr (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"
              using tuv \<alpha>'.preserves_reflects_arr arr_eval_Arr eval.simps(10)
              by (metis (no_types, lifting))
            have "\<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]\<rbrace> = ((\<lbrace>t\<rbrace> \<star> \<lbrace>u\<rbrace>) \<star> \<lbrace>v\<rbrace>) \<cdot> \<a>\<^sup>-\<^sup>1[dom \<lbrace>t\<rbrace>, dom \<lbrace>u\<rbrace>, dom \<lbrace>v\<rbrace>]"
            proof -
              have "VVV.arr (\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"
                using tuv \<alpha>'.preserves_reflects_arr arr_eval_Arr eval.simps(10)
                by (metis (no_types, lifting))
              thus ?thesis
                using t u v \<alpha>'.is_natural_1 [of "(\<lbrace>t\<rbrace>, \<lbrace>u\<rbrace>, \<lbrace>v\<rbrace>)"] HoHV_def \<a>'_def
                by simp
            qed
            also have "... = \<lbrace>((t \<^bold>\<star> u) \<^bold>\<star> v) \<^bold>\<cdot> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[Dom t, Dom u, Dom v\<^bold>]\<rbrace>"
              by (simp add: eval_simps'(4) t u v \<a>'_def)
            finally show ?thesis by blast
          qed
          ultimately show "coherent \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[t, u, v\<^bold>]" by argo
        qed
      qed
      thus ?thesis using assms by blast
    qed

    corollary eval_eqI:
    assumes "VPar t u" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
    shows "\<lbrace>t\<rbrace> = \<lbrace>u\<rbrace>"
      using assms coherence canonical_factorization by simp

    text \<open>
      The following allows us to prove that two 1-cells in a bicategory are isomorphic
      simply by expressing them as the evaluations of terms having the same normalization.
      The benefits are: (1) we do not have to explicitly exhibit the isomorphism,
      which is canonical and is obtained by evaluating the reductions of the terms
      to their normalizations, and (2) the normalizations can be computed automatically
      by the simplifier.
    \<close>

    lemma canonically_isomorphicI:
    assumes "f = \<lbrace>t\<rbrace>" and "g = \<lbrace>u\<rbrace>" and "Ide t" and "Ide u" and "\<^bold>\<lfloor>t\<^bold>\<rfloor> = \<^bold>\<lfloor>u\<^bold>\<rfloor>"
    shows "f \<cong> g"
    proof -
      have "f \<cong> \<lbrace>t\<rbrace>"
        using assms isomorphic_reflexive ide_eval_Ide by blast
      also have "... \<cong> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>"
      proof -
        have "\<guillemotleft>\<lbrace>t\<^bold>\<down>\<rbrace> : \<lbrace>t\<rbrace> \<Rightarrow> \<lbrace>\<^bold>\<lfloor>t\<^bold>\<rfloor>\<rbrace>\<guillemotright> \<and> iso \<lbrace>t\<^bold>\<down>\<rbrace>"
          using assms(1,3) Can_red iso_eval_Can red_in_Hom(2) eval_in_hom(2) by fastforce
        thus ?thesis
          using isomorphic_def by blast
      qed
      also have "... \<cong> \<lbrace>\<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace>"
        using assms isomorphic_reflexive
        by (simp add: Ide_Nmlize_Ide ide_eval_Ide)
      also have "... \<cong> \<lbrace>u\<rbrace>"
      proof -
        have "\<guillemotleft>\<lbrace>u\<^bold>\<down>\<rbrace> : \<lbrace>u\<rbrace> \<Rightarrow> \<lbrace>\<^bold>\<lfloor>u\<^bold>\<rfloor>\<rbrace>\<guillemotright> \<and> iso \<lbrace>u\<^bold>\<down>\<rbrace>"
          using assms(2,4) Can_red iso_eval_Can red_in_Hom(2) eval_in_hom(2) by fastforce
        thus ?thesis
          using isomorphic_def isomorphic_symmetric by blast
      qed
      also have "... \<cong> g"
        using assms isomorphic_reflexive ide_eval_Ide by blast
      finally show ?thesis by simp
    qed

  end

end
