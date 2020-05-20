(*  Title:       Strictness
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Strictness"

theory Strictness
imports Category3.ConcreteCategory Pseudofunctor CanonicalIsos
begin

  text \<open>
    In this section we consider bicategories in which some or all of the canonical isomorphisms
    are assumed to be identities.  A \emph{normal} bicategory is one in which the unit
    isomorphisms are identities, so that unit laws for horizontal composition are satisfied
    ``on the nose''.
    A \emph{strict} bicategory (also known as a \emph{2-category}) is a bicategory in which both
    the unit and associativity isomoprhisms are identities, so that horizontal composition is
    strictly associative as well as strictly unital.

    From any given bicategory \<open>B\<close> we may construct a related strict bicategory \<open>S\<close>,
    its \emph{strictification}, together with a pseudofunctor that embeds \<open>B\<close> in \<open>S\<close>.
    The Strictness Theorem states that this pseudofunctor is an equivalence pseudofunctor,
    so that bicategory \<open>B\<close> is biequivalent to its strictification.
    The Strictness Theorem is often used informally to justify suppressing canonical
    isomorphisms; which amounts to proving a theorem about 2-categories and asserting that
    it holds for all bicategories.  Here we are working formally, so we can't just wave
    our hands and mutter something about the Strictness Theorem when we want to avoid
    dealing with units and associativities.  However, in cases where we can establish that the
    property we would like to prove is reflected by the embedding of a bicategory in its
    strictification, then we can formally apply the Strictness Theorem to generalize to all
    bicategories a result proved for 2-categories.  We will apply this approach here to
    simplify the proof of some facts about internal equivalences in a bicategory.
  \<close>

  subsection "Normal and Strict Bicategories"

  text \<open>
    A \emph{normal} bicategory is one in which the unit isomorphisms are identities,
    so that unit laws for horizontal composition are satisfied ``on the nose''.
  \<close>

  locale normal_bicategory =
    bicategory +
  assumes strict_lunit: "\<And>f. ide f \<Longrightarrow> \<l>[f] = f"
  and strict_runit: "\<And>f. ide f \<Longrightarrow> \<r>[f] = f"
  begin

    lemma strict_unit:
    assumes "obj a"
    shows "ide \<i>[a]"
      using assms strict_runit unitor_coincidence(2) [of a] by auto

    lemma strict_lunit':
    assumes "ide f"
    shows "\<l>\<^sup>-\<^sup>1[f] = f"
      using assms strict_lunit by simp

    lemma strict_runit':
    assumes "ide f"
    shows "\<r>\<^sup>-\<^sup>1[f] = f"
      using assms strict_runit by simp

    lemma hcomp_obj_arr:
    assumes "obj b" and "arr f" and "b = trg f"
    shows "b \<star> f = f"
      using assms strict_lunit
      by (metis comp_arr_dom comp_ide_arr ide_cod ide_dom lunit_naturality)

    lemma hcomp_arr_obj:
    assumes "arr f" and "obj a" and "src f = a"
    shows "f \<star> a = f"
      using assms strict_runit
      by (metis comp_arr_dom comp_ide_arr ide_cod ide_dom runit_naturality)

  end

  text \<open>
    A \emph{strict} bicategory is a normal bicategory in which the associativities are also
    identities, so that associativity of horizontal composition holds ``on the nose''.
  \<close>

  locale strict_bicategory =
    normal_bicategory +
  assumes strict_assoc: "\<And>f g h. \<lbrakk>ide f; ide g; ide h; src f = trg g; src g = trg h\<rbrakk> \<Longrightarrow>
                                  ide \<a>[f, g, h]"
  begin

    lemma strict_assoc':
    assumes "ide f" and "ide g" and "ide h" and "src f = trg g" and "src g = trg h"
    shows "ide \<a>\<^sup>-\<^sup>1[f, g, h]"
      using assms strict_assoc by simp

    lemma hcomp_assoc:
    shows "(\<mu> \<star> \<nu>) \<star> \<tau> = \<mu> \<star> \<nu> \<star> \<tau>"
    proof (cases "hseq \<mu> \<nu> \<and> hseq \<nu> \<tau>")
      show "\<not> (hseq \<mu> \<nu> \<and> hseq \<nu> \<tau>) \<Longrightarrow> ?thesis"
        by (metis hseqE hseq_char' match_1 match_2)
      show "hseq \<mu> \<nu> \<and> hseq \<nu> \<tau> \<Longrightarrow> ?thesis"
      proof -
        assume 1: "hseq \<mu> \<nu> \<and> hseq \<nu> \<tau>"
        have 2: "arr \<mu> \<and> arr \<nu> \<and> arr \<tau> \<and> src \<mu> = trg \<nu> \<and> src \<nu> = trg \<tau>"
          using 1 by blast
        have "(\<mu> \<star> \<nu>) \<star> \<tau> = \<a>[cod \<mu>, cod \<nu>, cod \<tau>] \<cdot> ((\<mu> \<star> \<nu>) \<star> \<tau>)"
          using 1 assoc_in_hom strict_assoc comp_cod_arr assoc_simps(4) hseq_char
          by simp
        also have "... = (\<mu> \<star> \<nu> \<star> \<tau>) \<cdot> \<a>[dom \<mu>, dom \<nu>, dom \<tau>]"
          using 1 assoc_naturality by auto
        also have "... = \<mu> \<star> \<nu> \<star> \<tau>"
          using 2 assoc_in_hom [of "dom \<mu>" "dom \<nu>" "dom \<tau>"] strict_assoc comp_arr_dom
          by auto
        finally show ?thesis by simp
      qed
    qed

    text \<open>
      In a strict bicategory, every canonical isomorphism is an identity.
    \<close>

    interpretation bicategorical_language ..
    interpretation E: self_evaluation_map V H \<a> \<i> src trg ..
    notation E.eval ("\<lbrace>_\<rbrace>")

    lemma ide_eval_Can:
    assumes "Can t"
    shows "ide \<lbrace>t\<rbrace>"
    proof -
      have 1: "\<And>u1 u2. \<lbrakk> ide \<lbrace>u1\<rbrace>; ide \<lbrace>u2\<rbrace>; Arr u1; Arr u2; Dom u1 = Cod u2 \<rbrakk>
                           \<Longrightarrow> ide (\<lbrace>u1\<rbrace> \<cdot> \<lbrace>u2\<rbrace>)"
        by (metis (no_types, lifting) E.eval_simps'(4-5) comp_ide_self ide_char)
      have "\<And>u. Can u \<Longrightarrow> ide \<lbrace>u\<rbrace>"
      proof -
        fix u
        show "Can u \<Longrightarrow> ide \<lbrace>u\<rbrace>"
          (* TODO: Rename \<ll>_ide_simp \<rr>_ide_simp to \<ll>_ide_eq \<rr>_ide_eq *)
          using 1 \<alpha>_def \<a>'_def strict_lunit strict_runit strict_assoc strict_assoc'
                \<ll>_ide_simp \<rr>_ide_simp Can_implies_Arr comp_ide_arr E.eval_simps'(2-3)
          apply (induct u) by auto
      qed
      thus ?thesis
        using assms by simp
    qed

    lemma ide_can:
    assumes "Ide f" and "Ide g" and "\<^bold>\<lfloor>f\<^bold>\<rfloor> = \<^bold>\<lfloor>g\<^bold>\<rfloor>"
    shows "ide (can g f)"
    proof -
      have "Can (Inv (g\<^bold>\<down>) \<^bold>\<cdot> f\<^bold>\<down>)"
        using assms Can_red Can_Inv red_in_Hom Inv_in_Hom by simp
      thus ?thesis
        using assms can_def ide_eval_Can by presburger
    qed

  end

  subsection "Strictification"

  (*
   * TODO: Perhaps change the typeface used for a symbol that stands for a bicategory;
   * for example, to avoid the clashes here between B used as the name of a bicategory
   * and B used to denote a syntactic identity term.
   *)

  text \<open>
    The Strictness Theorem asserts that every bicategory is biequivalent to a
    strict bicategory.  More specifically, it shows how to construct, given an arbitrary
    bicategory, a strict bicategory (its \emph{strictification}) that is biequivalent to it.
    Consequently, given a property \<open>P\<close> of bicategories that is ``bicategorical''
    (\emph{i.e.}~respects biequivalence), if we want to show that \<open>P\<close> holds for a bicategory \<open>B\<close>
    then it suffices to show that \<open>P\<close> holds for the strictification of \<open>B\<close>, and if we want to show
    that \<open>P\<close> holds for all bicategories, it is sufficient to show that it holds for all
    strict bicategories.  This is very useful, because it becomes quite tedious, even
    with the aid of a proof assistant, to do ``diagram chases'' with all the units and
    associativities fully spelled out.

    Given a bicategory \<open>B\<close>, the strictification \<open>S\<close> of \<open>B\<close> may be constructed as the bicategory
    whose arrows are triples \<open>(A, B, \<mu>)\<close>, where \<open>X\<close> and \<open>Y\<close> are ``normal identity terms''
    (essentially, nonempty horizontally composable lists of 1-cells of \<open>B\<close>) having the same
    syntactic source and target, and \<open>\<guillemotleft>\<mu> : \<lbrace>X\<rbrace> \<Rightarrow> \<lbrace>Y\<rbrace>\<guillemotright>\<close> in \<open>B\<close>.
    Vertical composition in \<open>S\<close> is given by composition of the underlying arrows in \<open>B\<close>.
    Horizontal composition in \<open>S\<close> is given by \<open>(A, B, \<mu>) \<star> (A', B', \<mu>') = (AA', BB', \<nu>)\<close>,
    where \<open>AA'\<close> and \<open>BB'\<close> denote concatenations of lists and where \<open>\<nu>\<close> is defined as the
    composition \<open>can BB' (B \<^bold>\<star> B') \<cdot> (\<mu> \<star> \<mu>') \<cdot> can (A \<^bold>\<star> A') AA'\<close>, where \<open>can (A \<^bold>\<star> A') AA'\<close> and
    \<open>can BB' (B \<^bold>\<star> B')\<close> are canonical isomorphisms in \<open>B\<close>.  The canonical isomorphism
    \<open>can (A \<^bold>\<star> A') AA'\<close> corresponds to taking a pair of lists \<open>A \<^bold>\<star> A'\<close> and
    ``shifting the parentheses to the right'' to obtain a single list \<open>AA'\<close>.
    The canonical isomorphism can \<open>BB' (B \<^bold>\<star> B')\<close> corresponds to the inverse rearrangement.

    The bicategory \<open>B\<close> embeds into its strictification \<open>S\<close> via the functor \<open>UP\<close> that takes
    each arrow \<open>\<mu>\<close> of \<open>B\<close> to \<open>(\<^bold>\<langle>dom \<mu>\<^bold>\<rangle>, \<^bold>\<langle>cod \<mu>\<^bold>\<rangle>, \<mu>)\<close>, where \<open>\<^bold>\<langle>dom \<mu>\<^bold>\<rangle>\<close> and \<open>\<^bold>\<langle>cod \<mu>\<^bold>\<rangle>\<close> denote
    one-element lists.  This mapping extends to a pseudofunctor.
    There is also a pseudofunctor \<open>DN\<close>, which maps \<open>(A, B, \<mu>)\<close> in \<open>S\<close> to \<open>\<mu>\<close> in \<open>B\<close>;
    this is such that \<open>DN o UP\<close> is the identity on \<open>B\<close> and \<open>UP o DN\<close> is equivalent to the
    identity on \<open>S\<close>, so we obtain a biequivalence between \<open>B\<close> and \<open>S\<close>.

    It seems difficult to find references that explicitly describe a strictification
    construction in elementary terms like this (in retrospect, it ought to have been relatively
    easy to rediscover such a construction, but my thinking got off on the wrong track).
    One reference that I did find useful was \cite{unapologetic-strictification},
    which discusses strictification for monoidal categories.
  \<close>

  locale strictified_bicategory =
    B: bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
  for V\<^sub>B :: "'a comp"                  (infixr "\<cdot>\<^sub>B" 55)
  and H\<^sub>B :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"           (infixr "\<star>\<^sub>B" 53)
  and \<a>\<^sub>B :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"      ("\<a>\<^sub>B[_, _, _]")
  and \<i>\<^sub>B :: "'a \<Rightarrow> 'a"                  ("\<i>\<^sub>B[_]")
  and src\<^sub>B :: "'a \<Rightarrow> 'a"
  and trg\<^sub>B :: "'a \<Rightarrow> 'a"
  begin

    sublocale E: self_evaluation_map V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B ..

    notation B.in_hhom  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")
    notation B.in_hom  ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>B _\<guillemotright>")

    notation E.eval ("\<lbrace>_\<rbrace>")
    notation E.Nmlize ("\<^bold>\<lfloor>_\<^bold>\<rfloor>")

    text \<open>
      The following gives the construction of a bicategory whose arrows are triples \<open>(A, B, \<mu>)\<close>,
      where \<open>Nml A \<and> Ide A\<close>, \<open>Nml B \<and> Ide B\<close>, \<open>Src A = Src B\<close>, \<open>Trg A = Trg B\<close>, and \<open>\<mu> : \<lbrace>A\<rbrace> \<Rightarrow> \<lbrace>B\<rbrace>\<close>.
      We use @{locale concrete_category} to construct the vertical composition, so formally the
      arrows of the bicategory will be of the form \<open>MkArr A B \<mu>\<close>.
    \<close>

    text \<open>
      The 1-cells of the bicategory correspond to normal, identity terms \<open>A\<close>
      in the bicategorical language associated with \<open>B\<close>.
    \<close>

    abbreviation IDE
    where "IDE \<equiv> {A. E.Nml A \<and> E.Ide A}"

    text \<open>
      If terms \<open>A\<close> and \<open>B\<close> determine 1-cells of the strictification and have a
      common source and target, then the 2-cells between these 1-cells correspond
      to arrows \<open>\<mu>\<close> of the underlying bicategory such that \<open>\<guillemotleft>\<mu> : \<lbrace>A\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>B\<rbrace>\<guillemotright>\<close>.
    \<close>

    abbreviation HOM
    where "HOM A B \<equiv> {\<mu>. E.Src A = E.Src B \<and> E.Trg A = E.Trg B \<and> \<guillemotleft>\<mu> : \<lbrace>A\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>B\<rbrace>\<guillemotright>}"

    text \<open>
      The map taking term \<open>A \<in> OBJ\<close> to its evaluation \<open>\<lbrace>A\<rbrace> \<in> HOM A A\<close> defines the
      embedding of 1-cells as identity 2-cells.
    \<close>

    abbreviation EVAL
    where "EVAL \<equiv> E.eval"

    sublocale concrete_category IDE HOM EVAL \<open>\<lambda>_ _ _ \<mu> \<nu>. \<mu> \<cdot>\<^sub>B \<nu>\<close>
      using E.ide_eval_Ide B.comp_arr_dom B.comp_cod_arr B.comp_assoc
      by (unfold_locales, auto)

    lemma is_concrete_category:
    shows "concrete_category IDE HOM EVAL (\<lambda>_ _ _ \<mu> \<nu>. \<mu> \<cdot>\<^sub>B \<nu>)"
      ..

    abbreviation vcomp     (infixr "\<cdot>" 55)
    where "vcomp \<equiv> COMP"

    lemma arr_char:
    shows "arr F \<longleftrightarrow>
           E.Nml (Dom F) \<and> E.Ide (Dom F) \<and> E.Nml (Cod F) \<and> E.Ide (Cod F) \<and>
           E.Src (Dom F) = E.Src (Cod F) \<and> E.Trg (Dom F) = E.Trg (Cod F) \<and>
           \<guillemotleft>Map F : \<lbrace>Dom F\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod F\<rbrace>\<guillemotright> \<and> F \<noteq> Null"
      using arr_char by auto

    lemma arrI (* [intro] *):
    assumes "E.Nml (Dom F)" and "E.Ide (Dom F)" and "E.Nml (Cod F)" and "E.Ide (Cod F)"
    and "E.Src (Dom F) = E.Src (Cod F)" and "E.Trg (Dom F) = E.Trg (Cod F)"
    and "\<guillemotleft>Map F : \<lbrace>Dom F\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod F\<rbrace>\<guillemotright>" and "F \<noteq> Null"
    shows "arr F"
      using assms arr_char by blast

    lemma arrE [elim]:
    assumes "arr F"
    shows "(\<lbrakk> E.Nml (Dom F); E.Ide (Dom F); E.Nml (Cod F); E.Ide (Cod F);
              E.Src (Dom F) = E.Src (Cod F); E.Trg (Dom F) = E.Trg (Cod F);
              \<guillemotleft>Map F : \<lbrace>Dom F\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod F\<rbrace>\<guillemotright>; F \<noteq> Null \<rbrakk> \<Longrightarrow> T) \<Longrightarrow> T"
      using assms arr_char by simp

    lemma ide_char:
    shows "ide F \<longleftrightarrow> endo F \<and> B.ide (Map F)"
    proof
      show "ide F \<Longrightarrow> endo F \<and> B.ide (Map F)"
        using ide_char by (simp add: E.ide_eval_Ide)
      show "endo F \<and> B.ide (Map F) \<Longrightarrow> ide F"
        by (metis (no_types, lifting) B.ide_char B.in_homE arr_char ide_char
            mem_Collect_eq seq_char)
    qed

    lemma ideI [intro]:
    assumes "arr F" and "Dom F = Cod F" and "B.ide (Map F)"
    shows "ide F"
      using assms ide_char dom_char cod_char seq_char by presburger

    lemma ideE [elim]:
    assumes "ide F"
    shows "(\<lbrakk> arr F; Dom F = Cod F; B.ide (Map F); Map F = \<lbrace>Dom F\<rbrace>;
              Map F = \<lbrace>Cod F\<rbrace> \<rbrakk> \<Longrightarrow> T) \<Longrightarrow> T"
    proof -
      assume 1: "\<lbrakk> arr F; Dom F = Cod F; B.ide (Map F); Map F = \<lbrace>Dom F\<rbrace>;
                   Map F = \<lbrace>Cod F\<rbrace> \<rbrakk> \<Longrightarrow> T"
      show T
      proof -
        have "arr F"
          using assms by auto
        moreover have "Dom F = Cod F"
          using assms ide_char dom_char cod_char
          by (metis (no_types, lifting) Dom_cod calculation ideD(3))
        moreover have "B.ide (Map F)"
          using assms ide_char by blast
        moreover have "Map F = \<lbrace>Dom F\<rbrace>"
          using assms ide_char dom_char Map_ide(1) by blast
        ultimately show T
          using 1 by simp
      qed
    qed

    text \<open>
      Source and target are defined by the corresponding syntactic operations on terms.
    \<close>

    definition src
    where "src F \<equiv> if arr F then MkIde (E.Src (Dom F)) else null"

    definition trg
    where "trg F \<equiv> if arr F then MkIde (E.Trg (Dom F)) else null"

    lemma src_simps [simp]:
    assumes "arr F"
    shows "Dom (src F) = E.Src (Dom F)" and "Cod (src F) = E.Src (Dom F)"
    and "Map (src F) = \<lbrace>E.Src (Dom F)\<rbrace>"
      using assms src_def arr_char by auto

    lemma trg_simps [simp]:
    assumes "arr F"
    shows "Dom (trg F) = E.Trg (Dom F)" and "Cod (trg F) = E.Trg (Dom F)"
    and "Map (trg F) = \<lbrace>E.Trg (Dom F)\<rbrace>"
      using assms trg_def arr_char by auto

    interpretation src: endofunctor vcomp src
      using src_def comp_char
      apply (unfold_locales)
          apply auto[4]
    proof -
      show "\<And>g f. seq g f \<Longrightarrow> src (g \<cdot> f) = src g \<cdot> src f"
      proof -
        fix g f
        assume gf: "seq g f"
        have "src (g \<cdot> f) = MkIde (E.Src (Dom (g \<cdot> f)))"
          using gf src_def comp_char by simp
        also have "... = MkIde (E.Src (Dom f))"
          using gf by (simp add: seq_char)
        also have "... = MkIde (E.Src (Dom g)) \<cdot> MkIde (E.Src (Dom f))"
          using gf seq_char by auto
        also have "... = src g \<cdot> src f"
          using gf src_def comp_char by auto
        finally show "src (g \<cdot> f) = src g \<cdot> src f" by blast
      qed
    qed

    interpretation trg: endofunctor vcomp trg
      using trg_def comp_char
      apply (unfold_locales)
          apply auto[4]
    proof -
      show "\<And>g f. seq g f \<Longrightarrow> trg (g \<cdot> f) = trg g \<cdot> trg f"
      proof -
        fix g f
        assume gf: "seq g f"
        have "trg (g \<cdot> f) = MkIde (E.Trg (Dom (g \<cdot> f)))"
          using gf trg_def comp_char by simp
        also have "... = MkIde (E.Trg (Dom f))"
          using gf by (simp add: seq_char)
        also have "... = MkIde (E.Trg (Dom g)) \<cdot> MkIde (E.Trg (Dom f))"
          using gf seq_char by auto
        also have "... = trg g \<cdot> trg f"
          using gf trg_def comp_char by auto
        finally show "trg (g \<cdot> f) = trg g \<cdot> trg f" by blast
      qed
    qed

    interpretation horizontal_homs vcomp src trg
      using src_def trg_def Cod_in_Obj Map_in_Hom
      by (unfold_locales, auto)

    notation in_hhom  ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    definition hcomp    (infixr "\<star>" 53)
    where "\<mu> \<star> \<nu> \<equiv> if arr \<mu> \<and> arr \<nu> \<and> src \<mu> = trg \<nu>
                   then MkArr (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>)
                              (B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) (Cod \<mu> \<^bold>\<star> Cod \<nu>) \<cdot>\<^sub>B
                                (Map \<mu> \<star>\<^sub>B Map \<nu>) \<cdot>\<^sub>B
                                B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>))
                   else null"

    lemma arr_hcomp:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<mu> = trg \<nu>"
    shows "arr (\<mu> \<star> \<nu>)"
    proof -
      have 1: "E.Ide (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<and> E.Nml (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<and>
               E.Ide (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<and> E.Nml (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>)"
        using assms arr_char src_def trg_def E.Ide_HcompNml E.Nml_HcompNml(1) by auto
      moreover
      have "\<guillemotleft>B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) (Cod \<mu> \<^bold>\<star> Cod \<nu>) \<cdot>\<^sub>B (Map \<mu> \<star>\<^sub>B Map \<nu>) \<cdot>\<^sub>B
               B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) :
                  \<lbrace>Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>\<rbrace>\<guillemotright>"
      proof -
        have "\<guillemotleft>Map \<mu> \<star>\<^sub>B Map \<nu> : \<lbrace>Dom \<mu> \<^bold>\<star> Dom \<nu>\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod \<mu> \<^bold>\<star> Cod \<nu>\<rbrace>\<guillemotright>"
          using assms arr_char dom_char cod_char src_def trg_def E.eval_simps'(2-3)
          by auto
        moreover
        have "\<guillemotleft>B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) :
                  \<lbrace>Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Dom \<mu> \<^bold>\<star> Dom \<nu>\<rbrace>\<guillemotright> \<and>
               \<guillemotleft>B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) (Cod \<mu> \<^bold>\<star> Cod \<nu>) :
                  \<lbrace>Cod \<mu> \<^bold>\<star> Cod \<nu>\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>\<rbrace>\<guillemotright>"
          using assms 1 arr_char src_def trg_def
          apply (intro conjI B.in_homI) by auto
        ultimately show ?thesis by auto
      qed
      moreover have "E.Src (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) = E.Src (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<and>
                     E.Trg (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) = E.Trg (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>)"
        using assms arr_char src_def trg_def
        by (simp add: E.Src_HcompNml E.Trg_HcompNml)
      ultimately show ?thesis
        unfolding hcomp_def
        using assms by (intro arrI, auto)
    qed

    lemma src_hcomp [simp]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<mu> = trg \<nu>"
    shows "src (\<mu> \<star> \<nu>) = src \<nu>"
      using assms arr_char hcomp_def src_def trg_def arr_hcomp E.Src_HcompNml by simp

    lemma trg_hcomp [simp]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<mu> = trg \<nu>"
    shows "trg (hcomp \<mu> \<nu>) = trg \<mu>"
      using assms arr_char hcomp_def src_def trg_def arr_hcomp E.Trg_HcompNml by simp

    lemma hseq_char:
    shows "arr (\<mu> \<star> \<nu>) \<longleftrightarrow> arr \<mu> \<and> arr \<nu> \<and> src \<mu> = trg \<nu>"
      using arr_hcomp hcomp_def by simp

    lemma Dom_hcomp [simp]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<mu> = trg \<nu>"
    shows "Dom (\<mu> \<star> \<nu>) = Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>"
      using assms hcomp_def [of \<mu> \<nu>] by simp

    lemma Cod_hcomp [simp]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<mu> = trg \<nu>"
    shows "Cod (\<mu> \<star> \<nu>) = Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>"
      using assms hcomp_def [of \<mu> \<nu>] by simp

    lemma Map_hcomp [simp]:
    assumes "arr \<mu>" and "arr \<nu>" and "src \<mu> = trg \<nu>"
    shows "Map (\<mu> \<star> \<nu>) = B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) (Cod \<mu> \<^bold>\<star> Cod \<nu>) \<cdot>\<^sub>B
                           (Map \<mu> \<star>\<^sub>B Map \<nu>) \<cdot>\<^sub>B
                           B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>)"
      using assms hcomp_def [of \<mu> \<nu>] by simp

    interpretation VxV: product_category vcomp vcomp ..
    interpretation VV: subcategory VxV.comp
                          \<open>\<lambda>\<mu>\<nu>. arr (fst \<mu>\<nu>) \<and> arr (snd \<mu>\<nu>) \<and> src (fst \<mu>\<nu>) = trg (snd \<mu>\<nu>)\<close>
      using subcategory_VV by simp

    interpretation H: "functor" VV.comp vcomp \<open>\<lambda>\<mu>\<nu>. hcomp (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close>
    proof
      show "\<And>f. \<not> VV.arr f \<Longrightarrow> fst f \<star> snd f = null"
        using hcomp_def by auto
      show A: "\<And>f. VV.arr f \<Longrightarrow> arr (fst f \<star> snd f)"
        using VV.arrE hseq_char by blast
      show "\<And>f. VV.arr f \<Longrightarrow> dom (fst f \<star> snd f) = fst (VV.dom f) \<star> snd (VV.dom f)"
      proof -
        fix f
        assume f: "VV.arr f"
        have "dom (fst f \<star> snd f) = MkIde (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f))"
          using f VV.arrE [of f] dom_char arr_hcomp hcomp_def by simp
        also have "... = fst (VV.dom f) \<star> snd (VV.dom f)"
        proof -
          have "hcomp (fst (VV.dom f)) (snd (VV.dom f)) =
                MkArr (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)) (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f))
                      (B.can (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)) (Dom (fst f) \<^bold>\<star> Dom (snd f)) \<cdot>\<^sub>B
                        (\<lbrace>Dom (fst f)\<rbrace> \<star>\<^sub>B \<lbrace>Dom (snd f)\<rbrace>) \<cdot>\<^sub>B
                        B.can (Dom (fst f) \<^bold>\<star> Dom (snd f)) (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)))"
            using f VV.arrE [of f] arr_hcomp hcomp_def by simp
          moreover have "B.can (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)) (Dom (fst f) \<^bold>\<star> Dom (snd f)) \<cdot>\<^sub>B
                           (\<lbrace>Dom (fst f)\<rbrace> \<star>\<^sub>B \<lbrace>Dom (snd f)\<rbrace>) \<cdot>\<^sub>B
                              B.can (Dom (fst f) \<^bold>\<star> Dom (snd f)) (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)) =
                         \<lbrace>Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)\<rbrace>"
          proof -
            have 1: "E.Ide (Dom (fst f) \<^bold>\<star> Dom (snd f))"
              using f VV.arr_char arr_char dom_char
              apply simp
              by (metis (no_types, lifting) src_simps(1) trg_simps(1))
            have 2: "E.Ide (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f))"
              using f VV.arr_char arr_char dom_char
              apply simp
              by (metis (no_types, lifting) E.Ide_HcompNml src_simps(1) trg_simps(1))
            have 3: "\<^bold>\<lfloor>Dom (fst f) \<^bold>\<star> Dom (snd f)\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)\<^bold>\<rfloor>"
              using f VV.arr_char arr_char dom_char
              apply simp
              by (metis (no_types, lifting) E.Nml_HcompNml(1) E.Nmlize_Nml
                  src_simps(1) trg_simps(1))
            have "(\<lbrace>Dom (fst f)\<rbrace> \<star>\<^sub>B \<lbrace>Dom (snd f)\<rbrace>) \<cdot>\<^sub>B
                    B.can (Dom (fst f) \<^bold>\<star> Dom (snd f)) (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)) =
                  B.can (Dom (fst f) \<^bold>\<star> Dom (snd f)) (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f))"
            proof -
              have "B.in_hom (B.can (Dom (fst f) \<^bold>\<star> Dom (snd f))
                             (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)))
                             \<lbrace>Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)\<rbrace> (\<lbrace>Dom (fst f)\<rbrace> \<star>\<^sub>B \<lbrace>Dom (snd f)\<rbrace>)"
                using 1 2 3 f VV.arr_char arr_char
                      B.can_in_hom [of "Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)" "Dom (fst f) \<^bold>\<star> Dom (snd f)"]
                by simp
              thus ?thesis
                using B.comp_cod_arr by auto
            qed
            thus ?thesis
              using 1 2 3 f VV.arr_char B.can_Ide_self B.vcomp_can by simp
          qed
          ultimately show ?thesis by simp
        qed
        finally show "dom (fst f \<star> snd f) = fst (VV.dom f) \<star> snd (VV.dom f)"
          by simp
      qed
      show "\<And>f. VV.arr f \<Longrightarrow> cod (fst f \<star> snd f) = fst (VV.cod f) \<star> snd (VV.cod f)"
      proof -
        fix f
        assume f: "VV.arr f"
        have "cod (fst f \<star> snd f) = MkIde (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f))"
          using f VV.arrE [of f] cod_char arr_hcomp hcomp_def by simp
        also have "... = fst (VV.cod f) \<star> snd (VV.cod f)"
        proof -
          have "hcomp (fst (VV.cod f)) (snd (VV.cod f)) =
                MkArr (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)) (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f))
                      (B.can (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)) (Cod (fst f) \<^bold>\<star> Cod (snd f)) \<cdot>\<^sub>B
                        (\<lbrace>Cod (fst f)\<rbrace> \<star>\<^sub>B \<lbrace>Cod (snd f)\<rbrace>) \<cdot>\<^sub>B
                        B.can (Cod (fst f) \<^bold>\<star> Cod (snd f)) (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)))"
            using f VV.arrE [of f] arr_hcomp hcomp_def by simp
          moreover have "B.can (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)) (Cod (fst f) \<^bold>\<star> Cod (snd f)) \<cdot>\<^sub>B
                           (\<lbrace>Cod (fst f)\<rbrace> \<star>\<^sub>B \<lbrace>Cod (snd f)\<rbrace>) \<cdot>\<^sub>B
                             B.can (Cod (fst f) \<^bold>\<star> Cod (snd f)) (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)) =
                         \<lbrace>Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)\<rbrace>"
          proof -
            have 1: "E.Ide (Cod (fst f) \<^bold>\<star> Cod (snd f))"
              using f VV.arr_char arr_char dom_char
              apply simp
              by (metis (no_types, lifting) src_simps(1) trg_simps(1))
            have 2: "E.Ide (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f))"
              using f VV.arr_char arr_char dom_char
              apply simp
              by (metis (no_types, lifting) E.Ide_HcompNml src_simps(1) trg_simps(1))
            have 3: "\<^bold>\<lfloor>Cod (fst f) \<^bold>\<star> Cod (snd f)\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)\<^bold>\<rfloor>"
              using f VV.arr_char arr_char dom_char
              apply simp
              by (metis (no_types, lifting) E.Nml_HcompNml(1) E.Nmlize_Nml
                  src_simps(1) trg_simps(1))
            have "(\<lbrace>Cod (fst f)\<rbrace> \<star>\<^sub>B \<lbrace>Cod (snd f)\<rbrace>) \<cdot>\<^sub>B
                    B.can (Cod (fst f) \<^bold>\<star> Cod (snd f)) (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)) =
                  B.can (Cod (fst f) \<^bold>\<star> Cod (snd f)) (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f))"
            proof -
              have "B.in_hom (B.can (Cod (fst f) \<^bold>\<star> Cod (snd f))
                             (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)))
                             \<lbrace>Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)\<rbrace> (\<lbrace>Cod (fst f)\<rbrace> \<star>\<^sub>B \<lbrace>Cod (snd f)\<rbrace>)"
                using 1 2 3 f VV.arr_char arr_char
                      B.can_in_hom [of "Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)"
                                       "Cod (fst f) \<^bold>\<star> Cod (snd f)"]
                by simp
              thus ?thesis
                using B.comp_cod_arr by auto
            qed
            thus ?thesis
              using 1 2 3 f VV.arr_char B.can_Ide_self B.vcomp_can by simp
          qed
          ultimately show ?thesis by simp
        qed
        finally show "cod (fst f \<star> snd f) = fst (VV.cod f) \<star> snd (VV.cod f)"
          by simp
      qed
      show "\<And>g f. VV.seq g f \<Longrightarrow>
                   fst (VV.comp g f) \<star> snd (VV.comp g f) = (fst g \<star> snd g) \<cdot> (fst f \<star> snd f)"
      proof -
        fix f g
        assume fg: "VV.seq g f"
        have f: "arr (fst f) \<and> arr (snd f) \<and> src (fst f) = trg (snd f)"
          using fg VV.seq_char VV.arr_char by simp
        have g: "arr (fst g) \<and> arr (snd g) \<and> src (fst g) = trg (snd g)"
          using fg VV.seq_char VV.arr_char by simp
        have 1: "arr (fst (VV.comp g f)) \<and> arr (snd (VV.comp g f)) \<and>
                 src (fst (VV.comp g f)) = trg (snd (VV.comp g f))"
          using fg VV.arrE by blast
        have 0: "VV.comp g f = (fst g \<cdot> fst f, snd g \<cdot> snd f)"
          using fg 1 VV.comp_char VxV.comp_char
          by (metis (no_types, lifting) VV.seq_char VxV.seqE)
        let ?X = "MkArr (Dom (fst (VV.comp g f)) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd (VV.comp g f)))
                        (Cod (fst (VV.comp g f)) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd (VV.comp g f)))
                        (B.can (Cod (fst (VV.comp g f)) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd (VV.comp g f)))
                               (Cod (fst (VV.comp g f)) \<^bold>\<star> Cod (snd (VV.comp g f))) \<cdot>\<^sub>B
                           (Map (fst (VV.comp g f)) \<star>\<^sub>B Map (snd (VV.comp g f))) \<cdot>\<^sub>B
                           B.can (Dom (fst (VV.comp g f)) \<^bold>\<star> Dom (snd (VV.comp g f)))
                                 (Dom (fst (VV.comp g f)) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd (VV.comp g f))))"
        have 2: "fst (VV.comp g f) \<star> snd (VV.comp g f) = ?X"
          unfolding hcomp_def using 1 by simp
        also have "... = (fst g \<star> snd g) \<cdot> (fst f \<star> snd f)"
        proof -
          let ?GG = "MkArr (Dom (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd g)) (Cod (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd g))
                           (B.can (Cod (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd g)) (Cod (fst g) \<^bold>\<star> Cod (snd g)) \<cdot>\<^sub>B
                             (Map (fst g) \<star>\<^sub>B Map (snd g)) \<cdot>\<^sub>B
                             B.can (Dom (fst g) \<^bold>\<star> Dom (snd g)) (Dom (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd g)))"
          let ?FF = "MkArr (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)) (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f))
                           (B.can (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)) (Cod (fst f) \<^bold>\<star> Cod (snd f)) \<cdot>\<^sub>B
                             (Map (fst f) \<star>\<^sub>B Map (snd f)) \<cdot>\<^sub>B
                             B.can (Dom (fst f) \<^bold>\<star> Dom (snd f)) (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)))"
          have 4: "arr ?FF \<and> arr ?GG \<and> Dom ?GG = Cod ?FF"
          proof -
            have "arr ?FF \<and> arr ?GG"
              using f g fg VV.arr_char VV.seqE hcomp_def A by presburger
            thus ?thesis
              using 0 1 by (simp add: fg seq_char)
          qed
          have "(fst g \<star> snd g) \<cdot> (fst f \<star> snd f) = ?GG \<cdot> ?FF"
            unfolding hcomp_def
            using 1 f g fg VV.arr_char VV.seqE by simp
          also have "... = ?X"
          proof (intro arr_eqI)
            show "seq ?GG ?FF"
              using fg 4 seq_char by blast
            show "arr ?X"
              using fg 1 arr_hcomp hcomp_def by simp
            show "Dom (?GG \<cdot> ?FF) = Dom ?X"
              using fg 0 1 4 seq_char by simp
            show "Cod (?GG \<cdot> ?FF) = Cod ?X"
              using fg 0 1 4 seq_char by simp
            show "Map (?GG \<cdot> ?FF) = Map ?X"
            proof -
              have "Map (?GG \<cdot> ?FF) = Map ?GG \<cdot>\<^sub>B Map ?FF"
                using 4 by auto
              also have
                "... = (B.can (Cod (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd g)) (Cod (fst g) \<^bold>\<star> Cod (snd g)) \<cdot>\<^sub>B
                         (Map (fst g) \<star>\<^sub>B Map (snd g)) \<cdot>\<^sub>B
                         B.can (Dom (fst g) \<^bold>\<star> Dom (snd g)) (Dom (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd g))) \<cdot>\<^sub>B
                       (B.can (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)) (Cod (fst f) \<^bold>\<star> Cod (snd f)) \<cdot>\<^sub>B
                         (Map (fst f) \<star>\<^sub>B Map (snd f)) \<cdot>\<^sub>B
                         B.can (Dom (fst f) \<^bold>\<star> Dom (snd f)) (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f)))"
                using fg by simp
              also have
                "... = B.can (Cod (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd g)) (Cod (fst g) \<^bold>\<star> Cod (snd g)) \<cdot>\<^sub>B
                         ((Map (fst g) \<star>\<^sub>B Map (snd g)) \<cdot>\<^sub>B (Map (fst f) \<star>\<^sub>B Map (snd f))) \<cdot>\<^sub>B
                         B.can (Dom (fst f) \<^bold>\<star> Dom (snd f)) (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f))"
              proof -
                have "(B.can (Cod (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd g)) (Cod (fst g) \<^bold>\<star> Cod (snd g)) \<cdot>\<^sub>B
                        (Map (fst g) \<star>\<^sub>B Map (snd g)) \<cdot>\<^sub>B
                        B.can (Dom (fst g) \<^bold>\<star> Dom (snd g)) (Dom (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd g))) \<cdot>\<^sub>B
                        (B.can (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)) (Cod (fst f) \<^bold>\<star> Cod (snd f)) \<cdot>\<^sub>B
                        (Map (fst f) \<star>\<^sub>B Map (snd f)) \<cdot>\<^sub>B
                        B.can (Dom (fst f) \<^bold>\<star> Dom (snd f)) (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f))) =
                      B.can (Cod (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd g)) (Cod (fst g) \<^bold>\<star> Cod (snd g)) \<cdot>\<^sub>B
                        ((Map (fst g) \<star>\<^sub>B Map (snd g)) \<cdot>\<^sub>B
                        (B.can (Dom (fst g) \<^bold>\<star> Dom (snd g)) (Dom (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd g)) \<cdot>\<^sub>B
                        B.can (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)) (Cod (fst f) \<^bold>\<star> Cod (snd f))) \<cdot>\<^sub>B
                        (Map (fst f) \<star>\<^sub>B Map (snd f))) \<cdot>\<^sub>B
                        B.can (Dom (fst f) \<^bold>\<star> Dom (snd f)) (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f))"
                  using B.comp_assoc by simp
                also have "... = B.can (Cod (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd g)) (Cod (fst g) \<^bold>\<star> Cod (snd g)) \<cdot>\<^sub>B
                                  ((Map (fst g) \<star>\<^sub>B Map (snd g)) \<cdot>\<^sub>B (Map (fst f) \<star>\<^sub>B Map (snd f))) \<cdot>\<^sub>B
                                   B.can (Dom (fst f) \<^bold>\<star> Dom (snd f)) (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f))"
                proof -
                  have "(B.can (Dom (fst g) \<^bold>\<star> Dom (snd g)) (Dom (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd g))) \<cdot>\<^sub>B
                          (B.can (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)) (Cod (fst f) \<^bold>\<star> Cod (snd f))) =
                        \<lbrace>Cod (fst f) \<^bold>\<star> Cod (snd f)\<rbrace>"
                  proof -
                    have "(B.can (Dom (fst g) \<^bold>\<star> Dom (snd g)) (Dom (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd g))) \<cdot>\<^sub>B
                          (B.can (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)) (Cod (fst f) \<^bold>\<star> Cod (snd f))) =
                          B.can (Dom (fst g) \<^bold>\<star> Dom (snd g)) (Cod (fst f) \<^bold>\<star> Cod (snd f))"
                    proof -
                      have "E.Ide (Dom (fst g) \<^bold>\<star> Dom (snd g))"
                        using g arr_char
                        apply simp
                        by (metis (no_types, lifting) src_simps(1) trg_simps(1))
                      moreover have "E.Ide (Dom (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd g))"
                        using g arr_char
                        apply simp
                        by (metis (no_types, lifting) E.Ide_HcompNml src_simps(1) trg_simps(1))
                      moreover have "E.Ide (Cod (fst f) \<^bold>\<star> Cod (snd f))"
                        using f arr_char
                        apply simp
                        by (metis (no_types, lifting) src_simps(1) trg_simps(1))
                      moreover have
                        "\<^bold>\<lfloor>Dom (fst g) \<^bold>\<star> Dom (snd g)\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd g)\<^bold>\<rfloor>"
                        using g
                        apply simp
                        by (metis (no_types, lifting) E.Nml_HcompNml(1) E.Nmlize_Nml
                            arrE src_simps(1) trg_simps(1))
                      moreover have
                        "\<^bold>\<lfloor>Dom (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd g)\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod (fst f) \<^bold>\<star> Cod (snd f)\<^bold>\<rfloor>"
                        using g
                        apply simp
                        by (metis (no_types, lifting) "0" "1" E.Nmlize.simps(3)
                            calculation(4) fst_conv seq_char snd_conv)
                      moreover have
                        "Dom (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd g) = Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)"
                        using 0 1 by (simp add: seq_char)
                      ultimately show ?thesis
                        using B.vcomp_can by simp
                    qed
                    also have "... = \<lbrace>Cod (fst f) \<^bold>\<star> Cod (snd f)\<rbrace>"
                    proof -
                      have "Dom (fst g) \<^bold>\<star> Dom (snd g) = Cod (fst f) \<^bold>\<star> Cod (snd f)"
                        using 0 f g fg seq_char VV.seq_char VV.arr_char
                        by simp
                      thus ?thesis
                        using f B.can_Ide_self [of "Dom (fst f) \<^bold>\<star> Dom (snd f)"]
                        apply simp
                        by (metis (no_types, lifting) B.can_Ide_self E.eval.simps(3)
                            E.Ide.simps(3) arr_char src_simps(2) trg_simps(2))
                    qed
                    finally show ?thesis by simp
                  qed
                  hence "(B.can (Dom (fst g) \<^bold>\<star> Dom (snd g)) (Dom (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd g)) \<cdot>\<^sub>B
                           B.can (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)) (Cod (fst f) \<^bold>\<star> Cod (snd f))) \<cdot>\<^sub>B
                           (Map (fst f) \<star>\<^sub>B Map (snd f)) =
                         \<lbrace>Cod (fst f) \<^bold>\<star> Cod (snd f)\<rbrace> \<cdot>\<^sub>B (Map (fst f) \<star>\<^sub>B Map (snd f))"
                    by simp
                  also have "... = Map (fst f) \<star>\<^sub>B Map (snd f)"
                  proof -
                    have 1: "\<forall>p. arr p \<longrightarrow> map (cod p) \<cdot> map p = map p"
                      by blast
                    have 3: "\<lbrace>Cod (fst f)\<rbrace> \<cdot>\<^sub>B Map (fst f) = Map (map (cod (fst f)) \<cdot> map (fst f))"
                      by (simp add: f)
                    have 4: "map (cod (fst f)) \<cdot> map (fst f) = fst f"
                      using 1 f map_simp by simp
                    show ?thesis
                    proof -
                      have 2: "\<lbrace>Cod (snd f)\<rbrace> \<cdot>\<^sub>B Map (snd f) = Map (snd f)"
                      proof -
                        have "\<lbrace>Cod (snd f)\<rbrace> \<cdot>\<^sub>B Map (snd f) =
                              Map (map (cod (snd f)) \<cdot> map (snd f))"
                          by (simp add: f)
                        moreover have "map (cod (snd f)) \<cdot> map (snd f) = snd f"
                          using 1 f map_simp by simp
                        ultimately show ?thesis by presburger
                      qed
                      have "B.seq \<lbrace>Cod (snd f)\<rbrace> (Map (snd f))"
                        using f 2 by auto
                      moreover have "B.seq \<lbrace>Cod (fst f)\<rbrace> (Map (fst f))"
                        using 4 f 3 by auto
                      moreover have
                        "\<lbrace>Cod (fst f)\<rbrace> \<cdot>\<^sub>B Map (fst f) \<star>\<^sub>B \<lbrace>Cod (snd f)\<rbrace> \<cdot>\<^sub>B Map (snd f) =
                         Map (fst f) \<star>\<^sub>B Map (snd f)"
                        using 2 3 4 by presburger
                      ultimately show ?thesis
                        by (simp add: B.interchange)
                    qed
                  qed
                  finally have
                    "(B.can (Dom (fst g) \<^bold>\<star> Dom (snd g)) (Dom (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd g)) \<cdot>\<^sub>B
                       B.can (Cod (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd f)) (Cod (fst f) \<^bold>\<star> Cod (snd f))) \<cdot>\<^sub>B
                       (Map (fst f) \<star>\<^sub>B Map (snd f)) =
                     Map (fst f) \<star>\<^sub>B Map (snd f)"
                    by simp
                  thus ?thesis
                    using fg B.comp_cod_arr by simp
                qed
                finally show ?thesis by simp
              qed
              also have "... = B.can (Cod (fst g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd g)) (Cod (fst g) \<^bold>\<star> Cod (snd g)) \<cdot>\<^sub>B
                                 (Map (fst g \<cdot> fst f) \<star>\<^sub>B Map (snd g \<cdot> snd f)) \<cdot>\<^sub>B
                                 B.can (Dom (fst f) \<^bold>\<star> Dom (snd f)) (Dom (fst f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd f))"
              proof -
                have 2: "Dom (fst g) = Cod (fst f)"
                  using 0 f g fg VV.seq_char [of g f] VV.arr_char arr_char seq_char
                  by (metis (no_types, lifting) fst_conv)
                hence "Map (fst g \<cdot> fst f) = Map (fst g) \<cdot>\<^sub>B Map (fst f)"
                  using f g Map_comp [of "fst f" "fst g"] by simp
                moreover have "B.seq (Map (fst g)) (Map (fst f)) \<and>
                               B.seq (Map (snd g)) (Map (snd f))"
                  using f g 0 1 2 arr_char
                  by (metis (no_types, lifting) B.seqI' prod.sel(2) seq_char)
                ultimately show ?thesis
                  using 0 1 seq_char Map_comp B.interchange by auto
              qed
              also have "... = Map ?X"
                using fg 0 1 by (simp add: seq_char)
              finally show ?thesis by simp
            qed
          qed
          finally show ?thesis by simp
        qed
        finally show "fst (VV.comp g f) \<star> snd (VV.comp g f) = (fst g \<star> snd g) \<cdot> (fst f \<star> snd f)"
          by simp
      qed
    qed

    interpretation H: horizontal_composition vcomp hcomp src trg
      using hseq_char by (unfold_locales, auto)

    lemma hcomp_assoc:
    assumes "arr \<mu>" and "arr \<nu>" and "arr \<tau>"
    and "src \<mu> = trg \<nu>" and "src \<nu> = trg \<tau>"
    shows "(\<mu> \<star> \<nu>) \<star> \<tau> = \<mu> \<star> \<nu> \<star> \<tau>"
    proof (intro arr_eqI)
      have \<mu>\<nu>: "\<guillemotleft>Map \<mu> \<star>\<^sub>B Map \<nu> : \<lbrace>Dom \<mu> \<^bold>\<star> Dom \<nu>\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod \<mu> \<^bold>\<star> Cod \<nu>\<rbrace>\<guillemotright>"
        using assms src_def trg_def arr_char
        by (auto simp add: E.eval_simps'(2-3) Pair_inject)
      have \<nu>\<tau>: "\<guillemotleft>Map \<nu> \<star>\<^sub>B Map \<tau> : \<lbrace>Dom \<nu> \<^bold>\<star> Dom \<tau>\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod \<nu> \<^bold>\<star> Cod \<tau>\<rbrace>\<guillemotright>"
        using assms src_def trg_def arr_char
        by (auto simp add: E.eval_simps'(2-3) Pair_inject)
      show "H.hseq (\<mu> \<star> \<nu>) \<tau>"
        using assms \<mu>\<nu> \<nu>\<tau> by auto
      show "H.hseq \<mu> (\<nu> \<star> \<tau>)"
        using assms \<mu>\<nu> \<nu>\<tau> by auto
      show "Dom ((\<mu> \<star> \<nu>) \<star> \<tau>) = Dom (\<mu> \<star> \<nu> \<star> \<tau>)"
      proof -
        have "E.Nml (Dom \<mu>) \<and> E.Nml (Dom \<nu>) \<and> E.Nml (Dom \<tau>)"
          using assms by blast
        moreover have "E.Src (Dom \<mu>) = E.Trg (Dom \<nu>) \<and> E.Src (Dom \<nu>) = E.Trg (Dom \<tau>)"
          using assms \<mu>\<nu> \<nu>\<tau>
          by (metis (no_types, lifting) src_simps(2) trg_simps(2))
        ultimately show ?thesis
          using assms \<mu>\<nu> \<nu>\<tau> E.HcompNml_assoc by simp
      qed
      show "Cod ((\<mu> \<star> \<nu>) \<star> \<tau>) = Cod (\<mu> \<star> \<nu> \<star> \<tau>)"
      proof -
        have "E.Nml (Cod \<mu>) \<and> E.Nml (Cod \<nu>) \<and> E.Nml (Cod \<tau>)"
          using assms by blast
        moreover have "E.Src (Cod \<mu>) = E.Trg (Cod \<nu>) \<and> E.Src (Cod \<nu>) = E.Trg (Cod \<tau>)"
          using assms \<mu>\<nu> \<nu>\<tau>
          by (metis (no_types, lifting) arrE src_simps(2) trg_simps(2))
        ultimately show ?thesis
          using assms \<mu>\<nu> \<nu>\<tau> E.HcompNml_assoc by simp
      qed
     show "Map ((\<mu> \<star> \<nu>) \<star> \<tau>) = Map (\<mu> \<star> \<nu> \<star> \<tau>)"
      proof -
        have "Map ((\<mu> \<star> \<nu>) \<star> \<tau>) =
              B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                   B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>)"
        proof -
          have 1: "Map ((\<mu> \<star> \<nu>) \<star> \<tau>) =
                   B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) ((Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                     (B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) (Cod \<mu> \<^bold>\<star> Cod \<nu>) \<cdot>\<^sub>B
                       (Map \<mu> \<star>\<^sub>B Map \<nu>) \<cdot>\<^sub>B
                         B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                       B.can ((Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<^bold>\<star> Dom \<tau>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>)"
            using assms \<mu>\<nu> \<nu>\<tau> hcomp_def E.HcompNml_assoc src_def trg_def arr_char
                  E.Nml_HcompNml E.Ide_HcompNml
            by auto (* 5 sec *)
          also have
            "... = B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) ((Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                     (B.can ((Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<^bold>\<star> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                       (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                         B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) ((Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<^bold>\<star> Dom \<tau>)) \<cdot>\<^sub>B
                       B.can ((Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<^bold>\<star> Dom \<tau>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>)"
          proof -
            have
              "B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) (Cod \<mu> \<^bold>\<star> Cod \<nu>) \<cdot>\<^sub>B
                 (Map \<mu> \<star>\<^sub>B Map \<nu>) \<cdot>\<^sub>B B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<star>\<^sub>B Map \<tau> =
               B.can ((Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<^bold>\<star> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                 (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                 B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) ((Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<^bold>\<star> Dom \<tau>)"
            proof -
              have "B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) (Cod \<mu> \<^bold>\<star> Cod \<nu>) \<cdot>\<^sub>B
                      (Map \<mu> \<star>\<^sub>B Map \<nu>) \<cdot>\<^sub>B B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>)
                         \<star>\<^sub>B Map \<tau> =
                    (B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) (Cod \<mu> \<^bold>\<star> Cod \<nu>) \<star>\<^sub>B B.can (Cod \<tau>) (Cod \<tau>)) \<cdot>\<^sub>B
                      ((Map \<mu> \<star>\<^sub>B Map \<nu>) \<cdot>\<^sub>B
                         B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<star>\<^sub>B Map \<tau>)"
              proof -
                have "B.seq (B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) (Cod \<mu> \<^bold>\<star> Cod \<nu>))
                               ((Map \<mu> \<star>\<^sub>B Map \<nu>) \<cdot>\<^sub>B B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>))"
                  by (metis (no_types, lifting) B.arrI Map_hcomp arrE arr_hcomp
                      assms(1) assms(2) assms(4))
                moreover have "B.seq (B.can (Cod \<tau>) (Cod \<tau>)) (Map \<tau>)"
                  using B.can_in_hom assms(3) by blast
                moreover have "B.ide (B.can (Cod \<tau>) (Cod \<tau>))"
                  using B.can_Ide_self E.ide_eval_Ide arr_char assms(3) by presburger
                ultimately show ?thesis
                  by (metis (no_types) B.comp_ide_arr B.interchange)
              qed
              also have
                "... = (B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) (Cod \<mu> \<^bold>\<star> Cod \<nu>) \<star>\<^sub>B B.can (Cod \<tau>) (Cod \<tau>)) \<cdot>\<^sub>B
                         ((Map \<mu> \<star>\<^sub>B Map \<nu>) \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                           (B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<star>\<^sub>B
                              B.can (Dom \<tau>) (Dom \<tau>))"
              proof -
                have "B.seq (Map \<mu> \<star>\<^sub>B Map \<nu>) (B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>))"
                  by (metis (no_types, lifting) B.arrI B.comp_null(2) B.ext Map_hcomp
                      arrE arr_hcomp assms(1) assms(2) assms(4))
                moreover have "B.seq (Map \<tau>) (B.can (Dom \<tau>) (Dom \<tau>))"
                  using assms(3) by fastforce
                ultimately show ?thesis
                  using B.interchange
                  by (metis (no_types, lifting) B.can_Ide_self B.comp_arr_ide E.ide_eval_Ide
                      arrE assms(3))
              qed
              also have
                "... = (B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) (Cod \<mu> \<^bold>\<star> Cod \<nu>) \<star>\<^sub>B B.can (Cod \<tau>) (Cod \<tau>)) \<cdot>\<^sub>B
                         (B.can ((Cod \<mu> \<^bold>\<star> Cod \<nu>) \<^bold>\<star> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                           (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                             B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) ((Dom \<mu> \<^bold>\<star> Dom \<nu>) \<^bold>\<star> Dom \<tau>)) \<cdot>\<^sub>B
                           (B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<star>\<^sub>B
                              B.can (Dom \<tau>) (Dom \<tau>))"
              proof -
                have "(Map \<mu> \<star>\<^sub>B Map \<nu>) \<star>\<^sub>B Map \<tau> =
                        B.\<a>' \<lbrace>Cod \<mu>\<rbrace> \<lbrace>Cod \<nu>\<rbrace> \<lbrace>Cod \<tau>\<rbrace> \<cdot>\<^sub>B
                          (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                             \<a>\<^sub>B \<lbrace>Dom \<mu>\<rbrace> \<lbrace>Dom \<nu>\<rbrace> \<lbrace>Dom \<tau>\<rbrace>"
                  using B.hcomp_reassoc(1)
                  by (metis (no_types, lifting) B.hcomp_in_vhomE B.in_homE \<mu>\<nu> \<nu>\<tau> arrE
                      assms(1) assms(2) assms(3))
                also have "... = B.can ((Cod \<mu> \<^bold>\<star> Cod \<nu>) \<^bold>\<star> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                                   (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                                      B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) ((Dom \<mu> \<^bold>\<star> Dom \<nu>) \<^bold>\<star> Dom \<tau>)"
                  using assms arr_char src_def trg_def arr_char B.canE_associator by simp
               finally show ?thesis by simp
              qed
              also have
                "... = ((B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) (Cod \<mu> \<^bold>\<star> Cod \<nu>) \<star>\<^sub>B B.can (Cod \<tau>) (Cod \<tau>)) \<cdot>\<^sub>B
                         (B.can ((Cod \<mu> \<^bold>\<star> Cod \<nu>) \<^bold>\<star> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>))) \<cdot>\<^sub>B
                       (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                       (B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) ((Dom \<mu> \<^bold>\<star> Dom \<nu>) \<^bold>\<star> Dom \<tau>) \<cdot>\<^sub>B
                          (B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<star>\<^sub>B
                             B.can (Dom \<tau>) (Dom \<tau>)))"
                using B.comp_assoc by simp
              also have
                "... = B.can ((Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<^bold>\<star> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                         (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                         B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) ((Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<^bold>\<star> Dom \<tau>)"
              proof -
                have "(B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) (Cod \<mu> \<^bold>\<star> Cod \<nu>) \<star>\<^sub>B B.can (Cod \<tau>) (Cod \<tau>)) \<cdot>\<^sub>B
                        (B.can ((Cod \<mu> \<^bold>\<star> Cod \<nu>) \<^bold>\<star> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>)) =
                      B.can ((Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<^bold>\<star> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>)"
                proof -
                  have "E.Ide (Cod \<mu> \<^bold>\<star> Cod \<nu>)"
                    by (metis (no_types, lifting) E.Ide.simps(3) arrE assms(1-2,4)
                        src_simps(1) trg_simps(1))
                  moreover have "E.Ide (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>)"
                    using E.Ide_HcompNml assms(1) assms(2) calculation by auto
                  moreover have "\<^bold>\<lfloor>Cod \<mu> \<^bold>\<star> Cod \<nu>\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>\<^bold>\<rfloor>"
                    using E.Nml_HcompNml(1) assms(1) assms(2) calculation(1) by fastforce
                  moreover have "E.Src (Cod \<mu> \<^bold>\<star> Cod \<nu>) = E.Trg (Cod \<tau>)"
                    by (metis (no_types, lifting) E.Src.simps(3) arrE assms(2-3,5)
                        src_simps(2) trg_simps(2))
                  moreover have "E.Src (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) = E.Trg (Cod \<tau>)"
                    using E.Src_HcompNml assms(1) assms(2) calculation(1) calculation(4)
                    by fastforce
                  moreover have "\<^bold>\<lfloor>Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>\<^bold>\<rfloor> = \<^bold>\<lfloor>(Cod \<mu> \<^bold>\<star> Cod \<nu>) \<^bold>\<star> Cod \<tau>\<^bold>\<rfloor>"
                    by (metis (no_types, lifting) E.Arr.simps(3) E.Nmlize_Hcomp_Hcomp
                        E.Nmlize_Hcomp_Hcomp' E.Ide_implies_Arr E.Src.simps(3) arrE assms(3)
                        calculation(1) calculation(4))
                  ultimately show ?thesis
                    using assms(3) B.hcomp_can B.vcomp_can by auto
                qed
                moreover have
                  "B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) ((Dom \<mu> \<^bold>\<star> Dom \<nu>) \<^bold>\<star> Dom \<tau>) \<cdot>\<^sub>B
                     (B.can (Dom \<mu> \<^bold>\<star> Dom \<nu>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<star>\<^sub>B B.can (Dom \<tau>) (Dom \<tau>)) =
                   B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) ((Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<^bold>\<star> Dom \<tau>)"
                proof -
                  have "E.Ide (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>)"
                    by (metis (no_types, lifting) E.Ide_HcompNml arrE assms(1-2,4)
                        src_simps(2) trg_simps(2))
                  moreover have "E.Ide (Dom \<mu> \<^bold>\<star> Dom \<nu>)"
                    by (metis (no_types, lifting) E.Ide.simps(3) arrE assms(1-2,4)
                        src_simps(1) trg_simps(1))
                  moreover have "\<^bold>\<lfloor>Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom \<mu> \<^bold>\<star> Dom \<nu>\<^bold>\<rfloor>"
                    using E.Nml_HcompNml(1) assms(1-2) calculation(2) by fastforce
                  moreover have "E.Src (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) = E.Trg (Dom \<tau>)"
                    by (metis (no_types, lifting) E.Ide.simps(3) E.Src_HcompNml arrE
                        assms(1-3,5) calculation(2) src_simps(2) trg_simps(2))
                  moreover have "E.Src (Dom \<mu> \<^bold>\<star> Dom \<nu>) = E.Trg (Dom \<tau>)"
                    using E.Src_HcompNml assms(1-2) calculation(2) calculation(4)
                    by fastforce
                  moreover have "E.Ide ((Dom \<mu> \<^bold>\<star> Dom \<nu>) \<^bold>\<star> Dom \<tau>)"
                    using E.Ide.simps(3) assms(3) calculation(2) calculation(5) by blast
                  moreover have "\<^bold>\<lfloor>(Dom \<mu> \<^bold>\<star> Dom \<nu>) \<^bold>\<star> Dom \<tau>\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>\<^bold>\<rfloor>"
                    using E.Nmlize_Hcomp_Hcomp calculation(6) by auto
                  ultimately show ?thesis
                    using assms(3) B.hcomp_can B.vcomp_can by auto
                qed
                ultimately show ?thesis by simp
              qed
              finally show ?thesis by simp
            qed
            thus ?thesis by simp
          qed
          also have
            "... = (B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) ((Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                     B.can ((Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<^bold>\<star> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>)) \<cdot>\<^sub>B
                       (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                         B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) ((Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<^bold>\<star> Dom \<tau>) \<cdot>\<^sub>B
                           B.can ((Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<^bold>\<star> Dom \<tau>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>)"
            using B.comp_assoc by simp
          also have "... = B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                             (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                               B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>)"
          proof -
            have "B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) ((Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                    B.can ((Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<^bold>\<star> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>) =
                  B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>)"
            proof -
              have "E.Ide (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>)"
                using assms src_def trg_def by fastforce
              moreover have "E.Ide ((Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<^bold>\<star> Cod \<tau>)"
                using assms arr_char src_def trg_def E.Ide_HcompNml E.Src_HcompNml
                by auto
              moreover have "E.Ide (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>)"
                using assms arr_char src_def trg_def
                by (simp add: E.Nml_HcompNml(1) E.Ide_HcompNml E.Trg_HcompNml)
              moreover have "\<^bold>\<lfloor>Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>\<^bold>\<rfloor> = \<^bold>\<lfloor>(Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<^bold>\<star> Cod \<tau>\<^bold>\<rfloor>"
                using assms arr_char src_def trg_def E.Nml_HcompNml E.HcompNml_assoc by simp
              moreover have "\<^bold>\<lfloor>(Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu>) \<^bold>\<star> Cod \<tau>\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>\<^bold>\<rfloor>"
                using assms arr_char src_def trg_def E.Nml_HcompNml E.HcompNml_assoc
                by simp
              ultimately show ?thesis by simp
            qed
            moreover have
              "B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) ((Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<^bold>\<star> Dom \<tau>) \<cdot>\<^sub>B
                 B.can ((Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<^bold>\<star> Dom \<tau>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>) =
               B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>)"
            proof -
              have "E.Ide (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>)"
                using assms src_def trg_def by fastforce
              moreover have "E.Ide ((Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<^bold>\<star> Dom \<tau>)"
                using assms arr_char src_def trg_def E.Ide_HcompNml E.Src_HcompNml
                by auto
              moreover have "E.Ide (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>)"
                using assms arr_char src_def trg_def
                by (simp add: E.Nml_HcompNml(1) E.Ide_HcompNml E.Trg_HcompNml)
              moreover have "\<^bold>\<lfloor>Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>\<^bold>\<rfloor> = \<^bold>\<lfloor>(Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<^bold>\<star> Dom \<tau>\<^bold>\<rfloor>"
                using assms arr_char src_def trg_def E.Nml_HcompNml E.HcompNml_assoc by simp
              moreover have
                "\<^bold>\<lfloor>(Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu>) \<^bold>\<star> Dom \<tau>\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>\<^bold>\<rfloor>"
                using assms arr_char src_def trg_def E.Nml_HcompNml E.HcompNml_assoc
                by simp
              ultimately show ?thesis by simp
            qed
            ultimately show ?thesis by simp
          qed
          finally show ?thesis by simp
        qed
        also have "... = Map (\<mu> \<star> \<nu> \<star> \<tau>)"
        proof -
          have 1: "Map (\<mu> \<star> \<nu> \<star> \<tau>) =
                   B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) \<cdot>\<^sub>B
                     (Map \<mu> \<star>\<^sub>B B.can (Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<nu> \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                                (Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                                  B.can (Dom \<nu> \<^bold>\<star> Dom \<tau>) (Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>)) \<cdot>\<^sub>B
                        B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>)"
            using assms Map_hcomp [of \<mu> "\<nu> \<star> \<tau>"] Map_hcomp [of \<nu> \<tau>] by simp
          also have
            "... = B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) \<cdot>\<^sub>B
                     ((B.can (Cod \<mu>) (Cod \<mu>) \<star>\<^sub>B B.can (Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<nu> \<^bold>\<star> Cod \<tau>)) \<cdot>\<^sub>B
                       (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                         (B.can (Dom \<mu>) (Dom \<mu>) \<star>\<^sub>B
                            B.can (Dom \<nu> \<^bold>\<star> Dom \<tau>) (Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>))) \<cdot>\<^sub>B
                     B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>)"
          proof -
            have "Map \<mu> \<star>\<^sub>B B.can (Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<nu> \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                            (Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                              B.can (Dom \<nu> \<^bold>\<star> Dom \<tau>) (Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>) =
                    (B.can (Cod \<mu>) (Cod \<mu>) \<star>\<^sub>B B.can (Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<nu> \<^bold>\<star> Cod \<tau>)) \<cdot>\<^sub>B
                       (Map \<mu> \<star>\<^sub>B (Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                          B.can (Dom \<nu> \<^bold>\<star> Dom \<tau>) (Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>))"
              using assms B.interchange B.comp_cod_arr
              by (metis (no_types, lifting) B.can_Ide_self B.in_homE Map_hcomp arrE hseq_char)
            also have "... = (B.can (Cod \<mu>) (Cod \<mu>) \<star>\<^sub>B
                                 B.can (Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<nu> \<^bold>\<star> Cod \<tau>)) \<cdot>\<^sub>B
                               (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                                 (B.can (Dom \<mu>) (Dom \<mu>) \<star>\<^sub>B
                                    B.can (Dom \<nu> \<^bold>\<star> Dom \<tau>) (Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>))"
              using assms B.interchange B.comp_arr_dom [of "Map \<mu>" "B.can (Dom \<mu>) (Dom \<mu>)"]
              by (metis (no_types, lifting) B.can_Ide_self B.comp_null(2) B.ext B.in_homE
                  Map_hcomp arrE hseq_char)
            finally have
              "Map \<mu> \<star>\<^sub>B B.can (Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<nu> \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                 (Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                   B.can (Dom \<nu> \<^bold>\<star> Dom \<tau>) (Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>) =
              (B.can (Cod \<mu>) (Cod \<mu>) \<star>\<^sub>B B.can (Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<nu> \<^bold>\<star> Cod \<tau>)) \<cdot>\<^sub>B
                (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                  (B.can (Dom \<mu>) (Dom \<mu>) \<star>\<^sub>B B.can (Dom \<nu> \<^bold>\<star> Dom \<tau>) (Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>))"
              by simp
            thus ?thesis by simp
          qed
          also have
            "... = (B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) \<cdot>\<^sub>B
                     (B.can (Cod \<mu>) (Cod \<mu>) \<star>\<^sub>B B.can (Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<nu> \<^bold>\<star> Cod \<tau>))) \<cdot>\<^sub>B
                       (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                         ((B.can (Dom \<mu>) (Dom \<mu>) \<star>\<^sub>B
                             B.can (Dom \<nu> \<^bold>\<star> Dom \<tau>) (Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>)) \<cdot>\<^sub>B
                           B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>))"
            using B.comp_assoc by simp
          also have "... = B.can (Cod \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod \<tau>) (Cod \<mu> \<^bold>\<star> Cod \<nu> \<^bold>\<star> Cod \<tau>) \<cdot>\<^sub>B
                             (Map \<mu> \<star>\<^sub>B Map \<nu> \<star>\<^sub>B Map \<tau>) \<cdot>\<^sub>B
                                B.can (Dom \<mu> \<^bold>\<star> Dom \<nu> \<^bold>\<star> Dom \<tau>) (Dom \<mu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<nu> \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom \<tau>)"
            using assms \<mu>\<nu> \<nu>\<tau> E.HcompNml_assoc src_def trg_def arr_char
                  E.Src_HcompNml E.Trg_HcompNml E.Nml_HcompNml E.Ide_HcompNml
            by simp
          finally show ?thesis by simp
        qed
        ultimately show ?thesis by metis
      qed
    qed

    lemma obj_char:
    shows "obj a \<longleftrightarrow> endo a \<and> E.Obj (Dom a) \<and> Map a = \<lbrace>Dom a\<rbrace>"
    proof
      assume a: "obj a"
      show "endo a \<and> E.Obj (Dom a) \<and> Map a = \<lbrace>Dom a\<rbrace>"
      proof (intro conjI)
        show "endo a"
          using a ide_char by blast
        show "E.Obj (Dom a)"
          using a ide_char src_def
          by (metis (no_types, lifting) E.Ide_implies_Arr E.Obj_Trg arrE obj_def
              trg_simps(1) trg_src) 
        show "Map a = \<lbrace>Dom a\<rbrace>"
          using a ide_char src_def by blast
      qed
      next
      assume a: "endo a \<and> E.Obj (Dom a) \<and> Map a = \<lbrace>Dom a\<rbrace>"
      show "obj a"
      proof -
        have "arr a" using a by auto
        moreover have "src a = a"
          using a E.Obj_in_Hom(1) seq_char by (intro arr_eqI, auto)
        ultimately show ?thesis
          using obj_def by simp
      qed
    qed

    lemma hcomp_obj_self:
    assumes "obj a"
    shows "a \<star> a = a"
    proof (intro arr_eqI)
      show "H.hseq a a"
        using assms by auto
      show "arr a"
        using assms by auto
      show 1: "Dom (a \<star> a) = Dom a"
        unfolding hcomp_def
        using assms arr_char E.HcompNml_Trg_Nml
        apply simp
        by (metis (no_types, lifting) objE obj_def trg_simps(1))
      show 2: "Cod (a \<star> a) = Cod a"
        unfolding hcomp_def
        using assms 1 arr_char E.HcompNml_Trg_Nml
        apply simp
        by (metis (no_types, lifting) Dom_hcomp ideE objE)
      show "Map (a \<star> a) = Map a"
      proof -
        have "Map (a \<star> a) = B.can (Cod a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod a) (Cod a \<^bold>\<star> Cod a) \<cdot>\<^sub>B
                              (Map a \<star>\<^sub>B Map a) \<cdot>\<^sub>B
                                B.can (Dom a \<^bold>\<star> Dom a) (Dom a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom a)"
          using assms Map_hcomp by auto
        also have "... = B.can (Dom a) (Dom a \<^bold>\<star> Dom a) \<cdot>\<^sub>B
                           (\<lbrace>Dom a\<rbrace> \<star>\<^sub>B \<lbrace>Dom a\<rbrace>) \<cdot>\<^sub>B
                              B.can (Dom a \<^bold>\<star> Dom a) (Dom a)"
        proof -
          have "Dom a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom a = Dom a"
            using assms obj_char arr_char E.HcompNml_Trg_Nml
            by (metis (no_types, lifting) ideE objE obj_def' trg_simps(2))
          moreover have "Cod a = Dom a"
            using assms obj_char arr_char dom_char cod_char objE ide_char'
            by (metis (no_types, lifting) src_simps(1) src_simps(2))
          moreover have "Map a = \<lbrace>Dom a\<rbrace>"
            using assms obj_char by simp
          ultimately show ?thesis by simp
        qed
        also have "... = B.can (Dom a) (Dom a \<^bold>\<star> Dom a) \<cdot>\<^sub>B B.can (Dom a \<^bold>\<star> Dom a) (Dom a)"
          using assms obj_char arr_char B.comp_cod_arr E.ide_eval_Ide B.can_in_hom
          by (metis (no_types, lifting) H.ide_hcomp obj_def obj_def'
              calculation B.comp_ide_arr B.ide_hcomp B.hseqE B.ideD(1) ide_char B.seqE)
        also have "... = \<lbrace>Dom a\<rbrace>"
          using assms 1 2 obj_char arr_char B.vcomp_can calculation H.ide_hcomp ideE objE
          by (metis (no_types, lifting))
        also have "... = Map a"
          using assms obj_char by simp
        finally show ?thesis by simp
      qed
    qed

    lemma hcomp_ide_src:
    assumes "ide f"
    shows "f \<star> src f = f"
    proof (intro arr_eqI)
      show "H.hseq f (src f)"
        using assms by simp
      show "arr f"
        using assms by simp
      show 1: "Dom (f \<star> src f) = Dom f"
        unfolding hcomp_def
        using assms apply simp
        using assms ide_char arr_char E.HcompNml_Nml_Src
        by (metis (no_types, lifting) ideD(1))
      show "Cod (f \<star> src f) = Cod f"
        unfolding hcomp_def
        using assms apply simp
        using assms ide_char arr_char E.HcompNml_Nml_Src
        by (metis (no_types, lifting) ideD(1))
      show "Map (f \<star> src f) = Map f"
      proof -
        have "Map (f \<star> src f) = B.can (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (src f)) (Cod f \<^bold>\<star> Cod (src f)) \<cdot>\<^sub>B
                                  (Map f \<star>\<^sub>B Map (src f)) \<cdot>\<^sub>B
                                    B.can (Dom f \<^bold>\<star> Dom (src f)) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (src f))"
          unfolding hcomp_def
          using assms by simp
        also have "... = B.can (Dom f) (Dom f \<^bold>\<star> E.Src (Dom f)) \<cdot>\<^sub>B
                           (\<lbrace>Dom f\<rbrace> \<star>\<^sub>B \<lbrace>E.Src (Dom f)\<rbrace>) \<cdot>\<^sub>B
                             B.can (Dom f \<^bold>\<star> E.Src (Dom f)) (Dom f)"
          using assms arr_char E.HcompNml_Nml_Src by fastforce
        also have "... = B.can (Dom f) (Dom f \<^bold>\<star> E.Src (Dom f)) \<cdot>\<^sub>B
                           B.can (Dom f \<^bold>\<star> E.Src (Dom f)) (Dom f)"
        proof -
          have "\<guillemotleft>B.can (Dom f \<^bold>\<star> E.Src (Dom f)) (Dom f) :
                  \<lbrace>Dom f\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Dom f\<rbrace> \<star>\<^sub>B \<lbrace>E.Src (Dom f)\<rbrace>\<guillemotright>"
            using assms ide_char arr_char B.can_in_hom
            by (metis (no_types, lifting) B.canE_unitor(3) B.runit'_in_vhom E.eval_simps(2)
                E.Ide_implies_Arr ideE)
          thus ?thesis
            using B.comp_cod_arr by auto
        qed
        also have "... = \<lbrace>Dom f\<rbrace>"
          using assms 1 ide_char arr_char
          by (metis (no_types, lifting) H.ide_hcomp calculation ideE ide_src obj_def' obj_src)
        also have "... = Map f"
          using assms by auto
        finally show ?thesis by simp
      qed
    qed

    lemma hcomp_trg_ide:
    assumes "ide f"
    shows "trg f \<star> f = f"
    proof (intro arr_eqI)
      show "H.hseq (trg f) f"
        using assms by auto
      show "arr f"
        using assms by auto
      show 1: "Dom (trg f \<star> f) = Dom f"
        unfolding hcomp_def
        using assms apply simp
        using assms ide_char arr_char E.HcompNml_Trg_Nml
        by (metis (no_types, lifting) ideD(1))
      show "Cod (trg f \<star> f) = Cod f"
        unfolding hcomp_def
        using assms apply simp
        using assms ide_char arr_char E.HcompNml_Trg_Nml
        by (metis (no_types, lifting)  ideD(1))
      show "Map (trg f \<star> f) = Map f"
      proof -
        have "Map (trg f \<star> f) = B.can (Cod (trg f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod f) (Cod (trg f) \<^bold>\<star> Cod f) \<cdot>\<^sub>B
                                  (Map (trg f) \<star>\<^sub>B Map f) \<cdot>\<^sub>B
                                    B.can (Dom (trg f) \<^bold>\<star> Dom f) (Dom (trg f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom f)"
          unfolding hcomp_def
          using assms by simp
        also have "... = B.can (Dom f) (E.Trg (Dom f) \<^bold>\<star> Dom f) \<cdot>\<^sub>B
                           (\<lbrace>E.Trg (Dom f)\<rbrace> \<star>\<^sub>B \<lbrace>Dom f\<rbrace>) \<cdot>\<^sub>B
                             B.can (E.Trg (Dom f) \<^bold>\<star> Dom f) (Dom f)"
          using assms arr_char E.HcompNml_Trg_Nml by fastforce
        also have "... = B.can (Dom f) (E.Trg (Dom f) \<^bold>\<star> Dom f) \<cdot>\<^sub>B
                           B.can (E.Trg (Dom f) \<^bold>\<star> Dom f) (Dom f)"
        proof -
          have "\<guillemotleft>B.can (E.Trg (Dom f) \<^bold>\<star> Dom f) (Dom f) :
                  \<lbrace>Dom f\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>E.Trg (Dom f)\<rbrace> \<star>\<^sub>B \<lbrace>Dom f\<rbrace>\<guillemotright>"
            using assms ide_char arr_char B.can_in_hom
            by (metis (no_types, lifting) B.canE_unitor(4) B.lunit'_in_vhom E.Nml_implies_Arr
                E.eval_simps'(3) ideE)
          thus ?thesis
            using B.comp_cod_arr by auto
        qed
        also have "... = \<lbrace>Dom f\<rbrace>"
          using assms 1 ide_char arr_char
          by (metis (no_types, lifting) H.ide_hcomp Map_ide(1) calculation ideD(1)
              src_trg trg.preserves_ide)
        also have "... = Map f"
          using assms by auto
        finally show ?thesis by simp
      qed
    qed

    interpretation L: endofunctor vcomp H.L
      using H.endofunctor_L by auto
    interpretation R: endofunctor vcomp H.R
      using H.endofunctor_R by auto

    interpretation L: full_functor vcomp vcomp H.L
    proof
      fix a a' g
      assume a: "ide a" and a': "ide a'"
      assume g: "in_hom g (H.L a') (H.L a)"
      have a_eq: "a = MkIde (Dom a)"
        using a dom_char [of a] by simp
      have a'_eq: "a' = MkIde (Dom a')"
        using a' dom_char [of a'] by simp
      have 1: "Cod g = Dom a"
      proof -
        have "Dom (H.L a) = Dom a"
        proof -
          have "Dom (H.L a) = E.Trg (Dom a) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom a"
            using a trg_def hcomp_def
            apply simp
            by (metis (no_types, lifting) ideE src_trg trg.preserves_reflects_arr)
          also have "... = Dom a"
            using a arr_char E.Trg_HcompNml
            by (metis (no_types, lifting) E.HcompNml_Trg_Nml ideD(1))
          finally show ?thesis by simp
        qed
        thus ?thesis
          using g cod_char [of g]
          by (metis (no_types, lifting) Dom_cod in_homE)
      qed
      have 2: "Dom g = Dom a'"
      proof -
        have "Dom (H.L a') = Dom a'"
        proof -
          have "Dom (H.L a') = E.Trg (Dom a') \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom a'"
            using a' trg_def hcomp_def
            apply simp
            by (metis (no_types, lifting) ideE src_trg trg.preserves_reflects_arr)
          also have "... = Dom a'"
            using a' arr_char E.Trg_HcompNml
            by (metis (no_types, lifting) E.HcompNml_Trg_Nml ideD(1))
          finally show ?thesis by simp
        qed
        thus ?thesis
          using g dom_char [of g]
          by (metis (no_types, lifting) Dom_dom in_homE)
      qed
      let ?f = "MkArr (Dom a') (Cod a) (Map g)"
      have f: "in_hom ?f a' a"
      proof (intro in_homI)
        show 3: "arr (MkArr (Dom a') (Cod a) (Map g))"
        proof (intro arr_MkArr [of "Dom a'" "Cod a" "Map g"])
          show "Dom a' \<in> IDE"
            using a' ide_char arr_char by blast
          show "Cod a \<in> IDE"
            using a ide_char arr_char by blast
          show "Map g \<in> HOM (Dom a') (Cod a)"
          proof
            show "E.Src (Dom a') = E.Src (Cod a) \<and> E.Trg (Dom a') = E.Trg (Cod a) \<and>
                  \<guillemotleft>Map g : \<lbrace>Dom a'\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod a\<rbrace>\<guillemotright>"
              using a a' a_eq g 1 2 ide_char arr_char src_def trg_def trg_hcomp
              by (metis (no_types, lifting) Cod.simps(1) in_homE)
          qed
        qed
        show "dom (MkArr (Dom a') (Cod a) (Map g)) = a'"
          using a a' 3 dom_char by auto
        show "cod (MkArr (Dom a') (Cod a) (Map g)) = a"
          using a a' 3 cod_char by auto
      qed
      moreover have "H.L ?f = g"
      proof -
        have "H.L ?f =
              trg (MkArr (Dom a') (Cod a) (Map g)) \<star> MkArr (Dom a') (Cod a) (Map g)"
          using f by auto
        also have "... = MkIde (E.Trg (Cod a)) \<star> MkArr (Dom a') (Cod a) (Map g)"
          using a a' f trg_def [of a] vconn_implies_hpar by auto
        also have "... = MkArr (E.Trg (Cod a) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom a') (E.Trg (Cod a) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod a)
                               (B.can (E.Trg (Cod a) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod a) (E.Trg (Cod a) \<^bold>\<star> Cod a) \<cdot>\<^sub>B
                                 (\<lbrace>E.Trg (Cod a)\<rbrace> \<star>\<^sub>B Map g) \<cdot>\<^sub>B
                                 B.can (E.Trg (Cod a) \<^bold>\<star> Dom a') (E.Trg (Cod a) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom a'))"
          using hcomp_def
          apply simp
          by (metis (no_types, lifting) Cod.simps(1) arrE f in_homE src_trg trg.preserves_arr
              trg_def)
        also have "... = MkArr (Dom a') (Cod a)
                               (B.can (Cod a) (E.Trg (Cod a) \<^bold>\<star> Cod a) \<cdot>\<^sub>B
                                 (trg\<^sub>B \<lbrace>Cod a\<rbrace> \<star>\<^sub>B Map g) \<cdot>\<^sub>B
                                 B.can (E.Trg (Cod a) \<^bold>\<star> Dom a') (Dom a'))"
        proof -
          have "E.Trg (Cod a) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom a' = Dom a'"
            using a a' arr_char E.HcompNml_Trg_Nml
            by (metis (no_types, lifting) f ideE trg_simps(1) vconn_implies_hpar(4))
          moreover have "E.Trg (Cod a) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod a = Cod a"
            using a a' arr_char E.HcompNml_Trg_Nml by blast
          moreover have "\<lbrace>E.Trg (Cod a)\<rbrace> = trg\<^sub>B \<lbrace>Cod a\<rbrace>"
            using a a' arr_char E.eval_simps'(3) by fastforce
          ultimately show ?thesis by simp
        qed
        also have "... = MkArr (Dom a') (Cod a)
                           (B.lunit \<lbrace>Cod a\<rbrace> \<cdot>\<^sub>B (trg\<^sub>B \<lbrace>Cod a\<rbrace> \<star>\<^sub>B Map g) \<cdot>\<^sub>B B.lunit' \<lbrace>Dom a'\<rbrace>)"
        proof -
          have "E.Trg (Cod a) = E.Trg (Dom a')"
            using a a' a_eq g ide_char arr_char src_def trg_def trg_hcomp
                  \<open>Cod g = Dom a\<close> \<open>Dom g = Dom a'\<close>
            by (metis (no_types, lifting) Cod.simps(1) in_homE)
          moreover have "B.can (Cod a) (E.Trg (Cod a) \<^bold>\<star> Cod a) = B.lunit \<lbrace>Cod a\<rbrace>"
            using a ide_char arr_char B.canE_unitor(2) by blast
          moreover have "B.can (E.Trg (Dom a') \<^bold>\<star> Dom a') (Dom a') = B.lunit' \<lbrace>Dom a'\<rbrace>"
            using a' ide_char arr_char B.canE_unitor(4) by blast
          ultimately show ?thesis by simp
        qed
        also have "... = MkArr (Dom g) (Cod g) (Map g)"
        proof -
          have "src\<^sub>B \<lbrace>Cod a\<rbrace> = src\<^sub>B (Map g)"
            using a f g ide_char arr_char src_def B.comp_cod_arr
            by (metis (no_types, lifting) B.vconn_implies_hpar(1) B.vconn_implies_hpar(3)
                Cod.simps(1) Map.simps(1) in_homE)
          moreover have
            "B.lunit \<lbrace>Cod g\<rbrace> \<cdot>\<^sub>B (trg\<^sub>B (Map g) \<star>\<^sub>B Map g) \<cdot>\<^sub>B B.lunit' \<lbrace>Dom g\<rbrace> = Map g"
          proof -
            have "B.lunit \<lbrace>Cod g\<rbrace> \<cdot>\<^sub>B (trg\<^sub>B (Map g) \<star>\<^sub>B Map g) \<cdot>\<^sub>B B.lunit' \<lbrace>Dom g\<rbrace> =
                  B.lunit \<lbrace>Cod g\<rbrace> \<cdot>\<^sub>B B.lunit' \<lbrace>Cod g\<rbrace> \<cdot>\<^sub>B Map g"
              using g ide_char arr_char B.lunit'_naturality
              by (metis (no_types, lifting) partial_magma_axioms B.in_homE partial_magma.arrI)
            also have "... = (B.lunit \<lbrace>Cod g\<rbrace> \<cdot>\<^sub>B B.lunit' \<lbrace>Cod g\<rbrace>) \<cdot>\<^sub>B Map g"
              using B.comp_assoc by simp
            also have "... = Map g"
              using g arr_char E.ide_eval_Ide B.comp_arr_inv' B.comp_cod_arr by fastforce
            finally show ?thesis by simp
          qed
          ultimately have
            "B.lunit \<lbrace>Cod a\<rbrace> \<cdot>\<^sub>B (trg\<^sub>B \<lbrace>Cod a\<rbrace> \<star>\<^sub>B Map g) \<cdot>\<^sub>B B.lunit' \<lbrace>Dom a'\<rbrace> = Map g"
            using a a' 1 2 f g hcomp_def dom_char cod_char
            by (metis (no_types, lifting) B.comp_null(2) B.ext B.lunit_simps(2) B.lunit_simps(3)
                B.src.preserves_reflects_arr B.trg_vcomp B.vseq_implies_hpar(1) ideE)
          thus ?thesis
            using a 1 2 by auto
        qed
        also have "... = g"
          using g MkArr_Map by blast
        finally show ?thesis by simp
      qed
      ultimately show "\<exists>f. in_hom f a' a \<and> H.L f = g"
        by blast
    qed

    interpretation R: full_functor vcomp vcomp H.R
    proof
      fix a a' g
      assume a: "ide a" and a': "ide a'"
      assume g: "in_hom g (H.R a') (H.R a)"
      have a_eq: "a = MkIde (Dom a)"
        using a dom_char [of a] by simp
      have a'_eq: "a' = MkIde (Dom a')"
        using a' dom_char [of a'] by simp
      have 1: "Cod g = Dom a"
      proof -
        have "Dom (H.R a) = Dom a"
        proof -
          have "Dom (H.R a) = Dom a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom a)"
            using a src_def hcomp_def
            apply simp
            by (metis (no_types, lifting) ideE trg_src src.preserves_reflects_arr)
          also have "... = Dom a"
            using a arr_char E.Src_HcompNml
            by (metis (no_types, lifting) E.HcompNml_Nml_Src ideD(1))
          finally show ?thesis by simp
        qed
        thus ?thesis
          using g cod_char [of g]
          by (metis (no_types, lifting) Dom_cod in_homE)
      qed
      have 2: "Dom g = Dom a'"
      proof -
        have "Dom (H.R a') = Dom a'"
        proof -
          have "Dom (H.R a') = Dom a' \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom a')"
            using a' src_def hcomp_def
            apply simp
            by (metis (no_types, lifting) ideE trg_src src.preserves_reflects_arr)
          also have "... = Dom a'"
            using a' arr_char E.Src_HcompNml
            by (metis (no_types, lifting) E.HcompNml_Nml_Src ideD(1))
          finally show ?thesis by simp
        qed
        thus ?thesis
          using g dom_char [of g]
          by (metis (no_types, lifting) Dom_dom in_homE)
      qed
      let ?f = "MkArr (Dom a') (Cod a) (Map g)"
      have f: "in_hom ?f a' a"
      proof (intro in_homI)
        show 3: "arr (MkArr (Dom a') (Cod a) (Map g))"
        proof (intro arr_MkArr [of "Dom a'" "Cod a" "Map g"])
          show "Dom a' \<in> IDE"
            using a' ide_char arr_char by blast
          show "Cod a \<in> IDE"
            using a ide_char arr_char by blast
          show "Map g \<in> HOM (Dom a') (Cod a)"
          proof
            show "E.Src (Dom a') = E.Src (Cod a) \<and> E.Trg (Dom a') = E.Trg (Cod a) \<and>
                  \<guillemotleft>Map g : \<lbrace>Dom a'\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod a\<rbrace>\<guillemotright>"
              using a a' a_eq g 1 2 ide_char arr_char src_def trg_def trg_hcomp
              by (metis (no_types, lifting) Cod.simps(1) in_homE)
          qed
        qed
        show "dom (MkArr (Dom a') (Cod a) (Map g)) = a'"
          using a a' 3 dom_char by auto
        show "cod (MkArr (Dom a') (Cod a) (Map g)) = a"
          using a a' 3 cod_char by auto
      qed
      moreover have "H.R ?f = g"
      proof -
        have "H.R ?f =
               MkArr (Dom a') (Cod a) (Map g) \<star> src (MkArr (Dom a') (Cod a) (Map g))"
          using f by auto
        also have "... = MkArr (Dom a') (Cod a) (Map g) \<star> MkIde (E.Src (Cod a))"
          using a a' f src_def [of a] vconn_implies_hpar by auto
        also have "... = MkArr (Dom a' \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Cod a)) (Cod a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Cod a))
                               (B.can (Cod a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Cod a)) (Cod a \<^bold>\<star> E.Src (Cod a)) \<cdot>\<^sub>B
                                 (Map g \<star>\<^sub>B \<lbrace>E.Src (Cod a)\<rbrace>) \<cdot>\<^sub>B
                                 B.can (Dom a' \<^bold>\<star> E.Src (Cod a)) (Dom a' \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Cod a)))"
          using hcomp_def
          apply simp
          by (metis (no_types, lifting) Cod_cod arrE f in_homE trg_src src.preserves_arr src_def)
        also have "... = MkArr (Dom a') (Cod a)
                               (B.can (Cod a) (Cod a \<^bold>\<star> E.Src (Cod a)) \<cdot>\<^sub>B
                                 (Map g \<star>\<^sub>B src\<^sub>B \<lbrace>Cod a\<rbrace>) \<cdot>\<^sub>B
                                 B.can (Dom a' \<^bold>\<star> E.Src (Cod a)) (Dom a'))"
        proof -
          have "Dom a' \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Cod a) = Dom a'"
            using a a' arr_char E.HcompNml_Nml_Src
            by (metis (no_types, lifting) f ideE src_simps(1) vconn_implies_hpar(3))
          moreover have "Cod a \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Cod a) = Cod a"
            using a a' arr_char E.HcompNml_Nml_Src by blast
          moreover have "\<lbrace>E.Src (Cod a)\<rbrace> = src\<^sub>B \<lbrace>Cod a\<rbrace>"
            using a a' arr_char E.eval_simps'(2) by fastforce
          ultimately show ?thesis by simp
        qed
        also have "... = MkArr (Dom a') (Cod a)
                               (B.runit \<lbrace>Cod a\<rbrace> \<cdot>\<^sub>B (Map g \<star>\<^sub>B src\<^sub>B \<lbrace>Cod a\<rbrace>) \<cdot>\<^sub>B B.runit' \<lbrace>Dom a'\<rbrace>)"
        proof -
          have "E.Src (Cod a) = E.Src (Dom a')"
            using a a' g ide_char arr_char src_def trg_def src_hcomp
            by (metis (no_types, lifting) Cod_dom f ideE in_homE src_cod src_simps(1))
          moreover have "B.can (Cod a) (Cod a \<^bold>\<star> E.Src (Cod a)) = B.runit \<lbrace>Cod a\<rbrace>"
            using a ide_char arr_char B.canE_unitor(1) by blast
          moreover have "B.can (Dom a' \<^bold>\<star> E.Src (Dom a')) (Dom a') = B.runit' \<lbrace>Dom a'\<rbrace>"
            using a' ide_char arr_char B.canE_unitor(3) by blast
          ultimately show ?thesis by simp
        qed
        also have "... = MkArr (Dom g) (Cod g) (Map g)"
        proof -
          have "src\<^sub>B \<lbrace>Cod a\<rbrace> = src\<^sub>B (Map g)"
            using a f g ide_char arr_char src_def B.comp_cod_arr
            by (metis (no_types, lifting) B.vconn_implies_hpar(1) B.vconn_implies_hpar(3)
                Cod.simps(1) Map.simps(1) in_homE)
          moreover have
            "B.runit \<lbrace>Cod g\<rbrace> \<cdot>\<^sub>B (Map g \<star>\<^sub>B src\<^sub>B (Map g)) \<cdot>\<^sub>B B.runit' \<lbrace>Dom g\<rbrace> = Map g"
          proof -
            have "B.runit \<lbrace>Cod g\<rbrace> \<cdot>\<^sub>B (Map g \<star>\<^sub>B src\<^sub>B (Map g)) \<cdot>\<^sub>B B.runit' \<lbrace>Dom g\<rbrace> =
                  B.runit \<lbrace>Cod g\<rbrace> \<cdot>\<^sub>B B.runit'\<lbrace>Cod g\<rbrace> \<cdot>\<^sub>B Map g"
              using g ide_char arr_char B.runit'_naturality [of "Map g"]
              by (metis (no_types, lifting) partial_magma_axioms B.in_homE partial_magma.arrI)
            also have "... = (B.runit \<lbrace>Cod g\<rbrace> \<cdot>\<^sub>B B.runit' \<lbrace>Cod g\<rbrace>) \<cdot>\<^sub>B Map g"
              using B.comp_assoc by simp
            also have "... = Map g"
              using g arr_char E.ide_eval_Ide B.comp_arr_inv' B.comp_cod_arr by fastforce
            finally show ?thesis by simp
          qed
          ultimately have
            "B.runit \<lbrace>Cod a\<rbrace> \<cdot>\<^sub>B (Map g \<star>\<^sub>B src\<^sub>B \<lbrace>Cod a\<rbrace>) \<cdot>\<^sub>B B.runit' \<lbrace>Dom a'\<rbrace> = Map g"
            using a a' 1 2 f g hcomp_def dom_char cod_char
            by (metis (no_types, lifting) ideE)
          thus ?thesis
            using a 1 2 by auto
        qed
        also have "... = g"
           using g MkArr_Map by blast
        finally show ?thesis by simp
      qed
      ultimately show "\<exists>f. in_hom f a' a \<and> H.R f = g"
        by blast
    qed

    interpretation L: faithful_functor vcomp vcomp H.L
    proof
      fix f f'
      assume par: "par f f'" and eq: "H.L f = H.L f'"
      show "f = f'"
      proof (intro arr_eqI)
        have 1: "Dom f = Dom f' \<and> Cod f = Cod f'"
          using par dom_char cod_char by auto
        show "arr f"
          using par by simp
        show "arr f'"
          using par by simp
        show 2: "Dom f = Dom f'" and 3: "Cod f = Cod f'"
          using 1 by auto
        show "Map f = Map f'"
        proof -
          have "B.L (Map f) = trg\<^sub>B (Map f) \<star>\<^sub>B Map f"
            using par by auto
          also have "... = trg\<^sub>B (Map f') \<star>\<^sub>B Map f'"
          proof -
            have "\<lbrace>E.Trg (Dom f)\<rbrace> \<star>\<^sub>B Map f = \<lbrace>E.Trg (Dom f')\<rbrace> \<star>\<^sub>B Map f'"
            proof -
              have A: "\<guillemotleft>B.can (E.Trg (Dom f) \<^bold>\<star> Dom f) (E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom f) :
                          \<lbrace>E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom f\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>E.Trg (Dom f)\<rbrace> \<star>\<^sub>B \<lbrace>Dom f\<rbrace>\<guillemotright>"
                using par arr_char B.can_in_hom E.Ide_HcompNml
                      E.Ide_Nmlize_Ide E.Nml_Trg E.Nmlize_Nml E.HcompNml_Trg_Nml
                      src_def trg_def
                by (metis (no_types, lifting) E.eval_simps(3) E.ide_eval_Ide E.Ide_implies_Arr
                    B.canE_unitor(4) B.lunit'_in_vhom)
              have B: "\<guillemotleft>B.can (E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod f) (E.Trg (Dom f) \<^bold>\<star> Cod f) :
                          \<lbrace>E.Trg (Dom f)\<rbrace> \<star>\<^sub>B \<lbrace>Cod f\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod f\<rbrace>\<guillemotright>"
                using par arr_char B.can_in_hom E.Ide_HcompNml
                      E.Ide_Nmlize_Ide E.Nml_Trg E.Nmlize_Nml E.HcompNml_Trg_Nml
                      src_def trg_def
                by (metis (no_types, lifting) E.Nmlize.simps(3) E.eval.simps(3) E.Ide.simps(3)
                    E.Ide_implies_Arr E.Src_Trg trg.preserves_arr trg_simps(2))
              have C: "\<guillemotleft>\<lbrace>E.Trg (Dom f)\<rbrace> \<star>\<^sub>B Map f :
                          \<lbrace>E.Trg (Dom f)\<rbrace> \<star>\<^sub>B \<lbrace>Dom f\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>E.Trg (Dom f)\<rbrace> \<star>\<^sub>B \<lbrace>Cod f\<rbrace>\<guillemotright>"
                using par arr_char
                by (metis (no_types, lifting) E.eval_simps'(1) E.eval_simps(3) E.ide_eval_Ide
                    E.Ide_implies_Arr E.Obj_Trg E.Obj_implies_Ide B.hcomp_in_vhom
                    B.ide_in_hom(2) B.src_trg)
              have 3: "(\<lbrace>E.Trg (Dom f)\<rbrace> \<star>\<^sub>B Map f) \<cdot>\<^sub>B
                          B.can (E.Trg (Dom f) \<^bold>\<star> Dom f) (E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom f) =
                        (\<lbrace>E.Trg (Dom f')\<rbrace> \<star>\<^sub>B Map f') \<cdot>\<^sub>B
                            B.can (E.Trg (Dom f') \<^bold>\<star> Dom f') (E.Trg (Dom f') \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom f')"
              proof -
                have 2: "B.can (E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod f) (E.Trg (Dom f) \<^bold>\<star> Cod f) \<cdot>\<^sub>B
                          (\<lbrace>E.Trg (Dom f)\<rbrace> \<star>\<^sub>B Map f) \<cdot>\<^sub>B
                            B.can (E.Trg (Dom f) \<^bold>\<star> Dom f) (E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom f) =
                         B.can (E.Trg (Dom f') \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod f') (E.Trg (Dom f') \<^bold>\<star> Cod f') \<cdot>\<^sub>B
                           (\<lbrace>E.Trg (Dom f')\<rbrace> \<star>\<^sub>B Map f') \<cdot>\<^sub>B
                             B.can (E.Trg (Dom f') \<^bold>\<star> Dom f') (E.Trg (Dom f') \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom f')"
                  using par eq hcomp_def trg_def src_trg trg.preserves_arr Map_hcomp
                        trg_simps(1) trg_simps(2) trg_simps(3)
                  by auto
                have "B.mono (B.can (E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod f) (E.Trg (Dom f) \<^bold>\<star> Cod f))"
                  using par arr_char B.inverse_arrows_can B.iso_is_section B.section_is_mono
                        src_def trg_def E.Nmlize_Nml E.HcompNml_Trg_Nml E.Ide_implies_Arr
                        trg.preserves_arr trg_simps(1)
                  by auto
                moreover have
                  "B.seq (B.can (E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod f) (E.Trg (Dom f) \<^bold>\<star> Cod f))
                     ((\<lbrace>E.Trg (Dom f)\<rbrace> \<star>\<^sub>B Map f) \<cdot>\<^sub>B
                       B.can (E.Trg (Dom f) \<^bold>\<star> Dom f) (E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom f))"
                  using A B C by auto
                moreover have
                  "B.seq (B.can (E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod f) (E.Trg (Dom f) \<^bold>\<star> Cod f))
                     ((\<lbrace>E.Trg (Dom f')\<rbrace> \<star>\<^sub>B Map f') \<cdot>\<^sub>B
                       B.can (E.Trg (Dom f') \<^bold>\<star> Dom f') (E.Trg (Dom f') \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom f'))"
                  using par 1 2 arr_char calculation(2) by auto
                moreover have "B.can (E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod f) (E.Trg (Dom f) \<^bold>\<star> Cod f) =
                               B.can (E.Trg (Dom f') \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod f') (E.Trg (Dom f') \<^bold>\<star> Cod f')"
                  using par 1 arr_char by simp
                ultimately show ?thesis
                  using 2 B.monoE cod_char by auto
              qed
              show ?thesis
              proof -
                have "B.epi (B.can (E.Trg (Dom f) \<^bold>\<star> Dom f) (E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom f))"
                  using par arr_char B.inverse_arrows_can B.iso_is_retraction
                        B.retraction_is_epi E.Nmlize_Nml E.HcompNml_Trg_Nml src_def trg_def
                        E.Ide_implies_Arr
                  by (metis (no_types, lifting) E.Nmlize.simps(3) E.Ide.simps(3) E.Src_Trg
                      trg.preserves_arr trg_simps(1))
                moreover have "B.seq (\<lbrace>E.Trg (Dom f)\<rbrace> \<star>\<^sub>B Map f)
                                     (B.can (E.Trg (Dom f) \<^bold>\<star> Dom f) (E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom f))"
                  using A C by auto
                moreover have "B.seq (\<lbrace>E.Trg (Dom f')\<rbrace> \<star>\<^sub>B Map f')
                                     (B.can (E.Trg (Dom f) \<^bold>\<star> Dom f) (E.Trg (Dom f) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom f))"
                  using 1 3 calculation(2) by auto
                ultimately show ?thesis
                  using par 1 3 arr_char B.epiE by simp
              qed
            qed
            moreover have "trg\<^sub>B (Map f) = \<lbrace>E.Trg (Dom f)\<rbrace> \<and>
                           trg\<^sub>B (Map f') = \<lbrace>E.Trg (Dom f')\<rbrace>"
              using par arr_char trg_def E.Ide_implies_Arr B.comp_arr_dom
                    B.vseq_implies_hpar(2) E.eval_simps(3)
              by (metis (no_types, lifting) B.vconn_implies_hpar(2))
            ultimately show ?thesis by simp
          qed
          also have "... = B.L (Map f')"
            using par B.hseqE B.hseq_char' by auto
          finally have "B.L (Map f) = B.L (Map f')"
            by simp
          thus ?thesis
            using 2 3 par arr_char B.L.is_faithful
            by (metis (no_types, lifting) B.in_homE)
        qed
      qed
    qed

    interpretation R: faithful_functor vcomp vcomp H.R
    proof
      fix f f'
      assume par: "par f f'" and eq: "H.R f = H.R f'"
      show "f = f'"
      proof (intro arr_eqI)
        have 1: "Dom f = Dom f' \<and> Cod f = Cod f'"
          using par dom_char cod_char by auto
        show "arr f"
          using par by simp
        show "arr f'"
          using par by simp
        show 2: "Dom f = Dom f'" and 3: "Cod f = Cod f'"
          using 1 by auto
        show "Map f = Map f'"
        proof -
          have "B.R (Map f) = Map f \<star>\<^sub>B src\<^sub>B (Map f)"
            using par apply simp by (metis B.hseqE B.hseq_char')
          also have "... = Map f' \<star>\<^sub>B src\<^sub>B (Map f')"
          proof -
            have "Map f \<star>\<^sub>B \<lbrace>E.Src (Dom f)\<rbrace> = Map f' \<star>\<^sub>B \<lbrace>E.Src (Dom f')\<rbrace>"
            proof -
              have 2: "E.Ide (Cod f \<^bold>\<star> E.Src (Dom f))"
                using par arr_char src.preserves_arr by auto
              hence 3: "E.Ide (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f))"
                using par arr_char E.Nml_Src E.Ide_HcompNml calculation by auto
              have 4: "\<^bold>\<lfloor>Cod f \<^bold>\<star> E.Src (Dom f)\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)\<^bold>\<rfloor>"
                using par arr_char by (simp add: E.Nml_HcompNml(1))
              have A: "\<guillemotleft>B.can (Dom f \<^bold>\<star> E.Src (Dom f)) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)) :
                          \<lbrace>Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Dom f\<rbrace> \<star>\<^sub>B \<lbrace>E.Src (Dom f)\<rbrace>\<guillemotright>"
                using par arr_char B.can_in_hom E.Ide_HcompNml
                      E.Ide_Nmlize_Ide E.Nml_Src E.Nmlize_Nml E.HcompNml_Nml_Src
                      src_def trg_def
                by (metis (no_types, lifting) E.eval_simps(2) E.ide_eval_Ide E.Ide_implies_Arr
                    B.canE_unitor(3) B.runit'_in_vhom)
              have B: "\<guillemotleft>B.can (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)) (Cod f \<^bold>\<star> E.Src (Dom f)) :
                          \<lbrace>Cod f\<rbrace> \<star>\<^sub>B \<lbrace>E.Src (Dom f)\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)\<rbrace>\<guillemotright>"
                using 2 3 4 B.can_in_hom [of "Cod f \<^bold>\<star> E.Src (Dom f)" "Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)"]
                by simp
              have C: "\<guillemotleft>Map f \<star>\<^sub>B \<lbrace>E.Src (Dom f)\<rbrace> :
                         \<lbrace>Dom f\<rbrace> \<star>\<^sub>B \<lbrace>E.Src (Dom f)\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod f\<rbrace> \<star>\<^sub>B \<lbrace>E.Src (Dom f)\<rbrace>\<guillemotright>"
                using par arr_char E.Ide_Nmlize_Ide E.Nml_Trg E.Nmlize_Nml E.HcompNml_Trg_Nml
                      src_def trg_def E.ide_eval_Ide E.Ide_implies_Arr E.Obj_implies_Ide
                apply (intro B.hcomp_in_vhom)
                  apply (simp add: B.ide_in_hom(2))
                 apply simp
                by (metis (no_types, lifting) A B.ideD(1) B.not_arr_null B.seq_if_composable
                    B.src.preserves_reflects_arr B.vconn_implies_hpar(3) E.HcompNml_Nml_Src)
              have 5: "(Map f \<star>\<^sub>B \<lbrace>E.Src (Dom f)\<rbrace>) \<cdot>\<^sub>B
                          B.can (Dom f \<^bold>\<star> E.Src (Dom f)) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)) =
                        (Map f' \<star>\<^sub>B \<lbrace>E.Src (Dom f')\<rbrace>) \<cdot>\<^sub>B
                            B.can (Dom f' \<^bold>\<star> E.Src (Dom f')) (Dom f' \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f'))"
              proof -
                have 6: "B.can (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)) (Cod f \<^bold>\<star> E.Src (Dom f)) \<cdot>\<^sub>B
                           (Map f \<star>\<^sub>B \<lbrace>E.Src (Dom f)\<rbrace>) \<cdot>\<^sub>B
                             B.can (Dom f \<^bold>\<star> E.Src (Dom f)) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)) =
                         B.can (Cod f' \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f')) (Cod f' \<^bold>\<star> E.Src (Dom f')) \<cdot>\<^sub>B
                           (Map f' \<star>\<^sub>B \<lbrace>E.Src (Dom f')\<rbrace>) \<cdot>\<^sub>B
                             B.can (Dom f' \<^bold>\<star> E.Src (Dom f')) (Dom f' \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f'))"
                  using par eq hcomp_def src_def trg_src src.preserves_arr Map_hcomp
                        src_simps(1) src_simps(2) src_simps(3)
                  by auto
                have "B.mono (B.can (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)) (Cod f \<^bold>\<star> E.Src (Dom f)))"
                  using 2 3 4 B.inverse_arrows_can(1) B.iso_is_section B.section_is_mono
                  by simp
                moreover have
                  "B.seq (B.can (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)) (Cod f \<^bold>\<star> E.Src (Dom f)))
                     ((Map f \<star>\<^sub>B \<lbrace>E.Src (Dom f)\<rbrace>) \<cdot>\<^sub>B
                       B.can (Dom f \<^bold>\<star> E.Src (Dom f)) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)))"
                  using A B C by auto
                moreover have
                  "B.seq (B.can (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)) (Cod f \<^bold>\<star> E.Src (Dom f)))
                     ((Map f' \<star>\<^sub>B \<lbrace>E.Src (Dom f')\<rbrace>) \<cdot>\<^sub>B
                       B.can (Dom f' \<^bold>\<star> E.Src (Dom f')) (Dom f' \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f')))"
                  using par 1 6 arr_char calculation(2) by auto
                moreover have "B.can (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)) (Cod f \<^bold>\<star> E.Src (Dom f)) =
                               B.can (Cod f' \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f')) (Cod f' \<^bold>\<star> E.Src (Dom f'))"
                  using par 1 arr_char by simp
                ultimately show ?thesis
                  using 6 B.monoE cod_char by auto
              qed
              show ?thesis
              proof -
                have "B.epi (B.can (Dom f \<^bold>\<star> E.Src (Dom f)) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)))"
                  using 2 3 4 B.inverse_arrows_can(1) B.iso_is_retraction B.retraction_is_epi
                  by (metis (no_types, lifting) E.Nml_Src E.Nmlize.simps(3) E.Nmlize_Nml
                      E.HcompNml_Nml_Src E.Ide.simps(3) par arrE)
                moreover have "B.seq (Map f \<star>\<^sub>B \<lbrace>E.Src (Dom f)\<rbrace>)
                                   (B.can (Dom f \<^bold>\<star> E.Src (Dom f)) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)))"
                  using A C by auto
                moreover have "B.seq (Map f' \<star>\<^sub>B \<lbrace>E.Src (Dom f')\<rbrace>)
                                   (B.can (Dom f \<^bold>\<star> E.Src (Dom f)) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> E.Src (Dom f)))"
                  using 1 5 calculation(2) by auto
                ultimately show ?thesis
                  using par 1 5 arr_char B.epiE by simp
              qed
            qed
            moreover have "src\<^sub>B (Map f) = \<lbrace>E.Src (Dom f)\<rbrace> \<and>
                           src\<^sub>B (Map f') = \<lbrace>E.Src (Dom f')\<rbrace>"
              using par arr_char src_def
              by (metis (no_types, lifting) B.vconn_implies_hpar(1) E.Nml_implies_Arr
                  E.eval_simps(2))
            ultimately show ?thesis by simp
          qed
          also have "... = B.R (Map f')"
            using par B.hseqE B.hseq_char' by auto
          finally have "B.R (Map f) = B.R (Map f')"
            by simp
          thus ?thesis
            using 2 3 par arr_char B.R.is_faithful
            by (metis (no_types, lifting) B.in_homE)
        qed
      qed
    qed

    interpretation VxVxV: product_category vcomp VxV.comp ..
    interpretation VVV: subcategory VxVxV.comp
                 \<open>\<lambda>\<tau>\<mu>\<nu>. arr (fst \<tau>\<mu>\<nu>) \<and> VV.arr (snd \<tau>\<mu>\<nu>) \<and> src (fst \<tau>\<mu>\<nu>) = trg (fst (snd \<tau>\<mu>\<nu>))\<close>
      using subcategory_VVV by auto

    interpretation HoHV: "functor" VVV.comp vcomp H.HoHV
      using H.functor_HoHV by auto
    interpretation HoVH: "functor" VVV.comp vcomp H.HoVH
      using H.functor_HoVH by auto

    definition \<a>
    where "\<a> \<tau> \<mu> \<nu> \<equiv> if VVV.arr (\<tau>, \<mu>, \<nu>) then hcomp \<tau> (hcomp \<mu> \<nu>) else null"

    interpretation natural_isomorphism VVV.comp vcomp H.HoHV H.HoVH
                     \<open>\<lambda>\<tau>\<mu>\<nu>. \<a> (fst \<tau>\<mu>\<nu>) (fst (snd \<tau>\<mu>\<nu>)) (snd (snd \<tau>\<mu>\<nu>))\<close>
    proof
      show "\<And>\<tau>\<mu>\<nu>. \<not> VVV.arr \<tau>\<mu>\<nu> \<Longrightarrow> \<a> (fst \<tau>\<mu>\<nu>) (fst (snd \<tau>\<mu>\<nu>)) (snd (snd \<tau>\<mu>\<nu>)) = null"
        using \<a>_def by simp
      show "\<And>\<tau>\<mu>\<nu>. VVV.arr \<tau>\<mu>\<nu> \<Longrightarrow>
                  dom (\<a> (fst \<tau>\<mu>\<nu>) (fst (snd \<tau>\<mu>\<nu>)) (snd (snd \<tau>\<mu>\<nu>))) = H.HoHV (VVV.dom \<tau>\<mu>\<nu>)"
        using VVV.arr_char VV.arr_char \<a>_def hcomp_assoc H.HoHV_def by force
      show 1: "\<And>\<tau>\<mu>\<nu>. VVV.arr \<tau>\<mu>\<nu> \<Longrightarrow>
                     cod (\<a> (fst \<tau>\<mu>\<nu>) (fst (snd \<tau>\<mu>\<nu>)) (snd (snd \<tau>\<mu>\<nu>))) = H.HoVH (VVV.cod \<tau>\<mu>\<nu>)"
        using VVV.arr_char VV.arr_char \<a>_def H.HoVH_def by force
      show "\<And>\<tau>\<mu>\<nu>. VVV.arr \<tau>\<mu>\<nu> \<Longrightarrow>
                  H.HoVH \<tau>\<mu>\<nu> \<cdot>
                    \<a> (fst (VVV.dom \<tau>\<mu>\<nu>)) (fst (snd (VVV.dom \<tau>\<mu>\<nu>)))
                      (snd (snd (VVV.dom \<tau>\<mu>\<nu>))) =
                  \<a> (fst \<tau>\<mu>\<nu>) (fst (snd \<tau>\<mu>\<nu>)) (snd (snd \<tau>\<mu>\<nu>))"
        using \<a>_def HoVH.is_natural_1 H.HoVH_def by auto
      show "\<And>\<tau>\<mu>\<nu>. VVV.arr \<tau>\<mu>\<nu> \<Longrightarrow>
                   \<a> (fst (VVV.cod \<tau>\<mu>\<nu>)) (fst (snd (VVV.cod \<tau>\<mu>\<nu>)))
                     (snd (snd (VVV.cod \<tau>\<mu>\<nu>))) \<cdot> H.HoHV \<tau>\<mu>\<nu> =
                   \<a> (fst \<tau>\<mu>\<nu>) (fst (snd \<tau>\<mu>\<nu>)) (snd (snd \<tau>\<mu>\<nu>))"
      proof -
        fix \<tau>\<mu>\<nu>
        assume \<tau>\<mu>\<nu>: "VVV.arr \<tau>\<mu>\<nu>"
        have "H.HoHV \<tau>\<mu>\<nu> = \<a> (fst \<tau>\<mu>\<nu>) (fst (snd \<tau>\<mu>\<nu>)) (snd (snd \<tau>\<mu>\<nu>))"
          unfolding \<a>_def H.HoHV_def
          using \<tau>\<mu>\<nu> HoHV.preserves_cod hcomp_assoc VVV.arr_char VV.arr_char
          by simp
        thus "\<a> (fst (VVV.cod \<tau>\<mu>\<nu>)) (fst (snd (VVV.cod \<tau>\<mu>\<nu>))) (snd (snd (VVV.cod \<tau>\<mu>\<nu>))) \<cdot>
                H.HoHV \<tau>\<mu>\<nu> =
              \<a> (fst \<tau>\<mu>\<nu>) (fst (snd \<tau>\<mu>\<nu>)) (snd (snd \<tau>\<mu>\<nu>))"
          using 1 \<tau>\<mu>\<nu> comp_cod_arr \<a>_def
          by (metis (no_types, lifting) H.HoVH_def HoHV.preserves_arr prod.collapse)
      qed
      show "\<And>fgh. VVV.ide fgh \<Longrightarrow> iso (\<a> (fst fgh) (fst (snd fgh)) (snd (snd fgh)))"
        using \<a>_def HoVH.preserves_ide H.HoVH_def by auto
    qed

    definition \<i>
    where "\<i> \<equiv> \<lambda>a. a"

    sublocale bicategory vcomp hcomp \<a> \<i> src trg
      using hcomp_obj_self \<a>_def hcomp_assoc VVV.arr_char VV.arr_char
      apply unfold_locales
      by (auto simp add: \<i>_def ide_in_hom(2))

    lemma is_bicategory:
    shows "bicategory vcomp hcomp \<a> \<i> src trg"
      ..

    sublocale strict_bicategory vcomp hcomp \<a> \<i> src trg
    proof
      show "\<And>fgh. ide fgh \<Longrightarrow> lunit fgh = fgh"
      proof -
        fix fgh
        assume fgh: "ide fgh"
        have "fgh = lunit fgh"
        proof (intro lunit_eqI)
          show "ide fgh" using fgh by simp
          show "\<guillemotleft>fgh : trg fgh \<star> fgh \<Rightarrow> fgh\<guillemotright>"
            using fgh hcomp_def hcomp_trg_ide by auto
          show "trg fgh \<star> fgh = (\<i> (trg fgh) \<star> fgh) \<cdot> \<a>' (trg fgh) (trg fgh) fgh"
          proof -
            have "(\<i> (trg fgh) \<star> fgh) \<cdot> \<a>' (trg fgh) (trg fgh) fgh =
                  (trg fgh \<star> fgh) \<cdot> \<a>' (trg fgh) (trg fgh) fgh"
              using fgh \<i>_def by metis
            also have "... = (trg fgh \<star> fgh) \<cdot> (trg fgh \<star> trg fgh \<star> fgh)"
              using fgh \<a>_def by fastforce
            also have "... = trg fgh \<star> fgh"
              using fgh hcomp_obj_self hcomp_assoc
              by (simp add: hcomp_trg_ide)
            finally show ?thesis by simp
          qed
        qed
        thus "lunit fgh = fgh" by simp
      qed
      show "\<And>fgh. ide fgh \<Longrightarrow> runit fgh = fgh"
      proof -
        fix fgh
        assume fgh: "ide fgh"
        have "fgh = runit fgh"
        proof (intro runit_eqI)
          show "ide fgh" using fgh by simp
          show "\<guillemotleft>fgh : fgh \<star> src fgh \<Rightarrow> fgh\<guillemotright>"
            using fgh hcomp_def hcomp_ide_src by auto
          show "fgh \<star> src fgh = (fgh \<star> \<i> (src fgh)) \<cdot> \<a> fgh (src fgh) (src fgh)"
          proof -
            have "(fgh \<star> \<i> (src fgh)) \<cdot> \<a> fgh (src fgh) (src fgh) =
                  (fgh \<star> src fgh) \<cdot> \<a> fgh (src fgh) (src fgh)"
              using fgh \<i>_def by metis
            also have "... = (fgh \<star> src fgh) \<cdot> (fgh \<star> src fgh \<star> src fgh)"
              using fgh \<a>_def by fastforce
            also have "... = fgh \<star> src fgh"
              using fgh comp_arr_dom hcomp_obj_self by simp
            finally show ?thesis by simp
          qed
        qed
        thus "runit fgh = fgh" by simp
      qed
      show "\<And>f g h. \<lbrakk> ide f; ide g; ide h; src f = trg g; src g = trg h \<rbrakk> \<Longrightarrow> ide (\<a> f g h)"
        using \<a>_def VV.arr_char VVV.arr_char by auto
    qed

    theorem is_strict_bicategory:
    shows "strict_bicategory vcomp hcomp \<a> \<i> src trg"
      ..

    subsection "The Strictness Theorem"

    text \<open>
      The Strictness Theorem asserts: ``Every bicategory is biequivalent to a strict bicategory.''
      This amounts to an equivalent (and perhaps more desirable) formulation of the
      Coherence Theorem.
      In this section we prove the Strictness Theorem by constructing an equivalence pseudofunctor
      from a bicategory to its strictification.
    \<close>

    lemma iso_char:
    shows "iso \<mu> \<longleftrightarrow> arr \<mu> \<and> B.iso (Map \<mu>)"
    and "iso \<mu> \<Longrightarrow> inv \<mu> = MkArr (Cod \<mu>) (Dom \<mu>) (B.inv (Map \<mu>))"
    proof -
      have 1: "iso \<mu> \<Longrightarrow> arr \<mu> \<and> B.iso (Map \<mu>)"
      proof -
        assume \<mu>: "iso \<mu>"
        obtain \<nu> where \<nu>: "inverse_arrows \<mu> \<nu>"
          using \<mu> by auto
        have "B.inverse_arrows (Map \<mu>) (Map \<nu>)"
        proof
          show "B.ide (Map \<mu> \<cdot>\<^sub>B Map \<nu>)"
          proof -
            have "Map \<mu> \<cdot>\<^sub>B Map \<nu> = Map (\<mu> \<cdot> \<nu>)"
              using \<mu> \<nu> inverse_arrows_def Map_comp arr_char seq_char
              by (metis (no_types, lifting) ide_compE)
            moreover have "B.ide ..."
              using \<nu> ide_char by blast
            ultimately show ?thesis by simp
          qed
          show "B.ide (Map \<nu> \<cdot>\<^sub>B Map \<mu>)"
          proof -
            have "Map \<nu> \<cdot>\<^sub>B Map \<mu> = Map (\<nu> \<cdot> \<mu>)"
              using \<mu> \<nu> inverse_arrows_def comp_char [of \<nu> \<mu>] by simp
            moreover have "B.ide ..."
              using \<nu> ide_char by blast
            ultimately show ?thesis by simp
          qed
        qed
        thus "arr \<mu> \<and> B.iso (Map \<mu>)"
          using \<mu> by auto
      qed
      let ?\<nu> = "MkArr (Cod \<mu>) (Dom \<mu>) (B.inv (Map \<mu>))"
      have 2: "arr \<mu> \<and> B.iso (Map \<mu>) \<Longrightarrow> iso \<mu> \<and> inv \<mu> = ?\<nu>"
      proof
        assume \<mu>: "arr \<mu> \<and> B.iso (Map \<mu>)"
        have \<nu>: "\<guillemotleft>?\<nu> : cod \<mu> \<Rightarrow> dom \<mu>\<guillemotright>"
          using \<mu> arr_char dom_char cod_char by auto
        have 4: "inverse_arrows \<mu> ?\<nu>"
        proof
          show "ide (?\<nu> \<cdot> \<mu>)"
          proof -
            have "?\<nu> \<cdot> \<mu> = dom \<mu>"
              using \<mu> \<nu> MkArr_Map comp_char seq_char B.comp_inv_arr' dom_char by auto
            thus ?thesis
              using \<mu> by simp
          qed
          show "ide (\<mu> \<cdot> ?\<nu>)"
          proof -
            have "\<mu> \<cdot> ?\<nu> = cod \<mu>"
              using \<mu> \<nu> MkArr_Map comp_char seq_char B.comp_arr_inv' cod_char by auto
            thus ?thesis
              using \<mu> by simp
          qed
        qed
        thus "iso \<mu>" by auto
        show "inv \<mu> = ?\<nu>"
          using 4 inverse_unique by simp
      qed
      have 3: "arr \<mu> \<and> B.iso (Map \<mu>) \<Longrightarrow> iso \<mu>"
        using 2 by simp
      show "iso \<mu> \<longleftrightarrow> arr \<mu> \<and> B.iso (Map \<mu>)"
        using 1 3 by blast
      show "iso \<mu> \<Longrightarrow> inv \<mu> = ?\<nu>"
        using 1 2 by blast
    qed

    text \<open>
      We next define a map \<open>UP\<close> from the given bicategory \<open>B\<close> to its strictification,
      and show that it is an equivalence pseudofunctor.
      The following auxiliary definition is not logically necessary, but it provides some
      terms that can be the targets of simplification rules and thereby enables some proofs
      to be done by simplification that otherwise could not be.  Trying to eliminate it
      breaks some short proofs below, so I have kept it.
    \<close>

    definition UP\<^sub>0
    where "UP\<^sub>0 a \<equiv> if B.obj a then MkIde \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 else null"

    lemma obj_UP\<^sub>0 [simp]:
    assumes "B.obj a"
    shows "obj (UP\<^sub>0 a)"
      using assms UP\<^sub>0_def ide_MkIde [of "\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0"] src_def obj_def by simp

    lemma UP\<^sub>0_in_hom [intro]:
    assumes "B.obj a"
    shows "\<guillemotleft>UP\<^sub>0 a : UP\<^sub>0 a \<rightarrow> UP\<^sub>0 a\<guillemotright>"
    and "\<guillemotleft>UP\<^sub>0 a : UP\<^sub>0 a \<Rightarrow> UP\<^sub>0 a\<guillemotright>"
      using assms obj_UP\<^sub>0 by blast+

    lemma UP\<^sub>0_simps [simp]:
    assumes "B.obj a"
    shows "ide (UP\<^sub>0 a)" "arr (UP\<^sub>0 a)"
    and "src (UP\<^sub>0 a) = UP\<^sub>0 a" and "trg (UP\<^sub>0 a) = UP\<^sub>0 a"
    and "dom (UP\<^sub>0 a) = UP\<^sub>0 a" and "cod (UP\<^sub>0 a) = UP\<^sub>0 a"
      using assms obj_UP\<^sub>0
           apply blast
      using assms obj_UP\<^sub>0
          apply blast
      using assms obj_UP\<^sub>0 obj_simps
         apply simp_all
      using ideD(2) obj_UP\<^sub>0
       apply blast
      using ideD(3) obj_UP\<^sub>0
      by blast

    definition UP
    where "UP \<mu> \<equiv> if B.arr \<mu> then MkArr \<^bold>\<langle>B.dom \<mu>\<^bold>\<rangle> \<^bold>\<langle>B.cod \<mu>\<^bold>\<rangle> \<mu> else null"

    lemma Dom_UP [simp]:
    assumes "B.arr \<mu>"
    shows "Dom (UP \<mu>) = \<^bold>\<langle>B.dom \<mu>\<^bold>\<rangle>"
      using assms UP_def by fastforce

    lemma Cod_UP [simp]:
    assumes "B.arr \<mu>"
    shows "Cod (UP \<mu>) = \<^bold>\<langle>B.cod \<mu>\<^bold>\<rangle>"
      using assms UP_def by fastforce

    lemma Map_UP [simp]:
    assumes "B.arr \<mu>"
    shows "Map (UP \<mu>) = \<mu>"
      using assms UP_def by fastforce

    lemma arr_UP:
    assumes "B.arr \<mu>"
    shows "arr (UP \<mu>)"
      using assms UP_def
      by (intro arrI, fastforce+)

    lemma UP_in_hom [intro]:
    assumes "B.arr \<mu>"
    shows "\<guillemotleft>UP \<mu> : UP\<^sub>0 (src\<^sub>B \<mu>) \<rightarrow> UP\<^sub>0 (trg\<^sub>B \<mu>)\<guillemotright>"
    and "\<guillemotleft>UP \<mu> : UP (B.dom \<mu>) \<Rightarrow> UP (B.cod \<mu>)\<guillemotright>"
      using assms arr_UP UP_def UP\<^sub>0_def dom_char cod_char src_def trg_def by auto

    lemma UP_simps [simp]:
    assumes "B.arr \<mu>"
    shows "arr (UP \<mu>)"
    and "src (UP \<mu>) = UP\<^sub>0 (src\<^sub>B \<mu>)" and "trg (UP \<mu>) = UP\<^sub>0 (trg\<^sub>B \<mu>)"
    and "dom (UP \<mu>) = UP (B.dom \<mu>)" and "cod (UP \<mu>) = UP (B.cod \<mu>)"
      using assms arr_UP UP_in_hom by auto

    interpretation UP: "functor" V\<^sub>B vcomp UP
      using UP_def arr_UP UP_simps(4-5)
      apply unfold_locales
          apply auto[4]
      using arr_UP UP_def comp_char seq_char
      by auto

    interpretation UP: weak_arrow_of_homs V\<^sub>B src\<^sub>B trg\<^sub>B vcomp src trg UP
    proof
      fix \<mu>
      assume \<mu>: "B.arr \<mu>"
      show "isomorphic (UP (src\<^sub>B \<mu>)) (src (UP \<mu>))"
      proof -
        let ?\<phi> = "MkArr \<^bold>\<langle>src\<^sub>B \<mu>\<^bold>\<rangle> \<^bold>\<langle>src\<^sub>B \<mu>\<^bold>\<rangle>\<^sub>0 (src\<^sub>B \<mu>)"
        have \<phi>: "\<guillemotleft>?\<phi> : UP (src\<^sub>B \<mu>) \<Rightarrow> src (UP \<mu>)\<guillemotright>"
        proof
          show 1: "arr ?\<phi>"
            using \<mu> by (intro arrI, auto)
          show "dom ?\<phi> = UP (src\<^sub>B \<mu>)"
            using \<mu> 1 dom_char UP_def by simp
          show "cod ?\<phi> = src (UP \<mu>)"
            using \<mu> 1 cod_char src_def by auto
        qed
        have "iso ?\<phi>"
          using \<mu> \<phi> iso_char src_def by auto
        thus ?thesis
          using \<phi> isomorphic_def by auto
      qed
      show "isomorphic (UP (trg\<^sub>B \<mu>)) (trg (UP \<mu>))"
      proof -
        let ?\<phi> = "MkArr \<^bold>\<langle>trg\<^sub>B \<mu>\<^bold>\<rangle> \<^bold>\<langle>trg\<^sub>B \<mu>\<^bold>\<rangle>\<^sub>0 (trg\<^sub>B \<mu>)"
        have \<phi>: "\<guillemotleft>?\<phi> : UP (trg\<^sub>B \<mu>) \<Rightarrow> trg (UP \<mu>)\<guillemotright>"
        proof
          show 1: "arr ?\<phi>"
            using \<mu> by (intro arrI, auto)
          show "dom ?\<phi> = UP (trg\<^sub>B \<mu>)"
            using \<mu> 1 dom_char UP_def by simp
          show "cod ?\<phi> = trg (UP \<mu>)"
            using \<mu> 1 cod_char trg_def by auto
        qed
        have "iso ?\<phi>"
          using \<mu> \<phi> iso_char trg_def by auto
        thus ?thesis
          using \<phi> isomorphic_def by auto
      qed
    qed

    interpretation "functor" B.VV.comp VV.comp UP.FF
      using UP.functor_FF by auto
    interpretation HoUP_UP: composite_functor B.VV.comp VV.comp vcomp
                              UP.FF \<open>\<lambda>\<mu>\<nu>. hcomp (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close> ..
    interpretation UPoH: composite_functor B.VV.comp V\<^sub>B vcomp
                           \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>\<close> UP ..

    abbreviation \<Phi>\<^sub>o
    where "\<Phi>\<^sub>o fg \<equiv> MkArr (\<^bold>\<langle>fst fg\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>snd fg\<^bold>\<rangle>) \<^bold>\<langle>fst fg \<star>\<^sub>B snd fg\<^bold>\<rangle> (fst fg \<star>\<^sub>B snd fg)"

    interpretation \<Phi>: transformation_by_components
                        B.VV.comp vcomp HoUP_UP.map UPoH.map \<Phi>\<^sub>o
    proof
      fix fg
      assume fg: "B.VV.ide fg"
      show "\<guillemotleft>\<Phi>\<^sub>o fg : HoUP_UP.map fg \<Rightarrow> UPoH.map fg\<guillemotright>"
        using fg arr_char dom_char cod_char B.VV.ide_char B.VV.arr_char
              UP.FF_def UP_def hcomp_def B.can_Ide_self src_def trg_def
        apply (intro in_homI) by auto
      next
      fix \<mu>\<nu>
      assume \<mu>\<nu>: "B.VV.arr \<mu>\<nu>"
      show "\<Phi>\<^sub>o (B.VV.cod \<mu>\<nu>) \<cdot> HoUP_UP.map \<mu>\<nu> = UPoH.map \<mu>\<nu> \<cdot> \<Phi>\<^sub>o (B.VV.dom \<mu>\<nu>)"
      proof -
        have "\<Phi>\<^sub>o (B.VV.cod \<mu>\<nu>) \<cdot> HoUP_UP.map \<mu>\<nu> =
              MkArr (\<^bold>\<langle>B.dom (fst \<mu>\<nu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>B.dom (snd \<mu>\<nu>)\<^bold>\<rangle>)
                    (\<^bold>\<langle>B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>)\<^bold>\<rangle>)
                    (fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>)"
        proof -
          have "\<Phi>\<^sub>o (B.VV.cod \<mu>\<nu>) \<cdot> HoUP_UP.map \<mu>\<nu> =
                MkArr (\<^bold>\<langle>B.cod (fst \<mu>\<nu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>B.cod (snd \<mu>\<nu>)\<^bold>\<rangle>) (\<^bold>\<langle>B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>)\<^bold>\<rangle>)
                      (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>)) \<cdot>
                MkArr (\<^bold>\<langle>B.dom (fst \<mu>\<nu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>B.dom (snd \<mu>\<nu>)\<^bold>\<rangle>)
                      (\<^bold>\<langle>B.cod (fst \<mu>\<nu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>B.cod (snd \<mu>\<nu>)\<^bold>\<rangle>)
                      (fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>)"
            using \<mu>\<nu> B.VV.arr_char arr_char UP.FF_def hcomp_def UP_def
                  src_def trg_def B.can_in_hom B.can_Ide_self B.comp_arr_dom B.comp_cod_arr
            by auto
          also have "... = MkArr (\<^bold>\<langle>B.dom (fst \<mu>\<nu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>B.dom (snd \<mu>\<nu>)\<^bold>\<rangle>)
                                 (\<^bold>\<langle>B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>)\<^bold>\<rangle>)
                                 ((B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>)) \<cdot>\<^sub>B (fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>))"
            using \<mu>\<nu> B.VV.arr_char
            by (intro comp_MkArr arr_MkArr, auto)
          also have "... = MkArr (\<^bold>\<langle>B.dom (fst \<mu>\<nu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>B.dom (snd \<mu>\<nu>)\<^bold>\<rangle>)
                                 (\<^bold>\<langle>B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>)\<^bold>\<rangle>)
                                 (fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>)"
            using \<mu>\<nu> B.VV.arr_char B.comp_cod_arr by auto
          finally show ?thesis by simp
        qed
        also have "... = UPoH.map \<mu>\<nu> \<cdot> \<Phi>\<^sub>o (B.VV.dom \<mu>\<nu>)"
        proof -
          have "UPoH.map \<mu>\<nu> \<cdot> \<Phi>\<^sub>o (B.VV.dom \<mu>\<nu>) =
                MkArr (\<^bold>\<langle>B.dom (fst \<mu>\<nu>) \<star>\<^sub>B B.dom (snd \<mu>\<nu>)\<^bold>\<rangle>)
                      (\<^bold>\<langle>B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>)\<^bold>\<rangle>)
                      (fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>) \<cdot>
                MkArr (\<^bold>\<langle>B.dom (fst \<mu>\<nu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>B.dom (snd \<mu>\<nu>)\<^bold>\<rangle>)
                      (\<^bold>\<langle>B.dom (fst \<mu>\<nu>) \<star>\<^sub>B B.dom (snd \<mu>\<nu>)\<^bold>\<rangle>)
                      (B.dom (fst \<mu>\<nu>) \<star>\<^sub>B B.dom (snd \<mu>\<nu>))"
            using \<mu>\<nu> B.VV.arr_char arr_char UP.FF_def hcomp_def UP_def
                  src_def trg_def B.can_in_hom B.can_Ide_self B.comp_arr_dom B.comp_cod_arr
            by auto
          also have "... = MkArr (\<^bold>\<langle>B.dom (fst \<mu>\<nu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>B.dom (snd \<mu>\<nu>)\<^bold>\<rangle>)
                                 (\<^bold>\<langle>B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>)\<^bold>\<rangle>)
                                 ((fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>) \<cdot>\<^sub>B (B.dom (fst \<mu>\<nu>) \<star>\<^sub>B B.dom (snd \<mu>\<nu>)))"
            using \<mu>\<nu> B.VV.arr_char arr_MkArr
            apply (intro comp_MkArr arr_MkArr) by auto
          also have "... = MkArr (\<^bold>\<langle>B.dom (fst \<mu>\<nu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>B.dom (snd \<mu>\<nu>)\<^bold>\<rangle>)
                                 (\<^bold>\<langle>B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>)\<^bold>\<rangle>)
                                 (fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>)"
            using \<mu>\<nu> B.VV.arr_char B.comp_arr_dom by auto
         finally show ?thesis by simp
        qed
        finally show ?thesis by simp
      qed
    qed

    abbreviation \<Phi>
    where "\<Phi> \<equiv> \<Phi>.map"

    lemma \<Phi>_in_hom [intro]:
    assumes "B.arr (fst \<mu>\<nu>)" and "B.arr (snd \<mu>\<nu>)" and "src\<^sub>B (fst \<mu>\<nu>) = trg\<^sub>B (snd \<mu>\<nu>)"
    shows "\<guillemotleft>\<Phi> \<mu>\<nu> : UP\<^sub>0 (src\<^sub>B (snd \<mu>\<nu>)) \<rightarrow> UP\<^sub>0 (trg\<^sub>B (fst \<mu>\<nu>))\<guillemotright>"
    and "\<guillemotleft>\<Phi> \<mu>\<nu> : UP (B.dom (fst \<mu>\<nu>)) \<star> UP (B.dom (snd \<mu>\<nu>))
                    \<Rightarrow> UP (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>))\<guillemotright>"
    proof -
      let ?\<mu> = "fst \<mu>\<nu>" and ?\<nu> = "snd \<mu>\<nu>"
      show 1: "\<guillemotleft>\<Phi> \<mu>\<nu> : UP (B.dom ?\<mu>) \<star> UP (B.dom ?\<nu>) \<Rightarrow> UP (B.cod ?\<mu> \<star>\<^sub>B B.cod ?\<nu>)\<guillemotright>"
      proof
        show "arr (\<Phi> \<mu>\<nu>)"
          using assms by auto
        show "dom (\<Phi> \<mu>\<nu>) = UP (B.dom ?\<mu>) \<star> UP (B.dom ?\<nu>)"
        proof -
          have "B.VV.in_hom (?\<mu>, ?\<nu>) (B.dom ?\<mu>, B.dom ?\<nu>) (B.cod ?\<mu>, B.cod ?\<nu>)"
            using assms B.VV.in_hom_char B.VV.arr_char by auto
          hence "dom (\<Phi> \<mu>\<nu>) = HoUP_UP.map (B.dom ?\<mu>, B.dom ?\<nu>)"
            by auto
          also have "... = UP (B.dom ?\<mu>) \<star> UP (B.dom ?\<nu>)"
            using assms UP.FF_def by fastforce
          finally show ?thesis by simp
        qed
        show "cod (\<Phi> \<mu>\<nu>) = UP (B.cod ?\<mu> \<star>\<^sub>B B.cod ?\<nu>)"
          using assms B.VV.in_hom_char B.VV.arr_char by auto
      qed
      show "\<guillemotleft>\<Phi> \<mu>\<nu> : UP\<^sub>0 (src\<^sub>B ?\<nu>) \<rightarrow> UP\<^sub>0 (trg\<^sub>B ?\<mu>)\<guillemotright>"
        using assms 1 src_dom [of "\<Phi> \<mu>\<nu>"] trg_dom [of "\<Phi> \<mu>\<nu>"] by auto
    qed

    lemma \<Phi>_simps [simp]:
    assumes "B.arr (fst \<mu>\<nu>)" and "B.arr (snd \<mu>\<nu>)" and "src\<^sub>B (fst \<mu>\<nu>) = trg\<^sub>B (snd \<mu>\<nu>)"
    shows "arr (\<Phi> \<mu>\<nu>)"
    and "src (\<Phi> \<mu>\<nu>) = UP\<^sub>0 (src\<^sub>B (snd \<mu>\<nu>))" and "trg (\<Phi> \<mu>\<nu>) = UP\<^sub>0 (trg\<^sub>B (fst \<mu>\<nu>))"
    and "dom (\<Phi> \<mu>\<nu>) = UP (B.dom (fst \<mu>\<nu>)) \<star> UP (B.dom (snd \<mu>\<nu>))"
    and "cod (\<Phi> \<mu>\<nu>) = UP (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>))"
      using assms \<Phi>_in_hom [of \<mu>\<nu>] by auto

    lemma \<Phi>_ide_simps [simp]:
    assumes "B.ide (fst fg)" and "B.ide (snd fg)" and "src\<^sub>B (fst fg) = trg\<^sub>B (snd fg)"
    shows "Dom (\<Phi> fg) = \<^bold>\<langle>fst fg\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>snd fg\<^bold>\<rangle>"
    and "Cod (\<Phi> fg) = \<^bold>\<langle>fst fg \<star>\<^sub>B snd fg\<^bold>\<rangle>"
    and "Map (\<Phi> fg) = fst fg \<star>\<^sub>B snd fg"
      using assms B.VV.ide_char B.VV.arr_char by auto

    interpretation \<Phi>: natural_isomorphism B.VV.comp vcomp HoUP_UP.map UPoH.map \<Phi>
    proof
      fix fg
      assume fg: "B.VV.ide fg"
      have "arr (\<Phi> fg)"
        using fg \<Phi>.preserves_reflects_arr [of fg] by simp
      thus "iso (\<Phi> fg)"
        using fg iso_char by simp
    qed

    lemma \<Phi>_ide_simp:
    assumes "B.ide f" and "B.ide g" and "src\<^sub>B f = trg\<^sub>B g"
    shows "\<Phi> (f, g) = MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> (f \<star>\<^sub>B g)"
      using assms B.VV.ide_char B.VV.arr_char by simp

    lemma \<Phi>'_ide_simp:
    assumes "B.ide f" and "B.ide g" and "src\<^sub>B f = trg\<^sub>B g"
    shows "inv (\<Phi> (f, g)) = MkArr \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) (f \<star>\<^sub>B g)"
      using assms \<Phi>_ide_simp iso_char \<Phi>.components_are_iso [of "(f, g)"]
            B.VV.ide_char B.VV.arr_char
      by simp

    interpretation UP: pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B vcomp hcomp \<a> \<i> src trg UP \<Phi>
    proof
      fix f g h
      assume f: "B.ide f" and g: "B.ide g" and h: "B.ide h"
      and fg: "src\<^sub>B f = trg\<^sub>B g" and gh: "src\<^sub>B g = trg\<^sub>B h"
      show "UP \<a>\<^sub>B[f, g, h] \<cdot> \<Phi> (f \<star>\<^sub>B g, h) \<cdot> (\<Phi> (f, g) \<star> UP h) =
            \<Phi> (f, g \<star>\<^sub>B h) \<cdot> (UP f \<star> \<Phi> (g, h)) \<cdot> \<a> (UP f) (UP g) (UP h)"
      proof -
        have "UP \<a>\<^sub>B[f, g, h] \<cdot> \<Phi> (f \<star>\<^sub>B g, h) \<cdot> (\<Phi> (f, g) \<star> UP h) =
              MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g \<star>\<^sub>B h\<^bold>\<rangle> (f \<star>\<^sub>B g \<star>\<^sub>B h)"
        proof -
          have 1: "UP.hseq\<^sub>D (MkIde \<^bold>\<langle>f\<^bold>\<rangle>) (MkIde \<^bold>\<langle>g\<^bold>\<rangle>)"
            using f g fg hseq_char src_def trg_def arr_char by auto
          have 2: "UP.hseq\<^sub>D (MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> (f \<star>\<^sub>B g) \<cdot> MkIde (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>))
                            (MkIde \<^bold>\<langle>h\<^bold>\<rangle>)"
          proof -
            have "MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> (f \<star>\<^sub>B g) \<cdot> MkIde (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) =
                  MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> (f \<star>\<^sub>B g)"
            proof -
              have "MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> (f \<star>\<^sub>B g) \<cdot> MkIde (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) =
                    MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> (f \<star>\<^sub>B g) \<cdot> MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) (f \<star>\<^sub>B g)"
                using f g fg by simp
              also have "... = MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> ((f \<star>\<^sub>B g) \<cdot>\<^sub>B (f \<star>\<^sub>B g))"
                using f g fg by (intro comp_MkArr arr_MkArr, auto)
              also have "... = MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> (f \<star>\<^sub>B g)"
                using f g fg by simp
              finally show ?thesis by blast
            qed
            thus ?thesis
              using f g h fg gh arr_char src_def trg_def by auto
          qed
          have "UP \<a>\<^sub>B[f, g, h] = MkArr \<^bold>\<langle>(f \<star>\<^sub>B g) \<star>\<^sub>B h\<^bold>\<rangle> \<^bold>\<langle>f \<star>\<^sub>B g \<star>\<^sub>B h\<^bold>\<rangle> \<a>\<^sub>B[f, g, h]"
            using f g h fg gh UP_def B.HoHV_def B.HoVH_def B.VVV.arr_char B.VV.arr_char
                  B.VVV.dom_char B.VVV.cod_char
            by simp
          moreover have
            "\<Phi> (f \<star>\<^sub>B g, h) = MkArr (\<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<langle>(f \<star>\<^sub>B g) \<star>\<^sub>B h\<^bold>\<rangle> ((f \<star>\<^sub>B g) \<star>\<^sub>B h) \<cdot>
                             MkArr (\<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) ((f \<star>\<^sub>B g) \<star>\<^sub>B h)"
            using f g h fg gh \<Phi>.map_simp_ide \<Phi>.map_def UP.FF_def UP_def hcomp_def
                  B.VV.arr_char B.can_Ide_self B.comp_arr_dom B.comp_cod_arr src_def trg_def
            apply simp
            by (metis (no_types, lifting) B.ide_hcomp B.ide_char arr_UP)
          moreover have "\<Phi> (f, g) \<star> UP h =
                         MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (B.inv \<a>\<^sub>B[f, g, h])"
          proof -
            have "MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>)
                        (B.can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<cdot>\<^sub>B (f \<star>\<^sub>B g) \<cdot>\<^sub>B B.can (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>)) =
                  MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) (f \<star>\<^sub>B g)"
              using f g fg B.can_Ide_self B.comp_arr_dom B.comp_cod_arr by simp
            moreover have "MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> (f \<star>\<^sub>B g) \<cdot>
                             MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) (f \<star>\<^sub>B g) =
                           MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> (f \<star>\<^sub>B g)"
            proof -
              have "MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> (f \<star>\<^sub>B g) \<cdot>
                      MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) (f \<star>\<^sub>B g) =
                    MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> ((f \<star>\<^sub>B g) \<cdot>\<^sub>B (f \<star>\<^sub>B g))"
                using f g fg arr_MkArr by (intro comp_MkArr arr_MkArr) auto
              also have "... = MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> (f \<star>\<^sub>B g)"
                using f g fg by simp
              finally show ?thesis by blast
            qed
            moreover have "B.can ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) = B.inv \<a>\<^sub>B[f, g, h]"
              using f g h fg gh B.canI_associator_0 B.inverse_arrows_can by simp
            ultimately show ?thesis
              using 1 2 f g h fg gh \<Phi>.map_def UP_def hcomp_def UP.FF_def
                    B.VV.arr_char trg_def B.can_Ide_self B.comp_cod_arr
              by simp
          qed
          ultimately have "UP \<a>\<^sub>B[f, g, h] \<cdot> \<Phi> (f \<star>\<^sub>B g, h) \<cdot> (\<Phi> (f, g) \<star> UP h) =
                           MkArr \<^bold>\<langle>(f \<star>\<^sub>B g) \<star>\<^sub>B h\<^bold>\<rangle> \<^bold>\<langle>f \<star>\<^sub>B g \<star>\<^sub>B h\<^bold>\<rangle> \<a>\<^sub>B[f, g, h] \<cdot>
                             MkArr (\<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<langle>(f \<star>\<^sub>B g) \<star>\<^sub>B h\<^bold>\<rangle> ((f \<star>\<^sub>B g) \<star>\<^sub>B h) \<cdot>
                               MkArr (\<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) ((f \<star>\<^sub>B g) \<star>\<^sub>B h) \<cdot>
                                 MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (B.inv \<a>\<^sub>B[f, g, h])"
            using comp_assoc by presburger
          also have "... = MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g \<star>\<^sub>B h\<^bold>\<rangle>
                                 (\<a>\<^sub>B[f, g, h] \<cdot>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B h) \<cdot>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B h) \<cdot>\<^sub>B
                                   B.inv \<a>\<^sub>B[f, g, h])"
          proof -
            have "Arr (MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (B.inv \<a>\<^sub>B[f, g, h])) \<and>
                     Arr (MkArr (\<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) ((f \<star>\<^sub>B g) \<star>\<^sub>B h)) \<and>
                     Arr (MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>)
                                (((f \<star>\<^sub>B g) \<star>\<^sub>B h) \<cdot>\<^sub>B B.inv \<a>\<^sub>B[f, g, h])) \<and>
                     Arr (MkArr (\<^bold>\<langle>f \<star>\<^sub>B g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<langle>(f \<star>\<^sub>B g) \<star>\<^sub>B h\<^bold>\<rangle> ((f \<star>\<^sub>B g) \<star>\<^sub>B h)) \<and>
                     Arr (MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<langle>(f \<star>\<^sub>B g) \<star>\<^sub>B h\<^bold>\<rangle>
                          (((f \<star>\<^sub>B g) \<star>\<^sub>B h) \<cdot>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B h) \<cdot>\<^sub>B B.inv \<a>\<^sub>B[f, g, h])) \<and>
                     Arr (MkArr \<^bold>\<langle>(f \<star>\<^sub>B g) \<star>\<^sub>B h\<^bold>\<rangle> \<^bold>\<langle>f \<star>\<^sub>B g \<star>\<^sub>B h\<^bold>\<rangle> \<a>\<^sub>B[f, g, h])"
              using f g h fg gh B.\<alpha>.preserves_hom B.HoHV_def B.HoVH_def by auto
            thus ?thesis
              using f g h fg gh comp_def B.comp_arr_dom B.comp_cod_arr by simp
          qed
          also have "... = MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g \<star>\<^sub>B h\<^bold>\<rangle> (f \<star>\<^sub>B g \<star>\<^sub>B h)"
            using B.comp_cod_arr B.comp_arr_inv'
            by (auto simp add: f fg g gh h)
          finally show ?thesis by simp
        qed
        also have "... = \<Phi> (f, g \<star>\<^sub>B h) \<cdot> (UP f \<star> \<Phi> (g, h)) \<cdot> \<a> (UP f) (UP g) (UP h)"
        proof -
          have "\<Phi> (f, g \<star>\<^sub>B h) \<cdot> (UP f \<star> \<Phi> (g, h)) \<cdot> \<a> (UP f) (UP g) (UP h) =
                \<Phi> (f, g \<star>\<^sub>B h) \<cdot> (MkIde \<^bold>\<langle>f\<^bold>\<rangle> \<star> \<Phi> (g, h)) \<cdot> (MkIde \<^bold>\<langle>f\<^bold>\<rangle> \<star> MkIde \<^bold>\<langle>g\<^bold>\<rangle> \<star> MkIde \<^bold>\<langle>h\<^bold>\<rangle>)"
            using f g h fg gh VVV.arr_char VV.arr_char arr_char src_def trg_def UP_def \<a>_def
            by auto
          also have "... = MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g \<star>\<^sub>B h\<^bold>\<rangle> (f \<star>\<^sub>B g \<star>\<^sub>B h) \<cdot>
                            MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle>) (f \<star>\<^sub>B g \<star>\<^sub>B h) \<cdot>
                             MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle>) (f \<star>\<^sub>B g \<star>\<^sub>B h) \<cdot>
                              MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (f \<star>\<^sub>B g \<star>\<^sub>B h)"
          proof -
            have "\<Phi> (f, g \<star>\<^sub>B h) = MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g \<star>\<^sub>B h\<^bold>\<rangle> (f \<star>\<^sub>B g \<star>\<^sub>B h) \<cdot>
                                  MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle>) (f \<star>\<^sub>B g \<star>\<^sub>B h)"
              using f g h fg gh \<Phi>.map_simp_ide \<Phi>.map_def UP.FF_def UP_def hcomp_def
                    B.VV.arr_char B.can_Ide_self B.comp_arr_dom B.comp_cod_arr src_def trg_def
                    arr_char
              apply simp_all
              by blast
            moreover
            have "\<Phi> (g, h) = MkArr (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle> (g \<star>\<^sub>B h)"
              using f g h fg gh \<Phi>.map_def UP.FF_def UP_def hcomp_def B.VV.arr_char
                    B.can_Ide_self src_def trg_def arr_char
              by auto
            moreover have "MkIde \<^bold>\<langle>f\<^bold>\<rangle> \<star> MkArr (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle> (g \<star>\<^sub>B h) =
                           MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle>) (f \<star>\<^sub>B g \<star>\<^sub>B h)"
              using f g h fg gh hcomp_def arr_char src_def trg_def B.can_Ide_self
                    B.comp_arr_dom B.comp_cod_arr
              by auto
            moreover
            have "MkIde \<^bold>\<langle>f\<^bold>\<rangle> \<star> MkIde \<^bold>\<langle>g\<^bold>\<rangle> \<star> MkIde \<^bold>\<langle>h\<^bold>\<rangle> =
                  MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (f \<star>\<^sub>B g \<star>\<^sub>B h)"
            proof -
              have "\<guillemotleft>f : f \<Rightarrow>\<^sub>B f\<guillemotright> \<and> \<guillemotleft>g : g \<Rightarrow>\<^sub>B g\<guillemotright> \<and> \<guillemotleft>h : h \<Rightarrow>\<^sub>B h\<guillemotright>"
                using f g h by auto
              thus ?thesis
                using f g h fg gh hcomp_def arr_char src_def trg_def B.can_Ide_self
                      B.comp_arr_dom B.comp_cod_arr
                by simp
            qed
            ultimately show ?thesis
              using comp_assoc by auto
          qed
          also have "... = MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g \<star>\<^sub>B h\<^bold>\<rangle> (f \<star>\<^sub>B g \<star>\<^sub>B h)"
          proof -
            have "Arr (MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (f \<star>\<^sub>B g \<star>\<^sub>B h)) \<and>
                  Arr (MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle>) (f \<star>\<^sub>B g \<star>\<^sub>B h)) \<and>
                  Arr (MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle>) (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle>) (f \<star>\<^sub>B g \<star>\<^sub>B h)) \<and>
                  Arr (MkArr (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g \<star>\<^sub>B h\<^bold>\<rangle>) \<^bold>\<langle>f \<star>\<^sub>B g \<star>\<^sub>B h\<^bold>\<rangle> (f \<star>\<^sub>B g \<star>\<^sub>B h))"
              using f g h fg gh by auto
            thus ?thesis
              using f g h fg gh comp_def by auto
          qed
          finally show ?thesis by simp
        qed
        finally show ?thesis by blast
      qed
    qed

    lemma UP_is_pseudofunctor:
    shows "pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B vcomp hcomp \<a> \<i> src trg UP \<Phi>" ..

    lemma UP_map\<^sub>0_obj [simp]:
    assumes "B.obj a"
    shows "UP.map\<^sub>0 a = UP\<^sub>0 a"
      using assms UP.map\<^sub>0_def by auto

    interpretation UP: full_functor V\<^sub>B vcomp UP
    proof
      fix \<mu> f g
      assume f: "B.ide f" and g: "B.ide g"
      assume \<mu>: "\<guillemotleft>\<mu> : UP f \<Rightarrow> UP g\<guillemotright>"
      show "\<exists>\<nu>. \<guillemotleft>\<nu> : f \<Rightarrow>\<^sub>B g\<guillemotright> \<and> UP \<nu> = \<mu>"
      proof -
        have 1: "\<guillemotleft>Map \<mu> : f \<Rightarrow>\<^sub>B g\<guillemotright>"
          using f g \<mu> UP_def arr_char in_hom_char by auto
        moreover have "UP (Map \<mu>) = \<mu>"
        proof -
          have "\<mu> = MkArr (Dom \<mu>) (Cod \<mu>) (Map \<mu>)"
            using \<mu> MkArr_Map by auto
          also have "... = UP (Map \<mu>)"
            using f g \<mu> 1 UP_def arr_char dom_char cod_char
            apply simp
            by (metis (no_types, lifting) B.in_homE Dom.simps(1) in_homE)
          finally show ?thesis by auto
        qed
        ultimately show ?thesis by blast
      qed
    qed

    interpretation UP: faithful_functor V\<^sub>B vcomp UP
      using arr_char UP_def
      by (unfold_locales, simp_all)

    interpretation UP: fully_faithful_functor V\<^sub>B vcomp UP ..

    lemma UP_is_fully_faithful_functor:
    shows "fully_faithful_functor V\<^sub>B vcomp UP"
      ..

    no_notation B.in_hom  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")   (* Inherited from functor, I think. *)

    lemma Map_reflects_hhom:
    assumes "B.obj a" and "B.obj b" and "ide g"
    and "\<guillemotleft>g : UP.map\<^sub>0 a \<rightarrow> UP.map\<^sub>0 b\<guillemotright>"
    shows "\<guillemotleft>Map g : a \<rightarrow>\<^sub>B b\<guillemotright>"
    proof
      have 1: "B.ide (Map g)"
        using assms ide_char by blast
      show "B.arr (Map g)"
        using 1 by simp
      show "src\<^sub>B (Map g) = a"
      proof -
        have "src\<^sub>B (Map g) = Map (src g)"
          using assms src_def apply simp
          by (metis (no_types, lifting) E.eval_simps(2) E.Ide_implies_Arr arr_char ideE)
        also have "... = Map (UP.map\<^sub>0 a)"
          using assms by (metis (no_types, lifting) in_hhomE)
        also have "... = a"
          using assms UP.map\<^sub>0_def UP_def [of a] src_def by auto
        finally show ?thesis by simp
      qed
      show "trg\<^sub>B (Map g) = b"
      proof -
        have "trg\<^sub>B (Map g) = Map (trg g)"
          using assms trg_def apply simp
          by (metis (no_types, lifting) E.eval_simps(3) E.Ide_implies_Arr arr_char ideE)
        also have "... = Map (UP.map\<^sub>0 b)"
          using assms by (metis (no_types, lifting) in_hhomE)
        also have "... = b"
          using assms UP.map\<^sub>0_def UP_def [of b] src_def by auto
        finally show ?thesis by simp
      qed
    qed

    lemma eval_Dom_ide [simp]:
    assumes "ide g"
    shows "\<lbrace>Dom g\<rbrace> = Map g"
      using assms dom_char ideD by auto

    lemma Cod_ide:
    assumes "ide f"
    shows "Cod f = Dom f"
      using assms dom_char by auto

    lemma Map_preserves_objects:
    assumes "obj a"
    shows "B.obj (Map a)"
    proof -
      have "src\<^sub>B (Map a) = Map (src a)"
        using assms src_def apply simp
        using E.eval_simps(2) E.Ide_implies_Arr arr_char ideE
        by (metis (no_types, lifting) objE)
      also have 1: "... = \<lbrace>E.Src (Dom a)\<rbrace>"
        using assms src_def by auto
      also have "... = \<lbrace>\<^bold>\<langle>Map a\<^bold>\<rangle>\<^sub>0\<rbrace>"
        using assms B.src.is_extensional 1 by force
      also have "... = Map a"
        using assms by auto
      finally have "src\<^sub>B (Map a) = Map a" by simp
      moreover have "B.arr (Map a)"
        using assms B.ideD arr_char by auto
      ultimately show ?thesis
        using B.obj_def by simp
    qed

    interpretation UP: equivalence_pseudofunctor
                         V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B vcomp hcomp \<a> \<i> src trg UP \<Phi>
    proof
      (* UP is full, hence locally full. *)
      show "\<And>f f' \<nu>. \<lbrakk> B.ide f; B.ide f'; src\<^sub>B f = src\<^sub>B f'; trg\<^sub>B f = trg\<^sub>B f';
                       \<guillemotleft>\<nu> : UP f \<Rightarrow> UP f'\<guillemotright> \<rbrakk> \<Longrightarrow> \<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>B f'\<guillemotright> \<and> UP \<mu> = \<nu>"
        using UP.is_full by simp
      (* UP is essentially surjective up to equivalence on objects. *)
      show "\<And>b. obj b \<Longrightarrow> \<exists>a. B.obj a \<and> equivalent_objects (UP.map\<^sub>0 a) b"
      proof -
        fix b
        assume b: "obj b"
        have 1: "B.obj (Map b)"
          using b Map_preserves_objects by simp
        have 3: "UP.map\<^sub>0 (Map b) = MkArr \<^bold>\<langle>Map b\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>Map b\<^bold>\<rangle>\<^sub>0 (Map b)"
          using b 1 UP.map\<^sub>0_def [of "Map b"] UP_def src_def arr_char by auto
        have 4: "b = MkArr (Dom b) (Dom b) (Map b)"
          using b objE eval_Dom_ide
          by (metis (no_types, lifting) dom_char ideD(2) obj_def)
        let ?\<phi> = "MkArr \<^bold>\<langle>Map b\<^bold>\<rangle>\<^sub>0 (Dom b) (Map b)"
        have \<phi>: "arr ?\<phi>"
        proof -
          have 2: "E.Obj (Dom b)"
          proof -
            have "Dom b = Dom (src b)"
              using b obj_def by simp
            moreover have "Dom (src b) = E.Src (Dom b)"
              using b obj_def src_def arr_char by simp
            moreover have "E.Obj (E.Src (Dom b))"
              using b obj_def src_def arr_char arr_def E.Obj_Src by simp
            ultimately show ?thesis by simp
          qed
          have "E.Nml \<^bold>\<langle>Map b\<^bold>\<rangle>\<^sub>0 \<and> E.Ide \<^bold>\<langle>Map b\<^bold>\<rangle>\<^sub>0"
            using 1 by auto
          moreover have "E.Nml (Dom b) \<and> E.Ide (Dom b)"
            using b arr_char [of b] by auto
          moreover have "E.Src \<^bold>\<langle>Map b\<^bold>\<rangle>\<^sub>0 = E.Src (Dom b)"
            using b 1 2 B.obj_def obj_char
            by (cases "Dom b", simp_all)
          moreover have "E.Trg \<^bold>\<langle>Map b\<^bold>\<rangle>\<^sub>0 = E.Trg (Dom b)"
            using b 1 2 B.obj_def obj_char
            by (cases "Dom b", simp_all)
          moreover have "\<guillemotleft>Map b : \<lbrace>\<^bold>\<langle>Map b\<^bold>\<rangle>\<^sub>0\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Dom b\<rbrace>\<guillemotright>"
            using b 1 by (elim objE, auto)
          ultimately show ?thesis
            using arr_char \<open>E.Nml \<^bold>\<langle>Map b\<^bold>\<rangle>\<^sub>0 \<and> E.Ide \<^bold>\<langle>Map b\<^bold>\<rangle>\<^sub>0\<close> by auto
        qed
        hence "iso ?\<phi>"
          using 1 iso_char by auto
        moreover have "dom ?\<phi> = UP.map\<^sub>0 (Map b)"
          using \<phi> dom_char b 1 3 B.objE UP.map\<^sub>0_def UP_def src_def by auto
        moreover have "cod ?\<phi> = b"
          using \<phi> cod_char b 4 1 by auto
        ultimately have "isomorphic (UP.map\<^sub>0 (Map b)) b"
          using \<phi> 3 4 isomorphic_def by blast
        moreover have 5: "obj (UP.map\<^sub>0 (Map b))"
          using 1 UP.map\<^sub>0_simps(2) by simp
        ultimately have 6: "UP.map\<^sub>0 (Map b) = b"
          using b isomorphic_objects_are_equal by simp
        have "equivalent_objects (UP.map\<^sub>0 (Map b)) b"
          using b 6 equivalent_objects_reflexive [of b] by simp
        thus "\<exists>a. B.obj a \<and> equivalent_objects (UP.map\<^sub>0 a) b"
          using 1 6 by auto
      qed
      (* UP is locally essentially surjective. *)
      show "\<And>a b g. \<lbrakk> B.obj a; B.obj b; \<guillemotleft>g : UP.map\<^sub>0 a \<rightarrow> UP.map\<^sub>0 b\<guillemotright>; ide g \<rbrakk> \<Longrightarrow>
                        \<exists>f. \<guillemotleft>f : a \<rightarrow>\<^sub>B b\<guillemotright> \<and> B.ide f \<and> isomorphic (UP f) g"
      proof -
        fix a b g
        assume a: "B.obj a" and b: "B.obj b"
        assume g_in_hhom: "\<guillemotleft>g : UP.map\<^sub>0 a \<rightarrow> UP.map\<^sub>0 b\<guillemotright>"
        assume ide_g: "ide g"
        have 1: "B.ide (Map g)"
          using ide_g ide_char by blast
        have "arr (UP a)"
          using a by auto
        have "arr (UP b)"
          using b by auto
        have Map_g_eq: "Map g = \<lbrace>Dom g\<rbrace>"
          using ide_g by simp
        have Map_g_in_hhom: "\<guillemotleft>Map g : a \<rightarrow>\<^sub>B b\<guillemotright>"
          using a b ide_g g_in_hhom Map_reflects_hhom by simp

        let ?\<phi> = "MkArr \<^bold>\<langle>Map g\<^bold>\<rangle> (Dom g) (Map g)"
        have \<phi>: "arr ?\<phi>"
        proof -
          have "\<guillemotleft>Map ?\<phi> : \<lbrace>Dom ?\<phi>\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod ?\<phi>\<rbrace>\<guillemotright>"
            using 1 Map_g_eq by auto
          moreover have "E.Ide \<^bold>\<langle>Map g\<^bold>\<rangle> \<and> E.Nml \<^bold>\<langle>Map g\<^bold>\<rangle>"
            using 1 by simp
          moreover have "E.Ide (Dom g) \<and> E.Nml (Dom g)"
            using ide_g arr_char ide_char by blast
          moreover have "E.Src \<^bold>\<langle>Map g\<^bold>\<rangle> = E.Src (Dom g)"
            using ide_g g_in_hhom src_def Map_g_in_hhom
            by (metis (no_types, lifting) B.ideD(2) B.in_hhom_def B.objE B.obj_def'
                Dom.simps(1) E.Src.simps(2) UP.map\<^sub>0_def \<open>arr (UP a)\<close> a in_hhomE UP_def)
          moreover have "E.Trg \<^bold>\<langle>Map g\<^bold>\<rangle> = E.Trg (Dom g)"
          proof -
            have "E.Trg \<^bold>\<langle>Map g\<^bold>\<rangle> = \<^bold>\<langle>b\<^bold>\<rangle>\<^sub>0"
              using Map_g_in_hhom by auto
            also have "... = E.Trg (Dom g)"
            proof -
              have "E.Trg (Dom g) = Dom (trg g)"
                using ide_g trg_def by simp
              also have "... = Dom (UP.map\<^sub>0 b)"
                using g_in_hhom by auto
              also have "... = \<^bold>\<langle>b\<^bold>\<rangle>\<^sub>0"
                using b \<open>arr (UP b)\<close> UP.map\<^sub>0_def src_def UP_def B.objE by auto
              finally show ?thesis by simp
            qed
            finally show ?thesis by simp
          qed
          ultimately show ?thesis
            using arr_char by simp
        qed
        have "\<guillemotleft>?\<phi> : UP (Map g) \<Rightarrow> g\<guillemotright>"
        proof
          show "arr ?\<phi>"
            using \<phi> by simp
          show "dom ?\<phi> = UP (Map g)"
            using \<phi> 1 dom_char UP_def by simp
          show "cod ?\<phi> = g"
          proof -
            have "cod ?\<phi> = MkArr (Dom g) (Dom g) (Map g)"
              using ide_g cod_char Map_g_eq \<phi> by auto
            moreover have "Dom g = Cod g"
              using ide_g Cod_ide by simp
            ultimately have "cod ?\<phi> = MkArr (Dom g) (Cod g) (Map g)"
              by simp
            thus ?thesis
              by (metis (no_types, lifting) "1" B.comp_ide_self
                  \<open>Dom g = Cod g\<close> comp_cod_arr ideD(1) ideD(3) ide_g comp_char)
          qed
        qed
        moreover have "iso ?\<phi>"
          using \<phi> 1 iso_char by simp
        ultimately have "isomorphic (UP (Map g)) g"
          using isomorphic_def by auto
        thus "\<exists>f. \<guillemotleft>f : a \<rightarrow>\<^sub>B b\<guillemotright> \<and> B.ide f \<and> isomorphic (UP f) g"
          using 1 Map_g_in_hhom by auto
      qed
    qed

    theorem UP_is_equivalence_pseudofunctor:
    shows "equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B vcomp hcomp \<a> \<i> src trg UP \<Phi>" ..

    text \<open>
      Next, we work out the details of the equivalence pseudofunctor \<open>DN\<close> in the
      converse direction.
    \<close>

    definition DN
    where "DN \<mu> \<equiv> if arr \<mu> then Map \<mu> else B.null"

    lemma DN_in_hom [intro]:
    assumes "arr \<mu>"
    shows "\<guillemotleft>DN \<mu> : DN (src \<mu>) \<rightarrow>\<^sub>B DN (trg \<mu>)\<guillemotright>"
    and "\<guillemotleft>DN \<mu> : DN (dom \<mu>) \<Rightarrow>\<^sub>B DN (cod \<mu>)\<guillemotright>"
      using assms DN_def arr_char [of \<mu>] B.vconn_implies_hpar(1-2) E.eval_in_hom(1)
            B.in_hhom_def
      by auto

    lemma DN_simps [simp]:
    assumes "arr \<mu>"
    shows "B.arr (DN \<mu>)"
    and "src\<^sub>B (DN \<mu>) = DN (src \<mu>)" and "trg\<^sub>B (DN \<mu>) = DN (trg \<mu>)"
    and "B.dom (DN \<mu>) = DN (dom \<mu>)" and "B.cod (DN \<mu>) = DN (cod \<mu>)"
      using assms DN_in_hom by auto

    interpretation "functor" vcomp V\<^sub>B DN
      using DN_def seqE Map_comp seq_char
      by (unfold_locales, auto)

    interpretation DN: weak_arrow_of_homs vcomp src trg V\<^sub>B src\<^sub>B trg\<^sub>B DN
    proof
      fix \<mu>
      assume \<mu>: "arr \<mu>"
      show "B.isomorphic (DN (src \<mu>)) (src\<^sub>B (DN \<mu>))"
      proof -
        have "DN (src \<mu>) = src\<^sub>B (DN \<mu>)"
          using \<mu> DN_def arr_char E.eval_simps(2) E.Ide_implies_Arr
          apply simp
          by (metis (no_types, lifting) B.vconn_implies_hpar(1) E.Nml_implies_Arr ideE
              ide_src src_simps(3))
        moreover have "B.ide (DN (src \<mu>))"
          using \<mu> by simp
        ultimately show ?thesis
          using \<mu> B.isomorphic_reflexive by auto
      qed
      show "B.isomorphic (DN (trg \<mu>)) (trg\<^sub>B (DN \<mu>))"
      proof -
        have "DN (trg \<mu>) = trg\<^sub>B (DN \<mu>)"
          using \<mu> DN_def arr_char E.eval_simps(3) E.Ide_implies_Arr
          apply simp
          by (metis (no_types, lifting) B.vconn_implies_hpar(2) E.Nml_implies_Arr ideE
              ide_trg trg_simps(3))
        moreover have "B.ide (DN (trg \<mu>))"
          using \<mu> by simp
        ultimately show ?thesis
          using B.isomorphic_reflexive by auto
      qed
    qed

    interpretation "functor" VV.comp B.VV.comp DN.FF
      using DN.functor_FF by auto
    interpretation HoDN_DN: composite_functor VV.comp B.VV.comp V\<^sub>B
                      DN.FF \<open>\<lambda>\<mu>\<nu>. H\<^sub>B (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close> ..
    interpretation DNoH: composite_functor VV.comp vcomp V\<^sub>B
                      \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu>\<close> DN ..

    abbreviation \<Psi>\<^sub>o
    where "\<Psi>\<^sub>o fg \<equiv> B.can (Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg)) (Dom (fst fg) \<^bold>\<star> Dom (snd fg))"

    abbreviation \<Psi>\<^sub>o'
    where "\<Psi>\<^sub>o' fg \<equiv> B.can (Dom (fst fg) \<^bold>\<star> Dom (snd fg)) (Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg))"

    lemma \<Psi>\<^sub>o_in_hom:
    assumes "VV.ide fg"
    shows "\<guillemotleft>\<Psi>\<^sub>o fg : Map (fst fg) \<star>\<^sub>B Map (snd fg) \<Rightarrow>\<^sub>B \<lbrace>Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg)\<rbrace>\<guillemotright>"
    and "\<guillemotleft>\<Psi>\<^sub>o' fg : \<lbrace>Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg)\<rbrace> \<Rightarrow>\<^sub>B Map (fst fg) \<star>\<^sub>B Map (snd fg)\<guillemotright>"
    and "B.inverse_arrows (\<Psi>\<^sub>o fg) (\<Psi>\<^sub>o' fg)"
    proof -
      have 1: "E.Ide (Dom (fst fg) \<^bold>\<star> Dom (snd fg))"
        unfolding E.Ide.simps(3)
        apply (intro conjI)
        using assms VV.ide_char VV.arr_char arr_char
          apply simp
        using VV.arr_char VV.ideD(1) assms
         apply blast
        by (metis (no_types, lifting) VV.arrE VV.ideD(1) assms src_simps(1) trg_simps(1))
      have 2: "E.Ide (Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg))"
        using 1
        by (meson E.Ide.simps(3) E.Ide_HcompNml VV.arr_char VV.ideD(1) arr_char assms)
      have 3: "\<^bold>\<lfloor>Dom (fst fg) \<^bold>\<star> Dom (snd fg)\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg)\<^bold>\<rfloor>"
        by (metis (no_types, lifting) E.Ide.simps(3) E.Nml_HcompNml(1) E.Nmlize.simps(3)
            E.Nmlize_Nml VV.arr_char VV.ideD(1) arr_char assms 1)
      have 4: "\<lbrace>Dom (fst fg) \<^bold>\<star> Dom (snd fg)\<rbrace> = Map (fst fg) \<star>\<^sub>B Map (snd fg)"
        using assms VV.ide_char VV.arr_char arr_char by simp
      show "\<guillemotleft>\<Psi>\<^sub>o fg : Map (fst fg) \<star>\<^sub>B Map (snd fg) \<Rightarrow>\<^sub>B \<lbrace>Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg)\<rbrace>\<guillemotright>"
        using 1 2 3 4 by auto
      show "\<guillemotleft>\<Psi>\<^sub>o' fg : \<lbrace>Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg)\<rbrace> \<Rightarrow>\<^sub>B Map (fst fg) \<star>\<^sub>B Map (snd fg)\<guillemotright>"
        using 1 2 3 4 by auto
      show "B.inverse_arrows (\<Psi>\<^sub>o fg) (\<Psi>\<^sub>o' fg)"
        using 1 2 3 B.inverse_arrows_can by blast
    qed

    interpretation \<Psi>: transformation_by_components
                         VV.comp V\<^sub>B HoDN_DN.map DNoH.map \<Psi>\<^sub>o
    proof
      fix fg
      assume fg: "VV.ide fg"
      have 1: "\<lbrace>Dom (fst fg) \<^bold>\<star> Dom (snd fg)\<rbrace> = Map (fst fg) \<star>\<^sub>B Map (snd fg)"
        using fg VV.ide_char VV.arr_char arr_char by simp
      show "\<guillemotleft>\<Psi>\<^sub>o fg : HoDN_DN.map fg \<Rightarrow>\<^sub>B DNoH.map fg\<guillemotright>"
      proof
        show "B.arr (\<Psi>\<^sub>o fg)"
          using fg \<Psi>\<^sub>o_in_hom by blast
        show "B.dom (\<Psi>\<^sub>o fg) = HoDN_DN.map fg"
        proof -
          have "B.dom (\<Psi>\<^sub>o fg) = Map (fst fg) \<star>\<^sub>B Map (snd fg)"
            using fg \<Psi>\<^sub>o_in_hom by blast
          also have "... = HoDN_DN.map fg"
            using fg DN.FF_def DN_def VV.arr_char src_def trg_def VV.ide_char by auto
          finally show ?thesis by simp
        qed
        show "B.cod (\<Psi>\<^sub>o fg) = DNoH.map fg"
        proof -
          have "B.cod (\<Psi>\<^sub>o fg) = \<lbrace>Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg)\<rbrace>"
            using fg \<Psi>\<^sub>o_in_hom by blast
          also have "... = DNoH.map fg"
          proof -
            have "DNoH.map fg = 
                  B.can (Cod (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd fg)) (Cod (fst fg) \<^bold>\<star> Cod (snd fg)) \<cdot>\<^sub>B
                    (Map (fst fg) \<star>\<^sub>B Map (snd fg)) \<cdot>\<^sub>B
                      B.can (Dom (fst fg) \<^bold>\<star> Dom (snd fg)) (Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg))"
              using fg DN_def Map_hcomp VV.arr_char
              apply simp
              using VV.ideD(1) by blast
            also have "... =
                       B.can (Cod (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd fg)) (Cod (fst fg) \<^bold>\<star> Cod (snd fg)) \<cdot>\<^sub>B
                         B.can (Dom (fst fg) \<^bold>\<star> Dom (snd fg)) (Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg))"
            proof -
              have "(Map (fst fg) \<star>\<^sub>B Map (snd fg)) \<cdot>\<^sub>B
                      B.can (Dom (fst fg) \<^bold>\<star> Dom (snd fg)) (Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg)) =
                    B.can (Dom (fst fg) \<^bold>\<star> Dom (snd fg)) (Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg))"
                using fg 1 \<Psi>\<^sub>o_in_hom B.comp_cod_arr by blast
              thus ?thesis by simp
            qed
            also have "... = \<lbrace>Dom (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd fg)\<rbrace>"
            proof -
              have "B.can (Cod (fst fg) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd fg)) (Cod (fst fg) \<^bold>\<star> Cod (snd fg)) = \<Psi>\<^sub>o fg"
                using fg VV.ide_char Cod_ide by simp
              thus ?thesis
                using fg 1 \<Psi>\<^sub>o_in_hom [of fg] B.comp_arr_inv' by fastforce
            qed
            finally show ?thesis by simp
          qed
          finally show ?thesis by blast
        qed
      qed
      next
      show "\<And>f. VV.arr f \<Longrightarrow>
                   \<Psi>\<^sub>o (VV.cod f) \<cdot>\<^sub>B HoDN_DN.map f = DNoH.map f \<cdot>\<^sub>B \<Psi>\<^sub>o (VV.dom f)"
      proof -
        fix \<mu>\<nu>
        assume \<mu>\<nu>: "VV.arr \<mu>\<nu>"
        show "\<Psi>\<^sub>o (VV.cod \<mu>\<nu>) \<cdot>\<^sub>B HoDN_DN.map \<mu>\<nu> = DNoH.map \<mu>\<nu> \<cdot>\<^sub>B \<Psi>\<^sub>o (VV.dom \<mu>\<nu>)"
        proof -
          have 1: "E.Ide (Dom (fst \<mu>\<nu>) \<^bold>\<star> Dom (snd \<mu>\<nu>))"
            unfolding E.Ide.simps(3)
            apply (intro conjI)
            using \<mu>\<nu> VV.ide_char VV.arr_char arr_char
              apply simp
            using VV.arr_char VV.ideD(1) \<mu>\<nu>
             apply blast
            by (metis (no_types, lifting) VV.arrE \<mu>\<nu> src_simps(1) trg_simps(1))
          have 2: "E.Ide (Dom (fst \<mu>\<nu>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd \<mu>\<nu>))"
            using 1
            by (meson E.Ide.simps(3) E.Ide_HcompNml VV.arr_char VV.ideD(1) arr_char \<mu>\<nu>)
          have 3: "\<^bold>\<lfloor>Dom (fst \<mu>\<nu>) \<^bold>\<star> Dom (snd \<mu>\<nu>)\<^bold>\<rfloor> = \<^bold>\<lfloor>Dom (fst \<mu>\<nu>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd \<mu>\<nu>)\<^bold>\<rfloor>"
            by (metis (no_types, lifting) E.Ide.simps(3) E.Nml_HcompNml(1) E.Nmlize.simps(3)
               E.Nmlize_Nml VV.arr_char arr_char \<mu>\<nu> 1)
          have 4: "E.Ide (Cod (fst \<mu>\<nu>) \<^bold>\<star> Cod (snd \<mu>\<nu>))"
            unfolding E.Ide.simps(3)
            apply (intro conjI)
            using \<mu>\<nu> VV.ide_char VV.arr_char arr_char
              apply simp
            using VV.arr_char VV.ideD(1) \<mu>\<nu>
             apply blast
            by (metis (no_types, lifting) "1" E.Ide.simps(3) VV.arrE \<mu>\<nu> arrE)
          have 5: "E.Ide (Cod (fst \<mu>\<nu>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd \<mu>\<nu>))"
            using 4
            by (meson E.Ide.simps(3) E.Ide_HcompNml VV.arr_char VV.ideD(1) arr_char \<mu>\<nu>)
          have 6: "\<^bold>\<lfloor>Cod (fst \<mu>\<nu>) \<^bold>\<star> Cod (snd \<mu>\<nu>)\<^bold>\<rfloor> = \<^bold>\<lfloor>Cod (fst \<mu>\<nu>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd \<mu>\<nu>)\<^bold>\<rfloor>"
            by (metis (no_types, lifting) E.Ide.simps(3) E.Nml_HcompNml(1) E.Nmlize.simps(3)
               E.Nmlize_Nml VV.arr_char arr_char \<mu>\<nu> 1)
          have A: "\<guillemotleft>\<Psi>\<^sub>o' \<mu>\<nu> : \<lbrace>Dom (fst \<mu>\<nu>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom (snd \<mu>\<nu>)\<rbrace>
                                 \<Rightarrow>\<^sub>B \<lbrace>Dom (fst \<mu>\<nu>) \<^bold>\<star> Dom (snd \<mu>\<nu>)\<rbrace>\<guillemotright>"
            using 1 2 3 by auto
          have B: "\<guillemotleft>Map (fst \<mu>\<nu>) \<star>\<^sub>B Map (snd \<mu>\<nu>) :
                     \<lbrace>Dom (fst \<mu>\<nu>) \<^bold>\<star> Dom (snd \<mu>\<nu>)\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod (fst \<mu>\<nu>) \<^bold>\<star> Cod (snd \<mu>\<nu>)\<rbrace>\<guillemotright>"
            using \<mu>\<nu> VV.arr_char arr_char src_def trg_def E.Nml_implies_Arr E.eval_simps'(2-3)
            by auto
          have C: "\<guillemotleft>B.can (Cod (fst \<mu>\<nu>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd \<mu>\<nu>)) (Cod (fst \<mu>\<nu>) \<^bold>\<star> Cod (snd \<mu>\<nu>)) :
                     \<lbrace>Cod (fst \<mu>\<nu>) \<^bold>\<star> Cod (snd \<mu>\<nu>)\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod (fst \<mu>\<nu>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd \<mu>\<nu>)\<rbrace>\<guillemotright>"
            using 4 5 6 by auto
          have "\<Psi>\<^sub>o (VV.cod \<mu>\<nu>) \<cdot>\<^sub>B HoDN_DN.map \<mu>\<nu> =
                B.can (Cod (fst \<mu>\<nu>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd \<mu>\<nu>)) (Cod (fst \<mu>\<nu>) \<^bold>\<star> Cod (snd \<mu>\<nu>)) \<cdot>\<^sub>B
                  (Map (fst \<mu>\<nu>) \<star>\<^sub>B Map (snd \<mu>\<nu>))"
            using \<mu>\<nu> VV.arr_char VV.cod_char arr_char src_def trg_def cod_char DN.FF_def DN_def
            by auto
          also have "... = B.can (Cod (fst \<mu>\<nu>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd \<mu>\<nu>))
                                 (Cod (fst \<mu>\<nu>) \<^bold>\<star> Cod (snd \<mu>\<nu>)) \<cdot>\<^sub>B
                             (Map (fst \<mu>\<nu>) \<star>\<^sub>B Map (snd \<mu>\<nu>)) \<cdot>\<^sub>B \<Psi>\<^sub>o' \<mu>\<nu> \<cdot>\<^sub>B \<Psi>\<^sub>o \<mu>\<nu>"
            using B B.comp_assoc \<mu>\<nu> VV.arr_char arr_char src_def trg_def B.inverse_arrows_can
                  E.Ide_HcompNml E.Nmlize_Nml E.Nml_HcompNml(1) B.can_Ide_self B.comp_arr_dom
            by auto
          also have "... = DNoH.map \<mu>\<nu> \<cdot>\<^sub>B \<Psi>\<^sub>o (VV.dom \<mu>\<nu>)"
          proof -
            have "DNoH.map \<mu>\<nu> \<cdot>\<^sub>B \<Psi>\<^sub>o (VV.dom \<mu>\<nu>) =
                  B.can (Cod (fst \<mu>\<nu>) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod (snd \<mu>\<nu>)) (Cod (fst \<mu>\<nu>) \<^bold>\<star> Cod (snd \<mu>\<nu>)) \<cdot>\<^sub>B
                    (Map (fst \<mu>\<nu>) \<star>\<^sub>B Map (snd \<mu>\<nu>)) \<cdot>\<^sub>B \<Psi>\<^sub>o' \<mu>\<nu> \<cdot>\<^sub>B \<Psi>\<^sub>o (VV.dom \<mu>\<nu>)"
              using \<mu>\<nu> DN_def VV.arr_char B.comp_assoc by simp
            moreover have "\<Psi>\<^sub>o (VV.dom \<mu>\<nu>) = \<Psi>\<^sub>o \<mu>\<nu>"
              using \<mu>\<nu> VV.dom_char VV.arr_char by auto
            ultimately show ?thesis
              using B.comp_assoc by simp
          qed
          finally show ?thesis by blast
        qed
      qed
    qed

    abbreviation \<Psi>
    where "\<Psi> \<equiv> \<Psi>.map"

    interpretation \<Psi>: natural_isomorphism VV.comp V\<^sub>B HoDN_DN.map DNoH.map \<Psi>
    proof
      show "\<And>fg. VV.ide fg \<Longrightarrow> B.iso (\<Psi> fg)"
      proof -
        fix fg
        assume fg: "VV.ide fg"
        have "B.inverse_arrows (\<Psi>\<^sub>o fg) (\<Psi>\<^sub>o' fg)"
          using fg \<Psi>\<^sub>o_in_hom by simp
        thus "B.iso (\<Psi> fg)"
          using fg B.iso_def \<Psi>.map_simp_ide by auto
      qed
    qed

    no_notation B.in_hom  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")

    lemma \<Psi>_in_hom [intro]:
    assumes "arr (fst \<mu>\<nu>)" and "arr (snd \<mu>\<nu>)" and "src (fst \<mu>\<nu>) = trg (snd \<mu>\<nu>)"
    shows "\<guillemotleft>\<Psi> \<mu>\<nu> : DN (src (snd \<mu>\<nu>)) \<rightarrow>\<^sub>B DN (trg (fst \<mu>\<nu>))\<guillemotright>"
    and "\<guillemotleft>\<Psi> \<mu>\<nu> : DN (dom (fst \<mu>\<nu>)) \<star>\<^sub>B DN (dom (snd \<mu>\<nu>))
                    \<Rightarrow>\<^sub>B DN (cod (fst \<mu>\<nu>) \<star> cod (snd \<mu>\<nu>))\<guillemotright>"
    proof -
      have 1: "VV.arr \<mu>\<nu>"
        using assms VV.arr_char by simp
      show 2: "\<guillemotleft>\<Psi> \<mu>\<nu> : DN (dom (fst \<mu>\<nu>)) \<star>\<^sub>B DN (dom (snd \<mu>\<nu>))
                          \<Rightarrow>\<^sub>B DN (cod (fst \<mu>\<nu>) \<star> cod (snd \<mu>\<nu>))\<guillemotright>"
      proof -
        have "HoDN_DN.map (VV.dom \<mu>\<nu>) = DN (dom (fst \<mu>\<nu>)) \<star>\<^sub>B DN (dom (snd \<mu>\<nu>))"
          using assms 1 DN.FF_def by auto
        moreover have "DNoH.map (VV.cod \<mu>\<nu>) = DN (cod (fst \<mu>\<nu>) \<star> cod (snd \<mu>\<nu>))"
          using assms 1 by simp
        ultimately show ?thesis
          using assms 1 \<Psi>.preserves_hom by auto
      qed
      show "\<guillemotleft>\<Psi> \<mu>\<nu> : DN (src (snd \<mu>\<nu>)) \<rightarrow>\<^sub>B DN (trg (fst \<mu>\<nu>))\<guillemotright>"
        using assms 1 2 B.src_dom [of "\<Psi> \<mu>\<nu>"] B.trg_dom [of "\<Psi> \<mu>\<nu>"] by auto
    qed

    lemma \<Psi>_simps [simp]:
    assumes "arr (fst \<mu>\<nu>)" and "arr (snd \<mu>\<nu>)" and "src (fst \<mu>\<nu>) = trg (snd \<mu>\<nu>)"
    shows "B.arr (\<Psi> \<mu>\<nu>)"
    and "src\<^sub>B (\<Psi> \<mu>\<nu>) = DN (src (snd \<mu>\<nu>))" and "trg\<^sub>B (\<Psi> \<mu>\<nu>) = DN (trg (fst \<mu>\<nu>))"
    and "B.dom (\<Psi> \<mu>\<nu>) = DN (dom (fst \<mu>\<nu>)) \<star>\<^sub>B DN (dom (snd \<mu>\<nu>))"
    and "B.cod (\<Psi> \<mu>\<nu>) = DN (cod (fst \<mu>\<nu>) \<star> cod (snd \<mu>\<nu>))"
    proof
      show "VV.arr \<mu>\<nu>"
        using assms by blast
      have 1: "\<guillemotleft>\<Psi> \<mu>\<nu> : DN (src (snd \<mu>\<nu>)) \<rightarrow>\<^sub>B DN (trg (fst \<mu>\<nu>))\<guillemotright>"
        using assms by blast
      show "src\<^sub>B (\<Psi> \<mu>\<nu>) = DN (src (snd \<mu>\<nu>))"
        using 1 by fast
      show "trg\<^sub>B (\<Psi> \<mu>\<nu>) = DN (trg (fst \<mu>\<nu>))"
        using 1 by fast
      have 2: "\<guillemotleft>\<Psi> \<mu>\<nu> : DN (dom (fst \<mu>\<nu>)) \<star>\<^sub>B DN (dom (snd \<mu>\<nu>))
                          \<Rightarrow>\<^sub>B DN (cod (fst \<mu>\<nu>) \<star> cod (snd \<mu>\<nu>))\<guillemotright>"
        using assms by blast
      show "B.dom (\<Psi> \<mu>\<nu>) = DN (dom (fst \<mu>\<nu>)) \<star>\<^sub>B DN (dom (snd \<mu>\<nu>))"
        using 2 by fast
      show "B.cod (\<Psi> \<mu>\<nu>) = DN (cod (fst \<mu>\<nu>) \<star> cod (snd \<mu>\<nu>))"
        using 2 by fast
    qed

    interpretation DN: pseudofunctor vcomp hcomp \<a> \<i> src trg V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B DN \<Psi>
    proof
      show "\<And>f g h. \<lbrakk> ide f; ide g; ide h; src f = trg g; src g = trg h \<rbrakk> \<Longrightarrow>
                       DN (\<a> f g h) \<cdot>\<^sub>B \<Psi> (f \<star> g, h) \<cdot>\<^sub>B (\<Psi> (f, g) \<star>\<^sub>B DN h) =
                       \<Psi> (f, g \<star> h) \<cdot>\<^sub>B (DN f \<star>\<^sub>B \<Psi> (g, h)) \<cdot>\<^sub>B \<a>\<^sub>B[DN f, DN g, DN h]"
      proof -
        fix f g h
        assume f: "ide f" and g: "ide g" and h: "ide h"
        and fg: "src f = trg g" and gh: "src g = trg h"
        show "DN (\<a> f g h) \<cdot>\<^sub>B \<Psi> (f \<star> g, h) \<cdot>\<^sub>B (\<Psi> (f, g) \<star>\<^sub>B DN h) =
              \<Psi> (f, g \<star> h) \<cdot>\<^sub>B (DN f \<star>\<^sub>B \<Psi> (g, h)) \<cdot>\<^sub>B \<a>\<^sub>B[DN f, DN g, DN h]"
        proof -
          have 1: "E.Trg (Dom g) = E.Trg (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<and>
                   \<lbrace>E.Trg (Dom g)\<rbrace> = \<lbrace>E.Trg (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)\<rbrace>"
            using f g h fg gh arr_char src_def trg_def E.Trg_HcompNml
            by (metis (no_types, lifting) ideD(1) src_simps(2) trg_simps(2))
          have 2: "arr (MkArr (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h)
                       (B.can (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) (Cod f \<^bold>\<star> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) \<cdot>\<^sub>B
                          (Map f \<star>\<^sub>B B.can (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) (Cod g \<^bold>\<star> Cod h) \<cdot>\<^sub>B
                          (Map g \<star>\<^sub>B Map h) \<cdot>\<^sub>B B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)) \<cdot>\<^sub>B
                          B.can (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)))"
          proof -
            have "\<guillemotleft>B.can (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) (Cod f \<^bold>\<star> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) \<cdot>\<^sub>B
                     (Map f \<star>\<^sub>B
                        B.can (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) (Cod g \<^bold>\<star> Cod h) \<cdot>\<^sub>B
                          (Map g \<star>\<^sub>B Map h) \<cdot>\<^sub>B B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)) \<cdot>\<^sub>B
                          B.can (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) :
                     EVAL (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<Rightarrow>\<^sub>B EVAL (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h)\<guillemotright>"
            proof (intro B.comp_in_homI)
              show 2: "\<guillemotleft>B.can (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) :
                          EVAL (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<Rightarrow>\<^sub>B
                            EVAL (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)\<guillemotright>"
                using f g h fg gh 1
                apply (intro B.can_in_hom)
                  apply (metis (no_types, lifting) E.Ide_HcompNml E.Nml_HcompNml(1)
                    arr_char ideD(1) src_simps(1) trg_simps(1))
                 apply (metis (no_types, lifting) E.Ide.simps(3) E.Ide_HcompNml ideD(1)
                    arr_char src_simps(1) trg_simps(1))
                by (metis (no_types, lifting) E.Nml_HcompNml(1) E.Nmlize.simps(3)
                    E.Nmlize_Nml ideD(1) arr_char src_simps(1) trg_simps(1))
              show "\<guillemotleft>B.can (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) (Cod f \<^bold>\<star> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) :
                       EVAL (Cod f \<^bold>\<star> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) \<Rightarrow>\<^sub>B
                         EVAL (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h)\<guillemotright>"
              proof -
                have "E.Ide (Cod f \<^bold>\<star> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h)"
                  using f g h fg gh 1 Cod_ide E.Ide_HcompNml arr_char
                  apply simp
                  by (metis (no_types, lifting) ideD(1) src_simps(1) trg_simps(1))
                moreover have "E.Ide (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h)"
                  using f g h fg gh
                  by (metis (no_types, lifting) E.Ide.simps(3) E.Ide_HcompNml E.Nml_HcompNml(1)
                      arr_char calculation ideD(1) src_simps(1) trg_simps(1))
                moreover have "E.Nmlize (Cod f \<^bold>\<star> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) =
                               E.Nmlize (Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h)"
                  using f g h fg gh
                  by (metis (no_types, lifting) E.Ide.simps(3) E.Nml_HcompNml(1) E.Nmlize.simps(3)
                      E.Nmlize_Nml arr_char calculation(1) ideD(1) src_simps(1) trg_simps(1))
                ultimately show ?thesis
                  using B.can_in_hom [of "Cod f \<^bold>\<star> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h" "Cod f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h"]
                  by blast
              qed
              show
                "\<guillemotleft>Map f \<star>\<^sub>B B.can (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) (Cod g \<^bold>\<star> Cod h) \<cdot>\<^sub>B (Map g \<star>\<^sub>B Map h) \<cdot>\<^sub>B
                  B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) :
                    EVAL (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<Rightarrow>\<^sub>B EVAL (Cod f \<^bold>\<star> Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h)\<guillemotright>"
                using f g h fg gh B.can_in_hom
                apply simp
              proof (intro B.hcomp_in_vhom B.comp_in_homI)
                show 1: "\<guillemotleft>B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) :
                            EVAL (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<Rightarrow>\<^sub>B EVAL (Dom g \<^bold>\<star> Dom h)\<guillemotright>"
                  using g h gh B.can_in_hom
                  by (metis (no_types, lifting) E.Ide.simps(3) E.Ide_HcompNml E.Nml_HcompNml(1)
                      E.Nmlize.simps(3) E.Nmlize_Nml arr_char ideD(1) src_simps(1) trg_simps(1))
                show "\<guillemotleft>B.can (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) (Cod g \<^bold>\<star> Cod h) :
                         EVAL (Cod g \<^bold>\<star> Cod h) \<Rightarrow>\<^sub>B EVAL (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h)\<guillemotright>"
                  using g h gh B.can_in_hom
                  by (metis (no_types, lifting) Cod_ide E.Ide.simps(3) E.Ide_HcompNml
                      E.Nml_HcompNml(1) E.Nmlize.simps(3) E.Nmlize_Nml arr_char ideD(1)
                      src_simps(2) trg_simps(2))
                show "\<guillemotleft>Map g \<star>\<^sub>B Map h : EVAL (Dom g \<^bold>\<star> Dom h) \<Rightarrow>\<^sub>B EVAL (Cod g \<^bold>\<star> Cod h)\<guillemotright>"
                  using g h gh 1 Map_in_Hom B.hcomp_in_vhom B.not_arr_null B.seq_if_composable
                        B.trg.is_extensional B.trg.preserves_hom B.vconn_implies_hpar(2)
                        B.vconn_implies_hpar(4) Cod_ide E.eval.simps(3) Map_ide(1)
                        arr_char ideD(1)
                  by (metis (no_types, lifting))
                show "\<guillemotleft>Map f : Map f \<Rightarrow>\<^sub>B EVAL (Cod f)\<guillemotright>"
                  using f arr_char Cod_ide by auto
                show "src\<^sub>B (Map f) = trg\<^sub>B \<lbrace>Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace>"
                  using f g h fg gh 1 2 src_def trg_def B.arrI B.hseqE B.not_arr_null
                        B.trg.is_extensional B.trg.preserves_hom B.vconn_implies_hpar(2)
                        B.vconn_implies_hpar(4) E.eval.simps(3)
                  by (metis (no_types, lifting) Map_ide(1))
              qed
            qed
            thus ?thesis
              using f g h fg gh arr_char src_def trg_def E.Nml_HcompNml E.Ide_HcompNml
                    ideD(1)
              apply (intro arr_MkArr) by auto
          qed
          have 3: "E.Ide (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
            using g h gh ide_char arr_char src_def trg_def E.Ide_HcompNml Cod_ide
            by (metis (no_types, lifting) ideD(1) src_simps(2) trg_simps(2))
          have 4: "E.Ide (Dom g \<^bold>\<star> Dom h)"
            using g h gh ide_char arr_char src_def trg_def Cod_ide
            by (metis (no_types, lifting) E.Ide.simps(3) arrE ideD(1) src_simps(2) trg_simps(2))
          have 5: "E.Nmlize (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) = E.Nmlize (Dom g \<^bold>\<star> Dom h)"
            using g h gh ide_char arr_char src_def trg_def E.Nml_HcompNml
            by (metis (no_types, lifting) 4 E.Ide.simps(3) E.Nmlize.simps(3) E.Nmlize_Nml
                ideD(1))
          have 6: "E.Ide (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
            using f g h fg gh arr_char src_def trg_def
            by (metis (no_types, lifting) 1 E.Nml_HcompNml(1) E.Ide_HcompNml ideD(1)
                src_simps(2) trg_simps(2))
          have 7: "E.Ide (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
            using f g h fg gh arr_char src_def trg_def
            by (metis (no_types, lifting) 1 3 E.Ide.simps(3) ideD(1) src_simps(2) trg_simps(2))
          have 8: "E.Nmlize (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) =
                   E.Nmlize (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
            using f g h fg gh arr_char src_def trg_def
                  7 E.Nml_HcompNml(1) ideD(1)
            by auto
          have "DN (\<a> f g h) \<cdot>\<^sub>B \<Psi> (f \<star> g, h) \<cdot>\<^sub>B (\<Psi> (f, g) \<star>\<^sub>B DN h) =
                B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) ((Dom f \<^bold>\<star> Dom g) \<^bold>\<star> Dom h)"
          proof -
            have 9: "VVV.arr (f, g, h)"
              using f g h fg gh VVV.arr_char VV.arr_char arr_char ideD by simp
            have 10: "VV.ide (f, g)"
              using f g fg VV.ide_char by auto
            have 11: "VV.ide (hcomp f g, h)"
              using f g h fg gh VV.ide_char VV.arr_char by simp
            have 12: "arr (MkArr (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h)
                                (B.can (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) (Cod g \<^bold>\<star> Cod h) \<cdot>\<^sub>B
                                  (Map g \<star>\<^sub>B Map h) \<cdot>\<^sub>B
                                  B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)))"
            proof (intro arr_MkArr)
              show "Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h \<in> IDE"
                using g h gh
                by (metis (no_types, lifting) 3 E.Nml_HcompNml(1) arr_char ideD(1)
                    mem_Collect_eq src_simps(2) trg_simps(2))
              show "Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h \<in> IDE"
                using g h gh Cod_ide \<open>Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h \<in> IDE\<close> by auto
              show "B.can (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) (Cod g \<^bold>\<star> Cod h) \<cdot>\<^sub>B
                      (Map g \<star>\<^sub>B Map h) \<cdot>\<^sub>B
                      B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)
                    \<in> HOM (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h)"
              proof
                show "E.Src (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) = E.Src (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) \<and>
                      E.Trg (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) = E.Trg (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) \<and>
                      \<guillemotleft>B.can (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) (Cod g \<^bold>\<star> Cod h) \<cdot>\<^sub>B
                         (Map g \<star>\<^sub>B Map h) \<cdot>\<^sub>B B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) :
                         \<lbrace>Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h\<rbrace>\<guillemotright>"
                proof (intro conjI)
                  show "E.Src (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) = E.Src (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h)"
                    using g h gh Cod_ide by simp
                  show "E.Trg (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) = E.Trg (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h)"
                    using g h gh Cod_ide by simp
                  show "\<guillemotleft>B.can (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) (Cod g \<^bold>\<star> Cod h) \<cdot>\<^sub>B
                           (Map g \<star>\<^sub>B Map h) \<cdot>\<^sub>B B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) :
                           \<lbrace>Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h\<rbrace>\<guillemotright>"
                  proof (intro B.comp_in_homI)
                    show "\<guillemotleft>B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) :
                             \<lbrace>Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Dom g \<^bold>\<star> Dom h\<rbrace>\<guillemotright>"
                      using 3 4 5 by blast
                    show "\<guillemotleft>Map g \<star>\<^sub>B Map h : \<lbrace>Dom g \<^bold>\<star> Dom h\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod g \<^bold>\<star> Cod h\<rbrace>\<guillemotright>"
                      using g h gh
                      by (metis (no_types, lifting) 4 B.ide_in_hom(2) Cod_ide E.eval.simps(3)
                          E.ide_eval_Ide Map_ide(2))
                    show "\<guillemotleft>B.can (Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h) (Cod g \<^bold>\<star> Cod h) :
                            \<lbrace>Cod g \<^bold>\<star> Cod h\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Cod h\<rbrace>\<guillemotright>"
                      using 3 4 5 Cod_ide g h by auto
                  qed
                qed
              qed
            qed
            have "DN (\<a> f g h) = \<lbrace>Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace>"
            proof -
              have "DN (\<a> f g h) =
                    (B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<cdot>\<^sub>B
                      ((Map f \<star>\<^sub>B B.can (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom g \<^bold>\<star> Dom h) \<cdot>\<^sub>B
                         (Map g \<star>\<^sub>B Map h) \<cdot>\<^sub>B B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h))) \<cdot>\<^sub>B
                      B.can (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h))"
                using f g h fg gh 1 2 9 10 11 12 DN_def \<a>_def hcomp_def src_def trg_def
                      B.comp_assoc Cod_ide
                by simp
              also have
                "... = B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<cdot>\<^sub>B
                         (Map f \<star>\<^sub>B \<lbrace>Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace>) \<cdot>\<^sub>B
                           B.can (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
              proof -
                have "\<guillemotleft>B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) :
                                    \<lbrace>Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace> \<Rightarrow>\<^sub>B Map g \<star>\<^sub>B Map h\<guillemotright>"
                  using g h 3 4 5 B.can_in_hom [of "Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h" "Dom g \<^bold>\<star> Dom h"]
                  by simp
                hence "Map f \<star>\<^sub>B B.can (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom g \<^bold>\<star> Dom h) \<cdot>\<^sub>B
                                 (Map g \<star>\<^sub>B Map h) \<cdot>\<^sub>B B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) =
                       Map f \<star>\<^sub>B B.can (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom g \<^bold>\<star> Dom h) \<cdot>\<^sub>B
                                 B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
                  using B.comp_cod_arr by auto
                also have "... = Map f \<star>\<^sub>B \<lbrace>Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace>"
                  using f g h fg gh arr_char src_def trg_def B.vcomp_can
                        B.can_Ide_self
                  using 3 4 5 by auto
                finally have "Map f \<star>\<^sub>B B.can (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom g \<^bold>\<star> Dom h) \<cdot>\<^sub>B
                                 (Map g \<star>\<^sub>B Map h) \<cdot>\<^sub>B B.can (Dom g \<^bold>\<star> Dom h) (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) =
                              Map f \<star>\<^sub>B \<lbrace>Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace>"
                  by simp
                thus ?thesis by simp
              qed
              also have
                "... = B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<cdot>\<^sub>B
                         B.can (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
              proof -
                have "\<guillemotleft>B.can (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) :
                               \<lbrace>Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace> \<Rightarrow>\<^sub>B Map f \<star>\<^sub>B \<lbrace>Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace>\<guillemotright>"
                  using f g h 6 7 8
                        B.can_in_hom [of "Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h" "Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h"]
                  by simp
                hence "(Map f \<star>\<^sub>B \<lbrace>Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace>) \<cdot>\<^sub>B
                         B.can (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) =
                       B.can (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
                  using B.comp_cod_arr by auto
                thus ?thesis by simp
              qed
              also have
                "... = B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
                using f g h fg gh src_def trg_def B.vcomp_can
                using 6 7 8 by auto
              also have "... = \<lbrace>Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace>"
                using f g h fg gh src_def trg_def B.can_Ide_self
                using 6 by blast
              finally show ?thesis by simp
            qed
            have "DN (\<a> f g h) \<cdot>\<^sub>B \<Psi> (f \<star> g, h) \<cdot>\<^sub>B (\<Psi> (f, g) \<star>\<^sub>B DN h) =
                  B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<cdot>\<^sub>B
                  B.can ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<star> Dom h) \<cdot>\<^sub>B
                    (B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) (Dom f \<^bold>\<star> Dom g) \<star>\<^sub>B Map h)"
            proof -
              have "DN (\<a> f g h) =
                    B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
                using f g h fg gh DN_def 1 4 6 7 B.can_Ide_self E.HcompNml_assoc
                      E.Ide.simps(3) \<open>DN (\<a> f g h) = \<lbrace>Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h\<rbrace>\<close> ide_char
                by (metis (no_types, lifting) arr_char ideD(1))
              thus ?thesis
                using f g h fg gh 1 2 4 5 6 7 8 9 10 11 12 DN_def \<alpha>_def
                      \<Psi>.map_simp_ide hcomp_def src_def trg_def Cod_ide
                by simp
            qed
            also have
              "... = (B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<cdot>\<^sub>B
                       B.can ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<star> Dom h)) \<cdot>\<^sub>B
                        (B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) (Dom f \<^bold>\<star> Dom g) \<star>\<^sub>B Map h)"
              using B.comp_assoc by simp
            also have
              "... = B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<star> Dom h) \<cdot>\<^sub>B
                       B.can ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<star> Dom h) ((Dom f \<^bold>\<star> Dom g) \<^bold>\<star> Dom h)"
            proof -
              have "B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) (Dom f \<^bold>\<star> Dom g) \<star>\<^sub>B Map h =
                    B.can ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<star> Dom h) ((Dom f \<^bold>\<star> Dom g) \<^bold>\<star> Dom h)"
              proof -
                have "B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) (Dom f \<^bold>\<star> Dom g) \<star>\<^sub>B Map h =
                      B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) (Dom f \<^bold>\<star> Dom g) \<star>\<^sub>B B.can (Dom h) (Dom h)"
                  using h B.can_Ide_self by fastforce
                also have "... = B.can ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<star> Dom h) ((Dom f \<^bold>\<star> Dom g) \<^bold>\<star> Dom h)"
                  using f g h 1 4 7 arr_char E.Nml_HcompNml(1) E.Src_HcompNml
                        B.hcomp_can [of "Dom f \<^bold>\<star> Dom g" "Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g" "Dom h" "Dom h"]
                  by (metis (no_types, lifting) E.Nmlize.simps(3) E.Nmlize_Nml
                      E.Ide.simps(3) E.Ide_HcompNml E.Src.simps(3) arrE ideD(1))
                finally show ?thesis by simp
              qed
              moreover have
                "B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<cdot>\<^sub>B
                   B.can ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<star> Dom h) =
                     B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<star> Dom h)"
              proof -
                have "E.Ide ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<star> Dom h)"
                  using f g h 1 4 7
                  by (metis (no_types, lifting) E.Ide.simps(3) E.Ide_HcompNml E.Src_HcompNml
                      arrE ideD(1))
                moreover have "E.Ide ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
                  using f g h 1 4 7 E.Ide_HcompNml E.Nml_HcompNml(1) arr_char calculation
                        ideD(1)
                  by auto
                moreover have "E.Ide (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
                  using f g h 1 4 6 by blast
                moreover have "E.Nmlize ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<star> Dom h) =
                               E.Nmlize ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
                  using f g h 1 4 7
                  by (metis (no_types, lifting) E.Nml_HcompNml(1) E.Nmlize.simps(3)
                      E.Nmlize_Nml E.Ide.simps(3) arrE calculation(1) ideD(1))
                moreover have "E.Nmlize ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) =
                               E.Nmlize (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
                  using f g h 1 4 7 E.HcompNml_assoc by fastforce
                ultimately show ?thesis
                  using B.vcomp_can by simp
              qed
              ultimately show ?thesis by simp
            qed
            also have "... = B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) ((Dom f \<^bold>\<star> Dom g) \<^bold>\<star> Dom h)"
            proof -
              have "E.Ide ((Dom f \<^bold>\<star> Dom g) \<^bold>\<star> Dom h)"
                using 1 4 7 by simp
              moreover have "E.Ide ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<star> Dom h)"
                using f g 1 4 7
                by (metis (no_types, lifting) E.Ide.simps(3) E.Ide_HcompNml E.Src_HcompNml
                    arrE ideD(1))
              moreover have "E.Ide (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
                using f g h 1 8 6 7 by blast
              moreover have "E.Nmlize ((Dom f \<^bold>\<star> Dom g) \<^bold>\<star> Dom h) =
                             E.Nmlize ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<star> Dom h)"
                using f g h 1 4 7 E.Nml_HcompNml(1) by fastforce
              moreover have "E.Nmlize ((Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g) \<^bold>\<star> Dom h) =
                             E.Nmlize (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h)"
                using f g h 1 4 7
                by (metis (no_types, lifting) E.Nml_HcompNml(1) E.Nmlize.simps(3)
                    E.Nmlize_Nml E.HcompNml_assoc E.Ide.simps(3) arrE ideD(1))
              ultimately show ?thesis
                using B.vcomp_can by simp
            qed
            finally show ?thesis by simp
          qed
          also have "... = \<Psi> (f, g \<star> h) \<cdot>\<^sub>B (DN f \<star>\<^sub>B \<Psi> (g, h)) \<cdot>\<^sub>B \<a>\<^sub>B[DN f, DN g, DN h]"
          proof -
            have "\<Psi> (f, g \<star> h) \<cdot>\<^sub>B (DN f \<star>\<^sub>B \<Psi> (g, h)) \<cdot>\<^sub>B \<a>\<^sub>B[DN f, DN g, DN h] =
                  (\<Psi> (f, g \<star> h) \<cdot>\<^sub>B (DN f \<star>\<^sub>B \<Psi> (g, h))) \<cdot>\<^sub>B \<a>\<^sub>B[DN f, DN g, DN h]"
              using B.comp_assoc by simp
            also have
              "... = B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<star> Dom g \<^bold>\<star> Dom h) \<cdot>\<^sub>B
                       B.can (Dom f \<^bold>\<star> Dom g \<^bold>\<star> Dom h) ((Dom f \<^bold>\<star> Dom g) \<^bold>\<star> Dom h)"
            proof -
              have "\<Psi> (f, g \<star> h) \<cdot>\<^sub>B (DN f \<star>\<^sub>B \<Psi> (g, h)) =
                    B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<star> Dom g \<^bold>\<star> Dom h)"
              proof -
                have "\<Psi> (f, g \<star> h) \<cdot>\<^sub>B (DN f \<star>\<^sub>B \<Psi> (g, h)) =
                      B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<cdot>\<^sub>B
                            (Map f \<star>\<^sub>B B.can (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom g \<^bold>\<star> Dom h))"
               proof -
                  have "VV.ide (g, h)"
                    using g h gh VV.ide_char VV.arr_char by simp
                  moreover have "VV.ide (f, hcomp g h)"
                    using f g h fg gh VV.ide_char VV.arr_char by simp
                  ultimately show ?thesis
                    using f g h fg gh \<Psi>.map_simp_ide DN_def hcomp_def src_def trg_def
                    by simp
                qed
                also have
                  "... = B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<cdot>\<^sub>B
                           (B.can (Dom f) (Dom f) \<star>\<^sub>B B.can (Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom g \<^bold>\<star> Dom h))"
                proof -
                  have "Map f = B.can (Dom f) (Dom f)"
                    using f arr_char B.can_Ide_self [of "Dom f"] Map_ide
                    by (metis (no_types, lifting) ide_char')
                  thus ?thesis by simp
                qed
                also have
                  "... = B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) \<cdot>\<^sub>B
                         B.can (Dom f \<^bold>\<star> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<star> Dom g \<^bold>\<star> Dom h)"
                  using 1 4 5 7 B.hcomp_can by auto
                also have "... = B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) (Dom f \<^bold>\<star> Dom g \<^bold>\<star> Dom h)"
                  using 1 4 5 6 7 8 B.vcomp_can by auto
                finally show ?thesis by simp
              qed
              moreover have "\<a>\<^sub>B[DN f, DN g, DN h] =
                             B.can (Dom f \<^bold>\<star> Dom g \<^bold>\<star> Dom h) ((Dom f \<^bold>\<star> Dom g) \<^bold>\<star> Dom h)"
                using f g h 1 4 7 DN_def B.canE_associator(1) Map_ide
                by auto
              ultimately show ?thesis by simp
            qed
            also have  "... = B.can (Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h) ((Dom f \<^bold>\<star> Dom g) \<^bold>\<star> Dom h)"
              using 1 4 5 6 7 8 E.Nmlize_Hcomp_Hcomp
                    B.vcomp_can [of "(Dom f \<^bold>\<star> Dom g) \<^bold>\<star> Dom h" "Dom f \<^bold>\<star> Dom g \<^bold>\<star> Dom h"
                                    "Dom f \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom g \<^bold>\<lfloor>\<^bold>\<star>\<^bold>\<rfloor> Dom h"]
              by simp
            finally show ?thesis by simp
          qed
          finally show ?thesis by blast
        qed
      qed
    qed

    lemma DN_is_pseudofunctor:
    shows "pseudofunctor vcomp hcomp \<a> \<i> src trg V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B DN \<Psi>"
      ..

    interpretation faithful_functor vcomp V\<^sub>B DN
    proof
      fix \<mu> \<mu>'
      assume par: "par \<mu> \<mu>'" and eq: "DN \<mu> = DN \<mu>'"
      show "\<mu> = \<mu>'"
      proof (intro arr_eqI)
        show "arr \<mu>"
          using par by simp
        show "arr \<mu>'"
          using par by simp
        show "Dom \<mu> = Dom \<mu>'"
          using par arr_char dom_char by force
        show "Cod \<mu> = Cod \<mu>'"
          using par arr_char cod_char by force
        show "Map \<mu> = Map \<mu>'"
          using par eq DN_def by simp
      qed
    qed

    no_notation B.in_hom  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")

    lemma DN_UP:
    assumes "B.arr \<mu>"
    shows "DN (UP \<mu>) = \<mu>"
      using assms UP_def DN_def arr_UP by auto

    interpretation DN: equivalence_pseudofunctor
                         vcomp hcomp \<a> \<i> src trg V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B DN \<Psi>
    proof
      (* DN is locally (but not globally) full. *)
      show "\<And>f f' \<nu>. \<lbrakk> ide f; ide f'; src f = src f'; trg f = trg f'; \<guillemotleft>\<nu> : DN f \<Rightarrow>\<^sub>B DN f'\<guillemotright> \<rbrakk>
                         \<Longrightarrow> \<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow> f'\<guillemotright> \<and> DN \<mu> = \<nu>"
      proof -
        fix f f' \<nu>
        assume f: "ide f" and f': "ide f'"
        and eq_src: "src f = src f'" and eq_trg: "trg f = trg f'"
        and \<nu>: "\<guillemotleft>\<nu> : DN f \<Rightarrow>\<^sub>B DN f'\<guillemotright>"
        show "\<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow> f'\<guillemotright> \<and> DN \<mu> = \<nu>"
        proof -
          let ?\<mu> = "MkArr (Dom f) (Dom f') \<nu>"
          have \<mu>: "\<guillemotleft>?\<mu> : f \<Rightarrow> f'\<guillemotright>"
          proof
            have "Map f = \<lbrace>Dom f\<rbrace>"
              using f by simp
            have "Map f' = \<lbrace>Dom f'\<rbrace>"
              using f' by simp
            have "Dom f' = Cod f'"
              using f' Cod_ide by simp
            show \<mu>: "arr ?\<mu>"
            proof -
              have "E.Nml (Dom ?\<mu>) \<and> E.Ide (Dom ?\<mu>)"
              proof -
                have "E.Nml (Dom f) \<and> E.Ide (Dom f)"
                  using f ide_char arr_char by blast
                thus ?thesis
                  using f by simp
              qed
              moreover have "E.Nml (Cod ?\<mu>) \<and> E.Ide (Cod ?\<mu>)"
              proof -
                have "E.Nml (Dom f') \<and> E.Ide (Dom f')"
                  using f' ide_char arr_char by blast
                thus ?thesis
                  using f' by simp
              qed
              moreover have "E.Src (Dom ?\<mu>) = E.Src (Cod ?\<mu>)"
                using f f' \<nu> arr_char src_def eq_src ideD(1) by auto
              moreover have "E.Trg (Dom ?\<mu>) = E.Trg (Cod ?\<mu>)"
                using f f' \<nu> arr_char trg_def eq_trg ideD(1) by auto
              moreover have "\<guillemotleft>Map ?\<mu> : \<lbrace>Dom ?\<mu>\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Cod ?\<mu>\<rbrace>\<guillemotright>"
              proof -
                have "\<guillemotleft>\<nu> : \<lbrace>Dom f\<rbrace> \<Rightarrow>\<^sub>B \<lbrace>Dom f'\<rbrace>\<guillemotright>"
                  using f f' \<nu> ide_char arr_char DN_def Cod_ide Map_ide
                  by (metis (no_types, lifting) ideD(1))
                thus ?thesis by simp
              qed
              ultimately show ?thesis
                using f f' \<nu> ide_char arr_char by blast
            qed
            show "dom ?\<mu> = f"
              using f \<mu> dom_char MkArr_Map MkIde_Dom' by simp
            show "cod ?\<mu> = f'"
            proof -
              have "cod ?\<mu> = MkIde (Dom f')"
                using \<mu> cod_char by simp
              also have "... = MkArr (Dom f') (Cod f') (Map f')"
                using f' by auto
              also have "... = f'"
                using f' MkArr_Map by simp
              finally show ?thesis by simp
            qed
          qed
          moreover have "DN ?\<mu> = \<nu>"
            using \<mu> DN_def by auto
          ultimately show ?thesis by blast
        qed
      qed
      (* DN is essentially surjective up to equivalence on objects. *)
      show "\<And>a'. B.obj a' \<Longrightarrow> \<exists>a. obj a \<and> B.equivalent_objects (DN.map\<^sub>0 a) a'"
      proof -
        fix a'
        assume a': "B.obj a'"
        have "obj (UP.map\<^sub>0 a')"
          using a' UP.map\<^sub>0_simps(1) by simp
        moreover have "B.equivalent_objects (DN.map\<^sub>0 (UP.map\<^sub>0 a')) a'"
        proof -
          have "arr (MkArr \<^bold>\<langle>a'\<^bold>\<rangle> \<^bold>\<langle>a'\<^bold>\<rangle> a')"
            using a' UP_def [of a'] UP.preserves_reflects_arr [of a'] by auto
          moreover have "arr (MkArr \<^bold>\<langle>a'\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a'\<^bold>\<rangle>\<^sub>0 a')"
            using a' arr_char B.obj_def by auto
          ultimately have "DN.map\<^sub>0 (UP.map\<^sub>0 a') = a'"
            using a' UP.map\<^sub>0_def UP_def DN.map\<^sub>0_def DN_def src_def UP.map\<^sub>0_simps(1)
            by auto
          thus ?thesis
            using a' B.equivalent_objects_reflexive by simp
        qed
        ultimately show "\<exists>a. obj a \<and> B.equivalent_objects (DN.map\<^sub>0 a) a'"
          by blast
      qed
      (* DN is locally essentially surjective. *)
      show "\<And>a b g. \<lbrakk> obj a; obj b; \<guillemotleft>g : DN.map\<^sub>0 a \<rightarrow>\<^sub>B DN.map\<^sub>0 b\<guillemotright>; B.ide g \<rbrakk> \<Longrightarrow>
                       \<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> ide f \<and> B.isomorphic (DN f) g"
      proof -
        fix a b g
        assume a: "obj a" and b: "obj b"
        and g: "\<guillemotleft>g : DN.map\<^sub>0 a \<rightarrow>\<^sub>B DN.map\<^sub>0 b\<guillemotright>" and ide_g: "B.ide g"
        have "ide (UP g)"
          using ide_g UP.preserves_ide by simp
        moreover have "B.isomorphic (DN (UP g)) g"
          using ide_g DN_UP B.isomorphic_reflexive by simp
        moreover have "\<guillemotleft>UP g : a \<rightarrow> b\<guillemotright>"
        proof
          show "arr (UP g)"
            using g UP.preserves_reflects_arr by auto
          show "src (UP g) = a"
          proof -
            have "src (UP g) = MkArr \<^bold>\<langle>src\<^sub>B g\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>src\<^sub>B g\<^bold>\<rangle>\<^sub>0 (src\<^sub>B g)"
              using ide_g src_def UP_def UP.preserves_reflects_arr [of g] B.ideD(1) by simp
            also have "... = a"
            proof -
              have "src\<^sub>B g = src\<^sub>B (DN.map\<^sub>0 a)"
                using a g B.in_hhom_def by simp
              also have "... = Map a"
                using a Map_preserves_objects DN.map\<^sub>0_def DN_def B.src_src B.obj_simps
                by auto
              finally have "src\<^sub>B g = Map a" by simp
              hence "MkArr \<^bold>\<langle>src\<^sub>B g\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>src\<^sub>B g\<^bold>\<rangle>\<^sub>0 (src\<^sub>B g) = MkArr \<^bold>\<langle>Map a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>Map a\<^bold>\<rangle>\<^sub>0 (Map a)"
                by simp
              also have "... = a"
                using a obj_char apply (cases "Dom a", simp_all)
                by (metis (no_types, lifting) B.obj_def' a comp_ide_arr dom_char dom_eqI objE)
              finally show ?thesis by simp
            qed
            finally show ?thesis by simp
          qed
          show "trg (UP g) = b"
          proof -
            have "trg (UP g) = MkArr \<^bold>\<langle>trg\<^sub>B g\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>trg\<^sub>B g\<^bold>\<rangle>\<^sub>0 (trg\<^sub>B g)"
              using ide_g trg_def UP_def UP.preserves_reflects_arr [of g] B.ideD(1) by simp
            also have "... = b"
            proof -
              have "trg\<^sub>B g = trg\<^sub>B (DN.map\<^sub>0 b)"
                using b g B.in_hhom_def by simp
              also have "... = Map b"
                using b Map_preserves_objects DN.map\<^sub>0_def DN_def B.src_src B.obj_simps
                by auto
              finally have "trg\<^sub>B g = Map b" by simp
              hence "MkArr \<^bold>\<langle>trg\<^sub>B g\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>trg\<^sub>B g\<^bold>\<rangle>\<^sub>0 (trg\<^sub>B g) = MkArr \<^bold>\<langle>Map b\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>Map b\<^bold>\<rangle>\<^sub>0 (Map b)"
                by simp
              also have "... = b"
                using b obj_char apply (cases "Dom b", simp_all)
                by (metis (no_types, lifting) B.obj_def' b comp_ide_arr dom_char dom_eqI objE)
              finally show ?thesis by simp
            qed
            finally show ?thesis by simp
          qed
        qed
        ultimately show "\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> ide f \<and> B.isomorphic (DN f) g"
          by blast
      qed
    qed

    theorem DN_is_equivalence_pseudofunctor:
    shows "equivalence_pseudofunctor vcomp hcomp \<a> \<i> src trg V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B DN \<Psi>"
      ..

    text \<open>
      The following gives an explicit formula for a component of the unit isomorphism of
      the pseudofunctor \<open>UP\<close> from a bicategory to its strictification.
      It is not currently being used -- I originally proved it in order to establish something
      that I later proved in a more abstract setting -- but it might be useful at some point.
    \<close>

    interpretation L: bicategorical_language V\<^sub>B src\<^sub>B trg\<^sub>B ..
    interpretation E: evaluation_map V\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                        \<open>\<lambda>\<mu>. if B.arr \<mu> then \<mu> else B.null\<close>
      using B.src.is_extensional B.trg.is_extensional
      by (unfold_locales, auto)
    notation E.eval ("\<lbrace>_\<rbrace>")

    interpretation UP: equivalence_pseudofunctor
                         V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B vcomp hcomp \<a> \<i> src trg UP \<Phi>
      using UP_is_equivalence_pseudofunctor by auto

    lemma UP_\<Psi>_char:
    assumes "B.obj a"
    shows "UP.\<Psi> a = MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a"
    proof -
      have " MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a = UP.\<Psi> a"
      proof (intro UP.\<Psi>_eqI)
        show "B.obj a"
          using assms by simp
        have 0: "\<guillemotleft>a : a \<Rightarrow>\<^sub>B a\<guillemotright>"
          using assms by auto
        have 1: "arr (MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a)"
          apply (unfold arr_char, intro conjI)
          using assms by auto
        have 2: "arr (MkArr \<^bold>\<langle>a\<^bold>\<rangle> \<^bold>\<langle>a\<^bold>\<rangle> a)"
          apply (unfold arr_char, intro conjI)
          using assms by auto
        have 3: "arr (MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 a)"
          apply (unfold arr_char, intro conjI)
          using assms by auto
        show "\<guillemotleft>MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a : UP.map\<^sub>0 a \<Rightarrow> UP a\<guillemotright>"
        proof
          show "arr (MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a)" by fact
          show "dom (MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a) = UP.map\<^sub>0 a"
            using assms 1 2 dom_char UP.map\<^sub>0_def UP_def src_def by auto
          show "cod (MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a) = UP a"
            using assms 1 2 cod_char UP.map\<^sub>0_def UP_def src_def by auto
        qed
        show "iso (MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a)"
          using assms 1 iso_char by auto
        show "MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a \<cdot> \<i> (UP.map\<^sub>0 a) =
              (UP \<i>\<^sub>B[a] \<cdot> \<Phi> (a, a)) \<cdot> (MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a \<star> MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a)"
        proof -
          have "MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a \<cdot> \<i> (UP.map\<^sub>0 a) = MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a"
            unfolding \<i>_def UP.map\<^sub>0_def UP_def
            using assms 0 1 2 src_def by auto
          also have "... = (UP \<i>\<^sub>B[a] \<cdot> \<Phi> (a, a)) \<cdot> (MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a \<star> MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a)"
          proof -
            have "(UP \<i>\<^sub>B[a] \<cdot> \<Phi> (a, a)) \<cdot> (MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a \<star> MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a) =
                  (MkArr \<^bold>\<langle>a \<star>\<^sub>B a\<^bold>\<rangle> \<^bold>\<langle>a\<^bold>\<rangle> \<i>\<^sub>B[a] \<cdot> MkArr (\<^bold>\<langle>a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>) \<^bold>\<langle>a \<star>\<^sub>B a\<^bold>\<rangle> (a \<star>\<^sub>B a))
                     \<cdot> (MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a \<star> MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a)"
              using assms UP_def \<Phi>_ide_simp by auto
            also have "... = (MkArr \<^bold>\<langle>a \<star>\<^sub>B a\<^bold>\<rangle> \<^bold>\<langle>a\<^bold>\<rangle> \<i>\<^sub>B[a] \<cdot> MkArr (\<^bold>\<langle>a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>) \<^bold>\<langle>a \<star>\<^sub>B a\<^bold>\<rangle> (a \<star>\<^sub>B a))
                               \<cdot> MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 (\<^bold>\<langle>a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>) (B.runit' a)"
              using assms 0 1 2 3 hcomp_def B.comp_cod_arr src_def trg_def
                    B.can_Ide_self B.canE_unitor [of "\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0"] B.comp_cod_arr
              by auto
            also have "... = MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> ((\<i>\<^sub>B[a] \<cdot>\<^sub>B (a \<star>\<^sub>B a)) \<cdot>\<^sub>B B.runit' a)"
            proof -
              have "MkArr \<^bold>\<langle>a \<star>\<^sub>B a\<^bold>\<rangle> \<^bold>\<langle>a\<^bold>\<rangle> \<i>\<^sub>B[a] \<cdot> MkArr (\<^bold>\<langle>a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>) \<^bold>\<langle>a \<star>\<^sub>B a\<^bold>\<rangle> (a \<star>\<^sub>B a) =
                    MkArr (\<^bold>\<langle>a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>) \<^bold>\<langle>a\<^bold>\<rangle> (\<i>\<^sub>B[a] \<cdot>\<^sub>B (a \<star>\<^sub>B a))"
                using assms
                by (intro comp_MkArr arr_MkArr) auto
              moreover have "MkArr (\<^bold>\<langle>a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>) \<^bold>\<langle>a\<^bold>\<rangle> (\<i>\<^sub>B[a] \<cdot>\<^sub>B (a \<star>\<^sub>B a))
                               \<cdot> MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 (\<^bold>\<langle>a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>) (B.runit' a) =
                             MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> ((\<i>\<^sub>B[a] \<cdot>\<^sub>B (a \<star>\<^sub>B a)) \<cdot>\<^sub>B B.runit' a)"
                using assms 0 B.comp_arr_dom
                by (intro comp_MkArr arr_MkArr, auto)
              ultimately show ?thesis by argo
            qed
            also have "... = MkArr \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<langle>a\<^bold>\<rangle> a"
              using assms B.comp_arr_dom B.comp_arr_inv' B.iso_unit B.unitor_coincidence(2)
              by simp
            finally show ?thesis by argo
          qed
          finally show ?thesis by simp
        qed
      qed
      thus ?thesis by simp
    qed

  end

  subsection "Pseudofunctors into a Strict Bicategory"

  text \<open>
    In the special case of a pseudofunctor into a strict bicategory, we can obtain
    explicit formulas for the images of the units and associativities under the pseudofunctor,
    which only involve the structure maps of the pseudofunctor, since the units and associativities
    in the target bicategory are all identities.  This is useful in applying strictification.
  \<close>

  locale pseudofunctor_into_strict_bicategory =
    pseudofunctor +
    D: strict_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
  begin

    lemma image_of_unitor:
    assumes "C.ide g"
    shows "F \<l>\<^sub>C[g] = (D.inv (\<Psi> (trg\<^sub>C g)) \<star>\<^sub>D F g) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g))"
    and "F \<r>\<^sub>C[g] = (F g \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C g))) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g))"
    and "F (C.lunit' g) = \<Phi> (trg\<^sub>C g, g) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C g) \<star>\<^sub>D F g)"
    and "F (C.runit' g) = \<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g))"
    proof -
      show A: "F \<l>\<^sub>C[g] = (D.inv (\<Psi> (trg\<^sub>C g)) \<star>\<^sub>D F g) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g))"
      proof -
        have 1: "\<guillemotleft>(D.inv (\<Psi> (trg\<^sub>C g)) \<star>\<^sub>D F g) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g)) :
                     F (trg\<^sub>C g \<star>\<^sub>C g) \<Rightarrow>\<^sub>D F g\<guillemotright>"
        proof
          show "\<guillemotleft>D.inv (\<Psi> (trg\<^sub>C g)) \<star>\<^sub>D F g : F (trg\<^sub>C g) \<star>\<^sub>D F g \<Rightarrow>\<^sub>D F g\<guillemotright>"
            using assms \<Psi>_char by (auto simp add: D.hcomp_obj_arr)
          show "\<guillemotleft>D.inv (\<Phi> (trg\<^sub>C g, g)) : F (trg\<^sub>C g \<star>\<^sub>C g) \<Rightarrow>\<^sub>D F (trg\<^sub>C g) \<star>\<^sub>D F g\<guillemotright>"
            using assms \<Phi>_in_hom(2) D.inv_is_inverse by simp
        qed
        have "(D.inv (\<Psi> (trg\<^sub>C g)) \<star>\<^sub>D F g) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g)) =
              F g \<cdot>\<^sub>D (D.inv (\<Psi> (trg\<^sub>C g)) \<star>\<^sub>D F g) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g))"
          using 1 D.comp_cod_arr by auto
        also have "... = (F \<l>\<^sub>C[g] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C g, g) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C g) \<star>\<^sub>D F g)) \<cdot>\<^sub>D
                           (D.inv (\<Psi> (trg\<^sub>C g)) \<star>\<^sub>D F g) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g))"
          using assms lunit_coherence [of g] D.strict_lunit by simp
        also have "... = F \<l>\<^sub>C[g] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C g, g) \<cdot>\<^sub>D
                                    ((\<Psi> (trg\<^sub>C g) \<star>\<^sub>D F g) \<cdot>\<^sub>D (D.inv (\<Psi> (trg\<^sub>C g)) \<star>\<^sub>D F g)) \<cdot>\<^sub>D
                                   D.inv (\<Phi> (trg\<^sub>C g, g))"
          using D.comp_assoc by simp
        also have "... = F \<l>\<^sub>C[g]"
        proof -
          have "(\<Psi> (trg\<^sub>C g) \<star>\<^sub>D F g) \<cdot>\<^sub>D (D.inv (\<Psi> (trg\<^sub>C g)) \<star>\<^sub>D F g) = F (trg\<^sub>C g) \<star>\<^sub>D F g"
            using assms \<Psi>_char D.whisker_right
            by (metis C.ideD(1) C.obj_trg C.trg.preserves_reflects_arr D.comp_arr_inv'
                \<Psi>_simps(5) preserves_arr preserves_ide)
          moreover have "\<Phi> (trg\<^sub>C g, g) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g)) = F (trg\<^sub>C g \<star>\<^sub>C g)"
            using assms D.comp_arr_inv D.inv_is_inverse by simp
          ultimately show ?thesis
            using assms D.comp_arr_dom D.comp_cod_arr \<Psi>_char by auto
        qed
        finally show ?thesis by simp
      qed
      show B: "F \<r>\<^sub>C[g] = (F g \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C g))) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g))"
      proof -
        have 1: "\<guillemotleft>(F g \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C g))) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g)) :
                    F (g \<star>\<^sub>C src\<^sub>C g) \<Rightarrow>\<^sub>D F g\<guillemotright>"
        proof
          show "\<guillemotleft>F g \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C g)) : F g \<star>\<^sub>D F (src\<^sub>C g) \<Rightarrow>\<^sub>D F g\<guillemotright>"
            using assms \<Psi>_char by (auto simp add: D.hcomp_arr_obj)
          show "\<guillemotleft>D.inv (\<Phi> (g, src\<^sub>C g)) : F (g \<star>\<^sub>C src\<^sub>C g) \<Rightarrow>\<^sub>D F g \<star>\<^sub>D F (src\<^sub>C g)\<guillemotright>"
            using assms \<Phi>_in_hom(2) by simp
        qed
        have "(F g \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C g))) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g)) =
              F g \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C g))) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g))"
          using 1 D.comp_cod_arr by auto
        also have "... = (F \<r>\<^sub>C[g] \<cdot>\<^sub>D \<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g))) \<cdot>\<^sub>D
                           (F g \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C g))) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g))"
           using assms runit_coherence [of g] D.strict_runit by simp
        also have "... = F \<r>\<^sub>C[g] \<cdot>\<^sub>D (\<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D ((F g \<star>\<^sub>D \<Psi> (src\<^sub>C g)) \<cdot>\<^sub>D
                           (F g \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C g))))) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g))"
           using D.comp_assoc by simp
        also have "... = F \<r>\<^sub>C[g]"
        proof -
          have "(F g \<star>\<^sub>D \<Psi> (src\<^sub>C g)) \<cdot>\<^sub>D (F g \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C g))) = F g \<star>\<^sub>D F (src\<^sub>C g)"
            using assms D.whisker_left \<Psi>_char
            by (metis C.ideD(1) C.obj_src C.src.preserves_ide D.comp_arr_inv' D.ideD(1)
                \<Psi>_simps(5) preserves_ide)
          moreover have "\<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g)) = F (g \<star>\<^sub>C src\<^sub>C g)"
            using assms D.comp_arr_inv D.inv_is_inverse by simp
          ultimately show ?thesis
            using assms D.comp_arr_dom D.comp_cod_arr \<Psi>_char \<Phi>_in_hom(2) [of g "src\<^sub>C g"]
            by auto
        qed
        finally show ?thesis by simp
      qed
      show "F (C.lunit' g) = \<Phi> (trg\<^sub>C g, g) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C g) \<star>\<^sub>D F g)"
      proof -
        have "F (C.lunit' g) = D.inv (F \<l>\<^sub>C[g])"
          using assms C.iso_lunit preserves_inv by simp
        also have "... = D.inv ((D.inv (\<Psi> (trg\<^sub>C g)) \<star>\<^sub>D F g) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C g, g)))"
          using A by simp
        also have "... = \<Phi> (trg\<^sub>C g, g) \<cdot>\<^sub>D (\<Psi> (trg\<^sub>C g) \<star>\<^sub>D F g)"
        proof -
          have "D.iso (D.inv (\<Phi> (trg\<^sub>C g, g))) \<and> D.inv (D.inv (\<Phi> (trg\<^sub>C g, g))) = \<Phi> (trg\<^sub>C g, g)"
            using assms D.iso_inv_iso by simp
          moreover have "D.iso (D.inv (\<Psi> (trg\<^sub>C g)) \<star>\<^sub>D F g) \<and>
                         D.inv (D.inv (\<Psi> (trg\<^sub>C g)) \<star>\<^sub>D F g) = \<Psi> (trg\<^sub>C g) \<star>\<^sub>D F g"
            using assms \<Psi>_char D.iso_inv_iso by simp
          moreover have "D.seq (D.inv (\<Psi> (trg\<^sub>C g)) \<star>\<^sub>D F g) (D.inv (\<Phi> (trg\<^sub>C g, g)))"
            using assms \<Psi>_char by (metis A C.lunit_simps(1) preserves_arr)
          ultimately show ?thesis
            using D.inv_comp by simp
        qed
        finally show ?thesis by simp
      qed
      show "F (C.runit' g) = \<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g))"
      proof -
        have "F (C.runit' g) = D.inv (F \<r>\<^sub>C[g])"
          using assms C.iso_runit preserves_inv by simp
        also have "... = D.inv ((F g \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C g))) \<cdot>\<^sub>D D.inv (\<Phi> (g, src\<^sub>C g)))"
          using B by simp
        also have "... = \<Phi> (g, src\<^sub>C g) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<Psi> (src\<^sub>C g))"
        proof -
          have "D.iso (D.inv (\<Phi> (g, src\<^sub>C g))) \<and> D.inv (D.inv (\<Phi> (g, src\<^sub>C g))) = \<Phi> (g, src\<^sub>C g)"
            using assms D.iso_inv_iso by simp
          moreover have "D.iso (F g \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C g))) \<and>
                         D.inv (F g \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C g))) = F g \<star>\<^sub>D \<Psi> (src\<^sub>C g)"
            using assms \<Psi>_char D.iso_inv_iso by simp
          moreover have "D.seq (F g \<star>\<^sub>D D.inv (\<Psi> (src\<^sub>C g))) (D.inv (\<Phi> (g, src\<^sub>C g)))"
            using assms \<Psi>_char by (metis B C.runit_simps(1) preserves_arr)
          ultimately show ?thesis
            using D.inv_comp by simp
        qed
        finally show ?thesis by simp
      qed
    qed

    lemma image_of_associator:
    assumes "C.ide f" and "C.ide g" and "C.ide h" and "src\<^sub>C f = trg\<^sub>C g" and "src\<^sub>C g = trg\<^sub>C h"
    shows "F \<a>\<^sub>C[f, g, h] = \<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D
                             (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, h))"
    and "F (C.\<a>' f g h) = \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) \<cdot>\<^sub>D
                                (F f \<star>\<^sub>D D.inv (\<Phi> (g, h))) \<cdot>\<^sub>D D.inv (\<Phi> (f, g \<star>\<^sub>C h))"
    proof -
      show 1: "F \<a>\<^sub>C[f, g, h] = \<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D
                                 (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, h))"
      proof -
        have 2: "D.seq (\<Phi> (f, g \<star>\<^sub>C h)) ((F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h])"
        proof (intro D.seqI)
          show "D.arr \<a>\<^sub>D[F f, F g, F h]"
            using assms D.assoc_in_hom(2) [of "F f" "F g" "F h"] by auto
          show "D.hseq (F f) (\<Phi> (g, h))"
            using assms by fastforce
          show "D.dom (F f \<star>\<^sub>D \<Phi> (g, h)) = D.cod \<a>\<^sub>D[F f, F g, F h]"
            using assms \<open>D.hseq (F f) (\<Phi> (g, h))\<close> \<Phi>_simps(1) \<Phi>_simps(4) by auto
          show "D.arr (\<Phi> (f, g \<star>\<^sub>C h))"
            using assms by auto
          show "D.dom (\<Phi> (f, g \<star>\<^sub>C h)) = D.cod ((F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h])"
            using assms \<open>D.hseq (F f) (\<Phi> (g, h))\<close> \<Phi>_simps(1) \<Phi>_simps(4) by auto
        qed
        moreover have 3: "F \<a>\<^sub>C[f, g, h] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) =
                          \<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h]"
          using assms assoc_coherence [of f g h] by blast
        moreover have "D.iso (\<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h))"
        proof -
          have "D.iso (\<Phi> (f \<star>\<^sub>C g, h)) \<and> D.iso (\<Phi> (f, g)) \<and> D.iso (F h)"
            using assms by simp
          moreover have "D.seq (\<Phi> (f \<star>\<^sub>C g, h)) (\<Phi> (f, g) \<star>\<^sub>D F h)"
          proof (intro D.seqI)
            show "D.hseq (\<Phi> (f, g)) (F h)"
              using assms C.VV.arr_char by simp
            show "D.arr (\<Phi> (f \<star>\<^sub>C g, h))"
              using assms C.VV.arr_char by simp
            show "D.dom (\<Phi> (f \<star>\<^sub>C g, h)) = D.cod (\<Phi> (f, g) \<star>\<^sub>D F h)"
              using assms 2 3 by (metis D.seqE)
          qed
          ultimately show ?thesis
            using assms D.isos_compose by simp
        qed
        ultimately have "F \<a>\<^sub>C[f, g, h] =
                         (\<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D ((F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h])) \<cdot>\<^sub>D
                           D.inv (\<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h))"
          using D.invert_side_of_triangle(2)
                  [of "\<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h]"
                      "F \<a>\<^sub>C[f, g, h]" "\<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h)"]
          by presburger
        also have "... = \<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D
                            (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, h))"
        proof -
          have "D.inv (\<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h)) =
                (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, h))"
          proof -
            have "D.iso (\<Phi> (f \<star>\<^sub>C g, h))"
              using assms D.iso_inv_iso by simp
            moreover have "D.iso (\<Phi> (f, g) \<star>\<^sub>D F h) \<and>
                           D.inv (\<Phi> (f, g) \<star>\<^sub>D F h) = D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h"
              using assms D.iso_inv_iso by simp
            moreover have "D.seq (\<Phi> (f \<star>\<^sub>C g, h)) (\<Phi> (f, g) \<star>\<^sub>D F h)"
              using assms by fastforce
            ultimately show ?thesis
              using D.inv_comp by simp
          qed
          moreover have "(F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h] = (F f \<star>\<^sub>D \<Phi> (g, h))"
            using assms D.comp_arr_dom D.assoc_in_hom [of "F f" "F g" "F h"] \<Phi>_in_hom
            by (metis "2" "3" D.comp_arr_ide D.hseq_char D.seqE D.strict_assoc
                \<Phi>_simps(2) \<Phi>_simps(3) preserves_ide)
          ultimately show ?thesis
            using D.comp_assoc by simp
        qed
        finally show ?thesis
          by simp
      qed
      show "F (C.\<a>' f g h) = \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) \<cdot>\<^sub>D
                               (F f \<star>\<^sub>D D.inv (\<Phi> (g, h))) \<cdot>\<^sub>D D.inv (\<Phi> (f, g \<star>\<^sub>C h))"
      proof -
        have "F (C.\<a>' f g h) = D.inv (F \<a>\<^sub>C[f, g, h])"
          using assms preserves_inv by simp
        also have "... = D.inv (\<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D
                                  (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, h)))"
          using 1 by simp
        also have "... = \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) \<cdot>\<^sub>D
                                   (F f \<star>\<^sub>D D.inv (\<Phi> (g, h))) \<cdot>\<^sub>D D.inv (\<Phi> (f, g \<star>\<^sub>C h))"
          using assms C.VV.arr_char D.iso_inv_iso FF_def D.hcomp_assoc D.comp_assoc
          (* OK, this is pretty cool, but not as cool as if I didn't have to direct it. *)
          by (simp add: D.inv_comp D.isos_compose)
        finally show ?thesis by simp
      qed
    qed

  end

  subsection "Internal Equivalences in a Strict Bicategory"

  text \<open>
    In this section we prove a useful fact about internal equivalences in a strict bicategory:
    namely, that if the ``right'' triangle identity holds for such an equivalence then the
    ``left'' does, as well.  Later we will dualize this property, and use strictification to
    extend it to arbitrary bicategories.
  \<close>

  locale equivalence_in_strict_bicategory =
    strict_bicategory +
    equivalence_in_bicategory
  begin

    lemma triangle_right_implies_left:
    shows "(g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g) = g \<Longrightarrow> (\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>) = f"
    proof -
      text \<open>
        The formal proof here was constructed following the string diagram sketch below,
        which appears in \cite{nlab-zigzag-diagram}
        (see it also in context in \cite{nlab-adjoint-equivalence}).
        The diagram is reproduced here by permission of its author, Mike Shulman,
        who says (private communication):
        ``Just don't give the impression that the proof itself is due to me, because it's not.
        I don't know who first gave that proof; it's probably folklore.''
        \begin{figure}[h]
          \includegraphics[width=6.5in]{triangle_right_implies_left.png}
        \end{figure}
      \<close>
      assume 1: "(g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g) = g"
      have 2: "(inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>) = g"
      proof -
        have "(inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>) = inv ((g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g))"
          using antipar inv_comp hcomp_assoc by simp
        also have "... = g"
          using 1 by simp
        finally show ?thesis by blast
      qed
      have "(\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>) = (\<epsilon> \<star> f) \<cdot> (f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>) \<star> f) \<cdot> (f \<star> \<eta>)"
      proof -
        have "(f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>) \<star> f) \<cdot> (f \<star> \<eta>) = f \<star> \<eta>"
          using 2 ide_left ide_right antipar whisker_left
          by (metis comp_cod_arr unit_simps(1) unit_simps(3))
        thus ?thesis by simp
      qed
      also have "... = (\<epsilon> \<star> f) \<cdot> (f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>) \<star> f) \<cdot> (f \<star> \<eta>) \<star> (inv \<eta> \<cdot> \<eta>)"
      proof -
        have "inv \<eta> \<cdot> \<eta> = src f"
          by (simp add: comp_inv_arr')
        thus ?thesis
          by (metis antipar(1) antipar(2) arrI calculation
              comp_ide_arr hcomp_arr_obj ideD(1) ide_left ide_right obj_src seqE
              strict_assoc' triangle_in_hom(1) vconn_implies_hpar(1))
      qed
      also have "... = (\<epsilon> \<cdot> (f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>)) \<star> ((f \<star> inv \<eta>) \<cdot> (f \<star> \<eta>))) \<cdot> (f \<star> \<eta>)"
        using ide_left ide_right antipar unit_is_iso
        by (metis "2" arr_inv calculation comp_arr_dom comp_inv_arr' counit_simps(1)
            counit_simps(2) dom_inv hcomp_arr_obj ideD(1) unit_simps(1) unit_simps(2)
            unit_simps(5) obj_trg seqI whisker_left)
      also have "... = (\<epsilon> \<cdot> (f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>)) \<star>
                         ((f \<star> inv \<eta>) \<cdot> ((inv \<epsilon> \<star> f) \<cdot> (\<epsilon> \<star> f)) \<cdot> (f \<star> \<eta>))) \<cdot> (f \<star> \<eta>)"
      proof -
        have "(inv \<epsilon> \<star> f) \<cdot> (\<epsilon> \<star> f) = (f \<star> g) \<star> f"
          using whisker_right [of f "inv \<epsilon>" \<epsilon>] counit_in_hom
          by (simp add: antipar(1) comp_inv_arr')
        thus ?thesis
          using hcomp_assoc comp_arr_dom
          by (metis comp_cod_arr ide_left local.unit_simps(1) local.unit_simps(3)
              whisker_left)
      qed
      also have "... = (((\<epsilon> \<cdot> (f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>))) \<cdot> (f \<star> g)) \<star>
                         (((f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f)) \<cdot> (\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>))) \<cdot>
                           (f \<star> \<eta>)"
        using ide_left ide_right antipar comp_assoc whisker_right comp_cod_arr
        by (metis "2" comp_arr_dom counit_simps(1-2))
      also have "... = (((\<epsilon> \<cdot> (f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>))) \<star> ((f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f))) \<cdot>
                         ((f \<star> g) \<star> (\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>))) \<cdot>
                           (f \<star> \<eta>)"
      proof -
        have 3: "seq (\<epsilon> \<cdot> (f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>))) (f \<star> g)"
          using 2 antipar by auto
        moreover have 4: "seq ((f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f)) ((\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>))"
          using antipar hcomp_assoc by auto
        ultimately show ?thesis
          using interchange by simp
      qed
      also have "... = ((\<epsilon> \<cdot> (f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>))) \<star> ((f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f))) \<cdot>
                        ((f \<star> g) \<star> (\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>)) \<cdot> (f \<star> \<eta>)"
        using comp_assoc by presburger
      also have "... = ((\<epsilon> \<star> (f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f)) \<cdot>
                         ((f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>)) \<star> f)) \<cdot>
                           (f \<star> (g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g) \<star> f) \<cdot> (f \<star> \<eta>)"
      proof -
        have "(\<epsilon> \<cdot> (f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>))) \<star> ((f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f)) =
              (\<epsilon> \<star> (f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f)) \<cdot> ((f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>)) \<star> f)"
        proof -
          have "seq \<epsilon> (f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>))"
            using 2 antipar by simp
          moreover have "seq ((f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f)) f"
            using antipar hcomp_assoc hcomp_obj_arr by auto
          ultimately show ?thesis
            using comp_assoc comp_arr_dom hcomp_obj_arr
                  interchange [of \<epsilon> "f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>)" "(f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f)" f]
            by simp
        qed
        moreover have "((f \<star> g) \<star> (\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>)) \<cdot> (f \<star> \<eta>) =
                       (f \<star> (g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g) \<star> f) \<cdot> (f \<star> \<eta>)"
        proof -
          have "((f \<star> g) \<star> (\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>)) \<cdot> (f \<star> \<eta>) =
                (f \<star> g \<star> \<epsilon> \<star> f) \<cdot> (f \<star> (g \<star> f) \<star> \<eta>) \<cdot> (f \<star> \<eta> \<star> src f)"
            using antipar comp_assoc hcomp_assoc whisker_left hcomp_arr_obj by simp
          also have "... = (f \<star> g \<star> \<epsilon> \<star> f) \<cdot> (f \<star> ((g \<star> f) \<star> \<eta>) \<cdot> (\<eta> \<cdot> src f))"
            using antipar comp_arr_dom whisker_left hcomp_arr_obj by simp
          also have "... = (f \<star> g \<star> \<epsilon> \<star> f) \<cdot> (f \<star> \<eta> \<star> \<eta>)"
            using antipar comp_arr_dom comp_cod_arr hcomp_arr_obj
                  interchange [of "g \<star> f" \<eta> \<eta> "src f"]
            by simp
          also have "... = (f \<star> g \<star> \<epsilon> \<star> f) \<cdot> (f \<star> \<eta> \<star> g \<star> f) \<cdot> (f \<star> src f \<star> \<eta>)"
            using antipar comp_arr_dom comp_cod_arr whisker_left
                  interchange [of \<eta> "src f" "g \<star> f" \<eta>]
            by simp
          also have "... = ((f \<star> g \<star> \<epsilon> \<star> f) \<cdot> (f \<star> \<eta> \<star> g \<star> f)) \<cdot> (f \<star> \<eta>)"
            using antipar comp_assoc by (simp add: hcomp_obj_arr)
          also have "... = (f \<star> (g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g) \<star> f) \<cdot> (f \<star> \<eta>)"
            using antipar comp_assoc whisker_left whisker_right hcomp_assoc by simp
          finally show ?thesis by blast
        qed
        ultimately show ?thesis by simp
      qed
      also have "... = (\<epsilon> \<star> (f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f)) \<cdot>
                         ((f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>) \<star> f) \<cdot>
                           (f \<star> (g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g) \<star> f)) \<cdot> (f \<star> \<eta>)"
        using comp_assoc hcomp_assoc antipar(1) antipar(2) by auto
      also have "... = (\<epsilon> \<star> (f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f)) \<cdot>
                         ((f \<star> (inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>) \<cdot> (g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g) \<star> f)) \<cdot>
                           (f \<star> \<eta>)"
        using ide_left ide_right antipar comp_cod_arr comp_assoc whisker_left
        by (metis "1" "2" comp_ide_self unit_simps(1) unit_simps(3))
      also have "... = (\<epsilon> \<star> (f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f)) \<cdot> (f \<star> \<eta>)"
      proof -
        have "(inv \<eta> \<star> g) \<cdot> (g \<star> inv \<epsilon>) \<cdot> (g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g) = g"
          using ide_left ide_right antipar comp_arr_dom comp_assoc
          by (metis "1" "2" comp_ide_self)
        thus ?thesis
          using antipar comp_cod_arr by simp
      qed
      also have "... = (f \<star> inv \<eta>) \<cdot> ((inv \<epsilon> \<star> f) \<cdot> (\<epsilon> \<star> f)) \<cdot> (f \<star> \<eta>)"
      proof -
        have "(\<epsilon> \<star> (f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f)) \<cdot> (f \<star> \<eta>) =
              (trg f \<cdot> \<epsilon> \<star> (f \<star> inv \<eta>) \<cdot> (inv \<epsilon> \<star> f)) \<cdot> (f \<star> \<eta>)"
          using hcomp_obj_arr comp_cod_arr by simp
        also have "... = ((trg f \<star> f \<star> inv \<eta>) \<cdot> (\<epsilon> \<star> inv \<epsilon> \<star> f)) \<cdot> (f \<star> \<eta>)"
          using antipar hcomp_arr_obj hcomp_assoc interchange by auto
        also have "... = (f \<star> inv \<eta>) \<cdot> ((inv \<epsilon> \<star> f) \<cdot> (\<epsilon> \<star> f)) \<cdot> (f \<star> \<eta>)"
        proof -
          have "(inv \<epsilon> \<star> f) \<cdot> (\<epsilon> \<star> f) = (trg f \<star> inv \<epsilon> \<star> f) \<cdot> (\<epsilon> \<star> trg f \<star> f)"
            using hseqI' by (simp add: hcomp_obj_arr)
          also have "... = \<epsilon> \<star> inv \<epsilon> \<star> f"
            using antipar comp_arr_dom comp_cod_arr
                  interchange [of "trg f" \<epsilon> "inv \<epsilon> \<star> f" "trg f \<star> f"]
            by force
          finally have "(inv \<epsilon> \<star> f) \<cdot> (\<epsilon> \<star> f) = \<epsilon> \<star> inv \<epsilon> \<star> f" by simp
          moreover have "trg f \<star> f \<star> inv \<eta> = f \<star> inv \<eta>"
            using hcomp_obj_arr [of "trg f" "f \<star> inv \<eta>"] by fastforce
          ultimately have "((trg f \<star> f \<star> inv \<eta>) \<cdot> (\<epsilon> \<star> inv \<epsilon> \<star> f)) \<cdot> (f \<star> \<eta>) =
                           ((f \<star> inv \<eta>) \<cdot> ((inv \<epsilon> \<star> f) \<cdot> (\<epsilon> \<star> f))) \<cdot> (f \<star> \<eta>)"
            by simp
          thus ?thesis
            using comp_assoc by simp
        qed
        finally show ?thesis by simp
      qed
      also have "... = f \<star> inv \<eta> \<cdot> \<eta>"
      proof -
        have "(inv \<epsilon> \<star> f) \<cdot> (\<epsilon> \<star> f) = f \<star> g \<star> f"
          using ide_left ide_right antipar counit_is_iso whisker_right hcomp_assoc
          by (metis comp_arr_dom comp_inv_arr' counit_simps(1) counit_simps(2) seqE)
        thus ?thesis
          using ide_left ide_right antipar unit_is_iso comp_cod_arr
          by (metis arr_inv dom_inv unit_simps(1) unit_simps(3) seqI whisker_left)
      qed
      also have "... = f \<star> src f"
        using antipar by (simp add: comp_inv_arr')
      also have "... = f"
        using hcomp_arr_obj by simp
      finally show ?thesis by simp
    qed

  end

  text \<open>
    Now we use strictification to generalize the preceding result to arbitrary bicategories.
    I originally attempted to generalize this proof directly from the strict case, by filling
    in the necessary canonical isomorphisms, but it turned out to be too daunting.
    The proof using strictification is still fairly tedious, but it is manageable.
  \<close>

  context equivalence_in_bicategory
  begin

    interpretation S: strictified_bicategory V H \<a> \<i> src trg ..

    notation S.vcomp  (infixr "\<cdot>\<^sub>S" 55)
    notation S.hcomp  (infixr "\<star>\<^sub>S" 53)
    notation S.in_hom  ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>S _\<guillemotright>")
    notation S.in_hhom  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>S _\<guillemotright>")

    interpretation UP: equivalence_pseudofunctor V H \<a> \<i> src trg
                          S.vcomp S.hcomp S.\<a> S.\<i> S.src S.trg S.UP S.\<Phi>
      using S.UP_is_equivalence_pseudofunctor by auto
    interpretation UP: pseudofunctor_into_strict_bicategory V H \<a> \<i> src trg
                          S.vcomp S.hcomp S.\<a> S.\<i> S.src S.trg S.UP S.\<Phi>
      ..
    interpretation E: equivalence_in_bicategory S.vcomp S.hcomp S.\<a> S.\<i> S.src S.trg
                        \<open>S.UP f\<close> \<open>S.UP g\<close>
                        \<open>S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<cdot>\<^sub>S UP.\<Psi> (src f)\<close>
                        \<open>S.inv (UP.\<Psi> (trg f)) \<cdot>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)\<close>
      using equivalence_in_bicategory_axioms UP.preserves_equivalence [of f g \<eta> \<epsilon>] by auto
    interpretation E: equivalence_in_strict_bicategory S.vcomp S.hcomp S.\<a> S.\<i> S.src S.trg
                        \<open>S.UP f\<close> \<open>S.UP g\<close>
                        \<open>S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<cdot>\<^sub>S UP.\<Psi> (src f)\<close>
                        \<open>S.inv (UP.\<Psi> (trg f)) \<cdot>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)\<close>
      ..

    lemma UP_triangle:
    shows "S.UP ((g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)) =
            S.\<Phi> (g, src g) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S
              (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g) \<cdot>\<^sub>S S.inv (S.\<Phi> (trg g, g))"
    and "S.UP (\<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]) =
            (S.\<Phi> (g, src g) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S UP.\<Psi> (src g))) \<cdot>\<^sub>S
               (S.inv (UP.\<Psi> (trg g)) \<star>\<^sub>S S.UP g) \<cdot>\<^sub>S S.inv (S.\<Phi> (trg g, g))"
    and "S.UP ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) =
            S.\<Phi> (trg f, f) \<cdot>\<^sub>S (S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
              (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
    and "S.UP (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]) =
            (S.\<Phi> (trg f, f) \<cdot>\<^sub>S (UP.\<Psi> (trg f) \<star>\<^sub>S S.UP f)) \<cdot>\<^sub>S
              (S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> (src f))) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
    and "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g] \<Longrightarrow>
            S.\<Phi> (trg f, f) \<cdot>\<^sub>S (S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                 (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f)) =
               (S.\<Phi> (trg f, f) \<cdot>\<^sub>S (UP.\<Psi> (trg f) \<star>\<^sub>S S.UP f)) \<cdot>\<^sub>S
                 (S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> (src f))) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
    proof -
      show T1: "S.UP ((g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)) =
                S.\<Phi> (g, src g) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S
                  (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g) \<cdot>\<^sub>S S.inv (S.\<Phi> (trg g, g))"
      proof -
        have "S.UP ((g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)) =
                S.UP (g \<star> \<epsilon>) \<cdot>\<^sub>S S.UP \<a>[g, f, g] \<cdot>\<^sub>S S.UP (\<eta> \<star> g)"
          using antipar by simp
        also have "... = (S.\<Phi> (g, src g) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.UP \<epsilon>) \<cdot>\<^sub>S ((S.inv (S.\<Phi> (g, f \<star> g)) \<cdot>\<^sub>S
                           S.\<Phi> (g, f \<star> g)) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.\<Phi> (f, g))) \<cdot>\<^sub>S
                             (((S.inv (S.\<Phi> (g, f)) \<star>\<^sub>S S.UP g) \<cdot>\<^sub>S (S.inv (S.\<Phi> (g \<star> f, g)))) \<cdot>\<^sub>S
                           S.\<Phi> (g \<star> f, g)) \<cdot>\<^sub>S (S.UP \<eta> \<star>\<^sub>S S.UP g)) \<cdot>\<^sub>S S.inv (S.\<Phi> (trg g, g))"
        proof -
          have "S.UP \<a>[g, f, g] =
                S.\<Phi> (g, f \<star> g) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S (S.inv (S.\<Phi> (g, f)) \<star>\<^sub>S S.UP g) \<cdot>\<^sub>S
                  S.inv (S.\<Phi> (g \<star> f, g))"
            using ide_left ide_right antipar UP.image_of_associator [of g f g] by simp
          moreover have
            "S.UP (g \<star> \<epsilon>) = S.\<Phi> (g, src g) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.UP \<epsilon>) \<cdot>\<^sub>S S.inv (S.\<Phi> (g, f \<star> g))"
          proof -
            have "S.seq (S.\<Phi> (g, src g)) (S.UP g \<star>\<^sub>S S.UP \<epsilon>)"
              using antipar UP.FF_def UP.\<Phi>_in_hom [of g "src g"]
              apply (intro S.seqI) by auto
            moreover have
              "S.UP (g \<star> \<epsilon>) \<cdot>\<^sub>S S.\<Phi> (g, f \<star> g) = S.\<Phi> (g, src g) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.UP \<epsilon>)"
              using antipar UP.\<Phi>.naturality [of "(g, \<epsilon>)"] UP.FF_def VV.arr_char by simp
            moreover have "S.iso (S.\<Phi> (g, f \<star> g))"
              using antipar by simp
            ultimately show ?thesis
              using antipar S.comp_assoc
                    S.invert_side_of_triangle(2)
                      [of "S.\<Phi> (g, src g) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.UP \<epsilon>)" "S.UP (g \<star> \<epsilon>)" "S.\<Phi> (g, f \<star> g)"]
              by simp
          qed
          moreover have "S.UP (\<eta> \<star> g) =
                         (S.\<Phi> (g \<star> f, g) \<cdot>\<^sub>S (S.UP \<eta> \<star>\<^sub>S S.UP g)) \<cdot>\<^sub>S S.inv (S.\<Phi> (trg g, g))"
          proof -
            have "S.UP (\<eta> \<star> g) \<cdot>\<^sub>S S.\<Phi> (trg g, g) = S.\<Phi> (g \<star> f, g) \<cdot>\<^sub>S (S.UP \<eta> \<star>\<^sub>S S.UP g)"
              using antipar UP.\<Phi>.naturality [of "(\<eta>, g)"] UP.FF_def VV.arr_char by simp
            moreover have "S.seq (S.\<Phi> (g \<star> f, g)) (S.UP \<eta> \<star>\<^sub>S S.UP g)"
              using antipar UP.\<Phi>_in_hom(2) by (intro S.seqI, auto)
            ultimately show ?thesis
              using antipar S.invert_side_of_triangle(2) by simp
          qed
          ultimately show ?thesis
            using S.comp_assoc by simp
        qed
        also have "... = S.\<Phi> (g, src g) \<cdot>\<^sub>S
                           ((S.UP g \<star>\<^sub>S S.UP \<epsilon>) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.\<Phi> (f, g))) \<cdot>\<^sub>S
                           ((S.inv (S.\<Phi> (g, f)) \<star>\<^sub>S S.UP g) \<cdot>\<^sub>S (S.UP \<eta> \<star>\<^sub>S S.UP g)) \<cdot>\<^sub>S
                           S.inv (S.\<Phi> (trg g, g))"
        proof -
          have "(S.inv (S.\<Phi> (g \<star> f, g)) \<cdot>\<^sub>S S.\<Phi> (g \<star> f, g)) \<cdot>\<^sub>S (S.UP \<eta> \<star>\<^sub>S S.UP g) =
                (S.UP \<eta> \<star>\<^sub>S S.UP g)"
            using antipar S.comp_inv_arr' S.comp_cod_arr by auto
          moreover have "(S.inv (S.\<Phi> (g, f \<star> g)) \<cdot>\<^sub>S S.\<Phi> (g, f \<star> g)) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.\<Phi> (f, g)) =
                         (S.UP g \<star>\<^sub>S S.\<Phi> (f, g))"
          proof -
            have "S.inv (S.\<Phi> (g, f \<star> g)) \<cdot>\<^sub>S S.\<Phi> (g, f \<star> g) = S.UP g \<star>\<^sub>S S.UP (f \<star> g)"
              using antipar S.comp_inv_arr' UP.\<Phi>_in_hom by auto
            thus ?thesis
              using antipar VV.arr_char S.comp_cod_arr by simp
          qed
          ultimately show ?thesis
            using S.comp_assoc by simp
        qed
        also have "... = S.\<Phi> (g, src g) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S
                           (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g) \<cdot>\<^sub>S S.inv (S.\<Phi> (trg g, g))"
            using antipar VV.arr_char S.whisker_left S.whisker_right by auto
        finally show ?thesis by simp
      qed
      show T2: "S.UP (\<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]) =
                (S.\<Phi> (g, src g) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S UP.\<Psi> (src g))) \<cdot>\<^sub>S
                   (S.inv (UP.\<Psi> (trg g)) \<star>\<^sub>S S.UP g) \<cdot>\<^sub>S S.inv (S.\<Phi> (trg g, g))"
        using UP.image_of_unitor by simp
      show "S.UP ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) =
            S.\<Phi> (trg f, f) \<cdot>\<^sub>S (S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
              (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
      proof -
        have "S.UP ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) =
                 S.UP (\<epsilon> \<star> f) \<cdot>\<^sub>S S.UP \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot>\<^sub>S S.UP (f \<star> \<eta>)"
          using antipar by simp
        also have "... = S.\<Phi> (trg f, f) \<cdot>\<^sub>S (S.UP \<epsilon> \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S (S.inv (S.\<Phi> (f \<star> g, f)) \<cdot>\<^sub>S
                           S.\<Phi> (f \<star> g, f) \<cdot>\<^sub>S (S.\<Phi> (f, g) \<star>\<^sub>S S.UP f)) \<cdot>\<^sub>S
                             (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f))) \<cdot>\<^sub>S (S.inv (S.\<Phi> (f, g \<star> f)) \<cdot>\<^sub>S
                           S.\<Phi> (f, g \<star> f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.UP \<eta>)) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
        proof -
          have "S.UP \<a>\<^sup>-\<^sup>1[f, g, f] =
                S.\<Phi> (f \<star> g, f) \<cdot>\<^sub>S (S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f))) \<cdot>\<^sub>S
                   S.inv (S.\<Phi> (f, g \<star> f))"
            using ide_left ide_right antipar UP.image_of_associator by simp
          moreover have "S.UP (\<epsilon> \<star> f) =
                         S.\<Phi> (trg f, f) \<cdot>\<^sub>S (S.UP \<epsilon> \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S S.inv (S.\<Phi> (f \<star> g, f))"
          proof -
            have "S.seq (S.\<Phi> (trg f, f)) (S.UP \<epsilon> \<star>\<^sub>S S.UP f)"
              using antipar UP.FF_def VV.ide_char VV.arr_char UP.\<Phi>_in_hom [of "trg f" f]
              apply (intro S.seqI) by auto
            moreover have
              "S.\<Phi> (trg f, f) \<cdot>\<^sub>S (S.UP \<epsilon> \<star>\<^sub>S S.UP f) = S.UP (\<epsilon> \<star> f) \<cdot>\<^sub>S S.\<Phi> (f \<star> g, f)"
              using antipar UP.\<Phi>.naturality [of "(\<epsilon>, f)"] UP.FF_def VV.arr_char by simp
            moreover have "S.iso (S.\<Phi> (f \<star> g, f))"
              using antipar by simp
            ultimately show ?thesis
              using antipar S.comp_assoc
                    S.invert_side_of_triangle(2)
                      [of "S.\<Phi> (trg f, f) \<cdot>\<^sub>S (S.UP \<epsilon> \<star>\<^sub>S S.UP f)" "S.UP (\<epsilon> \<star> f)" "S.\<Phi> (f \<star> g, f)"]
              by metis
          qed
          moreover have "S.UP (f \<star> \<eta>) =
                        (S.\<Phi> (f, g \<star> f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.UP \<eta>)) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
          proof -
            have "S.\<Phi> (f, g \<star> f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.UP \<eta>) = S.UP (f \<star> \<eta>) \<cdot>\<^sub>S S.\<Phi> (f, src f)"
              using antipar UP.\<Phi>.naturality [of "(f, \<eta>)"] UP.FF_def VV.arr_char by simp
            moreover have "S.seq (S.\<Phi> (f, g \<star> f)) (S.UP f \<star>\<^sub>S S.UP \<eta>)"
              using antipar by (intro S.seqI, auto)
            ultimately show ?thesis
              using antipar S.invert_side_of_triangle(2) by auto
          qed
          ultimately show ?thesis
            using S.comp_assoc by simp
        qed
        also have "... = S.\<Phi> (trg f, f) \<cdot>\<^sub>S
                           ((S.UP \<epsilon> \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S (S.\<Phi> (f, g) \<star>\<^sub>S S.UP f)) \<cdot>\<^sub>S
                           ((S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f))) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.UP \<eta>)) \<cdot>\<^sub>S
                           S.inv (S.\<Phi> (f, src f))"
        proof -
          have "(S.inv (S.\<Phi> (f \<star> g, f)) \<cdot>\<^sub>S S.\<Phi> (f \<star> g, f)) \<cdot>\<^sub>S (S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) =
                (S.\<Phi> (f, g) \<star>\<^sub>S S.UP f)"
            using antipar S.comp_cod_arr VV.arr_char S.comp_inv_arr' by auto
          moreover have "(S.inv (S.\<Phi> (f, g \<star> f)) \<cdot>\<^sub>S S.\<Phi> (f, g \<star> f)) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.UP \<eta>) =
                         (S.UP f \<star>\<^sub>S S.UP \<eta>)"
            using antipar S.comp_inv_arr' S.comp_cod_arr by auto
          ultimately show ?thesis
            using S.comp_assoc by simp
        qed
        also have "... = S.\<Phi> (trg f, f) \<cdot>\<^sub>S (S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                           (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
            using antipar VV.arr_char S.whisker_left S.whisker_right by auto
        finally show ?thesis by simp
      qed
      show "S.UP (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]) =
            (S.\<Phi> (trg f, f) \<cdot>\<^sub>S (UP.\<Psi> (trg f) \<star>\<^sub>S S.UP f)) \<cdot>\<^sub>S
              (S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> (src f))) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
        using UP.image_of_unitor by simp
      show "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g] \<Longrightarrow>
              S.\<Phi> (trg f, f) \<cdot>\<^sub>S (S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                  (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f)) =
              (S.\<Phi> (trg f, f) \<cdot>\<^sub>S (UP.\<Psi> (trg f) \<star>\<^sub>S S.UP f)) \<cdot>\<^sub>S
                  (S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> (src f))) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
      proof -
        assume A: "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
        have B: "(S.UP g \<star>\<^sub>S S.inv (UP.\<Psi> (src g)) \<cdot>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S
                   (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<cdot>\<^sub>S UP.\<Psi> (trg g) \<star>\<^sub>S S.UP g) = S.UP g"
        proof -
          show "(S.UP g \<star>\<^sub>S S.inv (UP.\<Psi> (src g)) \<cdot>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S
                (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<cdot>\<^sub>S UP.\<Psi> (trg g) \<star>\<^sub>S S.UP g) = S.UP g"
          proof -
            have 2: "S.\<Phi> (g, src g) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S
                       (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g) \<cdot>\<^sub>S S.inv (S.\<Phi> (trg g, g)) =
                     (S.\<Phi> (g, src g) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S UP.\<Psi> (src g))) \<cdot>\<^sub>S
                       (S.inv (UP.\<Psi> (trg g)) \<star>\<^sub>S S.UP g) \<cdot>\<^sub>S S.inv (S.\<Phi> (trg g, g))"
              using A T1 T2 by simp
            show ?thesis
            proof -
              have 8: "S.seq (S.\<Phi> (g, src g))
                             ((S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S
                               (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g) \<cdot>\<^sub>S
                               S.inv (S.\<Phi> (trg g, g)))"
                using antipar VV.arr_char S.hcomp_assoc
                apply (intro S.seqI) by auto
              have 7: "S.seq (S.\<Phi> (g, src g))
                             ((S.UP g \<star>\<^sub>S UP.\<Psi> (src g)) \<cdot>\<^sub>S (S.inv (UP.\<Psi> (trg g)) \<star>\<^sub>S S.UP g) \<cdot>\<^sub>S
                               S.inv (S.\<Phi> (trg g, g)))"
                using antipar 2 8 S.comp_assoc by auto
              have 5: "(S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S
                         (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g) =
                       (S.UP g \<star>\<^sub>S UP.\<Psi> (src g)) \<cdot>\<^sub>S (S.inv (UP.\<Psi> (trg g)) \<star>\<^sub>S S.UP g)"
              proof -
                have "((S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S
                        S.UP \<eta> \<star>\<^sub>S S.UP g)) \<cdot>\<^sub>S S.inv (S.\<Phi> (trg g, g)) =
                      ((S.UP g \<star>\<^sub>S UP.\<Psi> (src g)) \<cdot>\<^sub>S (S.inv (UP.\<Psi> (trg g)) \<star>\<^sub>S S.UP g)) \<cdot>\<^sub>S
                        S.inv (S.\<Phi> (trg g, g))"
                proof -
                  have "S.mono (S.\<Phi> (g, src g))"
                    using antipar S.iso_is_section S.section_is_mono by simp
                  thus ?thesis
                    using 2 8 7 S.monoE S.comp_assoc by presburger
                qed
                moreover have "S.epi (S.inv (S.\<Phi> (trg g, g)))"
                  using antipar S.iso_is_retraction S.retraction_is_epi S.iso_inv_iso
                  by simp
                moreover have "S.seq ((S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S
                                      S.UP \<eta> \<star>\<^sub>S S.UP g))
                                     (S.inv (S.\<Phi> (trg g, g)))"
                  using S.comp_assoc S.seq_char 8 by presburger
                moreover have
                  "S.seq ((S.UP g \<star>\<^sub>S UP.\<Psi> (src g)) \<cdot>\<^sub>S (S.inv (UP.\<Psi> (trg g)) \<star>\<^sub>S S.UP g))
                         (S.inv (S.\<Phi> (trg g, g)))"
                  using antipar calculation(1) calculation(3) by presburger
                ultimately show ?thesis
                  using 2 S.epiE by blast
              qed
              have 6: "S.seq (S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g))
                             (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g)"
                using antipar VV.arr_char S.hcomp_assoc by auto
              have 3: "(S.UP g \<star>\<^sub>S S.inv (UP.\<Psi> (src g))) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S
                       (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g) =
                       (S.inv (UP.\<Psi> (trg g)) \<star>\<^sub>S S.UP g)"
              proof -
                have "S.seq (S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g))
                            (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g)"
                  using 6 by simp
                moreover have "(S.UP g \<star>\<^sub>S UP.\<Psi> (src g)) \<cdot>\<^sub>S (S.inv (UP.\<Psi> (trg g)) \<star>\<^sub>S S.UP g) =
                               (S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S
                                 (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g)"
                  using 5 by argo
                moreover have "S.iso (S.UP g \<star>\<^sub>S UP.\<Psi> (src g))"
                  using antipar UP.\<Psi>_char S.UP_map\<^sub>0_obj by simp
                moreover have "S.inv (S.UP g \<star>\<^sub>S UP.\<Psi> (src g)) =
                               S.UP g \<star>\<^sub>S S.inv (UP.\<Psi> (src g))"
                  using antipar UP.\<Psi>_char S.UP_map\<^sub>0_obj by simp
                ultimately show ?thesis
                  using S.invert_side_of_triangle(1)
                          [of "(S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g)) \<cdot>\<^sub>S
                                 (S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g)"
                              "S.UP g \<star>\<^sub>S UP.\<Psi> (src g)" "S.inv (UP.\<Psi> (trg g)) \<star>\<^sub>S S.UP g"]
                  by presburger
              qed
              have 4: "(((S.UP g \<star>\<^sub>S S.inv (UP.\<Psi> (src g))) \<cdot>\<^sub>S
                         (S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g))) \<cdot>\<^sub>S
                         ((S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g)) \<cdot>\<^sub>S (UP.\<Psi> (trg g) \<star>\<^sub>S S.UP g))
                       = S.UP g"
              proof -
                have "(((S.UP g \<star>\<^sub>S S.inv (UP.\<Psi> (src g))) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g))) \<cdot>\<^sub>S
                         ((S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g)) \<cdot>\<^sub>S (UP.\<Psi> (trg g) \<star>\<^sub>S S.UP g)) =
                      (((S.UP g \<star>\<^sub>S S.inv (UP.\<Psi> (src g))) \<cdot>\<^sub>S (S.UP g \<star>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g))) \<cdot>\<^sub>S
                         ((S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<star>\<^sub>S S.UP g))) \<cdot>\<^sub>S (UP.\<Psi> (trg g) \<star>\<^sub>S S.UP g)"
                  using S.comp_assoc by simp
                also have "... = (S.inv (UP.\<Psi> (trg g)) \<star>\<^sub>S S.UP g) \<cdot>\<^sub>S (UP.\<Psi> (trg g) \<star>\<^sub>S S.UP g)"
                  using 3 S.comp_assoc by auto
                also have "... = S.inv (UP.\<Psi> (trg g)) \<cdot>\<^sub>S UP.\<Psi> (trg g) \<star>\<^sub>S S.UP g"
                  using UP.\<Psi>_char(2) S.whisker_right by auto
                also have "... = UP.map\<^sub>0 (trg g) \<star>\<^sub>S S.UP g"
                  using UP.\<Psi>_char [of "trg g"] S.comp_inv_arr S.inv_is_inverse by simp
                also have "... = S.UP g"
                  using S.UP_map\<^sub>0_obj by (simp add: S.hcomp_obj_arr)
                finally show ?thesis by blast
              qed
              thus ?thesis
                using antipar S.whisker_left S.whisker_right UP.\<Psi>_char S.comp_assoc by simp
            qed
          qed
        qed
        show "S.\<Phi> (trg f, f) \<cdot>\<^sub>S (S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f)) =
              (S.\<Phi> (trg f, f) \<cdot>\<^sub>S (UP.\<Psi> (trg f) \<star>\<^sub>S S.UP f)) \<cdot>\<^sub>S
                (S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> (src f))) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
        proof -
          have "(S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) =
                   (UP.\<Psi> (trg f) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> (src f)))"
          proof -
            have 2: "(S.inv (UP.\<Psi> (trg f)) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                        ((S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                          (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>)) \<cdot>\<^sub>S
                        (S.UP f \<star>\<^sub>S UP.\<Psi> (src f)) =
                     S.UP f"
            proof -
              have "S.UP f = (S.inv (UP.\<Psi> (trg f)) \<cdot>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                               (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<cdot>\<^sub>S UP.\<Psi> (src f))"
                using B antipar E.triangle_right_implies_left by argo
              also have "... = (S.inv (UP.\<Psi> (trg f)) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                                 ((S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                                    (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>)) \<cdot>\<^sub>S
                                 (S.UP f \<star>\<^sub>S UP.\<Psi> (src f))"
              proof -
                have "S.inv (UP.\<Psi> (trg f)) \<cdot>\<^sub>S S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f =
                        (S.inv (UP.\<Psi> (trg f)) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S (S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f)"
                  using UP.\<Psi>_char S.whisker_right by simp
                moreover have "S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta> \<cdot>\<^sub>S UP.\<Psi> (src f) =
                                 (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>) \<cdot>\<^sub>S
                                   (S.UP f \<star>\<^sub>S UP.\<Psi> (src f))"
                  using antipar UP.\<Psi>_char S.whisker_left S.comp_assoc by simp
                ultimately show ?thesis
                  using S.comp_assoc by presburger
              qed
              finally show ?thesis by argo
            qed
            show ?thesis
            proof -
              have "((S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                        (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>)) \<cdot>\<^sub>S (S.UP f \<star>\<^sub>S UP.\<Psi> (src f)) =
                     (UP.\<Psi> (trg f) \<star>\<^sub>S S.UP f)"
              proof -
                have "S.inv (S.inv (UP.\<Psi> (trg f)) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S S.UP f = UP.\<Psi> (trg f) \<star>\<^sub>S S.UP f"
                  using UP.\<Psi>_char S.iso_inv_iso S.comp_arr_dom S.UP_map\<^sub>0_obj
                  by (simp add: S.hcomp_obj_arr)
                moreover have "S.arr (S.UP f)"
                  by simp
                moreover have "S.iso (S.inv (UP.\<Psi> (trg f)) \<star>\<^sub>S S.UP f)"
                  using S.iso_inv_iso S.UP_map\<^sub>0_obj
                  by (simp add: UP.\<Psi>_char(2))
                ultimately show ?thesis
                  using 2 S.invert_side_of_triangle(1)
                            [of "S.UP f" "S.inv (UP.\<Psi> (trg f)) \<star>\<^sub>S S.UP f"
                                "((S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                                   (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>)) \<cdot>\<^sub>S
                                 (S.UP f \<star>\<^sub>S UP.\<Psi> (src f))"]
                  by presburger
              qed
              moreover have "S.hseq (UP.\<Psi> (trg f)) (S.UP f) \<and>
                             S.iso (S.UP f \<star>\<^sub>S UP.\<Psi> (src f)) \<and>
                             S.inv (S.UP f \<star>\<^sub>S UP.\<Psi> (src f)) = S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> (src f))"
                using UP.\<Psi>_char S.UP_map\<^sub>0_obj by simp
              ultimately show ?thesis
                using S.invert_side_of_triangle(2)
                        [of "UP.\<Psi> (trg f) \<star>\<^sub>S S.UP f"
                            "(S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                               (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>)"
                            "S.UP f \<star>\<^sub>S UP.\<Psi> (src f)"]
                by presburger
            qed
          qed
          hence "S.\<Phi> (trg f, f) \<cdot>\<^sub>S ((S.UP \<epsilon> \<cdot>\<^sub>S S.\<Phi> (f, g) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                   (S.UP f \<star>\<^sub>S S.inv (S.\<Phi> (g, f)) \<cdot>\<^sub>S S.UP \<eta>)) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f)) =
                 S.\<Phi> (trg f, f) \<cdot>\<^sub>S ((UP.\<Psi> (trg f) \<star>\<^sub>S S.UP f) \<cdot>\<^sub>S
                   (S.UP f \<star>\<^sub>S S.inv (UP.\<Psi> (src f)))) \<cdot>\<^sub>S S.inv (S.\<Phi> (f, src f))"
            by simp
          thus ?thesis
            using S.comp_assoc by simp
        qed
      qed
    qed

    lemma triangle_right_implies_left:
    assumes "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
    shows "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
    proof -
      have "par ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f])"
        using antipar by simp
      moreover have "S.UP ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) = S.UP (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f])"
        using assms UP_triangle(3-5) by simp
      ultimately show "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
        using UP.is_faithful by blast
    qed

    text \<open>
      We \emph{really} don't want to go through the ordeal of proving a dual version of
      \<open>UP_triangle(5)\<close>, do we?  So let's be smart and dualize via the opposite bicategory.
    \<close>

    lemma triangle_left_implies_right:
    assumes "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
    shows "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
    proof -
      interpret Cop: op_bicategory V H \<a> \<i> src trg ..
      interpret Eop: equivalence_in_bicategory V Cop.H Cop.\<a> \<i> Cop.src Cop.trg g f \<eta> \<epsilon>
      using antipar unit_in_hom counit_in_hom iso_inv_iso
        by (unfold_locales, simp_all)
      have "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<Longrightarrow>
            (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
        using antipar Cop.lunit_ide_simp Cop.runit_ide_simp Cop.assoc_ide_simp
              VVV.ide_char VVV.arr_char VV.arr_char Eop.triangle_right_implies_left
        by simp
      thus ?thesis
        using assms by simp
    qed

    lemma triangle_left_iff_right:
    shows "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<longleftrightarrow>
           (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
      using triangle_left_implies_right triangle_right_implies_left by auto

  end

  text \<open>
    We might as well specialize the dual result back to the strict case while we are at it.
  \<close>

  context equivalence_in_strict_bicategory
  begin

    lemma triangle_left_iff_right:
    shows "(\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>) = f \<longleftrightarrow> (g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g) = g"
    proof -
      have "(\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>) = f \<longleftrightarrow> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
      proof -
        have "\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] = f"
          using strict_lunit strict_runit by simp
        moreover have "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = (\<epsilon> \<star> f) \<cdot> (f \<star> \<eta>)"
          using antipar strict_assoc assoc'_in_hom(2) [of f g f] comp_cod_arr
          by auto
        ultimately show ?thesis by simp
      qed
      also have "... \<longleftrightarrow> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
        using triangle_left_iff_right by blast
      also have "... \<longleftrightarrow> (g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g) = g"
      proof -
        have "\<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g] = g"
          using strict_lunit strict_runit by simp
        moreover have "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = (g \<star> \<epsilon>) \<cdot> (\<eta> \<star> g)"
          using antipar strict_assoc assoc_in_hom(2) [of g f g] comp_cod_arr
          by auto
        ultimately show ?thesis by simp
      qed
      finally show ?thesis by simp
    qed

  end

end
