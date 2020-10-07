(*  Title:       Category
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Category"

theory Category
imports Main "HOL-Library.FuncSet"
begin

  text \<open>
    This theory develops an ``object-free'' definition of category loosely following
    \cite{AHS}, Sec. 3.52-3.53.
    We define the notion ``category'' in terms of axioms that concern a single
    partial binary operation on a type, some of whose elements are to be regarded
    as the ``arrows'' of the category.

    The nonstandard definition of category has some advantages and disadvantages.
    An advantage is that only one piece of data (the composition operation) is required
    to specify a category, so the use of records is not required to bundle up several
    separate objects.  A related advantage is the fact that functors and natural
    transformations can be defined simply to be functions that satisfy certain axioms,
    rather than more complex composite objects.
    One disadvantage is that the notions of ``object'' and ``identity arrow'' are
    conflated, though this is easy to get used to.  Perhaps a more significant disadvantage
    is that each arrow of a category must carry along the information about its domain
    and codomain. This implies, for example, that the arrows of a category of sets and
    functions cannot be directly identified with functions, but rather only with functions that
    have been equipped with their domain and codomain sets.

    To represent the partiality of the composition operation of a category, we assume that the
    composition for a category has a unique zero element, which we call \<open>null\<close>,
    and we consider arrows to be ``composable'' if and only if their composite is non-null.
    Functors and natural transformations are required to map arrows to arrows and be
    ``extensional'' in the sense that they map non-arrows to null.  This is so that
    equality of functors and natural transformations coincides with their extensional equality
    as functions in HOL.
    The fact that we co-opt an element of the arrow type to serve as \<open>null\<close> means that
    it is not possible to define a category whose arrows exhaust the elements of a given type.
    This presents a disadvantage in some situations.  For example, we cannot construct a
    discrete category whose arrows are directly identified with the set of \emph{all}
    elements of a given type @{typ 'a}; instead, we must pass to a larger type
    (such as @{typ "'a option"}) so that there is an element available for use as \<open>null\<close>.
    The presence of \<open>null\<close>, however, is crucial to our being able to define a
    system of introduction and elimination rules that can be applied automatically to establish
    that a given expression denotes an arrow.  Without \<open>null\<close>, we would be able to
    define an introduction rule to infer, say, that the composition of composable arrows
    is composable, but not an elimination rule to infer that arrows are composable from
    the fact that their composite is an arrow.  Having the ability to do both is critical
    to the usability of the theory.
\<close>

  section "Partial Magmas"

  text \<open>
    A \emph{partial magma} is a partial binary operation \<open>C\<close> defined on the set
    of elements at a type @{typ 'a}.  As discussed above,
    we assume the existence of a unique element \<open>null\<close> of type @{typ 'a}
    that is a zero for \<open>C\<close>, and we use \<open>null\<close> to represent ``undefined''.
    We think of the operation \<open>C\<close> as an operation of ``composition'', and
    we regard elements \<open>f\<close> and \<open>g\<close> of type @{typ 'a} as \emph{composable}
    if \<open>C g f \<noteq> null\<close>.
\<close>

  type_synonym 'a comp = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

  locale partial_magma =
  fixes C :: "'a comp" (infixr "\<cdot>" 55)
  assumes ex_un_null: "\<exists>!n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n"
  begin

    definition null :: 'a
    where "null = (THE n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n)"

    lemma null_eqI:
    assumes "\<And>f. n \<cdot> f = n \<and> f \<cdot> n = n"
    shows "n = null"
      using assms null_def ex_un_null the1_equality [of "\<lambda>n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n"]
      by auto
    
    lemma comp_null [simp]:
    shows "null \<cdot> f = null" and "f \<cdot> null = null"
      using null_def ex_un_null theI' [of "\<lambda>n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n"]
      by auto

    text \<open>
      An \emph{identity} is a self-composable element \<open>a\<close> such that composition of
      any other element \<open>f\<close> with \<open>a\<close> on either the left or the right results in
      \<open>f\<close> whenever the composition is defined.
\<close>

    definition ide
    where "ide a \<equiv> a \<cdot> a \<noteq> null \<and>
                   (\<forall>f. (f \<cdot> a \<noteq> null \<longrightarrow> f \<cdot> a = f) \<and> (a \<cdot> f \<noteq> null \<longrightarrow> a \<cdot> f = f))"

    text \<open>
      A \emph{domain} of an element \<open>f\<close> is an identity \<open>a\<close> for which composition of
      \<open>f\<close> with \<open>a\<close> on the right is defined.
      The notion \emph{codomain} is defined similarly, using composition on the left.
      Note that, although these definitions are completely dual, the choice of terminology
      implies that we will think of composition as being written in traditional order,
      as opposed to diagram order.  It is pretty much essential to do it this way, to maintain
      compatibility with the notation for function application once we start working with
      functors and natural transformations.
\<close>

    definition domains
    where "domains f \<equiv> {a. ide a \<and> f \<cdot> a \<noteq> null}"

    definition codomains
    where "codomains f \<equiv> {b. ide b \<and> b \<cdot> f \<noteq> null}"

    lemma domains_null:
    shows "domains null = {}"
      by (simp add: domains_def)

    lemma codomains_null:
    shows "codomains null = {}"
      by (simp add: codomains_def)

    lemma self_domain_iff_ide:
    shows "a \<in> domains a \<longleftrightarrow> ide a"
      using ide_def domains_def by auto

    lemma self_codomain_iff_ide:
    shows "a \<in> codomains a \<longleftrightarrow> ide a"
      using ide_def codomains_def by auto

    text \<open>
      An element \<open>f\<close> is an \emph{arrow} if either it has a domain or it has a codomain.
      In an arbitrary partial magma it is possible for \<open>f\<close> to have one but not the other,
      but the \<open>category\<close> locale will include assumptions to rule this out.
\<close>

    definition arr
    where "arr f \<equiv> domains f \<noteq> {} \<or> codomains f \<noteq> {}"

    lemma not_arr_null [simp]:
    shows "\<not> arr null"
      by (simp add: arr_def domains_null codomains_null)

    text \<open>
      Using the notions of domain and codomain, we can define \emph{homs}.
      The predicate @{term "in_hom f a b"} expresses ``@{term f} is an arrow from @{term a}
      to @{term b},'' and the term @{term "hom a b"} denotes the set of all such arrows.
      It is convenient to have both of these, though passing back and forth sometimes involves
      extra work.  We choose @{term "in_hom"} as the more fundamental notion.
\<close>

    definition in_hom     ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    where "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<equiv> a \<in> domains f \<and> b \<in> codomains f"

    abbreviation hom
    where "hom a b \<equiv> {f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright>}"

    lemma arrI:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
    shows "arr f"
      using assms arr_def in_hom_def by auto

    lemma ide_in_hom [intro]:
    shows "ide a \<longleftrightarrow> \<guillemotleft>a : a \<rightarrow> a\<guillemotright>"
      using self_domain_iff_ide self_codomain_iff_ide in_hom_def ide_def by fastforce

    text \<open>
      Arrows @{term "f"} @{term "g"} for which the composite @{term "g \<cdot> f"} is defined
      are \emph{sequential}.
\<close>

    abbreviation seq
    where "seq g f \<equiv> arr (g \<cdot> f)"

    lemma comp_arr_ide:
    assumes "ide a" and "seq f a"
    shows "f \<cdot> a = f"
      using assms ide_in_hom ide_def not_arr_null by metis

    lemma comp_ide_arr:
    assumes "ide b" and "seq b f"
    shows "b \<cdot> f = f"
      using assms ide_in_hom ide_def not_arr_null by metis

    text \<open>
      The \emph{domain} of an arrow @{term f} is an element chosen arbitrarily from the
      set of domains of @{term f} and the \emph{codomain} of @{term f} is an element chosen
      arbitrarily from the set of codomains.
\<close>

    definition dom
    where "dom f = (if domains f \<noteq> {} then (SOME a. a \<in> domains f) else null)"

    definition cod
    where "cod f = (if codomains f \<noteq> {} then (SOME b. b \<in> codomains f) else null)"

    lemma dom_null [simp]:
    shows "dom null = null"
      by (simp add: dom_def domains_null)

    lemma cod_null [simp]:
    shows "cod null = null"
      by (simp add: cod_def codomains_null)

    lemma dom_in_domains:
    assumes "domains f \<noteq> {}"
    shows "dom f \<in> domains f"
      using assms dom_def someI [of "\<lambda>a. a \<in> domains f"] by auto

    lemma cod_in_codomains:
    assumes "codomains f \<noteq> {}"
    shows "cod f \<in> codomains f"
      using assms cod_def someI [of "\<lambda>b. b \<in> codomains f"] by auto

  end

  section "Categories"

  text\<open>
    A \emph{category} is defined to be a partial magma whose composition satisfies an
    extensionality condition, an associativity condition, and the requirement that every
    arrow have both a domain and a codomain.
    The associativity condition involves four ``matching conditions''
    (\<open>match_1\<close>, \<open>match_2\<close>, \<open>match_3\<close>, and \<open>match_4\<close>)
    which constrain the domain of definition of the composition, and a fifth condition
    (\<open>comp_assoc'\<close>) which states that the results of the two ways of composing
    three elements are equal.  In the presence of the \<open>comp_assoc'\<close> axiom
    \<open>match_4\<close> can be derived from \<open>match_3\<close> and vice versa.
\<close>

  locale category = partial_magma +
  assumes ext: "g \<cdot> f \<noteq> null \<Longrightarrow> seq g f"
  and has_domain_iff_has_codomain: "domains f \<noteq> {} \<longleftrightarrow> codomains f \<noteq> {}"
  and match_1: "\<lbrakk> seq h g; seq (h \<cdot> g) f \<rbrakk> \<Longrightarrow> seq g f"
  and match_2: "\<lbrakk> seq h (g \<cdot> f); seq g f \<rbrakk> \<Longrightarrow> seq h g"
  and match_3: "\<lbrakk> seq g f; seq h g \<rbrakk> \<Longrightarrow> seq (h \<cdot> g) f"
  and comp_assoc': "\<lbrakk> seq g f; seq h g \<rbrakk> \<Longrightarrow> (h \<cdot> g) \<cdot> f = h \<cdot> g \<cdot> f"
  begin

    text\<open>
      Associativity of composition holds unconditionally.  This was not the case in
      previous, weaker versions of this theory, and I did not notice this for some
      time after updating to the current axioms.  It is obviously an advantage that
      no additional hypotheses have to be verified in order to apply associativity,
      but a disadvantage is that this fact is now ``too readily applicable,''
      so that if it is made a default simplification it tends to get in the way of
      applying other simplifications that we would also like to be able to apply automatically.
      So, it now seems best not to make this fact a default simplification, but rather
      to invoke it explicitly where it is required.
\<close>

    lemma comp_assoc:
    shows "(h \<cdot> g) \<cdot> f = h \<cdot> g \<cdot> f"
    proof -
      have "seq g f \<and> seq h g \<Longrightarrow> ?thesis"
        using comp_assoc' by simp
      moreover have "\<not> (seq g f \<and> seq h g) \<Longrightarrow> ?thesis"
        using ext by (metis comp_null match_1 match_2)
      ultimately show ?thesis by blast
    qed

    lemma match_4:
    assumes "seq g f" and "seq h g"
    shows "seq h (g \<cdot> f)"
      using assms match_3 comp_assoc by auto

    lemma domains_comp:
    assumes "seq g f"
    shows "domains (g \<cdot> f) = domains f"
    proof -
      have "domains (g \<cdot> f) = {a. ide a \<and> seq (g \<cdot> f) a}"
        using domains_def ext by auto
      also have "... = {a. ide a \<and> seq f a}"
        using assms ide_def match_1 match_3 by meson
      also have "... = domains f"
        using domains_def ext by auto
      finally show ?thesis by blast
    qed

    lemma codomains_comp:
    assumes "seq g f"
    shows "codomains (g \<cdot> f) = codomains g"
    proof -
      have "codomains (g \<cdot> f) = {b. ide b \<and> seq b (g \<cdot> f)}"
        using codomains_def ext by auto
      also have "... = {b. ide b \<and> seq b g}"
        using assms ide_def match_2 match_4 by meson
      also have "... = codomains g"
        using codomains_def ext by auto
      finally show ?thesis by blast
    qed

    lemma has_domain_iff_arr:
    shows "domains f \<noteq> {} \<longleftrightarrow> arr f"
      by (simp add: arr_def has_domain_iff_has_codomain)

    lemma has_codomain_iff_arr:
    shows "codomains f \<noteq> {} \<longleftrightarrow> arr f"
      using has_domain_iff_arr has_domain_iff_has_codomain by auto

    text\<open>
      A consequence of the category axioms is that domains and codomains, if they exist,
      are unique.
\<close>

    lemma domain_unique:
    assumes "a \<in> domains f" and "a' \<in> domains f"
    shows "a = a'"
    proof -
      have "ide a \<and> seq f a \<and> ide a' \<and> seq f a'"
        using assms domains_def ext by force
      then show ?thesis
        using match_1 ide_def not_arr_null by metis
    qed

    lemma codomain_unique:
    assumes "b \<in> codomains f" and "b' \<in> codomains f"
    shows "b = b'"
    proof -
      have "ide b \<and> seq b f \<and> ide b' \<and> seq b' f"
        using assms codomains_def ext by force
      thus ?thesis
        using match_2 ide_def not_arr_null by metis
    qed

    lemma domains_char:
    assumes "arr f"
    shows "domains f = {dom f}"
      using assms dom_in_domains has_domain_iff_arr domain_unique by auto

    lemma codomains_char:
    assumes "arr f"
    shows "codomains f = {cod f}"
      using assms cod_in_codomains has_codomain_iff_arr codomain_unique by auto

    text\<open>
      A consequence of the following lemma is that the notion @{term "arr"} is redundant,
      given @{term "in_hom"}, @{term "dom"}, and @{term "cod"}.  However, I have retained it
      because I have not been able to find a set of usefully powerful simplification rules
      expressed only in terms of @{term "in_hom"} that does not result in looping in many
      situations.
\<close>

    lemma arr_iff_in_hom:
    shows "arr f \<longleftrightarrow> \<guillemotleft>f : dom f \<rightarrow> cod f\<guillemotright>"
      using cod_in_codomains dom_in_domains has_domain_iff_arr has_codomain_iff_arr in_hom_def
      by auto

    lemma in_homI [intro]:
    assumes "arr f" and "dom f = a" and "cod f = b"
    shows "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
      using assms cod_in_codomains dom_in_domains has_domain_iff_arr has_codomain_iff_arr
            in_hom_def
      by auto

    lemma in_homE [elim]:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
    and "arr f \<Longrightarrow> dom f = a \<Longrightarrow> cod f = b \<Longrightarrow> T"
    shows "T"
     using assms in_hom_def domains_char codomains_char has_domain_iff_arr
     by (metis empty_iff singleton_iff)

    text\<open>
      To obtain the ``only if'' direction in the next two results and in similar results later
      for composition and the application of functors and natural transformations,
      is the reason for assuming the existence of @{term null} as a special element of the
      arrow type, as opposed to, say, using option types to represent partiality.
      The presence of @{term null} allows us not only to make the ``upward'' inference that
      the domain of an arrow is again an arrow, but also to make the ``downward'' inference
      that if @{term "dom f"} is an arrow then so is @{term f}.  Similarly, we will be able
      to infer not only that if @{term f} and @{term g} are composable arrows then
      @{term "C g f"} is an arrow, but also that if @{term "C g f"} is an arrow then
      \<open>f\<close> and \<open>g\<close> are composable arrows.  These inferences allow most necessary
      facts about what terms denote arrows to be deduced automatically from minimal
      assumptions.  Typically all that is required is to assume or establish that certain
      terms denote arrows in particular homs at the point where those terms are first
      introduced, and then similar facts about related terms can be derived automatically.
      Without this feature, nearly every proof would involve many tedious additional steps
      to establish that each of the terms appearing in the proof (including all its subterms)
      in fact denote arrows.
\<close>

    lemma arr_dom_iff_arr:
    shows "arr (dom f) \<longleftrightarrow> arr f"
      using dom_def dom_in_domains has_domain_iff_arr self_domain_iff_ide domains_def
      by fastforce

    lemma arr_cod_iff_arr:
    shows "arr (cod f) \<longleftrightarrow> arr f"
      using cod_def cod_in_codomains has_codomain_iff_arr self_codomain_iff_ide codomains_def
      by fastforce

    lemma arr_dom [simp]:
    assumes "arr f"
    shows "arr (dom f)"
      using assms arr_dom_iff_arr by simp

    lemma arr_cod [simp]:
    assumes "arr f"
    shows "arr (cod f)"
      using assms arr_cod_iff_arr by simp

    lemma seqI [simp]:
    assumes "arr f" and "arr g" and "dom g = cod f"
    shows "seq g f"
    proof -
      have "ide (cod f) \<and> seq (cod f) f"
        using assms(1) has_codomain_iff_arr codomains_def cod_in_codomains ext by blast
      moreover have "ide (cod f) \<and> seq g (cod f)"
        using assms(2) assms(3) domains_def domains_char ext by fastforce
      ultimately show ?thesis
        using match_4 ide_def ext by metis
    qed

    lemma seqI' [intro]:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>g : b \<rightarrow> c\<guillemotright>"
    shows "seq g f"
      using assms by fastforce

    lemma compatible_iff_seq:
    shows "domains g \<inter> codomains f \<noteq> {} \<longleftrightarrow> seq g f"
    proof
      show "domains g \<inter> codomains f \<noteq> {} \<Longrightarrow> seq g f"
        using cod_in_codomains dom_in_domains empty_iff has_domain_iff_arr has_codomain_iff_arr
              domain_unique codomain_unique
        by (metis Int_emptyI seqI)
      show "seq g f \<Longrightarrow> domains g \<inter> codomains f \<noteq> {}"
      proof -
        assume gf: "seq g f"
        have 1: "cod f \<in> codomains f"
          using gf has_domain_iff_arr domains_comp cod_in_codomains codomains_char by blast
        have "ide (cod f) \<and> seq (cod f) f"
          using 1 codomains_def ext by auto
        hence "seq g (cod f)"
          using gf has_domain_iff_arr match_2 domains_null ide_def by metis
        thus ?thesis
          using domains_def 1 codomains_def by auto
      qed
    qed

    text\<open>
      The following is another example of a crucial ``downward'' rule that would not be possible
      without a reserved @{term null} value.
\<close>

    lemma seqE [elim]:
    assumes "seq g f"
    and "arr f \<Longrightarrow> arr g \<Longrightarrow> dom g = cod f \<Longrightarrow> T"
    shows "T"
      using assms cod_in_codomains compatible_iff_seq has_domain_iff_arr has_codomain_iff_arr
            domains_comp codomains_comp domains_char codomain_unique
      by (metis Int_emptyI singletonD)

    lemma comp_in_homI [intro]:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>g : b \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>g \<cdot> f : a \<rightarrow> c\<guillemotright>"
    proof
      show 1: "seq g f" using assms compatible_iff_seq by blast
      show "dom (g \<cdot> f) = a"
        using assms 1 domains_comp domains_char by blast
      show "cod (g \<cdot> f) = c"
        using assms 1 codomains_comp codomains_char by blast
    qed

    lemma comp_in_homE [elim]:
    assumes "\<guillemotleft>g \<cdot> f : a \<rightarrow> c\<guillemotright>"
    obtains b where "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>g : b \<rightarrow> c\<guillemotright>"
      using assms in_hom_def domains_comp codomains_comp
      by (metis arrI in_homI seqE)

    lemma comp_in_hom_simp [simp]:
    assumes "\<guillemotleft>f : a \<rightarrow> cod f\<guillemotright>" and "\<guillemotleft>g : cod f \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>g \<cdot> f : a \<rightarrow> c\<guillemotright>"
      using assms by auto

    lemma comp_in_hom_simp' [simp]:
    assumes "\<guillemotleft>f : a \<rightarrow> dom g\<guillemotright>" and "\<guillemotleft>g : dom g \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>g \<cdot> f : a \<rightarrow> c\<guillemotright>"
      using assms by auto

    lemma comp_arr_dom:
    assumes "arr f" and "dom f = a"
    shows "f \<cdot> a = f"
      using assms dom_in_domains has_domain_iff_arr domains_def ide_def by auto

    lemma comp_cod_arr:
    assumes "arr f" and "cod f = b"
    shows "b \<cdot> f = f"
      using assms cod_in_codomains has_codomain_iff_arr ide_def codomains_def by auto

    lemma ide_char:
    shows "ide a \<longleftrightarrow> arr a \<and> dom a = a \<and> cod a = a"
      using ide_in_hom by auto

    lemma ideD [simp]:
    assumes "ide a"
    shows "arr a" and "dom a = a" and "cod a = a"
      using assms ide_char by auto

    lemma ide_dom [simp]:
    assumes "arr f"
    shows "ide (dom f)"
      using assms dom_in_domains has_domain_iff_arr domains_def by auto

    lemma ide_cod [simp]:
    assumes "arr f"
    shows "ide (cod f)"
      using assms cod_in_codomains has_codomain_iff_arr codomains_def by auto

    lemma dom_eqI:
    assumes "ide a" and "seq f a"
    shows "dom f = a"
      using assms cod_in_codomains codomain_unique ide_char
      by (metis seqE)

    lemma cod_eqI:
    assumes "ide b" and "seq b f"
    shows "cod f = b"
      using assms dom_in_domains domain_unique ide_char
      by (metis seqE)

    lemma ide_char':
    shows "ide a \<longleftrightarrow> arr a \<and> (dom a = a \<or> cod a = a)"
    proof -
      have "arr a \<and> dom a = a \<Longrightarrow> ide a"
        using ide_dom [of a] by simp
      moreover have "arr a \<and> cod a = a \<Longrightarrow> ide a"
        using ide_cod [of a] by simp
      ultimately show ?thesis by fastforce
    qed

    lemma dom_dom [simp]:
    assumes "arr f"
    shows "dom (dom f) = dom f"
    proof -
      have "ide (dom f)" using assms by simp
      thus ?thesis by auto
    qed

    lemma cod_cod [simp]:
    assumes "arr f"
    shows "cod (cod f) = cod f"
    proof -
      have "ide (cod f)" using assms by simp
      thus ?thesis by auto
    qed

    lemma dom_cod [simp]:
    assumes "arr f"
    shows "dom (cod f) = cod f"
    proof -
      have "ide (cod f)" using assms by simp
      thus ?thesis by auto
    qed

    lemma cod_dom [simp]:
    assumes "arr f"
    shows "cod (dom f) = dom f"
    proof -
      have "ide (dom f)" using assms by simp
      thus ?thesis by auto
    qed

    lemma dom_comp [simp]:
    assumes "seq g f"
    shows "dom (g \<cdot> f) = dom f"
      using assms by (simp add: dom_def domains_comp)

    lemma cod_comp [simp]:
    assumes "seq g f"
    shows "cod (g \<cdot> f) = cod g"
      using assms by (simp add: cod_def codomains_comp)

    lemma comp_ide_self [simp]:
    assumes "ide a"
    shows "a \<cdot> a = a"
      using assms comp_arr_ide arrI by auto

    lemma ide_compE [elim]:
    assumes "ide (g \<cdot> f)"
    and "seq g f \<Longrightarrow> seq f g \<Longrightarrow> g \<cdot> f = dom f \<Longrightarrow> g \<cdot> f = cod g \<Longrightarrow> T"
    shows "T"
    proof -
      have "g \<cdot> f = dom f \<and> g \<cdot> f = cod g"
        using assms by (metis dom_comp cod_comp ide_char)
      thus ?thesis
        using assms ide_in_hom using seqI' by blast
    qed

    text \<open>
      The next two results are sometimes useful for performing manipulations at the
      head of a chain of composed arrows.  I have adopted the convention that such
      chains are canonically represented in right-associated form.  This makes it
      easy to perform manipulations at the ``tail'' of a chain, but more difficult
      to perform them at the ``head''.  These results take care of the rote manipulations
      using associativity that are needed to either permute or combine arrows at the
      head of a chain.
\<close>

    lemma comp_permute:
    assumes "f \<cdot> g = k \<cdot> l" and "seq f g" and "seq g h"
    shows "f \<cdot> g \<cdot> h = k \<cdot> l \<cdot> h"
      using assms by (metis comp_assoc)

    lemma comp_reduce:
    assumes "f \<cdot> g = k" and "seq f g" and "seq g h"
    shows "f \<cdot> g \<cdot> h = k \<cdot> h"
      using assms comp_assoc by auto

    text\<open>
      Here we define some common configurations of arrows.
      These are defined as abbreviations, because we want all ``diagrammatic'' assumptions
      in a theorem to reduce readily to a conjunction of assertions of the basic forms
      @{term "arr f"}, @{term "dom f = X"}, @{term "cod f = Y"}, and @{term "in_hom f a b"}.
\<close>

    abbreviation endo
    where "endo f \<equiv> seq f f"
     
    abbreviation antipar
    where "antipar f g \<equiv> seq g f \<and> seq f g"

    abbreviation span
    where "span f g \<equiv> arr f \<and> arr g \<and> dom f = dom g"

    abbreviation cospan
    where "cospan f g \<equiv> arr f \<and> arr g \<and> cod f = cod g"

    abbreviation par
    where "par f g \<equiv> arr f \<and> arr g \<and> dom f = dom g \<and> cod f = cod g"

  end

  section "Classical Categories"

  text\<open>
    In this section we define a secondary axiomatization of categories, \<open>classical_category\<close>,
    which is a more traditional one, except that in view of the totality of functions in HOL
    we need to introduce predicates \<open>Obj\<close> and \<open>Arr\<close> that characterize the bona fide
    objects and arrows among the elements of their respective types.
    A category defined this way is not ``extensional'', in the sense that there
    will in general be categories with the same sets of objects and arrows,
    such that \<open>Dom\<close>, \<open>Cod\<close>, \<open>Id\<close>, and \<open>Comp\<close> agree on these
    objects and arrows, but they do not necessarily agree on other values of the corresponding
    types.

    We show below that an interpretation of the \<open>category\<close> induces an interpretation
    of the \<open>classical_category\<close> locale.
    Conversely, we show that if \<open>Obj\<close>, \<open>Arr\<close>, \<open>Dom\<close>, \<open>Cod\<close>,
    \<open>Id\<close>, and \<open>Comp\<close> comprise an interpretation of \<open>classical_category\<close>,
    then we can define from them a partial composition that interprets the \<open>category\<close> locale.
    Moreover, the predicate derived \<open>arr\<close> derived from this partial composition agrees
    with the originally given predicate \<open>Arr\<close>, the notions \<open>dom\<close>, \<open>cod\<close>,
    and \<open>comp\<close> derived from the partial composition agree with the originally given
    \<open>Dom\<close>, \<open>Cod\<close>, and \<open>Comp\<close> on arguments that satisfy \<open>arr\<close>,
    and the identities derived from the partial composition are in bijective correspondence with
    the elements that satisfy the originally given predicate \<open>Obj\<close>.

    In some cases, rather than defining a construction on categories directly
    in terms of the partial-composition-based axioms, it can be simpler to
    define the construction in classical terms in a convenient way, and then
    extract a partial composition via the construction given here.
\<close>

  locale classical_category =
  fixes Obj :: "'obj \<Rightarrow> bool"
  and Arr :: "'arr \<Rightarrow> bool"
  and Dom :: "'arr \<Rightarrow> 'obj"
  and Cod :: "'arr \<Rightarrow> 'obj"
  and Id :: "'obj \<Rightarrow> 'arr"
  and Comp :: "'arr \<Rightarrow> 'arr \<Rightarrow> 'arr"
  assumes Obj_Dom: "Arr f \<Longrightarrow> Obj (Dom f)"
  and Obj_Cod: "Arr f \<Longrightarrow> Obj (Cod f)"
  and Arr_Id [simp]: "Obj a \<Longrightarrow> Arr (Id a)"
  and Dom_Id [simp]: "Obj a \<Longrightarrow> Dom (Id a) = a"
  and Cod_Id [simp]: "Obj a \<Longrightarrow> Cod (Id a) = a"
  and Arr_Comp [simp]: "\<lbrakk> Arr f; Arr g; Cod f = Dom g \<rbrakk> \<Longrightarrow> Arr (Comp g f)"
  and Comp_assoc [simp]: "\<lbrakk> Arr f; Arr g; Arr h; Cod f = Dom g; Cod g = Dom h \<rbrakk>
                                              \<Longrightarrow> Comp (Comp h g) f = Comp h (Comp g f)"
  and Dom_Comp [simp]: "\<lbrakk> Arr f; Arr g; Cod f = Dom g \<rbrakk> \<Longrightarrow> Dom (Comp g f) = Dom f"
  and Cod_Comp [simp]: "\<lbrakk> Arr f; Arr g; Cod f = Dom g \<rbrakk> \<Longrightarrow> Cod (Comp g f) = Cod g"
  and Comp_Arr_Id_Dom [simp]: "Arr f \<Longrightarrow> Comp f (Id (Dom f)) = f"
  and Comp_Id_Cod_Arr [simp]: "Arr f \<Longrightarrow> Comp (Id (Cod f)) f = f"
  begin

    abbreviation Seq
    where "Seq g f \<equiv> (Arr f \<and> Arr g \<and> Cod f = Dom g)"

    text\<open>
      Because @{term Arr} might be the universal predicate for type @{typ 'arr},
      it is necessary to pass to type @{typ "'arr option"} in order to have a value
      available to serve as \<open>null\<close>.
\<close>

    definition comp :: "'arr option \<Rightarrow> 'arr option \<Rightarrow> 'arr option"
    where "comp g f = (if f \<noteq> None \<and> g \<noteq> None \<and> Seq (the g) (the f)
                       then Some (Comp (the g) (the f)) else None)"

    interpretation C: partial_magma comp
    proof
      show "\<exists>!n. \<forall>f. comp n f = n \<and> comp f n = n"
      proof
        show "\<forall>f. comp None f = None \<and> comp f None = None"
          using comp_def by auto
        show "\<And>n. \<forall>f. comp n f = n \<and> comp f n = n \<Longrightarrow> n = None"
          by (metis comp_def)
      qed
    qed

    lemma null_char:
    shows "C.null = None"
    proof -
      let ?P = "\<lambda>n. \<forall>f. comp n f = n \<and> comp f n = n"
      have "?P None" using comp_def by auto
      hence "(THE n. ?P n) = None"
        using C.ex_un_null the1_equality [of ?P] by simp
      thus ?thesis using C.null_def by auto
    qed

    lemma ide_Some_Id:
    assumes "Obj A"
    shows "C.ide (Some (Id A))"
    proof -
      have "\<And>f. comp f (Some (Id A)) \<noteq> C.null \<Longrightarrow> comp f (Some (Id A)) = f"
        using assms comp_def null_char by auto
      moreover have "\<And>f. comp (Some (Id A)) f \<noteq> C.null \<Longrightarrow> comp (Some (Id A)) f = f"
        using assms comp_def null_char by auto
      ultimately show ?thesis
        using assms C.ide_def comp_def null_char by auto
    qed

    lemma has_domain_char:
    shows "C.domains f \<noteq> {} \<longleftrightarrow> f \<noteq> None \<and> Arr (the f)"
    proof
      assume f: "C.domains f \<noteq> {}"
      show "f \<noteq> None \<and> Arr (the f)"
        using f Collect_empty_eq comp_def null_char C.domains_def by fastforce
      next
      assume f: "f \<noteq> None \<and> Arr (the f)"
      have "Some (Id (Dom (the f))) \<in> C.domains f"
        using f C.domains_def Obj_Dom comp_def null_char ide_Some_Id by auto
      thus "C.domains f \<noteq> {}" by blast
    qed

    lemma has_codomain_char:
    shows "C.codomains f \<noteq> {} \<longleftrightarrow> f \<noteq> None \<and> Arr (the f)"
    proof
      assume f: "C.codomains f \<noteq> {}"
      show "f \<noteq> None \<and> Arr (the f)"
         using f Collect_empty_eq comp_def null_char C.codomains_def by fastforce
      next
      assume f: "f \<noteq> None \<and> Arr (the f)"
      have "Some (Id (Cod (the f))) \<in> C.codomains f"
        using f C.codomains_def Obj_Cod comp_def null_char ide_Some_Id by auto
      thus "C.codomains f \<noteq> {}" by blast
    qed

    lemma arr_char:
    shows "C.arr f \<longleftrightarrow> f \<noteq> None \<and> Arr (the f)"
      using has_domain_char has_codomain_char
      by (simp add: C.arr_def)

    lemma comp_simp:
    assumes "comp g f \<noteq> C.null"
    shows "comp g f = Some (Comp (the g) (the f))"
      using assms by (metis comp_def null_char)

    interpretation C: category comp
    proof
      fix f g h
      show 1: "C.domains f \<noteq> {} \<longleftrightarrow> C.codomains f \<noteq> {}"
      proof
        assume f: "C.domains f \<noteq> {}"
        obtain a where a: "a \<in> C.domains f" using f by blast
        have "Some (Id (Cod (the f))) \<in> C.codomains f"
          using a f C.codomains_def Obj_Cod has_domain_char comp_def null_char ide_Some_Id
          by auto
        thus "C.codomains f \<noteq> {}" by blast
        next
        assume f: "C.codomains f \<noteq> {}"
        obtain b where b: "b \<in> C.codomains f" using f by blast
        have "Some (Id (Dom (the f))) \<in> C.domains f"
          using b f C.domains_def Obj_Dom has_codomain_char comp_def null_char ide_Some_Id
          by auto
        thus "C.domains f \<noteq> {}" by blast
      qed
      show "comp g f \<noteq> C.null \<Longrightarrow> C.seq g f"
        using has_codomain_char null_char comp_def C.arr_def C.not_arr_null by auto
      show "C.seq h g \<Longrightarrow> C.seq (comp h g) f \<Longrightarrow> C.seq g f"
        by (metis Arr_Comp C.arr_def Dom_Comp has_codomain_char comp_def option.sel
                  option.simps(3))
      show "C.seq h (comp g f) \<Longrightarrow> C.seq g f \<Longrightarrow> C.seq h g"
        by (metis Arr_Comp C.arr_def Cod_Comp has_domain_char comp_def option.sel
                  option.simps(3))
      show "C.seq g f \<Longrightarrow> C.seq h g \<Longrightarrow> C.seq (comp h g) f"
        by (metis Arr_Comp C.arr_def Dom_Comp has_codomain_char comp_def option.sel
                  option.simps(3))
      thus "C.seq g f \<Longrightarrow> C.seq h g \<Longrightarrow> comp (comp h g) f = comp h (comp g f)"
        by (metis (no_types, lifting) C.arr_def Cod_Comp Comp_assoc has_domain_char
            has_codomain_char comp_def option.sel)
    qed

    theorem induces_category:
    shows "category comp" ..

    text\<open>
      The arrows of the classical category are in bijective correspondence with the
      arrows of the category defined by @{term comp}, and the originally given
      @{term Dom}, @{term Cod}, and @{term Comp} coincide along this bijection with
      @{term C.dom}, @{term C.cod}, and @{term comp}.
\<close>

    lemma bij_betw_Arr_arr:
    shows "bij_betw Some (Collect Arr) (Collect C.arr)"
      using C.has_codomain_iff_arr has_codomain_char C.not_arr_null null_char
      apply (intro bij_betwI) apply auto
       apply fastforce
      by (metis option.collapse)

    lemma dom_char:
    shows "C.dom f = (if C.arr f then Some (Id (Dom (the f))) else None)"
    proof (cases "C.arr f")
      assume f: "C.arr f"
      hence "C.dom f = Some (Id (Dom (the f)))"
        using Obj_Dom arr_char ide_Some_Id arr_char comp_def
        by (intro C.dom_eqI, auto)
      thus ?thesis using f by auto
      next
      assume "\<not>C.arr f"
      thus ?thesis
        using C.dom_def null_char C.has_domain_iff_arr by metis
    qed

    lemma cod_char:
    shows "C.cod f = (if C.arr f then Some (Id (Cod (the f))) else None)"
    proof (cases "C.arr f")
      assume f: "C.arr f"
      hence "C.cod f = Some (Id (Cod (the f)))"
        using dom_char C.has_domain_iff_arr has_domain_char comp_def
        by (metis C.comp_cod_arr C.dom_cod)
      thus ?thesis using f by auto
      next
      assume "\<not>C.arr f"
      thus ?thesis
        using C.cod_def null_char C.has_codomain_iff_arr by metis
    qed

    lemma comp_char:
    shows "comp g f = (if f \<noteq> None \<and> g \<noteq> None \<and> Seq (the g) (the f)
                       then Some (Comp (the g) (the f)) else None)"
      using comp_def by simp

    lemma ide_char:
    shows "C.ide a \<longleftrightarrow> Arr (the a) \<and> a = Some (Id (Dom (the a)))"
      using C.ide_dom arr_char dom_char C.ide_in_hom by fastforce

    text\<open>
      The objects of the classical category are in bijective correspondence with
      the identities of the category defined by comp.
\<close>

    lemma bij_betw_Obj_ide:
    shows "bij_betw (Some o Id) (Collect Obj) (Collect C.ide)"
      using ide_char Obj_Dom by (intro bij_betwI, auto)

  end

  sublocale classical_category \<subseteq> category comp
    using induces_category by auto

  text\<open>
    A category defined using the nonstandard, partial-composition-based axiomatization
    admits an interpretation of the classical axioms, and the composition derived
    from this interpretation coincides with the originally given one.
\<close>

  context category
  begin

    theorem is_classical_category:
    shows "classical_category ide arr dom cod dom C"
      using comp_arr_dom comp_cod_arr comp_assoc by (unfold_locales, auto)

    interpretation CC: classical_category ide arr dom cod dom C
      using is_classical_category by auto

    lemma comp_agreement:
    assumes "seq g f"
    shows "g \<cdot> f = the (CC.comp (Some g) (Some f))"
      using assms CC.comp_def seqE by fastforce

  end

end
