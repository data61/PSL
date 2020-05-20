(*  Title:       ConcreteCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Concrete Categories"

text \<open>
  In this section we define a locale \<open>concrete_category\<close>, which provides a uniform
  (and more traditional) way to construct a category from specified sets of objects and arrows,
  with specified identity objects and composition of arrows.
  We prove that the identities and arrows of the constructed category are appropriately
  in bijective correspondence with the given sets and that domains, codomains, and composition
  in the constructed category are as expected according to this correspondence.
  In the later theory \<open>Functor\<close>, once we have defined functors and isomorphisms of categories,
  we will show a stronger property of this construction: if \<open>C\<close> is any category,
  then \<open>C\<close> is isomorphic to the concrete category formed from it in the obvious way by taking
  the identities of \<open>C\<close> as objects, the set of arrows of \<open>C\<close> as arrows, the identities of
  \<open>C\<close> as identity objects, and defining composition of arrows using the composition of \<open>C\<close>.
  Thus no information about \<open>C\<close> is lost by extracting its objects, arrows, identities, and
  composition and rebuilding it as a concrete category.
  We note, however, that we do not assume that the composition function given as parameter
  to the concrete category construction is ``extensional'', so in general it will contain
  incidental information about composition of non-composable arrows, and this information
  is not preserved by the concrete category construction.
\<close>

theory ConcreteCategory
imports Category
begin

  locale concrete_category =
    fixes Obj :: "'o set"
    and Hom :: "'o \<Rightarrow> 'o \<Rightarrow> 'a set"
    and Id :: "'o \<Rightarrow> 'a"
    and Comp :: "'o \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>'a"
    assumes Id_in_Hom: "A \<in> Obj \<Longrightarrow> Id A \<in> Hom A A"
    and Comp_in_Hom: "\<lbrakk> A \<in> Obj; B \<in> Obj; C \<in> Obj; f \<in> Hom A B; g \<in> Hom B C \<rbrakk>
                         \<Longrightarrow> Comp C B A g f \<in> Hom A C"
    and Comp_Hom_Id: "\<lbrakk> A \<in> Obj; f \<in> Hom A B \<rbrakk> \<Longrightarrow> Comp B A A f (Id A) = f"
    and Comp_Id_Hom: "\<lbrakk> B \<in> Obj; f \<in> Hom A B \<rbrakk> \<Longrightarrow> Comp B B A (Id B) f = f"
    and Comp_assoc: "\<lbrakk> A \<in> Obj; B \<in> Obj; C \<in> Obj; D \<in> Obj;
                       f \<in> Hom A B; g \<in> Hom B C; h \<in> Hom C D \<rbrakk> \<Longrightarrow>
                        Comp D C A h (Comp C B A g f) = Comp D B A (Comp D C B h g) f"
  begin

    datatype ('oo, 'aa) arr =
      Null
    | MkArr 'oo 'oo 'aa

    abbreviation MkIde :: "'o \<Rightarrow> ('o, 'a) arr"
    where "MkIde A \<equiv> MkArr A A (Id A)"

    fun Dom :: "('o, 'a) arr \<Rightarrow> 'o"
    where "Dom (MkArr A _ _) = A"
        | "Dom _ = undefined"

    fun Cod
    where "Cod (MkArr _ B _) = B"
        | "Cod _ = undefined"

    fun Map
    where "Map (MkArr _ _ F) = F"
        | "Map _ = undefined"

    abbreviation Arr
    where "Arr f \<equiv> f \<noteq> Null \<and> Dom f \<in> Obj \<and> Cod f \<in> Obj \<and> Map f \<in> Hom (Dom f) (Cod f)"

    abbreviation Ide
    where "Ide a \<equiv> a \<noteq> Null \<and> Dom a \<in> Obj \<and> Cod a = Dom a \<and> Map a = Id (Dom a)"

    (*
     * Here we use COMP in order that uses of this locale can declare themselves as
     * sublocales and then define the abbreviation comp \<equiv> COMP.
     *)
    definition COMP :: "('o, 'a) arr comp"
    where "COMP g f \<equiv> if Arr f \<and> Arr g \<and> Dom g = Cod f then
                         MkArr (Dom f) (Cod g) (Comp (Cod g) (Dom g) (Dom f) (Map g) (Map f))
                      else
                         Null"

    interpretation partial_magma COMP
      using COMP_def by (unfold_locales, metis)

    lemma null_char:
    shows "null = Null"
    proof -
      let ?P = "\<lambda>n. \<forall>f. COMP n f = n \<and> COMP f n = n"
      have "Null = null"
        using COMP_def null_def the1_equality [of ?P] by metis
      thus ?thesis by simp
    qed

    lemma ide_char:
    shows "ide f \<longleftrightarrow> Ide f"
    proof
      assume f: "Ide f"
      show "ide f"
      proof -
        have "COMP f f \<noteq> null"
          using f COMP_def null_char Id_in_Hom by auto
        moreover have "\<forall>g. (COMP g f \<noteq> null \<longrightarrow> COMP g f = g) \<and>
                           (COMP f g \<noteq> null \<longrightarrow> COMP f g = g)"
        proof (intro allI conjI)
          fix g
          show "COMP g f \<noteq> null \<longrightarrow> COMP g f = g"
            using f COMP_def null_char Comp_Hom_Id Id_in_Hom
            by (cases g, auto)
          show "COMP f g \<noteq> null \<longrightarrow> COMP f g = g"
            using f COMP_def null_char Comp_Id_Hom Id_in_Hom
            by (cases g, auto)
        qed
        ultimately show ?thesis
          using ide_def by blast
      qed
      next
      assume f: "ide f"
      have 1: "Arr f \<and> Dom f = Cod f"
        using f ide_def COMP_def null_char by metis
      moreover have "Map f = Id (Dom f)"
      proof -
        let ?g = "MkIde (Dom f)"
        have g: "Arr f \<and> Arr ?g \<and> Dom ?g = Cod f"
          using 1 Id_in_Hom
          by (intro conjI, simp_all)
        have "COMP ?g f = MkArr (Dom f) (Dom f) (Map f)"
          using g COMP_def Comp_Id_Hom by auto
        moreover have "COMP ?g f = ?g"
        proof -
          have "COMP ?g f \<noteq> null"
            using g 1 COMP_def null_char by simp
          thus ?thesis
            using f ide_def by blast
        qed
        ultimately show ?thesis by simp
      qed
      ultimately show "Ide f" by auto
    qed

    lemma ide_MkIde [simp]:
    assumes "A \<in> Obj"
    shows "ide (MkIde A)"
      using assms ide_char Id_in_Hom by simp

    lemma in_domains_char:
    shows "a \<in> domains f \<longleftrightarrow> Arr f \<and> a = MkIde (Dom f)"
    proof
      assume a: "a \<in> domains f"
      have "Ide a"
        using a domains_def ide_char COMP_def null_char by auto
      moreover have "Arr f \<and> Dom f = Cod a"
      proof -
        have "COMP f a \<noteq> null"
          using a domains_def by simp
        thus ?thesis
          using a domains_def COMP_def [of f a] null_char by metis
      qed
      ultimately show "Arr f \<and> a = MkIde (Dom f)"
        by (cases a, auto)
      next
      assume a: "Arr f \<and> a = MkIde (Dom f)"
      show "a \<in> domains f"
        using a Id_in_Hom COMP_def null_char domains_def by auto
    qed

    lemma in_codomains_char:
    shows "b \<in> codomains f \<longleftrightarrow> Arr f \<and> b = MkIde (Cod f)"
    proof
      assume b: "b \<in> codomains f"
      have "Ide b"
        using b codomains_def ide_char COMP_def null_char by auto
      moreover have "Arr f \<and> Dom b = Cod f"
      proof -
        have "COMP b f \<noteq> null"
          using b codomains_def by simp
        thus ?thesis
          using b codomains_def COMP_def [of b f] null_char by metis
      qed
      ultimately show "Arr f \<and> b = MkIde (Cod f)"
        by (cases b, auto)
      next
      assume b: "Arr f \<and> b = MkIde (Cod f)"
      show "b \<in> codomains f"
        using b Id_in_Hom COMP_def null_char codomains_def by auto
    qed

    lemma arr_char:
    shows "arr f \<longleftrightarrow> Arr f"
      using arr_def in_domains_char in_codomains_char by auto

    lemma arrI:
    assumes "f \<noteq> Null" and "Dom f \<in> Obj" "Cod f \<in> Obj" "Map f \<in> Hom (Dom f) (Cod f)"
    shows "arr f"
      using assms arr_char by blast

    lemma arrE:
    assumes "arr f"
    and "\<lbrakk> f \<noteq> Null; Dom f \<in> Obj; Cod f \<in> Obj; Map f \<in> Hom (Dom f) (Cod f) \<rbrakk> \<Longrightarrow> T"
    shows T
      using assms arr_char by simp

    lemma arr_MkArr [simp]:
    assumes "A \<in> Obj" and "B \<in> Obj" and "f \<in> Hom A B"
    shows "arr (MkArr A B f)"
      using assms arr_char by simp

    lemma MkArr_Map:
    assumes "arr f"
    shows "MkArr (Dom f) (Cod f) (Map f) = f"
      using assms arr_char by (cases f, auto)

    lemma Arr_comp:
    assumes "arr f" and "arr g" and "Dom g = Cod f"
    shows "Arr (COMP g f)"
      unfolding COMP_def
      using assms arr_char Comp_in_Hom by simp

    lemma Dom_comp [simp]:
    assumes "arr f" and "arr g" and "Dom g = Cod f"
    shows "Dom (COMP g f) = Dom f"
      unfolding COMP_def
      using assms arr_char by simp

    lemma Cod_comp [simp]:
    assumes "arr f" and "arr g" and "Dom g = Cod f"
    shows "Cod (COMP g f) = Cod g"
      unfolding COMP_def
      using assms arr_char by simp

    lemma Map_comp [simp]:
    assumes "arr f" and "arr g" and "Dom g = Cod f"
    shows "Map (COMP g f) = Comp (Cod g) (Dom g) (Dom f) (Map g) (Map f)"
      unfolding COMP_def
      using assms arr_char by simp

    lemma seq_char:
    shows "seq g f \<longleftrightarrow> arr f \<and> arr g \<and> Dom g = Cod f"
      using arr_char not_arr_null null_char COMP_def Arr_comp by metis

    interpretation category COMP
    proof
      show "\<And>g f. COMP g f \<noteq> null \<Longrightarrow> seq g f"
        using arr_char COMP_def null_char Comp_in_Hom by auto
      show 1: "\<And>f. (domains f \<noteq> {}) = (codomains f \<noteq> {})"
        using in_domains_char in_codomains_char by auto
      show "\<And>f g h. seq h g \<Longrightarrow> seq (COMP h g) f \<Longrightarrow> seq g f"
        by (auto simp add: seq_char)
      show "\<And>f g h. seq h (COMP g f) \<Longrightarrow> seq g f \<Longrightarrow> seq h g"
        using seq_char COMP_def Comp_in_Hom by (metis Cod_comp)
      show "\<And>f g h. seq g f \<Longrightarrow> seq h g \<Longrightarrow> seq (COMP h g) f"
        using Comp_in_Hom
        by (auto simp add: COMP_def seq_char)
      show "\<And>g f h. seq g f \<Longrightarrow> seq h g \<Longrightarrow> COMP (COMP h g) f = COMP h (COMP g f)"
        using seq_char COMP_def Comp_assoc Comp_in_Hom Dom_comp Cod_comp Map_comp
        by auto
    qed

    proposition is_category:
    shows "category COMP"
      ..

    text \<open>
      Functions \<open>Dom\<close>, \<open>Cod\<close>, and \<open>Map\<close> establish a correspondence between the
      arrows of the constructed category and the elements of the originally given
      parameters \<open>Obj\<close> and \<open>Hom\<close>.
    \<close>

    lemma Dom_in_Obj:
    assumes "arr f"
    shows "Dom f \<in> Obj"
      using assms arr_char by simp

    lemma Cod_in_Obj:
    assumes "arr f"
    shows "Cod f \<in> Obj"
      using assms arr_char by simp

    lemma Map_in_Hom:
    assumes "arr f"
    shows "Map f \<in> Hom (Dom f) (Cod f)"
      using assms arr_char by simp

    lemma MkArr_in_hom:
    assumes "A \<in> Obj" and "B \<in> Obj" and "f \<in> Hom A B"
    shows "in_hom (MkArr A B f) (MkIde A) (MkIde B)"
      using assms arr_char ide_MkIde
      by (simp add: in_codomains_char in_domains_char in_hom_def)

    text \<open>
      The next few results show that domains, codomains, and composition in the constructed
      category are as expected according to the just-given correspondence.
    \<close>

    lemma dom_char:
    shows "dom f = (if arr f then MkIde (Dom f) else null)"
      using dom_def in_domains_char dom_in_domains has_domain_iff_arr by auto

    lemma cod_char:
    shows "cod f = (if arr f then MkIde (Cod f) else null)"
      using cod_def in_codomains_char cod_in_codomains has_codomain_iff_arr by auto

    lemma comp_char:
    shows "COMP g f = (if seq g f then
                         MkArr (Dom f) (Cod g) (Comp (Cod g) (Dom g) (Dom f) (Map g) (Map f))
                       else
                         null)"
      using COMP_def seq_char arr_char null_char by auto

    lemma in_hom_char:
    shows "in_hom f a b \<longleftrightarrow> arr f \<and> ide a \<and> ide b \<and> Dom f = Dom a \<and> Cod f = Dom b"
    proof
      show "in_hom f a b \<Longrightarrow> arr f \<and> ide a \<and> ide b \<and> Dom f = Dom a \<and> Cod f = Dom b"
        using arr_char dom_char cod_char by auto
      show "arr f \<and> ide a \<and> ide b \<and> Dom f = Dom a \<and> Cod f = Dom b \<Longrightarrow> in_hom f a b"
        using arr_char dom_char cod_char ide_char Id_in_Hom MkArr_Map in_homI by metis
    qed

    lemma Dom_dom [simp]:
    assumes "arr f"
    shows "Dom (dom f) = Dom f"
      using assms MkArr_Map dom_char by simp

    lemma Cod_dom [simp]:
    assumes "arr f"
    shows "Cod (dom f) = Dom f"
      using assms MkArr_Map dom_char by simp

    lemma Dom_cod [simp]:
    assumes "arr f"
    shows "Dom (cod f) = Cod f"
      using assms MkArr_Map cod_char by simp

    lemma Cod_cod [simp]:
    assumes "arr f"
    shows "Cod (cod f) = Cod f"
      using assms MkArr_Map cod_char by simp

    lemma Map_dom [simp]:
    assumes "arr f"
    shows "Map (dom f) = Id (Dom f)"
      using assms MkArr_Map dom_char by simp

    lemma Map_cod [simp]:
    assumes "arr f"
    shows "Map (cod f) = Id (Cod f)"
      using assms MkArr_Map cod_char by simp

    lemma Map_ide:
    assumes "ide a"
    shows "Map a = Id (Dom a)" and "Map a = Id (Cod a)"
      using assms ide_char dom_char [of a] Map_dom Map_cod ideD(1) by metis+

    (*
     * TODO: The next two ought to be simps, but they cause looping when they find themselves
     * in combination with dom_char and cod_char.
     *)
    lemma MkIde_Dom:
    assumes "arr a"
    shows "MkIde (Dom a) = dom a"
      using assms arr_char dom_char by (cases a, auto)

    lemma MkIde_Cod:
    assumes "arr a"
    shows "MkIde (Cod a) = cod a"
      using assms arr_char cod_char by (cases a, auto)

    lemma MkIde_Dom' [simp]:
    assumes "ide a"
    shows "MkIde (Dom a) = a"
      using assms MkIde_Dom by simp

    lemma MkIde_Cod' [simp]:
    assumes "ide a"
    shows "MkIde (Cod a) = a"
      using assms MkIde_Cod by simp

    lemma dom_MkArr [simp]:
    assumes "arr (MkArr A B F)"
    shows "dom (MkArr A B F) = MkIde A"
      using assms dom_char by simp

    lemma cod_MkArr [simp]:
    assumes "arr (MkArr A B F)"
    shows "cod (MkArr A B F) = MkIde B"
      using assms cod_char by simp

    lemma comp_MkArr [simp]:
    assumes "arr (MkArr A B F)" and "arr (MkArr B C G)"
    shows "COMP (MkArr B C G) (MkArr A B F) = MkArr A C (Comp C B A G F)"
      using assms comp_char [of "MkArr B C G" "MkArr A B F"] by simp

    text \<open>
      The set \<open>Obj\<close> of ``objects'' given as a parameter is in bijective correspondence
      (via function \<open>MkIde\<close>) with the set of identities of the resulting category.
    \<close>

    proposition bij_betw_ide_Obj:
    shows "MkIde \<in> Obj \<rightarrow> Collect ide"
    and "Dom \<in> Collect ide \<rightarrow> Obj"
    and "A \<in> Obj \<Longrightarrow> Dom (MkIde A) = A"
    and "a \<in> Collect ide \<Longrightarrow> MkIde (Dom a) = a"
    and "bij_betw Dom (Collect ide) Obj"
    proof -
      show "MkIde \<in> Obj \<rightarrow> Collect ide"
        using ide_MkIde by simp
      moreover show "Dom \<in> Collect ide \<rightarrow> Obj"
        using arr_char ideD(1) by simp
      moreover show "\<And>A. A \<in> Obj \<Longrightarrow> Dom (MkIde A) = A"
        by simp
      moreover show "\<And>a. a \<in> Collect ide \<Longrightarrow> MkIde (Dom a) = a"
        using MkIde_Dom by simp
      ultimately show "bij_betw Dom (Collect ide) Obj"
        using bij_betwI by blast
    qed

    text \<open>
      For each pair of identities \<open>a\<close> and \<open>b\<close>, the set \<open>Hom (Dom a) (Dom b)\<close> is in
      bijective correspondence (via function \<open>MkArr (Dom a) (Dom b)\<close>) with the
      ``hom-set'' \<open>hom a b\<close> of the resulting category.
    \<close>

    proposition bij_betw_hom_Hom:
    assumes "ide a" and "ide b"
    shows "Map \<in> hom a b \<rightarrow> Hom (Dom a) (Dom b)"
    and "MkArr (Dom a) (Dom b) \<in> Hom (Dom a) (Dom b) \<rightarrow> hom a b"
    and "\<And>f. f \<in> hom a b \<Longrightarrow> MkArr (Dom a) (Dom b) (Map f) = f"
    and "\<And>F. F \<in> Hom (Dom a) (Dom b) \<Longrightarrow> Map (MkArr (Dom a) (Dom b) F) = F"
    and "bij_betw Map (hom a b) (Hom (Dom a) (Dom b))"
    proof -
      show "Map \<in> hom a b \<rightarrow> Hom (Dom a) (Dom b)"
        using Map_in_Hom cod_char dom_char in_hom_char by fastforce
      moreover show "MkArr (Dom a) (Dom b) \<in> Hom (Dom a) (Dom b) \<rightarrow> hom a b"
        using assms Dom_in_Obj MkArr_in_hom [of "Dom a" "Dom b"] by simp
      moreover show "\<And>f. f \<in> hom a b \<Longrightarrow> MkArr (Dom a) (Dom b) (Map f) = f"
        using MkArr_Map by auto
      moreover show "\<And>F. F \<in> Hom (Dom a) (Dom b) \<Longrightarrow> Map (MkArr (Dom a) (Dom b) F) = F"
        by simp
      ultimately show "bij_betw Map (hom a b) (Hom (Dom a) (Dom b))"
        using bij_betwI by blast
    qed

    lemma arr_eqI:
    assumes "arr t" and "arr t'" and "Dom t = Dom t'" and "Cod t = Cod t'" and "Map t = Map t'"
    shows "t = t'"
      using assms MkArr_Map by metis

  end

  sublocale concrete_category \<subseteq> category COMP
    using is_category by auto

end
