(*  Title:       SetCat
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter SetCat

theory SetCat
imports SetCategory AbstractedCategory
begin

  text\<open>
    This theory proves the consistency of the \<open>set_category\<close> locale by giving
    a particular concrete construction of an interpretation for it.  Although the
    construction used here is probably the first one that would come to mind
    (arrows are defined as triples @{term "(F, (A, B))"} where @{term A} and @{term B}
    are sets and @{term F} is an extensional function from @{term A} to @{term B}),
    there is nothing particularly unique or special about it.
    Because of this, we don't want clients of this theory to have implicit dependencies
    on the specific details of the construction we use.  We therefore go to some
    trouble to hide these details behind an opaque arrow type and export only the
    definitions and facts that are made explicit in the \<open>set_category\<close> locale.
\<close>

  text\<open>
    We first define a locale \<open>setcat\<close> that gives the details of the particular
    construction of ``the category of @{typ 'a}-sets and functions between them''.
    We use a locale so that we can later interpret it once in a local context,
    prove the main fact, which is that we thereby obtain an interpretation of the
    \<open>set_category\<close> locale, and leave no other permanent vestiges of it
    in this theory.
\<close>

  locale setcat
  begin

    text\<open>
      We represent an arrow as a tuple @{term "(F, (A, B))"}, where @{term A} and
      @{term B} are @{typ 'a}-sets and @{term "(F :: 'a \<Rightarrow> 'a) \<in> extensional A \<inter> (A \<rightarrow> B)"}.
      Since in HOL every type is inhabited, we can avoid using option types here
      by letting @{term "(\<lambda>x. x, ({undefined}, {}))"} serve as the null element of
      the arrow type.  This term can never denote an arrow, because the set
      @{term "{undefined} \<rightarrow> {}"} is empty at any type.
\<close>

    type_synonym 'a arr = "('a \<Rightarrow> 'a) * 'a set * 'a set"

    abbreviation Null :: "'a arr"
    where "Null \<equiv> (\<lambda>x. x, ({undefined}, {}))"
  
    abbreviation MkArr :: "'a set => 'a set => ('a \<Rightarrow> 'a) \<Rightarrow> 'a arr"
    where "MkArr A B F \<equiv> (restrict F A, (A, B))"
  
    abbreviation Dom :: "'a arr \<Rightarrow> 'a set"
    where "Dom f \<equiv> fst (snd f)"

    abbreviation Cod :: "'a arr \<Rightarrow> 'a set"
    where "Cod f \<equiv> snd (snd f)"

    abbreviation Fun :: "'a arr \<Rightarrow> 'a \<Rightarrow> 'a"
    where "Fun f \<equiv> fst f"

    definition Id :: "'a set \<Rightarrow> 'a arr"
    where "Id A \<equiv> (\<lambda>x \<in> A. x, (A, A))"

    (*
     * I attempted to use here the notion A \<rightarrow>\<^sub>E B ("extensional_funcset") defined
     * in FuncSet, but it seems that the rules provided for reasoning directly about
     * it are somewhat weak.  So for the moment I am just using the following
     * longer definition, which caused me less trouble.
     *)
    definition Arr :: "'a arr \<Rightarrow> bool"
    where "Arr f \<equiv> Fun f \<in> extensional (Dom f) \<inter> (Dom f \<rightarrow> Cod f)"

    (*
     * Similarly, it is not clear that there is much to be gained from using
     * "FuncSet.compose A G F" rather than the more basic "restrict (G o F) A".
     * However, the differences were not that significant, so I went with the
     * former.
     *)
    definition comp :: "'a arr \<Rightarrow> 'a arr \<Rightarrow> 'a arr"      (infixr "\<cdot>" 55)
    where "g \<cdot> f = (if Arr f \<and> Arr g \<and> Cod f = Dom g then
                      (compose (Dom f) (Fun g) (Fun f), (Dom f, Cod g))
                    else Null)"

    text\<open>
      Our first objective is to develop just enough properties of the preceding
      definitions to show that they yield a category.
\<close>

    lemma Arr_Id:
    shows "Arr (Id A)"
      unfolding Id_def Arr_def by force

    lemma Dom_Id:
    shows "Dom (Id A) = A"
      by (simp add: Id_def)

    lemma Cod_Id:
    shows "Cod (Id A) = A"
      by (simp add: Id_def)

    lemma comp_Id_Dom:
    assumes "Arr f"
    shows "f \<cdot> Id (Dom f) = f"
    proof -
      have "\<And>F A. F \<in> extensional A \<Longrightarrow> compose A F (\<lambda>x \<in> A. x) = F"
        using compose_extensional extensional_arb by fastforce
      thus ?thesis
        using assms Arr_Id Id_def comp_def
        by (metis (no_types, lifting) Arr_def Cod_Id Dom_Id IntD1 prod.collapse prod.sel(1))
    qed

    lemma comp_Cod_Id:
    assumes "Arr f"
    shows "Id (Cod f) \<cdot> f = f"
    proof -
      have 1: "Fun f \<in> Dom f \<rightarrow> Cod f"
        by (metis (no_types) Arr_def IntD2 assms)
      have 2: "Fun (Id (Cod f)) = (\<lambda>x \<in> Cod f. x) \<and> snd (Id (Cod f)) = (Cod f, Cod f)"
        by (simp add: Id_def)
      hence "compose (Dom f) (Fun (Id (Cod f))) (Fun f) = Fun f"
        using 1 by (metis (no_types) Arr_def Id_compose IntD1 assms)
      then show ?thesis
        using 2 by (simp add: Arr_Id assms comp_def)
    qed

    lemma Arr_comp:
    assumes "Arr f" and "Arr g" and "Cod f = Dom g"
    shows "Arr (g \<cdot> f)"
    proof -
      have "\<forall>x. x \<in> Dom g \<longrightarrow> Fun g x \<in> Cod g"
        using assms(2) Arr_def by fast
      moreover have "\<forall>x. x \<in> Dom f \<longrightarrow> Fun f x \<in> Cod f"
        using assms(1) Arr_def by fast
      moreover have "g \<cdot> f = (compose (Dom f) (Fun g) (Fun f), Dom f, Cod g)"
        by (simp add: assms(1-3) comp_def)
      ultimately show ?thesis by (simp add: Arr_def assms(3))
    qed

    lemma not_Arr_Null:
    shows "\<not>Arr Null"
      by (simp add: Arr_def)

    interpretation partial_magma comp
    proof
      show "\<exists>!n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n"
      proof
        let ?P = "\<lambda>n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n"
        show 1: "?P Null" using comp_def not_Arr_Null by metis
        thus "\<And>n. \<forall>f. n \<cdot> f = n \<and> f \<cdot> n = n \<Longrightarrow> n = Null" by metis
      qed
    qed

    notation in_hom ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    lemma null_char:
    shows "null = Null"
      using comp_def not_Arr_Null ex_un_null by (metis comp_null(2))

    lemma ide_Id:
    shows "ide (Id A)"
    proof -
      have "Id A \<cdot> Id A = Id A"
        unfolding comp_def apply (auto simp add: Arr_Id Dom_Id Cod_Id)
        unfolding Id_def by auto
      moreover have "\<And>f. f \<cdot> Id A \<noteq> null \<Longrightarrow> f \<cdot> Id A = f"
        by (metis Cod_Id comp_Id_Dom comp_def null_char)
      moreover have "\<And>f. Id A \<cdot> f \<noteq> null \<Longrightarrow> Id A \<cdot> f = f"
        by (metis Dom_Id comp_Cod_Id comp_def null_char)
      ultimately show ?thesis
        unfolding ide_def
        using null_char not_Arr_Null Arr_Id by metis
    qed

    lemma has_domain_char:
    shows "Arr f \<Longrightarrow> Id (Dom f) \<in> domains f"
    and "domains f \<noteq> {} \<Longrightarrow> Arr f"
    proof -
      assume f: "domains f \<noteq> {}"
      obtain x where x: "x \<in> domains f"
        using f by blast
      have "f \<cdot> x \<noteq> null"
        using x by (simp add: domains_def)
      thus "Arr f"
        using comp_def null_char by metis
      next
      assume f: "Arr f"
      have "f \<noteq> null"
        by (metis f not_Arr_Null null_char)
      hence "Id (Dom f) \<in> {p. ide p \<and> comp f p \<noteq> null}"
        by (simp add: f comp_Id_Dom ide_Id)
      thus "Id (Dom f) \<in> domains f"
        using domains_def by blast
    qed

    lemma has_codomain_char:
    shows "Arr f \<Longrightarrow> Id (Cod f) \<in> codomains f"
    and "codomains f \<noteq> {} \<Longrightarrow> Arr f"
    proof -
      assume f: "codomains f \<noteq> {}"
      obtain x where x: "x \<in> codomains f"
        using f by blast
      have "x \<cdot> f \<noteq> null"
        using x by (simp add: codomains_def)
      thus "Arr f"
        using comp_def null_char by metis
      next
      assume f: "Arr f"
      have "f \<noteq> null"
        by (metis f not_Arr_Null null_char)
      hence "Id (Cod f) \<in> {p. ide p \<and> comp p f \<noteq> null}"
        by (simp add: f comp_Cod_Id ide_Id)
      thus "Id (Cod f) \<in> codomains f"
        using codomains_def by blast
    qed

    lemma arr_char:
    shows "arr f \<longleftrightarrow> Arr f"
      using has_domain_char has_codomain_char arr_def by blast

    lemma comp_assoc:
    assumes "g \<cdot> f \<noteq> null" and "h \<cdot> g \<noteq> null"
    shows "h \<cdot> g \<cdot> f = (h \<cdot> g) \<cdot> f"
    proof -
      have 1: "Arr f \<and> Arr g \<and> Cod f = Dom g"
        using assms(1) comp_def null_char by metis
      have 2: "Arr g \<and> Arr h \<and> Cod g = Dom h"
        using assms(2) comp_def null_char by metis
      have 3: "Arr (comp g f) \<and>
               comp g f = (compose (Dom f) (Fun g) (Fun f), (Dom f, Cod g))"
        using 1 comp_def Arr_comp by metis
      have 4: "Arr (comp h g) \<and>
               comp h g = (compose (Dom g) (Fun h) (Fun g), (Dom g, Cod h))"
        using 2 comp_def Arr_comp by metis
      have "h \<cdot> g \<cdot> f =
            (compose (Dom f) (Fun h) (compose (Dom f) (Fun g) (Fun f)), (Dom f, Cod h))"
        using 1 2 3 comp_def by (metis (no_types, lifting) fst_conv snd_conv)
      also have
          "... = (compose (Dom f) (compose (Dom g) (Fun h) (Fun g)) (Fun f), (Dom f, Cod h))"
        using 1 2 unfolding Arr_def using compose_assoc by fastforce
      also have "... = (h \<cdot> g) \<cdot> f"
        using 1 2 4 comp_def by (metis (no_types) fst_conv snd_conv)
      finally show ?thesis by auto
    qed

    theorem is_category:
    shows "category comp"
    proof
      fix f g h :: "'a arr"
      show "g \<cdot> f \<noteq> null \<Longrightarrow> seq g f"
        using null_char comp_def Arr_comp arr_char by metis
      show "(domains f \<noteq> {}) = (codomains f \<noteq> {})"
        using has_domain_char has_codomain_char by blast
      show "seq h g \<Longrightarrow> seq (h \<cdot> g) f \<Longrightarrow> seq g f"
        using Arr_comp arr_char comp_def [of h g] comp_def [of g f] comp_def [of "comp h g" f]
        by (metis fst_conv snd_conv)
      show "seq h (g \<cdot> f) \<Longrightarrow> seq g f \<Longrightarrow> seq h g"
        using Arr_comp arr_char comp_def [of h g] comp_def [of g f] comp_def [of h "comp g f"]
        by (metis snd_conv)
      show "seq g f \<Longrightarrow> seq h g \<Longrightarrow> seq (h \<cdot> g) f"
        using Arr_comp arr_char comp_def [of h g] comp_def [of g f] comp_def [of "comp h g" f]
        by (metis fst_conv snd_conv)
      show "seq g f \<Longrightarrow> seq h g \<Longrightarrow> (h \<cdot> g) \<cdot> f = h \<cdot> g \<cdot> f"
        using comp_assoc not_arr_null by metis
    qed

    interpretation category comp
      using is_category by auto

    text\<open>
      Next, we obtain characterizations of the basic notions of the \<open>category\<close>
      locale in terms of the concrete structure.
\<close>

    lemma dom_simp:
    assumes "arr f"
    shows "dom f = Id (Dom f)"
      using assms has_domain_char domain_unique dom_in_domains has_domain_iff_arr
      by blast

    lemma cod_simp:
    assumes "arr f"
    shows "cod f = Id (Cod f)"
      using assms has_codomain_char codomain_unique cod_in_codomains has_codomain_iff_arr
      by blast

    lemma dom_char:
    shows "dom f = (if arr f then (\<lambda>x \<in> Dom f. x, (Dom f, Dom f)) else null)"
      using Id_def dom_simp has_domain_iff_arr dom_def by metis
  
    lemma cod_char:
    shows "cod f = (if arr f then (\<lambda>x \<in> Cod f. x, (Cod f, Cod f)) else null)"
      using Id_def cod_simp has_codomain_iff_arr cod_def by metis

    lemma ide_char:
    shows "ide a \<longleftrightarrow> Dom a = Cod a \<and> Fun a = (\<lambda>x \<in> Dom a. x)"
      using dom_char in_homE [of a a a] arr_char dom_char ide_dom Arr_Id Id_def ide_in_hom
      by (metis fst_conv snd_conv prod.collapse)

    lemma seq_char:
    shows "seq g f \<longleftrightarrow> Arr f \<and> Arr g \<and> Cod f = Dom g"
    proof -
      have "seq g f \<longrightarrow> snd (snd f) = fst (snd g)"
        by (metis not_arr_null comp_def null_char)
      thus ?thesis
        using arr_char dom_char cod_char seqI seqE by metis
    qed
    
    lemma comp_char:
    shows "g \<cdot> f = (if seq g f then
                      (compose (Dom f) (Fun g) (Fun f), (Dom f, Cod g))
                    else Null)"
      using seq_char comp_def null_char by metis
   
  end

  sublocale setcat \<subseteq> category comp
    using is_category by auto

  text\<open>
    Now we want to apply the preceding construction to obtain an actual interpretation
    of the \<open>set_category\<close> locale that hides the concrete details of the construction.
    To do this, we first import the preceding construction into a local context,
    then define an opaque new arrow type for the arrows, and lift just enough
    of the properties of the concrete construction to the abstract setting to make
    it possible to prove that the abstracted category interprets the \<open>set_category\<close>
    locale.  We can then forget about everything except the \<open>set_category\<close> axioms.
    All of this is done within a local context to avoid making any global interpretations.
    Everything except what we ultimately want to export is declared ``private''.
\<close>

  context begin

    interpretation SC: setcat .
    no_notation SC.comp      (infixr "\<cdot>" 55)

    typedef 'a arr = "UNIV :: (('a \<Rightarrow> 'a) * ('a set * 'a set)) set" ..

    interpretation AC: abstracted_category SC.comp Abs_arr Rep_arr UNIV
      using Rep_arr_inverse Abs_arr_inverse by (unfold_locales, auto)

    definition comp
    where "comp \<equiv> AC.comp"

    lemma is_category:
    shows "category comp"
      using comp_def AC.category_axioms by metis

    interpretation category comp using is_category by auto

    notation comp      (infixr "\<cdot>" 55)
    notation in_hom    ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    text\<open>
      To be able to accomplish anything with the category we just defined,
      we have to lift a certain amount of the features of the concrete structure
      through the abstraction.
\<close>

    private definition MkArr
    where "MkArr A B F \<equiv> Abs_arr (restrict F A, (A, B))"

    private abbreviation Id
    where "Id A \<equiv> MkArr A A id"
  
    private definition Dom
    where "Dom f \<equiv> SC.Dom (Rep_arr f)"

    private definition Cod
    where "Cod f \<equiv> SC.Cod (Rep_arr f)"

    private definition Fun
    where "Fun f \<equiv> SC.Fun (Rep_arr f)"

    private lemma Dom_MkArr [simp]:
    shows "Dom (MkArr A B F) = A"
      using Dom_def MkArr_def by (metis AC.rep_abs UNIV_I fst_conv snd_conv)

    private lemma Cod_MkArr [simp]:
    shows "Cod (MkArr A B F) = B"
      using Cod_def MkArr_def by (metis AC.rep_abs UNIV_I snd_conv)

    private lemma Fun_MkArr [simp]:
    shows "Fun (MkArr A B F) = restrict F A"
      using Fun_def MkArr_def by (metis AC.rep_abs UNIV_I fst_conv)

    private lemma null_char:
    shows "null = Abs_arr SC.Null"
      using comp_def by (metis AC.null_char SC.null_char)

    private lemma arr_char:
    shows "arr f \<longleftrightarrow> Fun f \<in> extensional (Dom f) \<inter> (Dom f \<rightarrow> Cod f)"
      using comp_def AC.arr_char SC.arr_char SC.Arr_def Dom_def Cod_def Fun_def by metis

    private lemma dom_char:
    shows "dom f = (if arr f then MkArr (Dom f) (Dom f) id else null)"
      using MkArr_def id_apply restrict_ext comp_def AC.dom_char AC.arr_char SC.dom_char
            Dom_def
      by metis
   
    private lemma cod_char:
    shows "cod f = (if arr f then MkArr (Cod f) (Cod f) id else null)"
      using MkArr_def id_apply restrict_ext comp_def AC.cod_char AC.arr_char SC.cod_char
            Cod_def
      by metis

    private lemma ide_char:
    shows "ide f = (Dom f = Cod f \<and> Fun f = (\<lambda>x \<in> Dom f. x))"
      using comp_def AC.ide_char SC.ide_char Dom_def Cod_def Fun_def by metis

    private lemma seq_char:
    shows "seq g f = (arr f \<and> arr g \<and> Cod f = Dom g)"
      using dom_char cod_char Dom_MkArr seqI seqE by metis

    private lemma comp_char:
    shows "g \<cdot> f = (if seq g f then
                      MkArr (Dom f) (Cod g) (compose (Dom f) (Fun g) (Fun f))
                    else null)"
    proof (cases "seq g f")
      show "\<not>seq g f \<Longrightarrow> ?thesis"
        using comp_def AC.comp_char by metis
      show "seq g f \<Longrightarrow> ?thesis"
      proof -
        assume gf: "seq g f"
        have "g \<cdot> f = Abs_arr (compose (Dom f) (Fun g) (Fun f), Dom f, Cod g)"
          using gf
          by (metis (no_types, lifting) AC.comp_char Cod_def Dom_def Fun_def
              comp_def has_codomain_iff_arr null_char setcat.comp_def codomains_null)
        also have "... = MkArr (Dom f) (Cod g) (compose (Dom f) (Fun g) (Fun f))"
          using MkArr_def [of "Dom f" "Cod g" "compose (Dom f) (Fun g) (Fun f)"]
                compose_def
          by simp
        finally have "g \<cdot> f = MkArr (Dom f) (Cod g) (compose (Dom f) (Fun g) (Fun f))"
          by auto
        thus ?thesis using gf by auto
      qed
    qed
   
    private lemma arr_MkArr:
    assumes "F \<in> A \<rightarrow> B"
    shows "arr (MkArr A B F)"
      using assms arr_char Fun_MkArr Dom_MkArr Cod_MkArr by force

    private lemma MkArr_Fun:
    assumes "arr f"
    shows "MkArr (Dom f) (Cod f) (Fun f) = f"
      using assms arr_char MkArr_def Dom_def Cod_def Fun_def
      by (metis AC.abs_rep IntD1 extensional_restrict prod.collapse)

    private lemma arr_eqI:
    assumes "arr f" and "arr f'"
    and "Dom f = Dom f'" and "Cod f = Cod f'" and "Fun f = Fun f'"
    shows "f = f'"
      using assms MkArr_Fun by metis

    private lemma ide_Id:
    shows "ide (Id A)"
      using ide_char Fun_MkArr Dom_MkArr Cod_MkArr id_apply restrict_ext by metis

    private lemma Id_Dom:
    assumes "ide a"
    shows "Id (Dom a) = a"
      using assms dom_char ide_in_hom by (metis in_homE)

    private lemma Id_Cod:
    assumes "ide a"
    shows "Id (Cod a) = a"
      using assms ide_char by (metis Id_Dom)

    private lemma MkArr_in_hom:
    assumes "F \<in> A \<rightarrow> B"
    shows "\<guillemotleft>MkArr A B F : Id A \<rightarrow> Id B\<guillemotright>"
    proof -
      have 1: "arr (MkArr A B F)" using assms arr_MkArr by blast
      moreover have "dom (MkArr A B F) = Id A"
        using 1 dom_char Dom_MkArr by metis
      moreover have "cod (MkArr A B F) = Id B"
        using 1 cod_char Cod_MkArr by metis
      ultimately show ?thesis by blast
    qed

    private lemma terminal_char:
    shows "terminal a \<longleftrightarrow> (\<exists>x. a = Id {x})"
    proof
      show "\<exists>x. a = Id {x} \<Longrightarrow> terminal a"
      proof -
        assume a: "\<exists>x. a = Id {x}"
        from this obtain x where x: "a = Id {x}" by blast
        have "terminal (Id {x})"
        proof
          show 1: "ide (Id {x})"
            using ide_Id by metis
          show "\<And>a. ide a \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> Id {x}\<guillemotright>"
          proof
            fix a :: "'a arr"
            assume a: "ide a"
            show "\<guillemotleft>MkArr (Dom a) {x} (\<lambda>_\<in>Dom a. x) : a \<rightarrow> Id {x}\<guillemotright>"
              using a Id_Dom MkArr_in_hom
              by (metis restrictI singletonI)
            fix f :: "'a arr"
            assume f: "\<guillemotleft>f : a \<rightarrow> Id {x}\<guillemotright>"
            show "f = MkArr (Dom a) {x} (\<lambda>_ \<in> Dom a. x)"
            proof -
              have 2: "Dom f = Dom a \<and> Cod f = {x}"
                using a f Dom_MkArr dom_char cod_char in_homE by metis
              moreover have "Fun f = (\<lambda>_ \<in> Dom a. x)"
              proof
                fix z
                have "z \<notin> Dom a \<Longrightarrow> Fun f z = (\<lambda>_ \<in> Dom a. x) z"
                  by (metis f 2 Fun_MkArr MkArr_Fun in_homE restrict_def)
                moreover have "z \<in> Dom a \<Longrightarrow> Fun f z = (\<lambda>_ \<in> Dom a. x) z"
                  using f 2 arr_char [of f] by auto
                ultimately show "Fun f z = (\<lambda>_ \<in> Dom a. x) z" by auto
              qed
              ultimately show ?thesis
                using a f arr_eqI MkArr_Fun mem_Collect_eq by fastforce
            qed
          qed
        qed
        thus "terminal a" using x by simp
      qed
      show "terminal a \<Longrightarrow> \<exists>x. a = Id {x}"
      proof -
        assume a: "terminal a"
        hence "ide a" using terminal_def by auto
        have 1: "\<exists>!x. x \<in> Dom a"
        proof -
          have "Dom a = {} \<Longrightarrow> \<not>terminal a"
          proof -
            assume "Dom a = {}"
            hence 1: "a = Id {}" using \<open>ide a\<close> Id_Dom by force
            have "\<And>f. f \<in> hom (Id {undefined}) (Id {}) \<Longrightarrow> Fun f \<in> {undefined} \<rightarrow> {}"
              by (metis Cod_MkArr CollectD IntD2 arrI arr_char cod_char dom_char in_homE)
            hence "hom (Id {undefined}) a = {}" using 1 by auto
            moreover have "ide (Id {undefined})" using ide_Id by auto
            ultimately show "\<not>terminal a" by auto
          qed
          moreover have "\<And>x x'. x \<in> Dom a \<and> x' \<in> Dom a \<and> x \<noteq> x' \<Longrightarrow> \<not>terminal a"
          proof -
            fix x x'
            assume 1: "x \<in> Dom a \<and> x' \<in> Dom a \<and> x \<noteq> x'"
            have "\<guillemotleft>MkArr {undefined} (Dom a) (\<lambda>_. x) : Id {undefined} \<rightarrow> a\<guillemotright>"
              using 1 MkArr_in_hom [of "\<lambda>_. x" "{undefined}" "Dom a"] Id_Dom [of a] \<open>ide a\<close>
              by simp
            moreover have "\<guillemotleft>MkArr {undefined} (Dom a) (\<lambda>_. x') : Id {undefined} \<rightarrow> a\<guillemotright>"
              using 1 MkArr_in_hom [of "\<lambda>_. x'" "{undefined}" "Dom a"] Id_Dom [of a] \<open>ide a\<close>
              by simp
            moreover have
                "MkArr {undefined} (Dom a) (\<lambda>_. x) \<noteq> MkArr {undefined} (Dom a) (\<lambda>_. x')"
              using 1 Fun_MkArr restrict_apply by (metis singletonI)
            ultimately show "\<not>terminal a"
              using terminal_arr_unique by (metis arrI in_homE)
          qed
          ultimately show ?thesis
            using a by auto
        qed
        hence "Dom a = {THE x. x \<in> Dom a}"
          using theI [of "\<lambda>x. x \<in> Dom a"] by auto
        hence "a = Id {THE x. x \<in> Dom a}"
          using a Id_Dom terminal_def by metis
        thus "\<exists>x. a = Id {x}"
          by auto
      qed
    qed

    private definition Img :: "'a arr \<Rightarrow> 'a arr"
    where "Img f = Id (Fun f ` Dom f)"
  
    interpretation set_category_data comp Img ..

    private lemma terminal_unity:
    shows "terminal unity"
      using terminal_char unity_def someI_ex [of terminal] by metis
  
    text\<open>
      The inverse maps @{term UP} and @{term DOWN} are used to pass back and forth between
      the inhabitants of type @{typ 'a} and the corresponding terminal objects.
      These are exported so that a client of the theory can relate the concrete
      element type @{typ 'a} to the otherwise abstract arrow type.
\<close>

    definition UP :: "'a \<Rightarrow> 'a arr"
    where "UP x \<equiv> Id {x}"
  
    definition DOWN :: "'a arr \<Rightarrow> 'a"
    where "DOWN t \<equiv> the_elem (Dom t)"

    abbreviation U :: 'a
    where "U \<equiv> DOWN unity"
  
    lemma UP_mapsto:
    shows "UP \<in> UNIV \<rightarrow> Univ"
      using terminal_char UP_def by fast
    
    lemma DOWN_mapsto:
    shows "DOWN \<in> Univ \<rightarrow> UNIV"
      by auto
    
    lemma DOWN_UP [simp]:
    shows "DOWN (UP x) = x"
      by (simp add: DOWN_def UP_def)
    
    lemma UP_DOWN [simp]:
    assumes "t \<in> Univ"
    shows "UP (DOWN t) = t"
      using assms terminal_char UP_def DOWN_def
      by (metis CollectD Dom_MkArr the_elem_eq)
  
    lemma inj_UP:
    shows "inj UP"
      by (metis DOWN_UP injI)
  
    lemma bij_UP:
    shows "bij_betw UP UNIV Univ"
    proof (intro bij_betwI)
      interpret category comp using is_category by auto
      show DOWN_UP: "\<And>x :: 'a. DOWN (UP x) = x" by auto
      show UP_DOWN: "\<And>t. t \<in> Univ \<Longrightarrow> UP (DOWN t) = t" by auto
      show "UP \<in> UNIV \<rightarrow> Univ" using UP_mapsto by auto
      show "DOWN \<in> Collect terminal \<rightarrow> UNIV" by auto
    qed
  
    private lemma Dom_terminal:
    assumes "terminal t"
    shows "Dom t = {DOWN t}"
      using assms UP_DOWN UP_def
      by (metis Dom_MkArr mem_Collect_eq)

    text\<open>
      The image of a point @{term "p \<in> hom unity a"} is a terminal object, which is given
      by the formula @{term "(UP o Fun p o DOWN) unity"}.
\<close>

    private lemma Img_point:
    assumes "\<guillemotleft>p : unity \<rightarrow> a\<guillemotright>"
    shows "Img \<in> hom unity a \<rightarrow> Univ"
    and "Img p = (UP o Fun p o DOWN) unity"
    proof -
      show "Img \<in> hom unity a \<rightarrow> Univ"
      proof
        fix x
        assume x: "x \<in> hom unity a"
        have "terminal (Id (Fun x ` Dom unity))"
          using x terminal_char
          by (metis (no_types, lifting) Dom_terminal image_empty image_insert terminal_unity)
        hence "Id (Fun x ` Dom unity) \<in> Univ" by simp
        moreover have "Id (Fun x ` Dom unity) = Img x"
          using x dom_char Dom_MkArr Img_def in_homE by (metis CollectD)
        ultimately show "Img x \<in> Univ" by auto
      qed
      have 1: "Dom p = Dom unity"
        using assms dom_char Dom_MkArr by (metis in_homE)
      have "Img p = Id (Fun p ` Dom p)" using Img_def by blast
      also have "... = Id (Fun p ` {U})"
        using 1 terminal_unity Dom_terminal by metis
      also have "... = (UP o Fun p o DOWN) unity" by (simp add: UP_def)
      finally show "Img p = (UP o Fun p o DOWN) unity" using assms by auto
    qed
  
    text\<open>
      The function @{term Img} is injective on @{term "hom unity a"} and its inverse takes
      a terminal object @{term t} to the arrow in @{term "hom unity a"} corresponding to the
      constant-@{term t} function.
\<close>

    private abbreviation MkElem
    where "MkElem t a \<equiv> MkArr {U} (Dom a) (\<lambda>_ \<in> {U}. DOWN t)"

    private lemma MkElem_in_hom:
    assumes "arr f" and "x \<in> Dom f"
    shows "\<guillemotleft>MkElem (UP x) (dom f) : unity \<rightarrow> dom f\<guillemotright>"
    proof -
      have "(\<lambda>_ \<in> {U}. DOWN (UP x)) \<in> {U} \<rightarrow> Dom (dom f)"
        using assms dom_char [of f] by fastforce
      moreover have "Id {U} = unity"
        by (metis Dom_MkArr Dom_terminal terminal_char terminal_unity)
      moreover have "Id (Dom (dom f)) = dom f"
        using assms by (simp add: dom_char)
      ultimately show ?thesis
        using assms MkArr_in_hom [of "\<lambda>_ \<in> {U}. DOWN (UP x)" "{U}" "Dom (dom f)"] by metis
    qed

    private lemma MkElem_Img:
    assumes "p \<in> hom unity a"
    shows "MkElem (Img p) a = p"
    proof -
      have 0: "Img p = UP (Fun p U)"
        using assms Img_point(2) by auto
      have 1: "Dom p = {U}"
        using assms dom_char Dom_MkArr terminal_unity Dom_terminal
        by (metis in_homE CollectD)
      moreover have "Cod p = Dom a"
        using assms cod_char by (metis Dom_MkArr in_homE CollectD)
      moreover have "Fun p = (\<lambda>_ \<in> {U}. DOWN (Img p))"
      proof
        fix e
        show "Fun p e = (\<lambda>_ \<in> {U}. DOWN (Img p)) e"
          using assms 0 1 Fun_MkArr MkArr_Fun in_homE
          by (metis DOWN_UP restrict_apply singleton_iff CollectD)
      qed
      ultimately show "MkElem (Img p) a = p"
        using assms arr_eqI Dom_MkArr Cod_MkArr Fun_MkArr MkArr_Fun CollectD by fastforce
    qed

    private lemma inj_Img:
    assumes "ide a"
    shows "inj_on Img (hom unity a)"
      using assms MkElem_Img inj_onI [of "hom unity a" Img] by metis

    private lemma set_char:
    assumes "ide a"
    shows "set a = UP ` Dom a"
    proof
      show "set a \<subseteq> UP ` Dom a"
      proof
        fix t
        assume "t \<in> set a"
        from this obtain p where p: "\<guillemotleft>p : unity \<rightarrow> a\<guillemotright> \<and> t = Img p"
          using set_def by blast
        have 1: "Dom p = Dom unity"
          using p dom_char Dom_MkArr by (metis in_homE)
        have "t = (UP o Fun p o DOWN) unity"
          using p Img_point(2) by blast
        moreover have "(Fun p o DOWN) unity \<in> Dom a"
          using 1 p arr_char Dom_terminal terminal_unity cod_char
          by (metis Dom_MkArr IntD2 PiE comp_apply in_homE singletonI)
        ultimately show "t \<in> UP ` Dom a" by simp
      qed
      show "UP ` Dom a \<subseteq> set a"
      proof
        fix t
        assume "t \<in> UP ` Dom a"
        from this obtain x where x: "x \<in> Dom a \<and> t = UP x" by blast
        let ?p = "MkElem (UP x) a"
        have p: "?p \<in> hom unity a"
          using assms x MkElem_in_hom [of "dom a"] by auto
        moreover have "Img ?p = t" using p x Img_point by force
        ultimately show "t \<in> set a" using set_def by blast
      qed
    qed
  
    private lemma Fun_via_comp:
    assumes "arr f"
    shows "Fun f = restrict (\<lambda>x. Fun (comp f (MkElem (UP x) (dom f))) U) (Dom f)"
    proof
      fix x
      have "x \<notin> Dom f \<Longrightarrow>
              Fun f x = restrict (\<lambda>x. Fun (comp f (MkElem (UP x) (dom f))) U) (Dom f) x"
        using assms arr_char [of f] IntD1 extensional_arb restrict_apply by fastforce
      moreover have
           "x \<in> Dom f \<Longrightarrow>
              Fun f x = restrict (\<lambda>x. Fun (comp f (MkElem (UP x) (dom f))) U) (Dom f) x"
      proof -
        assume x: "x \<in> Dom f"
        have "\<guillemotleft>MkElem (UP x) (dom f) : unity \<rightarrow> dom f\<guillemotright>"
          using assms x MkElem_in_hom by auto
        hence "f \<cdot> MkElem (UP x) (dom f) =
               MkArr {U} (Cod f) (compose {U} (Fun f) (\<lambda>_ \<in> {U}. x))"
          using assms MkArr_Fun comp_char [of f "MkElem (UP x) (dom f)"] by auto
        hence "Fun (f \<cdot> MkElem (UP x) (dom f)) = compose {U} (Fun f) (\<lambda>_ \<in> {U}. x)"
           by (simp add: extensional_restrict)
        thus ?thesis
          using x by (simp add: compose_eq restrict_apply' singletonI)
      qed
      ultimately show
            "Fun f x = restrict (\<lambda>x. Fun (f \<cdot> MkElem (UP x) (dom f)) U) (Dom f) x"
        by auto
    qed
    
    text\<open>
      The main result, which establishes the consistency of the \<open>set_category\<close> locale
      and provides us with a way of obtaining ``set categories'' at arbitrary types.
\<close>

    theorem is_set_category:
    shows "set_category comp"
    proof
      show "\<exists>img :: 'a arr \<Rightarrow> 'a arr. set_category_given_img comp img"
      proof
        show "set_category_given_img (comp :: 'a arr comp) Img"
        proof
          show "Univ \<noteq> {}" using terminal_char by blast
          fix a :: "'a arr"
          assume a: "ide a"
          show "Img \<in> hom unity a \<rightarrow> Univ" using Img_point terminal_unity by blast
          show "inj_on Img (hom unity a)" using a inj_Img terminal_unity by blast
          next
          fix t :: "'a arr"
          assume t: "terminal t"
          show "t \<in> Img ` hom unity t"
          proof -
            have "UP ` Dom t = {t}" using t Dom_terminal [of t] UP_DOWN by simp
            thus ?thesis using t set_char set_def terminal_def by blast
          qed
          next
          fix A :: "'a arr set"
          assume A: "A \<subseteq> Univ"
          show "\<exists>a. ide a \<and> set a = A"
          proof
            let ?a = "MkArr (DOWN ` A) (DOWN ` A) (\<lambda>x. x)"
            show "ide ?a \<and> set ?a = A"
            proof
              show 1: "ide ?a"
                using ide_char by fastforce
              show "set ?a = A"
              proof -
                have 2: "\<And>x. x \<in> A \<Longrightarrow> x = UP (DOWN x)"
                  using A UP_DOWN by force
                hence "UP ` DOWN ` A = A"
                  using A UP_DOWN by auto
                thus ?thesis
                  using 1 A set_char [of ?a] by simp
              qed
            qed
          qed
          next
          fix a b :: "'a arr"
          assume a: "ide a" and b: "ide b" and ab: "set a = set b"
          show "a = b"
            using a b ab set_char inj_UP inj_image_eq_iff dom_char in_homE ide_in_hom by metis
          next
          fix f f' :: "'a arr"
          assume par: "par f f'" and ff': "\<And>x. \<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright> \<Longrightarrow> f \<cdot> x = f' \<cdot> x"
          have 1: "Dom f = Dom f' \<and> Cod f = Cod f'"
            using par dom_char cod_char Dom_MkArr by (metis (no_types, lifting))
          moreover have "Fun f = Fun f'"
            using 1 par ff' MkElem_in_hom Fun_via_comp Fun_via_comp by fastforce
          ultimately show "f = f'" using par arr_eqI by auto
          next
          fix a b :: "'a arr" and F :: "'a arr \<Rightarrow> 'a arr"
          assume a: "ide a" and b: "ide b" and F: "F \<in> hom unity a \<rightarrow> hom unity b"
          show "\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright> \<longrightarrow> f \<cdot> x = F x)"
          proof
            let ?f = "MkArr (Dom a) (Dom b) (\<lambda>x. Fun (F (MkElem (UP x) a)) U)"
            have "(\<lambda>x. Fun (F (MkElem (UP x) a)) U) \<in> Dom a \<rightarrow> Dom b"
            proof
              fix x
              assume x: "x \<in> Dom a"
              have "MkElem (UP x) a \<in> hom unity a"
                using x a MkElem_in_hom [of a x] ide_char by force
              hence 1: "F (MkElem (UP x) a) \<in> hom unity b"
                using F by auto
              moreover have "Dom (F (MkElem (UP x) a)) = {U}"
                using 1 by (metis Dom_MkArr MkElem_Img)
              moreover have "Cod (F (MkElem (UP x) a)) = Dom b"
                using 1 by (metis Dom_MkArr cod_char in_homE CollectD)
              ultimately have "Fun (F (MkElem (UP x) a)) \<in> {U} \<rightarrow> Dom b"
                using arr_char [of "F (MkElem (UP x) a)"] by blast
              thus "Fun (F (MkElem (UP x) a)) U \<in> Dom b" by blast
            qed
            hence 1: "\<guillemotleft>?f : a \<rightarrow> b\<guillemotright>"
              using a b Id_Dom MkArr_in_hom by metis
            have "\<And>x. \<guillemotleft>x : unity \<rightarrow> dom ?f\<guillemotright> \<Longrightarrow> ?f \<cdot> x = F x"
            proof -
              fix x
              assume x: "\<guillemotleft>x : unity \<rightarrow> dom ?f\<guillemotright>"
              have 2: "x = MkElem (Img x) a"
                using a x 1 MkElem_Img [of x a] by auto
              moreover have 5: "Dom x = {U} \<and> Cod x = Dom a \<and>
                                Fun x = (\<lambda>_ \<in> {U}. DOWN (Img x))"
                using x 2 Dom_MkArr [of "{U}" "Dom a" "\<lambda>_ \<in> {U}. DOWN (Img x)"]
                      Cod_MkArr [of "{U}" "Dom a" "\<lambda>_ \<in> {U}. DOWN (Img x)"]
                      Fun_MkArr [of "{U}" "Dom a" "\<lambda>_ \<in> {U}. DOWN (Img x)"]
                by simp
              moreover have "Cod ?f = Dom b" using 1 by simp
              ultimately have
                   3: "?f \<cdot> x =
                       MkArr {U} (Dom b) (compose {U} (Fun ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)))"
                using 1 x comp_char [of ?f "MkElem (Img x) a"] Dom_MkArr Cod_MkArr Fun_MkArr
                by fastforce
              have 4: "compose {U} (Fun ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) = Fun (F x)"
              proof
                fix y
                have "y \<notin> {U} \<Longrightarrow>
                        compose {U} (Fun ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) y = Fun (F x) y"
                proof -
                  assume y: "y \<notin> {U}"
                  have "compose {U} (Fun ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) y = undefined"
                    using y compose_def extensional_arb by simp
                  also have "... = Fun (F x) y"
                  proof -
                    have 5: "F x \<in> hom unity b" using x F 1 by fastforce
                    hence "Dom (F x) = {U}"
                      by (metis Dom_MkArr MkElem_Img)
                    thus ?thesis
                      using y 5 arr_char [of "F x"] extensional_arb by fastforce
                  qed
                  ultimately show ?thesis by auto
                qed
                moreover have
                    "y \<in> {U} \<Longrightarrow>
                       compose {U} (Fun ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) y = Fun (F x) y"
                proof -
                  assume y: "y \<in> {U}"
                  have "compose {U} (Fun ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) y =
                        Fun ?f (DOWN (Img x))"
                    using y by (simp add: compose_eq restrict_apply')
                  also have "... = (\<lambda>x. Fun (F (MkElem (UP x) a)) U) (DOWN (Img x))"
                  proof -
                    have "DOWN (Img x) \<in> Dom a"
                      using x y a 5 arr_char in_homE restrict_apply
                      by (metis (no_types, lifting) IntD2 PiE)
                    thus ?thesis
                      using Fun_MkArr restrict_apply by simp
                  qed
                  also have "... = Fun (F x) y"
                    using x y 1 MkElem_Img [of x a] by auto
                  finally show
                      "compose {U} (Fun ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) y = Fun (F x) y"
                    by auto
                qed
                ultimately show
                    "compose {U} (Fun ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) y = Fun (F x) y"
                  by auto
              qed
              show "?f \<cdot> x = F x"
              proof (intro arr_eqI)
                have 5: "?f \<cdot> x \<in> hom unity b" using 1 x by auto
                have 6: "F x \<in> hom unity b" using x F 1 by force
                show "arr (comp ?f x)" using 5 by auto
                show "arr (F x)" using 6 by auto
                show "Dom (comp ?f x) = Dom (F x)"
                  using 5 6 Dom_MkArr MkElem_Img by metis
                show "Cod (comp ?f x) = Cod (F x)"
                  using 5 6 Cod_MkArr MkElem_Img by metis
                show "Fun (comp ?f x) = Fun (F x)"
                  using 3 4 Fun_MkArr
                  by (metis compose_def extensional_restrict restrict_extensional)
              qed
            qed
            thus "\<guillemotleft>?f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> dom ?f\<guillemotright> \<longrightarrow> comp ?f x = F x)"
              using 1 by blast
          qed
        qed
      qed
    qed

    text\<open>
      As a consequence of the categoricity of the \<open>set_category\<close> axioms,
      if @{term S} interprets \<open>set_category\<close>, and if @{term \<phi>} is a bijection between
      the universe of @{term S} and the elements of type @{typ 'a}, then @{term S} is isomorphic
      to the category \<open>SetCat\<close> of @{typ 'a} sets and functions between them constructed here.
\<close>

    corollary set_category_iso_SetCat:
    fixes S :: "'s comp" and \<phi> :: "'s \<Rightarrow> 'a"
    assumes "set_category S"
    and "bij_betw \<phi> (Collect (category.terminal S)) UNIV"
    shows "\<exists>\<Phi>. invertible_functor S (SetCat.comp :: 'a arr comp) \<Phi>
              \<and> (\<forall>m. set_category.incl S m \<longrightarrow> set_category.incl SetCat.comp (\<Phi> m))"
    proof -
      interpret S: set_category S using assms by auto
      let ?\<psi> = "inv_into S.Univ \<phi>"
      have "bij_betw (UP o \<phi>) S.Univ (Collect (category.terminal comp))"
      proof (intro bij_betwI)
        show "UP o \<phi> \<in> S.Univ \<rightarrow> Collect (category.terminal comp)"
          using assms(2) UP_mapsto by auto
        show "?\<psi> o DOWN \<in> Collect (category.terminal comp) \<rightarrow> S.Univ"
          using assms(2) by (metis Pi_I UNIV_I bij_betw_def comp_apply inv_into_into)
        fix t
        assume "t \<in> S.Univ"
        thus "(?\<psi> o DOWN) ((UP o \<phi>) t) = t"
          using assms(2) bij_betw_inv_into_left comp_def by fastforce
        next
        fix t' :: "'a arr"
        assume "t' \<in> Collect (category.terminal comp)"
        thus "(UP o \<phi>) ((?\<psi> o DOWN) t') = t'"
          using assms(2) by (metis UNIV_I UP_DOWN bij_betw_def comp_apply f_inv_into_f)
      qed
      thus ?thesis
        using assms(1) set_category_is_categorical [of S SetCat.comp "UP o \<phi>"] is_set_category 
        by blast
    qed

    text\<open>
      \<open>SetCat\<close> can be viewed as a concrete set category over its own element type
      @{typ 'a}, using @{term UP} as the required injection from @{typ 'a} to the universe
      of \<open>SetCat\<close>.
\<close>

    corollary is_concrete_set_category:
    shows "concrete_set_category comp Univ UP"
    proof -
      interpret S: set_category comp using is_set_category by auto
      show ?thesis
      proof
        show 1: "UP \<in> S.Univ \<rightarrow> S.Univ" using UP_mapsto by auto
        show "inj_on UP S.Univ" by (metis injD inj_UP inj_onI)
      qed
    qed

    no_notation comp      (infixr "\<cdot>" 55)
    no_notation in_hom    ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

  end
  
end

