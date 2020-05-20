(*  Title:       SetCat
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter SetCat

theory SetCat
imports SetCategory ConcreteCategory
begin

  text\<open>
    This theory proves the consistency of the \<open>set_category\<close> locale by giving
    a particular concrete construction of an interpretation for it.
    Applying the general construction given by @{locale concrete_category},
    we define arrows to be terms \<open>MkArr A B F\<close>, where \<open>A\<close> and \<open>B\<close> are sets
    and \<open>F\<close> is an extensional function that maps \<open>A\<close> to \<open>B\<close>.
\<close>

  locale setcat
  begin

    type_synonym 'aa arr = "('aa set, 'aa \<Rightarrow> 'aa) concrete_category.arr"

    interpretation concrete_category \<open>UNIV :: 'a set set\<close> \<open>\<lambda>A B. extensional A \<inter> (A \<rightarrow> B)\<close>
      \<open>\<lambda>A. \<lambda>x \<in> A. x\<close> \<open>\<lambda>C B A g f. compose A g f\<close>
      using compose_Id Id_compose
      apply unfold_locales
          apply auto[3]
       apply blast
      by (metis IntD2 compose_assoc)

    abbreviation Comp      (infixr "\<cdot>" 55)
    where "Comp \<equiv> COMP"
    notation in_hom        ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    lemma MkArr_expansion:
    assumes "arr f"
    shows "f = MkArr (Dom f) (Cod f) (\<lambda>x \<in> Dom f. Map f x)"
    proof (intro arr_eqI)
      show "arr f" by fact
      show "arr (MkArr (Dom f) (Cod f) (\<lambda>x \<in> Dom f. Map f x))"
        using assms arr_char
        by (metis (mono_tags, lifting) Int_iff MkArr_Map extensional_restrict)
      show "Dom f = Dom (MkArr (Dom f) (Cod f) (\<lambda>x \<in> Dom f. Map f x))"
        by simp
      show "Cod f = Cod (MkArr (Dom f) (Cod f) (\<lambda>x \<in> Dom f. Map f x))"
        by simp
      show "Map f = Map (MkArr (Dom f) (Cod f) (\<lambda>x \<in> Dom f. Map f x))"
        using assms arr_char
        by (metis (mono_tags, lifting) Int_iff MkArr_Map extensional_restrict)
    qed

    lemma arr_char:
    shows "arr f \<longleftrightarrow> f \<noteq> Null \<and> Map f \<in> extensional (Dom f) \<inter> (Dom f \<rightarrow> Cod f)"
      using arr_char by auto

    lemma terminal_char:
    shows "terminal a \<longleftrightarrow> (\<exists>x. a = MkIde {x})"
    proof
      show "\<exists>x. a = MkIde {x} \<Longrightarrow> terminal a"
      proof -
        assume a: "\<exists>x. a = MkIde {x}"
        from this obtain x where x: "a = MkIde {x}" by blast
        have "terminal (MkIde {x})"
        proof
          show "ide (MkIde {x})"
            using ide_MkIde by auto
          show "\<And>a. ide a \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> MkIde {x}\<guillemotright>"
          proof
            fix a :: "'a setcat.arr"
            assume a: "ide a"
            show "\<guillemotleft>MkArr (Dom a) {x} (\<lambda>_\<in>Dom a. x) : a \<rightarrow> MkIde {x}\<guillemotright>"
              using a MkArr_in_hom
              by (metis (mono_tags, lifting) IntI MkIde_Dom' restrictI restrict_extensional
                  singletonI UNIV_I)
            fix f :: "'a setcat.arr"
            assume f: "\<guillemotleft>f : a \<rightarrow> MkIde {x}\<guillemotright>"
            show "f = MkArr (Dom a) {x} (\<lambda>_ \<in> Dom a. x)"
            proof -
              have 1: "Dom f = Dom a \<and> Cod f = {x}"
                using a f by (metis (mono_tags, lifting) Dom.simps(1) in_hom_char)
              moreover have "Map f = (\<lambda>_ \<in> Dom a. x)"
              proof
                fix z
                have "z \<notin> Dom a \<Longrightarrow> Map f z = (\<lambda>_ \<in> Dom a. x) z"
                  using f 1 MkArr_expansion
                  by (metis (mono_tags, lifting) Map.simps(1) in_homE restrict_apply)
                moreover have "z \<in> Dom a \<Longrightarrow> Map f z = (\<lambda>_ \<in> Dom a. x) z"
                  using f 1 arr_char [of f] by fastforce
                ultimately show "Map f z = (\<lambda>_ \<in> Dom a. x) z" by auto
              qed
              ultimately show ?thesis
               using f MkArr_expansion [of f] by fastforce
            qed
          qed
        qed
        thus "terminal a" using x by simp
      qed
      show "terminal a \<Longrightarrow> \<exists>x. a = MkIde {x}"
      proof -
        assume a: "terminal a"
        hence "ide a" using terminal_def by auto
        have 1: "\<exists>!x. x \<in> Dom a"
        proof -
          have "Dom a = {} \<Longrightarrow> \<not>terminal a"
          proof -
            assume "Dom a = {}"
            hence 1: "a = MkIde {}" using \<open>ide a\<close> MkIde_Dom' by force
            have "\<And>f. f \<in> hom (MkIde {undefined}) (MkIde ({} :: 'a set))
                         \<Longrightarrow> Map f \<in> {undefined} \<rightarrow> {}"
            proof -
              fix f
              assume f: "f \<in> hom (MkIde {undefined}) (MkIde ({} :: 'a set))"
              show "Map f \<in> {undefined} \<rightarrow> {}"
                using f MkArr_expansion arr_char [of f] in_hom_char  by auto
            qed
            hence "hom (MkIde {undefined}) a = {}" using 1 by auto
            moreover have "ide (MkIde {undefined})" using ide_MkIde by auto
            ultimately show "\<not>terminal a" by blast
          qed
          moreover have "\<And>x x'. x \<in> Dom a \<and> x' \<in> Dom a \<and> x \<noteq> x' \<Longrightarrow> \<not>terminal a"
          proof -
            fix x x'
            assume 1: "x \<in> Dom a \<and> x' \<in> Dom a \<and> x \<noteq> x'"
            have "\<guillemotleft>MkArr {undefined} (Dom a) (\<lambda>_ \<in> {undefined}. x) : MkIde {undefined} \<rightarrow> a\<guillemotright>"
              using 1
              by (metis (mono_tags, lifting) IntI MkIde_Dom' \<open>ide a\<close> restrictI
                  restrict_extensional MkArr_in_hom UNIV_I)
            moreover have
              "\<guillemotleft>MkArr {undefined} (Dom a) (\<lambda>_ \<in> {undefined}. x') : MkIde {undefined} \<rightarrow> a\<guillemotright>"
              using 1
              by (metis (mono_tags, lifting) IntI MkIde_Dom' \<open>ide a\<close> restrictI
                  restrict_extensional MkArr_in_hom UNIV_I)
            moreover have "MkArr {undefined} (Dom a) (\<lambda>_ \<in> {undefined}. x) \<noteq>
                           MkArr {undefined} (Dom a) (\<lambda>_ \<in> {undefined}. x')"
              using 1 by (metis arr.inject restrict_apply' singletonI)
            ultimately show "\<not>terminal a"
              using terminal_arr_unique
              by (metis (mono_tags, lifting) in_homE)
          qed
          ultimately show ?thesis
            using a by auto
        qed
        hence "Dom a = {THE x. x \<in> Dom a}"
          using theI [of "\<lambda>x. x \<in> Dom a"] by auto
        hence "a = MkIde {THE x. x \<in> Dom a}"
          using a terminal_def by (metis (mono_tags, lifting) MkIde_Dom')
        thus "\<exists>x. a = MkIde {x}"
          by auto
      qed
    qed

    definition Img :: "'a setcat.arr \<Rightarrow> 'a setcat.arr"
    where "Img f = MkIde (Map f ` Dom f)"
  
    interpretation set_category_data Comp Img ..

    lemma terminal_unity:
    shows "terminal unity"
      using terminal_char unity_def someI_ex [of terminal]
      by (metis (mono_tags, lifting))
  
    text\<open>
      The inverse maps @{term UP} and @{term DOWN} are used to pass back and forth between
      the inhabitants of type @{typ 'a} and the corresponding terminal objects.
      These are exported so that a client of the theory can relate the concrete
      element type @{typ 'a} to the otherwise abstract arrow type.
\<close>

    definition UP :: "'a \<Rightarrow> 'a setcat.arr"
    where "UP x \<equiv> MkIde {x}"
  
    definition DOWN :: "'a setcat.arr \<Rightarrow> 'a"
    where "DOWN t \<equiv> the_elem (Dom t)"

    abbreviation U
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
      by (metis (mono_tags, lifting) mem_Collect_eq DOWN_UP)
  
    lemma inj_UP:
    shows "inj UP"
      by (metis DOWN_UP injI)
  
    lemma bij_UP:
    shows "bij_betw UP UNIV Univ"
    proof (intro bij_betwI)
      interpret category Comp using is_category by auto
      show DOWN_UP: "\<And>x :: 'a. DOWN (UP x) = x" by simp
      show UP_DOWN: "\<And>t. t \<in> Univ \<Longrightarrow> UP (DOWN t) = t" by simp
      show "UP \<in> UNIV \<rightarrow> Univ" using UP_mapsto by auto
      show "DOWN \<in> Collect terminal \<rightarrow> UNIV" by auto
    qed
  
    lemma Dom_terminal:
    assumes "terminal t"
    shows "Dom t = {DOWN t}"
      using assms UP_def
      by (metis (mono_tags, lifting) Dom.simps(1) DOWN_def terminal_char the_elem_eq)

    text\<open>
      The image of a point @{term "p \<in> hom unity a"} is a terminal object, which is given
      by the formula @{term "(UP o Fun p o DOWN) unity"}.
\<close>

    lemma Img_point:
    assumes "\<guillemotleft>p : unity \<rightarrow> a\<guillemotright>"
    shows "Img \<in> hom unity a \<rightarrow> Univ"
    and "Img p = (UP o Map p o DOWN) unity"
    proof -
      show "Img \<in> hom unity a \<rightarrow> Univ"
      proof
        fix f
        assume f: "f \<in> hom unity a"
        have "terminal (MkIde (Map f ` Dom unity))"
        proof -
          obtain u :: 'a where u: "unity = MkIde {u}"
            using terminal_unity terminal_char
            by (metis (mono_tags, lifting))
          have "Map f ` Dom unity = {Map f u}"
            using u by simp
          thus ?thesis
            using terminal_char by auto
        qed
        hence "MkIde (Map f ` Dom unity) \<in> Univ" by simp
        moreover have "MkIde (Map f ` Dom unity) = Img f"
          using f dom_char Img_def in_homE
          by (metis (mono_tags, lifting) Dom.simps(1) mem_Collect_eq)
        ultimately show "Img f \<in> Univ" by auto
      qed
      have "Img p = MkIde (Map p ` Dom p)" using Img_def by blast
      also have "... = MkIde (Map p ` {U})"
        using assms in_hom_char terminal_unity Dom_terminal
        by (metis (mono_tags, lifting))
      also have "... = (UP o Map p o DOWN) unity" by (simp add: UP_def)
      finally show "Img p = (UP o Map p o DOWN) unity" using assms by auto
    qed
  
    text\<open>
      The function @{term Img} is injective on @{term "hom unity a"} and its inverse takes
      a terminal object @{term t} to the arrow in @{term "hom unity a"} corresponding to the
      constant-@{term t} function.
\<close>

    abbreviation MkElem :: "'a setcat.arr => 'a setcat.arr => 'a setcat.arr"
    where "MkElem t a \<equiv> MkArr {U} (Dom a) (\<lambda>_ \<in> {U}. DOWN t)"

    lemma MkElem_in_hom:
    assumes "arr f" and "x \<in> Dom f"
    shows "\<guillemotleft>MkElem (UP x) (dom f) : unity \<rightarrow> dom f\<guillemotright>"
    proof -
      have "(\<lambda>_ \<in> {U}. DOWN (UP x)) \<in> {U} \<rightarrow> Dom (dom f)"
        using assms dom_char [of f] by simp
      moreover have "MkIde {U} = unity"
        using terminal_char terminal_unity
        by (metis (mono_tags, lifting) DOWN_UP UP_def)
      moreover have "MkIde (Dom (dom f)) = dom f"
        using assms dom_char MkIde_Dom' ide_dom by blast
      ultimately show ?thesis
        using assms MkArr_in_hom [of "{U}" "Dom (dom f)" "\<lambda>_ \<in> {U}. DOWN (UP x)"]
        by (metis (mono_tags, lifting) IntI restrict_extensional UNIV_I)
    qed

    lemma MkElem_Img:
    assumes "p \<in> hom unity a"
    shows "MkElem (Img p) a = p"
    proof -
      have 0: "Img p = UP (Map p U)"
        using assms Img_point(2) by auto
      have 1: "Dom p = {U}"
        using assms terminal_unity Dom_terminal
        by (metis (mono_tags, lifting) in_hom_char mem_Collect_eq)
      moreover have "Cod p = Dom a"
        using assms
        by (metis (mono_tags, lifting) in_hom_char mem_Collect_eq)
      moreover have "Map p = (\<lambda>_ \<in> {U}. DOWN (Img p))"
      proof
        fix e
        show "Map p e = (\<lambda>_ \<in> {U}. DOWN (Img p)) e"
        proof -
          have "Map p e = (\<lambda>x \<in> Dom p. Map p x) e"
            using assms MkArr_expansion [of p]
            by (metis (mono_tags, lifting) CollectD Map.simps(1) in_homE)
          also have "... = (\<lambda>_ \<in> {U}. DOWN (Img p)) e"
            using assms 0 1 by simp
          finally show ?thesis by blast
        qed
      qed
      ultimately show "MkElem (Img p) a = p"
        using assms MkArr_Map CollectD
        by (metis (mono_tags, lifting) in_homE mem_Collect_eq)
    qed

    lemma inj_Img:
    assumes "ide a"
    shows "inj_on Img (hom unity a)"
    proof (intro inj_onI)
      fix x y
      assume x: "x \<in> hom unity a"
      assume y: "y \<in> hom unity a"
      assume eq: "Img x = Img y"
      show "x = y"
      proof (intro arr_eqI)
        show "arr x" using x by blast
        show "arr y" using y by blast
        show "Dom x = Dom y"
          using x y in_hom_char by (metis (mono_tags, lifting) CollectD)
        show "Cod x = Cod y"
          using x y in_hom_char by (metis (mono_tags, lifting) CollectD)
        show "Map x = Map y"
        proof -
          have "Map x = (\<lambda>z \<in> {U}. Map x z) \<and> Map y = (\<lambda>z \<in> {U}. Map y z)"
            using x y \<open>arr x\<close> \<open>arr y\<close> Dom_terminal terminal_unity MkArr_expansion
            by (metis (mono_tags, lifting) CollectD Map.simps(1) in_hom_char)
          moreover have "Map x U = Map y U"
            using x y eq
            by (metis (mono_tags, lifting) CollectD Img_point(2) o_apply setcat.DOWN_UP)
          ultimately show ?thesis
            by (metis (mono_tags, lifting) restrict_ext singletonD)
        qed
      qed
    qed

    lemma set_char:
    assumes "ide a"
    shows "set a = UP ` Dom a"
    proof
      show "set a \<subseteq> UP ` Dom a"
      proof
        fix t
        assume "t \<in> set a"
        from this obtain p where p: "\<guillemotleft>p : unity \<rightarrow> a\<guillemotright> \<and> t = Img p"
          using set_def by blast
        have "t = (UP o Map p o DOWN) unity"
          using p Img_point(2) by blast
        moreover have "(Map p o DOWN) unity \<in> Dom a"
          using p arr_char in_hom_char Dom_terminal terminal_unity
          by (metis (mono_tags, lifting) IntD2 Pi_split_insert_domain o_apply)
        ultimately show "t \<in> UP ` Dom a" by simp
      qed
      show "UP ` Dom a \<subseteq> set a"
      proof
        fix t
        assume "t \<in> UP ` Dom a"
        from this obtain x where x: "x \<in> Dom a \<and> t = UP x" by blast
        let ?p = "MkElem (UP x) a"
        have p: "?p \<in> hom unity a"
          using assms x MkElem_in_hom [of "dom a"] ideD(1-2) by force
        moreover have "Img ?p = t"
          using p x DOWN_UP
          by (metis (no_types, lifting) Dom.simps(1) Map.simps(1) image_empty
              image_insert image_restrict_eq setcat.Img_def UP_def)
        ultimately show "t \<in> set a" using set_def by blast
      qed
    qed
  
    lemma Map_via_comp:
    assumes "arr f"
    shows "Map f = (\<lambda>x \<in> Dom f. Map (f \<cdot> MkElem (UP x) (dom f)) U)"
    proof
      fix x
      have "x \<notin> Dom f \<Longrightarrow> Map f x = (\<lambda>x \<in> Dom f. Map (f \<cdot> MkElem (UP x) (dom f)) U) x"
        using assms arr_char [of f] IntD1 extensional_arb restrict_apply by fastforce
      moreover have
           "x \<in> Dom f \<Longrightarrow> Map f x = (\<lambda>x \<in> Dom f. Map (f \<cdot> MkElem (UP x) (dom f)) U) x"
      proof -
        assume x: "x \<in> Dom f"
        let ?X = "MkElem (UP x) (dom f)"
        have "\<guillemotleft>?X : unity \<rightarrow> dom f\<guillemotright>"
          using assms x MkElem_in_hom by auto
        moreover have "Dom ?X = {U} \<and> Map ?X = (\<lambda>_ \<in> {U}. x)"
          using x by simp
        ultimately have
	    "Map (f \<cdot> MkElem (UP x) (dom f)) = compose {U} (Map f) (\<lambda>_ \<in> {U}. x)"
          using assms x Map_comp [of "MkElem (UP x) (dom f)" f]
          by (metis (mono_tags, lifting) Cod.simps(1) Dom_dom arr_iff_in_hom seqE seqI')
        thus ?thesis
          using x by (simp add: compose_eq restrict_apply' singletonI)
      qed
      ultimately show "Map f x = (\<lambda>x \<in> Dom f. Map (f \<cdot> MkElem (UP x) (dom f)) U) x"
        by auto
    qed

    lemma arr_eqI':
    assumes "par f f'" and "\<And>t. \<guillemotleft>t : unity \<rightarrow> dom f\<guillemotright> \<Longrightarrow> f \<cdot> t = f' \<cdot> t"
    shows "f = f'"
    proof (intro arr_eqI)
      show "arr f" using assms by simp
      show "arr f'" using assms by simp
      show "Dom f = Dom f'"
        using assms by (metis (mono_tags, lifting) Dom_dom)
      show "Cod f = Cod f'"
        using assms by (metis (mono_tags, lifting) Cod_cod)
      show "Map f = Map f'"
      proof
        have 1: "\<And>x. x \<in> Dom f \<Longrightarrow> \<guillemotleft>MkElem (UP x) (dom f) : unity \<rightarrow> dom f\<guillemotright>"
          using MkElem_in_hom by (metis (mono_tags, lifting) assms(1))
        fix x
        show "Map f x = Map f' x"
          using assms 1 \<open>Dom f = Dom f'\<close> by (simp add: Map_via_comp)
      qed
    qed
    
    text\<open>
      The main result, which establishes the consistency of the \<open>set_category\<close> locale
      and provides us with a way of obtaining ``set categories'' at arbitrary types.
\<close>

    theorem is_set_category:
    shows "set_category Comp"
    proof
      show "\<exists>img :: 'a setcat.arr \<Rightarrow> 'a setcat.arr. set_category_given_img Comp img"
      proof
        show "set_category_given_img (Comp :: 'a setcat.arr comp) Img"
        proof
          show "Univ \<noteq> {}" using terminal_char by blast
          fix a :: "'a setcat.arr"
          assume a: "ide a"
          show "Img \<in> hom unity a \<rightarrow> Univ" using Img_point terminal_unity by blast
          show "inj_on Img (hom unity a)" using a inj_Img terminal_unity by blast
          next
          fix t :: "'a setcat.arr"
          assume t: "terminal t"
          show "t \<in> Img ` hom unity t"
          proof -
            have "t \<in> set t"
              using t set_char [of t]
              by (metis (mono_tags, lifting) Dom.simps(1) image_insert insertI1 UP_def
                  terminal_char terminal_def)
            thus ?thesis
              using t set_def [of t] by simp
          qed
          next
          fix A :: "'a setcat.arr set"
          assume A: "A \<subseteq> Univ"
          show "\<exists>a. ide a \<and> set a = A"
          proof
            let ?a = "MkArr (DOWN ` A) (DOWN ` A) (\<lambda>x \<in> (DOWN ` A). x)"
            show "ide ?a \<and> set ?a = A"
            proof
              show 1: "ide ?a"
                using ide_char [of ?a] by simp
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
          fix a b :: "'a setcat.arr"
          assume a: "ide a" and b: "ide b" and ab: "set a = set b"
          show "a = b"
            using a b ab set_char inj_UP inj_image_eq_iff dom_char in_homE ide_in_hom
            by (metis (mono_tags, lifting))
          next
          fix f f' :: "'a setcat.arr"
          assume par: "par f f'" and ff': "\<And>x. \<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright> \<Longrightarrow> f \<cdot> x = f' \<cdot> x"
          show "f = f'" using par ff' arr_eqI' by blast
          next
          fix a b :: "'a setcat.arr" and F :: "'a setcat.arr \<Rightarrow> 'a setcat.arr"
          assume a: "ide a" and b: "ide b" and F: "F \<in> hom unity a \<rightarrow> hom unity b"
          show "\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright> \<longrightarrow> f \<cdot> x = F x)"
          proof
            let ?f = "MkArr (Dom a) (Dom b) (\<lambda>x \<in> Dom a. Map (F (MkElem (UP x) a)) U)"
            have 1: "\<guillemotleft>?f : a \<rightarrow> b\<guillemotright>"
            proof -
              have "(\<lambda>x \<in> Dom a. Map (F (MkElem (UP x) a)) U)
                      \<in> extensional (Dom a) \<inter> (Dom a \<rightarrow> Dom b)"
              proof
                show "(\<lambda>x \<in> Dom a. Map (F (MkElem (UP x) a)) U) \<in> extensional (Dom a)"
                  using a F by simp
                show "(\<lambda>x \<in> Dom a. Map (F (MkElem (UP x) a)) U) \<in> Dom a \<rightarrow> Dom b"
                proof
                  fix x
                  assume x: "x \<in> Dom a"
                  have "MkElem (UP x) a \<in> hom unity a"
                    using x a MkElem_in_hom [of a x] ide_char ideD(1-2) by force
                  hence 1: "F (MkElem (UP x) a) \<in> hom unity b"
                    using F by auto
                  moreover have "Dom (F (MkElem (UP x) a)) = {U}"
                    using 1 MkElem_Img
                    by (metis (mono_tags, lifting) Dom.simps(1))
                  moreover have "Cod (F (MkElem (UP x) a)) = Dom b"
                    using 1 by (metis (mono_tags, lifting) CollectD in_hom_char)
                  ultimately have "Map (F (MkElem (UP x) a)) \<in> {U} \<rightarrow> Dom b"
                    using arr_char [of "F (MkElem (UP x) a)"] by blast
                  thus "Map (F (MkElem (UP x) a)) U \<in> Dom b" by blast
                qed
              qed
              hence "\<guillemotleft>?f : MkIde (Dom a) \<rightarrow> MkIde (Dom b)\<guillemotright>"
                using a b MkArr_in_hom by blast
              thus ?thesis
                using a b by simp
            qed
            moreover have "\<And>x. \<guillemotleft>x : unity \<rightarrow> dom ?f\<guillemotright> \<Longrightarrow> ?f \<cdot> x = F x"
            proof -
              fix x
              assume x: "\<guillemotleft>x : unity \<rightarrow> dom ?f\<guillemotright>"
              have 2: "x = MkElem (Img x) a"
                using a x 1 MkElem_Img [of x a]
                by (metis (mono_tags, lifting) in_homE mem_Collect_eq)
              moreover have 5: "Dom x = {U} \<and> Cod x = Dom a \<and>
                                Map x = (\<lambda>_ \<in> {U}. DOWN (Img x))"
                using x 2
                by (metis (no_types, lifting) Cod.simps(1) Dom.simps(1) Map.simps(1))
              moreover have "Cod ?f = Dom b" using 1 by simp
              ultimately have
                   3: "?f \<cdot> x =
                       MkArr {U} (Dom b) (compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)))"
                using 1 x comp_char [of ?f "MkElem (Img x) a"]
                by (metis (mono_tags, lifting) in_homE seqI)
              have 4: "compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) = Map (F x)"
              proof
                fix y
                have "y \<notin> {U} \<Longrightarrow>
                        compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) y = Map (F x) y"
                proof -
                  assume y: "y \<notin> {U}"
                  have "compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) y = undefined"
                    using y compose_def extensional_arb by simp
                  also have "... = Map (F x) y"
                  proof -
                    have 5: "F x \<in> hom unity b" using x F 1 by fastforce
                    hence "Dom (F x) = {U}"
                      by (metis (mono_tags, lifting) "2" CollectD Dom.simps(1) in_hom_char x)
                    thus ?thesis
                      using x y F 5 arr_char [of "F x"] extensional_arb [of "Map (F x)" "{U}" y]
                      by (metis (mono_tags, lifting) CollectD Int_iff in_hom_char)
                  qed
                  ultimately show ?thesis by auto
                qed
                moreover have
                    "y \<in> {U} \<Longrightarrow>
                       compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) y = Map (F x) y"
                proof -
                  assume y: "y \<in> {U}"
                  have "compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) y =
                        Map ?f (DOWN (Img x))"
                    using y by (simp add: compose_eq restrict_apply')
                  also have "... = (\<lambda>x. Map (F (MkElem (UP x) a)) U) (DOWN (Img x))"
                  proof -
                    have "DOWN (Img x) \<in> Dom a"
                      using x y a 5 arr_char in_homE restrict_apply
                      by (metis (mono_tags, lifting) IntD2 PiE)
                    thus ?thesis
                      using restrict_apply by simp
                  qed
                  also have "... = Map (F x) y"
                    using x y 1 2 MkElem_Img [of x a] by simp
                  finally show
                      "compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) y = Map (F x) y"
                    by auto
                qed
                ultimately show
                    "compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (Img x)) y = Map (F x) y"
                  by auto
              qed
              show "?f \<cdot> x = F x"
              proof (intro arr_eqI)
                have 5: "?f \<cdot> x \<in> hom unity b" using 1 x by blast
                have 6: "F x \<in> hom unity b"
                  using x F 1
                  by (metis (mono_tags, lifting) PiE in_homE mem_Collect_eq)
                show "arr (Comp ?f x)" using 5 by blast
                show "arr (F x)" using 6 by blast
                show "Dom (Comp ?f x) = Dom (F x)"
                  using 5 6 by (metis (mono_tags, lifting) CollectD in_hom_char)
                show "Cod (Comp ?f x) = Cod (F x)"
                  using 5 6 by (metis (mono_tags, lifting) CollectD in_hom_char)
                show "Map (Comp ?f x) = Map (F x)"
                  using 3 4 by simp
              qed
            qed
            thus "\<guillemotleft>?f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> dom ?f\<guillemotright> \<longrightarrow> Comp ?f x = F x)"
              using 1 by blast
          qed
        qed
      qed
    qed

    text\<open>
      \<open>SetCat\<close> can be viewed as a concrete set category over its own element type
      @{typ 'a}, using @{term UP} as the required injection from @{typ 'a} to the universe
      of \<open>SetCat\<close>.
\<close>

    corollary is_concrete_set_category:
    shows "concrete_set_category Comp Univ UP"
    proof -
      interpret S: set_category Comp using is_set_category by auto
      show ?thesis
      proof
        show 1: "UP \<in> Univ \<rightarrow> S.Univ"
          using UP_def terminal_char by force
        show "inj_on UP Univ"
          by (metis (mono_tags, lifting) injD inj_UP inj_onI)
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
    shows "\<exists>\<Phi>. invertible_functor S (Comp :: 'a setcat.arr comp) \<Phi>
                 \<and> (\<forall>m. set_category.incl S m \<longrightarrow> set_category.incl Comp (\<Phi> m))"
    proof -
      interpret S: set_category S using assms by auto
      let ?\<psi> = "inv_into S.Univ \<phi>"
      have "bij_betw (UP o \<phi>) S.Univ (Collect terminal)"
      proof (intro bij_betwI)
        show "UP o \<phi> \<in> S.Univ \<rightarrow> Collect terminal"
          using assms(2) UP_mapsto by auto
        show "?\<psi> o DOWN \<in> Collect terminal \<rightarrow> S.Univ"
        proof
          fix x :: "'a setcat.arr"
          assume x: "x \<in> Univ"
          show "(inv_into S.Univ \<phi> \<circ> DOWN) x \<in> S.Univ"
            using x assms(2) bij_betw_def comp_apply inv_into_into
            by (metis UNIV_I)
        qed
        fix t
        assume "t \<in> S.Univ"
        thus "(?\<psi> o DOWN) ((UP o \<phi>) t) = t"
          using assms(2) bij_betw_inv_into_left
          by (metis comp_apply DOWN_UP)
        next
        fix t' :: "'a setcat.arr"
        assume "t' \<in> Collect terminal"
        thus "(UP o \<phi>) ((?\<psi> o DOWN) t') = t'"
          using assms(2) by (simp add: bij_betw_def f_inv_into_f)
      qed
      thus ?thesis
        using assms(1) set_category_is_categorical [of S Comp "UP o \<phi>"] is_set_category
        by auto
    qed

  end

  text \<open>
    The following context defines the entities that are intended to be exported
    from this theory.  The idea is to avoid exposing as little detail about the
    construction used in the @{locale setcat} locale as possible, so that proofs
    using the result of that construction will depend only on facts proved from
    axioms in the @{locale set_category} locale and not on concrete details from
    the construction of the interpretation.
\<close>

  context
  begin

    interpretation S: setcat .

    definition comp
    where "comp \<equiv> S.Comp"

    interpretation set_category comp
      unfolding comp_def using S.is_set_category by simp

    lemma is_set_category:
    shows "set_category comp"
      ..

    definition DOWN
    where "DOWN = S.DOWN"

    definition UP
    where "UP = S.UP"

    lemma UP_mapsto:
    shows "UP \<in> UNIV \<rightarrow> Univ"
      using S.UP_mapsto
      by (simp add: UP_def comp_def)

    lemma DOWN_mapsto:
    shows "DOWN \<in> Univ \<rightarrow> UNIV"
      by auto

    lemma DOWN_UP [simp]:
    shows "DOWN (UP x) = x"
      by (simp add: DOWN_def UP_def)

    lemma UP_DOWN [simp]:
    assumes "t \<in> Univ"
    shows "UP (DOWN t) = t"
      using assms DOWN_def UP_def
      by (simp add: DOWN_def UP_def comp_def)

    lemma inj_UP:
    shows "inj UP"
      by (metis DOWN_UP injI)
  
    lemma bij_UP:
    shows "bij_betw UP UNIV Univ"
      by (metis S.bij_UP UP_def comp_def)

  end

end

