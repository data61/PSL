(*  Title:       SetCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter SetCategory

theory SetCategory
imports Category Functor
begin

  text\<open>
    This theory defines a locale \<open>set_category\<close> that axiomatizes the notion
    ``category of all @{typ 'a}-sets and functions between them'' in the context of HOL.
    A primary reason for doing this is to make it possible to prove results
    (such as the Yoneda Lemma) that use such categories without having to commit to a
    particular element type @{typ 'a} and without having the results depend on the
    concrete details of a particular construction.
    The axiomatization given here is categorical, in the sense that if categories
    @{term S} and @{term S'} each interpret the \<open>set_category\<close> locale,
    then a bijection between the sets of terminal objects of @{term S} and @{term S'}
    extends to an isomorphism of @{term S} and @{term S'} as categories.

    The axiomatization is based on the following idea: if, for some type @{typ 'a},
    category @{term S} is the category of all @{typ 'a}-sets and functions between
    them, then the elements of type @{typ 'a} are in bijective correspondence with
    the terminal objects of category @{term S}.  In addition, if @{term unity}
    is an arbitrarily chosen terminal object of @{term S}, then for each object @{term a},
    the hom-set @{term "hom unity a"} (\emph{i.e.} the set of ``points'' or
    ``global elements'' of @{term a}) is in bijective correspondence with a subset
    of the terminal objects of @{term S}.  By making a specific, but arbitrary,
    choice of such a correspondence, we can then associate with each object @{term a}
    of @{term S} a set @{term "set a"} that consists of all terminal objects @{term t}
    that correspond to some point @{term x} of @{term a}.  Each arrow @{term f}
    then induces a function \<open>Fun f \<in> set (dom f) \<rightarrow> set (cod f)\<close>,
    defined on terminal objects of @{term S} by passing to points of @{term "dom f"},
    composing with @{term f}, then passing back from points of @{term "cod f"}
    to terminal objects.  Once we can associate a set with each object of @{term S}
    and a function with each arrow, we can force @{term S} to be isomorphic to the
    category of @{typ 'a}-sets by imposing suitable extensionality and completeness axioms.
\<close>
 
  section "Some Lemmas about Restriction"

    text\<open>
      The development of the \<open>set_category\<close> locale makes heavy use of the
      theory @{theory "HOL-Library.FuncSet"}.  However, in some cases, I found that
      @{theory "HOL-Library.FuncSet"} did not provide results about restriction in the form that was
      most useful to me. I used the following additional results in various places.
\<close>

  (* This variant of FuncSet.restrict_ext is sometimes useful. *)

  lemma restr_eqI:
  assumes "A = A'" and "\<And>x. x \<in> A \<Longrightarrow> F x = F' x"
  shows "restrict F A = restrict F' A'"
    using assms by force

  (* This rule avoided a long proof in at least one instance
     where FuncSet.restrict_apply did not work.
   *)
  lemma restr_eqE [elim]:
  assumes "restrict F A = restrict F' A" and "x \<in> A"
  shows "F x = F' x"
    using assms restrict_def by metis

  (* This seems more useful than compose_eq in FuncSet. *)
  lemma compose_eq' [simp]:
  shows "compose A G F = restrict (G o F) A"
    unfolding compose_def restrict_def by auto

  section "Set Categories"

  text\<open>
    We first define the locale \<open>set_category_data\<close>, which sets out the basic
    data and definitions for the \<open>set_category\<close> locale, without imposing any conditions
    other than that @{term S} is a category and that @{term img} is a function defined
    on the arrow type of @{term S}.  The function @{term img} should be thought of
    as a mapping that takes a point @{term "x \<in> hom unity a"} to a corresponding
    terminal object @{term "img x"}.  Eventually, assumptions will be introduced so
    that this is in fact the case.
\<close>

  locale set_category_data = category S
  for S :: "'s comp"      (infixr "\<cdot>" 55)
  and img :: "'s \<Rightarrow> 's"
  begin

    notation in_hom       ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    text\<open>
      Call the set of all terminal objects of S the ``universe''.
\<close>
    abbreviation Univ :: "'s set"
    where "Univ \<equiv> Collect terminal"
  
    text\<open>
      Choose an arbitrary element of the universe and call it @{term unity}.
\<close>
    definition unity :: 's
    where "unity = (SOME t. terminal t)"
    
    text\<open>
      Each object @{term a} determines a subset @{term "set a"} of the universe,
      consisting of all those terminal objects @{term t} such that @{term "t = img x"}
      for some @{term "x \<in> hom unity a"}.
\<close>
    definition set :: "'s \<Rightarrow> 's set"
    where "set a = img ` hom unity a"

    text\<open>
      The inverse of the map @{term set} is a map @{term mkIde} that takes each subset
      of the universe to an identity of @{term[source=true] S}.
\<close>
    definition mkIde :: "'s set \<Rightarrow> 's"
    where "mkIde A = (if A \<subseteq> Univ then inv_into (Collect ide) set A else null)"

  end

  text\<open>
    Next, we define a locale \<open>set_category_given_img\<close> that augments the
    \<open>set_category_data\<close> locale with assumptions that serve to define
    the notion of a set category with a chosen correspondence between points
    and terminal objects.  The assumptions require that the universe be nonempty
    (so that the definition of @{term unity} makes sense), that the map
    @{term img} is a locally injective map taking points to terminal objects,
    that each terminal object @{term t} belongs to @{term "set t"},
    that two objects of @{term S} are equal if they determine the same set,
    that two parallel arrows of @{term S} are equal if they determine the same
    function, that there is an object corresponding to each subset of the universe,
    and for any objects @{term a} and @{term b} and function
    @{term "F \<in> hom unity a \<rightarrow> hom unity b"} there is an arrow @{term "f \<in> hom a b"}
    whose action under the composition of @{term S} coincides with the function @{term F}.
\<close>
    
  locale set_category_given_img = set_category_data S img
  for S :: "'s comp"      (infixr "\<cdot>" 55)
  and img :: "'s \<Rightarrow> 's" +
  assumes nonempty_Univ: "Univ \<noteq> {}"
  and img_mapsto: "ide a \<Longrightarrow> img \<in> hom unity a \<rightarrow> Univ"
  and inj_img: "ide a \<Longrightarrow> inj_on img (hom unity a)"
  and stable_img: "terminal t \<Longrightarrow> t \<in> img ` hom unity t"
  and extensional_set: "\<lbrakk> ide a; ide b; set a = set b \<rbrakk> \<Longrightarrow> a = b"
  and extensional_arr: "\<lbrakk> par f f'; \<And>x. \<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright> \<Longrightarrow> f \<cdot> x = f' \<cdot> x \<rbrakk> \<Longrightarrow> f = f'"
  and set_complete: "A \<subseteq> Univ \<Longrightarrow> \<exists>a. ide a \<and> set a = A"
  and fun_complete1: "\<lbrakk> ide a; ide b; F \<in> hom unity a \<rightarrow> hom unity b \<rbrakk>
                          \<Longrightarrow> \<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright> \<longrightarrow> f \<cdot> x = F x)"
  begin
  
    text\<open>
      Each arrow @{term "f \<in> hom a b"} determines a function @{term "Fun f \<in> Univ \<rightarrow> Univ"},
      by passing from @{term Univ} to @{term "hom a unity"}, composing with @{term f},
      then passing back to @{term Univ}.
\<close>

    definition Fun :: "'s \<Rightarrow> 's \<Rightarrow> 's"
    where "Fun f = restrict (img o S f o inv_into (hom unity (dom f)) img) (set (dom f))"

    lemma comp_arr_point:
    assumes "arr f" and "\<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright>"
    shows "f \<cdot> x = inv_into (hom unity (cod f)) img (Fun f (img x))"
    proof -
      have "\<guillemotleft>f \<cdot> x : unity \<rightarrow> cod f\<guillemotright>"
        using assms by blast
      thus ?thesis
        using assms Fun_def inj_img set_def by simp
    qed
      
    text\<open>
      Parallel arrows that determine the same function are equal.
\<close>

    lemma arr_eqI:
    assumes "par f f'" and "Fun f = Fun f'"
    shows "f = f'"
      using assms comp_arr_point extensional_arr by metis

    lemma terminal_unity:
    shows "terminal unity"
      using unity_def nonempty_Univ by (simp add: someI_ex)

    lemma ide_unity [simp]:
    shows "ide unity"
      using terminal_unity terminal_def by blast

    lemma set_subset_Univ [simp]:
    assumes "ide a"
    shows "set a \<subseteq> Univ"
      using assms set_def img_mapsto by auto
  
    lemma inj_on_set:
    shows "inj_on set (Collect ide)"
      using extensional_set by (intro inj_onI, auto)
      
    text\<open>
      The mapping @{term mkIde}, which takes subsets of the universe to identities,
      and @{term set}, which takes identities to subsets of the universe, are inverses.
\<close>

    lemma mkIde_set [simp]:
    assumes "ide a"
    shows "mkIde (set a) = a"
      using assms mkIde_def inj_on_set inv_into_f_f by simp

    lemma set_mkIde [simp]:
    assumes "A \<subseteq> Univ"
    shows "set (mkIde A) = A"
      using assms mkIde_def set_complete someI_ex [of "\<lambda>a. a \<in> Collect ide \<and> set a = A"]
      by (simp add: inv_into_def)
      
    lemma ide_mkIde [simp]:
    assumes "A \<subseteq> Univ"
    shows "ide (mkIde A)"
      using assms mkIde_def mkIde_set set_complete by metis
      
    lemma arr_mkIde [iff]:
    shows "arr (mkIde A) \<longleftrightarrow> A \<subseteq> Univ"
      using not_arr_null mkIde_def ide_mkIde by auto
    
    lemma dom_mkIde [simp]:
    assumes "A \<subseteq> Univ"
    shows "dom (mkIde A) = mkIde A"
      using assms ide_mkIde by simp
    
    lemma cod_mkIde [simp]:
    assumes "A \<subseteq> Univ"
    shows "cod (mkIde A) = mkIde A"
      using assms ide_mkIde by simp
      
    text\<open>
      Each arrow @{term f} determines an extensional function from
      @{term "set (dom f)"} to @{term "set (cod f)"}.
\<close>

    lemma Fun_mapsto:
    assumes "arr f"
    shows "Fun f \<in> extensional (set (dom f)) \<inter> (set (dom f) \<rightarrow> set (cod f))"
    proof
      show "Fun f \<in> extensional (set (dom f))" using Fun_def by fastforce
      show "Fun f \<in> set (dom f) \<rightarrow> set (cod f)"
      proof
        fix t
        assume t: "t \<in> set (dom f)"
        have "Fun f t = img (f \<cdot> inv_into (hom unity (dom f)) img t)"
          using assms t Fun_def comp_def by simp
        moreover have "... \<in> set (cod f)"
          using assms t set_def inv_into_into [of t img "hom unity (dom f)"] by blast
        ultimately show "Fun f t \<in> set (cod f)" by auto
      qed
    qed
    
    text\<open>
      Identities of @{term[source=true] S} correspond to restrictions of the identity function.
\<close>

    lemma Fun_ide [simp]:
    assumes "ide a"
    shows "Fun a = restrict (\<lambda>x. x) (set a)"
      using assms Fun_def inj_img set_def comp_cod_arr by fastforce
    
    lemma Fun_mkIde [simp]:
    assumes "A \<subseteq> Univ"
    shows "Fun (mkIde A) = restrict (\<lambda>x. x) A"
      using assms by simp
    
    text\<open>
      Composition in @{term S} corresponds to extensional function composition.
\<close>

    lemma Fun_comp [simp]:
    assumes "seq g f"
    shows "Fun (g \<cdot> f) = restrict (Fun g o Fun f) (set (dom f))"
    proof -
      have "restrict (img o S (g \<cdot> f) o (inv_into (hom unity (dom (g \<cdot> f))) img))
                     (set (dom (g \<cdot> f)))
              = restrict (Fun g o Fun f) (set (dom f))"
      proof -
        have 1: "set (dom (g \<cdot> f)) = set (dom f)"
          using assms by auto
        let ?img' = "\<lambda>a. \<lambda>t. inv_into (hom unity a) img t"
        have 2: "\<And>t. t \<in> set (dom (g \<cdot> f)) \<Longrightarrow>
                     (img o S (g \<cdot> f) o ?img' (dom (g \<cdot> f))) t = (Fun g o Fun f) t"
        proof -
          fix t
          assume "t \<in> set (dom (g \<cdot> f))"
          hence t: "t \<in> set (dom f)" by (simp add: 1)
          have 3: "\<And>a x. x \<in> hom unity a \<Longrightarrow> ?img' a (img x) = x"
            using assms img_mapsto inj_img ide_cod inv_into_f_eq
            by (metis arrI in_homE mem_Collect_eq)
          have 4: "?img' (dom f) t \<in> hom unity (dom f)"
            using assms t inv_into_into [of t img "hom unity (dom f)"] set_def by simp
          have "(img o S (g \<cdot> f) o ?img' (dom (g \<cdot> f))) t = img (g \<cdot> f \<cdot> ?img' (dom f) t)"
            using assms dom_comp comp_assoc by simp
          also have "... = img (g \<cdot> ?img' (dom g) (Fun f t))"
            using assms t 3 Fun_def set_def comp_arr_point by auto
          also have "... = Fun g (Fun f t)"
          proof -
            have "Fun f t \<in> img ` hom unity (cod f)"
              using assms t Fun_mapsto set_def by fast
            thus ?thesis using assms by (auto simp add: set_def Fun_def)
          qed
          finally show "(img o S (g \<cdot> f) o ?img' (dom (g \<cdot> f))) t = (Fun g o Fun f) t"
            by auto
        qed
        show ?thesis using 1 2 by auto
      qed
      thus ?thesis using Fun_def by auto
    qed

    text\<open>
      The constructor @{term mkArr} is used to obtain an arrow given subsets
      @{term A} and @{term B} of the universe and a function @{term "F \<in> A \<rightarrow> B"}.
\<close>
    
    definition mkArr :: "'s set \<Rightarrow> 's set \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> 's"
    where "mkArr A B F = (if A \<subseteq> Univ \<and> B \<subseteq> Univ \<and> F \<in> A \<rightarrow> B
                          then (THE f. f \<in> hom (mkIde A) (mkIde B) \<and> Fun f = restrict F A)
                          else null)"

    text\<open>
      Each function @{term "F \<in> set a \<rightarrow> set b"} determines a unique arrow @{term "f \<in> hom a b"},
      such that @{term "Fun f"} is the restriction of @{term F} to @{term "set a"}.
\<close>

    lemma fun_complete:
    assumes "ide a" and "ide b" and "F \<in> set a \<rightarrow> set b"
    shows "\<exists>!f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> Fun f = restrict F (set a)"
    proof -
      let ?P = "\<lambda>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> Fun f = restrict F (set a)"
      show "\<exists>!f. ?P f"
      proof
        have "\<exists>f. ?P f"
        proof -
          let ?F' = "\<lambda>x. inv_into (hom unity b) img (F (img x))"
          have "?F' \<in> hom unity a \<rightarrow> hom unity b"
          proof
            fix x
            assume x: "x \<in> hom unity a"
            have "F (img x) \<in> set b" using assms(3) x set_def by auto
            thus "inv_into (hom unity b) img (F (img x)) \<in> hom unity b"
              using assms img_mapsto inj_img set_def by auto
          qed
          hence "\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<longrightarrow> f \<cdot> x = ?F' x)"
            using assms fun_complete1 by force
          from this obtain f where f: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<longrightarrow> f \<cdot> x = ?F' x)"
            by blast
          let ?img' = "\<lambda>a. \<lambda>t. inv_into (hom unity a) img t"
          have "Fun f = restrict F (set a)"
          proof (unfold Fun_def, intro restr_eqI)
            show "set (dom f) = set a" using f by auto
            show "\<And>t. t \<in> set (dom f) \<Longrightarrow> (img \<circ> S f \<circ> ?img' (dom f)) t = F t"
            proof -
              fix t
              assume t: "t \<in> set (dom f)"
              have "(img \<circ> S f \<circ> ?img' (dom f)) t = img (f \<cdot> ?img' (dom f) t)"
                by simp
              also have "... = img (?F' (?img' (dom f) t))"
              proof -
                have "?img' (dom f) t \<in> hom unity (dom f)"
                  using t set_def inv_into_into by metis
                thus ?thesis using f by auto
              qed
              also have "... = img (?img' (cod f) (F t))"
                using f t set_def inj_img by auto
              also have "... = F t"
              proof -
                have "F t \<in> set (cod f)"
                  using assms f t by auto
                thus ?thesis
                  using f t set_def inj_img by auto
              qed
              finally show "(img \<circ> S f \<circ> ?img' (dom f)) t = F t" by auto
            qed
          qed
          thus ?thesis using f by blast
        qed
        thus F: "?P (SOME f. ?P f)" using someI_ex [of ?P] by fast
        show "\<And>f'. ?P f' \<Longrightarrow> f' = (SOME f. ?P f)"
          using F arr_eqI
          by (metis (no_types, lifting) in_homE)
      qed
    qed
                          
    lemma mkArr_in_hom:
    assumes "A \<subseteq> Univ" and "B \<subseteq> Univ" and "F \<in> A \<rightarrow> B"
    shows "\<guillemotleft>mkArr A B F : mkIde A \<rightarrow> mkIde B\<guillemotright>"
      using assms mkArr_def fun_complete [of "mkIde A" "mkIde B" F]
            theI' [of "\<lambda>f. f \<in> hom (mkIde A) (mkIde B) \<and> Fun f = restrict F A"]
      by simp

    text\<open>
      The ``only if'' direction of the next lemma can be achieved only if there exists a
      non-arrow element of type @{typ 's}, which can be used as the value of @{term "mkArr A B F"}
      in cases where @{term "F \<notin> A \<rightarrow> B"}.  Nevertheless, it is essential to have this,
      because without the ``only if'' direction, we can't derive any useful
      consequences from an assumption of the form @{term "arr (mkArr A B F)"};
      instead we have to obtain @{term "F \<in> A \<rightarrow> B"} some other way.
      This is is usually highly inconvenient and it makes the theory very weak and almost
      unusable in practice.  The observation that having a non-arrow value of type @{typ 's}
      solves this problem is ultimately what led me to incorporate @{term null} first into the
      definition of the \<open>set_category\<close> locale and then, ultimately, into the definition
      of the \<open>category\<close> locale.  I believe this idea is critical to the usability of the
      entire development.
\<close>

    (* TODO: This gets used as an introduction rule, but the conjunction on the right-hand side
       is not very convenient. *)
    lemma arr_mkArr [iff]:
    shows "arr (mkArr A B F) \<longleftrightarrow> A \<subseteq> Univ \<and> B \<subseteq> Univ \<and> F \<in> A \<rightarrow> B"
    proof
      show "arr (mkArr A B F) \<Longrightarrow> A \<subseteq> Univ \<and> B \<subseteq> Univ \<and> F \<in> A \<rightarrow> B"
        using mkArr_def not_arr_null ex_un_null someI_ex [of "\<lambda>f. \<not>arr f"] by metis
      show "A \<subseteq> Univ \<and> B \<subseteq> Univ \<and> F \<in> A \<rightarrow> B \<Longrightarrow> arr (mkArr A B F)"
        using mkArr_in_hom by auto
    qed
    
    lemma Fun_mkArr':
    assumes "arr (mkArr A B F)"
    shows "\<guillemotleft>mkArr A B F : mkIde A \<rightarrow> mkIde B\<guillemotright>"
    and "Fun (mkArr A B F) = restrict F A"
    proof -
      have 1: "A \<subseteq> Univ \<and> B \<subseteq> Univ \<and> F \<in> A \<rightarrow> B" using assms by fast
      have 2: "mkArr A B F \<in> hom (mkIde A) (mkIde B) \<and>
                     Fun (mkArr A B F) = restrict F (set (mkIde A))"
      proof -
        have "\<exists>!f. f \<in> hom (mkIde A) (mkIde B) \<and> Fun f = restrict F (set (mkIde A))"
          using 1 fun_complete [of "mkIde A" "mkIde B" F] by simp
        thus ?thesis using 1 mkArr_def theI' by simp
      qed
      show "\<guillemotleft>mkArr A B F : mkIde A \<rightarrow> mkIde B\<guillemotright>" using 1 2 by auto
      show "Fun (mkArr A B F) = restrict F A" using 1 2 by auto
    qed

    lemma mkArr_Fun [simp]:
    assumes "arr f"
    shows "mkArr (set (dom f)) (set (cod f)) (Fun f) = f"
    proof -
      have 1: "set (dom f) \<subseteq> Univ \<and> set (cod f) \<subseteq> Univ \<and> ide (dom f) \<and> ide (cod f) \<and>
               Fun f \<in> extensional (set (dom f)) \<inter> (set (dom f) \<rightarrow> set (cod f))"
        using assms Fun_mapsto by force
      hence "\<exists>!f'. f' \<in> hom (dom f) (cod f) \<and> Fun f' = restrict (Fun f) (set (dom f))"
        using fun_complete by force
      moreover have "f \<in> hom (dom f) (cod f) \<and> Fun f = restrict (Fun f) (set (dom f))"
        using assms 1 extensional_restrict by force
      ultimately have "f = (THE f'. f' \<in> hom (dom f) (cod f) \<and>
                                    Fun f' = restrict (Fun f) (set (dom f)))"
        using theI' [of "\<lambda>f'. f' \<in> hom (dom f) (cod f) \<and> Fun f' = restrict (Fun f) (set (dom f))"]
        by blast
      also have "... = mkArr (set (dom f)) (set (cod f)) (Fun f)"
        using assms 1 mkArr_def by simp
      finally show ?thesis by auto
    qed
    
    lemma dom_mkArr [simp]:
    assumes "arr (mkArr A B F)"
    shows "dom (mkArr A B F) = mkIde A"
      using assms Fun_mkArr' by auto
        
    lemma cod_mkArr [simp]:
    assumes "arr (mkArr A B F)"
    shows "cod (mkArr A B F) = mkIde B"
      using assms Fun_mkArr' by auto
     
    lemma Fun_mkArr [simp]:
    assumes "arr (mkArr A B F)"
    shows "Fun (mkArr A B F) = restrict F A"
      using assms Fun_mkArr' by auto

    text\<open>
      The following provides the basic technique for showing that arrows
      constructed using @{term mkArr} are equal.
\<close>

    lemma mkArr_eqI [intro]:
    assumes "arr (mkArr A B F)"
    and "A = A'" and "B = B'" and "\<And>x. x \<in> A \<Longrightarrow> F x = F' x"
    shows "mkArr A B F = mkArr A' B' F'"
      using assms arr_mkArr Fun_mkArr
      by (intro arr_eqI, auto simp add: Pi_iff)

    text\<open>
      This version avoids trivial proof obligations when the domain and codomain
      sets are identical from the context.
\<close>
    
    lemma mkArr_eqI' [intro]:
    assumes "arr (mkArr A B F)" and "\<And>x. x \<in> A \<Longrightarrow> F x = F' x"
    shows "mkArr A B F = mkArr A B F'"
      using assms mkArr_eqI by simp
    
    lemma mkArr_restrict_eq [simp]:
    assumes "arr (mkArr A B F)"
    shows "mkArr A B (restrict F A) = mkArr A B F"
      using assms by (intro mkArr_eqI', auto)
      
    lemma mkArr_restrict_eq':
    assumes "arr (mkArr A B (restrict F A))"
    shows "mkArr A B (restrict F A) = mkArr A B F"
      using assms by (intro mkArr_eqI', auto)
      
    lemma mkIde_as_mkArr [simp]:
    assumes "A \<subseteq> Univ"
    shows "mkArr A A (\<lambda>x. x) = mkIde A"
      using assms by (intro arr_eqI, auto)

    lemma comp_mkArr [simp]:
    assumes "arr (mkArr A B F)" and "arr (mkArr B C G)"
    shows "mkArr B C G \<cdot> mkArr A B F = mkArr A C (G \<circ> F)"
    proof (intro arr_eqI)
      have 1: "seq (mkArr B C G) (mkArr A B F)" using assms by force
      have 2: "G o F \<in> A \<rightarrow> C" using assms by auto
      show "par (mkArr B C G \<cdot> mkArr A B F) (mkArr A C (G \<circ> F))"
        using 1 2 by auto
      show "Fun (mkArr B C G \<cdot> mkArr A B F) = Fun (mkArr A C (G \<circ> F))"
        using 1 2 by fastforce
    qed
    
    text\<open>
      The locale assumption @{prop stable_img} forces @{term "t \<in> set t"} in case
      @{term t} is a terminal object.  This is very convenient, as it results in the
      characterization of terminal objects as identities @{term t} for which
      @{term "set t = {t}"}.  However, it is not absolutely necessary to have this.
      The following weaker characterization of terminal objects can be proved without
      the @{prop stable_img} assumption.
\<close>

    lemma terminal_char1:
    shows "terminal t \<longleftrightarrow> ide t \<and> (\<exists>!x. x \<in> set t)"
    proof -
      have "terminal t \<Longrightarrow> ide t \<and> (\<exists>!x. x \<in> set t)"
      proof -
        assume t: "terminal t"
        have "ide t" using t terminal_def by auto
        moreover have "\<exists>!x. x \<in> set t"
        proof -
          have "\<exists>!x. x \<in> hom unity t"
            using t terminal_unity terminal_def by auto
          thus ?thesis using set_def by auto
        qed
        ultimately show "ide t \<and> (\<exists>!x. x \<in> set t)" by auto
      qed
      moreover have "ide t \<and> (\<exists>!x. x \<in> set t) \<Longrightarrow> terminal t"
      proof -
        assume t: "ide t \<and> (\<exists>!x. x \<in> set t)"
        from this obtain t' where "set t = {t'}" by blast
        hence t': "set t = {t'} \<and> {t'} \<subseteq> Univ \<and> t = mkIde {t'}"
          using t set_subset_Univ mkIde_set by metis
        show "terminal t"
        proof
          show "ide t" using t by simp
          show "\<And>a. ide a \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> t\<guillemotright>"
          proof -
            fix a
            assume a: "ide a"
            show "\<exists>!f. \<guillemotleft>f : a \<rightarrow> t\<guillemotright>"
            proof
              show 1: "\<guillemotleft>mkArr (set a) {t'} (\<lambda>x. t') : a \<rightarrow> t\<guillemotright>"
                using a t t' mkArr_in_hom
                by (metis Pi_I' mkIde_set set_subset_Univ singletonD)
              show "\<And>f. \<guillemotleft>f : a \<rightarrow> t\<guillemotright> \<Longrightarrow> f = mkArr (set a) {t'} (\<lambda>x. t')"
              proof -
                fix f
                assume f: "\<guillemotleft>f : a \<rightarrow> t\<guillemotright>"
                show "f = mkArr (set a) {t'} (\<lambda>x. t')"
                proof (intro arr_eqI)
                  show 1: "par f (mkArr (set a) {t'} (\<lambda>x. t'))" using 1 f in_homE by metis
                  show "Fun f = Fun (mkArr (set a) {t'} (\<lambda>x. t'))"
                  proof -
                    have "Fun (mkArr (set a) {t'} (\<lambda>x. t')) = (\<lambda>x\<in>set a. t')"
                      using 1 Fun_mkArr by simp
                    also have "... = Fun f"
                    proof -
                      have "\<And>x. x \<in> set a \<Longrightarrow> Fun f x = t'"
                        using f t' Fun_def mkArr_Fun arr_mkArr
                        by (metis PiE in_homE singletonD)
                      moreover have "\<And>x. x \<notin> set a \<Longrightarrow> Fun f x = undefined"
                        using f Fun_def by auto
                      ultimately show ?thesis by auto
                    qed
                    finally show ?thesis by force
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
      ultimately show ?thesis by blast
    qed
    
    text\<open>
      As stated above, in the presence of the @{prop stable_img} assumption we have
      the following stronger characterization of terminal objects.
\<close>

    lemma terminal_char2:
    shows "terminal t \<longleftrightarrow> ide t \<and> set t = {t}"
    proof
      assume t: "terminal t"
      show "ide t \<and> set t = {t}"
      proof
        show "ide t" using t terminal_char1 by auto
        show "set t = {t}"
        proof -
          have "\<exists>!x. x \<in> hom unity t" using t terminal_def terminal_unity by force
          moreover have "t \<in> img ` hom unity t" using t stable_img set_def by simp
          ultimately show ?thesis using set_def by auto
        qed
      qed
      next
      assume "ide t \<and> set t = {t}"
      thus "terminal t" using terminal_char1 by force
    qed

  end

  text\<open>
    At last, we define the \<open>set_category\<close> locale by existentially quantifying
    out the choice of a particular @{term img} map.  We need to know that such a map
    exists, but it does not matter which one we choose.
\<close>

  locale set_category = category S
  for S :: "'s comp"      (infixr "\<cdot>" 55) +
  assumes ex_img: "\<exists>img. set_category_given_img S img"
  begin

    notation in_hom ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
  
    definition some_img
    where "some_img = (SOME img. set_category_given_img S img)"
   
  end
  
  sublocale set_category \<subseteq> set_category_given_img S some_img
  proof -
    have "\<exists>img. set_category_given_img S img" using ex_img by auto
    thus "set_category_given_img S some_img" 
      using someI_ex [of "\<lambda>img. set_category_given_img S img"] some_img_def
      by metis
  qed

  context set_category
  begin

    text\<open>
      The arbitrary choice of @{term img} induces a system of inclusions,
      which are arrows corresponding to inclusions of subsets.
\<close>

    definition incl :: "'s \<Rightarrow> bool"
    where "incl f = (arr f \<and> set (dom f) \<subseteq> set (cod f) \<and>
                     f = mkArr (set (dom f)) (set (cod f)) (\<lambda>x. x))"

    lemma Fun_incl:
    assumes "incl f"
    shows "Fun f = (\<lambda>x \<in> set (dom f). x)"
      using assms incl_def by (metis Fun_mkArr)

    lemma ex_incl_iff_subset:
    assumes "ide a" and "ide b"
    shows "(\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> incl f) \<longleftrightarrow> set a \<subseteq> set b"
    proof
      show "\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> incl f \<Longrightarrow> set a \<subseteq> set b"
        using incl_def by auto
      show "set a \<subseteq> set b \<Longrightarrow> \<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> incl f"
      proof
        assume 1: "set a \<subseteq> set b"
        show "\<guillemotleft>mkArr (set a) (set b) (\<lambda>x. x) : a \<rightarrow> b\<guillemotright> \<and> incl (mkArr (set a) (set b) (\<lambda>x. x))"
        proof
          show "\<guillemotleft>mkArr (set a) (set b) (\<lambda>x. x) : a \<rightarrow> b\<guillemotright>"
          proof -
            have "(\<lambda>x. x) \<in> set a \<rightarrow> set b" using 1 by auto
            thus ?thesis
              using assms mkArr_in_hom set_subset_Univ in_homI by auto
          qed
          thus "incl (mkArr (set a) (set b) (\<lambda>x. x))"
            using 1 incl_def by force
        qed
      qed
    qed

  end

  section "Categoricity"

  text\<open>
    In this section we show that the \<open>set_category\<close> locale completely characterizes
    the structure of its interpretations as categories, in the sense that for any two
    interpretations @{term S} and @{term S'}, a bijection between the universe of @{term S}
    and the universe of @{term S'} extends to an isomorphism of @{term S} and @{term S'}.
\<close>
  
  locale two_set_categories_bij_betw_Univ =
    S: set_category S +
    S': set_category S'
  for S :: "'s comp"      (infixr "\<cdot>" 55)
  and S' :: "'t comp"     (infixr "\<cdot>\<acute>" 55)
  and \<phi> :: "'s \<Rightarrow> 't" +
  assumes bij_\<phi>: "bij_betw \<phi> S.Univ S'.Univ"
  begin

    notation S.in_hom     ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    notation S'.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>' _\<guillemotright>")

    abbreviation \<psi>
    where "\<psi> \<equiv> inv_into S.Univ \<phi>"

    lemma \<psi>_\<phi>:
    assumes "t \<in> S.Univ"
    shows "\<psi> (\<phi> t) = t"
      using assms bij_\<phi> bij_betw_inv_into_left by metis

    lemma \<phi>_\<psi>:
    assumes "t' \<in> S'.Univ"
    shows "\<phi> (\<psi> t') = t'"
      using assms bij_\<phi> bij_betw_inv_into_right by metis
    
    lemma \<psi>_img_\<phi>_img:
    assumes "A \<subseteq> S.Univ"
    shows "\<psi> ` \<phi> ` A = A"
      using assms bij_\<phi> by (simp add: bij_betw_def)
      
    lemma \<phi>_img_\<psi>_img:
    assumes "A' \<subseteq> S'.Univ"
    shows "\<phi> ` \<psi> ` A' = A'"
      using assms bij_\<phi> by (simp add: bij_betw_def image_inv_into_cancel)
  
    text\<open>
      The object map @{term \<Phi>o} of a functor from @{term[source=true] S}
      to @{term[source=true] S'}.
\<close>

    definition \<Phi>o
    where "\<Phi>o = (\<lambda>a \<in> Collect S.ide. S'.mkIde (\<phi> ` S.set a))"

    lemma set_\<Phi>o:
    assumes "S.ide a"
    shows "S'.set (\<Phi>o a) = \<phi> ` S.set a"
    proof -
      from assms have "S.set a \<subseteq> S.Univ" by simp
      then show ?thesis
      using S'.set_mkIde \<Phi>o_def assms bij_\<phi> bij_betw_def image_mono mem_Collect_eq restrict_def
      by (metis (no_types, lifting))
    qed

    lemma \<Phi>o_preserves_ide:
    assumes "S.ide a"
    shows "S'.ide (\<Phi>o a)"
      using assms S'.ide_mkIde S.set_subset_Univ bij_\<phi> bij_betw_def image_mono restrict_apply'
      unfolding \<Phi>o_def
      by (metis (mono_tags, lifting) mem_Collect_eq)
      
    text\<open>
      The map @{term \<Phi>a} assigns to each arrow @{term f} of @{term[source=true] S} the function on
      the universe of @{term[source=true] S'} that is the same as the function induced by @{term f}
      on the universe of @{term[source=true] S}, up to the bijection @{term \<phi>} between the two
      universes.
\<close>

    definition \<Phi>a
    where "\<Phi>a = (\<lambda>f. \<lambda>x' \<in> \<phi> ` S.set (S.dom f). \<phi> (S.Fun f (\<psi> x')))"
    
    lemma \<Phi>a_mapsto:
    assumes "S.arr f"
    shows "\<Phi>a f \<in> S'.set (\<Phi>o (S.dom f)) \<rightarrow> S'.set (\<Phi>o (S.cod f))"
    proof -
      have "\<Phi>a f \<in> \<phi> ` S.set (S.dom f) \<rightarrow> \<phi> ` S.set (S.cod f)"
      proof
        fix x
        assume x: "x \<in> \<phi> ` S.set (S.dom f)"
        have "\<psi> x \<in> S.set (S.dom f)"
          using assms x \<psi>_img_\<phi>_img [of "S.set (S.dom f)"] S.set_subset_Univ by auto
        hence "S.Fun f (\<psi> x) \<in> S.set (S.cod f)" using assms S.Fun_mapsto by auto
        hence "\<phi> (S.Fun f (\<psi> x)) \<in> \<phi> ` S.set (S.cod f)" by simp
        thus "\<Phi>a f x \<in> \<phi> ` S.set (S.cod f)" using x \<Phi>a_def by auto
      qed
      thus ?thesis using assms set_\<Phi>o \<Phi>o_preserves_ide by auto
    qed
    
    text\<open>
      The map @{term \<Phi>a} takes composition of arrows to extensional
      composition of functions.
\<close>

    lemma \<Phi>a_comp:
    assumes gf: "S.seq g f"
    shows "\<Phi>a (g \<cdot> f) = restrict (\<Phi>a g o \<Phi>a f) (S'.set (\<Phi>o (S.dom f)))"
    proof -
      have "\<Phi>a (g \<cdot> f) = (\<lambda>x' \<in> \<phi> ` S.set (S.dom f). \<phi> (S.Fun (S g f) (\<psi> x')))"
        using gf \<Phi>a_def by auto
      also have "... = (\<lambda>x' \<in> \<phi> ` S.set (S.dom f).
                           \<phi> (restrict (S.Fun g o S.Fun f) (S.set (S.dom f)) (\<psi> x')))"
        using gf set_\<Phi>o S.Fun_comp by simp
      also have "... = restrict (\<Phi>a g o \<Phi>a f) (S'.set (\<Phi>o (S.dom f)))"
      proof -
        have "\<And>x'. x' \<in> \<phi> ` S.set (S.dom f)
                 \<Longrightarrow> \<phi> (restrict (S.Fun g o S.Fun f) (S.set (S.dom f)) (\<psi> x')) = \<Phi>a g (\<Phi>a f x')"
        proof -
          fix x'
          assume X': "x' \<in> \<phi> ` S.set (S.dom f)"
          hence 1: "\<psi> x' \<in> S.set (S.dom f)"
            using gf \<psi>_img_\<phi>_img [of "S.set (S.dom f)"] S.set_subset_Univ S.ide_dom by blast
          hence "\<phi> (restrict (S.Fun g o S.Fun f) (S.set (S.dom f)) (\<psi> x'))
                   = \<phi> (S.Fun g (S.Fun f (\<psi> x')))"
            using restrict_apply by auto
          also have "... = \<phi> (S.Fun g (\<psi> (\<phi> (S.Fun f (\<psi> x')))))"
          proof -
            have "S.Fun f (\<psi> x') \<in> S.set (S.cod f)"
              using gf 1 S.Fun_mapsto by fast
            hence "\<psi> (\<phi> (S.Fun f (\<psi> x'))) = S.Fun f (\<psi> x')"
              using assms bij_\<phi> S.set_subset_Univ bij_betw_def inv_into_f_f subsetCE S.ide_cod
              by (metis S.seqE)
            thus ?thesis by auto
          qed
          also have "... = \<Phi>a g (\<Phi>a f x')"
          proof -
            have "\<Phi>a f x' \<in> \<phi> ` S.set (S.cod f)"
              using gf S.ide_dom S.ide_cod X' \<Phi>a_mapsto [of f] set_\<Phi>o [of "S.dom f"]
                    set_\<Phi>o [of "S.cod f"]
              by blast
            thus ?thesis using gf X' \<Phi>a_def by auto
          qed
          finally show "\<phi> (restrict (S.Fun g o S.Fun f) (S.set (S.dom f)) (\<psi> x')) =
                        \<Phi>a g (\<Phi>a f x')"
            by auto
        qed
        thus ?thesis using assms set_\<Phi>o by fastforce
      qed
      finally show ?thesis by auto
    qed
    
    text\<open>
      Finally, we use @{term \<Phi>o} and @{term \<Phi>a} to define a functor @{term \<Phi>}.
\<close>

    definition \<Phi>
    where "\<Phi> f = (if S.arr f then
                     S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod f))) (\<Phi>a f)
                   else S'.null)"
    
    lemma \<Phi>_in_hom:
    assumes "S.arr f"
    shows "\<Phi> f \<in> S'.hom (\<Phi>o (S.dom f)) (\<Phi>o (S.cod f))"
    proof -
      have "\<guillemotleft>\<Phi> f : S'.dom (\<Phi> f) \<rightarrow>' S'.cod (\<Phi> f)\<guillemotright>"
        using assms \<Phi>_def \<Phi>a_mapsto \<Phi>o_preserves_ide
        by (intro S'.in_homI, auto)
      thus ?thesis
        using assms \<Phi>_def \<Phi>a_mapsto \<Phi>o_preserves_ide by auto
    qed

    lemma \<Phi>_ide [simp]:
    assumes "S.ide a"
    shows "\<Phi> a = \<Phi>o a"
    proof -
      have "\<Phi> a = S'.mkArr (S'.set (\<Phi>o a)) (S'.set (\<Phi>o a)) (\<lambda>x'. x')"
      proof -
        have "\<guillemotleft>\<Phi> a : \<Phi>o a \<rightarrow>' \<Phi>o a\<guillemotright>"
          using assms \<Phi>_in_hom S.ide_in_hom by fastforce
        moreover have "\<Phi>a a = restrict (\<lambda>x'. x') (S'.set (\<Phi>o a))"
        proof -
          have "\<Phi>a a = (\<lambda>x' \<in> \<phi> ` S.set a. \<phi> (S.Fun a (\<psi> x')))"
            using assms \<Phi>a_def restrict_apply by auto
          also have "... = (\<lambda>x' \<in> S'.set (\<Phi>o a). \<phi> (\<psi> x'))"
          proof -
            have "S.Fun a = (\<lambda>x \<in> S.set a. x)" using assms S.Fun_ide by simp
            moreover have "\<And>x'. x' \<in> \<phi> ` S.set a \<Longrightarrow> \<psi> x' \<in> S.set a"
              using assms bij_\<phi> S.set_subset_Univ image_iff by (metis \<psi>_img_\<phi>_img)
            ultimately show ?thesis
              using assms set_\<Phi>o by auto
          qed
          also have "... = restrict (\<lambda>x'. x') (S'.set (\<Phi>o a))"
            using assms S'.set_subset_Univ \<Phi>o_preserves_ide \<phi>_\<psi>
            by (meson restr_eqI subsetCE)
          ultimately show ?thesis by auto
        qed
        ultimately show ?thesis
          using assms \<Phi>_def \<Phi>o_preserves_ide S'.mkArr_restrict_eq'
          by (metis S'.arrI S.ide_char)
      qed
      thus ?thesis
        using assms S'.mkIde_as_mkArr \<Phi>o_preserves_ide \<Phi>_in_hom by simp
    qed
    
    lemma set_dom_\<Phi>:
    assumes "S.arr f"
    shows "S'.set (S'.dom (\<Phi> f)) = \<phi> ` (S.set (S.dom f))"
      using assms S.ide_dom \<Phi>_in_hom \<Phi>_ide set_\<Phi>o by fastforce
    
    lemma \<Phi>_comp:
    assumes "S.seq g f"
    shows "\<Phi> (g \<cdot> f) = \<Phi> g \<cdot>\<acute> \<Phi> f"
    proof -
      have "\<Phi> (g \<cdot> f) = S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod g))) (\<Phi>a (S g f))"
        using \<Phi>_def assms by auto
      also have "... = S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod g)))
                                (restrict (\<Phi>a g o \<Phi>a f) (S'.set (\<Phi>o (S.dom f))))"
        using assms \<Phi>a_comp set_\<Phi>o by force
      also have "... = S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod g))) (\<Phi>a g o \<Phi>a f)"
      proof -
        have "S'.arr (S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod g))) (\<Phi>a g o \<Phi>a f))"
          using assms \<Phi>a_mapsto [of f] \<Phi>a_mapsto [of g] \<Phi>o_preserves_ide S'.arr_mkArr
          by (elim S.seqE, auto)
        thus ?thesis
          using assms S'.mkArr_restrict_eq by auto
      qed
      also have "... = S' (S'.mkArr (S'.set (\<Phi>o (S.dom g))) (S'.set (\<Phi>o (S.cod g))) (\<Phi>a g))
                          (S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod f))) (\<Phi>a f))"
      proof -
        have "S'.arr (S'.mkArr (S'.set (\<Phi>o (S.dom f))) (S'.set (\<Phi>o (S.cod f))) (\<Phi>a f))"
          using assms \<Phi>a_mapsto set_\<Phi>o S.ide_dom S.ide_cod \<Phi>o_preserves_ide
                S'.arr_mkArr S'.set_subset_Univ S.seqE
          by metis
        moreover have "S'.arr (S'.mkArr (S'.set (\<Phi>o (S.dom g))) (S'.set (\<Phi>o (S.cod g)))
                              (\<Phi>a g))"
          using assms \<Phi>a_mapsto set_\<Phi>o S.ide_dom S.ide_cod \<Phi>o_preserves_ide S'.arr_mkArr
                S'.set_subset_Univ S.seqE
          by metis
        ultimately show ?thesis using assms S'.comp_mkArr by force
      qed
      also have "... = \<Phi> g \<cdot>\<acute> \<Phi> f" using assms \<Phi>_def by force
      finally show ?thesis by fast
    qed
      
    interpretation \<Phi>: "functor" S S' \<Phi>
      apply unfold_locales
      using \<Phi>_def
          apply simp
      using \<Phi>_in_hom \<Phi>_comp
      by auto

    lemma \<Phi>_is_functor:
    shows "functor S S' \<Phi>" ..
      
    lemma Fun_\<Phi>:
    assumes "S.arr f" and "x \<in> S.set (S.dom f)"
    shows "S'.Fun (\<Phi> f) (\<phi> x) = \<Phi>a f (\<phi> x)"
      using assms \<Phi>_def \<Phi>.preserves_arr set_\<Phi>o by auto
      
    lemma \<Phi>_acts_elementwise:
    assumes "S.ide a"
    shows "S'.set (\<Phi> a) = \<Phi> ` S.set a"
    proof
      have 0: "S'.set (\<Phi> a) = \<phi> ` S.set a"
        using assms \<Phi>_ide set_\<Phi>o by simp
      have 1: "\<And>x. x \<in> S.set a \<Longrightarrow> \<Phi> x = \<phi> x"
      proof -
        fix x
        assume x: "x \<in> S.set a"
        have 1: "S.terminal x" using assms x S.set_subset_Univ by blast
        hence 2: "S'.terminal (\<phi> x)"
          by (metis CollectD CollectI bij_\<phi> bij_betw_def image_iff)
        have "\<Phi> x = \<Phi>o x"
          using assms x 1 \<Phi>_ide S.terminal_def by auto
        also have "... = \<phi> x"
        proof -
          have "\<Phi>o x = S'.mkIde (\<phi> ` S.set x)"
            using assms 1 x \<Phi>o_def S.terminal_def by auto
          moreover have "S'.mkIde (\<phi> ` S.set x) = \<phi> x"
            using assms x 1 2 S.terminal_char2 S'.terminal_char2 S'.mkIde_set bij_\<phi>
            by (metis image_empty image_insert)
          ultimately show ?thesis by auto
        qed
        finally show "\<Phi> x = \<phi> x" by auto
      qed
      show "S'.set (\<Phi> a) \<subseteq> \<Phi> ` S.set a" using 0 1 by force
      show "\<Phi> ` S.set a \<subseteq> S'.set (\<Phi> a)" using 0 1 by force
    qed

    lemma \<Phi>_preserves_incl:
    assumes "S.incl m"
    shows "S'.incl (\<Phi> m)"
    proof -
      have 1: "S.arr m \<and> S.set (S.dom m) \<subseteq> S.set (S.cod m) \<and>
               m = S.mkArr (S.set (S.dom m)) (S.set (S.cod m)) (\<lambda>x. x)"
        using assms S.incl_def by blast
      have "S'.arr (\<Phi> m)" using 1 by auto
      moreover have 2: "S'.set (S'.dom (\<Phi> m)) \<subseteq> S'.set (S'.cod (\<Phi> m))"
        using 1 \<Phi>.preserves_dom \<Phi>.preserves_cod \<Phi>_acts_elementwise
        by (metis (full_types) S.ide_cod S.ide_dom image_mono)
      moreover have "\<Phi> m =
                     S'.mkArr (S'.set (S'.dom (\<Phi> m))) (S'.set (S'.cod (\<Phi> m))) (\<lambda>x'. x')"
      proof -
        have "\<Phi> m = S'.mkArr (S'.set (\<Phi>o (S.dom m))) (S'.set (\<Phi>o (S.cod m))) (\<Phi>a m)"
          using 1 \<Phi>_def by simp
        also have "... = S'.mkArr (S'.set (S'.dom (\<Phi> m))) (S'.set (S'.cod (\<Phi> m))) (\<Phi>a m)"
          using 1 \<Phi>_ide by auto
        finally have 3: "\<Phi> m =
                         S'.mkArr (S'.set (S'.dom (\<Phi> m))) (S'.set (S'.cod (\<Phi> m))) (\<Phi>a m)"
          by auto
        also have "... = S'.mkArr (S'.set (S'.dom (\<Phi> m))) (S'.set (S'.cod (\<Phi> m))) (\<lambda>x'. x')"
        proof -
          have 4: "S.Fun m = restrict (\<lambda>x. x) (S.set (S.dom m))"
            using assms S.incl_def by (metis (full_types) S.Fun_mkArr)
          hence "\<Phi>a m = restrict (\<lambda>x'. x') (\<phi> ` (S.set (S.dom m)))"
          proof -
            have 5: "\<And>x'. x' \<in> \<phi> ` S.set (S.dom m) \<Longrightarrow> \<phi> (\<psi> x') = x'"
              using 1 bij_\<phi> bij_betw_def S'.set_subset_Univ S.ide_dom \<Phi>o_preserves_ide
                    f_inv_into_f set_\<Phi>o
              by (metis subsetCE)
            have "\<Phi>a m = restrict (\<lambda>x'. \<phi> (S.Fun m (\<psi> x'))) (\<phi> ` S.set (S.dom m))"
              using \<Phi>a_def by simp
            also have "... = restrict (\<lambda>x'. x') (\<phi> ` S.set (S.dom m))"
            proof -
              have "\<And>x. x \<in> \<phi> ` (S.set (S.dom m)) \<Longrightarrow> \<phi> (S.Fun m (\<psi> x)) = x"
              proof -
                fix x
                assume x: "x \<in> \<phi> ` (S.set (S.dom m))"
                hence "\<psi> x \<in> S.set (S.dom m)"
                  using 1 S.ide_dom S.set_subset_Univ \<psi>_img_\<phi>_img image_eqI by metis
                thus "\<phi> (S.Fun m (\<psi> x)) = x" using 1 4 5 x by simp
              qed
              thus ?thesis by auto
            qed
            finally show ?thesis by auto
          qed
          hence "\<Phi>a m = restrict (\<lambda>x'. x') (S'.set (S'.dom (\<Phi> m)))"
            using 1 set_dom_\<Phi> by auto
          thus ?thesis
            using 2 3 \<open>S'.arr (\<Phi> m)\<close> S'.mkArr_restrict_eq S'.ide_cod S'.ide_dom S'.incl_def
            by (metis S'.arr_mkArr image_restrict_eq image_subset_iff_funcset)
        qed
        finally show ?thesis by auto
      qed
      ultimately show ?thesis using S'.incl_def by blast
    qed

    text\<open>
      Interchange the role of @{term \<phi>} and @{term \<psi>} to obtain a functor \<open>\<Psi>\<close>
      from @{term[source=true] S'} to @{term[source=true] S}.
\<close>

    interpretation INV: two_set_categories_bij_betw_Univ S' S \<psi>
      apply unfold_locales by (simp add: bij_\<phi> bij_betw_inv_into)

    abbreviation \<Psi>o
    where "\<Psi>o \<equiv> INV.\<Phi>o"

    abbreviation \<Psi>a
    where "\<Psi>a \<equiv> INV.\<Phi>a"

    abbreviation \<Psi>
    where "\<Psi> \<equiv> INV.\<Phi>"

    interpretation \<Psi>: "functor" S' S \<Psi>
      using INV.\<Phi>_is_functor by auto

    text\<open>
      The functors @{term \<Phi>} and @{term \<Psi>} are inverses.
\<close>

    lemma Fun_\<Psi>:
    assumes "S'.arr f'" and "x' \<in> S'.set (S'.dom f')"
    shows "S.Fun (\<Psi> f') (\<psi> x') = \<Psi>a f' (\<psi> x')"
      using assms INV.Fun_\<Phi> by blast
          
    lemma \<Psi>o_\<Phi>o:
    assumes "S.ide a"
    shows "\<Psi>o (\<Phi>o a) = a"
      using assms \<Phi>o_def INV.\<Phi>o_def \<psi>_img_\<phi>_img \<Phi>o_preserves_ide set_\<Phi>o by force
     
    lemma \<Phi>\<Psi>:
    assumes "S.arr f"
    shows "\<Psi> (\<Phi> f) = f"
    proof (intro S.arr_eqI)
      show par: "S.par (\<Psi> (\<Phi> f)) f"
        using assms \<Phi>o_preserves_ide \<Psi>o_\<Phi>o by auto
      show "S.Fun (\<Psi> (\<Phi> f)) = S.Fun f"
      proof -
        have "S.arr (\<Psi> (\<Phi> f))" using assms by auto
        moreover have "\<Psi> (\<Phi> f) = S.mkArr (S.set (S.dom f)) (S.set (S.cod f)) (\<Psi>a (\<Phi> f))"
          using assms INV.\<Phi>_def \<Phi>_in_hom \<Psi>o_\<Phi>o by auto
        moreover have "\<Psi>a (\<Phi> f) = (\<lambda>x \<in> S.set (S.dom f). \<psi> (S'.Fun (\<Phi> f) (\<phi> x)))"
        proof -
          have "\<Psi>a (\<Phi> f) = (\<lambda>x \<in> \<psi> ` S'.set (S'.dom (\<Phi> f)). \<psi> (S'.Fun (\<Phi> f) (\<phi> x)))"
          proof -
            have "\<And>x. x \<in> \<psi> ` S'.set (S'.dom (\<Phi> f)) \<Longrightarrow> INV.\<psi> x = \<phi> x"
              using assms S.ide_dom S.set_subset_Univ \<Psi>.preserves_reflects_arr par bij_\<phi>
                    inv_into_inv_into_eq subsetCE INV.set_dom_\<Phi>
              by metis
            thus ?thesis
              using INV.\<Phi>a_def by auto
          qed
          moreover have "\<psi> ` S'.set (S'.dom (\<Phi> f)) = S.set (S.dom f)"
            using assms by (metis par \<Psi>.preserves_reflects_arr INV.set_dom_\<Phi>)
          ultimately show ?thesis by auto
        qed
        ultimately have 1: "S.Fun (\<Psi> (\<Phi> f)) = (\<lambda>x \<in> S.set (S.dom f). \<psi> (S'.Fun (\<Phi> f) (\<phi> x)))"
          using S'.Fun_mkArr by simp
        show ?thesis
        proof
          fix x
          have "x \<notin> S.set (S.dom f) \<Longrightarrow> S.Fun (\<Psi> (\<Phi> f)) x = S.Fun f x"
            using 1 assms extensional_def S.Fun_mapsto S.Fun_def by auto
          moreover have "x \<in> S.set (S.dom f) \<Longrightarrow> S.Fun (\<Psi> (\<Phi> f)) x = S.Fun f x"
          proof -
            assume x: "x \<in> S.set (S.dom f)"
            have "S.Fun (\<Psi> (\<Phi> f)) x = \<psi> (\<phi> (S.Fun f (\<psi> (\<phi> x))))"
              using assms x 1 Fun_\<Phi> bij_\<phi> \<Phi>a_def by auto
            also have "... = S.Fun f x"
            proof -
              have 2: "\<And>x. x \<in> S.Univ \<Longrightarrow> \<psi> (\<phi> x) = x"
                using bij_\<phi> bij_betw_inv_into_left by fast
              have "S.Fun f (\<psi> (\<phi> x)) = S.Fun f x"
                using assms x 2
                by (metis S.ide_dom S.set_subset_Univ subsetCE)
              moreover have "S.Fun f x \<in> S.Univ"
                using x assms S.Fun_mapsto S.set_subset_Univ S.ide_cod by blast
              ultimately show ?thesis using 2 by auto
            qed
            finally show ?thesis by auto
          qed
          ultimately show "S.Fun (\<Psi> (\<Phi> f)) x = S.Fun f x" by auto
        qed
      qed
    qed

    lemma \<Phi>o_\<Psi>o:
    assumes "S'.ide a'"
    shows "\<Phi>o (\<Psi>o a') = a'"
      using assms \<Phi>o_def INV.\<Phi>o_def \<phi>_img_\<psi>_img INV.\<Phi>o_preserves_ide \<psi>_\<phi> INV.set_\<Phi>o
      by force

    lemma \<Psi>\<Phi>:
    assumes "S'.arr f'"
    shows "\<Phi> (\<Psi> f') = f'"
    proof (intro S'.arr_eqI)
      show par: "S'.par (\<Phi> (\<Psi> f')) f'"
        using assms \<Phi>.preserves_ide \<Psi>.preserves_ide \<Phi>_ide INV.\<Phi>_ide \<Phi>o_\<Psi>o by auto
      show "S'.Fun (\<Phi> (\<Psi> f')) = S'.Fun f'"
      proof -
        have "S'.arr (\<Phi> (\<Psi> f'))" using assms by blast
        moreover have "\<Phi> (\<Psi> f') =
                       S'.mkArr (S'.set (S'.dom f')) (S'.set (S'.cod f')) (\<Phi>a (\<Psi> f'))"
          using assms \<Phi>_def INV.\<Phi>_in_hom \<Phi>o_\<Psi>o by simp
        moreover have "\<Phi>a (\<Psi> f') = (\<lambda>x' \<in> S'.set (S'.dom f'). \<phi> (S.Fun (\<Psi> f') (\<psi> x')))"
          unfolding \<Phi>a_def
          using assms par \<Psi>.preserves_arr set_dom_\<Phi> by metis
        ultimately have 1: "S'.Fun (\<Phi> (\<Psi> f')) =
                            (\<lambda>x' \<in> S'.set (S'.dom f'). \<phi> (S.Fun (\<Psi> f') (\<psi> x')))"
          using S'.Fun_mkArr by simp
        show ?thesis
        proof
          fix x'
          have "x' \<notin> S'.set (S'.dom f') \<Longrightarrow> S'.Fun (\<Phi> (\<Psi> f')) x' = S'.Fun f' x'"
            using 1 assms S'.Fun_mapsto extensional_def by (simp add: S'.Fun_def)
          moreover have "x' \<in> S'.set (S'.dom f') \<Longrightarrow> S'.Fun (\<Phi> (\<Psi> f')) x' = S'.Fun f' x'"
          proof -
            assume x': "x' \<in> S'.set (S'.dom f')"
            have "S'.Fun (\<Phi> (\<Psi> f')) x' = \<phi> (S.Fun (\<Psi> f') (\<psi> x'))"
              using x' 1 by auto
            also have "... = \<phi> (\<Psi>a f' (\<psi> x'))"
              using Fun_\<Psi> x' assms S'.set_subset_Univ bij_\<phi> by metis
            also have "... = \<phi> (\<psi> (S'.Fun f' (\<phi> (\<psi> x'))))"
            proof -
              have "\<phi> (\<Psi>a f' (\<psi> x')) = \<phi> (\<psi> (S'.Fun f' x'))"
              proof -
                have "x' \<in> S'.Univ"
                  by (meson S'.ide_dom S'.set_subset_Univ assms subsetCE x')
                thus ?thesis
                  by (simp add: INV.\<Phi>a_def INV.\<psi>_\<phi> x')
              qed
              also have "... = \<phi> (\<psi> (S'.Fun f' (\<phi> (\<psi> x'))))"
                using assms x' \<phi>_\<psi> S'.set_subset_Univ S'.ide_dom by (metis subsetCE)
              finally show ?thesis by auto
            qed
            also have "... = S'.Fun f' x'"
            proof -
              have 2: "\<And>x'. x' \<in> S'.Univ \<Longrightarrow> \<phi> (\<psi> x') = x'"
                using bij_\<phi> bij_betw_inv_into_right by fast
              have "S'.Fun f' (\<phi> (\<psi> x')) = S'.Fun f' x'"
                using assms x' 2 S'.set_subset_Univ S'.ide_dom by (metis subsetCE)
              moreover have "S'.Fun f' x' \<in> S'.Univ"
                using x' assms S'.Fun_mapsto S'.set_subset_Univ S'.ide_cod by blast
              ultimately show ?thesis using 2 by auto
            qed
            finally show ?thesis by auto
          qed
          ultimately show "S'.Fun (\<Phi> (\<Psi> f')) x' = S'.Fun f' x'" by auto
        qed
      qed
    qed
          
    lemma inverse_functors_\<Phi>_\<Psi>:
    shows "inverse_functors S S' \<Phi> \<Psi>"
    proof -
      interpret \<Phi>\<Psi>: composite_functor S S' S \<Phi> \<Psi> ..
      have inv: "\<Psi> o \<Phi> = S.map"
        using \<Phi>\<Psi> S.map_def \<Phi>\<Psi>.is_extensional by auto
    
      interpret \<Psi>\<Phi>: composite_functor S' S S' \<Psi> \<Phi> ..
      have inv': "\<Phi> o \<Psi> = S'.map"
        using \<Psi>\<Phi> S'.map_def \<Psi>\<Phi>.is_extensional by auto
    
      show ?thesis
        using inv inv' by (unfold_locales, auto)
    qed
      
    lemma are_isomorphic:
    shows "\<exists>\<Phi>. invertible_functor S S' \<Phi> \<and> (\<forall>m. S.incl m \<longrightarrow> S'.incl (\<Phi> m))"
    proof -
      interpret inverse_functors S S' \<Phi> \<Psi>
        using inverse_functors_\<Phi>_\<Psi> by auto
      have 1: "inverse_functors S S' \<Phi> \<Psi>" ..
      interpret invertible_functor S S' \<Phi>
        apply unfold_locales using 1 by auto
      have "invertible_functor S S' \<Phi>" ..
      thus ?thesis using \<Phi>_preserves_incl by auto
    qed
    
  end
  
  (*
   * The main result: set_category is categorical, in the following (logical) sense:
   * If S and S' are two "set categories", and if the sets of terminal objects of S and S'
   * are in bijective correspondence, then S and S' are isomorphic as categories,
   * via a functor that preserves inclusion maps, hence the inclusion relation between sets.
   *)
  theorem set_category_is_categorical:
  assumes "set_category S" and "set_category S'"
  and "bij_betw \<phi> (set_category_data.Univ S) (set_category_data.Univ S')"
  shows "\<exists>\<Phi>. invertible_functor S S' \<Phi> \<and>
             (\<forall>m. set_category.incl S m \<longrightarrow> set_category.incl S' (\<Phi> m))"
  proof -
    interpret S: set_category S using assms(1) by auto
    interpret S': set_category S' using assms(2) by auto
    interpret two_set_categories_bij_betw_Univ S S' \<phi>
      apply (unfold_locales) using assms(3) by auto
    show ?thesis using are_isomorphic by auto
  qed
  
  section "Further Properties of Set Categories"

  text\<open>
    In this section we further develop the consequences of the \<open>set_category\<close>
    axioms, and establish characterizations of a number of standard category-theoretic
    notions for a \<open>set_category\<close>.
\<close>

  context set_category
  begin
  
    abbreviation Dom
    where "Dom f \<equiv> set (dom f)"
    
    abbreviation Cod
    where "Cod f \<equiv> set (cod f)"

    subsection "Initial Object"

    text\<open>
      The object corresponding to the empty set is an initial object.
\<close>

    definition empty
    where "empty = mkIde {}"

    lemma initial_empty:
    shows "initial empty"
    proof
      show 0: "ide empty" using empty_def by auto
      show "\<And>b. ide b \<Longrightarrow> \<exists>!f. \<guillemotleft>f : empty \<rightarrow> b\<guillemotright>"
      proof -
        fix b
        assume b: "ide b"
        show "\<exists>!f. \<guillemotleft>f : empty \<rightarrow> b\<guillemotright>"
        proof
          show 1: "\<guillemotleft>mkArr {} (set b) (\<lambda>x. x) : empty \<rightarrow> b\<guillemotright>"
            using b empty_def mkArr_in_hom mkIde_set set_subset_Univ
            by (metis 0 Pi_empty UNIV_I arr_mkIde)
          show "\<And>f. \<guillemotleft>f : empty \<rightarrow> b\<guillemotright> \<Longrightarrow> f = mkArr {} (set b) (\<lambda>x. x)"
          proof -
            fix f
            assume f: "\<guillemotleft>f : empty \<rightarrow> b\<guillemotright>"
            show "f = mkArr {} (set b) (\<lambda>x. x)"
            proof (intro arr_eqI)
              show 1: "par f (mkArr {} (set b) (\<lambda>x. x))"
                using 1 f by force
              show "Fun f = Fun (mkArr {} (set b) (\<lambda>x. x))"
                using empty_def 1 f Fun_mapsto by fastforce
            qed
          qed
        qed
      qed
    qed

    subsection "Identity Arrows"
    
    text\<open>
      Identity arrows correspond to restrictions of the identity function.
\<close>

    lemma ide_char:
    assumes "arr f"
    shows "ide f \<longleftrightarrow> Dom f = Cod f \<and> Fun f = (\<lambda>x \<in> Dom f. x)"
      using assms mkIde_as_mkArr mkArr_Fun Fun_ide in_homE ide_cod mkArr_Fun mkIde_set
      by (metis ide_char)

    lemma ideI:
    assumes "arr f" and "Dom f = Cod f" and "\<And>x. x \<in> Dom f \<Longrightarrow> Fun f x = x"
    shows "ide f"
    proof -
      have "Fun f = (\<lambda>x \<in> Dom f. x)"
        using assms Fun_def by auto
      thus ?thesis using assms ide_char by blast
    qed

    subsection "Inclusions"
    
    lemma ide_implies_incl:
    assumes "ide a"
    shows "incl a"
    proof -
      have "arr a \<and> Dom a \<subseteq> Cod a" using assms by auto
      moreover have "a = mkArr (Dom a) (Cod a) (\<lambda>x. x)"
        using assms by simp
      ultimately show ?thesis using incl_def by simp
    qed
    
    definition incl_in :: "'s \<Rightarrow> 's \<Rightarrow> bool"
    where "incl_in a b = (ide a \<and> ide b \<and> set a \<subseteq> set b)"
    
    abbreviation incl_of
    where "incl_of a b \<equiv> mkArr (set a) (set b) (\<lambda>x. x)"

    lemma elem_set_implies_set_eq_singleton:
    assumes "a \<in> set b"
    shows "set a = {a}"
    proof -
      have "ide b" using assms set_def by auto
      thus ?thesis using assms set_subset_Univ terminal_char2
        by (metis mem_Collect_eq subsetCE)
    qed

    lemma elem_set_implies_incl_in:
    assumes "a \<in> set b"
    shows "incl_in a b"
    proof -
      have b: "ide b" using assms set_def by auto
      hence "set b \<subseteq> Univ" by simp
      hence "a \<in> Univ \<and> set a \<subseteq> set b"
        using assms elem_set_implies_set_eq_singleton by auto
      hence "ide a \<and> set a \<subseteq> set b"
        using b terminal_char1 by simp
      thus ?thesis using b incl_in_def by simp
    qed
    
    lemma incl_incl_of [simp]:
    assumes "incl_in a b"
    shows "incl (incl_of a b)"
    and "\<guillemotleft>incl_of a b : a \<rightarrow> b\<guillemotright>"
    proof -
      show "\<guillemotleft>incl_of a b : a \<rightarrow> b\<guillemotright>"
        using assms incl_in_def mkArr_in_hom
        by (metis image_ident image_subset_iff_funcset mkIde_set set_subset_Univ)
      thus "incl (incl_of a b)"
        using assms incl_def incl_in_def by fastforce
    qed
    
    text\<open>
      There is at most one inclusion between any pair of objects.
\<close>

    lemma incls_coherent:
    assumes "par f f'" and "incl f" and "incl f'"
    shows "f = f'"
      using assms incl_def fun_complete by auto

    text\<open>
      The set of inclusions is closed under composition.
\<close>

    lemma incl_comp [simp]:
    assumes "incl f" and "incl g" and "cod f = dom g"
    shows "incl (g \<cdot> f)"
    proof -
      have 1: "seq g f" using assms incl_def by auto
      moreover have "Dom (g \<cdot> f) \<subseteq> Cod (g \<cdot> f)"
        using assms 1 incl_def by auto
      moreover have "g \<cdot> f = mkArr (Dom f) (Cod g) (restrict (\<lambda>x. x) (Dom f))"
        using assms 1 Fun_comp incl_def Fun_mkArr mkArr_Fun Fun_ide comp_cod_arr
              ide_dom dom_comp cod_comp
        by metis
      ultimately show ?thesis using incl_def by force
    qed

    subsection "Image Factorization"

    text\<open>
      The image of an arrow is the object that corresponds to the set-theoretic
      image of the domain set under the function induced by the arrow.
\<close>

    abbreviation Img
    where "Img f \<equiv> Fun f ` Dom f"

    definition img
    where "img f = mkIde (Img f)"

    lemma ide_img [simp]:
    assumes "arr f"
    shows "ide (img f)"
    proof -
      have "Fun f ` Dom f \<subseteq> Cod f" using assms Fun_mapsto by blast
      moreover have "Cod f \<subseteq> Univ" using assms by simp
      ultimately show ?thesis using img_def by simp
    qed
    
    lemma set_img [simp]:
    assumes "arr f"
    shows "set (img f) = Img f"
    proof -
      have "Fun f ` set (dom f) \<subseteq> set (cod f) \<and> set (cod f) \<subseteq> Univ"
        using assms Fun_mapsto by auto
      hence "Fun f ` set (dom f) \<subseteq> Univ" by auto
      thus ?thesis using assms img_def set_mkIde by auto
    qed

    lemma img_point_in_Univ:
    assumes "\<guillemotleft>x : unity \<rightarrow> a\<guillemotright>"
    shows "img x \<in> Univ"
    proof -
      have "set (img x) = {Fun x unity}"
        using assms img_def terminal_unity terminal_char2
              image_empty image_insert mem_Collect_eq set_img
        by force
      thus "img x \<in> Univ" using assms terminal_char1 by auto
    qed

    lemma incl_in_img_cod:
    assumes "arr f"
    shows "incl_in (img f) (cod f)"
    proof (unfold img_def)
      have 1: "Img f \<subseteq> Cod f \<and> Cod f \<subseteq> Univ"
        using assms Fun_mapsto by auto
      hence 2: "ide (mkIde (Img f))" by fastforce
      moreover have "ide (cod f)" using assms by auto
      moreover have "set (mkIde (Img f)) \<subseteq> Cod f"
        using 1 2 by force
      ultimately show "incl_in (mkIde (Img f)) (cod f)"
        using incl_in_def by blast
    qed

    lemma img_point_elem_set:
    assumes "\<guillemotleft>x : unity \<rightarrow> a\<guillemotright>"
    shows "img x \<in> set a"
    proof -
      have "incl_in (img x) a"
        using assms incl_in_img_cod by auto
      hence "set (img x) \<subseteq> set a"
        using incl_in_def by blast
      moreover have "img x \<in> set (img x)"
        using assms img_point_in_Univ terminal_char2 by simp
      ultimately show ?thesis by auto
    qed

    text\<open>
      The corestriction of an arrow @{term f} is the arrow
      @{term "corestr f \<in> hom (dom f) (img f)"} that induces the same function
      on the universe as @{term f}.
\<close>

    definition corestr
    where "corestr f = mkArr (Dom f) (Img f) (Fun f)"
    
    lemma corestr_in_hom:
    assumes "arr f"
    shows "\<guillemotleft>corestr f : dom f \<rightarrow> img f\<guillemotright>"
    proof -
      have "Fun f \<in> Dom f \<rightarrow> Fun f ` Dom f \<and> Dom f \<subseteq> Univ"
        using assms by auto
      moreover have "Fun f ` Dom f \<subseteq> Univ"
      proof -
        have "Fun f ` Dom f \<subseteq> Cod f \<and> Cod f \<subseteq> Univ"
          using assms Fun_mapsto by auto
        thus ?thesis by blast
      qed
      ultimately have "mkArr (Dom f) (Fun f ` Dom f) (Fun f) \<in> hom (dom f) (img f)"
        using assms img_def mkArr_in_hom [of "Dom f" "Fun f ` Dom f" "Fun f"] by simp
      thus ?thesis using corestr_def by fastforce
    qed
    
    text\<open>
      Every arrow factors as a corestriction followed by an inclusion.
\<close>

    lemma img_fact:
    assumes "arr f"
    shows "S (incl_of (img f) (cod f)) (corestr f) = f"
    proof (intro arr_eqI)
      have 1: "\<guillemotleft>corestr f : dom f \<rightarrow> img f\<guillemotright>"
        using assms corestr_in_hom by blast
      moreover have 2: "\<guillemotleft>incl_of (img f) (cod f) : img f \<rightarrow> cod f\<guillemotright>"
        using assms incl_in_img_cod incl_incl_of by fast
      ultimately show P: "par (incl_of (img f) (cod f) \<cdot> corestr f) f"
        using assms in_homE by blast
      show "Fun (incl_of (img f) (cod f) \<cdot> corestr f) = Fun f"
      proof -
        have "Fun (incl_of (img f) (cod f) \<cdot> corestr f)
                 = restrict (Fun (incl_of (img f) (cod f)) o Fun (corestr f)) (Dom f)"
          using Fun_comp 1 2 P by auto
        also have
           "... = restrict (restrict (\<lambda>x. x) (Img f) o restrict (Fun f) (Dom f)) (Dom f)"
        proof -
          have "Fun (corestr f) = restrict (Fun f) (Dom f)"
            using assms corestr_def Fun_mkArr corestr_in_hom by force
          moreover have "Fun (incl_of (img f) (cod f)) = restrict (\<lambda>x. x) (Img f)"
          proof -
            have "arr (incl_of (img f) (cod f))" using incl_incl_of P by blast
            moreover have "incl_of (img f) (cod f) = mkArr (Img f) (Cod f) (\<lambda>x. x)"
              using assms by fastforce
            ultimately show ?thesis using assms img_def Fun_mkArr by metis
          qed
          ultimately show ?thesis by argo
        qed
        also have "... = Fun f"
         proof
          fix x
          show "restrict (restrict (\<lambda>x. x) (Img f) o restrict (Fun f) (Dom f)) (Dom f) x = Fun f x"
            using assms extensional_restrict Fun_mapsto extensional_arb [of "Fun f" "Dom f" x]
            by (cases "x \<in> Dom f", auto)
        qed
        finally show ?thesis by auto
      qed
    qed

    lemma Fun_corestr:
    assumes "arr f"
    shows "Fun (corestr f) = Fun f"
    proof -
      have 1: "f = incl_of (img f) (cod f) \<cdot> corestr f"
        using assms img_fact by auto
      hence 2: "Fun f = restrict (Fun (incl_of (img f) (cod f)) o Fun (corestr f)) (Dom f)"
        using assms by (metis Fun_comp dom_comp)
      also have "... = restrict (Fun (corestr f)) (Dom f)"
        using assms by (metis 1 2 Fun_mkArr seqE mkArr_Fun corestr_def)
      also have "... = Fun (corestr f)"
        using assms 1 by (metis Fun_def dom_comp extensional_restrict restrict_extensional)
      finally show ?thesis by auto
    qed
    
    subsection "Points and Terminal Objects"

    text\<open>
      To each element @{term t} of @{term "set a"} is associated a point
      @{term "mkPoint a t \<in> hom unity a"}.  The function induced by such
      a point is the constant-@{term t} function on the set @{term "{unity}"}.
\<close>

    definition mkPoint
    where "mkPoint a t \<equiv> mkArr {unity} (set a) (\<lambda>_. t)"

    lemma mkPoint_in_hom:
    assumes "ide a" and "t \<in> set a"
    shows "\<guillemotleft>mkPoint a t : unity \<rightarrow> a\<guillemotright>"
      using assms mkArr_in_hom
      by (metis Pi_I mkIde_set set_subset_Univ terminal_char2 terminal_unity mkPoint_def)

    lemma Fun_mkPoint:
    assumes "ide a" and "t \<in> set a"
    shows "Fun (mkPoint a t) = (\<lambda>_ \<in> {unity}. t)"
      using assms mkPoint_def terminal_unity by force

    text\<open>
      For each object @{term a} the function @{term "mkPoint a"} has as its inverse
      the restriction of the function @{term img} to @{term "hom unity a"}
\<close>

    lemma mkPoint_img:
    shows "img \<in> hom unity a \<rightarrow> set a"
    and "\<And>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<Longrightarrow> mkPoint a (img x) = x"
    proof -
      show "img \<in> hom unity a \<rightarrow> set a"
        using img_point_elem_set by simp
      show "\<And>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<Longrightarrow> mkPoint a (img x) = x"
      proof -
        fix x
        assume x: "\<guillemotleft>x : unity \<rightarrow> a\<guillemotright>"
        show "mkPoint a (img x) = x"
        proof (intro arr_eqI)
          have 0: "img x \<in> set a"
            using x img_point_elem_set by metis
          hence 1: "mkPoint a (img x) \<in> hom unity a"
            using x mkPoint_in_hom by force
          thus 2: "par (mkPoint a (img x)) x"
            using x by fastforce
          have "Fun (mkPoint a (img x)) = (\<lambda>_ \<in> {unity}. img x)"
            using 1 mkPoint_def by auto
          also have "... = Fun x"
          proof
            fix z
            have "z \<noteq> unity \<Longrightarrow> (\<lambda>_ \<in> {unity}. img x) z = Fun x z"
              using x Fun_mapsto Fun_def restrict_apply singletonD terminal_char2 terminal_unity
              by auto
            moreover have "(\<lambda>_ \<in> {unity}. img x) unity = Fun x unity"
              using x 0 elem_set_implies_set_eq_singleton set_img terminal_char2 terminal_unity
              by (metis 2 image_insert in_homE restrict_apply singletonI singleton_insert_inj_eq)
            ultimately show "(\<lambda>_ \<in> {unity}. img x) z = Fun x z" by auto
          qed
          finally show "Fun (mkPoint a (img x)) = Fun x" by auto
        qed
      qed
    qed

    lemma img_mkPoint:
    assumes "ide a"
    shows "mkPoint a \<in> set a \<rightarrow> hom unity a"
    and "\<And>t. t \<in> set a \<Longrightarrow> img (mkPoint a t) = t"
    proof -
      show "mkPoint a \<in> set a \<rightarrow> hom unity a"
        using assms(1) mkPoint_in_hom by simp
      show "\<And>t. t \<in> set a \<Longrightarrow> img (mkPoint a t) = t"
        proof -
        fix t
        assume t: "t \<in> set a"
        show "img (mkPoint a t) = t"
        proof -
          have 1: "arr (mkPoint a t)"
            using assms t mkPoint_in_hom by auto
          have "Fun (mkPoint a t) ` {unity} = {t}"
            using 1 mkPoint_def by simp
          thus ?thesis
            by (metis 1 t elem_set_implies_incl_in elem_set_implies_set_eq_singleton img_def
                      incl_in_def dom_mkArr mkIde_set terminal_char2 terminal_unity mkPoint_def)
        qed
      qed
    qed

    text\<open>
      For each object @{term a} the elements of @{term "hom unity a"} are therefore in
      bijective correspondence with @{term "set a"}.
\<close>

    lemma bij_betw_points_and_set:
    assumes "ide a"
    shows "bij_betw img (hom unity a) (set a)"
    proof (intro bij_betwI)
      show "img \<in> hom unity a \<rightarrow> set a"
        using assms mkPoint_img by auto
      show "mkPoint a \<in> set a \<rightarrow> hom unity a"
        using assms img_mkPoint by auto
      show "\<And>x. x \<in> hom unity a \<Longrightarrow> mkPoint a (img x) = x"
        using assms mkPoint_img by auto
      show "\<And>t. t \<in> set a \<Longrightarrow> img (mkPoint a t) = t"
        using assms img_mkPoint by auto
    qed

    text\<open>
      The function on the universe induced by an arrow @{term f} agrees, under the bijection
      between @{term "hom unity (dom f)"} and @{term "Dom f"}, with the action of @{term f}
      by composition on @{term "hom unity (dom f)"}.
\<close>

    lemma Fun_point:
    assumes "\<guillemotleft>x : unity \<rightarrow> a\<guillemotright>"
    shows "Fun x = (\<lambda>_ \<in> {unity}. img x)"
      using assms mkPoint_img img_mkPoint Fun_mkPoint [of a "img x"] img_point_elem_set
      by auto

    lemma comp_arr_mkPoint:
    assumes "arr f" and "t \<in> Dom f"
    shows "f \<cdot> mkPoint (dom f) t = mkPoint (cod f) (Fun f t)"
    proof (intro arr_eqI)
      have 0: "seq f (mkPoint (dom f) t)"
        using assms mkPoint_in_hom [of "dom f" t] by auto
      have 1: "\<guillemotleft>f \<cdot> mkPoint (dom f) t : unity \<rightarrow> cod f\<guillemotright>"
        using assms mkPoint_in_hom [of "dom f" t] by auto
      show "par (f \<cdot> mkPoint (dom f) t) (mkPoint (cod f) (Fun f t))"
      proof -
        have "\<guillemotleft>mkPoint (cod f) (Fun f t) : unity \<rightarrow> cod f\<guillemotright>"
          using assms Fun_mapsto mkPoint_in_hom [of "cod f" "Fun f t"] by auto
        thus ?thesis using 1 by fastforce
      qed
      show "Fun (f \<cdot> mkPoint (dom f) t) = Fun (mkPoint (cod f) (Fun f t))"
      proof -
        have "Fun (f \<cdot> mkPoint (dom f) t) = restrict (Fun f o Fun (mkPoint (dom f) t)) {unity}"
          using assms 0 1 Fun_comp terminal_char2 terminal_unity by auto
        also have "... = (\<lambda>_ \<in> {unity}. Fun f t)"
          using assms Fun_mkPoint by auto
        also have "... = Fun (mkPoint (cod f) (Fun f t))"
          using assms Fun_mkPoint [of "cod f" "Fun f t"] Fun_mapsto by fastforce
        finally show ?thesis by auto
      qed
    qed

    lemma comp_arr_point:
    assumes "arr f" and "\<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright>"
    shows "f \<cdot> x = mkPoint (cod f) (Fun f (img x))"
    proof -
      have "x = mkPoint (dom f) (img x)" using assms mkPoint_img by simp
      thus ?thesis using assms comp_arr_mkPoint [of f "img x"]
        by (simp add: img_point_elem_set)
    qed

    text\<open>
      This agreement allows us to express @{term "Fun f"} in terms of composition.
\<close>

    lemma Fun_in_terms_of_comp:
    assumes "arr f"
    shows "Fun f = restrict (img o S f o mkPoint (dom f)) (Dom f)"
    proof
      fix t
      have "t \<notin> Dom f \<Longrightarrow> Fun f t = restrict (img o S f o mkPoint (dom f)) (Dom f) t"
        using assms by (simp add: Fun_def)
      moreover have "t \<in> Dom f \<Longrightarrow>
                     Fun f t = restrict (img o S f o mkPoint (dom f)) (Dom f) t"
      proof -
        assume t: "t \<in> Dom f"
        have 1: "f \<cdot> mkPoint (dom f) t = mkPoint (cod f) (Fun f t)"
          using assms t comp_arr_mkPoint by simp
        hence "img (f \<cdot> mkPoint (dom f) t) = img (mkPoint (cod f) (Fun f t))" by simp
        thus ?thesis
        proof -
          have "Fun f t \<in> Cod f" using assms t Fun_mapsto by auto
          thus ?thesis using assms t 1 img_mkPoint by auto
        qed
      qed
      ultimately show "Fun f t = restrict (img o S f o mkPoint (dom f)) (Dom f) t" by auto
    qed

    text\<open>
      We therefore obtain a rule for proving parallel arrows equal by showing
      that they have the same action by composition on points.
\<close>

    (*
     * TODO: Find out why attempts to use this as the main rule for a proof loop
     * unless the specific instance is given.
     *)
    lemma arr_eqI':
    assumes "par f f'" and "\<And>x. \<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright> \<Longrightarrow> f \<cdot> x = f' \<cdot> x"
    shows "f = f'"
      using assms Fun_in_terms_of_comp mkPoint_in_hom by (intro arr_eqI, auto)

    text\<open>
      An arrow can therefore be specified by giving its action by composition on points.
      In many situations, this is more natural than specifying it as a function on the universe.
\<close>

    definition mkArr'
    where "mkArr' a b F = mkArr (set a) (set b) (img o F o mkPoint a)"

    lemma mkArr'_in_hom:
    assumes "ide a" and "ide b" and "F \<in> hom unity a \<rightarrow> hom unity b"
    shows "\<guillemotleft>mkArr' a b F : a \<rightarrow> b\<guillemotright>"
    proof -
      have "img o F o mkPoint a \<in> set a \<rightarrow> set b"
      proof
        fix t
        assume t: "t \<in> set a"
        thus "(img o F o mkPoint a) t \<in> set b"
          using assms mkPoint_in_hom img_point_elem_set [of "F (mkPoint a t)" b]
          by auto
      qed
      thus ?thesis
        using assms mkArr'_def mkArr_in_hom [of "set a" "set b"] by simp
    qed

    lemma comp_point_mkArr':
    assumes "ide a" and "ide b" and "F \<in> hom unity a \<rightarrow> hom unity b"
    shows "\<And>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<Longrightarrow> mkArr' a b F \<cdot> x = F x"
    proof -
      fix x
      assume x: "\<guillemotleft>x : unity \<rightarrow> a\<guillemotright>"
      have "Fun (mkArr' a b F) (img x) = img (F x)"
        unfolding mkArr'_def
        using assms x Fun_mkArr arr_mkArr img_point_elem_set mkPoint_img mkPoint_in_hom
        by (simp add: Pi_iff)
      hence "mkArr' a b F \<cdot> x = mkPoint b (img (F x))"
        using assms x mkArr'_in_hom [of a b F] comp_arr_point by auto
      thus "mkArr' a b F \<cdot> x = F x"
        using assms x mkPoint_img(2) by auto
    qed

    text\<open>
      A third characterization of terminal objects is as those objects whose set of
      points is a singleton.
\<close>

    lemma terminal_char3:
    assumes "\<exists>!x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright>"
    shows "terminal a"
    proof -
      have a: "ide a"
        using assms ide_cod mem_Collect_eq by blast
      hence 1: "bij_betw img (hom unity a) (set a)"
        using assms bij_betw_points_and_set by auto
      hence "img ` (hom unity a) = set a"
        by (simp add: bij_betw_def)
      moreover have "hom unity a = {THE x. x \<in> hom unity a}"
        using assms theI' [of "\<lambda>x. x \<in> hom unity a"] by auto
      ultimately have "set a = {img (THE x. x \<in> hom unity a)}"
        by (metis image_empty image_insert)
      thus ?thesis using a terminal_char1 by simp
    qed

    text\<open>
      The following is an alternative formulation of functional completeness, which says that
      any function on points uniquely determines an arrow.
\<close>

    lemma fun_complete':
    assumes "ide a" and "ide b" and "F \<in> hom unity a \<rightarrow> hom unity b"
    shows "\<exists>!f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<longrightarrow> f \<cdot> x = F x)"
    proof
      have 1: "\<guillemotleft>mkArr' a b F : a \<rightarrow> b\<guillemotright>" using assms mkArr'_in_hom by auto
      moreover have 2: "\<And>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<Longrightarrow> mkArr' a b F \<cdot> x = F x"
        using assms comp_point_mkArr' by auto
      ultimately show "\<guillemotleft>mkArr' a b F : a \<rightarrow> b\<guillemotright> \<and>
                       (\<forall>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<longrightarrow> mkArr' a b F \<cdot> x = F x)" by blast
      fix f
      assume f: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> a\<guillemotright> \<longrightarrow> f \<cdot> x = F x)"
      show "f = mkArr' a b F"
        using f 1 2 by (intro arr_eqI' [of f "mkArr' a b F"], fastforce, auto)
    qed

    subsection "The `Determines Same Function' Relation on Arrows"

    text\<open>
      An important part of understanding the structure of a category of sets and functions
      is to characterize when it is that two arrows ``determine the same function''.
      The following result provides one answer to this: two arrows with a common domain
      determine the same function if and only if they can be rendered equal by composing with
      a cospan of inclusions.
\<close>

    lemma eq_Fun_iff_incl_joinable:
    assumes "span f f'"
    shows "Fun f = Fun f' \<longleftrightarrow>
           (\<exists>m m'. incl m \<and> incl m' \<and> seq m f \<and> seq m' f' \<and> m \<cdot> f = m' \<cdot> f')"
    proof
      assume ff': "Fun f = Fun f'"
      let ?b = "mkIde (Cod f \<union> Cod f')"
      let ?m = "incl_of (cod f) ?b"
      let ?m' = "incl_of (cod f') ?b"
      have "incl ?m"
        using assms incl_incl_of [of "cod f" ?b] incl_in_def by simp
      have "incl ?m'"
        using assms incl_incl_of [of "cod f'" ?b] incl_in_def by simp
      have m: "?m = mkArr (Cod f) (Cod f \<union> Cod f') (\<lambda>x. x)"
        by (simp add: assms)
      have m': "?m' = mkArr (Cod f') (Cod f \<union> Cod f') (\<lambda>x. x)"
        by (simp add: assms)
      have seq: "seq ?m f \<and> seq ?m' f'"
        using assms m m' by simp
      have "?m \<cdot> f = ?m' \<cdot> f'"
      proof (intro arr_eqI)
        show par: "par (?m \<cdot> f) (?m' \<cdot> f')"
          using assms m m' by simp
        show "Fun (?m \<cdot> f) = Fun (?m' \<cdot> f')"
          using assms seq par ff' Fun_mapsto Fun_comp seqE
          by (metis Fun_ide Fun_mkArr comp_cod_arr ide_cod)
      qed
      hence "incl ?m \<and> incl ?m' \<and> seq ?m f \<and> seq ?m' f' \<and> ?m \<cdot> f = ?m' \<cdot> f'"
        using seq \<open>incl ?m\<close> \<open>incl ?m'\<close> by simp
      thus "\<exists>m m'. incl m \<and> incl m' \<and> seq m f \<and> seq m' f' \<and> m \<cdot> f = m' \<cdot> f'" by auto
      next
      assume ff': "\<exists>m m'. incl m \<and> incl m' \<and> seq m f \<and> seq m' f' \<and> m \<cdot> f = m' \<cdot> f'"
      show "Fun f = Fun f'"
      proof -
        from ff' obtain m m'
        where mm': "incl m \<and> incl m' \<and> seq m f \<and> seq m' f' \<and> m \<cdot> f = m' \<cdot> f'"
          by blast
        show ?thesis
          using ff' mm' Fun_incl seqE
          by (metis Fun_comp Fun_ide comp_cod_arr ide_cod)
      qed
    qed

    text\<open>
      Another answer to the same question: two arrows with a common domain determine the
      same function if and only if their corestrictions are equal.
\<close>

    lemma eq_Fun_iff_eq_corestr:
    assumes "span f f'"
    shows "Fun f = Fun f' \<longleftrightarrow> corestr f = corestr f'"
      using assms corestr_def Fun_corestr by metis

    subsection "Retractions, Sections, and Isomorphisms"

    text\<open>
      An arrow is a retraction if and only if its image coincides with its codomain.
\<close>

    lemma retraction_if_Img_eq_Cod:
    assumes "arr g" and "Img g = Cod g"
    shows "retraction g"
    and "ide (g \<cdot> mkArr (Cod g) (Dom g) (inv_into (Dom g) (Fun g)))"
    proof -
      let ?F = "inv_into (Dom g) (Fun g)"
      let ?f = "mkArr (Cod g) (Dom g) ?F"
      have f: "arr ?f"
      proof
        have "Cod g \<subseteq> Univ \<and> Dom g \<subseteq> Univ" using assms by auto
        moreover have "?F \<in> Cod g \<rightarrow> Dom g"
        proof
          fix y
          assume y: "y \<in> Cod g"
          let ?P = "\<lambda>x. x \<in> Dom g \<and> Fun g x = y"
          have "\<exists>x. ?P x" using y assms by force
          hence "?P (SOME x. ?P x)" using someI_ex [of ?P] by fast
          hence "?P (?F y)" using Hilbert_Choice.inv_into_def by metis
          thus "?F y \<in> Dom g" by auto
        qed
        ultimately show "Cod g \<subseteq> Univ \<and> Dom g \<subseteq> Univ \<and> ?F \<in> Cod g \<rightarrow> Dom g" by auto
      qed
      show "ide (g \<cdot> ?f)"
      proof -
        have "g = mkArr (Dom g) (Cod g) (Fun g)" using assms by auto
        hence "g \<cdot> ?f = mkArr (Cod g) (Cod g) (Fun g o ?F)"
          using assms(1) f comp_mkArr by metis
        moreover have "mkArr (Cod g) (Cod g) (\<lambda>y. y) = ..."
        proof (intro mkArr_eqI')
          show "arr (mkArr (Cod g) (Cod g) (\<lambda>y. y))"
            using assms arr_cod_iff_arr by auto
          show "\<And>y. y \<in> Cod g \<Longrightarrow> y = (Fun g o ?F) y"
            using assms by (simp add: f_inv_into_f)
        qed
        ultimately show ?thesis using assms f by auto
      qed
      thus "retraction g" by auto
    qed

    lemma retraction_char:
    shows "retraction g \<longleftrightarrow> arr g \<and> Img g = Cod g"
    proof
      assume G: "retraction g"
      show "arr g \<and> Img g = Cod g"
      proof
        show "arr g" using G by blast
        show "Img g = Cod g"
        proof -
          from G obtain f where f: "ide (g \<cdot> f)" by blast
          have "restrict (Fun g o Fun f) (Cod g) = restrict (\<lambda>x. x) (Cod g)"
            using f Fun_comp Fun_ide ide_compE by metis
          hence "Fun g ` Fun f ` Cod g = Cod g"
            by (metis image_comp image_ident image_restrict_eq)
          moreover have "Fun f ` Cod g \<subseteq> Dom g"
            using f Fun_mapsto arr_mkArr mkArr_Fun funcset_image
            by (metis seqE ide_compE ide_compE)
          moreover have "Img g \<subseteq> Cod g"
            using f Fun_mapsto by blast
          ultimately show ?thesis by blast
        qed
      qed
      next
      assume "arr g \<and> Img g = Cod g"
      thus "retraction g" using retraction_if_Img_eq_Cod by blast
    qed

    text\<open>
      Every corestriction is a retraction.
\<close>

    lemma retraction_corestr:
    assumes "arr f"
    shows "retraction (corestr f)"
      using assms retraction_char Fun_corestr corestr_in_hom by fastforce

    text\<open>
      An arrow is a section if and only if it induces an injective function on its
      domain, except in the special case that it has an empty domain set and a
      nonempty codomain set.
\<close>

    lemma section_if_inj:
    assumes "arr f" and "inj_on (Fun f) (Dom f)" and "Dom f = {} \<longrightarrow> Cod f = {}"
    shows "section f"
    and "ide (mkArr (Cod f) (Dom f)
                    (\<lambda>y. if y \<in> Img f then SOME x. x \<in> Dom f \<and> Fun f x = y
                         else SOME x. x \<in> Dom f)
                \<cdot> f)"
    proof -
      let ?P= "\<lambda>y. \<lambda>x. x \<in> Dom f \<and> Fun f x = y"
      let ?G = "\<lambda>y. if y \<in> Img f then SOME x. ?P y x else SOME x. x \<in> Dom f"
      let ?g = "mkArr (Cod f) (Dom f) ?G"
      have g: "arr ?g"
      proof -
        have 1: "Cod f \<subseteq> Univ" using assms by simp
        have 2: "Dom f \<subseteq> Univ" using assms by simp
        have 3: "?G \<in> Cod f \<rightarrow> Dom f"
        proof
          fix y
          assume Y: "y \<in> Cod f"
          show "?G y \<in> Dom f"
          proof (cases "y \<in> Img f")
            assume "y \<in> Img f"
            hence "(\<exists>x. ?P y x) \<and> ?G y = (SOME x. ?P y x)" using Y by auto
            hence "?P y (?G y)" using someI_ex [of "?P y"] by argo
            thus "?G y \<in> Dom f" by auto
            next
            assume "y \<notin> Img f"
            hence "(\<exists>x. x \<in> Dom f) \<and> ?G y = (SOME x. x \<in> Dom f)" using assms Y by auto
            thus "?G y \<in> Dom f" using someI_ex [of "\<lambda>x. x \<in> Dom f"] by argo
          qed
        qed
        show ?thesis using 1 2 3 by simp
      qed
      show "ide (?g \<cdot> f)"
      proof -
        have "f = mkArr (Dom f) (Cod f) (Fun f)" using assms by auto
        hence "?g \<cdot> f = mkArr (Dom f) (Dom f) (?G o Fun f)"
          using assms(1) g comp_mkArr [of "Dom f" "Cod f" "Fun f" "Dom f" ?G] by argo
        moreover have "mkArr (Dom f) (Dom f) (\<lambda>x. x) = ..."
        proof (intro mkArr_eqI')
          show "arr (mkArr (Dom f) (Dom f) (\<lambda>x. x))" using assms by auto
          show "\<And>x. x \<in> Dom f \<Longrightarrow> x = (?G o Fun f) x"
          proof -
            fix x
            assume x: "x \<in> Dom f"
            have "Fun f x \<in> Img f" using x by blast
            hence *: "(\<exists>x'. ?P (Fun f x) x') \<and> ?G (Fun f x) = (SOME x'. ?P (Fun f x) x')"
              by auto
            then have "?P (Fun f x) (?G (Fun f x))"
              using someI_ex [of "?P (Fun f x)"] by argo
            with * have "x = ?G (Fun f x)"
              using assms x inj_on_def [of "Fun f" "Dom f"] by simp
            thus "x = (?G o Fun f) x" by simp
          qed
        qed
        ultimately show ?thesis using assms by auto
      qed
      thus "section f" by auto
    qed

    lemma section_char:
    shows "section f \<longleftrightarrow> arr f \<and> (Dom f = {} \<longrightarrow> Cod f = {}) \<and> inj_on (Fun f) (Dom f)"
    proof
      assume f: "section f"
      from f obtain g where g: "ide (g \<cdot> f)" using section_def by blast
      show "arr f \<and> (Dom f = {} \<longrightarrow> Cod f = {}) \<and> inj_on (Fun f) (Dom f)"
      proof -
        have "arr f" using f by blast
        moreover have "Dom f = {} \<longrightarrow> Cod f = {}"
        proof -
          have "Cod f \<noteq> {} \<longrightarrow> Dom f \<noteq> {}"
          proof
            assume "Cod f \<noteq> {}"
            from this obtain y where "y \<in> Cod f" by blast
            hence "Fun g y \<in> Dom f"
              using g Fun_mapsto
              by (metis seqE ide_compE image_eqI retractionI retraction_char)
            thus "Dom f \<noteq> {}" by blast
          qed
          thus ?thesis by auto
        qed
        moreover have "inj_on (Fun f) (Dom f)"
        proof -
          have "restrict (Fun g o Fun f) (Dom f) = Fun (g \<cdot> f)"
            using g Fun_comp by (metis Fun_comp ide_compE)
          also have "... = restrict (\<lambda>x. x) (Dom f)"
            using g Fun_ide by auto
          finally have "restrict (Fun g o Fun f) (Dom f) = restrict (\<lambda>x. x) (Dom f)" by auto
          thus ?thesis using inj_onI inj_on_imageI2 inj_on_restrict_eq by metis
        qed
        ultimately show ?thesis by auto
      qed
      next
      assume F: "arr f \<and> (Dom f = {} \<longrightarrow> Cod f = {}) \<and> inj_on (Fun f) (Dom f)"
      thus "section f" using section_if_inj by auto
    qed

    text\<open>
      Section-retraction pairs can also be characterized by an inverse relationship
      between the functions they induce.
\<close>

    lemma section_retraction_char:
    shows "ide (g \<cdot> f) \<longleftrightarrow> antipar f g \<and> compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x)"
    proof
      show "ide (g \<cdot> f) \<Longrightarrow> antipar f g \<and> compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x)"
      proof -
        assume fg: "ide (g \<cdot> f)"
        have 1: "antipar f g" using fg by force
        moreover have "compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x)"
        proof
          fix x
          have "x \<notin> Dom f \<Longrightarrow> compose (Dom f) (Fun g) (Fun f) x = (\<lambda>x \<in> Dom f. x) x"
            by (simp add: compose_def)
          moreover have "x \<in> Dom f \<Longrightarrow>
                         compose (Dom f) (Fun g) (Fun f) x = (\<lambda>x \<in> Dom f. x) x"
            using fg 1 Fun_comp by (metis Fun_comp Fun_ide compose_eq' ide_compE)
          ultimately show "compose (Dom f) (Fun g) (Fun f) x = (\<lambda>x \<in> Dom f. x) x" by auto
        qed
        ultimately show ?thesis by auto
      qed
      show "antipar f g \<and> compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x) \<Longrightarrow> ide (g \<cdot> f)"
      proof -
        assume fg: "antipar f g \<and> compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x)"
        show "ide (g \<cdot> f)"
        proof -
          have 1: "arr (g \<cdot> f)" using fg by auto
          moreover have "Dom (g \<cdot> f) = Cod (S g f)"
            using fg 1 by force
          moreover have "Fun (g \<cdot> f) = (\<lambda>x \<in> Dom (g \<cdot> f). x)"
            using fg 1 by force
          ultimately show ?thesis using 1 ide_char by blast
        qed
      qed
    qed

    text\<open>
      Antiparallel arrows @{term f} and @{term g} are inverses if the functions
      they induce are inverses.
\<close>

    lemma inverse_arrows_char:
    shows "inverse_arrows f g \<longleftrightarrow>
             antipar f g \<and> compose (Dom f) (Fun g) (Fun f) = (\<lambda>x \<in> Dom f. x)
                         \<and> compose (Dom g) (Fun f) (Fun g) = (\<lambda>y \<in> Dom g. y)"
      using section_retraction_char by blast

    text\<open>
      An arrow is an isomorphism if and only if the function it induces is a bijection.
\<close>

    lemma iso_char:
    shows "iso f \<longleftrightarrow> arr f \<and> bij_betw (Fun f) (Dom f) (Cod f)"
    proof -
      have "iso f \<longleftrightarrow> section f \<and> retraction f"
        using iso_iff_section_and_retraction by auto
      also have "... \<longleftrightarrow> arr f \<and> inj_on (Fun f) (Dom f) \<and> Img f = Cod f"
        using section_char retraction_char by force
      also have "... \<longleftrightarrow> arr f \<and> bij_betw (Fun f) (Dom f) (Cod f)"
        using inj_on_def bij_betw_def [of "Fun f" "Dom f" "Cod f"] by meson
      finally show ?thesis by auto
    qed

    text\<open>
      The inverse of an isomorphism is constructed by inverting the induced function.
\<close>

    lemma inv_char:
    assumes "iso f"
    shows "inv f = mkArr (Cod f) (Dom f) (inv_into (Dom f) (Fun f))"
    proof -
      let ?g = "mkArr (Cod f) (Dom f) (inv_into (Dom f) (Fun f))"
      have "ide (f \<cdot> ?g)"
        using assms iso_is_retraction retraction_char retraction_if_Img_eq_Cod by simp
      moreover have "ide (?g \<cdot> f)"
      proof -
        let ?g' = "mkArr (Cod f) (Dom f)
                         (\<lambda>y. if y \<in> Img f then SOME x. x \<in> Dom f \<and> Fun f x = y
                              else SOME x. x \<in> Dom f)"
        have 1: "ide (?g' \<cdot> f)"
          using assms iso_is_section section_char section_if_inj by simp
        moreover have "?g' = ?g"
        proof
          show "arr ?g'" using 1 ide_compE by blast
          show "\<And>y. y \<in> Cod f \<Longrightarrow> (if y \<in> Img f then SOME x. x \<in> Dom f \<and> Fun f x = y
                                                  else SOME x. x \<in> Dom f)
                                     = inv_into (Dom f) (Fun f) y"
          proof -
            fix y
            assume "y \<in> Cod f"
            hence "y \<in> Img f" using assms iso_is_retraction retraction_char by metis
            thus "(if y \<in> Img f then SOME x. x \<in> Dom f \<and> Fun f x = y
                   else SOME x. x \<in> Dom f)
                     = inv_into (Dom f) (Fun f) y"
              using inv_into_def by metis
          qed
        qed
        ultimately show ?thesis by auto
      qed
      ultimately have "inverse_arrows f ?g" by auto
      thus ?thesis using inverse_unique by blast
    qed

    lemma Fun_inv:
    assumes "iso f"
    shows "Fun (inv f) = restrict (inv_into (Dom f) (Fun f)) (Cod f)"
      using assms inv_in_hom inv_char iso_inv_iso iso_is_arr Fun_mkArr by metis

    subsection "Monomorphisms and Epimorphisms"

    text\<open>
      An arrow is a monomorphism if and only if the function it induces is injective.
\<close>

    lemma mono_char:
    shows "mono f \<longleftrightarrow> arr f \<and> inj_on (Fun f) (Dom f)"
    proof
      assume f: "mono f"
      hence "arr f" using mono_def by auto
      moreover have "inj_on (Fun f) (Dom f)"
      proof (intro inj_onI)
        have 0: "inj_on (S f) (hom unity (dom f))"
        proof -
          have "hom unity (dom f) \<subseteq> {g. seq f g}"
            using f mono_def arrI by auto
          hence "\<exists>A. hom unity (dom f) \<subseteq> A \<and> inj_on (S f) A"
            using f mono_def by auto
          thus ?thesis
            by (meson subset_inj_on)
        qed
        fix x x'
        assume x: "x \<in> Dom f" and x': "x' \<in> Dom f" and xx': "Fun f x = Fun f x'"
        have 1: "mkPoint (dom f) x \<in> hom unity (dom f) \<and>
                 mkPoint (dom f) x' \<in> hom unity (dom f)"
          using x x' \<open>arr f\<close> mkPoint_in_hom by simp
        have "f \<cdot> mkPoint (dom f) x = f \<cdot> mkPoint (dom f) x'"
          using \<open>arr f\<close> x x' xx' comp_arr_mkPoint by simp
        hence "mkPoint (dom f) x = mkPoint (dom f) x'"
          using 0 1 inj_onD [of "S f" "hom unity (dom f)" "mkPoint (dom f) x"] by simp
        thus "x = x'"
          using \<open>arr f\<close> x x' img_mkPoint(2) img_mkPoint(2) ide_dom by metis
      qed
      ultimately show "arr f \<and> inj_on (Fun f) (Dom f)" by auto
      next
      assume f: "arr f \<and> inj_on (Fun f) (Dom f)"
      show "mono f"
      proof
        show "arr f" using f by auto
        show "\<And>g g'. seq f g \<and> seq f g' \<and> f \<cdot> g = f \<cdot> g' \<Longrightarrow> g = g'"
        proof -
          fix g g'
          assume gg': "seq f g \<and> seq f g' \<and> f \<cdot> g = f \<cdot> g'"
          show "g = g'"
          proof (intro arr_eqI)
            show par: "par g g'"
              using gg' dom_comp by (metis seqE)
            show "Fun g = Fun g'"
            proof
              fix x
              have "x \<notin> Dom g \<Longrightarrow> Fun g x = Fun g' x"
                using gg' by (simp add: par Fun_def)
              moreover have "x \<in> Dom g \<Longrightarrow> Fun g x = Fun g' x"
              proof -
                assume x: "x \<in> Dom g"
                have "Fun f (Fun g x) = Fun (f \<cdot> g) x"
                  using gg' x Fun_comp [of f g] by auto
                also have "... = Fun f (Fun g' x)"
                  using par f gg' x monoE by simp
                finally have "Fun f (Fun g x) = Fun f (Fun g' x)" by auto
                moreover have "Fun g x \<in> Dom f \<and> Fun g' x \<in> Dom f"
                  using par gg' x Fun_mapsto by fastforce
                ultimately show "Fun g x = Fun g' x"
                  using f gg' inj_onD [of "Fun f" "Dom f" "Fun g x" "Fun g' x"]
                  by simp
              qed
              ultimately show "Fun g x = Fun g' x" by auto
            qed
          qed
        qed
      qed
    qed

    text\<open>
      Inclusions are monomorphisms.
\<close>

    lemma mono_imp_incl:
    assumes "incl f"
    shows "mono f"
      using assms incl_def Fun_incl mono_char by auto

    text\<open>
      A monomorphism is a section, except in case it has an empty domain set and
      a nonempty codomain set.
\<close>

    lemma mono_imp_section:
    assumes "mono f" and "Dom f = {} \<longrightarrow> Cod f = {}"
    shows "section f"
      using assms mono_char section_char by auto

    text\<open>
      An arrow is an epimorphism if and only if either its image coincides with its
      codomain, or else the universe has only a single element (in which case all arrows
      are epimorphisms).
\<close>
  
    lemma epi_char:
    shows "epi f \<longleftrightarrow> arr f \<and> (Img f = Cod f \<or> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t'))"
    proof
      assume epi: "epi f"
      show "arr f \<and> (Img f = Cod f \<or> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t'))"
      proof -
        have f: "arr f" using epi epi_implies_arr by auto
        moreover have "\<not>(\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t') \<Longrightarrow> Img f = Cod f"
        proof -
          assume "\<not>(\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t')"
          from this obtain tt and ff
            where B: "tt \<in> Univ \<and> ff \<in> Univ \<and> tt \<noteq> ff" by blast
          show "Img f = Cod f"
          proof
            show "Img f \<subseteq> Cod f" using f Fun_mapsto by auto
            show "Cod f \<subseteq> Img f"
            proof
              let ?g = "mkArr (Cod f) {ff, tt} (\<lambda>y. tt)"
              let ?g' = "mkArr (Cod f) {ff, tt} (\<lambda>y. if \<exists>x. x \<in> Dom f \<and> Fun f x = y
                                                     then tt else ff)"
              let ?b = "mkIde {ff, tt}"
              have g: "\<guillemotleft>?g : cod f \<rightarrow> ?b\<guillemotright> \<and> Fun ?g = (\<lambda>y \<in> Cod f. tt)"
                using f B in_homI [of ?g] by simp
              have g': "?g' \<in> hom (cod f) ?b \<and>
                        Fun ?g' = (\<lambda>y \<in> Cod f. if \<exists>x. x \<in> Dom f \<and> Fun f x = y then tt else ff)"
                using f B in_homI [of ?g'] by simp
              have "?g \<cdot> f = ?g' \<cdot> f"
              proof (intro arr_eqI)
                show "par (?g \<cdot> f) (?g' \<cdot> f)"
                  using f g g' by auto
                show "Fun (?g \<cdot> f) = Fun (?g' \<cdot> f)"
                  using f g g' Fun_comp comp_mkArr by force
              qed
              hence gg': "?g = ?g'"
                using epi f g g' epiE [of f ?g ?g'] by fastforce
              fix y
              assume y: "y \<in> Cod f"
              have "Fun ?g' y = tt" using gg' g y by simp
              hence "(if \<exists>x. x \<in> Dom f \<and> Fun f x = y then tt else ff) = tt"
                using g' y by simp
              hence "\<exists>x. x \<in> Dom f \<and> Fun f x = y"
                using B by argo
              thus "y \<in> Img f" by blast
            qed
          qed
        qed
        ultimately show "arr f \<and> (Img f = Cod f \<or> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t'))"
          by fast
      qed
      next
      show "arr f \<and> (Img f = Cod f \<or> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t')) \<Longrightarrow> epi f"
      proof -
        have "arr f \<and> Img f = Cod f \<Longrightarrow> epi f"
        proof -
          assume f: "arr f \<and> Img f = Cod f"
          show "epi f"
            using f arr_eqI' epiE retractionI retraction_if_Img_eq_Cod retraction_is_epi
            by meson
        qed
        moreover have "arr f \<and> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t') \<Longrightarrow> epi f"
        proof -
          assume f: "arr f \<and> (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t')"
          have "\<And>f f'. par f f' \<Longrightarrow> f = f'"
          proof -
            fix f f'
            assume ff': "par f f'"
            show "f = f'"
            proof (intro arr_eqI)
              show "par f f'" using ff' by simp
              have "\<And>t t'. t \<in> Cod f \<and> t' \<in> Cod f \<Longrightarrow> t = t'"
                using f ff' set_subset_Univ ide_cod subsetD by blast
              thus "Fun f = Fun f'"
                using ff' Fun_mapsto [of f] Fun_mapsto [of f']
                      extensional_arb [of "Fun f" "Dom f"] extensional_arb [of "Fun f'" "Dom f"]
                by fastforce
            qed
          qed
          moreover have "\<And>g g'. par (g \<cdot> f) (g' \<cdot> f) \<Longrightarrow> par g g'"
            by force
          ultimately show "epi f"
            using f by (intro epiI; metis)
        qed
        ultimately show "arr f \<and> (Img f = Cod f \<or>  (\<forall>t t'. t \<in> Univ \<and> t' \<in> Univ \<longrightarrow> t = t'))
                           \<Longrightarrow> epi f"
          by auto
      qed
    qed

    text\<open>
      An epimorphism is a retraction, except in the case of a degenerate universe with only
      a single element.
\<close>

    lemma epi_imp_retraction:
    assumes "epi f" and "\<exists>t t'. t \<in> Univ \<and> t' \<in> Univ \<and> t \<noteq> t'"
    shows "retraction f"
      using assms epi_char retraction_char by auto

    text\<open>
      Retraction/inclusion factorization is unique (not just up to isomorphism -- remember
      that the notion of inclusion is not categorical but depends on the arbitrarily chosen
      @{term img}).
\<close>

    lemma unique_retr_incl_fact:
    assumes "seq m e" and "seq m' e'" and "m \<cdot> e = m' \<cdot> e'"
    and "incl m" and "incl m'" and "retraction e" and "retraction e'"
    shows "m = m'" and "e = e'"
    proof -
      have 1: "cod m = cod m' \<and> dom e = dom e'"
        using assms(1-3) by (metis dom_comp cod_comp)
      hence 2: "span e e'" using assms(1-2) by blast
      hence 3: "Fun e = Fun e'"
        using assms eq_Fun_iff_incl_joinable by meson
      hence "img e = img e'" using assms 1 img_def by auto
      moreover have "img e = cod e \<and> img e' = cod e'"
        using assms(6-7) retraction_char img_def by simp
      ultimately have "par e e'" using 2 by simp
      thus "e = e'" using 3 arr_eqI by blast
      hence "par m m'" using assms(1) assms(2) 1 by fastforce
      thus "m = m'" using assms(4) assms(5) incls_coherent by blast
    qed

  end

  section "Concrete Set Categories"

  text\<open>
    The \<open>set_category\<close> locale is useful for stating results that depend on a
    category of @{typ 'a}-sets and functions, without having to commit to a particular
    element type @{typ 'a}.  However, in applications we often need to work with a
    category of sets and functions that is guaranteed to contain sets corresponding
    to the subsets of some extrinsically given type @{typ 'a}.
    A \emph{concrete set category} is a set category \<open>S\<close> that is equipped
    with an injective function @{term \<iota>} from type @{typ 'a} to \<open>S.Univ\<close>.
    The following locale serves to facilitate some of the technical aspects of passing
    back and forth between elements of type @{typ 'a} and the elements of \<open>S.Univ\<close>.
\<close>

  locale concrete_set_category = set_category S
    for S :: "'s comp"      (infixr "\<cdot>\<^sub>S" 55)
    and U :: "'a set"
    and \<iota> :: "'a \<Rightarrow> 's" +
    assumes \<iota>_mapsto: "\<iota> \<in> U \<rightarrow> Univ"
    and inj_\<iota>: "inj_on \<iota> U"
  begin

    abbreviation \<o>
    where "\<o> \<equiv> inv_into U \<iota>"

    lemma \<o>_mapsto:
    shows "\<o> \<in> \<iota> ` U \<rightarrow> U"
      by (simp add: inv_into_into)

    lemma \<o>_\<iota> [simp]:
    assumes "x \<in> U"
    shows "\<o> (\<iota> x) = x"
      using assms inj_\<iota> inv_into_f_f by simp
      
    lemma \<iota>_\<o> [simp]:
    assumes "t \<in> \<iota> ` U"
    shows "\<iota> (\<o> t) = t"
      using assms o_def inj_\<iota> by auto

  end

end
