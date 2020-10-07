section \<open>Coinductive Lists\<close>

theory Coinductive_List_Extensions
imports
  Coinductive.Coinductive_List
  Coinductive.Coinductive_List_Prefix
  Coinductive.Coinductive_Stream
  "../Extensions/List_Extensions"
  "../Extensions/ESet_Extensions"
begin

  hide_const (open) Sublist.prefix
  hide_const (open) Sublist.suffix

  declare list_of_lappend[simp]
  declare lnth_lappend1[simp]
  declare lnth_lappend2[simp]
  declare lprefix_llength_le[dest]
  declare Sup_llist_def[simp]
  declare length_list_of[simp]
  declare llast_linfinite[simp]
  declare lnth_ltake[simp]
  declare lappend_assoc[simp]
  declare lprefix_lappend[simp]

  lemma lprefix_lSup_revert: "lSup = Sup" "lprefix = less_eq" by auto
  lemma admissible_lprefixI[cont_intro]:
    assumes "mcont lub ord lSup lprefix f"
    assumes "mcont lub ord lSup lprefix g"
    shows "ccpo.admissible lub ord (\<lambda> x. lprefix (f x) (g x))"
    using ccpo_class.admissible_leI assms unfolding lprefix_lSup_revert by this
  lemma llist_lift_admissible:
    assumes "ccpo.admissible lSup lprefix P"
    assumes "\<And> u. u \<le> v \<Longrightarrow> lfinite u \<Longrightarrow> P u"
    shows "P v"
    using assms by (metis LNil_lprefix le_llist_conv_lprefix lfinite.simps llist_gen_induct)

  abbreviation "linfinite w \<equiv> \<not> lfinite w"

  notation LNil ("<>")
  notation LCons (infixr "%" 65)
  notation lzip (infixr "\<bar>\<bar>" 51)
  notation lappend (infixr "$" 65)
  notation lnth (infixl "?" 100)

  syntax "_llist" :: "args \<Rightarrow> 'a llist" ("<_>")
  translations
    "<a, x>" \<rightleftharpoons> "a % <x>"
    "<a>" \<rightleftharpoons> "a % <>"

  lemma eq_LNil_conv_lnull[simp]: "w = <> \<longleftrightarrow> lnull w" by auto
  lemma Collect_lnull[simp]: "{w. lnull w} = {<>}" by auto

  lemma inj_on_ltake: "inj_on (\<lambda> k. ltake k w) {.. llength w}"
    by (rule inj_onI, auto, metis llength_ltake min_def)

  lemma lnth_inf_llist'[simp]: "lnth (inf_llist f) = f" by auto

  lemma not_lnull_lappend_startE[elim]:
    assumes "\<not> lnull w"
    obtains a v
    where "w = <a> $ v"
    using not_lnull_conv assms by (simp, metis)
  lemma not_lnull_lappend_endE[elim]:
    assumes "\<not> lnull w"
    obtains a v
    where "w = v $ <a>"
  proof (cases "lfinite w")
    case False
    show ?thesis
    proof
      show "w = w $ <a>" using lappend_inf False by force
    qed
  next
    case True
    show ?thesis
    using True assms that
    proof (induct arbitrary: thesis)
      case (lfinite_LNil)
      show ?case using lfinite_LNil by auto
    next
      case (lfinite_LConsI w a)
      show ?case
      proof (cases "lnull w")
        case False
        obtain b v where 1: "w = v $ <b>" using lfinite_LConsI(2) False by this
        show ?thesis
        proof (rule lfinite_LConsI(4))
          show "a % w = (a % v) $ <b>" unfolding 1 by simp
        qed
      next
        case True
        show ?thesis
        proof (rule lfinite_LConsI(4))
          show "a % w = <> $ <a>" using True by simp
        qed
      qed
    qed
  qed

  lemma llength_lappend_startE[elim]:
    assumes "llength w \<ge> eSuc n"
    obtains a v
    where "w = <a> $ v" "llength v \<ge> n"
  proof -
    have 1: "\<not> lnull w" using assms by auto
    show ?thesis using assms 1 that by auto
  qed
  lemma llength_lappend_endE[elim]:
    assumes "llength w \<ge> eSuc n"
    obtains a v
    where "w = v $ <a>" "llength v \<ge> n"
  proof -
    have 1: "\<not> lnull w" using assms by auto
    show ?thesis using assms 1 that by auto
  qed

  lemma llength_lappend_start'E[elim]:
    assumes "llength w = enat (Suc n)"
    obtains a v
    where "w = <a> $ v" "llength v = enat n"
  proof -
    have 1: "llength w \<ge> eSuc (enat n)" using assms by simp
    obtain a v where 2: "w = <a> $ v" using 1 by blast
    show ?thesis
    proof
      show "w = <a> $ v" using 2(1) by this
      show "llength v = enat n" using assms unfolding 2(1) by (simp, metis eSuc_enat eSuc_inject)
    qed
  qed
  lemma llength_lappend_end'E[elim]:
    assumes "llength w = enat (Suc n)"
    obtains a v
    where "w = v $ <a>" "llength v = enat n"
  proof -
    have 1: "llength w \<ge> eSuc (enat n)" using assms by simp
    obtain a v where 2: "w = v $ <a>" using 1 by blast
    show ?thesis
    proof
      show "w = v $ <a>" using 2(1) by this
      show "llength v = enat n" using assms unfolding 2(1) by (simp, metis eSuc_enat eSuc_inject)
    qed
  qed

  lemma ltake_llast[simp]:
    assumes "enat k < llength w"
    shows "llast (ltake (enat (Suc k)) w) = w ? k"
  proof -
    have 1: "llength (ltake (enat (Suc k)) w) = eSuc (enat k)"using min.absorb_iff1 assms by auto
    have "llast (ltake (enat (Suc k)) w) = ltake (enat (Suc k)) w ? k"
      using llast_conv_lnth 1 by this
    also have "\<dots> = w ? k" by (rule lnth_ltake, simp)
    finally show ?thesis by this
  qed

  lemma linfinite_llength[dest, simp]:
    assumes "linfinite w"
    shows "enat k < llength w"
    using assms not_lfinite_llength by force

  lemma llist_nth_eqI[intro]:
    assumes "llength u = llength v"
    assumes "\<And> i. enat i < llength u \<Longrightarrow> enat i < llength v \<Longrightarrow> u ? i = v ? i"
    shows "u = v"
  using assms
  proof (coinduction arbitrary: u v)
    case Eq_llist
    have 10: "llength u = llength v" using Eq_llist by auto
    have 11: "\<And> i. enat i < llength u \<Longrightarrow>  enat i < llength v \<Longrightarrow> u ? i = v ? i"
      using Eq_llist by auto
    show ?case
    proof (intro conjI impI exI allI)
      show "lnull u \<longleftrightarrow> lnull v" using 10 by auto
    next
      assume 20: "\<not> lnull u" "\<not> lnull v"
      show "lhd u = lhd v" using lhd_conv_lnth enat_0 11 20 by force
    next
      show "ltl u = ltl u" by rule
    next
      show "ltl v = ltl v" by rule
    next
      assume 30: "\<not> lnull u" "\<not> lnull v"
      show "llength (ltl u) = llength (ltl v)" using 10 30 by force
    next
      fix i
      assume 40: "\<not> lnull u" "\<not> lnull v" "enat i < llength (ltl u)" "enat i < llength (ltl v)"
      have 41: "u ? Suc i = v ? Suc i"
      proof (rule 11)
        show "enat (Suc i) < llength u" using Suc_ile_eq 40(1) 40(3) by auto
        show "enat (Suc i) < llength v" using Suc_ile_eq 40(2) 40(4) by auto
      qed
      show "ltl u ? i = ltl v ? i" using lnth_ltl 40(1-2) 41 by metis
    qed
  qed

  primcorec lscan :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a llist \<Rightarrow> 'b \<Rightarrow> 'b llist"
    where "lscan f w a = (case w of <> \<Rightarrow> <a> | x % xs \<Rightarrow> a % lscan f xs (f x a))"

  lemma lscan_simps[simp]:
    "lscan f <> a = <a>"
    "lscan f (x % xs) a = a % lscan f xs (f x a)"
    by (metis llist.simps(4) lscan.code, metis llist.simps(5) lscan.code)

  lemma lscan_lfinite[iff]: "lfinite (lscan f w a) \<longleftrightarrow> lfinite w"
  proof
    assume "lfinite (lscan f w a)"
    thus "lfinite w"
    proof (induct "lscan f w a" arbitrary: w a rule: lfinite_induct)
      case LNil
      show ?case using LNil by simp
    next
      case LCons
      show ?case by (cases w, simp, simp add: LCons(3))
    qed
  next
    assume "lfinite w"
    thus "lfinite (lscan f w a)" by (induct arbitrary: a, auto)
  qed
  lemma lscan_llength[simp]: "llength (lscan f w a) = eSuc (llength w)"
  proof (cases "lfinite w")
    case False
    have 1: "llength (lscan f w a) = \<infinity>" using not_lfinite_llength False by auto
    have 2: "llength w = \<infinity>" using not_lfinite_llength False by auto
    show ?thesis using 1 2 by simp
  next
    case True
    show ?thesis using True by (induct arbitrary: a, auto)
  qed

  function lfold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a llist \<Rightarrow> 'b \<Rightarrow> 'b"
    where "lfinite w \<Longrightarrow> lfold f w = fold f (list_of w)" | "linfinite w \<Longrightarrow> lfold f w = id"
    by (auto, metis) termination by lexicographic_order

  lemma lfold_llist_of[simp]: "lfold f (llist_of xs) = fold f xs" by simp

  lemma finite_UNIV_llength_eq:
    assumes "finite (UNIV :: 'a set)"
    shows "finite {w :: 'a llist. llength w = enat n}"
  proof (induct n)
    case (0)
    show ?case by simp
  next
    case (Suc n)
    have 1: "finite ({v. llength v = enat n} \<times> UNIV :: ('a llist \<times> 'a) set)"
      using Suc assms by simp
    have 2: "finite ((\<lambda> (v, a). v $ <a> :: 'a llist ) ` ({v. llength v = enat n} \<times> UNIV))"
      using 1 by auto
    have 3: "finite {v $ <a> :: 'a llist |v a. llength v = enat n}"
    proof -
      have 0: "{v $ <a> :: 'a llist  |v a. llength v = enat n} =
        (\<lambda> (v, a). v $ <a> :: 'a llist ) ` ({v. llength v = enat n} \<times> UNIV)" by auto
      show ?thesis using 2 unfolding 0 by this
    qed
    have 4: "finite {w :: 'a llist . llength w = enat (Suc n)}"
    proof -
      have 0: "{w :: 'a llist . llength w = enat (Suc n)} =
        {v $ <a> :: 'a llist  |v a. llength v = enat n}" by force
      show ?thesis using 3 unfolding 0 by this
    qed
    show ?case using 4 by this
  qed
  lemma finite_UNIV_llength_le:
    assumes "finite (UNIV :: 'a set)"
    shows "finite {w :: 'a llist. llength w \<le> enat n}"
  proof -
    have 1: "{w. llength w \<le> enat n} = (\<Union> k \<le> n. {w. llength w = enat k})"
      by (auto, metis atMost_iff enat_ile enat_ord_simps(1))
    show ?thesis unfolding 1 using finite_UNIV_llength_eq assms by auto
  qed

  lemma lprefix_ltake[dest]: "u \<le> v \<Longrightarrow> u = ltake (llength u) v"
    by (metis le_llist_conv_lprefix lprefix_conv_lappend ltake_all ltake_lappend1 order_refl)
  lemma prefixes_set: "{v. v \<le> w} = {ltake k w |k. k \<le> llength w}" by fastforce
  lemma esize_prefixes[simp]: "esize {v. v \<le> w} = eSuc (llength w)"
  proof -
    have "esize {v. v \<le> w} = esize {ltake k w |k. k \<le> llength w}" unfolding prefixes_set by rule
    also have "\<dots> = esize ((\<lambda> k. ltake k w) ` {.. llength w})"
      unfolding atMost_def image_Collect by rule
    also have "\<dots> = esize {.. llength w}" using inj_on_ltake esize_image by blast
    also have "\<dots> = eSuc (llength w)" by simp
    finally show ?thesis by this
  qed
  lemma prefix_subsume: "v \<le> w \<Longrightarrow> u \<le> w \<Longrightarrow> llength v \<le> llength u \<Longrightarrow> v \<le> u"
    by (metis le_llist_conv_lprefix lprefix_conv_lappend
      lprefix_ltake ltake_is_lprefix ltake_lappend1)

  lemma ltake_infinite[simp]: "ltake \<infinity> w = w" by (metis enat_ord_code(3) ltake_all)

  lemma lprefix_infinite:
    assumes "u \<le> v" "linfinite u"
    shows "u = v"
  proof -
    have 1: "llength u = \<infinity>" using not_lfinite_llength assms(2) by this
    have "u = ltake (llength u) v" using lprefix_ltake assms(1) by this
    also have "\<dots> = v" using 1 by simp
    finally show ?thesis by this
  qed

  instantiation llist :: (type) esize_order
  begin

    definition [simp]: "esize \<equiv> llength"

    instance
    proof
      fix w :: "'a llist"
      assume 1: "esize w \<noteq> \<infinity>"
      show "finite {v. v \<le> w}"
        using esize_prefixes 1 by (metis eSuc_eq_infinity_iff esize_set.simps(2) esize_llist_def)
    next
      fix u v :: "'a llist"
      assume 1: "u \<le> v"
      show "esize u \<le> esize v" using lprefix_llength_le 1 by auto
    next
      fix u v :: "'a llist"
      assume 1: "u < v"
      show "esize u < esize v" using lstrict_prefix_llength_less 1 by auto
    qed

  end

  subsection \<open>Index Sets\<close>
  
    definition liset :: "'a set \<Rightarrow> 'a llist \<Rightarrow> nat set"
      where "liset A w \<equiv> {i. enat i < llength w \<and> w ? i \<in> A}"

    lemma lisetI[intro]:
      assumes "enat i < llength w" "w ? i \<in> A"
      shows "i \<in> liset A w"
      using assms unfolding liset_def by auto
    lemma lisetD[dest]:
      assumes "i \<in> liset A w"
      shows "enat i < llength w" "w ? i \<in> A"
      using assms unfolding liset_def by auto

    lemma liset_finite:
      assumes "lfinite w"
      shows "finite (liset A w)"
    proof
      show "liset A w \<subseteq> {i. enat i < llength w}" by auto
      show "finite {i. enat i < llength w}" using lfinite_finite_index assms by this
    qed

    lemma liset_nil[simp]: "liset A <> = {}" by auto
    lemma liset_cons_not_member[simp]:
      assumes "a \<notin> A"
      shows "liset A (a % w) = Suc ` liset A w"
    proof -
      have "liset A (a % w) = {i. enat i < llength (a % w) \<and> (a % w) ? i \<in> A}" by auto
      also have "\<dots> = Suc ` {i. enat (Suc i) < llength (a % w) \<and> (a % w) ? Suc i \<in> A}"
        using Collect_split_Suc(1) assms by simp
      also have "\<dots> = Suc ` {i. enat i < llength w \<and> w ? i \<in> A}" using Suc_ile_eq by simp
      also have "\<dots> = Suc ` liset A w" by auto
      finally show ?thesis by this
    qed
    lemma liset_cons_member[simp]:
      assumes "a \<in> A"
      shows "liset A (a % w) = {0} \<union> Suc ` liset A w"
    proof -
      have "liset A (a % w) = {i. enat i < llength (a % w) \<and> (a % w) ? i \<in> A}" by auto
      also have "\<dots> = {0} \<union> Suc ` {i. enat (Suc i) < llength (a % w) \<and> (a % w) ? Suc i \<in> A}"
        using Collect_split_Suc(2) assms by simp
      also have "\<dots> = {0} \<union> Suc ` {i. enat i < llength w \<and> w ? i \<in> A}" using Suc_ile_eq by simp
      also have "\<dots> = {0} \<union> Suc ` liset A w" by auto
      finally show ?thesis by this
    qed
  
    lemma liset_prefix:
      assumes "i \<in> liset A v" "u \<le> v" "enat i < llength u"
      shows "i \<in> liset A u"
    unfolding liset_def
    proof (intro CollectI conjI)
      have 1: "v ? i \<in> A" using assms(1) by auto
      show "enat i < llength u" using assms(3) by this
      show "u ? i \<in> A" using lprefix_lnthD assms(2, 3) 1 by force
    qed
    lemma liset_suffix:
      assumes "i \<in> liset A u" "u \<le> v"
      shows "i \<in> liset A v"
    unfolding liset_def
    proof (intro CollectI conjI)
      have 1: "enat i < llength u" "u ? i \<in> A" using assms(1) by auto
      show "enat i < llength v" using lprefix_llength_le 1(1) assms(2) by fastforce
      show "v ? i \<in> A" using lprefix_lnthD assms(2) 1 by force
    qed

    lemma liset_ltake[simp]: "liset A (ltake (enat k) w) = liset A w \<inter> {..< k}"
    proof (intro equalityI subsetI)
      fix i
      assume 1: "i \<in> liset A (ltake (enat k) w)"
      have 2: "enat i < enat k" using 1 by auto
      have 3: "ltake (enat k) w ? i = w ? i" using lnth_ltake 2 by this
      show "i \<in> liset A w \<inter> {..< k}" using 1 3 by fastforce
    next
      fix i
      assume 1: "i \<in> liset A w \<inter> {..< k}"
      have 2: "enat i < enat k" using 1 by auto
      have 3: "ltake (enat k) w ? i = w ? i" using lnth_ltake 2 by this
      show "i \<in> liset A (ltake (enat k) w)" using 1 3 by fastforce
    qed

    lemma liset_mono[dest]: "u \<le> v \<Longrightarrow> liset A u \<subseteq> liset A v"
      unfolding liset_def using lprefix_lnthD by fastforce
    lemma liset_cont[dest]:
      assumes "Complete_Partial_Order.chain less_eq C" "C \<noteq> {}"
      shows "liset A (\<Squnion> C) = (\<Union> w \<in> C. liset A w)"
    proof safe
      fix i
      assume 1: "i \<in> liset A (\<Squnion> C)"
      show "i \<in> (\<Union> w \<in> C. liset A w)"
      proof (cases "finite C")
        case False
        obtain w where 2: "w \<in> C" "enat i < llength w"
          using esize_llist_def infinite_chain_arbitrary_esize assms(1) False Suc_ile_eq by metis
        have 3: "w \<le> \<Squnion> C" using chain_lprefix_lSup assms(1) 2(1) by simp
        have 4: "i \<in> liset A w" using liset_prefix 1 3 2(2) by this
        show ?thesis using 2(1) 4 by auto
      next
        case True
        have 2: "\<Squnion> C \<in> C" using in_chain_finite assms(1) True assms(2) by this
        show ?thesis using 1 2 by auto
      qed
    next
      fix w i
      assume 1: "w \<in> C" "i \<in> liset A w"
      have 2: "w \<le> \<Squnion> C" using chain_lprefix_lSup assms(1) 1(1) by simp
      show "i \<in> liset A (\<Squnion> C)" using liset_suffix 1(2) 2 by this
    qed

    lemma liset_mcont: "Complete_Partial_Order2.mcont lSup lprefix Sup less_eq (liset A)"
      unfolding lprefix_lSup_revert by (blast intro: mcontI monotoneI contI)

    lemmas mcont2mcont_liset = liset_mcont[THEN lfp.mcont2mcont, simp, cont_intro]

  subsection \<open>Selections\<close>

    (* TODO: thm lfitler_K_False *)

    abbreviation "lproject A \<equiv> lfilter (\<lambda> a. a \<in> A)"
    abbreviation "lselect s w \<equiv> lnths w s"

    lemma lselect_to_lproject: "lselect s w = lmap fst (lproject (UNIV \<times> s) (w \<bar>\<bar> iterates Suc 0))"
    proof -
      have 1: "{(x, y). y \<in> s} = UNIV \<times> s" by auto
      have "lselect s w = lmap fst (lproject {(x, y). y \<in> s} (w \<bar>\<bar> iterates Suc 0))"
        unfolding lnths_def by simp
      also have "\<dots> = lmap fst (lproject (UNIV \<times> s) (w \<bar>\<bar> iterates Suc 0))" unfolding 1 by rule
      finally show ?thesis by this
    qed
    lemma lproject_to_lselect: "lproject A w = lselect (liset A w) w"
      unfolding lfilter_conv_lnths liset_def by rule

    lemma lproject_llength[simp]: "llength (lproject A w) = esize (liset A w)"
      by (induct rule: llist_induct) (auto)
    lemma lproject_lfinite[simp]: "lfinite (lproject A w) \<longleftrightarrow> finite (liset A w)"
      using lproject_llength esize_iff_infinite llength_eq_infty_conv_lfinite by metis

    lemma lselect_restrict_indices[simp]: "lselect {i \<in> s. enat i < llength w} w = lselect s w"
    proof (rule lnths_cong)
      show "w = w" by rule
    next
      fix n
      assume 1: "enat n < llength w"
      show "n \<in> {i \<in> s. enat i < llength w} \<longleftrightarrow> n \<in> s" using 1 by blast
    qed

    lemma lselect_llength: "llength (lselect s w) = esize {i \<in> s. enat i < llength w}"
    proof -
      have 1: "\<And> i. enat i < llength w \<Longrightarrow> (w \<bar>\<bar> iterates Suc 0) ? i = (w ? i, i)"
        by (metis Suc_funpow enat.distinct(1) enat_ord_simps(4) llength_iterates lnth_iterates
          lnth_lzip monoid_add_class.add.right_neutral)
      have 2: "{i. enat i < llength w \<and> (w \<bar>\<bar> iterates Suc 0) ? i \<in> UNIV \<times> s} =
        {i \<in> s. enat i < llength w}" using 1 by auto
      have "llength (lselect s w) = esize (liset (UNIV \<times> s) (w \<bar>\<bar> iterates Suc 0))"
        unfolding lselect_to_lproject by simp
      also have "\<dots> = esize {i. enat i < llength w \<and> (w \<bar>\<bar> iterates Suc 0) ? i \<in> UNIV \<times> s}"
        unfolding liset_def by simp
      also have "\<dots> = esize {i \<in> s. enat i < llength w}" unfolding 2 by rule
      finally show ?thesis by this
    qed
    lemma lselect_llength_le[simp]: "llength (lselect s w) \<le> esize s"
    proof -
      have "llength (lselect s w) = esize {i \<in> s. enat i < llength w}"
        unfolding lselect_llength by rule
      also have "\<dots> = esize (s \<inter> {i. enat i < llength w})" unfolding Collect_conj_eq by simp
      also have "\<dots> \<le> esize s" by blast
      finally show ?thesis by this
    qed
    lemma least_lselect_llength:
      assumes "\<not> lnull (lselect s w)"
      shows "enat (least s) < llength w"
    proof -
      have 0: "llength (lselect s w) > 0" using assms by auto
      have 1: "\<And> i. i \<in> s \<Longrightarrow> least s \<le> i" using Least_le 0 by fast
      obtain i where 2: "i \<in> s" "enat i < llength w" using 0 unfolding lselect_llength by auto
      have "enat (least s) \<le> enat i" using 1 2(1) by auto
      also have "\<dots> < llength w" using 2(2) by this
      finally show "enat (least s) < llength w" by this
    qed
    lemma lselect_lnull: "lnull (lselect s w) \<longleftrightarrow> (\<forall> i \<in> s. enat i \<ge> llength w)"
      unfolding llength_eq_0[symmetric] lselect_llength by auto

    lemma lselect_discard_start:
      assumes "\<And> i. i \<in> s \<Longrightarrow> k \<le> i"
      shows "lselect {i. k + i \<in> s} (ldropn k w) = lselect s w"
    proof -
      have 1: "lselect s (ltake (enat k) w) = <>"
        using assms by (fastforce simp add: lselect_lnull min_le_iff_disj)
      have "lselect {m. k + m \<in> s} (ldropn k w) =
        lselect s (ltake (enat k) w) $ lselect {m. k + m \<in> s} (ldropn k w)" unfolding 1 by simp
      also have "\<dots> = lselect s w" using lnths_split by rule
      finally show ?thesis by this
    qed
    lemma lselect_discard_end:
      assumes "\<And> i. i \<in> s \<Longrightarrow> i < k"
      shows "lselect s (ltake (enat k) w) = lselect s w"
    proof -
      have 1: "lselect {m. k + m \<in> s} (ldropn k w) = <>"
        using assms by (fastforce simp add: lselect_lnull min_le_iff_disj)
      have "lselect s (ltake (enat k) w) =
        lselect s (ltake (enat k) w) $ lselect {m. k + m \<in> s} (ldropn k w)" unfolding 1 by simp
      also have "\<dots> = lselect s w" using lnths_split by rule
      finally show ?thesis by this
    qed

    lemma lselect_least:
      assumes "\<not> lnull (lselect s w)"
      shows "lselect s w = w ? least s % lselect (s - {least s}) w"
    proof -
      have 0: "s \<noteq> {}" using assms by auto
      have 1: "least s \<in> s" using LeastI 0 by fast
      have 2: "\<And> i. i \<in> s \<Longrightarrow> least s \<le> i" using Least_le 0 by fast
      have 3: "\<And> i. i \<in> s - {least s} \<Longrightarrow> Suc (least s) \<le> i" using least_unique 2 by force
      have 4: "insert (least s) (s - {least s}) = s" using 1 by auto
      have 5: "enat (least s) < llength w" using least_lselect_llength assms by this
      have 6: "lselect (s - {least s}) (ltake (enat (least s)) w) = <>"
        by (rule, auto simp: lselect_llength dest: least_not_less)
      have 7: "lselect {i. Suc (least s) + i \<in> s - {least s}} (ldropn (Suc (least s)) w) =
        lselect (s - {least s}) w" using lselect_discard_start 3 by this
      have "lselect s w = lselect (insert (least s) (s - {least s})) w" unfolding 4 by simp
      also have "\<dots> = lselect (s - {least s}) (ltake (enat (least s)) w) $ <w ? least s> $
        lselect {m. Suc (least s) + m \<in> s - {least s}} (ldropn (Suc (least s)) w)"
        unfolding lnths_insert[OF 5] by simp
      also have "\<dots> = <w ? least s> $
        lselect {m. Suc (least s) + m \<in> s - {least s}} (ldropn (Suc (least s)) w)"
        unfolding 6 by simp
      also have "\<dots> = w ? (least s) % lselect (s - {least s}) w" unfolding 7 by simp
      finally show ?thesis by this
    qed

    lemma lselect_lnth[simp]:
      assumes "enat i < llength (lselect s w)"
      shows "lselect s w ? i = w ? nth_least s i"
    using assms
    proof (induct i arbitrary: s)
      case 0
      have 1: "\<not> lnull (lselect s w)" using 0 by auto
      show ?case using lselect_least 1 by force
    next
      case (Suc i)
      have 1: "\<not> lnull (lselect s w)" using Suc(2) by auto
      have 2: "lselect s w = w ? least s % lselect (s - {least s}) w" using lselect_least 1 by this
      have 3: "llength (lselect s w) = eSuc (llength (lselect (s - {least s}) w))" using 2 by simp
      have 4: "enat i < llength (lselect (s - {least s}) w)" using 3 Suc(2) by simp
      have "lselect s w ? Suc i = (w ? least s % lselect (s - {least s}) w) ? Suc i" using 2 by simp
      also have "\<dots> = lselect (s - {least s}) w ? i" by simp
      also have "\<dots> = w ? nth_least (s - {least s}) i" using Suc(1) 4 by simp
      also have "\<dots> = w ? nth_least s (Suc i)" by simp
      finally show ?case by this
    qed
    lemma lproject_lnth[simp]:
      assumes "enat i < llength (lproject A w)"
      shows "lproject A w ? i = w ? nth_least (liset A w) i"
      using assms unfolding lproject_to_lselect by simp

    lemma lproject_ltake[simp]:
      assumes "enat k \<le> llength (lproject A w)"
      shows "lproject A (ltake (enat (nth_least (lift (liset A w)) k)) w) =
        ltake (enat k) (lproject A w)"
    proof
      have "llength (lproject A (ltake (enat (nth_least (lift (liset A w)) k)) w)) =
        enat (card (liset A w \<inter> {..< nth_least (lift (liset A w)) k}))" by simp
      also have "\<dots> = enat (card {i \<in> liset A w. i < nth_least (lift (liset A w)) k})"
        unfolding lessThan_def Collect_conj_eq by simp
      also have "\<dots> = enat k" using assms by simp
      also have "\<dots> = llength (ltake (enat k) (lproject A w))" using min_absorb1 assms by force
      finally show "llength (lproject A (ltake (enat (nth_least (lift (liset A w)) k)) w)) =
        llength (ltake (enat k) (lproject A w))" by this
    next
      fix i
      assume 1: "enat i < llength (lproject A (ltake (enat (nth_least (lift (liset A w)) k)) w))"
      assume 2: "enat i < llength (ltake (enat k) (lproject A w))"
      obtain k' where 3: "k = Suc k'" using 2 nat.exhaust by auto
      have 4: "enat k' < llength (lproject A w)" using assms 3 by simp
      have 5: "i \<le> k'" using 2 3 by simp
      have 6: "nth_least (lift (liset A w)) k = Suc (nth_least (liset A w) k')"
        using 3 4 by (simp del: nth_least.simps)
      have 7: "nth_least (liset A w) i < Suc (nth_least (liset A w) k')"
      proof -
        have "nth_least (liset A w) i \<le> nth_least (liset A w) k'" using 4 5 by simp
        also have "\<dots> < Suc (nth_least (liset A w) k')" by simp
        finally show ?thesis by this
      qed
      have 8: "nth_least (liset A w \<inter> {..< Suc (nth_least (liset A w) k')}) i =
        nth_least (liset A w) i"
      proof (rule nth_least_eq)
        show "enat i < esize (liset A w \<inter> {..< Suc (nth_least (liset A w) k')})" using 1 6 by simp
        have "enat i \<le> enat k'" using 5 by simp
        also have "enat k' < esize (liset A w)" using 4 by simp
        finally show "enat i < esize (liset A w)" by this
      next
        fix j
        assume 1: "j \<le> nth_least (liset A w) i"
        show "j \<in> liset A w \<inter> {..< Suc (nth_least (liset A w) k')} \<longleftrightarrow> j \<in> liset A w"
          using 1 7 by simp
      qed
      have "lproject A (ltake (enat (nth_least (lift (liset A w)) k)) w) ? i =
        ltake (enat (Suc (nth_least (liset A w) k'))) w ?
        nth_least (liset A w \<inter> {..< Suc (nth_least (liset A w) k')}) i"
        using 1 6 by simp
      also have "\<dots> = ltake (enat (Suc (nth_least (liset A w) k'))) w ? nth_least (liset A w) i"
        using 8 by simp
      also have "\<dots> = w ? nth_least (liset A w) i" using 7 by simp
      also have "\<dots> = lproject A w ? i" using 2 by simp
      also have "\<dots> = ltake (enat k) (lproject A w) ? i" using 2 by simp
      finally show "lproject A (ltake (enat (nth_least (lift (liset A w)) k)) w) ? i =
        ltake (enat k) (lproject A w) ? i" by this
    qed

    lemma llength_less_llength_lselect_less:
      "enat i < esize s \<and> enat (nth_least s i) < llength w \<longleftrightarrow> enat i < llength (lselect s w)"
      using nth_least_less_esize_less unfolding lselect_llength by this

    lemma lselect_lselect'':
      assumes "\<And> i. i \<in> s \<Longrightarrow> enat i < llength w"
      assumes "\<And> i. i \<in> t \<Longrightarrow> enat i < llength (lselect s w)"
      shows "lselect t (lselect s w) = lselect (nth_least s ` t) w"
    proof
      note lselect_llength[simp]
      have 1: "\<And> i. i \<in> nth_least s ` t \<Longrightarrow> enat i < llength w" using assms by auto
      have 2: "t \<subseteq> {i. enat i < esize s}"
        using assms(2) lselect_llength_le less_le_trans by blast
      have 3: "inj_on (nth_least s) t" using subset_inj_on nth_least.inj_on 2 by this
      have "llength (lselect t (lselect s w)) = esize t" using assms(2) by simp
      also have "\<dots> = esize (nth_least s ` t)" using 3 by auto
      also have "\<dots> = llength (lselect (nth_least s ` t) w)" using 1 by simp
      finally show "llength (lselect t (lselect s w)) = llength (lselect (nth_least s ` t) w)"
        by this
    next
      fix i
      assume 1: "enat i < llength (lselect t (lselect s w))"
      assume 2: "enat i < llength (lselect (nth_least s ` t) w)"
      have 3: "enat i < esize t" using less_le_trans 1 lselect_llength_le by this
      have 4: "\<And> i. i \<in> t \<Longrightarrow> enat i < esize s"
        using assms(2) lselect_llength_le less_le_trans by blast
      have "lselect t (lselect s w) ? i = lselect s w ? nth_least t i" using 1 by simp
      also have "\<dots> = w ? nth_least s (nth_least t i)" using assms(2) 3 by simp
      also have "\<dots> = w ? nth_least (nth_least s ` t) i" using 3 4 by simp
      also have "\<dots> = lselect (nth_least s ` t) w ? i" using 2 by simp
      finally show "lselect t (lselect s w) ? i = lselect (nth_least s ` t) w ? i" by this
    qed

    lemma lselect_lselect'[simp]:
      assumes "\<And> i. i \<in> t \<Longrightarrow> enat i < esize s"
      shows "lselect t (lselect s w) = lselect (nth_least s ` t) w"
    proof -
      have 1: "nth_least {i \<in> s. enat i < llength w} ` {i \<in> t. enat i < llength (lselect s w)} =
        {i \<in> nth_least s ` t. enat i < llength w}"
      unfolding Compr_image_eq
      proof (rule image_cong)
        show "{i \<in> t. enat i < llength (lselect s w)} = {i \<in> t. enat (nth_least s i) < llength w}"
          using llength_less_llength_lselect_less assms by blast
      next
        fix i
        assume 1: "i \<in> {i \<in> t. enat (nth_least s i) < llength w}"
        have 2: "enat i < esize {i \<in> s. enat i < llength w}"
          using nth_least_less_esize_less assms 1 by blast
        show "nth_least {i \<in> s. enat i < llength w} i = nth_least s i" using 2 by simp
      qed
      have "lselect t (lselect s w) =
        lselect {i \<in> t. enat i < llength (lselect s w)} (lselect {i \<in> s. enat i < llength w} w)"
        by simp
      also have "\<dots> = lselect (nth_least {i \<in> s. enat i < llength w} `
        {i \<in> t. enat i < llength (lselect s w)}) w"
        by (rule lselect_lselect'', auto simp: lselect_llength)
      also have "\<dots> = lselect {i \<in> nth_least s ` t. enat i < llength w} w" unfolding 1 by rule
      also have "\<dots> = lselect (nth_least s ` t) w" by simp
      finally show ?thesis by this
    qed

    lemma lselect_lselect:
      "lselect t (lselect s w) = lselect (nth_least s ` {i \<in> t. enat i < esize s}) w"
    proof -
      have "lselect t (lselect s w) = lselect {i \<in> t. enat i < llength (lselect s w)} (lselect s w)"
        by simp
      also have "\<dots> = lselect (nth_least s ` {i \<in> t. enat i < llength (lselect s w)}) w"
        using lselect_llength_le less_le_trans by (blast intro: lselect_lselect')
      also have "\<dots> = lselect (nth_least s ` {i \<in> t. enat i < esize s}) w"
        using llength_less_llength_lselect_less by (auto intro!: lnths_cong)
      finally show ?thesis by this
    qed

    lemma lselect_lproject':
      assumes "\<And> i. i \<in> s \<Longrightarrow> enat i < llength w"
      shows "lproject A (lselect s w) = lselect (s \<inter> liset A w) w"
    proof -
      have 1: "\<And> i. i \<in> liset A (lselect s w) \<Longrightarrow> enat i < esize s" using less_le_trans by force
      have 2: "{i \<in> liset A (lselect s w). enat i < esize s} = liset A (lselect s w)"
        using 1 by auto
      have 3: "nth_least s ` liset A (lselect s w) = s \<inter> liset A w"
      proof safe
        fix k
        assume 4: "k \<in> liset A (lselect s w)"
        show "nth_least s k \<in> s" using 1 4 by simp
        show "nth_least s k \<in> liset A w"
          using llength_less_llength_lselect_less 4 unfolding liset_def by auto
      next
        fix k
        assume 1: "k \<in> s" "k \<in> liset A w"
        have 2: "nth_least s (card {i \<in> s. i < k}) = k" using nth_least_card 1(1) by this
        have 3: "enat (card {i \<in> s. i < k}) < llength (lselect s w)"
          unfolding lselect_llength using assms 1(1) by simp
        show "k \<in> nth_least s ` liset A (lselect s w)"
        proof
          show "k = nth_least s (card {i \<in> s. i < k})" using 2 by simp
          show "card {i \<in> s. i < k} \<in> liset A (lselect s w)" using 1(2) 2 3 by fastforce
        qed
      qed
      have "lproject A (lselect s w) = lselect (liset A (lselect s w)) (lselect s w)"
        unfolding lproject_to_lselect by rule
      also have "\<dots> = lselect (nth_least s ` {i \<in> liset A (lselect s w). enat i < esize s}) w"
        unfolding lselect_lselect by rule
      also have "\<dots> = lselect (nth_least s ` liset A (lselect s w)) w" unfolding 2 by rule
      also have "\<dots> = lselect (s \<inter> liset A w) w" unfolding 3 by rule
      finally show ?thesis by this
    qed

    lemma lselect_lproject[simp]: "lproject A (lselect s w) = lselect (s \<inter> liset A w) w"
    proof -
      have 1: "{i \<in> s. enat i < llength w} \<inter> liset A w = s \<inter> liset A w" by auto
      have "lproject A (lselect s w) = lproject A (lselect {i \<in> s. enat i < llength w} w)" by simp
      also have "\<dots> = lselect ({i \<in> s. enat i < llength w} \<inter> liset A w) w"
        by (rule lselect_lproject', simp)
      also have "\<dots> = lselect (s \<inter> liset A w) w" unfolding 1 by rule
      finally show ?thesis by this
    qed

    lemma lproject_lselect_subset[simp]:
      assumes "liset A w \<subseteq> s"
      shows "lproject A (lselect s w) = lproject A w"
    proof -
      have 1: "s \<inter> liset A w = liset A w" using assms by auto
      have "lproject A (lselect s w) = lselect (s \<inter> liset A w) w" by simp
      also have "\<dots> = lselect (liset A w) w" unfolding 1 by rule
      also have "\<dots> = lproject A w" unfolding lproject_to_lselect by rule
      finally show ?thesis by this
    qed

    lemma lselect_prefix[intro]:
      assumes "u \<le> v"
      shows "lselect s u \<le> lselect s v"
    proof (cases "lfinite u")
      case False
      show ?thesis using lprefix_infinite assms False by auto
    next
      case True
      obtain k where 1: "llength u = enat k" using True length_list_of by metis
      obtain w where 2: "v = u $ w" using lprefix_conv_lappend assms by auto
      have "lselect s u \<le> lselect s u $ lselect {n. n + k \<in> s} w" by simp
      also have "\<dots> = lselect s (u $ w)" using lnths_lappend_lfinite[symmetric] 1 by this
      also have "\<dots> = lselect s v" unfolding 2 by rule
      finally show ?thesis by this
    qed
    lemma lproject_prefix[intro]:
      assumes "u \<le> v"
      shows "lproject A u \<le> lproject A v"
      using lprefix_lfilterI assms by auto

    lemma lproject_prefix_limit[intro?]:
      assumes "\<And> v. v \<le> w \<Longrightarrow> lfinite v \<Longrightarrow> lproject A v \<le> x"
      shows "lproject A w \<le> x"
    proof -
      have 1: "ccpo.admissible lSup lprefix (\<lambda> v. lproject A v \<le> x)" by simp
      show ?thesis using llist_lift_admissible 1 assms(1) by this
    qed
    lemma lproject_prefix_limit':
      assumes "\<And> k. \<exists> v. v \<le> w \<and> enat k < llength v \<and> lproject A v \<le> x"
      shows "lproject A w \<le> x"
    proof (rule lproject_prefix_limit)
      fix u
      assume 1: "u \<le> w" "lfinite u"
      obtain k where 2: "llength u = enat k" using 1(2) by (metis length_list_of)
      obtain v where 3: "v \<le> w" "llength u < llength v" "lproject A v \<le> x"
        unfolding 2 using assms(1) by auto
      have 4: "llength u \<le> llength v" using 3(2) by simp
      have 5: "u \<le> v" using prefix_subsume 1(1) 3(1) 4 by this
      have "lproject A u \<le> lproject A v" using 5 by rule
      also have "\<dots> \<le> x" using 3(3) by this
      finally show "lproject A u \<le> x" by this
    qed

end
