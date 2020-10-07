theory Transition_System
imports
  Residual
begin

section \<open>Nominal Transition Systems and Bisimulations\<close>

subsection \<open>Basic Lemmas\<close>

lemma symp_eqvt [eqvt]:
  assumes "symp R" shows "symp (p \<bullet> R)"
using assms unfolding symp_def by (subst permute_fun_def)+ (simp add: permute_pure)


subsection \<open>Nominal transition systems\<close>

locale nominal_ts =
  fixes satisfies :: "'state::fs \<Rightarrow> 'pred::fs \<Rightarrow> bool"                (infix "\<turnstile>" 70)
    and transition :: "'state \<Rightarrow> ('act::bn,'state) residual \<Rightarrow> bool"  (infix "\<rightarrow>" 70)
  assumes satisfies_eqvt [eqvt]: "P \<turnstile> \<phi> \<Longrightarrow> p \<bullet> P \<turnstile> p \<bullet> \<phi>"
      and transition_eqvt [eqvt]: "P \<rightarrow> \<alpha>Q \<Longrightarrow> p \<bullet> P \<rightarrow> p \<bullet> \<alpha>Q"
begin

  lemma transition_eqvt':
    assumes "P \<rightarrow> \<langle>\<alpha>,Q\<rangle>" shows "p \<bullet> P \<rightarrow> \<langle>p \<bullet> \<alpha>, p \<bullet> Q\<rangle>"
  using assms by (metis abs_residual_pair_eqvt transition_eqvt)

end


subsection \<open>Bisimulations\<close>

context nominal_ts
begin

  definition is_bisimulation :: "('state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> bool" where
    "is_bisimulation R \<equiv>
      symp R \<and>
      (\<forall>P Q. R P Q \<longrightarrow> (\<forall>\<phi>. P \<turnstile> \<phi> \<longrightarrow> Q \<turnstile> \<phi>)) \<and>
      (\<forall>P Q. R P Q \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* Q \<longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> R P' Q')))"

  definition bisimilar :: "'state \<Rightarrow> 'state \<Rightarrow> bool"  (infix "\<sim>\<cdot>" 100) where
    "P \<sim>\<cdot> Q \<equiv> \<exists>R. is_bisimulation R \<and> R P Q"

  text \<open>@{const bisimilar} is an equivariant equivalence relation.\<close>

  lemma is_bisimulation_eqvt (*[eqvt]*):
    assumes "is_bisimulation R" shows "is_bisimulation (p \<bullet> R)"
  using assms unfolding is_bisimulation_def
  proof (clarify)
    assume 1: "symp R"
    assume 2: "\<forall>P Q. R P Q \<longrightarrow> (\<forall>\<phi>. P \<turnstile> \<phi> \<longrightarrow> Q \<turnstile> \<phi>)"
    assume 3: "\<forall>P Q. R P Q \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* Q \<longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> R P' Q'))"
    have "symp (p \<bullet> R)" (is ?S)
      using 1 by (simp add: symp_eqvt)
    moreover have "\<forall>P Q. (p \<bullet> R) P Q \<longrightarrow> (\<forall>\<phi>. P \<turnstile> \<phi> \<longrightarrow> Q \<turnstile> \<phi>)" (is ?T)
      proof (clarify)
        fix P Q \<phi>
        assume *: "(p \<bullet> R) P Q" and **: "P \<turnstile> \<phi>"
        from * have "R (-p \<bullet> P) (-p \<bullet> Q)"
          by (simp add: eqvt_lambda permute_bool_def unpermute_def)
        then show "Q \<turnstile> \<phi>"
          using 2 ** by (metis permute_minus_cancel(1) satisfies_eqvt)
      qed
    moreover have "\<forall>P Q. (p \<bullet> R) P Q \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* Q \<longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> (p \<bullet> R) P' Q'))" (is ?U)
      proof (clarify)
        fix P Q \<alpha> P'
        assume *: "(p \<bullet> R) P Q" and **: "bn \<alpha> \<sharp>* Q" and ***: "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
        from * have "R (-p \<bullet> P) (-p \<bullet> Q)"
          by (simp add: eqvt_lambda permute_bool_def unpermute_def)
        moreover have "bn (-p \<bullet> \<alpha>) \<sharp>* (-p \<bullet> Q)"
          using ** by (metis bn_eqvt fresh_star_permute_iff)
        moreover have "-p \<bullet> P \<rightarrow> \<langle>-p \<bullet> \<alpha>, -p \<bullet> P'\<rangle>"
          using *** by (metis transition_eqvt')
        ultimately obtain Q' where T: "-p \<bullet> Q \<rightarrow> \<langle>-p \<bullet> \<alpha>,Q'\<rangle>" and R: "R (-p \<bullet> P') Q'"
          using 3 by metis
        from T have "Q \<rightarrow> \<langle>\<alpha>, p \<bullet> Q'\<rangle>"
          by (metis permute_minus_cancel(1) transition_eqvt')
        moreover from R have "(p \<bullet> R) P' (p \<bullet> Q')"
          by (metis eqvt_apply eqvt_lambda permute_bool_def unpermute_def)
        ultimately show "\<exists>Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> (p \<bullet> R) P' Q'"
          by metis
      qed
    ultimately show "?S \<and> ?T \<and> ?U" by simp
  qed

  lemma bisimilar_eqvt (*[eqvt]*):
    assumes "P \<sim>\<cdot> Q" shows "(p \<bullet> P) \<sim>\<cdot> (p \<bullet> Q)"
  proof -
    from assms obtain R where *: "is_bisimulation R \<and> R P Q"
      unfolding bisimilar_def ..
    then have "is_bisimulation (p \<bullet> R)"
      by (simp add: is_bisimulation_eqvt)
    moreover from "*" have "(p \<bullet> R) (p \<bullet> P) (p \<bullet> Q)"
      by (metis eqvt_apply permute_boolI)
    ultimately show "(p \<bullet> P) \<sim>\<cdot> (p \<bullet> Q)"
      unfolding bisimilar_def by auto
  qed

  lemma bisimilar_reflp: "reflp bisimilar"
  proof (rule reflpI)
    fix x
    have "is_bisimulation (=)"
      unfolding is_bisimulation_def by (simp add: symp_def)
    then show "x \<sim>\<cdot> x"
      unfolding bisimilar_def by auto
  qed

  lemma bisimilar_symp: "symp bisimilar"
  proof (rule sympI)
    fix P Q
    assume "P \<sim>\<cdot> Q"
    then obtain R where *: "is_bisimulation R \<and> R P Q"
      unfolding bisimilar_def ..
    then have "R Q P"
      unfolding is_bisimulation_def by (simp add: symp_def)
    with "*" show "Q \<sim>\<cdot> P"
      unfolding bisimilar_def by auto
  qed

  lemma bisimilar_is_bisimulation: "is_bisimulation bisimilar"
  unfolding is_bisimulation_def proof
    show "symp (\<sim>\<cdot>)"
      by (fact bisimilar_symp)
  next
    show "(\<forall>P Q. P \<sim>\<cdot> Q \<longrightarrow> (\<forall>\<phi>. P \<turnstile> \<phi> \<longrightarrow> Q \<turnstile> \<phi>)) \<and>
      (\<forall>P Q. P \<sim>\<cdot> Q \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* Q \<longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> P' \<sim>\<cdot> Q')))"
      by (auto simp add: is_bisimulation_def bisimilar_def) blast
  qed

  lemma bisimilar_transp: "transp bisimilar"
  proof (rule transpI)
    fix P Q R
    assume PQ: "P \<sim>\<cdot> Q" and QR: "Q \<sim>\<cdot> R"
    let ?bisim = "bisimilar OO bisimilar"
    have "symp ?bisim"
      proof (rule sympI)
        fix P R
        assume "?bisim P R"
        then obtain Q where "P \<sim>\<cdot> Q" and "Q \<sim>\<cdot> R"
          by blast
        then have "R \<sim>\<cdot> Q" and "Q \<sim>\<cdot> P"
          by (metis bisimilar_symp sympE)+
        then show "?bisim R P"
          by blast
      qed
    moreover have "\<forall>P Q. ?bisim P Q \<longrightarrow> (\<forall>\<phi>. P \<turnstile> \<phi> \<longrightarrow> Q \<turnstile> \<phi>)"
      using bisimilar_is_bisimulation is_bisimulation_def by auto
    moreover have "\<forall>P Q. ?bisim P Q \<longrightarrow>
           (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* Q \<longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> ?bisim P' Q'))"
      proof (clarify)
        fix P R Q \<alpha> P'
        assume PR: "P \<sim>\<cdot> R" and RQ: "R \<sim>\<cdot> Q" and fresh: "bn \<alpha> \<sharp>* Q" and trans: "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
        \<comment> \<open>rename~@{term "\<langle>\<alpha>,P'\<rangle>"} to avoid~@{term R}, without touching~@{term Q}\<close>
        obtain p where 1: "(p \<bullet> bn \<alpha>) \<sharp>* R" and 2: "supp (\<langle>\<alpha>,P'\<rangle>, Q) \<sharp>* p"
          proof (rule at_set_avoiding2[of "bn \<alpha>" R "(\<langle>\<alpha>,P'\<rangle>, Q)", THEN exE])
            show "finite (bn \<alpha>)" by (fact bn_finite)
          next
            show "finite (supp R)" by (fact finite_supp)
          next
            show "finite (supp (\<langle>\<alpha>,P'\<rangle>, Q))" by (simp add: finite_supp supp_Pair)
          next
            show "bn \<alpha> \<sharp>* (\<langle>\<alpha>,P'\<rangle>, Q)" by (simp add: fresh fresh_star_Pair)
          qed metis
        from 2 have 3: "supp \<langle>\<alpha>,P'\<rangle> \<sharp>* p" and 4: "supp Q \<sharp>* p"
          by (simp add: fresh_star_Un supp_Pair)+
        from 3 have "\<langle>p \<bullet> \<alpha>, p \<bullet> P'\<rangle> = \<langle>\<alpha>,P'\<rangle>"
          using supp_perm_eq by fastforce
        then obtain pR' where 5: "R \<rightarrow> \<langle>p \<bullet> \<alpha>, pR'\<rangle>" and 6: "(p \<bullet> P') \<sim>\<cdot> pR'"
          using PR trans 1 by (metis (mono_tags, lifting) bisimilar_is_bisimulation bn_eqvt is_bisimulation_def)
        from fresh and 4 have "bn (p \<bullet> \<alpha>) \<sharp>* Q"
          by (metis bn_eqvt fresh_star_permute_iff supp_perm_eq)
        then obtain pQ' where 7: "Q \<rightarrow> \<langle>p \<bullet> \<alpha>, pQ'\<rangle>" and 8: "pR' \<sim>\<cdot> pQ'"
          using RQ 5 by (metis (full_types) bisimilar_is_bisimulation is_bisimulation_def)
        from 7 have "Q \<rightarrow> \<langle>\<alpha>, -p \<bullet> pQ'\<rangle>"
          using 4 by (metis permute_minus_cancel(2) supp_perm_eq transition_eqvt')
        moreover from 6 and 8 have "?bisim P' (-p \<bullet> pQ')"
          by (metis (no_types, hide_lams) bisimilar_eqvt permute_minus_cancel(2) relcompp.simps)
        ultimately show "\<exists>Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> ?bisim P' Q'"
          by metis
      qed
    ultimately have "is_bisimulation ?bisim"
      unfolding is_bisimulation_def by metis
    moreover have "?bisim P R"
      using PQ QR by blast
    ultimately show "P \<sim>\<cdot> R"
      unfolding bisimilar_def by meson
  qed

  lemma bisimilar_equivp: "equivp bisimilar"
  by (metis bisimilar_reflp bisimilar_symp bisimilar_transp equivp_reflp_symp_transp)

  lemma bisimilar_simulation_step:
    assumes "P \<sim>\<cdot> Q" and "bn \<alpha> \<sharp>* Q" and "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
    obtains Q' where "Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>" and "P' \<sim>\<cdot> Q'"
  using assms by (metis (poly_guards_query) bisimilar_is_bisimulation is_bisimulation_def)

end

end
