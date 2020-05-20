theory FL_Transition_System
imports
  Transition_System FS_Set
begin

section \<open>Nominal Transition Systems with Effects and \texorpdfstring{$F/L$}{F/L}-Bisimilarity\<close>

subsection \<open>Nominal transition systems with effects\<close>

text \<open>The paper defines an effect as a finitely supported function from states to states. It then
fixes an equivariant set~@{term \<F>} of effects. In our formalization, we avoid working with such a
(carrier) set, and instead introduce a type of (finitely supported) effects together with an
(equivariant) application operator for effects and states.

Equivariance (of the type of effects) is implicitly guaranteed (by the type of~@{const permute}).

\emph{First} represents the (finitely supported) set of effects that must be observed before
following a transition.\<close>

type_synonym 'eff first = "'eff fs_set"

text \<open>\emph{Later} is a function that represents how the set~$F$ (for \emph{first}) changes
depending on the action of a transition and the chosen effect.\<close>

type_synonym ('a,'eff) later = "'a \<times> 'eff first \<times> 'eff \<Rightarrow> 'eff first"

locale effect_nominal_ts = nominal_ts satisfies transition
  for satisfies :: "'state::fs \<Rightarrow> 'pred::fs \<Rightarrow> bool" (infix "\<turnstile>" 70)
  and transition :: "'state \<Rightarrow> ('act::bn,'state) residual \<Rightarrow> bool" (infix "\<rightarrow>" 70) +
  fixes effect_apply :: "'effect::fs \<Rightarrow> 'state \<Rightarrow> 'state" ("\<langle>_\<rangle>_" [0,101] 100)
    and L :: "('act,'effect) later"
  assumes effect_apply_eqvt: "eqvt effect_apply"  (* using [eqvt] here generates an error message *)
      and L_eqvt: "eqvt L"  \<comment> \<open>@{term L} is assumed to be equivariant.\<close>
                            (* using [eqvt] here generates an error message *)
begin

  lemma effect_apply_eqvt_aux [simp]: "p \<bullet> effect_apply = effect_apply"
  by (metis effect_apply_eqvt eqvt_def)

  lemma effect_apply_eqvt' [eqvt]: "p \<bullet> \<langle>f\<rangle>P = \<langle>p \<bullet> f\<rangle>(p \<bullet> P)"
  by simp

  lemma L_eqvt_aux [simp]: "p \<bullet> L = L"
  by (metis L_eqvt eqvt_def)

  lemma L_eqvt' [eqvt]: "p \<bullet> L (\<alpha>, P, f) = L (p \<bullet> \<alpha>, p \<bullet> P, p \<bullet> f)"
  by simp

end


subsection \<open>\texorpdfstring{$L$}{L}-bisimulations and \texorpdfstring{$F/L$}{F/L}-bisimilarity\<close>

context effect_nominal_ts
begin

  definition is_L_bisimulation:: "('effect first \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> bool" where
    "is_L_bisimulation R \<equiv>
      \<forall>F. symp (R F) \<and>
          (\<forall>P Q. R F P Q \<longrightarrow> (\<forall>f. f \<in>\<^sub>f\<^sub>s F \<longrightarrow> (\<forall>\<phi>. \<langle>f\<rangle>P \<turnstile> \<phi> \<longrightarrow> \<langle>f\<rangle>Q \<turnstile> \<phi>))) \<and>
          (\<forall>P Q. R F P Q \<longrightarrow> (\<forall>f. f \<in>\<^sub>f\<^sub>s F \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F, f) \<longrightarrow>
                  \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. \<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> R (L (\<alpha>,F,f)) P' Q'))))"

  definition FL_bisimilar :: "'effect first \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
    "FL_bisimilar F P Q \<equiv> \<exists>R. is_L_bisimulation R \<and> (R F) P Q"

  abbreviation FL_bisimilar' ("_ \<sim>\<cdot>[_] _" [51,0,51] 50) where
    "P \<sim>\<cdot>[F] Q \<equiv> FL_bisimilar F P Q"

  text \<open>@{term "FL_bisimilar"} is an equivariant relation, and (for every~@{term F}) an
    equivalence.\<close>

  lemma is_L_bisimulation_eqvt [eqvt]:
    assumes "is_L_bisimulation R" shows "is_L_bisimulation (p \<bullet> R)"
  unfolding is_L_bisimulation_def
  proof (clarify)
    fix F
    have "symp ((p \<bullet> R) F)" (is ?S)
      using assms unfolding is_L_bisimulation_def by (metis eqvt_lambda symp_eqvt)
    moreover have "\<forall>P Q. (p \<bullet> R) F P Q \<longrightarrow> (\<forall>f. f \<in>\<^sub>f\<^sub>s F \<longrightarrow> (\<forall>\<phi>. \<langle>f\<rangle>P \<turnstile> \<phi> \<longrightarrow> \<langle>f\<rangle>Q \<turnstile> \<phi>))" (is ?T)
      proof (clarify)
        fix P Q f \<phi>
        assume pR: "(p \<bullet> R) F P Q" and effect: "f \<in>\<^sub>f\<^sub>s F" and satisfies: "\<langle>f\<rangle>P \<turnstile> \<phi>"
        from pR have "R (-p \<bullet> F) (-p \<bullet> P) (-p \<bullet> Q)"
          by (simp add: eqvt_lambda permute_bool_def unpermute_def)
        moreover have "(-p \<bullet> f) \<in>\<^sub>f\<^sub>s (-p \<bullet> F)"
          using effect by simp
        moreover have "\<langle>-p \<bullet> f\<rangle>(-p \<bullet> P) \<turnstile> -p \<bullet> \<phi>"
          using satisfies by (metis effect_apply_eqvt' satisfies_eqvt)
        ultimately have "\<langle>-p \<bullet> f\<rangle>(-p \<bullet> Q) \<turnstile> -p \<bullet> \<phi>"
          using assms unfolding is_L_bisimulation_def by auto
        then show "\<langle>f\<rangle>Q \<turnstile> \<phi>"
          by (metis (full_types) effect_apply_eqvt' permute_minus_cancel(1) satisfies_eqvt)
      qed
    moreover have "\<forall>P Q. (p \<bullet> R) F P Q \<longrightarrow> (\<forall>f. f \<in>\<^sub>f\<^sub>s F \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F, f) \<longrightarrow>
                                \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. \<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> (p \<bullet> R) (L (\<alpha>, F, f)) P' Q')))" (is ?U)
      proof (clarify)
        fix P Q f \<alpha> P'
        assume pR: "(p \<bullet> R) F P Q" and effect: "f \<in>\<^sub>f\<^sub>s F" and fresh: "bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F, f)" and trans: "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
        from pR have "R (-p \<bullet> F) (-p \<bullet> P) (-p \<bullet> Q)"
          by (simp add: eqvt_lambda permute_bool_def unpermute_def)
        moreover have "(-p \<bullet> f) \<in>\<^sub>f\<^sub>s (-p \<bullet> F)"
          using effect by simp
        moreover have "bn (-p \<bullet> \<alpha>) \<sharp>* (\<langle>-p \<bullet> f\<rangle>(-p \<bullet> Q), -p \<bullet> F, -p \<bullet> f)"
          using fresh by (metis (full_types) effect_apply_eqvt' bn_eqvt fresh_star_Pair fresh_star_permute_iff)
        moreover have "\<langle>-p \<bullet> f\<rangle>(-p \<bullet> P) \<rightarrow> \<langle>-p \<bullet> \<alpha>, -p \<bullet> P'\<rangle>"
          using trans by (metis effect_apply_eqvt' transition_eqvt')
        ultimately obtain Q' where T: "\<langle>-p \<bullet> f\<rangle>(-p \<bullet> Q) \<rightarrow> \<langle>-p \<bullet> \<alpha>,Q'\<rangle>" and R: "R (L (-p \<bullet> \<alpha>, -p \<bullet> F, -p \<bullet> f)) (-p \<bullet> P') Q'"
          using assms unfolding is_L_bisimulation_def by meson
        from T have "\<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>, p \<bullet> Q'\<rangle>"
          by (metis (no_types, lifting) effect_apply_eqvt' abs_residual_pair_eqvt permute_minus_cancel(1) transition_eqvt)
        moreover from R have "(p \<bullet> R) (p \<bullet> L (-p \<bullet> \<alpha>, -p \<bullet> F, -p \<bullet> f)) (p \<bullet> -p \<bullet> P') (p \<bullet> Q')"
          by (metis permute_boolI permute_fun_def permute_minus_cancel(2))
        then have "(p \<bullet> R) (L (\<alpha>,F,f)) P' (p \<bullet> Q')"
          by (simp add: permute_self)
        ultimately show "\<exists>Q'. \<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> (p \<bullet> R) (L (\<alpha>,F,f)) P' Q'"
          by metis
      qed
    ultimately show "?S \<and> ?T \<and> ?U" by simp
  qed

  lemma FL_bisimilar_eqvt:
    assumes "P \<sim>\<cdot>[F] Q" shows "(p \<bullet> P) \<sim>\<cdot>[p \<bullet> F] (p \<bullet> Q)"
  using assms
  by (metis eqvt_apply permute_boolI is_L_bisimulation_eqvt FL_bisimilar_def)

  lemma FL_bisimilar_reflp: "reflp (FL_bisimilar F)"
  proof (rule reflpI)
    fix x
    have "is_L_bisimulation (\<lambda>_. (=))"
      unfolding is_L_bisimulation_def by (simp add: symp_def)
    then show "x \<sim>\<cdot>[F] x"
      unfolding FL_bisimilar_def by auto
  qed

  lemma FL_bisimilar_symp: "symp (FL_bisimilar F)"
  proof (rule sympI)
    fix P Q
    assume "P \<sim>\<cdot>[F] Q"
    then obtain R where *: "is_L_bisimulation R \<and> R F P Q"
      unfolding FL_bisimilar_def ..
    then have "R F Q P"
      unfolding is_L_bisimulation_def by (simp add: symp_def)
    with "*" show "Q \<sim>\<cdot>[F] P"
      unfolding FL_bisimilar_def by auto
  qed

  lemma FL_bisimilar_is_L_bisimulation: "is_L_bisimulation FL_bisimilar"
  unfolding is_L_bisimulation_def proof
    fix F
    have "symp (FL_bisimilar F)" (is ?R)
      by (fact FL_bisimilar_symp)
    moreover have "\<forall>P Q. P \<sim>\<cdot>[F] Q \<longrightarrow> (\<forall>f. f \<in>\<^sub>f\<^sub>s F \<longrightarrow> (\<forall>\<phi>. \<langle>f\<rangle>P \<turnstile> \<phi> \<longrightarrow> \<langle>f\<rangle>Q \<turnstile> \<phi>))" (is ?S)
      by (auto simp add: is_L_bisimulation_def FL_bisimilar_def)
    moreover have "\<forall>P Q. P \<sim>\<cdot>[F] Q \<longrightarrow> (\<forall>f. f \<in>\<^sub>f\<^sub>s F \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F, f) \<longrightarrow>
          \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. \<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> P' \<sim>\<cdot>[L (\<alpha>, F, f)] Q')))" (is ?T)
      by (auto simp add: is_L_bisimulation_def FL_bisimilar_def) blast
    ultimately show "?R \<and> ?S \<and> ?T"
      by metis
  qed

  lemma FL_bisimilar_simulation_step:
    assumes "P \<sim>\<cdot>[F] Q" and "f \<in>\<^sub>f\<^sub>s F" and "bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F, f)" and "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
    obtains Q' where "\<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>" and "P' \<sim>\<cdot>[L (\<alpha>,F,f)] Q'"
  using assms by (metis (poly_guards_query) FL_bisimilar_is_L_bisimulation is_L_bisimulation_def)

  lemma FL_bisimilar_transp: "transp (FL_bisimilar F)"
  proof (rule transpI)
    fix P Q R
    assume PQ: "P \<sim>\<cdot>[F] Q" and QR: "Q \<sim>\<cdot>[F] R"
    let ?FL_bisim = "\<lambda>F. (FL_bisimilar F) OO (FL_bisimilar F)"
    have "\<And>F. symp (?FL_bisim F)"
      proof (rule sympI)
        fix F P R
        assume "?FL_bisim F P R"
        then obtain Q where "P \<sim>\<cdot>[F] Q" and "Q \<sim>\<cdot>[F] R"
          by blast
        then have "R \<sim>\<cdot>[F] Q" and "Q \<sim>\<cdot>[F] P"
          by (metis FL_bisimilar_symp sympE)+
        then show "?FL_bisim F R P"
          by blast
      qed
    moreover have "\<And>F. \<forall>P Q. ?FL_bisim F P Q \<longrightarrow> (\<forall>f. f \<in>\<^sub>f\<^sub>s F \<longrightarrow> (\<forall>\<phi>. \<langle>f\<rangle>P \<turnstile> \<phi> \<longrightarrow> \<langle>f\<rangle>Q \<turnstile> \<phi>))"
      using FL_bisimilar_is_L_bisimulation is_L_bisimulation_def by auto
    moreover have "\<And>F. \<forall>P Q. ?FL_bisim F P Q \<longrightarrow>
           (\<forall>f. f \<in>\<^sub>f\<^sub>s F \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F, f) \<longrightarrow>
                     \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. \<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> ?FL_bisim (L (\<alpha>,F,f)) P' Q')))"
      proof (clarify)
        fix F P R Q f \<alpha> P'
        assume PR: "P \<sim>\<cdot>[F] R" and RQ: "R \<sim>\<cdot>[F] Q" and effect: "f \<in>\<^sub>f\<^sub>s F" and fresh: "bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F, f)" and trans: "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
        \<comment> \<open>rename~@{term "\<langle>\<alpha>,P'\<rangle>"} to avoid~@{term "(\<langle>f\<rangle>R, F)"}, without touching~@{term "(\<langle>f\<rangle>Q, F, f)"}\<close>
        obtain p where 1: "(p \<bullet> bn \<alpha>) \<sharp>* (\<langle>f\<rangle>R, F, f)" and 2: "supp (\<langle>\<alpha>,P'\<rangle>, (\<langle>f\<rangle>Q, F, f)) \<sharp>* p"
          proof (rule at_set_avoiding2[of "bn \<alpha>" "(\<langle>f\<rangle>R, F, f)" "(\<langle>\<alpha>,P'\<rangle>, (\<langle>f\<rangle>Q, F, f))", THEN exE])
            show "finite (bn \<alpha>)" by (fact bn_finite)
          next
            show "finite (supp (\<langle>f\<rangle>R, F, f))" by (fact finite_supp)
          next
            show "finite (supp (\<langle>\<alpha>,P'\<rangle>, (\<langle>f\<rangle>Q, F, f)))" by (simp add: finite_supp supp_Pair)
          next
            show "bn \<alpha> \<sharp>* (\<langle>\<alpha>,P'\<rangle>, (\<langle>f\<rangle>Q, F, f))"
              using bn_abs_residual_fresh fresh fresh_star_Pair by blast
          qed metis
        from 2 have 3: "supp \<langle>\<alpha>,P'\<rangle> \<sharp>* p" and 4: "supp (\<langle>f\<rangle>Q, F, f) \<sharp>* p"
          by (simp add: fresh_star_Un supp_Pair)+
        from 3 have "\<langle>p \<bullet> \<alpha>, p \<bullet> P'\<rangle> = \<langle>\<alpha>,P'\<rangle>"
          using supp_perm_eq by fastforce
        then obtain pR' where 5: "\<langle>f\<rangle>R \<rightarrow> \<langle>p \<bullet> \<alpha>, pR'\<rangle>" and 6: "(p \<bullet> P') \<sim>\<cdot>[L (p \<bullet> \<alpha>,F,f)] pR'"
          using PR effect trans 1 by (metis FL_bisimilar_simulation_step bn_eqvt)
        from fresh and 4 have "bn (p \<bullet> \<alpha>) \<sharp>* (\<langle>f\<rangle>Q, F, f)"
          by (metis bn_eqvt fresh_star_permute_iff supp_perm_eq)
        then obtain pQ' where 7: "\<langle>f\<rangle>Q \<rightarrow> \<langle>p \<bullet> \<alpha>, pQ'\<rangle>" and 8: "pR' \<sim>\<cdot>[L (p \<bullet> \<alpha>,F,f)] pQ'"
          using RQ effect 5 by (metis FL_bisimilar_simulation_step)
        from 4 have "supp (\<langle>f\<rangle>Q) \<sharp>* p"
          by (simp add: fresh_star_Un supp_Pair)
        with 7 have "\<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>, -p \<bullet> pQ'\<rangle>"
          by (metis permute_minus_cancel(2) supp_perm_eq transition_eqvt')
        moreover from 6 and 8 have "?FL_bisim (L (p \<bullet> \<alpha>, F, f)) (p \<bullet> P') pQ'"
          by (metis relcompp.relcompI)
        then have "?FL_bisim (-p \<bullet> L (p \<bullet> \<alpha>, F, f)) (-p \<bullet> p \<bullet> P') (-p \<bullet> pQ')"
          using FL_bisimilar_eqvt by blast
        then have "?FL_bisim (L (\<alpha>, -p \<bullet> F, -p \<bullet> f)) P' (-p \<bullet> pQ')"
          by (simp add: L_eqvt')
        then have "?FL_bisim (L (\<alpha>,F,f)) P' (-p \<bullet> pQ')"
          using 4 by (metis fresh_star_Un permute_minus_cancel(2) supp_Pair supp_perm_eq)
        ultimately show "\<exists>Q'. \<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> ?FL_bisim (L (\<alpha>,F,f)) P' Q'"
          by metis
      qed
    ultimately have "is_L_bisimulation ?FL_bisim"
      unfolding is_L_bisimulation_def by metis
    moreover have "?FL_bisim F P R"
      using PQ QR by blast
    ultimately show "P \<sim>\<cdot>[F] R"
      unfolding FL_bisimilar_def by meson
  qed

  lemma FL_bisimilar_equivp: "equivp (FL_bisimilar F)"
  by (metis FL_bisimilar_reflp FL_bisimilar_symp FL_bisimilar_transp equivp_reflp_symp_transp)

end

end
