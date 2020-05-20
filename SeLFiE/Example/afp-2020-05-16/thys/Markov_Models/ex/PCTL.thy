(* Author: Johannes Hölzl <hoelzl@in.tum.de>
   Author: Tobias Nipkow <nipkow@in.tum.de> *)
theory PCTL
imports
  "../Discrete_Time_Markov_Chain"
  "Gauss-Jordan-Elim-Fun.Gauss_Jordan_Elim_Fun"
  "HOL-Library.While_Combinator"
  "HOL-Library.Monad_Syntax"
begin

section \<open>Adapt Gauss-Jordan elimination to DTMCs\<close>

locale Finite_DTMC =
  fixes K :: "'s \<Rightarrow> 's pmf" and S :: "'s set" and \<rho> :: "'s \<Rightarrow> real" and \<iota> :: "'s \<Rightarrow> 's \<Rightarrow> real"
  assumes \<iota>_nonneg[simp]: "\<And>s t. 0 \<le> \<iota> s t" and \<rho>_nonneg[simp]: "\<And>s. 0 \<le> \<rho> s"
  assumes measurable_\<iota>: "(\<lambda>(a, b). \<iota> a b) \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M count_space UNIV)"
  assumes finite_S[simp]: "finite S" and S_not_empty: "S \<noteq> {}"
  assumes E_closed: "(\<Union>s\<in>S. set_pmf (K s)) \<subseteq> S"
begin

lemma measurable_\<iota>'[measurable (raw)]:
  "f \<in> measurable M (count_space UNIV) \<Longrightarrow> g \<in> measurable M (count_space UNIV) \<Longrightarrow>
    (\<lambda>x. \<iota> (f x) (g x)) \<in> borel_measurable M"
  using measurable_compose[OF _ measurable_\<iota>, of "\<lambda>x. (f x, g x)" M] by simp

lemma measurable_\<rho>[measurable]: "\<rho> \<in> borel_measurable (count_space UNIV)"
  by simp

sublocale R?: MC_with_rewards K \<iota> \<rho>
  by standard (auto intro: \<iota>_nonneg \<rho>_nonneg)

lemma single_l:
  fixes s and x :: real assumes "s \<in> S"
  shows "(\<Sum>s'\<in>S. (if s' = s then 1 else 0) * l s') = x \<longleftrightarrow> l s = x"
  by (simp add: assms if_distrib [of "\<lambda>x. x * a" for a] cong: if_cong)

definition "order = (SOME f. bij_betw f {..< card S} S)"

lemma
  shows bij_order[simp]: "bij_betw order {..< card S} S"
    and inj_order[simp]: "inj_on order {..<card S}"
    and image_order[simp]: "order ` {..<card S} = S"
    and order_S[simp, intro]: "\<And>i. i < card S \<Longrightarrow> order i \<in> S"
proof -
  from finite_same_card_bij[OF _ finite_S] show "bij_betw order {..< card S} S"
    unfolding order_def by (rule someI_ex) auto
  then show "inj_on order {..<card S}" "order ` {..<card S} = S"
    unfolding bij_betw_def by auto
  then show "\<And>i. i < card S \<Longrightarrow> order i \<in> S"
    by auto
qed

lemma order_Ex:
  assumes "s \<in> S" obtains i where "i < card S" "s = order i"
proof -
  from \<open>s \<in> S\<close> have "s \<in> order ` {..<card S}"
    by simp
  with that show thesis
    by (auto simp del: image_order)
qed

definition "iorder = the_inv_into {..<card S} order"

lemma bij_iorder: "bij_betw iorder S {..<card S}"
  unfolding iorder_def by (rule bij_betw_the_inv_into bij_order)+

lemma iorder_image_eq: "iorder ` S = {..<card S}"
  and inj_iorder: "inj_on iorder S"
  using bij_iorder  unfolding bij_betw_def by auto

lemma order_iorder: "\<And>s. s \<in> S \<Longrightarrow> order (iorder s) = s"
  unfolding iorder_def using bij_order
  by (intro f_the_inv_into_f) (auto simp: bij_betw_def)

definition gauss_jordan' :: "('s \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real) option" where
  "gauss_jordan' M a = do {
     let M' = (\<lambda>i j. if j = card S then a (order i) else M (order i) (order j)) ;
     sol \<leftarrow> gauss_jordan M' (card S) ;
     Some (\<lambda>i. sol (iorder i) (card S))
  }"

lemma gauss_jordan'_correct:
  assumes "gauss_jordan' M a = Some f"
  shows "\<forall>s\<in>S. (\<Sum>s'\<in>S. M s s' * f s') = a s"
proof -
  note \<open>gauss_jordan' M a = Some f\<close>
  moreover define M' where "M' = (\<lambda>i j. if j = card S then
    a (order i) else M (order i) (order j))"
  ultimately obtain sol where sol: "gauss_jordan M' (card S) = Some sol"
    and f: "f = (\<lambda>i. sol (iorder i) (card S))"
    by (auto simp: gauss_jordan'_def Let_def split: bind_split_asm)

  from gauss_jordan_correct[OF sol]
  have "\<forall>i\<in>{..<card S}. (\<Sum>j<card S. M (order i) (order j) * sol j (card S)) = a (order i)"
    unfolding solution_def M'_def by (simp add: atLeast0LessThan)
  then show ?thesis
    unfolding iorder_image_eq[symmetric] f using inj_iorder
    by (subst (asm) sum.reindex) (auto simp: order_iorder)
qed

lemma gauss_jordan'_complete:
  assumes exists: "\<forall>s\<in>S. (\<Sum>s'\<in>S. M s s' * x s') = a s"
  assumes unique: "\<And>y. \<forall>s\<in>S. (\<Sum>s'\<in>S. M s s' * y s') = a s \<Longrightarrow> \<forall>s\<in>S. y s = x s"
  shows "\<exists>y. gauss_jordan' M a = Some y"
proof -
  define M' where "M' = (\<lambda>i j. if j = card S then
    a (order i) else M (order i) (order j))"

  { fix x
    have iorder_neq_card_S: "\<And>s. s \<in> S \<Longrightarrow> iorder s \<noteq> card S"
      using iorder_image_eq by (auto simp: set_eq_iff less_le)
    have "solution2 M' (card S) (card S) x \<longleftrightarrow>
      (\<forall>s\<in>{..<card S}. (\<Sum>s'\<in>{..<card S}. M' s s' * x s') = M' s (card S))"
      unfolding solution2_def by (auto simp: atLeast0LessThan)
    also have "\<dots> \<longleftrightarrow> (\<forall>s\<in>S. (\<Sum>s'\<in>S. M s s' * x (iorder s')) = a s)"
      unfolding iorder_image_eq[symmetric] M'_def
      using inj_iorder iorder_neq_card_S
      by (simp add: sum.reindex order_iorder)
    finally have "solution2 M' (card S) (card S) x \<longleftrightarrow>
      (\<forall>s\<in>S. (\<Sum>s'\<in>S. M s s' * x (iorder s')) = a s)" . }
  note sol2_eq = this
  have "usolution M' (card S) (card S) (\<lambda>i. x (order i))"
    unfolding usolution_def
  proof safe
    from exists show "solution2 M' (card S) (card S) (\<lambda>i. x (order i))"
      by (simp add: sol2_eq order_iorder)
  next
    fix y j assume y: "solution2 M' (card S) (card S) y" and "j < card S"
    then have "\<forall>s\<in>S. (\<Sum>s'\<in>S. M s s' * y (iorder s')) = a s"
      by (simp add: sol2_eq)
    from unique[OF this]
    have "\<forall>i\<in>{..<card S}. y i = x (order i)"
      unfolding iorder_image_eq[symmetric]
      by (simp add: order_iorder)
    with \<open>j < card S\<close> show "y j = x (order j)" by simp
  qed
  from gauss_jordan_complete[OF _ this]
  show ?thesis
    by (auto simp: gauss_jordan'_def simp: M'_def)
qed

end

section \<open>pCTL model checking\<close>

subsection \<open>Syntax\<close>

datatype realrel = LessEqual | Less | Greater | GreaterEqual | Equal

datatype 's sform = "true"
                  | "Label" "'s set"
                  | "Neg" "'s sform"
                  | "And" "'s sform" "'s sform"
                  | "Prob" "realrel" "real" "'s pform"
                  | "Exp" "realrel" "real" "'s eform"
     and 's pform = "X" "'s sform"
                  | "U" "nat" "'s sform" "'s sform"
                  | "UInfinity" "'s sform" "'s sform" ("U\<^sup>\<infinity>")
     and 's eform = "Cumm" "nat" ("C\<^sup>\<le>")
                  | "State" "nat" ("I\<^sup>=")
                  | "Future" "'s sform"

primrec bound_until where
  "bound_until 0 \<phi> \<psi> = \<psi>"
| "bound_until (Suc n) \<phi> \<psi> = \<psi> or (\<phi> aand nxt (bound_until n \<phi> \<psi>))"

lemma measurable_bound_until[measurable]:
  assumes [measurable]: "Measurable.pred (stream_space M) \<phi>" "Measurable.pred (stream_space M) \<psi>"
  shows "Measurable.pred (stream_space M) (bound_until n \<phi> \<psi>)"
  by (induct n) simp_all

subsection \<open>Semantics\<close>

primrec inrealrel :: "realrel \<Rightarrow> 'a \<Rightarrow> ('a::linorder) \<Rightarrow> bool" where
"inrealrel LessEqual r q    \<longleftrightarrow> q \<le> r" |
"inrealrel Less r q         \<longleftrightarrow> q < r" |
"inrealrel Greater r q      \<longleftrightarrow> q > r" |
"inrealrel GreaterEqual r q \<longleftrightarrow> q \<ge> r" |
"inrealrel Equal r q        \<longleftrightarrow> q = r"

context Finite_DTMC
begin

abbreviation "prob s P \<equiv> measure (T s) {x\<in>space (T s). P x}"
abbreviation "E s \<equiv> set_pmf (K s)"

primrec svalid :: "'s sform \<Rightarrow> 's set"
and pvalid :: "'s pform \<Rightarrow> 's stream \<Rightarrow> bool"
and reward :: "'s eform \<Rightarrow> 's stream \<Rightarrow> ennreal" where
"svalid true           = S" |
"svalid (Label L)      = {s \<in> S. s \<in> L}" |
"svalid (Neg F)        = S - svalid F" |
"svalid (And F1 F2)    = svalid F1 \<inter> svalid F2" |
"svalid (Prob rel r F) = {s \<in> S. inrealrel rel r \<P>(\<omega> in T s. pvalid F (s ## \<omega>)) }" |
"svalid (Exp rel r F)  = {s \<in> S. inrealrel rel (ennreal r) (\<integral>\<^sup>+ \<omega>. reward F (s ## \<omega>) \<partial>T s) }" |

"pvalid (X F)        = nxt (HLD (svalid F))" |
"pvalid (U k F1 F2)  = bound_until k (HLD (svalid F1)) (HLD (svalid F2))" |
"pvalid (U\<^sup>\<infinity> F1 F2)   = HLD (svalid F1) suntil HLD (svalid F2)" |

"reward (C\<^sup>\<le> k)         = (\<lambda>\<omega>. (\<Sum>i<k. \<rho> (\<omega> !! i) + \<iota> (\<omega> !! i) (\<omega> !! (Suc i))))" |
"reward (I\<^sup>= k)         = (\<lambda>\<omega>. \<rho> (\<omega> !! k))" |
"reward (Future F)     = (\<lambda>\<omega>. if ev (HLD (svalid F)) \<omega> then reward_until (svalid F) (shd \<omega>) (stl \<omega>) else \<infinity>)"

lemma svalid_subset_S: "svalid F \<subseteq> S"
  by (induct F) auto

lemma finite_svalid[simp, intro]: "finite (svalid F)"
  using svalid_subset_S finite_S by (blast intro: finite_subset)

lemma svalid_sets[measurable]: "svalid F \<in> sets (count_space S)"
  using svalid_subset_S by auto

lemma pvalid_sets[measurable]: "Measurable.pred R.S (pvalid F)"
  by (cases F) (auto intro!: svalid_sets)

lemma reward_measurable[measurable]: "reward F \<in> borel_measurable R.S"
  by (cases F) auto

subsection \<open>Implementation of \<open>Sat\<close>\<close>

subsubsection \<open>\<open>Prob0\<close>\<close>

definition Prob0 where
  "Prob0 \<Phi> \<Psi> = S - while (\<lambda>R. \<exists>s\<in>\<Phi>. R \<inter> E s \<noteq> {} \<and> s \<notin> R) (\<lambda>R. R \<union> {s\<in>\<Phi>. R \<inter> E s \<noteq> {}}) \<Psi>"

lemma Prob0_subset_S: "Prob0 \<Phi> \<Psi> \<subseteq> S"
  unfolding Prob0_def by auto

lemma Prob0_iff_reachable:
  assumes "\<Phi> \<subseteq> S" "\<Psi> \<subseteq> S"
  shows "Prob0 \<Phi> \<Psi> = {s \<in> S. ((SIGMA x:\<Phi>. E x)\<^sup>* `` {s}) \<inter> \<Psi> = {}}" (is "_ = ?U")
  unfolding Prob0_def
proof (intro while_rule[where Q="\<lambda>R. S - R = ?U" and P="\<lambda>R. \<Psi> \<subseteq> R \<and> R \<subseteq> S - ?U"] conjI)
  show "wf {(B, A). A \<subset> B \<and> B \<subseteq> S}"
    by (rule wf_bounded_set[where ub="\<lambda>_. S" and f="\<lambda>x. x"]) auto
  show "\<Psi> \<subseteq> S - ?U"
    using assms by auto

  let ?\<Delta> = "\<lambda>R. {s\<in>\<Phi>. R \<inter> E s \<noteq> {}}"
  { fix R assume R: "\<Psi> \<subseteq> R \<and> R \<subseteq> S - ?U" and "\<exists>s\<in>\<Phi>. R \<inter> E s \<noteq> {} \<and> s \<notin> R"
    with assms show "(R \<union> ?\<Delta> R, R) \<in> {(B, A). A \<subset> B \<and> B \<subseteq> S}" "\<Psi> \<subseteq> R \<union> ?\<Delta> R"
      by auto

    { fix s s' assume s: "s \<in> \<Phi>" "s' \<in> R" "s' \<in> E s" and r: "(Sigma \<Phi> E)\<^sup>* `` {s} \<inter> \<Psi> = {}"
      with R have "(s, s') \<in> (Sigma \<Phi> E)\<^sup>*" "s' \<in> \<Phi> - \<Psi>"
        by (auto elim: converse_rtranclE)
      moreover with \<open>s' \<in> R\<close> R obtain s'' where "(s', s'') \<in> (Sigma \<Phi> E)\<^sup>*" "s'' \<in> \<Psi>"
        by auto
      ultimately have "(s, s'') \<in> (Sigma \<Phi> E)\<^sup>*" "s'' \<in> \<Psi>"
        by auto
      with r have False
        by auto }
    with \<open>\<Phi> \<subseteq> S\<close> R show "R \<union> ?\<Delta> R \<subseteq> S - ?U" by auto }

  { fix R assume R: "\<Psi> \<subseteq> R \<and> R \<subseteq> S - ?U" and dR: "\<not> (\<exists>s\<in>\<Phi>. R \<inter> E s \<noteq> {} \<and> s \<notin> R)"
    { fix s t assume s: "s \<in> S - R"
      assume s_t: "(s, t) \<in> (Sigma \<Phi> E)\<^sup>*" then have "t \<in> S - R"
      proof induct
        case (step t u) with R dR E_closed show ?case
          by auto
      qed fact
      then have "t \<notin> \<Psi>"
        using R by auto }
    with R show "S - R = ?U"
      by auto }
qed rule

lemma Prob0_iff:
  assumes "\<Phi> \<subseteq> S" "\<Psi> \<subseteq> S"
  shows "Prob0 \<Phi> \<Psi> = {s\<in>S. AE \<omega> in T s. \<not> (HLD \<Phi> suntil HLD \<Psi>) (s ## \<omega>)}" (is "_ = ?U")
  unfolding Prob0_iff_reachable[OF assms]
proof (intro Collect_cong conj_cong refl iffI)
  fix s assume s: "s \<in> S" "(Sigma \<Phi> E)\<^sup>* `` {s} \<inter> \<Psi> = {}"
  { fix \<omega> assume "(HLD \<Phi> suntil HLD \<Psi>) \<omega>" "enabled (shd \<omega>) (stl \<omega>)" "(Sigma \<Phi> E)\<^sup>* `` {shd \<omega>} \<inter> \<Psi> = {}"
    from this have False
    proof induction
      case (step \<omega>)
      moreover
      then have "(shd \<omega>, shd (stl \<omega>)) \<in> (Sigma \<Phi> E)\<^sup>*"
        by (auto simp: enabled.simps[of _ "stl \<omega>"] HLD_iff)
      then have "(Sigma \<Phi> E)\<^sup>* `` {shd (stl \<omega>)} \<subseteq> (Sigma \<Phi> E)\<^sup>* `` {shd \<omega>}"
        by auto
      ultimately show ?case
        by (auto simp add: enabled.simps[of _ "stl \<omega>"])
    qed (auto simp: HLD_iff) }
  from s this[of "s ## \<omega>" for \<omega>] show "AE \<omega> in T s. \<not> (HLD \<Phi> suntil HLD \<Psi>) (s ## \<omega>)"
    using AE_T_enabled[of s] by auto
next
  fix s assume s: "AE \<omega> in T s. \<not> (HLD \<Phi> suntil HLD \<Psi>) (s ## \<omega>)"
  { fix t assume "(s, t) \<in> (Sigma \<Phi> E)\<^sup>*" from this s have "t \<notin> \<Psi>"
    proof (induction rule: converse_rtrancl_induct)
      case (step s u) then show ?case
        by (simp add: AE_T_iff[where x=s] suntil_Stream[of _ _ s])
    qed (simp add: suntil_Stream) }
  then show "(Sigma \<Phi> E)\<^sup>* `` {s} \<inter> \<Psi> = {}"
    by auto
qed

lemma E_rtrancl_closed:
  assumes "s \<in> S" "(s, t) \<in> (SIGMA x:A. B x)\<^sup>*" "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> E x" shows "t \<in> S"
  using assms(2,3,1) E_closed by induction force+

subsubsection \<open>\<open>Prob1\<close>\<close>

definition Prob1 where
  "Prob1 Y \<Phi> \<Psi> = Prob0 (\<Phi> - \<Psi>) Y"

lemma Prob1_iff:
  assumes "\<Phi> \<subseteq> S" "\<Psi> \<subseteq> S"
  shows "Prob1 (Prob0 \<Phi> \<Psi>) \<Phi> \<Psi> = {s\<in>S. AE \<omega> in T s. (HLD \<Phi> suntil HLD \<Psi>) (s ## \<omega>)}"
    (is "Prob1 ?P0 _ _ = {s\<in>S. ?pU s}")
proof -
  note P0 = Prob0_iff_reachable[OF assms]
  have *: "\<Phi> - \<Psi> \<subseteq> S" "?P0 \<subseteq> S"
    using P0 assms by auto

  have P0_subset: "S - \<Phi> - \<Psi> \<subseteq> ?P0"
    unfolding P0 by (auto elim: converse_rtranclE)

  have "Prob1 ?P0 \<Phi> \<Psi> = {s \<in> S. (Sigma (\<Phi> - \<Psi>) E)\<^sup>* `` {s} \<inter> ?P0 = {}}"
    unfolding Prob0_iff_reachable[OF *] Prob1_def ..
  also have "\<dots> = {s\<in>S. AE \<omega> in T s. (HLD \<Phi> suntil HLD \<Psi>) (s ## \<omega>)}"
  proof (intro Collect_cong conj_cong refl iffI)
    fix s assume s: "s \<in> S" "(Sigma (\<Phi> - \<Psi>) E)\<^sup>* `` {s} \<inter> ?P0 = {}"
    then have "s \<notin> ?P0"
      by auto
    then have "s \<in> \<Phi> - \<Psi> \<or> s \<in> \<Psi>"
      using P0_subset \<open>s \<in> S\<close> by auto
    moreover
    { assume "s \<in> \<Phi> - \<Psi>"
      have "AE \<omega> in T s. ev (HLD (\<Psi> \<union> ?P0)) \<omega>"
      proof (rule AE_T_ev_HLD)
        fix t assume s_t: "(s, t) \<in> acc_on (- (\<Psi> \<union> ?P0))"
        from \<open>s \<in> S\<close> s_t have "t \<in> S"
          by (rule E_rtrancl_closed) auto

        show "\<exists>t'\<in>\<Psi> \<union> ?P0. (t, t') \<in> acc"
        proof cases
          assume "t \<in> ?P0" then show ?thesis by auto
        next
          assume "t \<notin> ?P0"
          with \<open>t\<in>S\<close> obtain s where t_s: "(t, s) \<in> (SIGMA x:\<Phi>. E x)\<^sup>*" and "s \<in> \<Psi>"
            unfolding P0 by auto
          from t_s have "(t, s) \<in> acc"
            by (rule rev_subsetD) (intro rtrancl_mono Sigma_mono, auto)
          with \<open>s \<in> \<Psi>\<close> show ?thesis by auto
        qed
      next
        have "acc_on (- (\<Psi> \<union> ?P0)) `` {s} \<subseteq> S"
          using \<open>s \<in> S\<close> by (auto intro: E_rtrancl_closed)
        then show "finite (acc_on (- (\<Psi> \<union> ?P0)) `` {s})"
          using finite_S by (auto dest: finite_subset)
      qed
      then have "AE \<omega> in T s. (HLD \<Phi> suntil HLD \<Psi>) \<omega>"
        using AE_T_enabled
      proof eventually_elim
        fix \<omega> assume "ev (HLD (\<Psi> \<union> ?P0)) \<omega>" "enabled s \<omega>"
        from this s \<open>s \<in> \<Phi> - \<Psi>\<close> show "(HLD \<Phi> suntil HLD \<Psi>) \<omega>"
        proof (induction arbitrary: s)
          case (base \<omega>) then show ?case
            by (auto simp: HLD_iff enabled.simps[of s] intro: suntil.intros)
        next
          case (step \<omega>)
          then have "(s, shd \<omega>) \<in> (Sigma (\<Phi> - \<Psi>) E)"
            by (auto simp: enabled.simps[of s])
          then have *: "(Sigma (\<Phi> - \<Psi>) E)\<^sup>* `` {shd \<omega>} \<inter> ?P0 = {}"
            using step.prems by (auto intro: converse_rtrancl_into_rtrancl)
          then have "shd \<omega> \<in> \<Phi> - \<Psi> \<or> shd \<omega> \<in> \<Psi>" "shd \<omega> \<in> S"
            using P0_subset step.prems(1,2) E_closed by (auto simp add: enabled.simps[of s])
          then show ?case
            using step.prems(1) step.IH[OF _ _ *] \<open>shd \<omega> \<in> S\<close>
            by (auto simp add: suntil.simps[of _ _ \<omega>] HLD_iff[abs_def] enabled.simps[of s \<omega>])
        qed
      qed }
    ultimately show "AE \<omega> in T s. (HLD \<Phi> suntil HLD \<Psi>) (s ## \<omega>)"
      by (cases "s \<in> \<Phi> - \<Psi>") (auto simp add: suntil_Stream)
  next
    fix s assume s: "s \<in> S" "AE \<omega> in T s. (HLD \<Phi> suntil HLD \<Psi>) (s ## \<omega>)"
    { fix t assume "(s, t) \<in> (SIGMA s:\<Phi>-\<Psi>. E s)\<^sup>*"
      from this \<open>s \<in> S\<close> have "(AE \<omega> in T t. (HLD \<Phi> suntil HLD \<Psi>) (t ## \<omega>)) \<and> t \<in> S"
      proof induction
        case (step t u) with E_closed show ?case
          by (auto simp add: AE_T_iff[of _ t] suntil_Stream)
      qed (insert s, auto)
      then have "t \<notin> ?P0"
        unfolding Prob0_iff[OF assms] by (auto dest: T.AE_contr) }
    then show "(Sigma (\<Phi> - \<Psi>) E)\<^sup>* `` {s} \<inter> Prob0 \<Phi> \<Psi> = {}"
      by auto
  qed
  finally show ?thesis .
qed

subsubsection \<open>\<open>ProbU\<close>,  \<open>ExpCumm\<close>, and \<open>ExpState\<close>\<close>

abbreviation "\<tau> s t \<equiv> pmf (K s) t"

fun ProbU :: "'s \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> real" where
"ProbU q 0 S1 S2       = (if q \<in> S2 then 1 else 0)" |
"ProbU q (Suc k) S1 S2 =
  (if q \<in> S1 - S2 then (\<Sum>q'\<in>S. \<tau> q q' * ProbU q' k S1 S2)
                  else if q \<in> S2 then 1 else 0)"

fun ExpCumm :: "'s \<Rightarrow> nat \<Rightarrow> ennreal" where
"ExpCumm s 0       = 0" |
"ExpCumm s (Suc k) = \<rho> s + (\<Sum>s'\<in>S. \<tau> s s' * (\<iota> s s' + ExpCumm s' k))"

fun ExpState :: "'s \<Rightarrow> nat \<Rightarrow> ennreal" where
"ExpState s 0       = \<rho> s" |
"ExpState s (Suc k) = (\<Sum>s'\<in>S. \<tau> s s' * ExpState s' k)"

subsubsection \<open>\<open>LES\<close>\<close>

definition LES :: "'s set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> real" where
  "LES F r c =
       (if r \<in> F then (if c = r then 1 else 0)
                 else (if c = r then \<tau> r c - 1 else \<tau> r c ))"


subsubsection \<open>\<open>ProbUinfty\<close>, compute unbounded until\<close>

definition ProbUinfty :: "'s set \<Rightarrow> 's set \<Rightarrow> ('s \<Rightarrow> real) option" where
  "ProbUinfty S1 S2 = gauss_jordan' (LES (Prob0 S1 S2 \<union> S2))
                                    (\<lambda>i. if i \<in> S2 then 1 else 0)"

subsubsection \<open>\<open>ExpFuture\<close>, compute unbounded reward\<close>

definition ExpFuture :: "'s set \<Rightarrow> ('s \<Rightarrow> ennreal) option" where
  "ExpFuture F = do {
      let N = Prob0 S F ;
      let Y = Prob1 N S F ;
      sol \<leftarrow> gauss_jordan' (LES (S - Y \<union> F))
        (\<lambda>i. if i \<in> Y \<and> i \<notin> F then - \<rho> i - (\<Sum>s'\<in>S. \<tau> i s' * \<iota> i s') else 0) ;
      Some (\<lambda>s. if s \<in> Y then ennreal (sol s) else \<infinity>)
    }"

subsubsection \<open>\<open>Sat\<close>\<close>

fun Sat :: "'s sform \<Rightarrow> 's set option" where
"Sat true                   = Some S" |
"Sat (Label L)              = Some {s \<in> S. s \<in> L}" |
"Sat (Neg F)                = do { F \<leftarrow> Sat F ; Some (S - F) }" |
"Sat (And F1 F2)            = do { F1 \<leftarrow> Sat F1 ; F2 \<leftarrow> Sat F2 ; Some (F1 \<inter> F2) }" |

"Sat (Prob rel r (X F))        = do { F \<leftarrow> Sat F ; Some {q \<in> S. inrealrel rel r (\<Sum>q'\<in>F. \<tau> q q')} }" |
"Sat (Prob rel r (U k F1 F2))  = do { F1 \<leftarrow> Sat F1 ; F2 \<leftarrow> Sat F2 ; Some {q \<in> S. inrealrel rel r (ProbU q k F1 F2) } }" |
"Sat (Prob rel r (U\<^sup>\<infinity> F1 F2))   = do { F1 \<leftarrow> Sat F1 ; F2 \<leftarrow> Sat F2 ; P \<leftarrow> ProbUinfty F1 F2 ; Some {q \<in> S. inrealrel rel r (P q) } }" |

"Sat (Exp rel r (Cumm k))      = Some {s \<in> S. inrealrel rel r (ExpCumm s k) }" |
"Sat (Exp rel r (State k))     = Some {s \<in> S. inrealrel rel r (ExpState s k) }" |
"Sat (Exp rel r (Future F))    = do { F \<leftarrow> Sat F ; E \<leftarrow> ExpFuture F ; Some {q \<in> S. inrealrel rel (ennreal r) (E q) } }"


lemma prob_sum:
  "s \<in> S \<Longrightarrow> Measurable.pred R.S P \<Longrightarrow> \<P>(\<omega> in T s. P \<omega>) = (\<Sum>t\<in>S. \<tau> s t * \<P>(\<omega> in T t. P (t ## \<omega>)))"
  unfolding prob_T using E_closed by (subst integral_measure_pmf[OF finite_S]) (auto simp: mult.commute)

lemma nn_integral_eq_sum:
  "s \<in> S \<Longrightarrow> f \<in> borel_measurable R.S \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>T s) = (\<Sum>t\<in>S. \<tau> s t * (\<integral>\<^sup>+x. f (t ## x) \<partial>T t))"
  unfolding nn_integral_T using E_closed
  by (subst nn_integral_measure_pmf_support[OF finite_S])
     (auto simp: mult.commute)

lemma T_space[simp]: "measure (T s) (space R.S) = 1"
  using T.prob_space by simp

lemma emeasure_T_space[simp]: "emeasure (T s) (space R.S) = 1"
  using T.emeasure_space_1 by simp

lemma \<tau>_distr[simp]: "s \<in> S \<Longrightarrow> (\<Sum>t\<in>S. \<tau> s t) = 1"
  using prob_sum[of s "\<lambda>_. True"] by simp

lemma ProbU:
  "q \<in> S \<Longrightarrow> ProbU q k (svalid F1) (svalid F2) = \<P>(\<omega> in T q. pvalid (U k F1 F2) (q ## \<omega>))"
proof (induct k arbitrary: q)
  case 0 with T.prob_space show ?case by simp
next
  case (Suc k)

  have "\<P>(\<omega> in T q. pvalid (U (Suc k) F1 F2) (q ## \<omega>)) =
    (if q \<in> svalid F2 then 1 else if q \<in> svalid F1 then
      \<Sum>t\<in>S. \<tau> q t * \<P>(\<omega> in T t. pvalid (U k F1 F2) (t ## \<omega>)) else 0)"
    using \<open>q \<in> S\<close> by (subst prob_sum) simp_all
  also have "\<dots> = ProbU q (Suc k) (svalid F1) (svalid F2)"
    using Suc by simp
  finally show ?case ..
qed

lemma Prob0_imp_not_Psi:
  assumes "\<Phi> \<subseteq> S" "\<Psi> \<subseteq> S" "s \<in> Prob0 \<Phi> \<Psi>" shows "s \<notin> \<Psi>"
proof -
  have "s \<in> S" using \<open>s \<in> Prob0 \<Phi> \<Psi>\<close> Prob0_subset_S by auto
  with assms show ?thesis by (auto simp add: Prob0_iff suntil_Stream)
qed

lemma Psi_imp_not_Prob0:
  assumes "\<Phi> \<subseteq> S" "\<Psi> \<subseteq> S" shows "s \<in> \<Psi> \<Longrightarrow> s \<notin> Prob0 \<Phi> \<Psi>"
  using Prob0_imp_not_Psi[OF assms] by metis

subsubsection \<open>Finite expected reward\<close>

abbreviation "s0 \<equiv> SOME s. s \<in> S"

lemma s0_in_S: "s0 \<in> S"
  using S_not_empty by (auto intro!: someI_ex[of "\<lambda>x. x \<in> S"])

lemma nn_integral_reward_finite:
  assumes "s \<in> S"
  assumes until: "AE \<omega> in T s. (HLD S suntil HLD (svalid F)) (s ## \<omega>)"
  shows "(\<integral>\<^sup>+ \<omega>. reward (Future F) (s ## \<omega>) \<partial>T s) \<noteq> \<infinity>"
proof -
  have "(\<integral>\<^sup>+ \<omega>. reward (Future F) (s ## \<omega>) \<partial>T s) = (\<integral>\<^sup>+ \<omega>. reward_until (svalid F) s \<omega> \<partial>T s)"
    using until by (auto intro!: nn_integral_cong_AE ev_suntil)
  also have "\<dots> \<noteq> \<infinity>"
  proof cases
    assume "s \<notin> svalid F"
    show ?thesis
    proof (rule nn_integral_reward_until_finite)
      have "acc `` {s} \<subseteq> S"
        using E_rtrancl_closed[of s _ _ E] \<open>s \<in> S\<close> by auto
      then show "finite (acc `` {s})"
        using finite_S by (auto dest: finite_subset)
      show "AE \<omega> in T s. (ev (HLD (svalid F))) \<omega>"
        using until by (auto simp add: suntil_Stream \<open>s \<notin> svalid F\<close> intro: ev_suntil)
    qed auto
  qed simp
  finally show ?thesis .
qed

lemma unique:
  assumes in_S: "\<Phi> \<subseteq> S" "\<Psi> \<subseteq> S" "N \<subseteq> S" "Prob0 \<Phi> \<Psi> \<subseteq> N" "\<Psi> \<subseteq> N"
  assumes l1: "\<And>s. s \<in> S \<Longrightarrow> s \<notin> N \<Longrightarrow> l1 s - c s = (\<Sum>s'\<in>S. \<tau> s s' * l1 s')"
  assumes l2: "\<And>s. s \<in> S \<Longrightarrow> s \<notin> N \<Longrightarrow> l2 s - c s = (\<Sum>s'\<in>S. \<tau> s s' * l2 s')"
  assumes eq: "\<And>s. s \<in> N \<Longrightarrow> l1 s = l2 s"
  shows "\<forall>s\<in>S. l1 s = l2 s"
proof
  fix s assume "s \<in> S"
  show "l1 s = l2 s"
  proof cases
    assume "s \<in> N" then show ?thesis
      by (rule eq)
  next
    assume "s \<notin> N"
    show ?thesis
    proof (rule unique_les[of _ "S - N" K N])
      show "finite ((\<lambda>x. l1 x - l2 x) ` (S - N \<union> N))" "(\<Union>x\<in>S - N. E x) \<subseteq> S - N \<union> N"
        using E_closed finite_S \<open>N \<subseteq> S\<close> by (auto dest: finite_subset)
      show "\<And>s. s \<in> N \<Longrightarrow> l1 s = l2 s" by fact
      { fix s assume "s \<in> S - N" with E_closed finite_S show "integrable (K s) l1" "integrable (K s) l2"
          by (auto intro!: integrable_measure_pmf_finite dest: finite_subset)
        obtain t where "(t \<in> \<Psi> \<and> (s, t) \<in> (Sigma \<Phi> E)\<^sup>*) \<or> s \<in> N"
          using \<open>s \<in> S - N\<close> in_S(4) unfolding Prob0_iff_reachable[OF in_S(1,2)] by auto
        moreover have "(Sigma \<Phi> E)\<^sup>* \<subseteq> acc"
          by (intro rtrancl_mono Sigma_mono) auto
        ultimately show "\<exists>t\<in>N. (s, t) \<in> acc"
          using \<open>\<Psi> \<subseteq> N\<close> by auto
        show "l1 s = integral\<^sup>L (K s) l1 + c s"
          using E_closed l1 \<open>s \<in> S - N\<close>
          by (subst integral_measure_pmf[OF finite_S]) (auto simp: subset_eq field_simps)
        show "l2 s = integral\<^sup>L (K s) l2 + c s"
          using E_closed l2 \<open>s \<in> S - N\<close>
          by (subst integral_measure_pmf[OF finite_S]) (auto simp: subset_eq field_simps) }
    qed (insert \<open>s \<notin>  N\<close> \<open>s \<in> S\<close>, auto)
  qed
qed

lemma uniqueness_of_ProbU:
  assumes sol:
    "\<forall>s\<in>S. (\<Sum>s'\<in>S. LES (Prob0 (svalid F1) (svalid F2) \<union> svalid F2) s s' * l s') =
      (if s \<in> svalid F2 then 1 else 0)"
  shows "\<forall>s\<in>S. l s = \<P>(\<omega> in T s. pvalid (U\<^sup>\<infinity> F1 F2) (s ## \<omega>))"
proof (rule unique)
  show "svalid F1 \<subseteq> S" "svalid F2 \<subseteq> S"
    "Prob0 (svalid F1) (svalid F2) \<subseteq> Prob0 (svalid F1) (svalid F2) \<union> svalid F2"
    "svalid F2 \<subseteq> Prob0 (svalid F1) (svalid F2) \<union> svalid F2"
    "Prob0 (svalid F1) (svalid F2) \<union> svalid F2 \<subseteq> S"
    using svalid_subset_S by (auto simp: Prob0_def)
next
  fix s assume s: "s \<in> S" "s \<notin> Prob0 (svalid F1) (svalid F2) \<union> svalid F2"
  have "(\<Sum>s'\<in>S. (if s' = s then \<tau> s s' - 1 else \<tau> s s') * l s') =
    (\<Sum>s'\<in>S. \<tau> s s' * l s' - (if s' = s then 1 else 0) * l s')"
    by (auto intro!: sum.cong simp: field_simps)
  also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * l s') - l s"
    using \<open>s \<in> S\<close> by (simp add: sum_subtractf single_l)
  finally show "l s - 0 = (\<Sum>s'\<in>S. \<tau> s s' * l s')"
    using sol[THEN bspec, of s] s by (simp add: LES_def)
next
  fix s assume s: "s \<in> S" "s \<notin> Prob0 (svalid F1) (svalid F2) \<union> svalid F2"
  then show "\<P>(\<omega> in T s. pvalid (U\<^sup>\<infinity> F1 F2) (s ## \<omega>)) - 0 =
    (\<Sum>t\<in>S. \<tau> s t * \<P>(\<omega> in T t. pvalid (U\<^sup>\<infinity> F1 F2) (t ## \<omega>)))"
    unfolding Prob0_iff[OF svalid_subset_S svalid_subset_S]
    by (subst prob_sum) (auto simp add: suntil_Stream)
next
  fix s assume "s \<in> Prob0 (svalid F1) (svalid F2) \<union> svalid F2"
  then show "l s = \<P>(\<omega> in T s. pvalid (U\<^sup>\<infinity> F1 F2) (s ## \<omega>))"
  proof
    assume P0: "s \<in> Prob0 (svalid F1) (svalid F2)"
    then have "s \<in> S" "AE \<omega> in T s. \<not> (HLD (svalid F1) suntil HLD (svalid F2)) (s ## \<omega>)"
      unfolding Prob0_iff[OF svalid_subset_S svalid_subset_S] by auto
    then have "\<P>(\<omega> in T s. pvalid (U\<^sup>\<infinity> F1 F2) (s ## \<omega>)) = 0"
      by (intro T.prob_eq_0_AE) simp
    moreover have "l s = 0"
      using \<open>s \<in> S\<close> P0 sol[THEN bspec, of s] Prob0_subset_S
        Prob0_imp_not_Psi[OF svalid_subset_S svalid_subset_S P0]
      by (auto simp: LES_def single_l split: if_split_asm)
    ultimately show "l s = \<P>(\<omega> in T s. pvalid (U\<^sup>\<infinity> F1 F2) (s ## \<omega>))" by simp
  next
    assume s: "s \<in> svalid F2"
    moreover with svalid_subset_S have "s \<in> S" by auto
    moreover note Psi_imp_not_Prob0[OF svalid_subset_S svalid_subset_S s]
    ultimately have "l s = 1"
      using sol[THEN bspec, of s]
      by (auto simp: LES_def single_l dest: Psi_imp_not_Prob0[OF svalid_subset_S svalid_subset_S])
    then show "l s = \<P>(\<omega> in T s. pvalid (U\<^sup>\<infinity> F1 F2) (s ## \<omega>))"
      using s by (simp add: suntil_Stream)
  qed
qed

lemma infinite_reward:
  fixes s F
  defines "N \<equiv> Prob0 S (svalid F)" (is "_ \<equiv> Prob0 S ?F")
  defines "Y \<equiv> Prob1 N S (svalid F)"
  assumes s: "s \<in> S" "s \<notin> Y"
  shows "(\<integral>\<^sup>+\<omega>. reward (Future F) (s ## \<omega>) \<partial>T s) = \<infinity>"
proof -
  { assume "(AE \<omega> in T s. ev (HLD ?F) \<omega>)"
    with AE_T_enabled have "(AE \<omega> in T s. (HLD S suntil HLD ?F) \<omega>)"
    proof eventually_elim
      fix \<omega> assume "ev (HLD ?F) \<omega>" "enabled s \<omega>"
      from this \<open>s \<in> S\<close> show "(HLD S suntil HLD ?F) \<omega>"
      proof (induction arbitrary: s)
        case (step \<omega>) show ?case
          using E_closed step.IH[of "shd \<omega>"] step.prems
          by (auto simp: subset_eq enabled.simps[of s] suntil.simps[of _ _ \<omega>] HLD_iff)
       qed (auto intro: suntil.intros)
    qed }
  moreover have "\<not> (AE \<omega> in T s. (HLD S suntil HLD ?F) (s ## \<omega>))"
    using s svalid_subset_S unfolding N_def Y_def by (simp add: Prob1_iff)
  ultimately have *: "\<not> (AE \<omega> in T s. ev (HLD ?F) (s ## \<omega>))"
    using \<open>s \<in> S\<close> by (cases "s \<in> ?F") (auto simp add: suntil_Stream ev_Stream)

  show ?thesis
  proof (rule ccontr)
    assume "\<not> ?thesis"
    from nn_integral_PInf_AE[OF _ this] \<open>s\<in>S\<close>
    have "AE \<omega> in T s. ev (HLD ?F) (s ## \<omega>)"
      by (simp split: if_split_asm)
    with * show False ..
  qed
qed

subsubsection \<open>The expected reward implies a unique LES\<close>

lemma existence_of_ExpFuture:
  fixes s F
  assumes N_def: "N \<equiv> Prob0 S (svalid F)" (is "_ \<equiv> Prob0 S ?F")
  assumes Y_def: "Y \<equiv> Prob1 N S (svalid F)"
  assumes s: "s \<in> S" "s \<notin> S - (Y - ?F)"
  shows "enn2real (\<integral>\<^sup>+\<omega>. reward (Future F) (s ## \<omega>) \<partial>T s) - (\<rho> s + (\<Sum>s'\<in>S. \<tau> s s' * \<iota> s s')) =
    (\<Sum>s'\<in>S. \<tau> s s' * enn2real (\<integral>\<^sup>+\<omega>. reward (Future F) (s' ## \<omega>) \<partial>T s'))"
proof -
  let ?R = "reward (Future F)"

  from s have "s \<in> Prob1 (Prob0 S ?F) S ?F"
    unfolding Y_def N_def by auto
  then have AE_until: "AE \<omega> in T s. (HLD S suntil HLD (svalid F)) (s ## \<omega>)"
    using Prob1_iff[of S ?F] svalid_subset_S by auto

  from s have "s \<notin> ?F" by auto

  let ?E = "\<lambda>s'. \<integral>\<^sup>+ \<omega>. reward (Future F) (s' ## \<omega>) \<partial>T s'"
  have *: "(\<Sum>s'\<in>S. \<tau> s s' * ?E s') = (\<Sum>s'\<in>S. ennreal (\<tau> s s' * enn2real (?E s')))"
  proof (rule sum.cong)
    fix s' assume "s' \<in> S"
    show "\<tau> s s' * ?E s' = ennreal (\<tau> s s' * enn2real (?E s'))"
    proof cases
      assume "\<tau> s s' \<noteq> 0"
      with \<open>s \<in> S\<close> \<open>s' \<in> S\<close> have "s' \<in> E s" by (simp add: set_pmf_iff)
      from \<open>s \<notin> ?F\<close> AE_until have "AE \<omega> in T s. (HLD S suntil HLD ?F) (s ## \<omega>)"
        using svalid_subset_S \<open>s \<in> S\<close> by simp
      with nn_integral_reward_finite[OF \<open>s' \<in> S\<close>, of F] \<open>s \<in> S\<close> \<open>s' \<in> E s\<close> \<open>s \<notin> ?F\<close>
      have "?E s' \<noteq> \<infinity>"
        by (simp add: AE_T_iff[of _ s] AE_measure_pmf_iff suntil_Stream
                 del: reward.simps)
      then show ?thesis by (cases "?E s'") (auto simp: ennreal_mult)
    qed simp
  qed simp

  have "AE \<omega> in T s. ?R (s ## \<omega>) = \<rho> s + \<iota> s (shd \<omega>) + ?R \<omega>"
    using \<open>s \<notin> svalid F\<close> by (auto simp: ev_Stream )
  then have "(\<integral>\<^sup>+\<omega>. ?R (s ## \<omega>) \<partial>T s) = (\<integral>\<^sup>+\<omega>. (\<rho> s + \<iota> s (shd \<omega>)) + ?R \<omega> \<partial>T s)"
    by (rule nn_integral_cong_AE)
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. \<rho> s + \<iota> s (shd \<omega>) \<partial>T s) +
    (\<integral>\<^sup>+\<omega>. ?R \<omega> \<partial>T s)"
    using \<open>s \<in> S\<close>
    by (subst nn_integral_add)
       (auto simp add: space_PiM PiE_iff simp del: reward.simps)
  also have "\<dots> = ennreal (\<rho> s + (\<Sum>s'\<in>S. \<tau> s s' * \<iota> s s')) + (\<integral>\<^sup>+\<omega>. ?R \<omega> \<partial>T s)"
    using \<open>s \<in> S\<close>
    by (subst nn_integral_eq_sum)
       (auto simp: field_simps sum.distrib sum_distrib_left[symmetric] ennreal_mult[symmetric] sum_nonneg)
  finally show ?thesis
    apply (simp del: reward.simps)
    apply (subst nn_integral_eq_sum[OF \<open>s \<in> S\<close> reward_measurable])
    apply (simp del: reward.simps ennreal_plus add: * ennreal_plus[symmetric] sum_nonneg)
    done
qed

lemma uniqueness_of_ExpFuture:
  fixes F
  assumes N_def: "N \<equiv> Prob0 S (svalid F)" (is "_ \<equiv> Prob0 S ?F")
  assumes Y_def: "Y \<equiv> Prob1 N S (svalid F)"
  assumes const_def: "const \<equiv> \<lambda>s. if s \<in> Y \<and> s \<notin> svalid F then - \<rho> s - (\<Sum>s'\<in>S. \<tau> s s' * \<iota> s s') else 0"
  assumes sol: "\<And>s. s\<in>S \<Longrightarrow> (\<Sum>s'\<in>S. LES (S - Y \<union> ?F) s s' * l s') = const s"
  shows "\<forall>s\<in>S. l s = enn2real (\<integral>\<^sup>+\<omega>. reward (Future F) (s ## \<omega>) \<partial>T s)"
    (is "\<forall>s\<in>S. l s = enn2real (\<integral>\<^sup>+\<omega>. ?R (s ## \<omega>) \<partial>T s)")
proof (rule unique)
  show "S \<subseteq> S" "?F \<subseteq> S" using svalid_subset_S by auto
  show "S - (Y - ?F) \<subseteq> S" "Prob0 S ?F \<subseteq> S - (Y - ?F)" "?F \<subseteq> S - (Y - ?F)"
    using svalid_subset_S
    by (auto simp add: Y_def N_def Prob1_iff)
       (auto simp add: Prob0_iff dest!: T.AE_contr)
next
  fix s assume "s \<in> S" "s \<notin> S - (Y - ?F)"
  then show "enn2real (\<integral>\<^sup>+\<omega>. ?R (s ## \<omega>) \<partial>T s) - (\<rho> s + (\<Sum>s'\<in>S. \<tau> s s' * \<iota> s s')) =
    (\<Sum>s'\<in>S. \<tau> s s' * enn2real (\<integral>\<^sup>+\<omega>. ?R (s' ## \<omega>) \<partial>T s'))"
    by (rule existence_of_ExpFuture[OF N_def Y_def])
next
  fix s assume "s \<in> S" "s \<notin> S - (Y - ?F)"
  then have "s \<in> Y" "s \<notin> ?F" by auto
  have "(\<Sum>s'\<in>S. (if s' = s then \<tau> s s' - 1 else \<tau> s s') * l s') =
    (\<Sum>s'\<in>S. \<tau> s s' * l s' - (if s' = s then 1 else 0) * l s')"
    by (auto intro!: sum.cong simp: field_simps)
  also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * l s') - l s"
    using \<open>s \<in> S\<close> by (simp add: sum_subtractf single_l)
  finally have "l s = (\<Sum>s'\<in>S. \<tau> s s' * l s') - (\<Sum>s'\<in>S. (if s' = s then \<tau> s s' - 1 else \<tau> s s') * l s')"
    by (simp add: field_simps)
  then show "l s - (\<rho> s + (\<Sum>s'\<in>S. \<tau> s s' * \<iota> s s')) = (\<Sum>s'\<in>S. \<tau> s s' * l s')"
    using sol[OF \<open>s \<in> S\<close>] \<open>s \<in> Y\<close> \<open>s \<notin> ?F\<close> by (simp add: const_def LES_def)
next
  fix s assume s: "s \<in> S - (Y - ?F)"
  with sol[of s] have "l s = 0"
    by (cases "s \<in> ?F") (simp_all add: const_def LES_def single_l)
  also have "0 = enn2real (\<integral>\<^sup>+\<omega>. reward (Future F) (s ## \<omega>) \<partial>T s)"
  proof cases
    assume "s \<in> ?F" then show ?thesis
      by (simp add: HLD_iff ev_Stream)
  next
    assume "s \<notin> ?F"
    with s have "s \<in> S - Y" by auto
    with infinite_reward[of s F] show ?thesis
      by (simp add: Y_def N_def del: reward.simps)
  qed
  finally show "l s = enn2real (\<integral>\<^sup>+\<omega>. ?R (s ## \<omega>) \<partial>T s)" .
qed

subsection \<open>Soundness of @{const Sat}\<close>

theorem Sat_sound:
  "Sat F \<noteq> None \<Longrightarrow> Sat F = Some (svalid F)"
proof (induct F rule: Sat.induct)
  case (5 rel r F)
  { fix q assume "q \<in> S"
    with svalid_subset_S have "sum (\<tau> q) (svalid F) = \<P>(\<omega> in T q. HLD (svalid F) \<omega>)"
      by (subst prob_sum[OF \<open>q\<in>S\<close>]) (auto intro!: sum.mono_neutral_cong_left) }
  with 5 show ?case
    by (auto split: bind_split_asm)

next
  case (6 rel r k F1 F2)
  then show ?case
    by (simp add: ProbU cong: conj_cong split: bind_split_asm)

next
  case (7 rel r F1 F2)
  moreover
  define constants :: "'s \<Rightarrow> real" where "constants = (\<lambda>s. if s \<in> (svalid F2) then 1 else 0)"
  moreover define distr where "distr = LES (Prob0 (svalid F1) (svalid F2) \<union> svalid F2)"
  ultimately obtain l where eq: "Sat F1 = Some (svalid F1)" "Sat F2 = Some (svalid F2)"
    and l: "gauss_jordan' distr constants = Some l"
    by atomize_elim (simp add: ProbUinfty_def split: bind_split_asm)

  from l have P: "ProbUinfty (svalid F1) (svalid F2) = Some l"
    unfolding ProbUinfty_def constants_def distr_def by simp

  have "\<forall>s\<in>S. l s = \<P>(\<omega> in T s. pvalid (U\<^sup>\<infinity> F1 F2) (s ## \<omega>))"
  proof (rule uniqueness_of_ProbU)
    show "\<forall>s\<in>S. (\<Sum>s'\<in>S. LES (Prob0 (svalid F1) (svalid F2) \<union> svalid F2) s s' * l s') =
                   (if s \<in> svalid F2 then 1 else 0)"
      using gauss_jordan'_correct[OF l]
      unfolding distr_def constants_def by simp
  qed
  then show ?case
    by (auto simp add: eq P)
next
  case (8 rel r k)
  { fix s assume "s \<in> S"
    then have "ExpCumm s k = (\<integral>\<^sup>+ x. ennreal (\<Sum>i<k. \<rho> ((s ## x) !! i) + \<iota> ((s ## x) !! i) (x !! i)) \<partial>T s)"
    proof (induct k arbitrary: s)
      case 0 then show ?case by simp
    next
      case (Suc k)
      have "(\<integral>\<^sup>+\<omega>. ennreal (\<Sum>i<Suc k. \<rho> ((s ## \<omega>) !! i) + \<iota> ((s ## \<omega>) !! i) (\<omega> !! i)) \<partial>T s)
        = (\<integral>\<^sup>+\<omega>. ennreal (\<rho> s + \<iota> s (\<omega> !! 0)) + ennreal (\<Sum>i<k. \<rho> (\<omega> !! i) + \<iota> (\<omega> !! i) (\<omega> !! (Suc i))) \<partial>T s)"
        by (auto intro!: nn_integral_cong
                 simp del: ennreal_plus
                 simp: ennreal_plus[symmetric] sum_nonneg sum.reindex lessThan_Suc_eq_insert_0 zero_notin_Suc_image)
      also have "\<dots> = (\<integral>\<^sup>+\<omega>. \<rho> s + \<iota> s (\<omega> !! 0) \<partial>T s) +
          (\<integral>\<^sup>+\<omega>. (\<Sum>i<k. \<rho> (\<omega> !! i) + \<iota> (\<omega> !! i) (\<omega> !! (Suc i))) \<partial>T s)"
        using \<open>s \<in> S\<close>
        by (intro nn_integral_add AE_I2) (auto simp: sum_nonneg)
      also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * (\<rho> s + \<iota> s s')) +
        (\<integral>\<^sup>+\<omega>. (\<Sum>i<k. \<rho> (\<omega> !! i) + \<iota> (\<omega> !! i) (\<omega> !! (Suc i))) \<partial>T s)"
        using \<open>s \<in> S\<close> by (subst nn_integral_eq_sum)
          (auto simp del: ennreal_plus simp: ennreal_plus[symmetric] ennreal_mult[symmetric] sum_nonneg)
      also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * (\<rho> s + \<iota> s s')) +
        (\<Sum>s'\<in>S. \<tau> s s' * ExpCumm s' k)"
        using \<open>s \<in> S\<close> by (subst nn_integral_eq_sum) (auto simp: Suc)
      also have "\<dots> = ExpCumm s (Suc k)"
        using \<open>s \<in> S\<close>
        by (simp add: field_simps sum.distrib sum_distrib_left[symmetric] ennreal_mult[symmetric]
            ennreal_plus[symmetric] sum_nonneg del: ennreal_plus)
      finally show ?case by simp
    qed }
  then show ?case by auto

next
  case (9 rel r k)
  { fix s assume "s \<in> S"
    then have "ExpState s k = (\<integral>\<^sup>+ x. ennreal (\<rho> ((s ## x) !! k)) \<partial>T s)"
    proof (induct k arbitrary: s)
      case (Suc k) then show ?case by (simp add: nn_integral_eq_sum[of s])
    qed simp }
  then show ?case by auto

next
  case (10 rel r F)
  moreover
  let ?F = "svalid F"
  define N where "N \<equiv> Prob0 S ?F"
  moreover define Y where "Y \<equiv> Prob1 N S ?F"
  moreover define const where "const \<equiv> (\<lambda>s. if s \<in> Y \<and> s \<notin> ?F then - \<rho> s - (\<Sum>s'\<in>S. \<tau> s s' * \<iota> s s') else 0)"
  ultimately obtain l
    where l: "gauss_jordan' (LES (S - Y \<union> ?F)) const = Some l"
    and F: "Sat F = Some ?F"
    by (auto simp: ExpFuture_def Let_def split: bind_split_asm)

  from l have EF: "ExpFuture ?F =
    Some (\<lambda>s. if s \<in> Y then ennreal (l s) else \<infinity>)"
    unfolding ExpFuture_def N_def Y_def const_def by auto

  let ?R = "reward (Future F)"
  have l_eq: "\<forall>s\<in>S. l s = enn2real (\<integral>\<^sup>+\<omega>. ?R (s ## \<omega>) \<partial>T s)"
  proof (rule uniqueness_of_ExpFuture[OF N_def Y_def const_def])
    fix s assume "s \<in> S"
    show "\<And>s. s\<in>S \<Longrightarrow> (\<Sum>s'\<in>S. LES (S - Y \<union> ?F) s s' * l s') = const s"
      using gauss_jordan'_correct[OF l] by auto
  qed
  { fix s assume [simp]: "s \<in> S" "s \<in> Y"
    then have "s \<in> Prob1 (Prob0 S ?F) S ?F"
      unfolding Y_def N_def by auto
    then have "AE \<omega> in T s. (HLD S suntil HLD ?F) (s ## \<omega>)"
      using svalid_subset_S by (auto simp add: Prob1_iff)
    from nn_integral_reward_finite[OF \<open>s \<in> S\<close>] this
    have "(\<integral>\<^sup>+\<omega>. reward (Future F) (s ## \<omega>) \<partial>T s) \<noteq> \<infinity>"
      by (simp add: )
    with l_eq \<open>s \<in> S\<close> have "(\<integral>\<^sup>+\<omega>. reward (Future F) (s ## \<omega>) \<partial>T s) = ennreal (l s)"
      by (auto simp: less_top) }
  moreover
  { fix s assume "s \<in> S" "s \<notin> Y"
    with infinite_reward[of s F]
    have "(\<integral>\<^sup>+\<omega>. reward (Future F) (s ## \<omega>) \<partial>T s) = \<infinity>"
      by (simp add: Y_def N_def) }
  ultimately show ?case
    apply (auto simp add: EF F simp del: reward.simps)
    apply (case_tac "x \<in> Y")
    apply auto
    done
qed (auto split: bind_split_asm)

subsection \<open>Completeness of @{const Sat}\<close>

theorem Sat_complete:
  "Sat F \<noteq> None"
proof (induct F rule: Sat.induct)
  case (7 r rel \<Phi> \<Psi>)
  then have F: "Sat \<Phi> = Some (svalid \<Phi>)" "Sat \<Psi> = Some (svalid \<Psi>)"
    by (auto intro!: Sat_sound)

  define constants :: "'s \<Rightarrow> real" where "constants = (\<lambda>s. if s \<in> svalid \<Psi> then 1 else 0)"
  define distr where "distr = LES (Prob0 (svalid \<Phi>) (svalid \<Psi>) \<union> svalid \<Psi>)"
  have "\<exists>l. gauss_jordan' distr constants = Some l"
  proof (rule gauss_jordan'_complete[OF _ uniqueness_of_ProbU])
    show "\<forall>s\<in>S. (\<Sum>s'\<in>S. distr s s' * \<P>(\<omega> in T s'. pvalid (U\<^sup>\<infinity> \<Phi> \<Psi>) (s' ## \<omega>))) = constants s"
      apply (simp add: distr_def constants_def LES_def del: pvalid.simps space_T)
    proof safe
      fix s assume "s \<in> svalid \<Psi>" "s \<in> S"
      then show "(\<Sum>s'\<in>S. (if s' = s then 1 else 0) * \<P>(\<omega> in T s'. pvalid (U\<^sup>\<infinity> \<Phi> \<Psi>) (s' ## \<omega>))) = 1"
        by (simp add: single_l suntil_Stream)
    next
      fix s assume s: "s \<notin> svalid \<Psi>" "s \<in> S"
      let ?x = "\<lambda>s'. \<P>(\<omega> in T s'. pvalid (U\<^sup>\<infinity> \<Phi> \<Psi>) (s' ## \<omega>))"
      show "(\<Sum>s'\<in>S. (if s \<in> Prob0 (svalid \<Phi>) (svalid \<Psi>) then if s' = s then 1 else 0 else if s' = s then \<tau> s s' - 1 else \<tau> s s') * ?x s') = 0"
      proof cases
        assume "s \<in> Prob0 (svalid \<Phi>) (svalid \<Psi>)"
        with s show ?thesis
          by (simp add: single_l Prob0_iff svalid_subset_S T.prob_eq_0_AE del: space_T)
      next
        assume s_not_0: "s \<notin> Prob0 (svalid \<Phi>) (svalid \<Psi>)"
        with s have *:"\<And>s' \<omega>. s' \<in> S \<Longrightarrow> pvalid (U\<^sup>\<infinity> \<Phi> \<Psi>) (s ## s' ## \<omega>) = pvalid (U\<^sup>\<infinity> \<Phi> \<Psi>) (s' ## \<omega>)"
          by (auto simp: suntil_Stream Prob0_iff svalid_subset_S)

        have "(\<Sum>s'\<in>S. (if s' = s then \<tau> s s' - 1 else \<tau> s s') * ?x s') =
          (\<Sum>s'\<in>S. \<tau> s s' * ?x s' - (if s' = s then 1 else 0) * ?x s')"
          by (auto intro!: sum.cong simp: field_simps)
        also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * ?x s') - ?x s"
          using s by (simp add: single_l sum_subtractf)
        finally show ?thesis
          using * prob_sum[OF \<open>s \<in> S\<close>] s_not_0 by (simp del: pvalid.simps)
      qed
    qed
  qed (simp add: distr_def constants_def)
  then have P: "\<exists>l. ProbUinfty (svalid \<Phi>) (svalid \<Psi>) = Some l"
    unfolding ProbUinfty_def constants_def distr_def by simp
  with F show ?case
    by auto
next
  case (10 rel r \<Phi>)
  then have F: "Sat \<Phi> = Some (svalid \<Phi>)"
    by (auto intro!: Sat_sound)

  let ?F = "svalid \<Phi>"
  define N where "N \<equiv> Prob0 S ?F"
  define Y where "Y \<equiv> Prob1 N S ?F"
  define const where "const \<equiv> (\<lambda>s. if s \<in> Y \<and> s \<notin> ?F then - \<rho> s - (\<Sum>s'\<in>S. \<tau> s s' * \<iota> s s') else 0)"
  let ?E = "\<lambda>s'. \<integral>\<^sup>+ \<omega>. reward (Future \<Phi>) (s' ## \<omega>) \<partial>T s'"
  have "\<exists>l. gauss_jordan' (LES (S - Y \<union> ?F)) const = Some l"
  proof (rule gauss_jordan'_complete[OF _ uniqueness_of_ExpFuture[OF N_def Y_def const_def]])
    show "\<forall>s\<in>S. (\<Sum>s'\<in>S. LES (S - Y \<union> svalid \<Phi>) s s' * enn2real (?E s')) = const s"
    proof
      fix s assume "s \<in> S"
      show "(\<Sum>s'\<in>S. LES (S - Y \<union> svalid \<Phi>) s s' * enn2real (?E s')) = const s"
      proof cases
        assume s: "s \<in> S - (Y - svalid \<Phi>)"
        show ?thesis
        proof cases
          assume "s \<in> Y"
          with \<open>s \<in> S\<close> s \<open>s \<in> Y\<close> show ?thesis
            by (simp add: LES_def const_def single_l ev_Stream)
        next
          assume "s \<notin> Y"
          with infinite_reward[of s \<Phi>] Y_def N_def s \<open>s \<in> S\<close>
          show ?thesis by (simp add: const_def LES_def single_l del: reward.simps)
        qed
      next
        assume s: "s \<notin> S - (Y - svalid \<Phi>)"

        have "(\<Sum>s'\<in>S. (if s' = s then \<tau> s s' - 1 else \<tau> s s') * enn2real (?E s')) =
          (\<Sum>s'\<in>S. \<tau> s s' * enn2real (?E s') - (if s' = s then 1 else 0) * enn2real (?E s'))"
          by (auto intro!: sum.cong simp: field_simps)
        also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * enn2real (?E s')) - enn2real (?E s)"
          using \<open>s \<in> S\<close> by (simp add: sum_subtractf single_l)
        finally show ?thesis
          using s \<open>s \<in> S\<close> existence_of_ExpFuture[OF N_def Y_def \<open>s \<in> S\<close> s]
          by (simp add: LES_def const_def del: reward.simps)
      qed
    qed
  qed simp
  then have P: "\<exists>l. ExpFuture (svalid \<Phi>) = Some l"
    unfolding ExpFuture_def const_def N_def Y_def by auto
  with F show ?case
    by auto
qed (force split: bind_split)+

subsection \<open>Completeness and Soundness @{const Sat}\<close>

corollary Sat: "Sat \<Phi> = Some (svalid \<Phi>)"
  using Sat_sound Sat_complete by auto

end

end
