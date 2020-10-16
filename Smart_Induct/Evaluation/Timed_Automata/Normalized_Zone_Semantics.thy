chapter \<open>Forward Analysis with DBMs and Widening\<close>

theory Normalized_Zone_Semantics
  imports DBM_Zone_Semantics Approx_Beta
begin

section \<open>DBM-based Semantics with Normalization\<close>

subsection \<open>Single Step\<close>

inductive step_z_norm ::
  "('a, 'c, t, 's) ta \<Rightarrow> 's \<Rightarrow> t DBM \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> t DBM \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsub>_,_,_\<^esub> \<langle>_, _\<rangle>" [61,61,61,61,61] 61)
where step_z_norm:
  "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l', D'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>k,v,n\<^esub> \<langle>l', norm (FW D' n) k n\<rangle>"

inductive steps_z_norm ::
  "('a, 'c, t, 's) ta \<Rightarrow> 's \<Rightarrow> t DBM \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> t DBM \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsub>_,_,_\<^esub>* \<langle>_, _\<rangle>" [61,61,61,61,61] 61)
where
  refl: "A \<turnstile> \<langle>l, Z\<rangle>  \<leadsto>\<^bsub>k,v,n\<^esub>* \<langle>l, Z\<rangle>" |
  step: "A \<turnstile> \<langle>l, Z\<rangle>  \<leadsto>\<^bsub>k,v,n\<^esub>* \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>k,v,n\<^esub> \<langle>l'', Z''\<rangle>
        \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>k,v,n\<^esub>* \<langle>l'', Z''\<rangle>"

context Regions
begin

abbreviation "v' \<equiv> beta_interp.v'"

abbreviation step_z_norm' ("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^sub>\<N> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^sub>\<N> \<langle>l', D'\<rangle> \<equiv> A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>(k o v'),v,n\<^esub> \<langle>l', D'\<rangle>"

abbreviation steps_z_norm' ("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^sub>\<N>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l', D'\<rangle> \<equiv> A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>(k o v'),v,n\<^esub>* \<langle>l', D'\<rangle>"

inductive_cases[elim!]: "A \<turnstile> \<langle>l, u\<rangle> \<leadsto>\<^sub>\<N> \<langle>l',u'\<rangle>"

declare step_z_norm.intros[intro]

lemma apx_empty_iff'':
  assumes "canonical M1 n" "[M1]\<^bsub>v,n\<^esub> \<subseteq> V" "dbm_int M1 n"
  shows "[M1]\<^bsub>v,n\<^esub> = {} \<longleftrightarrow> [norm M1 (k o v') n]\<^bsub>v,n\<^esub> = {}"
using beta_interp.apx_norm_eq[OF assms] apx_empty_iff'[of "[M1]\<^bsub>v,n\<^esub>"] assms unfolding V'_def by blast

inductive valid_dbm where
  "[M]\<^bsub>v,n\<^esub> \<subseteq> V \<Longrightarrow> dbm_int M n \<Longrightarrow> valid_dbm M"

inductive_cases valid_dbm_cases[elim]: "valid_dbm M"

declare valid_dbm.intros[intro]

lemma step_z_valid_dbm:
  assumes "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l', D'\<rangle>"
    and "global_clock_numbering A v n" "valid_abstraction A X k" "valid_dbm D"
  shows "valid_dbm D'"
proof -
  from alpha_interp.step_z_V step_z_dbm_sound[OF assms(1,2)] step_z_dbm_preserves_int[OF assms(1,2)]
       assms(3,4)
  have
    "dbm_int D' n" "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto> \<langle>l', [D']\<^bsub>v,n\<^esub>\<rangle>"
  by fastforce+
  with alpha_interp.step_z_V[OF this(2)] assms(4) show ?thesis by auto
qed

lemma FW_zone_equiv_spec:
  shows "[M]\<^bsub>v,n\<^esub> = [FW M n]\<^bsub>v,n\<^esub>"
apply (rule FW_zone_equiv) using clock_numbering(2) by auto

lemma cn_weak: "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)" using clock_numbering(2) by blast

lemma valid_dbm_non_empty_diag:
  assumes "valid_dbm M" "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "\<forall> k \<le> n. M k k \<ge> \<one>"
proof safe
  fix k assume k: "k \<le> n"
  have "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)" using clock_numbering(2) by blast
  from k not_empty_cyc_free[OF this assms(2)] show "\<one> \<le> M k k" by (simp add: cyc_free_diag_dest')
qed

lemma non_empty_cycle_free:
  assumes "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "cycle_free M n"
by (meson assms clock_numbering(2) neg_cycle_empty negative_cycle_dest_diag)

lemma norm_empty_diag_preservation:
  assumes "i \<le> n"
  assumes "M i i < Le 0"
  shows "norm M (k o v') n i i < Le 0"
proof -
  have "\<not> Le (k (v' i)) \<prec> Le 0" by auto
  with assms show ?thesis unfolding norm_def by (auto simp: Let_def less)
qed

lemma norm_FW_empty:
  assumes "valid_dbm M"
  assumes "[M]\<^bsub>v,n\<^esub> = {}"
  shows "[norm (FW M n) (k o v') n]\<^bsub>v,n\<^esub> = {}" (is "[?M]\<^bsub>v,n\<^esub> = {}")
proof -
  from assms(2) cyc_free_not_empty clock_numbering(1) cycle_free_diag_equiv have "\<not> cycle_free M n"
  by metis
  from FW_neg_cycle_detect[OF this] obtain i where i: "i \<le> n" "FW M n i i < \<one>" by auto
  with norm_empty_diag_preservation[folded neutral] have "?M i i < \<one>" .
  with \<open>i \<le> n\<close> show ?thesis using beta_interp.neg_diag_empty_spec by auto 
qed

lemma apx_norm_eq_spec:
  assumes "valid_dbm M"
    and "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "beta_interp.Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) = [norm (FW M n) (k o v') n]\<^bsub>v,n\<^esub>"
proof -
  note cyc_free = non_empty_cycle_free[OF assms(2)]
  from assms(1) FW_zone_equiv_spec[of M] have "[M]\<^bsub>v,n\<^esub> = [FW M n]\<^bsub>v,n\<^esub>" by (auto simp: neutral)
  with beta_interp.apx_norm_eq[OF fw_canonical[OF cyc_free] _ FW_int_preservation]
      valid_dbm_non_empty_diag[OF assms(1,2)] assms(1)
 show "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) = [norm (FW M n) (k o v') n]\<^bsub>v,n\<^esub>" by auto
 
qed

print_statement step_z_norm.inducts

(* Crudely copied from step_z_norm.inducts *)
lemma step_z_norm_induct[case_names _ step_z_norm step_z_refl]:
  assumes "x1 \<turnstile> \<langle>x2, x3\<rangle> \<leadsto>\<^bsub>(k o v'),v,n\<^esub> \<langle>x7,x8\<rangle>"
    and step_z_norm:
    "\<And>A l D l' D'.
        A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l',D'\<rangle> \<Longrightarrow>
        P A l D l' (norm (FW D' n) (k o v') n)"
  shows "P x1 x2 x3 x7 x8"
using assms by (induction rule: step_z_norm.inducts) auto

lemma FW_valid_preservation:
  assumes "valid_dbm M"
  shows "valid_dbm (FW M n)"
proof standard
  from FW_int_preservation assms show "dbm_int (FW M n) n" by blast
next
  from FW_zone_equiv_spec[of M, folded neutral] assms show "[FW M n]\<^bsub>v,n\<^esub> \<subseteq> V" by fastforce
qed

text \<open>Obsolete\<close>
lemma norm_diag_preservation:
  assumes "\<forall>l\<le>n. M1 l l \<le> \<one>"
  shows "\<forall>l\<le>n. (norm M1 (k o v') n) l l \<le> \<one>" (is "\<forall> l \<le> n. ?M l l \<le> \<one>")
proof safe
  fix j assume j: "j \<le> n"
  show "?M j j \<le> \<one>"
  proof (cases "j = 0")
    case True
    with j assms show ?thesis unfolding norm_def neutral less_eq dbm_le_def by auto
  next
    case False
    have *: "real ((k \<circ> v') j) \<ge> 0" by auto
    from j assms have **: "M1 j j \<le> Le 0" unfolding neutral by auto
    have "norm_upper (M1 j j) (real ((k \<circ> v') j)) = M1 j j"
    using * ** apply (cases "M1 j j") apply auto by fastforce+
    with assms(1) j False have
      "?M j j = norm_lower (M1 j j) (- real ((k \<circ> v') j))"
    unfolding norm_def by auto
    with ** show ?thesis unfolding neutral by auto
  qed
qed

lemma norm_FW_valid_preservation_non_empty:
  assumes "valid_dbm M" "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "valid_dbm (norm (FW M n) (k o v') n)" (is "valid_dbm ?M")
proof -
  from FW_valid_preservation[OF assms(1)] have valid: "valid_dbm (FW M n)" .
  show ?thesis
  proof standard
    from valid beta_interp.norm_int_preservation show "dbm_int ?M n" by blast
  next
    from fw_canonical[OF non_empty_cycle_free] assms have "canonical (FW M n) n" by auto
    from beta_interp.norm_V_preservation[OF _ this ] valid show "[?M]\<^bsub>v,n\<^esub> \<subseteq> V" by fast
  qed
qed

lemma norm_FW_valid_preservation_empty:
  assumes "valid_dbm M" "[M]\<^bsub>v,n\<^esub> = {}"
  shows "valid_dbm (norm (FW M n) (k o v') n)" (is "valid_dbm ?M")
proof -
  from FW_valid_preservation[OF assms(1)] have valid: "valid_dbm (FW M n)" .
  show ?thesis
  proof standard
    from valid beta_interp.norm_int_preservation show "dbm_int ?M n" by blast
  next
    from norm_FW_empty[OF assms(1,2)] show "[?M]\<^bsub>v,n\<^esub> \<subseteq> V" by fast
  qed
qed

lemma norm_FW_valid_preservation:
  assumes "valid_dbm M"
  shows "valid_dbm (norm (FW M n) (k o v') n)"
using assms norm_FW_valid_preservation_empty norm_FW_valid_preservation_non_empty by metis

lemma norm_beta_sound:
  assumes "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^sub>\<N> \<langle>l',D'\<rangle>" "global_clock_numbering A v n" "valid_abstraction A X k"
  and     "valid_dbm D"
  shows   "A \<turnstile> \<langle>l,[D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l',[D']\<^bsub>v,n\<^esub>\<rangle>" using assms(2-)
proof (induction A l D l' D' rule: step_z_norm_induct, intro assms(1))
  case (step_z_norm A l D l' D')
  from step_z_dbm_sound[OF step_z_norm(1,2)] have "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto> \<langle>l',[D']\<^bsub>v,n\<^esub>\<rangle>" by blast
  then have *: "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l',Approx\<^sub>\<beta> ([D']\<^bsub>v,n\<^esub>)\<rangle>" by force
  show ?case
  proof (cases "[D']\<^bsub>v,n\<^esub> = {}")
    case False
    from apx_norm_eq_spec[OF step_z_valid_dbm[OF step_z_norm] False] *
    show ?thesis by auto
  next
    case True
    with norm_FW_empty[OF step_z_valid_dbm[OF step_z_norm] this] beta_interp.apx_empty *
    show ?thesis by auto
  qed
qed

lemma step_z_norm_valid_dbm:
  assumes "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^sub>\<N> \<langle>l',D'\<rangle>" "global_clock_numbering A v n" "valid_abstraction A X k" "valid_dbm D"
  shows "valid_dbm D'" using assms(2-)
proof (induction A l D l' D' rule: step_z_norm_induct, intro assms(1))
  case (step_z_norm A l D l' D')
  with norm_FW_valid_preservation[OF step_z_valid_dbm[OF step_z_norm]] show ?case by fast
qed

lemma norm_beta_complete:
  assumes "A \<turnstile> \<langle>l,[D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l',Z\<rangle>" "global_clock_numbering A v n" "valid_abstraction A X k"
  and     "valid_dbm D"
  obtains D' where "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^sub>\<N> \<langle>l',D'\<rangle>" "[D']\<^bsub>v,n\<^esub> = Z" "valid_dbm D'"
proof -
  from assms(1) obtain Z' where Z': "A \<turnstile> \<langle>l,[D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto> \<langle>l',Z'\<rangle>" "Z = Approx\<^sub>\<beta> Z'" by auto
  from assms(4) have "dbm_int D n" by auto
  with step_z_dbm_DBM[OF Z'(1) assms(2)] step_z_dbm_preserves_int[OF _ assms(2,3)] obtain D' where
    D': "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l',D'\<rangle>" "Z' = [D']\<^bsub>v,n\<^esub>" "dbm_int D' n"
  by auto
  note valid_D' = step_z_valid_dbm[OF D'(1) assms(2,3)]
  obtain D'' where D'': "D'' = norm (FW D' n) (k \<circ> v') n" by auto
  show ?thesis
  proof (cases "Z' = {}")
    case False
    with D' have *: "[D']\<^bsub>v,n\<^esub> \<noteq> {}" by auto
    from apx_norm_eq_spec[OF valid_D' this] D'' D'(2) Z'(2) assms(4) have "Z = [D'']\<^bsub>v,n\<^esub>" by auto
    with norm_FW_valid_preservation[OF valid_D'] D' D'' * that[of D''] assms(4)
    show thesis by blast
  next
    case True
    with norm_FW_empty[OF valid_D'[OF assms(4)]] D'' D' Z'(2)
         norm_FW_valid_preservation[OF valid_D'[OF assms(4)]] beta_interp.apx_empty
    show thesis
    apply -
    apply (rule that[of D''])
      apply blast
    by fastforce+
  qed
qed

subsection \<open>Multi step\<close>

declare steps_z_norm.intros[intro]

lemma steps_z_norm_induct[case_names _ refl step]:
  assumes "x1 \<turnstile> \<langle>x2, x3\<rangle> \<leadsto>\<^bsub>(k o v'),v,n\<^esub>* \<langle>x7,x8\<rangle>"
    and "\<And>A l Z. P A l Z l Z"
    and
    "\<And>A l Z l' Z' l'' Z''.
        A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>(k o v'),v,n\<^esub>* \<langle>l',Z'\<rangle> \<Longrightarrow>
        P A l Z l' Z' \<Longrightarrow>
        A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>(k o v'),v,n\<^esub> \<langle>l'',Z''\<rangle> \<Longrightarrow> P A l Z l'' Z''"
  shows "P x1 x2 x3 x7 x8"
using assms by (induction rule: steps_z_norm.induct) auto

lemma norm_beta_sound_multi:
  assumes "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l',D'\<rangle>" "global_clock_numbering A v n" "valid_abstraction A X k" "valid_dbm D"
  shows "A \<turnstile> \<langle>l,[D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l',[D']\<^bsub>v,n\<^esub>\<rangle> \<and> valid_dbm D'" using assms(2-)
proof (induction A l D l' D' rule: steps_z_norm_induct, intro assms(1))
  case refl then show ?case by fast
next
  case (step A l Z l' Z' l'' Z'')
  then have "A \<turnstile> \<langle>l, [Z]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l',[Z']\<^bsub>v,n\<^esub>\<rangle>" "valid_dbm Z'" by fast+
  with norm_beta_sound[OF step(2,4,5)] step_z_norm_valid_dbm[OF step(2,4,5)] show ?case by force
qed

lemma norm_beta_complete_multi:
  assumes "A \<turnstile> \<langle>l,[D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l',Z\<rangle>" "global_clock_numbering A v n" "valid_abstraction A X k"
  and     "valid_dbm D"
  obtains D' where "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l',D'\<rangle>" "[D']\<^bsub>v,n\<^esub> = Z" "valid_dbm D'"
using assms
proof (induction A l "[D]\<^bsub>v,n\<^esub>" l' Z arbitrary: thesis rule: steps_z_beta.induct)
  case refl
  from this(1)[OF steps_z_norm.refl] this(4) show thesis by fast
next
  case (step A l l' Z' l'' Z'')
  from step(2)[OF _ step(5,6,7)] obtain D' where D':
    "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l',D'\<rangle>" "[D']\<^bsub>v,n\<^esub> = Z'" "valid_dbm D'"
  .
  with norm_beta_complete[OF _ step(5,6), of l' D' l'' Z''] step(3) obtain D'' where D'':
    "A \<turnstile> \<langle>l', D'\<rangle> \<leadsto>\<^sub>\<N> \<langle>l'',D''\<rangle>" "[D'']\<^bsub>v,n\<^esub> = Z''" "valid_dbm D''"
  by auto
  with D'(1) step(4)[of D''] show thesis by blast
qed

lemma norm_beta_equiv_multi:
  assumes "global_clock_numbering A v n" "valid_abstraction A X k"
  and     "valid_dbm D"
  shows "(\<exists> D'. A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l',D'\<rangle> \<and> Z = [D']\<^bsub>v,n\<^esub>) \<longleftrightarrow> A \<turnstile> \<langle>l,[D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l',Z\<rangle>"
using norm_beta_complete_multi[OF _ assms] norm_beta_sound_multi[OF _ assms] by metis


subsection \<open>Connecting with Correctness Results for Approximating Semantics\<close>

lemma steps_z_norm_complete':
  assumes "A \<turnstile> \<langle>l,[D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>* \<langle>l',Z\<rangle>" "global_clock_numbering A v n" "valid_abstraction A X k"
  and "valid_dbm D"
  shows "\<exists> D'. A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l',D'\<rangle> \<and>  Z \<subseteq> [D']\<^bsub>v,n\<^esub>"
proof -
  from steps_z_beta_complete[OF assms(1,3)] assms(4) obtain Z'' where Z'':
    "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l',Z''\<rangle>" "Z \<subseteq> Z''"
  by auto
  from this(2) norm_beta_complete_multi[OF this(1) assms(2,3,4)] show ?thesis by metis
qed

lemma valid_dbm_V':
  assumes "valid_dbm M"
  shows "[M]\<^bsub>v,n\<^esub> \<in> V'"
using assms unfolding V'_def by force

lemma steps_z_norm_sound':
  assumes "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l',D'\<rangle>"
    and "global_clock_numbering A v n"
    and "valid_abstraction A X k"
    and "valid_dbm D"
    and "[D']\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "\<exists>Z. A \<turnstile> \<langle>l,[D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>* \<langle>l',Z\<rangle> \<and> Z \<noteq> {}"
proof -
  from norm_beta_sound_multi[OF assms(1-4)] have "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l',[D']\<^bsub>v,n\<^esub>\<rangle>" by fast
  from steps_z_beta_sound[OF this _ assms(3) valid_dbm_V'] assms(2,4,5) show ?thesis by blast
qed


section \<open>The Final Result About Language Emptiness\<close>

lemma steps_z_norm_complete:
  assumes "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" "u \<in> [D]\<^bsub>v,n\<^esub>"
    and   "global_clock_numbering A v n" "valid_abstraction A X k" "valid_dbm D"
  shows "\<exists> D'. A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l',D'\<rangle> \<and> u' \<in> [D']\<^bsub>v,n\<^esub>"
using steps_z_norm_complete'[OF _ assms(3-)] steps_z_complete[OF assms(1,2)] by fast

lemma steps_z_norm_sound:
  assumes "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l',D'\<rangle>"
    and   "global_clock_numbering A v n" "valid_abstraction A X k" "valid_dbm D"
    and   "[D']\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "\<exists> u \<in> [D]\<^bsub>v,n\<^esub>. \<exists> u'. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>"
using steps_z_norm_sound'[OF assms] steps_z_sound by fast

theorem steps_z_norm_decides_emptiness:
  assumes "global_clock_numbering A v n" "valid_abstraction A X k" "valid_dbm D"
  shows "(\<exists> D'. A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l',D'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> \<noteq> {})
     \<longleftrightarrow> (\<exists> u \<in> [D]\<^bsub>v,n\<^esub>. \<exists> u'. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>)"
using steps_z_norm_sound[OF _ assms] steps_z_norm_complete[OF _ _ assms] by fast


section \<open>Finiteness of the Search Space\<close>

abbreviation "dbm_default M \<equiv> (\<forall> i > n. \<forall> j. M i j = \<one>) \<and> (\<forall> j > n. \<forall> i. M i j = \<one>)"

lemma "a \<in> \<int> \<Longrightarrow> \<exists> b. a = real_of_int b" using Ints_cases by auto

lemma norm_default_preservation:
  "dbm_default M \<Longrightarrow> dbm_default (norm M (k o v') n)"
by (simp add: norm_def)

lemma normalized_integral_dbms_finite:
  "finite {norm M (k o v') n | M. dbm_int M n \<and> dbm_default M}"
proof -
  let ?u = "Max {(k o v') i | i. i \<le> n}" let ?l = "- ?u"
  let ?S = "(Le ` {d :: int. ?l \<le> d \<and> d \<le> ?u}) \<union> (Lt ` {d :: int. ?l \<le> d \<and> d \<le> ?u}) \<union> {\<infinity>}"
  from finite_set_of_finite_funs2[of "{0..n}" "{0..n}" ?S] have fin:
    "finite {f. \<forall>x y. (x \<in> {0..n} \<and> y \<in> {0..n} \<longrightarrow> f x y \<in> ?S)
                \<and> (x \<notin> {0..n} \<longrightarrow> f x y = \<one>) \<and> (y \<notin> {0..n} \<longrightarrow> f x y = \<one>)}" (is "finite ?R")
  by auto
  { fix M :: "t DBM" assume A: "dbm_int M n" "dbm_default M"
    let ?M = "norm M (k o v') n"
    from beta_interp.norm_int_preservation[OF A(1)] norm_default_preservation[OF A(2)] have
      A: "dbm_int ?M n" "dbm_default ?M"
    by blast+
    { fix i j assume "i \<in> {0..n}" "j \<in> {0..n}"
      then have B: "i \<le> n" "j \<le> n" by auto
      have "?M i j \<in> ?S"
      proof (cases "?M i j = \<infinity>")
        case True then show ?thesis by auto
      next
        case False
        note not_inf = this
        with B A(1) have "get_const (?M i j) \<in> \<int>" by auto
        moreover have "?l \<le> get_const (?M i j) \<and> get_const (?M i j) \<le> ?u"
        proof (cases "i = 0")
          case True
          show ?thesis
          proof (cases "j = 0")
            case True
            with \<open>i = 0\<close> A(1) B have
              "?M i j = norm_lower (norm_upper (M 0 0) 0) 0"
            unfolding norm_def by auto
            also have "\<dots> \<noteq> \<infinity> \<longrightarrow> get_const \<dots> = 0" by (cases "M 0 0"; fastforce)
            finally show ?thesis using not_inf by auto
          next
            case False
            with \<open>i = 0\<close> B not_inf have "?M i j \<le> Le 0" "Lt (-real (k (v' j))) \<le> ?M i j"
            by (unfold norm_def, auto simp: Let_def, unfold less[symmetric], auto)
            with not_inf have "get_const (?M i j) \<le> 0" "-k (v' j) \<le> get_const (?M i j)"
            by (cases "?M i j"; auto)+
            moreover from \<open>j \<le> n\<close> have "- (k o v') j \<ge> ?l" by (auto intro: Max_ge)
            ultimately show ?thesis by auto
          qed
        next
          case False
          then have "i > 0" by simp
          show ?thesis
          proof (cases "j = 0")
            case True
            with \<open>i > 0\<close> A(1) B not_inf have "Lt 0 \<le> ?M i j" "?M i j \<le> Le (real ((k \<circ> v') i))"
            by (unfold norm_def, auto simp: Let_def, unfold less[symmetric], auto)
            with not_inf have "0 \<le> get_const (?M i j)" "get_const (?M i j) \<le> k (v' i)"
            by (cases "?M i j"; auto)+
            moreover from \<open>i \<le> n\<close> have "(k o v') i \<le> ?u" by (auto intro: Max_ge)
            ultimately show ?thesis by auto
          next
            case False
            with \<open>i > 0\<close> A(1) B not_inf have
              "Lt (-real ((k \<circ> v') j)) \<le> ?M i j" "?M i j \<le> Le (real ((k \<circ> v') i))"
            by (unfold norm_def, auto simp: Let_def, unfold less[symmetric], auto)
            with not_inf have "- k (v' j) \<le> get_const (?M i j)" "get_const (?M i j) \<le> k (v' i)"
            by (cases "?M i j"; auto)+
            moreover from \<open>i \<le> n\<close> \<open>j \<le> n\<close> have "(k o v') i \<le> ?u" "(k o v') j \<le> ?u" by (auto intro: Max_ge)
            ultimately show ?thesis by auto
          qed
        qed
        ultimately show ?thesis by (cases "?M i j"; auto elim: Ints_cases)
      qed
    } moreover
    { fix i j assume "i \<notin> {0..n}"
      with A(2) have "?M i j = \<one>" by auto
    } moreover
    { fix i j assume "j \<notin> {0..n}"
      with A(2) have "?M i j = \<one>" by auto
    } moreover note the = calculation
  } then have "{norm M (k o v') n | M. dbm_int M n \<and> dbm_default M} \<subseteq> ?R" by blast
  with fin show ?thesis by (blast intro: finite_subset)
qed

end


section \<open>Appendix: Standard Clock Numberings for Concrete Models\<close>

locale Regions' =
  fixes X and k :: "'c \<Rightarrow> nat" and v :: "'c \<Rightarrow> nat" and n :: nat and not_in_X
  assumes finite: "finite X"
  assumes clock_numbering': "\<forall> c \<in> X. v c > 0" "\<forall> c. c \<notin> X \<longrightarrow> v c > n"
  assumes bij: "bij_betw v X {1..n}"
  assumes non_empty: "X \<noteq> {}"
  assumes not_in_X: "not_in_X \<notin> X"

begin

lemma inj: "inj_on v X" using bij_betw_imp_inj_on bij by simp

lemma cn_weak: "\<forall> c. v c > 0" using clock_numbering' by force

lemma in_X: assumes "v x \<le> n" shows "x \<in> X" using assms clock_numbering'(2) by force

end

sublocale Regions' \<subseteq> Regions
proof (unfold_locales, auto simp: finite clock_numbering' non_empty cn_weak not_in_X, goal_cases)
  case (1 x y) with inj in_X show ?case unfolding inj_on_def by auto
next
  case (2 k)
  from bij have "v ` X = {1..n}" unfolding bij_betw_def by auto
  from 2 have "k \<in> {1..n}" by simp
  then obtain x where "x \<in> X" "v x = k" unfolding image_def
  by (metis (no_types, lifting) \<open>v ` X = {1..n}\<close> imageE)
  then show ?case by blast
next
  case (3 x) with bij show ?case unfolding bij_betw_def by auto
qed

(* This is for automata carrying real time annotations *)
lemma standard_abstraction:
  assumes "finite (clkp_set A)" "finite (collect_clkvt (trans_of A))" "\<forall>(_,m::real) \<in> clkp_set A. m \<in> \<nat>"
  obtains k :: "'c \<Rightarrow> nat" where "valid_abstraction A (clk_set A) k"
proof -
  from assms have 1: "finite (clk_set A)" by auto
  have 2: "collect_clkvt (trans_of A) \<subseteq> clk_set A" by auto
  from assms obtain L where L: "distinct L" "set L = clkp_set A" by (meson finite_distinct_list)
  let ?M = "\<lambda> c. {m . (c, m) \<in> clkp_set A}"
  let ?X = "clk_set A"
  let ?m = "map_of L"
  let ?k = "\<lambda> x. if ?M x = {} then 0 else nat (floor (Max (?M x)) + 1)"
  { fix c m assume A: "(c, m) \<in> clkp_set A"
    from assms(1) have "finite (snd ` clkp_set A)" by auto
    moreover have "?M c \<subseteq> (snd ` clkp_set A)" by force
    ultimately have fin: "finite (?M c)" by (blast intro: finite_subset)
    then have "Max (?M c) \<in> {m . (c, m) \<in> clkp_set A}" using Max_in A by auto
    with assms(3) have "Max (?M c) \<in> \<nat>" by auto
    then have "floor (Max (?M c)) = Max (?M c)" by (metis Nats_cases floor_of_nat of_int_of_nat_eq)
    with A have *: "?k c = Max (?M c) + 1"
    proof auto
      fix n :: int and x :: real
      assume "Max {m. (c, m) \<in> clkp_set A} = real_of_int n"
      then have "real_of_int (n + 1) \<in> \<nat>"
        using \<open>Max {m. (c, m) \<in> clkp_set A} \<in> \<nat>\<close> by auto
      then show "real (nat (n + 1)) = real_of_int n + 1"
        by (metis Nats_cases ceiling_of_int nat_int of_int_1 of_int_add of_int_of_nat_eq)
    qed
    from fin A have "Max (?M c) \<ge> m" by auto
    moreover from A assms(3) have "m \<in> \<nat>" by auto
    ultimately have "m \<le> ?k c" "m \<in> \<nat>" "c \<in> clk_set A" using A * by force+
  }
  then have "\<forall>(x, m)\<in>clkp_set A. m \<le> ?k x \<and> x \<in> clk_set A \<and> m \<in> \<nat>" by blast
  with 1 2 have "valid_abstraction A ?X ?k" by - (standard, assumption+)
  then show thesis ..
qed

definition
  "finite_ta A \<equiv> finite (clkp_set A) \<and> finite (collect_clkvt (trans_of A))
                 \<and> (\<forall>(_,m::real) \<in> clkp_set A. m \<in> \<nat>) \<and> clk_set A \<noteq> {} \<and> -clk_set A \<noteq> {}"

lemma finite_ta_Regions':
  fixes A :: "('a, 'c, real, 's) ta"
  assumes "finite_ta A"
  obtains v n x where "Regions' (clk_set A) v n x"
proof -
  from assms obtain x where x: "x \<notin> clk_set A" unfolding finite_ta_def by auto
  from assms(1) have "finite (clk_set A)" unfolding finite_ta_def by auto
  with standard_numbering[of "clk_set A"] assms obtain v and n :: nat where
            "bij_betw v (clk_set A) {1..n}"
            "\<forall>c\<in>clk_set A. 0 < v c" "\<forall>c. c \<notin> clk_set A \<longrightarrow> n < v c"
  by auto
  then have "Regions' (clk_set A) v n x" using x assms unfolding finite_ta_def by - (standard, auto)
  then show ?thesis ..
qed

lemma finite_ta_RegionsD:
  assumes "finite_ta A"
  obtains k :: "'b \<Rightarrow> nat" and v n x where
    "Regions' (clk_set A) v n x" "valid_abstraction A (clk_set A) k" "global_clock_numbering A v n"
proof -
  from standard_abstraction assms obtain k :: "'b \<Rightarrow> nat" where k:
    "valid_abstraction A (clk_set A) k" 
  unfolding finite_ta_def by blast
  from finite_ta_Regions'[OF assms] obtain v n x where *: "Regions' (clk_set A) v n x" .
  then interpret interp: Regions' "clk_set A" k v n x .
  from interp.clock_numbering have "global_clock_numbering A v n" by blast
  with * k show ?thesis ..
qed

definition valid_dbm where "valid_dbm M n \<equiv> dbm_int M n \<and> (\<forall> i \<le> n. M 0 i \<le> \<one>)"

lemma dbm_positive:
  assumes "M 0 (v c) \<le> \<one>" "v c \<le> n" "DBM_val_bounded v u M n"
  shows "u c \<ge> 0"
proof -
  from assms have "dbm_entry_val u None (Some c) (M 0 (v c))" unfolding DBM_val_bounded_def by auto
  with assms(1) show ?thesis
  proof (cases "M 0 (v c)", goal_cases)
    case 1
    then show ?case unfolding less_eq neutral using order_trans by (fastforce dest!: le_dbm_le)
  next
    case 2
    then show ?case unfolding less_eq neutral
    by (auto dest!: lt_dbm_le) (meson less_trans neg_0_less_iff_less not_less)
  next
    case 3
    then show ?case unfolding neutral less_eq dbm_le_def by auto
  qed
qed


lemma valid_dbm_pos:
  assumes "valid_dbm M n"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> {u. \<forall> c. v c \<le> n \<longrightarrow> u c \<ge> 0}"
using dbm_positive assms unfolding valid_dbm_def unfolding DBM_zone_repr_def by fast

lemma (in Regions') V_alt_def:
  shows "{u. \<forall> c. v c > 0 \<and> v c \<le> n \<longrightarrow> u c \<ge> 0} = V"
unfolding V_def using clock_numbering by metis

text \<open>
  An example of obtaining concrete models from our formalizations.
\<close>
lemma steps_z_norm_sound_spec:
  assumes "finite_ta A"
  obtains k v n where
  "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>k,v,n\<^esub>* \<langle>l',D'\<rangle> \<and> valid_dbm D n \<and> [D']\<^bsub>v,n\<^esub> \<noteq> {}
  \<longrightarrow> (\<exists>Z. A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>* \<langle>l',Z\<rangle> \<and> Z \<noteq> {})"
proof -
  from finite_ta_RegionsD[OF assms(1)] obtain k :: "'b \<Rightarrow> nat" and v n x where *:
    "Regions' (clk_set A) v n x" "valid_abstraction A (clk_set A) k" "global_clock_numbering A v n"
  .
  from this(1) interpret interp: Regions' "clk_set A" k v n x .
  define v' where "v' i = (if i \<le> n then (THE c. c \<in> clk_set A \<and> v c = i) else x)" for i
  { fix l D l' D'
    assume step: "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>(k o v'),v,n\<^esub>* \<langle>l',D'\<rangle>"
    and valid: "valid_dbm D n" and non_empty: "[D']\<^bsub>v,n\<^esub> \<noteq> {}"
    from valid_dbm_pos[OF valid] interp.V_alt_def have "[D]\<^bsub>v,n\<^esub> \<subseteq> interp.V" by blast
    with valid have valid: "interp.valid_dbm D" unfolding valid_dbm_def by auto
    from step have "interp.steps_z_norm' A l D l' D'" unfolding v'_def interp.beta_interp.v'_def .
    note this = interp.steps_z_norm_sound'[OF this *(3,2) valid non_empty]
  }
  then show thesis by (blast intro: that)
qed

end
