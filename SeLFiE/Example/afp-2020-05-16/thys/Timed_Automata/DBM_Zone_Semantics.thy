subsection \<open>Semantics Based on DBMs\<close>

theory DBM_Zone_Semantics
imports DBM_Operations
begin

subsection \<open>Single Step\<close>

inductive step_z_dbm ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('t::time) DBM
    \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> ('t::time) DBM \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsub>_,_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  step_t_z_dbm:
    "D_inv = abstr (inv_of A l) (\<lambda>i j. \<infinity>) v \<Longrightarrow> A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l,And (up (And D D_inv)) D_inv\<rangle>" |
  step_a_z_dbm:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'
    \<Longrightarrow> A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l',And (reset' (And D (abstr g (\<lambda>i j. \<infinity>) v)) n r v 0)
                                             (abstr (inv_of A l') (\<lambda>i j. \<infinity>) v)\<rangle>"
inductive_cases step_z_cases: "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l', D'\<rangle>"

declare step_z_dbm.intros[intro]

lemma step_z_dbm_preserves_int:
  assumes "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l',D'\<rangle>" "global_clock_numbering A v n" "valid_abstraction A X k"
          "dbm_int D n"
  shows "dbm_int D' n"
using assms
proof (cases, goal_cases)
  case (1 D'')
  hence "clock_numbering' v n" "\<forall>c\<in>clk_set A. v c \<le> n" by blast+
  from 1(2) have "\<forall> (x, m) \<in> clkp_set A. m \<in> \<nat>" by (auto elim: valid_abstraction.cases)
  from dbm_int_inv_abstr[OF this] 1 have D''_int: "dbm_int D'' n" by simp
  show ?thesis unfolding 1(5) by (intro And_int_preservation up_int_preservation dbm_int_inv_abstr D''_int 1)
next
  case (2 g a r)
  hence assms: "clock_numbering' v n" "\<forall>c\<in>clk_set A. v c \<le> n" "\<forall>k\<le>n. k > 0 \<longrightarrow> (\<exists>c. v c = k)" by blast+
  from 2(2) have *: "\<forall> (x, m) \<in> clkp_set A. m \<in> \<nat>" by (auto elim: valid_abstraction.cases)
  from dbm_int_inv_abstr[OF this] have D'_int: "dbm_int (abstr (inv_of A l') (\<lambda>i j. \<infinity>) v) n" by simp
  from dbm_int_guard_abstr 2 have D''_int: "dbm_int (abstr g (\<lambda>i j. \<infinity>) v) n" by simp
  have "set r \<subseteq> clk_set A" using 2(5) unfolding trans_of_def collect_clkvt_def by fastforce
  hence **:"\<forall>c\<in>set r. v c \<le> n" using assms(2) by fastforce
  show ?thesis unfolding 2(4)
  by (intro And_int_preservation DBM_reset'_int_preservation dbm_int_inv_abstr 2 D''_int)
     (simp_all add: assms(1) * **)
qed

lemma And_correct:
  shows "[M1]\<^bsub>v,n\<^esub> \<inter> [M2]\<^bsub>v,n\<^esub> = [And M1 M2]\<^bsub>v,n\<^esub>"
using DBM_and_sound1 DBM_and_sound2 DBM_and_complete unfolding DBM_zone_repr_def by auto

lemma up_correct:
  assumes "clock_numbering' v n"
  shows "[up M]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>\<^sup>\<up>"
using assms
 apply safe
  apply (rule DBM_up_sound')
   apply assumption+
 apply (rule DBM_up_complete')
  apply auto
done

lemma step_z_dbm_sound:
  assumes "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l', D'\<rangle>" "global_clock_numbering A v n"
  shows "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto> \<langle>l', [D']\<^bsub>v,n\<^esub>\<rangle>"
using assms
proof (cases, goal_cases)
  case (1 D'')
  hence "clock_numbering' v n" "\<forall>c\<in>clk_set A. v c \<le> n" by blast+
  note assms = assms(1) this
  from assms(3) have *: "\<forall>c\<in>collect_clks (inv_of A l). v c \<le> n"
  unfolding clkp_set_def collect_clki_def inv_of_def by (fastforce simp: collect_clks_id)
  from 1 have D'':"[D'']\<^bsub>v,n\<^esub> = {u. u \<turnstile> inv_of A l}" using dbm_abstr_zone_eq[OF assms(2) *] by metis
  with And_correct have A11: "[And D D'']\<^bsub>v,n\<^esub> = ([D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> inv_of A l})" by blast
  with And_correct D'' have
    "[D']\<^bsub>v,n\<^esub> = ([up (And D D'')]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> inv_of A l})"
  unfolding 1(3) by blast
  with up_correct[OF assms(2)] A11 have
    "[D']\<^bsub>v,n\<^esub> = (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}"
  by metis
  with 1(2) show ?thesis by auto
next
  case (2 g a r)
  hence "clock_numbering' v n" "\<forall>c\<in>clk_set A. v c \<le> n" "\<forall>k\<le>n. k > 0 \<longrightarrow> (\<exists>c. v c = k)" by blast+
  note assms = assms(1) this
  from assms(3) have *: "\<forall>c\<in>collect_clks (inv_of A l'). v c \<le> n"
  unfolding clkp_set_def collect_clki_def inv_of_def by (fastforce simp: collect_clks_id)
  have D':
    "[abstr (inv_of A l') (\<lambda>i j. \<infinity>) v]\<^bsub>v,n\<^esub> = {u. u \<turnstile> inv_of A l'}"
  using 2 dbm_abstr_zone_eq[OF assms(2) *] by simp
  from assms(3) 2(3) have *: "\<forall>c\<in>collect_clks g. v c \<le> n" 
  unfolding clkp_set_def collect_clkt_def inv_of_def by (fastforce simp: collect_clks_id)
  have D'':"[abstr g (\<lambda>i j. \<infinity>) v]\<^bsub>v,n\<^esub> = {u. u \<turnstile> g}" using 2 dbm_abstr_zone_eq[OF assms(2) *] by auto
  with And_correct have A11: "[And D (abstr g (\<lambda>i j. \<infinity>) v)]\<^bsub>v,n\<^esub> = ([D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> g})" by blast
  let ?D = "reset' (And D (abstr g (\<lambda>i j. \<infinity>) v)) n r v 0"
  have "set r \<subseteq> clk_set A" using 2(3) unfolding trans_of_def collect_clkvt_def by fastforce
  hence **:"\<forall>c\<in>set r. v c \<le> n" using assms(3) by fastforce
  have D_reset: "[?D]\<^bsub>v,n\<^esub> = zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r"
  proof safe
    fix u assume u: "u \<in> [?D]\<^bsub>v,n\<^esub>"
    from DBM_reset'_sound[OF assms(4,2) ** this] obtain ts where
      "set_clocks r ts u \<in> [And D (abstr g (\<lambda>i j. \<infinity>) v)]\<^bsub>v,n\<^esub>"
    by auto
    with A11 have *: "set_clocks r ts u \<in> ([D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> g})" by blast
    from DBM_reset'_resets[OF assms(4,2) **] u 
    have "\<forall>c \<in> set r. u c = 0" unfolding DBM_zone_repr_def by auto
    from reset_set[OF this] have "[r\<rightarrow>0]set_clocks r ts u = u" by simp
    with * show "u \<in> zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r" unfolding zone_set_def by force
  next
    fix u assume u: "u \<in> zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r"
    from DBM_reset'_complete[OF _ assms(2) **] u A11
    show "u \<in> [?D]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def zone_set_def by force
  qed
  from D' And_correct D_reset have A22:
    "[And ?D (abstr (inv_of A l') (\<lambda>i j. \<infinity>) v)]\<^bsub>v,n\<^esub> = ([?D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> inv_of A l'})"
  by blast
  with D_reset 2(2,3) show ?thesis by auto
qed

lemma step_z_dbm_DBM:
  assumes "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto> \<langle>l', Z\<rangle>" "global_clock_numbering A v n"
  obtains D' where "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l', D'\<rangle>" "Z = [D']\<^bsub>v,n\<^esub>"
using assms
proof (cases, goal_cases)
  case 1
  hence "clock_numbering' v n" "\<forall>c\<in>clk_set A. v c \<le> n" by metis+
  note assms = assms(1) this
  from assms(3) have *: "\<forall>c\<in>collect_clks (inv_of A l). v c \<le> n"
  unfolding clkp_set_def collect_clki_def inv_of_def by (fastforce simp: collect_clks_id)
  obtain D'' where D''_def: "D'' = abstr (inv_of A l) (\<lambda>i j. \<infinity>) v" by auto
  hence D'':"[D'']\<^bsub>v,n\<^esub> = {u. u \<turnstile> inv_of A l}" using dbm_abstr_zone_eq[OF assms(2) *] by metis
  obtain A1 where A1: "A1 = And D D''" by fast
  with And_correct D'' have A11: "[A1]\<^bsub>v,n\<^esub> = ([D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> inv_of A l})" by blast
  then obtain D_up where D_up': "D_up = up A1" by blast
  with up_correct assms(2) A11 have D_up: "[D_up]\<^bsub>v,n\<^esub> = (([D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> inv_of A l}))\<^sup>\<up>" by metis
  obtain A2 where A2: "A2 = And D_up D''" by fast
  with And_correct D'' have A22: "[A2]\<^bsub>v,n\<^esub> = ([D_up]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> inv_of A l})" by blast
  from A2 D_up' D''_def A1 have "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l,A2\<rangle>" by blast
  moreover from A22 D_up have
    "[A2]\<^bsub>v,n\<^esub> = (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}"
  by auto
  ultimately show thesis using 1 by (intro that[of A2]) auto
next
  case (2 g a r)
  hence "clock_numbering' v n" "\<forall>c\<in>clk_set A. v c \<le> n" "\<forall>k\<le>n. k > 0 \<longrightarrow> (\<exists>c. v c = k)" by metis+
  note assms = assms(1) this
  from assms(3) have *: "\<forall>c\<in>collect_clks (inv_of A l'). v c \<le> n"
  unfolding clkp_set_def collect_clki_def inv_of_def by (fastforce simp: collect_clks_id)
  obtain D' where D'_def: "D' = abstr (inv_of A l') (\<lambda>i j. \<infinity>) v" by blast
  hence D':"[D']\<^bsub>v,n\<^esub> = {u. u \<turnstile> inv_of A l'}" using dbm_abstr_zone_eq[OF assms(2) *] by simp
  from assms(3) 2(4) have *: "\<forall>c\<in>collect_clks g. v c \<le> n" 
  unfolding clkp_set_def collect_clkt_def inv_of_def by (fastforce simp: collect_clks_id)
  obtain D'' where D''_def: "D'' = abstr g (\<lambda>i j. \<infinity>) v" by blast
  hence D'':"[D'']\<^bsub>v,n\<^esub> = {u. u \<turnstile> g}" using dbm_abstr_zone_eq[OF assms(2) *] by auto
  obtain A1 where A1: "A1 = And D D''" by fast
  with And_correct D'' have A11: "[A1]\<^bsub>v,n\<^esub> = ([D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> g})" by blast
  let ?D = "reset' A1 n r v 0"
  have "set r \<subseteq> clk_set A" using 2(4) unfolding trans_of_def collect_clkvt_def by fastforce
  hence **:"\<forall>c\<in>set r. v c \<le> n" using assms(3) by fastforce
  have D_reset: "[?D]\<^bsub>v,n\<^esub> = zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r"
  proof safe
    fix u assume u: "u \<in> [?D]\<^bsub>v,n\<^esub>"
    from DBM_reset'_sound[OF assms(4,2) ** this] obtain ts where
      "set_clocks r ts u \<in> [A1]\<^bsub>v,n\<^esub>"
    by auto
    with A11 have *: "set_clocks r ts u \<in> ([D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> g})" by blast
    from DBM_reset'_resets[OF assms(4,2) **] u 
    have "\<forall>c \<in> set r. u c = 0" unfolding DBM_zone_repr_def by auto
    from reset_set[OF this] have "[r\<rightarrow>0]set_clocks r ts u = u" by simp
    with * show "u \<in> zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r" unfolding zone_set_def by force
  next
    fix u assume u: "u \<in> zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r"
    from DBM_reset'_complete[OF _ assms(2) **] u A11
    show "u \<in> [?D]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def zone_set_def by force
  qed
  obtain A2 where A2: "A2 = And ?D D'" by fast
  with And_correct D' have A22: "[A2]\<^bsub>v,n\<^esub> = ([?D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> inv_of A l'})" by blast
  from 2(4) A2 D'_def D''_def A1 have "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l',A2\<rangle>" by blast
  moreover from A22 D_reset have
    "[A2]\<^bsub>v,n\<^esub> = zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"
  by auto
  ultimately show ?thesis using 2 by (intro that[of A2]) simp+
qed

lemma step_z_computable:
  assumes "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto> \<langle>l',Z\<rangle>" "global_clock_numbering A v n"
  obtains D' where "Z = [D']\<^bsub>v,n\<^esub>"
using step_z_dbm_DBM[OF assms] by blast

lemma step_z_dbm_complete:
  assumes "global_clock_numbering A v n" "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>"
  and     "u \<in> [(D )]\<^bsub>v,n\<^esub>"
  shows "\<exists> D'. A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l',D'\<rangle> \<and> u' \<in> [D']\<^bsub>v,n\<^esub>"
proof -
  note A = assms
  from step_z_complete[OF A(2,3)] obtain Z' where Z': "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto> \<langle>l',Z'\<rangle>" "u' \<in> Z'" by auto
  with step_z_dbm_DBM[OF Z'(1) A(1)] obtain D' where D':
    "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l',D'\<rangle>" "Z' = [D']\<^bsub>v,n\<^esub>"
  by metis
  with Z'(2) show ?thesis by auto
qed


subsection \<open>Multi Step\<close>

inductive steps_z_dbm ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('t::time) DBM
    \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> ('t::time) DBM \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>*\<^bsub>_,_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  refl: "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>*\<^bsub>v,n\<^esub> \<langle>l,D\<rangle>" |
  step: "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l',D'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l',D'\<rangle> \<leadsto>*\<^bsub>v,n\<^esub> \<langle>l'',D''\<rangle> \<Longrightarrow>
         A \<turnstile> \<langle>l,D\<rangle> \<leadsto>*\<^bsub>v,n\<^esub> \<langle>l'',D''\<rangle>"

declare steps_z_dbm.intros[intro]

lemma steps_z_dbm_sound:
  assumes "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>*\<^bsub>v,n\<^esub> \<langle>l',D'\<rangle>"
  and "global_clock_numbering A v n"
  and "u' \<in> [D']\<^bsub>v,n\<^esub>"
  shows "\<exists> u \<in> [D]\<^bsub>v,n\<^esub>. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l',u'\<rangle>" using assms
proof (induction A l D v n l' D' rule: steps_z_dbm.induct)
  case refl thus ?case by fast
next
  case (step A l D v n l' D' l'' D'')
  then obtain u'' where u'': "A \<turnstile> \<langle>l', u''\<rangle> \<rightarrow>* \<langle>l'',u'\<rangle>" "u''\<in>[D']\<^bsub>v,n\<^esub>" by blast
  with step_z_sound[OF step_z_dbm_sound[OF step(1,4)]] obtain u where
    "u \<in> [D]\<^bsub>v,n\<^esub>" "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u''\<rangle>"
  by blast
  with u'' show ?case by blast
qed

lemma steps_z_dbm_complete:
  assumes "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l',u'\<rangle>"
  and "global_clock_numbering A v n"
  and "u \<in> [D]\<^bsub>v,n\<^esub>"
  shows "\<exists> D'. A \<turnstile> \<langle>l, D\<rangle> \<leadsto>*\<^bsub>v,n\<^esub> \<langle>l', D'\<rangle> \<and> u' \<in> [D']\<^bsub>v,n\<^esub>" using assms
proof (induction arbitrary: D rule: steps.induct)
  case refl thus ?case by auto
next
  case (step A l u l' u' l'' u'' D)
  from step_z_dbm_complete[OF step(4,1,5)] obtain D'
  where D': "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n\<^esub> \<langle>l',D'\<rangle>" "u' \<in> [D']\<^bsub>v,n\<^esub>" by auto
  with step(3)[OF step(4)] obtain D'' where
    "A \<turnstile> \<langle>l',D'\<rangle> \<leadsto>*\<^bsub>v,n\<^esub> \<langle>l'',D''\<rangle>" "u'' \<in> [D'']\<^bsub>v,n\<^esub>"
  by blast
  with D' show ?case by blast
qed

end
(*>*)
