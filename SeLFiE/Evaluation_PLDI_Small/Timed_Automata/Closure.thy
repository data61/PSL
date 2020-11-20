theory Closure
  imports Regions
begin

section \<open>Correct Approximation of Zones with \<open>\<alpha>\<close>-regions\<close>

locale AlphaClosure =
  fixes X k \<R> and V :: "('c, t) cval set"
  defines "\<R> \<equiv> {region X I r | I r. valid_region X k I r}"
  defines "V \<equiv> {v . \<forall> x \<in> X. v x \<ge> 0}"
  assumes finite: "finite X"
begin

lemmas set_of_regions_spec = set_of_regions[OF _ _ _ finite, of _ k, folded \<R>_def]
lemmas region_cover_spec = region_cover[of X _ k, folded \<R>_def]
lemmas region_unique_spec = region_unique[of \<R> X k, folded \<R>_def, simplified]
lemmas regions_closed'_spec = regions_closed'[of \<R> X k, folded \<R>_def, simplified]

lemma valid_regions_distinct_spec:
  "R \<in> \<R> \<Longrightarrow> R' \<in> \<R> \<Longrightarrow> v \<in> R \<Longrightarrow> v \<in> R' \<Longrightarrow> R = R'"
unfolding \<R>_def using valid_regions_distinct
by auto (drule valid_regions_distinct, assumption+, simp)+

definition cla ("Closure\<^sub>\<alpha> _" [71] 71)
where
  "cla Z = \<Union> {R \<in> \<R>. R \<inter> Z \<noteq> {}}"


subsubsection \<open>The nice and easy properties proved by Bouyer\<close>

lemma closure_constraint_id:
  "\<forall>(x, m)\<in>collect_clock_pairs g. m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat> \<Longrightarrow> Closure\<^sub>\<alpha> \<lbrace>g\<rbrace> = \<lbrace>g\<rbrace> \<inter> V"
proof goal_cases
  case 1
  show ?case
  proof auto
    fix v assume v: "v \<in> Closure\<^sub>\<alpha> \<lbrace>g\<rbrace>"
    then obtain R where R: "v \<in> R" "R \<in> \<R>" "R \<inter> \<lbrace>g\<rbrace> \<noteq> {}" unfolding cla_def by auto
    with ccompatible[OF 1, folded \<R>_def] show "v \<in> \<lbrace>g\<rbrace>" unfolding ccompatible_def by auto
    from R show "v \<in> V" unfolding V_def \<R>_def by auto
  next
    fix v assume v: "v \<in> \<lbrace>g\<rbrace>" "v \<in> V"
    with region_cover[of X v k, folded \<R>_def] obtain R where "R \<in> \<R>" "v \<in> R" unfolding V_def by auto
    then show "v \<in> Closure\<^sub>\<alpha> \<lbrace>g\<rbrace>" unfolding cla_def using v by auto
  qed
qed

lemma closure_id':
  "Z \<noteq> {} \<Longrightarrow> Z \<subseteq> R \<Longrightarrow> R \<in> \<R> \<Longrightarrow> Closure\<^sub>\<alpha> Z = R"
proof goal_cases
  case 1
  note A = this
  then have "R \<subseteq> Closure\<^sub>\<alpha> Z" unfolding cla_def by auto
  moreover
  { fix R' assume R': "Z \<inter> R' \<noteq> {}" "R' \<in> \<R>" "R \<noteq> R'"
    with A obtain v where "v \<in> R" "v \<in> R'" by auto
    with \<R>_regions_distinct[OF _ A(3) this(1) R'(2-)] \<R>_def have False by auto
  }
  ultimately show ?thesis unfolding cla_def by auto
qed

lemma closure_id:
  "Closure\<^sub>\<alpha> Z \<noteq> {} \<Longrightarrow> Z \<subseteq> R \<Longrightarrow> R \<in> \<R> \<Longrightarrow> Closure\<^sub>\<alpha> Z = R"
proof goal_cases
  case 1
  then have "Z \<noteq> {}" unfolding cla_def by auto
  with 1 closure_id' show ?case by blast
qed

lemma closure_update_mono:
  "Z \<subseteq> V \<Longrightarrow> set r \<subseteq> X \<Longrightarrow> zone_set (Closure\<^sub>\<alpha> Z) r \<subseteq> Closure\<^sub>\<alpha>(zone_set Z r)"
proof -
  assume A: "Z \<subseteq> V" "set r \<subseteq> X"
  let ?U = "{R \<in> \<R>. Z \<inter> R \<noteq> {}}"
  from A(1) region_cover_spec  have "\<forall> v \<in> Z. \<exists> R. R \<in> \<R> \<and> v \<in> R" unfolding V_def by auto
  then have "Z = \<Union> {Z \<inter> R | R. R \<in> ?U}"
  proof (auto, goal_cases)
    case (1 v)
    then obtain R where "R \<in> \<R>" "v \<in> R" by auto
    moreover with 1 have "Z \<inter> R \<noteq> {}" "v \<in> Z \<inter> R" by auto
    ultimately show ?case by auto
  qed
  then obtain U where U: "Z = \<Union> {Z \<inter> R | R. R \<in> U}" "\<forall> R \<in> U. R \<in> \<R>" by blast
  { fix R assume R: "R \<in> U"
    { fix v' assume v': "v' \<in> zone_set (Closure\<^sub>\<alpha> (Z \<inter> R)) r - Closure\<^sub>\<alpha>(zone_set (Z \<inter> R) r)"
      then obtain v where *:
        "v \<in> Closure\<^sub>\<alpha> (Z \<inter> R)" "v' = [r \<rightarrow> 0]v"
      unfolding zone_set_def by auto
      with closure_id[of "Z \<inter> R" R] R U(2) have **:
        "Closure\<^sub>\<alpha> (Z \<inter> R) = R" "Closure\<^sub>\<alpha> (Z \<inter> R) \<in> \<R>"
      by fastforce+
      with region_set'_id[OF _ *(1) finite _ _ A(2), of k 0, folded \<R>_def, OF this(2)]
      have ***: "zone_set R r \<in> \<R>" "[r\<rightarrow>0]v \<in> zone_set R r"
      unfolding zone_set_def region_set'_def by auto
      from * have "Z \<inter> R \<noteq> {}" unfolding cla_def by auto
      then have "zone_set (Z \<inter> R) r \<noteq> {}" unfolding zone_set_def by auto
      from closure_id'[OF this _ ***(1)] have "Closure\<^sub>\<alpha> zone_set (Z \<inter> R) r = zone_set R r"
      unfolding zone_set_def by auto
      with v' **(1) have False by auto
    }
    then have "zone_set (Closure\<^sub>\<alpha> (Z \<inter> R)) r \<subseteq> Closure\<^sub>\<alpha>(zone_set (Z \<inter> R) r)" by auto
  } note Z_i = this
  from U(1) have "Closure\<^sub>\<alpha> Z = \<Union> {Closure\<^sub>\<alpha> (Z \<inter> R) | R. R \<in> U}" unfolding cla_def by auto
  then have "zone_set (Closure\<^sub>\<alpha> Z) r = \<Union> {zone_set (Closure\<^sub>\<alpha> (Z \<inter> R)) r | R. R \<in> U}"
  unfolding zone_set_def by auto
  also have "\<dots> \<subseteq> \<Union> {Closure\<^sub>\<alpha>(zone_set (Z \<inter> R) r) | R. R \<in> U}" using Z_i by auto
  also have "\<dots> = Closure\<^sub>\<alpha> \<Union> {(zone_set (Z \<inter> R) r) | R. R \<in> U}" unfolding cla_def by auto
  also have "\<dots> = Closure\<^sub>\<alpha> zone_set (\<Union> {Z \<inter> R| R. R \<in> U}) r"
  proof goal_cases
    case 1
    have "zone_set (\<Union> {Z \<inter> R| R. R \<in> U}) r = \<Union> {(zone_set (Z \<inter> R) r) | R. R \<in> U}"
    unfolding zone_set_def by auto
    then show ?case by auto
  qed
  finally show "zone_set (Closure\<^sub>\<alpha> Z) r \<subseteq> Closure\<^sub>\<alpha>(zone_set Z r)" using U by simp
qed

lemma SuccI3:
  "R \<in> \<R> \<Longrightarrow> v \<in> R \<Longrightarrow> t \<ge> 0 \<Longrightarrow> (v \<oplus> t) \<in> R' \<Longrightarrow> R' \<in> \<R> \<Longrightarrow> R' \<in> Succ \<R> R"
 apply (intro SuccI2[of \<R> X k, folded \<R>_def, simplified])
    apply assumption+
   apply (intro region_unique[of \<R> X k, folded \<R>_def, simplified, symmetric])
by assumption+

lemma closure_delay_mono:
  "Z \<subseteq> V \<Longrightarrow> (Closure\<^sub>\<alpha> Z)\<^sup>\<up> \<subseteq> Closure\<^sub>\<alpha> (Z\<^sup>\<up>)"
proof
  fix v assume v: "v \<in> (Closure\<^sub>\<alpha> Z)\<^sup>\<up>" and Z: "Z \<subseteq> V"
  then obtain u u' t R where A:
    "u \<in> Closure\<^sub>\<alpha> Z" "v = (u \<oplus> t)" "u \<in> R" "u' \<in> R" "R \<in> \<R>" "u' \<in> Z" "t \<ge> 0"
  unfolding cla_def zone_delay_def by blast
  from A(3,5) have "\<forall> x \<in> X. u x \<ge> 0" unfolding \<R>_def by fastforce
  with region_cover_spec[of v] A(2,7) obtain R' where R':
    "R' \<in> \<R>" "v \<in> R'"
  unfolding cval_add_def by auto
  with set_of_regions_spec[OF A(5,4), OF SuccI3, of u] A obtain t where t:
    "t \<ge> 0" "[u' \<oplus> t]\<^sub>\<R> = R'"
  by auto
  with A have "(u' \<oplus> t) \<in> Z\<^sup>\<up>" unfolding zone_delay_def by auto
  moreover from regions_closed'_spec[OF A(5,4)] t have "(u' \<oplus> t) \<in> R'" by auto
  ultimately have "R' \<inter> (Z\<^sup>\<up>) \<noteq> {}" by auto
  with R' show "v \<in> Closure\<^sub>\<alpha> (Z\<^sup>\<up>)" unfolding cla_def by auto
qed

lemma region_V: "R \<in> \<R> \<Longrightarrow> R \<subseteq> V" using V_def \<R>_def region.cases by auto

lemma closure_V:
  "Closure\<^sub>\<alpha> Z \<subseteq> V"
unfolding cla_def using region_V by auto

lemma closure_V_int:
  "Closure\<^sub>\<alpha> Z = Closure\<^sub>\<alpha> (Z \<inter> V)"
unfolding cla_def using region_V by auto

lemma closure_constraint_mono:
  "Closure\<^sub>\<alpha> g = g \<Longrightarrow> g \<inter> (Closure\<^sub>\<alpha> Z) \<subseteq> Closure\<^sub>\<alpha> (g \<inter> Z)"
unfolding cla_def by auto

lemma closure_constraint_mono':
  assumes "Closure\<^sub>\<alpha> g = g \<inter> V"
  shows "g \<inter> (Closure\<^sub>\<alpha> Z) \<subseteq> Closure\<^sub>\<alpha> (g \<inter> Z)"
proof -
  from assms closure_V_int have "Closure\<^sub>\<alpha> (g \<inter> V) = g \<inter> V" by auto
  from closure_constraint_mono[OF this, of Z] have
    "g \<inter> (V \<inter> Closure\<^sub>\<alpha> Z) \<subseteq> Closure\<^sub>\<alpha> (g \<inter> Z \<inter> V)"
  by (metis Int_assoc Int_commute)
  with closure_V[of Z] closure_V_int[of "g \<inter> Z"] show ?thesis by auto
qed

lemma cla_empty_iff:
  "Z \<subseteq> V \<Longrightarrow> Z = {} \<longleftrightarrow> Closure\<^sub>\<alpha> Z = {}"
unfolding cla_def V_def using region_cover_spec by fast

lemma closure_involutive_aux:
  "U \<subseteq> \<R> \<Longrightarrow> Closure\<^sub>\<alpha> \<Union> U = \<Union> U"
unfolding cla_def using valid_regions_distinct_spec by blast

lemma closure_involutive_aux':
  "\<exists> U. U \<subseteq> \<R> \<and> Closure\<^sub>\<alpha> Z = \<Union> U"
unfolding cla_def by (rule exI[where x = "{R \<in> \<R>. R \<inter> Z \<noteq> {}}"]) auto

lemma closure_involutive:
  "Closure\<^sub>\<alpha> Closure\<^sub>\<alpha> Z = Closure\<^sub>\<alpha> Z"
using closure_involutive_aux closure_involutive_aux' by metis

lemma closure_involutive':
  "Z \<subseteq> Closure\<^sub>\<alpha> W \<Longrightarrow> Closure\<^sub>\<alpha> Z \<subseteq> Closure\<^sub>\<alpha> W"
unfolding cla_def using valid_regions_distinct_spec by fast

lemma closure_subs:
  "Z \<subseteq> V \<Longrightarrow> Z \<subseteq> Closure\<^sub>\<alpha> Z"
unfolding cla_def V_def using region_cover_spec by fast

lemma cla_mono':
  "Z' \<subseteq> V \<Longrightarrow> Z \<subseteq> Z' \<Longrightarrow> Closure\<^sub>\<alpha> Z \<subseteq> Closure\<^sub>\<alpha> Z'"
by (meson closure_involutive' closure_subs subset_trans)

lemma cla_mono:
  "Z \<subseteq> Z' \<Longrightarrow> Closure\<^sub>\<alpha> Z \<subseteq> Closure\<^sub>\<alpha> Z'"
using closure_V_int cla_mono'[of "Z' \<inter> V" "Z \<inter> V"] by auto


section \<open>A New Zone Semantics Abstracting with \<open>Closure\<^sub>\<alpha>\<close>\<close>

subsection \<open>Single step\<close>

inductive step_z_alpha ::
  "('a, 'c, t, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^sub>\<alpha> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  step_alpha: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha> \<langle>l', Closure\<^sub>\<alpha> Z'\<rangle>"

inductive_cases[elim!]: "A \<turnstile> \<langle>l, u\<rangle> \<leadsto>\<^sub>\<alpha> \<langle>l',u'\<rangle>"

declare step_z_alpha.intros[intro]

lemma up_V: "Z \<subseteq> V \<Longrightarrow> Z\<^sup>\<up> \<subseteq> V"
unfolding V_def zone_delay_def cval_add_def by auto

lemma reset_V: "Z \<subseteq> V \<Longrightarrow> (zone_set Z r) \<subseteq> V"
unfolding V_def unfolding zone_set_def by (induction r, auto)

lemma step_z_V: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z'\<rangle> \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> Z' \<subseteq> V"
 apply (induction rule: step_z.induct)
  apply (rule le_infI1)
  apply (rule up_V)
  apply blast
 apply (rule le_infI1)
 apply (rule reset_V)
by blast


text \<open>Single-step soundness and completeness follows trivially from \<open>cla_empty_iff\<close>.\<close>

lemma step_z_alpha_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha> \<langle>l',Z'\<rangle> \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> Z' \<noteq> {} \<Longrightarrow> \<exists> Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z''\<rangle> \<and> Z'' \<noteq> {}"
 apply (induction rule: step_z_alpha.induct)
  apply (frule step_z_V)
  apply assumption
 apply (rotate_tac 3)
 apply (drule cla_empty_iff)
by auto

lemma step_z_alpha_complete:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z'\<rangle> \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> Z' \<noteq> {} \<Longrightarrow> \<exists> Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha> \<langle>l',Z''\<rangle> \<and> Z'' \<noteq> {}"
 apply (frule step_z_V)
  apply assumption
 apply (rotate_tac 3)
 apply (drule cla_empty_iff)
by auto

lemma zone_set_mono:
  "A \<subseteq> B \<Longrightarrow> zone_set A r \<subseteq> zone_set B r"
unfolding zone_set_def by auto

lemma zone_delay_mono:
  "A \<subseteq> B \<Longrightarrow> A\<^sup>\<up> \<subseteq> B\<^sup>\<up>"
unfolding zone_delay_def by auto


subsection \<open>Multi step\<close>

inductive
  steps_z_alpha :: "('a, 'c, t, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  refl: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l, Z\<rangle>" |
  step: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^sub>\<alpha> \<langle>l'', Z''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l'', Z''\<rangle>"

declare steps_z_alpha.intros[intro]

lemma subset_int_mono: "A \<subseteq> B \<Longrightarrow> A \<inter> C \<subseteq> B \<inter> C" by blast

text \<open>P. Bouyer's calculation for @{term "Post(Closure\<^sub>\<alpha> Z, e) \<subseteq> Closure\<^sub>\<alpha>(Post (Z, e))"}\<close>
text \<open>This is now obsolete as we argue solely with monotonicty of \<open>steps_z\<close> w.r.t \<open>Closure\<^sub>\<alpha>\<close>\<close>

lemma calc:
  "valid_abstraction A X k \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> A \<turnstile> \<langle>l, Closure\<^sub>\<alpha> Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>
  \<Longrightarrow> \<exists>Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha> \<langle>l', Z''\<rangle> \<and> Z' \<subseteq> Z''"
proof (cases rule: step_z.cases, assumption, goal_cases)
  case 1
  note A = this
  from A(1) have "\<forall>(x, m)\<in>clkp_set A. m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
  by (fastforce elim: valid_abstraction.cases)
  then have "\<forall>(x, m)\<in>collect_clock_pairs (inv_of A l). m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
  unfolding clkp_set_def collect_clki_def inv_of_def by auto
  from closure_constraint_id[OF this] have *: "Closure\<^sub>\<alpha> \<lbrace>inv_of A l\<rbrace> = \<lbrace>inv_of A l\<rbrace> \<inter> V" .
  from closure_constraint_mono'[OF *, of Z] have
    "(Closure\<^sub>\<alpha> Z) \<inter> {u. u \<turnstile> inv_of A l} \<subseteq> Closure\<^sub>\<alpha> (Z \<inter> {u. u \<turnstile> inv_of A l})"
  unfolding ccval_def by (subst Int_commute) (subst (asm) (2) Int_commute, assumption)
  moreover have "\<dots>\<^sup>\<up> \<subseteq> Closure\<^sub>\<alpha> ((Z \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<up>)" using A(2) by (blast intro!: closure_delay_mono)
  ultimately have "Z' \<subseteq> Closure\<^sub>\<alpha> ((Z \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l})"
  using closure_constraint_mono'[OF *, of "(Z \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<up>"] unfolding ccval_def
   apply (subst A(5))
   apply (subst (asm) (5 7) Int_commute)
   apply (rule subset_trans)
    defer
    apply assumption
   apply (subst subset_int_mono)
    defer
    apply rule
   apply (rule subset_trans)
    defer
    apply assumption
   apply (rule zone_delay_mono)
   apply assumption
  done
  with A(4,3) show ?thesis by auto
next
  case (2 g a r)
  note A = this
  from A(1) have *:
    "\<forall>(x, m)\<in>clkp_set A. m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
    "collect_clkvt (trans_of A) \<subseteq> X"
    "finite X"
  by (auto elim: valid_abstraction.cases)
  from *(1) A(5) have "\<forall>(x, m)\<in>collect_clock_pairs (inv_of A l'). m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
  unfolding clkp_set_def collect_clki_def inv_of_def by fastforce
  from closure_constraint_id[OF this] have **: "Closure\<^sub>\<alpha> \<lbrace>inv_of A l'\<rbrace> = \<lbrace>inv_of A l'\<rbrace> \<inter> V" .
  from *(1) A(5) have "\<forall>(x, m)\<in>collect_clock_pairs g. m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
  unfolding clkp_set_def collect_clkt_def by fastforce
  from closure_constraint_id[OF this] have ***: "Closure\<^sub>\<alpha> \<lbrace>g\<rbrace> = \<lbrace>g\<rbrace> \<inter> V" .
  from *(2) A(5) have ****: "set r \<subseteq> X" unfolding collect_clkvt_def by fastforce
  from closure_constraint_mono'[OF ***, of Z] have
    "(Closure\<^sub>\<alpha> Z) \<inter> {u. u \<turnstile> g} \<subseteq> Closure\<^sub>\<alpha> (Z \<inter> {u. u \<turnstile> g})" unfolding ccval_def
  by (subst Int_commute) (subst (asm) (2) Int_commute, assumption)
  moreover have "zone_set \<dots> r \<subseteq> Closure\<^sub>\<alpha> (zone_set (Z \<inter> {u. u \<turnstile> g}) r)" using **** A(2)
  by (intro closure_update_mono, auto)
  ultimately have "Z' \<subseteq> Closure\<^sub>\<alpha> (zone_set (Z \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'})"
  using closure_constraint_mono'[OF **, of "zone_set (Z \<inter> {u. u \<turnstile> g}) r"] unfolding ccval_def
    apply (subst A(4))
    apply (subst (asm) (5 7) Int_commute)
    apply (rule subset_trans)
     defer
     apply assumption
    apply (subst subset_int_mono)
     defer
     apply rule
    apply (rule subset_trans)
     defer
     apply assumption
    apply (rule zone_set_mono)
    apply assumption
  done
  with A(5) show ?thesis by auto
qed


text \<open>
  Turning P. Bouyers argument for multiple steps into an inductive proof is not direct.
  With this initial argument we can get to a point where the induction hypothesis is applicable.
  This breaks the "information hiding" induced by the different variants of steps.
\<close>

lemma steps_z_alpha_closure_involutive'_aux:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z'\<rangle> \<Longrightarrow> Closure\<^sub>\<alpha> Z \<subseteq> Closure\<^sub>\<alpha> W \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> Z \<subseteq> V
  \<Longrightarrow> \<exists> W'. A \<turnstile> \<langle>l, W\<rangle> \<leadsto> \<langle>l',W'\<rangle> \<and> Closure\<^sub>\<alpha> Z' \<subseteq> Closure\<^sub>\<alpha> W'"
proof (induction rule: step_z.induct)
  case A: (step_t_z A l Z)
  let ?Z' = "(Z \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}"
  let ?W' = "(W \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}"
  from \<R>_def have \<R>_def': "\<R> = {region X I r |I r. valid_region X k I r}" by simp
  have step_z: "A \<turnstile> \<langle>l, W\<rangle> \<leadsto> \<langle>l,?W'\<rangle>" by auto
  moreover have "Closure\<^sub>\<alpha> ?Z' \<subseteq> Closure\<^sub>\<alpha> ?W'"
  proof
    fix v assume v: "v \<in> Closure\<^sub>\<alpha> ?Z'"
    then obtain R' v' where 1: "R' \<in> \<R>" "v \<in> R'" "v' \<in> R'" "v' \<in> ?Z'" unfolding cla_def by auto
    then obtain u d where
      "u \<in> Z" and v': "v' = u \<oplus> d" "u \<turnstile> inv_of A l" "u \<oplus> d \<turnstile> inv_of A l" "0 \<le> d"
    unfolding zone_delay_def by blast
    with closure_subs[OF A(3)] A(1) obtain u' R where u': "u' \<in> W" "u \<in> R" "u' \<in> R" "R \<in> \<R>"
    unfolding cla_def by blast
    then have "\<forall>x\<in>X. 0 \<le> u x" unfolding \<R>_def by fastforce
    from region_cover'[OF \<R>_def' this] have R: "[u]\<^sub>\<R> \<in> \<R>" "u \<in> [u]\<^sub>\<R>" by auto
    from SuccI2[OF \<R>_def' this(2,1) v'(4), of "[v']\<^sub>\<R>"] v'(1) have v'1:
      "[v']\<^sub>\<R> \<in> Succ \<R> ([u]\<^sub>\<R>)" "[v']\<^sub>\<R> \<in> \<R>"
    by auto
    from regions_closed'_spec[OF R(1,2) v'(4)] v'(1) have v'2: "v' \<in> [v']\<^sub>\<R>" by simp
    from A(2) have *:
      "\<forall>(x, m)\<in>clkp_set A. m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
      "collect_clkvt (trans_of A) \<subseteq> X"
      "finite X"
    by (auto elim: valid_abstraction.cases)
    from *(1) u'(2) have "\<forall>(x, m)\<in>collect_clock_pairs (inv_of A l). m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
    unfolding clkp_set_def collect_clki_def inv_of_def by fastforce
    from ccompatible[OF this, folded \<R>_def'] v'1(2) v'2 v'(1,2,3) R have 3:
      "[v']\<^sub>\<R> \<subseteq> \<lbrace>inv_of A l\<rbrace>" "([u]\<^sub>\<R>) \<subseteq> \<lbrace>inv_of A l\<rbrace>"
    unfolding ccompatible_def ccval_def by auto
    with A v'1 R(1) \<R>_def' have "A,\<R> \<turnstile> \<langle>l, ([u]\<^sub>\<R>)\<rangle> \<leadsto> \<langle>l,([v']\<^sub>\<R>)\<rangle>" by auto
    with valid_regions_distinct_spec[OF v'1(2) 1(1) v'2 1(3)] region_unique_spec[OF u'(2,4)]
    have step_r: "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto> \<langle>l, R'\<rangle>" and 2: "[v']\<^sub>\<R> = R'" "[u]\<^sub>\<R> = R" by auto
    from set_of_regions_spec[OF u'(4,3)] v'1(1) 2 obtain t where t: "t \<ge> 0" "[u' \<oplus> t]\<^sub>\<R> = R'" by auto
    with regions_closed'_spec[OF u'(4,3) this(1)] step_t_r(1) have *: "u' \<oplus> t \<in> R'" by auto
    with t(1) 3 2 u'(1,3) have "A \<turnstile> \<langle>l, u'\<rangle> \<rightarrow> \<langle>l, u' \<oplus> t\<rangle>" "u' \<oplus> t \<in> ?W'"
    unfolding zone_delay_def ccval_def by auto
    with * 1(1) have "R' \<subseteq> Closure\<^sub>\<alpha> ?W'" unfolding cla_def by auto
    with 1(2) show "v \<in> Closure\<^sub>\<alpha> ?W'" ..
  qed
  ultimately show ?case by auto
next
  case A: (step_a_z A l g a r l' Z)
  let ?Z' = "zone_set (Z \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"
  let ?W' = "zone_set (W \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"
  from \<R>_def have \<R>_def': "\<R> = {region X I r |I r. valid_region X k I r}" by simp
  from A(1) have step_z: "A \<turnstile> \<langle>l, W\<rangle> \<leadsto> \<langle>l',?W'\<rangle>" by auto
  moreover have "Closure\<^sub>\<alpha> ?Z' \<subseteq> Closure\<^sub>\<alpha> ?W'"
  proof
    fix v assume v: "v \<in> Closure\<^sub>\<alpha> ?Z'"
    then obtain R' v' where 1: "R' \<in> \<R>" "v \<in> R'" "v' \<in> R'" "v' \<in> ?Z'" unfolding cla_def by auto
    then obtain u where
      "u \<in> Z" and v': "v' = [r\<rightarrow>0]u" "u \<turnstile> g" "v' \<turnstile> inv_of A l'"
    unfolding zone_set_def by blast
    let ?R'= "region_set' (([u]\<^sub>\<R>) \<inter> {u. u \<turnstile> g}) r 0 \<inter> {u. u \<turnstile> inv_of A l'}"
    from \<open>u \<in> Z\<close> closure_subs[OF A(4)] A(2) obtain u' R where u': "u' \<in> W" "u \<in> R" "u' \<in> R" "R \<in> \<R>"
    unfolding cla_def by blast
    then have "\<forall>x\<in>X. 0 \<le> u x" unfolding \<R>_def by fastforce
    from region_cover'[OF \<R>_def' this] have R: "[u]\<^sub>\<R> \<in> \<R>" "u \<in> [u]\<^sub>\<R>" by auto
    from step_r_complete_aux[OF \<R>_def' A(3) this(2,1) A(1) v'(2)] v'
    have *: "[u]\<^sub>\<R> = ([u]\<^sub>\<R>) \<inter> {u. u \<turnstile> g}" "?R' = region_set' ([u]\<^sub>\<R>) r 0" "?R' \<in> \<R>" by auto
    from \<R>_def' A(3) have "collect_clkvt (trans_of A) \<subseteq> X" "finite X"
    by (auto elim: valid_abstraction.cases)
    with A(1) have r: "set r \<subseteq> X" unfolding collect_clkvt_def by fastforce
    from * v'(1) R(2) have "v' \<in> ?R'" unfolding region_set'_def by auto
    moreover have "A,\<R> \<turnstile> \<langle>l,([u]\<^sub>\<R>)\<rangle> \<leadsto> \<langle>l',?R'\<rangle>" using R(1) \<R>_def' A(1,3) v'(2) by auto
    thm valid_regions_distinct_spec
    with valid_regions_distinct_spec[OF *(3) 1(1) \<open>v' \<in> ?R'\<close> 1(3)] region_unique_spec[OF u'(2,4)]
    have 2: "?R' = R'" "[u]\<^sub>\<R> = R" by auto
    with * u' have *: "[r\<rightarrow>0]u' \<in> ?R'" "u' \<turnstile> g" "[r\<rightarrow>0]u' \<turnstile> inv_of A l'"
    unfolding region_set'_def by auto
    with A(1) have "A \<turnstile> \<langle>l, u'\<rangle> \<rightarrow> \<langle>l',[r\<rightarrow>0]u'\<rangle>" apply (intro step.intros(1)) apply rule by auto
    moreover from * u'(1) have "[r\<rightarrow>0]u' \<in> ?W'" unfolding zone_set_def by auto
    ultimately have "R' \<subseteq> Closure\<^sub>\<alpha> ?W'" using *(1) 1(1) 2(1) unfolding cla_def by auto
    with 1(2) show "v \<in> Closure\<^sub>\<alpha> ?W'" ..
  qed
  ultimately show ?case by meson
qed

lemma steps_z_alpha_closure_involutive'_aux':
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z'\<rangle> \<Longrightarrow> Closure\<^sub>\<alpha> Z \<subseteq> Closure\<^sub>\<alpha> W \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> W \<subseteq> Z
  \<Longrightarrow> \<exists> W'. A \<turnstile> \<langle>l, W\<rangle> \<leadsto> \<langle>l',W'\<rangle> \<and> Closure\<^sub>\<alpha> Z' \<subseteq> Closure\<^sub>\<alpha> W' \<and> W' \<subseteq> Z'"
proof (induction rule: step_z.induct)
  case A: (step_t_z A l Z)
  let ?Z' = "(Z \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}"
  let ?W' = "(W \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}"
  from \<R>_def have \<R>_def': "\<R> = {region X I r |I r. valid_region X k I r}" by simp
  have step_z: "A \<turnstile> \<langle>l, W\<rangle> \<leadsto> \<langle>l,?W'\<rangle>" by auto
  moreover have "Closure\<^sub>\<alpha> ?Z' \<subseteq> Closure\<^sub>\<alpha> ?W'"
  proof
    fix v assume v: "v \<in> Closure\<^sub>\<alpha> ?Z'"
    then obtain R' v' where 1: "R' \<in> \<R>" "v \<in> R'" "v' \<in> R'" "v' \<in> ?Z'" unfolding cla_def by auto
    then obtain u d where
      "u \<in> Z" and v': "v' = u \<oplus> d" "u \<turnstile> inv_of A l" "u \<oplus> d \<turnstile> inv_of A l" "0 \<le> d"
    unfolding zone_delay_def by blast
    with closure_subs[OF A(3)] A(1) obtain u' R where u': "u' \<in> W" "u \<in> R" "u' \<in> R" "R \<in> \<R>"
    unfolding cla_def by blast
    then have "\<forall>x\<in>X. 0 \<le> u x" unfolding \<R>_def by fastforce
    from region_cover'[OF \<R>_def' this] have R: "[u]\<^sub>\<R> \<in> \<R>" "u \<in> [u]\<^sub>\<R>" by auto
    from SuccI2[OF \<R>_def' this(2,1) v'(4), of "[v']\<^sub>\<R>"] v'(1) have v'1:
      "[v']\<^sub>\<R> \<in> Succ \<R> ([u]\<^sub>\<R>)" "[v']\<^sub>\<R> \<in> \<R>"
    by auto
    from regions_closed'_spec[OF R(1,2) v'(4)] v'(1) have v'2: "v' \<in> [v']\<^sub>\<R>" by simp
    from A(2) have *:
      "\<forall>(x, m)\<in>clkp_set A. m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
      "collect_clkvt (trans_of A) \<subseteq> X"
      "finite X"
    by (auto elim: valid_abstraction.cases)
    from *(1) u'(2) have "\<forall>(x, m)\<in>collect_clock_pairs (inv_of A l). m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
    unfolding clkp_set_def collect_clki_def inv_of_def by fastforce
    from ccompatible[OF this, folded \<R>_def'] v'1(2) v'2 v'(1,2,3) R have 3:
      "[v']\<^sub>\<R> \<subseteq> \<lbrace>inv_of A l\<rbrace>" "([u]\<^sub>\<R>) \<subseteq> \<lbrace>inv_of A l\<rbrace>"
    unfolding ccompatible_def ccval_def by auto
    with A v'1 R(1) \<R>_def' have "A,\<R> \<turnstile> \<langle>l, ([u]\<^sub>\<R>)\<rangle> \<leadsto> \<langle>l,([v']\<^sub>\<R>)\<rangle>" by auto
    with valid_regions_distinct_spec[OF v'1(2) 1(1) v'2 1(3)] region_unique_spec[OF u'(2,4)]
    have step_r: "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto> \<langle>l, R'\<rangle>" and 2: "[v']\<^sub>\<R> = R'" "[u]\<^sub>\<R> = R" by auto
    from set_of_regions_spec[OF u'(4,3)] v'1(1) 2 obtain t where t: "t \<ge> 0" "[u' \<oplus> t]\<^sub>\<R> = R'" by auto
    with regions_closed'_spec[OF u'(4,3) this(1)] step_t_r(1) have *: "u' \<oplus> t \<in> R'" by auto
    with t(1) 3 2 u'(1,3) have "A \<turnstile> \<langle>l, u'\<rangle> \<rightarrow> \<langle>l, u' \<oplus> t\<rangle>" "u' \<oplus> t \<in> ?W'"
    unfolding zone_delay_def ccval_def by auto
    with * 1(1) have "R' \<subseteq> Closure\<^sub>\<alpha> ?W'" unfolding cla_def by auto
    with 1(2) show "v \<in> Closure\<^sub>\<alpha> ?W'" ..
  qed
  moreover have "?W' \<subseteq> ?Z'" using \<open>W \<subseteq> Z\<close> unfolding zone_delay_def by auto
  ultimately show ?case by auto
next
  case A: (step_a_z A l g a r l' Z)
  let ?Z' = "zone_set (Z \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"
  let ?W' = "zone_set (W \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"
  from \<R>_def have \<R>_def': "\<R> = {region X I r |I r. valid_region X k I r}" by simp
  from A(1) have step_z: "A \<turnstile> \<langle>l, W\<rangle> \<leadsto> \<langle>l',?W'\<rangle>" by auto
  moreover have "Closure\<^sub>\<alpha> ?Z' \<subseteq> Closure\<^sub>\<alpha> ?W'"
  proof
    fix v assume v: "v \<in> Closure\<^sub>\<alpha> ?Z'"
    then obtain R' v' where 1: "R' \<in> \<R>" "v \<in> R'" "v' \<in> R'" "v' \<in> ?Z'" unfolding cla_def by auto
    then obtain u where
      "u \<in> Z" and v': "v' = [r\<rightarrow>0]u" "u \<turnstile> g" "v' \<turnstile> inv_of A l'"
    unfolding zone_set_def by blast
    let ?R'= "region_set' (([u]\<^sub>\<R>) \<inter> {u. u \<turnstile> g}) r 0 \<inter> {u. u \<turnstile> inv_of A l'}"
    from \<open>u \<in> Z\<close> closure_subs[OF A(4)] A(2) obtain u' R where u': "u' \<in> W" "u \<in> R" "u' \<in> R" "R \<in> \<R>"
    unfolding cla_def by blast
    then have "\<forall>x\<in>X. 0 \<le> u x" unfolding \<R>_def by fastforce
    from region_cover'[OF \<R>_def' this] have R: "[u]\<^sub>\<R> \<in> \<R>" "u \<in> [u]\<^sub>\<R>" by auto
    from step_r_complete_aux[OF \<R>_def' A(3) this(2,1) A(1) v'(2)] v'
    have *: "[u]\<^sub>\<R> = ([u]\<^sub>\<R>) \<inter> {u. u \<turnstile> g}" "?R' = region_set' ([u]\<^sub>\<R>) r 0" "?R' \<in> \<R>" by auto
    from \<R>_def' A(3) have "collect_clkvt (trans_of A) \<subseteq> X" "finite X"
    by (auto elim: valid_abstraction.cases)
    with A(1) have r: "set r \<subseteq> X" unfolding collect_clkvt_def by fastforce
    from * v'(1) R(2) have "v' \<in> ?R'" unfolding region_set'_def by auto
    moreover have "A,\<R> \<turnstile> \<langle>l,([u]\<^sub>\<R>)\<rangle> \<leadsto> \<langle>l',?R'\<rangle>" using R(1) \<R>_def' A(1,3) v'(2) by auto
    thm valid_regions_distinct_spec
    with valid_regions_distinct_spec[OF *(3) 1(1) \<open>v' \<in> ?R'\<close> 1(3)] region_unique_spec[OF u'(2,4)]
    have 2: "?R' = R'" "[u]\<^sub>\<R> = R" by auto
    with * u' have *: "[r\<rightarrow>0]u' \<in> ?R'" "u' \<turnstile> g" "[r\<rightarrow>0]u' \<turnstile> inv_of A l'"
    unfolding region_set'_def by auto
    with A(1) have "A \<turnstile> \<langle>l, u'\<rangle> \<rightarrow> \<langle>l',[r\<rightarrow>0]u'\<rangle>" apply (intro step.intros(1)) apply rule by auto
    moreover from * u'(1) have "[r\<rightarrow>0]u' \<in> ?W'" unfolding zone_set_def by auto
    ultimately have "R' \<subseteq> Closure\<^sub>\<alpha> ?W'" using *(1) 1(1) 2(1) unfolding cla_def by auto
    with 1(2) show "v \<in> Closure\<^sub>\<alpha> ?W'" ..
  qed
  moreover have "?W' \<subseteq> ?Z'" using \<open>W \<subseteq> Z\<close> unfolding zone_set_def by auto
  ultimately show ?case by meson
qed

lemma steps_z_alt:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l',Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto> \<langle>l'',Z''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l'',Z''\<rangle>"
by (induction rule: steps_z.induct) auto

lemma steps_z_alpha_V: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l',Z'\<rangle> \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> Z' \<subseteq> V"
apply (induction rule: steps_z_alpha.induct) using closure_V by auto

lemma steps_z_alpha_closure_involutive':
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l',Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto> \<langle>l'',Z''\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> Z \<subseteq> V
  \<Longrightarrow> \<exists> Z'''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l'',Z'''\<rangle> \<and> Closure\<^sub>\<alpha> Z'' \<subseteq> Closure\<^sub>\<alpha> Z''' \<and> Z''' \<subseteq> Z''"
proof (induction A l Z l' Z' arbitrary: Z'' l'' rule: steps_z_alpha.induct, goal_cases)
  case refl from this(1) show ?case by blast
next
  case A: (2 A l Z l' Z' l'' Z'' Z''a l''a)
  from A(3) obtain \<Z> where Z'': "Z'' = Closure\<^sub>\<alpha> \<Z>" "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto> \<langle>l'',\<Z>\<rangle>" by auto
  from A(2)[OF Z''(2) A(5,6)] obtain Z''' where Z''':
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l'',Z'''\<rangle>" "Closure\<^sub>\<alpha> \<Z> \<subseteq> Closure\<^sub>\<alpha> Z'''" "Z''' \<subseteq> \<Z>"
  by auto
  from closure_subs have *:
    "Z''' \<subseteq> Closure\<^sub>\<alpha> \<Z>"
  by (metis A(1,6) Z'''(3) Z''(2) step_z_V steps_z_alpha_V subset_trans) 
  from A(4) Z'' have "A \<turnstile> \<langle>l'', Closure\<^sub>\<alpha> \<Z>\<rangle> \<leadsto> \<langle>l''a,Z''a\<rangle>" by auto
  from steps_z_alpha_closure_involutive'_aux'[OF this(1) _ A(5) closure_V *] Z'''(2,3) obtain W'
    where ***: "A \<turnstile> \<langle>l'', Z'''\<rangle> \<leadsto> \<langle>l''a,W'\<rangle>" "Closure\<^sub>\<alpha> Z''a \<subseteq> Closure\<^sub>\<alpha> W'" "W' \<subseteq> Z''a"
  by (auto simp: closure_involutive)
  with Z'''(1) have "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l''a,W'\<rangle>" by (blast intro: steps_z_alt)
  with ***(2,3) show ?case by blast
qed

text \<open>Old proof using Bouyer's calculation\<close>
lemma steps_z_alpha_closure_involutive'':
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l',Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto> \<langle>l'',Z''\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> Z \<subseteq> V
  \<Longrightarrow> \<exists> Z'''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l'',Z'''\<rangle> \<and> Closure\<^sub>\<alpha> Z'' \<subseteq> Closure\<^sub>\<alpha> Z'''"
proof (induction A l Z l' Z' arbitrary: Z'' l'' rule: steps_z_alpha.induct, goal_cases)
  case refl from this(1) show ?case by blast
next
  case A: (2 A l Z l' Z' l'' Z'' Z''a l''a)
  from A(3) obtain \<Z> where Z'': "Z'' = Closure\<^sub>\<alpha> \<Z>" "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto> \<langle>l'',\<Z>\<rangle>" by auto
  from A(2)[OF Z''(2) A(5,6)] obtain Z''' where Z''':
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l'',Z'''\<rangle>" "Closure\<^sub>\<alpha> \<Z> \<subseteq> Closure\<^sub>\<alpha> Z'''"
  by auto
  from steps_z_alpha_V[OF A(1,6)] step_z_V[OF Z''(2)] have *: "\<Z> \<subseteq> V" by blast
  from A Z'' have "A \<turnstile> \<langle>l'', Closure\<^sub>\<alpha> \<Z>\<rangle> \<leadsto> \<langle>l''a,Z''a\<rangle>" by auto
  from calc[OF A(5) * this] obtain \<Z>' where **:
    "A \<turnstile> \<langle>l'', \<Z>\<rangle> \<leadsto> \<langle>l''a,\<Z>'\<rangle>" "Z''a \<subseteq> Closure\<^sub>\<alpha> \<Z>'"
  by auto
  from steps_z_alpha_closure_involutive'_aux[OF this(1) Z'''(2) A(5) *] obtain W' where ***:
    "A \<turnstile> \<langle>l'', Z'''\<rangle> \<leadsto> \<langle>l''a,W'\<rangle>" "Closure\<^sub>\<alpha> \<Z>' \<subseteq> Closure\<^sub>\<alpha> W'"
  by auto
  with Z'''(1) have "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l''a,W'\<rangle>" by (blast intro: steps_z_alt)
  with closure_involutive'[OF **(2)] ***(2) show ?case by blast
qed

lemma steps_z_alpha_closure_involutive:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l',Z'\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> Z \<subseteq> V
  \<Longrightarrow> \<exists> Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l',Z''\<rangle> \<and> Closure\<^sub>\<alpha> Z' \<subseteq> Closure\<^sub>\<alpha> Z'' \<and> Z'' \<subseteq> Z'"
proof (induction A l Z l' Z' rule: steps_z_alpha.induct)
  case refl show ?case by blast
next
  case 2: (step A l Z l' Z' l'' Z'')
  then obtain Z''a where *: "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto> \<langle>l'',Z''a\<rangle>" "Z'' = Closure\<^sub>\<alpha> Z''a" by auto
  from steps_z_alpha_closure_involutive'[OF 2(1) this(1) 2(4,5)] obtain Z''' where Z''':
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l'',Z'''\<rangle>" "Closure\<^sub>\<alpha> Z''a \<subseteq> Closure\<^sub>\<alpha> Z'''" "Z''' \<subseteq> Z''a" by blast
  have "Z''' \<subseteq> Z''" by (metis *(1,2) 2(1,5) Z'''(3) closure_subs step_z_V steps_z_alpha_V subset_trans) 
  with * closure_involutive Z''' show ?case by auto
qed

lemma steps_z_V:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l',Z'\<rangle> \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> Z' \<subseteq> V"
apply (induction rule: steps_z.induct)
  apply blast
using step_z_V by metis

lemma steps_z_alpha_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l',Z'\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> Z' \<noteq> {}
  \<Longrightarrow> \<exists> Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l',Z''\<rangle> \<and> Z'' \<noteq> {} \<and> Z'' \<subseteq> Z'"
proof goal_cases
  case 1
  from steps_z_alpha_closure_involutive[OF 1(1-3)] obtain Z'' where
    Z'': "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l',Z''\<rangle>" "Closure\<^sub>\<alpha> Z' \<subseteq> Closure\<^sub>\<alpha> Z''" "Z'' \<subseteq> Z'"
    by blast
  with 1(4) cla_empty_iff[OF steps_z_alpha_V[OF 1(1)], OF 1(3)]
    cla_empty_iff[OF steps_z_V, OF this(1) 1(3)] have "Z'' \<noteq> {}" by auto
  with Z'' show ?case by auto
qed

lemma step_z_mono:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z'\<rangle> \<Longrightarrow> Z \<subseteq> W \<Longrightarrow> \<exists> W'. A \<turnstile> \<langle>l, W\<rangle> \<leadsto> \<langle>l',W'\<rangle> \<and> Z' \<subseteq> W'"
proof (cases rule: step_z.cases, assumption, goal_cases)
  case A: 1
  let ?W' = "(W \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}"
  from A have "A \<turnstile> \<langle>l, W\<rangle> \<leadsto> \<langle>l',?W'\<rangle>" by auto
  moreover have "Z' \<subseteq> ?W'"
    apply (subst A(4))
    apply (rule subset_int_mono)
    apply (rule zone_delay_mono)
    apply (rule subset_int_mono)
    apply (rule A(2))
  done
  ultimately show ?thesis by auto
next
  case A: (2 g a r)
  let ?W' = "zone_set (W \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"
  from A have "A \<turnstile> \<langle>l, W\<rangle> \<leadsto> \<langle>l',?W'\<rangle>" by auto
  moreover have "Z' \<subseteq> ?W'"
    apply (subst A(3))
    apply (rule subset_int_mono)
    apply (rule zone_set_mono)
    apply (rule subset_int_mono)
    apply (rule A(2))
  done
  ultimately show ?thesis by auto
qed

lemma step_z_alpha_mono:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha> \<langle>l',Z'\<rangle> \<Longrightarrow> Z \<subseteq> W \<Longrightarrow> W \<subseteq> V \<Longrightarrow> \<exists> W'. A \<turnstile> \<langle>l, W\<rangle> \<leadsto>\<^sub>\<alpha> \<langle>l',W'\<rangle> \<and> Z' \<subseteq> W'"
proof goal_cases
  case 1
  then obtain Z'' where *: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z''\<rangle>" "Z' = Closure\<^sub>\<alpha> Z''" by auto
  from step_z_mono[OF this(1) 1(2)] obtain W' where "A \<turnstile> \<langle>l, W\<rangle> \<leadsto> \<langle>l',W'\<rangle>" "Z'' \<subseteq> W'" by auto
  moreover with *(2) have "Z' \<subseteq> Closure\<^sub>\<alpha> W'" unfolding cla_def by auto
  ultimately show ?case by blast
qed

lemma steps_z_alpha_mono:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l',Z'\<rangle> \<Longrightarrow> Z \<subseteq> W \<Longrightarrow> W \<subseteq> V \<Longrightarrow> \<exists> W'. A \<turnstile> \<langle>l, W\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l',W'\<rangle> \<and> Z' \<subseteq> W'"
proof (induction rule: steps_z_alpha.induct, goal_cases)
  case refl then show ?case by auto
next
  case (2 A l Z l' Z' l'' Z'')
  then obtain W' where "A \<turnstile> \<langle>l, W\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l',W'\<rangle>" "Z' \<subseteq> W'" by auto
  with step_z_alpha_mono[OF 2(3) this(2) steps_z_alpha_V[OF this(1) 2(5)]]
  show ?case by blast
qed

lemma steps_z_alpha_alt:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha> \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l'', Z''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l'', Z''\<rangle>"
by (rotate_tac, induction rule: steps_z_alpha.induct) blast+

lemma steps_z_alpha_complete:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l',Z'\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> Z' \<noteq> {}
  \<Longrightarrow> \<exists> Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l',Z''\<rangle> \<and> Z' \<subseteq> Z''"
proof (induction rule: steps_z.induct, goal_cases)
  case refl with cla_empty_iff show ?case by blast
next
  case (2 A l Z l' Z' l'' Z'')
  with step_z_V[OF this(1,5)] obtain Z''' where "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l'',Z'''\<rangle>" "Z'' \<subseteq> Z'''" by blast
  with steps_z_alpha_mono[OF this(1) closure_subs[OF step_z_V[OF 2(1,5)]] closure_V]
  obtain W' where "A \<turnstile> \<langle>l', Closure\<^sub>\<alpha> Z'\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l'',W'\<rangle>" " Z'' \<subseteq> W'" by auto
  moreover with 2(1) have "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l'',W'\<rangle>" by (auto intro: steps_z_alpha_alt)
  ultimately show ?case by auto
qed

lemma steps_z_alpha_complete':
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l',Z'\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> Z' \<noteq> {}
  \<Longrightarrow> \<exists> Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l',Z''\<rangle> \<and> Z'' \<noteq> {}"
using steps_z_alpha_complete by fast

end

end
