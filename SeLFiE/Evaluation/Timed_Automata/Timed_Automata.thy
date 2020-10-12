theory Timed_Automata
  imports Main
begin

chapter \<open>Basic Definitions and Semantics\<close>

section \<open>Time\<close>

class time = linordered_ab_group_add +
  assumes dense: "x < y \<Longrightarrow> \<exists>z. x < z \<and> z < y"
  assumes non_trivial: "\<exists> x. x \<noteq> 0"

begin

lemma non_trivial_neg: "\<exists> x. x < 0"
proof -
  from non_trivial obtain x where "x \<noteq> 0" by auto
  then show ?thesis
  proof (cases "x < 0", auto, goal_cases)
    case 1
    then have "x > 0" by auto
    then have "(-x) < 0" by auto
    then show ?case by blast
  qed
qed

end

datatype ('c, 't :: time) cconstraint =
  AND "('c, 't) cconstraint" "('c, 't) cconstraint" |
  LT 'c 't |
  LE 'c 't |
  EQ 'c 't |
  GT 'c 't |
  GE 'c 't

section \<open>Syntactic Definition\<close>

text \<open>
  For an informal description of timed automata we refer to Bengtsson and Yi \cite{BengtssonY03}.
  We define a timed automaton \<open>A\<close>
\<close>

type_synonym
  ('c, 'time, 's) invassn = "'s \<Rightarrow> ('c, 'time) cconstraint"

type_synonym
  ('a, 'c, 'time, 's) transition = "'s * ('c, 'time) cconstraint * 'a * 'c list * 's"

type_synonym
  ('a, 'c, 'time, 's) ta = "('a, 'c, 'time, 's) transition set * ('c, 'time, 's) invassn"

definition trans_of :: "('a, 'c, 'time, 's) ta \<Rightarrow> ('a, 'c, 'time, 's) transition set" where
  "trans_of \<equiv> fst"
definition inv_of  :: "('a, 'c, 'time, 's) ta \<Rightarrow> ('c, 'time, 's) invassn" where
  "inv_of \<equiv> snd"

abbreviation transition ::
  "('a, 'c, 'time, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, 'time) cconstraint \<Rightarrow> 'a \<Rightarrow> 'c list \<Rightarrow> 's \<Rightarrow> bool"
("_ \<turnstile> _ \<longrightarrow>\<^bsup>_,_,_\<^esup> _" [61,61,61,61,61,61] 61) where
  "(A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l') \<equiv> (l,g,a,r,l') \<in> trans_of A"

subsection \<open>Collecting Information About Clocks\<close>

fun collect_clks :: "('c, 't :: time) cconstraint \<Rightarrow> 'c set"
where
  "collect_clks (AND cc1 cc2) = collect_clks cc1 \<union> collect_clks cc2" |
  "collect_clks (LT c _) = {c}" |
  "collect_clks (LE c _) = {c}" |
  "collect_clks (EQ c _) = {c}" |
  "collect_clks (GE c _) = {c}" |
  "collect_clks (GT c _) = {c}"

fun collect_clock_pairs :: "('c, 't :: time) cconstraint \<Rightarrow> ('c * 't) set"
where
  "collect_clock_pairs (LT x m) = {(x, m)}" |
  "collect_clock_pairs (LE x m) = {(x, m)}" |
  "collect_clock_pairs (EQ x m) = {(x, m)}" |
  "collect_clock_pairs (GE x m) = {(x, m)}" |
  "collect_clock_pairs (GT x m) = {(x, m)}" |
  "collect_clock_pairs (AND cc1 cc2) = (collect_clock_pairs cc1 \<union> collect_clock_pairs cc2)"

definition collect_clkt :: "('a, 'c, 't::time, 's) transition set \<Rightarrow> ('c *'t) set"
where
  "collect_clkt S = \<Union> {collect_clock_pairs (fst (snd t)) | t . t \<in> S}"

definition collect_clki :: "('c, 't :: time, 's) invassn \<Rightarrow> ('c *'t) set"
where
  "collect_clki I = \<Union> {collect_clock_pairs (I x) | x. True}"

definition clkp_set :: "('a, 'c, 't :: time, 's) ta \<Rightarrow> ('c *'t) set"
where
  "clkp_set A = collect_clki (inv_of A) \<union> collect_clkt (trans_of A)"

definition collect_clkvt :: "('a, 'c, 't::time, 's) transition set \<Rightarrow> 'c set"
where
  "collect_clkvt S = \<Union> {set ((fst o snd o snd o snd) t) | t . t \<in> S}"

abbreviation clk_set where "clk_set A \<equiv> fst ` clkp_set A \<union> collect_clkvt (trans_of A)"

(* We don not need this here but most other theories will make use of this predicate *)
inductive valid_abstraction
where
  "\<lbrakk>\<forall>(x,m) \<in> clkp_set A. m \<le> k x \<and> x \<in> X \<and> m \<in> \<nat>; collect_clkvt (trans_of A) \<subseteq> X; finite X\<rbrakk>
  \<Longrightarrow> valid_abstraction A X k"

section \<open>Operational Semantics\<close>

type_synonym ('c, 't) cval = "'c \<Rightarrow> 't"

definition cval_add :: "('c,'t) cval \<Rightarrow> 't::time \<Rightarrow> ('c,'t) cval" (infixr "\<oplus>" 64)
where
  "u \<oplus> d = (\<lambda> x. u x + d)"

inductive clock_val :: "('c, 't) cval \<Rightarrow> ('c, 't::time) cconstraint \<Rightarrow> bool" ("_ \<turnstile> _" [62, 62] 62)
where
  "\<lbrakk>u \<turnstile> cc1; u \<turnstile> cc2\<rbrakk> \<Longrightarrow> u \<turnstile> AND cc1 cc2" |
  "\<lbrakk>u c < d\<rbrakk> \<Longrightarrow> u \<turnstile> LT c d" |
  "\<lbrakk>u c \<le> d\<rbrakk> \<Longrightarrow> u \<turnstile> LE c d" |
  "\<lbrakk>u c = d\<rbrakk> \<Longrightarrow> u \<turnstile> EQ c d" |
  "\<lbrakk>u c \<ge> d\<rbrakk> \<Longrightarrow> u \<turnstile> GE c d" |
  "\<lbrakk>u c > d\<rbrakk> \<Longrightarrow> u \<turnstile> GT c d"

declare clock_val.intros[intro]

inductive_cases[elim!]: "u \<turnstile> AND cc1 cc2"
inductive_cases[elim!]: "u \<turnstile> LT c d"
inductive_cases[elim!]: "u \<turnstile> LE c d"
inductive_cases[elim!]: "u \<turnstile> EQ c d"
inductive_cases[elim!]: "u \<turnstile> GE c d"
inductive_cases[elim!]: "u \<turnstile> GT c d"

fun clock_set :: "'c list \<Rightarrow> 't::time \<Rightarrow> ('c,'t) cval \<Rightarrow> ('c,'t) cval"
where
  "clock_set [] _ u = u" |
  "clock_set (c#cs) t u = (clock_set cs t u)(c:=t)"

abbreviation clock_set_abbrv :: "'c list \<Rightarrow> 't::time \<Rightarrow> ('c,'t) cval \<Rightarrow> ('c,'t) cval"
("[_\<rightarrow>_]_" [65,65,65] 65)
where
  "[r \<rightarrow> t]u \<equiv> clock_set r t u"

inductive step_t ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> ('t::time) \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>\<^bsup>_\<^esup> \<langle>_, _\<rangle>" [61,61,61] 61)                      
where
  "\<lbrakk>u \<turnstile> inv_of A l; u \<oplus> d \<turnstile> inv_of A l; d \<ge> 0\<rbrakk> \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l, u \<oplus> d\<rangle>"

declare step_t.intros[intro!]

inductive_cases[elim!]: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>"

lemma step_t_determinacy1:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle> \<Longrightarrow>  A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l'',u''\<rangle> \<Longrightarrow> l' = l''"
by auto

lemma step_t_determinacy2:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle> \<Longrightarrow>  A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l'',u''\<rangle> \<Longrightarrow> u' = u''"
by auto

lemma step_t_cont1:
  "d \<ge> 0 \<Longrightarrow> e \<ge> 0 \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow>\<^bsup>e\<^esup> \<langle>l'',u''\<rangle>
  \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d+e\<^esup> \<langle>l'',u''\<rangle>"
proof -
  assume A: "d \<ge> 0" "e \<ge> 0" "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>" "A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow>\<^bsup>e\<^esup> \<langle>l'',u''\<rangle>"
  hence "u' = (u \<oplus> d)" "u'' = (u' \<oplus> e)" by auto
  hence "u'' = (u \<oplus> (d + e))" unfolding cval_add_def by auto
  with A show ?thesis by auto
qed

inductive step_a ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  "\<lbrakk>A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'; u \<turnstile> g; u' \<turnstile> inv_of A l'; u' = [r \<rightarrow> 0]u\<rbrakk> \<Longrightarrow> (A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u'\<rangle>)"

inductive step ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow> \<langle>_,_\<rangle>" [61,61,61] 61)
where
  step_a: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l',u'\<rangle> \<Longrightarrow> (A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>)" |
  step_t: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle> \<Longrightarrow> (A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>)"

inductive_cases[elim!]: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>"

declare step.intros[intro]

inductive
  steps :: "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  refl: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l, u\<rangle>" |
  step: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle>"

declare steps.intros[intro]

section \<open>Zone Semantics\<close>

type_synonym ('c, 't) zone = "('c, 't) cval set"

definition zone_delay :: "('c, ('t::time)) zone \<Rightarrow> ('c, 't) zone"
("_\<^sup>\<up>" [71] 71)
where
  "Z\<^sup>\<up> = {u \<oplus> d|u d. u \<in> Z \<and> d \<ge> (0::'t)}"

definition zone_set :: "('c, 't::time) zone \<Rightarrow> 'c list \<Rightarrow> ('c, 't) zone"
("_\<^bsub>_ \<rightarrow> 0\<^esub>" [71] 71)
where
  "zone_set Z r = {[r \<rightarrow> (0::'t)]u | u . u \<in> Z}"

inductive step_z ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) zone \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  step_t_z: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l, (Z \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}\<rangle>" |
  step_a_z: "\<lbrakk>A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'\<rbrakk>
              \<Longrightarrow> (A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', zone_set (Z \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}\<rangle> )"

inductive_cases[elim!]: "A \<turnstile> \<langle>l, u\<rangle> \<leadsto> \<langle>l', u'\<rangle>"

declare step_z.intros[intro]

lemma step_z_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z'\<rangle> \<Longrightarrow> (\<forall> u' \<in> Z'. \<exists> u \<in> Z.  A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>)"
proof (induction rule: step_z.induct, goal_cases)
  case 1 thus ?case unfolding zone_delay_def by blast
next
  case (2 A l g a r l' Z)
  show ?case
  proof
    fix u' assume "u' \<in> zone_set (Z \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"
    then obtain u where
      "u \<turnstile> g" "u' \<turnstile> inv_of A l'" "u' = [r\<rightarrow>0]u" "u \<in> Z"
    unfolding zone_set_def by auto
    with step_a.intros[OF 2 this(1-3)] show "\<exists>u\<in>Z. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>" by fast
  qed
qed

lemma step_z_complete:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists> Z'. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
proof (induction rule: step.induct, goal_cases)
  case (1 A l u a l' u')
  then obtain g r
  where u': "u' = [r\<rightarrow>0]u" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "u \<turnstile> g" "[r\<rightarrow>0]u \<turnstile> inv_of A l'"
  by (cases rule: step_a.cases) auto
  hence "u' \<in> zone_set (Z \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"
  unfolding zone_set_def using \<open>u \<in> Z\<close> by blast
  with u'(1,2) show ?case by blast
next
  case (2 A l u d l' u')
  hence u': "u' = (u \<oplus> d)" "u \<turnstile> inv_of A l" "u \<oplus> d \<turnstile> inv_of A l" "0 \<le> d" and "l = l'" by auto
  with u' \<open>u \<in> Z\<close> have
    "u' \<in> {u'' \<oplus> d |u'' d. u'' \<in> Z \<inter> {u. u \<turnstile> inv_of A l} \<and> 0 \<le> d} \<inter> {u. u \<turnstile> inv_of A l}"
  by fastforce
  thus ?case using \<open>l = l'\<close>  step_t_z[unfolded zone_delay_def, of A l] by blast
qed

text \<open>
  Corresponds to version in old papers --
  not strong enough for inductive proof over transitive closure relation.
\<close>
lemma step_z_complete1:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> \<exists> Z. A \<turnstile> \<langle>l, {u}\<rangle> \<leadsto> \<langle>l', Z\<rangle> \<and> u' \<in> Z"
proof (induction rule: step.induct, goal_cases)
  case (1 A l u a l' u')
  then obtain g r
  where u': "u' = [r\<rightarrow>0]u" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "u \<turnstile> g" "[r\<rightarrow>0]u \<turnstile> inv_of A l'"
  by (cases rule: step_a.cases) auto
  hence "{[r\<rightarrow>0]u} = zone_set ({u} \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"
  unfolding zone_set_def by blast
  with u'(1,2) show ?case by auto 
next
  case (2 A l u d l' u')
  hence u': "u' = (u \<oplus> d)" "u \<turnstile> inv_of A l" "u \<oplus> d \<turnstile> inv_of A l" "0 \<le> d" and "l = l'" by auto
  hence "{u} = {u} \<inter> {u''. u'' \<turnstile> inv_of A l}" by fastforce 
  with u'(1) have "{u'} = {u'' \<oplus> d |u''. u'' \<in> {u} \<inter> {u''. u'' \<turnstile> inv_of A l}}" by fastforce
  with u' have
    "u' \<in> {u'' \<oplus> d |u'' d. u'' \<in> {u} \<inter> {u. u \<turnstile> inv_of A l} \<and> 0 \<le> d} \<inter> {u. u \<turnstile> inv_of A l}"
  by fastforce
  thus ?case using \<open>l = l'\<close> step_t_z[unfolded zone_delay_def, of A l "{u}"] by blast
qed

text \<open>
  Easier proof.
\<close>
lemma step_z_complete2:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> \<exists> Z. A \<turnstile> \<langle>l, {u}\<rangle> \<leadsto> \<langle>l', Z\<rangle> \<and> u' \<in> Z"
using step_z_complete by fast

inductive
  steps_z :: "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) zone \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  refl: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l, Z\<rangle>" |
  step: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>* \<langle>l'', Z''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l'', Z''\<rangle>"

declare steps_z.intros[intro]

lemma steps_z_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l', Z'\<rangle> \<Longrightarrow> u' \<in> Z' \<Longrightarrow> \<exists> u \<in> Z. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>"
proof (induction A l _ l' _ arbitrary: rule: steps_z.induct, goal_cases)
  case refl thus ?case by fast
next
  case (step A l Z l' Z' l'' Z'')
  then obtain u'' where u'': "A \<turnstile> \<langle>l', u''\<rangle> \<rightarrow>* \<langle>l'',u'\<rangle>" "u'' \<in> Z'" by auto
  then obtain u where "u \<in> Z" "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u''\<rangle>" using step_z_sound[OF step(1)] by blast
  with u'' show ?case by blast
qed

lemma steps_z_complete:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists> Z'. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
proof (induction arbitrary: Z rule: steps.induct)
  case refl thus ?case by auto
next
  case (step A l u l' u' l'' u'' Z)
  from step_z_complete[OF this(1,4)] obtain Z' where Z': "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z'\<rangle>" "u' \<in> Z'" by auto
  then obtain Z'' where "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>* \<langle>l'',Z''\<rangle>" "u'' \<in> Z''" using step by metis
  with Z' show ?case by blast
qed

end
