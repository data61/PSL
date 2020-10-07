(*<*)
theory Abstract_Monitor
  imports MFOTL
begin
(*>*)

section \<open>Abstract Specification of a Monitor\<close>

locale monitorable =
  fixes monitorable :: "'a MFOTL.formula \<Rightarrow> bool"

text \<open>The following locale specifies the desired behavior ouf a monitor abstractly.\<close>

locale monitor = monitorable +
  fixes
    M :: "'a MFOTL.formula \<Rightarrow> 'a MFOTL.prefix \<Rightarrow> (nat \<times> 'a option list) set"
  assumes
    mono_monitor: "monitorable \<phi> \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> M \<phi> \<pi> \<subseteq> M \<phi> \<pi>'"
    and sound_monitor: "monitorable \<phi> \<Longrightarrow> (i, v) \<in> M \<phi> \<pi> \<Longrightarrow>
      i < plen \<pi> \<and> wf_tuple (MFOTL.nfv \<phi>) (MFOTL.fv \<phi>) v \<and> (\<forall>\<sigma>. prefix_of \<pi> \<sigma> \<longrightarrow> MFOTL.sat \<sigma> (map the v) i \<phi>)"
    and complete_monitor: "monitorable \<phi> \<Longrightarrow> prefix_of \<pi> \<sigma> \<Longrightarrow>
      i < plen \<pi> \<Longrightarrow> wf_tuple (MFOTL.nfv \<phi>) (MFOTL.fv \<phi>) v \<Longrightarrow>
      (\<forall>\<sigma>. prefix_of \<pi> \<sigma> \<longrightarrow> MFOTL.sat \<sigma> (map the v) i \<phi>) \<Longrightarrow> \<exists>\<pi>'. prefix_of \<pi>' \<sigma> \<and> (i, v) \<in> M \<phi> \<pi>'"

locale slicable_monitor = monitor +
  assumes monitor_slice: "mem_restr S v \<Longrightarrow> (i, v) \<in> M \<phi> (MFOTL.pslice \<phi> S \<pi>) \<longleftrightarrow> (i, v) \<in> M \<phi> \<pi>"

locale monitor_pre_progress = monitorable +
  fixes progress :: "'a MFOTL.trace \<Rightarrow> 'a MFOTL.formula \<Rightarrow> nat \<Rightarrow> nat"
  assumes
    progress_mono: "j \<le> j' \<Longrightarrow> progress \<sigma> \<phi> j \<le> progress \<sigma> \<phi> j'"
    and progress_le: "progress \<sigma> \<phi> j \<le> j"
    and progress_ge: "monitorable \<phi> \<Longrightarrow> \<exists>j. i \<le> progress \<sigma> \<phi> j"

locale monitor_progress = monitor_pre_progress +
  assumes progress_prefix_conv: "prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of \<pi> \<sigma>' \<Longrightarrow>
    progress \<sigma> \<phi> (plen \<pi>) = progress \<sigma>' \<phi> (plen \<pi>)"
begin

definition verdicts :: "'a MFOTL.formula \<Rightarrow> 'a MFOTL.prefix \<Rightarrow> (nat \<times> 'a tuple) set" where
  "verdicts \<phi> \<pi> = {(i, v). wf_tuple (MFOTL.nfv \<phi>) (MFOTL.fv \<phi>) v \<and>
    (\<forall>\<sigma>. prefix_of \<pi> \<sigma> \<longrightarrow> i < progress \<sigma> \<phi> (plen \<pi>) \<and> MFOTL.sat \<sigma> (map the v) i \<phi>)}"

lemma verdicts_mono: "\<pi> \<le> \<pi>' \<Longrightarrow> verdicts \<phi> \<pi> \<subseteq> verdicts \<phi> \<pi>'"
  unfolding verdicts_def
  by (auto dest: prefix_of_antimono elim!: order.strict_trans2 intro!: progress_mono plen_mono)

end

lemma stake_eq_mono: "stake b x = stake b y \<Longrightarrow> a \<le> b \<Longrightarrow> stake a x = stake a y"
proof (induction a arbitrary: b x y)
  case 0
  then show ?case by simp
next
  case Suca: (Suc a)
  show ?case proof (cases b)
    case 0
    with Suca show ?thesis by (simp del: stake.simps)
  next
    case (Suc b')
    with Suca show ?thesis by (auto simp only: stake.simps list.inject)
  qed
qed

sublocale monitor_progress \<subseteq> monitor monitorable verdicts
proof (standard, goal_cases)
  case (1 \<phi> \<pi> \<pi>')
  from 1(2) show ?case by (rule verdicts_mono)
next
  case (2 \<phi> i v \<pi>)
  from \<open>(i, v) \<in> verdicts \<phi> \<pi>\<close> show ?case
    unfolding verdicts_def
    using ex_prefix_of[of \<pi>]
    by (auto elim!: order.strict_trans2 intro!: progress_le)
next
  case complete: (3 \<phi> \<pi> \<sigma> i v)
  from \<open>monitorable \<phi>\<close> obtain j where eval: "i < progress \<sigma> \<phi> j"
    unfolding less_eq_Suc_le
    using progress_ge by blast
  define j' where "j' = max (plen \<pi>) j"
  then have "plen \<pi> \<le> j'" by simp
  from eval have eval': "i < progress \<sigma> \<phi> j'"
    unfolding j'_def
    by (auto elim: order.strict_trans2 intro!: progress_mono)
  from complete(2) \<open>plen \<pi> \<le> j'\<close> have "\<pi> \<le> take_prefix j' \<sigma>"
  proof (transfer fixing: j', goal_cases prefix)
    case (prefix \<pi> \<sigma>)
    then have "stake j' \<sigma> = stake (length \<pi>) \<sigma> @ stake (j' - length \<pi>) (sdrop (length \<pi>) \<sigma>)"
      by (unfold stake_add) auto
    with \<open>stake (length \<pi>) \<sigma> = \<pi>\<close> show ?case 
      by auto
  qed
  with complete(4) eval' show ?case using progress_prefix_conv[of "take_prefix j' \<sigma>" \<sigma> \<sigma>' \<phi> for \<sigma>']
    unfolding verdicts_def
    by (auto intro!: exI[where x="take_prefix j' \<sigma>"] complete(5)[rule_format] elim: prefix_of_antimono)
qed

locale monitor_timed_progress = monitor_pre_progress +
  assumes progress_time_conv: "\<forall>i<j. \<tau> \<sigma> i = \<tau> \<sigma>' i \<Longrightarrow> progress \<sigma> \<phi> j = progress \<sigma>' \<phi> j"
    and progress_sat_cong: "prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of \<pi> \<sigma>' \<Longrightarrow> i < progress \<sigma> \<phi> (plen \<pi>) \<Longrightarrow>
      MFOTL.sat \<sigma> v i \<phi> \<longleftrightarrow> MFOTL.sat \<sigma>' v i \<phi>"
begin

lemma progress_map_conv: "progress (map_\<Gamma> f \<sigma>) \<phi> j = progress (map_\<Gamma> g \<sigma>) \<phi> j"
  by (auto intro: progress_time_conv)

lemma progress_slice_conv: "progress (MFOTL.slice \<phi>' R \<sigma>) \<phi> j = progress (MFOTL.slice \<phi>' R' \<sigma>) \<phi> j"
  unfolding MFOTL.slice_def using progress_map_conv .

lemma progress_slice: "progress (MFOTL.slice \<phi> R \<sigma>) \<phi> j = progress \<sigma> \<phi> j"
  using progress_map_conv[where g=id] by (simp add: MFOTL.slice_def)

end

sublocale monitor_timed_progress \<subseteq> monitor_progress
  by (unfold_locales, auto intro: progress_time_conv \<tau>_prefix_conv)

lemma (in monitor_timed_progress) verdicts_alt:
  "verdicts \<phi> \<pi> = {(i, v). wf_tuple (MFOTL.nfv \<phi>) (MFOTL.fv \<phi>) v \<and>
    (\<exists>\<sigma>. prefix_of \<pi> \<sigma> \<and> i < progress \<sigma> \<phi> (plen \<pi>) \<and> MFOTL.sat \<sigma> (map the v) i \<phi>)}"
  unfolding verdicts_def
  using ex_prefix_of[of \<pi>]
  by (auto dest: progress_prefix_conv[of \<pi> _ _ \<phi>] elim!: progress_sat_cong[THEN iffD1, rotated -1])

sublocale monitor_timed_progress \<subseteq> slicable_monitor monitorable verdicts
proof
  fix S :: "'a list set" and v i \<phi> \<pi>
  assume *: "mem_restr S v"
  show "((i, v) \<in> verdicts \<phi> (MFOTL.pslice \<phi> S \<pi>)) = ((i, v) \<in> verdicts \<phi> \<pi>)" (is "?L = ?R")
  proof
    assume ?L
    with * show ?R unfolding verdicts_def
      by (auto simp: progress_slice fvi_less_nfv wf_tuple_def elim!: mem_restrE
        box_equals[OF sat_slice_iff sat_fvi_cong sat_fvi_cong, symmetric, THEN iffD1, rotated -1]
        dest: spec[of _ "MFOTL.slice \<phi> S _"] prefix_of_pslice_slice)
  next
    assume ?R
    with * show ?L unfolding verdicts_alt
      by (auto simp: progress_slice fvi_less_nfv wf_tuple_def elim!: mem_restrE
        box_equals[OF sat_slice_iff sat_fvi_cong sat_fvi_cong, symmetric, THEN iffD2, rotated -1]
        intro: exI[of _ "MFOTL.slice \<phi> S _"] prefix_of_pslice_slice)
  qed
qed

text \<open>Past-only Formulas.\<close>

fun past_only :: "'a MFOTL.formula \<Rightarrow> bool" where
  "past_only (MFOTL.Pred _ _) = True"
| "past_only (MFOTL.Eq _ _) = True"
| "past_only (MFOTL.Neg \<psi>) = past_only \<psi>"
| "past_only (MFOTL.Or \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (MFOTL.Exists \<psi>) = past_only \<psi>"
| "past_only (MFOTL.Prev _ \<psi>) = past_only \<psi>"
| "past_only (MFOTL.Next _ _) = False"
| "past_only (MFOTL.Since \<alpha> _ \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (MFOTL.Until \<alpha> _ \<beta>) = False"

interpretation past_only_monitor: monitor_timed_progress past_only "\<lambda>\<sigma> \<phi> j. if past_only \<phi> then j else 0"
proof (unfold_locales, goal_cases)
  case (5 \<pi> \<sigma> \<sigma>' i \<phi> v)
  then have "past_only \<phi>" and "i < plen \<pi>" by (simp_all split: if_splits)
  then show ?case proof (induction \<phi> arbitrary: v i)
    case (Pred e ts)
    with \<Gamma>_prefix_conv[OF 5(1,2)] show ?case by simp
  next
    case (Prev I \<phi>)
    with \<tau>_prefix_conv[OF 5(1,2)] show ?case by (simp split: nat.split)
  next
    case (Since \<phi>1 I \<phi>2)
    with Since \<tau>_prefix_conv[OF 5(1,2)] show ?case by auto
  qed simp_all
qed auto

(*<*)
end
(*>*)
