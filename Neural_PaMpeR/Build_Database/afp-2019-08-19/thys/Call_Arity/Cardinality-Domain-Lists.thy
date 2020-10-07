theory "Cardinality-Domain-Lists"
imports Launchbury.Vars "Launchbury.Nominal-HOLCF" Launchbury.Env "Cardinality-Domain" "Set-Cpo" "Env-Set-Cpo"
begin

fun no_call_in_path where
  "no_call_in_path x [] \<longleftrightarrow> True"
 | "no_call_in_path x (y#xs) \<longleftrightarrow> y \<noteq> x \<and> no_call_in_path x xs"

fun one_call_in_path where
  "one_call_in_path x [] \<longleftrightarrow> True"
 | "one_call_in_path x (y#xs) \<longleftrightarrow> (if x = y then no_call_in_path x xs else one_call_in_path x xs)"

lemma no_call_in_path_set_conv:
  "no_call_in_path x p \<longleftrightarrow> x \<notin> set p"
  by(induction p) auto 

lemma one_call_in_path_filter_conv:
  "one_call_in_path x p \<longleftrightarrow> length (filter (\<lambda> x'. x' = x) p) \<le> 1"
  by(induction p) (auto simp add: no_call_in_path_set_conv filter_empty_conv)

lemma no_call_in_tail: "no_call_in_path x (tl p) \<longleftrightarrow> (no_call_in_path x p \<or> one_call_in_path x p \<and> hd p = x)"
  by(induction p) auto

lemma no_imp_one: "no_call_in_path x p \<Longrightarrow> one_call_in_path x p"
  by (induction p) auto

lemma one_imp_one_tail: "one_call_in_path x p \<Longrightarrow> one_call_in_path x (tl p)"
  by (induction p) (auto split: if_splits intro: no_imp_one)

lemma more_than_one_setD:
  "\<not> one_call_in_path x p \<Longrightarrow> x \<in> set p" 
  by (induction p) (auto split: if_splits)

lemma no_call_in_path[eqvt]: "no_call_in_path p x \<Longrightarrow> no_call_in_path (\<pi> \<bullet> p) (\<pi> \<bullet> x)"
  by (induction p x rule: no_call_in_path.induct) auto

lemma one_call_in_path[eqvt]: "one_call_in_path p x \<Longrightarrow> one_call_in_path (\<pi> \<bullet> p) (\<pi> \<bullet> x)"
  by (induction p x rule: one_call_in_path.induct) (auto dest: no_call_in_path)

definition pathCard :: "var list  \<Rightarrow> (var \<Rightarrow> two)"
  where "pathCard p x = (if no_call_in_path x p then none else (if one_call_in_path x p then once else many))"

lemma pathCard_Nil[simp]: "pathCard [] = \<bottom>"
   by rule (simp add: pathCard_def)

lemma pathCard_Cons[simp]: "pathCard (x#xs) x = two_add\<cdot>once\<cdot>(pathCard xs x)"
  unfolding pathCard_def
  by (auto simp add: two_add_simp)

lemma pathCard_Cons_other[simp]: "x' \<noteq> x \<Longrightarrow> pathCard (x#xs) x' = pathCard xs x'"
  unfolding pathCard_def by auto

lemma no_call_in_path_filter[simp]: "no_call_in_path x [x\<leftarrow>xs . x \<in> S] \<longleftrightarrow> no_call_in_path x xs \<or> x \<notin> S"
  by (induction xs) auto

lemma one_call_in_path_filter[simp]: "one_call_in_path x [x\<leftarrow>xs . x \<in> S] \<longleftrightarrow> one_call_in_path x xs \<or> x \<notin> S"
  by (induction xs) auto

definition pathsCard :: "var list set \<Rightarrow> (var \<Rightarrow> two)"
  where "pathsCard ps x = (if (\<forall> p \<in> ps. no_call_in_path x p) then none else (if (\<forall> p\<in>ps. one_call_in_path x p) then once else many))"

lemma paths_Card_above:
  "p \<in> ps \<Longrightarrow> pathCard p \<sqsubseteq> pathsCard ps"
  by (rule fun_belowI) (auto simp add: pathsCard_def pathCard_def)

lemma pathsCard_below:
  assumes  "\<And> p. p \<in> ps \<Longrightarrow> pathCard p \<sqsubseteq> ce"
  shows "pathsCard ps \<sqsubseteq> ce"
proof(rule fun_belowI)
  fix x
  show "pathsCard ps x \<sqsubseteq> ce x"
    by (auto simp add: pathsCard_def pathCard_def split: if_splits dest!: fun_belowD[OF assms, where x = x] elim: below_trans[rotated] dest: no_imp_one)
qed

lemma pathsCard_mono:
  "ps \<subseteq> ps' \<Longrightarrow> pathsCard ps \<sqsubseteq> pathsCard ps'"
  by (auto intro: pathsCard_below paths_Card_above)

lemmas pathsCard_mono' = pathsCard_mono[folded below_set_def]

lemma record_call_pathsCard: 
  "pathsCard ({ tl p | p . p \<in> fs \<and> hd p = x}) \<sqsubseteq> record_call x\<cdot>(pathsCard fs)"
proof (rule pathsCard_below)
  fix p'
  assume "p' \<in> {tl p |p. p \<in> fs \<and> hd p = x}"
  then obtain p where "p' = tl p" and "p \<in> fs" and "hd p = x" by auto
  
  have "pathCard (tl p) \<sqsubseteq> record_call x\<cdot>(pathCard p)"
    apply (rule fun_belowI)
    using \<open>hd p = x\<close> by (auto simp add: pathCard_def record_call_simp no_call_in_tail dest: one_imp_one_tail)
    
  hence "pathCard (tl p) \<sqsubseteq> record_call x\<cdot>(pathsCard fs)"
    by (rule below_trans[OF _ monofun_cfun_arg[OF  paths_Card_above[OF \<open>p \<in> fs\<close>]]])
  thus "pathCard p' \<sqsubseteq> record_call x\<cdot>(pathsCard fs)" using \<open>p' = _\<close> by simp
qed
  
lemma pathCards_noneD:
  "pathsCard ps x = none \<Longrightarrow> x \<notin> \<Union>(set ` ps)"
  by (auto simp add: pathsCard_def no_call_in_path_set_conv split:if_splits)

lemma cont_pathsCard[THEN cont_compose, cont2cont, simp]:
  "cont pathsCard"
  by(fastforce intro!: cont2cont_lambda cont_if_else_above simp add: pathsCard_def below_set_def)

lemma pathsCard_eqvt[eqvt]: "\<pi> \<bullet> pathsCard ps x = pathsCard (\<pi> \<bullet> ps) (\<pi> \<bullet> x)"
  unfolding pathsCard_def by perm_simp rule

lemma edom_pathsCard[simp]: "edom (pathsCard ps) = \<Union>(set ` ps)"
  unfolding edom_def pathsCard_def
  by (auto simp add:  no_call_in_path_set_conv)

lemma env_restr_pathsCard[simp]: "pathsCard ps f|` S = pathsCard (filter (\<lambda> x. x \<in> S) ` ps)"
  by (auto simp add: pathsCard_def lookup_env_restr_eq)


end
