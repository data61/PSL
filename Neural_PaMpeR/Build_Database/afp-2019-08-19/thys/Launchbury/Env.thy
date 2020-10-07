theory Env
  imports Main "HOLCF-Join-Classes"
begin

default_sort type

text \<open>
Our type for environments is a function with a pcpo as the co-domain; this theory collects
related definitions.
\<close>

subsubsection \<open>The domain of a pcpo-valued function\<close>

definition edom :: "('key \<Rightarrow> 'value::pcpo) \<Rightarrow> 'key set"
  where "edom m = {x. m x \<noteq> \<bottom>}"

lemma bot_edom[simp]: "edom \<bottom> = {}" by (simp add: edom_def)

lemma bot_edom2[simp]: "edom (\<lambda>_ . \<bottom>) = {}" by (simp add: edom_def)

lemma edomIff: "(a \<in> edom m) = (m a \<noteq> \<bottom>)" by (simp add: edom_def)
lemma edom_iff2: "(m a = \<bottom>) \<longleftrightarrow> (a \<notin> edom m)" by (simp add: edom_def)

lemma edom_empty_iff_bot: "edom m = {} \<longleftrightarrow> m = \<bottom>"
  by (metis below_bottom_iff bot_edom edomIff empty_iff fun_belowI)

lemma lookup_not_edom: "x \<notin> edom m \<Longrightarrow> m x = \<bottom>"  by (auto iff:edomIff)

lemma lookup_edom[simp]: "m x \<noteq> \<bottom> \<Longrightarrow> x \<in> edom m"  by (auto iff:edomIff)

lemma edom_mono: "x \<sqsubseteq> y \<Longrightarrow> edom x \<subseteq> edom y"
  unfolding edom_def
  by auto (metis below_bottom_iff fun_belowD)
  

lemma edom_subset_adm[simp]:
  "adm (\<lambda>ae'. edom ae' \<subseteq> S)"
  apply (rule admI)
  apply rule
  apply (subst (asm) edom_def) back
  apply simp
  apply (subst (asm) lub_fun) apply assumption
  apply (subst (asm) lub_eq_bottom_iff)
  apply (erule ch2ch_fun)
  unfolding not_all
  apply (erule exE)
  apply (rule subsetD)
  apply (rule allE) apply assumption apply assumption
  unfolding edom_def
  apply simp
  done

subsubsection \<open>Updates\<close>

lemma edom_fun_upd_subset: "edom (h (x := v)) \<subseteq> insert x (edom h)"
  by (auto simp add: edom_def)

declare fun_upd_same[simp] fun_upd_other[simp]

subsubsection \<open>Restriction\<close>

definition env_restr :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::pcpo) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "env_restr S m = (\<lambda> x. if x \<in> S then m x else \<bottom>)"

abbreviation env_restr_rev  (infixl "f|`"  110)
  where "env_restr_rev m S \<equiv> env_restr S m"

notation (latex output) env_restr_rev ("_|\<^bsub>_\<^esub>")

lemma env_restr_empty_iff[simp]: "m f|` S = \<bottom> \<longleftrightarrow> edom m \<inter> S = {}"
  apply (auto simp add: edom_def env_restr_def lambda_strict[symmetric]  split:if_splits)
  apply metis
  apply (fastforce simp add: edom_def env_restr_def lambda_strict[symmetric]  split:if_splits)
  done
lemmas env_restr_empty = iffD2[OF env_restr_empty_iff, simp]

lemma lookup_env_restr[simp]: "x \<in> S \<Longrightarrow> (m f|` S) x = m x"
  by (fastforce simp add: env_restr_def)

lemma lookup_env_restr_not_there[simp]: "x \<notin> S \<Longrightarrow> (env_restr S m) x = \<bottom>"
  by (fastforce simp add: env_restr_def)

lemma lookup_env_restr_eq: "(m f|` S) x = (if x \<in> S then m x else \<bottom>)"
  by simp

lemma env_restr_eqI: "(\<And>x. x \<in> S \<Longrightarrow> m\<^sub>1 x = m\<^sub>2 x) \<Longrightarrow> m\<^sub>1 f|` S = m\<^sub>2 f|` S"
  by (auto simp add: lookup_env_restr_eq)

lemma env_restr_eqD: "m\<^sub>1 f|` S = m\<^sub>2 f|` S \<Longrightarrow> x \<in> S \<Longrightarrow> m\<^sub>1 x = m\<^sub>2 x"
  by (auto dest!: fun_cong[where x = x])

lemma env_restr_belowI: "(\<And>x. x \<in> S \<Longrightarrow> m\<^sub>1 x \<sqsubseteq> m\<^sub>2 x) \<Longrightarrow> m\<^sub>1 f|` S \<sqsubseteq> m\<^sub>2 f|` S"
  by (auto intro: fun_belowI simp add: lookup_env_restr_eq)

lemma env_restr_belowD: "m\<^sub>1 f|` S \<sqsubseteq> m\<^sub>2 f|` S \<Longrightarrow> x \<in> S \<Longrightarrow> m\<^sub>1 x \<sqsubseteq> m\<^sub>2 x"
  by (auto dest!: fun_belowD[where x = x])

lemma env_restr_env_restr[simp]:
 "x f|` d2 f|` d1 = x f|` (d1 \<inter> d2)"
  by (fastforce simp add: env_restr_def)

lemma env_restr_env_restr_subset:
 "d1 \<subseteq> d2 \<Longrightarrow> x f|` d2 f|` d1 = x f|` d1"
 by (metis Int_absorb2 env_restr_env_restr)

lemma env_restr_useless: "edom m \<subseteq> S \<Longrightarrow> m f|` S = m"
  by (rule ext) (auto simp add: lookup_env_restr_eq dest!: subsetD)

lemma env_restr_UNIV[simp]: "m f|` UNIV = m"
  by (rule env_restr_useless) simp

lemma env_restr_fun_upd[simp]: "x \<in> S \<Longrightarrow> m1(x := v) f|` S = (m1 f|` S)(x := v)"
  apply (rule ext)
  apply (case_tac "xa = x")
  apply (auto simp add: lookup_env_restr_eq)
  done

lemma env_restr_fun_upd_other[simp]: "x \<notin> S \<Longrightarrow> m1(x := v) f|` S = m1 f|` S"
  apply (rule ext)
  apply (case_tac "xa = x")
  apply (auto simp add: lookup_env_restr_eq)
  done

lemma env_restr_eq_subset:
  assumes "S \<subseteq> S'"
  and "m1 f|` S' = m2 f|` S'"
  shows "m1 f|` S = m2 f|` S"
using assms
by (metis env_restr_env_restr le_iff_inf)

lemma env_restr_below_subset:
  assumes "S \<subseteq> S'"
  and "m1 f|` S' \<sqsubseteq> m2 f|` S'"
  shows "m1 f|` S \<sqsubseteq> m2 f|` S"
using assms
by (auto intro!: env_restr_belowI dest!: env_restr_belowD)

lemma edom_env[simp]:
  "edom (m f|` S) = edom m \<inter> S"
  unfolding edom_def env_restr_def by auto

lemma env_restr_below_self: "f f|` S \<sqsubseteq> f"
  by (rule fun_belowI) (auto simp add: env_restr_def)

lemma env_restr_below_trans:
  "m1 f|` S1 \<sqsubseteq> m2 f|` S1 \<Longrightarrow> m2 f|` S2 \<sqsubseteq> m3 f|` S2 \<Longrightarrow> m1 f|` (S1 \<inter> S2) \<sqsubseteq> m3 f|` (S1 \<inter> S2)"
by (auto intro!: env_restr_belowI dest!: env_restr_belowD elim: below_trans)

lemma env_restr_cont: "cont (env_restr S)"
  apply (rule cont2cont_lambda)
  unfolding env_restr_def
  apply (intro cont2cont cont_fun)
  done

lemma env_restr_mono: "m1 \<sqsubseteq> m2 \<Longrightarrow>  m1 f|` S \<sqsubseteq> m2 f|` S"
  by (metis env_restr_belowI fun_belowD)

lemma env_restr_mono2: "S2 \<subseteq> S1  \<Longrightarrow> m f|` S2 \<sqsubseteq> m f|` S1"
  by (metis env_restr_below_self env_restr_env_restr_subset)

lemmas cont_compose[OF env_restr_cont, cont2cont, simp]

lemma env_restr_cong: "(\<And>x. edom m \<subseteq> S \<inter> S' \<union> -S \<inter> -S')  \<Longrightarrow> m f|` S = m f|` S'"
  by (rule ext)(auto simp add: lookup_env_restr_eq edom_def)

subsubsection \<open>Deleting\<close>

definition env_delete :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::pcpo)"
  where "env_delete x m = m(x := \<bottom>)"

lemma lookup_env_delete[simp]:
  "x' \<noteq> x \<Longrightarrow> env_delete x m x' = m x'"
  by (simp add: env_delete_def)

lemma lookup_env_delete_None[simp]:
  "env_delete x m x = \<bottom>"
  by (simp add: env_delete_def)

lemma edom_env_delete[simp]:
  "edom (env_delete x m) = edom m - {x}"
  by (auto simp add: env_delete_def edom_def)

lemma edom_env_delete_subset:
  "edom (env_delete x m) \<subseteq> edom m" by auto

lemma env_delete_fun_upd[simp]:
  "env_delete x (m(x := v)) = env_delete x m"
  by (auto simp add: env_delete_def)

lemma env_delete_fun_upd2[simp]:
  "(env_delete x m)(x := v) = m(x := v)"
  by (auto simp add: env_delete_def)

lemma env_delete_fun_upd3[simp]:
  "x \<noteq> y \<Longrightarrow> env_delete x (m(y := v)) = (env_delete x m)(y := v)"
  by (auto simp add: env_delete_def)

lemma env_delete_noop[simp]:
  "x \<notin> edom m \<Longrightarrow> env_delete x m = m"
  by (auto simp add: env_delete_def edom_def)

lemma fun_upd_env_delete[simp]: "x \<in> edom \<Gamma> \<Longrightarrow> (env_delete x \<Gamma>)(x := \<Gamma> x) = \<Gamma>"
  by (auto)

lemma env_restr_env_delete_other[simp]: "x \<notin> S \<Longrightarrow> env_delete x m f|` S = m f|` S"
  apply (rule ext)
  apply (auto simp add: lookup_env_restr_eq)
  by (metis lookup_env_delete)

lemma env_delete_restr: "env_delete x m = m f|` (-{x})"
  by (auto simp add: lookup_env_restr_eq)

lemma below_env_deleteI: "f x = \<bottom> \<Longrightarrow> f \<sqsubseteq> g \<Longrightarrow> f \<sqsubseteq> env_delete x g"
  by (metis env_delete_def env_delete_restr env_restr_mono fun_upd_triv)

lemma env_delete_below_cong[intro]:
  assumes "x \<noteq> v \<Longrightarrow> e1 x \<sqsubseteq> e2 x"
  shows "env_delete v e1 x \<sqsubseteq> env_delete v e2 x"
  using assms unfolding env_delete_def by auto

lemma env_delete_env_restr_swap:
  "env_delete x (env_restr S e) = env_restr S (env_delete x e)"
  by (metis (erased, hide_lams) env_delete_def env_restr_fun_upd env_restr_fun_upd_other fun_upd_triv lookup_env_restr_eq)

lemma env_delete_mono:
  "m \<sqsubseteq> m' \<Longrightarrow> env_delete x m \<sqsubseteq> env_delete x m'"
  unfolding env_delete_restr
  by (rule env_restr_mono)
  
lemma env_delete_below_arg:
  "env_delete x m \<sqsubseteq> m"
  unfolding env_delete_restr
  by (rule env_restr_below_self)

subsubsection \<open>Merging of two functions\<close>

text \<open>
We'd like to have some nice syntax for @{term "override_on"}.
\<close>

abbreviation override_on_syn ("_ ++\<^bsub>_\<^esub> _" [100, 0, 100] 100) where "f1 ++\<^bsub>S\<^esub> f2 \<equiv> override_on f1 f2 S"

lemma override_on_bot[simp]:
  "\<bottom> ++\<^bsub>S\<^esub> m = m f|` S" 
  "m ++\<^bsub>S\<^esub> \<bottom> = m f|` (-S)" 
  by (auto simp add: override_on_def env_restr_def)

lemma edom_override_on[simp]: "edom (m1 ++\<^bsub>S\<^esub> m2) = (edom m1 - S) \<union> (edom m2 \<inter> S)"
  by (auto simp add: override_on_def edom_def)

lemma lookup_override_on_eq: "(m1 ++\<^bsub>S\<^esub> m2) x = (if x \<in> S then m2 x else m1 x)"
  by (cases "x \<notin> S") simp_all

lemma override_on_upd_swap: 
  "x \<notin> S \<Longrightarrow> \<rho>(x := z) ++\<^bsub>S\<^esub> \<rho>' = (\<rho> ++\<^bsub>S\<^esub> \<rho>')(x := z)"
  by (auto simp add: override_on_def  edom_def)

lemma override_on_upd: 
  "x \<in> S \<Longrightarrow> \<rho> ++\<^bsub>S\<^esub> (\<rho>'(x := z)) = (\<rho> ++\<^bsub>S - {x}\<^esub> \<rho>')(x := z)"
  by (auto simp add: override_on_def  edom_def)

lemma env_restr_add: "(m1 ++\<^bsub>S2\<^esub> m2) f|` S = m1 f|` S ++\<^bsub>S2\<^esub> m2 f|` S"
  by (auto simp add: override_on_def  edom_def env_restr_def)

lemma env_delete_add: "env_delete x (m1 ++\<^bsub>S\<^esub> m2) = env_delete x m1 ++\<^bsub>S - {x}\<^esub> env_delete x m2"
  by (auto simp add: override_on_def  edom_def env_restr_def env_delete_def)

subsubsection \<open>Environments with binary joins\<close>

lemma edom_join[simp]: "edom (f \<squnion> (g::('a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}))) = edom f \<union> edom g"
  unfolding edom_def by auto

lemma env_delete_join[simp]: "env_delete x (f \<squnion> (g::('a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}))) = env_delete x f \<squnion> env_delete x g"
  by (metis env_delete_def fun_upd_meet_simp)

lemma env_restr_join:
  fixes m1 m2 :: "'a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}"
  shows "(m1 \<squnion> m2) f|` S = (m1 f|` S) \<squnion> (m2 f|` S )"
  by (auto simp add: env_restr_def)

lemma env_restr_join2:
  fixes m :: "'a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}"
  shows "m f|` S \<squnion> m f|` S' = m f|` (S \<union> S')"
  by (auto simp add: env_restr_def)

lemma join_env_restr_UNIV:
  fixes m :: "'a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}"
  shows "S1 \<union> S2 = UNIV \<Longrightarrow> (m f|` S1) \<squnion> (m f|` S2) = m"
  by (fastforce simp add: env_restr_def)

lemma env_restr_split:
  fixes m :: "'a::type \<Rightarrow> 'b::{Finite_Join_cpo,pcpo}"
  shows "m = m f|` S \<squnion> m f|` (- S)"
by (simp add: env_restr_join2 Compl_partition)

lemma env_restr_below_split:
  "m f|` S \<sqsubseteq> m' \<Longrightarrow> m f|` (- S) \<sqsubseteq> m' \<Longrightarrow> m \<sqsubseteq> m'"
  by (metis ComplI fun_below_iff lookup_env_restr)

subsubsection \<open>Singleton environments\<close>

definition esing :: "'a \<Rightarrow> 'b::{pcpo} \<rightarrow> ('a \<Rightarrow> 'b)"
  where "esing x = (\<Lambda> a. (\<lambda> y . (if x = y then a else \<bottom>)))"

lemma esing_bot[simp]: "esing x \<cdot> \<bottom> = \<bottom>"
  by (rule ext)(simp add: esing_def)

lemma esing_simps[simp]:
  "(esing x \<cdot> n) x = n"
  "x' \<noteq> x \<Longrightarrow> (esing x \<cdot> n) x' = \<bottom>"
  by (simp_all add: esing_def)

lemma esing_eq_up_iff[simp]: "(esing x\<cdot>(up\<cdot>a)) y = up\<cdot>a' \<longleftrightarrow> (x = y \<and> a = a')"
  by (auto simp add: fun_below_iff esing_def)

lemma esing_below_iff[simp]: "esing x \<cdot> a \<sqsubseteq> ae  \<longleftrightarrow> a \<sqsubseteq> ae x"
  by (auto simp add: fun_below_iff esing_def)

lemma edom_esing_subset: "edom (esing x\<cdot>n) \<subseteq> {x}"
  unfolding edom_def esing_def by auto

lemma edom_esing_up[simp]: "edom (esing x \<cdot> (up \<cdot> n)) = {x}"
  unfolding edom_def esing_def by auto

lemma env_delete_esing[simp]: "env_delete x (esing x \<cdot> n) = \<bottom>"
  unfolding env_delete_def esing_def
  by auto

lemma env_restr_esing[simp]:
  "x\<in> S \<Longrightarrow> esing x\<cdot>v f|` S = esing x\<cdot>v" 
  by (auto intro: env_restr_useless dest: subsetD[OF edom_esing_subset])

lemma env_restr_esing2[simp]:
  "x \<notin> S \<Longrightarrow> esing x\<cdot>v f|` S = \<bottom>" 
  by (auto  dest: subsetD[OF edom_esing_subset])

lemma esing_eq_iff[simp]:
  "esing x\<cdot>v = esing x\<cdot>v' \<longleftrightarrow> v = v'"
  by (metis esing_simps(1))


end
