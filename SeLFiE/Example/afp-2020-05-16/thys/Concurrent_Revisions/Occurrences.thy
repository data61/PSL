section Occurrences

text \<open>This theory contains all of the definitions and laws required for reasoning about
  identifiers that occur in the data structures of the concurrent revisions model.\<close>

theory Occurrences
  imports Data
begin

subsection Definitions

subsubsection \<open>Revision identifiers\<close>

definition RID\<^sub>S :: "('r,'l,'v) store \<Rightarrow> 'r set" where
  "RID\<^sub>S \<sigma> \<equiv> \<Union> (RID\<^sub>V ` ran \<sigma>)"

definition RID\<^sub>L :: "('r,'l,'v) local_state \<Rightarrow> 'r set" where
  "RID\<^sub>L s \<equiv> case s of (\<sigma>, \<tau>, e) \<Rightarrow> RID\<^sub>S \<sigma> \<union> RID\<^sub>S \<tau> \<union> RID\<^sub>E e"

definition RID\<^sub>G :: "('r,'l,'v) global_state \<Rightarrow> 'r set" where
  "RID\<^sub>G s \<equiv> dom s \<union> \<Union> (RID\<^sub>L ` ran s)"

subsubsection \<open>Location identifiers\<close>

definition LID\<^sub>S :: "('r,'l,'v) store \<Rightarrow> 'l set" where
  "LID\<^sub>S \<sigma> \<equiv> dom \<sigma> \<union> \<Union> (LID\<^sub>V ` ran \<sigma>)"

definition LID\<^sub>L :: "('r,'l,'v) local_state \<Rightarrow> 'l set" where
  "LID\<^sub>L s \<equiv> case s of (\<sigma>, \<tau>, e) \<Rightarrow> LID\<^sub>S \<sigma> \<union> LID\<^sub>S \<tau> \<union> LID\<^sub>E e"

definition LID\<^sub>G :: "('r,'l,'v) global_state \<Rightarrow> 'l set" where
  "LID\<^sub>G s \<equiv> \<Union> (LID\<^sub>L ` ran s)"

subsection \<open>Inference rules\<close>

subsubsection \<open>Introduction and elimination rules\<close>

lemma RID\<^sub>SI [intro]: "\<sigma> l = Some v \<Longrightarrow> r \<in> RID\<^sub>V v \<Longrightarrow> r \<in> RID\<^sub>S \<sigma>"
  by (auto simp add: RID\<^sub>S_def ran_def)

lemma RID\<^sub>SE [elim]: "r \<in> RID\<^sub>S \<sigma> \<Longrightarrow> (\<And>l v. \<sigma> l = Some v \<Longrightarrow> r \<in> RID\<^sub>V v \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp add: RID\<^sub>S_def ran_def)

lemma RID\<^sub>LI [intro, consumes 1]:
  assumes "s = (\<sigma>, \<tau>, e)"
  shows
    "r \<in> RID\<^sub>S \<sigma> \<Longrightarrow> r \<in> RID\<^sub>L s"
    "r \<in> RID\<^sub>S \<tau> \<Longrightarrow> r \<in> RID\<^sub>L s"
    "r \<in> RID\<^sub>E e \<Longrightarrow> r \<in> RID\<^sub>L s"
  by (auto simp add: RID\<^sub>L_def assms)

lemma RID\<^sub>LE [elim]:
  "\<lbrakk> r \<in> RID\<^sub>L s; (\<And>\<sigma> \<tau> e. s = (\<sigma>, \<tau>, e) \<Longrightarrow> (r \<in> RID\<^sub>S \<sigma> \<Longrightarrow> P) \<Longrightarrow> (r \<in> RID\<^sub>S \<tau> \<Longrightarrow> P) \<Longrightarrow> (r \<in> RID\<^sub>E e \<Longrightarrow> P) \<Longrightarrow> P) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" 
  by (cases s) (auto simp add: RID\<^sub>L_def)

lemma RID\<^sub>GI [intro]:
  "s r = Some v \<Longrightarrow> r \<in> RID\<^sub>G s"
  "s r' = Some ls \<Longrightarrow> r \<in> RID\<^sub>L ls \<Longrightarrow> r \<in> RID\<^sub>G s"
   apply (simp add: RID\<^sub>G_def domI)
  by (metis (no_types, lifting) RID\<^sub>G_def UN_I UnI2 ranI)

lemma RID\<^sub>GE [elim]:
  assumes
    "r \<in> RID\<^sub>G s"
    "r \<in> dom s \<Longrightarrow> P"
    "\<And>r' ls. s r' = Some ls \<Longrightarrow> r \<in> RID\<^sub>L ls \<Longrightarrow> P"
  shows P
  using assms by (auto simp add: RID\<^sub>G_def ran_def)

lemma LID\<^sub>SI [intro]:
  "\<sigma> l = Some v \<Longrightarrow> l \<in> LID\<^sub>S \<sigma>"
  "\<sigma> l' = Some v \<Longrightarrow> l \<in> LID\<^sub>V v \<Longrightarrow> l \<in> LID\<^sub>S \<sigma>"
  by (auto simp add: LID\<^sub>S_def ran_def)

lemma LID\<^sub>SE [elim]:
  assumes 
    "l \<in> LID\<^sub>S \<sigma>"
    "l \<in> dom \<sigma> \<Longrightarrow> P"
    "\<And>l' v. \<sigma> l' = Some v \<Longrightarrow> l \<in> LID\<^sub>V v \<Longrightarrow> P"
  shows P
  using assms by (auto simp add: LID\<^sub>S_def ran_def)

lemma LID\<^sub>LI [intro]:
  assumes "s = (\<sigma>, \<tau>, e)"
  shows
    "r \<in> LID\<^sub>S \<sigma> \<Longrightarrow> r \<in> LID\<^sub>L s" 
    "r \<in> LID\<^sub>S \<tau> \<Longrightarrow> r \<in> LID\<^sub>L s" 
    "r \<in> LID\<^sub>E e \<Longrightarrow> r \<in> LID\<^sub>L s"
  by (auto simp add: LID\<^sub>L_def assms)

lemma LID\<^sub>LE [elim]:
  "\<lbrakk> l \<in> LID\<^sub>L s; (\<And>\<sigma> \<tau> e. s = (\<sigma>, \<tau>, e) \<Longrightarrow> (l \<in> LID\<^sub>S \<sigma> \<Longrightarrow> P) \<Longrightarrow> (l \<in> LID\<^sub>S \<tau> \<Longrightarrow> P) \<Longrightarrow> (l \<in> LID\<^sub>E e \<Longrightarrow> P) \<Longrightarrow> P) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" 
  by (cases s) (auto simp add: LID\<^sub>L_def)

lemma LID\<^sub>GI [intro]: "s r = Some ls \<Longrightarrow> l \<in> LID\<^sub>L ls \<Longrightarrow> l \<in> LID\<^sub>G s"
  by (auto simp add: LID\<^sub>G_def LID\<^sub>L_def ran_def)

lemma LID\<^sub>GE [elim]: "l \<in> LID\<^sub>G s \<Longrightarrow> (\<And>r ls. s r = Some ls \<Longrightarrow> l \<in> LID\<^sub>L ls \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp add: LID\<^sub>G_def ran_def)

subsubsection \<open>Distributive laws\<close>

lemma ID_distr_completion [simp]: 
  "RID\<^sub>E (\<E>[e]) = RID\<^sub>C \<E> \<union> RID\<^sub>E e"
  "LID\<^sub>E (\<E>[e]) = LID\<^sub>C \<E> \<union> LID\<^sub>E e"
  by (induct rule: plug.induct) auto

lemma ID_restricted_store_subset_store: 
  "RID\<^sub>S (\<sigma>(l := None)) \<subseteq> RID\<^sub>S \<sigma>"
  "LID\<^sub>S (\<sigma>(l := None)) \<subseteq> LID\<^sub>S \<sigma>"
proof -
  show "RID\<^sub>S (\<sigma>(l := None)) \<subseteq> RID\<^sub>S \<sigma>"
  proof (rule subsetI)
    fix r
    assume "r \<in> RID\<^sub>S (\<sigma>(l := None))"
    then obtain l' v where "(\<sigma>(l := None)) l' = Some v" and r_v: "r \<in> RID\<^sub>V v" by blast
    have "l' \<noteq> l" using \<open>(\<sigma>(l := None)) l' = Some v\<close> by auto
    hence "\<sigma> l' = Some v" using \<open>(\<sigma>(l := None)) l' = Some v\<close> by auto
    thus "r \<in> RID\<^sub>S \<sigma>" using r_v by blast
  qed
next
  show "LID\<^sub>S (\<sigma>(l := None)) \<subseteq> LID\<^sub>S \<sigma>"
  proof (rule subsetI)
    fix l'
    assume "l' \<in> LID\<^sub>S (\<sigma>(l := None))"
    hence "l' \<in> dom (\<sigma>(l := None)) \<or> (\<exists>l'' v. (\<sigma>(l := None)) l'' = Some v \<and> l' \<in> LID\<^sub>V v)" by blast
    thus "l' \<in> LID\<^sub>S \<sigma>"
    proof (rule disjE)
      assume "l' \<in> dom (\<sigma>(l := None))"
      thus "l' \<in> LID\<^sub>S \<sigma>" by auto
    next
      assume "\<exists>l'' v. (\<sigma>(l := None)) l'' = Some v \<and> l' \<in> LID\<^sub>V v"
      then obtain l'' v where "(\<sigma>(l := None)) l'' = Some v" and l'_in_v: "l' \<in> LID\<^sub>V v" by blast
      hence "\<sigma> l'' = Some v" by (cases "l = l''", auto)
      thus "l' \<in> LID\<^sub>S \<sigma>" using l'_in_v by blast
    qed
  qed
qed

lemma in_restricted_store_in_unrestricted_store [intro]: 
  "r \<in> RID\<^sub>S (\<sigma>(l := None)) \<Longrightarrow> r \<in> RID\<^sub>S \<sigma>"
  "l' \<in> LID\<^sub>S (\<sigma>(l := None)) \<Longrightarrow> l' \<in> LID\<^sub>S \<sigma>" 
  by (meson contra_subsetD ID_restricted_store_subset_store)+

lemma in_restricted_store_in_updated_store [intro]: 
  "r \<in> RID\<^sub>S (\<sigma>(l := None)) \<Longrightarrow> r \<in> RID\<^sub>S (\<sigma>(l \<mapsto> v))" 
  "l' \<in> LID\<^sub>S (\<sigma>(l := None)) \<Longrightarrow> l' \<in> LID\<^sub>S (\<sigma>(l \<mapsto> v))"
proof -
  assume "r \<in> RID\<^sub>S (\<sigma>(l := None))"
  hence "r \<in> RID\<^sub>S (\<sigma> |` (- {l}))" by (simp add: restrict_complement_singleton_eq)
  hence "r \<in> RID\<^sub>S (\<sigma>(l \<mapsto> v) |` (- {l}))" by simp
  hence "r \<in> RID\<^sub>S (\<sigma>(l := Some v, l := None))" by (simp add: restrict_complement_singleton_eq)
  thus "r \<in> RID\<^sub>S (\<sigma>(l \<mapsto> v))" by blast
next
  assume "l' \<in> LID\<^sub>S (\<sigma>(l := None))"
  hence "l' \<in> LID\<^sub>S (\<sigma> |` (- {l}))" by (simp add: restrict_complement_singleton_eq)
  hence "l' \<in> LID\<^sub>S (\<sigma>(l \<mapsto> v) |` (- {l}))" by simp
  hence "l' \<in> LID\<^sub>S (\<sigma>(l := Some v, l := None))" by (simp add: restrict_complement_singleton_eq)
  thus "l' \<in> LID\<^sub>S (\<sigma>(l \<mapsto> v))" by blast
qed

lemma ID_distr_store [simp]:
  "RID\<^sub>S (\<tau>(l \<mapsto> v)) = RID\<^sub>S (\<tau>(l := None)) \<union> RID\<^sub>V v"
  "LID\<^sub>S (\<tau>(l \<mapsto> v)) = insert l (LID\<^sub>S (\<tau>(l := None)) \<union> LID\<^sub>V v)"
proof -
  show "RID\<^sub>S (\<tau>(l \<mapsto> v)) = RID\<^sub>S (\<tau>(l := None)) \<union> RID\<^sub>V v"
  proof (rule set_eqI, rule iffI)
    fix r
    assume "r \<in> RID\<^sub>S (\<tau>(l \<mapsto> v))"
    then obtain l' v' where "(\<tau>(l \<mapsto> v)) l' = Some v'" "r \<in> RID\<^sub>V v'" by blast
    thus "r \<in> RID\<^sub>S (\<tau>(l := None)) \<union> RID\<^sub>V v" by (cases "l' = l") auto
  qed auto
next
  show "LID\<^sub>S (\<tau>(l \<mapsto> v)) = insert l (LID\<^sub>S (\<tau>(l := None)) \<union> LID\<^sub>V v)"
  proof (rule set_eqI, rule iffI)
    fix l'
    assume "l' \<in> LID\<^sub>S (\<tau>(l \<mapsto> v))"
    hence "l' \<in> dom (\<tau>(l \<mapsto> v)) \<or> (\<exists>l'' v'. (\<tau>(l \<mapsto> v)) l'' = Some v' \<and> l' \<in> LID\<^sub>V v')" by blast
    thus "l' \<in> insert l (LID\<^sub>S (\<tau>(l := None)) \<union> LID\<^sub>V v)"
    proof (rule disjE)
      assume "l' \<in> dom (\<tau>(l \<mapsto> v))"
      thus "l' \<in> insert l (LID\<^sub>S (\<tau>(l := None)) \<union> LID\<^sub>V v)" by (cases "l' = l") auto
    next
      assume "\<exists>l'' v'. (\<tau>(l \<mapsto> v)) l'' = Some v' \<and> l' \<in> LID\<^sub>V v'"
      then obtain l'' v' where "(\<tau>(l \<mapsto> v)) l'' = Some v'" "l' \<in> LID\<^sub>V v'" by blast
      thus "l' \<in> insert l (LID\<^sub>S (\<tau>(l := None)) \<union> LID\<^sub>V v)" by (cases "l = l''") auto
    qed
  qed auto
qed

lemma ID_distr_local [simp]: 
  "LID\<^sub>L (\<sigma>,\<tau>,e) = LID\<^sub>S \<sigma> \<union> LID\<^sub>S \<tau> \<union> LID\<^sub>E e"
  "RID\<^sub>L (\<sigma>,\<tau>,e) = RID\<^sub>S \<sigma> \<union> RID\<^sub>S \<tau> \<union> RID\<^sub>E e"
  by (simp add: LID\<^sub>L_def RID\<^sub>L_def)+

lemma ID_restricted_global_subset_unrestricted:
  "LID\<^sub>G (s(r := None)) \<subseteq> LID\<^sub>G s"
  "RID\<^sub>G (s(r := None)) \<subseteq> RID\<^sub>G s"
proof -
  show "LID\<^sub>G (s(r := None)) \<subseteq> LID\<^sub>G s"
  proof (rule subsetI)
    fix l
    assume "l \<in> LID\<^sub>G (s(r := None))"
    then obtain r'' ls where "(s(r := None)) r'' = Some ls" and l_in_ls: "l \<in> LID\<^sub>L ls" by blast
    have "r'' \<noteq> r " using \<open>(s(r := None)) r'' = Some ls\<close> by auto
    hence "s r'' = Some ls" using \<open>(s(r := None)) r'' = Some ls\<close> by auto
    thus "l \<in> LID\<^sub>G s" using l_in_ls by blast
  qed
next
  show "RID\<^sub>G (s(r := None)) \<subseteq> RID\<^sub>G s"
  proof (rule subsetI)
    fix r'
    assume "r' \<in> RID\<^sub>G (s(r := None))"
    hence "r' \<in> dom (s(r := None)) \<or> (\<exists>r'' ls. (s(r := None)) r'' = Some ls \<and> r' \<in> RID\<^sub>L ls)" by blast
    thus "r' \<in> RID\<^sub>G s"
    proof (rule disjE)
      assume "\<exists>r'' ls. (s(r := None)) r'' = Some ls \<and> r' \<in> RID\<^sub>L ls"
      then obtain r'' ls where "(s(r := None)) r'' = Some ls" and r'_in_ls: "r' \<in> RID\<^sub>L ls" by blast
      have neq: "r'' \<noteq> r" using \<open>(s(r := None)) r'' = Some ls\<close> by auto
      hence "s r'' = Some ls" using \<open>(s(r := None)) r'' = Some ls\<close> by auto
      thus "r' \<in> RID\<^sub>G s" using r'_in_ls by blast
    qed auto
  qed
qed

lemma in_restricted_global_in_unrestricted_global [intro]: 
  "r' \<in> RID\<^sub>G (s(r := None)) \<Longrightarrow> r' \<in> RID\<^sub>G s"
  "l \<in> LID\<^sub>G (s(r := None)) \<Longrightarrow> l \<in> LID\<^sub>G s"
  by (simp add: ID_restricted_global_subset_unrestricted rev_subsetD)+

lemma in_restricted_global_in_updated_global [intro]: 
  "r' \<in> RID\<^sub>G (s(r := None)) \<Longrightarrow> r' \<in> RID\<^sub>G (s(r \<mapsto> ls))" 
  "l \<in> LID\<^sub>G (s(r := None)) \<Longrightarrow> l \<in> LID\<^sub>G (s(r \<mapsto> ls))"
proof -
  assume "r' \<in> RID\<^sub>G (s(r := None))"
  hence "r' \<in> RID\<^sub>G (s |` (- {r}))" by (simp add: restrict_complement_singleton_eq)
  hence "r' \<in> RID\<^sub>G (s(r \<mapsto> ls) |` (- {r}))" by simp
  hence "r' \<in> RID\<^sub>G (s(r := Some ls, r := None))" by (simp add: restrict_complement_singleton_eq)
  thus "r' \<in> RID\<^sub>G (s(r \<mapsto> ls))" by blast
next
  assume "l \<in> LID\<^sub>G (s(r := None))"
  hence "l \<in> LID\<^sub>G (s |` (- {r}))" by (simp add: restrict_complement_singleton_eq)
  hence "l \<in> LID\<^sub>G (s(r \<mapsto> ls) |` (- {r}))" by simp
  hence "l \<in> LID\<^sub>G (s(r := Some ls, r := None))" by (simp add: restrict_complement_singleton_eq)
  thus "l \<in> LID\<^sub>G (s(r \<mapsto> ls))" by blast
qed

lemma ID_distr_global [simp]:
  "RID\<^sub>G (s(r \<mapsto> ls)) = insert r (RID\<^sub>G (s(r := None)) \<union> RID\<^sub>L ls)"
  "LID\<^sub>G (s(r \<mapsto> ls)) = LID\<^sub>G (s(r := None)) \<union> LID\<^sub>L ls"
proof -
  show "LID\<^sub>G (s(r \<mapsto> ls)) = LID\<^sub>G (s(r := None)) \<union> LID\<^sub>L ls"
  proof (rule set_eqI)
    fix l
    show "(l \<in> LID\<^sub>G (s(r \<mapsto> ls))) = (l \<in> LID\<^sub>G (s(r := None)) \<union> LID\<^sub>L ls)"
    proof (rule iffI)
      assume "l \<in> LID\<^sub>G (s(r \<mapsto> ls))"
      from this obtain r' ls' where "(s(r \<mapsto> ls)) r' = Some ls'" "l \<in> LID\<^sub>L ls'" by auto
      thus "l \<in> LID\<^sub>G (s(r := None)) \<union> LID\<^sub>L ls" by (cases "r = r'") auto
    qed auto
  qed
  show "RID\<^sub>G (s(r \<mapsto> ls)) = insert r (RID\<^sub>G (s(r := None)) \<union> RID\<^sub>L ls)"
  proof (rule set_eqI)
    fix r'
    show "(r' \<in> RID\<^sub>G (s(r \<mapsto> ls))) = (r' \<in> insert r (RID\<^sub>G (s(r := None)) \<union> RID\<^sub>L ls))"
    proof (rule iffI, clarsimp)
      assume r'_g: "r' \<in> RID\<^sub>G (s(r \<mapsto> ls))" and neq: "r' \<noteq> r" and r'_l: "r' \<notin> RID\<^sub>L ls"
      show "r' \<in> RID\<^sub>G (s(r := None))"
      proof (rule RID\<^sub>GE[OF r'_g])
        assume "r' \<in> dom (s(r \<mapsto> ls))"
        thus ?thesis by (simp add: RID\<^sub>G_def neq)
      next
        fix ls' r''
        assume r'_in_range:"(s(r \<mapsto> ls)) r'' = Some ls'" "r' \<in> RID\<^sub>L ls'"
        thus ?thesis by (cases "r'' = r") (use neq r'_l in auto)
      qed
    qed auto
  qed
qed

lemma restrictions_inwards [simp]:
  "x \<noteq> x' \<Longrightarrow> f(x := Some y, x' := None) = (f(x':= None, x := Some y))"
  by (rule fun_upd_twist)

subsubsection \<open>Miscellaneous laws\<close>

lemma ID_combination_subset_union [intro]:
  "RID\<^sub>S (\<sigma>;;\<tau>) \<subseteq> RID\<^sub>S \<sigma> \<union> RID\<^sub>S \<tau>"
  "LID\<^sub>S (\<sigma>;;\<tau>) \<subseteq> LID\<^sub>S \<sigma> \<union> LID\<^sub>S \<tau>"
proof -
  show "RID\<^sub>S (\<sigma>;;\<tau>) \<subseteq> RID\<^sub>S \<sigma> \<union> RID\<^sub>S \<tau>"
  proof (rule subsetI)
    fix r
    assume "r \<in> RID\<^sub>S (\<sigma>;;\<tau>)"
    from this obtain l v where "(\<sigma>;;\<tau>) l = Some v" and "r \<in> RID\<^sub>V v" by blast
    thus "r \<in> RID\<^sub>S \<sigma> \<union> RID\<^sub>S \<tau>" by (cases "l \<in> dom \<tau>") auto
  qed
  show "LID\<^sub>S (\<sigma>;;\<tau>) \<subseteq> LID\<^sub>S \<sigma> \<union> LID\<^sub>S \<tau>"
  proof (rule subsetI)
    fix l
    assume "l \<in> LID\<^sub>S (\<sigma>;;\<tau>)"
    hence "l \<in> dom (\<sigma>;;\<tau>) \<or> (\<exists>l' v. (\<sigma>;;\<tau>) l' = Some v \<and> l \<in> LID\<^sub>V v)" by blast
    thus "l \<in> LID\<^sub>S \<sigma> \<union> LID\<^sub>S \<tau>"
    proof (rule disjE)
      assume "l \<in> dom (\<sigma>;;\<tau>)"
      thus "l \<in> LID\<^sub>S \<sigma> \<union> LID\<^sub>S \<tau>" by (cases "l \<in> dom \<tau>") auto
    next 
      assume "\<exists>l' v. (\<sigma>;;\<tau>) l' = Some v \<and> l \<in> LID\<^sub>V v"
      from this obtain l' v where "(\<sigma>;;\<tau>) l' = Some v" "l \<in> LID\<^sub>V v" by blast
      thus "l \<in> LID\<^sub>S \<sigma> \<union> LID\<^sub>S \<tau>" by (cases "l' \<in> dom \<tau>") auto
    qed
  qed
qed

lemma in_combination_in_component [intro]: 
  "r \<in> RID\<^sub>S (\<sigma>;;\<tau>) \<Longrightarrow> r \<notin> RID\<^sub>S \<sigma> \<Longrightarrow> r \<in> RID\<^sub>S \<tau>"
  "r \<in> RID\<^sub>S (\<sigma>;;\<tau>) \<Longrightarrow> r \<notin> RID\<^sub>S \<tau> \<Longrightarrow> r \<in> RID\<^sub>S \<sigma>"
  "l \<in> LID\<^sub>S (\<sigma>;;\<tau>) \<Longrightarrow> l \<notin> LID\<^sub>S \<sigma> \<Longrightarrow> l \<in> LID\<^sub>S \<tau>"
  "l \<in> LID\<^sub>S (\<sigma>;;\<tau>) \<Longrightarrow> l \<notin> LID\<^sub>S \<tau> \<Longrightarrow> l \<in> LID\<^sub>S \<sigma>"
  by (meson Un_iff ID_combination_subset_union subsetCE)+

lemma in_mapped_in_component_of_combination [intro]:
  assumes 
    maps_to_v: "(\<sigma>;;\<tau>) l = Some v" and
    l'_in_v: "l' \<in> LID\<^sub>V v"
  shows
    "l' \<notin> LID\<^sub>S \<tau> \<Longrightarrow> l' \<in> LID\<^sub>S \<sigma>"
    "l' \<notin> LID\<^sub>S \<sigma> \<Longrightarrow> l' \<in> LID\<^sub>S \<tau>"
  by (metis LID\<^sub>SI(2) combine.simps l'_in_v maps_to_v)+

lemma elim_trivial_restriction [simp]: "l \<notin> LID\<^sub>S \<tau> \<Longrightarrow> (\<tau>(l := None)) = \<tau>" 
  by (simp add: LID\<^sub>S_def domIff fun_upd_idem)

lemma ID_distr_global_conditional:
  "s r = Some ls \<Longrightarrow> RID\<^sub>G s = insert r (RID\<^sub>G (s(r := None)) \<union> RID\<^sub>L ls)"
  "s r = Some ls \<Longrightarrow> LID\<^sub>G s = LID\<^sub>G (s(r := None)) \<union> LID\<^sub>L ls"
proof -
  assume "s r = Some ls"
  hence s_as_upd: "s = (s(r \<mapsto> ls))" by (simp add: fun_upd_idem)
  show "RID\<^sub>G s = insert r (RID\<^sub>G (s(r := None)) \<union> RID\<^sub>L ls)" by (subst s_as_upd, simp)
  show "LID\<^sub>G s = LID\<^sub>G (s(r := None)) \<union> LID\<^sub>L ls" by (subst s_as_upd, simp)
qed

end
