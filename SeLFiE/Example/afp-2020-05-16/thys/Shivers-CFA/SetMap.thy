section \<open>Set-valued maps\<close>
theory SetMap
  imports Main
begin

text \<open>
For the abstract semantics, we need methods to work with set-valued maps, i.e.\ functions from a key type to sets of values. For this type, some well known operations are introduced and properties shown, either borrowing the nomenclature from finite maps (\<open>sdom\<close>, \<open>sran\<close>,...) or of sets (\<open>{}.\<close>, \<open>\<union>.\<close>,...).
\<close>

definition
  sdom :: "('a => 'b set) => 'a set" where
  "sdom m = {a. m a ~= {}}"

definition
  sran :: "('a => 'b set) => 'b set" where
  "sran m = {b. \<exists>a. b \<in> m a}"

lemma sranI: "b \<in> m a \<Longrightarrow> b \<in> sran m"
  by(auto simp: sran_def)

lemma sdom_not_mem[elim]: "a \<notin> sdom m \<Longrightarrow> m a = {}"
  by (auto simp: sdom_def)

definition smap_empty ("{}.")
 where "{}. k = {}"

definition smap_union :: "('a::type \<Rightarrow> 'b::type set)  \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)" ("_ \<union>. _")
 where "smap1 \<union>. smap2 k =  smap1 k \<union> smap2 k"

primrec smap_Union :: "('a::type \<Rightarrow> 'b::type set) list \<Rightarrow> 'a \<Rightarrow> 'b set" ("\<Union>._")
  where [simp]:"\<Union>. [] = {}."
      | "\<Union>. (m#ms) = m  \<union>. \<Union>. ms"

definition smap_singleton :: "'a::type \<Rightarrow> 'b::type set \<Rightarrow> 'a \<Rightarrow> 'b set" ("{ _ := _}.")
  where "{k := vs}. = {}. (k := vs)"

definition smap_less :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> bool" ("_/ \<subseteq>. _" [50, 51] 50)
  where "smap_less m1 m2 = (\<forall>k. m1 k \<subseteq> m2 k)"

lemma sdom_empty[simp]: "sdom {}. = {}"
  unfolding sdom_def smap_empty_def by auto

lemma sdom_singleton[simp]: "sdom {k := vs}. \<subseteq> {k}"
  by (auto simp add: sdom_def smap_singleton_def smap_empty_def)

lemma sran_singleton[simp]: "sran {k := vs}. = vs"
  by (auto simp add: sran_def smap_singleton_def smap_empty_def)

lemma sran_empty[simp]: "sran {}. = {}"
  unfolding sran_def smap_empty_def by auto

lemma sdom_union[simp]: "sdom (m \<union>. n) = sdom m \<union> sdom n"
  by(auto simp add:smap_union_def sdom_def)

lemma sran_union[simp]: "sran (m \<union>. n) = sran m \<union> sran n"
  by(auto simp add:smap_union_def sran_def)

lemma smap_empty[simp]: "{}. \<subseteq>. {}."
  unfolding smap_less_def by auto

lemma smap_less_refl: "m \<subseteq>. m"
  unfolding smap_less_def by simp

lemma smap_less_trans[trans]: "\<lbrakk> m1 \<subseteq>. m2; m2 \<subseteq>. m3 \<rbrakk> \<Longrightarrow> m1 \<subseteq>. m3"
  unfolding smap_less_def by auto

lemma smap_union_mono: "\<lbrakk> ve1 \<subseteq>. ve1'; ve2 \<subseteq>. ve2' \<rbrakk> \<Longrightarrow> ve1 \<union>. ve2 \<subseteq>. ve1' \<union>. ve2'"
  by (auto simp add:smap_less_def smap_union_def)

lemma smap_Union_union: "m1 \<union>. \<Union>.ms = \<Union>.(m1#ms)"
  by (rule ext, auto simp add: smap_union_def smap_Union_def)

lemma smap_Union_mono:
  assumes "list_all2 smap_less ms1 ms2"
  shows "\<Union>. ms1 \<subseteq>. \<Union>. ms2"
using assms 
  by(induct rule:list_induct2[OF list_all2_lengthD[OF assms]])
    (auto intro:smap_union_mono)

lemma smap_singleton_mono: "v \<subseteq> v' \<Longrightarrow> {k := v}. \<subseteq>. {k := v'}."
 by (auto simp add: smap_singleton_def smap_less_def)

lemma smap_union_comm: "m1 \<union>. m2 = m2 \<union>. m1"
by (rule ext,auto simp add:smap_union_def)

lemma smap_union_empty1[simp]: "{}. \<union>. m = m"
  by(rule ext, auto simp add:smap_union_def smap_empty_def)

lemma smap_union_empty2[simp]: "m \<union>. {}. = m"
  by(rule ext, auto simp add:smap_union_def smap_empty_def)

lemma smap_union_assoc [simp]: "(m1 \<union>. m2) \<union>. m3 = m1 \<union>. (m2 \<union>. m3)"
  by (rule ext, auto simp add:smap_union_def)

lemma smap_Union_append[simp]: "\<Union>. (m1@m2) = (\<Union>. m1) \<union>. (\<Union>. m2)"
  by (induct m1) auto

lemma smap_Union_rev[simp]: "\<Union>. (rev l) = \<Union>. l"
  by(induct l)(auto simp add:smap_union_comm)

lemma smap_Union_map_rev[simp]: "\<Union>. (map f (rev l)) = \<Union>. (map f l)"
  by(subst rev_map[THEN sym], subst smap_Union_rev, rule refl)

end
