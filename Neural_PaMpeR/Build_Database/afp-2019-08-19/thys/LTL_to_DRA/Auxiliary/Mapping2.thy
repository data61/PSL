(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Auxiliary Mapping Facts\<close>

theory Mapping2
  imports Main Map2 "HOL-Library.Mapping"
begin 

lemma lookup_delete:
  "Mapping.lookup (Mapping.delete k m) k = None"
  by (transfer; simp) 

lemma lookup_tabulate:
  "Mapping.lookup (Mapping.tabulate xs f) x = (if x \<in> set xs then Some (f x) else None)"
  by (transfer; insert map_of_tabulate_simp)

lemma lookup_tabulate_Some:
  "x \<in> set xs \<Longrightarrow> the (Mapping.lookup (Mapping.tabulate xs f) x) = f x" 
  by (simp add: lookup_tabulate)

lemma finite_keys_tabulate:
  "finite (Mapping.keys (Mapping.tabulate xs f))"
  by simp

lemma keys_empty_iff_map_empty:
  "Mapping.keys m = {} \<longleftrightarrow> m = Mapping.empty"
  by (transfer; simp)

lemma mapping_equal:
  "Mapping.keys m = Mapping.keys m' \<Longrightarrow> (\<And>x. x \<in> Mapping.keys m \<Longrightarrow> Mapping.lookup m x = Mapping.lookup m' x) \<Longrightarrow> m = m'"
  by (transfer; blast intro: map_equal)

fun mapping_generator :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) mapping set"
where
  "mapping_generator V [] = {Mapping.empty}"
| "mapping_generator V (k#ks) = {Mapping.update k v m | v m.  v \<in> set (V k) \<and> m \<in> mapping_generator V ks}"

fun mapping_generator_list :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) mapping list"
where
  "mapping_generator_list V [] = [Mapping.empty]"
| "mapping_generator_list V (k#ks) = concat (map (\<lambda>m. map (\<lambda>v. Mapping.update k v m) (V k)) (mapping_generator_list V ks))"

lemma mapping_generator_code [code]:
  "mapping_generator V K = set (mapping_generator_list V K)"
  by (induction K) auto 

lemma mapping_generator_set_eq:
  "mapping_generator V K = {m. Mapping.keys m = set K \<and> (\<forall>k \<in> (set K). the (Mapping.lookup m k) \<in> set (V k))}"
proof (induction K)
  case (Cons k ks)
    let ?l = "{m(k \<mapsto> v) |v m. v \<in> set (V k) \<and>  m \<in> {m. dom m = set ks \<and> (\<forall>k\<in>set ks. the (m k) \<in> set (V k))}}"
    let ?r = "{m. dom m = set (k # ks) \<and> (\<forall>k\<in>set (k # ks). the (m k) \<in> set (V k))}"

    have "?l \<subseteq> ?r"
      by fastforce
    moreover
    {
      fix m 
      assume "m \<in> ?r" 
      hence "dom m = set (k#ks)" 
        and "\<forall>k \<in> set (k#ks). the (m k) \<in> set (V k)" 
        and "\<forall>k' \<in> set (k#ks). m k \<noteq> None"
        by auto   
      moreover
      then obtain m' where "dom m' = set ks"
        and "\<forall>x \<in> set ks. m x = m' x"
        using map_reduce[of m k "set ks"] by auto
      ultimately
      have "the (m k) \<in> set (V k)"
        and "dom m' = set ks" 
        and "\<forall>k \<in> (set ks). the (m' k) \<in> set (V k)"
        and "m = m'(k \<mapsto> the (m k))"
        apply (simp, blast, auto) 
        apply (insert map_equal[of m "m'(k \<mapsto> the (m k))"])
        apply (unfold dom_map_update \<open>dom m = set (k#ks)\<close> \<open>dom m' = set ks\<close>)
        by fastforce
      moreover
      hence "m \<in> set (map (\<lambda>v. m'(k \<mapsto> v)) (V k))"
        by simp
      ultimately
      have "m \<in> ?l"
        using \<open>dom m = set (k#ks)\<close> by blast       
    }
    ultimately
    have "{Mapping.update k v m |v m. v \<in> set (V k) \<and> m \<in> {m. Mapping.keys m = set ks \<and> (\<forall>k\<in>set ks. the (Mapping.lookup m k) \<in> set (V k))}} 
      = {m. Mapping.keys m = set (k # ks) \<and> (\<forall>k\<in>set (k # ks). the (Mapping.lookup m k) \<in> set (V k))}" 
      by (transfer; blast)
    thus ?case
      by (simp add: Cons)
qed (force simp add: keys_empty_iff_map_empty)

end
