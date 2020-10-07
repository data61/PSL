theory Prefix
imports Main
begin

(* 
  Prefixes and Prefix Closure of traces 
*)
definition prefix :: "'e list \<Rightarrow> 'e list \<Rightarrow> bool" (infixl "\<preceq>" 100)
where
"(l1 \<preceq> l2) \<equiv> (\<exists>l3. l1 @ l3 = l2)" 

definition prefixclosed :: "('e list) set \<Rightarrow> bool"
where
"prefixclosed tr \<equiv> (\<forall>l1 \<in> tr. \<forall>l2. l2 \<preceq> l1 \<longrightarrow> l2 \<in> tr)"

(* the empty list is a prefix of every list *)
lemma empty_prefix_of_all: "[] \<preceq> l" 
  using prefix_def [of "[]" l] by simp

(* the empty list is in any non-empty prefix-closed set *)
lemma empty_trace_contained: "\<lbrakk> prefixclosed tr ; tr \<noteq> {} \<rbrakk> \<Longrightarrow> [] \<in> tr"
proof -
  assume 1: "prefixclosed tr" and
         2: "tr \<noteq> {}"
  then obtain l1 where "l1 \<in> tr" 
    by auto
  with 1 have "\<forall>l2. l2 \<preceq> l1 \<longrightarrow> l2 \<in> tr" 
    by (simp add: prefixclosed_def)
  thus "[] \<in> tr" 
    by (simp add: empty_prefix_of_all)
qed

(* the prefix-predicate is transitive *)
lemma transitive_prefix: "\<lbrakk> l1 \<preceq> l2 ; l2 \<preceq> l3 \<rbrakk> \<Longrightarrow> l1 \<preceq> l3"
  by (auto simp add: prefix_def)

end
