section \<open>Priority Map Specifications\<close>

theory Prio_Map_Specs
imports "HOL-Data_Structures.Map_Specs"
begin

(*<*)
(** TODO/FIXME:
  Duplicated from List_Ins_Del.
  We cannot import this theory, as it has name clashed with AList_Upd_Del!
*)
lemma sorted_Cons_iff:
  "sorted(x # xs) = ((\<forall>y \<in> set xs. x < y) \<and> sorted xs)"
by(simp add: sorted_wrt_Cons)

(** TODO: Belongs into AList_Upd_Del *)
lemma sorted_map_of_Some_eq: 
  "sorted1 xs \<Longrightarrow> map_of xs k = Some v \<longleftrightarrow> (k,v)\<in>set xs"
by (induction xs arbitrary: k v) (auto split: if_splits simp: sorted_Cons_iff)

(*>*)
  
subsection \<open>Abstract Data Type\<close>
  
locale PrioMap = Map where lookup = lookup 
  for lookup :: "'m \<Rightarrow> 'a \<Rightarrow> 'b::linorder option" +
  fixes is_empty :: "'m \<Rightarrow> bool"
  fixes getmin :: "'m \<Rightarrow> 'a \<times> 'b"
  assumes map_is_empty: "invar m \<Longrightarrow> is_empty m \<longleftrightarrow> lookup m = Map.empty"
  and map_getmin: "getmin m = (k,p) \<Longrightarrow> invar m \<Longrightarrow> lookup m \<noteq> Map.empty 
  \<Longrightarrow> lookup m k = Some p \<and> (\<forall>p'\<in>ran (lookup m). p\<le>p')"
begin

lemmas prio_map_specs = map_specs map_is_empty 

lemma map_getminE:
  assumes "getmin m = (k,p)" "invar m" "lookup m \<noteq> Map.empty" 
  obtains "lookup m k = Some p" "\<forall>k' p'. lookup m k' = Some p' \<longrightarrow> p\<le>p'"  
using map_getmin[OF assms] by (auto simp: ran_def)

end

definition is_min2 :: "(_\<times>'a::linorder) \<Rightarrow> (_\<times>'a) set \<Rightarrow> bool" where
"is_min2 x xs \<equiv> x\<in>xs \<and> (\<forall>y\<in>xs. snd x \<le> snd y)"


subsection \<open>Inorder-Based Specification\<close>  
  
locale PrioMap_by_Ordered = Map_by_Ordered 
  where lookup=lookup for lookup :: "'t \<Rightarrow> 'a::linorder \<Rightarrow> 'b::linorder option" +
  fixes is_empty :: "'t \<Rightarrow> bool"
  fixes getmin :: "'t \<Rightarrow> 'a\<times>'b"
  assumes inorder_isempty': "\<lbrakk>inv t; sorted1 (inorder t)\<rbrakk> 
      \<Longrightarrow> is_empty t \<longleftrightarrow> inorder t = []"
  and inorder_getmin': 
      "\<lbrakk>inv t; sorted1 (inorder t); inorder t \<noteq> []; getmin t = (a,b)\<rbrakk> 
        \<Longrightarrow> is_min2 (a,b) (set (inorder t))"
begin

lemma 
  inorder_isempty: "invar t \<Longrightarrow> is_empty t \<longleftrightarrow> inorder t = []"
  and inorder_getmin: "\<lbrakk>invar t; inorder t \<noteq> []; getmin t = (a,b)\<rbrakk> 
        \<Longrightarrow> is_min2 (a,b) (set (inorder t))"
unfolding invar_def by (auto simp: inorder_isempty' inorder_getmin') 

lemma inorder_lookup_empty_iff: 
  "invar m \<Longrightarrow> lookup m = Map.empty \<longleftrightarrow> inorder m = []"
using inorder_lookup[of m]
apply (auto split: if_splits simp: invar_def)
by (metis map_of.elims option.discI)

lemma inorder_lookup_ran_eq: 
  "\<lbrakk>inv m; sorted1 (inorder m)\<rbrakk> \<Longrightarrow> ran (lookup m) = snd ` set (inorder m)"
using inorder_lookup[of m] unfolding ran_def
by (force simp: sorted_map_of_Some_eq)

sublocale PrioMap empty update delete invar lookup is_empty getmin
apply unfold_locales
 apply (auto simp: inorder_isempty inorder_lookup_empty_iff)
 apply (frule (2) inorder_getmin)
 apply (auto simp: is_min2_def sorted_map_of_Some_eq invar_def inorder_lookup) []
apply (frule (2) inorder_getmin)
apply (force simp: is_min2_def sorted_map_of_Some_eq inorder_lookup_ran_eq 
                   eq_Min_iff invar_def inorder_lookup) []
done

end

end
  