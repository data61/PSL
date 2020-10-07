(*
  Boolean Expression Checkers Based on Binary Decision Trees
  Author: Tobias Nipkow
*)

theory Boolean_Expression_Checkers_AList_Mapping
  imports Main "HOL-Library.AList_Mapping" Boolean_Expression_Checkers
begin

section\<open>Tweaks for @{const AList_Mapping.Mapping}\<close>
                                                       
\<comment> \<open>If mappings are implemented by @{const AList_Mapping.Mapping}, the functions @{const reduce} and @{const normif} 
    search for x twice. The following code equations remove this redundant operation\<close>

lemma AList_Mapping_update: 
  "map_of m k = None \<Longrightarrow> Mapping.update k v (AList_Mapping.Mapping xs) = AList_Mapping.Mapping ((k,v)#xs)"
  by (metis Mapping.abs_eq map_of.simps(2) prod.sel(1) prod.sel(2) update_Mapping update_conv')

fun reduce_alist :: "('a * bool) list \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex"
where
  "reduce_alist xs (IF x t1 t2) = (case map_of xs x of
     None \<Rightarrow> mkIF x (reduce_alist ((x, True)#xs) t1) (reduce_alist ((x, False)#xs) t2) |
     Some b \<Rightarrow> reduce_alist xs (if b then t1 else t2))" 
| "reduce_alist _ t = t"

primrec normif_alist :: "('a * bool) list \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex \<Rightarrow> 'a ifex" 
where
  "normif_alist xs Trueif t1 t2 = reduce_alist xs t1" 
| "normif_alist xs Falseif t1 t2 = reduce_alist xs t2" 
| "normif_alist xs (IF x t1 t2) t3 t4 = (case map_of xs x of
    None \<Rightarrow> mkIF x (normif_alist ((x, True)#xs) t1 t3 t4) (normif_alist ((x, False)#xs) t2 t3 t4) |
    Some b \<Rightarrow> if b then normif_alist xs t1 t3 t4 else normif_alist xs t2 t3 t4)"
   
lemma reduce_alist_code [code, code_unfold]:
  "reduce (AList_Mapping.Mapping xs) t = reduce_alist xs t"
  by (induction t arbitrary: xs)
     (auto simp: AList_Mapping_update split: option.split)  

lemma normif_alist_code [code, code_unfold]:
  "normif (AList_Mapping.Mapping xs) t = normif_alist xs t"
  by (induction t arbitrary: xs)
     (fastforce simp: AList_Mapping_update reduce_alist_code split: option.split)+

lemmas empty_Mapping [code_unfold]

end
