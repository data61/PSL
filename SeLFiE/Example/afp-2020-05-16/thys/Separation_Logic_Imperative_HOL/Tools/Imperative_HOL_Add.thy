section \<open>Additions to Imperative/HOL\<close>
theory Imperative_HOL_Add
imports "HOL-Imperative_HOL.Imperative_HOL" 
begin 

text \<open>This theory loads the Imperative HOL framework and provides 
        some additional lemmas needed for the separation logic framework.\<close> 

text \<open>A stronger elimination rule for \<open>ref\<close>\<close>

lemma effect_ref[effect_elims]:
  assumes "effect (ref (x::('a::heap))) h h' r"
  obtains "r = fst (Ref.alloc x h)" and "h' = snd (Ref.alloc x h)"
proof -
  from assms have "execute (ref x) h = Some (r, h')" by (unfold effect_def)
  then have "r = fst (Ref.alloc x h)" "h' = snd (Ref.alloc x h)" 
    by (auto simp add: execute_simps)
  then show thesis ..
qed


text \<open>Some lemmas about the evaluation of the limit for modifications on 
  a heap\<close>

lemma lim_Ref_alloc[simp]: "lim (snd (Ref.alloc x h)) = Suc (lim h)"
  unfolding Ref.alloc_def
  by (simp add: Let_def)

lemma lim_Array_alloc[simp]: "lim (snd (Array.alloc x h)) = Suc (lim h)"
  unfolding Array.alloc_def Array.set_def
  by (simp add: Let_def)


lemma lim_Array_set[simp]: "lim (Array.set a xs h) = lim h"
  unfolding Array.set_def
  by (simp add: Let_def)

thm Array.update_def
lemma lim_Array_update[simp]: "lim (Array.update a i x h) = lim h"
  unfolding Array.update_def
  by (simp add: Let_def)


text \<open>Simplification rules for the addresses of new allocated arrays and
  references\<close>

lemma addr_of_ref_alloc[simp]:
  "addr_of_ref (fst (Ref.alloc x h)) = lim h"
  unfolding Ref.alloc_def
  by (simp add: Let_def)

lemma addr_of_array_alloc[simp]:
  "addr_of_array (fst (Array.alloc x h)) = lim h"
  unfolding Array.alloc_def
  by (simp add: Let_def)

end
