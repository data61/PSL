theory Sepref_Misc
imports 
  Refine_Monadic.Refine_Monadic
  PO_Normalizer
  "List-Index.List_Index"
  Separation_Logic_Imperative_HOL.Sep_Main
  Named_Theorems_Rev
  "HOL-Eisbach.Eisbach"
  Separation_Logic_Imperative_HOL.Array_Blit
begin

  hide_const (open) CONSTRAINT

  (* Additions for List_Index *)  
  lemma index_of_last_distinct[simp]: 
    "distinct l \<Longrightarrow> index l (last l) = length l - 1"  
    apply (cases l rule: rev_cases)
    apply (auto simp: index_append)
    done

  lemma index_eqlen_conv[simp]: "index l x = length l \<longleftrightarrow> x\<notin>set l"
    by (auto simp: index_size_conv)


  subsection \<open>Iterated Curry and Uncurry\<close>    


  text \<open>Uncurry0\<close>  
  definition "uncurry0 c \<equiv> \<lambda>_::unit. c"
  definition curry0 :: "(unit \<Rightarrow> 'a) \<Rightarrow> 'a" where "curry0 f = f ()"
  lemma uncurry0_apply[simp]: "uncurry0 c x = c" by (simp add: uncurry0_def)

  lemma curry_uncurry0_id[simp]: "curry0 (uncurry0 f) = f" by (simp add: curry0_def)
  lemma uncurry_curry0_id[simp]: "uncurry0 (curry0 g) = g" by (auto simp: curry0_def)
  lemma param_uncurry0[param]: "(uncurry0,uncurry0) \<in> A \<rightarrow> (unit_rel\<rightarrow>A)" by auto
    
  text \<open>Abbreviations for higher-order uncurries\<close>    
  abbreviation "uncurry2 f \<equiv> uncurry (uncurry f)"
  abbreviation "curry2 f \<equiv> curry (curry f)"
  abbreviation "uncurry3 f \<equiv> uncurry (uncurry2 f)"
  abbreviation "curry3 f \<equiv> curry (curry2 f)"
  abbreviation "uncurry4 f \<equiv> uncurry (uncurry3 f)"
  abbreviation "curry4 f \<equiv> curry (curry3 f)"
  abbreviation "uncurry5 f \<equiv> uncurry (uncurry4 f)"
  abbreviation "curry5 f \<equiv> curry (curry4 f)"
  abbreviation "uncurry6 f \<equiv> uncurry (uncurry5 f)"
  abbreviation "curry6 f \<equiv> curry (curry5 f)"
  abbreviation "uncurry7 f \<equiv> uncurry (uncurry6 f)"
  abbreviation "curry7 f \<equiv> curry (curry6 f)"
  abbreviation "uncurry8 f \<equiv> uncurry (uncurry7 f)"
  abbreviation "curry8 f \<equiv> curry (curry7 f)"
  abbreviation "uncurry9 f \<equiv> uncurry (uncurry8 f)"
  abbreviation "curry9 f \<equiv> curry (curry8 f)"

    
    
  lemma fold_partial_uncurry: "uncurry (\<lambda>(ps, cf). f ps cf) = uncurry2 f" by auto

  lemma curry_shl: 
    "\<And>g f. (g \<equiv> curry f) \<equiv> (uncurry g \<equiv> f)"
    "\<And>g f. (g \<equiv> curry0 f) \<equiv> (uncurry0 g \<equiv> f)"
    by (atomize (full); auto)+
  
  lemma curry_shr: 
    "\<And>f g. (curry f \<equiv> g) \<equiv> (f \<equiv> uncurry g)"
    "\<And>f g. (curry0 f \<equiv> g) \<equiv> (f \<equiv> uncurry0 g)"
    by (atomize (full); auto)+
  
  lemmas uncurry_shl = curry_shr[symmetric]  
  lemmas uncurry_shr = curry_shl[symmetric]  
  
end
