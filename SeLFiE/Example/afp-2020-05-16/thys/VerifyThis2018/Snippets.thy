chapter \<open>Code Snippets\<close>
theory Snippets
imports "lib/VTcomp"
begin

  section \<open>Find Element in Array (Arrays)\<close>

  definition "find_elem (x::int) xs \<equiv> doN {
    WHILEIT (\<lambda>i. i\<le>length xs \<and> x\<notin>set (take i xs)) (\<lambda>i. i<length xs \<and> xs!i\<noteq>x) (\<lambda>i. RETURN (i+1)) 0
  }"
  
  lemma find_elem_correct: "find_elem x xs \<le> SPEC (\<lambda>i. i\<le>length xs \<and> (i<length xs \<longrightarrow> xs!i = x))"
    unfolding find_elem_def
    apply refine_vcg
    apply (rule wf_measure[of "\<lambda>i. length xs - i"])
    apply (auto simp: in_set_conv_nth)
    (*sledgehammer*)
    using less_Suc_eq by blast
    
  sepref_definition find_elem_impl is "uncurry find_elem" :: "int_assn\<^sup>k *\<^sub>a (array_assn int_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    unfolding find_elem_def short_circuit_conv
    by sepref
  
  export_code find_elem_impl in Haskell module_name test

  
  subsection \<open>Combined Correctness Theorem\<close>  
  lemma find_elem_r1: "(find_elem, \<lambda> x xs. SPEC (\<lambda>i. i\<le>length xs \<and> (i<length xs \<longrightarrow> xs!i = x))) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    using find_elem_correct by (auto intro: nres_relI)
  
  thm find_elem_impl.refine[FCOMP find_elem_r1]
  

  section \<open>Check Prefix (Arrays, Exceptions: Check)\<close>
    
  definition "check_prefix xs ys \<equiv> doE {
    CHECK (length xs \<le> length ys) ();
    EWHILEIT (\<lambda>i. i\<le>length xs \<and> take i xs = take i ys) (\<lambda>i. i<length xs) (\<lambda>i. doE { 
      EASSERT (i<length xs \<and> i<length ys); 
      CHECK (xs!i = ys!i) (); 
      ERETURN (i+1) 
    } ) 0;
    ERETURN ()
  }"
  
  (* ESPEC Exc Normal ! *)
  lemma check_prefix_correct: "check_prefix xs ys \<le> ESPEC (\<lambda>_. xs \<noteq> take (length xs) ys) (\<lambda>_. xs = take (length xs) ys)"
    unfolding check_prefix_def
    apply (refine_vcg EWHILEIT_rule[where R="measure (\<lambda>i. length xs - i)"])
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    subgoal
      by (simp add: take_Suc_conv_app_nth)
    apply auto []
    apply auto []
    subgoal 
      by (metis nth_take)
    subgoal 
      by force
    apply auto []
    done
  
  synth_definition check_prefix_bd is [enres_unfolds]: "check_prefix xs ys = \<hole>"
    apply (rule CNV_eqD)
    unfolding check_prefix_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
    
  sepref_definition check_prefix_impl is "uncurry check_prefix_bd" 
    :: "(array_assn int_assn)\<^sup>k *\<^sub>a (array_assn int_assn)\<^sup>k \<rightarrow>\<^sub>a (unit_assn +\<^sub>a unit_assn)"
    unfolding check_prefix_bd_def
    by sepref
  
  export_code check_prefix_impl checking SML_imp

  subsection \<open>Modularity\<close>
    
  lemmas [refine_vcg] = check_prefix_correct[THEN ESPEC_trans]
  thm SPEC_trans (* for plain nres-monad without exceptions *)
    
  (* TODO: I remember to have automated the order_trans transformation, but cannot find it right now. *)
  

  definition "is_prefix' xs ys \<equiv> CATCH (doE {check_prefix xs ys; ERETURN True }) (\<lambda>_. ERETURN False)"  
  
  lemma is_prefix'_correct: "is_prefix' xs ys \<le> ESPEC (\<lambda>_. False) (\<lambda>r. r \<longleftrightarrow> xs = take (length xs) ys)"
    unfolding is_prefix'_def
    apply refine_vcg
    by auto
  
  lemmas [sepref_fr_rules] = check_prefix_impl.refine  
  sepref_register check_prefix_bd :: "'a list \<Rightarrow> 'a list \<Rightarrow> (unit+unit) nres"
    (* Optional interface type. Required if interfaces used that do not match Isabelle types, e.g. i_map, i_mtx, \<dots>*)

  synth_definition is_prefix_bd' is [enres_unfolds]: "is_prefix' xs ys = \<hole>"
    apply (rule CNV_eqD)
    unfolding is_prefix'_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
    
  sepref_definition is_prefix_impl' is "uncurry is_prefix_bd'" 
    :: "(array_assn int_assn)\<^sup>k *\<^sub>a (array_assn int_assn)\<^sup>k \<rightarrow>\<^sub>a (unit_assn +\<^sub>a bool_assn)"
    unfolding is_prefix_bd'_def
    by sepref
  
  export_code is_prefix_impl' checking SML_imp
  
  
      

  section \<open>Is Prefix (Arrays, Exceptions: Catch)\<close>
  
  definition "is_prefix xs ys \<equiv> CATCH (doE {
    CHECK (length xs \<le> length ys) False;
    EWHILEIT (\<lambda>i. i\<le>length xs \<and> take i xs = take i ys) (\<lambda>i. i<length xs) (\<lambda>i. doE { 
      EASSERT (i<length xs \<and> i<length ys); 
      CHECK (xs!i = ys!i) False;
      ERETURN (i+1) 
    } ) 0;
    THROW True
  }) (ERETURN)"
  
  (* ESPEC Exc Normal ! *)
  lemma "is_prefix xs ys \<le> ESPEC (\<lambda>_. False) (\<lambda>r. r \<longleftrightarrow> xs = take (length xs) ys)"
    unfolding is_prefix_def
    apply (refine_vcg EWHILEIT_rule[where R="measure (\<lambda>i. length xs - i)"])
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    subgoal
      by (simp add: take_Suc_conv_app_nth)
    apply auto []
    apply auto []
    subgoal 
      by (metis nth_take)
    subgoal 
      by force
    apply auto []
    done
  
  synth_definition is_prefix_bd is [enres_unfolds]: "is_prefix xs ys = \<hole>"
    apply (rule CNV_eqD)
    unfolding is_prefix_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
    
  sepref_definition is_prefix_impl is "uncurry is_prefix_bd" 
    :: "(array_assn int_assn)\<^sup>k *\<^sub>a (array_assn int_assn)\<^sup>k \<rightarrow>\<^sub>a (unit_assn +\<^sub>a bool_assn)"
    unfolding is_prefix_bd_def
    by sepref
  
  export_code is_prefix_impl checking SML_imp
  
  
  
  
  
  
  
  
  
  section \<open>Copy Array (Arrays, For i=l..u)\<close>  
  
  definition "cp_array xs \<equiv> doN {
    let ys = op_array_replicate (length xs) 0;   \<comment> \<open>Use proper constructors\<close>
    
    ys \<leftarrow> nfoldli [0..<length xs] (\<lambda>_. True) (\<lambda>i ys. doN {  \<comment> \<open>Ensure linearity! \<open>ys\<leftarrow>\<dots>\<close>\<close>
      ASSERT (i<length xs \<and> i<length ys); 
      RETURN (ys[i:=xs!i]) 
    }) ys;
    
    RETURN ys
  }"

  
  lemma "cp_array xs \<le> SPEC (\<lambda>ys. ys=xs)"
    unfolding cp_array_def
    supply nfoldli_rule nfoldli_rule[where I="\<lambda>l1 l2 ys. length ys = length xs \<and> (\<forall>i\<in>set l1. ys!i = xs!i)", refine_vcg]
    apply refine_vcg
    apply auto
    subgoal 
      using upt_eq_lel_conv by blast
    subgoal
      using upt_eq_lel_conv by blast
    subgoal 
      by (simp add: nth_list_update)
    subgoal 
      by (simp add: nth_equalityI)
    done  
    

  term arl_assn  
    
  subsection \<open>Proof with \<open>nfoldli_upt_rule\<close>\<close>  
  lemma "cp_array xs \<le> SPEC (\<lambda>ys. ys=xs)"
    unfolding cp_array_def
    supply nfoldli_upt_rule nfoldli_upt_rule[where I="\<lambda>i ys. length ys = length xs \<and> (\<forall>j<i. ys!j = xs!j)", refine_vcg]
    apply refine_vcg
    apply auto
    subgoal
      using less_Suc_eq by auto 
    subgoal
      by (simp add: nth_equalityI)
    done
      
  
    
  sepref_definition cp_array_impl is cp_array :: "(array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a array_assn nat_assn"
    unfolding cp_array_def
    by sepref
  
  
  
end
