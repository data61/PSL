chapter \<open>VT-Comp Library Setup\<close>
theory VTcomp
imports 
  Array_Map_Default
  Dynamic_Array
  (*Impl_List_Set_Ndj*)
  Synth_Definition
  Exc_Nres_Monad
begin

(* TODO: Move these stuff to AFP! *)


no_notation Ref.lookup ("!_" 61)
no_notation Ref.update ("_ := _" 62)

section \<open>Extra Stuff\<close>
text \<open>We added this stuff as preparation for the competition. \<close>

subsection \<open>Specialized Rules for Foreach Loops\<close>
lemma nfoldli_upt_rule:
  assumes INTV: "lb\<le>ub"
  assumes I0: "I lb \<sigma>0"
  assumes IS: "\<And>i \<sigma>. \<lbrakk> lb\<le>i; i<ub; I i \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f i \<sigma> \<le> SPEC (I (i+1))"
  assumes FNC: "\<And>i \<sigma>. \<lbrakk> lb\<le>i; i\<le>ub; I i \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes FC: "\<And>\<sigma>. \<lbrakk> I ub \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "nfoldli [lb..<ub] c f \<sigma>0 \<le> SPEC P"
  apply (rule nfoldli_rule[where I="\<lambda>l _ \<sigma>. I (lb+length l) \<sigma>"])
  apply simp_all
  apply (simp add: I0)
  subgoal using IS
    by (metis Suc_eq_plus1 add_diff_cancel_left' eq_diff_iff le_add1 length_upt upt_eq_lel_conv)
  subgoal for l1 l2 \<sigma> 
    apply (rule FNC[where i="lb + length l1"])
    apply (auto simp: INTV)
    using INTV upt_eq_append_conv by auto
  apply (rule FC) using INTV 
  by auto  


definition [enres_unfolds]: "efor (lb::int) ub f \<sigma> \<equiv> doE {
  EASSERT (lb\<le>ub);
  (_,\<sigma>) \<leftarrow> EWHILET (\<lambda>(i,\<sigma>). i<ub) (\<lambda>(i,\<sigma>). doE { \<sigma> \<leftarrow> f i \<sigma>; ERETURN (i+1,\<sigma>) }) (lb,\<sigma>);
  ERETURN \<sigma>
}"  
  
lemma efor_rule:
  assumes INTV: "lb\<le>ub"
  assumes I0: "I lb \<sigma>0"
  assumes IS: "\<And>i \<sigma>. \<lbrakk> lb\<le>i; i<ub; I i \<sigma> \<rbrakk> \<Longrightarrow> f i \<sigma> \<le> ESPEC E (I (i+1))"
  assumes FC: "\<And>\<sigma>. \<lbrakk> I ub \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "efor lb ub f \<sigma>0 \<le> ESPEC E P"
  unfolding efor_def
  supply EWHILET_rule[where R="measure (\<lambda>(i,_). nat (ub-i))" and I="\<lambda>(i,\<sigma>). lb\<le>i \<and> i\<le>ub \<and> I i \<sigma>", refine_vcg]
  apply refine_vcg
  apply auto
  using assms apply auto
  done
  
  
subsection \<open>Nicer do-notation for the nres-monad\<close>  
    
abbreviation (do_notation) bind_doN where "bind_doN \<equiv> Refine_Basic.bind"

notation (output) bind_doN (infixr "\<bind>" 54)
notation (ASCII output) bind_doN (infixr ">>=" 54)

nonterminal doN_binds and doN_bind
syntax
  "_doN_block" :: "doN_binds \<Rightarrow> 'a" ("doN {//(2  _)//}" [12] 62)
  "_doN_bind"  :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2_ \<leftarrow>/ _)" 13)
  "_doN_let" :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2let _ =/ _)" [1000, 13] 13)
  "_doN_then" :: "'a \<Rightarrow> doN_bind" ("_" [14] 13)
  "_doN_final" :: "'a \<Rightarrow> doN_binds" ("_")
  "_doN_cons" :: "[doN_bind, doN_binds] \<Rightarrow> doN_binds" ("_;//_" [13, 12] 12)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr "\<then>" 54)

syntax (ASCII)
  "_doN_bind" :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2_ <-/ _)" 13)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr ">>" 54)

translations
  "_doN_block (_doN_cons (_doN_then t) (_doN_final e))"
    \<rightleftharpoons> "CONST bind_doN t (\<lambda>_. e)"
  "_doN_block (_doN_cons (_doN_bind p t) (_doN_final e))"
    \<rightleftharpoons> "CONST bind_doN t (\<lambda>p. e)"
  "_doN_block (_doN_cons (_doN_let p t) bs)"
    \<rightleftharpoons> "let p = t in _doN_block bs"
  "_doN_block (_doN_cons b (_doN_cons c cs))"
    \<rightleftharpoons> "_doN_block (_doN_cons b (_doN_final (_doN_block (_doN_cons c cs))))"
  "_doN_cons (_doN_let p t) (_doN_final s)"
    \<rightleftharpoons> "_doN_final (let p = t in s)"
  "_doN_block (_doN_final e)" \<rightharpoonup> "e"
  "(m \<then> n)" \<rightharpoonup> "(m \<bind> (\<lambda>_. n))"
  

subsection \<open>Array Blit exposed to Sepref (Added after Competition)\<close>  

  definition "op_list_blit src si dst di len \<equiv> 
    (take di dst @ take len (drop si src) @ drop (di+len) dst)"

  context 
    notes op_list_blit_def[simp] 
  begin  
    sepref_decl_op (no_def) list_blit : 
      "op_list_blit" 
      :: "[\<lambda>((((src,si),dst),di),len). si+len \<le> length src \<and> di+len \<le> length dst]\<^sub>f  
        ((((\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r \<langle>A\<rangle>list_rel) \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel) \<rightarrow> \<langle>A\<rangle>list_rel" .
  end

  lemma blit_len[simp]: "si + len \<le> length src \<and> di + len \<le> length dst 
    \<Longrightarrow> length (op_list_blit src si dst di len) = length dst"
    by (auto simp: op_list_blit_def)
  
    
  context 
    notes [fcomp_norm_unfold] = array_assn_def[symmetric]
  begin    
    lemma array_blit_hnr_aux: 
          "(uncurry4 (\<lambda>src si dst di len. do { blit src si dst di len; return dst }), 
            uncurry4 mop_list_blit) 
      \<in> is_array\<^sup>k*\<^sub>anat_assn\<^sup>k*\<^sub>ais_array\<^sup>d*\<^sub>anat_assn\<^sup>k*\<^sub>anat_assn\<^sup>k \<rightarrow>\<^sub>a is_array"
      apply sepref_to_hoare
      apply (clarsimp simp: refine_pw_simps)
      apply (sep_auto simp: is_array_def op_list_blit_def)
      done
    
    sepref_decl_impl (ismop) array_blit: array_blit_hnr_aux .
  end  

end
