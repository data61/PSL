section \<open>Shorter Solution\<close>
theory Challenge1_short
imports "lib/VTcomp"
begin

text \<open>Small specification of textbuffer ADT,
  and its implementation by a gap buffer.
  
  Annotated and elaborated version of just the challenge requirements.
\<close>
subsection \<open>Abstract Specification\<close>

  datatype 'a textbuffer = BUF ("pos": "nat") ("text": "'a list")
  \<comment> \<open>Note that we do not model the abstract invariant --- pos in range --- here,
    as it is not strictly required for the challenge spec.\<close>

  text \<open>These are the operations that were specified in the challenge.
    Note: Isabelle has type inference, so we do not need to specify types.
    Note: We exploit that, in Isabelle, we have @{lemma "(0::nat)-1=0" by simp}.
  \<close>
  primrec move_left where "move_left (BUF p t) = BUF (p-1) t" 
  primrec move_right where "move_right (BUF p t) = BUF (min (length t) (p+1)) t"
  primrec insert where "insert x (BUF p t) = BUF (p+1) (take p t@x#drop p t)"
  primrec delete where "delete (BUF p t) = BUF (p-1) (take (p-1) t@drop p t)"
  
subsection \<open>Refinement 1: List with Gap\<close>  
  
  subsection \<open>Implementation on List-Level\<close>  
  type_synonym 'a gap_buffer = "nat \<times> nat \<times> 'a list"

  subsubsection \<open>Abstraction Relation\<close>
  text \<open>We define an invariant on the concrete gap-buffer, and its mapping to the
    abstract model. From these two, we define a relation \<open>gap_rel\<close> between
    concrete and abstract buffers. \<close>
  definition "gap_\<alpha> \<equiv> \<lambda>(l,r,buf). BUF l (take l buf @ drop r buf)"
  definition "gap_invar \<equiv> \<lambda>(l,r,buf). l\<le>r \<and> r\<le>length buf"
  abbreviation "gap_rel \<equiv> br gap_\<alpha> gap_invar"

  subsubsection \<open>Left\<close>
  
  text \<open>For the operations, we insert assertions. These are not required to prove
    the list-level specification correct (during the proof, they are inferred easily).
    However, they are required in the subsequent automatic refinement step to arrays,
    to give our tool the information that all indexes are, indeed, in bounds.\<close>
  
  definition "move_left1 \<equiv> \<lambda>(l,r,buf). doN {
    if l\<noteq>0 then doN {
      ASSERT(r-1<length buf \<and> l-1<length buf);
      RETURN (l-1,r-1,buf[r-1:=buf!(l-1)])
    } else RETURN (l,r,buf)
  }"

  lemma move_left1_correct: 
    "(move_left1, RETURN o move_left) \<in> gap_rel \<rightarrow> \<langle>gap_rel\<rangle>nres_rel"
    apply clarsimp
    unfolding move_left1_def
    apply refine_vcg
    apply (auto 
      simp: in_br_conv gap_\<alpha>_def gap_invar_def move_left1_def 
      split: prod.splits)
    (* sledgehammer! *)  
    by (smt Cons_nth_drop_Suc Suc_pred append.assoc append_Cons append_Nil 
      diff_Suc_less drop_update_cancel hd_drop_conv_nth length_list_update 
      less_le_trans nth_list_update_eq take_hd_drop)  

  subsubsection \<open>Right\<close>        
  definition "move_right1 \<equiv> \<lambda>(l,r,buf). doN {
    if r<length buf then doN {
      ASSERT (l<length buf);
      RETURN (l+1,r+1,buf[l:=buf!r])
    } else RETURN (l,r,buf)
  }"
    
  lemma move_right1_correct: 
    "(move_right1,RETURN o move_right) \<in> gap_rel \<rightarrow> \<langle>gap_rel\<rangle>nres_rel"
    apply clarsimp
    unfolding move_right1_def
    apply refine_vcg
    unfolding gap_\<alpha>_def gap_invar_def
    apply (auto simp: in_br_conv split: prod.split)
    (* sledgehammer *)
    by (metis Cons_eq_appendI Cons_nth_drop_Suc append_eq_append_conv2 
      atd_lem drop_0 dual_order.strict_trans2 take_eq_Nil take_update_last)
    (* Manual: by (simp add: hd_drop_conv_nth take_update_last Cons_nth_drop_Suc) *)
        
  subsubsection \<open>Insert and Grow\<close>
     
  definition "can_insert \<equiv> \<lambda>(l,r,buf). l<r"
  
  definition "grow1 K \<equiv> \<lambda>(l,r,buf). doN {
    let b = op_array_replicate (length buf + K) default;
    b \<leftarrow> mop_list_blit buf 0 b 0 l;
    b \<leftarrow> mop_list_blit buf r b (r+K) (length buf - r);
    RETURN (l,r+K,b)
  }"
  \<comment> \<open>Note: Most operations have also a variant prefixed with \<open>mop\<close>.
    These are defined in the refinement monad and already contain the assertion 
    of their precondition. The backside is that they cannot be easily used in as part
    of expressions, e.g., in @{term "buf[l:=buf!r]"}, we would have to explicitly bind
    each intermediate value: @{term "doN { v \<leftarrow> mop_list_get buf r; mop_list_set buf l v }"}.
  \<close>
  
  lemma grow1_correct[THEN SPEC_trans, refine_vcg]: 
    \<comment> \<open>Declares this as a rule to be used by the VCG\<close>
    assumes "gap_invar gb"
    shows "grow1 K gb \<le> (SPEC (\<lambda>gb'. 
        gap_invar gb' 
      \<and> gap_\<alpha> gb' = gap_\<alpha> gb 
      \<and> (K>0 \<longrightarrow> can_insert gb')))"
    unfolding grow1_def
    apply refine_vcg    
    using assms
    unfolding gap_\<alpha>_def gap_invar_def can_insert_def
    apply clarsimp_all
    apply (auto simp: op_list_blit_def)
    by (simp add: min_def)  
  
  definition "insert1 x \<equiv> \<lambda>(l,r,buf). doN {
    (l,r,buf) \<leftarrow> 
      if (l=r) then grow1 (length buf+1) (l,r,buf) else RETURN (l,r,buf);
    ASSERT (l<length buf);
    RETURN (l+1,r,buf[l:=x])
  }" 
  
  lemma insert1_correct: 
    "(insert1,RETURN oo insert) \<in> Id \<rightarrow> gap_rel \<rightarrow> \<langle>gap_rel\<rangle>nres_rel"
    apply clarsimp
    unfolding insert1_def
    apply refine_vcg \<comment> \<open>VCG knows the rule for grow1 already\<close>
    unfolding insert_def gap_\<alpha>_def gap_invar_def can_insert_def
    apply (auto simp: in_br_conv take_update_last split: prod.split)
    done
  

  subsubsection \<open>Delete\<close>
  definition "delete1 
    \<equiv> \<lambda>(l,r,buf). if l>0 then RETURN (l-1,r,buf) else RETURN (l,r,buf)" 
  lemma delete1_correct: 
    "(delete1,RETURN o delete) \<in> gap_rel \<rightarrow> \<langle>gap_rel\<rangle>nres_rel"
    apply clarsimp
    unfolding delete1_def
    apply refine_vcg
    unfolding gap_\<alpha>_def gap_invar_def
    by (auto simp: in_br_conv butlast_take split: prod.split)
  
subsection \<open>Imperative Arrays\<close>  
  text \<open>The following indicates how we will further refine the gap-buffer:
    The list will become an array, the indices and the content will not be 
    refined (expressed by @{const nat_assn} and @{const id_assn}).
  \<close>
  abbreviation "gap_impl_assn \<equiv> nat_assn \<times>\<^sub>a nat_assn \<times>\<^sub>a array_assn id_assn"  
  
  sepref_definition move_left_impl 
    is move_left1 :: "gap_impl_assn\<^sup>d\<rightarrow>\<^sub>agap_impl_assn"
    unfolding move_left1_def by sepref

  sepref_definition move_right_impl 
    is move_right1 :: "gap_impl_assn\<^sup>d\<rightarrow>\<^sub>agap_impl_assn"
    unfolding move_right1_def by sepref
  
  sepref_definition insert_impl 
    is "uncurry insert1" :: "id_assn\<^sup>k*\<^sub>agap_impl_assn\<^sup>d\<rightarrow>\<^sub>agap_impl_assn"
    unfolding insert1_def grow1_def by sepref 
    \<comment> \<open>We inline @{const grow1} here\<close>
    
  sepref_definition delete_impl 
    is delete1 :: "gap_impl_assn\<^sup>d\<rightarrow>\<^sub>agap_impl_assn"
    unfolding delete1_def by sepref
  
  
  text \<open>Finally, we combine the two refinement steps, to get overall correctness theorems\<close>  
  definition "gap_assn \<equiv> hr_comp gap_impl_assn gap_rel" 
    \<comment> \<open>@{const hr_comp} is composition of refinement relations\<close>
  context notes gap_assn_def[symmetric,fcomp_norm_unfold] begin
    lemmas move_left_impl_correct = move_left_impl.refine[FCOMP move_left1_correct]
       and move_right_impl_correct = move_right_impl.refine[FCOMP move_right1_correct]
       and insert_impl_correct = insert_impl.refine[FCOMP insert1_correct]
       and delete_impl_correct = delete_impl.refine[FCOMP delete1_correct]
    text \<open>Proves:
      @{thm [display] move_left_impl_correct}
      @{thm [display] move_right_impl_correct}
      @{thm [display] insert_impl_correct}
      @{thm [display] delete_impl_correct}
    \<close>
       
  
  end
  
subsection \<open>Executable Code\<close>  
  text \<open>Isabelle/HOL can generate code in various target languages.\<close>

  export_code move_left_impl move_right_impl insert_impl delete_impl  
    in SML_imp module_name Gap_Buffer
    in OCaml_imp module_name Gap_Buffer
    in Haskell module_name Gap_Buffer
    in Scala module_name Gap_Buffer
    
        
end
