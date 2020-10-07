theory SM_Datastructures
imports Main 
  CAVA_Base.CAVA_Base
  "../Lib/SOS_Misc_Add"
  DFS_Framework.Feedback_Arcs (* TODO: Only for oo-symbol !?*)

begin

  lemma [code_unfold]: "{(a,b). (a,b)\<in>X \<and> P a b} = Set.filter (\<lambda>(a,b). P a b) X"
    by auto

  lemma in_dom_map_code[code_unfold]: 
    "x\<in>dom m = (case m x of None \<Rightarrow> False | _ \<Rightarrow> True)"
    by (auto split: option.splits)

  (* TODO: Move to gen_set. Generic algorithm for set_of_list *)
  lemma set_by_fold: "set l = fold insert l {}"
  proof -
    {
      fix s
      have "fold insert l s = s \<union> set l"
        by (induction l arbitrary: s) auto
    } from this[of "{}"] show ?thesis by simp
  qed

  context
  begin

    interpretation autoref_syn .

    lemma [autoref_itype]: "set ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set" by simp

  end

  lemma gen_set[autoref_rules_raw]:
    fixes R :: "('c\<times>'a)set" and Rs :: "('c\<times>'a) set \<Rightarrow> (_\<times>'a set) set"
    assumes [simplified,param]:
      "GEN_OP em {} (\<langle>R\<rangle>Rs)"
      "GEN_OP ins insert (R \<rightarrow> \<langle>R\<rangle>Rs \<rightarrow> \<langle>R\<rangle>Rs)"
    shows "(\<lambda>li. fold ins li em,set)\<in>\<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>Rs"
      unfolding set_by_fold[abs_def]
      by parametricity

  schematic_goal
    shows "(?c,set [1,2,3::nat])\<in>\<langle>nat_rel\<rangle>dflt_ahs_rel"
      using [[autoref_trace_failed_id]]
      by (autoref (trace, keep_goal))

  (* TODO: Possibly, we can drop the
    find_min_idx_f - stuff, and formalize our ample-set 
    using the abstract LEAST, which is then implemented
    by collecti_index.
  *)

  text \<open>Find minimum index and result where function returns non-none value\<close>
  primrec find_min_idx_f :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a list \<rightharpoonup> (nat \<times> 'b)" where
    "find_min_idx_f f [] = None"
  | "find_min_idx_f f (x#xs) = (
      case f x of 
        Some r \<Rightarrow> Some (0,r) 
      | None \<Rightarrow> map_option (map_prod Suc id) (find_min_idx_f f xs)
    )"
  
  lemma find_min_idx_f_None_conv: 
    "find_min_idx_f f l = None \<longleftrightarrow> (\<forall>a\<in>set l. f a = None)"
    apply (induction l)
    apply (auto split: option.splits)
    done

  lemma find_min_idx_f_SomeD:
    "find_min_idx_f f l = Some (i,r) \<Longrightarrow> f (l!i) = Some r \<and> i < length l"
    by (induction l arbitrary: i) (auto split: if_split_asm option.splits)

  lemma find_min_idx_f_SomeD_complete: 
    "find_min_idx_f f l = Some (i,r) 
      \<Longrightarrow> (f (l!i) = Some r \<and> i < length l \<and> (\<forall>j<i. f (l!j) = None))"
    apply (induction l arbitrary: i) 
    apply (auto split: if_split_asm option.splits)
    apply (case_tac j)
    apply auto
    done

  lemma find_min_idx_f_LEAST_eq: "find_min_idx_f f l = (
    if \<exists>i<length l. f (l!i) \<noteq> None then
      let i = LEAST i. i<length l \<and> f (l!i) \<noteq> None in Some (i,the (f (l!i)))
    else
      None
  )"
  proof (cases "find_min_idx_f f l")
    case None
    show ?thesis using None by (auto simp: find_min_idx_f_None_conv)
  next
    case (Some a)
    obtain i r where 1: "a = (i, r)" by force
    have 2: "f (l ! i) = Some r" "i < length l" "\<forall> j < i. f (l ! j) = None"
      using find_min_idx_f_SomeD_complete[OF Some[unfolded 1]] by auto
    have 3: "(LEAST i. i < length l \<and> (\<exists> y. f (l ! i) = Some y)) = i"
      using 2 linorder_neqE_nat by (force intro!: Least_equality)
    show ?thesis unfolding Some 1 using 2 3 by auto
  qed  

  primrec collect_indexr' :: "nat \<Rightarrow> (nat\<times>'b) set \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'b set) \<Rightarrow> 'a list \<Rightarrow> (nat\<times>'b) set" where
    "collect_indexr' i a c [] = a"
  | "collect_indexr' i a c (x#xs) = (collect_indexr' (Suc i) (a\<union>({i} \<times> c i x)) c xs)"  

  abbreviation "collect_indexr \<equiv> collect_indexr' 0 {}"

  lemma collect_indexr'_collect: "collect_indexr' i0 a f l 
    = a \<union> {(i0+i,x) | i x. i<length l \<and> x\<in>f (i0+i) (l!i)}"
    apply (induction l arbitrary: i0 a)
    apply simp
    apply simp
    apply auto
    apply (case_tac i, auto)
    apply (case_tac i, auto)
    done

  lemma collect_indexr_collect: "collect_indexr f l 
    = {(i,x) | i x. i<length l \<and> x\<in>f i (l!i)}"  
    by (simp add: collect_indexr'_collect)
  

  primrec collecti_index' :: "nat \<Rightarrow> (nat\<times>'b) set \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> (bool \<times> 'b set)) \<Rightarrow> 'a list \<Rightarrow> (nat\<times>'b) set" where
    "collecti_index' i a c [] = a"
  | "collecti_index' i a c (x#xs) = (case c i x of
      (False,s) \<Rightarrow> collecti_index' (Suc i) (a \<union> {i}\<times>s) c xs
    | (True,s) \<Rightarrow> {i}\<times>s)"

  abbreviation "collecti_index \<equiv> collecti_index' 0 {}"

  lemma collecti_index'_collect: "collecti_index' i0 a0 f l 
    = (
      if \<exists>i<length l. fst (f (i0+i) (l!i)) then
        let i=LEAST i . i<length l \<and> fst (f (i0+i) (l!i)) in {i0+i} \<times> snd (f (i0+i) (l!i))
      else
        a0 \<union> {(i0+i,x) | i x. i<length l \<and> x\<in>snd (f (i0+i) (l!i))})"
  proof (cases "\<exists>i<length l. fst (f (i0+i) (l!i))")
    case False
    note False[simp]
    hence "\<forall>i<length l. \<not>fst (f (i0+i) (l!i))" by blast
    hence "collecti_index' i0 a0 f l = collect_indexr' i0 a0 (snd oo f) l"
    proof (induction l arbitrary: i0 a0)
      case (Cons x l)
      from Cons.prems have "\<not>fst (f i0 x)" by auto
      hence [simp]: "\<And>v. f i0 x \<noteq> (True,v)" by auto
      have "collecti_index' i0 a0 f (x#l) = 
        collecti_index' (Suc i0) (a0 \<union> {i0} \<times> (snd (f i0 x))) f l" 
        by (simp split: prod.splits bool.splits)
      also have "\<dots> = collect_indexr' (Suc i0) ((a0 \<union> {i0} \<times> (snd (f i0 x)))) (snd oo f) l" 
        apply (subst Cons.IH)
        using Cons.prems
        by auto
      finally have 1: "collecti_index' i0 a0 f (x # l) =
        collect_indexr' (Suc i0) (a0 \<union> {i0} \<times> snd (f i0 x)) (snd \<circ>\<circ> f) l" . 
      show ?case by (subst 1) simp
    qed simp
    also note collect_indexr'_collect
    finally show ?thesis by simp
  next
    case True
    note True[simp]
    define im where "im \<equiv> \<lambda>l (i0::nat). LEAST i . i<length l \<and> fst (f (i0+i) (l!i))"
    from LeastI_ex[OF True] have 
      1: "im l i0<length l" "fst (f (i0+im l i0) (l!im l i0))" 
      unfolding im_def by (auto) 
    have 2: "\<forall>i<im l i0. \<not> fst (f (i0+i) (l!i))"
    proof safe
      fix i
      assume A: "i<im l i0" with 1 have "i<length l" by simp
      moreover assume "fst (f (i0+i) (l!i))"
      ultimately have "im l i0 \<le> i"
        unfolding im_def by (auto intro: Least_le)
      with A show False by simp  
    qed  

    from 1 2 have "collecti_index' i0 a0 f l = {i0+im l i0} \<times> snd (f (i0+im l i0) (l!im l i0))"
    proof (induction l arbitrary: i0 a0)
      case (Cons x l)
      show ?case proof (cases "fst (f i0 x)")
        case True
        hence [simp]: "\<And>y. f i0 x \<noteq> (False,y)" by auto
        note [simp] = True        

        from Cons.prems(3) have [simp]: "im (x#l) i0 = 0"
          by auto

        thus ?thesis
          by (auto split: prod.splits bool.splits)
      next
        case False
        hence "im (x#l) i0 = Suc (im l (Suc i0))"
          unfolding im_def
          apply (subst Least_Suc)
          apply (rule conjI) 
          apply (rule Cons.prems)+
          apply simp
          apply simp
          done
        hence ims: "im (x#l) i0 > 0" "im l (Suc i0) = im (x#l) i0 - 1" 
          by simp_all

        from False have 1: "collecti_index' i0 a0 f (x # l) 
          = collecti_index' (Suc i0) (a0 \<union> {i0} \<times> (snd (f i0 x))) f l"
          by (auto)

        show ?thesis
          apply (subst 1)
          apply (subst Cons.IH)
          using Cons.prems(1) ims apply (simp)
          using Cons.prems(2) ims apply simp
          using Cons.prems(3)
          apply (auto simp: ims nth_Cons less_diff_conv split: nat.splits) []
          using ims(1) apply (auto simp: ims(2))
          done
      qed
    qed simp
    thus ?thesis
      by (simp add: im_def)

  qed      

  lemma collecti_index_collect: "collecti_index f l 
    = (
      if \<exists>i<length l. fst (f i (l!i)) then
        let i=LEAST i . i<length l \<and> fst (f i (l!i)) in {i} \<times> snd (f i (l!i))
      else
        {(i,x) | i x. i<length l \<and> x\<in>snd (f i (l!i))})"
    using collecti_index'_collect[of 0 "{}" f l]
    by (simp cong: if_cong)

  primrec collecti_index'_list :: "nat \<Rightarrow> (nat\<times>'b) list \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> (bool \<times> 'b list)) \<Rightarrow> 'a list \<Rightarrow> (nat\<times>'b) list" where
    "collecti_index'_list i a c [] = a"
  | "collecti_index'_list i a c (x#xs) = (case c i x of
      (False,s) \<Rightarrow> collecti_index'_list (Suc i) (a @ map (Pair i) s) c xs
    | (True,s) \<Rightarrow> map (Pair i) s)"

  abbreviation "collecti_index_list \<equiv> collecti_index'_list 0 []"

  lemma collecti_index'_list_invar:
    assumes "\<And>i x b l. c i x = (b,l) \<Longrightarrow> distinct l"
    assumes "fst`set a \<subseteq> {0..<i0}" "distinct a"
    shows "distinct (collecti_index'_list i0 a c l)"
    using assms
    apply (induction l arbitrary: i0 a)
    apply simp
    apply (auto split: prod.splits bool.splits simp: nth_Cons' distinct_map)
    apply rprems
    apply (auto simp: distinct_map)
    done

  lemma image_Pair_eq_prod_sng[simp]: "Pair x ` s = {x}\<times>s" by auto  

  lemma collecti_index'_list_\<alpha>: 
    assumes "\<And>i x b l. ci i x = (b,l) \<Longrightarrow> c i x = (b,set l)"
    shows 
      "set (collecti_index'_list i0 ai ci l) = collecti_index' i0 (set ai) c l"
  proof -
    from assms have A: "\<And>i x b s. c i x = (b,s) \<longleftrightarrow> (\<exists>l. ci i x = (b, l) \<and> s=set l)"
      apply auto apply (case_tac "ci i x") apply auto done

    show ?thesis  
      apply (induction l arbitrary: i0 ai)
      apply simp
      apply simp
      apply (split prod.split, clarsimp)
      apply (split bool.split, clarsimp, intro allI impI conjI)
      apply (force simp add: A) []
  
      apply (simp split: prod.splits bool.splits add: A)
      apply safe
      apply simp_all
      apply blast
      done
  qed

  lemma collecti_index_list_refine:
    "(collecti_index_list,collecti_index)\<in>
       (nat_rel \<rightarrow> Id \<rightarrow> bool_rel \<times>\<^sub>r \<langle>Id\<rangle>list_set_rel) \<rightarrow> \<langle>Id\<rangle>list_rel 
    \<rightarrow> \<langle>nat_rel\<times>\<^sub>rId\<rangle>list_set_rel"
    apply (intro fun_relI)
    apply (simp add: list_set_rel_def)
    apply (rule brI)

    apply (simp add: br_def)
    apply (rule collecti_index'_list_\<alpha>[of _ _ 0 "[]", simplified, symmetric])
    apply (drule_tac x=i and x'=i in fun_relD, simp)
    apply (drule_tac x=x and x'=x in fun_relD, simp)
    apply (auto simp: prod_rel_def) []

    apply (rule collecti_index'_list_invar)
    apply auto
    apply (drule_tac x=i and x'=i in fun_relD, simp)
    apply (drule_tac x=x and x'=x in fun_relD, simp)
    apply (auto simp: prod_rel_def br_def) []
    done





end

