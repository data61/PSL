section \<open>Challenge 3\<close>
theory Challenge3
  imports Parallel_Multiset_Fold Refine_Imperative_HOL.IICF
begin

text \<open>Problem definition:
\<^url>\<open>https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Verify%20This/Challenges%202019/sparse_matrix_multiplication.pdf\<close>\<close>

subsection \<open>Single-Threaded Implementation\<close>
text \<open>We define type synonyms for values (which we fix to integers here) and 
  triplets, which are a pair of coordinates and a value.
\<close>
type_synonym val = int
type_synonym triplet = "(nat \<times> nat) \<times> val"

text \<open>We fix a size \<open>n\<close> for the vector.\<close>
context 
  fixes n :: nat 
begin

  text \<open>An algorithm finishing triples in any order.
  \<close>
  definition
    "alg (ts :: triplet list) x = fold_mset (\<lambda>((r,c),v) y. y(c:=y c + x r * v)) (\<lambda>_. 0 :: int) (mset ts)"

  text \<open>
    We show that the folding function is commutative, i.e., the order of the folding does not matter.
    We will use this below to show that the computation can be parallelized.
  \<close>  
  interpretation comp_fun_commute "(\<lambda>((r, c), v) y. y(c := (y c :: val) + x r * v))"
    apply unfold_locales
    apply (auto intro!: ext)
    done

  subsection \<open>Specification\<close>
  text \<open>Abstraction function, mapping a sparse matrix to a function from coordinates to values.\<close>
  definition \<alpha> :: "triplet list \<Rightarrow> (nat \<times> nat) \<Rightarrow> val" where 
    "\<alpha> = the_default 0 oo map_of"

  text \<open>Abstract product.\<close>
  definition "pr m x i \<equiv> \<Sum>k=0..<n. x k * m (k, i)"    

  subsection \<open>Correctness\<close>

  lemma aux: 
    "
    distinct (map fst (ts1@ts2)) \<Longrightarrow>
    the_default (0::val) (case map_of ts1 (k, i) of None \<Rightarrow> map_of ts2 (k, i) | Some x \<Rightarrow> Some x)
    
    = the_default 0 (map_of ts1 (k, i)) + the_default 0 (map_of ts2 (k, i))
    "    
    apply (auto split: option.splits)
    by (metis disjoint_iff_not_equal img_fst map_of_eq_None_iff the_default.simps(2))
    
  lemma 1[simp]: "distinct (map fst (ts1@ts2)) \<Longrightarrow> 
    pr (\<alpha> (ts1@ts2)) x i = pr (\<alpha> ts1) x i + pr (\<alpha> ts2) x i"
    apply (auto simp: pr_def \<alpha>_def map_add_def aux split: option.splits)
    apply (auto simp: algebra_simps)
    by (simp add: sum.distrib)

  lemmas 2 = 1[of "[((r,c),v)]" "ts", simplified] for r c v ts 
    
  lemma [simp]: "\<alpha> [] = (\<lambda>_. 0)" by (auto simp: \<alpha>_def)  
    
  lemma [simp]: "pr (\<lambda>_. 0::val) x = (\<lambda>_. 0)" 
    by (auto simp: pr_def[abs_def])
  
  lemma aux3: "the_default 0 (if b then Some x else None) = (if b then x else 0)"
    by auto
  
  lemma correct_aux: "\<lbrakk>distinct (map fst ts); \<forall>((r,c),_)\<in>set ts. r<n\<rbrakk> 
    \<Longrightarrow> \<forall>i. fold (\<lambda>((r,c),v) y. y(c:=y c + x r * v)) ts m i = m i + pr (\<alpha> ts) x i"  
    apply (induction ts arbitrary: m)
    apply (auto simp: )
    subgoal
      apply (subst 2)
      apply auto 
      unfolding pr_def \<alpha>_def
      apply (auto split: if_splits cong: sum.cong simp: aux3)
      apply (auto simp: if_distrib[where f="\<lambda>x. _*x"] cong: sum.cong if_cong)
      done
        
    subgoal
      apply (subst 2)
      apply auto 
      unfolding pr_def \<alpha>_def
      apply (auto split: if_splits cong: sum.cong simp: aux3)
      done
    done

    
  lemma correct_fold: 
    assumes "distinct (map fst ts)"
    assumes "\<forall>((r,c),_)\<in>set ts. r<n"
    shows "fold (\<lambda>((r,c),v) y. y(c:=y c + x r * v)) ts (\<lambda>_. 0) = pr (\<alpha> ts) x"
    apply (rule ext)
    using correct_aux[OF assms, rule_format, where m = "\<lambda>_. 0", simplified]
    by simp

  lemma alg_by_fold: "alg ts x = fold (\<lambda>((r,c),v) y. y(c:=y c + x r * v)) ts (\<lambda>_. 0)"    
    unfolding alg_def by (simp add: fold_mset_rewr)
          
  theorem correct: 
    assumes "distinct (map fst ts)"
    assumes "\<forall>((r,c),_)\<in>set ts. r<n"
    shows "alg ts x = pr (\<alpha> ts) x"
    using alg_by_fold correct_fold[OF assms] by simp 

  subsection \<open>Multi-Threaded Implementation\<close>
  text \<open>Correctness of the parallel implementation:\<close>
  theorem parallel_correct:
    assumes "distinct (map fst ts)" "\<forall>((r,c),_)\<in>set ts. r<n"
        and "0 < n" \<comment> \<open>At least on thread\<close>
        \<comment>\<open>We have reached a final state.\<close>
        and "reachable x n ts (\<lambda>_. 0) (ts', ms, r)" "final n (ts', ms, r)"
      shows "r = pr (\<alpha> ts) x"
    unfolding final_state_correct[OF assms(3-)] correct[OF assms(1,2)] alg_by_fold[symmetric] ..

  text \<open>We also know that the computation will always terminate.\<close>
  theorem parallel_termination:
    assumes "0 < n"
      and "reachable x n ts (\<lambda>_. 0) s"
    shows "\<exists>s'. final n s' \<and> (step x n)\<^sup>*\<^sup>* s s'"
    using assms by (rule "termination")

end \<comment> \<open>Context for fixed \<open>n\<close>.\<close>

end