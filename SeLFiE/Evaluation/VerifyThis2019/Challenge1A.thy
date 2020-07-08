section \<open>Challenge 1.A\<close>
theory Challenge1A
imports Main
begin

text \<open>Problem definition:
\<^url>\<open>https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Verify%20This/Challenges%202019/ghc_sort.pdf\<close>\<close>

  subsection \<open>Implementation\<close>
  text \<open>We phrase the algorithm as a functional program. 
    Instead of a list of indexes for segment boundaries,
    we return a list of lists, containing the segments.\<close>

  text \<open>We start with auxiliary functions to take the longest
    increasing/decreasing sequence from the start of the list
  \<close>  
  fun take_incr :: "int list \<Rightarrow> _" where
    "take_incr [] = []"
  | "take_incr [x] = [x]"
  | "take_incr (x#y#xs) = (if x<y then x#take_incr (y#xs) else [x])"  

  fun take_decr :: "int list \<Rightarrow> _" where
    "take_decr [] = []"
  | "take_decr [x] = [x]"
  | "take_decr (x#y#xs) = (if x\<ge>y then x#take_decr (y#xs) else [x])"  
  
  fun take where
    "take [] = []"
  | "take [x] = [x]"
  | "take (x#y#xs) = (if x<y then take_incr (x#y#xs) else take_decr (x#y#xs))"  

  
  definition "take2 xs \<equiv> let l=take xs in (l,drop (length l) xs)"
    \<comment> \<open>Splits of a longest increasing/decreasing sequence from the list\<close>

  
  text \<open>The main algorithm then iterates until the whole input list is split\<close>
  function cuts where
    "cuts xs = (if xs=[] then [] else let (c,xs) = take2 xs in c#cuts xs)"    
    by pat_completeness auto

  subsection \<open>Termination\<close>  
  text \<open>First, we show termination. This will give us induction and proper unfolding lemmas.\<close>

  lemma take_non_empty:
    "take xs \<noteq> []" if "xs \<noteq> []"
    using that
    apply (cases xs)
     apply clarsimp
    subgoal for x ys
      apply (cases ys)
       apply auto
      done
    done

  termination
    apply (relation "measure length")
     apply (auto simp: take2_def Let_def)
    using take_non_empty
    apply auto
    done
    
  declare cuts.simps[simp del]  
    
  subsection \<open>Correctness\<close>
  

  subsubsection \<open>Property 1: The Exact Sequence is Covered\<close>
  lemma tdconc: "\<exists>ys. xs = take_decr xs @ ys"
    apply (induction xs rule: take_decr.induct)
    apply auto
    done

  lemma ticonc: "\<exists>ys. xs = take_incr xs @ ys"
    apply (induction xs rule: take_incr.induct)
    apply auto
    done

  lemma take_conc: "\<exists>ys. xs = take xs@ys"  
    using tdconc ticonc 
    apply (cases xs rule: take.cases)
    by auto 
  
  theorem concat_cuts: "concat (cuts xs) = xs"
    apply (induction xs rule: cuts.induct)
    apply (subst cuts.simps)
    apply (auto simp: take2_def Let_def)
    by (metis append_eq_conv_conj take_conc)  
  
        
        
  subsubsection \<open>Property 2: Monotonicity\<close>
  text \<open>We define constants to specify increasing/decreasing sequences.\<close>
  fun incr where
    "incr [] \<longleftrightarrow> True"
  | "incr [_] \<longleftrightarrow> True"
  | "incr (x#y#xs) \<longleftrightarrow> x<y \<and> incr (y#xs)"  
  
  fun decr where
    "decr [] \<longleftrightarrow> True"
  | "decr [_] \<longleftrightarrow> True"
  | "decr (x#y#xs) \<longleftrightarrow> x\<ge>y \<and> decr (y#xs)"  
  
  lemma tki: "incr (take_incr xs)"
    apply (induction xs rule: take_incr.induct)
    apply auto
    apply (case_tac xs)
    apply auto
    done
    
  lemma tkd: "decr (take_decr xs)"
    apply (induction xs rule: take_decr.induct)
    apply auto
    apply (case_tac xs)
    apply auto
    done
  
  lemma icod: "incr (take xs) \<or> decr (take xs)"
    apply (cases xs rule: take.cases) 
    apply (auto simp: tki tkd simp del: take_incr.simps take_decr.simps)
    done   
        
  theorem cuts_incr_decr: "\<forall>c\<in>set (cuts xs). incr c \<or> decr c"  
    apply (induction xs rule: cuts.induct)
    apply (subst cuts.simps)
    apply (auto simp: take2_def Let_def)
    using icod by blast
    
      
  subsubsection \<open>Property 3: Maximality\<close>      
  text \<open>Specification of a cut that consists of maximal segments:
    The segements are non-empty, and for every two neighbouring segments,
    the first value of the last segment cannot be used to continue the first segment:
  \<close>
  fun maxi where
     "maxi [] \<longleftrightarrow> True"
   | "maxi [c] \<longleftrightarrow> c\<noteq>[]"
   | "maxi (c1#c2#cs) \<longleftrightarrow> (c1\<noteq>[] \<and> c2\<noteq>[] \<and> maxi (c2#cs) \<and> ( 
        incr c1 \<and> \<not>(last c1 < hd c2) 
      \<or> decr c1 \<and> \<not>(last c1 \<ge> hd c2)        
        ))"  

  text \<open>Obviously, our specification implies that there are no 
    empty segments\<close>    
  lemma maxi_imp_non_empty: "maxi xs \<Longrightarrow> []\<notin>set xs"  
    by (induction xs rule: maxi.induct) auto
        
          
  lemma tdconc': "xs\<noteq>[] \<Longrightarrow> 
    \<exists>ys. xs = take_decr xs @ ys \<and> (ys\<noteq>[] 
      \<longrightarrow> \<not>(last (take_decr xs) \<ge> hd ys))"
    apply (induction xs rule: take_decr.induct)
    apply auto
    apply (case_tac xs) apply (auto split: if_splits)
    done
    
  lemma ticonc': "xs\<noteq>[] \<Longrightarrow> \<exists>ys. xs = take_incr xs @ ys \<and> (ys\<noteq>[] \<longrightarrow> \<not>(last (take_incr xs) < hd ys))"
    apply (induction xs rule: take_incr.induct)
    apply auto
    apply (case_tac xs) apply (auto split: if_splits)
    done

  lemma take_conc': "xs\<noteq>[] \<Longrightarrow> \<exists>ys. xs = take xs@ys \<and> (ys\<noteq>[] \<longrightarrow> (
    take xs=take_incr xs \<and> \<not>(last (take_incr xs) < hd ys)
  \<or> take xs=take_decr xs \<and> \<not>(last (take_decr xs) \<ge> hd ys)  
  ))"  
    using tdconc' ticonc' 
    apply (cases xs rule: take.cases)
    by auto 
    
    
  lemma take_decr_non_empty:
    "take_decr xs \<noteq> []" if "xs \<noteq> []"
    using that
    apply (cases xs)
     apply auto
    subgoal for x ys
      apply (cases ys)
       apply (auto split: if_split_asm)
      done
    done
  
  lemma take_incr_non_empty:
    "take_incr xs \<noteq> []" if "xs \<noteq> []"
    using that
    apply (cases xs)
     apply auto
    subgoal for x ys
      apply (cases ys)
       apply (auto split: if_split_asm)
      done
    done
    
  lemma take_conc'': "xs\<noteq>[] \<Longrightarrow> \<exists>ys. xs = take xs@ys \<and> (ys\<noteq>[] \<longrightarrow> (
    incr (take xs) \<and> \<not>(last (take xs) < hd ys)
  \<or> decr (take xs) \<and> \<not>(last (take xs) \<ge> hd ys)  
  ))"  
    using tdconc' ticonc' tki tkd 
    apply (cases xs rule: take.cases)
    apply auto
    apply (auto simp add: take_incr_non_empty) 
    apply (simp add: take_decr_non_empty)
    apply (metis list.distinct(1) take_incr.simps(3))
    by (smt list.simps(3) take_decr.simps(3))
    
    
  
  lemma [simp]: "cuts [] = []"
    apply (subst cuts.simps) by auto
    
  lemma [simp]: "cuts xs \<noteq> [] \<longleftrightarrow> xs \<noteq> []"  
    apply (subst cuts.simps) 
    apply (auto simp: take2_def Let_def)
    done

  lemma inv_cuts: "cuts xs = c#cs \<Longrightarrow> \<exists>ys. c=take xs \<and> xs=c@ys \<and> cs = cuts ys"
    apply (subst (asm) cuts.simps)
    apply (cases xs rule: cuts.cases)
    apply (auto split: if_splits simp: take2_def Let_def)
    by (metis append_eq_conv_conj take_conc)
    
  theorem maximal_cuts: "maxi (cuts xs)" 
    apply (induction "cuts xs" arbitrary: xs rule: maxi.induct)
    subgoal by auto
    subgoal for c xs
      apply (drule sym; simp)
      apply (subst (asm) cuts.simps)
      apply (auto split: if_splits prod.splits simp: take2_def Let_def take_non_empty)
      done
    subgoal for c1 c2 cs xs
      apply (drule sym)
      apply simp
      apply (drule inv_cuts; clarsimp)
      apply auto
      subgoal by (metis cuts.simps list.distinct(1) take_non_empty) 
      subgoal by (metis append.left_neutral inv_cuts not_Cons_self) 
      subgoal using icod by blast 
      subgoal by (metis
            Nil_is_append_conv cuts.simps hd_append2 inv_cuts list.distinct(1)
            same_append_eq take_conc'' take_non_empty) 
      subgoal by (metis
            append_is_Nil_conv cuts.simps hd_append2 inv_cuts list.distinct(1)
            same_append_eq take_conc'' take_non_empty) 
      done
    done

  subsubsection \<open>Equivalent Formulation Over Indexes\<close>
  text \<open>After the competition, we got the comment that a specification of 
    monotonic sequences via indexes might be more readable.
  
    We show that our functional specification is equivalent to a 
    specification over indexes.\<close>
    
  fun ii_induction where
    "ii_induction [] = ()"
  | "ii_induction [_] = ()"
  | "ii_induction (_#y#xs) = ii_induction (y#xs)"      

  locale cnvSpec =
    fixes fP P
    assumes [simp]: "fP [] \<longleftrightarrow> True"
    assumes [simp]: "fP [x] \<longleftrightarrow> True"
    assumes [simp]: "fP (a#b#xs) \<longleftrightarrow> P a b \<and> fP (b#xs)"
  begin

    lemma idx_spec: "fP xs \<longleftrightarrow> (\<forall>i<length xs - 1. P (xs!i) (xs!Suc i))"
      apply (induction xs rule: ii_induction.induct)
      using less_Suc_eq_0_disj
      by auto
  
  end

  locale cnvSpec' =
    fixes fP P P'
    assumes [simp]: "fP [] \<longleftrightarrow> True"
    assumes [simp]: "fP [x] \<longleftrightarrow> P' x"
    assumes [simp]: "fP (a#b#xs) \<longleftrightarrow> P' a \<and> P' b \<and> P a b \<and> fP (b#xs)"
  begin

    lemma idx_spec: "fP xs \<longleftrightarrow> (\<forall>i<length xs. P' (xs!i)) \<and> (\<forall>i<length xs - 1. P (xs!i) (xs!Suc i))"
      apply (induction xs rule: ii_induction.induct)
      apply auto []
      apply auto []
      apply clarsimp
      by (smt less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc)
  
  end
    
  interpretation INCR: cnvSpec incr "(<)"
    apply unfold_locales by auto
  
  interpretation DECR: cnvSpec decr "(\<ge>)"
    apply unfold_locales by auto
  
  interpretation MAXI: cnvSpec' maxi "\<lambda>c1 c2. ( ( 
        incr c1 \<and> \<not>(last c1 < hd c2) 
      \<or> decr c1 \<and> \<not>(last c1 \<ge> hd c2)        
        ))"
      "\<lambda>x. x \<noteq> []"  
    apply unfold_locales by auto
  
  lemma incr_by_idx: "incr xs = (\<forall>i<length xs - 1. xs ! i < xs ! Suc i)" 
    by (rule INCR.idx_spec)
    
  lemma decr_by_idx: "decr xs = (\<forall>i<length xs - 1. xs ! i \<ge> xs ! Suc i)" 
    by (rule DECR.idx_spec)
    
  lemma maxi_by_idx: "maxi xs \<longleftrightarrow>
    (\<forall>i<length xs. xs ! i \<noteq> []) \<and>
    (\<forall>i<length xs - 1. 
         incr (xs ! i) \<and> \<not> last (xs ! i) < hd (xs ! Suc i) 
       \<or> decr (xs ! i) \<and> \<not> hd (xs ! Suc i) \<le> last (xs ! i)
    )"
    by (rule MAXI.idx_spec)

  theorem all_correct:  
    "concat (cuts xs) = xs"
    "\<forall>c\<in>set (cuts xs). incr c \<or> decr c"
    "maxi (cuts xs)"
    "[] \<notin> set (cuts xs)"
    using cuts_incr_decr concat_cuts maximal_cuts 
          maxi_imp_non_empty[OF maximal_cuts]
    by auto

end