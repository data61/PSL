section \<open>Heap Implementation On Lists\<close>
theory IICF_Abs_Heap
imports 
  "HOL-Library.Multiset"
  "../../../Sepref" 
  "List-Index.List_Index"
  "../../Intf/IICF_List"
  "../../Intf/IICF_Prio_Bag"
begin

text \<open>
  We define Min-Heaps, which implement multisets of prioritized values.
  The operations are: 
    empty heap, emptiness check, insert an element, 
    remove a minimum priority element.\<close>

  subsection \<open>Basic Definitions\<close>

  type_synonym 'a heap = "'a list"

  locale heapstruct =
    fixes prio :: "'a \<Rightarrow> 'b::linorder"
  begin
    definition valid :: "'a heap \<Rightarrow> nat \<Rightarrow> bool" 
      where "valid h i \<equiv> i>0 \<and> i\<le>length h"

    abbreviation \<alpha> :: "'a heap \<Rightarrow> 'a multiset" where "\<alpha> \<equiv> mset"
  
    
    lemma valid_empty[simp]: "\<not>valid [] i" by (auto simp: valid_def)
    lemma valid0[simp]: "\<not>valid h 0" by (auto simp: valid_def)
    lemma valid_glen[simp]: "i>length h \<Longrightarrow> \<not>valid h i" by (auto simp: valid_def)

    lemma valid_len[simp]: "h\<noteq>[] \<Longrightarrow> valid h (length h)" by (auto simp: valid_def)

    lemma validI: "0<i \<Longrightarrow> i\<le>length h \<Longrightarrow> valid h i"  
      by (auto simp: valid_def)

    definition val_of :: "'a heap \<Rightarrow> nat \<Rightarrow> 'a" where "val_of l i \<equiv> l!(i-1)"
    abbreviation prio_of :: "'a heap \<Rightarrow> nat \<Rightarrow> 'b" where
      "prio_of l i \<equiv> prio (val_of l i)"

    subsubsection \<open>Navigating the tree\<close>

    definition parent :: "nat \<Rightarrow> nat" where "parent i \<equiv> i div 2"
    definition left :: "nat \<Rightarrow> nat" where "left i \<equiv> 2*i"
    definition right :: "nat \<Rightarrow> nat" where "right i \<equiv> 2*i + 1"

    abbreviation "has_parent h i \<equiv> valid h (parent i)"
    abbreviation "has_left h i \<equiv> valid h (left i)"
    abbreviation "has_right h i \<equiv> valid h (right i)"

    abbreviation "vparent h i == val_of h (parent i)"
    abbreviation "vleft h i == val_of h (left i)"
    abbreviation "vright h i == val_of h (right i)"

    abbreviation "pparent h i == prio_of h (parent i)"
    abbreviation "pleft h i == prio_of h (left i)"
    abbreviation "pright h i == prio_of h (right i)"

    lemma parent_left_id[simp]: "parent (left i) = i"
      unfolding parent_def left_def
      by auto

    lemma parent_right_id[simp]: "parent (right i) = i"
      unfolding parent_def right_def
      by auto

    lemma child_of_parentD:
      "has_parent l i \<Longrightarrow> left (parent i) = i \<or> right (parent i) = i"
      unfolding parent_def left_def right_def valid_def
      by auto

    lemma rc_imp_lc: "\<lbrakk>valid h i; has_right h i\<rbrakk> \<Longrightarrow> has_left h i"
      by (auto simp: valid_def left_def right_def)

    lemma plr_corner_cases[simp]: 
      assumes "0<i"
      shows 
      "i\<noteq>parent i"
      "i\<noteq>left i"
      "i\<noteq>right i"
      "parent i \<noteq> i"
      "left i \<noteq> i"
      "right i \<noteq> i"
      using assms
      by (auto simp: parent_def left_def right_def)

    lemma i_eq_parent_conv[simp]: "i=parent i \<longleftrightarrow> i=0"  
      by (auto simp: parent_def)

    subsubsection \<open>Heap Property\<close>
    text \<open>The heap property states, that every node's priority is greater 
      or equal to its parent's priority \<close>
    definition heap_invar :: "'a heap \<Rightarrow> bool"
      where "heap_invar l 
      \<equiv> \<forall>i. valid l i \<longrightarrow> has_parent l i \<longrightarrow> pparent l i \<le> prio_of l i"


    definition "heap_rel1 \<equiv> br \<alpha> heap_invar"  
    
    lemma heap_invar_empty[simp]: "heap_invar []"
      by (auto simp: heap_invar_def)

    function heap_induction_scheme :: "nat \<Rightarrow> unit" where
      "heap_induction_scheme i = (
        if i>1 then heap_induction_scheme (parent i) else ())"
      by pat_completeness auto  

    termination
      apply (relation "less_than")
      apply (auto simp: parent_def)
      done

    lemma 
      heap_parent_le: "\<lbrakk>heap_invar l; valid l i; has_parent l i\<rbrakk> 
        \<Longrightarrow> pparent l i \<le> prio_of l i"
      unfolding heap_invar_def
      by auto

    lemma heap_min_prop:
      assumes H: "heap_invar h"
      assumes V: "valid h i"
      shows "prio_of h (Suc 0) \<le> prio_of h i"
    proof (cases "i>1")
      case False with V show ?thesis
        by (auto simp: valid_def intro: Suc_lessI)
    next
      case True
      from V have "i\<le>length h" "valid h (Suc 0)" by (auto simp: valid_def)
      with True show ?thesis
        apply (induction i rule: heap_induction_scheme.induct)  
        apply (rename_tac i)
        apply (case_tac "parent i = Suc 0")
        apply (rule order_trans[rotated])
        apply (rule heap_parent_le[OF H])
        apply (auto simp: valid_def) [3]

        apply (rule order_trans)  
        apply (rprems)
        apply (auto simp: parent_def) [4]
        apply (rule heap_parent_le[OF H])
        apply (auto simp: valid_def parent_def)
        done
    qed

    text \<open> Obviously, the heap property can also be stated in terms of children,
      i.e., each node's priority is smaller or equal to it's children's priority.\<close>

    definition "children_ge h p i \<equiv> 
      (has_left h i \<longrightarrow> p \<le> pleft h i)
    \<and> (has_right h i \<longrightarrow> p \<le> pright h i)"
    
    definition "heap_invar' h \<equiv> \<forall>i. valid h i \<longrightarrow> children_ge h (prio_of h i) i"

    lemma heap_eq_heap':
      shows "heap_invar h \<longleftrightarrow> heap_invar' h"
      unfolding heap_invar_def 
      unfolding heap_invar'_def children_ge_def
      apply rule
      apply auto []
      apply clarsimp
      apply (frule child_of_parentD)
      apply auto []
      done

    subsection \<open>Basic Operations\<close>  
    text \<open>The basic operations are the only operations that directly 
      modify the underlying data structure.\<close>
    subsubsection \<open>Val-Of\<close>
    abbreviation (input) "val_of_pre l i \<equiv> valid l i"
    definition val_of_op :: "'a heap \<Rightarrow> nat \<Rightarrow> 'a nres" 
      where "val_of_op l i \<equiv> ASSERT (i>0) \<then> mop_list_get l (i-1)"
    lemma val_of_correct[refine_vcg]: 
      "val_of_pre l i \<Longrightarrow> val_of_op l i \<le> SPEC (\<lambda>r. r = val_of l i)"
      unfolding val_of_op_def val_of_def valid_def
      by refine_vcg auto
    
    abbreviation (input) "prio_of_pre \<equiv> val_of_pre"  
    definition "prio_of_op l i \<equiv> do {v \<leftarrow> val_of_op l i; RETURN (prio v)}"
    lemma prio_of_op_correct[refine_vcg]: 
      "prio_of_pre l i \<Longrightarrow> prio_of_op l i \<le> SPEC (\<lambda>r. r = prio_of l i)"
      unfolding prio_of_op_def
      apply refine_vcg by simp

    subsubsection \<open>Update\<close>
    abbreviation "update_pre h i v \<equiv> valid h i"
    definition update :: "'a heap \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a heap" 
      where "update h i v \<equiv> h[i - 1 := v]"
    definition update_op :: "'a heap \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a heap nres" 
      where "update_op h i v \<equiv> ASSERT (i>0) \<then> mop_list_set h (i-1) v"
    lemma update_correct[refine_vcg]:
      "update_pre h i v \<Longrightarrow> update_op h i v \<le> SPEC(\<lambda>r. r = update h i v)"
      unfolding update_op_def update_def valid_def by refine_vcg auto

    lemma update_valid[simp]: "valid (update h i v) j \<longleftrightarrow> valid h j"  
      by (auto simp: update_def valid_def)

    lemma val_of_update[simp]: "\<lbrakk>update_pre h i v; valid h j\<rbrakk> \<Longrightarrow> val_of (update h i v) j = (
      if i=j then v else val_of h j)"  
      unfolding update_def val_of_def
      by (auto simp: nth_list_update valid_def)

    lemma length_update[simp]: "length (update l i v) = length l"
      by (auto simp: update_def)

    subsubsection \<open>Exchange\<close>
    text \<open> Exchange two elements \<close>

    definition exch :: "'a heap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a heap" where
      "exch l i j \<equiv> swap l (i - 1) (j - 1)"
    abbreviation "exch_pre l i j \<equiv> valid l i \<and> valid l j"

    definition exch_op :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list nres"
    where "exch_op l i j \<equiv> do { 
      ASSERT (i>0 \<and> j>0);
      l \<leftarrow> mop_list_swap l (i - 1) (j - 1);
      RETURN l
    }"

    lemma exch_op_alt: "exch_op l i j = do { 
      vi \<leftarrow> val_of_op l i;
      vj \<leftarrow> val_of_op l j;
      l \<leftarrow> update_op l i vj;
      l \<leftarrow> update_op l j vi;
      RETURN l }"
      by (auto simp: exch_op_def swap_def val_of_op_def update_op_def 
        pw_eq_iff refine_pw_simps)

    lemma exch_op_correct[refine_vcg]: 
      "exch_pre l i j \<Longrightarrow> exch_op l i j \<le> SPEC (\<lambda>r. r = exch l i j)"
      unfolding exch_op_def 
      apply refine_vcg
      apply (auto simp: exch_def valid_def)
      done
       
    lemma valid_exch[simp]: "valid (exch l i j) k = valid l k"
      unfolding exch_def by (auto simp: valid_def)
    
    lemma val_of_exch[simp]: "\<lbrakk>valid l i; valid l j; valid l k\<rbrakk> \<Longrightarrow> 
      val_of (exch l i j) k = (
        if k=i then val_of l j
        else if k=j then val_of l i
        else val_of l k
      )"
      unfolding exch_def val_of_def valid_def
      by (auto)

    lemma exch_eq[simp]: "exch h i i = h" 
      by (auto simp: exch_def)

    lemma \<alpha>_exch[simp]: "\<lbrakk>valid l i; valid l j\<rbrakk> 
      \<Longrightarrow> \<alpha> (exch l i j) = \<alpha> l"
      unfolding exch_def valid_def 
      by (auto)

    lemma length_exch[simp]: "length (exch l i j) = length l"
      by (auto simp: exch_def)

    subsubsection \<open>Butlast\<close>
    text \<open>Remove last element\<close>

    abbreviation "butlast_pre l \<equiv> l\<noteq>[]"
    definition butlast_op :: "'a heap \<Rightarrow> 'a heap nres"
      where "butlast_op l \<equiv> mop_list_butlast l"
    lemma butlast_op_correct[refine_vcg]: 
      "butlast_pre l \<Longrightarrow> butlast_op l \<le> SPEC (\<lambda>r. r = butlast l)"
      unfolding butlast_op_def by (refine_vcg; auto)

    lemma valid_butlast_conv[simp]: "valid (butlast h) i \<longleftrightarrow> valid h i \<and> i < length h"
      by (auto simp: valid_def)

    lemma valid_butlast: "valid (butlast h) i \<Longrightarrow> valid h i"  
      by (cases h rule: rev_cases) (auto simp: valid_def)
    
    lemma val_of_butlast[simp]: "\<lbrakk>valid h i; i<length h\<rbrakk> 
      \<Longrightarrow> val_of (butlast h) i = val_of h i"
      by (auto simp: valid_def val_of_def nth_butlast)

    lemma val_of_butlast'[simp]: 
      "valid (butlast h) i \<Longrightarrow> val_of (butlast h) i = val_of h i"
      by (cases h rule: rev_cases) (auto simp: valid_def val_of_def nth_append)

    lemma \<alpha>_butlast[simp]: "\<lbrakk> length h \<noteq> 0 \<rbrakk> 
      \<Longrightarrow> \<alpha> (butlast h) = \<alpha> h - {# val_of h (length h)#}"
      apply (cases h rule: rev_cases)
      apply (auto simp: val_of_def)   
      done

    lemma heap_invar_butlast[simp]: "heap_invar h \<Longrightarrow> heap_invar (butlast h)"
      apply (cases "h = []")
      apply simp
      apply (auto simp: heap_invar_def dest: valid_butlast)
      done

    subsubsection \<open>Append\<close>  
    definition append_op :: "'a heap \<Rightarrow> 'a \<Rightarrow> 'a heap nres"
      where "append_op l v \<equiv> mop_list_append l v"
    lemma append_op_correct[refine_vcg]: 
      "append_op l v \<le> SPEC (\<lambda>r. r = l@[v])"
      unfolding append_op_def by (refine_vcg; auto)
    

    lemma valid_append[simp]: "valid (l@[v]) i \<longleftrightarrow> valid l i \<or> i = length l + 1"
      by (auto simp: valid_def)

    lemma val_of_append[simp]: "valid (l@[v]) i \<Longrightarrow> 
      val_of (l@[v]) i = (if valid l i then val_of l i else v)"
      unfolding valid_def val_of_def by (auto simp: nth_append)

    lemma \<alpha>_append[simp]: "\<alpha> (l@[v]) = \<alpha> l + {#v#}"
      by (auto simp: )

    subsection \<open>Auxiliary operations\<close>  
    text \<open>The auxiliary operations do not have a corresponding abstract operation, but
      are to restore the heap property after modification.\<close>
    subsubsection \<open>Swim\<close>

    text \<open>This invariant expresses that the heap has a single defect,
      which can be repaired by swimming up\<close>  
    definition swim_invar :: "'a heap \<Rightarrow> nat \<Rightarrow> bool"
      where "swim_invar h i \<equiv> 
        valid h i
      \<and> (\<forall>j. valid h j \<and> has_parent h j \<and> j\<noteq>i \<longrightarrow> pparent h j \<le> prio_of h j)
      \<and> (has_parent h i \<longrightarrow> 
        (\<forall>j. valid h j \<and> has_parent h j \<and> parent j = i 
          \<longrightarrow> pparent h i \<le> prio_of h j))"

    text \<open>Move up an element that is too small, until it fits\<close>
    definition swim_op :: "'a heap \<Rightarrow> nat \<Rightarrow> 'a heap nres" where
      "swim_op h i \<equiv> do {
        RECT (\<lambda>swim (h,i). do {
          ASSERT (valid h i \<and> swim_invar h i);
          if has_parent h i then do {
            ppi \<leftarrow> prio_of_op h (parent i);
            pi \<leftarrow> prio_of_op h i;
            if (\<not>ppi \<le> pi) then do {
              h \<leftarrow> exch_op h i (parent i);
              swim (h, parent i)
            } else
              RETURN h
          } else 
            RETURN h
        }) (h,i)
      }"

    lemma swim_invar_valid: "swim_invar h i \<Longrightarrow> valid h i"
      unfolding swim_invar_def by simp
    
    lemma swim_invar_exit1: "\<not>has_parent h i \<Longrightarrow> swim_invar h i \<Longrightarrow> heap_invar h"
      unfolding heap_invar_def swim_invar_def by auto

    lemma swim_invar_exit2: "pparent h i \<le> prio_of h i \<Longrightarrow> swim_invar h i \<Longrightarrow> heap_invar h"
      unfolding heap_invar_def swim_invar_def by auto

    lemma swim_invar_pres:
      assumes HPI: "has_parent h i" 
      assumes VIOLATED: "pparent h i > prio_of h i" 
      and INV: "swim_invar h i"
      defines "h' \<equiv> exch h i (parent i)"
      shows "swim_invar h' (parent i)"
      unfolding swim_invar_def
      apply safe
      apply (simp add: h'_def HPI)

      using HPI VIOLATED INV
      unfolding swim_invar_def h'_def
      apply auto []

      using HPI VIOLATED INV
      unfolding swim_invar_def h'_def
      apply auto
      by (metis order_trans)


    lemma swim_invar_decr:
      assumes INV: "heap_invar h"
      assumes V: "valid h i"
      assumes DECR: "prio v \<le> prio_of h i"
      shows "swim_invar (update h i v) i"
      using INV V DECR
      apply (auto simp: swim_invar_def heap_invar_def intro: dual_order.trans)
      done

    lemma swim_op_correct[refine_vcg]: 
    "\<lbrakk>swim_invar h i\<rbrakk> \<Longrightarrow>
      swim_op h i \<le> SPEC (\<lambda>h'. \<alpha> h' = \<alpha> h \<and> heap_invar h' \<and> length h' = length h)"  
      unfolding swim_op_def
      using [[goals_limit = 1]]
      apply (refine_vcg  RECT_rule[where 
          pre="\<lambda>(hh,i). 
            swim_invar hh i 
          \<and> \<alpha> hh = \<alpha> h 
          \<and> length hh = length h" and
          V = "inv_image less_than snd"
          ])
      apply (auto) []
      apply (auto) []
      apply (auto) []
      apply (auto) []
      apply (auto simp: swim_invar_valid) []
      apply (auto) []
      apply (auto) []
      apply (auto) []

      apply rprems
        apply (auto simp: swim_invar_pres) []
        apply (auto simp: parent_def valid_def) []

      apply (auto) []
      apply (auto simp: swim_invar_exit2) []
      apply (auto) []
      apply (auto) []
      apply (auto simp: swim_invar_exit1) []
      apply (auto) []
      done



    subsubsection \<open>Sink\<close>
    text \<open>Move down an element that is too big, until it fits in\<close>

    definition sink_op :: "'a heap \<Rightarrow> nat \<Rightarrow> 'a heap nres" where
      "sink_op h i \<equiv> do {
        RECT (\<lambda>sink (h,i). do {
          ASSERT (valid h i);
          if has_right h i then do {
            ASSERT (has_left h i);
            lp \<leftarrow> prio_of_op h (left i);
            rp \<leftarrow> prio_of_op h (right i);
            p \<leftarrow> prio_of_op h i;
            if (lp < p \<and> rp \<ge> lp) then do {
              h \<leftarrow> exch_op h i (left i);
              sink (h,left i)
            } else if (rp<lp \<and> rp < p) then do {
              h \<leftarrow> exch_op h i (right i);
              sink (h,right i)
            } else 
              RETURN h
          } else if (has_left h i) then do {
            lp \<leftarrow> prio_of_op h (left i);
            p \<leftarrow> prio_of_op h i;
            if (lp < p) then do {
              h \<leftarrow> exch_op h i (left i);
              sink (h,left i)
            } else
              RETURN h
            
          } else 
            RETURN h
        }) (h,i)
      }"

    text \<open>This invariant expresses that the heap has a single defect, 
      which can be repaired by sinking\<close>
    definition "sink_invar l i \<equiv> 
      valid l i
    \<and> (\<forall>j. valid l j \<and> j\<noteq>i \<longrightarrow> children_ge l (prio_of l j) j)
    \<and> (has_parent l i \<longrightarrow> children_ge l (pparent l i) i)"
    
    lemma sink_invar_valid: "sink_invar l i \<Longrightarrow> valid l i"
      unfolding sink_invar_def by auto
    
    lemma sink_invar_exit: "\<lbrakk>sink_invar l i; children_ge l (prio_of l i) i\<rbrakk> 
      \<Longrightarrow> heap_invar' l"
      unfolding heap_invar'_def sink_invar_def
      by auto
    
    lemma sink_aux1: "\<not> (2*i \<le> length h) \<Longrightarrow> \<not>has_left h i \<and> \<not>has_right h i"
      unfolding valid_def left_def right_def by auto
    
    lemma sink_invar_pres1:
      assumes "sink_invar h i"
      assumes "has_left h i" "has_right h i"
      assumes "prio_of h i \<ge> pleft h i"
      assumes "pleft h i \<ge> pright h i"
      shows "sink_invar (exch h i (right i)) (right i)"
      using assms  
      unfolding sink_invar_def
      apply auto
      apply (auto simp: children_ge_def)
      done
    
    lemma sink_invar_pres2:
      assumes "sink_invar h i"
      assumes "has_left h i" "has_right h i"
      assumes "prio_of h i \<ge> pleft h i"
      assumes "pleft h i \<le> pright h i"
      shows "sink_invar (exch h i (left i)) (left i)"
      using assms  
      unfolding sink_invar_def
      apply auto
      apply (auto simp: children_ge_def)
      done
    
    lemma sink_invar_pres3:
      assumes "sink_invar h i"
      assumes "has_left h i" "has_right h i"
      assumes "prio_of h i \<ge> pright h i"
      assumes "pleft h i \<le> pright h i"
      shows "sink_invar (exch h i (left i)) (left i)"
      using assms  
      unfolding sink_invar_def
      apply auto
      apply (auto simp: children_ge_def)
      done
    
    lemma sink_invar_pres4:
      assumes "sink_invar h i"
      assumes "has_left h i" "has_right h i"
      assumes "prio_of h i \<ge> pright h i"
      assumes "pleft h i \<ge> pright h i"
      shows "sink_invar (exch h i (right i)) (right i)"
      using assms  
      unfolding sink_invar_def
      apply auto
      apply (auto simp: children_ge_def)
      done
    
    lemma sink_invar_pres5:
      assumes "sink_invar h i"
      assumes "has_left h i" "\<not>has_right h i"
      assumes "prio_of h i \<ge> pleft h i"
      shows "sink_invar (exch h i (left i)) (left i)"
      using assms  
      unfolding sink_invar_def
      apply auto
      apply (auto simp: children_ge_def)
      done
    
    lemmas sink_invar_pres = 
      sink_invar_pres1 
      sink_invar_pres2 
      sink_invar_pres3 
      sink_invar_pres4 
      sink_invar_pres5


    lemma sink_invar_incr:
      assumes INV: "heap_invar h"
      assumes V: "valid h i"
      assumes INCR: "prio v \<ge> prio_of h i"
      shows "sink_invar (update h i v) i"
      using INV V INCR
      apply (auto simp: sink_invar_def)
      apply (auto simp: children_ge_def heap_invar_def) []
      apply (auto simp: children_ge_def heap_invar_def intro: order_trans) []
      apply (frule spec[where x="left i"])
      apply auto []
      apply (frule spec[where x="right i"])
      apply auto []
      done


    lemma sink_op_correct[refine_vcg]: 
    "\<lbrakk>sink_invar h i\<rbrakk> \<Longrightarrow>
      sink_op h i \<le> SPEC (\<lambda>h'. \<alpha> h' = \<alpha> h \<and> heap_invar h' \<and> length h' = length h)"  
      unfolding sink_op_def heap_eq_heap'
      using [[goals_limit = 1]]

      apply (refine_vcg  RECT_rule[where 
          pre="\<lambda>(hh,i). sink_invar hh i \<and> \<alpha> hh = \<alpha> h \<and> length hh = length h" and
          V = "measure (\<lambda>(l,i). length l - i)"
          ])

      apply (auto) []
      apply (auto) []
      apply (auto) []
      apply (auto) []
      apply (auto simp: sink_invar_valid) []
      apply (auto simp: valid_def left_def right_def) []

      apply rprems
        apply (auto intro: sink_invar_pres) []
        apply (auto simp: valid_def left_def right_def) []

      apply rprems
        apply (auto intro: sink_invar_pres) []
        apply (auto simp: valid_def left_def right_def) []

      apply (auto) []

      apply clarsimp
      apply (rule sink_invar_exit, assumption) []
      apply (auto simp: children_ge_def) []

      apply (auto) []
      
      apply rprems
        apply (auto intro: sink_invar_pres) []
        apply (auto simp: valid_def left_def right_def) []

      apply (auto) []

      apply clarsimp
      apply (rule sink_invar_exit, assumption) []
      apply (auto simp: children_ge_def) []

      apply (auto) []

      apply (auto) []

      apply clarsimp
      apply (rule sink_invar_exit, assumption) []
      apply (auto simp: children_ge_def) []

      apply (auto) []
      done

    lemma sink_op_swim_rule: 
      "swim_invar h i \<Longrightarrow> sink_op h i \<le> SPEC (\<lambda>h'. h'=h)"  
      apply (frule swim_invar_valid)
      unfolding sink_op_def
      apply (subst RECT_unfold, refine_mono)
      apply (fold sink_op_def)
      apply refine_vcg
      apply (simp_all)
      apply (auto simp add: valid_def left_def right_def dest: swim_invar_valid) []
      apply (auto simp: swim_invar_def) []
      apply (auto simp: swim_invar_def) []
      apply (auto simp: swim_invar_def) []
      apply (auto simp: swim_invar_def) []
      apply (auto simp: swim_invar_def) []
      apply (auto simp: swim_invar_def) []
      done

    definition sink_op_opt
      \<comment> \<open>Sink operation as presented in Sedgewick et al. Algs4 reference implementation\<close>
    where   
      "sink_op_opt h k \<equiv> RECT (\<lambda>D (h,k). do {
        ASSERT (k>0 \<and> k\<le>length h);
        let len = length h;
        if (2*k \<le> len) then do {
          let j = 2*k;
          pj \<leftarrow> prio_of_op h j;

          j \<leftarrow> (
            if j<len then do {
              psj \<leftarrow> prio_of_op h (Suc j);
              if pj>psj then RETURN (j+1) else RETURN j
            } else RETURN j);

          pj \<leftarrow> prio_of_op h j;
          pk \<leftarrow> prio_of_op h k;
          if (pk > pj) then do {
            h \<leftarrow> exch_op h k j;
            D (h,j)
          } else
            RETURN h
        } else RETURN h    
      }) (h,k)"

    lemma sink_op_opt_eq: "sink_op_opt h k = sink_op h k"
      unfolding sink_op_opt_def sink_op_def
      apply (fo_rule arg_cong fun_cong)+
      apply (intro ext)
      unfolding sink_op_def[symmetric]
      apply (simp cong: if_cong split del: if_split add: Let_def)

      apply (auto simp: valid_def left_def right_def prio_of_op_def val_of_op_def 
        val_of_def less_imp_diff_less ASSERT_same_eq_conv nz_le_conv_less) []
      done

    subsubsection \<open>Repair\<close>  
    text \<open>Repair a local defect in the heap. This can be done 
      by swimming and sinking. Note that, depending on the defect, only one
      of the operations will change the heap. 
      Moreover, note that we do not need repair to implement the heap operations. 
      However, it is required for heapmaps. \<close>
    
    definition "repair_op h i \<equiv> do {
      h \<leftarrow> sink_op h i;
      h \<leftarrow> swim_op h i;
      RETURN h
    }"

    lemma update_sink_swim_cases:
      assumes "heap_invar h"
      assumes "valid h i"
      obtains "swim_invar (update h i v) i" | "sink_invar (update h i v) i"
      apply (cases rule: linear[of "prio v" "prio_of h i", THEN disjE])
      apply (blast dest: swim_invar_decr[OF assms])
      apply (blast dest: sink_invar_incr[OF assms])
      done

    lemma heap_invar_imp_swim_invar: "\<lbrakk>heap_invar h; valid h i\<rbrakk> \<Longrightarrow> swim_invar h i"
      unfolding heap_invar_def swim_invar_def
      by (auto intro: order_trans)


    lemma repair_correct[refine_vcg]:
      assumes "heap_invar h" and "valid h i"
      shows "repair_op (update h i v) i \<le> SPEC (\<lambda>h'.
        heap_invar h' \<and> \<alpha> h' = \<alpha> (update h i v) \<and> length h' = length h)"
      apply (rule update_sink_swim_cases[of h i v, OF assms])
      unfolding repair_op_def  
      apply (refine_vcg sink_op_swim_rule)
      apply auto [4]
      apply (refine_vcg)
      using assms(2)
      apply (auto intro: heap_invar_imp_swim_invar simp: valid_def) []
      apply auto [3]
      done

    subsection \<open>Operations\<close>

    (*
    subsubsection \<open>Length\<close>
    definition length_op :: "'a heap \<Rightarrow> nat nres" where "length_op \<equiv> lst_op_length"

    lemma [refine_vcg]: "length_op l \<le> SPEC (\<lambda>r. r = length l)"
      unfolding length_op_def
      by refine_vcg
    *)  

    subsubsection \<open>Empty\<close>
    abbreviation (input) empty :: "'a heap" \<comment> \<open>The empty heap\<close>
      where "empty \<equiv> []"
    definition empty_op :: "'a heap nres" 
      where "empty_op \<equiv> mop_list_empty"
    lemma empty_op_correct[refine_vcg]:
      "empty_op \<le> SPEC (\<lambda>r. \<alpha> r = {#} \<and> heap_invar r)"
      unfolding empty_op_def apply refine_vcg by auto

    subsubsection \<open>Emptiness check\<close>  
    definition is_empty_op :: "'a heap \<Rightarrow> bool nres" \<comment> \<open>Check for emptiness\<close>
      where "is_empty_op h \<equiv> do {ASSERT (heap_invar h); let l=length h; RETURN (l=0)}"
    lemma is_empty_op_correct[refine_vcg]: 
      "heap_invar h \<Longrightarrow> is_empty_op h \<le> SPEC (\<lambda>r. r\<longleftrightarrow>\<alpha> h = {#})"  
      unfolding is_empty_op_def
      apply refine_vcg by auto

    subsubsection \<open>Insert\<close>
    definition insert_op :: "'a \<Rightarrow> 'a heap \<Rightarrow> 'a heap nres" \<comment> \<open>Insert element\<close>
      where "insert_op v h \<equiv> do {
        ASSERT (heap_invar h);
        h \<leftarrow> append_op h v;
        let l = length h;
        h \<leftarrow> swim_op h l;
        RETURN h
      }"

    lemma swim_invar_insert: "heap_invar l \<Longrightarrow> swim_invar (l@[x]) (Suc (length l))"
      unfolding swim_invar_def heap_invar_def valid_def parent_def val_of_def
      by (fastforce simp: nth_append)

    lemma  
      "(insert_op,RETURN oo op_mset_insert) \<in> Id \<rightarrow> heap_rel1 \<rightarrow> \<langle>heap_rel1\<rangle>nres_rel"
      unfolding insert_op_def[abs_def] heap_rel1_def o_def
      by refine_vcg (auto simp: swim_invar_insert in_br_conv)

    lemma insert_op_correct:
      "heap_invar h \<Longrightarrow> insert_op v h \<le> SPEC (\<lambda>h'. heap_invar h' \<and> \<alpha> h' = \<alpha> h + {#v#})"
      unfolding insert_op_def
      by (refine_vcg) (auto simp: swim_invar_insert)
    lemmas [refine_vcg] = insert_op_correct  

    subsubsection \<open>Pop minimum element\<close>  

    definition pop_min_op :: "'a heap \<Rightarrow> ('a \<times> 'a heap) nres" where
      "pop_min_op h \<equiv> do {
        ASSERT (heap_invar h);
        ASSERT (valid h 1);
        m \<leftarrow> val_of_op h 1;
        let l = length h;
        h \<leftarrow> exch_op h 1 l;
        h \<leftarrow> butlast_op h;
        
        if (l\<noteq>1) then do {
          h \<leftarrow> sink_op h 1;
          RETURN (m,h)
        } else RETURN (m,h)
      }"


    lemma left_not_one[simp]: "left j \<noteq> Suc 0"  
      by (auto simp: left_def)

    lemma right_one_conv[simp]: "right j = Suc 0 \<longleftrightarrow> j=0"
      by (auto simp: right_def)

    lemma parent_one_conv[simp]: "parent (Suc 0) = 0"  
      by (auto simp: parent_def)

    lemma sink_invar_init:
      assumes I: "heap_invar h" 
      assumes NE: "length h > 1" 
      shows "sink_invar (butlast (exch h (Suc 0) (length h))) (Suc 0)"
    proof -
      from NE have V: "valid h (Suc 0)" "valid h (length h)" 
        apply -
        apply (auto simp: valid_def neq_Nil_conv) []
        by (cases h) (auto simp: valid_def)
    
      show ?thesis using I
        unfolding heap_eq_heap' heap_invar'_def sink_invar_def
        apply (intro impI conjI allI)
        using NE apply (auto simp: V valid_butlast_conv) []
        apply (auto simp add: children_ge_def V NE valid_butlast_conv) []
        apply (auto simp add: children_ge_def V NE valid_butlast_conv) []
        done
    qed

    lemma in_set_conv_val: "v \<in> set h \<longleftrightarrow> (\<exists>i. valid h i \<and> v = val_of h i)"
      apply (rule iffI)
      apply (clarsimp simp add: valid_def val_of_def in_set_conv_nth)
      apply (rule_tac x="Suc i" in exI; auto)
      apply (clarsimp simp add: valid_def val_of_def in_set_conv_nth)
      apply (rule_tac x="i - Suc 0" in exI; auto)
      done
      

    lemma pop_min_op_correct: 
      assumes "heap_invar h" "\<alpha> h \<noteq> {#}" 
      shows "pop_min_op h \<le> SPEC (\<lambda>(v,h'). heap_invar h' \<and>
        v \<in># \<alpha> h \<and> \<alpha> h' = \<alpha> h - {#v#} \<and> (\<forall>v'\<in>set_mset (\<alpha> h). prio v \<le> prio v'))"
    proof -    
      note [simp del] = length_greater_0_conv
      note LG = length_greater_0_conv[symmetric]

      from assms show ?thesis
        unfolding pop_min_op_def  
        apply refine_vcg
        apply (simp_all add: sink_invar_init LG)
        apply (auto simp: valid_def) []
        apply (cases h; auto simp: val_of_def) [] (* FIXME: Looking below val_of! *)
        apply (auto simp: in_set_conv_val simp: heap_min_prop) []
        apply auto []
        apply (cases h; auto simp: val_of_def) [] (* FIXME: Looking below val_of! *)
        apply auto []
        apply (cases h; auto simp: val_of_def) [] (* FIXME: Looking below val_of! *)
        done
    qed    

    lemmas [refine_vcg] = pop_min_op_correct

    subsubsection \<open>Peek minimum element\<close>

    definition peek_min_op :: "'a heap \<Rightarrow> 'a nres" where
      "peek_min_op h \<equiv> do {
        ASSERT (heap_invar h);
        ASSERT (valid h 1);
        val_of_op h 1
      }"
    
    lemma peek_min_op_correct:
      assumes "heap_invar h" "\<alpha> h \<noteq> {#}" 
      shows "peek_min_op h \<le> SPEC (\<lambda>v. 
        v \<in># \<alpha> h \<and> (\<forall>v'\<in>set_mset (\<alpha> h). prio v \<le> prio v'))"
      unfolding peek_min_op_def  
      apply refine_vcg
      using assms
      apply clarsimp_all
      apply (auto simp: valid_def) []  
      apply (cases h; auto simp: val_of_def) [] (* FIXME: Looking below val_of! *)
      apply (auto simp: in_set_conv_val simp: heap_min_prop) []
      done
      
    lemmas peek_min_op_correct'[refine_vcg] = peek_min_op_correct


    subsection \<open>Operations as Relator-Style Refinement\<close>

    lemma empty_op_refine: "(empty_op,RETURN op_mset_empty)\<in>\<langle>heap_rel1\<rangle>nres_rel"
      apply (rule nres_relI)
      apply (rule order_trans)  
      apply (rule empty_op_correct)
      apply (auto simp: heap_rel1_def br_def pw_le_iff refine_pw_simps)
      done

    lemma is_empty_op_refine: "(is_empty_op,RETURN o op_mset_is_empty) \<in> heap_rel1 \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
      apply (intro nres_relI fun_relI; simp)
      apply refine_vcg  
      apply (auto simp: heap_rel1_def br_def)
      done  

    lemma insert_op_refine: "(insert_op,RETURN oo op_mset_insert) \<in> Id \<rightarrow> heap_rel1 \<rightarrow> \<langle>heap_rel1\<rangle>nres_rel"
      apply (intro nres_relI fun_relI; simp)
      apply (refine_vcg RETURN_as_SPEC_refine)
      apply (auto simp: heap_rel1_def br_def pw_le_iff refine_pw_simps)
      done  

    lemma pop_min_op_refine: 
      "(pop_min_op, PR_CONST (mop_prio_pop_min prio)) \<in> heap_rel1 \<rightarrow> \<langle>Id \<times>\<^sub>r heap_rel1\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding mop_prio_pop_min_def PR_CONST_def
      apply (refine_vcg SPEC_refine)
      apply (auto simp: heap_rel1_def br_def)
      done

    lemma peek_min_op_refine: 
      "(peek_min_op, PR_CONST (mop_prio_peek_min prio)) \<in> heap_rel1 \<rightarrow> \<langle>Id\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding mop_prio_peek_min_def PR_CONST_def
      apply (refine_vcg RES_refine)
      apply (auto simp: heap_rel1_def br_def)
      done


  end  

end

