theory Projection
imports Main
begin

(* Projection of an event list onto a subset of the events *)
definition projection:: "'e list \<Rightarrow> 'e set \<Rightarrow> 'e list" (infixl "\<upharpoonleft>" 100)
where
"l \<upharpoonleft> E \<equiv> filter (\<lambda>x . x \<in> E) l"

(* If projecting on Y yields the empty sequence, then projecting
  on X \<union> Y yields the projection on X. *)
lemma projection_on_union: 
  "l \<upharpoonleft> Y = [] \<Longrightarrow> l \<upharpoonleft> (X \<union> Y) = l \<upharpoonleft> X"
proof (induct l)
  case Nil show ?case by (simp add: projection_def)
next
  case (Cons a b) show ?case
  proof (cases "a \<in> Y")
    case True from Cons show "a \<in> Y \<Longrightarrow> (a # b) \<upharpoonleft> (X \<union> Y) = (a # b) \<upharpoonleft> X" 
      by (simp add: projection_def)
  next
    case False from Cons show "a \<notin> Y \<Longrightarrow> (a # b) \<upharpoonleft> (X \<union> Y) = (a # b) \<upharpoonleft> X" 
      by (simp add: projection_def)
  qed
qed

(*projection on the empty trace yields the empty trace*)
lemma projection_on_empty_trace: "[] \<upharpoonleft> X =[]" by (simp add: projection_def)

(*projection to the empty set yields the empty trace*)
lemma projection_to_emptyset_is_empty_trace: "l \<upharpoonleft>{} = []" by (simp add: projection_def)

(*projection is idempotent*)
lemma projection_idempotent: "l \<upharpoonleft> X= (l \<upharpoonleft>X) \<upharpoonleft>X" by (simp add: projection_def) 

(*empty projection implies that the trace contains no events of the set the trace is projected to*)
lemma projection_empty_implies_absence_of_events: "l \<upharpoonleft> X = [] \<Longrightarrow>  X \<inter> (set l) = {}" 
 by (metis empty_set inter_set_filter projection_def)

(*subsequently projecting to two disjoint sets yields the empty trace*)
lemma disjoint_projection: "X \<inter> Y = {} \<Longrightarrow> (l \<upharpoonleft> X) \<upharpoonleft> Y = []" 
proof -
  assume X_Y_disjoint: "X \<inter> Y = {}"
  show "(l \<upharpoonleft> X) \<upharpoonleft> Y = []" unfolding projection_def 
  proof (induct l)
    case Nil show ?case by simp
  next
    case (Cons x xs) show ?case
    proof (cases "x \<in> X")
      case True
      with X_Y_disjoint have "x \<notin> Y" by auto
      thus "[x\<leftarrow>[x\<leftarrow>x # xs . x \<in> X] . x \<in> Y] = []" using Cons.hyps by auto
    next
      case False show "[x\<leftarrow>[x\<leftarrow>x # xs . x \<in> X] . x \<in> Y] = []" using Cons.hyps False by auto
    qed
  qed  
qed      

(* auxiliary lemmas for projection *)
lemma projection_concatenation_commute:
  "(l1 @ l2) \<upharpoonleft> X = (l1 \<upharpoonleft> X) @ (l2 \<upharpoonleft> X)"
  by (unfold projection_def, auto)

(* Lists that are equal under projection on a set will remain 
equal under projection on a subset. *)
lemma projection_subset_eq_from_superset_eq: 
"((xs \<upharpoonleft> (X \<union> Y)) = (ys \<upharpoonleft> (X \<union> Y))) \<Longrightarrow> ((xs \<upharpoonleft> X) = (ys \<upharpoonleft> X))"
(is "(?L1 = ?L2) \<Longrightarrow> (?L3 = ?L4)")
proof -
  assume prem: "?L1 = ?L2"  
  have "?L1 \<upharpoonleft> X = ?L3 \<and> ?L2 \<upharpoonleft> X = ?L4"
  proof -
    have "\<And> a. ((a \<in> X \<or> a \<in> Y) \<and> a \<in> X) = (a \<in> X)" 
      by auto
    thus ?thesis
      by (simp add: projection_def)
  qed   
  with prem show ?thesis
    by auto
qed

(* All elements of a list l are in a set X if and only if
 the projection of l onto X yields l. *)
lemma list_subset_iff_projection_neutral: "(set l \<subseteq> X) = ((l \<upharpoonleft> X) = l)"
(is "?A = ?B")
proof -
  have "?A \<Longrightarrow> ?B"
    proof -
      assume "?A"
      hence "\<And>x. x \<in> (set l) \<Longrightarrow> x \<in> X"
        by auto
      thus ?thesis
        by (simp add: projection_def)
    qed
  moreover 
  have "?B \<Longrightarrow> ?A"
    proof -
      assume "?B"
      hence "(set (l \<upharpoonleft> X)) = set l"
        by (simp add: projection_def)
      thus ?thesis
        by (simp add: projection_def, auto)
    qed
  ultimately show ?thesis ..
qed

(* If the projection of \<tau> onto a set X is not the empty trace, then 
there is x \<in> X that is the last occurrence of all elements of X in \<tau>. 
\<tau> can then be split around x.

Expressing non-emptiness in terms of list length is quite useful
for inductive proofs. *)
lemma projection_split_last: "Suc n = length (\<tau> \<upharpoonleft> X) \<Longrightarrow> 
\<exists> \<beta> x \<alpha>. (x \<in> X \<and> \<tau> = \<beta> @ [x] @ \<alpha> \<and> \<alpha> \<upharpoonleft> X = [] \<and> n = length ((\<beta> @ \<alpha>) \<upharpoonleft> X))"
proof -
  assume Suc_n_is_len_\<tau>X: "Suc n = length (\<tau> \<upharpoonleft> X)"

  let ?L = "\<tau> \<upharpoonleft> X"
  let ?RL = "filter (\<lambda>x . x \<in> X) (rev \<tau>)"

  have "Suc n = length ?RL"
  proof -
    have "rev ?L = ?RL"
      by (simp add: projection_def, rule rev_filter)
    hence "rev (rev ?L) = rev ?RL" ..
    hence "?L = rev ?RL"
      by auto
    with Suc_n_is_len_\<tau>X show ?thesis
      by auto
  qed
  with Suc_length_conv[of n ?RL] obtain x xs
    where "?RL = x # xs"
    by auto
  hence "x # xs = ?RL" 
    by auto
  
  from Cons_eq_filterD[OF this] obtain rev\<alpha> rev\<beta>
    where "(rev \<tau>) = rev\<alpha> @ x # rev\<beta>"
    and rev\<alpha>_no_x: "\<forall>a \<in> set rev\<alpha>. a \<notin> X"
    and x_in_X: "x \<in> X"
    by auto
  hence "rev (rev \<tau>) = rev (rev\<alpha> @ x # rev\<beta>)"
    by auto
  hence "\<tau> = (rev rev\<beta>) @ [x] @ (rev rev\<alpha>)"
    by auto
  then obtain \<beta> \<alpha>
    where \<tau>_is_\<beta>x\<alpha>: "\<tau> = \<beta> @ [x] @ \<alpha>"
    and \<alpha>_is_revrev\<alpha>: "\<alpha> = (rev rev\<alpha>)"
    and \<beta>_is_revrev\<beta>: "\<beta> = (rev rev\<beta>)"
    by auto
  hence \<alpha>_no_x: "\<alpha> \<upharpoonleft> X = []"
  proof -
    from \<alpha>_is_revrev\<alpha> rev\<alpha>_no_x have "\<forall>a \<in> set \<alpha>. a \<notin> X"
      by auto
    thus ?thesis 
      by (simp add: projection_def)
  qed

  have "n = length ((\<beta> @ \<alpha>) \<upharpoonleft> X)"
  proof -
    from \<alpha>_no_x have \<alpha>X_zero_len: "length (\<alpha> \<upharpoonleft> X) = 0"
      by auto

    from x_in_X have xX_one_len: "length ([x] \<upharpoonleft> X) = 1"
      by (simp add: projection_def)

    from \<tau>_is_\<beta>x\<alpha> have "length ?L = length (\<beta> \<upharpoonleft> X) + length ([x] \<upharpoonleft> X) + length (\<alpha> \<upharpoonleft> X)"
      by (simp add: projection_def)            
    with \<alpha>X_zero_len have "length ?L = length (\<beta> \<upharpoonleft> X) + length ([x] \<upharpoonleft> X)"
      by auto
    with xX_one_len Suc_n_is_len_\<tau>X have "n = length (\<beta> \<upharpoonleft> X)"
      by auto
    with \<alpha>X_zero_len show ?thesis
      by (simp add: projection_def)
  qed
  with x_in_X \<tau>_is_\<beta>x\<alpha> \<alpha>_no_x show ?thesis
    by auto
qed

lemma projection_rev_commute:
  "rev (l \<upharpoonleft> X) = (rev l) \<upharpoonleft> X"
  by (induct l, simp add: projection_def, simp add: projection_def)

(* Same as the previous lemma except that we split around the FIRST
    occurrence.

    Note that we do not express non-emptiness via the length function
    simply because there is no need for it in the theories relying on
    this lemma. *)
lemma projection_split_first: "\<lbrakk> (\<tau> \<upharpoonleft> X) = x # xs \<rbrakk> \<Longrightarrow> \<exists> \<alpha> \<beta>. (\<tau> = \<alpha> @ [x] @ \<beta> \<and> \<alpha> \<upharpoonleft> X = [])"
proof -
  assume \<tau>X_is_x_xs: "(\<tau> \<upharpoonleft> X) = x # xs"
  hence "0 \<noteq> length (\<tau> \<upharpoonleft> X)"
    by auto
  hence "0 \<noteq> length (rev (\<tau> \<upharpoonleft> X))"
    by auto
  hence "0 \<noteq> length ((rev \<tau>) \<upharpoonleft> X)"
    by (simp add: projection_rev_commute)
  then obtain n where "Suc n = length ((rev \<tau>) \<upharpoonleft> X)"
    by (auto, metis Suc_pred length_greater_0_conv that)
  from projection_split_last[OF this] obtain \<beta>' x' \<alpha>' 
    where x'_in_X: "x' \<in> X"
    and rev\<tau>_is_\<beta>'x'\<alpha>': "rev \<tau> = \<beta>' @ [x'] @ \<alpha>'"
    and \<alpha>'X_empty: "\<alpha>' \<upharpoonleft> X = []"
    by auto

  from rev\<tau>_is_\<beta>'x'\<alpha>' have "rev (rev \<tau>) = rev (\<beta>' @ [x'] @ \<alpha>')" ..
  hence \<tau>_is_rev\<alpha>'_x'_rev\<beta>':"\<tau> = rev \<alpha>' @ [x'] @ rev \<beta>'"
    by auto
  moreover
  from \<alpha>'X_empty have rev\<alpha>'X_empty: "rev \<alpha>' \<upharpoonleft> X = []"
    by (metis projection_rev_commute rev_is_Nil_conv)
  moreover
  note x'_in_X
  ultimately have "(\<tau> \<upharpoonleft> X) = x' # ((rev \<beta>') \<upharpoonleft> X)"
    by (simp only: projection_concatenation_commute projection_def, auto)
  with \<tau>X_is_x_xs have "x = x'"
    by auto
  with \<tau>_is_rev\<alpha>'_x'_rev\<beta>' have \<tau>_is_rev\<alpha>'_x_rev\<beta>': "\<tau> = rev \<alpha>' @ [x] @ rev \<beta>'"
    by auto
  with rev\<alpha>'X_empty show ?thesis
    by auto
qed

(* this lemma extends the previous lemma by also concluding that the suffix of the splitted trace
   projected is equal to the projection of the initial trace without the first element *)
lemma projection_split_first_with_suffix: 
  "\<lbrakk> (\<tau> \<upharpoonleft> X) = x # xs \<rbrakk> \<Longrightarrow> \<exists> \<alpha> \<beta>. (\<tau> = \<alpha> @ [x] @ \<beta> \<and> \<alpha> \<upharpoonleft> X = [] \<and> \<beta> \<upharpoonleft> X = xs)" 
proof -
  assume tau_proj_X: "(\<tau> \<upharpoonleft> X) = x # xs"
  show ?thesis
  proof - 
    from   tau_proj_X have x_in_X: "x \<in> X"
      by (metis IntE inter_set_filter list.set_intros(1) projection_def)
    from  tau_proj_X have  "\<exists> \<alpha> \<beta>. \<tau> = \<alpha> @ [x] @ \<beta> \<and> \<alpha> \<upharpoonleft> X = []"
      using projection_split_first by auto
    then obtain \<alpha> \<beta> where tau_split: "\<tau> = \<alpha> @ [x] @ \<beta>"
                      and X_empty_prefix:"\<alpha> \<upharpoonleft> X = []"
      by auto
    from tau_split tau_proj_X  have  "(\<alpha> @ [x] @ \<beta>) \<upharpoonleft> X =x # xs"
      by auto
    with  X_empty_prefix have  "([x] @ \<beta>) \<upharpoonleft> X =x # xs"
      by (simp add: projection_concatenation_commute)   
    hence "(x # \<beta>) \<upharpoonleft> X =x # xs"
      by auto
    with  x_in_X have "\<beta> \<upharpoonleft> X = xs"
      unfolding projection_def by simp
    with  tau_split X_empty_prefix show ?thesis
      by auto
  qed   
qed




lemma projection_split_arbitrary_element: 
  "\<lbrakk>\<tau> \<upharpoonleft> X = (\<alpha> @ [x] @ \<beta>) \<upharpoonleft> X; x \<in> X \<rbrakk> 
      \<Longrightarrow> \<exists> \<alpha>' \<beta>'. (\<tau> = \<alpha>' @ [x] @ \<beta>' \<and> \<alpha>' \<upharpoonleft> X = \<alpha> \<upharpoonleft> X \<and> \<beta>' \<upharpoonleft> X = \<beta> \<upharpoonleft> X)" 
proof -
  assume "\<tau> \<upharpoonleft> X = (\<alpha> @ [x] @ \<beta>) \<upharpoonleft> X"
  and  " x \<in> X"
  { 
    fix n
    have "\<lbrakk>\<tau> \<upharpoonleft> X = (\<alpha> @ [x] @ \<beta>) \<upharpoonleft> X; x \<in> X; n = length(\<alpha>\<upharpoonleft>X) \<rbrakk>
          \<Longrightarrow> \<exists> \<alpha>' \<beta>'. (\<tau> = \<alpha>' @ [x] @ \<beta>' \<and> \<alpha>' \<upharpoonleft> X = \<alpha> \<upharpoonleft> X \<and> \<beta>' \<upharpoonleft> X = \<beta> \<upharpoonleft> X)"
    proof (induct n arbitrary: \<tau> \<alpha> )
      case 0
      hence "\<alpha>\<upharpoonleft>X = []"
        unfolding projection_def by simp
      with "0.prems"(1) "0.prems"(2) have "\<tau>\<upharpoonleft>X = x # \<beta>\<upharpoonleft>X"
        unfolding projection_def by simp
      with \<open>\<alpha>\<upharpoonleft>X = []\<close> show ?case
        using projection_split_first_with_suffix by fastforce
    next
      case (Suc n)
      from "Suc.prems"(1) have "\<tau>\<upharpoonleft>X=\<alpha>\<upharpoonleft>X @ ([x] @ \<beta>) \<upharpoonleft>X"
        using projection_concatenation_commute by auto
      from "Suc.prems"(3) obtain x' xs' where "\<alpha> \<upharpoonleft>X= x' #xs'"
                                            and "x' \<in> X" 
        by (metis filter_eq_ConsD length_Suc_conv projection_def)
      then obtain a\<^sub>1 a\<^sub>2 where "\<alpha> = a\<^sub>1 @ [x'] @ a\<^sub>2" 
                         and "a\<^sub>1\<upharpoonleft>X = []"
                         and "a\<^sub>2\<upharpoonleft>X = xs'" 
        using projection_split_first_with_suffix by metis
      with \<open>x' \<in> X\<close> "Suc.prems"(1) have "\<tau>\<upharpoonleft>X= x' #  (a\<^sub>2 @ [x] @ \<beta>) \<upharpoonleft>X" 
        unfolding projection_def by simp 
      then obtain t\<^sub>1 t\<^sub>2 where "\<tau>= t\<^sub>1 @ [x'] @ t\<^sub>2"
                         and "t\<^sub>1\<upharpoonleft>X = []"
                         and "t\<^sub>2\<upharpoonleft>X = (a\<^sub>2 @ [x] @ \<beta>) \<upharpoonleft>X"
        using projection_split_first_with_suffix by metis
      from Suc.prems(3) \<open>\<alpha> \<upharpoonleft>X= x' # xs'\<close> \<open>\<alpha> = a\<^sub>1 @ [x'] @ a\<^sub>2\<close> \<open>a\<^sub>1\<upharpoonleft>X = []\<close> \<open>a\<^sub>2\<upharpoonleft>X = xs'\<close>
      have "n=length(a\<^sub>2\<upharpoonleft>X)"
        by auto               
      with "Suc.hyps"(1) "Suc.prems"(2) \<open>t\<^sub>2\<upharpoonleft>X = (a\<^sub>2 @ [x] @ \<beta>) \<upharpoonleft>X\<close> 
        obtain t\<^sub>2' t\<^sub>3' where "t\<^sub>2=t\<^sub>2' @ [x] @ t\<^sub>3'"
                         and "t\<^sub>2'\<upharpoonleft>X = a\<^sub>2\<upharpoonleft>X"
                         and "t\<^sub>3'\<upharpoonleft>X = \<beta>\<upharpoonleft>X"
          using projection_concatenation_commute by blast
      
      let ?\<alpha>'="t\<^sub>1 @ [x'] @ t\<^sub>2'" and ?\<beta>'="t\<^sub>3'"
      from \<open>\<tau>= t\<^sub>1 @ [x'] @ t\<^sub>2\<close> \<open>t\<^sub>2=t\<^sub>2' @ [x] @ t\<^sub>3'\<close> have "\<tau>=?\<alpha>'@[x]@?\<beta>'"
        by auto
      moreover
      from  \<open>\<alpha> \<upharpoonleft>X= x' # xs'\<close>  \<open>t\<^sub>1\<upharpoonleft>X = []\<close> \<open>x' \<in> X\<close> \<open>t\<^sub>2'\<upharpoonleft>X = a\<^sub>2\<upharpoonleft>X\<close> \<open>a\<^sub>2\<upharpoonleft>X = xs'\<close>
      have "?\<alpha>'\<upharpoonleft>X = \<alpha>\<upharpoonleft>X"
        using projection_concatenation_commute unfolding projection_def by simp 
      ultimately
      show ?case using \<open>t\<^sub>3'\<upharpoonleft>X = \<beta>\<upharpoonleft>X\<close>
        by blast
    qed    
  }
  with \<open>\<tau> \<upharpoonleft> X = (\<alpha> @ [x] @ \<beta>) \<upharpoonleft> X\<close> \<open> x \<in> X\<close> show ?thesis
    by simp
qed
        
(* If the projection of a list l onto a set X is empty, it
    will remain empty when projecting further. *)
lemma projection_on_intersection: "l \<upharpoonleft> X = [] \<Longrightarrow> l \<upharpoonleft> (X \<inter> Y) = []"
(is "?L1 = [] \<Longrightarrow> ?L2 = []")
proof -
  assume "?L1 = []"
  hence "set ?L1 = {}" 
    by simp
  moreover
  have "set ?L2 \<subseteq> set ?L1"
    by (simp add: projection_def, auto)
  ultimately have "set ?L2 = {}"
    by auto
  thus ?thesis
    by auto
qed

(* The previous lemma expressed with subsets. *)
lemma projection_on_subset: "\<lbrakk> Y \<subseteq> X; l \<upharpoonleft> X = [] \<rbrakk> \<Longrightarrow> l \<upharpoonleft> Y = []"
proof -
  assume subset: "Y \<subseteq> X"
  assume proj_empty: "l \<upharpoonleft> X = []"
  hence "l \<upharpoonleft> (X \<inter> Y) = []"
    by (rule projection_on_intersection)
  moreover
  from subset have "X \<inter> Y = Y"
    by auto
  ultimately show ?thesis
    by auto
qed

(* Another variant that is used in proofs of BSP compositionality theorems. *)
lemma projection_on_subset2: "\<lbrakk> set l \<subseteq> L; l \<upharpoonleft> X' = []; X \<inter> L \<subseteq> X' \<rbrakk> \<Longrightarrow> l \<upharpoonleft> X = []"
proof -
  assume setl_subset_L: "set l \<subseteq> L"
  assume l_no_X': "l \<upharpoonleft> X' = []"
  assume X_inter_L_subset_X': "X \<inter> L \<subseteq> X'"

  from X_inter_L_subset_X' l_no_X' have "l \<upharpoonleft> (X \<inter> L) = []"
    by (rule projection_on_subset)
  moreover
  have "l \<upharpoonleft> (X \<inter> L) = (l \<upharpoonleft> L) \<upharpoonleft> X"
    by (simp add: Int_commute projection_def)
  moreover
  note setl_subset_L
  ultimately show ?thesis
    by (simp add: list_subset_iff_projection_neutral)
qed  

(*If the projection of two lists l1 and l2  onto a set Y is equal then its also equal for all X \<subseteq> Y*)
lemma non_empty_projection_on_subset: "X \<subseteq> Y \<and> l\<^sub>1 \<upharpoonleft> Y = l\<^sub>2 \<upharpoonleft> Y \<Longrightarrow>  l\<^sub>1 \<upharpoonleft> X = l\<^sub>2 \<upharpoonleft> X" 
  by (metis projection_subset_eq_from_superset_eq subset_Un_eq)

(* Intersecting a projection set with a list's elements does not change the result
    of the projection. *)
lemma projection_intersection_neutral: "(set l \<subseteq> X) \<Longrightarrow> (l \<upharpoonleft> (X \<inter> Y) = l \<upharpoonleft> Y)"
proof -
  assume "set l \<subseteq> X"
  hence "(l \<upharpoonleft> X) = l"
    by (simp add: list_subset_iff_projection_neutral)
  hence "(l \<upharpoonleft> X) \<upharpoonleft> Y = l \<upharpoonleft> Y"
    by simp
  moreover
  have "(l \<upharpoonleft> X) \<upharpoonleft> Y = l \<upharpoonleft> (X \<inter> Y)"
    by (simp add: projection_def)
  ultimately show ?thesis
    by simp
qed

lemma projection_commute:
  "(l \<upharpoonleft> X) \<upharpoonleft> Y = (l \<upharpoonleft> Y) \<upharpoonleft> X"
  by (simp add: projection_def conj_commute)


lemma projection_subset_elim: "Y \<subseteq> X \<Longrightarrow> (l \<upharpoonleft> X) \<upharpoonleft> Y = l \<upharpoonleft> Y"
by (simp only: projection_def, metis Diff_subset list_subset_iff_projection_neutral
    minus_coset_filter order_trans projection_commute projection_def)


lemma projection_sequence: "(xs \<upharpoonleft> X) \<upharpoonleft> Y = (xs \<upharpoonleft> (X \<inter> Y))"
by (metis Int_absorb inf_sup_ord(1) list_subset_iff_projection_neutral
    projection_intersection_neutral projection_subset_elim)


(* This function yields a possible interleaving for given 
  traces t1 and t2.
  The set A (B) shall denote the the set of events for t1 (t2).
  Non-synchronization events in trace t1 are prioritized. *)
fun merge :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e list \<Rightarrow> 'e list \<Rightarrow> 'e list"
where
"merge A B [] t2 = t2" |
"merge A B t1 [] = t1" |
"merge A B (e1 # t1') (e2 # t2') = (if e1 = e2 then 
                                          e1 # (merge A B t1' t2')
                                        else (if e1 \<in> (A \<inter> B) then
                                               e2 # (merge A B (e1 # t1') t2')
                                             else e1 # (merge A B t1' (e2 # t2'))))"

(* If two traces can be interleaved, then merge yields such an interleaving  *)
lemma merge_property: "\<lbrakk>set t1 \<subseteq> A; set t2 \<subseteq> B; t1 \<upharpoonleft> B = t2 \<upharpoonleft> A \<rbrakk> 
  \<Longrightarrow> let t = (merge A B t1 t2) in (t \<upharpoonleft> A = t1 \<and> t \<upharpoonleft> B = t2 \<and> set t \<subseteq> ((set t1) \<union> (set t2)))"
unfolding Let_def
proof (induct A B t1 t2 rule: merge.induct)
  case (1 A B t2) thus ?case
    by (metis Un_empty_left empty_subsetI list_subset_iff_projection_neutral 
      merge.simps(1) set_empty subset_iff_psubset_eq)
next
  case (2 A B t1) thus ?case
    by (metis Un_empty_right empty_subsetI list_subset_iff_projection_neutral 
      merge.simps(2) set_empty subset_refl)
next
  case (3 A B e1 t1' e2 t2') thus ?case
  proof (cases)
    assume e1_is_e2: "e1 = e2"
    
    note e1_is_e2 
    moreover
    from 3(4) have "set t1' \<subseteq> A"
      by auto
    moreover
    from 3(5) have "set t2' \<subseteq> B"
      by auto
    moreover
    from e1_is_e2 3(4-6) have "t1' \<upharpoonleft> B = t2' \<upharpoonleft> A"
      by (simp add: projection_def)
    moreover
    note 3(1)
    ultimately have ind1: "merge A B t1' t2' \<upharpoonleft> A = t1'"
      and ind2: "merge A B t1' t2' \<upharpoonleft> B = t2'"
      and ind3: "set (merge A B t1' t2') \<subseteq> (set t1') \<union> (set t2')"
      by auto
    
    from e1_is_e2 have merge_eq: 
      "merge A B (e1 # t1') (e2 # t2') = e1 # (merge A B t1' t2')"
      by auto

    from 3(4) ind1 have goal1: 
      "merge A B (e1 # t1') (e2 # t2') \<upharpoonleft> A = e1 # t1'"
      by (simp only: merge_eq projection_def, auto)
    moreover
    from e1_is_e2 3(5) ind2 have goal2: 
      "merge A B (e1 # t1') (e2 # t2') \<upharpoonleft> B = e2 # t2'"
      by (simp only: merge_eq projection_def, auto)
    moreover
    from ind3 have goal3: 
      "set (merge A B (e1 # t1') (e2 # t2')) \<subseteq> set (e1 # t1') \<union> set (e2 # t2')"
      by (simp only: merge_eq, auto)
    ultimately show ?thesis
      by auto (* case (3 e1 t1' e2 t2') for e1 = e2 *)
  next
    assume e1_isnot_e2: "e1 \<noteq> e2"
    show ?thesis
    proof (cases)
      assume e1_in_A_inter_B: "e1 \<in> A \<inter> B"
      
      from 3(6) e1_isnot_e2 e1_in_A_inter_B have e2_notin_A: "e2 \<notin> A"
        by (simp add: projection_def, auto)
      
      note e1_isnot_e2 e1_in_A_inter_B 3(4)
      moreover
      from 3(5) have "set t2' \<subseteq> B"
        by auto
      moreover
      from 3(6) e1_isnot_e2 e1_in_A_inter_B have "(e1 # t1') \<upharpoonleft> B = t2' \<upharpoonleft> A"
        by (simp add: projection_def, auto)
      moreover
      note 3(2)
      ultimately have ind1: "merge A B (e1 # t1') t2' \<upharpoonleft> A = (e1 # t1')"
        and ind2: "merge A B (e1 # t1') t2' \<upharpoonleft> B = t2'"
        and ind3: "set (merge A B (e1 # t1') t2') \<subseteq> set (e1 # t1') \<union> set t2'"
        by auto
      
      from e1_isnot_e2 e1_in_A_inter_B 
      have merge_eq: 
        "merge A B (e1 # t1') (e2 # t2') = e2 # (merge A B (e1 # t1') t2')"
        by auto
 
      from e1_isnot_e2 ind1 e2_notin_A have goal1: 
        "merge A B (e1 # t1') (e2 # t2') \<upharpoonleft> A = e1 # t1'"
        by (simp only: merge_eq projection_def, auto)
      moreover
      from 3(5) ind2 have goal2: "merge A B (e1 # t1') (e2 # t2') \<upharpoonleft> B = e2 # t2'"
        by (simp only: merge_eq projection_def, auto)
      moreover
      from 3(5) ind3 have goal3: 
        "set (merge A B (e1 # t1') (e2 # t2')) \<subseteq> set (e1 # t1') \<union> set (e2 # t2')"
        by (simp only: merge_eq, auto)
      ultimately show ?thesis
        by auto (* case (3 e1 t1' e2 t2') for e1 \<noteq> e2 e1 \<in> A \<inter> B *)
    next
      assume e1_notin_A_inter_B: "e1 \<notin> A \<inter> B"
      
      from 3(4) e1_notin_A_inter_B have e1_notin_B: "e1 \<notin> B"
        by auto
      
      note e1_isnot_e2 e1_notin_A_inter_B
      moreover
      from 3(4) have "set t1' \<subseteq> A"
        by auto
      moreover
      note 3(5)
      moreover
      from 3(6) e1_notin_B have "t1' \<upharpoonleft> B = (e2 # t2') \<upharpoonleft> A"
        by (simp add: projection_def)
      moreover
      note 3(3)
      ultimately have ind1: "merge A B t1' (e2 # t2') \<upharpoonleft> A = t1'"
        and ind2: "merge A B t1' (e2 # t2') \<upharpoonleft> B = (e2 # t2')"
        and ind3: "set (merge A B t1' (e2 # t2')) \<subseteq> set t1' \<union> set (e2 # t2')"
        by auto
      
      from e1_isnot_e2 e1_notin_A_inter_B 
      have merge_eq: "merge A B (e1 # t1') (e2 # t2') = e1 # (merge A B t1' (e2 # t2'))"
        by auto
      
      from 3(4) ind1 have goal1: "merge A B (e1 # t1') (e2 # t2') \<upharpoonleft> A = e1 # t1'"
        by (simp only: merge_eq projection_def, auto)
      moreover
      from ind2 e1_notin_B have goal2: 
        "merge A B (e1 # t1') (e2 # t2') \<upharpoonleft> B = e2 # t2'"
        by (simp only: merge_eq projection_def, auto)
      moreover
      from 3(4) ind3 have goal3: 
        "set (merge A B (e1 # t1') (e2 # t2')) \<subseteq> set (e1 # t1') \<union> set (e2 # t2')"
        by (simp only: merge_eq, auto)
      ultimately show ?thesis
        by auto (* case (3 e1 t1' e2 t2') for e1 \<noteq> e2 e1 \<notin> A \<inter> B *)
    qed
  qed
qed

end
