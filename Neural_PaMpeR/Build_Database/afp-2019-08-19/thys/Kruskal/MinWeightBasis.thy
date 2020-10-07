section \<open>Minimum Weight Basis\<close>

theory MinWeightBasis
  imports "Refine_Monadic.Refine_Monadic" Matroids.Matroid    
begin
  
text \<open>For a matroid together with a weight function, assigning each element
  of the carrier set an weight, we construct a greedy algorithm that determines
  a minimum weight basis.\<close>

(* TODO: consider greedoids instead of matroids as a more
   general class of structures that allow a greedy min weight algorithm *)

locale weighted_matroid = matroid carrier indep for carrier::"'a set" and indep  +
  fixes weight :: "'a \<Rightarrow> 'b::{linorder, ordered_comm_monoid_add}"
begin
    
definition minBasis where
  "minBasis B \<equiv> basis B \<and> (\<forall>B'. basis B' \<longrightarrow> sum weight B \<le> sum weight B')"

                             
subsection \<open>Preparations\<close>
     
fun in_sort_edge where
   "in_sort_edge x [] = [x]" 
 | "in_sort_edge x (y#ys) = (if weight x \<le> weight y then x#y#ys else y# in_sort_edge x ys)"  

lemma [simp]: "set (in_sort_edge x L) = insert x (set L)" by (induct L, auto)

lemma in_sort_edge: "sorted_wrt (\<lambda>e1 e2. weight e1 \<le> weight e2) L
         \<Longrightarrow> sorted_wrt (\<lambda>e1 e2. weight e1 \<le> weight e2) (in_sort_edge x L)"
  by (induct L, auto)
   
lemma in_sort_edge_distinct: "x \<notin> set L \<Longrightarrow> distinct L \<Longrightarrow> distinct (in_sort_edge x L)"    
  by (induct L, auto) 
    
lemma finite_sorted_edge_distinct:
  assumes "finite S" 
  obtains L where "distinct L" "sorted_wrt (\<lambda>e1 e2. weight e1 \<le> weight e2) L" "S = set L"
proof -
  {
    have "\<exists>L.  distinct L \<and> sorted_wrt (\<lambda>e1 e2. weight e1 \<le> weight e2) L \<and> S = set L"
      using assms
      apply(induct S)
       apply(clarsimp)
      apply(clarsimp) 
      subgoal for x L apply(rule exI[where x="in_sort_edge x L"])
        by (auto simp: in_sort_edge in_sort_edge_distinct)
      done
  }
  with that show ?thesis by blast
qed    
    
abbreviation "wsorted == sorted_wrt (\<lambda>e1 e2. weight e1 \<le> weight e2)"
 
lemma sum_list_map_cons:
  "sum_list (map weight (y # ys)) = weight y + sum_list (map weight ys)" 
  by auto
     
lemma exists_greater:
  assumes  len: "length F = length F'"
      and sum: "sum_list (map weight F) > sum_list (map weight F')"
    shows "\<exists>i<length F. weight (F ! i) > weight (F' ! i)"
using len sum    
proof (induct rule: list_induct2) 
  case (Cons x xs y ys)    
  from Cons(3)
  have *: "~ weight y < weight x \<Longrightarrow> sum_list (map weight ys) < sum_list (map weight xs)" 
    by (metis add_mono not_less sum_list_map_cons)
  show ?case              
    using Cons * 
    by (cases "weight y < weight x", auto)
qed simp
  
  
lemma wsorted_nth_mono: assumes "wsorted L" "i\<le>j" "j<length L"
  shows "weight (L!i) \<le> weight (L!j)"
  using assms by (induct L arbitrary: i j rule: list.induct, auto simp: nth_Cons') 

    
subsubsection \<open>Weight restricted set\<close>

text \<open>limi T g is the set T restricted  
     to elements only with weight
    strictly smaller than g.\<close>

definition "limi T g == {e. e\<in>T \<and> weight e < g}"
  
lemma limi_subset: "limi T g \<subseteq> T" by (auto simp: limi_def)  
  
lemma limi_mono: "A \<subseteq> B \<Longrightarrow> limi A g \<subseteq> limi B g"  by (auto simp: limi_def) 

subsubsection \<open>The greedy idea\<close>

definition "no_smallest_element_skipped E F
   = (\<forall>e\<in>carrier - E. \<forall>g>weight e. indep (insert e (limi F g)) \<longrightarrow> (e \<in> limi F g))"

text  \<open>let @{term F} be a set of elements
  @{term \<open>limi F g\<close>} is @{term F} restricted to elements with weight smaller than @{term g}
  let @{term E} be a set of elements we want to exclude.
    
  @{term \<open>no_smallest_element_skipped E F\<close>} expresses,
     that going greedily over @{term \<open>carrier-E\<close>}, every element that did not
     render the accumulated set dependent, was added to the set @{term F}.\<close>


lemma no_smallest_element_skipped_empty[simp]: "no_smallest_element_skipped carrier {}"
  by(auto simp: no_smallest_element_skipped_def)

lemma no_smallest_element_skippedD:
  assumes "no_smallest_element_skipped E F" "e \<in>carrier - E"
      "weight e < g" "(indep (insert e (limi F g)))"
  shows "e\<in> limi F g"
  using assms by(auto simp: no_smallest_element_skipped_def)

lemma no_smallest_element_skipped_skip: 
  assumes createsCycle: "\<not> indep (insert e F)"
       and    I: "no_smallest_element_skipped (E\<union>{e}) F"
       and    sorted: "(\<forall>x\<in>F.\<forall>y\<in>(E\<union>{e}). weight x \<le> weight y)"
     shows "no_smallest_element_skipped E F"
  unfolding no_smallest_element_skipped_def
proof (clarsimp)
  fix x g
  assume x: "x \<in> carrier"  "x \<notin> E"  "weight x < g"
  assume f: "indep (insert x (limi F g))" 
  show "(x \<in> limi F g)"  
  proof (cases "x=e")
    case True 
    from True have "limi F g = F"
      unfolding limi_def using \<open>weight x < g\<close> sorted by fastforce  
    with createsCycle f True have "False" by auto  
    then show ?thesis by simp
  next
    case False
    show ?thesis 
    apply(rule I[THEN no_smallest_element_skippedD, OF _ \<open>weight x < g\<close>])
    using x f False
    by auto
  qed
qed
  
lemma no_smallest_element_skipped_add:
  assumes I: "no_smallest_element_skipped (E\<union>{e}) F"
  shows "no_smallest_element_skipped E (insert e F)"
  unfolding no_smallest_element_skipped_def
proof (clarsimp)
  fix x g
  assume xc: "x \<in> carrier"
  assume x: "x \<notin> E"
  assume wx: "weight x < g"
  assume f: "indep (insert x (limi (insert e F) g))"
  show "(x \<in> limi (insert e F) g)"
  proof(cases "x=e")
    case True   
    then show ?thesis unfolding limi_def
      using wx by blast 
  next
    case False
    have ind: "indep (insert x (limi F g))"
      apply(rule indep_subset[OF f]) using limi_mono by blast  
    have "indep (insert x (limi F g)) \<Longrightarrow> x \<in> limi F g" 
      apply(rule I[THEN no_smallest_element_skippedD]) using False xc wx x by auto
    with ind show ?thesis using limi_mono by blast
  qed      
qed  


subsection \<open>Minimum Weight Basis algorithm\<close>


definition "obtain_sorted_carrier \<equiv> SPEC (\<lambda>L. wsorted L \<and> set L = carrier)"

abbreviation "empty_basis \<equiv> {}"

text \<open>To compute a minimum weight basis one obtains a list of the carrier set sorted ascendingly
  by the weight function. Then one iterates over the list and adds an elements greedily to 
  the independent set if it does not render the set dependet.\<close>

definition minWeightBasis where 
  "minWeightBasis \<equiv> do {
        l \<leftarrow> obtain_sorted_carrier;
        ASSERT (set l = carrier);
        T \<leftarrow> nfoldli l (\<lambda>_. True) 
        (\<lambda>e T. do { 
            ASSERT (indep T \<and> e\<in>carrier \<and> T\<subseteq>carrier);
            if indep (insert e T) then
              RETURN (insert e T)
            else 
              RETURN T
        }) empty_basis;
        RETURN T
      }"

 
subsection \<open>The heart of the argument\<close>

text \<open>The algorithmic idea above is correct, as an independent set, which
  is inclusion maximal and has not skipped any smaller element, is a minimum weight basis. \<close>

lemma greedy_approach_leads_to_minBasis: assumes indep: "indep F"
  and inclmax: "\<forall>e\<in>carrier - F. \<not> indep (insert e F)"
  and "no_smallest_element_skipped {} F"
  shows "minBasis F"
proof (rule ccontr)
  \<comment> \<open>from our assumptions we have that F is a basis\<close>  
  from indep inclmax have bF: "basis F" using indep_not_basis by blast
  \<comment> \<open>towards a contradiction, assume F is not a minimum Basis\<close>
  assume notmin: "\<not> minBasis F"    
  \<comment> \<open>then we can get a smaller Basis B\<close>
  from bF notmin[unfolded minBasis_def] obtain B
    where bB: "basis B" and sum: "sum weight B < sum weight F"
    by force
  \<comment> \<open>lets us obtain two sorted lists for the bases F and B\<close>
  from bF basis_finite finite_sorted_edge_distinct
  obtain FL where dF[simp]: "distinct FL" and wF[simp]: "wsorted FL" 
    and sF[simp]: "F = set FL"
    by blast
  from bB basis_finite finite_sorted_edge_distinct
  obtain BL where dB[simp]: "distinct BL" and wB[simp]: "wsorted BL"
    and sB[simp]: "B = set BL"
      by blast
  \<comment> \<open>as basis F has more total weight than basis B (and the basis have the same length) ...\<close>
  from sum have suml: "sum_list (map weight BL) < sum_list (map weight FL)"
    by(simp add: sum.distinct_set_conv_list[symmetric]) 
  from bB bF have "card B = card F" using basis_card by blast 
  then have l: "length FL = length BL" by (simp add: distinct_card) 
  \<comment> \<open>... there exists an index i such that the ith element of the BL is strictly smaller 
      than the ith element of FL \<close>
  from exists_greater[OF l suml] obtain i where i: "i<length FL"
    and gr: "weight (BL ! i) < weight (FL ! i)"
    by auto
  let ?FL_restricted = "limi (set FL) (weight (FL ! i))"

  \<comment> \<open>now let us look at the two independent sets X and Y:
        let X and Y be the set if we take the first i-1 elements of BL
         and the first i elements of FL respectively. 
      We want to use the augment property of Matroids in order to show that we must have skipped
      and optimal element, which then contradicts our assumption. \<close>
  let ?X = "take i FL"
  have X_size: "card (set ?X) = i" using i
    by (simp add: distinct_card)
  have X_indep: "indep (set ?X)" using bF
    using indep_iff_subset_basis set_take_subset by force

  let ?Y = "take (Suc i) BL"
  have Y_size: "card (set ?Y) = Suc i" using i l
    by (simp add: distinct_card)
  have Y_indep: "indep (set ?Y)" using bB
    using indep_iff_subset_basis set_take_subset by force 

  have "card (set ?X) < card (set ?Y)" using X_size Y_size by simp

  \<comment> \<open>X and Y are independent and X is smaller than Y, thus we can augment X with some element x\<close>
  with Y_indep X_indep                                 
  obtain x where x: "x\<in>set (take (Suc i) BL) - set ?X"
    and indepX: "indep (insert x (set ?X))"
      using augment by auto

  \<comment> \<open>we know many things about x now, i.e. x weights strictly less than the ith element of FL ...\<close>
  have "x\<in>carrier"  using indepX indep_subset_carrier by blast     
  from x have xs: "x\<in>set (take (Suc i) BL)" and xnX: "x \<notin> set ?X" by auto
  from xs obtain j where "x=(take (Suc i) BL)!j" and ij: "j\<le>i"  
    by (metis i in_set_conv_nth l length_take less_Suc_eq_le min_Suc_gt(2))
  then have x: "x=BL!j" by auto
  have il: "i < length BL" using i l by simp
  have "weight x \<le> weight (BL ! i)" 
    unfolding x apply(rule wsorted_nth_mono) by fact+
  then have k: "weight x < weight (FL ! i)" using gr by auto

  \<comment> \<open>... and that adding x to X gives us an independent set\<close>
  have "?FL_restricted \<subseteq> set ?X"
    unfolding  limi_def apply safe
    by (metis (no_types, lifting) i in_set_conv_nth length_take
              min_simps(2) not_less nth_take wF wsorted_nth_mono) 
  have z': "insert x ?FL_restricted \<subseteq> insert x (set ?X)"
    using xnX \<open>?FL_restricted \<subseteq> set (take i FL)\<close> by auto 
  from indep_subset[OF indepX z'] have add_x_stay_indep: "indep (insert x ?FL_restricted)" .

  \<comment> \<open>... finally this means that we must have taken the element during our greedy algorithm\<close>
  from \<open>no_smallest_element_skipped {} F\<close>
      \<open>x\<in>carrier\<close> \<open>weight x < weight (FL ! i)\<close> add_x_stay_indep
    have "x \<in> ?FL_restricted"  by (auto dest: no_smallest_element_skippedD)
  with \<open>?FL_restricted \<subseteq> set ?X\<close> have "x \<in> set ?X"  by auto

  \<comment> \<open>... but we actually didn't. This finishes our proof by contradiction.\<close>  
  with xnX show "False" by auto              
qed


subsection "The Invariant"

text \<open>The following predicate is invariant during the execution of the 
  minimum weight basis algorithm, and implies that its result is a minimum weight basis.\<close>

definition I_minWeightBasis where
  "I_minWeightBasis == \<lambda>(T,E). indep T 
                \<and> T \<subseteq> carrier
                 \<and> E \<subseteq> carrier  
                 \<and> (\<forall>x\<in>T.\<forall>y\<in>E. weight x \<le> weight y)
                \<and> (\<forall>e\<in>carrier-E-T. ~indep (insert e T))
                 \<and> no_smallest_element_skipped E T"

lemma I_minWeightBasisD: 
  assumes 
   "I_minWeightBasis (T,E)"
 shows"indep T" "\<And>e. e\<in>carrier-E-T \<Longrightarrow> ~indep (insert e T)"
    "E \<subseteq> carrier" "\<And>x y. x\<in>T \<Longrightarrow> y\<in>E \<Longrightarrow> weight x \<le> weight y"  "T \<subseteq> carrier"
    "no_smallest_element_skipped E T"
  using assms by(auto simp: no_smallest_element_skipped_def I_minWeightBasis_def)

lemma I_minWeightBasisI:
  assumes "indep T" "\<And>e. e\<in>carrier-E-T \<Longrightarrow> ~indep (insert e T)"
    "E \<subseteq> carrier" "\<And>x y. x\<in>T \<Longrightarrow> y\<in>E \<Longrightarrow> weight x \<le> weight y"  "T \<subseteq> carrier"
    "no_smallest_element_skipped E T"
  shows "I_minWeightBasis (T,E)"
  using assms by(auto simp: no_smallest_element_skipped_def I_minWeightBasis_def)

lemma I_minWeightBasisG: "I_minWeightBasis (T,E) \<Longrightarrow> no_smallest_element_skipped E T"
  by(auto simp: I_minWeightBasis_def)

lemma I_minWeightBasis_sorted: "I_minWeightBasis (T,E) \<Longrightarrow> (\<forall>x\<in>T.\<forall>y\<in>E. weight x \<le> weight y)"
  by(auto simp: I_minWeightBasis_def)


subsection \<open>Invariant proofs\<close>

lemma I_minWeightBasis_empty: "I_minWeightBasis ({}, carrier)"
  by (auto simp: I_minWeightBasis_def)

lemma I_minWeightBasis_final: "I_minWeightBasis (T, {}) \<Longrightarrow> minBasis T"
  by(auto simp: greedy_approach_leads_to_minBasis I_minWeightBasis_def)

lemma indep_aux:       
  assumes "e \<in> E" "\<forall>e\<in>carrier - E - F. \<not> indep (insert e F)"        
    and "x\<in>carrier - (E - {e}) - insert e F"
    shows  "\<not> indep (insert x (insert e F))"
  using assms indep_iff_subset_basis by auto 

lemma preservation_if: "wsorted x \<Longrightarrow>   set x = carrier \<Longrightarrow>
    x = l1 @ xa # l2 \<Longrightarrow> I_minWeightBasis (\<sigma>, set (xa # l2))  \<Longrightarrow> indep \<sigma>
   \<Longrightarrow> xa \<in> carrier \<Longrightarrow> indep (insert xa \<sigma>) \<Longrightarrow> I_minWeightBasis (insert xa \<sigma>, set l2)"
  apply(rule I_minWeightBasisI)
  subgoal by simp      
  subgoal unfolding I_minWeightBasis_def apply(rule indep_aux[where E="set (xa # l2)"]) 
    by simp_all 
  subgoal by auto        
  subgoal by (metis insert_iff list.set(2) I_minWeightBasis_sorted
        sorted_wrt_append sorted_wrt.simps(2))  
  subgoal by(auto simp: I_minWeightBasis_def)  
  subgoal apply (rule no_smallest_element_skipped_add)
    by(auto intro!:  simp: I_minWeightBasis_def)  
  done

lemma preservation_else: "set x = carrier \<Longrightarrow>
    x = l1 @ xa # l2 \<Longrightarrow> I_minWeightBasis (\<sigma>, set (xa # l2))
     \<Longrightarrow> indep \<sigma>   \<Longrightarrow> \<not> indep (insert xa \<sigma>) \<Longrightarrow> I_minWeightBasis (\<sigma>, set l2)"
  apply(rule I_minWeightBasisI)
  subgoal by simp
  subgoal by (auto simp: DiffD2 I_minWeightBasis_def)   
  subgoal by auto 
  subgoal by(auto simp: I_minWeightBasis_def)   
  subgoal by(auto simp: I_minWeightBasis_def)  
  subgoal apply (rule no_smallest_element_skipped_skip)
    by(auto intro!:  simp: I_minWeightBasis_def)  
  done


subsection \<open>The refinement lemma\<close>

theorem minWeightBasis_refine: "(minWeightBasis, SPEC minBasis)\<in>\<langle>Id\<rangle>nres_rel"
  unfolding minWeightBasis_def obtain_sorted_carrier_def
  apply(refine_vcg nfoldli_rule[where I="\<lambda>l1 l2 s. I_minWeightBasis (s,set l2)"])
  subgoal by auto
  subgoal by (auto simp: I_minWeightBasis_empty)
      \<comment> \<open>asserts\<close>
  subgoal by (auto simp: I_minWeightBasis_def)  
  subgoal by (auto simp: I_minWeightBasis_def) 
  subgoal by (auto simp: I_minWeightBasis_def)   
      \<comment> \<open>branches\<close>
  subgoal apply(rule preservation_if) by auto
  subgoal apply(rule preservation_else) by auto  
      \<comment> \<open>final\<close>
  subgoal by auto
  subgoal by (auto simp: I_minWeightBasis_final)  
  done

end \<comment> \<open>locale minWeightBasis\<close>
  
end