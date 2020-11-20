section "Assertions"

theory Assertions
imports 
  "Tools/Imperative_HOL_Add" 
  "Tools/Syntax_Match" 
  Automatic_Refinement.Misc
begin

subsection \<open>Partial Heaps\<close>
text \<open>
  A partial heap is modeled by a heap and a set of valid addresses, with the
  side condition that the valid addresses have to be within the limit of the
  heap. This modeling is somewhat strange for separation logic, however, it 
  allows us to solve some technical problems related to definition of 
  Hoare triples, that will be detailed later.
\<close>
type_synonym pheap = "heap \<times> addr set"

text \<open>Predicate that expresses that the address set of a partial heap is 
  within the heap's limit.
\<close>
fun in_range :: "(heap \<times> addr set) \<Rightarrow> bool" 
  where "in_range (h,as) \<longleftrightarrow> (\<forall>a\<in>as. a < lim h)"

declare in_range.simps[simp del]

lemma in_range_empty[simp, intro!]: "in_range (h,{})"
  by (auto simp: in_range.simps)

lemma in_range_dist_union[simp]: 
  "in_range (h,as \<union> as') \<longleftrightarrow> in_range (h,as) \<and> in_range (h,as')"
  by (auto simp: in_range.simps)

lemma in_range_subset: 
  "\<lbrakk>as \<subseteq> as'; in_range (h,as')\<rbrakk> \<Longrightarrow> in_range (h,as)"
  by (auto simp: in_range.simps)

text \<open>Relation that holds if two heaps are identical on a given 
  address range\<close>
definition relH :: "addr set \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool" 
  where "relH as h h' \<equiv> 
  in_range (h,as) 
  \<and> in_range (h',as) 
  \<and> (\<forall>t. \<forall>a \<in> as. 
        refs h t a = refs h' t a 
      \<and> arrays h t a = arrays h' t a
    )"

lemma relH_in_rangeI:
  assumes "relH as h h'"
  shows "in_range (h,as)" and "in_range (h',as)"
  using assms unfolding relH_def by auto

text "Reflexivity"
lemma relH_refl: "in_range (h,as) \<Longrightarrow> relH as h h"
  unfolding relH_def by simp

text "Symmetry"
lemma relH_sym: "relH as h h' \<Longrightarrow> relH as h' h"
  unfolding relH_def
  by auto

text "Transitivity"
lemma relH_trans[trans]: "\<lbrakk>relH as h1 h2; relH as h2 h3\<rbrakk> \<Longrightarrow> relH as h1 h3"
  unfolding relH_def
  by auto

lemma relH_dist_union[simp]: 
  "relH (as\<union>as') h h' \<longleftrightarrow> relH as h h' \<and> relH as' h h'"
  unfolding relH_def
  by auto

lemma relH_subset:
  assumes "relH bs h h'"
  assumes "as \<subseteq> bs"
  shows "relH as h h'"
  using assms unfolding relH_def by (auto intro: in_range_subset)

lemma relH_ref:
  assumes "relH as h h'"
  assumes "addr_of_ref r \<in> as"
  shows "Ref.get h r = Ref.get h' r"
  using assms unfolding relH_def Ref.get_def by auto

lemma relH_array:
  assumes "relH as h h'"
  assumes "addr_of_array r \<in> as"
  shows "Array.get h r = Array.get h' r"
  using assms unfolding relH_def Array.get_def by auto

lemma relH_set_ref: "\<lbrakk> addr_of_ref r \<notin> as; in_range (h,as)\<rbrakk> 
  \<Longrightarrow> relH as h (Ref.set r x h)"
  unfolding relH_def Ref.set_def 
  by (auto simp: in_range.simps)

lemma relH_set_array: "\<lbrakk>addr_of_array r \<notin> as; in_range (h,as)\<rbrakk> 
  \<Longrightarrow> relH as h (Array.set r x h)"
  unfolding relH_def Array.set_def 
  by (auto simp: in_range.simps)

subsection \<open>Assertions\<close>
text \<open>
  Assertions are predicates on partial heaps, that fulfill a well-formedness 
  condition called properness: They only depend on the part of the heap
  by the address set, and must be false for partial heaps that are not in range.
\<close>
type_synonym assn_raw = "pheap \<Rightarrow> bool"

definition proper :: "assn_raw \<Rightarrow> bool" where
  "proper P \<equiv> \<forall>h h' as. (P (h,as) \<longrightarrow> in_range (h,as)) 
    \<and> (P (h,as) \<and> relH as h h' \<and> in_range (h',as) \<longrightarrow> P (h',as))"

lemma properI[intro?]: 
  assumes "\<And>as h. P (h,as) \<Longrightarrow> in_range (h,as)"
  assumes "\<And>as h h'. 
    \<lbrakk>P (h,as); relH as h h'; in_range (h',as)\<rbrakk> \<Longrightarrow> P (h',as)"
  shows "proper P"
  unfolding proper_def using assms by blast

lemma properD1:
  assumes "proper P"
  assumes "P (h,as)"
  shows "in_range (h,as)"
  using assms unfolding proper_def by blast

lemma properD2:
  assumes "proper P"
  assumes "P (h,as)"
  assumes "relH as h h'"
  assumes "in_range (h',as)"
  shows "P (h',as)"
  using assms unfolding proper_def by blast

lemmas properD = properD1 properD2

lemma proper_iff:
  assumes "proper P"
  assumes "relH as h h'"
  assumes "in_range (h',as)"
  shows "P (h,as) \<longleftrightarrow> P (h',as)"
  using assms
  by (metis properD2 relH_in_rangeI(1) relH_sym) 

text \<open>We encapsulate assertions in their own type\<close>  
typedef assn = "Collect proper" 
  apply simp
  unfolding proper_def 
  by fastforce

lemmas [simp] = Rep_assn_inverse Rep_assn_inject 
lemmas [simp, intro!] = Rep_assn[unfolded mem_Collect_eq]

lemma Abs_assn_eqI[intro?]: 
  "(\<And>h. P h = Rep_assn Pr h) \<Longrightarrow> Abs_assn P = Pr"
  "(\<And>h. P h = Rep_assn Pr h) \<Longrightarrow> Pr = Abs_assn P"
  by (metis Rep_assn_inverse predicate1I xt1(5))+

abbreviation models :: "pheap \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Turnstile>" 50) 
  where "h\<Turnstile>P \<equiv> Rep_assn P h"


lemma models_in_range: "h\<Turnstile>P \<Longrightarrow> in_range h"
  apply (cases h)
  by (metis mem_Collect_eq Rep_assn properD1)
    
subsubsection \<open>Empty Partial Heap\<close>
text \<open>The empty partial heap satisfies some special properties.
  We set up a simplification that tries to rewrite it to the standard
  empty partial heap \<open>h\<^sub>\<bottom>\<close>\<close>
abbreviation h_bot ("h\<^sub>\<bottom>") where "h\<^sub>\<bottom> \<equiv> (undefined,{})"
lemma mod_h_bot_indep: "(h,{})\<Turnstile>P \<longleftrightarrow> (h',{})\<Turnstile>P"
  by (metis mem_Collect_eq Rep_assn emptyE in_range_empty 
    proper_iff relH_def)

lemma mod_h_bot_normalize[simp]: 
  "syntax_fo_nomatch undefined h \<Longrightarrow> (h,{})\<Turnstile>P \<longleftrightarrow> h\<^sub>\<bottom> \<Turnstile> P"
  using mod_h_bot_indep[where h'=undefined] by simp

text \<open>Properness, lifted to the assertion type.\<close>
lemma mod_relH: "relH as h h' \<Longrightarrow> (h,as)\<Turnstile>P \<longleftrightarrow> (h',as)\<Turnstile>P"
  by (metis mem_Collect_eq Rep_assn proper_iff relH_in_rangeI(2))
    
subsection \<open>Connectives\<close>
text \<open>
  We define several operations on assertions, and instantiate some type classes.
\<close>

subsubsection \<open>Empty Heap and Separation Conjunction\<close>
text \<open>The assertion that describes the empty heap, and the separation
  conjunction form a commutative monoid:\<close>
instantiation assn :: one begin
  fun one_assn_raw :: "pheap \<Rightarrow> bool" 
    where "one_assn_raw (h,as) \<longleftrightarrow> as={}"
  
  lemma one_assn_proper[intro!,simp]: "proper one_assn_raw"
    by (auto intro!: properI)
  
  definition one_assn :: assn where "1 \<equiv> Abs_assn one_assn_raw"
  instance ..
end

abbreviation one_assn::assn ("emp") where "one_assn \<equiv> 1"
  
instantiation assn :: times begin
  fun times_assn_raw :: "assn_raw \<Rightarrow> assn_raw \<Rightarrow> assn_raw" where
    "times_assn_raw P Q (h,as) 
    = (\<exists>as1 as2. as=as1\<union>as2 \<and> as1\<inter>as2={} 
        \<and> P (h,as1) \<and> Q (h,as2))"

  lemma times_assn_proper[intro!,simp]: 
    "proper P \<Longrightarrow> proper Q \<Longrightarrow> proper (times_assn_raw P Q)"
    apply (rule properI)
    apply (auto dest: properD1) []
    apply clarsimp
    apply (drule (3) properD2)
    apply (drule (3) properD2)
    apply blast
    done

  definition times_assn where "P*Q \<equiv> 
    Abs_assn (times_assn_raw (Rep_assn P) (Rep_assn Q))"

  instance ..
end

lemma mod_star_conv: "h\<Turnstile>A*B 
  \<longleftrightarrow> (\<exists>hr as1 as2. h=(hr,as1\<union>as2) \<and> as1\<inter>as2={} \<and> (hr,as1)\<Turnstile>A \<and> (hr,as2)\<Turnstile>B)"
  unfolding times_assn_def
  apply (cases h)
  by (auto simp: Abs_assn_inverse)

lemma mod_starD: "h\<Turnstile>A*B \<Longrightarrow> \<exists>h1 h2. h1\<Turnstile>A \<and> h2\<Turnstile>B"
  by (auto simp: mod_star_conv)

lemma star_assnI:
  assumes "(h,as)\<Turnstile>P" and "(h,as')\<Turnstile>Q" and "as\<inter>as'={}"
  shows "(h,as\<union>as')\<Turnstile>P*Q"
  using assms unfolding times_assn_def
  by (auto simp: Abs_assn_inverse)
 
instantiation assn :: comm_monoid_mult begin
  lemma assn_one_left: "1*P = (P::assn)"
    unfolding one_assn_def times_assn_def
    apply (rule)
    apply (auto simp: Abs_assn_inverse)
    done

  lemma assn_times_comm: "P*Q = Q*(P::assn)"
    unfolding times_assn_def
    apply rule
    apply (fastforce simp add: Abs_assn_inverse Un_ac)
    done

  lemma assn_times_assoc: "(P*Q)*R = P*(Q*(R::assn))"
    unfolding times_assn_def
    apply rule
    apply (auto simp: Abs_assn_inverse)
    apply (rule_tac x="as1\<union>as1a" in exI)
    apply (rule_tac x="as2a" in exI)
    apply (auto simp add: Un_ac) []

    apply (rule_tac x="as1a" in exI)
    apply (rule_tac x="as2a\<union>as2" in exI)
    apply (fastforce simp add: Un_ac) []
    done

  instance 
    apply standard
    apply (rule assn_times_assoc)
    apply (rule assn_times_comm)
    apply (rule assn_one_left)
    done

end
  
subsubsection \<open>Magic Wand\<close>
fun wand_raw :: "assn_raw \<Rightarrow> assn_raw \<Rightarrow> assn_raw" where
  "wand_raw P Q (h,as) \<longleftrightarrow> in_range (h,as) 
  \<and> (\<forall>h' as'. as\<inter>as'={} \<and> relH as h h' \<and> in_range (h',as)
    \<and> P (h',as')
    \<longrightarrow> Q (h',as\<union>as'))"

lemma wand_proper[simp, intro!]: "proper (wand_raw P Q)"
  apply (rule properI)
  apply simp
  apply (auto dest: relH_trans)
  done

definition 
  wand_assn :: "assn \<Rightarrow> assn \<Rightarrow> assn" (infixl "-*" 56)
  where "P-*Q \<equiv> Abs_assn (wand_raw (Rep_assn P) (Rep_assn Q))"

lemma wand_assnI: 
  assumes "in_range (h,as)"
  assumes "\<And>h' as'. \<lbrakk>
    as \<inter> as' = {}; 
    relH as h h'; 
    in_range (h',as); 
    (h',as')\<Turnstile>Q 
  \<rbrakk> \<Longrightarrow> (h',as\<union>as') \<Turnstile> R"
  shows "(h,as) \<Turnstile> Q -* R"
  using assms 
  unfolding wand_assn_def
  apply (auto simp: Abs_assn_inverse)
  done

subsubsection \<open>Boolean Algebra on Assertions\<close>
instantiation assn :: boolean_algebra begin
  definition top_assn where "top \<equiv> Abs_assn in_range"
  definition bot_assn where "bot \<equiv> Abs_assn (\<lambda>_. False)"
  definition sup_assn where "sup P Q \<equiv> Abs_assn (\<lambda>h. h\<Turnstile>P \<or> h\<Turnstile>Q)"
  definition inf_assn where "inf P Q \<equiv> Abs_assn (\<lambda>h. h\<Turnstile>P \<and> h\<Turnstile>Q)"
  definition uminus_assn where 
    "-P \<equiv> Abs_assn (\<lambda>h. in_range h \<and> \<not>h\<Turnstile>P)"

  lemma bool_assn_proper[simp, intro!]:
    "proper in_range"
    "proper (\<lambda>_. False)"
    "proper P \<Longrightarrow> proper Q \<Longrightarrow> proper (\<lambda>h. P h \<or> Q h)"
    "proper P \<Longrightarrow> proper Q \<Longrightarrow> proper (\<lambda>h. P h \<and> Q h)"
    "proper P \<Longrightarrow> proper (\<lambda>h. in_range h \<and> \<not>P h)"
    apply (auto 
      intro!: properI 
      intro: relH_in_rangeI 
      dest: properD1 
      simp: proper_iff)
    done

  text \<open>(And, Or, True, False, Not) are a Boolean algebra. 
    Due to idiosyncrasies of the Isabelle/HOL class setup, we have to
    also define a difference and an ordering:\<close>
  definition less_eq_assn where
  [simp]: "(a::assn) \<le> b \<equiv> a = inf a b"

  definition less_assn where
  [simp]: "(a::assn) < b \<equiv> a \<le> b \<and> a\<noteq>b"

  definition minus_assn where
  [simp]: "(a::assn) - b \<equiv> inf a (-b)"

  instance
    apply standard
    unfolding 
      top_assn_def bot_assn_def sup_assn_def inf_assn_def uminus_assn_def
      less_eq_assn_def less_assn_def minus_assn_def
    apply (auto 
      simp: Abs_assn_inverse conj_commute conj_ac 
      intro: Abs_assn_eqI models_in_range)
    apply rule
    apply (metis (mono_tags) Abs_assn_inverse[unfolded mem_Collect_eq]
      Rep_assn[unfolded mem_Collect_eq] bool_assn_proper(4))
    apply rule
    apply (metis (mono_tags)
      Abs_assn_inverse[unfolded mem_Collect_eq]
      Rep_assn[unfolded mem_Collect_eq] bool_assn_proper(4))
    apply rule
    apply (simp add: Abs_assn_inverse)
    apply (metis (mono_tags) 
      Abs_assn_inverse[unfolded mem_Collect_eq] 
      Rep_assn[unfolded mem_Collect_eq] bool_assn_proper(4))
    done

end

text \<open>We give the operations some more standard names\<close>
abbreviation top_assn::assn ("true") where "top_assn \<equiv> top"
abbreviation bot_assn::assn ("false") where "bot_assn \<equiv> bot"
abbreviation sup_assn::"assn\<Rightarrow>assn\<Rightarrow>assn" (infixr "\<or>\<^sub>A" 61) 
  where "sup_assn \<equiv> sup"
abbreviation inf_assn::"assn\<Rightarrow>assn\<Rightarrow>assn" (infixr "\<and>\<^sub>A" 62) 
  where "inf_assn \<equiv> inf"
abbreviation uminus_assn::"assn \<Rightarrow> assn" ("\<not>\<^sub>A _" [81] 80) 
  where "uminus_assn \<equiv> uminus"

text \<open>Now we prove some relations between the Boolean algebra operations
  and the (empty heap,separation conjunction) monoid\<close>

lemma star_false_left[simp]: "false * P = false"
  unfolding times_assn_def bot_assn_def
  apply rule
  apply (auto simp add: Abs_assn_inverse)
  done

lemma star_false_right[simp]: "P * false = false"
  using star_false_left by (simp add: assn_times_comm)

lemmas star_false = star_false_left star_false_right 
  
lemma assn_basic_inequalities[simp, intro!]:
  "true \<noteq> emp" "emp \<noteq> true"
  "false \<noteq> emp" "emp \<noteq> false"
  "true \<noteq> false" "false \<noteq> true"
  subgoal 
    unfolding one_assn_def top_assn_def
    proof (subst Abs_assn_inject; simp?) 
      have "in_range (\<lparr>arrays = (\<lambda>_ _. []), refs = (\<lambda>_ _. 0), lim = 1\<rparr>,{0})" (is "in_range ?h")
        by (auto simp: in_range.simps)
      moreover have "\<not>one_assn_raw ?h" by auto
      ultimately show "in_range \<noteq> one_assn_raw" by auto
    qed      
  subgoal
    by (simp add: \<open>true \<noteq> emp\<close>)
  subgoal
  using star_false_left \<open>true \<noteq> emp\<close> by force
  subgoal
    by (simp add: \<open>false \<noteq> emp\<close>)
  subgoal
    by (metis inf_bot_right inf_top.right_neutral \<open>true \<noteq> emp\<close>)
  subgoal
    using \<open>true \<noteq> false\<close> by auto
  done
  
  
subsubsection \<open>Existential Quantification\<close>
definition ex_assn :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "\<exists>\<^sub>A" 11)
  where "(\<exists>\<^sub>Ax. P x) \<equiv> Abs_assn (\<lambda>h. \<exists>x. h\<Turnstile>P x)"

lemma ex_assn_proper[simp, intro!]: 
  "(\<And>x. proper (P x)) \<Longrightarrow> proper (\<lambda>h. \<exists>x. P x h)"
  by (auto intro!: properI dest: properD1 simp: proper_iff)

lemma ex_assn_const[simp]: "(\<exists>\<^sub>Ax. c) = c" 
  unfolding ex_assn_def by auto

lemma ex_one_point_gen: 
  "\<lbrakk>\<And>h x. h\<Turnstile>P x \<Longrightarrow> x=v\<rbrakk> \<Longrightarrow> (\<exists>\<^sub>Ax. P x) = (P v)"
  unfolding ex_assn_def
  apply rule
  apply auto
  done

lemma ex_distrib_star: "(\<exists>\<^sub>Ax. P x * Q) = (\<exists>\<^sub>Ax. P x) * Q"
  unfolding ex_assn_def times_assn_def
  apply rule
  apply (simp add: Abs_assn_inverse)
  apply fastforce
  done

lemma ex_distrib_and: "(\<exists>\<^sub>Ax. P x \<and>\<^sub>A Q) = (\<exists>\<^sub>Ax. P x) \<and>\<^sub>A Q"
  unfolding ex_assn_def inf_assn_def
  apply rule
  apply (simp add: Abs_assn_inverse)
  done

lemma ex_distrib_or: "(\<exists>\<^sub>Ax. P x \<or>\<^sub>A Q) = (\<exists>\<^sub>Ax. P x) \<or>\<^sub>A Q"
  unfolding ex_assn_def sup_assn_def
  apply rule
  apply (auto simp add: Abs_assn_inverse)
  done

lemma ex_join_or: "(\<exists>\<^sub>Ax. P x \<or>\<^sub>A (\<exists>\<^sub>Ax. Q x)) = (\<exists>\<^sub>Ax. P x \<or>\<^sub>A Q x)"
  unfolding ex_assn_def sup_assn_def
  apply rule
  apply (auto simp add: Abs_assn_inverse)
  done

subsubsection \<open>Pure Assertions\<close>
text \<open>Pure assertions do not depend on any heap content.\<close>
fun pure_assn_raw where "pure_assn_raw b (h,as) \<longleftrightarrow> as={} \<and> b"
definition pure_assn :: "bool \<Rightarrow> assn" ("\<up>") where
  "\<up>b \<equiv> Abs_assn (pure_assn_raw b)"

lemma pure_assn_proper[simp, intro!]: "proper (pure_assn_raw b)"
  by (auto intro!: properI intro: relH_in_rangeI)


    
lemma pure_true[simp]: "\<up>True = emp"
  unfolding pure_assn_def one_assn_def 
  apply rule
  apply (simp add: Abs_assn_inverse)
  apply (auto)
  done

lemma pure_false[simp]: "\<up>False = false"
  unfolding pure_assn_def bot_assn_def 
  apply rule
  apply (auto simp: Abs_assn_inverse)
  done

lemma pure_assn_eq_false_iff[simp]: "\<up>P = false \<longleftrightarrow> \<not>P" by auto
  
lemma pure_assn_eq_emp_iff[simp]: "\<up>P = emp \<longleftrightarrow> P" by (cases P) auto
    
lemma merge_pure_star[simp]: 
  "\<up>a * \<up>b = \<up>(a\<and>b)"
  unfolding times_assn_def
  apply rule
  unfolding pure_assn_def
  apply (simp add: Abs_assn_inverse)
  apply fastforce
  done

lemma merge_true_star[simp]: "true*true = true"
  unfolding times_assn_def top_assn_def
  apply rule
  apply (simp add: Abs_assn_inverse)
  apply (fastforce simp: in_range.simps)
  done

lemma merge_pure_and[simp]:
  "\<up>a \<and>\<^sub>A \<up>b = \<up>(a\<and>b)"
  unfolding inf_assn_def
  apply rule
  unfolding pure_assn_def
  apply (simp add: Abs_assn_inverse)
  apply fastforce
  done

lemma merge_pure_or[simp]:
  "\<up>a \<or>\<^sub>A \<up>b = \<up>(a\<or>b)"
  unfolding sup_assn_def
  apply rule
  unfolding pure_assn_def
  apply (simp add: Abs_assn_inverse)
  apply fastforce
  done

    
lemma pure_assn_eq_conv[simp]: "\<up>P = \<up>Q \<longleftrightarrow> P=Q" by auto
    
definition "is_pure_assn a \<equiv> \<exists>P. a=\<up>P"
lemma is_pure_assnE: assumes "is_pure_assn a" obtains P where "a=\<up>P"
  using assms
  by (auto simp: is_pure_assn_def)

lemma is_pure_assn_pure[simp, intro!]: "is_pure_assn (\<up>P)" 
  by (auto simp add: is_pure_assn_def)

lemma is_pure_assn_basic_simps[simp]:
  "is_pure_assn false"
  "is_pure_assn emp"
proof -
  have "is_pure_assn (\<up>False)" by rule thus "is_pure_assn false" by simp
  have "is_pure_assn (\<up>True)" by rule thus "is_pure_assn emp" by simp
qed  

lemma is_pure_assn_starI[simp,intro!]: 
  "\<lbrakk>is_pure_assn a; is_pure_assn b\<rbrakk> \<Longrightarrow> is_pure_assn (a*b)"
  by (auto elim!: is_pure_assnE)
    
    
    
    
subsubsection \<open>Pointers\<close>
text \<open>In Imperative HOL, we have to distinguish between pointers to single
  values and pointers to arrays. For both, we define assertions that 
  describe the part of the heap that a pointer points to.\<close>
fun sngr_assn_raw :: "'a::heap ref \<Rightarrow> 'a \<Rightarrow> assn_raw" where
  "sngr_assn_raw r x (h,as) \<longleftrightarrow> Ref.get h r = x \<and> as = {addr_of_ref r} \<and> 
  addr_of_ref r < lim h"

lemma sngr_assn_proper[simp, intro!]: "proper (sngr_assn_raw r x)"
  apply (auto intro!: properI simp: relH_ref)
  apply (simp add: in_range.simps)
  apply (auto simp add: in_range.simps dest: relH_in_rangeI)
  done

definition sngr_assn :: "'a::heap ref \<Rightarrow> 'a \<Rightarrow> assn" (infix "\<mapsto>\<^sub>r" 82) 
  where "r\<mapsto>\<^sub>rx \<equiv> Abs_assn (sngr_assn_raw r x)"

fun snga_assn_raw :: "'a::heap array \<Rightarrow> 'a list \<Rightarrow> assn_raw" 
  where "snga_assn_raw r x (h,as) 
  \<longleftrightarrow> Array.get h r = x \<and> as = {addr_of_array r} 
      \<and> addr_of_array r < lim h"

lemma snga_assn_proper[simp, intro!]: "proper (snga_assn_raw r x)"
  apply (auto intro!: properI simp: relH_array)
  apply (simp add: in_range.simps)
  apply (auto simp add: in_range.simps dest: relH_in_rangeI)
  done

definition 
  snga_assn :: "'a::heap array \<Rightarrow> 'a list \<Rightarrow> assn" (infix "\<mapsto>\<^sub>a" 82)
  where "r\<mapsto>\<^sub>aa \<equiv> Abs_assn (snga_assn_raw r a)"

text \<open>Two disjoint parts of the heap cannot be pointed to by the 
  same pointer\<close>
lemma sngr_same_false[simp]: 
  "p \<mapsto>\<^sub>r x * p \<mapsto>\<^sub>r y = false"
  unfolding times_assn_def bot_assn_def sngr_assn_def
  apply rule
  apply (auto simp: Abs_assn_inverse)
  done

lemma snga_same_false[simp]: 
  "p \<mapsto>\<^sub>a x * p \<mapsto>\<^sub>a y = false"
  unfolding times_assn_def bot_assn_def snga_assn_def
  apply rule
  apply (auto simp: Abs_assn_inverse)
  done

subsection \<open>Properties of the Models-Predicate\<close>
lemma mod_true[simp]: "h\<Turnstile>true \<longleftrightarrow> in_range h"
  unfolding top_assn_def by (simp add: Abs_assn_inverse)
lemma mod_false[simp]: "\<not> h\<Turnstile>false"
  unfolding bot_assn_def by (simp add: Abs_assn_inverse)

lemma mod_emp: "h\<Turnstile>emp \<longleftrightarrow> snd h = {}"
  unfolding one_assn_def by (cases h) (simp add: Abs_assn_inverse)
  
lemma mod_emp_simp[simp]: "(h,{})\<Turnstile>emp"
  by (simp add: mod_emp)

lemma mod_pure[simp]: "h\<Turnstile>\<up>b \<longleftrightarrow> snd h = {} \<and> b"
  unfolding pure_assn_def 
  apply (cases h) 
  apply (auto simp add: Abs_assn_inverse)
  done

lemma mod_ex_dist[simp]: "h\<Turnstile>(\<exists>\<^sub>Ax. P x) \<longleftrightarrow> (\<exists>x. h\<Turnstile>P x)"
  unfolding ex_assn_def by (auto simp: Abs_assn_inverse)
  
lemma mod_exI: "\<exists>x. h\<Turnstile>P x \<Longrightarrow> h\<Turnstile>(\<exists>\<^sub>Ax. P x)"
  by (auto simp: mod_ex_dist)
lemma mod_exE: assumes "h\<Turnstile>(\<exists>\<^sub>Ax. P x)" obtains x where "h\<Turnstile>P x"
  using assms by (auto simp: mod_ex_dist)

(* Not declared as simp, to not interfere with precision.
  TODO: Perhaps define own connector for precision claims?
*)
lemma mod_and_dist: "h\<Turnstile>P\<and>\<^sub>AQ \<longleftrightarrow> h\<Turnstile>P \<and> h\<Turnstile>Q"
  unfolding inf_assn_def by (simp add: Abs_assn_inverse)

lemma mod_or_dist[simp]: "h\<Turnstile>P\<or>\<^sub>AQ \<longleftrightarrow> h\<Turnstile>P \<or> h\<Turnstile>Q"
  unfolding sup_assn_def by (simp add: Abs_assn_inverse)

lemma mod_not_dist[simp]: "h\<Turnstile>(\<not>\<^sub>AP) \<longleftrightarrow> in_range h \<and> \<not> h\<Turnstile>P"
  unfolding uminus_assn_def by (simp add: Abs_assn_inverse)

lemma mod_pure_star_dist[simp]: "h\<Turnstile>P*\<up>b \<longleftrightarrow> h\<Turnstile>P \<and> b"
  by (metis (full_types) mod_false mult_1_right pure_false 
    pure_true star_false_right)

lemmas mod_dist = mod_pure mod_pure_star_dist mod_ex_dist mod_and_dist
  mod_or_dist mod_not_dist

lemma mod_star_trueI: "h\<Turnstile>P \<Longrightarrow> h\<Turnstile>P*true"
  unfolding times_assn_def top_assn_def
  apply (simp add: Abs_assn_inverse)
  apply (cases h)
  apply auto
  done

lemma mod_star_trueE': assumes "h\<Turnstile>P*true" obtains h' where 
  "fst h' = fst h" and "snd h' \<subseteq> snd h" and "h'\<Turnstile>P"
  using assms
  unfolding times_assn_def top_assn_def
  apply (cases h)
  apply (fastforce simp add: Abs_assn_inverse)
  done

lemma mod_star_trueE: assumes "h\<Turnstile>P*true" obtains h' where "h'\<Turnstile>P"
  using assms by (blast elim: mod_star_trueE')

lemma mod_h_bot_iff[simp]:
  "(h,{}) \<Turnstile> \<up>b \<longleftrightarrow> b"
  "(h,{}) \<Turnstile> true"
  "(h,{}) \<Turnstile> p\<mapsto>\<^sub>rx \<longleftrightarrow> False"
  "(h,{}) \<Turnstile> q\<mapsto>\<^sub>ay \<longleftrightarrow> False"
  "(h,{}) \<Turnstile> P*Q \<longleftrightarrow> ((h,{}) \<Turnstile> P) \<and> ((h,{}) \<Turnstile> Q)"
  "(h,{}) \<Turnstile> P\<and>\<^sub>AQ \<longleftrightarrow> ((h,{}) \<Turnstile> P) \<and> ((h,{}) \<Turnstile> Q)"
  "(h,{}) \<Turnstile> P\<or>\<^sub>AQ \<longleftrightarrow> ((h,{}) \<Turnstile> P) \<or> ((h,{}) \<Turnstile> Q)"
  "(h,{}) \<Turnstile> (\<exists>\<^sub>Ax. R x) \<longleftrightarrow> (\<exists>x. (h,{}) \<Turnstile> R x)"
  apply (simp add: pure_assn_def Abs_assn_inverse)
  apply simp
  apply (simp add: sngr_assn_def Abs_assn_inverse)
  apply (simp add: snga_assn_def Abs_assn_inverse)
  apply (simp add: times_assn_def Abs_assn_inverse)
  apply (simp add: inf_assn_def Abs_assn_inverse)
  apply (simp add: sup_assn_def Abs_assn_inverse)
  apply (simp add: ex_assn_def Abs_assn_inverse)
  done

subsection \<open>Entailment\<close>
definition entails :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Longrightarrow>\<^sub>A" 10)
  where "P \<Longrightarrow>\<^sub>A Q \<equiv> \<forall>h. h\<Turnstile>P \<longrightarrow> h\<Turnstile>Q"

lemma entailsI: 
  assumes "\<And>h. h\<Turnstile>P \<Longrightarrow> h\<Turnstile>Q"
  shows "P \<Longrightarrow>\<^sub>A Q" 
  using assms unfolding entails_def by auto

lemma entailsD: 
  assumes "P \<Longrightarrow>\<^sub>A Q"
  assumes "h\<Turnstile>P"
  shows "h\<Turnstile>Q" 
  using assms unfolding entails_def by blast

subsubsection \<open>Properties\<close>
lemma ent_fwd: 
  assumes "h\<Turnstile>P"
  assumes "P \<Longrightarrow>\<^sub>A Q"
  shows "h\<Turnstile>Q" using assms(2,1) by (rule entailsD)

lemma ent_refl[simp]: "P \<Longrightarrow>\<^sub>A P"
  by (auto simp: entailsI)

lemma ent_trans[trans]: "\<lbrakk> P \<Longrightarrow>\<^sub>A Q; Q \<Longrightarrow>\<^sub>AR \<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>A R"
  by (auto intro: entailsI dest: entailsD)

lemma ent_iffI:
  assumes "A\<Longrightarrow>\<^sub>AB"
  assumes "B\<Longrightarrow>\<^sub>AA"
  shows "A=B"
  apply (subst Rep_assn_inject[symmetric])
  apply (rule ext)
  using assms unfolding entails_def
  by blast

lemma ent_false[simp]: "false \<Longrightarrow>\<^sub>A P"
  by (auto intro: entailsI)
lemma ent_true[simp]: "P \<Longrightarrow>\<^sub>A true"
  by (auto intro!: entailsI simp: models_in_range)

lemma ent_false_iff[simp]: "(P \<Longrightarrow>\<^sub>A false) \<longleftrightarrow> (\<forall>h. \<not>h\<Turnstile>P)"
  unfolding entails_def
  by auto

lemma ent_pure_pre_iff[simp]: "(P*\<up>b \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (b \<longrightarrow> (P \<Longrightarrow>\<^sub>A Q))"
  unfolding entails_def
  by (auto simp add: mod_dist)

lemma ent_pure_pre_iff_sng[simp]: 
  "(\<up>b \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (b \<longrightarrow> (emp \<Longrightarrow>\<^sub>A Q))"
  using ent_pure_pre_iff[where P=emp]
  by simp

lemma ent_pure_post_iff[simp]: 
  "(P \<Longrightarrow>\<^sub>A Q*\<up>b) \<longleftrightarrow> ((\<forall>h. h\<Turnstile>P \<longrightarrow> b) \<and> (P \<Longrightarrow>\<^sub>A Q))"
  unfolding entails_def
  by (auto simp add: mod_dist)

lemma ent_pure_post_iff_sng[simp]: 
  "(P \<Longrightarrow>\<^sub>A \<up>b) \<longleftrightarrow> ((\<forall>h. h\<Turnstile>P \<longrightarrow> b) \<and> (P \<Longrightarrow>\<^sub>A emp))"
  using ent_pure_post_iff[where Q=emp]
  by simp

lemma ent_ex_preI: "(\<And>x. P x \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> \<exists>\<^sub>Ax. P x \<Longrightarrow>\<^sub>A Q"
  unfolding entails_def ex_assn_def
  by (auto simp: Abs_assn_inverse)

lemma ent_ex_postI: "(P \<Longrightarrow>\<^sub>A Q x) \<Longrightarrow> P \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. Q x"
  unfolding entails_def ex_assn_def
  by (auto simp: Abs_assn_inverse)

lemma ent_mp: "(P * (P -* Q)) \<Longrightarrow>\<^sub>A Q"
  apply (rule entailsI)
  unfolding times_assn_def wand_assn_def
  apply (clarsimp simp add: Abs_assn_inverse)
  apply (drule_tac x="a" in spec)
  apply (drule_tac x="as1" in spec)
  apply (auto simp: Un_ac relH_refl)
  done

lemma ent_star_mono: "\<lbrakk> P \<Longrightarrow>\<^sub>A P'; Q \<Longrightarrow>\<^sub>A Q'\<rbrakk> \<Longrightarrow> P*Q \<Longrightarrow>\<^sub>A P'*Q'"
  unfolding entails_def times_assn_def
  apply (simp add: Abs_assn_inverse)
  apply metis
  done

lemma ent_wandI:
  assumes IMP: "Q*P \<Longrightarrow>\<^sub>A R"
  shows "P \<Longrightarrow>\<^sub>A (Q -* R)"
  unfolding entails_def 
  apply clarsimp
  apply (rule wand_assnI)
  apply (blast intro: models_in_range)
proof -
  fix h as h' as'
  assume "(h,as)\<Turnstile>P" 
    and "as\<inter>as'={}" 
    and "relH as h h'" 
    and "in_range (h',as)" 
    and "(h',as') \<Turnstile> Q"

  from \<open>(h,as)\<Turnstile>P\<close> and \<open>relH as h h'\<close> have "(h',as)\<Turnstile>P" 
    by (simp add: mod_relH)
  with \<open>(h',as') \<Turnstile> Q\<close> and \<open>as\<inter>as'={}\<close> have "(h',as\<union>as')\<Turnstile>Q*P" 
    by (metis star_assnI Int_commute Un_commute)
  with IMP show "(h',as\<union>as') \<Turnstile> R" by (blast dest: ent_fwd)
qed

lemma ent_disjI1:
  assumes "P \<or>\<^sub>A Q \<Longrightarrow>\<^sub>A R" 
  shows "P \<Longrightarrow>\<^sub>A R" using assms unfolding entails_def by simp

lemma ent_disjI2:
  assumes "P \<or>\<^sub>A Q \<Longrightarrow>\<^sub>A R" 
  shows "Q \<Longrightarrow>\<^sub>A R" using assms unfolding entails_def by simp

lemma ent_disjI1_direct[simp]: "A \<Longrightarrow>\<^sub>A A \<or>\<^sub>A B"
  by (simp add: entails_def)

lemma ent_disjI2_direct[simp]: "B \<Longrightarrow>\<^sub>A A \<or>\<^sub>A B"
  by (simp add: entails_def)
    
lemma ent_disjE: "\<lbrakk> A\<Longrightarrow>\<^sub>AC; B\<Longrightarrow>\<^sub>AC \<rbrakk> \<Longrightarrow> A\<or>\<^sub>AB \<Longrightarrow>\<^sub>AC"
  unfolding entails_def by auto

lemma ent_conjI: "\<lbrakk> A\<Longrightarrow>\<^sub>AB; A\<Longrightarrow>\<^sub>AC \<rbrakk> \<Longrightarrow> A \<Longrightarrow>\<^sub>A B \<and>\<^sub>A C"  
  unfolding entails_def by (auto simp: mod_and_dist)

lemma ent_conjE1: "\<lbrakk>A\<Longrightarrow>\<^sub>AC\<rbrakk> \<Longrightarrow> A\<and>\<^sub>AB\<Longrightarrow>\<^sub>AC"
  unfolding entails_def by (auto simp: mod_and_dist)
lemma ent_conjE2: "\<lbrakk>B\<Longrightarrow>\<^sub>AC\<rbrakk> \<Longrightarrow> A\<and>\<^sub>AB\<Longrightarrow>\<^sub>AC"
  unfolding entails_def by (auto simp: mod_and_dist)



lemma star_or_dist1: 
  "(A \<or>\<^sub>A B)*C = (A*C \<or>\<^sub>A B*C)"  
  apply (rule ent_iffI) 
  unfolding entails_def
  by (auto simp add: mod_star_conv) 
  
lemma star_or_dist2: 
  "C*(A \<or>\<^sub>A B) = (C*A \<or>\<^sub>A C*B)"  
  apply (rule ent_iffI) 
  unfolding entails_def
  by (auto simp add: mod_star_conv) 

lemmas star_or_dist = star_or_dist1 star_or_dist2  
    
lemma ent_disjI1': "A\<Longrightarrow>\<^sub>AB \<Longrightarrow> A\<Longrightarrow>\<^sub>AB\<or>\<^sub>AC"
  by (auto simp: entails_def star_or_dist)

lemma ent_disjI2': "A\<Longrightarrow>\<^sub>AC \<Longrightarrow> A\<Longrightarrow>\<^sub>AB\<or>\<^sub>AC"
  by (auto simp: entails_def star_or_dist)

lemma triv_exI[simp, intro!]: "Q x \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. Q x"
  by (meson ent_ex_postI ent_refl)
    
subsubsection \<open>Weak Entails\<close>    
text \<open>Weakening of entails to allow arbitrary unspecified memory in conclusion\<close>
definition entailst :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Longrightarrow>\<^sub>t" 10)
  where "entailst A B \<equiv> A \<Longrightarrow>\<^sub>A B * true"

lemma enttI: "A\<Longrightarrow>\<^sub>AB*true \<Longrightarrow> A\<Longrightarrow>\<^sub>tB" unfolding entailst_def .
lemma enttD: "A\<Longrightarrow>\<^sub>tB \<Longrightarrow> A\<Longrightarrow>\<^sub>AB*true" unfolding entailst_def .
    
lemma entt_trans:
  "entailst A B \<Longrightarrow> entailst B C \<Longrightarrow> entailst A C"
  unfolding entailst_def
  apply (erule ent_trans)
  by (metis assn_times_assoc ent_star_mono ent_true merge_true_star)  

lemma entt_refl[simp, intro!]: "entailst A A"
  unfolding entailst_def
  by (simp add: entailsI mod_star_trueI)

lemma entt_true[simp, intro!]:
  "entailst A true"
  unfolding entailst_def by simp

lemma entt_emp[simp, intro!]:
  "entailst A emp"
  unfolding entailst_def by simp

lemma entt_star_true_simp[simp]:
  "entailst A (B*true) \<longleftrightarrow> entailst A B"
  "entailst (A*true) B \<longleftrightarrow> entailst A B"
  unfolding entailst_def 
  subgoal by (auto simp: assn_times_assoc)
  subgoal
    apply (intro iffI)
    subgoal using entails_def mod_star_trueI by blast  
    subgoal by (metis assn_times_assoc ent_refl ent_star_mono merge_true_star)  
    done
  done

lemma entt_star_mono: "\<lbrakk>entailst A B; entailst C D\<rbrakk> \<Longrightarrow> entailst (A*C) (B*D)"
  unfolding entailst_def
proof -
  assume a1: "A \<Longrightarrow>\<^sub>A B * true"
  assume "C \<Longrightarrow>\<^sub>A D * true"
  then have "A * C \<Longrightarrow>\<^sub>A true * B * (true * D)"
    using a1 assn_times_comm ent_star_mono by force
  then show "A * C \<Longrightarrow>\<^sub>A B * D * true"
    by (simp add: ab_semigroup_mult_class.mult.left_commute assn_times_comm)
qed  
    
lemma entt_frame_fwd:
  assumes "entailst P Q"
  assumes "entailst A (P*F)"
  assumes "entailst (Q*F) B"
  shows "entailst A B"
  using assms
  by (metis entt_refl entt_star_mono entt_trans)

lemma enttI_true: "P*true \<Longrightarrow>\<^sub>A Q*true \<Longrightarrow> P\<Longrightarrow>\<^sub>tQ"
  by (drule enttI) simp

lemma entt_def_true: "(P\<Longrightarrow>\<^sub>tQ) \<equiv> (P*true \<Longrightarrow>\<^sub>A Q*true)"
  unfolding entailst_def
  apply (rule eq_reflection)
  using entailst_def entt_star_true_simp(2) by auto  

lemma ent_imp_entt: "P\<Longrightarrow>\<^sub>AQ \<Longrightarrow> P\<Longrightarrow>\<^sub>tQ" 
  apply (rule enttI)
  apply (erule ent_trans)
  by (simp add: entailsI mod_star_trueI)  

lemma entt_disjI1_direct[simp]: "A \<Longrightarrow>\<^sub>t A \<or>\<^sub>A B"
  by (rule ent_imp_entt[OF ent_disjI1_direct])

lemma entt_disjI2_direct[simp]: "B \<Longrightarrow>\<^sub>t A \<or>\<^sub>A B"
  by (rule ent_imp_entt[OF ent_disjI2_direct])

lemma entt_disjI1': "A\<Longrightarrow>\<^sub>tB \<Longrightarrow> A\<Longrightarrow>\<^sub>tB\<or>\<^sub>AC"
  by (auto simp: entailst_def entails_def star_or_dist)

lemma entt_disjI2': "A\<Longrightarrow>\<^sub>tC \<Longrightarrow> A\<Longrightarrow>\<^sub>tB\<or>\<^sub>AC"
  by (auto simp: entailst_def entails_def star_or_dist)

lemma entt_disjE: "\<lbrakk> A\<Longrightarrow>\<^sub>tM; B\<Longrightarrow>\<^sub>tM \<rbrakk> \<Longrightarrow> A\<or>\<^sub>AB \<Longrightarrow>\<^sub>t M"
  using ent_disjE enttD enttI by blast  
    
lemma entt_disjD1: "A\<or>\<^sub>AB\<Longrightarrow>\<^sub>tC \<Longrightarrow> A\<Longrightarrow>\<^sub>tC"
  using entt_disjI1_direct entt_trans by blast

lemma entt_disjD2: "A\<or>\<^sub>AB\<Longrightarrow>\<^sub>tC \<Longrightarrow> B\<Longrightarrow>\<^sub>tC"
  using entt_disjI2_direct entt_trans by blast
    
    
subsection \<open>Precision\<close>
text \<open>
  Precision rules describe that parts of an assertion may depend only on the
  underlying heap. For example, the data where a pointer points to is the same
  for the same heap.
\<close>
text \<open>Precision rules should have the form: 
  @{text [display] "\<forall>x y. (h\<Turnstile>(P x * F1) \<and>\<^sub>A (P y * F2)) \<longrightarrow> x=y"}\<close>
definition "precise R \<equiv> \<forall>a a' h p F F'. 
  h \<Turnstile> R a p * F \<and>\<^sub>A R a' p * F' \<longrightarrow> a = a'"

lemma preciseI[intro?]: 
  assumes "\<And>a a' h p F F'. h \<Turnstile> R a p * F \<and>\<^sub>A R a' p * F' \<Longrightarrow> a = a'"
  shows "precise R"
  using assms unfolding precise_def by blast

lemma preciseD:
  assumes "precise R"
  assumes "h \<Turnstile> R a p * F \<and>\<^sub>A R a' p * F'"
  shows "a=a'"
  using assms unfolding precise_def by blast

lemma preciseD':
  assumes "precise R"
  assumes "h \<Turnstile> R a p * F" 
  assumes "h \<Turnstile> R a' p * F'"
  shows "a=a'"
  apply (rule preciseD)
  apply (rule assms)
  apply (simp only: mod_and_dist)
  apply (blast intro: assms)
  done

lemma precise_extr_pure[simp]: 
  "precise (\<lambda>x y. \<up>P * R x y) \<longleftrightarrow> (P \<longrightarrow> precise R)"
  "precise (\<lambda>x y. R x y * \<up>P) \<longleftrightarrow> (P \<longrightarrow> precise R)"
  apply (cases P, (auto intro!: preciseI) [2])+
  done

lemma sngr_prec: "precise (\<lambda>x p. p\<mapsto>\<^sub>rx)"
  apply rule
  apply (clarsimp simp: mod_and_dist)
  unfolding sngr_assn_def times_assn_def
  apply (simp add: Abs_assn_inverse)
  apply auto
  done

lemma snga_prec: "precise (\<lambda>x p. p\<mapsto>\<^sub>ax)"
  apply rule
  apply (clarsimp simp: mod_and_dist)
  unfolding snga_assn_def times_assn_def
  apply (simp add: Abs_assn_inverse)
  apply auto
  done

end
