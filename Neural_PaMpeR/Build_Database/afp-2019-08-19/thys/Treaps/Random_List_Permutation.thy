(*
  File:      Random_List.thy
  Authors:   Manuel Eberl

  Some facts about randomly permuted lists and how to obtain them by drawing i.i.d.
  priorities for every element.
*)
section \<open>Randomly-permuted lists\<close>
theory Random_List_Permutation
imports
  Probability_Misc
  Comparison_Sort_Lower_Bound.Linorder_Relations
begin

subsection \<open>General facts about linear orderings\<close>

text \<open>
  We define the set of all linear orderings on a given set and show some properties about it.
\<close>
definition linorders_on :: "'a set \<Rightarrow> ('a \<times> 'a) set set" where
  "linorders_on A = {R. linorder_on A R}"
  
lemma linorders_on_empty [simp]: "linorders_on {} = {{}}"
  by (auto simp: linorders_on_def linorder_on_def refl_on_def)
    
lemma linorders_finite_nonempty:
  assumes "finite A"
  shows   "linorders_on A \<noteq> {}"
proof -
  from finite_distinct_list[OF assms] obtain xs where "set xs = A" "distinct xs" by blast
  hence "linorder_on A (linorder_of_list xs)" by auto
  thus ?thesis by (auto simp: linorders_on_def)
qed

text \<open>
  There is an obvious bijection between permutations of a set (i.\,e.\ lists with all elements
  from that set without repetition) and linear orderings on it.
\<close>
lemma bij_betw_linorders_on:
  assumes "finite A"
  shows   "bij_betw linorder_of_list (permutations_of_set A) (linorders_on A)"
  using bij_betw_linorder_of_list[of A] assms unfolding linorders_on_def by simp

lemma sorted_wrt_list_of_set_linorder_of_list [simp]:
  assumes "distinct xs"
  shows   "sorted_wrt_list_of_set (linorder_of_list xs) (set xs) = xs"
  by (rule sorted_wrt_list_of_set_eqI[of "set xs"]) (insert assms, auto)
    
lemma linorder_of_list_sorted_wrt_list_of_set [simp]:
  assumes "linorder_on A R" "finite A"
  shows   "linorder_of_list (sorted_wrt_list_of_set R A) = R"
proof -
  from assms(1) have subset: "R \<subseteq> A \<times> A" by (auto simp: linorder_on_def refl_on_def)
  from assms and subset show ?thesis
    by (auto simp: linorder_of_list_def linorder_sorted_wrt_list_of_set sorted_wrt_linorder_index_le_iff)
qed

lemma bij_betw_linorders_on':
  assumes "finite A"
  shows   "bij_betw (\<lambda>R. sorted_wrt_list_of_set R A) (linorders_on A) (permutations_of_set A)"
  by (rule bij_betw_byWitness[where f' = linorder_of_list])
     (insert assms, auto simp: linorders_on_def permutations_of_set_def
        linorder_sorted_wrt_list_of_set)

lemma finite_linorders_on [intro]:
  assumes "finite A"
  shows   "finite (linorders_on A)"
proof -
  have "finite (permutations_of_set A)" by simp
  also have "?this \<longleftrightarrow> finite (linorders_on A)"
    using assms by (rule bij_betw_finite [OF bij_betw_linorders_on])
  finally show ?thesis .
qed


text \<open>
  Next, we look at the ordering defined by a list that is permuted with some permutation
  function. For this, we first define the composition of a relation with a function.
\<close>
definition map_relation :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> ('a \<times> 'a) set" where
  "map_relation A f R = {(x,y)\<in>A\<times>A. (f x, f y) \<in> R}"

lemma index_distinct_eqI:
  assumes "distinct xs" "i < length xs" "xs ! i = x"
  shows   "index xs x = i"
  using assms by (induction xs arbitrary: i) (auto simp: nth_Cons split: nat.splits)
  
lemma index_permute_list:
  assumes "\<pi> permutes {..<length xs}" "distinct xs" "x \<in> set xs"
  shows   "index (permute_list \<pi> xs) x = inv \<pi> (index xs x)"
proof -
  have *: "inv \<pi> permutes {..<length xs}" by (rule permutes_inv) fact
  from assms show ?thesis
    using assms permutes_in_image[OF *]
    by (intro index_distinct_eqI) (simp_all add: permute_list_nth permutes_inverses)
qed

lemma linorder_of_list_permute:
  assumes "\<pi> permutes {..<length xs}" "distinct xs"
  shows   "linorder_of_list (permute_list \<pi> xs) =
             map_relation (set xs) ((!) xs \<circ> inv \<pi> \<circ> index xs) (linorder_of_list xs)"
proof -
  note * = permutes_inv[OF assms(1)]
  have less: "inv \<pi> i < length xs" if "i < length xs" for i
    using permutes_in_image[OF *] and that by simp
  from assms and * show ?thesis
    by (auto simp: linorder_of_list_def map_relation_def index_nth_id index_permute_list less)
qed


lemma inj_on_conv_Ex1: "inj_on f A \<longleftrightarrow> (\<forall>y\<in>f`A. \<exists>!x\<in>A. y = f x)"
  by (auto simp: inj_on_def)

lemma bij_betw_conv_Ex1: "bij_betw f A B \<longleftrightarrow> (\<forall>y\<in>B. \<exists>!x\<in>A. f x = y) \<and> B = f ` A"
  unfolding bij_betw_def inj_on_conv_Ex1 by (auto simp: eq_commute)

lemma permutesI:
  assumes "bij_betw f A A" "\<forall>x. x \<notin> A \<longrightarrow> f x = x"
  shows   "f permutes A"
  unfolding permutes_def
proof (intro conjI allI impI)
  fix y
  from assms have [simp]: "f x \<in> A \<longleftrightarrow> x \<in> A" for x
    by (auto simp: bij_betw_def)
  show "\<exists>!x. f x = y"
  proof (cases "y \<in> A")
    case True
    also from assms have "A = f ` A" by (auto simp: bij_betw_def)
    finally obtain x where "x \<in> A" "y = f x" by auto
    with assms and \<open>y \<in> A\<close> show ?thesis
      by (intro ex1I[of _ x]) (auto simp: bij_betw_def dest: inj_onD)
  qed (insert assms, auto)
qed (insert assms, auto)

text \<open>
  We now show the important lemma that any two linear orderings on a finite set can be
  mapped onto each other by a permutation.
\<close>
lemma linorder_permutation_exists:
  assumes "finite A" "linorder_on A R" "linorder_on A R'"
  obtains \<pi> where "\<pi> permutes A" "R' = map_relation A \<pi> R"
proof -
  define xs where "xs = sorted_wrt_list_of_set R A"
  define ys where "ys = sorted_wrt_list_of_set R' A"
  have xs_ys: "distinct xs" "distinct ys" "set xs = A" "set ys = A"
    using assms by (simp_all add: linorder_sorted_wrt_list_of_set xs_def ys_def)
      
  from xs_ys have "mset ys = mset xs" by (simp add: set_eq_iff_mset_eq_distinct [symmetric])
  from mset_eq_permutation[OF this] guess \<pi> . note \<pi> = this
  define \<pi>' where "\<pi>' = (\<lambda>x. if x \<notin> A then x else xs ! inv \<pi> (index xs x))"
  have \<pi>': "\<pi>' permutes A"
  proof (rule permutesI)
    have "bij_betw ((!) xs \<circ> inv \<pi>) {..<length xs} A"
      by (rule bij_betw_trans permutes_imp_bij permutes_inv \<pi> bij_betw_nth)+ (simp_all add: xs_ys)
    hence "bij_betw ((!) xs \<circ> inv \<pi> \<circ> index xs) A A"
      by (rule bij_betw_trans [rotated] bij_betw_index)+
         (insert bij_betw_index[of xs A "length xs"], simp_all add: xs_ys atLeast0LessThan)
    also have "bij_betw ((!) xs \<circ> inv \<pi> \<circ> index xs) A A \<longleftrightarrow> bij_betw \<pi>' A A"
      by (rule bij_betw_cong) (auto simp: \<pi>'_def)
    finally show \<dots> .
  qed (simp_all add: \<pi>'_def)
  
  from assms have "R' = linorder_of_list ys" by (simp add: ys_def)
  also from \<pi> have "ys = permute_list \<pi> xs" by simp
  also have "linorder_of_list (permute_list \<pi> xs) = 
               map_relation A ((!) xs \<circ> inv \<pi> \<circ> index xs) (linorder_of_list xs)"
    using \<pi> by (subst linorder_of_list_permute) (simp_all add: xs_ys)
  also from assms have "linorder_of_list xs = R" by (simp add: xs_def)
  finally have "R' = map_relation A ((!) xs \<circ> inv \<pi> \<circ> index xs) R" .
  also have "\<dots> = map_relation A \<pi>' R" by (auto simp: map_relation_def \<pi>'_def)
  finally show ?thesis using \<pi>' and that[of \<pi>'] by simp
qed

text \<open>
  We now define the linear ordering defined by some priority function, i.\,e.\ a function
  that injectively associates priorities to every element such that elements with lower priority
  are smaller in the resulting ordering.
\<close>
definition linorder_from_keys :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b :: linorder) \<Rightarrow> ('a \<times> 'a) set" where
  "linorder_from_keys A f = {(x,y)\<in>A\<times>A. f x \<le> f y}"

lemma linorder_from_keys_permute:
  assumes "g permutes A"
  shows   "linorder_from_keys A (f \<circ> g) = map_relation A g (linorder_from_keys A f)"
  using permutes_in_image[OF assms] by (auto simp: map_relation_def linorder_from_keys_def)
  
lemma linorder_on_linorder_from_keys [intro]:
  assumes "inj_on f A"
  shows   "linorder_on A (linorder_from_keys A f)"
  using assms by (auto simp: linorder_on_def refl_on_def antisym_def linorder_from_keys_def
                    trans_def total_on_def dest: inj_onD)

lemma linorder_from_keys_empty [simp]: "linorder_from_keys {} = (\<lambda>_. {})"
  by (simp add: linorder_from_keys_def fun_eq_iff)
    

text \<open>
  We now show another important fact, namely that when we draw $n$ values i.\,i.\,d.\ uniformly
  from a non-trivial real interval, we almost surely get distinct values.
\<close>
lemma emeasure_PiM_diagonal:
  fixes a b :: real
  assumes "x \<in> A" "y \<in> A" "x \<noteq> y"
  assumes "a < b" "finite A"
  defines "M \<equiv> uniform_measure lborel {a..b}"
  shows   "emeasure (PiM A (\<lambda>_. M)) {h\<in>A \<rightarrow>\<^sub>E UNIV. h x = h y} = 0"
proof -
  from assms have M: "prob_space M" unfolding M_def
    by (intro prob_space_uniform_measure) auto
  then interpret product_prob_space "\<lambda>_. M" A
    unfolding product_prob_space_def product_prob_space_axioms_def product_sigma_finite_def
    by (auto simp: prob_space_imp_sigma_finite)
  from M interpret pair_sigma_finite M M by unfold_locales
  have [measurable]: "{h\<in>extensional {x, y}. h x = h y} \<in> sets (Pi\<^sub>M {x, y} (\<lambda>i. lborel))"
  proof -
    have "{h\<in>extensional {x,y}. h x = h y} = {h \<in> space (Pi\<^sub>M {x, y} (\<lambda>i. lborel)). h x = h y}"
      by (auto simp: extensional_def space_PiM)
    also have "... \<in> sets (Pi\<^sub>M {x, y} (\<lambda>i. lborel))"
      by measurable
    finally show ?thesis .
  qed
  have [simp]: "sets (PiM A (\<lambda>_. M)) = sets (PiM A (\<lambda>_. lborel))" for A :: "'a set"
    by (intro sets_PiM_cong refl) (simp_all add: M_def)
  have sets_M_M: "sets (M \<Otimes>\<^sub>M M) = sets (borel \<Otimes>\<^sub>M borel)"
    by (intro sets_pair_measure_cong) (auto simp: M_def)
  have [measurable]: "(\<lambda>(b, a). if b = a then 1 else 0) \<in> borel_measurable (M \<Otimes>\<^sub>M M)"
    unfolding measurable_split_conv
    by (subst measurable_cong_sets[OF sets_M_M refl])
       (auto intro!: measurable_If measurable_const measurable_equality_set)
      
  have "{h\<in>A \<rightarrow>\<^sub>E UNIV. h x = h y} = 
          (\<lambda>h. restrict h {x, y}) -` {h\<in>extensional {x, y}. h x = h y} \<inter> space (PiM A (\<lambda>_. M :: real measure))"
    by (auto simp: space_PiM PiE_def extensional_def M_def)
  also have "emeasure (PiM A (\<lambda>_. M)) \<dots> = 
               emeasure (distr (PiM A (\<lambda>_. M)) (PiM {x,y} (\<lambda>_. lborel :: real measure)) 
                 (\<lambda>h. restrict h {x,y})) {h\<in>extensional {x, y}. h x = h y}"
  proof (rule emeasure_distr [symmetric])
    have "(\<lambda>h. restrict h {x, y}) \<in> Pi\<^sub>M A (\<lambda>_. lborel) \<rightarrow>\<^sub>M Pi\<^sub>M {x, y} (\<lambda>_. lborel)"
      using assms by (intro measurable_restrict_subset) auto
    also have "\<dots> = Pi\<^sub>M A (\<lambda>_. M) \<rightarrow>\<^sub>M Pi\<^sub>M {x, y} (\<lambda>_. lborel)"
      by (intro sets_PiM_cong measurable_cong_sets refl) (simp_all add: M_def)
    finally show "(\<lambda>h. restrict h {x, y}) \<in> \<dots>" .
  next
    show "{h\<in>extensional {x, y}. h x = h y} \<in> sets (Pi\<^sub>M {x, y} (\<lambda>_. lborel))" by simp
  qed
  also have "distr (PiM A (\<lambda>_. M)) (PiM {x,y} (\<lambda>_. lborel :: real measure)) (\<lambda>h. restrict h {x,y}) =
               distr (PiM A (\<lambda>_. M)) (PiM {x,y} (\<lambda>_. M)) (\<lambda>h. restrict h {x,y})"
    by (intro distr_cong refl sets_PiM_cong) (simp_all add: M_def)
  also from assms have "\<dots> = Pi\<^sub>M {x, y} (\<lambda>i. M)" by (intro distr_restrict [symmetric]) auto
  also have "emeasure \<dots> {h\<in>extensional {x, y}. h x = h y} =
    nn_integral \<dots> (\<lambda>h. indicator {h\<in>extensional {x, y}. h x = h y} h)"
    by (intro nn_integral_indicator [symmetric]) simp_all
  also have "\<dots> = nn_integral (Pi\<^sub>M {x, y} (\<lambda>i. M)) (\<lambda>h. if h x = h y then 1 else 0)"
    by (intro nn_integral_cong) (auto simp add: indicator_def space_PiM PiE_def)
  also from \<open>x \<noteq> y\<close> have "\<dots> = (\<integral>\<^sup>+ z. (if fst z = snd z then 1 else 0) \<partial>(M \<Otimes>\<^sub>M M))"
    by (intro product_nn_integral_pair) auto
  also have "\<dots> = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+y. (if x = y then 1 else 0) \<partial>M) \<partial>M)"
    by (subst M.nn_integral_fst [symmetric]) simp_all
  also have "\<dots> = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+y. indicator {x} y \<partial>M) \<partial>M)" by (simp add: indicator_def eq_commute)
  also have "\<dots> = (\<integral>\<^sup>+ x. emeasure M {x} \<partial>M)" by (subst nn_integral_indicator) (simp_all add: M_def)
  also have "\<dots> = (\<integral>\<^sup>+ x. 0 \<partial>M)" unfolding M_def
    by (intro nn_integral_cong_AE refl AE_uniform_measureI) auto
  also have "\<dots> = 0" by simp
  finally show ?thesis .
qed      

lemma measurable_linorder_from_keys_restrict:
  assumes fin: "finite A"
  shows "linorder_from_keys A \<in> Pi\<^sub>M A (\<lambda>_. borel :: real measure) \<rightarrow>\<^sub>M count_space (Pow (A \<times> A))"
  (is "_ : ?M \<rightarrow>\<^sub>M _")
  apply (subst measurable_count_space_eq2)
  apply (auto simp add: fin linorder_from_keys_def)
proof -
  note fin[simp]
  fix R assume "R \<subseteq> A \<times> A"
  then have "linorder_from_keys A -` {R} \<inter> space ?M =
    {f \<in> space ?M. \<forall>x\<in>A. \<forall>y\<in>A. (x, y) \<in> R \<longleftrightarrow> f x \<le> f y}"
    by (auto simp add: linorder_from_keys_def set_eq_iff)
  also have "\<dots> \<in> sets ?M"
    by measurable
  finally show "linorder_from_keys A -` {R} \<inter> space ?M \<in> sets ?M" .
qed

lemma measurable_count_space_extend:
  assumes "f \<in> measurable M (count_space A)" "A \<subseteq> B"
  shows   "f \<in> measurable M (count_space B)"
proof -
  note assms(1)
  also have "count_space A = restrict_space (count_space B) A"
    using assms(2) by (subst restrict_count_space) (simp_all add: Int_absorb2)
  finally show ?thesis by (simp add: measurable_restrict_space2_iff)
qed
  
lemma measurable_linorder_from_keys_restrict':
  assumes fin: "finite A" "A \<subseteq> B"
  shows "linorder_from_keys A \<in> Pi\<^sub>M A (\<lambda>_. borel :: real measure) \<rightarrow>\<^sub>M count_space (Pow (B \<times> B))"
  apply (rule measurable_count_space_extend)
   apply (rule measurable_linorder_from_keys_restrict[OF assms(1)])
  using assms by auto
  

context
  fixes a b :: real and A :: "'a set" and M and B
  assumes fin: "finite A" and ab: "a < b" and B: "A \<subseteq> B"
  defines "M \<equiv> distr (PiM A (\<lambda>_. uniform_measure lborel {a..b})) 
                  (count_space (Pow (B \<times> B))) (linorder_from_keys A)"
begin

lemma measurable_linorder_from_keys [measurable]: 
  "linorder_from_keys A \<in> Pi\<^sub>M A (\<lambda>_. borel :: real measure) \<rightarrow>\<^sub>M count_space (Pow (B \<times> B))"
  by (rule measurable_linorder_from_keys_restrict') (auto simp: fin B)

text \<open>
  The ordering defined by randomly-chosen priorities is almost surely linear:
\<close>
theorem almost_everywhere_linorder: "AE R in M. linorder_on A R"
proof -
  define N where "N = PiM A (\<lambda>_. uniform_measure lborel {a..b})"
  have [simp]: "sets (Pi\<^sub>M A (\<lambda>_. uniform_measure lborel {a..b})) = sets (PiM A (\<lambda>_. lborel))"
    by (intro sets_PiM_cong) simp_all
  let ?M_A = "(Pi\<^sub>M A (\<lambda>_. lborel :: real measure))"
  have meas: "{h \<in> A \<rightarrow>\<^sub>E UNIV. h i = h j} \<in> sets ?M_A"
    if [simp]: "i \<in> A" "j \<in> A" for i j
  proof -
    have "{h \<in> A \<rightarrow>\<^sub>E UNIV. h i = h j} = {h \<in> space ?M_A. h i = h j}"
      by (auto simp: space_PiM)
    also have "... \<in> sets ?M_A"
      by measurable
    finally show ?thesis .
  qed
  define X :: "('a \<Rightarrow> real) set" where "X = (\<Union>x\<in>A. \<Union>y\<in>A-{x}. {h\<in>A \<rightarrow>\<^sub>E UNIV. h x = h y})"
  have "AE f in N. inj_on f A"
  proof (rule AE_I)
    show "{f \<in> space N. \<not> inj_on f A} \<subseteq> X"
      by (auto simp: inj_on_def X_def space_PiM N_def)
  next
    show "X \<in> sets N" unfolding X_def N_def
      using meas by (auto intro!: countable_finite fin sets.countable_UN')
  next
    have "emeasure N X \<le> (\<Sum>i\<in>A. emeasure N (\<Union>y\<in>A - {i}. {h \<in> A \<rightarrow>\<^sub>E UNIV. h i = h y}))"
      unfolding X_def N_def using fin meas
      by (intro emeasure_subadditive_finite) 
         (auto simp: disjoint_family_on_def intro!: sets.countable_UN' countable_finite)
    also have "\<dots> \<le> (\<Sum>i\<in>A. \<Sum>j\<in>A-{i}. emeasure N {h \<in> A \<rightarrow>\<^sub>E UNIV. h i = h j})"
      unfolding N_def using fin meas
      by (intro emeasure_subadditive_finite sum_mono) 
         (auto simp: disjoint_family_on_def intro!: sets.countable_UN' countable_finite)
    also have "\<dots> = (\<Sum>i\<in>A. \<Sum>j\<in>A-{i}. 0)" unfolding N_def using fin ab
      by (intro sum.cong refl emeasure_PiM_diagonal) auto
    also have "\<dots> = 0" by simp
    finally show "emeasure N X = 0" by simp
  qed
  hence "AE f in N. linorder_on A (linorder_from_keys A f)"
    by eventually_elim auto
  thus ?thesis unfolding M_def N_def
    by (subst AE_distr_iff) auto
qed

text \<open>
  Furthermore, this is equivalent to choosing one of the $|A|!$ linear orderings uniformly
  at random.
\<close>
theorem random_linorder_by_prios:
  "M = uniform_measure (count_space (Pow (B \<times> B))) (linorders_on A)"
proof -
  from linorders_finite_nonempty[OF fin] obtain R where R: "linorder_on A R"
    by (auto simp: linorders_on_def)
  
  have *: "emeasure M {R} \<le> emeasure M {R'}" if "linorder_on A R" "linorder_on A R'" for R R'
  proof -
    define N where "N = PiM A (\<lambda>_. uniform_measure lborel {a..b})"
    from linorder_permutation_exists[OF fin that]
    obtain \<pi> where \<pi>: "\<pi> permutes A" "R' = map_relation A \<pi> R"
      by blast
    have "(\<lambda>f. f \<circ> \<pi>) \<in> Pi\<^sub>M A (\<lambda>_. lborel :: real measure) \<rightarrow>\<^sub>M Pi\<^sub>M A (\<lambda>_. lborel :: real measure)"
      by (auto intro!: measurable_PiM_single' measurable_PiM_component_rev
          simp: comp_def permutes_in_image[OF \<pi>(1)] space_PiM PiE_def extensional_def)
    also have "\<dots> = N \<rightarrow>\<^sub>M Pi\<^sub>M A (\<lambda>_. lborel)"
      unfolding N_def by (intro measurable_cong_sets refl sets_PiM_cong) simp_all
    finally have [measurable]: "(\<lambda>f. f \<circ> \<pi>) \<in> \<dots>" .    
        
    have [simp]: "measurable N X = measurable (PiM A (\<lambda>_. lborel)) X" for X :: "('a \<times> 'a) set measure"
      unfolding N_def by (intro measurable_cong_sets refl sets_PiM_cong) simp_all
    have [simp]: "measurable M X = measurable (count_space (Pow (B \<times> B))) X" for X :: "('a \<times> 'a) set measure"
      unfolding M_def by simp
      
    have M_eq: "M = distr N (count_space (Pow (B \<times> B))) (linorder_from_keys A)"
      by (simp only: M_def N_def)
    also have "N = distr N (PiM A (\<lambda>_. lborel)) (\<lambda>f. f \<circ> \<pi>)"
      unfolding N_def by (rule PiM_uniform_measure_permute [symmetric]) fact+
    also have "distr \<dots> (count_space (Pow (B \<times> B))) (linorder_from_keys A) = 
                 distr N (count_space (Pow (B \<times> B))) (linorder_from_keys A \<circ> (\<lambda>f. f \<circ> \<pi>)) "
      by (intro distr_distr) simp_all
    also have "\<dots> = distr N (count_space (Pow (B \<times> B))) (map_relation A \<pi> \<circ> linorder_from_keys A)"
      by (intro distr_cong refl) (auto simp: linorder_from_keys_permute[OF \<pi>(1)])
    also have "\<dots> = distr M (count_space (Pow (B \<times> B))) (map_relation A \<pi>)"
      unfolding M_eq using B
      by (intro distr_distr [symmetric]) (auto simp: map_relation_def)
    finally have M_eq': "distr M (count_space (Pow (B \<times> B))) (map_relation A \<pi>) = M" ..

    from that have subset': "R \<subseteq> B \<times> B" "R' \<subseteq> B \<times> B"
      using B by (auto simp: linorder_on_def refl_on_def)
    hence "emeasure M {R} \<le> emeasure M (map_relation A \<pi> -` {R'} \<inter> space M)"
      using subset' by (intro emeasure_mono) (auto simp: M_def \<pi> )
    also have "\<dots> = emeasure (distr M (count_space (Pow (B \<times> B))) (map_relation A \<pi>)) {R'} "
      by (rule emeasure_distr [symmetric]) (insert subset' B, auto simp: map_relation_def)
    also note M_eq'
    finally show ?thesis .
  qed
  have same_prob: "emeasure M {R'} = emeasure M {R}" if "linorder_on A R'" for R'
    using *[of R R'] and *[of R' R] and R and that by simp
  
  from ab have "prob_space M"
    unfolding M_def
    by (intro prob_space.prob_space_distr prob_space_PiM prob_space_uniform_measure) simp_all
  hence "1 = emeasure M (Pow (B \<times> B))" 
    using prob_space.emeasure_space_1[OF \<open>prob_space M\<close>] by (simp add: M_def)
  also have "(Pow (B \<times> B)) = linorders_on A \<union> ((Pow (B \<times> B))-linorders_on A)"
    using B by (auto simp: linorders_on_def linorder_on_def refl_on_def)
  also have "emeasure M \<dots> = emeasure M (linorders_on A) + emeasure M (Pow (B \<times> B)-linorders_on A)"
    using B by (subst plus_emeasure) (auto simp: M_def linorders_on_def linorder_on_def refl_on_def)
  also have "emeasure M (Pow (B \<times> B)-linorders_on A) = 0" using almost_everywhere_linorder 
    by (subst (asm) AE_iff_measurable) (auto simp: linorders_on_def M_def)
  also from fin have "emeasure M (linorders_on A) = (\<Sum>R'\<in>linorders_on A. emeasure M {R'})"
    using B by (intro emeasure_eq_sum_singleton) 
               (auto simp: M_def  linorders_on_def linorder_on_def refl_on_def)
  also have "\<dots> = (\<Sum>R'\<in>linorders_on A. emeasure M {R})"
    by (rule sum.cong) (simp_all add: linorders_on_def same_prob)
  also from fin have "\<dots> = fact (card A) * emeasure M {R}"
    by (simp add: linorders_on_def card_finite_linorders)
  finally have [simp]: "emeasure M {R} = inverse (fact (card A))"
    by (simp add: inverse_ennreal_unique)
  
  show ?thesis
  proof (rule measure_eqI_countable_AE')
    show "sets M = Pow (Pow (B \<times> B))"
      by (simp add: M_def)
  next
    from \<open>finite A\<close> show "countable (linorders_on A)"
      by (blast intro: countable_finite)
  next
    show "AE R in uniform_measure (count_space (Pow (B \<times> B))) 
            (linorders_on A). R \<in> linorders_on A"
      by (rule AE_uniform_measureI) 
         (insert B, auto simp: linorders_on_def linorder_on_def refl_on_def)
  next
    fix R' assume R': "R' \<in> linorders_on A"
    have subset: "linorders_on A \<subseteq> Pow (B \<times> B)"
      using B by (auto simp: linorders_on_def linorder_on_def refl_on_def)
    have "emeasure (uniform_measure (count_space (Pow (B \<times> B))) 
           (linorders_on A)) {R'} = emeasure (count_space (Pow (B \<times> B))) (linorders_on A \<inter> {R'}) /
                                      emeasure (count_space (Pow (B \<times> B))) (linorders_on A)"
      using R' B by (subst emeasure_uniform_measure) (auto simp: linorders_on_def linorder_on_def refl_on_def)
    also have "\<dots> = 1 / emeasure (count_space (Pow (B \<times> B))) (linorders_on A)"
      using R' B by (subst emeasure_count_space) (auto simp: linorders_on_def linorder_on_def refl_on_def)
    also have "\<dots> = 1 / fact (card A)"
      using fin finite_linorders_on[of A]
      by (subst emeasure_count_space [OF subset])
         (auto simp: divide_ennreal [symmetric] linorders_on_def card_finite_linorders)
    also have "\<dots> = emeasure M {R}"
      by (simp add: field_simps divide_ennreal_def)
    also have "\<dots> = emeasure M {R'}"
      using R' by (intro same_prob [symmetric]) (auto simp: linorders_on_def)
    finally show "emeasure M {R'} = emeasure (uniform_measure (count_space (Pow (B \<times> B))) 
                    (linorders_on A)) {R'}" ..
  next
    show "linorders_on A \<subseteq> Pow (B \<times> B)"
      using B by (auto simp: linorders_on_def linorder_on_def refl_on_def)
  qed (auto simp: M_def linorders_on_def almost_everywhere_linorder)
qed

end
end
