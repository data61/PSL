theory TheoremD14
imports TheoremD13
begin

context LocalLexing begin

lemma empty_tokens_of_empty[simp]: "empty_tokens {} = {}"
  using empty_tokens_is_filter by blast

lemma items_le_split_via_eq: "items_le (Suc k) J = items_le k J \<union> items_eq (Suc k) J"
  by (auto simp add: items_le_def items_eq_def)

lemma paths_le_split_via_eq: "paths_le (Suc k) P = paths_le k P \<union> paths_eq (Suc k) P"
  by (auto simp add: paths_le_def paths_eq_def)

lemma natUnion_superset:
  shows "g i \<subseteq> natUnion g"
by (meson natUnion_elem subset_eq)

definition indexle :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "indexle k' u' k u = ((indexlt k' u' k u) \<or> (k' = k \<and> u' = u))"

definition produced_by_scan_step :: "item \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "produced_by_scan_step x k u = (\<exists> k' u' y X. indexle k' u' k u \<and> y \<in> \<J> k' u' \<and> 
   item_end y = k' \<and> X \<in> (\<T> k' u') \<and> x = inc_item y (k' + length (chars_of_token X)) \<and> 
   next_symbol y = Some (terminal_of_token X))"

lemma indexle_trans: "indexle k'' u'' k' u' \<Longrightarrow> indexle k' u' k u \<Longrightarrow> indexle k'' u'' k u"
  using indexle_def indexlt_trans
proof -
  assume a1: "indexle k'' u'' k' u'"
  assume a2: "indexle k' u' k u"
  then have f3: "\<And>n na. u' = u \<or> indexlt n na k u \<or> \<not> indexlt n na k' u'"
    by (meson indexle_def indexlt_trans)
  have "\<And>n na. k' = k \<or> indexlt n na k u \<or> \<not> indexlt n na k' u'"
    using a2 by (meson indexle_def indexlt_trans)
  then show ?thesis
    using f3 a2 a1 indexle_def by auto
qed 

lemma produced_by_scan_step_trans:
  assumes "indexle k' u' k u"
  assumes "produced_by_scan_step x k' u'"
  shows "produced_by_scan_step x k u"
proof -
  from iffD1[OF produced_by_scan_step_def assms(2)] obtain k'a u'a y X where produced_k'_u':
    "indexle k'a u'a k' u' \<and>
     y \<in> \<J> k'a u'a \<and>
     item_end y = k'a \<and>
     X \<in> \<T> k'a u'a \<and>
     x = inc_item y (k'a + length (chars_of_token X)) \<and> next_symbol y = Some (terminal_of_token X)"
     by blast
  then show ?thesis using indexle_trans assms(1) produced_by_scan_step_def by blast 
qed

lemma \<J>_induct[consumes 1, case_names Induct]:
  assumes "x \<in> \<J> k u"
  assumes induct: "\<And> x k u . (\<And> x' k' u'. x' \<in> \<J> k' u' \<Longrightarrow> indexlt k' u' k u \<Longrightarrow> P x' k' u') 
                     \<Longrightarrow> x \<in> \<J> k u \<Longrightarrow> P x k u"
  shows "P x k u"
proof -
  let ?R = "indexlt_rel <*lex*> {}"
  have wf_R: "wf ?R" by (auto simp add: wf_indexlt_rel)
  let ?P = "\<lambda> a. snd a \<in> \<J> (fst (fst a)) (snd (fst a)) \<longrightarrow> P (snd a) (fst (fst a)) (snd (fst a))"
  have "x \<in> \<J> k u \<longrightarrow> P x k u"
    apply (rule wf_induct[OF wf_R, where P = ?P and a = "((k, u), x)", simplified])
    apply (auto simp add: indexlt_def[symmetric])
    apply (rule_tac x=ba and k=a and u=b in induct)
    by auto
  thus ?thesis using assms by auto 
qed

lemma \<pi>_no_tokens_item_end: 
  assumes x_in_\<pi>: "x \<in> \<pi> k {} I"
  shows "item_end x = k \<or> x \<in> I"
proof -
  have x_in_limit: "x \<in> limit (\<lambda>I. Complete k (Predict k I)) I"
    using x_in_\<pi> \<pi>_no_tokens by auto  
  then show ?thesis
  proof (induct rule: limit_induct)
    case (Init x) then show ?case by auto
  next
    case (Iterate x J)
      from Iterate(2) have "item_end x = k \<or> x \<in> Predict k J"
        using Complete_item_end by auto
      then show ?case 
      proof (induct rule: disjCases2)
        case 1 then show ?case by blast
      next
        case 2 
          then have "item_end x = k \<or> x \<in> J" 
            using Predict_item_end by auto
          then show ?case
          proof (induct rule: disjCases2)
            case 1 then show ?case by blast
          next
            case 2 then show ?case using Iterate(1)[OF 2] by blast
          qed
      qed 
  qed
qed 

lemma natUnion_ex: "x \<in> natUnion f \<Longrightarrow> \<exists> i. x \<in> f i"
  by (metis (no_types, hide_lams) mk_disjoint_insert natUnion_superset natUnion_upperbound 
    subsetCE subset_insert)

lemma locate_in_limit:
  assumes x_in_limit: "x \<in> limit f X"
  assumes x_notin_X: "x \<notin> X"
  shows "\<exists> n. x \<in> funpower f (Suc n) X \<and> x \<notin> funpower f n X"
proof -
  have "\<exists> N. x \<in> funpower f N X" using x_in_limit limit_def natUnion_ex by fastforce
  then obtain N where N: "x \<in> funpower f N X" by blast
  {
    fix n :: nat
    have "x \<in> funpower f n X \<Longrightarrow> \<exists> m < n. x \<in> funpower f (Suc m) X \<and> x \<notin> funpower f m X"
    proof (induct n)
      case 0 
        with x_notin_X show ?case by auto
    next
      case (Suc n)
        have "x \<notin> funpower f n X \<or> x \<in> funpower f n X" by blast
        then show ?case
        proof (induct rule: disjCases2)
          case 1     
            then show ?case using Suc by fastforce
        next
          case 2
            from Suc(1)[OF 2] show ?case using less_SucI by blast 
        qed 
    qed
  }
  with N show ?thesis by auto
qed

lemma produced_by_scan_step: 
  "x \<in> \<J> k u \<Longrightarrow> item_end x > k \<Longrightarrow> produced_by_scan_step x k u"
proof (induct rule: \<J>_induct)
  case (Induct x k u)
    have "(k = 0 \<and> u = 0) \<or> (k > 0 \<and> u = 0) \<or> (u > 0)" by arith
    then show ?case
    proof (induct rule: disjCases3)
      case 1
        with Induct have "item_end x = 0" using \<J>_0_0_item_end by blast  
        with Induct have "False" by arith
        then show ?case by  blast
    next
      case 2
        then obtain k' where k': "k = Suc k'" using Suc_pred' by blast 
        with Induct 2 have "x \<in> \<J> (Suc k') 0" by auto
        then have "x \<in> \<pi> k {} (\<I> k')" by (simp add: k') 
        then have "item_end x = k \<or> x \<in> \<I> k'" using \<pi>_no_tokens_item_end by blast
        then show ?case
        proof (induct rule: disjCases2)
          case 1
            with Induct have "False" by auto
            then show ?case by blast
        next
          case 2
            then have "\<exists> u'. x \<in> \<J> k' u'" using \<I>.simps natUnion_ex by fastforce
            then obtain u' where u': "x \<in> \<J> k' u'" by blast
            have k'_bound: "k' < item_end x" using k' Induct by arith
            have indexlt: "indexlt k' u' k u" by (simp add: indexlt_simp k') 
            from Induct(1)[OF u' this k'_bound] 
            have pred_produced: "produced_by_scan_step x k' u'" .
            then show ?case using indexlt produced_by_scan_step_trans indexle_def by blast 
        qed
    next
      case 3
        then have ex_u': "\<exists> u'. u = Suc u'" by arith
        then obtain u' where u': "u = Suc u'" by blast
        with Induct have "x \<in> \<J> k (Suc u')" by metis
        then have x_in_\<pi>: "x \<in> \<pi> k (\<T> k u) (\<J> k u')" using u' \<J>.simps by metis
        have "x \<in> \<J> k u' \<or> x \<notin> \<J> k u'" by blast
        then show ?case
        proof (induct rule: disjCases2)
          case 1
            have indexlt: "indexlt k u' k u" by (simp add: indexlt_simp u')             
            with Induct(1)[OF 1 indexlt Induct(3)] show ?case
              using indexle_def produced_by_scan_step_trans by blast
        next
          case 2
            have item_end_x: "k < item_end x" using Induct by auto
            obtain f where f: "f = Scan (\<T> k u) k \<circ> Complete k \<circ> Predict k" by blast
            have "x \<in> limit f (\<J> k u')"
              using x_in_\<pi> \<pi>_functional f by simp
            from locate_in_limit[OF this 2] obtain n where n:
              "x \<in> funpower f (Suc n) (\<J> k u') \<and>
               x \<notin> funpower f n (\<J> k u')" by blast
            obtain Y where Y: "Y = funpower f n (\<J> k u')"
              by blast
            have x_f_Y: "x \<in> f Y \<and> x \<notin> Y" using Y n by auto
            then have "x \<in> Scan (\<T> k u) k (Complete k (Predict k Y))" using comp_apply f by simp
            then have "x \<in> (Complete k (Predict k Y)) \<or>
              x \<in> { inc_item x' (k + length c) | x' t c. x' \<in> bin (Complete k (Predict k Y)) k \<and> 
                    (t, c) \<in> (\<T> k u) \<and> next_symbol x' = Some t }" using Scan_def by simp
            then show ?case
            proof (induct rule: disjCases2)
              case 1
                then have "False" using item_end_x x_f_Y Complete_item_end Predict_item_end
                  using less_not_refl3 by blast
                then show ?case by auto
            next
              case 2
                have "Y \<subseteq> limit f (\<J> k u')" using Y limit_def natUnion_superset by fastforce
                then have "Y \<subseteq> \<pi> k (\<T> k u) (\<J> k u')" using f by (simp add: \<pi>_functional)  
                then have Y_in_\<J>: "Y \<subseteq> \<J> k u" using u' by simp
                then have in_\<J>: "Complete k (Predict k Y) \<subseteq> \<J> k u"
                proof - (* automatically generated *)
                  have f1: "\<forall>f I Ia i. (\<not> mono f \<or> \<not> (I::item set) \<subseteq> Ia \<or> (i::item) \<notin> f I) \<or> i \<in> f Ia"
                    by (meson mono_subset_elem)
                  obtain ii :: "item set \<Rightarrow> item set \<Rightarrow> item" where
                    "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (ii x0 x1 \<in> x1 \<and> ii x0 x1 \<notin> x0)"
                    by moura
                  then have f2: "\<forall>I Ia. ii Ia I \<in> I \<and> ii Ia I \<notin> Ia \<or> I \<subseteq> Ia"
                    by blast
                  obtain nn :: nat where
                    f3: "u = Suc nn"
                    using ex_u' by presburger
                  moreover
                  { assume "ii (\<J> k u) (Complete k (Predict k Y)) \<in> Complete k (\<pi> k (\<T> k (Suc nn)) (\<J> k nn))"
                    then have ?thesis
                      using f3 f2 Complete_\<pi>_fix by auto }
                  ultimately show ?thesis
                    using f2 f1 by (metis (full_types) Complete_regular Predict_\<pi>_fix Predict_regular 
                      \<J>.simps(2) Y_in_\<J> regular_implies_mono)
                qed 
                from 2 obtain  x' t c where x'_t_c:
                  "x = inc_item x' (k + length c) \<and> x' \<in> bin (Complete k (Predict k Y)) k \<and> 
                    (t, c) \<in> \<T> k u \<and> next_symbol x' = Some t" by blast
                show ?case
                  apply (simp add: produced_by_scan_step_def)
                  apply (rule_tac x=k in exI)
                  apply (rule_tac x=u in exI)
                  apply (simp add: indexle_def)
                  apply (rule_tac x=x' in exI)
                  apply auto
                  using x'_t_c bin_def in_\<J> apply auto[1]
                  using x'_t_c bin_def apply blast
                  apply (rule_tac x=t in exI)
                  apply (rule_tac x=c in exI)
                  using x'_t_c by auto
            qed      
        qed
    qed  
qed

lemma limit_single_step:
  assumes "x \<in> f X"
  shows "x \<in> limit f X"
by (metis assms elem_limit_simp funpower.simps(1) funpower.simps(2))

lemma Gen_union: "Gen (A \<union> B) = Gen A \<union> Gen B"
  by (simp add: Gen_def, blast)

lemma is_prefix_Prefixes_subset:
  assumes "is_prefix q p"
  shows "Prefixes q \<subseteq> Prefixes p"
proof -
  show ?thesis
    apply (auto simp add: Prefixes_def)
    using assms by (metis is_prefix_append is_prefix_def) 
qed

lemma Prefixes_subset_\<P>:
  assumes "p \<in> \<P> k u"
  shows "Prefixes p \<subseteq> \<P> k u"
using Prefixes_is_prefix assms prefixes_are_paths by blast

lemma Prefixes_subset_paths_le:
  assumes "Prefixes p \<subseteq> P"
  shows "Prefixes p \<subseteq> paths_le (charslength p) P"
using Prefixes_is_prefix assms charslength_of_prefix paths_le_def by auto

lemma Scan_\<J>_subset_\<J>:
  "Scan (\<T> k (Suc u)) k (\<J> k u) \<subseteq> \<J> k (Suc u)"
by (metis (no_types, lifting) Scan_\<pi>_fix \<J>.simps(2) \<J>_subset_Suc_u monoD mono_Scan)

lemma subset_\<J>k: "u \<le> v \<Longrightarrow> \<J> k u \<subseteq> \<J> k v"
  thm \<J>_subset_Suc_u
  by (rule subset_fSuc, rule \<J>_subset_Suc_u) 

lemma subset_\<J>\<I>k: "\<J> k u \<subseteq> \<I> k" by (auto simp add: natUnion_def)

lemma subset_\<I>\<J>Suc: "\<I> k \<subseteq> \<J> (Suc k) u" 
proof -
  have a: "\<I> k \<subseteq> \<J> (Suc k) 0" 
    apply (simp only: \<J>.simps)
    using \<pi>_apply_setmonotone by blast    
  show ?thesis 
    apply (case_tac "u = 0")
    apply (simp only: a)
    apply (rule subset_trans[OF a subset_\<J>k])
    by auto
qed

lemma subset_\<I>Suc: "\<I> k \<subseteq> \<I> (Suc k)"
  by (rule subset_trans[OF subset_\<I>\<J>Suc subset_\<J>\<I>k])

lemma subset_\<I>: "i \<le> j \<Longrightarrow> \<I> i \<subseteq> \<I> j"
  by (rule subset_fSuc[where u=i and v=j and f = \<I>, OF subset_\<I>Suc])

lemma subset_\<J> :
  assumes leq: "k' < k \<or> (k' = k \<and> u' \<le> u)"
  shows "\<J> k' u' \<subseteq> \<J> k u"
proof -
  from leq show ?thesis
  proof (induct rule: disjCases2)
    case 1
    have s1: "\<J> k' u' \<subseteq> \<I> k'" by (rule_tac subset_\<J>\<I>k) 
    have s2: "\<I> k' \<subseteq> \<I> (k - 1)" 
      apply (rule_tac subset_\<I>)
      using 1 by arith
    from subset_\<I>\<J>Suc[where k="k - 1"] 1 have s3: "\<I> (k - 1) \<subseteq> \<J> k 0"
      by simp
    have s4: "\<J> k 0 \<subseteq> \<J> k u" by (rule_tac subset_\<J>k, simp)
    from s1 s2 s3 s4 subset_trans show ?case by blast
  next
    case 2 thus ?case by (simp add : subset_\<J>k)
  qed
qed  

lemma \<J>_subset:
  assumes "indexle k' u' k u"
  shows "\<J> k' u' \<subseteq> \<J> k u"
using subset_\<J> indexle_def indexlt_simp
by (metis assms less_imp_le_nat order_refl) 

lemma Scan_items_le:
  assumes bounded_T: "\<And> t . t \<in> T \<Longrightarrow> length (chars_of_token t) \<le> l"
  shows "Scan T k (items_le k P) \<subseteq> items_le (k + l) (Scan T k P)"
proof -
  {
    fix x :: item
    assume x_dom: "x \<in> Scan T k (items_le k P)"
    then have x_dom': "x \<in> Scan T k P"
      by (meson items_le_is_filter mono_Scan mono_subset_elem)
    from x_dom have "x \<in> items_le k P \<or> 
      (\<exists> y t c. x = inc_item y (k + length c) \<and> y \<in> bin (items_le k P) k \<and> (t, c) \<in> T
       \<and> next_symbol y = Some t)" 
      using Scan_def using UnE mem_Collect_eq by auto 
    then have "item_end x \<le> k + l"
    proof (induct rule: disjCases2)
      case 1 then show ?case
        by (meson items_le_fix_D items_le_idempotent trans_le_add1)
    next
      case 2 
        then obtain y t c where y: "x = inc_item y (k + length c) \<and> y \<in> bin (items_le k P) k \<and> 
          (t, c) \<in> T \<and> next_symbol y = Some t" by blast
        then have item_end_x: "item_end x = (k + length c)" by simp
        from bounded_T y have "length c \<le> l"
          using chars_of_token_simp by auto 
        with item_end_x show ?case by arith
    qed
    with x_dom' have "x \<in> items_le (k + l) (Scan T k P)"
      using items_le_def mem_Collect_eq by blast
  }
  then show ?thesis by blast      
qed

lemma Scan_mono_tokens:
  "P \<subseteq> Q \<Longrightarrow> Scan P k I \<subseteq> Scan Q k I"
by (auto simp add: Scan_def)

theorem thmD14: "k \<le> length Doc \<Longrightarrow> items_le k (\<J> k u) = Gen (paths_le k (\<P> k u)) \<and> \<T> k u = \<Z> k u 
    \<and> items_le k (\<I> k) = Gen (paths_le k (\<Q> k))"
proof (induct k arbitrary: u rule: less_induct)
  case (less k)
    have "k = 0 \<or> k \<noteq> 0" by arith
    then show ?case 
    proof (induct rule: disjCases2)
      case 1
        have \<J>_eq_\<P>: "items_le k (\<J> k 0) = Gen (paths_le k (\<P> k 0))" 
          by (simp only: 1 thmD8 items_le_paths_le)
        show ?case using thmD13[OF \<J>_eq_\<P> less.prems] by blast
    next
      case 2
        have "\<exists> k'. k = Suc k'" using 2 by arith
        then obtain k' where k': "k = Suc k'" by blast
        have k'_less_k: "k' < k" using k' by arith
        have "items_le k (\<J> k 0) = Gen (paths_le k (\<P> k 0))"          
        proof -
          have simp_left: "items_le k (\<J> k 0) = \<pi> k {} (items_le k (\<I> k'))"
            using items_le_\<pi>_swap k' wellformed_items_\<I> by auto 
          have simp_right: "Gen (paths_le k (\<P> k 0)) = natUnion (\<lambda> v. Gen (paths_le k (\<P> k' v)))"
            by (simp add: k' paths_le_pointwise pointwise_Gen pointwise_natUnion_swap)            
          {
            fix v :: nat
            have split_\<J>: "items_le k (\<J> k' v) = items_le k' (\<J> k' v) \<union> items_eq k (\<J> k' v)" 
              using k'  items_le_split_via_eq by blast
            have sub1: "items_le k' (\<J> k' v) \<subseteq> natUnion (\<lambda> v. Gen (paths_le k (\<P> k' v)))"
            proof -
              have h: "items_le k' (\<J> k' v) \<subseteq> Gen (paths_le k (\<P> k' v))"
              proof - (* automatically generated *)
                have f1: "items_le k' (Gen (\<P> k' v)) \<union> items_eq (Suc k') (Gen (\<P> k' v)) = 
                  Gen (paths_le k (\<P> k' v))"
                  using LocalLexing.items_le_split_via_eq LocalLexing_axioms items_le_paths_le k' 
                  by blast
                have "k' \<le> length Doc"
                  by (metis (no_types) dual_order.trans k' less.prems lessI less_imp_le_nat)
                then have "items_le k' (\<J> k' v) = items_le k' (Gen (\<P> k' v))"
                  by (simp add: items_le_paths_le k' less.hyps)
                then show ?thesis
                  using f1 by blast
              qed
              have "Gen (paths_le k (\<P> k' v)) \<subseteq> natUnion (\<lambda> v. Gen (paths_le k (\<P> k' v)))"
                using natUnion_superset by fastforce
              then show ?thesis using h by blast
            qed
            {
              fix x :: item
              assume x_dom: "x \<in> items_eq k (\<J> k' v)"
              have x_in_\<J>: "x \<in> \<J> k' v" using x_dom items_eq_def by auto
              have item_end_x: "item_end x = k" using x_dom items_eq_def by auto
              then have k'_bound: "k' < item_end x" using k' by arith
              from produced_by_scan_step[OF x_in_\<J> k'_bound]
              have "produced_by_scan_step x k' v" .
              from iffD1[OF produced_by_scan_step_def this] obtain k'' v'' y X where scan_step:
                "indexle k'' v'' k' v \<and> y \<in> \<J> k'' v'' \<and> item_end y = k'' \<and> X \<in> \<T> k'' v'' \<and>
                 x = inc_item y (k'' + length (chars_of_token X)) \<and> 
                 next_symbol y = Some (terminal_of_token X)" by blast
              then have y_in_items_le: "y \<in> items_le k'' (\<J> k'' v'')"
                using items_le_def LocalLexing_axioms le_refl mem_Collect_eq by blast 
              have y_in_Gen: "y \<in> Gen(paths_le k'' (\<P> k'' v''))"
              proof - (* automatically generated *)
                have f1: "\<And>n. k' < n \<or> \<not> k < n"
                  using Suc_lessD k' by blast
                have f2: "k'' = k' \<or> k'' < k'"
                  using indexle_def indexlt_simp scan_step by force
                have f3: "k' < k"
                  using k' by blast
                have f4: "k' \<le> length Doc"
                  using f1 by (meson less.prems less_Suc_eq_le)
                have "k'' \<le> length Doc \<or> k' = k''"
                  using f2 f1 by (meson Suc_lessD less.prems less_Suc_eq_le less_trans_Suc)
                then show ?thesis
                  using f4 f3 f2 Suc_lessD y_in_items_le less.hyps less_trans_Suc by blast
              qed
              then have "\<exists> p. p \<in> \<P> k'' v'' \<and> pvalid p y"
                by (meson Gen_implies_pvalid paths_le_is_filter rev_subsetD)
              then obtain p where p: "p \<in> \<P> k'' v'' \<and> pvalid p y" by blast
              then have charslength_p: "charslength p = k''" using pvalid_item_end scan_step by auto 
              have pvalid_p_y: "pvalid p y" using p by blast
              have "admissible (p@[(fst X, snd X)])"
                apply (rule pvalid_next_terminal_admissible)
                apply (rule pvalid_p_y)
                using scan_step apply (simp add: terminal_of_token_def) 
                using scan_step by (metis TokensAt_subset_\<X> \<T>_subset_TokensAt \<X>_are_terminals 
                  rev_subsetD terminal_of_token_def) 
              then have admissible_p_X: "admissible (p@[X])" by simp
              have X_in_\<Z>: "X \<in> \<Z> k'' (Suc v'')" by (metis (no_types, lifting) Suc_lessD \<Z>_subset_Suc 
                k'_bound dual_order.trans indexle_def indexlt_simp item_end_of_inc_item item_end_x 
                le_add1 le_neq_implies_less less.hyps less.prems not_less_eq scan_step subsetCE) 
              have pX_in_\<P>_k''_v'': "p@[X] \<in> \<P> k'' (Suc v'')"   
                apply (simp only: \<P>.simps)
                apply (rule limit_single_step)
                apply (auto simp only: Append_def)
                apply (rule_tac x=p in exI)
                apply (rule_tac x=X in exI)
                apply (simp only: admissible_p_X X_in_\<Z>)
                using charslength_p p by auto
              have "indexle k'' v'' k' v" using scan_step by simp
              then have "indexle k'' (Suc v'') k' (Suc v)"
                by (simp add: indexle_def indexlt_simp)               
              then have "\<P> k'' (Suc v'') \<subseteq> \<P> k' (Suc v)"
                by (metis indexle_def indexlt_simp less_or_eq_imp_le subset_\<P>) 
              with pX_in_\<P>_k''_v'' have pX_in_\<P>_k': "p@[X] \<in> \<P> k' (Suc v)" by blast
              have "charslength (p@[X]) = k'' +  length (chars_of_token X)"
                using charslength_p by auto
              then have "charslength (p@[X]) = item_end x" using scan_step by simp
              then have charslength_p_X: "charslength (p@[X]) = k" using item_end_x by simp
              then have pX_dom: "p@[X] \<in> paths_le k (\<P> k' (Suc v))"
                using lessI less_Suc_eq_le mem_Collect_eq pX_in_\<P>_k' paths_le_def by auto
              have wellformed_x: "wellformed_item x"
                using item_end_x less.prems scan_step wellformed_inc_item wellformed_items_\<J> 
                  wellformed_items_def by auto
              have wellformed_p_X: "wellformed_tokens (p@[X])"
                using \<P>_wellformed pX_in_\<P>_k''_v'' by blast
              from iffD1[OF pvalid_def pvalid_p_y] obtain r \<gamma> where r_\<gamma>:
                "wellformed_tokens p \<and>
                 wellformed_item y \<and>
                 r \<le> length p \<and>
                 charslength p = item_end y \<and>
                 charslength (take r p) = item_origin y \<and>
                 is_derivation (terminals (take r p) @ [item_nonterminal y] @ \<gamma>) \<and>
                 derives (item_\<alpha> y) (terminals (drop r p))" by blast
              have r_le_p: "r \<le> length p" by (simp add: r_\<gamma>)
              have item_nonterminal_x: "item_nonterminal x = item_nonterminal y" 
                by (simp add: scan_step)
              have item_\<alpha>_x: "item_\<alpha> x = (item_\<alpha> y) @ [terminal_of_token X]"
                by (simp add: item_\<alpha>_of_inc_item r_\<gamma> scan_step)              
              have pvalid_x: "pvalid (p@[X]) x"                
                apply (auto simp add: pvalid_def wellformed_x wellformed_p_X)
                apply (rule_tac x=r in exI)
                apply auto
                apply (simp add: le_SucI r_\<gamma>)
                using r_\<gamma> scan_step apply auto[1]
                using r_\<gamma> scan_step apply auto[1]
                apply (rule_tac x=\<gamma> in exI)
                apply (simp add: r_le_p item_nonterminal_x)
                using r_\<gamma> apply simp
                apply (simp add: r_le_p item_\<alpha>_x)
                by (metis terminals_singleton append_Nil2 
                  derives_implies_leftderives derives_is_sentence is_sentence_concat 
                  is_sentence_cons is_symbol_def is_word_append is_word_cons is_word_terminals 
                  is_word_terminals_drop leftderives_implies_derives leftderives_padback 
                  leftderives_refl r_\<gamma> terminals_append terminals_drop wellformed_p_X)
              then have "x \<in> Gen (paths_le k (\<P> k' (Suc v)))" using pX_dom Gen_def 
                LocalLexing_axioms mem_Collect_eq by auto 
            }
            then have sub2: "items_eq k (\<J> k' v) \<subseteq> natUnion (\<lambda> v. Gen (paths_le k (\<P> k' v)))"
              by (meson dual_order.trans natUnion_superset subsetI)                                       
            have suffices3: "items_le k (\<J> k' v) \<subseteq> natUnion (\<lambda> v. Gen (paths_le k (\<P> k' v)))"
              using split_\<J> sub1 sub2 by blast
            have "items_le k (\<J> k' v) \<subseteq> Gen (paths_le k (\<P> k 0))"
              using suffices3 simp_right by blast
          }
          note suffices2 = this
          have items_le_natUnion_swap: "items_le k (\<I> k') = natUnion(\<lambda> v. items_le k (\<J> k' v))"
            by (simp add: items_le_pointwise pointwise_natUnion_swap)            
          then have suffices1: "items_le k (\<I> k') \<subseteq> Gen (paths_le k (\<P> k 0))"
            using suffices2 natUnion_upperbound by metis    
          have sub_lemma: "items_le k (\<J> k 0) \<subseteq> Gen (paths_le k (\<P> k 0))"
          proof -
            have "items_le k (\<J> k 0) \<subseteq> Gen (\<P> k 0)"
              apply (subst simp_left)
              apply (rule thmD5)
              apply (auto simp only: less)
              using suffices1 items_le_is_filter items_le_paths_le subsetCE by blast 
            then show ?thesis
              by (simp add: items_le_idempotent remove_paths_le_in_subset_Gen)
          qed          
          have eq1: "\<pi> k {} (items_le k (\<I> k')) = \<pi> k {} (items_le k (natUnion (\<J> k')))" by simp
          then have eq2: "\<pi> k {} (items_le k (natUnion (\<J> k'))) = 
            \<pi> k {} (natUnion (\<lambda> v. items_le k (\<J> k' v)))"
            using items_le_natUnion_swap by auto
          from simp_left eq1 eq2 
          have simp_left': "items_le k (\<J> k 0) = \<pi> k {} (natUnion (\<lambda> v. items_le k (\<J> k' v)))"
            by metis
          {
            fix v :: nat
            fix q :: "token list"
            fix x :: item
            assume q_dom: "q \<in> paths_eq k (\<P> k' v)"
            assume pvalid_q_x: "pvalid q x"
            have q_in_\<P>: "q \<in> \<P> k' v" using q_dom paths_eq_def by auto
            have charslength_q: "charslength q = k" using q_dom paths_eq_def by auto
            with k'_less_k have q_nonempty: "q \<noteq> []"
              using "2.hyps" chars.simps(1) charslength.simps list.size(3) by auto 
            then have "\<exists> p X. q = p @ [X]" by (metis append_butlast_last_id) 
            then obtain p X where pX: "q = p @ [X]" by blast
            from last_step_of_path[OF q_in_\<P> pX] obtain k'' v'' where k'':
              "indexlt k'' v'' k' v \<and> q \<in> \<P> k'' (Suc v'') \<and> charslength p = k'' \<and> 
               X \<in> \<Z> k'' (Suc v'')" by blast
            have h1: "p \<in> \<PP>"
              by (metis (no_types, lifting) LocalLexing.\<PP>_covers_\<P> LocalLexing_axioms 
                append_Nil2 is_prefix_cancel is_prefix_empty pX prefixes_are_paths q_in_\<P> subsetCE) 
            have h2: "charslength p = k''" using k'' by blast
            obtain T where T: "T = {X}" by blast
            have h3: "X \<in> T" using T by blast
            have h4: "T \<subseteq> \<X> k''" using \<Z>_subset_\<X> T k'' by blast 
            obtain N where N: "N = item_nonterminal x" by blast
            obtain \<alpha> where \<alpha>: "\<alpha> = item_\<alpha> x" by blast
            obtain \<beta> where \<beta>: "\<beta> = item_\<beta> x" by blast
            have wellformed_x: "wellformed_item x" using pvalid_def pvalid_q_x by blast 
            then have h5: "(N, \<alpha> @ \<beta>) \<in> \<RR>"
              using N \<alpha> \<beta> item_nonterminal_def item_rhs_def item_rhs_split prod.collapse 
                wellformed_item_def by auto 
            have pvalid_left_q_x: "pvalid_left q x" using pvalid_q_x by (simp add: pvalid_left) 
            from iffD1[OF pvalid_left_def pvalid_left_q_x] obtain r \<gamma> where r_\<gamma>: 
              "wellformed_tokens q \<and>
               wellformed_item x \<and>
               r \<le> length q \<and>
               charslength q = item_end x \<and>
               charslength (take r q) = item_origin x \<and>
               is_leftderivation (terminals (take r q) @ [item_nonterminal x] @ \<gamma>) \<and>
               leftderives (item_\<alpha> x) (terminals (drop r q))" by blast
            have h6: "r \<le> length q" using r_\<gamma> by blast
            have h7: "leftderives [\<SS>] (terminals (take r q) @ [N] @ \<gamma>)"
              using r_\<gamma> N is_leftderivation_def by blast 
            have h8: "leftderives \<alpha> (terminals (drop r q))" using r_\<gamma> \<alpha> by metis
            have h9: "k = k'' + length (chars_of_token X)" using r_\<gamma>
              using charslength_q h2 pX by auto 
            have h10: "x = Item (N, \<alpha> @ \<beta>) (length \<alpha>) (charslength (take r q)) k"
              by (metis N \<alpha> \<beta> charslength_q item.collapse item_dot_is_\<alpha>_length item_nonterminal_def 
                item_rhs_def item_rhs_split prod.collapse r_\<gamma>)             
            from thmD11[OF h1 h2 h3 h4 pX h5 h6 h7 h8 h9 h10] 
            have "x \<in> items_le k (\<pi> k {} (Scan T k'' (Gen (Prefixes p))))" 
              by blast
            then have x_in: "x \<in> \<pi> k {} (Scan T k'' (Gen (Prefixes p)))"
              using items_le_is_filter by blast             
            have subset1: "Prefixes p \<subseteq> Prefixes q"
              apply (rule is_prefix_Prefixes_subset)
              by (simp add: pX is_prefix_def)
            have subset2: "Prefixes q \<subseteq> \<P> k'' (Suc v'')" 
              apply (rule Prefixes_subset_\<P>)
              using k'' by blast
            from subset1 subset2 have "Prefixes p \<subseteq> \<P> k'' (Suc v'')" by blast
            then have "Prefixes p \<subseteq> paths_le k'' (\<P> k'' (Suc v''))" 
              using k'' Prefixes_subset_paths_le by blast            
            then have subset3: "Gen (Prefixes p) \<subseteq> Gen (paths_le k'' (\<P> k'' (Suc v'')))"
              using Gen_def LocalLexing_axioms by auto
            have k''_less_k: "k'' < k" using k'' k' using indexlt_simp less_Suc_eq by auto 
            then have k''_Doc_bound: "k'' \<le> length Doc" using less by auto
            from less(1)[OF k''_less_k k''_Doc_bound, of "Suc v''"]
            have induct1: "items_le k'' (\<J> k'' (Suc v'')) = Gen (paths_le k'' (\<P> k'' (Suc v'')))"
              by blast
            from less(1)[OF k''_less_k k''_Doc_bound, of "Suc(Suc v'')"]
            have induct2: "\<T> k'' (Suc (Suc v'')) = \<Z> k'' (Suc (Suc v''))" by blast
            have subset4: "Gen (Prefixes p) \<subseteq> items_le k'' (\<J> k'' (Suc v''))"
              using subset3 induct1 by auto
            from induct1 subset4
            have subset6: "Scan T k'' (Gen (Prefixes p)) \<subseteq> 
              Scan T k'' (items_le k'' (\<J> k'' (Suc v'')))"
              apply (rule_tac monoD[OF mono_Scan])
              by blast
            have "k'' + length (chars_of_token X) = k"
              by (simp add: h9)
            have "\<And> t. t \<in> T \<Longrightarrow> length (chars_of_token t) \<le> length (chars_of_token X)"
              using T by auto
            from Scan_items_le[of T, OF this, simplified, of k'' "\<J> k'' (Suc v'')"] h9
            have subset7: "Scan T k'' (items_le k'' (\<J> k'' (Suc v'')))
              \<subseteq> items_le k (Scan T k'' (\<J> k'' (Suc v'')))" by simp
            have "T \<subseteq> \<Z> k'' (Suc (Suc v''))" using T k''
              using \<Z>_subset_Suc rev_subsetD singletonD subsetI by blast 
            then have T_subset_\<T>: "T \<subseteq> \<T> k'' (Suc (Suc v''))" using induct2 by auto
            have subset8: "Scan T k'' (\<J> k'' (Suc v'')) \<subseteq>
              Scan (\<T> k'' (Suc (Suc v''))) k'' (\<J> k'' (Suc v''))" 
              using T_subset_\<T> Scan_mono_tokens by blast
            have subset9: "Scan (\<T> k'' (Suc (Suc v''))) k'' (\<J> k'' (Suc v'')) \<subseteq> \<J> k'' (Suc (Suc v''))"
              by (rule Scan_\<J>_subset_\<J>)
            have subset10: "(Scan T k'' (\<J> k'' (Suc v''))) \<subseteq> \<J> k'' (Suc (Suc v''))"
              using subset8 subset9 by blast
            have "k'' \<le> k'" using k'' indexlt_simp by auto
            then have "indexle k'' (Suc (Suc v'')) k' (Suc (Suc v''))" using indexlt_simp
              using indexle_def le_neq_implies_less by auto
            then have subset11: "\<J> k'' (Suc (Suc v'')) \<subseteq> \<J> k' (Suc (Suc v''))"
              using \<J>_subset by blast
            have subset12: "Scan T k'' (\<J> k'' (Suc v'')) \<subseteq> \<J> k' (Suc (Suc v''))"
              using subset8 subset9 subset10 subset11 by blast
            then have subset13: "items_le k (Scan T k'' (\<J> k'' (Suc v''))) \<subseteq>
              items_le k (\<J> k' (Suc (Suc v'')))"
              using items_le_def mem_Collect_eq rev_subsetD subsetI by auto 
            have subset14: "Scan T k'' (Gen (Prefixes p)) \<subseteq> items_le k (\<J> k' (Suc (Suc v'')))"
              using subset6 subset7 subset13 by blast
            then have x_in': "x \<in> \<pi> k {} (items_le k (\<J> k' (Suc (Suc v''))))"
              using x_in
              by (meson \<pi>_apply_setmonotone \<pi>_subset_elem_trans subsetCE subsetI)
            from x_in' have "x \<in> \<pi> k {} (natUnion (\<lambda> v. items_le k (\<J> k' v)))"
              by (meson k' mono_\<pi> mono_subset_elem natUnion_superset)
          }
          note suffices6 = this
          {
            fix v :: nat
            have "Gen (paths_eq k (\<P> k' v)) \<subseteq> \<pi> k {} (natUnion (\<lambda> v. items_le k (\<J> k' v)))"
              using suffices6 by (meson Gen_implies_pvalid subsetI) 
          }
          note suffices5 = this
          {
            fix v :: nat
            have "paths_le k (\<P> k' v) = paths_le k' (\<P> k' v) \<union> paths_eq k (\<P> k' v)"
              using  paths_le_split_via_eq k' by metis
            then have Gen_split: "Gen (paths_le k (\<P> k' v)) = 
              Gen (paths_le k' (\<P> k' v)) \<union> Gen(paths_eq k (\<P> k' v))" using Gen_union by metis
            have case_le: "Gen (paths_le k' (\<P> k' v)) \<subseteq>  \<pi> k {} (natUnion (\<lambda> v. items_le k (\<J> k' v)))"
            proof -
              from less k'_less_k have "k' \<le> length Doc" by arith
              from less(1)[OF k'_less_k this]
              have "items_le k' (\<J> k' v) = Gen (paths_le k' (\<P> k' v))" by blast
              then have "Gen (paths_le k' (\<P> k' v)) \<subseteq> natUnion (\<lambda> v. items_le k (\<J> k' v))"
                using items_le_def LocalLexing_axioms k'_less_k natUnion_superset by fastforce
              then show ?thesis using \<pi>_apply_setmonotone by blast
            qed
            have "Gen (paths_le k (\<P> k' v)) \<subseteq> \<pi> k {} (natUnion (\<lambda> v. items_le k (\<J> k' v)))"
              using Gen_split case_le suffices5 UnE rev_subsetD subsetI by blast 
          }
          note suffices4 = this
          have super_lemma: "Gen (paths_le k (\<P> k 0)) \<subseteq> items_le k (\<J> k 0)"
            apply (subst simp_right)
            apply (subst simp_left')
            using suffices4 by (meson natUnion_ex rev_subsetD subsetI) 
          from super_lemma sub_lemma show ?thesis by blast
        qed             
        then show ?case using thmD13 less.prems by blast   
    qed
qed

end

end
