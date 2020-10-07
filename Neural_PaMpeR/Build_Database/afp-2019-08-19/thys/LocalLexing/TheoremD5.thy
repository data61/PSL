theory TheoremD5
imports TheoremD4
begin

context LocalLexing begin

lemma Scan_empty: "Scan {} k I = I"
  by (simp add: Scan_def)

lemma \<pi>_no_tokens: "\<pi> k {} I =  limit (\<lambda> I. Complete k (Predict k I)) I"
  by (simp add: \<pi>_def Scan_empty)

lemma bin_elem: "x \<in> bin I k \<Longrightarrow> x \<in> I"
  by (auto simp add: bin_def)

lemma Gen_implies_pvalid: "x \<in> Gen P \<Longrightarrow> \<exists> p \<in> P. pvalid p x"
  by (auto simp add: Gen_def)

lemma wellformed_init_item[simp]: "r \<in> \<RR> \<Longrightarrow> k \<le> length Doc \<Longrightarrow> wellformed_item (init_item r k)"
  by (simp add: init_item_def wellformed_item_def)

lemma init_item_origin[simp]: "item_origin (init_item r k) = k"
  by (auto simp add: item_origin_def init_item_def)

lemma init_item_end[simp]: "item_end (init_item r k) = k"
  by (auto simp add: item_end_def init_item_def)

lemma init_item_nonterminal[simp]: "item_nonterminal (init_item r k) = fst r"
  by (auto simp add: init_item_def item_nonterminal_def)

lemma init_item_\<alpha>[simp]: "item_\<alpha> (init_item r k) = []"
  by (auto simp add: init_item_def item_\<alpha>_def)

lemma Predict_elem_in_Gen:
  assumes I_in_Gen_P: "I \<subseteq> Gen P"
  assumes k: "k \<le> length Doc"
  assumes x_in_Predict: "x \<in> Predict k I"
  shows "x \<in> Gen P"
proof -
  have "x \<in> I \<or> (\<exists> r y. r \<in> \<RR> \<and> x = init_item r k \<and> y \<in> bin I k \<and> next_symbol y = Some(fst r))"
    using x_in_Predict by (auto simp add: Predict_def)
  then show ?thesis
  proof (induct rule: disjCases2)
    case 1 thus ?case using I_in_Gen_P by blast
  next
    case 2 
    then obtain r y where ry: "r \<in> \<RR> \<and> x = init_item r k \<and> y \<in> bin I k \<and> 
      next_symbol y = Some (fst r)" by blast
    then have "\<exists> p \<in> P. pvalid p y"
      using Gen_implies_pvalid I_in_Gen_P bin_elem subsetCE by blast 
    then obtain p where p: "p \<in> P \<and> pvalid p y" by blast
    have wellformed_p: "wellformed_tokens p" using p by (auto simp add: pvalid_def)
    have wellformed_x: "wellformed_item x"
      by (simp add: ry k)
    from ry have "item_end y = k" by (auto simp add: bin_def)
    with p have charslength_p[simplified]: "charslength p = k" by (auto simp add: pvalid_def)
    have item_end_x: "item_end x = k" by (simp add: ry)
    have pvalid_x: "pvalid p x"
      apply (auto simp add: pvalid_def)
      apply (simp add: wellformed_p)
      apply (simp add: wellformed_x)
      apply (rule_tac x="length p" in exI)
      apply (auto simp add: charslength_p ry)
      by (metis append_Cons next_symbol_starts_item_\<beta> p pvalid_def 
        pvalid_is_derivation_terminals_item_\<beta> ry)
    then show ?case using Gen_def mem_Collect_eq p by blast
 qed
qed

lemma Predict_subset_Gen:
  assumes "I \<subseteq> Gen P"
  assumes "k \<le> length Doc"
  shows "Predict k I \<subseteq> Gen P"
using Predict_elem_in_Gen assms by blast

lemma nth_superfluous_append[simp]: "i < length a \<Longrightarrow> (a@b)!i = a!i"
by (simp add: nth_append)

lemma tokens_nth_in_\<Z>: 
  "p \<in> \<PP> \<Longrightarrow> \<forall> i. i < length p \<longrightarrow> (\<exists> u. p ! i \<in> \<Z> (charslength (take i p)) u)"
proof (induct rule: \<PP>_induct)
  case Base thus ?case by simp
next
  case (Induct p k u)
  then have "p \<in> limit (Append (\<Z> k (Suc u)) k) (\<P> k u)" by simp
  then show ?case
  proof (induct rule: limit_induct)
    case (Init p) thus ?case using Induct by auto
  next
    case (Iterate p Y)
    from Iterate(2) have "p \<in> Y \<or> (\<exists> q t. p = q@[t] \<and> q \<in> by_length k Y \<and> t \<in> \<Z> k (Suc u) \<and> 
      admissible (q @ [t]))"
      by (auto simp add: Append_def)
    then show ?case
    proof (induct rule: disjCases2)
      case 1 thus ?case using Iterate(1) by auto
    next
      case 2 
      then obtain q t where 
        qt: "p = q @ [t] \<and> q \<in> by_length k Y \<and> t \<in> \<Z> k (Suc u) \<and> admissible (q @ [t])" by blast
      then have q_in_Y: "q \<in> Y" by auto
      with qt have k: "k = charslength q" by auto
      with qt have t: "t \<in> \<Z> k (Suc u)" by auto
      show ?case
      proof(auto simp add: qt)
        fix i
        assume i: "i < Suc (length q)"
        then have "i < length q \<or> i = length q" by arith
        then show "\<exists>u. (q @ [t]) ! i \<in> \<Z> (length (chars (take i q))) u"
        proof (induct rule: disjCases2)
          case 1
            from Iterate(1)[OF q_in_Y]
            show ?case by (simp add: 1)
        next
          case 2
            show ?case 
              apply (auto simp add: 2)
              apply (rule_tac x="Suc u" in exI)
              using k t by auto 
        qed
      qed
    qed
  qed
qed

lemma path_append_token:
  assumes p: "p \<in> \<P> k u"
  assumes t: "t \<in> \<Z> k (Suc u)"
  assumes pt: "admissible (p@[t])"
  assumes k: "charslength p = k"
  shows "p@[t] \<in> \<P> k (Suc u)"
apply (simp only: \<P>.simps)
apply (rule_tac n="Suc 0" in limit_elem)
using p t pt k apply (auto simp only: Append_def funpower.simps)
by fastforce

definition indexlt_rel :: "((nat \<times> nat) \<times> (nat \<times> nat)) set" where
  "indexlt_rel = less_than <*lex*> less_than"

definition indexlt :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "indexlt k' u' k u = (((k', u'), (k, u)) \<in> indexlt_rel)"

lemma indexlt_simp: "indexlt k' u' k u = (k' < k \<or> (k' = k \<and> u' < u))"
  by (auto simp add: indexlt_def indexlt_rel_def)

lemma wf_indexlt_rel: "wf indexlt_rel"
  using indexlt_rel_def pair_less_def by auto

lemma \<P>_induct[consumes 1, case_names Induct]:
  assumes "p \<in> \<P> k u"
  assumes induct: "\<And> p k u . (\<And> p' k' u'. p' \<in> \<P> k' u' \<Longrightarrow> indexlt k' u' k u \<Longrightarrow> P p' k' u') 
                     \<Longrightarrow> p \<in> \<P> k u \<Longrightarrow> P p k u"
  shows "P p k u"
proof -
  let ?R = "indexlt_rel <*lex*> {}"
  have wf_R: "wf ?R" by (auto simp add: wf_indexlt_rel)
  let ?P = "\<lambda> a. snd a \<in> \<P> (fst (fst a)) (snd (fst a)) \<longrightarrow> P (snd a) (fst (fst a)) (snd (fst a))"
  have "p \<in> \<P> k u \<longrightarrow> P p k u"
    apply (rule wf_induct[OF wf_R, where P = ?P and a = "((k, u), p)", simplified])
    apply (auto simp add: indexlt_def[symmetric])
    apply (rule_tac p=ba and k=a and u=b in induct)
    by auto
  thus ?thesis using assms by auto 
qed

lemma nonempty_path_indices: 
  assumes p: "p \<in> \<P> k u"
  assumes nonempty: "p \<noteq> []"
  shows "k > 0 \<or> u > 0"
proof (cases "u = 0")
  case True
  note u = True
  have "k > 0"
  proof (cases "k = 0")
    case True
    with p u have "p = []" by simp
    with nonempty have "False" by auto
    then show ?thesis by auto
  next
    case False
    then show ?thesis by arith
  qed
  then show ?thesis by blast
next
  case False
  then show ?thesis by arith
qed

lemma base_paths:
  assumes p: "p \<in> \<P> k 0"
  assumes k: "k > 0"
  shows "\<exists> u. p \<in> \<P> (k - 1) u"
proof -
  from k have "\<exists> i. k = Suc i" by arith
  then obtain i where i: "k = Suc i" by blast
  from p show ?thesis
    by (auto simp add: i natUnion_def)
qed

lemma indexlt_trans: "indexlt k'' u'' k' u' \<Longrightarrow> indexlt k' u' k u \<Longrightarrow> indexlt k'' u'' k u"
using dual_order.strict_trans indexlt_simp by auto

definition is_continuation :: "nat \<Rightarrow> nat \<Rightarrow> tokens \<Rightarrow> tokens \<Rightarrow> bool" where
  "is_continuation k u q ts = (q \<in> \<P> k u \<and> charslength q = k \<and> admissible (q@ts) \<and> 
     (\<forall> t \<in> set ts. t \<in> \<Z> k (Suc u)) \<and> (\<forall> t \<in> set (butlast ts). chars_of_token t = []))"

lemma limit_Append_path_nonelem_split: "p \<in> limit (Append T k) (\<P> k u) \<Longrightarrow> p \<notin> \<P> k u \<Longrightarrow>
  \<exists> q ts. p = q@ts \<and> q \<in> \<P> k u \<and> charslength q = k \<and> admissible (q@ts) \<and> (\<forall> t \<in> set ts. t \<in> T) \<and> 
    (\<forall> t \<in> set (butlast ts). chars_of_token t = [])"
proof (induct rule: limit_induct)
  case (Init p) thus ?case by auto
next
  case (Iterate p Y)
  show ?case
  proof (cases "p \<in> Y")
    case True
    from Iterate(1)[OF True Iterate(3)] show ?thesis by blast
  next
    case False
    with Append_def Iterate(2) 
    have "\<exists> q t. p = q@[t] \<and> q \<in> by_length k Y \<and> t \<in> T \<and> admissible (q @ [t])" by auto
    then obtain q t where qt: "p = q@[t] \<and> q \<in> by_length k Y \<and> t \<in> T \<and> admissible (q @ [t])" 
      by blast
    from qt have qlen: "charslength q = k" by auto
    have "q \<in> \<P> k u \<or> q \<notin> \<P> k u" by blast
    then show ?thesis
    proof(induct rule: disjCases2)
      case 1
      show ?case
        apply (rule_tac x=q in exI)
        apply (rule_tac x="[t]" in exI)
        using qlen by (simp add: qt 1)
    next
      case 2
      have q_in_Y: "q \<in> Y" using qt by auto
      from Iterate(1)[OF q_in_Y 2] 
      obtain q' ts where 
        q'ts: "q = q' @ ts \<and> q' \<in> \<P> k u \<and> charslength q' = k \<and> (\<forall>t\<in>set ts. t \<in> T) \<and>
               (\<forall>t\<in>set(butlast ts). chars_of_token t = [])"
        by blast
      with qlen have "charslength ts = 0" by auto
      hence empty: "\<forall> t \<in> set(ts). chars_of_token t = []" 
        apply (induct ts)
        by auto
      show ?case
        apply (rule_tac x=q' in exI)
        apply (rule_tac x="ts@[t]" in exI)
        using qt q'ts empty by auto
    qed
  qed
qed

lemma limit_Append_path_nonelem_split': 
  "p \<in> limit (Append (\<Z> k (Suc u)) k) (\<P> k u) \<Longrightarrow> p \<notin> \<P> k u \<Longrightarrow>
   \<exists> q ts. p = q@ts \<and> is_continuation k u q ts"
apply (simp only: is_continuation_def)
apply (rule_tac limit_Append_path_nonelem_split)
by auto

lemma final_step_of_path: "p \<in> \<P> k u \<Longrightarrow> p \<noteq> [] \<Longrightarrow> (\<exists> q ts k' u'. p = q@ts \<and> indexlt k' u' k u 
  \<and> is_continuation k' u' q ts)"
proof (induct rule: \<P>_induct)
  case (Induct p k u)
  from Induct(2) Induct(3) have ku_0: "k > 0 \<or> u > 0"
    using nonempty_path_indices by blast
  show ?case  
  proof (cases "u = 0")
    case True
    with ku_0 have k_0: "k > 0" by arith
    with True Induct(2) base_paths have "\<exists> u'. p \<in> \<P> (k - 1) u'" by auto
    then obtain u' where u': "p \<in> \<P> (k - 1) u'" by blast
    have indexlt: "indexlt (k - 1) u' k u" by (simp add: indexlt_simp k_0)
    from Induct(1)[OF u' indexlt Induct(3)] show ?thesis
      using indexlt indexlt_trans by blast
  next
    case False 
    then have "\<exists> u'. u = Suc u'" by arith
    then obtain u' where u': "u = Suc u'" by blast
    with Induct(2) have p_limit: "p \<in> limit (Append (\<Z> k (Suc u')) k) (\<P> k u')"
      using \<P>.simps(2) by blast
    from u' have indexlt: "indexlt k u' k u" by (simp add: indexlt_simp)
    have "p \<in> \<P> k u' \<or> p \<notin> \<P> k u'" by blast
    then show ?thesis
    proof (induct rule: disjCases2)
      case 1
      from Induct(1)[OF 1 indexlt Induct(3)] show ?case
        using indexlt indexlt_trans by blast
    next
      case 2
      from limit_Append_path_nonelem_split'[OF p_limit 2]
      show ?case using indexlt u' by auto
    qed
  qed
qed      

lemma terminals_empty[simp]: "terminals [] = []"
  by (auto simp add: terminals_def)

lemma empty_in_\<L>\<^sub>P[simp]: "[] \<in> \<L>\<^sub>P"
  apply (simp add: \<L>\<^sub>P_def is_derivation_def)
  apply (rule_tac x="[\<SS>]" in exI)
  by simp 
     
lemma admissible_empty[simp]: "admissible []"
  by (auto simp add: admissible_def)

lemma \<PP>_are_admissible: "p \<in> \<PP> \<Longrightarrow> admissible p"
proof (induct rule: \<PP>_induct)
  case Base thus ?case by simp
next
  case (Induct p k u)
  from Induct(2)[simplified] show ?case
  proof (induct rule: limit_induct)
    case (Init p) from Induct(1)[OF Init] show ?case .
  next
    case (Iterate p Y) 
    have "\<Y> (\<Z> k u) (\<P> k u) k \<subseteq> \<X> k" by (metis \<Z>.simps(2) \<Z>_subset_\<X>)
    then have 1: "Append (\<Y> (\<Z> k u) (\<P> k u) k) k Y \<subseteq> Append (\<X> k) k Y"
      by (rule Append_mono, simp) 
    have 2: "p \<in> Append (\<X> k) k Y \<Longrightarrow> admissible p"
      apply (auto simp add: Append_def)
      by (simp add: Iterate)
    show ?case 
      apply (rule 2)
      using "1" Iterate(2) by blast
  qed  
qed

lemma prefix_of_empty_is_empty: "is_prefix q [] \<Longrightarrow> q = []"
by (metis  is_prefix_cons neq_Nil_conv)

lemma subset_\<P> :
  assumes leq: "k' < k \<or> (k' = k \<and> u' \<le> u)"
  shows "\<P> k' u' \<subseteq> \<P> k u"
proof -
  from leq show ?thesis
  proof (induct rule: disjCases2)
    case 1
    have s1: "\<P> k' u' \<subseteq> \<Q> k'" by (rule_tac subset_\<P>\<Q>k) 
    have s2: "\<Q> k' \<subseteq> \<Q> (k - 1)" 
      apply (rule_tac subset_\<Q>)
      using 1 by arith
    from subset_\<Q>\<P>Suc[where k="k - 1"] 1 have s3: "\<Q> (k - 1) \<subseteq> \<P> k 0"
      by simp
    have s4: "\<P> k 0 \<subseteq> \<P> k u" by (rule_tac subset_\<P>k, simp)
    from s1 s2 s3 s4 subset_trans show ?case by blast
  next
    case 2 thus ?case by (simp add : subset_\<P>k)
  qed
qed  

lemma empty_path_is_elem[simp]: "[] \<in> \<P> k u"
proof -
  have "[] \<in> \<P> 0 0" by simp
  then show "[] \<in> \<P> k u" by (metis le0 not_gr0 subsetCE subset_\<P>) 
qed

lemma is_prefix_of_append:
  assumes "is_prefix p (a@b)"
  shows "is_prefix p a \<or> (\<exists> b'. b' \<noteq> [] \<and> is_prefix b' b \<and> p = a@b')"
apply (auto simp add: is_prefix_def) 
by (metis append_Nil2 append_eq_append_conv2 assms is_prefix_cancel is_prefix_def)

lemma prefix_is_continuation: "is_continuation k u p ts \<Longrightarrow> is_prefix ts' ts \<Longrightarrow> 
  is_continuation k u p ts'"
apply (auto simp add: is_continuation_def is_prefix_def)
apply (metis \<L>\<^sub>P_split admissible_def append_assoc terminals_append)
using in_set_butlast_appendI by fastforce 

lemma charslength_0: "(\<forall> t \<in> set ts. chars_of_token t = []) = (charslength ts = 0)"
by (induct ts, auto)
    
lemma is_continuation_in_\<P>: "is_continuation k u p ts \<Longrightarrow> p@ts \<in> \<P> k (Suc u)"
proof(induct ts rule: rev_induct)
  case Nil thus ?case 
    apply (auto simp add: is_continuation_def)
    using subset_\<P>Suc by fastforce
next
  case (snoc t ts)
  from snoc(2) have "is_continuation k u p ts"
    by (metis append_Nil2 is_prefix_cancel is_prefix_empty prefix_is_continuation)
  note induct = snoc(1)[OF this]
  then have pts: "p@ts \<in> limit (Append (\<Z> k (Suc u)) k) (\<P> k u)" by simp
  note is_cont = snoc(2)
  then have admissible: "admissible (p@ts@[t])" by (simp add: is_continuation_def)
  from is_cont have t: "t \<in> \<Z> k (Suc u)" by (simp add: is_continuation_def)
  from is_cont have "\<forall> t \<in> set ts. chars_of_token t = []" by (simp add: is_continuation_def)
  then have charslength_ts: "charslength ts = 0" by (simp only: charslength_0)
  from is_cont have plen: "charslength p = k" by (simp add: is_continuation_def)
  show ?case
    apply (simp only: \<P>.simps)
    apply (rule_tac limit_step_pointwise[OF pts])
    apply (simp add: pointwise_Append)
    apply (auto simp add: Append_def)
    apply (rule_tac x="fst t" in exI)
    apply (rule_tac x="snd t" in exI)
    apply (auto simp add: admissible)
    using charslength_ts apply simp
    using plen apply simp
    using t by simp
qed    

lemma indexlt_subset_\<P>: "indexlt k' u' k u \<Longrightarrow> \<P> k' (Suc u') \<subseteq> \<P> k u"
apply (rule_tac subset_\<P>)
apply (simp add: indexlt_simp)
apply arith
done

lemma prefixes_are_paths: "p \<in> \<P> k u \<Longrightarrow> is_prefix x p \<Longrightarrow> x \<in> \<P> k u"
proof (induct arbitrary: x rule: \<P>_induct)
  case (Induct p k u)
  show ?case
  proof (cases "p = []")
    case True
    then have "x = []"
      using Induct.prems prefix_of_empty_is_empty by blast 
    then show "x \<in> \<P> k u" by simp
  next
    case False
    from final_step_of_path[OF Induct(2) False]
    obtain q ts k' u' where step: "p = q@ts \<and> indexlt k' u' k u \<and> is_continuation k' u' q ts"
      by blast
    have subset: "\<P> k' u' \<subseteq> \<P> k u"
      by (metis indexlt_simp less_or_eq_imp_le step subset_\<P>)
    have "is_prefix x q \<or> (\<exists> ts'. ts' \<noteq> [] \<and> is_prefix ts' ts \<and> x = q@ts')"
      apply (rule_tac is_prefix_of_append)
      using Induct(3) step by auto
    then show ?thesis
    proof (induct rule: disjCases2)
      case 1
        have x: "x \<in> \<P> k' u'"
        using 1 Induct step by (auto simp add: is_continuation_def)
        then show "x \<in> \<P> k u" using subset subsetCE by blast
    next
      case 2
      then obtain ts' where ts': "is_prefix ts' ts \<and> x = q@ts'" by blast
      have "is_continuation k' u' q ts'" using step prefix_is_continuation ts' by blast 
      with ts' have "x \<in> \<P> k' (Suc u')"
        apply (simp only: ts')
        apply (rule_tac is_continuation_in_\<P>)
        by simp
      with subset show "x \<in> \<P> k u" using indexlt_subset_\<P> step by blast
    qed
  qed
qed  

lemma empty_or_last_of_suffix:
  assumes "q = q' @ [t]"
  assumes "q = p @ ts"
  shows "ts = [] \<or> (\<exists> ts'. q' = p @ ts' \<and> ts'@[t] = ts)"
by (metis assms(1) assms(2) butlast_append last_appendR snoc_eq_iff_butlast)

lemma is_prefix_butlast: "is_prefix q (butlast p) \<Longrightarrow> is_prefix q p"
by (metis butlast_conv_take is_prefix_append is_prefix_def is_prefix_take)
        
lemma last_step_of_path:
  "q \<in> \<P> k u \<Longrightarrow> q = q'@[t] \<Longrightarrow>
   \<exists> k' u'. indexlt k' u' k u \<and> q \<in> \<P> k' (Suc u') \<and> charslength q' = k' \<and> t \<in> \<Z> k' (Suc u')"
proof (induct arbitrary: q' t rule: \<P>_induct)
  case (Induct q k u)
    have "\<exists> p ts k' u'. q = p@ts \<and> indexlt k' u' k u \<and> is_continuation k' u' p ts"
      apply (rule_tac final_step_of_path)
      apply (simp add: Induct(2))
      apply (simp add: Induct(3))
      done
    then obtain p ts k' u' where pts: "q = p@ts \<and> indexlt k' u' k u \<and> is_continuation k' u' p ts"
      by blast
    then have indexlt: "indexlt k' u' k u" by auto
    from pts have "ts = [] \<or> (\<exists> ts'. q' = p @ ts' \<and> ts'@[t] = ts)"
      by (metis empty_or_last_of_suffix Induct(3))
    then show ?case
    proof (induct rule: disjCases2)
      case 1
        with pts have q: "q \<in> \<P> k' u'" by (auto simp add: is_continuation_def)
        from Induct(1)[OF this indexlt Induct(3)] show ?case
          using indexlt indexlt_trans by blast
    next
      case 2
        then obtain ts' where ts': "q' = p @ ts' \<and> ts'@[t] = ts" by blast
        then have "is_prefix ts' ts" using is_prefix_def by blast 
        then have "is_continuation k' u' p ts'" by (metis prefix_is_continuation pts)
        have "charslength ts' = 0" using charslength_0 is_continuation_def pts ts' by auto 
        then have q'len: "charslength q' = k'" using is_continuation_def pts ts' by auto 
        have "t \<in> set ts" using ts' by auto
        with pts have t_in_\<Z>: "t \<in> \<Z> k' (Suc u')" using is_continuation_def by blast 
        have q_dom: "q \<in> \<P> k' (Suc u')" using pts is_continuation_in_\<P> by blast
        show ?case  
          apply (rule_tac x=k' in exI)
          apply (rule_tac x=u' in exI)
          by (simp only: indexlt q'len t_in_\<Z> q_dom)
    qed
qed
      
lemma charslength_of_butlast_0: "p \<in> \<P> k 0 \<Longrightarrow> p = q@[t] \<Longrightarrow> charslength q < k"
using last_step_of_path LocalLexing_axioms indexlt_simp by blast

lemma charslength_of_butlast: "p \<in> \<P> k u \<Longrightarrow> p = q@[t] \<Longrightarrow> charslength q \<le> k"
by (metis indexlt_simp last_step_of_path eq_imp_le less_imp_le_nat)

lemma last_token_of_path:
  assumes "q \<in> \<P> k u"
  assumes "q = q'@[t]"
  assumes "charslength q' = k"
  shows "t \<in> \<Z> k u"
proof -
  from assms have "\<exists> k' u'. indexlt k' u' k u \<and> q \<in> \<P> k' (Suc u') \<and> charslength q' = k' \<and> 
    t \<in> \<Z> k' (Suc u')" using last_step_of_path by blast
  then obtain k' u' where th: "indexlt k' u' k u \<and> q \<in> \<P> k' (Suc u') \<and> charslength q' = k' \<and> 
    t \<in> \<Z> k' (Suc u')" by blast
  with assms(3) have k': "k' = k" by blast
  with th have "t \<in> \<Z> k' (Suc u') \<and> u' < u" using indexlt_simp by auto
  then show ?thesis
    by (metis (no_types, hide_lams) \<Z>_subset_Suc k' linorder_neqE_nat not_less_eq 
      subsetCE subset_fSuc_strict)
qed

lemma final_step_of_path': "p \<in> \<P> k u \<Longrightarrow> p \<notin> \<P> k (u - 1) \<Longrightarrow> 
  \<exists> q ts. u > 0 \<and> p = q@ts \<and> is_continuation k (u - 1) q ts"
by (metis Suc_diff_1 \<P>.simps(2) diff_0_eq_0 limit_Append_path_nonelem_split' not_gr0)

lemma is_continuation_continue:
  assumes "is_continuation k u q ts"
  assumes "charslength ts = 0"
  assumes "t \<in> \<Z> k (Suc u)"
  assumes "admissible (q @ ts @ [t])"
  shows "is_continuation k u q (ts@[t])"
proof -
  from assms show ?thesis
    by (simp add: is_continuation_def charslength_0)
qed

(* In an older version of local lexing, compatibility was an assumption we had to make, 
   but now it is a theorem *)

theorem compatibility_def:
  assumes p_in_dom: "p \<in> \<P> k u"
  assumes q_in_dom: "q \<in> \<P> k u"
  assumes p_charslength: "charslength p = k"
  assumes q_split: "q = q'@[t]"
  assumes q'len: "charslength q' = k"
  assumes admissible: "admissible (p @ [t])" 
  shows "p @ [t] \<in> \<P> k u"
proof - 
  have u: "u > 0"
  proof (cases "u = 0")
    case True
      then have "charslength q' < k" 
        using charslength_of_butlast_0 q_in_dom q_split by blast       
      with q'len have "False" by arith
      then show ?thesis by blast
  next
    case False
      then show ?thesis by arith
  qed
  have t_dom: "t \<in> \<Z> k u" using last_token_of_path q'len q_in_dom q_split by blast  
  have "p \<in> \<P> k (u - 1) \<or> p \<notin> \<P> k (u - 1)" by blast
  then show ?thesis
  proof (induct rule: disjCases2)
    case 1
      with t_dom p_charslength admissible u have "is_continuation k (u - 1) p [t]"
        by (auto simp add: is_continuation_def)
      with u show "p@[t] \<in> \<P> k u"
        by (metis One_nat_def Suc_pred is_continuation_in_\<P>)
  next
    case 2
      from final_step_of_path'[OF p_in_dom 2] 
      obtain p' ts where p': "p = p' @ ts \<and> is_continuation k (u - 1) p' ts"
        by blast
      from p' p_charslength is_continuation_def have charslength_ts: "charslength ts = 0"
        by auto
      from u have u': "Suc (u - 1) = u" by arith
      have "is_continuation k (u - 1) p' (ts@[t])"
        apply (rule_tac is_continuation_continue)
        using p' apply blast
        using charslength_ts apply blast
        apply (simp only: u' t_dom)
        using admissible p' apply auto
        done
      from is_continuation_in_\<P>[OF this] show ?case by (simp only: p' u', simp)
  qed
qed    

lemma is_prefix_admissible:
  assumes "is_prefix a b"
  assumes "admissible b"
  shows "admissible a"
proof -
  from assms show ?thesis
    by (auto simp add: is_prefix_def admissible_def \<L>\<^sub>P_def)
qed  

lemma butlast_split: "n < length q \<Longrightarrow> butlast q = (take n q)@(drop n (butlast q))"
by (metis append_take_drop_id take_butlast)

lemma in_\<P>_charslength:
  assumes p_dom: "p \<in> \<P> k u"
  shows "\<exists> v. p \<in> \<P> (charslength p) v"
proof (cases "charslength p \<ge> k")
  case True
    show ?thesis
      apply (rule_tac x=u in exI)
      by (metis True le_neq_implies_less p_dom subsetCE subset_\<P>)
next
  case False
    then have charslength: "charslength p < k" by arith
    have "p = [] \<or> p \<noteq> []" by blast
    thus ?thesis
    proof (induct rule: disjCases2)
      case 1 thus ?case by simp
    next
      case 2
        from final_step_of_path[OF p_dom 2] obtain q ts k' u' where
          step: "p = q @ ts \<and> indexlt k' u' k u \<and> is_continuation k' u' q ts" by blast
        from step have k': "charslength q = k'" using is_continuation_def by blast  
        from step have "charslength q \<le> charslength p"  by simp       
        with k' have k': "k' \<le> charslength p" by simp
        from step have "p \<in> \<P> k' (Suc u')" using is_continuation_in_\<P> by blast 
        with k' have "p \<in> \<P> (charslength p) (Suc u')"
          by (metis le_neq_implies_less subsetCE subset_\<P>) 
        then show ?case by blast
    qed
qed

theorem general_compatibility:
  "p \<in> \<P> k u \<Longrightarrow> q \<in> \<P> k u \<Longrightarrow> charslength p = charslength (take n q) 
    \<Longrightarrow> charslength p \<le> k \<Longrightarrow> admissible (p @ (drop n q)) \<Longrightarrow> p @ (drop n q) \<in> \<P> k u"
proof (induct "length q - n" arbitrary: p q n k u)
  case 0
    from 0 have "0 = length q - n" by auto
    then have n: "n \<ge> length q" by arith
    then have "drop n q = []" by auto
    then show ?case by (simp add: "0.prems"(1)) 
next
  case (Suc l)
    have "n \<ge> length q \<or> n < length q" by arith
    then show ?case
    proof (induct rule: disjCases2)
      case 1
        then have "drop n q = []" by auto
        then show ?case by (simp add: Suc.prems(1))
    next
      case 2
        then have "length q > 0" by auto
        then have q_nonempty: "q \<noteq> []" by auto
        let ?q' = "butlast q"
        from q_nonempty Suc(2) have h1: "l = length ?q' - n" by auto
        have h2: "?q' \<in> \<P> k u"
          by (metis Suc.prems(2) butlast_conv_take is_prefix_take prefixes_are_paths)
        have h3: "charslength p = charslength (take n ?q')"
          using "2.hyps" Suc.prems(3) take_butlast by force
        have "is_prefix (p @ drop n ?q') (p @ drop n q)"
          by (simp add: butlast_conv_take drop_take)
        note h4 = is_prefix_admissible[OF this Suc.prems(5)] 
        note induct = Suc(1)[OF h1 Suc(3) h2 h3 Suc.prems(4) h4] 
        let ?p' = "p @ (drop n (butlast q))"
        from induct have "?p' \<in> \<P> k u" .
        let ?i = "charslength ?p'"
        have charslength_i[symmetric]: "charslength ?q' = ?i"
          using Suc.prems(3) apply simp
          apply (subst butlast_split[OF 2])
          by simp
        have q_split: "q = ?q'@[last q]" by (simp add: q_nonempty)
        with Suc.prems(2) charslength_of_butlast have charslength_q': "charslength ?q' \<le> k" 
          by blast 
        from q_nonempty have p'last: "?p'@[last q] = p@(drop n q)"
          by (metis "2.hyps" append_assoc drop_eq_Nil drop_keep_last not_le q_split)
        have "?i \<le> k" by (simp only: charslength_i charslength_q')
        then have "?i = k \<or> ?i < k" by auto
        then show ?case
        proof (induct rule: disjCases2)
          case 1
            have charslength_q': "charslength ?q' = k" using charslength_i[symmetric] 1 by blast
            from compatibility_def[OF induct Suc.prems(2) 1 q_split charslength_q']
            show ?case by (simp only: p'last Suc.prems(5))
        next
          case 2
            from in_\<P>_charslength[OF induct]
            obtain v1 where v1: "?p' \<in> \<P> ?i v1" by blast 
            from last_step_of_path[OF Suc.prems(2) q_split] 
            have "\<exists> u. q \<in> \<P> ?i u" by (metis charslength_i)
            then obtain v2 where v2: "q \<in> \<P> ?i v2" by blast
            let ?v = "max v1 v2"
            have "v1 \<le> ?v" by auto
            with v1 have dom1: "?p' \<in> \<P> ?i ?v" by (metis (no_types, hide_lams) subsetCE subset_\<P>k) 
            have "v2 \<le> ?v" by auto
            with v2 have dom2: "q \<in> \<P> ?i ?v" by (metis (no_types, hide_lams) subsetCE subset_\<P>k) 
            from compatibility_def[OF dom1 dom2 _ q_split] 
            have "p @ drop n q \<in> \<P> ?i ?v"
              by (simp only: p'last charslength_i[symmetric] Suc.prems(5))
            then show "p @ drop n q \<in> \<P> k u" by (meson "2.hyps" subsetCE subset_\<P>) 
        qed                                                          
    qed        
qed

lemma wellformed_item_derives:
  assumes wellformed: "wellformed_item x"
  shows "derives [item_nonterminal x] (item_rhs x)"
proof -
  from wellformed have "(item_nonterminal x, item_rhs x) \<in> \<RR>"
    by (simp add: item_nonterminal_def item_rhs_def wellformed_item_def)
  then show ?thesis
    by (metis append_Nil2 derives1_def derives1_implies_derives is_sentence_concat 
        rule_\<alpha>_type self_append_conv2)
qed      

lemma wellformed_complete_item_\<beta>:
  assumes wellformed: "wellformed_item x"
  assumes complete: "is_complete x" 
  shows "item_\<beta> x = []"
using complete is_complete_def item_\<beta>_def by auto

lemma wellformed_complete_item_derives:
  assumes wellformed: "wellformed_item x"
  assumes complete: "is_complete x" 
  shows "derives [item_nonterminal x] (item_\<alpha> x)"
using complete is_complete_def item_\<alpha>_def wellformed wellformed_item_derives by auto 

lemma is_derivation_implies_admissible:
  "is_derivation (terminals p @ \<delta>) \<Longrightarrow> is_word (terminals p) \<Longrightarrow> admissible p"
using \<L>\<^sub>P_def admissible_def by blast

lemma item_rhs_of_inc_item[simp]: "item_rhs (inc_item x k) = item_rhs x"
  by (auto simp add: inc_item_def item_rhs_def)

lemma item_rule_of_inc_item[simp]: "item_rule (inc_item x k) = item_rule x"
  by (simp add: inc_item_def)

lemma item_origin_of_inc_item[simp]: "item_origin (inc_item x k) = item_origin x"
  by (simp add: inc_item_def)

lemma item_end_of_inc_item[simp]: "item_end (inc_item x k) = k"
  by (simp add: inc_item_def)

lemma item_dot_of_inc_item[simp]: "item_dot (inc_item x k) = (item_dot x) + 1"
  by (simp add: inc_item_def)

lemma item_nonterminal_of_inc_item[simp]: "item_nonterminal (inc_item x k) = item_nonterminal x"
  by (simp add: inc_item_def item_nonterminal_def)

lemma wellformed_inc_item:
  assumes wellformed: "wellformed_item x"
  assumes next_symbol: "next_symbol x = Some s"
  assumes k_upper_bound: "k \<le> length Doc"
  assumes k_lower_bound: "k \<ge> item_end x"
  shows "wellformed_item (inc_item x k)"
proof -
  have k_lower_bound': "k \<ge> item_origin x"
    using k_lower_bound wellformed wellformed_item_def by auto  
  show ?thesis
    apply (auto simp add: wellformed_item_def k_upper_bound k_lower_bound')
    using wellformed wellformed_item_def apply blast
    using is_complete_def next_symbol next_symbol_not_complete not_less_eq_eq by blast
qed    

lemma item_\<alpha>_of_inc_item:
  assumes wellformed: "wellformed_item x"
  assumes next_symbol: "next_symbol x = Some s"
  shows "item_\<alpha> (inc_item x k) = item_\<alpha> x @ [s]"
by (metis (mono_tags, lifting) item_dot_of_inc_item item_rhs_of_inc_item 
  One_nat_def add.right_neutral add_Suc_right is_complete_def item_\<alpha>_def item_\<beta>_def 
  le_neq_implies_less list.sel(1) next_symbol next_symbol_not_complete next_symbol_starts_item_\<beta> 
  take_hd_drop wellformed wellformed_item_def)

lemma derives1_pad: 
  assumes derives1: "derives1 \<alpha> \<beta>"
  assumes u: "is_sentence u"
  assumes v: "is_sentence v"
  shows "derives1 (u@\<alpha>@v) (u@\<beta>@v)"
proof -
  from derives1 have 
   "\<exists>x y N \<delta>. \<alpha> = x @ [N] @ y \<and> \<beta> = x @ \<delta> @ y \<and> is_sentence x \<and> is_sentence y \<and> (N, \<delta>) \<in> \<RR>"
   by (auto simp add: derives1_def)
  then obtain x y N \<delta> where 
   1: "\<alpha> = x @ [N] @ y \<and> \<beta> = x @ \<delta> @ y \<and> is_sentence x \<and> is_sentence y \<and> (N, \<delta>) \<in> \<RR>" by blast
  show ?thesis
    apply (simp only: derives1_def)
    apply (rule_tac x="u@x" in exI)
    apply (rule_tac x="y@v" in exI)
    apply (rule_tac x=N in exI)
    apply (rule_tac x=\<delta> in exI)
    using 1 u v is_sentence_concat by auto
qed

lemma derives_pad:
  "derives \<alpha> \<beta> \<Longrightarrow> is_sentence u \<Longrightarrow> is_sentence v \<Longrightarrow> derives (u@\<alpha>@v) (u@\<beta>@v)"
proof (induct rule: derives_induct)
  case Base thus ?case by simp
next
  case (Step y z) 
    from Step have 1: "derives (u@\<alpha>@v) (u@y@v)" by auto
    from Step have 2: "derives1 y z" by auto
    then have "derives1 (u@y@v) (u@z@v)" by (simp add: Step.prems derives1_pad)    
    then show ?case
      using "1" derives1_implies_derives derives_trans by blast
qed  

lemma derives1_is_sentence: "derives1 \<alpha> \<beta> \<Longrightarrow> is_sentence \<alpha> \<and> is_sentence \<beta>"
using Derives1_sentence1 Derives1_sentence2 derives1_implies_Derives1 by blast

lemma derives_is_sentence: "derives \<alpha> \<beta> \<Longrightarrow> (\<alpha> = \<beta>) \<or> (is_sentence \<alpha> \<and> is_sentence \<beta>)"
proof (induct rule: derives_induct)
  case Base thus ?case by simp
next
  case (Step y z) 
    show ?case using Step.hyps(2) Step.hyps(3) derives1_is_sentence by blast
qed

lemma derives_append: 
  assumes au: "derives a u"
  assumes bv: "derives b v"
  assumes is_sentence_a: "is_sentence a"
  assumes is_sentence_b: "is_sentence b"
  shows "derives (a@b) (u@v)"
proof -
  from au have "a = u \<or> (is_sentence a \<and> is_sentence u)"
    using derives_is_sentence by blast
  then have au_sentences: "is_sentence a \<and> is_sentence u" using is_sentence_a by blast 
  from bv have "b = v \<or> (is_sentence b \<and> is_sentence v)"
    using derives_is_sentence by blast
  then have bv_sentences: "is_sentence b \<and> is_sentence v" using is_sentence_b by blast 
  have 1: "derives (a@b) (u@b)"
    apply (rule_tac derives_pad[OF au, where u="[]", simplified])
    using is_sentence_b by auto
  have 2: "derives (u@b) (u@v)"
    apply (rule_tac derives_pad[OF bv, where v="[]", simplified])
    apply (simp add: au_sentences)
    done
  from 1 2 derives_trans show ?thesis by blast
qed  

lemma is_sentence_item_\<alpha>: "wellformed_item x \<Longrightarrow> is_sentence (item_\<alpha> x)"
  by (metis is_sentence_take item_\<alpha>_def item_rhs_def prod.collapse rule_\<alpha>_type wellformed_item_def)

lemma is_nonterminal_item_nonterminal:  "wellformed_item x \<Longrightarrow> is_nonterminal (item_nonterminal x)"
  by (metis item_nonterminal_def prod.collapse rule_nonterminal_type wellformed_item_def)
  
lemma Complete_elem_in_Gen:
  assumes I_in_Gen: "I \<subseteq> Gen (\<P> k u)"
  assumes k: "k \<le> length Doc"
  assumes x_in_Complete: "x \<in> Complete k I"
  shows "x \<in> Gen (\<P> k u)"
proof -
  let ?P = "\<P> k u"
  from x_in_Complete have "x \<in> I \<or> (\<exists> x1 x2. x = inc_item x1 k \<and> 
     x1 \<in> bin I (item_origin x2) \<and> x2 \<in> bin I k \<and> is_complete x2 \<and> 
     next_symbol x1 = Some (item_nonterminal x2))"
     by (auto simp add: Complete_def)
  then show ?thesis
  proof (induct rule: disjCases2)
    case 1 thus ?case using I_in_Gen subsetCE by blast 
  next
    case 2 
    then obtain x1 x2 where x12: "x = inc_item x1 k \<and> 
      x1 \<in> bin I (item_origin x2) \<and> x2 \<in> bin I k \<and> is_complete x2 \<and> 
      next_symbol x1 = Some (item_nonterminal x2)" by blast
    from x12 have "\<exists> p1 p2. p1 \<in> ?P \<and> pvalid p1 x1 \<and> p2 \<in> ?P \<and> pvalid p2 x2"
      by (meson Gen_implies_pvalid I_in_Gen bin_elem subsetCE)
    then obtain p1 p2 where p1: "p1 \<in> ?P \<and> pvalid p1 x1" and p2: "p2 \<in> ?P \<and> pvalid p2 x2"
      by blast
    from p1 obtain w \<delta> where p1valid:
      "wellformed_tokens p1 \<and>
       wellformed_item x1 \<and>
       w \<le> length p1 \<and>
       charslength p1 = item_end x1 \<and>
       charslength (take w p1) = item_origin x1 \<and>
       is_derivation (terminals (take w p1) @ [item_nonterminal x1] @ \<delta>) \<and>
       derives (item_\<alpha> x1) (terminals (drop w p1))"
       using pvalid_def by blast
    from p2 obtain y \<gamma> where p2valid:
      "wellformed_tokens p2 \<and>
       wellformed_item x2 \<and>
       y \<le> length p2 \<and>
       charslength p2 = item_end x2 \<and>
       charslength (take y p2) = item_origin x2 \<and>
       is_derivation (terminals (take y p2) @ [item_nonterminal x2] @ \<gamma>) \<and>
       derives (item_\<alpha> x2) (terminals (drop y p2))"
       using pvalid_def by blast
    let ?r = "p1 @ (drop y p2)"
    have charslength_p1_eq: "charslength p1 = item_end x1" by (simp only: p1valid)
    from x12 have item_end_x1: "item_end x1 = item_origin x2" 
      using bin_def mem_Collect_eq by blast
    have item_end_x2: "item_end x2 = k" using bin_def x12 by blast 
    then have charslength_p1_leq: "charslength p1 \<le> k"
      using charslength_p1_eq item_end_x1 p2valid wellformed_item_def by auto 
    have "\<exists>\<delta>'. item_\<beta> x1 = [item_nonterminal x2] @ \<delta>'"
      by (simp add: next_symbol_starts_item_\<beta> p1valid x12)  
    then obtain \<delta>' where \<delta>': "item_\<beta> x1 = [item_nonterminal x2] @ \<delta>'" by blast
    have "is_derivation ((terminals (take w p1))@(item_rhs x1)@\<delta>)"
      using is_derivation_derives p1valid wellformed_item_derives by blast
    then have "is_derivation ((terminals (take w p1))@(item_\<alpha> x1 @ item_\<beta> x1)@\<delta>)"
       by (simp add: item_rhs_split)
    then have "is_derivation ((terminals (take w p1))@((terminals (drop w p1)) @ item_\<beta> x1)@\<delta>)"
      using is_derivation_derives p1valid by auto
    then have "is_derivation ((terminals p1)@(item_\<beta> x1)@\<delta>)"
      by (metis append_assoc append_take_drop_id terminals_append)
    then have "is_derivation ((terminals p1)@([item_nonterminal x2] @ \<delta>')@\<delta>)"
      using is_derivation_derives \<delta>' by auto
    then have "is_derivation ((terminals p1)@(terminals (drop y p2)) @ \<delta>' @\<delta>)"
      using is_complete_def is_derivation_derives is_derivation_step item_\<alpha>_def 
        item_nonterminal_def item_rhs_def p2valid wellformed_item_def x12 by auto
    then have "is_derivation (terminals (p1 @ (drop y p2)) @ (\<delta>' @ \<delta>))" by simp
    then have admissible_r: "admissible (p1 @ (drop y p2))"
      apply (rule_tac is_derivation_implies_admissible)
      apply auto
      apply (rule is_word_terminals)
      apply (simp add: p1valid)
      using p2valid using is_word_terminals_drop terminals_drop by auto 
    have r_in_dom: "?r \<in> \<P> k u"
      apply (rule_tac general_compatibility)
      apply (simp add: p1)
      apply (simp add: p2)
      apply (simp only: p2valid charslength_p1_eq item_end_x1)
      apply (simp only: charslength_p1_leq)
      by (simp add: admissible_r)
    have wellformed_r: "wellformed_tokens ?r" 
      using admissible_r admissible_wellformed_tokens by blast 
    have wellformed_x: "wellformed_item x"
      apply (simp add: x12)
      apply (rule_tac wellformed_inc_item)
      apply (simp add: p1valid)
      apply (simp add: x12)
      apply (simp add: k)
      using charslength_p1_eq charslength_p1_leq by auto
    have charslength_p1_as_p2: "charslength p1 = charslength (take y p2)"
      using charslength_p1_eq item_end_x1 p2valid by linarith     
    then have charslength_r: "charslength ?r = item_end x"
      apply (simp add: x12)
      apply (subst length_append[symmetric])
      apply (subst chars_append[symmetric])
      apply (subst append_take_drop_id)
      using item_end_x2 p2valid by auto
    have item_\<alpha>_x: "item_\<alpha> x = item_\<alpha> x1 @ [item_nonterminal x2]"
      using x12 p1valid by (simp add: item_\<alpha>_of_inc_item)
    from p2valid have derives_item_nonterminal_x2:
      "derives [item_nonterminal x2] (terminals (drop y p2))"
      using derives_trans wellformed_complete_item_derives x12 by blast
    have "pvalid ?r x"
      apply (auto simp only: pvalid_def)
      apply (rule_tac x=w in exI)
      apply (rule_tac x=\<delta> in exI)
      apply (auto simp only:)
      apply (simp add: wellformed_r)
      apply (simp add: wellformed_x)
      using p1valid apply simp
      apply (simp only: charslength_r)
      using x12 p1valid apply simp
      using x12 p1valid apply simp
      apply (simp add:  item_\<alpha>_x)
      apply (rule_tac derives_append)
      using p1valid apply simp
      using derives_item_nonterminal_x2 p1valid apply auto[1]
      using is_sentence_item_\<alpha> p1valid apply blast
      using is_derivation_is_sentence is_sentence_concat p2valid by blast
    with r_in_dom show ?case using Gen_def mem_Collect_eq by blast
  qed
qed

lemma Complete_subset_Gen:
  assumes I_in_Gen_P: "I \<subseteq> Gen (\<P> k u)"
  assumes k: "k \<le> length Doc"
  shows "Complete k I \<subseteq> Gen (\<P> k u)"
using Complete_elem_in_Gen I_in_Gen_P k by blast

lemma \<P>_are_admissible: "p \<in> \<P> k u \<Longrightarrow> admissible p"
apply (rule_tac \<PP>_are_admissible)
using \<PP>_covers_\<P> subsetCE by blast

lemma is_continuation_base:
  assumes p_dom: "p \<in> \<P> k u"
  assumes charslength_p: "charslength p = k"
  shows "is_continuation k u p []"
apply (auto simp add: is_continuation_def)
apply (simp add: p_dom)
using charslength_p apply simp
using \<P>_are_admissible p_dom by blast

lemma is_continuation_empty_chars: 
  "is_continuation k u q ts \<Longrightarrow> charslength (q@ts) = k \<Longrightarrow> chars ts = []"
by (simp add: is_continuation_def)

lemma \<Z>_subset: "u \<le> v \<Longrightarrow> \<Z> k u \<subseteq> \<Z> k v"
using \<Z>_subset_Suc subset_fSuc by blast

lemma is_continuation_increase_u:
  assumes cont: "is_continuation k u q ts"
  assumes uv: "u \<le> v"
  shows "is_continuation k v q ts"
proof -
  have "q \<in> \<P> k u" using cont is_continuation_def by blast
  with uv have q_dom: "q \<in> \<P> k v" by (meson subsetCE subset_\<P>k) 
  from uv have \<Z>: "\<And> t. t \<in> \<Z> k (Suc u) \<Longrightarrow> t \<in> \<Z> k (Suc v)"
    using \<Z>_subset le_neq_implies_less less_imp_le_nat not_less_eq subsetCE by blast  
  show ?thesis
    apply (auto simp only: is_continuation_def)
    apply (simp add: q_dom)
    using cont is_continuation_def apply simp
    using cont is_continuation_def apply simp
    using cont is_continuation_def \<Z> apply simp
    using cont is_continuation_def apply (simp only:)
    done
qed

lemma pvalid_next_symbol_derivable:
  assumes pvalid: "pvalid p x" 
  assumes next_symbol: "next_symbol x = Some s"
  shows "\<exists> \<delta>. is_derivation((terminals p)@[s]@\<delta>)"
proof -
  from pvalid pvalid_def have wellformed_x: "wellformed_item x" by auto
  from next_symbol_starts_item_\<beta>[OF wellformed_x next_symbol]
  obtain \<omega> where \<omega>: "item_\<beta> x = [s] @ \<omega>" by auto
  from pvalid have "\<exists> \<gamma>. is_derivation((terminals p)@(item_\<beta> x)@\<gamma>)"
    using pvalid_is_derivation_terminals_item_\<beta> by blast
  then obtain \<gamma> where "is_derivation((terminals p)@(item_\<beta> x)@\<gamma>)" by blast
  with \<omega> have "is_derivation((terminals p)@[s]@\<omega>@\<gamma>)" by auto
  then show ?thesis by blast
qed

lemma pvalid_admissible: 
  assumes pvalid: "pvalid p x" 
  shows "admissible p"
proof -
  have "\<exists> \<delta>. is_derivation((terminals p)@(item_\<beta> x)@\<delta>)"
    by (simp add: pvalid pvalid_is_derivation_terminals_item_\<beta>)
  then obtain \<delta> where \<delta>: "is_derivation((terminals p)@(item_\<beta> x)@\<delta>)" by blast
  have is_word: "is_word (terminals p)"
    using pvalid_def is_word_terminals pvalid by blast 
  show ?thesis using \<delta> is_derivation_implies_admissible is_word by blast
qed 

lemma pvalid_next_terminal_admissible:
  assumes pvalid: "pvalid p x" 
  assumes next_symbol: "next_symbol x = Some t"
  assumes terminal: "is_terminal t"
  shows "admissible (p@[(t, c)])"
proof -
  have "is_word (terminals p)"
    using is_word_terminals pvalid pvalid_def by blast
  then show ?thesis
    using is_derivation_implies_admissible next_symbol pvalid pvalid_next_symbol_derivable 
      terminal by fastforce
qed

lemma \<X>_wellformed: "t \<in> \<X> k \<Longrightarrow> wellformed_token t"
  by (simp add: \<X>_are_terminals wellformed_token_def)

lemma \<Z>_wellformed: "t \<in> \<Z> k u \<Longrightarrow> wellformed_token t"
  using \<X>_wellformed \<Z>_subset_\<X> by blast
 
lemma Scan_elem_in_Gen:
  assumes I_in_Gen: "I \<subseteq> Gen (\<P> k u)"
  assumes k: "k \<le> length Doc"
  assumes T: "T \<subseteq> \<Z> k u"
  assumes x_in_Scan: "x \<in> Scan T k I"
  shows "x \<in> Gen (\<P> k u)"
proof -
  have "u = 0 \<Longrightarrow> x \<in> I" 
  proof -
    assume "u = 0"
    then have "\<Z> k u = {}" by simp
    then have "T = {}" using T by blast
    then have "Scan T k I = I" by (simp add: Scan_empty)
    then show "x \<in> I" using x_in_Scan by simp
  qed
  then have "x \<in> I \<or> (u > 0 \<and> (\<exists> y t c. x = inc_item y (k + length c) \<and> y \<in> bin I k \<and> 
    (t, c) \<in> T \<and> next_symbol y = Some t))" using x_in_Scan Scan_def by auto
  then show ?thesis
  proof (induct rule: disjCases2)
    case 1 thus ?case using I_in_Gen by blast
  next
    case 2 
    then obtain y t c where x_is_scan: "x = inc_item y (k + length c) \<and> y \<in> bin I k \<and> 
       (t, c) \<in> T \<and> next_symbol y = Some t" by blast
    have u_gt_0: "0 < u" using 2 by blast
    have "\<exists> p \<in> \<P> k u. pvalid p y" using Gen_implies_pvalid I_in_Gen bin_elem x_is_scan by blast 
    then obtain p where p: "p \<in> \<P> k u \<and> pvalid p y" by blast
    have p_dom: "p \<in> \<P> k u" using p by blast
    from p pvalid_def x_is_scan have charslength_p: "charslength p = k"
      using bin_def mem_Collect_eq by auto 
    obtain tok where tok: "tok = (t, c)" using x_is_scan by blast
    have tok_dom: "tok \<in> \<Z> k u" using tok x_is_scan T by blast
    have "p = [] \<or> p \<noteq> []" by blast
    then have "\<exists> q ts u'. p = q@ts \<and> u' < u \<and> charslength ts = 0 \<and> is_continuation k u' q ts"
    proof (induct rule: disjCases2)
      case 1 thus ?case
        apply (rule_tac x=p in exI)
        apply (rule_tac x="[]" in exI)
        apply (rule_tac x="0" in exI)
        apply (simp add: 2 is_continuation_def)
        using charslength_p by simp
    next
      case 2
      from final_step_of_path[OF p_dom 2] obtain q ts k' u'
        where final_step: "p = q @ ts \<and> indexlt k' u' k u \<and> is_continuation k' u' q ts" by blast
      then have "k' \<le> k" using indexlt_simp by auto 
      then have "k' < k \<or> k' = k" by arith
      then show ?case
      proof (induct rule: disjCases2)
        case 1 
        have "p \<in> \<P> k' (Suc u')" using final_step is_continuation_in_\<P> by blast 
        then have p_dom: "p \<in> \<P> k 0" by (meson 1 subsetCE subset_\<P>) 
        with charslength_p have "is_continuation k 0 p []" using is_continuation_base by blast 
        then show ?case
          apply (rule_tac x=p in exI)
          apply (rule_tac x="[]" in exI)
          apply (rule_tac x="0" in exI)
          apply (simp add: u_gt_0)
          done
      next
        case 2
        with final_step indexlt_simp have "u' < u" by auto
        then show ?case
          apply (rule_tac x=q in exI)
          apply (rule_tac x=ts in exI)
          apply (rule_tac x=u' in exI)
          using final_step 2 apply auto
          using charslength_p is_continuation_empty_chars by blast
      qed
    qed
    then obtain q ts u' where 
      p_split: "p = q@ts \<and> u' < u \<and> charslength ts = 0 \<and> is_continuation k u' q ts" by blast
    then have "\<exists> u''. u' \<le> u'' \<and> Suc u'' = u" by (auto, arith)
    then obtain u'' where u'': " u' \<le> u'' \<and> Suc u'' = u" by blast
    with p_split have cont_u'': "is_continuation k u'' q ts" 
      using is_continuation_increase_u by blast 
    have admissible: "admissible (p@[tok])"
      apply (simp add: tok)
      apply (rule_tac pvalid_next_terminal_admissible[where x=y])
      apply (simp add: p)
      apply (simp add: x_is_scan)
      using \<Z>_wellformed tok tok_dom wellformed_token_def by auto 
    have "is_continuation k u'' q (ts@[tok])"
      apply (rule is_continuation_continue)
      apply (simp add: cont_u'')
      using p_split apply simp
      using u'' tok_dom apply simp
      using admissible p_split by auto
    with p_split u'' have ptok_dom: "p@[tok] \<in> \<P> k u" 
      using append_assoc is_continuation_in_\<P> by auto 
    from p obtain i \<gamma> where valid:
      "wellformed_tokens p \<and>
       wellformed_item y \<and>
       i \<le> length p \<and>
       charslength p = item_end y \<and>
       charslength (take i p) = item_origin y \<and>
       is_derivation (terminals (take i p) @ [item_nonterminal y] @ \<gamma>) \<and>
       derives (item_\<alpha> y) (terminals (drop i p))" using pvalid_def by blast 
    have clen_ptok: "k + length c = charslength (p@[tok])"
      using charslength_p tok by simp
    from ptok_dom have ptok_doc_tokens: "doc_tokens (p@[tok])"
      using \<PP>_are_doc_tokens \<PP>_covers_\<P> rev_subsetD by blast
    have wellformed_x: "wellformed_item x"
      apply (simp add: x_is_scan)
      apply (rule_tac wellformed_inc_item)
      apply (simp add: valid)
      apply (simp add: x_is_scan)
      apply (simp only: clen_ptok) 
      using ptok_doc_tokens charslength.simps doc_tokens_length apply presburger 
      apply (simp only: clen_ptok)
      using valid by auto
    have "pvalid (p@[tok]) x"
      apply (auto simp only: pvalid_def)
      apply (rule_tac x=i in exI)
      apply (rule_tac x=\<gamma> in exI)
      apply (auto simp only:)
      using ptok_dom admissible admissible_wellformed_tokens apply blast 
      apply (simp add: wellformed_x)
      using valid apply simp
      apply (simp add: x_is_scan clen_ptok)
      using valid apply (simp add: x_is_scan)
      using valid apply (simp add: x_is_scan)
      using valid apply (simp add: x_is_scan)
      apply (subst item_\<alpha>_of_inc_item)
      using valid apply simp
      using x_is_scan apply simp
      apply (rule_tac derives_append)
      apply simp
      apply (simp add: tok)
      using is_sentence_item_\<alpha> apply blast
      by (meson pvalid_next_symbol_derivable LocalLexing_axioms is_derivation_is_sentence 
          is_sentence_concat p x_is_scan)
    with ptok_dom show ?thesis
      using Gen_def mem_Collect_eq by blast
  qed
qed

lemma Scan_subset_Gen:
  assumes I_in_Gen: "I \<subseteq> Gen (\<P> k u)"
  assumes k: "k \<le> length Doc"
  assumes T: "T \<subseteq> \<Z> k u"
  shows "Scan T k I \<subseteq> Gen (\<P> k u)"
using I_in_Gen Scan_elem_in_Gen T k by blast

theorem thmD5:
  assumes I: "I \<subseteq> Gen (\<P> k u)"
  assumes k: "k \<le> length Doc"
  assumes T: "T \<subseteq> \<Z> k u"
  shows "\<pi> k T I \<subseteq> Gen (\<P> k u)"
apply (simp add: \<pi>_def)
apply (rule_tac limit_upperbound)
using I k T Predict_subset_Gen Complete_subset_Gen Scan_subset_Gen apply metis
by (simp add: I)

end

end
