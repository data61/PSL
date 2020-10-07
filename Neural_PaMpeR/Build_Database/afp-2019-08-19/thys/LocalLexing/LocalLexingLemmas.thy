theory LocalLexingLemmas
imports LocalLexing Limit
begin

context LocalLexing begin

lemma[simp]: "setmonotone (Append Z k)" by (auto simp add: Append_def setmonotone_def)

lemma subset_\<P>Suc: "\<P> k u \<subseteq> \<P> k (Suc u)"
  by (simp add: subset_setmonotone[OF setmonotone_limit])

lemma subset_fSuc_strict:
  assumes f: "\<And> u. f u \<subseteq> f (Suc u)"
  shows "u < v \<Longrightarrow> f u \<subseteq> f v"
proof (induct v)
  show "u < 0 \<Longrightarrow> f u \<subseteq> f 0"
    by auto
next
  fix v
  assume a:"(u < v \<Longrightarrow> f u \<subseteq> f v)"
  assume b:"u < Suc v"
  from b have c: "f u \<subseteq> f v"
    apply (case_tac "u < v")
    apply (simp add: a)
    apply (case_tac "u = v")
    apply simp
    by auto
  show "f u \<subseteq> f (Suc v)"
    apply (rule subset_trans[OF c])
    by (rule f)
qed

lemma subset_fSuc:
  assumes f: "\<And> u. f u \<subseteq> f (Suc u)"
  shows "u \<le> v \<Longrightarrow> f u \<subseteq> f v"
  apply (case_tac "u < v")
  apply (rule subset_fSuc_strict[where f=f, OF f])
  by auto

lemma subset_\<P>k: "u \<le> v \<Longrightarrow> \<P> k u \<subseteq> \<P> k v"
  by (rule subset_fSuc, rule subset_\<P>Suc) 
  
lemma subset_\<P>\<Q>k: "\<P> k u \<subseteq> \<Q> k" by (auto simp add: natUnion_def)

lemma subset_\<Q>\<P>Suc: "\<Q> k \<subseteq> \<P> (Suc k) u" 
proof -
  have a: "\<Q> k \<subseteq> \<P> (Suc k) 0" by simp
  show ?thesis 
    apply (case_tac "u = 0")
    apply (simp add: a)
    apply (rule subset_trans[OF a subset_\<P>k])
    by auto
qed

lemma subset_\<Q>Suc: "\<Q> k \<subseteq> \<Q> (Suc k)"
  by (rule subset_trans[OF subset_\<Q>\<P>Suc subset_\<P>\<Q>k])

lemma subset_\<Q>: "i \<le> j \<Longrightarrow> \<Q> i \<subseteq> \<Q> j"
  by (rule subset_fSuc[where u=i and v=j and f = \<Q>, OF subset_\<Q>Suc])

lemma empty_\<X>[simp]: "k > length Doc \<Longrightarrow> \<X> k = {}"
  apply (simp add: \<X>_def)
  apply (insert Lex_is_lexer)
  by (simp add: is_lexer_def)

lemma Sel_empty[simp]: "Sel {} {} = {}"
  apply (insert Sel_is_selector)
  by (auto simp add: is_selector_def)

lemma empty_\<Z>[simp]: "k > length Doc \<Longrightarrow> \<Z> k u = {}"
  apply (induct u)
  by (simp_all add: \<Y>_def \<W>_def)

lemma[simp]: "Append {} k = id" by (auto simp add: Append_def)

lemma[simp]: "k > length Doc \<Longrightarrow> \<P> k v = \<P> k 0"
  by (induct v, simp_all add: \<Y>_def \<W>_def)

lemma \<Q>SucEq: "k \<ge> length Doc \<Longrightarrow> \<Q> (Suc k) = \<Q> k"
  by (simp add: natUnion_def) 

lemma \<Q>_converges:
  assumes k: "k \<ge> length Doc"
  shows "\<Q> k = \<PP>"
proof -
  { 
    fix n
    have "\<Q> (length Doc + n) = \<PP>"
    proof (induct n)
      show "\<Q> (length Doc + 0) = \<PP>" by (simp add: \<PP>_def)
    next
      fix n
      assume hyp: "\<Q> (length Doc + n) = \<PP>"
      have "\<Q> (Suc (length Doc + n)) = \<PP>"
        by (rule trans[OF \<Q>SucEq hyp], auto)
      then show "\<Q> (length Doc + Suc n) = \<PP>"
        by auto
    qed
  }
  note helper = this
  from k have "\<exists> n. k = length Doc + n" by presburger
  then obtain "n" where n: "k = length Doc + n" by blast
  then show ?thesis
    apply (simp only: n)
    by (rule helper)
qed

lemma \<PP>_covers_\<Q>: "\<Q> k \<subseteq> \<PP>"
proof (case_tac "k \<ge> length Doc")
  assume "k \<ge> length Doc"
  then have \<Q>: "\<Q> k = \<PP>" by (rule \<Q>_converges)
  then show "\<Q> k \<subseteq> \<PP>" by (simp only: \<Q>)
next
  assume "\<not> length Doc \<le> k"
  then have "k < length Doc" by auto
  then show ?thesis
    apply (simp only: \<PP>_def)
    apply (rule subset_\<Q>)
    by auto
qed

lemma Sel_upper_bound: "A \<subseteq> B \<Longrightarrow> Sel A B \<subseteq> B"
  by (metis Sel_is_selector is_selector_def)

lemma Sel_lower_bound: "A \<subseteq> B \<Longrightarrow> A \<subseteq> Sel A B"
  by (metis Sel_is_selector is_selector_def)  

lemma \<PP>_covers_\<P>: "\<P> k u \<subseteq> \<PP>"
  by (rule subset_trans[OF subset_\<P>\<Q>k \<PP>_covers_\<Q>])

lemma \<W>_montone: "P \<subseteq> Q \<Longrightarrow> \<W> P k \<subseteq> \<W> Q k"
  by (auto simp add: \<W>_def)

lemma Sel_precondition: 
  "\<Z> k u \<subseteq> \<W> (\<P> k u) k"
proof (induct u)
  case 0 thus ?case by simp
next
  case (Suc u)
  have 1: "\<Y> (\<Z> k u) (\<P> k u) k \<subseteq> \<W> (\<P> k u) k"
    apply (simp add: \<Y>_def)
    apply (rule_tac Sel_upper_bound)
    using Suc by simp
  have 2: "\<W> (\<P> k u) k \<subseteq> \<W> (\<P> k (Suc u)) k"
    by (metis \<W>_montone subset_\<P>Suc)    
  show ?case
    apply (rule_tac subset_trans[where B="\<W> (\<P> k u) k"])
    apply (simp add: 1)
    apply (simp only: 2)
    done
qed    

lemma \<W>_bounded_by_\<X>: "\<W> P k \<subseteq> \<X> k"
  by (metis (no_types, lifting) \<W>_def mem_Collect_eq subsetI)

lemma \<Z>_subset_\<X>: "\<Z> k n \<subseteq> \<X> k"
  by (metis Sel_precondition \<W>_bounded_by_\<X> rev_subsetD subsetI)

lemma \<Z>_subset_Suc: "\<Z> k n \<subseteq> \<Z> k (Suc n)"
apply (induct n)
apply simp
by (metis Sel_lower_bound Sel_precondition \<Y>_def \<Z>.simps(2))

lemma \<Y>_upper_bound: "\<Y> (\<Z> k u) (\<P> k u) k \<subseteq> \<W>  (\<P> k u) k"
  apply (simp add: \<Y>_def)
  by (metis Sel_precondition Sel_upper_bound)

lemma \<PP>_induct[consumes 1, case_names Base Induct]:
  assumes p: "p \<in> \<PP>"
  assumes base: "P []"
  assumes induct: "\<And> p k u. (\<And> q. q \<in> \<P> k u \<Longrightarrow> P q) \<Longrightarrow> p \<in> \<P> k (Suc u) \<Longrightarrow> P p"
  shows "P p"
proof -
  {
    fix p :: "tokens"
    fix k :: nat
    fix u :: nat
    have "p \<in> \<P> k u \<Longrightarrow> P p"
    proof (induct k arbitrary: p u)
      case 0
        have "p \<in> \<P> 0 u \<Longrightarrow> P p"
        proof (induct u arbitrary: p)
          case 0 thus ?case using base by simp
        next
          case (Suc u) show ?case
            apply (rule induct[OF _ Suc(2)])
            apply (rule Suc(1))
            by simp
        qed
        with 0 show ?case by simp
    next
      case (Suc k)
        have "p \<in> \<P> (Suc k) u \<Longrightarrow> P p"
        proof (induct u arbitrary: p)
          case 0 thus ?case
            apply simp
            apply (induct rule: natUnion_decompose) 
            using Suc by simp
        next
          case (Suc u) show ?case
            apply (rule induct[OF _ Suc(2)])
            apply (rule Suc(1))
            by simp
        qed
        with Suc show ?case by simp
    qed 
  }
  note all = this
  from p show ?thesis
    apply (simp add: \<PP>_def)
    apply (induct rule: natUnion_decompose)
    using all by simp
qed 
    
lemma Append_mono: "U \<subseteq> V \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> Append U k P \<subseteq> Append V k Q"
  by (auto simp add: Append_def)

lemma pointwise_Append: "pointwise (Append T k)"
by (auto simp add: pointwise_def Append_def)

lemma regular_Append: "regular (Append T k)"
proof -
  have "pointwise (Append T k)" using pointwise_Append by blast
  then have "pointbased (Append T k)" using pointwise_implies_pointbased by blast
  then have "continuous (Append T k)" using pointbased_implies_continuous by blast 
  moreover have "setmonotone (Append T k)" by (simp add: setmonotone_def Append_def)
  ultimately show ?thesis using regular_def by blast
qed

end

end
