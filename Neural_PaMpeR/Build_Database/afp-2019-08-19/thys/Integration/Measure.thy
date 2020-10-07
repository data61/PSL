subsection \<open>Measure spaces \label{sec:measure-spaces}\<close>

theory Measure
imports Sigma_Algebra MonConv
begin

(*We use a modified version of the simple Sigma_Algebra Theory by
Markus Wenzel here,
  which does not need an explicit definition of countable,
  changing the names according to Joe Hurd*)
text \<open>Now we are already set for the central concept of
  measure. The following definitions are translated as faithfully as possible
  from those in Joe Hurd's thesis \cite{hurd2002}.\<close>

definition
  measurable:: "'a set set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "measurable F G = {f. \<forall>g\<in>G. f -` g \<in> F}"

text \<open>So a function is called $F$-$G$-measurable if and only if the inverse
  image of any set in $G$ is in $F$. $F$ and $G$ are usually the sets of
  measurable sets, the first component of a measure space\footnote{In
  standard mathematical notation, the universe is first in a
  measure space triple, but in our definitions, following Joe Hurd, it is always the
  whole type universe and therefore omitted.}.\<close>


definition
  measurable_sets:: "('a set set * ('a set \<Rightarrow> real)) \<Rightarrow> 'a set set" where
  "measurable_sets = fst"

definition
  measure:: "('a set set * ('a set \<Rightarrow> real)) \<Rightarrow> ('a set \<Rightarrow> real)" where
  "measure = snd"

text \<open>The other component is the measure itself. It is a function that
  assigns a nonnegative real number to every measurable set and has
  the property of being
  countably additive for disjoint sets.\<close>


definition
  positive:: "('a set set * ('a set \<Rightarrow> real)) \<Rightarrow> bool" where
  "positive M \<longleftrightarrow> measure M {} = 0 \<and> 
  (\<forall>A. A\<in> measurable_sets M \<longrightarrow> 0 \<le> measure M A)"
  (*Remark: This definition of measure space is not minimal,
  in the sense that the containment of the \<Union>(the ` in) measurable sets 
  is implied by the measurable sets being a sigma algebra*)

definition
  countably_additive:: "('a set set * ('a set => real)) => bool" where
  "countably_additive M \<longleftrightarrow> (\<forall>f::(nat => 'a set). range f \<subseteq> measurable_sets M
  \<and> (\<forall>m n. m \<noteq> n \<longrightarrow> f m \<inter> f n = {}) \<and>  (\<Union>i. f i) \<in> measurable_sets M
  \<longrightarrow> (\<lambda>n. measure M (f n)) sums  measure M (\<Union>i. f i))" 

text \<open>This last property deserves some comments. The conclusion is
  usually --- also in the aforementioned source --- phrased as
  
  \<open>measure M (\<Union>i. f i) = (\<Sum>n. measure M (f n))\<close>.

  In our formal setting this is unsatisfactory, because the
  sum operator\footnote{Which is merely syntactic sugar for the
  \isa{suminf} functional from the \isa{Series} theory
  \cite{Fleuriot:2000:MNR}.}, like any HOL function, is total, although
  a series obviously need not converge. It is defined using the \<open>\<epsilon>\<close> operator, and its
  behavior is unspecified in the diverging case. Hence, the above assertion
  would give no information about the convergence of the series. 
  
  Furthermore, the definition contains redundancy. Assuming that the
  countable union of sets is measurable is unnecessary when the
  measurable sets form a sigma algebra, which is postulated in the
  final definition\footnote{Joe Hurd inherited this practice from a very
  influential probability textbook \cite{Williams.mart}}. 
\<close>

definition
  measure_space:: "('a set set * ('a set \<Rightarrow> real)) \<Rightarrow> bool" where
  "measure_space M \<longleftrightarrow> sigma_algebra (measurable_sets M) \<and> 
  positive M \<and> countably_additive M"

text \<open>Note that our definition is restricted to finite measure
  spaces --- that is, \<open>measure M UNIV < \<infinity>\<close> --- since the measure
  must be a real number for any measurable set. In probability, this
  is naturally the case.    

  Two important theorems close this section. Both appear in
  Hurd's work as well, but are shown anyway, owing to their central
  role in measure theory. The first one is a mighty tool for proving measurability. It states
  that for a function mapping one sigma algebra into another, it is
  sufficient to be measurable regarding only a generator of the target
  sigma algebra. Formalizing the interesting proof out of Bauer's
  textbook \cite{Bauer} is relatively straightforward using rule
  induction.\<close>

theorem assumes sig: "sigma_algebra a" and meas: "f \<in> measurable a b" shows 
  measurable_lift: "f \<in> measurable a (sigma b)"
proof -
  define Q where "Q = {q. f -` q \<in> a}"
  with meas have 1: "b \<subseteq> Q" by (auto simp add: measurable_def) 

  { fix x assume "x\<in>sigma b"
    hence "x\<in>Q"
    proof (induct rule: sigma.induct)
      case basic
      from 1 show " \<And>a. a \<in> b \<Longrightarrow> a \<in> Q" ..
    next
      case empty
      from sig have "{}\<in>a" 
        by (simp only: sigma_algebra_def)     
      thus "{} \<in> Q" 
        by (simp add: Q_def)
    next
      case complement
      fix r assume "r \<in> Q"
      then obtain r1 where im: "r1 = f -` r" and a: "r1 \<in> a" 
        by (simp add: Q_def)
      with sig have "-r1 \<in> a" 
        by (simp only: sigma_algebra_def)
      with im Q_def show "-r \<in> Q" 
        by (simp add: vimage_Compl)
    next
      case Union
      fix r assume "\<And>i::nat. r i \<in> Q"
      then obtain r1 where im: "\<And>i. r1 i =  f -` r i" and a: "\<And>i. r1 i \<in>        a" 
        by (simp add: Q_def)
      from a sig have "\<Union>(r1 ` UNIV) \<in> a" 
        by (auto simp only: sigma_algebra_def)
      with im Q_def show "\<Union>(r ` UNIV) \<in> Q" 
        by (auto simp add: vimage_UN)
    qed }
        
  hence "(sigma b) \<subseteq> Q" ..
  thus "f \<in> measurable a (sigma b)" 
    by (auto simp add: measurable_def Q_def)
qed

text \<open>The case is different for the second theorem. It is only five
  lines in the book (ibid.), but almost 200 in formal text. Precision
  still pays here, gaining a detailed view of a technique that
  is often employed in measure theory --- making a sequence of sets
  disjoint. Moreover, the necessity for the above-mentioned change in the
  definition of countably additive was detected only in the
  formalization of this proof. 

  To enable application of the additivity of measures, the following construction
  yields disjoint sets. We skip the justification of the lemmata for
  brevity.\<close> 

primrec mkdisjoint:: "(nat \<Rightarrow> 'a set) \<Rightarrow> (nat \<Rightarrow> 'a set)"
where
  "mkdisjoint A 0 = A 0"
| "mkdisjoint A (Suc n) = A (Suc n) - A n"

lemma mkdisjoint_un: 
  assumes up: "\<And>n. A n \<subseteq> A (Suc n)"
  shows "A n = (\<Union>i\<in>{..n}. mkdisjoint A i)"
(*<*)proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  hence "A n = (\<Union>i\<in>{..n}. mkdisjoint A i)" .
  moreover
  have "(\<Union>i\<in>{..(Suc n)}. mkdisjoint A i) = mkdisjoint A (Suc n) \<union>
    (\<Union>i\<in>{..n}. mkdisjoint A i)" by (simp add: atMost_Suc) 
  moreover
  have "mkdisjoint A (Suc n) \<union> A n = A (Suc n) \<union> A n" by simp
  moreover
  from up have "\<dots> = A (Suc n)" by auto
  ultimately
  show ?case by simp
qed(*>*)


lemma mkdisjoint_disj: 
  assumes up: "\<And>n. A n \<subseteq> A (Suc n)" and ne: "m \<noteq> n"
  shows "mkdisjoint A m \<inter> mkdisjoint A n = {}"
(*<*)proof -
  { fix m1 m2::nat assume less: "m1 < m2"
    hence "0 < m2" by simp
    then obtain n where eq: "m2 = Suc n" by (auto simp add: gr0_conv_Suc)
    with less have less2: "m1 < Suc n" by simp
    
    {
      fix y assume y: "y \<in> mkdisjoint A m1"
      fix x assume x: "x \<in> mkdisjoint A m2"
      with eq have"x \<notin> A n" by simp
      also from up have "A n = (\<Union>i\<in>{..n}. mkdisjoint A i)" 
        by (rule mkdisjoint_un) 
      also 
      from less2 have "m1 \<in> {..n}" by simp
      hence "mkdisjoint A m1 \<subseteq> (\<Union>i\<in>{..n}. mkdisjoint A i)" by auto
      ultimately 
      have "x \<notin> mkdisjoint A m1" by auto
      with y have "y \<noteq> x" by fast
    }
    hence "mkdisjoint A m1 \<inter> mkdisjoint A m2 = {}" 
      by (simp add: disjoint_iff_not_equal)
  } hence 1: "\<And>m1 m2. m1 < m2 \<Longrightarrow>  mkdisjoint A m1 \<inter> mkdisjoint A m2 = {}" .
  
  show ?thesis
  proof (cases "m < n")
    case True
    thus ?thesis by (rule 1)
  next
    case False
    with ne have "n < m" by arith
    hence "mkdisjoint A n \<inter> mkdisjoint A m = {}" by (rule 1)
    thus ?thesis by fast
  qed
qed(*>*)
   

lemma mkdisjoint_mon_conv:
  assumes mc: "A\<up>B" 
  shows "(\<Union>i. mkdisjoint A i) = B"
(*<*)proof
  { fix x assume "x \<in> (\<Union>i. mkdisjoint A i)"
    then obtain i where "x \<in> mkdisjoint A i" by auto
    hence "x \<in> A i" by (cases i) simp_all
    with mc have "x \<in> B" by (auto simp add: mon_conv_set_def)
  }
  thus "(\<Union>i. mkdisjoint A i) \<subseteq> B" by fast
     
  { fix x assume "x \<in> B"
    with mc obtain i where "x \<in> A i" by (auto simp add: mon_conv_set_def)
    also from mc have "\<And>n. A n \<subseteq> A (Suc n)" by (simp only: mon_conv_set_def)
    hence "A i = (\<Union>r\<in>{..i}. mkdisjoint A r)" by (rule mkdisjoint_un)
    also have "\<dots> \<subseteq> (\<Union>r. mkdisjoint A r)" by auto
    finally have "x \<in> (\<Union>i. mkdisjoint A i)".
  }
  thus "B \<subseteq> (\<Union>i. mkdisjoint A i)" by fast
qed(*>*)

  
(*This is in Joe Hurd's Thesis (p. 35) as Monotone Convergence theorem. Check the real name \<dots> . 
    Also, it's not as strong as it could be,
    but we need no more.*)

text \<open>Joe Hurd calls the following the Monotone Convergence Theorem,
  though in mathematical literature this name is often reserved for a
  similar fact
  about integrals that we will prove in \ref{nnfis}, which depends on this
  one. The claim made here is that the measures of monotonically convergent sets
  approach the measure of their limit. A strengthened version would
  imply monotone convergence of the measures, but is not needed in the
  development.
\<close>

theorem measure_mon_conv: 
  assumes ms: "measure_space M" and 
  Ams: "\<And>n. A n \<in> measurable_sets M" and AB: "A\<up>B" 
  shows "(\<lambda>n. measure M (A n)) \<longlonglongrightarrow> measure M B"
proof -
  
  from AB have up: "\<And>n. A n \<subseteq> A (Suc n)" 
    by (simp only: mon_conv_set_def)
  
  { fix i
    have "mkdisjoint A i \<in> measurable_sets M" 
    proof (cases i)
      case 0 with Ams show ?thesis by simp
    next
      case (Suc i)
      have "A (Suc i) - A i = A (Suc i) \<inter> - A i" by blast
      with Suc ms Ams show ?thesis 
        by (auto simp add: measure_space_def sigma_algebra_def sigma_algebra_inter)
    qed
  } 
  hence i: "\<And>i. mkdisjoint A i \<in> measurable_sets M" .
      
  with ms have un: "(\<Union>i. mkdisjoint A i) \<in> measurable_sets M" 
    by (simp add: measure_space_def sigma_algebra_def)
  moreover
  from i have range: "range (mkdisjoint A) \<subseteq> measurable_sets M" 
    by fast
  moreover
  from up have "\<forall>i j. i \<noteq> j \<longrightarrow>  mkdisjoint A i \<inter> mkdisjoint A j = {}" 
    by (simp add: mkdisjoint_disj)
  moreover note ms
  ultimately
  have sums:
    "(\<lambda>i. measure M (mkdisjoint A i)) sums (measure M (\<Union>i. mkdisjoint A i))"
    by (simp add: measure_space_def countably_additive_def)
  hence "(\<Sum>i. measure M (mkdisjoint A i)) = (measure M (\<Union>i. mkdisjoint A i))" 
    by (rule sums_unique[THEN sym])
  
  also
  from sums have "summable (\<lambda>i. measure M (mkdisjoint A i))" 
    by (rule sums_summable)

  hence "(\<lambda>n. \<Sum>i<n. measure M (mkdisjoint A i))
    \<longlonglongrightarrow> (\<Sum>i. measure M (mkdisjoint A i))"
    by (rule summable_LIMSEQ)
                                         
  hence "(\<lambda>n. \<Sum>i<Suc n. measure M (mkdisjoint A i)) \<longlonglongrightarrow> (\<Sum>i. measure M (mkdisjoint A i))"
    by (rule LIMSEQ_Suc)
  
  ultimately have "(\<lambda>n. \<Sum>i<Suc n. measure M (mkdisjoint A i))
    \<longlonglongrightarrow> (measure M (\<Union>i. mkdisjoint A i))" by simp
    
  also 
  { fix n 
    from up have "A n = (\<Union>i\<in>{..n}. mkdisjoint A i)" 
      by (rule mkdisjoint_un)
    hence "measure M (A n) = measure M (\<Union>i\<in>{..n}. mkdisjoint A i)"
      by simp
    
    also have 
      "(\<Union>i\<in>{..n}. mkdisjoint A i) = (\<Union>i. if i\<le>n then mkdisjoint A i else {})"
    proof -
      have "UNIV = {..n} \<union> {n<..}" by auto
      hence "(\<Union>i. if i\<le>n then mkdisjoint A i else {}) = 
        (\<Union>i\<in>{..n}. if i\<le>n then mkdisjoint A i else {}) 
        \<union>  (\<Union>i\<in>{n<..}. if i\<le>n then mkdisjoint A i else {})" 
        by (auto split: if_splits)
      moreover
      { have "(\<Union>i\<in>{n<..}. if i\<le>n then mkdisjoint A i else {}) = {}"
          by force }
      hence "\<dots> = (\<Union>i\<in>{..n}. mkdisjoint A i)" 
        by auto
      ultimately show 
        "(\<Union>i\<in>{..n}. mkdisjoint A i) = (\<Union>i. if i\<le>n then mkdisjoint A i else {})" by simp
    qed
    
    ultimately have 
      "measure M (A n) = measure M (\<Union>i. if i\<le>n then mkdisjoint A i else {})" 
      by simp

    also 
    from i ms have 
      un: "(\<Union>i. if i\<le>n then mkdisjoint A i else {}) \<in> measurable_sets M" 
      by (simp add: measure_space_def sigma_algebra_def cong add: SUP_cong_simp)
    moreover
    from i ms have 
      "range (\<lambda>i. if i\<le>n then mkdisjoint A i else {}) \<subseteq> measurable_sets M" 
      by (auto simp add: measure_space_def sigma_algebra_def)
    moreover
    from up have "\<forall>i j. i \<noteq> j \<longrightarrow> 
      (if i\<le>n then mkdisjoint A i else {}) \<inter> 
      (if j\<le>n then mkdisjoint A j else {}) = {}" 
      by (simp add: mkdisjoint_disj)
    moreover note ms
    ultimately have 
      "measure M (A n) = (\<Sum>i. measure M (if i \<le> n then mkdisjoint A i else {}))"
      by (simp add: measure_space_def countably_additive_def sums_unique cong add: SUP_cong_simp)
    
    also
    from ms have 
      "\<forall>i. (Suc n)\<le>i \<longrightarrow> measure M (if i \<le> n then mkdisjoint A i else {}) = 0"
      by (simp add: measure_space_def positive_def)
    hence "(\<lambda>i. measure M (if i \<le> n then mkdisjoint A i else {})) sums
      (\<Sum>i<Suc n. measure M (if i \<le> n then mkdisjoint A i else {}))"
      by (intro sums_finite) auto
    hence "(\<Sum>i. measure M (if i \<le> n then mkdisjoint A i else {})) = 
      (\<Sum>i<Suc n. measure M (if i \<le> n then mkdisjoint A i else {}))"
      by (rule sums_unique[THEN sym])
    also
    have "\<dots> = (\<Sum>i<Suc n. measure M (mkdisjoint A i))"
      by simp
    finally have 
      "measure M (A n) = (\<Sum>i<Suc n. measure M (mkdisjoint A i))" .
  }
  
  ultimately have 
    "(\<lambda>n. measure M (A n)) \<longlonglongrightarrow> (measure M (\<Union>i. mkdisjoint A i))" 
    by simp
  
  with AB show ?thesis 
    by (simp add: mkdisjoint_mon_conv)
qed(*>*)


(*<*)
primrec trivial_series2:: "'a set \<Rightarrow> 'a set \<Rightarrow> (nat \<Rightarrow> 'a set)"
where
  "trivial_series2 a b 0 = a"
| "trivial_series2 a b (Suc n) = (if (n=0) then b else {})"

lemma measure_additive: assumes ms: "measure_space M"
  and disj: "a \<inter> b = {}" and a: "a \<in> measurable_sets M"
  and b:"b \<in> measurable_sets M"
  shows "measure M (a \<union> b) = measure M a + measure M b"
(*<*)proof -
  have "(a \<union> b) = (\<Union>i. trivial_series2 a b i)"
  proof (rule set_eqI)
    fix x
    {
      assume "x \<in> a \<union> b"
      hence "\<exists>i. x \<in> trivial_series2 a b i"
      proof 
        assume "x \<in> a"
        hence "x \<in> trivial_series2 a b 0"
          by simp
        thus "\<exists>i. x \<in> trivial_series2 a b i"
          by fast
      next
        assume "x \<in> b"
        hence "x \<in> trivial_series2 a b 1"
          by simp
        thus "\<exists>i. x \<in> trivial_series2 a b i"
          by fast
      qed
    }
    hence "(x \<in> a \<union> b) \<Longrightarrow> (x \<in> (\<Union>i. trivial_series2 a b i))"
      by simp
    also
    { 
      assume "x \<in> (\<Union>i. trivial_series2 a b i)"
      then obtain i where x: "x \<in> trivial_series2 a b i"
        by auto
      hence "x \<in> a \<union> b"
      proof (cases i)
        case 0
        with x show ?thesis by simp
      next
        case (Suc n)
        with x show ?thesis
          by (cases n) auto
      qed
    }
    ultimately show "(x \<in> a \<union> b) = (x \<in> (\<Union>i. trivial_series2 a b i))"
      by fast
  qed
  also 
  { fix i
    from a b ms have "trivial_series2 a b i \<in> measurable_sets M"
      by (cases i) (auto simp add: measure_space_def sigma_algebra_def)
  }
  hence m1: "range (trivial_series2 a b) \<subseteq> measurable_sets M"
    and m2: "(\<Union>i. trivial_series2 a b i) \<in> measurable_sets M"
    using ms
    by (auto simp add: measure_space_def sigma_algebra_def)
  
  { fix i j::nat
    assume "i \<noteq> j"
    hence "trivial_series2 a b i \<inter> trivial_series2 a b j = {}"
      using disj
      by (cases i, cases j, auto)(cases j, auto)
  }
  with m1 m2 have "(\<lambda>n. measure M (trivial_series2 a b n)) sums  measure M (\<Union>i. trivial_series2 a b i)" 
    using ms 
    by (simp add: measure_space_def countably_additive_def)
  moreover
  from ms have "\<forall>m. Suc(Suc 0) \<le> m \<longrightarrow> measure M (trivial_series2 a b m) = 0"
  proof (clarify)
    fix m 
    assume "Suc (Suc 0) \<le> m"
    thus "measure M (trivial_series2 a b m) = 0"
      using ms
      by (cases m) (auto simp add: measure_space_def positive_def) 
  qed
  hence "(\<lambda>n. measure M (trivial_series2 a b n)) sums (\<Sum>n<Suc(Suc 0). measure M (trivial_series2 a b n))"
    by (intro sums_finite) auto
  moreover
  have "(\<Sum>n=0..<Suc(Suc 0). measure M (trivial_series2 a b n)) =
    measure M a + measure M b"
    by simp
  ultimately
  have "measure M (a \<union> b) = (\<Sum>n. measure M (trivial_series2 a b n))"
    and "Measure.measure M a + Measure.measure M b = (\<Sum>n. measure M (trivial_series2 a b n))"
    by (simp_all add: sums_unique)
  thus ?thesis by simp
qed
(*>*)
end
