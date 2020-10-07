(* The Lebesgue Integral 

    Stefan Richter 2002 *)

section \<open>The three-step approach \label{sec:stepwise-approach}\<close>

theory Integral
imports RealRandVar
begin
  (*simple function integral set*)
text \<open>Having learnt from my failures, we take the safe and clean way
  of Heinz Bauer \cite{Bauer}. It proceeds as outlined in the
  introduction. In three steps, we fix the integral for elementary
  (``step-'')functions, for limits of these, and finally for
  differences between such limits. 
\<close>

subsection \<open>Simple functions \label{sec:simple-fun}\<close>

text \<open>
  A simple function is a finite sum of characteristic functions, each
  multiplied with a nonnegative constant. These functions must be
  parametrized by measurable sets. Note that to check this condition,
  a tuple consisting of
  a set of measurable sets and a measure is required as
  the integral operator's second argument, whereas the
  measure only is given in informal notation. Usually the tuple will
  be a measure space, though it is not required so by the definition at
  this point. 

  It is most natural to declare the value of the integral in this
  elementary case by simply replacing the characteristic functions
  with the measures of their respective sets. Uniqueness remains to be
  shown, for a function may have
  infinitely many decompositions and these might give rise to more
  than one integral value. This is why we construct a \emph{simple
  function integral set} for any function and measurable sets/measure
  pair by means of an inductive set definition containing but one
  introduction rule.
\<close>

inductive_set
  sfis:: "('a \<Rightarrow> real) \<Rightarrow> ('a set set * ('a set \<Rightarrow> real)) \<Rightarrow> real set"
  for f :: "'a \<Rightarrow> real" and M :: "'a set set * ('a set \<Rightarrow> real)"
  where (*This uses normal forms*)
  base:  "\<lbrakk>f = (\<lambda>t. \<Sum>i\<in>(S::nat set). x i * \<chi> (A i) t);
  \<forall>i \<in> S. A i \<in> measurable_sets M; nonnegative x; finite S;
  \<forall>i\<in>S. \<forall>j\<in>S. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}; (\<Union>i\<in>S. A i) = UNIV\<rbrakk>
  \<Longrightarrow> (\<Sum>i\<in>S. x i * measure M (A i)) \<in> sfis f M"
  (*S may not be polymorphic*)

text\<open>As you can see we require two extra conditions, and they amount
  to the sets being a partition of the universe. We say that a
  function is in normal form if it is represented this way. Normal
  forms are only needed to show additivity and monotonicity of simple
  function integral sets. These theorems can then be used in turn to
  get rid of the normality condition. 

  More precisely, normal forms
  play a central role in the \<open>sfis_present\<close> lemma. For two
  simple functions with different underlying partitions it states
  the existence of a common finer-grained partition that can be used
  to represent the functions uniformly. The proof is remarkably
  lengthy, another case where informal reasoning is more intricate
  than it seems. The reason it is included anyway, with the exception
  of the two following lemmata, is that it gives insight into the
  arising complication and its formal solution. 

  The problem is in the use of informal sum
  notation, which easily permits for a change in index sets, allowing
  for a pair of indices. This change has to be rectified in formal
  reasoning. Luckily, the task is eased by an injective function from
  $\mathbb{N}^2$ into $\mathbb{N}$, which was developed for the
  rationals mentioned in \ref{sec:realrandvar}.
  It might have been still easier if index sets were
  polymorphic in our integral definition, permitting pairs to be
  formed when necessary, but the logic doesn't allow for this.\<close>
  


lemma assumes un: "(\<Union>i\<in>R. B i) = UNIV" and fin: "finite R"
  and dis: "\<forall>j1\<in>R. \<forall>j2\<in>R. j1 \<noteq> j2 \<longrightarrow> (B j1) \<inter> (B j2) = {}"
  shows char_split: "\<chi> A t = (\<Sum>j\<in>R. \<chi> (A \<inter> B j) t)"
(*<*)proof (cases "t \<in> A")
  case True
  with un obtain j where jR: "j\<in>R" and tj: "t \<in> A \<inter> B j" by fast
  from tj have "\<chi> (A \<inter> B j) t = 1" by (simp add: characteristic_function_def)
  with fin jR have "(\<Sum>i\<in>R-{j}. \<chi> (A \<inter> B i) t) = (\<Sum>i\<in>R. \<chi> (A \<inter> B i) t) - 1"
    by (simp add: sum_diff1)
  also 
  from dis jR tj have "R-{j} = R-{j}" and "\<And>x. x \<in> R-{j} \<Longrightarrow> \<chi> (A \<inter> B x) t = 0" 
    by (auto simp add: characteristic_function_def) 
  hence "(\<Sum>i\<in>R-{j}. \<chi> (A \<inter> B i) t) = (\<Sum>i\<in>R-{j}. 0)" by (rule sum.cong) 
  finally have "1 = (\<Sum>i\<in>R. \<chi> (A \<inter> B i) t)" by (simp)
  with True show ?thesis by (simp add: characteristic_function_def)
next
  case False
  hence "\<And>i. \<chi> (A \<inter> B i) t = 0" by (simp add: characteristic_function_def)
  hence "0 = (\<Sum>i\<in>R. \<chi> (A \<inter> B i) t)" by (simp)
  with False show ?thesis by (simp add: characteristic_function_def)
qed

lemma assumes ms: "measure_space M" and dis: "\<forall>j1\<in>(R::nat set). \<forall>j2\<in>R. j1 \<noteq> j2 \<longrightarrow> (B j1) \<inter> (B j2) = {}"
  and meas: "\<forall>j\<in>R. B j \<in> measurable_sets M"
  shows measure_sums_UNION: "(\<lambda>n. measure M (if n \<in> R then B n else {})) sums measure M (\<Union>i\<in>R. B i)" 
(*<*)proof -
  have eq: "(\<Union>i\<in>R. B i) = (\<Union>i. if i\<in>R then B i else {})"
    by (auto split: if_splits)
  
  from dis have dis2: "(\<forall>i j. i \<noteq> j \<longrightarrow> (if i\<in>R then B i else {}) \<inter> (if j\<in>R then B j else {})  = {})"
    by simp

  from meas have meas2: "range (\<lambda>i. if i\<in>R then B i else {}) \<subseteq> measurable_sets M"
    using ms by (auto simp add: measure_space_def sigma_algebra_def)
  hence "\<forall>i. (if i\<in>R then B i else {})\<in> measurable_sets M"
    by auto
  with ms have "(\<Union>i. if i\<in>R then B i else {}) \<in> measurable_sets M"
    by (auto simp add: measure_space_def sigma_algebra_def) (use eq in presburger)
  with meas2 dis2 have "(\<lambda>n. measure M (if n \<in> R then B n else {}))
    sums measure M (\<Union>i. if i\<in>R then B i else {})"
    using ms by (simp add: measure_space_def countably_additive_def cong: SUP_cong_simp)
  with eq show ?thesis  
    by simp
qed(*>*)

lemma sumr_sum:
 "(\<Sum>i=0..<k::nat. if i \<in> R then f i else (0::real)) = (\<Sum>i\<in>(R\<inter>{..<k}). f i)" 
(*<*)proof (induct k)
  case 0
  thus ?case
    by simp
  case (Suc l)
  hence "(\<Sum>i=0..<Suc l. if i \<in> R then f i else 0) =  
    (if l \<in> R then f l else 0) + (\<Sum>i\<in>(R\<inter>{..<l}). f i)"
    by simp
  also have "\<dots> =  (\<Sum>i\<in>(R \<inter> {..<Suc l}). f i)"
  proof (cases "l \<in> R")
    case True
    have "l \<notin> (R\<inter>{..<l})" by simp
    have "f l + (\<Sum>i\<in>(R\<inter>{..<l}). f i) = (\<Sum>i\<in>(insert l (R\<inter>{..<l})). f i)"
      by simp
    also from True have "insert l (R\<inter>{..<l}) = (R \<inter> {..<Suc l})"
      by (auto simp add: lessThan_Suc)
    finally show ?thesis
      using True by simp
  next
    case False
    hence "(R\<inter>{..<l}) = (R \<inter> {..<Suc l})" by (auto simp add: lessThan_Suc)
    thus ?thesis by auto
  qed
  finally show ?case .
qed(*>*)
     
lemma assumes ms: "measure_space M" and dis: "\<forall>j1\<in>(R::nat set). \<forall>j2\<in>R. j1 \<noteq> j2 \<longrightarrow> (B j1) \<inter> (B j2) = {}"
  and meas: "\<forall>j\<in>R. B j \<in> measurable_sets M" and fin: "finite R"
  shows measure_sum: "measure M (\<Union>i\<in>R. B i) = (\<Sum>j\<in>R. measure M (B j))"
(*<*)proof (cases "R={}")
  case False
  with fin have leR: "\<forall>r\<in>R. r  \<le> Max R"
    by simp
  hence "R = R \<inter> {..Max R}"
    by auto
  also have "\<dots> = R \<inter> {..<Suc (Max R)}"
    by (simp add: lessThan_Suc_atMost[THEN sym])
  finally have "(\<Sum>j\<in>R. measure M (B j)) = (\<Sum>j\<in>R\<inter> {..<Suc (Max R)} . measure M (B j))"
    by simp
  also have "\<dots> = (\<Sum>x=0..<Suc(Max R). if x \<in> R then measure M (B x) else 0)"
    by (rule sumr_sum[THEN sym])
  also { 
    fix x 
    from ms have "(if x \<in> R then measure M (B x) else 0) = (measure M (if x\<in>R then B x else {}))"
      by (simp add: measure_space_def positive_def)
  }
  hence "\<dots> = (\<Sum>x=0..<Suc(Max R). measure M (if x\<in>R then B x else {}))" by simp
  also {
    fix m
    assume "Suc (Max R) \<le> m"
    hence "Max R < m" by simp
    with leR have "m\<notin>R" by auto
    with ms have "measure M (if m\<in>R then B m else {}) = 0"
      by (simp add: measure_space_def positive_def)
  } 
  hence "\<forall>m. (Suc (Max R)) \<le> m \<longrightarrow> measure M (if m\<in>R then B m else {}) = 0"
    by simp
  hence "(\<lambda>n. measure M (if n \<in> R then B n else {})) sums (\<Sum>x=0..<Suc(Max R). measure M (if x\<in>R then B x else {}))"
    by (intro sums_finite) auto
  hence "(\<Sum>x=0..<Suc(Max R). measure M (if x\<in>R then B x else {})) = suminf (\<lambda>n. measure M (if n \<in> R then B n else {}))"
    by (rule sums_unique)
  also from ms dis meas have "(\<lambda>n. measure M (if n \<in> R then B n else {})) sums measure M (\<Union>i\<in>R. B i)"
    by (rule measure_sums_UNION)
  ultimately show ?thesis  by (simp add: sums_unique)
next
  case True
  with ms show ?thesis by (simp add: measure_space_def positive_def)
qed(*>*)


lemma assumes ms: "measure_space M" and un: "(\<Union>i\<in>R. B i) = UNIV" and 
  fin: "finite (R::nat set)" and dis: "\<forall>j1\<in>R. \<forall>j2\<in>R. j1 \<noteq> j2 \<longrightarrow> (B j1) \<inter> (B j2) = {}"
  and meas: "\<forall>j\<in>R. B j \<in> measurable_sets M" and Ameas: "A \<in> measurable_sets M"
  shows measure_split: "measure M A = (\<Sum>j\<in>R. measure M (A \<inter> B j))"
(*<*)proof -
  note ms moreover
  from dis have "\<forall>j1\<in>R. \<forall>j2\<in>R. j1 \<noteq> j2 \<longrightarrow> (A \<inter> B j1) \<inter> (A \<inter> B j2) = {}"
    by fast
  moreover
  from ms meas Ameas have "\<forall>j\<in>R. A \<inter> B j \<in> measurable_sets M"
    by (simp add: measure_space_def sigma_algebra_inter)
  moreover note fin
  ultimately have "measure M (\<Union>i\<in>R. A \<inter> B i) = (\<Sum>j\<in>R. measure M (A \<inter> B j))"
    by (rule measure_sum)
  also
  from un have "A = (\<Union>i\<in>R. A \<inter> B i)"
    by auto
  ultimately show ?thesis 
    by simp
qed(*>*)


lemma prod_encode_fst_inj: "inj (\<lambda>i. prod_encode(i,j))" using inj_prod_encode
  by (unfold inj_on_def) blast

lemma prod_encode_snd_inj: "inj (\<lambda>j. prod_encode(i,j))" using inj_prod_encode
  by (unfold inj_on_def) blast

(*>*)
lemma assumes (*<*)ms:(*>*) "measure_space M" and (*<*)a:(*>*) "a \<in> sfis f M" and (*<*)b:(*>*) "b \<in> sfis g M"
  shows sfis_present: "\<exists> z1 z2 C K. 
  f = (\<lambda>t. \<Sum>i\<in>(K::nat set). z1 i * \<chi> (C i) t) \<and> g = (\<lambda>t. \<Sum>i\<in>K. z2 i * \<chi> (C i) t) 
  \<and> a = (\<Sum>i\<in>K. z1 i * measure M (C i)) \<and> b = (\<Sum>i\<in>K. z2 i * measure M (C i))
  \<and> finite K \<and> (\<forall>i\<in>K. \<forall>j\<in>K. i \<noteq> j \<longrightarrow> C i \<inter> C j = {})
  \<and> (\<forall>i \<in> K. C i \<in> measurable_sets M) \<and> (\<Union>i\<in>K. C i) = UNIV 
  \<and> nonnegative z1 \<and> nonnegative z2"
  using a
proof cases 
  case (base x A R)
  note base_x = this
  show ?thesis using b
  proof cases
    case (base y B S) 
                      
    with assms base_x have ms: "measure_space M" 
      and f: "f = (\<lambda>t. \<Sum>i\<in>(R::nat set). x i * \<chi> (A i) t)"
      and a: "a = (\<Sum>i\<in>R. x i * measure M (A i))" 
      and Ams: "\<forall>i \<in> R. A i \<in> measurable_sets M" 
      and R: "finite R" and Adis: "\<forall>i\<in>R. \<forall>j\<in>R. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
      and Aun: "(\<Union>i\<in>R. A i) = UNIV" 
      and g: "g = (\<lambda>t. \<Sum>i\<in>(S::nat set). y i * \<chi> (B i) t)"
      and b: "b = (\<Sum>j\<in>S. y j * measure M (B j))" 
      and Bms: "\<forall>i \<in> S. B i \<in> measurable_sets M"
      and S: "finite S" 
      and Bdis: "\<forall>i\<in>S. \<forall>j\<in>S. i \<noteq> j \<longrightarrow> B i \<inter> B j = {}" 
      and Bun: "(\<Union>i\<in>S. B i) = UNIV" 
      and x: "nonnegative x" and y: "nonnegative y"
      by simp_all
txt\<open>\nopagebreak\<close>
    define C where "C = (\<lambda>(i,j). A i \<inter> B j) \<circ> prod_decode"
    define z1 where "z1 k = x (fst (prod_decode k))" for k
    define z2 where "z2 k = y (snd (prod_decode k))" for k
    define K where "K = {k. \<exists>i\<in>R. \<exists>j\<in>S. k = prod_encode (i,j)}"
    define G where "G i = (\<lambda>j. prod_encode (i,j)) ` S" for i                                            
    define H where "H j = (\<lambda>i. prod_encode (i,j)) ` R" for j

    { fix t
      { fix i
        from Bun S Bdis have "\<chi> (A i) t = (\<Sum>j\<in>S. \<chi> (A i \<inter> B j) t)" 
          by (rule char_split)
        hence "x i * \<chi> (A i) t = (\<Sum>j\<in>S. x i * \<chi> (A i \<inter> B j) t)" 
          by (simp add: sum_distrib_left)
        also 
        { fix j
          have "S=S" and 
            "x i * \<chi> (A i \<inter> B j) t = (let k=prod_encode(i,j) in z1 k * \<chi> (C k) t)"
            by (auto simp add: C_def z1_def Let_def)
        }
        hence "\<dots> = (\<Sum>j\<in>S. let k=prod_encode (i,j) in z1 k * \<chi> (C k) t)"
          by (rule sum.cong)

        also from S have "\<dots> = (\<Sum>k\<in>(G i). z1 k * \<chi> (C k) t)"
          by (simp add: G_def Let_def o_def
                sum.reindex[OF subset_inj_on[OF prod_encode_snd_inj]])

        finally have eq: "x i * \<chi> (A i) t = (\<Sum>k\<in> G i. z1 k * \<chi> (C k) t)" .
          (*Repeat with measure instead of char*)
        
        from S have G: "finite (G i)" 
          by (simp add: G_def)  
        
        { fix k assume "k \<in> G i"
          then obtain j where kij: "k=prod_encode (i,j)" 
            by (auto simp only: G_def)
          { 
            fix i2 assume i2: "i2 \<noteq> i" 
            
            { fix k2 assume "k2 \<in> G i2"
              then obtain j2 where kij2: "k2=prod_encode (i2,j2)" 
                by (auto simp only: G_def)
              
              from i2 have "(i2,j2) \<noteq> (i,j)" and "(i2,j2) \<in> UNIV" 
                and "(i,j) \<in> UNIV" by auto
              with inj_prod_encode have  "prod_encode (i2,j2) \<noteq> prod_encode (i,j)"
                by (rule inj_on_contraD)
              with kij kij2 have "k2 \<noteq> k" 
                by fast
            }
            hence "k \<notin> G i2" 
              by fast
          }
        }
        hence "\<And>j. i \<noteq> j \<Longrightarrow> G i \<inter> G j = {}" 
          by fast
        note eq G this
      }
      hence eq: "\<And>i. x i * \<chi> (A i) t = (\<Sum>k\<in>G i. z1 k * \<chi> (C k) t)"
        and G: "\<And>i. finite (G i)" 
        and Gdis: "\<And>i j. i \<noteq> j \<Longrightarrow> G i \<inter> G j = {}" .

      { fix i
        assume "i\<in>R"
        with ms Bun S Bdis Bms Ams have 
          "measure M (A i) = (\<Sum>j\<in>S. measure M (A i \<inter> B j))" 
          by (simp add: measure_split)
        hence "x i * measure M (A i) = (\<Sum>j\<in>S. x i * measure M (A i \<inter> B j))" 
          by (simp add: sum_distrib_left)
        
        also 
        { fix j 
          have "S=S" and "x i * measure M (A i \<inter> B j) = 
            (let k=prod_encode(i,j) in z1 k * measure M (C k))"
            by (auto simp add: C_def z1_def Let_def)
        }
        
        hence "\<dots> = (\<Sum>j\<in>S. let k=prod_encode (i,j) in z1 k * measure M (C k))"
          by (rule sum.cong)
        
        also from S have "\<dots> = (\<Sum>k\<in>(G i). z1 k * measure M (C k))"
          by (simp add: G_def Let_def o_def
                sum.reindex[OF subset_inj_on[OF prod_encode_snd_inj]])
        
        finally have 
          "x i * measure M (A i) = (\<Sum>k\<in>(G i). z1 k * measure M (C k))" .
      }
      with refl[of R] have
        "(\<Sum>i\<in>R. x i * measure M (A i)) 
        = (\<Sum>i\<in>R. (\<Sum>k\<in>(G i). z1 k * measure M (C k)))"  
        by (rule sum.cong)
      with eq f a have "f t = (\<Sum>i\<in>R. (\<Sum>k\<in>G i. z1 k * \<chi> (C k) t))"
        and "a = (\<Sum>i\<in>R. (\<Sum>k\<in>(G i). z1 k * measure M (C k)))" 
        by auto
      also have KG: "K = (\<Union>i\<in>R. G i)" 
        by (auto simp add: K_def G_def)
      moreover note G Gdis R
      ultimately have f: "f t = (\<Sum>k\<in>K. z1 k * \<chi> (C k) t)" 
        and a: "a = (\<Sum>k\<in>K. z1 k * measure M (C k))"
        by (auto simp add: sum.UNION_disjoint)
          (*And now (almost) the same for g*)
      { fix j
        from Aun R Adis have "\<chi> (B j) t = (\<Sum>i\<in>R. \<chi> (B j \<inter> A i) t)" 
          by (rule char_split) 
        hence "y j * \<chi> (B j) t = (\<Sum>i\<in>R. y j * \<chi> (A i \<inter> B j) t)" 
          by (simp add: sum_distrib_left Int_commute)
        also 
        { fix i
          have "R=R" and 
            "y j * \<chi> (A i \<inter> B j) t = (let k=prod_encode(i,j) in z2 k * \<chi> (C k) t)"
            by (auto simp add: C_def z2_def Let_def)
        }
        hence "\<dots> = (\<Sum>i\<in>R. let k=prod_encode (i,j) in z2 k * \<chi> (C k) t)"
          by (rule sum.cong)
        also from R have "\<dots> = (\<Sum>k\<in>(H j). z2 k * \<chi> (C k) t)" 
          by (simp add: H_def Let_def o_def
                sum.reindex[OF subset_inj_on[OF prod_encode_fst_inj]])
        finally have eq: "y j * \<chi> (B j) t = (\<Sum>k\<in> H j. z2 k * \<chi> (C k) t)" .
                
        from R have H: "finite (H j)"  by (simp add: H_def)
        
        { fix k assume "k \<in> H j"
          then obtain i where kij: "k=prod_encode (i,j)" 
            by (auto simp only: H_def)
          { fix j2 assume j2: "j2 \<noteq> j" 
            { fix k2 assume "k2 \<in> H j2"
              then obtain i2 where kij2: "k2=prod_encode (i2,j2)" 
                by (auto simp only: H_def)
              
              from j2 have "(i2,j2) \<noteq> (i,j)" and "(i2,j2) \<in> UNIV" and "(i,j) \<in> UNIV" 
                by auto
              with inj_prod_encode have  "prod_encode (i2,j2) \<noteq> prod_encode (i,j)"
                by (rule inj_on_contraD)
              with kij kij2 have "k2 \<noteq> k" 
                by fast
            }
            hence "k \<notin> H j2" 
              by fast
          }
        }
        hence "\<And>i. i \<noteq> j \<Longrightarrow>  H i \<inter> H j = {}" 
          by fast
        note eq H this
      }
      hence eq: "\<And>j.  y j * \<chi> (B j) t = (\<Sum>k\<in>H j. z2 k * \<chi> (C k) t)" 
        and H: "\<And>i. finite (H i)"
        and Hdis: "\<And>i j. i \<noteq> j \<Longrightarrow> H i \<inter> H j = {}" .
      from eq g have "g t = (\<Sum>j\<in>S. (\<Sum>k\<in>H j. z2 k * \<chi> (C k) t))" 
        by simp
      also
      { fix j assume jS: "j\<in>S"
        from ms Aun R Adis Ams Bms jS have "measure M (B j) = 
          (\<Sum>i\<in>R. measure M (B j \<inter> A i))" 
          by (simp add: measure_split)
        hence "y j * measure M (B j) = (\<Sum>i\<in>R. y j * measure M (A i \<inter> B j))"
          by (simp add: sum_distrib_left Int_commute)
        also 
        { fix i 
          have "R=R" and "y j * measure M (A i \<inter> B j) = 
            (let k=prod_encode(i,j) in z2 k * measure M (C k))"
            by (auto simp add: C_def z2_def Let_def)
        }
        hence "\<dots> = (\<Sum>i\<in>R. let k=prod_encode(i,j) in z2 k * measure M (C k))"
          by (rule sum.cong)
        also from R have "\<dots> = (\<Sum>k\<in>(H j). z2 k * measure M (C k))"
          by (simp add: H_def Let_def o_def
                sum.reindex[OF subset_inj_on[OF prod_encode_fst_inj]])
        finally have eq2: 
          "y j * measure M (B j) = (\<Sum>k\<in>(H j). z2 k * measure M (C k))" .
      }
      with refl have "(\<Sum>j\<in>S. y j * measure M (B j)) = (\<Sum>j\<in>S. (\<Sum>k\<in>(H j). z2 k * measure M (C k)))"
        by (rule sum.cong)
      with b have "b = (\<Sum>j\<in>S. (\<Sum>k\<in>(H j). z2 k * measure M (C k)))" 
        by simp
      moreover have "K = (\<Union>j\<in>S. H j)" 
        by (auto simp add: K_def H_def)
      moreover note H Hdis S
      ultimately have g: "g t = (\<Sum>k\<in>K. z2 k * \<chi> (C k) t)" and K: "finite K"
        and b: "b = (\<Sum>k\<in>K. z2 k * measure M (C k))"
        by (auto simp add: sum.UNION_disjoint)
      
      { fix i 
        from Bun have "(\<Union>k\<in>G i. C k) = A i" 
          by (simp add: G_def C_def)
      }
      with Aun have "(\<Union>i\<in>R. (\<Union>k\<in>G i. C k)) = UNIV" 
        by simp
      hence "(\<Union>k\<in>(\<Union>i\<in>R. G i). C k) = UNIV" 
        by simp
      with KG have Kun: "(\<Union>k\<in>K. C k) = UNIV" 
        by simp
      
      note f g a b Kun K
    }  txt\<open>\nopagebreak\<close>
    hence f: "f = (\<lambda>t. (\<Sum>k\<in>K. z1 k * \<chi> (C k) t))" 
      and g: "g = (\<lambda>t. (\<Sum>k\<in>K. z2 k * \<chi> (C k) t))" 
      and a: "a = (\<Sum>k\<in>K. z1 k * measure M (C k))" 
      and b: "b = (\<Sum>k\<in>K. z2 k * measure M (C k))" 
      and Kun: "\<Union>(C ` K) = UNIV" and K: "finite K" 
      by (auto simp add: ext)

    note f g a b K
    moreover
    { fix k1 k2 assume "k1\<in>K" and "k2\<in>K" and diff: "k1 \<noteq> k2"
      with K_def obtain i1 j1 i2 j2 where 
        RS: "i1 \<in> R \<and> i2 \<in> R \<and> j1 \<in> S \<and> j2 \<in> S"
        and k1: "k1 = prod_encode (i1,j1)" and k2: "k2 = prod_encode (i2,j2)" 
        by auto
      
      with diff have "(i1,j1) \<noteq> (i2,j2)" 
        by auto
      
      with RS Adis Bdis k1 k2 have "C k1 \<inter> C k2 = {}" 
        by (simp add: C_def) fast
    }   
    moreover
    { fix k assume "k \<in> K"
      with K_def obtain i j where R: "i \<in> R" and S: "j \<in> S"
        and k: "k = prod_encode (i,j)" 
        by auto
      with Ams Bms have "A i \<in> measurable_sets M" and "B j \<in> measurable_sets M"
        by auto
      with ms have "A i \<inter> B j \<in> measurable_sets M" 
        by (simp add: measure_space_def sigma_algebra_inter)
      with k have "C k \<in> measurable_sets M" 
        by (simp add: C_def)
    }
    moreover note Kun
    
    moreover from x have "nonnegative z1" 
      by (simp add: z1_def nonnegative_def) 
    moreover from y have "nonnegative z2" 
      by (simp add: z2_def nonnegative_def)
    ultimately show ?thesis by blast
  qed
qed

text\<open>Additivity and monotonicity are now almost obvious, the latter
  trivially implying uniqueness.\<close> 

lemma assumes ms: "measure_space M" and a: "a \<in> sfis f M" and b: "b \<in> sfis g M"
  shows sfis_add: "a+b \<in> sfis (\<lambda>w. f w + g w) M" 
proof -     
  from assms have 
    "\<exists> z1 z2 C K. f = (\<lambda>t. \<Sum>i\<in>(K::nat set). z1 i * \<chi> (C i) t) \<and> 
    g = (\<lambda>t. \<Sum>i\<in>K. z2 i * \<chi> (C i) t) \<and> a = (\<Sum>i\<in>K. z1 i * measure M (C i))
    \<and> b = (\<Sum>i\<in>K. z2 i * measure M (C i))
    \<and> finite K \<and> (\<forall>i\<in>K. \<forall>j\<in>K. i \<noteq> j \<longrightarrow> C i \<inter> C j = {})
    \<and> (\<forall>i \<in> K. C i \<in> measurable_sets M) \<and> (\<Union>i\<in>K. C i) = UNIV
    \<and> nonnegative z1 \<and> nonnegative z2"
    by (rule sfis_present)
        
  then obtain z1 z2 C K where f: "f = (\<lambda>t. \<Sum>i\<in>(K::nat set). z1 i * \<chi> (C i) t)" 
    and g: "g = (\<lambda>t. \<Sum>i\<in>K. z2 i * \<chi> (C i) t)" 
    and a2: "a = (\<Sum>i\<in>K. z1 i * measure M (C i))"
    and b2: "b = (\<Sum>i\<in>K. z2 i * measure M (C i))"
    and CK: "finite K \<and> (\<forall>i\<in>K. \<forall>j\<in>K. i \<noteq> j \<longrightarrow> C i \<inter> C j = {}) \<and> 
    (\<forall>i\<in>K. C i \<in> measurable_sets M) \<and> \<Union>(C ` K) = UNIV"
    and z1: "nonnegative z1" and z2: "nonnegative z2"
    by auto
 
  { fix t
    from f g have 
      "f t + g t = (\<Sum>i\<in>K. z1 i * \<chi> (C i) t) + (\<Sum>i\<in>K. z2 i * \<chi> (C i) t)" 
      by simp
    also have "\<dots> = (\<Sum>i\<in>K. z1 i * \<chi> (C i) t + z2 i * \<chi> (C i) t)" 
      by (rule sum.distrib[THEN sym])
    also have "\<dots> = (\<Sum>i\<in>K. (z1 i + z2 i) * \<chi> (C i) t)" 
      by (simp add: distrib_right)
    finally have "f t + g t = (\<Sum>i\<in>K. (z1 i + z2 i) * \<chi> (C i) t)" .
  }

  also
  { fix t
    from z1 have "0 \<le> z1 t" 
      by (simp add: nonnegative_def)
    also from z2 have "0 \<le> z2 t" 
      by (simp add: nonnegative_def)
    ultimately have "0 \<le> z1 t + z2 t" 
      by (rule add_nonneg_nonneg)
  }
   
  hence "nonnegative (\<lambda>w. z1 w + z2 w)" 
    by (simp add: nonnegative_def ext)
  moreover note CK
  ultimately have 
    "(\<Sum>i\<in>K. (z1 i + z2 i) * measure M (C i)) \<in> sfis (\<lambda>w. f w + g w) M"
    by (auto simp add: sfis.base)
  also 
  from a2 b2 have "a+b = (\<Sum>i\<in>K. (z1 i + z2 i) * measure M (C i))" 
    by (simp add: sum.distrib[THEN sym] distrib_right)
  ultimately show ?thesis by simp
qed

lemma assumes ms: "measure_space M" and a: "a \<in> sfis f M" 
  and b: "b \<in> sfis g M" and fg: "f\<le>g"
  shows sfis_mono: "a \<le> b" 
proof - txt\<open>\nopagebreak\<close>
  from ms a b have 
    "\<exists> z1 z2 C K. f = (\<lambda>t. \<Sum>i\<in>(K::nat set). z1 i * \<chi> (C i) t) \<and> 
    g = (\<lambda>t. \<Sum>i\<in>K. z2 i * \<chi> (C i) t) \<and> a = (\<Sum>i\<in>K. z1 i * measure M (C i))
    \<and> b = (\<Sum>i\<in>K. z2 i * measure M (C i))
    \<and> finite K \<and> (\<forall>i\<in>K. \<forall>j\<in>K. i \<noteq> j \<longrightarrow> C i \<inter> C j = {})
    \<and> (\<forall>i \<in> K. C i \<in> measurable_sets M) \<and> (\<Union>i\<in>K. C i) = UNIV
    \<and> nonnegative z1 \<and> nonnegative z2"
    by (rule sfis_present)
 
  then obtain z1 z2 C K where f: "f = (\<lambda>t. \<Sum>i\<in>(K::nat set). z1 i * \<chi> (C i) t)" 
    and g: "g = (\<lambda>t. \<Sum>i\<in>K. z2 i * \<chi> (C i) t)" 
    and a2: "a = (\<Sum>i\<in>K. z1 i * measure M (C i))"
    and b2: "b = (\<Sum>i\<in>K. z2 i * measure M (C i))"
    and K: "finite K" and dis: "(\<forall>i\<in>K. \<forall>j\<in>K. i \<noteq> j \<longrightarrow> C i \<inter> C j = {})" 
    and Cms: "(\<forall>i\<in>K. C i \<in> measurable_sets M)" and Cun: "\<Union>(C ` K) = UNIV"
    by auto

  { fix i assume iK: "i \<in> K" 
    { assume "C i \<noteq> {}" 
      then obtain t where ti: "t \<in> C i" 
        by auto
      hence "z1 i = z1 i * \<chi> (C i) t" 
        by (simp add: characteristic_function_def)
      also 
      from dis iK ti have "K-{i} = K-{i}" 
        and "\<And>x. x \<in> K-{i} \<Longrightarrow> z1 x * \<chi> (C x) t = 0" 
        by (auto simp add: characteristic_function_def) 
      hence "0 = (\<Sum>k\<in>K-{i}. z1 k * \<chi> (C k) t)" 
        by (simp only: sum.neutral_const sum.cong)
      with K iK have "z1 i * \<chi> (C i) t = (\<Sum>k\<in>K. z1 k * \<chi> (C k) t)" 
        by (simp add: sum_diff1)
      also  
      from fg f g have "(\<Sum>i\<in>K. z1 i * \<chi> (C i) t) \<le> (\<Sum>i\<in>K. z2 i * \<chi> (C i) t)" 
        by (simp add: le_fun_def)
      also 
      from dis iK ti have "K-{i} = K-{i}" 
        and "\<And>x. x \<in> K-{i} \<Longrightarrow> z2 x * \<chi> (C x) t = 0" 
        by (auto simp add: characteristic_function_def)
      hence "0 = (\<Sum>k\<in>K-{i}. z2 k * \<chi> (C k) t)" 
        by (simp only: sum.neutral_const sum.cong)
      with K iK have "(\<Sum>k\<in>K. z2 k * \<chi> (C k) t) = z2 i * \<chi> (C i) t" 
        by (simp add: sum_diff1)
      also
      from ti have "\<dots> = z2 i" 
        by (simp add: characteristic_function_def)
      finally
      have "z1 i \<le> z2 i" .
    } 
    hence h: "C i \<noteq> {} \<Longrightarrow> z1 i \<le> z2 i" .
                                          
    have "z1 i * measure M (C i) \<le> z2 i * measure M (C i)"
    proof (cases "C i \<noteq> {}")
      case False 
      with ms show ?thesis 
        by (auto simp add: measure_space_def positive_def)
                                                          
    next
      case True
      with h have "z1 i \<le> z2 i" 
        by fast
      also from iK ms Cms have "0 \<le> measure M (C i)" 
        by (auto simp add: measure_space_def positive_def )
      ultimately show ?thesis 
        by (simp add: mult_right_mono)
    qed
  }
  with a2 b2 show ?thesis by (simp add: sum_mono)
qed

lemma sfis_unique: 
  assumes ms: "measure_space M" and a: "a \<in> sfis f M" and b: "b \<in> sfis f M"
  shows "a=b"
proof -
  have "f\<le>f" by (simp add: le_fun_def)
  with assms have "a\<le>b" and "b\<le>a" 
    by (auto simp add: sfis_mono)
  thus ?thesis by simp
qed

text \<open>The integral of characteristic functions, as well as the effect of
  multiplication with a constant, follows directly from the
    definition. Together with a generalization of the addition theorem
    to sums, a less restrictive introduction rule emerges, making
    normal forms obsolete. It is only valid in measure spaces though.\<close>

lemma sfis_char:
  assumes ms: "measure_space M" and mA: "A \<in> measurable_sets M" 
  shows "measure M A \<in> sfis \<chi> A M"
(*<*)proof -
  define R :: "nat \<Rightarrow> 'a set" where "R i = (if i = 0 then A else if i=1 then -A else {})" for i
  define x :: "nat \<Rightarrow> real" where "x i = (if i = 0 then 1 else 0)" for i
  define K :: "nat set" where "K = {0,1}"
  
  from ms mA have Rms: "\<forall>i\<in>K. R i \<in> measurable_sets M" 
    by (simp add: K_def R_def measure_space_def sigma_algebra_def)
  have nn: "nonnegative x" by (simp add: nonnegative_def x_def)
  have un: "(\<Union>i\<in>K. R i) = UNIV" by (simp add: R_def K_def)
  have fin: "finite K" by (simp add: K_def)
  have dis: "\<forall>j1\<in>K. \<forall>j2\<in>K. j1 \<noteq> j2 \<longrightarrow> (R j1) \<inter> (R j2) = {}" by (auto simp add: R_def K_def)
  { fix t
    from un fin dis have "\<chi> A t = (\<Sum>i\<in>K. \<chi> (A \<inter> R i) t)" by (rule char_split)
    also 
    { fix i 
      have "K=K" and "\<chi> (A \<inter> R i) t = x i * \<chi> (R i) t" 
        by (auto simp add: R_def x_def characteristic_function_def)}
    hence "\<dots> = (\<Sum>i\<in>K. x i * \<chi> (R i) t)" by (rule sum.cong)
    finally have "\<chi> A t = (\<Sum>i\<in>K. x i * \<chi> (R i) t)" .
  }
  hence "\<chi> A = (\<lambda>t. \<Sum>i\<in>K. x i * \<chi> (R i) t)" by (simp add: ext)
  
  from this Rms nn fin dis un have "(\<Sum>i\<in>K. x i * measure M (R i)) \<in> sfis \<chi> A M"
    by (rule sfis.base)
  also
  { fix i
    from ms have "K=K" and "x i * measure M (R i) = measure M (A \<inter> R i)" 
      by (auto simp add: R_def x_def measure_space_def positive_def)
  } hence "(\<Sum>i\<in>K. x i * measure M (R i)) = (\<Sum>i\<in>K. measure M (A \<inter> R i))" 
    by (rule sum.cong)
  also from ms un fin dis Rms mA have "\<dots> = measure M A"
    by (rule measure_split[THEN sym]) 
  
  finally show ?thesis .
qed(*>*)
    (*Sums are always problematic, since they use informal notation
    all the time.*)

lemma sfis_times:
  assumes a: "a \<in> sfis f M" and z: "0\<le>z"
  shows "z*a \<in> sfis (\<lambda>w. z*f w) M" (*<*)using a
proof cases
  case (base x A S)
  {
    fix t
    from base have "z*f t = (\<Sum>i\<in>S. z * (x i * \<chi> (A i) t))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>i\<in>S. (z * x i) * \<chi> (A i) t)"
    proof (rule sum.cong)
      show "S = S" ..
      fix i show "z * (x i * \<chi> (A i) t) = (z * x i) * \<chi> (A i) t" by auto
    qed
    finally have "z * f t = (\<Sum>i\<in>S. z * x i * \<chi> (A i) t)" .
  }
  hence zf: "(\<lambda>w. z*f w) = (\<lambda>t. \<Sum>i\<in>S. z * x i * \<chi> (A i) t)" by (simp add: ext)
  
  from z base have "nonnegative (\<lambda>w. z*x w)" by (simp add: nonnegative_def zero_le_mult_iff)
  with base zf have "(\<Sum>i\<in>S. z * x i * measure M (A i)) \<in> sfis (\<lambda>w. z*f w) M" 
    by (simp add: sfis.base)
  also have "(\<Sum>i\<in>S. z * x i * measure M (A i)) = (\<Sum>i\<in>S. z * (x i * measure M (A i)))"
  proof (rule sum.cong)
    show "S = S" ..
    fix i show "(z * x i) * measure M (A i) = z * (x i * measure M (A i))" by auto
  qed
  also from base have "\<dots> = z*a" by (simp add: sum_distrib_left)
  finally show ?thesis .
qed(*>*)


lemma assumes ms: "measure_space M" 
  and a: "\<forall>i\<in>S. a i \<in> sfis (f i) M" and S: "finite S"
  shows sfis_sum: "(\<Sum>i\<in>S. a i) \<in> sfis (\<lambda>t. \<Sum>i\<in>S. f i t) M" (*<*)using S a
proof induct
  case empty
  with ms have "measure M {} \<in> sfis \<chi> {} M"
    by (simp add: measure_space_def sigma_algebra_def sfis_char)
  with ms show ?case
    by (simp add: sum.empty measure_space_def positive_def char_empty)
next
  case (insert s S)
  then have "\<And>t. (\<Sum>i \<in> insert s S. f i t) = f s t + (\<Sum>i\<in>S. f i t)" by simp
  moreover from insert have "(\<Sum>i \<in> insert s S. a i) = a s + (\<Sum>i\<in>S. a i)" by simp
  moreover from insert have "a s \<in> sfis (f s) M" by fast
  moreover from insert have "(\<Sum>i\<in>S. a i) \<in> sfis (\<lambda>t. \<Sum>i\<in>S. f i t) M" by fast
  moreover note ms ultimately show ?case by (simp add: sfis_add ext)
qed(*>*)

(*The introduction rule without normal forms, only in measure_spaces*)
lemma sfis_intro:
  assumes ms: "measure_space M" and Ams: "\<forall>i \<in> S. A i \<in> measurable_sets M" 
  and nn: "nonnegative x" and S: "finite S"
  shows "(\<Sum>i\<in>S. x i * measure M (A i)) \<in> 
  sfis (\<lambda>t. \<Sum>i\<in>(S::nat set). x i * \<chi> (A i) t) M"
proof -
  { fix i assume iS: "i \<in> S"
    with ms Ams have "measure M (A i) \<in> sfis \<chi> (A i) M" 
      by (simp add: sfis_char)
    with nn have "x i * measure M (A i) \<in> sfis (\<lambda>t. x i * \<chi> (A i) t) M" 
      by (simp add: nonnegative_def sfis_times) 
  }
  with ms S show ?thesis 
    by (simp add: sfis_sum)
qed

text\<open>That is nearly all there is to know about simple function
  integral sets. It will be useful anyway to have the next two facts
  available.\<close>

lemma sfis_nn:
  assumes f: "a \<in> sfis f M"
  shows "nonnegative f" (*<*)using f
proof (cases)
  case (base x A S)
  {
    fix t 
    from base have "\<And>i. 0 \<le> x i * \<chi> (A i) t"
      by (simp add: nonnegative_def characteristic_function_def)
    with base have "(\<Sum>i\<in>S. 0) \<le> f t"
      by (simp del: sum.neutral_const sum_constant add: sum_mono)
    hence "0 \<le> f t" by simp
  }
  thus ?thesis by (simp add: nonnegative_def)
qed(*>*)

lemma sum_rv:
  assumes rvs: "\<forall>k\<in>K. (f k) \<in> rv M" and ms: "measure_space M"
  shows "(\<lambda>t. \<Sum>k\<in>K. f k t) \<in> rv M"
(*<*)proof (cases "finite K")
  case False
  hence "(\<lambda>t. \<Sum>k\<in>K. f k t) = (\<lambda>t. 0)"
    by simp
  with ms show ?thesis
    by (simp add: const_rv)
next
  case True
  from this rvs show ?thesis 
  proof (induct)
    case empty
    have "(\<lambda>t. \<Sum>k\<in>{}. f k t) = (\<lambda>t. 0)"
      by simp
    with ms show ?case
      by (simp add: const_rv)
  next
    case (insert x F)
    hence "(\<lambda>t. \<Sum>k\<in>insert x F. f k t) = (\<lambda>t. f x t + (\<Sum>k\<in>F. f k t))"
      by simp
    also
    from insert have "f x \<in> rv M" and "(\<lambda>t. (\<Sum>k\<in>F. f k t)) \<in> rv M"
      by simp_all
    ultimately show ?case 
      by (simp add: rv_plus_rv)
  qed
qed(*>*)

lemma sfis_rv: 
  assumes ms: "measure_space M" and f: "a \<in> sfis f M"
  shows "f \<in> rv M" using f
proof (cases)
  case (base x A S)
  hence "f = (\<lambda>t. \<Sum>i\<in>S. x i * \<chi> (A i) t)" 
    by simp
  also
  { fix i
    assume "i \<in> S"
    with base have "A i \<in> measurable_sets M"
     by simp
    with ms have "(\<lambda>t. x i * \<chi> (A i) t) \<in> rv M"
      by (simp add: char_rv const_rv rv_times_rv)
  } with ms
  have "\<dots> \<in> rv M"
    by (simp add: sum_rv)
  ultimately show ?thesis 
    by simp
qed(*>*)(*>*)(*nonnegative function integral set*)(*>*)

subsection \<open>Nonnegative Functions\<close>

text \<open>
  \label{nnfis}There is one more important fact about \<open>sfis\<close>, easily the
  hardest one to see. It is about the relationship with monotone
  convergence and paves the way for a sensible definition of \<open>nnfis\<close>, the nonnegative function integral sets, enabling
  monotonicity and thus uniqueness. A reasonably concise formal proof could
  fortunately be achieved in spite of the nontrivial ideas involved
  --- compared for instance to the intuitive but hard-to-formalize
  \<open>sfis_present\<close>. A small lemma is needed to ensure that the
  inequation, which depends on an arbitrary $z$ strictly between
  $0$ and $1$, carries over to $z=1$, thereby eliminating $z$ in the end.\<close>

lemma real_le_mult_sustain:
  assumes zr: "\<And>z. \<lbrakk>0<z; z<1\<rbrakk> \<Longrightarrow> z * r \<le> y"
  shows "r \<le> (y::real)"(*<*)
proof (cases "0<y")
  case False
  
  have "0<(1::real)" 
    by simp
  hence "\<exists>z::real. 0<z \<and> z<1" 
    by (rule dense)
  then obtain z::real where 0: "0<z" and 1: "z<1" 
    by fast
  with zr have a: "z*r \<le> y"
    by simp
  
  also
  from False have "y\<le>0" 
    by simp
  with a have "z*r \<le> 0"
    by simp
  with 0 1 have z1: "z\<le>1" and r0: "r\<le>0"
    by (simp_all add: mult_le_0_iff)
  hence "1*r \<le> z*r" 
    by (rule mult_right_mono_neg)
  
  ultimately show "r\<le>y" 
    by simp
  
next
  case True
  {
  assume yr: "y < r"
  then have "\<exists>q. y<q \<and> q<r"
    by (rule dense)
  then obtain q where yq: "y<q" and q: "q<r" 
    by fast
  
  from yr True have r0: "0<r"
    by simp
  with q have "q/r < 1" 
    by (simp add: pos_divide_less_eq)
  
  also from True yq r0 have "0<q/r"
    by (simp add: zero_less_divide_iff)
  
  ultimately have "(q/r)*r\<le>y" using zr
    by force

  with r0 have "q\<le>y" 
    by simp
  with yq have False
    by simp
  }
  thus ?thesis 
    by force
qed(*>*)
    
lemma sfis_mon_conv_mono: 
  assumes uf: "u\<up>f" and xu: "\<And>n. x n \<in> sfis (u n) M" and xy: "x\<up>y"
    and sr: "r \<in> sfis s M" and sf: "s \<le> f" and ms: "measure_space M"
  shows "r \<le> y" (*This is Satz 11.1 in Bauer*) using sr 
proof cases
  case (base a A S)
  note base_a = this
  
  { fix z assume znn: "0<(z::real)" and z1: "z<1"
    define B where "B n = {w. z*s w \<le> u n w}" for n

    { fix n
      note ms also
      from xu have xu: "x n \<in> sfis (u n) M" .
      hence nnu: "nonnegative (u n)" 
        by (rule sfis_nn)
      from ms xu have "u n \<in> rv M" 
        by (rule sfis_rv)
      moreover from ms sr have "s \<in> rv M" 
        by (rule sfis_rv)
      with ms have "(\<lambda>w. z*s w) \<in> rv M" 
        by (simp add: const_rv rv_times_rv)
      ultimately have "B n \<in> measurable_sets M" 
        by (simp add: B_def rv_le_rv_measurable)
      with ms base have ABms: "\<forall>i\<in>S. (A i \<inter> B n) \<in> measurable_sets M" 
        by (auto simp add: measure_space_def sigma_algebra_inter)

      from xu have "z*(\<Sum>i\<in>S. a i * measure M (A i \<inter> B n)) \<le> x n" 
      proof (cases)
        case (base c C R)
        { fix t
          { fix i
            have "S=S" and "a i * \<chi> (A i \<inter> B n) t = \<chi> (B n) t * (a i * \<chi> (A i) t)" 
              by (auto simp add: characteristic_function_def) }
          hence "(\<Sum>i\<in>S. a i * \<chi> (A i \<inter> B n) t) = 
            (\<Sum>i\<in>S. \<chi> (B n) t * (a i * \<chi> (A i) t))" 
            by (rule sum.cong)
          hence "z*(\<Sum>i\<in>S. a i * \<chi> (A i \<inter> B n) t) = 
            z*(\<Sum>i\<in>S. \<chi> (B n) t * (a i * \<chi> (A i) t))" 
            by simp
          also have "\<dots> = z * \<chi> (B n) t * (\<Sum>i\<in>S. a i * \<chi> (A i) t)" 
            by (simp add: sum_distrib_left[THEN sym])
          also 
          from sr have "nonnegative s" by (simp add: sfis_nn)
          with nnu B_def base_a
          have "z * \<chi> (B n) t * (\<Sum>i\<in>S. a i * \<chi> (A i) t) \<le> u n t" 
            by (auto simp add: characteristic_function_def nonnegative_def)
          finally have "z*(\<Sum>i\<in>S. a i * \<chi> (A i \<inter> B n) t) \<le> u n t" .
        }
         
        also
        from ms base_a znn ABms have
          "z*(\<Sum>i\<in>S. a i * measure M (A i \<inter> B n)) \<in> 
          sfis (\<lambda>t. z*(\<Sum>i\<in>S. a i * \<chi> (A i \<inter> B n) t)) M" 
          by (simp add: sfis_intro sfis_times)
        moreover note xu ms
        ultimately show ?thesis 
          by (simp add: sfis_mono le_fun_def)
      qed
      note this ABms
    }
    hence 1: "\<And>n. z * (\<Sum>i\<in>S. a i * measure M (A i \<inter> B n)) \<le> x n"
      and ABms: "\<And>n. \<forall>i\<in>S. A i \<inter> B n \<in> measurable_sets M" .
  
    have Bun: "(\<lambda>n. B n)\<up>UNIV"
    proof (unfold mon_conv_set_def, rule)
      { fix n
        from uf have um: "u n \<le> u (Suc n)" 
          by (simp add: mon_conv_real_fun_def)
        { 
          fix w
          assume "z*s w \<le> u n w"
          also from um have "u n w \<le> u (Suc n) w" 
            by (simp add: le_fun_def)
          finally have "z*s w \<le> u (Suc n) w" . 
        }
        hence "B n \<le> B (Suc n)" 
          by (auto simp add: B_def)
      } 
      thus " \<forall>n. B n \<subseteq> B (Suc n)" 
        by fast
    
      { fix t
        have "\<exists>n. z*s t \<le> u n t"
        proof (cases "s t = 0")
          case True
          fix n
          from True have "z*s t = 0" 
            by simp
          also from xu have "nonnegative (u n)" 
            by (rule sfis_nn)
          hence "0 \<le> u n t" 
            by (simp add: nonnegative_def)
          finally show ?thesis 
            by rule
                   
        next
          case False
          from sr have "nonnegative s" 
            by(rule sfis_nn)
          hence "0 \<le> s t" 
            by (simp add: nonnegative_def)
          with False have "0 < s t" 
            by arith
          with z1 have "z*s t < 1*s t" 
            by (simp only: mult_strict_right_mono)
          also from sf have "\<dots> \<le> f t" 
            by (simp add: le_fun_def) 
          finally have "z * s t < f t" .
            (*Next we have to prove that u grows beyond z*s t*)
          also from uf have "(\<lambda>m. u m t)\<up>f t" 
            by (simp add: realfun_mon_conv_iff)
          ultimately have "\<exists>n.\<forall>m. n\<le>m \<longrightarrow> z*s t < u m t" 
            by (simp add: real_mon_conv_outgrow) 
          hence "\<exists>n. z*s t < u n t" 
            by fast
          thus ?thesis 
            by (auto simp add: order_less_le)
        qed

        hence "\<exists>n. t \<in> B n" 
          by (simp add: B_def)
        hence "t \<in> (\<Union>n. B n)" 
          by fast
      }
      thus "UNIV=(\<Union>n. B n)" 
        by fast
    qed 
    
    { fix j assume jS: "j \<in> S"
      note ms
      also
      from jS ABms have "\<And>n. A j \<inter> B n \<in> measurable_sets M" 
        by auto
      moreover
      from Bun have "(\<lambda>n. A j \<inter> B n)\<up>(A j)" 
        by (auto simp add: mon_conv_set_def)
      ultimately have "(\<lambda>n. measure M (A j \<inter> B n)) \<longlonglongrightarrow> measure M (A j)" 
        by (rule measure_mon_conv)
      
      hence "(\<lambda>n. a j * measure M (A j \<inter> B n)) \<longlonglongrightarrow> a j * measure M (A j)" 
        by (simp add: tendsto_const tendsto_mult)
    }
    hence "(\<lambda>n. \<Sum>j\<in>S. a j * measure M (A j \<inter> B n)) 
      \<longlonglongrightarrow> (\<Sum>j\<in>S. a j * measure M (A j))" 
      by (rule tendsto_sum)
    hence "(\<lambda>n. z* (\<Sum>j\<in>S. a j * measure M (A j \<inter> B n)))
      \<longlonglongrightarrow> z*(\<Sum>j\<in>S. a j * measure M (A j))" 
      by (simp add: tendsto_const tendsto_mult)
    
    with 1 xy base have "z*r \<le> y" 
      by (auto simp add: LIMSEQ_le mon_conv_real_def) 
  }
  hence zr: "\<And>z. 0 < z \<Longrightarrow> z < 1 \<Longrightarrow> z * r \<le> y" .
  thus ?thesis by (rule real_le_mult_sustain)
qed

text \<open>Now we are ready for the second step. The integral of a
  monotone limit of functions is the limit of their
  integrals. Note that this last limit has to exist in the
  first place, since we decided not to use infinite values. Backed
  by the last theorem and the preexisting knowledge about limits, the
  usual basic properties are
  straightforward.\<close>

inductive_set
  nnfis:: "('a \<Rightarrow> real) \<Rightarrow> ('a set set * ('a set \<Rightarrow> real)) \<Rightarrow> real set"
  for f :: "'a \<Rightarrow> real" and M :: "'a set set * ('a set \<Rightarrow> real)"
  where
  base: "\<lbrakk>u\<up>f; \<And>n. x n \<in> sfis (u n) M; x\<up>y\<rbrakk> \<Longrightarrow> y \<in> nnfis f M"

lemma sfis_nnfis:
  assumes s: "a \<in> sfis f M"
  shows "a \<in> nnfis f M"
(*<*)proof -
  { fix t
    have "(\<lambda>n. f t)\<up>f t" by (simp add: mon_conv_real_def tendsto_const)
  } hence "(\<lambda>n. f)\<up>f" by (simp add: realfun_mon_conv_iff)
  also 
  from s have "\<And>n. a \<in> sfis f M" .
  moreover have "(\<lambda>n. a)\<up>a" by (simp add: mon_conv_real_def tendsto_const)
  
  ultimately show ?thesis by (rule nnfis.base)
qed(*>*)


lemma nnfis_times: 
  assumes ms: "measure_space M" and a: "a \<in> nnfis f M" and nn: "0\<le>z"
  shows "z*a \<in> nnfis (\<lambda>w. z*f w) M" (*<*)using a
proof (cases)
  case (base u x)
  with nn have "(\<lambda>m w. z*u m w)\<up>(\<lambda>w. z*f w)" by (simp add: realfun_mon_conv_times)
  also from nn base have "\<And>m. z*x m \<in> sfis (\<lambda>w. z*u m w) M" by (simp add: sfis_times)
  moreover from a nn base have "(\<lambda>m. z*x m)\<up>(z*a)" by (simp add: real_mon_conv_times)
  ultimately have "z*a \<in> nnfis (\<lambda>w. z*f w) M" by (rule nnfis.base)
  
  with base show ?thesis by simp
qed(*>*)


lemma nnfis_add:
  assumes ms: "measure_space M" and a: "a \<in> nnfis f M" and b: "b \<in> nnfis g M"
  shows "a+b \<in> nnfis (\<lambda>w. f w + g w) M" (*<*)using a
proof (cases)
  case (base u x)
  note base_u = this
  from b show ?thesis 
  proof cases
    case (base v r)
    with base_u have "(\<lambda>m w. u m w + v m w)\<up>(\<lambda>w. f w + g w)"
      by (simp add: realfun_mon_conv_add)
    also
    from ms base_u base have "\<And>n. x n + r n \<in> sfis (\<lambda>w. u n w + v n w) M" by (simp add: sfis_add) 
    moreover from ms base_u base have "(\<lambda>m. x m + r m)\<up>(a+b)" by (simp add: real_mon_conv_add)
   
    ultimately have "a+b \<in> nnfis (\<lambda>w. f w + g w) M" by (rule nnfis.base)
    with a b show ?thesis by simp
  qed
qed(*>*)


lemma assumes ms: "measure_space M" and a: "a \<in> nnfis f M" 
  and b: "b \<in> nnfis g M" and fg: "f\<le>g"
  shows nnfis_mono: "a \<le> b" using a
proof (cases)
  case (base u x)
  note base_u = this
  from b show ?thesis 
  proof (cases)
    case (base v r)
    { fix m
      from base_u base have "u m \<le> f" 
        by (simp add: realfun_mon_conv_le) 
      also note fg finally have "u m \<le> g" .
      with ms base_u base have "v\<up>g" and  "\<And>n. r n \<in> sfis (v n) M" and "r\<up>b" 
          and "x m \<in> sfis (u m) M" and "u m \<le> g" and "measure_space M"
        by simp_all
      hence "x m \<le> b" 
        by (rule sfis_mon_conv_mono)
    }
    with ms base_u base show "a \<le> b" 
      by (auto simp add: mon_conv_real_def LIMSEQ_le_const2)
  qed
qed

corollary nnfis_unique: 
  assumes ms: "measure_space M" and a: "a \<in> nnfis f M" and b: "b \<in> nnfis f M"
  shows "a=b" (*<*)
proof -
  have "f\<le>f" ..
  with assms have "a\<le>b" and "b\<le>a" 
    by (auto simp add: nnfis_mono)
  thus ?thesis by simp
qed(*>*)


text\<open>There is much more to prove about nonnegative integration. Next
  up is a classic theorem by Beppo Levi, the monotone convergence
  theorem. In essence, it says that the introduction rule for \<open>nnfis\<close> holds not only for sequences of simple functions, but for any
  sequence of nonnegative integrable functions. It should be mentioned that this theorem cannot be
  formulated for the Riemann integral. We prove it by
  exhibiting a sequence of simple functions that converges to the same
  limit as the original one and then applying the introduction
  rule. 

  The construction and properties of the sequence are slightly intricate. By definition, for any $f_n$ in the original sequence,
  there is a sequence $(u_{m n})_{m\in\mathbb{N}}$ of simple functions converging to it.   
  The $n$th element of the new sequence is the upper closure of the
  $n$th elements of the first $n$ sequences.\<close>

definition (*The upper closure?*)
  upclose:: "('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)" where
  "upclose f g = (\<lambda>t. max (f t) (g t))" 

primrec
  mon_upclose_help :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> real)" ("muh") where
  "muh 0 u m = u m 0"
| "muh (Suc n) u m = upclose (u m (Suc n)) (muh n u m)" 

definition
  mon_upclose (*See Bauer p. 68*) :: "(nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> real)" ("mu") where
  "mu u m = muh m u m"

lemma sf_norm_help:
  assumes fin: "finite K" and jK: "j \<in> K" and tj: "t \<in> C j" and iK: "\<forall>i\<in>K-{j}. t \<notin> C i"
  shows "(\<Sum>i\<in>K. (z i) * \<chi> (C i) t) = z j"
(*<*)proof -
  from jK have "K = insert j (K-{j})"  by blast
  moreover
  from fin have finat2: "finite (K-{j})" and "j \<notin> (K-{j})"  by simp_all
  hence "(\<Sum>i\<in>insert j (K-{j}). (z i) * \<chi> (C i) t) = (z j * \<chi> (C j) t) + (\<Sum>i\<in>K-{j}. (z i) * \<chi> (C i) t)"
    by (rule sum.insert)
  moreover from tj have "\<dots> = z j + (\<Sum>i\<in>K-{j}. (z i) * \<chi> (C i) t)"
    by (simp add: characteristic_function_def)
  moreover
  { from iK have "\<forall>i\<in>K-{j}. (z i) * \<chi> (C i) t = 0"
      by (auto simp add: characteristic_function_def)
  }
  hence "\<dots> = z j"  by (simp add:sum.neutral)
  ultimately show ?thesis by simp
qed(*>*)

lemma upclose_sfis: 
  assumes ms: "measure_space M" and f: "a \<in> sfis f M" and g: "b \<in> sfis g M" 
  shows "\<exists>c. c \<in> sfis (upclose f g) M" (*<*)
proof -     
  from assms have 
    "\<exists> z1 z2 C K. f = (\<lambda>t. \<Sum>i\<in>(K::nat set). z1 i * \<chi> (C i) t) \<and> 
    g = (\<lambda>t. \<Sum>i\<in>K. z2 i * \<chi> (C i) t) \<and> a = (\<Sum>i\<in>K. z1 i * measure M (C i))
    \<and> b = (\<Sum>i\<in>K. z2 i * measure M (C i))
    \<and> finite K \<and> (\<forall>i\<in>K. \<forall>j\<in>K. i \<noteq> j \<longrightarrow> C i \<inter> C j = {})
    \<and> (\<forall>i \<in> K. C i \<in> measurable_sets M) \<and> (\<Union>i\<in>K. C i) = UNIV
    \<and> nonnegative z1 \<and> nonnegative z2"
    by (rule sfis_present)
        
  then obtain z1 z2 C K where f: "f = (\<lambda>t. \<Sum>i\<in>(K::nat set). z1 i * \<chi> (C i) t)" 
    and g: "g = (\<lambda>t. \<Sum>i\<in>K. z2 i * \<chi> (C i) t)" 
    and a2: "a = (\<Sum>i\<in>K. z1 i * measure M (C i))"
    and b2: "b = (\<Sum>i\<in>K. z2 i * measure M (C i))"
    and CK: "finite K \<and> (\<forall>i\<in>K. \<forall>j\<in>K. i \<noteq> j \<longrightarrow> C i \<inter> C j = {}) \<and> 
    (\<forall>i\<in>K. C i \<in> measurable_sets M) \<and> \<Union>(C ` K) = UNIV"
    and z1: "nonnegative z1" and z2: "nonnegative z2"
    by auto
  { fix t
    from CK obtain j where jK: "j \<in> K" and tj: "t \<in> C j"
      by force
    with CK have iK: "\<forall>i\<in>K-{j}. t \<notin> C i"
      by auto
    from f and g have "max (f t) (g t) = max (\<Sum>i\<in>K. (z1 i) * \<chi> (C i) t) (\<Sum>i\<in>K. (z2 i) * \<chi> (C i) t)" 
      by simp
    also
    from CK jK iK tj have "\<dots> = max (z1 j) (z2 j)"
      by (simp add: sf_norm_help)
    also 
    from CK jK iK tj have "\<dots> = (\<Sum>i\<in>K. (max (z1 i) (z2 i)) * \<chi> (C i) t)"
      by (simp add: sf_norm_help)
    finally have "max (f t) (g t) = (\<Sum>i\<in>K. max (z1 i) (z2 i) * \<chi> (C i) t)" .
  }
  hence "upclose f g = (\<lambda>t. (\<Sum>i\<in>K. max (z1 i) (z2 i) * \<chi> (C i) t))"
    by (simp add: upclose_def)
  also 
  { from z1 z2 have "nonnegative (\<lambda>i. max (z1 i) (z2 i))"
      by (simp add: nonnegative_def max_def)
  }
  with ms CK have "(\<Sum>i\<in>K. max (z1 i) (z2 i) * measure M (C i)) \<in> sfis \<dots> M"
    by (simp add: sfis_intro)
  ultimately show ?thesis
    by auto
qed(*>*)

lemma mu_sfis:
  assumes u: "\<And>m n. \<exists>a. a \<in> sfis (u m n) M" and ms: "measure_space M"
  shows "\<exists>c. \<forall>m. c m \<in> sfis (mu u m) M"
(*<*)proof -
  { fix m
    from u ms have "\<And>n. \<exists>c. c \<in> sfis (muh m u n) M"
    proof (induct m)
      case 0 
      from u show ?case
        by force
    next
      case (Suc m)
      { fix n
        from Suc obtain a b where "a \<in> sfis (muh m u n) M" and "b \<in> sfis (u n (Suc m)) M"
          by force
        with ms u have "\<exists>a. a \<in> sfis (muh (Suc m) u n) M" 
          by (simp add: upclose_sfis)
      }
      thus ?case
        by force
    qed
    hence "\<exists>c. c \<in> sfis (mu u m) M"
      by (simp add: mon_upclose_def)
  } hence "\<forall>m. \<exists>c. c \<in> sfis (mu u m) M"
    by simp
  thus ?thesis 
    by (rule choice)
qed(*>*)
      
      
lemma mu_help:
  assumes uf: "\<And>n. (\<lambda>m. u m n)\<up>(f n)" and fh: "f\<up>h"
  shows "(mu u)\<up>h" and "\<And>n. mu u n \<le> f n"
proof -
  show mu_le: "\<And>n. mu u n \<le> f n"  
  proof (unfold mon_upclose_def)
    fix n
    show "\<And>m. muh n u m \<le> f n"
    proof (induct n)
      case (0 m) 
      from uf have "u m 0 \<le> f 0" 
        by (rule realfun_mon_conv_le)
      thus ?case by simp
    next
      case (Suc n m)
      { fix t
        from Suc have "muh n u m t \<le> f n t" 
          by (simp add: le_fun_def)
        also from fh have "f n t \<le> f (Suc n) t" 
          by (simp add: realfun_mon_conv_iff mon_conv_real_def)
        also from uf have "(\<lambda>m. u m (Suc n) t)\<up>(f (Suc n) t)" 
          by (simp add: realfun_mon_conv_iff)
        hence "u m (Suc n) t \<le> f (Suc n) t" 
          by (rule real_mon_conv_le)
        ultimately have "muh (Suc n) u m t \<le> f (Suc n) t" 
          by (simp add: upclose_def)
      }
      thus ?case by (simp add: le_fun_def)
    qed
  qed
      (*isotony (?) of mu u is next to prove*)
  { fix t
    { fix m n 
      have "muh n u m t \<le> muh (Suc n) u m t"
        by (simp add: upclose_def)
    }
    hence pos1: "\<And>m n. muh n u m t \<le> muh (Suc n) u m t" .

    from uf have uiso: "\<And>m n. u m n t \<le> u (Suc m) n t"
      by (simp add: realfun_mon_conv_iff mon_conv_real_def)

    have iso: "\<And>n. mu u n t \<le> mu u (Suc n) t"
    proof (unfold mon_upclose_def)
      fix n           
      have "\<And>m. muh n u m t \<le> muh n u (Suc m) t"
      proof (induct n)
        case 0 from uiso show ?case 
          by (simp add: upclose_def le_max_iff_disj)
      next
        case (Suc n m)
        
        from Suc have "muh n u m t \<le> muh n u (Suc m) t" .         
        also from uiso have "u m (Suc n) t \<le> u (Suc m) (Suc n) t" .

        ultimately show ?case 
          by (auto simp add: upclose_def le_max_iff_disj)
      qed
      note this [of n] also note pos1 [of n "Suc n"]
      finally show "muh n u n t \<le> muh (Suc n) u (Suc n) t" .
    qed

    also 
    
    { fix n
      from mu_le [of n]
      have "mu u n t \<le> f n t" 
        by (simp add: le_fun_def) 
      also
      from fh have "(\<lambda>n. f n t)\<up>h t" 
        by (simp add: realfun_mon_conv_iff)      
      hence "f n t \<le> h t" 
        by (rule real_mon_conv_le)
      finally have "mu u n t \<le> h t" .
    }
    
    ultimately have "\<exists>l. (\<lambda>n. mu u n t)\<up>l \<and> l \<le> h t" 
      by (rule real_mon_conv_bound)
    then obtain l where 
      conv: "(\<lambda>n. mu u n t)\<up>l" and lh: "l \<le> h t" 
      by (force simp add: real_mon_conv_bound)
 
    { fix n::nat
      { fix m assume le: "n \<le> m"
        hence "u m n t \<le> mu u m t" 
        proof (unfold mon_upclose_def) 
          have "u m n t \<le> muh n u m t"
            by (induct n) (auto simp add: upclose_def le_max_iff_disj)
          also 
          from pos1 have "incseq (\<lambda>n. muh n u m t)" 
            by (simp add: incseq_Suc_iff)
          hence "muh n u m t \<le> muh (n+(m-n)) u m t"
            unfolding incseq_def by simp
          with le have "muh n u m t \<le> muh m u m t" 
            by simp
          finally show "u m n t \<le> muh m u m t" .
        qed
      } 
      hence "\<exists>N. \<forall>m. N \<le> m \<longrightarrow> u m n t \<le> mu u m t"
        by blast
      also from uf have "(\<lambda>m. u m n t) \<longlonglongrightarrow> f n t" 
        by (simp add: realfun_mon_conv_iff mon_conv_real_def)
      moreover 
      from conv have "(\<lambda>n. mu u n t) \<longlonglongrightarrow> l"
        by (simp add: mon_conv_real_def)
      ultimately have "f n t \<le> l" 
        by (simp add: LIMSEQ_le)
    } 
    also from fh have "(\<lambda>n. f n t) \<longlonglongrightarrow> h t" 
      by (simp add: realfun_mon_conv_iff mon_conv_real_def)
    ultimately have "h t \<le> l" 
      by (simp add: LIMSEQ_le_const2)
    
    with lh have "l = h t" 
      by simp
    with conv have "(\<lambda>n. mu u n t)\<up>(h t)" 
      by simp
  }
  with mon_upclose_def show "mu u\<up>h" 
    by (simp add: realfun_mon_conv_iff)
qed
(* The Beppo Levi - Theorem *)
theorem nnfis_mon_conv:
  assumes fh: "f\<up>h" and xf: "\<And>n. x n \<in> nnfis (f n) M" and xy: "x\<up>y"
  and ms: "measure_space M"
  shows "y \<in> nnfis h M"
proof -
  define u where "u n = (SOME u. u\<up>(f n) \<and> (\<forall>m. \<exists>a. a \<in> sfis (u m) M))" for n
  { fix n
    from xf[of n] have "\<exists>u. u\<up>(f n) \<and> (\<forall>m. \<exists>a. a \<in> sfis (u m) M)" (is "\<exists>x. ?P x")
    proof (cases)
      case (base r a)
      hence "r\<up>(f n)" and "\<And>m. \<exists>a. a \<in> sfis (r m) M" by auto
      thus ?thesis by fast
    qed
    hence "?P (SOME x. ?P x)"
      by (rule someI_ex)
    with u_def have "?P (u n)" 
      by simp
  } also
  define urev where "urev m n = u n m" for m n
  ultimately have uf: "\<And>n. (\<lambda>m. urev m n)\<up>(f n)" 
    and sf: "\<And>n m. \<exists>a. a \<in> sfis (urev m n) M"
    by auto
  
  from uf fh have up: "mu urev\<up>h" 
    by (rule mu_help) (*Could split the mu_help lemma in two*)
  from uf fh have le: "\<And>n. mu urev n \<le> f n" 
    by (rule mu_help)
  from sf ms obtain c where sf2: "\<And>m. c m \<in> sfis (mu urev m) M" 
    by (force simp add: mu_sfis) 

  { fix m
    from sf2 have "c m \<in> nnfis (mu urev m) M" 
      by (rule sfis_nnfis)
    with ms le[of m] xf[of m] have "c m \<le> x m" 
      by (simp add: nnfis_mono)    
  } hence "c \<le> x" by (simp add: le_fun_def)
  also
  { fix m note ms also
    from up have "mu urev m \<le> mu urev (Suc m)" 
      by (simp add: mon_conv_real_fun_def)
    moreover from sf2 have "c m \<in> sfis (mu urev m) M" 
      and "c (Suc m) \<in> sfis (mu urev (Suc m)) M" 
      by fast+
    ultimately have "c m \<le> c (Suc m)" 
      by (simp add: sfis_mono)
  }
  moreover note xy
  ultimately have "\<exists>l. c\<up>l \<and> l \<le> y" 
    by (simp add: real_mon_conv_dom)
  then obtain l where cl: "c\<up>l" and ly: "l \<le> y" 
    by fast
  
  from up sf2 cl have int: "l \<in> nnfis h M" 
    by (rule nnfis.base)

  { fix n 
    from fh have "f n \<le> h" 
      by (rule realfun_mon_conv_le) 
    with ms xf[of n] int have "x n \<le> l" 
      by (rule nnfis_mono)
  } with xy have "y \<le> l" 
    by (auto simp add: mon_conv_real_def LIMSEQ_le_const2)

  with ly have "l=y" 
    by simp
  with int show ?thesis 
    by simp
qed

text\<open>Establishing that only nonnegative functions may arise this way
  is a triviality.\<close>

lemma nnfis_nn: assumes "a \<in> nnfis f M"
  shows "nonnegative f" (*<*)using assms
proof cases
  case (base u x)
  {fix t
    { fix n
      from base have "x n \<in> sfis (u n) M" by fast
      hence "nonnegative (u n)" by (rule sfis_nn)
      hence "0 \<le> u n t" by (simp add: nonnegative_def)
    }
    also from base have "(\<lambda>n. u n t)\<longlonglongrightarrow>f t" by (simp add: realfun_mon_conv_iff mon_conv_real_def)
    ultimately have "0 \<le> f t" by (simp add: LIMSEQ_le_const)
  } thus ?thesis by (simp add: nonnegative_def)
qed(*>*)(*>*)

subsection \<open>Integrable Functions\<close>

text\<open>
  Before we take the final step of defining integrability and the
  integral operator, we should first clarify what kind of functions we
  are able to integrate up to now. It is easy to see that all nonnegative integrable
  functions are random variables.\<close> 

lemma assumes (*<*)ms:(*>*) "measure_space M" and (*<*)f:(*>*) "a \<in> nnfis f M"
  shows nnfis_rv: "f \<in> rv M" (*<*)using f
proof (cases)
  case (base u x)
  { fix n
    from base have "x n \<in> sfis (u n) M"
      by simp
    with ms have "u n \<in> rv M" 
      by (simp add: sfis_rv)
  }
  also from base
  have "u\<up>f" 
    by simp
  ultimately show ?thesis
    by (rule mon_conv_rv)
qed(*>*)

text\<open>The converse does not hold of course, since there are measurable
  functions whose integral is infinite. Regardless, it is possible to
  approximate any measurable function using simple
  step-functions. This means that all nonnegative random variables are quasi
  integrable, as the property is sometimes called, and brings forth the fundamental
  insight that a nonnegative function is integrable if and only if it is
  measurable and the integrals of the simple functions that
  approximate it converge monotonically. Technically, the proof is rather
  complex, involving many properties of real numbers.\<close>(*<*)



declare zero_le_power [simp]
(*>*)
lemma assumes (*<*)ms:(*>*) "measure_space M" and (*<*)f(*>*): "f \<in> rv M" and (*<*)nn:(*>*) "nonnegative f"
  shows rv_mon_conv_sfis: "\<exists>u x. u\<up>f \<and> (\<forall>n. x n \<in> sfis (u n) M)"
(*<*)proof (rule+)
    (*We don't need the greater case in the book, since our functions are real*)
  define A where "A n i = {w. real i/(2::real)^n \<le> f w} \<inter> {w. f w < real (Suc i)/(2::real)^n}" for n i
  define u where "u n t = (\<Sum>i\<in>{..<(n*2^n)}-{0}. (real i/(2::real)^n)*\<chi> (A n i) t)"  for n t
  define x where "x n = (\<Sum>i\<in>{..<(n*2^n)}-{0}. (real i/(2::real)^n)*measure M (A n i))" for n
  
  { fix n 
    note ms
    also
    { fix i::nat
      from ms f have "{w. real i/(2::real)^n \<le> f w} \<in> measurable_sets M" 
        by (simp_all add: rv_ge_iff)
      also from ms f have "{w. f w < real (Suc i)/(2::real)^n} \<in> measurable_sets M" 
        by (simp add: rv_less_iff)
      moreover note  ms
      ultimately have "A n i \<in> measurable_sets M" 
        by (simp add: A_def measure_space_def sigma_algebra_inter)
    } hence "\<forall>i\<in>{..<(n*2^n)}-{0}. A n i \<in> measurable_sets M" by fast
      moreover
    { fix i::nat
      have "0 \<le> real i" 
        by simp
      also have "0 \<le> (2::real)^n" 
        by simp
      ultimately have "0 \<le> real i/(2::real)^n" 
        by (simp add: zero_le_divide_iff)
    } hence "nonnegative (\<lambda>i::nat. real i/(2::real)^n)" 
      by (simp add: nonnegative_def)
   (*   This is a little stronger than it has to be, btw.. x i must only be nn for i in S *)
      
    moreover have "finite ({..<(n*2^n)}-{0})"
      by simp
    ultimately have "x n \<in> sfis (u n) M" 
      by (simp only: u_def [abs_def] x_def sfis_intro)
  } thus "\<forall>n. x n \<in> sfis (u n) M" 
    by simp
  
  show "u\<up>f"
  proof -
    { fix t

      { fix m i assume tai: "t \<in> A m i" and iS: "i \<in> {..<(m*2^m)}"
            
        have usum: "u m t = (\<Sum>j\<in>{..<(m*2^m)}-{0}. real j / (2::real)^m * \<chi> (A m j) t)"
          by (simp add: u_def)
            
        { fix j assume ne: "i \<noteq> j" 
          have "t \<notin> A m j"
          proof (cases "i < j")
            case True
            from tai have "f t < real (Suc i) / (2::real)^m"
              by (simp add: A_def)
            also
            from True have "real (Suc i)/(2::real)^m \<le> real j/(2::real)^m"
              by (simp add: divide_inverse) 
            finally
            show ?thesis 
              by (simp add: A_def)
            
          next
            case False
            with ne have no: "j<i" 
              by arith
            hence "real (Suc j)/(2::real)^m \<le> real i/(2::real)^m"
              by (simp add: divide_inverse)
            also
            from tai have "real i / (2::real)^m \<le> f t"
              by (simp add: A_def)
            
            finally show ?thesis 
              by (simp add: A_def order_less_le)
          qed
        }
        hence "\<And>j. i \<noteq> j \<Longrightarrow> \<chi> (A m j) t = 0"
          by (simp add: characteristic_function_def)
        hence "\<And>j. j\<in>{..<(m*2^m)}-{0}-{i} \<Longrightarrow>  real j / (2::real)^m * \<chi> (A m j) t = 0"
          by force
        with refl have "(\<Sum>j\<in>{..<(m*2^m)}-{0}-{i}. real j / (2::real)^m * \<chi> (A m j) t) = 
          (\<Sum>j\<in>{..<(m*2^m)}-{0}-{i}. 0)" 
          by (rule sum.cong)
        also have "\<dots> = 0"
          by (rule sum.neutral_const)
        finally have sum0: "(\<Sum>j\<in>{..<(m*2^m)}-{0}-{i}. real j / (2::real)^m * \<chi> (A m j) t) = 0" .
        
        have "u m t = real i / (2::real)^m"
        proof (cases "i=0")
          case True
          hence "i \<notin> {..<(m*2^m)}-{0}"
            by simp
          hence "{..<(m*2^m)}-{0} = {..<(m*2^m)}-{0}-{i}"
            by simp
          with usum sum0 have "u m t = 0" 
            by simp
          also from True have "\<dots> = real i / (2::real)^m * \<chi> (A m i) t"
            by simp
          finally show ?thesis using tai
            by (simp add: characteristic_function_def)
        next
          case False
          with iS have iS: "i \<in> {..<(m*2^m)}-{0}"
            by simp
          note usum  
          also 
          have fin: "finite ({..<(m*2^m)}-{0}-{i})" 
            by simp
          from iS have ins: "{..<(m*2^m)}-{0} = insert i
            ({..<(m*2^m)}-{0}-{i})"
            by auto
          have "i \<notin> ({..<(m*2^m)}-{0}-{i})" 
            by simp
          
          with fin have "(\<Sum>j\<in>insert i ({..<(m*2^m)}-{0}-{i}). real j / (2::real)^m * \<chi> (A m j) t)
            = real i / (2::real)^m * \<chi> (A m i) t +
            (\<Sum>j\<in>{..<(m*2^m)}-{0}-{i}. real j / (2::real)^m * \<chi> (A m j) t)"
            by (rule sum.insert)
          with ins tai have "(\<Sum>j\<in>{..<(m*2^m)}-{0}. real j / (2::real)^m * \<chi> (A m j) t)
            = real i / (2::real)^m +
            (\<Sum>j\<in>{..<(m*2^m)}-{0}-{i}. real j / (2::real)^m * \<chi> (A m j) t)"
            by (simp add: characteristic_function_def)
          
          also note sum0
          finally show ?thesis 
            by simp
        qed
      }
      hence disj: "\<And>m i. \<lbrakk>t \<in> A m i; i \<in> {..<m * 2 ^ m}\<rbrakk> 
        \<Longrightarrow> u m t = real i / (2::real)^m" .

      { fix n
        
        define a where "a = (f t)*(2::real)^n"
        define i where "i = (LEAST i. a < real (i::nat)) - 1"
        from nn have "0 \<le> a" 
          by (simp add: zero_le_mult_iff a_def nonnegative_def)
        also 
        have "\<exists>i. a < real (i::nat)"
          by (rule reals_Archimedean2)
        then obtain k where "a < real (k::nat)"
          by fast
        hence less: "a < real (LEAST i. a < real (i::nat))"
          by (rule LeastI)
      
        finally
        have "0 < (LEAST i. a < real (i::nat))"
          by simp
        hence min: "(LEAST i. a < real (i::nat)) - 1 < (LEAST i. a < real (i::nat))"
          by arith
        hence "\<not> (a < real ((LEAST i. a < real (i::nat)) - 1))" 
          by (rule not_less_Least)
        hence ia: "real i \<le> a" 
          by (auto simp add: i_def order_less_le)
        from min less have ai: "a < real (Suc i)"
          by (simp add: i_def)
      
        from ia have ia2: "real i / (2::real)^n \<le> f t"
          by (simp add: a_def pos_divide_le_eq)
        also from ai have ai2: "f t < real (Suc i) / (2::real)^n"
          by (simp add: a_def pos_less_divide_eq[THEN sym])
        ultimately have tA: "t \<in> A n i" 
          by (simp add: A_def)
      
        { assume ftn: "f t < real n"

          from ia a_def have "real i \<le> f t * (2::real)^n"
            by simp
          also from ftn have "f t * (2::real)^n < real n * (2::real)^n"
            by simp
          finally have ni: "i < n * 2 ^ n"
            by (simp add: of_nat_less_iff[symmetric, where 'a=real])
          
          with tA have un: "u n t = real i / (2::real)^n"
            using disj by simp
          
          with ia2 have lef: "u n t \<le> f t"
            by simp
          
          from un have "real (i+1) / (2::real)^n = (real i + real (1::nat))/(2::real)^n"
            by (simp only: of_nat_add)
          with un ai2 have fless: "f t < u n t + 1/(2::real)^n"
            by (simp add: add_divide_distrib)
          
          have uSuc: "u n t \<le> u (Suc n) t"
          proof (cases "f t < real (2*i+1) / (2*(2::real)^n)")
            case True
            from ia2 have "real (2*i)/(2::real)^(n+1) \<le> f t"
              by simp
            with True have tA2: "t \<in> A (n+1) (2*i)"
              by (simp add: A_def)

            from ni have "2*i < (n+1)*(2^(n+1))"
              by simp
            with tA2 have "u (n+1) t = real i / (2::real)^n"
              using disj by simp
            with un show ?thesis
              by simp
          next
            case False
            have "(2::real) \<noteq> 0"
              by simp
            hence "real (2*(Suc i)) / ((2::real)^(Suc n)) = real (Suc i) / (2::real)^n"
              by (metis mult_divide_mult_cancel_left_if power_Suc of_nat_mult of_nat_numeral)
            with ai2 have "f t < real (2*(Suc i)) / (2::real)^(n+1)"
             by simp 
            with False have tA2: "t \<in> A (n+1) (2*i+1)"    
              by (simp add: A_def) 
            
            from ni have "2*i+1 < (n+1)*(2^(n+1))"
              by simp
            with tA2 have "u (Suc n) t = real (2*i+1) / (2 * (2::real)^n)"
              using disj by simp
            also have "\<dots> = (real (2*i) + real (1::nat))/ (2 * (2::real)^n)"
              by (simp only: of_nat_add)
            also have "\<dots> = real i / (2::real)^n + real (1::nat) / (2 * (2::real)^n)"
              by (simp add: add_divide_distrib)
            finally show ?thesis using un
              by (simp add: zero_le_divide_iff)
          qed
          note this lef fless
        }
        hence uSuc: "f t < real n \<Longrightarrow> u n t \<le> u (Suc n) t" 
          and lef:  "f t < real n \<Longrightarrow> u n t \<le> f t"
          and fless:"f t < real n \<Longrightarrow> f t < u n t + 1 / (2::real)^n" 
          by auto

        have "u n t \<le> u (Suc n) t"
        proof (cases "real n \<le> f t")
          case True
          { fix i assume "i \<in> {..<(n*2^n)}-{0}"
            hence "Suc i \<le> n*2^n" by simp
            hence mult: "real (Suc i) \<le> real n * (2::real)^n"
              by (simp add: of_nat_le_iff[symmetric, where 'a=real])
            have "0 < (2::real)^n"
              by simp
            with mult have "real (Suc i) / (2::real)^n \<le> real n" 
              by (simp add: pos_divide_le_eq)
            also note True
            finally have "\<not> f t <  real (Suc i) / (2::real)^n"
              by (simp add: order_less_le)
            hence "t \<notin> A n i"
              by (simp add: A_def)
            hence "(real i/(2::real)^n)*\<chi> (A n i) t = 0"
              by (simp add: characteristic_function_def)
          }
          with refl have "(\<Sum>i\<in>{..<n * 2 ^ n} - {0}. real i / (2::real)^n * \<chi> (A n i) t)
            = (\<Sum>i\<in>{..<n * 2 ^ n} - {0}. 0)"
            by (rule sum.cong)
          hence "u n t = 0"  by (simp add: u_def)
            
          also 
          { fix m
            have "0 \<le> u m t"
              by (simp add: u_def characteristic_function_def zero_le_divide_iff sum_nonneg)
          }
          hence "0 \<le> u (Suc n) t" .

          finally show ?thesis .
          
        next
          case False
          with uSuc show ?thesis  by simp
        qed
        note this lef fless
      }
      hence uSuc: "\<And>n. u n t \<le> u (Suc n) t" 
        and lef:  "\<And>n. f t < real n \<Longrightarrow> u n t \<le> f t"
        and fless:"\<And>n. f t < real n \<Longrightarrow> f t < u n t + 1 / (2::real)^n" 
        by auto

      have "\<exists>n0::nat. f t < real n0"  by (rule reals_Archimedean2)
      then obtain n0::nat where "f t < real n0" ..
      also have "\<And>n. real n0 \<le> real (n+n0)"  by simp 
      finally
      have pro: "\<And>n. f t < real (n + n0)" .
      hence 2: "\<And>n. u (n+n0) t \<le> f t" using lef by simp
      from uSuc have 1: "\<And>n. u (n+n0) t \<le> u (Suc n + n0) t" by simp
      from 1 2 have "\<exists>c. (\<lambda>n. u (n+n0) t)\<up>c \<and> c \<le> f t"
        by (rule real_mon_conv_bound)
      with uSuc obtain c where n0mc: "(\<lambda>n. u (n+n0) t)\<up>c" and cle: "c \<le> f t"
        by fast

      from n0mc have "(\<lambda>n. u (n+n0) t) \<longlonglongrightarrow> c"
        by (simp add: mon_conv_real_def)
      hence lim: "(\<lambda>n. u n t) \<longlonglongrightarrow> c"
        by (subst limseq_shift_iff[THEN sym])

      have "\<forall>y. \<exists>N. \<forall>n. N \<le> n \<longrightarrow> y < (2::real)^n"
      proof
        fix y::real
        have "\<exists>N::nat. y < real N"
          by (rule reals_Archimedean2)
        then obtain N::nat where 1: "y < real N"
          by fast
        { fix n::nat
          note 1 
          also assume "N \<le> n"
          also have "real n < (2::real)^n"
            by (rule of_nat_less_two_power)
          finally
          have "y < 2 ^ n"
            by simp
        }
        thus "\<exists>N. \<forall>n. N \<le> n \<longrightarrow> y < (2::real)^n"
          by blast
      qed
      hence "(\<lambda>n. inverse ((2::real)^n)) \<longlonglongrightarrow> 0"
        by (intro LIMSEQ_inverse_zero) auto
      with lim have "(\<lambda>n. u n t + inverse ((2::real)^n)) \<longlonglongrightarrow> c+0"
        by (rule tendsto_add)
      hence "(\<lambda>n. u n t + 1/(2::real)^n) \<longlonglongrightarrow> c"
        by (simp add: divide_inverse)
      hence "(\<lambda>n. u (n+n0) t + 1/(2::real)^(n+n0)) \<longlonglongrightarrow> c"
        by (subst limseq_shift_iff)
      also from pro fless have "\<And>n. f t \<le> u (n+n0) t + 1 / 2 ^ (n+n0)"
        by (simp add: order_le_less)
      ultimately have "f t \<le> c"
        by (simp add: LIMSEQ_le_const)
      with cle have "c = f t" 
        by simp

      with lim have "(\<lambda>n. u n t) \<longlonglongrightarrow> f t"
        by simp

      with uSuc have "(\<lambda>n. u n t)\<up> f t"
        by (simp add: mon_conv_real_def)
    }
    thus ?thesis 
      by (simp add: realfun_mon_conv_iff)
  qed
qed(*>*)


text\<open>The following dominated convergence theorem is an easy
  corollary. It can be effectively applied to show integrability.\<close>

corollary assumes ms: "measure_space M" and f: "f \<in> rv M" 
  and b: "b \<in> nnfis g M" and fg: "f\<le>g" and nn: "nonnegative f"  
  shows nnfis_dom_conv: "\<exists>a. a \<in> nnfis f M \<and> a \<le> b" using b
proof (cases)
  case (base v r)
  from ms f nn have "\<exists>u x. u\<up>f \<and> (\<forall>n. x n \<in> sfis (u n) M)" 
    by (rule rv_mon_conv_sfis)
  then obtain u x where uf: "u\<up>f" and xu: "\<And>n. x n \<in> sfis (u n) M" 
    by fast 
  
  { fix n
    from uf have "u n \<le> f" 
      by (rule realfun_mon_conv_le)
    also note fg 
    also 
    from xu have "x n \<in> nnfis (u n) M" 
      by (rule sfis_nnfis)
    moreover note b ms
    ultimately  have le: "x n \<le> b" 
      by (simp add: nnfis_mono)
    
    from uf have "u n \<le> u (Suc n)" 
      by (simp only: mon_conv_real_fun_def)
    with ms xu[of n] xu[of "Suc n"] have "x n \<le> x (Suc n)" 
      by (simp add: sfis_mono) 
    note this le
  } 
  hence "\<exists>a. x\<up>a \<and> a \<le> b" 
    by (rule real_mon_conv_bound)
  then obtain a where xa: "x\<up>a" and ab: "a \<le> b" 
    by auto
  
  from uf xu xa have "a \<in> nnfis f M" 
    by (rule nnfis.base)
  with ab show ?thesis 
    by fast
qed

text\<open>Speaking all the time about integrability, it is time to define
  it at last.\<close>

definition
  integrable:: "('a \<Rightarrow> real) \<Rightarrow> ('a set set * ('a set \<Rightarrow> real)) \<Rightarrow> bool" where
  (*We could also demand that f be in rv M, but measurability is already ensured 
  by construction of the integral/nn_integrable functions*)
  "integrable f M \<longleftrightarrow> measure_space M \<and> 
  (\<exists>x. x \<in> nnfis (pp f) M) \<and> (\<exists>y. y \<in> nnfis (np f) M)"

definition
  integral:: "('a \<Rightarrow> real) \<Rightarrow> ('a set set * ('a set \<Rightarrow> real)) \<Rightarrow> real" ("\<integral> _ \<partial>_"(*<*)[60,61] 110(*>*)) where
  "integrable f M \<Longrightarrow> \<integral> f \<partial>M = (THE i. i \<in> nnfis (pp f) M) -
  (THE j. j \<in> nnfis (np f) M)" 

text\<open>So the final step is done, the integral defined. The theorems
  we are already used to prove from the
  earlier stages are still missing. Only now there are always two properties to be
  shown: integrability and the value of the integral. Isabelle makes
  it possible two have both goals in a single theorem, so that the
  user may derive the statement he desires. Two useful lemmata follow. They
  help lifting nonnegative function integral sets to integrals
  proper. Notice how the dominated convergence theorem from above is
  employed in the latter.\<close>

lemma nnfis_integral:
  assumes nn: "a \<in> nnfis f M" and ms: "measure_space M"
  shows "integrable f M" and "\<integral> f \<partial> M = a"
proof -
  from nn have "nonnegative f" 
    by (rule nnfis_nn)
  hence "pp f = f" and 0: "np f = (\<lambda>t. 0)" 
    by (auto simp add: nn_pp_np)
  with nn have a: "a \<in> nnfis (pp f) M" 
    by simp
  have "0\<le>(0::real)" 
    by (rule order_refl)
  with ms nn have "0*a \<in> nnfis (\<lambda>t. 0*f t) M" 
    by (rule nnfis_times) 
  with 0 have 02: "0 \<in> nnfis (np f) M" 
    by simp
  with ms a show "integrable f M" 
    by (auto simp add: integrable_def)
  also 
  from a ms have "(THE i. i \<in> nnfis (pp f) M) = a" 
    by (auto simp add: nnfis_unique)
  moreover
  from 02 ms have "(THE i. i \<in> nnfis (np f) M) = 0" 
    by (auto simp add: nnfis_unique)
  ultimately show "\<integral> f \<partial> M = a" 
    by (simp add: integral_def)
qed

lemma nnfis_minus_nnfis_integral:
  assumes a: "a \<in> nnfis f M" and b: "b \<in> nnfis g M"
  and ms: "measure_space M"
  shows "integrable (\<lambda>t. f t - g t) M" and "\<integral> (\<lambda>t. f t - g t) \<partial> M = a - b"
proof - 
  from ms a b have "(\<lambda>t. f t - g t) \<in> rv M" 
    by (auto simp only: nnfis_rv rv_minus_rv)
  hence prv: "pp (\<lambda>t. f t - g t) \<in> rv M" and nrv: " np (\<lambda>t. f t - g t) \<in> rv M"
    by (auto simp only: pp_np_rv)
  
  have nnp: "nonnegative (pp (\<lambda>t. f t - g t))" 
    and nnn: "nonnegative (np (\<lambda>t. f t - g t))"
    by (simp_all add: nonnegative_def positive_part_def negative_part_def)
  
  from ms a b have fg: "a+b \<in> nnfis (\<lambda>t. f t + g t) M" 
    by (rule nnfis_add)

  from a b have nnf: "nonnegative f" and nng: "nonnegative g" 
    by (simp_all only: nnfis_nn)
  
  { fix t
    from nnf nng have "0 \<le> f t" and "0 \<le> g t" 
      by (simp_all add: nonnegative_def)
    hence "(pp (\<lambda>t. f t - g t)) t \<le> f t + g t" and "(np (\<lambda>t. f t - g t)) t \<le> f t + g t"
      by (simp_all add: positive_part_def negative_part_def)
  } 
  hence "(pp (\<lambda>t. f t - g t)) \<le> (\<lambda>t. f t + g t)" 
    and "(np (\<lambda>t. f t - g t)) \<le> (\<lambda>t. f t + g t)"
    by (simp_all add: le_fun_def)
  with fg nnf nng prv nrv nnp nnn ms 
  have "\<exists>l. l \<in> nnfis (pp (\<lambda>t. f t - g t)) M \<and> l \<le> a+b"
    and "\<exists>k. k \<in> nnfis (np (\<lambda>t. f t - g t)) M \<and> k \<le> a+b" 
    by (auto simp only: nnfis_dom_conv)
  then obtain l k where l: "l \<in> nnfis (pp (\<lambda>t. f t - g t)) M" 
    and k: "k \<in> nnfis (np (\<lambda>t. f t - g t)) M" 
    by auto
  with ms show i: "integrable (\<lambda>t. f t - g t) M" 
    by (auto simp add: integrable_def)
  
  { fix t
    have "f t - g t = (pp (\<lambda>t. f t - g t)) t - (np (\<lambda>t. f t - g t)) t"
      by (rule f_plus_minus)
    
    hence "f t + (np (\<lambda>t. f t - g t)) t = g t + (pp (\<lambda>t. f t - g t)) t" 
      by arith
  } 
  hence "(\<lambda>t. f t + (np (\<lambda>t. f t - g t)) t) = 
    (\<lambda>t. g t + (pp (\<lambda>t. f t - g t)) t)" 
    by (rule ext)
  also 
  from ms a k b l have "a+k \<in> nnfis (\<lambda>t. f t + (np (\<lambda>t. f t - g t)) t) M"
    and "b+l \<in> nnfis (\<lambda>t. g t + (pp (\<lambda>t. f t - g t)) t) M" 
    by (auto simp add: nnfis_add)
  moreover note ms
  ultimately have "a+k = b+l" 
    by (simp add: nnfis_unique)
  hence "l-k=a-b" by arith
  also
  from k l ms have "(THE i. i \<in> nnfis (pp (\<lambda>t. f t - g t)) M) = l"
    and "(THE i. i \<in> nnfis (np (\<lambda>t. f t - g t)) M) = k" 
    by (auto simp add: nnfis_unique)
  moreover note i
  ultimately show "\<integral> (\<lambda>t. f t - g t) \<partial> M = a - b" 
    by (simp add: integral_def)
qed

text\<open>Armed with these, the standard integral behavior should not be
  hard to derive. Mind that integrability always implies a
  measure space, just like random variables did in \ref{sec:realrandvar}.\<close>

theorem assumes (*<*)int:(*>*) "integrable f M"
  shows integrable_rv: "f \<in> rv M"
(*<*)proof -
  from int have "pp f \<in> rv M \<and> np f \<in> rv M"
    by (auto simp add: integrable_def nnfis_rv)  
  thus ?thesis 
    by (simp add: pp_np_rv_iff[THEN sym])
qed(*>*)

theorem integral_char: 
  assumes ms: "measure_space M" and mA: "A \<in> measurable_sets M" 
  shows "\<integral> \<chi> A \<partial> M = measure M A" and "integrable \<chi> A M"
(*<*)proof -
  from ms mA have "measure M A \<in> sfis \<chi> A M" 
    by (rule sfis_char)
  hence nnfis: "measure M A \<in> nnfis \<chi> A M" 
    by (rule sfis_nnfis)
  from this and ms show "\<integral> \<chi> A \<partial> M = measure M A" 
    by (rule nnfis_integral)
  from nnfis and ms show "integrable \<chi> A M" 
    by (rule nnfis_integral) 
qed(*>*)


theorem integral_add:
  assumes f: "integrable f M" and g: "integrable g M"
  shows "integrable (\<lambda>t. f t + g t) M"
  and "\<integral> (\<lambda>t. f t + g t) \<partial>M = \<integral> f \<partial>M + \<integral> g \<partial>M"
proof -
  define u where "u = (\<lambda>t. pp f t + pp g t)"
  define v where "v = (\<lambda>t. np f t + np g t)"

  from f obtain pf nf where pf: "pf \<in> nnfis (pp f) M" 
    and nf: "nf \<in> nnfis (np f) M" and ms: "measure_space M"
    by (auto simp add: integrable_def)
  from g obtain pg ng where pg: "pg \<in> nnfis (pp g) M"
    and ng: "ng \<in> nnfis (np g) M"
    by (auto simp add: integrable_def)

  from ms pf pg u_def have
    u: "pf+pg \<in> nnfis u M" 
    by (simp add: nnfis_add)
 
  from ms nf ng v_def have
    v: "nf+ng \<in> nnfis v M" 
    by (simp add: nnfis_add)
  
  { fix  t
    from u_def v_def have "f t + g t = u t - v t"
      by (simp add: positive_part_def negative_part_def)
  }
  hence uvf: "(\<lambda>t. u t - v t) = (\<lambda>t. f t + g t)"
    by (simp add: ext)

  from u v ms have "integrable (\<lambda>t. u t - v t) M"
    by (rule nnfis_minus_nnfis_integral)
  with u_def v_def uvf  show "integrable (\<lambda>t. f t + g t) M"
    by simp
      
  from pf nf ms have "\<integral> (\<lambda>t. pp f t - np f t) \<partial>M = pf-nf"
    by (rule nnfis_minus_nnfis_integral)
  hence "\<integral> f \<partial>M = pf-nf"
    by (simp add: f_plus_minus[THEN sym])
  also 
  from pg ng ms have "\<integral> (\<lambda>t. pp g t - np g t) \<partial>M = pg-ng"
    by (rule nnfis_minus_nnfis_integral)
  hence "\<integral> g \<partial>M = pg-ng"
    by (simp add: f_plus_minus[THEN sym])
  moreover
  from u v ms have "\<integral> (\<lambda>t. u t - v t) \<partial>M = pf + pg - (nf + ng)"
    by (rule nnfis_minus_nnfis_integral)
  with uvf have "\<integral> (\<lambda>t. f t + g t) \<partial>M = pf-nf + pg-ng"
    by simp
  ultimately
  show "\<integral> (\<lambda>t. f t + g t) \<partial>M = \<integral> f \<partial>M + \<integral> g \<partial>M"
    by simp
qed
  
theorem integral_mono:
  assumes f: "integrable f M"    
  and g: "integrable g M"  and fg: "f\<le>g"
  shows "\<integral> f \<partial>M \<le> \<integral> g \<partial>M" 
proof -
  from f obtain pf nf where pf: "pf \<in> nnfis (pp f) M" 
    and nf: "nf \<in> nnfis (np f) M" and ms: "measure_space M"
    by (auto simp add: integrable_def)

  from g obtain pg ng where pg: "pg \<in> nnfis (pp g) M"
    and ng: "ng \<in> nnfis (np g) M"
    by (auto simp add: integrable_def)
  
  { fix t
    from fg have "f t \<le> g t"
      by (simp add: le_fun_def)
    hence "pp f t \<le> pp g t" and "np g t \<le> np f t"
      by (auto simp add: positive_part_def negative_part_def)
  }
  hence "pp f \<le> pp g" and "np g \<le> np f"
    by (simp_all add: le_fun_def)  
  with ms pf pg ng nf have "pf \<le> pg" and "ng \<le> nf"
    by (simp_all add: nnfis_mono)
 
  also
  from ms pf pg ng nf have "(THE i. i \<in> nnfis (pp f) M) = pf"
    and "(THE i. i \<in> nnfis (np f) M) = nf"
    and "(THE i. i \<in> nnfis (pp g) M) = pg"
    and "(THE i. i \<in> nnfis (np g) M) = ng"
    by (auto simp add: nnfis_unique)
  with f g have "\<integral> f \<partial>M = pf - nf"
    and "\<integral> g \<partial>M = pg - ng"
    by (auto simp add: integral_def)
  
  ultimately show ?thesis
    by simp
qed

theorem integral_times:
  assumes int: "integrable f M"
  shows "integrable (\<lambda>t. a*f t) M" and "\<integral> (\<lambda>t. a*f t) \<partial>M = a*\<integral> f \<partial>M"
(*<*)proof -
  from int have "\<integral> f \<partial>M = (THE i. i \<in> nnfis (pp f) M) -
  (THE j. j \<in> nnfis (np f) M)" by (simp only: integral_def)
  also from int obtain k l where k: "k \<in> nnfis (pp f) M"
    and l: "l \<in> nnfis (np f) M" and ms: "measure_space M"
    by (auto simp add: integrable_def)

  from k l ms have "(THE i. i \<in> nnfis (pp f) M) = k"
    and "(THE i. i \<in> nnfis (np f) M) = l" by (auto simp add: nnfis_unique)
  with int have uni: "k-l = \<integral> f \<partial>M" by (simp add: integral_def)

  have "integrable (\<lambda>t. a*f t) M \<and> \<integral> (\<lambda>t. a*f t) \<partial>M = a*\<integral> f \<partial>M"
  proof (cases "0\<le>a")
    case True
    hence pp: "pp (\<lambda>t. a * f t) = (\<lambda>t. a * pp f t)" and np: "np (\<lambda>t. a * f t) = (\<lambda>t. a * np f t)"
      by (auto simp add: real_pp_np_pos_times)
    
    from ms k True have "a*k \<in> nnfis (\<lambda>t. a * pp f t) M" by (rule nnfis_times)
    with pp have 1: "a*k \<in> nnfis (pp (\<lambda>t. a * f t)) M" by simp
    
    from np ms l True have 2: "a*l \<in> nnfis (np (\<lambda>t. a * f t)) M"
      by (simp add: nnfis_times)
    
    from ms 1 2 have i: "integrable (\<lambda>t. a*f t) M" by (auto simp add: integrable_def)
    also
    from 1 ms have "(THE i. i \<in> nnfis (pp (\<lambda>t. a * f t)) M) = a*k" by (auto simp add: nnfis_unique)
    moreover
    from 2 ms have "(THE i. i \<in> nnfis (np (\<lambda>t. a * f t)) M) = a*l" by (auto simp add: nnfis_unique)
    ultimately 
    have "\<integral> (\<lambda>t. a*f t) \<partial>M = a*k-a*l" by (simp add: integral_def)
    also have "\<dots> = a*(k-l)" by (simp add: right_diff_distrib)
    also note uni also note i
    ultimately show ?thesis by simp
  next
    case False
    hence pp: "pp (\<lambda>t. a*f t) = (\<lambda>t. -a*np f t)" and np: "np (\<lambda>t. a*f t) = (\<lambda>t. -a*pp f t)"
      by (auto simp add: real_pp_np_neg_times)
    
    from False have le: "0 \<le> -a" by simp
    with ms l have "-a*l \<in> nnfis (\<lambda>t. -a * np f t) M" by (rule nnfis_times)
    with pp have 1: "-a*l \<in> nnfis (pp (\<lambda>t. a * f t)) M" by simp
    
    from ms k le have "-a*k \<in> nnfis (\<lambda>t. -a * pp f t) M" by (rule nnfis_times)
    with np have 2: "-a*k \<in> nnfis (np (\<lambda>t. a * f t)) M" by simp
          
    from ms 1 2 have i: "integrable (\<lambda>t. a*f t) M" by (auto simp add: integrable_def)
    also
    from 1 ms have "(THE i. i \<in> nnfis (pp (\<lambda>t. a * f t)) M) = -a*l" by (auto simp add: nnfis_unique)
    moreover
    from 2 ms have "(THE i. i \<in> nnfis (np (\<lambda>t. a * f t)) M) = -a*k" by (auto simp add: nnfis_unique)
    ultimately 
    have "\<integral> (\<lambda>t. a*f t) \<partial>M = -a*l-(-a*k)" by (simp add: integral_def)
    also have "\<dots> = a*(k-l)" by (simp add: right_diff_distrib)
    also note uni also note i
    ultimately show ?thesis by simp
  qed
  thus "integrable (\<lambda>t. a*f t) M" and "\<integral> (\<lambda>t. a*f t) \<partial>M = a*\<integral> f \<partial>M" by simp_all
qed(*>*)

(* Left out for lack of time   
   
theorem sf_integral: 
  assumes M: "measure_space M" and f: "f = (\<lambda>t. \<Sum>i\<in>(S::nat set). x i * \<chi> (A i) t)"
  and A: "\<forall>i\<in>S. A i \<in> measurable_sets M" and S: "finite S"
  shows "\<integral> f \<partial> M = (\<Sum>i\<in>S. x i * measure M (A i))" 
  and "integrable f M"
  oops
  
constdefs
  The probabilistic Quantifiers as in Hurd: p. 53 could be defined as a special case of this
almost_everywhere:: "('a set set * ('a set \<Rightarrow> real)) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" ("_-a.e. _")
"M-a.e. P == measure_space M \<and> (\<exists>N. N \<in> measurable_sets M \<and> measure M N = 0 \<and> (\<forall>w \<in> -N. P w))"

theorem assumes ae0: "M-a.e. (\<lambda>w. f w = 0)" 
  shows ae0_nn_integ: "\<integral> f \<partial> M = 0"
  oops

theorem  assumes "integrable f M" and "integrable g M" and "M-a.e. (\<lambda>w. f w \<le> g w)"
  shows ae_integ_monotone: "\<integral> f \<partial> M \<le> \<integral> g \<partial> M"
  oops

theorem assumes aeq: "M-a.e. (\<lambda>w. f w = g w)" 
  shows aeq_nn_integ: "integrable f M \<Longrightarrow> \<integral> f \<partial> M = \<integral> g \<partial> M"
  oops
 *)
   
text\<open>To try out our definitions in an application, only one more
  theorem is missing. The famous Markov--Chebyshev inequation is not
  difficult to arrive at using the basic integral properties.\<close>

theorem assumes int: "integrable f M" and a: "0<a" and intp: "integrable (\<lambda>x. \<bar>f x\<bar> ^ n) M"
  shows markov_ineq: "law M f {a..} \<le>  \<integral> (\<lambda>x. \<bar>f x\<bar> ^ n) \<partial>M / (a^n)"
proof -
  from int have rv: "f \<in> rv M" 
    by (rule integrable_rv)
  hence ms: "measure_space M" 
    by (simp add: rv_def)
  from ms rv have ams: "{w. a \<le> f w} \<in> measurable_sets M"
    by (simp add: rv_ge_iff)
  
  from rv have "(a^n)*law M f {a..} = (a^n)*measure M {w. a \<le> f w}"
    by (simp add: distribution_def vimage_def)
  also 
  from ms ams have int2: "integrable \<chi> {w. a \<le> f w} M" 
    and eq2: "\<dots> = (a^n)*\<integral> \<chi> {w. a \<le> f w} \<partial> M"
    by (auto simp add: integral_char)
  note eq2 also 
  from int2 have int3: "integrable (\<lambda>t. (a^n)*\<chi> {w. a \<le> f w} t) M" 
    and eq3: "\<dots> = \<integral> (\<lambda>t. (a^n)*\<chi> {w. a \<le> f w} t) \<partial> M"
    by (auto simp add: integral_times)
  note eq3 also
  { fix t
    from a have "(a^n)*\<chi> {w. a \<le> f w} t \<le> \<bar>f t\<bar> ^ n"
    proof (cases "a \<le> f t")
      case False 
      thus ?thesis 
        by (simp add: characteristic_function_def)
    next
      case True
      with a have "a ^ n \<le> (f t)^ n"
        by (simp add: power_mono)
      also
      have "(f t)^ n \<le> \<bar>(f t) ^ n\<bar>"
        by arith
      hence "(f t)^ n \<le> \<bar>f t\<bar> ^ n"
        by (simp add: power_abs)
      finally
      show ?thesis 
        by (simp add: characteristic_function_def)
    qed
  }
  with int3 intp have "\<dots> \<le> \<integral> (\<lambda>x. \<bar>f x\<bar> ^ n) \<partial>M"
    by (simp add: le_fun_def integral_mono)
    
  also 
  from a have "0 < a^n" 
    by (rule zero_less_power)
  ultimately show ?thesis 
    by (simp add: pos_le_divide_eq mult.commute)
qed

end
