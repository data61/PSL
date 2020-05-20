subsection \<open>Monotone Convergence \label{sec:monconv}\<close>

theory MonConv
imports Complex_Main
begin

text \<open>A sensible requirement for an integral operator is that it be
  ``well-behaved'' with respect to limit functions. To become just a
  little more
  precise, it is expected that the limit operator may be interchanged
  with the integral operator under conditions that are as weak as
  possible. To this
  end, the notion of monotone convergence is introduced and later
  applied in the definition of the integral. 

  In fact, we distinguish three types of monotone convergence here:
  There are converging sequences of real numbers, real functions and
  sets. Monotone convergence could even be defined more generally for
  any type in the axiomatic type class\footnote{For the concept of axiomatic type
  classes, see \cite{Nipkow93,wenzelax}} \<open>ord\<close> of ordered
  types like this.

  @{prop "mon_conv u f \<equiv> (\<forall>n. u n \<le> u (Suc n)) \<and> Sup (range u) = f"}

  However, this employs the general concept of a least upper bound.
  For the special types we have in mind, the more specific
  limit --- respective union --- operators are available, combined with many theorems
  about their properties. For the type of real- (or rather ordered-) valued functions,
  the less-or-equal relation is defined pointwise.

  @{thm le_fun_def [no_vars]}
\<close>

(*monotone convergence*)
 
text \<open>Now the foundations are laid for the definition of monotone
  convergence. To express the similarity of the different types of
  convergence, a single overloaded operator is used.\<close>

consts
  mon_conv:: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a::ord \<Rightarrow> bool" ("_\<up>_" [60,61] 60) 
overloading
  mon_conv_real \<equiv> "mon_conv :: _ \<Rightarrow> real \<Rightarrow> bool"
  mon_conv_real_fun \<equiv> "mon_conv :: _ \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
  mon_conv_set \<equiv> "mon_conv :: _ \<Rightarrow> 'a set \<Rightarrow> bool"
begin

definition "x\<up>(y::real) \<equiv> (\<forall>n. x n \<le> x (Suc n)) \<and> x \<longlonglongrightarrow> y"
definition "u\<up>(f::'a \<Rightarrow> real) \<equiv> (\<forall>n. u n \<le> u (Suc n)) \<and>  (\<forall>w. (\<lambda>n. u n w) \<longlonglongrightarrow> f w)"
definition "A\<up>(B::'a set) \<equiv> (\<forall>n. A n \<le> A (Suc n)) \<and> B = (\<Union>n. A n)"

end

theorem realfun_mon_conv_iff: "(u\<up>f) = (\<forall>w. (\<lambda>n. u n w)\<up>((f w)::real))"
  by (auto simp add: mon_conv_real_def mon_conv_real_fun_def le_fun_def)

text \<open>The long arrow signifies convergence of real sequences as
  defined in the theory \<open>SEQ\<close> \cite{Fleuriot:2000:MNR}. Monotone convergence
  for real functions is simply pointwise monotone convergence.

  Quite a few properties of these definitions will be necessary later,
  and they are listed now, giving only few select proofs.\<close> 

    (*This theorem, too, could be proved just the same for any ord
  Type!*)


lemma assumes mon_conv: "x\<up>(y::real)"
  shows mon_conv_mon: "(x i) \<le> (x (m+i))"
(*<*)proof (induct m)
  case 0 
  show ?case by simp
  
next
  case (Suc n)
  also 
  from mon_conv have "x (n+i) \<le> x (Suc n+i)" 
    by (simp add: mon_conv_real_def)
  finally show ?case .
qed(*>*)


lemma limseq_shift_iff: "(\<lambda>m. x (m+i)) \<longlonglongrightarrow> y = x \<longlonglongrightarrow> y"
(*<*)proof (induct i)
  case 0 show ?case by simp
next 
  case (Suc n)
  also have "(\<lambda>m. x (m + n)) \<longlonglongrightarrow> y = (\<lambda>m. x (Suc m + n)) \<longlonglongrightarrow> y"
    by (rule LIMSEQ_Suc_iff[THEN sym])  
  also have "\<dots> = (\<lambda>m. x (m + Suc n)) \<longlonglongrightarrow> y"
    by simp
  finally show ?case .
qed(*>*)

    (*This, too, could be established in general*)
theorem assumes mon_conv: "x\<up>(y::real)"
  shows real_mon_conv_le: "x i \<le> y"
proof -
  from mon_conv have "(\<lambda>m. x (m+i)) \<longlonglongrightarrow> y" 
    by (simp add: mon_conv_real_def limseq_shift_iff)
  also from mon_conv have "\<forall>m\<ge>0. x i \<le> x (m+i)" by (simp add: mon_conv_mon)
  ultimately show ?thesis by (rule LIMSEQ_le_const[OF _ exI[where x=0]])
qed

theorem assumes mon_conv: "x\<up>(y::('a \<Rightarrow> real))"
  shows realfun_mon_conv_le: "x i \<le> y"
proof -
  {fix w
    from mon_conv have "(\<lambda>i. x i w)\<up>(y w)" 
      by (simp add: realfun_mon_conv_iff)    
    hence "x i w \<le> y w" 
      by (rule real_mon_conv_le)
  }
  thus ?thesis by (simp add: le_fun_def)
qed

lemma assumes mon_conv: "x\<up>(y::real)"
  and less: "z < y"
  shows real_mon_conv_outgrow: "\<exists>n. \<forall>m. n \<le> m \<longrightarrow> z < x m"
proof -
  from less have less': "0 < y-z" 
    by simp                
  have "\<exists>n.\<forall>m. n \<le> m \<longrightarrow> \<bar>x m - y\<bar> < y - z"
  proof -
    from mon_conv have aux: "\<And>r. r > 0 \<Longrightarrow> \<exists>n. \<forall>m. n \<le> m \<longrightarrow> \<bar>x m - y\<bar> < r"
    unfolding mon_conv_real_def lim_sequentially dist_real_def by auto
    with less' show "\<exists>n. \<forall>m. n \<le> m \<longrightarrow> \<bar>x m - y\<bar> < y - z" by auto
  qed
  also
  { fix m 
    from mon_conv have "x m \<le> y" 
      by (rule real_mon_conv_le)  
    hence "\<bar>x m - y\<bar> = y - x m" 
      by arith                    
    also assume "\<bar>x m - y\<bar> < y - z"
    ultimately have "z < x m" 
      by arith                
  }
  ultimately show ?thesis 
    by blast
qed


theorem real_mon_conv_times: 
  assumes xy: "x\<up>(y::real)" and nn: "0\<le>z"
  shows "(\<lambda>m. z*x m)\<up>(z*y)"
(*<*)proof -
  from assms have "\<And>n. z*x n \<le> z*x (Suc n)"
    by (simp add: mon_conv_real_def mult_left_mono)
  also from xy have "(\<lambda>m. z*x m)\<longlonglongrightarrow>(z*y)"
    by (simp add: mon_conv_real_def tendsto_const tendsto_mult)
  ultimately show ?thesis by (simp add: mon_conv_real_def)
qed(*>*)


theorem realfun_mon_conv_times: 
  assumes xy: "x\<up>(y::'a\<Rightarrow>real)" and nn: "0\<le>z"
  shows "(\<lambda>m w. z*x m w)\<up>(\<lambda>w. z*y w)"
(*<*)proof -
  from assms have "\<And>w. (\<lambda>m. z*x m w)\<up>(z*y w)"
    by (simp add: realfun_mon_conv_iff real_mon_conv_times)
  thus ?thesis by (auto simp add: realfun_mon_conv_iff)
qed(*>*)


theorem real_mon_conv_add: 
  assumes xy: "x\<up>(y::real)" and ab: "a\<up>(b::real)"
  shows "(\<lambda>m. x m + a m)\<up>(y + b)" 
(*<*)proof - 
  { fix n
    from assms have "x n \<le> x (Suc n)" and "a n \<le> a (Suc n)"
      by (simp_all add: mon_conv_real_def)
    hence "x n + a n \<le> x (Suc n) + a (Suc n)"
      by simp
  }
  also from assms have "(\<lambda>m. x m + a m)\<longlonglongrightarrow>(y + b)" by (simp add: mon_conv_real_def tendsto_add)
  ultimately show ?thesis by (simp add: mon_conv_real_def)
qed(*>*)

theorem realfun_mon_conv_add:
  assumes xy: "x\<up>(y::'a\<Rightarrow>real)" and ab: "a\<up>(b::'a \<Rightarrow> real)"
  shows "(\<lambda>m w. x m w + a m w)\<up>(\<lambda>w. y w + b w)"
(*<*)proof -
  from assms have "\<And>w. (\<lambda>m. x m w + a m w)\<up>(y w + b w)"
    by (simp add: realfun_mon_conv_iff real_mon_conv_add)
  thus ?thesis by (auto simp add: realfun_mon_conv_iff)
qed(*>*)


theorem real_mon_conv_bound:
  assumes mon: "\<And>n. c n \<le> c (Suc n)"
  and bound: "\<And>n. c n \<le> (x::real)"
  shows "\<exists>l. c\<up>l \<and> l\<le>x"
proof -
  from incseq_convergent[of c x] mon bound
  obtain l where "c \<longlonglongrightarrow> l" "\<forall>i. c i \<le> l"
    by (auto simp: incseq_Suc_iff)
  moreover \<comment> \<open>This is like $\isacommand{also}$ but lacks the transitivity step.\<close>
  with bound have "l \<le> x"
    by (intro LIMSEQ_le_const2) auto
  ultimately show ?thesis
    by (auto simp: mon_conv_real_def mon)
qed

theorem real_mon_conv_dom:
  assumes xy: "x\<up>(y::real)" and mon: "\<And>n. c n \<le> c (Suc n)"
  and dom: "c \<le> x"
  shows "\<exists>l. c\<up>l \<and> l\<le>y"
proof -
  from dom have "\<And>n. c n \<le> x n" by (simp add: le_fun_def)
  also from xy have "\<And>n. x n \<le> y" by (simp add: real_mon_conv_le)
  also note mon 
  ultimately show ?thesis by (simp add: real_mon_conv_bound) 
qed

text\<open>\newpage\<close>
theorem realfun_mon_conv_bound:
  assumes mon: "\<And>n. c n \<le> c (Suc n)"
  and bound: "\<And>n. c n \<le> (x::'a \<Rightarrow> real)"
  shows "\<exists>l. c\<up>l \<and> l\<le>x"
(*<*)proof 
  define r where "r t = (SOME l. (\<lambda>n. c n t)\<up>l \<and> l\<le>x t)" for t
  { fix t
    from mon have m2: "\<And>n. c n t \<le> c (Suc n) t" by (simp add: le_fun_def)
    also 
    from bound have "\<And>n. c n t \<le> x t" by (simp add: le_fun_def)
    
    ultimately have "\<exists>l. (\<lambda>n. c n t)\<up>l \<and> l\<le>x t" (is "\<exists>l. ?P l") 
      by (rule real_mon_conv_bound) 
    hence "?P (SOME l. ?P l)" by (rule someI_ex)
    hence "(\<lambda>n. c n t)\<up>r t \<and> r t\<le>x t" by (simp add: r_def)
  }  
  thus "c\<up>r \<and> r \<le> x" by (simp add: realfun_mon_conv_iff le_fun_def)
qed (*>*)  

text \<open>This brings the theory to an end. Notice how the definition of the limit of a
  real sequence is visible in the proof to \<open>real_mon_conv_outgrow\<close>, a lemma that will be used for a
  monotonicity proof of the integral of simple functions later on.\<close>(*<*)
  (*Another set construction. Needed in ImportPredSet, but Set is shadowed beyond 
  reconstruction there.
  Before making disjoint, we first need an ascending series of sets*)

primrec mk_mon::"(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> 'a set"
where
  "mk_mon A 0 = A 0"
| "mk_mon A (Suc n) = A (Suc n) \<union> mk_mon A n"

lemma "mk_mon A \<up> (\<Union>i. A i)"
proof (unfold mon_conv_set_def)
  { fix n
    have "mk_mon A n \<subseteq> mk_mon A (Suc n)"
      by auto
  }
  also
  have "(\<Union>i. mk_mon A i) = (\<Union>i. A i)"
  proof 
    { fix i x
      assume "x \<in> mk_mon A i"
      hence "\<exists>j. x \<in> A j"
        by (induct i) auto
      hence "x \<in> (\<Union>i. A i)"
        by simp
    }
    thus "(\<Union>i. mk_mon A i) \<subseteq> (\<Union>i. A i)"
      by auto
    
    { fix i 
      have "A i \<subseteq> mk_mon A i"
        by (induct i) auto
    }
    thus "(\<Union>i. A i) \<subseteq> (\<Union>i. mk_mon A i)"
      by auto
  qed
  ultimately show "(\<forall>n. mk_mon A n \<subseteq> mk_mon A (Suc n)) \<and> \<Union>(A ` UNIV) = (\<Union>n. mk_mon A n)"
    by simp
qed(*>*)

  
end
