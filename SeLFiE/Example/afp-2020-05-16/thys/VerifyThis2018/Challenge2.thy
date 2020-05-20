chapter \<open>Colored Tiles\<close>
section \<open>Challenge\<close>
text_raw \<open>{\upshape
This problem is based on Project Euler problem \#114.

Alice and Bob are decorating their kitchen, and they want to add
a single row of fifty tiles on the edge of the kitchen counter.
Tiles can be either red or black, and for aesthetic reasons,
Alice and Bob insist that red tiles come by blocks of
at least three consecutive tiles.
Before starting, they wish to know how many ways
there are of doing this.
They come up with the following algorithm:
\begin{lstlisting}[language=C,morekeywords={procedure,function,end,to,in,var,then,not,mod}]
var count[51]   // count[i] is the number of valid rows of size i
count[0] := 1   // []
count[1] := 1   // [B] - cannot have a single red tile
count[2] := 1   // [BB] - cannot have one or two red tiles
count[3] := 2   // [BBB] or [RRR]
for n = 4 to 50 do
    count[n] := count[n-1]  // either the row starts with a black tile
    for k = 3 to n-1 do     // or it starts with a block of k red tiles
        count[n] := count[n] + count[n-k-1]  // followed by a black one
    end-for
    count[n] := count[n]+1  // or the entire row is red
end-for
\end{lstlisting}

\paragraph{Verification tasks.}
You should verify that at the end, \texttt{count[50]} will contain the right number.

\bigskip
\noindent\emph{Hint:}
Since the algorithm works by enumerating the valid colorings, we expect you to give
a nice specification of a valid coloring and to prove the following properties:
\begin{enumerate}
\item Each coloring counted by the algorithm is valid.
\item No coloring is counted twice.
\item No valid coloring is missed.
\end{enumerate}
}
\clearpage
\<close>
section \<open>Solution\<close>
theory Challenge2
imports "lib/VTcomp"
begin

  text \<open>
    The algorithm describes a dynamic programming scheme. 
    
    Instead of proving the 3 properties stated in the challenge separately,
    we approach the problem by
    
    \<^enum> Giving a natural specification of a valid tiling as a grammar
    \<^enum> Deriving a recursion equation for the number of valid tilings
    \<^enum> Verifying that the program returns the correct number 
      (which obviously implies all three properties stated in the challenge)
  \<close>


  subsection \<open>Problem Specification\<close>

  subsubsection \<open>Colors\<close>

  datatype color = R | B

  subsubsection \<open>Direct Natural Definition of a Valid Line\<close>

  inductive valid where
    "valid []" |
    "valid xs \<Longrightarrow> valid (B # xs)" |
    "valid xs \<Longrightarrow> n \<ge> 3 \<Longrightarrow> valid (replicate n R @ xs)"

  definition "lcount n = card {l. length l=n \<and> valid l}"

  subsection \<open>Derivation of Recursion Equations\<close>
  
  text \<open>This alternative variant helps us to prove the split lemma below.\<close>
  inductive valid' where
    "valid' []" |
    "n \<ge> 3 \<Longrightarrow> valid' (replicate n R)" |
    "valid' xs \<Longrightarrow> valid' (B # xs)" |
    "valid' xs \<Longrightarrow> n \<ge> 3 \<Longrightarrow> valid' (replicate n R @ B # xs)"

  lemma valid_valid':
    "valid l \<Longrightarrow> valid' l"
    by (induction rule: valid.induct)
       (auto 4 4 intro: valid'.intros elim: valid'.cases
          simp: replicate_add[symmetric] append_assoc[symmetric]
       )

  lemmas valid_red = valid.intros(3)[OF valid.intros(1), simplified]

  lemma valid'_valid:
    "valid' l \<Longrightarrow> valid l"
    by (induction rule: valid'.induct) (auto intro: valid.intros valid_red)

  lemma valid_eq_valid':
    "valid' l = valid l"
    using valid_valid' valid'_valid by metis


  subsubsection \<open>Additional Facts on Replicate\<close>

  lemma replicate_iff:
    "(\<forall>i<length l. l ! i = R) \<longleftrightarrow> (\<exists> n. l = replicate n R)"
    by auto (metis (full_types) in_set_conv_nth replicate_eqI)

  lemma replicate_iff2:
    "(\<forall>i<n. l ! i = R) \<longleftrightarrow> (\<exists> l'. l = replicate n R @ l')" if "n < length l"
    using that by (auto simp: list_eq_iff_nth_eq nth_append intro: exI[where x = "drop n l"])

  lemma replicate_Cons_eq:
    "replicate n x = y # ys \<longleftrightarrow> (\<exists> n'. n = Suc n' \<and> x = y \<and> replicate n' x = ys)"
    by (cases n) auto


  subsubsection \<open>Main Case Analysis on \<open>@term valid\<close>\<close>

  lemma valid_split:
    "valid l \<longleftrightarrow>
    l = [] \<or>
    (l!0 = B \<and> valid (tl l)) \<or>
    length l \<ge> 3 \<and> (\<forall> i < length l. l ! i = R) \<or>
    (\<exists> j < length l. j \<ge> 3 \<and> (\<forall> i < j. l ! i = R) \<and> l ! j = B \<and> valid (drop (j + 1) l))"
    unfolding valid_eq_valid'[symmetric]
    apply standard
    subgoal
      by (erule valid'.cases) (auto simp: nth_append nth_Cons split: nat.splits)
    subgoal
      by (auto intro: valid'.intros simp: replicate_iff elim!: disjE1)
         (fastforce intro: valid'.intros simp: neq_Nil_conv replicate_iff2 nth_append)+
    done


  subsubsection \<open>Base cases\<close>

  lemma lc0_aux:
    "{l. l = [] \<and> valid l} = {[]}"
    by (auto intro: valid.intros)

  lemma lc0: "lcount 0 = 1"
    by (auto simp: lc0_aux lcount_def)

  lemma lc1aux: "{l. length l=1 \<and> valid l} = {[B]}"  
    by (auto intro: valid.intros elim: valid.cases simp: replicate_Cons_eq)

  lemma lc2aux: "{l. length l=2 \<and> valid l} = {[B,B]}"
    by (auto 4 3 intro: valid.intros elim: valid.cases simp: replicate_Cons_eq)

  lemma lc3_aux: "{l. length l=3 \<and> valid l} = {[B,B,B], [R,R,R]}"
    by (auto 4 4 intro: valid.intros valid_red[of 3, simplified] elim: valid.cases
        simp: replicate_Cons_eq)

  lemma lcounts_init: "lcount 0 = 1" "lcount 1 = 1" "lcount 2 = 1" "lcount 3 = 2"
    using lc0 lc1aux lc2aux lc3_aux unfolding lcount_def by simp_all


  subsubsection \<open>The Recursion Case\<close>

  lemma finite_valid_length:
    "finite {l. length l = n \<and> valid l}" (is "finite ?S")
  proof -
    have "?S \<subseteq> lists {R, B} \<inter> {l. length l = n}"
      by (auto intro: color.exhaust)
    moreover have "finite \<dots>"
      by (auto intro: lists_of_len_fin1)
    ultimately show ?thesis
      by (rule finite_subset)
  qed

  lemma valid_line_just_B:
    "valid (replicate n B)"
    by (induction n) (auto intro: valid.intros)

  lemma valid_line_aux:
    "{l. length l = n \<and> valid l} \<noteq> {}" (is "?S \<noteq> {}")
    using valid_line_just_B[of n] by force

  lemma replicate_unequal_aux:
    "replicate x R @ B # l \<noteq> replicate y R @ B # l'" (is "?l \<noteq> ?r") if \<open>x < y\<close> for l l'
  proof -
    have "?l ! x = B" "?r ! x = R"
      using that by (auto simp: nth_append)
    then show ?thesis
      by auto
  qed

  lemma valid_prepend_B_iff:
    "valid (B # xs) \<longleftrightarrow> valid xs"
    by (auto intro: valid.intros elim: valid.cases simp: Cons_replicate_eq Cons_eq_append_conv)

  lemma lcrec: "lcount n = lcount (n-1) + 1 + (\<Sum>i=3..<n. lcount (n-i-1))" if \<open>n>3\<close>
  proof -
    have "{l. length l = n \<and> valid l}
          = {l. length l = n \<and> valid (tl l) \<and> l!0=B}
          \<union> {l. length l = n \<and>
              (\<exists> i. i < n \<and> i \<ge> 3 \<and> (\<forall> k < i. l!k = R) \<and> l!i = B \<and> valid (drop (i + 1) l))}
          \<union> {l. length l = n \<and> (\<forall>i<n. l!i=R)}
          " (is "?A = ?B \<union> ?D \<union> ?C")
      using \<open>n > 3\<close> by (subst valid_split) auto
  
    let ?B1 = "((#) B) ` {l. length l = n - Suc 0 \<and> valid l}"
    from \<open>n > 3\<close> have "?B = ?B1"
      apply safe
      subgoal for l
        by (cases l) (auto simp: valid_prepend_B_iff)
      by auto
    have 1: "card ?B1 = lcount (n-1)"
      unfolding lcount_def by (auto intro: card_image)
  
    have "?C = {replicate n R}"
      by (auto simp: nth_equalityI)
    have 2: "card {replicate n R} = 1"
      by auto
  
    let ?D1="(\<Union> i \<in> {3..<n}. (\<lambda> l. replicate i R @ B # l)` {l. length l = n - i - 1 \<and> valid l})"
    have "?D =
        (\<Union>i \<in> {3..<n}. {l. length l = n \<and> (\<forall> k < i. l!k = R) \<and> l!i = B \<and> valid (drop (i + 1) l)})"
      by auto
    have "{l. length l = n \<and> (\<forall> k < i. l!k = R) \<and> l!i = B \<and> valid (drop (i + 1) l)}
              = (\<lambda> l. replicate i R @ B # l)` {l. length l = n - i - 1 \<and> valid l}"
      if "i < n" "2 < i" for i
      apply safe
      subgoal for l
        apply (rule image_eqI[where x = "drop (i + 1) l"])
         apply (rule nth_equalityI)
        using that
          apply (simp_all split: nat.split add: nth_Cons nth_append)
        using add_diff_inverse_nat apply fastforce
        done
      using that by (simp add: nth_append; fail)+
  
    then have D_eq: "?D = ?D1"
      unfolding \<open>?D = _\<close> by auto
  
    have inj: "inj_on (\<lambda>l. replicate x R @ B # l) {l. length l = n - Suc x \<and> valid l}" for x
      unfolding inj_on_def by auto
  
    have *:
      "(\<lambda>l. replicate x R @ B # l) ` {l. length l = n - Suc x \<and> valid l} \<inter>
         (\<lambda>l. replicate y R @ B # l) ` {l. length l = n - Suc y \<and> valid l} = {}"
      if "3 \<le> x" "x < y" "y < n" for x y
      using that replicate_unequal_aux[OF \<open>x < y\<close>] by auto
  
    have 3: "card ?D1 = (\<Sum>i=3..<n. lcount (n-i-1))"
    proof (subst card_Union_disjoint, goal_cases)
      case 1
      show ?case
        unfolding pairwise_def disjnt_def
      proof (clarsimp, goal_cases)
        case prems: (1 x y)
        from prems show ?case
          apply -
          apply (rule linorder_cases[of x y])
            apply (rule *; assumption)
           apply (simp; fail)
          apply (subst Int_commute; rule *; assumption)
          done
      qed
    next
      case 3
      show ?case
      proof (subst sum.reindex, unfold inj_on_def, clarsimp, goal_cases)
        case prems: (1 x y)
        with *[of y x] *[of x y] valid_line_aux[of "n - Suc x"] show ?case
          by - (rule linorder_cases[of x y], auto)
      next
        case 2
        then show ?case
          by (simp add: lcount_def card_image[OF inj])
      qed
    qed (auto intro: finite_subset[OF _ finite_valid_length])
  
    show ?thesis
      apply (subst lcount_def)
      unfolding \<open>?A = _\<close> \<open>?B = _\<close> \<open>?C = _\<close> D_eq
      apply (subst card_Un_disjoint)
        (* Finiteness *)
         apply (blast intro: finite_subset[OF _ finite_valid_length])+
        (* Disjointness *)
      subgoal
        using Cons_replicate_eq[of B _ n R] replicate_unequal_aux by fastforce
      apply (subst card_Un_disjoint)
        (* Finiteness *)
         apply (blast intro: finite_subset[OF _ finite_valid_length])+
        (* Disjointness & final rewriting *)
      unfolding 1 2 3
      by (auto simp: Cons_replicate_eq Cons_eq_append_conv)
  qed

subsection \<open>Verification of Program\<close>  
  subsubsection \<open>Inner Loop: Summation\<close>
  definition "sum_prog \<Phi> l u f \<equiv> 
    nfoldli [l..<u] (\<lambda>_. True) (\<lambda>i s. doN {
      ASSERT (\<Phi> i); 
      RETURN (s+f i)
    }) 0"
   
  lemma sum_spec[THEN SPEC_trans, refine_vcg]: 
    assumes "l\<le>u"
    assumes "\<And>i. l\<le>i \<Longrightarrow> i<u \<Longrightarrow> \<Phi> i" 
    shows "sum_prog \<Phi> l u f \<le> SPEC (\<lambda>r. r=(\<Sum>i=l..<u. f i))"
    unfolding sum_prog_def
    supply nfoldli_upt_rule[where I="\<lambda>j s. s=(\<Sum>i=l..<j. f i)", refine_vcg]
    apply refine_vcg
    using assms
    apply auto
    done    

  subsubsection \<open>Main Program\<close>    
  definition "icount M \<equiv> doN {
    ASSERT (M>2);
    let c = op_array_replicate (M+1) 0;
    let c = c[0:=1, 1:=1, 2:=1, 3:=2];
    
    ASSERT (\<forall>i<4. c!i = lcount i);
    
    c\<leftarrow>nfoldli [4..<M+1] (\<lambda>_. True) (\<lambda>n c. doN {
      \<^cancel>\<open>\<open>let sum =    (\<Sum>i=3..<n. c!(n-i-1));\<close>\<close>
      sum \<leftarrow> sum_prog (\<lambda>i. n-i-1 < length c) 3 n (\<lambda>i. c!(n-i-1));
      ASSERT (n-1<length c \<and> n<length c);
      RETURN (c[n := c!(n-1) + 1 + sum])
    }) c;
    
    ASSERT (\<forall>i\<le>M. c!i = lcount i);
    
    ASSERT (M < length c);
    RETURN (c!M)
  }"  
  
  subsubsection \<open>Abstract Correctness Statement\<close>    
  theorem icount_correct: "M>2 \<Longrightarrow> icount M \<le> SPEC (\<lambda>r. r=lcount M)"    
    unfolding icount_def
    thm nfoldli_upt_rule
    supply nfoldli_upt_rule[where 
      I="\<lambda>n c. length c = M+1 \<and> ( \<forall>i<n. c!i = lcount i)", refine_vcg]
    apply refine_vcg
    apply (auto simp:)
    subgoal for i
      apply (subgoal_tac "i\<in>{0,1,2,3}") using lcounts_init
      by (auto)
    
    subgoal for i c j
      apply (cases "j<i")
      apply auto
      apply (subgoal_tac "i=j")  
      apply auto
      apply (subst lcrec[where n=j])
      apply auto
      done
    done            


  subsection \<open>Refinement to Imperative Code\<close>  
  sepref_definition icount_impl is "icount" :: "nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"  
    unfolding icount_def sum_prog_def
    by sepref

  subsubsection \<open>Main Correctness Statement\<close>
  text \<open>
  As the main theorem, we prove the following Hoare triple, stating:
  starting from the empty heap, our program will compute the correct result (@{term "lcount M"}).
  \<close>
  theorem icount_impl_correct: 
    "M>2 \<Longrightarrow> <emp> icount_impl M <\<lambda>r. \<up>(r = lcount M)>\<^sub>t"
  proof -
    note A = icount_impl.refine[to_hnr, THEN hn_refineD]
    note A = A[unfolded autoref_tag_defs]
    note A = A[unfolded hn_ctxt_def pure_def, of M M, simplified]
    note [sep_heap_rules] = A

    assume "M>2"
        
    show ?thesis
      using icount_correct[OF \<open>M>2\<close>]
      by (sep_auto simp: refine_pw_simps pw_le_iff)    
  qed  

  subsubsection \<open>Code Export\<close>    
  export_code icount_impl in SML_imp module_name Tiling    
  export_code icount_impl in OCaml_imp module_name Tiling   
  export_code icount_impl in Haskell module_name Tiling   
  export_code icount_impl in Scala_imp module_name Tiling   


subsection \<open>Alternative Problem Specification\<close>  
  text \<open>Alternative definition of a valid line that we used in the competition\<close>

context fixes l :: "color list" begin

  inductive valid_point where
    "\<lbrakk>i+2<length l; l!i=R; l!(i+1) = R; l!(i+2) = R \<rbrakk> \<Longrightarrow> valid_point i"
  | "\<lbrakk>1\<le>i;i+1<length l; l!(i-1)=R; l!(i) = R; l!(i+1) = R \<rbrakk> \<Longrightarrow> valid_point i"
  | "\<lbrakk>2\<le>i; i<length l; l!(i-2)=R; l!(i-1) = R; l!(i) = R \<rbrakk> \<Longrightarrow> valid_point i"
  | "\<lbrakk> i<length l; l!i=B\<rbrakk> \<Longrightarrow> valid_point i"


  definition "valid_line = (\<forall>i<length l. valid_point i)"
end

lemma valid_lineI:
  assumes "\<And> i. i < length l \<Longrightarrow> valid_point l i"
  shows "valid_line l"
  using assms unfolding valid_line_def by auto

lemma valid_B_first:
  "valid_point xs i \<Longrightarrow> i < length xs \<Longrightarrow> valid_point (B # xs) (i + 1)"
  by (auto intro: valid_point.intros simp: numeral_2_eq_2 elim!: valid_point.cases)

lemma valid_line_prepend_B:
  "valid_line (B # xs)" if "valid_line xs"
  using that
  apply -
  apply (rule valid_lineI)
  subgoal for i
    by (cases i) (auto intro: valid_B_first[simplified] valid_point.intros simp: valid_line_def)
  done

lemma valid_drop_B:
  "valid_point xs (i - 1)" if "valid_point (B # xs) i" "i > 0"
  using that
  apply cases
     apply (fastforce intro: valid_point.intros)
  subgoal
    by (cases "i = 1") (auto intro: valid_point.intros(2))
  subgoal
    unfolding numeral_nat by (cases "i = 2") (auto intro: valid_point.intros(3))
  apply (fastforce intro: valid_point.intros)
  done

lemma valid_line_drop_B:
  "valid_line xs" if "valid_line (B # xs)"
  using that unfolding valid_line_def
proof (safe, goal_cases)
  case (1 i)
  with valid_drop_B[of xs "i + 1"] show ?case
    by auto
qed

lemma valid_line_prepend_B_iff:
  "valid_line (B # xs) \<longleftrightarrow> valid_line xs"
  using valid_line_prepend_B valid_line_drop_B by metis

lemma cases_valid_line:
  assumes
    "l = [] \<or>
    (l!0 = B \<and> valid_line (tl l)) \<or>
    length l \<ge> 3 \<and> (\<forall> i < length l. l ! i = R) \<or>
    (\<exists> j < length l. j \<ge> 3 \<and> (\<forall> i < j. l ! i = R) \<and> l ! j = B \<and> valid_line (drop (j + 1) l))"
    (is "?a \<or> ?b \<or> ?c \<or> ?d")
  shows "valid_line l"
proof -
  from assms consider (empty) ?a | (B) "\<not> ?a \<and> ?b" | (all_red) ?c | (R_B) ?d
    by blast
  then show ?thesis
  proof cases
    case empty
    then show ?thesis
      by (simp add: valid_line_def)
  next
    case B
    then show ?thesis
      by (cases l) (auto simp: valid_line_prepend_B_iff)
  next
    case prems: all_red
    show ?thesis
    proof (rule valid_lineI)
      fix i assume "i < length l"
      consider "i = 0" | "i = 1" | "i > 1"
        by atomize_elim auto
      then show "valid_point l i"
        using \<open>i < _\<close> prems by cases (auto 4 4 intro: valid_point.intros)
    qed
  next
    case R_B
    then obtain j where j:
      "j<length l" "3 \<le> j" "(\<forall>i<j. l ! i = R)" "l ! j = B" "valid_line (drop (j + 1) l)"
      by blast
    show ?thesis
    proof (rule valid_lineI)
      fix i assume "i < length l"
      with \<open>j \<ge> 3\<close> consider "i \<le> j - 3" | "i = j - 2" | "i = j - 1" | "i = j" | "i > j"
        by atomize_elim auto
      then show "valid_point l i"
      proof cases
        case 5
        with \<open>valid_line _\<close> \<open>i < length l\<close> have "valid_point (drop (j + 1) l) (i - j - 1)"
          unfolding valid_line_def by auto
        then show ?thesis
          using \<open>i > j\<close> by cases (auto intro: valid_point.intros)
      qed (use j in \<open>auto intro: valid_point.intros\<close>)
    qed
  qed
qed

lemma valid_line_cases:
  "l = [] \<or>
  (l!0 = B \<and> valid_line (tl l)) \<or>
  length l \<ge> 3 \<and> (\<forall> i < length l. l ! i = R) \<or>
  (\<exists> j < length l. j \<ge> 3 \<and> (\<forall> i < j. l ! i = R) \<and> l ! j = B \<and> valid_line (drop (j + 1) l))"
  if "valid_line l"
proof (cases "l = []")
  case True
  then show ?thesis
    by (simp add: valid_line_def)
next
  case False
  show ?thesis
  proof (cases "l!0 = B")
    case True
    with \<open>l \<noteq> []\<close> have "l = B # tl l"
      by (cases l) auto
    with \<open>valid_line l\<close> True show ?thesis
      by (metis valid_line_prepend_B_iff)
  next
    case False
    from \<open>valid_line l\<close> \<open>l \<noteq> []\<close> have "valid_point l 0"
      unfolding valid_line_def by auto
    with False have red_start: "length l \<ge> 3" "l!0 = R" "l!1 = R" "l!2 = R"
      by (auto elim!: valid_point.cases simp: numeral_2_eq_2)
    show ?thesis
    proof (cases "\<forall>i < length l. l ! i = R")
      case True
      with \<open>length l \<ge> 3\<close> show ?thesis
        by auto
    next
      case False
      let ?S = "{j. j < length l \<and> j \<ge> 3 \<and> l ! j = B}" let ?j = "Min ?S"
      have B_ge_3: "i \<ge> 3" if "l ! i = B" for i
      proof -
        consider "i = 0" | "i = 1" | "i = 2" | "i \<ge> 3"
          by atomize_elim auto
        then show "i \<ge> 3"
          using red_start \<open>l ! i = B\<close> by cases auto
      qed
      from False obtain i where "l ! i = B" "i < length l" "i \<ge> 3"
        by (auto intro: B_ge_3 color.exhaust)
      then have "?j \<in> ?S"
        by - (rule Min_in, auto)
      have "\<forall>i < ?j. l ! i = R"
      proof -
        {
          fix i assume "i < ?j" "l ! i = B"
          then have "i \<ge> 3"
            by (auto intro: B_ge_3)
          with \<open>i < ?j\<close> \<open>l ! i = B\<close> red_start \<open>?j \<in> ?S\<close> have "i \<in> ?S"
            by auto
          then have "?j \<le> i"
            by (auto intro: Min_le)
          with \<open>i < ?j\<close> have False
            by simp
        }
        then show ?thesis
          by (auto intro: color.exhaust)
      qed
      with \<open>?j \<in> ?S\<close> obtain j where j: "j < length l" "j \<ge> 3" "\<forall>i < j. l ! i = R" "l ! j = B"
        by blast
      moreover have "valid_line (drop (j + 1) l)"
      proof (rule valid_lineI)
        fix i assume "i < length (drop (j + 1) l)"
        with j \<open>valid_line l\<close> have "valid_point l (j + i + 1)"
          unfolding valid_line_def by auto
        then show "valid_point (drop (j + 1) l) i"
        proof cases
          case 2
          then show ?thesis
            using j by (cases i) (auto intro: valid_point.intros)
        next
          case prems: 3
          consider "i = 0" | "i = 1" | "i > 1"
            by atomize_elim auto
          then show ?thesis
            using j prems by cases (auto intro: valid_point.intros)
        qed (auto intro: valid_point.intros)
      qed
      ultimately show ?thesis
        by auto
    qed
  qed
qed

lemma valid_line_split:
  "valid_line l \<longleftrightarrow>
  l = [] \<or>
  (l!0 = B \<and> valid_line (tl l)) \<or>
  length l \<ge> 3 \<and> (\<forall> i < length l. l ! i = R) \<or>
  (\<exists> j < length l. j \<ge> 3 \<and> (\<forall> i < j. l ! i = R) \<and> l ! j = B \<and> valid_line (drop (j + 1) l))"
  using valid_line_cases cases_valid_line by blast

text \<open>Connection to the easier definition given above\<close>
lemma valid_valid_line:
  "valid l \<longleftrightarrow> valid_line l"
  by (induction l rule: length_induct, subst valid_line_split, subst valid_split, auto)

end
