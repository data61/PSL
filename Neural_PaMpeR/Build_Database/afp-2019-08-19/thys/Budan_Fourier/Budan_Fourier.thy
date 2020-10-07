(*
    Title:      Budan-Fourier theorem
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Budan-Fourier theorem\<close>

theory Budan_Fourier imports
  BF_Misc
begin

text \<open>
The Budan-Fourier theorem is a classic result in real algebraic geometry to over-approximate
real roots of a polynomial (counting multiplicity) within an interval. When all roots of the 
the polynomial are known to be real, the over-approximation becomes tight -- the number of 
roots are counted exactly. Also note that Descartes' rule of sign is a direct consequence of
the Budan-Fourier theorem.

The proof mainly follows Theorem 2.35 in
  Basu, S., Pollack, R., Roy, M.-F.: Algorithms in Real Algebraic Geometry. 
  Springer Berlin Heidelberg, Berlin, Heidelberg (2006).
\<close>

subsection \<open>More results related to @{term sign_r_pos}\<close>

lemma sign_r_pos_nzero_right:
  assumes nzero:"\<forall>x. c<x \<and> x\<le>d \<longrightarrow> poly p x \<noteq>0" and "c<d"
  shows "if sign_r_pos p c then poly p d>0 else poly p d<0"
proof (cases "sign_r_pos p c")
  case True
  then obtain d' where "d'>c" and d'_pos:"\<forall>y>c. y < d' \<longrightarrow> 0 < poly p y"
    unfolding sign_r_pos_def eventually_at_right by auto
  have False when "\<not> poly p d>0"
  proof -
    have "\<exists>x>(c + min d d') / 2. x < d \<and> poly p x = 0"
      apply (rule poly_IVT_neg)
      using \<open>d'>c\<close> \<open>c<d\<close> that nzero[rule_format,of d,simplified]  
      by (auto intro:d'_pos[rule_format])
    then show False using nzero \<open>c < d'\<close> by auto
  qed
  then show ?thesis using True by auto
next
  case False
  then have "sign_r_pos (-p) c"  
    using sign_r_pos_minus[of p c] nzero[rule_format,of d,simplified] \<open>c<d\<close>
    by fastforce
  then obtain d' where "d'>c" and d'_neg:"\<forall>y>c. y < d' \<longrightarrow> 0 > poly p y"
    unfolding sign_r_pos_def eventually_at_right by auto
  have False when "\<not> poly p d<0"
  proof -
    have "\<exists>x>(c + min d d') / 2. x < d \<and> poly p x = 0"
      apply (rule poly_IVT_pos)
      using \<open>d'>c\<close> \<open>c<d\<close> that nzero[rule_format,of d,simplified]  
      by (auto intro:d'_neg[rule_format])
    then show False using nzero \<open>c < d'\<close> by auto
  qed
  then show ?thesis using False by auto
qed 

lemma sign_r_pos_at_left:
  assumes "p\<noteq>0"
  shows "if even (order c p) \<longleftrightarrow>sign_r_pos p c then eventually (\<lambda>x. poly p x>0) (at_left c)
         else eventually (\<lambda>x. poly p x<0) (at_left c)"
  using assms
proof (induct p rule:poly_root_induct_alt)
  case 0
  then show ?case by simp
next
  case (no_proots p)
  then have [simp]:"order c p = 0" using order_root by blast
  have ?case when "poly p c >0" 
  proof -
    have "\<forall>\<^sub>F x in at c. 0 < poly p x"
      using that 
      by (metis (no_types, lifting) less_linear no_proots.hyps not_eventuallyD 
          poly_IVT_neg poly_IVT_pos)
    then have "\<forall>\<^sub>F x in at_left c. 0 < poly p x"
      using eventually_at_split by blast
    moreover have "sign_r_pos p c" using sign_r_pos_rec[OF \<open>p\<noteq>0\<close>] that by auto
    ultimately show ?thesis by simp
  qed
  moreover have ?case when "poly p c <0" 
  proof -
    have "\<forall>\<^sub>F x in at c. poly p x < 0"
      using that 
      by (metis (no_types, lifting) less_linear no_proots.hyps not_eventuallyD 
          poly_IVT_neg poly_IVT_pos)
    then have "\<forall>\<^sub>F x in at_left c. poly p x < 0" 
      using eventually_at_split by blast
    moreover have "\<not> sign_r_pos p c" using sign_r_pos_rec[OF \<open>p\<noteq>0\<close>] that by auto
    ultimately show ?thesis by simp
  qed
  ultimately show ?case using no_proots(1)[of c] by argo
next
  case (root a p)
  define aa where "aa=[:-a,1:]"
  have [simp]:"aa\<noteq>0" "p\<noteq>0" using \<open>[:- a, 1:] * p \<noteq> 0\<close> unfolding aa_def by auto
  have ?case when "c>a"
  proof -
    have "?thesis = (if even (order c p) = sign_r_pos p c 
            then \<forall>\<^sub>F x in at_left c. 0 < poly (aa * p) x
            else \<forall>\<^sub>F x in at_left c. poly (aa * p) x < 0)"
    proof -
      have "order c aa=0" unfolding aa_def using order_0I that by force
      then have "even (order c (aa * p)) = even (order c p)"
        by (subst order_mult) auto
      moreover have "sign_r_pos aa c" 
        unfolding aa_def using that 
        by (auto simp: sign_r_pos_rec) 
      then have "sign_r_pos (aa * p) c = sign_r_pos p c"
        by (subst sign_r_pos_mult) auto
      ultimately show ?thesis
        by (fold aa_def) auto
    qed
    also have "... = (if even (order c p) = sign_r_pos p c 
            then \<forall>\<^sub>F x in at_left c. 0 < poly p x
            else \<forall>\<^sub>F x in at_left c. poly p x < 0)"
    proof -
      have "\<forall>\<^sub>F x in at_left c. 0 < poly aa x" 
        apply (simp add:aa_def)
        using that eventually_at_left_field by blast
      then have "(\<forall>\<^sub>F x in at_left c. 0 < poly (aa * p) x) \<longleftrightarrow> (\<forall>\<^sub>F x in at_left c. 0 < poly p x)"
        "(\<forall>\<^sub>F x in at_left c. 0 > poly (aa * p) x) \<longleftrightarrow> (\<forall>\<^sub>F x in at_left c. 0 > poly p x)"
        apply auto
        by (erule (1) eventually_elim2,simp add: zero_less_mult_iff mult_less_0_iff)+
      then show ?thesis by simp
    qed
    also have "..." using root.hyps by simp
    finally show ?thesis .
  qed
  moreover have ?case when "c<a"
  proof -
    have "?thesis = (if even (order c p) = sign_r_pos p c 
            then \<forall>\<^sub>F x in at_left c. poly (aa * p) x < 0
            else \<forall>\<^sub>F x in at_left c. 0 < poly (aa * p) x) "
    proof -
      have "order c aa=0" unfolding aa_def using order_0I that by force
      then have "even (order c (aa * p)) = even (order c p)"
        by (subst order_mult) auto
      moreover have "\<not> sign_r_pos aa c" 
        unfolding aa_def using that 
        by (auto simp: sign_r_pos_rec) 
      then have "sign_r_pos (aa * p) c = (\<not> sign_r_pos p c)"
        by (subst sign_r_pos_mult) auto
      ultimately show ?thesis
        by (fold aa_def) auto
    qed
    also have "... = (if even (order c p) = sign_r_pos p c 
            then \<forall>\<^sub>F x in at_left c. 0 < poly p x
            else \<forall>\<^sub>F x in at_left c. poly p x < 0)"
    proof -
      have "\<forall>\<^sub>F x in at_left c. poly aa x < 0" 
        apply (simp add:aa_def)
        using that eventually_at_filter by fastforce
      then have "(\<forall>\<^sub>F x in at_left c. 0 < poly (aa * p) x) \<longleftrightarrow> (\<forall>\<^sub>F x in at_left c. poly p x < 0)"
        "(\<forall>\<^sub>F x in at_left c. 0 > poly (aa * p) x) \<longleftrightarrow> (\<forall>\<^sub>F x in at_left c. 0 < poly p x)"
        apply auto
        by (erule (1) eventually_elim2,simp add: zero_less_mult_iff mult_less_0_iff)+
      then show ?thesis by simp
    qed
    also have "..." using root.hyps by simp
    finally show ?thesis .
  qed
  moreover have ?case when "c=a"
  proof -
    have "?thesis = (if even (order c p) = sign_r_pos p c 
            then \<forall>\<^sub>F x in at_left c. 0 > poly (aa * p) x
            else \<forall>\<^sub>F x in at_left c. poly (aa * p) x > 0)"
    proof -
      have "order c aa=1" unfolding aa_def using that 
        by (metis order_power_n_n power_one_right)
      then have "even (order c (aa * p)) = odd (order c p)"
        by (subst order_mult) auto
      moreover have "sign_r_pos aa c" 
        unfolding aa_def using that 
        by (auto simp: sign_r_pos_rec pderiv_pCons) 
      then have "sign_r_pos (aa * p) c = sign_r_pos p c"
        by (subst sign_r_pos_mult) auto
      ultimately show ?thesis
        by (fold aa_def) auto
    qed
    also have "... = (if even (order c p) = sign_r_pos p c 
            then \<forall>\<^sub>F x in at_left c. 0 < poly p x
            else \<forall>\<^sub>F x in at_left c. poly p x < 0)"
    proof -
      have "\<forall>\<^sub>F x in at_left c. 0 > poly aa x" 
        apply (simp add:aa_def)
        using that by (simp add: eventually_at_filter)
      then have "(\<forall>\<^sub>F x in at_left c. 0 < poly (aa * p) x) \<longleftrightarrow> (\<forall>\<^sub>F x in at_left c. 0 > poly p x)"
        "(\<forall>\<^sub>F x in at_left c. 0 > poly (aa * p) x) \<longleftrightarrow> (\<forall>\<^sub>F x in at_left c. 0 < poly p x)"
        apply auto
        by (erule (1) eventually_elim2,simp add: zero_less_mult_iff mult_less_0_iff)+
      then show ?thesis by simp
    qed
    also have "..." using root.hyps by simp
    finally show ?thesis .
  qed
  ultimately show ?case by argo
qed 

lemma sign_r_pos_nzero_left:
  assumes nzero:"\<forall>x. d\<le>x \<and> x<c \<longrightarrow> poly p x \<noteq>0" and "d<c"
  shows "if even (order c p) \<longleftrightarrow>sign_r_pos p c then poly p d>0 else poly p d<0"
proof (cases "even (order c p) \<longleftrightarrow>sign_r_pos p c")
  case True
  then have "eventually (\<lambda>x. poly p x>0) (at_left c)"
    using nzero[rule_format,of d,simplified] \<open>d<c\<close> sign_r_pos_at_left 
    by (simp add: order_root)
  then obtain d' where "d'<c" and d'_pos:"\<forall>y>d'. y < c \<longrightarrow> 0 < poly p y"
    unfolding eventually_at_left by auto
  have False when "\<not> poly p d>0"
  proof -
    have "\<exists>x>d. x < (c + max d d') / 2 \<and> poly p x = 0"
      apply (rule poly_IVT_pos)
      using \<open>d'<c\<close> \<open>c>d\<close> that nzero[rule_format,of d,simplified]  
      by (auto intro:d'_pos[rule_format])
    then show False using nzero \<open>c > d'\<close> by auto
  qed
  then show ?thesis using True by auto
next
  case False
  then have "eventually (\<lambda>x. poly p x<0) (at_left c)"
    using nzero[rule_format,of d,simplified] \<open>d<c\<close> sign_r_pos_at_left 
    by (simp add: order_root)
  then obtain d' where "d'<c" and d'_neg:"\<forall>y>d'. y < c \<longrightarrow> 0 > poly p y"
    unfolding eventually_at_left by auto
  have False when "\<not> poly p d<0"
  proof -
    have "\<exists>x>d. x < (c + max d d') / 2 \<and> poly p x = 0"
      apply (rule poly_IVT_neg)
      using \<open>d'<c\<close> \<open>c>d\<close> that nzero[rule_format,of d,simplified]  
      by (auto intro:d'_neg[rule_format])
    then show False using nzero \<open>c > d'\<close> by auto
  qed
  then show ?thesis using False by auto
qed

subsection \<open>Fourier sequences\<close>

function pders::"real poly \<Rightarrow> real poly list" where
  "pders p = (if p =0 then [] else Cons p (pders (pderiv p)))"
  by auto
termination
  apply (relation "measure (\<lambda>p. if p=0 then 0 else degree p + 1)")
  by (auto simp:degree_pderiv pderiv_eq_0_iff)

declare pders.simps[simp del]

lemma set_pders_nzero:
  assumes "p\<noteq>0" "q\<in>set (pders p)"
  shows "q\<noteq>0"
  using assms 
proof (induct p rule:pders.induct)
  case (1 p)
  then have "q \<in> set (p # pders (pderiv p))"
    by (simp add: pders.simps)
  then have "q=p \<or> q\<in>set (pders (pderiv p))" by auto  
  moreover have ?case when "q=p" 
    using that \<open>p\<noteq>0\<close> by auto
  moreover have ?case when "q\<in>set (pders (pderiv p))"
    using 1 pders.simps by fastforce
  ultimately show ?case by auto
qed

subsection \<open>Sign variations for Fourier sequences\<close>

definition changes_itv_der:: "real \<Rightarrow> real \<Rightarrow>real poly \<Rightarrow>  int" where
  "changes_itv_der a b p= (let ps= pders p in changes_poly_at ps a - changes_poly_at ps b)"

definition changes_gt_der:: "real \<Rightarrow>real poly \<Rightarrow> int" where
  "changes_gt_der a p= changes_poly_at (pders p) a"

definition changes_le_der:: "real \<Rightarrow>real poly \<Rightarrow> int" where
  "changes_le_der b p= (degree p - changes_poly_at (pders p) b)"

lemma changes_poly_pos_inf_pders[simp]:"changes_poly_pos_inf (pders p) = 0"
proof (induct "degree p" arbitrary:p)
  case 0
  then obtain a where "p=[:a:]" using degree_eq_zeroE by auto
  then show ?case 
    apply (cases "a=0")
    by (auto simp:changes_poly_pos_inf_def pders.simps)
next
  case (Suc x)
  then have "pderiv p\<noteq>0" "p\<noteq>0" using pderiv_eq_0_iff by force+
  define ps where "ps=pders (pderiv (pderiv p))"
  have ps:"pders p = p# pderiv p #ps" "pders (pderiv p) = pderiv p#ps"
    unfolding ps_def by (simp_all add: \<open>p \<noteq> 0\<close> \<open>pderiv p \<noteq> 0\<close> pders.simps)
  have hyps:"changes_poly_pos_inf (pders (pderiv p)) = 0"
    apply (rule Suc(1))
    using \<open>Suc x = degree p\<close> by (metis degree_pderiv diff_Suc_1)
  moreover have "sgn_pos_inf p * sgn_pos_inf (pderiv p) >0" 
    unfolding sgn_pos_inf_def lead_coeff_pderiv
    apply (simp add:algebra_simps sgn_mult)
    using Suc.hyps(2) \<open>p \<noteq> 0\<close> by linarith
  ultimately show ?case unfolding changes_poly_pos_inf_def ps by auto
qed

lemma changes_poly_neg_inf_pders[simp]: "changes_poly_neg_inf (pders p) = degree p"
proof (induct "degree p" arbitrary:p)
  case 0
  then obtain a where "p=[:a:]" using degree_eq_zeroE by auto
  then show ?case unfolding changes_poly_neg_inf_def by (auto simp: pders.simps)
next
  case (Suc x)
  then have "pderiv p\<noteq>0" "p\<noteq>0" using pderiv_eq_0_iff by force+
  then have "changes_poly_neg_inf (pders p)   
                  = changes_poly_neg_inf (p # pderiv p#pders (pderiv (pderiv p)))"
    by (simp add:pders.simps)
  also have "... = 1 +  changes_poly_neg_inf (pderiv p#pders (pderiv (pderiv p)))"
  proof -
    have "sgn_neg_inf p * sgn_neg_inf (pderiv p) < 0" 
      unfolding sgn_neg_inf_def using \<open>p\<noteq>0\<close> \<open>pderiv p\<noteq>0\<close>
      by (auto simp add:lead_coeff_pderiv degree_pderiv coeff_pderiv sgn_mult pderiv_eq_0_iff)
    then show ?thesis unfolding changes_poly_neg_inf_def by auto
  qed
  also have "... = 1 +  changes_poly_neg_inf (pders (pderiv p))" 
    using \<open>pderiv p\<noteq>0\<close> by (simp add:pders.simps)
  also have "... = 1 + degree (pderiv p)"
    apply (subst Suc(1))
    using Suc(2) by (auto simp add: degree_pderiv)
  also have "... = degree p"
    by (metis Suc.hyps(2) degree_pderiv diff_Suc_1 plus_1_eq_Suc)
  finally show ?case .
qed

lemma pders_coeffs_sgn_eq:"map (\<lambda>p. sgn(poly p 0)) (pders p) = map sgn (coeffs p)"
proof (induct "degree p" arbitrary:p)
  case 0
  then obtain a where "p=[:a:]" using degree_eq_zeroE by auto
  then show ?case by (auto simp: pders.simps)
next
  case (Suc x)
  then have "pderiv p\<noteq>0" "p\<noteq>0" using pderiv_eq_0_iff by force+

  have "map (\<lambda>p. sgn (poly p 0)) (pders p)  
          = sgn (poly p 0)# map (\<lambda>p. sgn (poly p 0)) (pders (pderiv p))"
    apply (subst pders.simps)
    using \<open>p\<noteq>0\<close> by simp
  also have "... = sgn (coeff p 0) # map sgn (coeffs (pderiv p))"
  proof -
    have "sgn (poly p 0) = sgn (coeff p 0)" by (simp add: poly_0_coeff_0)
    then show ?thesis 
      apply (subst Suc(1))
      subgoal by (metis Suc.hyps(2) degree_pderiv diff_Suc_1)
      subgoal by auto
      done
  qed
  also have "... =  map sgn (coeffs p)"
  proof (rule nth_equalityI)
    show p_length:"length (sgn (coeff p 0) # map sgn (coeffs (pderiv p)))
                         = length (map sgn (coeffs p))"
      by (metis Suc.hyps(2) \<open>p \<noteq> 0\<close> \<open>pderiv p \<noteq> 0\<close> degree_pderiv diff_Suc_1 length_Cons 
          length_coeffs_degree length_map)
    show "(sgn (coeff p 0) # map sgn (coeffs (pderiv p))) ! i = map sgn (coeffs p) ! i"
      if "i < length (sgn (coeff p 0) # map sgn (coeffs (pderiv p)))" for i
    proof -
      show "(sgn (coeff p 0) # map sgn (coeffs (pderiv p))) ! i = map sgn (coeffs p) ! i"
      proof (cases i)
        case 0
        then show ?thesis
          by (simp add: \<open>p \<noteq> 0\<close> coeffs_nth)
      next
        case (Suc i')
        then show ?thesis 
          using that p_length
          apply simp
          apply (subst (1 2) coeffs_nth)
          by (auto simp add: \<open>p \<noteq> 0\<close> \<open>pderiv p \<noteq> 0\<close> length_coeffs_degree coeff_pderiv sgn_mult)
      qed
    qed
  qed
  finally show ?case .
qed

lemma changes_poly_at_pders_0:"changes_poly_at (pders p) 0 = changes (coeffs p)"
  unfolding changes_poly_at_def
  apply (subst (1 2) changes_map_sgn_eq)
  by (auto simp add:pders_coeffs_sgn_eq comp_def)

subsection \<open>Budan-Fourier theorem\<close>

lemma budan_fourier_aux_right:
  assumes "c<d2" and "p\<noteq>0"
  assumes "\<forall>x. c<x\<and> x\<le>d2 \<longrightarrow> (\<forall>q\<in>set (pders p). poly q x\<noteq>0)"  
  shows "changes_itv_der c d2 p=0"
  using assms(2-3) 
proof (induct "degree p" arbitrary:p)
  case 0
  then obtain a where "p=[:a:]" "a\<noteq>0" by (metis degree_eq_zeroE pCons_0_0)
  then show ?case
    by (auto simp add:changes_itv_der_def pders.simps intro:order_0I)
next
  case (Suc n)
  then have [simp]:"pderiv p\<noteq>0" by (metis nat.distinct(1) pderiv_eq_0_iff)
  note nzero=\<open>\<forall>x. c < x \<and> x \<le> d2 \<longrightarrow> (\<forall>q\<in>set (pders p). poly q x \<noteq> 0)\<close>

  have hyps:"changes_itv_der c d2 (pderiv p) = 0"
    apply (rule Suc(1))
    subgoal by (metis Suc.hyps(2) degree_pderiv diff_Suc_1)
    subgoal by (simp add: Suc.prems(1) Suc.prems(2) pders.simps)
    subgoal by (simp add: Suc.prems(1) nzero pders.simps)
    done
  have pders_changes_c:"changes_poly_at (r# pders q) c = (if sign_r_pos q c \<longleftrightarrow> poly r c>0
          then changes_poly_at (pders q) c else 1+changes_poly_at (pders q) c)"
    when "poly r c\<noteq>0" "q\<noteq>0" for q r 
    using \<open>q\<noteq>0\<close>
  proof (induct q rule:pders.induct)
    case (1 q)
    have ?case when "pderiv q=0"
    proof -
      have "degree q=0" using that pderiv_eq_0_iff by blast
      then obtain a where "q=[:a:]" "a\<noteq>0" using \<open>q\<noteq>0\<close> by (metis degree_eq_zeroE pCons_0_0)
      then show ?thesis using \<open>poly r c\<noteq>0\<close>
        by (auto simp add:sign_r_pos_rec changes_poly_at_def mult_less_0_iff pders.simps)
    qed
    moreover have ?case when "pderiv q\<noteq>0" 
    proof -
      obtain qs where qs:"pders q=q#qs" "pders (pderiv q) = qs"
        using \<open>q\<noteq>0\<close> by (simp add:pders.simps)
      have "changes_poly_at (r # qs) c = (if sign_r_pos (pderiv q) c = (0 < poly r c) 
              then changes_poly_at qs c else 1 + changes_poly_at qs c)"
        using 1 \<open>pderiv q\<noteq>0\<close> unfolding qs by simp
      then show ?thesis unfolding qs
        apply (cases "poly q c=0")
        subgoal unfolding changes_poly_at_def by (auto simp:sign_r_pos_rec[OF \<open>q\<noteq>0\<close>,of c])
        subgoal unfolding changes_poly_at_def using \<open>poly r c\<noteq>0\<close>
          by (auto simp:sign_r_pos_rec[OF \<open>q\<noteq>0\<close>,of c] mult_less_0_iff)
        done
    qed
    ultimately show ?case by blast
  qed
  have pders_changes_d2:"changes_poly_at (r# pders q) d2 = (if sign_r_pos q c \<longleftrightarrow> poly r c>0
          then changes_poly_at (pders q) d2 else 1+changes_poly_at (pders q) d2)"
    when "poly r c\<noteq>0" "q\<noteq>0" and qr_nzero:"\<forall>x. c < x \<and> x \<le> d2 \<longrightarrow> poly r x \<noteq> 0 \<and> poly q x\<noteq>0" 
    for q r 
  proof -
    have "r\<noteq>0" using that(1) using poly_0 by blast
    obtain qs where qs:"pders q=q#qs" "pders (pderiv q) = qs"
      using \<open>q\<noteq>0\<close> by (simp add:pders.simps)
    have "if sign_r_pos r c then 0 < poly r d2 else poly r d2 < 0"
      "if sign_r_pos q c then 0 < poly q d2 else poly q d2 < 0"
      subgoal by (rule sign_r_pos_nzero_right[of c d2 r]) (use qr_nzero \<open>c<d2\<close> in auto)
      subgoal by (rule sign_r_pos_nzero_right[of c d2 q]) (use qr_nzero \<open>c<d2\<close> in auto)
      done
    then show ?thesis unfolding qs changes_poly_at_def
      using \<open>poly r c\<noteq>0\<close> by (auto split:if_splits simp:mult_less_0_iff sign_r_pos_rec[OF \<open>r\<noteq>0\<close>])
  qed
  have  d2c_nzero:"\<forall>x. c<x \<and> x\<le>d2 \<longrightarrow> poly p x\<noteq>0 \<and> poly (pderiv p) x \<noteq>0"
    and p_cons:"pders p = p#pders(pderiv p)"
    subgoal by (simp add: nzero Suc.prems(1) pders.simps)
    subgoal by (simp add: Suc.prems(1) pders.simps)
    done

  have ?case when "poly p c=0"
  proof -
    define ps where "ps=pders (pderiv (pderiv p))"
    have ps_cons:"p#pderiv p#ps = pders p" "pderiv p#ps=pders (pderiv p)"
      unfolding ps_def using \<open>p\<noteq>0\<close> by (auto simp:pders.simps)

    have "changes_poly_at (p # pderiv p # ps) c =  changes_poly_at (pderiv p # ps) c"
      unfolding changes_poly_at_def using that by auto
    moreover have "changes_poly_at (p # pderiv p # ps) d2 = changes_poly_at (pderiv p # ps) d2" 
    proof -
      have "if sign_r_pos p c then 0 < poly p d2 else poly p d2 < 0"
        apply (rule sign_r_pos_nzero_right[OF _ \<open>c<d2\<close>])
        using nzero[folded ps_cons] assms(1-2) by auto
      moreover have "if sign_r_pos (pderiv p) c then 0 < poly (pderiv p) d2 
                     else poly (pderiv p) d2 < 0"
        apply (rule sign_r_pos_nzero_right[OF _ \<open>c<d2\<close>])
        using nzero[folded ps_cons] assms(1-2) by auto
      ultimately have "poly p d2 * poly (pderiv p) d2 > 0" 
        unfolding zero_less_mult_iff sign_r_pos_rec[OF \<open>p\<noteq>0\<close>] using \<open>poly p c=0\<close>
        by (auto split:if_splits)
      then show ?thesis unfolding changes_poly_at_def by auto
    qed
    ultimately show ?thesis using hyps unfolding changes_itv_der_def
      apply (fold ps_cons)
      by (auto simp:Let_def)
  qed  
  moreover have ?case when "poly p c\<noteq>0" "sign_r_pos (pderiv p) c \<longleftrightarrow> poly p c>0"
  proof -
    have "changes_poly_at (pders p) c = changes_poly_at (pders (pderiv p)) c" 
      unfolding p_cons
      apply (subst pders_changes_c[OF \<open>poly p c\<noteq>0\<close>])
      using that by auto
    moreover have "changes_poly_at (pders p) d2 = changes_poly_at (pders (pderiv p)) d2" 
      unfolding p_cons
      apply (subst pders_changes_d2[OF \<open>poly p c\<noteq>0\<close> _ d2c_nzero])
      using that by auto
    ultimately show ?thesis using hyps unfolding changes_itv_der_def Let_def 
      by auto
  qed
  moreover have ?case when "poly p c\<noteq>0" "\<not> sign_r_pos (pderiv p) c \<longleftrightarrow> poly p c>0"
  proof -
    have "changes_poly_at (pders p) c = changes_poly_at (pders (pderiv p)) c +1" 
      unfolding p_cons
      apply (subst pders_changes_c[OF \<open>poly p c\<noteq>0\<close>])
      using that by auto
    moreover have "changes_poly_at (pders p) d2 = changes_poly_at (pders (pderiv p)) d2 + 1" 
      unfolding p_cons
      apply (subst pders_changes_d2[OF \<open>poly p c\<noteq>0\<close> _ d2c_nzero])
      using that by auto
    ultimately show ?thesis using hyps unfolding changes_itv_der_def Let_def 
      by auto
  qed
  ultimately show ?case by blast
qed

lemma budan_fourier_aux_left':
  assumes "d1<c" and "p\<noteq>0"
  assumes "\<forall>x. d1\<le>x\<and> x<c \<longrightarrow> (\<forall>q\<in>set (pders p). poly q x\<noteq>0)"
  shows "changes_itv_der d1 c p \<ge> order c p \<and> even (changes_itv_der d1 c p - order c p)"
  using assms(2-3) 
proof (induct "degree p" arbitrary:p)
  case 0
  then obtain a where "p=[:a:]" "a\<noteq>0" by (metis degree_eq_zeroE pCons_0_0)
  then show ?case
    apply (auto simp add:changes_itv_der_def pders.simps intro:order_0I)
    by (metis add.right_neutral dvd_0_right mult_zero_right order_root poly_pCons)
next
  case (Suc n)
  then have [simp]:"pderiv p\<noteq>0" by (metis nat.distinct(1) pderiv_eq_0_iff)
  note nzero=\<open>\<forall>x. d1 \<le> x \<and> x < c \<longrightarrow> (\<forall>q\<in>set (pders p). poly q x \<noteq> 0)\<close>
  define v where "v=order c (pderiv p)"

  have hyps:"v \<le> changes_itv_der d1 c (pderiv p) \<and> even (changes_itv_der d1 c (pderiv p) - v)" 
    unfolding v_def
    apply (rule Suc(1))
    subgoal by (metis Suc.hyps(2) degree_pderiv diff_Suc_1)
    subgoal by (simp add: Suc.prems(1) Suc.prems(2) pders.simps)
    subgoal by (simp add: Suc.prems(1) nzero pders.simps)
    done
  have pders_changes_c:"changes_poly_at (r# pders q) c = (if sign_r_pos q c \<longleftrightarrow> poly r c>0
          then changes_poly_at (pders q) c else 1+changes_poly_at (pders q) c)"
    when "poly r c\<noteq>0" "q\<noteq>0" for q r 
    using \<open>q\<noteq>0\<close>
  proof (induct q rule:pders.induct)
    case (1 q)
    have ?case when "pderiv q=0"
    proof -
      have "degree q=0" using that pderiv_eq_0_iff by blast
      then obtain a where "q=[:a:]" "a\<noteq>0" using \<open>q\<noteq>0\<close> by (metis degree_eq_zeroE pCons_0_0)
      then show ?thesis using \<open>poly r c\<noteq>0\<close>
        by (auto simp add:sign_r_pos_rec changes_poly_at_def mult_less_0_iff pders.simps)
    qed
    moreover have ?case when "pderiv q\<noteq>0" 
    proof -
      obtain qs where qs:"pders q=q#qs" "pders (pderiv q) = qs"
        using \<open>q\<noteq>0\<close> by (simp add:pders.simps)
      have "changes_poly_at (r # qs) c = (if sign_r_pos (pderiv q) c = (0 < poly r c) 
              then changes_poly_at qs c else 1 + changes_poly_at qs c)"
        using 1 \<open>pderiv q\<noteq>0\<close> unfolding qs by simp
      then show ?thesis unfolding qs
        apply (cases "poly q c=0")
        subgoal unfolding changes_poly_at_def by (auto simp:sign_r_pos_rec[OF \<open>q\<noteq>0\<close>,of c])
        subgoal unfolding changes_poly_at_def using \<open>poly r c\<noteq>0\<close>
          by (auto simp:sign_r_pos_rec[OF \<open>q\<noteq>0\<close>,of c] mult_less_0_iff)
        done
    qed
    ultimately show ?case by blast
  qed
  have pders_changes_d1:"changes_poly_at (r# pders q) d1 = (if even (order c q) \<longleftrightarrow> sign_r_pos q c \<longleftrightarrow> poly r c>0
          then changes_poly_at (pders q) d1 else 1+changes_poly_at (pders q) d1)"
    when "poly r c\<noteq>0" "q\<noteq>0" and qr_nzero:"\<forall>x. d1 \<le> x \<and> x < c \<longrightarrow> poly r x \<noteq> 0 \<and> poly q x\<noteq>0" 
    for q r
  proof -
    have "r\<noteq>0" using that(1) using poly_0 by blast
    obtain qs where qs:"pders q=q#qs" "pders (pderiv q) = qs"
      using \<open>q\<noteq>0\<close> by (simp add:pders.simps)
    have "if even (order c r) = sign_r_pos r c then 0 < poly r d1 else poly r d1 < 0"
      "if even (order c q) = sign_r_pos q c then 0 < poly q d1 else poly q d1 < 0"
      subgoal by (rule sign_r_pos_nzero_left[of d1 c r]) (use qr_nzero \<open>d1<c\<close> in auto)
      subgoal by (rule sign_r_pos_nzero_left[of d1 c q]) (use qr_nzero \<open>d1<c\<close> in auto)
      done
    moreover have "order c r=0" by (simp add: order_0I that(1))
    ultimately show ?thesis unfolding qs changes_poly_at_def
      using \<open>poly r c\<noteq>0\<close> by (auto split:if_splits simp:mult_less_0_iff sign_r_pos_rec[OF \<open>r\<noteq>0\<close>])
  qed
  have d1c_nzero:"\<forall>x. d1 \<le> x \<and> x < c \<longrightarrow> poly p x \<noteq> 0 \<and> poly (pderiv p) x \<noteq> 0"
    and p_cons:"pders p = p#pders(pderiv p)"
    by (simp_all add: nzero Suc.prems(1) pders.simps)     

  have ?case when "poly p c=0"
  proof -
    define ps where "ps=pders (pderiv (pderiv p))"
    have ps_cons:"p#pderiv p#ps = pders p" "pderiv p#ps=pders (pderiv p)"
      unfolding ps_def using \<open>p\<noteq>0\<close> by (auto simp:pders.simps)

    have p_order:"order c p = Suc v"
      apply (subst order_pderiv)
      using Suc.prems(1) order_root that unfolding v_def by auto
    moreover have "changes_poly_at (p#pderiv p # ps) d1 = changes_poly_at (pderiv p#ps) d1 +1"
    proof -
      have "if even (order c p) = sign_r_pos p c then 0 < poly p d1 else poly p d1 < 0"
        apply (rule sign_r_pos_nzero_left[OF _ \<open>d1<c\<close>])
        using nzero[folded ps_cons] assms(1-2) by auto
      moreover have "if even v = sign_r_pos (pderiv p) c 
                      then 0 < poly (pderiv p) d1 else poly (pderiv p) d1 < 0"
        unfolding v_def
        apply (rule sign_r_pos_nzero_left[OF _ \<open>d1<c\<close>])
        using nzero[folded ps_cons] assms(1-2) by auto
      ultimately have "poly p d1 * poly (pderiv p) d1 < 0" 
        unfolding mult_less_0_iff sign_r_pos_rec[OF \<open>p\<noteq>0\<close>] using \<open>poly p c=0\<close> p_order
        by (auto split:if_splits)
      then show ?thesis
        unfolding changes_poly_at_def by auto
    qed
    moreover have "changes_poly_at (p # pderiv p # ps) c =  changes_poly_at (pderiv p # ps) c"
      unfolding changes_poly_at_def using that by auto
    ultimately show ?thesis using hyps unfolding changes_itv_der_def
      apply (fold ps_cons)
      by (auto simp:Let_def)
  qed  
  moreover have ?case when "poly p c\<noteq>0" "odd v" "sign_r_pos (pderiv p) c \<longleftrightarrow> poly p c>0"
  proof -
    have "order c p=0" by (simp add: order_0I that(1))
    moreover have "changes_poly_at (pders p) d1 = changes_poly_at (pders (pderiv p)) d1 +1" 
      unfolding p_cons
      apply (subst pders_changes_d1[OF \<open>poly p c\<noteq>0\<close> _ d1c_nzero])
      using that unfolding v_def by auto
    moreover have "changes_poly_at (pders p) c = changes_poly_at (pders (pderiv p)) c" 
      unfolding p_cons
      apply (subst pders_changes_c[OF \<open>poly p c\<noteq>0\<close>])
      using that unfolding v_def by auto
    ultimately show ?thesis using hyps \<open>odd v\<close> unfolding changes_itv_der_def Let_def 
      by auto
  qed
  moreover have ?case when "poly p c\<noteq>0" "odd v" "\<not> sign_r_pos (pderiv p) c \<longleftrightarrow> poly p c>0"
  proof -
    have "v\<ge>1" using \<open>odd v\<close> using not_less_eq_eq by auto
    moreover have "order c p=0" by (simp add: order_0I that(1))
    moreover have "changes_poly_at (pders p) d1 = changes_poly_at (pders (pderiv p)) d1" 
      unfolding p_cons
      apply (subst pders_changes_d1[OF \<open>poly p c\<noteq>0\<close> _ d1c_nzero])
      using that unfolding v_def by auto
    moreover have "changes_poly_at (pders p) c = changes_poly_at (pders (pderiv p)) c + 1" 
      unfolding p_cons
      apply (subst pders_changes_c[OF \<open>poly p c\<noteq>0\<close>])
      using that unfolding v_def by auto
    ultimately show ?thesis using hyps \<open>odd v\<close> unfolding changes_itv_der_def Let_def 
      by auto
  qed
  moreover have ?case when "poly p c\<noteq>0" "even v" "sign_r_pos (pderiv p) c \<longleftrightarrow> poly p c>0"
  proof -
    have "order c p=0" by (simp add: order_0I that(1))
    moreover have "changes_poly_at (pders p) d1 = changes_poly_at (pders (pderiv p)) d1" 
      unfolding p_cons
      apply (subst pders_changes_d1[OF \<open>poly p c\<noteq>0\<close> _ d1c_nzero])
      using that unfolding v_def by auto
    moreover have "changes_poly_at (pders p) c = changes_poly_at (pders (pderiv p)) c" 
      unfolding p_cons
      apply (subst pders_changes_c[OF \<open>poly p c\<noteq>0\<close>])
      using that unfolding v_def by auto
    ultimately show ?thesis using hyps \<open>even v\<close> unfolding changes_itv_der_def Let_def 
      by auto
  qed
  moreover have ?case when "poly p c\<noteq>0" "even v" "\<not> sign_r_pos (pderiv p) c \<longleftrightarrow> poly p c>0"
  proof -
    have "order c p=0" by (simp add: order_0I that(1))
    moreover have "changes_poly_at (pders p) d1 = changes_poly_at (pders (pderiv p)) d1 + 1" 
      unfolding p_cons
      apply (subst pders_changes_d1[OF \<open>poly p c\<noteq>0\<close> _ d1c_nzero])
      using that unfolding v_def by auto
    moreover have "changes_poly_at (pders p) c = changes_poly_at (pders (pderiv p)) c +1" 
      unfolding p_cons
      apply (subst pders_changes_c[OF \<open>poly p c\<noteq>0\<close>])
      using that unfolding v_def by auto
    ultimately show ?thesis using hyps \<open>even v\<close> unfolding changes_itv_der_def Let_def 
      by auto
  qed
  ultimately show ?case by blast
qed

lemma budan_fourier_aux_left:
  assumes "d1<c" and "p\<noteq>0"
  assumes nzero:"\<forall>x. d1<x\<and> x<c \<longrightarrow> (\<forall>q\<in>set (pders p). poly q x\<noteq>0)"
  shows "changes_itv_der d1 c p \<ge> order c p" "even (changes_itv_der d1 c p - order c p)"
proof -
  define d where "d=(d1+c)/2"
  have "d1<d" "d<c" unfolding d_def using \<open>d1<c\<close> by auto

  have "changes_itv_der d1 d p = 0"
    apply (rule budan_fourier_aux_right[OF \<open>d1<d\<close> \<open>p\<noteq>0\<close>])
    using nzero \<open>d1<d\<close> \<open>d<c\<close> by auto
  moreover have "order c p \<le> changes_itv_der d c p \<and> even (changes_itv_der d c p - order c p)"
    apply (rule budan_fourier_aux_left'[OF \<open>d<c\<close> \<open>p\<noteq>0\<close>])
    using nzero \<open>d1<d\<close> \<open>d<c\<close> by auto
  ultimately show "changes_itv_der d1 c p \<ge> order c p" "even (changes_itv_der d1 c p - order c p)" 
    unfolding changes_itv_der_def Let_def by auto
qed

theorem budan_fourier_interval: 
  assumes "a<b" "p\<noteq>0"
  shows "changes_itv_der a b p \<ge> proots_count p {x. a< x \<and> x\<le> b} \<and> 
          even (changes_itv_der a b p - proots_count p {x. a< x \<and> x\<le> b})"
  using \<open>a<b\<close>
proof (induct "card {x. \<exists>p\<in>set (pders p). poly p x=0 \<and> a<x \<and> x<b}" arbitrary:b)
  case 0
  have nzero:"\<forall>x. a<x \<and> x<b \<longrightarrow> (\<forall>q\<in>set (pders p). poly q x\<noteq>0)"
  proof -
    define S where "S={x. \<exists>p\<in>set (pders p). poly p x = 0 \<and> a < x \<and> x < b}"
    have "finite S"
    proof -
      have "S \<subseteq> (\<Union>p\<in>set (pders p). proots p)"
        unfolding S_def by auto
      moreover have "finite (\<Union>p\<in>set (pders p). proots p)"
        apply (subst finite_UN)
        using set_pders_nzero[OF \<open>p\<noteq>0\<close>] by auto
      ultimately show ?thesis by (simp add: finite_subset)
    qed
    moreover have "card S = 0" unfolding S_def using 0 by auto
    ultimately have "S={}" by auto
    then show ?thesis unfolding S_def using \<open>a<b\<close> assms(2) pders.simps by fastforce
  qed
  from budan_fourier_aux_left[OF \<open>a<b\<close> \<open>p\<noteq>0\<close> this] 
  have "order b p \<le> changes_itv_der a b p" "even (changes_itv_der a b p - order b p)" by simp_all
  moreover have "proots_count p {x. a< x \<and> x\<le> b} = order b p"
  proof -
    have p_cons:"pders p=p#pders (pderiv p)" by (simp add: assms(2) pders.simps)
    have "proots_within p {x. a < x \<and> x \<le> b} = (if poly p b=0 then {b} else {})"
      using nzero \<open>a< b\<close> unfolding p_cons
      apply auto
      using not_le by fastforce
    then show ?thesis unfolding proots_count_def using order_root by auto
  qed
  ultimately show ?case by auto
next
  case (Suc n)
  define P where "P=(\<lambda>x. \<exists>p\<in>set (pders p). poly p x = 0)"
  define S where "S=(\<lambda>b. {x. P x \<and> a < x \<and> x < b})"
  define b' where "b'=Max (S b)"
  have f_S:"finite (S x)" for x
  proof -
    have "S x \<subseteq> (\<Union>p\<in>set (pders p). proots p)"
      unfolding S_def P_def by auto
    moreover have "finite (\<Union>p\<in>set (pders p). proots p)"
      apply (subst finite_UN)
      using set_pders_nzero[OF \<open>p\<noteq>0\<close>] by auto
    ultimately show ?thesis by (simp add: finite_subset)
  qed
  have "b'\<in>S b"
    unfolding b'_def
    apply (rule Max_in[OF f_S])
    using Suc(2) unfolding S_def P_def by force
  then have "a<b'" "b'<b" unfolding S_def by auto
  have b'_nzero:"\<forall>x. b'<x \<and> x<b \<longrightarrow> (\<forall>q\<in>set (pders p). poly q x\<noteq>0)" 
  proof (rule ccontr)
    assume "\<not> (\<forall>x. b' < x \<and> x < b \<longrightarrow> (\<forall>q\<in>set (pders p). poly q x \<noteq> 0))"
    then obtain bb where "P bb" "b'<bb" "bb<b" unfolding P_def by auto
    then have "bb\<in>S b" unfolding S_def using \<open>a<b'\<close> \<open>b'<b\<close> by auto
    from Max_ge[OF f_S this, folded b'_def] have "bb \<le> b'" .
    then show False using \<open>b'<bb\<close> by auto
  qed

  have hyps:"proots_count p {x. a < x \<and> x \<le> b'} \<le> changes_itv_der a b' p \<and>
                even (changes_itv_der a b' p - proots_count p {x. a < x \<and> x \<le> b'})"
  proof (rule Suc(1)[OF _ \<open>a<b'\<close>])
    have "S b= {b'} \<union> S b'"
    proof -
      have "{x. P x \<and> b' < x \<and> x < b} = {}" 
        using b'_nzero unfolding P_def by auto
      then have "{x. P x\<and> b' \<le> x \<and> x < b} = {b'}"
        using \<open>b'\<in>S b\<close> unfolding S_def by force
      moreover have "S b= S b' \<union>  {x. P x \<and> b' \<le> x \<and> x < b}"
        unfolding S_def using \<open>a<b'\<close> \<open>b'<b\<close> by auto
      ultimately show ?thesis by auto
    qed
    moreover have "Suc n = card (S b)" using Suc(2) unfolding S_def P_def by simp
    moreover have "b'\<notin>S b'" unfolding S_def by auto
    ultimately have "n=card (S b')" using f_S by auto
    then show "n = card {x. \<exists>p\<in>set (pders p). poly p x = 0 \<and> a < x \<and> x < b'}" 
      unfolding S_def P_def by simp
  qed
  moreover have "proots_count p {x. a < x \<and> x \<le> b} 
                    = proots_count p {x. a < x \<and> x \<le> b'} + order b p" 
  proof -
    have p_cons:"pders p=p#pders (pderiv p)" by (simp add: assms(2) pders.simps)
    have "proots_within p {x. b' < x \<and> x \<le> b} = (if poly p b=0 then {b} else {})"
      using b'_nzero \<open>b' < b\<close> unfolding p_cons
      apply auto
      using not_le by fastforce
    then have "proots_count p {x. b' < x \<and> x \<le> b} = order b p" 
      unfolding proots_count_def using order_root by auto
    moreover have "proots_count p {x. a < x \<and> x \<le> b} = proots_count p {x. a < x \<and> x \<le> b'} +
            proots_count p {x. b' < x \<and> x \<le> b}"
      apply (subst proots_count_union_disjoint[symmetric])
      using \<open>a<b'\<close> \<open>b'<b\<close> \<open>p\<noteq>0\<close> by (auto intro:arg_cong2[where f=proots_count])
    ultimately show ?thesis by auto
  qed
  moreover note budan_fourier_aux_left[OF \<open>b'<b\<close> \<open>p\<noteq>0\<close> b'_nzero]
  ultimately show ?case unfolding changes_itv_der_def Let_def by auto
qed 

theorem budan_fourier_gt: 
  assumes "p\<noteq>0"
  shows "changes_gt_der a p \<ge> proots_count p {x. a< x} \<and> 
          even (changes_gt_der a p - proots_count p {x. a< x})"
proof -
  define ps where "ps=pders p"
  obtain ub where ub_root:"\<forall>p\<in>set ps. \<forall>x. poly p x = 0 \<longrightarrow> x < ub"
    and ub_sgn:"\<forall>x\<ge>ub. \<forall>p\<in>set ps. sgn (poly p x) = sgn_pos_inf p"
    and "a < ub"
    using root_list_ub[of ps a] set_pders_nzero[OF \<open>p\<noteq>0\<close>,folded ps_def] by blast
  have "proots_count p {x. a< x} = proots_count p {x. a< x \<and> x \<le> ub}"
  proof -
    have "p\<in>set ps" unfolding ps_def by (simp add: assms pders.simps)
    then have "proots_within p {x. a< x} = proots_within p {x. a< x \<and> x\<le>ub}"
      using ub_root by fastforce
    then show ?thesis unfolding proots_count_def by auto
  qed
  moreover have "changes_gt_der a p = changes_itv_der a ub p"
  proof -
    have "map (sgn \<circ> (\<lambda>p. poly p ub)) ps = map sgn_pos_inf ps"
      using ub_sgn[THEN spec,of ub,simplified] 
      by (metis (mono_tags, lifting) comp_def list.map_cong0)
    hence "changes_poly_at ps ub=changes_poly_pos_inf ps"
      unfolding changes_poly_pos_inf_def changes_poly_at_def
      by (subst changes_map_sgn_eq,metis map_map)
    then have "changes_poly_at ps ub=0" unfolding ps_def by simp
    thus ?thesis unfolding changes_gt_der_def changes_itv_der_def ps_def
      by (simp add:Let_def)
  qed
  moreover have "proots_count p {x. a < x \<and> x \<le> ub} \<le> changes_itv_der a ub p \<and>
      even (changes_itv_der a ub p - proots_count p {x. a < x \<and> x \<le> ub})"
    using budan_fourier_interval[OF \<open>a<ub\<close> \<open>p\<noteq>0\<close>] .
  ultimately show ?thesis by auto
qed

text \<open>Descartes' rule of signs is a direct consequence of the Budan-Fourier theorem\<close>
theorem descartes_sign:
  fixes p::"real poly"
  assumes "p\<noteq>0"
  shows " changes (coeffs p) \<ge> proots_count p {x. 0 < x} \<and> 
          even (changes (coeffs p) - proots_count p {x. 0< x})"
  using budan_fourier_gt[OF \<open>p\<noteq>0\<close>,of 0] unfolding changes_gt_der_def
  by (simp add:changes_poly_at_pders_0)

theorem budan_fourier_le: 
  assumes "p\<noteq>0"
  shows "changes_le_der b p \<ge> proots_count p {x. x \<le>b} \<and> 
          even (changes_le_der b p - proots_count p {x. x \<le>b})"
proof -
  define ps where "ps=pders p"
  obtain lb where lb_root:"\<forall>p\<in>set ps. \<forall>x. poly p x = 0 \<longrightarrow> x > lb"
    and lb_sgn:"\<forall>x\<le>lb. \<forall>p\<in>set ps. sgn (poly p x) = sgn_neg_inf p"
    and "lb < b"
    using root_list_lb[of ps b] set_pders_nzero[OF \<open>p\<noteq>0\<close>,folded ps_def] by blast
  have "proots_count p {x. x \<le>b} = proots_count p {x. lb< x \<and> x \<le> b}"
  proof -
    have "p\<in>set ps" unfolding ps_def by (simp add: assms pders.simps)
    then have "proots_within p {x. x \<le>b} = proots_within p {x. lb< x \<and> x\<le>b}"
      using lb_root by fastforce
    then show ?thesis unfolding proots_count_def by auto
  qed
  moreover have "changes_le_der b p = changes_itv_der lb b p"
  proof -
    have "map (sgn \<circ> (\<lambda>p. poly p lb)) ps = map sgn_neg_inf ps"
      using lb_sgn[THEN spec,of lb,simplified] 
      by (metis (mono_tags, lifting) comp_def list.map_cong0)
    hence "changes_poly_at ps lb=changes_poly_neg_inf ps"
      unfolding changes_poly_neg_inf_def changes_poly_at_def
      by (subst changes_map_sgn_eq,metis map_map)
    then have "changes_poly_at ps lb=degree p" unfolding ps_def by simp
    thus ?thesis unfolding changes_le_der_def changes_itv_der_def ps_def
      by (simp add:Let_def)
  qed
  moreover have "proots_count p {x. lb < x \<and> x \<le> b} \<le> changes_itv_der lb b p \<and>
      even (changes_itv_der lb b p - proots_count p {x. lb < x \<and> x \<le> b})"
    using budan_fourier_interval[OF \<open>lb<b\<close> \<open>p\<noteq>0\<close>] .
  ultimately show ?thesis by auto
qed

subsection \<open>Count exactly when all roots are real\<close>

definition all_roots_real:: "real poly \<Rightarrow> bool " where 
  "all_roots_real p = (\<forall>r\<in>proots (map_poly of_real p). Im r=0)"

lemma all_roots_real_mult[simp]:
  "all_roots_real (p*q) \<longleftrightarrow> all_roots_real p \<and> all_roots_real q"
  unfolding all_roots_real_def by auto

lemma all_roots_real_const_iff:
  assumes all_real:"all_roots_real p"
  shows "degree p\<noteq>0 \<longleftrightarrow> (\<exists>x. poly p x=0)"
proof 
  assume "degree p \<noteq> 0"
  moreover have "degree p=0" when "\<forall>x. poly p x\<noteq>0"
  proof -
    define pp where "pp=map_poly complex_of_real p"
    have "\<forall>x. poly pp x\<noteq>0"
    proof (rule ccontr)
      assume "\<not> (\<forall>x. poly pp x \<noteq> 0)"
      then obtain x where "poly pp x=0" by auto
      moreover have "Im x=0"
        using all_real[unfolded all_roots_real_def, rule_format,of x,folded pp_def] \<open>poly pp x=0\<close> 
        by auto
      ultimately have "poly pp (of_real (Re x)) = 0"
        by (simp add: complex_is_Real_iff)
      then have "poly p (Re x) = 0"
        unfolding pp_def 
        by (metis Re_complex_of_real of_real_poly_map_poly zero_complex.simps(1))
      then show False using that by simp
    qed
    then obtain a where "pp=[:of_real a:]" "a\<noteq>0"
      by (metis \<open>degree p \<noteq> 0\<close> constant_degree degree_map_poly 
            fundamental_theorem_of_algebra of_real_eq_0_iff pp_def)
    then have "p=[:a:]" unfolding pp_def 
      by (metis map_poly_0 map_poly_pCons of_real_0 of_real_poly_eq_iff)
    then show ?thesis by auto
  qed
  ultimately show "\<exists>x. poly p x = 0" by auto
next
  assume "\<exists>x. poly p x = 0"
  then show "degree p \<noteq> 0" 
    by (metis UNIV_I all_roots_real_def assms degree_pCons_eq_if 
        imaginary_unit.sel(2) map_poly_0 nat.simps(3) order_root pCons_eq_0_iff 
        proots_within_iff synthetic_div_eq_0_iff synthetic_div_pCons zero_neq_one)
qed
  
lemma all_roots_real_degree:
  assumes "all_roots_real p" 
  shows "proots_count p UNIV =degree p" using assms 
proof (induct p rule:poly_root_induct_alt)
  case 0
  then have False using imaginary_unit.sel(2) unfolding all_roots_real_def by auto
  then show ?case by simp
next
  case (no_proots p)
  from all_roots_real_const_iff[OF this(2)] this(1)
  have "degree p=0" by auto
  then obtain a where "p=[:a:]" "a\<noteq>0" 
    by (metis degree_eq_zeroE no_proots.hyps poly_const_conv)
  then have "proots p={}" by auto
  then show ?case using \<open>p=[:a:]\<close> by (simp add:proots_count_def)
next
  case (root a p)
  define a1 where "a1=[:- a, 1:]"
  have "p\<noteq>0" using root.prems 
    apply auto
    using imaginary_unit.sel(2) unfolding all_roots_real_def by auto
  have "a1\<noteq>0" unfolding a1_def by auto

  have "proots_count (a1 * p) UNIV = proots_count a1 UNIV + proots_count p UNIV"
    using \<open>p\<noteq>0\<close> \<open>a1\<noteq>0\<close> by (subst proots_count_times,auto)
  also have "... = 1 + degree p"
  proof -
    have "proots_count a1 UNIV = 1" unfolding a1_def by (simp add: proots_count_pCons_1_iff)
    moreover have hyps:"proots_count p UNIV = degree p"
      apply (rule root.hyps)
      using root.prems[folded a1_def] unfolding all_roots_real_def by auto
    ultimately show ?thesis by auto
  qed
  also have "... = degree (a1*p)"
    apply (subst degree_mult_eq)
    using \<open>a1\<noteq>0\<close> \<open>p\<noteq>0\<close> unfolding a1_def by auto
  finally show ?case unfolding a1_def .
qed

lemma all_real_roots_mobius:
  fixes a b::real 
  assumes "all_roots_real p" and "a<b"
  shows "all_roots_real (fcompose p [:a,b:] [:1,1:])" using assms(1)
proof (induct p rule:poly_root_induct_alt)
  case 0
  then show ?case by simp
next
  case (no_proots p)
  from all_roots_real_const_iff[OF this(2)] this(1)
  have "degree p=0" by auto
  then obtain a where "p=[:a:]" "a\<noteq>0" 
    by (metis degree_eq_zeroE no_proots.hyps poly_const_conv)
  then show ?case by (auto simp add:all_roots_real_def)
next
  case (root x p)
  define x1 where "x1=[:- x, 1:]"
  define fx where "fx=fcompose x1 [:a, b:] [:1, 1:]"

  have "all_roots_real fx"
  proof (cases "x=b")
    case True
    then have "fx = [:a-x:]" "a\<noteq>x"
      subgoal unfolding fx_def by (simp add:fcompose_def smult_add_right x1_def)
      subgoal using \<open>a<b\<close> True by auto
      done
    then have "proots (map_poly complex_of_real fx) = {}"
      by auto
    then show ?thesis unfolding all_roots_real_def by auto
  next
    case False
    then have "fx = [:a-x,b-x:]" 
      unfolding fx_def by (simp add:fcompose_def smult_add_right x1_def)
    then have "proots (map_poly complex_of_real fx) = {of_real ((x-a)/(b-x))}"
      using False by (auto simp add:field_simps)
    then show ?thesis unfolding all_roots_real_def by auto
  qed
  moreover have "all_roots_real (fcompose p [:a, b:] [:1, 1:])"
    using root[folded x1_def] all_roots_real_mult by auto
  ultimately show ?case 
    apply (fold x1_def)
    by (auto simp add:fcompose_mult fx_def)
qed

text \<open>If all roots are real, we can use the 
      Budan-Fourier theorem to EXACTLY count the number of real roots.\<close>
corollary budan_fourier_real:
  assumes "p\<noteq>0" 
  assumes "all_roots_real p"
  shows "proots_count p {x. x \<le>a} = changes_le_der a p"
        "a<b \<Longrightarrow> proots_count p {x. a <x \<and> x \<le>b} = changes_itv_der a b p"
        "proots_count p {x. b <x} = changes_gt_der b p"
proof -
  have *:"proots_count p {x. x \<le>a} = changes_le_der a p
        \<and> proots_count p {x. a <x \<and> x \<le>b} = changes_itv_der a b p
        \<and> proots_count p {x. b <x} = changes_gt_der b p"
    when "a<b" for a b
  proof -
    define c1 c2 c3 where 
      "c1=changes_le_der a p - proots_count p {x. x \<le>a}" and
      "c2=changes_itv_der a b p - proots_count p {x. a <x \<and> x \<le>b}" and
      "c3=changes_gt_der b p - proots_count p {x. b <x}" 

    have "c1\<ge>0" "c2\<ge>0" "c3\<ge>0" 
      using budan_fourier_interval[OF \<open>a<b\<close> \<open>p\<noteq>0\<close>] budan_fourier_gt[OF \<open>p\<noteq>0\<close>,of b]
          budan_fourier_le[OF \<open>p\<noteq>0\<close>,of a] 
      unfolding c1_def c2_def c3_def by auto
    moreover have "c1+c2+c3=0" 
    proof -
      have proots_deg:"proots_count p UNIV =degree p"
        using all_roots_real_degree[OF \<open>all_roots_real p\<close>] .
      have "changes_le_der a p + changes_itv_der a b p + changes_gt_der b p = degree p"
        unfolding changes_le_der_def changes_itv_der_def changes_gt_der_def 
        by (auto simp add:Let_def)
      moreover have "proots_count p {x. x \<le>a} + proots_count p {x. a <x \<and> x \<le>b} 
          + proots_count p {x. b <x} = degree p"
        using \<open>p\<noteq>0\<close> \<open>a<b\<close>
        apply (subst proots_count_union_disjoint[symmetric],auto)+
        apply (subst proots_deg[symmetric])
        by (auto intro!:arg_cong2[where f=proots_count])
      ultimately show ?thesis unfolding c1_def c2_def c3_def
        by (auto simp add:algebra_simps)
    qed
    ultimately have "c1 =0 \<and> c2=0 \<and> c3=0" by auto
    then show ?thesis unfolding c1_def c2_def c3_def by auto
  qed
  show "proots_count p {x. x \<le>a} = changes_le_der a p" using *[of a "a+1"] by auto
  show "proots_count p {x. a <x \<and> x \<le>b} = changes_itv_der a b p" when "a<b"
    using *[OF that] by auto
  show "proots_count p {x. b <x} = changes_gt_der b p"
    using *[of "b-1" b] by auto
qed

text \<open>Similarly, Descartes' rule of sign counts exactly when all roots are real.\<close>
corollary descartes_sign_real:
  fixes p::"real poly" and a b::real
  assumes "p\<noteq>0" 
  assumes "all_roots_real p"
  shows "proots_count p {x. 0 < x} = changes (coeffs p)"
  using budan_fourier_real(3)[OF \<open>p\<noteq>0\<close> \<open>all_roots_real p\<close>] 
  unfolding changes_gt_der_def by (simp add:changes_poly_at_pders_0)

end