section\<open>Auxiliary results on arithmetic\<close>
theory Nat_Miscellanea imports ZF begin

text\<open>Most of these results will get used at some point for the
calculation of arities.\<close>
lemmas nat_succI =  Ord_succ_mem_iff [THEN iffD2,OF nat_into_Ord]

lemma nat_succD : "m \<in> nat \<Longrightarrow>  succ(n) \<in> succ(m) \<Longrightarrow> n \<in> m"
  by (drule_tac j="succ(m)" in ltI,auto elim:ltD)

lemmas zero_in =  ltD [OF nat_0_le]

lemma in_n_in_nat :  "m \<in> nat \<Longrightarrow> n \<in> m \<Longrightarrow> n \<in> nat"
  by(drule ltI[of "n"],auto simp add: lt_nat_in_nat)

lemma in_succ_in_nat : "m \<in> nat \<Longrightarrow> n \<in> succ(m) \<Longrightarrow> n \<in> nat"
  by(auto simp add:in_n_in_nat)

lemma ltI_neg : "x \<in> nat \<Longrightarrow> j \<le> x \<Longrightarrow> j \<noteq> x \<Longrightarrow> j < x"
  by (simp add: le_iff)

lemma succ_pred_eq  :  "m \<in> nat \<Longrightarrow> m \<noteq> 0  \<Longrightarrow> succ(pred(m)) = m"
  by (auto elim: natE)

lemma succ_ltI : "succ(j) < n \<Longrightarrow> j < n"
  by (simp add: succ_leE[OF leI])

lemma succ_In : "n \<in> nat \<Longrightarrow> succ(j) \<in> n \<Longrightarrow> j \<in> n"
  by (rule succ_ltI[THEN ltD], auto intro: ltI)

lemmas succ_leD = succ_leE[OF leI]

lemma succpred_leI : "n \<in> nat \<Longrightarrow>  n \<le> succ(pred(n))"
  by (auto elim: natE)

lemma succpred_n0 : "succ(n) \<in> p \<Longrightarrow> p\<noteq>0"
  by (auto)


lemma funcI : "f \<in> A \<rightarrow> B \<Longrightarrow> a \<in> A \<Longrightarrow> b= f ` a \<Longrightarrow> \<langle>a, b\<rangle> \<in> f"
  by(simp_all add: apply_Pair)

lemmas natEin = natE [OF lt_nat_in_nat]

lemma succ_in : "succ(x) \<le> y  \<Longrightarrow> x \<in> y"
  by (auto dest:ltD)

lemmas Un_least_lt_iffn =  Un_least_lt_iff [OF nat_into_Ord nat_into_Ord]

lemma pred_le2 : "n\<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> pred(n) \<le> m \<Longrightarrow> n \<le> succ(m)"
  by(subgoal_tac "n\<in>nat",rule_tac n="n" in natE,auto)

lemma pred_le : "n\<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> n \<le> succ(m) \<Longrightarrow> pred(n) \<le> m"
  by(subgoal_tac "pred(n)\<in>nat",rule_tac n="n" in natE,auto)

lemma Un_leD1 : "Ord(i)\<Longrightarrow> Ord(j)\<Longrightarrow> Ord(k)\<Longrightarrow>  i \<union> j \<le> k \<Longrightarrow> i \<le> k"   
  by (rule Un_least_lt_iff[THEN iffD1[THEN conjunct1]],simp_all)

lemma Un_leD2 : "Ord(i)\<Longrightarrow> Ord(j)\<Longrightarrow> Ord(k)\<Longrightarrow>  i \<union> j \<le>k \<Longrightarrow> j \<le> k"   
  by (rule Un_least_lt_iff[THEN iffD1[THEN conjunct2]],simp_all)

lemma gt1 : "n \<in> nat \<Longrightarrow> i \<in> n \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> i \<noteq> 1 \<Longrightarrow> 1<i"
  by(rule_tac n="i" in natE,erule in_n_in_nat,auto intro: Ord_0_lt)

lemma pred_mono : "m \<in> nat \<Longrightarrow> n \<le> m \<Longrightarrow> pred(n) \<le> pred(m)"
  by(rule_tac n="n" in natE,auto simp add:le_in_nat,erule_tac n="m" in natE,auto)

lemma succ_mono : "m \<in> nat \<Longrightarrow> n \<le> m \<Longrightarrow> succ(n) \<le> succ(m)"
  by auto

lemma pred2_Un: 
  assumes "j \<in> nat" "m \<le> j" "n \<le> j" 
  shows "pred(pred(m \<union> n)) \<le> pred(pred(j))" 
  using assms pred_mono[of "j"] le_in_nat Un_least_lt pred_mono by simp

lemma nat_union_abs1 : 
  "\<lbrakk> Ord(i) ; Ord(j) ; i \<le> j \<rbrakk> \<Longrightarrow> i \<union> j = j"
  by (rule Un_absorb1,erule le_imp_subset)

lemma nat_union_abs2 : 
  "\<lbrakk> Ord(i) ; Ord(j) ; i \<le> j \<rbrakk> \<Longrightarrow> j \<union> i = j"
  by (rule Un_absorb2,erule le_imp_subset)

lemma nat_un_max : "Ord(i) \<Longrightarrow> Ord(j) \<Longrightarrow> i \<union> j = max(i,j)"
  using max_def nat_union_abs1 not_lt_iff_le leI nat_union_abs2
  by auto

lemma nat_max_ty : "Ord(i) \<Longrightarrow>Ord(j) \<Longrightarrow> Ord(max(i,j))"
  unfolding max_def by simp

lemma le_not_lt_nat : "Ord(p) \<Longrightarrow> Ord(q) \<Longrightarrow> \<not> p\<le> q \<Longrightarrow> q \<le> p" 
  by (rule ltE,rule not_le_iff_lt[THEN iffD1],auto,drule ltI[of q p],auto,erule leI)

lemmas nat_simp_union = nat_un_max nat_max_ty max_def 

lemma le_succ : "x\<in>nat \<Longrightarrow> x\<le>succ(x)" by simp
lemma le_pred : "x\<in>nat \<Longrightarrow> pred(x)\<le>x" 
  using pred_le[OF _ _ le_succ] pred_succ_eq 
  by simp

lemma Un_le_compat : "o \<le> p \<Longrightarrow> q \<le> r \<Longrightarrow> Ord(o) \<Longrightarrow> Ord(p) \<Longrightarrow> Ord(q) \<Longrightarrow> Ord(r) \<Longrightarrow> o \<union> q \<le> p \<union> r"
  using le_trans[of q r "p\<union>r",OF _ Un_upper2_le] le_trans[of o p "p\<union>r",OF _ Un_upper1_le]
    nat_simp_union 
  by auto

lemma Un_le : "p \<le> r \<Longrightarrow> q \<le> r \<Longrightarrow>
               Ord(p) \<Longrightarrow> Ord(q) \<Longrightarrow> Ord(r) \<Longrightarrow> 
                p \<union> q \<le> r"
  using nat_simp_union by auto

lemma Un_leI3 : "o \<le> r \<Longrightarrow> p \<le> r \<Longrightarrow> q \<le> r \<Longrightarrow> 
                Ord(o) \<Longrightarrow> Ord(p) \<Longrightarrow> Ord(q) \<Longrightarrow> Ord(r) \<Longrightarrow> 
                o \<union> p \<union> q \<le> r"
  using nat_simp_union by auto

lemma diff_mono :
  assumes "m \<in> nat" "n\<in>nat" "p \<in> nat" "m < n" "p\<le>m"
  shows "m#-p < n#-p"
proof -
  from assms
  have "m#-p \<in> nat" "m#-p #+p = m"
    using add_diff_inverse2 by simp_all
  with assms
  show ?thesis
    using less_diff_conv[of n p "m #- p",THEN iffD2] by simp
qed

lemma pred_Un:
  "x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> Arith.pred(succ(x) \<union> y) = x \<union> Arith.pred(y)"
  "x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> Arith.pred(x \<union> succ(y)) = Arith.pred(x) \<union> y"
  using pred_Un_distrib pred_succ_eq by simp_all

lemma le_natI : "j \<le> n \<Longrightarrow> n \<in> nat \<Longrightarrow> j\<in>nat"
  by(drule ltD,rule in_n_in_nat,rule nat_succ_iff[THEN iffD2,of n],simp_all)

lemma le_natE : "n\<in>nat \<Longrightarrow> j < n \<Longrightarrow>  j\<in>n"
  by(rule ltE[of j n],simp+)

lemma diff_cancel :
  assumes "m \<in> nat" "n\<in>nat" "m < n"
  shows "m#-n = 0"
  using assms diff_is_0_lemma leI by simp

lemma leD : assumes "n\<in>nat" "j \<le> n"
  shows "j < n | j = n"
  using leE[OF \<open>j\<le>n\<close>,of "j<n | j = n"] by auto

subsection\<open>Some results in ordinal arithmetic\<close>
text\<open>The following results are auxiliary to the proof of 
wellfoundedness of the relation \<^term>\<open>frecR\<close>\<close>

lemma max_cong :
  assumes "x \<le> y" "Ord(y)" "Ord(z)" shows "max(x,y) \<le> max(y,z)"
  using assms 
proof (cases "y \<le> z")
  case True
  then show ?thesis 
    unfolding max_def using assms by simp
next
  case False
  then have "z \<le> y"  using assms not_le_iff_lt leI by simp
  then show ?thesis 
    unfolding max_def using assms by simp 
qed

lemma max_commutes : 
  assumes "Ord(x)" "Ord(y)"
  shows "max(x,y) = max(y,x)"
  using assms Un_commute nat_simp_union(1) nat_simp_union(1)[symmetric] by auto

lemma max_cong2 :
  assumes "x \<le> y" "Ord(y)" "Ord(z)" "Ord(x)" 
  shows "max(x,z) \<le> max(y,z)"
proof -
  from assms 
  have " x \<union> z \<le> y \<union> z"
    using lt_Ord Ord_Un Un_mono[OF  le_imp_subset[OF \<open>x\<le>y\<close>]]  subset_imp_le by auto
  then show ?thesis 
    using  nat_simp_union \<open>Ord(x)\<close> \<open>Ord(z)\<close> \<open>Ord(y)\<close> by simp
qed

lemma max_D1 :
  assumes "x = y" "w < z"  "Ord(x)"  "Ord(w)" "Ord(z)" "max(x,w) = max(y,z)"
  shows "z\<le>y"
proof -
  from assms
  have "w <  x \<union> w" using Un_upper2_lt[OF \<open>w<z\<close>] assms nat_simp_union by simp
  then
  have "w < x" using assms lt_Un_iff[of x w w] lt_not_refl by auto
  then 
  have "y = y \<union> z" using assms max_commutes nat_simp_union assms leI by simp 
  then 
  show ?thesis using Un_leD2 assms by simp
qed

lemma max_D2 :
  assumes "w = y \<or> w = z" "x < y"  "Ord(x)"  "Ord(w)" "Ord(y)" "Ord(z)" "max(x,w) = max(y,z)"
  shows "x<w"
proof -
  from assms
  have "x < z \<union> y" using Un_upper2_lt[OF \<open>x<y\<close>] by simp
  then
  consider (a) "x < y" | (b) "x < w"
    using assms nat_simp_union by simp
  then show ?thesis proof (cases)
    case a
    consider (c) "w = y" | (d) "w = z" 
      using assms by auto
    then show ?thesis proof (cases)
      case c
      with a show ?thesis by simp
    next
      case d
      with a
      show ?thesis 
      proof (cases "y <w")
        case True       
        then show ?thesis using lt_trans[OF \<open>x<y\<close>] by simp
      next
        case False
        then
        have "w \<le> y" 
          using not_lt_iff_le[OF assms(5) assms(4)] by simp
        with \<open>w=z\<close>
        have "max(z,y) = y"  unfolding max_def using assms by simp
        with assms
        have "... = x \<union> w" using nat_simp_union max_commutes  by simp
        then show ?thesis using le_Un_iff assms by blast
      qed
    qed
  next
    case b
    then show ?thesis .
  qed
qed

lemma oadd_lt_mono2 :
  assumes  "Ord(n)" "Ord(\<alpha>)" "Ord(\<beta>)" "\<alpha> < \<beta>" "x < n" "y < n" "0 <n"
  shows "n ** \<alpha> ++ x < n **\<beta> ++ y"
proof -
  consider (0) "\<beta>=0" | (s) \<gamma> where  "Ord(\<gamma>)" "\<beta> = succ(\<gamma>)" | (l) "Limit(\<beta>)"
    using Ord_cases[OF \<open>Ord(\<beta>)\<close>,of ?thesis] by force
  then show ?thesis 
  proof cases
    case 0
    then show ?thesis using \<open>\<alpha><\<beta>\<close> by auto
  next
    case s
    then
    have "\<alpha>\<le>\<gamma>" using \<open>\<alpha><\<beta>\<close> using leI by auto
    then
    have "n ** \<alpha> \<le> n ** \<gamma>" using omult_le_mono[OF _ \<open>\<alpha>\<le>\<gamma>\<close>] \<open>Ord(n)\<close> by simp
    then
    have "n ** \<alpha> ++ x < n ** \<gamma> ++ n" using oadd_lt_mono[OF _ \<open>x<n\<close>] by simp
    also
    have "... = n ** \<beta>" using \<open>\<beta>=succ(_)\<close> omult_succ \<open>Ord(\<beta>)\<close> \<open>Ord(n)\<close> by simp
    finally
    have "n ** \<alpha> ++ x < n ** \<beta>" by auto
    then
    show ?thesis using oadd_le_self \<open>Ord(\<beta>)\<close> lt_trans2 \<open>Ord(n)\<close> by auto
  next
    case l
    have "Ord(x)" using \<open>x<n\<close> lt_Ord by simp
    with l
    have "succ(\<alpha>) < \<beta>" using Limit_has_succ \<open>\<alpha><\<beta>\<close> by simp
    have "n ** \<alpha> ++ x < n ** \<alpha> ++ n" 
      using oadd_lt_mono[OF le_refl[OF Ord_omult[OF _ \<open>Ord(\<alpha>)\<close>]] \<open>x<n\<close>] \<open>Ord(n)\<close> by simp
    also
    have "... = n ** succ(\<alpha>)" using omult_succ \<open>Ord(\<alpha>)\<close> \<open>Ord(n)\<close> by simp
    finally
    have "n ** \<alpha> ++ x < n ** succ(\<alpha>)" by simp 
    with \<open>succ(\<alpha>) < \<beta>\<close>
    have "n ** \<alpha> ++ x < n ** \<beta>" using lt_trans omult_lt_mono \<open>Ord(n)\<close> \<open>0<n\<close>  by auto      
    then show ?thesis using oadd_le_self \<open>Ord(\<beta>)\<close> lt_trans2 \<open>Ord(n)\<close> by auto
  qed
qed
end
