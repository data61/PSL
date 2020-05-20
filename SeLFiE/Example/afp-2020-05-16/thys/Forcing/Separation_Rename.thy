section\<open>Auxiliary renamings for Separation\<close>
theory Separation_Rename
  imports Interface Renaming
begin

lemmas apply_fun = apply_iff[THEN iffD1]

lemma nth_concat : "[p,t] \<in> list(A) \<Longrightarrow> env\<in> list(A) \<Longrightarrow> nth(1 #+ length(env),[p]@ env @ [t]) = t"
  by(auto simp add:nth_append)

lemma nth_concat2 : "env\<in> list(A) \<Longrightarrow> nth(length(env),env @ [p,t]) = p"
  by(auto simp add:nth_append)

lemma nth_concat3 : "env\<in> list(A) \<Longrightarrow> u = nth(succ(length(env)), env @ [pi, u])"
  by(auto simp add:nth_append)

definition 
  sep_var :: "i \<Rightarrow> i" where
  "sep_var(n) \<equiv> {\<langle>0,1\<rangle>,\<langle>1,3\<rangle>,\<langle>2,4\<rangle>,\<langle>3,5\<rangle>,\<langle>4,0\<rangle>,\<langle>5#+n,6\<rangle>,\<langle>6#+n,2\<rangle>}"

definition
  sep_env :: "i \<Rightarrow> i" where
  "sep_env(n) \<equiv> \<lambda> i \<in> (5#+n)-5 . i#+2"

definition weak :: "[i, i] \<Rightarrow> i" where
  "weak(n,m) \<equiv> {i#+m . i \<in> n}"

lemma weakD : 
  assumes "n \<in> nat" "k\<in>nat" "x \<in> weak(n,k)"
  shows "\<exists> i \<in> n . x = i#+k"
  using assms unfolding weak_def by blast

lemma weak_equal :
  assumes "n\<in>nat" "m\<in>nat"
  shows "weak(n,m) = (m#+n) - m"
proof -
  have "weak(n,m)\<subseteq>(m#+n)-m" 
  proof(intro subsetI)
    fix x
    assume "x\<in>weak(n,m)"
    with assms 
    obtain i where
      "i\<in>n" "x=i#+m"
      using weakD by blast
    then
    have "m\<le>i#+m" "i<n"
      using add_le_self2[of m i] \<open>m\<in>nat\<close> \<open>n\<in>nat\<close> ltI[OF \<open>i\<in>n\<close>] by simp_all
    then
    have "\<not>i#+m<m"
      using not_lt_iff_le in_n_in_nat[OF \<open>n\<in>nat\<close> \<open>i\<in>n\<close>] \<open>m\<in>nat\<close> by simp
    with \<open>x=i#+m\<close>
    have "x\<notin>m" 
      using ltI \<open>m\<in>nat\<close> by auto
    moreover
    from assms \<open>x=i#+m\<close> \<open>i<n\<close>
    have "x<m#+n"
      using add_lt_mono1[OF \<open>i<n\<close> \<open>n\<in>nat\<close>] by simp
    ultimately
    show "x\<in>(m#+n)-m" 
      using ltD DiffI by simp
  qed
  moreover
  have "(m#+n)-m\<subseteq>weak(n,m)" 
  proof (intro subsetI)
    fix x 
    assume "x\<in>(m#+n)-m"
    then 
    have "x\<in>m#+n" "x\<notin>m"
      using DiffD1[of x "n#+m" m] DiffD2[of x "n#+m" m] by simp_all
    then
    have "x<m#+n" "x\<in>nat" 
      using ltI in_n_in_nat[OF add_type[of m n]] by simp_all
    then
    obtain i where
      "m#+n = succ(x#+i)" 
      using less_iff_succ_add[OF \<open>x\<in>nat\<close>,of "m#+n"] add_type by auto
    then 
    have "x#+i<m#+n" using succ_le_iff by simp
    with \<open>x\<notin>m\<close> 
    have "\<not>x<m" using ltD by blast
    with \<open>m\<in>nat\<close> \<open>x\<in>nat\<close>
    have "m\<le>x" using not_lt_iff_le by simp 
    with \<open>x<m#+n\<close>  \<open>n\<in>nat\<close>
    have "x#-m<m#+n#-m" 
      using diff_mono[OF \<open>x\<in>nat\<close> _ \<open>m\<in>nat\<close>] by simp
    have "m#+n#-m =  n" using diff_cancel2 \<open>m\<in>nat\<close> \<open>n\<in>nat\<close> by simp   
    with \<open>x#-m<m#+n#-m\<close> \<open>x\<in>nat\<close>
    have "x#-m \<in> n" "x=x#-m#+m" 
      using ltD add_diff_inverse2[OF \<open>m\<le>x\<close>] by simp_all
    then 
    show "x\<in>weak(n,m)" 
      unfolding weak_def by auto
  qed
  ultimately
  show ?thesis by auto
qed

lemma weak_zero:
  shows "weak(0,n) = 0"
  unfolding weak_def by simp

lemma weakening_diff :
  assumes "n \<in> nat"
  shows "weak(n,7) - weak(n,5) \<subseteq> {5#+n, 6#+n}"
  unfolding weak_def using assms
proof(auto)
  {
    fix i
    assume "i\<in>n" "succ(succ(natify(i)))\<noteq>n" "\<forall>w\<in>n. succ(succ(natify(i))) \<noteq> natify(w)"
    then 
    have "i<n" 
      using ltI \<open>n\<in>nat\<close> by simp
    from \<open>n\<in>nat\<close> \<open>i\<in>n\<close> \<open>succ(succ(natify(i)))\<noteq>n\<close>
    have "i\<in>nat" "succ(succ(i))\<noteq>n" using in_n_in_nat by simp_all
    from \<open>i<n\<close>
    have "succ(i)\<le>n" using succ_leI by simp
    with \<open>n\<in>nat\<close>
    consider (a) "succ(i) = n" | (b) "succ(i) < n"
      using leD by auto
    then have "succ(i) = n" 
    proof cases
      case a
      then show ?thesis .
    next
      case b
      then 
      have "succ(succ(i))\<le>n" using succ_leI by simp
      with \<open>n\<in>nat\<close>
      consider (a) "succ(succ(i)) = n" | (b) "succ(succ(i)) < n"
        using leD by auto
      then have "succ(i) = n" 
      proof cases
        case a
        with \<open>succ(succ(i))\<noteq>n\<close> show ?thesis by blast
      next
        case b
        then 
        have "succ(succ(i))\<in>n" using ltD by simp
        with \<open>i\<in>nat\<close>
        have "succ(succ(natify(i))) \<noteq> natify(succ(succ(i)))"
          using  \<open>\<forall>w\<in>n. succ(succ(natify(i))) \<noteq> natify(w)\<close> by auto
        then 
        have "False" using \<open>i\<in>nat\<close> by auto
        then show ?thesis by blast
      qed
      then show ?thesis .
    qed
    with \<open>i\<in>nat\<close> have "succ(natify(i)) = n" by simp
  }
  then 
  show "n \<in> nat \<Longrightarrow> 
    succ(succ(natify(y))) \<noteq> n \<Longrightarrow> 
    \<forall>x\<in>n. succ(succ(natify(y))) \<noteq> natify(x) \<Longrightarrow>
    y \<in> n \<Longrightarrow> succ(natify(y)) = n" for y
    by blast
qed

lemma in_add_del :
  assumes "x\<in>j#+n" "n\<in>nat" "j\<in>nat"
  shows "x < j \<or> x \<in> weak(n,j)" 
proof (cases "x<j")
  case True
  then show ?thesis ..
next
  case False
  have "x\<in>nat" "j#+n\<in>nat"
    using in_n_in_nat[OF _ \<open>x\<in>j#+n\<close>] assms by simp_all
  then
  have "j \<le> x" "x < j#+n" 
    using not_lt_iff_le False \<open>j\<in>nat\<close> \<open>n\<in>nat\<close> ltI[OF \<open>x\<in>j#+n\<close>] by auto
  then 
  have "x#-j < (j #+ n) #- j" "x = j #+ (x #-j)"
    using diff_mono \<open>x\<in>nat\<close> \<open>j#+n\<in>nat\<close> \<open>j\<in>nat\<close> \<open>n\<in>nat\<close> 
      add_diff_inverse[OF \<open>j\<le>x\<close>] by simp_all
  then 
  have "x#-j < n" "x = (x #-j ) #+ j"
    using diff_add_inverse \<open>n\<in>nat\<close> add_commute by simp_all
  then 
  have "x#-j \<in>n" using ltD by simp
  then 
  have "x \<in> weak(n,j)" 
    unfolding weak_def
    using \<open>x= (x#-j) #+j\<close> RepFunI[OF \<open>x#-j\<in>n\<close>] add_commute by force
  then show ?thesis  ..
qed


lemma sep_env_action:
  assumes
    "[t,p,u,P,leq,o,pi] \<in> list(M)"
    "env \<in> list(M)"
  shows "\<forall> i . i \<in> weak(length(env),5) \<longrightarrow> 
      nth(sep_env(length(env))`i,[t,p,u,P,leq,o,pi]@env) = nth(i,[p,P,leq,o,t] @ env @ [pi,u])"
proof -
  from assms
  have A: "5#+length(env)\<in>nat" "[p, P, leq, o, t] \<in>list(M)"
    by simp_all
  let ?f="sep_env(length(env))"
  have EQ: "weak(length(env),5) = 5#+length(env) - 5"
    using weak_equal length_type[OF \<open>env\<in>list(M)\<close>] by simp
  let ?tgt="[t,p,u,P,leq,o,pi]@env"
  let ?src="[p,P,leq,o,t] @ env @ [pi,u]"
  have "nth(?f`i,[t,p,u,P,leq,o,pi]@env) = nth(i,[p,P,leq,o,t] @ env @ [pi,u])" 
    if "i \<in> (5#+length(env)-5)" for i 
  proof -
    from that 
    have 2: "i \<in> 5#+length(env)"  "i \<notin> 5" "i \<in> nat" "i#-5\<in>nat" "i#+2\<in>nat"
      using in_n_in_nat[OF \<open>5#+length(env)\<in>nat\<close>] by simp_all
    then 
    have 3: "\<not> i < 5" using ltD by force
    then
    have "5 \<le> i" "2 \<le> 5" 
      using  not_lt_iff_le \<open>i\<in>nat\<close> by simp_all
    then have "2 \<le> i" using le_trans[OF \<open>2\<le>5\<close>] by simp
    from A \<open>i \<in> 5#+length(env)\<close> 
    have "i < 5#+length(env)" using ltI by simp
    with \<open>i\<in>nat\<close> \<open>2\<le>i\<close> A
    have C:"i#+2 < 7#+length(env)"  by simp
    with that 
    have B: "?f`i = i#+2" unfolding sep_env_def by simp
    from 3 assms(1) \<open>i\<in>nat\<close>
    have "\<not> i#+2 < 7" using not_lt_iff_le add_le_mono by simp
    from \<open>i < 5#+length(env)\<close> 3 \<open>i\<in>nat\<close>
    have "i#-5 < 5#+length(env) #- 5" 
      using diff_mono[of i "5#+length(env)" 5,OF _ _ _ \<open>i < 5#+length(env)\<close>] 
        not_lt_iff_le[THEN iffD1] by force
    with assms(2)
    have "i#-5 < length(env)" using diff_add_inverse length_type by simp
    have "nth(i,?src) =nth(i#-5,env@[pi,u])"
      using nth_append[OF A(2) \<open>i\<in>nat\<close>] 3 by simp
    also 
    have "... = nth(i#-5, env)" 
      using nth_append[OF \<open>env \<in>list(M)\<close> \<open>i#-5\<in>nat\<close>] \<open>i#-5 < length(env)\<close> by simp
    also 
    have "... = nth(i#+2, ?tgt)"
      using nth_append[OF assms(1) \<open>i#+2\<in>nat\<close>] \<open>\<not> i#+2 <7\<close> by simp
    ultimately 
    have "nth(i,?src) = nth(?f`i,?tgt)"
      using B by simp 
    then show ?thesis using that by simp
  qed
  then show ?thesis using EQ by force
qed

lemma sep_env_type :
  assumes "n \<in> nat"
  shows "sep_env(n) : (5#+n)-5 \<rightarrow> (7#+n)-7"
proof -
  let ?h="sep_env(n)"
  from \<open>n\<in>nat\<close> 
  have "(5#+n)#+2 = 7#+n" "7#+n\<in>nat" "5#+n\<in>nat" by simp_all
  have
    D: "sep_env(n)`x \<in> (7#+n)-7" if "x \<in> (5#+n)-5" for x
  proof -
    from \<open>x\<in>5#+n-5\<close>
    have "?h`x = x#+2" "x<5#+n" "x\<in>nat"
      unfolding sep_env_def using ltI in_n_in_nat[OF \<open>5#+n\<in>nat\<close>] by simp_all
    then 
    have "x#+2 < 7#+n" by simp
    then 
    have "x#+2 \<in> 7#+n" using ltD by simp
    from \<open>x\<in>5#+n-5\<close>
    have "x\<notin>5" by simp 
    then have "\<not>x<5" using ltD by blast
    then have "5\<le>x" using not_lt_iff_le \<open>x\<in>nat\<close> by simp
    then have "7\<le>x#+2" using add_le_mono \<open>x\<in>nat\<close> by simp
    then have "\<not>x#+2<7" using not_lt_iff_le \<open>x\<in>nat\<close> by simp
    then have "x#+2 \<notin> 7" using ltI \<open>x\<in>nat\<close> by force
    with \<open>x#+2 \<in> 7#+n\<close> show ?thesis using  \<open>?h`x = x#+2\<close> DiffI by simp
  qed
  then show ?thesis unfolding sep_env_def using lam_type by simp
qed

lemma sep_var_fin_type :
  assumes "n \<in> nat"
  shows "sep_var(n) : 7#+n  -||> 7#+n"
  unfolding sep_var_def 
  using consI ltD emptyI by force

lemma sep_var_domain :
  assumes "n \<in> nat"
  shows "domain(sep_var(n)) =  7#+n - weak(n,5)"
proof - 
  let ?A="weak(n,5)"
  have A:"domain(sep_var(n)) \<subseteq> (7#+n)" 
    unfolding sep_var_def 
    by(auto simp add: le_natE)
  have C: "x=5#+n \<or> x=6#+n \<or> x \<le> 4" if "x\<in>domain(sep_var(n))" for x
    using that unfolding sep_var_def by auto
  have D : "x<n#+7" if "x\<in>7#+n" for x
    using that \<open>n\<in>nat\<close> ltI by simp
  have "\<not> 5#+n < 5#+n" using \<open>n\<in>nat\<close>  lt_irrefl[of _ False] by force
  have "\<not> 6#+n < 5#+n" using \<open>n\<in>nat\<close> by force
  have R: "x < 5#+n" if "x\<in>?A" for x
  proof -
    from that
    obtain i where
      "i<n" "x=5#+i" 
      unfolding weak_def
      using ltI \<open>n\<in>nat\<close> RepFun_iff by force
    with \<open>n\<in>nat\<close>
    have "5#+i < 5#+n" using add_lt_mono2 by simp
    with \<open>x=5#+i\<close> 
    show "x < 5#+n" by simp
  qed
  then 
  have 1:"x\<notin>?A" if "\<not>x <5#+n" for x using that by blast
  have "5#+n \<notin> ?A" "6#+n\<notin>?A"
  proof -
    show "5#+n \<notin> ?A" using 1 \<open>\<not>5#+n<5#+n\<close> by blast    
    with 1 show "6#+n \<notin> ?A" using  \<open>\<not>6#+n<5#+n\<close> by blast
  qed
  then 
  have E:"x\<notin>?A" if "x\<in>domain(sep_var(n))" for x 
    unfolding weak_def
    using C that by force
  then 
  have F: "domain(sep_var(n)) \<subseteq> 7#+n - ?A" using A by auto
  from assms
  have "x<7 \<or> x\<in>weak(n,7)" if "x\<in>7#+n" for x
    using in_add_del[OF \<open>x\<in>7#+n\<close>] by simp
  moreover
  {
    fix x
    assume asm:"x\<in>7#+n"  "x\<notin>?A"  "x\<in>weak(n,7)"
    then 
    have "x\<in>domain(sep_var(n))" 
    proof -
      from \<open>n\<in>nat\<close>
      have "weak(n,7)-weak(n,5)\<subseteq>{n#+5,n#+6}" 
        using weakening_diff by simp
      with  \<open>x\<notin>?A\<close> asm
      have "x\<in>{n#+5,n#+6}" using  subsetD DiffI by blast
      then 
      show ?thesis unfolding sep_var_def by simp
    qed
  }
  moreover
  {
    fix x
    assume asm:"x\<in>7#+n"  "x\<notin>?A" "x<7"
    then have "x\<in>domain(sep_var(n))"
    proof (cases "2 \<le> n")
      case True
      moreover
      have "0<n" using  leD[OF \<open>n\<in>nat\<close> \<open>2\<le>n\<close>] lt_imp_0_lt by auto
      ultimately
      have "x<5"
        using \<open>x<7\<close> \<open>x\<notin>?A\<close> \<open>n\<in>nat\<close> in_n_in_nat
        unfolding weak_def
        by (clarsimp simp add:not_lt_iff_le, auto simp add:lt_def)
      then
      show ?thesis unfolding sep_var_def 
        by (clarsimp simp add:not_lt_iff_le, auto simp add:lt_def)
    next
      case False 
      then 
      show ?thesis 
      proof (cases "n=0")
        case True
        then show ?thesis 
          unfolding sep_var_def using ltD asm \<open>n\<in>nat\<close> by auto
      next
        case False
        then 
        have "n < 2" using  \<open>n\<in>nat\<close> not_lt_iff_le \<open>\<not> 2 \<le> n\<close>  by force
        then 
        have "\<not> n <1" using \<open>n\<noteq>0\<close> by simp
        then 
        have "n=1" using not_lt_iff_le \<open>n<2\<close> le_iff by auto
        then show ?thesis 
          using \<open>x\<notin>?A\<close> 
          unfolding weak_def sep_var_def 
          using ltD asm \<open>n\<in>nat\<close> by force
      qed
    qed
  }
  ultimately
  have "w\<in>domain(sep_var(n))" if "w\<in> 7#+n - ?A" for w
    using that by blast
  then
  have "7#+n - ?A \<subseteq> domain(sep_var(n))" by blast
  with F 
  show ?thesis by auto
qed

lemma sep_var_type :
  assumes "n \<in> nat"
  shows "sep_var(n) : (7#+n)-weak(n,5) \<rightarrow> 7#+n"
  using FiniteFun_is_fun[OF sep_var_fin_type[OF \<open>n\<in>nat\<close>]]
    sep_var_domain[OF \<open>n\<in>nat\<close>] by simp

lemma sep_var_action :
  assumes 
    "[t,p,u,P,leq,o,pi] \<in> list(M)"
    "env \<in> list(M)"
  shows "\<forall> i . i \<in> (7#+length(env)) - weak(length(env),5) \<longrightarrow> 
    nth(sep_var(length(env))`i,[t,p,u,P,leq,o,pi]@env) = nth(i,[p,P,leq,o,t] @ env @ [pi,u])"
  using assms
proof (subst sep_var_domain[OF length_type[OF \<open>env\<in>list(M)\<close>],symmetric],auto)
  fix i y
  assume "\<langle>i, y\<rangle> \<in> sep_var(length(env))"
  with assms
  show "nth(sep_var(length(env)) ` i,
               Cons(t, Cons(p, Cons(u, Cons(P, Cons(leq, Cons(o, Cons(pi, env)))))))) =
           nth(i, Cons(p, Cons(P, Cons(leq, Cons(o, Cons(t, env @ [pi, u]))))))"  
    using apply_fun[OF sep_var_type] assms
      unfolding sep_var_def
      using nth_concat2[OF \<open>env\<in>list(M)\<close>]  nth_concat3[OF \<open>env\<in>list(M)\<close>,symmetric]
      by force
  qed

definition
  rensep :: "i \<Rightarrow> i" where
  "rensep(n) \<equiv> union_fun(sep_var(n),sep_env(n),7#+n-weak(n,5),weak(n,5))"

lemma rensep_aux :
  assumes "n\<in>nat"
  shows "(7#+n-weak(n,5)) \<union> weak(n,5) = 7#+n" "7#+n \<union> ( 7 #+ n - 7) = 7#+n"
proof -
  from \<open>n\<in>nat\<close>
  have "weak(n,5) = n#+5-5"
    using weak_equal by simp
  with  \<open>n\<in>nat\<close>
  show "(7#+n-weak(n,5)) \<union> weak(n,5) = 7#+n" "7#+n \<union> ( 7 #+ n - 7) = 7#+n"
    using Diff_partition le_imp_subset by auto
qed

lemma rensep_type :
  assumes "n\<in>nat"
  shows "rensep(n) \<in> 7#+n \<rightarrow> 7#+n"
proof -
  from \<open>n\<in>nat\<close>
  have "rensep(n) \<in> (7#+n-weak(n,5)) \<union> weak(n,5) \<rightarrow> 7#+n \<union> (7#+n - 7)"
    unfolding rensep_def 
    using union_fun_type  sep_var_type \<open>n\<in>nat\<close> sep_env_type weak_equal
    by force
  then
  show ?thesis using rensep_aux \<open>n\<in>nat\<close> by auto 
qed

lemma rensep_action :
  assumes "[t,p,u,P,leq,o,pi] @ env \<in> list(M)"
  shows "\<forall> i . i < 7#+length(env) \<longrightarrow> nth(rensep(length(env))`i,[t,p,u,P,leq,o,pi]@env) = nth(i,[p,P,leq,o,t] @ env @ [pi,u])"
proof - 
  let ?tgt="[t,p,u,P,leq,o,pi]@env"
  let ?src="[p,P,leq,o,t] @ env @ [pi,u]"
  let ?m="7 #+ length(env) - weak(length(env),5)"
  let ?p="weak(length(env),5)"
  let ?f="sep_var(length(env))"
  let ?g="sep_env(length(env))"
  let ?n="length(env)"
  from assms
  have 1 : "[t,p,u,P,leq,o,pi] \<in> list(M)" " env \<in> list(M)"
    "?src \<in> list(M)" "?tgt \<in> list(M)"  
    "7#+?n = (7#+?n-weak(?n,5)) \<union> weak(?n,5)"
    " length(?src) = (7#+?n-weak(?n,5)) \<union> weak(?n,5)"
    using Diff_partition le_imp_subset rensep_aux by auto
  then
  have "nth(i, ?src) = nth(union_fun(?f, ?g, ?m, ?p) ` i, ?tgt)" if "i < 7#+length(env)" for i
  proof -
    from \<open>i<7#+?n\<close>
    have "i \<in> (7#+?n-weak(?n,5)) \<union> weak(?n,5)" 
      using ltD by simp 
    then show ?thesis
      unfolding rensep_def using  
        union_fun_action[OF \<open>?src\<in>list(M)\<close> \<open>?tgt\<in>list(M)\<close> \<open>length(?src) = (7#+?n-weak(?n,5)) \<union> weak(?n,5)\<close>
          sep_var_action[OF \<open>[t,p,u,P,leq,o,pi] \<in> list(M)\<close> \<open>env\<in>list(M)\<close>]      
          sep_env_action[OF \<open>[t,p,u,P,leq,o,pi] \<in> list(M)\<close> \<open>env\<in>list(M)\<close>]
          ] that 
      by simp
  qed
  then show ?thesis unfolding rensep_def by simp
qed

definition sep_ren :: "[i,i] \<Rightarrow> i" where
  "sep_ren(n,\<phi>) \<equiv> ren(\<phi>)`(7#+n)`(7#+n)`rensep(n)"

lemma arity_rensep: assumes "\<phi>\<in>formula" "env \<in> list(M)"
  "arity(\<phi>) \<le> 7#+length(env)"
shows "arity(sep_ren(length(env),\<phi>)) \<le> 7#+length(env)"
  unfolding sep_ren_def
  using arity_ren rensep_type assms
  by simp

lemma type_rensep [TC]: 
  assumes "\<phi>\<in>formula" "env\<in>list(M)" 
  shows "sep_ren(length(env),\<phi>) \<in> formula"
  unfolding sep_ren_def
  using ren_tc rensep_type assms
  by simp

lemma sepren_action: 
  assumes "arity(\<phi>) \<le> 7 #+ length(env)"
    "[t,p,u,P,leq,o,pi] \<in> list(M)"
    "env\<in>list(M)"
    "\<phi>\<in>formula"
  shows "sats(M, sep_ren(length(env),\<phi>),[t,p,u,P,leq,o,pi] @ env) \<longleftrightarrow> sats(M, \<phi>,[p,P,leq,o,t] @ env @ [pi,u])"
proof -
  from assms
  have 1: " [t, p, u, P, leq, o, pi] @ env \<in> list(M)" 
    "[P,leq,o,p,t] \<in> list(M)"
    "[pi,u] \<in> list(M)"    
    by simp_all
  then 
  have 2: "[p,P,leq,o,t] @ env @ [pi,u] \<in> list(M)" using app_type by simp
  show ?thesis 
    unfolding sep_ren_def
    using sats_iff_sats_ren[OF \<open>\<phi>\<in>formula\<close>       
        add_type[of 7 "length(env)"]
        add_type[of 7 "length(env)"]
        2 1(1) 
        rensep_type[OF length_type[OF \<open>env\<in>list(M)\<close>]] 
        \<open>arity(\<phi>) \<le> 7 #+ length(env)\<close>]
      rensep_action[OF 1(1),rule_format,symmetric]
    by simp
qed

end