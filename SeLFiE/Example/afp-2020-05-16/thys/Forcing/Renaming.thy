section\<open>Renaming of variables in internalized formulas\<close>

theory Renaming
  imports
    Nat_Miscellanea
    "ZF-Constructible.Formula"
begin

lemma app_nm :
  assumes "n\<in>nat" "m\<in>nat" "f\<in>n\<rightarrow>m" "x \<in> nat"
  shows "f`x \<in> nat"
proof(cases "x\<in>n")
  case True
  then show ?thesis using assms in_n_in_nat apply_type by simp
next
  case False
  then show ?thesis using assms apply_0 domain_of_fun by simp
qed

subsection\<open>Renaming of free variables\<close>

definition
  union_fun :: "[i,i,i,i] \<Rightarrow> i" where
  "union_fun(f,g,m,p) \<equiv> \<lambda>j \<in> m \<union> p  . if j\<in>m then f`j else g`j"

lemma union_fun_type:
  assumes "f \<in> m \<rightarrow> n"
    "g \<in> p \<rightarrow> q"
  shows "union_fun(f,g,m,p) \<in> m \<union> p \<rightarrow> n \<union> q"
proof -
  let ?h="union_fun(f,g,m,p)"
  have
    D: "?h`x \<in> n \<union> q" if "x \<in> m \<union> p" for x
  proof (cases "x \<in> m")
    case True
    then have
      "x \<in> m \<union> p" by simp
    with \<open>x\<in>m\<close>
    have "?h`x = f`x"
      unfolding union_fun_def  beta by simp
    with \<open>f \<in> m \<rightarrow> n\<close> \<open>x\<in>m\<close>
    have "?h`x \<in> n" by simp
    then show ?thesis ..
  next
    case False
    with \<open>x \<in> m \<union> p\<close>
    have "x \<in> p"
      by auto
    with \<open>x\<notin>m\<close>
    have "?h`x = g`x"
      unfolding union_fun_def using beta by simp
    with \<open>g \<in> p \<rightarrow> q\<close> \<open>x\<in>p\<close>
    have "?h`x \<in> q" by simp
    then show ?thesis ..
  qed
  have A:"function(?h)" unfolding union_fun_def using function_lam by simp
  have " x\<in> (m \<union> p) \<times> (n \<union> q)" if "x\<in> ?h" for x
    using that lamE[of x "m \<union> p" _ "x \<in> (m \<union> p) \<times> (n \<union> q)"] D unfolding union_fun_def
    by auto
  then have B:"?h \<subseteq> (m \<union> p) \<times> (n \<union> q)" ..
  have "m \<union> p \<subseteq> domain(?h)"
    unfolding union_fun_def using domain_lam by simp
  with A B
  show ?thesis using  Pi_iff [THEN iffD2] by simp
qed

lemma union_fun_action :
  assumes
    "env \<in> list(M)"
    "env' \<in> list(M)"
    "length(env) = m \<union> p"
    "\<forall> i . i \<in> m \<longrightarrow>  nth(f`i,env') = nth(i,env)"
    "\<forall> j . j \<in> p \<longrightarrow> nth(g`j,env') = nth(j,env)"
  shows "\<forall> i . i \<in> m \<union> p \<longrightarrow>
          nth(i,env) = nth(union_fun(f,g,m,p)`i,env')"
proof -
  let ?h = "union_fun(f,g,m,p)"
  have "nth(x, env) = nth(?h`x,env')" if "x \<in> m \<union> p" for x
    using that
  proof (cases "x\<in>m")
    case True
    with \<open>x\<in>m\<close>
    have "?h`x = f`x"
      unfolding union_fun_def  beta by simp
    with assms \<open>x\<in>m\<close>
    have "nth(x,env) = nth(?h`x,env')" by simp
    then show ?thesis .
  next
    case False
    with \<open>x \<in> m \<union> p\<close>
    have
      "x \<in> p" "x\<notin>m"  by auto
    then
    have "?h`x = g`x"
      unfolding union_fun_def beta by simp
    with assms \<open>x\<in>p\<close>
    have "nth(x,env) = nth(?h`x,env')" by simp
    then show ?thesis .
  qed
  then show ?thesis by simp
qed


lemma id_fn_type :
  assumes "n \<in> nat"
  shows "id(n) \<in> n \<rightarrow> n"
  unfolding id_def using \<open>n\<in>nat\<close> by simp

lemma id_fn_action:
  assumes "n \<in> nat" "env\<in>list(M)"
  shows "\<And> j . j < n \<Longrightarrow> nth(j,env) = nth(id(n)`j,env)"
proof -
  show "nth(j,env) = nth(id(n)`j,env)" if "j < n" for j using that \<open>n\<in>nat\<close> ltD by simp
qed


definition
  sum :: "[i,i,i,i,i] \<Rightarrow> i" where
  "sum(f,g,m,n,p) \<equiv> \<lambda>j \<in> m#+p  . if j<m then f`j else (g`(j#-m))#+n"

lemma sum_inl:
  assumes "m \<in> nat" "n\<in>nat"
    "f \<in> m\<rightarrow>n" "x \<in> m"
  shows "sum(f,g,m,n,p)`x = f`x"
proof -
  from \<open>m\<in>nat\<close>
  have "m\<le>m#+p"
    using add_le_self[of m] by simp
  with assms
  have "x\<in>m#+p"
    using ltI[of x m] lt_trans2[of x m "m#+p"] ltD by simp
  from assms
  have "x<m"
    using ltI by simp
  with \<open>x\<in>m#+p\<close>
  show ?thesis unfolding sum_def by simp
qed

lemma sum_inr:
  assumes "m \<in> nat" "n\<in>nat" "p\<in>nat"
    "g\<in>p\<rightarrow>q" "m \<le> x" "x < m#+p"
  shows "sum(f,g,m,n,p)`x = g`(x#-m)#+n"
proof -
  from assms
  have "x\<in>nat"
    using in_n_in_nat[of "m#+p"] ltD
    by simp
  with assms
  have "\<not> x<m"
    using not_lt_iff_le[THEN iffD2] by simp
  from assms
  have "x\<in>m#+p"
    using ltD by simp
  with \<open>\<not> x<m\<close>
  show ?thesis unfolding sum_def by simp
qed


lemma sum_action :
  assumes "m \<in> nat" "n\<in>nat" "p\<in>nat" "q\<in>nat"
    "f \<in> m\<rightarrow>n" "g\<in>p\<rightarrow>q"
    "env \<in> list(M)"
    "env' \<in> list(M)"
    "env1 \<in> list(M)"
    "env2 \<in> list(M)"
    "length(env) = m"
    "length(env1) = p"
    "length(env') = n"
    "\<And> i . i < m \<Longrightarrow> nth(i,env) = nth(f`i,env')"
    "\<And> j. j < p \<Longrightarrow> nth(j,env1) = nth(g`j,env2)"
  shows "\<forall> i . i < m#+p \<longrightarrow>
          nth(i,env@env1) = nth(sum(f,g,m,n,p)`i,env'@env2)"
proof -
  let ?h = "sum(f,g,m,n,p)"
  from \<open>m\<in>nat\<close> \<open>n\<in>nat\<close> \<open>q\<in>nat\<close>
  have "m\<le>m#+p" "n\<le>n#+q" "q\<le>n#+q"
    using add_le_self[of m]  add_le_self2[of n q] by simp_all
  from \<open>p\<in>nat\<close>
  have "p = (m#+p)#-m" using diff_add_inverse2 by simp
  have "nth(x, env @ env1) = nth(?h`x,env'@env2)" if "x<m#+p" for x
  proof (cases "x<m")
    case True
    then
    have 2: "?h`x= f`x" "x\<in>m" "f`x \<in> n" "x\<in>nat"
      using assms sum_inl ltD apply_type[of f m _ x] in_n_in_nat by simp_all
    with \<open>x<m\<close> assms
    have "f`x < n" "f`x<length(env')"  "f`x\<in>nat"
      using ltI in_n_in_nat by simp_all
    with 2 \<open>x<m\<close> assms
    have "nth(x,env@env1) = nth(x,env)"
      using nth_append[OF \<open>env\<in>list(M)\<close>] \<open>x\<in>nat\<close> by simp
    also
    have
      "... = nth(f`x,env')"
      using 2 \<open>x<m\<close> assms by simp
    also
    have "... = nth(f`x,env'@env2)"
      using nth_append[OF \<open>env'\<in>list(M)\<close>] \<open>f`x<length(env')\<close> \<open>f`x \<in>nat\<close> by simp
    also
    have "... = nth(?h`x,env'@env2)"
      using 2 by simp
    finally
    have "nth(x, env @ env1) = nth(?h`x,env'@env2)" .
    then show ?thesis .
  next
    case False
    have "x\<in>nat"
      using that in_n_in_nat[of "m#+p" x] ltD \<open>p\<in>nat\<close> \<open>m\<in>nat\<close> by simp
    with \<open>length(env) = m\<close>
    have "m\<le>x" "length(env) \<le> x"
      using not_lt_iff_le \<open>m\<in>nat\<close> \<open>\<not>x<m\<close> by simp_all
    with \<open>\<not>x<m\<close> \<open>length(env) = m\<close>
    have 2 : "?h`x= g`(x#-m)#+n"  "\<not> x <length(env)"
      unfolding sum_def
      using  sum_inr that beta ltD by simp_all
    from assms \<open>x\<in>nat\<close> \<open>p=m#+p#-m\<close>
    have "x#-m < p"
      using diff_mono[OF _ _ _ \<open>x<m#+p\<close> \<open>m\<le>x\<close>] by simp
    then have "x#-m\<in>p" using ltD by simp
    with \<open>g\<in>p\<rightarrow>q\<close>
    have "g`(x#-m) \<in> q"  by simp
    with \<open>q\<in>nat\<close> \<open>length(env') = n\<close>
    have "g`(x#-m) < q" "g`(x#-m)\<in>nat" using ltI in_n_in_nat by simp_all
    with \<open>q\<in>nat\<close> \<open>n\<in>nat\<close>
    have "(g`(x#-m))#+n <n#+q" "n \<le> g`(x#-m)#+n" "\<not> g`(x#-m)#+n < length(env')"
      using add_lt_mono1[of "g`(x#-m)" _ n,OF _ \<open>q\<in>nat\<close>]
        add_le_self2[of n] \<open>length(env') = n\<close>
      by simp_all
    from assms \<open>\<not> x < length(env)\<close> \<open>length(env) = m\<close>
    have "nth(x,env @ env1) = nth(x#-m,env1)"
      using nth_append[OF \<open>env\<in>list(M)\<close> \<open>x\<in>nat\<close>] by simp
    also
    have "... = nth(g`(x#-m),env2)"
      using assms \<open>x#-m < p\<close> by simp
    also
    have "... = nth((g`(x#-m)#+n)#-length(env'),env2)"
      using  \<open>length(env') = n\<close>
        diff_add_inverse2 \<open>g`(x#-m)\<in>nat\<close>
      by simp
    also
    have "... = nth((g`(x#-m)#+n),env'@env2)"
      using  nth_append[OF \<open>env'\<in>list(M)\<close>] \<open>n\<in>nat\<close> \<open>\<not> g`(x#-m)#+n < length(env')\<close>
      by simp
    also
    have "... = nth(?h`x,env'@env2)"
      using 2 by simp
    finally
    have "nth(x, env @ env1) = nth(?h`x,env'@env2)" .
    then show ?thesis .
  qed
  then show ?thesis by simp
qed

lemma sum_type  :
  assumes "m \<in> nat" "n\<in>nat" "p\<in>nat" "q\<in>nat"
    "f \<in> m\<rightarrow>n" "g\<in>p\<rightarrow>q"
  shows "sum(f,g,m,n,p) \<in> (m#+p) \<rightarrow> (n#+q)"
proof -
  let ?h = "sum(f,g,m,n,p)"
  from \<open>m\<in>nat\<close> \<open>n\<in>nat\<close> \<open>q\<in>nat\<close>
  have "m\<le>m#+p" "n\<le>n#+q" "q\<le>n#+q"
    using add_le_self[of m]  add_le_self2[of n q] by simp_all
  from \<open>p\<in>nat\<close>
  have "p = (m#+p)#-m" using diff_add_inverse2 by simp
  {fix x
    assume 1: "x\<in>m#+p" "x<m"
    with 1 have "?h`x= f`x" "x\<in>m"
      using assms sum_inl ltD by simp_all
    with \<open>f\<in>m\<rightarrow>n\<close>
    have "?h`x \<in> n" by simp
    with \<open>n\<in>nat\<close> have "?h`x < n" using ltI by simp
    with \<open>n\<le>n#+q\<close>
    have "?h`x < n#+q" using lt_trans2 by simp
    then
    have "?h`x \<in> n#+q"  using ltD by simp
  }
  then have 1:"?h`x \<in> n#+q" if "x\<in>m#+p" "x<m" for x using that .
  {fix x
    assume 1: "x\<in>m#+p" "m\<le>x"
    then have "x<m#+p" "x\<in>nat" using ltI in_n_in_nat[of "m#+p"] ltD by simp_all
    with 1
    have 2 : "?h`x= g`(x#-m)#+n"
      using assms sum_inr ltD by simp_all
    from assms \<open>x\<in>nat\<close> \<open>p=m#+p#-m\<close>
    have "x#-m < p" using diff_mono[OF _ _ _ \<open>x<m#+p\<close> \<open>m\<le>x\<close>] by simp
    then have "x#-m\<in>p" using ltD by simp
    with \<open>g\<in>p\<rightarrow>q\<close>
    have "g`(x#-m) \<in> q"  by simp
    with \<open>q\<in>nat\<close> have "g`(x#-m) < q" using ltI by simp
    with \<open>q\<in>nat\<close>
    have "(g`(x#-m))#+n <n#+q" using add_lt_mono1[of "g`(x#-m)" _ n,OF _ \<open>q\<in>nat\<close>] by simp
    with 2
    have "?h`x \<in> n#+q"  using ltD by simp
  }
  then have 2:"?h`x \<in> n#+q" if "x\<in>m#+p" "m\<le>x" for x using that .
  have
    D: "?h`x \<in> n#+q" if "x\<in>m#+p" for x
    using that
  proof (cases "x<m")
    case True
    then show ?thesis using 1 that by simp
  next
    case False
    with \<open>m\<in>nat\<close> have "m\<le>x" using not_lt_iff_le that in_n_in_nat[of "m#+p"] by simp
    then show ?thesis using 2 that by simp
  qed
  have A:"function(?h)" unfolding sum_def using function_lam by simp
  have " x\<in> (m #+ p) \<times> (n #+ q)" if "x\<in> ?h" for x
    using that lamE[of x "m#+p" _ "x \<in> (m #+ p) \<times> (n #+ q)"] D unfolding sum_def
    by auto
  then have B:"?h \<subseteq> (m #+ p) \<times> (n #+ q)" ..
  have "m #+ p \<subseteq> domain(?h)"
    unfolding sum_def using domain_lam by simp
  with A B
  show ?thesis using  Pi_iff [THEN iffD2] by simp
qed

lemma sum_type_id :
  assumes
    "f \<in> length(env)\<rightarrow>length(env')"
    "env \<in> list(M)"
    "env' \<in> list(M)"
    "env1 \<in> list(M)"
  shows
    "sum(f,id(length(env1)),length(env),length(env'),length(env1)) \<in>
        (length(env)#+length(env1)) \<rightarrow> (length(env')#+length(env1))"
  using assms length_type id_fn_type sum_type
  by simp

lemma sum_type_id_aux2 :
  assumes
    "f \<in> m\<rightarrow>n"
    "m \<in> nat" "n \<in> nat"
    "env1 \<in> list(M)"
  shows
    "sum(f,id(length(env1)),m,n,length(env1)) \<in>
        (m#+length(env1)) \<rightarrow> (n#+length(env1))"
  using assms id_fn_type sum_type
  by auto

lemma sum_action_id :
  assumes
    "env \<in> list(M)"
    "env' \<in> list(M)"
    "f \<in> length(env)\<rightarrow>length(env')"
    "env1 \<in> list(M)"
    "\<And> i . i < length(env) \<Longrightarrow> nth(i,env) = nth(f`i,env')"
  shows "\<And> i . i < length(env)#+length(env1) \<Longrightarrow>
          nth(i,env@env1) = nth(sum(f,id(length(env1)),length(env),length(env'),length(env1))`i,env'@env1)"
proof -
  from assms
  have "length(env)\<in>nat" (is "?m \<in> _") by simp
  from assms have "length(env')\<in>nat" (is "?n \<in> _") by simp
  from assms have "length(env1)\<in>nat" (is "?p \<in> _") by simp
  note lenv = id_fn_action[OF \<open>?p\<in>nat\<close> \<open>env1\<in>list(M)\<close>]
  note lenv_ty = id_fn_type[OF \<open>?p\<in>nat\<close>]
  {
    fix i
    assume "i < length(env)#+length(env1)"
    have "nth(i,env@env1) = nth(sum(f,id(length(env1)),?m,?n,?p)`i,env'@env1)"
      using sum_action[OF \<open>?m\<in>nat\<close> \<open>?n\<in>nat\<close> \<open>?p\<in>nat\<close> \<open>?p\<in>nat\<close> \<open>f\<in>?m\<rightarrow>?n\<close>
          lenv_ty \<open>env\<in>list(M)\<close> \<open>env'\<in>list(M)\<close>
          \<open>env1\<in>list(M)\<close> \<open>env1\<in>list(M)\<close> _
          _ _  assms(5) lenv
          ] \<open>i<?m#+length(env1)\<close> by simp
  }
  then show "\<And> i . i < ?m#+length(env1) \<Longrightarrow>
          nth(i,env@env1) = nth(sum(f,id(?p),?m,?n,?p)`i,env'@env1)" by simp
qed

lemma sum_action_id_aux :
  assumes
    "f \<in> m\<rightarrow>n"
    "env \<in> list(M)"
    "env' \<in> list(M)"
    "env1 \<in> list(M)"
    "length(env) = m"
    "length(env') = n"
    "length(env1) = p"
    "\<And> i . i < m \<Longrightarrow> nth(i,env) = nth(f`i,env')"
  shows "\<And> i . i < m#+length(env1) \<Longrightarrow>
          nth(i,env@env1) = nth(sum(f,id(length(env1)),m,n,length(env1))`i,env'@env1)"
  using assms length_type id_fn_type sum_action_id
  by auto


definition
  sum_id :: "[i,i] \<Rightarrow> i" where
  "sum_id(m,f) \<equiv> sum(\<lambda>x\<in>1.x,f,1,1,m)"

lemma sum_id0 : "m\<in>nat\<Longrightarrow>sum_id(m,f)`0 = 0"
  by(unfold sum_id_def,subst sum_inl,auto)

lemma sum_idS : "p\<in>nat \<Longrightarrow> q\<in>nat \<Longrightarrow> f\<in>p\<rightarrow>q \<Longrightarrow> x \<in> p \<Longrightarrow> sum_id(p,f)`(succ(x)) = succ(f`x)"
  by(subgoal_tac "x\<in>nat",unfold sum_id_def,subst sum_inr,
      simp_all add:ltI,simp_all add: app_nm in_n_in_nat)

lemma sum_id_tc_aux :
  "p \<in> nat \<Longrightarrow>  q \<in> nat \<Longrightarrow> f \<in> p \<rightarrow> q \<Longrightarrow> sum_id(p,f) \<in> 1#+p \<rightarrow> 1#+q"
  by (unfold sum_id_def,rule sum_type,simp_all)

lemma sum_id_tc :
  "n \<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> f \<in> n \<rightarrow> m \<Longrightarrow> sum_id(n,f) \<in> succ(n) \<rightarrow> succ(m)"
  by(rule ssubst[of  "succ(n) \<rightarrow> succ(m)" "1#+n \<rightarrow> 1#+m"],
      simp,rule sum_id_tc_aux,simp_all)

subsection\<open>Renaming of formulas\<close>

consts   ren :: "i\<Rightarrow>i"
primrec
  "ren(Member(x,y)) =
      (\<lambda> n \<in> nat . \<lambda> m \<in> nat. \<lambda>f \<in> n \<rightarrow> m. Member (f`x, f`y))"

"ren(Equal(x,y)) =
      (\<lambda> n \<in> nat . \<lambda> m \<in> nat. \<lambda>f \<in> n \<rightarrow> m. Equal (f`x, f`y))"

"ren(Nand(p,q)) =
      (\<lambda> n \<in> nat . \<lambda> m \<in> nat. \<lambda>f \<in> n \<rightarrow> m. Nand (ren(p)`n`m`f, ren(q)`n`m`f))"

"ren(Forall(p)) =
      (\<lambda> n \<in> nat . \<lambda> m \<in> nat. \<lambda>f \<in> n \<rightarrow> m. Forall (ren(p)`succ(n)`succ(m)`sum_id(n,f)))"

lemma arity_meml : "l \<in> nat \<Longrightarrow> Member(x,y) \<in> formula \<Longrightarrow> arity(Member(x,y)) \<le> l \<Longrightarrow> x \<in> l"
  by(simp,rule subsetD,rule le_imp_subset,assumption,simp)
lemma arity_memr : "l \<in> nat \<Longrightarrow> Member(x,y) \<in> formula \<Longrightarrow> arity(Member(x,y)) \<le> l \<Longrightarrow> y \<in> l"
  by(simp,rule subsetD,rule le_imp_subset,assumption,simp)
lemma arity_eql : "l \<in> nat \<Longrightarrow> Equal(x,y) \<in> formula \<Longrightarrow> arity(Equal(x,y)) \<le> l \<Longrightarrow> x \<in> l"
  by(simp,rule subsetD,rule le_imp_subset,assumption,simp)
lemma arity_eqr : "l \<in> nat \<Longrightarrow> Equal(x,y) \<in> formula \<Longrightarrow> arity(Equal(x,y)) \<le> l \<Longrightarrow> y \<in> l"
  by(simp,rule subsetD,rule le_imp_subset,assumption,simp)
lemma  nand_ar1 : "p \<in> formula \<Longrightarrow> q\<in>formula \<Longrightarrow>arity(p) \<le> arity(Nand(p,q))"
  by (simp,rule Un_upper1_le,simp+)
lemma nand_ar2 : "p \<in> formula \<Longrightarrow> q\<in>formula \<Longrightarrow>arity(q) \<le> arity(Nand(p,q))"
  by (simp,rule Un_upper2_le,simp+)

lemma nand_ar1D : "p \<in> formula \<Longrightarrow> q\<in>formula \<Longrightarrow> arity(Nand(p,q)) \<le> n \<Longrightarrow> arity(p) \<le> n"
  by(auto simp add:  le_trans[OF Un_upper1_le[of "arity(p)" "arity(q)"]])
lemma nand_ar2D : "p \<in> formula \<Longrightarrow> q\<in>formula \<Longrightarrow> arity(Nand(p,q)) \<le> n \<Longrightarrow> arity(q) \<le> n"
  by(auto simp add:  le_trans[OF Un_upper2_le[of "arity(p)" "arity(q)"]])


lemma ren_tc : "p \<in> formula \<Longrightarrow>
  (\<And> n m f . n \<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> f \<in> n\<rightarrow>m \<Longrightarrow>  ren(p)`n`m`f \<in> formula)"
  by (induct set:formula,auto simp add: app_nm sum_id_tc)


lemma arity_ren :
  fixes "p"
  assumes "p \<in> formula"
  shows "\<And> n m f . n \<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> f \<in> n\<rightarrow>m \<Longrightarrow> arity(p) \<le> n \<Longrightarrow> arity(ren(p)`n`m`f)\<le>m"
  using assms
proof (induct set:formula)
  case (Member x y)
  then have "f`x \<in> m" "f`y \<in> m"
    using Member assms by (simp add: arity_meml apply_funtype,simp add:arity_memr apply_funtype)
  then show ?case using Member by (simp add: Un_least_lt ltI)
next
  case (Equal x y)
  then have "f`x \<in> m" "f`y \<in> m"
    using Equal assms by (simp add: arity_eql apply_funtype,simp add:arity_eqr apply_funtype)
  then show ?case using Equal by (simp add: Un_least_lt ltI)
next
  case (Nand p q)
  then have "arity(p)\<le>arity(Nand(p,q))"
    "arity(q)\<le>arity(Nand(p,q))"
    by (subst  nand_ar1,simp,simp,simp,subst nand_ar2,simp+)
  then have "arity(p)\<le>n"
    and "arity(q)\<le>n" using Nand
    by (rule_tac j="arity(Nand(p,q))" in le_trans,simp,simp)+
  then have "arity(ren(p)`n`m`f) \<le> m" and  "arity(ren(q)`n`m`f) \<le> m"
    using Nand by auto
  then show ?case using Nand by (simp add:Un_least_lt)
next
  case (Forall p)
  from Forall have "succ(n)\<in>nat"  "succ(m)\<in>nat" by auto
  from Forall have 2: "sum_id(n,f) \<in> succ(n)\<rightarrow>succ(m)" by (simp add:sum_id_tc)
  from Forall have 3:"arity(p) \<le> succ(n)" by (rule_tac n="arity(p)" in natE,simp+)
  then have "arity(ren(p)`succ(n)`succ(m)`sum_id(n,f))\<le>succ(m)" using
      Forall \<open>succ(n)\<in>nat\<close> \<open>succ(m)\<in>nat\<close> 2 by force
  then show ?case using Forall 2 3 ren_tc arity_type pred_le by auto
qed

lemma arity_forallE : "p \<in> formula \<Longrightarrow> m \<in> nat \<Longrightarrow> arity(Forall(p)) \<le> m \<Longrightarrow> arity(p) \<le> succ(m)"
  by(rule_tac n="arity(p)" in natE,erule arity_type,simp+)

lemma env_coincidence_sum_id :
  assumes "m \<in> nat" "n \<in> nat"
    "\<rho> \<in> list(A)" "\<rho>' \<in> list(A)"
    "f \<in> n \<rightarrow> m"
    "\<And> i . i < n \<Longrightarrow> nth(i,\<rho>) = nth(f`i,\<rho>')"
    "a \<in> A" "j \<in> succ(n)"
  shows "nth(j,Cons(a,\<rho>)) = nth(sum_id(n,f)`j,Cons(a,\<rho>'))"
proof -
  let ?g="sum_id(n,f)"
  have "succ(n) \<in> nat" using \<open>n\<in>nat\<close> by simp
  then have "j \<in> nat" using \<open>j\<in>succ(n)\<close> in_n_in_nat by blast
  then have "nth(j,Cons(a,\<rho>)) = nth(?g`j,Cons(a,\<rho>'))"
  proof (cases rule:natE[OF \<open>j\<in>nat\<close>])
    case 1
    then show ?thesis using assms sum_id0 by simp
  next
    case (2 i)
    with \<open>j\<in>succ(n)\<close> have "succ(i)\<in>succ(n)" by simp
    with \<open>n\<in>nat\<close> have "i \<in> n" using nat_succD assms by simp
    have "f`i\<in>m" using \<open>f\<in>n\<rightarrow>m\<close> apply_type \<open>i\<in>n\<close> by simp
    then have "f`i \<in> nat" using in_n_in_nat \<open>m\<in>nat\<close> by simp
    have "nth(succ(i),Cons(a,\<rho>)) = nth(i,\<rho>)" using \<open>i\<in>nat\<close> by simp
    also have "... = nth(f`i,\<rho>')" using assms \<open>i\<in>n\<close> ltI by simp
    also have "... = nth(succ(f`i),Cons(a,\<rho>'))" using \<open>f`i\<in>nat\<close> by simp
    also have "... = nth(?g`succ(i),Cons(a,\<rho>'))"
      using assms sum_idS[OF \<open>n\<in>nat\<close> \<open>m\<in>nat\<close>  \<open>f\<in>n\<rightarrow>m\<close> \<open>i \<in> n\<close>] cases by simp
    finally have "nth(succ(i),Cons(a,\<rho>)) = nth(?g`succ(i),Cons(a,\<rho>'))" .
    then show ?thesis using \<open>j=succ(i)\<close> by simp
  qed
  then show ?thesis .
qed

lemma sats_iff_sats_ren :
  fixes "\<phi>"
  assumes "\<phi> \<in> formula"
  shows  "\<lbrakk>  n \<in> nat ; m \<in> nat ; \<rho> \<in> list(M) ; \<rho>' \<in> list(M) ; f \<in> n \<rightarrow> m ;
            arity(\<phi>) \<le> n ;
            \<And> i . i < n \<Longrightarrow> nth(i,\<rho>) = nth(f`i,\<rho>') \<rbrakk> \<Longrightarrow>
         sats(M,\<phi>,\<rho>) \<longleftrightarrow> sats(M,ren(\<phi>)`n`m`f,\<rho>')"
  using \<open>\<phi> \<in> formula\<close>
proof(induct \<phi> arbitrary:n m \<rho> \<rho>' f)
  case (Member x y)
  have "ren(Member(x,y))`n`m`f = Member(f`x,f`y)" using Member assms arity_type by force
  moreover
  have "x \<in> n" using Member arity_meml by simp
  moreover 
  have "y \<in> n" using Member arity_memr by simp
  ultimately
  show ?case using Member ltI by simp
next
  case (Equal x y)
  have "ren(Equal(x,y))`n`m`f = Equal(f`x,f`y)" using Equal assms arity_type by force
  moreover
  have "x \<in> n" using Equal arity_eql by simp
  moreover
  have "y \<in> n" using Equal arity_eqr by simp
  ultimately show ?case using Equal ltI by simp
next
  case (Nand p q)
  have "ren(Nand(p,q))`n`m`f = Nand(ren(p)`n`m`f,ren(q)`n`m`f)" using Nand by simp
  moreover
  have "arity(p) \<le> n" using Nand nand_ar1D by simp
  moreover from this
  have "i \<in> arity(p) \<Longrightarrow> i \<in> n" for i using subsetD[OF le_imp_subset[OF \<open>arity(p) \<le> n\<close>]] by simp
  moreover from this
  have "i \<in> arity(p) \<Longrightarrow> nth(i,\<rho>) = nth(f`i,\<rho>')" for i using Nand ltI by simp
  moreover from this
  have "sats(M,p,\<rho>) \<longleftrightarrow> sats(M,ren(p)`n`m`f,\<rho>')" using \<open>arity(p)\<le>n\<close> Nand by simp
  have "arity(q) \<le> n" using Nand nand_ar2D by simp
  moreover from this
  have "i \<in> arity(q) \<Longrightarrow> i \<in> n" for i using subsetD[OF le_imp_subset[OF \<open>arity(q) \<le> n\<close>]] by simp
  moreover from this
  have "i \<in> arity(q) \<Longrightarrow> nth(i,\<rho>) = nth(f`i,\<rho>')" for i using Nand ltI by simp
  moreover from this
  have "sats(M,q,\<rho>) \<longleftrightarrow> sats(M,ren(q)`n`m`f,\<rho>')" using assms \<open>arity(q)\<le>n\<close> Nand by simp
  ultimately
  show ?case using Nand by simp
next
  case (Forall p)
  have 0:"ren(Forall(p))`n`m`f = Forall(ren(p)`succ(n)`succ(m)`sum_id(n,f))"
    using Forall by simp
  have 1:"sum_id(n,f) \<in> succ(n) \<rightarrow> succ(m)" (is "?g \<in> _") using sum_id_tc Forall by simp
  then have 2: "arity(p) \<le> succ(n)"
    using Forall le_trans[of _ "succ(pred(arity(p)))"] succpred_leI by simp
  have "succ(n)\<in>nat" "succ(m)\<in>nat" using Forall by auto
  then have A:"\<And> j .j < succ(n) \<Longrightarrow> nth(j, Cons(a, \<rho>)) = nth(?g`j, Cons(a, \<rho>'))" if "a\<in>M" for a
    using that env_coincidence_sum_id Forall ltD by force
  have
    "sats(M,p,Cons(a,\<rho>)) \<longleftrightarrow> sats(M,ren(p)`succ(n)`succ(m)`?g,Cons(a,\<rho>'))" if "a\<in>M" for a
  proof -
    have C:"Cons(a,\<rho>) \<in> list(M)" "Cons(a,\<rho>')\<in>list(M)" using Forall that by auto
    have "sats(M,p,Cons(a,\<rho>)) \<longleftrightarrow> sats(M,ren(p)`succ(n)`succ(m)`?g,Cons(a,\<rho>'))"
      using Forall(2)[OF \<open>succ(n)\<in>nat\<close> \<open>succ(m)\<in>nat\<close> C(1) C(2) 1 2 A[OF \<open>a\<in>M\<close>]] by simp
    then show ?thesis .
  qed
  then show ?case using Forall 0 1 2 by simp
qed

end
