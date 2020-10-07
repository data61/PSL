theory multisets_continued

(* N. Peltier - http://membres-lig.imag.fr/peltier/ *)

imports Main "HOL-Library.Multiset"

begin

subsection \<open>Multisets\<close>

text \<open>We use the Multiset theory provided in Isabelle. We prove some additional 
(mostly trivial) lemmata.\<close>

lemma mset_set_inclusion:
  assumes "finite E2"
  assumes "E1 \<subset> E2"  
  shows "mset_set E1 \<subset># (mset_set E2)"
proof (rule ccontr) 
  let ?s1 = "mset_set E1" 
  let ?s2 = "mset_set E2"
  assume "\<not> ?s1 \<subset># ?s2"
  from assms(1) and assms(2) have "finite E1" using finite_subset less_imp_le by auto 
  from \<open>\<not> ?s1 \<subset># ?s2\<close> obtain x where "(count ?s1 x > count ?s2 x)" using subseteq_mset_def [of ?s1 ?s2]
    by (metis assms(1) assms(2) finite_set_mset_mset_set finite_subset less_imp_le 
      less_le not_le_imp_less subset_mset.le_less) 
  from this have "count ?s1 x > 0" by linarith
  from this and \<open>finite E1\<close> have "count ?s1 x = 1" and "x \<in> E1" using subseteq_mset_def by auto
  from this and assms(2) have "x \<in> E2" by auto
  from this and \<open>finite E2\<close> have "count ?s2 x = 1" by auto
  from this and \<open>count ?s1 x = 1\<close> and \<open>(count ?s1 x > count ?s2 x)\<close> show False by auto
qed

lemma mset_ordering_addition:
  assumes "A = B + C"
  shows "B \<subseteq># A"
  using assms by simp

lemma equal_image_mset:
  assumes "\<forall>x \<in> E. (f x) = (g x)"
  shows "{# (f x). x \<in># (mset_set E) #} = {# (g x). x \<in># (mset_set E)  #}"
by (meson assms count_eq_zero_iff count_mset_set(3) image_mset_cong)

lemma multiset_order_inclusion:
  assumes "E \<subset># F"
  assumes "trans r"
  shows "(E,F) \<in> (mult r)"
proof -
  let ?G = "F-E"
  from assms(1) have "F = E +?G"
    by (simp add: subset_mset.add_diff_inverse subset_mset_def) 
  from this assms(1) have "?G \<noteq> {#}"
    by fastforce
  have "E = E + {#}" by auto
  from this \<open>F = E +?G\<close>  \<open>?G \<noteq> {#}\<close> assms(2) show ?thesis  using one_step_implies_mult [of ?G "{#}" r E] by auto
qed

lemma multiset_order_inclusion_eq:
  assumes "E \<subseteq># F"
  assumes "trans r"
  shows "E = F \<or> (E,F) \<in> (mult r)"
proof (cases)
  assume "E = F"
  then show ?thesis by auto
next
  assume "E \<noteq> F"
  from this and assms(1) have "E \<subset># F" by auto
  from this assms(2) and multiset_order_inclusion show ?thesis by auto
qed

lemma image_mset_ordering:
  assumes "M1 = {# (f1 u). u \<in># L #}"
  assumes "M2 = {# (f2 u). u \<in># L #}"
  assumes "\<forall>u. (u \<in># L \<longrightarrow> (((f1 u), (f2 u)) \<in> r \<or> (f1 u) = (f2 u)))"
  assumes "\<exists>u. (u \<in># L \<and> ((f1 u), (f2 u)) \<in> r)"
  assumes "irrefl r"
  shows "( (M1,M2) \<in> (mult r) )"
proof -
  let ?L' = "{# u \<in># L.  (f1 u) = (f2 u) #}"
  let ?L'' = "{# u \<in># L.  (f1 u) \<noteq> (f2 u) #}"
  have "L = ?L' + ?L''" by (simp) 
  from assms(3) have "\<forall>u. (u \<in># ?L'' \<longrightarrow> ((f1 u),(f2 u)) \<in> r)" by auto
  let ?M1' = "{# (f1 u). u \<in># ?L' #}"
  let ?M2' = "{# (f2 u). u \<in># ?L' #}"
  have "?M1' = ?M2'"
    by (metis (mono_tags, lifting) mem_Collect_eq multiset.map_cong0 set_mset_filter) 
  let ?M1'' = "{# (f1 u). u \<in># ?L'' #}"
  let ?M2'' = "{# (f2 u). u \<in># ?L'' #}"
  from \<open>L = ?L' + ?L''\<close> have "M1 = ?M1' + ?M1''" by (metis assms(1) image_mset_union) 
  from \<open>L = ?L' + ?L''\<close> have "M2 = ?M2' + ?M2''" by (metis assms(2) image_mset_union) 
  have dom: "(\<forall>k \<in> set_mset ?M1''. \<exists>j \<in> set_mset ?M2''. (k, j) \<in> r)"  
  proof 
    fix k assume "k \<in> set_mset ?M1''"
    from this obtain u where "k = (f1 u)" and "u \<in># ?L''" by auto
    from \<open>u \<in># ?L''\<close> have "(f2 u) \<in># ?M2''" by simp
    from \<open>\<forall>u. (u \<in># ?L'' \<longrightarrow> ((f1 u),(f2 u)) \<in> r)\<close> and \<open>u \<in># ?L''\<close> 
      have "((f1 u),(f2 u)) \<in> r" by auto
    from this and \<open>k = (f1 u)\<close> and \<open>(f2 u) \<in> set_mset ?M2''\<close>
      show "\<exists>j \<in> set_mset ?M2''. (k, j) \<in> r" by auto
  qed
  have "?L'' \<noteq> {#}" 
  proof -
    from assms(4) obtain u where "u \<in># L" and "( (f1 u),(f2 u) ) \<in> r" by auto
    from assms(5) \<open>( (f1 u),(f2 u) ) \<in> r\<close> have "( (f1 u) \<noteq> (f2 u) )"  
      unfolding irrefl_def by fastforce 
    from \<open>u \<in># L\<close> \<open>( (f1 u) \<noteq> (f2 u) )\<close> have "u \<in># ?L''" by auto
    from this show ?thesis by force 
  qed
  from this have  "?M2'' \<noteq> {#}" by auto
  from this and dom and \<open>M1 = ?M1' + ?M1''\<close> \<open>M2 = ?M2' + ?M2''\<close> \<open>?M1'=?M2'\<close> 
  show "(M1,M2) \<in> (mult r)" by (simp add: one_step_implies_mult)
qed

lemma image_mset_ordering_eq:
  assumes "M1 = {# (f1 u). u \<in># L #}"
  assumes "M2 = {# (f2 u). u \<in># L #}"
  assumes "\<forall>u. (u \<in># L \<longrightarrow> (((f1 u), (f2 u)) \<in> r \<or> (f1 u) = (f2 u)))"
  shows "(M1 = M2) \<or> ( (M1,M2) \<in> (mult r) )"
proof (cases)
  assume "M1 = M2" then show ?thesis by auto
  next assume "M1 \<noteq> M2"
  let ?L' = "{# u \<in># L.  (f1 u) = (f2 u) #}"
  let ?L'' = "{# u \<in># L.  (f1 u) \<noteq> (f2 u) #}"
  have "L = ?L' + ?L''" by (simp) 
  from assms(3) have "\<forall>u. (u \<in># ?L'' \<longrightarrow> ((f1 u),(f2 u)) \<in> r)" by auto
  let ?M1' = "{# (f1 u). u \<in># ?L' #}"
  let ?M2' = "{# (f2 u). u \<in># ?L' #}"
  have "?M1' = ?M2'"
    by (metis (mono_tags, lifting) mem_Collect_eq multiset.map_cong0 set_mset_filter)
  let ?M1'' = "{# (f1 u). u \<in># ?L'' #}"
  let ?M2'' = "{# (f2 u). u \<in># ?L'' #}"
  from \<open>L = ?L' + ?L''\<close> have "M1 = ?M1' + ?M1''" by (metis assms(1) image_mset_union) 
  from \<open>L = ?L' + ?L''\<close> have "M2 = ?M2' + ?M2''" by (metis assms(2) image_mset_union) 
  have dom: "(\<forall>k \<in> set_mset ?M1''. \<exists>j \<in> set_mset ?M2''. (k, j) \<in> r)"  
  proof 
    fix k assume "k \<in> set_mset ?M1''"
    from this obtain u where "k = (f1 u)" and "u \<in># ?L''" by auto
    from \<open>u \<in># ?L''\<close> have "(f2 u) \<in># ?M2''" by simp
    from \<open>\<forall>u. (u \<in># ?L'' \<longrightarrow> ((f1 u),(f2 u)) \<in> r)\<close> and \<open>u \<in># ?L''\<close> 
      have "((f1 u),(f2 u)) \<in> r" by auto
    from this and \<open>k = (f1 u)\<close> and \<open>(f2 u) \<in> set_mset ?M2''\<close>
      show "\<exists>j \<in> set_mset ?M2''. (k, j) \<in> r" by auto
  qed
  from \<open>M1 \<noteq> M2\<close> have  "?M2'' \<noteq> {#}"
    using \<open>M1 = image_mset f1 {# u \<in># L. f1 u = f2 u#} + image_mset f1 {# u \<in># L. f1 u \<noteq> f2 u#}\<close> \<open>M2 = image_mset f2 {# u \<in># L. f1 u = f2 u#} + image_mset f2 {# u \<in># L. f1 u \<noteq> f2 u#}\<close> \<open>image_mset f1 {# u \<in># L. f1 u = f2 u#} = image_mset f2 {# u \<in># L. f1 u = f2 u#}\<close> by auto 
  from this and dom and \<open>M1 = ?M1' + ?M1''\<close> \<open>M2 = ?M2' + ?M2''\<close> \<open>?M1'=?M2'\<close> 
  have "(M1,M2) \<in> (mult r)" by (simp add: one_step_implies_mult)
  from this show ?thesis by auto
qed

lemma mult1_def_lemma :
  assumes "M = M0 + {#a#} \<and> N = M0 + K \<and> (\<forall>b. b \<in># K \<longrightarrow> (b, a) \<in> r)"
  shows "(N,M) \<in> (mult1 r)"
proof -
  from assms(1) show ?thesis using mult1_def [of r] by auto
qed

lemma mset_ordering_add1:
  assumes "(E1,E2) \<in> (mult r)"
  shows "(E1,E2 + {# a #}) \<in> (mult r)"
proof -
  have i: "(E2,E2 + {# a #}) \<in> (mult1 r)" using mult1_def_lemma [of "E2 + {# a #}" E2 a E2 "{#}" r] 
    by auto
  have i: "(E2,E2 + {# a #}) \<in> (mult1 r)" using mult1_def_lemma [of "E2 + {# a #}" E2 a E2 "{#}" r] 
    by auto
  from assms(1) have "(E1,E2) \<in> (mult1 r)\<^sup>+" using mult_def by auto 
  from this and i have "(E1,E2 + {# a #}) \<in> (mult1 r)\<^sup>+" by auto
  then show ?thesis using mult_def by auto
qed

lemma mset_ordering_singleton:
  assumes "\<forall>x. (x \<in># E1 \<longrightarrow> (x,a) \<in> r)"
  shows "(E1, {# a #}) \<in> (mult r)"
proof -
  let ?K = "E1"
  let ?M0 = "{#}"
  have i: "E1 = ?M0 + ?K" by auto
  have ii: "{# a #} = ?M0 + {# a #}" by auto
  from assms(1) have iii: "\<forall>x. (x \<in># ?K \<longrightarrow> (x,a) \<in> r)" by auto
  from i and ii and iii show ?thesis using mult1_def_lemma [of "{# a #}"  ?M0 a E1 ?K r] mult_def by auto 
qed


lemma monotonic_fun_mult1:
  assumes "\<And> t s. ((t,s) \<in> r \<Longrightarrow> ((f t), (f s)) \<in> r)"
  assumes "(E1,E2) \<in> (mult1 r)"
  shows "({# (f x). x \<in># E1 #},{# (f x). x \<in># E2 #}) \<in>  (mult1 r)"
proof -
  let ?E1 = "{# (f x). x \<in># E1 #}"
  let ?E2 = "{# (f x). x \<in># E2 #}"
  from assms(2) obtain M0 a K where "E2 = M0 + {#a#}" and "E1 = M0 + K" and "(\<forall>b. b \<in># K \<longrightarrow> (b, a) \<in> r)" 
    unfolding mult1_def [of r]  by auto
  let ?K = "{# (f x). x \<in># K #}"
  let ?M0 = "{# (f x). x \<in># M0 #}"
  from \<open>E2 = M0 + {#a#}\<close> have "?E2 = ?M0 + {# (f a) #}" by simp 
  from \<open>E1 = M0 + K\<close> have "?E1 = ?M0 + ?K" by simp 
  have "(\<forall>b. b \<in># ?K \<longrightarrow> (b, (f a)) \<in> r)"
  proof ((rule allI),(rule impI))
    fix b assume "b  \<in># ?K"
    from \<open>b  \<in># ?K\<close> obtain b' where "b = (f b')" and "b' \<in># K"
      by (auto simp: insert_DiffM2 msed_map_invR union_single_eq_member)
    from \<open>b' \<in># K\<close> and \<open>(\<forall>b. b \<in># K \<longrightarrow> (b, a) \<in> r)\<close> have "(b',a) \<in> r" by auto
    from assms(1) and this and \<open>b = (f b')\<close> show "(b, (f a)) \<in> r" by auto
  qed
  from \<open>?E1 = ?M0 + ?K\<close> and \<open>?E2 = ?M0 + {# (f a) #}\<close> and \<open>(\<forall>b. b \<in># ?K \<longrightarrow> (b, (f a)) \<in> r)\<close> 
    show "(?E1,?E2) \<in>  (mult1 r)" by (metis mult1_def_lemma)
qed

lemma monotonic_fun_mult:
  assumes "\<And> t s. ((t,s) \<in> r \<Longrightarrow> ((f t), (f s)) \<in> r)"
  assumes "(E1,E2) \<in> (mult r)"
  shows "({# (f x). x \<in># E1 #},{# (f x). x \<in># E2 #}) \<in>  (mult r)"
proof -
  let ?E1 = "{# (f x). x \<in># E1 #}"
  let ?E2 = "{# (f x). x \<in># E2 #}"
  let ?P = "\<lambda>x. (?E1,{# (f y). y \<in># x #}) \<in> (mult r)"
  show ?thesis
  proof (rule trancl_induct [of E1 E2 "(mult1 r)" ?P])
    from assms(1) show "(E1, E2) \<in> (mult1 r)\<^sup>+" using assms(2) mult_def by blast
  next
    fix x assume "(E1, x) \<in> mult1 r" 
    have "(image_mset f E1, image_mset f x) \<in> mult1 r" 
      by (simp add: \<open>(E1, x) \<in> mult1 r\<close> assms(1) monotonic_fun_mult1) 
    from this show "(image_mset f E1, image_mset f x) \<in> mult r" by (simp add: mult_def) 
  next
    fix x z assume "(E1, x) \<in> (mult1 r)\<^sup>+"
      "(x, z) \<in> mult1 r" and "(image_mset f E1, image_mset f x) \<in> mult r"
    from \<open>(x, z) \<in> mult1 r\<close> have "(image_mset f x, image_mset f z) \<in> mult1 r"
      by (simp add: assms(1) monotonic_fun_mult1) 
    from this and \<open>(image_mset f E1, image_mset f x) \<in> mult r\<close> 
      show "(image_mset f E1, image_mset f z) \<in> mult r" 
      using mult_def trancl.trancl_into_trancl by fastforce  
  qed
qed

lemma mset_set_insert_eq:
  assumes "finite E"
  shows "mset_set (E \<union> { x }) \<subseteq># mset_set E + {# x #}"
proof (rule ccontr)
  assume "\<not> ?thesis"
  from this obtain y where "(count (mset_set (E \<union> { x })) y) 
    > (count (mset_set E + {# x #}) y)"
    by (meson leI subseteq_mset_def)
  from assms(1) have "finite (E \<union> { x })" by auto
  have "(count (mset_set E + {# x #}) y) = (count (mset_set E) y) + (count {# x #} y)" by auto
  have "x \<noteq> y"
  proof
    assume "x = y"
    then have "y \<in> E \<union> { x }" by auto
    from \<open>finite (E \<union> { x })\<close> this have "(count (mset_set (E \<union> { x })) y) = 1" 
      using count_mset_set(1) by auto
    from this and \<open>(count (mset_set (E \<union> { x })) y) > (count (mset_set E + {# x #}) y)\<close> have 
      "(count (mset_set E + {# x #}) y) = 0" by auto
    from \<open>(count (mset_set E + {# x #}) y) = 0\<close> have "count {# x #} y = 0" by auto
    from \<open>x = y\<close> have "count {# x #} y = 1" using count_mset_set by auto
    from this and \<open>count {# x #} y = 0\<close> show False by auto
  qed
  have "y \<notin> E"
  proof 
    assume "y \<in> E"
    then have "y \<in> E \<union> { x }" by auto
    from \<open>finite (E \<union> { x })\<close> this have "(count (mset_set (E \<union> { x })) y) = 1" 
      using count_mset_set(1) by auto
    from this and \<open>(count (mset_set (E \<union> { x })) y) > (count (mset_set E + {# x #}) y)\<close> have 
      "(count (mset_set E + {# x #}) y) = 0" by auto
    from \<open>(count (mset_set E + {# x #}) y) = 0\<close> have "count (mset_set E) y = 0" by (simp split: if_splits)
    from \<open>y \<in> E\<close> \<open>finite E\<close> have "count (mset_set E) y = 1" using count_mset_set(1) by auto
    from this and \<open>count (mset_set E) y = 0\<close> show False by auto
  qed
  from this and \<open>x \<noteq> y\<close> have "y \<notin> E \<union> { x }" by auto
  from this have "(count (mset_set (E \<union> { x })) y) = 0" by auto
  from this and \<open>(count (mset_set (E \<union> { x })) y) 
    > (count (mset_set E + {# x #}) y)\<close> show False by auto
qed
  
lemma mset_set_insert:
  assumes "x \<notin> E"
  assumes "finite E"
  shows "mset_set (E \<union> { x }) = mset_set E + {# x #}"
proof (rule ccontr)
  assume "\<not> ?thesis"
  from this obtain y where "(count (mset_set (E \<union> { x })) y) 
    \<noteq> (count (mset_set E + {# x #}) y)" by (meson multiset_eqI) 
  have "(count (mset_set E + {# x #}) y) = (count (mset_set E) y) + (count {# x #} y)" by auto
  from assms(2) have "finite (E \<union> { x })" by auto
  have "x \<noteq> y"
  proof
    assume "x = y"
    then have "y \<in> E \<union> { x }" by auto
    from \<open>finite (E \<union> { x })\<close> this have "(count (mset_set (E \<union> { x })) y) = 1" 
      using count_mset_set(1) by auto
    from \<open>x = y\<close> have "count {# x #} y = 1" using count_mset_set by auto
    from \<open>x = y\<close> \<open>x \<notin> E\<close> have "(count (mset_set E) y) = 0"  using count_mset_set by auto
    from \<open>count {# x #} y = 1\<close> \<open>(count (mset_set E) y) = 0\<close> 
      \<open>(count (mset_set E + {# x #}) y) = (count (mset_set E) y) + (count {# x #} y)\<close> 
      have "(count (mset_set E + {# x #}) y) = 1" by auto
    from this and \<open>(count (mset_set (E \<union> { x })) y) = 1\<close> and \<open>(count (mset_set (E \<union> { x })) y) 
    \<noteq> (count (mset_set E + {# x #}) y)\<close> show False by auto
  qed
  from \<open>x \<noteq> y\<close> have "count {# x #} y = 0" using count_mset_set by auto
  have "y \<notin> E"
  proof
    assume "y \<in> E"
    then have "y \<in> E \<union> { x }" by auto
    from \<open>finite (E \<union> { x })\<close> this have "(count (mset_set (E \<union> { x })) y) = 1" 
      using count_mset_set(1) by auto
    from assms(2) \<open>y \<in> E\<close> have "(count (mset_set E) y) = 1"  using count_mset_set by auto
    from \<open>count {# x #} y = 0\<close> \<open>(count (mset_set E) y) = 1\<close> 
      \<open>(count (mset_set E + {# x #}) y) = (count (mset_set E) y) + (count {# x #} y)\<close> 
      have "(count (mset_set E + {# x #}) y) = 1" by auto
    from this and \<open>(count (mset_set (E \<union> { x })) y) = 1\<close> and \<open>(count (mset_set (E \<union> { x })) y) 
    \<noteq> (count (mset_set E + {# x #}) y)\<close> show False by auto
  qed
  from this and \<open>x \<noteq> y\<close> have "y \<notin> E \<union> { x }" by auto
  from this have "(count (mset_set (E \<union> { x })) y) = 0" by auto
  from \<open>y \<notin> E\<close> have "(count (mset_set E) y) = 0" using count_mset_set by auto
  from \<open>count {# x #} y = 0\<close> \<open>(count (mset_set E) y) = 0\<close> 
      \<open>(count (mset_set E + {# x #}) y) = (count (mset_set E) y) + (count {# x #} y)\<close> 
      have "(count (mset_set E + {# x #}) y) = 0" by auto
   from this and \<open>(count (mset_set (E \<union> { x })) y) = 0\<close> and \<open>(count (mset_set (E \<union> { x })) y) 
    \<noteq> (count (mset_set E + {# x #}) y)\<close> show False by auto
qed

lemma mset_image_comp:
  shows "{# (f x). x \<in># {# (g x). x \<in># E #} #} = {# (f (g x)). x \<in># E #}"
   by (simp add: image_mset.compositionality comp_def)

lemma mset_set_mset_image:
  shows "\<And> E. card E = N \<Longrightarrow> finite E \<Longrightarrow> mset_set (g ` E) \<subseteq>#  {# (g x). x \<in># mset_set (E) #}"
proof (induction N)
  case 0
    assume "card E = 0"
    assume "finite E"
    from this and \<open>card E = 0\<close> have "E = {}" by auto
    then show "mset_set (g ` E) \<subseteq>#  {# (g x). x \<in># mset_set (E) #}" by auto
next
  case (Suc N)
    assume "card E = (Suc N)"
    assume "finite E"
    from this and \<open>card E = (Suc N)\<close> have "E \<noteq> {}" by auto
    from this obtain x where "x \<in> E" by auto
    let ?E = "E - { x }"
    from \<open>finite E\<close> \<open>card E = (Suc N)\<close> and \<open>x \<in> E\<close> have "card ?E = N" by auto
    from \<open>finite E\<close> have "finite ?E" by auto
    from this and "Suc.IH" [of ?E] and \<open>card ?E = N\<close> 
      have ind: "mset_set (g ` ?E) \<subseteq>#  {# (g x). x \<in># mset_set (?E) #}" by force
    from \<open>x \<in> E\<close> have "E = ?E \<union> { x }" by auto
    have "x \<notin> ?E" by auto
    from \<open>finite ?E\<close> \<open>E = ?E \<union> { x }\<close> and \<open>x \<notin> ?E\<close> have "mset_set (?E \<union> { x }) = mset_set ?E + {# x #}" 
      using mset_set_insert [of x ?E] by auto
    from this have 
    "{# (g x). x \<in># mset_set (?E \<union> { x }) #} = {# (g x). x \<in># mset_set ?E #} + {# (g x) #}"
      by auto
    have "(g ` (?E \<union> { x }) = (g ` ?E) \<union> { g x })" by auto
    from this have i: "mset_set (g ` (?E \<union> { x })) = mset_set ( (g ` ?E) \<union> { g x } )" by auto 
    from \<open>finite ?E\<close> have "finite (g ` ?E)" by auto
    from this have "mset_set ( (g ` ?E) \<union> { g x } ) \<subseteq># mset_set (g ` ?E) + {# (g x) #}" 
        using  mset_set_insert_eq [of "(g ` ?E)" "(g x)" ] by meson
    from this i have ii: "mset_set (g ` (?E \<union> { x })) \<subseteq># mset_set (g ` ?E) + {# (g x) #}" by auto
    from ind have "mset_set (g ` ?E) + {# (g x) #} \<subseteq>#  {# (g x). x \<in># mset_set (?E) #} + {# (g x) #}" 
      using Multiset.subset_mset.add_right_mono by metis
    from this and ii have "mset_set (g ` (?E \<union> { x })) \<subseteq># {# (g x). x \<in># mset_set (?E) #} + {# (g x) #}"
      using Multiset.subset_mset.order.trans [of "mset_set (g ` (?E \<union> { x }))" ] by metis
    from this and \<open>E = ?E \<union> { x }\<close> \<open>{# (g x). x \<in># mset_set (?E \<union> { x }) #} = {# (g x). x \<in># mset_set ?E #} + {# (g x) #}\<close> 
     show "mset_set (g ` E) \<subseteq># {# (g x). x \<in># mset_set E #}" 
      by metis
qed

lemma split_mset_set: 
  assumes "C = C1 \<union> C2"
  assumes "C1 \<inter> C2 = {}"
  assumes "finite C1"
  assumes "finite C2"
  shows "(mset_set C) = (mset_set C1) + (mset_set C2)"
proof (rule ccontr)
  assume "(mset_set C) \<noteq> (mset_set C1) + (mset_set C2)"
  then obtain x where "count (mset_set C) x \<noteq> count ((mset_set C1) + (mset_set C2)) x"
    by (meson multiset_eqI)
  from assms(3) assms(4) assms(1) have "finite C" by auto

  have "count ((mset_set C1) + (mset_set C2)) x = (count (mset_set C1) x) + (count (mset_set C2) x)"
    by auto
  from this and \<open>count (mset_set C) x \<noteq> count ((mset_set C1) + (mset_set C2)) x\<close> have 
    "count (mset_set C) x \<noteq> (count (mset_set C1) x) + (count (mset_set C2) x)" by auto
  have "x \<in> C1 \<or> x \<in> C2"
  proof (rule ccontr)
    assume "\<not> (x \<in> C1 \<or> x \<in> C2)"
    then have "x \<notin> C1" and "x\<notin> C2" by auto
    from assms(1) \<open>x \<notin> C1\<close> and \<open>x\<notin> C2\<close> have "x \<notin> C" by auto
    from \<open>x \<notin> C1\<close> have "(count (mset_set C1) x) = 0" by auto
    from \<open>x \<notin> C2\<close> have "(count (mset_set C2) x) = 0" by auto
    from \<open>x \<notin> C\<close> have "(count (mset_set C) x) = 0" by auto
    from \<open>(count (mset_set C1) x) = 0\<close> \<open>(count (mset_set C2) x) = 0\<close> 
      \<open>(count (mset_set C) x) = 0\<close> 
      \<open>count (mset_set C) x \<noteq> (count (mset_set C1) x) + (count (mset_set C2) x)\<close>
      show False by auto
  qed

  have "(x \<notin> C1 \<or> x \<in> C2)"
  proof (rule ccontr)
    assume "\<not> (x \<notin> C1 \<or> x \<in> C2)"  
    then have "x \<in> C1" and " x\<notin> C2" by auto
    from assms(1) \<open>x \<in> C1\<close> have "x \<in> C" by auto
    from assms(3) \<open>x \<in> C1\<close> have "(count (mset_set C1) x) = 1" by auto
    from \<open>x \<notin> C2\<close> have "(count (mset_set C2) x) = 0" by auto
    from assms(3) assms(4) assms(1) have "finite C" by auto
    from \<open>finite C\<close> \<open>x \<in> C\<close> have "(count (mset_set C) x) = 1" by auto
    from \<open>(count (mset_set C1) x) = 1\<close> \<open>(count (mset_set C2) x) = 0\<close> 
      \<open>(count (mset_set C) x) = 1\<close> 
      \<open>count (mset_set C) x \<noteq> (count (mset_set C1) x) + (count (mset_set C2) x)\<close>
      show False by auto
  qed
  have "(x \<notin> C2 \<or> x \<in> C1)"
  proof (rule ccontr)
    assume "\<not> (x \<notin> C2 \<or> x \<in> C1)"  
    then have "x \<in> C2" and " x\<notin> C1" by auto
    from assms(1) \<open>x \<in> C2\<close> have "x \<in> C" by auto
    from assms(4) \<open>x \<in> C2\<close> have "(count (mset_set C2) x) = 1" by auto
    from \<open>x \<notin> C1\<close> have "(count (mset_set C1) x) = 0" by auto
    from \<open>finite C\<close> \<open>x \<in> C\<close> have "(count (mset_set C) x) = 1" by auto
    from \<open>(count (mset_set C2) x) = 1\<close> \<open>(count (mset_set C1) x) = 0\<close> 
      \<open>(count (mset_set C) x) = 1\<close> 
      \<open>count (mset_set C) x \<noteq> (count (mset_set C1) x) + (count (mset_set C2) x)\<close>
      show False by auto
  qed
  from \<open>x \<in> C1 \<or> x \<in> C2\<close> \<open>(x \<notin> C1 \<or> x \<in> C2)\<close> \<open>(x \<notin> C2 \<or> x \<in> C1)\<close>
    have "x \<in> C1 \<and> x \<in> C2" by blast
  from this and assms(2) show False by auto
qed

lemma image_mset_thm:
  assumes "E = {# (f x). x \<in># E' #}"
  assumes "x \<in># E"
  shows "\<exists> y. ((y \<in># E') \<and> x = (f y))"
using assms by auto

lemma split_image_mset:
  assumes "M = M1 + M2"
  shows "{# (f x). x \<in># M #} = {# (f x). x \<in># M1 #} + {# (f x). x \<in># M2 #}"
by (simp add: assms)

end
