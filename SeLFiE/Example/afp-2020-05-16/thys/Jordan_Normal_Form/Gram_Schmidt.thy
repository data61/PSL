(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Gram-Schmidt Orthogonalization\<close>

text \<open>
  This theory provides the Gram-Schmidt orthogonalization algorithm,
  that takes the conjugate operation into account. It works over fields
  like the rational, real, or complex numbers. 
\<close>

theory Gram_Schmidt
imports 
  VS_Connect 
  Missing_VectorSpace
  Conjugate
begin

subsection \<open>Orthogonality with Conjugates\<close>

definition "corthogonal vs \<equiv>
    \<forall>i < length vs. \<forall>j < length vs. vs ! i \<bullet>c vs ! j = 0 \<longleftrightarrow> i \<noteq> j"

lemma corthogonalD[elim]:
  "corthogonal vs \<Longrightarrow> i < length vs \<Longrightarrow> j < length vs \<Longrightarrow>
   vs ! i \<bullet>c vs ! j = 0 \<longleftrightarrow> i \<noteq> j"
  unfolding corthogonal_def by auto

lemma corthogonalI[intro]:
  "(\<And>i j. i < length vs \<Longrightarrow> j < length vs \<Longrightarrow> vs ! i \<bullet>c vs ! j = 0 \<longleftrightarrow> i \<noteq> j) \<Longrightarrow>
   corthogonal vs"
  unfolding corthogonal_def by auto

lemma corthogonal_distinct: "corthogonal us \<Longrightarrow> distinct us"
proof (induct us)
  case (Cons u us)
    have "u \<notin> set us"
    proof
      assume "u : set us"
      then obtain j where uj: "u = us!j" and j: "j < length us"
        using in_set_conv_nth by metis
      hence j': "j+1 < length (u#us)" by auto
      have "u \<bullet>c us!j = 0"
        using corthogonalD[OF Cons(2) _ j',of 0] by auto
      hence "u \<bullet>c u = 0" using uj by simp
      thus False using corthogonalD[OF Cons(2),of 0 0] by auto
    qed
    moreover have "distinct us"
    proof (rule Cons(1),intro corthogonalI)
      fix i j assume "i < length (us)" "j < length (us)"
      hence len: "i+1 < length (u#us)" "j+1 < length (u#us)" by auto
      show "(us!i \<bullet>c us!j = 0) = (i\<noteq>j)"
        using corthogonalD[OF Cons(2) len] by simp
    qed
    ultimately show ?case by simp
qed simp

lemma corthogonal_sort:
  assumes dist': "distinct us'"
      and mem: "set us = set us'"
  shows "corthogonal us \<Longrightarrow> corthogonal us'"
proof
  assume orth: "corthogonal us"
  hence dist: "distinct us" using corthogonal_distinct by auto
  fix i' j' assume i': "i' < length us'" and j': "j' < length us'"
  obtain i where ii': "us!i = us'!i'" and i: "i < length us"
    using mem i' in_set_conv_nth by metis
  obtain j where jj': "us!j = us'!j'" and j: "j < length us"
    using mem j' in_set_conv_nth by metis
  from corthogonalD[OF orth i j]
  have "(us!i \<bullet>c us!j = 0) = (i \<noteq> j)".
  hence "(us'!i' \<bullet>c us'!j' = 0) = (i \<noteq> j)" using ii' jj' by auto
  also have "... = (us!i \<noteq> us!j)" using nth_eq_iff_index_eq dist i j by auto
  also have "... = (us'!i' \<noteq> us'!j')" using ii' jj' by auto
  also have "... = (i' \<noteq> j')" using nth_eq_iff_index_eq dist' i' j' by auto
  finally show "(us'!i' \<bullet>c us'!j' = 0) = (i' \<noteq> j')".
qed

subsection\<open>The Algorithm\<close>

fun adjuster :: "nat \<Rightarrow> 'a :: conjugatable_field vec \<Rightarrow> 'a vec list \<Rightarrow> 'a vec"
  where "adjuster n w [] = 0\<^sub>v n"
    |  "adjuster n w (u#us) = -(w \<bullet>c u)/(u \<bullet>c u) \<cdot>\<^sub>v u + adjuster n w us"

text \<open>
  The following formulation is easier to analyze,
  but outputs of the subroutine should be properly reversed.
\<close>

fun gram_schmidt_sub
  where "gram_schmidt_sub n us [] = us"
  | "gram_schmidt_sub n us (w # ws) =
     gram_schmidt_sub n ((adjuster n w us + w) # us) ws"

definition gram_schmidt :: "nat \<Rightarrow> 'a :: conjugatable_field vec list \<Rightarrow> 'a vec list"
  where "gram_schmidt n ws = rev (gram_schmidt_sub n [] ws)"

text \<open>
  The following formulation requires no reversal.
\<close>

fun gram_schmidt_sub2
  where "gram_schmidt_sub2 n us [] = []"
  | "gram_schmidt_sub2 n us (w # ws) =
     (let u = adjuster n w us + w in
      u # gram_schmidt_sub2 n (u # us) ws)"

lemma gram_schmidt_sub_eq:
  "rev (gram_schmidt_sub n us ws) = rev us @ gram_schmidt_sub2 n us ws"
  by (induct ws arbitrary:us, auto simp:Let_def)

lemma gram_schmidt_code[code]:
  "gram_schmidt n ws = gram_schmidt_sub2 n [] ws"
  unfolding gram_schmidt_def
  apply(subst gram_schmidt_sub_eq) by simp

subsection \<open>Properties of the Algorithms\<close>

locale cof_vec_space = vec_space f_ty for
  f_ty :: "'a :: conjugatable_ordered_field itself"
begin

lemma adjuster_finsum:
  assumes U: "set us \<subseteq> carrier_vec n"
    and dist: "distinct (us :: 'a vec list)"
  shows "adjuster n w us = finsum V (\<lambda>u. -(w \<bullet>c u)/(u \<bullet>c u) \<cdot>\<^sub>v u) (set us)"
  using assms
proof (induct us)
  case Cons show ?case unfolding set_simps
  by (subst finsum_insert[OF finite_set], insert Cons, auto)
qed simp

lemma adjuster_lincomb:
  assumes w: "(w :: 'a vec) : carrier_vec n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
    and dist: "distinct us"
  shows "adjuster n w us = lincomb (\<lambda>u. -(w \<bullet>c u)/(u \<bullet>c u)) (set us)"
    (is "_ = lincomb ?a _")
  using us dist unfolding lincomb_def
proof (induct us)
  case (Cons u us)
    let ?f = "\<lambda>u. ?a u \<cdot>\<^sub>v u"
    have "?f : (set us) \<rightarrow> carrier_vec n" and "?f u : carrier_vec n" using w Cons by auto
    moreover have "u \<notin> set us" using Cons by auto
    ultimately show ?case
      unfolding adjuster.simps
      unfolding set_simps
      using finsum_insert[OF finite_set] Cons by auto
qed simp

lemma adjuster_in_span:
  assumes w: "(w :: 'a vec) : carrier_vec n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
    and dist: "distinct us"
  shows "adjuster n w us : span (set us)"
  using adjuster_lincomb[OF assms]
  unfolding finite_span[OF finite_set us] by auto

lemma adjuster_carrier[simp]:
  assumes w: "(w :: 'a vec) : carrier_vec n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
    and dist: "distinct us"
  shows "adjuster n w us : carrier_vec n"
  using adjuster_in_span span_closed assms by auto

lemma adjust_not_in_span:
  assumes w[simp]: "(w :: 'a vec) : carrier_vec n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
    and dist: "distinct us"
    and ind: "w \<notin> span (set us)"
  shows "adjuster n w us + w \<notin> span (set us)"
  using span_add[OF us adjuster_in_span[OF w us dist] w]
  using comm_add_vec ind by auto

lemma adjust_not_mem:
  assumes w[simp]: "(w :: 'a vec) : carrier_vec n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
    and dist: "distinct us"
    and ind: "w \<notin> span (set us)"
  shows "adjuster n w us + w \<notin> set us"
  using adjust_not_in_span[OF assms] span_mem[OF us] by auto

lemma adjust_in_span:
  assumes w[simp]: "(w :: 'a vec) : carrier_vec n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
    and dist: "distinct us"
  shows "adjuster n w us + w : span (insert w (set us))" (is "?v + _ : span ?U")
proof -
  let ?a = "\<lambda>u. -(w \<bullet>c u)/(u \<bullet>c u)"
  have "?v = lincomb ?a (set us)" using adjuster_lincomb[OF assms].
  hence vU: "?v : span (set us)" unfolding finite_span[OF finite_set us] by auto
  hence v[simp]: "?v : carrier_vec n" using span_closed[OF us] by auto
  have vU': "?v : span ?U" using vU span_is_monotone[OF subset_insertI] by auto

  have "{w} \<subseteq> ?U" by simp
  from span_is_monotone[OF this]
  have wU': "w : span ?U" using span_self[OF w] by auto

  have "?U \<subseteq> carrier_vec n" using us w by simp
  from span_add[OF this wU' v] vU' comm_add_vec[OF w]
  show ?thesis by simp
qed

lemma adjust_not_lindep:
  assumes w[simp]: "(w :: 'a vec) : carrier_vec n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
    and dist: "distinct us"
    and wus: "w \<notin> span (set us)"
    and ind: "~ lin_dep (set us)"
  shows "~ lin_dep (insert (adjuster n w us + w) (set us))"
    (is "~ _ (insert ?v _)")
proof -
  have v: "?v : carrier_vec n" using assms by auto
  have "?v \<notin> span (set us)"
    using adjust_not_in_span[OF w us dist wus]
    using comm_add_vec[OF adjuster_carrier[OF w us dist] w] by auto
  thus ?thesis
    using lin_dep_iff_in_span[OF us ind v] adjust_not_mem[OF w us dist wus] by auto
qed

lemma adjust_preserves_span:
  assumes w[simp]: "(w :: 'a vec) : carrier_vec n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
    and dist: "distinct us"
  shows "w : span (set us) \<longleftrightarrow> adjuster n w us + w : span (set us)"
    (is "_ \<longleftrightarrow> ?v + _ : _")
proof -
  have "?v : span (set us)"
    using adjuster_lincomb[OF assms]
    unfolding finite_span[OF finite_set us] by auto
  hence [simp]: "?v : carrier_vec n" using span_closed[OF us] by auto
  show ?thesis
    using span_add[OF us adjuster_in_span[OF w us] w] comm_add_vec[OF w] dist
    by auto
qed

lemma in_span_adjust:
  assumes w[simp]: "(w :: 'a vec) : carrier_vec n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
    and dist: "distinct us"
  shows "w : span (insert (adjuster n w us + w) (set us))"
    (is "_ : span (insert ?v _)")
proof -
  have v: "?v : carrier_vec n" using assms by auto
  have a[simp]: "adjuster n w us : carrier_vec n"
   and neg: "- adjuster n w us : carrier_vec n" using assms by auto
  hence vU: "insert ?v (set us) \<subseteq> carrier_vec n" using us by auto
  have aS: "adjuster n w us : span (insert ?v (set us))"
    using adjuster_in_span[OF w us] span_is_monotone[OF subset_insertI] dist
    by auto
  have negS: "- adjuster n w us : span (insert ?v (set us))"
    using span_neg[OF vU aS] us by simp
  have [simp]:"- adjuster n w us + (adjuster n w us + w) = w"
    unfolding a_assoc[OF neg a w,symmetric] by simp
  have "{?v} \<subseteq> insert ?v (set us)" by simp
  from span_is_monotone[OF this]
  have vS: "?v : span (insert ?v (set us))" using span_self[OF v] by auto
  thus ?thesis using span_add[OF vU negS v] by auto
qed

lemma adjust_zero:
  assumes U: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
    and orth: "corthogonal us"
    and w[simp]: "w : carrier_vec n"
    and i: "i < length us"
  shows "(adjuster n w us + w) \<bullet>c us!i = 0"
proof -
  define u where "u = us!i"
  have u[simp]: "u : carrier_vec n" using i U u_def by auto
  hence cu[simp]: "conjugate u : carrier_vec n" by auto
  have uU: "u : set us" using i u_def by auto
  let ?g = "\<lambda>u'::'a vec. (-(w \<bullet>c u')/(u' \<bullet>c u') \<cdot>\<^sub>v u')"
  have g: "?g : set us \<rightarrow> carrier_vec n" using w U by auto
  hence carrier: "finsum V ?g (set us) : carrier_vec n" by simp
  let ?f = "\<lambda>u'. ?g u' \<bullet>c u"
  let ?U = "set us - {u}"
  { fix u' assume u': "(u'::'a vec) : carrier_vec n"
    have [simp]: "dim_vec u = n" by auto
    have "?f u' = (- (w \<bullet>c u') / (u' \<bullet>c u')) * (u' \<bullet>c u)"
      using scalar_prod_smult_left[of "u'" "conjugate u"]
      unfolding carrier_vecD[OF u] carrier_vecD[OF u'] by auto
  } note conv = this
  have "?f : ?U \<rightarrow> {0}"
  proof (intro Pi_I)
    fix u' assume u'Uu: "u' : set us - {u}"
    hence u'U: "u' : set us" by auto
    hence u'[simp]: "u' : carrier_vec n" using U by auto
    obtain j where j: "j < length us" and u'j: "u' = us ! j"
      using u'U in_set_conv_nth by metis
    have "i \<noteq> j" using u'Uu u'j u_def by auto
    hence "u' \<bullet>c u = 0"
      unfolding u'j using corthogonalD[OF orth j i] u_def by auto
    hence "?f u' = 0" using mult_zero_right conv[OF u'] by auto
    thus "?f u' : {0}" by auto
  qed
  hence "restrict ?f ?U = restrict (\<lambda>u. 0) ?U" by force
  hence "sum ?f ?U = sum (\<lambda>u. 0) ?U"
    by (intro R.finsum_restrict, auto)
  hence fU'0: "sum ?f ?U = 0" by auto
  have uU': "u \<notin> ?U" by auto
  have "set us = insert u ?U"
    using insert_Diff_single uU by auto
  hence "sum ?f (set us) = ?f u + sum ?f ?U"
    using R.finsum_insert[OF _ uU'] by auto
  also have "... = ?f u" using fU'0 by auto
  also have "... = - (w \<bullet>c u) / (u \<bullet>c u) * (u \<bullet>c u)"
    using conv[OF u] by auto
  finally have main: "sum ?f (set us) = - (w \<bullet>c u)"
    unfolding u_def
    by (simp add: i orth corthogonalD)
  show ?thesis
    unfolding u_def[symmetric]
    unfolding adjuster_finsum[OF U corthogonal_distinct[OF orth]]
    unfolding add_scalar_prod_distrib[OF carrier w cu]
    unfolding finsum_scalar_prod_sum[OF g cu]
    unfolding main
    unfolding comm_scalar_prod[OF cu w]
    using left_minus by auto
qed

lemma adjust_nonzero:
  assumes U: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
    and dist: "distinct us"
    and w[simp]: "w : carrier_vec n"
    and wsU: "w \<notin> span (set us)"
  shows "adjuster n w us + w \<noteq> 0\<^sub>v n" (is "?a + _ \<noteq> _")
proof
  have [simp]: "?a : carrier_vec n" using U dist by auto
  have [simp]: "- ?a : carrier_vec n" by auto
  have [simp]: "?a + w : carrier_vec n" by auto
  assume "?a + w = 0\<^sub>v n"
  hence "- ?a = - ?a + (?a + w)" by auto
  also have "... = (- ?a + ?a) + w" apply(subst a_assoc) by auto
  also have "- ?a + ?a = 0\<^sub>v n" using r_neg[OF w] unfolding vec_neg[OF w] by auto
  finally have "- ?a = w" by auto
  moreover have "- ?a : span (set us)"
    using span_neg[OF U adjuster_in_span[OF w U dist]] by auto
  ultimately show "False" using wsU by auto
qed

lemma adjust_orthogonal:
  assumes U: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
    and orth: "corthogonal us"
    and w[simp]: "w : carrier_vec n"
    and wsU: "w \<notin> span (set us)"
  shows "corthogonal ((adjuster n w us + w) # us)"
    (is "corthogonal (?aw # _)")
proof
  have dist: "distinct us" using corthogonal_distinct orth by auto
  have aw[simp]: "?aw : carrier_vec n" using U dist by auto
  note adjust_nonzero[OF U dist w] wsU
  hence aw0: "?aw \<bullet>c ?aw \<noteq> 0" using conjugate_square_eq_0_vec[OF aw] by auto
  fix i j assume i: "i < length (?aw # us)" and j: "j < length (?aw # us)"
  show "((?aw # us) ! i \<bullet>c (?aw # us) ! j = 0) = (i \<noteq> j)"
  proof (cases "i = 0")
    case True note i0 = this
      show ?thesis
      proof (cases "j = 0")
        case True show ?thesis unfolding True i0 using aw0 by auto
        next case False
          define j' where "j' = j-1"
          hence jfold: "j = j'+1" using False by auto
          hence j': "j' < length us" using j by auto
          show ?thesis unfolding i0 jfold
            using adjust_zero[OF U orth w j'] by auto
      qed
    next case False
      define i' where "i' = i-1"
      hence ifold: "i = i'+1" using False by auto
      hence i': "i' < length us" using i by auto
      have [simp]: "us ! i' : carrier_vec n" using U i' by auto
      hence cu': "conjugate (us ! i') : carrier_vec n" by auto
      show ?thesis
      proof (cases "j = 0")
        case True
          { assume "?aw \<bullet>c us ! i' = 0"
            hence "conjugate (?aw \<bullet>c us ! i') = 0" using conjugate_zero by auto
            hence "conjugate ?aw \<bullet> us ! i' = 0"
              using conjugate_sprod_vec[OF aw cu'] by auto
          }
          thus ?thesis unfolding True ifold
          using adjust_zero[OF U orth w i']
          by (subst comm_scalar_prod[of _ n], auto)
        next case False
          define j' where "j' = j-1"
          hence jfold: "j = j'+1" using False by auto
          hence j': "j' < length us" using j by auto
          show ?thesis
            unfolding ifold jfold
            using orth i' j' by (auto simp: corthogonalD)
     qed
  qed
qed

lemma gram_schmidt_sub_span:
  assumes w[simp]: "w : carrier_vec n"
    and us: "set us \<subseteq> carrier_vec n"
    and dist: "distinct us"
  shows "span (set ((adjuster n w us + w) # us)) = span (set (w # us))"
  (is "span (set (?v # _)) = span ?wU")
proof (cases "w : span (set us)")
  case True
    hence "?v : span (set us)"
      using adjust_preserves_span[OF assms] by auto
    thus ?thesis using already_in_span[OF us] True by auto next
  case False show ?thesis
    proof
      have wU: "?wU \<subseteq> carrier_vec n" using us by simp 
      have vswU: "?v : span ?wU" using adjust_in_span[OF assms] by auto
      hence v: "?v : carrier_vec n" using span_closed[OF wU] by auto
      have wsvU: "w : span (insert ?v (set us))" using in_span_adjust[OF assms].
      show "span ?wU \<subseteq> span (set (?v # us))"
        using span_swap[OF finite_set us w False v wsvU] by auto
      have "?v \<notin> span (set us)"
        using False adjust_preserves_span[OF assms] by auto
      thus "span (set (?v # us)) \<subseteq> span ?wU"
        using span_swap[OF finite_set us v _ w] vswU by auto
    qed
qed

lemma gram_schmidt_sub_result:
  assumes "gram_schmidt_sub n us ws = us'"
    and "set ws \<subseteq> carrier_vec n"
    and "set us \<subseteq> carrier_vec n"
    and "distinct (us @ ws)"
    and "~ lin_dep (set (us @ ws))"
    and "corthogonal us"
  shows "set us' \<subseteq> carrier_vec n \<and>
         distinct us' \<and>
         corthogonal us' \<and>
         span (set (us @ ws)) = span (set us') \<and> length us' = length us + length ws"  
  using assms
proof (induct ws arbitrary: us us')
case (Cons w ws)
  let ?v = "adjuster n w us"
  have wW[simp]: "set (w#ws) \<subseteq> carrier_vec n" using Cons by simp
  hence W[simp]: "set ws \<subseteq> carrier_vec n"
   and w[simp]: "w : carrier_vec n" by auto
  have U[simp]: "set us \<subseteq> carrier_vec n" using Cons by simp
  have UW: "set (us@ws) \<subseteq> carrier_vec n" by simp
  have wU: "set (w#us) \<subseteq> carrier_vec n" by simp
  have dist: "distinct (us @ w # ws)" using Cons by simp
  hence dist_U: "distinct us"
    and dist_W: "distinct ws"
    and dist_UW: "distinct (us @ ws)"
    and w_U: "w \<notin> set us"
    and w_W: "w \<notin> set ws"
    and w_UW: "w \<notin> set (us @ ws)" by auto
  have ind: "~ lin_dep (set (us @ w # ws))" using Cons by simp
  have ind_U: "~ lin_dep (set us)"
    and ind_W: "~ lin_dep (set ws)"
    and ind_wU: "~ lin_dep (insert w (set us))"
    and ind_UW: "~ lin_dep (set (us @ ws))"
    by (subst subset_li_is_li[OF ind];auto)+
  have corth: "corthogonal us" using Cons by simp
  have U'def: "gram_schmidt_sub n ((?v + w)#us) ws = us'" using Cons by simp

  have v: "?v : carrier_vec n" using dist_U by auto
  hence vw: "?v + w : carrier_vec n" by auto
  hence vwU: "set ((?v + w) # us) \<subseteq> carrier_vec n" by auto
  have vsU: "?v : span (set us)" using adjuster_in_span[OF w] dist by auto
  hence vsUW: "?v : span (set (us @ ws))"
    using span_is_monotone[of "set us" "set (us@ws)"] by auto
  have wsU: "w \<notin> span (set us)"
    using lin_dep_iff_in_span[OF U ind_U w w_U] ind_wU by auto
  hence vwU: "?v + w \<notin> span (set us)" using adjust_not_in_span[OF w U dist_U] by auto

  have "w \<notin> span (set (us@ws))" using lin_dep_iff_in_span[OF _ ind_UW] dist ind by auto
  hence span: "?v + w \<notin> span (set (us@ws))" using span_add[OF UW vsUW w] by auto
  hence vwUS: "?v + w \<notin> set (us @ ws)" using span_mem by auto
  hence ind2: "~ lin_dep (set (((?v + w) # us) @ ws))"
    using lin_dep_iff_in_span[OF UW ind_UW vw] span by auto

  have vwU: "set ((?v + w) # us) \<subseteq> carrier_vec n" using U w dist by auto
  have dist2: "distinct (((?v + w) # us) @ ws)" using dist vwUS by simp

  have orth2: "corthogonal ((adjuster n w us + w) # us)"
    using adjust_orthogonal[OF U corth w wsU].

  show ?case
    using Cons(1)[OF U'def W vwU dist2 ind2] orth2
    using span_Un[OF vwU wU gram_schmidt_sub_span[OF w U dist_U] W W] by auto
    
qed simp

lemma gram_schmidt_hd [simp]:
  assumes [simp]: "w : carrier_vec n" shows "hd (gram_schmidt n (w#ws)) = w"
  unfolding gram_schmidt_code by simp

theorem gram_schmidt_result:
  assumes ws: "set ws \<subseteq> carrier_vec n"
    and dist: "distinct ws"
    and ind: "~ lin_dep (set ws)"
    and us: "us = gram_schmidt n ws"
  shows "span (set ws) = span (set us)"
    and "corthogonal us"
    and "set us \<subseteq> carrier_vec n"
    and "length us = length ws"
    and "distinct us"
proof -
  have main: "gram_schmidt_sub n [] ws = rev us"
    using us unfolding gram_schmidt_def
    using gram_schmidt_sub_eq by auto
  have orth: "corthogonal []" by auto
  have "span (set ws) = span (set (rev us))"
   and orth2: "corthogonal (rev us)"
   and "set us \<subseteq> carrier_vec n"
   and "length us = length ws"
   and dist: "distinct us" 
    using gram_schmidt_sub_result[OF main ws]
    by (auto simp: assms orth)
  thus "span (set ws) = span (set us)" by simp
  show "set us \<subseteq> carrier_vec n" by fact
  show "length us = length ws" by fact
  show "distinct us" by fact
  show "corthogonal us"
    using corthogonal_distinct[OF orth2] unfolding distinct_rev
    using corthogonal_sort[OF _ set_rev orth2] by auto
qed
end

end
