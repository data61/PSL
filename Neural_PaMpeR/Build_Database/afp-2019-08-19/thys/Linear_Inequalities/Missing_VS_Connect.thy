section \<open>Missing Lemmas on Vector Spaces\<close>

text \<open>We provide some results on vector spaces which should be merged into other AFP entries.\<close>
theory Missing_VS_Connect
  imports
    Jordan_Normal_Form.VS_Connect
    Missing_Matrix
    Polynomial_Factorization.Missing_List
begin

context vec_space
begin
lemma span_diff: assumes A: "A \<subseteq> carrier_vec n"
  and a: "a \<in> span A" and b: "b \<in> span A"
shows "a - b \<in> span A"
proof -
  from A a have an: "a \<in> carrier_vec n" by auto
  from A b have bn: "b \<in> carrier_vec n" by auto
  have "a + (-1 \<cdot>\<^sub>v b) \<in> span A"
    by (rule span_add1[OF A a], insert b A, auto)
  also have "a + (-1 \<cdot>\<^sub>v b) = a - b" using an bn by auto
  finally show ?thesis by auto
qed

lemma finsum_scalar_prod_sum':
  assumes f: "f \<in> U \<rightarrow> carrier_vec n"
    and w: "w \<in> carrier_vec n"
  shows "w \<bullet> finsum V f U = sum (\<lambda>u. w \<bullet> f u) U"
  by (subst comm_scalar_prod[OF w], (insert f, auto)[1],
      subst finsum_scalar_prod_sum[OF f w],
      insert f, intro sum.cong[OF refl] comm_scalar_prod[OF _ w], auto)

lemma lincomb_scalar_prod_left: assumes "W \<subseteq> carrier_vec n" "v \<in> carrier_vec n"
  shows "lincomb a W \<bullet> v = (\<Sum>w\<in>W. a w * (w \<bullet> v))"
  unfolding lincomb_def
  by (subst finsum_scalar_prod_sum, insert assms, auto intro!: sum.cong)

lemma lincomb_scalar_prod_right: assumes "W \<subseteq> carrier_vec n" "v \<in> carrier_vec n"
  shows "v \<bullet> lincomb a W = (\<Sum>w\<in>W. a w * (v \<bullet> w))"
  unfolding lincomb_def
  by (subst finsum_scalar_prod_sum', insert assms, auto intro!: sum.cong)

lemma lin_indpt_empty[simp]: "lin_indpt {}"
  using lin_dep_def by auto

lemma span_carrier_lin_indpt_card_n:
  assumes "W \<subseteq> carrier_vec n" "card W = n" "lin_indpt W"
  shows "span W = carrier_vec n"
  using assms basis_def dim_is_n dim_li_is_basis fin_dim_li_fin by simp

lemma ortho_span: assumes W: "W \<subseteq> carrier_vec n"
  and X: "X \<subseteq> carrier_vec n"
  and ortho: "\<And> w x. w \<in> W \<Longrightarrow> x \<in> X \<Longrightarrow> w \<bullet> x = 0"
  and w: "w \<in> span W" and x: "x \<in> X"
shows "w \<bullet> x = 0"
proof -
  from w W obtain c V where "finite V" and VW: "V \<subseteq> W" and w: "w = lincomb c V"
    by (meson in_spanE)
  show ?thesis unfolding w
    by (subst lincomb_scalar_prod_left, insert W VW X x ortho, auto intro!: sum.neutral)
qed

lemma ortho_span': assumes W: "W \<subseteq> carrier_vec n"
  and X: "X \<subseteq> carrier_vec n"
  and ortho: "\<And> w x. w \<in> W \<Longrightarrow> x \<in> X \<Longrightarrow> x \<bullet> w = 0"
  and w: "w \<in> span W" and x: "x \<in> X"
shows "x \<bullet> w = 0"
proof -
  from w W obtain c V where "finite V" and VW: "V \<subseteq> W" and w: "w = lincomb c V"
    by (meson in_spanE)
  show ?thesis unfolding w
    by (subst lincomb_scalar_prod_right, insert W VW X x ortho, auto intro!: sum.neutral)
qed

lemma ortho_span_span: assumes W: "W \<subseteq> carrier_vec n"
  and X: "X \<subseteq> carrier_vec n"
  and ortho: "\<And> w x. w \<in> W \<Longrightarrow> x \<in> X \<Longrightarrow> w \<bullet> x = 0"
  and w: "w \<in> span W" and x: "x \<in> span X"
shows "w \<bullet> x = 0"
  by (rule ortho_span[OF W _ ortho_span'[OF X W _ _] w x], insert W X ortho, auto)

lemma lincomb_in_span[intro]:
  assumes X: "X\<subseteq> carrier_vec n"
  shows "lincomb a X \<in> span X"
proof(cases "finite X")
  case False hence "lincomb a X = 0\<^sub>v n" using X
    by (simp add: lincomb_def)
  thus ?thesis using X by force
qed (insert X, auto)

lemma generating_card_n_basis: assumes X: "X \<subseteq> carrier_vec n"
  and span: "carrier_vec n \<subseteq> span X"
  and card: "card X = n"
shows "basis X"
proof -
  have fin: "finite X"
  proof (cases "n = 0")
    case False
    with card show "finite X" by (meson card_infinite)
  next
    case True
    with X have "X \<subseteq> carrier_vec 0" by auto
    also have "\<dots> = {0\<^sub>v 0}" by auto
    finally have "X \<subseteq> {0\<^sub>v 0}" .
    from finite_subset[OF this] show "finite X" by auto
  qed
  from X have "span X \<subseteq> carrier_vec n" by auto
  with span have span: "span X = carrier_vec n" by auto
  from dim_is_n card have card: "card X \<le> dim" by auto
  from dim_gen_is_basis[OF fin X span card] show "basis X" .
qed

lemma lincomb_list_append:
  assumes Ws: "set Ws \<subseteq> carrier_vec n"
  shows "set Vs \<subseteq> carrier_vec n \<Longrightarrow> lincomb_list f (Vs @ Ws) =
    lincomb_list f Vs + lincomb_list (\<lambda> i. f (i + length Vs)) Ws"
proof (induction Vs arbitrary: f)
  case Nil show ?case by(simp add: lincomb_list_carrier[OF Ws])
next
  case (Cons x Vs)
  have "lincomb_list f (x # (Vs @ Ws)) = f 0 \<cdot>\<^sub>v x + lincomb_list (f \<circ> Suc) (Vs @ Ws)"
    by (rule lincomb_list_Cons)
  also have "lincomb_list (f \<circ> Suc) (Vs @ Ws) =
             lincomb_list (f \<circ> Suc) Vs + lincomb_list (\<lambda> i. (f \<circ> Suc) (i + length Vs)) Ws"
    using Cons by auto
  also have "(\<lambda> i. (f \<circ> Suc) (i + length Vs)) = (\<lambda> i. f (i + length (x # Vs)))" by simp
  also have "f 0 \<cdot>\<^sub>v x + ((lincomb_list (f \<circ> Suc) Vs) + lincomb_list \<dots> Ws) =
             (f 0 \<cdot>\<^sub>v x + (lincomb_list (f \<circ> Suc) Vs)) + lincomb_list \<dots> Ws"
    using assoc_add_vec Cons.prems Ws lincomb_list_carrier by auto
  finally show ?case using lincomb_list_Cons by auto
qed

lemma lincomb_list_snoc[simp]:
  shows "set Vs \<subseteq> carrier_vec n \<Longrightarrow> x \<in> carrier_vec n \<Longrightarrow>
          lincomb_list f (Vs @ [x]) = lincomb_list f Vs + f (length Vs) \<cdot>\<^sub>v x"
  using lincomb_list_append by auto

lemma lincomb_list_smult:
  "set Vs \<subseteq> carrier_vec n \<Longrightarrow> lincomb_list (\<lambda> i. a * c i) Vs = a \<cdot>\<^sub>v lincomb_list c Vs"
proof (induction Vs rule: rev_induct)
  case (snoc x Vs)
  have x: "x \<in> carrier_vec n" and Vs: "set Vs \<subseteq> carrier_vec n" using snoc.prems by auto
  have "lincomb_list (\<lambda> i. a * c i) (Vs @ [x]) =
        lincomb_list (\<lambda> i. a * c i) Vs + (a * c (length Vs)) \<cdot>\<^sub>v x"
    using x Vs by auto
  also have "lincomb_list (\<lambda> i. a * c i) Vs = a \<cdot>\<^sub>v lincomb_list c Vs"
    by(rule snoc.IH[OF Vs])
  also have "(a * c (length Vs)) \<cdot>\<^sub>v x = a \<cdot>\<^sub>v (c (length Vs) \<cdot>\<^sub>v x)"
    using smult_smult_assoc x by auto
  also have "a \<cdot>\<^sub>v lincomb_list c Vs + \<dots> = a \<cdot>\<^sub>v (lincomb_list c Vs + c (length Vs) \<cdot>\<^sub>v x)"
    using smult_add_distrib_vec[of _ n _ a] lincomb_list_carrier[OF Vs] x by simp
  also have "lincomb_list c Vs + c (length Vs) \<cdot>\<^sub>v x = lincomb_list c (Vs @ [x])"
    using Vs x by auto
  finally show ?case by auto
qed simp

lemma lincomb_list_index:
  assumes i: "i < n"
  shows "set Xs \<subseteq> carrier_vec n \<Longrightarrow>
         lincomb_list c Xs $ i = sum (\<lambda> j. c j * (Xs ! j) $ i) {0..<length Xs}"
proof (induction Xs rule: rev_induct)
  case (snoc x Xs)
  hence x: "x \<in> carrier_vec n" and Xs: "set Xs \<subseteq> carrier_vec n" by auto
  hence "lincomb_list c (Xs @ [x]) = lincomb_list c Xs + c (length Xs) \<cdot>\<^sub>v x" by auto
  also have "\<dots> $ i = lincomb_list c Xs $ i + (c (length Xs) \<cdot>\<^sub>v x) $ i"
    using i index_add_vec(1) x by simp
  also have "(c (length Xs) \<cdot>\<^sub>v x) $ i = c (length Xs) * x $ i" using i x by simp
  also have "x $ i= (Xs @ [x]) ! (length Xs) $ i" by simp
  also have "lincomb_list c Xs $ i = (\<Sum>j = 0..<length Xs. c j * Xs ! j $ i)"
    by (rule snoc.IH[OF Xs])
  also have "\<dots> =  (\<Sum>j = 0..<length Xs. c j * (Xs @ [x]) ! j $ i)"
    by (rule R.finsum_restrict, force, rule restrict_ext, auto simp: append_Cons_nth_left)
  finally show ?case
    using sum.atLeast0_lessThan_Suc[of "\<lambda> j. c j * (Xs @ [x]) ! j $ i" "length Xs"]
    by fastforce
qed (simp add: i)

end
end