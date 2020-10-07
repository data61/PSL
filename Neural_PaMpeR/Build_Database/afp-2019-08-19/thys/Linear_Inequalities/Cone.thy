section \<open>Cones\<close>

text \<open>We define the notions like cone, polyhedral cone, etc. and prove some basic facts about them.\<close>

theory Cone
  imports
    Basis_Extension
    Missing_VS_Connect
    Integral_Bounded_Vectors
begin

context gram_schmidt
begin

definition "nonneg_lincomb c Vs b = (lincomb c Vs = b \<and> c ` Vs \<subseteq> {x. x \<ge> 0})"
definition "nonneg_lincomb_list c Vs b = (lincomb_list c Vs = b \<and> (\<forall> i < length Vs. c i \<ge> 0))"

definition finite_cone :: "'a vec set \<Rightarrow> 'a vec set" where
  "finite_cone Vs = ({ b. \<exists> c. nonneg_lincomb c (if finite Vs then Vs else {}) b})"

definition cone :: "'a vec set \<Rightarrow> 'a vec set" where
  "cone Vs = ({ x. \<exists> Ws. finite Ws \<and> Ws \<subseteq> Vs \<and> x \<in> finite_cone Ws})"

definition cone_list :: "'a vec list \<Rightarrow> 'a vec set" where
  "cone_list Vs = {b. \<exists>c. nonneg_lincomb_list c Vs b}"

lemma finite_cone_iff_cone_list: assumes Vs: "Vs \<subseteq> carrier_vec n"
  and id: "Vs = set Vsl"
shows "finite_cone Vs = cone_list Vsl"
proof -
  have fin: "finite Vs" unfolding id by auto
  from Vs id have Vsl: "set Vsl \<subseteq> carrier_vec n" by auto
  {
    fix c b
    assume b: "lincomb c Vs = b" and c: "c ` Vs \<subseteq> {x. x \<ge> 0}"
    from lincomb_as_lincomb_list[OF Vsl, of c]
    have b: "lincomb_list (\<lambda>i. if \<exists>j<i. Vsl ! i = Vsl ! j then 0 else c (Vsl ! i)) Vsl = b"
      unfolding b[symmetric] id by simp
    have "\<exists> c. nonneg_lincomb_list c Vsl b"
      unfolding nonneg_lincomb_list_def
      apply (intro exI conjI, rule b)
      by (insert c, auto simp: set_conv_nth id)
  }
  moreover
  {
    fix c b
    assume b: "lincomb_list c Vsl = b" and c: "(\<forall> i < length Vsl. c i \<ge> 0)"
    have "nonneg_lincomb (mk_coeff Vsl c) Vs b"
      unfolding b[symmetric] nonneg_lincomb_def
      apply (subst lincomb_list_as_lincomb[OF Vsl])
      by (insert c, auto simp: id mk_coeff_def intro!: sum_list_nonneg)
    hence "\<exists> c. nonneg_lincomb c Vs b" by blast
  }
  ultimately show ?thesis unfolding finite_cone_def cone_list_def
      nonneg_lincomb_def nonneg_lincomb_list_def using fin by auto
qed

lemma cone_alt_def: assumes Vs: "Vs \<subseteq> carrier_vec n"
  shows "cone Vs = ({ x. \<exists> Ws. set Ws \<subseteq> Vs \<and> x \<in> cone_list Ws})"
  unfolding cone_def
proof (intro Collect_cong iffI)
  fix x
  assume "\<exists>Ws. finite Ws \<and> Ws \<subseteq> Vs \<and> x \<in> finite_cone Ws"
  then obtain Ws where *: "finite Ws" "Ws \<subseteq> Vs" "x \<in> finite_cone Ws" by auto
  from finite_list[OF *(1)] obtain Wsl where id: "Ws = set Wsl" by auto
  from finite_cone_iff_cone_list[OF _ this] *(2-3) Vs
  have "x \<in> cone_list Wsl" by auto
  with *(2) id show "\<exists>Wsl. set Wsl \<subseteq> Vs \<and> x \<in> cone_list Wsl" by blast
next
  fix x
  assume "\<exists>Wsl. set Wsl \<subseteq> Vs \<and> x \<in> cone_list Wsl"
  then obtain Wsl where "set Wsl \<subseteq> Vs" "x \<in> cone_list Wsl" by auto
  thus "\<exists>Ws. finite Ws \<and> Ws \<subseteq> Vs \<and> x \<in> finite_cone Ws" using Vs
    by (intro exI[of _ "set Wsl"], subst finite_cone_iff_cone_list, auto)
qed

lemma cone_mono: "Vs \<subseteq> Ws \<Longrightarrow> cone Vs \<subseteq> cone Ws"
  unfolding cone_def by blast

lemma finite_cone_mono: assumes fin: "finite Ws"
  and Ws: "Ws \<subseteq> carrier_vec n"
  and sub: "Vs \<subseteq> Ws"
shows "finite_cone Vs \<subseteq> finite_cone Ws"
proof
  fix b
  assume "b \<in> finite_cone Vs"
  then obtain c where b: "b = lincomb c Vs" and c: "c ` Vs \<subseteq> {x. x \<ge> 0}"
    unfolding finite_cone_def nonneg_lincomb_def using finite_subset[OF sub fin] by auto
  define d where "d = (\<lambda> v. if v \<in> Vs then c v else 0)"
  from c have d: "d ` Ws \<subseteq> {x. x \<ge> 0}" unfolding d_def by auto
  have "lincomb d Ws = lincomb d (Ws - Vs) + lincomb d Vs"
    by (rule lincomb_vec_diff_add[OF Ws sub fin], auto)
  also have "lincomb d Vs = lincomb c Vs"
    by (rule lincomb_cong, insert Ws sub, auto simp: d_def)
  also have "lincomb d (Ws - Vs) = 0\<^sub>v n"
    by (rule lincomb_zero, insert Ws sub, auto simp: d_def)
  also have "0\<^sub>v n + lincomb c Vs = lincomb c Vs" using Ws sub by auto
  also have "\<dots> = b" unfolding b by simp
  finally
  have "b = lincomb d Ws" by auto
  then show "b \<in> finite_cone Ws" using d fin
    unfolding finite_cone_def nonneg_lincomb_def by auto
qed

lemma finite_cone_carrier: "A \<subseteq> carrier_vec n \<Longrightarrow> finite_cone A \<subseteq> carrier_vec n"
  unfolding finite_cone_def nonneg_lincomb_def by auto

lemma cone_carrier: "A \<subseteq> carrier_vec n \<Longrightarrow> cone A \<subseteq> carrier_vec n"
  using finite_cone_carrier unfolding cone_def by blast

lemma cone_iff_finite_cone: assumes A: "A \<subseteq> carrier_vec n"
  and fin: "finite A"
shows "cone A = finite_cone A"
proof
  show "finite_cone A \<subseteq> cone A" unfolding cone_def using fin by auto
  show "cone A \<subseteq> finite_cone A" unfolding cone_def using fin finite_cone_mono[OF fin A] by auto
qed

lemma set_in_finite_cone:
  assumes Vs: "Vs \<subseteq> carrier_vec n"
    and fin: "finite Vs"
  shows "Vs \<subseteq> finite_cone Vs"
proof
  fix x
  assume x: "x \<in> Vs"
  show "x \<in> finite_cone Vs" unfolding finite_cone_def
  proof
    let ?c = "\<lambda> y. if x = y then 1 else 0 :: 'a"
    have Vsx: "Vs - {x} \<subseteq> carrier_vec n" using Vs by auto
    have "lincomb ?c Vs = x + lincomb ?c (Vs - {x})"
      using lincomb_del2 x Vs fin by auto
    also have "lincomb ?c (Vs - {x}) = 0\<^sub>v n" using lincomb_zero Vsx by auto
    also have "x + 0\<^sub>v n = x " using M.r_zero Vs x by auto
    finally have "lincomb ?c Vs = x" by auto
    moreover have "?c ` Vs \<subseteq> {z. z \<ge> 0}" by auto
    ultimately show "\<exists>c. nonneg_lincomb c (if finite Vs then Vs else {}) x"
      unfolding nonneg_lincomb_def
      using fin by auto
  qed
qed

lemma set_in_cone:
  assumes Vs: "Vs \<subseteq> carrier_vec n"
  shows "Vs \<subseteq> cone Vs"
proof
  fix x
  assume x: "x \<in> Vs"
  show "x \<in> cone Vs" unfolding cone_def
  proof (intro CollectI exI)
    have "x \<in> carrier_vec n" using Vs x by auto
    then have "x \<in> finite_cone {x}" using set_in_finite_cone by auto
    then show "finite {x} \<and> {x} \<subseteq> Vs \<and> x \<in> finite_cone {x}" using x by auto
  qed
qed

lemma zero_in_finite_cone:
  assumes Vs: "Vs \<subseteq> carrier_vec n"
  shows "0\<^sub>v n \<in> finite_cone Vs"
proof -
  let ?Vs = "(if finite Vs then Vs else {})"
  have "lincomb (\<lambda> x. 0 :: 'a) ?Vs = 0\<^sub>v n" using lincomb_zero Vs by auto
  moreover have "(\<lambda> x. 0 :: 'a) ` ?Vs \<subseteq> {y. y \<ge> 0}" by auto
  ultimately show ?thesis unfolding finite_cone_def nonneg_lincomb_def by blast
qed

lemma lincomb_in_finite_cone:
  assumes "x = lincomb l W"
    and "finite W"
    and "\<forall>i \<in> W . l i \<ge> 0"
    and "W \<subseteq> carrier_vec n"
  shows "x \<in> finite_cone W"
  using cone_iff_finite_cone assms unfolding finite_cone_def nonneg_lincomb_def by auto

lemma lincomb_in_cone:
  assumes "x = lincomb l W"
    and "finite W"
    and "\<forall>i \<in> W . l i \<ge> 0"
    and "W \<subseteq> carrier_vec n"
  shows "x \<in> cone W"
  using cone_iff_finite_cone assms unfolding finite_cone_def nonneg_lincomb_def by auto

lemma zero_in_cone: "0\<^sub>v n \<in> cone Vs"
proof -
  have "finite {}" by auto
  moreover have "{} \<subseteq> cone Vs" by auto
  moreover have "0\<^sub>v n \<in> finite_cone {}" using zero_in_finite_cone by auto
  ultimately show ?thesis unfolding cone_def by blast
qed

lemma cone_smult:
  assumes a: "a \<ge> 0"
    and Vs: "Vs \<subseteq> carrier_vec n"
    and x: "x \<in> cone Vs"
  shows "a \<cdot>\<^sub>v x \<in> cone Vs"
proof -
  from x Vs obtain Ws c where Ws: "Ws \<subseteq> Vs" and fin: "finite Ws" and
    "nonneg_lincomb c Ws x"
    unfolding cone_def finite_cone_def by auto
  then have "nonneg_lincomb (\<lambda> w. a * c w) Ws (a \<cdot>\<^sub>v x)"
    unfolding nonneg_lincomb_def using a lincomb_distrib Vs by auto
  then show ?thesis using Ws fin unfolding cone_def finite_cone_def by auto
qed

lemma finite_cone_empty[simp]: "finite_cone {} = {0\<^sub>v n}"
  by (auto simp: finite_cone_def nonneg_lincomb_def)

lemma cone_empty[simp]: "cone {} = {0\<^sub>v n}"
  unfolding cone_def by simp


lemma cone_elem_sum:
  assumes Vs: "Vs \<subseteq> carrier_vec n"
    and x: "x \<in> cone Vs"
    and y: "y \<in> cone Vs"
  shows "x + y \<in> cone Vs"
proof -
  obtain Xs where Xs: "Xs \<subseteq> Vs" and fin_Xs: "finite Xs"
    and Xs_cone: "x \<in> finite_cone Xs"
    using Vs x unfolding cone_def by auto
  obtain Ys where Ys: "Ys \<subseteq> Vs" and fin_Ys: "finite Ys"
    and Ys_cone: "y \<in> finite_cone Ys"
    using Vs y unfolding cone_def
    by auto
  have "x \<in> finite_cone (Xs \<union> Ys)" and "y \<in> finite_cone (Xs \<union> Ys)"
    using finite_cone_mono fin_Xs fin_Ys Xs Ys Vs Xs_cone Ys_cone
    by (blast, blast)
  then obtain cx cy where "nonneg_lincomb cx (Xs \<union> Ys) x"
    and "nonneg_lincomb cy (Xs \<union> Ys) y"
    unfolding finite_cone_def using fin_Xs fin_Ys by auto
  hence "nonneg_lincomb (\<lambda> v. cx v + cy v) (Xs \<union> Ys) (x + y)"
    unfolding nonneg_lincomb_def
    using lincomb_sum[of "Xs \<union> Ys" cx cy] fin_Xs fin_Ys Xs Ys Vs
    by fastforce
  hence "x + y \<in> finite_cone (Xs \<union> Ys)"
    unfolding finite_cone_def using fin_Xs fin_Ys by auto
  thus ?thesis unfolding cone_def using fin_Xs fin_Ys Xs Ys by auto
qed

lemma cone_cone:
  assumes Vs: "Vs \<subseteq> carrier_vec n"
  shows "cone (cone Vs) = cone Vs"
proof
  show "cone Vs \<subseteq> cone (cone Vs)"
    by (rule set_in_cone[OF cone_carrier[OF Vs]])
next
  show "cone (cone Vs) \<subseteq> cone Vs"
  proof
    fix x
    assume x: "x \<in> cone (cone Vs)"
    then obtain Ws c where Ws: "set Ws \<subseteq> cone Vs"
      and c: "nonneg_lincomb_list c Ws x"
      using cone_alt_def Vs cone_carrier unfolding cone_list_def by auto

    have "set Ws \<subseteq> cone Vs \<Longrightarrow> nonneg_lincomb_list c Ws x \<Longrightarrow> x \<in> cone Vs"
    proof (induction Ws arbitrary: x c)
      case Nil
      hence "x = 0\<^sub>v n" unfolding nonneg_lincomb_list_def by auto
      thus "x \<in> cone Vs" using zero_in_cone by auto
    next
      case (Cons a Ws)
      have "a \<in> cone Vs" using Cons.prems(1) by auto
      moreover have "c 0 \<ge> 0"
        using Cons.prems(2) unfolding nonneg_lincomb_list_def by fastforce
      ultimately have "c 0 \<cdot>\<^sub>v a \<in> cone Vs" using cone_smult Vs by auto
      moreover have "lincomb_list (c \<circ> Suc) Ws \<in> cone Vs"
        using Cons unfolding nonneg_lincomb_list_def by fastforce
      moreover have "x = c 0 \<cdot>\<^sub>v a + lincomb_list (c \<circ> Suc) Ws"
        using Cons.prems(2) unfolding nonneg_lincomb_list_def
        by auto
      ultimately show "x \<in> cone Vs" using cone_elem_sum Vs by auto
    qed

    thus "x \<in> cone Vs" using Ws c by auto
  qed
qed

lemma cone_smult_basis:
  assumes Vs: "Vs \<subseteq> carrier_vec n"
    and l: "l ` Vs \<subseteq> {x. x > 0}"
  shows "cone {l v \<cdot>\<^sub>v v | v . v \<in> Vs} = cone Vs"
proof
  have "{l v \<cdot>\<^sub>v v |v. v \<in> Vs} \<subseteq> cone Vs"
  proof
    fix x
    assume "x \<in> {l v \<cdot>\<^sub>v v | v. v \<in> Vs}"
    then obtain v where "v \<in> Vs" and "x = l v \<cdot>\<^sub>v v" by auto
    thus "x \<in> cone Vs" using
        set_in_cone[OF Vs] cone_smult[OF _ Vs, of "l v" v] l by fastforce
  qed
  thus "cone {l v \<cdot>\<^sub>v v | v. v \<in> Vs} \<subseteq> cone Vs"
    using cone_mono cone_cone[OF Vs] by blast
next
  have lVs: "{l v \<cdot>\<^sub>v v | v. v \<in> Vs} \<subseteq> carrier_vec n" using Vs by auto
  have "Vs \<subseteq> cone {l v \<cdot>\<^sub>v v | v. v \<in> Vs}"
  proof
    fix v assume v: "v \<in> Vs"
    hence "l v \<cdot>\<^sub>v v \<in> cone {l v \<cdot>\<^sub>v v | v. v \<in> Vs}" using set_in_cone[OF lVs] by auto
    moreover have "1 / l v > 0" using l v by auto
    ultimately have "(1 / l v) \<cdot>\<^sub>v (l v \<cdot>\<^sub>v v) \<in> cone {l v \<cdot>\<^sub>v v | v. v \<in> Vs}"
      using cone_smult[OF _ lVs] by auto
    also have "(1 / l v) \<cdot>\<^sub>v (l v \<cdot>\<^sub>v v) = v" using l v
      by(auto simp add: smult_smult_assoc)
    finally show "v \<in> cone {l v \<cdot>\<^sub>v v | v. v \<in> Vs}" by auto
  qed
  thus "cone Vs \<subseteq> cone {l v \<cdot>\<^sub>v v | v. v \<in> Vs}"
    using cone_mono cone_cone[OF lVs] by blast
qed

lemma cone_add_cone:
  assumes C: "C \<subseteq> carrier_vec n"
  shows "cone C + cone C = cone C"
proof
  note CC = cone_carrier[OF C]
  have "cone C = cone C + {0\<^sub>v n}" by (subst add_0_right_vecset[OF CC], simp)
  also have "\<dots> \<subseteq> cone C + cone C"
    by (rule set_plus_mono2, insert zero_in_cone, auto)
  finally show "cone C \<subseteq> cone C + cone C" by auto
  from cone_elem_sum[OF C]
  show "cone C + cone C \<subseteq> cone C"
    by (auto elim!: set_plus_elim)
qed

lemma orthogonal_cone:
  assumes X: "X \<subseteq> carrier_vec n"
    and W: "W \<subseteq> carrier_vec n"
    and finX: "finite X"
    and spanLW: "span (set Ls \<union> W) = carrier_vec n"
    and ortho: "\<And> w x. w \<in> W \<Longrightarrow> x \<in> set Ls \<Longrightarrow> w \<bullet> x = 0"
    and WWs: "W = set Ws"
    and spanL: "span (set Ls) = span X"
    and LX: "set Ls \<subseteq> X"
    and lin_Ls_Bs: "lin_indpt_list (Ls @ Bs)"
    and len_Ls_Bs: "length (Ls @ Bs) = n"
  shows "cone (X \<union> set Bs) \<inter> {x \<in> carrier_vec n. \<forall>w\<in>W. w \<bullet> x = 0} = cone X"
    "\<And> x. \<forall>w\<in>W. w \<bullet> x = 0 \<Longrightarrow> Z \<subseteq> X \<Longrightarrow> B \<subseteq> set Bs \<Longrightarrow> x = lincomb c (Z \<union> B)
    \<Longrightarrow> x = lincomb c (Z - B)"
proof -
  from WWs have finW: "finite W" by auto
  define Y where "Y = X \<union> set Bs"
  from lin_Ls_Bs[unfolded lin_indpt_list_def] have
    Ls: "set Ls \<subseteq> carrier_vec n" and
    Bs: "set Bs \<subseteq> carrier_vec n" and
    distLsBs: "distinct (Ls @ Bs)" and
    lin: "lin_indpt (set (Ls @ Bs))"  by auto
  have LW: "set Ls \<inter> W = {}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain x where xX: "x \<in> set Ls" and xW: "x \<in> W" by auto
    from ortho[OF xW xX] have "x \<bullet> x = 0" by auto
    hence "sq_norm x = 0" by (auto simp: sq_norm_vec_as_cscalar_prod)
    with vs_zero_lin_dep[OF _ lin] xX Ls Bs show False by auto
  qed
  have Y: "Y \<subseteq> carrier_vec n" using X Bs unfolding Y_def by auto
  have CLB: "carrier_vec n = span (set (Ls @ Bs))"
    using lin_Ls_Bs len_Ls_Bs lin_indpt_list_length_eq_n by blast
  also have "\<dots> \<subseteq> span Y"
    by (rule span_is_monotone, insert LX, auto simp: Y_def)
  finally have span: "span Y = carrier_vec n" using Y by auto
  have finY: "finite Y" using finX finW unfolding Y_def by auto
  {
    fix x Z B d
    assume xX: "\<forall>w\<in>W. w \<bullet> x = 0" and ZX: "Z \<subseteq> X" and B: "B \<subseteq> set Bs" and
      xd: "x = lincomb d (Z \<union> B)"
    from ZX B X Bs have ZB: "Z \<union> B \<subseteq> carrier_vec n" by auto
    with xd have x: "x \<in> carrier_vec n" by auto
    from xX W have w0: "w \<in> W \<Longrightarrow> w \<bullet> x = 0" for w by auto
    from finite_in_span[OF _ _ x[folded spanLW]] Ls X W finW finX
    obtain c where xc: "x = lincomb c (set Ls \<union> W)" by auto
    have "x = lincomb c (set Ls \<union> W)" unfolding xc by auto
    also have "\<dots> = lincomb c (set Ls) + lincomb c W"
      by (rule lincomb_union, insert X LX W LW finW, auto)
    finally have xsum: "x = lincomb c (set Ls) + lincomb c W" .
    {
      fix w
      assume wW: "w \<in> W"
      with W have w: "w \<in> carrier_vec n" by auto
      from w0[OF wW, unfolded xsum]
      have "0 = w \<bullet> (lincomb c (set Ls) + lincomb c W)" by simp
      also have "\<dots> = w \<bullet> lincomb c (set Ls) + w \<bullet> lincomb c W"
        by (rule scalar_prod_add_distrib[OF w], insert Ls W, auto)
      also have "w \<bullet> lincomb c (set Ls) = 0" using ortho[OF wW]
        by (subst lincomb_scalar_prod_right[OF Ls w], auto)
      finally have "w \<bullet> lincomb c W = 0" by simp
    }
    hence "lincomb c W \<bullet> lincomb c W = 0" using W
      by (subst lincomb_scalar_prod_left, auto)
    hence "sq_norm (lincomb c W) = 0"
      by (auto simp: sq_norm_vec_as_cscalar_prod)
    hence 0: "lincomb c W = 0\<^sub>v n" using lincomb_closed[OF W, of c] by simp
    have xc: "x = lincomb c (set Ls)" unfolding xsum 0 using Ls by auto
    hence xL: "x \<in> span (set Ls)" by auto
    let ?X = "Z - B"
    have "lincomb d ?X \<in> span X" using finite_subset[OF _ finX, of ?X] X ZX by auto
    from finite_in_span[OF finite_set Ls this[folded spanL]]
    obtain e where ed: "lincomb e (set Ls) = lincomb d ?X" by auto
    from B finite_subset[OF B] have finB: "finite B" by auto
    from B Bs have BC: "B \<subseteq> carrier_vec n" by auto
    define f where "f =
      (\<lambda> x. if x \<in> set Bs then if x \<in> B then d x else 0 else if x \<in> set Ls then e x else undefined)"
    have "x = lincomb d (?X \<union> B)" unfolding xd by auto
    also have "\<dots> = lincomb d ?X + lincomb d B"
      by (rule lincomb_union[OF _ _ _ finite_subset[OF _ finX]], insert ZX X finB B Bs, auto)
    finally have xd: "x = lincomb d ?X + lincomb d B" .
    also have "\<dots> = lincomb e (set Ls) + lincomb d B" unfolding ed by auto
    also have "lincomb e (set Ls) = lincomb f (set Ls)"
      by (rule lincomb_cong[OF _ Ls], insert distLsBs, auto simp: f_def)
    also have "lincomb d B = lincomb f B"
      by (rule lincomb_cong[OF _ BC], insert B, auto simp: f_def)
    also have "lincomb f B = lincomb f (B \<union> (set Bs - B))"
      by (subst lincomb_clean, insert finB Bs B, auto simp: f_def)
    also have "B \<union> (set Bs - B) = set Bs" using B by auto
    finally have "x = lincomb f (set Ls) + lincomb f (set Bs)" by auto
    also have "lincomb f (set Ls) + lincomb f (set Bs) = lincomb f (set (Ls @ Bs))"
      by (subst lincomb_union[symmetric], insert Ls distLsBs Bs, auto)
    finally have "x = lincomb f (set (Ls @ Bs))" .
    hence f: "f \<in> set (Ls @ Bs) \<rightarrow>\<^sub>E UNIV \<and> lincomb f (set (Ls @ Bs)) = x"
      by (auto simp: f_def split: if_splits)
    from finite_in_span[OF finite_set Ls xL] obtain g where
      xg: "x = lincomb g (set Ls)" by auto
    define h where "h = (\<lambda> x. if x \<in> set Bs then 0 else if x \<in> set Ls then g x else undefined)"
    have "x = lincomb h (set Ls)" unfolding xg
      by (rule lincomb_cong[OF _ Ls], insert distLsBs, auto simp: h_def)
    also have "\<dots> = lincomb h (set Ls) + 0\<^sub>v n" using Ls by auto
    also have "0\<^sub>v n = lincomb h (set Bs)"
      by (rule lincomb_zero[symmetric, OF Bs], auto simp: h_def)
    also have "lincomb h (set Ls) + lincomb h (set Bs) = lincomb h (set (Ls @ Bs))"
      by (subst lincomb_union[symmetric], insert Ls Bs distLsBs, auto)
    finally have "x = lincomb h (set (Ls @ Bs))" .
    hence h: "h \<in> set (Ls @ Bs) \<rightarrow>\<^sub>E UNIV \<and> lincomb h (set (Ls @ Bs)) = x"
      by (auto simp: h_def split: if_splits)
    have basis: "basis (set (Ls @ Bs))" using lin_Ls_Bs[unfolded lin_indpt_list_def] len_Ls_Bs
      using CLB basis_def by blast
    from Ls Bs have "set (Ls @ Bs) \<subseteq> carrier_vec n" by auto
    from basis[unfolded basis_criterion[OF finite_set this], rule_format, OF x] f h
    have fh: "f = h" by auto
    hence "\<And> x. x \<in> set Bs \<Longrightarrow> f x = 0" unfolding h_def by auto
    hence "\<And> x. x \<in> B \<Longrightarrow> d x = 0" unfolding f_def using B by force
    thus "x = lincomb d ?X" unfolding xd
      by (subst (2) lincomb_zero, insert BC ZB X, auto intro!: M.r_zero)
  } note main = this
  have "cone Y \<inter> {x \<in> carrier_vec n. \<forall>w\<in>W. w \<bullet> x = 0} = cone X" (is "?I = _")
  proof
    {
      fix x
      assume xX: "x \<in> cone X"
      with cone_carrier[OF X] have x: "x \<in> carrier_vec n" by auto
      have "X \<subseteq> Y" unfolding Y_def by auto
      from cone_mono[OF this] xX have xY: "x \<in> cone Y" by auto
      from cone_iff_finite_cone[OF X finX] xX have "x \<in> finite_cone X" by auto
      from this[unfolded finite_cone_def nonneg_lincomb_def] finX obtain c
        where "x = lincomb c X" by auto
      with finX X have "x \<in> span X" by auto
      with spanL have "x \<in> span (set Ls)" by auto
      from finite_in_span[OF _ Ls this] obtain c where
        xc: "x = lincomb c (set Ls)" by auto
      {
        fix w
        assume wW: "w \<in> W"
        hence w: "w \<in> carrier_vec n" using W by auto
        have "w \<bullet> x = 0" unfolding xc using ortho[OF wW]
          by (subst lincomb_scalar_prod_right[OF Ls w], auto)
      }
      with xY x have "x \<in> ?I" by blast
    }
    thus "cone X \<subseteq> ?I" by blast
    {
      fix x
      let ?X = "X - set Bs"
      assume "x \<in> ?I"
      with cone_carrier[OF Y] cone_iff_finite_cone[OF Y finY]
      have xY: "x \<in> finite_cone Y" and x: "x \<in> carrier_vec n"
        and w0: "\<And> w. w \<in> W \<Longrightarrow> w \<bullet> x = 0" by auto
      from xY[unfolded finite_cone_def nonneg_lincomb_def] finY obtain d
        where xd: "x = lincomb d Y" and nonneg: "d ` Y \<subseteq> Collect ((\<le>) 0)" by auto
      from main[OF _ _ _ xd[unfolded Y_def]] w0
      have "x = lincomb d ?X" by auto
      hence "nonneg_lincomb d ?X x" unfolding nonneg_lincomb_def
        using nonneg[unfolded Y_def] by auto
      hence "x \<in> finite_cone ?X" using finX
        unfolding finite_cone_def by auto
      hence "x \<in> cone X" using finite_subset[OF _ finX, of ?X] unfolding cone_def by blast
    }
    then show "?I \<subseteq> cone X" by auto
  qed
  thus "cone (X \<union> set Bs) \<inter> {x \<in> carrier_vec n. \<forall>w\<in>W. w \<bullet> x = 0} = cone X" unfolding Y_def .
qed

definition "polyhedral_cone (A :: 'a mat) = { x . x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> 0\<^sub>v (dim_row A)}"

lemma polyhedral_cone_carrier: assumes "A \<in> carrier_mat nr n"
  shows "polyhedral_cone A \<subseteq> carrier_vec n"
  using assms unfolding polyhedral_cone_def by auto

lemma cone_in_polyhedral_cone:
  assumes CA: "C \<subseteq> polyhedral_cone A"
    and A: "A \<in> carrier_mat nr n"
  shows "cone C \<subseteq> polyhedral_cone A"
proof
  interpret nr: gram_schmidt nr "TYPE ('a)".
  from polyhedral_cone_carrier[OF A] assms(1)
  have C: "C \<subseteq> carrier_vec n" by auto
  fix x
  assume x: "x \<in> cone C"
  then have xn: "x \<in> carrier_vec n"
    using cone_carrier[OF C] by auto
  from x[unfolded cone_alt_def[OF C] cone_list_def nonneg_lincomb_list_def]
  obtain ll Ds where l0: "lincomb_list ll Ds = x" and l1: "\<forall>i<length Ds. 0 \<le> ll i"
    and DsC: "set Ds \<subseteq> C"
    by auto
  from DsC C have Ds: "set Ds \<subseteq> carrier_vec n" by auto

  have "A *\<^sub>v x = A *\<^sub>v (lincomb_list ll Ds)" using l0 by auto
  also have "\<dots> = nr.lincomb_list ll (map (\<lambda> d. A *\<^sub>v d) Ds)"
  proof -
    have one: " \<forall>w\<in>set Ds. dim_vec w = n" using DsC C by auto
    have two: "\<forall>w\<in>set (map ((*\<^sub>v) A) Ds). dim_vec w = nr" using A DsC C by auto
    show "A *\<^sub>v lincomb_list ll Ds = nr.lincomb_list ll (map ((*\<^sub>v) A) Ds)"
      unfolding lincomb_list_as_mat_mult[OF one] nr.lincomb_list_as_mat_mult[OF two] length_map
    proof (subst assoc_mult_mat_vec[symmetric, OF A], force+, rule arg_cong[of _ _ "\<lambda> x. x *\<^sub>v _"])
      show "A * mat_of_cols n Ds = mat_of_cols nr (map ((*\<^sub>v) A) Ds)"
        unfolding mat_of_cols_def
        by (intro eq_matI, insert A Ds[unfolded set_conv_nth],
            (force intro!: arg_cong[of _ _ "\<lambda> x. row A _ \<bullet> x"])+)
    qed
  qed
  also have "\<dots> \<le> 0\<^sub>v nr"
  proof (intro lesseq_vecI[of _ nr])
    have *: "set (map ((*\<^sub>v) A) Ds) \<subseteq> carrier_vec nr" using A Ds by auto
    show Carr: "nr.lincomb_list ll (map ((*\<^sub>v) A) Ds) \<in> carrier_vec nr"
      by (intro nr.lincomb_list_carrier[OF *])
    fix i
    assume i: "i < nr"
    from CA[unfolded polyhedral_cone_def] A
    have l2: "x \<in> C \<Longrightarrow> A *\<^sub>v x \<le> 0\<^sub>v nr" for x by auto
    show "nr.lincomb_list ll (map ((*\<^sub>v) A) Ds) $ i \<le> 0\<^sub>v nr $ i"
      unfolding subst nr.lincomb_list_index[OF i *] length_map index_zero_vec(1)[OF i]
    proof (intro sum_nonpos mult_nonneg_nonpos)
      fix j
      assume "j \<in> {0..<length Ds}"
      hence j: "j < length Ds" by auto
      from j show "0 \<le> ll j" using l1 by auto
      from j have "Ds ! j \<in> C" using DsC by auto
      from l2[OF this] have l2: "A *\<^sub>v Ds ! j \<le> 0\<^sub>v nr" by auto
      from lesseq_vecD[OF _ this i] i have "(A *\<^sub>v Ds ! j) $ i \<le> 0" by auto
      thus "map ((*\<^sub>v) A) Ds ! j $ i \<le> 0" using j i by auto
    qed
  qed auto
  finally show "x \<in> polyhedral_cone A"
    unfolding polyhedral_cone_def using A xn by auto
qed

lemma bounded_cone_is_zero:
  assumes Ccarr: "C \<subseteq> carrier_vec n" and bnd: "cone C \<subseteq> Bounded_vec bnd"
  shows "cone C = {0\<^sub>v n}"
proof(rule ccontr)
  assume "\<not> ?thesis"
  then obtain v where vC: "v \<in> cone C" and vnz: "v \<noteq> 0\<^sub>v n"
    using zero_in_cone assms by auto
  have vcarr: "v \<in> carrier_vec n" using vC Ccarr cone_carrier by blast
  from vnz vcarr obtain i where i_le_n: "i < dim_vec v" and vinz: "v $ i \<noteq> 0" by force
  define M where "M = (1 / (v $ i) * (bnd + 1))"
  have abs_ge_bnd: "abs (M * (v $ i)) > bnd" unfolding M_def by (simp add: vinz)
  have aMvC: "(abs M) \<cdot>\<^sub>v v \<in> cone C" using cone_smult[OF _ Ccarr vC] abs_ge_bnd by simp
  have "\<not>(abs (abs M * (v $ i)) \<le> bnd)" using abs_ge_bnd by simp
  hence "(abs M) \<cdot>\<^sub>v v \<notin> Bounded_vec bnd" unfolding Bounded_vec_def using i_le_n aMvC by auto
  thus False using aMvC bnd by auto
qed

lemma cone_of_cols: fixes A :: "'a mat" and b :: "'a vec"
  assumes A: "A \<in> carrier_mat n nr" and b: "b \<in> carrier_vec n"
  shows "b \<in> cone (set (cols A)) \<longleftrightarrow> (\<exists> x. x \<ge> 0\<^sub>v nr \<and> A *\<^sub>v x = b)"
proof -
  let ?C = "set (cols A)"
  from A have C: "?C \<subseteq> carrier_vec n" and C': " \<forall>w\<in>set (cols A). dim_vec w = n"
    unfolding cols_def by auto
  have id: "finite ?C = True" "length (cols A) = nr" using A by auto
  have Aid: "mat_of_cols n (cols A) = A" using A unfolding mat_of_cols_def
    by (intro eq_matI, auto)
  show ?thesis
    unfolding cone_iff_finite_cone[OF C finite_set] finite_cone_iff_cone_list[OF C refl]
    unfolding cone_list_def nonneg_lincomb_list_def mem_Collect_eq id
    unfolding lincomb_list_as_mat_mult[OF C'] id Aid
  proof -
    {
      fix x
      assume "x\<ge>0\<^sub>v nr" "A *\<^sub>v x = b"
      hence "\<exists>c. A *\<^sub>v vec nr c = b \<and> (\<forall>i<nr. 0 \<le> c i)" using A b
        by (intro exI[of _ "\<lambda> i. x $ i"], auto simp: less_eq_vec_def intro!: arg_cong[of _ _ "(*\<^sub>v) A"])
    }
    moreover
    {
      fix c
      assume "A *\<^sub>v vec nr c = b" "(\<forall>i<nr. 0 \<le> c i)"
      hence "\<exists> x. x\<ge>0\<^sub>v nr \<and> A *\<^sub>v x = b"
        by (intro exI[of _ "vec nr c"], auto simp: less_eq_vec_def)
    }
    ultimately show "(\<exists>c. A *\<^sub>v vec nr c = b \<and> (\<forall>i<nr. 0 \<le> c i)) = (\<exists>x\<ge>0\<^sub>v nr. A *\<^sub>v x = b)" by blast
  qed
qed

end
end