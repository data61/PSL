(*  Title:       The Embedding Path Order for Lambda-Free Higher-Order Terms
    Author:      Alexander Bentkamp <a.bentkamp at vu.nl>, 2018
    Maintainer:  Alexander Bentkamp <a.bentkamp at vu.nl>
*)

section \<open>The Embedding Path Order for Lambda-Free Higher-Order Terms\<close>

theory Lambda_Free_EPO
imports Chop
abbrevs ">t" = ">\<^sub>t"
  and "\<ge>t" = "\<ge>\<^sub>t"
begin

text \<open>
This theory defines the embedding path order for \<open>\<lambda>\<close>-free
higher-order terms.
\<close>

subsection \<open>Setup\<close>

locale epo = ground_heads "(>\<^sub>s)" arity_sym arity_var
    for
      gt_sym :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix ">\<^sub>s" 50) and
      arity_sym :: "'s \<Rightarrow> enat" and
      arity_var :: "'v \<Rightarrow> enat" +
  fixes
    extf :: "'s \<Rightarrow> (('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool) \<Rightarrow> ('s, 'v) tm list \<Rightarrow> ('s, 'v) tm list \<Rightarrow> bool"
  assumes
    extf_ext_trans_before_irrefl: "ext_trans_before_irrefl (extf f)" and
    extf_ext_compat_list: "ext_compat_list (extf f)"
  assumes extf_ext_compat_snoc: "ext_compat_snoc (extf f)"
  assumes extf_ext_compat_cons: "ext_compat_cons (extf f)"
  assumes extf_ext_snoc: "ext_snoc (extf f)"
  assumes extf_min_empty: "\<not> extf f gt [] ss" (* TODO: seperate definition? *)
begin

lemma extf_ext_trans: "ext_trans (extf f)"
  by (rule ext_trans_before_irrefl.axioms(1)[OF extf_ext_trans_before_irrefl])

lemma extf_ext: "ext (extf f)"
  by (rule ext_trans.axioms(1)[OF extf_ext_trans])

lemmas extf_mono_strong = ext.mono_strong[OF extf_ext]
lemmas extf_mono = ext.mono[OF extf_ext, mono]
lemmas extf_map = ext.map[OF extf_ext]
lemmas extf_trans = ext_trans.trans[OF extf_ext_trans]
lemmas extf_irrefl_from_trans =
  ext_trans_before_irrefl.irrefl_from_trans[OF extf_ext_trans_before_irrefl]
lemmas extf_compat_list = ext_compat_list.compat_list[OF extf_ext_compat_list]

lemmas extf_snoc = ext_snoc.snoc[OF extf_ext_snoc]

lemmas extf_compat_append_right = ext_compat_snoc.compat_append_right[OF extf_ext_compat_snoc]
lemmas extf_compat_append_left = ext_compat_cons.compat_append_left[OF extf_ext_compat_cons]

lemma extf_ext_insert_arg: "extf f gt (xs @ z # ys) (xs @ ys)" 
  using extf_compat_append_left extf_compat_append_right extf_snoc[of f gt Nil z] 
  by fastforce

subsection \<open>Inductive Definitions\<close>

definition
  chkchop :: "(('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool) \<Rightarrow> ('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool"
where
  [simp]: "chkchop gt t s \<longleftrightarrow> is_Hd s \<or> gt t (chop s)"

definition
  chkchop_same :: "(('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool) \<Rightarrow> ('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool"
where
  [simp]: "chkchop_same gt t s \<longleftrightarrow> 
            (if is_Var (head t) 
            then is_Hd t \<or> chkchop gt (chop t) s 
            else chkchop gt t s)"

lemma chkchop_mono[mono]: "gt \<le> gt' \<Longrightarrow> chkchop gt \<le> chkchop gt'"
  using chkchop_def by blast

lemma chkchop_same_mono[mono]: "gt \<le> gt' \<Longrightarrow> chkchop_same gt \<le> chkchop_same gt'"
  using chkchop_same_def by fastforce

inductive gt :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t" 50) where
  gt_chop: "is_App t \<Longrightarrow> chop t >\<^sub>t s \<or> chop t = s \<Longrightarrow> t >\<^sub>t s"
| gt_diff: "head t >\<^sub>h\<^sub>d head s \<Longrightarrow> is_Sym (head s) \<Longrightarrow> chkchop (>\<^sub>t) t s \<Longrightarrow> t >\<^sub>t s"
| gt_same: "head t = head s \<Longrightarrow> chkchop_same (>\<^sub>t) t s \<Longrightarrow>
    (\<forall>f \<in> ground_heads (head t). extf f (>\<^sub>t) (args t) (args s)) \<Longrightarrow> t >\<^sub>t s"

abbreviation ge :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix "\<ge>\<^sub>t" 50) where
  "t \<ge>\<^sub>t s \<equiv> t >\<^sub>t s \<or> t = s"

inductive gt_chop :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_chopI: "is_App t \<Longrightarrow> chop t \<ge>\<^sub>t s \<Longrightarrow> gt_chop t s"

inductive gt_diff :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_diffI: "head t >\<^sub>h\<^sub>d head s \<Longrightarrow> is_Sym (head s) \<Longrightarrow> chkchop (>\<^sub>t) t s \<Longrightarrow> gt_diff t s"

inductive gt_same :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_sameI: "head t = head s \<Longrightarrow> chkchop_same (>\<^sub>t) t s \<Longrightarrow>
    (\<forall>f \<in> ground_heads (head t). extf f (>\<^sub>t) (args t) (args s)) \<Longrightarrow> gt_same t s"

lemma gt_iff_chop_diff_same: "t >\<^sub>t s \<longleftrightarrow> gt_chop t s \<or> gt_diff t s \<or> gt_same t s"
  by (subst gt.simps) (auto simp: gt_chop.simps gt_diff.simps gt_same.simps)

subsection \<open>Transitivity\<close>

lemma t_gt_chop_t: "is_App t \<Longrightarrow> t >\<^sub>t chop t"
  by (simp add: gt_chop)

lemma gt_imp_vars: "t >\<^sub>t s \<Longrightarrow> vars t \<supseteq> vars s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(t, s). size t + size s"
      "\<lambda>(t, s). t >\<^sub>t s \<longrightarrow> vars t \<supseteq> vars s" "(t, s)", simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix t s
  assume
    ih: "\<And>ta sa. size ta + size sa < size t + size s \<Longrightarrow> ta >\<^sub>t sa \<Longrightarrow> vars ta \<supseteq> vars sa" and
    t_gt_s: "t >\<^sub>t s"
  show "vars t \<supseteq> vars s"
    using t_gt_s
  proof cases
    case (gt_chop)
    thus ?thesis
      using ih
      by (metis add_mono_thms_linordered_field(1) le_supI1 order_refl size_chop_lt vars_chop)
  next
    case gt_diff
    show ?thesis 
    proof (cases s)
      case Hd
      thus ?thesis
        using gt_diff(2) 
        by (metis empty_iff hd.collapse(2) hd.simps(18) subsetI tm.sel(1) tm.simps(17))
    next
      case (App s1 s2)
      have "vars (chop s) \<subseteq> vars t" using ih 
        using App chkchop_def local.gt_diff(3) nat_add_left_cancel_less size_chop_lt tm.disc(2) by blast
      thus ?thesis 
        using  App  le_sup_iff local.gt_diff(2) tm.disc(2) vars_chop
        by (metis empty_iff hd.collapse(2) hd.simps(18) subsetI)
    qed
  next
    case gt_same
    thus ?thesis
    proof (cases "head t")
      case (Var x)
      then show ?thesis 
      proof (cases t)
        case (Hd _)
        then show ?thesis using gt_same extf_min_empty[of _ "(>\<^sub>t)" "args s"]
          by simp
      next
        case (App t1 t2)
        then show ?thesis
        proof (cases s)
          case (Hd _)
          then show ?thesis 
            using local.gt_same(1) vars_head_subseteq by fastforce
        next
          case (App s1 s2)
          then have "chop t >\<^sub>t chop s" 
            by (metis Var args.simps(1) chkchop_def chkchop_same_def epo.extf_min_empty 
                epo_axioms gt_hd_def gt_hd_irrefl hd.disc(1) local.gt_same(2) local.gt_same(3) tm.collapse(1) tm.disc(2))
          then have "vars (chop s) \<subseteq> vars (chop t)" using ih[OF _ \<open>chop t >\<^sub>t chop s\<close>] 
            by (metis App add_mono_thms_linordered_field(5) args_Nil_iff_is_Hd extf_min_empty gt_hd_def gt_hd_irrefl local.gt_same(3) size_chop_lt tm.disc(2))
          then show ?thesis using  gt_same(1) vars_chop[of t] vars_chop[of s]
            by (metis App args_Nil_iff_is_Hd extf_min_empty gt_hd_def gt_hd_irrefl le_sup_iff local.gt_same(3) order_refl sup.coboundedI1 tm.disc(2))
        qed
      qed
    next
      case (Sym f)
      then have "chkchop (>\<^sub>t) t s" using gt_same chkchop_same_def by auto
      then show ?thesis 
      proof (cases s)
        case (Hd _)
        then show ?thesis using local.gt_same(1) vars_head_subseteq by force 
      next
        case (App s1 s2)
        then show ?thesis unfolding chkchop_def using vars_chop ih[of t "chop s"] 
          by (metis \<open>chkchop (>\<^sub>t) t s\<close> chkchop_def le_sup_iff local.gt_same(1) 
              nat_add_left_cancel_less size_chop_lt tm.disc(2) vars_head_subseteq)
      qed
    qed
  qed      
qed  

lemma gt_trans: "u >\<^sub>t t \<Longrightarrow> t >\<^sub>t s \<Longrightarrow> u >\<^sub>t s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(u, t, s). {#size u, size t, size s#}"
        "\<lambda>(u, t, s). u >\<^sub>t t \<longrightarrow> t >\<^sub>t s \<longrightarrow> u >\<^sub>t s" "(u, t, s)",
      simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix u t s
  assume
    ih: "\<And>ua ta sa. {#size ua, size ta, size sa#} < {#size u, size t, size s#} \<Longrightarrow>
      ua >\<^sub>t ta \<Longrightarrow> ta >\<^sub>t sa \<Longrightarrow> ua >\<^sub>t sa" and
    u_gt_t: "u >\<^sub>t t" and t_gt_s: "t >\<^sub>t s"

  have u_gt_s_if_ui: "chop u \<ge>\<^sub>t t \<Longrightarrow> u >\<^sub>t s" if ui_in: "is_App u"
    using ih[of "chop u" t s, simplified] t_gt_s gt_chop size_chop_lt ui_in by blast

  show "u >\<^sub>t s"
    using t_gt_s
  proof cases
    case gt_chop
    have u_gt_s_if_chk_u_t: ?thesis if chk_u_t: "chkchop (>\<^sub>t) u t"
      using ih[of u "chop u" s] gt_chop chk_u_t 
      by (metis add_mset_lt_left_lt add_mset_lt_right_lt chkchop_def ih size_chop_lt)
    show ?thesis 
      by (metis args_Nil_iff_is_Hd chkchop_def chkchop_same_def 
          epo.extf_min_empty epo_axioms gt.simps gt_hd_def gt_hd_irrefl
          u_gt_s_if_chk_u_t u_gt_s_if_ui u_gt_t)
  next
    case gt_diff_t_s: gt_diff
    show ?thesis
      using u_gt_t
    proof cases
      case gt_chop
      then show ?thesis 
        using u_gt_s_if_ui by blast
    next
      case gt_diff_u_t: gt_diff
      have "head u >\<^sub>h\<^sub>d head s"
        using gt_diff_u_t(1) gt_diff_t_s(1) by (auto intro: gt_hd_trans)
      thus ?thesis
        using add_mset_lt_left_lt add_mset_lt_right_lt chkchop_def  gt_diff gt_diff_t_s(3) ih size_chop_lt u_gt_t
        by (metis gt_diff_t_s(2))
    next
      case gt_same_u_t: gt_same
      have "head u >\<^sub>h\<^sub>d head s"
        using gt_diff_t_s(1) gt_same_u_t(1) by auto
      thus ?thesis
        using add_mset_lt_left_lt add_mset_lt_right_lt chkchop_def gt_diff gt_diff_t_s(3) ih size_chop_lt u_gt_t
        by (metis gt_diff_t_s(2))
    qed
  next
    case gt_same_t_s: gt_same
    show ?thesis
      using u_gt_t
    proof cases
      case gt_chop
      then show ?thesis 
        using u_gt_s_if_ui by linarith
    next
      case gt_diff_u_t: gt_diff
      have "head u >\<^sub>h\<^sub>d head s"
        using gt_diff_u_t(1) gt_same_t_s(1) by simp
      thus ?thesis
        using add_mset_lt_left_lt add_mset_lt_right_lt chkchop_def gt_diff gt_same_t_s ih size_chop_lt u_gt_t
        by (metis chkchop_same_def gt_diff_u_t(2))
    next
      case gt_same_u_t: gt_same
      have hd_u_s: "head u = head s"
        using gt_same_u_t(1) gt_same_t_s(1) by simp

      let ?S = "set (args u) \<union> set (args t) \<union> set (args s)"

      have gt_trans_args: "\<forall>ua \<in> ?S. \<forall>ta \<in> ?S. \<forall>sa \<in> ?S. ua >\<^sub>t ta \<longrightarrow> ta >\<^sub>t sa \<longrightarrow> ua >\<^sub>t sa"
      proof clarify
        fix sa ta ua
        assume
          ua_in: "ua \<in> ?S" and ta_in: "ta \<in> ?S" and sa_in: "sa \<in> ?S" and
          ua_gt_ta: "ua >\<^sub>t ta" and ta_gt_sa: "ta >\<^sub>t sa"
        show "ua >\<^sub>t sa"
          by (auto intro!: ih[OF Max_lt_imp_lt_mset ua_gt_ta ta_gt_sa])
            (meson ua_in ta_in sa_in Un_iff max.strict_coboundedI1 max.strict_coboundedI2
               size_in_args)+
      qed

      have "\<forall>f \<in> ground_heads (head u). extf f (>\<^sub>t) (args u) (args s)"
      proof (clarify, rule extf_trans[OF _ _ _ gt_trans_args])
        fix f
        assume f_in_grounds: "f \<in> ground_heads (head u)"
        show "extf f (>\<^sub>t) (args u) (args t)"
          using f_in_grounds gt_same_u_t(3) by blast
        show "extf f (>\<^sub>t) (args t) (args s)"
          using f_in_grounds gt_same_t_s(3) unfolding gt_same_u_t(1) by blast
      qed auto
      have "chkchop_same (>\<^sub>t) u s"
      proof (cases "head u")
        case (Var x)
        then show ?thesis
        proof (cases u)
          case (Hd _)
          then show ?thesis 
            using Var by auto
        next
          case (App u1 u2)
          then have "chop u >\<^sub>t chop t" 
            by (metis Var args.simps(1) chkchop_def chkchop_same_def epo.extf_min_empty epo_axioms gt_hd_def gt_hd_irrefl gt_same_t_s(3) gt_same_u_t(2) hd.disc(1) tm.collapse(1) tm.disc(2))
          then show ?thesis
          proof (cases t)
            case (Hd _)
            then show ?thesis 
              using extf_min_empty gt_same_t_s(3) by auto
          next
            case t_App: (App t1 t2)
            then have "is_App s \<Longrightarrow> chop t >\<^sub>t chop s" 
              using gt_same_t_s unfolding chkchop_same_def unfolding chkchop_def using Var hd_u_s by auto
            then have "chkchop (>\<^sub>t) (chop u) s" 
              unfolding chkchop_def using ih[of "chop u" "chop t" "chop s"]
              by (metis App \<open>chop u >\<^sub>t chop t\<close> t_App add_mset_lt_lt_le less_imp_le mset_lt_single_iff size_chop_lt tm.disc(2))
            then show ?thesis unfolding chkchop_same_def 
              using Var by auto
          qed
        qed
      next
        case (Sym f)
        have "chkchop (>\<^sub>t) u s" 
         proof (cases s)
           case (Hd _)
           then show ?thesis 
             by simp
         next
           case (App s1 s2)
           then have "t >\<^sub>t chop s"
             using Sym gt_same_t_s(1) gt_same_t_s(2) hd_u_s by auto
           then have "u >\<^sub>t chop s" using ih[of u t "chop s"] 
             by (metis App add_mset_lt_right_lt mset_lt_single_iff size_chop_lt tm.disc(2) u_gt_t)
           then show ?thesis unfolding chkchop_def
             by blast
         qed
        then show ?thesis
          by (simp add: Sym) 
      qed
      thus ?thesis 
        using \<open>\<forall>f\<in>local.ground_heads (head u). extf f (>\<^sub>t) (args u) (args s)\<close> gt_same hd_u_s by blast
    qed
  qed
qed

subsection \<open>Irreflexivity\<close>

theorem gt_irrefl: "\<not> s >\<^sub>t s"
proof (standard, induct s rule: measure_induct_rule[of size])
  case (less s)
  note ih = this(1) and s_gt_s = this(2)

  show False
    using s_gt_s
  proof cases
    case gt_chop
    then show False using ih[of "chop s"]
      by (metis gt.gt_chop gt_trans size_chop_lt)
  next
    case gt_diff
    thus False
      by (cases "head s") (auto simp: gt_hd_irrefl)
  next
    case gt_same
    note in_grounds = this(3)

    obtain si where si_in_args: "si \<in> set (args s)" and si_gt_si: "si >\<^sub>t si"
      using in_grounds
      by (metis (full_types) all_not_in_conv extf_irrefl_from_trans ground_heads_nonempty gt_trans)
    have "size si < size s"
      by (rule size_in_args[OF si_in_args])
    thus False
      by (rule ih[OF _ si_gt_si])
  qed
qed

lemma gt_antisym: "t >\<^sub>t s \<Longrightarrow> \<not> s >\<^sub>t t"
  using gt_irrefl gt_trans by blast


subsection "Compatibility with Embedding Relation"

(* TODO: move? *)
lemma nth_drop_lemma:
  assumes "length xs = length ys"
and "k \<le> length xs"
and "\<And>i. i < length xs \<longrightarrow> i \<ge> k \<longrightarrow> xs ! i = ys ! i"
shows "drop k xs = drop k ys"
  using assms proof (induct arbitrary:k rule:list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then show ?case proof (cases k)
    case 0
    then have "x # xs =  y # ys" 
      by (metis Cons.hyps(1) Cons.prems(2) leI length_Cons not_less_zero nth_equalityI)
    then show ?thesis 
      by blast
  next
    case (Suc m)
    then have "drop m xs = drop m ys" 
      by (metis Cons.hyps(2) Cons.prems(1) Cons.prems(2) Suc_le_mono Suc_mono length_Cons nth_Cons_Suc)
    then show ?thesis 
      by (simp add: Suc)
  qed
qed

lemma gt_embedding_step_property:
  assumes "t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s"
  shows "t >\<^sub>t s"
  using assms 
  apply(simp only: atomize_imp)
  apply (rule measure_induct_rule[of "\<lambda>(t, s). size t + size s"
      "\<lambda>(t, s). t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s \<longrightarrow> t >\<^sub>t s" "(t, s)", simplified prod.case])
proof(simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix s t :: "('s,'v) tm" 
  assume "t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s" 
    and ih: "\<And>tt ss. size tt + size ss < size t + size s \<Longrightarrow> tt \<rightarrow>\<^sub>e\<^sub>m\<^sub>b ss \<Longrightarrow> tt >\<^sub>t ss"
  have "is_App t" 
    by (metis \<open>t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s\<close> emb_step_at_is_App emb_step_equiv)

  obtain p d where "emb_step_at p d t = s" "position_of t (p @ [d])"
    using \<open>t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s\<close> emb_step_equiv by (metis position_if_emb_step_at)
  define q where q_rep_t: "q = replicate (num_args (fun t)) Left"

  show "t >\<^sub>t s"
  proof (cases "list_all (\<lambda>x. x = Left) p")
    case True
    show ?thesis
    proof (cases d)
      text \<open>Embedding removes an argument i\<close>
      case Left
      define i where "i = num_args t - Suc (length p)"
      then  have " head t = head s" "i < num_args t" "args s = take i (args t) @ drop (Suc i) (args t)"
        using emb_step_at_remove_arg Left True \<open>emb_step_at p d t = s\<close> \<open>position_of t (p @ [d])\<close> 
        by metis+
      have "is_App s \<Longrightarrow> chop t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b chop s" 
      proof (cases "p = q")
        case True
        assume "is_App s"
        show ?thesis 
        proof -          
          have "Suc (num_args (fun s)) = num_args (fun t)" 
            by (metis One_nat_def Suc_num_args True \<open>args s = take i (args t) @ drop (Suc i) (args t)\<close> \<open>is_App s\<close> \<open>is_App t\<close> append_self_conv2 cancel_comm_monoid_add_class.diff_cancel diff_Suc_1 i_def length_drop length_replicate q_rep_t take_eq_Nil)
          have "emb_step_at (replicate (num_args (fun s)) Left) Right (chop t) =
                emb_step_at (replicate (num_args (fun s)) Left) Right t" 
            using merge_emb_step_at[of "replicate (num_args (fun s)) Left" Right Nil Right t, unfolded append_Nil2 opp_simps(1) replicate_append_same]
            by (metis \<open>Suc (num_args (fun s)) = num_args (fun t)\<close> \<open>is_App t\<close> chop_emb_step_at replicate_Suc)
          then have "emb_step_at (replicate (num_args (fun s)) dir.Left) dir.Right (chop t) = chop s" unfolding chop_emb_step_at[OF \<open>is_App s\<close>]
            using merge_emb_step_at[of "replicate (num_args (fun s)) Left" Right Nil Left t, unfolded append_Nil2 opp_simps(1) replicate_append_same]
            by (metis Left True \<open>Suc (num_args (fun s)) = num_args (fun t)\<close> \<open>emb_step_at p d t = s\<close> q_rep_t replicate_Suc)
          then show "chop t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b chop s"
            by (metis \<open>is_App s\<close> \<open>is_App t\<close> \<open>t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s\<close> emb_step_equiv emb_step_size nat_neq_iff size_chop)
        qed
      next
        case False
        assume "is_App s" 
        have p_rep: "p = replicate (length p) Left" 
          by (metis (full_types) \<open>list_all (\<lambda>x. x = Left) p\<close> list_all_iff replicate_length_same)
        have length_p:"length p < num_args t" using no_position_replicate_num_args \<open>position_of t (p @ [d])\<close> 
            replicate_add[of "num_args t" "length p - num_args t" Left]  p_rep q_rep_t
          by (metis Left add_diff_inverse_nat replicate_app_Cons_same replicate_append_same shallower_pos)
        then have "length p \<le> length q" 
          using Suc_num_args \<open>is_App t\<close> q_rep_t by fastforce
        then have "length p < length q"
          using False le_neq_implies_less p_rep q_rep_t by fastforce
        then have "take (Suc (length p)) q = p @ [Left]" 
          by (metis (no_types, lifting) \<open>length p \<le> length q\<close> length_replicate min.orderE nth_replicate p_rep q_rep_t take_Suc_conv_app_nth take_replicate)
        then obtain q' where "q = p @ [Left] @ q'" 
          by (metis append.assoc append_take_drop_id)
        have "Suc (num_args (fun s)) = num_args (fun t)" 
          by (metis (no_types, lifting) Cons_nth_drop_Suc Suc_num_args \<open>args s = take i (args t) @ drop (Suc i) (args t)\<close> \<open>i < num_args t\<close> \<open>is_App s\<close> \<open>is_App t\<close> add_Suc_right append_take_drop_id diff_Suc_1 length_Cons length_append)
        then have "chop s = emb_step_at p dir.Left (chop t)"
          using swap_nested_emb_step_at[of p q' Right Left t] chop_emb_step_at[OF \<open>is_App s\<close>]
            chop_emb_step_at[OF \<open>is_App t\<close>]  
          by (metis (no_types, lifting) Cons_replicate_eq Left \<open>emb_step_at p d t = s\<close> \<open>q = p @ [dir.Left] @ q'\<close> append.assoc append_Cons diff_Suc_1 p_rep q_rep_t replicate_append_same)
        then show "chop t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b chop s" 
          by (metis Left \<open>is_App t\<close> \<open>position_of t (p @ [d])\<close> \<open>q = p @ [dir.Left] @ q'\<close> chop_emb_step_at emb_step_at_if_position pos_emb_step_at_nested q_rep_t)
      qed
      then have "chkchop_same (>\<^sub>t) t s"
      proof (cases "is_Var (head t)")
        case True
        then show ?thesis unfolding chkchop_same_def chkchop_def  using ih[of "chop t" "chop s"] 
           add_less_mono size_chop_lt \<open>is_App s \<Longrightarrow> chop t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b chop s\<close> by metis
      next
        case False
        then show ?thesis unfolding chkchop_same_def chkchop_def 
        using \<open>is_App t\<close> add_less_mono gt_chop ih size_chop_lt 
        \<open>is_App s \<Longrightarrow> chop t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b chop s\<close> by metis
      qed
      have "\<forall>f\<in>local.ground_heads (head t). extf f (>\<^sub>t) (args t) (args s)" 
        using extf_ext_insert_arg[of _ _ "take i (args t)" "args t ! i" "drop (Suc i) (args t)"]
        using \<open>args s = take i (args t) @ drop (Suc i) (args t)\<close> \<open>i < num_args t\<close> id_take_nth_drop by fastforce
      then show ?thesis using gt_same \<open>head t = head s\<close> \<open>chkchop_same (>\<^sub>t) t s\<close> by blast
    next
      text \<open>Embedding chops and might remove arguments from the left\<close>
      case Right
      show ?thesis using emb_step_at_chop
        by (metis Right True \<open>emb_step_at p d t = s\<close> \<open>is_App t\<close> \<open>position_of t (p @ [d])\<close> add_Suc gt_chop ih less_Suc_eq size_chop)
    qed
  next
    text \<open>Embedding operates under one of the arguments\<close>
    case False
    have "num_args t = num_args s" using emb_step_under_args_num_args[OF False] 
      by (metis (no_types) \<open>\<And>t d. num_args (emb_step_at p d t) = num_args t\<close> \<open>emb_step_at p d t = s\<close>)
    then have "is_App s" using \<open>num_args t = num_args s\<close> 
      by (metis args_Nil_iff_is_Hd length_0_conv \<open>is_App t\<close>)

    have q_rep_s: "q = replicate (num_args (fun s)) Left"
      by (metis  q_rep_t \<open>is_App s\<close> \<open>is_App t\<close> \<open>num_args t = num_args s\<close> args.simps(2) butlast_snoc length_butlast tm.collapse(2))

    have "chop t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b chop s"
    proof (cases "take (num_args (fun t)) p = q")
      case True
      have  "num_args (fun t) < length p"
      proof (rule ccontr)
        assume "\<not> num_args (fun t) < length p"
        then have "num_args (fun t) = length p"  "q = p"
          using True q_rep_t by auto
        then show False using False 
          using list_all_length q_rep_t by fastforce
      qed

      have "p ! (num_args (fun t)) = Right" 
      proof (rule ccontr)
        assume "p ! num_args (fun t) \<noteq> Right"
        then have "p ! num_args (fun t) = Left" using dir.exhaust by blast
        then have "take (num_args t) p = replicate (num_args t) Left" using True Suc_num_args[OF \<open>is_App t\<close>] q_rep_t
            take_Suc_conv_app_nth[of "num_args (fun t)" p]
          by (metis \<open>num_args (fun t) < length p\<close> replicate_Suc replicate_append_same)
        then show False 
          by (metis \<open>num_args t = num_args s\<close> \<open>num_args t = num_args s\<close> \<open>position_of t (p @ [d])\<close> 
              append.assoc append_eq_Cons_conv append_take_drop_id no_position_replicate_num_args shallower_pos)
      qed

      then obtain q' where "p = q @ [Right] @ q'"
        by (metis Cons_nth_drop_Suc True \<open>num_args (fun t) < length p\<close> append_Cons append_Nil append_eq_conv_conj length_replicate q_rep_t)
      have "emb_step_at (q @ q') d (chop t) = chop s"
        unfolding chop_emb_step_at[OF \<open>is_App t\<close>] chop_emb_step_at[OF \<open>is_App s\<close>] 
        using swap_nested_emb_step_at[of q q' d Right t, unfolded] \<open>emb_step_at p d t = s\<close> \<open>p = q @ [Right] @ q'\<close> 
        q_rep_t q_rep_s by auto
      moreover have "chop t \<noteq> chop s"
        by (metis \<open>is_App s\<close> \<open>is_App t\<close> \<open>t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b s\<close> emb_step_size nat_less_le size_chop)
      ultimately show "chop t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b chop s" 
        using emb_step_equiv by blast
    next
      case False
      then have takepq: "take (length q) p \<noteq> q" 
        using q_rep_t by auto
      have takeqp: "length p \<le> length q \<Longrightarrow> take (length p) q \<noteq> p"
        using \<open>\<not> list_all (\<lambda>x. x = Left) p\<close>[unfolded list_all_length]
        using diff_diff_cancel take_replicate length_replicate  nth_replicate q_rep_s by metis
      have "chop s = emb_step_at p d (chop t)" 
        using swap_disjunct_emb_step_at[of p q Right d t, OF takeqp takepq, unfolded \<open>emb_step_at p d t = s\<close>] 
        using \<open>is_App s\<close> \<open>is_App t\<close> chop_emb_step_at q_rep_s q_rep_t
        by (simp add: chop_emb_step_at)
      then show ?thesis 
        by (metis False \<open>is_App t\<close> \<open>position_of t (p @ [d])\<close> chop_emb_step_at emb_step_at_if_position length_replicate nat_le_linear pos_emb_step_at_disjunct q_rep_t take_all takeqp)
    qed
    then have gt1:"chkchop_same (>\<^sub>t) t s"  
    proof (cases "head t")
      case (Var _)
      then have "chop t >\<^sub>t chop s" using ih[of "chop t" "chop s"]
        by (meson \<open>chop t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b chop s\<close> \<open>is_App s\<close> \<open>is_App t\<close> add_strict_mono size_chop_lt)
      then show ?thesis  unfolding chkchop_same_def
        by (simp add: Var)
    next
      case (Sym _)
      then show ?thesis unfolding chkchop_same_def using \<open>chop t \<rightarrow>\<^sub>e\<^sub>m\<^sub>b chop s\<close> 
         \<open>is_App t\<close> add_Suc add_Suc_shift chkchop_def gt_trans ih 
         less_Suc_eq size_chop t_gt_chop_t 
        by (metis (no_types, lifting))
    qed
      have gt2:"head t = head s"  
      by (metis emb_step_under_args_head False \<open>emb_step_at p d t = s\<close>) 
    have gt3:"\<forall>f\<in>local.ground_heads (head t). extf f (>\<^sub>t) (args t) (args s)" 
    proof (rule ballI)
      fix f assume "f\<in>local.ground_heads (head t)"
      obtain i where i_def:
        "i < num_args t"
        "args t ! i \<rightarrow>\<^sub>e\<^sub>m\<^sub>b args (emb_step_at p d t) ! i"
        "\<And>j. j < num_args t \<Longrightarrow> i \<noteq> j \<Longrightarrow> args t ! j = args (emb_step_at p d t) ! j"
        using emb_step_under_args_emb_step[of p t d] 
        using False \<open>position_of t (p @ [d])\<close> by blast
      have compat_list1: "args t ! i >\<^sub>t args s ! i" 
        by (metis \<open>num_args t = num_args s\<close> \<open>emb_step_at p d t = s\<close>  add_less_mono i_def(1) i_def(2) ih nth_mem size_in_args)
      have compat_list2: "args t ! i \<noteq> args s ! i" 
        using emb_step_equiv i_def(2) \<open>emb_step_at p d t = s\<close>  by blast
      have argst:"args t = take i (args t) @ args t ! i # drop (Suc i) (args t)" 
        by (simp add: Cons_nth_drop_Suc i_def(1))
      have argss:"args s = take i (args t) @ args (emb_step_at p d t) ! i # drop (Suc i) (args t)"
      proof -
        have "take i (args t) = take i (args s)" 
          apply (rule nth_take_lemma) 
          using \<open>num_args t = num_args s\<close> i_def(1) i_def(3)[unfolded \<open>emb_step_at p d t = s\<close>] by auto
        moreover have "drop (Suc i) (args t) = drop (Suc i) (args s)" 
          apply (rule nth_drop_lemma) 
            apply (simp add: \<open>num_args t = num_args s\<close>)
           apply (simp add: Suc_le_eq i_def(1))
          using Suc_n_not_le_n \<open>emb_step_at p d t = s\<close> i_def(3) by blast
        ultimately show ?thesis
          using \<open>emb_step_at p d t = s\<close> \<open>num_args t = num_args s\<close> i_def(1) id_take_nth_drop by auto
      qed
      show "extf f (>\<^sub>t) (args t) (args s)"
        using  extf_compat_list[of "args t ! i" "args (emb_step_at p d t) ! i" gt f "take i (args t)"  "drop (Suc i) (args t)"] 
        using \<open>emb_step_at p d t = s\<close> argss argst compat_list1 compat_list2 by force
    qed
    show ?thesis using gt_same using gt1 gt2 gt3 by blast
  qed
qed  

lemma gt_embedding_property:
  assumes "t \<unrhd>\<^sub>e\<^sub>m\<^sub>b s" "t \<noteq> s"
  shows "t >\<^sub>t s"
  using assms 
proof (induction)
  case (refl t)
  then show ?case by simp
next
  case (step t u s)
  then show ?case using gt_embedding_step_property gt_trans by blast
qed


subsection \<open>Subterm Property\<close>
  
theorem gt_proper_sub: "proper_sub s t \<Longrightarrow> t >\<^sub>t s" 
  using gt_embedding_property sub_emb by blast

lemma
  gt_emb_fun: "App s t >\<^sub>t s" and
  gt_emb_arg: "App s t >\<^sub>t t"
  by (simp_all add: gt_embedding_step_property left right)


subsection \<open>Compatibility with Contexts\<close>

lemma gt_fun_imp: "fun t >\<^sub>t s \<Longrightarrow> t >\<^sub>t s" 
  by (metis emb_step_fun gt_embedding_step_property gt_trans tm.disc(2) tm.exhaust_sel tm.sel(3))

lemma gt_arg_imp: "arg t >\<^sub>t s \<Longrightarrow> t >\<^sub>t s" 
  by (metis emb_step_arg gt_embedding_step_property gt_trans tm.disc(2) tm.exhaust_sel tm.sel(5))

lemma gt_compat_fun:
  assumes "t' >\<^sub>t t"
  shows "App s t' >\<^sub>t App s t"
using assms  apply (simp only:atomize_imp)
proof (induction rule:measure_induct_rule[of "\<lambda>(t, s). size t + size s" "\<lambda>(t, s). t' >\<^sub>t t \<longrightarrow> App s t' >\<^sub>t App s t" "(t,s)", 
  simplified prod.case],
  simp only: split_paired_all prod.case atomize_imp[symmetric])

  fix t s ::"('s, 'v) tm" 
  assume ih:"\<And>ta sa. size ta + size sa < size t + size s \<Longrightarrow> t' >\<^sub>t ta \<Longrightarrow> App sa t' >\<^sub>t App sa ta"
  and t'_gt_t:"t' >\<^sub>t t" 

  have t'_ne_t: "t' \<noteq> t"
    using gt_antisym t'_gt_t by blast
  have extf_args_single: "\<forall>f \<in> ground_heads (head s). extf f (>\<^sub>t) (args s @ [t']) (args s @ [t])"
    by (simp add: extf_compat_list t'_gt_t t'_ne_t)

  show  "App s t' >\<^sub>t App s t"
  proof (rule gt_same)
    show "head (App s t') = head (App s t)" by simp
    show "\<forall>f\<in>local.ground_heads (head (App s t')). extf f (>\<^sub>t) (args (App s t')) (args (App s t))"
      by (simp add: extf_args_single)
    have 0: "chop (App s t') >\<^sub>t chop (App s t)" 
    proof (cases s)
      case (Hd _)
      then show ?thesis using chop_App_Hd
        by (simp add: chop_App_Hd t'_gt_t)
    next
      case (App s1 s2)
      then show ?thesis using ih[of t "chop s"] chop_fun 
        by (metis nat_add_left_cancel_less size_chop_lt t'_gt_t tm.disc(2) tm.sel(4) tm.sel(6))
    qed
    show "chkchop_same (>\<^sub>t) (App s t') (App s t)"
    proof (cases "is_Var (head (App s t'))")
      case True
      then show ?thesis unfolding chkchop_same_def chkchop_def
        using True 0 by auto
    next
      case False
      have "App s t' >\<^sub>t chop (App s t)" using 0 by (simp add: gt_chop)
      then show ?thesis  unfolding chkchop_same_def chkchop_def 
        using False by auto
    qed
  qed
qed

theorem gt_compat_arg:
  shows "s' >\<^sub>t s \<Longrightarrow> t' \<ge>\<^sub>t t \<Longrightarrow> App s' t' >\<^sub>t App s t"
proof (simp only:atomize_imp,induction rule:measure_induct[of "\<lambda>(s',s,t). size s' + size s + size t" "\<lambda>(s',s,t). s' >\<^sub>t s \<longrightarrow> t' \<ge>\<^sub>t t \<longrightarrow> App s' t' >\<^sub>t App s t" "(s',s,t)", simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric] atomize_all[symmetric])
  fix s' s t
  assume ih:"\<And>ab ac ba. size ab + size ac + size ba < size s' + size s + size t \<Longrightarrow> ab >\<^sub>t ac \<Longrightarrow> t' \<ge>\<^sub>t ba \<Longrightarrow> App ab t' >\<^sub>t App ac ba" 
    and "s' >\<^sub>t s" and "t' \<ge>\<^sub>t t" 

  {
    fix s''::"('s,'v) tm" assume size_s'':"size s'' \<le> size s'"
    assume chkchop_s'_s: "chkchop (>\<^sub>t) s'' s"
    then have "chkchop (>\<^sub>t) (App s'' t') (App s t)" 
    proof (cases "is_Hd s")
      case True
      then show ?thesis using chkchop_s'_s unfolding chkchop_def 
        by (metis \<open>t' \<ge>\<^sub>t t\<close> chop_App_Hd gt_arg_imp gt_emb_arg tm.sel(6))
    next
      case False
      then show ?thesis using chkchop_s'_s unfolding chkchop_def
        using ih[of s'' "chop s" t] size_s''
        by (metis \<open>t' \<ge>\<^sub>t t\<close> add_less_mono add_mono_thms_linordered_field(1) chop_fun le_eq_less_or_eq nat_add_left_cancel_less size_chop_lt tm.sel(4) tm.sel(6))
    qed
  }
  note chkchop_compat_arg = this

  show "App s' t' >\<^sub>t App s t " using \<open>s' >\<^sub>t s\<close>
  proof (cases rule:gt.cases)
    case gt_chop
    then show ?thesis 
    proof (cases "t = t'")
      case True
      show ?thesis using True gt.gt_chop[of "App s' t'" "App s t"] gt_chop chkchop_compat_arg[of "chop s'"]
        by (metis add_strict_right_mono chop_fun ih size_chop_lt tm.disc(2) tm.sel(4) tm.sel(6))
    next
      case False
      then have "t' >\<^sub>t t"
        using \<open>t' \<ge>\<^sub>t t\<close> by blast
      have "App s' t' >\<^sub>t App (chop s') t'" 
        by (simp add: context_left emb_step_chop gt_embedding_step_property local.gt_chop(1))
      moreover have "... >\<^sub>t App s t"  using ih[of "chop s'" s t]
        using \<open>t' >\<^sub>t t\<close> gt_compat_fun local.gt_chop(1) local.gt_chop(2) size_chop_lt by fastforce
      ultimately show ?thesis using gt_trans by blast
    qed
  next
    case gt_diff
    then show ?thesis 
      using chkchop_compat_arg gt.gt_diff by auto
  next
    case gt_same
    have hd_s'_eq_s: "head s' = head s" 
      by (simp add: local.gt_same(1))
    {
      fix f assume f_gh: "f \<in> ground_heads (head s)"
      have f_s_args: 
        "extf f (>\<^sub>t) (args s') (args s)"
        using local.gt_same(3) f_gh by (simp add: hd_s'_eq_s)
      have f_compat_snoc: 
        "\<And>xs ys x. extf f (>\<^sub>t) ys xs \<Longrightarrow> extf f (>\<^sub>t) (ys @ [x]) (xs @ [x])" 
        by (simp add: extf_compat_append_right)
     
      have f_st_args2:
        "extf f (>\<^sub>t) (args (App s' t)) (args (App s t))"
        by (simp add: f_compat_snoc f_s_args)
      have 0:"\<forall>z\<in>UNIV. \<forall>y\<in>UNIV. \<forall>x\<in>UNIV. z >\<^sub>t y \<longrightarrow> y >\<^sub>t x \<longrightarrow> z >\<^sub>t x" 
        using gt_trans by blast
      then have f_trans:"\<And>xs ys zs. extf f (>\<^sub>t) zs ys \<Longrightarrow> extf f (>\<^sub>t) ys xs \<Longrightarrow> extf f (>\<^sub>t) zs xs" 
        using  extf_trans[of _ UNIV, unfolded lists_UNIV, OF UNIV_I UNIV_I UNIV_I 0] by metis
      have "extf f (>\<^sub>t) (args (App s' t')) (args (App s t))"
      proof (cases "t' = t")
        case True
        then show ?thesis using f_st_args2 by metis
      next
        case False
        have f_st_args1: 
          "extf f (>\<^sub>t) (args (App s' t')) (args (App s' t))"
          using extf_compat_list \<open>t' \<ge>\<^sub>t t\<close> False by simp
        then show ?thesis using f_trans f_st_args1 f_st_args2 by metis
      qed
    }
    note extf_cond = this
    have "chkchop_same (>\<^sub>t) (App s' t') (App s t)" unfolding chkchop_same_def
      using args.simps(1) chop_fun chkchop_compat_arg[of "chop s'", unfolded le_eq_less_or_eq] 
      chkchop_compat_arg[of s'] chkchop_def chkchop_same_def 
      size_chop_lt   epo.extf_min_empty[OF epo_axioms] gt.gt_same gt_antisym hd_s'_eq_s head_App 
      leI less_irrefl_nat local.gt_same(2) local.gt_same(3) tm.collapse(1) tm.sel(4) tm.sel(6)
      by metis
    then show ?thesis 
      using extf_cond gt.gt_same hd_s'_eq_s by auto
  qed
qed

theorem gt_compat_fun_strong:
  assumes t'_gt_t: "t' >\<^sub>t t"
  shows "apps s (t' # us) >\<^sub>t apps s (t # us)" 
proof (induct us rule: rev_induct)
  case Nil
  then show ?case 
  by (simp add: gt_compat_fun t'_gt_t)
next
  case (snoc x xs)
  then show ?case unfolding App_apps[symmetric] append_Cons[symmetric]
    using gt_compat_arg by blast
qed

theorem gt_or_eq_compat_App: "s' \<ge>\<^sub>t s \<Longrightarrow> t' \<ge>\<^sub>t t \<Longrightarrow> App s' t' \<ge>\<^sub>t App s t"
  using gt_compat_fun gt_compat_arg by blast

theorem gt_compat_App:
  shows "s' \<ge>\<^sub>t s \<Longrightarrow> t' >\<^sub>t t \<Longrightarrow> App s' t' >\<^sub>t App s t"
  using gt_compat_fun gt_compat_arg by blast

subsection "Stability under Substitutions"

(* TODO: move *)
lemma extf_map2:
  assumes
    "\<forall>y\<in>set ys \<union> set xs. \<forall>x\<in>set ys \<union> set xs. y >\<^sub>t x \<longrightarrow> (h y) >\<^sub>t (h x)"
    "extf f (>\<^sub>t) ys xs"
  shows
    "extf f (>\<^sub>t) (map h ys) (map h xs)"
  apply (rule extf_map[of "set ys \<union> set xs" ys xs "(>\<^sub>t)" h f])
        apply simp
       apply (simp add: in_listsI)
      apply (simp add: in_listsI)
  using gt_antisym apply blast
  using gt_trans apply blast
  by (simp add: assms)+

(* TODO: move ? *)
lemma less_multiset_doubletons:
  assumes
    "y <  t \<or>  y <  s"  
    "x <  t \<or>  x <  s" 
  shows 
    "{# y,  x#} < {# t,  s#}" 
  unfolding less_multiset\<^sub>D\<^sub>M
proof (intro exI)
  let ?X = "{# t,  s#}"
  let ?Y = "{#y, x#}"
  show "?X \<noteq> {#} \<and> ?X \<subseteq># {#t, s#} \<and> {#y, x#} = {#t, s#} - ?X + ?Y \<and> (\<forall>k. k \<in># ?Y \<longrightarrow> (\<exists>a. a \<in># ?X \<and> k < a))"
    using add_eq_conv_diff assms(1) assms(2) by auto
qed

theorem gt_sus: 
  assumes \<rho>_wary: "wary_subst \<rho>"
  assumes ghd: "\<And>x. ground_heads (Var x) = UNIV" (* This condition is only needed for gt_same, not for gt_diff ! *)
  shows "t >\<^sub>t s \<Longrightarrow> subst \<rho> t >\<^sub>t subst \<rho> s"
proof (simp only:atomize_imp,induction rule:measure_induct[of "\<lambda>(t,s). {# size t, size s #}" "\<lambda>(t,s). t >\<^sub>t s \<longrightarrow> subst \<rho> t >\<^sub>t subst \<rho> s" "(t,s)", simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric] atomize_all[symmetric])
  fix t s
  assume ih:"\<And>tt ss.
               {# size tt, size ss #} < {# size t, size s #} \<Longrightarrow>
               tt >\<^sub>t ss \<Longrightarrow> subst \<rho> tt >\<^sub>t subst \<rho> ss" 
    and "t >\<^sub>t s" 
  show "subst \<rho> t >\<^sub>t subst \<rho> s" using \<open>t >\<^sub>t s\<close>
  proof (cases)
    case t_gt_s_chop: gt_chop
    then show ?thesis 
      using emb_step_subst emb_step_chop[OF t_gt_s_chop(1)] gt_embedding_step_property 
       emb_step_size gt_trans ih[of "chop t" s] by (metis add_mset_lt_left_lt)
  next
    case t_gt_s_diff: gt_diff
    have gt_diff1: "head (subst \<rho> t) >\<^sub>h\<^sub>d head (subst \<rho> s)" 
      by (meson assms gt_hd_def subsetCE t_gt_s_diff(1) wary_subst_ground_heads)
    have gt_diff2: "is_Sym (head (subst \<rho> s))"
      by (metis ground_imp_subst_iden hd.collapse(2) hd.simps(18) head_subst t_gt_s_diff(2) tm.sel(1) tm.simps(17))
    have gt_diff3: "chkchop (>\<^sub>t) (subst \<rho> t) (subst \<rho> s)"    
    proof (cases s)
      case (Hd _)
      then show ?thesis 
        using t_gt_s_diff unfolding chkchop_def 
        by (metis ground_imp_subst_iden hd.collapse(2) hd.simps(18) tm.disc(1) tm.sel(1) tm.simps(17))
    next
      case s_App: (App s1 s2)
      then show ?thesis using t_gt_s_diff unfolding chkchop_def
        using ih[of t "chop s"] chop_subst_Sym size_chop_lt tm.disc(2)
        by (metis add_mset_lt_left_lt add_mset_lt_right_lt)
    qed
    show ?thesis
      using gt_diff gt_diff1 gt_diff2 gt_diff3 by blast
  next
    case t_gt_s_same: gt_same
    have gt_same1: "head (subst \<rho> t) = head (subst \<rho> s)" 
      by (simp add: t_gt_s_same(1))

    have extf_map_ts:"\<forall>f\<in>ground_heads (head t). extf f (>\<^sub>t) (map (subst \<rho>) (args t)) (map (subst \<rho>) (args s))"
    proof -
      have ih_args: "\<forall>y\<in>set (args t) \<union> set (args s). \<forall>x\<in>set (args t) \<union> set (args s). y >\<^sub>t x \<longrightarrow> subst \<rho> y >\<^sub>t subst \<rho> x"
        by (metis Un_iff less_multiset_doubletons size_in_args ih)
      have "\<forall>f\<in>ground_heads (head t). extf f (>\<^sub>t) (args t) (args s)"  
        using ghd t_gt_s_same(3) by metis
      then show ?thesis
        using extf_map[of "set (args t) \<union> set (args s)" "args t" "args s" gt "subst \<rho>"]
        using gt_irrefl gt_trans ih_args by blast
    qed

    show ?thesis
    proof (cases "head t")
      case (Var x1)
      then have "is_Var (head t)" by simp
      {
        fix u :: "('s, 'v) tm"
        assume "ground_heads (head u) \<subseteq> ground_heads (head t)" "size u \<le> size (subst \<rho> (Hd (head t)))"
        then have "apps u (map (subst \<rho>) (args t)) >\<^sub>t apps u (map (subst \<rho>) (args s))" 
        proof (induct "size u" arbitrary:u rule:less_induct)
          case less
          then show ?case 
          proof (cases u)
            case u_Hd: (Hd _)
            then have "args u = []" 
              by simp
            then show ?thesis 
            proof (cases s)
              case s_Hd: (Hd _)
              show ?thesis 
                apply (rule gt_same) 
                using extf_map_ts  args_Nil_iff_is_Hd s_Hd u_Hd \<open>args u = []\<close> less by fastforce+
            next
              case s_App: (App _ _)
              then have "is_App t" 
                by (metis args_Nil_iff_is_Hd extf_min_empty gt_hd_def gt_hd_irrefl t_gt_s_same(3))
  
              have "chop t >\<^sub>t chop s" 
                using \<open>is_App t\<close> \<open>is_Var (head t)\<close> s_App t_gt_s_same(2) by auto
              then have "subst \<rho> (chop t) >\<^sub>t subst \<rho> (chop s)" using ih
                by (metis \<open>is_App t\<close> less_multiset_doubletons s_App size_chop_lt tm.disc(2))
  
              define ut where "ut = apps u (map (subst \<rho>) (args t))"
              define us where "us = apps u (map (subst \<rho>) (args s))"
              have 0:"\<And>ss. args (apps u ss) = ss" 
                using  \<open>args u = []\<close> by simp
              have chop_us: "chop us = subst \<rho> (chop s)" 
                unfolding chop_def subst_apps us_def 0 using hd_map
                by (metis (no_types, lifting) args_Nil_iff_is_Hd map_tl s_App tm.disc(2))
              have chop_ut: "chop ut = subst \<rho> (chop t)"
                unfolding chop_def subst_apps ut_def 0 using \<open>is_App t\<close> 
                by (simp add: args_Nil_iff_is_Hd hd_map map_tl)
  
              have "head ut = head us" 
                by (simp add: us_def ut_def)
              moreover have "chkchop_same (>\<^sub>t) ut us" unfolding chkchop_def chkchop_same_def 
                by (metis "0" UNIV_witness \<open>is_Var (head t)\<close> \<open>subst \<rho> (chop t) >\<^sub>t subst \<rho> (chop s)\<close> 
                    args.simps(1) chop_us chop_ut extf_map_ts extf_min_empty 
                    ghd gt_chop is_Var_def tm.collapse(1) ut_def)
              moreover have "\<forall>f\<in>local.ground_heads (head ut). extf f (>\<^sub>t) (args ut) (args us)" 
                using extf_map_ts less us_def ut_def using "0" by auto
              ultimately show "ut >\<^sub>t us" 
                using gt_same by blast
            qed
          next
            case u_app: (App _ _)
            let ?ut = "apps u (map (subst \<rho>) (args t))"
            let ?us = "apps u (map (subst \<rho>) (args s))"
            have 1:"head ?ut = head ?ut" 
              by simp
            have "apps (chop u) (map (subst \<rho>) (args t)) >\<^sub>t apps (chop u) (map (subst \<rho>) (args s))"
              using less.hyps[of "chop u"] size_chop_lt 
              by (metis Var dual_order.trans ghd less.prems(2) less_or_eq_imp_le subset_UNIV tm.disc(2) u_app)
            then have "chop ?ut >\<^sub>t chop ?us" 
              by (simp add: chop_apps u_app)
            then have 2:"chkchop_same (>\<^sub>t) ?ut ?us" unfolding chkchop_same_def chkchop_def 
              by (metis UNIV_I \<open>is_Var (head t)\<close> args_Nil_iff_is_Hd args_apps extf_compat_append_left 
                  extf_map_ts extf_min_empty ghd gt_chop is_Var_def)
            have 3:"\<forall>f\<in>local.ground_heads (head ?ut). extf f (>\<^sub>t) (args ?ut) (args ?us)"
              using extf_compat_append_left extf_map_ts less.prems(1) by auto
            show ?thesis using gt_same 1 2 3 by simp
          qed
        qed
      }
      note inner_induction = this
      show ?thesis using inner_induction[of "subst \<rho> (Hd (head t))", unfolded subst_apps[symmetric]]
        by (metis Var ghd order_refl subset_UNIV t_gt_s_same(1) tm_collapse_apps)
    next
      case (Sym _)
      then have "is_Sym (head (subst \<rho> t))" "head (subst \<rho> t) = head t"
        by simp_all
      then have "chkchop_same (>\<^sub>t) t s"
        using t_gt_s_same unfolding chkchop_same_def chkchop_def
        using Sym by metis
      then have gt_same2: "chkchop_same (>\<^sub>t) (subst \<rho> t) (subst \<rho> s)" unfolding chkchop_same_def chkchop_def
         using ih[of t "chop s"] 
         by (metis (no_types, lifting) Sym \<open>head (subst \<rho> t) = head t\<close> \<open>is_Sym (head (subst \<rho> t))\<close> 
             add_mset_commute add_mset_lt_left_lt chop_subst_Sym ground_imp_subst_iden hd.simps(18) 
             size_chop_lt t_gt_s_same(1) tm.collapse(1) tm.simps(17))
      have gt_same3: "\<forall>f\<in>local.ground_heads (head (subst \<rho> t)). extf f (>\<^sub>t) (args (subst \<rho> t)) (args (subst \<rho> s))"
        using \<open>head (subst \<rho> t) = head t\<close> extf_compat_append_left extf_map_ts t_gt_s_same(1) by auto
      show ?thesis using gt_same gt_same1 gt_same2 gt_same3 by blast
    qed
  qed
qed


subsection \<open>Totality on Ground Terms\<close>

theorem gt_total_ground:
  assumes extf_total: "\<And>f. ext_total (extf f)"
  shows "ground t \<Longrightarrow> ground s \<Longrightarrow> t >\<^sub>t s \<or> s >\<^sub>t t \<or> t = s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(t, s). size t + size s"
      "\<lambda>(t, s). ground t \<longrightarrow> ground s \<longrightarrow> t >\<^sub>t s \<or> s >\<^sub>t t \<or> t = s" "(t, s)", simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix t s :: "('s, 'v) tm"
  assume
    ih: "\<And>ta sa. size ta + size sa < size t + size s \<Longrightarrow> ground ta \<Longrightarrow> ground sa \<Longrightarrow>
      ta >\<^sub>t sa \<or> sa >\<^sub>t ta \<or> ta = sa" and
    gr_t: "ground t" and gr_s: "ground s"

  let ?case = "t >\<^sub>t s \<or> s >\<^sub>t t \<or> t = s"

  have "chkchop (>\<^sub>t) t s \<or> s >\<^sub>t t"
    unfolding chkchop_def tm.case_eq_if using ih[of t "fun s"] ih[of t "arg s"]
    by (metis gr_s gr_t gt_chop gt_imp_vars ih nat_add_left_cancel_less size_chop_lt subset_empty)
  moreover have "chkchop (>\<^sub>t) s t \<or> t >\<^sub>t s"
    unfolding chkchop_def tm.case_eq_if using ih[of "fun t" s] ih[of "arg t" s]
    by (metis add_less_cancel_right gr_s gr_t gt_chop gt_imp_vars ih size_chop_lt subset_empty)
  moreover
  {
    assume
      chkembs_t_s: "chkchop (>\<^sub>t) t s" and
      chkembs_s_t: "chkchop (>\<^sub>t) s t"

    obtain g where g: "head t = Sym g"
      using gr_t by (metis ground_head hd.collapse(2))
    obtain f where f: "head s = Sym f"
      using gr_s by (metis ground_head hd.collapse(2))

    {
      assume g_gt_f: "g >\<^sub>s f"
      have "t >\<^sub>t s"
        using chkembs_t_s f g g_gt_f gt_diff gt_sym_imp_hd by auto
    }
    moreover
    {
      assume f_gt_g: "f >\<^sub>s g"
      have "s >\<^sub>t t" 
        using chkembs_s_t f f_gt_g g gt_diff gt_sym_imp_hd by auto
    }
    moreover
    {
      assume g_eq_f: "g = f"
      hence hd_t: "head t = head s"
        using g f by auto

      let ?ts = "args t"
      let ?ss = "args s"

      have gr_ts: "\<forall>ta \<in> set ?ts. ground ta"
        using ground_args[OF _ gr_t] by blast
      have gr_ss: "\<forall>sa \<in> set ?ss. ground sa"
        using ground_args[OF _ gr_s] by blast

      {
        assume ts_eq_ss: "?ts = ?ss"
        have "t = s"
          using hd_t ts_eq_ss by (rule tm_expand_apps)
      }
      moreover
      {
        assume ts_gt_ss: "extf g (>\<^sub>t) ?ts ?ss"
        have "t >\<^sub>t s"
          using chkembs_t_s g gt_same hd_t ts_gt_ss by auto
      }
      moreover
      {
        assume ss_gt_ts: "extf g (>\<^sub>t) ?ss ?ts"
        have "s >\<^sub>t t"
          using chkembs_s_t f g_eq_f gt_same hd_t ss_gt_ts by auto
      }
      ultimately have ?case
        using ih gr_ss gr_ts
          ext_total.total[OF extf_total, rule_format, of "set ?ts" "set ?ss" "(>\<^sub>t)" ?ts ?ss g]
        by (metis add_strict_mono in_listsI size_in_args)
    }
    ultimately have ?case
      using gt_sym_total by blast
  }
  ultimately show ?case
    by fast
qed

subsection \<open>Well-foundedness\<close>

abbreviation gtg :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t\<^sub>g" 50) where
  "(>\<^sub>t\<^sub>g) \<equiv> \<lambda>t s. ground t \<and> t >\<^sub>t s"

theorem gt_wf:
  assumes ghd_UNIV: "\<And>x. ground_heads_var x = UNIV"
  assumes extf_wf: "\<And>f. ext_wf (extf f)"
  shows "wfP (\<lambda>s t. t >\<^sub>t s)"
proof -
  have ground_wfP: "wfP (\<lambda>s t. t >\<^sub>t\<^sub>g s)"
    unfolding wfP_iff_no_inf_chain
  proof
    assume "\<exists>f. inf_chain (>\<^sub>t\<^sub>g) f"
    then obtain t where t_bad: "bad (>\<^sub>t\<^sub>g) t"
      unfolding inf_chain_def bad_def by blast

    let ?ff = "worst_chain (>\<^sub>t\<^sub>g) (\<lambda>t s. size t > size s)"
    let ?U_of = "\<lambda>i. {u. (?ff i) \<rhd>\<^sub>e\<^sub>m\<^sub>b u}"

    note wf_sz = wf_app[OF wellorder_class.wf, of size, simplified]

    define U where "U = (\<Union>i. ?U_of i)"

    have gr: "\<And>i. ground (?ff i)"
      using worst_chain_bad[OF wf_sz t_bad, unfolded inf_chain_def] by fast
    have gr_u: "\<And>u. u \<in> U \<Longrightarrow> ground u" unfolding U_def
      using gr ground_emb by fastforce

    have "\<not> bad (>\<^sub>t\<^sub>g) u" if u_in: "u \<in> ?U_of i" for u i
    proof
      let ?ti = "?ff i"

      assume u_bad: "bad (>\<^sub>t\<^sub>g) u"
      have sz_u: "size u < size ?ti"
        using emb_size_neq u_in by blast

      show False
      proof (cases i)
        case 0
        thus False
          using sz_u min_worst_chain_0[OF wf_sz u_bad] by simp
      next
        case Suc
        hence "?ff (i - 1) >\<^sub>t ?ff i"
          using worst_chain_pred[OF wf_sz t_bad] by simp
        moreover have "?ff i >\<^sub>t u"
          using gt_embedding_property u_in by blast
        ultimately have "?ff (i - 1) >\<^sub>t u"
          by (rule gt_trans)
        thus False
          using Suc sz_u min_worst_chain_Suc[OF wf_sz u_bad] gr by fastforce
      qed
    qed
    hence u_good: "\<And>u. u \<in> U \<Longrightarrow> \<not> bad (>\<^sub>t\<^sub>g) u"
      unfolding U_def by blast

    have bad_diff_same: "inf_chain (\<lambda>t s. ground t \<and> (gt_diff t s \<or> gt_same t s)) ?ff"
      unfolding inf_chain_def
    proof (intro allI conjI)
      fix i

      show "ground (?ff i)"
        by (rule gr)

      have gt: "?ff i >\<^sub>t ?ff (Suc i)"
        using worst_chain_pred[OF wf_sz t_bad] by blast

      have "\<not> gt_chop (?ff i) (?ff (Suc i))" 
      proof
        assume a: "gt_chop (?ff i) (?ff (Suc i))"
        then have "chop (?ff i) \<in> ?U_of i" 
          by (metis (mono_tags, lifting) emb_step_chop emb_step_is_emb gt_chop gt_chop.cases gt_irrefl mem_Collect_eq)
        then have  uij_in:"chop (?ff i) \<in> U" unfolding U_def by fast

        have "\<And>n. ?ff n >\<^sub>t ?ff (Suc n)"
          by (rule worst_chain_pred[OF wf_sz t_bad, THEN conjunct2])
        hence uij_gt_i_plus_3: "chop (?ff i) >\<^sub>t ?ff (Suc (Suc i))"
          using gt_trans by (metis (mono_tags, lifting) a gt_chop.cases)

        have "inf_chain (>\<^sub>t\<^sub>g) (\<lambda>j. if j = 0 then chop (?ff i) else ?ff (Suc (i + j)))"
          unfolding inf_chain_def
          by (auto intro!: gr gr_u[OF uij_in] uij_gt_i_plus_3 worst_chain_pred[OF wf_sz t_bad])
        hence "bad (>\<^sub>t\<^sub>g) (chop (?ff i))"
          unfolding bad_def by fastforce
        thus False
          using u_good[OF uij_in] by sat
      qed
      thus "gt_diff (?ff i) (?ff (Suc i)) \<or> gt_same (?ff i) (?ff (Suc i))"
        using gt unfolding gt_iff_chop_diff_same by sat
    qed

    have "wf {(s, t). ground s \<and> ground t \<and> sym (head t) >\<^sub>s sym (head s)}"
      using gt_sym_wf unfolding wfP_def wf_iff_no_infinite_down_chain by fast
    moreover have "{(s, t). ground t \<and> gt_diff t s}
      \<subseteq> {(s, t). ground s \<and> ground t \<and> sym (head t) >\<^sub>s sym (head s)}"
    proof (clarsimp, intro conjI)
      fix s t
      assume gr_t: "ground t" and gt_diff_t_s: "gt_diff t s"
      thus gr_s: "ground s"
        using gt_iff_chop_diff_same gt_imp_vars by fastforce

      show "sym (head t) >\<^sub>s sym (head s)"
        using gt_diff_t_s ground_head[OF gr_s] ground_head[OF gr_t]
        by (cases; cases "head s"; cases "head t") (auto simp: gt_hd_def)
    qed
    ultimately have wf_diff: "wf {(s, t). ground t \<and> gt_diff t s}"
      by (rule wf_subset)

    have diff_O_same: "{(s, t). ground t \<and> gt_diff t s} O {(s, t). ground t \<and> gt_same t s}
      \<subseteq> {(s, t). ground t \<and> gt_diff t s}"
      unfolding gt_diff.simps gt_same.simps
      by clarsimp (metis chkchop_def chkchop_same_def gt_same gt_trans)

    have diff_same_as_union: "{(s, t). ground t \<and> (gt_diff t s \<or> gt_same t s)} =
      {(s, t). ground t \<and> gt_diff t s} \<union> {(s, t). ground t \<and> gt_same t s}"
      by auto

    obtain k where bad_same: "inf_chain (\<lambda>t s. ground t \<and> gt_same t s) (\<lambda>i. ?ff (i + k))"
      using wf_infinite_down_chain_compatible[OF wf_diff _ diff_O_same, of ?ff] bad_diff_same
      unfolding inf_chain_def diff_same_as_union[symmetric] by auto
    hence hd_sym: "\<And>i. is_Sym (head (?ff (i + k)))"
      unfolding inf_chain_def by (simp add: ground_head)

    define f where "f = sym (head (?ff k))"

    have hd_eq_f: "head (?ff (i + k)) = Sym f" for i
    proof (induct i)
      case 0
      thus ?case
        by (auto simp: f_def hd.collapse(2)[OF hd_sym, of 0, simplified])
    next
      case (Suc ia)
      thus ?case
        using bad_same unfolding inf_chain_def gt_same.simps by simp
    qed

    let ?gtu = "\<lambda>t s. t \<in> U \<and> t >\<^sub>t s"
    thm UnionI CollectI
    have "t \<in> set (args (?ff i)) \<Longrightarrow> t \<in> U" for t i
      unfolding U_def apply (rule UnionI[of "?U_of i"]) 
      using arg_emb CollectI arg_emb size_in_args by fast+
    moreover have "\<And>i. extf f (>\<^sub>t\<^sub>g) (args (?ff (i + k))) (args (?ff (Suc i + k)))"
      using bad_same hd_eq_f unfolding  inf_chain_def gt_same.simps f_def hd.collapse(2)[OF ground_head, OF gr]
      using extf_mono_strong[of _ _ "(>\<^sub>t)" "(\<lambda>t s. ground t \<and> t >\<^sub>t s)" ] ground_hd_in_ground_heads 
      by (metis (no_types, lifting) ground_args)
    ultimately have "\<And>i. extf f ?gtu (args (?ff (i + k))) (args (?ff (Suc i + k)))"
      using extf_mono_strong[of _ _ "(\<lambda>t s. ground t \<and> t >\<^sub>t s)" "\<lambda>t s. t \<in> U \<and> t >\<^sub>t s"] unfolding U_def by blast
    hence "inf_chain (extf f ?gtu) (\<lambda>i. args (?ff (i + k)))"
      unfolding inf_chain_def by blast
    hence nwf_ext: "\<not> wfP (\<lambda>xs ys. extf f ?gtu ys xs)"
      unfolding wfP_iff_no_inf_chain by fast

    have gtu_le_gtg: "?gtu \<le> (>\<^sub>t\<^sub>g)"
      by (auto intro!: gr_u)

    have "wfP (\<lambda>s t. ?gtu t s)"
      unfolding wfP_iff_no_inf_chain
    proof (intro notI, elim exE)
      fix f
      assume bad_f: "inf_chain ?gtu f"
      hence bad_f0: "bad ?gtu (f 0)"
        by (rule inf_chain_bad)

      have "f 0 \<in> U"
        using bad_f unfolding inf_chain_def by blast
      hence good_f0: "\<not> bad ?gtu (f 0)"
        using u_good bad_f inf_chain_bad inf_chain_subset[OF _ gtu_le_gtg] by blast

      show False
        using bad_f0 good_f0 by sat
    qed
    hence wf_ext: "wfP (\<lambda>xs ys. extf f ?gtu ys xs)"
      by (rule ext_wf.wf[OF extf_wf, rule_format])

    show False
      using nwf_ext wf_ext by blast
  qed

  let ?subst = "subst grounding_\<rho>"

  have "wfP (\<lambda>s t. ?subst t >\<^sub>t\<^sub>g ?subst s)"
    by (rule wfP_app[OF ground_wfP])
  hence "wfP (\<lambda>s t. ?subst t >\<^sub>t ?subst s)"
    by (simp add: ground_grounding_\<rho>)
  thus ?thesis
    using gt_sus ghd_UNIV ground_heads.simps(1) wary_grounding_\<rho> wfP_eq_minimal
    by (metis (no_types, lifting))
qed

end

end
