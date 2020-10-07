section \<open>Auxiliary lemmas\<close>

theory AuxLemmas imports Main begin

abbreviation "arbitrary == undefined"

text \<open>Lemmas about left- and rightmost elements in lists\<close>

lemma leftmost_element_property:
  assumes "\<exists>x \<in> set xs. P x"
  obtains zs x' ys where "xs = zs@x'#ys" and "P x'" and "\<forall>z \<in> set zs. \<not> P z"
proof(atomize_elim)
  from \<open>\<exists>x \<in> set xs. P x\<close> 
  show "\<exists>zs x' ys. xs = zs @ x' # ys \<and> P x' \<and> (\<forall>z\<in>set zs. \<not> P z)"
  proof(induct xs)
    case Nil thus ?case by simp
  next
    case (Cons x' xs')
    note IH = \<open>\<exists>a\<in>set xs'. P a
      \<Longrightarrow> \<exists>zs x' ys. xs' = zs@x'#ys \<and> P x' \<and> (\<forall>z\<in>set zs. \<not> P z)\<close>
    show ?case
    proof (cases "P x'")
      case True
      then have "(\<exists>ys. x' # xs' = [] @ x' # ys) \<and> P x' \<and> (\<forall>x\<in>set []. \<not> P x)" by simp
      then show ?thesis by blast
    next
      case False
      with \<open>\<exists>y\<in>set (x'#xs'). P y\<close> have "\<exists>y\<in>set xs'. P y" by simp
      from IH[OF this] obtain y ys zs where "xs' = zs@y#ys"
        and "P y" and "\<forall>z\<in>set zs. \<not> P z" by blast
      from \<open>\<forall>z\<in>set zs. \<not> P z\<close> False have "\<forall>z\<in>set (x'#zs). \<not> P z" by simp
      with \<open>xs' = zs@y#ys\<close> \<open>P y\<close> show ?thesis by (metis Cons_eq_append_conv)
    qed
  qed
qed



lemma rightmost_element_property:
  assumes "\<exists>x \<in> set xs. P x"
  obtains ys x' zs where "xs = ys@x'#zs" and "P x'" and "\<forall>z \<in> set zs. \<not> P z"
proof(atomize_elim)
  from \<open>\<exists>x \<in> set xs. P x\<close>
  show "\<exists>ys x' zs. xs = ys @ x' # zs \<and> P x' \<and> (\<forall>z\<in>set zs. \<not> P z)"
  proof(induct xs)
    case Nil thus ?case by simp
  next
    case (Cons x' xs')
    note IH = \<open>\<exists>a\<in>set xs'. P a
      \<Longrightarrow> \<exists>ys x' zs. xs' = ys @ x' # zs \<and> P x' \<and> (\<forall>z\<in>set zs. \<not> P z)\<close>
    show ?case
    proof(cases "\<exists>y\<in>set xs'. P y")
      case True
      from IH[OF this] obtain y ys zs where "xs' = ys @ y # zs"
        and "P y" and "\<forall>z\<in>set zs. \<not> P z" by blast
      thus ?thesis by (metis Cons_eq_append_conv)
    next
      case False
      with \<open>\<exists>y\<in>set (x'#xs'). P y\<close> have "P x'" by simp
      with False show ?thesis by (metis eq_Nil_appendI)
    qed
  qed
qed


text \<open>Lemma concerning maps and \<open>@\<close>\<close>

lemma map_append_append_maps:
  assumes map:"map f xs = ys@zs"
  obtains xs' xs'' where "map f xs' = ys" and "map f xs'' = zs" and "xs=xs'@xs''"
by (metis append_eq_conv_conj append_take_drop_id assms drop_map take_map that)


text \<open>Lemma concerning splitting of @{term list}s\<close>

lemma  path_split_general:
assumes all:"\<forall>zs. xs \<noteq> ys@zs"
obtains j zs where "xs = (take j ys)@zs" and "j < length ys"
  and "\<forall>k > j. \<forall>zs'. xs \<noteq> (take k ys)@zs'"
proof(atomize_elim)
  from \<open>\<forall>zs. xs \<noteq> ys@zs\<close>
  show "\<exists>j zs. xs = take j ys @ zs \<and> j < length ys \<and> 
               (\<forall>k>j. \<forall>zs'. xs \<noteq> take k ys @ zs')"
  proof(induct ys arbitrary:xs)
    case Nil thus ?case by auto
  next
    case (Cons y' ys')
    note IH = \<open>\<And>xs. \<forall>zs. xs \<noteq> ys' @ zs \<Longrightarrow>
      \<exists>j zs. xs = take j ys' @ zs \<and> j < length ys' \<and> 
      (\<forall>k. j < k \<longrightarrow> (\<forall>zs'. xs \<noteq> take k ys' @ zs'))\<close>
    show ?case
    proof(cases xs)
      case Nil thus ?thesis by simp
    next
      case (Cons x' xs')
      with \<open>\<forall>zs. xs \<noteq> (y' # ys') @ zs\<close> have "x' \<noteq> y' \<or> (\<forall>zs. xs' \<noteq> ys' @ zs)"
        by simp
      show ?thesis
      proof(cases "x' = y'")
        case True
        with \<open>x' \<noteq> y' \<or> (\<forall>zs. xs' \<noteq> ys' @ zs)\<close> have "\<forall>zs. xs' \<noteq> ys' @ zs" by simp
        from IH[OF this] have "\<exists>j zs. xs' = take j ys' @ zs \<and> j < length ys' \<and>
          (\<forall>k. j < k \<longrightarrow> (\<forall>zs'. xs' \<noteq> take k ys' @ zs'))" .
        then obtain j zs where "xs' = take j ys' @ zs"
          and "j < length ys'"
          and all_sub:"\<forall>k. j < k \<longrightarrow> (\<forall>zs'. xs' \<noteq> take k ys' @ zs')"
          by blast
        from \<open>xs' = take j ys' @ zs\<close> True
          have "(x'#xs') = take (Suc j) (y' # ys') @ zs"
          by simp
        from all_sub True have all_imp:"\<forall>k. j < k \<longrightarrow> 
          (\<forall>zs'. (x'#xs') \<noteq> take (Suc k) (y' # ys') @ zs')"
          by auto
        { fix l assume "(Suc j) < l"
          then obtain k where [simp]:"l = Suc k" by(cases l) auto
          with \<open>(Suc j) < l\<close> have "j < k" by simp
          with all_imp 
          have "\<forall>zs'. (x'#xs') \<noteq> take (Suc k) (y' # ys') @ zs'"
            by simp
          hence "\<forall>zs'. (x'#xs') \<noteq> take l (y' # ys') @ zs'"
            by simp }
        with \<open>(x'#xs') = take (Suc j) (y' # ys') @ zs\<close> \<open>j < length ys'\<close> Cons
        show ?thesis by (metis Suc_length_conv less_Suc_eq_0_disj)
      next
        case False
        with Cons have "\<forall>i zs'. i > 0 \<longrightarrow> xs \<noteq> take i (y' # ys') @ zs'"
          by auto(case_tac i,auto)
        moreover
        have "\<exists>zs. xs = take 0 (y' # ys') @ zs" by simp
        ultimately show ?thesis by(rule_tac x="0" in exI,auto)
      qed
    qed
  qed
qed

end
