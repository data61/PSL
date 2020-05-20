section \<open>Basis Extension\<close>

text \<open>We prove that every linear indepent set/list of vectors can be extended into a basis.
  Similarly, from every set of vectors one can extract a linear independent set of vectors
  that spans the same space.\<close>

theory Basis_Extension
  imports
    LLL_Basis_Reduction.Gram_Schmidt_2
begin


context cof_vec_space
begin

lemma lin_indpt_list_length_le_n: assumes "lin_indpt_list xs"
  shows "length xs \<le> n"
proof -
  from assms[unfolded lin_indpt_list_def]
  have xs: "set xs \<subseteq> carrier_vec n" and dist: "distinct xs" and lin: "lin_indpt (set xs)" by auto
  from dist have "card (set xs) = length xs" by (rule distinct_card)
  moreover have "card (set xs) \<le> n"
    using lin xs dim_is_n li_le_dim(2) by auto
  ultimately show ?thesis by auto
qed

lemma lin_indpt_list_length_eq_n: assumes "lin_indpt_list xs"
  and "length xs = n"
shows "span (set xs) = carrier_vec n" "basis (set xs)"
proof -
  from assms[unfolded lin_indpt_list_def]
  have xs: "set xs \<subseteq> carrier_vec n" and dist: "distinct xs" and lin: "lin_indpt (set xs)" by auto
  from dist have "card (set xs) = length xs" by (rule distinct_card)
  with assms have "card (set xs) = n" by auto
  with lin xs show "span (set xs) = carrier_vec n" "basis (set xs)"  using dim_is_n
    by (metis basis_def dim_basis dim_li_is_basis fin_dim finite_basis_exists gen_ge_dim li_le_dim(1))+
qed

lemma expand_to_basis: assumes lin: "lin_indpt_list xs"
  shows "\<exists> ys. set ys \<subseteq> set (unit_vecs n) \<and> lin_indpt_list (xs @ ys) \<and> length (xs @ ys) = n"
proof -
  define y where "y = n - length xs"
  from lin have "length xs \<le> n" by (rule lin_indpt_list_length_le_n)
  hence "length xs + y = n" unfolding y_def by auto
  thus "\<exists> ys. set ys \<subseteq> set (unit_vecs n) \<and> lin_indpt_list (xs @ ys) \<and> length (xs @ ys) = n"
    using lin
  proof (induct y arbitrary: xs)
    case (0 xs)
    thus ?case by (intro exI[of _ Nil], auto)
  next
    case (Suc y xs)
    hence "length xs < n" by auto
    from Suc(3)[unfolded lin_indpt_list_def]
    have xs: "set xs \<subseteq> carrier_vec n" and dist: "distinct xs" and lin: "lin_indpt (set xs)" by auto
    from distinct_card[OF dist] Suc(2) have card: "card (set xs) < n" by auto
    have "span (set xs) \<noteq> carrier_vec n" using card dim_is_n xs basis_def dim_basis lin by auto
    with span_closed[OF xs] have "span (set xs) \<subset> carrier_vec n" by auto
    also have "carrier_vec n = span (set (unit_vecs n))"
      unfolding span_unit_vecs_is_carrier ..
    finally have sub: "span (set xs) \<subset> span (set (unit_vecs n))" .
    have "\<exists> u. u \<in> set (unit_vecs n) \<and> u \<notin> span (set xs)"
      using span_subsetI[OF xs, of "set (unit_vecs n)"] sub by force
    then obtain u where uu: "u \<in> set (unit_vecs n)" and usxs: "u \<notin> span (set xs)" by auto
    then have u: "u \<in> carrier_vec n" unfolding unit_vecs_def by auto
    let ?xs = "xs @ [u]"
    from span_mem[OF xs, of u] usxs have uxs: "u \<notin> set xs" by auto
    with dist have dist: "distinct ?xs" by auto
    have lin: "lin_indpt (set ?xs)" using lin_dep_iff_in_span[OF xs lin u uxs] usxs by auto
    from lin dist u xs have lin: "lin_indpt_list ?xs" unfolding lin_indpt_list_def by auto
    from Suc(2) have "length ?xs + y = n" by auto
    from Suc(1)[OF this lin] obtain ys where
      "set ys \<subseteq> set (unit_vecs n)" "lin_indpt_list (?xs @ ys)" "length (?xs @ ys) = n" by auto
    thus ?case using uu
      by (intro exI[of _ "u # ys"], auto)
  qed
qed

definition "basis_extension xs = (SOME ys.
  set ys \<subseteq> set (unit_vecs n) \<and> lin_indpt_list (xs @ ys) \<and> length (xs @ ys) = n)"

lemma basis_extension: assumes "lin_indpt_list xs"
  shows "set (basis_extension xs) \<subseteq> set (unit_vecs n)"
    "lin_indpt_list (xs @ basis_extension xs)"
    "length (xs @ basis_extension xs) = n"
  using someI_ex[OF expand_to_basis[OF assms], folded basis_extension_def] by auto

lemma exists_lin_indpt_sublist: assumes X: "X \<subseteq> carrier_vec n"
  shows "\<exists> Ls. lin_indpt_list Ls \<and> span (set Ls) = span X \<and> set Ls \<subseteq> X"
proof -
  let ?T = ?thesis
  have "(\<exists> Ls. lin_indpt_list Ls \<and> span (set Ls) \<subseteq> span X \<and> set Ls \<subseteq> X \<and> length Ls = k) \<or> ?T" for k
  proof (induct k)
    case 0
    have "lin_indpt {}" by (simp add: lindep_span)
    thus ?case using span_is_monotone by (auto simp: lin_indpt_list_def)
  next
    case (Suc k)
    show ?case
    proof (cases ?T)
      case False
      with Suc obtain Ls where lin: "lin_indpt_list Ls"
        and span: "span (set Ls) \<subseteq> span X" and Ls: "set Ls \<subseteq> X"  and len: "length Ls = k" by auto
      from Ls X have LsC: "set Ls \<subseteq> carrier_vec n" by auto
      show ?thesis
      proof (cases "X \<subseteq> span (set Ls)")
        case True
        hence "span X \<subseteq> span (set Ls)" using LsC X by (metis span_subsetI)
        with span have "span (set Ls) = span X" by auto
        hence ?T by (intro exI[of _ Ls] conjI True lin Ls)
        thus ?thesis by auto
      next
        case False
        with span obtain x where xX: "x \<in> X" and xSLs: "x \<notin> span (set Ls)" by auto
        from Ls X have LsC: "set Ls \<subseteq> carrier_vec n" by auto
        from span_mem[OF this, of x] xSLs have xLs: "x \<notin> set Ls" by auto
        let ?Ls = "x # Ls"
        show ?thesis
        proof (intro disjI1 exI[of _ ?Ls] conjI)
          show "length ?Ls = Suc k" using len by auto
          show "lin_indpt_list ?Ls" using lin xSLs xLs unfolding lin_indpt_list_def
            using lin_dep_iff_in_span[OF LsC _ _ xLs] xX X by auto
          show "set ?Ls \<subseteq> X" using xX Ls by auto
          from span_is_monotone[OF this]
          show "span (set ?Ls) \<subseteq> span X" .
        qed
      qed
    qed auto
  qed
  from this[of "n + 1"] lin_indpt_list_length_le_n show ?thesis by fastforce
qed

lemma exists_lin_indpt_subset: assumes "X \<subseteq> carrier_vec n"
  shows "\<exists> Ls. lin_indpt Ls \<and> span (Ls) = span X \<and> Ls \<subseteq> X"
proof -
  from exists_lin_indpt_sublist[OF assms]
  obtain Ls where "lin_indpt_list Ls \<and> span (set Ls) = span X \<and> set Ls \<subseteq> X" by auto
  thus ?thesis by (intro exI[of _ "set Ls"], auto simp: lin_indpt_list_def)
qed
end

end