section \<open>Dimension of Spans\<close>

text \<open>We define the notion of dimension of a span of vectors and prove some natural results about them.
  The definition is made as a function, so that no interpretation of locales like subspace is required.\<close>
theory Dim_Span
  imports Missing_VS_Connect
begin

context vec_space
begin
definition "dim_span W = Max (card ` {V. V \<subseteq> carrier_vec n \<and> V \<subseteq> span W \<and> lin_indpt V})"

lemma fixes V W :: "'a vec set"
  shows
    card_le_dim_span:
    "V \<subseteq> carrier_vec n \<Longrightarrow> V \<subseteq> span W \<Longrightarrow> lin_indpt V \<Longrightarrow> card V \<le> dim_span W" and
    card_eq_dim_span_imp_same_span:
    "W \<subseteq> carrier_vec n \<Longrightarrow> V \<subseteq> span W \<Longrightarrow> lin_indpt V \<Longrightarrow> card V = dim_span W \<Longrightarrow> span V = span W" and
    same_span_imp_card_eq_dim_span:
    "V \<subseteq> carrier_vec n \<Longrightarrow> W \<subseteq> carrier_vec n \<Longrightarrow> span V = span W \<Longrightarrow> lin_indpt V \<Longrightarrow> card V = dim_span W" and
    dim_span_cong:
    "span V = span W \<Longrightarrow> dim_span V = dim_span W" and
    ex_basis_span:
    "V \<subseteq> carrier_vec n \<Longrightarrow> \<exists> W. W \<subseteq> carrier_vec n \<and> lin_indpt W \<and> span V = span W \<and> dim_span V = card W"
proof -
  show cong: "\<And> V W. span V = span W \<Longrightarrow> dim_span V = dim_span W" unfolding dim_span_def by auto
  {
    fix W :: "'a vec set"
    let ?M = "{V. V \<subseteq> carrier_vec n \<and> V \<subseteq> span W \<and> lin_indpt V}"
    have "card ` ?M \<subseteq> {0 .. n}"
    proof
      fix k
      assume "k \<in> card ` ?M"
      then obtain V where V: "V \<subseteq> carrier_vec n \<and> V \<subseteq> span W \<and> lin_indpt V"
        and k: "k = card V"
        by auto
      from V have "card V \<le> n" using dim_is_n li_le_dim by auto
      with k show "k \<in> {0 .. n}" by auto
    qed
    from finite_subset[OF this]
    have fin: "finite (card ` ?M)" by auto
    have "{} \<in> ?M" by (auto simp: span_empty span_zero)
    from imageI[OF this, of card]
    have "0 \<in> card ` ?M" by auto
    hence Mempty: "card ` ?M \<noteq> {}" by auto
    from Max_ge[OF fin, folded dim_span_def]
    show "\<And> V :: 'a vec set. V \<subseteq> carrier_vec n \<Longrightarrow> V \<subseteq> span W \<Longrightarrow> lin_indpt V \<Longrightarrow> card V \<le> dim_span W"
      by auto
    note this fin Mempty
  } note part1 = this
  {
    fix V W :: "'a vec set"
    assume  W: "W \<subseteq> carrier_vec n"
      and VsW: "V \<subseteq> span W" and linV: "lin_indpt V" and card: "card V = dim_span W"
    from W VsW have V: "V \<subseteq> carrier_vec n" using span_mem[OF W] by auto
    from Max_in[OF part1(2,3), folded dim_span_def, of W]
    obtain WW where WW: "WW \<subseteq> carrier_vec n" "WW \<subseteq> span W" "lin_indpt WW"
      and id: "dim_span W = card WW" by auto
    show "span V = span W"
    proof (rule ccontr)
      from VsW V W have sub: "span V \<subseteq> span W" using span_subsetI by metis
      assume "span V \<noteq> span W"
      with sub obtain w where wW: "w \<in> span W" and wsV: "w \<notin> span V" by auto
      from wW W have w: "w \<in> carrier_vec n" by auto
      from linV V have finV: "finite V" using fin_dim fin_dim_li_fin by blast
      from wsV span_mem[OF V, of w] have wV: "w \<notin> V" by auto
      let ?X = "insert w V"
      have "card ?X = Suc (card V)" using wV finV by simp
      hence gt: "card ?X > dim_span W" unfolding card by simp
      have linX: "lin_indpt ?X" using lin_dep_iff_in_span[OF V linV w wV] wsV by auto
      have XW: "?X \<subseteq> span W" using wW VsW by auto
      from part1(1)[OF _ XW linX] w V have "card ?X \<le> dim_span W" by auto
      with gt show False by auto
    qed
  } note card_dim_span = this
  {
    fix V :: "'a vec set"
    assume V: "V \<subseteq> carrier_vec n"
    from Max_in[OF part1(2,3), folded dim_span_def, of V]
    obtain W where W: "W \<subseteq> carrier_vec n" "W \<subseteq> span V" "lin_indpt W"
      and idW: "card W = dim_span V" by auto
    show "\<exists> W. W \<subseteq> carrier_vec n \<and> lin_indpt W \<and> span V = span W \<and> dim_span V = card W"
    proof (intro exI[of _ W] conjI W idW[symmetric])
      from card_dim_span[OF V(1) W(2-3) idW] show "span V = span W"  by auto
    qed
  }
  {
    fix V W
    assume V: "V \<subseteq> carrier_vec n"
      and W: "W \<subseteq> carrier_vec n"
      and span: "span V = span W"
      and lin: "lin_indpt V"
    from Max_in[OF part1(2,3), folded dim_span_def, of W]
    obtain WW where WW: "WW \<subseteq> carrier_vec n" "WW \<subseteq> span W" "lin_indpt WW"
      and idWW: "card WW = dim_span W" by auto
    from card_dim_span[OF W WW(2-3) idWW] span
    have spanWW: "span WW = span V" by auto
    from span have "V \<subseteq> span W" using span_mem[OF V] by auto
    from part1(1)[OF V this lin] have VW: "card V \<le> dim_span W" .
    have finWW: "finite WW" using WW by (simp add: fin_dim_li_fin)
    have finV: "finite V" using lin V by (simp add: fin_dim_li_fin)
    from replacement[OF finWW finV V WW(3) WW(2)[folded span], unfolded idWW]
    obtain C :: "'a vec set"
      where le: "int (card C) \<le> int (card V) - int (dim_span W)" by auto
    from le have "int (dim_span W) + int (card C) \<le> int (card V)" by linarith
    hence "dim_span W + card C \<le> card V" by linarith
    with VW show "card V = dim_span W" by auto
  }
qed

lemma dim_span_le_n: assumes W: "W \<subseteq> carrier_vec n" shows "dim_span W \<le> n"
proof -
  from ex_basis_span[OF W] obtain V where
    V: "V \<subseteq> carrier_vec n"
    and lin: "lin_indpt V"
    and dim: "dim_span W = card V"
    by auto
  show ?thesis unfolding dim using lin V
    using dim_is_n li_le_dim by auto
qed

lemma dim_span_insert: assumes W: "W \<subseteq> carrier_vec n"
  and v: "v \<in> carrier_vec n" and vs: "v \<notin> span W"
shows "dim_span (insert v W) = Suc (dim_span W)"
proof -
  from ex_basis_span[OF W] obtain V where
    V: "V \<subseteq> carrier_vec n"
    and lin: "lin_indpt V"
    and span: "span W = span V"
    and dim: "dim_span W = card V"
    by auto
  from V vs[unfolded span] have vV: "v \<notin> V" using span_mem[OF V] by blast
  from lin_dep_iff_in_span[OF V lin v vV] vs span
  have lin': "lin_indpt (insert v V)" by auto
  have finV: "finite V" using lin V using fin_dim fin_dim_li_fin by blast
  have "card (insert v V) = Suc (card V)" using finV vV by auto
  hence cvV: "card (insert v V) = Suc (dim_span W)" using dim by auto
  have "span (insert v V) = span (insert v W)"
    using span V W v by (metis bot_least insert_subset insert_union span_union_is_sum)
  from same_span_imp_card_eq_dim_span[OF _ _ this lin'] cvV v V W
  show ?thesis by auto
qed
end
end