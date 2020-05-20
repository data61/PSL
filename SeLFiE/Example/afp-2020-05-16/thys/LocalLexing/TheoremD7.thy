theory TheoremD7
imports TheoremD6
begin

context LocalLexing begin

lemma Derives1_keep_first_terminal: "Derives1 (x#u) i r (y#v) \<Longrightarrow> is_terminal x \<Longrightarrow> x = y"
  by (metis Derives1_leftmost Derives1_take leftmost_cons_terminal list.sel(1) not_le take_Cons')
  
lemma Derives1_nonterminal_head:
  assumes "Derives1 u i r (N#v)"
  assumes "is_nonterminal N"
  shows "\<exists> u' M. u = M#u' \<and> is_nonterminal M"
proof - 
  from assms have nonempty_u: "u \<noteq> []"
    by (metis Derives1_bound less_nat_zero_code list.size(3)) 
  have "\<exists> u' M. u = M#u'"
    using count_terminals.cases nonempty_u by blast 
  then obtain u' M where split_u: "u = M#u'" by blast
  have is_sentence_u: "is_sentence u" using assms
    using Derives1_sentence1 by blast 
  then have "is_terminal M \<or> is_nonterminal M"
    using is_sentence_cons is_symbol_distinct split_u by blast
  then show ?thesis
  proof (induct rule: disjCases2)
    case 1
      have "is_terminal N"
        using "1.hyps" Derives1_keep_first_terminal 
        assms(1) split_u by blast
      with assms have "False" using is_terminal_nonterminal by blast 
      then show ?case by blast
  next
    case 2 with split_u show ?case by blast
  qed
qed

lemma sentence_starts_with_nonterminal:
  assumes "is_nonterminal N"
  assumes "derives u []"
  shows "\<exists> X r. u@[N] = X#r \<and> is_nonterminal X"
proof (cases "u = []")
  case True thus ?thesis using assms(1) by blast
next
  case False 
  then have "\<exists> X r. u = X#r" using count_terminals.cases by blast 
  then obtain X r where Xr: "u = X#r" by blast
  then have "is_nonterminal X"
    by (metis False assms(2) count_terminals.simps derives_count_terminals_leq 
      derives_is_sentence is_sentence_cons is_symbol_distinct not_le zero_less_Suc) 
  with Xr show ?thesis by auto
qed

lemma Derives1_nonterminal_head':
  assumes "Derives1 u i r (v1@[N]@v2)"
  assumes "is_nonterminal N"
  assumes "derives v1 []"
  shows "\<exists> u' M. u = M#u' \<and> is_nonterminal M"
proof -
  from sentence_starts_with_nonterminal[OF assms(2,3)]
  obtain X r where "v1 @ [N] = X # r \<and> is_nonterminal X" by blast
  then show ?thesis
    by (metis Derives1_nonterminal_head append_Cons append_assoc assms(1))   
qed

lemma thmD7_helper: 
  assumes "LeftDerivation [\<SS>] D (N#v)"
  assumes "is_nonterminal N"
  assumes "\<SS> \<noteq> N"  
  shows "\<exists> n M a a1 a2 w. n < length D \<and> (M, a) \<in> \<RR> \<and> LeftDerivation [\<SS>] (take n D) (M#w) \<and> 
    a = a1 @ [N] @ a2 \<and> derives a1 []"
proof -
  have "\<exists> n u v. LeftDerivation [\<SS>] (take n D) (u@[N]@v) \<and> derives u []"
    apply (rule_tac x="length D" in exI)
    apply (rule_tac x="[]" in exI)
    apply (rule_tac x="v" in exI)
    using assms by simp
  then show ?thesis
  proof (induct rule: ex_minimal_witness)
    case (Minimal K)
      have nonzero_K: "K \<noteq> 0"
      proof (cases "K = 0")
        case True
          with Minimal have "\<exists> u v. [\<SS>] = u@[N]@v"
            using LeftDerivation.simps(1) take_0 by auto
          with assms have "False" by (simp add: Cons_eq_append_conv) 
          then show ?thesis by simp
      next
        case False
          then show ?thesis by arith
      qed
      from Minimal(1)
      obtain u v where uv: "LeftDerivation [\<SS>] (take K D) (u @ [N] @ v) \<and> derives u []" by blast
      from nonzero_K have "take K D \<noteq> []"
        using Minimal.hyps(2) less_nat_zero_code nat_neq_iff take_eq_Nil uv by force 
      then have "\<exists> E e. (take K D) = E@[e]" using rev_exhaust by blast 
      then obtain E e where Ee: "take K D = E@[e]" by blast
      with uv have "\<exists> x. LeftDerivation [\<SS>] E x \<and> LeftDerives1 x (fst e) (snd e) (u @ [N] @ v)"
        by (simp add: LeftDerivation_append) 
      then obtain x where x: "LeftDerivation [\<SS>] E x \<and> LeftDerives1 x (fst e) (snd e) (u @ [N] @ v)"  
        by blast
      then have "\<exists> w M. x = M#w \<and> is_nonterminal M"
        using Derives1_nonterminal_head' LeftDerives1_implies_Derives1 assms(2) uv by blast 
      then obtain w M where split_x: "x = M#w" and is_nonterminal_M: "is_nonterminal M" by blast
      from Ee nonzero_K have E: "E = take (K - 1) D"
        by (metis Minimal.hyps(2) butlast_snoc butlast_take dual_order.strict_implies_order 
          le_less_linear take_all uv) 
      have "leftmost (fst e) (M#w)" using x LeftDerives1_def split_x by blast 
      with is_nonterminal_M have fst_e: "fst e = 0" 
        by (simp add: leftmost_cons_nonterminal leftmost_unique) 
      have Derives1: "Derives1 x 0 (snd e) (u @ [N] @ v)"
        using LeftDerives1_implies_Derives1 fst_e x by auto 
      have x_splits_at: "splits_at x 0 [] M w"
        by (simp add: split_x splits_at_def)       
      from Derives1 x_splits_at 
      have pq: "\<exists>p q. u = [] @ p \<and> v = q @ w \<and> snd (snd e) = p @ [N] @ q"
      proof (induct rule: Derives1_X_is_part_of_rule)
        case (Suffix \<alpha>) thus ?case by blast
      next
        case (Prefix \<beta>)
          then have derives_\<beta>: "derives \<beta> []"
            using Derives1_implies_derives1 derives1_implies_derives derives_trans uv by blast 
          with Prefix(1) x Minimal E nonzero_K show "False"
            by (meson diff_less less_nat_zero_code less_one nat_neq_iff)
      qed
      from this[simplified] obtain q where q: "v = q @ w \<and> snd (snd e) = u @ N # q" by blast
      have M_def: "fst (snd e) = M"
        using Derives1 Derives1_nonterminal x_splits_at by blast 
      show ?case
        apply (rule_tac x="K-1" in exI)
        apply (rule_tac x="M" in exI)
        apply (rule_tac x="snd (snd e)" in exI)
        apply (rule_tac x="u" in exI)
        apply (rule_tac x="q" in exI)
        apply (rule_tac x="w" in exI)
        by (metis Derives1 Derives1_rule E Ee M_def One_nat_def Suc_pred pq append_Nil 
          append_same_eq dual_order.strict_implies_order le_less_linear nonzero_K not_Cons_self2 
          not_gr0 not_less_eq prod.collapse q self_append_conv split_x take_all uv x)
  qed
qed      

lemma head_of_item_\<beta>_is_next_symbol: 
  "wellformed_item x \<Longrightarrow> item_\<beta> x = t#\<delta> \<Longrightarrow> next_symbol x = Some t"
  using next_symbol_def next_symbol_starts_item_\<beta> wellformed_complete_item_\<beta> by fastforce
 
lemma next_symbol_predicts: "next_symbol x = Some N \<Longrightarrow> (N, a) \<in> \<RR> \<Longrightarrow> k = item_end x \<Longrightarrow> 
  init_item (N, a) k \<in> Predict k {x}"
using Predict_def bin_def by auto

lemma thmD7_LeftDerivation: "LeftDerivation [\<SS>] D (N#\<gamma>) \<Longrightarrow> is_nonterminal N \<Longrightarrow> (N, \<alpha>) \<in> \<RR> \<Longrightarrow> 
  init_item (N, \<alpha>) 0 \<in> \<pi> 0 {} Init"
proof (induct "length D" arbitrary: D N \<gamma> \<alpha> rule: less_induct)
  case less
    let ?trivial = "\<SS> = N"
    have "?trivial \<or> \<not> ?trivial" by blast
    then show ?case 
    proof (induct rule: disjCases2)
      case 1
        then have "init_item (N, \<alpha>) 0 \<in> Init"
          apply (subst Init_def) 
          by (auto simp add: less)
        then show ?case
          by (meson \<pi>_regular contra_subsetD regular_implies_setmonotone subset_setmonotone)
    next
      case 2
        from thmD7_helper[OF less(2) less(3) 2]
        obtain n M a a1 a2 w where "n < length D" and  "(M, a) \<in> \<RR>" and  
          "LeftDerivation [\<SS>] (take n D) (M # w)" and "a = a1 @ [N] @ a2" and "derives a1 []" 
          by blast
        note M = this
        let ?x = "init_item (M, a) 0"
        have x_dom: "?x \<in> \<pi> 0 {} Init"
          apply (rule less(1)[OF _ M(3) _ M(2)])
          using M(1) apply simp
          using M(2) by simp
        have wellformed_x: "wellformed_item ?x" by (simp add: M(2))
        let ?y = "inc_dot (length a1) ?x"
        have "?y \<in> \<pi> 0 {} {?x}"
          apply (rule thmD6[where \<omega>="[N] @ a2"])
          using wellformed_x by (auto simp add: M)
        with x_dom have y_dom: "?y \<in> \<pi> 0 {} Init"
          using \<pi>_subset_elem_trans empty_subsetI insert_subset by blast
        have wellformed_y: "wellformed_item ?y"
          using M(4) wellformed_inc_dot wellformed_x by auto          
        have "item_\<beta> ?y = N#a2" by (simp add: M(4) item_\<beta>_def) 
        then have next_symbol_y: "next_symbol ?y = Some N"
          by (simp add: head_of_item_\<beta>_is_next_symbol wellformed_y)
        let ?z = "init_item (N, \<alpha>) 0"
        have "?z \<in> Predict 0 {?y}"
          by (simp add: less.prems(3) next_symbol_predicts next_symbol_y)
        then have "?z \<in> \<pi> 0 {} {?y}" using Predict_subset_\<pi> by auto
        with y_dom show "?z \<in> \<pi> 0 {} Init"
          using \<pi>_subset_elem_trans empty_subsetI insert_subset by blast 
    qed
qed      
 
theorem thmD7: "is_derivation (N#\<gamma>) \<Longrightarrow> is_nonterminal N \<Longrightarrow> (N, \<alpha>) \<in> \<RR> \<Longrightarrow> 
  init_item (N, \<alpha>) 0 \<in> \<pi> 0 {} Init"
by (metis \<L>\<^sub>P_is_word derives_implies_leftderives_cons empty_in_\<L>\<^sub>P is_derivation_def 
  leftderives_implies_LeftDerivation self_append_conv2 thmD7_LeftDerivation)
         
end

end
