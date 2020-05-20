theory TheoremD6
imports TheoremD5
begin

context LocalLexing begin

definition inc_dot :: "nat \<Rightarrow> item \<Rightarrow> item"
where
  "inc_dot d x = Item (item_rule x) (item_dot x + d) (item_origin x) (item_end x)"

lemma inc_dot_0[simp]: "inc_dot 0 x = x"
  by (simp add: inc_dot_def)

lemma Predict_mk_regular1: 
  "\<exists> (P :: rule \<Rightarrow> item \<Rightarrow> bool) F. Predict k = mk_regular1 P F"
proof -
  let ?P = "\<lambda> r x::item. r \<in> \<RR> \<and> item_end x = k \<and> next_symbol x = Some(fst r)"
  let ?F = "\<lambda> r (x::item). init_item r k"
  show ?thesis
    apply (rule_tac x="?P" in exI)
    apply (rule_tac x="?F" in exI)
    apply (rule_tac ext)
    by (auto simp add: mk_regular1_def bin_def Predict_def)
qed

lemma Complete_mk_regular2: 
  "\<exists> (P :: dummy \<Rightarrow> item \<Rightarrow> item \<Rightarrow> bool) F. Complete k = mk_regular2 P F"
proof -
  let ?P = "\<lambda> (r::dummy) x y. item_end x = item_origin y \<and> item_end y = k \<and> is_complete y \<and> 
     next_symbol x = Some (item_nonterminal y)"
  let ?F = "\<lambda> (r::dummy) x y. inc_item x k"
  show ?thesis
    apply (rule_tac x="?P" in exI)
    apply (rule_tac x="?F" in exI)
    apply (rule_tac ext)
    by (auto simp add: mk_regular2_def bin_def Complete_def)
qed

lemma Scan_mk_regular1:
  "\<exists> (P :: token \<Rightarrow> item \<Rightarrow> bool) F. Scan T k = mk_regular1 P F"
proof -
  let ?P = "\<lambda> (tok::token) (x::item). item_end x = k \<and> tok \<in> T \<and> next_symbol x = Some (fst tok)"
  let ?F = "\<lambda> (tok::token) (x::item). inc_item x (k + length (snd tok))"
  show ?thesis
    apply (rule_tac x="?P" in exI)
    apply (rule_tac x="?F" in exI)
    apply (rule_tac ext)
    by (auto simp add: mk_regular1_def bin_def Scan_def)
qed

lemma Predict_regular: "regular (Predict k)" 
  by (metis Predict_mk_regular1 regular1)
  
lemma Complete_regular: "regular (Complete k)" 
  by (metis Complete_mk_regular2 regular2) 

lemma Scan_regular: "regular (Scan T k)"
  by (metis Scan_mk_regular1 regular1)

lemma \<pi>_functional: "\<pi> k T = limit ((Scan T k) o (Complete k) o (Predict k))"
proof -
  have "\<pi> k T = limit (\<lambda> I. Scan T k (Complete k (Predict k I)))"
    using \<pi>_def by blast
  moreover have "(\<lambda> I. Scan T k (Complete k (Predict k I))) = 
     (Scan T k) o (Complete k) o (Predict k)" 
     apply (rule ext)
     by simp
  ultimately show ?thesis by simp
qed

lemma \<pi>_step_regular: "regular ((Scan T k) o (Complete k) o (Predict k))"
  by (simp add: Complete_regular Predict_regular Scan_regular regular_comp)
  
lemma \<pi>_regular: "regular (\<pi> k T)"
  by (simp add: \<pi>_functional \<pi>_step_regular regular_limit)

lemma \<pi>_fix: "Scan T k (Complete k (Predict k (\<pi> k T I))) = \<pi> k T I"
  using \<pi>_functional \<pi>_step_regular regular_fixpoint by fastforce

lemma \<pi>_fix': "((Scan T k) o (Complete k) o (Predict k)) (\<pi> k T I) = \<pi> k T I"
  using \<pi>_functional \<pi>_step_regular regular_fixpoint by fastforce

lemma setmonotone_cases:
  assumes "setmonotone f"
  shows "f X = X \<or> X \<subset> f X"
using assms elem_setmonotone by fastforce

lemma distribute_fixpoint_over_setmonotone_comp:
  assumes f: "setmonotone f"
  assumes g: "setmonotone g"
  assumes fixpoint: "(f o g) I = I"
  shows "f I = I \<and> g I = I"
proof -
  from setmonotone_cases[OF g, where X=I] show ?thesis
  proof(induct rule: disjCases2)
    case 1
      thus ?case using fixpoint by simp
  next
    case 2
      with f have "I \<subset> (f o g) I"
        by (metis comp_apply fixpoint less_asym' setmonotone_cases)
      with fixpoint have "False" by simp
      then show ?case by blast
  qed
qed

lemma distribute_fixpoint_over_setmonotone_comp_3:
  assumes f: "setmonotone f"
  assumes g: "setmonotone g"
  assumes h: "setmonotone h"
  assumes fixpoint: "(f o g o h) I = I"
  shows "f I = I \<and> g I = I \<and> h I = I"
by (meson distribute_fixpoint_over_setmonotone_comp f fixpoint g h setmonotone_comp)

lemma Predict_\<pi>_fix: "Predict k (\<pi> k T I) = \<pi> k T I"
by (meson Complete_regular Predict_regular Scan_regular \<pi>_fix' 
  distribute_fixpoint_over_setmonotone_comp_3 regular_implies_setmonotone)

lemma Scan_\<pi>_fix: "Scan T k (\<pi> k T I) = \<pi> k T I"
by (meson Complete_regular Predict_regular Scan_regular \<pi>_fix' 
  distribute_fixpoint_over_setmonotone_comp_3 regular_implies_setmonotone)

lemma Complete_\<pi>_fix: "Complete k (\<pi> k T I) = \<pi> k T I"
by (meson Complete_regular Predict_regular Scan_regular \<pi>_fix' 
  distribute_fixpoint_over_setmonotone_comp_3 regular_implies_setmonotone)

lemma \<pi>_idempotent: "\<pi> k T (\<pi> k T I) = \<pi> k T I"
  by (simp add: \<pi>_functional \<pi>_step_regular limit_is_idempotent)

lemma derivation_shift_identity[simp]: "derivation_shift D 0 0 = D"
  by (simp add: derivation_shift_def)

lemma Derivation_skip_prefix: "Derivation (u@v) D w \<Longrightarrow> derivation_ge D (length u) \<Longrightarrow> 
  Derivation v (derivation_shift D (length u) 0) (drop (length u) w)"
proof (induct D arbitrary: u v w)
  case Nil
    thus ?case by (simp add: append_eq_conv_conj) 
next
  case (Cons d D)
    from Cons have "\<exists>x. Derives1 (u@v) (fst d) (snd d) x \<and> Derivation x D w" by auto
    then obtain x where x: "Derives1 (u@v) (fst d) (snd d) x \<and> Derivation x D w" by blast
    from Cons have d: "fst d \<ge> length u" and D: "derivation_ge D (length u)"
      using derivation_ge_cons apply blast
      using Cons.prems(2) derivation_ge_cons by blast
    have "\<exists> x'. x = u@x'" by (metis append_eq_conv_conj d le_Derives1_take x)   
    then obtain x' where x': "x = u@x'" by blast
    show ?case
      apply simp
      apply (rule_tac x="x'" in exI)
      using Cons.hyps D Derives1_skip_prefix d x x' by blast
qed

lemma leftmost_skip_prefix: "leftmost i (u@v) \<Longrightarrow> i \<ge> length u \<Longrightarrow> leftmost (i - length u) v"
by (simp add: leftmost_def less_diff_conv2 nth_append)
 
lemma LeftDerivation_skip_prefix: "LeftDerivation (u@v) D w \<Longrightarrow> derivation_ge D (length u) \<Longrightarrow> 
  LeftDerivation v (derivation_shift D (length u) 0) (drop (length u) w)"
proof (induct D arbitrary: u v w)
  case Nil
    thus ?case by (simp add: append_eq_conv_conj) 
next
  case (Cons d D)
    from Cons have "\<exists>x. LeftDerives1 (u@v) (fst d) (snd d) x \<and> LeftDerivation x D w" by auto
    then obtain x where x: "LeftDerives1 (u@v) (fst d) (snd d) x \<and> LeftDerivation x D w" by blast
    from Cons have d: "fst d \<ge> length u" and D: "derivation_ge D (length u)"
      using derivation_ge_cons apply blast
      using Cons.prems(2) derivation_ge_cons by blast
    have "\<exists> x'. x = u@x'"
      by (metis LeftDerives1_implies_Derives1 append_eq_conv_conj d le_Derives1_take x) 
    then obtain x' where x': "x = u@x'" by blast
    have leftmost: "leftmost (fst d) (u@v)" using LeftDerives1_def x by blast 
    have 1: "LeftDerives1 v (fst d - length u) (snd d) x'"
      apply (auto simp add: LeftDerives1_def)
      apply (simp add: leftmost d leftmost_skip_prefix)
      using Derives1_skip_prefix LeftDerives1_implies_Derives1 d x x' by blast
    have 2: "LeftDerivation x' (derivation_shift D (length u) 0) (drop (length u) w)"
      using Cons.hyps D x x' by blast      
    show ?case
      apply simp
      apply (rule_tac x="x'" in exI)
      using 1 2 by blast
qed

lemma splits_at_append: "splits_at u i u1 N u2 \<Longrightarrow> splits_at (u@v) i u1 N (u2@v)"
by (auto simp add: splits_at_def)

lemma LeftDerives1_append_leftmost_unique: "LeftDerives1 (a@b) i r c \<Longrightarrow> leftmost j a \<Longrightarrow> i = j"
  by (meson LeftDerives1_def leftmost_cons_less leftmost_def leftmost_unique)
  
lemma drop_derivation_shift: 
  "drop n (derivation_shift D left right) = derivation_shift (drop n D) left right"
by (auto simp add: derivation_shift_def drop_map)

lemma take_derivation_shift: 
  "take n (derivation_shift D left right) = derivation_shift (take n D) left right"
by (auto simp add: derivation_shift_def take_map)

lemma derivation_shift_0_shift: "derivation_shift (derivation_shift D left1 0) left2 right2 = 
  derivation_shift D (left1 + left2) right2"
by (auto simp add: derivation_shift_def)

lemma splits_at_append_prefix:
  "splits_at v i \<alpha> N \<beta> \<Longrightarrow> splits_at (u@v) (i + length u) (u@\<alpha>) N \<beta>"
  apply (auto simp add: splits_at_def)
  by (simp add: nth_append)
  
lemma splits_at_implies_Derives1: "splits_at \<delta> i \<alpha> N \<beta> \<Longrightarrow> is_sentence \<delta> \<Longrightarrow> r\<in> \<RR> \<Longrightarrow> fst r = N 
 \<Longrightarrow> Derives1 \<delta> i r (\<alpha>@(snd r)@\<beta>)"
by (metis (no_types, lifting) Derives1_def is_sentence_concat length_take 
  less_or_eq_imp_le min.absorb2 prod.collapse splits_at_combine splits_at_def)

lemma Derives1_append_prefix: 
  assumes Derives1: "Derives1 v i r w"
  assumes u: "is_sentence u"
  shows "Derives1 (u@v) (i + length u) r (u@w)"
proof -
  have "\<exists> \<alpha> N \<beta>. splits_at v i \<alpha> N \<beta>" using assms splits_at_ex by auto
  then obtain \<alpha> N \<beta> where split_v: "splits_at v i \<alpha> N \<beta>" by blast
  have split_w: "w = \<alpha>@(snd r)@\<beta>" using assms split_v splits_at_combine_dest by blast 
  have split_uv: "splits_at (u@v) (i + length u) (u@\<alpha>) N \<beta>"
    by (simp add: split_v splits_at_append_prefix)
  have is_sentence_uv: "is_sentence (u@v)"
    using Derives1 Derives1_sentence1 is_sentence_concat u by blast 
  show ?thesis
    by (metis Derives1 Derives1_nonterminal Derives1_rule append_assoc is_sentence_uv 
        split_uv split_v split_w splits_at_implies_Derives1)
qed

lemma leftmost_prepend_word: "leftmost i v \<Longrightarrow> is_word u \<Longrightarrow> leftmost (i + length u) (u@v)"
by (simp add: leftmost_def nth_append)

lemma LeftDerives1_append_prefix: 
  assumes Derives1: "LeftDerives1 v i r w"
  assumes u: "is_word u"
  shows "LeftDerives1 (u@v) (i + length u) r (u@w)"
proof -
  have 1: "Derives1 v i r w"
    by (simp add: Derives1 LeftDerives1_implies_Derives1) 
  have 2: "leftmost i v"
    using Derives1 LeftDerives1_def by blast  
  have 3: "is_sentence u" using u by fastforce 
  have 4: "Derives1 (u@v) (i + length u) r (u@w)"
    by (simp add: "1" "3" Derives1_append_prefix) 
  have 5: "leftmost (i + length u) (u@v)"
    by (simp add: "2" leftmost_prepend_word u) 
  show ?thesis
    by (simp add: "4" "5" LeftDerives1_def)
qed     

lemma Derivation_append_prefix: "Derivation v D w \<Longrightarrow> is_sentence u \<Longrightarrow>
  Derivation (u@v) (derivation_shift D 0 (length u)) (u@w)"
proof (induct D arbitrary: u v w)
  case Nil thus ?case by auto
next
  case (Cons d D)
    then have "\<exists> x. Derives1 v (fst d) (snd d) x \<and> Derivation x D w" by auto
    then obtain x where x: "Derives1 v (fst d) (snd d) x \<and> Derivation x D w" by blast
    with Cons have induct: "Derivation (u@x) (derivation_shift D 0 (length u)) (u@w)" by auto
    have Derives1: "Derives1 (u@v) ((fst d) + length u) (snd d) (u@x)"
      by (simp add: Cons.prems(2) Derives1_append_prefix x) 
    show ?case 
      apply simp
      apply (rule_tac x="u@x" in exI)
      by (simp add: Cons.hyps Cons.prems(2) Derives1 x)
qed     

lemma LeftDerivation_append_prefix: "LeftDerivation v D w \<Longrightarrow> is_word u \<Longrightarrow> 
  LeftDerivation (u@v) (derivation_shift D 0 (length u)) (u@w)"
proof (induct D arbitrary: u v w)
  case Nil thus ?case by auto
next
  case (Cons d D)
    then have "\<exists> x. LeftDerives1 v (fst d) (snd d) x \<and> LeftDerivation x D w" by auto
    then obtain x where x: "LeftDerives1 v (fst d) (snd d) x \<and> LeftDerivation x D w" by blast
    with Cons have induct: "LeftDerivation (u@x) (derivation_shift D 0 (length u)) (u@w)" by auto
    have Derives1: "LeftDerives1 (u@v) ((fst d) + length u) (snd d) (u@x)"
      by (simp add: Cons.prems(2) LeftDerives1_append_prefix x) 
    show ?case 
      apply simp
      apply (rule_tac x="u@x" in exI)
      by (simp add: Cons.hyps Cons.prems(2) Derives1 x)
qed     

lemma derivation_ge_shift_simp: "derivation_ge D i \<Longrightarrow> i \<ge> l \<Longrightarrow> r \<ge> l \<Longrightarrow> 
   derivation_shift D l r = derivation_shift D 0 (r - l)"
proof (induct D)
  case Nil thus ?case by auto
next
  case (Cons d D) 
  have fst_d: "fst d \<ge> l"
    using Cons.prems(1) Cons.prems(2) derivation_ge_cons le_trans by blast 
  show ?case
    apply auto
    using Cons fst_d apply arith 
    using Cons derivation_ge_cons apply auto
    done
qed

lemma append_dropped_prefix: "is_prefix u v \<Longrightarrow> drop (length u) v = w \<Longrightarrow> u@w = v"
using is_prefix_unsplit by blast 

lemma derivation_ge_shift_plus:
  assumes "derivation_ge D u"
  assumes "derivation_ge (derivation_shift D u 0) v"
  shows "derivation_ge D (u + v)"
proof -
  from assms show ?thesis
    apply (auto simp add: derivation_ge_def derivation_shift_def)
    by fastforce
qed    

lemma LeftDerivation_breakdown: 
  "LeftDerivation (u@v) D w \<Longrightarrow> \<exists> n w1 w2. w = w1 @ w2 \<and> 
     LeftDerivation u (take n D) w1 \<and>
     derivation_ge (drop n D) (length w1) \<and>
     LeftDerivation v (derivation_shift (drop n D) (length w1) 0) w2"
proof (induct "length D" arbitrary: u v D w)
  case 0
    then have D: "D = []" by auto
    with 0 have "u@v = w" by auto
    with D show ?case
      apply (rule_tac x=0 in exI)
      apply (rule_tac x="u" in exI)
      apply (rule_tac x="v" in exI)
      by auto
next
  case (Suc l)
    then have "\<exists> d D'. D = d#D'"
      by (metis LeftDerivation.elims(2) length_0_conv nat.simps(3)) 
    then obtain d D' where D_split: "D = d#D'" by blast
    from Suc have is_sentence_uv: "is_sentence (u@v)"
      by (metis D_split Derives1_sentence1 LeftDerivation.simps(2) LeftDerives1_implies_Derives1)
    then have is_sentence_u: "is_sentence u" and is_sentence_v: "is_sentence v"
      by (simp add: is_sentence_concat)+   
    have "is_word u \<or> (\<not> is_word u)" by blast 
    then show ?case 
      proof(induct rule: disjCases2)
        case 1
          then have derivation_ge_u: "derivation_ge D (length u)"
            using LeftDerivation_implies_Derivation Suc.prems is_word_Derivation_derivation_ge by blast
          have is_prefix: "is_prefix u w"
            using "1.hyps" LeftDerivation_implies_leftderives Suc.prems 
              derives_word_is_prefix leftderives_implies_derives by blast          
          have u_w: "w = u @ (drop (length u) w)"
            by (metis "1.hyps" LeftDerivation_implies_leftderives Suc.prems 
              derives_word_is_prefix is_prefix_unsplit leftderives_implies_derives)  
          show ?case
            apply (rule_tac x="0" in exI)
            apply (rule_tac x="u" in exI)
            apply (rule_tac x="drop (length u) w" in exI)
            apply (auto)
            apply (rule u_w)
            apply (rule derivation_ge_u)
            by (simp add: LeftDerivation_skip_prefix Suc.prems derivation_ge_u)
      next
        case 2
          with is_sentence_u have "\<exists> i u1 N u2. splits_at u i u1 N u2 \<and> leftmost i u"
            using leftmost_def nonword_leftmost_exists splits_at_def by auto
          then obtain i u1 N u2 where split_u: "splits_at u i u1 N u2 \<and> leftmost i u" by blast
          have is_word_u1: "is_word u1" by (metis leftmost_def split_u splits_at_def) 
          have "LeftDerivation (u@v) (d#D') w"  using D_split Suc.prems by blast 
          then have "\<exists> x. LeftDerives1 (u@v) (fst d) (snd d) x \<and> LeftDerivation x D' w"
            by simp  
          then obtain x where x: "LeftDerives1 (u@v) (fst d) (snd d) x \<and> LeftDerivation x D' w"
            by blast
          then have fst_d_eq_i: "fst d = i" using 
            splits_at_combine LeftDerives1_append_leftmost_unique split_u
            by metis
          have split_uv: "splits_at (u@v) i u1 N (u2@v)" by (simp add: split_u splits_at_append) 
          have split_x: "x = u1 @ ((snd (snd d)) @ u2 @ v)"
            using LeftDerives1_implies_Derives1 fst_d_eq_i split_uv 
              splits_at_combine_dest x by blast 
          have derivation_ge_D': "derivation_ge D' (length u1)"
            using LeftDerivation_implies_Derivation is_word_Derivation_derivation_ge 
              leftmost_def split_u split_x splits_at_def x by fastforce
          have D1: "LeftDerivation ((snd (snd d)) @ u2 @ v) (derivation_shift D' (length u1) 0) 
            (drop (length u1) w)"
            using LeftDerivation_skip_prefix derivation_ge_D' split_x x by blast 
          then have D2: "LeftDerivation (((snd (snd d)) @ u2) @ v) (derivation_shift D' (length u1) 0) 
            (drop (length u1) w)" by auto
          have "l = length (derivation_shift D' (length u1) 0)"
            using D_split Suc.hyps(2) by auto
          from Suc(1)[OF this D2] obtain n w1 w2 where induct:
            "drop (length u1) w = w1 @ w2 \<and> 
             LeftDerivation (snd (snd d) @ u2) 
               (take n (derivation_shift D' (length u1) 0)) w1 \<and> 
             derivation_ge (drop n (derivation_shift D' (length u1) 0)) (length w1) \<and>
             LeftDerivation v (derivation_shift (drop n (derivation_shift D' (length u1) 0)) 
               (length w1) 0) w2" by blast
          have derivation_ge_D'_u1_w1: "derivation_ge (drop n D') (length u1 + length w1)"
          proof -
            from induct have 1: "derivation_ge (derivation_shift (drop n D') (length u1) 0) (length w1)"
              apply (subst drop_derivation_shift[symmetric])
              by blast
            have 2: "derivation_ge (drop n D') (length u1)"
              by (metis append_take_drop_id derivation_ge_D' derivation_ge_append)
            show ?thesis using 1 2 derivation_ge_shift_plus by blast
          qed
          have "LeftDerivation (u1@(snd (snd d) @ u2)) (derivation_shift 
                (take n (derivation_shift D' (length u1) 0)) 0 (length u1)) (u1@w1)"
          using induct LeftDerivation_append_prefix is_word_u1 by blast  
          then have der1: "LeftDerivation (u1@(snd (snd d) @ u2)) 
              (derivation_shift (take n D') (length u1) (length u1)) (u1@w1)"
            using take_derivation_shift derivation_shift_0_shift by auto 
          have eq1: "derivation_shift (take n D') (length u1) (length u1) = take n D'"
            apply (subst derivation_ge_shift_simp[where i = "length u1"])
            apply auto
            by (metis append_take_drop_id derivation_ge_D' derivation_ge_append)
          from der1 eq1 have der2: "LeftDerivation (u1@(snd (snd d) @ u2)) (take n D') (u1@w1)" 
            by auto
          have eq2: "take (Suc n) D = d#(take n D')"
            by (simp add: D_split)  
          have der3: "LeftDerivation u (take (Suc n) D) (u1@w1)"
            apply (simp add: eq2)
            apply (rule_tac x="u1@(snd (snd d) @ u2)" in exI)
            by (metis Derives1_skip_suffix LeftDerives1_def append_assoc der2 fst_d_eq_i 
              split_u split_x splits_at_def x)
          have "is_prefix u1 w"
            using LeftDerivation_implies_leftderives derives_word_is_prefix is_word_u1 
              leftderives_implies_derives split_x x by blast 
          then have eq3: "u1 @ (w1@w2) = w"  
            apply (rule_tac append_dropped_prefix)
            apply (auto simp add: induct)
            done
          show ?case
            apply (rule_tac x="Suc n" in exI)
            apply (rule_tac x="u1@w1" in exI)
            apply (rule_tac x="w2" in exI)
            apply auto
            apply (simp add: eq3)
            apply (simp add: der3)
            apply (simp add: D_split)
            apply (rule derivation_ge_D'_u1_w1)
            apply (simp add: D_split)
            using induct derivation_shift_0_shift drop_derivation_shift apply auto
            done
      qed
qed
                  
lemma Derives1_terminals_stay:
  assumes Derives1: "Derives1 u i r v"
  assumes t_dom: "t \<in> set u"
  assumes terminal: "is_terminal t"
  shows "t \<in> set v"
proof -
  have "\<exists> \<alpha> \<beta> N. splits_at u i \<alpha> N \<beta>" using Derives1 splits_at_ex by blast 
  then obtain \<alpha> \<beta> N where split_u: "splits_at u i \<alpha> N \<beta>" by blast
  then have "t \<in> set (\<alpha> @ [N] @ \<beta>)" using splits_at_combine t_dom by auto
  then have t_possible_locations: "t \<in> set \<alpha> \<or> t = N \<or> t \<in> set \<beta>" by auto
  have is_nonterminal: "is_nonterminal N" using Derives1 Derives1_nonterminal split_u by auto 
  with t_possible_locations terminal have t_locations: "t \<in> set \<alpha> \<or> t \<in> set \<beta>"
    using is_terminal_nonterminal by blast 
  from Derives1 split_u have "v = \<alpha> @ (snd r) @ \<beta>" by (simp add: splits_at_combine_dest) 
  with t_locations show ?thesis by auto
qed

lemma Derivation_terminals_stay: "Derivation u D v \<Longrightarrow> t \<in> set u \<Longrightarrow> is_terminal t \<Longrightarrow> t \<in> set v"
proof (induct D arbitrary: u v)
  case Nil thus ?case by auto
next
  case (Cons d D)
  then have "\<exists> x. Derives1 u (fst d) (snd d) x \<and> Derivation x D v" by auto
  then obtain x where x: "Derives1 u (fst d) (snd d) x \<and> Derivation x D v" by auto
  show ?case using Cons Derives1_terminals_stay x by blast
qed
    
lemma Derivation_empty_no_terminals: "Derivation u D [] \<Longrightarrow> t \<in> set u \<Longrightarrow> is_nonterminal t"
  by (metis Ball_set Derivation_implies_derives Derivation_terminals_stay 
    derives_is_sentence is_sentence_def is_symbol_distinct list.pred_inject(1))

lemma mono_subset_elem: "mono f \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<in> f A \<Longrightarrow> x \<in> f B" using mono_def by blast

lemma wellformed_inc_dot: "wellformed_item x \<Longrightarrow> item_dot x + d \<le> length (item_rhs x) \<Longrightarrow>
  wellformed_item(inc_dot d x)"
by (simp add: inc_dot_def item_rhs_def wellformed_item_def)

lemma init_item_dot[simp]: "item_dot (init_item r k) = 0"
  by (simp add: init_item_def)

lemma init_item_rhs[simp]: "item_rhs (init_item r k) = snd r"
  by (simp add: init_item_def item_rhs_def)

lemma init_item_\<beta>[simp]: "item_\<beta> (init_item r k) = snd r"
  by (simp add: item_\<beta>_def)

lemma mono_\<pi>: "mono (\<pi> k T)"
  by (simp add: \<pi>_regular regular_implies_mono)

lemma \<pi>_subset_elem_trans: 
  assumes Y: "Y \<subseteq> \<pi> k T X"
  assumes z: "z \<in> \<pi> k T Y"
  shows "z \<in>  \<pi> k T X"
proof -
  from Y have "\<pi> k T Y \<subseteq> \<pi> k T (\<pi> k T X)" by (simp add: monoD mono_\<pi>) 
  then have "\<pi> k T Y \<subseteq> \<pi> k T X" using \<pi>_idempotent by blast 
  with z show ?thesis using contra_subsetD by blast 
qed

lemma inc_dot_origin[simp]: "item_origin (inc_dot d x) = item_origin x"
  by (simp add: inc_dot_def)

lemma inc_dot_end[simp]: "item_end (inc_dot d x) = item_end x"
  by (simp add: inc_dot_def)

lemma inc_dot_rhs[simp]: "item_rhs (inc_dot d x) = item_rhs x"
  by (simp add: inc_dot_def item_rhs_def)

lemma inc_dot_dot[simp]: "item_dot (inc_dot d x) = item_dot x + d"
  by (simp add: inc_dot_def)

lemma inc_dot_nonterminal[simp]: "item_nonterminal (inc_dot d x) = item_nonterminal x"
  by (simp add: inc_dot_def item_nonterminal_def)
  
lemma Predict_subset_\<pi>: "Predict k X \<subseteq> \<pi> k T X"
proof -
  have "setmonotone (\<pi> k T)"
    by (simp add: \<pi>_regular regular_implies_setmonotone) 
  then have s: "X \<subseteq> \<pi> k T X" by (simp add: subset_setmonotone) 
  have "mono (Predict k)" by (simp add: Predict_regular regular_implies_mono) 
  with s have "Predict k X \<subseteq> Predict k (\<pi> k T X)" by (simp add: monoD) 
  then show "Predict k X \<subseteq> \<pi> k T X" by (simp add: Predict_\<pi>_fix)
qed 

lemma Complete_subset_\<pi>: "Complete k X \<subseteq> \<pi> k T X"
proof -
  have "setmonotone (\<pi> k T)"
    by (simp add: \<pi>_regular regular_implies_setmonotone) 
  then have s: "X \<subseteq> \<pi> k T X" by (simp add: subset_setmonotone) 
  have "mono (Complete k)" by (simp add: Complete_regular regular_implies_mono) 
  with s have "Complete k X \<subseteq> Complete k (\<pi> k T X)" by (simp add: monoD) 
  then show "Complete k X \<subseteq> \<pi> k T X" by (simp add: Complete_\<pi>_fix)
qed 

lemma inc_inc_dot[simp]: "inc_dot a (inc_dot b x) = inc_dot (a + b) x"
  by (simp add: inc_dot_def)

lemma thmD6_Left: "wellformed_item x \<Longrightarrow> item_\<beta> x = \<delta> @ \<omega> \<Longrightarrow> item_end x = k \<Longrightarrow> 
  LeftDerivation \<delta> D [] \<Longrightarrow> inc_dot (length \<delta>) x \<in> \<pi> k {} {x}"
proof (induct "length D" arbitrary: x \<delta> \<omega> D rule: less_induct)
  case less
    have "length \<delta> = 0 \<or> length \<delta> = 1 \<or> length \<delta> \<ge> 2" by arith
    then show ?case
    proof (induct rule: disjCases3)
      case 1
        then have "\<delta> = []" by auto
        then show ?case by (simp add: \<pi>_regular elem_setmonotone regular_implies_setmonotone)
    next
      case 2
        then have "\<exists> N. \<delta> = [N]" 
          by (metis One_nat_def append_self_conv2 drop_all id_take_nth_drop 
            le_numeral_extra(4) lessI take_0) 
        then obtain N where N: "\<delta> = [N]" by blast
        then have "N \<in> set \<delta>" by auto
        then have is_nonterminal_N: "is_nonterminal N" using Derivation_empty_no_terminals 
          LeftDerivation_implies_Derivation less.prems(4) by blast 
        have "D \<noteq> []" using LeftDerivation.elims(2) N less.prems(4) by blast 
        then have "\<exists> e E. D = e#E" using LeftDerivation.elims(2) less.prems(4) by blast 
        then obtain e E where eE: "D = e#E" by blast
        then have "\<exists> \<gamma>. LeftDerives1 \<delta> (fst e) (snd e) \<gamma> \<and> 
          LeftDerivation \<gamma> E []" using LeftDerivation.simps(2) less.prems(4) by blast 
        then obtain \<gamma> where \<gamma>: "LeftDerives1 \<delta> (fst e) (snd e) \<gamma> \<and> LeftDerivation \<gamma> E []" by blast
        with N have \<gamma>_def: "\<gamma> = snd (snd e)"
          by (metis "2.hyps" Derives1_split LeftDerives1_def One_nat_def append_Cons 
            append_Nil append_Nil2 leftmost_def length_0_conv less_nat_zero_code linorder_neqE_nat 
            list.inject not_less_eq) 
        have next_symbol_x: "next_symbol x = Some N"
          using N less.prems(1) less.prems(2) next_symbol_def next_symbol_starts_item_\<beta> 
            wellformed_complete_item_\<beta> by fastforce  
        have x_subset: "{x} \<subseteq> \<pi> k {} {x}"
          using \<pi>_regular regular_implies_setmonotone subset_setmonotone by blast 
        let ?y = "init_item (snd e) k"
        have "?y \<in> Predict k {x}" 
          apply (simp add: Predict_def)
          apply (rule disjI2)
          apply (rule_tac x="fst (snd e)" in exI)
          apply (rule_tac x="snd (snd e)" in exI)
          apply auto
          using Derives1_rule LeftDerives1_implies_Derives1 \<gamma> apply blast
          apply (rule_tac x=x in exI)
          by (metis (mono_tags, lifting) Derives1_split LeftDerives1_def N \<gamma> 
              append.simps(1) append.simps(2) bin_def is_nonterminal_N leftmost_cons_nonterminal 
              leftmost_unique length_greater_0_conv less.prems(3) less_nat_zero_code 
              list.inject mem_Collect_eq next_symbol_x singletonI)
       then have y_dom: "?y \<in> \<pi> k {} {x}" using Predict_subset_\<pi> by blast 
       let ?z = "inc_dot (length \<gamma>) ?y"
       have "item_dot ?y = 0" and "item_rhs ?y = \<gamma>" by (auto simp add: \<gamma>_def)
       note y_props = this
       then have wellformed_y: "wellformed_item ?y"
        using Derives1_rule LeftDerives1_implies_Derives1 \<gamma> less.prems(1) less.prems(3) 
          wellformed_init_item wellformed_item_def by blast 
       with y_props have wellformed_z: "wellformed_item ?z" by (simp add: wellformed_inc_dot)
       have item_\<beta>_y: "item_\<beta> ?y = \<gamma> @ []" using item_rhs_split y_props(2) by auto
       have is_complete_z: "is_complete ?z" by (simp add: is_complete_def \<gamma>_def)
       have "?z \<in> \<pi> k {} {?y}" 
         apply (rule less(1)[where D="E"])
         apply (auto simp add: eE wellformed_y \<gamma>)
         apply (simp add: \<gamma>_def)
         done
       with y_dom have z_dom: "?z \<in> \<pi> k {} {x}"
         using \<pi>_subset_elem_trans empty_subsetI insert_subset by blast 
       let ?w = "inc_dot (length \<delta>) x" 
       have "?w \<in> Complete k {x, ?z}"
        apply (simp add: Complete_def)
        apply (rule_tac disjI2)+
        apply (rule_tac x=x in exI)
        apply (auto simp add: 2)
        apply (simp add: inc_dot_def inc_item_def less)
        apply (rule_tac x="?z" in exI)
        apply (auto simp add: bin_def less is_complete_z next_symbol_x)
        by (metis Derives1_split LeftDerives1_def N \<gamma> append_Cons append_self_conv2 
          is_nonterminal_N leftmost_cons_nonterminal leftmost_unique length_0_conv list.inject)
       then have "?w \<in> \<pi> k {} {x, ?z}" using Complete_subset_\<pi> by blast  
       then show ?case by (meson \<pi>_subset_elem_trans insert_subset x_subset z_dom) 
    next
      case 3
       then have "\<exists> N \<alpha>. \<delta> = [N] @ \<alpha>" 
         by (metis append_Cons append_Nil count_terminals.cases le0 le_0_eq list.size(3) 
           numeral_le_iff semiring_norm(69))
       then obtain N \<alpha> where \<delta>_split: "\<delta> = [N] @ \<alpha>" by blast
       with 3 have \<alpha>_nonempty: "\<alpha> \<noteq> []"
         by (metis (full_types) One_nat_def Suc_eq_plus1 append_Nil2 impossible_Cons length_Cons 
          list.size(3) nat_1_add_1) 
       have "LeftDerivation ([N] @ \<alpha>) D []" using \<delta>_split less.prems(4) by blast 
       from LeftDerivation_breakdown[OF this, simplified] 
       obtain n where n: "LeftDerivation [N] (take n D) [] \<and> LeftDerivation \<alpha> (drop n D) []" by blast
       let ?E = "take n D"
       from n have E: "LeftDerivation [N] ?E []" by auto
       let ?F = "drop n D"
       from n have F: "LeftDerivation \<alpha> ?F []" by auto
       have length_add: "length ?E + length ?F = length D" by simp 
       have "?E \<noteq> []" using E by force
       then have length_E_0: "length ?E > 0" by auto
       have "?F \<noteq> []" using F \<alpha>_nonempty by force
       then have length_F_0: "length ?F > 0" by auto
       from length_add length_E_0 length_F_0 
       have "length ?E < length D \<and> length ?F < length D"
         using add.commute nat_add_left_cancel_less nat_neq_iff not_add_less2 by linarith
       then have length_E: "length ?E < length D" and length_F: "length ?F < length D" by auto 
       let ?y = "inc_dot (length [N]) x"
       have y_dom: "?y \<in> \<pi> k {} {x}"
        apply (rule_tac less(1)[where D="?E" and \<omega>="\<alpha>@\<omega>"])
        apply (rule length_E)
        by (auto simp add: less \<delta>_split E)
      let ?z = "inc_dot (length \<alpha>) ?y"
      have wellformed_y: "wellformed_item ?y"
        using \<delta>_split is_complete_def less.prems(1) less.prems(2) wellformed_complete_item_\<beta> 
          wellformed_inc_dot by fastforce 
      have "?z \<in> \<pi> k {} {?y}"
        apply (rule_tac less(1)[where D="?F" and \<omega>="\<omega>"])
        apply (rule length_F)
        apply (rule wellformed_y)
        apply (auto simp add: F less)
        by (metis \<delta>_split add.commute append_assoc append_eq_conv_conj drop_drop inc_dot_dot 
          inc_dot_rhs item_\<beta>_def length_Cons less.prems(2) list.size(3))
      then have z_dom: "?z \<in> \<pi> k {} {x}" using \<pi>_subset_elem_trans y_dom by blast 
      have "?z = inc_dot (length \<delta>) x" by (simp add: \<delta>_split)
      with z_dom show ?case by auto
    qed
qed  

lemma derives_empty_implies_LeftDerivation: "derives \<delta> [] \<Longrightarrow> \<exists> D. LeftDerivation \<delta> D []"
  using derives_implies_leftderives is_word_def leftderives_implies_LeftDerivation 
    list.pred_inject(1) by blast
  
lemma thmD6: "wellformed_item x \<Longrightarrow> item_\<beta> x = \<delta> @ \<omega> \<Longrightarrow> item_end x = k \<Longrightarrow> 
  derives \<delta> [] \<Longrightarrow> inc_dot (length \<delta>) x \<in> \<pi> k {} {x}"
using derives_empty_implies_LeftDerivation thmD6_Left by blast

end

end
