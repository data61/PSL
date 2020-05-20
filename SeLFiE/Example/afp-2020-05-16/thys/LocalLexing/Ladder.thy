theory Ladder
imports TheoremD9
begin

context LocalLexing begin

definition LeftDerivationFix :: "sentence \<Rightarrow> nat \<Rightarrow> derivation \<Rightarrow> nat \<Rightarrow> sentence \<Rightarrow> bool"
where
  "LeftDerivationFix \<alpha> i D j \<beta> = (is_sentence \<alpha> \<and> is_sentence \<beta> 
     \<and> LeftDerivation \<alpha> D \<beta> \<and> i < length \<alpha> \<and> j < length \<beta>
     \<and> \<alpha> ! i = \<beta> ! j \<and> (\<exists> E F. D = E@(derivation_shift F 0 (Suc j)) \<and> 
       LeftDerivation (take i \<alpha>) E (take j \<beta>) \<and>
       LeftDerivation (drop (Suc i) \<alpha>) F (drop (Suc j) \<beta>)))" 

definition LeftDerivationIntro :: 
  "sentence \<Rightarrow> nat \<Rightarrow> rule \<Rightarrow> nat \<Rightarrow> derivation \<Rightarrow> nat \<Rightarrow> sentence \<Rightarrow> bool"
where
  "LeftDerivationIntro \<alpha> i r ix D j \<gamma> = (\<exists> \<beta>. LeftDerives1 \<alpha> i r \<beta> \<and>  
     ix < length (snd r) \<and> (snd r) ! ix = \<gamma> ! j \<and>
     LeftDerivationFix \<beta> (i + ix) D j \<gamma>)"

lemma LeftDerivationFix_empty[simp]: "is_sentence \<alpha> \<Longrightarrow> i < length \<alpha> \<Longrightarrow> LeftDerivationFix \<alpha> i [] i \<alpha>"
  apply (auto simp add: LeftDerivationFix_def)
  apply (rule_tac x="[]" in exI)
  apply auto
  done

lemma Derive_empty[simp]: "Derive a [] = a"
  by (auto simp add: Derive_def)

lemma LeftDerivation_append1: "LeftDerivation a (D@[(i, r)]) c \<Longrightarrow> \<exists> b. LeftDerivation a D b 
  \<and> LeftDerives1 b i r c"
by (simp add: LeftDerivation_append)

lemma Derivation_append1: "Derivation a (D@[(i, r)]) c \<Longrightarrow> \<exists> b. Derivation a D b 
  \<and> Derives1 b i r c"
by (simp add: Derivation_append)

lemma  Derivation_take_derive:
  assumes "Derivation a D b"
  shows "Derivation a (take n D) (Derive a (take n D))"
by (metis Derivation_append Derive append_take_drop_id assms)

lemma  LeftDerivation_take_derive:
  assumes "LeftDerivation a D b"
  shows "LeftDerivation a (take n D) (Derive a (take n D))"
by (metis Derive LeftDerivation_append LeftDerivation_implies_Derivation append_take_drop_id assms)

lemma Derivation_Derive_take_Derives1:
  assumes "N \<noteq> 0"
  assumes "N \<le> length D"
  assumes "Derivation a D b"
  assumes \<alpha>: "\<alpha> = Derive a (take (N - 1) D)"
  assumes "\<beta> = Derive a (take N D)"
  shows "Derives1 \<alpha> (fst (D ! (N - 1))) (snd (D ! (N - 1))) \<beta>"
proof -
  let ?D1 = "take (N - 1) D"
  let ?D2 = "take N D"
  from assms have app: "?D2 = ?D1 @ [D ! (N - 1)]"
    apply auto
    by (metis Suc_less_eq Suc_pred le_imp_less_Suc take_Suc_conv_app_nth)
  from assms have "Derivation a ?D2 \<beta>"
    using Derivation_take_derive by blast
  with app show ?thesis
    using Derivation.simps Derivation_append Derive \<alpha> by auto   
qed    

lemma LeftDerivation_Derive_take_LeftDerives1:
  assumes "N \<noteq> 0"
  assumes "N \<le> length D"
  assumes "LeftDerivation a D b"
  assumes \<alpha>: "\<alpha> = Derive a (take (N - 1) D)"
  assumes "\<beta> = Derive a (take N D)"
  shows "LeftDerives1 \<alpha> (fst (D ! (N - 1))) (snd (D ! (N - 1))) \<beta>"
proof -
  let ?D1 = "take (N - 1) D"
  let ?D2 = "take N D"
  from assms have app: "?D2 = ?D1 @ [D ! (N - 1)]"
    apply auto
    by (metis Suc_less_eq Suc_pred le_imp_less_Suc take_Suc_conv_app_nth)
  from assms have "LeftDerivation a ?D2 \<beta>"
    using LeftDerivation_take_derive by blast
  with app show ?thesis
    by (metis Derive LeftDerivation_append1 LeftDerivation_implies_Derivation \<alpha> prod.collapse)
qed

lemma LeftDerives1_skip_prefix:
  "length a \<le> i \<Longrightarrow> LeftDerives1 (a@b) i r (a@c) \<Longrightarrow> LeftDerives1 b (i - length a) r c"
apply (auto simp add: LeftDerives1_def)
using leftmost_skip_prefix apply blast
by (simp add: Derives1_skip_prefix)

lemma LeftDerives1_skip_suffix:
  assumes i: "i < length a"
  assumes D: "LeftDerives1 (a@c) i r (b@c)"
  shows "LeftDerives1 a i r b"
proof -
  note Derives1_def[where u="a@c" and v="b@c" and i=i and r=r]
  then have "\<exists>x y N \<alpha>.
    a @ c = x @ [N] @ y \<and>
    b @ c = x @ \<alpha> @ y \<and> is_sentence x \<and> is_sentence y \<and> (N, \<alpha>) \<in> \<RR> \<and> r = (N, \<alpha>) \<and> i = length x"
    using D LeftDerives1_implies_Derives1 by auto 
  then obtain x y N \<alpha> where split:
    "a @ c = x @ [N] @ y \<and>
     b @ c = x @ \<alpha> @ y \<and> is_sentence x \<and> is_sentence y \<and> (N, \<alpha>) \<in> \<RR> \<and> r = (N, \<alpha>) \<and> i = length x"
     by blast
  from split have "length (a@c) = length (x @ [N] @ y)" by auto
  then have "length a + length c = length x + length y + 1" by simp
  with split have "length a + length c = i + length y + 1" by simp
  with i have len_c_y: "length c \<le> length y" by arith
  let ?y = "take (length y - length c) y"
  from split have ac: "a @ c = (x @ [N]) @ y" by auto
  note cancel_suffix[where a=a and c = c and b = "x@[N]" and d = "y", OF ac len_c_y]
  then have a: "a = x @ [N] @ ?y" by auto
  from split have bc: "b @ c = (x @ \<alpha>) @ y" by auto
  note cancel_suffix[where a=b and c = c and b = "x@\<alpha>" and d = "y", OF bc len_c_y]
  then have b: "b = x @ \<alpha> @ ?y" by auto
  from split len_c_y a b show ?thesis
    apply (simp only: LeftDerives1_def Derives1_def)
    apply (rule_tac conjI)
    using D LeftDerives1_def i leftmost_cons_less apply blast    
    apply (rule_tac x=x in exI)
    apply (rule_tac x="?y" in exI)
    apply (rule_tac x="N" in exI)
    apply (rule_tac x="\<alpha>" in exI)
    apply auto
    by (rule is_sentence_take)
qed

lemma LeftDerives1_X_is_part_of_rule[consumes 2, case_names Suffix Prefix]:
  assumes aXb: "LeftDerives1 \<delta> i r (a@[X]@b)"
  assumes split: "splits_at \<delta> i \<alpha> N \<beta>"
  assumes prefix: "\<And> \<beta>. \<delta> = a @ [X] @ \<beta> \<Longrightarrow> length a < i \<Longrightarrow> is_word (a @ [X]) \<Longrightarrow>
                     LeftDerives1 \<beta> (i - length a - 1) r b \<Longrightarrow> False"
  assumes suffix: "\<And> \<alpha>. \<delta> = \<alpha> @ [X] @ b \<Longrightarrow> LeftDerives1 \<alpha> i r a \<Longrightarrow> False" 
  shows "\<exists> u v. a = \<alpha> @ u \<and> b = v @ \<beta> \<and> (snd r) = u@[X]@v"
proof -
  have aXb_old: "Derives1 \<delta> i r (a@[X]@b)"
    using LeftDerives1_implies_Derives1 aXb by blast
  have prefix_or: "is_prefix \<alpha> a \<or> is_proper_prefix a \<alpha>"
    by (metis Derives1_prefix split aXb_old is_prefix_eq_proper_prefix)
  have is_word_\<alpha>: "is_word \<alpha>"
    using LeftDerives1_splits_at_is_word aXb assms(2) by blast 
  have "is_proper_prefix a \<alpha> \<Longrightarrow> False"
  proof -
    assume proper:"is_proper_prefix a \<alpha>"
    then have "\<exists> u. u \<noteq> [] \<and> \<alpha> = a@u" by (metis is_proper_prefix_def)
    then obtain u where u: "u \<noteq> [] \<and> \<alpha> = a@u" by blast
    note splits_at = splits_at_\<alpha>[OF aXb_old split] splits_at_combine[OF split]
    from splits_at have \<alpha>1: "\<alpha> = take i \<delta>" by blast
    from splits_at have \<alpha>2: "\<alpha> = take i (a@[X]@b)" by blast
    from splits_at have len\<alpha>: "length \<alpha> = i" by blast
    with proper have lena: "length a < i"
      using append_eq_conv_conj drop_eq_Nil leI u by auto 
    with is_word_\<alpha> \<alpha>2 have is_word_aX: "is_word (a@[X])"
      by (simp add: is_word_terminals not_less take_Cons' u)
    from u \<alpha>2 have "a@u = take i (a@[X]@b)" by auto
    with lena have "u = take (i - length a) ([X]@b)" by (simp add: less_or_eq_imp_le) 
    with lena have uX: "u = [X]@(take (i - length a - 1) b)" by (simp add: not_less take_Cons')
    let ?\<beta> = "(take (i - length a - 1) b) @ [N] @ \<beta>"
    from splits_at have f1: "\<delta> = \<alpha> @ [N] @ \<beta>" by blast
    with u uX have f2: "\<delta> = a @ [X] @ ?\<beta>" by simp
    note skip = LeftDerives1_skip_prefix[where a = "a @ [X]" and b = "?\<beta>" and 
      r = r and i = i and c = b]
    then have D: "LeftDerives1 ?\<beta> (i - length a - 1) r b"
      using One_nat_def Suc_leI aXb append_assoc diff_diff_left f2 lena length_Cons 
        length_append length_append_singleton list.size(3) by fastforce
    note prefix[OF f2 lena is_word_aX D]
    then show "False" .
  qed
  with prefix_or have is_prefix: "is_prefix \<alpha> a" by blast

  from aXb have aXb': "LeftDerives1 \<delta> i r ((a@[X])@b)" by auto
  then have aXb'_old: "Derives1 \<delta> i r ((a@[X])@b)" by (simp add: LeftDerives1_implies_Derives1)  
  note Derives1_suffix[OF aXb'_old split]
  then have suffix_or: "is_suffix \<beta> b \<or> is_proper_suffix b \<beta>"
    by (metis is_suffix_eq_proper_suffix)
  have "is_proper_suffix b \<beta> \<Longrightarrow> False"
  proof -
    assume proper: "is_proper_suffix b \<beta>"
    then have "\<exists> u. u \<noteq> [] \<and> \<beta> = u@b" by (metis is_proper_suffix_def)
    then obtain u where u: "u \<noteq> [] \<and> \<beta> = u@b" by blast
    note splits_at = splits_at_\<beta>[OF aXb_old split] splits_at_combine[OF split]
    from splits_at have \<beta>1: "\<beta> = drop (Suc i) \<delta>" by blast
    from splits_at have \<beta>2: "\<beta> = drop (i + length (snd r)) (a @ [X] @ b)" by blast
    from splits_at have len\<beta>: "length \<beta> = length \<delta> - i - 1" by blast
    with proper have lenb: "length b < length \<beta>" by (metis is_proper_suffix_length_cmp) 
    from u \<beta>2 have "u@b = drop (i + length (snd r)) ((a @ [X]) @ b)" by auto
    hence "u = drop (i + length (snd r)) (a @ [X])" 
      by (metis drop_cancel_suffix)
    hence uX: "u = drop (i + length (snd r)) a @ [X]" by (metis drop_keep_last u)
    let ?\<alpha> = "\<alpha> @ [N] @ (drop (i + length (snd r)) a)"
    from splits_at have f1: "\<delta> = \<alpha> @ [N] @ \<beta>" by blast
    with u uX have f2: "\<delta> = ?\<alpha> @ [X] @ b" by simp
    note skip = LeftDerives1_skip_suffix[where a = "?\<alpha>" and c = "[X]@b" and b="a" and
      r = r and i = i]
    have f3: "i < length (\<alpha> @ [N] @ drop (i + length (snd r)) a)"
    proof -
      have f1: "1 + i + length b = length [X] + length b + i"
        by (metis Groups.add_ac(2) Suc_eq_plus1_left length_Cons list.size(3) list.size(4) semiring_normalization_rules(22))
      have f2: "length \<delta> - i - 1 = length ((\<alpha> @ [N] @ drop (i + length (snd r)) a) @ [X] @ b) - Suc i"
        by (metis f2 length_drop splits_at(1))
      have "length ([]::symbol list) \<noteq> length \<delta> - i - 1 - length b"
        by (metis add_diff_cancel_right' append_Nil2 append_eq_append_conv len\<beta> length_append u)
      then have "length ([]::symbol list) \<noteq> length \<alpha> + length ([N] @ drop (i + length (snd r)) a) - i"
        using f2 f1 by (metis Suc_eq_plus1_left add_diff_cancel_right' diff_diff_left length_append)
      then show ?thesis
        by auto
    qed
    from aXb f2 have D: "LeftDerives1 (?\<alpha> @ [X] @ b) i r (a@[X]@b)" by auto
    note skip[OF f3 D]
    note suffix[OF f2  skip[OF f3 D]]
    then show "False" .
  qed
  with suffix_or have is_suffix: "is_suffix \<beta> b" by blast

  from is_prefix have "\<exists> u. a = \<alpha> @ u" by (auto simp add: is_prefix_def)
  then obtain u where u: "a = \<alpha> @ u" by blast
  from is_suffix have "\<exists> v. b = v @ \<beta>" by (auto simp add: is_suffix_def)
  then obtain v where v: "b = v @ \<beta>" by blast
  
  from u v splits_at_combine[OF split] aXb have D:"LeftDerives1 (\<alpha>@[N]@\<beta>) i r (\<alpha>@(u@[X]@v)@\<beta>)"
    by simp
  from splits_at_\<alpha>[OF aXb_old split] have i: "length \<alpha> = i" by blast
  from i have i1: "length \<alpha> \<le> i" and i2: "i \<le> length \<alpha>" by auto
  note LeftDerives1_skip_suffix[OF _ LeftDerives1_skip_prefix[OF i1 D], simplified, OF i2]
  then have "LeftDerives1 [N] 0 r (u @ [X] @ v)" by auto
  then have "Derives1 [N] 0 r (u @ [X] @ v)"
    using LeftDerives1_implies_Derives1 by auto 
  then have r: "snd r = u @ [X] @ v"  
    by (metis Derives1_split append_Cons append_Nil length_0_conv list.inject self_append_conv) 
  show ?thesis using u v r by auto
qed   

lemma LeftDerivationFix_grow_suffix:
  assumes LDF: "LeftDerivationFix (b1@[X]@b2) (length b1) D j c"
  assumes suffix_b2: "LeftDerives1 suffix e r b2"
  assumes is_word_b1X: "is_word (b1@[X])"
  shows "LeftDerivationFix (b1@[X]@suffix) (length b1) ((e + length (b1@[X]), r)#D) j c"
proof -
  from LDF have LDF': "is_sentence (b1@[X]@b2) \<and> is_sentence c \<and> 
    LeftDerivation (b1 @ [X] @ b2) D c \<and> length b1 < length (b1 @ [X] @ b2) \<and>
    j < length c \<and>
    (b1 @ [X] @ b2) ! length b1 = c ! j \<and>
    (\<exists>E F. D = E @ derivation_shift F 0 (Suc j) \<and>
        LeftDerivation (take (length b1) (b1 @ [X] @ b2)) E (take j c) \<and>
        LeftDerivation (drop (Suc (length b1)) (b1 @ [X] @ b2)) F (drop (Suc j) c))"
    using LeftDerivationFix_def by blast
  then obtain E F where EF: "D = E @ derivation_shift F 0 (Suc j) \<and>
        LeftDerivation (take (length b1) (b1 @ [X] @ b2)) E (take j c) \<and>
        LeftDerivation (drop (Suc (length b1)) (b1 @ [X] @ b2)) F (drop (Suc j) c)" by blast
  then have LD_b1_c: "LeftDerivation b1 E (take j c)" by simp 
  with is_word_b1X have E: "E = []"
    using LeftDerivation_implies_Derivation is_word_Derivation is_word_append by blast 
  then have b1_def: "b1 = take j c" using LD_b1_c by auto
  then have b1_len: "j = length b1"
    by (simp add: LDF' dual_order.strict_implies_order min.absorb2) 
  have D: "D = derivation_shift F 0 (Suc j)" using EF E by simp  
  have step: "LeftDerives1 (b1 @ [X] @ suffix) (Suc (e + length b1)) r (b1 @ [X] @ b2) \<and> 
    LeftDerivation  (b1 @ [X] @ b2) D c"
    by (metis LDF' LeftDerives1_append_prefix add_Suc_right append_assoc assms(2) is_word_b1X 
      length_append_singleton)
  then have is_sentence_b1Xsuffix: "is_sentence (b1 @ [X] @ suffix)"
    using Derives1_sentence1 LeftDerives1_implies_Derives1 by blast
  have X_eq_cj: "X = c ! j" using LDF' by auto    
  show ?thesis
    apply (simp add: LeftDerivationFix_def)
    apply (rule conjI)
    using is_sentence_b1Xsuffix apply simp
    apply (rule conjI)
    using LDF' apply simp
    apply (rule conjI)
    using step apply force
    apply (rule conjI)
    using LDF' apply simp
    apply (rule conjI)
    apply (rule X_eq_cj)
    apply (rule_tac x="[]" in exI)
    apply (rule_tac x="(e, r)#F" in exI)
    apply auto
    apply (rule b1_len[symmetric])
    apply (rule D)
    apply (rule b1_def)
    apply (rule_tac x="b2" in exI)
    apply (simp add: suffix_b2)
    using EF by auto
qed

lemma Derives1_append_suffix: 
  assumes Derives1: "Derives1 v i r w"
  assumes u: "is_sentence u"
  shows "Derives1 (v@u) i r (w@u)"
proof -
  have "\<exists> \<alpha> N \<beta>. splits_at v i \<alpha> N \<beta>" using assms splits_at_ex by auto
  then obtain \<alpha> N \<beta> where split_v: "splits_at v i \<alpha> N \<beta>" by blast
  have split_w: "w = \<alpha>@(snd r)@\<beta>" using assms split_v splits_at_combine_dest by blast 
  have split_uv: "splits_at (v@u) i \<alpha> N (\<beta>@u)"   
    by (simp add: split_v splits_at_append)
  have is_sentence_uv: "is_sentence (v@u)"
    using Derives1 Derives1_sentence1 is_sentence_concat u by blast 
  show ?thesis
    by (metis Derives1 Derives1_nonterminal Derives1_rule append_assoc is_sentence_uv 
        split_uv split_v split_w splits_at_implies_Derives1)
qed

lemma leftmost_append_suffix: "leftmost i v \<Longrightarrow> leftmost i (v@u)"
by (simp add: leftmost_def nth_append)

lemma LeftDerives1_append_suffix: 
  assumes Derives1: "LeftDerives1 v i r w"
  assumes u: "is_sentence u"
  shows "LeftDerives1 (v@u) i r (w@u)"
proof -
  have 1: "Derives1 v i r w"
    by (simp add: Derives1 LeftDerives1_implies_Derives1) 
  have 2: "leftmost i v"
    using Derives1 LeftDerives1_def by blast  
  have 3: "is_sentence u" using u by fastforce 
  have 4: "Derives1 (v@u) i r (w@u)"
    by (simp add: "1" "3" Derives1_append_suffix) 
  have 5: "leftmost i (v@u)"
    by (simp add: "2" leftmost_append_suffix u) 
  show ?thesis
    by (simp add: "4" "5" LeftDerives1_def)
qed     

lemma LeftDerivationFix_is_sentence: 
  "LeftDerivationFix a i D j b \<Longrightarrow> is_sentence a \<and> is_sentence b"
  using LeftDerivationFix_def by blast
  
lemma LeftDerivationIntro_is_sentence:
  "LeftDerivationIntro \<alpha> i r ix D j \<gamma> \<Longrightarrow> is_sentence \<alpha> \<and> is_sentence \<gamma>"
  by (meson Derives1_sentence1 LeftDerivationFix_is_sentence LeftDerivationIntro_def 
    LeftDerives1_implies_Derives1)

lemma LeftDerivationFix_grow_prefix:
  assumes LDF: "LeftDerivationFix (b1@[X]@b2) (length b1) D j c"
  assumes prefix_b1: "LeftDerives1 prefix e r b1"
  shows "LeftDerivationFix (prefix@[X]@b2) (length prefix) ((e, r)#D) j c"
proof -
  from LDF have LDF': "LeftDerivation (b1 @ [X] @ b2) D c \<and>
    length b1 < length (b1 @ [X] @ b2) \<and>
    j < length c \<and>
    (b1 @ [X] @ b2) ! length b1 = c ! j \<and>
    (\<exists>E F. D = E @ derivation_shift F 0 (Suc j) \<and>
        LeftDerivation (take (length b1) (b1 @ [X] @ b2)) E (take j c) \<and>
        LeftDerivation (drop (Suc (length b1)) (b1 @ [X] @ b2)) F (drop (Suc j) c))"
    using LeftDerivationFix_def by blast
  then obtain E F where EF: "D = E @ derivation_shift F 0 (Suc j) \<and>
        LeftDerivation (take (length b1) (b1 @ [X] @ b2)) E (take j c) \<and>
        LeftDerivation (drop (Suc (length b1)) (b1 @ [X] @ b2)) F (drop (Suc j) c)" by blast
  then have E_b1_c: "LeftDerivation b1 E (take j c)" by simp 
  with EF have F_b2_c: "LeftDerivation b2 F (drop (Suc j) c)" by simp
  have step: "LeftDerives1 (prefix @ [X] @ b2) e r (b1 @ [X] @ b2)"
    using LDF LeftDerivationFix_is_sentence LeftDerives1_append_suffix 
      is_sentence_concat prefix_b1 by blast   
  show ?thesis
    apply (simp add: LeftDerivationFix_def)
    apply (rule conjI)
    apply (metis Derives1_sentence1 LDF LeftDerivationFix_def LeftDerives1_implies_Derives1 
      is_sentence_concat is_sentence_cons prefix_b1)
    apply (rule conjI)
    using LDF LeftDerivationFix_is_sentence apply blast
    apply (rule conjI)
    apply (rule_tac x="b1@[X]@b2" in exI)
    using step apply simp
    using LDF' apply auto[1]
    apply (rule conjI)
    using LDF' apply simp
    apply (rule conjI)
    using LDF' apply auto[1]
    apply (rule_tac x="(e,r)#E" in exI)
    apply (rule_tac x="F" in exI)
    apply (auto simp add: EF F_b2_c)
    apply (rule_tac x="b1" in exI)
    apply (simp add: prefix_b1 E_b1_c)
    done
qed

lemma LeftDerivationFixOrIntro: 
  "LeftDerivation a D \<gamma> \<Longrightarrow> is_sentence \<gamma> \<Longrightarrow> j < length \<gamma> \<Longrightarrow>
  (\<exists> i. LeftDerivationFix a i D j \<gamma>) \<or> 
  (\<exists> d \<alpha> ix. d < length D \<and> LeftDerivation a (take d D) \<alpha> \<and> 
    LeftDerivationIntro \<alpha> (fst (D ! d)) (snd (D ! d)) ix (drop (Suc d) D) j \<gamma>)" 
proof (induct "length D" arbitrary: a D \<gamma> j rule: less_induct) 
  (* The induction here is unnecessary, but we use it anyway for context reasons *)
  case less
  have "length D = 0 \<or> length D \<noteq> 0" by blast
  then show ?case
  proof (induct rule: disjCases2)
    case 1 
    then have D: "D = []" by auto
    with less have "\<exists>i. LeftDerivationFix a i D j \<gamma>" 
      apply (rule_tac x=j in exI)
      by auto
    then show ?case by blast
  next
    case 2
    note less2 = 2
    have "\<exists> n \<beta> i. n \<le> length D \<and> \<beta> = Derive a (take n D) \<and> LeftDerivationFix \<beta> i (drop n D) j \<gamma>"  
      apply (rule_tac x="length D" in exI)
      apply auto
      using Derive LeftDerivationFix_empty LeftDerivation_implies_Derivation less by blast
    then show ?case
    proof (induct rule: ex_minimal_witness)
      case (Minimal N)
      then obtain \<beta> i where Minimal_N:
        "N \<le> length D \<and> \<beta> = Derive a (take N D) \<and> LeftDerivationFix \<beta> i (drop N D) j \<gamma>" by blast 
      have "N = 0 \<or> N \<noteq> 0" by blast
      then show ?case
      proof (induct rule: disjCases2)
        case 1
        with Minimal_N have "\<beta> = a" by auto
        with 1 Minimal_N show ?case
          apply (rule_tac disjI1)
          by auto
      next
        case 2
        let ?\<delta> = "Derive a (take (N - 1) D)"
        have LeftDerives1_\<delta>: "LeftDerives1 ?\<delta> (fst (D ! (N - 1))) (snd (D ! (N - 1))) \<beta>"
          using "2.hyps" LeftDerivation_Derive_take_LeftDerives1 Minimal_N less.prems(1) by blast
        then have Derives1_\<delta>: "Derives1 ?\<delta> (fst (D ! (N - 1))) (snd (D ! (N - 1))) \<beta>"
          using LeftDerives1_implies_Derives1 by blast   
        have i_len: "i < length \<beta>" using Minimal_N 
          by (auto simp add: LeftDerivationFix_def)
        then have "\<exists> X \<beta>_1 \<beta>_2. splits_at \<beta> i \<beta>_1 X \<beta>_2"
          using splits_at_def by blast
        then obtain X \<beta>_1 \<beta>_2 where \<beta>_split: "splits_at \<beta> i \<beta>_1 X \<beta>_2" by blast
        then have \<beta>_combine: "\<beta> = \<beta>_1 @ [X] @ \<beta>_2" using splits_at_combine by blast 
        then have LeftDerives1_\<delta>_hyp: 
          "LeftDerives1 ?\<delta> (fst (D ! (N - 1))) (snd (D ! (N - 1))) (\<beta>_1 @ [X] @ \<beta>_2)"
          using LeftDerives1_\<delta> by blast 
        from \<beta>_split have i_def: "i = length \<beta>_1"
          by (simp add: dual_order.strict_implies_order  min.absorb2 splits_at_def)  
        have "\<exists> Y \<delta>_1 \<delta>_2. splits_at ?\<delta> (fst (D ! (N - 1))) \<delta>_1 Y \<delta>_2"
          using Derives1_\<delta> splits_at_ex by blast
        then obtain Y \<delta>_1 \<delta>_2 where \<delta>_split: "splits_at ?\<delta> (fst (D ! (N - 1))) \<delta>_1 Y \<delta>_2" by blast 
        have NFix: "LeftDerivationFix (\<beta>_1 @ [X] @ \<beta>_2) (length \<beta>_1) (drop N D) j \<gamma>"              
          using Minimal_N \<beta>_combine i_def by auto      
        from LeftDerives1_\<delta>_hyp \<delta>_split 
        have "\<exists>u v. \<beta>_1 = \<delta>_1 @ u \<and> \<beta>_2 = v @ \<delta>_2 \<and> snd (snd (D ! (N - 1))) = u @ [X] @ v"
        proof (induct rule: LeftDerives1_X_is_part_of_rule)
          case (Suffix suffix)
            let ?k = "N - 1"
            let ?\<beta> = "Derive a (take ?k D)"
            let ?i = "length \<beta>_1"
            have k_less: "?k < length D" using "2.hyps" Minimal_N by linarith 
            then have k_leq: "?k \<le> length D" by auto
            have drop_k_d: "drop ?k D = (D ! (N - 1))#(drop N D)"
              using "2.hyps" Cons_nth_drop_Suc k_less by fastforce 
            from LeftDerivationFix_grow_suffix[OF NFix Suffix(4) Suffix(3)] Suffix(1) Suffix(2) 2
            have "LeftDerivationFix ?\<beta> ?i (drop ?k D) j \<gamma>" 
              apply auto
              by (metis One_nat_def drop_k_d)
            with Minimal(2)[where k="?k"] show "False"
              using "2.hyps" k_leq by auto 
        next
          case (Prefix prefix)
            have collapse: "(fst (D ! (N - 1)), snd (D ! (N - 1))) # drop N D = drop (N - 1) D"
              by (metis "2.hyps" Cons_nth_drop_Suc Minimal_N Suc_diff_1 neq0_conv not_less 
                not_less_eq prod.collapse)          
            from LeftDerivationFix_grow_prefix[OF NFix Prefix(2)] Prefix(1) collapse
            have "LeftDerivationFix ?\<delta> (length prefix) (drop (N - 1) D) j \<gamma>" by auto
            with Minimal(2)[where k = "N - 1"] show "False"
              by (metis Minimal_N collapse diff_le_self le_neq_implies_less less_imp_diff_less 
                less_or_eq_imp_le not_Cons_self2)
        qed
        then obtain u v where uv:
          "\<beta>_1 = \<delta>_1 @ u \<and> \<beta>_2 = v @ \<delta>_2 \<and> snd (snd (D ! (N - 1))) = u @ [X] @ v" by blast
        have X_1: "snd (snd (D ! (N - Suc 0))) ! length u = X" using uv by auto
        have X_2: "\<gamma> ! j = X" using LeftDerivationFix_def NFix by auto        
        show ?case
          apply (rule disjI2)
          apply (rule_tac x="N - 1" in exI)
          apply (rule_tac x="?\<delta>" in exI)
          apply (rule_tac x="length u" in exI)
          apply (rule conjI)
          using Minimal_N less2 apply linarith
          apply (rule conjI)
          using LeftDerivation_take_derive less.prems(1) apply blast
          apply (subst LeftDerivationIntro_def)
          apply (rule_tac x=\<beta> in exI)
          apply auto
          using LeftDerives1_\<delta> One_nat_def apply presburger
          using uv apply auto[1]
          using X_1 X_2 apply auto[1]
          by (metis (no_types, lifting) "2.hyps" Derives1_\<delta> Derives1_split Minimal_N One_nat_def 
            Suc_diff_1 \<delta>_split append_eq_conv_conj i_def length_append neq0_conv splits_at_def uv)
      qed
    qed
  qed
qed

type_synonym deriv = "nat \<times> nat \<times> nat" 
type_synonym ladder = "deriv list"

definition deriv_n :: "deriv \<Rightarrow> nat" where 
  "deriv_n d = fst d"

definition deriv_j :: "deriv \<Rightarrow> nat" where
  "deriv_j d = fst (snd d)"

definition deriv_ix :: "deriv \<Rightarrow> nat" where
  "deriv_ix d = snd (snd d)"

definition deriv_i :: "deriv \<Rightarrow> nat" where
  "deriv_i d = snd (snd d)"

definition ladder_j :: "ladder \<Rightarrow> nat \<Rightarrow> nat" where
  "ladder_j L index = deriv_j (L ! index)"

definition ladder_i :: "ladder \<Rightarrow> nat \<Rightarrow> nat" where
  "ladder_i L index = (if index = 0 then deriv_i (hd L) else ladder_j L (index - 1))"

definition ladder_n :: "ladder \<Rightarrow> nat \<Rightarrow> nat" where
  "ladder_n L index = deriv_n (L ! index)"

definition ladder_prev_n :: "ladder \<Rightarrow> nat \<Rightarrow> nat" where
  "ladder_prev_n L index = (if index = 0 then 0 else (ladder_n L (index - 1)))" 

definition ladder_ix :: "ladder \<Rightarrow> nat \<Rightarrow> nat" where
  "ladder_ix L index = (if index = 0 then undefined else deriv_ix (L ! index))"

definition ladder_last_j :: "ladder \<Rightarrow> nat" where
  "ladder_last_j L = ladder_j L (length L - 1)"

definition ladder_last_n :: "ladder \<Rightarrow> nat" where
  "ladder_last_n L = ladder_n L (length L - 1)"

definition is_ladder :: "derivation \<Rightarrow> ladder \<Rightarrow> bool" where
  "is_ladder D L = (L \<noteq> [] \<and> 
    (\<forall> u. u < length L \<longrightarrow> ladder_n L u \<le> length D) \<and>
    (\<forall> u v. u < v \<and> v < length L \<longrightarrow> ladder_n L u < ladder_n L v) \<and>
    ladder_last_n L = length D)"   

definition ladder_\<gamma> :: "sentence \<Rightarrow> derivation \<Rightarrow> ladder \<Rightarrow> nat \<Rightarrow> sentence" where
  "ladder_\<gamma> a D L index = Derive a (take (ladder_n L index) D)"

definition ladder_\<alpha> :: "sentence \<Rightarrow> derivation \<Rightarrow> ladder \<Rightarrow> nat \<Rightarrow> sentence" where
  "ladder_\<alpha> a D L index = (if index = 0 then a else ladder_\<gamma> a D L (index - 1))"

definition LeftDerivationIntrosAt :: "sentence \<Rightarrow> derivation \<Rightarrow> ladder \<Rightarrow> nat \<Rightarrow> bool" where
  "LeftDerivationIntrosAt a D L index = (
       let \<alpha> = ladder_\<alpha> a D L index in
       let i = ladder_i L index in
       let j = ladder_j L index in
       let ix = ladder_ix L index in
       let \<gamma> = ladder_\<gamma> a D L index in 
       let n = ladder_n L (index - 1) in
       let m = ladder_n L index in
       let e = D ! n in
       let E = drop (Suc n) (take m D) in
        i = fst e \<and>
        LeftDerivationIntro \<alpha> i (snd e) ix E j \<gamma>)"

definition LeftDerivationIntros :: "sentence \<Rightarrow> derivation \<Rightarrow> ladder \<Rightarrow> bool" where
  "LeftDerivationIntros a D L = (
     \<forall> index. 1 \<le> index \<and> index < length L \<longrightarrow> LeftDerivationIntrosAt a D L index)"

definition LeftDerivationLadder :: "sentence \<Rightarrow> derivation \<Rightarrow> ladder \<Rightarrow> sentence \<Rightarrow> bool" where 
  "LeftDerivationLadder a D L b = (
    LeftDerivation a D b \<and> 
    is_ladder D L \<and>
    LeftDerivationFix a (ladder_i L 0) (take (ladder_n L 0) D) (ladder_j L 0) (ladder_\<gamma> a D L 0) \<and> 
    LeftDerivationIntros a D L)" 

definition mk_deriv_fix :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> deriv" where
  "mk_deriv_fix i n j = (n, j, i)"

definition mk_deriv_intro :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> deriv" where
  "mk_deriv_intro ix n j = (n, j, ix)"

lemma mk_deriv_fix_i[simp]: "deriv_i (mk_deriv_fix i n j) = i"
  by (simp add: deriv_i_def mk_deriv_fix_def)

lemma mk_deriv_fix_j[simp]: "deriv_j (mk_deriv_fix i n j) = j"
  by (simp add: deriv_j_def mk_deriv_fix_def)

lemma mk_deriv_fix_n[simp]: "deriv_n (mk_deriv_fix i n j) = n"
  by (simp add: deriv_n_def mk_deriv_fix_def)

lemma mk_deriv_intro_i[simp]: "deriv_i (mk_deriv_intro i n j) = i"
  by (simp add: deriv_i_def mk_deriv_intro_def)

lemma mk_deriv_intro_ix[simp]: "deriv_ix (mk_deriv_intro ix n j) = ix"
  by (simp add: deriv_ix_def mk_deriv_intro_def)

lemma mk_deriv_intro_j[simp]: "deriv_j (mk_deriv_intro i n j) = j"
  by (simp add: deriv_j_def mk_deriv_intro_def)

lemma mk_deriv_intro_n[simp]: "deriv_n (mk_deriv_intro i n j) = n"
  by (simp add: deriv_n_def mk_deriv_intro_def)

lemma LeftDerivationFix_implies_ex_ladder:
  "LeftDerivationFix a i D j \<gamma> \<Longrightarrow> \<exists> L. LeftDerivationLadder a D L \<gamma> \<and> 
    ladder_last_j L = j \<and> ladder_last_n L = length D"
  apply (rule_tac x="[mk_deriv_fix i (length D) j]" in exI)
  apply (auto simp add: LeftDerivationLadder_def)
  apply (simp add: LeftDerivationFix_def)
  apply (simp add: is_ladder_def)
  apply (auto simp add: ladder_i_def ladder_j_def ladder_n_def ladder_\<gamma>_def)
  apply (simp add: ladder_last_n_def ladder_n_def)
  using Derive LeftDerivationFix_def LeftDerivation_implies_Derivation apply blast
  apply (simp add: LeftDerivationIntros_def)
  apply (simp add: ladder_last_j_def ladder_j_def)
  apply (simp add: ladder_last_n_def ladder_n_def)
  done 

lemma trivP[case_names prems]: "P \<Longrightarrow> P" by blast

lemma LeftDerivationLadder_ladder_n_bound:
  assumes "LeftDerivationLadder a D L b"
  assumes "index < length L"
  shows "ladder_n L index \<le> length D"
using LeftDerivationLadder_def assms(1) assms(2) is_ladder_def by blast 

lemma LeftDerivationLadder_deriv_n_bound:
  assumes "LeftDerivationLadder a D L b"
  assumes "index < length L"
  shows "deriv_n (L ! index) \<le> length D"
using LeftDerivationLadder_def assms(1) assms(2) is_ladder_def ladder_n_def by auto

lemma ladder_n_simp1[simp]: "u < length L \<Longrightarrow> ladder_n (L@L') u = ladder_n L u"
by (simp add: ladder_n_def)

lemma ladder_n_simp2[simp]: "ladder_n (L@[d]) (length L) = deriv_n d"
by (simp add: ladder_n_def)

lemma ladder_j_simp1[simp]: "u < length L \<Longrightarrow> ladder_j (L@L') u = ladder_j L u"
by (simp add: ladder_j_def)

lemma ladder_j_simp2[simp]: "ladder_j (L@[d]) (length L) = deriv_j d"
by (simp add: ladder_j_def)

lemma ladder_i_simp1[simp]: "u < length L \<Longrightarrow> ladder_i (L@L') u = ladder_i L u"
by (auto simp add: ladder_i_def)

lemma ladder_ix_simp1[simp]: "u < length L \<Longrightarrow> ladder_ix (L@L') u = ladder_ix L u"
by (auto simp add: ladder_ix_def)

lemma ladder_ix_simp2[simp]: "L \<noteq> [] \<Longrightarrow> ladder_ix (L@[d]) (length L) = deriv_ix d"
by (auto simp add: ladder_ix_def)

lemma ladder_\<gamma>_simp1[simp]: "u < length L \<Longrightarrow> ladder_\<gamma> a D (L@L') u = ladder_\<gamma> a D L u"
by (simp add: ladder_\<gamma>_def)

lemma ladder_\<gamma>_simp2[simp]: "u < length L \<Longrightarrow> is_ladder D L \<Longrightarrow> 
  ladder_\<gamma> a (D@D') L u = ladder_\<gamma> a D L u"
by (simp add: is_ladder_def ladder_\<gamma>_def)

lemma ladder_\<alpha>_simp1[simp]: "u < length L \<Longrightarrow> ladder_\<alpha> a D (L@L') u = ladder_\<alpha> a D L u"
by (simp add: ladder_\<alpha>_def)

lemma ladder_\<alpha>_simp2[simp]: "u < length L \<Longrightarrow> is_ladder D L \<Longrightarrow> 
  ladder_\<alpha> a (D@D') L u = ladder_\<alpha> a D L u"
by (simp add: is_ladder_def ladder_\<alpha>_def)

lemma ladder_n_minus_1_bound: "is_ladder D L \<Longrightarrow> index \<ge> 1 \<Longrightarrow> index < length L \<Longrightarrow> 
  ladder_n L (index - Suc 0) < length D"
by (metis (no_types, lifting) One_nat_def Suc_diff_1 Suc_le_lessD dual_order.strict_implies_order 
  is_ladder_def le_neq_implies_less not_less)

lemma LeftDerivationIntrosAt_ignore_appendix:
  assumes is_ladder: "is_ladder D L"
  assumes hyp: "LeftDerivationIntrosAt a D L index"
  assumes index_ge: "index \<ge> 1"
  assumes index_less: "index < length L"
  shows "LeftDerivationIntrosAt a (D @ D') (L @ L') index"
proof -
  have index_minus_1: "index - Suc 0 < length L"
    using index_less by arith
  have is_0: "ladder_n L index - length D = 0"
    using index_less is_ladder is_ladder_def by auto
  from index_ge index_less show ?thesis
    apply (simp add: LeftDerivationIntrosAt_def Let_def)
    apply (simp add: index_minus_1 is_ladder ladder_n_minus_1_bound is_0)
    using hyp apply (auto simp add: LeftDerivationIntrosAt_def Let_def)
    done
qed

lemma ladder_i_eq_last_j: "L \<noteq> [] \<Longrightarrow> ladder_i (L @ L') (length L) = ladder_last_j L"
by (simp add: ladder_i_def ladder_last_j_def)

lemma ladder_last_n_intro: "L \<noteq> [] \<Longrightarrow> ladder_n L (length L - Suc 0) = ladder_last_n L"
by (simp add: ladder_last_n_def)
  
lemma is_ladder_not_empty: "is_ladder D L \<Longrightarrow> L \<noteq> []"
using is_ladder_def by blast
  
lemma last_ladder_\<gamma>:
  assumes is_ladder: "is_ladder D L"
  assumes ladder_last_n: "ladder_last_n L = length D"
  shows "ladder_\<gamma> a D L (length L - Suc 0) = Derive a D"
proof -
  from is_ladder is_ladder_not_empty have "L \<noteq> []" by blast
  then show ?thesis
    by (simp add: ladder_\<gamma>_def ladder_last_n_intro ladder_last_n)
qed

lemma ladder_\<alpha>_full:
  assumes is_ladder: "is_ladder D L"
  assumes ladder_last_n: "ladder_last_n L = length D"
  shows "ladder_\<alpha> a (D @ D') (L @ L') (length L) = Derive a D"
proof -
  from is_ladder have L_not_empty: "L \<noteq> []" by (simp add: is_ladder_def)  
  with is_ladder ladder_last_n show ?thesis
    apply (simp add: ladder_\<alpha>_def)
    apply (simp add: last_ladder_\<gamma>) 
    done
qed

lemma LeftDerivationIntro_implies_LeftDerivation:
  "LeftDerivationIntro \<alpha> i r ix D j \<gamma> \<Longrightarrow> LeftDerivation \<alpha> ((i,r)#D) \<gamma>"
using LeftDerivationFix_def LeftDerivationIntro_def by auto

lemma LeftDerivationLadder_grow: 
  "LeftDerivationLadder a D L \<alpha> \<Longrightarrow> ladder_last_j L = i \<Longrightarrow>
   LeftDerivationIntro \<alpha> i r ix E j \<gamma> \<Longrightarrow>
   LeftDerivationLadder a (D@[(i, r)]@E) (L@[mk_deriv_intro ix (Suc(length D + length E)) j]) \<gamma>"
proof (induct arbitrary: a D L \<alpha> i r ix E j \<gamma> rule: trivP)
  case prems
  {
    fix u :: nat
    assume "u < Suc (length L)"
    then have "u < length L \<or> u = length L" by arith
    then have "ladder_n (L @ [mk_deriv_intro ix (Suc (length D + length E)) j]) u \<le> 
      Suc (length D + length E)"
    proof (induct rule: disjCases2)
      case 1
      then show ?case
        apply simp
        by (meson LeftDerivationLadder_ladder_n_bound le_Suc_eq le_add1 le_trans prems(1))
    next
      case 2
      then show ?case
        by (simp add: ladder_n_def)
    qed
  }
  note ladder_n_ineqs = this    
  {
    fix u :: nat
    fix v :: nat
    assume u_less_v: "u < v"
    assume "v < Suc (length L)"
    then have "v < length L \<or> v = length L" by arith
    then have "ladder_n (L @ [mk_deriv_intro ix (Suc (length D + length E)) j]) u
           < ladder_n (L @ [mk_deriv_intro ix (Suc (length D + length E)) j]) v"
    proof (induct rule: disjCases2) 
      case 1
      with u_less_v have u_bound: "u < length L" by arith
      show ?case using 1 u_bound apply simp
      using prems u_less_v LeftDerivationLadder_def is_ladder_def by auto
    next
      case 2
      with u_less_v have u_bound: "u < length L" by arith
      have "deriv_n (L ! u) \<le> length D"
        using LeftDerivationLadder_deriv_n_bound prems(1) u_bound by blast       
      then show ?case
        apply (simp add: u_bound)
        apply (simp add: ladder_n_def 2)
        done
    qed
  }
  note ladder_n_ineqs = ladder_n_ineqs this
  have is_ladder: 
    "is_ladder (D @ (i, r) # E) (L @ [mk_deriv_intro ix (Suc (length D + length E)) j])"
    apply (auto simp add: is_ladder_def)
    using ladder_n_ineqs apply auto
    apply (simp add: ladder_last_n_def)
    done
  have is_ladder_L: "is_ladder D L"
    using LeftDerivationLadder_def prems.prems(1) by blast 
  have ladder_last_n_eq_length: "ladder_last_n L = length D"
    using is_ladder_L is_ladder_def by blast   
  have L_not_empty: "L \<noteq> []"
    using LeftDerivationLadder_def is_ladder_def prems(1) by blast 
  {
    fix index :: nat
    assume index_ge: "Suc 0 \<le> index"
    assume "index < Suc (length L)"
    then have "index < length L \<or> index = length L" by arith
    then have "LeftDerivationIntrosAt a (D @ (i, r) # E) 
      (L @ [mk_deriv_intro ix (Suc (length D + length E)) j]) index"
    proof (induct rule: disjCases2)
      case 1
      then show ?case
        using LeftDerivationIntrosAt_ignore_appendix
          LeftDerivationIntros_def LeftDerivationLadder_def One_nat_def 
          index_ge prems.prems(1) by presburger 
    next
      case 2
      have min_simp:  "\<And> n E. min n (Suc (n + length E)) = n"
        by auto
      with 2 prems is_ladder_L ladder_last_n_eq_length show ?case        
        apply (simp add: LeftDerivationIntrosAt_def)
        apply (simp add: L_not_empty ladder_i_eq_last_j ladder_last_n_intro)
        apply (simp add: ladder_\<alpha>_full min_simp)
        apply (simp add: ladder_\<gamma>_def)
        by (metis Derive LeftDerivationIntro_implies_LeftDerivation LeftDerivationLadder_def 
          LeftDerivation_implies_Derivation LeftDerivation_implies_append)
    qed
  }
  then show ?case
    apply (auto simp add: LeftDerivationLadder_def)
    using prems apply (auto simp add: LeftDerivationLadder_def)[1]
    using LeftDerivationFix_def LeftDerivationIntro_def LeftDerivation_append apply auto[1]
    using is_ladder apply simp
    using L_not_empty apply simp
    using LeftDerivationLadder_def LeftDerivationLadder_ladder_n_bound ladder_\<gamma>_def 
      prems.prems(1) apply auto[1]
    apply (subst LeftDerivationIntros_def)
    apply auto
    done
qed 

lemma LeftDerivationIntro_bounds_ij: 
  "LeftDerivationIntro \<alpha> i r ix D j \<beta> \<Longrightarrow> i < length \<alpha> \<and> j < length \<beta>"
  by (meson Derives1_bound LeftDerivationFix_def LeftDerivationIntro_def 
    LeftDerives1_implies_Derives1)

theorem LeftDerivationLadder_exists: "LeftDerivation a D \<gamma> \<Longrightarrow> is_sentence \<gamma> \<Longrightarrow> j < length \<gamma> \<Longrightarrow> 
  \<exists> L. LeftDerivationLadder a D L \<gamma> \<and> ladder_last_j L = j"
proof (induct "length D" arbitrary: a D \<gamma> j rule: less_induct)
  case less
  from LeftDerivationFixOrIntro[OF less(2,3,4)] show ?case
  proof (induct rule: disjCases2) 
    case 1
    then obtain i where "LeftDerivationFix a i D j \<gamma>" by blast
    show ?case
    using "1.hyps" LeftDerivationFix_implies_ex_ladder by blast
  next
    case 2
    then obtain d \<alpha> ix where inductrule: "d < length D \<and>
      LeftDerivation a (take d D) \<alpha> \<and>
      LeftDerivationIntro \<alpha> (fst (D ! d)) (snd (D ! d)) ix (drop (Suc d) D) j \<gamma>" by blast
    then have less_length_D: "length (take d D) < length D" 
      and LeftDerivation_\<alpha>: "LeftDerivation a (take d D) \<alpha>" by auto
    have is_sentence_\<alpha>: "is_sentence \<alpha>" using LeftDerivationIntro_is_sentence inductrule by blast
    have "fst (D ! d) < length \<alpha>" using LeftDerivationIntro_bounds_ij inductrule by blast 
    from less(1)[OF less_length_D LeftDerivation_\<alpha> is_sentence_\<alpha>, where j=" fst (D ! d)", OF this]
    obtain L where induct_Ladder:
      "LeftDerivationLadder a (take d D) L \<alpha>" and induct_last: "ladder_last_j L = fst (D ! d)" 
      by blast
    have induct_intro: "LeftDerivationIntro \<alpha> (fst (D ! d)) (snd (D ! d)) ix (drop (Suc d) D) j \<gamma>"
      using inductrule by blast
    have "d < length D" using inductrule by blast
    then have simp_to_D: "take d D @ D ! d # drop (Suc d) D = D"
      using id_take_nth_drop by force        
    from LeftDerivationLadder_grow[OF induct_Ladder induct_last induct_intro] simp_to_D
    show ?case
      apply auto
      apply (rule_tac x=
        "L @ [mk_deriv_intro ix (Suc (min (length D) d + (length D - Suc d))) j]" in exI)
      apply (simp add: ladder_last_j_def)
      done
  qed
qed

lemma LeftDerivationLadder_L_0: 
  assumes "LeftDerivationLadder \<alpha> D L \<beta>"
  assumes "length L = 1"
  shows "\<exists> i. LeftDerivationFix \<alpha> i D (ladder_last_j L) \<beta>"
proof -
  have "is_ladder D L" using assms by (auto simp add: LeftDerivationLadder_def)
  then have ladder_n: "ladder_n L 0 = length D"
    by (simp add: assms(2) is_ladder_def ladder_last_n_def)
  show ?thesis
    apply (rule_tac x = "ladder_i L 0" in exI)
    using assms(1) apply (auto simp add: LeftDerivationLadder_def)
    by (metis Derive LeftDerivationFix_def LeftDerivation_implies_Derivation One_nat_def assms(2) 
      diff_Suc_1 ladder_last_j_def ladder_n order_refl take_all) 
qed    
  
lemma LeftDerivationFix_splits_at_derives:
  assumes "LeftDerivationFix a i D j b"
  shows "\<exists> U a1 a2 b1 b2. splits_at a i a1 U a2 \<and> splits_at b j b1 U b2 \<and> 
    derives a1 b1 \<and> derives a2 b2"
proof -
  note hyp = LeftDerivationFix_def[where \<alpha>=a and \<beta>=b and D=D and i=i and j=j]
  from hyp obtain E F where EF:
    "D = E @ derivation_shift F 0 (Suc j) \<and>
      LeftDerivation (take i a) E (take j b) \<and> LeftDerivation (drop (Suc i) a) F (drop (Suc j) b)"
    using assms by blast
  show ?thesis
    apply (rule_tac x="a ! i" in exI)
    apply (rule_tac x="take i a" in exI)
    apply (rule_tac x="drop (Suc i) a" in exI)
    apply (rule_tac x="take j b" in exI)
    apply (rule_tac x="drop (Suc j) b" in exI)
    using Derivation_implies_derives LeftDerivation_implies_Derivation assms hyp 
      splits_at_def by blast
qed

lemma  LeftDerivation_append_suffix:
  "LeftDerivation a D b \<Longrightarrow> is_sentence c \<Longrightarrow> LeftDerivation (a@c) D (b@c)" 
proof (induct D arbitrary: a b c)
  case Nil
  then show ?case by auto
next
  case (Cons d D)
  then show ?case 
    apply auto
    apply (rule_tac x="x@c" in exI)
    apply auto
    using LeftDerives1_append_suffix by simp
qed

lemma LeftDerivation_impossible: "LeftDerivation a D b \<Longrightarrow> i < length a \<Longrightarrow> 
  is_nonterminal (a ! i) \<Longrightarrow> derivation_ge D (Suc i) \<Longrightarrow> D = []"
proof (induct D)
  case Nil then show ?case by auto
next
  case (Cons d D) 
  then have lm: "\<And> j. leftmost j a \<Longrightarrow> j \<le> i"
    by (metis Derives1_sentence1 LeftDerivation.simps(2) LeftDerives1_implies_Derives1 
      leftmost_exists leftmost_unique)     
  from Cons show ?case
    apply auto
    apply (auto simp add: derivation_ge_def LeftDerives1_def)
    using lm[where j="fst d"] by arith
qed

lemma derivation_ge_shift: "derivation_ge (derivation_shift F 0 j) j"
  apply (induct F)
  apply (auto simp add: derivation_ge_def)
  done

lemma LeftDerivationFix_splits_at_nonterminal:
  assumes "LeftDerivationFix a i D j b"
  assumes "is_nonterminal (a ! i)"
  shows "\<exists> U a1 a2 b1. splits_at a i a1 U a2 \<and> splits_at b j b1 U a2 \<and> LeftDerivation a1 D b1"
proof -
  note hyp = LeftDerivationFix_def[where \<alpha>=a and \<beta>=b and D=D and i=i and j=j]
  from hyp obtain E F where EF:
    "D = E @ derivation_shift F 0 (Suc j) \<and> LeftDerivation (take i a) E (take j b) \<and> 
      LeftDerivation (drop (Suc i) a) F (drop (Suc j) b)"
    using assms by blast
  have "\<exists> \<beta>. LeftDerivation a E \<beta> \<and> LeftDerivation \<beta> (derivation_shift F 0 (Suc j)) b"
    using EF LeftDerivation_append assms(1) hyp by blast
  then obtain \<beta> where \<beta>_intro: 
    "LeftDerivation a E \<beta> \<and> LeftDerivation \<beta> (derivation_shift F 0 (Suc j)) b" by blast
  have "LeftDerivation ((take i a)@(drop i a)) E ((take j b)@(drop i a))"
    by (metis EF LeftDerivation_append_suffix append_take_drop_id assms(1) hyp is_sentence_concat)
  then have "LeftDerivation a E ((take j b)@(drop i a))" by simp 
  then have \<beta>_decomposed: "\<beta> = (take j b)@(drop i a)"
    using Derivation_unique_dest LeftDerivation_implies_Derivation \<beta>_intro by blast 
  then have "\<beta> ! j = a ! i"
    by (metis Cons_nth_drop_Suc assms(1) hyp length_take min.absorb2 nth_append_length 
      order.strict_implies_order)
  then have is_nt: "is_nonterminal (\<beta> ! j)" by (simp add: assms(2)) 
  have index_j: "j < length \<beta>" using \<beta>_decomposed assms(1) hyp by auto 
  have derivation: "LeftDerivation \<beta> (derivation_shift F 0 (Suc j)) b"
    by (simp add: \<beta>_intro) 
  from LeftDerivation_impossible[OF derivation index_j is_nt derivation_ge_shift]
  have F: "F = []" by (metis length_0_conv length_derivation_shift)    
  then have \<beta>_is_b: "\<beta> = b" using \<beta>_intro by auto     
  show ?thesis
    apply (rule_tac x="a ! i" in exI)
    apply (rule_tac x="take i a" in exI)
    apply (rule_tac x="drop (Suc i) a" in exI)
    apply (rule_tac x="take j b" in exI)
    using EF F assms(1) hyp splits_at_def by auto
qed

lemma LeftDerivationIntro_implies_nonterminal: 
  "LeftDerivationIntro \<alpha> i (snd e) ix E j \<gamma> \<Longrightarrow> is_nonterminal (\<alpha> ! i)"
by (simp add: LeftDerivationIntro_def LeftDerives1_def leftmost_is_nonterminal)

lemma LeftDerivationIntrosAt_implies_nonterminal:
  "LeftDerivationIntrosAt a D L index \<Longrightarrow> is_nonterminal((ladder_\<alpha> a D L index) ! (ladder_i L index))"
by (meson LeftDerivationIntro_implies_nonterminal LeftDerivationIntrosAt_def)
   
lemma LeftDerivationIntro_examine_rule: 
  "LeftDerivationIntro \<alpha> i r ix D j \<gamma> \<Longrightarrow> splits_at \<alpha> i \<alpha>1 M \<alpha>2 \<Longrightarrow> 
    \<exists> \<eta>. M = fst r \<and> \<eta> = snd r \<and> (M, \<eta>) \<in> \<RR>"
by (metis Derives1_nonterminal Derives1_rule LeftDerivationIntro_def LeftDerives1_implies_Derives1 
  prod.collapse)

lemma LeftDerivation_skip_prefixword_ex:
  assumes "LeftDerivation (u@v) D w"
  assumes "is_word u"
  shows "\<exists> w'. w = u@w' \<and> LeftDerivation v (derivation_shift D (length u) 0) w'"
by (metis LeftDerivation.simps(1) LeftDerivation_breakdown LeftDerivation_implies_Derivation 
  LeftDerivation_skip_prefix append_eq_conv_conj assms(1) assms(2) is_word_Derivation 
  is_word_Derivation_derivation_ge)

definition ladder_cut :: "ladder \<Rightarrow> nat \<Rightarrow> ladder"
where "ladder_cut L n = (let i = length L - 1 in L[i := (n, snd (L ! i))])"

fun deriv_shift :: "nat \<Rightarrow> nat \<Rightarrow> deriv \<Rightarrow> deriv"
where "deriv_shift dn dj (n, j, i) = (n - dn, j - dj, i)"

definition ladder_shift :: "ladder \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ladder"
where "ladder_shift L dn dj = map (deriv_shift dn dj) L"

lemma splits_at_append_suffix_prevails: 
  assumes "splits_at (a@b) i u N v"
  assumes "i < length a"
  shows "\<exists> v'. v = v'@b \<and> a=u@[N]@v'"
proof -
  have "min (length a) (Suc i) = Suc i"
    using Suc_leI assms(2) min.absorb2 by blast
  then show ?thesis
    by (metis (no_types) append_assoc append_eq_conv_conj append_take_drop_id assms(1) 
      hd_drop_conv_nth length_take splits_at_def take_hd_drop)
qed

lemma derivation_shift_right_left_cancel:
  "derivation_shift (derivation_shift D 0 r) r 0 = D"
by (induct D, auto)

lemma derivation_shift_left_right_cancel:
  assumes "derivation_ge D r"
  shows "derivation_shift (derivation_shift D r 0) 0 r = D"
using assms derivation_ge_shift_simp derivation_shift_0_shift by auto

lemma LeftDerivation_ge_take:
  assumes "derivation_ge D k"
  assumes "LeftDerivation a D b"
  assumes "D \<noteq> []"
  shows "take k a = take k b \<and> is_word (take k a)"
proof -
  obtain d D' where d: "d#D' = D" using assms(3) list.exhaust by blast 
  then have "\<exists> x. LeftDerives1 a (fst d) (snd d) x \<and> LeftDerivation x D' b"
    using LeftDerivation.simps(2) assms(2) by blast
  then obtain x where x: "LeftDerives1 a (fst d) (snd d) x \<and> LeftDerivation x D' b" by blast
  have fst_d_k: "fst d \<ge> k" using d assms(1) derivation_ge_cons by blast 
  from x fst_d_k have is_word: "is_word (take k a)"
    by (metis LeftDerives1_def append_take_drop_id is_word_append leftmost_def 
      min.absorb2 take_append take_take)
  have is_eq: "take k a = take k b"
    using Derivation_take LeftDerivation_implies_Derivation assms(1) assms(2) by blast
  show ?thesis using is_word is_eq by blast
qed 
        
lemma LeftDerivationFix_splits_at_symbol:
  assumes "LeftDerivationFix a i D j b"
  shows "\<exists> U a1 a2 b1 b2 n. splits_at a i a1 U a2 \<and> splits_at b j b1 U b2 \<and> 
    n \<le> length D \<and> LeftDerivation a1 (take n D) b1 \<and> derivation_ge (drop n D) (Suc(length b1)) \<and>
    LeftDerivation a2 (derivation_shift (drop n D) (Suc(length b1)) 0) b2 \<and>
    (n = length D \<or> (n < length D \<and> is_word (b1@[U])))"
proof -
  note hyp = LeftDerivationFix_def[where \<alpha>=a and \<beta>=b and D=D and i=i and j=j]
  from hyp obtain E F where EF:
    "D = E @ derivation_shift F 0 (Suc j) \<and> LeftDerivation (take i a) E (take j b) \<and> 
      LeftDerivation (drop (Suc i) a) F (drop (Suc j) b)"
    using assms by blast
  have "\<exists> \<beta>. LeftDerivation a E \<beta> \<and> LeftDerivation \<beta> (derivation_shift F 0 (Suc j)) b"
    using EF LeftDerivation_append assms(1) hyp by blast
  then obtain \<beta> where \<beta>_intro: 
    "LeftDerivation a E \<beta> \<and> LeftDerivation \<beta> (derivation_shift F 0 (Suc j)) b" by blast
  have "LeftDerivation ((take i a)@(drop i a)) E ((take j b)@(drop i a))"
    by (metis EF LeftDerivation_append_suffix append_take_drop_id assms(1) hyp is_sentence_concat)
  then have "LeftDerivation a E ((take j b)@(drop i a))" by simp 
  then have \<beta>_decomposed: "\<beta> = (take j b)@(drop i a)"
    using Derivation_unique_dest LeftDerivation_implies_Derivation \<beta>_intro by blast 
  have derivation: "LeftDerivation \<beta> (derivation_shift F 0 (Suc j)) b"
    by (simp add: \<beta>_intro) 
  have "\<exists> n. n \<le> length D \<and> E = take n D"
    by (metis EF append_eq_conv_conj is_prefix_length is_prefix_take)
  then obtain n where n: "n \<le> length D \<and> E = take n D" by blast
  have F_def: "drop n D = derivation_shift F 0 (Suc j)"
    by (metis EF append_eq_conv_conj length_take min.absorb2 n)
  have min_j: "min (length b) j = j" using assms hyp by linarith 
  have derivation_ge_Suc_j: "derivation_ge (drop n D) (Suc j)"
    using F_def derivation_ge_shift by simp
  have LeftDerivation_\<beta>_b: "LeftDerivation \<beta> (drop n D) b" by (simp add: F_def \<beta>_intro)
  have is_word_Suc_j_b: "n \<noteq> length D \<Longrightarrow> is_word (take (Suc j) b)"
    by (metis EF F_def LeftDerivation_ge_take \<beta>_intro append_Nil2 derivation_ge_Suc_j 
      length_take min.absorb2 n)
  have take_Suc_j_b_decompose: "take (Suc j) b = take j b @ [a ! i]"
    using assms hyp take_Suc_conv_app_nth by auto
  show ?thesis
    apply (rule_tac x="a ! i" in exI)
    apply (rule_tac x="take i a" in exI)
    apply (rule_tac x="drop (Suc i) a" in exI)
    apply (rule_tac x="take j b" in exI)
    apply (rule_tac x="drop (Suc j) b" in exI)
    apply (rule_tac x="n" in exI)
    apply (auto simp add: min_j)
    using assms hyp splits_at_def apply blast
    using assms hyp splits_at_def apply blast
    using n apply blast
    using EF n apply simp
    using F_def apply simp
    using derivation_ge_shift apply blast
    using F_def  derivation_shift_right_left_cancel apply simp
    using EF apply blast
    using n apply arith
    using is_word_Suc_j_b  take_Suc_j_b_decompose is_word_append apply simp+
    done
qed    

lemma LeftDerivation_breakdown': "LeftDerivation (u @ v) D w \<Longrightarrow>
  \<exists>n w1 w2.
    n \<le> length D \<and>
    w = w1 @ w2 \<and>
    LeftDerivation u (take n D) w1 \<and>
    derivation_ge (drop n D) (length w1) \<and>
    LeftDerivation v (derivation_shift (drop n D) (length w1) 0) w2"
proof -
  assume hyp: "LeftDerivation (u @ v) D w"
  from LeftDerivation_breakdown[OF hyp] obtain n w1 w2 where breakdown:
   "w = w1 @ w2 \<and>
    LeftDerivation u (take n D) w1 \<and>
    derivation_ge (drop n D) (length w1) \<and>
    LeftDerivation v (derivation_shift (drop n D) (length w1) 0) w2" by blast
  obtain m where m: "m = min (length D) n" by blast
  have take_m: "take m D = take n D" using m is_prefix_take take_prefix by fastforce
  have drop_m: "drop m D = drop n D"
    by (metis append_eq_conv_conj append_take_drop_id length_take m) 
  have m_bound: "m \<le> length D" by (simp add: m)      
  show ?thesis
    apply (rule_tac x="m" in exI)
    apply (rule_tac x="w1" in exI)
    apply (rule_tac x="w2" in exI)
    using breakdown m_bound take_m drop_m by auto
qed    

lemma LeftDerives1_append_replace_in_left: 
  assumes ld1: "LeftDerives1 (\<alpha>@\<delta>) i r \<beta>"
  assumes i_bound: "i < length \<alpha>"
  shows "\<exists> \<alpha>'. \<beta> = \<alpha>'@\<delta> \<and> LeftDerives1 \<alpha> i r \<alpha>' \<and> i + length (snd r) \<le> length \<alpha>'"
proof - 
  obtain \<alpha>' where \<alpha>': "\<alpha>' = (take i \<alpha>)@(snd r)@(drop (i+1) \<alpha>)" by blast
  have fst_r: "fst r = \<alpha> ! i"
  proof -
    have "\<forall>ss n p ssa. \<not> LeftDerives1 ss n p ssa \<or> Derives1 ss n p ssa"
      using LeftDerives1_implies_Derives1 by blast
    then have "Derives1 (\<alpha> @ \<delta>) i r \<beta>"
      using ld1 by blast
    then show ?thesis
      using Derives1_nonterminal i_bound splits_at_def by auto
  qed    
  have "Derives1 \<alpha> i r \<alpha>'"
    using i_bound ld1
    apply (auto simp add: \<alpha>' Derives1_def)
    apply (rule_tac x="take i \<alpha>" in exI)
    apply (rule_tac x="drop (i+1) \<alpha>" in exI)
    apply (rule_tac x="fst r" in exI)
    apply auto
    apply (simp add: fst_r)
    using id_take_nth_drop apply blast
    using Derives1_sentence1 LeftDerives1_implies_Derives1 is_sentence_concat 
      is_sentence_take apply blast
    apply (metis Derives1_sentence1 LeftDerives1_implies_Derives1 append_take_drop_id 
      is_sentence_concat)
    using Derives1_rule LeftDerives1_implies_Derives1 by blast
  then have leftderives1_\<alpha>_\<alpha>': "LeftDerives1 \<alpha> i r \<alpha>'"
    using LeftDerives1_def i_bound ld1 leftmost_cons_less by auto
  have i_bound_\<alpha>': "i + length (snd r) \<le> length \<alpha>'"
    using \<alpha>' i_bound
    by (simp add: add_mono_thms_linordered_semiring(2) le_add1 less_or_eq_imp_le min.absorb2)
  have is_sentence_\<delta>: "is_sentence \<delta>"
    using Derives1_sentence1 LeftDerives1_implies_Derives1 is_sentence_concat ld1 by blast
  then have \<beta>: "\<beta> = \<alpha>'@\<delta>"
    using ld1 leftderives1_\<alpha>_\<alpha>' Derives1_append_suffix Derives1_unique_dest 
      LeftDerives1_implies_Derives1 by blast 
  show ?thesis
    apply (rule_tac x="\<alpha>'" in exI)
    using \<beta> i_bound_\<alpha>' leftderives1_\<alpha>_\<alpha>' by blast
qed   
    
lemma LeftDerivationIntro_propagate:
  assumes intro: "LeftDerivationIntro (\<alpha>@\<delta>) i r ix D j \<gamma>"
  assumes i_\<alpha>: "i < length \<alpha>"
  assumes non: "is_nonterminal (\<gamma> ! j)"
  shows "\<exists> \<omega>. LeftDerivation \<alpha> ((i,r)#D) \<omega> \<and> \<gamma> = \<omega>@\<delta> \<and> j < length \<omega>"
proof -
  from intro LeftDerivationIntro_def[where \<alpha>="\<alpha>@\<delta>" and i=i and r=r and ix=ix and D=D and 
    j=j and \<gamma>=\<gamma>]
  obtain \<beta> where ld_\<beta>: "LeftDerives1 (\<alpha> @ \<delta>) i r \<beta>" and 
     ix: "ix < length (snd r) \<and> snd r ! ix = \<gamma> ! j" and 
     \<beta>_fix: "LeftDerivationFix \<beta> (i + ix) D j \<gamma>"
     by blast
  from LeftDerives1_append_replace_in_left[OF ld_\<beta> i_\<alpha>]
  obtain \<alpha>' where \<alpha>': "\<beta> = \<alpha>' @ \<delta> \<and> LeftDerives1 \<alpha> i r \<alpha>' \<and> i + length (snd r) \<le> length \<alpha>'"
    by blast
  have i_plus_ix_bound: "i + ix < length \<alpha>'" using \<alpha>' ix by linarith
  have ld_\<gamma>: "LeftDerivationFix (\<alpha>' @ \<delta>) (i + ix) D j \<gamma>"
    using \<beta>_fix \<alpha>' by simp
  then have non_i_ix: "is_nonterminal ((\<alpha>' @ \<delta>) ! (i + ix))"
    by (simp add: LeftDerivationFix_def non)
  from LeftDerivationFix_splits_at_nonterminal[OF ld_\<gamma> non_i_ix] 
  obtain U a1 a2 b1 where U: 
    "splits_at (\<alpha>' @ \<delta>) (i + ix) a1 U a2 \<and> splits_at \<gamma> j b1 U a2 \<and> LeftDerivation a1 D b1" 
    by blast
  have "\<exists> q. a2 = q@\<delta> \<and> \<alpha>' = a1 @ [U] @ q" 
    using splits_at_append_suffix_prevails[OF _ i_plus_ix_bound, where b=\<delta>] U by blast
  then obtain q where q: "a2 = q@\<delta> \<and> \<alpha>' = a1 @ [U] @ q" by blast
  show ?thesis
    apply (rule_tac x="b1@[U]@q" in exI)
    apply auto
    apply (rule_tac x="\<alpha>'" in exI)
    apply (metis LeftDerivationFix_def LeftDerivation_append_suffix U \<alpha>' 
      q append_Cons append_Nil is_sentence_concat ld_\<gamma>)
    using U q splits_at_combine apply auto[1]
    using U splits_at_def by auto  
qed    

lemma LeftDerivationIntro_finish:
  assumes intro: "LeftDerivationIntro (\<alpha>@\<delta>) i r ix D j \<gamma>"
  assumes i_\<alpha>: "i < length \<alpha>"
  shows "\<exists> k \<omega> \<delta>'.
    k \<le> length D \<and>
    LeftDerivation \<alpha> ((i, r)#(take k D)) \<omega> \<and>
    LeftDerivation (\<alpha> @ \<delta>) ((i, r)#(take k D)) (\<omega> @ \<delta>) \<and>
    derivation_ge (drop k D) (length \<omega>) \<and>
    LeftDerivation \<delta> (derivation_shift (drop k D) (length \<omega>) 0) \<delta>' \<and>
    \<gamma> = \<omega> @ \<delta>' \<and> j < length \<omega>"
proof -
  from intro LeftDerivationIntro_def[where \<alpha>="\<alpha>@\<delta>" and i=i and r=r and ix=ix and D=D and 
    j=j and \<gamma>=\<gamma>]
  obtain \<beta> where ld_\<beta>: "LeftDerives1 (\<alpha> @ \<delta>) i r \<beta>" and 
     ix: "ix < length (snd r) \<and> snd r ! ix = \<gamma> ! j" and 
     \<beta>_fix: "LeftDerivationFix \<beta> (i + ix) D j \<gamma>"
     by blast
  from LeftDerives1_append_replace_in_left[OF ld_\<beta> i_\<alpha>]
  obtain \<alpha>' where \<alpha>': "\<beta> = \<alpha>' @ \<delta> \<and> LeftDerives1 \<alpha> i r \<alpha>' \<and> i + length (snd r) \<le> length \<alpha>'"
    by blast
  have i_plus_ix_bound: "i + ix < length \<alpha>'" using \<alpha>' ix by linarith
  have ld_\<gamma>: "LeftDerivationFix (\<alpha>' @ \<delta>) (i + ix) D j \<gamma>"
    using \<beta>_fix \<alpha>' by simp
  from LeftDerivationFix_splits_at_symbol[OF ld_\<gamma>] 
  obtain U a1 a2 b1 b2 n where U: 
    "splits_at (\<alpha>' @ \<delta>) (i + ix) a1 U a2 \<and>
     splits_at \<gamma> j b1 U b2 \<and>
     n \<le> length D \<and>
     LeftDerivation a1 (take n D) b1 \<and>
     derivation_ge (drop n D) (Suc (length b1)) \<and>
     LeftDerivation a2 (derivation_shift (drop n D) (Suc (length b1)) 0) b2 \<and>
     (n = length D \<or> n < length D \<and> is_word (b1 @ [U]))"
    by blast
  have n_bound: "n \<le> length D" using U by blast
  have "\<exists> q. a2 = q@\<delta> \<and> \<alpha>' = a1 @ [U] @ q" 
    using splits_at_append_suffix_prevails[OF _ i_plus_ix_bound, where b=\<delta>] U by blast
  then obtain q where q: "a2 = q@\<delta> \<and> \<alpha>' = a1 @ [U] @ q" by blast
  have j: "j = length b1"
    using U by (simp add: dual_order.strict_implies_order  min.absorb2 splits_at_def)
  have "n = length D \<or> n < length D \<and> is_word (b1 @ [U])" using U by blast
  then show ?thesis
  proof (induct rule: disjCases2)
    case 1
      from 1 have drop_n_D: "drop n D = []" by (simp add: U)
      then have "LeftDerivation a2 [] b2" using U by simp
      then have a2_eq_b2: "a2 = b2" by simp
        show ?case
          apply (rule_tac x="n" in exI)
          apply (rule_tac x="b1@[U]@q" in exI)
          apply (rule_tac x="\<delta>" in exI)
          apply auto
          apply (simp add: 1)
          apply (rule_tac x="\<alpha>'" in exI)
          apply (metis LeftDerivationFix_is_sentence LeftDerivation_append_suffix U \<alpha>' 
            append_Cons append_Nil is_sentence_concat ld_\<gamma> q)
          apply (rule_tac x="\<alpha>' @ \<delta>" in exI)
          apply (metis "1.hyps" LeftDerivationFix_def U \<alpha>' a2_eq_b2 id_take_nth_drop ld_\<beta> 
            ld_\<gamma> q splits_at_def take_all)
          apply (simp add: drop_n_D)+
          apply (metis U a2_eq_b2 id_take_nth_drop q splits_at_def)
          using j apply arith
          done
  next
    case 2   
      obtain E where E: "E = (derivation_shift (drop n D) (Suc (length b1)) 0)" by blast
      then have "LeftDerivation (q@\<delta>) E b2" using U q  by simp
      from LeftDerivation_breakdown'[OF this] obtain n' w1 w2 where w1w2:
        "n' \<le> length E \<and>
         b2 = w1 @ w2 \<and>
         LeftDerivation q (take n' E) w1 \<and>
         derivation_ge (drop n' E) (length w1) \<and>
         LeftDerivation \<delta> (derivation_shift (drop n' E) (length w1) 0) w2" by blast
      have length_E_D: "length E = length D - n" using E n_bound by simp
      have n_plus_n'_bound: "n + n' \<le> length D" using length_E_D w1w2 n_bound by arith
      have take_breakdown: "take (n + n') D = (take n D) @ (take n' (drop n D))"
        using take_add by blast
      have q_w1: "LeftDerivation q (take n' E) w1" using w1w2 by blast
      have isw: "is_word (b1 @ [U])" using 2 by blast
      have take_n': "take n' (drop n D) = derivation_shift (take n' E) 0 (Suc (length b1))"
        by (metis E U derivation_shift_left_right_cancel take_derivation_shift)  
      have \<alpha>'_derives_b1_U_w1: "LeftDerivation \<alpha>' (take (n + n') D) (b1 @ U # w1)"
        apply (subst take_breakdown)
        apply (rule_tac LeftDerivation_implies_append[where b="b1@[U]@q"])
        apply (metis LeftDerivationFix_is_sentence LeftDerivation_append_suffix U 
          is_sentence_concat ld_\<gamma> q)
        apply (simp add: take_n')
        by (rule LeftDerivation_append_prefix[OF q_w1, where u = "b1@[U]", OF isw, simplified])
      have dge: "derivation_ge (drop (n + n') D) (Suc (length b1 + length w1))"
      proof -
        have "derivation_ge (drop n' (drop n D)) (length b1 + 1 + length w1)"
          by (metis (no_types) E Suc_eq_plus1 U append_take_drop_id derivation_ge_append derivation_ge_shift_plus drop_derivation_shift w1w2)
        then show "derivation_ge (drop (n + n') D) (Suc (length b1 + length w1))"
          by (metis (no_types) Suc_eq_plus1 add.commute drop_drop semiring_normalization_rules(23))
      qed
      show ?case
        apply (rule_tac x="n+n'" in exI)
        apply (rule_tac x="b1 @ [U] @ w1" in exI)
        apply (rule_tac x=w2 in exI)
        apply auto
        using n_plus_n'_bound apply simp
        apply (rule_tac x="\<alpha>'" in exI)
        using \<alpha>' \<alpha>'_derives_b1_U_w1 apply blast
        apply (rule_tac x="\<alpha>' @ \<delta>" in exI)
        apply (metis Cons_eq_appendI LeftDerivationFix_is_sentence LeftDerivation_append_suffix
          \<alpha>' \<alpha>'_derives_b1_U_w1 append_assoc is_sentence_concat ld_\<beta> ld_\<gamma>)
        apply (rule dge)
        apply (metis E Suc_eq_plus1 add.commute derivation_shift_0_shift drop_derivation_shift 
          drop_drop w1w2)
        using U splits_at_combine w1w2 apply auto[1]
        by (simp add: j)  
  qed      
qed    

lemma LeftDerivationLadder_propagate:
  "LeftDerivationLadder (\<alpha>@\<delta>) D L \<gamma> \<Longrightarrow> ladder_i L 0 < length \<alpha> \<Longrightarrow> n = ladder_n L index
   \<Longrightarrow> index < length L \<Longrightarrow> 
     if (index + 1 < length L) then
       (\<exists> \<beta>. LeftDerivation \<alpha> (take n D) \<beta> \<and> ladder_\<gamma> (\<alpha>@\<delta>) D L index = \<beta>@\<delta> \<and> 
         ladder_j L index < length \<beta>)
     else 
       (\<exists> n' \<beta> \<delta>'. (index = 0 \<or> ladder_prev_n L index < n') \<and> n' \<le> n \<and> LeftDerivation \<alpha> (take n' D) \<beta> \<and>
         LeftDerivation (\<alpha>@\<delta>) (take n' D) (\<beta>@\<delta>) \<and>
         derivation_ge (drop n' D) (length \<beta>) \<and> 
         LeftDerivation \<delta> (derivation_shift (drop n' D) (length \<beta>) 0) \<delta>' \<and>
         ladder_\<gamma> (\<alpha>@\<delta>) D L index = \<beta>@\<delta>' \<and> ladder_j L index < length \<beta>)"
proof (induct index arbitrary: n)
  case 0
  have ldfix:
    "LeftDerivationFix (\<alpha>@\<delta>) (ladder_i L 0) (take n D) (ladder_j L 0) (ladder_\<gamma> (\<alpha>@\<delta>) D L 0)"
    using "0.prems"(1) "0.prems"(3) LeftDerivationLadder_def by blast
  from 0 have "1 < length L \<or> 1 = length L" by arith
  then show ?case
  proof (induct rule: disjCases2) 
    case 1
    have "LeftDerivationIntrosAt (\<alpha>@\<delta>) D L 1"
      using "0.prems"(1) "1.hyps" LeftDerivationIntros_def LeftDerivationLadder_def by blast
    from LeftDerivationIntrosAt_implies_nonterminal[OF this] 
    have "is_nonterminal (ladder_\<gamma> (\<alpha> @ \<delta>) D L 0 ! ladder_j L 0)"
      by (simp add: ladder_\<alpha>_def ladder_i_def)
    with ldfix have "is_nonterminal ((\<alpha>@\<delta>) ! (ladder_i L 0))" by (simp add: LeftDerivationFix_def)
    from LeftDerivationFix_splits_at_nonterminal[OF ldfix this] obtain U a1 a2 b where thesplit:
      "splits_at (\<alpha> @ \<delta>) (ladder_i L 0) a1 U a2 \<and>
       splits_at (ladder_\<gamma> (\<alpha> @ \<delta>) D L 0) (ladder_j L 0) b U a2 \<and> 
       LeftDerivation a1 (take n D) b" by blast
    have "\<exists> \<delta>'. a2 = \<delta>' @ \<delta> \<and> \<alpha> = a1 @ [U] @ \<delta>'" 
    using thesplit splits_at_append_suffix_prevails using "0.prems"(2) by blast
    then obtain \<delta>' where \<delta>': "a2 = \<delta>' @ \<delta> \<and> \<alpha> = a1 @ ([U] @ \<delta>')" by blast
    obtain \<beta> where \<beta>: "\<beta> = b @ ([U] @ \<delta>')" by blast
    have "is_sentence \<alpha>" using LeftDerivationFix_is_sentence is_sentence_concat ldfix by blast
    then have "is_sentence ([U] @ \<delta>')" using \<delta>' is_sentence_concat by blast
    with \<delta>' thesplit have "LeftDerivation (a1 @ ([U] @ \<delta>')) (take n D) (b @ ([U] @ \<delta>'))"
      using LeftDerivation_append_suffix by blast
    then have \<alpha>_derives_\<beta>: "LeftDerivation \<alpha> (take n D) \<beta>" using \<beta> \<delta>' by blast
    have \<beta>_append_\<delta>: "ladder_\<gamma> (\<alpha> @ \<delta>) D L 0 = \<beta>@\<delta>" 
      by (metis \<beta> \<delta>' append_assoc splits_at_combine thesplit) 
    have ladder_j_bound: "ladder_j L 0 < length \<beta>"
      by (metis One_nat_def \<beta> diff_add_inverse dual_order.strict_implies_order leD le_add1 
        length_Cons length_append length_take list.size(3) min.absorb2 neq0_conv splits_at_def 
        thesplit zero_less_diff zero_less_one)
    show ?case
      using 1 apply simp
      apply (rule_tac x="\<beta>" in exI)
      by (auto simp add: \<alpha>_derives_\<beta> \<beta>_append_\<delta> ladder_j_bound)
  next
    case 2  
    note case_2 = 2
    have n_def: "n = length D"
      by (metis "0.prems"(1) "0.prems"(3) "2.hyps" LeftDerivationLadder_def One_nat_def 
        diff_Suc_1 is_ladder_def ladder_last_n_intro)
    then have take_n_D: "take n D = D" by (simp add: eq_imp_le)   
    from LeftDerivationFix_splits_at_symbol[OF ldfix] obtain U a1 a2 b1 b2 m where U:
      "splits_at (\<alpha> @ \<delta>) (ladder_i L 0) a1 U a2 \<and>
       splits_at (ladder_\<gamma> (\<alpha> @ \<delta>) D L 0) (ladder_j L 0) b1 U b2 \<and>
       m \<le> length (take n D) \<and>
       LeftDerivation a1 (take m (take n D)) b1 \<and>
       derivation_ge (drop m (take n D)) (Suc (length b1)) \<and> 
       LeftDerivation a2 (derivation_shift (drop m (take n D)) (Suc (length b1)) 0) b2 \<and>
       (m = length (take n D) \<or> (m < length (take n D) \<and> is_word (b1 @ [U])))" by blast
    obtain D' where D': "D' = derivation_shift (drop m D) (Suc (length b1)) 0" by blast
    then have a2_derives_b2: "LeftDerivation a2 D' b2" using U take_n_D by auto
    from U have m_leq_n: "m \<le> n"
      by (simp add: "0.prems"(1) "0.prems"(3) "0.prems"(4) LeftDerivationLadder_def is_ladder_def 
         min.absorb2) 
    from U have "splits_at (\<alpha> @ \<delta>) (ladder_i L 0) a1 U a2" by blast
    from splits_at_append_suffix_prevails[OF this 0(2)] obtain v' where 
      v': "a2 = v' @ \<delta> \<and> \<alpha> = a1 @ [U] @ v'" by blast
    have a1_derives_b1: "LeftDerivation a1 (take m D) b1" using m_leq_n U
      by (metis "0.prems"(1) "0.prems"(3) "2.hyps" LeftDerivationLadder_def One_nat_def 
        cancel_comm_monoid_add_class.diff_cancel is_ladder_def ladder_last_n_intro order_refl 
        take_all) 
    have "LeftDerivation (v' @ \<delta>) D' b2" using a2_derives_b2 v' by simp
    from LeftDerivation_breakdown'[OF this] obtain m' w1 w2 where w12:
      "b2 = w1 @ w2 \<and>
       m' \<le> length D' \<and>
       LeftDerivation v' (take m' D') w1 \<and>
       derivation_ge (drop m' D') (length w1) \<and>
       LeftDerivation \<delta> (derivation_shift (drop m' D') (length w1) 0) w2" by blast
    have "length D' \<le> length D - m" by (simp add: D')
    then have "m' \<le> length D - m" using w12 dual_order.trans by blast   
    then have m_m'_leq_n: "m + m' \<le> n" using n_def m_leq_n Nat.le_diff_conv2 add.commute 
      by linarith  
    obtain \<beta> where \<beta>: "\<beta> = b1 @ ([U] @ w1)" by blast
    have "is_sentence ([U] @ v')"
      using LeftDerivationFix_is_sentence is_sentence_concat ldfix v' by blast 
    then have "LeftDerivation (a1 @ ([U] @ v')) (take m D) (b1 @ ([U] @ v'))"
      using LeftDerivation_append_suffix a1_derives_b1 by blast
    then have \<alpha>_derives_pre_\<beta>: "LeftDerivation \<alpha> (take m D) (b1 @ ([U] @ v'))" 
      using v' by blast 
    have "m = n \<or> (m < n \<and> is_word (b1 @ [U]))"
      using U n_def[symmetric] take_n_D by simp
    then have pre_\<beta>_derives_\<beta>: "LeftDerivation (b1 @ ([U] @ v')) (take m' (drop m D)) \<beta>"
    proof (induct rule: disjCases2)
      case 1
        then have "m' = 0" using m_m'_leq_n by arith
        then show ?case
          apply (simp add: \<beta>)
          using w12 by simp
    next
      case 2
        then have is_word_prefix: "is_word (b1 @ [U])" by blast
        have take_drop_eq: "take m' (drop m D) = derivation_shift (take m' D') 
            0 (length (b1 @ [U]))"
            apply (simp add: D' take_derivation_shift)
            by (metis U derivation_shift_left_right_cancel take_derivation_shift take_n_D)
        have v'_derives_w1: "LeftDerivation v' (take m' D') w1"
          by (simp add: w12)  
        with is_word_prefix have 
          "LeftDerivation ((b1 @ [U]) @ v') (derivation_shift (take m' D') 
            0 (length (b1 @ [U]))) ((b1 @ [U]) @ w1)"
          using  LeftDerivation_append_prefix by blast
        with take_drop_eq show ?case by (simp add: \<beta>) 
    qed   
    have "(take m D) @ (take m' (drop m D)) = (take (m + m') D)"
      by (simp add: take_add)  
    then have \<alpha>_derives_\<beta>: "LeftDerivation \<alpha> (take (m + m') D) \<beta>"
      using LeftDerivation_implies_append \<alpha>_derives_pre_\<beta> pre_\<beta>_derives_\<beta> by fastforce
    have derivation_ge_drop_m_m': "derivation_ge (drop (m + m') D) (length \<beta>)"
      proof -
        have f1: "drop m' (drop m D) = drop (m + m') D"
          by (simp add: add.commute)
        have "derivation_ge (drop m' (drop m D)) (Suc (length b1))"
          by (metis (no_types) U append_take_drop_id derivation_ge_append take_n_D)
        then show "derivation_ge (drop (m + m') D) (length \<beta>)"
          using f1 by (metis (no_types) D' \<beta> append_assoc derivation_ge_shift_plus 
            drop_derivation_shift length_append length_append_singleton w12)   
      qed  
    have \<delta>_derives_w2: "LeftDerivation \<delta> (derivation_shift (drop (m + m') D) (length \<beta>) 0) w2" 
      proof -
        have "derivation_shift (drop m' D') (length w1) 0 = derivation_shift (drop (m + m') D) (length \<beta>) 0"
          by (simp add: D' \<beta> add.commute derivation_shift_0_shift drop_derivation_shift)
        then show "LeftDerivation \<delta> (derivation_shift (drop (m + m') D) (length \<beta>) 0) w2"
          using w12 by presburger
      qed
    have ladder_\<gamma>_def: "ladder_\<gamma> (\<alpha> @ \<delta>) D L 0 = \<beta> @ w2"
      using U \<beta> splits_at_combine w12 by auto
    have ladder_j_bound: "ladder_j L 0 < length \<beta>" using U \<beta> splits_at_def by auto 
    show ?case
      using 2 apply simp
      apply (rule_tac x="m + m'" in exI)
      apply (auto simp add: m_m'_leq_n)
      apply (rule_tac x="\<beta>" in exI)
      apply (auto simp add: \<alpha>_derives_\<beta>)
      using LeftDerivationFix_is_sentence LeftDerivation_append_suffix \<alpha>_derives_\<beta> 
        is_sentence_concat ldfix apply blast
      using derivation_ge_drop_m_m' apply blast
      apply (rule_tac x="w2" in exI)
      apply auto
      using \<delta>_derives_w2 apply blast
      using ladder_\<gamma>_def apply blast
      using ladder_j_bound apply blast
      done
  qed
next
  case (Suc index)
  have step: "LeftDerivationIntrosAt (\<alpha>@\<delta>) D L (Suc index)"
    by (metis LeftDerivationIntros_def LeftDerivationLadder_def Suc.prems(1) Suc.prems(4)      
      Suc_eq_plus1_left le_add1)
  have index_plus_1_bound: "index + 1 < length L"
    using Suc.prems(4) by linarith
  then have index_bound: "index < length L" by arith
  obtain n' where n': "n' = ladder_n L index" by blast
  from Suc.hyps[OF Suc.prems(1) Suc.prems(2) n' index_bound] index_plus_1_bound 
  have "\<exists> \<alpha>'. LeftDerivation \<alpha> (take n' D) \<alpha>' \<and> 
    ladder_\<gamma> (\<alpha>@\<delta>) D L index = \<alpha>'@\<delta> \<and> ladder_j L index < length \<alpha>'"
    by auto
  then obtain \<alpha>' where \<alpha>': "LeftDerivation \<alpha> (take n' D) \<alpha>' \<and> 
    ladder_\<gamma> (\<alpha>@\<delta>) D L index = \<alpha>'@\<delta> \<and> ladder_j L index < length \<alpha>'"
    by blast
  have Suc_index_bound: "Suc index < length L" using Suc.prems by auto
  have is_ladder: "is_ladder D L" using Suc.prems LeftDerivationLadder_def by auto 
  have n_def: "n = ladder_n L (Suc index)" 
    using Suc_index_bound n' by (simp add: Suc.prems(3)) 
  with n' have n'_less_n: "n' < n" using is_ladder Suc_index_bound is_ladder_def lessI by blast
  have ladder_\<alpha>_is_\<gamma>: "ladder_\<alpha> (\<alpha>@\<delta>) D L (Suc index) = ladder_\<gamma> (\<alpha>@\<delta>) D L index"
    by (simp add: ladder_\<alpha>_def)
  obtain i where i: "i = ladder_i L (Suc index)" by blast
  obtain e where e: "e = (D ! n')" by blast
  obtain E where E: "E = drop (Suc n') (take n D)" by blast
  obtain ix where ix: "ix = ladder_ix L (Suc index)" by blast
  obtain j where j: "j = ladder_j L (Suc index)" by blast
  obtain \<gamma> where \<gamma>: "\<gamma> = ladder_\<gamma> (\<alpha>@\<delta>) D L (Suc index)" by blast
  have intro: "LeftDerivationIntro (\<alpha>'@\<delta>) i (snd e) ix E j \<gamma>"
    by (metis E LeftDerivationIntrosAt_def \<alpha>' \<gamma> ladder_\<alpha>_is_\<gamma> 
      diff_Suc_1 e i ix j local.step n' n_def)
  have is_eq_fst_e: "i = fst e" 
    by (metis LeftDerivationIntrosAt_def diff_Suc_1 e i local.step n')
  have i_less_\<alpha>': "i < length \<alpha>'" using i \<alpha>' ladder_i_def by simp
  have "(Suc index) + 1 < length L \<or> (Suc index) + 1 = length L"
    using Suc_index_bound by arith
  then show ?case
  proof (induct rule: disjCases2)
    case 1
      from 1 have "LeftDerivationIntrosAt (\<alpha>@\<delta>) D L (Suc (Suc index))"
        by (metis LeftDerivationIntros_def LeftDerivationLadder_def Suc.prems(1) 
          Suc_eq_plus1 Suc_eq_plus1_left le_add1)
      from LeftDerivationIntrosAt_implies_nonterminal[OF this] have 
        "is_nonterminal (ladder_\<alpha> (\<alpha> @ \<delta>) D L (Suc (Suc index)) ! ladder_i L (Suc (Suc index)))"
        by blast
      then have non_\<gamma>_j: "is_nonterminal (\<gamma> ! j)" by (simp add: \<gamma> j ladder_\<alpha>_def ladder_i_def)
      from LeftDerivationIntro_propagate[OF intro i_less_\<alpha>' non_\<gamma>_j]  
      obtain \<omega> where \<omega>: "LeftDerivation \<alpha>' ((i, snd e) # E) \<omega> \<and> \<gamma> = \<omega> @ \<delta> \<and> j < length \<omega>"
        by blast
      have \<alpha>_\<omega>: "LeftDerivation \<alpha> ((take n' D)@((i, snd e) # E)) \<omega>"
        using \<alpha>' \<omega> LeftDerivation_implies_append by blast
      have i_e: "(i, snd e) = e" by (simp add: is_eq_fst_e)
      have take_n_D_e: "((take n' D)@(e # E)) = take n D"
      proof - (* automatically found *)
        obtain nn :: "(nat \<times> symbol \<times> symbol list) list \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> nat" and 
          nna :: "(nat \<times> symbol \<times> symbol list) list \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> nat" and 
          nnb :: "(nat \<times> symbol \<times> symbol list) list \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> nat" where
          f1: "(\<forall>ps psa. \<not> is_ladder ps psa \<or> psa \<noteq> [] \<and> (\<forall>n. \<not> n < length psa \<or> 
            ladder_n psa n \<le> length ps) \<and> (\<forall>n na. (\<not> n < na \<or> \<not> na < length psa) \<or> 
            ladder_n psa n < ladder_n psa na) \<and> ladder_last_n psa = length ps) \<and> 
            (\<forall>ps psa. (psa = [] \<or> nn ps psa < length psa \<and> \<not> ladder_n psa (nn ps psa) \<le> 
              length ps \<or> (nna ps psa < nnb ps psa \<and> nnb ps psa < length psa) \<and> 
              \<not> ladder_n psa (nna ps psa) < ladder_n psa (nnb ps psa) \<or> 
              ladder_last_n psa \<noteq> length ps) \<or> is_ladder ps psa)"
          using is_ladder_def by moura
        then have f2: "ladder_last_n L = length D"
          using is_ladder by blast
        have f3: "min (ladder_last_n L) n = n"
          using f1 by (metis (no_types) Suc_eq_plus1 index_plus_1_bound is_ladder 
            min.absorb2 n_def)
        then have "take n' (take n D) @ take n D ! n' # E = take n D"
          using f2 by (metis E id_take_nth_drop length_take n'_less_n)
        then show ?thesis
          using f3 f2 by (metis (no_types) append_assoc append_eq_conv_conj 
            dual_order.strict_implies_order e length_take min.absorb2 n'_less_n nth_append)
      qed             
      from 1 show ?case
        apply auto
        apply (rule_tac x=\<omega> in exI)
        apply auto
        using \<alpha>_\<omega> i_e take_n_D_e apply auto[1]
        using \<gamma> \<omega> apply blast
        using \<omega> j by blast
  next
    case 2  
    from LeftDerivationIntro_finish[OF intro i_less_\<alpha>'] obtain k \<omega> \<delta>' where kw\<delta>':
      "k \<le> length E \<and>
       LeftDerivation \<alpha>' ((i, snd e) # take k E) \<omega> \<and>
       LeftDerivation (\<alpha>' @ \<delta>) ((i, snd e) # take k E) (\<omega> @ \<delta>) \<and>
       derivation_ge (drop k E) (length \<omega>) \<and>
       LeftDerivation \<delta> (derivation_shift (drop k E) (length \<omega>) 0) \<delta>' \<and> 
       \<gamma> = \<omega> @ \<delta>' \<and> j < length \<omega>" by blast
    have ladder_last_n_1: "ladder_last_n L = n"
      by (metis "2.hyps" Suc_eq_plus1 diff_Suc_1 ladder_last_n_def n_def)
    from is_ladder have ladder_last_n_2: "ladder_last_n L = length D"
      using is_ladder_def by blast 
    from ladder_last_n_1 ladder_last_n_2 have n_eq_length_D: "n = length D" by blast  
    have take_split: "take (Suc (n' + k)) D = (take n' D) @ ((i, snd e) # take k E)"
      apply (simp add: E n_eq_length_D)
      by (metis (no_types, lifting) Cons_eq_appendI add_Suc append_eq_appendI e 
        is_eq_fst_e n'_less_n n_eq_length_D prod.collapse 
        self_append_conv2 take_Suc_conv_app_nth take_add)
    have \<alpha>_\<omega>: "LeftDerivation \<alpha> (take (Suc (n' + k)) D) \<omega>" 
      apply (subst take_split)
      apply (rule LeftDerivation_implies_append[where b="\<alpha>'"])
      apply (simp add: \<alpha>')
      using kw\<delta>' by blast 
    have Suc_n'_k_bound: "Suc (n' + k) \<le> n" using E kw\<delta>' n'_less_n by auto[1]
    from 2 show ?case
      apply auto   
      apply (rule_tac x="Suc (n' + k)" in exI)
      apply auto
      apply (simp add: ladder_prev_n_def n')
      using Suc_n'_k_bound apply blast
      apply (rule_tac x="\<omega>" in exI)
      apply auto
      using \<alpha>_\<omega> apply blast
      using \<alpha>_\<omega> LeftDerivationFix_def LeftDerivationLadder_def LeftDerivation_append_suffix 
        Suc.prems(1) is_sentence_concat apply auto[1]
      apply (metis E add.commute add_Suc_right drop_drop kw\<delta>' n_eq_length_D nat_le_linear 
        take_all)
      apply (rule_tac x="\<delta>'" in exI)
      apply auto
      apply (metis E LeftDerivationLadder_ladder_n_bound Suc.prems(1) Suc_index_bound 
        add.commute add_Suc_right drop_drop kw\<delta>' n_def n_eq_length_D take_all)
      using \<gamma> kw\<delta>' apply blast
      using j kw\<delta>' by blast
  qed
qed    

lemma ladder_i_of_cut_at_0: 
  assumes L_non_empty: "L \<noteq> []"
  shows "ladder_i (ladder_cut L n) 0 = ladder_i L 0"
proof -
  have "length L \<noteq> 0" using L_non_empty by auto
  then have "length L = 1 \<or> length L > 1" by arith
  then show ?thesis
  proof (induct rule: disjCases2)
    case 1
      then show ?case
        apply (simp add: ladder_cut_def ladder_i_def deriv_i_def)
        by (simp add: assms hd_conv_nth)
  next  
    case 2
      then show ?case
        apply (simp add: ladder_cut_def ladder_i_def deriv_i_def)
        by (metis diff_is_0_eq hd_conv_nth leD list_update_nonempty nth_list_update_neq)
  qed
qed 

lemma ladder_last_j_of_cut: 
  assumes L_non_empty: "L \<noteq> []"
  shows "ladder_last_j (ladder_cut L n) = ladder_last_j L"
proof -
  have length_L_nonzero: "length L \<noteq> 0" using L_non_empty by auto
  then have length_ladder_cut: "length (ladder_cut L n) = length L"
    by (metis ladder_cut_def length_list_update) 
  show ?thesis
    apply (simp add: ladder_last_j_def length_ladder_cut)
    apply (simp add: ladder_cut_def ladder_j_def deriv_j_def)
    by (metis length_L_nonzero diff_less neq0_conv nth_list_update_eq snd_conv zero_less_Suc)
qed

lemma length_ladder_cut:
  assumes L_non_empty: "L \<noteq> []"
  shows "length (ladder_cut L n) = length L"
by (metis ladder_cut_def length_list_update)

lemma ladder_last_n_of_cut:
  assumes L_non_empty: "L \<noteq> []"
  shows "ladder_last_n (ladder_cut L n) = n"
proof -
  show ?thesis
    apply (simp add: ladder_last_n_def length_ladder_cut[OF L_non_empty])
    apply (simp add: ladder_n_def ladder_cut_def deriv_n_def)
    by (metis assms diff_Suc_less fst_conv length_greater_0_conv nth_list_update_eq)
qed  

lemma ladder_n_of_cut:
  assumes L_non_empty: "L \<noteq> []"
  assumes "index < length L - 1"
  shows "ladder_n (ladder_cut L n) index = ladder_n L index"
by (metis assms(2) ladder_cut_def ladder_n_def nat_neq_iff nth_list_update_neq)
     
lemma ladder_n_prev_bound:
  assumes ladder: "is_ladder D L"
  assumes u_bound: "u < length L - 1"
  shows "ladder_n L u \<le> ladder_prev_n L (length L - 1)"
proof -
  have "ladder_n L u \<le> ladder_n L (length L - 2)"
  proof -
    have "u < Suc (length L - 2)"
      using u_bound by linarith
    then show ?thesis
      by (metis (no_types) diff_Suc_less is_ladder_def ladder leI length_greater_0_conv 
        not_less_eq numeral_2_eq_2 order.order_iff_strict)
  qed
  then show ?thesis
    by (metis One_nat_def Suc_diff_Suc diff_Suc_1 ladder_prev_n_def neq0_conv not_less0 
      numeral_2_eq_2 u_bound zero_less_diff)
qed      

lemma ladder_n_last_is_length:
  assumes "is_ladder D L"
  shows "ladder_n L (length L - 1) = length D"
using assms is_ladder_def ladder_last_n_intro by auto

lemma derivation_ge_shift_implies_derivation_ge:
  assumes dge: "derivation_ge (derivation_shift F 0 j) k"
  shows "derivation_ge F (k - j)"
proof -
  have "\<And> i r. (i, r) \<in> set (derivation_shift F 0 j) \<Longrightarrow> i \<ge> k"
    using dge derivation_ge_def by auto
  {
    fix i :: nat
    fix r :: "symbol \<times> (symbol list)"
    assume ir: "(i, r) \<in> set F"
    then have "(i + j, r) \<in> set (derivation_shift F 0 j)"
    proof -
      have "(i + j, r) \<in> (\<lambda>p. (fst p - 0 + j, snd p)) ` set F"
        by (metis (lifting) ir diff_zero image_eqI prod.collapse prod.inject)
      then show ?thesis
        by (simp add: derivation_shift_def)
    qed
    then have "i + j \<ge> k" using dge derivation_ge_def by auto
    then have "i \<ge> k - j" by auto
  }
  then show ?thesis using derivation_ge_def by auto
qed      

lemma Derives1_bound': "Derives1 a i r b \<Longrightarrow> i \<le> length b"
  by (metis Derives1_bound Derives1_take append_Nil2 append_take_drop_id drop_eq_Nil 
    dual_order.strict_implies_order length_take min.absorb2 nat_le_linear) 

lemma LeftDerivation_Derives1_last:
  assumes "LeftDerivation a D b"
  assumes "D \<noteq> []"
  shows "Derives1 (Derive a (take (length D - 1) D)) (fst (last D)) (snd (last D)) b"
by (metis Derive LeftDerivation_Derive_take_LeftDerives1 LeftDerivation_implies_Derivation 
  LeftDerives1_implies_Derives1 assms(1) assms(2) last_conv_nth le_refl length_0_conv take_all)

lemma last_of_prefix_in_set:
  assumes "n < length E"
  assumes "D = E@F"
  shows "last E \<in> set (drop n D)"
proof -
  have f1: "last (drop n E) = last E"
    by (simp add: assms(1))
  have "drop n E \<noteq> []"
    by (metis (no_types) Cons_nth_drop_Suc assms(1) list.simps(3))
  then show ?thesis
    using f1 by (metis (no_types) append.simps(2) append_butlast_last_id append_eq_conv_conj assms(2) drop_append in_set_dropD insertCI list.set(2))
qed

lemma LeftDerivationFix_cut_appendix:
  assumes ldfix: "LeftDerivationFix (\<alpha>@\<delta>) i D j (\<beta>@\<delta>')"
  assumes \<alpha>_\<beta>: "LeftDerivation \<alpha> (take n D) \<beta>"
  assumes n_bound: "n \<le> length D"
  assumes dge: "derivation_ge (drop n D) (length \<beta>)"
  assumes i_in: "i < length \<alpha>"
  assumes j_in: "j < length \<beta>"
  shows "LeftDerivationFix \<alpha> i (take n D) j \<beta>"
proof - 
  from LeftDerivationFix_def[where \<alpha>="\<alpha>@\<delta>" and i=i and D=D and j=j and \<beta>="\<beta>@\<delta>'"] 
  obtain E F where EF:
    "is_sentence (\<alpha> @ \<delta>) \<and>
     is_sentence (\<beta> @ \<delta>') \<and>
     LeftDerivation (\<alpha> @ \<delta>) D (\<beta> @ \<delta>') \<and>
     i < length (\<alpha> @ \<delta>) \<and>
     j < length (\<beta> @ \<delta>') \<and>
     (\<alpha> @ \<delta>) ! i = (\<beta> @ \<delta>') ! j \<and>
     D = E @ derivation_shift F 0 (Suc j) \<and>
        LeftDerivation (take i (\<alpha> @ \<delta>)) E (take j (\<beta> @ \<delta>')) \<and>
        LeftDerivation (drop (Suc i) (\<alpha> @ \<delta>)) F (drop (Suc j) (\<beta> @ \<delta>'))" using ldfix by auto
  with i_in j_in have take_i_E_take_j: "LeftDerivation (take i \<alpha>) E (take j \<beta>)"
    by (simp add: less_or_eq_imp_le)  
  obtain m where m: "m = length E" by blast
  {
    assume n_less_m: "n < m"
    then have E_nonempty: "E \<noteq> []" using gr_implies_not0 list.size(3) m by auto 
    have last_E_in_set: "last E \<in> set (drop n D)" 
      using last_of_prefix_in_set n_less_m m EF by blast 
    obtain k r where kr: "(k, r) = last E" by (metis old.prod.exhaust)
    have k_lower_bound: "k \<ge> length \<beta>" using dge last_E_in_set kr
      by (metis derivation_ge_def fst_conv) 
    have "\<exists> \<alpha>'. Derives1 \<alpha>' k r (take j \<beta>)"  using LeftDerivation_Derives1_last take_i_E_take_j
      by (metis E_nonempty kr fst_conv snd_conv)
    then have "k \<le> j" by (metis Derives1_bound' j_in length_take less_imp_le_nat min.absorb2)   
    then have k_upper_bound: "k < length \<beta>" using j_in by arith
    from k_lower_bound k_upper_bound have "False" by arith
  }
  then have m_le_n: "m \<le> n" by arith
  have take_i_E_take_j: "LeftDerivation (take i \<alpha>) E (take j \<beta>)"
    by (simp add: take_i_E_take_j)
  have "take n D = E @ (take (n - m) (derivation_shift F 0 (Suc j)))"
    using EF m m_le_n by auto
  then have take_n_D: "take n D = E @ (derivation_shift (take (n - m) F) 0 (Suc j))"
    using take_derivation_shift by auto
  obtain F' where F': "F' = derivation_shift (take (n - m) F) 0 (Suc j)" by blast 
  have "LeftDerivation ((take i \<alpha>)@(drop i \<alpha>)) E ((take j \<beta>)@(drop i \<alpha>))" 
    using take_i_E_take_j
    by (metis EF LeftDerivation_append_suffix append_take_drop_id is_sentence_concat)     
  then have "LeftDerivation \<alpha> E ((take j \<beta>)@(drop i \<alpha>))" by simp
  with take_n_D have take_j_drop_i: "LeftDerivation ((take j \<beta>)@(drop i \<alpha>)) F' \<beta>" using F'  
    by (metis Derivation_unique_dest LeftDerivation_append LeftDerivation_implies_Derivation \<alpha>_\<beta>)
  have F'_ge: "derivation_ge F' (Suc j)" using F' derivation_ge_shift by blast 
  have drop_append: "drop i \<alpha> = [\<alpha>!i] @ (drop (Suc i) \<alpha>)" by (simp add: Cons_nth_drop_Suc i_in)
  have take_append: "take j \<beta> @ [\<alpha>!i] = take (Suc j) \<beta>"
    by (metis LeftDerivationFix_def i_in j_in ldfix nth_superfluous_append take_Suc_conv_app_nth)
  have take_drop_Suc: "(take j \<beta>)@(drop i \<alpha>) = (take (Suc j) \<beta>)@(drop (Suc i) \<alpha>)"
    by (simp add: drop_append take_append)
  with take_drop_Suc take_j_drop_i have "LeftDerivation ((take (Suc j) \<beta>)@(drop (Suc i) \<alpha>)) F' \<beta>"
    by auto
  note helper = LeftDerivation_skip_prefix[OF this]
  have len_take: "length (take (Suc j) \<beta>) = Suc j" by (simp add: Suc_leI j_in min.absorb2)    
  have F'_shift: "derivation_shift F' (Suc j) 0 = take (n - m) F"
    using F' derivation_shift_right_left_cancel by blast  
  have LeftDerivation_drop: "LeftDerivation (drop (Suc i) \<alpha>) (take (n - m) F) (drop (Suc j) \<beta>)"  
    using helper len_take F'_shift F'_ge by auto   
  show ?thesis
    apply (auto simp add: LeftDerivationFix_def)
    using LeftDerivationFix_is_sentence is_sentence_concat ldfix apply blast
    using LeftDerivationFix_is_sentence is_sentence_concat ldfix apply blast
    using \<alpha>_\<beta> apply blast
    using i_in apply blast
    using j_in apply blast
    using LeftDerivationFix_def i_in j_in ldfix apply auto[1]
    apply (rule_tac x=E in exI)
    apply (rule_tac x="take (n - m) F" in exI)
    apply auto
    using take_n_D apply blast
    using take_i_E_take_j apply blast
    using LeftDerivation_drop by blast
qed

lemma LeftDerivationFix_cut_appendix':
  assumes ldfix: "LeftDerivationFix (\<alpha>@\<delta>) i D j (\<beta>@\<delta>')"
  assumes \<alpha>_\<beta>: "LeftDerivation \<alpha> D \<beta>"
  assumes i_in: "i < length \<alpha>"
  assumes j_in: "j < length \<beta>"
  shows "LeftDerivationFix \<alpha> i D j \<beta>"
proof -
  obtain n where n: "n = length D" by blast
  have "LeftDerivationFix \<alpha> i (take n D) j \<beta>"
    apply (rule_tac LeftDerivationFix_cut_appendix)
    apply (rule ldfix)
    using \<alpha>_\<beta> n apply auto[1]
    using n apply auto[1]
    using n apply auto[1]
    using i_in apply blast
    using j_in apply blast
    done
  then show ?thesis using n by auto
qed

lemma LeftDerivationIntro_cut_appendix:
  assumes ldfix: "LeftDerivationIntro (\<alpha>@\<delta>) i r ix D j (\<beta>@\<delta>')"
  assumes \<alpha>_\<beta>: "LeftDerivation \<alpha> ((i,r)#(take n D)) \<beta>"
  assumes n_bound: "n \<le> length D"
  assumes dge: "derivation_ge (drop n D) (length \<beta>)"
  assumes i_in: "i < length \<alpha>"
  assumes j_in: "j < length \<beta>"
  shows "LeftDerivationIntro \<alpha> i r ix (take n D) j \<beta>"
proof -
  from LeftDerivationIntro_def[where \<alpha>="\<alpha>@\<delta>" and i=i and r=r and ix=ix and D=D and j=j and \<gamma>="\<beta>@\<delta>'"]
  obtain \<omega> where \<omega>: "LeftDerives1 (\<alpha> @ \<delta>) i r \<omega> \<and>
      ix < length (snd r) \<and> snd r ! ix = (\<beta> @ \<delta>') ! j \<and> LeftDerivationFix \<omega> (i + ix) D j (\<beta> @ \<delta>')"
      using ldfix by blast
  then have "\<exists> \<alpha>'. \<omega> = \<alpha>' @ \<delta> \<and> i + length (snd r) \<le> length \<alpha>'" 
    using i_in using LeftDerives1_append_replace_in_left by blast 
  then obtain \<alpha>' where \<alpha>': "\<omega> = \<alpha>' @ \<delta> \<and> i + length (snd r) \<le> length \<alpha>'" by blast
  have \<alpha>_\<alpha>': "LeftDerives1 \<alpha> i r \<alpha>'" using \<alpha>' \<omega> using LeftDerives1_skip_suffix i_in by blast 
  from \<alpha>_\<beta> obtain u where u: "LeftDerives1 \<alpha> i r u \<and> LeftDerivation u (take n D) \<beta>" by auto
  with \<alpha>_\<alpha>' have "u = \<alpha>'" using Derives1_unique_dest LeftDerives1_implies_Derives1 by blast
  with u have \<alpha>'_\<beta>: "LeftDerivation \<alpha>' (take n D) \<beta>" by auto
  have ldfix_append: "LeftDerivationFix (\<alpha>' @ \<delta>) (i + ix) D j (\<beta> @ \<delta>')" using \<alpha>' \<omega> by blast
  have i_plus_ix_bound: "i + ix < length \<alpha>'" using \<omega> \<alpha>'
    using add_lessD1 le_add_diff_inverse less_asym' linorder_neqE_nat nat_add_left_cancel_less 
    by linarith 
  from LeftDerivationFix_cut_appendix[OF ldfix_append \<alpha>'_\<beta> n_bound dge i_plus_ix_bound j_in]  
  have ldfix: "LeftDerivationFix \<alpha>' (i + ix) (take n D) j \<beta>" .
  show ?thesis
    apply (simp add: LeftDerivationIntro_def)
    apply (rule_tac x="\<alpha>'" in exI)
    apply auto
    using \<alpha>_\<alpha>' apply blast
    using \<omega> apply blast
    apply (simp add: \<omega> j_in)
    using ldfix by blast
qed

lemma LeftDerivationIntro_cut_appendix':
  assumes ldfix: "LeftDerivationIntro (\<alpha>@\<delta>) i r ix D j (\<beta>@\<delta>')"
  assumes \<alpha>_\<beta>: "LeftDerivation \<alpha> ((i,r)#D) \<beta>"
  assumes i_in: "i < length \<alpha>"
  assumes j_in: "j < length \<beta>"
  shows "LeftDerivationIntro \<alpha> i r ix D j \<beta>"
proof -
  obtain n where n: "n = length D" by blast
  have "LeftDerivationIntro \<alpha> i r ix (take n D) j \<beta>"
    apply (rule_tac LeftDerivationIntro_cut_appendix)
    apply (rule ldfix)
    using \<alpha>_\<beta> n apply auto[1]
    using n apply auto[1]
    using n apply auto[1]
    using i_in apply blast
    using j_in apply blast
    done
  then show ?thesis using n by auto
qed

lemma ladder_n_monotone: "is_ladder D L \<Longrightarrow> u \<le> v \<Longrightarrow> v < length L \<Longrightarrow> ladder_n L u \<le> ladder_n L v"
by (metis is_ladder_def le_neq_implies_less linear not_less)
    
lemma ladder_i_cut: 
  assumes index_bound: "index < length L"
  shows "ladder_i (ladder_cut L n) index = ladder_i L index"
proof -
  have "index = 0 \<or> index > 0" by arith
  then show ?thesis
  proof (induct rule: disjCases2)
    case 1 
      with index_bound have "L \<noteq> []" by (simp add: less_numeral_extra(3))
      then show ?case using 1 by (simp add: ladder_i_of_cut_at_0) 
  next
    case 2      
      then show ?case
        apply (auto simp add: ladder_i_def ladder_cut_def ladder_j_def deriv_j_def Let_def)
        using index_bound by auto
  qed
qed

lemma ladder_j_cut: 
  assumes index_bound: "index < length L"
  shows "ladder_j (ladder_cut L n) index = ladder_j L index"
by (metis gr_implies_not0 index_bound ladder_cut_def ladder_j_def ladder_last_j_def 
  ladder_last_j_of_cut length_ladder_cut list.size(3) nth_list_update_neq)

lemma ladder_ix_cut: 
  assumes index_lower_bound: "index > 0"
  assumes index_upper_bound: "index < length L"
  shows "ladder_ix (ladder_cut L n) index = ladder_ix L index"
proof -
  show ?thesis
    using index_lower_bound apply (simp add: ladder_ix_def deriv_ix_def)
    by (metis index_upper_bound ladder_cut_def nth_list_update_eq nth_list_update_neq snd_conv)
qed    

lemma LeftDerivation_from_in_between:
  assumes \<alpha>_\<beta>: "LeftDerivation \<alpha> (take u D) \<beta>"
  assumes \<alpha>_\<gamma>: "LeftDerivation \<alpha> (take v D) \<gamma>"
  assumes u_le_v: "u \<le> v"
  shows "LeftDerivation \<beta> (drop u (take v D)) \<gamma>"
proof -
  have take_split: "take v D = take u D @ (drop u (take v D))"
    by (metis u_le_v add_diff_cancel_left' drop_take le_Suc_ex take_add) 
  then show ?thesis using \<alpha>_\<gamma> \<alpha>_\<beta>
    by (metis (no_types, lifting) Derivation_unique_dest LeftDerivation_append 
      LeftDerivation_implies_Derivation) 
qed

lemma LeftDerivationLadder_cut_appendix_helper: 
  assumes LDLadder: "LeftDerivationLadder (\<alpha>@\<delta>) D L \<gamma>"
  assumes ladder_i_in_\<alpha>: "ladder_i L 0 < length \<alpha>"
  shows "\<exists> E F \<gamma>1 \<gamma>2 L'. D = E@F \<and> 
    \<gamma> = \<gamma>1 @ \<gamma>2 \<and> 
    LeftDerivationLadder \<alpha> E L' \<gamma>1 \<and> 
    derivation_ge F (length \<gamma>1) \<and>
    LeftDerivation \<delta> (derivation_shift F (length \<gamma>1) 0) \<gamma>2 \<and>
    L' = ladder_cut L (length E)" 
proof -
  have is_ladder_D_L: "is_ladder D L" using LDLadder LeftDerivationLadder_def by blast 
  obtain n where n: "n = ladder_last_n L" by blast
  then have n_eq_ladder_n: "n = ladder_n L (length L - 1)" using ladder_last_n_def by blast 
  have length_L_nonzero: "length L > 0"
    using LeftDerivationLadder_def assms(1) is_ladder_def by blast 
  from LeftDerivationLadder_propagate[OF LDLadder ladder_i_in_\<alpha> n_eq_ladder_n]
  obtain n' \<beta> \<delta>' where finish:
    "(length L - 1 = 0 \<or> ladder_prev_n L (length L - 1) < n') \<and>
     n' \<le> n \<and>
     LeftDerivation \<alpha> (take n' D) \<beta> \<and>
     LeftDerivation (\<alpha> @ \<delta>) (take n' D) (\<beta> @ \<delta>) \<and>
     derivation_ge (drop n' D) (length \<beta>) \<and>
     LeftDerivation \<delta> (derivation_shift (drop n' D) (length \<beta>) 0) \<delta>' \<and>
     ladder_\<gamma> (\<alpha> @ \<delta>) D L (length L - 1) = \<beta> @ \<delta>' \<and> ladder_j L (length L - 1) < length \<beta>"
     using length_L_nonzero by auto
  obtain E where E: "E = take n' D" by blast
  obtain F where F: "F = drop n' D" by blast
  obtain L' where L': "L' = ladder_cut L (length E)" by blast
  have \<gamma>_ladder: "\<gamma> = ladder_\<gamma> (\<alpha> @ \<delta>) D L (length L - 1)"
    by (metis Derive LDLadder LeftDerivationLadder_def LeftDerivation_implies_Derivation 
      append_Nil2 append_take_drop_id drop_eq_Nil is_ladder_def ladder_\<gamma>_def le_refl n 
      n_eq_ladder_n) 
  then have \<gamma>: "\<gamma> = \<beta> @ \<delta>'" using finish by auto
  have "is_sentence (\<alpha>@\<delta>)"
    using LDLadder LeftDerivationFix_is_sentence LeftDerivationLadder_def by blast
  then have is_sentence_\<alpha>: "is_sentence \<alpha>" using is_sentence_concat by blast 
  have "is_sentence \<gamma>"
    using Derivation_implies_derives LDLadder LeftDerivationFix_is_sentence 
      LeftDerivationLadder_def LeftDerivation_implies_Derivation derives_is_sentence by blast
  then have is_sentence_\<beta>: "is_sentence \<beta>" using \<gamma> is_sentence_concat by blast 
  have length_L': "length L' = length L"
    by (metis L' ladder_cut_def length_list_update)
  have ladder_last_n_L': "ladder_last_n L' = length E"
    using L' ladder_last_n_of_cut length_L_nonzero by blast
  have length_D_eq_n: "length D = n"
    using LDLadder LeftDerivationLadder_def is_ladder_def n by auto     
  then have length_E_eq_n': "length E = n'" by (simp add: E finish min.absorb2) 
  {
    fix u :: nat
    assume "u < length L'"
    then have "u < length L' - 1 \<or> u = length L' - 1" by arith
    then have "ladder_n L' u \<le> length E"
    proof (induct rule: disjCases2) 
      case 1
        have u_bound: "u < length L - 1" using 1 by (simp add: length_L')
        then have L'_eq_L: "ladder_n L' u = ladder_n L u" using L' ladder_n_of_cut 
          length_L_nonzero length_greater_0_conv by blast 
        from u_bound have "ladder_n L u \<le> ladder_prev_n L (length L - 1)" 
          using ladder_n_prev_bound LeftDerivationLadder_def assms(1) by blast    
        then show ?case
          using L'_eq_L finish length_E_eq_n' u_bound by linarith 
    next
      case 2
        then have "ladder_n L' u = length E" using ladder_last_n_L' ladder_last_n_def by auto
        then show ?case by auto
    qed
  }
  note ladder_n_bound = this
  {
    fix u :: nat
    fix v :: nat
    assume u_less_v: "u < v"
    assume v_bound: "v < length L'"
    have "v < length L' - 1 \<or> v = length L' - 1" using v_bound by arith
    then have "ladder_n L' u < ladder_n L' v"
    proof (induct rule: disjCases2)
      case 1
        show ?case
          using "1.hyps" L' LeftDerivationLadder_def assms(1) is_ladder_def ladder_n_of_cut 
            length_L' u_less_v by auto
    next
      case 2
        note v_def = 2
        have "v = 0 \<or> v \<noteq> 0" by arith
        then show ?case
        proof (induct rule: disjCases2)
          case 1
          then show ?case using u_less_v by auto
        next
          case 2
          then have "ladder_prev_n L (length L - 1) < n'" using finish v_def length_L' 
            by linarith 
          then show ?case
            by (metis (no_types, lifting) L' LeftDerivationLadder_def assms(1) 
              ladder_last_n_L' ladder_last_n_def ladder_n_of_cut ladder_n_prev_bound 
              le_neq_implies_less length_E_eq_n' length_L' length_greater_0_conv 
              less_trans u_less_v v_def) 
        qed
    qed
  }
  note ladder_n_pairwise_bound = this

  have is_ladder_E_L': "is_ladder E L'"
    apply (auto simp add: is_ladder_def ladder_last_n_L')
    using length_L_nonzero length_L' apply simp
    using ladder_n_bound apply blast
    using ladder_n_pairwise_bound by blast

  {
    fix index :: nat
    assume index_bound: "index + 1 < length L"
    then have index_le: "index < length L" by arith
    from index_bound have len_L_minus_1: "length L - 1 \<noteq> 0" by arith
    obtain m where m: "m = ladder_n L index" by blast
    from LeftDerivationLadder_propagate[OF LDLadder ladder_i_in_\<alpha> m index_le] obtain \<omega> where
      \<omega>: "LeftDerivation \<alpha> (take m D) \<omega> \<and> ladder_\<gamma> (\<alpha> @ \<delta>) D L index = \<omega> @ \<delta> \<and> 
      ladder_j L index < length \<omega>" using index_bound by auto
    have L'_Derive: "ladder_\<gamma> \<alpha> E L' index = Derive \<alpha> (take (ladder_n L' index) E)"
      by (simp add: ladder_\<gamma>_def)
    have ladder_n_L'_eq_L: "ladder_n L' index = ladder_n L index"
      using L' index_bound ladder_n_of_cut length_L_nonzero by auto
    have "ladder_prev_n L (length L - 1) < n'" using finish len_L_minus_1 by blast 
    then have n'_is_upper_bound: "ladder_n L (length L - 2) < n'" using index_bound
      by (metis diff_diff_left ladder_prev_n_def len_L_minus_1 one_add_one)  
    have index_upper_bound: "index \<le> length L - 2" using index_bound by linarith  
    have ladder_n_upper_bound: "ladder_n L index \<le> ladder_n L (length L - 2)"
      apply (rule_tac ladder_n_monotone)
      apply (rule_tac is_ladder_D_L)
      apply (rule index_upper_bound)
      using length_L_nonzero by linarith
    with n'_is_upper_bound have m_le_n': "m \<le> n'"
      using dual_order.strict_implies_order le_less_trans m by linarith
    then have "take m E = take m D"
      by (metis E le_take_same length_E_eq_n' order_refl take_all)
    then have take_helper: "(take (ladder_n L' index) E) = take m D"
      by (simp add: ladder_n_L'_eq_L m)
    then have Derive_eq_\<omega>: "Derive \<alpha> (take (ladder_n L' index) E) = \<omega>"
      by (simp add: Derive LeftDerivation_implies_Derivation \<omega>)
    then have t1: "ladder_\<gamma> (\<alpha>@\<delta>) D L index = (ladder_\<gamma> \<alpha> E L' index) @ \<delta>"
      by (simp add: L'_Derive \<omega>)
    have \<omega>_eq: "\<omega> = ladder_\<gamma> \<alpha> E L' index" by (simp add: Derive_eq_\<omega> L'_Derive) 
    then have t2: "LeftDerivation \<alpha> (take (ladder_n L index) D) (ladder_\<gamma> \<alpha> E L' index)"
      using \<omega> m by blast 
    have t3: "(take (ladder_n L' index) E) = take (ladder_n L index) D"
      by (simp add: m take_helper)     
    have t4: "ladder_j L index < length (ladder_\<gamma> \<alpha> E L' index)"
      using \<omega> \<omega>_eq by blast     
    have t5: "E ! (ladder_n L' index) = D ! (ladder_n L index)"
      using E ladder_n_L'_eq_L ladder_n_upper_bound n'_is_upper_bound by auto
    note t = t1 t2 t3 t4 t5
  }  
  note ladder_early_stage = this

  {
    fix index :: nat
    assume index_bound: "index < length L"
    have i: "ladder_i L' index = ladder_i L index"
      using L' ladder_i_cut by (simp add: index_bound) 
    have j: "ladder_j L' index = ladder_j L index"
      using L' ladder_j_cut by (simp add: index_bound)
    have ix: "index > 0 \<Longrightarrow> ladder_ix L' index = ladder_ix L index"
      using L' ladder_ix_cut by (simp add: index_bound)
    have \<alpha>: "ladder_\<alpha> (\<alpha>@\<delta>) D L index = (ladder_\<alpha> \<alpha> E L' index) @ \<delta>"
      by (simp add: index_bound ladder_\<alpha>_def ladder_early_stage(1))
    have i_bound: "index > 0 \<Longrightarrow> ladder_i L' index < length (ladder_\<alpha> \<alpha> E L' index)"
      using i index_bound ladder_\<alpha>_def ladder_early_stage(4) ladder_i_def by auto     
    note ij = i j ix \<alpha> i_bound
  }
  note ladder_every_stage = this

  {
    fix u :: nat
    fix v :: nat
    assume u_le_v: "u \<le> v"
    assume v_bound: "v < length L"
    have "ladder_n L u \<le> ladder_n L v"
      using is_ladder_D_L ladder_n_monotone u_le_v v_bound by blast
  }       
  note ladder_L_n_pairwise_le = this

  {
    fix index :: nat
    assume index_lower_bound: "index > 0"
    assume index_upper_bound: "index + 1 < length L"
    note derivation = ladder_early_stage(2)
    have derivation1: 
      "LeftDerivation \<alpha> (take (ladder_n L (index - Suc 0)) D) (ladder_\<gamma> \<alpha> E L' (index - Suc 0))"
      using derivation[of "index - Suc 0"] index_lower_bound index_upper_bound
      using One_nat_def Suc_diff_1 Suc_eq_plus1 le_less_trans lessI less_or_eq_imp_le by linarith
    have derivation2:
      "LeftDerivation \<alpha> (take (ladder_n L index) D) (ladder_\<gamma> \<alpha> E L' index)"
      using derivation[of index] index_upper_bound by blast
    have ladder_\<alpha>_is_\<gamma>[symmetric]: "ladder_\<gamma> \<alpha> E L' (index - Suc 0) = ladder_\<alpha> \<alpha> E L' index"
      using index_lower_bound ladder_\<alpha>_def by auto
    have ladder_n_le: "ladder_n L (index - Suc 0) \<le> ladder_n L index"
      apply (rule_tac ladder_L_n_pairwise_le)
      apply arith
      using index_upper_bound by arith 
    from LeftDerivation_from_in_between[OF derivation1 derivation2 ladder_n_le] ladder_\<alpha>_is_\<gamma>
    have "LeftDerivation (ladder_\<alpha> \<alpha> E L' index) (drop (ladder_n L' (index - Suc 0)) 
      (take (ladder_n L' index) E)) (ladder_\<gamma> \<alpha> E L' index)"
      by (metis L' Suc_leI add_lessD1 index_lower_bound index_upper_bound ladder_early_stage(3) 
        ladder_n_of_cut le_add_diff_inverse2 length_L_nonzero length_greater_0_conv less_diff_conv)          
  }
  note LeftDerivation_delta_early = this 
   
  have LeftDerivationFix_\<alpha>_0: "LeftDerivationFix \<alpha> (ladder_i L' 0) (take (ladder_n L' 0) E) 
    (ladder_j L' 0) (ladder_\<gamma> \<alpha> E L' 0)"
  proof -
    have ldfix: "LeftDerivationFix (\<alpha>@\<delta>) (ladder_i L 0) (take (ladder_n L 0) D) (ladder_j L 0) 
      (ladder_\<gamma> (\<alpha>@\<delta>) D L 0)"
      using LDLadder LeftDerivationLadder_def by blast
    have ladder_i_L': "ladder_i L' 0 = ladder_i L 0"
      using L' ladder_i_of_cut_at_0 length_L_nonzero by blast
    have ladder_j_L': "ladder_j L' 0 = ladder_j L 0"
      by (metis L' ladder_cut_def ladder_j_def ladder_last_j_def ladder_last_j_of_cut 
         length_L' length_greater_0_conv nth_list_update_neq)
    have "length L = 1 \<or> length L > 1" using length_L_nonzero by linarith 
    then show ?thesis
    proof (induct rule: disjCases2)
      case 1
        from 1 have ladder_n_L'_0: "ladder_n L' 0 = n'"
          using diff_is_0_eq' ladder_last_n_L' ladder_last_n_def length_E_eq_n' 
            length_L' less_or_eq_imp_le by auto 
        have take_n'_E: "take n' E = E" by (simp add: length_E_eq_n') 
        from ladder_n_L'_0 take_n'_E have take_ladder_n_L': "take (ladder_n L' 0) E = E" by auto
        have "ladder_n L 0 = length D"
          by (simp add: "1.hyps" length_D_eq_n n_eq_ladder_n) 
        then have take_ladder_n_L_0: "take (ladder_n L 0) D = D" by simp 
        have ladder_\<gamma>_\<alpha>: "ladder_\<gamma> \<alpha> E L' 0 = \<beta>"
          apply (simp add: ladder_\<gamma>_def take_ladder_n_L')
          by (simp add: Derive E LeftDerivation_implies_Derivation finish)
        have ladder_j_in_\<beta>: "ladder_j L 0 < length \<beta>" 
          using finish "1.hyps" by auto 
        have ldfix_1: "LeftDerivationFix (\<alpha>@\<delta>) (ladder_i L 0) D (ladder_j L 0) (\<beta>@\<delta>')"
          using "1.hyps" \<gamma> \<gamma>_ladder ldfix take_ladder_n_L_0 by auto
        then have "LeftDerivationFix \<alpha> (ladder_i L 0) E (ladder_j L 0) \<beta>"
          by (simp add: E LeftDerivationFix_cut_appendix finish ladder_i_in_\<alpha> ladder_j_in_\<beta> 
            length_D_eq_n)
        then show ?case
          by (simp add: ladder_i_L' ladder_j_L' take_ladder_n_L' ladder_\<gamma>_\<alpha>)
    next
      case 2
        have h: "0 + 1 < length L" using "2.hyps" by auto 
        note stage = ladder_early_stage[of 0, OF h]
        have ldfix0: "LeftDerivationFix (\<alpha>@\<delta>) (ladder_i L 0) (take (ladder_n L 0) D) (ladder_j L 0) 
          ((ladder_\<gamma> \<alpha> E L' 0) @ \<delta>)"
          using ladder_i_L' ladder_j_L' ldfix stage(1) stage(3) by auto
        from LeftDerivationFix_cut_appendix'[OF ldfix0 stage(2) ladder_i_in_\<alpha> stage(4)]
        show ?case
          by (simp add: ladder_i_L' ladder_j_L' stage(3))
    qed
  qed

  {
    fix index :: nat
    assume index_bounds: "1 \<le> index \<and> index + 1 < length L"
    have introsAt_appendix: "LeftDerivationIntrosAt (\<alpha>@\<delta>) D L index"
      using LDLadder LeftDerivationIntros_def LeftDerivationLadder_def add_lessD1 index_bounds 
      by blast
    have index_plus_1_upper_bound: "index + 1 < length L" using index_bounds by arith
    note early_stage = ladder_early_stage[of index, OF index_plus_1_upper_bound]
    have ladder_i_L_index_eq_fst: "ladder_i L index = fst (D ! ladder_n L (index - Suc 0))"
      using introsAt_appendix LeftDerivationIntrosAt_def index_bounds by (metis One_nat_def) 
    have E_at_D_at: "(E ! ladder_n L' (index - Suc 0)) = (D ! ladder_n L (index - Suc 0))"
      using ladder_early_stage[of "index - Suc 0"]
      by (metis One_nat_def add_lessD1 index_bounds le_add_diff_inverse2) 
    then have ladder_i_L'_index_eq_fst: "ladder_i L' index = fst (E ! ladder_n L' (index - Suc 0))"
      using index_bounds ladder_i_L_index_eq_fst ladder_every_stage(1) le_add1 le_less_trans by auto
    have same_derivation: "(drop (Suc (ladder_n L' (index - Suc 0))) (take (ladder_n L' index) E)) =
     (drop (Suc (ladder_n L (index - Suc 0))) (take (ladder_n L index) D))"
     using L' early_stage(3) index_bounds ladder_n_of_cut length_L_nonzero by auto
    have deriv_split: "(drop (ladder_n L' (index - Suc 0)) (take (ladder_n L' index) E)) =
       ((ladder_i L' index, snd (E ! ladder_n L' (index - Suc 0))) #
      drop (Suc (ladder_n L' (index - Suc 0))) (take (ladder_n L' index) E))"
      by (metis Cons_nth_drop_Suc One_nat_def Suc_le_lessD add_lessD1 diff_Suc_less index_bounds 
        ladder_i_L'_index_eq_fst ladder_n_bound ladder_n_pairwise_bound length_L' 
        length_take min.absorb2 nth_take prod.collapse)       
    have "LeftDerivationIntrosAt \<alpha> E L' index"
      apply (auto simp add: LeftDerivationIntrosAt_def Let_def)
      using ladder_i_L'_index_eq_fst apply blast
      apply (rule_tac LeftDerivationIntro_cut_appendix'[where \<delta>=\<delta> and \<delta>' = \<delta>])
      apply (metis E_at_D_at LeftDerivationIntrosAt_def One_nat_def Suc_le_lessD add_lessD1 
        early_stage(1) index_bounds introsAt_appendix ladder_every_stage(2) 
        ladder_every_stage(3) ladder_every_stage(4) ladder_i_L'_index_eq_fst same_derivation)
      defer 1
      using index_bounds ladder_every_stage(5) apply auto[1]
      using early_stage(4) index_bounds ladder_every_stage(2) apply auto[1]
      using LeftDerivation_delta_early deriv_split
      by (metis One_nat_def Suc_le_eq index_bounds) 
  }
  note LeftDerivationIntrosAt_early = this

  {
    fix index :: nat
    assume index_bounds: "1 \<le> index \<and> index + 1 = length L"
    have introsAt_appendix: "LeftDerivationIntrosAt (\<alpha>@\<delta>) D L index"
      using LDLadder LeftDerivationIntros_def LeftDerivationLadder_def add_lessD1 index_bounds
      by (metis Suc_eq_plus1 not_less_eq)      
    have ladder_i_L_index_eq_fst: "ladder_i L index = fst (D ! ladder_n L (index - Suc 0))"
      using introsAt_appendix LeftDerivationIntrosAt_def index_bounds by (metis One_nat_def) 
    have E_at_D_at: "(E ! ladder_n L' (index - Suc 0)) = (D ! ladder_n L (index - Suc 0))"
      using ladder_early_stage[of "index - Suc 0"]
      by (metis One_nat_def Suc_eq_plus1 index_bounds le_add_diff_inverse2 lessI)
    then have ladder_i_L'_index_eq_fst: "ladder_i L' index = fst (E ! ladder_n L' (index - Suc 0))"
      using index_bounds ladder_i_L_index_eq_fst ladder_every_stage(1) le_add1 le_less_trans by auto      
    obtain D' where D': "D' = (drop (Suc (ladder_n L (index - Suc 0))) (take (ladder_n L index) D))"
      by blast
    obtain k where k: "k = (ladder_n L' index) - (Suc (ladder_n L' (index - Suc 0)))"
      by blast
    have ladder_n_L'_index: "ladder_n L' index = length E"
      by (metis diff_add_inverse2 index_bounds ladder_last_n_L' ladder_last_n_def length_L')
    have take_is_E: "take (ladder_n L' index) E = E" by (simp add: ladder_n_L'_index)
    have ladder_n_L_index: "ladder_n L index = length D"
      by (metis diff_add_inverse2 index_bounds length_D_eq_n n_eq_ladder_n)
    have take_is_D: "take (ladder_n L index) D = D"
      by (simp add: ladder_n_L_index)
    have write_as_take_k_D': "(drop (Suc (ladder_n L' (index - Suc 0))) E) = take k D'"
      using take_is_D
      by (metis D' E L' One_nat_def Suc_le_lessD add_diff_cancel_right' diff_Suc_less 
        drop_take index_bounds k ladder_n_L'_index ladder_n_of_cut length_E_eq_n' 
        length_L_nonzero length_greater_0_conv)   
    have k_bound: "k \<le> length D'"
      by (metis le_iff_add append_take_drop_id k ladder_n_L'_index length_append 
        length_drop write_as_take_k_D')
    have D'_alt: "D' = drop (Suc (ladder_n L (index - Suc 0))) D"
      by (simp add: D' take_is_D)
    have "LeftDerivationIntrosAt \<alpha> E L' index"
      apply (auto simp add: LeftDerivationIntrosAt_def Let_def)
      using ladder_i_L'_index_eq_fst apply blast
      apply (subst take_is_E)
      apply (subst write_as_take_k_D')
      apply (rule_tac LeftDerivationIntro_cut_appendix[where \<delta>=\<delta> and \<delta>' = \<delta>'])
      apply (metis D' Derive E E_at_D_at LeftDerivationIntrosAt_def 
        LeftDerivation_implies_Derivation One_nat_def Suc_le_lessD add_diff_cancel_right' 
        diff_Suc_less finish index_bounds introsAt_appendix ladder_\<gamma>_def ladder_every_stage(2) 
        ladder_every_stage(3) ladder_every_stage(4) ladder_i_L'_index_eq_fst length_L_nonzero 
        take_is_E)
      apply (metis Cons_nth_drop_Suc E L' LeftDerivation_from_in_between LeftDerivation_take_derive 
        One_nat_def Suc_le_lessD add_diff_cancel_right' diff_Suc_less finish index_bounds 
        ladder_\<alpha>_def ladder_\<gamma>_def ladder_i_L'_index_eq_fst ladder_n_L'_index ladder_n_of_cut 
        ladder_prev_n_def length_E_eq_n' length_L_nonzero less_imp_le_nat less_numeral_extra(3) 
        list.size(3) prod.collapse take_is_E write_as_take_k_D')
      using k_bound apply blast
      using D'_alt apply (metis (no_types, lifting) Derive E L' LeftDerivation_implies_Derivation 
        One_nat_def Suc_leI Suc_le_lessD add_diff_cancel_right' diff_Suc_less drop_drop finish 
        index_bounds k ladder_\<gamma>_def ladder_n_L'_index ladder_n_of_cut ladder_prev_n_def 
        le_add_diff_inverse2 length_E_eq_n' length_L_nonzero length_greater_0_conv 
        less_not_refl2 take_is_E) 
      using index_bounds ladder_every_stage(5) apply auto[1]
      by (metis Derive E LeftDerivation_implies_Derivation One_nat_def add_diff_cancel_right' 
        diff_Suc_less finish index_bounds ladder_\<gamma>_def ladder_every_stage(2) length_L_nonzero 
        take_is_E)
  }
  note LeftDerivationIntrosAt_last = this

  have ladder_E_L': "LeftDerivationLadder \<alpha> E L' \<beta>"
    apply (auto simp add: LeftDerivationLadder_def)
    using finish E apply blast
    using is_ladder_E_L' apply blast
    using LeftDerivationFix_\<alpha>_0 apply blast
    using LeftDerivationIntros_def LeftDerivationIntrosAt_early LeftDerivationIntrosAt_last
    by (metis Suc_eq_plus1 Suc_leI le_neq_implies_less length_L')
    
  show ?thesis
    apply (rule_tac x=E in exI)
    apply (rule_tac x=F in exI)
    apply (rule_tac x=\<beta> in exI)
    apply (rule_tac x=\<delta>' in exI)
    apply (rule_tac x=L' in exI)
    apply auto
    using E F apply simp
    apply (rule \<gamma>)
    using ladder_E_L' apply blast
    using F finish apply blast
    using F finish apply blast
    by (rule L')
qed  

theorem LeftDerivationLadder_cut_appendix: 
  assumes LDLadder: "LeftDerivationLadder (\<alpha>@\<delta>) D L \<gamma>"
  assumes ladder_i_in_\<alpha>: "ladder_i L 0 < length \<alpha>"
  shows "\<exists> E F \<gamma>1 \<gamma>2 L'. D = E@F \<and> 
    \<gamma> = \<gamma>1 @ \<gamma>2 \<and> 
    LeftDerivationLadder \<alpha> E L' \<gamma>1 \<and> 
    derivation_ge F (length \<gamma>1) \<and>
    LeftDerivation \<delta> (derivation_shift F (length \<gamma>1) 0) \<gamma>2 \<and>
    length L' = length L \<and> ladder_i L' 0 = ladder_i L 0 \<and>
    ladder_last_j L' = ladder_last_j L"
proof -
  from LeftDerivationLadder_cut_appendix_helper[OF LDLadder ladder_i_in_\<alpha>]
  obtain E F \<gamma>1 \<gamma>2 L' where helper:
    "D = E @ F \<and>
     \<gamma> = \<gamma>1 @ \<gamma>2 \<and>
     LeftDerivationLadder \<alpha> E L' \<gamma>1 \<and>
     derivation_ge F (length \<gamma>1) \<and>
     LeftDerivation \<delta> (derivation_shift F (length \<gamma>1) 0) \<gamma>2 \<and> L' = ladder_cut L (length E)"
     by blast
  show ?thesis
    apply (rule_tac x=E in exI)
    apply (rule_tac x=F in exI)
    apply (rule_tac x=\<gamma>1 in exI)
    apply (rule_tac x=\<gamma>2 in exI)
    apply (rule_tac x=L' in exI)
    using helper LDLadder LeftDerivationLadder_def is_ladder_def ladder_i_of_cut_at_0 
      ladder_last_j_of_cut length_ladder_cut by force 
qed

definition ladder_stepdown_diff :: "ladder \<Rightarrow> nat" where
  "ladder_stepdown_diff L = Suc (ladder_n L 0)"

definition ladder_stepdown_\<alpha>_0 :: "sentence \<Rightarrow> derivation \<Rightarrow> ladder \<Rightarrow> sentence" where
  "ladder_stepdown_\<alpha>_0 a D L = Derive a (take (ladder_stepdown_diff L) D)"

lemma LeftDerivationIntro_LeftDerives1:
  assumes "LeftDerivationIntro \<alpha> i r ix D j \<gamma>"
  assumes "splits_at \<alpha> i a1 A a2"
  shows "LeftDerives1 \<alpha> i r (a1@(snd r)@a2)"
by (metis LeftDerivationIntro_def LeftDerivationIntro_examine_rule LeftDerivationIntro_is_sentence 
  LeftDerives1_def assms(1) assms(2) prod.collapse splits_at_implies_Derives1)

lemma LeftDerives1_Derive:
  assumes "LeftDerives1 \<alpha> i r \<gamma>"
  shows "Derive \<alpha> [(i, r)] = \<gamma>"
by (metis Derive LeftDerivation.simps(1) LeftDerivation_LeftDerives1 
  LeftDerivation_implies_Derivation append_Nil assms)

lemma ladder_stepdown_\<alpha>_0_altdef:
  assumes ladder: "LeftDerivationLadder \<alpha> D L \<gamma>"
  assumes length_L: "length L > 1"
  assumes split: "splits_at (ladder_\<alpha> \<alpha> D L 1) (ladder_i L 1) a1 A a2"
  shows "ladder_stepdown_\<alpha>_0 \<alpha> D L = a1 @ (snd (snd (D ! (ladder_n L 0)))) @ a2"
proof -
  have 1: "ladder_\<alpha> \<alpha> D L 1 = Derive \<alpha> (take (ladder_n L 0) D)"
    by (simp add: ladder_\<alpha>_def ladder_\<gamma>_def)
  obtain rule  where rule: "rule = snd (D ! (ladder_n L 0))" by blast
  have "\<exists> E \<omega>. LeftDerivationIntro (ladder_\<alpha> \<alpha> D L 1) (ladder_i L 1) rule (ladder_ix L 1)
    E (ladder_j L 1) \<omega>"
    by (metis LeftDerivationIntrosAt_def LeftDerivationIntros_def LeftDerivationLadder_def 
      One_nat_def diff_Suc_1 ladder length_L order_refl rule)
  then obtain E \<omega> where intro: 
    "LeftDerivationIntro (ladder_\<alpha> \<alpha> D L 1) (ladder_i L 1) rule (ladder_ix L 1) E (ladder_j L 1) \<omega>"
    by blast
  then have 2: "LeftDerives1 (ladder_\<alpha> \<alpha> D L 1) (ladder_i L 1) rule (a1@(snd rule)@a2)"
    using LeftDerivationIntro_LeftDerives1 split by blast
  have fst_D: "fst (D ! (ladder_n L 0)) = ladder_i L 1"
    by (metis LeftDerivationIntrosAt_def LeftDerivationIntros_def LeftDerivationLadder_def 
      One_nat_def diff_Suc_1 ladder le_numeral_extra(4) length_L)
  have derive_derive: "Derive \<alpha> (take (Suc (ladder_n L 0)) D) = 
    Derive (Derive \<alpha> (take (ladder_n L 0) D)) [D ! (ladder_n L 0)]"
    proof -
      have f1: "Derivation \<alpha> (take (Suc (ladder_n L 0)) D) (Derive \<alpha> (take (Suc (ladder_n L 0)) D))"
        using Derivation_take_derive LeftDerivationLadder_def LeftDerivation_implies_Derivation ladder by blast
      have f2: "length L - 1 < length L"
        using length_L by linarith
      have "0 < length L - 1"
        using length_L by linarith
      then have f3: "take (Suc (ladder_n L 0)) D = take (ladder_n L 0) D @ [D ! ladder_n L 0]"
        using f2 by (metis (full_types) LeftDerivationLadder_def is_ladder_def ladder ladder_last_n_def take_Suc_conv_app_nth)
      obtain sss :: "symbol list \<Rightarrow> (nat \<times> symbol \<times> symbol list) list \<Rightarrow> (nat \<times> symbol \<times> symbol list) list \<Rightarrow> symbol list \<Rightarrow> symbol list" where
        "\<forall>x0 x1 x2 x3. (\<exists>v4. Derivation x3 x2 v4 \<and> Derivation v4 x1 x0) = (Derivation x3 x2 (sss x0 x1 x2 x3) \<and> Derivation (sss x0 x1 x2 x3) x1 x0)"
        by moura
      then show ?thesis
        using f3 f1 Derivation_append Derive by auto
    qed
  then have 3: "ladder_stepdown_\<alpha>_0 \<alpha> D L = Derive (ladder_\<alpha> \<alpha> D L 1) [D ! (ladder_n L 0)]"
    using 1 by (simp add: ladder_stepdown_\<alpha>_0_def ladder_stepdown_diff_def) 
  have 4: "D ! (ladder_n L 0) = (ladder_i L 1, rule)"
    using rule fst_D by (metis prod.collapse) 
  then show ?thesis using 2 3 4 LeftDerives1_Derive snd_conv by auto 
qed   

lemma ladder_i_0_bound:
  assumes ld: "LeftDerivationLadder \<alpha> D L \<gamma>"
  shows "ladder_i L 0 < length \<alpha>"
proof -
  have "LeftDerivationFix \<alpha> (ladder_i L 0) (take (ladder_n L 0) D) 
    (ladder_j L 0) (ladder_\<gamma> \<alpha> D L 0)"
    using ld LeftDerivationLadder_def by simp
  then show ?thesis using LeftDerivationFix_def by simp
qed

lemma ladder_j_bound:
  assumes ld: "LeftDerivationLadder \<alpha> D L \<gamma>"
  assumes index_bound: "index < length L"
  shows "ladder_j L index < length (ladder_\<gamma> \<alpha> D L index)"
proof -
  have ld': "LeftDerivationLadder (\<alpha>@[]) D L \<gamma>" using ld by simp
  have ladder_i_0: "ladder_i L 0 < length \<alpha>" using ladder_i_0_bound ld by auto
  obtain n where n: "n = ladder_n L index" by blast
  note propagate = LeftDerivationLadder_propagate[OF ld' ladder_i_0 n index_bound]
  from index_bound have "index + 1 < length L \<or> index + 1 = length L" by arith
  then show ?thesis
  proof (induct rule: disjCases2)
    case 1
      then have "\<exists>\<beta>. LeftDerivation \<alpha> (take n D) \<beta> \<and>
         ladder_\<gamma> (\<alpha> @ []) D L index = \<beta> @ [] \<and> ladder_j L index < length \<beta>"
         using propagate by auto
      then show ?case by auto
  next
    case 2
      then have "
        \<exists>n' \<beta> \<delta>'.
          (index = 0 \<or> ladder_prev_n L index < n') \<and>
          n' \<le> n \<and>
          LeftDerivation \<alpha> (take n' D) \<beta> \<and>
          LeftDerivation (\<alpha> @ []) (take n' D) (\<beta> @ []) \<and>
          derivation_ge (drop n' D) (length \<beta>) \<and>
          LeftDerivation [] (derivation_shift (drop n' D) (length \<beta>) 0) \<delta>' \<and>
          ladder_\<gamma> (\<alpha> @ []) D L index = \<beta> @ \<delta>' \<and> ladder_j L index < length \<beta>"
          using propagate by auto
      then show ?case by auto
  qed
qed
  
lemma ladder_last_j_bound:
  assumes ld: "LeftDerivationLadder \<alpha> D L \<gamma>"
  shows "ladder_last_j L < length \<gamma>"
proof -
  have "length L - 1 < length L"
    using LeftDerivationLadder_def assms is_ladder_def by auto 
  from ladder_j_bound[OF ld this]
  show ?thesis
    by (metis Derive LeftDerivationLadder_def LeftDerivation_implies_Derivation One_nat_def 
      is_ladder_def ladder_last_j_def last_ladder_\<gamma> ld) 
qed    

fun ladder_shift_n :: "nat \<Rightarrow> ladder \<Rightarrow> ladder" where 
  "ladder_shift_n N [] = []"
| "ladder_shift_n N ((n, j, i)#L) = ((n - N, j, i)#(ladder_shift_n N L))" 

fun ladder_stepdown :: "ladder \<Rightarrow> ladder"
where 
  "ladder_stepdown [] = undefined"
| "ladder_stepdown [v] = undefined"
| "ladder_stepdown ((n0, j0, i0)#(n1, j1, ix1)#L) = 
  (n1 - Suc n0, j1, j0 + ix1) # (ladder_shift_n (Suc n0) L)"
    
lemma ladder_shift_n_length: 
  "length (ladder_shift_n N L) = length L"
  by (induct L, auto)

lemma ladder_stepdown_prepare:
  assumes "length L > 1"
  shows "L = (ladder_n L 0, ladder_j L 0, ladder_i L 0)#
    (ladder_n L 1, ladder_j L 1, ladder_ix L 1)#(drop 2 L)"
proof -
  have "\<exists> n0 j0 i0 n1 j1 ix1 L'. L = ((n0, j0, i0)#(n1, j1, ix1)#L')"
    by (metis One_nat_def Suc_eq_plus1 assms ladder_stepdown.cases less_not_refl list.size(3) 
      list.size(4) not_less0)
  then obtain n0 j0 i0 n1 j1 ix1 L' where L': "L = ((n0, j0, i0)#(n1, j1, ix1)#L')" by blast
  have n0: "n0 = ladder_n L 0" using L'
    by (auto simp add: ladder_n_def deriv_n_def)
  show ?thesis using L'
    by (auto simp add: ladder_n_def deriv_n_def ladder_j_def deriv_j_def 
      ladder_i_def deriv_i_def ladder_ix_def deriv_ix_def)
qed

lemma ladder_stepdown_length:
  assumes "length L > 1"
  shows "length (ladder_stepdown L) = length L - 1"
apply (subst ladder_stepdown_prepare[OF assms(1)])
apply (simp add: ladder_shift_n_length)
using assms apply arith
done

lemma ladder_stepdown_i_0:
  assumes "length L > 1"
  shows "ladder_i (ladder_stepdown L) 0 = ladder_i L 1 + ladder_ix L 1"
  using ladder_stepdown_prepare[OF assms] ladder_i_def ladder_j_def deriv_j_def
  by (metis One_nat_def deriv_i_def diff_Suc_1 ladder_stepdown.simps(3) list.sel(1) 
    snd_conv zero_neq_one)

lemma ladder_shift_n_cons: "ladder_shift_n N (x#L) = (fst x - N, snd x)#(ladder_shift_n N L)"
  apply (induct L)
  by (cases x, simp)+

lemma ladder_shift_n_drop: "ladder_shift_n N (drop n L) = drop n (ladder_shift_n N L)"
proof (induct L arbitrary: n)
  case Nil then show ?case by simp
next
  case (Cons x L)
    show ?case
    proof (cases n)
      case 0 then show ?thesis 
        by simp
    next
      case (Suc n) then show ?thesis
        by (simp add: ladder_shift_n_cons Cons)
    qed
qed

lemma drop_2_shift:
  assumes "index > 0"
  assumes "length L > 1"
  shows "drop 2 L ! (index - Suc 0) = L ! Suc index"
proof -
  define l1 l2 and L' where "l1 = L ! 0" "l2 = L ! 1"
    and "L' = drop 2 L"
  with \<open>length L > 1\<close> have "L = l1 # l2 # L'"
    by (cases L) (auto simp add: neq_Nil_conv)
  with \<open>index > 0\<close> show ?thesis
    by simp
qed

lemma ladder_shift_n_at:
  "index < length L \<Longrightarrow> (ladder_shift_n N L) ! index = (fst (L ! index) - N, snd (L ! index))"
proof (induct L arbitrary: index)
  case Nil then show ?case by auto
next
  case (Cons x L)
    show ?case
      apply (simp add: ladder_shift_n_cons)
      apply (cases index)
      apply (auto)
      apply (rule_tac Cons(1))
      using Cons(2) by auto
qed

lemma ladder_stepdown_j:
  assumes length_L_greater_1: "length L > 1"
  assumes L': "L' = ladder_stepdown L"
  assumes index_bound: "index < length L'"
  shows "ladder_j L' index = ladder_j L (Suc index)"
proof -
  note L_prepare = ladder_stepdown_prepare[OF length_L_greater_1]  
  have ladder_stepdown_L_def: "ladder_stepdown L = ((ladder_n L (Suc 0) - Suc (ladder_n L 0), ladder_j L (Suc 0), ladder_j L 0 + ladder_ix L (Suc 0)) #
    ladder_shift_n (Suc (ladder_n L 0)) (drop 2 L))" 
    by (subst L_prepare, simp)
  have "index = 0 \<or> index > 0" by arith
  then show "ladder_j L' index = ladder_j L (Suc index)"
  proof (induct rule: disjCases2)
    case 1
      show ?case
        by (simp add: L' ladder_stepdown_L_def 1 ladder_j_def deriv_j_def)
  next
    case 2
      have index_bound': "Suc index < length L"
        using index_bound L' ladder_stepdown_length length_L_greater_1 by auto
      show ?case
        apply (simp add: L' ladder_stepdown_L_def 2 ladder_j_def ladder_shift_n_drop drop_2_shift)
        apply (subst drop_2_shift)
        apply (simp add: 2)
        using length_L_greater_1 apply (simp add: ladder_shift_n_length)
        apply (simp add: deriv_j_def)
        apply (simp add: ladder_shift_n_at[OF index_bound'])
        done
  qed
qed  

lemma ladder_stepdown_last_j:
  assumes length_L_greater_1: "length L > 1"
  shows "ladder_last_j (ladder_stepdown L) = ladder_last_j L"
  using ladder_stepdown_j Suc_diff_Suc diff_Suc_1 ladder_last_j_def ladder_stepdown_length 
  length_L_greater_1 lessI by auto

lemma ladder_stepdown_n:
  assumes length_L_greater_1: "length L > 1"
  assumes L': "L' = ladder_stepdown L"
  assumes index_bound: "index < length L'"
  shows "ladder_n L' index = ladder_n L (Suc index) - ladder_stepdown_diff L"
proof -
  note L_prepare = ladder_stepdown_prepare[OF length_L_greater_1]  
  have ladder_stepdown_L_def: "ladder_stepdown L = ((ladder_n L (Suc 0) - Suc (ladder_n L 0), ladder_j L (Suc 0), ladder_j L 0 + ladder_ix L (Suc 0)) #
    ladder_shift_n (Suc (ladder_n L 0)) (drop 2 L))" 
    by (subst L_prepare, simp)
  have "index = 0 \<or> index > 0" by arith
  then show "ladder_n L' index = ladder_n L (Suc index) - ladder_stepdown_diff L"
  proof (induct rule: disjCases2)
    case 1
      show ?case
        by (simp add: L' ladder_stepdown_L_def 1 ladder_n_def deriv_n_def ladder_stepdown_diff_def)
  next
    case 2
      have index_bound': "Suc index < length L"
        using index_bound L' ladder_stepdown_length length_L_greater_1 by auto
      show ?case
        apply (simp add: L' ladder_stepdown_L_def 2 ladder_n_def ladder_shift_n_drop drop_2_shift
          ladder_stepdown_diff_def)
        apply (subst drop_2_shift)
        apply (simp add: 2)
        using length_L_greater_1 apply (simp add: ladder_shift_n_length)
        apply (simp add: deriv_n_def)
        apply (simp add: ladder_shift_n_at[OF index_bound'])
        done
  qed
qed  

lemma ladder_stepdown_ix:
  assumes length_L_greater_1: "length L > 1"
  assumes L': "L' = ladder_stepdown L"
  assumes index_lower_bound: "0 < index"
  assumes index_upper_bound: "index < length L'"
  shows "ladder_ix L' index = ladder_ix L (Suc index)"
proof -
  note L_prepare = ladder_stepdown_prepare[OF length_L_greater_1]  
  have ladder_stepdown_L_def: "ladder_stepdown L = ((ladder_n L (Suc 0) - Suc (ladder_n L 0), ladder_j L (Suc 0), ladder_j L 0 + ladder_ix L (Suc 0)) #
    ladder_shift_n (Suc (ladder_n L 0)) (drop 2 L))" 
    by (subst L_prepare, simp)
      
  have index_bound': "Suc index < length L"
    using index_upper_bound L' ladder_stepdown_length length_L_greater_1 by auto
  show ?thesis
        apply (simp add: L' ladder_stepdown_L_def index_lower_bound ladder_ix_def ladder_shift_n_drop)
        apply (subst drop_2_shift)
        apply (simp add: index_lower_bound)
        using length_L_greater_1 apply (simp add: ladder_shift_n_length)
        apply (simp add: deriv_ix_def)
        apply (simp add: ladder_shift_n_at[OF index_bound'])
        using index_lower_bound by arith
qed

lemma Derive_Derive:
  assumes "Derivation \<alpha> (D@E) \<gamma>"
  shows "Derive (Derive \<alpha> D) E = Derive \<alpha> (D@E)"
using Derivation_append Derive assms by fastforce

lemma drop_at_shift:
  assumes "n \<le> index"
  assumes "index < length D"
  shows "drop n D ! (index - n) = D ! index"
using assms(1) assms(2) by auto

theorem LeftDerivationLadder_stepdown:
  assumes ldl: "LeftDerivationLadder \<alpha> D L \<gamma>" 
  assumes length_L: "length L > 1"
  shows "\<exists> L'. LeftDerivationLadder (ladder_stepdown_\<alpha>_0 \<alpha> D L) (drop (ladder_stepdown_diff L) D)
           L' \<gamma> \<and> length L' = length L - 1 \<and> ladder_i L' 0 = ladder_i L 1 + ladder_ix L 1 \<and>
           ladder_last_j L' = ladder_last_j L" 
proof -
  obtain L' where L': "L' = ladder_stepdown L" by blast
  have ldl1: "LeftDerivation (ladder_stepdown_\<alpha>_0 \<alpha> D L) (drop (ladder_stepdown_diff L) D) \<gamma>"
  proof -
    have D_split: "D = (take (ladder_stepdown_diff L) D) @ (drop (ladder_stepdown_diff L) D)"
      by simp
    show ?thesis using D_split ldl
      proof -
        obtain sss :: "symbol list \<Rightarrow> (nat \<times> symbol \<times> symbol list) list \<Rightarrow> (nat \<times> symbol \<times> symbol list) list \<Rightarrow> symbol list \<Rightarrow> symbol list" where
          "\<forall>x0 x1 x2 x3. (\<exists>v4. LeftDerivation x3 x2 v4 \<and> LeftDerivation v4 x1 x0) = (LeftDerivation x3 x2 (sss x0 x1 x2 x3) \<and> LeftDerivation (sss x0 x1 x2 x3) x1 x0)"
          by moura
        then have "(\<not> LeftDerivation \<alpha> (take (ladder_stepdown_diff L) D @ drop (ladder_stepdown_diff L) D) \<gamma> \<or> LeftDerivation \<alpha> (take (ladder_stepdown_diff L) D) (sss \<gamma> (drop (ladder_stepdown_diff L) D) (take (ladder_stepdown_diff L) D) \<alpha>) \<and> LeftDerivation (sss \<gamma> (drop (ladder_stepdown_diff L) D) (take (ladder_stepdown_diff L) D) \<alpha>) (drop (ladder_stepdown_diff L) D) \<gamma>) \<and> (LeftDerivation \<alpha> (take (ladder_stepdown_diff L) D @ drop (ladder_stepdown_diff L) D) \<gamma> \<or> (\<forall>ss. \<not> LeftDerivation \<alpha> (take (ladder_stepdown_diff L) D) ss \<or> \<not> LeftDerivation ss (drop (ladder_stepdown_diff L) D) \<gamma>))"
          using LeftDerivation_append by blast
        then show ?thesis
          by (metis (no_types) D_split Derivation_take_derive Derivation_unique_dest LeftDerivationLadder_def LeftDerivation_implies_Derivation ladder_stepdown_\<alpha>_0_def ldl)
      qed 
  qed
  have L'_nonempty: "L' \<noteq> []" using L' ladder_stepdown_length length_L by fastforce
  {
    fix u :: nat
    assume u': "u < length L'"
    then have Suc_u: "Suc u < length L" using L' ladder_stepdown_length length_L by auto
    have "ladder_n L (Suc u)  \<le> length D"
      using ldl Suc_u by (simp add: LeftDerivationLadder_ladder_n_bound) 
    then have "ladder_n L' u \<le> length D - ladder_stepdown_diff L"
      apply (subst ladder_stepdown_n[OF length_L L' u'])
      by auto
  }
  note is_ladder_prop1 = this
  {
    fix u :: nat
    fix v :: nat
    assume u_less_v: "u < v"
    assume v_L': "v < length L'"
    from u_less_v v_L' have u_L': "u < length L'" by arith
    have "ladder_n L (Suc u) < ladder_n L (Suc v)"
      using ldl by (metis (no_types, lifting) L' LeftDerivationLadder_def One_nat_def Suc_diff_1 
        Suc_lessD Suc_mono is_ladder_def ladder_stepdown_length length_L u_less_v v_L') 
    then have "ladder_n L' u < ladder_n L' v"
      apply (simp add: ladder_stepdown_n[OF length_L L'] u_L' v_L')
      by (metis (no_types, lifting) L' LeftDerivationLadder_def Suc_eq_plus1 Suc_leI 
        diff_less_mono is_ladder_def ladder_stepdown_diff_def ladder_stepdown_length ldl 
        length_L less_diff_conv u_L' zero_less_Suc)
  }
  note is_ladder_prop2 = this
  have is_ladder_L': "is_ladder (drop (ladder_stepdown_diff L) D) L'"
    apply (auto simp add: is_ladder_def)
    using L'_nonempty apply blast
    using is_ladder_prop1 apply blast
    using is_ladder_prop2 apply blast
    using ladder_last_n_def ladder_stepdown_n L' LeftDerivationLadder_def Suc_diff_Suc diff_Suc_1 
      ladder_n_last_is_length ladder_stepdown_length ldl length_L lessI by auto 
  have ldfix: "LeftDerivationFix (ladder_stepdown_\<alpha>_0 \<alpha> D L) (ladder_i L' 0)
     (take (ladder_n L' 0) (drop (ladder_stepdown_diff L) D)) (ladder_j L' 0)
     (ladder_\<gamma> (ladder_stepdown_\<alpha>_0 \<alpha> D L) (drop (ladder_stepdown_diff L) D) L' 0)"
  proof -
    have introsAt_L_1: "LeftDerivationIntrosAt \<alpha> D L 1"
      using LeftDerivationIntros_def LeftDerivationLadder_def ldl length_L by blast
    thm LeftDerivationIntrosAt_def
    obtain n where n: "n = ladder_n L 0" by blast
    obtain m where m: "m = ladder_n L 1" by blast
    have "LeftDerivationIntro (ladder_\<alpha> \<alpha> D L 1) (ladder_i L 1) (snd (D ! n)) 
      (ladder_ix L 1) (drop (Suc n) (take m D)) (ladder_j L 1) (ladder_\<gamma> \<alpha> D L 1)"  
      using n m introsAt_L_1 by (metis LeftDerivationIntrosAt_def One_nat_def diff_Suc_1) 
    from iffD1[OF  LeftDerivationIntro_def this] obtain \<beta> where \<beta>:
      "LeftDerives1 (ladder_\<alpha> \<alpha> D L 1) (ladder_i L 1) (snd (D ! n)) \<beta> \<and>
       ladder_ix L 1 < length (snd (snd (D ! n))) \<and>
       snd (snd (D ! n)) ! ladder_ix L 1 = ladder_\<gamma> \<alpha> D L 1 ! ladder_j L 1 \<and>
       LeftDerivationFix \<beta> (ladder_i L 1 + ladder_ix L 1) (drop (Suc n) (take m D)) (ladder_j L 1)
       (ladder_\<gamma> \<alpha> D L 1)"
       by blast
    have "\<beta> = Derive (ladder_\<alpha> \<alpha> D L 1) [D ! n]"
      by (metis (no_types, hide_lams) LeftDerivationIntrosAt_def LeftDerives1_Derive \<beta> 
        cancel_comm_monoid_add_class.diff_cancel introsAt_L_1 n prod.collapse) 
    then have \<beta>_def: "\<beta> = ladder_stepdown_\<alpha>_0 \<alpha> D L"
      proof -
        obtain sss :: "nat \<Rightarrow> symbol list \<Rightarrow> symbol list" and ss :: "nat \<Rightarrow> symbol list \<Rightarrow> symbol" and sssa :: "nat \<Rightarrow> symbol list \<Rightarrow> symbol list" where
          "\<forall>x2 x3. (\<exists>v4 v5 v6. splits_at x3 x2 v4 v5 v6) = splits_at x3 x2 (sss x2 x3) (ss x2 x3) (sssa x2 x3)"
          by moura
        then have f1: "\<forall>ssa n p ssb. \<not> Derives1 ssa n p ssb \<or> splits_at ssa n (sss n ssa) (ss n ssa) (sssa n ssa)"
          using splits_at_ex by presburger
        then have "\<beta> = sss (ladder_i L 1) (ladder_\<alpha> \<alpha> D L 1) @ snd (snd (D ! n)) @ sssa (ladder_i L 1) (ladder_\<alpha> \<alpha> D L 1)"
          by (meson LeftDerives1_implies_Derives1 \<beta> splits_at_combine_dest)
        then show ?thesis
          using f1 by (metis (no_types) LeftDerives1_implies_Derives1 \<beta> ladder_stepdown_\<alpha>_0_altdef ldl length_L n)
      qed       
    have ladder_i_L'_0: "ladder_i L' 0 = ladder_i L 1 + ladder_ix L 1"
      using L' ladder_stepdown_i_0 length_L by blast
    have derivation_eq: "(take (ladder_n L' 0) (drop (ladder_stepdown_diff L) D)) = 
      (drop (Suc n) (take m D))" using n m
      by (metis L' L'_nonempty One_nat_def drop_take ladder_stepdown_diff_def ladder_stepdown_n
        length_L length_greater_0_conv)  
    have ladder_j_L'_0: "ladder_j L' 0 = ladder_j L 1"
      using L' L'_nonempty ladder_stepdown_j length_L by auto  
    have ladder_\<gamma>: "(ladder_\<gamma> (ladder_stepdown_\<alpha>_0 \<alpha> D L) (drop (ladder_stepdown_diff L) D) L' 0) =
      ladder_\<gamma> \<alpha> D L 1"
      by (metis Derivation_take_derive Derivation_unique_dest LeftDerivationFix_def 
        LeftDerivation_implies_Derivation \<beta> \<beta>_def derivation_eq ladder_\<gamma>_def ldl1)   
    from \<beta>_def \<beta> ladder_i_L'_0 derivation_eq ladder_j_L'_0 ladder_\<gamma>
    show ?thesis by auto
  qed 
  {
    fix index :: nat
    assume index_lower_bound: "Suc 0 \<le> index"
    assume index_upper_bound: "index < length L'"
    then have Suc_index_upper_bound: "Suc index < length L"
      using L' Suc_diff_Suc Suc_less_eq diff_Suc_1 ladder_stepdown_length length_L less_Suc_eq 
      by auto
    then have intros_at_Suc_index: "LeftDerivationIntrosAt \<alpha> D L (Suc index)"
      by (metis LeftDerivationIntros_def LeftDerivationLadder_def Suc_eq_plus1_left ldl le_add1)      
    from iffD1[OF LeftDerivationIntrosAt_def this] have ldintro:
      "let \<alpha>' = ladder_\<alpha> \<alpha> D L (Suc index); i = ladder_i L (Suc index); j = ladder_j L (Suc index);
       ix = ladder_ix L (Suc index); \<gamma> = ladder_\<gamma> \<alpha> D L (Suc index); n = ladder_n L (Suc index - 1);
       m = ladder_n L (Suc index); e = D ! n; E = drop (Suc n) (take m D)
       in i = fst e \<and> LeftDerivationIntro \<alpha>' i (snd e) ix E j \<gamma>" by blast
    have index_minus_Suc_0_bound: "index - Suc 0 < length L'"
      by (simp add: index_upper_bound less_imp_diff_less)
    note helpers = length_L L' index_minus_Suc_0_bound
    have ladder_i_L'_index:
      "ladder_i L' index = fst (drop (ladder_stepdown_diff L) D ! ladder_n L' (index - Suc 0))"
      apply (auto simp add: ladder_i_def)
      using index_lower_bound apply arith
      apply (simp add: ladder_stepdown_n[OF helpers] ladder_stepdown_j[OF helpers])
      apply (subst drop_at_shift)
      using LeftDerivationLadder_def Suc_index_upper_bound Suc_leI Suc_lessD is_ladder_def 
        ladder_stepdown_diff_def ldl apply presburger
      apply (metis LeftDerivationLadder_def One_nat_def Suc_eq_plus1 Suc_index_upper_bound 
        add.commute add_diff_cancel_right' ladder_n_minus_1_bound ldl le_add1)
      by (metis LeftDerivationIntrosAt_def intros_at_Suc_index diff_Suc_1 ladder_i_def nat.simps(3))
    have intro_at_index: 
      "LeftDerivationIntro (ladder_\<alpha> (ladder_stepdown_\<alpha>_0 \<alpha> D L) (drop (ladder_stepdown_diff L) D) L' index)
       (ladder_i L' index) (snd (drop (ladder_stepdown_diff L) D ! ladder_n L' (index - Suc 0)))
       (ladder_ix L' index)
       (drop (Suc (ladder_n L' (index - Suc 0)))
         (take (ladder_n L' index) (drop (ladder_stepdown_diff L) D)))
       (ladder_j L' index) (ladder_\<gamma> (ladder_stepdown_\<alpha>_0 \<alpha> D L) 
         (drop (ladder_stepdown_diff L) D) L' index)" 
    proof -
      have arg1: "(ladder_\<alpha> (ladder_stepdown_\<alpha>_0 \<alpha> D L) 
        (drop (ladder_stepdown_diff L) D) L' index) = ladder_\<alpha> \<alpha> D L (Suc index)"
        apply (auto simp add: ladder_\<alpha>_def ladder_\<gamma>_def)
        using index_lower_bound apply arith
        apply (simp add: ladder_stepdown_n[OF helpers] ladder_stepdown_\<alpha>_0_def)
        apply (subst Derive_Derive[where \<gamma>="ladder_\<gamma> \<alpha> D L index"])
        apply (metis (no_types, lifting) Derivation_take_derive LeftDerivationLadder_def 
          LeftDerivation_implies_Derivation Suc_index_upper_bound Suc_leI Suc_lessD 
          add.commute is_ladder_def ladder_\<gamma>_def ladder_stepdown_diff_def ldl 
          le_add_diff_inverse2 take_add)
        by (metis LeftDerivationLadder_def Suc_index_upper_bound Suc_leI Suc_lessD add.commute 
          is_ladder_def ladder_stepdown_diff_def ldl le_add_diff_inverse2 take_add)
      have arg2: "ladder_i L' index = ladder_i L (Suc index)"
        using L' index_lower_bound index_minus_Suc_0_bound ladder_i_def ladder_stepdown_j 
          length_L by auto
      obtain n where n: "n = ladder_n L (Suc index - 1)" by blast
      have arg3: "(snd (drop (ladder_stepdown_diff L) D ! ladder_n L' (index - Suc 0))) = 
        snd (D ! n)"
        apply (simp add: ladder_stepdown_n[OF helpers] index_lower_bound)
        apply (subst drop_at_shift)
        using index_lower_bound
        apply (metis (no_types, hide_lams) L' LeftDerivationLadder_def One_nat_def Suc_eq_plus1 
          add.commute diff_Suc_1 index_upper_bound is_ladder_def ladder_stepdown_diff_def 
          ladder_stepdown_length ldl le_add_diff_inverse2 length_L less_or_eq_imp_le n 
          nat.simps(3) neq0_conv not_less not_less_eq_eq) 
        using index_lower_bound
        apply (metis LeftDerivationLadder_def One_nat_def Suc_index_upper_bound Suc_le_lessD 
          Suc_pred diff_Suc_1 ladder_n_minus_1_bound ldl le_imp_less_Suc less_imp_le) 
        using index_lower_bound n by (simp add: Suc_diff_le) 
      have arg4: "ladder_ix L' index = ladder_ix L (Suc index)"
        using ladder_stepdown_ix L' Suc_le_lessD index_lower_bound index_upper_bound length_L 
        by auto 
      obtain m where m: "m = ladder_n L (Suc index)" by blast
      have Suc_index_Suc: "Suc (index - Suc 0) = index"
        using index_lower_bound by arith
      have arg5: "(drop (Suc (ladder_n L' (index - Suc 0))) (take (ladder_n L' index) 
        (drop (ladder_stepdown_diff L) D))) = drop (Suc n) (take m D)"
        apply (simp add: ladder_stepdown_n[OF helpers] 
          ladder_stepdown_n[OF length_L L' index_upper_bound] n m Suc_index_Suc)
        by (metis (no_types, lifting) LeftDerivationLadder_def Suc_eq_plus1_left 
          Suc_index_upper_bound Suc_leI Suc_le_lessD Suc_lessD drop_drop drop_take 
          index_lower_bound is_ladder_def ladder_stepdown_diff_def ldl le_add_diff_inverse2)
      have arg6: "ladder_j L' index = ladder_j L (Suc index)"
        using L' index_upper_bound ladder_stepdown_j length_L by blast
      have arg7: "(ladder_\<gamma> (ladder_stepdown_\<alpha>_0 \<alpha> D L) 
         (drop (ladder_stepdown_diff L) D) L' index) = ladder_\<gamma> \<alpha> D L (Suc index)"
        apply (simp add: ladder_\<gamma>_def)
        apply (simp add: ladder_stepdown_n[OF length_L L' index_upper_bound] ladder_stepdown_\<alpha>_0_def)
        apply (subst Derive_Derive[where \<gamma>="ladder_\<gamma> \<alpha> D L (Suc index)"])
        apply (metis (no_types, lifting) L' LeftDerivationLadder_def 
          LeftDerivation_implies_Derivation LeftDerivation_take_derive Suc_le_lessD 
          add_diff_inverse_nat diff_is_0_eq index_lower_bound index_upper_bound is_ladder_L' 
          is_ladder_def ladder_\<gamma>_def ladder_stepdown_n ldl le_0_eq length_L less_numeral_extra(3) 
          less_or_eq_imp_le take_add)
        by (metis (no_types, lifting) L' One_nat_def add_diff_inverse_nat diff_is_0_eq 
          index_lower_bound index_upper_bound is_ladder_L' is_ladder_def ladder_stepdown_n le_0_eq 
          le_neq_implies_less length_L less_numeral_extra(3) less_or_eq_imp_le take_add zero_less_one)
      from ldintro arg1 arg2 arg3 arg4 arg5 arg6 arg7 show ?thesis
        by (metis m n)
    qed            
    have "LeftDerivationIntrosAt (ladder_stepdown_\<alpha>_0 \<alpha> D L) (drop (ladder_stepdown_diff L) D) 
      L' index"
      apply (auto simp add: LeftDerivationIntrosAt_def Let_def)
      using ladder_i_L'_index apply blast
      using intro_at_index by blast
  }  
  note introsAt = this
  show ?thesis
    apply (rule_tac x="L'" in exI)
    apply auto
    defer 1
    using L' ladder_stepdown_length length_L apply auto[1]
    using ladder_stepdown_i_0 length_L L' apply auto[1]
    using ladder_stepdown_last_j L' length_L apply auto[1]
    apply (auto simp add: LeftDerivationLadder_def)
    using ldl1 apply blast
    using is_ladder_L' apply blast
    using ldfix apply blast
    apply (auto simp add: LeftDerivationIntros_def)
    apply (simp add: introsAt)
    done
qed

fun ladder_shift_j :: "nat \<Rightarrow> ladder \<Rightarrow> ladder" where 
  "ladder_shift_j d [] = []"
| "ladder_shift_j d ((n, j, i)#L) = ((n, j - d, i)#(ladder_shift_j d L))" 

definition ladder_cut_prefix :: "nat \<Rightarrow> ladder \<Rightarrow> ladder"
where
  "ladder_cut_prefix d L = 
    (ladder_shift_j d L)[0 := (ladder_n L 0, ladder_j L 0 - d, ladder_i L 0 - d)]"

lemma ladder_shift_j_length: 
  "length (ladder_shift_j d L) = length L"
  by (induct L, auto)

lemma ladder_cut_prefix_length:
  shows "length (ladder_cut_prefix d L) = length L"
apply (simp add: ladder_cut_prefix_def)
apply (simp add: ladder_shift_j_length)
done

lemma ladder_shift_j_cons: "ladder_shift_j d (x#L) = (fst x, fst (snd x) - d, snd(snd x))#
  (ladder_shift_j d L)"
  apply (induct L)
  by (cases x, simp)+

lemma deriv_j_ladder_shift_j: 
  "index < length L \<Longrightarrow> deriv_j (ladder_shift_j d L ! index) = deriv_j (L ! index) - d"
proof (induct L arbitrary: index)
  case Nil
    then show ?case by auto
next
  case (Cons x L)
    show ?case
      apply (subst ladder_shift_j_cons)
      apply (cases index)
      using Cons by (auto simp add: deriv_j_def)
qed     

lemma deriv_n_ladder_shift_j: 
  "index < length L \<Longrightarrow> deriv_n (ladder_shift_j d L ! index) = deriv_n (L ! index)"
proof (induct L arbitrary: index)
  case Nil
    then show ?case by auto
next
  case (Cons x L)
    show ?case
      apply (subst ladder_shift_j_cons)
      apply (cases index)
      using Cons by (auto simp add: deriv_n_def)
qed     

lemma deriv_ix_ladder_shift_j: 
  "index < length L \<Longrightarrow> deriv_ix (ladder_shift_j d L ! index) = deriv_ix (L ! index)"
proof (induct L arbitrary: index)
  case Nil
    then show ?case by auto
next
  case (Cons x L)
    show ?case
      apply (subst ladder_shift_j_cons)
      apply (cases index)
      using Cons by (auto simp add: deriv_ix_def)
qed     

lemma ladder_cut_prefix_j: 
  assumes index_bound: "index < length L"
  assumes length_L: "length L > 0"
  shows "ladder_j (ladder_cut_prefix d L) index = ladder_j L index - d"
  apply (simp add: ladder_j_def ladder_cut_prefix_def)
  apply (cases index)
  apply (auto simp add: length_L)
  apply (subst nth_list_update_eq)
  apply (simp only: ladder_shift_j_length length_L)
  apply (simp add: deriv_j_def)
  apply (subst deriv_j_ladder_shift_j)
  using index_bound apply arith
  by blast  

lemma hd_0_subst: "length L > 0 \<Longrightarrow> hd (L [0 := x]) = x"
  using hd_conv_nth by (simp add: upd_conv_take_nth_drop) 

lemma ladder_cut_prefix_i: 
  assumes index_bound: "index < length L"
  assumes length_L: "length L > 0"
  shows "ladder_i (ladder_cut_prefix d L) index = ladder_i L index - d"
  apply (simp add: ladder_i_def ladder_cut_prefix_def)
  apply (cases index)
  apply auto[1]
  apply (subst hd_0_subst)
  using length_L ladder_shift_j_length apply metis 
  apply (auto simp add: deriv_i_def)
  apply (case_tac nat)
  apply (simp add: ladder_j_def deriv_j_def)
  apply auto
  apply (subst nth_list_update_eq)
  using length_L ladder_shift_j_length apply auto[1]
  apply simp
  apply (simp add: ladder_j_def)
  apply (subst deriv_j_ladder_shift_j)
  using index_bound apply arith
  apply simp
  done  

lemma ladder_cut_prefix_n: 
  assumes index_bound: "index < length L"
  assumes length_L: "length L > 0"
  shows "ladder_n (ladder_cut_prefix d L) index = ladder_n L index"
  apply (simp add: ladder_cut_prefix_def)
  apply (cases index)
  apply (auto simp add: ladder_n_def)
  apply (subst nth_list_update_eq)
  apply (simp add: ladder_shift_j_length)
  using length_L apply blast
  apply (simp add: deriv_n_def )
  apply (rule_tac deriv_n_ladder_shift_j)
  using index_bound by arith

lemma ladder_cut_prefix_ix: 
  assumes index_bound: "index < length L"
  assumes length_L: "length L > 0"
  shows "ladder_ix (ladder_cut_prefix d L) index = ladder_ix L index"
  apply (simp add: ladder_cut_prefix_def)
  apply (cases index)
  apply (auto simp add: ladder_ix_def)
  apply (rule_tac deriv_ix_ladder_shift_j)
  using index_bound by arith

lemma LeftDerivationFix_derivation_ge_is_nonterminal:
  assumes ldfix: "LeftDerivationFix \<alpha> i D j \<gamma>"
  assumes derivation_ge_d: "derivation_ge D d"
  assumes is_nonterminal: "is_nonterminal (\<gamma> ! j)"
  shows "(D = [] \<and> \<alpha> = \<gamma> \<and> i = j) \<or> (i > d \<and> j \<ge> d)"
proof -
  have "is_nonterminal (\<alpha> ! i)" using ldfix is_nonterminal
    by (simp add: LeftDerivationFix_def)  
  from LeftDerivationFix_splits_at_nonterminal[OF ldfix this] obtain U a1 a2 b1 where U:
    "splits_at \<alpha> i a1 U a2 \<and> splits_at \<gamma> j b1 U a2 \<and> LeftDerivation a1 D b1" by blast
  have "D = [] \<or> D \<noteq> []" by auto
  then show ?thesis
  proof (induct rule: disjCases2)
    case 1
      then have "a1 = b1" using U by auto
      then have i_eq_j: "i = j" using U
        by (metis dual_order.strict_implies_order length_take min.absorb2 splits_at_def) 
      from 1 have "\<alpha> = \<gamma>" using ldfix LeftDerivationFix_def by auto
      with 1 i_eq_j show ?case by blast
  next
    case 2
      have "\<exists> a1'. LeftDerives1 a1 (fst (hd D)) (snd (hd D)) a1'" using U 2
        by (metis LeftDerivation.elims(2) list.sel(1))
      then obtain a1' where a1': "LeftDerives1 a1 (fst (hd D)) (snd (hd D)) a1'" by blast
      then have "(fst (hd D)) < length a1" using Derives1_bound LeftDerives1_implies_Derives1 by blast 
      then have fst_less_i: "(fst (hd D)) < i" using U
        by (simp add: leD min.absorb2 nat_le_linear splits_at_def) 
      have d_le_fst: "d \<le> fst (hd D)" using derivation_ge_d 2 by (simp add: derivation_ge_def)  
      with fst_less_i have d_less_i: "d < i" using le_less_trans by blast 
      have "\<exists> b1'. LeftDerives1 b1' (fst (last D)) (snd (last D)) b1" using U 2
        by (metis Derive LeftDerivation_Derive_take_LeftDerives1 LeftDerivation_implies_Derivation 
          last_conv_nth length_0_conv order_refl take_all)
      then obtain b1' where b1': "LeftDerives1 b1' (fst (last D)) (snd (last D)) b1" by blast
      then have "fst (last D) \<le> length b1" 
        using Derives1_bound' LeftDerives1_implies_Derives1 by blast 
      then have fst_le_j: "fst (last D) \<le> j" using U splits_at_def by auto   
      have "d \<le> fst (last D)" using derivation_ge_d 2 using derivation_ge_def last_in_set by blast 
      with fst_le_j have "d \<le> j" using order.trans by blast       
      with d_less_i show ?thesis by auto
  qed
qed

lemma LeftDerivationFix_derivation_ge:
  assumes ldfix: "LeftDerivationFix \<alpha> i D j \<gamma>"
  assumes derivation_ge_d: "derivation_ge D d"
  shows "i = j \<or> (i > d \<and> j \<ge> d)"
proof -
  from LeftDerivationFix_splits_at_symbol[OF ldfix] obtain U a1 a2 b1 b2 n where U:
    "splits_at \<alpha> i a1 U a2 \<and>
     splits_at \<gamma> j b1 U b2 \<and>
     n \<le> length D \<and>
     LeftDerivation a1 (take n D) b1 \<and>
     derivation_ge (drop n D) (Suc (length b1)) \<and>
     LeftDerivation a2 (derivation_shift (drop n D) (Suc (length b1)) 0) b2 \<and>
     (n = length D \<or> n < length D \<and> is_word (b1 @ [U]))" by blast
  have "n = 0 \<or> n > 0" by auto
  then show ?thesis
  proof (induct rule: disjCases2)
    case 1
      then have "a1 = b1" using U by auto
      then have i_eq_j: "i = j" using U
        by (metis dual_order.strict_implies_order length_take min.absorb2 splits_at_def) 
      then show ?case by blast
  next
    case 2
      obtain E where E: "E = take n D" by blast
      have E_nonempty: "E \<noteq> []" using E 2
        using U less_nat_zero_code list.size(3) take_eq_Nil by auto 
      have "\<exists> a1'. LeftDerives1 a1 (fst (hd E)) (snd (hd E)) a1'" using U E E_nonempty
        by (metis LeftDerivation.simps(2) list.exhaust list.sel(1))        
      then obtain a1' where a1': "LeftDerives1 a1 (fst (hd E)) (snd (hd E)) a1'" by blast
      then have "(fst (hd E)) < length a1" using Derives1_bound LeftDerives1_implies_Derives1 by blast 
      then have fst_less_i: "(fst (hd E)) < i" using U
        by (simp add: leD min.absorb2 nat_le_linear splits_at_def) 
      have d_le_fst: "d \<le> fst (hd E)" using derivation_ge_d E_nonempty E
        by (simp add: LeftDerivation.elims(2) U derivation_ge_def hd_conv_nth)
      with fst_less_i have d_less_i: "d < i" using le_less_trans by blast 
      have "\<exists> b1'. LeftDerives1 b1' (fst (last E)) (snd (last E)) b1" using E_nonempty U E
        by (metis LeftDerivation_append1 append_butlast_last_id prod.collapse)                
      then obtain b1' where b1': "LeftDerives1 b1' (fst (last E)) (snd (last E)) b1" by blast
      then have "fst (last E) \<le> length b1" 
        using Derives1_bound' LeftDerives1_implies_Derives1 by blast 
      then have fst_le_j: "fst (last E) \<le> j" using U splits_at_def by auto   
      have "d \<le> fst (last E)" using derivation_ge_d E_nonempty E 
        using derivation_ge_d last_in_set by (metis derivation_ge_def set_take_subset subsetCE) 
      with fst_le_j have "d \<le> j" using order.trans by blast       
      with d_less_i show ?thesis by auto
  qed
qed

lemma LeftDerivationIntro_derivation_ge:
  assumes ldintro: "LeftDerivationIntro \<alpha> i r ix D j \<gamma>"
  assumes i_ge_d: "i \<ge> d"
  assumes derivation_ge_d: "derivation_ge D d"
  shows "j \<ge> d"
proof -
  from iffD1[OF LeftDerivationIntro_def ldintro] obtain \<beta> where \<beta>:
    "LeftDerives1 \<alpha> i r \<beta> \<and> ix < length (snd r) \<and> snd r ! ix = \<gamma> ! j \<and> 
     LeftDerivationFix \<beta> (i + ix) D j \<gamma>" by blast
  then have "(i + ix = j) \<or> (i + ix > d \<and> j \<ge> d)"
    using LeftDerivationFix_derivation_ge derivation_ge_d by blast    
  then show ?thesis
  proof (induct rule: disjCases2)
    case 1 then show ?case using i_ge_d trans_le_add1 by blast
  next
    case 2 then show ?case by simp
  qed
qed

lemma derivation_ge_LeftDerivationLadder:
  assumes derivation_ge_d: "derivation_ge D d"
  assumes ladder: "LeftDerivationLadder \<alpha> D L \<gamma>"
  assumes ladder_i_0: "ladder_i L 0 \<ge> d"
  shows "index < length L \<Longrightarrow> ladder_i L index \<ge> d \<and> ladder_j L index \<ge> d"
proof (induct index)
  case 0
    from iffD1[OF LeftDerivationLadder_def ladder]
    have ldfix: "LeftDerivationFix \<alpha> (ladder_i L 0)
      (take (ladder_n L 0) D) (ladder_j L 0) (ladder_\<gamma> \<alpha> D L 0)" by blast
    have "derivation_ge (take (ladder_n L 0) D) d"
      using derivation_ge_d by (metis append_take_drop_id derivation_ge_append) 
    from ladder_i_0 derivation_ge_d LeftDerivationFix_derivation_ge[OF ldfix this]
    show ?case by linarith
next
  case (Suc n)
    have ladder_i_Suc: "ladder_i L (Suc n) \<ge> d" 
      apply (auto simp add: ladder_i_def)
      using Suc by auto
    from iffD1[OF LeftDerivationLadder_def ladder] have "LeftDerivationIntros \<alpha> D L"
      by blast
    then have "LeftDerivationIntrosAt \<alpha> D L (Suc n)"
      using Suc.prems
      by (metis LeftDerivationIntros_def Suc_eq_plus1_left le_add1)
    from iffD1[OF LeftDerivationIntrosAt_def this]
    show ?case using ladder_i_Suc LeftDerivationIntro_derivation_ge
      by (metis append_take_drop_id derivation_ge_append derivation_ge_d)
qed        

lemma derivation_shift_append:
  "derivation_shift (A@B) left right = 
    (derivation_shift A left right) @ (derivation_shift B left right)"
by (induct A, simp+)

lemma derivation_shift_right_left_subtract: 
  "right \<ge> left \<Longrightarrow> derivation_shift (derivation_shift L 0 right) left 0 = 
  derivation_shift L 0 (right - left)"
by (induct L, simp+)

lemma LeftDerivationFix_cut_prefix:
  assumes "LeftDerivationFix (\<delta>@\<alpha>) i D j \<gamma>"
  assumes "derivation_ge D (length \<delta>)"
  assumes "i \<ge> length \<delta>"
  assumes is_word_\<delta>: "is_word \<delta>"
  shows "\<exists> \<gamma>'. \<gamma> = \<delta> @ \<gamma>' \<and> 
    LeftDerivationFix \<alpha> (i - length \<delta>) (derivation_shift D (length \<delta>) 0) (j - length \<delta>) \<gamma>'"
proof -
  have j_ge_d: "j \<ge> length \<delta>" 
    using assms(3) LeftDerivationFix_derivation_ge[OF assms(1) assms(2)] by arith
  obtain \<gamma>' where \<gamma>': "\<gamma>' = drop (length \<delta>) \<gamma>" by blast
  from iffD1[OF LeftDerivationFix_def assms(1)] obtain E F where EF:
   "is_sentence (\<delta> @ \<alpha>) \<and>
    is_sentence \<gamma> \<and>
    LeftDerivation (\<delta> @ \<alpha>) D \<gamma> \<and>
    i < length (\<delta> @ \<alpha>) \<and>
    j < length \<gamma> \<and>
    (\<delta> @ \<alpha>) ! i = \<gamma> ! j \<and>
    D = E @ derivation_shift F 0 (Suc j) \<and>
    LeftDerivation (take i (\<delta> @ \<alpha>)) E (take j \<gamma>) \<and>
    LeftDerivation (drop (Suc i) (\<delta> @ \<alpha>)) F (drop (Suc j) \<gamma>)" by blast
  then have "LeftDerivation (\<delta> @ \<alpha>) D \<gamma>" by blast
  from LeftDerivation_skip_prefixword_ex[OF this is_word_\<delta>]
  obtain \<gamma>' where \<gamma>': "\<gamma> = \<delta> @ \<gamma>' \<and> LeftDerivation \<alpha> (derivation_shift D (length \<delta>) 0) \<gamma>'" by blast
  have ldf1: "is_sentence \<alpha>" using EF is_sentence_concat by blast 
  have ldf2: "is_sentence \<gamma>'" using EF \<gamma>' is_sentence_concat by blast 
  have ldf3: "i - length \<delta> < length \<alpha>"
    by (metis EF append_Nil assms(3) drop_append drop_eq_Nil not_le) 
  have ldf4: "j - length \<delta> < length \<gamma>'"
    by (metis EF append_Nil j_ge_d \<gamma>' drop_append drop_eq_Nil not_le) 
  have ldf5: "\<alpha> ! (i - length \<delta>) = \<gamma>' ! (j - length \<delta>)"
    by (metis \<gamma>' EF assms(3) j_ge_d leD nth_append)
  have D_split: "D = E @ derivation_shift F 0 (Suc j)" using EF by blast
  show ?thesis
    apply (rule_tac x=\<gamma>' in exI)
    apply (auto simp add: \<gamma>')
    apply (auto simp add: LeftDerivationFix_def)
    using ldf1 apply blast
    using ldf2 apply blast
    using \<gamma>' apply blast
    using ldf3 apply blast
    using ldf4 apply blast
    using ldf5 apply blast
    apply (rule_tac x="derivation_shift E (length \<delta>) 0" in exI)
    apply (rule_tac x="F" in exI)
    apply auto
    apply (subst D_split)
    apply (simp add: derivation_shift_append)
    apply (subst derivation_shift_right_left_subtract)
    apply (simp add: j_ge_d le_Suc_eq)
    using j_ge_d apply (simp add: Suc_diff_le)
    apply (metis EF LeftDerivation_implies_Derivation LeftDerivation_skip_prefix \<gamma>' 
      append_eq_conv_conj assms(3) drop_take is_word_Derivation_derivation_ge is_word_\<delta> 
      take_all take_append)
    using EF Suc_diff_le \<gamma>' assms(3) j_ge_d by auto 
qed

lemma LeftDerives1_propagate_prefix:
  "LeftDerives1 (\<delta> @ \<alpha>) i r \<beta> \<Longrightarrow> i \<ge> length \<delta> \<Longrightarrow> is_prefix \<delta> \<beta>"
proof -
  assume a1: "LeftDerives1 (\<delta> @ \<alpha>) i r \<beta>"
  assume a2: "length \<delta> \<le> i"
  have f3: "take i (\<delta> @ \<alpha>) = take i \<beta>"
    using a1 Derives1_take LeftDerives1_implies_Derives1 by blast
  then have f4: "length (take i \<beta>) = i"
    using a1 by (metis (no_types) Derives1_bound LeftDerives1_implies_Derives1 dual_order.strict_implies_order length_take min.absorb2)
  have "take (length \<delta>) (take i \<beta>) = \<delta>"
    using f3 a2 by (simp add: append_eq_conv_conj)
  then show ?thesis
    using f4 a2 by (metis (no_types) append_Nil2 append_eq_conv_conj diff_is_0_eq' is_prefix_take take_0 take_append)
qed

lemma LeftDerivationIntro_cut_prefix:
  assumes "LeftDerivationIntro (\<delta>@\<alpha>) i r ix D j \<gamma>"
  assumes "derivation_ge D (length \<delta>)"
  assumes "i \<ge> length \<delta>"
  assumes is_word_\<delta>: "is_word \<delta>"
  shows "\<exists> \<gamma>'. \<gamma> = \<delta> @ \<gamma>' \<and> 
    LeftDerivationIntro \<alpha> (i - length \<delta>) r ix (derivation_shift D (length \<delta>) 0) (j - length \<delta>) \<gamma>'"
proof -
  from iffD1[OF LeftDerivationIntro_def assms(1)] obtain \<beta> where \<beta>:
    "LeftDerives1 (\<delta> @ \<alpha>) i r \<beta> \<and>
     ix < length (snd r) \<and> snd r ! ix = \<gamma> ! j \<and> LeftDerivationFix \<beta> (i + ix) D j \<gamma>" by blast
  have "\<exists> \<beta>'. \<beta> = \<delta> @ \<beta>'" 
    using LeftDerives1_propagate_prefix \<beta> assms(3) by (metis append_dropped_prefix) 
  then obtain \<beta>' where \<beta>': "\<beta> = \<delta> @ \<beta>'" by blast
  with \<beta> have "LeftDerives1 (\<delta> @ \<alpha>) i r (\<delta> @ \<beta>')" by simp
  from LeftDerives1_skip_prefix[OF assms(3) this] 
  have \<alpha>_\<beta>': "LeftDerives1 \<alpha> (i - length \<delta>) r \<beta>'" by blast
  have ldfix: "LeftDerivationFix (\<delta> @ \<beta>') (i + ix) D j \<gamma>" using \<beta> \<beta>' by auto
  have \<delta>_le_i_plus_ix: "length \<delta> \<le> i + ix" using assms(3) by arith
  from LeftDerivationFix_cut_prefix[OF ldfix assms(2) \<delta>_le_i_plus_ix assms(4)]
  obtain \<gamma>' where \<gamma>': "\<gamma> = \<delta> @ \<gamma>' \<and>
     LeftDerivationFix \<beta>' (i + ix - length \<delta>) (derivation_shift D (length \<delta>) 0) (j - length \<delta>) \<gamma>'"
     by blast
  have same_symbol: "\<gamma> ! j = \<gamma>' ! (j - length \<delta>)"
    by (metis LeftDerivationFix_def \<beta> \<beta>' \<delta>_le_i_plus_ix \<gamma>' leD nth_append)
  have \<beta>'_\<gamma>': "LeftDerivationFix \<beta>' (i - length \<delta> + ix) 
    (derivation_shift D (length \<delta>) 0) (j - length \<delta>) \<gamma>'" by (simp add: \<gamma>' assms(3))   
  show ?thesis
    apply (simp add: LeftDerivationIntro_def)
    apply (rule_tac x=\<gamma>' in exI)
    apply (auto simp add: \<gamma>')
    apply (rule_tac x=\<beta>' in exI)
    by (auto simp add: \<beta> \<alpha>_\<beta>' same_symbol \<beta>'_\<gamma>')
qed    

lemma LeftDerivationLadder_implies_LeftDerivation_at_index:
  assumes "LeftDerivationLadder \<alpha> D L \<gamma>"
  assumes "index < length L"
  shows "LeftDerivation \<alpha> (take (ladder_n L index) D) (ladder_\<gamma> \<alpha> D L index)"
using LeftDerivationLadder_def LeftDerivation_take_derive assms(1) ladder_\<gamma>_def by auto

lemma LeftDerivationLadder_cut_prefix_propagate:
  assumes ladder: "LeftDerivationLadder (\<delta>@\<alpha>) D L \<gamma>"
  assumes is_word_\<delta>: "is_word \<delta>"
  assumes derivation_ge_\<delta>: "derivation_ge D (length \<delta>)"
  assumes ladder_i_0: "ladder_i L 0 \<ge> length \<delta>"
  assumes L': "L' = ladder_cut_prefix (length \<delta>) L"
  assumes D': "D' = derivation_shift D (length \<delta>) 0"
  shows "index < length L \<Longrightarrow> 
    LeftDerivation \<alpha> (take (ladder_n L' index) D') (ladder_\<gamma> \<alpha> D' L' index) \<and>
    ladder_\<alpha> (\<delta>@\<alpha>) D L index = \<delta>@(ladder_\<alpha> \<alpha> D' L' index) \<and>
    ladder_\<gamma> (\<delta>@\<alpha>) D L index = \<delta>@(ladder_\<gamma> \<alpha> D' L' index)"
proof (induct index) 
  case 0
    have ladder_\<alpha>: "ladder_\<alpha> (\<delta>@\<alpha>) D L 0 = \<delta>@(ladder_\<alpha> \<alpha> D' L' 0)"
      by (simp add: ladder_\<alpha>_def)
    have ldfix: "LeftDerivationFix (\<delta>@\<alpha>) (ladder_i L 0) (take (ladder_n L 0) D) 
      (ladder_j L 0) (ladder_\<gamma> (\<delta>@\<alpha>) D L 0)" using ladder LeftDerivationLadder_def by blast
    have dge_take: "derivation_ge (take (ladder_n L 0) D) (length \<delta>)"
      using derivation_ge_\<delta> by (metis append_take_drop_id derivation_ge_append) 
    from LeftDerivationFix_cut_prefix[OF ldfix dge_take ladder_i_0 is_word_\<delta>] 
    obtain \<gamma>' where \<gamma>': "ladder_\<gamma> (\<delta> @ \<alpha>) D L 0 = \<delta> @ \<gamma>' \<and>
      LeftDerivationFix \<alpha> (ladder_i L 0 - length \<delta>) (derivation_shift (take (ladder_n L 0) D) (length \<delta>) 0)
      (ladder_j L 0 - length \<delta>) \<gamma>'" by blast
    have ladder_\<gamma>: "ladder_\<gamma> (\<delta>@\<alpha>) D L 0 = \<delta>@(ladder_\<gamma> \<alpha> D' L' 0)"
      using \<gamma>' by (metis "0.prems" D' Derive L' LeftDerivationFix_def 
        LeftDerivation_implies_Derivation ladder_\<gamma>_def ladder_cut_prefix_n take_derivation_shift)
    have "LeftDerivation \<alpha> (take (ladder_n L' 0) D') (ladder_\<gamma> \<alpha> D' L' 0)" 
    proof -
      have "LeftDerivation (\<delta>@\<alpha>) (take (ladder_n L 0) D) (ladder_\<gamma> (\<delta>@\<alpha>) D L 0)"
        using LeftDerivationLadder_implies_LeftDerivation_at_index ladder "0.prems" by blast
      then show ?thesis
        by (metis D' LeftDerivationLadder_def LeftDerivation_skip_prefix 
          LeftDerivation_take_derive derivation_ge_\<delta> ladder ladder_\<gamma>_def)
    qed        
    then show ?case using ladder_\<alpha> ladder_\<gamma> by auto
next
  case (Suc index)
    have index_less_L: "index < length L" using Suc(2) by arith
    then have induct: "ladder_\<gamma> (\<delta>@\<alpha>) D L index = \<delta>@(ladder_\<gamma> \<alpha> D' L' index)"
      using Suc by blast
    then have ladder_\<alpha>: "ladder_\<alpha> (\<delta>@\<alpha>) D L (Suc index) = \<delta>@(ladder_\<alpha> \<alpha> D' L' (Suc index))"
      by (simp add: ladder_\<alpha>_def)
    have introsAt: "LeftDerivationIntrosAt (\<delta>@\<alpha>) D L (Suc index)"
      using Suc(2) ladder
      by (metis LeftDerivationIntros_def LeftDerivationLadder_def Suc_eq_plus1_left le_add1) 
    obtain n m e E where n: "n = ladder_n L (Suc index - 1)" and
      m: "m = ladder_n L (Suc index)" and e: "e = D ! n" and E: "E = drop (Suc n) (take m D)"
      by blast
    from iffD1[OF LeftDerivationIntrosAt_def introsAt] have 
      "LeftDerivationIntro (ladder_\<alpha> (\<delta> @ \<alpha>) D L (Suc index)) (ladder_i L (Suc index)) (snd e) 
       (ladder_ix L (Suc index)) E (ladder_j L (Suc index)) (ladder_\<gamma> (\<delta> @ \<alpha>) D L (Suc index))"
      using n m e E Let_def by meson 
    then have ldintro:
      "LeftDerivationIntro (\<delta>@(ladder_\<alpha> \<alpha> D' L' (Suc index))) (ladder_i L (Suc index)) (snd e) 
       (ladder_ix L (Suc index)) E (ladder_j L (Suc index)) (ladder_\<gamma> (\<delta> @ \<alpha>) D L (Suc index))"
      by (simp add: ladder_\<alpha>)
    have dge_E_\<delta>: "derivation_ge E (length \<delta>)"
      apply (simp add: E)
      using derivation_ge_\<delta>
      by (metis append_take_drop_id derivation_ge_append) 
    have ladder_i_Suc: "length \<delta> \<le> ladder_i L (Suc index)"
      using Suc.prems derivation_ge_LeftDerivationLadder derivation_ge_\<delta> ladder ladder_i_0 
      by blast
    from LeftDerivationIntro_cut_prefix[OF ldintro dge_E_\<delta> ladder_i_Suc is_word_\<delta>]
    obtain \<gamma>' where \<gamma>': "ladder_\<gamma> (\<delta> @ \<alpha>) D L (Suc index) = \<delta> @ \<gamma>' \<and>
      LeftDerivationIntro (ladder_\<alpha> \<alpha> D' L' (Suc index)) (ladder_i L (Suc index) - length \<delta>) (snd e)
      (ladder_ix L (Suc index)) (derivation_shift E (length \<delta>) 0) (ladder_j L (Suc index) - length \<delta>) \<gamma>'"
      by blast
    then have "LeftDerivation (ladder_\<alpha> \<alpha> D' L' (Suc index)) 
      ((ladder_i L (Suc index) - length \<delta>, snd e) # (derivation_shift E (length \<delta>) 0)) \<gamma>'"
      using LeftDerivationIntro_implies_LeftDerivation by blast
    then have "LeftDerivation (ladder_\<gamma> \<alpha> D' L' index) 
      ((ladder_i L (Suc index) - length \<delta>, snd e) # (derivation_shift E (length \<delta>) 0)) \<gamma>'"
      by (auto simp add: ladder_\<alpha>_def)
    have ld: "LeftDerivation \<alpha> (take (ladder_n L' (Suc index)) D') (ladder_\<gamma> \<alpha> D' L' (Suc index))" 
    proof -
      have "LeftDerivation (\<delta>@\<alpha>) (take (ladder_n L (Suc index)) D) (ladder_\<gamma> (\<delta>@\<alpha>) D L (Suc index))"
        using LeftDerivationLadder_implies_LeftDerivation_at_index ladder Suc.prems by blast
      then show ?thesis
        by (metis D' LeftDerivationLadder_def LeftDerivation_skip_prefix 
          LeftDerivation_take_derive derivation_ge_\<delta> ladder ladder_\<gamma>_def)
    qed        
    then show ?case
      using \<gamma>' D' Derive L' LeftDerivationIntro_def n m e E ld
        LeftDerivation_implies_Derivation ladder_\<gamma>_def ladder_cut_prefix_n take_derivation_shift
      by (metis (no_types, lifting) LeftDerivationLadder_implies_LeftDerivation_at_index 
        LeftDerivation_skip_prefixword_ex Suc.prems Suc_leI index_less_L is_word_\<delta> ladder 
        ladder_\<alpha> le_0_eq neq0_conv)
qed       

theorem LeftDerivationLadder_cut_prefix:
  assumes ladder: "LeftDerivationLadder (\<delta>@\<alpha>) D L \<gamma>"
  assumes is_word_\<delta>: "is_word \<delta>"
  assumes ladder_i_0: "ladder_i L 0 \<ge> length \<delta>"
  shows "\<exists> D' L' \<gamma>'. \<gamma> = \<delta> @ \<gamma>' \<and> 
    LeftDerivationLadder \<alpha> D' L' \<gamma>' \<and>
    D' = derivation_shift D (length \<delta>) 0 \<and>
    length L' = length L \<and> ladder_i L' 0 + length \<delta> = ladder_i L 0 \<and>
    ladder_last_j L' + length \<delta> = ladder_last_j L"
proof -
  obtain D' where D': "D' = derivation_shift D (length \<delta>) 0" by blast
  obtain L' where L': "L' = ladder_cut_prefix (length \<delta>) L" by blast
  obtain \<gamma>' where \<gamma>': "\<gamma>' = drop (length \<delta>) \<gamma>" by blast 
  have ladder_last_j_upper_bound: "ladder_last_j L < length \<gamma>" using ladder
    using ladder_last_j_bound by blast 
  have derivation_ge_\<delta>: "derivation_ge D (length \<delta>)" using is_word_\<delta> LeftDerivationLadder_def 
    LeftDerivation_implies_Derivation is_word_Derivation_derivation_ge ladder by blast 
  note derivation_ge_ladder =  
    derivation_ge_LeftDerivationLadder[OF derivation_ge_\<delta> ladder ladder_i_0]  
  have ladder_last_j_lower_bound: "ladder_last_j L \<ge> length \<delta>"
    using LeftDerivationLadder_def derivation_ge_ladder is_ladder_def ladder 
      ladder_last_j_def by auto 
  from ladder_last_j_upper_bound ladder_last_j_lower_bound 
  have \<delta>_less_\<gamma>: "length \<delta> < length \<gamma>" by arith
  then have \<gamma>_def: "\<gamma> = \<delta> @ \<gamma>'"
    by (metis LeftDerivation.simps(1) LeftDerivationLadder_def LeftDerivation_ge_take \<gamma>' 
      append_eq_conv_conj derivation_ge_\<delta> ladder)
  have length_L_nonzero: "length L \<noteq> 0"
     using LeftDerivationLadder_def is_ladder_def ladder by auto
  have ladder_i_L'_thm: "\<And> index. index < length L \<Longrightarrow> ladder_i L' index + length \<delta> = ladder_i L index"
    apply (simp add: L')
    apply (subst ladder_cut_prefix_i)
    apply simp
    using length_L_nonzero apply blast
    using derivation_ge_ladder by auto   
  have ladder_j_L'_thm: "\<And> index. index < length L \<Longrightarrow> ladder_j L' index + length \<delta> = ladder_j L index"
    apply (simp add: L')
    apply (subst ladder_cut_prefix_j)
    using LeftDerivationLadder_def is_ladder_def ladder apply blast 
    using LeftDerivationLadder_def is_ladder_def ladder apply blast 
    using derivation_ge_ladder by auto
  have length_L': "length L' = length L" using L' ladder_cut_prefix_length by simp 
  have \<alpha>_\<gamma>': "LeftDerivation \<alpha> D' \<gamma>'"
    using D' LeftDerivationLadder_def LeftDerivation_skip_prefix \<gamma>' derivation_ge_\<delta> ladder 
    by blast
  have length_D': "length D' = length D" by (simp add: D')   
  have is_ladder_D_L: "is_ladder D L" using LeftDerivationLadder_def ladder by blast 
  {
    fix u :: nat
    assume u_bound_L': "u < length L'"
    have u_bound_L: "u < length L" using length_L' using u_bound_L' by simp
    have "ladder_n L' u \<le> length D'"
      apply (simp add: length_D' L')
      apply (subst ladder_cut_prefix_n)
      apply (simp add: u_bound_L)
      using length_L_nonzero apply arith
      using u_bound_L is_ladder_D_L
      by (simp add: is_ladder_def)
  }
  note is_ladder_1 = this 
  {
    fix u :: nat
    fix v :: nat
    assume u_less_v: "u < v"
    assume v_bound_L': "v < length L'"
    then have v_bound_L: "v < length L" by (simp add: length_L')
    with u_less_v have u_bound_L: "u < length L" by arith
    have "ladder_n L' u < ladder_n L' v"
      apply (simp add: L')
      apply (subst ladder_cut_prefix_n)
      using u_bound_L apply blast
      using length_L_nonzero apply blast
      apply (subst ladder_cut_prefix_n)
      using v_bound_L apply blast
      using length_L_nonzero apply blast
      using u_less_v v_bound_L is_ladder_D_L by (simp add: is_ladder_def)
  }      
  note is_ladder_2 = this
  have is_ladder_3: "ladder_last_n L' = length D'"
    apply (simp add: length_D' ladder_last_n_def L')
    apply (subst ladder_cut_prefix_n)
    apply (simp add: ladder_cut_prefix_length)
    using length_L_nonzero apply auto[1]
    using length_L_nonzero apply blast
    apply (simp add: ladder_cut_prefix_length)
    using is_ladder_D_L by (simp add: is_ladder_def ladder_last_n_def) 
  have is_ladder_4: "LeftDerivationFix \<alpha> (ladder_i L' 0) (take (ladder_n L' 0) D') 
    (ladder_j L' 0) (ladder_\<gamma> \<alpha> D' L' 0)"
  proof -
    have ldfix: "LeftDerivationFix (\<delta>@\<alpha>) (ladder_i L 0) (take (ladder_n L 0) D) 
    (ladder_j L 0) (ladder_\<gamma> (\<delta>@\<alpha>) D L 0)"
    using ladder LeftDerivationLadder_def by blast 
    have dge: "derivation_ge (take (ladder_n L 0) D) (length \<delta>)"
      using derivation_ge_\<delta> by (metis append_take_drop_id derivation_ge_append) 
    from LeftDerivationFix_cut_prefix[OF ldfix dge ladder_i_0 is_word_\<delta>] 
    obtain \<gamma>' where \<gamma>': "ladder_\<gamma> (\<delta> @ \<alpha>) D L 0 = \<delta> @ \<gamma>' \<and>
      LeftDerivationFix \<alpha> (ladder_i L 0 - length \<delta>) (derivation_shift (take (ladder_n L 0) D) (length \<delta>) 0)
      (ladder_j L 0 - length \<delta>) \<gamma>'" by blast
    then show ?thesis
      using LeftDerivationLadder_cut_prefix_propagate D' L' append_eq_conv_conj derivation_ge_\<delta> 
        is_word_\<delta> ladder ladder_cut_prefix_i ladder_cut_prefix_j ladder_cut_prefix_n ladder_i_0 
        length_0_conv length_L_nonzero length_greater_0_conv take_derivation_shift by auto 
  qed  
  {
    fix index :: nat
    assume index_lower_bound: "Suc 0 \<le> index"
    assume index_upper_bound: "index < length L'"
    have introsAt: "LeftDerivationIntrosAt (\<delta>@\<alpha>) D L index"
      by (metis LeftDerivationIntros_def LeftDerivationLadder_def One_nat_def index_lower_bound 
        index_upper_bound ladder length_L')    
    then have ladder_i_L: "ladder_i L index = fst (D ! ladder_n L (index - Suc 0))"
      by (metis LeftDerivationIntrosAt_def One_nat_def \<open>LeftDerivationIntrosAt (\<delta> @ \<alpha>) D L index\<close>)
    have ladder_i_L'_as_L: "ladder_i L' index = ladder_i L index - (length \<delta>)"
      using ladder_cut_prefix_i L' index_upper_bound is_ladder_D_L is_ladder_not_empty length_L' 
        length_greater_0_conv by auto 
    have length_L_gr_0: "length L > 0" using length_L' length_L_nonzero by arith
    have index_Suc_upper_bound_L: "index - Suc 0 < length L" using index_upper_bound length_L' by arith
    have "fst (D' ! ladder_n L' (index - Suc 0)) =  fst (D ! ladder_n L (index - Suc 0)) - (length \<delta>)"
      apply (subst D', subst L')
      apply (subst ladder_cut_prefix_n[OF index_Suc_upper_bound_L length_L_gr_0])
      apply (simp add: derivation_shift_def)
      using index_lower_bound index_upper_bound is_ladder_D_L ladder_n_minus_1_bound length_L' by auto
    then have ladder_i_L': "ladder_i L' index = fst (D' ! ladder_n L' (index - Suc 0))" 
      using ladder_i_L ladder_i_L'_as_L by auto
    have "LeftDerivationIntro (ladder_\<alpha> \<alpha> D' L' index) (ladder_i L' index)
      (snd (D' ! ladder_n L' (index - Suc 0))) (ladder_ix L' index)
      (drop (Suc (ladder_n L' (index - Suc 0))) (take (ladder_n L' index) D')) (ladder_j L' index)
      (ladder_\<gamma> \<alpha> D' L' index)"
    proof -
      have "LeftDerivationIntro (ladder_\<alpha> (\<delta>@\<alpha>) D L index) (ladder_i L index)
        (snd (D ! ladder_n L (index - Suc 0))) (ladder_ix L index)
        (drop (Suc (ladder_n L (index - Suc 0))) (take (ladder_n L index) D)) (ladder_j L index)
        (ladder_\<gamma> (\<delta>@\<alpha>) D L index)" using introsAt
        by (metis LeftDerivationIntrosAt_def One_nat_def)
      then have ldintro: "LeftDerivationIntro (\<delta>@(ladder_\<alpha> \<alpha> D' L' index)) (ladder_i L index)
        (snd (D ! ladder_n L (index - Suc 0))) (ladder_ix L index)
        (drop (Suc (ladder_n L (index - Suc 0))) (take (ladder_n L index) D)) (ladder_j L index)
        (ladder_\<gamma> (\<delta>@\<alpha>) D L index)"
        using D' L' LeftDerivationLadder_cut_prefix_propagate derivation_ge_\<delta> index_upper_bound 
          is_word_\<delta> ladder ladder_i_0 length_L' by auto 
      have dge: "derivation_ge (drop (Suc (ladder_n L (index - Suc 0))) 
        (take (ladder_n L index) D)) (length \<delta>)" using derivation_ge_\<delta>
        by (metis append_take_drop_id derivation_ge_append)
      have \<delta>_le_i_L: "length \<delta> \<le> ladder_i L index"
        using derivation_ge_ladder index_upper_bound length_L' by auto        
      from LeftDerivationIntro_cut_prefix[OF ldintro dge \<delta>_le_i_L is_word_\<delta>] obtain \<gamma>' where \<gamma>':
         "ladder_\<gamma> (\<delta> @ \<alpha>) D L index = \<delta> @ \<gamma>' \<and>
           LeftDerivationIntro (ladder_\<alpha> \<alpha> D' L' index) (ladder_i L index - length \<delta>)
           (snd (D ! ladder_n L (index - Suc 0))) (ladder_ix L index)
           (derivation_shift (drop (Suc (ladder_n L (index - Suc 0))) (take (ladder_n L index) D)) 
           (length \<delta>) 0) (ladder_j L index - length \<delta>) \<gamma>'" by blast
      have h1: "ladder_i L' index = ladder_i L index - length \<delta>"
        using L' ladder_cut_prefix_i ladder_i_L'_as_L by blast 
      have h2: "(snd (D' ! ladder_n L' (index - Suc 0))) = (snd (D ! ladder_n L (index - Suc 0)))"
        apply (subst L', subst ladder_cut_prefix_n)
        apply (simp add: index_Suc_upper_bound_L)
        using length_L_gr_0 apply auto[1]
        apply (subst D')
        apply (simp add: derivation_shift_def)
        using index_lower_bound index_upper_bound is_ladder_D_L ladder_n_minus_1_bound 
          length_L' by auto
      have h3: "ladder_ix L' index = ladder_ix L index"
        using ladder_cut_prefix_ix L' index_upper_bound length_L' length_L_gr_0 by auto 
      have h4: "(drop (Suc (ladder_n L' (index - Suc 0))) (take (ladder_n L' index) D')) = 
        (derivation_shift (drop (Suc (ladder_n L (index - Suc 0))) (take (ladder_n L index) D)) 
           (length \<delta>) 0)"
        apply (subst D')
        apply (subst L')+
        apply (subst ladder_cut_prefix_n, simp add: index_Suc_upper_bound_L)
        using length_L_gr_0 apply blast
        apply (subst ladder_cut_prefix_n)
        using index_upper_bound length_L' apply arith
        using length_L_gr_0 apply blast
        apply (simp add: derivation_shift_def)
        by (simp add: drop_map take_map)
      have h5: "ladder_j L' index = ladder_j L index - length \<delta>"
        using ladder_cut_prefix_j L' index_upper_bound length_L' length_L_gr_0 by auto 
      have h6: "ladder_\<gamma> \<alpha> D' L' index = \<gamma>'"
        using D' L' LeftDerivationLadder_cut_prefix_propagate \<gamma>' derivation_ge_\<delta> index_upper_bound 
          is_word_\<delta> ladder ladder_i_0 length_L' by auto    
      show ?thesis using h1 h2 h3 h4 h5 h6 \<gamma>' by simp
    qed
    then have "LeftDerivationIntrosAt \<alpha> D' L' index"
      apply (auto simp add: LeftDerivationIntrosAt_def Let_def)
      using ladder_i_L' by blast
  }
  note is_ladder_5 = this
  show ?thesis
    apply (rule_tac x="D'" in exI)
    apply (rule_tac x="L'" in exI)
    apply (rule_tac x="\<gamma>'" in exI)
    apply auto
    using \<gamma>_def apply blast
    defer 1
    using D' apply blast
    using L' ladder_cut_prefix_length apply auto[1]
    apply (subst ladder_i_L'_thm)
    using LeftDerivationLadder_def is_ladder_def ladder apply blast 
    apply simp
    apply (simp add: ladder_last_j_def)
    apply (subst ladder_j_L'_thm)
    apply (simp add: length_L')
    using length_L_nonzero apply arith
    apply (simp add: length_L')
    apply (auto simp add: LeftDerivationLadder_def)
    using \<alpha>_\<gamma>' apply blast
    apply (auto simp add: is_ladder_def)
    using length_L_nonzero length_L' apply auto[1]
    using is_ladder_1 apply blast
    using is_ladder_2 apply blast
    using is_ladder_3 apply blast
    using is_ladder_4 apply blast
    by (auto simp add: LeftDerivationIntros_def is_ladder_5)
qed

end

end
