theory TheoremD2
imports LocalLexingLemmas Validity Derivations
begin

context LocalLexing begin

definition splits_at :: "sentence \<Rightarrow> nat \<Rightarrow> sentence \<Rightarrow> symbol \<Rightarrow> sentence \<Rightarrow> bool"
where
  "splits_at \<delta> i \<alpha> N \<beta> = (i < length \<delta> \<and> \<alpha> = take i \<delta> \<and> N = \<delta> ! i \<and> \<beta> = drop (Suc i) \<delta>)"

lemma splits_at_combine: "splits_at \<delta> i \<alpha> N \<beta> \<Longrightarrow> \<delta> = \<alpha> @ [N] @ \<beta>"
  by (simp add: id_take_nth_drop splits_at_def)

lemma splits_at_combine_dest: "Derives1 a i r b \<Longrightarrow> splits_at a i \<alpha> N \<beta> \<Longrightarrow> b = \<alpha> @ (snd r) @ \<beta>"
  by (metis (no_types, lifting) Derives1_drop Derives1_split append_assoc append_eq_conv_conj 
      length_append splits_at_def)

lemma Derives1_nonterminal: 
  assumes "Derives1 a i r b"
  assumes "splits_at a i \<alpha> N \<beta>"
  shows "fst r = N \<and> is_nonterminal N"
proof - 
  from assms have fst: "fst r = N"
    by (metis Derives1_split append_Cons nth_append_length splits_at_def)
  then have "is_nonterminal N"
    by (metis Derives1_def assms(1) prod.collapse rule_nonterminal_type)
  with fst show ?thesis by auto
qed

  
lemma splits_at_ex: "Derives1 \<delta> i r s \<Longrightarrow> \<exists> \<alpha> N \<beta>. splits_at \<delta> i \<alpha> N \<beta>"
by (simp add: Derives1_bound splits_at_def)

lemma splits_at_\<alpha>: "Derives1 \<delta> i r s \<Longrightarrow> splits_at \<delta> i \<alpha> N \<beta> \<Longrightarrow> 
  \<alpha> = take i \<delta> \<and> \<alpha> = take i s \<and> length \<alpha> = i"
by (metis Derives1_split append_eq_conv_conj splits_at_def)

lemma LeftDerives1_splits_at_is_word: "LeftDerives1 \<delta> i r s \<Longrightarrow> splits_at \<delta> i \<alpha> N \<beta> \<Longrightarrow> is_word \<alpha>"
by (metis LeftDerives1_def leftmost_def splits_at_def)
  
lemma splits_at_\<beta>: "Derives1 \<delta> i r s \<Longrightarrow> splits_at \<delta> i \<alpha> N \<beta> \<Longrightarrow> 
  \<beta> = drop (Suc i) \<delta> \<and> \<beta> = drop (i + length (snd r)) s \<and> length \<beta> = length \<delta> - i - 1"
by (metis Derives1_drop Suc_eq_plus1 diff_diff_left length_drop splits_at_def)

lemma Derives1_prefix:
  assumes ab: "Derives1 \<delta> i r (a@b)"
  assumes split: "splits_at \<delta> i \<alpha> N \<beta>"
  shows "is_prefix \<alpha> a \<or> is_prefix a \<alpha>" 
proof -
  have take: "\<alpha> = take i (a@b)" using ab split splits_at_\<alpha> by blast
  show ?thesis
  proof (cases "i \<le> length a")
    case True
    then have "\<alpha> = take i a" by (simp add: take)
    then have "is_prefix \<alpha> a" 
      by (metis append_take_drop_id is_prefix_def) 
    with True show ?thesis by auto
  next
    case False
    then have "is_prefix a \<alpha>"
      by (simp add: is_prefix_def nat_le_linear take) 
    with False show ?thesis by auto
  qed
qed

lemma Derives1_suffix:
  assumes ab: "Derives1 \<delta> i r (a@b)"
  assumes split: "splits_at \<delta> i \<alpha> N \<beta>"
  shows "is_suffix \<beta> b \<or> is_suffix b \<beta>" 
proof -
  have drop1: "\<beta> = drop (i + length (snd r)) (a@b)" using ab split splits_at_\<beta> by blast
  have drop2: "b = drop (length a) (a@b)" by simp
  show ?thesis
  proof (cases "(i + length (snd r)) \<le> length a")
    case True
    with drop1 drop2 have "is_suffix b \<beta>" by (simp add: is_suffix_def)
    then show ?thesis by auto
  next
    case False
    then have "length a \<le> (i + length (snd r))" by arith
    with drop1 drop2 have "is_suffix \<beta> b"
      by (metis append_Nil append_take_drop_id drop_append drop_eq_Nil is_suffix_def)
    then show ?thesis by auto
  qed
qed

lemma Derives1_skip_prefix:
  "length a \<le> i \<Longrightarrow> Derives1 (a@b) i r (a@c) \<Longrightarrow> Derives1 b (i - length a) r c"
apply (auto simp add: Derives1_def)
by (metis append_eq_append_conv_if is_sentence_concat is_sentence_cons is_symbol_def 
    length_drop rule_nonterminal_type)

lemma cancel_suffix:
  assumes "a @ c = b @ d"
  assumes "length c \<le> length d"
  shows "a = b @ (take (length d - length c) d)"
proof -
  have "a @ c = (b @ take (length d - length c) d) @ drop (length d - length c) d"
    by (metis append_assoc append_take_drop_id assms(1))
  then show ?thesis
    by (metis append_eq_append_conv assms(2) diff_diff_cancel length_drop)
qed

lemma is_sentence_take:
  "is_sentence y \<Longrightarrow> is_sentence (take n y)"
by (metis append_take_drop_id is_sentence_concat)

lemma Derives1_skip_suffix:
  assumes i: "i < length a"
  assumes D: "Derives1 (a@c) i r (b@c)"
  shows "Derives1 a i r b"
proof -
  note Derives1_def[where u="a@c" and v="b@c" and i=i and r=r]
  then have "\<exists>x y N \<alpha>.
    a @ c = x @ [N] @ y \<and>
    b @ c = x @ \<alpha> @ y \<and> is_sentence x \<and> is_sentence y \<and> (N, \<alpha>) \<in> \<RR> \<and> r = (N, \<alpha>) \<and> i = length x"
    using D by blast
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
    apply (simp only: Derives1_def)
    apply (rule_tac x=x in exI)
    apply (rule_tac x="?y" in exI)
    apply (rule_tac x="N" in exI)
    apply (rule_tac x="\<alpha>" in exI)
    apply auto
    by (rule is_sentence_take)
qed
  
lemma drop_cancel_suffix: "a@c = drop n (b@c) \<Longrightarrow> a = drop n b"
proof -
  assume a1: "a @ c = drop n (b @ c)"
  have "length (drop n b) = length b + length c - n - length c"
    by (metis add_diff_cancel_right' diff_commute length_drop)
  then show ?thesis
    using a1 by (metis add_diff_cancel_right' append_eq_append_conv drop_append 
      length_append length_drop)
qed

lemma drop_keep_last: "u \<noteq> [] \<Longrightarrow> u = drop n (a@[X]) \<Longrightarrow> u = drop n a @ [X]"
by (metis append_take_drop_id drop_butlast last_appendR snoc_eq_iff_butlast)
  
lemma Derives1_X_is_part_of_rule[consumes 2, case_names Suffix Prefix]:
  assumes aXb: "Derives1 \<delta> i r (a@[X]@b)"
  assumes split: "splits_at \<delta> i \<alpha> N \<beta>"
  assumes prefix: "\<And> \<beta>. \<delta> = a @ [X] @ \<beta> \<Longrightarrow> length a < i \<Longrightarrow> 
                     Derives1 \<beta> (i - length a - 1) r b \<Longrightarrow> False"
  assumes suffix: "\<And> \<alpha>. \<delta> = \<alpha> @ [X] @ b \<Longrightarrow> Derives1 \<alpha> i r a \<Longrightarrow> False" 
  shows "\<exists> u v. a = \<alpha> @ u \<and> b = v @ \<beta> \<and> (snd r) = u@[X]@v"
proof -
  have prefix_or: "is_prefix \<alpha> a \<or> is_proper_prefix a \<alpha>"
    by (metis Derives1_prefix split aXb is_prefix_eq_proper_prefix)
  have "is_proper_prefix a \<alpha> \<Longrightarrow> False"
  proof -
    assume proper:"is_proper_prefix a \<alpha>"
    then have "\<exists> u. u \<noteq> [] \<and> \<alpha> = a@u" by (metis is_proper_prefix_def)
    then obtain u where u: "u \<noteq> [] \<and> \<alpha> = a@u" by blast
    note splits_at = splits_at_\<alpha>[OF aXb split] splits_at_combine[OF split]
    from splits_at have \<alpha>1: "\<alpha> = take i \<delta>" by blast
    from splits_at have \<alpha>2: "\<alpha> = take i (a@[X]@b)" by blast
    from splits_at have len\<alpha>: "length \<alpha> = i" by blast
    with proper have lena: "length a < i"
      using append_eq_conv_conj drop_eq_Nil leI u by auto 
    from u \<alpha>2 have "a@u = take i (a@[X]@b)" by auto
    with lena have "u = take (i - length a) ([X]@b)" by (simp add: less_or_eq_imp_le) 
    with lena have uX: "u = [X]@(take (i - length a - 1) b)" by (simp add: not_less take_Cons')
    let ?\<beta> = "(take (i - length a - 1) b) @ [N] @ \<beta>"
    from splits_at have f1: "\<delta> = \<alpha> @ [N] @ \<beta>" by blast
    with u uX have f2: "\<delta> = a @ [X] @ ?\<beta>" by simp
    note skip = Derives1_skip_prefix[where a = "a @ [X]" and b = "?\<beta>" and 
      r = r and i = i and c = b]
    then have D: "Derives1 ?\<beta> (i - length a - 1) r b"
      using One_nat_def Suc_leI aXb append_assoc diff_diff_left f2 lena length_Cons 
        length_append length_append_singleton list.size(3) by fastforce
    note prefix[OF f2 lena D]
    then show "False" .
  qed
  with prefix_or have is_prefix: "is_prefix \<alpha> a" by blast

  from aXb have aXb': "Derives1 \<delta> i r ((a@[X])@b)" by auto
  note  Derives1_suffix[OF aXb' split]
  then have suffix_or: "is_suffix \<beta> b \<or> is_proper_suffix b \<beta>"
    by (metis is_suffix_eq_proper_suffix)
  have "is_proper_suffix b \<beta> \<Longrightarrow> False"
  proof -
    assume proper: "is_proper_suffix b \<beta>"
    then have "\<exists> u. u \<noteq> [] \<and> \<beta> = u@b" by (metis is_proper_suffix_def)
    then obtain u where u: "u \<noteq> [] \<and> \<beta> = u@b" by blast
    note splits_at = splits_at_\<beta>[OF aXb split] splits_at_combine[OF split]
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
    note skip = Derives1_skip_suffix[where a = "?\<alpha>" and c = "[X]@b" and b="a" and
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
    from aXb f2 have D: "Derives1 (?\<alpha> @ [X] @ b) i r (a@[X]@b)" by auto
    note skip[OF f3 D]
    note suffix[OF f2  skip[OF f3 D]]
    then show "False" .
  qed
  with suffix_or have is_suffix: "is_suffix \<beta> b" by blast

  from is_prefix have "\<exists> u. a = \<alpha> @ u" by (auto simp add: is_prefix_def)
  then obtain u where u: "a = \<alpha> @ u" by blast
  from is_suffix have "\<exists> v. b = v @ \<beta>" by (auto simp add: is_suffix_def)
  then obtain v where v: "b = v @ \<beta>" by blast
  
  from u v splits_at_combine[OF split] aXb have D:"Derives1 (\<alpha>@[N]@\<beta>) i r (\<alpha>@(u@[X]@v)@\<beta>)"
    by simp
  from splits_at_\<alpha>[OF aXb split] have i: "length \<alpha> = i" by blast
  from i have i1: "length \<alpha> \<le> i" and i2: "i \<le> length \<alpha>" by auto
  note Derives1_skip_suffix[OF _ Derives1_skip_prefix[OF i1 D], simplified, OF i2]
  then have "Derives1 [N] 0 r (u @ [X] @ v)" by auto
  then have r: "snd r = u @ [X] @ v"
    by (metis Derives1_split append_Cons append_Nil length_0_conv list.inject self_append_conv) 

  show ?thesis using u v r by auto
qed   

lemma \<L>\<^sub>P_derives: "a \<in> \<L>\<^sub>P \<Longrightarrow> \<exists> b. derives [\<SS>] (a@b)"
by (simp add: \<L>\<^sub>P_def is_derivation_def)

lemma \<L>\<^sub>P_leftderives: "a \<in> \<L>\<^sub>P \<Longrightarrow> \<exists> b. leftderives [\<SS>] (a@b)"
by (metis \<L>\<^sub>P_derives \<L>\<^sub>P_is_word derives_implies_leftderives_gen)

lemma Derives1_rule: "Derives1 a i r b \<Longrightarrow> r \<in> \<RR>"
  by (auto simp add: Derives1_def)

lemma is_prefix_empty[simp]: "is_prefix [] a"
  by (simp add: is_prefix_def)

lemma is_prefix_cons: "is_prefix (x # a) b = (\<exists> c. b = x # c \<and> is_prefix a c)"
  by (metis append_Cons is_prefix_def)

lemma is_prefix_cancel[simp]: "is_prefix (a@b) (a@c) = is_prefix b c"
  by (metis append_assoc is_prefix_def same_append_eq)

lemma is_prefix_chars: "is_prefix a b \<Longrightarrow> is_prefix (chars a) (chars b)"
proof (induct a arbitrary: b)
  case Nil thus ?case by simp
next
  case (Cons x a)
  from Cons(2) have "\<exists> c. b = x # c \<and> is_prefix a c" 
    by (simp add: is_prefix_cons)
  then obtain c where c: "b = x # c \<and> is_prefix a c" by blast
  from c Cons(1) show ?case by simp
qed

lemma is_prefix_length: "is_prefix a b \<Longrightarrow> length a \<le> length b"
by (auto simp add: is_prefix_def)

lemma is_prefix_take[simp]: "is_prefix (take n a) a"
apply (auto simp add: is_prefix_def)
apply (rule_tac x="drop n a" in exI)
by simp

lemma doc_tokens_length: "doc_tokens p \<Longrightarrow> length (chars p) \<le> length Doc"
by (metis doc_tokens_def is_prefix_length)

fun count_terminals :: "sentence \<Rightarrow> nat" where
  "count_terminals [] = 0"
| "count_terminals (x#xs) = (if (is_terminal x) then Suc (count_terminals xs) else (count_terminals xs))"

lemma count_terminals_upper_bound: "count_terminals p \<le> length p"
  by (induct p, auto)

lemma count_terminals_append[simp]: "count_terminals (a@b) = count_terminals a + count_terminals b"
  by (induct a arbitrary: b, auto)

lemma Derives1_count_terminals:
  assumes D: "Derives1 a i r b"
  shows "count_terminals b = count_terminals a + count_terminals (snd r)"
proof -
  have "\<exists> \<alpha> N \<beta>. splits_at a i \<alpha> N \<beta>" using D splits_at_ex by simp
  then obtain \<alpha> N \<beta> where split: "splits_at a i \<alpha> N \<beta>" by blast
  from D split have N: "is_nonterminal N" by (simp add: Derives1_nonterminal)
  have a: "a = \<alpha> @ [N] @ \<beta>" by (metis split splits_at_combine)
  from D split have b: "b = \<alpha> @ (snd r) @ \<beta>" using splits_at_combine_dest by simp
  show ?thesis
    apply (simp add: a b)
    using N by (metis is_terminal_nonterminal) 
qed

lemma Derives1_count_terminals_leq:
  assumes D: "Derives1 a i r b"
  shows "count_terminals a \<le> count_terminals b"
by (metis Derives1_count_terminals assms le_less_linear not_add_less1)

lemma Derivation_count_terminals_leq:
  "Derivation a E b \<Longrightarrow> count_terminals a \<le> count_terminals b"
proof (induct E arbitrary: a)
  case Nil thus ?case by auto
next
  case (Cons e E)
  then have "\<exists> x i r. Derives1 a i r x \<and> Derivation x E b" using Derivation.simps(2) by blast 
  then obtain x i r where axb: "Derives1 a i r x \<and> Derivation x E b" by blast
  from axb have ax: "count_terminals a \<le> count_terminals x"
    using Derives1_count_terminals_leq by blast 
  from axb have xb: "count_terminals x \<le> count_terminals b" using Cons by simp
  show ?case using ax xb by arith
qed

lemma derives_count_terminals_leq: "derives a b \<Longrightarrow> count_terminals a \<le> count_terminals b"
using Derivation_count_terminals_leq derives_implies_Derivation by force

lemma is_word_cons[simp]: "is_word (x#xs) = (is_terminal x \<and> is_word xs)"
  by (simp add: is_word_def)  

lemma count_terminals_of_word: "is_word w \<Longrightarrow> count_terminals w = length w"
  by (induct w, auto)

lemma length_terminals[simp]: "length (terminals p) = length p"
  by (auto simp add: terminals_def)

lemma path_length_is_upper_bound:
  assumes p: "wellformed_tokens p"
  assumes \<alpha>: "is_word \<alpha>"
  assumes derives: "derives (\<alpha>@u) (terminals p)"
  shows "length \<alpha> \<le> length p"
proof -
  have counts: "count_terminals \<alpha> \<le> count_terminals (terminals p)"
    using derives derives_count_terminals_leq by fastforce
  have len1: "length \<alpha> = count_terminals \<alpha>" by (simp add: \<alpha> count_terminals_of_word)
  have len2: "length (terminals p) = count_terminals (terminals p)"
    by (simp add: count_terminals_of_word is_word_terminals p)
  show ?thesis using counts len1 len2 by auto
qed   
 
lemma is_word_Derives1_index:
  assumes w: "is_word w"
  assumes derives1: "Derives1 (w@a) i r b"
  shows "i \<ge> length w"
proof -
  from derives1 have n: "is_nonterminal ((w@a) ! i)"
    using Derives1_nonterminal splits_at_def splits_at_ex by auto
  from w have t: "i < length w \<Longrightarrow> is_terminal ((w@a) ! i)"
    by (simp add: is_word_is_terminal nth_append)
  show ?thesis
    by (metis t n is_terminal_nonterminal less_le_not_le nat_le_linear)
qed   
    
lemma is_word_Derivation_derivation_ge:
  assumes w: "is_word w"
  assumes D: "Derivation (w@a) D b"
  shows "derivation_ge D (length w)"
by (metis D Derivation_leftmost derivation_ge_empty leftmost_Derivation leftmost_append w)

lemma derives_word_is_prefix:
  assumes w: "is_word w"
  assumes derives: "derives (w@a) b"
  shows "is_prefix w b"
by (metis Derivation_take append_eq_conv_conj derives derives_implies_Derivation 
    is_prefix_take is_word_Derivation_derivation_ge w) 

lemma terminals_take[simp]: "terminals (take n p) = take n (terminals p)"
by (simp add: take_map terminals_def)

lemma terminals_drop[simp]: "terminals (drop n p) = drop n (terminals p)"
by (simp add: drop_map terminals_def)

lemma take_prefix[simp]: "is_prefix a b \<Longrightarrow> take (length a) b = a"
by (metis append_eq_conv_conj is_prefix_unsplit)
    
lemma Derives1_drop_prefixword: 
  assumes w: "is_word w"
  assumes wa_b: "Derives1 (w@a) i r b"
  shows "Derives1 a (i - length w) r (drop (length w) b)"
proof -
  have i: "length w \<le> i" using wa_b is_word_Derives1_index w by blast 
  have "is_prefix w b" by (metis append_eq_conv_conj i is_prefix_take le_Derives1_take wa_b)
  then have b: "b = w @ (drop (length w) b)" by (simp add: is_prefix_unsplit) 
  show ?thesis
    apply (rule_tac Derives1_skip_prefix[OF i])
    by (simp add: b[symmetric] wa_b)
qed

lemma derives1_drop_prefixword: 
  assumes w: "is_word w"
  assumes wa_b: "derives1 (w@a) b"
  shows "derives1 a (drop (length w) b)"
by (metis Derives1_drop_prefixword Derives1_implies_derives1 derives1_implies_Derives1 w wa_b)

lemma derives1_is_word_is_prefix_drop: 
  assumes w: "is_word w"
  assumes w_a: "is_prefix w a"
  assumes ab: "derives1 a b"
  shows "derives1 (drop (length w) a) (drop (length w) b)"
by (metis ab append_take_drop_id derives1_drop_prefixword take_prefix w w_a)
    
lemma derives_drop_prefixword_helper: 
  "derives a b \<Longrightarrow> is_word w \<Longrightarrow> is_prefix w a \<Longrightarrow> derives (drop (length w) a) (drop (length w) b)"
proof (induct rule: derives_induct)
  case Base thus ?case by auto
next
  case (Step y z) 
  have is_prefix_w_y: "is_prefix w y"
    by (metis Step.hyps(1) Step.prems(1) Step.prems(2) derives_word_is_prefix is_prefix_def) 
  thus ?case
    by (metis Step.hyps(2) Step.hyps(3) Step.prems(1) Step.prems(2) derives1_implies_derives 
        derives1_is_word_is_prefix_drop derives_trans) 
qed

lemma derive_drop_prefixword:
  "is_word w \<Longrightarrow> derives (w@a) b \<Longrightarrow> derives a (drop (length w) b)"
by (metis append_eq_conv_conj derives_drop_prefixword_helper is_prefix_take)

lemma thmD2':
  assumes X: "is_terminal X"
  assumes p: "doc_tokens p"
  assumes pX: "(terminals p)@[X] \<in> \<L>\<^sub>P"
  shows "\<exists> x. pvalid p x \<and> next_symbol x = Some X"
proof -
  from p have wellformed_p: "wellformed_tokens p" by (simp add: doc_tokens_def)
  have "\<exists> \<omega>. leftderives [\<SS>] (((terminals p)@[X]) @ \<omega>)" using \<L>\<^sub>P_leftderives pX by blast
  then obtain \<omega> where "leftderives [\<SS>] (((terminals p)@[X]) @ \<omega>)" by blast
  then have "\<exists> D. LeftDerivation [\<SS>] D (((terminals p)@[X]) @ \<omega>)"
    using leftderives_implies_LeftDerivation by blast
  then obtain D where D: "LeftDerivation [\<SS>] D (((terminals p)@[X]) @ \<omega>)" by blast
  let ?P = "\<lambda> k. (\<exists> a b. LeftDerivation [\<SS>] (take k D) (a@[X]@b) \<and> derives a (terminals p))"  
  have "?P (length D)"
    apply (rule_tac x="terminals p" in exI)
    apply (rule_tac x="\<omega>" in exI)
    using D by simp
  then show ?thesis
  proof (induct rule: minimal_witness[where P="?P"])
    case (Minimal K)
    from Minimal(2) obtain a b where
       aXb: "LeftDerivation [\<SS>] (take K D) (a @ [X] @ b)" and
       a: "derives a (terminals p)" by blast
    have KD: "K > 0 \<and> length D > 0"
    proof (cases "K = 0 \<or> length D = 0")
      case True
        hence "take K D = []" by auto
        with True aXb have "[\<SS>] = a @ [X] @ b" by simp
        hence "\<SS> = X"
          by (metis Nil_is_append_conv append_self_conv2 butlast.simps(2) 
              butlast_append hd_append2 list.sel(1) not_Cons_self2) 
        then have "False"
          using X is_nonterminal_startsymbol is_terminal_nonterminal by auto  
        then show ?thesis by blast
    next
      case False thus ?thesis by arith
    qed
    then have "take K D = take (K - 1) D @ [D ! (K - 1)]"
      by (metis Minimal.hyps(1) One_nat_def Suc_less_eq Suc_pred hd_drop_conv_nth 
          le_imp_less_Suc take_hd_drop)
    then have "\<exists> \<delta>. LeftDerivation [\<SS>] (take (K - 1) D) \<delta> \<and> LeftDerivation \<delta> [D ! (K - 1)] (a@[X]@b)"
      by (metis LeftDerivation_append aXb)
    then obtain \<delta> where 
      \<delta>1: "LeftDerivation [\<SS>] (take (K - 1) D) \<delta>"  
      and \<delta>2: "LeftDerivation \<delta> [D ! (K - 1)] (a@[X]@b)" 
      by blast
    from \<delta>2 have "\<exists> i r. LeftDerives1 \<delta> i r (a@[X]@b)" by fastforce
    then obtain i r where LeftDerives1_\<delta>: "LeftDerives1 \<delta> i r (a@[X]@b)" by blast
    then have Derives1_\<delta>: "Derives1 \<delta> i r (a@[X]@b)" 
      by (metis LeftDerives1_implies_Derives1) 
    then have "\<exists> \<alpha> N \<beta> . splits_at \<delta> i \<alpha> N \<beta>" by (simp add: splits_at_ex)
    then obtain \<alpha> N \<beta> where split_\<delta>: "splits_at \<delta> i \<alpha> N \<beta>" by blast
    have is_word_\<alpha>: "is_word \<alpha>" by (metis LeftDerives1_\<delta> LeftDerives1_splits_at_is_word split_\<delta>) 
    have "\<not> (?P (K - 1))" using KD Minimal(3) by auto
    with \<delta>1 have min_\<delta>: "\<not> (\<exists> a b. \<delta> = a@[X]@b \<and> derives a (terminals p))" by blast
    from Derives1_\<delta> split_\<delta> have "\<exists> u v. a = \<alpha> @ u \<and> b = v @ \<beta> \<and> (snd r) = u@[X]@v"
    proof (induction rule: Derives1_X_is_part_of_rule)
      case (Suffix \<gamma>)
        from min_\<delta> Suffix(1) a show ?case by auto
    next
      case (Prefix \<gamma>)
        have "derives \<gamma> (terminals p)"
          by (metis Derives1_implies_derives1 Prefix(2) a 
              derives1_implies_derives derives_trans)
        with min_\<delta> Prefix(1) show ?case by auto 
    qed
    then obtain u v where uXv: "a = \<alpha> @ u \<and> b = v @ \<beta> \<and> (snd r) = u@[X]@v" by blast 
    let ?l = "length \<alpha>"
    let ?q = "take ?l p"
    let ?x = "Item r (length u) (charslength ?q) (charslength p)"  
    have "item_rhs ?x = snd r" by (simp add: item_rhs_def)
    then have item_rhs_x: "item_rhs ?x = u@[X]@v" using uXv by simp
    have wellformed_x: "wellformed_item ?x" 
      apply (auto simp add: wellformed_item_def)
      apply (metis Derives1_\<delta> Derives1_rule)
      apply (rule is_prefix_length)
      apply (rule is_prefix_chars)
      apply simp
      apply (simp add: doc_tokens_length[OF p])
      using item_rhs_x by simp
    from item_rhs_x have next_symbol_x: "next_symbol ?x = Some X"
      by (auto simp add: next_symbol_def is_complete_def)
    have len_\<alpha>_p: "length \<alpha> \<le> length p"
      apply (rule_tac path_length_is_upper_bound[where u=u])
      apply (simp add: wellformed_p)
      apply (simp add: is_word_\<alpha>)
      using a uXv by blast
    have item_nonterminal_x: "item_nonterminal ?x = N"
      apply (simp add: item_nonterminal_def)
      using Derives1_\<delta> Derives1_nonterminal split_\<delta> by blast
    have take_terminals: "take (length \<alpha>) (terminals p) = \<alpha>"
      apply (rule_tac take_prefix)
      using a derives_word_is_prefix is_word_\<alpha> uXv by blast
    have item_\<alpha>_x: "item_\<alpha> ?x = u" using item_\<alpha>_def item_rhs_x by auto    
    from wellformed_x next_symbol_x len_\<alpha>_p show ?thesis
      apply (rule_tac x="?x" in exI)
      apply (auto simp add: pvalid_def wellformed_p)
      apply (rule_tac x="length \<alpha>" in exI)
      apply (auto)
      using item_nonterminal_x apply (simp)
      apply (simp add: take_terminals)
      apply (rule_tac x="\<beta>" in exI)
      using LeftDerivation_implies_leftderives \<delta>1 is_leftderivation_def split_\<delta> splits_at_combine 
      apply auto[1]
      using item_\<alpha>_x apply simp
      by (metis a derive_drop_prefixword is_word_\<alpha> uXv)
  qed
qed    
        
lemma admissible_wellformed_tokens: "admissible p \<Longrightarrow> wellformed_tokens p"
  by (auto simp add: admissible_def \<L>\<^sub>P_wellformed_tokens)

lemma chars_append[simp]: "chars (a@b) = (chars a)@(chars b)"
  by (induct a arbitrary: b, auto)

lemma chars_of_token_simp[simp]: "chars_of_token (a, b) = b"
  by (simp add: chars_of_token_def)

lemma \<X>_is_prefix: "t \<in> \<X> k \<Longrightarrow> is_prefix (snd t) (drop k Doc)"
  by (auto simp add: \<X>_def)

lemma is_prefix_append: "is_prefix (a@b) D = (is_prefix a D \<and> is_prefix b (drop (length a) D))"
  by (metis append_assoc is_prefix_cancel is_prefix_def is_prefix_unsplit)
  
lemma \<PP>_are_doc_tokens: "p \<in> \<PP> \<Longrightarrow> doc_tokens p"
proof (induct rule: \<PP>_induct)
  case Base thus ?case
    by (simp add: doc_tokens_def wellformed_tokens_def)
next
  case (Induct p k u)
  from Induct(2)[simplified] show ?case
  proof (induct rule: limit_induct)
    case (Init p) from Induct(1)[OF Init] show ?case .
  next
    case (Iterate p Y) 
    have Y_is_prefix: "\<And> p. p \<in> Y \<Longrightarrow> is_prefix (chars p) Doc"
      apply (drule Iterate(1))
      by (simp add: doc_tokens_def)
    have "\<Y> (\<Z> k u) (\<P> k u) k \<subseteq> \<X> k" by (metis \<Z>.simps(2) \<Z>_subset_\<X>)
    then have 1: "Append (\<Y> (\<Z> k u) (\<P> k u) k) k Y \<subseteq> Append (\<X> k) k Y"
      by (rule Append_mono, simp) 
    have 2: "p \<in> Append (\<X> k) k Y \<Longrightarrow> doc_tokens p"
      apply (auto simp add: Append_def)
      apply (simp add: Iterate)
      apply (auto simp add: doc_tokens_def admissible_wellformed_tokens 
             is_prefix_append Y_is_prefix)
      by (metis \<X>_is_prefix snd_conv)
    show ?case 
      apply (rule 2)
      by (metis (mono_tags, lifting) "1" Iterate(2) subsetCE)
  qed  
qed
    
theorem thmD2:
  assumes X: "is_terminal X"
  assumes p: "p \<in> \<PP>"
  assumes pX: "(terminals p)@[X] \<in> \<L>\<^sub>P"
  shows "\<exists> x. pvalid p x \<and> next_symbol x = Some X"
by (metis X \<PP>_are_doc_tokens p pX thmD2')

end

end
