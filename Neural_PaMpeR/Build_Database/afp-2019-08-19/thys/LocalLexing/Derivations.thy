theory Derivations
imports CFG ListTools InductRules
begin

(* leftderives and leftderives1 *)
context CFG begin

lemma [simp]: "is_terminal t \<Longrightarrow> is_symbol t"
  by (auto simp add: is_terminal_def is_symbol_def)

lemma [simp]: "is_sentence []" by (auto simp add: is_sentence_def)

lemma [simp]: "is_word []" by (auto simp add: is_word_def)

lemma [simp]: "is_word u \<Longrightarrow> is_sentence u"
  by (induct u, auto simp add: is_word_def is_sentence_def)

definition leftderives1 :: "sentence \<Rightarrow> sentence \<Rightarrow> bool"
where
  "leftderives1 u v = 
     (\<exists> x y N \<alpha>. 
          u = x @ [N] @ y
        \<and> v = x @ \<alpha> @ y
        \<and> is_word x
        \<and> is_sentence y
        \<and> (N, \<alpha>) \<in> \<RR>)"  

lemma leftderives1_implies_derives1[simp]: "leftderives1 u v \<Longrightarrow> derives1 u v"
  apply (auto simp add: leftderives1_def derives1_def)
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="y" in exI)
  apply (rule_tac x="N" in exI)
  by auto

definition leftderivations1 :: "(sentence \<times> sentence) set"
where
  "leftderivations1 = { (u,v) | u v. leftderives1 u v }"

lemma [simp]: "leftderivations1 \<subseteq> derivations1"
  by (auto simp add: leftderivations1_def derivations1_def)

definition leftderivations :: "(sentence \<times> sentence) set"
where 
  "leftderivations = leftderivations1^*"

lemma rtrancl_subset_implies: "a \<subseteq> b \<Longrightarrow> a \<subseteq> b^*" by blast

lemma leftderivations_subset_derivations[simp]: "leftderivations \<subseteq> derivations"
  apply (simp add: leftderivations_def derivations_def)
  apply (rule rtrancl_subset_rtrancl)
  apply (rule rtrancl_subset_implies)
  by simp

definition leftderives :: "sentence \<Rightarrow> sentence \<Rightarrow> bool"
where
  "leftderives u v = ((u, v) \<in> leftderivations)"

lemma leftderives_implies_derives[simp]: "leftderives u v \<Longrightarrow> derives u v"
  apply (auto simp add: leftderives_def derives_def)
  by (rule subsetD[OF leftderivations_subset_derivations])

definition is_leftderivation :: "sentence \<Rightarrow> bool"
where
  "is_leftderivation u = leftderives [\<SS>] u"

lemma leftderivation_implies_derivation[simp]: 
  "is_leftderivation u \<Longrightarrow> is_derivation u"
  by (simp add: is_leftderivation_def is_derivation_def)

lemma leftderives_refl[simp]: "leftderives u u"
  by (auto simp add: leftderives_def leftderivations_def)

lemma leftderives1_implies_leftderives[simp]:"leftderives1 a b \<Longrightarrow> leftderives a b"
  by (auto simp add: leftderives_def leftderivations_def leftderivations1_def)

lemma leftderives_trans: "leftderives a b \<Longrightarrow> leftderives b c \<Longrightarrow> leftderives a c"
  by (auto simp add: leftderives_def leftderivations_def)

lemma leftderives1_eq_leftderivations1: "leftderives1 x y = ((x, y) \<in> leftderivations1)"
  by (simp add: leftderivations1_def)

lemma leftderives_induct[consumes 1, case_names Base Step]:
  assumes derives: "leftderives a b"
  assumes Pa: "P a"
  assumes induct: "\<And>y z. leftderives a y \<Longrightarrow> leftderives1 y z \<Longrightarrow> P y \<Longrightarrow> P z"
  shows "P b"
proof -
  note rtrancl_lemma = rtrancl_induct[where a = a and b = b and r = leftderivations1 and P=P]
  from derives Pa induct rtrancl_lemma show "P b"
    by (metis leftderives_def leftderivations_def leftderives1_eq_leftderivations1)
qed

end

(* Basic lemmas about derives1 and derives *)
context CFG begin

lemma derives1_implies_derives[simp]:"derives1 a b \<Longrightarrow> derives a b"
  by (auto simp add: derives_def derivations_def derivations1_def)

lemma derives_trans: "derives a b \<Longrightarrow> derives b c \<Longrightarrow> derives a c"
  by (auto simp add: derives_def derivations_def)

lemma derives1_eq_derivations1: "derives1 x y = ((x, y) \<in> derivations1)"
  by (simp add: derivations1_def)

lemma derives_induct[consumes 1, case_names Base Step]:
  assumes derives: "derives a b"
  assumes Pa: "P a"
  assumes induct: "\<And>y z. derives a y \<Longrightarrow> derives1 y z \<Longrightarrow> P y \<Longrightarrow> P z"
  shows "P b"
proof -
  note rtrancl_lemma = rtrancl_induct[where a = a and b = b and r = derivations1 and P=P]
  from derives Pa induct rtrancl_lemma show "P b"
    by (metis derives_def derivations_def derives1_eq_derivations1)
qed

end

(* Derives1 and Derivation, LDerives1 and LDerivation *)
context CFG begin

definition Derives1 :: "sentence \<Rightarrow> nat \<Rightarrow> rule \<Rightarrow> sentence \<Rightarrow> bool"
where
  "Derives1 u i r v = 
     (\<exists> x y N \<alpha>. 
          u = x @ [N] @ y
        \<and> v = x @ \<alpha> @ y
        \<and> is_sentence x
        \<and> is_sentence y
        \<and> (N, \<alpha>) \<in> \<RR>
        \<and> r = (N, \<alpha>) \<and> i = length x)"  

lemma Derives1_split:
  "Derives1 u i r v \<Longrightarrow> \<exists> x y. u = x @ [fst r] @ y \<and> v = x @ (snd r) @ y \<and> length x = i"
by (metis Derives1_def fst_conv snd_conv)

lemma Derives1_implies_derives1: "Derives1 u i r v \<Longrightarrow> derives1 u v"
  by (auto simp add: Derives1_def derives1_def)

lemma derives1_implies_Derives1: "derives1 u v \<Longrightarrow> \<exists> i r. Derives1 u i r v"
  by (auto simp add: Derives1_def derives1_def)

lemma Derives1_unique_dest: "Derives1 u i r v \<Longrightarrow> Derives1 u i r w \<Longrightarrow> v = w"
  by (auto simp add: Derives1_def derives1_def)

lemma Derives1_unique_src: "Derives1 u i r w \<Longrightarrow> Derives1 v i r w \<Longrightarrow> u = v"
  by (auto simp add: Derives1_def derives1_def)

type_synonym derivation = "(nat \<times> rule) list"

fun Derivation :: "sentence \<Rightarrow> derivation \<Rightarrow> sentence \<Rightarrow> bool"
where
  "Derivation a [] b = (a = b)"
| "Derivation a (d#D) b = (\<exists> x. Derives1 a (fst d) (snd d) x \<and> Derivation x D b)"

lemma Derivation_implies_derives: "Derivation a D b \<Longrightarrow> derives a b"
proof (induct D arbitrary: a b)
  case Nil thus ?case 
    by (simp add: derives_def derivations_def)
next
  case (Cons d D)
    note ihyps = this
    from ihyps have "\<exists> x. Derives1 a (fst d) (snd d) x \<and> Derivation x D b" by auto
    then obtain x where "Derives1 a (fst d) (snd d) x" and xb: "Derivation x D b" by blast
    with Derives1_implies_derives1 have d1: "derives a x" by auto
    from ihyps xb have d2:"derives x b" by simp
    show "derives a b" by (rule derives_trans[OF d1 d2])
qed 

lemma Derivation_Derives1: "Derivation a S y \<Longrightarrow> Derives1 y i r z \<Longrightarrow> Derivation a (S@[(i,r)]) z"
proof (induct S arbitrary: a y z i r)
  case Nil thus ?case by simp
next
  case (Cons s S) thus ?case 
    by (metis Derivation.simps(2) append_Cons) 
qed

lemma derives_implies_Derivation: "derives a b \<Longrightarrow> \<exists> D. Derivation a D b"
proof (induct rule: derives_induct)
  case Base
  show ?case by (rule exI[where x="[]"], simp)
next
  case (Step y z)
  note ihyps = this
  from ihyps obtain D where ay: "Derivation a D y" by blast
  from ihyps derives1_implies_Derives1 obtain i r where yz: "Derives1 y i r z" by blast
  from Derivation_Derives1[OF ay yz] show ?case by auto
qed
    
lemma Derives1_take: "Derives1 a i r b \<Longrightarrow> take i a = take i b"
  by (auto simp add: Derives1_def)

lemma Derives1_drop: "Derives1 a i r b \<Longrightarrow> drop (Suc i) a = drop (i + length (snd r)) b"
  by (auto simp add: Derives1_def)

lemma Derives1_bound: "Derives1 a i r b \<Longrightarrow> i < length a"
  by (auto simp add: Derives1_def)

lemma Derives1_length: "Derives1 a i r b \<Longrightarrow> length b = length a + length (snd r) - 1"
  by (auto simp add: Derives1_def)

definition leftmost :: "nat \<Rightarrow> sentence \<Rightarrow> bool"
where
  "leftmost i s = (i < length s \<and> is_word (take i s) \<and> is_nonterminal (s ! i))" 

lemma set_take: "set (take n s) = { s ! i | i. i < n \<and> i < length s}"
proof (cases "n \<le> length s")
  case True thus ?thesis
  by (subst List.nth_image[symmetric], auto)
next
  case False thus ?thesis
    apply (subst set_conv_nth)
    by (metis less_trans linear not_le take_all)
qed
  
lemma list_all_take: "list_all P (take n s) = (\<forall> i. i < n \<and> i < length s \<longrightarrow> P (s ! i))"
  by (auto simp add: set_take list_all_iff)

lemma is_sentence_concat: "is_sentence (x@y) = (is_sentence x \<and> is_sentence y)"
  by (auto simp add: is_sentence_def)

lemma is_sentence_cons: "is_sentence (x#xs) = (is_symbol x \<and> is_sentence xs)"
  by (auto simp add: is_sentence_def)

lemma rule_nonterminal_type[simp]: "(N, \<alpha>) \<in> \<RR> \<Longrightarrow> is_nonterminal N"
  apply (insert validRules)
  by (auto simp add: is_nonterminal_def)

lemma rule_\<alpha>_type[simp]: "(N, \<alpha>) \<in> \<RR> \<Longrightarrow> is_sentence \<alpha>"
  apply (insert validRules)
  by (auto simp add: is_sentence_def is_symbol_def list_all_iff is_terminal_def is_nonterminal_def)

lemma [simp]: "is_nonterminal N \<Longrightarrow> is_symbol N"
  by (simp add: is_symbol_def)

lemma Derives1_sentence1[elim]: "Derives1 a i r b \<Longrightarrow> is_sentence a"
  by (auto simp add: Derives1_def is_sentence_cons is_sentence_concat)

lemma Derives1_sentence2[elim]: "Derives1 a i r b \<Longrightarrow> is_sentence b"
  by (auto simp add: Derives1_def is_sentence_cons is_sentence_concat)

lemma [elim]: "Derives1 a i r b \<Longrightarrow> r \<in> \<RR>"
  using Derives1_def by auto

lemma is_sentence_symbol: "is_sentence a \<Longrightarrow> i < length a \<Longrightarrow> is_symbol (a ! i)"
  by (simp add: is_sentence_def list_all_iff)

lemma is_symbol_distinct: "is_symbol x \<Longrightarrow> is_terminal x \<noteq> is_nonterminal x"
  apply (insert disjunct_symbols)
  apply (auto simp add: is_symbol_def is_terminal_def is_nonterminal_def)
  done

lemma is_terminal_nonterminal: "is_terminal x \<Longrightarrow> is_nonterminal x \<Longrightarrow> False"
  by (metis is_symbol_def is_symbol_distinct)

lemma Derives1_leftmost:
  assumes "Derives1 a i r b"
  shows "\<exists> j. leftmost j a \<and> j \<le> i"
proof -
  let ?J = "{j . j < length a \<and> is_nonterminal (a ! j)}"
  let ?M = "Min ?J"
  from assms have J1:"i \<in> ?J"
    apply (auto simp add: Derives1_def is_nonterminal_def)
    by (metis (mono_tags, lifting) prod.simps(2) validRules)
  have J2:"finite ?J" by auto
  note J = J1 J2
  from J have M1: "?M \<in> ?J" by (rule_tac Min_in, auto) 
  {
    fix j
    assume "j \<in> ?J"
    with J have "?M \<le> j" by auto
  }
  note M3 = this[OF J1]
  from assms have a_sentence: "is_sentence a" by (simp add: Derives1_sentence1)
  have is_word: "is_word (take ?M a)"
    apply (auto simp add: is_word_def list_all_take)
    proof -
      fix i
      assume i_less_M: "i < ?M"
      assume i_inbounds: "i < length a"
      show "is_terminal (a ! i)"
      proof(cases "is_terminal (a ! i)")
        case True thus ?thesis by auto
      next
        case False
        then have "is_nonterminal (a ! i)"
        using i_inbounds a_sentence is_sentence_symbol is_symbol_distinct by blast
        then have "i \<in> ?J" by (metis i_inbounds mem_Collect_eq) 
        then have "?M < i" by (metis J2 Min_le i_less_M leD) 
        then have "False" by (metis i_less_M less_asym') 
        then show ?thesis by auto
      qed
    qed  
  show ?thesis 
    apply (rule_tac exI[where x="?M"])
    apply (simp add: leftmost_def)
    by (metis (mono_tags, lifting) M1 M3 is_word mem_Collect_eq)
qed

lemma Derivation_leftmost: "D \<noteq> [] \<Longrightarrow> Derivation a D b \<Longrightarrow> \<exists> i. leftmost i a"
  apply (case_tac "D")
  apply (auto)
  apply (metis Derives1_leftmost)
  done

lemma nonword_has_nonterminal:
  "is_sentence a \<Longrightarrow>  \<not> (is_word a) \<Longrightarrow> \<exists> k. k < length a \<and> is_nonterminal (a ! k)"
  apply (auto simp add: is_sentence_def list_all_iff is_word_def)
  by (metis in_set_conv_nth is_symbol_distinct)

lemma leftmost_cons_nonterminal: 
  "is_nonterminal x \<Longrightarrow> leftmost 0 (x#xs)"
by (metis CFG.is_word_def CFG_axioms leftmost_def length_greater_0_conv list.distinct(1) 
    list_all_simps(2) nth_Cons_0 take_Cons')

lemma leftmost_cons_terminal: 
  "is_terminal x \<Longrightarrow> leftmost i (x#xs) = (i > 0 \<and> leftmost (i - 1) xs)"
by (metis Suc_diff_1 Suc_less_eq is_terminal_nonterminal is_word_def leftmost_def length_Cons 
    list_all_simps(1) not_gr0 nth_Cons' take_Cons')

lemma is_nonterminal_cons_terminal: 
  "is_terminal x \<Longrightarrow> k < length (x # a) \<Longrightarrow> is_nonterminal ((x # a) ! k) \<Longrightarrow>
   k > 0 \<and> k - 1 < length a \<and> is_nonterminal (a ! (k - 1))"
by (metis One_nat_def Suc_leI is_terminal_nonterminal less_diff_conv2 
    list.size(4) nth_non_equal_first_eq)

lemma leftmost_exists:
  "is_sentence a \<Longrightarrow> k < length a \<Longrightarrow> is_nonterminal (a ! k) \<Longrightarrow> 
   \<exists> i. leftmost i a \<and> i \<le> k" 
proof (induct a arbitrary: k)
  case Nil thus ?case by auto
next
  case (Cons x a) 
  show ?case
  proof(cases "is_nonterminal x")
    case True thus ?thesis
      apply(rule_tac exI[where x="0"])
      apply (simp add: leftmost_cons_nonterminal)
      done
  next
    case False
    then have x: "is_terminal x"
      by (metis Cons.prems(1) is_sentence_cons is_symbol_distinct)
    note k = is_nonterminal_cons_terminal[OF x Cons(3) Cons(4)]
    with Cons have "\<exists>i. leftmost i a \<and> i \<le> k - 1" by (metis is_sentence_cons)
    then show ?thesis
      apply (auto simp add: leftmost_cons_terminal[OF x])
      by (metis Nat.le_diff_conv2 Suc_leI add_Suc_right add_diff_cancel_right' k 
          le_0_eq le_imp_less_Suc nat_le_linear)
  qed
qed

lemma nonword_leftmost_exists: 
  "is_sentence a \<Longrightarrow> \<not> (is_word a) \<Longrightarrow> \<exists> i. leftmost i a"
  by (metis leftmost_exists nonword_has_nonterminal)
  
lemma leftmost_unaffected_Derives1: "leftmost j a \<Longrightarrow> j < i \<Longrightarrow> Derives1 a i r b \<Longrightarrow> leftmost j b"
apply (simp add: leftmost_def)
proof -
  assume a1: "j < length a \<and> is_word (take j a) \<and> is_nonterminal (a ! j)"
  assume a2: "j < i"
  assume "Derives1 a i r b"
  then have f3: "take i a = take i b"
    by (metis Derives1_take)
  have f4: "\<And>n ss ssa. take (length (take n (ss::symbol list))) (ssa::symbol list) = take (length ss) (take n ssa)"
    by (metis length_take take_take)
  have f5: "\<And>ss. take j (ss::symbol list) = take i (take j ss)"
    using a2 by (metis dual_order.strict_implies_order min.absorb2 take_take)
  have f6: "length (take j a) = j"
    using a1 by (metis dual_order.strict_implies_order length_take min.absorb2)
  then have f7: "\<And>n. min j n = length (take n (take j a))"
    by (metis length_take)
  have f8: "\<And>n ss. n = length (take n (ss::symbol list)) \<or> length ss < n"
    by (metis leI length_take min.absorb2)
  have f9: "\<And>ss. take j (ss::symbol list) = take j (take i ss)"
    using f7 f6 f5 by (metis take_take)
  have f10: "\<And>ss n. length (ss::symbol list) \<le> n \<or> length (take n ss) = n"
    using f8 by (metis dual_order.strict_implies_order)
  then have f11: "\<And>ss ssa. length (ss::symbol list) = length (take (length ss) (ssa::symbol list)) \<or> length (take (length ssa) ss) = length ssa"
    by (metis length_take min.absorb2)
  have f12: "\<And>ss ssa n. take (length (ss::symbol list)) (ssa::symbol list) = take n (take (length ss) ssa) \<or> length (take n ss) = n"
    using f10 by (metis min.absorb2 take_take)
  { assume "\<not> j < j"
    { assume "\<not> j < j \<and> i \<noteq> j"
      moreover
      { assume "length a \<noteq> j \<and> length (take i a) \<noteq> i"
        then have "\<exists>ss. length (take (length (take i (take (length a) (ss::symbol list)))) (take j ss)) \<noteq> length (take i (take (length a) ss))"
          using f12 f11 f6 f5 f4 by metis
        then have "\<exists>ss ssa. take (length (ss::symbol list)) (take j (ssa::symbol list)) \<noteq> take (length ss) (take i (take (length a) ssa))"
          using f11 by metis
        then have "length b \<noteq> j"
          using f9 f4 f3 by metis }
      ultimately have "length b \<noteq> j"
        using f7 f6 f5 f3 a1 by (metis length_take) }
    then have "length b = j \<longrightarrow> j < j"
      using a2 by metis }
  then have "j < length b"
    using f9 f8 f7 f6 f4 f3 by metis
  then show "j < length b \<and> is_word (take j b) \<and> is_nonterminal (b ! j)"
    using f9 f3 a2 a1 by (metis nth_take)
qed

definition derivation_ge :: "derivation \<Rightarrow> nat \<Rightarrow> bool"
where
  "derivation_ge D i = (\<forall> d \<in> set D. fst d \<ge> i)"

lemma derivation_ge_cons: "derivation_ge (d#D) i = (fst d \<ge> i \<and> derivation_ge D i)"
  by (auto simp add: derivation_ge_def)

lemma derivation_ge_append: 
  "derivation_ge (D@E) i = (derivation_ge D i \<and> derivation_ge E i)"
  by (auto simp add: derivation_ge_def)

lemma leftmost_unaffected_Derivation: 
  "derivation_ge D (Suc i) \<Longrightarrow> leftmost i a \<Longrightarrow> Derivation a D b \<Longrightarrow> leftmost i b"
proof (induct D arbitrary: a)
  case Nil thus ?case by auto
next
  case (Cons d D) 
  then have "\<exists> x. Derives1 a (fst d) (snd d) x \<and> Derivation x D b" by simp
  then obtain x where x1: "Derives1 a (fst d) (snd d) x" and x2: "Derivation x D b" by blast  
  with Cons have leftmost_x: "leftmost i x"
    apply (rule_tac leftmost_unaffected_Derives1[
           where a=a and j=i and b="x" and i="fst d" and r="snd d"])
    by (auto simp add: derivation_ge_def)
  with Cons x2 show ?case by (auto simp add: derivation_ge_def)
qed

lemma le_Derives1_take: 
  assumes le: "i \<le> j" 
  and D: "Derives1 a j r b"
  shows "take i a = take i b"
proof -
  note Derives1_take[where a=a and i=j and r=r and b=b]
  with le D show ?thesis by (rule_tac le_take_same[where i=i and j=j], auto)
qed  

lemma Derivation_take: "derivation_ge D i \<Longrightarrow> Derivation a D b \<Longrightarrow> take i a = take i b"
proof(induct D arbitrary: a b)
  case Nil thus ?case by auto
next
  case (Cons d D)
  then have "\<exists> x. Derives1 a (fst d) (snd d) x \<and> Derivation x D b"
    by simp
  then obtain x where ax: "Derives1 a (fst d) (snd d) x" and xb: "Derivation x D b" by blast  
  from derivation_ge_cons Cons(2) have d: "i \<le> fst d" and D: "derivation_ge D i" by auto
  note take_i_xb = Cons(1)[OF D xb]
  note take_i_ax = le_Derives1_take[OF d ax]
  from take_i_xb take_i_ax show ?case by auto
qed

lemma leftmost_cons_less: "i < length u \<Longrightarrow> leftmost i (u@v) = leftmost i u"
  by (auto simp add: leftmost_def nth_append)

lemma leftmost_is_nonterminal: "leftmost i u \<Longrightarrow> is_nonterminal (u ! i)"
  by (metis leftmost_def)

lemma is_word_is_terminal: "i < length u \<Longrightarrow> is_word u \<Longrightarrow> is_terminal (u ! i)"
  by (metis is_word_def list_all_length)
  
lemma leftmost_append: 
  assumes leftmost: "leftmost i (u@v)"
  and is_word: "is_word u"
  shows "length u \<le> i"
proof (cases "i < length u")
  case False thus ?thesis by auto
next
  case True 
  with leftmost have "leftmost i u" using leftmost_cons_less[OF True] by simp
  then have is_nonterminal: "is_nonterminal (u ! i)" by (rule leftmost_is_nonterminal)
  note is_terminal = is_word_is_terminal[OF True is_word]
  note is_terminal_nonterminal[OF is_terminal is_nonterminal]
  then show ?thesis by auto
qed

lemma derivation_ge_empty[simp]: "derivation_ge [] i" 
by (simp add: derivation_ge_def)

lemma leftmost_notword: "leftmost i a \<Longrightarrow> j > i \<Longrightarrow> \<not> (is_word (take j a))"
by (metis is_terminal_nonterminal is_word_def leftmost_def list_all_take)

lemma leftmost_unique: "leftmost i a \<Longrightarrow> leftmost j a \<Longrightarrow> i = j" 
by (metis leftmost_def leftmost_notword linorder_neqE_nat)

lemma leftmost_Derives1: "leftmost i a \<Longrightarrow> Derives1 a j r b \<Longrightarrow> i \<le> j"
by (metis Derives1_leftmost leftmost_unique)

lemma leftmost_Derives1_propagate: 
  assumes leftmost: "leftmost i a"
      and Derives1: "Derives1 a j r b"
    shows "(is_word b \<and> i = j) \<or> (\<exists> k. leftmost k b \<and> i \<le> k)"
proof -
  from leftmost_Derives1[OF leftmost Derives1] have ij: "i \<le> j" by auto
  show ?thesis
  proof (cases "is_word b")
    case True show ?thesis
      by (metis Derives1 True ij le_neq_implies_less leftmost 
          leftmost_unaffected_Derives1 order_refl)
  next
    case False show ?thesis
      by (metis (no_types, hide_lams) Derives1 Derives1_bound Derives1_sentence2 
          Derives1_take append_take_drop_id ij le_neq_implies_less leftmost 
          leftmost_append leftmost_cons_less leftmost_def length_take 
          min.absorb2 nat_le_linear nonword_leftmost_exists not_le)
  qed
qed

lemma is_word_Derives1[elim]: "is_word a \<Longrightarrow> Derives1 a i r b \<Longrightarrow> False"
by (metis Derives1_leftmost is_terminal_nonterminal is_word_is_terminal leftmost_def)
  
lemma is_word_Derivation[elim]: "is_word a \<Longrightarrow> Derivation a D b \<Longrightarrow> D = []"
by (metis Derivation_leftmost is_terminal_nonterminal is_word_def 
    leftmost_def list_all_length)
 
lemma leftmost_Derivation: 
  "leftmost i a \<Longrightarrow> Derivation a D b \<Longrightarrow> j \<le> i \<Longrightarrow> derivation_ge D j"
proof (induct D arbitrary: a b i j)
  case Nil thus ?case by auto
next
  case (Cons d D)
  then have "\<exists> x. Derives1 a (fst d) (snd d) x \<and> Derivation x D b" by auto
  then obtain x where ax:"Derives1 a (fst d) (snd d) x" and xb:"Derivation x D b" by blast
  note ji = Cons(4)
  note i_fstd = leftmost_Derives1[OF Cons(2) ax]
  note disj = leftmost_Derives1_propagate[OF Cons(2) ax]
  thus ?case
  proof(induct rule: disjCases2)
    case 1 
    with xb have "D = []" by auto
    with 1 ji show ?case by (simp add: derivation_ge_def)
  next
    case 2 
    then obtain k where k: "leftmost k x" and ik: "i \<le> k" by blast
    note ge = Cons(1)[OF k xb, where j=j]
    from ji ik i_fstd ge show ?case
      by (simp add: derivation_ge_cons)
  qed
qed

lemma derivation_ge_list_all: "derivation_ge D i = list_all (\<lambda> d. fst d \<ge> i) D"
by (simp add: Ball_set derivation_ge_def)

lemma split_derivation_leftmost:
  assumes "derivation_ge D i"
  and "\<not> (derivation_ge D (Suc i))"
  shows "\<exists> E F r. D = E@[(i, r)]@F \<and> derivation_ge E (Suc i)"
proof -
  from assms have "\<exists> k. k < length D \<and> fst(D ! k) \<ge> i \<and> \<not>(fst(D ! k) \<ge> Suc i)"
    by (metis derivation_ge_def in_set_conv_nth)
  then have "\<exists> k. k < length D \<and> fst(D ! k) = i" by auto
  then show ?thesis
  proof(induct rule: ex_minimal_witness)
    case (Minimal k)
      then have k_len: "k < length D" and k_i: "fst (D ! k) = i" by auto
      let ?E = "take k D"
      let ?r = "snd (D ! k)"
      let ?F = "drop (Suc k) D"
      note split = split_list_at[OF k_len]
      from k_i have D_k: "D ! k = (i, ?r)" by auto
      show ?case
        apply (rule exI[where x="?E"])
        apply (rule exI[where x="?F"])
        apply (rule exI[where x="?r"])
        apply (subst D_k[symmetric])
        apply (rule conjI)
        apply (rule split)
        by (metis (mono_tags, lifting) Minimal.hyps(2) Suc_leI assms(1) 
            derivation_ge_list_all le_neq_implies_less list_all_length list_all_take)
  qed
qed

lemma Derives1_Derives1_swap:
  assumes "i < j"
  and "Derives1 a j p b"
  and "Derives1 b i q c"
  shows "\<exists> b'. Derives1 a i q b' \<and> Derives1 b' (j - 1 + length (snd q)) p c"
proof -
  from Derives1_split[OF assms(2)] obtain a1 a2 where
    a_src: "a = a1 @ [fst p] @ a2" and a_dest: "b = a1 @ snd p @ a2" 
    and a1_len: "length a1 = j" by blast
  note a = this
  from a have is_sentence_a1: "is_sentence a1"
    using Derives1_sentence2 assms(2) is_sentence_concat by blast
  from a have is_sentence_a2: "is_sentence a2"
    using Derives1_sentence2 assms(2) is_sentence_concat by blast
  from a have is_symbol_fst_p:  "is_symbol (fst p)"
    by (metis Derives1_sentence1 assms(2) is_sentence_concat is_sentence_cons)
  from Derives1_split[OF assms(3)] obtain b1 b2 where
    b_src: "b = b1 @ [fst q] @ b2" and b_dest: "c = b1 @ snd q @ b2" 
    and b1_len: "length b1 = i" by blast
  have a_take_j: "a1 = take j a" by (metis a1_len a_src append_eq_conv_conj) 
  have b_take_i: "b1 @ [fst q] = take (Suc i) b"
    by (metis append_assoc append_eq_conv_conj b1_len b_src length_append_singleton) 
  from a_take_j b_take_i  take_eq_take_append[where j=j and i="Suc i" and a=a]
  have "\<exists> u. a1 = (b1 @ [fst q]) @ u"
    by (metis le_iff_add Suc_leI a1_len a_dest append_eq_conv_conj assms(1) take_add) 
  then obtain u where u1: "a1 = (b1 @ [fst q]) @ u" by blast
  then have j_i_u: "j = i + 1 + length u"
    using Suc_eq_plus1 a1_len b1_len length_append length_append_singleton by auto
  from u1 is_sentence_a1 have is_sentence_b1_u: "is_sentence b1 \<and> is_sentence u"
    using is_sentence_concat by blast    
  have u2: "b2 = u @ snd p @ a2" by (metis a_dest append_assoc b_src same_append_eq u1) 
  let ?b = "b1 @ (snd q) @ u @ [fst p] @ a2"
  from assms have q_dom: "q \<in> \<RR>" by auto
  have a_b': "Derives1 a i q ?b"
    apply (subst Derives1_def)
    apply (rule exI[where x="b1"])
    apply (rule exI[where x="u@[fst p]@a2"])
    apply (rule exI[where x="fst q"])
    apply (rule exI[where x="snd q"])
    apply (auto simp add: b1_len is_sentence_cons is_sentence_concat
           is_sentence_a2 is_symbol_fst_p is_sentence_b1_u a_src u1 q_dom)
    done
  from assms have p_dom: "p \<in> \<RR>" by auto
  have is_sentence_snd_q: "is_sentence (snd q)" 
    using Derives1_sentence2 a_b' is_sentence_concat by blast
  have b'_c: "Derives1 ?b (j - 1 + length (snd q)) p c"
    apply (subst Derives1_def)
    apply (rule exI[where x="b1 @ (snd q) @ u"])
    apply (rule exI[where x="a2"])
    apply (rule exI[where x="fst p"])
    apply (rule exI[where x="snd p"])
    apply (auto simp add: is_sentence_concat is_sentence_b1_u is_sentence_a2 p_dom
           is_sentence_snd_q b_dest u2 b1_len j_i_u)
    done
  show ?thesis
    apply (rule exI[where x="?b"])
    apply (rule conjI)
    apply (rule a_b')
    apply (rule b'_c)
    done
qed

definition derivation_shift :: "derivation \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> derivation"
where
  "derivation_shift D left right = map (\<lambda> d. (fst d - left + right, snd d)) D"

lemma derivation_shift_empty[simp]: "derivation_shift [] left right = []" 
  by (auto simp add: derivation_shift_def)

lemma derivation_shift_cons[simp]:
  "derivation_shift (d#D) left right = ((fst d - left + right, snd d)#(derivation_shift D left right))"
by (simp add: derivation_shift_def)

lemma Derivation_append: "Derivation a (D@E) c = (\<exists> b. Derivation a D b \<and> Derivation b E c)"
proof(induct D arbitrary: a c E)
  case Nil thus ?case by auto
next
  case (Cons d D) thus ?case by auto
qed

lemma Derivation_implies_append: 
  "Derivation a D b \<Longrightarrow> Derivation b E c \<Longrightarrow> Derivation a (D@E) c"
using Derivation_append by blast

lemma Derivation_swap_single_end_to_front: 
  "i < j \<Longrightarrow> derivation_ge D j \<Longrightarrow> Derivation a (D@[(i,r)]) b \<Longrightarrow>
   Derivation a ((i,r)#(derivation_shift D 1 (length (snd r)))) b"
proof(induct D arbitrary: a)
  case Nil thus ?case by auto
next
  case (Cons d D) 
  from Cons have "\<exists> c. Derives1 a (fst d) (snd d) c \<and> Derivation c (D @ [(i, r)]) b"
    by simp
  then obtain c where ac: "Derives1 a (fst d) (snd d) c"
    and cb: "Derivation c (D @ [(i, r)]) b" by blast
  from Cons(3) have D_j: "derivation_ge D j" by (simp add: derivation_ge_cons)
  from Cons(1)[OF Cons(2) D_j cb, simplified]
  obtain x where cx: "Derives1 c i r x" and  
    xb: "Derivation x (derivation_shift D 1 (length (snd r))) b" by auto
  have i_fst_d: "i < fst d" using Cons derivation_ge_cons by auto
  from Derives1_Derives1_swap[OF i_fst_d ac cx]
  obtain b' where ab': "Derives1 a i r b'" and 
    b'x: "Derives1 b' (fst d - 1 + length (snd r)) (snd d) x" by blast
  show ?case using ab' b'x xb by auto
qed    

lemma Derivation_swap_single_mid_to_front: 
  assumes "i < j"
  and "derivation_ge D j" 
  and "Derivation a (D@[(i,r)]@E) b"
  shows "Derivation a ((i,r)#((derivation_shift D 1 (length (snd r)))@E)) b"
proof -
  from assms have "\<exists> x. Derivation a (D@[(i, r)]) x \<and> Derivation x E b"
    using Derivation_append by auto
  then obtain x where ax: "Derivation a (D@[(i, r)]) x" and xb: "Derivation x E b"
    by blast
  with assms have "Derivation a ((i, r)#(derivation_shift D 1 (length (snd r)))) x"
    using Derivation_swap_single_end_to_front by blast
  then show ?thesis using Derivation_append xb by auto
qed

lemma length_derivation_shift[simp]: 
  "length(derivation_shift D left right) = length D"
  by (simp add: derivation_shift_def)

definition LeftDerives1 :: "sentence \<Rightarrow> nat \<Rightarrow> rule \<Rightarrow> sentence \<Rightarrow> bool"
where 
  "LeftDerives1 u i r v = (leftmost i u \<and> Derives1 u i r v)"

lemma LeftDerives1_implies_leftderives1: "LeftDerives1 u i r v \<Longrightarrow> leftderives1 u v"
by (metis Derives1_def LeftDerives1_def append_eq_conv_conj leftderives1_def 
    leftmost_def)
    
lemma leftmost_Derives1_leftderives: 
  "leftmost i a \<Longrightarrow> Derives1 a i r b \<Longrightarrow> leftderives b c \<Longrightarrow> leftderives a c"
using LeftDerives1_def LeftDerives1_implies_leftderives1 
  leftderives1_implies_leftderives leftderives_trans by blast

theorem Derivation_implies_leftderives_gen:
  "Derivation a D (u@v) \<Longrightarrow> is_word u \<Longrightarrow> (\<exists> w. 
          leftderives a (u@w) \<and> 
          (v = [] \<longrightarrow> w = []) \<and> 
          (\<forall> X. is_first X v \<longrightarrow> is_first X w))"
proof (induct "length D" arbitrary: D a u v)
  case 0
    then have "a = u@v" by auto
    thus ?case by (rule_tac x = v in exI, auto)
next
  case (Suc n)
    from Suc have "D \<noteq> []" by auto
    with Suc Derivation_leftmost have "\<exists> i. leftmost i a" by auto
    then obtain i where i: "leftmost i a" by blast
    show "?case"
    proof (cases "derivation_ge D (Suc i)")
      case True
        with Suc have leftmost: "leftmost i (u@v)" 
          by (rule_tac leftmost_unaffected_Derivation[OF True i], auto)
        have length_u: "length u \<le> i" 
          using leftmost_append[OF leftmost Suc(4)] .
        have take_Suc: "take (Suc i) a = take (Suc i) (u@v)" 
          using  Derivation_take[OF True Suc(3)] .
        with length_u have is_prefix_u: "is_prefix u a"
          by (metis append_assoc append_take_drop_id dual_order.strict_implies_order 
              is_prefix_def le_imp_less_Suc take_all take_append)  
        have a: "u @ drop (length u) a = a" 
          using is_prefix_unsplit[OF is_prefix_u] .
        from take_Suc have length_take_Suc: "length (take (Suc i) a) = Suc i"
          by (metis Suc_leI i leftmost_def length_take min.absorb2)
        have v: "v \<noteq> []"
        proof(cases "v = []")
          case False thus ?thesis by auto
        next
          case True
          with length_u have right: "length(take (Suc i) (u@v)) = length u" by simp
          note left = length_take_Suc
          from left right take_Suc have "Suc i = length u" by auto
          with length_u show ?thesis by auto
        qed
        then have "\<exists> X w. v = X#w" by (cases v, auto)
        then obtain X w where v: "v = X#w" by blast
        have is_first_X: "is_first X (drop (length u) a)"
          apply (rule_tac is_first_drop_length[where v=v and w=w and k="Suc i"])
          apply (simp_all add: take_Suc v)
          apply (metis Suc_leI i leftmost_def)
          apply (insert length_u)
          apply arith
          done
        show ?thesis
          apply (rule exI[where x="drop (length u) a"])
          by (simp add: a v is_first_cons is_first_X)
    next
      case False
      have Di: "derivation_ge D i" 
      using leftmost_Derivation[OF i Suc(3), where j=i, simplified] .
      from split_derivation_leftmost[OF Di False]
      obtain E F r where D_split: "D = E @ [(i, r)] @ F" 
        and E_Suc: "derivation_ge E (Suc i)" by auto
      let ?D = "(derivation_shift E 1 (length (snd r)))@F"
      from D_split 
      have "Derivation a ((i,r) # ?D) (u @ v)"
        using Derivation_swap_single_mid_to_front E_Suc Suc.prems(1) lessI by blast
      then have "\<exists> y. Derives1 a i r y \<and> Derivation y ?D (u @ v)" by simp
      then obtain y where ay:"Derives1 a i r y" 
        and yuv: "Derivation y ?D (u @ v)" by blast
      have length_D': "length ?D = n" using D_split Suc.hyps(2) by auto
      from Suc(1)[OF length_D'[symmetric] yuv Suc(4)] 
      obtain w where "leftderives y (u @ w)" and "(v = [] \<longrightarrow> w = [])" 
        and "\<forall>X. is_first X v \<longrightarrow> is_first X w" by blast 
      then show ?thesis using ay i leftmost_Derives1_leftderives by blast
    qed    
qed   

lemma derives_implies_leftderives_gen: "derives a (u@v) \<Longrightarrow> is_word u \<Longrightarrow> (\<exists> w. 
          leftderives a (u@w) \<and> 
          (v = [] \<longrightarrow> w = []) \<and> 
          (\<forall> X. is_first X v \<longrightarrow> is_first X w))"
using Derivation_implies_leftderives_gen derives_implies_Derivation by blast

lemma derives_implies_leftderives: "derives a b \<Longrightarrow> is_word b \<Longrightarrow> leftderives a b"
using derives_implies_leftderives_gen by force

fun LeftDerivation :: "sentence \<Rightarrow> derivation \<Rightarrow> sentence \<Rightarrow> bool"
where
  "LeftDerivation a [] b = (a = b)"
| "LeftDerivation a (d#D) b = (\<exists> x. LeftDerives1 a (fst d) (snd d) x \<and> LeftDerivation x D b)"
  
lemma LeftDerives1_implies_Derives1: "LeftDerives1 a i r b \<Longrightarrow> Derives1 a i r b"
by (metis LeftDerives1_def)

lemma LeftDerivation_implies_Derivation:
  "LeftDerivation a D b \<Longrightarrow> Derivation a D b"
proof (induct D arbitrary: a)
  case (Nil) thus ?case by simp
next
  case (Cons d D)
  thus ?case
  using CFG.LeftDerivation.simps(2) CFG_axioms Derivation.simps(2) 
    LeftDerives1_implies_Derives1 by blast 
qed

lemma LeftDerivation_implies_leftderives: "LeftDerivation a D b \<Longrightarrow> leftderives a b"
proof (induct D arbitrary: a b)
  case Nil thus ?case by simp
next
  case (Cons d D)
    note ihyps = this
    from ihyps have "\<exists> x. LeftDerives1 a (fst d) (snd d) x \<and> LeftDerivation x D b" by auto
    then obtain x where "LeftDerives1 a (fst d) (snd d) x" and xb: "LeftDerivation x D b" by blast
    with LeftDerives1_implies_leftderives1 have d1: "leftderives a x" by auto
    from ihyps xb have d2:"leftderives x b" by simp
    show "leftderives a b" by (rule leftderives_trans[OF d1 d2])
qed 

lemma leftmost_witness[simp]: "leftmost (length x) (x@(N#y)) = (is_word x \<and> is_nonterminal N)"
  by (auto simp add: leftmost_def)

lemma leftderives1_implies_LeftDerives1: 
  assumes leftderives1: "leftderives1 u v"
  shows "\<exists> i r. LeftDerives1 u i r v"
proof -
  from leftderives1 have 
    "\<exists>x y N \<alpha>. u = x @ [N] @ y \<and> v = x @ \<alpha> @ y \<and> is_word x \<and> is_sentence y \<and> (N, \<alpha>) \<in> \<RR>"
    by (simp add: leftderives1_def)
  then obtain x y N \<alpha> where 
    u:"u = x @ [N] @ y" and
    v:"v = x @ \<alpha> @ y" and
    x:"is_word x" and  
    y:"is_sentence y" and 
    r:"(N, \<alpha>) \<in> \<RR>"
    by blast
  show ?thesis
    apply (rule_tac x="length x" in exI)
    apply (rule_tac x="(N, \<alpha>)" in exI)
    apply (auto simp add: LeftDerives1_def)
    apply (simp add: leftmost_def x u rule_nonterminal_type[OF r])
    apply (simp add: Derives1_def u v)
    apply (rule_tac x=x in exI)
    apply (rule_tac x=y in exI)
    apply (auto simp add: x y r)
    done
qed    

lemma LeftDerivation_LeftDerives1: 
  "LeftDerivation a S y \<Longrightarrow> LeftDerives1 y i r z \<Longrightarrow> LeftDerivation a (S@[(i,r)]) z"
proof (induct S arbitrary: a y z i r)
  case Nil thus ?case by simp
next
  case (Cons s S) thus ?case 
    by (metis LeftDerivation.simps(2) append_Cons) 
qed

lemma leftderives_implies_LeftDerivation: "leftderives a b \<Longrightarrow> \<exists> D. LeftDerivation a D b"
proof (induct rule: leftderives_induct)
  case Base
  show ?case by (rule exI[where x="[]"], simp)
next
  case (Step y z)
  note ihyps = this
  from ihyps obtain D where ay: "LeftDerivation a D y" by blast
  from ihyps leftderives1_implies_LeftDerives1 obtain i r where yz: "LeftDerives1 y i r z" by blast
  from LeftDerivation_LeftDerives1[OF ay yz] show ?case by auto
qed

lemma LeftDerivation_append: 
  "LeftDerivation a (D@E) c = (\<exists> b. LeftDerivation a D b \<and> LeftDerivation b E c)"
proof(induct D arbitrary: a c E)
  case Nil thus ?case by auto
next
  case (Cons d D) thus ?case by auto
qed

lemma LeftDerivation_implies_append: 
  "LeftDerivation a D b \<Longrightarrow> LeftDerivation b E c \<Longrightarrow> LeftDerivation a (D@E) c"
using LeftDerivation_append by blast

lemma Derivation_unique_dest: "Derivation a D b \<Longrightarrow> Derivation a D c \<Longrightarrow> b = c"
  apply (induct D arbitrary: a b c)
  apply auto
  using Derives1_unique_dest by blast

lemma Derivation_unique_src: "Derivation a D c \<Longrightarrow> Derivation b D c \<Longrightarrow> a = b"
  apply (induct D arbitrary: a b c)
  apply auto
  using Derives1_unique_src by blast

lemma LeftDerives1_unique: "LeftDerives1 a i r b \<Longrightarrow> LeftDerives1 a j s b \<Longrightarrow> i = j \<and> r = s"
using Derives1_def LeftDerives1_def leftmost_unique by auto
 
lemma leftlang: "\<L> = { v | v. is_word v \<and> is_leftderivation v }"
by (metis (no_types, lifting) CFG.is_derivation_def CFG.is_leftderivation_def 
    CFG.leftderivation_implies_derivation CFG_axioms Collect_cong 
    \<L>_def derives_implies_leftderives)
  
lemma leftprefixlang:  "\<L>\<^sub>P = { u | u v. is_word u \<and> is_leftderivation (u@v) }"
apply (auto simp add: \<L>\<^sub>P_def)
using derives_implies_leftderives_gen is_derivation_def is_leftderivation_def apply blast
using leftderivation_implies_derivation by blast

lemma derives_implies_leftderives_cons:
  "is_word a \<Longrightarrow> derives u (a@X#b) \<Longrightarrow> \<exists> c. leftderives u  (a@X#c)"
by (metis append_Cons append_Nil derives_implies_leftderives_gen is_first_def) 

lemma is_word_append[simp]: "is_word (a@b) = (is_word a \<and> is_word b)"
  by (auto simp add: is_word_def)

lemma \<L>\<^sub>P_split: "a@b \<in> \<L>\<^sub>P \<Longrightarrow> a \<in> \<L>\<^sub>P"
  by (auto simp add: \<L>\<^sub>P_def)

lemma \<L>\<^sub>P_is_word: "a \<in> \<L>\<^sub>P \<Longrightarrow> is_word a"
  by (metis (no_types, lifting) leftprefixlang mem_Collect_eq)

definition Derive :: "sentence \<Rightarrow> derivation \<Rightarrow> sentence"
where 
  "Derive a D = (THE b. Derivation a D b)"

lemma Derivation_dest_ex_unique: "Derivation a D b \<Longrightarrow> \<exists>! x. Derivation a D x"
using CFG.Derivation_unique_dest CFG_axioms by blast

lemma Derive:
  assumes ab: "Derivation a D b"
  shows "Derive a D = b"
proof -
  note the1_equality[OF Derivation_dest_ex_unique[OF ab] ab]
  thus ?thesis by (simp add: Derive_def)
qed

end

end

