theory Validity 
imports LLEarleyParsing Derivations
begin

context LocalLexing begin

definition wellformed_token :: "token \<Rightarrow> bool"
where
  "wellformed_token t = is_terminal (terminal_of_token t)"

definition wellformed_tokens :: "tokens \<Rightarrow> bool"
where
  "wellformed_tokens ts = list_all wellformed_token ts"

definition doc_tokens :: "tokens \<Rightarrow> bool"
where
  "doc_tokens p = (wellformed_tokens p \<and> is_prefix (chars p) Doc)"

definition wellformed_item :: "item \<Rightarrow> bool"
where 
  "wellformed_item x = (
    item_rule x \<in> \<RR> \<and> 
    item_origin x \<le> item_end x \<and> 
    item_end x \<le> length Doc \<and>
    item_dot x \<le> length (item_rhs x))"

definition wellformed_items :: "items \<Rightarrow> bool"
where
  "wellformed_items X = (\<forall> x \<in> X. wellformed_item x)"

lemma is_word_terminals: "wellformed_tokens p \<Longrightarrow> is_word (terminals p)"
by (simp add: is_word_def list_all_length terminals_def wellformed_token_def wellformed_tokens_def)

lemma is_word_subset: "is_word x \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> is_word y"
by (metis (mono_tags, hide_lams) in_set_conv_nth is_word_def list_all_length subsetCE)
 
lemma is_word_terminals_take: "wellformed_tokens p \<Longrightarrow> is_word(terminals (take n p))"
by (metis append_take_drop_id is_word_terminals list_all_append wellformed_tokens_def)

lemma is_word_terminals_drop: "wellformed_tokens p \<Longrightarrow> is_word(terminals (drop n p))"
by (metis append_take_drop_id is_word_terminals list_all_append wellformed_tokens_def)

definition pvalid :: "tokens \<Rightarrow> item \<Rightarrow> bool"
where
  "pvalid p x = (\<exists> u \<gamma>.
     wellformed_tokens p \<and>
     wellformed_item x \<and>
     u \<le> length p \<and>
     charslength p = item_end x \<and>
     charslength (take u p) = item_origin x \<and>
     is_derivation (terminals (take u p) @ [item_nonterminal x] @ \<gamma>) \<and>
     derives (item_\<alpha> x) (terminals (drop u p)))"

definition Gen :: "tokens set \<Rightarrow> items"
where
  "Gen P = { x | x p. p \<in> P \<and> pvalid p x }"

lemma "wellformed_items (Gen P)"
  by (auto simp add: Gen_def pvalid_def wellformed_items_def)

lemma "wellformed_items (Init)"
  by (auto simp add: wellformed_items_def Init_def init_item_def wellformed_item_def)

definition pvalid_left :: "tokens \<Rightarrow> item \<Rightarrow> bool"
where
  "pvalid_left p x = (\<exists> u \<gamma>.
     wellformed_tokens p \<and>
     wellformed_item x \<and>
     u \<le> length p \<and>
     charslength p = item_end x \<and>
     charslength (take u p) = item_origin x \<and>
     is_leftderivation (terminals (take u p) @ [item_nonterminal x] @ \<gamma>) \<and>
     leftderives (item_\<alpha> x) (terminals (drop u p)))"

lemma pvalid_left: "pvalid p x = pvalid_left p x"
proof -
  have right_imp_left: "pvalid_left p x \<Longrightarrow> pvalid p x"
    by (meson CFG.leftderives_implies_derives CFG_axioms LocalLexing.pvalid_def 
        LocalLexing.pvalid_left_def LocalLexing_axioms leftderivation_implies_derivation)
  have left_imp_right: "pvalid p x \<Longrightarrow> pvalid_left p x"
  proof -
    assume "pvalid p x"
    then obtain u \<gamma> where 
      "wellformed_tokens p \<and>
       wellformed_item x \<and>
       u \<le> length p \<and>
       charslength p = item_end x \<and>
       charslength (take u p) = item_origin x \<and>
       is_derivation (terminals (take u p) @ [item_nonterminal x] @ \<gamma>) \<and>
       derives (item_\<alpha> x) (terminals (drop u p))" by (simp add: pvalid_def, blast)
    thus ?thesis
      apply (auto simp add: pvalid_left_def)
      apply (rule_tac x=u in exI)
      apply auto
      apply (simp add: is_leftderivation_def)
      apply (rule_tac derives_implies_leftderives_cons[where b=\<gamma>])
      apply (erule is_word_terminals_take)
      apply (simp add: is_derivation_def)
      by (metis derives_implies_leftderives is_word_terminals_drop)
  qed
  show ?thesis by (metis left_imp_right right_imp_left)
qed
  
lemma \<L>\<^sub>P_wellformed_tokens: "terminals p \<in> \<L>\<^sub>P \<Longrightarrow> wellformed_tokens p"
by (metis (mono_tags, lifting) \<L>\<^sub>P_is_word is_word_def length_map list_all_length 
    nth_map terminals_def wellformed_token_def wellformed_tokens_def)

end

end
