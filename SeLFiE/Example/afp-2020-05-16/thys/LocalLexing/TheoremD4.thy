theory TheoremD4
imports TheoremD2
begin

context LocalLexing begin

lemma \<X>_are_terminals: "u \<in> \<X> k \<Longrightarrow> is_terminal (terminal_of_token u)"
  by (auto simp add: \<X>_def is_terminal_def terminal_of_token_def)

lemma terminals_append[simp]: "terminals (a@b) = ((terminals a) @ (terminals b))"
  by (auto simp add: terminals_def)

lemma terminals_singleton[simp]: "terminals [u] = [terminal_of_token u]"
  by (simp add: terminals_def)

lemma terminal_of_token_simp[simp]: "terminal_of_token (a, b) = a"
  by (simp add: terminal_of_token_def)

lemma pvalid_item_end: "pvalid p x \<Longrightarrow> item_end x = charslength p"
  by (metis pvalid_def)

lemma \<W>_elem_in_TokensAt: 
  assumes P: "P \<subseteq> \<PP>"
  assumes u_in_\<W>: "u \<in> \<W> P k"
  shows "u \<in> TokensAt k (Gen P)"
proof -
  have u: "u \<in> \<X> k \<and> (\<exists>p\<in>by_length k P. admissible (p @ [u]))" using u_in_\<W>
    by (auto simp add: \<W>_def)
  then obtain p where p: "p \<in> by_length k P \<and> admissible (p @ [u])" by blast 
  then have charslength_p: "charslength p = k"
    by (metis (mono_tags, lifting) by_length.simps charslength.simps mem_Collect_eq)   
  from u have u: "u \<in> \<X> k" by blast
  from p have p_in_\<PP>: "p \<in> \<PP>"
    by (metis (no_types, lifting) P by_length.simps mem_Collect_eq subsetCE)
  then have doc_tokens_p: "doc_tokens p" by (metis \<PP>_are_doc_tokens)
  let ?X = "terminal_of_token u"
  have X_is_terminal: "is_terminal ?X" by (metis \<X>_are_terminals u) 
  from p have "terminals p @ [terminal_of_token u] \<in> \<L>\<^sub>P"
    by (auto simp add: admissible_def)
  from thmD2[OF X_is_terminal p_in_\<PP> this] obtain x where
    x: "pvalid p x \<and> next_symbol x = Some (terminal_of_token u)" by blast
  have x_is_in_Gen_P: "x \<in> Gen P"
    by (metis (mono_tags, lifting) Gen_def by_length.simps mem_Collect_eq p x)
  have u_split[dest!]: "\<And> t s. u = (t, s) \<Longrightarrow> t = terminal_of_token u \<and> s = chars_of_token u"
    by (metis chars_of_token_simp fst_conv terminal_of_token_def)
  show ?thesis
    apply (auto simp add: TokensAt_def bin_def)
    apply (rule_tac x=x in exI)
    apply (auto simp add: x_is_in_Gen_P x X_is_terminal)
    using x charslength_p pvalid_item_end apply (simp, blast)
    using u by (auto simp add: \<X>_def)
qed

lemma is_derivation_is_sentence: "is_derivation s \<Longrightarrow> is_sentence s"
by (metis (no_types, lifting) Derives1_sentence2 derives1_implies_Derives1 
    derives_induct is_derivation_def is_nonterminal_startsymbol is_sentence_cons 
    is_sentence_def is_symbol_def list.pred_inject(1))
  
lemma is_sentence_cons: "is_sentence (N#s) = (is_symbol N \<and> is_sentence s)"
  by (auto simp add: is_sentence_def)

lemma is_derivation_step:
  assumes uNv: "is_derivation (u@[N]@v)"
  assumes N\<alpha>: "(N, \<alpha>) \<in> \<RR>"
  shows "is_derivation (u@\<alpha>@v)"
proof -
  from uNv have "is_sentence (u@[N]@v)" by (metis is_derivation_is_sentence) 
  with is_sentence_concat is_sentence_cons 
  have u_is_sentence: "is_sentence u" and v_is_sentence: "is_sentence v"
    by auto
  from N\<alpha> have "derives1 (u@[N]@v) (u@\<alpha>@v)"
    apply (auto simp add: derives1_def)
    apply (rule_tac x=u in exI)
    apply (rule_tac x=v in exI)
    apply (rule_tac x=N in exI)
    by (auto simp add: u_is_sentence v_is_sentence)
  then show ?thesis
    by (metis derives1_implies_derives derives_trans is_derivation_def uNv)
qed  

lemma is_derivation_derives:
  "derives \<alpha> \<beta> \<Longrightarrow> is_derivation (u@\<alpha>@v) \<Longrightarrow> is_derivation (u@\<beta>@v)"
proof (induct rule: derives_induct)
  case Base thus ?case by simp
next
  case (Step y z)
    from Step have 1: "is_derivation (u @ y @ v)" by auto
    from Step have 2: "derives1 y z" by auto
    from 1 2 show ?case by (metis append_assoc derives1_def is_derivation_step)
qed  

lemma item_rhs_split: "item_rhs x = (item_\<alpha> x)@(item_\<beta> x)"
  by (metis append_take_drop_id item_\<alpha>_def item_\<beta>_def)

lemma pvalid_is_derivation_terminals_item_\<beta>:
  assumes pvalid: "pvalid p x"
  shows "\<exists> \<delta>. is_derivation ((terminals p)@(item_\<beta> x)@\<delta>)"
proof -
  from pvalid have "\<exists> u \<gamma>. is_derivation (terminals (take u p) @ [item_nonterminal x] @ \<gamma>) \<and>
    derives (item_\<alpha> x) (terminals (drop u p))"
    by (auto simp add: pvalid_def)  
  then obtain u \<gamma> where 1: "is_derivation (terminals (take u p) @ [item_nonterminal x] @ \<gamma>) \<and>
    derives (item_\<alpha> x) (terminals (drop u p))" by blast
  have x_rule: "(item_nonterminal x, item_rhs x) \<in> \<RR>"
    by (metis (no_types, lifting) LocalLexing.pvalid_def LocalLexing_axioms assms case_prodE item_nonterminal_def item_rhs_def prod.sel(1) snd_conv validRules wellformed_item_def)
  from 1 x_rule is_derivation_step have 
    "is_derivation ((take u (terminals p)) @ (item_rhs x) @ \<gamma>)"
    by auto
  then have "is_derivation ((take u (terminals p)) @ ((item_\<alpha> x)@(item_\<beta> x)) @ \<gamma>)" 
    by (simp add: item_rhs_split)
  then have "is_derivation ((take u (terminals p)) @ (item_\<alpha> x) @ ((item_\<beta> x) @ \<gamma>))"
    by simp
  then have "is_derivation ((take u (terminals p)) @ (drop u (terminals p)) @ ((item_\<beta> x) @ \<gamma>))"
    by (metis 1 is_derivation_derives terminals_drop)
  then have "is_derivation ((terminals p) @ ((item_\<beta> x) @ \<gamma>))"
    by (metis append_assoc append_take_drop_id)
  then show ?thesis by auto
qed

lemma next_symbol_not_complete: "next_symbol x = Some t \<Longrightarrow> \<not> (is_complete x)"
  by (metis next_symbol_def option.discI)

lemma next_symbol_starts_item_\<beta>:
  assumes wf: "wellformed_item x"
  assumes next_symbol: "next_symbol x = Some t"
  shows "\<exists> \<delta>. item_\<beta> x = t#\<delta>"
proof -
  from next_symbol have nc: "\<not> (is_complete x)" using next_symbol_not_complete by auto
  from next_symbol have atdot: "item_rhs x ! item_dot x = t" by (simp add: next_symbol_def nc)
  from nc have inrange: "item_dot x < length (item_rhs x)" 
    by (simp add: is_complete_def)
  from inrange atdot show ?thesis
    apply (simp add: item_\<beta>_def)
    by (metis Cons_nth_drop_Suc)
qed   

lemma pvalid_prefixlang:
  assumes pvalid: "pvalid p x"
  assumes is_terminal: "is_terminal t"
  assumes next_symbol: "next_symbol x = Some t"
  shows "(terminals p) @ [t] \<in> \<L>\<^sub>P"
proof -
  have "\<exists> \<delta>. item_\<beta> x = t#\<delta>"
    by (metis next_symbol next_symbol_starts_item_\<beta> pvalid pvalid_def)
  then obtain \<delta> where \<delta>:"item_\<beta> x = t#\<delta>" by blast
  have "\<exists> \<omega>. is_derivation ((terminals p)@(item_\<beta> x)@\<omega>)"
    by (metis pvalid pvalid_is_derivation_terminals_item_\<beta>) 
  then obtain \<omega> where "is_derivation ((terminals p)@(item_\<beta> x)@\<omega>)" by blast
  then have "is_derivation ((terminals p)@(t#\<delta>)@\<omega>)" by (metis \<delta>)
  then have "is_derivation (((terminals p)@[t])@(\<delta>@\<omega>))" by simp
  then show ?thesis
    by (metis (no_types, lifting) CFG.\<L>\<^sub>P_def CFG_axioms  
      append_Nil2 is_terminal is_word_append is_word_cons 
      is_word_terminals mem_Collect_eq pvalid pvalid_def) 
qed 

lemma TokensAt_elem_in_\<W>: 
  assumes P: "P \<subseteq> \<PP>"
  assumes u_in_Tokens_at: "u \<in> TokensAt k (Gen P)"
  shows "u \<in> \<W> P k"
proof -
  have "\<exists>t s x l.
         u = (t, s) \<and>
         x \<in> bin (Gen P) k \<and>
         next_symbol x = Some t \<and> is_terminal t \<and> l \<in> Lex t Doc k \<and> s = take l (drop k Doc)"
  using u_in_Tokens_at by (auto simp add: TokensAt_def)
  then obtain t s x l where
     u: "u = (t, s) \<and>
         x \<in> bin (Gen P) k \<and>
         next_symbol x = Some t \<and> is_terminal t \<and> l \<in> Lex t Doc k \<and> s = take l (drop k Doc)"
        by blast
  from u have t: "t = terminal_of_token u" by (metis terminal_of_token_simp)
  from u have s: "s = chars_of_token u" by (metis chars_of_token_simp) 
  from u have item_end_x: "item_end x = k" by (metis (mono_tags, lifting) bin_def mem_Collect_eq) 
  from u have "\<exists> p \<in> P. pvalid p x" by (auto simp add: bin_def Gen_def)
  then obtain p where p: "p \<in> P" and pvalid: "pvalid p x" by blast
  have p_len: "length (chars p) = k"
    by (metis charslength.simps item_end_x pvalid pvalid_item_end) 
  have u_in_\<X>: "u \<in> \<X> k"
    apply (simp add: \<X>_def)
    apply (rule_tac x=t in exI)
    apply (rule_tac x=l in exI)
    using u by (simp add: is_terminal_def)
  show ?thesis
    apply (auto simp add: \<W>_def)
    apply (simp add: u_in_\<X>)
    apply (rule_tac x=p in exI)
    apply (simp add: p p_len)
    apply (simp add: admissible_def t[symmetric])
    apply (rule pvalid_prefixlang[where x=x])
    apply (simp add: pvalid)
    apply (simp add: u)
    apply (simp add: u)
    done
qed

theorem thmD4:
  assumes P: "P \<subseteq> \<PP>"
  shows "\<W> P k = TokensAt k (Gen P)"
using \<W>_elem_in_TokensAt TokensAt_elem_in_\<W>
by (metis Collect_cong Collect_mem_eq assms)

end

end
