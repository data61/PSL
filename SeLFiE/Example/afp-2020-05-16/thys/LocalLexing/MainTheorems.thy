theory MainTheorems
imports PathLemmas
begin

context LocalLexing begin

theorem \<II>_is_generated_by_\<PP>: "\<II> = Gen \<PP>"
proof -
  have "wellformed_items (\<I> (length Doc))"
    using wellformed_items_\<I> by auto
  then have "\<And> x. x \<in> \<I> (length Doc) \<Longrightarrow> item_end x \<le> length Doc"
    using wellformed_item_def wellformed_items_def by blast
  then have "\<I> (length Doc) \<subseteq> items_le (length Doc) (\<I> (length Doc))"
    by (auto simp only: items_le_def)  
  then have "\<I> (length Doc) = items_le (length Doc) (\<I> (length Doc))"
    using items_le_is_filter by blast
  then have \<II>_altdef: "\<II> = items_le (length Doc) (\<I> (length Doc))" using \<II>_def by auto
  have "\<And> p. p \<in> (\<Q> (length Doc)) \<Longrightarrow> charslength p \<le> length Doc"
    using \<PP>_are_doc_tokens \<PP>_def doc_tokens_length by auto
  then have "\<Q> (length Doc) \<subseteq> paths_le (length Doc) (\<Q> (length Doc))"
    by (auto simp only: paths_le_def)
  then have "\<Q> (length Doc) = paths_le (length Doc) (\<Q> (length Doc))"
    using paths_le_is_filter by blast
  then have \<PP>_altdef: "\<PP> = paths_le (length Doc) (\<Q> (length Doc))" using \<PP>_def by auto
  show ?thesis using \<II>_altdef \<PP>_altdef thmD14 by auto
qed

definition finished_item :: "symbol list \<Rightarrow> item"
where
  "finished_item \<alpha> = Item (\<SS>, \<alpha>) (length \<alpha>) 0 (length Doc)"

lemma item_rule_finished_item[simp]: "item_rule (finished_item \<alpha>) = (\<SS>, \<alpha>)"
  by (simp add: finished_item_def)

lemma item_origin_finished_item[simp]: "item_origin (finished_item \<alpha>) = 0"
  by (simp add: finished_item_def)

lemma item_end_finished_item[simp]: "item_end (finished_item \<alpha>) = length Doc"
  by (simp add: finished_item_def)

lemma item_dot_finished_item[simp]: "item_dot (finished_item \<alpha>) = length \<alpha>"
  by (simp add: finished_item_def)

lemma item_rhs_finished_item[simp]: "item_rhs (finished_item \<alpha>) = \<alpha>"
  by (simp add: finished_item_def)

lemma item_\<alpha>_finished_item[simp]: "item_\<alpha> (finished_item \<alpha>) = \<alpha>"
  by (simp add: finished_item_def item_\<alpha>_def)

lemma item_nonterminal_finished_item[simp]: "item_nonterminal (finished_item \<alpha>) = \<SS>"
  by (simp add: finished_item_def item_nonterminal_def)
  
lemma Derives1_of_singleton:
  assumes "Derives1 [N] i r \<alpha>"
  shows "i = 0 \<and> r = (N, \<alpha>)"
proof -
  from assms have "i = 0" using Derives1_bound
    using length_Cons less_Suc0 list.size(3) by fastforce 
  then show ?thesis using assms
    using Derives1_def append_Cons append_self_conv append_self_conv2 length_0_conv 
      list.inject by auto
qed    

definition pvalid_with :: "tokens \<Rightarrow> item \<Rightarrow> nat \<Rightarrow> symbol list \<Rightarrow> bool"
where
  "pvalid_with p x u \<gamma> = 
     (wellformed_tokens p \<and>
     wellformed_item x \<and>
     u \<le> length p \<and>
     charslength p = item_end x \<and>
     charslength (take u p) = item_origin x \<and>
     is_derivation (terminals (take u p) @ [item_nonterminal x] @ \<gamma>) \<and>
     derives (item_\<alpha> x) (terminals (drop u p)))"

lemma pvalid_with: "pvalid p x = (\<exists> u \<gamma>. pvalid_with p x u \<gamma>)"
  using pvalid_def pvalid_with_def by blast

theorem Completeness:
  assumes p_in_ll: "p \<in> ll"
  shows "\<exists> \<alpha>. pvalid_with p (finished_item \<alpha>) 0 [] \<and> finished_item \<alpha> \<in> \<II>"
proof -
  have p: "p \<in> \<PP> \<and> charslength p = length Doc \<and> terminals p \<in> \<L>"
    using p_in_ll ll_def by auto
  then have derives_p: "derives [\<SS>] (terminals p)"
    using \<L>_def is_derivation_def mem_Collect_eq by blast
  then have "\<exists> D. Derivation [\<SS>] D (terminals p)"
    by (simp add: derives_implies_Derivation)   
  then obtain D where D: "Derivation [\<SS>] D (terminals p)" by blast
  have is_word_p: "is_word (terminals p)"  using leftlang p by blast
  have not_is_word_\<SS>: "\<not> (is_word [\<SS>])" using is_nonterminal_startsymbol is_terminal_nonterminal 
    is_word_cons by blast  
  have "D \<noteq> []" using D is_word_p not_is_word_\<SS> using Derivation.simps(1) by force
  then have "\<exists> d D'. D = d#D'" using D Derivation.elims(2) by blast 
  then obtain d D' where d: "D = d#D'" by blast
  have "\<exists> \<alpha>. Derives1 [\<SS>] (fst d) (snd d) \<alpha> \<and> derives \<alpha> (terminals p)"
    using d D Derivation.simps(2) Derivation_implies_derives by blast 
  then obtain \<alpha> where \<alpha>: "Derives1 [\<SS>] (fst d) (snd d) \<alpha> \<and> derives \<alpha> (terminals p)" by blast
  then have snd_d_in_\<RR>: "snd d \<in> \<RR>" using Derives1_rule by blast 
  with \<alpha> have snd_d: "snd d = (\<SS>, \<alpha>)" using Derives1_of_singleton by blast
  have wellformed_p: "wellformed_tokens p" by (simp add: \<PP>_wellformed p)
  have wellformed_finished_item: "wellformed_item (finished_item \<alpha>)"  
    apply (auto simp add: wellformed_item_def)
    using snd_d snd_d_in_\<RR> by metis    
  have pvalid_with: "pvalid_with p (finished_item \<alpha>) 0 []" 
    apply (auto simp add: pvalid_with_def)
    using wellformed_p apply blast
    using wellformed_finished_item apply blast
    using p apply (simp add: finished_item_def)
    apply (simp add: is_derivation_def)
    by (simp add: \<alpha>)
  then have "pvalid p (finished_item \<alpha>)" using pvalid_def pvalid_with_def by blast 
  then have "finished_item \<alpha> \<in> Gen \<PP>" using Gen_def mem_Collect_eq p by blast
  then have "finished_item \<alpha> \<in> \<II>" using \<II>_is_generated_by_\<PP> by blast 
  with pvalid_with show ?thesis by blast
qed
  
theorem Soundness:
  assumes finished_item_\<alpha>: "finished_item \<alpha> \<in> \<II>"
  shows "\<exists> p. pvalid_with p (finished_item \<alpha>) 0 [] \<and> p \<in> ll"
proof -
  have "finished_item \<alpha> \<in> Gen \<PP>"
    using \<II>_is_generated_by_\<PP> finished_item_\<alpha> by auto 
  then obtain p where p: "p \<in> \<PP> \<and> pvalid p (finished_item \<alpha>)"
    using Gen_implies_pvalid by blast 
  have pvalid_p_finished_item: "pvalid  p (finished_item \<alpha>)" using p by blast
  from iffD1[OF pvalid_def this, simplified] obtain r \<gamma> where pvalid:
    "wellformed_tokens p \<and>
     wellformed_item (finished_item \<alpha>) \<and>
     r \<le> length p \<and>
     length (chars p) = length Doc \<and>
     chars (take r p) = [] \<and>
     is_derivation (take r (terminals p) @ \<SS> # \<gamma>) \<and> derives \<alpha> (drop r (terminals p))"
     by  blast
  have "item_rule (finished_item \<alpha>) \<in> \<RR>" using pvalid
    using wellformed_item_def by blast
  then have "(\<SS>, \<alpha>) \<in> \<RR>" by simp 
  then have is_derivation_\<alpha>: "is_derivation \<alpha>" by (simp add: is_derivation_def leftderives_rule)
  have drop_r_p_in_\<PP>: "drop r p \<in> \<PP>"
    apply (rule drop_empty_tokens)
    using p apply blast
    using pvalid apply blast
    using pvalid apply simp
    by (metis append_Nil2 derives_trans is_derivation_\<alpha> is_derivation_def 
      is_derivation_implies_admissible is_word_terminals_drop pvalid terminals_drop)
  then have in_ll: "drop r p \<in> ll"
    apply (auto simp add: ll_def) 
    apply (metis append_Nil append_take_drop_id chars_append pvalid) 
    using is_derivation_\<alpha> pvalid
    by (metis (no_types, lifting) \<L>_def derives_trans is_derivation_def 
      is_word_terminals_drop mem_Collect_eq terminals_drop)
  have "pvalid_with (drop r p) (finished_item \<alpha>) 0 []"
    apply (auto simp add: pvalid_with_def)
    using \<PP>_wellformed drop_r_p_in_\<PP> apply blast 
    using pvalid apply blast
    apply (metis append_Nil append_take_drop_id chars_append pvalid)
    apply (simp add: is_derivation_def)
    using pvalid by blast
  with in_ll show ?thesis by auto
qed

lemma is_finished_and_finished_item:
  assumes wellformed_x: "wellformed_item x"
  shows "is_finished x = (\<exists> \<alpha>. x = finished_item \<alpha>)"
proof -
  {
    assume is_finished_x: "is_finished x"
    obtain \<alpha> where \<alpha>: "\<alpha> = item_rhs x" by blast
    have "x = finished_item \<alpha>"
      apply (rule item.expand)
      apply auto
      using \<alpha> is_finished_def is_finished_x item_nonterminal_def item_rhs_def apply auto[1]
      using \<alpha> assms is_complete_def is_finished_def is_finished_x wellformed_item_def apply auto[1]
      using is_finished_def is_finished_x apply blast
      using is_finished_def is_finished_x by auto
    then have "\<exists> \<alpha>. x = finished_item \<alpha>" by blast
  }
  note left_implies_right = this
  {
    assume "\<exists> \<alpha>. x = finished_item \<alpha>"
    then obtain \<alpha> where \<alpha>: "x = finished_item \<alpha>" by blast
    have "is_finished x" by (simp add: \<alpha> is_finished_def is_complete_def)
  }
  note right_implies_left = this
  show ?thesis using left_implies_right right_implies_left by blast
qed 

theorem Correctness:
  shows "(ll \<noteq> {}) = earley_recognised"
proof -
  have 1: "(ll \<noteq> {}) = (\<exists> \<alpha>. finished_item \<alpha> \<in> \<II>)"
    using Soundness Completeness ex_in_conv by fastforce
  have 2: "(\<exists> \<alpha>. finished_item \<alpha> \<in> \<II>) = (\<exists> x \<in> \<II>. is_finished x)"
    using \<II>_def is_finished_and_finished_item wellformed_items_\<I> wellformed_items_def by auto
  show ?thesis using earley_recognised_def 1 2 by blast
qed 

end

end
