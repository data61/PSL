theory TheoremD12
imports TheoremD11
begin

context LocalLexing begin

lemma charslength_appendix_is_empty:
  "charslength (p@ts) = charslength p \<Longrightarrow> (\<And> t. t \<in> set ts \<Longrightarrow> chars_of_token t = [])"
proof (induct ts)
  case Nil then show ?case by auto
next
  case (Cons s ts)
    have "charslength (p @ s # ts) = charslength (p @ ts) + length (chars_of_token s)"
      by simp
    then have "charslength (p @ s # ts) = charslength p + charslength ts + length (chars_of_token s)"
      by simp
    with Cons.prems(1) have "charslength ts + length (chars_of_token s) = 0" by arith
    then show ?case using Cons.prems(2) charslength_0 by auto
qed        

lemma empty_tokens_have_charslength_0:
  "(\<And> t. t \<in> set ts \<Longrightarrow> chars_of_token t = []) \<Longrightarrow> charslength ts = 0"
proof (induct ts)
  case Nil then show ?case by simp
next
  case (Cons t ts)
    then show ?case by auto
qed

lemma \<pi>_idempotent': "\<pi> k {} (\<pi> k T I) = \<pi> k T I"
  apply (simp add: \<pi>_no_tokens)
  by (simp add: Complete_\<pi>_fix Predict_\<pi>_fix fix_is_fix_of_limit)

theorem thmD12:
  assumes induct: "items_le k (\<J> k u) = Gen (paths_le k (\<P> k u))"
  assumes induct_tokens: "\<T> k u = \<Z> k u"
  shows "items_le k (\<J> k (Suc u)) \<supseteq> Gen (paths_le k (\<P> k (Suc u)))"
proof -
  {
    fix x :: item
    assume x_dom: "x \<in> Gen (paths_le k (\<P> k (Suc u)))" 
    have "\<exists> q. pvalid q x \<and> q \<in> \<P> k (Suc u) \<and> charslength q \<le> k"
    proof -
      have "\<And>i I n. i \<in> I \<or> i \<notin> items_le n I"
        by (meson items_le_is_filter subsetCE)
      then show ?thesis
        by (metis Gen_implies_pvalid x_dom items_le_fix_D items_le_idempotent items_le_paths_le 
          pvalid_item_end)
    qed
    then obtain q where q: "pvalid q x \<and> q \<in> \<P> k (Suc u) \<and> charslength q \<le> k" by blast
    have "q \<in> \<P> k u \<or> q \<notin> \<P> k u" by blast
    then have "x \<in> items_le k (\<J> k (Suc u))"
    proof (induct rule: disjCases2) 
      case 1
        with q have "x \<in> Gen (paths_le k (\<P> k u))"
          apply (auto simp add: Gen_def)
          apply (rule_tac x=q in exI)
          by (simp add: paths_le_def)
        with induct have "x \<in> items_le k (\<J> k u)" by simp
        then show ?case
          using LocalLexing.items_le_def LocalLexing_axioms \<J>_subset_Suc_u by fastforce
    next
      case 2
        have q_is_limit: "q \<in> limit (Append (\<Y> (\<Z> k u) (\<P> k u) k) k) (\<P> k u)" using q by auto
        from limit_Append_path_nonelem_split[OF q_is_limit 2] obtain p ts where p_ts:
          "q = p @ ts \<and>
           p \<in> \<P> k u \<and>
           charslength p = k \<and>
           admissible (p @ ts) \<and>
           (\<forall>t\<in>set ts. t \<in> \<Y> (\<Z> k u) (\<P> k u) k) \<and> (\<forall>t\<in>set (butlast ts). chars_of_token t = [])"
           by blast
        then have ts_nonempty: "ts \<noteq> []" using 2 using self_append_conv by auto
        obtain T where T: "T = \<Y> (\<Z> k u) (\<P> k u) k" by blast
        obtain J where J: "J = \<pi> k T (Gen (paths_le k (\<P> k u)))" by blast
        from q p_ts have chars_of_token_is_empty: "\<And> t. t\<in>set ts \<Longrightarrow> chars_of_token t = []"
          using charslength_appendix_is_empty chars_append charslength.simps le_add1 le_imp_less_Suc 
            le_neq_implies_less length_append not_less_eq by auto        
        {
          fix sss :: "token list"
          have "is_prefix sss ts \<Longrightarrow> pvalid (p @ sss) x \<Longrightarrow> x \<in> J"
          proof (induct "length sss" arbitrary: sss x rule: less_induct)
            case less
              have "sss = [] \<or> sss \<noteq> []" by blast
              then show ?case
              proof (induct rule: disjCases2)
                case 1                
                  with less have pvalid_p_x: "pvalid p x" by auto
                  have charslength_p: "charslength p \<le> k" using p_ts by blast 
                  with p_ts have "p \<in> paths_le k (\<P> k u)"
                    by (simp add: paths_le_def)
                  with pvalid_p_x have "x \<in> Gen (paths_le k (\<P> k u))" 
                    using Gen_def mem_Collect_eq by blast 
                  then have "x \<in> \<pi> k T (Gen (paths_le k (\<P> k u)))" using \<pi>_apply_setmonotone 
                    by blast
                  then show "x \<in> J" using pvalid_item_end q J LocalLexing.items_le_def 
                    LocalLexing_axioms charslength_p mem_Collect_eq pvalid_p_x by auto 
              next
                case 2
                  then have "\<exists> a ss. sss = ss@[a]" using rev_exhaust by blast 
                  then obtain a ss where snoc: "sss = ss@[a]" by blast
                  obtain p' where p': "p' = p @ ss" by auto
                  then have "pvalid_left (p'@[a]) x" using snoc less pvalid_left by simp
                  from iffD1[OF pvalid_left_def this] obtain r \<omega> where pvalid:
                    "wellformed_tokens (p' @ [a]) \<and>
                     wellformed_item x \<and>
                     r \<le> length (p' @ [a]) \<and>
                     charslength (p' @ [a]) = item_end x \<and>
                     charslength (take r (p' @ [a])) = item_origin x \<and>
                     is_leftderivation (terminals (take r (p' @ [a])) @ [item_nonterminal x] @ \<omega>) \<and>
                     leftderives (item_\<alpha> x) (terminals (drop r (p' @ [a])))" by blast
                  obtain q' where q': "q' = p'@[a]" by blast
                  have is_prefix_ss_ts: "is_prefix ss ts" using snoc less 
                    by (simp add: is_prefix_append) 
                  then have "is_prefix (p@ss) q" using p' snoc p_ts by simp
                  then have "is_prefix p' q" using p' by simp
                  then have h1: "p' \<in> \<PP>" using q \<PP>_covers_\<P> prefixes_are_paths' subsetCE by blast 
                  have charslength_ss: "charslength ss = 0" 
                    apply (rule empty_tokens_have_charslength_0)
                    by (metis is_prefix_ss_ts append_is_Nil_conv chars_append chars_of_token_is_empty 
                      charslength.simps charslength_0 is_prefix_def length_greater_0_conv list.size(3))
                  then have h2: "charslength p' = k" using p' p_ts by auto  
                  have a_in_ts: "a \<in> set ts"
                    by (metis in_set_dropD is_prefix_append is_prefix_cons list.set_intros(1) 
                      snoc less(2)) 
                  then have h3: "a \<in> T" using T p_ts by blast 
                  have h4: "T \<subseteq> \<X> k"
                    using LocalLexing.\<Z>.simps(2) LocalLexing_axioms T \<Z>_subset_\<X> by blast
                  note h5 = q'
                  obtain N where N: "N = item_nonterminal x" by blast
                  obtain \<alpha> where \<alpha>: "\<alpha> = item_\<alpha> x" by blast
                  obtain \<beta> where \<beta>: "\<beta> = item_\<beta> x" by blast
                  have item_rule_x: "item_rule x = (N, \<alpha> @ \<beta>)"
                    using N \<alpha> \<beta> item_nonterminal_def item_rhs_def item_rhs_split by auto 
                  have "wellformed_item x" using pvalid by blast
                  then have h6: "(N, \<alpha>@\<beta>) \<in> \<RR>" using item_rule_x
                    by (simp add: wellformed_item_def) 
                  have h7: "r \<le> length q'" using pvalid q' by blast 
                  have h8: "leftderives [\<SS>] (terminals (take r q') @ [N] @ \<omega>)"
                    using N is_leftderivation_def pvalid q' by blast
                  have h9: "leftderives \<alpha> (terminals (drop r q'))" using \<alpha> pvalid q' by blast
                  have h10: "k = k + length (chars_of_token a)"
                    by (simp add: a_in_ts chars_of_token_is_empty)
                  have h11: "x = Item (N, \<alpha> @ \<beta>) (length \<alpha>) (charslength (take r q')) k"
                    by (metis \<alpha> charslength_ss a_in_ts append_Nil2 chars.simps(2) chars_append 
                      chars_of_token_is_empty charslength.simps h2 item.collapse item_dot_is_\<alpha>_length 
                      item_rule_x length_greater_0_conv list.size(3) pvalid q')
                  have x_dom: "x \<in> items_le k (\<pi> k {} (Scan T k (Gen (Prefixes p'))))"  
                    using thmD11[OF h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11] by auto
                  {
                    fix y :: item
                    fix toks :: "token list"
                    assume pvalid_toks_y: "pvalid toks y"
                    assume is_prefix_toks_p': "is_prefix toks p'"
                    then have charslength_toks: "charslength toks \<le> k"
                      using charslength_of_prefix h2 by blast 
                    then have item_end_y: "item_end y \<le> k" using pvalid_item_end pvalid_toks_y 
                      by auto 
                    have "is_prefix toks p \<or> (\<exists> ss'. is_prefix ss' ss \<and> toks = p@ss')"
                      using is_prefix_of_append is_prefix_toks_p' p' by auto
                    then have "y \<in> J"
                    proof (induct rule: disjCases2)
                      case 1  
                        then have "toks \<in> \<P> k u" using p_ts prefixes_are_paths by blast 
                        with charslength_toks have "toks \<in> paths_le k (\<P> k u)"
                          by (simp add: paths_le_def)
                        then have "y \<in> Gen (paths_le k (\<P> k u))" using pvalid_toks_y
                          Gen_def mem_Collect_eq by blast 
                        then have "y \<in> \<pi> k T (Gen (paths_le k (\<P> k u)))" using \<pi>_apply_setmonotone 
                          by blast
                        then show "y \<in> J" by (simp add: J items_le_def item_end_y)
                    next
                      case 2
                        then obtain ss' where ss': "is_prefix ss' ss \<and> toks = p@ss'" by blast
                        then have l1: "length ss' < length sss"
                          using append_eq_conv_conj append_self_conv is_prefix_length length_append 
                            less_le_trans nat_neq_iff not_Cons_self2 not_add_less1 snoc by fastforce
                        have l2: "is_prefix ss' ts" using ss' is_prefix_ss_ts
                          by (metis append_dropped_prefix is_prefix_append) 
                        have l3: "pvalid (p @ ss') y" using ss' pvalid_toks_y by simp 
                        show ?case using less.hyps[OF l1 l2 l3] by blast
                    qed
                  }
                  then have "Gen (Prefixes p') \<subseteq> J"
                    by (meson Gen_implies_pvalid Prefixes_is_prefix subsetI) 
                  with x_dom have r0: "x \<in> items_le k (\<pi> k {} (Scan T k J))"
                    by (metis (no_types, lifting) LocalLexing.items_le_def LocalLexing_axioms 
                      mem_Collect_eq mono_Scan mono_\<pi> mono_subset_elem subsetI)
                  then have x_in_\<pi>: "x \<in> \<pi> k {} (Scan T k J)"
                    using LocalLexing.items_le_is_filter LocalLexing_axioms subsetCE by blast 
                  have r1: "Scan T k J = J"
                    by (simp add: J Scan_\<pi>_fix)
                  have r2: "\<pi> k {} J = J" using \<pi>_idempotent' using J by blast
                  from x_in_\<pi> r1 r2 show "x \<in> J" by auto
              qed
          qed    
        }
        note th = this
        have x_in_J: "x \<in> J"
          apply (rule th[of ts])
          apply (simp add: is_prefix_eq_proper_prefix)
          using p_ts q by blast
        have \<T>_eq_\<Z>: "\<T> k (Suc u) = \<Z> k (Suc u)"
          using induct induct_tokens \<T>_equals_\<Z>_induct_step by blast
        have T_alt: "T = \<T> k (Suc u)" using \<T>_eq_\<Z> T by simp
        have "J = \<pi> k T (items_le k (\<J> k u))" using induct J by simp
        then have "J \<subseteq> \<pi> k T (\<J> k u)" by (simp add: items_le_is_filter monoD mono_\<pi>) 
        with T_alt have "J \<subseteq> \<J> k (Suc u)" using \<J>.simps(2) by blast
        with x_in_J have "x \<in> \<J> k (Suc u)" by blast
        then show ?case
          using LocalLexing.items_le_def LocalLexing_axioms pvalid_item_end q by auto
    qed
  }
  then show ?thesis by auto
qed
    
end

end
