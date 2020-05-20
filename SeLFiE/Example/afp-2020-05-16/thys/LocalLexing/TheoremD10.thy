theory TheoremD10
imports TheoremD9 Ladder
begin

context LocalLexing begin

lemma \<P>_wellformed: "p \<in> \<P> k u \<Longrightarrow> wellformed_tokens p"
using \<P>_are_admissible admissible_wellformed_tokens by blast

lemma \<X>_token_length: "t \<in> \<X> k \<Longrightarrow> k + length (chars_of_token t) \<le> length Doc"
by (metis Nat.le_diff_conv2 \<X>_is_prefix add.commute chars_of_token_def empty_\<X> 
  empty_iff is_prefix_length le_neq_implies_less length_drop linear)

lemma mono_Scan: "mono (Scan T k)"
  by (simp add: Scan_regular regular_implies_mono)

lemma \<pi>_apply_setmonotone: "x \<in> I \<Longrightarrow> x \<in> \<pi> k T I"
using Complete_subset_\<pi> LocalLexing.Complete_def LocalLexing_axioms by blast

lemma Scan_apply_setmonotone: "x \<in> I \<Longrightarrow> x \<in> Scan T k I"
  by (simp add: Scan_def)
  
  
lemma leftderives_padfront:
  assumes "leftderives \<alpha> \<beta>"
  assumes "is_word u"
  shows "leftderives (u@\<alpha>) (u@\<beta>)"
using LeftDerivation_append_prefix LeftDerivation_implies_leftderives assms(1) assms(2) 
  leftderives_implies_LeftDerivation by blast

lemma leftderives_padback:
  assumes "leftderives \<alpha> \<beta>"
  assumes "is_sentence u"
  shows "leftderives (\<alpha>@u) (\<beta>@u)"
using LeftDerivation_append_suffix LeftDerivation_implies_leftderives assms(1) assms(2) 
  leftderives_implies_LeftDerivation by blast

lemma leftderives_pad:
  assumes \<alpha>_\<beta>: "leftderives \<alpha> \<beta>"
  assumes is_word: "is_word u"
  assumes is_sentence: "is_sentence v"
  shows "leftderives (u@\<alpha>@v) (u@\<beta>@v)"
by (simp add: \<alpha>_\<beta> is_sentence is_word leftderives_padback leftderives_padfront)    

lemma leftderives_rule:
  assumes "(N, w) \<in> \<RR>"
  shows "leftderives [N] w"
by (metis append_Nil append_Nil2 assms is_sentence_def is_word_terminals leftderives1_def 
  leftderives1_implies_leftderives list.pred_inject(1) terminals_empty wellformed_tokens_empty_path)

lemma leftderives_rule_step:
  assumes ld: "leftderives a (u@[N]@v)"
  assumes rule: "(N, w) \<in> \<RR>"
  assumes is_word: "is_word u"
  assumes is_sentence: "is_sentence v"
  shows "leftderives a (u@w@v)"
proof -
  have N_w: "leftderives [N] w" using rule leftderives_rule by blast
  then have "leftderives (u@[N]@v) (u@w@v)" using leftderives_pad is_word is_sentence by blast
  then show "leftderives a (u@w@v)" using leftderives_trans ld by blast    
qed

lemma leftderives_trans_step:
  assumes ld: "leftderives a (u@b@v)"
  assumes rule: "leftderives b c"
  assumes is_word: "is_word u"
  assumes is_sentence: "is_sentence v"
  shows "leftderives a (u@c@v)"
proof -
  have "leftderives (u@b@v) (u@c@v)" using leftderives_pad ld rule is_word is_sentence by blast
  then show ?thesis using leftderives_trans ld by blast
qed

lemma charslength_of_prefix:
  assumes "is_prefix a b"
  shows "charslength a \<le> charslength b"
by (simp add: assms is_prefix_chars is_prefix_length)

lemma item_rhs_simp[simp]: "item_rhs (Item (N, \<alpha>) d i j) = \<alpha>"
  by (simp add: item_rhs_def)

definition Prefixes :: "'a list \<Rightarrow> 'a list set"
where
  "Prefixes p = { q . is_prefix q p }"

lemma \<PP>_wellformed: "p \<in> \<PP> \<Longrightarrow> wellformed_tokens p"
  by (simp add: \<PP>_are_admissible admissible_wellformed_tokens)
    
lemma Prefixes_reflexive[simp]: "p \<in> Prefixes p"
  by (simp add: Prefixes_def is_prefix_def)

lemma Prefixes_is_prefix: "q \<in> Prefixes p = is_prefix q p"
  by (simp add: Prefixes_def)

lemma prefixes_are_paths': "p \<in> \<PP> \<Longrightarrow> is_prefix q p \<Longrightarrow> q \<in> \<PP>"
  using \<P>.simps(3) \<PP>_def prefixes_are_paths by blast

lemma thmD10_ladder:
  "p \<in> \<PP> \<Longrightarrow> 
   charslength p = k \<Longrightarrow> 
   X \<in> T \<Longrightarrow> 
   T \<subseteq> \<X> k \<Longrightarrow> 
   (N, \<alpha>@\<beta>) \<in> \<RR> \<Longrightarrow>
   r \<le> length p \<Longrightarrow> 
   leftderives [\<SS>] ((terminals (take r p))@[N]@\<gamma>) \<Longrightarrow>
   LeftDerivationLadder \<alpha> D L (terminals ((drop r p)@[X])) \<Longrightarrow> 
   ladder_last_j L = length (drop r p) \<Longrightarrow> 
   k' = k + length (chars_of_token X) \<Longrightarrow>
   x = Item (N, \<alpha>@\<beta>) (length \<alpha>) (charslength (take r p)) k' \<Longrightarrow>
   I = items_le k' (\<pi> k' {} (Scan T k (Gen (Prefixes p)))) 
   \<Longrightarrow> x \<in> I"
proof (induct "length L" arbitrary: N \<alpha> \<beta> r \<gamma> D L x rule: less_induct)
  case less
    have item_origin_x_def: "item_origin x = (charslength (take r p))"
      by (simp add: less.prems(11)) 
    then have x_k: "item_origin x \<le> k"
      using charslength.simps is_prefix_chars is_prefix_length is_prefix_take less.prems(2) by force 
    have item_end_x_def: "item_end x = k'" by (simp add: less.prems(11)) 
    have item_dot_x_def: "item_dot x = length \<alpha>" by (simp add: less.prems(11))  
    have k'_upperbound: "k' \<le> length Doc"
      using \<X>_token_length less.prems(10) less.prems(3) less.prems(4) by blast 
    note item_def = less.prems(11) 
    note k' = less.prems(10)
    note rule_dom = less.prems(5)
    note p_charslength = less.prems(2)
    note p_dom = less.prems(1)
    note r = less.prems(6)
    note leftderives_start = less.prems(7)
    note X_dom = less.prems(3)
    have wellformed_x: "wellformed_item x"
      apply (auto simp add: wellformed_item_def item_def rule_dom p_charslength)
      apply (subst k')
      apply (subst charslength.simps[symmetric])
      apply (subst p_charslength[symmetric])
      using item_origin_x_def p_charslength x_k apply linarith
      apply (rule k'_upperbound)
      done
    have  leftderives_\<alpha>: "leftderives \<alpha> (terminals ((drop r p)@[X]))"
      using LeftDerivationLadder_def LeftDerivation_implies_leftderives less.prems(8) by blast  
    have is_sentence_drop_pX: "is_sentence (drop r (terminals p) @ [terminal_of_token X])"
      by (metis derives_is_sentence is_sentence_concat leftderives_\<alpha> leftderives_implies_derives 
        rule_\<alpha>_type rule_dom terminals_append terminals_drop terminals_singleton)
    have snd_item_rule_x: "snd (item_rule x) = \<alpha>@\<beta>" by (simp add: item_def)
    from less have "is_ladder D L" using LeftDerivationLadder_def by blast 
    then have "length L \<noteq> 0" by (simp add: is_ladder_not_empty) 
    then have "length L = 1 \<or> length L > 1" by arith
    then show ?case 
    proof (induct rule: disjCases2)
      case 1
        have "\<exists> i. LeftDerivationFix \<alpha> i D (length (drop r p)) (terminals ((drop r p)@[X]))"
          using "1.hyps" LeftDerivationLadder_L_0 less.prems(8) less.prems(9) by fastforce 
        then obtain i where LDF:
          "LeftDerivationFix \<alpha> i D (length (drop r p)) (terminals ((drop r p)@[X]))" by blast
        from LeftDerivationFix_splits_at_derives[OF this] obtain U a1 a2 b1 b2 where decompose:
          "splits_at \<alpha> i a1 U a2 \<and> splits_at (terminals (drop r p @ [X])) 
            (length (drop r p)) b1 U b2 \<and> derives a1 b1 \<and> derives a2 b2" by blast
        then have b1: "b1 = terminals (drop r p)"
          by (simp add: append_eq_conv_conj splits_at_def)
        with decompose have U: "U = fst X"
          by (metis length_terminals nth_append_length splits_at_def terminal_of_token_def 
            terminals_append terminals_singleton)
        from decompose b1 U have b2: "b2 = []"
          by (simp add: splits_at_combine splits_at_def)
        have D: "LeftDerivation \<alpha> D (terminals ((drop r p)@[X]))" 
          using LDF LeftDerivationLadder_def less.prems(8) by blast 
        let ?y = "Item (item_rule x) (length a1) (item_origin x) k"
        have wellformed_y: "wellformed_item ?y"
          using wellformed_x
          apply (auto simp add: wellformed_item_def x_k)
          using k' k'_upperbound apply arith
          apply (simp add: item_rhs_def snd_item_rule_x)
          using decompose splits_at_def
          by (simp add: is_prefix_length trans_le_add1) 
        have y_nonterminal: "item_nonterminal ?y = N"
          by (simp add: item_def item_nonterminal_def)   
        have item_\<alpha>_y: "item_\<alpha> ?y = a1"
          by (metis append_assoc append_eq_conv_conj append_take_drop_id decompose item.sel(1) 
            item.sel(2) item_\<alpha>_def item_rhs_def snd_item_rule_x splits_at_def)    
        have pvalid_y: "pvalid p ?y"
          apply (auto simp add: pvalid_def)
          using p_dom \<PP>_wellformed apply blast
          using wellformed_y apply auto[1]
          apply (rule_tac x=r in exI)
          apply (auto simp add: r)
          using p_charslength apply simp
          using item_def apply simp
          apply (rule_tac x=\<gamma> in exI)
          using y_nonterminal apply simp
          using is_derivation_def leftderives_start apply auto[1]
          apply (simp add: item_\<alpha>_y)
          using b1 decompose by auto
        let ?z = "inc_item ?y k'"
        have item_rhs_y: "item_rhs ?y = \<alpha>@\<beta>"
          by (simp add: item_def item_rhs_def)
        have split_\<alpha>: "\<alpha> = a1@[U]@a2" using decompose splits_at_combine by blast 
        have next_symbol_y: "next_symbol ?y = Some(fst X)"  
          by (auto simp add: next_symbol_def is_complete_def item_rhs_y split_\<alpha> U)
        have z_in_Scan_y: "?z \<in> Scan T k {?y}" 
          apply (simp add: Scan_def)
          apply (rule disjI2)
          apply (rule_tac x="?y" in exI)
          apply (rule_tac x="fst X" in exI)
          apply (rule_tac x="snd X" in exI)
          apply (auto simp add: bin_def X_dom)
          using k' chars_of_token_def apply simp
          using next_symbol_y apply simp
          done
        from pvalid_y have "?y \<in> Gen(Prefixes p)"
          apply (simp add: Gen_def)
          apply (rule_tac x=p in exI)
          by (auto simp add: paths_le_def p_dom)
        then have "Scan T k {?y} \<subseteq> Scan T k (Gen(Prefixes p))"
          apply (rule_tac monoD[OF mono_Scan])
          apply blast
          done
        with z_in_Scan_y have z_in_Scan_Gen: "?z \<in> Scan T k (Gen(Prefixes p))"
          using rev_subsetD by blast
        have wellformed_z: "wellformed_item ?z"
          using k' k'_upperbound next_symbol_y wellformed_inc_item wellformed_y by auto
        have item_\<beta>_z: "item_\<beta> ?z = a2@\<beta>"
          apply (simp add: item_\<beta>_def)
          apply (simp add: item_rhs_y split_\<alpha>)
          done
        have item_end_z: "item_end ?z = k'" by simp
        have x_via_z: "x = inc_dot (length a2) ?z"
          by (simp add: inc_dot_def less.prems(11) split_\<alpha>)
        have x_in_z: "x \<in> \<pi> k' {} {?z}"
          apply (subst x_via_z)
          apply (rule_tac thmD6[OF wellformed_z item_\<beta>_z item_end_z])
          using decompose b2 by blast  
        have "\<pi> k' {} {?z} \<subseteq> \<pi> k' {} (Scan T k (Gen(Prefixes p)))"
          apply (rule_tac monoD[OF mono_\<pi>])
          using z_in_Scan_Gen using empty_subsetI insert_subset by blast 
        then have x_in_Scan_Gen: "x \<in> \<pi> k' {} (Scan T k (Gen(Prefixes p)))"
          using x_in_z by blast
        have "item_end x = k'" by (simp add: item_end_x_def)
        with x_in_Scan_Gen show ?case
          using items_le_def less.prems(12) mem_Collect_eq nat_le_linear by blast
    next
      case 2
        obtain i where i: "i = ladder_i L 0" by blast
        obtain i' where i': "i' = ladder_j L 0" by blast
        obtain \<alpha>' where \<alpha>': "\<alpha>' = ladder_\<gamma> \<alpha> D L 0" by blast
        obtain n where n: "n = ladder_n L 0" by blast
        have ldfix: "LeftDerivationFix \<alpha> i (take n D)  i' \<alpha>'"
          using LeftDerivationLadder_def \<alpha>' i i' n less.prems(8) by blast 
        have \<alpha>'_alt: "\<alpha>' = ladder_\<alpha> \<alpha> D L 1" using 2 by (simp add: \<alpha>' ladder_\<alpha>_def) 
        have i'_alt: "i' = ladder_i L 1" using 2 by (simp add: i' ladder_i_def)
        obtain e where e: "e = D ! n" by blast
        obtain ix where ix: "ix = ladder_ix L 1" by blast
        obtain m where m: "m = ladder_n L 1" by blast
        obtain E where E: "E = drop (Suc n) (take m D)" by blast
        have ldintro: "LeftDerivationIntro \<alpha>' i' (snd e) ix E (ladder_j L 1) (ladder_\<gamma> \<alpha> D L 1)"
          by (metis "2.hyps" LeftDerivationIntrosAt_def LeftDerivationIntros_def 
            LeftDerivationLadder_def One_nat_def \<alpha>'_alt E diff_Suc_1 e i'_alt ix leI 
            less.prems(8) m n not_less_eq zero_less_one)
        have is_nonterminal_\<alpha>'_at_i': "is_nonterminal (\<alpha>' ! i')"
          using LeftDerivationIntro_implies_nonterminal ldintro by blast   
        then have is_nonterminal_\<alpha>_at_i: "is_nonterminal (\<alpha> ! i)" 
          using LeftDerivationFix_def ldfix by auto
        then have "\<exists> A a1 a2 a1'. splits_at \<alpha> i a1 A a2 \<and> splits_at \<alpha>' i' a1' A a2 \<and>
          LeftDerivation a1 (take n D) a1'"
          using LeftDerivationFix_splits_at_nonterminal ldfix by auto
        then obtain A a1 a2 a1' where A: "splits_at \<alpha> i a1 A a2 \<and> splits_at \<alpha>' i' a1' A a2 \<and>
          LeftDerivation a1 (take n D) a1'" by blast
        have A_def: "A = \<alpha>' ! i'" using A splits_at_def by blast 
        have is_nonterminal_A: "is_nonterminal A" using A_def is_nonterminal_\<alpha>'_at_i' by blast
        have "\<exists> rule. e = (i', rule)"
          by (metis e "2.hyps" LeftDerivationIntrosAt_def LeftDerivationIntros_def 
            LeftDerivationLadder_def One_nat_def Suc_leI diff_Suc_1 i'_alt less.prems(8) 
            n prod.collapse zero_less_one) 
        then obtain rule where rule: "e = (i', rule)" by blast
        obtain w where w: "w = snd rule" by blast
        obtain \<alpha>'' where \<alpha>'': "\<alpha>'' = a1' @ w @ a2" by blast
        have \<alpha>'_\<alpha>'': "LeftDerives1 \<alpha>' i' rule \<alpha>''"
          by (metis A w LeftDerivationFix_is_sentence LeftDerivationIntro_def 
            LeftDerivationIntro_examine_rule LeftDerives1_def \<alpha>'' ldfix ldintro prod.collapse 
            rule snd_conv splits_at_implies_Derives1) 
        then have is_word_a1': "is_word a1'" using LeftDerives1_splits_at_is_word A by blast
        have A_eq_fst_rule: "A = fst rule"
          using A LeftDerivationIntro_examine_rule ldintro rule by fastforce 
        have ix_bound: "ix < length w" using ix w rule ldintro LeftDerivationIntro_def snd_conv 
          by auto      
        then have "\<exists> w1 W w2. splits_at w ix w1 W w2" using splits_at_def by blast 
        then obtain w1 W w2 where W: "splits_at w ix w1 W w2" by blast
        have a1'_w_a2: "a1'@w@a2 = ladder_stepdown_\<alpha>_0 \<alpha> D L" 
          using ladder_stepdown_\<alpha>_0_altdef "2.hyps" A \<alpha>'_alt e i'_alt less.prems(8) n rule 
          snd_conv w by force 
        from LeftDerivationLadder_stepdown[OF less.prems(8) 2] obtain L' where L':
          "LeftDerivationLadder (a1'@(w@a2)) (drop (ladder_stepdown_diff L) D) L'
           (terminals (drop r p @ [X])) \<and>
           length L' = length L - 1 \<and>
           ladder_i L' 0 = ladder_i L 1 + ladder_ix L 1 \<and> ladder_last_j L' = ladder_last_j L"
          using a1'_w_a2 by auto
        have ladder_i_L'_0: "ladder_i L' 0 = i' + ix" using L' i'_alt ix by auto
        have ladder_last_j_L': "ladder_last_j L' = length (drop r p)" using L' less.prems by auto
        from L' have this1: "LeftDerivationLadder (a1'@(w@a2)) (drop (ladder_stepdown_diff L) D) L'
           (terminals (drop r p @ [X]))" by blast
        have this2: "length a1' \<le> ladder_i L' 0" using A ladder_i_L'_0 splits_at_def by auto     
        from LeftDerivationLadder_cut_prefix[OF this1 is_word_a1' this2]
        obtain D' L'' \<gamma>' where L'':
          "terminals (drop r p @ [X]) = a1' @ \<gamma>' \<and>
            LeftDerivationLadder (w @ a2) D' L'' \<gamma>' \<and>
            D' = derivation_shift (drop (ladder_stepdown_diff L) D) (length a1') 0 \<and>
            length L'' = length L' \<and>
            ladder_i L'' 0 + length a1' = ladder_i L' 0 \<and> 
            ladder_last_j L'' + length a1' = ladder_last_j L'" by blast
        have length_a1'_bound: "length a1' \<le> length (drop r p)" using L'' ladder_last_j_L' 
          by linarith
        then have is_prefix_a1'_drop_r_p: "is_prefix a1' (terminals (drop r p))"
        proof -
          have f1: "\<forall>ss ssa ssb. \<not> is_prefix (ss::symbol list) (ssa @ ssb) \<or> is_prefix ss ssa \<or> (\<exists>ssc. ssc \<noteq> [] \<and> is_prefix ssc ssb \<and> ss = ssa @ ssc)"
            by (simp add: is_prefix_of_append)
          have f2: "\<And>ss ssa. is_prefix ((ss::symbol list) @ ssa) ss \<or> \<not> is_prefix ssa []"
            by (metis (no_types) append_Nil2 is_prefix_cancel)
          have f3: "\<And>ss. is_prefix ss [] \<or> \<not> is_prefix (terminals (drop r p) @ ss) a1'"
            by (metis (no_types) drop_eq_Nil is_prefix_append length_a1'_bound length_terminals)
          have "is_prefix a1' (a1' @ \<gamma>') \<and> is_prefix a1' a1'"
            by (metis (no_types) append_Nil2 is_prefix_cancel is_prefix_empty)
          then show ?thesis
            using f3 f2 f1 by (metis L'' terminals_append)
        qed 
        obtain r' where r': "r' = r + i'" by blast
        have length_a1'_eq_i': "length a1' = i'"
          using A less_or_eq_imp_le min.absorb2 splits_at_def by auto      
        have a1'_r': "r \<le> r' \<and> r' \<le> length p \<and> 
          terminals (drop r p) = a1' @ (terminals (drop r' p))"
          using is_prefix_a1'_drop_r_p r'
        proof -
          have "\<exists> q. terminals (drop r p) = a1' @ q"
            using is_prefix_a1'_drop_r_p by (metis is_prefix_unsplit)
          then obtain q where q: "terminals (drop r p) = a1' @ q" by blast
          have "q = drop i' (terminals (drop r p))"
            using length_a1'_eq_i' q by (simp add: append_eq_conv_conj)
          then have "q = terminals (drop i' (drop r p))" by simp
          then have "q = terminals (drop r' p)" by (simp add: r' add.commute)
          with q show ?thesis
            using add.commute diff_add_inverse le_Suc_ex le_add1 le_diff_conv length_a1'_bound 
              length_a1'_eq_i' length_drop r r' by auto
        qed    
        have ladder_i_L'': "ladder_i L'' 0 = ix" using L'' ladder_i_L'_0 length_a1'_eq_i' 
          add.commute add_left_cancel by linarith 
        have L''_ladder: "LeftDerivationLadder (w @ a2) D' L'' \<gamma>'" using L'' by blast
        have "ladder_i L'' 0 < length w" using ladder_i_L'' ix_bound by blast 
        from LeftDerivationLadder_cut_appendix[OF L''_ladder this] 
        obtain E' F' \<gamma>1' \<gamma>2' L''' where L''':
          "D' = E' @ F' \<and>
           \<gamma>' = \<gamma>1' @ \<gamma>2' \<and>
           LeftDerivationLadder w E' L''' \<gamma>1' \<and>
           derivation_ge F' (length \<gamma>1') \<and>
           LeftDerivation a2 (derivation_shift F' (length \<gamma>1') 0) \<gamma>2' \<and>
           length L''' = length L'' \<and> ladder_i L''' 0 = ladder_i L'' 0 \<and> 
           ladder_last_j L''' = ladder_last_j L''"
          by blast
        obtain z where z: "z = Item (A, w) (length w) (charslength (take r' p)) k'" by blast       
        have z1: "length L''' < length L" using "2.hyps" L' L'' L''' by linarith
        have z2: "p \<in> \<PP>" by (simp add: p_dom) 
        have z3: "charslength p = k" using p_charslength by auto 
        have z4: "X \<in> T" by (simp add: X_dom) 
        have z5: "T \<subseteq> \<X> k" by (simp add: less.prems(4)) 
        have "rule \<in> \<RR>"
          using Derives1_rule LeftDerives1_implies_Derives1 \<alpha>'_\<alpha>'' by blast 
        then have z6: "(A, w @ []) \<in> \<RR>" using w A_eq_fst_rule by auto
        have z7: "r' \<le> length p" using a1'_r' by linarith
        have "leftderives [\<SS>] ((terminals (take r p))@[N]@\<gamma>)"
          using leftderives_start by blast 
        then have "leftderives [\<SS>] ((terminals (take r p))@(\<alpha>@\<beta>)@\<gamma>)"
          by (metis \<PP>_wellformed is_derivation_def is_derivation_is_sentence is_sentence_concat 
            is_word_terminals_take leftderives_implies_derives leftderives_rule_step p_dom rule_dom)
        then have "leftderives [\<SS>] ((terminals (take r p))@a1@([A]@a2@\<beta>)@\<gamma>)"
          using A splits_at_combine append_assoc by fastforce 
        then have z8_helper: "leftderives [\<SS>] ((terminals (take r p))@a1'@([A]@a2@\<beta>)@\<gamma>)"
          by (meson A LeftDerivation_implies_leftderives \<PP>_wellformed is_derivation_def 
            is_derivation_is_sentence is_sentence_concat is_word_terminals_take 
            leftderives_implies_derives leftderives_trans_step p_dom)
        have join_terminals: "(terminals (take r p))@a1' = terminals (take r' p)"
          by (metis is_prefix_a1'_drop_r_p length_a1'_eq_i' r' take_add take_prefix 
            terminals_drop terminals_take)  
        from z8_helper join_terminals have z8: 
          "leftderives [\<SS>] (terminals (take r' p) @ [A] @ a2 @ \<beta> @ \<gamma>)"
          by (metis append_assoc) 
        have \<gamma>'_altdef: "\<gamma>' = terminals (drop r' p @ [X])"
          using L'' a1'_r' by auto
        have "ladder_last_j L''' + length a1' = length (drop r p)"
          using L'' L''' ladder_last_j_L' by linarith 
        then have ladder_last_j_L'''_\<gamma>': "ladder_last_j L''' = length \<gamma>' - 1"
          by (simp add: \<gamma>'_altdef length_a1'_eq_i' r')
        then have "length \<gamma>' - 1 < length \<gamma>1'"
          using L''' ladder_last_j_bound by fastforce 
        then have "length \<gamma>1' + length \<gamma>2' - 1 < length \<gamma>1'" 
          using L''' by simp
        then have "length \<gamma>2' = 0" by arith
        then have \<gamma>2': "\<gamma>2' = []" by simp
        then have \<gamma>1': "\<gamma>1' = terminals (drop r' p @ [X])" using \<gamma>'_altdef L''' by auto   
        then have z9: "LeftDerivationLadder w E' L''' (terminals (drop r' p @ [X]))"
          using L''' by blast
        have z10: "ladder_last_j L''' = length (drop r' p)" 
          using \<gamma>'_altdef ladder_last_j_L'''_\<gamma>' by auto
        note z11 = k'
        have z12: "z = Item (A, w @ []) (length w) (charslength (take r' p)) k'"
          using z by simp
        note z13 = less.prems(12)
        note induct = less.hyps(1)[of L''' A w "[]" r' "a2@\<beta>@\<gamma>" E' z]
        note z_in_I = induct[OF z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13]
        have a2_derives_empty: "derives a2 []" using L''' \<gamma>2'
          using LeftDerivation_implies_leftderives leftderives_implies_derives by blast 
        obtain x1 where x1: "x1 = Item (N, \<alpha>@\<beta>) (length a1) 
          (charslength (take r p)) (charslength (take r' p))" by blast
        obtain q where q: "q = take r' p" by blast
        then have is_prefix_q_p: "is_prefix q p" by simp 
        then have q_in_Prefixes: "q \<in> Prefixes p" using Prefixes_is_prefix by blast
        then have wellformed_q: "wellformed_tokens q"
          using p_dom is_prefix_q_p prefixes_are_paths' \<PP>_wellformed by blast   
        have item_rule_x1: "item_rule x1 = (N, \<alpha>@\<beta>)" 
          using x1 by simp
        have is_prefix_r_r': "is_prefix (take r p) (take r' p)"
          by (metis append_eq_conv_conj is_prefix_take r' take_add)          
        then have charslength_le_r_r': "charslength (take r p) \<le> charslength (take r' p)"
          using charslength_of_prefix by blast
        have "is_prefix (take r' p) p" by auto
        then have charslength_r'_p: "charslength (take r' p) \<le> charslength p"
          using charslength_of_prefix by blast
        have "charslength p \<le> length Doc"
          using less.prems(1) add_leE k' k'_upperbound z3 by blast
        with charslength_r'_p have charslength_r'_Doc: 
          "charslength (take r' p) \<le> length Doc" by arith
        have \<alpha>_decompose: "\<alpha> = a1 @ [A] @ a2" using A splits_at_combine by blast 
        have wellformed_x1: "wellformed_item x1"
          apply (auto simp add: wellformed_item_def)
          using item_rule_x1 less.prems apply auto[1]
          using charslength_le_r_r' x1 apply auto[1]
          using charslength_r'_Doc x1 apply auto[1]
          using x1 \<alpha>_decompose by simp
        have item_nonterminal_x1: "item_nonterminal x1 = N"
          by (simp add: x1 item_nonterminal_def)
        have r_q_p: "take r (terminals q) = terminals (take r p)"
          by (metis q is_prefix_r_r' length_take min.absorb2 r take_prefix terminals_take) 
        have item_\<alpha>_x1: "item_\<alpha> x1 = a1" by (simp add: \<alpha>_decompose item_\<alpha>_def x1)
        have a1': "a1' = drop r (terminals q)"
          by (metis append_eq_conv_conj join_terminals length_take length_terminals min.absorb2 q r)         
        have pvalid_q_x1: "pvalid q x1"
          apply (simp add: pvalid_def wellformed_q wellformed_x1 item_nonterminal_x1)
          apply (rule_tac x=r in exI)
          apply auto
          apply (simp add: a1'_r' min.absorb2 q)
          apply (simp add: q x1)
          apply (simp add: q x1 r')
          using r_q_p less.prems(7) append_Cons is_leftderivation_def 
            leftderivation_implies_derivation apply fastforce 
          apply (simp add: item_\<alpha>_x1)
          using a1' A LeftDerivation_implies_leftderives leftderives_implies_derives by blast 
        have item_end_x1_le_k': "item_end x1 \<le> k'"
          using charslength_r'_p
          apply (simp add: x1)
          using less.prems by auto
        have x1_in_I: "x1 \<in> I"
          apply (subst less.prems(12))
          apply (auto simp add: items_le_def item_end_x1_le_k')
          apply (rule \<pi>_apply_setmonotone)
          apply (rule Scan_apply_setmonotone)
          apply (simp add: Gen_def)
          apply (rule_tac x=q in exI)
          by (simp add: pvalid_q_x1 paths_le_def q_in_Prefixes)
        obtain x2 where x2: "x2 = inc_item x1 k'" by blast
        have x1_in_bin: "x1 \<in> bin I (item_origin z)"
          using bin_def x1 x1_in_I z12 by auto           
        have x2_in_Complete: "x2 \<in> Complete k' I"
          apply (simp add: Complete_def)
          apply (rule disjI2)
          apply (rule_tac x=x1 in exI)
          apply (simp add: x2)
          apply (rule_tac x=z in exI)
          apply auto
          using x1_in_bin apply blast
          using bin_def z12 z_in_I apply auto[1]
          apply (simp add: is_complete_def z12)
          by (simp add: \<alpha>_decompose is_complete_def item_nonterminal_def next_symbol_def x1 z12)
        have wf_I': "wellformed_items (\<pi> k' {} (Scan T k (Gen (Prefixes p))))"
          by (simp add: wellformed_items_Gen wellformed_items_Scan wellformed_items_\<pi> z5)
        from items_le_Complete[OF this] x2_in_Complete
        have x2_in_I: "x2 \<in> I" by (metis Complete_\<pi>_fix z13) 
        have "wellformed_items I"
          using wf_I' items_le_is_filter wellformed_items_def z13 by auto
        with x2_in_I have wellformed_x2: "wellformed_item x2" 
          by (simp add: wellformed_items_def)
        have item_dot_x2: "item_dot x2 = Suc (length a1)"
          by (simp add: x2 x1)
        have item_\<beta>_x2: "item_\<beta> x2 = a2 @ \<beta>"
          apply (simp add: item_\<beta>_def item_dot_x2)
          apply (simp add: item_rhs_def x2 x1 \<alpha>_decompose)
          done  
        have item_end_x2: "item_end x2 = k'" by (simp add: x2)
        note inc_dot_x2_by_a2 = thmD6[OF wellformed_x2 item_\<beta>_x2 item_end_x2 a2_derives_empty]
        have "x = inc_dot (length a2) x2"
          by (simp add: \<alpha>_decompose inc_dot_def less.prems(11) x1 x2)
        with inc_dot_x2_by_a2 have "x \<in> \<pi> k' {} {x2}" by auto
        then have "x \<in> \<pi> k' {} I" using x2_in_I
          by (meson contra_subsetD empty_subsetI insert_subset monoD mono_\<pi>)
        then show "x \<in> I"
          by (metis (no_types, lifting) \<pi>_subset_elem_trans dual_order.refl item_end_x_def 
            items_le_def items_le_is_filter mem_Collect_eq z13) 
    qed
qed       

theorem thmD10:
  assumes p_dom: "p \<in> \<PP>"
  assumes p_charslength: "charslength p = k"
  assumes X_dom: "X \<in> T"
  assumes T_dom: "T \<subseteq> \<X> k"
  assumes rule_dom: "(N, \<alpha>@\<beta>) \<in> \<RR>"
  assumes r: "r \<le> length p"
  assumes leftderives_start: "leftderives [\<SS>] ((terminals (take r p))@[N]@\<gamma>)"
  assumes leftderives_\<alpha>: "leftderives \<alpha> (terminals ((drop r p)@[X]))"
  assumes k': "k' = k + length (chars_of_token X)"
  assumes item_def: "x = Item (N, \<alpha>@\<beta>) (length \<alpha>) (charslength (take r p)) k'"
  assumes I: "I = items_le k' (\<pi> k' {} (Scan T k (Gen (Prefixes p))))"
  shows "x \<in> I"
proof -
  have "\<exists> D. LeftDerivation \<alpha> D (terminals ((drop r p)@[X]))"
    using leftderives_\<alpha> leftderives_implies_LeftDerivation by blast
  then obtain D where D: "LeftDerivation \<alpha> D (terminals ((drop r p)@[X]))" by blast
  have is_sentence: "is_sentence (terminals (drop r p @ [X]))"
    using derives_is_sentence is_sentence_concat leftderives_\<alpha> leftderives_implies_derives 
      rule_\<alpha>_type rule_dom by blast
  have "\<exists> L. LeftDerivationLadder \<alpha> D L  (terminals ((drop r p)@[X])) \<and>
         ladder_last_j L = length (drop r p)"
    apply (rule LeftDerivationLadder_exists)
    apply (rule D)
    apply (rule is_sentence)
    by auto
  then obtain L where L: "LeftDerivationLadder \<alpha> D L  (terminals ((drop r p)@[X]))" and
    L_ladder_last_j: "ladder_last_j L = length (drop r p)" by blast
  from thmD10_ladder[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7)
    L L_ladder_last_j k' item_def I]
  show ?thesis .
qed

end

end
