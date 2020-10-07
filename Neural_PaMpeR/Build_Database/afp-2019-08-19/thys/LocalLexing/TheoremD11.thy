theory TheoremD11
imports TheoremD10
begin

context LocalLexing begin

lemma LeftDerivationLadder_length_1:
  assumes ladder: "LeftDerivationLadder \<alpha> D L \<gamma>"
  assumes singleton_L: "length L = 1"
  shows "LeftDerivationFix \<alpha> (ladder_i L 0) D (ladder_last_j L) \<gamma>"
proof -
  have ldfix: "LeftDerivationFix \<alpha> (ladder_i L 0) (take (ladder_n L 0) D) (ladder_j L 0) 
    (ladder_\<gamma> \<alpha> D L 0)"
    using ladder LeftDerivationLadder_def by blast
  have ladder_n_0: "ladder_n L 0 = length D"
    using ladder singleton_L
    by (metis LeftDerivationLadder_def One_nat_def diff_Suc_1 is_ladder_def ladder_last_n_intro) 
  from ldfix ladder_n_0 ladder singleton_L show ?thesis
    by (metis Derivation_unique_dest LeftDerivationLadder_def 
      LeftDerivationLadder_implies_LeftDerivation_at_index LeftDerivationLadder_ladder_n_bound 
      LeftDerivation_implies_Derivation One_nat_def diff_Suc_1 ladder_last_j_def take_all 
      zero_less_one)
qed 

lemma LeftDerivationFix_from_singleton_helper:
  assumes "LeftDerivationFix [A] 0 D (length u) (u @ [B] @ v)"
  shows "D = []"
proof -
  from iffD1[OF LeftDerivationFix_def assms] obtain E F where EF:
    "is_sentence [A] \<and>
     is_sentence (u @ [B] @ v) \<and>
     LeftDerivation [A] D (u @ [B] @ v) \<and>
     0 < length [A] \<and>
     length u < length (u @ [B] @ v) \<and>
     [A] ! 0 = (u @ [B] @ v) ! length u \<and>
     D = E @ derivation_shift F 0 (Suc (length u)) \<and>
     LeftDerivation (take 0 [A]) E (take (length u) (u @ [B] @ v)) \<and>
     LeftDerivation (drop (Suc 0) [A]) F (drop (Suc (length u)) (u @ [B] @ v))"
    by blast
  from EF have E: "E = []"
    by (metis Derivation.elims(2) Derives1_split LeftDerivation_implies_Derivation 
      Nil_is_append_conv list.distinct(1) take_0) 
  from EF have F: "F = []"
    by (metis E LeftDerivation.simps(1) LeftDerivation_ge_take LeftDerivation_implies_Derivation 
      append_eq_conv_conj derivation_ge_shift is_word_Derivation length_Cons length_derivation_shift 
      list.size(3) nth_Cons_0 nth_append self_append_conv2 take_0)
  from EF E F show "D = []"  by auto  
qed

lemma LeftDerivationFix_from_singleton:
  assumes "LeftDerivationFix [A] i D j \<gamma>"
  shows "D = []"
proof -
  have "\<exists> u B v. splits_at \<gamma> j u B v"  using assms
    using LeftDerivationFix_splits_at_derives by blast
  then obtain u B v where s: "splits_at \<gamma> j u B v" by blast
  from s have s1: "\<gamma> = u @ [B] @ v" using splits_at_combine by blast
  from s have s2: "j = length u" using splits_at_def by auto
  from assms s1 s2 LeftDerivationFix_from_singleton_helper 
  show ?thesis by (metis LeftDerivationFix_def length_Cons less_Suc0 list.size(3))
qed

lemma LeftDerivationLadder_ladder_\<gamma>_last:
  assumes "LeftDerivationLadder \<alpha> D L \<gamma>"
  shows "\<gamma> = ladder_\<gamma> \<alpha> D L (length L - 1)"
by (metis Derive LeftDerivationLadder_def LeftDerivation_implies_Derivation One_nat_def assms 
  is_ladder_def last_ladder_\<gamma>)

theorem thmD11_helper:
  "p \<in> \<PP> \<Longrightarrow>
   charslength p = k \<Longrightarrow> 
   X \<in> T \<Longrightarrow>
   T \<subseteq> \<X> k \<Longrightarrow>
   q = p @ [X] \<Longrightarrow>
   (N, \<alpha>@\<beta>) \<in> \<RR> \<Longrightarrow>
   r \<le> length q \<Longrightarrow>
   LeftDerivation [\<SS>] D ((terminals (take r q))@[N]@\<gamma>) \<Longrightarrow>
   leftderives \<alpha> (terminals (drop r q)) \<Longrightarrow>
   k' = k + length (chars_of_token X) \<Longrightarrow>
   x = Item (N, \<alpha>@\<beta>) (length \<alpha>) (charslength (take r q)) k' \<Longrightarrow>
   I = items_le k' (\<pi> k' {} (Scan T k (Gen (Prefixes p)))) \<Longrightarrow>
   x \<in> I"
proof (induct "length D" arbitrary: D r N \<gamma> \<alpha> \<beta> x rule: less_induct)
  case less
    have "D = [] \<or> D \<noteq> []" by blast
    then show ?case 
    proof (induct rule: disjCases2)
      case 1
        then have r: "r = 0"
          by (metis LeftDerivation.simps(1) diff_add_0 diff_add_inverse2 le_0_eq length_0_conv 
            length_append length_terminals less.prems(7) less.prems(8) list.size(4) take_eq_Nil)
        with 1 have \<gamma>: "\<gamma> = []"
          using LeftDerivation.simps(1) append_Cons append_self_conv2 less.prems(8) list.inject 
            take_eq_Nil terminals_empty by auto 
        from r \<gamma> 1 have start_is_N: "\<SS> = N"
          using LeftDerivation.simps(1) append_eq_Cons_conv less.prems(8) list.inject take_eq_Nil 
            terminals_empty by auto   
        have h1: "r \<le> length p" using r by auto
        have h2: "leftderives [\<SS>] (terminals (take r p) @ [N] @ \<gamma>)" 
          by (simp add: r \<gamma> start_is_N)
        have h3: "leftderives \<alpha> (terminals (drop r p @ [X]))"
          using "less.prems" by (simp add: r "less.prems")
        have h4: "x = Item (N, \<alpha> @ \<beta>) (length \<alpha>) (charslength (take r p)) k'"
          using "less.prems" by (simp add: r "less.prems") 
        from thmD10[OF "less.prems"(1, 2, 3, 4, 6) h1 h2 h3 "less.prems"(10) h4  "less.prems"(12)]
        show ?case .
    next 
      case 2
        note D_non_empty = 2
        have "r < length q \<or> r = length q" using less by arith
        then show ?case
        proof (induct rule: disjCases2)
          case 1
            have h1: "r \<le> length p" using less.prems 1 by auto
            have take_q_p: "take r q = take r p"
              using 1 less.prems
              by (simp add: drop_keep_last le_neq_implies_less nat_le_linear not_less_eq not_less_eq_eq) 
            have h2: "leftderives [\<SS>] (terminals (take r p) @ [N] @ \<gamma>)"
              apply (simp only: take_q_p[symmetric])
              using less.prems LeftDerivation_implies_leftderives by blast
            have h3: "leftderives \<alpha> (terminals (drop r p @ [X]))"
              using less.prems(5, 9) h1 by simp
            have h4: "k' = k + length (chars_of_token X)" using less.prems by blast
            have h5: "x = Item (N, \<alpha> @ \<beta>) (length \<alpha>) (charslength (take r p)) k'"
            using less.prems take_q_p by simp
            from thmD10[OF "less.prems"(1, 2, 3, 4, 6) h1 h2 h3 h4 h5 less.prems(12)] show ?case .
        next
          case 2
            from 2 have ld: "LeftDerivation [\<SS>] D (terminals q @ [N] @ \<gamma>)"
              using less.prems(8) by auto
            from 2 have \<alpha>_derives_empty: "derives \<alpha> []"
              using less.prems(9) by auto
            have is_sentence_p: "is_sentence (terminals p)"
              using less.prems(1) \<L>\<^sub>P_derives \<PP>_are_admissible admissible_def is_derivation_def 
                is_derivation_is_sentence is_sentence_concat by blast
            have is_symbol_X: "is_symbol (terminal_of_token X)"
              using less.prems(3, 4) \<X>_are_terminals is_symbol_def rev_subsetD by blast      
            have is_sentence_q: "is_sentence (terminals q)" using is_sentence_p is_symbol_X 
              less.prems LeftDerivation_implies_leftderives is_derivation_def 
              is_derivation_is_sentence is_sentence_concat ld leftderives_implies_derives by blast
            have is_symbol_N: "is_symbol N" 
              using less.prems(6) is_symbol_def rule_nonterminal_type by blast 
            have is_sentence_\<gamma>: "is_sentence \<gamma>"
              by (meson LeftDerivation_implies_leftderives is_derivation_def is_derivation_is_sentence 
                is_sentence_concat ld leftderives_implies_derives) 
            have ld_exists_h1: "is_sentence (terminals q @ [N] @ \<gamma>)"
              using is_sentence_q is_sentence_\<gamma> is_symbol_N is_sentence_concat 
                LeftDerivation_implies_leftderives is_derivation_def is_derivation_is_sentence ld 
                leftderives_implies_derives by blast
            have ld_exists_h2: "length q < length (terminals q @ [N] @ \<gamma>)" by simp
            from LeftDerivationLadder_exists[OF ld ld_exists_h1 ld_exists_h2] obtain L where 
              L: "LeftDerivationLadder [\<SS>] D L (terminals q @ [N] @ \<gamma>)" and 
              L_last_j: "ladder_last_j L = length q" by blast
            note r_eq_length_q = 2
            have ladder_i_0_eq_0: "ladder_i L 0 = 0" using L append_Nil ladder_i_0_bound 
              length_append_singleton less_Suc0 list.size(3) by fastforce          
            have "length L = 1 \<or> length L > 1" using L
              by (metis LeftDerivationLadder_def Suc_eq_plus1 Suc_eq_plus1_left butlast_conv_take 
                butlast_snoc diff_add_inverse2 is_ladder_def le_add1 le_neq_implies_less 
                length_append_singleton old.nat.exhaust take_0)
            then show ?case
            proof (induct rule: disjCases2)
              case 1
                from LeftDerivationLadder_length_1[OF L 1] ladder_i_0_eq_0 
                have ldfix: "LeftDerivationFix [\<SS>] 0 D (ladder_last_j L) (terminals q @ [N] @ \<gamma>)"
                  by auto
                with LeftDerivationFix_from_singleton have "D = []" by blast
                with D_non_empty have "False" by auto
                then show ?case by blast
            next
              case 2
                obtain a where a: "a = ladder_\<alpha> [\<SS>] D L (length L - 1)" by blast
                then have a_as_\<gamma>: "a = ladder_\<gamma> [\<SS>] D L (length L - 2)" using 2 ladder_\<alpha>_def
                  by (metis diff_diff_left diff_is_0_eq not_le one_add_one)
                have introsAt: "LeftDerivationIntrosAt [\<SS>] D L (length L - 1)" using L
                  by (metis "2.hyps" LeftDerivationIntros_def LeftDerivationLadder_def One_nat_def 
                    Suc_leI Suc_lessD diff_less less_not_refl not_less_eq zero_less_diff)
                obtain i where i: "i = ladder_i L (length L - 1)" by blast
                obtain j where j: "j = ladder_j L (length L - 1)" by blast
                obtain ix where ix: "ix = ladder_ix L (length L - 1)" by blast
                obtain c where c: "c = ladder_\<gamma> [\<SS>] D L (length L - 1)" by blast
                obtain n where n: "n = ladder_n L (length L - 1 - 1)" by blast
                obtain m where m: "m = ladder_n L (length L - 1)" by blast
                obtain e where e: "e = D ! n" by blast
                obtain E where E: "E = drop (Suc n) (take m D)" by blast
                from iffD1[OF LeftDerivationIntrosAt_def introsAt]  
                have "i = fst e \<and> LeftDerivationIntro a i (snd e) ix E j c"
                  by (metis E a c e i ix j m n)
                then have i_eq_fst_e: "i = fst e" and 
                  ldintro: "LeftDerivationIntro a i (snd e) ix E j c" by auto
                have c_def: "c = terminals q @ [N] @ \<gamma>" 
                  using c L LeftDerivationLadder_ladder_\<gamma>_last by simp            
                from iffD1[OF LeftDerivationIntro_def ldintro] obtain b where b:
                  "LeftDerives1 a i (snd e) b \<and> ix < length (snd (snd e)) \<and> 
                   snd (snd e) ! ix = c ! j \<and> LeftDerivationFix b (i + ix) E j c" by blast
                obtain M \<omega> where M\<omega>: "(M, \<omega>) = snd e" using prod.collapse by blast 
                have j_q: "j = length q" using L_last_j j ladder_last_j_def by auto
                with c_def have c_at_j: "c ! j = N"
                  by (metis append_Cons length_terminals nth_append_length)  
                with b M\<omega> have \<omega>_at_ix: "\<omega> ! ix = N" by (metis snd_conv)
                obtain \<mu>1 \<mu>2 where split_\<omega>: "splits_at \<omega> ix \<mu>1 N \<mu>2"
                  by (metis M\<omega> \<omega>_at_ix b snd_conv splits_at_def)
                obtain a1 a2 where split_a: "splits_at a i a1 M a2" using b
                  by (metis LeftDerivationIntro_bounds_ij LeftDerivationIntro_examine_rule M\<omega> 
                   fst_conv ldintro splits_at_def)
                then have is_word_a1: "is_word a1"
                  using LeftDerives1_splits_at_is_word b by blast 
                have "b = a1 @ \<omega> @ a2" using split_a b M\<omega>
                  by (metis LeftDerives1_implies_Derives1 snd_conv splits_at_combine_dest) 
                then have b_def: "b = a1 @ \<mu>1 @ [N] @ \<mu>2 @ a2" using split_\<omega> splits_at_combine 
                  by simp
                have is_nonterminal_N: "is_nonterminal N"
                  using less.prems(6) rule_nonterminal_type by blast 
                with LeftDerivationFix_splits_at_nonterminal split_a b 
                have "\<exists> U b1 b2 c1. splits_at b (i + ix) b1 U b2 \<and> splits_at c j c1 U b2 \<and>
                  LeftDerivation b1 E c1" by (simp add: LeftDerivationFix_def c_at_j)
                then obtain b1 b2 c1 where b1b2c1:
                  "splits_at b (i + ix) b1 N b2 \<and> splits_at c j c1 N b2 \<and>
                   LeftDerivation b1 E c1" using c_at_j splits_at_def by auto 
                then have c1_q: "c1 = terminals q" using c_def j_q
                  by (simp add: append_eq_conv_conj splits_at_def) 
                have length_a1_eq_i: "length a1 = i" using split_a splits_at_def by auto 
                have length_\<mu>1_eq_ix: "length \<mu>1 = ix" using split_\<omega> splits_at_def by auto
                have "b1 = take (i + ix) b" using b1b2c1 splits_at_def by blast 
                then have b1_eq_a1_\<mu>1: "b1 = a1 @ \<mu>1" using b_def length_a1_eq_i length_\<mu>1_eq_ix
                  by (simp add: append_eq_conv_conj take_add)
                have "LeftDerivation (a1 @ \<mu>1) E c1" using b1b2c1 b1_eq_a1_\<mu>1 by blast
                from LeftDerivation_skip_prefixword_ex[OF this is_word_a1]
                obtain w where w: "c1 = a1 @ w \<and> 
                  LeftDerivation \<mu>1 (derivation_shift E (length a1) 0) w" by blast
                have a1_eq_take_i: "a1 = take i (terminals q)"
                  using w c1_q split_a append_eq_conv_conj length_a1_eq_i by blast 
                have \<mu>1_leftderives: "leftderives \<mu>1 (terminals (drop i q))" using w c1_q split_a 
                  LeftDerivation_implies_leftderives append_eq_conv_conj length_a1_eq_i by auto
                have "LeftDerivation [\<SS>] (take n D) a"
                  by (metis "2.hyps" L LeftDerivationLadder_implies_LeftDerivation_at_index 
                    One_nat_def Suc_lessD a_as_\<gamma> diff_Suc_eq_diff_pred diff_Suc_less n numeral_2_eq_2) 
                then have LD_to_M: "LeftDerivation [\<SS>] (take n D) ((terminals (take i q))@[M]@a2)"
                  using split_a splits_at_combine a1_eq_take_i terminals_take by auto
                have is_ladder: "is_ladder D L" using L by (simp add: LeftDerivationLadder_def)
                then have n_less_m: "n < m" using n m is_ladder_def
                  by (metis (no_types, lifting) "2.hyps" One_nat_def diff_Suc_less 
                    length_greater_0_conv zero_less_diff) 
                have m_le_D: "m \<le> length D" using m is_ladder_def is_ladder dual_order.refl 
                  ladder_n_last_is_length by auto 
                have "length (take n D) = n" using  n_less_m m_le_D
                  using length_take less_irrefl less_le_trans linear min.absorb2 by auto 
                then have length_take_n_D: "length (take n D) < length D" 
                  using n_less_m m_le_D less_le_trans by linarith 
                have \<omega>_decompose: "\<omega> = \<mu>1@(N#\<mu>2)" using split_\<omega> splits_at_combine by simp
                have "(M, \<omega>) \<in> \<RR>" by (metis Derives1_rule LeftDerives1_implies_Derives1 M\<omega> b) 
                with \<omega>_decompose have M_rule: "(M, \<mu>1@(N#\<mu>2)) \<in> \<RR>" by simp
                have i_le_q: "i \<le> length q" using a1_eq_take_i length_a1_eq_i by auto 
                obtain y where 
                  y: "y = Item (M, \<mu>1 @ N # \<mu>2) (length \<mu>1) (charslength (take i q)) k'" by blast
                from less.hyps[OF length_take_n_D less.prems(1, 2, 3, 4, 5) M_rule i_le_q LD_to_M
                   \<mu>1_leftderives less.prems(10) y less.prems(12)]
                have y_in_I: "y \<in> I" by blast
                obtain z where z: "z = Item (N, \<alpha>@\<beta>) 0 k' k'" by blast
                then have z_is_init_item: "z = init_item (N, \<alpha>@\<beta>) k'" by (simp add: init_item_def) 
                have "z \<in> Predict k' {y}"
                  apply (simp add: z_is_init_item)
                  apply (rule next_symbol_predicts)
                  apply (simp add: is_complete_def next_symbol_def y)
                  apply (simp add: less.prems(6))
                  apply (simp add: y item_end_def)
                  done
                then have "z \<in> Predict k' I" using Predict_def bin_def y_in_I by auto
                then have z_in_I: "z \<in> I" by (metis Predict_\<pi>_fix items_le_Predict less.prems(12)) 
                have length_chars_q: "length (chars q) = k'" using less.prems by simp
                have x_is_inc_dot: "x = inc_dot (length \<alpha>) z"
                  by (simp add: less.prems(11) r_eq_length_q length_chars_q z inc_dot_def)
                have wellformed_items_I: "wellformed_items I"
                  apply (subst less.prems(12))
                  by (meson LocalLexing.items_le_is_filter LocalLexing.wellformed_items_Gen 
                    LocalLexing_axioms empty_subsetI less.prems(4) subsetCE wellformed_items_Scan 
                    wellformed_items_\<pi> wellformed_items_def)
                with z_in_I have wellformed_z: "wellformed_item z" 
                  using wellformed_items_def by blast   
                have item_\<beta>_z: "item_\<beta> z = \<alpha>@\<beta>" by (simp add: z_is_init_item) 
                have item_end_z: "item_end z = k'" by (simp add: z_is_init_item)               
                have "x \<in> \<pi> k' {} {z}"
                  apply (simp add: x_is_inc_dot)
                  apply (rule thmD6)
                  apply (rule wellformed_z)
                  apply (rule item_\<beta>_z)
                  apply (rule item_end_z)
                  by (simp add: \<alpha>_derives_empty) 
                then have "x \<in> \<pi> k' {} I" using z_in_I
                  by (meson contra_subsetD empty_subsetI insert_subset monoD mono_\<pi>) 
                then show ?case
                  by (metis (no_types, lifting) LocalLexing.wellformed_item_def LocalLexing_axioms 
                    \<pi>_subset_elem_trans item.sel(3) item.sel(4) items_le_def items_le_is_filter 
                    less.prems(11) less.prems(12) mem_Collect_eq wellformed_z z)
            qed
        qed
    qed    
qed

theorem thmD11:
  assumes p_dom: "p \<in> \<PP>"
  assumes p_charslength: "charslength p = k"
  assumes X_dom: "X \<in> T"
  assumes T_dom: "T \<subseteq> \<X> k"
  assumes q_def: "q = p @ [X]"
  assumes rule_dom: "(N, \<alpha>@\<beta>) \<in> \<RR>"
  assumes r: "r \<le> length q"
  assumes leftderives_start: "leftderives [\<SS>] ((terminals (take r q))@[N]@\<gamma>)"
  assumes leftderives_\<alpha>: "leftderives \<alpha> (terminals (drop r q))"
  assumes k': "k' = k + length (chars_of_token X)"
  assumes item_def: "x = Item (N, \<alpha>@\<beta>) (length \<alpha>) (charslength (take r q)) k'"
  assumes I: "I = items_le k' (\<pi> k' {} (Scan T k (Gen (Prefixes p))))"
  shows "x \<in> I"
proof -
  have "\<exists> D. LeftDerivation  [\<SS>] D ((terminals (take r q))@[N]@\<gamma>)"
    using leftderives_start leftderives_implies_LeftDerivation by blast 
  then obtain D where D: "LeftDerivation  [\<SS>] D ((terminals (take r q))@[N]@\<gamma>)" by blast
  from thmD11_helper[OF assms(1, 2, 3, 4, 5, 6, 7) D assms(9, 10, 11, 12)]
  show ?thesis .
qed

end

end
