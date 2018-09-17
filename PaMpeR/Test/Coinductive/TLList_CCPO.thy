(*  Title:       TLList_CCPO.thy
    Author:      Andreas Lochbihler, ETH Zurich
*)

section {* Ccpo structure for terminated lazy lists *}

theory TLList_CCPO imports TLList begin

lemma Set_is_empty_parametric [transfer_rule]:
  includes lifting_syntax
  shows "(rel_set A ===> (=)) Set.is_empty Set.is_empty"
by(auto simp add: rel_fun_def Set.is_empty_def dest: rel_setD1 rel_setD2)

lemma monotone_comp: "\<lbrakk> monotone orda ordb g; monotone ordb ordc f \<rbrakk> \<Longrightarrow> monotone orda ordc (f \<circ> g)"
by(rule monotoneI)(simp add: monotoneD)

lemma cont_comp: "\<lbrakk> mcont luba orda lubb ordb g; cont lubb ordb lubc ordc f \<rbrakk> \<Longrightarrow> cont luba orda lubc ordc (f \<circ> g)"
apply(rule contI)
apply(frule (2) mcont_contD)
apply(simp)
apply(drule (1) contD[OF _ chain_imageI])
  apply(erule (1) mcont_monoD)
apply(simp_all add: image_image o_def)
done

lemma mcont_comp: "\<lbrakk> mcont luba orda lubb ordb g; mcont lubb ordb lubc ordc f \<rbrakk> \<Longrightarrow> mcont luba orda lubc ordc (f \<circ> g)"
by(auto simp add: mcont_def intro: cont_comp monotone_comp)

context includes lifting_syntax
begin

lemma monotone_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total A"
  shows "((A ===> A ===> (=)) ===> (B ===> B ===> (=)) ===> (A ===> B) ===> (=)) monotone monotone"
unfolding monotone_def[abs_def] by transfer_prover

lemma cont_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total A" "bi_unique B"
  shows "((rel_set A ===> A) ===> (A ===> A ===> (=)) ===> (rel_set B ===> B) ===> (B ===> B ===> (=)) ===> (A ===> B) ===> (=)) cont cont"
unfolding cont_def[abs_def] Set.is_empty_def[symmetric] by transfer_prover

lemma mcont_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total A" "bi_unique B"
  shows "((rel_set A ===> A) ===> (A ===> A ===> (=)) ===> (rel_set B ===> B) ===> (B ===> B ===> (=)) ===> (A ===> B) ===> (=)) mcont mcont"
unfolding mcont_def[abs_def] by transfer_prover

end

lemma (in ccpo) Sup_Un_less:
  assumes chain: "Complete_Partial_Order.chain (\<le>) (A \<union> B)"
  and AB: "\<forall>x\<in>A. \<exists>y\<in>B. x \<le> y"
  shows "Sup (A \<union> B) = Sup B"
proof(rule antisym)
  from chain have chain': "Complete_Partial_Order.chain (\<le>) B"
    by(blast intro: chain_subset)
  show "Sup (A \<union> B) \<le> Sup B" using chain
  proof(rule ccpo_Sup_least)
    fix x
    assume "x \<in> A \<union> B"
    thus "x \<le> Sup B"
    proof
      assume "x \<in> A"
      then obtain y where "x \<le> y" "y \<in> B" using AB by blast
      note `x \<le> y`
      also from chain' `y \<in> B` have "y \<le> Sup B" by(rule ccpo_Sup_upper)
      finally show ?thesis .
    qed(rule ccpo_Sup_upper[OF chain'])
  qed
  show "Sup B \<le> Sup (A \<union> B)"
    using chain chain' by(blast intro: ccpo_Sup_least ccpo_Sup_upper)
qed

subsection {* The ccpo structure *}

context includes tllist.lifting fixes b :: 'b begin

lift_definition tllist_ord :: "('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist \<Rightarrow> bool"
is "\<lambda>(xs1, b1) (xs2, b2). if lfinite xs1 then b1 = b \<and> lprefix xs1 xs2 \<or> xs1 = xs2 \<and> flat_ord b b1 b2 else xs1 = xs2"
by auto

lift_definition tSup :: "('a, 'b) tllist set \<Rightarrow> ('a, 'b) tllist"
is "\<lambda>A. (lSup (fst ` A), flat_lub b (snd ` (A \<inter> {(xs, _). lfinite xs})))"
proof goal_cases
  case (1 A1 A2)
  hence "fst ` A1 = fst ` A2" "snd ` (A1 \<inter> {(xs, _). lfinite xs}) = snd ` (A2 \<inter> {(xs, _). lfinite xs})"
    by(auto 4 3 simp add: rel_set_def intro: rev_image_eqI)
  thus ?case by simp
qed

lemma tllist_ord_simps [simp, code]: (* FIXME: does not work with transfer *)
  shows tllist_ord_TNil_TNil: "tllist_ord (TNil b1) (TNil b2) \<longleftrightarrow> flat_ord b b1 b2"
  and tllist_ord_TNil_TCons: "tllist_ord (TNil b1) (TCons y ys) \<longleftrightarrow> b1 = b"
  and tllist_ord_TCons_TNil: "tllist_ord (TCons x xs) (TNil b2) \<longleftrightarrow> False"
  and tllist_ord_TCons_TCons: "tllist_ord (TCons x xs) (TCons y ys) \<longleftrightarrow> x = y \<and> tllist_ord xs ys"
by(auto simp add: tllist_ord.rep_eq flat_ord_def)

lemma tllist_ord_refl [simp]: "tllist_ord xs xs"
by transfer(auto simp add: flat_ord_def)

lemma tllist_ord_antisym: "\<lbrakk> tllist_ord xs ys; tllist_ord ys xs \<rbrakk> \<Longrightarrow> xs = ys"
by transfer(auto simp add: flat_ord_def split: if_split_asm intro: lprefix_antisym)

lemma tllist_ord_trans [trans]: "\<lbrakk> tllist_ord xs ys; tllist_ord ys zs \<rbrakk> \<Longrightarrow> tllist_ord xs zs"
by transfer(auto simp add: flat_ord_def split: if_split_asm intro: lprefix_trans)

lemma chain_tllist_llist_of_tllist:
  assumes "Complete_Partial_Order.chain tllist_ord A"
  shows "Complete_Partial_Order.chain lprefix (llist_of_tllist ` A)"
by(rule chainI)(auto 4 3 simp add: tllist_ord.rep_eq split: if_split_asm dest: chainD[OF assms])

lemma chain_tllist_terminal:
  assumes "Complete_Partial_Order.chain tllist_ord A"
  shows "Complete_Partial_Order.chain (flat_ord b) {terminal xs|xs. xs \<in> A \<and> tfinite xs}"
by(rule chainI)(auto simp add: tllist_ord.rep_eq flat_ord_def dest: chainD[OF assms])

lemma flat_ord_chain_finite:
  assumes "Complete_Partial_Order.chain (flat_ord b) A"
  shows "finite A"
proof -
  from assms have "\<exists>z. \<forall>x\<in>A. x = b \<or> x = z"
    by(clarsimp simp add: chain_def flat_ord_def) metis
  then obtain z where "\<And>x. x \<in> A \<Longrightarrow> x = b \<or> x = z" by blast
  hence "A \<subseteq> {b, z}" by auto
  thus ?thesis by(rule finite_subset) simp
qed

lemma tSup_empty [simp]: "tSup {} = TNil b"
by(transfer)(simp add: flat_lub_def)

lemma is_TNil_tSup [simp]: "is_TNil (tSup A) \<longleftrightarrow> (\<forall>x\<in>A. is_TNil x)"
by transfer(simp add: split_beta)

lemma chain_tllist_ord_tSup:
  assumes chain: "Complete_Partial_Order.chain tllist_ord A"
  and A: "xs \<in> A"
  shows "tllist_ord xs (tSup A)"
proof(cases "tfinite xs")
  case True
  show ?thesis
  proof(cases "llist_of_tllist xs = llist_of_tllist (tSup A)")
    case True
    with `tfinite xs` have "lfinite (lSup (llist_of_tllist ` A))"
      by(simp add: tSup_def image_image)
    hence "terminal (tSup A) = flat_lub b {terminal xs|xs. xs \<in> A \<and> tfinite xs}" (is "_ = flat_lub _ ?A")
      by(simp add: tSup_def terminal_tllist_of_llist image_image)(auto intro: rev_image_eqI intro!: arg_cong[where f="flat_lub b"])
    moreover have "flat_ord b (terminal xs) (flat_lub b ?A)"
      by(rule ccpo.ccpo_Sup_upper[OF Partial_Function.ccpo[OF flat_interpretation]])(blast intro: chain_tllist_terminal[OF chain] A `tfinite xs`)+
    ultimately show ?thesis using True by(simp add: tllist_ord.rep_eq)
  next
    case False
    hence "\<exists>ys\<in>A. \<not> tllist_ord ys xs"
      by(rule contrapos_np)(auto intro!: lprefix_antisym chain_lSup_lprefix chain_lprefix_lSup simp add: tSup_def image_image A chain_tllist_llist_of_tllist[OF chain] tllist_ord.rep_eq split: if_split_asm)
    then obtain ys where "ys \<in> A" "\<not> tllist_ord ys xs" by blast
    with A have "tllist_ord xs ys" "xs \<noteq> ys" by(auto dest: chainD[OF chain])
    with True have "terminal xs = b" by transfer(auto simp add: flat_ord_def)
    with True False show ?thesis
      by(simp add: tllist_ord.rep_eq tSup_def image_image chain_lprefix_lSup chain_tllist_llist_of_tllist chain A)
  qed
next
  case False
  thus ?thesis using assms by(simp add: tllist_ord.rep_eq tSup_def image_image chain_lprefix_lSup chain_tllist_llist_of_tllist not_lfinite_lprefix_conv_eq[THEN iffD1] terminal_tllist_of_llist split: if_split_asm)
qed

lemma chain_tSup_tllist_ord:
  assumes chain: "Complete_Partial_Order.chain tllist_ord A"
  and lub: "\<And>xs'. xs' \<in> A \<Longrightarrow> tllist_ord xs' xs"
  shows "tllist_ord (tSup A) xs"
proof -
  have "\<And>xs'. xs' \<in> llist_of_tllist ` A \<Longrightarrow> lprefix xs' (llist_of_tllist xs)"
    by(auto dest!: lub simp add: tllist_ord.rep_eq split: if_split_asm)
  with chain_tllist_llist_of_tllist[OF chain]
  have prefix: "lprefix (lSup (llist_of_tllist ` A)) (llist_of_tllist xs)"
    by(rule chain_lSup_lprefix)

  show ?thesis
  proof(cases "tfinite (tSup A)")
    case False thus ?thesis using prefix
      by(simp add: tllist_ord.rep_eq tSup_def image_image not_lfinite_lprefix_conv_eq[THEN iffD1])
  next
    case True
    from True have fin: "lfinite (lSup (llist_of_tllist ` A))" by(simp add: tSup_def image_image)
    have eq: "terminal (tSup A) = flat_lub b {terminal xs|xs. xs \<in> A \<and> tfinite xs}" (is "_ = flat_lub _ ?A")
      by(simp add: tSup_def terminal_tllist_of_llist image_image fin)(auto intro: rev_image_eqI intro!: arg_cong[where f="flat_lub b"])
    
    show ?thesis
    proof(cases "lprefix (llist_of_tllist xs) (lSup (llist_of_tllist ` A))")
      case True
      with prefix have "lSup (llist_of_tllist ` A) = llist_of_tllist xs" by(rule lprefix_antisym)
      moreover have "flat_ord b (flat_lub b ?A) (terminal xs)"
        by(rule ccpo.ccpo_Sup_least[OF Partial_Function.ccpo[OF flat_interpretation]])(auto intro: chain_tllist_terminal[OF chain] dest: lub simp add: tllist_ord.rep_eq flat_ord_def)
      ultimately show ?thesis using eq by(simp add: tllist_ord.rep_eq tSup_def image_image)
    next
      case False
      { fix xs'
        assume "xs' \<in> A"
        with False have "\<not> lprefix (llist_of_tllist xs) (llist_of_tllist xs')"
          by-(erule contrapos_nn, auto 4 4 intro: lprefix_trans chain_lprefix_lSup chain_tllist_llist_of_tllist chain)
        with lub[OF `xs' \<in> A`] have "terminal xs' = b"
          by(auto simp add: tllist_ord.rep_eq split: if_split_asm) }
      with chain_tllist_terminal[OF chain] have "flat_ord b (flat_lub b ?A) b"
        by -(rule ccpo.ccpo_Sup_least[OF Partial_Function.ccpo[OF flat_interpretation]], auto simp add: flat_ord_def)
      hence "flat_lub b ?A = b" by(simp add: flat_ord_def)
      thus ?thesis using True eq prefix
        by(simp add: tSup_def terminal_tllist_of_llist tllist_ord.rep_eq image_image)
    qed
  qed
qed

lemma tllist_ord_ccpo [simp, cont_intro]:
  "class.ccpo tSup tllist_ord (mk_less tllist_ord)"
by unfold_locales(auto simp add: mk_less_def intro: tllist_ord_antisym tllist_ord_trans chain_tllist_ord_tSup chain_tSup_tllist_ord)

lemma tllist_ord_partial_function_definitions: "partial_function_definitions tllist_ord tSup"
by unfold_locales(auto simp add: mk_less_def intro: tllist_ord_antisym tllist_ord_trans chain_tllist_ord_tSup chain_tSup_tllist_ord)

interpretation tllist: partial_function_definitions "tllist_ord" "tSup"
by(rule tllist_ord_partial_function_definitions)

lemma admissible_mcont_is_TNil [THEN admissible_subst, cont_intro, simp]:
  shows admissible_is_TNil: "ccpo.admissible tSup tllist_ord is_TNil"
by(rule ccpo.admissibleI)(simp)

lemma terminal_tSup:
  "\<forall>xs\<in>Y. is_TNil xs \<Longrightarrow> terminal (tSup Y) = flat_lub b (terminal ` Y)"
including tllist.lifting
apply(transfer)
apply(clarsimp simp add: split_def)
apply(rule arg_cong[where f="flat_lub b"])
apply(auto simp add: split_def)
done

lemma thd_tSup:
  "\<exists>xs \<in> Y. \<not> is_TNil xs
  \<Longrightarrow> thd (tSup Y) = (THE x. x \<in> thd ` (Y \<inter> {xs. \<not> is_TNil xs}))"
apply(simp add: tSup_def image_image)
apply(rule arg_cong[where f=The])
apply(auto intro: rev_image_eqI intro!: ext)
done

lemma ex_TCons_raw_parametric:
  includes lifting_syntax
  shows "(rel_set (rel_prod (llist_all2 A) B) ===> (=)) (\<lambda>Y. \<exists>(xs, b) \<in> Y. \<not> lnull xs) (\<lambda>Y. \<exists>(xs, b) \<in> Y. \<not> lnull xs)"
by(auto 4 4 simp add: rel_fun_def dest: rel_setD1 rel_setD2 llist_all2_lnullD intro: rev_bexI)

lift_definition ex_TCons :: "('a, 'b) tllist set \<Rightarrow> bool"
is "\<lambda>Y. \<exists>(xs, b) \<in> Y. \<not> lnull xs" parametric ex_TCons_raw_parametric
by (blast dest: rel_setD1 rel_setD2)+

lemma ex_TCons_iff: "ex_TCons Y \<longleftrightarrow> (\<exists>xs \<in> Y. \<not> is_TNil xs)"
by transfer auto

lemma retain_TCons_raw_parametric:
  includes lifting_syntax
  shows "(rel_set (rel_prod (llist_all2 A) B) ===> rel_set (rel_prod (llist_all2 A) B))
    (\<lambda>A. A \<inter> {(xs, b). \<not> lnull xs}) (\<lambda>A. A \<inter> {(xs, b). \<not> lnull xs})"
by(rule rel_funI rel_setI)+(auto 4 4 dest: llist_all2_lnullD rel_setD2 rel_setD1 intro: rev_bexI)

lift_definition retain_TCons :: "('a, 'b) tllist set \<Rightarrow> ('a, 'b) tllist set"
is "\<lambda>A. A \<inter> {(xs, b). \<not> lnull xs}" parametric retain_TCons_raw_parametric
by(rule rel_setI)(fastforce dest: rel_setD1 rel_setD2)+

lemma retain_TCons_conv: "retain_TCons A = A \<inter> {xs. \<not> is_TNil xs}"
by(auto simp add: retain_TCons_def intro: rev_image_eqI)

lemma ttl_tSup:
  "\<lbrakk> Complete_Partial_Order.chain tllist_ord Y; \<exists>xs \<in> Y. \<not> is_TNil xs \<rbrakk>
  \<Longrightarrow> ttl (tSup Y) = tSup (ttl ` (Y \<inter> {xs. \<not> is_TNil xs}))"
unfolding ex_TCons_iff[symmetric] retain_TCons_conv[symmetric]
proof (transfer, goal_cases)
  case prems: (1 Y)
  then obtain xs b' where xsb: "(xs, b') \<in> Y" "\<not> lnull xs" by blast
  note chain = prems(1)

  have "flat_lub b (snd ` (Y \<inter> {(xs, _). lfinite xs})) = flat_lub b (insert b (snd ` (Y \<inter> {(xs, _). lfinite xs})))"
    by(auto simp add: flat_lub_def)
  also have "insert b (snd ` (Y \<inter> {(xs, _). lfinite xs})) = insert b (snd ` (apfst ltl ` (Y \<inter> {(xs, b). \<not> lnull xs}) \<inter> {(xs, _). lfinite xs}))"
    apply(auto intro: rev_image_eqI)
    apply(erule contrapos_np)
    apply(frule chainD[OF chain `(xs, b') \<in> Y`])
    using `\<not> lnull xs` xsb
    by(fastforce split: if_split_asm simp add: lprefix_lnull intro!: rev_image_eqI)
  also have "flat_lub b \<dots> = flat_lub b (snd ` (apfst ltl ` (Y \<inter> {(xs, b). \<not> lnull xs}) \<inter> {(xs, _). lfinite xs}))"
    by(auto simp add: flat_lub_def)
  also
  have "ltl ` (fst ` Y \<inter> {xs. \<not> lnull xs}) = fst ` apfst ltl ` (Y \<inter> {(xs, b). \<not> lnull xs})"
    by(auto simp add: image_image)
  ultimately show ?case using prems by clarsimp
qed

lemma tSup_TCons: "A \<noteq> {} \<Longrightarrow> tSup (TCons x ` A) = TCons x (tSup A)"
unfolding Set.is_empty_def[symmetric]
apply transfer
unfolding Set.is_empty_def
apply(clarsimp simp add: image_image lSup_LCons[symmetric])
apply(rule arg_cong[where f="flat_lub b"])
apply(auto 4 3 intro: rev_image_eqI)
done

lemma tllist_ord_terminalD:
  "\<lbrakk> tllist_ord xs ys; is_TNil ys \<rbrakk> \<Longrightarrow> flat_ord b (terminal xs) (terminal ys)"
by(cases xs)(auto simp add: is_TNil_def)

lemma tllist_ord_bot [simp]: "tllist_ord (TNil b) xs"
by(cases xs)(simp_all add: flat_ord_def)

lemma tllist_ord_ttlI:
  "tllist_ord xs ys \<Longrightarrow> tllist_ord (ttl xs) (ttl ys)"
by(cases xs ys rule: tllist.exhaust[case_product tllist.exhaust])(simp_all)

lemma not_is_TNil_conv: "\<not> is_TNil xs \<longleftrightarrow> (\<exists>x xs'. xs = TCons x xs')"
by(cases xs) simp_all

subsection {* Continuity of predefined constants *}

lemma mono_tllist_ord_case:
  fixes bot
  assumes mono: "\<And>x. monotone tllist_ord ord (\<lambda>xs. f x xs (TCons x xs))"
  and ord: "class.preorder ord (mk_less ord)"
  and bot: "\<And>x. ord (bot b) x"
  shows "monotone tllist_ord ord (\<lambda>xs. case xs of TNil b \<Rightarrow> bot b | TCons x xs' \<Rightarrow> f x xs' xs)"
proof -
  interpret preorder ord "mk_less ord" by (fact ord)
  show ?thesis by(rule monotoneI)(auto split: tllist.split dest: monotoneD[OF mono] simp add: flat_ord_def bot)
qed

lemma mcont_lprefix_case_aux:
  fixes f bot ord
  defines "g \<equiv> \<lambda>xs. f (thd xs) (ttl xs) (TCons (thd xs) (ttl xs))"
  assumes mcont: "\<And>x. mcont tSup tllist_ord lub ord (\<lambda>xs. f x xs (TCons x xs))"
  and ccpo: "class.ccpo lub ord (mk_less ord)"
  and bot: "\<And>x. ord (bot b) x"
  and cont_bot: "cont (flat_lub b) (flat_ord b) lub ord bot"
  shows "mcont tSup tllist_ord lub ord (\<lambda>xs. case xs of TNil b \<Rightarrow> bot b | TCons x xs' \<Rightarrow> f x xs' xs)"
  (is "mcont _ _ _ _ ?f")
proof(rule mcontI)
  interpret b: ccpo lub ord "mk_less ord" by(rule ccpo)

  show "cont tSup tllist_ord lub ord ?f"
  proof(rule contI)
    fix Y :: "('a, 'b) tllist set"
    assume chain: "Complete_Partial_Order.chain tllist_ord Y"
      and Y: "Y \<noteq> {}"
    from chain have chain': "Complete_Partial_Order.chain ord (?f ` Y)"
      by(rule chain_imageI)(auto split: tllist.split simp add: flat_ord_def intro!: bot mcont_monoD[OF mcont])

    show "?f (tSup Y) = lub (?f ` Y)"
    proof(cases "is_TNil (tSup Y)")
      case True
      hence "?f ` Y = bot ` terminal ` Y"
        by(auto 4 3 split: tllist.split intro: rev_image_eqI intro!: imageI)
      moreover from True have "tSup Y = TNil (flat_lub b (terminal ` Y))"
        by -(rule tllist.expand, simp_all add: terminal_tSup)
      moreover have "Complete_Partial_Order.chain (flat_ord b) (terminal ` Y)"
        using chain True by(auto intro: chain_imageI tllist_ord_terminalD)
      ultimately show ?thesis using Y
      by (simp add: contD [OF cont_bot] cong del: b.strong_SUP_cong)
    next
      case False
      hence eq: "tSup Y = TCons (thd (tSup Y)) (ttl (tSup Y))" by simp
      have eq': 
        "?f ` Y =
         (\<lambda>x. bot (terminal x)) ` (Y \<inter> {xs. is_TNil xs}) \<union>
         (\<lambda>xs. f (thd xs) (ttl xs) xs) ` (Y \<inter> {xs. \<not> is_TNil xs})"
        by(auto 4 3 split: tllist.splits intro: rev_image_eqI)
      
      from False obtain xs where xs: "xs \<in> Y" "\<not> is_TNil xs" by auto
      { fix ys
        assume "ys \<in> Y" "is_TNil ys"
        hence "terminal ys = b" using xs
          by(cases xs ys rule: tllist.exhaust[case_product tllist.exhaust])(auto dest: chainD[OF chain]) }
      then have lub: "lub (?f ` Y) = lub ((\<lambda>xs. f (thd xs) (ttl xs) xs) ` (Y \<inter> {xs. \<not> is_TNil xs}))"
        using xs chain' unfolding eq'
        by -(erule ccpo.Sup_Un_less[OF ccpo], auto simp add: intro!: bot)
      { fix xs
        assume xs:  "xs \<in> Y \<inter> {xs. \<not> is_TNil xs}"
        hence "(THE x. x \<in> thd ` (Y \<inter> {xs. \<not> is_TNil xs})) = thd xs"
          by(auto dest: chainD[OF chain] simp add: not_is_TNil_conv intro!: the_equality)
        hence "f (THE x. x \<in> thd ` (Y \<inter> {xs. \<not> is_TNil xs})) (ttl xs) (TCons (THE x. x \<in> thd ` (Y \<inter> {xs. \<not> is_TNil xs})) (ttl xs)) = f (thd xs) (ttl xs) xs"
          using xs by simp }
      moreover have "Complete_Partial_Order.chain tllist_ord (ttl ` (Y \<inter> {xs. \<not> is_TNil xs}))"
        using chain by(rule chain_imageI[OF chain_subset])(auto simp add: tllist_ord_ttlI)
      moreover from False have "Y \<inter> {xs. \<not> is_TNil xs} \<noteq> {}" by auto
      ultimately show ?thesis
        apply(subst (1 2) eq)
        using False
        apply(simp add: thd_tSup ttl_tSup[OF chain] mcont_contD[OF mcont] image_image lub)
        done
    qed
  qed
  from mcont_mono[OF mcont] _ bot
  show "monotone tllist_ord ord ?f"
    by(rule mono_tllist_ord_case)(unfold_locales)
qed

lemma cont_TNil [simp, cont_intro]: "cont (flat_lub b) (flat_ord b) tSup tllist_ord TNil"
apply(rule contI)
apply transfer
apply(simp add: image_image image_constant_conv)
apply(rule arg_cong[where f="flat_lub b"])
apply(auto intro: rev_image_eqI)
done

lemma monotone_TCons: "monotone tllist_ord tllist_ord (TCons x)"
by(rule monotoneI) simp

lemmas mono2mono_TCons[cont_intro] = monotone_TCons[THEN tllist.mono2mono]

lemma mcont_TCons: "mcont tSup tllist_ord tSup tllist_ord (TCons x)"
apply(rule mcontI)
apply(rule monotone_TCons)
apply(rule contI)
apply(simp add: tSup_TCons)
done

lemmas mcont2mcont_TCons[cont_intro] = mcont_TCons[THEN tllist.mcont2mcont]

lemmas [transfer_rule del] = tllist_ord.transfer tSup.transfer

lifting_update tllist.lifting
lifting_forget tllist.lifting

lemmas [transfer_rule] = tllist_ord.transfer tSup.transfer

lemma mono2mono_tset[THEN lfp.mono2mono, cont_intro]:
  shows smonotone_tset: "monotone tllist_ord (\<subseteq>) tset"
including tllist.lifting
by transfer(rule monotone_comp[OF _ monotone_lset], auto intro: monotoneI)

lemma mcont2mcont_tset [THEN lfp.mcont2mcont, cont_intro]:
  shows mcont_tset: "mcont tSup tllist_ord Union (\<subseteq>) tset"
including tllist.lifting
apply transfer
apply(rule mcont_comp[OF _ mcont_lset])
unfolding mcont_def by(auto intro: monotoneI contI )

end

context includes lifting_syntax
begin

lemma rel_fun_lift:
  "(\<And>x. A (f x) (g x)) \<Longrightarrow> ((=) ===> A) f g"
by(simp add: rel_fun_def)

lemma tllist_ord_transfer [transfer_rule]:
  "((=) ===> pcr_tllist (=) (=) ===> pcr_tllist (=) (=) ===> (=))
     (\<lambda>b (xs1, b1) (xs2, b2). if lfinite xs1 then b1 = b \<and> lprefix xs1 xs2 \<or> xs1 = xs2 \<and> flat_ord b b1 b2 else xs1 = xs2)
     tllist_ord"
by(rule rel_fun_lift)(rule tllist_ord.transfer)

lemma tSup_transfer [transfer_rule]:
  "((=) ===> rel_set (pcr_tllist (=) (=)) ===> pcr_tllist (=) (=))
     (\<lambda>b A. (lSup (fst ` A), flat_lub b (snd ` (A \<inter> {(xs, _). lfinite xs}))))
     tSup"
by(rule rel_fun_lift)(rule tSup.transfer)

end

lifting_update tllist.lifting
lifting_forget tllist.lifting

interpretation tllist: partial_function_definitions "tllist_ord b" "tSup b" for b
by(rule tllist_ord_partial_function_definitions)

lemma tllist_case_mono [partial_function_mono, cont_intro]: 
  assumes tnil: "\<And>b. monotone orda ordb (\<lambda>f. tnil f b)"
  and tcons: "\<And>x xs. monotone orda ordb (\<lambda>f. tcons f x xs)"
  shows "monotone orda ordb (\<lambda>f. case_tllist (tnil f) (tcons f) xs)"
by(rule monotoneI)(auto split: tllist.split dest: monotoneD[OF tnil] monotoneD[OF tcons])

subsection {* Definition of recursive functions *}

locale tllist_pf = fixes b :: 'b
begin

declaration {* Partial_Function.init "tllist" @{term "tllist.fixp_fun b"}
  @{term "tllist.mono_body b"} @{thm tllist.fixp_rule_uc[where b=b]} @{thm tllist.fixp_induct_uc[where b=b]} NONE *}

abbreviation mono_tllist where "mono_tllist \<equiv> monotone (fun_ord (tllist_ord b)) (tllist_ord b)"

lemma LCons_mono [partial_function_mono, cont_intro]:
  "mono_tllist A \<Longrightarrow> mono_tllist (\<lambda>f. TCons x (A f))"
by(rule monotoneI)(auto dest: monotoneD)

end

lemma mono_tllist_lappendt2 [partial_function_mono]:
  "tllist_pf.mono_tllist b A \<Longrightarrow> tllist_pf.mono_tllist b (\<lambda>f. lappendt xs (A f))"
apply(rule monotoneI)
apply(drule (1) monotoneD)
apply(simp add: tllist_ord.rep_eq split: if_split_asm)
apply(auto simp add: lappend_inf)
done

lemma mono_tllist_tappend2 [partial_function_mono]:
  assumes "\<And>y. tllist_pf.mono_tllist b (C y)"
  shows "tllist_pf.mono_tllist b (\<lambda>f. tappend xs (\<lambda>y. C y f))"
apply(cases "tfinite xs")
 apply(rule monotoneI)
 apply(drule monotoneD[OF assms[where y="terminal xs"]])
 including tllist.lifting
 apply transfer
 apply(fastforce split: if_split_asm)
apply(simp add: tappend_inf)
done

end
