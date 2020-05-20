(*  Title:      Minimality.thy
    Author:     Sebastian Ullrich
*)

section \<open>Minimality\<close>

text \<open>We show that every reducible CFG without trivial \pf s is minimal, recreating the proof in~\cite{braun13cc}.
  The original proof is inlined as prose text.\<close>

theory Minimality
imports SSA_CFG Serial_Rel
begin

context graph_path
begin
  text \<open>Cytron's definition of path convergence\<close>
  definition "pathsConverge g x xs y ys z \<equiv> g \<turnstile> x-xs\<rightarrow>z \<and> g \<turnstile> y-ys\<rightarrow>z \<and> length xs > 1 \<and> length ys > 1 \<and> x \<noteq> y \<and>
    (\<forall>j \<in> {0..< length xs}. \<forall>k \<in> {0..<length ys}. xs ! j = ys ! k \<longrightarrow> j = length xs - 1 \<or> k = length ys - 1)"

  text \<open>Simplified definition\<close>
  definition "pathsConverge' g x xs y ys z \<equiv> g \<turnstile> x-xs\<rightarrow>z \<and> g \<turnstile> y-ys\<rightarrow>z \<and> length xs > 1 \<and> length ys > 1 \<and> x \<noteq> y \<and>
    set (butlast xs) \<inter> set (butlast ys) = {}"

  lemma pathsConverge'[simp]: "pathsConverge g x xs y ys z \<longleftrightarrow> pathsConverge' g x xs y ys z"
  proof-
    have "(\<forall>j \<in> {0..< length xs}. \<forall>k \<in> {0..<length ys}. xs ! j = ys ! k \<longrightarrow> j = length xs - 1 \<or> k = length ys - 1)
          \<longleftrightarrow> (\<forall>x' \<in> set (butlast xs). \<forall>y' \<in> set (butlast ys). x' \<noteq> y')"
    proof
      assume 1: "\<forall>j\<in>{0..<length xs}. \<forall>k\<in>{0..<length ys}. xs ! j = ys ! k \<longrightarrow> j = length xs - 1 \<or> k = length ys - 1"
      show "\<forall>x'\<in>set (butlast xs). \<forall>y'\<in>set (butlast ys). x' \<noteq> y'"
      proof (rule, rule, rule)
        fix x' y'
        assume 2: "x' \<in> set (butlast xs)" "y' \<in> set (butlast ys)" and[simp]: "x' = y'"
        from 2(1) obtain j where j: "xs ! j = x'" "j < length xs - 1" by (rule butlast_idx)
        moreover from j have "j < length xs" by simp
        moreover from 2(2) obtain k where k: "ys ! k = y'" "k < length ys - 1" by (rule butlast_idx)
        moreover from k have "k < length ys" by simp
        ultimately show False using 1[THEN bspec[where x=j], THEN bspec[where x=k]] by auto
      qed
    next
      assume 1: "\<forall>x'\<in>set (butlast xs). \<forall>y'\<in>set (butlast ys). x' \<noteq> y'"
      show "\<forall>j\<in>{0..<length xs}. \<forall>k\<in>{0..<length ys}. xs ! j = ys ! k \<longrightarrow> j = length xs - 1 \<or> k = length ys - 1"
      proof (rule, rule, rule, simp)
        fix j k
        assume 2: "j < length xs" "k < length ys" "xs ! j = ys ! k"
        show "j = length xs - Suc 0 \<or> k = length ys - Suc 0"
        proof (rule ccontr, simp)
          assume 3: "j \<noteq> length xs - Suc 0 \<and> k \<noteq> length ys - Suc 0"
          let ?x' = "xs ! j"
          let ?y' = "ys ! k"
          from 2(1) 3 have "?x' \<in> set (butlast xs)" by - (rule butlast_idx', auto)
          moreover from 2(2) 3 have "?y' \<in> set (butlast ys)" by - (rule butlast_idx', auto)
          ultimately have "?x' \<noteq> ?y'" using 1 by simp
          with 2(3) show False by simp
        qed
      qed
    qed
    thus ?thesis by (auto simp:pathsConverge_def pathsConverge'_def)
  qed

  lemma pathsConvergeI:
    assumes "g \<turnstile> x-xs\<rightarrow>z" "g \<turnstile> y-ys\<rightarrow>z" "length xs > 1" "length ys > 1" "set (butlast xs) \<inter> set (butlast ys) = {}"
    shows "pathsConverge g x xs y ys z"
  proof-
    from assms have "x \<noteq> y"
      by (metis append_is_Nil_conv disjoint_iff_not_equal length_butlast list.collapse list.distinct(1) nth_Cons_0 nth_butlast nth_mem path2_def split_list zero_less_diff)
    with assms show ?thesis by (simp add:pathsConverge'_def)
  qed
end

text \<open>A (control) flow graph G is reducible iff for each cycle C of G there is a node of C that dominates all other nodes in C.\<close>
definition (in graph_Entry) "reducible g \<equiv> \<forall>n ns. g \<turnstile> n-ns\<rightarrow>n \<longrightarrow> (\<exists>m \<in> set ns. \<forall>n \<in> set ns. dominates g m n)"

context CFG_SSA_Transformed
begin
  text \<open>A $\phi$ function for variable v is necessary in block Z iff two non-null paths $X \rightarrow^+ Z$ and $Y \rightarrow^+ Z$ converge at a block Z,
    such that the blocks X and Y contain assignments to v.\<close>
  definition "necessaryPhi g v z \<equiv> \<exists>n ns m ms. old.pathsConverge g n ns m ms z \<and> v \<in> oldDefs g n \<and> v \<in> oldDefs g m"
  abbreviation "necessaryPhi' g val \<equiv> necessaryPhi g (var g val) (defNode g val)"
  definition "unnecessaryPhi g val \<equiv> phi g val \<noteq> None \<and> \<not>necessaryPhi' g val"

  lemma necessaryPhiI: "old.pathsConverge g n ns m ms z \<Longrightarrow> v \<in> oldDefs g n \<Longrightarrow> v \<in> oldDefs g m \<Longrightarrow> necessaryPhi g v z"
    by (auto simp: necessaryPhi_def)

  text \<open>A program with only necessary $\phi$ functions is in minimal SSA form.\<close>
  definition "cytronMinimal g \<equiv> \<forall>v \<in> allVars g. phi g v \<noteq> None \<longrightarrow> necessaryPhi' g v"

  text \<open>Let p be a $\phi$ function in a block P. Furthermore, let q in a block Q
and r in a block R be two operands of p, such that p, q and r are pairwise distinct.
Then at least one of Q and R does not dominate P.\<close>
  lemma 2:
    assumes "phiArg g p q" "phiArg g p r" "distinct [p, q, r]" and[simp]: "p \<in> allVars g"
    shows "\<not>(def_dominates g q p \<and> def_dominates g r p)"
  proof (rule, erule conjE)
    txt \<open>Proof. Assume that Q and R dominate P, i.e., every path from the start block to P contains Q and R.\<close>
    assume asm: "def_dominates g q p" "def_dominates g r p"

    txt \<open>Since immediate dominance forms a tree, Q dominates R or R dominates Q.\<close>
    hence "def_dominates g q r \<or> def_dominates g r q"
      by - (rule old.dominates_antitrans[of g "defNode g q" "defNode g p" "defNode g r"], auto)
    moreover
    {
      txt \<open>Without loss of generality, let Q dominate R.\<close>
      fix q r
      assume assms: "phiArg g p q" "phiArg g p r" "distinct [p, q, r]"
      assume asm: "def_dominates g q p" "def_dominates g r p"
      assume wlog: "def_dominates g q r"

      have[simp]: "var g q = var g r" using phiArg_same_var[OF assms(1)] phiArg_same_var[OF assms(2)] by simp

      txt \<open>Furthermore, let S be the corresponding predecessor block of P where p is using q.\<close>
      obtain S where S: "q \<in> phiUses g S" "S \<in> set (old.predecessors g (defNode g p))" by (rule phiUses_exI'[OF assms(1)], simp)

      txt \<open>Then there is a path from the start block crossing Q then R and S.\<close>
      have "defNode g p \<noteq> defNode g q" using assms(1,3)
        by - (rule phiArg_distinct_nodes, auto)
      with S have "old.dominates g (defNode g q) S"
        by - (rule allUses_dominated, auto)
      then obtain ns where ns: "g \<turnstile> defNode g q-ns\<rightarrow>S" "distinct ns"
        by (rule old.dominates_path, auto elim: old.simple_path2)
      moreover have "defNode g r \<in> set (tl ns)"
      proof-
        have "defNode g r \<noteq> defNode g q" using assms
          by - (rule phiArgs_def_distinct, auto)
        hence "hd ns \<noteq> defNode g r" using ns by (auto simp:old.path2_def)
        moreover
        have "defNode g p \<noteq> defNode g r" using assms(2,3)
          by - (rule phiArg_distinct_nodes, auto)
        with S(2) have "old.dominates g (defNode g r) S"
          by - (rule old.dominates_unsnoc[where m="defNode g p"], auto simp:wlog asm assms)
        with wlog have "defNode g r \<in> set ns" using ns(1)
          by (rule old.dominates_mid, auto)
        ultimately
        show ?thesis by (metis append_Nil in_set_conv_decomp list.sel(1) tl_append2)
      qed

      txt \<open>This violates the SSA property.\<close>
      moreover have "q \<in> allDefs g (defNode g q)" using assms S(1) by simp
      moreover have "r \<in> allDefs g (defNode g r)" using assms S(1) by simp
      ultimately have "var g r \<noteq> var g q" using S(1)
        by - (rule conventional, auto simp:old.path2_def distinct_hd_tl)
      hence False by simp
    }
    ultimately show False using assms asm by auto
  qed

  lemma convergence_prop:
    assumes "necessaryPhi g (var g v) n" "g \<turnstile> n-ns\<rightarrow>m" "v \<in> allUses g m" "\<And>x. x \<in> set (tl ns) \<Longrightarrow> v \<notin> allDefs g x" "v \<notin> defs g n"
    shows "phis g (n,v) \<noteq> None"
  proof
    from assms(2, 3) have "v \<in> allVars g" by auto
    hence 1: "v \<in> allDefs g (defNode g v)" by (rule defNode)

    assume "phis g (n,v) = None"
    with assms(5) have 2: "v \<notin> allDefs g n"
      by (auto simp:allDefs_def phiDefs_def)

    from assms(1) obtain a as b bs v\<^sub>a v\<^sub>b where
      a: "v\<^sub>a \<in> defs g a" "var g v\<^sub>a = var g v" and
      b: "v\<^sub>b \<in> defs g b" "var g v\<^sub>b = var g v"
      and conv: "g \<turnstile> a-as\<rightarrow>n" "g \<turnstile> b-bs\<rightarrow>n" "1 < length as" "1 < length bs" "a \<noteq> b" "set (butlast as) \<inter> set (butlast bs) = {}"
      by (auto simp:necessaryPhi_def old.pathsConverge'_def oldDefs_def)
    have "old.dominates g (defNode g v) m" using assms(2,3)
      by - (rule allUses_dominated, auto)
    hence dom: "old.dominates g (defNode g v) n" using assms(2,4) 1
      by - (rule old.dominates_unsnoc', auto)
    hence "old.strict_dom g (defNode g v) n" using 1 2 by auto

    {
      fix v\<^sub>a a as v\<^sub>b b bs
      assume a: "v\<^sub>a \<in> defs g a" "var g v\<^sub>a = var g v"
      assume as: "g \<turnstile> a-as\<rightarrow>n" "length as > 1"
      assume b: "v\<^sub>b \<in> defs g b" "var g v\<^sub>b = var g v"
      assume bs: "g \<turnstile> b-bs\<rightarrow>n"
      assume conv: "a \<noteq> b" "set (butlast as) \<inter> set (butlast bs) = {}"
      have 3: "defNode g v \<noteq> a"
      proof
        assume contr: "defNode g v = a"

        have "a \<in> set (butlast as)" using as by (auto simp:old.path2_def intro:hd_in_butlast)
        hence "a \<notin> set (butlast bs)" using conv(2) by auto
        moreover
        have "a \<noteq> n" using 1 2 contr by auto
        hence "a \<noteq> last bs" using bs by (auto simp:old.path2_def)
        ultimately have 4: "a \<notin> set bs"
          by - (subst append_butlast_last_id[symmetric], rule old.path2_not_Nil[OF bs], auto)

        have "v \<noteq> v\<^sub>a"
        proof
          assume asm: "v = v\<^sub>a"
          have "v \<noteq> v\<^sub>b"
          proof
            assume "v = v\<^sub>b"
            with asm[symmetric] b(1) have "v\<^sub>a \<in> allDefs g b" by simp
            with asm have "a = b" using as bs a(1) by - (rule allDefs_disjoint', auto)
            with conv(1) show False by simp
          qed
          obtain ebs where ebs: "g \<turnstile> Entry g-ebs\<rightarrow>b"
            using bs by (atomize, auto)
          hence "g \<turnstile> Entry g-butlast ebs@bs\<rightarrow>n" using bs by auto
          hence 5: "a \<in> set (butlast ebs@bs)"
            by - (rule old.dominatesE[OF dom[simplified contr]])
          show False
          proof (cases "a \<in> set (butlast ebs)")
            case True
            hence "a \<in> set ebs" by (rule in_set_butlastD)
            with ebs obtain abs where abs: "g \<turnstile> a-abs\<rightarrow>b" "a \<notin> set (tl abs)"
              by (rule old.path2_split_first_last, auto)
            let ?path = "(abs@tl bs)@tl ns"
            have "var g v\<^sub>b \<noteq> var g v\<^sub>a"
            proof (rule conventional)
              show "g \<turnstile> a-?path\<rightarrow>m" using abs(1) bs assms(2)
                by - (rule old.path2_app, rule old.path2_app)
              have "a \<notin> set (tl bs)" using 4 by (auto simp:in_set_tlD)
              moreover have "a \<notin> set (tl ns)" using 1 2 contr assms(4) by auto
              ultimately show "a \<notin> set (tl ?path)" using abs conv(2)
                by - (subst tl_append2, auto simp: old.path2_not_Nil)
              show "v\<^sub>a \<in> allUses g m" using asm assms(3) by simp
              have "b \<in> set (tl abs)" using abs(1) conv(1)
                by (auto simp:old.path2_def intro!:last_in_tl nonsimple_length_gt_1)
              thus "b \<in> set (tl ?path)" using abs(1) by (simp add: old.path2_not_Nil)
            qed (simp_all add: a b)
            thus False using a b by simp
          next
            case False
            with 4 5 show False by simp
          qed
        qed
        hence "var g v \<noteq> var g v\<^sub>a" using a as 1 contr by - (rule allDefs_var_disjoint, auto)
        with a(2) show False by simp
      qed
      obtain eas where eas: "g \<turnstile> Entry g-eas\<rightarrow>a"
        using as by (atomize, auto)
      hence "g \<turnstile> Entry g-eas@tl as\<rightarrow>n" using as by auto
      hence 4: "defNode g v \<in> set (eas@tl as)" by - (rule old.dominatesE[OF dom])

      have "defNode g v \<in> set (tl as)"
      proof (rule ccontr)
        assume asm: "defNode g v \<notin> set (tl as)"
        with 4 have "defNode g v \<in> set eas" by simp
        then obtain eas' where eas': "g \<turnstile> defNode g v-defNode g v#eas'\<rightarrow>a" "defNode g v \<notin> set eas'" using eas
          by - (rule old.path2_split_first_last)
        let ?path = "((defNode g v#eas')@tl as)@tl ns"
        have "var g v\<^sub>a \<noteq> var g v"
        proof (rule conventional)
          show "g \<turnstile> defNode g v-?path\<rightarrow>m" using eas' as assms(2)
            by (auto simp del:append_Cons append_assoc intro: old.path2_app)
          show "a \<in> set (tl ?path)" using eas' 3 by (auto simp:old.path2_def)
          show "defNode g v \<notin> set (tl ?path)" using assms(4) 1 eas'(2) asm by auto
        qed (simp_all add:1 assms(3) a(1))
        with a(2) show False by simp
      qed
      moreover have "defNode g v \<noteq> n" using 1 2 by auto
      ultimately have "defNode g v \<in> set (butlast as)" using as subsetD[OF set_tl, of "defNode g v" as]
        by - (rule in_set_butlastI, auto simp:old.path2_def)
    }
    note def_in_as = this
    from def_in_as[OF a conv(1,3) b conv(2)] def_in_as[OF b conv(2,4) a conv(1)] conv(5,6) show False by auto
  qed

  lemma convergence_prop':
    assumes "necessaryPhi g v n" "g \<turnstile> n-ns\<rightarrow>m" "v \<in> var g ` allUses g m" "\<And>x. x \<in> set ns \<Longrightarrow> v \<notin> oldDefs g x"
    obtains val where "var g val = v" "phis g (n,val) \<noteq> None"
  using assms proof (induction "length ns" arbitrary: ns m rule: less_induct)
    case less
    from less.prems(4) obtain val where val: "var g val = v" "val \<in> allUses g m" by auto
    show ?thesis
    proof (cases "\<exists>m' \<in> set (tl ns). v \<in> var g ` phiDefs g m'")
      case False
      with less.prems(5) have "\<And>x. x \<in> set (tl ns) \<Longrightarrow> val \<notin> allDefs g x"
        by (auto simp: allDefs_def val(1)[symmetric] oldDefs_def dest: in_set_tlD)
      moreover from less.prems(3,5) have "val \<notin> defs g n"
        by (auto simp: oldDefs_def val(1)[symmetric] dest: old.path2_hd_in_ns)
      ultimately show ?thesis
        using less.prems
        by - (rule that[OF val(1)], rule convergence_prop, auto simp: val)
    next
      case True
      with less.prems(3) obtain ns' m' where m': "g \<turnstile> n-ns'\<rightarrow>m'" "v \<in> var g ` phiDefs g m'" "prefix ns' ns"
        by - (erule old.path2_split_first_prop[where P="\<lambda>m. v \<in> var g ` phiDefs g m"], auto dest: in_set_tlD)
      show ?thesis
      proof (cases "m' = n")
        case True
        with m'(2) show ?thesis by (auto simp: phiDefs_def intro: that)
      next
        case False
        with m'(1) obtain m'' where m'': "g \<turnstile> n-butlast ns'\<rightarrow>m''" "m'' \<in> set (old.predecessors g m')"
          by - (rule old.path2_unsnoc, auto)
        show ?thesis
        proof (rule less.hyps[of "butlast ns'", OF _])
          show "length (butlast ns') < length ns"
            using m''(1) m'(3) by (cases "length ns'", auto dest: prefix_length_le)

          from m'(2) obtain val vs where vs: "phis g (m',val) = Some vs" "var g val = v"
            by (auto simp: phiDefs_def)
          with m'' obtain val' where "val' \<in> phiUses g m''" "val' \<in> set vs"
            by - (rule phiUses_exI, auto simp: phiDefs_def)
          with vs have "val' \<in> allUses g m''" "var g val' = v" by auto
          then show "v \<in> var g ` allUses g m''" by auto

          from m'(3) show "\<And>x. x \<in> set (butlast ns') \<Longrightarrow> v \<notin> oldDefs g x"
            by - (rule less.prems(5), auto elim: in_set_butlastD)
        qed (auto intro: less.prems(1,2) m''(1))
      qed
    qed
  qed

  lemma nontrivialE:
    assumes "\<not>trivial g p" "phi g p \<noteq> None" and[simp]: "p \<in> allVars g"
    obtains r s where "phiArg g p r" "phiArg g p s" "distinct [p, r, s]"
  proof-
    from assms(2) obtain vs where vs: "phi g p = Some vs" by auto
    have "card (set vs - {p}) \<ge> 2"
    proof-
      have "card (set vs) \<noteq> 0" using Entry_no_phis[of g p] phi_wf[OF vs] vs by (auto simp:phi_def invar)
      moreover have "set vs \<noteq> {p}" using vs by - (rule phi_no_closed_loop, auto)
      ultimately have "card (set vs - {p}) \<noteq> 0"
        by (metis List.finite_set card_0_eq insert_Diff_single insert_absorb removeAll_id set_removeAll)
      moreover have "card (set vs - {p}) \<noteq> 1"
      proof
        assume "card (set vs - {p}) = 1"
        then obtain q where q: "{q} = set vs - {p}" by - (erule card_eq_1_singleton, auto)
        hence "isTrivialPhi g p q" using vs by (auto simp:isTrivialPhi_def split:option.split)
        moreover have "phiArg g p q" using q vs unfolding phiArg_def by auto
        ultimately show False using assms(1) by (auto simp:trivial_def)
      qed
      ultimately show ?thesis by arith
    qed
    then obtain r s where rs: "r \<noteq> s" "r \<in> set vs - {p}" "s \<in> set vs - {p}" by (rule set_take_two)
    thus ?thesis using vs by - (rule that[of r s], auto simp: phiArg_def)
  qed

  lemma paths_converge_prefix:
    assumes "g \<turnstile> x-xs\<rightarrow>z" "g \<turnstile> y-ys\<rightarrow>z" "x \<noteq> y" "length xs > 1" "length ys > 1" "x \<notin> set (butlast ys)" "y \<notin> set (butlast xs)"
    obtains xs' ys' z' where "old.pathsConverge g x xs' y ys' z'" "prefix xs' xs" "prefix ys' ys"
  using assms proof (induction "length xs" arbitrary:xs ys z rule:nat_less_induct)
    case 1
    from "1.prems"(3,4) have 2: "x \<noteq> y" by (auto simp:old.path2_def)
    show thesis
    proof (cases "set (butlast xs) \<inter> set (butlast ys) = {}")
      case True
      with "1.prems"(2-) have "old.pathsConverge g x xs y ys z" by (auto simp add: old.pathsConverge'_def)
      thus thesis by (rule "1.prems"(1), simp_all)
    next
      case False
      then obtain xs' z' where xs': "g \<turnstile> x-xs'\<rightarrow>z'" "prefix xs' (butlast xs)" "z' \<in> set (butlast ys)" "\<forall>a \<in> set (butlast xs'). a \<notin> set (butlast ys)"
        using "1.prems"(2,5) by - (rule old.path2_split_first_prop[of g x "butlast xs" _ "\<lambda>a. a \<in> set (butlast ys)"], auto elim: old.path2_unsnoc)
      from xs'(3) "1.prems"(3) obtain ys' where ys': "g \<turnstile> y-ys'\<rightarrow>z'" "strict_prefix ys' ys"
        by - (rule old.path2_strict_prefix_ex)
      show ?thesis
      proof (rule "1.hyps"[rule_format, OF _ _ _ xs'(1) ys'(1) assms(3)])
        show "length xs' < length xs" using xs'(2) xs'(1)
          by - (rule prefix_length_less, rule strict_prefix_butlast, auto)
        from "1.prems"(1) prefix_order.dual_order.strict_implies_order prefix_order.dual_order.trans
          prefix_butlastD xs'(2) ys'(2)
        show "\<And>xs'' ys'' z''. old.pathsConverge g x xs'' y ys'' z'' \<Longrightarrow> prefix xs'' xs' \<Longrightarrow> prefix ys'' ys' \<Longrightarrow> thesis"
          by blast
        show "length xs' > 1"
        proof-
          have "length xs' \<noteq> 0" using xs' by auto
          moreover {
            assume "length xs' = 1"
            with xs'(1,3) have "x \<in> set (butlast ys)"
              by (auto simp:old.path2_def simp del:One_nat_def dest!:singleton_list_hd_last)
            with "1.prems"(7) have False ..
          }
          ultimately show ?thesis by arith
        qed

        show "length ys' > 1"
        proof-
          have "length ys' \<noteq> 0" using ys' by auto
          moreover {
            assume "length ys' = 1"
            with ys'(1) xs'(1,2) have "y \<in> set (butlast xs)"
              by (auto simp:old.path2_def old.path_not_Nil simp del:One_nat_def dest!:singleton_list_hd_last)
            with "1.prems"(8) have False ..
          }
          ultimately show ?thesis by arith
        qed

        show "y \<notin> set (butlast xs')"
          using  xs'(2) "1.prems"(8)
          by (metis in_prefix in_set_butlastD)
        show "x \<notin> set (butlast ys')"
          by (metis "1.prems"(7) in_set_butlast_appendI strict_prefixE' ys'(2))
      qed simp
    qed
  qed

  lemma ununnecessaryPhis_disjoint_paths_aux:
    assumes "\<not>unnecessaryPhi g r" and[simp]: "r \<in> allVars g"
    obtains n\<^sub>1 ns\<^sub>1 n\<^sub>2 ns\<^sub>2 where
      "var g r \<in> oldDefs g n\<^sub>1" "g \<turnstile> n\<^sub>1-ns\<^sub>1\<rightarrow>defNode g r" and
      "var g r \<in> oldDefs g n\<^sub>2" "g \<turnstile> n\<^sub>2-ns\<^sub>2\<rightarrow>defNode g r" and
      "set (butlast ns\<^sub>1) \<inter> set (butlast ns\<^sub>2) = {}"
  proof (cases "phi g r")
    case None
    thus thesis by - (rule that[of "defNode g r" _ "defNode g r"], auto intro!: oldDefsI intro: defNode_cases[of r g])
  next
    case Some
    with assms that show ?thesis by (auto simp: unnecessaryPhi_def necessaryPhi_def old.pathsConverge'_def)
  qed

  lemma ununnecessaryPhis_disjoint_paths:
    assumes "\<not>unnecessaryPhi g r" "\<not>unnecessaryPhi g s"
      (* and rs: "phiArg p r" "phiArg p s" "distinct [p, r, s]" *)
      and rs: "defNode g r \<noteq> defNode g s"
      and[simp]: "r \<in> allVars g" "s \<in> allVars g" "var g r = V" "var g s = V"
    obtains n ns m ms where "V \<in> oldDefs g n" "g \<turnstile> n-ns\<rightarrow>defNode g r" and "V \<in> oldDefs g m" "g \<turnstile> m-ms\<rightarrow>defNode g s"
        and "set ns \<inter> set ms = {}"
  proof-
    obtain n\<^sub>1 ns\<^sub>1 n\<^sub>2 ns\<^sub>2 where
      ns\<^sub>1: "V \<in> oldDefs g n\<^sub>1" "g \<turnstile> n\<^sub>1-ns\<^sub>1\<rightarrow>defNode g r" "defNode g r \<notin> set (butlast ns\<^sub>1)" and
      ns\<^sub>2: "V \<in> oldDefs g n\<^sub>2" "g \<turnstile> n\<^sub>2-ns\<^sub>2\<rightarrow>defNode g r" "defNode g r \<notin> set (butlast ns\<^sub>2)" and
      ns: "set (butlast ns\<^sub>1) \<inter> set (butlast ns\<^sub>2) = {}"
    proof-
      from assms obtain n\<^sub>1 ns\<^sub>1 n\<^sub>2 ns\<^sub>2 where
        ns\<^sub>1: "V \<in> oldDefs g n\<^sub>1" "g \<turnstile> n\<^sub>1-ns\<^sub>1\<rightarrow>defNode g r" and
        ns\<^sub>2: "V \<in> oldDefs g n\<^sub>2" "g \<turnstile> n\<^sub>2-ns\<^sub>2\<rightarrow>defNode g r" and
        ns: "set (butlast ns\<^sub>1) \<inter> set (butlast ns\<^sub>2) = {}"
      by - (rule ununnecessaryPhis_disjoint_paths_aux, auto)

      from ns\<^sub>1 obtain ns\<^sub>1' where ns\<^sub>1': "g \<turnstile> n\<^sub>1-ns\<^sub>1'\<rightarrow>defNode g r" "defNode g r \<notin> set (butlast ns\<^sub>1')" "distinct ns\<^sub>1'" "set ns\<^sub>1' \<subseteq> set ns\<^sub>1"
        by (auto elim: old.simple_path2)
      from ns\<^sub>2 obtain ns\<^sub>2' where ns\<^sub>2': "g \<turnstile> n\<^sub>2-ns\<^sub>2'\<rightarrow>defNode g r" "defNode g r \<notin> set (butlast ns\<^sub>2')" "distinct ns\<^sub>2'" "set ns\<^sub>2' \<subseteq> set ns\<^sub>2"
        by (auto elim: old.simple_path2)

      have "set (butlast ns\<^sub>1') \<inter> set (butlast ns\<^sub>2') = {}"
      proof (rule equals0I)
        fix x
        assume 1: "x \<in> set (butlast ns\<^sub>1') \<inter> set (butlast ns\<^sub>2')"
        with set_butlast_distinct[OF ns\<^sub>1'(3)] ns\<^sub>1'(1) have 2: "x \<noteq> defNode g r" by (auto simp:old.path2_def)
        with 1 ns\<^sub>1'(4) ns\<^sub>2'(4) ns\<^sub>1(2) ns\<^sub>2(2) have "x \<in> set (butlast ns\<^sub>1)" "x \<in> set (butlast ns\<^sub>2)"
          by - (auto intro!:in_set_butlastI elim:in_set_butlastD simp:old.path2_def)
        with ns show False by auto
      qed

      thus thesis by (rule that[OF ns\<^sub>1(1) ns\<^sub>1'(1,2) ns\<^sub>2(1) ns\<^sub>2'(1,2)])
    qed

    obtain m ms where ms: "V \<in> oldDefs g m" "g \<turnstile> m-ms\<rightarrow>defNode g s" "defNode g r \<notin> set ms"
    proof-
      from assms(2) obtain m\<^sub>1 ms\<^sub>1 m\<^sub>2 ms\<^sub>2 where
        ms\<^sub>1: "V \<in> oldDefs g m\<^sub>1" "g \<turnstile> m\<^sub>1-ms\<^sub>1\<rightarrow>defNode g s" and
        ms\<^sub>2: "V \<in> oldDefs g m\<^sub>2" "g \<turnstile> m\<^sub>2-ms\<^sub>2\<rightarrow>defNode g s" and
        ms: "set (butlast ms\<^sub>1) \<inter> set (butlast ms\<^sub>2) = {}"
        by - (rule ununnecessaryPhis_disjoint_paths_aux, auto)
      show thesis
      proof (cases "defNode g r \<in> set ms\<^sub>1")
        case False
        with ms\<^sub>1 show thesis by (rule that)
      next
        case True
        have "defNode g r \<notin> set ms\<^sub>2"
        proof
          assume "defNode g r \<in> set ms\<^sub>2"
          moreover note \<open>defNode g r \<noteq> defNode g s\<close>
          ultimately have "defNode g r \<in> set (butlast ms\<^sub>1)" "defNode g r \<in> set (butlast ms\<^sub>2)" using True ms\<^sub>1(2) ms\<^sub>2(2)
            by (auto simp:old.path2_def intro:in_set_butlastI)
          with ms show False by auto
        qed
        with ms\<^sub>2 show thesis by (rule that)
      qed
    qed

    show ?thesis
    proof (cases "(set ns\<^sub>1 \<union> set ns\<^sub>2) \<inter> set ms = {}")
      case True
      with ns\<^sub>1 ms show ?thesis by - (rule that, auto)
    next
      case False
      then obtain m' ms' where ms': "g \<turnstile> m'-ms'\<rightarrow>defNode g s" "m' \<in> set ns\<^sub>1 \<union> set ns\<^sub>2" "set (tl ms') \<inter> (set ns\<^sub>1 \<union> set ns\<^sub>2) = {}" "suffix ms' ms"
        by - (rule old.path2_split_last_prop[OF ms(2), of "\<lambda>x. x \<in> set ns\<^sub>1 \<union> set ns\<^sub>2"], auto)
      from this(4) ms(3) have 2: "defNode g r \<notin> set ms'"
        by (auto dest: set_mono_suffix)
      {
        fix n\<^sub>1 ns\<^sub>1 n\<^sub>2 ns\<^sub>2
        assume 4: "m' \<in> set ns\<^sub>1"
        assume ns\<^sub>1: "V \<in> oldDefs g n\<^sub>1" "g \<turnstile> n\<^sub>1-ns\<^sub>1\<rightarrow>defNode g r" "defNode g r \<notin> set (butlast ns\<^sub>1)"
        assume ns\<^sub>2: "V \<in> oldDefs g n\<^sub>2" "g \<turnstile> n\<^sub>2-ns\<^sub>2\<rightarrow>defNode g r" "defNode g r \<notin> set (butlast ns\<^sub>2)"
        assume ns: "set (butlast ns\<^sub>1) \<inter> set (butlast ns\<^sub>2) = {}"
        assume ms': "g \<turnstile> m'-ms'\<rightarrow>defNode g s" "set (tl ms') \<inter> (set ns\<^sub>1 \<union> set ns\<^sub>2) = {}"
        have "m' \<in> set (butlast ns\<^sub>1)"
        proof-
          from ms'(1) have "m' \<in> set ms'" by auto
          with 2 have "defNode g r \<noteq> m'" by auto
          with 4 ns\<^sub>1(2) show ?thesis by - (rule in_set_butlastI, auto simp:old.path2_def)
        qed
        with ns\<^sub>1(2) obtain ns\<^sub>1' where ns\<^sub>1': "g \<turnstile> n\<^sub>1-ns\<^sub>1'\<rightarrow>m'" "m' \<notin> set (butlast ns\<^sub>1')" "strict_prefix ns\<^sub>1' ns\<^sub>1"
          by - (rule old.path2_strict_prefix_ex)
        have thesis
        proof (rule that[OF ns\<^sub>2(1,2), OF ns\<^sub>1(1), of "ns\<^sub>1'@tl ms'"])
          show "g \<turnstile> n\<^sub>1-ns\<^sub>1' @ tl ms'\<rightarrow>defNode g s" using ns\<^sub>1'(1) ms'(1) by auto
          show "set ns\<^sub>2 \<inter> set (ns\<^sub>1' @ tl ms') = {}"
          proof (rule equals0I)
            fix x
            assume x: "x \<in> set ns\<^sub>2 \<inter> set (ns\<^sub>1' @ tl ms')"
            show False
            proof (cases "x \<in> set ns\<^sub>1'")
              case True
              hence 4: "x \<in> set (butlast ns\<^sub>1)" using ns\<^sub>1'(3) by (auto dest:set_mono_strict_prefix)
              with ns\<^sub>1(3) have "x \<noteq> defNode g r" by auto
              with ns\<^sub>2(2) x have "x \<in> set (butlast ns\<^sub>2)"
                by - (rule in_set_butlastI, auto simp:old.path2_def)
              with 4 ns show False by auto
            next
              case False
              with x have "x \<in> set (tl ms')" by simp
              with x ms'(2) show False by auto
            qed
          qed
        qed
      }
      note 4 = this
      show ?thesis
      proof (cases "m' \<in> set ns\<^sub>1")
        case True
        thus ?thesis using ns\<^sub>1 ns\<^sub>2 ns ms'(1,3) by (rule 4)
      next
        case False
        with ms'(2) have "m' \<in> set ns\<^sub>2" by simp
        thus ?thesis using ns ms'(1,3) by - (rule 4[OF _ ns\<^sub>2 ns\<^sub>1], auto)
      qed
    qed
  qed

  text \<open>Lemma 3. If a $\phi$ function p in a block P for a variable v is unnecessary, but non-trivial, then it has an operand q in a block Q,
    such that q is an unnecessary $\phi$ function and Q does not dominate P.\<close>
  lemma 3:
    assumes "unnecessaryPhi g p" "\<not>trivial g p" and[simp]: "p \<in> allVars g"
    obtains q where "phiArg g p q" "unnecessaryPhi g q" "\<not>def_dominates g q p"
  proof-
    note unnecessaryPhi_def[simp]
    let ?P = "defNode g p"

    txt \<open>The node p must have at least two different operands r and s, which are not p itself. Otherwise, p is trivial.\<close>
    from assms obtain r s where rs: "phiArg g p r" "phiArg g p s" "distinct [p, r, s]"
      by - (rule nontrivialE, auto)
    hence[simp]: "var g r = var g p" "var g s = var g p" "r \<in> allVars g" "s \<in> allVars g"
      by (simp_all add:phiArg_same_var)

    txt \<open>They can either be:
      \<^item> The result of a direct assignment to v.
      \<^item> The result of a necessary $\phi$ function r' . This however means that r' was
        reachable by at least two different direct assignments to v. So there is a path
        from a direct assignment of v to p.
      \<^item> Another unnecessary $\phi$ function.\<close>

    let ?R = "defNode g r"
    let ?S = "defNode g s"

    have[simp]: "?R \<noteq> ?S" using rs by - (rule phiArgs_def_distinct, auto)

    have one_unnec: "unnecessaryPhi g r \<or> unnecessaryPhi g s"
    proof (rule ccontr, simp only: de_Morgan_disj not_not)

      txt \<open>Assume neither r in a block R nor s in a block S is an unnecessary $\phi$ function.\<close>
      assume asm: "\<not>unnecessaryPhi g r \<and> \<not>unnecessaryPhi g s"

      txt \<open>Then a path from an assignment to v in a block n crosses R and a path from an assignment to v in a block m crosses S.\<close>
      txt \<open>AMENDMENT: ...so that the paths are disjoint!\<close>
      obtain n ns m ms where ns: "var g p \<in> oldDefs g n" "g \<turnstile> n-ns\<rightarrow>?R" "n \<notin> set (tl ns)"
        and ms: "var g p \<in> oldDefs g m" "g \<turnstile> m-ms\<rightarrow>defNode g s" "m \<notin> set (tl ms)"
        and ns_ms: "set ns \<inter> set ms = {}"
      proof-
        obtain n ns m ms where ns: "var g p \<in> oldDefs g n" "g \<turnstile> n-ns\<rightarrow>?R" and ms: "var g p \<in> oldDefs g m" "g \<turnstile> m-ms\<rightarrow>?S"
          and ns_ms: "set ns \<inter> set ms = {}"
          using asm[THEN conjunct1] asm[THEN conjunct2] by (rule ununnecessaryPhis_disjoint_paths, auto)
        moreover from ns obtain ns' where "g \<turnstile> n-ns'\<rightarrow>?R" "n \<notin> set (tl ns')" "set ns' \<subseteq> set ns"
          by (auto intro: old.simple_path2)
        moreover from ms obtain ms' where "g \<turnstile> m-ms'\<rightarrow>?S" "m \<notin> set (tl ms')" "set ms' \<subseteq> set ms"
          by (auto intro: old.simple_path2)
        ultimately show thesis by - (rule that[of n ns' m ms'], auto)
      qed

      from ns(1) ms(1) obtain v v' where v: "v \<in> defs g n" and v': "v' \<in> defs g m" and[simp]: "var g v = var g p" "var g v' = var g p"
        by (auto simp:oldDefs_def)

      txt \<open>They converge at P or earlier.\<close>
      obtain ns' n' where ns': "g \<turnstile> ?R-ns'\<rightarrow>n'" "r \<in> phiUses g n'" "n' \<in> set (old.predecessors g ?P)" "?R \<notin> set (tl ns')"
        by (rule phiArg_path_ex'[OF rs(1)], auto elim: old.simple_path2)
      obtain ms' m' where ms': "g \<turnstile> ?S-ms'\<rightarrow>m'" "s \<in> phiUses g m'" "m' \<in> set (old.predecessors g ?P)" "?S \<notin> set (tl ms')"
        by (rule phiArg_path_ex'[OF rs(2)], auto elim: old.simple_path2)

      let ?left = "(ns@tl ns')@[?P]"
      let ?right = "(ms@tl ms')@[?P]"

      obtain ns'' ms'' z where z: "old.pathsConverge g n ns'' m ms'' z" "prefix ns'' ?left" "prefix ms'' ?right"
      proof (rule paths_converge_prefix)
        show "n \<noteq> m" using ns ms ns_ms by auto

        show "g \<turnstile> n-?left\<rightarrow>?P" using ns ns'
          by - (rule old.path2_snoc, rule old.path2_app)
        show "length ?left > 1" using ns by auto
        show "g \<turnstile> m-?right\<rightarrow>?P" using ms ms'
          by - (rule old.path2_snoc, rule old.path2_app)
        show "length ?right > 1" using ms by auto

        have "n \<notin> set ms" using ns_ms ns by auto
        moreover have "n \<notin> set (tl ms')" using v rs(2) ms'(2) asm
          by - (rule conventional'[OF ms'(1,4), of s v], auto)
        ultimately show "n \<notin> set (butlast ?right)"
          by (auto simp del:append_assoc)

        have "m \<notin> set ns" using ns_ms ms by auto
        moreover have "m \<notin> set (tl ns')" using v' rs(1) ns'(2) asm
          by - (rule conventional'[OF ns'(1,4), of r v'], auto)
        ultimately show "m \<notin> set (butlast ?left)"
          by (auto simp del:append_assoc)
      qed

      from this(1) ns(1) ms(1) have necessary: "necessaryPhi g (var g p) z" by (rule necessaryPhiI)

      show False
      proof (cases "z = ?P")

        txt \<open>Convergence at P is not possible because p is unnecessary.\<close>
        case True
        thus False using assms(1) necessary by simp
      next

        txt \<open>An earlier convergence would imply a necessary $\phi$ function at this point, which violates the SSA property.\<close>
        case False
        from z(1) have "z \<in> set ns'' \<inter> set ms''" by (auto simp: old.pathsConverge'_def)
        with False have "z \<in> set (ns@tl ns') \<inter> set (ms@tl ms')"
          using z(2,3)[THEN set_mono_prefix] by (auto elim:set_mono_prefix)
        hence z_on: "z \<in> set (tl ns') \<union> set (tl ms')" using ns_ms by auto

        {
          fix r ns' n'
          let ?R = "defNode g r"
          assume ns': "g \<turnstile> ?R-ns'\<rightarrow>n'" "r \<in> phiUses g n'" "n' \<in> set (old.predecessors g (?P))" "?R \<notin> set (tl ns')"
          assume rs: "var g r = var g p"
          have "z \<notin> set (tl ns')"
          proof
            assume asm: "z \<in> set (tl ns')"
            obtain zs where zs: "g \<turnstile> z-zs\<rightarrow>n'" "set (tl zs) \<subseteq> set (tl ns')" using asm
              by - (rule old.path2_split_ex[OF ns'(1)], auto simp: old.path2_not_Nil elim: subsetD[OF set_tl])

            have "phis g (z, r) \<noteq> None"
            proof (rule convergence_prop[OF necessary[simplified rs[symmetric]] zs(1)])
              show "r \<in> allUses g n'" using ns'(2) by auto
              show "r \<notin> defs g z"
              proof
                assume "r \<in> defs g z"
                hence "?R = z" using zs by - (rule defNode_eq, auto)
                thus False using ns'(4) asm by auto
              qed
            next
              fix x
              assume "x \<in> set (tl zs)"
              moreover have "?R \<notin> set (tl zs)" using ns'(4) zs(2) by auto
              ultimately show "r \<notin> allDefs g x"
                by (metis defNode_eq old.path2_in_\<alpha>n set_tl subset_code(1) zs(1))
            qed
            hence "?R = z" using zs(1) by - (rule defNode_eq, auto simp:allDefs_def phiDefs_def)
            thus False using ns'(4) asm by auto
          qed
        }
        note z_not_on = this

        have "z \<notin> set (tl ns')" by (rule z_not_on[OF ns'], simp)
        moreover have "z \<notin> set (tl ms')" by (rule z_not_on[OF ms'], simp)
        ultimately show False using z_on by simp
      qed
    qed

    txt \<open>
So r or s must be an unnecessary $\phi$ function. Without loss of generality, let
this be r.\<close>
    {
      fix r s
      assume r: "unnecessaryPhi g r" and[simp]: "var g r = var g p"
      assume[simp]: "var g s = var g p"
      assume rs: "phiArg g p r" "phiArg g p s" "distinct [p, r, s]"
      let ?R = "defNode g r"
      let ?S = "defNode g s"

      have[simp]: "?R \<noteq> ?S" using rs by - (rule phiArgs_def_distinct, auto)
      have[simp]: "s \<in> allVars g" using rs by auto

      have thesis
      proof (cases "old.dominates g ?R ?P")
        case False

        txt \<open>If R does not dominate P, then r is the sought-after q.\<close>
        thus thesis using r rs(1) by - (rule that)
      next
        case True

        txt \<open>So let R dominate P.
Due to Lemma 2, S does not dominate P.\<close>
        hence 4: "\<not>old.dominates g ?S ?P" using 2[OF rs] by simp

        txt \<open>Employing the SSA property, r /= p
yields R /= P.\<close>
        (* actually not SSA property *)
        have "?R \<noteq> ?P"
        proof (rule notI, rule allDefs_var_disjoint[of ?R g p r, simplified])
          show "r \<in> allDefs g (defNode g r)" using rs(1) by auto
          show "p \<noteq> r" using rs(3) by auto
        qed auto

        txt \<open>Thus, R strictly dominates P.\<close>
        hence "old.strict_dom g ?R ?P" using True by simp

        txt \<open>This implies that R dominates all
predecessors of P, which contain the uses of p, especially the predecessor S' that
contains the use of s.\<close>
        moreover obtain ss' S' where ss': "g \<turnstile> ?S-ss'\<rightarrow>S'"
          and S': "s \<in> phiUses g S'" "S' \<in> set (old.predecessors g ?P)"
          by (rule phiArg_path_ex'[OF rs(2)], simp)
        ultimately have 5: "old.dominates g ?R S'" by - (rule old.dominates_unsnoc, auto)

        txt \<open>Due to the SSA property, there is a path from S to S' that
does not contain R.\<close>
        from ss' obtain ss' where ss': "g \<turnstile> ?S-ss'\<rightarrow>S'" "?S \<notin> set (tl ss')" by (rule old.simple_path2)
        hence "?R \<notin> set (tl ss')" using rs(1,2) S'(1)
          by - (rule conventional'[where v=s and v'=r], auto simp del: phiArg_def)

        txt \<open>Employing R dominates S' this yields R dominates S.\<close>
        hence dom: "old.dominates g ?R ?S" using 5 ss' by - (rule old.dominates_extend)

        txt \<open>Now assume that s is necessary.\<close>
        have "unnecessaryPhi g s"
        proof (rule ccontr)
          assume s: "\<not>unnecessaryPhi g s"

          txt \<open>Let X contain the most recent definition of v on a path from the start block to R.\<close>
          from rs(1) obtain X xs where xs: "g \<turnstile> X-xs\<rightarrow>?R" "var g r \<in> oldDefs g X" "old.EntryPath g xs"
            by - (rule allDef_path_from_simpleDef[of r g], auto simp del: phiArg_def)
          then obtain X xs where xs: "g \<turnstile> X-xs\<rightarrow>?R" "var g r \<in> oldDefs g X" "\<forall>x \<in> set (tl xs). var g r \<notin> oldDefs g x" "old.EntryPath g xs"
            by - (rule old.path2_split_last_prop[OF xs(1), of "\<lambda>x. var g r \<in> oldDefs g x"], auto dest: old.EntryPath_suffix)
          then obtain x where x: "x \<in> defs g X" "var g x = var g r" by (auto simp: oldDefs_def old.path2_def)
          hence[simp]: "X = defNode g x" using xs by - (rule defNode_eq[symmetric], auto)
          from xs obtain xs where xs: "g \<turnstile> X-xs\<rightarrow>?R" "X \<notin> set (tl xs)" "old.EntryPath g xs"
            by - (rule old.simple_path2, auto dest: old.EntryPath_suffix)

          txt \<open>By Definition 2 there are two definitions
of v that render s necessary. Since R dominates S, the SSA property yields that
one of these definitions is contained in a block Y on a path $R \rightarrow^+ S$.\<close>
          (* actually not SSA property *)
          obtain Y ys ys' where Y: "var g s \<in> oldDefs g Y"
            and ys: "g \<turnstile> Y-ys\<rightarrow>?S" "?R \<notin> set ys"
            and ys': "g \<turnstile> ?R-ys'\<rightarrow>Y" "?R \<notin> set (tl ys')"
          proof (cases "phi g s")
            case None
            hence "s \<in> defs g ?S" by - (rule defNode_cases[of s g], auto)
            moreover obtain ns where "g \<turnstile> ?R-ns\<rightarrow>?S" "?R \<notin> set (tl ns)" using dom
              by - (rule old.dominates_path, auto intro: old.simple_path2)
            ultimately show thesis by - (rule that[where ys1="[?S]"], auto dest: oldDefsI)
          next
            case Some
            with s obtain Y\<^sub>1 ys\<^sub>1 Y\<^sub>2 ys\<^sub>2 where "var g s \<in> oldDefs g Y\<^sub>1" "g \<turnstile> Y\<^sub>1-ys\<^sub>1\<rightarrow>?S"
              and "var g s \<in> oldDefs g Y\<^sub>2" "g \<turnstile> Y\<^sub>2-ys\<^sub>2\<rightarrow>?S"
              and ys: "set (butlast ys\<^sub>1) \<inter> set (butlast ys\<^sub>2) = {}" "Y\<^sub>1 \<noteq> Y\<^sub>2"
              by (auto simp:necessaryPhi_def old.pathsConverge'_def)
            moreover from ys(1) have "?R \<notin> set (butlast ys\<^sub>1) \<or> ?R \<notin> set (butlast ys\<^sub>2)" by auto
            ultimately obtain Y ys where ys: "var g s \<in> oldDefs g Y" "g \<turnstile> Y-ys\<rightarrow>?S" "?R \<notin> set (butlast ys)" by auto
            obtain es where es: "g \<turnstile> Entry g-es\<rightarrow>Y" using ys(2)
              by - (atomize_elim, rule old.Entry_reaches, auto)
            have "?R \<in> set (butlast es@ys)" using old.path2_app'[OF es ys(2)] by - (rule old.dominatesE[OF dom])
            moreover have "?R \<noteq> last ys" using old.path2_last[OF ys(2), symmetric] by simp
            hence 1: "?R \<notin> set ys" using ys(3) by (auto dest: in_set_butlastI)
            ultimately have "?R \<in> set (butlast es)" by auto
            then obtain ys' where "g \<turnstile> ?R-ys'\<rightarrow>Y" "?R \<notin> set (tl ys')" using es
              by - (rule old.path2_split_ex, assumption, rule in_set_butlastD, auto intro: old.simple_path2)
            thus thesis using ys(1,2) 1 by - (rule that[of Y ys ys'], auto)
          qed

          from Y obtain y where y: "y \<in> defs g Y" "var g y = var g s" by (auto simp: oldDefs_def)
          hence[simp]: "Y = defNode g y" using ys by - (rule defNode_eq[symmetric], auto)

          obtain rr' R' where "g \<turnstile> ?R-rr'\<rightarrow>R'"
            and R': "r \<in> phiUses g R'" "R' \<in> set (old.predecessors g ?P)"
            by (rule phiArg_path_ex'[OF rs(1)], simp)
          then obtain rr' where rr': "g \<turnstile> ?R-rr'\<rightarrow>R'" "?R \<notin> set (tl rr')" by - (rule old.simple_path2)
          with R' obtain rr where rr: "g \<turnstile> ?R-rr\<rightarrow>?P" and[simp]: "rr = rr' @ [?P]" by (auto intro: old.path2_snoc)
          from ss' S' obtain ss where ss: "g \<turnstile> ?S-ss\<rightarrow>?P" and[simp]: "ss = ss' @ [?P]" by (auto intro: old.path2_snoc)

          txt \<open>Thus, there are paths $X \rightarrow^+ P$ and $Y \rightarrow^+ P$ rendering p necessary. Since this is a
contradiction, s is unnecessary and the sought-after q.\<close>
          have "old.pathsConverge g X (butlast xs@rr) Y (ys@tl ss) ?P"
          proof (rule old.pathsConvergeI)
            show "g \<turnstile> X-butlast xs@rr\<rightarrow>?P" using xs rr by auto
            show "g \<turnstile> Y-ys@tl ss\<rightarrow>?P" using ys ss by auto

            {
              assume "X = ?P"
              moreover have "p \<in> phiDefs g ?P" using assms(1) by (auto simp:phiDefs_def phi_def)
              ultimately have False using simpleDefs_phiDefs_disjoint[of X g] allDefs_var_disjoint[of X g] x by (cases "x = p", auto)
            }
            thus "length (butlast xs@rr) > 1" using xs rr by - (rule old.path2_nontriv, auto)

            {
              assume "Y = ?P"
              moreover have "p \<in> phiDefs g ?P" using assms(1) by (auto simp:phiDefs_def phi_def)
              ultimately have False using simpleDefs_phiDefs_disjoint[of Y g] allDefs_var_disjoint[of Y g] y by (cases "y = p", auto)
            }
            thus "length (ys@tl ss) > 1" using ys ss by - (rule old.path2_nontriv, auto)
            show "set (butlast (butlast xs @rr)) \<inter> set (butlast (ys @ tl ss)) = {}"
            proof (rule equals0I)
              fix z
              assume "z \<in> set (butlast (butlast xs@rr)) \<inter> set (butlast (ys@tl ss))"
              moreover {
                assume asm: "z \<in> set (butlast xs)" "z \<in> set ys"
                have "old.shortestPath g z < old.shortestPath g ?R" using asm(1) xs(3)
                  by - (subst old.path2_last[OF xs(1)], rule old.EntryPath_butlast_less_last)
                moreover
                from ys asm(2) obtain ys' where ys': "g \<turnstile> z-ys'\<rightarrow>?S" "suffix ys' ys"
                  by - (rule old.path2_split_ex, auto simp: Sublist.suffix_def)
                have "old.dominates g ?R z" using ys(2) set_tl[of ys] suffix_tl_subset[OF ys'(2)]
                  by - (rule old.dominates_extend[OF dom ys'(1)], auto)
                hence "old.shortestPath g ?R \<le> old.shortestPath g z"
                  by (rule old.dominates_shortestPath_order, auto)
                ultimately have False by simp
              }
              moreover {
                assume asm: "z \<in> set (butlast xs)" "z \<in> set (tl ss')"
                have "old.shortestPath g z < old.shortestPath g ?R" using asm(1) xs(3)
                  by - (subst old.path2_last[OF xs(1)], rule old.EntryPath_butlast_less_last)
                moreover
                from asm(2) obtain ss\<^sub>2 where ss\<^sub>2: "g \<turnstile> z-ss\<^sub>2\<rightarrow>S'" "set (tl ss\<^sub>2) \<subseteq> set (tl ss')"
                  using set_tl[of ss'] by - (rule old.path2_split_ex[OF ss'(1)], auto simp: old.path2_not_Nil dest: in_set_butlastD)
                from S'(1) ss'(1) have "old.dominates g ?S S'" by - (rule allUses_dominated, auto)
                hence "old.dominates g ?S z" using ss'(2) ss\<^sub>2(2)
                  by - (rule old.dominates_extend[OF _ ss\<^sub>2(1)], auto)
                with dom have "old.dominates g ?R z" by auto
                hence "old.shortestPath g ?R \<le> old.shortestPath g z"
                  by - (rule old.dominates_shortestPath_order, auto)
                ultimately have False by simp
              }
              moreover
              have "?R \<noteq> Y" using ys by (auto simp:old.path2_def)
              with ys'(1) have 1: "length ys' > 1" by (rule old.path2_nontriv)
              {
                assume asm: "z \<in> set rr'" "z \<in> set ys"
                then obtain ys\<^sub>1 where ys\<^sub>1: "g \<turnstile> Y-ys\<^sub>1\<rightarrow>z" "prefix ys\<^sub>1 ys"
                  by - (rule old.path2_split_ex[OF ys(1)], auto)
                from asm obtain rr\<^sub>2 where rr\<^sub>2: "g \<turnstile> z-rr\<^sub>2\<rightarrow>R'" "set (tl rr\<^sub>2) \<subseteq> set (tl rr')"
                  by - (rule old.path2_split_ex[OF rr'(1)], auto simp: old.path2_not_Nil)
                let ?path = "ys'@tl (ys\<^sub>1@tl rr\<^sub>2)"
                have "var g y \<noteq> var g r"
                proof (rule conventional)
                  show "g \<turnstile> ?R-?path\<rightarrow>R'" using ys' ys\<^sub>1 rr\<^sub>2 by (intro old.path2_app)
                  show "r \<in> allDefs g ?R" using rs by auto
                  show "r \<in> allUses g R'" using R' by auto

                  thus "Y \<in> set (tl ?path)" using ys'(1) 1
                    by (auto simp:old.path2_def old.path2_not_Nil intro:last_in_tl)
                  show "y \<in> allDefs g Y" using y by simp
                  show "defNode g r \<notin> set (tl ?path)"
                    using ys' ys\<^sub>1(1) ys(2) rr\<^sub>2(2) rr'(2) prefix_tl_subset[OF ys\<^sub>1(2)] set_tl[of ys] by (auto simp: old.path2_not_Nil)
                qed
                hence False using y by simp
              }
              moreover {
                assume asm: "z \<in> set rr'" "z \<in> set (tl ss')"
                then obtain ss'\<^sub>1 where ss'\<^sub>1: "g \<turnstile> ?S-ss'\<^sub>1\<rightarrow>z" "prefix ss'\<^sub>1 ss'" using ss'
                  by - (rule old.path2_split_ex[OF ss'(1), of z], auto)
                from asm obtain rr'\<^sub>2 where rr'\<^sub>2: "g \<turnstile> z-rr'\<^sub>2\<rightarrow>R'" "suffix rr'\<^sub>2 rr'"
                  using rr' by - (rule old.path2_split_ex, auto simp: Sublist.suffix_def)
                let ?path = "butlast ys'@(ys@tl (ss'\<^sub>1@tl rr'\<^sub>2))"
                have "var g s \<noteq> var g r"
                proof (rule conventional)
                  show "g \<turnstile> ?R-?path\<rightarrow>R'" using ys' ys ss'\<^sub>1 rr'\<^sub>2(1) by (intro old.path2_app old.path2_app')
                  show "r \<in> allDefs g ?R" using rs by auto
                  show "r \<in> allUses g R'" using R' by auto
                  from 1 have[simp]: "butlast ys' \<noteq> []" by (cases ys', auto)
                  show "?S \<in> set (tl ?path)" using ys(1) by auto
                  show "s \<in> allDefs g ?S" using rs(2) by auto
                  have "?R \<notin> set (tl ss')"
                    using rs S'(1) by - (rule conventional''[OF ss'], auto)
                  thus "defNode g r \<notin> set (tl ?path)"
                    using ys(1) ss'\<^sub>1(1) suffix_tl_subset[OF rr'\<^sub>2(2)] ys'(2) ys(2) rr'(2) prefix_tl_subset[OF ss'\<^sub>1(2)]
                    by (auto simp: List.butlast_tl[symmetric] old.path2_not_Nil dest: in_set_butlastD)
                qed
                hence False using y by simp
              }
              ultimately show False using rr'(1) ss'(1)
                by (auto simp del: append_assoc simp: append_assoc[symmetric] old.path2_not_Nil dest: in_set_tlD)
            qed
          qed
          hence "necessaryPhi' g p" using xs oldDefsI[OF x(1)] x(2) oldDefsI[OF y(1)] y(2)
            by - (rule necessaryPhiI[where v="var g p"], assumption, auto simp:old.path2_def)
          with assms(1) show False by auto
        qed
        thus ?thesis using rs(2) 4 by - (rule that)
      qed
    }
    from one_unnec this[of r s] this[of s r] rs show thesis by auto
  qed

text \<open>Theorem 1. A program in SSA form with a reducible CFG G without any trivial $\phi$ functions is in minimal SSA form.\<close>
  theorem reducible_nonredundant_imp_minimal:
    assumes "old.reducible g" "\<not>redundant g"
    shows "cytronMinimal g"
  unfolding cytronMinimal_def
  proof (rule, rule)
    txt \<open>
Proof. Assume G is not in minimal SSA form and contains no trivial $\phi$ functions.
We choose an unnecessary $\phi$ function p.\<close>
    fix p
    assume[simp]: "p \<in> allVars g" and phi: "phi g p \<noteq> None"
    show "necessaryPhi' g p"
    proof (rule ccontr)
      assume "\<not>necessaryPhi' g p"
      with phi have asm: "unnecessaryPhi g p" by (simp add: unnecessaryPhi_def)
      let ?A = "{p. p \<in> allVars g \<and> unnecessaryPhi g p}"
      let ?r = "\<lambda>p q. p \<in> ?A \<and> q \<in> ?A \<and> phiArg g p q \<and> \<not>def_dominates g q p"
      let ?r' = "{(p,q). ?r p q}"
      note phiArg_def[simp del]

      txt \<open>Due to Lemma 3, p has an operand q,
which is unnecessary and does not dominate p. By induction q has an unnecessary
$\phi$ function as operand as well and so on. Since the program only has a finite
number of operations, there must be a cycle when following the q chain.\<close>
      obtain q where q: "(q,q) \<in> ?r'\<^sup>+" "q \<in> ?A"
      proof (rule serial_on_finite_cycle)
        show "serial_on ?A ?r'"
        proof (rule serial_onI)
          fix x
          assume "x \<in> ?A"
          then obtain y where "unnecessaryPhi g y" "phiArg g x y" "\<not>def_dominates g y x"
            using assms(2) by - (rule 3, auto simp: redundant_def)
          thus "\<exists>y \<in> ?A. (x,y) \<in> ?r'" using \<open>x \<in> ?A\<close> by - (rule bexI[where x=y], auto)
        qed
        show "?A \<noteq> {}" using asm by (auto intro!: exI)
      qed auto

      txt \<open>A cycle in the $\phi$ functions implies a cycle in G.\<close>
      then obtain ns where ns: "g \<turnstile> defNode g q-ns\<rightarrow>defNode g q" "length ns > 1"
        "\<forall>n \<in> set (butlast ns). \<exists>p q m ns'. ?r p q \<and> g \<turnstile> defNode g q-ns'\<rightarrow>m \<and> (defNode g q) \<notin> set (tl ns') \<and> q \<in> phiUses g m \<and> m \<in> set (old.predecessors g (defNode g p)) \<and> n \<in> set ns' \<and> set ns' \<subseteq> set ns \<and> defNode g p \<in> set ns"
        by - (rule phiArg_tranclp_path_ex[where r="?r"], auto simp: tranclp_unfold)

      txt \<open>As G is reducible, the control flow
cycle contains one entry block, which dominates all other blocks in the cycle.\<close>
      obtain n where n: "n \<in> set ns" "\<forall>m \<in> set ns. old.dominates g n m"
        using assms(1)[unfolded old.reducible_def, rule_format, OF ns(1)] by auto

      txt \<open>Without loss of generality, let q be in the entry block, which means it dominates p.\<close>
      have "n \<in> set (butlast ns)"
      proof (cases "n = last ns")
        case False
        with n(1) show ?thesis by (rule in_set_butlastI)
      next
        case True
        with ns(1) have "n = hd ns" by (auto simp: old.path2_def)
        with ns(2) show ?thesis by - (auto intro: hd_in_butlast)
      qed
      then obtain p q ns' m where ns': "?r p q" "g \<turnstile> defNode g q-ns'\<rightarrow>m" "defNode g q \<notin> set (tl ns')" "q \<in> phiUses g m" "m \<in> set (old.predecessors g (defNode g p))" "n \<in> set ns'" "set ns' \<subseteq> set ns" "defNode g p \<in> set ns"
        by - (drule ns(3)[THEN bspec], auto)
      hence "old.dominates g (defNode g q) n" by - (rule defUse_path_dominated, auto)
      moreover from ns' n(2) have n_dom: "old.dominates g n (defNode g q)" "old.dominates g n (defNode g p)" by - (auto elim!:bspec)
      ultimately have "defNode g q = n" by auto

      txt \<open>Therefore, our assumption is wrong and G is either in minimal SSA form or there exist trivial $\phi$ functions.\<close>
      with ns'(1) n_dom(2) show False by auto
    qed
  qed
end

context CFG_SSA_Transformed
begin
  definition "phiCount g = card ((\<lambda>(n,v). (n, var g v)) ` dom (phis g))"

  lemma phiCount: "phiCount g = card (dom (phis g))"
  proof-
    have 1: "v = v'"
      if asm: "phis g (n, v) \<noteq> None" "phis g (n, v') \<noteq> None" "var g v = var g v'"
      for n v v'
    proof (rule ccontr)
      from asm have[simp]: "v \<in> allDefs g n" "v' \<in> allDefs g n" by (auto simp: phiDefs_def allDefs_def)
      from asm have[simp]: "n \<in> set (\<alpha>n g)" by - (auto simp: phis_in_\<alpha>n)
      assume "v \<noteq> v'"
      with asm show False
        by - (rule allDefs_var_disjoint[of n g v v', THEN notE], auto)
    qed

    show ?thesis
    unfolding phiCount_def
    apply (rule card_image)
    apply (rule inj_onI)
    by (auto intro!: 1)
  qed

  theorem phi_count_minimal:
    assumes "cytronMinimal g" "pruned g"
    assumes "CFG_SSA_Transformed \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs' uses' phis' var'"
    shows "card (dom (phis g)) \<le> card (dom (phis' g))"
  proof-
    interpret other: CFG_SSA_Transformed \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs' uses' phis' var'
      by (rule assms(3))
    {
      fix n v
      assume asm: "phis g (n,v) \<noteq> None"
      from asm have[simp]: "v \<in> phiDefs g n" "v \<in> allDefs g n" by (auto simp: phiDefs_def allDefs_def)
      from asm have[simp]: "defNode g v = n" "n \<in> set (\<alpha>n g)" by - (auto simp: phis_in_\<alpha>n)
      from asm have "liveVal g v"
        by - (rule \<open>pruned g\<close>[unfolded pruned_def, THEN bspec, of n, rule_format]; simp)
      then obtain ns m where ns: "g \<turnstile> n-ns\<rightarrow>m" "var g v \<in> oldUses g m" "\<And>x. x \<in> set (tl ns) \<Longrightarrow> var g v \<notin> oldDefs g x"
        by (rule liveVal_use_path, simp)
      have "\<exists>v'. phis' g (n,v') \<noteq> None \<and> var g v = var' g v'"
      proof (rule other.convergence_prop'[OF _ ns(1)])
        from asm show "necessaryPhi g (var g v) n"
          by - (rule \<open>cytronMinimal g\<close>[unfolded cytronMinimal_def, THEN bspec, of v, simplified, rule_format],
            auto simp: cytronMinimal_def phi_def, auto intro: allDefs_in_allVars[where n=n])
        with ns(1,2) show "var g v \<in> var' g ` other.allUses g m"
          by (subst(asm) other.oldUses_def, auto simp: image_def allUses_def other.oldUses_def intro!: bexI)
        have "var g v \<notin> oldDefs g n"
          by (rule simpleDefs_phiDefs_var_disjoint, auto)
        then show "\<And>x. x \<in> set ns \<Longrightarrow> var g v \<notin> oldDefs g x"
          using ns(1) by (case_tac "x = hd ns", auto dest: ns(3) not_hd_in_tl dest: old.path2_hd)
      qed auto
    }
    note 1 = this

    have "phiCount g \<le> other.phiCount g"
    unfolding phiCount_def other.phiCount_def
    apply (rule card_mono)
     apply (rule finite_imageI)
     apply (rule other.phis_finite)
    by (auto simp: dom_def image_def simp del: not_None_eq intro!: 1)

    thus ?thesis by (simp add: phiCount other.phiCount)
  qed
end

end
