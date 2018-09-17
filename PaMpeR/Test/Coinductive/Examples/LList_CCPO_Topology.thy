(*  Title:       LList_CCPO_Topology.thy
    Author:      Johannes Hölzl, TU Munich
    Author:      Andreas Lochbihler, ETH Zurich
*)

section {* A CCPO topology on lazy lists with examples *}

theory LList_CCPO_Topology imports
  CCPO_Topology
  "../Coinductive_List_Prefix"
begin

lemma closed_Collect_eq_isCont:
  fixes f g :: "'a :: t2_space \<Rightarrow> 'b::t2_space"
  assumes f: "\<And>x. isCont f x" and g: "\<And>x. isCont g x"
  shows "closed {x. f x = g x}"
  by (intro closed_Collect_eq continuous_at_imp_continuous_on ballI assms)

instantiation llist :: (type) ccpo_topology
begin

definition open_llist :: "'a llist set \<Rightarrow> bool" where
  "open_llist A \<longleftrightarrow> (\<forall>C. chain C \<longrightarrow> C \<noteq> {} \<longrightarrow> Sup C \<in> A \<longrightarrow> C \<inter> A \<noteq> {})"

instance
  by intro_classes (simp add: open_llist_def)

end

subsection {* Continuity and closedness of predefined constants *}

lemma tendsto_mcont_llist: "mcont lSup lprefix lSup lprefix f \<Longrightarrow> f \<midarrow>l\<rightarrow> f l"
  by (auto simp add: Sup_llist_def[abs_def] intro!: tendsto_mcont)

lemma tendsto_ltl[THEN tendsto_compose, tendsto_intros]: "ltl \<midarrow>l\<rightarrow> ltl l"
  by (intro tendsto_mcont_llist mcont_ltl)

lemma tendsto_lappend2[THEN tendsto_compose, tendsto_intros]: "lappend l \<midarrow>l'\<rightarrow> lappend l l'"
  by (intro tendsto_mcont_llist mcont_lappend2)

lemma tendsto_LCons[THEN tendsto_compose, tendsto_intros]: "LCons x \<midarrow>l\<rightarrow> LCons x l"
  by (intro tendsto_mcont_llist mcont_LCons)

lemma tendsto_lmap[THEN tendsto_compose, tendsto_intros]: "lmap f \<midarrow>l\<rightarrow> lmap f l"
  by (intro tendsto_mcont_llist mcont_lmap)

lemma tendsto_llength[THEN tendsto_compose, tendsto_intros]: "llength \<midarrow>l\<rightarrow> llength l"
  by (intro tendsto_mcont) (simp add: Sup_llist_def[abs_def])

lemma tendsto_lset[THEN tendsto_compose, tendsto_intros]: "lset \<midarrow>l\<rightarrow> lset l"
  by(rule tendsto_mcont)(simp add: Sup_llist_def[abs_def])

lemma open_lhd: "open {l. \<not> lnull l \<and> lhd l = x}"
  unfolding open_ccpo set_eq_iff
proof (simp add: imp_conjL Sup_llist_def del: lhd_lSup, intro allI impI)
  fix C assume "Complete_Partial_Order.chain lprefix C" "lhd (lSup C) = x"
  moreover assume "\<exists>c\<in>C. \<not> lnull c"
  then obtain c where "c \<in> C" "\<not> lnull c"
    by auto
  ultimately show "\<exists>c. c \<in> C \<and> \<not> lnull c \<and> lhd c = x"
    by (force simp: lhd_lSup_eq)
qed

lemma open_LCons': assumes A: "open A" shows "open (LCons x ` A)"
proof -
  have "open (ltl -` A \<inter> {l. \<not> lnull l \<and> lhd l = x})"
    by (intro open_Int open_vimageI open_lhd A tendsto_intros)
  also have "(ltl -` A \<inter> {l. \<not> lnull l \<and> lhd l = x}) = LCons x ` A"
    by force
  finally show ?thesis .
qed

lemma open_Ici: "lfinite xs \<Longrightarrow> open {xs ..}"
proof (induct xs rule: lfinite.induct)
  case lfinite_LNil then show ?case
    by (simp add: atLeast_def)
next
  case (lfinite_LConsI xs x)
  moreover have "{LCons x xs ..} = LCons x ` {xs ..}"
    by (auto simp: LCons_lprefix_conv)
  ultimately show ?case
    by (auto intro: open_LCons')
qed

lemma open_lfinite[simp]: "lfinite x \<Longrightarrow> open {x}"
proof (induct rule: lfinite.induct)
  show "open {LNil}"
    using open_ccpo_Iic[of LNil] by (simp add: atMost_def lnull_def)
qed (auto dest: open_LCons')

lemma open_singleton_iff_lfinite: "open {x} \<longleftrightarrow> lfinite x"
proof
  assume "lfinite x" then show "open {x}"
    unfolding compact_eq_lfinite[symmetric] Sup_llist_def[abs_def, symmetric] less_eq_llist_def[abs_def, symmetric]
    by (rule open_singletonI_compact)
next
  assume "open {x}"
  show "lfinite x"
  proof (rule ccontr)
    let ?C = "{ys. lprefix ys x \<and> ys \<noteq> x}"
    assume inf: "\<not> lfinite x"
    note lSup_strict_prefixes[OF this] `open {x}`
    moreover have "chain ?C"
      using lprefixes_chain[of x] by (auto dest: chain_compr)
    moreover have "?C \<noteq> {}"
      using inf by (cases x) auto
    ultimately show False
      by (auto simp: open_ccpo Sup_llist_def)
  qed
qed

lemma closure_eq_lfinite:
  assumes closed_Q: "closed {xs. Q xs}"
  assumes downwards_Q: "\<And>xs ys. Q xs \<Longrightarrow> lprefix ys xs \<Longrightarrow> Q ys"
  shows "{xs. Q xs} = closure {xs. lfinite xs \<and> Q xs}"
proof (rule closure_unique[symmetric])
  fix T assume T: "{xs. lfinite xs \<and> Q xs} \<subseteq> T" and "closed T"

  show "{xs. Q xs} \<subseteq> T"
  proof clarify
    fix xs :: "'a llist"
    let ?F = "{ys. lprefix ys xs \<and> lfinite ys}"
    assume "Q xs"
    with T downwards_Q have "?F \<subseteq> T"
      by auto
    moreover have "chain ?F" "?F \<noteq> {}"
      by (auto intro: lprefixes_chain chain_subset)
    moreover have "lSup ?F = xs"
      by (rule lSup_finite_prefixes)
    ultimately show "xs \<in> T"
      using `closed T` by (auto simp: closed_ccpo Sup_llist_def)
  qed
qed (auto simp: closed_Q)

lemma closure_lfinite: "closure {xs. lfinite xs} = UNIV"
  using closure_eq_lfinite[of "\<lambda>_. True"] by auto

lemma closed_ldistinct: "closed {xs. ldistinct xs}"
  unfolding closed_ccpo by (auto simp: ldistinct_lSup Sup_llist_def subset_eq)

lemma ldistinct_closure: "{xs. ldistinct xs} = closure {xs. lfinite xs \<and> ldistinct xs}"
  by (rule closure_eq_lfinite[OF closed_ldistinct ldistinct_lprefix])

lemma closed_ldistinct': "(\<And>x. isCont f x) \<Longrightarrow> closed {xs. ldistinct (f xs)}"
  using continuous_closed_vimage[of _ f, OF closed_ldistinct] by auto

lemma closed_lsorted: "closed {xs. lsorted xs}"
  unfolding closed_ccpo by (auto simp: lsorted_lSup Sup_llist_def subset_eq)

lemma lsorted_closure: "{xs. lsorted xs} = closure {xs. lfinite xs \<and> lsorted xs}"
  by (rule closure_eq_lfinite[OF closed_lsorted lsorted_lprefixD])

lemma closed_lsorted': "(\<And>x. isCont f x) \<Longrightarrow> closed {xs. lsorted (f xs)}"
  using continuous_closed_vimage[of _ f, OF closed_lsorted] by auto

lemma closed_in_lset: "closed {l. x \<in> lset l}"
  unfolding closed_ccpo by (auto simp add: subset_eq lset_lSup Sup_llist_def)

lemma closed_llist_all2:
  "closed {(x, y). llist_all2 R x y}"
proof -
  { fix a b assume *: "\<And>A B. open A \<Longrightarrow> open B \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> (\<exists>x\<in>A. \<exists>y\<in>B. llist_all2 R x y)"
    then have "llist_all2 R a b"
    proof (coinduction arbitrary: a b)
      case LNil
      from LNil[rule_format, of "{LNil}" "- {LNil}"] LNil[rule_format, of "- {LNil}" "{LNil}"]
      show ?case
        by (auto simp: closed_def[symmetric] lnull_def)
    next
      case LCons
      show ?case
      proof
        show ?lhd
          using LCons(1)[rule_format, OF open_lhd open_lhd, of "lhd a" "lhd b"] LCons(2,3)
          by (auto dest: llist_all2_lhdD)
        show ?ltl
        proof (rule, simp, safe)
          fix A B assume "open A" "open B" "ltl a \<in> A" "ltl b \<in> B"
          with LCons(1)[rule_format, OF open_LCons' open_LCons', of A B "lhd a" "lhd b"] LCons(2,3)
          show "\<exists>a'\<in>A. \<exists>b'\<in>B. llist_all2 R a' b'"
            by (auto simp: not_lnull_conv)
        qed
      qed
    qed }
  then show ?thesis
    unfolding closed_def open_prod_def
    by (auto simp: subset_eq)
qed

lemma closed_list_all2:
  fixes f g :: "'b::t2_space \<Rightarrow> 'a llist"
  assumes f: "\<And>x. isCont f x" and g: "\<And>x. isCont g x"
  shows "closed {x. llist_all2 R (f x) (g x)}"
  using  continuous_closed_vimage[OF closed_llist_all2  isCont_Pair[OF f g]] by simp

lemma at_botI_lfinite[simp]: "lfinite l \<Longrightarrow> at l = bot"
  by (simp add: at_eq_bot_iff)

lemma at_eq_lfinite: "at l = (if lfinite l then bot else at' l)"
  by (auto simp: at'_def open_singleton_iff_lfinite)

lemma eventually_lfinite: "eventually lfinite (at' x)"
  apply (simp add: at'_def open_singleton_iff_lfinite eventually_principal eventually_at_topological)
  apply (intro exI[of _ "{.. x}"] impI conjI open_ccpo_Iic)
  apply (auto simp: lstrict_prefix_def intro!: lstrict_prefix_lfinite1)
  done

lemma eventually_nhds_llist:
  "eventually P (nhds l) \<longleftrightarrow> (\<exists>xs\<le>l. lfinite xs \<and> (\<forall>ys\<ge>xs. ys \<le> l \<longrightarrow> P ys))"
  unfolding eventually_nhds
proof safe
  let ?F = "{l'. lprefix l' l \<and> lfinite l'}"
  fix A assume "open A" "l \<in> A" "\<forall>l\<in>A. P l"
  moreover have "chain ?F" "?F \<noteq> {}"
    by (auto simp: chain_def dest: lprefix_down_linear)
  moreover have "Sup ?F = l"
    unfolding Sup_llist_def by (rule lSup_finite_prefixes)
  ultimately have "\<exists>xs. xs \<in> ?F \<and> (\<forall>ys\<ge>xs. ys \<in> ?F \<longrightarrow> P ys)"
    using open_ccpoD[of A ?F] by auto
  then show "\<exists>xs\<le>l. lfinite xs \<and> (\<forall>ys\<ge>xs. ys \<le> l \<longrightarrow> P ys)"
    by (metis (lifting) `l \<in> A` `\<forall>l\<in>A. P l` le_llist_conv_lprefix mem_Collect_eq not_lfinite_lprefix_conv_eq)
next
  fix xs assume "xs \<le> l" "lfinite xs" "\<forall>ys\<ge>xs. ys \<le> l \<longrightarrow> P ys"
  then show "\<exists>S. open S \<and> l \<in> S \<and> Ball S P"
    by (intro exI[of _ "{xs ..} \<inter> {.. l}"] conjI open_Int open_Ici open_ccpo_Iic) auto
qed

lemma nhds_lfinite: "lfinite l \<Longrightarrow> nhds l = principal {l}"
  unfolding filter_eq_iff eventually_principal eventually_nhds_llist
  by (auto simp del: le_llist_conv_lprefix)

lemma eventually_at'_llist:
  "eventually P (at' l) \<longleftrightarrow> (\<exists>xs\<le>l. lfinite xs \<and> (\<forall>ys\<ge>xs. lfinite ys \<longrightarrow> ys \<le> l \<longrightarrow> P ys))"
proof cases
  assume "lfinite l"
  then show ?thesis
    by (auto simp add: eventually_filtermap at'_def open_singleton_iff_lfinite
                       eventually_principal lfinite_eq_range_llist_of)
next
  assume "\<not> lfinite l"
  then show ?thesis
    by (auto simp: eventually_filtermap at'_def open_singleton_iff_lfinite
                   eventually_at_filter eventually_nhds_llist)
       (metis not_lfinite_lprefix_conv_eq)
qed

lemma eventually_at'_llistI: "(\<And>xs. lfinite xs \<Longrightarrow> xs \<le> l \<Longrightarrow> P xs) \<Longrightarrow> eventually P (at' l)"
  by (auto simp: eventually_at'_llist)

lemma Lim_at'_lfinite: "lfinite xs \<Longrightarrow> Lim (at' xs) f = f xs"
  by (rule tendsto_Lim[OF at'_bot]) (auto simp add: at'_def topological_tendstoI eventually_principal)

lemma filterlim_at'_list:
  "(f \<longlongrightarrow> y) (at' (x::'a llist)) \<Longrightarrow> f \<midarrow>x\<rightarrow> y"
  unfolding at'_def by (auto split: if_split_asm simp: open_singleton_iff_lfinite)

lemma tendsto_mcont_llist': "mcont lSup lprefix lSup lprefix f \<Longrightarrow> (f \<longlongrightarrow> f x) (at' (x :: 'a llist))"
by(auto simp add: at'_def nhds_lfinite[symmetric] open_singleton_iff_lfinite tendsto_at_iff_tendsto_nhds[symmetric] intro: tendsto_mcont_llist)

lemma tendsto_closed:
  assumes eq: "closed {x. P x}"
  assumes ev: "\<And>ys. lfinite ys \<Longrightarrow> ys \<le> x \<Longrightarrow> P ys"
  shows "P x"
proof -
  have "x \<in> {x. P x}"
  proof (rule Lim_in_closed_set)
    show "eventually (\<lambda>x. x \<in> {x. P x}) (at' x)"
      unfolding eq using ev
      by (force intro!: eventually_at'_llistI)
  qed (rule assms tendsto_id_at' at'_bot)+
  then show ?thesis
    by simp
qed


lemma tendsto_Sup_at':
  fixes f :: "'a llist \<Rightarrow> 'b::ccpo_topology"
  assumes f: "\<And>x y. x \<le> y \<Longrightarrow> lfinite x \<Longrightarrow> lfinite y \<Longrightarrow> f x \<le> f y"
  shows "(f \<longlongrightarrow> (Sup (f`{xs. lfinite xs \<and> xs \<le> l}))) (at' l)"
proof (rule topological_tendstoI)
  let ?F = "{xs. lfinite xs \<and> xs \<le> l}"

  have ch_F: "chain (f`?F)" "f`?F \<noteq> {}"
    by (rule chain_imageI[OF chain_subset, OF lprefixes_chain]) (auto simp: f)

  fix A assume A: "open A" "Sup (f`?F) \<in> A" then show "eventually (\<lambda>x. f x \<in> A) (at' l)"
    using open_ccpoD[OF _ ch_F, OF A] by (auto simp: eventually_at'_llist f simp del: le_llist_conv_lprefix)
qed

lemma tendsto_Lim_at':
  fixes f :: "'a llist \<Rightarrow> 'b::ccpo_topology"
  assumes f: "\<And>l. f l = Lim (at' l) f'"
  assumes mono: "\<And>x y. x \<le> y \<Longrightarrow> lfinite x \<Longrightarrow> lfinite y \<Longrightarrow> f' x \<le> f' y"
  shows "(f \<longlongrightarrow> f l) (at' l)"
  unfolding f[abs_def]
  apply (subst filterlim_cong[OF refl refl eventually_mono[OF eventually_lfinite Lim_at'_lfinite]])
  apply assumption
  apply (rule tendsto_LimI[OF tendsto_Sup_at'[OF mono]])
  apply assumption+
  done


lemma isCont_LCons[THEN isCont_o2[rotated]]: "isCont (LCons x) l"
  by (simp add: isCont_def tendsto_LCons tendsto_ident_at)

lemma isCont_lmap[THEN isCont_o2[rotated]]: "isCont (lmap f) l"
  by (simp add: isCont_def tendsto_lmap tendsto_ident_at)

lemma isCont_lappend[THEN isCont_o2[rotated]]: "isCont (lappend xs) ys"
  by (simp add: isCont_def tendsto_lappend2 tendsto_ident_at)

lemma isCont_lset[THEN isCont_o2[rotated]]: "isCont lset xs"
  by(simp add: isCont_def tendsto_lset tendsto_ident_at)



subsection {* Define @{term lfilter} as continuous extension *}

definition "lfilter' P l = Lim (at' l) (\<lambda>xs. llist_of (filter P (list_of xs)))"

lemma tendsto_lfilter: "(lfilter' P \<longlongrightarrow> lfilter' P xs) (at' xs)"
  by (rule tendsto_Lim_at'[OF lfilter'_def]) (auto simp add: lfinite_eq_range_llist_of less_eq_list_def prefix_def)

lemma isCont_lfilter[THEN isCont_o2[rotated]]: "isCont (lfilter' P) l"
  by (simp add: isCont_def filterlim_at'_list tendsto_lfilter)

lemma lfilter'_lfinite[simp]: "lfinite xs \<Longrightarrow> lfilter' P xs = llist_of (filter P (list_of xs))"
  by (simp add: lfilter'_def Lim_at'_lfinite)

lemma lfilter'_LNil: "lfilter' P LNil = LNil"
  by simp

lemma lfilter'_LCons [simp]: "lfilter' P (LCons a xs) = (if P a then LCons a (lfilter' P xs) else lfilter' P xs)"
  by (rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont])
     (auto intro!: isCont_lfilter isCont_LCons isCont_If)

lemma ldistinct_lfilter': "ldistinct l \<Longrightarrow> ldistinct (lfilter' P l)"
  by (rule tendsto_closed[OF closed_ldistinct', OF isCont_lfilter])
     (auto intro!: distinct_filter dest: ldistinct_lprefix simp: lfinite_eq_range_llist_of)

lemma lfilter'_lmap: "lfilter' P (lmap f xs) = lmap f (lfilter' (P \<circ> f) xs)"
  by (rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont])
     (auto simp add: filter_map comp_def intro!: isCont_lmap isCont_lfilter)

lemma lfilter'_lfilter': "lfilter' P (lfilter' Q xs) = lfilter' (\<lambda>x. Q x \<and> P x) xs"
  by (rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont]) (auto intro!: isCont_lfilter)

lemma lfilter'_LNil_I[simp]: "(\<forall>x \<in> lset xs. \<not> P x) \<Longrightarrow> lfilter' P xs = LNil"
  by (rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont])
     (auto simp add: lfinite_eq_range_llist_of llist_of_eq_LNil_conv filter_empty_conv intro: isCont_lfilter dest!: lprefix_lsetD)

lemma lset_lfilter': "lset (lfilter' P xs) = lset xs \<inter> {x. P x}"
  by(rule tendsto_closed[OF closed_Collect_eq_isCont])
    (auto 4 3 intro: isCont_lset isCont_lfilter isCont_inf2)

lemma lfilter'_eq_LNil_iff: "lfilter' P xs = LNil \<longleftrightarrow> (\<forall>x\<in>lset xs. \<not> P x)"
  using lset_lfilter'[of P xs] by auto

lemma lfilter'_eq_lfilter: "lfilter' P xs = lfilter P xs"
using isCont_lfilter
proof(rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont])
  fix ys :: "'a llist"
  assume "lfinite ys"
  thus "lfilter' P ys = lfilter P ys" by induction simp_all
qed(simp_all add: isCont_def tendsto_mcont_llist mcont_lfilter)


subsection {* Define @{term lconcat} as continuous extension*}

definition "lconcat' xs = Lim (at' xs) (\<lambda>xs. foldr lappend (list_of xs) LNil)"

lemma tendsto_lconcat': "(lconcat' \<longlongrightarrow> lconcat' xss) (at' xss)"
  apply (rule tendsto_Lim_at'[OF lconcat'_def])
  apply (auto simp add: lfinite_eq_range_llist_of less_eq_list_def prefix_def)
  apply (induct_tac xa)
  apply simp_all
  done

lemma isCont_lconcat'[THEN isCont_o2[rotated]]: "isCont lconcat' l"
  by (simp add: isCont_def filterlim_at'_list tendsto_lconcat')

lemma lconcat'_lfinite[simp]: "lfinite xs \<Longrightarrow> lconcat' xs = foldr lappend (list_of xs) LNil"
  by (simp add: lconcat'_def Lim_at'_lfinite)

lemma lconcat'_LNil: "lconcat' LNil = LNil"
  by simp

lemma lconcat'_LCons [simp]: "lconcat' (LCons l xs) = lappend l (lconcat' xs)"
  by (rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont])
     (auto intro!: isCont_lconcat' isCont_lappend isCont_LCons)

lemma lmap_lconcat: "lmap f (lconcat' xss) = lconcat' (lmap (lmap f) (xss::'a llist llist))"
proof (rule tendsto_closed[where x=xss, OF closed_Collect_eq_isCont])
  fix xs :: "'a llist llist"
  assume "lfinite xs"
  then show "lmap f (lconcat' xs) = lconcat' (lmap (lmap f) xs)"
    by (induct xs rule: lfinite.induct) (auto simp: lmap_lappend_distrib)
qed (intro isCont_lconcat' isCont_lappend isCont_LCons continuous_ident isCont_lmap)+

lemmas tendsto_Sup[THEN tendsto_compose, tendsto_intros] =
  mcont_SUP[OF mcont_id' mcont_const, THEN tendsto_mcont]

lemma
  assumes fin: "\<forall>xs\<in>lset xss. lfinite xs"
  shows "lset (lconcat' xss) = (\<Union>xs\<in>lset xss. lset xs)" (is "?lhs = ?rhs")
proof(rule tendsto_unique_eventually[OF at'_bot])
  show "eventually (\<lambda>x. lset (lconcat' x) = (\<Union>y\<in>lset x. lset y)) (at' xss)"
  proof(rule eventually_at'_llistI)
    fix xss'
    assume "lfinite xss'" "xss' \<le> xss"
    hence "\<forall>xs\<in>lset xss'. lfinite xs" using fin by (auto dest!: lprefix_lsetD)
    with `lfinite xss'` show "lset (lconcat' xss') = (\<Union>xs\<in>lset xss'. lset xs)"
      by (induct xss') auto
  qed
qed (rule tendsto_intros tendsto_lconcat' tendsto_id_at')+

subsection {* Define @{term ldropWhile} as continuous extension *}

definition "ldropWhile' P xs = Lim (at' xs) (\<lambda>xs. llist_of (dropWhile P (list_of xs)))"

lemma tendsto_ldropWhile':
  "(ldropWhile' P \<longlongrightarrow> ldropWhile' P xs) (at' xs)"
  by (rule tendsto_Lim_at'[OF ldropWhile'_def])
     (auto simp add: lfinite_eq_range_llist_of less_eq_list_def prefix_def dropWhile_append dropWhile_False)

lemma isCont_ldropWhile'[THEN isCont_o2[rotated]]: "isCont (ldropWhile' P) l"
  by (simp add: isCont_def filterlim_at'_list tendsto_ldropWhile')

lemma ldropWhile'_lfinite[simp]: "lfinite xs \<Longrightarrow> ldropWhile' P xs = llist_of (dropWhile P (list_of xs))"
  by (simp add: ldropWhile'_def Lim_at'_lfinite)

lemma ldropWhile'_LNil: "ldropWhile' P LNil = LNil"
  by simp

lemma ldropWhile'_LCons [simp]: "ldropWhile' P (LCons l xs) = (if P l then ldropWhile' P xs else LCons l xs)"
  by (rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont])
     (auto intro!: isCont_ldropWhile' isCont_If isCont_LCons)

lemma "ldropWhile' P (lmap f xs) = lmap f (ldropWhile' (P \<circ> f) xs)"
  by (rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont])
     (auto simp add: dropWhile_map comp_def intro!: isCont_lmap isCont_ldropWhile')

lemma ldropWhile'_LNil_I[simp]: "\<forall>x \<in> lset xs. P x \<Longrightarrow> ldropWhile' P xs = LNil"
  by (rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont])
     (auto simp add: llist_of_eq_LNil_conv intro!: isCont_lmap isCont_ldropWhile' dest!: lprefix_lsetD)

lemma lnull_ldropWhile': "lnull (ldropWhile' P xs) \<longleftrightarrow> (\<forall>x \<in> lset xs. P x)" (is "?lhs \<longleftrightarrow> _")
proof (intro iffI ballI)
  fix x assume "x \<in> lset xs" ?lhs then show "P x" by induct (simp_all split: if_split_asm)
qed simp

lemma lhd_lfilter': "lhd (lfilter' P xs) = lhd (ldropWhile' (Not \<circ> P) xs)"
proof cases
  assume "\<exists>x\<in>lset xs. P x"
  then obtain x where "x \<in> lset xs" and "P x" by blast
  from `x \<in> lset xs` show ?thesis by induct (simp_all add: `P x`)
qed simp


subsection {* Define @{text ldrop} as continuous extension *}

primrec edrop where
  "edrop n [] = []"
| "edrop n (x # xs) = (case n of eSuc n \<Rightarrow> edrop n xs | 0 \<Rightarrow> x # xs)"

lemma mono_edrop: "edrop n xs \<le> edrop n (xs @ ys)"
  by (induct xs arbitrary: n) (auto split: enat_cosplit)

lemma edrop_mono: "xs \<le> ys \<Longrightarrow> edrop n xs \<le> edrop n ys"
  using mono_edrop[of n xs] by (auto simp add: less_eq_list_def prefix_def)

definition "ldrop' n xs = Lim (at' xs) (llist_of \<circ> edrop n \<circ> list_of)"

lemma ldrop'_lfinite[simp]: "lfinite xs \<Longrightarrow> ldrop' n xs = llist_of (edrop n (list_of xs))"
  by (simp add: ldrop'_def Lim_at'_lfinite)

lemma tendsto_ldrop': "(ldrop' n \<longlongrightarrow> ldrop' n l) (at' l)"
  by (rule tendsto_Lim_at'[OF ldrop'_def]) (auto simp add: lfinite_eq_range_llist_of intro!: edrop_mono)

lemma isCont_ldrop'[THEN isCont_o2[rotated]]: "isCont (ldrop' n) l"
  by (simp add: isCont_def filterlim_at'_list tendsto_ldrop')

lemma "ldrop' n LNil = LNil"
  by simp

lemma "ldrop' n (LCons x xs) = (case n of 0 \<Rightarrow> LCons x xs | eSuc n \<Rightarrow> ldrop' n xs)"
  by (rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont])
     (auto intro!: isCont_ldrop' isCont_enat_case isCont_LCons split: enat_cosplit)

primrec up :: "'a :: order \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "up a [] = []"
| "up a (x # xs) = (if a < x then x # up x xs else up a xs)"

lemma set_upD: "x \<in> set (up y xs) \<Longrightarrow> x \<in> set xs \<and> y < x"
  by (induct xs arbitrary: y) (auto split: if_split_asm intro: less_trans)

lemma prefix_up: "prefix (up a xs) (up a (xs @  ys))"
  by (induction xs arbitrary: a) auto

lemma mono_up: "xs \<le> ys \<Longrightarrow> up a xs \<le> up a ys"
  unfolding less_eq_list_def by (subst (asm) prefix_def) (auto intro!: prefix_up)

lemma sorted_up: "sorted (up a xs)"
  by (induction xs arbitrary: a) (auto dest: set_upD intro: less_imp_le)


subsection {* Define more functions on lazy lists as continuous extensions *}

definition "lup a xs = Lim (at' xs) (\<lambda>xs. llist_of (up a (list_of xs)))"

lemma tendsto_lup: "(lup a \<longlongrightarrow> lup a xs) (at' xs)"
  by (rule tendsto_Lim_at'[OF lup_def]) (auto simp: lfinite_eq_range_llist_of mono_up)

lemma isCont_lup[THEN isCont_o2[rotated]]: "isCont (lup a) l"
  by (simp add: isCont_def filterlim_at'_list tendsto_lup)

lemma lup_lfinite[simp]: "lfinite xs \<Longrightarrow> lup a xs = llist_of (up a (list_of xs))"
  by (simp add: lup_def Lim_at'_lfinite)

lemma lup_LNil: "lup a LNil = LNil"
  by simp

lemma lup_LCons [simp]: "lup a (LCons x xs) = (if a < x then LCons x (lup x xs) else lup a xs)"
  by (rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont])
     (auto intro!: isCont_lup isCont_If isCont_LCons)

lemma lset_lup: "lset (lup x xs) \<subseteq> lset xs \<inter> {y. x < y}"
  by (rule tendsto_le_ccpo[where g="\<lambda>xs. lset (lup x xs)" and f="\<lambda>xs. lset xs \<inter> {y. x < y}" and F="at' xs"])
     (auto dest!: lprefix_lsetD set_upD intro!:  tendsto_intros at'_bot tendsto_lup eventually_at'_llistI)

lemma lsorted_lup: "lsorted (lup (a::'a::linorder) l)"
  by (rule tendsto_closed[OF closed_lsorted', OF isCont_lup])
     (auto intro!: sorted_up simp: lprefix_conv_lappend)

context notes [[function_internals]]
begin

partial_function (llist) lup' :: "'a :: ord \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
  "lup' a xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> if a < x then LCons x (lup' x xs) else lup' a xs)"

end

declare lup'.mono[cont_intro]

lemma monotone_lup': "monotone (rel_prod (=) lprefix) lprefix (\<lambda>(a, xs). lup' a xs)"
by(rule llist.fixp_preserves_mono2[OF lup'.mono lup'_def]) simp

lemma mono2mono_lup'2[THEN llist.mono2mono, simp, cont_intro]:
  shows monotone_lup'2: "monotone lprefix lprefix (lup' a)"
using monotone_lup' by auto

lemma mcont_lup': "mcont (prod_lub the_Sup lSup) (rel_prod (=) lprefix) lSup lprefix (\<lambda>(a, xs). lup' a xs)"
by(rule llist.fixp_preserves_mcont2[OF lup'.mono lup'_def]) simp

lemma mcont2mcont_lup'2[THEN llist.mcont2mcont, simp, cont_intro]:
  shows mcont_lup'2: "mcont lSup lprefix lSup lprefix (lup' a)"
using mcont_lup' by auto

simps_of_case lup'_simps [simp]: lup'.simps

lemma lset_lup'_subset:
  fixes x :: "_ :: preorder"
  shows "lset (lup' x xs) \<subseteq> lset xs \<inter> {y. x < y}"
by(induction xs arbitrary: x)(auto intro: less_trans)

lemma in_lset_lup'D:
  fixes x :: "_ :: preorder"
  assumes "y \<in> lset (lup' x xs)"
  shows "y \<in> lset xs \<and> x < y"
using lset_lup'_subset[of x xs] assms by auto

lemma lsorted_lup':
  fixes x :: "_ :: preorder"
  shows "lsorted (lup' x xs)"
by(induction xs arbitrary: x)(auto simp add: lsorted_LCons dest: in_lset_lup'D intro: less_imp_le)

lemma ldistinct_lup':
  fixes x :: "_ :: preorder"
  shows "ldistinct (lup' x xs)"
by(induction xs arbitrary: x)(auto dest: in_lset_lup'D)

context fixes f :: "'a \<Rightarrow> 'a" begin

partial_function (llist) iterate :: "'a \<Rightarrow> 'a llist"
where "iterate x = LCons x (iterate (f x))"

lemma lmap_iterate: "lmap f (iterate x) = iterate (f x)"
by(induction arbitrary: x rule: iterate.fixp_induct) simp_all

end

fun extup extdown  :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "extup i [] = []"
| "extup i (x # xs) = (if i \<le> x then extup x xs else i # extdown x xs)"
| "extdown i [] = []"
| "extdown i (x # xs) = (if i \<ge> x then extdown x xs else i # extup x xs)"

lemma prefix_ext:
  "prefix (extup a xs) (extup a (xs @  ys))"
  "prefix (extdown a xs) (extdown a (xs @  ys))"
  by (induction xs arbitrary: a) auto

lemma mono_ext: assumes "xs \<le> ys" shows "extup a xs \<le> extup a ys" "extdown a xs \<le> extdown a ys"
  using assms[unfolded less_eq_list_def prefix_def] by (auto simp: less_eq_list_def prefix_ext)

lemma set_ext: "set (extup a xs) \<subseteq> {a} \<union> set xs" "set (extdown a xs) \<subseteq> {a} \<union> set xs"
  by (induction xs arbitrary: a) auto

definition "lextup i l = Lim (at' l) (llist_of \<circ> extup i \<circ> list_of)"
definition "lextdown i l = Lim (at' l) (llist_of \<circ> extdown i \<circ> list_of)"

lemma tendsto_lextup[tendsto_intros]: "(lextup i \<longlongrightarrow> lextup i xs) (at' xs)"
  by (rule tendsto_Lim_at'[OF lextup_def]) (auto simp: lfinite_eq_range_llist_of mono_ext)

lemma tendsto_lextdown[tendsto_intros]: "(lextdown i \<longlongrightarrow> lextdown i xs) (at' xs)"
  by (rule tendsto_Lim_at'[OF lextdown_def]) (auto simp: lfinite_eq_range_llist_of mono_ext)

lemma isCont_lextup[THEN isCont_o2[rotated]]: "isCont (lextup a) l"
  by (simp add: isCont_def filterlim_at'_list tendsto_lextup)

lemma isCont_lextdown[THEN isCont_o2[rotated]]: "isCont (lextdown a) l"
  by (simp add: isCont_def filterlim_at'_list tendsto_lextdown)

lemma lextup_lfinite[simp]: "lfinite xs \<Longrightarrow> lextup i xs = llist_of (extup i (list_of xs))"
  by (simp add: lextup_def Lim_at'_lfinite)

lemma lextdown_lfinite[simp]: "lfinite xs \<Longrightarrow> lextdown i xs = llist_of (extdown i (list_of xs))"
  by (simp add: lextdown_def Lim_at'_lfinite)

lemma "lextup i LNil = LNil" "lextdown i LNil = LNil"
  by simp_all

lemma "lextup i (LCons x xs) = (if i \<le> x then lextup x xs else LCons i (lextdown x xs))"
  by (rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont])
     (auto intro!: isCont_lextdown isCont_lextup isCont_If isCont_LCons)

lemma "lextdown i (LCons x xs) = (if x \<le> i then lextdown x xs else LCons i (lextup x xs))"
  by (rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont])
     (auto intro!: isCont_lextdown isCont_lextup isCont_If isCont_LCons)

lemma "lset (lextup a xs) \<subseteq> {a} \<union> lset xs"
  apply (rule tendsto_le_ccpo[where g="\<lambda>xs. lset (lextup a xs)" and f="\<lambda>xs. {a} \<union> lset xs" and F="at' xs"])
  apply (rule tendsto_intros at'_bot tendsto_lup eventually_at'_llistI tendsto_id_at')+
  apply (auto dest!: lprefix_lsetD set_ext[THEN set_mp])
  done

lemma "lset (lextdown a xs) \<subseteq> {a} \<union> lset xs"
  apply (rule tendsto_le_ccpo[where g="\<lambda>xs. lset (lextdown a xs)" and f="\<lambda>xs. {a} \<union> lset xs" and F="at' xs"])
  apply (rule tendsto_intros at'_bot tendsto_lup eventually_at'_llistI tendsto_id_at')+
  apply (auto dest!: lprefix_lsetD set_ext[THEN set_mp])
  done

lemma distinct_ext:
  assumes "distinct xs" "a \<notin> set xs"
  shows "distinct (extup a xs)" "distinct (extdown a xs)"
  using assms set_ext
  apply (induction xs arbitrary: a)
  apply auto
  apply (metis eq_iff insert_iff subset_iff)+
  done

lemma "ldistinct xs \<Longrightarrow> a \<notin> lset xs \<Longrightarrow> ldistinct (lextup a xs)"
  by (rule_tac tendsto_closed[OF closed_ldistinct', OF isCont_lextup])
     (force simp: lfinite_eq_range_llist_of intro!: distinct_ext dest: ldistinct_lprefix dest: lprefix_lsetD)+

definition esum_list :: "ereal llist \<Rightarrow> ereal" where
  "esum_list xs = Lim (at' xs) (sum_list \<circ> list_of)"

lemma esum_list_lfinite[simp]: "lfinite xs \<Longrightarrow> esum_list xs = sum_list (list_of xs)"
  by (simp add: esum_list_def Lim_at'_lfinite)

lemma esum_list_LNil: "esum_list LNil = 0"
  by simp

context
  fixes xs :: "ereal llist"
  assumes xs: "\<And>x. x \<in> lset xs \<Longrightarrow> 0 \<le> x"
begin

lemma esum_list_tendsto_SUP:
  "((sum_list\<circ>list_of) \<longlongrightarrow> (SUP ys : {ys. lfinite ys \<and> ys \<le> xs}. esum_list ys)) (at' xs)"
    (is "(_ \<longlongrightarrow> ?y) _")
proof (rule order_tendstoI)
  fix a assume "a < ?y"
  then obtain ys where "llist_of ys \<le> xs" "a < sum_list ys"
    by (auto simp: less_SUP_iff lfinite_eq_range_llist_of)
  moreover
  { fix zs assume "ys \<le> zs" "llist_of zs \<le> xs"
    then obtain ys' where zs: "zs = ys @ ys'"
      by (auto simp: prefix_def less_eq_list_def)
    with `llist_of zs \<le> xs` have nonneg: "0 \<le> sum_list ys'"
      using xs by (auto simp: lprefix_conv_lappend sum_list_sum_nth intro: sum_nonneg)
    note `a < sum_list ys`
    also have "sum_list ys \<le> sum_list zs"
      using zs ereal_add_mono[OF order_refl nonneg] by auto
    finally have "a < sum_list zs" . }
  ultimately show "eventually (\<lambda>x. a < (sum_list\<circ>list_of) x) (at' xs)"
    unfolding eventually_at'_llist by (auto simp: lfinite_eq_range_llist_of)
next
  fix a assume "?y < a" then show "eventually (\<lambda>x. (sum_list\<circ>list_of) x < a) (at' xs)"
    by (auto intro!: eventually_at'_llistI dest: SUP_lessD)
qed

lemma tendsto_esum_list: "(esum_list \<longlongrightarrow> esum_list xs) (at' xs)"
  apply (rule filterlim_cong[where g="sum_list \<circ> list_of", THEN iffD2, OF refl refl])
  apply (rule eventually_mono[OF eventually_lfinite])
  apply simp
  unfolding esum_list_def
  apply (rule tendsto_LimI)
  apply (rule esum_list_tendsto_SUP)
  done

lemma isCont_esum_list: "isCont esum_list xs"
  by (simp add: isCont_def filterlim_at'_list tendsto_esum_list)

end

lemma esum_list_nonneg:
  "(\<And>x. x \<in> lset xs \<Longrightarrow> 0 \<le> x) \<Longrightarrow> 0 \<le> esum_list xs"
  by (rule tendsto_le[OF at'_bot tendsto_esum_list tendsto_const])
     (auto intro!: eventually_at'_llistI sum_nonneg
           simp: lprefix_conv_lappend sum_list_sum_nth lfinite_eq_range_llist_of)

lemma esum_list_LCons:
  assumes x: "0 \<le> x" "\<And>x. x \<in> lset xs \<Longrightarrow> 0 \<le> x" shows "esum_list (LCons x xs) = x + esum_list xs"
proof (rule tendsto_unique_eventually[OF at'_bot])
  from x show "((\<lambda>xs. esum_list (LCons x xs)) \<longlongrightarrow> esum_list (LCons x xs)) (at' xs)"
    by (intro tendsto_compose[OF filterlim_at'_list[OF tendsto_esum_list] tendsto_LCons]) auto
  show "eventually (\<lambda>xa. esum_list (LCons x xa) = x + esum_list xa) (at' xs)"
    using eventually_lfinite by eventually_elim simp
  from x show "((\<lambda>xa. x + esum_list xa) \<longlongrightarrow> x + esum_list xs) (at' xs)"
    by (intro esum_list_nonneg tendsto_esum_list tendsto_add_ereal) auto
qed

lemma esum_list_lfilter':
  assumes nn: "\<And>x. x \<in> lset xs \<Longrightarrow> 0 \<le> x" shows "esum_list (lfilter' (\<lambda>x. x \<noteq> 0) xs) = esum_list xs"
proof (rule tendsto_unique_eventually[OF at'_bot])
  show "(esum_list \<longlongrightarrow> esum_list xs) (at' xs)"
    using nn by (rule tendsto_esum_list)
  from nn show "((\<lambda>xs. esum_list (lfilter' (\<lambda>x. x \<noteq> 0) xs)) \<longlongrightarrow> esum_list (lfilter' (\<lambda>x. x \<noteq> 0) xs)) (at' xs)"
    by (intro tendsto_compose[OF filterlim_at'_list[OF tendsto_esum_list] tendsto_lfilter]) (auto simp: lset_lfilter')
  show "eventually (\<lambda>xs. esum_list (lfilter' (\<lambda>x. x \<noteq> 0) xs) = esum_list xs) (at' xs)"
    using eventually_lfinite
    by eventually_elim (simp add: sum_list_map_filter[where f = "\<lambda>x. x" and P="\<lambda>x. x \<noteq> 0", simplified])
qed

function f:: "nat list \<Rightarrow> nat list" where
  "f [] = []"
| "f (x#xs) = (x * 2) # f (f xs)"
  by auto pat_completeness

termination f
proof (relation "inv_image natLess length")
  fix x xs assume "f_dom xs" then show "(f xs, x # xs) \<in> inv_image natLess length"
    by induct (auto simp: f.psimps natLess_def)
qed (auto intro: wf_less simp add: natLess_def)

lemma length_f[simp]: "length (f xs) = length xs"
  by (induct rule: f.induct) simp_all

lemma f_mono': "\<exists>ys'. f (xs @ ys) = f xs @ ys'"
proof (induct "length xs" arbitrary: xs ys rule: less_induct)
  case less then show ?case
    apply (cases xs)
    apply auto
    apply (metis length_f lessI)
    done
qed

lemma f_mono: "xs \<le> ys \<Longrightarrow> f xs \<le> f ys"
  by (auto simp: less_eq_list_def prefix_def f_mono')

definition "f' l = Lim (at' l) (\<lambda>l. llist_of (f (list_of l)))"

lemma f'_lfinite[simp]: "lfinite xs \<Longrightarrow> f' xs = llist_of (f (list_of xs))"
  by (simp add: f'_def Lim_at'_lfinite)

lemma tendsto_f': "(f' \<longlongrightarrow> f' l) (at' l)"
  by (rule tendsto_Lim_at'[OF f'_def]) (auto simp add: lfinite_eq_range_llist_of intro!: f_mono)

lemma isCont_f'[THEN isCont_o2[rotated]]: "isCont f' l"
  by (simp add: isCont_def filterlim_at'_list tendsto_f')

lemma "f' LNil = LNil"
  by simp

lemma "f' (LCons x xs) = LCons (x * 2) (f' (f' xs))"
  by (rule tendsto_closed[where x=xs, OF closed_Collect_eq_isCont])
     (auto intro!: isCont_f' isCont_LCons)

end
