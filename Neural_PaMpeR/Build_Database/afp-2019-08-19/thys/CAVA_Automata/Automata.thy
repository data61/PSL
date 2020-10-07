section \<open>Automata\<close>
(* Author: Peter Lammich *)
theory Automata
imports Digraph
begin
  text \<open>
    In this theory, we define Generalized Buchi Automata and Buchi Automata 
    based on directed graphs
\<close>

hide_const (open) prod
  
subsection "Generalized Buchi Graphs"
text \<open>
  A generalized Buchi graph is a graph where each node belongs to a set of
  acceptance classes. An infinite run on this graph is accepted, iff
  it visits nodes from each acceptance class infinitely often.

  The standard encoding of acceptance classes is as a set of sets of nodes,
  each inner set representing one acceptance class.
\<close>

record 'Q gb_graph_rec = "'Q graph_rec" +
  gbg_F :: "'Q set set"


locale gb_graph =
  graph G 
  for G :: "('Q,'more) gb_graph_rec_scheme" +
  assumes finite_F[simp, intro!]: "finite (gbg_F G)"
  assumes F_ss: "gbg_F G \<subseteq> Pow V"
begin
  abbreviation "F \<equiv> gbg_F G"

  lemma is_gb_graph: "gb_graph G" by unfold_locales


  definition 
    is_acc :: "'Q word \<Rightarrow> bool" where "is_acc r \<equiv> (\<forall>A\<in>F. \<exists>\<^sub>\<infinity>i. r i \<in> A)"

  definition "is_acc_run r \<equiv> is_run r \<and> is_acc r"

  (* For presentation in paper *)
  lemma "is_acc_run r \<equiv> is_run r \<and> (\<forall>A\<in>F. \<exists>\<^sub>\<infinity>i. r i \<in> A)"
    unfolding is_acc_run_def is_acc_def .

  lemma acc_run_run: "is_acc_run r \<Longrightarrow> is_run r"
    unfolding is_acc_run_def by simp

  lemmas acc_run_reachable = run_reachable[OF acc_run_run]


  lemma acc_eq_limit: 
    assumes FIN: "finite (range r)"  
    shows "is_acc r \<longleftrightarrow> (\<forall>A\<in>F. limit r \<inter> A \<noteq> {})"
  proof 
    assume "\<forall>A\<in>F. limit r \<inter> A \<noteq> {}"
    thus "is_acc r"
      unfolding is_acc_def
      by (metis limit_inter_INF)
  next
    from FIN have FIN': "\<And>A. finite (A \<inter> range r)"
      by simp

    assume "is_acc r"
    hence AUX: "\<forall>A\<in>F. \<exists>\<^sub>\<infinity>i. r i \<in> (A \<inter> range r)"
      unfolding is_acc_def by auto
    have "\<forall>A\<in>F. limit r \<inter> (A \<inter> range r) \<noteq> {}"
      apply (rule ballI)
      apply (drule bspec[OF AUX])
      apply (subst (asm) fin_ex_inf_eq_limit[OF FIN'])
      .
    thus "\<forall>A\<in>F. limit r \<inter> A \<noteq> {}" 
      by auto
  qed

  lemma is_acc_run_limit_alt:
    assumes "finite (E\<^sup>* `` V0)"
    shows "is_acc_run r \<longleftrightarrow> is_run r \<and> (\<forall>A\<in>F. limit r \<inter> A \<noteq> {})"
    using assms acc_eq_limit[symmetric] unfolding is_acc_run_def
    by (auto dest: run_reachable finite_subset)

  lemma is_acc_suffix[simp]: "is_acc (suffix i r) \<longleftrightarrow> is_acc r"
    unfolding is_acc_def suffix_def
    apply (clarsimp simp: INFM_nat)
    apply (rule iffI)
    apply (metis trans_less_add2)
    by (metis add_lessD1 less_imp_add_positive nat_add_left_cancel_less)

  lemma finite_V_Fe:
    assumes "finite V" "A \<in> F"
    shows "finite A"
    using assms by (metis Pow_iff infinite_super rev_subsetD F_ss)

end


definition "gb_rename_ecnv ecnv f G \<equiv> \<lparr>
  gbg_F = { f`A | A. A\<in>gbg_F G }, \<dots> = ecnv G
\<rparr>"


abbreviation "gb_rename_ext ecnv f \<equiv> fr_rename_ext (gb_rename_ecnv ecnv f) f"


locale gb_rename_precond =
  gb_graph G +
  g_rename_precond G f "gb_rename_ecnv ecnv f"
  for G :: "('u,'more) gb_graph_rec_scheme"
  and f :: "'u \<Rightarrow> 'v" and ecnv
begin
  lemma G'_gb_fields: "gbg_F G' = { f`A | A. A\<in>F }"
    unfolding gb_rename_ecnv_def fr_rename_ext_def
    by simp

  sublocale G': gb_graph G' 
    apply unfold_locales
    apply (simp_all add: G'_fields G'_gb_fields)
    using F_ss 
    by auto

  lemma acc_sim1: "is_acc r \<Longrightarrow> G'.is_acc (f o r)"
    unfolding is_acc_def G'.is_acc_def G'_gb_fields
    by (fastforce intro: imageI simp: INFM_nat)

  lemma acc_sim2: 
    assumes "G'.is_acc r" shows "is_acc (fi o r)"
  proof -
    from assms have 1: "\<And>A m. A \<in> gbg_F G \<Longrightarrow> \<exists>i>m. r i \<in> f`A"
      unfolding G'.is_acc_def G'_gb_fields
      by (auto simp: INFM_nat)

    { fix A m 
      assume 2: "A \<in> gbg_F G"  
      from 1[OF this, of m] have "\<exists>i>m. fi (r i) \<in> A"
        using F_ss
        apply clarsimp
        by (metis Pow_iff 2 fi_f in_mono)
    } thus ?thesis
      unfolding is_acc_def
      by (auto simp: INFM_nat)
  qed

  lemma acc_run_sim1: "is_acc_run r \<Longrightarrow> G'.is_acc_run (f o r)"
    using acc_sim1 run_sim1 unfolding G'.is_acc_run_def is_acc_run_def
    by auto

  lemma acc_run_sim2: "G'.is_acc_run r \<Longrightarrow> is_acc_run (fi o r)"
    using acc_sim2 run_sim2 unfolding G'.is_acc_run_def is_acc_run_def
    by auto

end

subsection "Generalized Buchi Automata"
text \<open>
  A GBA is obtained from a GBG by adding a labeling function, that associates
  each state with a set of labels. A word is accepted if there is an
  accepting run that can be labeld with this word.
\<close>

record ('Q,'L) gba_rec = "'Q gb_graph_rec" +
  gba_L :: "'Q \<Rightarrow> 'L \<Rightarrow> bool"

locale gba =
  gb_graph G
  for G :: "('Q,'L,'more) gba_rec_scheme" +
  assumes L_ss: "gba_L G q l \<Longrightarrow> q \<in> V"
begin
  abbreviation "L \<equiv> gba_L G"

  lemma is_gba: "gba G" by unfold_locales

  definition "accept w \<equiv> \<exists>r. is_acc_run r \<and> (\<forall>i. L (r i) (w i))"
  lemma acceptI[intro?]: "\<lbrakk>is_acc_run r; \<And>i. L (r i) (w i)\<rbrakk> \<Longrightarrow> accept w"
    by (auto simp: accept_def)

  definition "lang \<equiv> Collect (accept)"
  lemma langI[intro?]: "accept w \<Longrightarrow> w\<in>lang" by (auto simp: lang_def)
end

definition "gba_rename_ecnv ecnv f G \<equiv> \<lparr>
  gba_L = \<lambda>q l. 
    if q\<in>f`g_V G then 
      gba_L G (the_inv_into (g_V G) f q) l
    else
      False, 
  \<dots> = ecnv G
\<rparr>"

abbreviation "gba_rename_ext ecnv f \<equiv> gb_rename_ext (gba_rename_ecnv ecnv f) f"

locale gba_rename_precond =  
  gb_rename_precond G f "gba_rename_ecnv ecnv f" + gba G
  for G :: "('u,'L,'more) gba_rec_scheme"
  and f :: "'u \<Rightarrow> 'v" and ecnv
begin
  lemma G'_gba_fields: "gba_L G' = (\<lambda>q l. 
    if q\<in>f`V then L (fi q) l else False)"
    unfolding gb_rename_ecnv_def gba_rename_ecnv_def fr_rename_ext_def fi_def
    by simp

  sublocale G': gba G'
    apply unfold_locales
    apply (auto simp add: G'_gba_fields G'_fields split: if_split_asm)
    done

  lemma L_sim1: "\<lbrakk>range r \<subseteq> V; L (r i) l\<rbrakk> \<Longrightarrow> G'.L (f (r i)) l"
    by (auto simp: G'_gba_fields fi_def[symmetric] fi_f 
      dest: inj_onD[OF INJ]
      dest!: rev_subsetD[OF rangeI[of _ i]])

  lemma L_sim2: "\<lbrakk> range r \<subseteq> f`V; G'.L (r i) l \<rbrakk> \<Longrightarrow> L (fi (r i)) l"
    by (auto
      simp: G'_gba_fields fi_def[symmetric] f_fi
      dest!: rev_subsetD[OF rangeI[of _ i]])
    
  lemma accept_eq[simp]: "G'.accept = accept"
    apply (rule ext)
    unfolding accept_def G'.accept_def
  proof safe
    fix w r
    assume R: "G'.is_acc_run r"
    assume L: "\<forall>i. G'.L (r i) (w i)"
    from R have RAN: "range r \<subseteq> f`V"
      using G'.run_reachable[OF G'.acc_run_run[OF R]] G'.reachable_V
      unfolding G'_fields
      by simp
    from L show "\<exists>r. is_acc_run r \<and> (\<forall>i. L (r i) (w i))"
      using acc_run_sim2[OF R] L_sim2[OF RAN]
      by auto
  next
    fix w r
    assume R: "is_acc_run r" 
    assume L: "\<forall>i. L (r i) (w i)"
    
    from R have RAN: "range r \<subseteq> V"
      using run_reachable[OF acc_run_run[OF R]] reachable_V by simp
      
    from L show "\<exists>r. 
        G'.is_acc_run r 
      \<and> (\<forall>i. G'.L (r i) (w i))"
      using acc_run_sim1[OF R] L_sim1[OF RAN]
      by auto
  qed

  lemma lang_eq[simp]: "G'.lang = lang"
    unfolding G'.lang_def lang_def by simp

  lemma finite_G'_V:
    assumes "finite V"
    shows "finite G'.V"
    using assms by (auto simp add: G'_gba_fields G'_fields split: if_split_asm)

end


abbreviation "gba_rename \<equiv> gba_rename_ext (\<lambda>_. ())"

lemma gba_rename_correct:
  fixes G :: "('v,'l,'m) gba_rec_scheme"
  assumes "gba G" 
  assumes INJ: "inj_on f (g_V G)" 
  defines "G' \<equiv> gba_rename f G"
  shows "gba G'"
  and "finite (g_V G) \<Longrightarrow> finite (g_V G')"
  and "gba.accept G' = gba.accept G"
  and "gba.lang G' = gba.lang G"
  unfolding G'_def
proof -
  let ?G' = "gba_rename f G"
  interpret gba G by fact
  
  from INJ interpret gba_rename_precond G f "\<lambda>_. ()"
    by unfold_locales simp_all

  show "gba ?G'" by (rule G'.is_gba)
  show "finite (g_V G) \<Longrightarrow> finite (g_V ?G')" by (fact finite_G'_V)
  show "G'.accept = accept" by simp
  show "G'.lang = lang" by simp
qed

subsection "Buchi Graphs"

text \<open>A Buchi graph has exactly one acceptance class\<close>

record 'Q b_graph_rec = "'Q graph_rec" +
  bg_F :: "'Q set"

locale b_graph =
  graph G 
  for G :: "('Q,'more) b_graph_rec_scheme"
  +
  assumes F_ss: "bg_F G \<subseteq> V"
begin
  abbreviation F where "F \<equiv> bg_F G"

  lemma is_b_graph: "b_graph G" by unfold_locales

  definition "to_gbg_ext m 
    \<equiv> \<lparr> g_V = V, 
        g_E=E, 
        g_V0=V0, 
        gbg_F = if F=UNIV then {} else {F}, 
        \<dots> = m \<rparr>"
  abbreviation "to_gbg \<equiv> to_gbg_ext ()"

  sublocale gbg: gb_graph "to_gbg_ext m"
    apply unfold_locales 
    using V0_ss E_ss F_ss
    apply (auto simp: to_gbg_ext_def split: if_split_asm)
    done

  definition is_acc :: "'Q word \<Rightarrow> bool" where "is_acc r \<equiv> (\<exists>\<^sub>\<infinity>i. r i \<in> F)"
  definition is_acc_run where "is_acc_run r \<equiv> is_run r \<and> is_acc r"

  lemma to_gbg_alt:
    "gbg.V T m = V"
    "gbg.E T m = E"
    "gbg.V0 T m = V0"
    "gbg.F T m = (if F=UNIV then {} else {F})"
    "gbg.is_run T m = is_run"
    "gbg.is_acc T m = is_acc"
    "gbg.is_acc_run T m = is_acc_run"
    unfolding is_run_def[abs_def] gbg.is_run_def[abs_def]
      is_acc_def[abs_def] gbg.is_acc_def[abs_def]
      is_acc_run_def[abs_def] gbg.is_acc_run_def[abs_def]
    by (auto simp: to_gbg_ext_def)

end

subsection "Buchi Automata"
text \<open>Buchi automata are labeled Buchi graphs\<close>

record ('Q,'L) ba_rec = "'Q b_graph_rec" +
  ba_L :: "'Q \<Rightarrow> 'L \<Rightarrow> bool"

locale ba =
  bg?: b_graph G 
  for G :: "('Q,'L,'more) ba_rec_scheme"
  +
  assumes L_ss: "ba_L G q l \<Longrightarrow> q \<in> V"
begin
  abbreviation L where "L == ba_L G"

  lemma is_ba: "ba G" by unfold_locales


  abbreviation "to_gba_ext m \<equiv> to_gbg_ext \<lparr> gba_L = L, \<dots>=m \<rparr>"
  abbreviation "to_gba \<equiv> to_gba_ext ()"

  sublocale gba: gba "to_gba_ext m" 
    apply unfold_locales
    unfolding to_gbg_ext_def
    using L_ss apply auto []
    done

  lemma ba_acc_simps[simp]: "gba.L T m = L"
    by (simp add: to_gbg_ext_def)

  definition "accept w \<equiv> (\<exists>r. is_acc_run r \<and> (\<forall>i. L (r i) (w i)))"
  definition "lang \<equiv> Collect accept"

  lemma to_gba_alt_accept: 
    "gba.accept T m = accept"
    apply (intro ext)
    unfolding accept_def gba.accept_def
    apply (simp_all add: to_gbg_alt)
    done

  lemma to_gba_alt_lang: 
    "gba.lang T m = lang"
    unfolding lang_def gba.lang_def
    apply (simp_all add: to_gba_alt_accept)
    done

  lemmas to_gba_alt = to_gbg_alt to_gba_alt_accept to_gba_alt_lang
end

subsection "Indexed acceptance classes"
record 'Q igb_graph_rec = "'Q graph_rec" +
  igbg_num_acc :: nat
  igbg_acc :: "'Q \<Rightarrow> nat set"

locale igb_graph = 
  graph G
  for G :: "('Q,'more) igb_graph_rec_scheme"
  +
  assumes acc_bound: "\<Union>(range (igbg_acc G)) \<subseteq> {0..<(igbg_num_acc G)}"
  assumes acc_ss: "igbg_acc G q \<noteq> {} \<Longrightarrow> q\<in>V"
begin
  abbreviation num_acc where "num_acc \<equiv> igbg_num_acc G"
  abbreviation acc where "acc \<equiv> igbg_acc G"

  lemma is_igb_graph: "igb_graph G" by unfold_locales


  lemma acc_boundI[simp, intro]: "x\<in>acc q \<Longrightarrow> x<num_acc"
    using acc_bound by fastforce

  definition "accn i \<equiv> {q . i\<in>acc q}"
  definition "F \<equiv> { accn i | i. i<num_acc }"

  definition "to_gbg_ext m 
    \<equiv> \<lparr> g_V = V, g_E = E, g_V0 = V0, gbg_F = F, \<dots>=m \<rparr>"

  sublocale gbg: gb_graph "to_gbg_ext m" 
    apply unfold_locales
    using V0_ss E_ss acc_ss
    apply (auto simp: to_gbg_ext_def F_def accn_def)
    done

  lemma to_gbg_alt1: 
    "gbg.E T m = E"
    "gbg.V0 T m = V0"
    "gbg.F T m = F" 
    by (simp_all add: to_gbg_ext_def)

  lemma F_fin[simp,intro!]: "finite F"
    unfolding F_def
    by auto

  definition is_acc :: "'Q word \<Rightarrow> bool" 
    where "is_acc r \<equiv> (\<forall>n<num_acc. \<exists>\<^sub>\<infinity>i. n \<in> acc (r i))"
  definition "is_acc_run r \<equiv> is_run r \<and> is_acc r"

  lemma is_run_gbg: 
    "gbg.is_run T m = is_run"
    unfolding is_run_def[abs_def] is_acc_run_def[abs_def] 
      gbg.is_run_def[abs_def] gbg.is_acc_run_def[abs_def] 
    by (simp_all add: to_gbg_ext_def)

  lemma is_acc_gbg: 
    "gbg.is_acc T m = is_acc"
    apply (intro ext)
    unfolding gbg.is_acc_def is_acc_def
    apply (simp add: to_gbg_alt1 is_run_gbg)
    unfolding F_def accn_def
    apply (blast intro: INFM_mono)
    done

  lemma is_acc_run_gbg: 
    "gbg.is_acc_run T m = is_acc_run"
    apply (intro ext)
    unfolding gbg.is_acc_run_def is_acc_run_def
    by (simp_all add: to_gbg_alt1 is_run_gbg is_acc_gbg)

  lemmas to_gbg_alt = to_gbg_alt1 is_run_gbg is_acc_gbg is_acc_run_gbg

  lemma acc_limit_alt: 
    assumes FIN: "finite (range r)"
    shows "is_acc r \<longleftrightarrow> (\<forall>n<num_acc. limit r \<inter> accn n \<noteq> {})"
  proof
    assume "\<forall>n<num_acc. limit r \<inter> accn n \<noteq> {}"
    thus "is_acc r"
      unfolding is_acc_def accn_def
      by (auto dest!: limit_inter_INF)
  next
    from FIN have FIN': "\<And>A. finite (A \<inter> range r)" by simp
    assume "is_acc r"
    hence "\<forall>n<num_acc. limit r \<inter> (accn n \<inter> range r) \<noteq> {}"
      unfolding is_acc_def accn_def
      by (auto simp: fin_ex_inf_eq_limit[OF FIN', symmetric])
    thus "\<forall>n<num_acc. limit r \<inter> accn n \<noteq> {}" by auto
  qed

  lemma acc_limit_alt': 
    "finite (range r) \<Longrightarrow> is_acc r \<longleftrightarrow> (\<Union>(acc ` limit r) = {0..<num_acc})"
    unfolding acc_limit_alt
    by (auto simp: accn_def)

end

record ('Q,'L) igba_rec = "'Q igb_graph_rec" +
  igba_L :: "'Q \<Rightarrow> 'L \<Rightarrow> bool"

locale igba =
  igbg?: igb_graph G
  for G :: "('Q,'L,'more) igba_rec_scheme"
  +
  assumes L_ss: "igba_L G q l \<Longrightarrow> q \<in> V"
begin
  abbreviation L where "L \<equiv> igba_L G"

  lemma is_igba: "igba G" by unfold_locales


  abbreviation "to_gba_ext m \<equiv> to_gbg_ext \<lparr> gba_L = igba_L G, \<dots>=m \<rparr>"

  sublocale gba: gba "to_gba_ext m" 
    apply unfold_locales
    unfolding to_gbg_ext_def
    using L_ss
    apply auto
    done
  
  lemma to_gba_alt_L:
    "gba.L T m = L"
    by (auto simp: to_gbg_ext_def)

  definition "accept w \<equiv> \<exists>r. is_acc_run r \<and> (\<forall>i. L (r i) (w i))"
  definition "lang \<equiv> Collect accept"

  lemma accept_gba_alt: "gba.accept T m = accept"
    apply (intro ext)
    unfolding accept_def gba.accept_def
    apply (simp add: to_gbg_alt to_gba_alt_L)
    done

  lemma lang_gba_alt: "gba.lang T m = lang"
    unfolding lang_def gba.lang_def
    apply (simp add: accept_gba_alt)
    done

  lemmas to_gba_alt = to_gbg_alt to_gba_alt_L accept_gba_alt lang_gba_alt

end

subsubsection \<open>Indexing Conversion\<close>
definition F_to_idx :: "'Q set set \<Rightarrow> (nat \<times> ('Q \<Rightarrow> nat set)) nres" where
  "F_to_idx F \<equiv> do {
    Flist \<leftarrow> SPEC (\<lambda>Flist. distinct Flist \<and> set Flist = F);
    let num_acc = length Flist;
    let acc = (\<lambda>v. {i . i<num_acc \<and> v\<in>Flist!i});
    RETURN (num_acc,acc)
  }"

lemma F_to_idx_correct:
  shows "F_to_idx F \<le> SPEC (\<lambda>(num_acc,acc). F = { {q. i\<in>acc q} | i. i<num_acc } 
    \<and> \<Union>(range acc) \<subseteq> {0..<num_acc})"
  unfolding F_to_idx_def
  apply (refine_rcg refine_vcg)
  apply (clarsimp dest!: sym[where t=F])
  apply (intro equalityI subsetI)
  apply (auto simp: in_set_conv_nth) [2]

  apply auto []
  done

definition "mk_acc_impl Flist \<equiv> do {
  let acc = Map.empty;

  (_,acc) \<leftarrow> nfoldli Flist (\<lambda>_. True) (\<lambda>A (i,acc). do {
    acc \<leftarrow> FOREACHi (\<lambda>it acc'. 
      acc' = (\<lambda>v. 
        if v\<in>A-it then 
          Some (insert i (the_default {} (acc v))) 
        else 
          acc v
      )
    ) 
      A (\<lambda>v acc. RETURN (acc(v\<mapsto>insert i (the_default {} (acc v))))) acc;
    RETURN (Suc i,acc)
  }) (0,acc);
  RETURN (\<lambda>x. the_default {} (acc x))
}"

lemma mk_acc_impl_correct: 
  assumes F: "(Flist',Flist)\<in>Id"
  assumes FIN: "\<forall>A\<in>set Flist. finite A"
  shows "mk_acc_impl Flist' \<le> \<Down>Id (RETURN (\<lambda>v. {i . i<length Flist \<and> v\<in>Flist!i}))"
  using F apply simp
  unfolding mk_acc_impl_def

  apply (refine_rcg 
    nfoldli_rule[where 
      I="\<lambda>l1 l2 (i,res). i=length l1 
        \<and> the_default {} o res = (\<lambda>v. {j . j<i \<and> v\<in>Flist!j})"
    ]
    refine_vcg 
  )
  using FIN apply (simp_all)
  apply (rule ext) apply auto []

  apply (rule ext) apply (auto split: if_split_asm simp: nth_append nth_Cons') []
  apply (rule ext) apply (auto split: if_split_asm simp: nth_append nth_Cons' 
    fun_comp_eq_conv) []

  apply (rule ext) apply (auto simp: fun_comp_eq_conv) []
  done

definition F_to_idx_impl :: "'Q set set \<Rightarrow> (nat \<times> ('Q \<Rightarrow> nat set)) nres" where
  "F_to_idx_impl F \<equiv> do {
    Flist \<leftarrow> SPEC (\<lambda>Flist. distinct Flist \<and> set Flist = F);
    let num_acc = length Flist;
    acc \<leftarrow> mk_acc_impl Flist;
    RETURN (num_acc,acc)
  }"

lemma F_to_idx_refine: 
  assumes FIN: "\<forall>A\<in>F. finite A"
  shows "F_to_idx_impl F \<le> \<Down>Id (F_to_idx F)"
  using assms
  unfolding F_to_idx_impl_def F_to_idx_def

  apply (refine_rcg bind_Let_refine2[OF mk_acc_impl_correct])

  apply auto
  done

definition gbg_to_idx_ext 
  :: "_ \<Rightarrow> ('a, 'more) gb_graph_rec_scheme \<Rightarrow> ('a, 'more') igb_graph_rec_scheme nres"
  where "gbg_to_idx_ext ecnv A = do {
  (num_acc,acc) \<leftarrow> F_to_idx_impl (gbg_F A); 
  RETURN \<lparr> 
    g_V = g_V A,
    g_E = g_E A, 
    g_V0=g_V0 A, 
    igbg_num_acc = num_acc, 
    igbg_acc = acc,
    \<dots> = ecnv A
  \<rparr>
}"

lemma (in gb_graph) gbg_to_idx_ext_correct:
  assumes [simp, intro]: "\<And> A. A \<in> F \<Longrightarrow> finite A"
  shows "gbg_to_idx_ext ecnv G \<le> SPEC (\<lambda>G'. 
    igb_graph.is_acc_run G' = is_acc_run 
  \<and> g_V G' = V
  \<and> g_E G' = E
  \<and> g_V0 G' = V0
  \<and> igb_graph_rec.more G' = ecnv G
  \<and> igb_graph G'
)"
proof -
  note F_to_idx_refine[of F]
  also note F_to_idx_correct
  finally have R: "F_to_idx_impl F
    \<le> SPEC (\<lambda>(num_acc, acc). F = {{q. i \<in> acc q} |i. i < num_acc}
      \<and> \<Union>(range acc) \<subseteq> {0..<num_acc})" by simp

  have eq_conjI: "\<And>a b c. (b\<longleftrightarrow>c) \<Longrightarrow> (a&b \<longleftrightarrow> a&c)" by simp

  {
    fix acc :: "'Q \<Rightarrow> nat set" and num_acc r
    have "(\<forall>A. (\<exists>i. A = {q. i \<in> acc q} \<and> i < num_acc) \<longrightarrow> (limit r \<inter> A \<noteq> {})) 
      \<longleftrightarrow> (\<forall>i<num_acc. \<exists>q\<in>limit r. i\<in>acc q)"
      by blast
  } note aux1=this

  {
    fix acc :: "'Q \<Rightarrow> nat set" and num_acc i
    assume FE: "F = {{q. i \<in> acc q} |i. i < num_acc}"
    assume INR: "(\<Union>x. acc x) \<subseteq> {0..<num_acc}"
    have "finite {q. i \<in> acc q}" 
    proof (cases "i<num_acc")
      case True thus ?thesis using FE by auto
    next
      case False hence "{q. i \<in> acc q} = {}" using INR by force
      thus ?thesis by simp
    qed
  } note aux2=this

  {
    fix acc :: "'Q \<Rightarrow> nat set" and num_acc q
    assume FE: "F = {{q. i \<in> acc q} |i. i < num_acc}"
      and INR: "(\<Union>x. acc x) \<subseteq> {0..<num_acc}"
      and "acc q \<noteq> {}"
    then obtain i where "i\<in>acc q" by auto
    moreover with INR have "i<num_acc" by force
    ultimately have "q\<in>\<Union>F" by (auto simp: FE)
    with F_ss have "q\<in>V" by auto
  } note aux3=this

  show ?thesis
    unfolding gbg_to_idx_ext_def
    apply (refine_rcg order_trans[OF R] refine_vcg)
  proof clarsimp_all
    fix acc and num_acc :: nat
    assume FE[simp]: "F = {{q. i \<in> acc q} |i. i < num_acc}"
      and BOUND: "(\<Union>x. acc x) \<subseteq> {0..<num_acc}"
    let ?G' = "\<lparr>
      g_V = V, 
      g_E = E, 
      g_V0 = V0, 
      igbg_num_acc = num_acc, 
      igbg_acc = acc,
      \<dots> = ecnv G\<rparr>"

    interpret G': igb_graph ?G'
      apply unfold_locales
      using V0_ss E_ss 
      apply (auto simp add: aux2 aux3 BOUND)
      done

    show "igb_graph ?G'" by unfold_locales

    show "G'.is_acc_run = is_acc_run"
      unfolding G'.is_acc_run_def[abs_def] is_acc_run_def[abs_def] 
        G'.is_run_def[abs_def] is_run_def[abs_def]
        G'.is_acc_def[abs_def] is_acc_def[abs_def]
      
      apply (clarsimp intro!: ext eq_conjI)
      apply auto []
      apply (metis (lifting, no_types) INFM_mono mem_Collect_eq)
      done
  qed
qed

abbreviation gbg_to_idx :: "('q,_) gb_graph_rec_scheme \<Rightarrow> 'q igb_graph_rec nres"
  where "gbg_to_idx \<equiv> gbg_to_idx_ext (\<lambda>_. ())"

definition ti_Lcnv where "ti_Lcnv ecnv A \<equiv> \<lparr> igba_L = gba_L A, \<dots>=ecnv A \<rparr>"

abbreviation "gba_to_idx_ext ecnv \<equiv> gbg_to_idx_ext (ti_Lcnv ecnv)"
abbreviation "gba_to_idx \<equiv> gba_to_idx_ext (\<lambda>_. ())"

lemma (in gba) gba_to_idx_ext_correct:
  assumes [simp, intro]: "\<And> A. A \<in> F \<Longrightarrow> finite A"
  shows "gba_to_idx_ext ecnv G \<le> 
    SPEC (\<lambda>G'.
    igba.accept G' = accept 
  \<and> g_V G' = V
  \<and> g_E G' = E
  \<and> g_V0 G' = V0
  \<and> igba_rec.more G' = ecnv G
  \<and> igba G')"
  apply (rule order_trans[OF gbg_to_idx_ext_correct])
  apply (rule, assumption)
  apply (rule SPEC_rule)
  apply (elim conjE, intro conjI)
proof -
  fix G'
  assume 
    ARUN: "igb_graph.is_acc_run G' = is_acc_run"
    and MORE: "igb_graph_rec.more G' = ti_Lcnv ecnv G" 
    and LOC: "igb_graph G'"
    and FIELDS: "g_V G' = V" "g_E G' = E" "g_V0 G' = V0"
  
  from LOC interpret igb: igb_graph G' .

  interpret igb: igba G'
    apply unfold_locales
    using MORE FIELDS L_ss
    unfolding ti_Lcnv_def
    apply (cases G')
    apply simp
    done

  show "igba.accept G' = accept" and "igba_rec.more G' = ecnv G"
    using ARUN MORE 
    unfolding accept_def[abs_def] igb.accept_def[abs_def] ti_Lcnv_def
    apply (cases G', (auto) []) +
    done

  show "igba G'" by unfold_locales
qed

corollary (in gba) gba_to_idx_ext_lang_correct:
  assumes [simp, intro]: "\<And> A. A \<in> F \<Longrightarrow> finite A"
  shows "gba_to_idx_ext ecnv G \<le> 
    SPEC (\<lambda>G'. igba.lang G' = lang \<and> igba_rec.more G' = ecnv G \<and> igba G')"
  apply (rule order_trans[OF gba_to_idx_ext_correct])
  apply (rule, assumption)
  apply (rule SPEC_rule)
  unfolding lang_def[abs_def]
  apply (subst igba.lang_def)
  apply auto
  done

subsubsection \<open>Degeneralization\<close>

context igb_graph
begin

  definition degeneralize_ext :: "_ \<Rightarrow> ('Q \<times> nat, _) b_graph_rec_scheme" where
    "degeneralize_ext ecnv \<equiv> 
      if num_acc = 0 then \<lparr>
        g_V = V \<times> {0},
        g_E = {((q,0),(q',0)) | q q'. (q,q')\<in>E}, 
        g_V0 = V0\<times>{0}, 
        bg_F = V \<times> {0},
        \<dots> = ecnv G
      \<rparr>
      else \<lparr>
        g_V = V \<times> {0..<num_acc},
        g_E = { ((q,i),(q',i')) | i i' q q'. 
            i<num_acc 
          \<and> (q,q')\<in>E 
          \<and> i' = (if i\<in>acc q then (i+1) mod num_acc else i) },
        g_V0 = V0 \<times> {0},
        bg_F = {(q,0)| q. 0\<in>acc q},
        \<dots> = ecnv G
      \<rparr>"

  abbreviation degeneralize where "degeneralize \<equiv> degeneralize_ext (\<lambda>_. ())"

  lemma degen_more[simp]: "b_graph_rec.more (degeneralize_ext ecnv) = ecnv G"
    unfolding degeneralize_ext_def
    by auto

  lemma degen_invar: "b_graph (degeneralize_ext ecnv)"
  proof
    let ?G' = "degeneralize_ext ecnv"

    show "g_V0 ?G' \<subseteq> g_V ?G'"
      unfolding degeneralize_ext_def
      using V0_ss
      by auto

    show "g_E ?G' \<subseteq> g_V ?G' \<times> g_V ?G'"
      unfolding degeneralize_ext_def
      using E_ss
      by auto

    show "bg_F ?G' \<subseteq> g_V ?G'"
      unfolding degeneralize_ext_def
      using acc_ss
      by auto

  qed

  sublocale degen: b_graph "degeneralize_ext m" using degen_invar .

  lemma degen_finite_reachable:
    assumes [simp, intro]: "finite (E\<^sup>* `` V0)"
    shows "finite ((g_E (degeneralize_ext ecnv))\<^sup>* `` g_V0 (degeneralize_ext ecnv))"
  proof -
    let ?G' = "degeneralize_ext ecnv"
    have "((g_E ?G')\<^sup>* `` g_V0 ?G')
      \<subseteq> E\<^sup>*``V0 \<times> {0..num_acc}"
    proof -
      {
        fix q n q' n'
        assume "((q,n),(q',n'))\<in>(g_E ?G')\<^sup>*" 
          and 0: "(q,n)\<in>g_V0 ?G'"
        hence G1: "(q,q')\<in>E\<^sup>* \<and> n'\<le>num_acc"
          apply (induction rule: rtrancl_induct2)
          by (auto simp: degeneralize_ext_def split: if_split_asm)
        
        from 0 have G2: "q\<in>V0 \<and> n\<le>num_acc"
          by (auto simp: degeneralize_ext_def split: if_split_asm)
        note G1 G2
      } thus ?thesis by fastforce
    qed
    also have "finite \<dots>" by auto
    finally (finite_subset) show "finite ((g_E ?G')\<^sup>* `` g_V0 ?G')" .
  qed

  lemma degen_is_run_sound: 
    "degen.is_run T m r \<Longrightarrow> is_run (fst o r)"
    unfolding degen.is_run_def is_run_def
    unfolding degeneralize_ext_def
    apply (clarsimp split: if_split_asm simp: ipath_def)
    apply (metis fst_conv)+
    done

  lemma degen_path_sound: 
    assumes "path (degen.E T m) u p v" 
    shows "path E (fst u) (map fst p) (fst v)"
    using assms
    by induction (auto simp: degeneralize_ext_def path_simps split: if_split_asm)

  lemma degen_V0_sound: 
    assumes "u \<in> degen.V0 T m" 
    shows "fst u \<in> V0"
    using assms
    by (auto simp: degeneralize_ext_def path_simps split: if_split_asm)


  lemma degen_visit_acc:
    assumes "path (degen.E T m) (q,n) p (q',n')"
    assumes "n\<noteq>n'"
    shows "\<exists>qa. (qa,n)\<in>set p \<and> n\<in>acc qa"
    using assms
  proof (induction _ "(q,n)" p "(q',n')" arbitrary: q rule: path.induct)
    case (path_prepend qnh p)
    then obtain qh nh where [simp]: "qnh=(qh,nh)" by (cases qnh)
    from \<open>((q,n),qnh) \<in> degen.E T m\<close> 
    have "nh=n \<or> (nh=(n+1) mod num_acc \<and> n\<in>acc q)"
      by (auto simp: degeneralize_ext_def split: if_split_asm)
    thus ?case proof
      assume [simp]: "nh=n"
      from path_prepend obtain qa where "(qa, n) \<in> set p" and "n \<in> acc qa" 
        by auto
      thus ?case by auto
    next
      assume "(nh=(n+1) mod num_acc \<and> n\<in>acc q)" thus ?case by auto
    qed
  qed simp

  lemma degen_run_complete0:
    assumes [simp]: "num_acc = 0"
    assumes R: "is_run r"
    shows "degen.is_run T m (\<lambda>i. (r i,0))"
    using R
    unfolding degen.is_run_def is_run_def
    unfolding ipath_def degeneralize_ext_def
    by auto

  lemma degen_acc_run_complete0:
    assumes [simp]: "num_acc = 0"
    assumes R: "is_acc_run r"
    shows "degen.is_acc_run T m (\<lambda>i. (r i,0))"
    using R
    unfolding degen.is_acc_run_def is_acc_run_def is_acc_def degen.is_acc_def
    apply (simp add: degen_run_complete0)
    unfolding degeneralize_ext_def
    using run_reachable[of r] reachable_V
    by (auto simp: INFM_nat)

  lemma degen_run_complete:
    assumes [simp]: "num_acc \<noteq> 0"
    assumes R: "is_run r"
    shows "\<exists>r'. degen.is_run T m r' \<and> r = fst o r'"
    using R
    unfolding degen.is_run_def is_run_def ipath_def
    apply (elim conjE)
  proof -
    assume R0: "r 0 \<in> V0" and RS: "\<forall>i. (r i, r (Suc i)) \<in> E"

    define r' where "r' = rec_nat
      (r 0,0) 
      (\<lambda>i (q,n). (r (Suc i), if n \<in> acc q then (n+1) mod num_acc else n))"

    have [simp]:
      "r' 0 = (r 0,0)"
      "\<And>i. r' (Suc i) = (
        let 
          (q,n)=r' i 
        in 
          (r (Suc i), if n \<in> acc q then (n+1) mod num_acc else n)
      )"
      unfolding r'_def
      by auto

    have R0': "r' 0 \<in> degen.V0 T m" using R0
      unfolding degeneralize_ext_def by auto

    have MAP: "r = fst o r'"
    proof (rule ext)
      fix i
      show "r i = (fst o r') i"
        by (cases i) (auto simp: split: prod.split)
    qed

    have [simp]: "0<num_acc" by (cases num_acc) auto

    have SND_LESS: "\<And>i. snd (r' i) < num_acc"
    proof -
      fix i show "snd (r' i) < num_acc" by (induction i) (auto split: prod.split) 
    qed

    have RS': "\<forall>i. (r' i, r' (Suc i)) \<in> degen.E T m"
    proof
      fix i
      obtain n where [simp]: "r' i = (r i,n)"
        apply (cases i)
        apply (force)
        apply (force split: prod.split)
        done
      from SND_LESS[of i] have [simp]: "n<num_acc" by simp

      show "(r' i, r' (Suc i)) \<in> degen.E T m" using RS
        by (auto simp: degeneralize_ext_def)
    qed

    from R0' RS' MAP show 
      "\<exists>r'. (r' 0 \<in> degen.V0 T m
      \<and> (\<forall>i. (r' i, r' (Suc i)) \<in> degen.E T m)) 
      \<and> r = fst \<circ> r'" by blast
  qed

  lemma degen_run_bound:
    assumes [simp]: "num_acc \<noteq> 0"
    assumes R: "degen.is_run T m r"
    shows "snd (r i) < num_acc"
    apply (induction i)
    using R 
    unfolding degen.is_run_def is_run_def
    unfolding degeneralize_ext_def ipath_def
    apply -
    apply auto []
    apply clarsimp
    by (metis snd_conv)
  
  lemma degen_acc_run_complete_aux1: 
    assumes NN0[simp]: "num_acc \<noteq> 0"
    assumes R: "degen.is_run T m r"
    assumes EXJ: "\<exists>j\<ge>i. n \<in> acc (fst (r j))"
    assumes RI: "r i = (q,n)"
    shows "\<exists>j\<ge>i. \<exists>q'. r j = (q',n) \<and> n \<in> acc q'"
  proof -
    define j where "j = (LEAST j. j\<ge>i \<and> n \<in> acc (fst (r j)))"

    from RI have "n<num_acc" using degen_run_bound[OF NN0 R, of i] by auto
    from EXJ have 
      "j\<ge>i" 
      "n \<in> acc (fst (r j))" 
      "\<forall>k\<ge>i. n \<in> acc (fst (r k)) \<longrightarrow> j\<le>k"
      using LeastI_ex[OF EXJ]
      unfolding j_def
      apply (auto) [2]
      apply (metis (lifting) Least_le)
      done
    hence "\<forall>k\<ge>i. k<j \<longrightarrow> n \<notin> acc (fst (r k))" by auto

    have "\<forall>k. k\<ge>i \<and> k\<le>j \<longrightarrow> (snd (r k) = n)"
    proof (clarify)
      fix k
      assume "i\<le>k" "k\<le>j"
      thus "snd (r k) = n"
      proof (induction k rule: less_induct)
        case (less k)
        show ?case proof (cases "k=i")
          case True thus ?thesis using RI by simp
        next
          case False with less.prems have "k - 1 < k" "i \<le> k - 1" "k - 1\<le>j"
            by auto
          from less.IH[OF this] have "snd (r (k - 1)) = n" .
          moreover from R have 
            "(r (k - 1), r k) \<in> degen.E T m"
            unfolding degen.is_run_def is_run_def ipath_def
            by clarsimp (metis One_nat_def Suc_diff_1 \<open>k - 1 < k\<close> 
              less_nat_zero_code neq0_conv)
          moreover have "n \<notin> acc (fst (r (k - 1)))"
            using \<open>\<forall>k\<ge>i. k < j \<longrightarrow> n \<notin> acc (fst (r k))\<close> \<open>i \<le> k - 1\<close> \<open>k - 1 < k\<close> 
              dual_order.strict_trans1 less.prems(2) 
              by blast
          ultimately show ?thesis
            by (auto simp: degeneralize_ext_def)
        qed
      qed
    qed

    thus ?thesis 
      by (metis \<open>i \<le> j\<close> \<open>n \<in> local.acc (fst (r j))\<close> 
        order_refl surjective_pairing)
  qed
      
  lemma degen_acc_run_complete_aux1': 
    assumes NN0[simp]: "num_acc \<noteq> 0"
    assumes R: "degen.is_run T m r"
    assumes ACC: "\<forall>n<num_acc. \<exists>\<^sub>\<infinity>i. n \<in> acc (fst (r i))"
    assumes RI: "r i = (q,n)"
    shows "\<exists>j\<ge>i. \<exists>q'. r j = (q',n) \<and> n \<in> acc q'"
  proof -
    from RI have "n<num_acc" using degen_run_bound[OF NN0 R, of i] by auto
    with ACC have EXJ: "\<exists>j\<ge>i. n \<in> acc (fst (r j))" 
      unfolding INFM_nat_le by blast

    from degen_acc_run_complete_aux1[OF NN0 R EXJ RI] show ?thesis .
  qed

  lemma degen_acc_run_complete_aux2:
    assumes NN0[simp]: "num_acc \<noteq> 0"
    assumes R: "degen.is_run T m r"
    assumes ACC: "\<forall>n<num_acc. \<exists>\<^sub>\<infinity>i. n \<in> acc (fst (r i))"
    assumes RI: "r i = (q,n)" and OFS: "ofs<num_acc"
    shows "\<exists>j\<ge>i. \<exists>q'. 
      r j = (q',(n + ofs) mod num_acc) \<and> (n + ofs) mod num_acc \<in> acc q'"
    using RI OFS
  proof (induction ofs arbitrary: q n i)
    case 0 
    from degen_run_bound[OF NN0 R, of i] \<open>r i = (q, n)\<close> 
    have NLE: "n<num_acc" 
      by simp

    with degen_acc_run_complete_aux1'[OF NN0 R ACC \<open>r i = (q, n)\<close>] show ?case
      by auto
  next
    case (Suc ofs)
    from Suc.IH[OF Suc.prems(1)] Suc.prems(2)
    obtain j q' where "j\<ge>i" and RJ: "r j = (q',(n+ofs) mod num_acc)" 
      and A: "(n+ofs) mod num_acc \<in> acc q'"
      by auto
    from R have "(r j, r (Suc j)) \<in> degen.E T m" 
      by (auto simp: degen.is_run_def is_run_def ipath_def)
    with RJ A obtain q2 where RSJ: "r (Suc j) = (q2,(n+Suc ofs) mod num_acc)" 
      by (auto simp: degeneralize_ext_def mod_simps)

    have aux: "\<And>j'. i\<le>j \<Longrightarrow> Suc j \<le> j' \<Longrightarrow> i\<le>j'" by auto
    from degen_acc_run_complete_aux1'[OF NN0 R ACC RSJ] \<open>j\<ge>i\<close> 
    show ?case 
      by (auto dest: aux)
  qed

  lemma degen_acc_run_complete:
    assumes AR: "is_acc_run r"
    obtains r' 
    where "degen.is_acc_run T m r'" and "r = fst o r'"
  proof (cases "num_acc = 0")
    case True 
    with AR degen_acc_run_complete0 
    show ?thesis by (auto intro!: that[of "(\<lambda>i. (r i, 0))"])
  next
    case False
    assume NN0[simp]: "num_acc \<noteq> 0"

    from AR have R: "is_run r" and ACC: "\<forall>n<num_acc. \<exists>\<^sub>\<infinity>i. n \<in> acc (r i)"
      unfolding is_acc_run_def is_acc_def by auto

    from degen_run_complete[OF NN0 R] obtain r' where 
      R': "degen.is_run T m r'" 
      and [simp]: "r = fst \<circ> r'" 
      by auto

    from ACC have ACC': "\<forall>n<num_acc. \<exists>\<^sub>\<infinity>i. n \<in> acc (fst (r' i))" by simp

    have "\<forall>i. \<exists>j>i. r' j \<in> degen.F T m"
    proof
      fix i
      obtain q n where RI: "r' (Suc i) = (q,n)" by (cases "r' (Suc i)")
      have "(n + (num_acc - n mod num_acc)) mod num_acc = 0"
        by (metis NN0 R' \<open>r' (Suc i) = (q, n)\<close> add_diff_cancel_left' 
          degen_run_bound less_imp_add_positive mod_self nat_mod_eq' snd_conv)
      then obtain ofs where 
        OFS_LESS: "ofs<num_acc" 
        and [simp]: "(n + ofs) mod num_acc = 0"
        by (metis NN0 Nat.add_0_right diff_less neq0_conv)
      with degen_acc_run_complete_aux2[OF NN0 R' ACC' RI OFS_LESS]
      obtain j q' where 
        "j>i" "r' j = (q',0)" and "0\<in>acc q'" 
        by (auto simp: less_eq_Suc_le)
      thus "\<exists>j>i. r' j \<in> degen.F T m" 
        by (auto simp: degeneralize_ext_def)
    qed
    hence "\<exists>\<^sub>\<infinity>i. r' i \<in> degen.F T m" by (auto simp: INFM_nat)

    have "degen.is_acc_run T m r'"
      unfolding degen.is_acc_run_def degen.is_acc_def
      by rule fact+
    thus ?thesis by (auto intro: that)
  qed

  lemma degen_run_find_change:
    assumes NN0[simp]: "num_acc \<noteq> 0"
    assumes R: "degen.is_run T m r"
    assumes A: "i\<le>j" "r i = (q,n)" "r j = (q',n')" "n\<noteq>n'"
    obtains k qk where "i\<le>k" "k<j" "r k = (qk,n)" "n \<in> acc qk"
  proof -
    from degen_run_bound[OF NN0 R] A have "n<num_acc" "n'<num_acc"
      by (metis snd_conv)+

    define k where "k = (LEAST k. i<k \<and> snd (r k) \<noteq> n)"

    have "i<k" "snd (r k) \<noteq> n"
      by (metis (lifting, mono_tags) LeastI_ex A k_def leD less_linear snd_conv)+

    from Least_le[where P="\<lambda>k. i<k \<and> snd (r k) \<noteq> n", folded k_def]
    have LEK_EQN: "\<forall>k'. i\<le>k' \<and> k'<k \<longrightarrow> snd (r k') = n"
      using \<open>r i = (q,n)\<close>
      by clarsimp (metis le_neq_implies_less not_le snd_conv)
    hence SND_RKMO: "snd (r (k - 1)) = n" using \<open>i<k\<close> by auto
    moreover from R have "(r (k - 1), r k) \<in> degen.E T m"
      unfolding degen.is_run_def ipath_def using \<open>i<k\<close>
      by clarsimp (metis Suc_pred gr_implies_not0 neq0_conv) 
    moreover note \<open>snd (r k) \<noteq> n\<close>
    ultimately have "n \<in> acc (fst (r (k - 1)))"
      by (auto simp: degeneralize_ext_def split: if_split_asm)
    moreover have "k - 1 < j" using A LEK_EQN 
      apply (rule_tac ccontr)
      apply clarsimp
      by (metis One_nat_def \<open>snd (r (k - 1)) = n\<close> less_Suc_eq 
        less_imp_diff_less not_less_eq snd_conv)
    ultimately show thesis
      apply -
      apply (rule that[of "k - 1" "fst (r (k - 1))"])
      using \<open>i<k\<close> SND_RKMO by auto
  qed


  lemma degen_run_find_acc_aux:
    assumes NN0[simp]: "num_acc \<noteq> 0"
    assumes AR: "degen.is_acc_run T m r"
    assumes A: "r i = (q,0)" "0 \<in> acc q" "n<num_acc"
    shows "\<exists>j qj. i\<le>j \<and> r j = (qj,n) \<and> n \<in> acc qj"
  proof -
    from AR have R: "degen.is_run T m r" 
      and ACC: "\<exists>\<^sub>\<infinity>i. r i \<in> degen.F T m"
      (*and ACC: "limit r \<inter> bg_F (degeneralize_ext ecnv) \<noteq> {}"*)
      unfolding degen.is_acc_run_def degen.is_acc_def by auto
    from ACC have ACC': "\<forall>i. \<exists>j>i. r j \<in> degen.F T m"
      by (auto simp: INFM_nat)
    
    show ?thesis using \<open>n<num_acc\<close>
    proof (induction n)
      case 0 thus ?case using A by auto
    next
      case (Suc n)
      then obtain j qj where "i\<le>j" "r j = (qj,n)" "n\<in>acc qj" by auto
      moreover from R have "(r j, r (Suc j)) \<in> degen.E T m" 
        unfolding degen.is_run_def ipath_def
        by auto
      ultimately obtain qsj where RSJ: "r (Suc j) = (qsj,Suc n)"
        unfolding degeneralize_ext_def using \<open>Suc n<num_acc\<close> by auto
      
      from ACC' obtain k q0 where "Suc j \<le> k" "r k = (q0, 0)"
        unfolding degeneralize_ext_def apply auto
        by (metis less_imp_le_nat)
      from degen_run_find_change[OF NN0 R \<open>Suc j \<le> k\<close> RSJ \<open>r k = (q0, 0)\<close>] 
      obtain l ql where
        "Suc j \<le> l" "l < k" "r l = (ql, Suc n)" "Suc n \<in> acc ql" 
        by blast
      thus ?case using \<open>i \<le> j\<close>
        by (intro exI[where x=l] exI[where x=ql]) auto
    qed
  qed
      
  lemma degen_acc_run_sound:
    assumes A: "degen.is_acc_run T m r"
    shows "is_acc_run (fst o r)"
  proof -
    from A have R: "degen.is_run T m r" 
      and ACC: "\<exists>\<^sub>\<infinity>i. r i \<in> degen.F T m"
      unfolding degen.is_acc_run_def degen.is_acc_def by auto
    from degen_is_run_sound[OF R] have R': "is_run (fst o r)" .

    show ?thesis
    proof (cases "num_acc = 0")
      case NN0[simp]: False

      from ACC have ACC': "\<forall>i. \<exists>j>i. r j \<in> degen.F T m"
        by (auto simp: INFM_nat)

      have "\<forall>n<num_acc. \<forall>i. \<exists>j>i. n \<in> acc (fst (r j))" 
      proof (intro allI impI)
        fix n i

        obtain j qj where "j>i" and RJ: "r j = (qj,0)" and ACCJ: "0 \<in> acc (qj)"
          using ACC' unfolding degeneralize_ext_def by fastforce

        assume NLESS: "n<num_acc"
        show "\<exists>j>i. n \<in> acc (fst (r j))"
        proof (cases n)
          case 0 thus ?thesis using \<open>j>i\<close> RJ ACCJ by auto
        next
          case [simp]: (Suc n')
          from degen_run_find_acc_aux[OF NN0 A RJ ACCJ NLESS] obtain k qk where
            "j\<le>k" "r k = (qk,n)" "n \<in> acc qk" by auto
          thus ?thesis
            by (metis \<open>i < j\<close> dual_order.strict_trans1 fst_conv)
        qed
      qed
      hence "\<forall>n<num_acc. \<exists>\<^sub>\<infinity>i. n \<in> acc (fst (r i))"
        by (auto simp: INFM_nat)
      with R' show ?thesis
        unfolding is_acc_run_def is_acc_def by auto
    next
      case [simp]: True
      with R' show ?thesis
        unfolding is_acc_run_def is_acc_def
        by auto
    qed
  qed

  lemma degen_acc_run_iff:
    "is_acc_run r \<longleftrightarrow> (\<exists>r'. fst o r' = r \<and> degen.is_acc_run T m r')"
    using degen_acc_run_complete degen_acc_run_sound
    by blast

end

subsection "System Automata"
text \<open>
  System automata are (finite) rooted graphs with a labeling function. They are 
  used to describe the model (system) to be checked.
\<close>

record ('Q,'L) sa_rec = "'Q graph_rec" +
  sa_L :: "'Q \<Rightarrow> 'L"

locale sa =
  g?: graph G
  for G :: "('Q, 'L, 'more) sa_rec_scheme"
begin

  abbreviation L where "L \<equiv> sa_L G"

  definition "accept w \<equiv> \<exists>r. is_run r \<and> w = L o r"

  lemma acceptI[intro?]: "\<lbrakk>is_run r; w = L o r\<rbrakk> \<Longrightarrow> accept w" by (auto simp: accept_def)

  definition "lang \<equiv> Collect accept"

  lemma langI[intro?]: "accept w \<Longrightarrow> w\<in>lang" by (auto simp: lang_def)

end

subsubsection "Product Construction"
text \<open>
  In this section we formalize the product construction between a GBA and a system
  automaton. The result is a GBG and a projection function, such that projected 
  runs of the GBG correspond to words accepted by the GBA and the system.
\<close>

locale igba_sys_prod_precond = igba: igba G + sa: sa S for
  G :: "('q,'l,'moreG) igba_rec_scheme"
  and S :: "('s,'l,'moreS) sa_rec_scheme"
begin

  definition "prod \<equiv> \<lparr>
    g_V = igba.V \<times> sa.V,
    g_E = { ((q,s),(q',s')). 
      igba.L q (sa.L s) \<and> (q,q') \<in> igba.E \<and> (s,s') \<in> sa.E },
    g_V0 = igba.V0 \<times> sa.V0,
    igbg_num_acc = igba.num_acc,
    igbg_acc = (\<lambda>(q,s). if s\<in>sa.V then igba.acc q else {} ) \<rparr>"

  lemma prod_invar: "igb_graph prod" 
    apply unfold_locales

    using igba.V0_ss sa.V0_ss
    apply (auto simp: prod_def) []

    using igba.E_ss sa.E_ss
    apply (auto simp: prod_def) []

    using igba.acc_bound
    apply (auto simp: prod_def split: if_split_asm) []

    using igba.acc_ss
    apply (fastforce simp: prod_def split: if_split_asm) []
    done
  
  sublocale prod: igb_graph prod using prod_invar .

  lemma prod_finite_reachable:
    assumes "finite (igba.E\<^sup>* `` igba.V0)" "finite (sa.E\<^sup>* `` sa.V0)"
    shows "finite ((g_E prod)\<^sup>* `` g_V0 prod)"
  proof -
    {
      fix q s q' s'
      assume "((q,s),(q',s')) \<in> (g_E prod)\<^sup>*"
      hence "(q,q') \<in> (igba.E)\<^sup>* \<and> (s,s') \<in> (sa.E)\<^sup>*"
        apply (induction rule: rtrancl_induct2)
        apply (auto simp: prod_def)
        done
    } note gsp_reach=this

    have [simp]: "\<And>q s. (q,s) \<in> g_V0 prod \<longleftrightarrow> q \<in> igba.V0 \<and> s \<in> sa.V0"
      by (auto simp: prod_def)

    have reachSS: 
      "((g_E prod)\<^sup>* `` g_V0 prod) 
      \<subseteq> ((igba.E)\<^sup>* `` igba.V0) \<times> (sa.E\<^sup>* `` sa.V0)"
      by (auto dest: gsp_reach)
    show ?thesis
      apply (rule finite_subset[OF reachSS])
      using assms
      by simp
  qed

  lemma prod_fields:
    "prod.V = igba.V \<times> sa.V"
    "prod.E = { ((q,s),(q',s')). 
      igba.L q (sa.L s) \<and> (q,q') \<in> igba.E \<and> (s,s') \<in> sa.E }"
    "prod.V0 = igba.V0 \<times> sa.V0"
    "prod.num_acc = igba.num_acc"
    "prod.acc = (\<lambda>(q,s). if s\<in>sa.V then igba.acc q else {} )"
    unfolding prod_def
    apply simp_all
    done

  lemma prod_run: "prod.is_run r \<longleftrightarrow> 
      igba.is_run (fst o r) 
    \<and> sa.is_run (snd o r)
    \<and> (\<forall>i. igba.L (fst (r i)) (sa.L (snd (r i))))" (is "?L=?R")
    apply rule
    unfolding igba.is_run_def sa.is_run_def prod.is_run_def
    unfolding prod_def ipath_def
    apply (auto split: prod.split_asm intro: in_prod_fst_sndI)
    apply (metis surjective_pairing)
    apply (metis surjective_pairing)
    apply (metis fst_conv snd_conv)
    apply (metis fst_conv snd_conv)
    apply (metis fst_conv snd_conv)
    done

  lemma prod_acc:
    assumes A: "range (snd o r) \<subseteq> sa.V"
    shows "prod.is_acc r \<longleftrightarrow> igba.is_acc (fst o r)"
  proof -
    {
      fix i
      from A have "prod.acc (r i) = igba.acc (fst (r i))"
        unfolding prod_fields
        apply safe
        apply (clarsimp_all split: if_split_asm)
        by (metis UNIV_I comp_apply imageI snd_conv subsetD)
    } note [simp] = this
    show ?thesis
      unfolding prod.is_acc_def igba.is_acc_def
      by (simp add: prod_fields(4))
  qed
  
  lemma gsp_correct1: 
    assumes A: "prod.is_acc_run r"
    shows "sa.is_run (snd o r) \<and> (sa.L o snd o r \<in> igba.lang)"
  proof -
    from A have PR: "prod.is_run r" and PA: "prod.is_acc r" 
      unfolding prod.is_acc_run_def by auto

    have PRR: "range r \<subseteq> prod.V" using prod.run_reachable prod.reachable_V PR by auto

    have RSR: "range (snd o r) \<subseteq> sa.V" using PRR unfolding prod_fields by auto
  
    show ?thesis
      using PR PA
      unfolding igba.is_acc_run_def
        igba.lang_def igba.accept_def[abs_def]
      apply (auto simp: prod_run prod_acc[OF RSR])
      done
  qed
  
  lemma gsp_correct2: 
    assumes A: "sa.is_run r" "sa.L o r \<in> igba.lang"
    shows "\<exists>r'. r = snd o r' \<and> prod.is_acc_run r'"
  proof -
    have [simp]: "\<And>r r'. fst o (\<lambda>i. (r i, r' i)) = r" 
      "\<And>r r'. snd o (\<lambda>i. (r i, r' i)) = r'"
      by auto

    from A show ?thesis
      unfolding prod.is_acc_run_def 
        igba.lang_def igba.accept_def[abs_def] igba.is_acc_run_def
      apply (clarsimp simp: prod_run)
      apply (rename_tac ra)
      apply (rule_tac x="\<lambda>i. (ra i, r i)" in exI)
      apply clarsimp
      
      apply (subst prod_acc)
      using order_trans[OF sa.run_reachable sa.reachable_V]
      apply auto []

      apply auto []
      done
  qed

end

end
