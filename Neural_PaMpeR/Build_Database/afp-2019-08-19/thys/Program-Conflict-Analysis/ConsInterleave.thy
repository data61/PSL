(*  Title:       Conflict analysis/Monitor Consistent Interleaving
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)
section "Monitor Consistent Interleaving"
theory ConsInterleave
imports Interleave Misc
begin
text_raw \<open>\label{thy:ConsInterleave}\<close>

text \<open>The monitor consistent interleaving operator is defined on two lists of arbitrary elements, provided an abstraction function @{term \<alpha>} that maps list elements to pairs of sets of monitors is available.
  @{term "\<alpha> e = (M,M')"} intuitively means that step @{term e} enters the monitors in @{term M} and passes (enters and leaves) the monitors in @{term M'}.
  The consistent interleaving describes all interleavings of the two lists that are consistent w.r.t. the monitor usage. 
\<close>

subsection "Monitors of lists of monitor pairs"
text \<open>The following defines the set of all monitors that occur in a list of pairs of monitors. This definition is used in the following context:
  \<open>mon_pl (map \<alpha> w)\<close> is the set of monitors used by a word \<open>w\<close> w.r.t. the abstraction \<open>\<alpha>\<close>\<close>
definition 
  "mon_pl w == foldl (\<union>) {} (map (\<lambda>e. fst e \<union> snd e) w)"

lemma mon_pl_empty[simp]: "mon_pl [] = {}"
  by (unfold mon_pl_def, auto)
lemma mon_pl_cons[simp]: "mon_pl (e#w) = fst e \<union> snd e \<union> mon_pl w"
  by (unfold mon_pl_def) (simp, subst foldl_un_empty_eq, auto)

lemma mon_pl_unconc: "!!b. mon_pl (a@b) = mon_pl a \<union> mon_pl b"
  by (induct a) auto

lemma mon_pl_ileq: "w\<preceq>w' \<Longrightarrow> mon_pl w \<subseteq> mon_pl w'"
  by (induct rule: less_eq_list_induct) auto

lemma mon_pl_set: "mon_pl w = \<Union>{ fst e \<union> snd e | e. e\<in>set w }"
  by (auto simp add: mon_pl_def foldl_set) blast+

fun
  cil :: "'a list \<Rightarrow> ('a \<Rightarrow> ('m set \<times> 'm set)) \<Rightarrow> 'a list \<Rightarrow> 'a list set" 
    ("_ \<otimes>\<^bsub>_\<^esub> _" [64,64,64] 64) where
  \<comment> \<open>Interleaving with the empty word results in the empty word\<close>
  "[] \<otimes>\<^bsub>\<alpha> \<^esub> w = {w}" 
  | "w \<otimes>\<^bsub>\<alpha>\<^esub> [] = {w}"
  \<comment> \<open>If both words are not empty, we can take the first step of one word, 
  interleave the rest with the other word and then append
  the first step to all result set elements, provided it does not allocate 
  a monitor that is used by the other word\<close>
  | "e1#w1 \<otimes>\<^bsub>\<alpha>\<^esub> e2#w2 = (
    if fst (\<alpha> e1) \<inter> mon_pl (map \<alpha> (e2#w2)) = {} then 
      e1\<cdot>(w1 \<otimes>\<^bsub>\<alpha>\<^esub> e2#w2) 
    else {}
  ) \<union> (
    if fst (\<alpha> e2) \<inter> mon_pl (map \<alpha> (e1#w1)) = {} then 
      e2\<cdot>(e1#w1 \<otimes>\<^bsub>\<alpha>\<^esub> w2) 
    else {}
  )"

text \<open>Note that this definition allows reentrant monitors, because it only checks that a monitor that is going to be entered by one word is not used in the {\em other} word. Thus the same word may enter the same monitor
  multiple times.\<close>

text \<open>The next lemmas are some auxiliary lemmas to simplify the handling of the consistent interleaving operator.\<close>
lemma cil_last_case_split[cases set, case_names left right]: "
  \<lbrakk> w\<in>e1#w1 \<otimes>\<^bsub>\<alpha>\<^esub> e2#w2; 
    !!w'. \<lbrakk>w=e1#w'; w'\<in>(w1 \<otimes>\<^bsub>\<alpha>\<^esub> e2#w2); 
           fst (\<alpha> e1) \<inter> mon_pl (map \<alpha> (e2#w2)) = {} \<rbrakk> \<Longrightarrow> P;
    !!w'. \<lbrakk>w=e2#w'; w'\<in>(e1#w1 \<otimes>\<^bsub>\<alpha>\<^esub> w2); 
           fst (\<alpha> e2) \<inter> mon_pl (map \<alpha> (e1#w1)) = {} \<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
  by (auto elim: list_set_cons_cases split: if_split_asm)

lemma cil_cases[cases set, case_names both_empty left_empty right_empty app_left app_right]: "
  \<lbrakk> w\<in>wa\<otimes>\<^bsub>\<alpha>\<^esub>wb; 
    \<lbrakk> w=[]; wa=[]; wb=[] \<rbrakk> \<Longrightarrow> P; 
    \<lbrakk>wa=[]; w=wb\<rbrakk> \<Longrightarrow> P; 
    \<lbrakk> w=wa; wb=[] \<rbrakk> \<Longrightarrow> P; 
    !!ea wa' w'. \<lbrakk>w=ea#w'; wa=ea#wa'; w'\<in>wa'\<otimes>\<^bsub>\<alpha>\<^esub>wb; 
                  fst (\<alpha> ea) \<inter> mon_pl (map \<alpha> wb) = {}  \<rbrakk> \<Longrightarrow> P;
    !!eb wb' w'. \<lbrakk>w=eb#w'; wb=eb#wb'; w'\<in>wa\<otimes>\<^bsub>\<alpha>\<^esub>wb'; 
                  fst (\<alpha> eb) \<inter> mon_pl (map \<alpha> wa) = {}  \<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
proof (induct wa \<alpha> wb rule: cil.induct)
  case 1 thus ?case by simp next
  case 2 thus ?case by simp next
  case (3 ea wa' \<alpha> eb wb') 
  from "3.prems"(1) show ?thesis proof (cases rule: cil_last_case_split)
    case (left w') from "3.prems"(5)[OF left(1) _ left(2,3)] show ?thesis by simp next
    case (right w') from "3.prems"(6)[OF right(1) _ right(2,3)] show ?thesis by simp
  qed
qed

lemma cil_induct'[case_names both_empty left_empty right_empty append]: "\<lbrakk>
  \<And>\<alpha>. P \<alpha> [] []; 
  \<And>\<alpha> ad ae. P \<alpha> [] (ad # ae); 
  \<And>\<alpha> z aa. P \<alpha> (z # aa) [];
  \<And>\<alpha> e1 w1 e2 w2. \<lbrakk>
    \<lbrakk>fst (\<alpha> e1) \<inter> mon_pl (map \<alpha> (e2 # w2)) = {}\<rbrakk> \<Longrightarrow> P \<alpha> w1 (e2 # w2); 
    \<lbrakk>fst (\<alpha> e2) \<inter> mon_pl (map \<alpha> (e1 # w1)) = {}\<rbrakk> \<Longrightarrow> P \<alpha> (e1 # w1) w2\<rbrakk> 
  \<Longrightarrow> P \<alpha> (e1 # w1) (e2 # w2)
  \<rbrakk> \<Longrightarrow> P \<alpha> wa wb"
  apply (induct wa \<alpha> wb rule: cil.induct)
  apply (case_tac w)
  apply auto
  done
  
lemma cil_induct_fix\<alpha>: "\<lbrakk>
  P \<alpha> [] []; 
  \<And>ad ae. P \<alpha> [] (ad # ae); 
  \<And>z aa. P \<alpha> (z # aa) [];
  \<And>e1 w1 e2 w2.
    \<lbrakk>fst (\<alpha> e2) \<inter> mon_pl (map \<alpha> (e1 # w1)) = {} \<longrightarrow> P \<alpha> (e1 # w1) w2;
     fst (\<alpha> e1) \<inter> mon_pl (map \<alpha> (e2 # w2)) = {} \<longrightarrow> P \<alpha> w1 (e2 # w2)\<rbrakk>
     \<Longrightarrow> P \<alpha> (e1 # w1) (e2 # w2)\<rbrakk>
  \<Longrightarrow> P \<alpha> v w"
  apply (induct v \<alpha> w rule: cil.induct)
  apply (case_tac w)
  apply auto
  done

lemma cil_induct_fix\<alpha>'[case_names both_empty left_empty right_empty append]: "\<lbrakk>
  P \<alpha> [] []; 
  \<And>ad ae. P \<alpha> [] (ad # ae); 
  \<And>z aa. P \<alpha> (z # aa) [];
  \<And>e1 w1 e2 w2. \<lbrakk>
    fst (\<alpha> e1) \<inter> mon_pl (map \<alpha> (e2 # w2)) = {} \<Longrightarrow> P \<alpha> w1 (e2 # w2);
    fst (\<alpha> e2) \<inter> mon_pl (map \<alpha> (e1 # w1)) = {} \<Longrightarrow> P \<alpha> (e1 # w1) w2\<rbrakk> 
    \<Longrightarrow> P \<alpha> (e1 # w1) (e2 # w2)
  \<rbrakk> \<Longrightarrow> P \<alpha> wa wb"
  apply (induct wa \<alpha> wb rule: cil.induct)
  apply (case_tac w)
  apply auto
  done

lemma [simp]: "w\<otimes>\<^bsub>\<alpha>\<^esub>[] = {w}"
  by (cases w, auto)

lemma cil_contains_empty[rule_format, simp]: "([] \<in> wa\<otimes>\<^bsub>\<alpha>\<^esub>wb) = (wa=[] \<and> wb=[])"
  by (induct wa \<alpha> wb rule: cil.induct) auto

lemma cil_cons_cases[cases set, case_names left right]: "\<lbrakk> e#w \<in> w1\<otimes>\<^bsub>\<alpha>\<^esub>w2; 
  !!w1'. \<lbrakk>w1=e#w1'; w\<in>w1'\<otimes>\<^bsub>\<alpha>\<^esub>w2; fst (\<alpha> e) \<inter> mon_pl (map \<alpha> w2) = {} \<rbrakk> \<Longrightarrow> P;
  !!w2'. \<lbrakk>w2=e#w2'; w\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2'; fst (\<alpha> e) \<inter> mon_pl (map \<alpha> w1) = {} \<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P" 
  by (cases rule: cil_cases) auto

lemma cil_set_induct[induct set, case_names empty left right]: "!!\<alpha> w1 w2. \<lbrakk> 
    w\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2; 
    !!\<alpha>. P [] \<alpha> [] []; 
    !!\<alpha> e w' w1' w2. \<lbrakk>w'\<in>w1'\<otimes>\<^bsub>\<alpha>\<^esub>w2; fst (\<alpha> e) \<inter> mon_pl (map \<alpha> w2) = {}; 
                      P w' \<alpha> w1' w2 \<rbrakk> \<Longrightarrow> P (e#w') \<alpha> (e#w1') w2;
    !!\<alpha> e w' w2' w1. \<lbrakk>w'\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2'; fst (\<alpha> e) \<inter> mon_pl (map \<alpha> w1) = {}; 
                      P w' \<alpha> w1 w2' \<rbrakk> \<Longrightarrow> P (e#w') \<alpha> w1 (e#w2')
  \<rbrakk> \<Longrightarrow> P w \<alpha> w1 w2" 
  by (induct w) (auto intro!: cil_contains_empty elim: cil_cons_cases)

lemma cil_set_induct_fix\<alpha>[induct set, case_names empty left right]: "!!w1 w2. \<lbrakk> 
    w\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2; 
    P [] \<alpha> [] []; 
    !!e w' w1' w2. \<lbrakk>w'\<in>w1'\<otimes>\<^bsub>\<alpha>\<^esub>w2; fst (\<alpha> e) \<inter> mon_pl (map \<alpha> w2) = {}; 
                    P w' \<alpha> w1' w2 \<rbrakk> \<Longrightarrow> P (e#w') \<alpha> (e#w1') w2;
    !!e w' w2' w1. \<lbrakk>w'\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2'; fst (\<alpha> e) \<inter> mon_pl (map \<alpha> w1) = {}; 
                    P w' \<alpha> w1 w2' \<rbrakk> \<Longrightarrow> P (e#w') \<alpha> w1 (e#w2')
  \<rbrakk> \<Longrightarrow> P w \<alpha> w1 w2" 
  by (induct w) (auto intro!: cil_contains_empty elim: cil_cons_cases)

lemma cil_cons1: "\<lbrakk>w\<in>wa\<otimes>\<^bsub>\<alpha>\<^esub>wb; fst (\<alpha> e) \<inter> mon_pl (map \<alpha> wb) = {}\<rbrakk> 
                  \<Longrightarrow> e#w \<in> e#wa \<otimes>\<^bsub>\<alpha>\<^esub> wb"
  by (cases wb) auto
lemma cil_cons2: "\<lbrakk>w\<in>wa\<otimes>\<^bsub>\<alpha>\<^esub>wb; fst (\<alpha> e) \<inter> mon_pl (map \<alpha> wa) = {}\<rbrakk> 
                  \<Longrightarrow> e#w \<in> wa \<otimes>\<^bsub>\<alpha>\<^esub> e#wb"
  by (cases wa) auto

subsection "Properties of consistent interleaving"

\<comment> \<open>Consistent interleaving is a restriction of interleaving\<close>
lemma cil_subset_il: "w\<otimes>\<^bsub>\<alpha>\<^esub>w' \<subseteq> w\<otimes>w'"
  apply (induct w \<alpha> w' rule: cil.induct)
  apply simp_all
  apply safe
  apply auto
  done

lemma cil_subset_il': "w\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2 \<Longrightarrow> w\<in>w1\<otimes>w2" 
  using cil_subset_il by (auto)

\<comment> \<open>Consistent interleaving preserves the set of letters of both operands\<close>
lemma cil_set: "w\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2 \<Longrightarrow> set w = set w1 \<union> set w2"
  by (induct rule: cil_set_induct_fix\<alpha>) auto
corollary cil_mon_pl: "w\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2 
  \<Longrightarrow> mon_pl (map \<alpha> w) = mon_pl (map \<alpha> w1) \<union> mon_pl (map \<alpha> w2)" 
  by (subst mon_pl_unconc[symmetric]) (simp add: mon_pl_set cil_set, blast 20)

\<comment> \<open>Consistent interleaving preserves the length of both operands\<close>
lemma cil_length[rule_format]: "\<forall>w\<in>wa\<otimes>\<^bsub>\<alpha>\<^esub>wb. length w = length wa + length wb"
  by (induct rule: cil.induct) auto

\<comment> \<open>Consistent interleaving contains all letters of each operand in the original order\<close>
lemma cil_ileq: "w\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2 \<Longrightarrow> w1\<preceq>w \<and> w2\<preceq>w"
  by (intro conjI cil_subset_il' ileq_interleave)

\<comment> \<open>Consistent interleaving is commutative and associative\<close>
lemma cil_commute: "w\<otimes>\<^bsub>\<alpha>\<^esub>w' = w'\<otimes>\<^bsub>\<alpha>\<^esub>w"
  by (induct rule: cil.induct) auto

lemma cil_assoc1: "!!wl w1 w2 w3. \<lbrakk> w\<in>wl\<otimes>\<^bsub>\<alpha>\<^esub>w3; wl\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2 \<rbrakk> 
  \<Longrightarrow> \<exists>wr. w\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>wr \<and> wr\<in>w2\<otimes>\<^bsub>\<alpha>\<^esub>w3" 
proof (induct w rule: length_compl_induct)
  case Nil thus ?case by auto
next
  case (Cons e w) from Cons.prems(1) show ?case proof (cases rule: cil_cons_cases)
    case (left wl') with Cons.prems(2) have "e#wl' \<in> w1\<otimes>\<^bsub>\<alpha>\<^esub>w2" by simp
    thus ?thesis proof (cases rule: cil_cons_cases[case_names left' right'])
      case (left' w1')
      from Cons.hyps[OF _ left(2) left'(2)] obtain wr where IHAPP: "w \<in> w1' \<otimes>\<^bsub>\<alpha>\<^esub> wr" "wr \<in> w2 \<otimes>\<^bsub>\<alpha>\<^esub> w3" by blast
      have "e#w\<in>e#w1'\<otimes>\<^bsub>\<alpha>\<^esub>wr" proof (rule cil_cons1[OF IHAPP(1)])
        from left left' cil_mon_pl[OF IHAPP(2)] show "fst (\<alpha> e) \<inter> mon_pl (map \<alpha> wr) = {}" by auto
      qed
      thus ?thesis using IHAPP(2) left' by blast
    next
      case (right' w2') from Cons.hyps[OF _ left(2) right'(2)] obtain wr where IHAPP: "w \<in> w1 \<otimes>\<^bsub>\<alpha>\<^esub> wr" "wr \<in> w2' \<otimes>\<^bsub>\<alpha>\<^esub> w3" by blast
      from IHAPP(2) left have "e#wr \<in> e#w2' \<otimes>\<^bsub>\<alpha>\<^esub> w3" by (auto intro: cil_cons1)
      moreover from right' IHAPP(1) have "e#w \<in> w1 \<otimes>\<^bsub>\<alpha>\<^esub> e#wr" by (auto intro: cil_cons2)
      ultimately show ?thesis using right' by blast
    qed
  next
    case (right w3') from Cons.hyps[OF _ right(2) Cons.prems(2)] obtain wr where IHAPP: "w \<in> w1 \<otimes>\<^bsub>\<alpha>\<^esub> wr" "wr \<in> w2 \<otimes>\<^bsub>\<alpha>\<^esub> w3'" by blast
    from IHAPP(2) right cil_mon_pl[OF Cons.prems(2)] have "e#wr \<in> w2 \<otimes>\<^bsub>\<alpha>\<^esub> e#w3'" by (auto intro: cil_cons2)
    moreover from IHAPP(1) right cil_mon_pl[OF Cons.prems(2)] have "e#w \<in> w1 \<otimes>\<^bsub>\<alpha>\<^esub> e#wr" by (auto intro: cil_cons2)
    ultimately show ?thesis using right by blast
  qed
qed
    
lemma cil_assoc2: 
  assumes A: "w\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>wr" and B: "wr\<in>w2\<otimes>\<^bsub>\<alpha>\<^esub>w3" 
  shows "\<exists>wl. w\<in>wl\<otimes>\<^bsub>\<alpha>\<^esub>w3 \<and> wl\<in>w1\<otimes>\<^bsub>\<alpha>\<^esub>w2" 
proof -
  from A have A': "w\<in>wr\<otimes>\<^bsub>\<alpha>\<^esub>w1" by (simp add: cil_commute)
  from B have B': "wr\<in>w3\<otimes>\<^bsub>\<alpha>\<^esub>w2" by (simp add: cil_commute)
  from cil_assoc1[OF A' B'] obtain wl where "w \<in> w3 \<otimes>\<^bsub>\<alpha>\<^esub> wl \<and> wl \<in> w2 \<otimes>\<^bsub>\<alpha>\<^esub> w1" by blast
  thus ?thesis by (auto simp add: cil_commute)
qed


\<comment> \<open>Parts of the abstraction can be moved to the operands\<close>
(* FIXME: ?? Something strange is going on with the simplification of \<alpha>\<circ>f and implicit \<eta>-contraction/expansion, hence this lengthy isar proof. Usually, this proof should be a just few lines apply-script !*)
lemma cil_map: "w\<in>w1 \<otimes>\<^bsub>(\<alpha>\<circ>f)\<^esub> w2 \<Longrightarrow> map f w \<in> map f w1 \<otimes>\<^bsub>\<alpha>\<^esub> map f w2" 
proof (induct rule: cil_set_induct_fix\<alpha>)
  case empty thus ?case by auto
next
  case (left e w' w1' w2) 
  have "f e # map f w' \<in> f e # map f w1' \<otimes>\<^bsub>\<alpha>\<^esub> map f w2" proof (rule cil_cons1)
    from left(2) have "fst ((\<alpha>\<circ>f) e) \<inter> mon_pl (map \<alpha> (map f w2)) = {}" by (simp only: map_map[symmetric])
    thus "fst (\<alpha> (f e)) \<inter> mon_pl (map \<alpha> (map f w2)) = {}" by (simp only: o_apply)
  qed (rule left(3))
  thus ?case by simp
next
  case (right e w' w2' w1) 
  have "f e # map f w' \<in> map f w1 \<otimes>\<^bsub>\<alpha>\<^esub> f e # map f w2'" proof (rule cil_cons2)
    from right(2) have "fst ((\<alpha>\<circ>f) e) \<inter> mon_pl (map \<alpha> (map f w1)) = {}" by (simp only: map_map[symmetric])
    thus "fst (\<alpha> (f e)) \<inter> mon_pl (map \<alpha> (map f w1)) = {}" by (simp only: o_apply)
  qed (rule right(3))
  thus ?case by simp
qed



end
