section\<open>Proof Systems\<close>
subsection\<open>Sequent Calculus\<close>

theory SC
imports Formulas "HOL-Library.Multiset"
begin

abbreviation msins ("_, _" [56,56] 56) where "x,M == add_mset x M"  

text\<open>We do not formalize the concept of sequents, only that of sequent calculus derivations.\<close>
inductive SCp :: "'a formula multiset \<Rightarrow> 'a formula multiset \<Rightarrow> bool" ("(_ \<Rightarrow>/ _)" [53] 53) where
BotL: "\<bottom> \<in># \<Gamma> \<Longrightarrow> \<Gamma>\<Rightarrow>\<Delta>" |
Ax: "Atom k \<in># \<Gamma> \<Longrightarrow> Atom k \<in># \<Delta> \<Longrightarrow> \<Gamma>\<Rightarrow>\<Delta>" |
NotL: "\<Gamma> \<Rightarrow> F,\<Delta> \<Longrightarrow> Not F, \<Gamma> \<Rightarrow> \<Delta>" |
NotR: "F,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> Not F, \<Delta>" |
AndL: "F,G,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> And F G, \<Gamma> \<Rightarrow> \<Delta>" |
AndR: "\<lbrakk> \<Gamma> \<Rightarrow> F,\<Delta>; \<Gamma> \<Rightarrow> G,\<Delta> \<rbrakk> \<Longrightarrow> \<Gamma> \<Rightarrow> And F G, \<Delta>" |
OrL: "\<lbrakk> F,\<Gamma> \<Rightarrow> \<Delta>; G,\<Gamma> \<Rightarrow> \<Delta> \<rbrakk> \<Longrightarrow> Or F G, \<Gamma> \<Rightarrow> \<Delta>" |
OrR: "\<Gamma> \<Rightarrow> F,G,\<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> Or F G, \<Delta>" |
ImpL: "\<lbrakk> \<Gamma> \<Rightarrow> F,\<Delta>; G,\<Gamma> \<Rightarrow> \<Delta> \<rbrakk> \<Longrightarrow> Imp F G, \<Gamma> \<Rightarrow> \<Delta>" |
ImpR: "F,\<Gamma> \<Rightarrow> G,\<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> Imp F G, \<Delta>"

text\<open>Many of the proofs here are inspired Troelstra and Schwichtenberg~\cite{troelstra2000basic}.\<close>

lemma
  shows BotL_canonical[intro!]: "\<bottom>,\<Gamma>\<Rightarrow>\<Delta>"
    and Ax_canonical[intro!]: "Atom k,\<Gamma> \<Rightarrow> Atom k,\<Delta>"
  by (meson SCp.intros union_single_eq_member)+
    

lemma lem1: "x \<noteq> y \<Longrightarrow> x, M = y,N \<longleftrightarrow> x \<in># N \<and> M = y,(N - {#x#})"
  by (metis (no_types, lifting) add_eq_conv_ex add_mset_remove_trivial add_mset_remove_trivial_eq)

lemma lem2: "x \<noteq> y \<Longrightarrow> x, M = y, N \<longleftrightarrow> y \<in># M \<and> N = x, (M - {#y#})"
  using lem1 by fastforce

text\<open>This is here to deal with a technical problem: the way the simplifier uses @{thm add_mset_commute} is really suboptimal for the unification of SC rules.\<close>
  
lemma sc_insertion_ordering[simp]:
  "NO_MATCH (I\<^bold>\<rightarrow>J) H \<Longrightarrow> H,F\<^bold>\<rightarrow>G,S = F\<^bold>\<rightarrow>G,H,S"
  "NO_MATCH (I\<^bold>\<rightarrow>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<or>J) H \<Longrightarrow> H,F\<^bold>\<or>G,S = F\<^bold>\<or>G,H,S"
  "NO_MATCH (I\<^bold>\<rightarrow>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<or>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<and>J) H \<Longrightarrow> H,F\<^bold>\<and>G,S = F\<^bold>\<and>G,H,S"
  "NO_MATCH (I\<^bold>\<rightarrow>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<or>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<and>J) H \<Longrightarrow> NO_MATCH (\<^bold>\<not>J) H \<Longrightarrow> H,\<^bold>\<not>G,S = \<^bold>\<not>G,H,S"
  "NO_MATCH (I\<^bold>\<rightarrow>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<or>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<and>J) H \<Longrightarrow> NO_MATCH (\<^bold>\<not>J) H \<Longrightarrow> NO_MATCH (\<bottom>) H \<Longrightarrow> H,\<bottom>,S = \<bottom>,H,S"
  "NO_MATCH (I\<^bold>\<rightarrow>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<or>J) H \<Longrightarrow> NO_MATCH (I\<^bold>\<and>J) H \<Longrightarrow> NO_MATCH (\<^bold>\<not>J) H \<Longrightarrow> NO_MATCH (\<bottom>) H \<Longrightarrow> NO_MATCH (Atom k) H \<Longrightarrow> H,Atom l,S = Atom l,H,S"
  (* I have decided that \<bottom> and atoms should be pulled outwards with the lowest priorities. this may not always be smart. *)
  by simp_all
    
lemma shows
     inR1: "\<Gamma> \<Rightarrow> G, H, \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> H, G, \<Delta>"
 and inL1: "G, H, \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> H, G, \<Gamma> \<Rightarrow> \<Delta>"
 and inR2: "\<Gamma> \<Rightarrow> F, G, H, \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> G, H, F, \<Delta>"
 and inL2: "F, G, H, \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> G, H, F, \<Gamma> \<Rightarrow> \<Delta>" by(simp_all add: add_mset_commute)
lemmas SCp_swap_applies[elim!,intro] = inL1 inL2 inR1 inR2

lemma NotL_inv: "Not F, \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta>"
proof(induction "Not F, \<Gamma>" \<Delta> arbitrary: \<Gamma> rule: SCp.induct)
  case (NotL \<Gamma>' G \<Delta>) thus ?case by(cases "Not F = Not G") (auto intro!: SCp.intros(3-) dest!: multi_member_split simp: lem1 lem2)
qed (auto intro!: SCp.intros(3-) dest!: multi_member_split simp: SCp.intros lem1 lem2)

lemma AndL_inv: "And F G, \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> F,G,\<Gamma> \<Rightarrow> \<Delta>"
proof(induction "And F G, \<Gamma>" \<Delta> arbitrary: \<Gamma> rule: SCp.induct)
  case (AndL F' G' \<Gamma>' \<Delta>) thus ?case 
    by(cases "And F G = And F' G'"; 
       auto intro!: SCp.intros(3-) dest!: multi_member_split simp: lem1 lem2;
       metis add_mset_commute)
qed (auto intro!: SCp.intros(3-) dest!: multi_member_split simp: SCp.intros lem1 lem2 inL2)

lemma OrL_inv: 
  assumes "Or F G, \<Gamma> \<Rightarrow> \<Delta>"
  shows "F,\<Gamma> \<Rightarrow> \<Delta> \<and> G,\<Gamma> \<Rightarrow> \<Delta>"
proof(insert assms, induction "Or F G, \<Gamma>" \<Delta> arbitrary: \<Gamma> rule: SCp.induct)
  case (OrL F' \<Gamma>' \<Delta> G') thus ?case 
    by(cases "Or F G = Or F' G'"; 
       auto intro!: SCp.intros(3-) dest!: multi_member_split simp: lem1 lem2;
       blast)
qed (fastforce intro!: SCp.intros(3-) dest!: multi_member_split simp: SCp.intros lem1 lem2)+

lemma ImpL_inv: 
  assumes "Imp F G, \<Gamma> \<Rightarrow> \<Delta>"
  shows "\<Gamma> \<Rightarrow> F,\<Delta> \<and> G,\<Gamma> \<Rightarrow> \<Delta>"
proof(insert assms, induction "Imp F G, \<Gamma>" \<Delta> arbitrary: \<Gamma> rule: SCp.induct)
  case (ImpL \<Gamma>' F' \<Delta> G') thus ?case 
    by(cases "Or F G = Or F' G'"; (* oops, I didn't pay attention and used the wrong constructor\<dots> doesn't matter! *)
       auto intro!: SCp.intros(3-) dest!: multi_member_split simp: lem1 lem2;
       blast)
qed (fastforce intro!: SCp.intros(3-) dest!: multi_member_split simp: SCp.intros lem1 lem2)+
  
lemma ImpR_inv:
  assumes "\<Gamma> \<Rightarrow> Imp F G,\<Delta>"
  shows "F,\<Gamma> \<Rightarrow> G,\<Delta>"
proof(insert assms, induction \<Gamma> "Imp F G, \<Delta>" arbitrary: \<Delta> rule: SCp.induct)
  case (ImpR  F' \<Gamma> G' \<Delta>') thus ?case 
    by(cases "Or F G = Or F' G'"; 
       auto intro!: SCp.intros(3-) dest!: multi_member_split simp: lem1 lem2;
       blast)
qed (fastforce intro!: SCp.intros(3-) dest!: multi_member_split simp: SCp.intros lem1 lem2)+

lemma AndR_inv:
shows "\<Gamma> \<Rightarrow> And F G, \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> F, \<Delta> \<and> \<Gamma> \<Rightarrow> G, \<Delta>"
proof(induction \<Gamma> "And F G, \<Delta>" arbitrary: \<Delta> rule: SCp.induct)
  case (AndR  \<Gamma> F' \<Delta>' G') thus ?case 
    by(cases "Or F G = Or F' G'"; 
       auto intro!: SCp.intros(3-) dest!: multi_member_split simp: lem1 lem2;
       blast)
qed (fastforce intro!: SCp.intros(3-) dest!: multi_member_split simp: SCp.intros lem1 lem2)+

lemma OrR_inv: "\<Gamma> \<Rightarrow> Or F G, \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> F,G,\<Delta>"
proof(induction \<Gamma> "Or F G, \<Delta>" arbitrary: \<Delta> rule: SCp.induct)
  case (OrR  \<Gamma> F' G' \<Delta>') thus ?case 
    by(cases "Or F G = Or F' G'"; 
       auto intro!: SCp.intros(3-) dest!: multi_member_split simp: lem1 lem2;
       metis add_mset_commute)
qed (fastforce intro!: SCp.intros(3-) dest!: multi_member_split simp: SCp.intros lem1 lem2)+

lemma NotR_inv: "\<Gamma> \<Rightarrow> Not F, \<Delta> \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta>"
proof(induction \<Gamma> "Not F, \<Delta>" arbitrary: \<Delta> rule: SCp.induct)
  case (NotR  G \<Gamma> \<Delta>') thus ?case 
    by(cases "Not F = Not G"; 
       auto intro!: SCp.intros(3-) dest!: multi_member_split simp: lem1 lem2;
       metis add_mset_commute)
qed (fastforce intro!: SCp.intros(3-) dest!: multi_member_split simp: SCp.intros lem1 lem2)+

lemma weakenL: "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta>"
  by(induction rule: SCp.induct) 
    (auto intro!: SCp.intros(3-) intro: SCp.intros(1,2))

lemma weakenR: "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta> "
  by(induction rule: SCp.induct)
    (auto intro!: SCp.intros(3-) intro: SCp.intros(1,2))

lemma weakenL_set: "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> F + \<Gamma> \<Rightarrow> \<Delta>"
  by(induction F; simp add: weakenL) 
lemma weakenR_set: "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> F + \<Delta>"
  by(induction F; simp add: weakenR)

lemma extended_Ax: "\<Gamma> \<inter># \<Delta> \<noteq> {#} \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
proof -
  assume "\<Gamma> \<inter># \<Delta> \<noteq> {#}"
  then obtain W where "W \<in># \<Gamma>" "W \<in># \<Delta>" by force
  then show ?thesis proof(induction W arbitrary: \<Gamma> \<Delta>)
    case (Not W)
    from Not.prems obtain \<Gamma>' \<Delta>' where [simp]: "\<Gamma> = Not W,\<Gamma>'" "\<Delta> = Not W,\<Delta>'" by (metis insert_DiffM)
    have "W \<in># W,\<Gamma>'" "W \<in># W,\<Delta>'" by simp_all
    from Not.IH[OF this] obtain n where "W, \<Gamma>' \<Rightarrow> W, \<Delta>'" by presburger
    hence "Not W, \<Gamma>' \<Rightarrow> Not W, \<Delta>'" using SCp.intros(3,4) add_mset_commute by metis
    thus "\<Gamma> \<Rightarrow> \<Delta>" by auto
  next
    case (And G H)
    from And.prems obtain \<Gamma>' \<Delta>' where [simp]: "\<Gamma> = And G H,\<Gamma>'" "\<Delta> = And G H,\<Delta>'" by (metis insert_DiffM)
    have "G \<in># G, H, \<Gamma>'" "G \<in># G, \<Delta>'" by simp_all
    with And.IH(1) have IH1: "G, H, \<Gamma>' \<Rightarrow> G, \<Delta>'" .
    have "H \<in># G, H, \<Gamma>'" "H \<in># H, \<Delta>'" by simp_all
    with And.IH(2) have IH2: "G, H, \<Gamma>' \<Rightarrow> H, \<Delta>'" .
    from IH1 IH2 have "G, H, \<Gamma>' \<Rightarrow> G, \<Delta>'" "G, H, \<Gamma>' \<Rightarrow> H, \<Delta>'" by fast+
    thus "\<Gamma> \<Rightarrow> \<Delta>" using SCp.intros(5,6) by fastforce
  next
    case (Or G H)
    case (Imp G H)
    text\<open>analogously\<close> (*<*)
  next
    case (Or G H)
    from Or.prems obtain \<Gamma>' \<Delta>' where [simp]: "\<Gamma> = Or G H,\<Gamma>'" "\<Delta> = Or G H,\<Delta>'" by (metis insert_DiffM)
    with Or.IH show ?case using SCp.intros(7,8)[where 'a='a] by fastforce
  next
    case (Imp G H)
    from Imp.prems obtain \<Gamma>' \<Delta>' where [simp]: "\<Gamma> = Imp G H,\<Gamma>'" "\<Delta> = Imp G H,\<Delta>'" by (metis insert_DiffM)
    from Imp.IH have "G, \<Gamma>' \<Rightarrow> G, H, \<Delta>'" "H, G, \<Gamma>' \<Rightarrow> H, \<Delta>'" by simp_all
    thus ?case by(auto intro!: SCp.intros(3-))
  (*>*)
  qed (auto intro: SCp.intros)
qed

lemma Bot_delR: "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>-{#\<bottom>#}"
proof(induction rule: SCp.induct)
  case BotL
  thus ?case by (simp add: SCp.BotL)
next
  case Ax
  thus ?case
    by (metis SCp.Ax diff_union_swap formula.distinct(1) insert_DiffM union_single_eq_member)
next
  case NotL
  thus ?case
    by (metis SCp.NotL diff_single_trivial diff_union_swap2)
next
  case NotR
  thus ?case by(simp add: SCp.NotR)
next
  case AndL
  thus ?case by (simp add: SCp.AndL)
next
  case AndR
  thus ?case
    by (metis SCp.AndR diff_single_trivial diff_union_swap diff_union_swap2 formula.distinct(13))
next
  case OrL
  thus ?case by(simp add: SCp.OrL)
next
  case OrR
  thus ?case
    by (metis SCp.OrR diff_single_trivial diff_union_swap2 formula.distinct(15) insert_iff set_mset_add_mset_insert)
next
  case ImpL
  thus ?case by (metis SCp.ImpL diff_single_trivial diff_union_swap2)
next
  case ImpR
  thus ?case
    by (metis SCp.ImpR diff_single_trivial diff_union_swap diff_union_swap2 formula.distinct(17))
qed
corollary Bot_delR_simp: "\<Gamma> \<Rightarrow> \<bottom>,\<Delta> = \<Gamma> \<Rightarrow> \<Delta>"
  using Bot_delR weakenR by fastforce

end
