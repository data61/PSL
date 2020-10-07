theory SC_Depth
imports SC
begin
  
text\<open>
Many textbook arguments about SC use the depth of the derivation tree as basis for inductions.
We had originally thought that this is mandatory for the proof of contraction,
but found out it is not.
It remains unclear to us whether there is any proof on SC that requires an argument using depth.
\<close>
text\<open>
We keep our formalization of SC with depth for didactic reasons:
we think that arguments about depth do not need much meta-explanation,
but structural induction and rule induction usually need extra explanation
for students unfamiliar with Isabelle/HOL.
They are also a lot harder to execute.
We dare the reader to write down (a few of) the cases for, e.g. \<open>AndL_inv'\<close>, by hand.
\<close>

(* Warning: This theory may have name collisions with SC.thy\<dots> *)

inductive SCc :: "'a formula multiset \<Rightarrow> 'a formula multiset \<Rightarrow> nat \<Rightarrow> bool" ("((_ \<Rightarrow>/ _) \<down> _)" [53,53] 53) where
BotL: "\<bottom> \<in># \<Gamma> \<Longrightarrow> \<Gamma>\<Rightarrow>\<Delta> \<down> Suc n" |
Ax: "Atom k \<in># \<Gamma> \<Longrightarrow> Atom k \<in># \<Delta> \<Longrightarrow> \<Gamma>\<Rightarrow>\<Delta> \<down> Suc n" |
NotL: "\<Gamma> \<Rightarrow> F,\<Delta> \<down> n \<Longrightarrow> Not F, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n" |
NotR: "F,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> Not F, \<Delta> \<down> Suc n" |
AndL: "F,G,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> And F G, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n" |
AndR: "\<lbrakk> \<Gamma> \<Rightarrow> F,\<Delta> \<down> n; \<Gamma> \<Rightarrow> G,\<Delta> \<down> n \<rbrakk> \<Longrightarrow> \<Gamma> \<Rightarrow> And F G, \<Delta> \<down> Suc n" |
OrL: "\<lbrakk> F,\<Gamma> \<Rightarrow> \<Delta> \<down> n; G,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<rbrakk> \<Longrightarrow> Or F G, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n" |
OrR: "\<Gamma> \<Rightarrow> F,G,\<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> Or F G, \<Delta> \<down> Suc n" |
ImpL: "\<lbrakk> \<Gamma> \<Rightarrow> F,\<Delta> \<down> n; G,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<rbrakk> \<Longrightarrow> Imp F G, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n" |
ImpR: "F,\<Gamma> \<Rightarrow> G,\<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> Imp F G, \<Delta> \<down> Suc n"

lemma
  shows BotL_canonical'[intro!]: "\<bottom>,\<Gamma>\<Rightarrow>\<Delta> \<down> Suc n"
    and Ax_canonical'[intro!]: "Atom k,\<Gamma> \<Rightarrow> Atom k,\<Delta> \<down> Suc n"
  by (meson SCc.intros union_single_eq_member)+
    
lemma deeper: "\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta> \<down> n + m"
  by(induction rule: SCc.induct; insert SCc.intros; auto) 
lemma deeper_suc: "\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n"
  (* this version is actually required more often. It can be declared as an elim!, but I want to make its usage explicit *)
  thm deeper[unfolded Suc_eq_plus1[symmetric]]
  by(drule deeper[where m=1]) simp
    
text\<open>The equivalence is obvious.\<close>
theorem SC_SCp_eq:
  fixes \<Gamma> \<Delta> :: "'a formula multiset"
  shows "(\<exists>n. \<Gamma> \<Rightarrow> \<Delta> \<down> n) \<longleftrightarrow> \<Gamma> \<Rightarrow> \<Delta>" (is "?c \<longleftrightarrow> ?p")
proof
  assume ?c then guess n ..
  thus ?p by(induction rule: SCc.induct; simp add: SCp.intros)
next
  have deeper_max: "\<Gamma> \<Rightarrow> \<Delta> \<down> max m n" "\<Gamma> \<Rightarrow> \<Delta> \<down> max n m" if "\<Gamma> \<Rightarrow> \<Delta> \<down> n" for n m and \<Gamma> \<Delta> :: "'a formula multiset"
  proof -
    have "n \<le> m \<Longrightarrow> \<exists>k. m = n + k" by presburger
    with that[THEN deeper] that
    show "\<Gamma> \<Rightarrow> \<Delta> \<down> max n m" unfolding max_def by clarsimp
    thus "\<Gamma> \<Rightarrow> \<Delta> \<down> max m n" by (simp add: max.commute)
  qed
  assume ?p thus ?c by(induction rule: SCp.induct)
    (insert SCc.intros[where 'a='a] deeper_max; metis)+
qed

(* it makes a difference whether we say Ax is 0 or any: with Ax \<down> 0 we could not prove the deepening rules.
   Also, it is important to allow only atoms in Ax, otherwise the inv-rules are not depth preserving.
  Making Ax/BotL start from \<ge>1 saves proving the base-cases twice
 *)
lemma no_0_SC[dest!]: "\<Gamma> \<Rightarrow> \<Delta> \<down> 0 \<Longrightarrow> False"
  by(cases rule: SCc.cases[of \<Gamma> \<Delta> 0]) assumption
    

lemma inR1': "\<Gamma> \<Rightarrow> G, H, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> H, G, \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inL1': "G, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> H, G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inR2': "\<Gamma> \<Rightarrow> F, G, H, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> G, H, F, \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inL2': "F, G, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> G, H, F, \<Gamma> \<Rightarrow> \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inR3': "\<Gamma> \<Rightarrow> F, G, H, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> H, F, G, \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inR4': "\<Gamma> \<Rightarrow> F, G, H, I, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> H, I, F, G, \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inL3': "F, G, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> H, F, G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" by(simp add: add_mset_commute)
lemma inL4': "F, G, H, I, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> H, I, F, G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" by(simp add: add_mset_commute)
lemmas SC_swap_applies[intro,elim!] = inL1' inL2' inL3' inL4' inR1' inR2' inR3' inR4'
  (* these are here because they can be used for more careful reasoning with intro *)

lemma "Atom C \<^bold>\<rightarrow> Atom D \<^bold>\<rightarrow> Atom E,
       Atom k \<^bold>\<rightarrow> Atom C \<^bold>\<and> Atom D, 
       Atom k, {#} 
\<Rightarrow> {# Atom E #} \<down> Suc (Suc (Suc (Suc (Suc 0))))"
  by(auto intro!: SCc.intros(3-) intro: SCc.intros(1,2))

lemma Bot_delR': "\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>-{#\<bottom>#} \<down> n"
proof(induction rule: SCc.induct) 
  case BotL thus ?case by(rule SCc.BotL; simp) (* SC.BotL refers to SC.SCp.BotL. Even more interestingly, there used to be a SCc.SC.BotL (which was not reffered to). I'll just leave this here and see how long till someone breaks it. *)
next case (Ax k) thus ?case by(intro SCc.Ax[of k]; simp; metis diff_single_trivial formula.distinct(1) insert_DiffM lem1)
next case NotL thus ?case using SCc.NotL by (metis add_mset_remove_trivial diff_single_trivial diff_union_swap insert_DiffM)
next case NotR thus ?case using SCc.NotR by (metis diff_union_swap formula.distinct(11))
next case AndR thus ?case using SCc.AndR by (metis diff_single_trivial diff_union_swap diff_union_swap2 formula.distinct(13))
next case OrR thus ?case using SCc.OrR by (metis diff_single_trivial diff_union_swap2 formula.distinct(15) insert_iff set_mset_add_mset_insert)
next case ImpL thus ?case using SCc.ImpL by (metis diff_single_trivial diff_union_swap2)
next case ImpR thus ?case using SCc.ImpR by (metis diff_single_trivial diff_union_swap diff_union_swap2 formula.distinct(17))
qed (simp_all add: SCc.intros)
  
lemma NotL_inv': "Not F, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta>  \<down> n"
proof(induction "Not F, \<Gamma>" \<Delta> n arbitrary: \<Gamma> rule: SCc.induct)
  case (NotL \<Gamma>' G \<Delta> n) thus ?case by(cases "Not F = Not G")
    (auto intro!: SCc.intros(3-) dest!: multi_member_split simp: lem1 lem2 deeper_suc)
qed (auto intro!: SCc.intros(3-) dest!: multi_member_split simp: SCp.intros lem1 lem2)

lemma AndL_inv': "And F G, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> F,G,\<Gamma> \<Rightarrow> \<Delta> \<down> n"
proof(induction "And F G, \<Gamma>" \<Delta> n arbitrary: \<Gamma> rule: SCc.induct)
  case (AndL F' G' \<Gamma>' \<Delta>) thus ?case 
    by(cases "And F G = And F' G'"; 
       auto intro!: SCc.intros(3-) dest!: multi_member_split simp: lem1 lem2 deeper_suc;
       metis add_mset_commute)
qed (auto intro!: SCc.intros(3-) dest!: multi_member_split simp: SCc.intros lem1 lem2 inL2')

lemma OrL_inv': 
  assumes "Or F G, \<Gamma> \<Rightarrow> \<Delta> \<down> n"
  shows "F,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<and> G,\<Gamma> \<Rightarrow> \<Delta> \<down> n"
proof(insert assms, induction "Or F G, \<Gamma>" \<Delta> n arbitrary: \<Gamma> rule: SCc.induct)
  case (OrL F' \<Gamma>' \<Delta> n G') thus ?case 
    by(cases "Or F G = Or F' G'"; 
       auto intro!: SCc.intros(3-) dest!: multi_member_split simp: lem1 lem2 deeper_suc;
       blast)
qed (fastforce intro!: SCc.intros(3-) dest!: multi_member_split simp: SCc.intros lem1 lem2)+

lemma ImpL_inv': 
  assumes "Imp F G, \<Gamma> \<Rightarrow> \<Delta> \<down> n"
  shows "\<Gamma> \<Rightarrow> F,\<Delta> \<down> n \<and> G,\<Gamma> \<Rightarrow> \<Delta> \<down> n"
proof(insert assms, induction "Imp F G, \<Gamma>" \<Delta> n arbitrary: \<Gamma> rule: SCc.induct)
  case (ImpL \<Gamma>' F' \<Delta> n G') thus ?case 
    by(cases "Or F G = Or F' G'"; (* oops, I didn't pay attention and used the wrong constructor\<dots> doesn't matter! *)
       auto intro!: SCc.intros(3-) dest!: multi_member_split simp: lem1 lem2 deeper_suc;
       blast)
qed (fastforce intro!: SCc.intros(3-) dest!: multi_member_split simp: SCc.intros lem1 lem2)+
  
lemma ImpR_inv':
  assumes "\<Gamma> \<Rightarrow> Imp F G,\<Delta> \<down> n"
  shows "F,\<Gamma> \<Rightarrow> G,\<Delta> \<down> n"
proof(insert assms, induction \<Gamma> "Imp F G, \<Delta>" n arbitrary: \<Delta> rule: SCc.induct)
  case (ImpR  F' \<Gamma> G' \<Delta>') thus ?case 
    by(cases "Or F G = Or F' G'"; 
       auto intro!: SCc.intros(3-) dest!: multi_member_split simp: lem1 lem2 deeper_suc;
       blast)
qed (fastforce intro!: SCc.intros(3-) dest!: multi_member_split simp: SCc.intros lem1 lem2)+

lemma AndR_inv':
shows "\<Gamma> \<Rightarrow> And F G, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> F, \<Delta> \<down> n \<and> \<Gamma> \<Rightarrow> G, \<Delta> \<down> n"
proof(induction \<Gamma> "And F G, \<Delta>" n arbitrary: \<Delta> rule: SCc.induct)
  case (AndR  \<Gamma> F' \<Delta>' n G') thus ?case 
    by(cases "Or F G = Or F' G'"; 
       auto intro!: SCc.intros(3-) dest!: multi_member_split simp: lem1 lem2 deeper_suc;
       blast)
qed (fastforce intro!: SCc.intros(3-) dest!: multi_member_split simp: SCc.intros lem1 lem2)+

lemma OrR_inv': "\<Gamma> \<Rightarrow> Or F G, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> F,G,\<Delta> \<down> n"
proof(induction \<Gamma> "Or F G, \<Delta>" n arbitrary: \<Delta> rule: SCc.induct)
  case (OrR  \<Gamma> F' G' \<Delta>') thus ?case 
    by(cases "Or F G = Or F' G'"; 
       auto intro!: SCc.intros(3-) dest!: multi_member_split simp: lem1 lem2 deeper_suc;
       metis add_mset_commute)
qed (fastforce intro!: SCc.intros(3-) dest!: multi_member_split simp: SCc.intros lem1 lem2)+

lemma NotR_inv': "\<Gamma> \<Rightarrow> Not F, \<Delta> \<down> n \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta> \<down> n"
proof(induction \<Gamma> "Not F, \<Delta>" n arbitrary: \<Delta> rule: SCc.induct)
  case (NotR  G \<Gamma> \<Delta>') thus ?case 
    by(cases "Not F = Not G"; 
       auto intro!: SCc.intros(3-) dest!: multi_member_split simp: lem1 lem2 deeper_suc;
       metis add_mset_commute)
qed (fastforce intro!: SCc.intros(3-) dest!: multi_member_split simp: SCc.intros lem1 lem2)+

lemma weakenL': "\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta>  \<down> n"
  by(induction rule: SCc.induct) 
    (auto intro!: SCc.intros(3-) intro: SCc.intros(1,2))

lemma weakenR': "\<Gamma> \<Rightarrow> \<Delta>  \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta>  \<down> n"
  by(induction rule: SCc.induct)
    (auto intro!: SCc.intros(3-) intro: SCc.intros(1,2))

lemma contract':
  "(F,F,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta> \<down> n) \<and> (\<Gamma> \<Rightarrow> F,F,\<Delta> \<down> n \<longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta> \<down> n)"
proof(induction n arbitrary: F \<Gamma> \<Delta>)
  case (Suc n)
  hence IH: "F, F, \<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> F, \<Gamma> \<Rightarrow> \<Delta> \<down> n" "\<Gamma> \<Rightarrow> F, F, \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> F, \<Delta> \<down> n" for F :: "'a formula" and \<Gamma> \<Delta> by blast+
  show ?case proof(intro conjI allI impI, goal_cases)
    case 1
    let ?ffs = "\<lambda>\<Gamma>. \<Gamma> - {# F #} - {# F #}"
    from 1 show ?case proof(insert 1; cases rule: SCc.cases[of "F,F,\<Gamma>" \<Delta> "Suc n"])
      case (NotL  \<Gamma>' G)
      show ?thesis
      proof(cases)
        assume e: "F = \<^bold>\<not>G"
        with NotL have \<Gamma>': "\<Gamma>' = \<^bold>\<not>G, \<Gamma>" by simp
        from NotL_inv' NotL(2) have "\<Gamma> \<Rightarrow> G, G, \<Delta> \<down> n" unfolding \<Gamma>' .
        with IH(2) have "\<Gamma> \<Rightarrow> G, \<Delta> \<down> n" .
        with SCc.NotL show ?thesis unfolding e .
      next
        assume e: "F \<noteq> \<^bold>\<not>G"
        have ?thesis
          using NotL(2) IH(1)[of F "?ffs \<Gamma>'" "G, \<Delta>"] SCc.NotL[of "F, \<Gamma>' - {# F #} - {# F #}" G \<Delta> n]
          using e NotL(1) by (metis (no_types, lifting) insert_DiffM lem2)
        from e NotL(1) have \<Gamma>: "\<Gamma> = \<^bold>\<not> G, ?ffs \<Gamma>'" by (meson lem1)
        with NotL(1) have \<Gamma>': "F,F,?ffs \<Gamma>' = \<Gamma>'" by simp
        show ?thesis using NotL(2) IH(1)[of F "?ffs \<Gamma>'" "G, \<Delta>"] SCc.NotL[of "F, ?ffs \<Gamma>'" G \<Delta> n] \<open>F, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n\<close> by blast
      qed
    next
      case (AndL G H \<Gamma>') show ?thesis proof cases
        assume e: "F = And G H"
        with AndL(1) have \<Gamma>': "\<Gamma>' = And G H, \<Gamma>" by simp
        have "G \<^bold>\<and> H, G, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" using AndL(2) unfolding \<Gamma>' by auto
        hence "G, H, G, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" by(rule AndL_inv')
        hence "G, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" using IH(1) by (metis inL1' inL3')
        thus "F, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n" using e SCc.AndL by simp
      next
        assume ne: "F \<noteq> And G H"
        with AndL(1) have \<Gamma>: "\<Gamma> = And G H, ?ffs \<Gamma>'" by (metis (no_types, lifting) diff_diff_add lem2)
        have "F, F, G, H, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" using AndL(2) using \<Gamma> inL4' local.AndL(1) by auto
        hence "G, H, F, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" using IH(1) inL2 by blast
        thus ?thesis using SCc.AndL unfolding \<Gamma> using inL1 by blast
      qed
    next
      case (OrL G \<Gamma>' H) show ?thesis proof cases
        assume e: "F = Or G H"
        with OrL(1) have \<Gamma>': "\<Gamma>' = Or G H, \<Gamma>" by simp
        have "Or G H, G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" "Or G H, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" using OrL(2,3) unfolding \<Gamma>' by simp_all
        hence "G, G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" "H, H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" using OrL_inv' by blast+
        hence "G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" "H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" using IH(1) by presburger+
        thus "F, \<Gamma> \<Rightarrow> \<Delta> \<down> Suc n" unfolding e using SCc.OrL by blast
      next
        assume ne: "F \<noteq> Or G H"
        with OrL(1) have \<Gamma>: "\<Gamma> = Or G H, ?ffs \<Gamma>'" by (metis (no_types, lifting) diff_diff_add lem2)
        have "F, F, G, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" "F, F, H,?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" using OrL \<Gamma> by auto
        hence "G, F, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" "H, F, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" using IH(1) by(metis add_mset_commute)+
        thus ?thesis using SCc.OrL unfolding \<Gamma> by auto
      qed
    next
      case (ImpL \<Gamma>' G H) show ?thesis proof cases
        assume e: "F = Imp G H"
        with ImpL(1) have \<Gamma>': "\<Gamma>' = Imp G H, \<Gamma>" by simp
        have "H, \<Gamma> \<Rightarrow> \<Delta> \<down> n" "\<Gamma> \<Rightarrow> G,\<Delta> \<down> n" using IH ImpL_inv' ImpL(2,3) unfolding \<Gamma>'
          by (metis add_mset_commute)+
        thus ?thesis unfolding e using SCc.ImpL[where 'a='a] by simp
      next
        assume ne: "F \<noteq> Imp G H"
        with ImpL(1) have \<Gamma>: "\<Gamma> = Imp G H, ?ffs \<Gamma>'" by (metis (no_types, lifting) diff_diff_add lem2)
        have "F, F, ?ffs \<Gamma>' \<Rightarrow> G, \<Delta> \<down> n" "F, F, H, ?ffs \<Gamma>' \<Rightarrow> \<Delta> \<down> n" using ImpL \<Gamma> by auto
        thus ?thesis using SCc.ImpL IH unfolding \<Gamma> by (metis inL1')
      qed
    next
      case ImpR thus ?thesis by (simp add: IH(1) SCc.intros(10) add_mset_commute)
    next
      case (NotR G \<Delta>') thus ?thesis using IH(1) by (simp add: SCc.NotR add_mset_commute)
    qed (auto intro: IH SCc.intros(1,2) intro!: SCc.intros(3-10))
  next
    case 2
    let ?ffs = "\<lambda>\<Gamma>. \<Gamma> - {# F #} - {# F #}"
    have not_principal[dest]:
      "\<lbrakk>F \<noteq> f G H; F, F, \<Delta> = f G H, \<Delta>'\<rbrakk> \<Longrightarrow> \<Delta> = f G H, ?ffs \<Delta>' \<and> F, F, ?ffs \<Delta>' = \<Delta>'" for f G H \<Delta>' proof(intro conjI, goal_cases)
        case 2
        from 2 have "F \<in># \<Delta>'" by(blast dest: lem1[THEN iffD1])
        then obtain \<Delta>'' where \<Delta>': "\<Delta>' = F,\<Delta>''"  by (metis insert_DiffM)
        with 2(2) have "F, \<Delta> = f G H, \<Delta>''" by(simp add: add_mset_commute)
        hence "F \<in># \<Delta>''" using 2(1) by(blast dest: lem1[THEN iffD1])
        then obtain \<Delta>''' where \<Delta>'': "\<Delta>'' = F,\<Delta>'''" by (metis insert_DiffM)
        show ?case unfolding \<Delta>' \<Delta>'' by simp
        case 1 show ?case using 1(2) unfolding \<Delta>' \<Delta>'' by(simp add: add_mset_commute)
      qed
    have principal[dest]: "F, F, \<Delta> = f G H, \<Delta>' \<Longrightarrow> F = f G H \<Longrightarrow> \<Delta>' = f G H, \<Delta>" for f G H \<Delta>' by simp
    from 2 show ?case proof(cases rule: SCc.cases[of \<Gamma> "F,F,\<Delta>" "Suc n"])
      case (ImpR G H \<Delta>') thus ?thesis proof cases
        assume e[simp]: "F = Imp G H"
        with ImpR(1) have \<Delta>'[simp]: "\<Delta>' = Imp G H, \<Delta>" by simp
        have "G, \<Gamma> \<Rightarrow> Imp G H, H, \<Delta> \<down> n" using ImpR(2) by simp
        hence "G, G, \<Gamma> \<Rightarrow> H, H, \<Delta> \<down> n" by(rule ImpR_inv')
        hence "G, \<Gamma> \<Rightarrow> H, \<Delta> \<down> n" using IH by fast
        thus "\<Gamma> \<Rightarrow> F, \<Delta> \<down> Suc n" using SCc.ImpR by simp
      next
        assume a: "F \<noteq> Imp G H"
        with ImpR(1) have \<Delta>: "\<Delta> = Imp G H, ?ffs \<Delta>'" by (metis (no_types, lifting) diff_diff_add lem2)
        have "G,\<Gamma> \<Rightarrow> F, F, H, ?ffs \<Delta>' \<down> n" using ImpR \<Delta> by fastforce
        thus ?thesis using SCc.ImpR IH unfolding \<Delta> by (metis inR1')
      qed
    next
      case (AndR G \<Delta>' H) thus ?thesis proof(cases "F = And G H")
        case True thus ?thesis using AndR by(auto intro!: SCc.intros(3-) dest!: AndR_inv' intro: IH)
      next
        case False 
        hence e: "\<Delta> = And G H, ?ffs \<Delta>'" using AndR(1) using diff_diff_add lem2 by blast
        hence "G \<^bold>\<and> H, F, F, ?ffs \<Delta>' = G \<^bold>\<and> H, \<Delta>'" using AndR(1) by simp
        hence "\<Gamma> \<Rightarrow> F, F, G, ?ffs \<Delta>' \<down> n" "\<Gamma> \<Rightarrow> F, F, H, ?ffs \<Delta>' \<down> n" using AndR(2,3) using add_left_imp_eq inR2 by fastforce+
        hence "\<Gamma> \<Rightarrow> G, F, ?ffs \<Delta>' \<down> n" "\<Gamma> \<Rightarrow> H, F, ?ffs \<Delta>' \<down> n" using IH(2) by blast+
        thus ?thesis unfolding e by(intro SCc.AndR[THEN inR1'])
      qed
    next
    case (OrR G H \<Delta>') thus ?thesis proof cases
      assume a: "F = Or G H" 
      hence \<Delta>': "\<Delta>' = G \<^bold>\<or> H, \<Delta>" using OrR(1) by(intro principal)
      hence "\<Gamma> \<Rightarrow> G, H, G, H, \<Delta> \<down> n" using inR3'[THEN OrR_inv'] OrR(2) by auto
      hence "\<Gamma> \<Rightarrow> H, G, \<Delta> \<down> n" using IH(2)[of \<Gamma> G "H,H,\<Delta>"] IH(2)[of \<Gamma> H "G,\<Delta>"]
        unfolding add_ac(3)[of "{#H#}" "{#G#}"] using inR2  by blast
      hence "\<Gamma> \<Rightarrow> G, H, \<Delta> \<down> n" by(elim SC_swap_applies)
    thus ?thesis unfolding a by (simp add: SCc.OrR)
    next
      assume a: "F \<noteq> Or G H"
      with not_principal have np: "\<Delta> = G \<^bold>\<or> H, ?ffs \<Delta>' \<and> F, F, ?ffs \<Delta>' = \<Delta>'" using OrR(1) .
      with OrR(2) have "\<Gamma> \<Rightarrow> G, H, F, ?ffs \<Delta>' \<down> n" using IH(2) by (metis inR2' inR4')
      hence "\<Gamma> \<Rightarrow> F, G \<^bold>\<or> H, ?ffs \<Delta>' \<down> Suc n" by(intro SCc.OrR[THEN inR1'])
      thus ?thesis using np by simp
    qed
    next
      case (NotR G \<Delta>') thus ?thesis proof(cases "F = Not G") 
        case True 
        with principal NotR(1) have "\<Delta>' = \<^bold>\<not> G, \<Delta>" .
        with NotR_inv' NotR(2) have "G, G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" by blast
        with IH(1) have "G, \<Gamma> \<Rightarrow> \<Delta> \<down> n" .
        thus "\<Gamma> \<Rightarrow> F, \<Delta> \<down> Suc n" unfolding True by(intro SCc.NotR)
      next
        case False 
        with not_principal have np: "\<Delta> = \<^bold>\<not> G, \<Delta>' - (F, {#F#}) \<and> F, F, \<Delta>' - (F, {#F#}) = \<Delta>'" using NotR(1) by auto
        hence "G, \<Gamma> \<Rightarrow> F, F, ?ffs \<Delta>' \<down> n" using NotR(2) by simp
        hence "G, \<Gamma> \<Rightarrow> F, ?ffs \<Delta>' \<down> n" by(elim IH(2))
        thus ?thesis using np SCc.NotR inR1 by auto
      qed
    next
      case BotL thus ?thesis by(elim SCc.BotL)
    next
      case (Ax k) thus ?thesis by(intro SCc.Ax[where k=k]) simp_all
    next
      case NotL thus ?thesis by (simp add: SCc.NotL Suc.IH add_mset_commute)
    next
      case AndL thus ?thesis using SCc.AndL Suc.IH by blast
    next
      case OrL thus ?thesis using SCc.OrL Suc.IH by blast
    next
      case ImpL thus ?thesis by (metis SCc.ImpL Suc.IH add_mset_commute)
    qed
  qed
qed blast

(* depth for cut? *)
lemma Cut_Atom_depth: "Atom k,\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> \<Gamma> \<Rightarrow> Atom k,\<Delta> \<down> m \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta> \<down> n + m"
proof(induction "Atom k,\<Gamma>" "\<Delta>" n arbitrary: \<Gamma> m rule: SCc.induct)
  case (BotL \<Delta>)
  hence "\<bottom> \<in># \<Gamma>" by simp
  thus ?case using SCc.BotL  by auto
next
  case (Ax l \<Delta>)
  show ?case proof cases
    assume "l = k"
    with \<open>Atom l \<in># \<Delta>\<close> obtain \<Delta>' where "\<Delta> = Atom k, \<Delta>'" by (meson multi_member_split)
    with \<open>\<Gamma> \<Rightarrow> Atom k, \<Delta> \<down> m\<close> have "\<Gamma> \<Rightarrow> \<Delta> \<down> m" using contract' by blast
    thus ?thesis by (metis add.commute deeper)
  next
    assume "l \<noteq> k"
    with \<open>Atom l \<in># Atom k, \<Gamma>\<close> have "Atom l \<in># \<Gamma>" by simp
    with \<open>Atom l \<in># \<Delta>\<close> show ?thesis using SCc.Ax[of l] by simp
  qed
next
  case (NotL \<Gamma> F \<Delta>)
  obtain \<Gamma>' where \<Gamma>: "\<Gamma> = Not F, \<Gamma>'" by (meson NotL.hyps(3) add_eq_conv_ex formula.simps(9))
  show ?case unfolding \<Gamma>
    apply(unfold plus_nat.add_Suc)
    apply(intro SCc.NotL)
    apply(intro NotL.hyps (* IH *))
     subgoal using NotL \<Gamma> by (simp add: lem2)
    subgoal using \<Gamma> NotL.prems NotL_inv' by blast
  done
next
  case (NotR F \<Delta>)
  then show ?case by(auto intro!: SCc.NotR dest!: NotR_inv')
next
  case (AndL F G \<Gamma> \<Delta>)
  obtain \<Gamma>' where \<Gamma>: "\<Gamma> = And F G, \<Gamma>'" by (metis AndL.hyps(3) add_eq_conv_diff formula.distinct(5))
  show ?case unfolding \<Gamma>
    apply(unfold plus_nat.add_Suc)
    apply(intro SCc.AndL)
    apply(intro AndL.hyps (* IH *))
     subgoal using AndL \<Gamma> by (simp add: lem2)
    subgoal using \<Gamma> AndL.prems AndL_inv' by blast
  done
next
  case (AndR F \<Delta> G)
  then show ?case
    using AndR_inv' SCc.AndR by (metis add_Suc inR1')
next
  case (OrL F \<Gamma>' \<Delta> n G)
  obtain \<Gamma>'' where \<Gamma>: "\<Gamma> = Or F G, \<Gamma>''" by (meson OrL.hyps(5) add_eq_conv_ex formula.simps(13))
  have ihm: "F, \<Gamma>' = Atom k, F, \<Gamma>''" "G, \<Gamma>' = Atom k, G, \<Gamma>''" using OrL \<Gamma>  by (simp_all add: lem2)
  show ?case unfolding \<Gamma>
    apply(unfold plus_nat.add_Suc)
    apply(intro SCc.OrL OrL.hyps(2)[OF ihm(1)] OrL.hyps(4)[OF ihm(2)])
     subgoal using \<Gamma> OrL.prems OrL_inv' by blast
    subgoal using \<Gamma> OrL.prems OrL_inv' by blast
  done
next
  case (OrR F G \<Delta>)
  then show ?case by(auto intro!: SCc.intros(3-) dest!: OrR_inv')
next
  case (ImpL \<Gamma>' F \<Delta> n G)
  obtain \<Gamma>'' where \<Gamma>: "\<Gamma> = Imp F G, \<Gamma>''" by (metis ImpL.hyps(5) add_eq_conv_ex formula.simps)
  show ?case unfolding \<Gamma>
    apply(unfold plus_nat.add_Suc)
    apply(intro SCc.ImpL ImpL.hyps(2) ImpL.hyps(4))
       subgoal using ImpL \<Gamma> by (simp add: lem2)
      subgoal using \<Gamma> ImpL.prems by(auto dest!: ImpL_inv')
     subgoal using ImpL \<Gamma> by (simp add: lem2)
    subgoal using \<Gamma> ImpL.prems ImpL_inv' by blast
  done
next
  case (ImpR F G \<Delta>)
  then show ?case by (auto dest!: ImpR_inv' intro!: SCc.ImpR)
qed
primrec cut_bound :: "nat \<Rightarrow> nat \<Rightarrow> 'a formula \<Rightarrow> nat" where
  "cut_bound n m (Atom _) = m + n" |
  "cut_bound n m Bot = n" |
  "cut_bound n m (Not F) = cut_bound m n F" |
  "cut_bound n m (And F G) = cut_bound n (cut_bound n m F) G" |
  "cut_bound n m (Or F G) = cut_bound (cut_bound n m F) m G" |
  "cut_bound n m (Imp F G) = cut_bound (cut_bound m n F) m G"
theorem cut_bound: "\<Gamma> \<Rightarrow> F,\<Delta> \<down> n \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta>  \<down> m \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta> \<down> cut_bound n m F"
proof(induction F arbitrary: \<Gamma> \<Delta> n m)
  case (Atom k) thus ?case using Cut_Atom_depth by simp fast
next
  case Bot thus ?case using Bot_delR' by fastforce 
next
  case Not from Not.prems show ?case by(auto dest!: NotL_inv' NotR_inv' intro!: Not.IH elim!: weakenL)
next
  case (And F G) from And.prems show ?case by(auto dest!: AndL_inv' AndR_inv' intro!: And.IH elim!: weakenR' weakenL')
next
  case (Or F G) from Or.prems show ?case by(auto dest: OrL_inv' OrR_inv' intro!: Or.IH elim!:  weakenR' weakenL')
next
  case (Imp F G)
  from ImpR_inv' \<open>\<Gamma> \<Rightarrow> F \<^bold>\<rightarrow> G, \<Delta> \<down> n\<close> have R: "F, \<Gamma> \<Rightarrow> G, \<Delta> \<down> n" by blast
  from ImpL_inv' \<open>F \<^bold>\<rightarrow> G, \<Gamma> \<Rightarrow> \<Delta> \<down> m\<close> have L: "\<Gamma> \<Rightarrow> F, \<Delta> \<down> m" "G, \<Gamma> \<Rightarrow> \<Delta> \<down> m" by blast+
  from L(1) have "\<Gamma> \<Rightarrow> F, G, \<Delta> \<down> m" using weakenR' by blast
  from Imp.IH(1)[OF this R] have "\<Gamma> \<Rightarrow> G, \<Delta> \<down> cut_bound m n F" .
  from Imp.IH(2)[OF this L(2)] have "\<Gamma> \<Rightarrow> \<Delta> \<down> cut_bound (cut_bound m n F) m G" .
  thus "\<Gamma> \<Rightarrow> \<Delta> \<down> cut_bound n m (F \<^bold>\<rightarrow> G)" by simp
qed
  
context begin
private primrec cut_bound' :: "nat \<Rightarrow> 'a formula \<Rightarrow> nat" where
  "cut_bound' n (Atom _) = 2*n" |
  "cut_bound' n Bot = n" |
  "cut_bound' n (Not F) = cut_bound' n F" |
  "cut_bound' n (And F G) = cut_bound' (cut_bound' n F) G" |
  "cut_bound' n (Or F G) = cut_bound' (cut_bound' n F) G" |
  "cut_bound' n (Imp F G) = cut_bound' (cut_bound' n F) G"
  
private lemma cut_bound'_mono: "a \<le> b \<Longrightarrow> cut_bound' a F \<le> cut_bound' b F"
  by(induction F arbitrary: a b; simp)
    
private lemma cut_bound_mono: "a \<le> c \<Longrightarrow> b \<le> d \<Longrightarrow> cut_bound a b F \<le> cut_bound c d F"
  by(induction F arbitrary: a b c d; simp)
    
private lemma cut_bound_max: "max n (cut_bound' (max n m) F) = cut_bound' (max n m) F"
  by(induction F arbitrary: n m; simp; metis)
private lemma cut_bound_max': "max n (cut_bound' n F) = cut_bound' n F"
  by(induction F arbitrary: n ; simp; metis max.assoc)
    
private lemma cut_bound_': "cut_bound n m F \<le> cut_bound' (max n m) F"
proof(induction F arbitrary: n m)
  case (Not F)
  then show ?case by simp (metis max.commute)
next
  case (And F1 F2)
  from And.IH(1) have 1: "cut_bound n (cut_bound n m F1) F2 \<le> cut_bound n (cut_bound' (max n m) F1) F2" 
    by(rule cut_bound_mono[OF order.refl])
  also from And.IH(2) have "\<dots> \<le> cut_bound' (max n (cut_bound' (max n m) F1)) F2" by simp
  also have "\<dots> = cut_bound' (cut_bound' (max n m) F1) F2" by (simp add: cut_bound_max)
  finally show ?case by simp
next
  case (Or F1 F2)
  from Or.IH(1) have 1: "cut_bound (cut_bound n m F1) m F2 \<le> cut_bound (cut_bound' (max n m) F1) m F2" 
    by(rule cut_bound_mono[OF _ order.refl])
  also from Or.IH(2)[of "cut_bound' (max n m) F1"] have "\<dots> \<le> cut_bound' (max (cut_bound' (max n m) F1) m) F2" by simp
  also have "\<dots> = cut_bound' (cut_bound' (max n m) F1) F2" by (simp add: cut_bound_max max.commute)
  finally show ?case by simp
next
  case (Imp F1 F2)
  from Imp.IH(1) have 1: "cut_bound (cut_bound m n F1) m F2 \<le> cut_bound (cut_bound' (max m n) F1) m F2" 
    by(rule cut_bound_mono[OF _ order.refl])
  also from Imp.IH(2)[of "cut_bound' (max m n) F1"] have "\<dots> \<le> cut_bound' (max (cut_bound' (max m n) F1) m) F2" by simp
  also have "\<dots> = cut_bound' (cut_bound' (max n m) F1) F2" by (simp add: cut_bound_max max.commute)
  finally show ?case by simp
qed simp_all
    
primrec depth :: "'a formula \<Rightarrow> nat" where
  "depth (Atom _) = 0" |
  "depth Bot = 0" |
  "depth (Not F) = Suc (depth F)" |
  "depth (And F G) = Suc (max (depth F) (depth G))" |
  "depth (Or F G) = Suc (max (depth F) (depth G))" |
  "depth (Imp F G) = Suc (max (depth F) (depth G))"
  
private primrec (* primrec works, but fun would give me a nicer induction rule *) cbnd where
  "cbnd k 0 = 2*k" |
  "cbnd k (Suc n) = cbnd (cbnd k n) n"
  
private lemma cbnd_grow: "(k :: nat) \<le> cbnd k d"
  by(induction d arbitrary: k; simp) (insert le_trans, blast)
    
private lemma cbnd_mono: assumes "b \<le> d" shows "cbnd (a::nat) b \<le> cbnd a d"
proof -
  have "cbnd (a::nat) b \<le> cbnd a (b + d)" for b d
    by(induction d arbitrary: a b; simp) (insert le_trans cbnd_grow, blast)
  thus ?thesis using assms using le_Suc_ex by blast
qed

private lemma cut_bound'_cbnd: "cut_bound' n F \<le> cbnd n (depth F)"
proof(induction F arbitrary: n)
next
  case (Not F)
  then show ?case using cbnd_grow dual_order.trans by fastforce
next
  case (And F1 F2)
  let ?md = "max (depth F1) (depth F2)"
  have "cut_bound' (cut_bound' n F1) F2 \<le> cut_bound' (cbnd n (depth F1)) F2" by (simp add: And.IH(1) cut_bound'_mono)
  also have "... \<le> cut_bound' (cbnd n ?md) F2" by (simp add: cbnd_mono cut_bound'_mono)
  also have "... \<le> cbnd (cbnd n ?md) (depth F2)" using And.IH(2) by blast
  also have "... \<le> cbnd (cbnd n ?md) ?md" by (simp add: cbnd_mono)
  finally show ?case by simp
next
  case (Imp F1 F2)
  case (Or F1 F2)
  text\<open>analogous\<close> (*<*)
  let ?md = "max (depth F1) (depth F2)"
  have "cut_bound' (cut_bound' n F1) F2 \<le> cut_bound' (cbnd n (depth F1)) F2" by (simp add: Or.IH(1) cut_bound'_mono)
  also have "... \<le> cut_bound' (cbnd n ?md) F2" by (simp add: cbnd_mono cut_bound'_mono)
  also have "... \<le> cbnd (cbnd n ?md) (depth F2)" using Or.IH(2) by blast
  also have "... \<le> cbnd (cbnd n ?md) ?md" by (simp add: cbnd_mono)
  finally show ?case by simp
next
  case (Imp F1 F2)
  let ?md = "max (depth F1) (depth F2)"
  have "cut_bound' (cut_bound' n F1) F2 \<le> cut_bound' (cbnd n (depth F1)) F2" by (simp add: Imp.IH(1) cut_bound'_mono)
  also have "... \<le> cut_bound' (cbnd n ?md) F2" by (simp add: cbnd_mono cut_bound'_mono)
  also have "... \<le> cbnd (cbnd n ?md) (depth F2)" using Imp.IH(2) by blast
  also have "... \<le> cbnd (cbnd n ?md) ?md" by (simp add: cbnd_mono)
  finally show ?case by simp
(*>*)
qed simp_all

value "map (cbnd (0::int)) [0,1,2,3,4]"
value "map (cbnd (1::int)) [0,1,2,3,4]" (* int, because that's easier to read\<dots> *)
value "map (cbnd (2::int)) [0,1,2,3,4]"
value "map (cbnd (3::int)) [0,1,2,3,4]"
value [nbe] "map (int \<circ> (\<lambda>n. n div 3) \<circ> cut_bound 3 3 \<circ> (\<lambda>n. ((\<lambda>F. And F F) ^^ n) (Atom 0))) [0,1,2,3,4,5,6,7]"
value [nbe] "map (int \<circ> (\<lambda>n. n div 3) \<circ> cut_bound' 3 \<circ> (\<lambda>n. ((\<lambda>F. And F F) ^^ n) (Atom 0))) [0,1,2,3,4]"
(* TODO: hm *)
value [nbe] "map (int \<circ> (\<lambda>n. n div 3) \<circ> cut_bound 3 3 \<circ> (\<lambda>n. ((\<lambda>F. Imp (Or F F) (And F F)) ^^ n) (Atom 0))) [0,1,2]"
value [nbe] "map (int \<circ> (\<lambda>n. n div 3) \<circ> cut_bound' 3 \<circ> (\<lambda>n. ((\<lambda>F. Imp (Or F F) (And F F)) ^^ n) (Atom 0))) [0,1,2]"
(* Hmhm *)
value [nbe] "(\<lambda>F. And (Or F F) (Or F F)) ^^ 2"

lemma "n + ((n + m) * 2 ^ (size F - Suc 0) + 
      (n + (n + m + (n + m) * 2 ^ (size F - Suc 0))) * 2 ^ (size G - Suc 0))
    \<le> (n + (m :: nat)) * 2 ^ (size F + size G)"
  oops
    (* so the proof below won't work. *)
lemma "cut_bound (n :: nat) m F \<le> (n + m) * (2 ^ (size F - 1) + 1)"
proof(induction F arbitrary: n m)
next
  case (Not F)
  show ?case unfolding cut_bound.simps by(rule le_trans[OF Not]) (simp add: add.commute)
next
  have "1 \<le> size F" for F :: "'a formula" by(cases F; simp)
  case (And F G)
  from And(2) have "cut_bound n (cut_bound n m F) G \<le> (n + (cut_bound n m F)) * (2 ^ (size G - 1) + 1)" by simp
  also from And(1) have "\<dots> \<le> (n + (n + m) * (2 ^ (size F - 1) + 1)) * (2 ^ (size G - 1) + 1)" 
    by (meson add_le_cancel_left mult_le_mono1)
  also have "\<dots> \<le> (n + m) * (2 ^ (size (F \<^bold>\<and> G) - 1) + 1)"
    apply simp
    oops
      
(* Oh! Look: *)
private lemma cbnd_comm: "cbnd (l * k::nat) n = l * cbnd (k::nat) n"
  by(induction n arbitrary: k; simp)

private lemma cbnd_closed: "cbnd (k::nat) n = k * 2 ^ (2 ^ n)"
  by(induction n arbitrary: k;simp add: semiring_normalization_rules(26))
    
theorem cut': assumes "\<Gamma> \<Rightarrow> F,\<Delta> \<down> n" "F,\<Gamma> \<Rightarrow> \<Delta> \<down> n" shows "\<Gamma> \<Rightarrow> \<Delta> \<down> n * 2 ^ (2 ^ depth F)"
proof -
  from cut_bound[OF assms] have c: "\<Gamma> \<Rightarrow> \<Delta> \<down> cut_bound n n F" .
  have d: "cut_bound n n F \<le> max n n * 2 ^ (2 ^ depth F)" 
    using cut_bound_' cut_bound'_cbnd cbnd_closed by (metis order_trans)
  show ?thesis using c d le_Suc_ex deeper unfolding max.idem by metis
qed
  
end

end
