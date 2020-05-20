(*
  File:     Fishburn_Impossibility.thy
  Author:   Manuel Eberl, TU München
  Author:   Christian Saile, TU München

  Incompatibility of Pareto Optimality and Fishburn-Strategy-Proofness
*)
section \<open>Main impossibility result\<close>

theory Fishburn_Impossibility
imports
  Social_Choice_Functions
begin

subsection \<open>Setting of the base case\<close>

text \<open>
  Suppose we have an anonymous, Fishburn-strategyproof, and Pareto-efficient SCF
  for three agents $A1$ to $A3$ and three alternatives $a$, $b$, and $c$. We will derive
  a contradiction from this.
\<close>
locale fb_impossibility_3_3 =
  strategyproof_anonymous_scf agents alts scf Fishb +
  pareto_efficient_scf agents alts scf
  for agents :: "'agent set" and alts :: "'alt set" and scf A1 A2 A3 a b c +
  assumes agents_eq: "agents = {A1, A2, A3}"
  assumes alts_eq:    "alts = {a, b, c}"
  assumes distinct_agents: "distinct [A1, A2, A3]"
  assumes distinct_alts: "distinct [a, b, c]"
begin

text \<open>
  We first give some simple rules that will allow us to break down the strategyproofness
  and support conditions more easily later.
\<close>
lemma agents_neq [simp]: "A1 \<noteq> A2" "A2 \<noteq> A1" "A1 \<noteq> A3" "A3 \<noteq> A1" "A2 \<noteq> A3" "A3 \<noteq> A2"
  using distinct_agents by auto

lemma alts_neq [simp]: "a \<noteq> b" "a \<noteq> c" "b \<noteq> c" "b \<noteq> a" "c \<noteq> a" "c \<noteq> b"
  using distinct_alts by auto

lemma agent_in_agents [simp]: "A1 \<in> agents" "A2 \<in> agents" "A3 \<in> agents"
  by (simp_all add: agents_eq)

lemma alt_in_alts [simp]: "a \<in> alts" "b \<in> alts" "c \<in> alts"
  by (simp_all add: alts_eq)

lemma Bex_alts: "(\<exists>x\<in>alts. P x) \<longleftrightarrow> P a \<or> P b \<or> P c"
  by (simp add: alts_eq)

lemma eval_pareto_loser_aux: 
  assumes "is_pref_profile R"
  shows   "x \<in> pareto_losers R \<longleftrightarrow> (\<exists>y\<in>{a,b,c}. x \<prec>[Pareto(R)] y)"
proof -
  interpret pref_profile_wf agents alts R by fact
  have *: "y \<in> {a,b,c}" if "x \<prec>[Pareto(R)] y" for y
    using Pareto.strict_not_outside[of x y] that by (simp add: alts_eq)
  show ?thesis by (auto simp: pareto_losers_def dest: *)
qed

lemma eval_Pareto:
  assumes "is_pref_profile R"
  shows   "x \<prec>[Pareto(R)] y \<longleftrightarrow> (\<forall>i\<in>{A1,A2,A3}. x \<preceq>[R i] y) \<and> (\<exists>i\<in>{A1,A2,A3}. \<not>x \<succeq>[R i] y)"
proof -
  interpret R: pref_profile_wf agents alts by fact
  show ?thesis unfolding R.Pareto_strict_iff by (auto simp: strongly_preferred_def agents_eq)
qed

lemmas eval_pareto = eval_pareto_loser_aux eval_Pareto
lemma pareto_efficiency: "is_pref_profile R \<Longrightarrow> x \<in> pareto_losers R \<Longrightarrow> x \<notin> scf R"
  using pareto_efficient[of R] by blast

lemma Ball_scf:
  assumes "is_pref_profile R"
  shows   "(\<forall>x\<in>scf R. P x) \<longleftrightarrow> (a \<notin> scf R \<or> P a) \<and> (b \<notin> scf R \<or> P b) \<and> (c \<notin> scf R \<or> P c)"
  using scf_alts[OF assms] unfolding alts_eq by blast

lemma Ball_scf_diff: 
  assumes "is_pref_profile R1" "is_pref_profile R2"
  shows   "(\<forall>x\<in>scf R1 - scf R2. P x) \<longleftrightarrow> 
             (a \<in> scf R2 \<or> a \<notin> scf R1 \<or> P a) \<and> (b \<in> scf R2 \<or> b \<notin> scf R1 \<or> P b) \<and> 
             (c \<in> scf R2 \<or> c \<notin> scf R1 \<or> P c)"
  using assms[THEN scf_alts] unfolding alts_eq by blast

lemma scf_nonempty':
  assumes "is_pref_profile R"
  shows   "\<exists>x\<in>alts. x \<in> scf R"
  using scf_nonempty[OF assms] scf_alts[OF assms] by blast


subsection \<open>Definition of Preference Profiles and Fact Gathering\<close>

text \<open>
  We now define the 21 preference profile that will lead to the impossibility result.
\<close>
preference_profile 
  agents: agents
  alts:   alts
where R1   = A1: [a, c], b    A2: [a, c], b     A3: b, c, a  
  and R2   = A1: c, [a, b]    A2: b, c, a       A3: c, b, a 
  and R3   = A1: [a, c], b    A2: b, c, a       A3: c, b, a   
  and R4   = A1: [a, c], b    A2:  a, b, c      A3: b, c, a
  and R5   = A1: c, [a, b]    A2:  a, b, c      A3: b, c, a
  and R6   = A1: b, [a, c]    A2: c, [a, b]     A3:  b, c, a
  and R7   = A1: [a, c], b    A2: b, [a, c]     A3: b, c, a 
  and R8   = A1: [b, c], a    A2: a, [b, c]     A3: a, c, b
  and R9   = A1: [b, c], a    A2: b, [a, c]     A3: a, b, c
  and R10  = A1: c, [a, b]    A2: a, b, c       A3: c, b, a   
  and R11  = A1: [a, c], b    A2: a, b, c       A3: c, b, a  
  and R12  = A1: c, [a, b]    A2: b, a, c       A3: c, b, a   
  and R13  = A1: [a, c], b    A2: b, a, c       A3: c, b, a  
  and R14  = A1: a, [b, c]    A2: c, [a, b]     A3: a, c, b   
  and R15  = A1: [b, c], a    A2: a, [b, c]     A3: a, b, c  
  and R16  = A1: [a, b], c    A2: c, [a, b]     A3: a, b, c  
  and R17  = A1: a, [b, c]    A2: a, b, c       A3: b, c, a
  and R18  = A1: [a, c], b    A2: b, [a, c]     A3: b, a, c 
  and R19  = A1: a, [b, c]    A2: c, [a, b]     A3: a, b, c
  and R20  = A1: b, [a, c]    A2: a, b, c       A3: b, a, c
  and R21  = A1: [b, c], a    A2: a, b, c       A3: b, c, a
  by (simp_all add: agents_eq alts_eq)

lemmas R_wfs = 
  R1.wf R2.wf R3.wf R4.wf R5.wf R6.wf R7.wf R8.wf R9.wf R10.wf R11.wf R12.wf R13.wf R14.wf R15.wf 
  R16.wf R17.wf R18.wf R19.wf R20.wf R21.wf 

lemmas R_evals =
  R1.eval R2.eval R3.eval R4.eval R5.eval R6.eval R7.eval R8.eval R9.eval R10.eval R11.eval R12.eval  R13.eval 
  R14.eval R15.eval R16.eval R17.eval R18.eval R19.eval R20.eval R21.eval

lemmas nonemptiness = R_wfs [THEN scf_nonempty', unfolded Bex_alts]

text \<open>
  We show the support conditions from Pareto efficiency
\<close>
lemma [simp]: "a \<notin> scf R1" by (rule pareto_efficiency) (simp_all add: eval_pareto R1.eval)
lemma [simp]: "a \<notin> scf R2" by (rule pareto_efficiency) (simp_all add: eval_pareto R2.eval)
lemma [simp]: "a \<notin> scf R3" by (rule pareto_efficiency) (simp_all add: eval_pareto R3.eval)
lemma [simp]: "a \<notin> scf R6" by (rule pareto_efficiency) (simp_all add: eval_pareto R6.eval)
lemma [simp]: "a \<notin> scf R7" by (rule pareto_efficiency) (simp_all add: eval_pareto R7.eval)
lemma [simp]: "b \<notin> scf R8" by (rule pareto_efficiency) (simp_all add: eval_pareto R8.eval)
lemma [simp]: "c \<notin> scf R9" by (rule pareto_efficiency) (simp_all add: eval_pareto R9.eval)
lemma [simp]: "a \<notin> scf R12" by (rule pareto_efficiency) (simp_all add: eval_pareto R12.eval)
lemma [simp]: "b \<notin> scf R14" by (rule pareto_efficiency) (simp_all add: eval_pareto R14.eval)
lemma [simp]: "c \<notin> scf R15" by (rule pareto_efficiency) (simp_all add: eval_pareto R15.eval)
lemma [simp]: "b \<notin> scf R16" by (rule pareto_efficiency) (simp_all add: eval_pareto R16.eval)
lemma [simp]: "c \<notin> scf R17" by (rule pareto_efficiency) (simp_all add: eval_pareto R17.eval)
lemma [simp]: "c \<notin> scf R18" by (rule pareto_efficiency) (simp_all add: eval_pareto R18.eval)
lemma [simp]: "b \<notin> scf R19" by (rule pareto_efficiency) (simp_all add: eval_pareto R19.eval)
lemma [simp]: "c \<notin> scf R20" by (rule pareto_efficiency) (simp_all add: eval_pareto R20.eval)
lemma [simp]: "c \<notin> scf R21" by (rule pareto_efficiency) (simp_all add: eval_pareto R21.eval)

text \<open>
  We derive the strategyproofness conditions:
\<close>
lemma s41: "\<not> scf R4 \<succ>[Fishb(R1 A2)] scf R1"
    by (intro strategyproof'[where j = A2]) (simp_all add: R4.eval R1.eval)
   
lemma s32: "\<not> scf R3 \<succ>[Fishb(R2 A1)] scf R2"
    by (intro strategyproof'[where j = A1]) (simp_all add: R3.eval R2.eval)
 
lemma s122: "\<not> scf R12 \<succ>[Fishb(R2 A2)] scf R2"
    by (intro strategyproof'[where j = A2]) (simp_all add: R12.eval R2.eval)
   
lemma s133: "\<not> scf R13 \<succ>[Fishb(R3 A2)] scf R3"
    by (intro strategyproof'[where j = A2]) (simp_all add: R13.eval R3.eval)
    
lemma s102: "\<not> scf R10 \<succ>[Fishb(R2 A2)] scf R2"
    by (intro strategyproof'[where j = A2]) (simp_all add: R10.eval R2.eval)
         
lemma s13: "\<not> scf R1 \<succ>[Fishb(R3 A3)] scf R3"
    by (intro strategyproof'[where j = A2]) (simp_all add: R1.eval R3.eval)
    
lemma s54: "\<not> scf R5 \<succ>[Fishb(R4 A1)] scf R4"
    by (intro strategyproof'[where j = A1]) (simp_all add: R5.eval R4.eval)
    
lemma s174: "\<not> scf R17 \<succ>[Fishb(R4 A1)] scf R4"
    by (intro strategyproof'[where j = A1]) (simp_all add: R17.eval R4.eval)
      
lemma s74: "\<not> scf R7 \<succ>[Fishb(R4 A2)] scf R4"
    by (intro strategyproof'[where j = A2]) (simp_all add: R7.eval R4.eval)
    
lemma s114: "\<not> scf R11 \<succ>[Fishb(R4 A3)] scf R4"
    by (intro strategyproof'[where j = A3]) (simp_all add: R11.eval R4.eval)
  
lemma s45: "\<not> scf R4 \<succ>[Fishb(R5 A1)] scf R5"
    by (intro strategyproof'[where j = A1]) (simp_all add: R4.eval R5.eval)
     
lemma s65: "\<not> scf R6 \<succ>[Fishb(R5 A2)] scf R5"
    by (intro strategyproof'[where j = A1]) (simp_all add: insert_commute R5.eval R6.eval)
    
lemma s105: "\<not> scf R10 \<succ>[Fishb(R5 A3)] scf R5"
    by (intro strategyproof'[where j = A3]) (simp_all add:  R10.eval R5.eval)
    
lemma s67: "\<not> scf R6 \<succ>[Fishb(R7 A1)] scf R7"
    by (intro strategyproof'[where j = A2]) (simp_all add: insert_commute  R6.eval R7.eval)
    
lemma s187: "\<not> scf R18 \<succ>[Fishb(R7 A3)] scf R7"
    by (intro strategyproof'[where j = A3]) (simp_all add: insert_commute R7.eval R18.eval)
   
lemma s219: "\<not> scf R21 \<succ>[Fishb(R9 A2)] scf R9"
    by (intro strategyproof'[where j = A3]) (simp_all add: insert_commute R9.eval R21.eval)
   
lemma s1011: "\<not> scf R10 \<succ>[Fishb(R11 A1)] scf R11"
    by (intro strategyproof'[where j = A1]) (simp_all add: insert_commute R10.eval R11.eval)
    
lemma s1012: "\<not> scf R10 \<succ>[Fishb(R12 A2)] scf R12"
    by (intro strategyproof'[where j = A2]) (simp_all add: insert_commute R10.eval R12.eval)
    
lemma s1213: "\<not> scf R12 \<succ>[Fishb(R13 A1)] scf R13"
    by (intro strategyproof'[where j = A1]) (simp_all add: insert_commute R12.eval R13.eval)
    
lemma s1113: "\<not> scf R11 \<succ>[Fishb(R13 A2)] scf R13"
    by (intro strategyproof'[where j = A2]) (simp_all add: insert_commute R11.eval R13.eval)
    
lemma s1813: "\<not> scf R18 \<succ>[Fishb(R13 A3)] scf R13"
    by (intro strategyproof'[where j = A2]) (simp_all add: insert_commute R18.eval R13.eval)
    
lemma s814: "\<not> scf R8 \<succ>[Fishb(R14 A2)] scf R14"
    by (intro strategyproof'[where j = A1]) (simp_all add: insert_commute R8.eval R14.eval)
   
lemma s1914: "\<not> scf R19 \<succ>[Fishb(R14 A3)] scf R14"
    by (intro strategyproof'[where j = A3]) (simp_all add: insert_commute R19.eval R14.eval)
   
lemma s1715: "\<not> scf R17 \<succ>[Fishb(R15 A1)] scf R15"
    by (intro strategyproof'[where j = A3]) (simp_all add: insert_commute R17.eval R15.eval)

lemma s815: "\<not> scf R8 \<succ>[Fishb(R15 A3)] scf R15"
    by (intro strategyproof'[where j = A3]) (simp_all add: insert_commute R8.eval R15.eval)

lemma s516: "\<not> scf R5 \<succ>[Fishb(R16 A1)] scf R16"
    by (intro strategyproof'[where j = A3]) (simp_all add: insert_commute R5.eval R16.eval)
  
lemma s517: "\<not> scf R5 \<succ>[Fishb(R17 A1)] scf R17"
    by (intro strategyproof'[where j = A1]) (simp_all add: insert_commute R5.eval R17.eval)
   
lemma s1619: "\<not> scf R16 \<succ>[Fishb(R19 A1)] scf R19"
     by (intro strategyproof'[where j = A1]) (simp_all add: insert_commute  R16.eval R19.eval) 
     
lemma s1820: "\<not> scf R18 \<succ>[Fishb(R20 A2)] scf R20"
    by (intro strategyproof'[where j = A1]) (simp_all add: insert_commute  R18.eval R20.eval)
   
lemma s920: "\<not> scf R9 \<succ>[Fishb(R20 A3)] scf R20"
    by (intro strategyproof'[where j = A1]) (simp_all add: insert_commute  R20.eval R9.eval)

lemma s521: "\<not> scf R5 \<succ>[Fishb(R21 A1)] scf R21"
    by (intro strategyproof'[where j = A1]) (simp_all add: insert_commute  R21.eval R5.eval)
 
lemma s421: "\<not> scf R4 \<succ>[Fishb(R21 A1)] scf R21"
    by (intro strategyproof'[where j = A1]) (simp_all add: insert_commute  R21.eval R4.eval)
 

lemmas sp = s41 s32 s122 s102 s133 s13 s54 s174 s54 s74 s114 s45 s65 s105 s67
            s187 s219 s1011 s1012 s1213 s1113 s1813 s814 s1914 s1715 s815 s516
            s517 s1619 s1820 s920 s521 s421 

text \<open>
  We now use the simplifier to break down the strategyproofness conditions into SAT formulae.
  This takes a few seconds, so we use some low-level ML code to at least do the simplification
  in parallel.
\<close>
local_setup \<open>fn lthy =>
  let
    val lthy' = lthy addsimps @{thms Fishb_strict_iff Ball_scf Ball_scf_diff R_evals}
    val thms = Par_List.map (Simplifier.asm_full_simplify lthy') @{thms sp}
  in
    Local_Theory.notes [((@{binding sp'}, []), [(thms, [])])] lthy |> snd
  end
\<close>

text \<open>
  We show that the strategyproofness conditions, the non-emptiness conditions (i.\,e.\ every SCF
  must return at least one winner), and the efficiency conditions are not satisfiable together,
  which means that the SCF whose existence we assumed simply cannot exist.
\<close>
theorem absurd: False
  using sp' and nonemptiness [simplified] by satx

end


subsection \<open>Lifting to more than 3 agents and alternatives\<close>

text \<open>
  We now employ the standard lifting argument outlined before to lift this impossibility
  from 3 agents and alternatives to any setting with at least 3 agents and alternatives.
\<close>
locale fb_impossibility =
  strategyproof_anonymous_scf agents alts scf Fishb +
  pareto_efficient_scf agents alts scf
  for agents :: "'agent set" and alts :: "'alt set" and scf +
  assumes card_agents_ge: "card agents \<ge> 3"
      and card_alts_ge:   "card alts \<ge> 3"
begin

(* TODO: Move? *)
lemma finite_list':
  assumes "finite A"
  obtains xs where "A = set xs" "distinct xs" "length xs = card A"
proof -
  from assms obtain xs where "set xs = A" using finite_list by blast
  thus ?thesis using distinct_card[of "remdups xs"]
    by (intro that[of "remdups xs"]) simp_all
qed

lemma finite_list_subset:
  assumes "finite A" "card A \<ge> n"
  obtains xs where "set xs \<subseteq> A" "distinct xs" "length xs = n"
proof -
  obtain xs where "A = set xs" "distinct xs" "length xs = card A"
    using finite_list'[OF assms(1)] by blast
  with assms show ?thesis
    by (intro that[of "take n xs"]) (simp_all add: set_take_subset)
qed

lemma card_ge_3E:
  assumes "finite A" "card A \<ge> 3"
  obtains a b c where "distinct [a,b,c]" "{a,b,c} \<subseteq> A"
proof -
  from finite_list_subset[OF assms] guess xs .
  moreover then obtain a b c where "xs = [a, b, c]" 
    by (auto simp: eval_nat_numeral length_Suc_conv)
  ultimately show ?thesis by (intro that[of a b c]) simp_all
qed

theorem absurd: False
proof -
  from card_ge_3E[OF finite_agents card_agents_ge] guess A1 A2 A3 .
  note agents = this
  let ?agents' = "{A1, A2, A3}"
  from card_ge_3E[OF finite_alts card_alts_ge] guess a b c .
  note alts = this
  let ?alts' = "{a, b, c}"

  interpret scf_lowering_anonymous agents alts scf ?agents' ?alts'
    by standard (use agents alts in auto)
  interpret liftable_set_extension ?alts' alts Fishb
    by (intro Fishburn_liftable alts)
  interpret scf_lowering_strategyproof agents alts scf ?agents' ?alts' Fishb ..
  interpret fb_impossibility_3_3 ?agents' ?alts' lowered A1 A2 A3 a b c
    by standard (use agents alts in simp_all)
  from absurd show False .
qed

end

end