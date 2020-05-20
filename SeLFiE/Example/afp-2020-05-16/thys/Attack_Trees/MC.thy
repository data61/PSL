section "Kripke structures and CTL"

text \<open>We apply Kripke structures and CTL to model state based systems and analyse properties under 
dynamic state changes. Snapshots of systems are the states on which we define a state transition. 
Temporal logic is then employed to express security and privacy properties.\<close>
theory MC
imports Main
begin

subsection "Lemmas to support least and greatest fixpoints"

lemma predtrans_empty: 
  assumes "mono (\<tau> :: 'a set \<Rightarrow> 'a set)"
  shows "\<forall> i. (\<tau> ^^ i) ({}) \<subseteq> (\<tau> ^^(i + 1))({})"
  using assms funpow_decreasing le_add1 by blast

lemma ex_card: "finite S \<Longrightarrow> \<exists> n:: nat. card S = n"
by simp

lemma less_not_le: "\<lbrakk>(x:: nat) < y; y \<le> x\<rbrakk> \<Longrightarrow> False"
by arith

lemma infchain_outruns_all: 
  assumes "finite (UNIV :: 'a set)" 
    and "\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set)^^ i) ({}:: 'a set) \<subset> (\<tau> ^^ (i + 1)) {}"
  shows "\<forall>j :: nat. \<exists>i :: nat. j < card ((\<tau> ^^ i) {})"
proof (rule allI, induct_tac j)
  show "\<exists>i. 0 < card ((\<tau> ^^ i) {})" using assms
    by (metis bot.not_eq_extremum card_gt_0_iff finite_subset subset_UNIV)
next show "\<And>j n. \<exists>i. n < card ((\<tau> ^^ i) {}) 
             \<Longrightarrow> \<exists>i. Suc n < card ((\<tau> ^^ i) {})"
    proof -
      fix j n
      assume a: "\<exists>i. n < card ((\<tau> ^^ i) {})"
      obtain i where "n < card ((\<tau> ^^ i) {})"
        using a by blast 
      thus "\<exists> i. Suc n < card ((\<tau> ^^ i) {})" using assms
        by (meson finite_subset le_less_trans le_simps(3) psubset_card_mono subset_UNIV)
    qed
  qed

lemma no_infinite_subset_chain: 
   assumes "finite (UNIV :: 'a set)"
    and    "mono (\<tau> :: ('a set \<Rightarrow> 'a set))"
    and    "\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set) ^^ i) {} \<subset> (\<tau> ^^ (i + (1 :: nat))) ({} :: 'a set)" 
  shows   "False"
text \<open>Proof idea: since @{term "UNIV"} is finite, we have from @{text \<open>ex_card\<close>} that there is
    an n with @{term "card UNIV = n"}. Now, use @{text \<open>infchain_outruns_all\<close>} to show as 
    contradiction point that
    @{term "\<exists> i :: nat. card UNIV < card ((\<tau> ^^ i) {})"}. 
    Since all sets are subsets of @{term "UNIV"}, we also have 
    @{term "card ((\<tau> ^^ i) {}) \<le> card UNIV"}:
    Contradiction!, i.e. proof of False  \<close>
proof -
  have a: "\<forall> (j :: nat). (\<exists> (i :: nat). (j :: nat) < card((\<tau> ^^ i)({} :: 'a set)))" using assms
    by (erule_tac \<tau> = \<tau> in infchain_outruns_all)
  hence b: "\<exists> (n :: nat). card(UNIV :: 'a set) = n" using assms
    by (erule_tac S = UNIV in ex_card)
  from this obtain n where c: "card(UNIV :: 'a set) = n" by (erule exE)
  hence   d: "\<exists>i. card UNIV < card ((\<tau> ^^ i) {})" using a
    by (drule_tac x = "card UNIV" in spec)
  from this obtain i where e: "card (UNIV :: 'a set) < card ((\<tau> ^^ i) {})"
    by (erule exE)
  hence f: "(card((\<tau> ^^ i){})) \<le> (card (UNIV :: 'a set))" using assms
    apply (erule_tac A = "((\<tau> ^^ i){})" in Finite_Set.card_mono)
    by (rule subset_UNIV)
  thus "False" using e
    by (erule_tac y = "card((\<tau> ^^ i){})" in less_not_le)
qed

lemma finite_fixp: 
  assumes "finite(UNIV :: 'a set)" 
      and "mono (\<tau> :: ('a set \<Rightarrow> 'a set))"
    shows "\<exists> i. (\<tau> ^^ i) ({}) = (\<tau> ^^(i + 1))({})"
text \<open>Proof idea: 
with @{text predtrans_empty} we know 

@{term "\<forall> i. (\<tau> ^^ i){} \<subseteq> (\<tau> ^^(i + 1))({})"} (1).

If we can additionally show 

@{term "\<exists> i.  (\<tau> ^^ i)({}) \<supseteq> (\<tau> ^^(i + 1))({})"} (2),

we can get the goal together with equalityI 
@{text "\<subseteq> + \<supseteq> \<longrightarrow> ="}. 
To prove (1) we observe that 
@{term "(\<tau> ^^ i)({}) \<supseteq> (\<tau> ^^(i + 1))({})"} 
can be inferred from 
@{term "\<not>((\<tau> ^^ i)({}) \<subseteq> (\<tau> ^^(i + 1))({}))"} 
and (1).
Finally, the latter is solved directly by @{text \<open>no_infinite_subset_chain\<close>}.\<close>
proof -
  have a: "\<forall>i. (\<tau> ^^ i) ({}:: 'a set) \<subseteq> (\<tau> ^^ (i + (1))) {}" 
    by(rule predtrans_empty, rule assms(2))
  have a3: "\<not> (\<forall> i :: nat. (\<tau> ^^ i) {} \<subset> (\<tau> ^^(i + 1)) {})" 
    by (rule notI, rule no_infinite_subset_chain, (rule assms)+)
  hence b: "(\<exists> i :: nat. \<not>((\<tau> ^^ i) {} \<subset> (\<tau> ^^(i + 1)) {}))" using assms a3
    by blast
  thus "\<exists> i. (\<tau> ^^ i) ({}) = (\<tau> ^^(i + 1))({})" using a
    by blast
qed

lemma predtrans_UNIV: 
  assumes "mono (\<tau> :: ('a set \<Rightarrow> 'a set))"
  shows "\<forall> i. (\<tau> ^^ i) (UNIV) \<supseteq> (\<tau> ^^(i + 1))(UNIV)"
proof (rule allI, induct_tac i)
  show "(\<tau> ^^ ((0) + (1))) UNIV \<subseteq> (\<tau> ^^ (0)) UNIV" 
    by simp
next show "\<And>(i) n.
       (\<tau> ^^ (n + (1))) UNIV \<subseteq> (\<tau> ^^ n) UNIV \<Longrightarrow> (\<tau> ^^ (Suc n + (1))) UNIV \<subseteq> (\<tau> ^^ Suc n) UNIV"
  proof -
    fix i n
    assume a: "(\<tau> ^^ (n + (1))) UNIV \<subseteq> (\<tau> ^^ n) UNIV"
    have "(\<tau> ((\<tau> ^^ n) UNIV)) \<supseteq> (\<tau> ((\<tau> ^^ (n + (1 :: nat))) UNIV))" using assms a
      by (rule monoE)
    thus "(\<tau> ^^ (Suc n + (1))) UNIV \<subseteq> (\<tau> ^^ Suc n) UNIV" by simp
   qed
 qed

lemma Suc_less_le: "x < (y - n) \<Longrightarrow> x \<le> (y - (Suc n))"
 by simp

lemma card_univ_subtract: 
  assumes "finite (UNIV :: 'a set)" and  "mono \<tau>"
     and  "(\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set) ^^ (i + (1 :: nat)))(UNIV :: 'a set) \<subset> (\<tau> ^^ i) UNIV)"
   shows "(\<forall> i :: nat. card((\<tau> ^^ i) (UNIV ::'a set)) \<le> (card (UNIV :: 'a set)) - i)"
proof (rule allI, induct_tac i) 
  show "card ((\<tau> ^^ (0)) UNIV) \<le> card (UNIV :: 'a set) - (0)" using assms
    by (simp)
next show "\<And>(i) n.
       card ((\<tau> ^^ n) (UNIV :: 'a set)) \<le> card (UNIV :: 'a set) - n \<Longrightarrow>
       card ((\<tau> ^^ Suc n) (UNIV :: 'a set)) \<le> card (UNIV :: 'a set) - Suc n" using assms
  proof -
    fix i n
    assume a: "card ((\<tau> ^^ n) (UNIV :: 'a set)) \<le> card (UNIV :: 'a set) - n"
    have b: "(\<tau> ^^ (n + (1)))(UNIV :: 'a set) \<subset> (\<tau> ^^ n) UNIV" using assms
      by (erule_tac x = n in spec)
    have "card((\<tau> ^^ (n + (1 :: nat)))(UNIV :: 'a set)) < card((\<tau> ^^ n) (UNIV :: 'a set))"       
      by (rule psubset_card_mono, rule finite_subset, rule subset_UNIV, rule assms(1), rule b)
    thus "card ((\<tau> ^^ Suc n) (UNIV :: 'a set)) \<le> card (UNIV :: 'a set) - Suc n" using a
      by simp
    qed
  qed

lemma card_UNIV_tau_i_below_zero: 
  assumes "finite (UNIV :: 'a set)" and "mono \<tau>"
   and  "(\<forall>i :: nat. ((\<tau> :: ('a set \<Rightarrow> 'a set)) ^^ (i + (1 :: nat)))(UNIV :: 'a set) \<subset> (\<tau> ^^ i) UNIV)"
 shows "card((\<tau> ^^ (card (UNIV ::'a set))) (UNIV ::'a set)) \<le> 0"
proof -
  have "(\<forall> i :: nat. card((\<tau> ^^ i) (UNIV ::'a set)) \<le> (card (UNIV :: 'a set)) - i)" using assms
    by (rule card_univ_subtract)
  thus "card((\<tau> ^^ (card (UNIV ::'a set))) (UNIV ::'a set)) \<le> 0"
   by (drule_tac x = "card (UNIV ::'a set)" in spec, simp)
qed

lemma finite_card_zero_empty: "\<lbrakk> finite S; card S \<le> 0\<rbrakk> \<Longrightarrow> S = {}"
by simp

lemma UNIV_tau_i_is_empty:
  assumes "finite (UNIV :: 'a set)" and "mono (\<tau> :: ('a set \<Rightarrow> 'a set))"
    and   "(\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set) ^^ (i + (1 :: nat)))(UNIV :: 'a set) \<subset> (\<tau> ^^ i) UNIV)"
  shows "(\<tau> ^^ (card (UNIV ::'a set))) (UNIV ::'a set) = {}"
  by (meson assms card_UNIV_tau_i_below_zero finite_card_zero_empty finite_subset subset_UNIV)

lemma down_chain_reaches_empty:
  assumes "finite (UNIV :: 'a set)" and "mono (\<tau> :: 'a set \<Rightarrow> 'a set)"
   and "(\<forall>i :: nat. ((\<tau> :: 'a set \<Rightarrow> 'a set) ^^ (i + (1 :: nat))) UNIV \<subset> (\<tau> ^^ i) UNIV)"
 shows "\<exists> (j :: nat). (\<tau> ^^ j) UNIV = {}"
  using UNIV_tau_i_is_empty assms by blast

lemma no_infinite_subset_chain2: 
  assumes "finite (UNIV :: 'a set)" and "mono (\<tau> :: ('a set \<Rightarrow> 'a set))"
      and "\<forall>i :: nat. (\<tau> ^^ i) UNIV \<supset> (\<tau> ^^ (i + (1 :: nat))) UNIV"
  shows "False"
proof -
  have "\<exists> j :: nat. (\<tau> ^^ j) UNIV = {}" using assms
    by (rule down_chain_reaches_empty)
  from this obtain j where a: "(\<tau> ^^ j) UNIV = {}" by (erule exE)
  have "(\<tau> ^^ (j + (1))) UNIV \<subset> (\<tau> ^^ j) UNIV" using assms
    by (erule_tac x = j in spec)
  thus False using a by simp 
qed

lemma finite_fixp2: 
  assumes "finite(UNIV :: 'a set)" and "mono (\<tau> :: ('a set \<Rightarrow> 'a set))"
  shows "\<exists> i. (\<tau> ^^ i) UNIV = (\<tau> ^^(i + 1)) UNIV"
proof -
  have "\<forall>i. (\<tau> ^^ (i + (1))) UNIV \<subseteq> (\<tau> ^^ i) UNIV" 
    by (rule predtrans_UNIV , simp add: assms(2))  
  moreover have "\<exists>i. \<not> (\<tau> ^^ (i + (1))) UNIV \<subset> (\<tau> ^^ i) UNIV" using assms
  proof -
    have "\<not> (\<forall> i :: nat. (\<tau> ^^ i) UNIV \<supset> (\<tau> ^^(i + 1)) UNIV)"
      using assms(1) assms(2) no_infinite_subset_chain2 by blast 
    thus "\<exists>i. \<not> (\<tau> ^^ (i + (1))) UNIV \<subset> (\<tau> ^^ i) UNIV" by blast
  qed
  ultimately show "\<exists> i. (\<tau> ^^ i) UNIV = (\<tau> ^^(i + 1)) UNIV" 
    by blast
qed

lemma lfp_loop: 
  assumes "finite (UNIV :: 'b set)" and "mono (\<tau> :: ('b set \<Rightarrow> 'b set))"
  shows "\<exists> n . lfp \<tau>  = (\<tau> ^^ n) {}"
proof -
  have "\<exists>i. (\<tau> ^^ i) {} = (\<tau> ^^ (i + (1))) {}"  using assms
    by (rule finite_fixp)
  from this obtain i where " (\<tau> ^^ i) {} = (\<tau> ^^ (i + (1))) {}"
    by (erule exE)
  hence "(\<tau> ^^ i) {} = (\<tau> ^^ Suc i) {}"
    by simp
  hence "(\<tau> ^^ Suc i) {} = (\<tau> ^^ i) {}"
    by (rule sym)
  hence "lfp \<tau> = (\<tau> ^^ i) {}"
     by (simp add: assms(2) lfp_Kleene_iter)
   thus "\<exists> n . lfp \<tau>  = (\<tau> ^^ n) {}" 
   by (rule exI) 
qed

text \<open>These next two are repeated from the corresponding
   theorems in HOL/ZF/Nat.thy for the sake of self-containedness of the exposition.\<close>
lemma Kleene_iter_gpfp:
  assumes "mono f" and "p \<le> f p" shows "p \<le> (f^^k) (top::'a::order_top)"
proof(induction k)
  case 0 show ?case by simp
next
  case Suc
  from monoD[OF assms(1) Suc] assms(2)
  show ?case by simp
qed

lemma gfp_loop: 
  assumes "finite (UNIV :: 'b set)"
   and "mono (\<tau> :: ('b set \<Rightarrow> 'b set))"
    shows "\<exists> n . gfp \<tau>  = (\<tau> ^^ n)UNIV"
proof -
  have " \<exists>i. (\<tau> ^^ i)(UNIV :: 'b set) = (\<tau> ^^ (i + (1))) UNIV" using assms
    by (rule finite_fixp2)
  from this obtain i where "(\<tau> ^^ i)UNIV = (\<tau> ^^ (i + (1))) UNIV" by (erule exE)
  thus "\<exists> n . gfp \<tau>  = (\<tau> ^^ n)UNIV" using assms
    by (metis Suc_eq_plus1 gfp_Kleene_iter)
qed

subsection \<open>Generic type of state with state transition and CTL operators\<close>
text \<open>The system states and their transition relation are defined as a class called
 @{text \<open>state\<close>} containing an abstract constant@{text \<open>state_transition\<close>}. It introduces the 
syntactic infix notation @{text \<open>I \<rightarrow>\<^sub>i I'\<close>} to denote that system state @{text \<open>I\<close>} and @{text \<open>I’\<close>} 
are in this relation over an arbitrary (polymorphic) type @{text \<open>'a\<close>}.\<close>
class state =
  fixes state_transition :: "['a :: type, 'a] \<Rightarrow> bool"  (infixr "\<rightarrow>\<^sub>i" 50)

text \<open>The above class definition lifts Kripke structures and CTL to a general level. 
The definition of the inductive relation is given by a set of specific rules which are, 
however, part of an application like infrastructures. Branching time temporal logic CTL 
is defined in general over Kripke structures with arbitrary state transitions and can later 
be applied to suitable theories, like infrastructures.
Based on the generic state transition @{text \<open>\<rightarrow>\<close>} of the type class state, the CTL-operators 
EX and AX express that property f holds in some or all next states, respectively.\<close> 
    
definition AX where "AX f \<equiv> {s. {f0. s \<rightarrow>\<^sub>i f0} \<subseteq> f}"
definition EX' where "EX' f \<equiv> {s . \<exists> f0 \<in> f. s \<rightarrow>\<^sub>i f0 }"

text \<open>The CTL formula @{text \<open>AG f\<close>} means that on all paths branching from a state @{text \<open>s\<close>} 
the formula @{text \<open>f\<close>} is always true (@{text \<open>G\<close>} stands for ‘globally’). It can be defined 
using the Tarski fixpoint theory by applying the greatest fixpoint operator. In a similar way, 
the other CTL operators are defined.\<close>
definition AF where "AF f \<equiv> lfp (\<lambda> Z. f \<union> AX Z)"
definition EF where "EF f \<equiv> lfp (\<lambda> Z. f \<union> EX' Z)"
definition AG where "AG f \<equiv> gfp (\<lambda> Z. f \<inter> AX Z)"
definition EG where "EG f \<equiv> gfp (\<lambda> Z. f \<inter> EX' Z)"
definition AU where "AU f1 f2 \<equiv> lfp(\<lambda> Z. f2 \<union> (f1 \<inter> AX Z))"
definition EU where "EU f1 f2 \<equiv> lfp(\<lambda> Z. f2 \<union> (f1 \<inter> EX' Z))"
definition AR where "AR f1 f2 \<equiv> gfp(\<lambda> Z. f2 \<inter> (f1 \<union> AX Z))"
definition ER where "ER f1 f2 \<equiv> gfp(\<lambda> Z. f2 \<inter> (f1 \<union> EX' Z))"

subsection  \<open>Kripke structures and Modelchecking\<close>
datatype 'a kripke = 
  Kripke "'a set" "'a set"

primrec states where "states (Kripke S I) = S" 
primrec init where "init (Kripke S I) = I" 

text \<open>The formal Isabelle definition of what it means that formula f holds 
in a Kripke structure M can be stated as: the initial states of the Kripke 
structure init M need to be contained in the set of all states states M that 
imply f.\<close>
definition check ("_ \<turnstile> _" 50)
 where "M \<turnstile> f \<equiv> (init M) \<subseteq> {s \<in> (states M). s \<in> f }"

definition state_transition_refl (infixr "\<rightarrow>\<^sub>i*" 50)
where "s \<rightarrow>\<^sub>i* s' \<equiv> ((s,s') \<in> {(x,y). state_transition x y}\<^sup>*)"
  
subsection \<open>Lemmas for CTL operators\<close>

subsubsection \<open>EF lemmas\<close>
lemma EF_lem0: "(x \<in> EF f) = (x \<in> f \<union> EX' (lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z)))"
proof -
  have "lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z) = 
                    f \<union> (EX' (lfp (\<lambda>Z :: 'a set. f \<union> EX' Z)))"
    by (rule def_lfp_unfold, rule reflexive, unfold mono_def EX'_def, auto)
  thus "(x \<in> EF (f :: ('a :: state) set)) = (x \<in> f \<union> EX' (lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z)))"
    by (simp add: EF_def) 
qed

lemma EF_lem00: "(EF f) = (f \<union> EX' (lfp (\<lambda> Z :: ('a :: state) set. f \<union> EX' Z)))"
  by (auto simp: EF_lem0)

lemma EF_lem000: "(EF f) = (f \<union> EX' (EF f))"
  by (metis EF_def EF_lem00)

lemma EF_lem1: "x \<in> f \<or> x \<in> (EX' (EF f)) \<Longrightarrow> x \<in> EF f"
proof (simp add: EF_def)
  assume a: "x \<in> f \<or> x \<in> EX' (lfp (\<lambda>Z::'a set. f \<union> EX' Z))"
  show "x \<in> lfp (\<lambda>Z::'a set. f \<union> EX' Z)"
  proof -
    have b: "lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z) =
                    f \<union> (EX' (lfp (\<lambda>Z :: ('a :: state) set. f \<union> EX' Z)))"
      using EF_def EF_lem00 by blast
    thus "x \<in> lfp (\<lambda>Z::'a set. f \<union> EX' Z)" using a
      by (subst b, blast)
  qed   
qed

lemma EF_lem2b: 
  assumes "x \<in> (EX' (EF f))"
  shows "x \<in> EF f"
  by (simp add: EF_lem1 assms)

lemma EF_lem2a: assumes "x \<in> f" shows "x \<in> EF f"
  by (simp add: EF_lem1 assms)

lemma EF_lem2c: assumes "x \<notin> f" shows "x \<in> EF (- f)"
  by (simp add: EF_lem1 assms)

lemma EF_lem2d: assumes "x \<notin> EF f" shows "x \<notin> f"
  using EF_lem1 assms by auto

lemma EF_lem3b: assumes "x \<in> EX' (f \<union> EX' (EF f))" shows "x \<in> (EF f)"
  by (metis EF_lem000 EF_lem2b assms)

lemma EX_lem0l: "x \<in> (EX' f) \<Longrightarrow> x \<in> (EX' (f \<union> g))"
  by (auto simp: EX'_def)

lemma EX_lem0r: "x \<in> (EX' g) \<Longrightarrow> x \<in> (EX' (f \<union> g))"
  by (auto simp: EX'_def)

lemma EX_step: assumes "x  \<rightarrow>\<^sub>i y" and "y \<in> f" shows "x \<in> EX' f"
  using assms by (auto simp: EX'_def)

lemma EF_E[rule_format]: "\<forall> f. x \<in> (EF f) \<longrightarrow> x \<in> (f \<union> EX' (EF f))"
  using EF_lem000 by blast

lemma EF_step: assumes "x  \<rightarrow>\<^sub>i y" and "y \<in> f" shows "x \<in> EF f"
  using EF_lem3b EX_step assms by blast

lemma EF_step_step: assumes "x  \<rightarrow>\<^sub>i y" and "y \<in> EF f" shows  "x \<in> EF f"
  using EF_lem2b EX_step assms by blast

lemma EF_step_star: "\<lbrakk> x  \<rightarrow>\<^sub>i* y; y \<in> f \<rbrakk> \<Longrightarrow> x \<in> EF f"
proof (simp add: state_transition_refl_def)
  show "(x, y) \<in> {(x::'a, y::'a). x \<rightarrow>\<^sub>i y}\<^sup>* \<Longrightarrow> y \<in> f \<Longrightarrow> x \<in> EF f"
  proof (erule converse_rtrancl_induct)
    show "y \<in> f \<Longrightarrow> y \<in> EF f" 
      by (erule EF_lem2a)
    next show "\<And>ya z::'a. y \<in> f \<Longrightarrow>
                 (ya, z) \<in> {(x,y). x \<rightarrow>\<^sub>i y} \<Longrightarrow>
                 (z, y) \<in> {(x,y). x \<rightarrow>\<^sub>i y}\<^sup>* \<Longrightarrow> z \<in> EF f \<Longrightarrow> ya \<in> EF f"
        by (simp add: EF_step_step)
    qed
  qed

lemma EF_induct: "(a::'a::state) \<in> EF f \<Longrightarrow>
    mono (\<lambda> Z. f \<union> EX' Z) \<Longrightarrow>
    (\<And>x. x \<in> ((\<lambda> Z. f \<union> EX' Z)(EF f \<inter> {x::'a::state. P x})) \<Longrightarrow> P x) \<Longrightarrow>
    P a"
  by (metis (mono_tags, lifting) EF_def def_lfp_induct_set)

lemma valEF_E: "M \<turnstile> EF f \<Longrightarrow> x \<in> init M \<Longrightarrow> x \<in> EF f"
  by (auto simp: check_def)

lemma EF_step_star_rev[rule_format]: "x \<in> EF s \<Longrightarrow>  (\<exists> y \<in> s.  x  \<rightarrow>\<^sub>i* y)"
proof (erule EF_induct)
  show "mono (\<lambda>Z::'a set. s \<union> EX' Z)"
    by (force simp add: mono_def EX'_def)
next show "\<And>x::'a. x \<in> s \<union> EX' (EF s \<inter> {x::'a. \<exists>y::'a\<in>s. x \<rightarrow>\<^sub>i* y}) \<Longrightarrow> \<exists>y::'a\<in>s. x \<rightarrow>\<^sub>i* y"
    apply (erule UnE)
    using state_transition_refl_def apply auto[1]
    by (auto simp add: EX'_def state_transition_refl_def intro: converse_rtrancl_into_rtrancl)
qed

lemma EF_step_inv: "(I \<subseteq> {sa::'s :: state. (\<exists>i\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF s})  
         \<Longrightarrow> \<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y"
  using EF_step_star_rev by fastforce
  
subsubsection \<open>AG lemmas\<close> 

lemma AG_in_lem:   "x \<in> AG s \<Longrightarrow> x \<in> s"  
  by (auto simp add: AG_def gfp_def)

lemma AG_lem1: "x \<in> s \<and> x \<in> (AX (AG s)) \<Longrightarrow> x \<in> AG s"
proof (simp add: AG_def)
  have "gfp (\<lambda>Z::'a set. s \<inter> AX Z) = s \<inter> (AX (gfp (\<lambda>Z::'a set. s \<inter> AX Z)))"
    by (rule def_gfp_unfold) (auto simp: mono_def AX_def)
  then show "x \<in> s \<and> x \<in> AX (gfp (\<lambda>Z::'a set. s \<inter> AX Z)) \<Longrightarrow> x \<in> gfp (\<lambda>Z::'a set. s \<inter> AX Z)"
    by blast
qed

lemma AG_lem2: "x \<in> AG s \<Longrightarrow> x \<in> (s \<inter> (AX (AG s)))"
proof -
  have a: "AG s = s \<inter> (AX (AG s))"
    unfolding AG_def
    by (rule def_gfp_unfold) (auto simp: mono_def AX_def)
  thus "x \<in> AG s \<Longrightarrow> x \<in> (s \<inter> (AX (AG s)))"
   by (erule subst)
qed

lemma AG_lem3: "AG s = (s \<inter> (AX (AG s)))"    
  using AG_lem1 AG_lem2 by blast

lemma AG_step: "y \<rightarrow>\<^sub>i z \<Longrightarrow> y \<in> AG s \<Longrightarrow> z \<in> AG s"
  using AG_lem2 AX_def by blast  

lemma AG_all_s: " x \<rightarrow>\<^sub>i* y \<Longrightarrow> x \<in> AG s \<Longrightarrow> y \<in> AG s"
proof (simp add: state_transition_refl_def)
  show "(x, y) \<in> {(x,y). x \<rightarrow>\<^sub>i y}\<^sup>* \<Longrightarrow> x \<in> AG s \<Longrightarrow> y \<in> AG s" 
    by (erule rtrancl_induct) (auto simp add: AG_step)
qed

lemma AG_imp_notnotEF: 
"I \<noteq> {} \<Longrightarrow> ((Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I  \<turnstile> AG s)) \<Longrightarrow> 
 (\<not>(Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF (- s)))"
proof (rule notI, simp add: check_def)
  assume a0: "I \<noteq> {}" and
    a1: "I \<subseteq> {sa::'s. (\<exists>i\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s}" and
    a2: "I \<subseteq> {sa::'s. (\<exists>i\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)}" 
  show "False"
  proof - 
    have a3: "{sa::'s. (\<exists>i\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s} \<inter>
                        {sa::'s. (\<exists>i\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)} = {}"
      proof -
        have "(? x. x \<in> {sa::'s. (\<exists>i\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s} \<and>
                           x \<in> {sa::'s. (\<exists>i\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)}) \<Longrightarrow> False"
        proof -
          assume a4: "(? x. x \<in> {sa::'s. (\<exists>i\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s} \<and>
                           x \<in> {sa::'s. (\<exists>i\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)})"          
            from a4 obtain x where  a5: "x \<in> {sa::'s. (\<exists>i\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s} \<and>
                                   x \<in> {sa::'s. (\<exists>i\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)}"
            by (erule exE) 
            thus "False"
              by (metis (mono_tags, lifting) AG_all_s AG_in_lem ComplD EF_step_star_rev a5 mem_Collect_eq)
          qed
        thus "{sa::'s. (\<exists>i\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> AG s} \<inter>
                        {sa::'s. (\<exists>i\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF (- s)} = {}"
        by blast
      qed
    moreover have b: "? x. x : I" using a0
      by blast
    moreover obtain x where "x \<in> I"
      using b by blast 
    ultimately show "False" using a0 a1 a2
      by blast
  qed
qed

text \<open>A simplified way of Modelchecking is given by the following lemma.\<close>
lemma check2_def: "(Kripke S I \<turnstile> f) = (I \<subseteq> S \<inter> f)" 
  by (auto simp add: check_def)
    
end