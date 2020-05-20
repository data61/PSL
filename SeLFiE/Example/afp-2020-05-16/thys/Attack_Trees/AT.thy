section "Attack Trees"
theory AT
imports MC 
begin

text \<open>Attack Trees are an intuitive and practical formal method to analyse and quantify
attacks on security and privacy. They are very useful to identify the steps an attacker
takes through a system when approaching the attack goal. Here, we provide 
a proof calculus to analyse concrete attacks using a notion of attack validity.
We define a state based semantics with Kripke models and the temporal logic
CTL in the proof assistant Isabelle \cite{npw:02} using its Higher Order Logic 
(HOL). We prove the correctness and completeness (adequacy) of Attack Trees in Isabelle 
with respect to the model.\<close>

subsection "Attack Tree datatype"
text \<open>The following datatype definition @{text \<open>attree\<close>} defines attack trees.
The simplest case of an attack tree is a base attack.
The principal idea is that base attacks are defined by a pair of
state sets representing the initial states and the {\it attack property}
-- a set of states characterized by the fact that this property holds
in them. 
Attacks can also be combined as the conjunction or disjunction of other attacks. 
The operator @{text \<open>\<oplus>\<^sub>\<or>\<close>} creates or-trees and @{text \<open>\<oplus>\<^sub>\<and>\<close>} creates and-trees.
And-attack trees @{text \<open>l \<oplus>\<^sub>\<and> s\<close>} and or-attack trees @{text \<open>l \<oplus>\<^sub>\<or> s\<close>} 
combine lists of attack trees $l$ either conjunctively or disjunctively and
consist of a list of sub-attacks -- again attack trees.\<close>
datatype ('s :: state) attree = BaseAttack "('s set) * ('s set)" ("\<N>\<^bsub>(_)\<^esub>") |
                  AndAttack "('s attree) list" "('s set) * ('s set)" ("_ \<oplus>\<^sub>\<and>\<^bsup>(_)\<^esup>" 60) | 
                  OrAttack  "('s attree) list" "('s set) * ('s set)" ("_ \<oplus>\<^sub>\<or>\<^bsup>(_)\<^esup>" 61)

primrec attack :: "('s :: state) attree \<Rightarrow> ('s set) * ('s set)"
  where 
"attack (BaseAttack b) = b"|
"attack (AndAttack as s) = s"  | 
"attack (OrAttack as s) = s"

subsection \<open>Attack Tree refinement\<close>
text \<open>When we develop an attack tree, we proceed from an abstract attack, given
by an attack goal, by breaking it down into a series of sub-attacks. This
proceeding corresponds to a process of {\it refinement}. Therefore, as part of
the attack tree calculus, we provide a notion of attack tree refinement.

The relation @{text \<open>refines_to\<close>} "constructs" the attack tree. Here the above
defined attack vectors are used to define how nodes in an attack tree 
can be expanded into more detailed (refined) attack sequences. This 
process of refinement @{text "\<sqsubseteq>"} allows to eventually reach a fully detailed
attack that can then be proved using @{text "\<turnstile>"}.\<close>
inductive refines_to :: "[('s :: state) attree, 's attree] \<Rightarrow> bool" ("_ \<sqsubseteq> _" [40] 40)
where 
refI: "\<lbrakk>  A = ((l @ [ \<N>\<^bsub>(si',si'')\<^esub>] @ l'')\<oplus>\<^sub>\<and>\<^bsup>(si,si''')\<^esup> );
          A' = (l' \<oplus>\<^sub>\<and>\<^bsup>(si',si'')\<^esup>);
          A'' = (l @ l' @ l'' \<oplus>\<^sub>\<and>\<^bsup>(si,si''')\<^esup>)
        \<rbrakk> \<Longrightarrow> A \<sqsubseteq> A''"| 
ref_or: "\<lbrakk> as \<noteq> []; \<forall> A' \<in> set(as). (A  \<sqsubseteq> A') \<and> attack A = s \<rbrakk> \<Longrightarrow> A \<sqsubseteq> (as \<oplus>\<^sub>\<or>\<^bsup>s\<^esup>)" |
ref_trans: "\<lbrakk> A \<sqsubseteq> A'; A' \<sqsubseteq> A'' \<rbrakk> \<Longrightarrow> A \<sqsubseteq> A''"|
ref_refl : "A \<sqsubseteq> A"


subsection \<open>Validity of Attack Trees\<close>
text \<open>A valid attack, intuitively, is one which is fully refined into fine-grained
attacks that are feasible in a model. The general model we provide is
a Kripke structure, i.e., a set of states and a generic state transition.
Thus, feasible steps in the model are single steps of the state transition.
We call them valid base attacks.
The composition of sequences of valid base attacks into and-attacks yields
again valid attacks if the base attacks line up with respect to the states
in the state transition. If there are different valid attacks for the same
attack goal starting from the same initial state set, these can be 
summarized in an or-attack.
More precisely, the different cases of the validity predicate are distinguished
by pattern matching over the attack tree structure.
\begin{itemize}
\item A  base attack @{text \<open>\<N>(s0,s1)\<close>} is  valid if from all
states in the pre-state set @{text \<open>s0\<close>} we can get with a single step of the 
state transition relation to a state in the post-state set \<open>s1\<close>. Note,
that it is sufficient for a post-state to exist for each pre-state. After all,
we are aiming to validate attacks, that is, possible attack paths to some
state that fulfills the attack property.
\item An and-attack @{text \<open>As \<oplus>\<^sub>\<and> (s0,s1)\<close>} is a valid attack
 if either of the following cases holds:
  \begin{itemize}
   \item empty attack sequence @{text \<open>As\<close>}: in this case 
       all pre-states in @{text \<open>s0\<close>} must already be attack states 
       in @{text \<open>s1\<close>}, i.e., @{text \<open>s0 \<subseteq> s1\<close>};
   \item attack sequence @{text \<open>As\<close>} is singleton: in this case, the 
      singleton element attack @{text \<open>a\<close>} in @{text \<open>[a]\<close>}, 
      must be a valid attack and it must be an attack with pre-state 
      @{text \<open>s0\<close>} and post-state @{text \<open>s1\<close>};
   \item otherwise, @{text \<open>As\<close>} must be a list matching @{text \<open>a # l\<close>} for
     some attack @{text \<open>a\<close>} and tail of attack list @{text \<open>l\<close>} such that
     @{text \<open>a\<close>} is a valid attack with pre-state identical to the overall 
     pre-state @{text \<open>s0\<close>} and the goal of the tail @{text \<open>l\<close>} is 
     @{text \<open>s1\<close>} the goal of the  overall attack. The pre-state of the
     attack represented by @{text \<open>l\<close>} is @{text \<open>snd(attack a)\<close>} since this is 
     the post-state set of the first step @{text \<open>a\<close>}.
\end{itemize}
 \item An or-attack @{text \<open>As  \<oplus>\<^sub>\<or>(s0,s1)\<close>} is a valid attack 
  if either of the following cases holds: 
  \begin{itemize}
   \item the empty attack case is identical to the and-attack above: 
       @{text \<open>s0 \<subseteq> s1\<close>};
   \item attack sequence @{text \<open>As\<close>} is singleton: in this case, the 
      singleton element attack @{text \<open>a\<close>}
      must be a valid attack and 
      its pre-state must include the overall attack pre-state set @{text \<open>s0\<close>} 
      (since @{text \<open>a\<close>} is singleton in the or) while the post-state of 
      @{text \<open>a\<close>} needs to be included in the global attack goal @{text \<open>s1\<close>};
   \item otherwise, @{text \<open>As\<close>} must be a list  @{text \<open>a # l\<close>} for
     an attack @{text \<open>a\<close>} and a list @{text \<open>l\<close>} of alternative attacks.
     The pre-states can be just a subset of @{text \<open>s0\<close>} (since there are
     other attacks in @{text \<open>l\<close>} that can cover the rest) and the goal
     states @{text \<open>snd(attack a)\<close>} need to lie all in the overall goal
     state @{text \<open>set s1\<close>}. The other or-attacks in @{text \<open>l\<close>} need
     to cover only the pre-states @{text \<open>fst s - fst(attack a)\<close>}
     (where @{text \<open>-\<close>} is set difference) and have the same goal @{text \<open>snd s\<close>}.
   \end{itemize}
\end{itemize}
The proof calculus is thus completely described by one recursive function. \<close>
fun is_attack_tree :: "[('s :: state) attree] \<Rightarrow> bool"  ("\<turnstile>_" [40] 40) 
where 
att_base:  "(\<turnstile> \<N>\<^bsub>s\<^esub>) = ( (\<forall> x \<in> (fst s). (\<exists> y \<in> (snd s). x  \<rightarrow>\<^sub>i y )))" |
att_and: "(\<turnstile>(As \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>)) = 
               (case As of
                  [] \<Rightarrow> (fst s \<subseteq> snd s)
                | [a] \<Rightarrow> ( \<turnstile> a \<and> attack a = s) 
                | (a # l) \<Rightarrow> (( \<turnstile> a) \<and> (fst(attack a) = fst s) \<and> 
                            (\<turnstile>(l \<oplus>\<^sub>\<and>\<^bsup>(snd(attack a),snd(s))\<^esup>))))" |
att_or: "(\<turnstile>(As \<oplus>\<^sub>\<or>\<^bsup>s\<^esup>)) = 
               (case As of 
                  [] \<Rightarrow> (fst s \<subseteq> snd s) 
                | [a] \<Rightarrow> ( \<turnstile> a \<and> (fst(attack a) \<supseteq> fst s) \<and> (snd(attack a) \<subseteq> snd s)) 
                | (a # l) \<Rightarrow> (( \<turnstile> a) \<and> fst(attack a) \<subseteq> fst s \<and> 
                              snd(attack a) \<subseteq> snd s \<and>
                       ( \<turnstile>(l \<oplus>\<^sub>\<or>\<^bsup>(fst s - fst(attack a), snd s)\<^esup>))))" 
text \<open>Since the definition is constructive, code can be generated directly from it, here
into the programming language Scala.\<close>
export_code is_attack_tree in Scala    

subsection "Lemmas for Attack Tree validity"
lemma att_and_one: assumes "\<turnstile> a" and  "attack a = s"
  shows  "\<turnstile>([a] \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>)"
proof -
  show " \<turnstile>([a] \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>)" using assms
    by (subst att_and, simp del: att_and att_or)
qed

declare is_attack_tree.simps[simp del]
  
lemma att_and_empty[rule_format] : " \<turnstile>([] \<oplus>\<^sub>\<and>\<^bsup>(s', s'')\<^esup>) \<longrightarrow> s' \<subseteq> s''"
  by (simp add: is_attack_tree.simps(2))

lemma att_and_empty2: " \<turnstile>([] \<oplus>\<^sub>\<and>\<^bsup>(s, s)\<^esup>)"
  by (simp add: is_attack_tree.simps(2))

lemma att_or_empty[rule_format] : " \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>(s', s'')\<^esup>) \<longrightarrow> s' \<subseteq> s''"
  by (simp add: is_attack_tree.simps(3))

lemma att_or_empty_back[rule_format]: " s' \<subseteq> s'' \<longrightarrow>  \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>(s', s'')\<^esup>)"
  by (simp add: is_attack_tree.simps(3))

lemma att_or_empty_rev: assumes "\<turnstile>(l \<oplus>\<^sub>\<or>\<^bsup>(s, s')\<^esup>)" and "\<not>(s \<subseteq> s')" shows "l \<noteq> []"    
  using assms att_or_empty by blast

lemma att_or_empty2: "\<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>(s, s)\<^esup>)"
  by (simp add: att_or_empty_back)

lemma att_andD1: " \<turnstile>(x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>) \<Longrightarrow> \<turnstile> x1"
  by (metis (no_types, lifting) is_attack_tree.simps(2) list.exhaust list.simps(4) list.simps(5))

lemma att_and_nonemptyD2[rule_format]: 
       "(x2 \<noteq> [] \<longrightarrow> \<turnstile>(x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>) \<longrightarrow> \<turnstile> (x2 \<oplus>\<^sub>\<and>\<^bsup>(snd(attack x1),snd s)\<^esup>))" 
  by (metis (no_types, lifting) is_attack_tree.simps(2) list.exhaust list.simps(5)) 

lemma att_andD2 : " \<turnstile>(x1 # x2 \<oplus>\<^sub>\<and>\<^bsup>s\<^esup>) \<Longrightarrow> \<turnstile> (x2 \<oplus>\<^sub>\<and>\<^bsup>(snd(attack x1),snd s)\<^esup>)" 
  by (metis (mono_tags, lifting) att_and_empty2 att_and_nonemptyD2 is_attack_tree.simps(2) list.simps(4) list.simps(5))
    
lemma att_and_fst_lem[rule_format]: 
   "\<turnstile>(x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<longrightarrow> xa \<in> fst (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>))
                     \<longrightarrow> xa \<in> fst (attack x1)"  
  by (induction x2a, (subst att_and, simp)+)

lemma att_orD1: " \<turnstile>(x1 # x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<Longrightarrow> \<turnstile> x1"
  by (case_tac x2, (subst (asm) att_or, simp)+)
    
lemma att_or_snd_hd: " \<turnstile>(a # list \<oplus>\<^sub>\<or>\<^bsup>(aa, b)\<^esup>) \<Longrightarrow> snd(attack a) \<subseteq> b"
  by (case_tac list,  (subst (asm) att_or, simp)+)
 
lemma att_or_singleton[rule_format]: 
   " \<turnstile>([x1] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow> \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>(fst x - fst (attack x1), snd x)\<^esup>)" 
  by (subst att_or, simp, rule impI, rule att_or_empty_back, blast)

lemma att_orD2[rule_format]: 
     " \<turnstile>(x1 # x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow>  \<turnstile> (x2 \<oplus>\<^sub>\<or>\<^bsup>(fst x - fst(attack x1), snd x)\<^esup>)"
  by (case_tac x2, simp add: att_or_singleton, simp, subst att_or, simp)

lemma att_or_snd_att[rule_format]: "\<forall> x. \<turnstile> (x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>) \<longrightarrow> (\<forall> a \<in> (set x2). snd(attack a) \<subseteq> snd x )" 
proof (induction x2)
  case Nil
  then show ?case by (simp add: att_or)
next
  case (Cons a x2)
  then show ?case using att_orD2 att_or_snd_hd by fastforce
qed

lemma singleton_or_lem: " \<turnstile>([x1] \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>)  \<Longrightarrow> fst x \<subseteq> fst(attack x1)"
  by (subst (asm) att_or, simp)+

lemma or_att_fst_sup0[rule_format]: "x2 \<noteq> [] \<longrightarrow> (\<forall> x. (\<turnstile> ((x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>):: ('s :: state) attree)) \<longrightarrow>
                      ((\<Union> y::'s attree\<in> set x2. fst (attack y)) \<supseteq> fst(x))) "
proof (induction x2)
  case Nil
  then show ?case by simp
next
  case (Cons a x2)
  then show ?case using att_orD2 singleton_or_lem by fastforce
qed

lemma or_att_fst_sup: 
    assumes "(\<turnstile> ((x1 # x2 \<oplus>\<^sub>\<or>\<^bsup>x\<^esup>):: ('s :: state) attree))"
    shows   "((\<Union> y::'s attree\<in> set (x1 # x2). fst (attack y)) \<supseteq> fst(x))"
  by (rule or_att_fst_sup0, simp, rule assms)

text \<open>The lemma @{text \<open>att_elem_seq\<close>} is the main lemma for Correctness.
  It shows that for a given attack tree x1, for each element in the set of start sets 
  of the first attack, we can reach in zero or more steps a state in the states in which 
  the attack is successful (the final attack state @{text \<open>snd(attack x1)\<close>}).
  This proof is a big alternative to an earlier version of the proof with
  @{text \<open>first_step\<close>} etc that mapped first on a sequence of sets of states.\<close>
lemma att_elem_seq[rule_format]: "\<turnstile> x1 \<longrightarrow> (\<forall> x \<in> fst(attack x1).
                     (\<exists> y. y \<in> snd(attack x1) \<and> x \<rightarrow>\<^sub>i* y))"
  text \<open>First attack tree induction\<close>
proof (induction x1)
  case (BaseAttack x)
  then show ?case
    by (metis AT.att_base EF_step EF_step_star_rev attack.simps(1))
next
  case (AndAttack x1a x2)
  then show ?case
    apply (rule_tac x = x2 in spec)
    apply (subgoal_tac "(\<forall> x1aa::'a attree.
                              x1aa \<in> set x1a \<longrightarrow>
                               \<turnstile>x1aa \<longrightarrow>
                               (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y))")
     apply (rule mp)
      prefer 2
      apply (rotate_tac -1)
      apply assumption
    text \<open>Induction for @{text \<open>\<and>\<close>}: the manual instantiation seems tedious but in the @{text \<open>\<and>\<close>} 
            case necessary to get the right induction hypothesis.\<close>
  proof (rule_tac list = "x1a" in list.induct)
    text \<open>The @{text \<open>\<and>\<close>} induction empty case\<close>
    show "(\<forall>x1aa::'a attree.
           x1aa \<in> set [] \<longrightarrow>
           \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<longrightarrow>
       (\<forall>x::'a set \<times> 'a set.
           \<turnstile>([] \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<longrightarrow>
           (\<forall>xa::'a\<in>fst (attack ([] \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack ([] \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y))"
      using att_and_empty state_transition_refl_def by fastforce
    text \<open>The @{text \<open>\<and>\<close>} induction case nonempty\<close>
  next show "\<And>(x1a::'a attree list) (x2::'a set \<times> 'a set) (x1::'a attree) (x2a::'a attree list).
       (\<And>x1aa::'a attree.
           (x1aa \<in> set x1a) \<Longrightarrow>
           ((\<turnstile>x1aa) \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y))) \<Longrightarrow>
       \<forall>x1aa::'a attree.
          (x1aa \<in> set x1a) \<longrightarrow>
          (\<turnstile>x1aa) \<longrightarrow> ((\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<Longrightarrow>
       (\<forall>x1aa::'a attree.
           (x1aa \<in> set x2a) \<longrightarrow>
           (\<turnstile>x1aa) \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y)) \<longrightarrow>
       (\<forall>x::'a set \<times> 'a set.
           (\<turnstile>(x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<longrightarrow>
           ((\<forall>xa::'a\<in>fst (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y))) \<Longrightarrow>
       ((\<forall>x1aa::'a attree.
           (x1aa \<in> set (x1 # x2a)) \<longrightarrow>
           (\<turnstile>x1aa) \<longrightarrow> ((\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y))) \<longrightarrow>
       (\<forall>x::'a set \<times> 'a set.
          ( \<turnstile>(x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<longrightarrow>
           (\<forall>xa::'a\<in>fst (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)).
               (\<exists>y::'a. y \<in> snd (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> (xa \<rightarrow>\<^sub>i* y)))))"
      apply (rule impI, rule allI, rule impI)
      text \<open>Set free the Induction Hypothesis: this is necessary to provide the grounds for specific 
              instantiations in the step.\<close>
      apply (subgoal_tac "(\<forall>x::'a set \<times> 'a set.
                             \<turnstile>(x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<longrightarrow>
                             (\<forall>xa::'a\<in>fst (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)).
                              \<exists>y::'a. y \<in> snd (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y))")
       prefer 2
       apply simp
      text \<open>The following induction step for @{text \<open>\<and>\<close>} needs a number of manual instantiations 
              so that the proof is not found automatically. In the subsequent case for @{text \<open>\<or>\<close>}, 
              sledgehammer finds the proof.\<close>
    proof -
      show "\<And>(x1a::'a attree list) (x2::'a set \<times> 'a set) (x1::'a attree) (x2a::'a attree list) x::'a set \<times> 'a set.
       \<forall>x1aa::'a attree.
          x1aa \<in> set (x1 # x2a) \<longrightarrow>
          \<turnstile>x1aa \<longrightarrow> (\<forall>x::'a\<in>fst (attack x1aa). \<exists>y::'a. y \<in> snd (attack x1aa) \<and> x \<rightarrow>\<^sub>i* y) \<Longrightarrow>
       \<turnstile>(x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<Longrightarrow>
       \<forall>x::'a set \<times> 'a set.
          \<turnstile>(x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>) \<longrightarrow>
          (\<forall>xa::'a\<in>fst (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y) \<Longrightarrow>
       \<forall>xa::'a\<in>fst (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)). \<exists>y::'a. y \<in> snd (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) \<and> xa \<rightarrow>\<^sub>i* y"
        apply (rule ballI)
        apply (rename_tac xa)
        text \<open>Prepare the steps\<close> 
        apply (drule_tac x = "(snd(attack x1), snd x)" in spec)
        apply (rotate_tac -1)
        apply (erule impE)
         apply (erule att_andD2)
        text \<open>Premise for x1\<close>
        apply (drule_tac x = x1 in spec)
        apply (drule mp)
         apply simp
        apply (drule mp)
         apply (erule att_andD1)
        text \<open>Instantiate first step for xa\<close>
        apply (rotate_tac -1)
        apply (drule_tac x = xa in bspec)
         apply (erule att_and_fst_lem, assumption)
        apply (erule exE)
        apply (erule conjE)
        text \<open>Take this y and put it as first into the second part\<close>
        apply (drule_tac x = y in bspec)
         apply simp
        apply (erule exE)
        apply (erule conjE)
        text \<open>Bind the first @{text \<open>xa \<rightarrow>\<^sub>i* y\<close>} and second @{text \<open>y \<rightarrow>\<^sub>i* ya\<close>} together for solution\<close>
        apply (rule_tac x = ya in exI)
        apply (rule conjI)
         apply simp
        by (simp add: state_transition_refl_def)
    qed
  qed auto
next
  case (OrAttack x1a x2)
  then show ?case
  proof (induction x1a arbitrary: x2)
    case Nil
    then show ?case
      by (metis EF_lem2a EF_step_star_rev att_or_empty attack.simps(3) subsetD surjective_pairing)
  next
    case (Cons a x1a)
    then show ?case
      by (smt DiffI att_orD1 att_orD2 att_or_snd_att attack.simps(3) insert_iff list.set(2) prod.sel(1) snd_conv subset_iff) 
  qed
qed

  
lemma att_elem_seq0: "\<turnstile> x1 \<Longrightarrow> (\<forall> x \<in> fst(attack x1).
                     (\<exists> y. y \<in> snd(attack x1) \<and> x \<rightarrow>\<^sub>i* y))"
  by (simp add: att_elem_seq)
          
subsection \<open>Valid refinements\<close>
definition valid_ref :: "[('s :: state) attree, 's attree] \<Rightarrow> bool" ("_ \<sqsubseteq>\<^sub>V _" 50)
  where
"A \<sqsubseteq>\<^sub>V A' \<equiv>  ( (A \<sqsubseteq> A') \<and>  \<turnstile> A')"

definition ref_validity :: "[('s :: state) attree] \<Rightarrow> bool" ("\<turnstile>\<^sub>V _" 50)
  where
"\<turnstile>\<^sub>V A  \<equiv>  (\<exists> A'. (A \<sqsubseteq>\<^sub>V A'))"

lemma ref_valI: " A \<sqsubseteq> A'\<Longrightarrow>  \<turnstile> A' \<Longrightarrow> \<turnstile>\<^sub>V A"
  using ref_validity_def valid_ref_def by blast

section "Correctness and Completeness"
text \<open>This section presents the main theorems of Correctness and Completeness
      between AT and Kripke, essentially: 

@{text \<open>\<turnstile> (init K, p) \<equiv>  K \<turnstile> EF p\<close>}.

First, we proof a number of lemmas needed for both directions before we 
show the Correctness theorem followed by the Completeness theorem.
\<close>    
subsection \<open>Lemma for Correctness and Completeness\<close>
lemma nth_app_eq[rule_format]: 
              "\<forall> sl x. sl \<noteq> [] \<longrightarrow> sl ! (length sl - Suc (0)) = x
              \<longrightarrow> (l @ sl) ! (length l + length sl - Suc (0)) = x"    
  by (induction l) auto

lemma nth_app_eq1[rule_format]: "i < length sla \<Longrightarrow> (sla @ sl) ! i = sla ! i"
  by (simp add: nth_append)

lemma nth_app_eq1_rev:   "i < length sla \<Longrightarrow>  sla ! i = (sla @ sl) ! i"
  by (simp add: nth_append)

lemma nth_app_eq2[rule_format]: "\<forall> sl i. length sla \<le> i \<and> i < length (sla @ sl)
                     \<longrightarrow> (sla @ sl) ! i = sl ! (i - (length sla))"
  by (simp add: nth_append)


lemma tl_ne_ex[rule_format]: "l \<noteq> [] \<longrightarrow> (? x . l = x # (tl l))"
  by (induction l, auto)


lemma tl_nempty_lngth[rule_format]: "tl sl \<noteq> [] \<longrightarrow> 2 \<le> length(sl)"
  using le_less by fastforce
  
lemma list_app_one_length: "length l = n \<Longrightarrow> (l @ [s]) ! n = s"
  by (erule subst, simp)
  
lemma tl_lem1[rule_format]: "l \<noteq> [] \<longrightarrow> tl l = [] \<longrightarrow> length l = 1"
  by (induction l, simp+)

lemma nth_tl_length[rule_format]: "tl sl \<noteq> [] \<longrightarrow>
      tl sl ! (length (tl sl) - Suc (0)) = sl ! (length sl - Suc (0))" 
  by (induction sl, simp+)

lemma nth_tl_length1[rule_format]: "tl sl \<noteq> [] \<longrightarrow>
      tl sl ! n = sl ! (n + 1)" 
  by (induction sl, simp+)
   
lemma ineq1: "i < length sla - n  \<Longrightarrow>
       (0) \<le> n \<Longrightarrow> i < length sla"  
by simp

lemma ineq2[rule_format]: "length sla \<le> i \<longrightarrow> i + (1) - length sla = i - length sla + 1"
by arith

lemma ineq3: "tl sl \<noteq> []  \<Longrightarrow> length sla \<le> i \<Longrightarrow> i < length (sla @ tl sl) - (1)
              \<Longrightarrow> i - length sla + (1) < length sl - (1)"    
by simp

lemma tl_eq1[rule_format]: "sl \<noteq> [] \<longrightarrow> tl sl ! (0) = sl ! Suc (0)"  
  by (induction sl, simp+)

lemma tl_eq2[rule_format]: "tl sl = [] \<longrightarrow> sl ! (0) = sl ! (length sl - (1))"
  by (induction sl, simp+)

lemma tl_eq3[rule_format]: "tl sl \<noteq> [] \<longrightarrow>
    tl sl ! (length sl - Suc (Suc (0))) = sl ! (length sl - Suc (0))"    
  by (induction sl, simp+)

lemma nth_app_eq3: assumes "tl sl \<noteq> []"
  shows "(sla @ tl sl) ! (length (sla @ tl sl) - (1)) = sl ! (length sl - (1))"
  using assms nth_app_eq nth_tl_length by fastforce 

lemma not_empty_ex: "A \<noteq> {} \<Longrightarrow> ? x. x \<in> A"
by force

lemma fst_att_eq: "(fst x # sl) ! (0) = fst (attack (al \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>))"
by simp

lemma list_eq1[rule_format]: "sl \<noteq> [] \<longrightarrow>
     (fst x # sl) ! (length (fst x # sl) - (1)) = sl ! (length sl - (1))"
  by (induction sl, auto)

lemma attack_eq1: "snd (attack (x1 # x2a \<oplus>\<^sub>\<and>\<^bsup>x\<^esup>)) = snd (attack (x2a \<oplus>\<^sub>\<and>\<^bsup>(snd (attack x1), snd x)\<^esup>))"
by simp

lemma fst_lem1[rule_format]: "\<forall> (a:: 's set) b (c :: 's set) d. (a, c) = (b, d) \<longrightarrow> a = b"
by auto

lemma fst_eq1: "(sla ! (0), y) = attack x1 \<Longrightarrow>
       sla ! (0) = fst (attack x1)"
  by (rule_tac c = y and d = "snd(attack  x1)" in fst_lem1, simp)
    
lemma base_att_lem1: " y0 \<subseteq> y1 \<Longrightarrow> \<turnstile> \<N>\<^bsub>(y1, y)\<^esub> \<Longrightarrow>\<turnstile> \<N>\<^bsub>(y0, y)\<^esub>"
  by (simp add: att_base, blast)

lemma ref_pres_att: "A \<sqsubseteq> A' \<Longrightarrow> attack A = attack A'"
proof (erule refines_to.induct)
  show "\<And>(A::'a attree) (l::'a attree list) (si'::'a set) (si''::'a set) (l''::'a attree list) (si::'a set)
       (si'''::'a set) (A'::'a attree) (l'::'a attree list) A''::'a attree.
       A = (l @ [\<N>\<^bsub>(si', si'')\<^esub>] @ l'' \<oplus>\<^sub>\<and>\<^bsup>(si, si''')\<^esup>) \<Longrightarrow>
       A' = (l' \<oplus>\<^sub>\<and>\<^bsup>(si', si'')\<^esup>) \<Longrightarrow> A'' = (l @ l' @ l'' \<oplus>\<^sub>\<and>\<^bsup>(si, si''')\<^esup>) \<Longrightarrow> attack A = attack A''"
    by simp
next show "\<And>(as::'a attree list) (A::'a attree) (s::'a set \<times> 'a set).
       as \<noteq> [] \<Longrightarrow>
       (\<forall>A'::'a attree\<in> (set as). ((A \<sqsubseteq> A') \<and> (attack A = attack A')) \<and> attack A = s) \<Longrightarrow>
       attack A = attack (as \<oplus>\<^sub>\<or>\<^bsup>s\<^esup>)"
    using last_in_set by auto
next show "\<And>(A::'a attree) (A'::'a attree) A''::'a attree.
       A \<sqsubseteq> A' \<Longrightarrow> attack A = attack A' \<Longrightarrow> A' \<sqsubseteq> A'' \<Longrightarrow> attack A' = attack A'' \<Longrightarrow> attack A = attack A''"
    by simp
next show "\<And>A::'a attree. attack A = attack A" by (rule refl)
qed

lemma  base_subset: 
    assumes "xa \<subseteq> xc"
    shows  "\<turnstile>\<N>\<^bsub>(x, xa)\<^esub> \<Longrightarrow> \<turnstile>\<N>\<^bsub>(x, xc)\<^esub>" 
proof (simp add: att_base)
  show " \<forall>x::'a\<in>x. \<exists>xa::'a\<in>xa. x \<rightarrow>\<^sub>i xa \<Longrightarrow> \<forall>x::'a\<in>x. \<exists>xa::'a\<in>xc. x \<rightarrow>\<^sub>i xa"
    by (meson assms in_mono)
qed

subsection "Correctness Theorem"
text \<open>Proof with induction over the definition of EF using the main 
lemma @{text \<open>att_elem_seq0\<close>}. 

There is also a second version of Correctness for valid refinements.\<close>

theorem AT_EF: assumes " \<turnstile> (A :: ('s :: state) attree)"
               and  "attack A = (I,s)"
               shows "Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF s"
proof (simp add:check_def)
  show "I \<subseteq> {sa::('s :: state). (\<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* sa) \<and> sa \<in> EF s}" 
  proof (rule subsetI, rule CollectI, rule conjI, simp add: state_transition_refl_def)
    show "\<And>x::'s. x \<in> I \<Longrightarrow> \<exists>i::'s\<in>I. (i, x) \<in> {(x::'s, y::'s). x \<rightarrow>\<^sub>i y}\<^sup>*"
    by (rule_tac x = x in bexI, simp)
next show "\<And>x::'s. x \<in> I \<Longrightarrow> x \<in> EF s" using assms
  proof -
    have a: "\<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y" using assms
    proof -
      have "\<forall>x::'s\<in>fst (attack A). \<exists>y::'s. y \<in> snd (attack A) \<and> x \<rightarrow>\<^sub>i* y"
        by (rule att_elem_seq0, rule assms)
      thus " \<forall>x::'s\<in>I. \<exists>y::'s\<in>s. x \<rightarrow>\<^sub>i* y" using assms
      by force  
    qed
    thus "\<And>x::'s. x \<in> I \<Longrightarrow> x \<in> EF s" 
    proof -
      fix x
      assume b: "x \<in> I"
      have "\<exists>y::'s\<in>s::('s :: state) set. x \<rightarrow>\<^sub>i* y" 
        by (rule_tac x = x and A = I in bspec, rule a, rule b)
      from this obtain y where "y \<in> s" and "x \<rightarrow>\<^sub>i* y" by (erule bexE)
      thus "x \<in> EF s" 
       by (erule_tac f = s in EF_step_star)
   qed  
  qed
 qed
qed

theorem ATV_EF: "\<lbrakk> \<turnstile>\<^sub>V A; (I,s) = attack A \<rbrakk> \<Longrightarrow>
 (Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s) } I  \<turnstile> EF s)"
  by (metis (full_types) AT_EF ref_pres_att ref_validity_def valid_ref_def) 
    
subsection "Completeness Theorem"
text \<open>This section contains the completeness direction, informally:

@{text \<open>\<turnstile> EF s \<Longrightarrow> \<exists> A. \<turnstile> A \<and> attack A = (I,s)\<close>}.

The main theorem is presented last since its
proof just summarises a number of main lemmas @{text \<open>Compl_step1, Compl_step2,
Compl_step3, Compl_step4\<close>} which are presented first together with other
auxiliary lemmas.\<close>

subsubsection "Lemma @{text \<open>Compl_step1\<close>}"
lemma Compl_step1: 
"Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I  \<turnstile> EF s 
\<Longrightarrow> \<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y"
  by (simp add: EF_step_star_rev valEF_E)

subsubsection "Lemma @{text \<open>Compl_step2\<close>}"
text \<open>First, we prove some auxiliary lemmas.\<close>
lemma rtrancl_imp_singleton_seq2: "x \<rightarrow>\<^sub>i* y \<Longrightarrow> 
          x = y \<or> (\<exists> s. s \<noteq> [] \<and> (tl s \<noteq> []) \<and> s ! 0 = x \<and> s ! (length s - 1) = y \<and> 
               (\<forall> i < (length s - 1). (s ! i) \<rightarrow>\<^sub>i (s ! (Suc i))))"

  unfolding state_transition_refl_def
proof (induction rule: rtrancl_induct)
  case base
  then show ?case
    by simp
next
  case (step y z)
  show ?case
    using step.IH
  proof (elim disjE exE conjE)
    assume "x=y"
    with step.hyps show ?case
      by (force intro!: exI [where x="[y,z]"])
  next
    show "\<And>s. \<lbrakk>s \<noteq> []; tl s \<noteq> []; s ! 0 = x;
          s ! (length s - 1) = y;
          \<forall>i<length s - 1.
             s ! i \<rightarrow>\<^sub>i s ! Suc i\<rbrakk>
         \<Longrightarrow> x = z \<or>
             (\<exists>s. s \<noteq> [] \<and>
                  tl s \<noteq> [] \<and> s ! 0 = x \<and>
                  s ! (length s - 1) = z \<and>
                  (\<forall>i<length s - 1. s ! i \<rightarrow>\<^sub>i s ! Suc i))"
      apply (rule disjI2)
      apply (rule_tac x="s @ [z]" in exI)
      apply (auto simp: nth_append)
      by (metis One_nat_def Suc_lessI diff_Suc_1 mem_Collect_eq old.prod.case step.hyps(2))
  qed
qed

lemma tl_nempty_length[rule_format]: "s \<noteq> [] \<longrightarrow> tl s \<noteq> [] \<longrightarrow> 0 < length s - 1"
  by (induction s, simp+)

lemma tl_nempty_length2[rule_format]: "s \<noteq> [] \<longrightarrow> tl s \<noteq> [] \<longrightarrow> Suc 0 < length s"
  by (induction s, simp+)

lemma length_last[rule_format]: "(l @ [x]) ! (length (l @ [x]) - 1) = x"
  by (induction l, simp+)

lemma Compl_step2: "\<forall> x \<in> I. \<exists> y \<in> s. x \<rightarrow>\<^sub>i* y \<Longrightarrow> 
                   ( \<forall> x \<in> I.  x \<in> s \<or> (\<exists> (sl :: ((('s :: state) set)list)). 
                  (sl \<noteq> []) \<and> (tl sl \<noteq> []) \<and>
                 (sl ! 0, sl ! (length sl - 1)) = ({x},s) \<and>
                 (\<forall> i < (length sl - 1).  \<turnstile> \<N>\<^bsub>(sl ! i,sl ! (i+1) )\<^esub>
                         )))"
proof (rule ballI, drule_tac x = x in bspec, assumption, erule bexE)
  fix x y
  assume a: "x \<in> I" and b: "y \<in> s" and  c: "x \<rightarrow>\<^sub>i* y"
  show "x \<in> s \<or>
       (\<exists>sl::'s set list.
           sl \<noteq> [] \<and>
           tl sl \<noteq> [] \<and>
           (sl ! (0), sl ! (length sl - (1))) = ({x}, s) \<and>
           (\<forall>i<length sl - (1). \<turnstile>\<N>\<^bsub>(sl ! i, sl ! (i + (1)))\<^esub>))"
  proof -
    have d : "x = y \<or>
       (\<exists>s'. s' \<noteq> [] \<and>
           tl s' \<noteq> [] \<and>
           s' ! (0) = x \<and>
           s' ! (length s' - (1)) = y \<and> (\<forall>i<length s' - (1). s' ! i \<rightarrow>\<^sub>i s' ! Suc i))"
      using c rtrancl_imp_singleton_seq2 by blast
    thus "x \<in> s \<or>
       (\<exists>sl::'s set list.
           sl \<noteq> [] \<and>
           tl sl \<noteq> [] \<and>
           (sl ! (0), sl ! (length sl - (1))) = ({x}, s) \<and>
           (\<forall>i<length sl - (1). \<turnstile>\<N>\<^bsub>(sl ! i, sl ! (i + (1)))\<^esub>))"
      apply (rule disjE)
      using b apply blast
      apply (rule disjI2, elim conjE exE)
      apply (rule_tac x = "[{s' ! j}. j \<leftarrow> [0..<(length s' - 1)]] @ [s]" in exI)
      apply (auto simp: nth_append)
        apply (metis AT.att_base Suc_lessD fst_conv prod.sel(2) singletonD singletonI)
       apply (metis AT.att_base Suc_lessI b fst_conv prod.sel(2) singletonD)
      using tl_nempty_length2 by blast
  qed
qed

subsubsection "Lemma @{text \<open>Compl_step3\<close>}"
text \<open>First, we need a few lemmas.\<close>
lemma map_hd_lem[rule_format] : "n > 0 \<longrightarrow> (f 0 #  map (\<lambda>i. f i) [1..<n]) = map  (\<lambda>i. f i) [0..<n]"    
  by (simp add : hd_map upt_rec)

lemma map_Suc_lem[rule_format] : "n > 0 \<longrightarrow> map (\<lambda> i:: nat. f i)[1..<n] =
                                  map (\<lambda> i:: nat. f(Suc i))[0..<(n - 1)]"
proof -
  have "(f 0 # map (\<lambda>n. f (Suc n)) [0..<n - 1] = f 0 # map f [1..<n]) = (map (\<lambda>n. f (Suc n)) [0..<n - 1] = map f [1..<n])"
    by blast
  then show ?thesis
    by (metis Suc_pred' map_hd_lem map_upt_Suc)
qed

lemma forall_ex_fun: "finite S \<Longrightarrow> (\<forall> x \<in> S. (\<exists> y. P y x)) \<longrightarrow> (\<exists> f. \<forall> x \<in> S. P (f x) x)"
proof (induction rule: finite.induct)
  case emptyI
  then show ?case 
    by simp
next
  case (insertI F x)
  then show ?case
  proof (clarify)
    assume d: "(\<forall>x::'a\<in>insert x F. \<exists>y::'b. P y x)"
    have "(\<forall>x::'a\<in>F. \<exists>y::'b. P y x)" 
      using d by blast
    then obtain f where f: "\<forall>x::'a\<in>F. P (f x) x" 
      using insertI.IH by blast 
    from d obtain y where "P y x" by blast
    thus "(\<exists>f::'a \<Rightarrow> 'b. \<forall>x::'a\<in>insert x F. P (f x) x)" using f 
      by (rule_tac x = "\<lambda> z. if z = x then y else f z" in exI, simp)
  qed
qed

primrec nodup :: "['a, 'a list] \<Rightarrow> bool"
  where 
    nodup_nil: "nodup a [] = True" |
    nodup_step: "nodup a (x # ls) = (if x = a then (a \<notin> (set ls)) else nodup a ls)"

definition nodup_all:: "'a list \<Rightarrow> bool"
  where
    "nodup_all l \<equiv> \<forall> x \<in> set l. nodup x l"

lemma nodup_all_lem[rule_format]: 
  "nodup_all (x1 # a # l) \<longrightarrow> (insert x1 (insert a (set l)) - {x1}) = insert a (set l)"
  by (induction l, (simp add: nodup_all_def)+)

lemma nodup_all_tl[rule_format]: "nodup_all (x # l) \<longrightarrow> nodup_all l"  
  by (induction l, (simp add: nodup_all_def)+)

lemma finite_nodup: "finite I \<Longrightarrow> \<exists> l. set l = I \<and> nodup_all l"
proof (induction rule: finite.induct)
  case emptyI
  then show ?case
    by (simp add: nodup_all_def)
next
  case (insertI A a)
  then show ?case
    by (metis insertE insert_absorb list.simps(15) nodup_all_def nodup_step)
qed

lemma Compl_step3: "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow>
     ( \<forall> x \<in> I.  x \<in> s \<or> (\<exists> (sl :: ((('s :: state) set)list)). 
                  (sl \<noteq> []) \<and> (tl sl \<noteq> []) \<and>
                 (sl ! 0, sl ! (length sl - 1)) = ({x},s) \<and>
                 (\<forall> i < (length sl - 1).  \<turnstile> \<N>\<^bsub>(sl ! i,sl ! (i+1) )\<^esub>
                         )) \<Longrightarrow> 
     (\<exists> lI. set lI = {x :: 's :: state. x \<in> I \<and> x \<notin> s} \<and> (\<exists> Sj :: ((('s :: state) set)list) list. 
               length Sj = length lI \<and> nodup_all lI \<and>
            (\<forall> j < length Sj. (((Sj ! j)  \<noteq> []) \<and> (tl (Sj ! j) \<noteq> []) \<and>
                 ((Sj ! j) ! 0, (Sj ! j) ! (length (Sj ! j) - 1)) = ({lI ! j},s) \<and>
                 (\<forall> i < (length (Sj ! j) - 1).  \<turnstile> \<N>\<^bsub>((Sj ! j) ! i, (Sj ! j) ! (i+1) )\<^esub>
                         ))))))"  
proof -
  assume i: "I \<noteq> {}" and f: "finite I" and
      fa: "\<forall>x::'s\<in>I.
       x \<in> s \<or>
       (\<exists>sl::'s set list.
           sl \<noteq> [] \<and>
           tl sl \<noteq> [] \<and>
           (sl ! (0), sl ! (length sl - (1))) = ({x}, s) \<and>
           (\<forall>i<length sl - (1). \<turnstile>\<N>\<^bsub>(sl ! i, sl ! (i + (1)))\<^esub>))"
  have a: "\<exists> lI. set lI = {x::'s \<in> I. x \<notin> s} \<and> nodup_all lI"
    by (simp add: f finite_nodup)
  from this obtain lI where b: "set lI = {x::'s \<in> I. x \<notin> s} \<and> nodup_all lI"
    by (erule exE)
  thus "\<exists>lI::'s list.
       set lI = {x::'s \<in> I. x \<notin> s} \<and>
       (\<exists>Sj::'s set list list.
           length Sj = length lI \<and>
           nodup_all lI \<and>
           (\<forall>j<length Sj.
               Sj ! j \<noteq> [] \<and>
               tl (Sj ! j) \<noteq> [] \<and>
               (Sj ! j ! (0), Sj ! j ! (length (Sj ! j) - (1))) = ({lI ! j}, s) \<and>
               (\<forall>i<length (Sj ! j) - (1). \<turnstile>\<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1)))\<^esub>)))"
    apply (rule_tac x = lI in exI)
    apply (rule conjI)
     apply (erule conjE, assumption)
  proof -
    have c:  "\<forall> x \<in> set(lI). (\<exists> sl::'s set list.
              sl \<noteq> [] \<and>
              tl sl \<noteq> [] \<and>
              (sl ! (0), sl ! (length sl - (1))) = ({x}, s) \<and>
              (\<forall>i<length sl - (1). \<turnstile>\<N>\<^bsub>(sl ! i, sl ! (i + (1)))\<^esub>))"
      using b fa by fastforce
    thus "\<exists>Sj::'s set list list.
       length Sj = length lI \<and>
       nodup_all lI \<and>
       (\<forall>j<length Sj.
           Sj ! j \<noteq> [] \<and>
           tl (Sj ! j) \<noteq> [] \<and>
           (Sj ! j ! (0), Sj ! j ! (length (Sj ! j) - (1))) = ({lI ! j}, s) \<and>
           (\<forall>i<length (Sj ! j) - (1). \<turnstile>\<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1)))\<^esub>))"
      apply (subgoal_tac "finite (set lI)")
       apply (rotate_tac -1)
       apply (drule forall_ex_fun)
       apply (drule mp)
        apply assumption
       apply (erule exE)
       apply (rule_tac x = "[f (lI ! j). j \<leftarrow> [0..<(length lI)]]" in exI)
       apply simp
       apply (insert b)
       apply (erule conjE, assumption)
      apply (rule_tac A = "set lI" and B = I in finite_subset)
       apply blast
      by (rule f)
  qed
qed

subsubsection \<open>Lemma @{text \<open>Compl_step4\<close>}\<close>
text \<open>Again, we need some additional lemmas first.\<close>
lemma list_one_tl_empty[rule_format]: "length l = Suc (0 :: nat) \<longrightarrow> tl l = []"
  by (induction l, simp+)

lemma list_two_tl_not_empty[rule_format]: "\<forall> list. length l = Suc (Suc (length list)) \<longrightarrow> tl l \<noteq> []"  
  by (induction l, simp+, force)

lemma or_empty: "\<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>({}, s)\<^esup>)" by (simp add: att_or)

text \<open>Note, this is not valid for any l, i.e., @{text \<open>\<turnstile> l \<oplus>\<^sub>\<or>\<^bsup>({}, s)\<^esup>\<close>} is not a theorem.\<close>
lemma list_or_upt[rule_format]:
 "\<forall> l . lI \<noteq> [] \<longrightarrow> length l = length lI \<longrightarrow> nodup_all lI \<longrightarrow>
  (\<forall> i < length lI. (\<turnstile> (l ! i)) \<and> (attack (l ! i) = ({lI ! i}, s))) 
                \<longrightarrow> ( \<turnstile> (l \<oplus>\<^sub>\<or>\<^bsup>(set lI, s)\<^esup>))"     
proof (induction lI, simp, clarify)
  fix x1 x2 l
  show "\<forall>l::'a attree list.
          x2 \<noteq> [] \<longrightarrow>
          length l = length x2 \<longrightarrow>
          nodup_all x2 \<longrightarrow>
          (\<forall>i<length x2. \<turnstile>(l ! i) \<and> attack (l ! i) = ({x2 ! i}, s)) \<longrightarrow> \<turnstile>(l \<oplus>\<^sub>\<or>\<^bsup>(set x2, s)\<^esup>) \<Longrightarrow>
       x1 # x2 \<noteq> [] \<Longrightarrow>
       length l = length (x1 # x2) \<Longrightarrow>
       nodup_all (x1 # x2) \<Longrightarrow>
       \<forall>i<length (x1 # x2). \<turnstile>(l ! i) \<and> attack (l ! i) = ({(x1 # x2) ! i}, s) \<Longrightarrow> \<turnstile>(l \<oplus>\<^sub>\<or>\<^bsup>(set (x1 # x2), s)\<^esup>)"
    apply (case_tac x2, simp, subst att_or, case_tac l, simp+)
    text \<open>Case @{text \<open>\<forall>i<Suc (Suc (length list)). \<turnstile>l ! i \<and> attack (l ! i) = ({(x1 # a # list) ! i}, s) \<Longrightarrow>
       x2 = a # list \<Longrightarrow>  \<turnstile>l \<oplus>\<^sub>\<or>\<^bsup>(insert x1 (insert a (set list)), s)\<^esup>\<close>}\<close>
    apply (subst att_or, case_tac l, simp, clarify, simp, rename_tac lista, case_tac lista, simp+)
    text \<open>Remaining conjunct of three conditions: @{text \<open> \<turnstile>aa \<and>
       fst (attack aa) \<subseteq> insert x1 (insert a (set list)) \<and>
       snd (attack aa) \<subseteq> s \<and> \<turnstile>ab # listb \<oplus>\<^sub>\<or>\<^bsup>(insert x1 (insert a (set list)) - fst (attack aa), s)\<^esup>\<close>}\<close>
    apply (rule conjI)
    text \<open>First condition @{text \<open> \<turnstile>aa\<close>}\<close>
     apply (drule_tac x = 0 in spec, drule mp, simp, (erule conjE)+, simp, rule conjI)
    text \<open>Second condition @{text \<open>fst (attack aa) \<subseteq> insert x1 (insert a (set list))\<close>}\<close>
     apply (drule_tac x = 0 in spec, drule mp, simp, erule conjE, simp)
    text \<open>The remaining conditions 

          @{text \<open>snd (attack aa) \<subseteq> s \<and> \<turnstile>ab # listb \<oplus>\<^sub>\<or>\<^bsup>(insert x1 (insert a (set list)) - fst (attack aa), s)\<^esup>\<close>}
 
          are solved automatically!\<close>
    by (metis Suc_mono add.right_neutral add_Suc_right list.size(4) nodup_all_lem nodup_all_tl nth_Cons_0 nth_Cons_Suc order_refl prod.sel(1) prod.sel(2) zero_less_Suc)
qed

lemma app_tl_empty_hd[rule_format]: "tl (l @ [a]) = [] \<longrightarrow> hd (l @ [a]) = a"
  by (induction l) auto
       
lemma tl_hd_empty[rule_format]: "tl (l @ [a]) = [] \<longrightarrow> l = []"
  by (induction l) auto

lemma tl_hd_not_empty[rule_format]: "tl (l @ [a]) \<noteq> [] \<longrightarrow> l \<noteq> []"
  by (induction l) auto
  
lemma app_tl_empty_length[rule_format]: "tl (map f [0..<length l] @ [a]) = []  
                                        \<Longrightarrow> l = []"
  by (drule tl_hd_empty, simp)

lemma not_empty_hd_fst[rule_format]: "l \<noteq> [] \<longrightarrow> hd(l @ [a]) = l ! 0"
  by (induction l) auto
  
lemma app_tl_hd_list[rule_format]: "tl (map f [0..<length l] @ [a]) \<noteq> []  
                             \<Longrightarrow> hd(map f [0..<length l] @ [a]) = (map f [0..<length l]) ! 0"
  by (drule tl_hd_not_empty, erule not_empty_hd_fst)

lemma tl_app_in[rule_format]: "l \<noteq> [] \<longrightarrow>
   map f [0..<(length l - (Suc 0:: nat))] @ [f(length l - (Suc 0 :: nat))] = map f [0..<length l]"    
  by (induction l) auto

lemma map_fst[rule_format]: "n > 0 \<longrightarrow> map f [0..<n] = f 0 # (map f [1..<n])"
  by (induction n) auto

lemma step_lem[rule_format]:  "l \<noteq> [] \<Longrightarrow>
       tl (map (\<lambda> i. f((x1 # a # l) ! i)((a # l) ! i)) [0..<length l]) =
       map (\<lambda>i. f((a # l) ! i)(l ! i)) [0..<length l - (1)]"
proof (simp)
  assume l: "l \<noteq> []"
    have a: "map (\<lambda>i. f ((x1 # a # l) ! i) ((a # l) ! i)) [0..<length l] =
                 (f(x1)(a) # (map (\<lambda>i. f ((a # l) ! i) (l ! i)) [0..<(length l - 1)]))"
    proof -
      have b : "map (\<lambda>i. f ((x1 # a # l) ! i) ((a # l) ! i)) [0..<length l] =
                     f ((x1 # a # l) ! 0) ((a # l) ! 0) # 
                     (map (\<lambda>i. f ((x1 # a # l) ! i) ((a # l) ! i)) [1..<length l])"
        by (rule map_fst, simp, rule l)
      have c: "map (\<lambda>i. f ((x1 # a # l) ! i) ((a # l) ! i)) [Suc (0)..<length l] =
                map (\<lambda>i. f ((x1 # a # l) ! Suc i) ((a # l) ! Suc i)) [(0)..<(length l - 1)]"
        by (subgoal_tac "[Suc (0)..<length l] = map Suc [0..<(length l - 1)]", 
             simp, simp add: map_Suc_upt l)
      thus "map (\<lambda>i. f ((x1 # a # l) ! i) ((a # l) ! i)) [0..<length l] =
             f x1 a # map (\<lambda>i. f ((a # l) ! i) (l ! i)) [0..<length l - (1)]"
         by (simp add: b c)
    qed
    thus "l \<noteq> [] \<Longrightarrow>
    tl (map (\<lambda>i. f ((x1 # a # l) ! i) ((a # l) ! i)) [0..<length l]) =
    map (\<lambda>i. f ((a # l) ! i) (l ! i)) [0..<length l - Suc (0)]" 
      by (subst a, simp)
  qed

lemma step_lem2a[rule_format]: "0 < length list \<Longrightarrow> map (\<lambda>i. \<N>\<^bsub>((x1 # a # list) ! i, (a # list) ! i)\<^esub>)
        [0..<length list] @
       [\<N>\<^bsub>((x1 # a # list) ! length list, (a # list) ! length list)\<^esub>] =
       aa # listb \<longrightarrow> \<N>\<^bsub>((x1, a))\<^esub> = aa"
  by (subst map_fst, assumption, simp)

lemma step_lem2b[rule_format]: "0 = length list \<Longrightarrow> map (\<lambda>i. \<N>\<^bsub>((x1 # a # list) ! i, (a # list) ! i)\<^esub>)
        [0..<length list] @
       [\<N>\<^bsub>((x1 # a # list) ! length list, (a # list) ! length list)\<^esub>] =
       aa # listb \<longrightarrow> \<N>\<^bsub>((x1, a))\<^esub> = aa"
by simp

lemma step_lem2: "map (\<lambda>i. \<N>\<^bsub>((x1 # a # list) ! i, (a # list) ! i)\<^esub>)
        [0..<length list] @
       [\<N>\<^bsub>((x1 # a # list) ! length list, (a # list) ! length list)\<^esub>] =
       aa # listb \<Longrightarrow> \<N>\<^bsub>((x1, a))\<^esub> = aa"
proof (case_tac "length list", rule step_lem2b, erule sym, assumption)
  show "\<And>nat.
       map (\<lambda>i. \<N>\<^bsub>((x1 # a # list) ! i, (a # list) ! i)\<^esub>) [0..<length list] @
       [\<N>\<^bsub>((x1 # a # list) ! length list, (a # list) ! length list)\<^esub>] =
       aa # listb \<Longrightarrow>
       length list = Suc nat \<Longrightarrow> \<N>\<^bsub>(x1, a)\<^esub> = aa"
    by (rule_tac list = list in step_lem2a, simp)
qed

lemma base_list_and[rule_format]: "Sji \<noteq> [] \<longrightarrow> tl Sji \<noteq> [] \<longrightarrow>
         (\<forall> li.  Sji ! (0) = li \<longrightarrow>
        Sji! (length (Sji) - 1) = s \<longrightarrow>
       (\<forall>i<length (Sji) - 1. \<turnstile>\<N>\<^bsub>(Sji ! i, Sji ! Suc i)\<^esub>) \<longrightarrow>
       \<turnstile> (map (\<lambda>i. \<N>\<^bsub>(Sji ! i, Sji ! Suc i)\<^esub>)
          [0..<length (Sji) - Suc (0)] \<oplus>\<^sub>\<and>\<^bsup>(li, s)\<^esup>))"
proof (induction Sji)
  case Nil
  then show ?case by simp
next
  case (Cons a Sji)
  then show ?case 
    apply (subst att_and, case_tac Sji, simp, simp)
    apply (rule impI)+
  proof -
    fix aa list
    show "list \<noteq> [] \<longrightarrow>
       list ! (length list - Suc 0) = s \<longrightarrow>
       (\<forall>i<length list. \<turnstile>\<N>\<^bsub>((aa # list) ! i, list ! i)\<^esub>) \<longrightarrow>
       \<turnstile>(map (\<lambda>i. \<N>\<^bsub>((aa # list) ! i, list ! i)\<^esub>) [0..<length list] \<oplus>\<^sub>\<and>\<^bsup>(aa, s)\<^esup>) \<Longrightarrow>
       Sji = aa # list \<Longrightarrow>
       (aa # list) ! length list = s \<Longrightarrow>
       \<forall>i<Suc (length list). \<turnstile>\<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub> \<Longrightarrow>
       case map (\<lambda>i. \<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub>) [0..<length list] @
            [\<N>\<^bsub>((a # aa # list) ! length list, s)\<^esub>] of
       [] \<Rightarrow> fst (a, s) \<subseteq> snd (a, s) | [aa] \<Rightarrow> \<turnstile>aa \<and> attack aa = (a, s)
       | aa # ab # list \<Rightarrow>
           \<turnstile>aa \<and> fst (attack aa) = fst (a, s) \<and> \<turnstile>(ab # list \<oplus>\<^sub>\<and>\<^bsup>(snd (attack aa), snd (a, s))\<^esup>)"
    proof (case_tac "map (\<lambda>i. \<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub>) [0..<length list] @
            [\<N>\<^bsub>((a # aa # list) ! length list, s)\<^esub>]", simp, clarify, simp)
      fix ab lista
      have *: "tl (map (\<lambda>i. \<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub>) [0..<length list])
                    =  (map (\<lambda>i. \<N>\<^bsub>((aa # list) ! i, (list) ! i)\<^esub>) [0..<(length list - 1)])"
        if "list \<noteq> []"
        apply (subgoal_tac "tl (map (\<lambda>i. \<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub>) [0..<length list])
                    =  (map (\<lambda>i. \<N>\<^bsub>((aa # list) ! i, (list) ! i)\<^esub>) [0..<(length list - 1)])")
         apply blast
        apply (subst step_lem [OF that])
        apply simp
        done
      show "list \<noteq> [] \<longrightarrow>
       (\<forall>i<length list. \<turnstile>\<N>\<^bsub>((aa # list) ! i, list ! i)\<^esub>) \<longrightarrow>
       \<turnstile>(map (\<lambda>i. \<N>\<^bsub>((aa # list) ! i, list ! i)\<^esub>)
          [0..<length list] \<oplus>\<^sub>\<and>\<^bsup>(aa, list ! (length list - Suc 0))\<^esup>) \<Longrightarrow>
       Sji = aa # list \<Longrightarrow>
       \<forall>i<Suc (length list). \<turnstile>\<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub> \<Longrightarrow>
       map (\<lambda>i. \<N>\<^bsub>((a # aa # list) ! i, (aa # list) ! i)\<^esub>) [0..<length list] @
       [\<N>\<^bsub>((a # aa # list) ! length list, (aa # list) ! length list)\<^esub>] =
       ab # lista \<Longrightarrow>
       s = (aa # list) ! length list \<Longrightarrow>
       case lista of [] \<Rightarrow> \<turnstile>ab \<and> attack ab = (a, (aa # list) ! length list)
       | aba # lista \<Rightarrow>
           \<turnstile>ab \<and> fst (attack ab) = a \<and> \<turnstile>(aba # lista \<oplus>\<^sub>\<and>\<^bsup>(snd (attack ab), (aa # list) ! length list)\<^esup>)"
        apply (auto simp: split: list.split)
           apply (metis (no_types, lifting) app_tl_hd_list length_greater_0_conv list.sel(1) list.sel(3) list.simps(3) list.simps(8) list.size(3) map_fst nth_Cons_0 self_append_conv2 upt_0 zero_less_Suc)
          apply (metis (no_types, lifting) app_tl_hd_list attack.simps(1) fst_conv length_greater_0_conv list.sel(1) list.sel(3) list.simps(3) list.simps(8) list.size(3) map_fst nth_Cons_0 self_append_conv2 upt_0)
         apply (metis (mono_tags, lifting) app_tl_hd_list attack.simps(1) fst_conv length_greater_0_conv list.sel(1) list.sel(3) list.simps(3) list.simps(8) list.size(3) map_fst nth_Cons_0 self_append_conv2 upt_0)
        by (smt * One_nat_def app_tl_hd_list attack.simps(1) length_greater_0_conv list.sel(1) list.sel(3) list.simps(3) list.simps(8) list.size(3) map_fst nth_Cons_0 nth_Cons_pos self_append_conv2 snd_conv tl_app_in tl_append2 upt_0)
    qed
  qed
qed

lemma Compl_step4: "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow> \<not> I \<subseteq> s \<Longrightarrow>
(\<exists> lI. set lI = {x. x \<in> I \<and> x \<notin> s} \<and> (\<exists> Sj :: ((('s :: state) set)list) list. 
               length Sj = length lI \<and> nodup_all lI \<and>
            (\<forall> j < length Sj. (((Sj ! j)  \<noteq> []) \<and> (tl (Sj ! j) \<noteq> []) \<and>
                 ((Sj ! j) ! 0, (Sj ! j) ! (length (Sj ! j) - 1)) = ({lI ! j},s) \<and>
                 (\<forall> i < (length (Sj ! j) - 1).  \<turnstile> \<N>\<^bsub>((Sj ! j) ! i, (Sj ! j) ! (i+1) )\<^esub>
                         )))))
 \<Longrightarrow>  \<exists> (A :: ('s :: state) attree).  \<turnstile> A \<and> attack A = (I,s)"
proof (erule exE, erule conjE, erule exE, erule conjE)
  fix lI Sj
  assume  a: "I \<noteq> {}" and b: "finite I" and c: "\<not> I \<subseteq> s"
    and d: "set lI = {x::'s \<in> I. x \<notin> s}" and e: "length Sj = length lI"
    and f: "nodup_all lI \<and> 
              (\<forall>j<length Sj. Sj ! j \<noteq> [] \<and>
                             tl (Sj ! j) \<noteq> [] \<and>
           (Sj ! j ! (0), Sj ! j ! (length (Sj ! j) - (1))) = ({lI ! j}, s) \<and>
           (\<forall>i<length (Sj ! j) - (1). \<turnstile>\<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1)))\<^esub>))"
  show    "\<exists>A::'s attree. \<turnstile>A \<and> attack A = (I, s)"
    apply (rule_tac x = 
        "[([] \<oplus>\<^sub>\<or>\<^bsup>({x. x \<in> I \<and> x \<in> s}, s)\<^esup>),
    ([[ \<N>\<^bsub>((Sj ! j) ! i, (Sj ! j) ! (i + (1)))\<^esub>. 
      i \<leftarrow> [0..<(length (Sj ! j)-(1))]] \<oplus>\<^sub>\<and>\<^bsup>(({lI ! j},s))\<^esup>. j \<leftarrow> [0..<(length Sj)]]
     \<oplus>\<^sub>\<or>\<^bsup>({x. x \<in> I \<and> x \<notin> s},s)\<^esup>)] \<oplus>\<^sub>\<or>\<^bsup>(I, s)\<^esup>" in exI)
  proof 
    show  "\<turnstile>([[] \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<in> s}, s)\<^esup>,
       map (\<lambda>j.
               ((map (\<lambda>i. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1)))\<^esub>)
                [0..<length (Sj ! j) - (1)]) \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>))
       [0..<length Sj] \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<notin> s}, s)\<^esup>] \<oplus>\<^sub>\<or>\<^bsup>(I, s)\<^esup>)"
    proof -
      have g: "I - {x::'s \<in> I. x \<in> s} = {x::'s \<in> I. x \<notin> s}" by blast
      thus "\<turnstile>([[] \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<in> s}, s)\<^esup>,
       (map (\<lambda>j.
               ((map (\<lambda>i. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! (i + (1)))\<^esub>)
                [0..<length (Sj ! j) - (1)]) \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>))
       [0..<length Sj]) \<oplus>\<^sub>\<or>\<^bsup>({x::'s \<in> I. x \<notin> s}, s)\<^esup>] \<oplus>\<^sub>\<or>\<^bsup>(I, s)\<^esup>)"
        apply (subst att_or, simp)
      proof 
        show "I - {x \<in> I. x \<in> s} = {x \<in> I. x \<notin> s} \<Longrightarrow> \<turnstile>([] \<oplus>\<^sub>\<or>\<^bsup>({x \<in> I. x \<in> s}, s)\<^esup>)"
          by (metis (no_types, lifting) CollectD att_or_empty_back subsetI)
      next show "I - {x \<in> I. x \<in> s} = {x \<in> I. x \<notin> s} \<Longrightarrow>
    \<turnstile>([map (\<lambda>j. ((map (\<lambda>i. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! Suc i)\<^esub>) [0..<length (Sj ! j) - Suc 0]) \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>))
        [0..<length Sj] \<oplus>\<^sub>\<or>\<^bsup>({x \<in> I. x \<notin> s}, s)\<^esup>] \<oplus>\<^sub>\<or>\<^bsup>({x \<in> I. x \<notin> s}, s)\<^esup>)"
          text \<open>Use lemma @{text \<open>list_or_upt\<close>} to distribute attack validity  over list lI\<close>
        proof (erule ssubst, subst att_or, simp, rule subst, rule d, rule_tac lI = lI in list_or_upt)
          show "lI \<noteq> []"
            using c d by auto 
        next show "\<And>i.
       i < length lI \<Longrightarrow>
       \<turnstile>(map (\<lambda>j.
                 ((map (\<lambda>i. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! Suc i)\<^esub>)
                  [0..<length (Sj ! j) - Suc (0)]) \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>))
          [0..<length Sj] !
         i) \<and>
       (attack
        (map (\<lambda>j.
                 ((map (\<lambda>i. \<N>\<^bsub>(Sj ! j ! i, Sj ! j ! Suc i)\<^esub>)
                  [0..<length (Sj ! j) - Suc (0)]) \<oplus>\<^sub>\<and>\<^bsup>({lI ! j}, s)\<^esup>))
          [0..<length Sj] !
         i) =
       ({lI ! i}, s))"
          proof (simp add: a b c d e f)
            show "\<And>i.
                i < length lI \<Longrightarrow>
                \<turnstile>(map (\<lambda>ia. \<N>\<^bsub>(Sj ! i ! ia, Sj ! i ! Suc ia)\<^esub>)
                [0..<length (Sj ! i) - Suc (0)] \<oplus>\<^sub>\<and>\<^bsup>({lI ! i}, s)\<^esup>)"
            proof -
              fix i :: nat
              assume a1: "i < length lI"
              have "\<forall>n. \<turnstile>map (\<lambda>na. \<N>\<^bsub>(Sj ! n ! na, Sj ! n ! Suc na)\<^esub>) [0..< length (Sj ! n) - 1] \<oplus>\<^sub>\<and>\<^bsup>(Sj ! n ! 0, Sj ! n ! (length (Sj ! n) - 1))\<^esup> \<or> \<not> n < length Sj"
                by (metis (no_types) One_nat_def add.right_neutral add_Suc_right base_list_and f)
              then show "\<turnstile>map (\<lambda>n. \<N>\<^bsub>(Sj ! i ! n, Sj ! i ! Suc n)\<^esub>) [0..< length (Sj ! i) - Suc 0] \<oplus>\<^sub>\<and>\<^bsup>({lI ! i}, s)\<^esup>"
                using a1 by (metis (no_types) One_nat_def e f)
            qed
          qed
        qed (auto simp add: e f)
      qed
    qed
  qed auto
qed

subsubsection \<open>Main Theorem Completeness\<close> 
theorem Completeness: "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow> 
Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} (I :: ('s :: state)set)  \<turnstile> EF s 
\<Longrightarrow> \<exists> (A :: ('s :: state) attree). \<turnstile> A \<and> attack A = (I,s)"
proof (case_tac "I \<subseteq> s")
  show "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow>
    Kripke {s::'s. \<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* s} I \<turnstile> EF s \<Longrightarrow> I \<subseteq> s \<Longrightarrow> \<exists>A::'s attree. \<turnstile>A \<and> attack A = (I, s)"
    using att_or_empty_back attack.simps(3) by blast
next 
  show "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow>
    Kripke {s::'s. \<exists>i::'s\<in>I. i \<rightarrow>\<^sub>i* s} I \<turnstile> EF s \<Longrightarrow> \<not> I \<subseteq> s 
   \<Longrightarrow> \<exists>A::'s attree. \<turnstile>A \<and> attack A = (I, s)"
    by (iprover intro: Compl_step1 Compl_step2 Compl_step3 Compl_step4 elim: )
qed

subsubsection \<open>Contrapositions of Correctness and Completeness\<close>   
lemma contrapos_compl: 
  "I \<noteq> {} \<Longrightarrow> finite I \<Longrightarrow> 
  (\<not> (\<exists> (A :: ('s :: state) attree). \<turnstile> A \<and> attack A = (I, - s))) \<Longrightarrow>
\<not> (Kripke {s. \<exists>i\<in>I. i \<rightarrow>\<^sub>i* s} I \<turnstile> EF (- s))"
  using Completeness by auto

lemma contrapos_corr:   
"(\<not>(Kripke {s :: ('s :: state). \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I  \<turnstile> EF s))
\<Longrightarrow> attack A = (I,s) 
\<Longrightarrow> \<not> (\<turnstile> A)"
  using AT_EF by blast

end