(*File: VS_OBJ.thy*)
(*Authors: Lennart Beringer and Martin Hofmann, LMU Munich 2008*)
theory VS_OBJ imports VDM_OBJ PBIJ begin

subsection\<open>Non-interference\<close>
text\<open>\label{sec:ObjNI}\<close>
subsubsection\<open>Indistinguishability relations\<close>

text\<open>We have the usual two security types.\<close>

datatype TP = low | high

text\<open>Global contexts assigns security types to program
variables and field names.\<close>

consts CONTEXT :: "Var \<Rightarrow> TP"
consts GAMMA :: "Field \<Rightarrow> TP"

text\<open>Indistinguishability of values depends on a partial bijection
$\beta$.\<close>

inductive_set twiddleVal::"(PBij \<times> Val \<times> Val) set"
where
twiddleVal_Null: "(\<beta>, RVal Nullref, RVal Nullref) : twiddleVal"

| twiddleVal_Loc: "(l1,l2) : \<beta> \<Longrightarrow>
                 (\<beta>, RVal (Loc l1), RVal (Loc l2)) : twiddleVal"
| twiddleVal_IVal: "i1 = i2 \<Longrightarrow> (\<beta>, IVal i1, IVal i2) : twiddleVal"

text\<open>For stores, indistinguishability is as follows.\<close>

definition twiddleStore::"PBij \<Rightarrow> Store \<Rightarrow> Store \<Rightarrow> bool"
where "twiddleStore \<beta> s1 s2 =
  (\<forall> x. CONTEXT x = low \<longrightarrow> (\<beta>, s1 x, s2 x) : twiddleVal)"

abbreviation twiddleStore_syntax  ("_  \<approx>\<^sub>_ _" [100,100] 50)
  where "s \<approx>\<^sub>\<beta> t == twiddleStore \<beta> s t"

text\<open>On objects, we require the values in low fields to be related,
and the sets of defined low fields to be equal.\<close>

definition LowDom::"((Field \<times> Val) list) \<Rightarrow> Field set"
where "LowDom F = {f . \<exists> v . lookup F f = Some v \<and> GAMMA f = low}"

definition twiddleObj::"PBij \<Rightarrow> Object \<Rightarrow> Object \<Rightarrow> bool"
where "twiddleObj \<beta> o1 o2 = ((fst o1 = fst o2) \<and> 
                          LowDom (snd o1) = LowDom (snd o2) \<and>
                         (\<forall> f v w . lookup (snd o1) f = Some v \<longrightarrow>
                                     lookup (snd o2) f = Some w \<longrightarrow>
                                     GAMMA f = low \<longrightarrow>
                                     (\<beta>, v, w) : twiddleVal))"

text\<open>On heaps, we require locations related by $\beta$ to contain
indistinguishable objects. Domain and codomain of the bijection
should be subsets of the domains of the heaps, of course.\<close>

definition twiddleHeap::"PBij \<Rightarrow> Heap \<Rightarrow> Heap \<Rightarrow> bool"
where "twiddleHeap \<beta> h1 h2 = (\<beta>:Pbij \<and>
                          Pbij_Dom \<beta> \<subseteq> Dom h1 \<and> 
                          Pbij_Rng \<beta> \<subseteq> Dom h2 \<and>
                          (\<forall> l ll v w . (l,ll):\<beta> \<longrightarrow>
                                        lookup h1 l = Some v \<longrightarrow>
                                        lookup h2 ll = Some w \<longrightarrow>
                                        twiddleObj \<beta> v w))"

text\<open>We also define a predicate which expresses when a state does not
contain dangling pointers.\<close>

(*The notion used in our paper:
definition noDPs::"State \<Rightarrow> bool"
where "noDPs S = (case S of (s,h) \<Rightarrow>  ((\<forall> x l . s x = RVal(Loc l) \<longrightarrow> l:Dom h) \<and>
                (\<forall> ll c F f l . lookup h ll = Some(c,F) \<longrightarrow>
                               lookup F f = Some(RVal(Loc l))
                                 \<longrightarrow> l:Dom h)))"
*)

definition noLowDPs::"State \<Rightarrow> bool"
where "noLowDPs S = (case S of (s,h) \<Rightarrow> 
   ((\<forall> x l . CONTEXT x = low \<longrightarrow> s x = RVal(Loc l) \<longrightarrow> l:Dom h) \<and>
    (\<forall> ll c F f l . lookup h ll = Some(c,F) \<longrightarrow> GAMMA f = low \<longrightarrow>
                    lookup F f = Some(RVal(Loc l)) \<longrightarrow> l:Dom h)))"

text\<open>The motivation for introducing this notion stems from the
intended interpretation of the proof rule for skip, where the initial
and final states should be low equivalent. However, in the presence of
dangling pointers, indistinguishability does not hold as such a
dangling pointer is not in the expected bijection \<open>mkId\<close>. In
contrast, for the notion of indistinguishability we use (see the
following definition), reflexivity indeed holds, as proven in lemma
\<open>twiddle_mkId\<close> below. As a small improvement in comparison to
our paper, we now allow dangling pointers in high variables and high
fields since these are harmless.\<close>

definition twiddle::"PBij \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool"
where "twiddle \<beta> s t = (noLowDPs s \<and> noLowDPs t \<and> 
                 (fst s) \<approx>\<^sub>\<beta> (fst t) \<and> twiddleHeap \<beta> (snd s) (snd t))"

abbreviation twiddle_syntax  ("_ \<equiv>\<^sub>_ _" [100,100] 50)
  where "s \<equiv>\<^sub>\<beta> t == twiddle \<beta> s t"

text\<open>The following properties are easily proven by unfolding the
definitions.\<close>

lemma twiddleHeap_isPbij:"twiddleHeap \<beta> h hh \<Longrightarrow> \<beta>:Pbij"
(*<*)
by (simp add:twiddleHeap_def)
(*>*)

lemma isPBij:"s \<equiv>\<^sub>\<beta> t \<Longrightarrow> \<beta>:Pbij"
(*<*)
apply (simp add: twiddle_def, clarsimp)
by (erule twiddleHeap_isPbij) 
(*>*)

lemma twiddleVal_inverse:
  "(\<beta>, w, v) \<in> twiddleVal \<Longrightarrow> (Pbij_inverse \<beta>, v, w) \<in> twiddleVal"
(*<*)
apply (erule twiddleVal.cases) 
  apply clarsimp apply (rule twiddleVal_Null)
  apply clarsimp apply (rule twiddleVal_Loc) 
    apply (erule Pbij_inverseI) 
  apply clarsimp apply (rule twiddleVal_IVal) apply simp
done
(*>*)

lemma twiddleStore_inverse: "s \<approx>\<^sub>\<beta> t \<Longrightarrow> t \<approx>\<^sub>(Pbij_inverse \<beta>) s"
(*<*)
apply (simp add: twiddleStore_def, clarsimp)
apply (rule twiddleVal_inverse) apply fast
done
(*>*)

lemma twiddleHeap_inverse:
  "twiddleHeap \<beta> s t \<Longrightarrow> twiddleHeap (Pbij_inverse \<beta>) t s"
(*<*)
apply (simp add: twiddleHeap_def, clarsimp)
apply (rule, erule Pbij_inverse_Pbij)
apply (rule, simp add:  Pbij_inverse_Rng) 
apply (rule, simp add: Pbij_inverse_Dom)
apply clarsimp
  apply (erule_tac x=ll in allE, erule_tac x=l in allE, erule impE, erule Pbij_inverseD) 
  apply clarsimp
  apply (simp add: twiddleObj_def, clarsimp)
  apply (erule_tac x=f in allE, clarsimp)
  apply (erule twiddleVal_inverse)
done
(*>*)

lemma Pbij_inverse_twiddle: "\<lbrakk>s \<equiv>\<^sub>\<beta> t\<rbrakk> \<Longrightarrow> t \<equiv>\<^sub>(Pbij_inverse \<beta>) s"
(*<*)
apply (simp add: twiddle_def, clarsimp)
apply (rule, erule twiddleStore_inverse)
apply (erule twiddleHeap_inverse)
done
(*>*)

lemma twiddleVal_betaExtend[rule_format]:
  "(\<beta>,v,w):twiddleVal \<Longrightarrow> \<forall> \<gamma>. Pbij_extends \<gamma> \<beta> \<longrightarrow> (\<gamma>,v,w):twiddleVal"
(*<*)
apply (erule twiddleVal.induct)
apply clarsimp apply (rule twiddleVal_Null)
apply clarsimp apply (rule twiddleVal_Loc) apply (simp add: Pbij_extends_def) apply fast
apply clarsimp apply (rule twiddleVal_IVal) apply simp
done
(*>*)

lemma twiddleObj_betaExtend[rule_format]:
  "\<lbrakk>twiddleObj \<beta> o1 o2; Pbij_extends \<gamma> \<beta>\<rbrakk> \<Longrightarrow> twiddleObj \<gamma> o1 o2"
(*<*)
apply (simp add: twiddleObj_def, clarsimp)
apply (erule_tac x=f in allE, erule_tac x=v in allE, clarsimp)
apply (erule twiddleVal_betaExtend) apply assumption 
done
(*>*)

lemma twiddleVal_compose:
  "\<lbrakk>(\<beta>, v, u) \<in> twiddleVal; (\<gamma>, u, w) \<in> twiddleVal\<rbrakk> 
   \<Longrightarrow> (Pbij_compose \<beta> \<gamma>, v, w) \<in> twiddleVal"
(*<*)
apply (erule twiddleVal.cases)
  apply clarsimp
    apply (erule twiddleVal.cases)
    apply clarsimp apply (rule twiddleVal_Null)
    apply clarsimp 
    apply clarsimp
  apply clarsimp
    apply (erule twiddleVal.cases)
    apply clarsimp 
    apply clarsimp apply (rule twiddleVal_Loc) apply (erule Pbij_composeI, assumption)
    apply clarsimp 
  apply clarsimp
    apply (erule twiddleVal.cases)
    apply clarsimp 
    apply clarsimp 
    apply clarsimp apply (rule twiddleVal_IVal) apply simp
done
(*>*)

lemma twiddleHeap_compose: 
  "\<lbrakk> twiddleHeap \<beta> h1 h2; twiddleHeap \<gamma> h2 h3; \<beta> \<in> Pbij; \<gamma> \<in> Pbij\<rbrakk>
   \<Longrightarrow> twiddleHeap (Pbij_compose \<beta> \<gamma>) h1 h3"
(*<*)
apply (simp add: twiddleHeap_def)
apply rule apply (erule Pbij_compose_Pbij) apply assumption
apply rule apply (subgoal_tac "Pbij_Dom (Pbij_compose \<beta> \<gamma>) \<subseteq> Pbij_Dom \<beta>", fast) apply (rule Pbij_compose_Dom)
apply rule apply (subgoal_tac "Pbij_Rng (Pbij_compose \<beta> \<gamma>) \<subseteq> Pbij_Rng \<gamma>", fast) apply (rule Pbij_compose_Rng)
apply (erule conjE)+
apply (rule, rule, rule)
apply (subgoal_tac "\<exists> l1 . (l,l1) : \<beta> \<and> (l1,ll):\<gamma>", erule exE, erule conjE)
prefer 2 apply (simp add: Pbij_compose_def)
apply (subgoal_tac "\<exists> x y . lookup h2 l1 = Some(x,y)", (erule exE)+)
prefer 2 apply (subgoal_tac "l1 : Dom h2", simp add: Dom_def)
         apply (simp add:Pbij_compose_def Pbij_Dom_def) apply clarsimp apply fast
apply (rule, rule, rule)
apply (rule, rule, rule)
apply (erule_tac x=l in allE, erule_tac x=l1 in allE, erule impE, assumption)
apply (erule_tac x=l1 in allE, erule_tac x=ll in allE, erule impE, assumption)
apply (erule_tac x=a in allE, erule_tac x=b in allE, erule impE, assumption)
apply (erule_tac x=x in allE, erule_tac x=y in allE, erule impE, assumption)
apply (erule_tac x=aa in allE, erule_tac x=ba in allE, erule impE, assumption)
apply (erule_tac x=x in allE, erule_tac x=y in allE, erule impE, assumption)
apply (simp add: twiddleObj_def)
apply clarsimp
  apply (subgoal_tac "\<exists> u . lookup y f = Some u", erule exE)
  prefer 2 apply (simp add: LowDom_def) apply (rotate_tac -6) apply (erule thin_rl, erule thin_rl) apply (erule thin_rl) apply fast
  apply (erule_tac x=f in allE, erule_tac x=u in allE, clarsimp)
  apply (erule_tac x=f in allE, erule_tac x=v in allE, clarsimp)
  apply (erule twiddleVal_compose) apply assumption
done
(*>*)

lemma twiddleStore_compose:
  "\<lbrakk>s \<approx>\<^sub>\<beta> r; r\<approx>\<^sub>\<gamma> t\<rbrakk> \<Longrightarrow> s \<approx>\<^sub>(Pbij_compose \<beta> \<gamma>) t"
(*<*)
apply (simp add:twiddleStore_def)
  apply clarsimp apply (erule_tac x=x in allE, clarsimp)+
  apply (erule twiddleVal_compose) apply assumption 
done
(*>*)

lemma twiddle_compose:
  "\<lbrakk>s \<equiv>\<^sub>\<beta> r; r \<equiv>\<^sub>\<gamma> t\<rbrakk> \<Longrightarrow> s \<equiv>\<^sub>(Pbij_compose \<beta> \<gamma>) t"
(*<*)
apply (simp add: twiddle_def)
apply (erule conjE)+
apply rule apply (erule twiddleStore_compose) apply assumption
apply (rule twiddleHeap_compose) apply assumption+
apply (simp add: twiddleHeap_def)
apply (simp add: twiddleHeap_def)
done
(*>*)

lemma twiddle_mkId: "noLowDPs (s,h) \<Longrightarrow> (s,h) \<equiv>\<^sub>(mkId h) (s,h)"
(*<*)
apply (simp add: twiddle_def)
apply rule
  apply (simp add: twiddleStore_def)
    apply (rule, rule) 
    apply (case_tac "s x")
    apply (rename_tac Var Ref)
    apply clarsimp apply (case_tac Ref) 
      apply clarsimp apply (rule twiddleVal_Null) 
      apply clarsimp apply (rule twiddleVal_Loc) apply (rule mkId4) apply (simp add: noLowDPs_def)
      apply clarsimp apply (simp add: twiddleVal_IVal)
(*twiddleHeap*)
  apply (simp add: twiddleHeap_def) 
  apply (rule, rule mkId1)
  apply (rule, simp add: mkId2) 
  apply (rule, simp add: mkId2b Dom_def) 
  apply clarsimp 
      apply (simp add: twiddleObj_def) apply (drule mkId4b) apply clarsimp
        apply (case_tac v, clarsimp)
        apply (rename_tac Ref)
        apply (case_tac Ref, clarsimp)
        apply (rule twiddleVal_Null)
        apply clarsimp apply (rule twiddleVal_Loc) apply (rule mkId4) apply (simp add: noLowDPs_def) 
        apply clarsimp apply (rule twiddleVal_IVal) apply simp
done(*>*)


text\<open>We call expressions (semantically) low if the following
predicate is satisfied. In particular, this means that if $e$
evaluates in $s$ (respecitvely, $t$) to some location $l$, then $l
\in Pbij\_dom(\beta)$ ($l \in Pbij\_cod(\beta)$) holds.\<close>

definition Expr_low::"Expr \<Rightarrow> bool"
where "Expr_low e = (\<forall> s t \<beta>. s \<approx>\<^sub>\<beta> t \<longrightarrow> (\<beta>, evalE e s, evalE e t):twiddleVal)"

text\<open>A similar notion is defined for boolean expressions, but the
fact that these evaluate to (meta-logical) boolean values allows us to
replace indistinguishability by equality.\<close>

definition BExpr_low::"BExpr \<Rightarrow> bool"
where "BExpr_low b = (\<forall> s t \<beta> . s \<approx>\<^sub>\<beta> t \<longrightarrow> evalB b s = evalB b t)"

subsubsection\<open>Definition and characterisation of security\<close>

text\<open>Now, the notion of security, as defined in the paper. Banerjee
and Naumann's paper~\cite{DBLP:journals/jfp/BanerjeeN05} and the
Mobius Deliverable 2.3~\cite{MobiusDeliverable2.3} contain similar
notions.\<close>

definition secure::"OBJ \<Rightarrow> bool"
where "secure c = (\<forall> s ss t tt \<beta> . 
               s \<equiv>\<^sub>\<beta> ss \<longrightarrow> (s,c \<Down> t) \<longrightarrow> (ss,c \<Down> tt) \<longrightarrow>
               (\<exists> \<gamma> . t \<equiv>\<^sub>\<gamma> tt \<and> Pbij_extends \<gamma> \<beta>))"

(*<*)
lemma Skip1: "secure Skip"
apply (simp only: secure_def Sem_def twiddle_def)
apply (rule, rule, rule, rule, rule, rule)
apply (rule, rule, erule exE, erule exE)
apply (erule Sem_eval_cases)
apply (erule Sem_eval_cases)
apply (rule_tac x=\<beta> in exI)
apply simp
apply (rule Pbij_extends_reflexive)
done

lemma AssignAux:
  "\<lbrakk> Expr_low e; s \<equiv>\<^sub>\<beta> t\<rbrakk> 
  \<Longrightarrow> (update (fst s) x (evalE e (fst s)), snd s) \<equiv>\<^sub>\<beta>
      (update (fst t) x (evalE e (fst t)), snd t)"
apply (simp only: twiddle_def Expr_low_def)
apply rule apply (simp add: noLowDPs_def) 
  apply (case_tac s, clarsimp, hypsubst_thin) apply (rename_tac s h y t k l)
  apply (case_tac "x=y", clarsimp) apply (simp add: update_def) 
    apply (erule_tac x=s in allE)
    apply (erule_tac x=t in allE, clarsimp)
    apply (erule_tac x=\<beta> in allE, erule impE, assumption)
    apply (erule twiddleVal.cases, clarsimp) prefer 2 apply clarsimp apply clarsimp
    apply (simp add: twiddleHeap_def) apply (simp add: Pbij_Dom_def) apply fast
  apply (simp add: update_def)
apply rule apply (simp add: noLowDPs_def)
  apply (case_tac s, clarsimp, hypsubst_thin) apply (rename_tac s h t k y l) 
  apply (case_tac "x=y", clarsimp) apply (simp add: update_def) 
    apply (erule_tac x=s in allE)
    apply (erule_tac x=t in allE)
    apply (erule_tac x=\<beta> in allE, clarsimp)
    apply (erule twiddleVal.cases, clarsimp) prefer 2 apply clarsimp apply clarsimp
    apply (simp add: twiddleHeap_def) apply (simp add: Pbij_Rng_def) apply fast
  apply (simp add: update_def)
apply rule
prefer 2 apply simp
apply (unfold twiddleStore_def)
  apply (rule, rule)
  apply (case_tac "x=xa", clarsimp)
    apply (erule_tac x="fst s" in allE)
    apply (erule_tac x="fst t" in allE)
    apply (erule_tac x=\<beta> in allE, clarsimp)
    apply (simp add: update_def)
  apply (simp add: update_def)
done

lemma Assign1: 
  "Expr_low e \<Longrightarrow> secure (Assign x e)"
apply (simp only: secure_def Sem_def)
apply (rule, rule, rule, rule, rule, rule)
apply (rule, rule, erule exE, erule exE)
apply (erule Sem_eval_cases)
apply (erule Sem_eval_cases)
apply (rule_tac x=\<beta> in exI)
apply simp
apply rule
apply (rule AssignAux) apply fastforce apply assumption
apply (rule Pbij_extends_reflexive)
done

lemma Comp1: "\<lbrakk>secure c1; secure c2\<rbrakk> \<Longrightarrow> secure (Comp c1 c2)"
apply (simp only: secure_def Sem_def)
apply (rule, rule, rule, rule, rule, rule)
apply (rule, rule)
apply (erule exE, erule exE)
apply (erule Sem_eval_cases, erule Sem_eval_cases)
apply (erule_tac x=s in allE, rotate_tac -1)
apply (erule_tac x=ss in allE, rotate_tac -1)
apply (erule_tac x=r in allE, rotate_tac -1)
apply (erule_tac x=ra in allE, rotate_tac -1)
apply (erule_tac x=\<beta> in allE, rotate_tac -1)
apply (erule impE, assumption)
apply (erule impE, rule, assumption)
apply (erule impE, rule, assumption)
apply (erule exE, erule conjE)
apply (erule_tac x=r in allE, rotate_tac -1)
apply (erule_tac x=ra in allE, rotate_tac -1)
apply (erule_tac x=t in allE, rotate_tac -1)
apply (erule_tac x=tt in allE, rotate_tac -1)
apply (erule_tac x=\<gamma> in allE, rotate_tac -1)
apply (erule impE, assumption)
apply (erule impE, rule, assumption)
apply (erule impE, rule, assumption)
apply (erule exE, erule conjE)
apply (rule_tac x=\<gamma>' in exI, simp)
apply (rule Pbij_extends_transitive)
apply (assumption, assumption)
done

lemma Iff1:
  "\<lbrakk>BExpr_low b; secure c1; secure c2\<rbrakk> \<Longrightarrow> secure (Iff b c1 c2)"
apply (simp only: secure_def Sem_def BExpr_low_def)
apply (rule, rule, rule, rule, rule, rule)
apply (rule, rule)
apply (erule exE, erule exE)
apply (erule Sem_eval_cases, erule Sem_eval_cases)
apply (rotate_tac 2, erule thin_rl)
apply (erule_tac x=s in allE, rotate_tac -1)
apply (erule_tac x=ss in allE, rotate_tac -1)
apply (erule_tac x=t in allE, rotate_tac -1)
apply (erule_tac x=tt in allE, rotate_tac -1)
apply (erule_tac x=\<beta> in allE, clarsimp)
apply (erule impE, rule, assumption)
apply (erule impE, rule, assumption)
apply assumption
apply (erule_tac x="fst s" in allE, erule thin_rl, erule thin_rl)
apply (erule_tac x="fst ss" in allE)
apply (erule_tac x=\<beta> in allE, erule impE, simp add: twiddle_def)
apply simp
apply (erule Sem_eval_cases)
apply (erule_tac x="fst s" in allE, erule thin_rl, erule thin_rl)
apply (erule_tac x="fst ss" in allE)
apply (erule_tac x=\<beta> in allE, erule impE, simp add: twiddle_def)
apply simp
apply (erule thin_rl, erule thin_rl)
apply (erule_tac x=s in allE, rotate_tac -1)
apply (erule_tac x=ss in allE, rotate_tac -1)
apply (erule_tac x=t in allE, rotate_tac -1)
apply (erule_tac x=tt in allE, rotate_tac -1)
apply (erule_tac x=\<beta> in allE, rotate_tac -1)
apply (erule impE, assumption)
apply (erule impE, rule, assumption)
apply (erule impE, rule, assumption)
apply assumption
done
(*>*)

text\<open>The type of invariants $\Phi$ includes a component that holds a
partial bijection.\<close>

type_synonym TT = "(State \<times> State \<times> PBij) \<Rightarrow> bool"

text\<open>The operator constructing an assertion from an invariant.\<close>

definition Sec :: "TT \<Rightarrow> Assn"
where "Sec \<Phi> s t =
   ((\<forall> r \<beta>. s \<equiv>\<^sub>\<beta> r \<longrightarrow> \<Phi>(t,r,\<beta>)) \<and>
    (\<forall> r \<beta> . \<Phi> (r,s,\<beta>) \<longrightarrow> (\<exists> \<gamma> . r \<equiv>\<^sub>\<gamma> t \<and> Pbij_extends \<gamma> \<beta>)))"

text\<open>The lemmas proving that the operator ensures security, and that
secure programs satisfy an assertion formed by the operator, are
proven in a similar way as in Section \ref{sec:BaseLineNI}.\<close>

lemma Prop1A:"\<Turnstile> c : Sec \<Phi> \<Longrightarrow> secure c"
(*<*)
apply (simp only: VDM_valid_def secure_def Sec_def) 
apply (rule, rule, rule, rule)
apply (rule, rule, rule, rule)
apply (subgoal_tac "(\<forall>r \<beta>. s \<equiv>\<^sub>\<beta> r \<longrightarrow> \<Phi>(t, r, \<beta>)) \<and>
              (\<forall>r \<beta>. \<Phi>(r, s, \<beta>) \<longrightarrow> (\<exists>\<gamma>. r \<equiv>\<^sub>\<gamma> t \<and> Pbij_extends \<gamma> \<beta>))")
prefer 2 apply fast
apply (erule_tac x=ss in allE, erule_tac x=tt in allE, erule impE, assumption)
apply clarsimp
done
(*>*)

lemma Prop1B:
 "secure c \<Longrightarrow> \<Turnstile> c : Sec (\<lambda> (r, t, \<beta>). \<exists> s. s , c \<Down> r \<and> s \<equiv>\<^sub>\<beta> t)"
(*<*)
apply (simp only: VDM_valid_def Sec_def)
apply (rule, rule) apply (rule, rule)
apply (rule, rule, rule)
  apply simp
  apply (case_tac s, clarsimp)
  apply (rule_tac x=ac in exI, rule_tac x=bc in exI, simp)
apply (rule, rule)
  apply (rule)
  apply simp
  apply ((erule exE)+, (erule conjE)+) 
  apply (unfold secure_def)
  apply (erule_tac x="(a,b)" in allE, erule_tac x=s in allE)
  apply (erule_tac x=r in allE, erule_tac x=t in allE)
  apply (erule_tac x=\<beta> in allE)
  apply (erule impE, assumption)+
  apply (erule exE, erule conjE)
  apply (rule_tac x=\<gamma> in exI, simp)
(*  apply (rule Pbij_extends_RCompl)*)
done
(*>*)

lemma Prop1BB:"secure c \<Longrightarrow> \<exists> \<Phi> . \<Turnstile> c : Sec \<Phi>"
(*<*)
by (drule Prop1B, fast)
(*>*)

lemma Prop1:
 "secure c = (\<Turnstile> c : Sec (\<lambda> (r, t,\<beta>) . \<exists> s . (s , c \<Down> r) \<and> s \<equiv>\<^sub>\<beta> t))"
(*<*)
apply rule
apply (erule Prop1B)
apply (erule Prop1A)
done
(*>*)

subsection\<open>Derivation of proof rules\<close>
text\<open>\label{sec:ObjDerivedRules}\<close>
subsubsection\<open>Low proof rules\<close>
(*<*)
lemma SkipSem: "\<Turnstile> Skip : Sec (\<lambda> (s, t, \<beta>) . s \<equiv>\<^sub>\<beta> t)"
apply (simp only: VDM_valid_def Sec_def Sem_def)
apply (rule, rule, rule)
apply (erule exE)
apply (erule Sem_eval_cases)
apply rule
  apply simp
apply (rule, rule, rule)
  apply (rule_tac x=\<beta> in exI, simp)
  apply (rule Pbij_extends_reflexive)
done
(*>*)

lemma SKIP: "G \<rhd> Skip : Sec (\<lambda> (s, t, \<beta>) . s \<equiv>\<^sub>\<beta> t)"
(*<*)
apply (rule VDMConseq, rule VDMSkip)
apply (simp only: Sec_def)
apply (rule, rule, rule)
apply rule
  apply simp
apply (rule, rule, rule)
  apply (rule_tac x=\<beta> in exI,simp)
  apply (rule Pbij_extends_reflexive)
done
(*>*)

lemma ASSIGN:
  "Expr_low e
  \<Longrightarrow> G \<rhd> Assign x e : Sec (\<lambda> (s, t, \<beta>) .
          \<exists> r . s = (update (fst r) x (evalE e (fst r)), snd r)
                \<and> r \<equiv>\<^sub>\<beta> t)"
(*<*)
apply (rule VDMConseq, rule VDMAssign)
apply (simp only: Sec_def Expr_low_def)
apply (rule, rule, rule)
apply rule
apply (rule, rule, rule)
  apply simp
  apply (erule_tac x="fst s" in allE, erule_tac x="fst r" in allE, erule_tac x=\<beta> in allE, erule impE)
    apply (simp add: twiddle_def)
  apply (simp add: twiddle_def)
  apply (simp add: twiddleStore_def)
  apply (erule conjE)
  apply (rule_tac x="fst s" in exI, simp)
apply (rule, rule, rule)
  apply simp
  apply (erule exE)+
  apply (erule conjE)+
  apply (rule_tac x=\<beta> in exI)
  apply rule prefer 2 apply (rule Pbij_extends_reflexive)
  apply clarsimp
    apply (simp add: twiddle_def)
    apply (simp add: twiddleStore_def)
    apply clarsimp
    apply (case_tac "xa=x")
      apply (simp add: update_def noLowDPs_def) 
      apply (rule, clarsimp) apply (erule_tac x=ac in allE, erule_tac x=a in allE, erule_tac x=\<beta> in allE, erule impE, assumption)
        apply (erule twiddleVal.cases, clarsimp) 
          apply (simp add: twiddleHeap_def  Pbij_Dom_def, clarsimp) apply fast
        apply clarsimp
      apply clarsimp  apply (erule_tac x=ac in allE, erule_tac x=a in allE, erule_tac x=\<beta> in allE, erule impE, assumption)
        apply (erule twiddleVal.cases, clarsimp) 
          apply (simp add: twiddleHeap_def  Pbij_Rng_def, clarsimp) apply fast
        apply clarsimp
    apply (simp add: update_def noLowDPs_def) 
      apply (rule, clarsimp) apply (erule_tac x=ac in allE, erule_tac x=a in allE, erule_tac x=\<beta> in allE, erule impE, assumption)
        apply (erule twiddleVal.cases, clarsimp) 
          apply (simp add: twiddleHeap_def  Pbij_Dom_def, clarsimp) apply fast
        apply clarsimp
      apply clarsimp  apply (erule_tac x=ac in allE, erule_tac x=a in allE, erule_tac x=\<beta> in allE, erule impE, assumption)
        apply (erule twiddleVal.cases, clarsimp) 
          apply (simp add: twiddleHeap_def  Pbij_Rng_def, clarsimp) apply fast
        apply clarsimp
done
(*>*)

(*<*)
lemma CompSem: 
  "\<lbrakk> \<Turnstile> c1 : Sec \<Phi>; \<Turnstile> c2 : Sec \<Psi>\<rbrakk> \<Longrightarrow>
   \<Turnstile> (Comp c1 c2) : Sec (\<lambda> (s, t, \<beta>) . \<exists> r . \<Phi>(r, t, \<beta>) \<and> 
                                      (\<forall> w \<gamma>. r \<equiv>\<^sub>\<gamma> w \<longrightarrow> \<Psi>(s, w, \<gamma>)))"
apply (simp only: VDM_valid_def Sec_def Sem_def)
apply (rule, rule, rule)
apply (erule exE)
apply (erule Sem_eval_cases)
apply (erule_tac x=s in allE, rotate_tac -1)
apply (erule_tac x=r in allE, rotate_tac -1)
apply (erule impE, rule, assumption)
apply (erule_tac x=r in allE, rotate_tac -1)
apply (erule_tac x=t in allE, rotate_tac -1)
apply (erule impE, rule, assumption)
apply (erule thin_rl, erule thin_rl)
apply (erule conjE)+
apply rule
  apply (rule, rule, rule)
  apply (erule_tac x=ra in allE, rotate_tac -1)
  apply (erule_tac x=\<beta> in allE, rotate_tac -1)
  apply (erule impE, assumption)
  apply simp
  apply (case_tac r, clarsimp)
  apply (rule_tac x=ad in exI, rule_tac x=bd in exI, simp)
apply (rule, rule, rule)
  apply simp
  apply (erule exE)+ apply (erule conjE)+
  apply (rotate_tac 2, erule_tac x=a in allE)
  apply (rotate_tac -1, erule_tac x=b in allE)
  apply (rotate_tac -1, erule_tac x=\<beta> in allE)
  apply (rotate_tac -1, erule impE, assumption)
  apply (erule exE, erule conjE)
  apply (case_tac r, clarsimp)
  apply (rotate_tac 3, erule_tac x=aaa in allE)
  apply (rotate_tac -1, erule_tac x=baa in allE)
  apply (rotate_tac -1, erule_tac x=\<gamma> in allE)
  apply (erule impE, assumption)
  apply (rotate_tac 5, erule_tac x=ac in allE)
  apply (rotate_tac -1, erule_tac x=bc in allE)
  apply (rotate_tac -1, erule_tac x=\<gamma> in allE)
  apply (erule impE, assumption)
  apply (erule exE)
  apply (erule conjE)
  apply (rule_tac x=\<gamma>' in exI, rule, assumption)
apply (erule Pbij_extends_transitive) apply assumption
done
(*>*)

lemma COMP:
  "\<lbrakk> G \<rhd> c1 : Sec \<Phi>; G \<rhd> c2 : Sec \<Psi>\<rbrakk>
  \<Longrightarrow> G \<rhd> (Comp c1 c2) : Sec (\<lambda> (s, t, \<beta>) . 
           \<exists> r . \<Phi>(r, t, \<beta>) \<and> (\<forall> w \<gamma>. r \<equiv>\<^sub>\<gamma> w \<longrightarrow> \<Psi>(s, w, \<gamma>)))"
(*<*)
apply (rule VDMConseq, rule VDMComp)
apply (assumption, assumption)
apply (simp only: Sec_def)
apply (rule, rule, rule)
apply (erule exE)
apply (erule conjE)+
apply (erule thin_rl, erule thin_rl)
apply rule
  apply (rule, rule, rule)
  apply simp
  apply (case_tac ra, clarsimp)
  apply (erule_tac x=ad in allE, rotate_tac -1)
  apply (erule_tac x=bd in allE, rotate_tac -1)
  apply (erule_tac x=\<beta> in allE, rotate_tac -1)
  apply (erule impE, assumption)
  apply (rule_tac x=ab in exI, rule_tac x=bb in exI, simp)
apply (rule, rule, rule)
  apply simp
  apply (erule exE)+ apply (erule conjE)+
  apply (rotate_tac 1, erule_tac x=a in allE)
  apply (rotate_tac -1, erule_tac x=b in allE)
  apply (rotate_tac -1, erule_tac x=\<beta> in allE)
  apply (rotate_tac -1, erule impE, assumption)
  apply (erule exE, erule conjE)
  apply (case_tac r, clarsimp)
  apply (rotate_tac 3, erule_tac x=aaa in allE)
  apply (rotate_tac -1, erule_tac x=baa in allE)
  apply (rotate_tac -1, erule_tac x=\<gamma> in allE)
  apply (erule impE, assumption)
  apply (rotate_tac 4, erule_tac x=ac in allE)
  apply (rotate_tac -1, erule_tac x=bc in allE)
  apply (rotate_tac -1, erule_tac x=\<gamma> in allE)
  apply (erule impE, assumption)
  apply (erule exE)
  apply (erule conjE)
  apply (rule_tac x=\<gamma>' in exI, rule, assumption)
apply (erule Pbij_extends_transitive) apply assumption
done(*>*)

(*<*)
lemma IffSem: 
  "\<lbrakk> BExpr_low b; \<Turnstile> c1 : Sec \<Phi>; \<Turnstile> c2 : Sec \<Psi>\<rbrakk> \<Longrightarrow>
   \<Turnstile> (Iff b c1 c2) : (Sec (\<lambda> (s, t, \<beta>) .
                       (evalB b (fst t) \<longrightarrow> \<Phi>(s,t, \<beta>)) \<and> 
                       ((\<not> evalB b (fst t)) \<longrightarrow> \<Psi>(s,t,\<beta>))))"
apply (simp only: VDM_valid_def Sec_def Sem_def BExpr_low_def)
apply (rule, rule, rule)
apply (erule exE)
apply (erule Sem_eval_cases)
apply rule
  apply (rule, rule, rule)
  apply simp
  apply (erule_tac x="fst s" in allE, rotate_tac -1)
  apply (erule_tac x="fst r" in allE, rotate_tac -1)
  apply (erule impE, rule_tac x=\<beta> in exI, simp add: twiddle_def)
  apply (case_tac s, clarsimp)
  apply (erule_tac x=ac in allE, rotate_tac -1)
  apply (erule_tac x=bc in allE, rotate_tac -1)
  apply (erule_tac x=aa in allE, rotate_tac -1)
  apply (erule_tac x=ba in allE, rotate_tac -1)
  apply (erule impE, rule, assumption)
(*  apply (simp add: twiddle_def)*)
  apply clarsimp
  apply (rule, rule, rule)
  apply simp
  apply (case_tac s, clarsimp)
  apply (rotate_tac 1)
  apply (erule_tac x=ac in allE, rotate_tac -1)
  apply (erule_tac x=bc in allE, rotate_tac -1)
  apply (erule_tac x=aa in allE, rotate_tac -1)
  apply (erule_tac x=ba in allE, rotate_tac -1)
  apply (erule impE, rule, assumption)
  apply clarsimp
apply rule
  apply (rule, rule, rule, rule)
  apply simp
  apply (case_tac s, clarsimp)
  apply (erule_tac x=ac in allE, rotate_tac -1)
  apply (erule_tac x=ab in allE, rotate_tac -1)
  apply (erule impE) apply(rule_tac x=\<beta> in exI, simp add: twiddle_def)
  apply clarsimp apply (erule thin_rl, erule_tac x=ac in allE)
                 apply (erule_tac x=bc in allE, erule_tac x=aa in allE, erule_tac x=ba in allE, erule impE)
                   apply (rule, assumption)
                apply clarsimp
  apply clarsimp apply (erule thin_rl, erule thin_rl, erule_tac x=a in allE)
                 apply (erule_tac x=ba in allE, erule_tac x=aa in allE, erule_tac x=baa in allE, erule impE)
                   apply (rule, assumption)
                apply clarsimp
done
(*>*)

lemma IFF:
  "\<lbrakk> BExpr_low b; G \<rhd> c1 : Sec \<Phi>; G \<rhd> c2 : Sec \<Psi>\<rbrakk> 
 \<Longrightarrow> G \<rhd> (Iff b c1 c2) : Sec (\<lambda> (s,t,\<beta>) .
                         (evalB b (fst t) \<longrightarrow> \<Phi>(s,t,\<beta>)) \<and> 
                         ((\<not> evalB b (fst t)) \<longrightarrow> \<Psi>(s,t,\<beta>)))"
(*<*)
apply (rule VDMConseq, rule VDMIff) 
apply (assumption, assumption)
apply (simp only: Sec_def BExpr_low_def)
apply (rule, rule, rule)
apply (rule, rule, rule, rule)
  apply (erule_tac x="fst s" in allE, rotate_tac -1)
  apply (erule_tac x="fst r" in allE, rotate_tac -1)
  apply (erule_tac x=\<beta> in allE, rotate_tac -1)
  apply (simp add: twiddle_def)
  apply clarsimp
apply (rule, rule, rule)
  apply (case_tac "evalB b (fst s)")
  apply clarsimp
  apply clarsimp
done
(*>*)

(*<*)
lemma noLowDPs_NEW:
  "noLowDPs (s,h) \<Longrightarrow> noLowDPs (update s x (RVal (Loc l)), (l, C, []) # h)"
apply (simp add: noLowDPs_def update_def, clarsimp)
apply (rule, clarsimp)
  apply (rule, clarsimp) apply (simp add: Dom_def)
  apply clarsimp apply (simp add: Dom_def)
apply clarsimp apply (erule_tac x=ll in allE, clarsimp) apply (simp add: Dom_def)
done
(*>*)

lemma NEW:
  "CONTEXT x = low
  \<Longrightarrow> G \<rhd> (New x C) : Sec (\<lambda> (s,t,\<beta>) . 
                 \<exists> l r . l \<notin> Dom (snd r) \<and> r \<equiv>\<^sub>\<beta> t \<and> 
                         s = (update (fst r) x (RVal (Loc l)), 
                                 (l,(C,[])) # (snd r)))"
(*<*)
apply (rule VDMConseq, rule VDMNew)
apply (simp only: Sec_def)
apply (rule, rule, rule)
apply (erule exE, (erule conjE)+)
apply rule
(*First part of Sec*)
apply (rule, rule, rule)
  apply simp
  apply (rule, rule, assumption)
  apply (rule_tac x="fst s" in exI, simp)
(*Second part of Sec*)
apply (rule, rule, rule)
  apply simp
  apply (erule exE)+
  apply (erule conjE)+
  apply (rule_tac x="insert (la,l) \<beta>" in exI)

  apply rule 
  (*Show twiddle*)
    apply (frule isPBij)
    apply (simp add: twiddle_def, clarsimp)
    apply rule apply (erule noLowDPs_NEW)
    apply rule apply (erule noLowDPs_NEW) 
    (*twiddleStore*)
    apply (simp add: twiddleStore_def)
      apply (rule, rule)
        apply (case_tac "x=xa")
        apply (simp add: update_def) apply clarsimp 
          apply (rule twiddleVal_Loc) apply simp
        apply (simp add: update_def) apply clarsimp
         apply (erule_tac x=xa in allE, clarsimp)
         apply (rule twiddleVal_betaExtend, assumption) apply (simp add: Pbij_extends_def) apply fast
    (*twiddleHeap*)     
    apply (simp add: twiddleHeap_def) apply clarsimp
      apply rule apply (erule Pbij_insert) apply fast apply fast 
      apply (rule, simp add: Pbij_Dom_def Dom_def) apply fast 
      apply (rule, simp add: Pbij_Rng_def Dom_def) apply fast
      apply (rule, rule)
        apply clarsimp
        apply (rule, clarsimp)
          apply (rule, clarsimp) apply (simp add: twiddleObj_def)
          apply clarsimp apply (simp add: twiddleObj_def)
        apply clarsimp apply (simp add: Pbij_Dom_def) apply fast 
      apply clarsimp
        apply (rule, clarsimp) apply (simp add: Pbij_Rng_def) apply fast 
      apply clarsimp
          apply (erule_tac x=lb in allE, erule_tac x=ll in allE, clarsimp)
          apply (rule twiddleObj_betaExtend) apply assumption+ apply (simp add: Pbij_extends_def) apply fast
  (*Pbij_extends*)
    apply (simp add: Pbij_extends_def) apply fast 
done
(*>*)

lemma GET: 
  "\<lbrakk> CONTEXT y = low; GAMMA f = low\<rbrakk>
  \<Longrightarrow> G \<rhd> Get x y f : Sec (\<lambda> (s,t,\<beta>) .
               \<exists> r l C Flds v. (fst r) y = RVal(Loc l) \<and> 
                               lookup (snd r) l = Some(C,Flds) \<and> 
                               lookup Flds f = Some v \<and> r \<equiv>\<^sub>\<beta> t \<and> 
                               s = (update (fst r) x v, snd r))"
(*<*)
apply (rule VDMConseq, rule VDMGet)
apply (simp only: Sec_def)
apply (rule, rule, rule)
apply (erule exE)+
apply (erule conjE)+
apply rule
  apply (rule, rule, rule)
  apply simp
  apply (rule, rule, rule)
  apply (rule, assumption)
  apply (rule, rule, rule, assumption)
  apply (rule, rule, assumption)
  apply simp
apply (rule, rule, rule)
  apply simp
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply (erule conjE)+
  apply (rule_tac x=\<beta> in exI, rule)
  prefer 2 apply (rule Pbij_extends_reflexive)
  apply (simp add: twiddle_def, (erule conjE)+)
    apply (rule, simp add: noLowDPs_def update_def, clarsimp)
    apply (rule, simp add: noLowDPs_def update_def)
    apply (simp add: twiddleStore_def) apply clarsimp
    apply (case_tac "x=xa", clarsimp) prefer 2  apply (simp add: update_def)
    apply (simp add:update_def) apply (simp add: twiddleHeap_def) apply clarsimp
    apply (erule_tac x=y in allE, clarsimp)
    apply (erule twiddleVal.cases)
    apply clarsimp
    prefer 2 apply clarsimp
    apply clarsimp
      apply (erule_tac x=l1 in allE) 
      apply (erule_tac x=l2 in allE, clarsimp) 
      apply (simp add: twiddleObj_def)
done
(*>*)

lemma PUT: 
  "\<lbrakk> CONTEXT x = low; GAMMA f = low; Expr_low e\<rbrakk>
  \<Longrightarrow> G \<rhd> Put x f e: Sec (\<lambda> (s,t,\<beta>) .
           \<exists> r l C Flds. (fst r) x = RVal(Loc l) \<and> r \<equiv>\<^sub>\<beta> t \<and>
                         lookup (snd r) l = Some(C,Flds) \<and> 
                         s = (fst r, 
                              (l,(C,(f,evalE e (fst r)) # Flds)) # (snd r)))"
(*<*)
apply (rule VDMConseq, rule VDMPut)
apply (simp only: Sec_def Expr_low_def)
apply (rule, rule, rule)
apply (erule exE)+
apply (erule conjE)+
apply rule
  apply (rule, rule, rule)
  apply simp
apply (rule, rule, rule)
  apply simp
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply (erule conjE)+
  apply (rule_tac x=\<beta> in exI, rule)
  prefer 2 apply (rule Pbij_extends_reflexive)
  apply (simp add: twiddle_def)
  apply (simp add: twiddleStore_def)
  apply (simp add: twiddleHeap_def)
  apply clarsimp
  apply (rule, rotate_tac -1, erule thin_rl, simp add: noLowDPs_def) 
    apply (rule, clarsimp) apply (subgoal_tac "lb : Dom bc", simp add: Dom_def) 
      apply (erule_tac x=xa in allE, erule impE, assumption,
             erule_tac x=lb in allE, erule mp, assumption) 
    apply clarsimp apply (rule, clarsimp)
                     apply (rule, clarsimp) 
                       apply (erule_tac x=ac in allE, erule_tac x=a in allE, erule_tac x=\<beta> in allE, erule impE, assumption) 
                       apply (erule twiddleVal.cases, clarsimp) 
                         apply clarsimp apply (subgoal_tac "la : Dom bc", simp add: Dom_def) 
                                        apply (simp add: Pbij_Dom_def) apply fast
                         apply clarsimp
                     apply clarsimp apply (erule_tac x=ll in allE, clarsimp)
                                    apply (erule_tac x=fa in allE, clarsimp) apply (simp add: Dom_def)
                   apply clarsimp apply (erule_tac x=ll in allE, clarsimp)
                                    apply (erule_tac x=fa in allE, clarsimp) apply (simp add: Dom_def)
  apply (rule, rotate_tac -1, erule thin_rl, simp add: noLowDPs_def) 
    apply (rule, clarsimp) apply (subgoal_tac "lb : Dom b", simp add: Dom_def) 
      apply (erule_tac x=xa in allE, erule impE, assumption,
             erule_tac x=lb in allE, erule mp, assumption) 
    apply clarsimp apply (rule, clarsimp)
                     apply (rule, clarsimp) 
                       apply (erule_tac x=ac in allE, erule_tac x=a in allE, erule_tac x=\<beta> in allE, erule impE, assumption) 
                       apply (erule twiddleVal.cases, clarsimp) 
                         apply clarsimp apply (subgoal_tac "l : Dom b", simp add: Dom_def) 
                                        apply (simp add: Pbij_Rng_def) apply fast
                         apply clarsimp
                     apply clarsimp apply (erule_tac x=ll in allE, clarsimp)
                                    apply (erule_tac x=fa in allE, clarsimp) apply (simp add: Dom_def)
                   apply clarsimp apply (erule_tac x=ll in allE, clarsimp)
                                    apply (erule_tac x=fa in allE, clarsimp) apply (simp add: Dom_def)
  apply (rule, rotate_tac -1, erule thin_rl, simp add: Dom_def) apply fast
  apply (rule, rotate_tac -1, erule thin_rl, simp add: Dom_def) apply fast
  apply clarsimp
  apply (rule, rule, rule)
  apply rule apply clarsimp
             apply (erule_tac x=lb in allE, rotate_tac -1)
             apply (erule_tac x=ll in allE, rotate_tac -1, clarsimp)
             apply (erule_tac x=ac in allE, erule_tac x=a in allE, erule_tac x=\<beta> in allE, erule impE, assumption)
             apply (simp add: twiddleObj_def, clarsimp)
             apply (simp add: LowDom_def) apply (rotate_tac -1, erule thin_rl) 
             apply rule apply (rule, clarsimp) apply fast
               apply (rule, clarsimp) apply fast
             apply clarsimp apply (erule_tac x=x in allE, clarsimp)
               apply (erule twiddleVal.cases)
               apply clarsimp 
               apply clarsimp apply (simp add: Pbij_def) apply fast
               apply clarsimp
  apply clarsimp apply (erule_tac x=x in allE, clarsimp)
               apply (erule twiddleVal.cases)
               apply clarsimp 
               apply clarsimp apply (simp add: Pbij_def) 
               apply clarsimp
done
(*>*)

text\<open>Again, we define a fixed point operator over invariants.\<close>

definition FIX::"(TT \<Rightarrow> TT) \<Rightarrow> TT"
where "FIX \<phi> = (\<lambda> (s,t,\<beta>). 
      \<forall> \<Phi> . (\<forall> ss tt \<gamma>. \<phi> \<Phi> (ss, tt,\<gamma>) \<longrightarrow> \<Phi> (ss, tt,\<gamma>)) \<longrightarrow> \<Phi> (s, t,\<beta>))"

definition Monotone::"(TT \<Rightarrow> TT) \<Rightarrow> bool"
where "Monotone \<phi> =
   (\<forall> \<Phi> \<Psi> . (\<forall> s t \<beta>. \<Phi>(s,t,\<beta>) \<longrightarrow> \<Psi>(s,t,\<beta>)) \<longrightarrow> 
               (\<forall> s t \<beta>. \<phi> \<Phi> (s,t,\<beta>) \<longrightarrow> \<phi> \<Psi> (s,t,\<beta>)))"

(*<*)
lemma Fix2: "\<lbrakk>Monotone \<phi>; \<phi> (FIX \<phi>) (s, t,\<beta>)\<rbrakk> \<Longrightarrow> FIX \<phi> (s,t,\<beta>)"
apply (unfold FIX_def)
apply (rule, rule)
apply (rule, rule) 
apply (subgoal_tac "\<phi> \<Phi> (s,t,\<beta>)") apply fast 
apply (subgoal_tac "\<forall> r u \<gamma>. FIX \<phi> (r,u,\<gamma>) \<longrightarrow> \<Phi>(r,u,\<gamma>)")
prefer 2 apply (erule thin_rl) apply (simp add: FIX_def) apply clarsimp
  apply (erule_tac x=\<Phi> in allE, simp)
apply (unfold Monotone_def)
  apply (erule_tac x="FIX \<phi>" in allE, erule_tac x=\<Phi> in allE)
  apply (erule impE) apply assumption
  apply (unfold FIX_def) apply fast 
done

lemma Fix1: "\<lbrakk>Monotone \<phi>; FIX \<phi> (s,t,\<beta>)\<rbrakk> \<Longrightarrow> \<phi> (FIX \<phi>) (s,t,\<beta>)"
apply (simp add: FIX_def) 
apply (erule_tac x="\<phi>(FIX \<phi>)" in allE) 
apply (erule impE)
prefer 2 apply (simp add: FIX_def)
apply (subgoal_tac "\<forall> r u \<gamma>. \<phi> (FIX \<phi>) (r,u,\<gamma>) \<longrightarrow> FIX \<phi> (r,u,\<gamma>)")
  prefer 2 apply clarsimp apply (erule Fix2) apply assumption
apply (unfold Monotone_def)
  apply (erule_tac x="\<phi> (FIX \<phi>)" in allE, erule_tac x="FIX \<phi>" in allE, erule impE) apply assumption
apply simp
done
(*>*)

text\<open>For monotone transformers, the construction indeed
yields a fixed point.\<close>

lemma Fix_lemma:"Monotone \<phi> \<Longrightarrow> \<phi> (FIX \<phi>) = FIX \<phi>"
(*<*)
apply (rule ext, rule iffI)
apply clarsimp apply (erule Fix2) apply assumption
apply clarsimp apply (erule Fix1) apply assumption
done
(*>*)

text\<open>The operator used in the while rule is defined by\<close>

definition PhiWhileOp::"BExpr \<Rightarrow> TT \<Rightarrow> TT \<Rightarrow> TT"
where "PhiWhileOp b \<Phi> = (\<lambda> \<Psi> . (\<lambda> (s, t, \<beta>).
  (evalB b (fst t) \<longrightarrow>
      (\<exists> r. \<Phi> (r, t, \<beta>) \<and> (\<forall> w \<gamma>. r \<equiv>\<^sub>\<gamma> w \<longrightarrow> \<Psi>(s, w, \<gamma>)))) \<and>
  (\<not> evalB b (fst t) \<longrightarrow> s\<equiv>\<^sub>\<beta> t)))"

text\<open>and is monotone:\<close>

lemma PhiWhileOp_Monotone: "Monotone (PhiWhileOp b \<Phi>)"
(*<*)
apply (simp add: PhiWhileOp_def Monotone_def) apply clarsimp
  apply (rule_tac x=ab in exI, rule_tac x=bb in exI, simp)
done
(*>*)

text\<open>Hence, we can define its fixed point:\<close>

definition PhiWhile::"BExpr \<Rightarrow> TT \<Rightarrow> TT"
where "PhiWhile b \<Phi> = FIX (PhiWhileOp b \<Phi>)"

text\<open>The while rule may now be given as follows:\<close>

lemma WHILE:  
  "\<lbrakk> BExpr_low b; G \<rhd> c : (Sec \<Phi>)\<rbrakk> 
  \<Longrightarrow> G \<rhd> (While b c) : (Sec (PhiWhile b \<Phi>))"
(*<*)
apply (rule VDMConseq)
apply (rule VDMWhile) 
prefer 4 apply (subgoal_tac "\<forall>s t. (Sec (PhiWhileOp b \<Phi> (PhiWhile b \<Phi>))) s t \<and> 
                             \<not> evalB b (fst t) \<longrightarrow> Sec (PhiWhile b \<Phi>) s t", assumption)
prefer 2 apply assumption
  apply clarsimp apply (subgoal_tac "PhiWhileOp b \<Phi> (PhiWhile b \<Phi>)= PhiWhile b \<Phi>", clarsimp)
                 apply (simp add: PhiWhile_def) apply (rule Fix_lemma) apply (rule PhiWhileOp_Monotone)
apply clarsimp apply (simp add: Sec_def) 
  apply (rule, clarsimp) apply (simp add: PhiWhileOp_def  BExpr_low_def) 
    apply clarsimp apply (simp add: twiddle_def) apply (erule_tac x=a in allE, erule_tac x=aa in allE, clarsimp) 
  apply clarsimp apply (simp add: PhiWhileOp_def)
    apply (rule_tac x=\<beta> in exI, simp) apply (rule Pbij_extends_reflexive)

apply clarsimp apply (simp add: Sec_def)
  apply rule
  prefer 2 apply clarsimp
    apply (subgoal_tac "\<exists> r1 r2 \<gamma> . \<Phi> ((r1,r2), (a,ba),\<gamma>) \<and> Pbij_extends \<gamma> \<beta> \<and>
                                  (\<forall> w1 w2 \<gamma> . (r1,r2) \<equiv>\<^sub>\<gamma> (w1,w2) \<longrightarrow> 
                                                   (PhiWhile b \<Phi>) ((ac,bc), (w1,w2),\<gamma>))")
    prefer 2 apply (simp add: PhiWhileOp_def) 
      apply (erule exE)+ apply (erule conjE)+ apply (rule_tac x=ad in exI, rule_tac x=bd in exI, rule)
      apply (rule, assumption)
      apply (rule, rule Pbij_extends_reflexive)
      apply assumption
    apply (erule exE)+ apply (erule conjE)+
    apply (rotate_tac 4, erule_tac x=r1 in allE, 
           rotate_tac -1, erule_tac x=r2 in allE, 
           rotate_tac -1, erule_tac x=\<gamma> in allE, erule impE, assumption)
    apply (erule exE, erule conjE)
    apply (rotate_tac 4, erule_tac x=aa in allE, 
           rotate_tac -1, erule_tac x=baa in allE, 
           rotate_tac -1, erule_tac x=\<gamma>' in allE, erule impE, assumption)
    apply (rotate_tac 8, erule_tac x=ac in allE,
           rotate_tac -1, erule_tac x=bc in allE, 
           rotate_tac -1, erule_tac x=\<gamma>' in allE, erule impE)
      apply (subgoal_tac "PhiWhileOp b \<Phi> (PhiWhile b \<Phi>) = (PhiWhile b \<Phi>)", clarsimp)
      apply (simp add: PhiWhile_def)
      apply (rule Fix_lemma) apply (rule PhiWhileOp_Monotone)
    apply (erule exE, erule conjE)
    apply (rule, rule, assumption) apply (erule Pbij_extends_transitive) 
        apply (erule Pbij_extends_transitive) apply assumption

  apply clarsimp
    apply (simp only:  BExpr_low_def)
    apply (erule_tac x=a in allE, rotate_tac -1)
    apply (erule_tac x=ac in allE, rotate_tac -1)
    apply (erule_tac x=\<beta> in allE, rotate_tac -1)
    apply (erule impE, simp add: twiddle_def)
    apply (simp (no_asm_simp) add: PhiWhileOp_def)
    apply clarsimp
    apply (erule thin_rl)
    apply (erule_tac x=ac in allE, rotate_tac -1)
    apply (erule_tac x=bc in allE, rotate_tac -1)
    apply (erule_tac x=\<beta> in allE, rotate_tac -1)
    apply (erule impE, assumption)
    apply (rule_tac x=aa in exI, rule_tac x=baa in exI, rule, assumption) 
    apply clarsimp
    apply (rotate_tac 2)
    apply (erule_tac x=ad in allE, rotate_tac -1)
    apply (erule_tac x=bd in allE, rotate_tac -1)
    apply (erule_tac x=\<gamma> in allE, rotate_tac -1)
    apply (erule impE, assumption)
    apply (subgoal_tac "PhiWhileOp b \<Phi> (PhiWhile b \<Phi>) = PhiWhile b \<Phi>", clarsimp)
    apply (simp add: PhiWhile_def)
    apply (rule Fix_lemma) apply (rule PhiWhileOp_Monotone)
done
(*>*)

text\<open>Operator $\mathit{PhiWhile}$ is itself monotone in $\Phi$:\<close>

lemma PhiWhileMonotone: "Monotone (\<lambda> \<Phi> . PhiWhile b \<Phi>)"
(*<*)
apply (simp add: Monotone_def) apply clarsimp
apply (simp add: PhiWhile_def)
apply (simp add: FIX_def) apply clarsimp
apply (erule_tac x=\<Phi>' in allE, erule mp)
apply (clarsimp) apply (erule_tac x=a in allE, erule_tac x=ba in allE,
                        erule_tac x=aa in allE, erule_tac x=baa in allE,
                        erule_tac x=\<gamma> in allE, erule mp)
apply (simp add: PhiWhileOp_def) apply clarsimp
apply (rule_tac x=ab in exI, rule_tac x=bb in exI, simp)
done
(*>*)

text\<open>We now give an alternative formulation using an inductive
relation equivalent to FIX. First, the definition of the variant.\<close>

inductive_set var::"(BExpr \<times> TT \<times> PBij \<times> State \<times> State) set"
where
varFalse: "\<lbrakk>\<not> evalB b (fst t); s \<equiv>\<^sub>\<beta> t\<rbrakk> \<Longrightarrow> (b,\<Phi>,\<beta>,s,t):var"

| varTrue:
  "\<lbrakk> evalB b (fst t); \<Phi>(r,t,\<beta>); \<forall> w \<gamma>. r \<equiv>\<^sub>\<gamma> w \<longrightarrow> (b,\<Phi>,\<gamma>,s,w): var\<rbrakk>
  \<Longrightarrow> (b,\<Phi>,\<beta>,s,t):var"

text\<open>The equivalence of the invariant with the fixed point
construction.\<close>
(*<*)
lemma varFIX: "(b,\<Phi>,\<beta>,s,t):var \<Longrightarrow> PhiWhile b \<Phi> (s,t,\<beta>)"
apply (erule var.induct)
apply (simp add: PhiWhile_def)
  apply (subgoal_tac "PhiWhileOp b \<Phi> (FIX (PhiWhileOp b \<Phi>)) (s,t,\<beta>)")
  apply (subgoal_tac "PhiWhileOp b \<Phi> (FIX (PhiWhileOp b \<Phi>)) = FIX (PhiWhileOp b \<Phi>)", clarsimp)
  apply (rule Fix_lemma) apply (rule PhiWhileOp_Monotone)
  apply (simp add: PhiWhileOp_def)
apply (simp (no_asm_simp) add: PhiWhile_def)
apply (subgoal_tac "PhiWhileOp b \<Phi> (FIX (PhiWhileOp b \<Phi>)) (s,t,\<beta>)")
  apply (subgoal_tac "PhiWhileOp b \<Phi> (FIX (PhiWhileOp b \<Phi>)) = FIX (PhiWhileOp b \<Phi>)", clarsimp)
  apply (rule Fix_lemma) apply (rule PhiWhileOp_Monotone)
  apply (simp add: PhiWhileOp_def)
  apply (case_tac r, clarsimp)
  apply (rule_tac x=ac in exI, rule_tac x=baa in exI, rule) apply assumption
  apply clarsimp
  apply (erule_tac x=aa in allE)
  apply (erule_tac x=bb in allE)
  apply (erule_tac x=\<gamma> in allE, clarsimp)
  apply (simp add: PhiWhile_def)
  apply (simp add: PhiWhileOp_def)
done

lemma FIXvar: "PhiWhile b \<Phi> (s,t,\<beta>) \<Longrightarrow> (b,\<Phi>,\<beta>,s,t):var"
apply (simp add: PhiWhile_def)
apply (subgoal_tac "PhiWhileOp b \<Phi> (FIX (PhiWhileOp b \<Phi>)) (s, t,\<beta>)")
prefer 2 
  apply (subgoal_tac "PhiWhileOp b \<Phi> (FIX (PhiWhileOp b \<Phi>)) = FIX (PhiWhileOp b \<Phi>)", clarsimp)
  apply (rule Fix_lemma) apply (rule PhiWhileOp_Monotone)
apply (erule thin_rl, simp add: PhiWhileOp_def) apply clarsimp
  apply (case_tac "evalB b (fst t)")
  prefer 2 apply clarsimp apply (rule varFalse) apply assumption+
  apply clarsimp apply (rule varTrue) apply assumption apply assumption
    apply (rule, rule, rule) 
    apply (case_tac w, clarsimp) 
    apply (erule_tac x=aaa in allE, erule_tac x=baa in allE, erule_tac x=\<gamma> in allE, clarsimp)
    apply (unfold FIX_def) apply clarify
    apply (erule_tac x="\<lambda> (x,y,\<beta>) . (b,\<Phi>,\<beta>,x,y):var" in allE, erule impE) prefer 2 apply simp
    apply clarsimp
    apply (case_tac "evalB b ab")
    prefer 2 apply clarsimp apply (rule varFalse) apply simp apply assumption
    apply clarsimp apply (rule varTrue) apply simp apply assumption apply simp
done
(*>*)

lemma varFIXvar: "(PhiWhile b \<Phi> (s,t,\<beta>)) = ((b,\<Phi>,\<beta>,s,t):var)"
(*<*)
apply rule
apply (erule FIXvar)
apply (erule varFIX)
done
(*>*)

(*<*)
lemma FIXvarFIX':
  "(PhiWhile b \<Phi>) = (\<lambda> (s,t,\<beta>) . (b,\<Phi>,\<beta>,s,t):var)"
apply (rule ext, rule iffI)
apply (case_tac x, clarsimp) apply (erule FIXvar)
apply (case_tac x, clarsimp) apply (simp add: varFIXvar) 
done

lemma FIXvarFIX: "(PhiWhile b) = (\<lambda> \<Phi> . (\<lambda> (s,t,\<beta>) . (b,\<Phi>,\<beta>,s,t):var))"
apply rule apply (rule FIXvarFIX')
done
(*>*)

text\<open>Using this equivalence we can derive the while rule given in our
paper from \<open>WHILE\<close>.\<close>

lemma WHILE_IND:
  "\<lbrakk> BExpr_low b; G \<rhd> c : (Sec \<Phi>)\<rbrakk>
  \<Longrightarrow> G \<rhd> While b c: (Sec (\<lambda>(s,t,\<gamma>). (b,\<Phi>,\<gamma>,s,t):var))"
(*<*)
apply (rule VDMConseq)
apply (erule WHILE) apply assumption
apply clarsimp
apply (simp add: FIXvarFIX')
done
(*>*)

text\<open>We can also show the following property.\<close>

(*<*)
lemma varMonotoneAux[rule_format]:
  "(b, \<Phi>, \<beta>, s, t) \<in> var \<Longrightarrow> 
   (\<forall>s t \<gamma>. \<Phi> (s, t, \<gamma>) \<longrightarrow> \<Psi> (s, t, \<gamma>)) \<longrightarrow> 
   (b, \<Psi>, \<beta>, s, t) \<in> var"
apply (erule var.induct)
apply clarsimp apply (rule varFalse) apply simp apply assumption
apply clarsimp apply (rule varTrue) apply simp apply fast apply clarsimp  
done
(*>*)

lemma var_Monotone:
  "Monotone (\<lambda> \<Phi> . (\<lambda> (s,t,\<beta>) .(b,\<Phi>,\<beta>,s,t):var))"
(*<*)
apply (simp add: Monotone_def)
apply clarsimp
apply (rule varMonotoneAux) apply assumption apply clarsimp
done
(*>*)

(*<*)
lemma varMonotone_byFIX: "Monotone (\<lambda> \<Phi> . (\<lambda> (s,t,\<beta>) .(b,\<Phi>,\<beta>,s,t):var))"
apply (subgoal_tac "Monotone (\<lambda> \<Phi> . PhiWhile b \<Phi>)")
apply (simp add: FIXvarFIX)
apply (rule PhiWhileMonotone)
done  
(*>*)

text\<open>The call rule is formulated for an arbitrary fixed point of
a monotone transformer.\<close>

lemma CALL: 
  "\<lbrakk>({Sec (FIX \<phi>)} \<union> X) \<rhd> body : Sec (\<phi> (FIX \<phi>)); Monotone \<phi>\<rbrakk>
  \<Longrightarrow> X \<rhd> Call : Sec (FIX \<phi>)"
(*<*)
apply (rule VDMCall)
apply (subgoal_tac "\<phi> (FIX \<phi>) = FIX \<phi>", clarsimp)
apply (erule Fix_lemma)
done
(*>*)

subsubsection\<open>High proof rules\<close>

definition HighSec::Assn
where "HighSec = (\<lambda> s t . noLowDPs s \<longrightarrow> s \<equiv>\<^sub>(mkId (snd s)) t)"

lemma CAST[rule_format]:
  "G \<rhd> c : HighSec \<Longrightarrow> G \<rhd> c : Sec (\<lambda> (s, t, \<beta>) . s \<equiv>\<^sub>\<beta> t)"
(*<*)
apply (erule VDMConseq)  apply (simp add:Sec_def) apply clarsimp
 apply (rule, clarsimp)
     apply (simp add: HighSec_def)
     apply (simp add: twiddle_def, clarsimp) 
     apply (rule, simp add: twiddleStore_def, clarsimp) 
       apply (erule_tac x=x in allE, clarsimp)
       apply (erule_tac x=x in allE, clarsimp)
       apply (erule twiddleVal.cases)
         apply clarsimp
         apply clarsimp apply (erule twiddleVal.cases)
                          apply clarsimp
                          apply clarsimp apply (drule mkId4b, clarsimp) apply (erule twiddleVal_Loc)
                          apply clarsimp
         apply clarsimp
     apply (simp add: twiddleHeap_def, clarsimp)
       apply (rule, simp add:  mkId2 mkId2b)
       apply (simp add:  mkId2 mkId2b, clarsimp)
         apply (subgoal_tac "l:Dom b")
         prefer 2 apply (simp add: Pbij_Dom_def) apply fast
         apply (erule_tac x=l in allE, erule_tac x=ll in allE, erule impE, assumption)
         apply (erule_tac x=l in allE, erule_tac x=l in allE, erule impE, erule mkId4) 
         apply (subgoal_tac "\<exists> x y . lookup b l = Some (x,y)", clarsimp)
         prefer  2 apply (simp add: Dom_def)
         apply (simp add: twiddleObj_def, clarsimp)
         apply (subgoal_tac "\<exists> u . lookup y f = Some u", clarsimp)
         prefer 2 apply (rotate_tac -6, erule thin_rl, erule thin_rl, erule thin_rl)
                  apply (simp add: LowDom_def) apply fastforce
         apply (erule_tac x=f in allE, erule_tac x=f in allE, clarsimp)
       apply (erule twiddleVal.cases)
         apply clarsimp apply (erule twiddleVal.cases)
                          apply clarsimp apply (rule twiddleVal_Null)
                          apply clarsimp 
                          apply clarsimp 
         apply clarsimp apply (erule twiddleVal.cases)
                          apply clarsimp 
                          apply clarsimp apply (drule mkId4b, clarsimp) 
                                         apply (erule twiddleVal_Loc)
                          apply clarsimp 
         apply clarsimp apply (erule twiddleVal.cases)
                          apply clarsimp 
                          apply clarsimp 
                          apply clarsimp apply (rule twiddleVal_IVal) apply simp
 apply (simp add: HighSec_def)
     apply (simp add: twiddle_def, clarsimp) 
     apply (rule_tac x=\<beta> in exI)
     apply (rule, simp add: twiddleStore_def, clarsimp) 
       apply (erule_tac x=x in allE, clarsimp)
       apply (erule_tac x=x in allE, clarsimp)
       apply (erule twiddleVal.cases)
         apply clarsimp apply (erule twiddleVal.cases)
                          apply clarsimp apply (rule twiddleVal_Null)
                          apply clarsimp 
                          apply clarsimp 
         apply clarsimp apply (erule twiddleVal.cases)
                          apply clarsimp 
                          apply clarsimp apply (drule mkId4b, clarsimp) 
                                         apply (erule twiddleVal_Loc)
                          apply clarsimp 
         apply clarsimp apply (erule twiddleVal.cases)
                          apply clarsimp 
                          apply clarsimp 
                          apply clarsimp apply (rule twiddleVal_IVal) apply simp
     apply (rule, simp add: twiddleHeap_def, clarsimp)
       apply (rule, simp add:  mkId2 mkId2b)
       apply (simp add:  mkId2 mkId2b, clarsimp)
         apply (subgoal_tac "ll:Dom b")
         prefer 2 apply (simp add: Pbij_Rng_def) apply fast
         apply (erule_tac x=l in allE, erule_tac x=ll in allE, erule impE, assumption)
         apply (erule_tac x=ll in allE, erule_tac x=ll in allE, erule impE, erule mkId4) 
         apply (subgoal_tac "\<exists> x y . lookup b ll = Some (x,y)", clarsimp)
         prefer  2 apply (simp add: Dom_def)
         apply (simp add: twiddleObj_def, clarsimp)
         apply (subgoal_tac "\<exists> u . lookup y f = Some u", clarsimp)
         prefer 2 apply (rotate_tac -8, erule thin_rl, erule thin_rl, erule thin_rl)
                  apply (simp add: LowDom_def) apply fastforce
         apply (erule_tac x=f in allE, erule_tac x=f in allE, clarsimp)
       apply (erule twiddleVal.cases)
         apply clarsimp apply (erule twiddleVal.cases)
                          apply clarsimp apply (rule twiddleVal_Null)
                          apply clarsimp 
                          apply clarsimp 
         apply clarsimp apply (erule twiddleVal.cases)
                          apply clarsimp 
                          apply clarsimp apply (drule mkId4b, clarsimp) 
                                         apply (erule twiddleVal_Loc)
                          apply clarsimp 
         apply clarsimp apply (erule twiddleVal.cases)
                          apply clarsimp 
                          apply clarsimp 
                          apply clarsimp apply (rule twiddleVal_IVal) apply simp
  apply (rule Pbij_extends_reflexive)
done
(*>*)

lemma SkipHigh: "G \<rhd> Skip: HighSec"
(*<*)
apply (rule VDMConseq, rule VDMSkip)
apply (simp add: HighSec_def) apply clarsimp
(*apply (rule_tac x="mkId b" in exI)*)
apply (erule twiddle_mkId) 
done
(*>*)

text\<open>We define a predicate expressing when locations obtained by
evaluating an expression are non-dangling.\<close>

definition Expr_good::"Expr \<Rightarrow> State \<Rightarrow> bool"
where "Expr_good e s =
  (\<forall> l . evalE e (fst s) = RVal(Loc l) \<longrightarrow> l : Dom (snd s))"

lemma AssignHigh: 
  "\<lbrakk> CONTEXT x = high; \<forall> s . noLowDPs s \<longrightarrow> Expr_good e s\<rbrakk> 
  \<Longrightarrow> G \<rhd> Assign x e: HighSec"
(*<*)
apply (rule VDMConseq, rule VDMAssign, unfold HighSec_def)
apply (rule, rule, rule, rule)
apply (simp add: twiddle_def)
apply rule
  (*noLowDPs t*)
  apply (simp add: noLowDPs_def update_def) apply clarsimp 
apply rule
  (*twiddleStore*)
    apply (simp add: twiddleStore_def update_def)
    apply (rule, rule) 
      apply clarsimp 
    apply clarsimp
    apply (case_tac "a xa")
    apply (rename_tac Ref)
    apply clarsimp apply (case_tac Ref) 
      apply clarsimp apply (rule twiddleVal_Null) 
      apply clarsimp apply (rule twiddleVal_Loc) apply (rule mkId4) apply (simp add: noLowDPs_def)
      apply clarsimp apply (simp add: twiddleVal_IVal)
(*twiddleHeap*)
  apply (simp add: twiddleHeap_def update_def) apply clarsimp
  apply (rule, rule mkId1)
  apply (rule, simp add: mkId2)
  apply (rule, simp add: mkId2b) 
  apply clarsimp apply (drule mkId4b) apply clarsimp
  (*l=ll*)
      apply (simp add: twiddleObj_def) 
        apply clarsimp 
        apply (case_tac v, clarsimp)
        apply (rename_tac Ref)
        apply (case_tac Ref, clarsimp)
        apply (rule twiddleVal_Null)
        apply clarsimp apply (rule twiddleVal_Loc) apply (rule mkId4) apply (simp add: noLowDPs_def)
        apply clarsimp apply (rule twiddleVal_IVal) apply simp
done
(*>*)

lemma NewHigh:
  "CONTEXT x = high \<Longrightarrow> G \<rhd> New x C : HighSec"
(*<*)
apply (rule VDMConseq, rule VDMNew, unfold HighSec_def)
apply (rule, rule, rule)
apply (erule exE, (erule conjE)+)
apply (rule, simp add: twiddle_def, rule)
(*noLowDPs t*)
  apply (simp add: noLowDPs_def, clarsimp) apply (rename_tac l s h) apply rule 
  (*store content*)
    apply clarsimp apply (simp add: update_def)
    apply (case_tac "x=xa", clarsimp) apply (simp add: Dom_def)
    (*apply clarsimp apply (erule_tac x=xa in allE, erule_tac x=la in allE, clarsimp)
      apply (simp add: Dom_def)*)
  (*Field content*)
    apply clarsimp apply (simp add: Dom_def)
(*apply (rule_tac x="mkId (snd s)" in exI)*)
apply rule
(*twiddleStore*)
    apply (simp add: twiddleStore_def)
    apply (rule, rule) apply (simp add: update_def) apply clarsimp
    apply (rename_tac s h l xa)
    apply (case_tac "x=xa", clarsimp) apply clarsimp
    apply (case_tac "s xa")
    apply (rename_tac Ref)
    apply clarsimp apply (case_tac Ref) 
      apply clarsimp apply (rule twiddleVal_Null) 
      apply clarsimp apply (rule twiddleVal_Loc) apply (rule mkId4) apply (simp add: noLowDPs_def)
      apply clarsimp apply (simp add: twiddleVal_IVal)
(*twiddleHeap*)
  apply (simp add: twiddleHeap_def) apply clarsimp
  apply (rename_tac s h l)
  apply (rule, rule mkId1)
  apply (rule, simp add: mkId2) 
  apply (rule, simp add: mkId2b Dom_def) apply fastforce
  apply clarsimp 
  apply rule
    apply clarsimp apply (drule mkId4b) apply clarsimp
    apply clarsimp apply (drule mkId4b) apply clarsimp
      apply (rename_tac C F)
      apply (simp add: twiddleObj_def) apply clarsimp
        apply (case_tac v, clarsimp)
        apply (rename_tac Ref)
        apply (case_tac Ref, clarsimp)
        apply (rule twiddleVal_Null)
        apply clarsimp apply (rule twiddleVal_Loc) apply (rule mkId4) apply (simp add: noLowDPs_def)
        apply clarsimp apply (rule twiddleVal_IVal) apply simp
done
(*>*)

lemma GetHigh: 
"\<lbrakk> CONTEXT x = high \<rbrakk> \<Longrightarrow> G \<rhd> Get x y f : HighSec"
(*<*)
apply (rule VDMConseq, rule VDMGet, unfold HighSec_def)
apply (rule, rule, rule)
apply (erule exE)+
apply (erule conjE)+
apply (rule, simp add: twiddle_def, rule)
(*noLowDPs t*)
  apply (simp add: noLowDPs_def, clarsimp)
  (*store content*)
    apply (rename_tac s h xa la)
    apply (simp add: update_def)
    apply (case_tac "x=xa", clarsimp) apply (simp add: Dom_def)
  (*Field content already discharged*)
(*apply (rule_tac x="mkId (snd s)" in exI)*)
apply rule
(*twiddleStore*)
    apply (simp add: twiddleStore_def)
    apply (rule, rule) apply (simp add: update_def) apply clarsimp
    apply (rename_tac s h l C Flds v xa)
    apply (case_tac "x=xa", clarsimp) apply clarsimp
    apply (case_tac "s xa")
    apply (rename_tac Ref)
    apply clarsimp apply (case_tac Ref) 
      apply clarsimp apply (rule twiddleVal_Null) 
      apply clarsimp apply (rule twiddleVal_Loc) apply (rule mkId4) apply (simp add: noLowDPs_def)
      apply clarsimp apply (simp add: twiddleVal_IVal)
(*twiddleHeap*)
  apply (simp add: twiddleHeap_def) apply clarsimp
  apply (rename_tac s h l C Flds v)
  apply (rule, rule mkId1)
  apply (rule, simp add: mkId2)
  apply (rule, simp add: mkId2b)
  apply clarsimp apply (drule mkId4b) apply clarsimp
    apply (rename_tac D F)
      apply (simp add: twiddleObj_def) apply clarsimp
        apply (case_tac va, clarsimp)
        apply (rename_tac Ref)
        apply (case_tac Ref, clarsimp)
        apply (rule twiddleVal_Null)
        apply clarsimp apply (rule twiddleVal_Loc) apply (rule mkId4) apply (simp add: noLowDPs_def)
        apply clarsimp apply (rule twiddleVal_IVal) apply simp
done
(*>*)

lemma PutHigh: 
"\<lbrakk> GAMMA f = high; \<forall> s . noLowDPs s \<longrightarrow> Expr_good e s\<rbrakk>
  \<Longrightarrow> G \<rhd> Put x f e: HighSec"
(*<*)
apply (rule VDMConseq, rule VDMPut, unfold HighSec_def)
apply (rule, rule, rule)
apply (erule exE)+
apply (erule conjE)+
apply (rule, simp add: twiddle_def, rule)
(*noLowDPs t*)
  apply (simp add: noLowDPs_def, clarsimp)
  apply (rename_tac s h)
  apply rule
  (*store content*)
    apply clarsimp apply (erule_tac x=xa in allE, erule_tac x=la in allE, clarsimp) 
      apply (simp add: Dom_def)
  (*Field content*)
    apply clarsimp apply rule
    (*l=ll*)
      apply clarsimp apply rule
      (*f=fa*)
        apply clarsimp 
      (*f\<noteq>fa*)
        apply clarsimp apply (simp add: Dom_def)
    (*l\<noteq>ll*)
     apply clarsimp apply (simp add: Dom_def)
apply rule
(*twiddleStore*)
    apply (simp add: twiddleStore_def)
    apply (rule, rule) 
    apply (case_tac "fst s xa")
    apply (rename_tac Ref)
    apply clarsimp apply (case_tac Ref) 
      apply clarsimp apply (rule twiddleVal_Null) 
      apply clarsimp apply (rule twiddleVal_Loc) apply (rule mkId4) apply (simp add: noLowDPs_def)
      apply clarsimp apply (simp add: twiddleVal_IVal)
(*twiddleHeap*)
  apply (simp add: twiddleHeap_def) apply clarsimp
  apply (rule, simp add: mkId1)
  apply (rule, simp add: mkId2)
  apply (rule, simp add: mkId2b Dom_def) apply fast
  apply clarsimp apply rule
  (*l=ll*)
    apply clarsimp apply (drule mkId4b) apply clarsimp 
      apply (simp add: twiddleObj_def) 
        apply (rule, simp add: LowDom_def) apply (rotate_tac -1, erule thin_rl) apply fastforce
        apply clarsimp apply rule
        (*f=fa*)
        apply clarsimp
        (*f\<noteq>fa*)
        apply clarsimp 
        apply (case_tac v, clarsimp)
        apply (rename_tac Ref)
        apply (case_tac Ref, clarsimp)
        apply (rule twiddleVal_Null)
        apply clarsimp apply (rule twiddleVal_Loc) apply (rule mkId4) apply (simp add: noLowDPs_def)
        apply clarsimp apply (rule twiddleVal_IVal) apply simp
   (*l\<noteq>ll*)
     apply clarsimp apply (drule mkId4b) apply clarsimp 
      apply (simp add: twiddleObj_def) 
        apply clarsimp
        apply (case_tac v, clarsimp)
        apply (rename_tac Ref)
        apply (case_tac Ref, clarsimp)
        apply (rule twiddleVal_Null)
        apply clarsimp apply (rule twiddleVal_Loc) apply (rule mkId4) apply (simp add: noLowDPs_def)
        apply clarsimp apply (rule twiddleVal_IVal) apply simp
done
(*>*)

(*<*)
lemma PutHigh2: 
  "\<lbrakk> GAMMA f = high; \<forall> s . Expr_good e s\<rbrakk> \<Longrightarrow> G \<rhd> Put x f e: HighSec"
apply (rule VDMConseq, erule PutHigh) apply simp apply simp
done
(*>*)

(*<*)
lemma twiddle_mkIDs_compose:
  "\<lbrakk>(a,b) \<equiv>\<^sub>(mkId b) (ab, bb); (ab,bb) \<equiv>\<^sub>(mkId bb) (aa, ba)\<rbrakk>
  \<Longrightarrow> (a,b) \<equiv>\<^sub>(mkId b) (aa, ba)"
apply (simp add: twiddle_def)
  apply (rule, simp add: twiddleStore_def, clarsimp)
    apply (erule_tac x=x in allE, clarsimp)
    apply (erule_tac x=x in allE, clarsimp)
    apply (erule twiddleVal.cases)
      apply clarsimp 
      apply clarsimp apply (erule twiddleVal.cases)
                       apply clarsimp apply clarsimp prefer 2 apply clarsimp 
                       apply (drule mkId4b, clarsimp) apply (drule mkId4b, clarsimp) 
                       apply (rule twiddleVal_Loc) apply (erule mkId4)
      apply clarsimp 
  apply (simp add: twiddleHeap_def, clarsimp)
    apply (simp add: mkId2 mkId2b)
    apply rule apply fast
    apply clarsimp apply (drule mkId4b, clarsimp)
      apply (erule_tac x=ll in allE, erule_tac x=ll in allE, erule impE, erule mkId4) apply clarsimp
      apply (subgoal_tac "ll:Dom bb") prefer 2 apply fast
      apply (erule_tac x=ll in allE, erule_tac x=ll in allE, erule impE, erule mkId4) apply clarsimp
      apply (subgoal_tac "\<exists> x y . lookup bb ll = Some(x,y)", clarsimp)
      prefer 2 apply (simp add: Dom_def)
      apply (simp add: twiddleObj_def, clarsimp)
      apply (subgoal_tac "\<exists> u . lookup bc f = Some u", clarsimp)
      prefer 2 apply (simp add: LowDom_def) 
      apply (subgoal_tac "\<exists> u . lookup y f = Some u", clarsimp)
      prefer 2 apply (rotate_tac -7, erule thin_rl, erule thin_rl) apply (simp add: LowDom_def) apply fast
      apply (erule_tac x=f in allE, clarsimp)
      apply (erule_tac x=f in allE, clarsimp)
    apply (erule twiddleVal.cases)
      apply clarsimp apply (erule twiddleVal.cases)
                       apply clarsimp apply (rule twiddleVal_Null) apply clarsimp apply clarsimp
      apply clarsimp apply (erule twiddleVal.cases)
                       apply clarsimp apply clarsimp prefer 2 apply clarsimp 
                       apply (drule mkId4b, clarsimp) apply (drule mkId4b, clarsimp) 
                       apply (rule twiddleVal_Loc) apply (erule mkId4)
      apply clarsimp apply (erule twiddleVal.cases)
                       apply clarsimp apply clarsimp apply clarsimp apply (rule twiddleVal_IVal) apply clarsimp       
done
(*>*)
(*<*)
lemma twiddle_mkIDs_compose':
  "\<lbrakk> s \<equiv>\<^sub>(mkId (snd s)) r; r \<equiv>\<^sub>(mkId (snd r)) t\<rbrakk> \<Longrightarrow> s \<equiv>\<^sub>(mkId (snd s)) t"
apply (case_tac s, clarsimp)
apply (case_tac t, clarsimp)
apply (case_tac r, clarsimp)
apply (erule twiddle_mkIDs_compose, assumption)
done
(*>*)

lemma CompHigh:
 "\<lbrakk> G \<rhd> c: HighSec; G \<rhd> d:HighSec\<rbrakk> \<Longrightarrow> G \<rhd> Comp c d: HighSec"
(*<*)
apply (rule VDMConseq, erule VDMComp, assumption)
apply (unfold HighSec_def)
apply (rule, rule, rule)
apply (erule thin_rl, erule thin_rl, erule exE)
apply (erule conjE) apply clarsimp
apply (erule impE) prefer 2 apply (erule twiddle_mkIDs_compose, assumption) 
apply (simp add: noLowDPs_def twiddle_def)
done
(*>*)

lemma IfHigh: 
 "\<lbrakk> G \<rhd> c: HighSec; G \<rhd> d:HighSec\<rbrakk> \<Longrightarrow> G \<rhd> Iff b c d: HighSec"
(*<*)
apply (rule VDMConseq, rule VDMIff)
apply (assumption, assumption)
apply (erule thin_rl, erule thin_rl)
apply clarsimp
done(*>*)

lemma WhileHigh: "\<lbrakk> G \<rhd> c: HighSec\<rbrakk> \<Longrightarrow> G \<rhd> While b c: HighSec"
(*<*)
apply (rule VDMConseq, erule VDMWhile [of G c HighSec b HighSec])
apply (simp add: HighSec_def) apply clarsimp
(*apply (rule_tac x="mkId ba" in exI)*)
apply (erule twiddle_mkId) 

apply clarsimp
apply (simp add: HighSec_def) apply clarsimp
(*apply (rule_tac x="Pbij_compose \<beta> \<beta>'" in exI)*)
apply (erule impE) prefer 2 apply (erule twiddle_mkIDs_compose, assumption) 
(*apply (erule twiddle_compose, assumption)*)
apply (simp add: noLowDPs_def twiddle_def)

apply clarsimp
done(*>*)

lemma CallHigh:
  "({HighSec} \<union> G)  \<rhd> body : HighSec \<Longrightarrow> G \<rhd> Call : HighSec"
(*<*)
by (erule VDMCall)
(*>*)

text\<open>We combine all rules to an inductive derivation system.\<close>

inductive_set Deriv::"(Assn set \<times> OBJ \<times> Assn) set"
where
D_CAST: 
  "(G, c, HighSec):Deriv \<Longrightarrow>
  (G, c, Sec (\<lambda> (s, t, \<beta>). s \<equiv>\<^sub>\<beta> t)):Deriv"

| D_SKIP: "(G, Skip, Sec (\<lambda> (s, t, \<beta>) . s \<equiv>\<^sub>\<beta> t)) : Deriv"

| D_ASSIGN: 
  "Expr_low e \<Longrightarrow>
  (G, Assign x e, Sec (\<lambda> (s, t, \<beta>) . 
                 \<exists> r . s = (update (fst r) x (evalE e (fst r)), snd r)
                       \<and> r \<equiv>\<^sub>\<beta> t)):Deriv"

| D_COMP: 
  "\<lbrakk> (G, c1, Sec \<Phi>):Deriv; (G, c2, Sec \<Psi>):Deriv\<rbrakk> \<Longrightarrow>
  (G, Comp c1 c2, Sec (\<lambda> (s, t, \<beta>) . 
               \<exists> r . \<Phi>(r, t, \<beta>) \<and> 
                     (\<forall> w \<gamma>. r \<equiv>\<^sub>\<gamma> w \<longrightarrow> \<Psi>(s, w, \<gamma>)))):Deriv"

| D_IFF:
 "\<lbrakk> BExpr_low b; (G, c1, Sec \<Phi>):Deriv; (G, c2, Sec \<Psi>):Deriv\<rbrakk> \<Longrightarrow>
 (G, Iff b c1 c2, Sec (\<lambda> (s,t,\<beta>) .
                       (evalB b (fst t) \<longrightarrow> \<Phi>(s,t,\<beta>)) \<and> 
                       ((\<not> evalB b (fst t)) \<longrightarrow> \<Psi>(s,t,\<beta>)))):Deriv"

| D_NEW:
  "CONTEXT x = low \<Longrightarrow>
  (G, New x C, Sec (\<lambda> (s,t,\<beta>) . 
               \<exists> l r . l \<notin> Dom (snd r) \<and> r \<equiv>\<^sub>\<beta> t \<and> 
                       s = (update (fst r) x (RVal (Loc l)), 
                               (l,(C,[])) # (snd r)))):Deriv"

| D_GET:
  "\<lbrakk> CONTEXT y = low; GAMMA f = low\<rbrakk> \<Longrightarrow>
  (G, Get x y f, Sec (\<lambda> (s,t,\<beta>) .
               \<exists> r l C Flds v. (fst r) y = RVal(Loc l) \<and> 
                             lookup (snd r) l = Some(C,Flds) \<and> 
                             lookup Flds f = Some v \<and> r \<equiv>\<^sub>\<beta> t \<and> 
                             s = (update (fst r) x v, snd r))):Deriv"

| D_PUT: 
  "\<lbrakk> CONTEXT x = low; GAMMA f = low; Expr_low e\<rbrakk> \<Longrightarrow>
  (G, Put x f e, Sec (\<lambda> (s,t,\<beta>) .
         \<exists> r l C F h. (fst r) x = RVal(Loc l) \<and> r \<equiv>\<^sub>\<beta> t \<and>
                       lookup (snd r) l = Some(C,F) \<and> 
                       h = (l,(C,(f,evalE e (fst r)) # F)) # (snd r) \<and>
                       s = (fst r, h))):Deriv"

| D_WHILE:  
 "\<lbrakk> BExpr_low b; (G, c, Sec \<Phi>):Deriv\<rbrakk> 
  \<Longrightarrow> (G, While b c, Sec (PhiWhile b \<Phi>)):Deriv"

| D_CALL:
 "\<lbrakk>({Sec (FIX \<phi>)} \<union> G, body, Sec (\<phi> (FIX \<phi>))):Deriv; Monotone \<phi>\<rbrakk>
  \<Longrightarrow> (G, Call, Sec (FIX \<phi>)):Deriv"

| D_SKIP_H: "(G, Skip, HighSec):Deriv"

| D_ASSIGN_H:
 "\<lbrakk> CONTEXT x = high; \<forall> s . noLowDPs s \<longrightarrow> Expr_good e s\<rbrakk>
  \<Longrightarrow> (G, Assign x e, HighSec):Deriv"

| D_NEW_H: "CONTEXT x = high \<Longrightarrow> (G, New x C, HighSec):Deriv"

| D_GET_H: "CONTEXT x = high \<Longrightarrow> (G, Get x y f, HighSec):Deriv"

| D_PUT_H: 
 "\<lbrakk> GAMMA f = high; \<forall> s . noLowDPs s \<longrightarrow> Expr_good e s\<rbrakk>
  \<Longrightarrow> (G, Put x f e, HighSec):Deriv"  

| D_COMP_H:
 "\<lbrakk> (G, c, HighSec):Deriv; (G, d, HighSec):Deriv\<rbrakk> 
 \<Longrightarrow> (G, Comp c d, HighSec):Deriv"

| D_IFF_H:
 "\<lbrakk> (G, c, HighSec):Deriv; (G, d, HighSec):Deriv\<rbrakk>
  \<Longrightarrow> (G, Iff b c d, HighSec):Deriv"

| D_WHILE_H:
 "\<lbrakk> (G, c, HighSec):Deriv\<rbrakk> \<Longrightarrow> (G, While b c, HighSec):Deriv"

| D_CALL_H:
 "({HighSec} \<union> G, body, HighSec):Deriv \<Longrightarrow> (G, Call, HighSec):Deriv"

text\<open>By construction, all derivations represent legal derivations in
the program logic. Here's an explicit lemma to this effect.\<close>

lemma Deriv_derivable: "(G,c,A):Deriv \<Longrightarrow> G \<rhd> c: A"
(*<*)
apply (erule Deriv.induct)
apply (erule CAST)
apply (rule SKIP)
apply (erule ASSIGN)
apply (erule COMP) apply assumption
apply (erule IFF) apply assumption apply assumption
apply (erule NEW)
apply (erule GET) apply assumption 
apply (drule_tac G=G in PUT) apply assumption apply assumption apply simp
apply (erule WHILE) apply assumption 
apply (erule CALL) apply assumption
apply (rule SkipHigh)
apply (erule AssignHigh) apply assumption
apply (erule NewHigh)
apply (erule GetHigh)
apply (erule PutHigh) apply assumption
apply (erule CompHigh) apply assumption
apply (erule IfHigh) apply assumption
apply (erule WhileHigh) 
apply (erule CallHigh)
done
(*>*)

subsection\<open>Type system\<close>
text\<open>\label{sec:ObjTypeSystem}\<close>

text\<open>We now give a type system in the style of Volpano et al.~and
then prove its embedding into the system of derived rules. First, type
systems for expressions and boolean expressions. These are similar to
the ones in Section \ref{sec:BaseLineNI} but require some side
conditions regarding the (semantically modelled) operators.\<close>

definition opEGood::"(Val \<Rightarrow> Val \<Rightarrow> Val) \<Rightarrow> bool"
where "opEGood f = (\<forall> \<beta> v v' w w' . (\<beta>, v, v') \<in> twiddleVal\<longrightarrow>
        (\<beta>, w, w') \<in> twiddleVal \<longrightarrow> (\<beta>, f v w, f v' w') \<in> twiddleVal)"

definition compBGood::"(Val \<Rightarrow> Val \<Rightarrow> bool) \<Rightarrow> bool"
where "compBGood f = (\<forall> \<beta> v v' w w' . (\<beta>, v, v') \<in> twiddleVal\<longrightarrow>
        (\<beta>, w, w') \<in> twiddleVal \<longrightarrow> f v w = f v' w')"

inductive_set VS_expr:: "(Expr \<times> TP) set"
where
VS_exprVar: "CONTEXT x = t \<Longrightarrow> (varE x, t) : VS_expr"
|
VS_exprVal:
  "\<lbrakk>v=RVal Nullref \<or> (\<exists> i . v=IVal i)\<rbrakk> \<Longrightarrow> (valE v, low) : VS_expr"
|
VS_exprOp:
  "\<lbrakk>(e1,t) : VS_expr; (e2,t):VS_expr; opEGood f\<rbrakk>
   \<Longrightarrow> (opE f e1 e2,t) : VS_expr"
|
VS_exprHigh: "(e, high) : VS_expr"

inductive_set VS_Bexpr:: "(BExpr \<times> TP) set"
where
VS_BexprOp: 
  "\<lbrakk>(e1,t):VS_expr; (e2,t):VS_expr; compBGood f\<rbrakk> 
   \<Longrightarrow> (compB f e1 e2,t):VS_Bexpr"
|
VS_BexprHigh: "(e,high) : VS_Bexpr"

text\<open>Next, the core of the type system, the rules for commands. The
second side conditions of rules \<open>VS_comAssH\<close> and \<open>VS_comPutH\<close> could be strengthened to $\forall\; s .\;
\mathit{Epxr\_good}\; e\; s$.\<close>

inductive_set VS_com:: "(TP \<times> OBJ) set"
where
VS_comGetL: 
  "\<lbrakk> CONTEXT y = low; GAMMA f = low\<rbrakk> 
  \<Longrightarrow> (low, Get x y f):VS_com"

| VS_comGetH: "CONTEXT x = high \<Longrightarrow> (high, Get x y f):VS_com"

| VS_comPutL:
  "\<lbrakk> CONTEXT x = low; GAMMA f = low; (e, low) : VS_expr\<rbrakk>
  \<Longrightarrow> (low,Put x f e):VS_com"

| VS_comPutH:
  "\<lbrakk> GAMMA f = high; \<forall> s . noLowDPs s \<longrightarrow> Expr_good e s\<rbrakk>
  \<Longrightarrow> (high,Put x f e):VS_com"

| VS_comNewL:
  "CONTEXT x = low \<Longrightarrow> (low, New x c) : VS_com"

| VS_comNewH:
  "CONTEXT x = high \<Longrightarrow> (high, New x C):VS_com"

| VS_comAssL:
  "\<lbrakk>CONTEXT x = low; (e,low):VS_expr\<rbrakk>
  \<Longrightarrow> (low,Assign x e) : VS_com"

| VS_comAssH:
  "\<lbrakk>CONTEXT x = high; \<forall> s . noLowDPs s \<longrightarrow> Expr_good e s\<rbrakk> 
  \<Longrightarrow> (high,Assign x e) : VS_com"

| VS_comSkip: "(pc,Skip) : VS_com"

| VS_comComp:
  "\<lbrakk> (pc,c):VS_com; (pc,d):VS_com\<rbrakk>  \<Longrightarrow> (pc,Comp c d) : VS_com"

| VS_comIf: 
  "\<lbrakk> (b,pc):VS_Bexpr; (pc,c):VS_com; (pc,d):VS_com\<rbrakk>
  \<Longrightarrow> (pc,Iff b c d):VS_com"

| VS_comWhile:
  "\<lbrakk>(b,pc):VS_Bexpr; (pc,c):VS_com\<rbrakk> \<Longrightarrow> (pc,While b c):VS_com"

| VS_comSub: "(high,c) : VS_com \<Longrightarrow> (low,c):VS_com"

text\<open>In order to prove the type system sound, we first define the
interpretation of expression typings\ldots\<close>

primrec SemExpr::"Expr \<Rightarrow> TP \<Rightarrow> bool"
where
"SemExpr e low = Expr_low e" |
"SemExpr e high = True"

text\<open>\ldots and show the soundness of the typing rules.\<close>

lemma ExprSound: "(e,tp):VS_expr \<Longrightarrow> SemExpr e tp"
(*<*)
apply (erule VS_expr.induct)
apply clarsimp
  apply (case_tac "CONTEXT x", clarsimp) apply (simp add: Expr_low_def twiddleStore_def)
  apply clarsimp
apply (simp add: Expr_low_def)
  apply (erule disjE) apply clarsimp apply (rule twiddleVal_Null)
    apply clarsimp apply (rule twiddleVal_IVal) apply simp
apply (case_tac t, clarsimp)
  apply (simp add: Expr_low_def, clarsimp)
    apply (erule_tac x=s in allE, erule_tac x=t in allE, erule_tac x=\<beta> in allE, erule impE, assumption)
    apply (erule_tac x=s in allE, erule_tac x=t in allE, erule_tac x=\<beta> in allE, erule impE, assumption)
    apply (simp add: opEGood_def)
  apply simp
apply clarsimp
done
(*>*)

text\<open>Likewise for the boolean expressions.\<close>

primrec SemBExpr::"BExpr \<Rightarrow> TP \<Rightarrow> bool"
where
"SemBExpr b low = BExpr_low b" |
"SemBExpr b high = True"

lemma BExprSound: "(e,tp):VS_Bexpr \<Longrightarrow> SemBExpr e tp"
(*<*)
apply (erule VS_Bexpr.induct, simp_all)
apply (drule ExprSound) 
apply (drule ExprSound) 
apply (case_tac t, simp_all add: BExpr_low_def Expr_low_def) apply clarsimp
  apply (erule_tac x=s in allE, erule_tac x=ta in allE, erule_tac x=\<beta> in allE, erule impE, assumption)
  apply (erule_tac x=s in allE, erule_tac x=ta in allE, erule_tac x=\<beta> in allE, erule impE, assumption)
  apply (simp add: compBGood_def)
done
(*>*)

text\<open>Using these auxiliary lemmas we can prove the embedding of the
type system for commands into the system of derived proof rules, by
induction on the typing rules.\<close>

theorem VS_com_Deriv[rule_format]:
"(t,c):VS_com \<Longrightarrow> (t=high \<longrightarrow> (G, c, HighSec):Deriv) \<and>
                  (t=low \<longrightarrow> (\<exists> \<Phi> . (G, c, Sec \<Phi>):Deriv))"
(*<*)
apply (erule VS_com.induct)
apply clarsimp
  apply (rule, erule D_GET) apply assumption
apply clarsimp apply (erule D_GET_H) 
apply clarsimp
  apply (rule, erule D_PUT) apply assumption apply (drule ExprSound) apply simp
apply clarsimp apply (erule D_PUT_H) apply simp 
apply clarsimp apply (rule, erule D_NEW) 
apply clarsimp apply (erule D_NEW_H) 
apply clarsimp apply (rule, rule D_ASSIGN) apply (drule ExprSound) apply simp 
apply clarsimp apply (erule D_ASSIGN_H) apply simp
apply rule
  apply clarsimp apply (rule D_SKIP_H)
  apply clarsimp apply (rule, rule D_SKIP) 
apply (erule conjE)+ apply rule 
  apply rule apply (erule impE, assumption) apply (erule impE, assumption) 
             apply (erule D_COMP_H) apply assumption
  apply rule apply (erule impE, assumption, erule exE) apply (erule impE, assumption, erule exE) 
             apply (rule, erule D_COMP) apply assumption
apply (erule conjE)+ apply rule 
  apply rule apply (erule impE, assumption) apply (erule impE, assumption) 
             apply (erule D_IFF_H) apply assumption
  apply rule apply (erule impE, assumption, erule exE) apply (erule impE, assumption, erule exE) 
             apply (rule, rule D_IFF) prefer 2 apply assumption prefer 2 apply assumption
             apply (drule BExprSound) apply simp
apply (erule conjE)+ apply rule 
  apply (rule, erule impE, assumption) 
             apply (erule D_WHILE_H) 
  apply (rule, erule impE, assumption, erule exE) 
             apply (rule, rule D_WHILE) prefer 2 apply assumption 
             apply (drule BExprSound) apply simp
apply simp apply (rule, erule D_CAST)
done
(*>*)

text\<open>Combining this result with the derivability of the derived proof
system and the soundness theorem of the program logic yields non-interference
of programs that are low typeable.\<close>

theorem VS_SOUND: "(low,c):VS_com \<Longrightarrow> secure c"
(*<*)
apply (drule_tac G="{}" in VS_com_Deriv, simp)
apply (erule exE)
apply (drule  Deriv_derivable)
apply (drule VDM_Sound_emptyCtxt)
apply (erule Prop1A)
done
(*>*)

text\<open>End of theory \<open>VS_OBJ\<close>\<close>
end
