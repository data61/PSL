(* Author: Max Haslbeck *)

theory Nielson_VCG imports Nielson_Hoare begin

subsection "Verification Condition Generator"

text\<open>Annotated commands: commands where loops are annotated with
  invariants.\<close>

datatype acom =
  Askip                  ("SKIP") |
  Aassign vname aexp     ("(_ ::= _)" [1000, 61] 61) |
  Aseq   acom acom       ("_;;/ _"  [60, 61] 60) |
  Aif bexp acom acom     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61) |
  Aconseq assn2 assn2 tbd  acom
  ("({_'/_'/_}/ CONSEQ _)"  [0, 0, 0, 61] 61)|
  Awhile "(assn2)*((state\<Rightarrow>state)*(tbd))" bexp acom  ("({_}/ WHILE _/ DO _)"  [0, 0, 61] 61)
  
notation com.SKIP ("SKIP")

text\<open>Strip annotations:\<close>

fun strip :: "acom \<Rightarrow> com" where
  "strip SKIP = SKIP" |
  "strip (x ::= a) = (x ::= a)" |
  "strip (C\<^sub>1;; C\<^sub>2) = (strip C\<^sub>1;; strip C\<^sub>2)" |
  "strip (IF b THEN C\<^sub>1 ELSE C\<^sub>2) = (IF b THEN strip C\<^sub>1 ELSE strip C\<^sub>2)" |
  "strip ({_/_/_} CONSEQ C) = strip C" |
  "strip ({_} WHILE b DO C) = (WHILE b DO strip C)"
  
  
  
text "support of an expression"

subsubsection "support and supportE"
  
  
  
definition supportE :: "((char list \<Rightarrow> nat) \<Rightarrow> (char list \<Rightarrow> int) \<Rightarrow> nat)  \<Rightarrow> string set" where
  "supportE P = {x. \<exists>l1 l2 s. (\<forall>y. y \<noteq> x \<longrightarrow> l1 y = l2 y) \<and> P l1 s \<noteq> P l2 s}"
  
  
lemma expr_lupd: "x \<notin> supportE Q \<Longrightarrow> Q (l(x:=n)) = Q l"
  by(simp add: supportE_def fun_upd_other fun_eq_iff)
    (metis (no_types, lifting) fun_upd_def)

lemma supportE_if: "supportE (\<lambda>l s. if b s then A l s else B l s)
  \<subseteq> supportE A \<union> supportE B"
  unfolding supportE_def apply(auto)
  by metis+


lemma support_eq: "support (\<lambda>l s. l x = E l s) \<subseteq> supportE E \<union> {x}"
  unfolding support_def supportE_def 
  apply(auto)
   apply blast
  by metis


lemma support_impl_in: "G e \<longrightarrow> support (\<lambda>l s.  H e l s) \<subseteq> T
  \<Longrightarrow> support (\<lambda>l s. G e \<longrightarrow>  H e l s) \<subseteq> T"
  unfolding support_def apply(auto)
   apply blast+ done

lemma support_supportE: "\<And>P e. support (\<lambda>l s.  P (e l) s) \<subseteq> supportE e"
  unfolding support_def supportE_def
  apply(rule subsetI)
  apply(simp)
proof (clarify, goal_cases)
  case (1 P e x l1 l2 s)
  have P: "\<forall>s. e l1 s = e l2 s \<Longrightarrow> e l1 = e l2" by fast
  show "\<exists>l1 l2. (\<forall>y. y \<noteq> x \<longrightarrow> l1 y = l2 y) \<and> (\<exists>s. e l1 s \<noteq> e l2 s)"
    apply(rule exI[where x=l1])
    apply(rule exI[where x=l2])
    apply(safe)
    using 1 apply blast
    apply(rule ccontr)
    apply(simp) 
    using 1(2) P by force            
qed 
  
\<comment> \<open>collects the logical variables in the Invariants and Loop Bodies as well as the annotated
    assertions at CONSEQs of an annotated command\<close>
fun varacom :: "acom \<Rightarrow> lvname set" where
  "varacom (C\<^sub>1;; C\<^sub>2)= varacom C\<^sub>1 \<union> varacom C\<^sub>2"
| "varacom (IF b THEN C\<^sub>1 ELSE C\<^sub>2)= varacom C\<^sub>1 \<union> varacom C\<^sub>2"
| "varacom ({P/Qannot/_} CONSEQ C)= support P \<union> varacom C \<union> support Qannot"
| "varacom ({(I,(S,(E)))} WHILE b DO C) = support I \<union> varacom C"
| "varacom _ = {}"
    
text\<open>Weakest precondition from annotated commands:\<close>

fun preT :: "acom \<Rightarrow> tbd \<Rightarrow> tbd" where
  "preT SKIP e = e" |
  "preT (x ::= a) e = (\<lambda>s. e(s(x := aval a s)))" |
  "preT (C\<^sub>1;; C\<^sub>2) e = preT C\<^sub>1 (preT C\<^sub>2 e)" |
  "preT ({_/_/_} CONSEQ C) e = preT C e" |
  "preT (IF b THEN C\<^sub>1 ELSE C\<^sub>2) e =
  (\<lambda>s. if bval b s then preT C\<^sub>1 e s else preT C\<^sub>2 e s)" |
  "preT ({(_,(S,_))} WHILE b DO C) e = e o S"
  
  
lemma preT_linear: "preT C (%s. k * e s) = (%s. k * preT C e s)"
by (induct C arbitrary: e, auto)
  
fun postQ :: "acom \<Rightarrow> state \<Rightarrow> state" where (* seems to be forward?! *)
  "postQ SKIP s = s" |
  "postQ (x ::= a) s =  s(x := aval a s)" |
  "postQ (C\<^sub>1;; C\<^sub>2) s = postQ C\<^sub>2 (postQ C\<^sub>1 s)" |
  "postQ ({_/_/_} CONSEQ C) s = postQ C s" |
  "postQ (IF b THEN C\<^sub>1 ELSE C\<^sub>2) s =
  (if bval b s then postQ C\<^sub>1 s else postQ C\<^sub>2 s)" |
  "postQ ({(_,(S,_))} WHILE b DO C) s = S s"
    
lemma TQ: "preT C e s = e (postQ C s)"
  apply(induct C arbitrary: e s) by (auto) 
  
(* given a state, how often will a While loop be evaluated ? *)  
function (domintros) times :: "state \<Rightarrow> bexp \<Rightarrow> acom \<Rightarrow> nat" where
  "times s b C = (if bval b s then Suc (times (postQ C s) b C) else 0)" 
   apply(auto) done

  
    
    
lemma assumes I: "I z s" and
  i:   "\<And>s z. I (Suc z) s \<Longrightarrow> bval b s \<and> I z (postQ C s)"
  and  ii:  "\<And>s. I 0 s \<Longrightarrow> ~ bval b s"
shows times_z: "times s b C = z"
proof -  
  have "I z s \<Longrightarrow> times_dom (s, b, C) \<and> times s b C = z"
  proof(induct z arbitrary: s)
    case 0
    have A: "times_dom (s, b, C)"
      apply(rule times.domintros)
      apply(simp add:  ii[OF 0] ) done
    have B: "times s b C = 0"
      using times.psimps[OF A] by(simp add:  ii[OF 0])
    
    show ?case using A B by simp
  next
    case (Suc z)
    from i[OF Suc(2)] have bv: "bval b s"
      and g:  "I z (postQ C s)" by simp_all
    from Suc(1)[OF g] have p1: "times_dom (postQ C s, b, C)"
      and p2: "times (postQ C s) b C = z" by simp_all
    have A: "times_dom (s, b, C)" 
      apply(rule times.domintros) apply(rule p1) done
    have B: "times s b C = Suc z" 
      using times.psimps[OF A] bv p2 by simp
    show ?case using A B by simp
  qed
  
  then show "times s b C = z" using I by simp
qed
  
  
function (domintros) postQs :: "acom \<Rightarrow> bexp \<Rightarrow> state \<Rightarrow> state" where
  "postQs C b s = (if bval b s then (postQs C b (postQ C s))  else s)" 
  apply(auto) done
  
  
  
fun postQz :: "acom \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> state" where
  "postQz C s 0 = s" |
  "postQz C s (Suc n) =  (postQz C (postQ C s) n)"
  
fun preTz :: "acom \<Rightarrow> tbd \<Rightarrow> nat \<Rightarrow> tbd" where
  "preTz C e 0 = e" |
  "preTz C e (Suc n) = preT C (preTz C e n)"
  
  
  
  
lemma TzQ: "preTz C e n s = e (postQz C s n)"
  by (induct n arbitrary: s, simp_all add: TQ)



subsubsection \<open>Weakest precondition from annotated commands:\<close>

fun pre :: "acom \<Rightarrow> assn2 \<Rightarrow> assn2" where
  "pre SKIP Q  = Q" |
  "pre (x ::= a) Q = (\<lambda>l s. Q l (s(x := aval a s)))" |
  "pre (C\<^sub>1;; C\<^sub>2) Q  = pre C\<^sub>1 (pre C\<^sub>2 Q)" |
  "pre ({P'/_/_} CONSEQ C) Q = P'" |
  "pre (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q =
  (\<lambda>l s. if bval b s then pre C\<^sub>1 Q l s else pre C\<^sub>2 Q l s)" |
  "pre ({(I,(S,(E)))} WHILE b DO C) Q = I" 
  
lemma supportE_preT: "supportE (%l. preT C (e l)) \<subseteq> supportE e"
proof(induct C arbitrary: e)
  case (Aif b C1 C2 e)
  show ?case
    apply(simp)
    apply(rule subset_trans[OF supportE_if])
    using Aif by fast
next
  case (Awhile A y C e)
  obtain I S E  where A: "A= (I,S,E)" using prod_cases3 by blast
  show ?case using A apply(simp) unfolding supportE_def
    by blast
next
  case (Aseq)
  then show ?case by force
qed (simp_all add: supportE_def, blast)

lemma supportE_twicepreT: "supportE (%l. preT C1 (preT C2 (e l))) \<subseteq> supportE e"
  by (rule subset_trans[OF supportE_preT supportE_preT])



lemma supportE_preTz: "supportE (%l. preTz C (e l) n) \<subseteq> supportE e"
proof (induct n) 
  case (Suc n)
  show ?case  
    apply(simp)
    apply(rule subset_trans[OF supportE_preT]) 
    by fact 
qed simp


lemma supportE_preTz_Un: (* like in support_wpw_Un *)
  "supportE (\<lambda>l. preTz C (e l) (l x)) \<subseteq> insert x (UN n. supportE (\<lambda>l. preTz C (e l) n))"
  apply(auto simp add: supportE_def subset_iff)
  apply metis
  done


lemma supportE_preTz2: "supportE (%l. preTz C (e l) (l x)) \<subseteq> insert x (supportE e)" 
  apply(rule subset_trans[OF supportE_preTz_Un])
  using supportE_preTz by blast  
  


lemma pff: "\<And>n. support (\<lambda>l. I (l(x := n))) \<subseteq> support I - {x}"
  unfolding support_def apply(auto)  using fun_upd_apply apply smt
    apply (smt fun_upd_apply)  oops
  
lemma pff: "\<And>n. support (\<lambda>l. I (l(x := n))) \<subseteq> support I"
  unfolding support_def apply(auto)  using fun_upd_apply apply smt
  by (smt fun_upd_apply)  


lemma supportAB: "support (\<lambda>l s. A l s \<and> B s) \<subseteq> support A"    
  apply(rule subset_trans[OF support_and]) 
    by (simp add: support_inv) 
    
lemma "support (pre ({(I,(S,(E )))} WHILE b DO C) Q) \<subseteq> support I" 
 by (simp add: supportAB) 

lemma support_pre: "support (pre C Q) \<subseteq> support Q \<union> varacom C"
proof (induct C arbitrary: Q)
  case (Awhile A b C Q)
  obtain I S E  where A: "A= (I,(S,(E )))" using prod_cases3 by blast   
  have support_inv: "\<And>P. support (\<lambda>l s. P s) = {}"
    unfolding support_def by blast   
  show ?case unfolding A  apply(simp) using supportAB  by fast
next
  case (Aseq C1 C2)
  then show ?case by(auto)
next
  case (Aif x C1 C2 Q)
  have s1: "support (\<lambda>l s. bval x s \<longrightarrow> pre C1 Q l s) \<subseteq> support Q \<union> varacom C1"
    apply(rule subset_trans[OF support_impl]) by(rule Aif)
  have s2: "support (\<lambda>l s. ~ bval x s \<longrightarrow> pre C2 Q l s) \<subseteq> support Q \<union> varacom C2"
    apply(rule subset_trans[OF support_impl]) by(rule Aif)
  
  show ?case apply(simp)
    apply(rule subset_trans[OF support_and]) 
    using s1 s2 by blast    
next
  case (Aconseq x1 x2 x3 C)
  then show ?case by(auto)
qed (auto simp add: support_def) 

lemma finite_support_pre[simp]: "finite (support Q)  \<Longrightarrow> finite (varacom C) \<Longrightarrow>  finite (support (pre C Q))"
  using finite_subset support_pre finite_UnI by metis 


fun time :: "acom \<Rightarrow> tbd" where
  "time SKIP = (%s. Suc 0)" |
  "time (x ::= a) = (%s. Suc 0)" |
  "time (C\<^sub>1;; C\<^sub>2) = (%s. time C\<^sub>1 s + preT C\<^sub>1 (time C\<^sub>2) s)" |
  "time ({_/_/e} CONSEQ C) = e" |
  "time (IF b THEN C\<^sub>1 ELSE C\<^sub>2) =
  (\<lambda>s. if bval b s then 1 + time C\<^sub>1 s else 1 + time C\<^sub>2 s)" |
  "time ({(_,(E',(E )))} WHILE b DO C) = E"
   
    
lemma supportE_single: "supportE (\<lambda>l s. P) = {}" 
  unfolding supportE_def by blast


lemma supportE_plus: "supportE (\<lambda>l s. e1 l s + e2 l s) \<subseteq> supportE e1 \<union> supportE e2" 
  unfolding supportE_def apply(auto)
  by metis 

lemma supportE_Suc: "supportE (\<lambda>l s. Suc (e1 l s)) = supportE e1"
  unfolding supportE_def by (auto) 


lemma supportE_single2: "supportE (\<lambda>l . P) = {}" 
  unfolding supportE_def by blast

lemma supportE_time: "supportE (\<lambda>l. time C) = {}"
  using supportE_single2 by simp   

lemma "\<And>s. (\<forall>l. I (l(x:=0)) s) = (\<forall>l. l x = 0 \<longrightarrow> I l s)"
  apply(auto) 
  by (metis fun_upd_triv)

lemma "\<And>s. (\<forall>l. I (l(x:=Suc (l x))) s) = (\<forall>l. (\<exists>n. l x = Suc n) \<longrightarrow> I l s)"
  apply(auto) 
proof (goal_cases)
  case (1 s l n)
  then have "\<And>l. I (l(x := Suc (l x))) s" by simp
  from this[where l="l(x:=n)"]
  have "I ((l(x:=n))(x := Suc ((l(x:=n)) x))) s" by simp
  then show ?case using 1(2) apply(simp) 
    by (metis fun_upd_triv)
qed 

text\<open>Verification condition:\<close>
fun vc :: "acom \<Rightarrow> assn2  \<Rightarrow> bool" where
  "vc SKIP Q = True" |
  "vc (x ::= a) Q = True" |
  "vc (C\<^sub>1 ;; C\<^sub>2) Q = ((vc C\<^sub>1 (pre C\<^sub>2 Q)) \<and> (vc C\<^sub>2 Q) )" |
  "vc (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q = (vc C\<^sub>1 Q \<and> vc C\<^sub>2 Q)" |  
  "vc ({P'/Q/e'} CONSEQ C) Q' = (vc C Q \<and> (\<exists>k>0. (\<forall>l s. P' l s \<longrightarrow> time C s \<le> k * e' s  \<and> (\<forall>t. \<exists>l'. (pre C Q) l' s \<and> ( Q l' t \<longrightarrow> Q' l t) ))))" |
  
  "vc ({(I,(S,(E)))} WHILE b DO C) Q = 
  ((\<forall>l s. (I l s \<and> bval b s \<longrightarrow>  pre C I l s \<and>   E s \<ge> 1 + preT C E s + time C s
  \<and> S s = S (postQ C s)) \<and>
  (I l s \<and> \<not> bval b s \<longrightarrow> Q l s \<and> E s \<ge> 1 \<and> S s = s) ) \<and>
  vc C I)"
      
lemma pre_mono:
  "(\<forall>l s. P l s \<longrightarrow> P' l s) \<Longrightarrow> pre C P l s \<Longrightarrow> pre C P' l s" 
proof (induction C arbitrary: P P' l s)
  case (Aseq C1 C2) 
  then have A: "pre C1 (pre C2 P) l s" by(simp)
  from Aseq(2)[OF Aseq(3)] Aseq(1)[OF _ A]
  show ?case by simp
next
  case (Awhile A b C)
  then obtain I S E   where A: "A = (I,S,E )"  using prod_cases3 by blast
  from Awhile show ?case unfolding A by simp
qed simp_all

lemma vc_mono: "(\<forall>l s. P l s \<longrightarrow> P' l s) \<Longrightarrow> vc C P \<Longrightarrow> vc C P'"
  apply (induct C arbitrary: P P')
       apply auto 
  subgoal using pre_mono by metis 
  subgoal using pre_mono by metis
  done

subsubsection \<open>Soundness:\<close>
 
abbreviation "preSet U C l s == (Ball U (%u. case u of (x,e) \<Rightarrow> l x = preT C e s))"
abbreviation "postSet U l s == (Ball U (%u. case u of (x,e) \<Rightarrow> l x = e s))"

fun ListUpdate where
  "ListUpdate f [] l = f"
| "ListUpdate f ((x,e)#xs) q = (ListUpdate f xs q)(x:=q e x)"

lemma allg: 
  assumes U2: "\<And>l s n x. x\<in> fst ` upds \<Longrightarrow> A (l(x := n))  = A l"
  shows
    "fst ` set xs \<subseteq> fst ` upds \<Longrightarrow> A (ListUpdate l'' xs q) = A l''" 
proof (induct xs) 
  case (Cons a xs)
  obtain x e where axe: "a = (x,e)" by fastforce 
  have "A (ListUpdate l'' (a # xs) q) 
    = A ((ListUpdate l'' xs q)(x := q e x))  " unfolding axe by(simp)
  also have
    "\<dots> =  A  (ListUpdate l'' xs q)  "
    apply(rule U2)
    using Cons axe by force
  also have "\<dots> = A l'' "
    using Cons by force
  finally show ?case .
qed simp  

fun ListUpdateE where
  "ListUpdateE f []   = f"
| "ListUpdateE f ((x,v)#xs)  = (ListUpdateE f xs  )(x:=v)"

lemma ListUpdate_E: "ListUpdateE f xs = ListUpdate f xs (%e x. e)"
  apply(induct xs) apply(simp_all)
  subgoal for a xs apply(cases a) apply(simp) done
  done
lemma allg_E: fixes A::assn2
    assumes 
   " (\<And>l s n x. x \<in> fst ` upds \<Longrightarrow> A (l(x := n)) = A l)" "fst ` set xs \<subseteq> fst ` upds"
   shows "A (ListUpdateE f xs) = A f"
proof -
  have " A (ListUpdate f xs (%e x. e)) = A f"
    apply(rule allg) 
    apply fact+ done
  then show ?thesis by(simp only: ListUpdate_E)
qed 

lemma ListUpdateE_updates: "distinct (map fst xs) \<Longrightarrow> x \<in> set xs \<Longrightarrow> ListUpdateE l'' xs (fst x) = snd x"
proof (induct xs)
  case Nil
  then show ?case apply(simp) done
next
  case (Cons a xs)
  show ?case
  proof (cases "fst a = fst x")
    case True
    then obtain y e where a: "a=(y,e)" by fastforce
    with True have fstx: "fst x=y" by simp
    from Cons(2,3) fstx  a have a2: "x=a"
      by force
    show ?thesis unfolding a2 a by(simp)
  next
    case False
    with Cons(3) have A: "x\<in>set xs" by auto
    obtain y e where a: "a=(y,e)" by fastforce
    from Cons(2) have B: "distinct (map fst xs)" by simp 
    from Cons(1)[OF B A] False
      show ?thesis unfolding a by(simp)  
  qed 
qed
  
    
lemma ListUpdate_updates: "x \<in> fst ` (set xs) \<Longrightarrow> ListUpdate l'' xs (%e. l) x = l x"
proof(induct xs)
  case Nil
  then show ?case by(simp)
next
  case (Cons a xs)
  obtain q p where axe: "a = (p,q)" by fastforce 
  from Cons show ?case unfolding axe
    apply(cases "x=p")  
    by(simp_all)
qed
  
abbreviation "lesvars xs == fst ` (set xs)"
  
fun preList where
  "preList [] C l s = True"
| "preList ((x,e)#xs) C l s = (l x = preT C e s \<and> preList xs C l s)"
        
lemma preList_Seq: "preList upds (C1;; C2) l s = preList (map (\<lambda>(x, e). (x, preT C2 e)) upds) C1 l s"
proof (induct upds)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  obtain y e where a: "a=(y,e)" by fastforce
  from Cons show ?case unfolding a by (simp)
qed

lemma support_True[simp]: "support (\<lambda>a b. True) = {}" 
  unfolding support_def 
  by fast
  
lemma support_preList: "support (preList upds C1) \<subseteq> lesvars upds"
proof (induct upds)
  case Nil
  then show ?case by simp 
next
  case (Cons a upds)
  obtain y e where a: "a=(y,e)" by fastforce
  from Cons show ?case unfolding a apply (simp)
    apply(rule subset_trans[OF support_and])
    apply(rule Un_least)
    subgoal apply(rule subset_trans[OF support_eq])
      using supportE_twicepreT subset_trans  supportE_single2 by simp
    subgoal by auto
    done
qed
  
  
lemma preListpreSet: "preSet (set xs) C l s \<Longrightarrow> preList xs C l s"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  obtain y e where a: "a=(y,e)" by fastforce
  from Cons show ?case unfolding a by (simp)
qed

lemma preSetpreList: "preList xs C l s \<Longrightarrow>  preSet (set xs) C l s"
proof (induct xs) 
  case (Cons a xs)
  obtain y e where a: "a=(y,e)" by fastforce
  from Cons show ?case unfolding a
    by(simp)
qed simp


(* surprise. but makes sense, if the clauses are contradictory on the 
    left side, so are they on the right side *)
lemma preSetpreList_eq: "preList xs C l s = preSet (set xs) C l s"
proof (induct xs) 
  case (Cons a xs)
  obtain y e where a: "a=(y,e)" by fastforce
  from Cons show ?case unfolding a
    by(simp)
qed simp  


fun postList where
  "postList []  l s = True"
| "postList ((x,e)#xs)  l s = (l x = e s \<and> postList xs l s)"

  
lemma support_postList: "support (postList xs) \<subseteq> lesvars xs"
proof (induct xs)    
  case (Cons a xs)
  obtain y e where a: "a=(y,e)" by fastforce
  from Cons show ?case unfolding a
    apply(simp) apply(rule subset_trans[OF support_and])
    apply(rule Un_least)
    subgoal apply(rule subset_trans[OF support_eq])
      using supportE_twicepreT subset_trans  supportE_single2 by simp
    subgoal by(auto)
      done   
qed simp
  
lemma postpreList_inv: assumes "S s = S (postQ C s)" 
  shows "postList (map (\<lambda>(x, e). (x, \<lambda>s. e (S s))) upds) l s =  preList (map (\<lambda>(x, e). (x, \<lambda>s. e (S s))) upds) C l s"
proof (induct upds) 
  case (Cons a upds)
  obtain y e where axe: "a = (y,e)" by fastforce    
  
  from Cons show ?case unfolding axe apply(simp) 
      apply(simp only: TQ) using assms by auto
qed simp
  
  
  
lemma postList_preList: "postList (map (\<lambda>(x, e). (x, preT C e)) upds) l s = preList upds C l s"
proof (induct upds) 
  case (Cons a xs)
  obtain y e where a: "a=(y,e)" by fastforce
  from Cons show ?case unfolding a
    by(simp)
qed simp
  
lemma postSetpostList: "postList xs l s \<Longrightarrow>  postSet (set xs) l s"
proof (induct xs) 
  case (Cons a xs)
  obtain y e where a: "a=(y,e)" by fastforce
  from Cons show ?case unfolding a
    by(simp)
qed simp
  

lemma postListpostSet: "postSet (set xs) l s \<Longrightarrow> postList xs l s"
proof (induct xs) 
  case (Cons a xs)
  obtain y e where a: "a=(y,e)" by fastforce
  from Cons show ?case unfolding a
    by(simp)
qed simp


lemma ListAskip: "preList xs Askip l s = postList xs  l s"
  apply(induct xs)
   apply(simp) by force

lemma SetAskip: "preSet U Askip l s = postSet U l s"
by simp

lemma ListAassign: "preList upds (Aassign x1 x2) l s = postList upds l (s[x2/x1])"
  apply(induct upds)
   apply(simp) by force

lemma SetAassign: "preSet U (Aassign x1 x2) l s = postSet U l (s[x2/x1])"
by simp


lemma ListAconseq: "preList upds (Aconseq x1 x2 x3 C) l s = preList upds C l s"
  apply(induct upds)
   apply(simp) by force

lemma SetAconseq: "preSet U (Aconseq x1 x2 x3 C) l s = preSet U C l s"
by simp

lemma ListAif1: "bval b s \<Longrightarrow> preList upds (IF b THEN C1 ELSE C2) l s = preList upds C1 l s"
  apply(induct upds)
   apply(simp) by force
lemma SetAif1: "bval b s \<Longrightarrow> preSet upds (IF b THEN C1 ELSE C2) l s = preSet upds C1 l s"
  apply(simp) done
lemma ListAif2: "~ bval b s \<Longrightarrow> preList upds (IF b THEN C1 ELSE C2) l s = preList upds C2 l s"
  apply(induct upds)
   apply(simp) by force

lemma SetAif2: "~ bval b s \<Longrightarrow> preSet upds (IF b THEN C1 ELSE C2) l s = preSet upds C2 l s"
  apply(simp) done
 
    
(*
  In upds we collect pairs of logical variables and time expressions, these logical variables
  are bound to the value of these expressions. postList upds C l s is an assertion stating that
  for every (x,e) in upds, l x = e s; preList upds C l s does the same, but pulls the expression
  e through the command c, i.e. stating for ever (x,e) in upds, l x = preT C e s. 

  we have to make sure, that no variable is assigned twice (the 5th premise), as well as they are 
  different from all the logical variables that occur in the annotated program C (4th premise)

  we have to make sure that we can always choose new logical variables (premise 2, 3)
*)    
lemma vc_sound: "vc C Q \<Longrightarrow> finite (support Q) \<Longrightarrow> finite (varacom C)
  \<Longrightarrow> fst ` (set upds) \<inter> varacom C = {} \<Longrightarrow> distinct (map fst upds)
  \<Longrightarrow>  \<turnstile>\<^sub>1 {%l s. pre C Q l s \<and> preList upds C l s} strip C { time C \<Down> %l s. Q l s \<and> postList upds l s}
  \<and> (\<forall>l s. pre C Q l s \<longrightarrow> Q l (postQ C s))"
proof(induction C arbitrary: Q upds)    
  case (Askip Q upds)
  then show ?case
    apply(auto)
    apply(rule weaken_post[where Q="%l s. Q l s \<and> preList upds Askip l s"])
     apply(simp add: Skip)  using ListAskip   
    by fast
next
  case (Aassign x1 x2 Q upds)
  then show ?case apply(safe) apply(auto simp add: Assign)[1]
     apply(rule weaken_post[where Q="%l s. Q l s \<and> postList upds l s"]) 
      apply(simp only: ListAassign)
      apply(rule Assign) apply simp
    apply(simp only: postQ.simps pre.simps) done
next
  case (Aif b C1 C2 Q upds )
  then show ?case apply(auto simp add: Assign)
     apply(rule If2[where e="\<lambda>a. if bval b a then  time C1 a else time C2 a"])
    subgoal
      apply(simp cong: rev_conj_cong)
      apply(rule ub_cost[where e'="time C1"])
       apply(simp) apply(auto)[1]
      apply(rule strengthen_pre[where P="%l s. pre C1 Q l s \<and> preList upds C1 l s"]) 
        using ListAif1
       apply fast
      apply(rule Aif(1)[THEN conjunct1])
           apply(auto)  
      done
    subgoal 
      apply(simp cong: rev_conj_cong)
      apply(rule ub_cost[where e'="time C2"])  (* k=1 and *)
       apply(simp) apply(auto)[1]
      apply(rule strengthen_pre[where P="%l s. pre C2 Q l s \<and> preList upds C2 l s"])
        using ListAif2
       apply fast
      apply(rule Aif(2)[THEN conjunct1])
           apply(auto)
      done
     apply auto apply fast+ done 
next
  case (Aconseq P' Qannot eannot C Q upds)  
  then obtain k where k: "k>0" and ih1: "vc C Qannot"
    and ih1': " (\<forall>l s. P' l s \<longrightarrow>  time C s \<le> k * eannot s \<and> (\<forall>t. \<exists>l'. pre C Qannot l' s \<and> (Qannot l' t \<longrightarrow> Q l t)))"
    by auto                       
      
  have ih2': "\<forall>l s. pre C Qannot l s \<longrightarrow> Qannot l (postQ C s)"
    apply(rule Aconseq(1)[THEN conjunct2]) using Aconseq(2-6) by auto    
    
  have G1: "\<turnstile>\<^sub>1 {\<lambda>l s. P' l s \<and> preList upds ({P'/Qannot/eannot} CONSEQ C) l s} strip C
         { eannot \<Down> \<lambda>l s. Q l s \<and> postList upds l s}"
  proof (rule conseq[rotated])
    show "\<turnstile>\<^sub>1 {\<lambda>l s. pre C Qannot l s \<and> preList upds C l s} strip C { time C \<Down> \<lambda>l s. Qannot l s \<and> postList upds l s}"
    apply(rule Aconseq(1)[THEN conjunct1])
      using Aconseq(2-6) by auto  
  next
    show "\<exists>k>0. \<forall>l s. P' l s \<and> preList upds ({P'/Qannot/eannot} CONSEQ C) l s \<longrightarrow>
              time C s \<le> k * eannot s \<and>
              (\<forall>t. \<exists>l'. (pre C Qannot l' s \<and> preList upds C l' s) \<and>
                        (Qannot l' t \<and> postList upds l' t \<longrightarrow> Q l t \<and> postList upds l t))"
    proof(rule exI[where x=k], safe)
      fix l s
      assume P': "P' l s" and prelist: "preList upds ({P'/Qannot/eannot} CONSEQ C) l s"
      then show "time C s \<le> k * eannot s" using ih1' by simp
                   
      fix t
      \<comment> \<open>we now have to construct a logical environment, that both
          * satisfies the annotated postcondition Qannot (we obtain it from the first IH)
          * lets the updates come true (we have to show that resetting these logical variables
              does not interfere with the other variables)\<close>  
      
      from ih1' P' have satQan:"(\<exists>l'. pre C Qannot l' s \<and> (Qannot l' t \<longrightarrow> Q l t))" by simp
      then obtain l' where i': "pre C Qannot l' s" and ii': "(Qannot l' t \<longrightarrow> Q l t)" by blast
          
      let ?upds' = "(map (%(x,e). (x,preT C e s)) upds)"
      let ?l'' = "(ListUpdateE l' ?upds')"
        
      {
        fix l s n x
        assume "x \<in> fst ` (set upds)"
        then have "x \<notin> support (pre C Qannot)" using Aconseq(5) support_pre by auto
        from assn2_lupd[OF this] have "pre C Qannot (l(x := n))  = pre C Qannot l" .
      } note U2=this 
      {
        fix l s n x
        assume "x \<in> fst ` (set upds)"
        then have "x \<notin> support Qannot" using Aconseq(5) by auto
        from assn2_lupd[OF this] have "Qannot (l(x := n))  = Qannot l" .
      } note K2=this  
              
      have "pre C Qannot ?l''  = pre C Qannot l'  "
        apply(rule allg_E[where ?upds="set upds"]) apply(rule U2) by force+
      with i' have i'': "pre C Qannot ?l'' s" by simp
      
      have "Qannot ?l'' = Qannot l'"
        apply(rule allg_E[where ?upds="set upds"]) apply(rule K2) by force+              
      then have K: "(%l' s. Qannot l' t \<longrightarrow> Q l t) ?l'' s = (%l' s. Qannot l' t \<longrightarrow> Q l t) l' s"
        by simp
      with ii' have ii'': "(Qannot ?l'' t \<longrightarrow> Q l t)" by simp
            
      have xs_upds: "map fst ?upds' = map fst upds"
           by auto          
      have resets: "\<And>x. x \<in> set ?upds' \<Longrightarrow> ListUpdateE l' ?upds' (fst x) = snd x" apply(rule ListUpdateE_updates)
         apply(simp only: xs_upds) using Aconseq(6) apply simp
           apply(simp) done         
        
      have A: "preList upds C ?l'' s" 
      proof (rule preListpreSet,safe,goal_cases)
        case (1 x e)
        then have "(x, preT C e s) \<in> set ?upds'"
          by fastforce
        from resets[OF this, simplified]
        show ?case .
      qed  
          
      have B: "Qannot ?l'' t \<Longrightarrow> postList upds ?l'' t \<Longrightarrow> postList upds l t"
      proof (rule postListpostSet, safe, goal_cases)        
        case (1 x e)            
        from postSetpostList[OF 1(2)] have g: "postSet (set upds) ?l'' t" .
        with 1(3) have A: "?l'' x = e t"
          by fast            
        from 1(3) resets[of "(x,preT C e s)"] have   B: "?l'' x = snd (x, preT C e s)"
          by fastforce
        from A B have X: "e t = preT C e s" by fastforce
        from preSetpreList[OF prelist] have "preSet (set upds) ({P'/Qannot/eannot} CONSEQ C) l s" .
        with 1(3) have Y: "l x = preT C e s" apply(simp) by fast
        from X Y show ?case by simp
      qed 
          
      show "\<exists>l'. (pre C Qannot l' s \<and> preList upds C l' s) \<and>
                  (Qannot l' t \<and> postList upds l' t \<longrightarrow> Q l t \<and> postList upds l t)"        
        apply(rule exI[where x="?l''"], safe)        
        using i'' A ii'' B by auto            
    qed fact 
  qed
    
  have G2: "\<And>l s. P' l s \<Longrightarrow> Q l (postQ C s)"
  proof -
    fix l s
    assume "P' l s"   
    with ih1' ih2' show "Q l (postQ C s)" by blast
  qed
     
  show ?case using G1 G2 by auto  
next
  case (Aseq C1 C2 Q upds)
   
  let ?P = "(\<lambda>l s. pre (C1;; C2) Q l s \<and> preList upds (C1;;C2) l s  )"
  let ?P' = "support Q \<union> varacom C1 \<union> varacom C2 \<union> lesvars upds"  
  
  have finite_varacom: "finite (varacom (C1;; C2))" by fact 
  have sup_L: "support (preList upds (C1;;C2)) \<subseteq> lesvars upds"
    apply(rule support_preList) done 
  
  \<comment> \<open>choose a fresh logical variable ?y in order to pull through the cost of the second command\<close>
  let ?y = "SOME x. x \<notin> ?P'" 
  have fP': "finite (?P')" using finite_varacom Aseq(4,5)   apply simp done
  from fP' have "\<exists>x. x \<notin> ?P'" using infinite_UNIV_listI
    using ex_new_if_finite by metis
  hence ynP': "?y \<notin> ?P'" by (rule someI_ex) 
  hence ysupC1: "?y \<notin> varacom C1" using support_pre by auto
  have sup_B: "support ?P \<subseteq> ?P'"                         
    apply(rule subset_trans[OF support_and]) apply simp using support_pre sup_L by blast   
        
  \<comment> \<open>we show the first goal: we can deduce the desired Hoare Triple\<close>  
  have C1: "\<turnstile>\<^sub>1 {\<lambda>l s. pre (C1;; C2) Q l s \<and> preList upds (C1;; C2) l s} strip C1;; strip C2
         { time (C1;; C2) \<Down> \<lambda>l s. Q l s \<and> postList upds l s}"
  proof (rule Seq[rotated])
    \<comment> \<open>start from the back: we can simply use the IH for C2, 
          and solve the side conditions automatically\<close>
    show "\<turnstile>\<^sub>1 {(%l s. pre C2 Q l s \<and>  preList upds C2 l s )} strip C2 { time C2 \<Down> (%l s. Q l s \<and> postList upds l s)}"
      apply(rule Aseq(2)[THEN conjunct1])  
      using Aseq(3-7) by auto   
  next    
    \<comment> \<open>prepare the new updates: pull them through C2 and save the new execution time of C2 in ?y\<close>    
    let ?upds = "map (\<lambda>a. case a of (x,e) \<Rightarrow> (x, preT C2 e )) upds"
    let ?upds' = "(?y,time C2)#?upds"   
      
    have dst_upds': "distinct (map fst ?upds')" 
      using  ynP' Aseq(7) apply simp apply safe 
        using image_iff apply fastforce  by (simp add: case_prod_beta' distinct_conv_nth) 
    
    \<comment> \<open>now use the first induction hypothesis (specialised with the augmented upds list, and the
        weakest precondition of Q through C as post condition)\<close>
    have IH1s: "\<turnstile>\<^sub>1 {\<lambda>l s. pre C1 (pre C2 Q) l s \<and> preList ?upds' C1 l s} strip C1
                    { time C1 \<Down> \<lambda>l s. pre C2 Q l s \<and> postList ?upds' l s}"
      apply(rule Aseq(1)[THEN conjunct1])
        using Aseq(3-7) ysupC1 dst_upds' by auto  
    
    \<comment> \<open>glue it together with a consequence rule, side conditions are automatic\<close>
    show " \<turnstile>\<^sub>1 {\<lambda>l s. (pre (C1;; C2) Q l s \<and> preList upds (C1;; C2) l s) \<and> l ?y = preT C1 (time C2) s} strip C1
     { time C1 \<Down> \<lambda>l s. (\<lambda>l s. pre C2 Q l s \<and> preList upds C2 l s) l s \<and> time C2 s \<le> l ?y}" 
      apply(rule conseq_old[OF _ IH1s]) 
      by (auto simp: preList_Seq postList_preList)  
  next
    \<comment> \<open>solve some side conditions showing that, ?y is indeed fresh\<close>
    show "?y \<notin> support ?P"
      using sup_B ynP' by auto        
    have F: "support (preList upds C2) \<subseteq> lesvars upds"  
      apply(rule support_preList) done 
    have "support (\<lambda>l s. pre C2 Q  l s \<and> preList upds C2 l s) \<subseteq> ?P'"
      apply(rule subset_trans[OF support_and]) using F support_pre by blast
    with ynP'
    show "?y \<notin> support (\<lambda>l s. pre C2 Q l s \<and> preList upds C2 l s)" by blast 
  qed simp
   
  \<comment> \<open>we show the second goal: weakest precondition implies, that
        Q holds after the execution of C1 and C2\<close>  
  have C2: "\<And>l s. pre (C1;; C2) Q l s \<Longrightarrow> Q l (postQ (C1;; C2) s)"
  proof -
    fix l s
    assume p: "pre (C1;; C2) Q l s"
    have A: "\<forall>l s. pre C1 (pre C2 Q )  l s \<longrightarrow> pre C2 Q  l (postQ C1 s)"
      apply(rule Aseq(1)[where upds="[]", THEN conjunct2])
      using Aseq by auto 
    have B: "(\<forall>l s. pre C2 Q  l s \<longrightarrow> Q l (postQ C2 s))" 
      apply(rule Aseq(2)[where upds="[]", THEN conjunct2])
      using Aseq by auto        
    from p A B show "Q l (postQ (C1;; C2) s)" by simp
  qed
    
  show ?case using C1 C2 by simp 
next
  case (Awhile A b C Q upds)
  
  \<comment> \<open>Let us first see, what we got from the induction hypothesis:\<close>
  obtain I S E  where [simp]: "A = (I,(S,(E)))" using prod_cases3 by blast
  with \<open>vc (Awhile A b C) Q\<close> have "vc (Awhile (I,S,E) b C) Q" by blast
  then  have vc: "vc C I"  and  pre2: "\<And>l s. I l s \<Longrightarrow> \<not> bval b s \<Longrightarrow>  Q l s \<and> 1 \<le> E s \<and> S s = s"
    and IQ2: "\<And>l s. I l s \<Longrightarrow> bval b s \<Longrightarrow>
                         pre C I l s
                          \<and>  1 + preT C E s + time C s \<le> E s \<and> S s = S (postQ C s)"  by auto      
    
  \<comment> \<open>the logical variable x represents the number of loop unfoldings\<close>
       
  
  from IQ2 have IQ_in: "\<And>l s. I l s \<Longrightarrow>   bval b s \<Longrightarrow> S s = S (postQ C s)" by auto
  
  have inv_impl: "\<And>l s.  I l s \<Longrightarrow>   bval b s \<Longrightarrow>  pre C I  l s" using IQ2 by auto    
  
  have yC: " lesvars upds \<inter> varacom C = {}" using Awhile(5) by auto
     
  let ?upds = "map (%(x,e). (x, %s. e (S s))) upds"
  let ?INV = "%l s. I l s \<and> postList ?upds l s"      
    
  have "lesvars upds \<inter> support I = {}" using Awhile(5) by auto
    
    
  \<comment> \<open>we need a fresh variable ?z to remember the time bound of the tail of the loop\<close>
  let ?P="lesvars upds \<union> varacom ({A} WHILE b DO C)"
  let ?z="SOME z::lvname. z \<notin> ?P"
  have "finite ?P" using Awhile by auto 
  hence "\<exists>z. z\<notin>?P"  using infinite_UNIV_listI
    using ex_new_if_finite by metis
  hence znP: "?z \<notin> ?P" by (rule someI_ex) 
  from znP have (* znx:  "?z\<noteq>x" 
    and *) zny:  "?z \<notin> lesvars upds"
    and zI:   "?z \<notin> support I" 
    and blb:  "?z \<notin> varacom C" by (simp_all)
      
  from Awhile(4,6) have 23: "finite (varacom C)" 
    and  26: "finite (support I)" by auto 
   
  have "\<forall>l s.  pre C I  l s \<longrightarrow> I l (postQ C s)"    
    apply(rule Awhile(1)[THEN conjunct2]) by(fact)+       
  hence step: "\<And>l s. pre C I l s \<Longrightarrow> I l (postQ C s)" by simp
 
      
  \<comment> \<open>we adapt the updates, by pulling them through the loop body 
      and remembering the time bound of the tail of the loop\<close>
  let ?upds = "map (\<lambda>(x, e). (x, \<lambda>s. e (S s))) upds"
  have fua: "lesvars ?upds = lesvars upds"
    by force
  let ?upds' = "(?z,E) # ?upds" 
     
      
  have g: "\<And>e. e \<circ> S = (%s. e (S s))" by auto
       
  \<comment> \<open>show that the Hoare Rule is derivable\<close>    
  have G1: "\<turnstile>\<^sub>1 {\<lambda>l s. I l s \<and> preList upds ({(I, S, E)} WHILE b DO C) l s} WHILE b DO strip C
         { E \<Down> \<lambda>l s. Q l s \<and> postList upds l s}"
  proof(rule conseq_old)
    show "\<turnstile>\<^sub>1 {\<lambda>l s. I l s \<and> postList ?upds l s} WHILE b DO strip C
              { E \<Down> \<lambda>l s. (I l s \<and> postList ?upds l s) \<and> \<not>bval b s }"
    \<comment> \<open>We use the While Rule and then have to show, that ...\<close>
    proof(rule While, goal_cases) 
      \<comment> \<open>A) the loop body preserves the loop invariant\<close>
      have "lesvars ?upds' \<inter> varacom C = {}"
        using yC blb by(auto)
          
      have z: "(fst \<circ> (\<lambda>(x, e). (x, \<lambda>s. e (S s)))) = fst" by auto
      have "distinct (map fst ?upds')"
        using Awhile(6) zny by (auto simp add: z)       
      
      \<comment> \<open>for showing preservation of the invariant, use the consequence rule ...\<close>
      show "\<turnstile>\<^sub>1 {\<lambda>l s. (I l s \<and> postList ?upds l s) \<and> bval b s \<and> preT C E s = l ?z}
       strip C {  time C \<Down> \<lambda>l s. (I l s \<and> postList ?upds l s) \<and> E s \<le> l ?z}" 
      proof (rule conseq_old)
        \<comment> \<open>... and employ the induction hypothesis, ...\<close>
        show " \<turnstile>\<^sub>1 {\<lambda>l s. pre C I l s \<and> preList ?upds' C l s} strip C
                { time C \<Down> \<lambda>l s. I l s \<and> postList ?upds' l s}"
          apply(rule Awhile.IH[THEN conjunct1]) by fact+              
      next
        \<comment> \<open>finally we have to prove the side condition.\<close>
        show "\<exists>k>0. \<forall>l s. (I l s \<and> postList ?upds l s) \<and> bval b s \<and> preT C E s = l ?z
                   \<longrightarrow> (pre C I l s \<and> preList ?upds' C l s) \<and> time C s \<le> k * time C s"
          apply(rule exI[where x=1]) apply(simp)
        proof (safe, goal_cases)              
          case (2 l s)
          note upds_invariant=postpreList_inv[OF IQ_in[OF 2(1)]]
          from 2  upds_invariant   show ?case by auto
        next
          case (1 l s) then show ?case using inv_impl by auto
        qed   
      qed auto
    next
      \<comment> \<open>B) the invariant with number of loop unfoldings greater than 0 implies true loop guard
             and running time is correctly bounded\<close>
      show "\<forall>l s. bval b s  \<and> I l s \<and> postList ?upds l s \<longrightarrow> 1 + preT C E s + time C s \<le> E s"        
      proof (clarify, goal_cases)
        case (1 l s)          
        show ?case using IQ2 1(1,2) by auto            
      qed
    next
      \<comment> \<open>C) the invariant with number of loop unfoldings equal to 0 implies false loop guard
             and running time is correctly bounded\<close>
      show "\<forall>l s.  \<not> bval b s \<and> I l s \<and> postList ?upds l s \<longrightarrow>  1 \<le> E s"
      proof (clarify, goal_cases)
        case (1 l s)  
        then show ?case 
          using pre2 1(2) by auto
      qed  
    next
      \<comment> \<open>D) ?z is indeed a fresh variable\<close>
      have pff: "?z \<notin> lesvars ?upds" apply(simp only: fua) by fact
      have "support (\<lambda>l s. I l s \<and> postList ?upds l s) \<subseteq> support I \<union> support (postList ?upds)"
        by(rule support_and) 
      also have "support (postList ?upds) \<subseteq> lesvars ?upds"
           apply(rule support_postList) done 
      finally 
      have "support (\<lambda>l s. I l s \<and> postList ?upds l s) \<subseteq> support I \<union> lesvars ?upds"
        by blast 
      thus "?z \<notin> support (\<lambda>l s. I l s \<and> postList ?upds l s)" 
        apply(rule contra_subsetD) 
        using zI pff by(simp)
    qed
  next
    show "\<exists>k>0. \<forall>l s. I l s  \<and> preList upds ({(I, S, E)} WHILE b DO C) l s \<longrightarrow>
              (I l s \<and> postList (map (\<lambda>(x, e). (x, \<lambda>s. e (S s))) upds) l s) \<and> E s \<le> k * E s"
       apply(rule exI[where x=1])   apply(auto)  apply(simp only: postList_preList[symmetric] ) apply (auto)
        apply(simp only:   g)  
        done
  next
    show "\<forall>l s. (I l s \<and> postList (map (\<lambda>(x, e). (x, \<lambda>s. e (S s))) upds) l s) \<and> \<not> bval b s  \<longrightarrow> Q l s \<and> postList upds l s"
      using pre2  by(induct upds, auto)  
  qed
    
  have G2: "\<And>l s. pre ({A} WHILE b DO C) Q l s \<Longrightarrow> Q l (postQ ({A} WHILE b DO C) s)"  
  proof -
    fix l s
    assume "pre ({A} WHILE b DO C) Q l s"
    then have I: "I l s" by simp
    { fix n
    have "E s = n \<Longrightarrow> I l s \<Longrightarrow> Q l (postQ ({A} WHILE b DO C) s)"
    proof (induct n arbitrary: s l rule: less_induct)
      case (less n)
      then show ?case 
      proof (cases "bval b s")
        case True
        with less IQ2 have "pre C I l s" and S: "S s = S (postQ C s)" and t: "1 + preT C E s + time C s \<le> E s" by auto
        with step have I': "I l (postQ C s)" and "1 + E (postQ C s) + time C s \<le> E s" using TQ by auto
        with less have "E (postQ C s) < n" by auto    
        with less(1) I' have "Q l (postQ ({A} WHILE b DO C) (postQ C s))" by auto
        with step show ?thesis using S by simp
      next
        case False
        with pre2 less(3) have "Q l s" "S s = s" by auto
        then show ?thesis by simp
      qed
    qed
    }
    with I show "Q l (postQ ({A} WHILE b DO C) s)" by simp   
  qed
   
  show ?case  using G1  G2 by auto    
qed
 


 


corollary vc_sound':
  assumes "vc C Q" 
          "finite (support Q)" "finite (varacom C)"
          "\<forall>l s. P l s \<longrightarrow> pre C Q l s" 
  shows "\<turnstile>\<^sub>1 {P} strip C {time C \<Down> Q}"
proof -
  show ?thesis
    apply(rule conseq_old)
      prefer 2 apply(rule vc_sound[where upds="[]", OF assms(1-3), THEN conjunct1])      
    using assms(4) apply auto 
    done 
qed

lemma preT_constant: "preT C (%_. a) = (%_. a)"
  apply(induct C) by (auto)
 

corollary vc_sound'':
  "\<lbrakk> vc C Q; (\<exists>k>0. \<forall>l s. P l s \<longrightarrow> pre C Q l s \<and> time C s \<le> k * e s);
  finite (support Q); finite (varacom C)\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>1 {P} strip C {e \<Down> Q}"
  apply(rule ub_cost[where e'="time C"])
   apply(auto)
  apply(rule vc_sound') by auto

subsubsection \<open>Completeness:\<close>

lemma vc_complete:
  "\<turnstile>\<^sub>1 {P} c { e \<Down> Q} \<Longrightarrow>   \<exists>C. strip C = c \<and> vc C Q 
  \<and> (\<forall>l s. P l s \<longrightarrow> pre C Q l s \<and> Q l (postQ C s))
  \<and> (\<exists>k. \<forall>l s. P l s \<longrightarrow>  time C s \<le> k * e s)  "
  (is "_ \<Longrightarrow>   \<exists>C. ?G P c Q C e")
proof (induction  rule: hoare1.induct )
  case Skip
  show ?case (is "\<exists>C. ?C C")
  proof show "?C Askip" by auto   
  qed
next
  case (Assign P a x  )
  show ?case (is "\<exists>C. ?C C")
  proof show "?C(Aassign x a)" apply (simp del: fun_upd_apply) apply(auto) done qed
next
  case (Seq P x e2' c1 e1 Q e2 c2 R e) 
  from Seq.IH(1)   obtain C1 where "?G (\<lambda>l s. P l s \<and> l x = e2' s) c1 (\<lambda>a b. Q a b \<and> e2 b \<le> a x) C1 e1 " by blast
  then obtain k where ih1: "strip C1 = c1"
    "vc C1 (\<lambda>a b. Q a b \<and> e2 b \<le> a x)"
    "\<And>l s. P l s \<Longrightarrow> l x = e2' s \<Longrightarrow> pre C1 (\<lambda>la sa. (Q la sa \<and> e2 sa \<le> la x)) l s"
    "(\<forall>l s. P l s \<and> l x = e2' s \<longrightarrow>  time C1 s \<le> k * e1 s)" 
    "\<And>l s.  P l s \<Longrightarrow> l x = e2' s \<Longrightarrow> Q l (postQ C1 s) \<and> e2 (postQ C1 s) \<le> l x" 
    apply auto done
  
  from Seq.IH(2)   obtain C2 where ih2: "?G Q c2 R C2 e2  " by blast
  then obtain k2 where ih2: "strip C2 = c2"
    "vc C2 R"
    "(\<And>l s. Q l s \<Longrightarrow> pre C2 R l s)"
    "(\<forall>l s. Q l s \<longrightarrow>  time C2 s \<le> k2 * e2 s)"
    "\<And>l s . Q l s \<Longrightarrow> R l (postQ C2 s)"  apply auto done
  
  show ?case (is "\<exists>C. ?C C")
  proof 
    show "?C(Aseq (Aconseq P Q (time C1) C1) C2)" (* with Q being (\<lambda>la sa. (Q la sa \<and> e2 sa \<le> la x)) some less mono is needed *)
    proof (safe, goal_cases)
      case 1
      then show ?case apply(simp add: ih1(1) ih2(1)) done
    next
      case 2
      then show ?case apply(simp) apply(safe)
        subgoal apply(rule vc_mono) prefer 2 apply (rule ih1(2)) apply(auto) done
        subgoal apply(rule exI[where x=1]) apply safe
          subgoal by(auto)              
          subgoal for l s t
            apply(rule exI[where x="l(x:= e2' s)"])              
            apply(safe)              
            subgoal apply(rule pre_mono) prefer 2 apply (rule ih1(3))                
                apply(subst assn2_lupd) using Seq(3) by auto                
            subgoal apply(rule ih2(3)) using assn2_lupd[OF Seq(4)] by auto               
            done
          done
        subgoal by (rule ih2(2)) 
        done
    next
      case (3 l s)
      then show ?case apply(simp) done
    next
      
      case (4 l s)      
      from 4 have "P (l(x:=e2' s)) s" using assn2_lupd[OF Seq(3)] by simp
      with ih1(5)[where l="l(x:=e2' s)"]
      have "Q (l(x := e2' s)) (postQ C1 s)" by simp
      then have "Q l (postQ C1 s)" using assn2_lupd[OF Seq(4)] by simp
      with ih2(3) have "Q l (postQ C1 s)" by simp 
      with  ih2(5)
      show ?case apply(auto) done 
    next
      case 5
      from ih1(4) have
        gg: "\<And>l s. \<lbrakk>P l s; e2' s = l x\<rbrakk> \<Longrightarrow>   time C1 s \<le> k * e1 s" by auto
      
      show ?case
      proof (rule exI[where x="(max k  k2)"], safe, goal_cases)
        case (1 l s)
        have xnP: "x \<notin> support P" by fact
        have 41: "P (l(x := e2' s)) s"
          apply(subst assn2_lupd)
           apply(fact xnP)
          apply(fact 5) done
        
        have A: "  time C1 s \<le> k * e1 s"
          apply(rule gg[where l="l(x:=e2' s)"])
           apply(rule 41)
          apply(simp)  done  
        
        have B: "preT C1 (time C2) s \<le> k2 * e2' s"
        proof - 
          from  1 have "P (l(x := e2' s)) s" using assn2_lupd[OF xnP] by simp
          
          have F: "Q (l(x:=e2' s)) (postQ C1 s) \<and> e2 (postQ C1 s) \<le> (l(x:=e2' s)) x"
            apply(rule ih1(5)[where l="l(x:=e2' s)" and s=s]) 
             apply(fact)
            apply(simp) done
          then have " time C2 (postQ C1 s) \<le> k2 * e2 (postQ C1 s)" using ih2(4) by auto
          with F have "time C2 (postQ C1 s) \<le> k2 * e2' s"
            using order_subst1 by fastforce 
          then show "preT C1 (time C2) s \<le> k2 * e2' s" using TQ by simp  
        qed  
        have "time C1 s + preT C1 (time C2) s \<le> k  * e1 s + k2 * e2' s" using A B by linarith
        also have "\<dots> \<le> (max k  k2) * e1 s + (max k  k2) * e2' s" 
        using nat_mult_max_left by auto
      also have "\<dots> = (max k  k2) * (e1 s + e2' s)" by algebra
      also have "\<dots> \<le> (max k  k2) * e s" using Seq(5)[OF 1] by auto 
      finally
      have "time C1 s + preT C1 (time C2) s \<le> (max k  k2) * e s" .
      then show ?case
        by auto  
    qed
  qed
  qed
  
next
  case (If P b c1 e1 Q c2) 
  from If.IH(1) obtain C1 where "?G (\<lambda>l s. P l s \<and> bval b s) c1 Q C1 e1"
    by blast
  then obtain k1 where ih1: " strip C1 = c1 \<and> vc C1 Q \<and> (\<forall>l s. P l s \<and> bval b s \<longrightarrow> pre C1 Q l s \<and> Q l (postQ C1 s)) \<and>  ( \<forall>l s. P l s \<and> bval b s \<longrightarrow> time C1 s \<le> k1 * e1 s) "
      by blast
  from If.IH(2) obtain C2 where "?G (\<lambda>l s. P l s \<and> \<not>bval b s) c2 Q C2 e1"
    by blast
  then obtain k2 where ih2: " strip C2 = c2 \<and> vc C2 Q \<and> (\<forall>l s. P l s \<and> \<not>bval b s \<longrightarrow> pre C2 Q l s \<and> Q l (postQ C2 s)) \<and>  ( \<forall>l s. P l s \<and> \<not>bval b s \<longrightarrow> time C2 s \<le> k2 * e1 s )"
    by blast
  define k' where "k' == max (k1+1) (k2+1)"
  show ?case (is "\<exists>C. ?C C")
  proof
    show "?C(Aif b C1 C2)"
      apply(safe)
          prefer 5
      apply(rule exI[where x="k'"]) apply(safe)
      subgoal for l s  apply(auto)
      proof(goal_cases)
        case 1
        with ih1 have "time C1 s \<le> k1 * e1 s" by blast
        then have "Suc (time C1 s) \<le> 1 + k1 * e1 s" by auto
        also have "\<dots> \<le> k' + k1 * e1 s" unfolding k'_def by(auto)
        also have "\<dots> \<le> k' + k' * e1 s" unfolding k'_def
          by (simp add: max_def) 
        finally show ?case .
      next
        case 2
        with ih2 have "time C2 s \<le> k2 * e1 s" by blast
        then have "Suc (time C2 s) \<le> 1 + k2 * e1 s" by auto
        also have "\<dots> \<le> k' + k2 * e1 s" unfolding k'_def by(auto)
        also have "\<dots> \<le> k' + k' * e1 s" unfolding k'_def
          by (simp add: max_def) 
        finally show ?case .
      qed       
      using ih1 ih2 apply(simp) 
      using ih1 ih2 apply(auto)
      done  
  qed  
next
  case (While P b e' y c e'' e)
  have supportPre: "support (\<lambda>l s. P l s \<and> bval b s \<and> e' s = l y) \<subseteq> support P \<union> {y}"
  using support_and support_single   by fast
  from   While.IH  obtain C where
    ih: "?G (\<lambda>l s. P l s \<and> bval b s \<and> e' s = l y) c (\<lambda>a b. P a b \<and> e b \<le> a y) C e''"
    using supportPre by blast
  then obtain k where ih2: "vc C (\<lambda>a b. P a b \<and> e b \<le> a y)"
    "\<And>l s. \<lbrakk> P l s ; bval b s ; e' s = l y \<rbrakk> \<Longrightarrow> pre C (\<lambda>la sa. (P la sa \<and> e sa \<le> la y)) l s" 
    "\<And>l s. \<lbrakk> P l s ; bval b s ; e' s = l y \<rbrakk> \<Longrightarrow>   time C s \<le> k * e'' s " 
    "\<And>l s.\<lbrakk> P l s ; bval b s ; e' s = l y\<rbrakk> \<Longrightarrow> P l (postQ C s) \<and> e (postQ C s) \<le> l y"
    by fast
   
  let ?S = "postQs C b"
  {
    fix l s n
    have "e s = n \<Longrightarrow> P l s \<Longrightarrow> postQs_dom (C, b, s) \<and> P l (?S s) \<and> ~ bval b (?S s)"
    proof (induct n arbitrary: l s rule: less_induct)
      case (less x)
      show ?case
      proof (cases "bval b s")
        case True
        with While(2) less(3) have "1 + e' s + e'' s \<le> e s" by auto
        then have e'e: "e' s < e s" by simp
        have "P (l(y:=e' s)) s" using less(3) assn2_lupd[OF While(4)] by simp    
        from ih2(4)[OF this] True have ee': "e (postQ C s) \<le> e' s" and P': "P (l(y := e' s)) (postQ C s)" by auto
        from P' have P'': "P l (postQ C s)" using less(3) assn2_lupd[OF While(4)] by simp 
        from ee' e'e less(2) have "e (postQ C s) < x" by auto 
        from less(1)[OF this _ P''] have d: "postQs_dom (C, b, postQ C s)" 
              and p: "P l (postQs C b (postQ C s))"
              and b: "\<not> bval b (postQs C b (postQ C s))" by auto
        have d': "postQs_dom (C, b, s)"
          by (simp add: d postQs.domintros)           
        have p': " P l (postQs C b s) "
          using True d p postQs.domintros postQs.psimps by fastforce 
        have b': "\<not> bval b (postQs C b s)"
          by (metis b d postQs.domintros postQs.pelims)
          
        from d' p' b' show ?thesis by auto
      next
        case False
        then have 1: "postQs_dom (C, b, s)"
          using postQs.domintros by blast    
        then have 2: "?S s = s" using postQs.psimps False by force
        from 1 2 less(3) False show ?thesis by simp
      qed
    qed
  }
  then have Pdom: "\<And>l s. P l s \<Longrightarrow> postQs_dom (C, b, s) \<and> P l (?S s) \<and> ~ bval b (?S s)" by simp
    
  have S1: "\<And>l s. P l s \<Longrightarrow> P l (?S s)" using Pdom by simp
  have S2: "\<And>l s. P l s \<Longrightarrow> ~ bval b (?S s)" using Pdom by simp  
  have S3: "\<And>l s. P l s \<Longrightarrow> bval b s \<Longrightarrow> ?S s = ?S (postQ C s)" using postQs.psimps Pdom by simp
  have S4: "\<And>l s. P l s \<Longrightarrow> \<not> bval b s \<Longrightarrow> ?S s = s" using postQs.psimps Pdom by simp
      
  let ?w = "{(P,?S,(%s. max k 1 * e s))} WHILE b DO (Aconseq (\<lambda>l s. P l s \<and> bval b s) (\<lambda>la sa. P la sa \<and> e sa \<le> la y) (time C) C)"
  
  show ?case (is "\<exists>C. ?C C")
  proof
    show "?C ?w" 
    proof (safe, goal_cases)
      case 1
      then show ?case using ih by(simp) 
    next
      case 2
      then show ?case 
      proof(simp, safe, goal_cases)
        case (1 l s)         
        from 2 have z: "P (l(y := e' s)) s "
          using 1 assn2_lupd[OF While(4)]  by metis
        from ih2(3)[where l="l(y := e' s)" and s=s]
        have A: " time C s \<le> k * e'' s " using 1 z by(simp)         
        
        from ih2(4)[where l="l(y := e' s)" and s=s]
        have "e (postQ C s) \<le> (l(y := e' s)) y" apply(simp) using 1 z by(simp) 
        then have "e (postQ C s) \<le> e' s" by simp 
        
        with TQ have B: "preT C e s \<le> e' s" by simp 
        let ?eskal = "(\<lambda>s. max k (Suc 0) * e s)"
        have "preT C (\<lambda>s. max k (Suc 0) * e s) s = max k (Suc 0) * preT C e s"
          using preT_linear by simp
        with B have  B: "preT C ?eskal s \<le> max k (Suc 0) * e' s" by auto
        
        from  While.hyps(2) 1 have C: "1 + e' s + e'' s \<le> e s" by auto       
        have "Suc (preT C ?eskal s + time C s) \<le> 1 + (max k 1) * e' s + k * e'' s"
          using A B by linarith
        also have "\<dots> \<le> (max k 1) + (max k 1) * e' s + (max k 1) * e'' s"
          using nat_mult_max_left by auto
        also have "\<dots> = (max k 1) * (1 + e' s + e'' s)"
          by algebra
        also have "\<dots> \<le> (max k 1) * e s" 
          using C by (metis mult.assoc mult_le_mono2) 
        finally have "Suc (preT C ?eskal s + time C s) \<le> ((max k 1) ) * e s" .
        thus ?case by auto
      next
        case (3 l s)
        with While.hyps(3) show ?case by auto      
      next
        case 5
        then show ?case
           apply(rule vc_mono)
           prefer 2 apply(fact ih2(1)) by auto
      next
        case 6
        show ?case apply(rule exI[where x="1"]) apply(safe)
          subgoal by simp
          subgoal for l s t apply(rule exI[where x="l(y:=e' s)"])
              
          proof (safe)
            assume 8: "P l s" and b: " bval b s"
            then have "P (l(y := e' s)) s" using assn2_lupd[OF While(4)]  by metis 
            with b ih2(2)  show "pre C (\<lambda>la sa. P la sa \<and> e sa \<le> la y) (l(y := e' s)) s"
              apply(auto) done
            fix t
            assume "P (l(y := e' s)) t"
            thus "P l t" using assn2_lupd[OF While(4)] by simp
          qed 
          done       
      qed (simp_all add: S4 S3)   
    next
      case 6
      show ?case apply(rule exI[where x="k+1"]) by auto 
    qed (simp_all add: S1 S2)
  qed 
next
  case (conseq P' e e' P Q Q' c) 
  then obtain C k where C: "strip C = c"
    "vc C Q"
    "(\<forall>l s  . P l s \<longrightarrow> pre C Q  l s )"
    "(\<forall>l s . P l s \<longrightarrow> Q l (postQ C s))"
    "(\<forall>l s. P l s \<longrightarrow>  time C s \<le> k * e s)" by metis
  from conseq(1) obtain k2 where cons: " \<forall>l s. P' l s \<longrightarrow> e s \<le> k2 * e' s \<and> (\<forall>t. \<exists>l'. P l' s \<and> (Q l' t \<longrightarrow> Q' l t))" by auto
   
  show ?case
    apply(rule exI[where x="Aconseq P' Q (time C) C"])
    apply(safe)
    subgoal apply(simp) by(fact)  
    subgoal apply(simp)
      apply(safe)
      subgoal using C(2)   
          apply(fast) done
      subgoal 
        apply(rule exI[where x="k+1"])
        apply auto
        using C(2) cons C(3) by blast   
      done
    subgoal apply(rule pre_mono)        
      prefer 2 apply(simp) using C(3) conseq(1) apply fast        
      done      
    subgoal  
      apply(simp)
      using C(4) conseq(1,3) apply blast done
    apply(rule exI[where x="k*k2"]) apply(safe)
    subgoal for l s
      using C(5) cons apply(auto) 
    proof(goal_cases)
      case 1
      then have absch: "e s \<le> k2 * e' s" "time C s \<le> k  * e s" by blast+
      show ?case  
        using absch order_trans by fastforce
    qed
    done
qed 

end