theory Nielson_VCGi
imports Nielson_Hoare "Vars"
begin

subsection "Optimized Verification Condition Generator"

text\<open>Annotated commands: commands where loops are annotated with invariants.\<close>

datatype acom =
  Askip                  ("SKIP") |
  Aassign vname aexp     ("(_ ::= _)" [1000, 61] 61) |
  Aseq   acom acom       ("_;;/ _"  [60, 61] 60) |
  Aif bexp acom acom     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61) |
  Aconseq "assn2*(vname set)" "assn2*(vname set)" "tbd * (vname set)"  acom
  ("({_'/_'/_}/ CONSEQ _)"  [0, 0, 0, 61] 61)|
  Awhile "(assn2*(vname set))*((state\<Rightarrow>state)*(tbd*((vname set*(vname \<Rightarrow> vname set)))))" bexp acom  ("({_}/ WHILE _/ DO _)"  [0, 0, 61] 61)
  
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

definition supportE :: "((char list \<Rightarrow> nat) \<Rightarrow> (char list \<Rightarrow> int) \<Rightarrow> nat)  \<Rightarrow> string set" where
  "supportE P = {x. \<exists>l1 l2 s. (\<forall>y. y \<noteq> x \<longrightarrow> l1 y = l2 y) \<and> P l1 s \<noteq> P l2 s}"
  
  
lemma expr_lupd: "x \<notin> supportE Q \<Longrightarrow> Q (l(x:=n)) = Q l"
  by(simp add: supportE_def fun_upd_other fun_eq_iff)
    (metis (no_types, lifting) fun_upd_def)

 
fun varacom :: "acom \<Rightarrow> lvname set" where
  "varacom (C\<^sub>1;; C\<^sub>2)= varacom C\<^sub>1 \<union> varacom C\<^sub>2"
| "varacom (IF b THEN C\<^sub>1 ELSE C\<^sub>2)= varacom C\<^sub>1 \<union> varacom C\<^sub>2"
| "varacom ({(P,_)/(Qannot,_)/_} CONSEQ C)= support P \<union> varacom C \<union> support Qannot"
| "varacom ({((I,_),(S,(E,Es)))} WHILE b DO C) = support I \<union> varacom C "
| "varacom _ = {}"
     
  
fun varnewacom :: "acom \<Rightarrow> lvname set" where
  "varnewacom (C\<^sub>1;; C\<^sub>2)= varnewacom C\<^sub>1 \<union> varnewacom C\<^sub>2"
| "varnewacom (IF b THEN C\<^sub>1 ELSE C\<^sub>2)= varnewacom C\<^sub>1 \<union> varnewacom C\<^sub>2"
| "varnewacom ({_/_/_} CONSEQ C)= varnewacom C"
| "varnewacom ({(I,(S,(E,Es)))} WHILE b DO C) = varnewacom C"
| "varnewacom _ = {}"
  
lemma finite_varnewacom: "finite (varnewacom C)"
  by (induct C) (auto)



fun wf :: "acom \<Rightarrow> lvname set \<Rightarrow> bool" where
  "wf SKIP _ = True" |
  "wf (x ::= a) _ = True" |
  "wf (C\<^sub>1;; C\<^sub>2) S = (wf C\<^sub>1 (S \<union> varnewacom C\<^sub>2) \<and> wf C\<^sub>2 S)" |
  "wf (IF b THEN C\<^sub>1 ELSE C\<^sub>2) S = (wf C\<^sub>1 S \<and> wf C\<^sub>2 S)" |
  "wf ({_/(Qannot,_)/_} CONSEQ C) S = (finite (support Qannot) \<and> wf C S)" |
  "wf ({(_,(_,(_,Es)))} WHILE b DO C) S = ( wf C S)"
    
text\<open>Weakest precondition from annotated commands:\<close>

fun preT :: "acom \<Rightarrow> tbd \<Rightarrow> tbd" where
  "preT SKIP e = e" |
  "preT (x ::= a) e = (\<lambda>s. e(s(x := aval a s)))" |
  "preT (C\<^sub>1;; C\<^sub>2) e = preT C\<^sub>1 (preT C\<^sub>2 e)" |
  "preT ({_/_/_} CONSEQ C) e = preT C e" |
  "preT (IF b THEN C\<^sub>1 ELSE C\<^sub>2) e =
  (\<lambda>s. if bval b s then preT C\<^sub>1 e s else preT C\<^sub>2 e s)" |
  "preT ({(_,(S,_))} WHILE b DO C) e = e o S"
  

lemma preT_constant: "preT C (%_. a) = (%_. a)"
  by(induct C, auto)

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
  
  
  
(* function that, given a Command C and a set of variables 
  gives the set of variables, that Es depends on,
  meaning a set S where
  if s1 = s2 on S \<longrightarrow> \<forall>x:Es. postQ C s1 x = postQ C s2 x
*)
fun fune :: "acom \<Rightarrow> vname set \<Rightarrow> vname set" where
  "fune SKIP LV = LV" |
  "fune (x ::= a) LV = LV \<union> vars a" |
  "fune (C\<^sub>1;; C\<^sub>2) LV = fune C\<^sub>1 (fune C\<^sub>2 LV)" |
  "fune ({_/_/_} CONSEQ C) LV = fune C LV" |
  "fune (IF b THEN C\<^sub>1 ELSE C\<^sub>2) LV = vars b \<union> fune C\<^sub>1 LV \<union> fune C\<^sub>2 LV" |
  "fune ({(_,(S,(E,Es,SS)))} WHILE b DO C) LV = (\<Union>x\<in>LV. SS x)"
  
lemma fune_mono: "A \<subseteq> B \<Longrightarrow> fune C A \<subseteq> fune C B"
proof(induct C arbitrary: A B)  
  case (Awhile x1 x2 C)
  obtain a b c d e f where a: "x1 = (a,b,c,d,e)" using prod_cases5 by blast
  from Awhile show ?case unfolding a by(auto)
qed (auto simp add: le_supI1 le_supI2)
  
  
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

fun postQz :: "acom \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> state" where
  "postQz C s 0 = s" |
  "postQz C s (Suc n) =  (postQz C (postQ C s) n)"
  
fun preTz :: "acom \<Rightarrow> tbd \<Rightarrow> nat \<Rightarrow> tbd" where
  "preTz C e 0 = e" |
  "preTz C e (Suc n) = preT C (preTz C e n)"
  
  
  
lemma TzQ: "preTz C e n s = e (postQz C s n)"
  by (induct n arbitrary: s, simp_all add: TQ)



text\<open>Weakest precondition from annotated commands:\<close>

  (* if the annotated command contains no loops,
  then the weakest precondition is just some mangled post condition
  in the other case, 
  the weakest precondition is essentially the annotated invariant
  of the first while loop, mangled somewhat by the commands
  preceding the loop. *)

fun pre :: "acom \<Rightarrow> assn2 \<Rightarrow> assn2" where
  "pre SKIP Q  = Q" |
  "pre (x ::= a) Q = (\<lambda>l s. Q l (s(x := aval a s)))" |
  "pre (C\<^sub>1;; C\<^sub>2) Q  = pre C\<^sub>1 (pre C\<^sub>2 Q)" |
  "pre ({(P',Ps)/_/_} CONSEQ C) Q = P'" |
  "pre (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q =
  (\<lambda>l s. if bval b s then pre C\<^sub>1 Q l s else pre C\<^sub>2 Q l s)" |
  "pre ({((I,Is),(S,(E,Es,SS)))} WHILE b DO C) Q = I" 
  
  
fun qdeps :: "acom \<Rightarrow> vname set \<Rightarrow> vname set" where
  "qdeps SKIP LV  = LV" |
  "qdeps (x ::= a) LV = LV \<union> vars a" | 
  "qdeps (C\<^sub>1;; C\<^sub>2) LV  = qdeps C\<^sub>1 (qdeps C\<^sub>2 LV)" |
  "qdeps ({(P',Ps)/_/_} CONSEQ C) _ = Ps" | (* the variables P' depends on *)
  "qdeps (IF b THEN C\<^sub>1 ELSE C\<^sub>2) LV = vars b \<union> qdeps C\<^sub>1 LV \<union> qdeps C\<^sub>2 LV" | 
  "qdeps ({((I,Is),(S,(E,x,Es)))} WHILE b DO C) _ = Is" (* the variables I depends on *) 
   
lemma qdeps_mono: "A \<subseteq> B \<Longrightarrow> qdeps C A \<subseteq> qdeps C B"
  by (induct C arbitrary: A B, auto simp: le_supI1 le_supI2)
  
lemma supportE_if: "supportE (\<lambda>l s. if b s then A l s else B l s)
  \<subseteq> supportE A \<union> supportE B"
  unfolding supportE_def apply(auto)
  by metis+

lemma supportE_preT: "supportE (%l. preT C (e l)) \<subseteq> supportE e"
proof(induct C arbitrary: e)
  case (Aif b C1 C2 e)
  show ?case
    apply(simp)
    apply(rule subset_trans[OF supportE_if])
    using Aif by fast
next
  case (Awhile A y C e)
  obtain I S E x where A: "A= (I,S,E,x)" using prod_cases4 by blast
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

lemma support_pre: "support (pre C Q) \<subseteq> support Q \<union> varacom C"
proof (induct C arbitrary: Q)
  case (Awhile A b C Q)
  obtain I2 S E Es SS where A: "A= (I2,(S,(E,Es,SS)))" using prod_cases5 by blast 
  obtain I Is where "I2=(I,Is)" by fastforce
  note A=this A
  have support_inv: "\<And>P. support (\<lambda>l s. P s) = {}"
    unfolding support_def by blast  
  show ?case unfolding A  by(auto)
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
  obtain a b c d e f where "x1=(a,b)" "x2=(c,d)" "x3=(e,f)" by force
  with Aconseq show ?case by auto  
qed (auto simp add: support_def) 

lemma finite_support_pre: "finite (support Q)  \<Longrightarrow> finite (varacom C) \<Longrightarrow>  finite (support (pre C Q))"
  using finite_subset support_pre finite_UnI by metis 


fun time :: "acom \<Rightarrow> tbd" where
  "time SKIP = (%s. Suc 0)" |
  "time (x ::= a) = (%s. Suc 0)" |
  "time (C\<^sub>1;; C\<^sub>2) = (%s. time C\<^sub>1 s + preT C\<^sub>1 (time C\<^sub>2) s)" |
  "time ({_/_/(e,es)} CONSEQ C) = e" |
  "time (IF b THEN C\<^sub>1 ELSE C\<^sub>2) =
  (\<lambda>s. if bval b s then 1 + time C\<^sub>1 s else 1 + time C\<^sub>2 s)" |
  "time ({(_,(E',(E,x)))} WHILE b DO C) = E"
   
   
(* the set of variables, i need to know about, i.e. s1 and s2 have to agree on 
  s.th. time C s1 = time C s2 *)    
fun kdeps :: "acom \<Rightarrow> vname set" where
  "kdeps SKIP = {}" |
  "kdeps (x ::= a) = {}" |
  "kdeps (C\<^sub>1;; C\<^sub>2) = kdeps C\<^sub>1 \<union> fune C\<^sub>1 (kdeps C\<^sub>2)" |
  "kdeps (IF b THEN C\<^sub>1 ELSE C\<^sub>2) =  vars b \<union> kdeps C\<^sub>1 \<union> kdeps C\<^sub>2" |
  "kdeps ({(_,(E',(E,Es,SS)))} WHILE b DO C) = Es" |
  "kdeps ({_/_/(e,es)} CONSEQ C) = es"  
     
     
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

     
definition funStar where "funStar f = (%x. {y. (x,y)\<in>{(x,y). y\<in>f x}\<^sup>*})"
  
lemma funStart_prop1: "x \<in> (funStar f) x" unfolding funStar_def by auto
lemma funStart_prop2: "f x \<subseteq> (funStar f) x" unfolding funStar_def by auto

fun vc :: "acom \<Rightarrow> assn2 \<Rightarrow> vname set \<Rightarrow> vname set \<Rightarrow> bool" where
  "vc SKIP Q _ _ = True" |
  "vc (x ::= a) Q _ _ = True" |
  "vc (C\<^sub>1 ;; C\<^sub>2) Q LVQ LVE = ((vc C\<^sub>1 (pre C\<^sub>2 Q) (qdeps C\<^sub>2 LVQ) (fune C\<^sub>2 LVE \<union> kdeps C\<^sub>2)) \<and> (vc C\<^sub>2 Q LVQ LVE) )" |
  "vc (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q LVQ LVE = (vc C\<^sub>1 Q LVQ LVE \<and> vc C\<^sub>2 Q LVQ LVE)" |  
  "vc ({(P',Ps)/(Q,Qs)/(e',es)} CONSEQ C) Q' LVQ LVE = (vc C Q Qs LVE  \<comment> \<open>evtl \<open>LV\<close> weglassen - glaub eher nicht\<close>
              \<and> (\<forall>s1 s2 l. (\<forall>x\<in>Ps. s1 x=s2 x) \<longrightarrow> P' l s1 = P' l s2)    \<comment> \<open>annotation \<open>Ps\<close> (the set of variables \<open>P'\<close> depends on) is correct\<close>
              \<and> (\<forall>s1 s2 l. (\<forall>x\<in>Qs. s1 x=s2 x) \<longrightarrow> Q l s1 = Q l s2)    \<comment> \<open>annotation \<open>Qs\<close> (the set of variables \<open>Q\<close> depends on) is correct\<close>
              \<and> (\<forall>s1 s2. (\<forall>x\<in>es. s1 x=s2 x) \<longrightarrow> e' s1 = e' s2)          \<comment> \<open>annotation \<open>es\<close> (the set of variables \<open>e'\<close> depends on) is correct\<close>
              \<and> (\<exists>k>0. (\<forall>l s. P' l s \<longrightarrow> time C s \<le> k * e' s  \<and> (\<forall>t. \<exists>l'. (pre C Q) l' s \<and> ( Q l' t \<longrightarrow> Q' l t) ))))" |
  
  "vc ({((I,Is),(S,(E,es,SS)))} WHILE b DO C) Q LVQ LVE = ((\<forall>s1 s2 l. (\<forall>x\<in>Is. s1 x = s2 x) \<longrightarrow> I l s1 = I l s2)  \<comment> \<open>annotation \<open>Is\<close> is correct\<close>
        \<and> (\<forall>y\<in>LVE \<union> LVQ. (let Ss=SS y in (\<forall>s1 s2. (\<forall>x\<in>Ss. s1 x = s2 x) \<longrightarrow> (S s1) y = (S s2) y)))                   \<comment> \<open>annotation \<open>SS\<close> is correct, for only one step\<close>
        \<and> (\<forall>s1 s2. (\<forall>x\<in>es. s1 x=s2 x) \<longrightarrow> E s1 = E s2)                                \<comment> \<open>annotation \<open>es\<close> (the set of variables \<open>E\<close> depends on) is correct\<close>
  \<and> (\<forall>l s. (I l s \<and> bval b s \<longrightarrow> pre C I l s \<and>   E s \<ge> 1 + preT C E s + time C s
  \<and> (\<forall>v\<in>(\<Union>y\<in>LVE \<union> LVQ. (funStar SS) y). (S s) v = (S (postQ C s)) v) ) \<and>
  (I l s \<and> \<not> bval b s \<longrightarrow> Q l s \<and> E s \<ge> 1 \<and> (\<forall>v\<in>(\<Union>y\<in>LVE \<union> LVQ. (funStar SS) y). (S s) v  = s v)) ) \<and>
  vc C I Is (es \<union> (\<Union>y\<in>LVE. (funStar SS) y)))"
     
subsubsection \<open>Soundness:\<close>

abbreviation "preSet U C l s == (Ball U (%u. case u of (x,e,v) \<Rightarrow> l x = preT C e s))"
abbreviation "postSet U l s == (Ball U (%u. case u of (x,e,v) \<Rightarrow> l x = e s))"


fun ListUpdate where
  "ListUpdate f [] l = f"
| "ListUpdate f ((x,e,v)#xs) q = (ListUpdate f xs q)(x:=q e x)"

lemma allg: 
  assumes U2: "\<And>l s n x. x\<in> fst ` upds \<Longrightarrow> A (l(x := n))  = A l"
  shows
    "fst ` set xs \<subseteq> fst ` upds \<Longrightarrow> A (ListUpdate l'' xs q) = A l''" 
proof (induct xs) 
  case (Cons a xs)
  obtain x e v where axe: "a = (x,e,v)"
    using prod_cases3 by blast 
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
| "ListUpdateE f ((x,e,v)#xs)  = (ListUpdateE f xs  )(x:=e)"

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

lemma ListUpdateE_updates: "distinct (map fst xs) \<Longrightarrow> x \<in> set xs \<Longrightarrow> ListUpdateE l'' xs (fst x) = fst (snd x)"
proof (induct xs)
  case Nil
  then show ?case apply(simp) done
next
  case (Cons a xs)
  show ?case
  proof (cases "fst a = fst x")
    case True
    then obtain y e v where a: "a=(y,e,v)"
      using prod_cases3 by blast 
    with True have fstx: "fst x=y" by simp
    from Cons(2,3) fstx  a have a2: "x=a"
      by force
    show ?thesis unfolding a2 a by(simp)
  next
    case False
    with Cons(3) have A: "x\<in>set xs" by auto
    then obtain y e v where a: "a=(y,e,v)"
      using prod_cases3 by blast 
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
  obtain q p v where axe: "a = (p,q,v)"
      using prod_cases3 by blast 
  from Cons show ?case unfolding axe
    apply(cases "x=p")  
    by(simp_all)
qed
  
abbreviation "lesvars xs == fst ` (set xs)"
  
fun preList where
  "preList [] C l s = True"
| "preList ((x,(e,v))#xs) C l s = (l x = preT C e s \<and> preList xs C l s)"
      
  
lemma preList_Seq: "preList upds (C1;; C2) l s = preList (map (\<lambda>(x, e, v). (x, preT C2 e, fune C2 v)) upds) C1 l s"
proof (induct upds)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  obtain y e v where a: "a=(y,(e,v))"
    using prod_cases3 by blast 
  from Cons show ?case unfolding a by (simp)
qed

lemma [simp]: "support (\<lambda>a b. True) = {}" 
  unfolding support_def 
  by fast
  
lemma support_preList: "support (preList upds C1) \<subseteq> lesvars upds"
proof (induct upds)
  case Nil
  then show ?case by simp 
next
  case (Cons a upds)
  obtain y e v where a: "a=(y,(e,v))"
    using prod_cases3 by blast 
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
  obtain y e v where a: "a=(y,(e,v))"
    using prod_cases3 by blast 
  from Cons show ?case unfolding a by (simp)
qed

lemma preSetpreList: "preList xs C l s \<Longrightarrow>  preSet (set xs) C l s"
proof (induct xs) 
  case (Cons a xs)
  obtain y e v where a: "a=(y,(e,v))"
    using prod_cases3 by blast 
  from Cons show ?case unfolding a
    by(simp)
qed simp


(* surprise. but makes sense, if the clauses are contradictory on the 
    left side, so are they on the right side *)
lemma preSetpreList_eq: "preList xs C l s = preSet (set xs) C l s"
proof (induct xs) 
  case (Cons a xs)
  obtain y e v where a: "a=(y,(e,v))"
    using prod_cases3 by blast 
  from Cons show ?case unfolding a
    by(simp)
qed simp  


fun postList where
  "postList []  l s = True"
| "postList ((x,e,v)#xs)  l s = (l x = e s \<and> postList xs l s)"

lemma "postList xs l s = (foldr (\<lambda>(x,e,v) acc l s. l x = e s \<and> acc l s) xs (%l s. True)) l s" 
apply(induct xs) apply(simp) by (auto)  
  
lemma support_postList: "support (postList xs) \<subseteq> lesvars xs"
proof (induct xs)    
  case (Cons a xs)
  obtain y e v where a: "a=(y,(e,v))"
    using prod_cases3 by blast 
  from Cons show ?case unfolding a
    apply(simp) apply(rule subset_trans[OF support_and])
    apply(rule Un_least)
    subgoal apply(rule subset_trans[OF support_eq])
      using supportE_twicepreT subset_trans  supportE_single2 by simp
    subgoal by(auto)
      done   
qed simp
  
  
  
lemma postList_preList: "postList (map (\<lambda>(x, e, v). (x, preT C2 e, fune C2 v)) upds) l s = preList upds C2 l s"
proof (induct upds) 
  case (Cons a xs)
  obtain y e v where a: "a=(y,(e,v))"
    using prod_cases3 by blast 
  from Cons show ?case unfolding a
    by(simp)
qed simp
  
lemma postSetpostList: "postList xs l s \<Longrightarrow>  postSet (set xs) l s"
proof (induct xs) 
  case (Cons a xs)
  obtain y e v where a: "a=(y,(e,v))"
    using prod_cases3 by blast 
  from Cons show ?case unfolding a
    by(simp)
qed simp
  

lemma postListpostSet: "postSet (set xs) l s \<Longrightarrow> postList xs l s"
proof (induct xs) 
  case (Cons a xs)
  obtain y e v where a: "a=(y,(e,v))"
    using prod_cases3 by blast 
  from Cons show ?case unfolding a
    by(simp)
qed simp

lemma postListpostSet2: " postList xs l s = postSet (set xs) l s "
  using postListpostSet postSetpostList by metis



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

definition K where "K C LVQ Q == (\<forall>l s1 s2. s1 = s2 on qdeps C LVQ \<longrightarrow> pre C Q l s1 = pre C Q l s2)"
  

definition K2 where "K2 C e Es Q == (\<forall>s1 s2. s1 = s2 on fune C Es \<longrightarrow> preT C e s1 = preT C e s2)"
  
definition K3 where "K3 upds C Q = (\<forall>(a,b,c)\<in>set upds. K2 C b c Q)"
definition K4 where "K4 upds LV C Q = (K C LV Q \<and> K3 upds C Q \<and> (\<forall>s1 s2. s1 = s2 on kdeps C \<longrightarrow> time C s1 = time C s2))"

lemma k4If: "K4 upds LVQ C1 Q \<Longrightarrow> K4 upds LVQ C2 Q \<Longrightarrow> K4 upds LVQ (IF b THEN C1 ELSE C2) Q"    
proof -
  have fl: "\<And>A B s1 s2. A \<subseteq> B \<Longrightarrow> s1 = s2 on B \<Longrightarrow> s1 = s2 on A" by auto
  assume "K4 upds LVQ C1 Q" "K4 upds LVQ C2 Q"
  then show "K4 upds LVQ (IF b THEN C1 ELSE C2) Q"
    unfolding K4_def K_def K3_def K2_def using bval_eq_if_eq_on_vars fl apply auto
       apply blast+ done
qed
   

subsubsection "Soundness"
  
lemma vc_sound: "vc C Q LVQ LVE \<Longrightarrow> finite (support Q)
  \<Longrightarrow> fst ` (set upds) \<inter> varacom C = {} \<Longrightarrow> distinct (map fst upds)
  \<Longrightarrow> finite (varacom C) 
  \<Longrightarrow> (\<forall>l s1 s2. s1 = s2 on LVQ \<longrightarrow> Q l s1 = Q l s2)
  \<Longrightarrow> (\<forall>l s1 s2. s1 = s2 on LVE \<longrightarrow> postList upds l s1 = postList upds l s2)
  \<Longrightarrow> (\<forall>(a,b,c)\<in>set upds. (\<forall>s1 s2. s1 = s2 on c \<longrightarrow> b s1 = b s2))             \<comment> \<open>\<open>c\<close> are really the variables \<open>b\<close> depends on\<close>
  \<Longrightarrow> (\<Union>(a,b,c)\<in>set upds. c) \<subseteq> LVE                                     \<comment> \<open>in \<open>LV\<close> are all the variables that the expressions in \<open>upds\<close> depend on\<close>
  \<Longrightarrow> \<turnstile>\<^sub>1 {%l s. pre C Q l s \<and> preList upds C l s} strip C { time C \<Down> %l s. Q l s \<and> postList upds l s}
  \<and> ((\<forall>l s. pre C Q l s \<longrightarrow> Q l (postQ C s)) \<and>  K4 upds LVQ C Q)"
proof(induction C arbitrary: Q upds LVE LVQ)    
  case (Askip Q upds)
  then show ?case unfolding K4_def K_def K3_def K2_def
    apply(auto)
    apply(rule weaken_post[where Q="%l s. Q l s \<and> preList upds Askip l s"])
     apply(simp add: Skip)  using ListAskip    
    by fast
next
  case (Aassign x1 x2 Q upds)
  then show ?case unfolding K_def apply(safe) apply(auto simp add: Assign)[1]
     apply(rule weaken_post[where Q="%l s. Q l s \<and> postList upds l s"]) 
      apply(simp only: ListAassign)
      apply(rule Assign) apply simp
     apply(simp only: postQ.simps pre.simps) apply(auto)  
        unfolding K4_def K2_def K3_def K_def by (auto)
next
  case (Aif b C1 C2 Q upds ) 
  from Aif(3) have 1: "vc C1 Q LVQ LVE" and 2: "vc C2 Q LVQ LVE" by auto
  have T: "\<And>l s. pre C1 Q l s \<Longrightarrow> bval b s \<Longrightarrow> Q l (postQ C1 s)"
      and kT: "K4 upds LVQ C1 Q"
    using Aif(1)[OF 1 Aif(4) _ Aif(6)] Aif(5-11) by auto 
  have F: "\<And>l s. pre C2 Q l s \<Longrightarrow> \<not> bval b s \<Longrightarrow> Q l (postQ C2 s)"
    and kF: "K4 upds LVQ C2 Q"
    using Aif(2)[OF 2 Aif(4) _ Aif(6)] Aif(5-11) by auto

  show ?case apply(safe)
    subgoal
      apply(simp)
     apply(rule If2[where e="\<lambda>a. if bval b a then  time C1 a else time C2 a"])
    subgoal
      apply(simp cong: rev_conj_cong)
      apply(rule ub_cost[where e'="time C1"])
       apply(simp) apply(auto)[1]
      apply(rule strengthen_pre[where P="%l s. pre C1 Q l s \<and> preList upds C1 l s"]) 
        using ListAif1
       apply fast
        apply(rule Aif(1)[THEN conjunct1])
          using Aif
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
          using Aif
           apply(auto)
          done
        by simp
    using T F kT kF  by (auto intro: k4If)  
next
  case (Aconseq P'2 Qannot2 eannot2 C Q upds) 
  obtain P' Ps where [simp]: "P'2 = (P',Ps)" by fastforce
  obtain Qannot Q's where [simp]: "Qannot2 = (Qannot,Q's)" by fastforce
  obtain eannot es where [simp]: "eannot2 = (eannot,es)" by fastforce
    
  have ih0: "finite (support Qannot)" using Aconseq(3,6) by simp
  
  from \<open>vc ({P'2/Qannot2/eannot2} CONSEQ C) Q LVQ LVE\<close>
  obtain k where k0: "k>0" and ih1: "vc C Qannot Q's LVE"
    and ih2: " (\<forall>l s. P' l s \<longrightarrow>  time C s \<le> k * eannot s \<and> (\<forall>t. \<exists>l'. pre C Qannot l' s \<and> (Qannot l' t \<longrightarrow> Q l t)))"
    and pc: "(\<forall>s1 s2 l. (\<forall>x\<in>Ps. s1 x=s2 x) \<longrightarrow> P' l s1 = P' l s2)"
    and qc: "(\<forall>s1 s2 l. (\<forall>x\<in>Q's. s1 x=s2 x) \<longrightarrow> Qannot l s1 = Qannot l s2)"
    and ec: "(\<forall>s1 s2. (\<forall>x\<in>es. s1 x=s2 x) \<longrightarrow> eannot s1 = eannot s2)"  
    by auto
  have  k: "\<turnstile>\<^sub>1 {\<lambda>l s. pre C Qannot l s \<and> preList upds C l s} strip C { time C \<Down> \<lambda>l s. Qannot l s \<and> postList upds l s}
    \<and> ((\<forall>l s. pre C Qannot l s \<longrightarrow> Qannot l (postQ C s)) \<and> K4 upds Q's C Qannot)" 
    apply(rule Aconseq(1)) using Aconseq(2-10) by auto 
      
  note ih=k[THEN conjunct1] and ihsnd=k[THEN conjunct2]

  show ?case apply(simp, safe)
     apply(rule conseq[where e="time C" and P="\<lambda>l s. pre C Qannot l s \<and> preList upds C l s" and Q="%l s. Qannot l s \<and> postList upds l s"])
      prefer 2
      apply(rule ih) 
    subgoal apply(rule exI[where x=k])
    proof (safe, goal_cases)
      case (1)
      with k0 show ?case by auto
    next      
      case (2 l s)
      then show ?case using ih2 by simp
    next
      case (3 l s t) 
      have finupds: "finite (set upds)" by simp
      {
        fix l s n x
        assume "x \<in> fst ` (set upds)"
        then have "x \<notin> support (pre C Qannot)" using Aconseq(4) support_pre by auto
        from assn2_lupd[OF this] have "pre C Qannot (l(x := n))  = pre C Qannot l" .                
      } note U2=this 
      {
        fix l s n x
        assume "x \<in> fst ` (set upds)"
        then have "x \<notin> support Qannot" using Aconseq(4) by auto
        from assn2_lupd[OF this] have "Qannot (l(x := n))  = Qannot l" .
      } note K2=this  
                           
      from ih2 3(1) have *: "(\<exists>l'. pre C Qannot l' s \<and> (Qannot l' t \<longrightarrow> Q l t))" by simp
      obtain l' where i': "pre C Qannot l' s" and ii': "(Qannot l' t \<longrightarrow> Q l t)" 
        and lxlx: "\<And>x. x\<in> fst ` (set upds) \<Longrightarrow> l' x = l x" 
      proof (goal_cases)
        case 1
        from * obtain l'' where i': "pre C Qannot l'' s" and ii': "(Qannot l'' t \<longrightarrow> Q l t)" 
          by blast
        
        note allg=allg[where q="%e x. l x"]
        
        have "pre C Qannot (ListUpdate l'' upds (\<lambda>e. l))  = pre C Qannot l''  "
          apply(rule allg[where ?upds="set upds"]) apply(rule U2) apply fast   by fast
        with i' have U: "pre C Qannot (ListUpdate l'' upds (\<lambda>e. l)) s" by simp
        
        have "Qannot (ListUpdate l'' upds (\<lambda>e. l)) = Qannot l''"
          apply(rule allg[where ?upds="set upds"]) apply(rule K2) apply fast  by fast
                
        then have K: "(%l' s. Qannot l' t \<longrightarrow> Q l t) (ListUpdate l'' upds (\<lambda>e. l)) s = (%l' s. Qannot l' t \<longrightarrow> Q l t) l'' s"
          by simp
        with ii' have K: "(Qannot (ListUpdate l'' upds (\<lambda>e. l)) t \<longrightarrow> Q l t)" by simp
        
        {
          fix x
          assume as: "x \<in> fst ` (set upds)" 
          have "ListUpdate l'' upds (\<lambda>e. l) x = l x"
            apply(rule ListUpdate_updates)
            using as   by fast
        } note kla=this        
        
        show "thesis"
          apply(rule 1)
            apply(fact U)
           apply(fact K)
          apply(fact kla)
          done
      qed 
      
      let ?upds' = "set (map (%(x,e,v). (x,preT C e s,fune C v)) upds)"
      have "finite ?upds'" by simp 
      define xs where "xs = map (%(x,e,v). (x,preT C e s,fune C v)) upds"
      then have "set xs= ?upds'" by simp
                                
      have "pre C Qannot (ListUpdateE l' xs)  = pre C Qannot l' " 
        apply(rule allg_E[where ?upds="?upds'"]) apply(rule U2)  
         apply force   unfolding xs_def by simp
      with i' have U: "pre C Qannot (ListUpdateE l' xs ) s" by simp
      
      have "Qannot (ListUpdateE l' xs) = Qannot l' "
          apply(rule allg_E[where ?upds="?upds'"]) apply(rule K2) apply force unfolding xs_def by auto
        then have K: "(%l' s. Qannot l' t \<longrightarrow> Q l t) (ListUpdateE l' xs) s = (%l' s. Qannot l' t \<longrightarrow> Q l t) l' s"
          by simp
        with ii' have K: "(Qannot (ListUpdateE l' xs) t \<longrightarrow> Q l t)" by simp
                  
        
      have xs_upds: "map fst xs = map fst upds"
          unfolding xs_def by auto
      
      have grr: "\<And>x. x \<in> ?upds' \<Longrightarrow> ListUpdateE l' xs (fst x) = fst (snd x)" apply(rule ListUpdateE_updates)
         apply(simp only: xs_upds) using Aconseq(5) apply simp
          unfolding xs_def apply(simp) done
      show ?case
        apply(rule exI[where x="ListUpdateE l' xs"]) 
        apply(safe)
        subgoal by fact
        subgoal apply(rule preListpreSet)   proof (safe,goal_cases)
          case (1 x e v)
          then have "(x, preT C e s, fune C v) \<in> ?upds'"  
            by force
          from grr[OF this, simplified]
          show ?case .
         
          qed 
        subgoal using K apply(simp) done (* Qannot must be independent of x *)
        subgoal apply(rule postListpostSet) 
          proof (safe, goal_cases)
            case (1 x e v)
            with lxlx[of x] have fF: "l x = l' x"  
              by force 
            
            from postSetpostList[OF 1(2)] have g: "postSet (set upds) (ListUpdateE l' xs) t" .
            with 1(3) have A: "(ListUpdateE l' xs) x = e t"
              by fast            
            from 1(3) grr[of "(x,preT C e s, fune C v)"] have   B: "ListUpdateE l' xs x = fst (snd (x, preT C e s, fune C v))"
               by force
            from A B have X: "e t = preT C e s" by fastforce
            from preSetpreList[OF 3(2)] have "preSet (set upds) ({P'2/Qannot2/eannot2} CONSEQ C) l s" apply(simp) done
            with 1(3) have Y: "l x = preT C e s" apply(simp) by fast
            from X Y show ?case by simp
          qed  
        done
    qed
    subgoal using ihsnd ih2 by blast
    subgoal using ihsnd[THEN conjunct2] pc unfolding K4_def K_def apply(auto)
              unfolding K3_def K2_def using ec by auto
    done 
next
  case (Aseq C1 C2 Q upds)
   
  let ?P = "(\<lambda>l s. pre C1 (pre C2 Q) l s \<and> preList upds (C1;;C2) l s  )"
  let ?P' = "support Q \<union> varacom C1 \<union> varacom C2 \<union> lesvars upds"
  
  
  have finite_varacom: "finite (varacom (C1;; C2))"  by fact 
  have finite_varacomC2: "finite (varacom C2)" 
    apply(rule finite_subset[OF _ finite_varacom]) by simp 
  
  let ?y = "SOME x. x \<notin> ?P'" 
  have sup_L: "support (preList upds (C1;;C2)) \<subseteq> lesvars upds"
    apply(rule support_preList) done 
  
  
  have sup_B: "support ?P \<subseteq> ?P'"                         
    apply(rule subset_trans[OF support_and]) using support_pre sup_L by blast 
  have fP': "finite (?P')" using finite_varacom Aseq(3,4,5)   apply simp done
  hence "\<exists>x. x \<notin> ?P'" using infinite_UNIV_listI
    using ex_new_if_finite by metis
  hence ynP': "?y \<notin> ?P'" by (rule someI_ex) 
  hence ysupPreC2Q: "?y \<notin> support (pre C2 Q)" and ysupC1: "?y \<notin> varacom C1" using support_pre by auto
  
  from Aseq(5) have "lesvars upds \<inter> varacom C2 = {}" by auto
  
  from Aseq show ?case apply(auto)
  proof (rule Seq, goal_cases)
    case 2   
    show "\<turnstile>\<^sub>1 {(%l s. pre C2 Q l s \<and>  preList upds C2 l s )} strip C2 { time C2 \<Down> (%l s. Q l s \<and> postList upds l s)}"
      apply(rule weaken_post[where Q="(%l s. Q l s \<and> postList upds l s)"])
       apply(rule 2(2)[THEN conjunct1])
          apply fact
         apply (fact)+ using 2(8) by simp      
  next
    case 3
    fix s
    show "time C1 s + preT C1 (time C2) s  \<le> time C1 s + preT C1 (time C2) s"
      by simp
  next
    case 1 
     
    
    from ynP' have yC1: "?y \<notin> varacom C1" by blast
    have xC1: "lesvars upds \<inter> varacom C1 = {}" using Aseq(5) by auto
    from finite_support_pre[OF Aseq(4) finite_varacomC2] 
    have G: "finite (support (pre C2 Q))" . 
         
    let ?upds = "map (\<lambda>a. case a of (x,e,v) \<Rightarrow> (x, preT C2 e, fune C2 v)) upds"
    let ?upds' = "(?y,time C2, kdeps C2)#?upds"
    
    { 
      have A: " lesvars ?upds' = {?y} \<union> lesvars upds" apply simp 
        by force
      from Aseq(5) have 2: "lesvars upds \<inter> varacom C1 = {}" by auto
      have " lesvars ?upds' \<inter> varacom C1 = {}"
        unfolding A using ysupC1 2 by blast
    } note klar=this
    
    have t: "fst \<circ> (\<lambda>(x, e, v). (x, preT C2 e, fune C2 v)) = fst" by auto
    
    {
      fix a b c X
      assume "a \<notin> lesvars X" "(a,b,c) \<in> set X" 
      then have "False" by force
    } note helper=this
    
    have dmap: "distinct (map fst ?upds')"
      apply(auto simp add: t)
      subgoal for e apply(rule helper[of ?y upds e])  using ynP' by auto
      subgoal by fact
      done
    note bla1=1(1)[where Q="pre C2 Q" and upds="?upds'", OF 1(10) G klar dmap]  
      
    note bla=1(2)[OF 1(11,3), THEN conjunct2, THEN conjunct2] 
    from 1(4) have kal: "lesvars upds \<inter> varacom C2 = {}" by auto
    from bla[OF kal Aseq.prems(4,6,7,8,9)] have bla4: "K4 upds LVQ C2 Q"   by auto
    then   have bla: "K C2 LVQ Q" unfolding K4_def  by auto
      
    have A:  
        "\<turnstile>\<^sub>1 {\<lambda>l s. pre C1 (pre C2 Q) l s \<and> preList ?upds' C1 l s}
      strip C1
      { time C1 \<Down> \<lambda>l s. pre C2 Q l s \<and> postList ?upds' l s} \<and>
  (\<forall>l s. pre C1 (pre C2 Q) l s \<longrightarrow> pre C2 Q l (postQ C1 s)) \<and>  K4 ?upds' (qdeps C2 LVQ) C1 (pre C2 Q)"
      apply(rule 1(1)[where Q="pre C2 Q" and upds="?upds'", OF 1(10) G klar dmap]) 
    proof (goal_cases)
      case 1        
      then show ?case using bla  unfolding K_def by auto
    next
      case 2
      show ?case apply(rule,rule,rule,rule) proof (goal_cases)
        case (1 l s1 s2)
      then show ?case using bla4 using Aseq.prems(9) unfolding K4_def K3_def K2_def
        apply(simp)
        proof (goal_cases)
          case 1
          then have t: "time C2 s1 = time C2 s2" by auto
          
          have post: "postList (map (\<lambda>(x, e, v). (x, preT C2 e, fune C2 v)) upds) l s1 = postList (map (\<lambda>(x, e, v). (x, preT C2 e, fune C2 v)) upds) l s2" (is "?IH upds")
            using 1 
          proof (induct upds) 
            case (Cons a upds)
            then have IH: "?IH upds" by auto
            obtain x e v where a: "a = (x,e,v)" using prod_cases3 by blast
            from Cons(4) have "v \<subseteq> LVE" unfolding a by auto
            with Cons(2) have s12v: "s1 = s2 on fune C2 v" unfolding a using fune_mono by blast 
            with Cons(3) IH a show ?case by auto 
          qed auto
          
          from post t show ?case by auto
        qed 
      qed
    next
      case 3
      then show ?case  using bla4 unfolding K4_def K3_def K2_def by(auto)
    next
      case 4
      then show ?case apply(auto)
      proof (goal_cases)
        case (1 x a aa b)
        with Aseq.prems(9) have "b \<subseteq> LVE" by auto
        with fune_mono have "fune C2 b \<subseteq> fune C2 LVE" by auto
        with 1 show ?case by blast
      qed  
    qed
       
    show " \<turnstile>\<^sub>1 {\<lambda>l s. (pre C1 (pre C2 Q) l s \<and> preList upds (C1;; C2) l s) \<and> l ?y = preT C1 (time C2) s} strip C1
         { time C1 \<Down> \<lambda>l s. (pre C2 Q l s \<and> preList upds C2 l s) \<and> time C2 s \<le> l ?y}" 
      apply(rule conseq_old)
       prefer 2 
      apply(rule A[THEN conjunct1]) 
       apply(auto simp: preList_Seq postList_preList) done 
    
    from A[THEN conjunct2, THEN conjunct2] have A1: "K C1 (qdeps C2 LVQ) (pre C2 Q)" 
            and A2: "K3 ?upds' C1 (pre C2 Q)"  and A3: "(\<forall>s1 s2. s1 = s2 on kdeps C1 \<longrightarrow> time C1 s1 = time C1 s2)" unfolding K4_def by auto
    from bla4 have B1: "K C2 LVQ Q" and B2: "K3 upds C2 Q" and B3: "(\<forall>s1 s2. s1 = s2 on kdeps C2 \<longrightarrow> time C2 s1 = time C2 s2)" unfolding K4_def by auto
    show "K4 upds LVQ (C1;; C2) Q " 
      unfolding K4_def apply(safe)
      subgoal using A1 B1 unfolding K_def by(simp)  
      subgoal using A2 B2 unfolding K3_def K2_def apply(auto) done
      subgoal for s1 s2 using A3 B3 apply auto
      proof (goal_cases)
        case 1
        then have t: "time C1 s1 = time C1 s2" by auto
        from A2 have "\<forall>s1 s2. s1 = s2 on fune C1 (kdeps C2) \<longrightarrow> preT C1 (time C2) s1 = preT C1 (time C2) s2" unfolding K3_def K2_def by auto
        then have p: "preT C1 (time C2) s1 =  preT C1 (time C2) s2"
            using 1(1) by simp
        from t p show ?case by auto
      qed
      done
  next    
    from ynP' sup_B show "?y \<notin> support ?P" by blast 
    have F: "support (preList upds C2) \<subseteq> lesvars upds"  
      apply(rule support_preList) done 
    have "support (\<lambda>l s. pre C2 Q  l s \<and> preList upds C2 l s) \<subseteq> ?P'"
      apply(rule subset_trans[OF support_and]) using F support_pre by blast
    with ynP'
    show "?y \<notin> support (\<lambda>l s. pre C2 Q  l s \<and> preList upds C2 l s)" by blast
  next
    case (6 l s) 
    
    
    note bla=6(2)[OF 6(11,3), THEN conjunct2, THEN conjunct2] 
    from 6(4) have kal: "lesvars upds \<inter> varacom C2 = {}" by auto
    from bla[OF kal Aseq.prems(4,6,7,8,9)] have bla4: "K4 upds LVQ C2 Q"   by auto
    then   have bla: "K C2 LVQ Q" unfolding K4_def  by auto
    
    have 11: "finite (support (pre C2 Q )) " 
      apply(rule finite_subset[OF support_pre])
      using 6(3,4,10)  finite_varacomC2 by blast 
    have A: "\<forall>l s. pre C1 (pre C2 Q )  l s \<longrightarrow> pre C2 Q  l (postQ C1 s)"
      apply(rule 6(1)[where upds="[]", THEN conjunct2, THEN conjunct1])
            apply(fact)+  apply(auto) using bla unfolding K_def apply blast+ done 
    have B: "(\<forall>l s. pre C2 Q  l s \<longrightarrow> Q l (postQ C2 s))" 
      apply(rule 6(2)[where upds="[]", THEN conjunct2, THEN conjunct1])
        apply(fact)+ apply auto using Aseq.prems(6) by auto    
    from A B 6 show ?case by simp 
  qed  
next
  case (Awhile A b C Q upds)
  obtain I2 S E Es SS where aha[simp]: "A = (I2,(S,(E,Es,SS)))" using prod_cases5 by blast
  obtain I Is where aha2: "I2 = (I, Is)"  
    by fastforce
  let ?LV ="(\<Union>y\<in>LVE \<union> LVQ. (funStar SS) y)" 
  have LVE_LVE: "LVE \<subseteq> (\<Union>y\<in>LVE. (funStar SS) y)" using funStart_prop1  by fast
  have LV_LV: "LVE \<union> LVQ \<subseteq> ?LV" using funStart_prop1  by fast
  have LV_LV2: "(\<Union>y\<in>LVE \<union> LVQ. SS y) \<subseteq> ?LV" using funStart_prop2 by fast
  have LVE_LV2: "(\<Union>y\<in>LVE. SS y) \<subseteq> (\<Union>y\<in>LVE. (funStar SS) y)" using funStart_prop2 by fast
  note aha = aha2 aha 
  with aha aha2 \<open>vc (Awhile A b C) Q LVQ LVE\<close> have "vc (Awhile ((I,Is),S,E,Es,SS) b C) Q LVQ LVE" apply auto apply fast+ done
  then                 
  have vc: "vc C I Is (Es \<union> (\<Union>y\<in>LVE. (funStar SS) y))" 
    and IQ: "\<forall>l s. (I l s \<and> bval b s \<longrightarrow> pre C I l s \<and>  1 + preT C E s + time C s \<le> E s \<and> S s = S (postQ C s) on ?LV)" and
    pre: "\<forall>l s. (I l s \<and> \<not> bval b s \<longrightarrow> Q l s \<and> 1 \<le> E s \<and> S s = s on ?LV)"
    and Is: "(\<forall>s1 s2 l. s1 = s2 on Is \<longrightarrow> I l s1 = I l s2)"
    and Ss:  "(\<forall>y\<in>LVE \<union> LVQ. let Ss = SS y in \<forall>s1 s2. s1 = s2 on Ss \<longrightarrow> S s1 y = S s2 y)"
    and Es: "(\<forall>s1 s2. s1 = s2 on Es \<longrightarrow> E s1 = E s2)" apply simp_all apply auto apply fast+ done
    
  then have pre2: "\<And>l s. I l s \<Longrightarrow> \<not> bval b s \<Longrightarrow> Q l s \<and> 1 \<le> E s \<and> S s = s on ?LV"
    and IQ2: "\<And>l s. (I l s \<Longrightarrow> bval b s \<Longrightarrow> pre C I l s \<and>  1 + preT C E s + time C s \<le> E s \<and> S s = S (postQ C s) on ?LV)"
    and Ss2:  "\<And>y s1 s2. s1 = s2 on (\<Union>y\<in>LVE. SS y) \<Longrightarrow> S s1 = S s2 on LVE"
    by auto
  
  from Ss have Ssc: "\<And>c s1 s2. c \<subseteq> LVE \<Longrightarrow>  s1 = s2 on (\<Union>y\<in>c. SS y) \<Longrightarrow> S s1 = S s2 on c" 
    by auto
    
  from IQ have IQ_in: "\<And>l s. I l s \<Longrightarrow> bval b s \<Longrightarrow> S s = S (postQ C s) on ?LV" by auto
  
  have inv_impl: "\<And>l s. I l s \<Longrightarrow> bval b s \<Longrightarrow> pre C I  l s" using IQ by auto    
  
  have yC: "lesvars upds \<inter> varacom C = {}" using Awhile(4) aha by auto
   
  let ?upds = "map (%(x,e,v). (x, %s. e (S s), \<Union>x\<in>v. SS x)) upds"
  let ?INV = "%l s. I l s \<and> postList ?upds l s" 
    
  have "lesvars upds \<inter> support I = {}" using Awhile(4) unfolding aha by auto
    
  let ?P="lesvars upds \<union> varacom ({A} WHILE b DO C) "
  let ?z="SOME z::lvname. z \<notin> ?P"
  have "finite ?P" apply(auto simp del: aha)   by (fact Awhile(6))  
  hence "\<exists>z. z\<notin>?P"  using infinite_UNIV_listI
    using ex_new_if_finite by metis
  hence znP: "?z \<notin> ?P" by (rule someI_ex) 
  from znP have   
      zny:  "?z \<notin> lesvars upds"
    and zI:   "?z \<notin> support I" 
    and blb:      "?z \<notin> varacom C" by (simp_all add: aha)
  
  from Awhile(4,6) have 23: "finite (varacom C)" 
    and  26: "finite (support I)" by (auto simp add: finite_subset aha) 
   
  have "\<forall>l s.  pre C I  l s \<longrightarrow> I l (postQ C s)"
    apply(rule Awhile(1)[THEN conjunct2, THEN conjunct1])
            apply(fact)+ subgoal using  Is apply auto done
    subgoal using Awhile(8) LVE_LVE  by (metis subsetD sup.cobounded2)
            apply fact using Awhile(10) LVE_LVE by blast 
  hence step: "\<And>l s. pre C I  l s \<Longrightarrow> I l (postQ C s)" by simp
   
  have fua: "lesvars ?upds = lesvars upds"
    by force
  let ?upds' = "(?z,E,Es) # ?upds"
  
  show ?case
  proof (safe, goal_cases)
    case (2 l s)
    from 2 have A: "I l s" unfolding aha by(simp) 
    then have I: "I l s" by simp
        
    { fix n
    have "E s = n \<Longrightarrow> I l s \<Longrightarrow> Q l (postQ ({A} WHILE b DO C) s)"
    proof (induct n arbitrary: s l rule: less_induct)
      case (less n)
      then show ?case 
      proof (cases "bval b s")
        case True
        with less IQ2 have "pre C I l s" and S: "S s = S (postQ C s) on ?LV" and t: "1 + preT C E s + time C s \<le> E s" by auto
        with step have I': "I l (postQ C s)" and "1 + E (postQ C s) + time C s \<le> E s" using TQ by auto
        with less have "E (postQ C s) < n" by auto    
        with less(1) I' have "Q l (postQ ({A} WHILE b DO C) (postQ C s))" by auto
        with step show ?thesis using S  apply simp using Awhile(7)
          by (metis (no_types, lifting) LV_LV SUP_union contra_subsetD sup.boundedE)
      next
        case False
        with pre2 less(3) have "Q l s" "S s = s  on ?LV" by auto
        then show ?thesis apply simp using Awhile(7)
          by (metis (no_types, lifting) LV_LV SUP_union contra_subsetD sup.boundedE)  
      qed
    qed
    }
    with I show "Q l (postQ ({A} WHILE b DO C) s)" by simp   
  next
    case 1    
   have g: "\<And>e. e \<circ> S = (%s. e (S s)) " by auto
   
   
   have "lesvars ?upds' \<inter> varacom C = {}"
          using yC blb by(auto)
        
        have z: "(fst \<circ> (\<lambda>(x, e, v). (x, \<lambda>s. e (S s), \<Union>x\<in>v. SS x))) = fst" by(auto)
        have "distinct (map fst ?upds')"
          using Awhile(5) zny by (auto simp add: z)
          
        have klae: "\<And>s1 s2 A B. B \<subseteq> A \<Longrightarrow> s1 = s2 on A \<Longrightarrow> s1 = s2 on B" by auto
        from Awhile(8) Awhile(9) have gl: "\<And>a b c s1 s2. (a,b,c) \<in> set upds \<Longrightarrow> s1 = s2 on c \<Longrightarrow> b s1 = b s2" 
          by fast
        have CombALL: " \<turnstile>\<^sub>1 {\<lambda>l s. pre C I l s \<and> preList ?upds' C l s}
                  strip C
                  { time C \<Down> \<lambda>l s. I l s \<and> postList ?upds' l s}   \<and>
(\<forall>l s. pre C I l s \<longrightarrow> I l (postQ C s)) \<and> K4 ((SOME z. z \<notin> lesvars upds \<union> varacom ({A} WHILE b DO C), E, Es) # map (\<lambda>(x, e, v). (x, \<lambda>s. e (S s), \<Union>x\<in>v. SS x)) upds) Is C I "
          apply(rule Awhile.IH[where upds="?upds'" ] )
                 apply (fact)+  
          
          subgoal apply safe using Is apply blast
            using Is apply blast done
          subgoal
            using Is Es apply auto   
             apply(simp_all add: postListpostSet2, safe) 
          proof (goal_cases)
            case (1 l s1 s2 x e v)
            from 1(5,6) have i: "l x = e (S s1)" by auto
            from  Awhile(10) 1(6) have vLC: "v \<subseteq> LVE" by auto
            have st: "(\<Union>y\<in>v. SS y) \<subseteq> (\<Union>y\<in>LVE. SS y)" using vLC by blast
            also have "\<dots> \<subseteq> (\<Union>y\<in>LVE. funStar SS y)" using LVE_LV2 by blast
            finally have st: "(\<Union>y\<in>v. SS y) \<subseteq>  Es \<union> (\<Union>y\<in>LVE. funStar SS y)" by blast
            have ii: "e (S s1) = e (S s2)"
              apply(rule gl)
               apply fact
              apply(rule Ssc)
              apply fact
              using st 1(3) by blast
            from i ii show ?case by simp 
          next
            case (2 l s1 s2 x e v)
            from 2(5,6) have i: "l x = e (S s2)" by auto
            from  Awhile(10) 2(6) have vLC: "v \<subseteq> LVE" by auto
            have st: "(\<Union>y\<in>v. SS y) \<subseteq> (\<Union>y\<in>LVE. SS y)" using vLC by blast
            also have "\<dots> \<subseteq> (\<Union>y\<in>LVE. funStar SS y)" using LVE_LV2 by blast
            finally have st: "(\<Union>y\<in>v. SS y) \<subseteq>  Es \<union> (\<Union>y\<in>LVE. funStar SS y)" by blast
            have ii: "e (S s1) = e (S s2)"
              apply(rule gl)
               apply fact
              apply(rule Ssc)
              apply fact
              using st 2(3) by blast
            from i ii show ?case by simp 
          qed  apply(auto)
          subgoal using Es by auto
          subgoal apply(rule gl) apply(simp) using Ss Awhile(10) by fastforce
          subgoal using Awhile(10) LVE_LV2 by  blast       
          done
        from this[THEN conjunct2, THEN conjunct2] have
          K: "K C Is I" and K3: "K3 ?upds' C I" and Kt: "\<forall>s1 s2. s1 = s2 on kdeps C \<longrightarrow> time C s1 = time C s2" unfolding K4_def by auto
        show "K4 upds LVQ ({A} WHILE b DO C) Q" 
          unfolding K4_def apply safe
          subgoal using K unfolding K_def aha using Is by auto 
          subgoal using K3 unfolding K3_def K2_def aha apply auto
            subgoal for x e v apply (rule gl) apply simp apply(rule Ssc)  using Awhile(10) 
               apply fast  apply blast done done
          subgoal using Kt Es unfolding aha by auto
          done
   
    show ?case  
      
      apply(simp add: aha) 
      apply(rule conseq_old[where P="?INV" and e'=E and Q="\<lambda>l s. ?INV l s \<and> ~ bval b s"])
      defer 
    proof (goal_cases)
      case 3
      show ?case  apply(rule exI[where x=1]) apply(auto)[1] apply(simp only: postList_preList[symmetric] ) apply (auto)[1]
        by(simp only:  g) 
    next
      case 2 (* post condition is satisfied after exiting the loop *)
      show ?case
      proof (safe, goal_cases)
        case (1 l s)
        then show ?case using pre by auto
      next
        case (2 l s)
        from Awhile(8) have Aw7: "\<And>l s1 s2. s1 = s2 on LVE \<Longrightarrow>  postList upds l s1 = postList upds l s2" by auto
        have "postList (map (\<lambda>(x, e, v). (x, \<lambda>s. e (S s), \<Union>x\<in>v. SS x)) upds) l s =
                postList upds l (S s)" apply(induct upds) apply auto done
        also have "\<dots> = postList upds l s" using  Aw7[of "S s" s "l"] pre2 2 LV_LV
          by fast
        finally show ?case using 2(3) by simp
      qed 
    next
      case 1
      show ?case 
      proof(rule While, goal_cases)
        case 1          
        
        
        note Comb=CombALL[THEN conjunct1]
        
        show "\<turnstile>\<^sub>1 {\<lambda>l s. (I l s \<and> postList ?upds l s) \<and> bval b s \<and> preT C E s = l ?z}
         strip C {  time C \<Down> \<lambda>l s. (I l s \<and> postList ?upds l s) \<and> E s \<le> l ?z}" 
          apply(rule conseq_old)
          apply(rule exI[where x=1]) apply(simp)
            prefer 2 
        proof (rule Comb, safe, goal_cases) 
          case (2 l s)
          from IQ_in[OF 2(1)] gl Awhile(10,9)
          have y: "postList ?upds l s = 
                preList ?upds C l s" (is "?IH upds")
          proof (induct upds) 
            case (Cons a  upds')
            obtain y e v where axe: "a = (y,e,v)" using prod_cases3 by blast    
            have IH: "?IH upds'" apply(rule Cons(1))
              using Cons(2-5) by auto
            from Cons(3) axe have ke: "\<And>s1 s2. s1 = s2 on v \<Longrightarrow> e s1 = e s2"
              by fastforce
            have vLC: "v \<subseteq> LVE" using axe Cons(4) by simp
            have step: "e (S s) = e (S (postQ C s))" apply(rule ke) using Cons(2)  using vLC LV_LV 2(3) 
              by blast
            show ?case unfolding axe using IH step apply(simp) 
                apply(simp only: TQ) done
          qed simp
          from 2 show ?case by(simp add: y) 
        qed  (auto simp: inv_impl)
      next 
        show "\<forall>l s. bval b s \<and> I l s \<and> postList ?upds l s \<longrightarrow>  1 + preT C E s + time C s \<le>   E s"
        proof (clarify, goal_cases)
          case (1 l s)
          thus ?case
            using 1 IQ by auto
        qed
      next 
        show "\<forall>l s. ~bval b s \<and> I l s \<and> postList ?upds l s \<longrightarrow>  1 \<le> E s"
        proof (clarify, goal_cases)
          case (1 l s)
          with pre show ?case by auto
        qed  
      next
        have pff: "?z \<notin> lesvars ?upds" apply(simp only: fua) by fact
        have "support (\<lambda>l s. I l s \<and> postList ?upds l s) \<subseteq> support I \<union> support (postList ?upds)"
          by(rule support_and) 
        also
        have "support (postList ?upds)
          \<subseteq> lesvars ?upds"
             apply(rule support_postList) done 
        finally 
        have "support (\<lambda>l s. I l s \<and> postList ?upds l s) \<subseteq> support I \<union> lesvars ?upds"
          by blast 
        thus "?z \<notin> support (\<lambda>l s. I l s \<and> postList ?upds l s)" 
          apply(rule contra_subsetD) 
          using zI pff by(simp)
      qed
    qed 
    
  qed
qed
 

corollary vc_sound':
  assumes "vc C Q Qset {}" 
          "finite (support Q)" "finite (varacom C)"
          "\<forall>l s. P l s \<longrightarrow> pre C Q l s" 
          "\<And>s1 s2 l. s1 = s2 on Qset \<Longrightarrow> Q l s1 = Q l s2"
  shows "\<turnstile>\<^sub>1 {P} strip C {time C \<Down> Q}"
proof -
  show ?thesis
    apply(rule conseq_old)
      prefer 2 apply(rule vc_sound[where upds="[]", OF assms(1), simplified, OF assms(2-3), THEN conjunct1])      
    using assms(4,5) apply auto 
    done 
qed

corollary vc_sound'':
  assumes "vc C Q Qset {}" 
          "finite (support Q)" "finite (varacom C)"
          " (\<exists>k>0. \<forall>l s. P l s \<longrightarrow> pre C Q l s \<and> time C s \<le> k * e s)"
          "\<And>s1 s2 l. s1 = s2 on Qset \<Longrightarrow> Q l s1 = Q l s2"
  shows "\<turnstile>\<^sub>1 {P} strip C {e \<Down> Q}"
proof -
  show ?thesis
    apply(rule conseq_old)
      prefer 2 apply(rule vc_sound[where upds="[]", OF assms(1), simplified, OF assms(2-3), THEN conjunct1])      
    using assms(4,5) apply auto 
    done 
qed    

end
