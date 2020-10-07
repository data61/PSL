(*  Title:      HOL/MicroJava/BV/Effect.thy
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

section \<open>Effect of Instructions on the State Type\<close>

theory Effect
imports JVM_SemiType "../JVM/JVMExceptions"
begin

\<comment> \<open>FIXME\<close>
locale prog =
  fixes P :: "'a prog"

locale jvm_method = prog +
  fixes mxs :: nat  
  fixes mxl\<^sub>0 :: nat   
  fixes Ts :: "ty list" 
  fixes T\<^sub>r :: ty
  fixes "is" :: "instr list" 
  fixes xt :: ex_table

  fixes mxl :: nat
  defines mxl_def: "mxl \<equiv> 1+size Ts+mxl\<^sub>0"

text \<open>Program counter of successor instructions:\<close>
primrec succs :: "instr \<Rightarrow> ty\<^sub>i \<Rightarrow> pc \<Rightarrow> pc list" where
  "succs (Load idx) \<tau> pc     = [pc+1]"
| "succs (Store idx) \<tau> pc    = [pc+1]"
| "succs (Push v) \<tau> pc       = [pc+1]"
| "succs (Getfield F C) \<tau> pc = [pc+1]"
| "succs (Putfield F C) \<tau> pc = [pc+1]"
| "succs (New C) \<tau> pc        = [pc+1]"
| "succs (Checkcast C) \<tau> pc  = [pc+1]"
| "succs Pop \<tau> pc            = [pc+1]"
| "succs IAdd \<tau> pc           = [pc+1]"
| "succs CmpEq \<tau> pc          = [pc+1]"
| succs_IfFalse:
    "succs (IfFalse b) \<tau> pc    = [pc+1, nat (int pc + b)]"
| succs_Goto:
    "succs (Goto b) \<tau> pc       = [nat (int pc + b)]"
| succs_Return:
    "succs Return \<tau> pc         = []"  
| succs_Invoke:
    "succs (Invoke M n) \<tau> pc   = (if (fst \<tau>)!n = NT then [] else [pc+1])"
| succs_Throw:
    "succs Throw \<tau> pc          = []"

text "Effect of instruction on the state type:"

fun the_class:: "ty \<Rightarrow> cname" where
  "the_class (Class C) = C"

fun eff\<^sub>i :: "instr \<times> 'm prog \<times> ty\<^sub>i \<Rightarrow> ty\<^sub>i" where
  eff\<^sub>i_Load:
    "eff\<^sub>i (Load n,  P, (ST, LT))          = (ok_val (LT ! n) # ST, LT)"
| eff\<^sub>i_Store:
    "eff\<^sub>i (Store n, P, (T#ST, LT))        = (ST, LT[n:= OK T])"
| eff\<^sub>i_Push:
    "eff\<^sub>i (Push v, P, (ST, LT))             = (the (typeof v) # ST, LT)"
| eff\<^sub>i_Getfield:
    "eff\<^sub>i (Getfield F C, P, (T#ST, LT))    = (snd (field P C F) # ST, LT)"
| eff\<^sub>i_Putfield:
   "eff\<^sub>i (Putfield F C, P, (T\<^sub>1#T\<^sub>2#ST, LT)) = (ST,LT)"
| eff\<^sub>i_New:
   "eff\<^sub>i (New C, P, (ST,LT))               = (Class C # ST, LT)"
| eff\<^sub>i_Checkcast:
   "eff\<^sub>i (Checkcast C, P, (T#ST,LT))       = (Class C # ST,LT)"
| eff\<^sub>i_Pop:
   "eff\<^sub>i (Pop, P, (T#ST,LT))               = (ST,LT)"
| eff\<^sub>i_IAdd:
   "eff\<^sub>i (IAdd, P,(T\<^sub>1#T\<^sub>2#ST,LT))           = (Integer#ST,LT)"
| eff\<^sub>i_CmpEq:
   "eff\<^sub>i (CmpEq, P, (T\<^sub>1#T\<^sub>2#ST,LT))         = (Boolean#ST,LT)"
| eff\<^sub>i_IfFalse:
   "eff\<^sub>i (IfFalse b, P, (T\<^sub>1#ST,LT))        = (ST,LT)"
| eff\<^sub>i_Invoke:
   "eff\<^sub>i (Invoke M n, P, (ST,LT))          =
    (let C = the_class (ST!n); (D,Ts,T\<^sub>r,b) = method P C M
     in (T\<^sub>r # drop (n+1) ST, LT))"
| eff\<^sub>i_Goto:
   "eff\<^sub>i (Goto n, P, s)                    = s"

fun is_relevant_class :: "instr \<Rightarrow> 'm prog \<Rightarrow> cname \<Rightarrow> bool" where
  rel_Getfield:
    "is_relevant_class (Getfield F D) = (\<lambda>P C. P \<turnstile> NullPointer \<preceq>\<^sup>* C)" 
| rel_Putfield:
    "is_relevant_class (Putfield F D) = (\<lambda>P C. P \<turnstile> NullPointer \<preceq>\<^sup>* C)" 
| rel_Checcast:
    "is_relevant_class (Checkcast D)  = (\<lambda>P C. P \<turnstile> ClassCast \<preceq>\<^sup>* C)" 
| rel_New:
    "is_relevant_class (New D)        = (\<lambda>P C. P \<turnstile> OutOfMemory \<preceq>\<^sup>* C)" 
| rel_Throw:
    "is_relevant_class Throw          = (\<lambda>P C. True)"
| rel_Invoke:
    "is_relevant_class (Invoke M n)   = (\<lambda>P C. True)"
| rel_default:
    "is_relevant_class i              = (\<lambda>P C. False)"

definition is_relevant_entry :: "'m prog \<Rightarrow> instr \<Rightarrow> pc \<Rightarrow> ex_entry \<Rightarrow> bool" where
  "is_relevant_entry P i pc e \<longleftrightarrow> (let (f,t,C,h,d) = e in is_relevant_class i P C \<and> pc \<in> {f..<t})"

definition relevant_entries :: "'m prog \<Rightarrow> instr \<Rightarrow> pc \<Rightarrow> ex_table \<Rightarrow> ex_table" where
  "relevant_entries P i pc = filter (is_relevant_entry P i pc)"

definition xcpt_eff :: "instr \<Rightarrow> 'm prog \<Rightarrow> pc \<Rightarrow> ty\<^sub>i 
               \<Rightarrow> ex_table \<Rightarrow> (pc \<times> ty\<^sub>i') list" where    
  "xcpt_eff i P pc \<tau> et = (let (ST,LT) = \<tau> in 
  map (\<lambda>(f,t,C,h,d). (h, Some (Class C#drop (size ST - d) ST, LT))) (relevant_entries P i pc et))"

definition norm_eff :: "instr \<Rightarrow> 'm prog \<Rightarrow> nat \<Rightarrow> ty\<^sub>i \<Rightarrow> (pc \<times> ty\<^sub>i') list" where
  "norm_eff i P pc \<tau> = map (\<lambda>pc'. (pc',Some (eff\<^sub>i (i,P,\<tau>)))) (succs i \<tau> pc)"

definition eff :: "instr \<Rightarrow> 'm prog \<Rightarrow> pc \<Rightarrow> ex_table \<Rightarrow> ty\<^sub>i' \<Rightarrow> (pc \<times> ty\<^sub>i') list" where
  "eff i P pc et t = (case t of           
    None \<Rightarrow> []          
  | Some \<tau> \<Rightarrow> (norm_eff i P pc \<tau>) @ (xcpt_eff i P pc \<tau> et))"


lemma eff_None:
  "eff i P pc xt None = []"
by (simp add: eff_def)

lemma eff_Some:
  "eff i P pc xt (Some \<tau>) = norm_eff i P pc \<tau> @ xcpt_eff i P pc \<tau> xt"
by (simp add: eff_def)

(* FIXME: getfield, \<exists>T D. P \<turnstile> C sees F:T in D \<and> .. *)

text "Conditions under which eff is applicable:"

fun app\<^sub>i :: "instr \<times> 'm prog \<times> pc \<times> nat \<times> ty \<times> ty\<^sub>i \<Rightarrow> bool" where
  app\<^sub>i_Load:
    "app\<^sub>i (Load n, P, pc, mxs, T\<^sub>r, (ST,LT)) = 
    (n < length LT \<and> LT ! n \<noteq> Err \<and> length ST < mxs)"
| app\<^sub>i_Store:
    "app\<^sub>i (Store n, P, pc, mxs, T\<^sub>r, (T#ST, LT)) = 
    (n < length LT)"
| app\<^sub>i_Push:
    "app\<^sub>i (Push v, P, pc, mxs, T\<^sub>r, (ST,LT)) = 
     (length ST < mxs \<and> typeof v \<noteq> None)"
| app\<^sub>i_Getfield:
    "app\<^sub>i (Getfield F C, P, pc, mxs, T\<^sub>r, (T#ST, LT)) = 
    (\<exists>T\<^sub>f. P \<turnstile> C sees F:T\<^sub>f in C \<and> P \<turnstile> T \<le> Class C)"
| app\<^sub>i_Putfield:
    "app\<^sub>i (Putfield F C, P, pc, mxs, T\<^sub>r, (T\<^sub>1#T\<^sub>2#ST, LT)) = 
    (\<exists>T\<^sub>f. P \<turnstile> C sees F:T\<^sub>f in C \<and> P \<turnstile> T\<^sub>2 \<le> (Class C) \<and> P \<turnstile> T\<^sub>1 \<le> T\<^sub>f)" 
| app\<^sub>i_New:
    "app\<^sub>i (New C, P, pc, mxs, T\<^sub>r, (ST,LT)) = 
    (is_class P C \<and> length ST < mxs)"
| app\<^sub>i_Checkcast:
    "app\<^sub>i (Checkcast C, P, pc, mxs, T\<^sub>r, (T#ST,LT)) = 
    (is_class P C \<and> is_refT T)"
| app\<^sub>i_Pop:
    "app\<^sub>i (Pop, P, pc, mxs, T\<^sub>r, (T#ST,LT)) = 
    True"
| app\<^sub>i_IAdd:
    "app\<^sub>i (IAdd, P, pc, mxs, T\<^sub>r, (T\<^sub>1#T\<^sub>2#ST,LT)) = (T\<^sub>1 = T\<^sub>2 \<and> T\<^sub>1 = Integer)"
| app\<^sub>i_CmpEq:
    "app\<^sub>i (CmpEq, P, pc, mxs, T\<^sub>r, (T\<^sub>1#T\<^sub>2#ST,LT)) =
    (T\<^sub>1 = T\<^sub>2 \<or> is_refT T\<^sub>1 \<and> is_refT T\<^sub>2)"
| app\<^sub>i_IfFalse:
    "app\<^sub>i (IfFalse b, P, pc, mxs, T\<^sub>r, (Boolean#ST,LT)) = 
    (0 \<le> int pc + b)"
| app\<^sub>i_Goto:
    "app\<^sub>i (Goto b, P, pc, mxs, T\<^sub>r, s) = 
    (0 \<le> int pc + b)"
| app\<^sub>i_Return:
    "app\<^sub>i (Return, P, pc, mxs, T\<^sub>r, (T#ST,LT)) = 
    (P \<turnstile> T \<le> T\<^sub>r)"
| app\<^sub>i_Throw:
    "app\<^sub>i (Throw, P, pc, mxs, T\<^sub>r, (T#ST,LT)) = 
    is_refT T"
| app\<^sub>i_Invoke:
    "app\<^sub>i (Invoke M n, P, pc, mxs, T\<^sub>r, (ST,LT)) =
    (n < length ST \<and> 
    (ST!n \<noteq> NT \<longrightarrow>
      (\<exists>C D Ts T m. ST!n = Class C \<and> P \<turnstile> C sees M:Ts \<rightarrow> T = m in D \<and>
                    P \<turnstile> rev (take n ST) [\<le>] Ts)))"
  
| app\<^sub>i_default:
    "app\<^sub>i (i,P, pc,mxs,T\<^sub>r,s) = False"


definition xcpt_app :: "instr \<Rightarrow> 'm prog \<Rightarrow> pc \<Rightarrow> nat \<Rightarrow> ex_table \<Rightarrow> ty\<^sub>i \<Rightarrow> bool" where
  "xcpt_app i P pc mxs xt \<tau> \<longleftrightarrow> (\<forall>(f,t,C,h,d) \<in> set (relevant_entries P i pc xt). is_class P C \<and> d \<le> size (fst \<tau>) \<and> d < mxs)"

definition app :: "instr \<Rightarrow> 'm prog \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ex_table \<Rightarrow> ty\<^sub>i' \<Rightarrow> bool" where
  "app i P mxs T\<^sub>r pc mpc xt t = (case t of None \<Rightarrow> True | Some \<tau> \<Rightarrow> 
  app\<^sub>i (i,P,pc,mxs,T\<^sub>r,\<tau>) \<and> xcpt_app i P pc mxs xt \<tau> \<and> 
  (\<forall>(pc',\<tau>') \<in> set (eff i P pc xt t). pc' < mpc))"


lemma app_Some:
  "app i P mxs T\<^sub>r pc mpc xt (Some \<tau>) = 
  (app\<^sub>i (i,P,pc,mxs,T\<^sub>r,\<tau>) \<and> xcpt_app i P pc mxs xt \<tau> \<and> 
  (\<forall>(pc',s') \<in> set (eff i P pc xt (Some \<tau>)). pc' < mpc))"
by (simp add: app_def)

locale eff = jvm_method +
  fixes eff\<^sub>i and app\<^sub>i and eff and app 
  fixes norm_eff and xcpt_app and xcpt_eff

  fixes mpc
  defines "mpc \<equiv> size is"

  defines "eff\<^sub>i i \<tau> \<equiv> Effect.eff\<^sub>i (i,P,\<tau>)"
  notes eff\<^sub>i_simps [simp] = Effect.eff\<^sub>i.simps [where P = P, folded eff\<^sub>i_def]

  defines "app\<^sub>i i pc \<tau> \<equiv> Effect.app\<^sub>i (i, P, pc, mxs, T\<^sub>r, \<tau>)"
  notes app\<^sub>i_simps [simp] = Effect.app\<^sub>i.simps [where P=P and mxs=mxs and T\<^sub>r=T\<^sub>r, folded app\<^sub>i_def]

  defines "xcpt_eff i pc \<tau> \<equiv> Effect.xcpt_eff i P pc \<tau> xt"
  notes xcpt_eff = Effect.xcpt_eff_def [of _ P _ _ xt, folded xcpt_eff_def]

  defines "norm_eff i pc \<tau> \<equiv> Effect.norm_eff i P pc \<tau>"
  notes norm_eff = Effect.norm_eff_def [of _ P, folded norm_eff_def eff\<^sub>i_def]

  defines "eff i pc \<equiv> Effect.eff i P pc xt"
  notes eff = Effect.eff_def [of _ P  _ xt, folded eff_def norm_eff_def xcpt_eff_def]

  defines "xcpt_app i pc \<tau> \<equiv> Effect.xcpt_app i P pc mxs xt \<tau>"
  notes xcpt_app = Effect.xcpt_app_def [of _ P _ mxs xt, folded xcpt_app_def]

  defines "app i pc \<equiv> Effect.app i P mxs T\<^sub>r pc mpc xt"
  notes app = Effect.app_def [of _ P mxs T\<^sub>r _ mpc xt, folded app_def xcpt_app_def app\<^sub>i_def eff_def]


lemma length_cases2:
  assumes "\<And>LT. P ([],LT)"
  assumes "\<And>l ST LT. P (l#ST,LT)"
  shows "P s"
  by (cases s, cases "fst s") (auto intro!: assms)


lemma length_cases3:
  assumes "\<And>LT. P ([],LT)"
  assumes "\<And>l LT. P ([l],LT)"
  assumes "\<And>l ST LT. P (l#ST,LT)"
  shows "P s"
(*<*)
proof -
  obtain xs LT where s: "s = (xs,LT)" by (cases s)
  show ?thesis
  proof (cases xs)
    case Nil with assms s show ?thesis by simp
  next
    fix l xs' assume "xs = l#xs'"
    with assms s show ?thesis by simp
  qed
qed
(*>*)

lemma length_cases4:
  assumes "\<And>LT. P ([],LT)"
  assumes "\<And>l LT. P ([l],LT)"
  assumes "\<And>l l' LT. P ([l,l'],LT)"
  assumes "\<And>l l' ST LT. P (l#l'#ST,LT)"
  shows "P s"
(*<*)
proof -
  obtain xs LT where s: "s = (xs,LT)" by (cases s)
  show ?thesis
  proof (cases xs)
    case Nil with assms s show ?thesis by simp
  next
    fix l xs' assume xs: "xs = l#xs'"
    thus ?thesis
    proof (cases xs')
      case Nil with assms s xs show ?thesis by simp
    next
      fix l' ST assume "xs' = l'#ST"
     with assms s xs show ?thesis by simp
    qed
  qed
qed
(*>*)

text \<open>
\medskip
simp rules for @{term app}
\<close>
lemma appNone[simp]: "app i P mxs T\<^sub>r pc mpc et None = True" 
  by (simp add: app_def)


lemma appLoad[simp]:
"app\<^sub>i (Load idx, P, T\<^sub>r, mxs, pc, s) = (\<exists>ST LT. s = (ST,LT) \<and> idx < length LT \<and> LT!idx \<noteq> Err \<and> length ST < mxs)"
  by (cases s, simp)

lemma appStore[simp]:
"app\<^sub>i (Store idx,P,pc,mxs,T\<^sub>r,s) = (\<exists>ts ST LT. s = (ts#ST,LT) \<and> idx < length LT)"
  by (rule length_cases2, auto)

lemma appPush[simp]:
"app\<^sub>i (Push v,P,pc,mxs,T\<^sub>r,s) =
 (\<exists>ST LT. s = (ST,LT) \<and> length ST < mxs \<and> typeof v \<noteq> None)"
  by (cases s, simp)

lemma appGetField[simp]:
"app\<^sub>i (Getfield F C,P,pc,mxs,T\<^sub>r,s) = 
 (\<exists> oT vT ST LT. s = (oT#ST, LT) \<and> 
  P \<turnstile> C sees F:vT in C \<and> P \<turnstile> oT \<le> (Class C))"
  by (rule length_cases2 [of _ s]) auto

lemma appPutField[simp]:
"app\<^sub>i (Putfield F C,P,pc,mxs,T\<^sub>r,s) = 
 (\<exists> vT vT' oT ST LT. s = (vT#oT#ST, LT) \<and>
  P \<turnstile> C sees F:vT' in C \<and> P \<turnstile> oT \<le> (Class C) \<and> P \<turnstile> vT \<le> vT')"
  by (rule length_cases4 [of _ s], auto)

lemma appNew[simp]:
  "app\<^sub>i (New C,P,pc,mxs,T\<^sub>r,s) = 
  (\<exists>ST LT. s=(ST,LT) \<and> is_class P C \<and> length ST < mxs)"
  by (cases s, simp)

lemma appCheckcast[simp]: 
  "app\<^sub>i (Checkcast C,P,pc,mxs,T\<^sub>r,s) =  
  (\<exists>T ST LT. s = (T#ST,LT) \<and> is_class P C \<and> is_refT T)"
  by (cases s, cases "fst s", simp add: app_def) (cases "hd (fst s)", auto)

lemma app\<^sub>iPop[simp]: 
"app\<^sub>i (Pop,P,pc,mxs,T\<^sub>r,s) = (\<exists>ts ST LT. s = (ts#ST,LT))"
  by (rule length_cases2, auto)

lemma appIAdd[simp]:
"app\<^sub>i (IAdd,P,pc,mxs,T\<^sub>r,s) = (\<exists>ST LT. s = (Integer#Integer#ST,LT))"
(*<*)
proof -
  obtain ST LT where [simp]: "s = (ST,LT)" by (cases s)
  have "ST = [] \<or> (\<exists>T. ST = [T]) \<or> (\<exists>T\<^sub>1 T\<^sub>2 ST'. ST = T\<^sub>1#T\<^sub>2#ST')"
    by (cases ST, auto, case_tac list, auto)
  moreover
  { assume "ST = []" hence ?thesis by simp }
  moreover
  { fix T assume "ST = [T]" hence ?thesis by (cases T, auto) }
  moreover
  { fix T\<^sub>1 T\<^sub>2 ST' assume "ST = T\<^sub>1#T\<^sub>2#ST'"
    hence ?thesis by (cases T\<^sub>1, auto)
  }
  ultimately show ?thesis by blast
qed
(*>*)


lemma appIfFalse [simp]:
"app\<^sub>i (IfFalse b,P,pc,mxs,T\<^sub>r,s) = 
  (\<exists>ST LT. s = (Boolean#ST,LT) \<and> 0 \<le> int pc + b)"
(*<*)
  apply (rule length_cases2)
  apply simp
  apply (case_tac l) 
  apply auto
  done
(*>*)

lemma appCmpEq[simp]:
"app\<^sub>i (CmpEq,P,pc,mxs,T\<^sub>r,s) = 
  (\<exists>T\<^sub>1 T\<^sub>2 ST LT. s = (T\<^sub>1#T\<^sub>2#ST,LT) \<and> (\<not>is_refT T\<^sub>1 \<and> T\<^sub>2 = T\<^sub>1 \<or> is_refT T\<^sub>1 \<and> is_refT T\<^sub>2))"
  by (rule length_cases4, auto)

lemma appReturn[simp]:
"app\<^sub>i (Return,P,pc,mxs,T\<^sub>r,s) = (\<exists>T ST LT. s = (T#ST,LT) \<and> P \<turnstile> T \<le> T\<^sub>r)" 
  by (rule length_cases2, auto)

lemma appThrow[simp]:
  "app\<^sub>i (Throw,P,pc,mxs,T\<^sub>r,s) = (\<exists>T ST LT. s=(T#ST,LT) \<and> is_refT T)"
  by (rule length_cases2, auto)  

lemma effNone: 
  "(pc', s') \<in> set (eff i P pc et None) \<Longrightarrow> s' = None"
  by (auto simp add: eff_def xcpt_eff_def norm_eff_def)


text \<open>some helpers to make the specification directly executable:\<close>
lemma relevant_entries_append [simp]:
  "relevant_entries P i pc (xt @ xt') = relevant_entries P i pc xt @ relevant_entries P i pc xt'"
  by (unfold relevant_entries_def) simp

lemma xcpt_app_append [iff]:
  "xcpt_app i P pc mxs (xt@xt') \<tau> = (xcpt_app i P pc mxs xt \<tau> \<and> xcpt_app i P pc mxs xt' \<tau>)"
  by (unfold xcpt_app_def) fastforce

lemma xcpt_eff_append [simp]:
  "xcpt_eff i P pc \<tau> (xt@xt') = xcpt_eff i P pc \<tau> xt @ xcpt_eff i P pc \<tau> xt'"
 by (unfold xcpt_eff_def, cases \<tau>) simp

lemma app_append [simp]:
  "app i P pc T mxs mpc (xt@xt') \<tau> = (app i P pc T mxs mpc xt \<tau> \<and> app i P pc T mxs mpc xt' \<tau>)"
  by (unfold app_def eff_def) auto

end
