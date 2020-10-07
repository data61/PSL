(*  Title:      JinjaThreads/BV/Effect.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

section \<open>Effect of Instructions on the State Type\<close>

theory Effect
imports
  JVM_SemiType
  "../JVM/JVMExceptions"
begin

locale jvm_method = prog +
  fixes mxs :: nat  
  fixes mxl\<^sub>0 :: nat   
  fixes Ts :: "ty list" 
  fixes T\<^sub>r :: ty
  fixes "is" :: "'addr instr list" 
  fixes xt :: ex_table

  fixes mxl :: nat
  defines mxl_def: "mxl \<equiv> 1+size Ts+mxl\<^sub>0"

text \<open>Program counter of successor instructions:\<close>
primrec succs :: "'addr instr \<Rightarrow> ty\<^sub>i \<Rightarrow> pc \<Rightarrow> pc list"
where
  "succs (Load idx) \<tau> pc     = [pc+1]"
| "succs (Store idx) \<tau> pc    = [pc+1]"
| "succs (Push v) \<tau> pc       = [pc+1]"
| "succs (Getfield F C) \<tau> pc = [pc+1]"
| "succs (Putfield F C) \<tau> pc = [pc+1]"
| "succs (CAS F C) \<tau> pc      = [pc+1]"
| "succs (New C) \<tau> pc        = [pc+1]"
| "succs (NewArray T) \<tau> pc   = [pc+1]"
| "succs ALoad \<tau> pc          = (if (fst \<tau>)!1 = NT then [] else [pc+1])"
| "succs AStore \<tau> pc         = (if (fst \<tau>)!2 = NT then [] else [pc+1])"
| "succs ALength \<tau> pc        = (if (fst \<tau>)!0 = NT then [] else [pc+1])"
| "succs (Checkcast C) \<tau> pc  = [pc+1]"
| "succs (Instanceof T) \<tau> pc  = [pc+1]"
| "succs Pop \<tau> pc            = [pc+1]"
| "succs Dup \<tau> pc            = [pc+1]"
| "succs Swap \<tau> pc           = [pc+1]"
| "succs (BinOpInstr b) \<tau> pc = [pc+1]"
| succs_IfFalse:
  "succs (IfFalse b) \<tau> pc    = [pc+1, nat (int pc + b)]"
| succs_Goto:
  "succs (Goto b) \<tau> pc       = [nat (int pc + b)]"
| succs_Return:
  "succs Return \<tau> pc         = []"  
| succs_Invoke:
  "succs (Invoke M n) \<tau> pc   = (if (fst \<tau>)!n = NT then [] else [pc+1])"
| succs_Throw:
  "succs ThrowExc \<tau> pc          = []"
| "succs MEnter \<tau> pc         = (if (fst \<tau>)!0 = NT then [] else [pc+1])"
| "succs MExit \<tau> pc          = (if (fst \<tau>)!0 = NT then [] else [pc+1])"

text "Effect of instruction on the state type:"

fun eff\<^sub>i :: "'addr instr \<times> 'm prog \<times> ty\<^sub>i \<Rightarrow> ty\<^sub>i"
where
  eff\<^sub>i_Load:
  "eff\<^sub>i (Load n,  P, (ST, LT))          = (ok_val (LT ! n) # ST, LT)"

| eff\<^sub>i_Store:
  "eff\<^sub>i (Store n, P, (T#ST, LT))        = (ST, LT[n:= OK T])"

| eff\<^sub>i_Push:
  "eff\<^sub>i (Push v, P, (ST, LT))             = (the (typeof v) # ST, LT)"

| eff\<^sub>i_Getfield:
  "eff\<^sub>i (Getfield F C, P, (T#ST, LT))    = (fst (snd (field P C F)) # ST, LT)"

| eff\<^sub>i_Putfield:
  "eff\<^sub>i (Putfield F C, P, (T\<^sub>1#T\<^sub>2#ST, LT)) = (ST,LT)"

| eff\<^sub>i_CAS:
  "eff\<^sub>i (CAS F C, P, (T\<^sub>1#T\<^sub>2#T\<^sub>3#ST, LT)) = (Boolean # ST, LT)"

| eff\<^sub>i_New:
  "eff\<^sub>i (New C, P, (ST,LT))               = (Class C # ST, LT)"

| eff\<^sub>i_NewArray:
  "eff\<^sub>i (NewArray Ty, P, (T#ST,LT))       = (Ty\<lfloor>\<rceil> # ST,LT)"

| eff\<^sub>i_ALoad:
  "eff\<^sub>i (ALoad, P, (T1#T2#ST,LT))       = (the_Array T2# ST,LT)"

| eff\<^sub>i_AStore:
  "eff\<^sub>i (AStore, P, (T1#T2#T3#ST,LT))  = (ST,LT)"

| eff\<^sub>i_ALength:
  "eff\<^sub>i (ALength, P, (T1#ST,LT))  = (Integer#ST,LT)"

| eff\<^sub>i_Checkcast:
  "eff\<^sub>i (Checkcast Ty, P, (T#ST,LT))       = (Ty # ST,LT)"

| eff\<^sub>i_Instanceof:
  "eff\<^sub>i (Instanceof Ty, P, (T#ST,LT))       = (Boolean # ST,LT)"

| eff\<^sub>i_Pop:
  "eff\<^sub>i (Pop, P, (T#ST,LT))               = (ST,LT)"

| eff\<^sub>i_Dup:
  "eff\<^sub>i (Dup, P, (T#ST,LT))               = (T#T#ST,LT)"

| eff\<^sub>i_Swap:
  "eff\<^sub>i (Swap, P, (T1#T2#ST,LT))               = (T2#T1#ST,LT)"

| eff\<^sub>i_BinOpInstr:
  "eff\<^sub>i (BinOpInstr bop, P, (T2#T1#ST,LT)) = ((THE T. P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T)#ST, LT)"

| eff\<^sub>i_IfFalse:
  "eff\<^sub>i (IfFalse b, P, (T\<^sub>1#ST,LT))        = (ST,LT)"

| eff\<^sub>i_Invoke:
  "eff\<^sub>i (Invoke M n, P, (ST,LT))          =
  (let U = fst (snd (snd (method P (the (class_type_of' (ST ! n))) M)))
   in (U # drop (n+1) ST, LT))"

| eff\<^sub>i_Goto:
  "eff\<^sub>i (Goto n, P, s)                    = s"

| eff\<^sub>i_MEnter:
  "eff\<^sub>i (MEnter, P, (T1#ST,LT))           = (ST,LT)"

| eff\<^sub>i_MExit:
  "eff\<^sub>i (MExit, P, (T1#ST,LT))            = (ST,LT)"


fun is_relevant_class :: "'addr instr \<Rightarrow> 'm prog \<Rightarrow> cname \<Rightarrow> bool" 
where
  rel_Getfield:
  "is_relevant_class (Getfield F D) = (\<lambda>P C. P \<turnstile> NullPointer \<preceq>\<^sup>* C)" 
| rel_Putfield:
  "is_relevant_class (Putfield F D) = (\<lambda>P C. P \<turnstile> NullPointer \<preceq>\<^sup>* C)" 
| rel_CAS:
  "is_relevant_class (CAS F D)      = (\<lambda>P C. P \<turnstile> NullPointer \<preceq>\<^sup>* C)" 
| rel_Checcast:
  "is_relevant_class (Checkcast T)  = (\<lambda>P C. P \<turnstile> ClassCast \<preceq>\<^sup>* C)" 
| rel_New:
  "is_relevant_class (New D)        = (\<lambda>P C. P \<turnstile> OutOfMemory \<preceq>\<^sup>* C)" 
| rel_Throw:
  "is_relevant_class ThrowExc       = (\<lambda>P C. True)"
| rel_Invoke:
  "is_relevant_class (Invoke M n)   = (\<lambda>P C. True)"
| rel_NewArray:
  "is_relevant_class (NewArray T)   = (\<lambda>P C. (P \<turnstile> OutOfMemory \<preceq>\<^sup>* C) \<or> (P \<turnstile> NegativeArraySize \<preceq>\<^sup>* C))"
| rel_ALoad:
  "is_relevant_class ALoad          = (\<lambda>P C. P \<turnstile> ArrayIndexOutOfBounds \<preceq>\<^sup>* C \<or> P \<turnstile> NullPointer \<preceq>\<^sup>* C)"
| rel_AStore:
  "is_relevant_class AStore         = (\<lambda>P C. P \<turnstile> ArrayIndexOutOfBounds \<preceq>\<^sup>* C \<or> P \<turnstile> ArrayStore \<preceq>\<^sup>* C \<or> P \<turnstile> NullPointer \<preceq>\<^sup>* C)"
| rel_ALength:
  "is_relevant_class ALength        = (\<lambda>P C. P \<turnstile> NullPointer \<preceq>\<^sup>* C)"
| rel_MEnter:
  "is_relevant_class MEnter         = (\<lambda>P C. P \<turnstile> IllegalMonitorState \<preceq>\<^sup>* C \<or> P \<turnstile> NullPointer \<preceq>\<^sup>* C)"
| rel_MExit:
  "is_relevant_class MExit          = (\<lambda>P C. P \<turnstile> IllegalMonitorState \<preceq>\<^sup>* C \<or> P \<turnstile> NullPointer \<preceq>\<^sup>* C)"
| rel_BinOp:
  "is_relevant_class (BinOpInstr bop) = binop_relevant_class bop"
| rel_default:
  "is_relevant_class i              = (\<lambda>P C. False)"

definition is_relevant_entry :: "'m prog \<Rightarrow> 'addr instr \<Rightarrow> pc \<Rightarrow> ex_entry \<Rightarrow> bool" 
where
  "is_relevant_entry P i pc e \<equiv> 
   let (f,t,C,h,d) = e 
   in (case C of None \<Rightarrow> True | \<lfloor>C'\<rfloor> \<Rightarrow> is_relevant_class i P C') \<and> pc \<in> {f..<t}"

definition relevant_entries :: "'m prog \<Rightarrow> 'addr instr \<Rightarrow> pc \<Rightarrow> ex_table \<Rightarrow> ex_table" 
where
  "relevant_entries P i pc \<equiv> filter (is_relevant_entry P i pc)"

definition xcpt_eff :: "'addr instr \<Rightarrow> 'm prog \<Rightarrow> pc \<Rightarrow> ty\<^sub>i \<Rightarrow> ex_table \<Rightarrow> (pc \<times> ty\<^sub>i') list"
where
  "xcpt_eff i P pc \<tau> et \<equiv> let (ST,LT) = \<tau> in 
  map (\<lambda>(f,t,C,h,d). (h, Some ((case C of None \<Rightarrow> Class Throwable | Some C' \<Rightarrow> Class C')#drop (size ST - d) ST, LT))) (relevant_entries P i pc et)"

definition norm_eff :: "'addr instr \<Rightarrow> 'm prog \<Rightarrow> nat \<Rightarrow> ty\<^sub>i \<Rightarrow> (pc \<times> ty\<^sub>i') list"
where "norm_eff i P pc \<tau> \<equiv> map (\<lambda>pc'. (pc',Some (eff\<^sub>i (i,P,\<tau>)))) (succs i \<tau> pc)"

definition eff :: "'addr instr \<Rightarrow> 'm prog \<Rightarrow> pc \<Rightarrow> ex_table \<Rightarrow> ty\<^sub>i' \<Rightarrow> (pc \<times> ty\<^sub>i') list"
where
  "eff i P pc et t \<equiv>
  case t of           
    None \<Rightarrow> []          
  | Some \<tau> \<Rightarrow> (norm_eff i P pc \<tau>) @ (xcpt_eff i P pc \<tau> et)"


lemma eff_None:
  "eff i P pc xt None = []"
by (simp add: eff_def)

lemma eff_Some:
  "eff i P pc xt (Some \<tau>) = norm_eff i P pc \<tau> @ xcpt_eff i P pc \<tau> xt"
by (simp add: eff_def)

(* FIXME: getfield, \<exists>T D. P \<turnstile> C sees F:T in D \<and> .. *)

text "Conditions under which eff is applicable:"

fun app\<^sub>i :: "'addr instr \<times> 'm prog \<times> pc \<times> nat \<times> ty \<times> ty\<^sub>i \<Rightarrow> bool"
where
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
    (\<exists>T\<^sub>f fm. P \<turnstile> C sees F:T\<^sub>f (fm) in C \<and> P \<turnstile> T \<le> Class C)"
| app\<^sub>i_Putfield:
  "app\<^sub>i (Putfield F C, P, pc, mxs, T\<^sub>r, (T\<^sub>1#T\<^sub>2#ST, LT)) = 
    (\<exists>T\<^sub>f fm. P \<turnstile> C sees F:T\<^sub>f (fm) in C \<and> P \<turnstile> T\<^sub>2 \<le> (Class C) \<and> P \<turnstile> T\<^sub>1 \<le> T\<^sub>f)" 
| app\<^sub>i_CAS:
  "app\<^sub>i (CAS F C, P, pc, mxs, T\<^sub>r, (T\<^sub>3#T\<^sub>2#T\<^sub>1#ST, LT)) = 
    (\<exists>T\<^sub>f fm. P \<turnstile> C sees F:T\<^sub>f (fm) in C \<and> volatile fm \<and> P \<turnstile> T\<^sub>1 \<le> Class C \<and> P \<turnstile> T\<^sub>2 \<le> T\<^sub>f \<and> P \<turnstile> T\<^sub>3 \<le> T\<^sub>f)" 
| app\<^sub>i_New:
  "app\<^sub>i (New C, P, pc, mxs, T\<^sub>r, (ST,LT)) = 
    (is_class P C \<and> length ST < mxs)"
| app\<^sub>i_NewArray:
  "app\<^sub>i (NewArray Ty, P, pc, mxs, T\<^sub>r, (Integer#ST,LT)) = 
    is_type P (Ty\<lfloor>\<rceil>)"
|  app\<^sub>i_ALoad:
  "app\<^sub>i (ALoad, P, pc, mxs, T\<^sub>r, (T1#T2#ST,LT)) = 
    (T1 = Integer \<and> (T2 \<noteq> NT \<longrightarrow> (\<exists>Ty. T2 = Ty\<lfloor>\<rceil>)))"
| app\<^sub>i_AStore:
  "app\<^sub>i (AStore, P, pc, mxs, T\<^sub>r, (T1#T2#T3#ST,LT)) = 
    (T2 = Integer \<and> (T3 \<noteq> NT \<longrightarrow> (\<exists>Ty. T3 = Ty\<lfloor>\<rceil>)))"
| app\<^sub>i_ALength:
  "app\<^sub>i (ALength, P, pc, mxs, T\<^sub>r, (T1#ST,LT)) = 
    (T1 = NT \<or> (\<exists>Ty. T1 = Ty\<lfloor>\<rceil>))"
| app\<^sub>i_Checkcast:
  "app\<^sub>i (Checkcast Ty, P, pc, mxs, T\<^sub>r, (T#ST,LT)) = 
    (is_type P Ty)"
| app\<^sub>i_Instanceof:
  "app\<^sub>i (Instanceof Ty, P, pc, mxs, T\<^sub>r, (T#ST,LT)) = 
    (is_type P Ty \<and> is_refT T)"
| app\<^sub>i_Pop:
  "app\<^sub>i (Pop, P, pc, mxs, T\<^sub>r, (T#ST,LT)) = 
    True"
| app\<^sub>i_Dup:
  "app\<^sub>i (Dup, P, pc, mxs, T\<^sub>r, (T#ST,LT)) = 
    (Suc (length ST) < mxs)"
| app\<^sub>i_Swap:
  "app\<^sub>i (Swap, P, pc, mxs, T\<^sub>r, (T1#T2#ST,LT)) = True"
| app\<^sub>i_BinOpInstr:
  "app\<^sub>i (BinOpInstr bop, P, pc, mxs, T\<^sub>r, (T2#T1#ST,LT)) = (\<exists>T. P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T)"
| app\<^sub>i_IfFalse:
  "app\<^sub>i (IfFalse b, P, pc, mxs, T\<^sub>r, (Boolean#ST,LT)) = 
    (0 \<le> int pc + b)"
| app\<^sub>i_Goto:
  "app\<^sub>i (Goto b, P, pc, mxs, T\<^sub>r, s) =  (0 \<le> int pc + b)"
| app\<^sub>i_Return:
  "app\<^sub>i (Return, P, pc, mxs, T\<^sub>r, (T#ST,LT)) = (P \<turnstile> T \<le> T\<^sub>r)"
| app\<^sub>i_Throw:
  "app\<^sub>i (ThrowExc, P, pc, mxs, T\<^sub>r, (T#ST,LT)) = 
    (T = NT \<or> (\<exists>C. T = Class C \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable))"
| app\<^sub>i_Invoke:
  "app\<^sub>i (Invoke M n, P, pc, mxs, T\<^sub>r, (ST,LT)) =
    (n < length ST \<and> 
    (ST!n \<noteq> NT \<longrightarrow>
      (\<exists>C D Ts T m. class_type_of' (ST ! n) = \<lfloor>C\<rfloor> \<and> P \<turnstile> C sees M:Ts \<rightarrow> T = m in D \<and> P \<turnstile> rev (take n ST) [\<le>] Ts)))"
| app\<^sub>i_MEnter:
  "app\<^sub>i (MEnter,P, pc,mxs,T\<^sub>r,(T#ST,LT)) = (is_refT T)"
| app\<^sub>i_MExit:
  "app\<^sub>i (MExit,P, pc,mxs,T\<^sub>r,(T#ST,LT)) = (is_refT T)"
| app\<^sub>i_default:
  "app\<^sub>i (i,P, pc,mxs,T\<^sub>r,s) = False"


definition xcpt_app :: "'addr instr \<Rightarrow> 'm prog \<Rightarrow> pc \<Rightarrow> nat \<Rightarrow> ex_table \<Rightarrow> ty\<^sub>i \<Rightarrow> bool"
where
  "xcpt_app i P pc mxs xt \<tau> \<equiv> \<forall>(f,t,C,h,d) \<in> set (relevant_entries P i pc xt). (case C of None \<Rightarrow> True | Some C' \<Rightarrow> is_class P C') \<and> d \<le> size (fst \<tau>) \<and> d < mxs"

definition app :: "'addr instr \<Rightarrow> 'm prog \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ex_table \<Rightarrow> ty\<^sub>i' \<Rightarrow> bool"
where
  "app i P mxs T\<^sub>r pc mpc xt t \<equiv> case t of None \<Rightarrow> True | Some \<tau> \<Rightarrow> 
  app\<^sub>i (i,P,pc,mxs,T\<^sub>r,\<tau>) \<and> xcpt_app i P pc mxs xt \<tau> \<and> 
  (\<forall>(pc',\<tau>') \<in> set (eff i P pc xt t). pc' < mpc)"


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
  assumes "\<And>l l' ST LT. P (l#l'#ST,LT)"
  shows "P s"
  apply(rule length_cases2; (rule assms)?)
  subgoal for l ST LT by(cases ST; clarsimp simp: assms)
  done

lemma length_cases4:
  assumes "\<And>LT. P ([],LT)"
  assumes "\<And>l LT. P ([l],LT)"
  assumes "\<And>l l' LT. P ([l,l'],LT)"
  assumes "\<And>l l' l'' ST LT. P (l#l'#l''#ST,LT)"
  shows "P s"
  apply(rule length_cases3; (rule assms)?)
  subgoal for l l' ST LT by(cases ST; clarsimp simp: assms)
  done

lemma length_cases5:
  assumes "\<And>LT. P ([],LT)"
  assumes "\<And>l LT. P ([l],LT)"
  assumes "\<And>l l' LT. P ([l,l'],LT)"
  assumes "\<And>l l' l'' LT. P ([l,l',l''],LT)"
  assumes "\<And>l l' l'' l''' ST LT. P (l#l'#l''#l'''#ST,LT)"
  shows "P s"
  apply(rule length_cases4; (rule assms)?)
  subgoal for l l' l'' ST LT by(cases ST; clarsimp simp: assms)
  done

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
 (\<exists> oT vT ST LT fm. s = (oT#ST, LT) \<and> 
  P \<turnstile> C sees F:vT (fm) in C \<and> P \<turnstile> oT \<le> (Class C))"
  by (rule length_cases2 [of _ s]) auto

lemma appPutField[simp]:
"app\<^sub>i (Putfield F C,P,pc,mxs,T\<^sub>r,s) = 
 (\<exists> vT vT' oT ST LT fm. s = (vT#oT#ST, LT) \<and>
  P \<turnstile> C sees F:vT' (fm) in C \<and> P \<turnstile> oT \<le> (Class C) \<and> P \<turnstile> vT \<le> vT')"
  by (rule length_cases4 [of _ s], auto)

lemma appCAS[simp]:
"app\<^sub>i (CAS F C, P, pc, mxs, T\<^sub>r, s) =
  (\<exists> T1 T2 T3 T' ST LT fm. s = (T3 # T2 # T1 # ST, LT) \<and>
  P \<turnstile> C sees F:T' (fm) in C \<and> volatile fm \<and> P \<turnstile> T1 \<le> Class C \<and> P \<turnstile> T2 \<le> T' \<and> P \<turnstile> T3 \<le> T')"
  by(rule length_cases4[of _ s]) auto

lemma appNew[simp]:
  "app\<^sub>i (New C,P,pc,mxs,T\<^sub>r,s) = 
  (\<exists>ST LT. s=(ST,LT) \<and> is_class P C \<and> length ST < mxs)"
  by (cases s, simp)

lemma appNewArray[simp]:
  "app\<^sub>i (NewArray Ty,P,pc,mxs,T\<^sub>r,s) = 
  (\<exists>ST LT. s=(Integer#ST,LT) \<and> is_type P (Ty\<lfloor>\<rceil>))"
  by (cases s, simp, cases "fst s", simp)(cases "hd (fst s)", auto)

lemma appALoad[simp]:
  "app\<^sub>i (ALoad,P,pc,mxs,T\<^sub>r,s) = 
  (\<exists>T ST LT. s=(Integer#T#ST,LT) \<and> (T \<noteq> NT \<longrightarrow> (\<exists>T'.  T = T'\<lfloor>\<rceil>)))"
proof -
  obtain ST LT where [simp]: "s = (ST, LT)" by (cases s)
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

lemma appAStore[simp]:
  "app\<^sub>i (AStore,P,pc,mxs,T\<^sub>r,s) = 
  (\<exists>T U ST LT. s=(T#Integer#U#ST,LT) \<and> (U \<noteq> NT \<longrightarrow> (\<exists>T'. U = T'\<lfloor>\<rceil>)))"
proof -
  obtain ST LT where [simp]: "s = (ST, LT)" by (cases s)
  have "ST = [] \<or> (\<exists>T. ST = [T]) \<or> (\<exists>T\<^sub>1 T\<^sub>2. ST = [T\<^sub>1, T\<^sub>2]) \<or> (\<exists>T1 T2 T3 ST'. ST = T1 # T2 # T3 # ST')"
    by (cases ST, auto, case_tac list, auto, case_tac lista, auto)
  moreover
  { assume "ST = []" hence ?thesis by simp }
  moreover
  { fix T assume "ST = [T]" hence ?thesis by(simp) }
  moreover
  { fix T1 T2 assume "ST = [T1, T2]" hence ?thesis by simp }
  moreover
  { fix T1 T2 T3 ST' assume "ST = T1 # T2 # T3 # ST'" hence ?thesis by(cases T2, auto) }
  ultimately show ?thesis by blast
qed

lemma appALength[simp]:
  "app\<^sub>i (ALength,P,pc,mxs,T\<^sub>r,s) = 
  (\<exists>T ST LT. s=(T#ST,LT) \<and> (T \<noteq> NT \<longrightarrow> (\<exists>T'.  T = T'\<lfloor>\<rceil>)))"
  by (cases s, cases "fst s", simp add: app_def) (cases "hd (fst s)", auto)

lemma appCheckcast[simp]: 
  "app\<^sub>i (Checkcast Ty,P,pc,mxs,T\<^sub>r,s) =  
  (\<exists>T ST LT. s = (T#ST,LT) \<and> is_type P Ty)"
  by (cases s, cases "fst s", simp add: app_def) (cases "hd (fst s)", auto)

lemma appInstanceof[simp]: 
  "app\<^sub>i (Instanceof Ty,P,pc,mxs,T\<^sub>r,s) =  
  (\<exists>T ST LT. s = (T#ST,LT) \<and> is_type P Ty \<and> is_refT T)"
  by (cases s, cases "fst s", simp add: app_def) (cases "hd (fst s)", auto)

lemma app\<^sub>iPop[simp]: 
"app\<^sub>i (Pop,P,pc,mxs,T\<^sub>r,s) = (\<exists>ts ST LT. s = (ts#ST,LT))"
  by (rule length_cases2, auto)

lemma appDup[simp]:
"app\<^sub>i (Dup,P,pc,mxs,T\<^sub>r,s) =
 (\<exists>T ST LT. s = (T#ST,LT) \<and> Suc (length ST) < mxs)"
by (cases s, cases "fst s", simp_all)

lemma app\<^sub>iSwap[simp]: 
"app\<^sub>i (Swap,P,pc,mxs,T\<^sub>r,s) = (\<exists>T1 T2 ST LT. s = (T1#T2#ST,LT))"
by(rule length_cases4) auto

lemma appBinOp[simp]:
"app\<^sub>i (BinOpInstr bop,P,pc,mxs,T\<^sub>r,s) = (\<exists>T1 T2 ST LT T. s = (T2 # T1 # ST, LT) \<and> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T)"
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
    hence ?thesis by simp
  }
  ultimately show ?thesis by blast
qed

lemma appIfFalse [simp]:
"app\<^sub>i (IfFalse b,P,pc,mxs,T\<^sub>r,s) = 
  (\<exists>ST LT. s = (Boolean#ST,LT) \<and> 0 \<le> int pc + b)"
  apply (rule length_cases2)
  apply simp
  apply (case_tac l) 
  apply auto
  done

lemma appReturn[simp]:
"app\<^sub>i (Return,P,pc,mxs,T\<^sub>r,s) = (\<exists>T ST LT. s = (T#ST,LT) \<and> P \<turnstile> T \<le> T\<^sub>r)" 
  by (rule length_cases2, auto)

lemma appThrow[simp]:
  "app\<^sub>i (ThrowExc,P,pc,mxs,T\<^sub>r,s) = (\<exists>T ST LT. s=(T#ST,LT) \<and> (T = NT \<or> (\<exists>C. T = Class C \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable)))"
  by (rule length_cases2, auto)  

lemma appMEnter[simp]:
  "app\<^sub>i (MEnter,P,pc,mxs,T\<^sub>r,s) = (\<exists>T ST LT. s=(T#ST,LT) \<and> is_refT T)"
  by (rule length_cases2, auto)  

lemma appMExit[simp]:
  "app\<^sub>i (MExit,P,pc,mxs,T\<^sub>r,s) = (\<exists>T ST LT. s=(T#ST,LT) \<and> is_refT T)"
  by (rule length_cases2, auto)

lemma effNone: 
  "(pc', s') \<in> set (eff i P pc et None) \<Longrightarrow> s' = None"
  by (auto simp add: eff_def xcpt_eff_def norm_eff_def)


lemma relevant_entries_append [simp]:
  "relevant_entries P i pc (xt @ xt') = relevant_entries P i pc xt @ relevant_entries P i pc xt'"
  by (unfold relevant_entries_def) simp

lemma xcpt_app_append [iff]:
  "xcpt_app i P pc mxs (xt@xt') \<tau> = (xcpt_app i P pc mxs xt \<tau> \<and> xcpt_app i P pc mxs xt' \<tau>)"
unfolding xcpt_app_def by force

lemma xcpt_eff_append [simp]:
  "xcpt_eff i P pc \<tau> (xt@xt') = xcpt_eff i P pc \<tau> xt @ xcpt_eff i P pc \<tau> xt'"
 by (unfold xcpt_eff_def, cases \<tau>) simp

lemma app_append [simp]:
  "app i P pc T mxs mpc (xt@xt') \<tau> = (app i P pc T mxs mpc xt \<tau> \<and> app i P pc T mxs mpc xt' \<tau>)"
  by (unfold app_def eff_def) auto


subsection \<open>Code generator setup\<close>

declare list_all2_Nil [code]
declare list_all2_Cons [code]

lemma eff\<^sub>i_BinOpInstr_code:
  "eff\<^sub>i (BinOpInstr bop, P, (T2#T1#ST,LT)) = (Predicate.the (WTrt_binop_i_i_i_i_o P T1 bop T2) # ST, LT)"
by(simp add: the_WTrt_binop_code)

lemmas eff\<^sub>i_code[code] =
  eff\<^sub>i_Load eff\<^sub>i_Store eff\<^sub>i_Push eff\<^sub>i_Getfield eff\<^sub>i_Putfield eff\<^sub>i_New eff\<^sub>i_NewArray eff\<^sub>i_ALoad
  eff\<^sub>i_AStore eff\<^sub>i_ALength eff\<^sub>i_Checkcast eff\<^sub>i_Instanceof eff\<^sub>i_Pop eff\<^sub>i_Dup eff\<^sub>i_Swap eff\<^sub>i_BinOpInstr_code
  eff\<^sub>i_IfFalse eff\<^sub>i_Invoke eff\<^sub>i_Goto eff\<^sub>i_MEnter eff\<^sub>i_MExit

lemma app\<^sub>i_Getfield_code:
  "app\<^sub>i (Getfield F C, P, pc, mxs, T\<^sub>r, (T#ST, LT)) \<longleftrightarrow>
  Predicate.holds (Predicate.bind (sees_field_i_i_i_o_o_i P C F C) (\<lambda>T. Predicate.single ())) \<and> P \<turnstile> T \<le> Class C"
apply(clarsimp simp add: Predicate.bind_def Predicate.single_def holds_eq eval_sees_field_i_i_i_o_i_conv)
done
 
lemma app\<^sub>i_Putfield_code:
  "app\<^sub>i (Putfield F C, P, pc, mxs, T\<^sub>r, (T\<^sub>1#T\<^sub>2#ST, LT)) \<longleftrightarrow>
   P \<turnstile> T\<^sub>2 \<le> (Class C) \<and>
   Predicate.holds (Predicate.bind (sees_field_i_i_i_o_o_i P C F C) (\<lambda>(T, fm). if P \<turnstile> T\<^sub>1 \<le> T then Predicate.single () else bot))"
by (auto simp add: holds_eq eval_sees_field_i_i_i_o_i_conv split: if_splits)

lemma app\<^sub>i_CAS_code:
  "app\<^sub>i (CAS F C, P, pc, mxs, T\<^sub>r, (T\<^sub>3#T\<^sub>2#T\<^sub>1#ST, LT)) \<longleftrightarrow>
   P \<turnstile> T\<^sub>1 \<le> Class C \<and>
  Predicate.holds (Predicate.bind (sees_field_i_i_i_o_o_i P C F C) (\<lambda>(T, fm). if P \<turnstile> T\<^sub>2 \<le> T \<and> P \<turnstile> T\<^sub>3 \<le> T \<and> volatile fm then Predicate.single () else bot))"
by(auto simp add: holds_eq eval_sees_field_i_i_i_o_i_conv)

lemma app\<^sub>i_ALoad_code:
  "app\<^sub>i (ALoad, P, pc, mxs, T\<^sub>r, (T1#T2#ST,LT)) = 
   (T1 = Integer \<and> (case T2 of Ty\<lfloor>\<rceil> \<Rightarrow> True | NT \<Rightarrow> True | _ \<Rightarrow> False))"
by(simp add: split: ty.split)

lemma app\<^sub>i_AStore_code:
  "app\<^sub>i (AStore, P, pc, mxs, T\<^sub>r, (T1#T2#T3#ST,LT)) = 
  (T2 = Integer \<and> (case T3 of Ty\<lfloor>\<rceil> \<Rightarrow> True | NT \<Rightarrow> True | _ \<Rightarrow> False))"
by(simp add: split: ty.split)

lemma app\<^sub>i_ALength_code:
  "app\<^sub>i (ALength, P, pc, mxs, T\<^sub>r, (T1#ST,LT)) = 
   (case T1 of Ty\<lfloor>\<rceil> \<Rightarrow> True | NT \<Rightarrow> True | _ \<Rightarrow> False)"
by(simp add: split: ty.split)

lemma app\<^sub>i_BinOpInstr_code:
  "app\<^sub>i (BinOpInstr bop, P, pc, mxs, T\<^sub>r, (T2#T1#ST,LT)) = 
   Predicate.holds (Predicate.bind (WTrt_binop_i_i_i_i_o P T1 bop T2) (\<lambda>T. Predicate.single ()))"
by (auto simp add: holds_eq eval_WTrt_binop_i_i_i_i_o)

lemma app\<^sub>i_Invoke_code:
  "app\<^sub>i (Invoke M n, P, pc, mxs, T\<^sub>r, (ST,LT)) =
  (n < length ST \<and> 
  (ST!n \<noteq> NT \<longrightarrow>
     (case class_type_of' (ST ! n) of Some C \<Rightarrow> 
         Predicate.holds (Predicate.bind (Method_i_i_i_o_o_o_o P C M) 
                                          (\<lambda>(Ts, _). if P \<turnstile> rev (take n ST) [\<le>] Ts then Predicate.single () else bot))
      | _ \<Rightarrow> False)))"
proof -
  have bind_Ex: "\<And>P f. Predicate.bind P f = Predicate.Pred (\<lambda>x. (\<exists>y. Predicate.eval P y \<and> Predicate.eval (f y) x))"
    by (rule pred_eqI) auto
  thus ?thesis
    by (auto simp add: bind_Ex Predicate.single_def holds_eq eval_Method_i_i_i_o_o_o_o_conv split: ty.split)
qed

lemma app\<^sub>i_Throw_code:
  "app\<^sub>i (ThrowExc, P, pc, mxs, T\<^sub>r, (T#ST,LT)) = 
  (case T of NT \<Rightarrow> True | Class C \<Rightarrow> P \<turnstile> C \<preceq>\<^sup>* Throwable | _ \<Rightarrow> False)"
by(simp split: ty.split)

lemmas app\<^sub>i_code [code] =
  app\<^sub>i_Load app\<^sub>i_Store app\<^sub>i_Push
  app\<^sub>i_Getfield_code app\<^sub>i_Putfield_code app\<^sub>i_CAS_code
  app\<^sub>i_New app\<^sub>i_NewArray
  app\<^sub>i_ALoad_code app\<^sub>i_AStore_code app\<^sub>i_ALength_code
  app\<^sub>i_Checkcast app\<^sub>i_Instanceof
  app\<^sub>i_Pop app\<^sub>i_Dup app\<^sub>i_Swap app\<^sub>i_BinOpInstr_code app\<^sub>i_IfFalse app\<^sub>i_Goto
  app\<^sub>i_Return app\<^sub>i_Throw_code app\<^sub>i_Invoke_code app\<^sub>i_MEnter app\<^sub>i_MExit
  app\<^sub>i_default

end
