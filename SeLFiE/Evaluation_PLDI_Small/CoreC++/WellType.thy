(*  Title:       CoreC++

    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Based on the Jinja theory J/WellType.thy by Tobias Nipkow 
*)

section \<open>Well-typedness of CoreC++ expressions\<close>

theory WellType imports Syntax TypeRel begin


subsection \<open>The rules\<close>

inductive
  WT :: "[prog,env,expr     ,ty     ] \<Rightarrow> bool"
         ("_,_ \<turnstile> _ :: _"   [51,51,51]50)
  and WTs :: "[prog,env,expr list,ty list] \<Rightarrow> bool"
         ("_,_ \<turnstile> _ [::] _" [51,51,51]50)
  for P :: prog
where
  
  WTNew:
  "is_class P C \<Longrightarrow>
  P,E \<turnstile> new C :: Class C"

| WTDynCast: (* not more than one path between classes *)
  "\<lbrakk>P,E \<turnstile> e :: Class D; is_class P C;
    P \<turnstile> Path D to C unique \<or> (\<forall>Cs. \<not> P \<turnstile> Path D to C via Cs)\<rbrakk> 
  \<Longrightarrow> P,E \<turnstile> Cast C e :: Class C"

| WTStaticCast:
  "\<lbrakk>P,E \<turnstile> e :: Class D; is_class P C;
    P \<turnstile> Path D to C unique \<or> 
   (P \<turnstile> C \<preceq>\<^sup>* D \<and> (\<forall>Cs. P \<turnstile> Path C to D via Cs \<longrightarrow> Subobjs\<^sub>R P C Cs)) \<rbrakk> 
  \<Longrightarrow> P,E \<turnstile> \<lparr>C\<rparr>e :: Class C"

| WTVal:
  "typeof v = Some T \<Longrightarrow>
  P,E \<turnstile> Val v :: T"

| WTVar:
  "E V = Some T \<Longrightarrow>
  P,E \<turnstile> Var V :: T"

| WTBinOp:
  "\<lbrakk> P,E \<turnstile> e\<^sub>1 :: T\<^sub>1;  P,E \<turnstile> e\<^sub>2 :: T\<^sub>2;
     case bop of Eq \<Rightarrow> T\<^sub>1 = T\<^sub>2 \<and> T = Boolean
               | Add \<Rightarrow> T\<^sub>1 = Integer \<and> T\<^sub>2 = Integer \<and> T = Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T"

| WTLAss:
  "\<lbrakk> E V = Some T;  P,E \<turnstile> e :: T'; P \<turnstile> T' \<le> T\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> V:=e :: T"

| WTFAcc:
  "\<lbrakk> P,E \<turnstile> e :: Class C;  P \<turnstile> C has least F:T via Cs\<rbrakk> 
  \<Longrightarrow> P,E \<turnstile> e\<bullet>F{Cs} :: T"

| WTFAss:
  "\<lbrakk> P,E \<turnstile> e\<^sub>1 :: Class C;  P \<turnstile> C has least F:T via Cs; 
     P,E \<turnstile> e\<^sub>2 :: T'; P \<turnstile> T' \<le> T\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2 :: T"

| WTStaticCall:
  "\<lbrakk> P,E \<turnstile> e :: Class C'; P \<turnstile> Path C' to C unique;
     P \<turnstile> C has least M = (Ts,T,m) via Cs; P,E \<turnstile> es [::] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>(C::)M(es) :: T"

| WTCall:
  "\<lbrakk> P,E \<turnstile> e :: Class C;  P \<turnstile> C has least M = (Ts,T,m) via Cs;
     P,E \<turnstile> es [::] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>M(es) :: T" 

| WTBlock:
  "\<lbrakk> is_type P T;  P,E(V \<mapsto> T) \<turnstile> e :: T' \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> {V:T; e} :: T'"

| WTSeq:
  "\<lbrakk> P,E \<turnstile> e\<^sub>1::T\<^sub>1;  P,E \<turnstile> e\<^sub>2::T\<^sub>2 \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> e\<^sub>1;;e\<^sub>2 :: T\<^sub>2"

| WTCond:
  "\<lbrakk> P,E \<turnstile> e :: Boolean;  P,E \<turnstile> e\<^sub>1::T;  P,E \<turnstile> e\<^sub>2::T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :: T"

| WTWhile:
  "\<lbrakk> P,E \<turnstile> e :: Boolean;  P,E \<turnstile> c::T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> while (e) c :: Void"

| WTThrow:
  "P,E \<turnstile> e :: Class C  \<Longrightarrow> 
  P,E \<turnstile> throw e :: Void"


\<comment> \<open>well-typed expression lists\<close>

| WTNil:
  "P,E \<turnstile> [] [::] []"

| WTCons:
  "\<lbrakk> P,E \<turnstile> e :: T;  P,E \<turnstile> es [::] Ts \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> e#es [::] T#Ts"


declare WT_WTs.intros[intro!] WTNil[iff]

lemmas WT_WTs_induct = WT_WTs.induct [split_format (complete)]
  and WT_WTs_inducts = WT_WTs.inducts [split_format (complete)]


subsection\<open>Easy consequences\<close>

lemma [iff]: "(P,E \<turnstile> [] [::] Ts) = (Ts = [])"

apply(rule iffI)
apply (auto elim: WTs.cases)
done


lemma [iff]: "(P,E \<turnstile> e#es [::] T#Ts) = (P,E \<turnstile> e :: T \<and> P,E \<turnstile> es [::] Ts)"

apply(rule iffI)
apply (auto elim: WTs.cases)
done


lemma [iff]: "(P,E \<turnstile> (e#es) [::] Ts) =
  (\<exists>U Us. Ts = U#Us \<and> P,E \<turnstile> e :: U \<and> P,E \<turnstile> es [::] Us)"

apply(rule iffI)
apply (auto elim: WTs.cases)
done


lemma [iff]: "\<And>Ts. (P,E \<turnstile> es\<^sub>1 @ es\<^sub>2 [::] Ts) =
  (\<exists>Ts\<^sub>1 Ts\<^sub>2. Ts = Ts\<^sub>1 @ Ts\<^sub>2 \<and> P,E \<turnstile> es\<^sub>1 [::] Ts\<^sub>1 \<and> P,E \<turnstile> es\<^sub>2[::]Ts\<^sub>2)"

apply(induct es\<^sub>1 type:list)
 apply simp
apply clarsimp
apply(erule thin_rl)
apply (rule iffI)
 apply clarsimp
 apply(rule exI)+
 apply(rule conjI)
  prefer 2 apply blast
 apply simp
apply fastforce
done


lemma [iff]: "P,E \<turnstile> Val v :: T = (typeof v = Some T)"

apply(rule iffI)
apply (auto elim: WT.cases)
done


lemma [iff]: "P,E \<turnstile> Var V :: T = (E V = Some T)"

apply(rule iffI)
apply (auto elim: WT.cases)
done


lemma [iff]: "P,E \<turnstile> e\<^sub>1;;e\<^sub>2 :: T\<^sub>2 = (\<exists>T\<^sub>1. P,E \<turnstile> e\<^sub>1::T\<^sub>1 \<and> P,E \<turnstile> e\<^sub>2::T\<^sub>2)"

apply(rule iffI)
apply (auto elim: WT.cases)
done


lemma [iff]: "(P,E \<turnstile> {V:T; e} :: T') = (is_type P T \<and> P,E(V\<mapsto>T) \<turnstile> e :: T')"

apply(rule iffI)
apply (auto elim: WT.cases)
done



inductive_cases WT_elim_cases[elim!]:
  "P,E \<turnstile> new C :: T"
  "P,E \<turnstile> Cast C e :: T"
  "P,E \<turnstile> \<lparr>C\<rparr>e :: T"
  "P,E \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T"
  "P,E \<turnstile> V:= e :: T"
  "P,E \<turnstile> e\<bullet>F{Cs} :: T"
  "P,E \<turnstile> e\<bullet>F{Cs} := v :: T"
  "P,E \<turnstile> e\<bullet>M(ps) :: T"
  "P,E \<turnstile> e\<bullet>(C::)M(ps) :: T"
  "P,E \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :: T"
  "P,E \<turnstile> while (e) c :: T"
  "P,E \<turnstile> throw e :: T"



lemma wt_env_mono:
  "P,E \<turnstile> e :: T \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E' \<turnstile> e :: T)" and 
  "P,E \<turnstile> es [::] Ts \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E' \<turnstile> es [::] Ts)"

apply(induct rule: WT_WTs_inducts)
apply(simp add: WTNew)
apply(fastforce simp: WTDynCast)
apply(fastforce simp: WTStaticCast)
apply(fastforce simp: WTVal)
apply(simp add: WTVar map_le_def dom_def)
apply(fastforce simp: WTBinOp)
apply(force simp:map_le_def)
apply(fastforce simp: WTFAcc)
apply(fastforce simp: WTFAss)
apply(fastforce simp: WTCall)
apply(fastforce simp: WTStaticCall)
apply(fastforce simp: map_le_def WTBlock)
apply(fastforce simp: WTSeq)
apply(fastforce simp: WTCond)
apply(fastforce simp: WTWhile)
apply(fastforce simp: WTThrow)
apply(simp add: WTNil)
apply(simp add: WTCons)
done



lemma WT_fv: "P,E \<turnstile> e :: T \<Longrightarrow> fv e \<subseteq> dom E"
and "P,E \<turnstile> es [::] Ts \<Longrightarrow> fvs es \<subseteq> dom E"

apply(induct rule:WT_WTs.inducts)
apply(simp_all del: fun_upd_apply)
apply fast+
done

end
