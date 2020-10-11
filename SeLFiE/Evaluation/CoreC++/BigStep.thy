(*  Title:       CoreC++
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Based on the Jinja theory J/BigStep.thy by Tobias Nipkow
*)

section \<open>Big Step Semantics\<close>

theory BigStep
imports Syntax State
begin


subsection \<open>The rules\<close>

inductive
  eval :: "prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
          ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  and evals :: "prog \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool"
           ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) [\<Rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  for P :: prog
where

  New:
  "\<lbrakk> new_Addr h = Some a; h' = h(a\<mapsto>(C,Collect (init_obj P C))) \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>new C,(h,l)\<rangle> \<Rightarrow> \<langle>ref (a,[C]),(h',l)\<rangle>"

| NewFail:
  "new_Addr h = None \<Longrightarrow>
  P,E \<turnstile> \<langle>new C, (h,l)\<rangle> \<Rightarrow> \<langle>THROW OutOfMemory,(h,l)\<rangle>"

| StaticUpCast:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^sub>1\<rangle>; P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a,Ds),s\<^sub>1\<rangle>"

| StaticDownCast:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs@[C]@Cs'),s\<^sub>1\<rangle>
   \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs@[C]),s\<^sub>1\<rangle>"

| StaticCastNull:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>"

| StaticCastFail:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^sub>1\<rangle>; \<not> P \<turnstile> (last Cs) \<preceq>\<^sup>* C; C \<notin> set Cs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW ClassCast,s\<^sub>1\<rangle>"

| StaticCastThrow:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| StaticUpDynCast:(* path uniqueness not necessary for type proof but for determinism *)
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a,Cs),s\<^sub>1\<rangle>; P \<turnstile> Path last Cs to C unique;
    P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a,Ds),s\<^sub>1\<rangle>"

| StaticDownDynCast:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs@[C]@Cs'),s\<^sub>1\<rangle>
   \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs@[C]),s\<^sub>1\<rangle>"

| DynCast: (* path uniqueness not necessary for type proof but for determinism *)
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>; h a = Some(D,S);
    P \<turnstile> Path D to C via Cs'; P \<turnstile> Path D to C unique \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),(h,l)\<rangle>"

| DynCastNull:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>"

| DynCastFail: (* fourth premise not necessary for type proof but for determinism *)
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle>\<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>; h a = Some(D,S); \<not> P \<turnstile> Path D to C unique;
    \<not> P \<turnstile> Path last Cs to C unique; C \<notin> set Cs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,(h,l)\<rangle>"

| DynCastThrow:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| Val:
  "P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>"

| BinOp:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v\<^sub>2,s\<^sub>2\<rangle>; 
    binop(bop,v\<^sub>1,v\<^sub>2) = Some v \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle>\<Rightarrow>\<langle>Val v,s\<^sub>2\<rangle>"

| BinOpThrow1:
  "P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle>"

| BinOpThrow2:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>2\<rangle>"

| Var:
  "l V = Some v \<Longrightarrow>
  P,E \<turnstile> \<langle>Var V,(h,l)\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>"

| LAss:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>; E V = Some T;
     P \<turnstile> T casts v to v'; l' = l(V\<mapsto>v') \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>V:=e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v',(h,l')\<rangle>"

| LAssThrow:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>V:=e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| FAcc:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),(h,l)\<rangle>; h a = Some(D,S);
     Ds = Cs'@\<^sub>pCs; (Ds,fs) \<in> S; fs F = Some v \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>"

| FAccNull:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>1\<rangle>" 

| FAccThrow:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| FAss:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(D,S); P \<turnstile> (last Cs') has least F:T via Cs; P \<turnstile> T casts v to v';
     Ds = Cs'@\<^sub>pCs; (Ds,fs) \<in> S; fs' = fs(F\<mapsto>v'); 
     S' = S - {(Ds,fs)} \<union> {(Ds,fs')}; h\<^sub>2' = h\<^sub>2(a\<mapsto>(D,S'))\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v',(h\<^sub>2',l\<^sub>2)\<rangle>"

| FAssNull:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>;  P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>2\<rangle>" 

| FAssThrow1:
  "P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| FAssThrow2:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"

| CallObjThrow:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>Call e Copt M es,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| CallParamsThrow:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs @ throw ex # es',s\<^sub>2\<rangle> \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> \<langle>Call e Copt M es,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"

| Call:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^sub>1\<rangle>;  P,E \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,S);  P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds;
     P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs'; length vs = length pns; 
     P \<turnstile> Ts Casts vs to vs'; l\<^sub>2' = [this\<mapsto>Ref (a,Cs'), pns[\<mapsto>]vs'];
     new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body   | _  \<Rightarrow> body);  
     P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> \<langle>new_body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>2)\<rangle>"

| StaticCall:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^sub>1\<rangle>;  P,E \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>;
     P \<turnstile> Path (last Cs) to C unique; P \<turnstile> Path (last Cs) to C via Cs'';
     P \<turnstile> C has least M = (Ts,T,pns,body) via Cs'; Ds = (Cs@\<^sub>pCs'')@\<^sub>pCs';
     length vs = length pns; P \<turnstile> Ts Casts vs to vs'; 
     l\<^sub>2' = [this\<mapsto>Ref (a,Ds), pns[\<mapsto>]vs'];
     P,E(this\<mapsto>Class(last Ds), pns[\<mapsto>]Ts) \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>(C::)M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>2)\<rangle>"

| CallNull:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>;  P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Call e Copt M es,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>2\<rangle>"

| Block:
  "\<lbrakk>P,E(V \<mapsto> T) \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0,l\<^sub>0(V:=None))\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1,l\<^sub>1)\<rangle> \<rbrakk> \<Longrightarrow>
  P,E \<turnstile> \<langle>{V:T; e\<^sub>0},(h\<^sub>0,l\<^sub>0)\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1,l\<^sub>1(V:=l\<^sub>0 V))\<rangle>"

| Seq:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>0;;e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"

| SeqThrow:
  "P,E \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^sub>0;;e\<^sub>1,s\<^sub>0\<rangle>\<Rightarrow>\<langle>throw e,s\<^sub>1\<rangle>"

| CondT:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle>"

| CondF:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle>"

| CondThrow:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| WhileF:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,s\<^sub>1\<rangle>"

| WhileT:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>2\<rangle>; 
     P,E \<turnstile> \<langle>while (e) c,s\<^sub>2\<rangle> \<Rightarrow> \<langle>e\<^sub>3,s\<^sub>3\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>3,s\<^sub>3\<rangle>"

| WhileCondThrow:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle> throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| WhileBodyThrow:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"

| Throw:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref r,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw r,s\<^sub>1\<rangle>"

| ThrowNull:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>1\<rangle>"

| ThrowThrow:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| Nil:
  "P,E \<turnstile> \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>[],s\<rangle>"

| Cons:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>es',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e#es,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>Val v # es',s\<^sub>2\<rangle>"

| ConsThrow:
  "P,E \<turnstile> \<langle>e, s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e', s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e#es, s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>throw e' # es, s\<^sub>1\<rangle>"

lemmas eval_evals_induct = eval_evals.induct [split_format (complete)]
  and eval_evals_inducts = eval_evals.inducts [split_format (complete)]

inductive_cases eval_cases [cases set]:
 "P,E \<turnstile> \<langle>new C,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>Cast C e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>Var V,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>V:=e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e\<bullet>M(es),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e\<bullet>(C::)M(es),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>{V:T;e\<^sub>1},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e\<^sub>1;;e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  
inductive_cases evals_cases [cases set]:
 "P,E \<turnstile> \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e#es,s\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>"



subsection \<open>Final expressions\<close>

definition final :: "expr \<Rightarrow> bool" where
  "final e  \<equiv>  (\<exists>v. e = Val v) \<or> (\<exists>r. e = Throw r)"

definition finals:: "expr list \<Rightarrow> bool" where
  "finals es  \<equiv>  (\<exists>vs. es = map Val vs) \<or> (\<exists>vs r es'. es = map Val vs @ Throw r # es')"

lemma [simp]: "final(Val v)"
by(simp add:final_def)

lemma [simp]: "final(throw e) = (\<exists>r. e = ref r)"
by(simp add:final_def)

lemma finalE: "\<lbrakk> final e;  \<And>v. e = Val v \<Longrightarrow> Q;  \<And>r. e = Throw r \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by(auto simp:final_def)

lemma [iff]: "finals []"
by(simp add:finals_def)

lemma [iff]: "finals (Val v # es) = finals es"

apply(clarsimp simp add:finals_def)
apply(rule iffI)
 apply(erule disjE)
  apply simp
 apply(rule disjI2)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastforce
apply(erule disjE)
 apply (rule disjI1)
 apply clarsimp
apply(rule disjI2)
apply clarsimp
apply(rule_tac x = "v#vs" in exI)
apply simp
done


lemma finals_app_map[iff]: "finals (map Val vs @ es) = finals es"
by(induct_tac vs, auto)

lemma [iff]: "finals (map Val vs)"
using finals_app_map[of vs "[]"]by(simp)

lemma [iff]: "finals (throw e # es) = (\<exists>r. e = ref r)"

apply(simp add:finals_def)
apply(rule iffI)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastforce
apply fastforce
done


lemma not_finals_ConsI: "\<not> final e \<Longrightarrow> \<not> finals(e#es)"
 
apply(auto simp add:finals_def final_def)
apply(case_tac vs)
apply auto
done


lemma eval_final: "P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> final e'"
 and evals_final: "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> finals es'"
by(induct rule:eval_evals.inducts, simp_all)


lemma eval_lcl_incr: "P,E \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>1,l\<^sub>1)\<rangle> \<Longrightarrow> dom l\<^sub>0 \<subseteq> dom l\<^sub>1"
 and evals_lcl_incr: "P,E \<turnstile> \<langle>es,(h\<^sub>0,l\<^sub>0)\<rangle> [\<Rightarrow>] \<langle>es',(h\<^sub>1,l\<^sub>1)\<rangle> \<Longrightarrow> dom l\<^sub>0 \<subseteq> dom l\<^sub>1"
by (induct rule:eval_evals_inducts) (auto simp del:fun_upd_apply)


text\<open>Only used later, in the small to big translation, but is already a
good sanity check:\<close>

lemma eval_finalId:  "final e \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e,s\<rangle>"
by (erule finalE) (fastforce intro: eval_evals.intros)+


lemma eval_finalsId:
assumes finals: "finals es" shows "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>"

  using finals
proof (induct es type: list)
  case Nil show ?case by (rule eval_evals.intros)
next
  case (Cons e es)
  have hyp: "finals es \<Longrightarrow> P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>"
   and finals: "finals (e # es)" by fact+
  show "P,E \<turnstile> \<langle>e # es,s\<rangle> [\<Rightarrow>] \<langle>e # es,s\<rangle>"
  proof cases
    assume "final e"
    thus ?thesis
    proof (cases rule: finalE)
      fix v assume e: "e = Val v"
      have "P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>" by (simp add: eval_finalId)
      moreover from finals e have "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>" by(fast intro:hyp)
      ultimately have "P,E \<turnstile> \<langle>Val v#es,s\<rangle> [\<Rightarrow>] \<langle>Val v#es,s\<rangle>"
        by (rule eval_evals.intros)
      with e show ?thesis by simp
    next
      fix a assume e: "e = Throw a"
      have "P,E \<turnstile> \<langle>Throw a,s\<rangle> \<Rightarrow> \<langle>Throw a,s\<rangle>" by (simp add: eval_finalId)
      hence "P,E \<turnstile> \<langle>Throw a#es,s\<rangle> [\<Rightarrow>] \<langle>Throw a#es,s\<rangle>" by (rule eval_evals.intros)
      with e show ?thesis by simp
    qed
  next
    assume "\<not> final e"
    with not_finals_ConsI finals have False by blast
    thus ?thesis ..
  qed
qed


lemma
eval_preserves_obj:"P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> (\<And>S. h a = Some(D,S) 
  \<Longrightarrow> \<exists>S'. h' a = Some(D,S'))"
and evals_preserves_obj:"P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<Rightarrow>] \<langle>es',(h',l')\<rangle> 
\<Longrightarrow> (\<And>S. h a = Some(D,S) \<Longrightarrow> \<exists>S'. h' a = Some(D,S'))"
by(induct rule:eval_evals_inducts)(fastforce dest:new_Addr_SomeD)+

end
