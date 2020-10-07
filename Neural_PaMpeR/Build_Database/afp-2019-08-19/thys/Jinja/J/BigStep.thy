(*  Title:      Jinja/J/BigStep.thy

    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

section \<open>Big Step Semantics\<close>

theory BigStep imports Expr State begin

inductive
  eval :: "J_prog \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
          ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  and evals :: "J_prog \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool"
           ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) [\<Rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  for P :: J_prog
where

  New:
  "\<lbrakk> new_Addr h = Some a; P \<turnstile> C has_fields FDTs; h' = h(a\<mapsto>(C,init_fields FDTs)) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C,(h,l)\<rangle> \<Rightarrow> \<langle>addr a,(h',l)\<rangle>"

| NewFail:
  "new_Addr h = None \<Longrightarrow>
  P \<turnstile> \<langle>new C, (h,l)\<rangle> \<Rightarrow> \<langle>THROW OutOfMemory,(h,l)\<rangle>"

| Cast:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l)\<rangle>; h a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l)\<rangle>"

| CastNull:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>"

| CastFail:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle>\<Rightarrow> \<langle>addr a,(h,l)\<rangle>; h a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW ClassCast,(h,l)\<rangle>"

| CastThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| Val:
  "P \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>"

| BinOp:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v\<^sub>2,s\<^sub>2\<rangle>; binop(bop,v\<^sub>1,v\<^sub>2) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle>\<Rightarrow>\<langle>Val v,s\<^sub>2\<rangle>"

| BinOpThrow1:
  "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle>"

| BinOpThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>2\<rangle>"

| Var:
  "l V = Some v \<Longrightarrow>
  P \<turnstile> \<langle>Var V,(h,l)\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>"

| LAss:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>; l' = l(V\<mapsto>v) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>V:=e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,(h,l')\<rangle>"

| LAssThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>V:=e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| FAcc:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l)\<rangle>; h a = Some(C,fs); fs(F,D) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>"

| FAccNull:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>1\<rangle>"

| FAccThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| FAss:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs); fs' = fs((F,D)\<mapsto>v); h\<^sub>2' = h\<^sub>2(a\<mapsto>(C,fs')) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,(h\<^sub>2',l\<^sub>2)\<rangle>"

| FAssNull:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>2\<rangle>"

| FAssThrow1:
  "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| FAssThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"

| CallObjThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| CallParamsThrow:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs @ throw ex # es',s\<^sub>2\<rangle> \<rbrakk>
   \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"

| CallNull:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>2\<rangle>"

| Call:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs);  P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D;
     length vs = length pns;  l\<^sub>2' = [this\<mapsto>Addr a, pns[\<mapsto>]vs];
     P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>2)\<rangle>"

| Block:
  "P \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0,l\<^sub>0(V:=None))\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1,l\<^sub>1)\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>{V:T; e\<^sub>0},(h\<^sub>0,l\<^sub>0)\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1,l\<^sub>1(V:=l\<^sub>0 V))\<rangle>"

| Seq:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>0;;e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"

| SeqThrow:
  "P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>0;;e\<^sub>1,s\<^sub>0\<rangle>\<Rightarrow>\<langle>throw e,s\<^sub>1\<rangle>"

| CondT:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle>"

| CondF:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle>"

| CondThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| WhileF:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,s\<^sub>1\<rangle>"

| WhileT:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>2\<rangle>; P \<turnstile> \<langle>while (e) c,s\<^sub>2\<rangle> \<Rightarrow> \<langle>e\<^sub>3,s\<^sub>3\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>3,s\<^sub>3\<rangle>"

| WhileCondThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle> throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| WhileBodyThrow:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>\<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"

| Throw:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,s\<^sub>1\<rangle>"

| ThrowNull:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>1\<rangle>"

| ThrowThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| Try:
  "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>try e\<^sub>1 catch(C V) e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>"

| TryCatch:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,l\<^sub>1)\<rangle>;  h\<^sub>1 a = Some(D,fs);  P \<turnstile> D \<preceq>\<^sup>* C;
     P \<turnstile> \<langle>e\<^sub>2,(h\<^sub>1,l\<^sub>1(V\<mapsto>Addr a))\<rangle> \<Rightarrow> \<langle>e\<^sub>2',(h\<^sub>2,l\<^sub>2)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try e\<^sub>1 catch(C V) e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',(h\<^sub>2,l\<^sub>2(V:=l\<^sub>1 V))\<rangle>"

| TryThrow:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,l\<^sub>1)\<rangle>;  h\<^sub>1 a = Some(D,fs);  \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try e\<^sub>1 catch(C V) e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,l\<^sub>1)\<rangle>"

| Nil:
  "P \<turnstile> \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>[],s\<rangle>"

| Cons:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>es',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e#es,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>Val v # es',s\<^sub>2\<rangle>"

| ConsThrow:
  "P \<turnstile> \<langle>e, s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e', s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e#es, s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>throw e' # es, s\<^sub>1\<rangle>"

(*<*)
lemmas eval_evals_induct = eval_evals.induct [split_format (complete)]
  and eval_evals_inducts = eval_evals.inducts [split_format (complete)]

inductive_cases eval_cases [cases set]:
 "P \<turnstile> \<langle>Cast C e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>V:=e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<bullet>F{D},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<bullet>M{D}(es),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>{V:T;e\<^sub>1},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<^sub>1;;e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>try e\<^sub>1 catch(C V) e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 
inductive_cases evals_cases [cases set]:
 "P \<turnstile> \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e#es,s\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>"
(*>*) 


subsection"Final expressions"

definition final :: "'a exp \<Rightarrow> bool"
where
  "final e  \<equiv>  (\<exists>v. e = Val v) \<or> (\<exists>a. e = Throw a)"

definition finals:: "'a exp list \<Rightarrow> bool"
where
  "finals es  \<equiv>  (\<exists>vs. es = map Val vs) \<or> (\<exists>vs a es'. es = map Val vs @ Throw a # es')"

lemma [simp]: "final(Val v)"
(*<*)by(simp add:final_def)(*>*)

lemma [simp]: "final(throw e) = (\<exists>a. e = addr a)"
(*<*)by(simp add:final_def)(*>*)

lemma finalE: "\<lbrakk> final e;  \<And>v. e = Val v \<Longrightarrow> R;  \<And>a. e = Throw a \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
(*<*)by(auto simp:final_def)(*>*)

lemma [iff]: "finals []"
(*<*)by(simp add:finals_def)(*>*)

lemma [iff]: "finals (Val v # es) = finals es"
(*<*)
apply(clarsimp simp add: finals_def)
apply(rule iffI)
 apply(erule disjE)
  apply simp
 apply(rule disjI2)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastforce
apply(erule disjE)
 apply clarsimp
apply(rule disjI2)
apply clarsimp
apply(rule_tac x = "v#vs" in exI)
apply simp
done
(*>*)

lemma finals_app_map[iff]: "finals (map Val vs @ es) = finals es"
(*<*)by(induct_tac vs, auto)(*>*)

lemma [iff]: "finals (map Val vs)"
(*<*)using finals_app_map[of vs "[]"]by(simp)(*>*)

lemma [iff]: "finals (throw e # es) = (\<exists>a. e = addr a)"
(*<*)
apply(simp add:finals_def)
apply(rule iffI)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastforce
apply clarsimp
apply(rule_tac x = "[]" in exI)
apply simp
done
(*>*)

lemma not_finals_ConsI: "\<not> final e \<Longrightarrow> \<not> finals(e#es)"
 (*<*)
apply(clarsimp simp add:finals_def final_def)
apply(case_tac vs)
apply auto
done
(*>*)


lemma eval_final: "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> final e'"
 and evals_final: "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> finals es'"
(*<*)by(induct rule:eval_evals.inducts, simp_all)(*>*)


lemma eval_lcl_incr: "P \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>1,l\<^sub>1)\<rangle> \<Longrightarrow> dom l\<^sub>0 \<subseteq> dom l\<^sub>1"
 and evals_lcl_incr: "P \<turnstile> \<langle>es,(h\<^sub>0,l\<^sub>0)\<rangle> [\<Rightarrow>] \<langle>es',(h\<^sub>1,l\<^sub>1)\<rangle> \<Longrightarrow> dom l\<^sub>0 \<subseteq> dom l\<^sub>1"
(*<*)
proof (induct rule: eval_evals_inducts)
  case BinOp show ?case by(rule subset_trans)(rule BinOp.hyps)+
next
  case Call thus ?case
    by(simp del: fun_upd_apply) 
next
  case Seq show ?case by(rule subset_trans)(rule Seq.hyps)+
next
  case CondT show ?case by(rule subset_trans)(rule CondT.hyps)+
next
  case CondF show ?case by(rule subset_trans)(rule CondF.hyps)+
next
  case WhileT thus ?case by(blast)
next
  case TryCatch thus ?case by(clarsimp simp:dom_def split:if_split_asm) blast
next
  case Cons show ?case by(rule subset_trans)(rule Cons.hyps)+
next
  case Block thus ?case by(auto simp del:fun_upd_apply)
qed auto
(*>*)

text\<open>Only used later, in the small to big translation, but is already a
good sanity check:\<close>

lemma eval_finalId:  "final e \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e,s\<rangle>"
(*<*)by (erule finalE) (iprover intro: eval_evals.intros)+(*>*)


lemma eval_finalsId:
assumes finals: "finals es" shows "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>"
(*<*)
  using finals
proof (induct es type: list)
  case Nil show ?case by (rule eval_evals.intros)
next
  case (Cons e es)
  have hyp: "finals es \<Longrightarrow> P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>"
   and finals: "finals (e # es)" by fact+
  show "P \<turnstile> \<langle>e # es,s\<rangle> [\<Rightarrow>] \<langle>e # es,s\<rangle>"
  proof cases
    assume "final e"
    thus ?thesis
    proof (cases rule: finalE)
      fix v assume e: "e = Val v"
      have "P \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>" by (simp add: eval_finalId)
      moreover from finals e have "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>" by(fast intro:hyp)
      ultimately have "P \<turnstile> \<langle>Val v#es,s\<rangle> [\<Rightarrow>] \<langle>Val v#es,s\<rangle>"
        by (rule eval_evals.intros)
      with e show ?thesis by simp
    next
      fix a assume e: "e = Throw a"
      have "P \<turnstile> \<langle>Throw a,s\<rangle> \<Rightarrow> \<langle>Throw a,s\<rangle>" by (simp add: eval_finalId)
      hence "P \<turnstile> \<langle>Throw a#es,s\<rangle> [\<Rightarrow>] \<langle>Throw a#es,s\<rangle>" by (rule eval_evals.intros)
      with e show ?thesis by simp
    qed
  next
    assume "\<not> final e"
    with not_finals_ConsI finals have False by blast
    thus ?thesis ..
  qed
qed
(*>*)


theorem eval_hext: "P \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> h \<unlhd> h'"
and evals_hext:  "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<Rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> h \<unlhd> h'"
(*<*)
proof (induct rule: eval_evals_inducts)
  case New thus ?case
    by(fastforce intro!: hext_new intro:LeastI simp:new_Addr_def
                split:if_split_asm simp del:fun_upd_apply)
next
  case BinOp thus ?case by (fast elim!:hext_trans)
next
  case BinOpThrow2 thus ?case by(fast elim!: hext_trans)
next
  case FAss thus ?case
    by(auto simp:sym[THEN hext_upd_obj] simp del:fun_upd_apply
            elim!: hext_trans)
next
  case FAssNull thus ?case by (fast elim!:hext_trans)
next
  case FAssThrow2 thus ?case by (fast elim!:hext_trans)
next
  case CallParamsThrow thus ?case by(fast elim!: hext_trans)
next
  case CallNull thus ?case by(fast elim!: hext_trans)
next
  case Call thus ?case by(fast elim!: hext_trans)
next
  case Seq thus ?case by(fast elim!: hext_trans)
next
  case CondT thus ?case by(fast elim!: hext_trans)
next
  case CondF thus ?case by(fast elim!: hext_trans)
next
  case WhileT thus ?case by(fast elim!: hext_trans)
next
  case WhileBodyThrow thus ?case by (fast elim!: hext_trans)
next
  case TryCatch thus ?case  by(fast elim!: hext_trans)
next
  case Cons thus ?case by (fast intro: hext_trans)
qed auto
(*>*)


end
