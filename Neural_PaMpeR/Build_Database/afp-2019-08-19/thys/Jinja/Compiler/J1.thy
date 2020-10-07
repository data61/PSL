(*  Title:      Jinja/Compiler/J1.thy
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

chapter \<open>Compilation \label{cha:comp}\<close>

section \<open>An Intermediate Language\<close>

theory J1 imports "../J/BigStep" begin

type_synonym expr\<^sub>1 = "nat exp"
type_synonym J\<^sub>1_prog = "expr\<^sub>1 prog"
type_synonym state\<^sub>1 = "heap \<times> (val list)"

primrec
  max_vars :: "'a exp \<Rightarrow> nat"
  and max_varss :: "'a exp list \<Rightarrow> nat"
where
  "max_vars(new C) = 0"
| "max_vars(Cast C e) = max_vars e"
| "max_vars(Val v) = 0"
| "max_vars(e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = max (max_vars e\<^sub>1) (max_vars e\<^sub>2)"
| "max_vars(Var V) = 0"
| "max_vars(V:=e) = max_vars e"
| "max_vars(e\<bullet>F{D}) = max_vars e"
| "max_vars(FAss e\<^sub>1 F D e\<^sub>2) = max (max_vars e\<^sub>1) (max_vars e\<^sub>2)"
| "max_vars(e\<bullet>M(es)) = max (max_vars e) (max_varss es)"
| "max_vars({V:T; e}) = max_vars e + 1"
| "max_vars(e\<^sub>1;;e\<^sub>2) = max (max_vars e\<^sub>1) (max_vars e\<^sub>2)"
| "max_vars(if (e) e\<^sub>1 else e\<^sub>2) =
   max (max_vars e) (max (max_vars e\<^sub>1) (max_vars e\<^sub>2))"
| "max_vars(while (b) e) = max (max_vars b) (max_vars e)"
| "max_vars(throw e) = max_vars e"
| "max_vars(try e\<^sub>1 catch(C V) e\<^sub>2) = max (max_vars e\<^sub>1) (max_vars e\<^sub>2 + 1)"

| "max_varss [] = 0"
| "max_varss (e#es) = max (max_vars e) (max_varss es)"

inductive
  eval\<^sub>1 :: "J\<^sub>1_prog \<Rightarrow> expr\<^sub>1 \<Rightarrow> state\<^sub>1 \<Rightarrow> expr\<^sub>1 \<Rightarrow> state\<^sub>1 \<Rightarrow> bool"
          ("_ \<turnstile>\<^sub>1 ((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  and evals\<^sub>1 :: "J\<^sub>1_prog \<Rightarrow> expr\<^sub>1 list \<Rightarrow> state\<^sub>1 \<Rightarrow> expr\<^sub>1 list \<Rightarrow> state\<^sub>1 \<Rightarrow> bool"
           ("_ \<turnstile>\<^sub>1 ((1\<langle>_,/_\<rangle>) [\<Rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  for P :: J\<^sub>1_prog
where

  New\<^sub>1:
  "\<lbrakk> new_Addr h = Some a; P \<turnstile> C has_fields FDTs; h' = h(a\<mapsto>(C,init_fields FDTs)) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>new C,(h,l)\<rangle> \<Rightarrow> \<langle>addr a,(h',l)\<rangle>"
| NewFail\<^sub>1:
  "new_Addr h = None \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>new C, (h,l)\<rangle> \<Rightarrow> \<langle>THROW OutOfMemory,(h,l)\<rangle>"

| Cast\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l)\<rangle>; h a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l)\<rangle>"
| CastNull\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>"
| CastFail\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l)\<rangle>; h a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW ClassCast,(h,l)\<rangle>"
| CastThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| Val\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>"

| BinOp\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v\<^sub>2,s\<^sub>2\<rangle>; binop(bop,v\<^sub>1,v\<^sub>2) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>2\<rangle>"
| BinOpThrow\<^sub>1\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle>"
| BinOpThrow\<^sub>2\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>2\<rangle>"

| Var\<^sub>1:
  "\<lbrakk> ls!i = v; i < size ls \<rbrakk> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>Var i,(h,ls)\<rangle> \<Rightarrow> \<langle>Val v,(h,ls)\<rangle>"

| LAss\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,ls)\<rangle>; i < size ls; ls' = ls[i := v] \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>i:= e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,(h,ls')\<rangle>"
| LAssThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>i:= e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| FAcc\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,ls)\<rangle>; h a = Some(C,fs); fs(F,D) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,ls)\<rangle>"
| FAccNull\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>1\<rangle>"
| FAccThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| FAss\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2)\<rangle>;
    h\<^sub>2 a = Some(C,fs); fs' = fs((F,D)\<mapsto>v); h\<^sub>2' = h\<^sub>2(a\<mapsto>(C,fs')) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1\<bullet>F{D}:= e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,(h\<^sub>2',l\<^sub>2)\<rangle>"
| FAssNull\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>;  P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1\<bullet>F{D}:= e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>2\<rangle>"
| FAssThrow\<^sub>1\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<^sub>1\<bullet>F{D}:= e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"
| FAssThrow\<^sub>2\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1\<bullet>F{D}:= e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"

| CallObjThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"
| CallNull\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>2\<rangle>"
| Call\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,ls\<^sub>2)\<rangle>;
    h\<^sub>2 a = Some(C,fs); P \<turnstile> C sees M:Ts\<rightarrow>T = body in D;
    size vs = size Ts; ls\<^sub>2' = (Addr a) # vs @ replicate (max_vars body) undefined;
    P \<turnstile>\<^sub>1 \<langle>body,(h\<^sub>2,ls\<^sub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,ls\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,ls\<^sub>2)\<rangle>"
| CallParamsThrow\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>es',s\<^sub>2\<rangle>;
     es' = map Val vs @ throw ex # es\<^sub>2 \<rbrakk>
   \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"

| Block\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>1\<rangle> \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>Block i T e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>1\<rangle>"

| Seq\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^sub>0;;e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
| SeqThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<^sub>0;;e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle>"

| CondT\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle>"
| CondF\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle>"
| CondThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| WhileF\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,s\<^sub>1\<rangle>"
| WhileT\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>2\<rangle>;
    P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^sub>2\<rangle> \<Rightarrow> \<langle>e\<^sub>3,s\<^sub>3\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>3,s\<^sub>3\<rangle>"
| WhileCondThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"
| WhileBodyThrow\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>\<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"

| Throw\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,s\<^sub>1\<rangle>"
| ThrowNull\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>1\<rangle>"
| ThrowThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| Try\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>try e\<^sub>1 catch(C i) e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>"
| TryCatch\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,ls\<^sub>1)\<rangle>;
    h\<^sub>1 a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C; i < length ls\<^sub>1;
    P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,(h\<^sub>1,ls\<^sub>1[i:=Addr a])\<rangle> \<Rightarrow> \<langle>e\<^sub>2',(h\<^sub>2,ls\<^sub>2)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>try e\<^sub>1 catch(C i) e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',(h\<^sub>2,ls\<^sub>2)\<rangle>"
| TryThrow\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,ls\<^sub>1)\<rangle>; h\<^sub>1 a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>try e\<^sub>1 catch(C i) e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,ls\<^sub>1)\<rangle>"

| Nil\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>[],s\<rangle>"

| Cons\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>es',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e#es,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>Val v # es',s\<^sub>2\<rangle>"
| ConsThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e#es,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>throw e' # es, s\<^sub>1\<rangle>"

(*<*)
lemmas eval\<^sub>1_evals\<^sub>1_induct = eval\<^sub>1_evals\<^sub>1.induct [split_format (complete)]
  and eval\<^sub>1_evals\<^sub>1_inducts = eval\<^sub>1_evals\<^sub>1.inducts [split_format (complete)]
(*>*)

lemma eval\<^sub>1_preserves_len:
  "P \<turnstile>\<^sub>1 \<langle>e\<^sub>0,(h\<^sub>0,ls\<^sub>0)\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1,ls\<^sub>1)\<rangle> \<Longrightarrow> length ls\<^sub>0 = length ls\<^sub>1"
and evals\<^sub>1_preserves_len:
  "P \<turnstile>\<^sub>1 \<langle>es\<^sub>0,(h\<^sub>0,ls\<^sub>0)\<rangle> [\<Rightarrow>] \<langle>es\<^sub>1,(h\<^sub>1,ls\<^sub>1)\<rangle> \<Longrightarrow> length ls\<^sub>0 = length ls\<^sub>1"
(*<*)by (induct rule:eval\<^sub>1_evals\<^sub>1_inducts, simp_all)(*>*)


lemma evals\<^sub>1_preserves_elen:
  "\<And>es' s s'. P \<turnstile>\<^sub>1 \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> length es = length es'"
(*<*)
apply(induct es type:list)
apply (auto elim:evals\<^sub>1.cases)
done
(*>*)


lemma eval\<^sub>1_final: "P \<turnstile>\<^sub>1 \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> final e'"
 and evals\<^sub>1_final: "P \<turnstile>\<^sub>1 \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> finals es'"
(*<*)by(induct rule:eval\<^sub>1_evals\<^sub>1.inducts, simp_all)(*>*)


end
