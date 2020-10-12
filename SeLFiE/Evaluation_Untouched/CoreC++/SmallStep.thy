(*  Title:       CoreC++
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

   Based on the Jinja theory J/SmallStep.thy by Tobias Nipkow 
*)

section \<open>Small Step Semantics\<close>

theory SmallStep imports Syntax State begin


subsection \<open>Some pre-definitions\<close>

fun blocks :: "vname list \<times> ty list \<times> val list \<times> expr \<Rightarrow> expr"
where
 blocks_Cons:"blocks(V#Vs, T#Ts, v#vs, e) = {V:T := Val v; blocks(Vs,Ts,vs,e)}" |
 blocks_Nil: "blocks([],[],[],e) = e"

lemma blocks_old_induct:
fixes P :: "vname list \<Rightarrow> ty list \<Rightarrow> val list \<Rightarrow> expr \<Rightarrow> bool"
shows
  "\<lbrakk>\<And>aj ak al. P [] [] (aj # ak) al; \<And>ad ae a b. P [] (ad # ae) a b;
  \<And>V Vs a b. P (V # Vs) [] a b; \<And>V Vs T Ts aw. P (V # Vs) (T # Ts) [] aw;
  \<And>V Vs T Ts v vs e. P Vs Ts vs e \<Longrightarrow> P (V # Vs) (T # Ts) (v # vs) e; \<And>e. P [] [] [] e\<rbrakk>
  \<Longrightarrow> P u v w x"
by (induction_schema) (pat_completeness, lexicographic_order)

lemma [simp]:
  "\<lbrakk> size vs = size Vs; size Ts = size Vs \<rbrakk> \<Longrightarrow> fv(blocks(Vs,Ts,vs,e)) = fv e - set Vs"

apply(induct rule:blocks_old_induct)
apply simp_all
apply blast
done



definition assigned :: "vname \<Rightarrow> expr \<Rightarrow> bool" where
  "assigned V e  \<equiv>  \<exists>v e'. e = (V:= Val v;; e')"


subsection \<open>The rules\<close>

inductive_set
  red  :: "prog \<Rightarrow> (env \<times> (expr \<times> state) \<times> (expr \<times> state)) set"
  and reds  :: "prog \<Rightarrow> (env \<times> (expr list \<times> state) \<times> (expr list \<times> state)) set"
  and red' :: "prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
          ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  and reds' :: "prog \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool"
          ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) [\<rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  for P :: prog
where

  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<equiv> (E,(e,s), e',s') \<in> red P"
| "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle> \<equiv> (E,(es,s), es',s') \<in> reds P"

| RedNew:
  "\<lbrakk> new_Addr h = Some a; h' = h(a\<mapsto>(C,Collect (init_obj P C))) \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>new C, (h,l)\<rangle> \<rightarrow> \<langle>ref (a,[C]), (h',l)\<rangle>"

| RedNewFail:
  "new_Addr h = None \<Longrightarrow>
  P,E \<turnstile> \<langle>new C, (h,l)\<rangle> \<rightarrow> \<langle>THROW OutOfMemory, (h,l)\<rangle>"

| StaticCastRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>\<lparr>C\<rparr>e, s\<rangle> \<rightarrow> \<langle>\<lparr>C\<rparr>e', s'\<rangle>"

| RedStaticCastNull:
  "P,E \<turnstile> \<langle>\<lparr>C\<rparr>null, s\<rangle> \<rightarrow> \<langle>null,s\<rangle>"

| RedStaticUpCast:
  "\<lbrakk> P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>(ref (a,Cs)), s\<rangle> \<rightarrow> \<langle>ref (a,Ds), s\<rangle>"

| RedStaticDownCast:
  "P,E \<turnstile> \<langle>\<lparr>C\<rparr>(ref (a,Cs@[C]@Cs')), s\<rangle> \<rightarrow> \<langle>ref (a,Cs@[C]), s\<rangle>"

| RedStaticCastFail:
  "\<lbrakk>C \<notin> set Cs; \<not> P \<turnstile> (last Cs) \<preceq>\<^sup>* C\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>(ref (a,Cs)), s\<rangle> \<rightarrow> \<langle>THROW ClassCast, s\<rangle>"

| DynCastRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>Cast C e, s\<rangle> \<rightarrow> \<langle>Cast C e', s'\<rangle>"

| RedDynCastNull:
  "P,E \<turnstile> \<langle>Cast C null, s\<rangle> \<rightarrow> \<langle>null,s\<rangle>"

| RedStaticUpDynCast: (* path uniqueness not necessary for type proof but for determinism *)
  "\<lbrakk> P \<turnstile> Path last Cs to C unique; P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C(ref(a,Cs)),s\<rangle> \<rightarrow> \<langle>ref(a,Ds),s\<rangle>"

| RedStaticDownDynCast:
  "P,E \<turnstile> \<langle>Cast C (ref (a,Cs@[C]@Cs')), s\<rangle> \<rightarrow> \<langle>ref (a,Cs@[C]), s\<rangle>"

| RedDynCast:(* path uniqueness not necessary for type proof but for determinism *)
 "\<lbrakk> hp s a = Some(D,S); P \<turnstile> Path D to C via Cs';
    P \<turnstile> Path D to C unique \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C (ref (a,Cs)), s\<rangle> \<rightarrow> \<langle>ref (a,Cs'), s\<rangle>"

| RedDynCastFail:(* third premise not necessary for type proof but for determinism *)
  "\<lbrakk>hp s a = Some(D,S); \<not> P \<turnstile> Path D to C unique;
    \<not> P \<turnstile> Path last Cs to C unique; C \<notin> set Cs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C (ref (a,Cs)), s\<rangle> \<rightarrow> \<langle>null, s\<rangle>"

| BinOpRed1:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<rangle> \<rightarrow> \<langle>e' \<guillemotleft>bop\<guillemotright> e\<^sub>2, s'\<rangle>"

| BinOpRed2:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>(Val v\<^sub>1) \<guillemotleft>bop\<guillemotright> e, s\<rangle> \<rightarrow> \<langle>(Val v\<^sub>1) \<guillemotleft>bop\<guillemotright> e', s'\<rangle>"

| RedBinOp:
  "binop(bop,v\<^sub>1,v\<^sub>2) = Some v \<Longrightarrow>
  P,E \<turnstile> \<langle>(Val v\<^sub>1) \<guillemotleft>bop\<guillemotright> (Val v\<^sub>2), s\<rangle> \<rightarrow> \<langle>Val v,s\<rangle>"

| RedVar:
  "lcl s V = Some v \<Longrightarrow>
  P,E \<turnstile> \<langle>Var V,s\<rangle> \<rightarrow> \<langle>Val v,s\<rangle>"

| LAssRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>V:=e,s\<rangle> \<rightarrow> \<langle>V:=e',s'\<rangle>"

| RedLAss:
  "\<lbrakk>E V = Some T; P \<turnstile> T casts v to v'\<rbrakk> \<Longrightarrow> 
  P,E \<turnstile> \<langle>V:=(Val v),(h,l)\<rangle> \<rightarrow> \<langle>Val v',(h,l(V\<mapsto>v'))\<rangle>"

| FAccRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<bullet>F{Cs}, s\<rangle> \<rightarrow> \<langle>e'\<bullet>F{Cs}, s'\<rangle>"

| RedFAcc:
  "\<lbrakk> hp s a = Some(D,S); Ds = Cs'@\<^sub>pCs; (Ds,fs) \<in> S; fs F = Some v \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>(ref (a,Cs'))\<bullet>F{Cs}, s\<rangle> \<rightarrow> \<langle>Val v,s\<rangle>"

| RedFAccNull:
  "P,E \<turnstile> \<langle>null\<bullet>F{Cs}, s\<rangle> \<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| FAssRed1:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<bullet>F{Cs}:=e\<^sub>2, s\<rangle> \<rightarrow> \<langle>e'\<bullet>F{Cs}:=e\<^sub>2, s'\<rangle>"

| FAssRed2:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
   P,E \<turnstile> \<langle>Val v\<bullet>F{Cs}:=e, s\<rangle> \<rightarrow> \<langle>Val v\<bullet>F{Cs}:=e', s'\<rangle>"

| RedFAss:
"\<lbrakk>h a = Some(D,S); P \<turnstile> (last Cs') has least F:T via Cs;
  P \<turnstile> T casts v to v'; Ds = Cs'@\<^sub>pCs; (Ds,fs) \<in> S\<rbrakk> \<Longrightarrow>
  P,E \<turnstile> \<langle>(ref (a,Cs'))\<bullet>F{Cs}:=(Val v), (h,l)\<rangle> \<rightarrow> \<langle>Val v', (h(a \<mapsto> (D,insert (Ds,fs(F\<mapsto>v')) (S - {(Ds,fs)}))),l)\<rangle>"

| RedFAssNull:
  "P,E \<turnstile> \<langle>null\<bullet>F{Cs}:=Val v, s\<rangle> \<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| CallObj:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>Call e Copt M es,s\<rangle> \<rightarrow> \<langle>Call e' Copt M es,s'\<rangle>"

| CallParams:
  "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
   P,E \<turnstile> \<langle>Call (Val v) Copt M es,s\<rangle> \<rightarrow> \<langle>Call (Val v) Copt M es',s'\<rangle>"

| RedCall:
  "\<lbrakk> hp s a = Some(C,S); P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds;
    P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs';
    size vs = size pns; size Ts = size pns; 
    bs = blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body);
    new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>bs | _ \<Rightarrow> bs)\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>(ref (a,Cs))\<bullet>M(map Val vs), s\<rangle> \<rightarrow> \<langle>new_body, s\<rangle>"

| RedStaticCall:
  "\<lbrakk> P \<turnstile> Path (last Cs) to C unique; P \<turnstile> Path (last Cs) to C via Cs'';
    P \<turnstile> C has least M = (Ts,T,pns,body) via Cs'; Ds = (Cs@\<^sub>pCs'')@\<^sub>pCs';
    size vs = size pns; size Ts = size pns \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>(ref (a,Cs))\<bullet>(C::)M(map Val vs), s\<rangle> \<rightarrow> 
            \<langle>blocks(this#pns,Class(last Ds)#Ts,Ref(a,Ds)#vs,body), s\<rangle>"

| RedCallNull:
  "P,E \<turnstile> \<langle>Call null Copt M (map Val vs),s\<rangle> \<rightarrow> \<langle>THROW NullPointer,s\<rangle>"

| BlockRedNone:
  "\<lbrakk> P,E(V \<mapsto> T) \<turnstile> \<langle>e, (h,l(V:=None))\<rangle> \<rightarrow> \<langle>e', (h',l')\<rangle>; l' V = None; \<not> assigned V e \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>{V:T; e}, (h,l)\<rangle> \<rightarrow> \<langle>{V:T; e'}, (h',l'(V := l V))\<rangle>"

| BlockRedSome:
  "\<lbrakk> P,E(V \<mapsto> T) \<turnstile> \<langle>e, (h,l(V:=None))\<rangle> \<rightarrow> \<langle>e', (h',l')\<rangle>; l' V = Some v;
     \<not> assigned V e \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>{V:T; e}, (h,l)\<rangle> \<rightarrow> \<langle>{V:T := Val v; e'}, (h',l'(V := l V))\<rangle>"

| InitBlockRed:
  "\<lbrakk> P,E(V \<mapsto> T) \<turnstile> \<langle>e, (h,l(V\<mapsto>v'))\<rangle> \<rightarrow> \<langle>e', (h',l')\<rangle>; l' V = Some v''; 
     P \<turnstile> T casts v to v' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>{V:T := Val v; e}, (h,l)\<rangle> \<rightarrow> \<langle>{V:T := Val v''; e'}, (h',l'(V := l V))\<rangle>"

| RedBlock:
  "P,E \<turnstile> \<langle>{V:T; Val u}, s\<rangle> \<rightarrow> \<langle>Val u, s\<rangle>"

| RedInitBlock:
  "P \<turnstile> T casts v to v' \<Longrightarrow> P,E \<turnstile> \<langle>{V:T := Val v; Val u}, s\<rangle> \<rightarrow> \<langle>Val u, s\<rangle>"

| SeqRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e;;e\<^sub>2, s\<rangle> \<rightarrow> \<langle>e';;e\<^sub>2, s'\<rangle>"

| RedSeq:
  "P,E \<turnstile> \<langle>(Val v);;e\<^sub>2, s\<rangle> \<rightarrow> \<langle>e\<^sub>2, s\<rangle>"

| CondRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<rangle> \<rightarrow> \<langle>if (e') e\<^sub>1 else e\<^sub>2, s'\<rangle>"

| RedCondT:
  "P,E \<turnstile> \<langle>if (true) e\<^sub>1 else e\<^sub>2, s\<rangle> \<rightarrow> \<langle>e\<^sub>1, s\<rangle>"

| RedCondF:
  "P,E \<turnstile> \<langle>if (false) e\<^sub>1 else e\<^sub>2, s\<rangle> \<rightarrow> \<langle>e\<^sub>2, s\<rangle>"

| RedWhile:
  "P,E \<turnstile> \<langle>while(b) c, s\<rangle> \<rightarrow> \<langle>if(b) (c;;while(b) c) else unit, s\<rangle>"

| ThrowRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>throw e, s\<rangle> \<rightarrow> \<langle>throw e', s'\<rangle>"

| RedThrowNull:
  "P,E \<turnstile> \<langle>throw null, s\<rangle> \<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

| ListRed1:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e#es,s\<rangle> [\<rightarrow>] \<langle>e'#es,s'\<rangle>"

| ListRed2:
  "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>Val v # es,s\<rangle> [\<rightarrow>] \<langle>Val v # es',s'\<rangle>"

\<comment> \<open>Exception propagation\<close>

| DynCastThrow: "P,E \<turnstile> \<langle>Cast C (Throw r), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
| StaticCastThrow: "P,E \<turnstile> \<langle>\<lparr>C\<rparr>(Throw r), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
| BinOpThrow1: "P,E \<turnstile> \<langle>(Throw r) \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
| BinOpThrow2: "P,E \<turnstile> \<langle>(Val v\<^sub>1) \<guillemotleft>bop\<guillemotright> (Throw r), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
| LAssThrow: "P,E \<turnstile> \<langle>V:=(Throw r), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
| FAccThrow: "P,E \<turnstile> \<langle>(Throw r)\<bullet>F{Cs}, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
| FAssThrow1: "P,E \<turnstile> \<langle>(Throw r)\<bullet>F{Cs}:=e\<^sub>2, s\<rangle> \<rightarrow> \<langle>Throw r,s\<rangle>"
| FAssThrow2: "P,E \<turnstile> \<langle>Val v\<bullet>F{Cs}:=(Throw r), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
| CallThrowObj: "P,E \<turnstile> \<langle>Call (Throw r) Copt M es, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
| CallThrowParams: "\<lbrakk> es = map Val vs @ Throw r # es' \<rbrakk> 
  \<Longrightarrow> P,E \<turnstile> \<langle>Call (Val v) Copt M es, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
| BlockThrow: "P,E \<turnstile> \<langle>{V:T; Throw r}, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
| InitBlockThrow: "P \<turnstile> T casts v to v' 
  \<Longrightarrow> P,E \<turnstile> \<langle>{V:T := Val v; Throw r}, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
| SeqThrow: "P,E \<turnstile> \<langle>(Throw r);;e\<^sub>2, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
| CondThrow: "P,E \<turnstile> \<langle>if (Throw r) e\<^sub>1 else e\<^sub>2, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
| ThrowThrow: "P,E \<turnstile> \<langle>throw(Throw r), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"


lemmas red_reds_induct = red_reds.induct [split_format (complete)]
  and red_reds_inducts = red_reds.inducts [split_format (complete)]

inductive_cases [elim!]:
 "P,E \<turnstile> \<langle>V:=e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e1;;e2,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"

declare Cons_eq_map_conv [iff]

lemma "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> True"
and reds_length:"P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> length es = length es'"
by (induct rule: red_reds.inducts) auto


subsection\<open>The reflexive transitive closure\<close>

definition Red :: "prog \<Rightarrow> env \<Rightarrow> ((expr \<times> state) \<times> (expr \<times> state)) set"
  where "Red P E = {((e,s),e',s'). P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>}"

definition Reds :: "prog \<Rightarrow> env \<Rightarrow> ((expr list \<times> state) \<times> (expr list \<times> state)) set"
  where "Reds P E = {((es,s),es',s'). P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>}"

lemma[simp]: "((e,s),e',s') \<in> Red P E = P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
by (simp add:Red_def)

lemma[simp]: "((es,s),es',s') \<in> Reds P E = P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>"
by (simp add:Reds_def)



abbreviation
  Step :: "prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
          ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<rightarrow>*/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81) where
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<equiv> ((e,s), e',s') \<in> (Red P E)\<^sup>*"

abbreviation
  Steps :: "prog \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool"
          ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) [\<rightarrow>]*/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81) where
  "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle> \<equiv> ((es,s), es',s') \<in> (Reds P E)\<^sup>*"


lemma converse_rtrancl_induct_red[consumes 1]:
assumes "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow>* \<langle>e',(h',l')\<rangle>"
and "\<And>e h l. R e h l e h l"
and "\<And>e\<^sub>0 h\<^sub>0 l\<^sub>0 e\<^sub>1 h\<^sub>1 l\<^sub>1 e' h' l'.
       \<lbrakk> P,E \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0,l\<^sub>0)\<rangle> \<rightarrow> \<langle>e\<^sub>1,(h\<^sub>1,l\<^sub>1)\<rangle>; R e\<^sub>1 h\<^sub>1 l\<^sub>1 e' h' l' \<rbrakk> \<Longrightarrow> R e\<^sub>0 h\<^sub>0 l\<^sub>0 e' h' l'"
shows "R e h l e' h' l'"

proof -
  { fix s s'
    assume reds: "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
       and base: "\<And>e s. R e (hp s) (lcl s) e (hp s) (lcl s)"
       and IH: "\<And>e\<^sub>0 s\<^sub>0 e\<^sub>1 s\<^sub>1 e' s'.
           \<lbrakk> P,E \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<rightarrow> \<langle>e\<^sub>1,s\<^sub>1\<rangle>; R e\<^sub>1 (hp s\<^sub>1) (lcl s\<^sub>1) e' (hp s') (lcl s') \<rbrakk>
           \<Longrightarrow> R e\<^sub>0 (hp s\<^sub>0) (lcl s\<^sub>0) e' (hp s') (lcl s')"
    from reds have "R e (hp s) (lcl s) e' (hp s') (lcl s')"
    proof (induct rule:converse_rtrancl_induct2)
      case refl show ?case by(rule base)
    next
      case (step e\<^sub>0 s\<^sub>0 e s)
      have Red:"((e\<^sub>0,s\<^sub>0),e,s) \<in> Red P E"
        and R:"R e (hp s) (lcl s) e' (hp s') (lcl s')" by fact+
      from IH[OF Red[simplified] R] show ?case .
    qed
    }
  with assms show ?thesis by fastforce
qed



lemma steps_length:"P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle> \<Longrightarrow> length es = length es'"
by(induct rule:rtrancl_induct2,auto intro:reds_length)


subsection\<open>Some easy lemmas\<close>

lemma [iff]: "\<not> P,E \<turnstile> \<langle>[],s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>"
by(blast elim: reds.cases)

lemma [iff]: "\<not> P,E \<turnstile> \<langle>Val v,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
by(fastforce elim: red.cases)

lemma [iff]: "\<not> P,E \<turnstile> \<langle>Throw r,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
by(fastforce elim: red.cases)


lemma red_lcl_incr: "P,E \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0)\<rangle> \<rightarrow> \<langle>e',(h\<^sub>1,l\<^sub>1)\<rangle> \<Longrightarrow> dom l\<^sub>0 \<subseteq> dom l\<^sub>1"
and "P,E \<turnstile> \<langle>es,(h\<^sub>0,l\<^sub>0)\<rangle> [\<rightarrow>] \<langle>es',(h\<^sub>1,l\<^sub>1)\<rangle> \<Longrightarrow> dom l\<^sub>0 \<subseteq> dom l\<^sub>1"
by (induct rule: red_reds_inducts) (auto simp del:fun_upd_apply)


lemma red_lcl_add: "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> (\<And>l\<^sub>0. P,E \<turnstile> \<langle>e,(h,l\<^sub>0++l)\<rangle> \<rightarrow> \<langle>e',(h',l\<^sub>0++l')\<rangle>)"
and "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> (\<And>l\<^sub>0. P,E \<turnstile> \<langle>es,(h,l\<^sub>0++l)\<rangle> [\<rightarrow>] \<langle>es',(h',l\<^sub>0++l')\<rangle>)"
 
proof (induct rule:red_reds_inducts)
  case RedLAss thus ?case by(auto intro:red_reds.intros simp del:fun_upd_apply)
next
  case RedStaticDownCast thus ?case by(fastforce intro:red_reds.intros)
next
  case RedStaticUpDynCast thus ?case by(fastforce intro:red_reds.intros)
next
  case RedStaticDownDynCast thus ?case by(fastforce intro:red_reds.intros)
next
  case RedDynCast thus ?case by(fastforce intro:red_reds.intros)
next
  case RedDynCastFail thus ?case by(fastforce intro:red_reds.intros)
next
  case RedFAcc thus ?case by(fastforce intro:red_reds.intros)
next
  case RedFAss thus ?case by (fastforce intro:red_reds.intros)
next
  case RedCall thus ?case by (fastforce intro!:red_reds.RedCall)
next
  case RedStaticCall thus ?case by(fastforce intro:red_reds.intros)
next
  case (InitBlockRed E V T e h l v' e' h' l' v'' v l\<^sub>0)
  have IH: "\<And>l\<^sub>0. P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l\<^sub>0 ++ l(V \<mapsto> v'))\<rangle> \<rightarrow> \<langle>e',(h', l\<^sub>0 ++ l')\<rangle>"
    and l'V: "l' V = Some v''" and casts:"P \<turnstile> T casts v to v'" by fact+
  from IH have IH': "P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, (l\<^sub>0 ++ l)(V \<mapsto> v'))\<rangle> \<rightarrow> \<langle>e',(h',l\<^sub>0 ++ l')\<rangle>"
    by simp
  have "(l\<^sub>0 ++ l')(V := (l\<^sub>0 ++ l) V) = l\<^sub>0 ++ l'(V := l V)"
    by(rule ext)(simp add:map_add_def)
  with red_reds.InitBlockRed[OF IH' _ casts] l'V show ?case
    by(simp del:fun_upd_apply)
next
  case (BlockRedNone E V T e h l e' h' l' l\<^sub>0)
  have IH: "\<And>l\<^sub>0. P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l\<^sub>0 ++ l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l\<^sub>0 ++ l')\<rangle>"
    and l'V: "l' V = None" and unass: "\<not> assigned V e" by fact+
  have "l\<^sub>0(V := None) ++ l(V := None) = (l\<^sub>0 ++ l)(V := None)"
    by(simp add:fun_eq_iff map_add_def)
  hence IH': "P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, (l\<^sub>0++l)(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l\<^sub>0(V := None) ++ l')\<rangle>"
    using IH[of "l\<^sub>0(V := None)"] by simp
  have "(l\<^sub>0(V := None) ++ l')(V := (l\<^sub>0 ++ l) V) = l\<^sub>0 ++ l'(V := l V)"
    by(simp add:fun_eq_iff map_add_def)
  with red_reds.BlockRedNone[OF IH' _ unass] l'V show ?case
    by(simp add: map_add_def)
next
  case (BlockRedSome E V T e h l e' h' l' v l\<^sub>0)
  have IH: "\<And>l\<^sub>0. P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l\<^sub>0 ++ l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l\<^sub>0 ++ l')\<rangle>"
    and l'V: "l' V = Some v" and unass: "\<not> assigned V e" by fact+
  have "l\<^sub>0(V := None) ++ l(V := None) = (l\<^sub>0 ++ l)(V := None)"
    by(simp add:fun_eq_iff map_add_def)
  hence IH': "P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, (l\<^sub>0++l)(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l\<^sub>0(V := None) ++ l')\<rangle>"
    using IH[of "l\<^sub>0(V := None)"] by simp
  have "(l\<^sub>0(V := None) ++ l')(V := (l\<^sub>0 ++ l) V) = l\<^sub>0 ++ l'(V := l V)"
    by(simp add:fun_eq_iff map_add_def)
  with red_reds.BlockRedSome[OF IH' _ unass] l'V show ?case
    by(simp add:map_add_def)
next
qed (simp_all add:red_reds.intros)



lemma Red_lcl_add:
assumes "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow>* \<langle>e',(h',l')\<rangle>" shows "P,E \<turnstile> \<langle>e,(h,l\<^sub>0++l)\<rangle> \<rightarrow>* \<langle>e',(h',l\<^sub>0++l')\<rangle>"
using assms
proof(induct rule:converse_rtrancl_induct_red)
  case 1 thus ?case by simp
next
  case 2 thus ?case
    by(auto dest: red_lcl_add intro: converse_rtrancl_into_rtrancl simp:Red_def)
qed



lemma 
red_preserves_obj:"\<lbrakk>P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>; h a = Some(D,S)\<rbrakk> 
  \<Longrightarrow> \<exists>S'. h' a = Some(D,S')"
and reds_preserves_obj:"\<lbrakk>P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle>; h a = Some(D,S)\<rbrakk> 
  \<Longrightarrow> \<exists>S'. h' a = Some(D,S')"
by (induct rule:red_reds_inducts) (auto dest:new_Addr_SomeD)

end
