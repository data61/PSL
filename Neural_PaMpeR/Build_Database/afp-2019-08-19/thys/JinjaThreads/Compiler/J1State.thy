(*  Title:      JinjaThreads/Compiler/J1State.thy
    Author:     Andreas Lochbihler
*)

section \<open>The intermediate language J1\<close>

theory J1State imports
  "../J/State"
  CallExpr
begin

type_synonym
  'addr expr1 = "(nat, nat, 'addr) exp"

type_synonym
  'addr J1_prog = "'addr expr1 prog"

type_synonym
  'addr locals1 = "'addr val list"

translations
  (type) "'addr expr1" <= (type) "(nat, nat, 'addr) exp"
  (type) "'addr J1_prog" <= (type) "'addr expr1 prog"

type_synonym
  'addr J1state = "('addr expr1 \<times> 'addr locals1) list"

type_synonym
  ('addr, 'thread_id, 'heap) J1_thread_action = 
  "('addr, 'thread_id, ('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list,'heap) Jinja_thread_action"

type_synonym
  ('addr, 'thread_id, 'heap) J1_state = 
  "('addr,'thread_id,('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list,'heap,'addr) state"

(* pretty printing for J1_thread_action type *)
print_translation \<open>
  let
    fun tr'
       [a1, t
       , Const (@{type_syntax "prod"}, _) $ 
           (Const (@{type_syntax "prod"}, _) $
              (Const (@{type_syntax "exp"}, _) $ Const (@{type_syntax "nat"}, _) $ Const (@{type_syntax "nat"}, _) $ a2) $
              (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "val"}, _) $ a3))) $
           (Const (@{type_syntax "list"}, _) $
              (Const (@{type_syntax "prod"}, _) $
                (Const (@{type_syntax "exp"}, _) $ Const (@{type_syntax "nat"}, _) $ Const (@{type_syntax "nat"}, _) $ a4) $
                (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "val"}, _) $ a5))))
       , h] =
      if a1 = a2 andalso a2 = a3 andalso a3 = a4 andalso a4 = a5 
      then Syntax.const @{type_syntax "J1_thread_action"} $ a1 $ t $ h
      else raise Match;
    in [(@{type_syntax "Jinja_thread_action"}, K tr')]
  end
\<close>
typ "('addr,'thread_id,'heap) J1_thread_action"

(* pretty printing for J1_state type *)
print_translation \<open>
  let
    fun tr'
       [a1, t
       , Const (@{type_syntax "prod"}, _) $ 
           (Const (@{type_syntax "prod"}, _) $
              (Const (@{type_syntax "exp"}, _) $ Const (@{type_syntax "nat"}, _) $ Const (@{type_syntax "nat"}, _) $ a2) $
              (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "val"}, _) $ a3))) $
           (Const (@{type_syntax "list"}, _) $
              (Const (@{type_syntax "prod"}, _) $
                (Const (@{type_syntax "exp"}, _) $ Const (@{type_syntax "nat"}, _) $ Const (@{type_syntax "nat"}, _) $ a4) $
                (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "val"}, _) $ a5))))
       , h, a6] =
      if a1 = a2 andalso a2 = a3 andalso a3 = a4 andalso a4 = a5 andalso a5 = a6
      then Syntax.const @{type_syntax "J1_state"} $ a1 $ t $ h
      else raise Match;
    in [(@{type_syntax "state"}, K tr')]
  end
\<close>
typ "('addr, 'thread_id, 'heap) J1_state"

fun blocks1 :: "nat \<Rightarrow> ty list \<Rightarrow> (nat,'b,'addr) exp \<Rightarrow> (nat,'b,'addr) exp"
where 
  "blocks1 n [] e = e"
| "blocks1 n (T#Ts) e = {n:T=None; blocks1 (Suc n) Ts e}"

primrec max_vars:: "('a,'b,'addr) exp \<Rightarrow> nat"
  and max_varss:: "('a,'b,'addr) exp list \<Rightarrow> nat"
where
  "max_vars (new C) = 0"
| "max_vars (newA T\<lfloor>e\<rceil>) = max_vars e"
| "max_vars (Cast C e) = max_vars e"
| "max_vars (e instanceof T) = max_vars e"
| "max_vars (Val v) = 0"
| "max_vars (e \<guillemotleft>bop\<guillemotright> e') = max (max_vars e) (max_vars e')"
| "max_vars (Var V) = 0"
| "max_vars (V:=e) = max_vars e"
| "max_vars (a\<lfloor>i\<rceil>) = max (max_vars a) (max_vars i)"
| "max_vars (AAss a i e) = max (max (max_vars a) (max_vars i)) (max_vars e)"
| "max_vars (a\<bullet>length) = max_vars a"
| "max_vars (e\<bullet>F{D}) = max_vars e"
| "max_vars (FAss e\<^sub>1 F D e\<^sub>2) = max (max_vars e\<^sub>1) (max_vars e\<^sub>2)"
| "max_vars (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) = max (max (max_vars e) (max_vars e')) (max_vars e'')"
| "max_vars (e\<bullet>M(es)) = max (max_vars e) (max_varss es)"
| "max_vars ({V:T=vo; e}) = max_vars e + 1"
\<comment> \<open>sync and insync will need an extra local variable when compiling to bytecode to store the object that is being synchronized on until its release\<close>
| "max_vars (sync\<^bsub>V\<^esub> (e') e) = max (max_vars e') (max_vars e + 1)"
| "max_vars (insync\<^bsub>V\<^esub> (a) e) = max_vars e + 1"
| "max_vars (e\<^sub>1;;e\<^sub>2) = max (max_vars e\<^sub>1) (max_vars e\<^sub>2)"
| "max_vars (if (e) e\<^sub>1 else e\<^sub>2) =
   max (max_vars e) (max (max_vars e\<^sub>1) (max_vars e\<^sub>2))"
| "max_vars (while (b) e) = max (max_vars b) (max_vars e)"
| "max_vars (throw e) = max_vars e"
| "max_vars (try e\<^sub>1 catch(C V) e\<^sub>2) = max (max_vars e\<^sub>1) (max_vars e\<^sub>2 + 1)"

| "max_varss [] = 0"
| "max_varss (e#es) = max (max_vars e) (max_varss es)"

\<comment> \<open>Indices in blocks increase by 1\<close>

primrec \<B> :: "'addr expr1 \<Rightarrow> nat \<Rightarrow> bool"
  and \<B>s :: "'addr expr1 list \<Rightarrow> nat \<Rightarrow> bool"
where
  "\<B> (new C) i = True"
| "\<B> (newA T\<lfloor>e\<rceil>) i = \<B> e i"
| "\<B> (Cast C e) i = \<B> e i"
| "\<B> (e instanceof T) i = \<B> e i"
| "\<B> (Val v) i = True"
| "\<B> (e1 \<guillemotleft>bop\<guillemotright> e2) i = (\<B> e1 i \<and> \<B> e2 i)"
| "\<B> (Var j) i = True"
| "\<B> (j:=e) i = \<B> e i"
| "\<B> (a\<lfloor>j\<rceil>) i = (\<B> a i \<and> \<B> j i)"
| "\<B> (a\<lfloor>j\<rceil>:=e) i = (\<B> a i \<and> \<B> j i \<and> \<B> e i)"
| "\<B> (a\<bullet>length) i = \<B> a i"
| "\<B> (e\<bullet>F{D}) i = \<B> e i"
| "\<B> (e1\<bullet>F{D} := e2) i = (\<B> e1 i \<and> \<B> e2 i)"
| "\<B> (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) i = (\<B> e i \<and> \<B> e' i \<and> \<B> e'' i)"
| "\<B> (e\<bullet>M(es)) i = (\<B> e i \<and> \<B>s es i)"
| "\<B> ({j:T=vo; e}) i = (i = j \<and> \<B> e (i+1))"
| "\<B> (sync\<^bsub>V\<^esub> (o') e) i = (i = V \<and> \<B> o' i \<and> \<B> e (i+1))"
| "\<B> (insync\<^bsub>V\<^esub> (a) e) i = (i = V \<and> \<B> e (i+1))"
| "\<B> (e1;;e2) i = (\<B> e1 i \<and> \<B> e2 i)"
| "\<B> (if (e) e1 else e2) i = (\<B> e i \<and> \<B> e1 i \<and> \<B> e2 i)"
| "\<B> (throw e) i = \<B> e i"
| "\<B> (while (e) c) i = (\<B> e i \<and> \<B> c i)"
| "\<B> (try e1 catch(C j) e2) i = (\<B> e1 i \<and> i=j \<and> \<B> e2 (i+1))"

| "\<B>s [] i = True"
| "\<B>s (e#es) i = (\<B> e i \<and> \<B>s es i)"

text \<open>
  Variables for monitor addresses do not occur freely in synchonization blocks
\<close>

primrec syncvars :: "('a, 'a, 'addr) exp \<Rightarrow> bool"
  and syncvarss :: "('a, 'a, 'addr) exp list \<Rightarrow> bool"
where
  "syncvars (new C) = True"
| "syncvars (newA T\<lfloor>e\<rceil>) = syncvars e"
| "syncvars (Cast T e) = syncvars e"
| "syncvars (e instanceof T) = syncvars e"
| "syncvars (Val v) = True"
| "syncvars (e1 \<guillemotleft>bop\<guillemotright> e2) = (syncvars e1 \<and> syncvars e2)"
| "syncvars (Var V) = True"
| "syncvars (V:=e) = syncvars e"
| "syncvars (a\<lfloor>i\<rceil>) = (syncvars a \<and> syncvars i)"
| "syncvars (a\<lfloor>i\<rceil> := e) = (syncvars a \<and> syncvars i \<and> syncvars e)"
| "syncvars (a\<bullet>length) = syncvars a"
| "syncvars (e\<bullet>F{D}) = syncvars e"
| "syncvars (e\<bullet>F{D} := e2) = (syncvars e \<and> syncvars e2)"
| "syncvars (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) = (syncvars e \<and> syncvars e' \<and> syncvars e'')"
| "syncvars (e\<bullet>M(es)) = (syncvars e \<and> syncvarss es)"
| "syncvars {V:T=vo;e} = syncvars e"
| "syncvars (sync\<^bsub>V\<^esub> (e1) e2) = (syncvars e1 \<and> syncvars e2 \<and> V \<notin> fv e2)"
| "syncvars (insync\<^bsub>V\<^esub> (a) e) = (syncvars e \<and> V \<notin> fv e)"
| "syncvars (e1;;e2) = (syncvars e1 \<and> syncvars e2)"
| "syncvars (if (b) e1 else e2) = (syncvars b \<and> syncvars e1 \<and> syncvars e2)"
| "syncvars (while (b) c) = (syncvars b \<and> syncvars c)"
| "syncvars (throw e) = syncvars e"
| "syncvars (try e1 catch(C V) e2) = (syncvars e1 \<and> syncvars e2)"

| "syncvarss [] = True"
| "syncvarss (e#es) = (syncvars e \<and> syncvarss es)"

definition bsok :: "'addr expr1 \<Rightarrow> nat \<Rightarrow> bool"
where "bsok e n \<equiv> \<B> e n \<and> expr_locks e = (\<lambda>ad. 0)"

definition bsoks :: "'addr expr1 list \<Rightarrow> nat \<Rightarrow> bool"
where "bsoks es n \<equiv> \<B>s es n \<and> expr_lockss es = (\<lambda>ad. 0)"

primrec call1 :: "('a, 'b, 'addr) exp \<Rightarrow> ('addr \<times> mname \<times> 'addr val list) option"
  and calls1 :: "('a, 'b, 'addr) exp list \<Rightarrow> ('addr \<times> mname \<times> 'addr val list) option"
where
  "call1 (new C) = None"
| "call1 (newA T\<lfloor>e\<rceil>) = call1 e"
| "call1 (Cast C e) = call1 e"
| "call1 (e instanceof T) = call1 e"
| "call1 (Val v) = None"
| "call1 (Var V) = None"
| "call1 (V:=e) = call1 e"
| "call1 (e \<guillemotleft>bop\<guillemotright> e') = (if is_val e then call1 e' else call1 e)"
| "call1 (a\<lfloor>i\<rceil>) = (if is_val a then call1 i else call1 a)"
| "call1 (AAss a i e) = (if is_val a then (if is_val i then call1 e else call1 i) else call1 a)"
| "call1 (a\<bullet>length) = call1 a"
| "call1 (e\<bullet>F{D}) = call1 e"
| "call1 (FAss e F D e') = (if is_val e then call1 e' else call1 e)"
| "call1 (CompareAndSwap e D F e' e'') = (if is_val e then (if is_val e' then call1 e'' else call1 e') else call1 e)"
| "call1 (e\<bullet>M(es)) = (if is_val e then
                     (if is_vals es \<and> is_addr e then \<lfloor>(THE a. e = addr a, M, THE vs. es = map Val vs)\<rfloor> else calls1 es) 
                     else call1 e)"
| "call1 ({V:T=vo; e}) = (case vo of None \<Rightarrow> call1 e | Some v \<Rightarrow> None)"
| "call1 (sync\<^bsub>V\<^esub> (o') e) = call1 o'"
| "call1 (insync\<^bsub>V\<^esub> (a) e) = call1 e"
| "call1 (e;;e') = call1 e"
| "call1 (if (e) e1 else e2) = call1 e"
| "call1 (while(b) e) = None"
| "call1 (throw e) = call1 e"
| "call1 (try e1 catch(C V) e2) = call1 e1"

| "calls1 [] = None"
| "calls1 (e#es) = (if is_val e then calls1 es else call1 e)"


lemma expr_locks_blocks1 [simp]:
  "expr_locks (blocks1 n Ts e) = expr_locks e"
by(induct n Ts e rule: blocks1.induct) simp_all

lemma max_varss_append [simp]:
  "max_varss (es @ es') = max (max_varss es) (max_varss es')"
by(induct es, auto)

lemma max_varss_map_Val [simp]: "max_varss (map Val vs) = 0"
by(induct vs) auto

lemma blocks1_max_vars:
  "max_vars (blocks1 n Ts e) = max_vars e + length Ts"
by(induct n Ts e rule: blocks1.induct)(auto)

lemma blocks_max_vars:
  "\<lbrakk> length vs = length pns; length Ts = length pns \<rbrakk>
  \<Longrightarrow> max_vars (blocks pns Ts vs e) = max_vars e + length pns"
by(induct pns Ts vs e rule: blocks.induct)(auto)

lemma Bs_append [simp]: "\<B>s (es @ es') n \<longleftrightarrow> \<B>s es n \<and> \<B>s es' n"
by(induct es) auto

lemma Bs_map_Val [simp]: "\<B>s (map Val vs) n"
by(induct vs) auto

lemma B_blocks1 [intro]: "\<B> body (n + length Ts) \<Longrightarrow> \<B> (blocks1 n Ts body) n"
by(induct n Ts body rule: blocks1.induct)(auto)

lemma B_extRet2J [simp]: "\<B> e n \<Longrightarrow> \<B> (extRet2J e va) n"
by(cases va) auto

lemma B_inline_call: "\<lbrakk> \<B> e n; \<And>n. \<B> e' n \<rbrakk> \<Longrightarrow> \<B> (inline_call e' e) n"
  and Bs_inline_calls: "\<lbrakk> \<B>s es n; \<And>n. \<B> e' n \<rbrakk> \<Longrightarrow> \<B>s (inline_calls e' es) n"
by(induct e and es arbitrary: n and n rule: call.induct calls.induct) auto

lemma syncvarss_append [simp]: "syncvarss (es @ es') \<longleftrightarrow> syncvarss es \<and> syncvarss es'"
by(induct es) auto

lemma syncvarss_map_Val [simp]: "syncvarss (map Val vs)"
by(induct vs) auto

lemma bsok_simps [simp]:
  "bsok (new C) n = True"
  "bsok (newA T\<lfloor>e\<rceil>) n = bsok e n"
  "bsok (Cast T e) n = bsok e n"
  "bsok (e instanceof T) n = bsok e n"
  "bsok (e1 \<guillemotleft>bop\<guillemotright> e2) n = (bsok e1 n \<and> bsok e2 n)"
  "bsok (Var V) n = True"
  "bsok (Val v) n = True"
  "bsok (V := e) n = bsok e n"
  "bsok (a\<lfloor>i\<rceil>) n = (bsok a n \<and> bsok i n)"
  "bsok (a\<lfloor>i\<rceil> := e) n = (bsok a n \<and> bsok i n \<and> bsok e n)"
  "bsok (a\<bullet>length) n = bsok a n"
  "bsok (e\<bullet>F{D}) n = bsok e n"
  "bsok (e\<bullet>F{D} := e') n = (bsok e n \<and> bsok e' n)"
  "bsok (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) n = (bsok e n \<and> bsok e' n \<and> bsok e'' n)"
  "bsok (e\<bullet>M(ps)) n = (bsok e n \<and> bsoks ps n)"
  "bsok {V:T=vo; e} n = (bsok e (Suc n) \<and> V = n)"
  "bsok (sync\<^bsub>V\<^esub> (e) e') n = (bsok e n \<and> bsok e' (Suc n) \<and> V = n)"
  "bsok (insync\<^bsub>V\<^esub> (ad) e) n = False"
  "bsok (e;; e') n = (bsok e n \<and> bsok e' n)"
  "bsok (if (e) e1 else e2) n = (bsok e n \<and> bsok e1 n \<and> bsok e2 n)"
  "bsok (while (b) c) n = (bsok b n \<and> bsok c n)"
  "bsok (throw e) n = bsok e n"
  "bsok (try e catch(C V) e') n = (bsok e n \<and> bsok e' (Suc n) \<and> V = n)"
  and bsoks_simps [simp]:
  "bsoks [] n = True"
  "bsoks (e # es) n = (bsok e n \<and> bsoks es n)"
by(auto simp add: bsok_def bsoks_def fun_eq_iff)

lemma call1_callE:
  assumes "call1 (obj\<bullet>M(pns)) = \<lfloor>(a, M', vs)\<rfloor>"
  obtains (CallObj) "call1 obj = \<lfloor>(a, M', vs)\<rfloor>"
  | (CallParams) v where "obj = Val v" "calls1 pns = \<lfloor>(a, M', vs)\<rfloor>"
  | (Call) "obj = addr a" "pns = map Val vs" "M = M'"
using assms by(auto split: if_split_asm simp add: is_vals_conv)

lemma calls1_map_Val_append [simp]:
  "calls1 (map Val vs @ es) = calls1 es"
by(induct vs) simp_all

lemma calls1_map_Val [simp]:
  "calls1 (map Val vs) = None"
by(induct vs) simp_all

lemma fixes e :: "('a, 'b, 'addr) exp" and es :: "('a, 'b, 'addr) exp list"
  shows call1_imp_call: "call1 e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> call e = \<lfloor>aMvs\<rfloor>"
  and calls1_imp_calls: "calls1 es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> calls es = \<lfloor>aMvs\<rfloor>"
by(induct e and es rule: call1.induct calls1.induct) auto

lemma max_vars_inline_call: "max_vars (inline_call e' e) \<le> max_vars e + max_vars e'"
  and max_varss_inline_calls: "max_varss (inline_calls e' es) \<le> max_varss es + max_vars e'"
by(induct e and es rule: call1.induct calls1.induct) auto

lemmas inline_call_max_vars1 = max_vars_inline_call
lemmas inline_calls_max_varss1 = max_varss_inline_calls

end
