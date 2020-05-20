(*  Title:      JinjaThreads/Common/CallExpr.thy
    Author:     Andreas Lochbihler
*)

chapter \<open>Compilation \label{cha:comp}\<close>

section \<open>Method calls in expressions\<close>

theory CallExpr imports 
  "../J/Expr"
begin

fun inline_call :: "('a,'b,'addr) exp \<Rightarrow> ('a,'b,'addr) exp \<Rightarrow> ('a,'b,'addr) exp"
  and inline_calls :: "('a,'b,'addr) exp \<Rightarrow> ('a,'b,'addr) exp list \<Rightarrow> ('a,'b,'addr) exp list"
where
  "inline_call f (new C) = new C"
| "inline_call f (newA T\<lfloor>e\<rceil>) = newA T\<lfloor>inline_call f e\<rceil>"
| "inline_call f (Cast C e) = Cast C (inline_call f e)"
| "inline_call f (e instanceof T) = (inline_call f e) instanceof T"
| "inline_call f (Val v) = Val v"
| "inline_call f (Var V) = Var V"
| "inline_call f (V:=e) = V := inline_call f e"
| "inline_call f (e \<guillemotleft>bop\<guillemotright> e') = (if is_val e then (e \<guillemotleft>bop\<guillemotright> inline_call f e') else (inline_call f e \<guillemotleft>bop\<guillemotright> e'))"
| "inline_call f (a\<lfloor>i\<rceil>) = (if is_val a then a\<lfloor>inline_call f i\<rceil> else (inline_call f a)\<lfloor>i\<rceil>)"
| "inline_call f (AAss a i e) =
   (if is_val a then if is_val i then AAss a i (inline_call f e) else AAss a (inline_call f i) e
    else AAss (inline_call f a) i e)"
| "inline_call f (a\<bullet>length) = inline_call f a\<bullet>length"
| "inline_call f (e\<bullet>F{D}) = inline_call f e\<bullet>F{D}"
| "inline_call f (FAss e F D e') = (if is_val e then FAss e F D (inline_call f e') else FAss (inline_call f e) F D e')"
| "inline_call f (CompareAndSwap e D F e' e'') = 
   (if is_val e then if is_val e' then CompareAndSwap e D F e' (inline_call f e'') 
     else CompareAndSwap e D F (inline_call f e') e''
    else CompareAndSwap (inline_call f e) D F e' e'')"
| "inline_call f (e\<bullet>M(es)) = 
   (if is_val e then if is_vals es \<and> is_addr e then f else e\<bullet>M(inline_calls f es) else inline_call f e\<bullet>M(es))"
| "inline_call f ({V:T=vo; e}) = {V:T=vo; inline_call f e}"
| "inline_call f (sync\<^bsub>V\<^esub> (o') e) = sync\<^bsub>V\<^esub> (inline_call f o') e"
| "inline_call f (insync\<^bsub>V\<^esub> (a) e) = insync\<^bsub>V\<^esub> (a) (inline_call f e)"
| "inline_call f (e;;e') = inline_call f e;;e'"
| "inline_call f (if (b) e else e') = (if (inline_call f b) e else e')"
| "inline_call f (while (b) e) = while (b) e"
| "inline_call f (throw e) = throw (inline_call f e)"
| "inline_call f (try e1 catch(C V) e2) = try inline_call f e1 catch(C V) e2"

| "inline_calls f [] = []"
| "inline_calls f (e#es) = (if is_val e then e # inline_calls f es else inline_call f e # es)"

fun collapse :: "'addr expr \<times> 'addr expr list \<Rightarrow> 'addr expr" where
  "collapse (e, []) = e"
| "collapse (e, (e' # es)) = collapse (inline_call e e', es)"

definition is_call :: "('a, 'b, 'addr) exp \<Rightarrow> bool"
where "is_call e = (call e \<noteq> None)"

definition is_calls :: "('a, 'b, 'addr) exp list \<Rightarrow> bool"
where "is_calls es = (calls es \<noteq> None)"



lemma inline_calls_map_Val_append [simp]:
  "inline_calls f (map Val vs @ es) = map Val vs @ inline_calls f es"
by(induct vs, auto)

lemma inline_call_eq_Val_aux:
  "inline_call e E = Val v \<Longrightarrow> call E = \<lfloor>aMvs\<rfloor> \<Longrightarrow> e = Val v"
by(induct E)(auto split: if_split_asm)

lemmas inline_call_eq_Val [dest] = inline_call_eq_Val_aux inline_call_eq_Val_aux[OF sym, THEN sym]

lemma inline_calls_eq_empty [simp]: "inline_calls e es = [] \<longleftrightarrow> es = []"
by(cases es, auto)

lemma inline_calls_map_Val [simp]: "inline_calls e (map Val vs) = map Val vs"
by(induct vs) auto

lemma  fixes E :: "('a,'b, 'addr) exp" and Es :: "('a,'b, 'addr) exp list"
  shows inline_call_eq_Throw [dest]: "inline_call e E = Throw a \<Longrightarrow> call E = \<lfloor>aMvs\<rfloor> \<Longrightarrow> e = Throw a \<or> e = addr a"
by(induct E rule: exp.induct)(fastforce split:if_split_asm)+

lemma Throw_eq_inline_call_eq [dest]:
  "inline_call e E = Throw a \<Longrightarrow> call E = \<lfloor>aMvs\<rfloor> \<Longrightarrow> Throw a = e \<or> addr a = e"
by(auto dest: inline_call_eq_Throw[OF sym])

lemma is_vals_inline_calls [dest]:
  "\<lbrakk> is_vals (inline_calls e es); calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> is_val e"
by(induct es, auto split: if_split_asm)

lemma [dest]: "\<lbrakk> inline_calls e es = map Val vs; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> is_val e"
              "\<lbrakk> map Val vs = inline_calls e es; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> is_val e"
by(fastforce intro!: is_vals_inline_calls del: is_val.intros simp add: is_vals_conv elim: sym)+

lemma inline_calls_eq_Val_Throw [dest]:
  "\<lbrakk> inline_calls e es = map Val vs @ Throw a # es'; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> e = Throw a \<or> is_val e"
apply(induct es arbitrary: vs a es')
apply(auto simp add: Cons_eq_append_conv split: if_split_asm)
done

lemma Val_Throw_eq_inline_calls [dest]:
  "\<lbrakk> map Val vs @ Throw a # es' = inline_calls e es; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> Throw a = e \<or> is_val e"
by(auto dest: inline_calls_eq_Val_Throw[OF sym])

declare option.split [split del] if_split_asm [split]  if_split [split del]

lemma call_inline_call [simp]:
  "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> call (inline_call {v:T=vo; e'} e) = call e'"
  "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> calls (inline_calls {v:T=vo;e'} es) = call e'"
apply(induct e and es rule: call.induct calls.induct)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce split: if_split)
apply(fastforce)
apply(fastforce)
apply(fastforce split: if_split)
apply(clarsimp)
 apply(fastforce split: if_split)
apply(fastforce split: if_split)
apply(fastforce)
apply(fastforce)
apply(fastforce split: if_split)
apply(fastforce split: if_split)
apply(fastforce split: if_split)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce split: if_split)
done

declare option.split [split] if_split [split] if_split_asm [split del]

lemma fv_inline_call: "fv (inline_call e' e) \<subseteq> fv e \<union> fv e'"
  and fvs_inline_calls: "fvs (inline_calls e' es) \<subseteq> fvs es \<union> fv e'"
by(induct e and es rule: call.induct calls.induct)(fastforce split: if_split_asm)+

lemma contains_insync_inline_call_conv:
  "contains_insync (inline_call e e') \<longleftrightarrow> contains_insync e \<and> call e' \<noteq> None \<or> contains_insync e'"
  and contains_insyncs_inline_calls_conv:
  "contains_insyncs (inline_calls e es') \<longleftrightarrow> contains_insync e \<and> calls es' \<noteq> None \<or> contains_insyncs es'"
by(induct e' and es' rule: call.induct calls.induct)(auto split: if_split_asm simp add: is_vals_conv)

lemma contains_insync_inline_call [simp]:
  "call e' = \<lfloor>aMvs\<rfloor> \<Longrightarrow> contains_insync (inline_call e e') \<longleftrightarrow> contains_insync e \<or> contains_insync e'"
  and contains_insyncs_inline_calls [simp]:
  "calls es' = \<lfloor>aMvs\<rfloor> \<Longrightarrow> contains_insyncs (inline_calls e es') \<longleftrightarrow> contains_insync e \<or> contains_insyncs es'"
by(simp_all add: contains_insync_inline_call_conv contains_insyncs_inline_calls_conv)

lemma collapse_append [simp]:
  "collapse (e, es @ es') = collapse (collapse (e, es), es')"
by(induct es arbitrary: e, auto)

lemma collapse_conv_foldl:
  "collapse (e, es) = foldl inline_call e es"
by(induct es arbitrary: e) simp_all

lemma fv_collapse: "\<forall>e \<in> set es. is_call e \<Longrightarrow> fv (collapse (e, es)) \<subseteq> fvs (e # es)"
apply(induct es arbitrary: e)
apply(insert fv_inline_call)
apply(fastforce dest: subsetD)+
done

lemma final_inline_callD: "\<lbrakk> final (inline_call E e); is_call e \<rbrakk> \<Longrightarrow> final E"
by(induct e)(auto simp add: is_call_def split: if_split_asm)

lemma collapse_finalD: "\<lbrakk> final (collapse (e, es)); \<forall>e\<in>set es. is_call e \<rbrakk> \<Longrightarrow> final e"
by(induct es arbitrary: e)(auto dest: final_inline_callD)

context heap_base begin

definition synthesized_call :: "'m prog \<Rightarrow> 'heap \<Rightarrow> ('addr \<times> mname \<times> 'addr val list) \<Rightarrow> bool"
where
  "synthesized_call P h = 
   (\<lambda>(a, M, vs). \<exists>T Ts Tr D. typeof_addr h a = \<lfloor>T\<rfloor> \<and> P \<turnstile> class_type_of T sees M:Ts\<rightarrow>Tr = Native in D)"

lemma synthesized_call_conv:
  "synthesized_call P h (a, M, vs) = 
   (\<exists>T Ts Tr D. typeof_addr h a = \<lfloor>T\<rfloor> \<and> P \<turnstile> class_type_of T sees M:Ts\<rightarrow>Tr = Native in D)"
by(simp add: synthesized_call_def)

end

end
