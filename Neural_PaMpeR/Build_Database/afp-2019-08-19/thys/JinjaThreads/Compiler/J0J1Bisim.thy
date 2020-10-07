(*  Title:      JinjaThreads/Compiler/J0J1Bisim.thy
    Author:     Andreas Lochbihler

    Reminiscent of the Jinja theory Compiler/Correctness1
*)

section \<open>The bisimulation relation betwenn source and intermediate language\<close>

theory J0J1Bisim imports
  J1
  J1WellForm
  Compiler1
  "../J/JWellForm"
  J0
begin

subsection\<open>Correctness of program compilation\<close>

primrec unmod :: "'addr expr1 \<Rightarrow> nat \<Rightarrow> bool"
  and unmods :: "'addr expr1 list \<Rightarrow> nat \<Rightarrow> bool"
where
  "unmod (new C) i = True"
| "unmod (newA T\<lfloor>e\<rceil>) i = unmod e i"
| "unmod (Cast C e) i = unmod e i"
| "unmod (e instanceof T) i = unmod e i"
| "unmod (Val v) i = True"
| "unmod (e1 \<guillemotleft>bop\<guillemotright> e2) i = (unmod e1 i \<and> unmod e2 i)"
| "unmod (Var i) j = True"
| "unmod (i:=e) j = (i \<noteq> j \<and> unmod e j)"
| "unmod (a\<lfloor>i\<rceil>) j = (unmod a j \<and> unmod i j)"
| "unmod (a\<lfloor>i\<rceil>:=e) j = (unmod a j \<and> unmod i j \<and> unmod e j)"
| "unmod (a\<bullet>length) j = unmod a j"
| "unmod (e\<bullet>F{D}) i = unmod e i"
| "unmod (e1\<bullet>F{D}:=e2) i = (unmod e1 i \<and> unmod e2 i)"
| "unmod (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) i = (unmod e1 i \<and> unmod e2 i \<and> unmod e3 i)"
| "unmod (e\<bullet>M(es)) i = (unmod e i \<and> unmods es i)"
| "unmod {j:T=vo; e} i = ((i = j \<longrightarrow> vo = None) \<and> unmod e i)"
| "unmod (sync\<^bsub>V\<^esub> (o') e) i = (unmod o' i \<and> unmod e i \<and> i \<noteq> V)"
| "unmod (insync\<^bsub>V\<^esub> (a) e) i = unmod e i"
| "unmod (e1;;e2) i = (unmod e1 i \<and> unmod e2 i)"
| "unmod (if (e) e\<^sub>1 else e\<^sub>2) i = (unmod e i \<and> unmod e\<^sub>1 i \<and> unmod e\<^sub>2 i)"
| "unmod (while (e) c) i = (unmod e i \<and> unmod c i)"
| "unmod (throw e) i = unmod e i"
| "unmod (try e\<^sub>1 catch(C i) e\<^sub>2) j = (unmod e\<^sub>1 j \<and> (if i=j then False else unmod e\<^sub>2 j))"

| "unmods ([]) i = True"
| "unmods (e#es) i = (unmod e i \<and> unmods es i)"

lemma unmods_map_Val [simp]: "unmods (map Val vs) V"
by(induct vs) simp_all

lemma fixes e :: "'addr expr" and es :: "'addr expr list"
  shows hidden_unmod: "hidden Vs i \<Longrightarrow> unmod (compE1 Vs e) i"
  and hidden_unmods: "hidden Vs i \<Longrightarrow> unmods (compEs1 Vs es) i"
apply(induct Vs e and Vs es rule: compE1_compEs1_induct)
apply (simp_all add:hidden_inacc)
apply(auto simp add:hidden_def)
done

lemma unmod_extRet2J [simp]: "unmod e i \<Longrightarrow> unmod (extRet2J e va) i"
by(cases va) simp_all

lemma max_dest: "(n :: nat) + max a b \<le> c \<Longrightarrow> n + a \<le> c \<and> n + b \<le> c"
apply(auto simp add: max_def split: if_split_asm) 
done

declare max_dest [dest!]

lemma fixes e :: "'addr expr" and es :: "'addr expr list"
  shows fv_unmod_compE1: "\<lbrakk> i < length Vs; Vs ! i \<notin> fv e \<rbrakk> \<Longrightarrow> unmod (compE1 Vs e) i"
  and fvs_unmods_compEs1: "\<lbrakk> i < length Vs; Vs ! i \<notin> fvs es \<rbrakk> \<Longrightarrow> unmods (compEs1 Vs es) i"
proof(induct Vs e and Vs es rule: compE1_compEs1_induct)
  case (Block Vs V ty vo exp)
  note IH = \<open>\<lbrakk>i < length (Vs @ [V]); (Vs @ [V]) ! i \<notin> fv exp \<rbrakk> \<Longrightarrow> unmod (compE1 (Vs @ [V]) exp) i\<close>
  note len = \<open>i < length Vs\<close>
  hence i: "i < length (Vs @ [V])" by simp
  show ?case
  proof(cases "Vs ! i = V")
    case True
    from len have "hidden (Vs @ [Vs ! i]) i" by(rule hidden_snoc_nth)
    with len True show ?thesis by(auto intro: hidden_unmod)
  next
    case False
    with \<open>Vs ! i \<notin> fv {V:ty=vo; exp}\<close> len have "(Vs @ [V]) ! i \<notin> fv exp"
      by(auto simp add: nth_append)
    from IH[OF i this] len show ?thesis by(auto)
  qed
next
  case (TryCatch Vs e1 C V e2)
  note IH1 = \<open>\<lbrakk>i < length Vs; Vs ! i \<notin> fv e1 \<rbrakk> \<Longrightarrow> unmod (compE1 Vs e1) i\<close>
  note IH2 = \<open>\<lbrakk>i < length (Vs @ [V]); (Vs @ [V]) ! i \<notin> fv e2 \<rbrakk> \<Longrightarrow> unmod (compE1 (Vs @ [V]) e2) i\<close>
  note len = \<open>i < length Vs\<close>
  hence i: "i < length (Vs @ [V])" by simp
  have "unmod (compE1 (Vs @ [V]) e2) i"
  proof(cases "Vs ! i = V")
    case True
    from len have "hidden (Vs @ [Vs ! i]) i" by(rule hidden_snoc_nth)
    with len True show ?thesis by(auto intro: hidden_unmod)
  next
    case False
    with \<open>Vs ! i \<notin> fv (try e1 catch(C V) e2)\<close> len have "(Vs @ [V]) ! i \<notin> fv e2"
      by(auto simp add: nth_append)
    from IH2[OF i this] len show ?thesis by(auto)
  qed
  with IH1[OF len] \<open>Vs ! i \<notin> fv (try e1 catch(C V) e2)\<close> len show ?case by(auto)
qed(auto dest: index_le_lengthD simp add: nth_append)

lemma hidden_lengthD: "hidden Vs i \<Longrightarrow> i < length Vs"
by(simp add: hidden_def)

lemma fixes e :: "'addr expr1" and es :: "'addr expr1 list"
  shows fv_B_unmod: "\<lbrakk> V \<notin> fv e; \<B> e n; V < n \<rbrakk> \<Longrightarrow> unmod e V"
  and fvs_Bs_unmods: "\<lbrakk> V \<notin> fvs es; \<B>s es n; V < n \<rbrakk> \<Longrightarrow> unmods es V"
by(induct e and es arbitrary: n and n rule: unmod.induct unmods.induct) auto

lemma assumes fin: "final e'"
  shows unmod_inline_call: "unmod (inline_call e' e) V \<longleftrightarrow> unmod e V"
  and unmods_inline_calls: "unmods (inline_calls e' es) V \<longleftrightarrow> unmods es V"
apply(induct e and es rule: unmod.induct unmods.induct)
apply(insert fin)
apply(auto simp add: is_vals_conv)
done

subsection \<open>The delay bisimulation relation\<close>

text \<open>Delay bisimulation for expressions\<close>

inductive bisim :: "vname list \<Rightarrow> 'addr expr \<Rightarrow> 'addr expr1 \<Rightarrow> 'addr val list \<Rightarrow> bool"
  and bisims :: "vname list \<Rightarrow> 'addr expr list \<Rightarrow> 'addr expr1 list \<Rightarrow> 'addr val list \<Rightarrow> bool"
where
  bisimNew: "bisim Vs (new C) (new C) xs"
| bisimNewArray: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (newA T\<lfloor>e\<rceil>) (newA T\<lfloor>e'\<rceil>) xs"
| bisimCast: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (Cast T e) (Cast T e') xs"
| bisimInstanceOf: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (e instanceof T) (e' instanceof T) xs"
| bisimVal: "bisim Vs (Val v) (Val v) xs"
| bisimBinOp1:
  "\<lbrakk> bisim Vs e e' xs; \<not> is_val e; \<not> contains_insync e'' \<rbrakk> \<Longrightarrow> bisim Vs (e \<guillemotleft>bop\<guillemotright> e'') (e' \<guillemotleft>bop\<guillemotright> compE1 Vs e'') xs"
| bisimBinOp2: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (Val v \<guillemotleft>bop\<guillemotright> e) (Val v \<guillemotleft>bop\<guillemotright> e') xs"
| bisimVar: "bisim Vs (Var V) (Var (index Vs V)) xs"
| bisimLAss: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (V:=e) (index Vs V:=e') xs"
| bisimAAcc1: "\<lbrakk> bisim Vs a a' xs; \<not> is_val a; \<not> contains_insync i \<rbrakk> \<Longrightarrow> bisim Vs (a\<lfloor>i\<rceil>) (a'\<lfloor>compE1 Vs i\<rceil>) xs"
| bisimAAcc2: "bisim Vs i i' xs \<Longrightarrow> bisim Vs (Val v\<lfloor>i\<rceil>) (Val v\<lfloor>i'\<rceil>) xs"
| bisimAAss1:
  "\<lbrakk> bisim Vs a a' xs; \<not> is_val a; \<not> contains_insync i; \<not> contains_insync e \<rbrakk>
  \<Longrightarrow> bisim Vs (a\<lfloor>i\<rceil>:=e) (a'\<lfloor>compE1 Vs i\<rceil>:=compE1 Vs e) xs"
| bisimAAss2: "\<lbrakk> bisim Vs i i' xs; \<not> is_val i; \<not> contains_insync e \<rbrakk> \<Longrightarrow> bisim Vs (Val v\<lfloor>i\<rceil>:=e) (Val v\<lfloor>i'\<rceil>:=compE1 Vs e) xs"
| bisimAAss3: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (Val v\<lfloor>Val i\<rceil> := e) (Val v\<lfloor>Val i\<rceil> := e') xs"
| bisimALength: "bisim Vs a a' xs \<Longrightarrow> bisim Vs (a\<bullet>length) (a'\<bullet>length) xs"
| bisimFAcc: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (e\<bullet>F{D}) (e'\<bullet>F{D}) xs"
| bisimFAss1: "\<lbrakk> bisim Vs e e' xs; \<not> is_val e; \<not> contains_insync e'' \<rbrakk> \<Longrightarrow> bisim Vs (e\<bullet>F{D}:=e'') (e'\<bullet>F{D}:=compE1 Vs e'') xs"
| bisimFAss2: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (Val v\<bullet>F{D} := e) (Val v\<bullet>F{D} := e') xs"
| bisimCAS1: "\<lbrakk> bisim Vs e e' xs; \<not> is_val e; \<not> contains_insync e2; \<not> contains_insync e3 \<rbrakk> 
  \<Longrightarrow> bisim Vs (e\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) (e'\<bullet>compareAndSwap(D\<bullet>F, compE1 Vs e2, compE1 Vs e3)) xs"
| bisimCAS2: "\<lbrakk> bisim Vs e e' xs; \<not> is_val e; \<not> contains_insync e3 \<rbrakk> 
  \<Longrightarrow> bisim Vs (Val v\<bullet>compareAndSwap(D\<bullet>F, e, e3)) (Val v\<bullet>compareAndSwap(D\<bullet>F, e', compE1 Vs e3)) xs"
| bisimCAS3: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e)) (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e')) xs"
| bisimCallObj: "\<lbrakk> bisim Vs e e' xs; \<not> is_val e; \<not> contains_insyncs es \<rbrakk> \<Longrightarrow> bisim Vs (e\<bullet>M(es)) (e'\<bullet>M(compEs1 Vs es)) xs"
| bisimCallParams: "bisims Vs es es' xs \<Longrightarrow> bisim Vs (Val v\<bullet>M(es)) (Val v\<bullet>M(es')) xs"
| bisimBlockNone: "bisim (Vs@[V]) e e' xs \<Longrightarrow> bisim Vs {V:T=None; e} {(length Vs):T=None; e'} xs"
| bisimBlockSome: "\<lbrakk> bisim (Vs@[V]) e e' (xs[length Vs := v]) \<rbrakk> \<Longrightarrow> bisim Vs {V:T=\<lfloor>v\<rfloor>; e} {(length Vs):T=\<lfloor>v\<rfloor>; e'} xs"
| bisimBlockSomeNone: "\<lbrakk> bisim (Vs@[V]) e e' xs; xs ! (length Vs) = v \<rbrakk> \<Longrightarrow> bisim Vs {V:T=\<lfloor>v\<rfloor>; e} {(length Vs):T=None; e'} xs"
| bisimSynchronized:
  "\<lbrakk> bisim Vs o' o'' xs; \<not> contains_insync e \<rbrakk>
  \<Longrightarrow> bisim Vs (sync(o') e) (sync\<^bsub>length Vs\<^esub>(o'') (compE1 (Vs@[fresh_var Vs]) e)) xs"
| bisimInSynchronized:
  "\<lbrakk> bisim (Vs@[fresh_var Vs]) e e' xs; xs ! length Vs = Addr a \<rbrakk> \<Longrightarrow> bisim Vs (insync(a) e) (insync\<^bsub>length Vs\<^esub>(a) e') xs"
| bisimSeq: "\<lbrakk> bisim Vs e e' xs; \<not> contains_insync e'' \<rbrakk> \<Longrightarrow> bisim Vs (e;;e'') (e';;compE1 Vs e'') xs"
| bisimCond:
  "\<lbrakk> bisim Vs e e' xs; \<not> contains_insync e1; \<not> contains_insync e2 \<rbrakk>
  \<Longrightarrow> bisim Vs (if (e) e1 else e2) (if (e') (compE1 Vs e1) else (compE1 Vs e2)) xs"
| bisimWhile:
  "\<lbrakk> \<not> contains_insync b; \<not> contains_insync e \<rbrakk> \<Longrightarrow> bisim Vs (while (b) e) (while (compE1 Vs b) (compE1 Vs e)) xs"
| bisimThrow: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (throw e) (throw e') xs"
| bisimTryCatch:
  "\<lbrakk> bisim Vs e e' xs; \<not> contains_insync e'' \<rbrakk>
  \<Longrightarrow> bisim Vs (try e catch(C V) e'') (try e' catch(C (length Vs)) compE1 (Vs@[V]) e'') xs"

| bisimsNil: "bisims Vs [] [] xs"
| bisimsCons1: "\<lbrakk> bisim Vs e e' xs; \<not> is_val e; \<not> contains_insyncs es \<rbrakk> \<Longrightarrow> bisims Vs (e # es) (e' # compEs1 Vs es) xs"
| bisimsCons2: "bisims Vs es es' xs \<Longrightarrow> bisims Vs (Val v # es) (Val v # es') xs"

declare bisimNew [iff]
declare bisimVal [iff]
declare bisimVar [iff]
declare bisimWhile [iff]
declare bisimsNil [iff]

declare bisim_bisims.intros [intro!]
declare bisimsCons1 [rule del, intro] bisimsCons2 [rule del, intro]
  bisimBinOp1 [rule del, intro] bisimAAcc1 [rule del, intro]
  bisimAAss1 [rule del, intro] bisimAAss2 [rule del, intro]
  bisimFAss1 [rule del, intro]
  bisimCAS1 [rule del, intro] bisimCAS2 [rule del, intro]
  bisimCallObj [rule del, intro] 

inductive_cases bisim_safe_cases [elim!]:
  "bisim Vs (new C) e' xs"
  "bisim Vs (newA T\<lfloor>e\<rceil>) e' xs"
  "bisim Vs (Cast T e) e' xs"
  "bisim Vs (e instanceof T) e' xs"
  "bisim Vs (Val v) e' xs"
  "bisim Vs (Var V) e' xs"
  "bisim Vs (V:=e) e' xs"
  "bisim Vs (Val v\<lfloor>i\<rceil>) e' xs"
  "bisim Vs (Val v\<lfloor>Val v'\<rceil> := e) e' xs"
  "bisim Vs (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e)) e' xs"
  "bisim Vs (a\<bullet>length) e' xs"
  "bisim Vs (e\<bullet>F{D}) e' xs"
  "bisim Vs (sync(o') e) e' xs"
  "bisim Vs (insync(a) e) e' xs"
  "bisim Vs (e;;e') e'' xs"
  "bisim Vs (if (b) e1 else e2) e' xs"
  "bisim Vs (while (b) e) e' xs"
  "bisim Vs (throw e) e' xs"
  "bisim Vs (try e catch(C V) e') e'' xs"
  "bisim Vs e' (new C) xs"
  "bisim Vs e' (newA T\<lfloor>e\<rceil>) xs"
  "bisim Vs e' (Cast T e) xs"
  "bisim Vs e' (e instanceof T) xs"
  "bisim Vs e' (Val v) xs"
  "bisim Vs e' (Var V) xs"
  "bisim Vs e' (V:=e) xs"
  "bisim Vs e' (Val v\<lfloor>i\<rceil>) xs"
  "bisim Vs e' (Val v\<lfloor>Val v'\<rceil> := e) xs"
  "bisim Vs e' (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e)) xs"
  "bisim Vs e' (a\<bullet>length) xs"
  "bisim Vs e' (e\<bullet>F{D}) xs"
  "bisim Vs e' (sync\<^bsub>V\<^esub> (o') e) xs"
  "bisim Vs e' (insync\<^bsub>V\<^esub> (a) e) xs"
  "bisim Vs e'' (e;;e') xs"
  "bisim Vs e' (if (b) e1 else e2) xs"
  "bisim Vs e' (while (b) e) xs"
  "bisim Vs e' (throw e) xs"
  "bisim Vs e'' (try e catch(C V) e') xs"

inductive_cases bisim_cases [elim]:
  "bisim Vs (e1 \<guillemotleft>bop\<guillemotright> e2) e' xs"
  "bisim Vs (a\<lfloor>i\<rceil>) e' xs"
  "bisim Vs (a\<lfloor>i\<rceil>:=e) e' xs"
  "bisim Vs (e\<bullet>F{D}:=e') e'' xs"
  "bisim Vs (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) e''' xs"
  "bisim Vs (e\<bullet>M(es)) e' xs"
  "bisim Vs {V:T=vo; e} e' xs"
  "bisim Vs e' (e1 \<guillemotleft>bop\<guillemotright> e2) xs"
  "bisim Vs e' (a\<lfloor>i\<rceil>) xs"
  "bisim Vs e' (a\<lfloor>i\<rceil>:=e) xs"
  "bisim Vs e'' (e\<bullet>F{D}:=e') xs"
  "bisim Vs e''' (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) xs"
  "bisim Vs e' (e\<bullet>M(es)) xs"
  "bisim Vs e' {V:T=vo; e} xs"

inductive_cases bisims_safe_cases [elim!]:
  "bisims Vs [] es xs"
  "bisims Vs es [] xs"

inductive_cases bisims_cases [elim]:
  "bisims Vs (e # es) es' xs"
  "bisims Vs es' (e # es) xs"

text \<open>Delay bisimulation for call stacks\<close>

inductive bisim01 :: "'addr expr \<Rightarrow> 'addr expr1 \<times> 'addr locals1 \<Rightarrow> bool"
where
  "\<lbrakk> bisim [] e e' xs; fv e = {}; \<D> e \<lfloor>{}\<rfloor>; max_vars e' \<le> length xs; call e = \<lfloor>aMvs\<rfloor>; call1 e' = \<lfloor>aMvs\<rfloor> \<rbrakk>
  \<Longrightarrow> bisim01 e (e', xs)"

inductive bisim_list :: "'addr expr list \<Rightarrow> ('addr expr1 \<times> 'addr locals1) list \<Rightarrow> bool"
where
  bisim_listNil: "bisim_list [] []"
| bisim_listCons: 
  "\<lbrakk> bisim_list es exs'; bisim [] e e' xs; 
     fv e = {}; \<D> e \<lfloor>{}\<rfloor>;
     max_vars e' \<le> length xs;
     call e = \<lfloor>aMvs\<rfloor>; call1 e' = \<lfloor>aMvs\<rfloor> \<rbrakk>
  \<Longrightarrow> bisim_list (e # es) ((e', xs) # exs')"

inductive_cases bisim_list_cases [elim!]:
 "bisim_list [] exs'"
 "bisim_list (ex # exs) exs'"
 "bisim_list exs (ex' # exs')"

fun bisim_list1 :: 
  "'addr expr \<times> 'addr expr list \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list \<Rightarrow> bool"
where
  "bisim_list1 (e, es) ((e1, xs1), exs1) \<longleftrightarrow> 
   bisim_list es exs1 \<and> bisim [] e e1 xs1 \<and> fv e = {} \<and> \<D> e \<lfloor>{}\<rfloor> \<and> max_vars e1 \<le> length xs1"

definition bisim_red0_Red1 :: 
  "(('addr expr \<times> 'addr expr list) \<times> 'heap)
  \<Rightarrow> ((('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list) \<times> 'heap) \<Rightarrow> bool"
where "bisim_red0_Red1 \<equiv> (\<lambda>(es, h) (exs, h'). bisim_list1 es exs \<and> h = h')"

abbreviation ta_bisim01 ::
  "('addr, 'thread_id, 'heap) J0_thread_action \<Rightarrow> ('addr, 'thread_id, 'heap) J1_thread_action \<Rightarrow> bool" 
where
  "ta_bisim01 \<equiv> ta_bisim (\<lambda>t. bisim_red0_Red1)"

definition bisim_wait01 ::
  "('addr expr \<times> 'addr expr list) \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list \<Rightarrow> bool"
where "bisim_wait01 \<equiv> \<lambda>(e0, es0) ((e1, xs1), exs1). call e0 \<noteq> None \<and> call1 e1 \<noteq> None"

lemma bisim_list1I[intro?]:
  "\<lbrakk> bisim_list es exs1; bisim [] e e1 xs1; fv e = {};
     \<D> e \<lfloor>{}\<rfloor>; max_vars e1 \<le> length xs1 \<rbrakk>
  \<Longrightarrow> bisim_list1 (e, es) ((e1, xs1), exs1)"
by simp

lemma bisim_list1E[elim?]:
  assumes "bisim_list1 (e, es) ((e1, xs1), exs1)"
  obtains "bisim_list es exs1" "bisim [] e e1 xs1" "fv e = {}" "\<D> e \<lfloor>{}\<rfloor>" "max_vars e1 \<le> length xs1"
using assms by auto

lemma bisim_list1_elim:
  assumes "bisim_list1 es' exs"
  obtains e es e1 xs1 exs1
  where "es' = (e, es)" "exs = ((e1, xs1), exs1)"
  and "bisim_list es exs1" "bisim [] e e1 xs1" "fv e = {}" "\<D> e \<lfloor>{}\<rfloor>" "max_vars e1 \<le> length xs1"
using assms by(cases es')(cases exs, fastforce)

declare bisim_list1.simps [simp del]


lemma bisims_map_Val_conv [simp]: "bisims Vs (map Val vs) es xs = (es = map Val vs)"
apply(induct vs arbitrary: es)
 apply(fastforce)
apply(simp)
apply(rule iffI)
apply(erule bisims_cases, auto)
done

declare compEs1_conv_map [simp del]

lemma bisim_contains_insync: "bisim Vs e e' xs \<Longrightarrow> contains_insync e = contains_insync e'"
  and bisims_contains_insyncs: "bisims Vs es es' xs \<Longrightarrow> contains_insyncs es = contains_insyncs es'"
by(induct rule: bisim_bisims.inducts)(auto)

lemma bisims_map_Val_Throw: 
  "bisims Vs (map Val vs @ Throw a # es) es' xs \<longleftrightarrow> es' = map Val vs @ Throw a # compEs1 Vs es \<and> \<not> contains_insyncs es"
apply(induct vs arbitrary: es')
 apply(simp)
 apply(fastforce simp add: compEs1_conv_map)
apply(fastforce elim!: bisims_cases intro: bisimsCons2)
done

lemma compE1_bisim [intro]: "\<lbrakk> fv e \<subseteq> set Vs; \<not> contains_insync e \<rbrakk> \<Longrightarrow> bisim Vs e (compE1 Vs e) xs"
  and compEs1_bisims [intro]: "\<lbrakk> fvs es \<subseteq> set Vs; \<not> contains_insyncs es \<rbrakk> \<Longrightarrow> bisims Vs es (compEs1 Vs es) xs"
proof(induct Vs e and Vs es arbitrary: xs and xs rule: compE1_compEs1_induct)
  case (BinOp Vs exp1 bop exp2 x)
  thus ?case by(cases "is_val exp1")(auto)
next
  case (AAcc Vs exp1 exp2 x)
  thus ?case by(cases "is_val exp1")(auto)
next
  case (AAss Vs exp1 exp2 exp3 x)
  thus ?case by(cases "is_val exp1", cases "is_val exp2", fastforce+)
next
  case (FAss Vs exp1 F D exp2 x)
  thus ?case by(cases "is_val exp1", auto)
next
  case (CAS Vs e1 D F e2 e3 x)
  thus ?case by(cases "is_val e1", cases "is_val e2", fastforce+)
next
  case (Call Vs obj M params x)
  thus ?case by(cases "is_val obj")(auto)
next
  case (Block Vs V T vo exp xs)
  from \<open>fv {V:T=vo; exp} \<subseteq> set Vs\<close> have "fv exp \<subseteq> set (Vs@[V])" by(auto)
  with Block show ?case by(cases vo)(auto)
next
  case (Cons Vs exp list x)
  thus ?case by(cases "is_val exp")(auto intro!: bisimsCons2)
qed(auto)

lemma bisim_hidden_unmod: "\<lbrakk> bisim Vs e e' xs; hidden Vs i \<rbrakk> \<Longrightarrow> unmod e' i"
  and bisims_hidden_unmods: "\<lbrakk> bisims Vs es es' xs; hidden Vs i \<rbrakk> \<Longrightarrow> unmods es' i"
by(induct rule: bisim_bisims.inducts)(auto intro: hidden_unmod hidden_unmods dest: hidden_inacc hidden_lengthD)

lemma bisim_fv_unmod: "\<lbrakk> bisim Vs e e' xs; i < length Vs; Vs ! i \<notin> fv e \<rbrakk> \<Longrightarrow> unmod e' i"
  and bisims_fvs_unmods: "\<lbrakk> bisims Vs es es' xs; i < length Vs; Vs ! i \<notin> fvs es \<rbrakk> \<Longrightarrow> unmods es' i"
proof(induct rule: bisim_bisims.inducts)
  case (bisimBlockNone Vs V e e' xs T)
  note len = \<open>i < length Vs\<close>
  have "unmod e' i"
  proof(cases "Vs ! i = V")
    case True
    from len have "hidden (Vs @ [Vs ! i]) i" by(rule hidden_snoc_nth)
    with len True \<open>bisim (Vs @ [V]) e e' xs\<close> show ?thesis by(auto intro: bisim_hidden_unmod)
  next
    case False
    with bisimBlockNone show ?thesis by(auto simp add: nth_append)
  qed
  thus ?case by simp
next
  case (bisimBlockSome Vs V e e' xs v T)
  note len = \<open>i < length Vs\<close>
  show ?case
  proof(cases "Vs ! i = V")
    case True
    from len have "hidden (Vs @ [Vs ! i]) i" by(rule hidden_snoc_nth)
    with len True \<open>bisim (Vs @ [V]) e e' (xs[length Vs := v])\<close>
    show ?thesis by(auto intro: bisim_hidden_unmod)
  next
    case False
    with bisimBlockSome show ?thesis by(auto simp add: nth_append)
  qed
next
  case (bisimBlockSomeNone Vs V e e' xs v T)
  note len = \<open>i < length Vs\<close>
  show ?case
  proof(cases "Vs ! i = V")
    case True
    from len have "hidden (Vs @ [Vs ! i]) i" by(rule hidden_snoc_nth)
    with len True \<open>bisim (Vs @ [V]) e e' xs\<close>
    show ?thesis by(auto intro: bisim_hidden_unmod)
  next
    case False
    with bisimBlockSomeNone show ?thesis by(auto simp add: nth_append)
  qed
qed(fastforce dest: fv_unmod_compE1 fvs_unmods_compEs1 index_le_lengthD simp add: nth_append)+

lemma bisim_extRet2J [intro!]: "bisim Vs e e' xs \<Longrightarrow> bisim Vs (extRet2J e va) (extRet2J1 e' va) xs"
by(cases va) auto

lemma bisims_map_Val_conv2 [simp]: "bisims Vs es (map Val vs) xs = (es = map Val vs)"
apply(induct vs arbitrary: es)
apply(fastforce elim!: bisims_cases)+
done

lemma bisims_map_Val_Throw2: 
  "bisims Vs es' (map Val vs @ Throw a # es) xs \<longleftrightarrow>
   (\<exists>es''. es' = map Val vs @ Throw a # es'' \<and> es = compEs1 Vs es'' \<and> \<not> contains_insyncs es'')"
apply(induct vs arbitrary: es')
 apply(simp)
 apply(fastforce simp add: compEs1_conv_map)
apply(fastforce elim!: bisims_cases)
done

lemma hidden_bisim_unmod: "\<lbrakk> bisim Vs e e' xs; hidden Vs i \<rbrakk> \<Longrightarrow> unmod e' i"
  and hidden_bisims_unmods: "\<lbrakk> bisims Vs es es' xs; hidden Vs i \<rbrakk> \<Longrightarrow> unmods es' i"
apply(induct rule: bisim_bisims.inducts)
apply(auto simp add:hidden_inacc intro: hidden_unmod hidden_unmods)
apply(auto simp add: hidden_def)
done

lemma bisim_list_list_all2_conv:
  "bisim_list es exs' \<longleftrightarrow> list_all2 bisim01 es exs'"
proof
  assume "bisim_list es exs'"
  thus "list_all2 bisim01 es exs'"
    by induct(auto intro!: bisim01.intros)
next
  assume "list_all2 bisim01 es exs'"
  thus "bisim_list es exs'"
    by(induct es arbitrary: exs')(auto intro!: bisim_listCons bisim_listNil elim!: bisim01.cases simp add: list_all2_Cons1)
qed

lemma bisim_list_extTA2J0_extTA2J1:
  assumes wf: "wf_J_prog P"
  and sees: "P \<turnstile> C sees M:[]\<rightarrow>T = \<lfloor>meth\<rfloor> in D"
  shows "bisim_list1 (extNTA2J0 P (C, M, a)) (extNTA2J1 (compP1 P) (C, M, a))"
proof -
  obtain pns body where "meth = (pns, body)" by(cases meth)
  with sees have sees: "P \<turnstile> C sees M:[]\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D" by simp
  moreover let ?xs = "Addr a # replicate (max_vars body) undefined_value"
  let ?e' = "{0:Class D=None; compE1 (this # pns) body}"
  have "bisim_list1 ({this:Class D=\<lfloor>Addr a\<rfloor>; body}, []) ((?e', ?xs), [])"
  proof
    show "bisim_list [] []" ..
    from sees_wf_mdecl[OF wf_prog_wwf_prog[OF wf] sees] have "fv body \<subseteq> set [this]" "pns = []"
      by(auto simp add: wf_mdecl_def)
    thus "fv ({this:Class D=\<lfloor>Addr a\<rfloor>; body}) = {}" by simp
    from sees_wf_mdecl[OF wf sees] obtain T' where "P,[this \<mapsto> Class D] \<turnstile> body :: T'" "this \<notin> set pns"
      and "\<D> body \<lfloor>dom [this \<mapsto> Addr a]\<rfloor>" by(auto simp add: wf_mdecl_def)
    hence "\<not> contains_insync body" by(auto simp add: contains_insync_conv dest: WT_expr_locks)
    with \<open>fv body \<subseteq> set [this]\<close>
    have "bisim ([] @ [this]) body (compE1 (this # pns) body) ?xs"
      unfolding append.simps \<open>pns = []\<close> by(rule compE1_bisim)
    hence "bisim [] {this:Class D=\<lfloor>Addr a\<rfloor>; body} {length ([] :: String.literal list):Class D=None; compE1 (this # pns) body} ?xs"
      by(rule bisimBlockSomeNone)(simp)
    thus "bisim [] ({this:Class D=\<lfloor>Addr a\<rfloor>; body}) ?e' ?xs" by simp
    from \<open>\<D> body \<lfloor>dom [this \<mapsto> Addr a]\<rfloor>\<close> show "\<D> ({this:Class D=\<lfloor>Addr a\<rfloor>; body}) \<lfloor>{}\<rfloor>" by simp
    show "max_vars ?e' \<le> length ?xs" by simp
  qed
  ultimately show ?thesis by(simp)
qed


lemma bisim_max_vars: "bisim Vs e e' xs \<Longrightarrow> max_vars e = max_vars e'"
  and bisims_max_varss: "bisims Vs es es' xs \<Longrightarrow> max_varss es = max_varss es'"
apply(induct rule: bisim_bisims.inducts)
apply(auto simp add: max_vars_compE1 max_varss_compEs1)
done

lemma bisim_call: "bisim Vs e e' xs \<Longrightarrow> call e = call e'"
  and bisims_calls: "bisims Vs es es' xs \<Longrightarrow> calls es = calls es'"
apply(induct rule: bisim_bisims.inducts)
apply(auto simp add: is_vals_conv)
done

lemma bisim_call_None_call1: "\<lbrakk> bisim Vs e e' xs; call e = None \<rbrakk> \<Longrightarrow> call1 e' = None"
  and bisims_calls_None_calls1: "\<lbrakk> bisims Vs es es' xs; calls es = None \<rbrakk> \<Longrightarrow> calls1 es' = None"
by(induct rule: bisim_bisims.inducts)(auto simp add: is_vals_conv split: if_split_asm)

lemma bisim_call1_Some_call:
  "\<lbrakk> bisim Vs e e' xs; call1 e' = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> call e = \<lfloor>aMvs\<rfloor>"

  and bisims_calls1_Some_calls:
  "\<lbrakk> bisims Vs es es' xs; calls1 es' = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> calls es = \<lfloor>aMvs\<rfloor>"
by(induct rule: bisim_bisims.inducts)(auto simp add: is_vals_conv split: if_split_asm)

lemma blocks_bisim: 
  assumes bisim: "bisim (Vs @ pns) e e' xs"
  and length: "length vs = length pns" "length Ts = length pns"
  and xs: "\<forall>i. i < length vs \<longrightarrow> xs ! (i + length Vs) = vs ! i"
  shows "bisim Vs (blocks pns Ts vs e) (blocks1 (length Vs) Ts e') xs"
using bisim length xs
proof(induct pns Ts vs e arbitrary: e' Vs rule: blocks.induct)
  case (1 V Vs T Ts v vs e e' VS)
  note IH = \<open>\<And>e' Vsa. \<lbrakk>bisim (Vsa @ Vs) e e' xs;
                       length vs = length Vs; length Ts = length Vs; \<forall>i<length vs. xs ! (i + length Vsa) = vs ! i\<rbrakk>
           \<Longrightarrow> bisim Vsa (blocks Vs Ts vs e) (blocks1 (length Vsa) Ts e') xs\<close>
  note xs = \<open>\<forall>i<length (v # vs). xs ! (i + length VS) = (v # vs) ! i\<close>
  hence xs': "\<forall>i<length vs. xs ! (i + length (VS @ [V])) = vs ! i" and v: "xs ! length VS = v" by(auto)
  from \<open>bisim (VS @ V # Vs) e e' xs\<close> have "bisim ((VS @ [V]) @ Vs) e e' xs" by simp
  from IH[OF this _ _ xs'] \<open>length (v # vs) = length (V # Vs)\<close> \<open>length (T # Ts) = length (V # Vs)\<close>
  have "bisim (VS @ [V]) (blocks Vs Ts vs e) (blocks1 (length (VS @ [V])) Ts e') xs"
    by auto
  hence "bisim VS ({V:T=\<lfloor>v\<rfloor>; blocks Vs Ts vs e}) {length VS:T=None; blocks1 (length (VS @ [V])) Ts e'} xs"
    using v by(rule bisimBlockSomeNone)
  thus ?case by simp
qed(auto)

lemma fixes e :: "('a,'b,'addr) exp" and es :: "('a,'b,'addr) exp list"
  shows inline_call_max_vars: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> max_vars (inline_call e' e) \<le> max_vars e + max_vars e'"
  and inline_calls_max_varss: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> max_varss (inline_calls e' es) \<le> max_varss es + max_vars e'"
by(induct e and es rule: call.induct calls.induct)(auto)

lemma assumes "final E" "bisim VS E E' xs"
  shows inline_call_compE1: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> inline_call E' (compE1 Vs e) = compE1 Vs (inline_call E e)"
  and inline_calls_compEs1: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> inline_calls E' (compEs1 Vs es) = compEs1 Vs (inline_calls E es)"
proof(induct Vs e and Vs es rule: compE1_compEs1_induct)
  case (Call Vs obj M params)
  note IHobj = \<open>call obj = \<lfloor>aMvs\<rfloor> \<Longrightarrow> inline_call E' (compE1 Vs obj) = compE1 Vs (inline_call E obj)\<close>
  note IHparams = \<open>calls params = \<lfloor>aMvs\<rfloor> \<Longrightarrow> inline_calls E' (compEs1 Vs params) = compEs1 Vs (inline_calls E params)\<close>
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by (cases aMvs, auto)
  with \<open>call (obj\<bullet>M(params)) = \<lfloor>aMvs\<rfloor>\<close> have "call (obj\<bullet>M(params)) = \<lfloor>(a, M', vs)\<rfloor>" by simp
  thus ?case
  proof(induct rule: call_callE)
    case CallObj
    with IHobj have "inline_call E' (compE1 Vs obj) = compE1 Vs (inline_call E obj)" by auto
    with CallObj show ?case by auto
  next
    case (CallParams v)
    with IHparams have "inline_calls E' (compEs1 Vs params) = compEs1 Vs (inline_calls E params)" by auto
    with CallParams show ?case by(auto simp add: is_vals_conv)
  next
    case Call
    with \<open>final E\<close> \<open>bisim VS E E' xs\<close> show ?case by(auto simp add: is_vals_conv)
  qed
qed(auto split: if_split_asm)

lemma assumes bisim: "bisim VS E E' XS"
  and final: "final E"
  shows bisim_inline_call:
  "\<lbrakk> bisim Vs e e' xs; call e = \<lfloor>aMvs\<rfloor>; fv e \<subseteq> set Vs \<rbrakk>
  \<Longrightarrow> bisim Vs (inline_call E e) (inline_call E' e') xs"
  
  and bisims_inline_calls: 
  "\<lbrakk> bisims Vs es es' xs; calls es = \<lfloor>aMvs\<rfloor>; fvs es \<subseteq> set Vs \<rbrakk>
  \<Longrightarrow> bisims Vs (inline_calls E es) (inline_calls E' es') xs"
proof(induct rule: bisim_bisims.inducts)
  case (bisimBinOp1 Vs e e' xs bop e'')
  thus ?case by(cases "is_val (inline_call E e)")(fastforce)+
next
  case (bisimAAcc1 Vs a a' xs i)
  thus ?case by(cases "is_val (inline_call E a)")(fastforce)+
next
  case (bisimAAss1 Vs a a' xs i e)
  thus ?case by(cases "is_val (inline_call E a)", cases "is_val i")(fastforce)+
next
  case (bisimAAss2 Vs i i' xs a e)
  thus ?case by(cases "is_val (inline_call E i)")(fastforce)+
next
  case (bisimFAss1 Vs e e' xs F D e'')
  thus ?case by(cases "is_val (inline_call E e)")(fastforce)+
next
  case (bisimCAS1 Vs e e' xs e2 e3 D F)
  thus ?case 
    apply(cases "is_val (inline_call E e)")
     apply(cases "is_val e2")
      apply(fastforce)
     apply clarsimp
     apply(safe; clarsimp?)
     apply auto
    done
next
  case (bisimCAS2 Vs e e' xs e3 v D F)
  thus ?case by(cases "is_val (inline_call E e)"; safe?; clarsimp; fastforce)
next
  case (bisimCallObj Vs e e' xs es M)
  obtain a M' vs where "aMvs = (a, M', vs)" by(cases aMvs, auto)
  with \<open>call (e\<bullet>M(es)) = \<lfloor>aMvs\<rfloor>\<close> have "call (e\<bullet>M(es)) = \<lfloor>(a, M', vs)\<rfloor>"  by simp
  thus ?case
  proof(induct rule: call_callE)
    case CallObj
    with \<open>fv (e\<bullet>M(es)) \<subseteq> set Vs\<close> \<open>aMvs = (a, M', vs)\<close>
      \<open>\<lbrakk>call e = \<lfloor>aMvs\<rfloor>; fv e \<subseteq> set Vs\<rbrakk> \<Longrightarrow> bisim Vs (inline_call E e) (inline_call E' e') xs\<close>
    have IH': "bisim Vs (inline_call E e) (inline_call E' e') xs" by(auto)
    with \<open>bisim Vs e e' xs\<close> \<open>fv (e\<bullet>M(es)) \<subseteq> set Vs\<close> CallObj \<open>\<not> contains_insyncs es\<close> show ?thesis
      by(cases "is_val (inline_call E e)")(fastforce)+
  next
    case (CallParams v)
    hence "inline_calls E' (compEs1 Vs es) = compEs1 Vs (inline_calls E es)"
      by -(rule inline_calls_compEs1[OF final bisim])
    moreover from \<open>fv (e\<bullet>M(es)) \<subseteq> set Vs\<close> final fvs_inline_calls[of E es]
    have "fvs (inline_calls E es) \<subseteq> set Vs" by(auto elim!: final.cases)
    moreover note CallParams \<open>bisim Vs e e' xs\<close> \<open>fv (e\<bullet>M(es)) \<subseteq> set Vs\<close> \<open>\<not> contains_insyncs es\<close> final
    ultimately show ?case by(auto simp add: is_vals_conv final_iff)
  next
    case Call
    with final bisim \<open>bisim Vs e e' xs\<close> show ?case by(auto simp add: is_vals_conv)
  qed
next
  case (bisimCallParams Vs es es' xs v M)
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by(cases aMvs, auto)
  with \<open>call (Val v\<bullet>M(es)) = \<lfloor>aMvs\<rfloor>\<close> have "call (Val v\<bullet>M(es)) = \<lfloor>(a, M', vs)\<rfloor>"  by simp
  thus ?case
  proof(induct rule: call_callE)
    case CallObj thus ?case by simp
  next
    case (CallParams v')
    with \<open> \<lbrakk>calls es = \<lfloor>aMvs\<rfloor>; fvs es \<subseteq> set Vs\<rbrakk> \<Longrightarrow> bisims Vs (inline_calls E es) (inline_calls E' es') xs\<close> \<open>fv (Val v\<bullet>M(es)) \<subseteq> set Vs\<close>
    have "bisims Vs (inline_calls E es) (inline_calls E' es') xs" by(auto)
    with final bisim \<open>bisims Vs es es' xs\<close> show ?case by(auto simp add: is_vals_conv)
  next
    case Call
    with final bisim \<open>bisims Vs es es' xs\<close> show ?case by(auto)
  qed
next
  case (bisimsCons1 Vs e e' xs es)
  thus ?case by(cases "is_val (inline_call E e)")(fastforce)+
qed(fastforce)+

declare hyperUn_ac [simp del]

lemma sqInt_lem3: "\<lbrakk> A \<sqsubseteq> A'; B \<sqsubseteq> B' \<rbrakk> \<Longrightarrow> A \<sqinter> B \<sqsubseteq> A' \<sqinter> B'"
by(auto simp add: hyperset_defs)

lemma sqUn_lem3: "\<lbrakk> A \<sqsubseteq> A'; B \<sqsubseteq> B' \<rbrakk> \<Longrightarrow> A \<squnion> B \<sqsubseteq> A' \<squnion> B'"
by(auto simp add: hyperset_defs)

lemma A_inline_call: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<A> e \<sqsubseteq> \<A> (inline_call e' e)"
  and As_inline_calls: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow>  \<A>s es \<sqsubseteq> \<A>s (inline_calls e' es)"
proof(induct e and es rule: call.induct calls.induct)
  case (Call obj M params)
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by(cases aMvs, auto)
  with \<open>call (obj\<bullet>M(params)) = \<lfloor>aMvs\<rfloor>\<close> have "call (obj\<bullet>M(params)) = \<lfloor>(a, M', vs)\<rfloor>"  by simp
  thus ?case
  proof(induct rule: call_callE)
    case CallObj
    with \<open>call obj = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<A> obj \<sqsubseteq> \<A> (inline_call e' obj)\<close>
    show ?case by(auto intro: sqUn_lem)
  next
    case CallParams
    with \<open>calls params = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<A>s params \<sqsubseteq> \<A>s (inline_calls e' params)\<close>
    show ?case by(auto intro: sqUn_lem)
  next
    case Call
    thus ?case by(auto simp add: hyperset_defs)
  qed
next
  case Block thus ?case by(fastforce intro: diff_lem)
next
  case throw thus ?case by(simp add: hyperset_defs)
next
  case TryCatch thus ?case by(auto intro: sqInt_lem)
qed(fastforce intro: sqUn_lem sqUn_lem2)+

lemma assumes "final e'"
  shows defass_inline_call: "\<lbrakk> call e = \<lfloor>aMvs\<rfloor>; \<D> e A \<rbrakk> \<Longrightarrow> \<D> (inline_call e' e) A"
  and defasss_inline_calls: "\<lbrakk> calls es = \<lfloor>aMvs\<rfloor>; \<D>s es A \<rbrakk> \<Longrightarrow> \<D>s (inline_calls e' es) A"
proof(induct e and es arbitrary: A and A rule: call.induct calls.induct)
  case (Call obj M params A)
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by(cases aMvs, auto)
  with \<open>call (obj\<bullet>M(params)) = \<lfloor>aMvs\<rfloor>\<close> have "call (obj\<bullet>M(params)) = \<lfloor>(a, M', vs)\<rfloor>"  by simp
  thus ?case
  proof(cases rule: call_callE)
    case CallObj
    with \<open>\<D> (obj\<bullet>M(params)) A\<close> \<open>\<lbrakk>call obj = \<lfloor>aMvs\<rfloor>; \<D> obj A\<rbrakk> \<Longrightarrow> \<D> (inline_call e' obj) A\<close>
    have "\<D> (inline_call e' obj) A" by simp
    moreover from A_inline_call[OF CallObj, of e']
    have "A \<squnion> (\<A> obj) \<sqsubseteq> A \<squnion> (\<A> (inline_call e' obj))" by(rule sqUn_lem2)
    with \<open>\<D> (obj\<bullet>M(params)) A\<close> have "\<D>s params (A \<squnion> \<A> (inline_call e' obj))" by(auto elim: Ds_mono')
    ultimately show ?thesis using CallObj by auto
  next
    case (CallParams v)
    with \<open>\<D> (obj\<bullet>M(params)) A\<close> \<open>\<lbrakk>calls params = \<lfloor>aMvs\<rfloor>; \<D>s params A\<rbrakk> \<Longrightarrow> \<D>s (inline_calls e' params) A\<close>
    have "\<D>s (inline_calls e' params) A" by(simp)
    with CallParams show ?thesis by(auto)
  next
    case Call
    with \<open>final e'\<close> show ?thesis by(auto elim!: D_mono' simp add: hyperset_defs)
  qed
next
  case (Cons_exp exp exps A)
  show ?case
  proof(cases "is_val exp")
    case True
    with \<open>\<D>s (exp # exps) A\<close> \<open>\<lbrakk>calls exps = \<lfloor>aMvs\<rfloor>; \<D>s exps A\<rbrakk> \<Longrightarrow> \<D>s (inline_calls e' exps) A\<close> 
      \<open>calls (exp # exps) = \<lfloor>aMvs\<rfloor>\<close>
    have "\<D>s (inline_calls e' exps) A" by(auto)
    with True show ?thesis by(auto)
  next
    case False
    with \<open>\<lbrakk>call exp = \<lfloor>aMvs\<rfloor>; \<D> exp A\<rbrakk> \<Longrightarrow> \<D> (inline_call e' exp) A\<close> \<open>calls (exp # exps) = \<lfloor>aMvs\<rfloor>\<close> \<open>\<D>s (exp # exps) A\<close>
    have "\<D> (inline_call e' exp) A" by auto
    moreover from False \<open>calls (exp # exps) = \<lfloor>aMvs\<rfloor>\<close> have "\<A> exp \<sqsubseteq> \<A> (inline_call e' exp)"
      by(auto intro: A_inline_call)
    hence "A \<squnion> \<A> exp \<sqsubseteq> A \<squnion> \<A> (inline_call e' exp)" by(rule sqUn_lem2)
    with \<open>\<D>s (exp # exps) A\<close> have "\<D>s exps (A \<squnion> \<A> (inline_call e' exp))"
      by(auto intro: Ds_mono')
    ultimately show ?thesis using False by(auto)
  qed
qed(fastforce split: if_split_asm elim: D_mono' intro: sqUn_lem2 sqUn_lem A_inline_call)+

lemma bisim_B: "bisim Vs e E xs \<Longrightarrow> \<B> E (length Vs)"
  and bisims_Bs: "bisims Vs es Es xs \<Longrightarrow> \<B>s Es (length Vs)"
apply(induct rule: bisim_bisims.inducts)
apply(auto intro: \<B> \<B>s)
done

lemma bisim_expr_locks_eq: "bisim Vs e e' xs \<Longrightarrow> expr_locks e = expr_locks e'"
  and bisims_expr_lockss_eq: "bisims Vs es es' xs \<Longrightarrow> expr_lockss es = expr_lockss es'"
by(induct rule: bisim_bisims.inducts)(auto intro!: ext)

lemma bisim_list_expr_lockss_eq: "bisim_list es exs' \<Longrightarrow> expr_lockss es = expr_lockss (map fst exs')"
apply(induct rule: bisim_list.induct)
apply(auto dest: bisim_expr_locks_eq)
done

context J1_heap_base begin

lemma [simp]:
  fixes e :: "('a, 'b, 'addr) exp" and es :: "('a, 'b, 'addr) exp list"
  shows \<tau>move1_compP: "\<tau>move1 (compP f P) h e = \<tau>move1 P h e"
  and \<tau>moves1_compP: "\<tau>moves1 (compP f P) h es = \<tau>moves1 P h es"
by(induct e and es rule: \<tau>move1.induct \<tau>moves1.induct) auto

lemma \<tau>Move1_compP [simp]: "\<tau>Move1 (compP f P) = \<tau>Move1 P"
by(intro ext) auto

lemma red1_preserves_unmod:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; unmod e i \<rbrakk> \<Longrightarrow> (lcl s') ! i = (lcl s) ! i"
  
  and reds1_preserves_unmod:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; unmods es i \<rbrakk> \<Longrightarrow> (lcl s') ! i = (lcl s) ! i"
apply(induct rule: red1_reds1.inducts)
apply(auto split: if_split_asm)
done

lemma red1_unmod_preserved:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; unmod e i \<rbrakk> \<Longrightarrow> unmod e' i"
  and reds1_unmods_preserved:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; unmods es i \<rbrakk> \<Longrightarrow> unmods es' i"
by(induct rule: red1_reds1.inducts)(auto split: if_split_asm)

lemma \<tau>red1t_unmod_preserved:
  "\<lbrakk> \<tau>red1gt uf P t h (e, xs) (e', xs'); unmod e i \<rbrakk> \<Longrightarrow> unmod e' i"
by(induct rule: tranclp_induct2)(auto intro: red1_unmod_preserved)

lemma \<tau>red1r_unmod_preserved:
  "\<lbrakk> \<tau>red1gr uf P t h (e, xs) (e', xs'); unmod e i \<rbrakk> \<Longrightarrow> unmod e' i"
by(induct rule: rtranclp_induct2)(auto intro: red1_unmod_preserved)

lemma \<tau>red1t_preserves_unmod: 
  "\<lbrakk>\<tau>red1gt uf P t h (e, xs) (e', xs'); unmod e i; i < length xs \<rbrakk>
  \<Longrightarrow> xs' ! i = xs ! i"
apply(induct rule: tranclp_induct2)
 apply(auto dest: red1_preserves_unmod)
apply(drule red1_preserves_unmod)
apply(erule (1) \<tau>red1t_unmod_preserved)
apply(drule \<tau>red1t_preserves_len)
apply auto
done

lemma \<tau>red1'r_preserves_unmod: 
  "\<lbrakk>\<tau>red1gr uf P t h (e, xs) (e', xs'); unmod e i; i < length xs \<rbrakk>
  \<Longrightarrow> xs' ! i = xs ! i"
apply(induct rule: converse_rtranclp_induct2)
 apply(auto dest: red1_preserves_unmod red1_unmod_preserved red1_preserves_len)
apply(frule (1) red1_unmod_preserved)
apply(frule red1_preserves_len)
apply(frule (1) red1_preserves_unmod)
apply auto
done

end

context J_heap_base begin

lemma [simp]:
  fixes e :: "('a, 'b, 'addr) exp" and es :: "('a, 'b, 'addr) exp list"
  shows \<tau>move0_compP: "\<tau>move0 (compP f P) h e = \<tau>move0 P h e"
  and \<tau>moves0_compP: "\<tau>moves0 (compP f P) h es = \<tau>moves0 P h es"
by(induct e and es rule: \<tau>move0.induct \<tau>moves0.induct) auto

lemma \<tau>Move0_compP [simp]: "\<tau>Move0 (compP f P) = \<tau>Move0 P"
by(intro ext) auto

end

end
