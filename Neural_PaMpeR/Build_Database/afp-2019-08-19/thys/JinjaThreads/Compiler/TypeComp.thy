(*  Title:      JinjaThreads/Compiler/TypeComp.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

section \<open>Preservation of Well-Typedness in Stage 2\<close>

theory TypeComp
imports 
  Exception_Tables
  J1WellForm
  "../BV/BVSpec"
  "HOL-Library.Prefix_Order"
  "HOL-Library.Sublist"
begin

(*<*)
declare nth_append[simp]
(*>*)

locale TC0 =
  fixes P :: "'addr J1_prog" and mxl :: nat
begin

definition ty :: "ty list \<Rightarrow> 'addr expr1 \<Rightarrow> ty"
where "ty E e \<equiv> THE T. P,E \<turnstile>1 e :: T"

definition ty\<^sub>l :: "ty list \<Rightarrow> nat set \<Rightarrow> ty\<^sub>l"
where "ty\<^sub>l E A' \<equiv> map (\<lambda>i. if i \<in> A' \<and> i < size E then OK(E!i) else Err) [0..<mxl]"

definition ty\<^sub>i' :: "ty list \<Rightarrow> ty list \<Rightarrow> nat set option \<Rightarrow> ty\<^sub>i'"
where "ty\<^sub>i' ST E A \<equiv> case A of None \<Rightarrow> None | \<lfloor>A'\<rfloor> \<Rightarrow> Some(ST, ty\<^sub>l E A')"

definition after :: "ty list \<Rightarrow> nat set option \<Rightarrow> ty list \<Rightarrow> 'addr expr1 \<Rightarrow> ty\<^sub>i'"
  where "after E A ST e \<equiv> ty\<^sub>i' (ty E e # ST) E (A \<squnion> \<A> e)"

end

locale TC1 = TC0 +
  fixes wfmd
  assumes wf_prog: "wf_prog wfmd P"
begin

lemma ty_def2 [simp]: "P,E \<turnstile>1 e :: T \<Longrightarrow> ty E e = T"
apply(unfold ty_def ty_def)
apply(blast intro: the_equality WT1_unique[OF wf_prog])
done

end

context TC0 begin

lemma ty\<^sub>i'_None [simp]: "ty\<^sub>i' ST E None = None"
by(simp add:ty\<^sub>i'_def)

lemma ty\<^sub>l_app_diff[simp]:
 "ty\<^sub>l (E@[T]) (A - {size E}) = ty\<^sub>l E A"
by(auto simp add:ty\<^sub>l_def hyperset_defs)

lemma ty\<^sub>i'_app_diff[simp]:
 "ty\<^sub>i' ST (E @ [T]) (A \<ominus> size E) = ty\<^sub>i' ST E A"
by(auto simp add:ty\<^sub>i'_def hyperset_defs)

lemma ty\<^sub>l_antimono:
 "A \<subseteq> A' \<Longrightarrow> P \<turnstile> ty\<^sub>l E A' [\<le>\<^sub>\<top>] ty\<^sub>l E A"
by(auto simp:ty\<^sub>l_def list_all2_conv_all_nth)


lemma ty\<^sub>i'_antimono:
 "A \<subseteq> A' \<Longrightarrow> P \<turnstile> ty\<^sub>i' ST E \<lfloor>A'\<rfloor> \<le>' ty\<^sub>i' ST E \<lfloor>A\<rfloor>"
by(auto simp:ty\<^sub>i'_def ty\<^sub>l_def list_all2_conv_all_nth)

lemma ty\<^sub>l_env_antimono:
 "P \<turnstile> ty\<^sub>l (E@[T]) A [\<le>\<^sub>\<top>] ty\<^sub>l E A" 
by(auto simp:ty\<^sub>l_def list_all2_conv_all_nth)


lemma ty\<^sub>i'_env_antimono:
 "P \<turnstile> ty\<^sub>i' ST (E@[T]) A \<le>' ty\<^sub>i' ST E A" 
by(auto simp:ty\<^sub>i'_def ty\<^sub>l_def list_all2_conv_all_nth)


lemma ty\<^sub>i'_incr:
 "P \<turnstile> ty\<^sub>i' ST (E @ [T]) \<lfloor>insert (size E) A\<rfloor> \<le>' ty\<^sub>i' ST E \<lfloor>A\<rfloor>"
by(auto simp:ty\<^sub>i'_def ty\<^sub>l_def list_all2_conv_all_nth)


lemma ty\<^sub>l_incr:
 "P \<turnstile> ty\<^sub>l (E @ [T]) (insert (size E) A) [\<le>\<^sub>\<top>] ty\<^sub>l E A"
by(auto simp: hyperset_defs ty\<^sub>l_def list_all2_conv_all_nth)


lemma ty\<^sub>l_in_types:
 "set E \<subseteq> types P \<Longrightarrow> ty\<^sub>l E A \<in> list mxl (err (types P))"
by(auto simp add:ty\<^sub>l_def intro!:listI dest!: nth_mem)


function compT :: "ty list \<Rightarrow> nat hyperset \<Rightarrow> ty list \<Rightarrow> 'addr expr1 \<Rightarrow> ty\<^sub>i' list"
  and compTs :: "ty list \<Rightarrow> nat hyperset \<Rightarrow> ty list \<Rightarrow> 'addr expr1 list \<Rightarrow> ty\<^sub>i' list"
where
  "compT E A ST (new C) = []"
| "compT E A ST (newA T\<lfloor>e\<rceil>) = compT E A ST e @ [after E A ST e]"
| "compT E A ST (Cast C e) = compT E A ST e @ [after E A ST e]"
| "compT E A ST (e instanceof T) = compT E A ST e @ [after E A ST e]"
| "compT E A ST (Val v) = []"
| "compT E A ST (e1 \<guillemotleft>bop\<guillemotright> e2) =
  (let ST1 = ty E e1#ST; A1 = A \<squnion> \<A> e1 in
   compT E A ST e1 @ [after E A ST e1] @
   compT E A1 ST1 e2 @ [after E A1 ST1 e2])"
| "compT E A ST (Var i) = []"
| "compT E A ST (i := e) = compT E A ST e @ [after E A ST e, ty\<^sub>i' ST E (A \<squnion> \<A> e \<squnion> \<lfloor>{i}\<rfloor>)]"
| "compT E A ST (a\<lfloor>i\<rceil>) =
  (let ST1 = ty E a # ST; A1 = A \<squnion> \<A> a
   in  compT E A ST a @ [after E A ST a] @ compT E A1 ST1 i @ [after E A1 ST1 i])"
| "compT E A ST (a\<lfloor>i\<rceil> := e) =
  (let ST1 = ty E a # ST; A1 = A \<squnion> \<A> a;
       ST2 = ty E i # ST1; A2 = A1 \<squnion> \<A> i; A3 = A2 \<squnion> \<A> e
   in compT E A ST a @ [after E A ST a] @ compT E A1 ST1 i @ [after E A1 ST1 i] @ compT E A2 ST2 e @ [after E A2 ST2 e, ty\<^sub>i' ST E A3])"
| "compT E A ST (a\<bullet>length) = compT E A ST a @ [after E A ST a]"
| "compT E A ST (e\<bullet>F{D}) = compT E A ST e @ [after E A ST e]"
| "compT E A ST (e1\<bullet>F{D} := e2) =
  (let ST1 = ty E e1#ST; A1 = A \<squnion> \<A> e1; A2 = A1 \<squnion> \<A> e2
   in  compT E A ST e1 @ [after E A ST e1] @ compT E A1 ST1 e2 @ [after E A1 ST1 e2] @ [ty\<^sub>i' ST E A2])"
| "compT E A ST (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) =
  (let ST1 = ty E e1 # ST; A1 = A \<squnion> \<A> e1; ST2 = ty E e2 # ST1; A2 = A1 \<squnion> \<A> e2; A3 = A2 \<squnion> \<A> e3
   in  compT E A ST e1 @ [after E A ST e1] @ compT E A1 ST1 e2 @ [after E A1 ST1 e2] @ compT E A2 ST2 e3 @ [after E A2 ST2 e3])"
| "compT E A ST (e\<bullet>M(es)) =
   compT E A ST e @ [after E A ST e] @
   compTs E (A \<squnion> \<A> e) (ty E e # ST) es"
| "compT E A ST {i:T=None; e} = compT (E@[T]) (A\<ominus>i) ST e"
| "compT E A ST {i:T=\<lfloor>v\<rfloor>; e} = 
   [after E A ST (Val v), ty\<^sub>i' ST (E@[T]) (A \<squnion> \<lfloor>{i}\<rfloor>)] @ compT (E@[T]) (A \<squnion> \<lfloor>{i}\<rfloor>) ST e"

| "compT E A ST (sync\<^bsub>i\<^esub> (e1) e2) =
  (let A1 = A \<squnion> \<A> e1 \<squnion> \<lfloor>{i}\<rfloor>; E1 = E @ [Class Object]; ST2 = ty E1 e2 # ST; A2 = A1 \<squnion> \<A> e2
   in  compT E A ST e1 @
       [after E A ST e1,
        ty\<^sub>i' (Class Object # Class Object # ST) E (A \<squnion> \<A> e1),
        ty\<^sub>i' (Class Object # ST) E1 A1,
        ty\<^sub>i' ST E1 A1] @
       compT E1 A1 ST e2 @ 
       [ty\<^sub>i' ST2 E1 A2, ty\<^sub>i' (Class Object # ST2) E1 A2, ty\<^sub>i' ST2 E1 A2, 
        ty\<^sub>i' (Class Throwable # ST) E1 A1,
        ty\<^sub>i' (Class Object # Class Throwable # ST) E1 A1,
        ty\<^sub>i' (Class Throwable # ST) E1 A1])"
| "compT E A ST (insync\<^bsub>i\<^esub> (a) e) = []"

| "compT E A ST (e1;;e2) =
  (let A1 = A \<squnion> \<A> e1 in
   compT E A ST e1 @ [after E A ST e1, ty\<^sub>i' ST E A1] @
   compT E A1 ST e2)"
| "compT E A ST (if (e) e1 else e2) =
   (let A0 = A \<squnion> \<A> e; \<tau> = ty\<^sub>i' ST E A0 in
    compT E A ST e @ [after E A ST e, \<tau>] @
    compT E A0 ST e1 @ [after E A0 ST e1, \<tau>] @
    compT E A0 ST e2)"
| "compT E A ST (while (e) c) =
   (let A0 = A \<squnion> \<A> e;  A1 = A0 \<squnion> \<A> c; \<tau> = ty\<^sub>i' ST E A0 in
    compT E A ST e @ [after E A ST e, \<tau>] @
    compT E A0 ST c @ [after E A0 ST c, ty\<^sub>i' ST E A1, ty\<^sub>i' ST E A0])"
| "compT E A ST (throw e) = compT E A ST e @ [after E A ST e]"
| "compT E A ST (try e1 catch(C i) e2) =
   compT E A ST e1 @ [after E A ST e1] @
   [ty\<^sub>i' (Class C#ST) E A, ty\<^sub>i' ST (E@[Class C]) (A \<squnion> \<lfloor>{i}\<rfloor>)] @
   compT (E@[Class C]) (A \<squnion> \<lfloor>{i}\<rfloor>) ST e2"

| "compTs E A ST [] = []"
| "compTs E A ST (e#es) = compT E A ST e @ [after E A ST e] @
                            compTs E (A \<squnion> (\<A> e)) (ty E e # ST) es"
by pat_completeness simp_all
termination
apply(relation "case_sum (\<lambda>p. size (snd (snd (snd p)))) (\<lambda>p. size_list size (snd (snd (snd p)))) <*mlex*> {}")
apply(rule wf_mlex[OF wf_empty])
apply(rule mlex_less, simp)+
done

lemmas compT_compTs_induct =
  compT_compTs.induct[
    unfolded meta_all5_eq_conv meta_all4_eq_conv meta_all3_eq_conv meta_all2_eq_conv meta_all_eq_conv,
    case_names
      new NewArray Cast InstanceOf Val BinOp Var LAss AAcc AAss ALen FAcc FAss CompareAndSwap Call BlockNone BlockSome
      Synchronized InSynchronized Seq Cond While throw TryCatch
      Nil Cons]

definition compTa :: "ty list \<Rightarrow> nat hyperset \<Rightarrow> ty list \<Rightarrow> 'addr expr1 \<Rightarrow> ty\<^sub>i' list"
where "compTa E A ST e \<equiv> compT E A ST e @ [after E A ST e]"

lemmas compE2_not_Nil = compE2_neq_Nil
declare compE2_not_Nil[simp]

lemma compT_sizes[simp]:
  shows "size(compT E A ST e) = size(compE2 e) - 1"
  and "size(compTs E A ST es) = size(compEs2 es)"
apply(induct E A ST e and E A ST es rule: compT_compTs_induct)
apply(auto split:nat_diff_split)
done

lemma compT_None_not_Some [simp]: "\<lfloor>\<tau>\<rfloor> \<notin> set (compT E None ST e)"
  and compTs_None_not_Some [simp]: "\<lfloor>\<tau>\<rfloor> \<notin> set (compTs E None ST es)"
by(induct E A\<equiv>"None :: nat hyperset" ST e and E A\<equiv>"None :: nat hyperset" ST es rule: compT_compTs_induct) (simp_all add:after_def)

lemma pair_eq_ty\<^sub>i'_conv:
  "(\<lfloor>(ST, LT)\<rfloor> = ty\<^sub>i' ST\<^sub>0 E A) = (case A of None \<Rightarrow> False | Some A \<Rightarrow> (ST = ST\<^sub>0 \<and> LT = ty\<^sub>l E A))"
by(simp add:ty\<^sub>i'_def)

lemma pair_conv_ty\<^sub>i': "\<lfloor>(ST, ty\<^sub>l E A)\<rfloor> = ty\<^sub>i' ST E \<lfloor>A\<rfloor>"
by(simp add:ty\<^sub>i'_def)

lemma ty\<^sub>i'_antimono2:
 "\<lbrakk> E \<le> E'; A \<subseteq> A' \<rbrakk> \<Longrightarrow> P \<turnstile> ty\<^sub>i' ST E' \<lfloor>A'\<rfloor> \<le>' ty\<^sub>i' ST E \<lfloor>A\<rfloor>"
by(auto simp:ty\<^sub>i'_def ty\<^sub>l_def list_all2_conv_all_nth less_eq_list_def prefix_def)

declare ty\<^sub>i'_antimono [intro!] after_def[simp] pair_conv_ty\<^sub>i'[simp] pair_eq_ty\<^sub>i'_conv[simp]

lemma compT_LT_prefix:
  "\<lbrakk> \<lfloor>(ST,LT)\<rfloor> \<in> set(compT E A ST0 e); \<B> e (size E) \<rbrakk> \<Longrightarrow> P \<turnstile> \<lfloor>(ST,LT)\<rfloor> \<le>' ty\<^sub>i' ST E A"
  and compTs_LT_prefix:
  "\<lbrakk> \<lfloor>(ST,LT)\<rfloor> \<in> set(compTs E A ST0 es); \<B>s es (size E) \<rbrakk> \<Longrightarrow> P \<turnstile> \<lfloor>(ST,LT)\<rfloor> \<le>' ty\<^sub>i' ST E A"
proof(induct E A ST0 e and E A ST0 es rule: compT_compTs_induct)
  case FAss thus ?case by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case BinOp thus ?case
    by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans split:bop.splits)
next
  case Seq thus ?case by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case While thus ?case by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case Cond thus ?case by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case BlockNone thus ?case by(auto)
next
  case BlockSome thus ?case
    by(clarsimp simp only: ty\<^sub>i'_def)(fastforce intro: ty\<^sub>i'_incr simp add: hyperset_defs elim: sup_state_opt_trans)
next
  case Call thus ?case by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case Cons thus ?case
    by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case TryCatch thus ?case
    by(fastforce simp:hyperset_defs intro!: ty\<^sub>i'_incr elim!:sup_state_opt_trans)
next
  case NewArray thus ?case by(auto simp add: hyperset_defs)
next
  case AAcc thus ?case by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case AAss thus ?case by(auto simp:hyperset_defs Un_ac elim!:sup_state_opt_trans)
next
  case ALen thus ?case by(auto simp add: hyperset_defs)
next
  case CompareAndSwap thus ?case by(auto simp: hyperset_defs Un_ac elim!:sup_state_opt_trans)
next
  case Synchronized thus ?case
    by(fastforce simp add: hyperset_defs elim: sup_state_opt_trans intro: sup_state_opt_trans[OF ty\<^sub>i'_incr] ty\<^sub>i'_antimono2)
qed (auto simp:hyperset_defs)

declare ty\<^sub>i'_antimono [rule del] after_def[simp del] pair_conv_ty\<^sub>i'[simp del] pair_eq_ty\<^sub>i'_conv[simp del]

lemma OK_None_states [iff]: "OK None \<in> states P mxs mxl"
by(simp add: JVM_states_unfold)

end

context TC1 begin

lemma after_in_states:
 "\<lbrakk> P,E \<turnstile>1 e :: T; set E \<subseteq> types P; set ST \<subseteq> types P; size ST + max_stack e \<le> mxs \<rbrakk>
 \<Longrightarrow> OK (after E A ST e) \<in> states P mxs mxl"
apply(subgoal_tac "size ST + 1 \<le> mxs")
 apply(simp add:after_def ty\<^sub>i'_def JVM_states_unfold ty\<^sub>l_in_types)
 apply(clarify intro!: exI)
 apply(rule conjI)
  apply(rule exI[where x="length ST + 1"], fastforce)
 apply(clarsimp)
 apply(rule conjI[OF WT1_is_type[OF wf_prog]], auto intro: listI)
using max_stack1[of e] by simp

end

context TC0 begin

lemma OK_ty\<^sub>i'_in_statesI [simp]:
  "\<lbrakk> set E \<subseteq> types P; set ST \<subseteq> types P; size ST \<le> mxs \<rbrakk>
  \<Longrightarrow> OK (ty\<^sub>i' ST E A) \<in> states P mxs mxl"
apply(simp add:ty\<^sub>i'_def JVM_states_unfold ty\<^sub>l_in_types)
apply(blast intro!:listI)
done

end

lemma is_class_type_aux: "is_class P C \<Longrightarrow> is_type P (Class C)"
by(simp)

context TC1 begin

declare is_type.simps[simp del] subsetI[rule del]

theorem
  shows compT_states:
  "\<lbrakk> P,E \<turnstile>1 e :: T; set E \<subseteq> types P; set ST \<subseteq> types P;
     size ST + max_stack e \<le> mxs; size E + max_vars e \<le> mxl \<rbrakk>
  \<Longrightarrow> OK ` set(compT E A ST e) \<subseteq> states P mxs mxl"
  (is "PROP ?P e E T A ST")

  and compTs_states: 
  "\<lbrakk> P,E \<turnstile>1 es[::]Ts;  set E \<subseteq> types P; set ST \<subseteq> types P;
    size ST + max_stacks es \<le> mxs; size E + max_varss es \<le> mxl \<rbrakk>
  \<Longrightarrow> OK ` set(compTs E A ST es) \<subseteq> states P mxs mxl"
    (is "PROP ?Ps es E Ts A ST")
proof(induct E A ST e and E A ST es arbitrary: T and Ts rule: compT_compTs_induct)
  case new thus ?case by(simp)
next
  case (Cast C e) thus ?case by (auto simp:after_in_states)
next
  case InstanceOf thus ?case by (auto simp:after_in_states)
next
  case Val thus  ?case by(simp)
next
  case Var thus ?case by(simp)
next
  case LAss thus ?case  by(auto simp:after_in_states)
next
  case FAcc thus ?case by(auto simp:after_in_states)
next
  case FAss thus ?case
    by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case CompareAndSwap thus ?case  by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case Seq thus ?case
    by(auto simp:image_Un after_in_states)
next
  case BinOp thus ?case
    by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case Cond thus ?case
    by(force simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case While thus ?case
    by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case BlockNone thus ?case by auto
next
  case (BlockSome E A ST i ty v exp)
  with max_stack1[of exp] show ?case by(auto intro: after_in_states)
next
  case (TryCatch E A ST e\<^sub>1 C i e\<^sub>2)
  moreover have "size ST + 1 \<le> mxs" using TryCatch.prems max_stack1[of e\<^sub>1] by auto
  ultimately show ?case  
    by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states
                  is_class_type_aux)
next
  case Nil thus ?case by simp
next
  case Cons thus ?case
    by(auto simp:image_Un  WT1_is_type[OF wf_prog] after_in_states)
next
  case throw thus ?case
    by(auto simp: WT1_is_type[OF wf_prog] after_in_states)
next
  case Call thus ?case
    by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case NewArray thus ?case
    by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case AAcc thus ?case by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case AAss thus ?case by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case ALen thus ?case by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case InSynchronized thus ?case by auto
next
  case (Synchronized E A ST i exp1 exp2)
  from \<open>P,E \<turnstile>1 sync\<^bsub>i\<^esub> (exp1) exp2 :: T\<close> obtain T1
    where wt1: "P,E \<turnstile>1 exp1 :: T1" and T1: "is_refT T1" "T1 \<noteq> NT"
    and wt2: "P,E@[Class Object] \<turnstile>1 exp2 :: T" by auto
  moreover note E = \<open>set E \<subseteq> types P\<close> with wf_prog
  have E': "set (E@[Class Object]) \<subseteq> types P" by(auto simp add: is_type.simps)
  moreover from wf_prog wt2 E' have T: "is_type P T" by(rule WT1_is_type)
  note ST = \<open>set ST \<subseteq> types P\<close> with wf_prog
  have ST': "set (Class Object # ST) \<subseteq> types P" by(auto simp add: is_type.simps)
  moreover from wf_prog have throwable: "is_type P (Class Throwable)"
    unfolding is_type.simps by(rule is_class_Throwable)
  ultimately show ?case using Synchronized max_stack1[of exp2] T
    by(auto simp add: image_Un after_in_states)
qed

declare is_type.simps[simp] subsetI[intro!]

end


locale TC2 = TC0 +
  fixes T\<^sub>r :: ty and mxs :: pc
begin
  
definition
  wt_instrs :: "'addr instr list \<Rightarrow> ex_table \<Rightarrow> ty\<^sub>i' list \<Rightarrow> bool" ("(\<turnstile> _, _ /[::]/ _)" [0,0,51] 50)
where
  "\<turnstile> is,xt [::] \<tau>s \<equiv> size is < size \<tau>s \<and> pcs xt \<subseteq> {0..<size is} \<and> (\<forall>pc< size is. P,T\<^sub>r,mxs,size \<tau>s,xt \<turnstile> is!pc,pc :: \<tau>s)"

lemmas wt_defs = wt_instrs_def wt_instr_def app_def eff_def norm_eff_def

lemma wt_instrs_Nil [simp]: "\<tau>s \<noteq> [] \<Longrightarrow> \<turnstile> [],[] [::] \<tau>s"
by(simp add:wt_defs)

end

locale TC3 = TC1 + TC2

lemma eff_None [simp]: "eff i P pc et None = []"
by (simp add: Effect.eff_def)

declare split_comp_eq[simp del]

lemma wt_instr_appR:
 "\<lbrakk> P,T,m,mpc,xt \<turnstile> is!pc,pc :: \<tau>s;
    pc < size is; size is < size \<tau>s; mpc \<le> size \<tau>s; mpc \<le> mpc' \<rbrakk>
  \<Longrightarrow> P,T,m,mpc',xt \<turnstile> is!pc,pc :: \<tau>s@\<tau>s'"
by (fastforce simp:wt_instr_def app_def)


lemma relevant_entries_shift [simp]:
  "relevant_entries P i (pc+n) (shift n xt) = shift n (relevant_entries P i pc xt)"
  apply (induct xt)
  apply (unfold relevant_entries_def shift_def) 
   apply simp
  apply (auto simp add: is_relevant_entry_def)
  done



lemma xcpt_eff_shift [simp]:
  "xcpt_eff i P (pc+n) \<tau> (shift n xt) =
   map (\<lambda>(pc,\<tau>). (pc + n, \<tau>)) (xcpt_eff i P pc \<tau> xt)"
apply(simp add: xcpt_eff_def)
apply(cases \<tau>)
apply(auto simp add: shift_def)
done


lemma  eff_shift [simp]:
  "app\<^sub>i (i, P, pc, m, T, \<tau>) \<Longrightarrow>
   eff i P (pc+n) (shift n xt) (Some \<tau>) =
   map (\<lambda>(pc,\<tau>). (pc+n,\<tau>)) (eff i P pc xt (Some \<tau>))"
apply(simp add:eff_def norm_eff_def)
apply(cases "i",auto)
done


lemma xcpt_app_shift [simp]:
  "xcpt_app i P (pc+n) m (shift n xt) \<tau> = xcpt_app i P pc m xt \<tau>"
by (simp add: xcpt_app_def) (auto simp add: shift_def)


lemma wt_instr_appL:
  "\<lbrakk> P,T,m,mpc,xt \<turnstile> i,pc :: \<tau>s; pc < size \<tau>s; mpc \<le> size \<tau>s \<rbrakk>
  \<Longrightarrow> P,T,m,mpc + size \<tau>s',shift (size \<tau>s') xt \<turnstile> i,pc+size \<tau>s' :: \<tau>s'@\<tau>s"
apply(clarsimp simp add: wt_instr_def app_def)
apply(auto)
apply(cases "i", auto)
done


lemma wt_instr_Cons:
  "\<lbrakk> P,T,m,mpc - 1,[] \<turnstile> i,pc - 1 :: \<tau>s;
     0 < pc; 0 < mpc; pc < size \<tau>s + 1; mpc \<le> size \<tau>s + 1 \<rbrakk>
  \<Longrightarrow> P,T,m,mpc,[] \<turnstile> i,pc :: \<tau>#\<tau>s"
apply(drule wt_instr_appL[where \<tau>s' = "[\<tau>]"])
apply arith
apply arith
apply (simp split:nat_diff_split_asm)
done


lemma wt_instr_append:
  "\<lbrakk> P,T,m,mpc - size \<tau>s',[] \<turnstile> i,pc - size \<tau>s' :: \<tau>s;
     size \<tau>s' \<le> pc; size \<tau>s' \<le> mpc; pc < size \<tau>s + size \<tau>s'; mpc \<le> size \<tau>s + size \<tau>s' \<rbrakk>
  \<Longrightarrow> P,T,m,mpc,[] \<turnstile> i,pc :: \<tau>s'@\<tau>s"
apply(drule wt_instr_appL[where \<tau>s' = \<tau>s'])
apply arith
apply arith
apply (simp split:nat_diff_split_asm)
done


lemma xcpt_app_pcs:
  "pc \<notin> pcs xt \<Longrightarrow> xcpt_app i P pc mxs xt \<tau>"
by (auto simp add: xcpt_app_def relevant_entries_def is_relevant_entry_def pcs_def)


lemma xcpt_eff_pcs:
  "pc \<notin> pcs xt \<Longrightarrow> xcpt_eff i P pc \<tau> xt = []"
by (cases \<tau>)
   (auto simp add: is_relevant_entry_def xcpt_eff_def relevant_entries_def pcs_def
           intro!: filter_False)


lemma pcs_shift:
  "pc < n \<Longrightarrow> pc \<notin> pcs (shift n xt)" 
by (auto simp add: shift_def pcs_def)

lemma xcpt_eff_shift_pc_ge_n: assumes "x \<in> set (xcpt_eff i P pc \<tau> (shift n xt))"
  shows "n \<le> pc"
proof -
  { assume "pc < n"
    hence "pc \<notin> pcs (shift n xt)" by(rule pcs_shift)
    with assms have False
      by(auto simp add: pcs_def xcpt_eff_def is_relevant_entry_def relevant_entries_def split_beta cong: filter_cong) }
  thus ?thesis by(cases "n \<le> pc")(auto)
qed

lemma wt_instr_appRx:
  "\<lbrakk> P,T,m,mpc,xt \<turnstile> is!pc,pc :: \<tau>s; pc < size is; size is < size \<tau>s; mpc \<le> size \<tau>s \<rbrakk>
  \<Longrightarrow> P,T,m,mpc,xt @ shift (size is) xt' \<turnstile> is!pc,pc :: \<tau>s"
apply(clarsimp simp:wt_instr_def eff_def app_def)
apply(fastforce dest: xcpt_eff_shift_pc_ge_n intro!: xcpt_app_pcs[OF pcs_shift])
done

lemma wt_instr_appLx: 
  "\<lbrakk> P,T,m,mpc,xt \<turnstile> i,pc :: \<tau>s; pc \<notin> pcs xt' \<rbrakk>
  \<Longrightarrow> P,T,m,mpc,xt'@xt \<turnstile> i,pc :: \<tau>s"
by (auto simp:wt_instr_def app_def eff_def xcpt_app_pcs xcpt_eff_pcs)


context TC2 begin

lemma wt_instrs_extR:
  "\<turnstile> is,xt [::] \<tau>s \<Longrightarrow> \<turnstile> is,xt [::] \<tau>s @ \<tau>s'"
by(auto simp add:wt_instrs_def wt_instr_appR)


lemma wt_instrs_ext:
  "\<lbrakk> \<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2; \<turnstile> is\<^sub>2,xt\<^sub>2 [::] \<tau>s\<^sub>2; size \<tau>s\<^sub>1 = size is\<^sub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^sub>1@is\<^sub>2, xt\<^sub>1 @ shift (size is\<^sub>1) xt\<^sub>2 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2"
apply(clarsimp simp:wt_instrs_def)
apply(rule conjI, fastforce)
apply(rule conjI, fastforce simp add: pcs_shift_conv)
apply clarsimp
apply(rule conjI, fastforce simp:wt_instr_appRx)
apply clarsimp
apply(erule_tac x = "pc - size is\<^sub>1" in allE)+
apply(thin_tac "P \<longrightarrow> Q" for P Q)
apply(erule impE, arith) 
apply(drule_tac \<tau>s' = "\<tau>s\<^sub>1" in wt_instr_appL)
  apply arith
 apply simp
apply(fastforce simp add:add.commute intro!: wt_instr_appLx)
done


corollary wt_instrs_ext2:
  "\<lbrakk> \<turnstile> is\<^sub>2,xt\<^sub>2 [::] \<tau>s\<^sub>2; \<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2; size \<tau>s\<^sub>1 = size is\<^sub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^sub>1@is\<^sub>2, xt\<^sub>1 @ shift (size is\<^sub>1) xt\<^sub>2 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2"
by(rule wt_instrs_ext)


corollary wt_instrs_ext_prefix [trans]:
  "\<lbrakk> \<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2; \<turnstile> is\<^sub>2,xt\<^sub>2 [::] \<tau>s\<^sub>3;
     size \<tau>s\<^sub>1 = size is\<^sub>1; \<tau>s\<^sub>3 \<le> \<tau>s\<^sub>2 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^sub>1@is\<^sub>2, xt\<^sub>1 @ shift (size is\<^sub>1) xt\<^sub>2 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2"
by(bestsimp simp:less_eq_list_def prefix_def elim: wt_instrs_ext dest:wt_instrs_extR)


corollary wt_instrs_app:
  assumes is\<^sub>1: "\<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>s\<^sub>1@[\<tau>]"
  assumes is\<^sub>2: "\<turnstile> is\<^sub>2,xt\<^sub>2 [::] \<tau>#\<tau>s\<^sub>2"
  assumes s: "size \<tau>s\<^sub>1 = size is\<^sub>1"
  shows "\<turnstile> is\<^sub>1@is\<^sub>2, xt\<^sub>1@shift (size is\<^sub>1) xt\<^sub>2 [::] \<tau>s\<^sub>1@\<tau>#\<tau>s\<^sub>2"
proof -
  from is\<^sub>1 have "\<turnstile> is\<^sub>1,xt\<^sub>1 [::] (\<tau>s\<^sub>1@[\<tau>])@\<tau>s\<^sub>2"
    by (rule wt_instrs_extR)
  hence "\<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>s\<^sub>1@\<tau>#\<tau>s\<^sub>2" by simp
  from this is\<^sub>2 s show ?thesis by (rule wt_instrs_ext) 
qed


corollary wt_instrs_app_last[trans]:
  "\<lbrakk> \<turnstile> is\<^sub>2,xt\<^sub>2 [::] \<tau>#\<tau>s\<^sub>2; \<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>s\<^sub>1;
     last \<tau>s\<^sub>1 = \<tau>;  size \<tau>s\<^sub>1 = size is\<^sub>1+1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^sub>1@is\<^sub>2, xt\<^sub>1@shift (size is\<^sub>1) xt\<^sub>2 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2"
apply(cases \<tau>s\<^sub>1 rule:rev_cases)
 apply simp
apply(simp add:wt_instrs_app)
done


corollary wt_instrs_append_last[trans]:
  "\<lbrakk> \<turnstile> is,xt [::] \<tau>s; P,T\<^sub>r,mxs,mpc,[] \<turnstile> i,pc :: \<tau>s;
     pc = size is; mpc = size \<tau>s; size is + 1 < size \<tau>s \<rbrakk>
  \<Longrightarrow> \<turnstile> is@[i],xt [::] \<tau>s"
apply(clarsimp simp add:wt_instrs_def)
apply(rule conjI, fastforce)
apply(fastforce intro!:wt_instr_appLx[where xt = "[]",simplified]
               dest!:less_antisym)
done


corollary wt_instrs_app2:
  "\<lbrakk> \<turnstile> (is\<^sub>2 :: 'b instr list),xt\<^sub>2 [::] \<tau>'#\<tau>s\<^sub>2;  \<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>#\<tau>s\<^sub>1@[\<tau>'];
     xt' = xt\<^sub>1 @ shift (size is\<^sub>1) xt\<^sub>2;  size \<tau>s\<^sub>1+1 = size is\<^sub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^sub>1@is\<^sub>2,xt' [::] \<tau>#\<tau>s\<^sub>1@\<tau>'#\<tau>s\<^sub>2"
using wt_instrs_app[where ?\<tau>s\<^sub>1.0 = "\<tau> # \<tau>s\<^sub>1" and ?'b = "'b"] by simp


corollary wt_instrs_app2_simp[trans,simp]:
  "\<lbrakk> \<turnstile> (is\<^sub>2 :: 'b instr list),xt\<^sub>2 [::] \<tau>'#\<tau>s\<^sub>2;  \<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>#\<tau>s\<^sub>1@[\<tau>']; size \<tau>s\<^sub>1+1 = size is\<^sub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^sub>1@is\<^sub>2, xt\<^sub>1@shift (size is\<^sub>1) xt\<^sub>2 [::] \<tau>#\<tau>s\<^sub>1@\<tau>'#\<tau>s\<^sub>2"
using wt_instrs_app[where ?\<tau>s\<^sub>1.0 = "\<tau> # \<tau>s\<^sub>1" and ?'b = "'b"] by simp


corollary wt_instrs_Cons[simp]:
  "\<lbrakk> \<tau>s \<noteq> []; \<turnstile> [i],[] [::] [\<tau>,\<tau>']; \<turnstile> is,xt [::] \<tau>'#\<tau>s \<rbrakk>
  \<Longrightarrow> \<turnstile> i#is,shift 1 xt [::] \<tau>#\<tau>'#\<tau>s"
using wt_instrs_app2[where ?is\<^sub>1.0 = "[i]" and ?\<tau>s\<^sub>1.0 = "[]" and ?is\<^sub>2.0 = "is"
                      and ?xt\<^sub>1.0 = "[]"]
by simp


corollary wt_instrs_Cons2[trans]:
  assumes \<tau>s: "\<turnstile> is,xt [::] \<tau>s"
  assumes i: "P,T\<^sub>r,mxs,mpc,[] \<turnstile> i,0 :: \<tau>#\<tau>s"
  assumes mpc: "mpc = size \<tau>s + 1"
  shows "\<turnstile> i#is,shift 1 xt [::] \<tau>#\<tau>s"
proof -
  from \<tau>s have "\<tau>s \<noteq> []" by (auto simp: wt_instrs_def)
  with mpc i have "\<turnstile> [i],[] [::] [\<tau>]@\<tau>s" by (simp add: wt_instrs_def)
  with \<tau>s show ?thesis by (fastforce dest: wt_instrs_ext)
qed


lemma wt_instrs_last_incr[trans]:
  "\<lbrakk> \<turnstile> is,xt [::] \<tau>s@[\<tau>]; P \<turnstile> \<tau> \<le>' \<tau>' \<rbrakk> \<Longrightarrow> \<turnstile> is,xt [::] \<tau>s@[\<tau>']"
apply(clarsimp simp add:wt_instrs_def wt_instr_def)
apply(rule conjI)
apply(fastforce)
apply(clarsimp)
apply(rename_tac pc' tau')
apply(erule allE, erule (1) impE)
apply(clarsimp)
apply(drule (1) bspec)
apply(clarsimp)
apply(subgoal_tac "pc' = size \<tau>s")
prefer 2
apply(clarsimp simp:app_def)
apply(drule (1) bspec)
apply(clarsimp)
apply(auto elim!:sup_state_opt_trans)
done

end

lemma [iff]: "xcpt_app i P pc mxs [] \<tau>"
by (simp add: xcpt_app_def relevant_entries_def)


lemma [simp]: "xcpt_eff i P pc \<tau> [] = []"
by (simp add: xcpt_eff_def relevant_entries_def)

context TC2 begin

lemma wt_New:
  "\<lbrakk> is_class P C; size ST < mxs \<rbrakk> \<Longrightarrow>
   \<turnstile> [New C],[] [::] [ty\<^sub>i' ST E A, ty\<^sub>i' (Class C#ST) E A]"
by(simp add:wt_defs ty\<^sub>i'_def)


lemma wt_Cast:
  "is_type P T \<Longrightarrow>
   \<turnstile> [Checkcast T],[] [::] [ty\<^sub>i' (U # ST) E A, ty\<^sub>i' (T # ST) E A]"
by(simp add: ty\<^sub>i'_def wt_defs)

lemma wt_Instanceof:
  "\<lbrakk> is_type P T; is_refT U \<rbrakk> \<Longrightarrow>
   \<turnstile> [Instanceof T],[] [::] [ty\<^sub>i' (U # ST) E A, ty\<^sub>i' (Boolean # ST) E A]"
by(simp add: ty\<^sub>i'_def wt_defs)

lemma wt_Push:
  "\<lbrakk> size ST < mxs; typeof v = Some T \<rbrakk>
  \<Longrightarrow> \<turnstile> [Push v],[] [::] [ty\<^sub>i' ST E A, ty\<^sub>i' (T#ST) E A]"
by(simp add: ty\<^sub>i'_def wt_defs)


lemma wt_Pop:
 "\<turnstile> [Pop],[] [::] (ty\<^sub>i' (T#ST) E A # ty\<^sub>i' ST E A # \<tau>s)"
by(simp add: ty\<^sub>i'_def wt_defs)

lemma wt_BinOpInstr:
  "P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T \<Longrightarrow> \<turnstile> [BinOpInstr bop],[] [::] [ty\<^sub>i' (T2 # T1 # ST) E A, ty\<^sub>i' (T # ST) E A]"
by(auto simp:ty\<^sub>i'_def wt_defs dest: WT_binop_WTrt_binop intro: list_all2_refl)

lemma wt_Load:
  "\<lbrakk> size ST < mxs; size E \<le> mxl; i \<in>\<in> A; i < size E \<rbrakk>
  \<Longrightarrow> \<turnstile> [Load i],[] [::] [ty\<^sub>i' ST E A, ty\<^sub>i' (E!i # ST) E A]"
by(auto simp add:ty\<^sub>i'_def wt_defs ty\<^sub>l_def hyperset_defs intro: widens_refl)


lemma wt_Store:
 "\<lbrakk> P \<turnstile> T \<le> E!i; i < size E; size E \<le> mxl \<rbrakk> \<Longrightarrow>
  \<turnstile> [Store i],[] [::] [ty\<^sub>i' (T#ST) E A, ty\<^sub>i' ST E (\<lfloor>{i}\<rfloor> \<squnion> A)]"
by(auto simp:hyperset_defs nth_list_update ty\<^sub>i'_def wt_defs ty\<^sub>l_def
        intro:list_all2_all_nthI)


lemma wt_Get:
 "\<lbrakk> P \<turnstile> C sees F:T (fm) in D; class_type_of' U = \<lfloor>C\<rfloor> \<rbrakk> \<Longrightarrow>
  \<turnstile> [Getfield F D],[] [::] [ty\<^sub>i' (U # ST) E A, ty\<^sub>i' (T # ST) E A]"
by(cases U)(auto simp: ty\<^sub>i'_def wt_defs dest: sees_field_idemp sees_field_decl_above intro: widens_refl widen_trans widen_array_object)

lemma wt_Put:
  "\<lbrakk> P \<turnstile> C sees F:T (fm) in D; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> T' \<le> T \<rbrakk> \<Longrightarrow>
  \<turnstile> [Putfield F D],[] [::] [ty\<^sub>i' (T' # U # ST) E A, ty\<^sub>i' ST E A]"
by(cases U)(auto 4 3 intro: sees_field_idemp widen_trans widen_array_object dest: sees_field_decl_above simp: ty\<^sub>i'_def wt_defs)

lemma wt_CAS:
  "\<lbrakk> P \<turnstile> C sees F:T (fm) in D; class_type_of' U' = \<lfloor>C\<rfloor>; volatile fm; P \<turnstile> T2 \<le> T; P \<turnstile> T3 \<le> T \<rbrakk> \<Longrightarrow>
  \<turnstile> [CAS F D],[] [::] [ty\<^sub>i' (T3 # T2 # U' # ST) E A, ty\<^sub>i' (Boolean # ST) E A]"
by(cases U')(auto 4 4 simp add: ty\<^sub>i'_def wt_defs intro: sees_field_idemp widen_trans widen_array_object dest: sees_field_decl_above)

lemma wt_Throw:
  "P \<turnstile> C \<preceq>\<^sup>* Throwable \<Longrightarrow> \<turnstile> [ThrowExc],[] [::] [ty\<^sub>i' (Class C # ST) E A, \<tau>']"
by(simp add: ty\<^sub>i'_def wt_defs)


lemma wt_IfFalse:
  "\<lbrakk> 2 \<le> i; nat i < size \<tau>s + 2; P \<turnstile> ty\<^sub>i' ST E A \<le>' \<tau>s ! nat(i - 2) \<rbrakk>
  \<Longrightarrow> \<turnstile> [IfFalse i],[] [::] ty\<^sub>i' (Boolean # ST) E A # ty\<^sub>i' ST E A # \<tau>s"
by(auto simp add: ty\<^sub>i'_def wt_defs eval_nat_numeral nat_diff_distrib)


lemma wt_Goto:
 "\<lbrakk> 0 \<le> int pc + i; nat (int pc + i) < size \<tau>s; size \<tau>s \<le> mpc;
    P \<turnstile> \<tau>s!pc \<le>' \<tau>s ! nat (int pc + i) \<rbrakk>
 \<Longrightarrow> P,T,mxs,mpc,[] \<turnstile> Goto i,pc :: \<tau>s"
by(clarsimp simp add: wt_defs)

end

context TC3 begin

lemma wt_Invoke:
  "\<lbrakk> size es = size Ts'; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C sees M: Ts\<rightarrow>T = m in D; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> \<turnstile> [Invoke M (size es)],[] [::] [ty\<^sub>i' (rev Ts' @ U # ST) E A, ty\<^sub>i' (T#ST) E A]"
apply(clarsimp simp add: ty\<^sub>i'_def wt_defs)
apply safe
apply(simp_all (no_asm_use))
apply(auto simp add: intro: widens_refl)
done

end

declare nth_append[simp del]
declare [[simproc del: list_to_set_comprehension]]

context TC2 begin

corollary wt_instrs_app3[simp]:
  "\<lbrakk> \<turnstile> (is\<^sub>2 :: 'b instr list),[] [::] (\<tau>' # \<tau>s\<^sub>2);  \<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau> # \<tau>s\<^sub>1 @ [\<tau>']; size \<tau>s\<^sub>1+1 = size is\<^sub>1\<rbrakk>
  \<Longrightarrow> \<turnstile> (is\<^sub>1 @ is\<^sub>2),xt\<^sub>1 [::] \<tau> # \<tau>s\<^sub>1 @ \<tau>' # \<tau>s\<^sub>2"
using wt_instrs_app2[where ?xt\<^sub>2.0 = "[]" and ?'b = "'b"] by (simp add:shift_def)


corollary wt_instrs_Cons3[simp]:
  "\<lbrakk> \<tau>s \<noteq> []; \<turnstile> [i],[] [::] [\<tau>,\<tau>']; \<turnstile> is,[] [::] \<tau>'#\<tau>s \<rbrakk>
  \<Longrightarrow> \<turnstile> (i # is),[] [::] \<tau> # \<tau>' # \<tau>s"
using wt_instrs_Cons[where ?xt = "[]"]
by (simp add:shift_def)

lemma wt_instrs_xapp:
  "\<lbrakk> \<turnstile> is\<^sub>1 @ is\<^sub>2, xt [::] \<tau>s\<^sub>1 @ ty\<^sub>i' (Class D # ST) E A # \<tau>s\<^sub>2;
     \<forall>\<tau> \<in> set \<tau>s\<^sub>1. \<forall>ST' LT'. \<tau> = Some(ST',LT') \<longrightarrow> 
      size ST \<le> size ST' \<and> P \<turnstile> Some (drop (size ST' - size ST) ST',LT') \<le>' ty\<^sub>i' ST E A;
     size is\<^sub>1 = size \<tau>s\<^sub>1; size ST < mxs; case Co of None \<Rightarrow> D = Throwable | Some C \<Rightarrow> D = C \<and> is_class P C  \<rbrakk> \<Longrightarrow>
  \<turnstile> is\<^sub>1 @ is\<^sub>2, xt @ [(0,size is\<^sub>1 - Suc n,Co,size is\<^sub>1,size ST)] [::] \<tau>s\<^sub>1 @ ty\<^sub>i' (Class D # ST) E A # \<tau>s\<^sub>2"
apply(simp add:wt_instrs_def split del: option.split_asm)
apply(rule conjI)
 apply(clarsimp split del: option.split_asm)
 apply arith
apply(clarsimp split del: option.split_asm)
apply(erule allE, erule (1) impE)
apply(clarsimp simp add: wt_instr_def app_def eff_def split del: option.split_asm)
apply(rule conjI)
 apply (thin_tac "\<forall>x\<in> A \<union> B. P x" for A B P)
 apply (thin_tac "\<forall>x\<in> A \<union> B. P x" for A B P)
 apply (clarsimp simp add: xcpt_app_def relevant_entries_def split del: option.split_asm)
 apply (simp add: nth_append is_relevant_entry_def split: if_split_asm split del: option.split_asm)
  apply (drule_tac x="\<tau>s\<^sub>1!pc" in bspec)
   apply (blast intro: nth_mem) 
  apply fastforce
 apply fastforce
apply (rule conjI)
 apply(clarsimp split del: option.split_asm)
 apply (erule disjE, blast)
 apply (erule disjE, blast)
 apply (clarsimp simp add: xcpt_eff_def relevant_entries_def split: if_split_asm)
apply(clarsimp split del: option.split_asm)
apply (erule disjE, blast)
apply (erule disjE, blast)
apply (clarsimp simp add: xcpt_eff_def relevant_entries_def split: if_split_asm split del: option.split_asm)
apply (simp add: nth_append is_relevant_entry_def split: if_split_asm split del: option.split_asm)
 apply (drule_tac x = "\<tau>s\<^sub>1!pc" in bspec)
  apply (blast intro: nth_mem)
 apply (fastforce simp add: ty\<^sub>i'_def)
done

lemma wt_instrs_xapp_Some[trans]:
  "\<lbrakk> \<turnstile> is\<^sub>1 @ is\<^sub>2, xt [::] \<tau>s\<^sub>1 @ ty\<^sub>i' (Class C # ST) E A # \<tau>s\<^sub>2;
     \<forall>\<tau> \<in> set \<tau>s\<^sub>1. \<forall>ST' LT'. \<tau> = Some(ST',LT') \<longrightarrow> 
      size ST \<le> size ST' \<and> P \<turnstile> Some (drop (size ST' - size ST) ST',LT') \<le>' ty\<^sub>i' ST E A;
     size is\<^sub>1 = size \<tau>s\<^sub>1; is_class P C; size ST < mxs  \<rbrakk> \<Longrightarrow>
  \<turnstile> is\<^sub>1 @ is\<^sub>2, xt @ [(0,size is\<^sub>1 - Suc n,Some C,size is\<^sub>1,size ST)] [::] \<tau>s\<^sub>1 @ ty\<^sub>i' (Class C # ST) E A # \<tau>s\<^sub>2"
by(erule (3) wt_instrs_xapp) simp

lemma wt_instrs_xapp_Any:
  "\<lbrakk> \<turnstile> is\<^sub>1 @ is\<^sub>2, xt [::] \<tau>s\<^sub>1 @ ty\<^sub>i' (Class Throwable # ST) E A # \<tau>s\<^sub>2;
     \<forall>\<tau> \<in> set \<tau>s\<^sub>1. \<forall>ST' LT'. \<tau> = Some(ST',LT') \<longrightarrow> 
      size ST \<le> size ST' \<and> P \<turnstile> Some (drop (size ST' - size ST) ST',LT') \<le>' ty\<^sub>i' ST E A;
     size is\<^sub>1 = size \<tau>s\<^sub>1; size ST < mxs \<rbrakk> \<Longrightarrow>
  \<turnstile> is\<^sub>1 @ is\<^sub>2, xt @ [(0,size is\<^sub>1 - Suc n,None,size is\<^sub>1,size ST)] [::] \<tau>s\<^sub>1 @ ty\<^sub>i' (Class Throwable # ST) E A # \<tau>s\<^sub>2"
by(erule (3) wt_instrs_xapp) simp

end

declare [[simproc add: list_to_set_comprehension]]
declare nth_append[simp]

lemma drop_Cons_Suc:
  "\<And>xs. drop n xs = y#ys \<Longrightarrow> drop (Suc n) xs = ys"
  apply (induct n)
   apply simp
  apply (simp add: drop_Suc)
  done

lemma drop_mess:
  "\<lbrakk>Suc (length xs\<^sub>0) \<le> length xs; drop (length xs - Suc (length xs\<^sub>0)) xs = x # xs\<^sub>0\<rbrakk> 
  \<Longrightarrow> drop (length xs - length xs\<^sub>0) xs = xs\<^sub>0"
apply (cases xs)
 apply simp
apply (simp add: Suc_diff_le)
apply (case_tac "length list - length xs\<^sub>0")
 apply simp
apply (simp add: drop_Cons_Suc)
done

lemma drop_mess2:
  assumes len: "Suc (Suc (length xs0)) \<le> length xs" 
  and drop: "drop (length xs - Suc (Suc (length xs0))) xs = x1 # x2 # xs0"
  shows "drop (length xs - length xs0) xs = xs0"
proof(cases xs)
  case Nil with assms show ?thesis by simp
next
  case (Cons x xs')
  note Cons[simp]
  show ?thesis
  proof(cases xs')
    case Nil with assms show ?thesis by(simp)
  next
    case (Cons x' xs'')
    note Cons[simp]
    show ?thesis 
    proof(rule drop_mess)
      from len show "Suc (length xs0) \<le> length xs" by simp
    next
      have "drop (length xs - length (x2 # xs0)) xs = x2 # xs0"
      proof(rule drop_mess)
        from len show "Suc (length (x2 # xs0)) \<le> length xs" by(simp)
      next
        from drop show "drop (length xs - Suc (length (x2 # xs0))) xs = x1 # x2 # xs0" by simp
      qed
      thus "drop (length xs - Suc (length xs0)) xs = x2 # xs0" by(simp)
    qed
  qed
qed

abbreviation postfix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  ("(_/ \<bind> _)" [51, 50] 50) where
  "postfix xs ys \<equiv> suffix ys xs"

lemma postfix_conv_eq_length_drop: 
  "ST' \<bind> ST \<longleftrightarrow> length ST \<le> length ST' \<and> drop (length ST' - length ST) ST' = ST"
apply(auto)
apply (metis append_eq_conv_conj append_take_drop_id diff_is_0_eq drop_0 linorder_not_less nat_le_linear suffix_take)
apply (metis append_take_drop_id length_drop suffix_take same_append_eq size_list_def)
by (metis suffix_drop)

declare suffix_ConsI[simp]

context TC0 begin

declare after_def[simp] pair_eq_ty\<^sub>i'_conv[simp] 

lemma
  assumes "ST0 \<bind> ST'"
  shows compT_ST_prefix: 
  "\<lfloor>(ST,LT)\<rfloor> \<in> set(compT E A ST0 e) \<Longrightarrow> ST \<bind> ST'"

  and compTs_ST_prefix:
  "\<lfloor>(ST,LT)\<rfloor> \<in> set(compTs E A ST0 es) \<Longrightarrow> ST \<bind> ST'"
using assms
by(induct E A ST0 e and E A ST0 es rule: compT_compTs_induct) auto

declare after_def[simp del] pair_eq_ty\<^sub>i'_conv[simp del]

end
declare suffix_ConsI[simp del]

(* FIXME *)
lemma fun_of_simp [simp]: "fun_of S x y = ((x,y) \<in> S)" 
by (simp add: fun_of_def)

declare widens_refl [iff]

context TC3 begin

theorem compT_wt_instrs:
  "\<lbrakk> P,E \<turnstile>1 e :: T; \<D> e A; \<B> e (size E); size ST + max_stack e \<le> mxs; size E + max_vars e \<le> mxl; set E \<subseteq> types P \<rbrakk>
  \<Longrightarrow> \<turnstile> compE2 e, compxE2 e 0 (size ST) [::] ty\<^sub>i' ST E A # compT E A ST e @ [after E A ST e]"
  (is "PROP ?P e E T A ST")

  and compTs_wt_instrs:
  "\<lbrakk> P,E \<turnstile>1 es[::]Ts;  \<D>s es A; \<B>s es (size E); size ST + max_stacks es \<le> mxs; size E + max_varss es \<le> mxl; set E \<subseteq> types P \<rbrakk>
  \<Longrightarrow> let \<tau>s = ty\<^sub>i' ST E A # compTs E A ST es
      in \<turnstile> compEs2 es,compxEs2 es 0 (size ST) [::] \<tau>s \<and> last \<tau>s = ty\<^sub>i' (rev Ts @ ST) E (A \<squnion> \<A>s es)"
  (is "PROP ?Ps es E Ts A ST")
proof(induct E A ST e and E A ST es arbitrary: T and Ts rule: compT_compTs_induct)
  case (TryCatch E A ST e\<^sub>1 C i e\<^sub>2)
  hence [simp]: "i = size E" by simp
  have wt\<^sub>1: "P,E \<turnstile>1 e\<^sub>1 :: T" and wt\<^sub>2: "P,E@[Class C] \<turnstile>1 e\<^sub>2 :: T"
    and "class": "is_class P C" using TryCatch by auto
  let ?A\<^sub>1 = "A \<squnion> \<A> e\<^sub>1" let ?A\<^sub>i = "A \<squnion> \<lfloor>{i}\<rfloor>" let ?E\<^sub>i = "E @ [Class C]"
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s\<^sub>1 = "compT E A ST e\<^sub>1"
  let ?\<tau>\<^sub>1 = "ty\<^sub>i' (T#ST) E ?A\<^sub>1" let ?\<tau>\<^sub>2 = "ty\<^sub>i' (Class C#ST) E A"
  let ?\<tau>\<^sub>3 = "ty\<^sub>i' ST ?E\<^sub>i ?A\<^sub>i" let ?\<tau>s\<^sub>2 = "compT ?E\<^sub>i ?A\<^sub>i ST e\<^sub>2"
  let ?\<tau>\<^sub>2' = "ty\<^sub>i' (T#ST) ?E\<^sub>i (?A\<^sub>i \<squnion> \<A> e\<^sub>2)"
  let ?\<tau>' = "ty\<^sub>i' (T#ST) E (A \<squnion> \<A> e\<^sub>1 \<sqinter> (\<A> e\<^sub>2 \<ominus> i))"
  let ?go = "Goto (int(size(compE2 e\<^sub>2)) + 2)"
  have "PROP ?P e\<^sub>2 ?E\<^sub>i T ?A\<^sub>i ST" by fact
  hence "\<turnstile> compE2 e\<^sub>2,compxE2 e\<^sub>2 0 (size ST) [::] (?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2) @ [?\<tau>\<^sub>2']"
    using TryCatch.prems "class" by(auto simp:after_def)
  also have "?A\<^sub>i \<squnion> \<A> e\<^sub>2 = (A \<squnion> \<A> e\<^sub>2) \<squnion> \<lfloor>{size E}\<rfloor>"
    by(fastforce simp:hyperset_defs)
  also have "P \<turnstile> ty\<^sub>i' (T#ST) ?E\<^sub>i \<dots> \<le>' ty\<^sub>i' (T#ST) E (A \<squnion> \<A> e\<^sub>2)"
    by(simp add:hyperset_defs ty\<^sub>l_incr ty\<^sub>i'_def)
  also have "P \<turnstile> \<dots> \<le>' ty\<^sub>i' (T#ST) E (A \<squnion> \<A> e\<^sub>1 \<sqinter> (\<A> e\<^sub>2 \<ominus> i))"
    by(auto intro!: ty\<^sub>l_antimono simp:hyperset_defs ty\<^sub>i'_def)
  also have "(?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2) @ [?\<tau>'] = ?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2 @ [?\<tau>']" by simp
  also have "\<turnstile> [Store i],[] [::] ?\<tau>\<^sub>2 # [] @ [?\<tau>\<^sub>3]"
    using TryCatch.prems
    by(auto simp:nth_list_update wt_defs ty\<^sub>i'_def ty\<^sub>l_def
      list_all2_conv_all_nth hyperset_defs)
  also have "[] @ (?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2 @ [?\<tau>']) = (?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2 @ [?\<tau>'])" by simp
  also have "P,T\<^sub>r,mxs,size(compE2 e\<^sub>2)+3,[] \<turnstile> ?go,0 :: ?\<tau>\<^sub>1#?\<tau>\<^sub>2#?\<tau>\<^sub>3#?\<tau>s\<^sub>2 @ [?\<tau>']"
    by(auto simp: hyperset_defs ty\<^sub>i'_def wt_defs nth_Cons nat_add_distrib
      fun_of_def intro: ty\<^sub>l_antimono list_all2_refl split:nat.split)
  also have "\<turnstile> compE2 e\<^sub>1,compxE2 e\<^sub>1 0 (size ST) [::] ?\<tau> # ?\<tau>s\<^sub>1 @ [?\<tau>\<^sub>1]"
    using TryCatch by(auto simp:after_def)
  also have "?\<tau> # ?\<tau>s\<^sub>1 @ ?\<tau>\<^sub>1 # ?\<tau>\<^sub>2 # ?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2 @ [?\<tau>'] =
             (?\<tau> # ?\<tau>s\<^sub>1 @ [?\<tau>\<^sub>1]) @ ?\<tau>\<^sub>2 # ?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2 @ [?\<tau>']" by simp
  also have "compE2 e\<^sub>1 @ ?go  # [Store i] @ compE2 e\<^sub>2 =
             (compE2 e\<^sub>1 @ [?go]) @ (Store i # compE2 e\<^sub>2)" by simp
  also 
  let "?Q \<tau>" = "\<forall>ST' LT'. \<tau> = \<lfloor>(ST', LT')\<rfloor> \<longrightarrow> 
    size ST \<le> size ST' \<and> P \<turnstile> Some (drop (size ST' - size ST) ST',LT') \<le>' ty\<^sub>i' ST E A"
  {
    have "?Q (ty\<^sub>i' ST E A)" by(clarsimp simp add: ty\<^sub>i'_def)
    moreover have "?Q (ty\<^sub>i' (T # ST) E ?A\<^sub>1)" 
      by (fastforce simp add: ty\<^sub>i'_def hyperset_defs intro!: ty\<^sub>l_antimono)
    moreover { fix \<tau>
      assume \<tau>: "\<tau> \<in> set (compT E A ST e\<^sub>1)"
      hence "\<forall>ST' LT'. \<tau> = \<lfloor>(ST', LT')\<rfloor> \<longrightarrow> ST' \<bind> ST" by(auto intro: compT_ST_prefix[OF suffix_order.order_refl])
      with \<tau> have "?Q \<tau>" unfolding postfix_conv_eq_length_drop using \<open>\<B> (try e\<^sub>1 catch(C i) e\<^sub>2) (length E)\<close>
        by(fastforce dest!: compT_LT_prefix simp add: ty\<^sub>i'_def) }
    ultimately
    have "\<forall>\<tau>\<in>set (ty\<^sub>i' ST E A # compT E A ST e\<^sub>1 @ [ty\<^sub>i' (T # ST) E ?A\<^sub>1]). ?Q \<tau>" by auto
  }
  also from TryCatch.prems max_stack1[of e\<^sub>1] have "size ST + 1 \<le> mxs" by auto
  ultimately show ?case using wt\<^sub>1 wt\<^sub>2 TryCatch.prems "class"
    by (simp add:after_def)(erule_tac x=0 in meta_allE, simp)
next
  case (Synchronized E A ST i e1 e2)
  note wt = \<open>P,E \<turnstile>1 sync\<^bsub>i\<^esub> (e1) e2 :: T\<close>
  then obtain U where wt1: "P,E \<turnstile>1 e1 :: U"
    and U: "is_refT U" "U \<noteq> NT"
    and wt2: "P,E@[Class Object] \<turnstile>1 e2 :: T" by auto
  from \<open>\<B> (sync\<^bsub>i\<^esub> (e1) e2) (length E)\<close> have [simp]: "i = length E"
    and B1: "\<B> e1 (length E)" and B2: "\<B> e2 (length (E@[Class Object]))" by auto
  
  note lenST = \<open>length ST + max_stack (sync\<^bsub>i\<^esub> (e1) e2) \<le> mxs\<close> 
  note lenE = \<open>length E + max_vars (sync\<^bsub>i\<^esub> (e1) e2) \<le> mxl\<close>

  let ?A1 = "A \<squnion> \<A> e1" let ?A2 = "?A1 \<squnion> \<lfloor>{i}\<rfloor>"
  let ?A3 = "?A2 \<squnion> \<A> e2" let ?A4 = "?A1 \<squnion> \<A> e2"
  let ?E1 = "E @ [Class Object]"
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s1 = "compT E A ST e1"
  let ?\<tau>1 = "ty\<^sub>i' (U#ST) E ?A1"
  let ?\<tau>1' = "ty\<^sub>i' (Class Object # Class Object # ST) E ?A1"
  let ?\<tau>1'' = "ty\<^sub>i' (Class Object#ST) ?E1 ?A2"
  let ?\<tau>1''' = "ty\<^sub>i' ST ?E1 ?A2"
  let ?\<tau>s2 = "compT ?E1 ?A2 ST e2"
  let ?\<tau>2 = "ty\<^sub>i' (T#ST) ?E1 ?A3" let ?\<tau>2' = "ty\<^sub>i' (Class Object#T#ST) ?E1 ?A3"
  let ?\<tau>2'' = ?\<tau>2
  let ?\<tau>3 = "ty\<^sub>i' (Class Throwable#ST) ?E1 ?A2"
  let ?\<tau>3' = "ty\<^sub>i' (Class Object#Class Throwable#ST) ?E1 ?A2"
  let ?\<tau>3'' = ?\<tau>3
  let ?\<tau>' = "ty\<^sub>i' (T#ST) E ?A4"

  from lenE lenST max_stack1[of e2] U 
  have "\<turnstile> [Load i, MExit, ThrowExc], [] [::] [?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
    by(auto simp add: ty\<^sub>i'_def ty\<^sub>l_def wt_defs hyperset_defs nth_Cons split: nat.split)
  also have "P,T\<^sub>r,mxs,5,[] \<turnstile> Goto 4,0 :: [?\<tau>2'', ?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
    by(auto simp: hyperset_defs ty\<^sub>i'_def wt_defs intro: ty\<^sub>l_antimono ty\<^sub>l_incr)
  also have "P,T\<^sub>r,mxs,6,[] \<turnstile> MExit,0 :: [?\<tau>2', ?\<tau>2'', ?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
    by(auto simp: hyperset_defs ty\<^sub>i'_def wt_defs intro: ty\<^sub>l_antimono ty\<^sub>l_incr)
  also from lenE lenST max_stack1[of e2]
  have "P,T\<^sub>r,mxs,7,[] \<turnstile> Load i,0 :: [?\<tau>2, ?\<tau>2', ?\<tau>2'', ?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
    by(auto simp: hyperset_defs ty\<^sub>i'_def wt_defs ty\<^sub>l_def intro: ty\<^sub>l_antimono)
  also from \<open>\<D> (sync\<^bsub>i\<^esub> (e1) e2) A\<close> have "\<D> e2 (A \<squnion> \<A> e1 \<squnion> \<lfloor>{length E}\<rfloor>)"
    by(auto elim!: D_mono' simp add: hyperset_defs)
  with \<open>PROP ?P e2 ?E1 T ?A2 ST\<close> Synchronized wt2 is_class_Object[OF wf_prog]
  have "\<turnstile> compE2 e2, compxE2 e2 0 (size ST) [::] ?\<tau>1'''#?\<tau>s2@[?\<tau>2]"
    by(auto simp add: after_def)
  finally have "\<turnstile> (compE2 e2 @ [Load i, MExit, Goto 4]) @ [Load i, MExit, ThrowExc], compxE2 e2 0 (size ST) [::]
             (?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2'']) @ [?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
    by(simp)
  hence "\<turnstile> (compE2 e2 @ [Load i, MExit, Goto 4]) @ [Load i, MExit, ThrowExc],
           compxE2 e2 0 (size ST) @ [(0, size (compE2 e2 @ [Load i, MExit, Goto 4]) - Suc 2, None, size (compE2 e2 @ [Load i, MExit, Goto 4]), size ST)] [::]
           (?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2'']) @ [?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
  proof(rule wt_instrs_xapp_Any)
    from lenST show "length ST < mxs" by simp
  next
    show "\<forall>\<tau>\<in>set (?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2'']). \<forall>ST' LT'.
          \<tau> = \<lfloor>(ST', LT')\<rfloor> \<longrightarrow> length ST \<le> length ST' \<and>
          P \<turnstile> \<lfloor>(drop (length ST' - length ST) ST',  LT')\<rfloor> \<le>' ty\<^sub>i' ST (E @ [Class Object]) ?A2"
    proof(intro strip)
      fix \<tau> ST' LT'
      assume "\<tau>\<in>set (?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2''])" "\<tau> = \<lfloor>(ST', LT')\<rfloor>"
      hence \<tau>: "\<lfloor>(ST', LT')\<rfloor> \<in> set (?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2''])" by simp
      show "length ST \<le> length ST' \<and> P \<turnstile> \<lfloor>(drop (length ST' - length ST) ST',  LT')\<rfloor> \<le>' ty\<^sub>i' ST (E @ [Class Object]) ?A2"
      proof(cases "\<lfloor>(ST', LT')\<rfloor> \<in> set ?\<tau>s2")
        case True
        from compT_ST_prefix[OF suffix_order.order_refl this] compT_LT_prefix[OF this B2]
        show ?thesis unfolding postfix_conv_eq_length_drop by(simp add: ty\<^sub>i'_def)
      next
        case False
        with \<tau> show ?thesis
          by(auto simp add: ty\<^sub>i'_def hyperset_defs intro: ty\<^sub>l_antimono)
      qed
    qed
  qed simp
  hence "\<turnstile> compE2 e2 @ [Load i, MExit, Goto 4, Load i, MExit, ThrowExc],
           compxE2 e2 0 (size ST) @ [(0, size (compE2 e2), None, Suc (Suc (Suc (size (compE2 e2)))), size ST)] [::]
           ?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2'', ?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']" by simp
  also from wt1 \<open>set E \<subseteq> types P\<close> have "is_type P U" by(rule WT1_is_type[OF wf_prog])
  with U have "P \<turnstile> U \<le> Class Object" by(auto elim!: is_refT.cases intro: subcls_C_Object[OF _ wf_prog] widen_array_object)
  with lenE lenST max_stack1[of e2]
  have "\<turnstile> [Dup, Store i, MEnter], [] [::] [?\<tau>1, ?\<tau>1', ?\<tau>1''] @ [?\<tau>1''']"
    by(auto simp add: ty\<^sub>i'_def ty\<^sub>l_def wt_defs hyperset_defs nth_Cons nth_list_update list_all2_conv_all_nth split: nat.split)
  finally have "\<turnstile> Dup # Store i # MEnter # compE2 e2 @ [Load i, MExit, Goto 4, Load i, MExit, ThrowExc],
               compxE2 e2 3 (size ST) @ [(3, 3 + size (compE2 e2), None, 6 + size (compE2 e2), size ST)]
            [::] ?\<tau>1 # ?\<tau>1' # ?\<tau>1'' # ?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2'', ?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
    by(simp add: eval_nat_numeral shift_def)
  also from \<open>PROP ?P e1 E U A ST\<close> wt1 B1 \<open>\<D> (sync\<^bsub>i\<^esub> (e1) e2) A\<close> lenE lenST \<open>set E \<subseteq> types P\<close>
  have "\<turnstile> compE2 e1, compxE2 e1 0 (size ST) [::] ?\<tau>#?\<tau>s1@[?\<tau>1]"
    by(auto simp add: after_def)
  finally show ?case using wt1 wt2 wt by(simp add: after_def ac_simps shift_Cons_tuple hyperUn_assoc)
next
  case new thus ?case by(auto simp add:after_def wt_New)
next
  case (BinOp E A ST e\<^sub>1 bop e\<^sub>2) 
  have T: "P,E \<turnstile>1 e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T" by fact
  then obtain T\<^sub>1 T\<^sub>2 where T\<^sub>1: "P,E \<turnstile>1 e\<^sub>1 :: T\<^sub>1" and T\<^sub>2: "P,E \<turnstile>1 e\<^sub>2 :: T\<^sub>2" and 
    bopT: "P \<turnstile> T\<^sub>1\<guillemotleft>bop\<guillemotright>T\<^sub>2 :: T" by auto
  let ?A\<^sub>1 = "A \<squnion> \<A> e\<^sub>1" let ?A\<^sub>2 = "?A\<^sub>1 \<squnion> \<A> e\<^sub>2"
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s\<^sub>1 = "compT E A ST e\<^sub>1"
  let ?\<tau>\<^sub>1 = "ty\<^sub>i' (T\<^sub>1#ST) E ?A\<^sub>1" let ?\<tau>s\<^sub>2 = "compT E ?A\<^sub>1 (T\<^sub>1#ST) e\<^sub>2"
  let ?\<tau>\<^sub>2 = "ty\<^sub>i' (T\<^sub>2#T\<^sub>1#ST) E ?A\<^sub>2" let ?\<tau>' = "ty\<^sub>i' (T#ST) E ?A\<^sub>2"
  from bopT have "\<turnstile> [BinOpInstr bop],[] [::] [?\<tau>\<^sub>2,?\<tau>']" by(rule wt_BinOpInstr)
  also from BinOp.hyps(2)[of T\<^sub>2] BinOp.prems T\<^sub>2 T\<^sub>1
  have "\<turnstile> compE2 e\<^sub>2, compxE2 e\<^sub>2 0 (size (ty E e\<^sub>1#ST)) [::] ?\<tau>\<^sub>1#?\<tau>s\<^sub>2@[?\<tau>\<^sub>2]" by (auto simp: after_def)
  also from BinOp T\<^sub>1 have "\<turnstile> compE2 e\<^sub>1, compxE2 e\<^sub>1 0 (size ST) [::] ?\<tau>#?\<tau>s\<^sub>1@[?\<tau>\<^sub>1]" 
    by (auto simp: after_def)
  finally show ?case using T T\<^sub>1 T\<^sub>2 by (simp add: after_def hyperUn_assoc)
next
  case (Cons E A ST e es)
  have "P,E \<turnstile>1 e # es [::] Ts" by fact
  then obtain T\<^sub>e Ts' where 
    T\<^sub>e: "P,E \<turnstile>1 e :: T\<^sub>e" and Ts': "P,E \<turnstile>1 es [::] Ts'" and
    Ts: "Ts = T\<^sub>e#Ts'" by auto
  let ?A\<^sub>e = "A \<squnion> \<A> e"  
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s\<^sub>e = "compT E A ST e"  
  let ?\<tau>\<^sub>e = "ty\<^sub>i' (T\<^sub>e#ST) E ?A\<^sub>e" let ?\<tau>s' = "compTs E ?A\<^sub>e (T\<^sub>e#ST) es"
  let ?\<tau>s = "?\<tau> # ?\<tau>s\<^sub>e @ (?\<tau>\<^sub>e # ?\<tau>s')"
  from Cons.hyps(2) Cons.prems T\<^sub>e Ts'
  have "\<turnstile> compEs2 es, compxEs2 es 0 (size (T\<^sub>e#ST)) [::] ?\<tau>\<^sub>e#?\<tau>s'" by (simp add: after_def)
  also from Cons T\<^sub>e have "\<turnstile> compE2 e, compxE2 e 0 (size ST) [::] ?\<tau>#?\<tau>s\<^sub>e@[?\<tau>\<^sub>e]" by (auto simp: after_def)
  moreover
  from Cons.hyps(2)[OF Ts'] Cons.prems T\<^sub>e Ts' Ts
  have "last ?\<tau>s = ty\<^sub>i' (rev Ts@ST) E (?A\<^sub>e \<squnion> \<A>s es)" by simp
  ultimately show ?case using T\<^sub>e
    by(auto simp add: after_def hyperUn_assoc shift_compxEs2 stack_xlift_compxEs2 simp del: compxE2_size_convs compxEs2_size_convs compxEs2_stack_xlift_convs compxE2_stack_xlift_convs intro: wt_instrs_app2)
next
  case (FAss E A ST e\<^sub>1 F D e\<^sub>2)
  hence Void: "P,E \<turnstile>1 e\<^sub>1\<bullet>F{D} := e\<^sub>2 :: Void" by auto
  then obtain U C T T' fm where    
    C: "P,E \<turnstile>1 e\<^sub>1 :: U" and U: "class_type_of' U = \<lfloor>C\<rfloor>" and sees: "P \<turnstile> C sees F:T (fm) in D" and
    T': "P,E \<turnstile>1 e\<^sub>2 :: T'" and T'_T: "P \<turnstile> T' \<le> T" by auto
  let ?A\<^sub>1 = "A \<squnion> \<A> e\<^sub>1" let ?A\<^sub>2 = "?A\<^sub>1 \<squnion> \<A> e\<^sub>2"  
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s\<^sub>1 = "compT E A ST e\<^sub>1"
  let ?\<tau>\<^sub>1 = "ty\<^sub>i' (U#ST) E ?A\<^sub>1" let ?\<tau>s\<^sub>2 = "compT E ?A\<^sub>1 (U#ST) e\<^sub>2"
  let ?\<tau>\<^sub>2 = "ty\<^sub>i' (T'#U#ST) E ?A\<^sub>2" let ?\<tau>\<^sub>3 = "ty\<^sub>i' ST E ?A\<^sub>2"
  let ?\<tau>' = "ty\<^sub>i' (Void#ST) E ?A\<^sub>2"
  from FAss.prems sees T'_T U
  have "\<turnstile> [Putfield F D,Push Unit],[] [::] [?\<tau>\<^sub>2,?\<tau>\<^sub>3,?\<tau>']"
    by (fastforce simp add: wt_Push wt_Put)
  also from FAss.hyps(2)[of T'] FAss.prems T' C
  have "\<turnstile> compE2 e\<^sub>2, compxE2 e\<^sub>2 0 (size ST+1) [::] ?\<tau>\<^sub>1#?\<tau>s\<^sub>2@[?\<tau>\<^sub>2]"
    by (auto simp add: after_def hyperUn_assoc) 
  also from FAss C have "\<turnstile> compE2 e\<^sub>1, compxE2 e\<^sub>1 0 (size ST) [::] ?\<tau>#?\<tau>s\<^sub>1@[?\<tau>\<^sub>1]" 
    by (auto simp add: after_def)
  finally show ?case using Void C T' by (simp add: after_def hyperUn_assoc) 
next
  case Val thus ?case by(auto simp:after_def wt_Push)
next
  case (Cast T exp) thus ?case by (auto simp:after_def wt_Cast)
next
  case (InstanceOf E A ST e) thus ?case
    by(auto simp:after_def intro!: wt_Instanceof wt_instrs_app3 intro: widen_refT refT_widen)
next
  case (BlockNone E A ST i Ti e)
  from \<open>P,E \<turnstile>1 {i:Ti=None; e} :: T\<close> have wte: "P,E@[Ti] \<turnstile>1 e :: T"
    and Ti: "is_type P Ti" by auto
  let ?\<tau>s = "ty\<^sub>i' ST E A # compT (E @ [Ti]) (A\<ominus>i) ST e"
  from BlockNone wte Ti
  have "\<turnstile> compE2 e, compxE2 e 0 (size ST) [::] ?\<tau>s @ [ty\<^sub>i' (T#ST) (E@[Ti]) (A\<ominus>(size E) \<squnion> \<A> e)]"
    by(auto simp add: after_def)
  also have "P \<turnstile> ty\<^sub>i' (T # ST) (E@[Ti]) (A \<ominus> size E \<squnion> \<A> e) \<le>' ty\<^sub>i' (T # ST) (E@[Ti]) ((A \<squnion> \<A> e) \<ominus> size E)"
    by(auto simp add:hyperset_defs intro: ty\<^sub>i'_antimono)
  also have "\<dots> = ty\<^sub>i' (T # ST) E (A \<squnion> \<A> e)" by simp
  also have "P \<turnstile> \<dots> \<le>' ty\<^sub>i' (T # ST) E (A \<squnion> (\<A> e \<ominus> i))"
    by(auto simp add:hyperset_defs intro: ty\<^sub>i'_antimono)
  finally show ?case using BlockNone.prems by(simp add: after_def)
next
  case (BlockSome E A ST i Ti v e)
  from \<open>P,E \<turnstile>1 {i:Ti=\<lfloor>v\<rfloor>; e} :: T\<close> obtain Tv
    where Tv: "P,E \<turnstile>1 Val v :: Tv" "P \<turnstile> Tv \<le> Ti"
    and wte: "P,E@[Ti] \<turnstile>1 e :: T"
    and Ti: "is_type P Ti" by auto
  from \<open>length ST + max_stack {i:Ti=\<lfloor>v\<rfloor>; e} \<le> mxs\<close>
  have lenST: "length ST + max_stack e \<le> mxs" by simp
  from \<open>length E + max_vars {i:Ti=\<lfloor>v\<rfloor>; e} \<le> mxl\<close>
  have lenE: "length (E@[Ti]) + max_vars e \<le> mxl" by simp
  from \<open>\<B> {i:Ti=\<lfloor>v\<rfloor>; e} (length E)\<close> have [simp]: "i = length E"
    and B: "\<B> e (length (E@[Ti]))" by auto


  from BlockSome wte
  have "\<turnstile> compE2 e, compxE2 e 0 (size ST) [::] (ty\<^sub>i' ST (E @ [Ti]) (A \<squnion> \<lfloor>{length E}\<rfloor>) # compT (E @ [Ti]) (A \<squnion> \<lfloor>{i}\<rfloor>) ST e) @ [ty\<^sub>i' (T#ST) (E@[Ti]) (A \<squnion> \<lfloor>{size E}\<rfloor> \<squnion> \<A> e)]"
    by(auto simp add: after_def)
  also have "P \<turnstile> ty\<^sub>i' (T # ST) (E @ [Ti]) (A \<squnion> \<lfloor>{length E}\<rfloor> \<squnion> \<A> e) \<le>' ty\<^sub>i' (T # ST) (E @ [Ti]) ((A \<squnion> \<A> e) \<ominus> length E)"
    by(auto simp add: hyperset_defs intro: ty\<^sub>i'_antimono)
  also have "\<dots> = ty\<^sub>i' (T # ST) E (A \<squnion> \<A> e)" by simp
  also have "P \<turnstile> \<dots> \<le>' ty\<^sub>i' (T # ST) E (A \<squnion> (\<A> e \<ominus> i))"
    by(auto simp add:hyperset_defs intro: ty\<^sub>i'_antimono)
  also note append_Cons
  also {
    from lenST max_stack1[of e] Tv
    have "\<turnstile> [Push v], [] [::] [ty\<^sub>i' ST E A, ty\<^sub>i' (ty E (Val v) # ST) E A]"
      by(auto intro: wt_Push)
    moreover from Tv lenE
    have "\<turnstile> [Store (length E)], [] [::] [ty\<^sub>i' (Tv # ST) (E @ [Ti]) (A \<ominus> length E), ty\<^sub>i' ST (E @ [Ti]) (\<lfloor>{length E}\<rfloor> \<squnion> (A \<ominus> length E))]"
      by -(rule wt_Store, auto)
    moreover have "ty\<^sub>i' (Tv # ST) (E @ [Ti]) (A \<ominus> length E) = ty\<^sub>i' (Tv # ST) E A" by(simp add: ty\<^sub>i'_def)
    moreover have "\<lfloor>{length E}\<rfloor> \<squnion> (A \<ominus> length E) = A \<squnion> \<lfloor>{length E}\<rfloor>" by(simp add: hyperset_defs)
    ultimately have "\<turnstile> [Push v, Store (length E)], [] [::] [ty\<^sub>i' ST E A, ty\<^sub>i' (Tv # ST) E A, ty\<^sub>i' ST (E @ [Ti]) (A \<squnion> \<lfloor>{length E}\<rfloor>)]"
      using Tv by(auto intro: wt_instrs_Cons3)
  }
  finally show ?case using Tv \<open>P,E \<turnstile>1 {i:Ti=\<lfloor>v\<rfloor>; e} :: T\<close> wte by(simp add: after_def)
next
  case Var thus ?case by(auto simp:after_def wt_Load)
next
  case FAcc thus ?case by(auto simp:after_def wt_Get)
next
  case (LAss E A ST i e) thus ?case using max_stack1[of e]
    by(auto simp: hyper_insert_comm after_def wt_Store wt_Push simp del: hyperUn_comm hyperUn_leftComm)
next
  case Nil thus ?case by auto
next
  case throw thus ?case by(auto simp add: after_def wt_Throw)
next
  case (While E A ST e c)
  obtain Tc where wte: "P,E \<turnstile>1 e :: Boolean" and wtc: "P,E \<turnstile>1 c :: Tc"
    and [simp]: "T = Void" using While by auto
  have [simp]: "ty E (while (e) c) = Void" using While by simp
  let ?A\<^sub>0 = "A \<squnion> \<A> e" let ?A\<^sub>1 = "?A\<^sub>0 \<squnion> \<A> c"
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s\<^sub>e = "compT E A ST e"
  let ?\<tau>\<^sub>e = "ty\<^sub>i' (Boolean#ST) E ?A\<^sub>0" let ?\<tau>\<^sub>1 = "ty\<^sub>i' ST E ?A\<^sub>0"
  let ?\<tau>s\<^sub>c = "compT E ?A\<^sub>0 ST c" let ?\<tau>\<^sub>c = "ty\<^sub>i' (Tc#ST) E ?A\<^sub>1"
  let ?\<tau>\<^sub>2 = "ty\<^sub>i' ST E ?A\<^sub>1" let ?\<tau>' = "ty\<^sub>i' (Void#ST) E ?A\<^sub>0"
  let ?\<tau>s = "(?\<tau> # ?\<tau>s\<^sub>e @ [?\<tau>\<^sub>e]) @ ?\<tau>\<^sub>1 # ?\<tau>s\<^sub>c @ [?\<tau>\<^sub>c, ?\<tau>\<^sub>2, ?\<tau>\<^sub>1, ?\<tau>']"
  have "\<turnstile> [],[] [::] [] @ ?\<tau>s" by(simp add:wt_instrs_def)
  also
  from While.hyps(1)[of Boolean] While.prems
  have "\<turnstile> compE2 e,compxE2 e 0 (size ST) [::] ?\<tau> # ?\<tau>s\<^sub>e @ [?\<tau>\<^sub>e]"
    by (auto simp:after_def)
  also
  have "[] @ ?\<tau>s = (?\<tau> # ?\<tau>s\<^sub>e) @ ?\<tau>\<^sub>e # ?\<tau>\<^sub>1 # ?\<tau>s\<^sub>c @ [?\<tau>\<^sub>c,?\<tau>\<^sub>2,?\<tau>\<^sub>1,?\<tau>']" by simp
  also
  let ?n\<^sub>e = "size(compE2 e)"  let ?n\<^sub>c = "size(compE2 c)"
  let ?if = "IfFalse (int ?n\<^sub>c + 3)"
  have "\<turnstile> [?if],[] [::] ?\<tau>\<^sub>e # ?\<tau>\<^sub>1 # ?\<tau>s\<^sub>c @ [?\<tau>\<^sub>c, ?\<tau>\<^sub>2, ?\<tau>\<^sub>1, ?\<tau>']"
    by(simp add: wt_instr_Cons wt_instr_append wt_IfFalse
                 nat_add_distrib split: nat_diff_split)
  also
  have "(?\<tau> # ?\<tau>s\<^sub>e) @ (?\<tau>\<^sub>e # ?\<tau>\<^sub>1 # ?\<tau>s\<^sub>c @ [?\<tau>\<^sub>c, ?\<tau>\<^sub>2, ?\<tau>\<^sub>1, ?\<tau>']) = ?\<tau>s" by simp
  also from While.hyps(2)[of Tc] While.prems wtc
  have "\<turnstile> compE2 c,compxE2 c 0 (size ST) [::] ?\<tau>\<^sub>1 # ?\<tau>s\<^sub>c @ [?\<tau>\<^sub>c]"
    by (auto simp:after_def)
  also have "?\<tau>s = (?\<tau> # ?\<tau>s\<^sub>e @ [?\<tau>\<^sub>e,?\<tau>\<^sub>1] @ ?\<tau>s\<^sub>c) @ [?\<tau>\<^sub>c,?\<tau>\<^sub>2,?\<tau>\<^sub>1,?\<tau>']" by simp
  also have "\<turnstile> [Pop],[] [::] [?\<tau>\<^sub>c, ?\<tau>\<^sub>2]"  by(simp add:wt_Pop)
  also have "(?\<tau> # ?\<tau>s\<^sub>e @ [?\<tau>\<^sub>e,?\<tau>\<^sub>1] @ ?\<tau>s\<^sub>c) @ [?\<tau>\<^sub>c,?\<tau>\<^sub>2,?\<tau>\<^sub>1,?\<tau>'] = ?\<tau>s" by simp
  also let ?go = "Goto (-int(?n\<^sub>c+?n\<^sub>e+2))"
  have "P \<turnstile> ?\<tau>\<^sub>2 \<le>' ?\<tau>" by(fastforce intro: ty\<^sub>i'_antimono simp: hyperset_defs)
  hence "P,T\<^sub>r,mxs,size ?\<tau>s,[] \<turnstile> ?go,?n\<^sub>e+?n\<^sub>c+2 :: ?\<tau>s"
    by(simp add: wt_Goto split: nat_diff_split)
  also have "?\<tau>s = (?\<tau> # ?\<tau>s\<^sub>e @ [?\<tau>\<^sub>e,?\<tau>\<^sub>1] @ ?\<tau>s\<^sub>c @ [?\<tau>\<^sub>c, ?\<tau>\<^sub>2]) @ [?\<tau>\<^sub>1, ?\<tau>']"
    by simp
  also have "\<turnstile> [Push Unit],[] [::] [?\<tau>\<^sub>1,?\<tau>']"
    using While.prems max_stack1[of c] by(auto simp add:wt_Push)
  finally show ?case using wtc wte
    by (simp add:after_def)
next
  case (Cond E A ST e e\<^sub>1 e\<^sub>2)
  obtain T\<^sub>1 T\<^sub>2 where wte: "P,E \<turnstile>1 e :: Boolean"
    and wt\<^sub>1: "P,E \<turnstile>1 e\<^sub>1 :: T\<^sub>1" and wt\<^sub>2: "P,E \<turnstile>1 e\<^sub>2 :: T\<^sub>2"
    and sub\<^sub>1: "P \<turnstile> T\<^sub>1 \<le> T" and sub\<^sub>2: "P \<turnstile> T\<^sub>2 \<le> T"
    using Cond by(auto dest: is_lub_upper)
  have [simp]: "ty E (if (e) e\<^sub>1 else e\<^sub>2) = T" using Cond by simp
  let ?A\<^sub>0 = "A \<squnion> \<A> e" let ?A\<^sub>2 = "?A\<^sub>0 \<squnion> \<A> e\<^sub>2" let ?A\<^sub>1 = "?A\<^sub>0 \<squnion> \<A> e\<^sub>1"
  let ?A' = "?A\<^sub>0 \<squnion> \<A> e\<^sub>1 \<sqinter> \<A> e\<^sub>2"
  let ?\<tau>\<^sub>2 = "ty\<^sub>i' ST E ?A\<^sub>0" let ?\<tau>' = "ty\<^sub>i' (T#ST) E ?A'"
  let ?\<tau>s\<^sub>2 = "compT E ?A\<^sub>0 ST e\<^sub>2"
  have "PROP ?P e\<^sub>2 E T\<^sub>2 ?A\<^sub>0 ST" by fact
  hence "\<turnstile> compE2 e\<^sub>2, compxE2 e\<^sub>2 0 (size ST) [::] (?\<tau>\<^sub>2#?\<tau>s\<^sub>2) @ [ty\<^sub>i' (T\<^sub>2#ST) E ?A\<^sub>2]"
    using Cond.prems wt\<^sub>2 by(auto simp add:after_def)
  also have "P \<turnstile> ty\<^sub>i' (T\<^sub>2#ST) E ?A\<^sub>2 \<le>' ?\<tau>'" using sub\<^sub>2
    by(auto simp add: hyperset_defs ty\<^sub>i'_def intro!: ty\<^sub>l_antimono)
  also
  let ?\<tau>\<^sub>3 = "ty\<^sub>i' (T\<^sub>1 # ST) E ?A\<^sub>1"
  let ?g\<^sub>2 = "Goto(int (size (compE2 e\<^sub>2) + 1))"
  from sub\<^sub>1 have "P,T\<^sub>r,mxs,size(compE2 e\<^sub>2)+2,[] \<turnstile> ?g\<^sub>2,0 :: ?\<tau>\<^sub>3#(?\<tau>\<^sub>2#?\<tau>s\<^sub>2)@[?\<tau>']"
    by(cases "length (compE2 e\<^sub>2)")
      (auto simp: hyperset_defs wt_defs nth_Cons ty\<^sub>i'_def neq_Nil_conv
             split:nat.split intro!: ty\<^sub>l_antimono)
  also let ?\<tau>s\<^sub>1 = "compT E ?A\<^sub>0 ST e\<^sub>1"
  have "PROP ?P e\<^sub>1 E T\<^sub>1 ?A\<^sub>0 ST" by fact
  hence "\<turnstile> compE2 e\<^sub>1,compxE2 e\<^sub>1 0 (size ST) [::] ?\<tau>\<^sub>2 # ?\<tau>s\<^sub>1 @ [?\<tau>\<^sub>3]"
    using Cond.prems wt\<^sub>1 by(auto simp add:after_def)
  also
  let ?\<tau>s\<^sub>1\<^sub>2 = "?\<tau>\<^sub>2 # ?\<tau>s\<^sub>1 @ ?\<tau>\<^sub>3 # (?\<tau>\<^sub>2 # ?\<tau>s\<^sub>2) @ [?\<tau>']"
  let ?\<tau>\<^sub>1 = "ty\<^sub>i' (Boolean#ST) E ?A\<^sub>0"
  let ?g\<^sub>1 = "IfFalse(int (size (compE2 e\<^sub>1) + 2))"
  let ?code = "compE2 e\<^sub>1 @ ?g\<^sub>2 # compE2 e\<^sub>2"
  have "\<turnstile> [?g\<^sub>1],[] [::] [?\<tau>\<^sub>1] @ ?\<tau>s\<^sub>1\<^sub>2"
    by(simp add: wt_IfFalse nat_add_distrib split:nat_diff_split)
  also (wt_instrs_ext2) have "[?\<tau>\<^sub>1] @ ?\<tau>s\<^sub>1\<^sub>2 = ?\<tau>\<^sub>1 # ?\<tau>s\<^sub>1\<^sub>2" by simp also
  let ?\<tau> = "ty\<^sub>i' ST E A"
  have "PROP ?P e E Boolean A ST" by fact
  hence "\<turnstile> compE2 e, compxE2 e 0 (size ST) [::] ?\<tau> # compT E A ST e @ [?\<tau>\<^sub>1]"
    using Cond.prems wte by(auto simp add:after_def)
  finally show ?case using wte wt\<^sub>1 wt\<^sub>2 by(simp add:after_def hyperUn_assoc)
next
  case (Call E A ST e M es)
  from \<open>P,E \<turnstile>1 e\<bullet>M(es) :: T\<close>
  obtain U C D Ts m Ts'
    where C: "P,E \<turnstile>1 e :: U"
    and icto: "class_type_of' U = \<lfloor>C\<rfloor>"
    and "method": "P \<turnstile> C sees M:Ts \<rightarrow> T = m in D"
    and wtes: "P,E \<turnstile>1 es [::] Ts'" and subs: "P \<turnstile> Ts' [\<le>] Ts"
    by(cases) auto
  from wtes have same_size: "size es = size Ts'" by(rule WTs1_same_size)
  let ?A\<^sub>0 = "A \<squnion> \<A> e" let ?A\<^sub>1 = "?A\<^sub>0 \<squnion> \<A>s es"
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s\<^sub>e = "compT E A ST e"
  let ?\<tau>\<^sub>e = "ty\<^sub>i' (U # ST) E ?A\<^sub>0"
  let ?\<tau>s\<^sub>e\<^sub>s = "compTs E ?A\<^sub>0 (U # ST) es"
  let ?\<tau>\<^sub>1 = "ty\<^sub>i' (rev Ts' @ U # ST) E ?A\<^sub>1"
  let ?\<tau>' = "ty\<^sub>i' (T # ST) E ?A\<^sub>1"
  have "\<turnstile> [Invoke M (size es)],[] [::] [?\<tau>\<^sub>1,?\<tau>']"
    by(rule wt_Invoke[OF same_size icto "method" subs])
  also
  from Call.hyps(2)[of Ts'] Call.prems wtes C
  have "\<turnstile> compEs2 es,compxEs2 es 0 (size ST+1) [::] ?\<tau>\<^sub>e # ?\<tau>s\<^sub>e\<^sub>s"
    "last (?\<tau>\<^sub>e # ?\<tau>s\<^sub>e\<^sub>s) = ?\<tau>\<^sub>1"
    by(auto simp add:after_def)
  also have "(?\<tau>\<^sub>e # ?\<tau>s\<^sub>e\<^sub>s) @ [?\<tau>'] = ?\<tau>\<^sub>e # ?\<tau>s\<^sub>e\<^sub>s @ [?\<tau>']" by simp
  also have "\<turnstile> compE2 e,compxE2 e 0 (size ST) [::] ?\<tau> # ?\<tau>s\<^sub>e @ [?\<tau>\<^sub>e]"
    using Call C by(auto simp add:after_def)
  finally show ?case using Call.prems C
    by(simp add:after_def hyperUn_assoc shift_compxEs2 stack_xlift_compxEs2 del: compxEs2_stack_xlift_convs compxEs2_size_convs)
next
  case Seq thus ?case
    by(auto simp:after_def)
      (fastforce simp:wt_Push wt_Pop hyperUn_assoc
                intro:wt_instrs_app2 wt_instrs_Cons)
next
  case (NewArray E A ST Ta e)
  from \<open>P,E \<turnstile>1 newA Ta\<lfloor>e\<rceil> :: T\<close>
  have "\<turnstile> [NewArray Ta], [] [::] [ty\<^sub>i' (Integer # ST) E (A \<squnion> \<A> e), ty\<^sub>i' (Ta\<lfloor>\<rceil> # ST) E (A \<squnion> \<A> e)]"
    by(auto simp:hyperset_defs ty\<^sub>i'_def wt_defs ty\<^sub>l_def)
  with NewArray show ?case by(auto simp: after_def intro: wt_instrs_app3)
next
  case (ALen E A ST exp)
  { fix T
    have "\<turnstile> [ALength], [] [::] [ty\<^sub>i' (T\<lfloor>\<rceil> # ST) E (A \<squnion> \<A> exp), ty\<^sub>i' (Integer # ST) E (A \<squnion> \<A> exp)]"
      by(auto simp:hyperset_defs ty\<^sub>i'_def wt_defs ty\<^sub>l_def) }
  with ALen show ?case by(auto simp add: after_def)(rule wt_instrs_app2, auto)
next
  case (AAcc E A ST a i)
  from \<open>P,E \<turnstile>1 a\<lfloor>i\<rceil> :: T\<close> have wta: "P,E \<turnstile>1 a :: T\<lfloor>\<rceil>" and wti: "P,E \<turnstile>1 i :: Integer" by auto
  let ?A1 = "A \<squnion> \<A> a" let ?A2 = "?A1 \<squnion> \<A> i"  
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>sa = "compT E A ST a"
  let ?\<tau>1 = "ty\<^sub>i' (T\<lfloor>\<rceil>#ST) E ?A1" let ?\<tau>si = "compT E ?A1 (T\<lfloor>\<rceil>#ST) i"
  let ?\<tau>2 = "ty\<^sub>i' (Integer#T\<lfloor>\<rceil>#ST) E ?A2" let ?\<tau>' = "ty\<^sub>i' (T#ST) E ?A2"
  have "\<turnstile> [ALoad], [] [::] [?\<tau>2,?\<tau>']" by(auto simp add: ty\<^sub>i'_def wt_defs)
  also from AAcc.hyps(2)[of Integer] AAcc.prems wti wta
  have "\<turnstile> compE2 i, compxE2 i 0 (size ST+1) [::] ?\<tau>1#?\<tau>si@[?\<tau>2]"
    by(auto simp add: after_def)
  also from wta AAcc have "\<turnstile> compE2 a, compxE2 a 0 (size ST) [::] ?\<tau>#?\<tau>sa@[?\<tau>1]" 
    by(auto simp add: after_def)
  finally show ?case using wta wti \<open>P,E \<turnstile>1 a\<lfloor>i\<rceil> :: T\<close> by(simp add: after_def hyperUn_assoc)
next
  case (AAss E A ST a i e)
  note wt = \<open>P,E \<turnstile>1 a\<lfloor>i\<rceil> := e :: T\<close>
  then obtain Ta U where wta: "P,E \<turnstile>1 a :: Ta\<lfloor>\<rceil>" and wti: "P,E \<turnstile>1 i :: Integer"
    and wte: "P,E \<turnstile>1 e :: U" and U: "P \<turnstile> U \<le> Ta" and [simp]: "T = Void" by auto
  let ?A1 = "A \<squnion> \<A> a" let ?A2 = "?A1 \<squnion> \<A> i" let ?A3 = "?A2 \<squnion> \<A> e"
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>sa = "compT E A ST a"
  let ?\<tau>1 = "ty\<^sub>i' (Ta\<lfloor>\<rceil>#ST) E ?A1" let ?\<tau>si = "compT E ?A1 (Ta\<lfloor>\<rceil>#ST) i"
  let ?\<tau>2 = "ty\<^sub>i' (Integer#Ta\<lfloor>\<rceil>#ST) E ?A2" let ?\<tau>se = "compT E ?A2 (Integer#Ta\<lfloor>\<rceil>#ST) e"
  let ?\<tau>3 = "ty\<^sub>i' (U#Integer#Ta\<lfloor>\<rceil>#ST) E ?A3" let ?\<tau>4 = "ty\<^sub>i' ST E ?A3"
  let ?\<tau>' = "ty\<^sub>i' (Void#ST) E ?A3"
  from \<open>length ST + max_stack (a\<lfloor>i\<rceil> := e) \<le> mxs\<close>
  have "\<turnstile> [AStore, Push Unit], [] [::] [?\<tau>3,?\<tau>4,?\<tau>']"
    by(auto simp add: ty\<^sub>i'_def wt_defs nth_Cons split: nat.split)
  also from AAss.hyps(3)[of U] wte AAss.prems wta wti
  have "\<turnstile> compE2 e, compxE2 e 0 (size ST+2) [::] ?\<tau>2#?\<tau>se@[?\<tau>3]"
    by(auto simp add: after_def)
  also from AAss.hyps(2)[of Integer] wti wta AAss.prems
  have "\<turnstile> compE2 i, compxE2 i 0 (size ST+1) [::] ?\<tau>1#?\<tau>si@[?\<tau>2]"
    by(auto simp add: after_def)
  also from wta AAss have "\<turnstile> compE2 a, compxE2 a 0 (size ST) [::] ?\<tau>#?\<tau>sa@[?\<tau>1]" 
    by(auto simp add: after_def)
  finally show ?case using wta wti wte \<open>P,E \<turnstile>1 a\<lfloor>i\<rceil> := e :: T\<close>
    by(simp add: after_def hyperUn_assoc)
next
  case (CompareAndSwap E A ST e1 D F e2 e3)
  note wt = \<open>P,E \<turnstile>1 e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3) :: T\<close>
  then obtain T1 T2 T3 C fm T' where [simp]: "T = Boolean"
    and wt1: "P,E \<turnstile>1 e1 :: T1" "class_type_of' T1 = \<lfloor>C\<rfloor>" "P \<turnstile> C sees F:T' (fm) in D" "volatile fm"
    and wt2: "P,E \<turnstile>1 e2 :: T2" "P \<turnstile> T2 \<le> T'" and wt3: "P,E \<turnstile>1 e3 :: T3" "P \<turnstile> T3 \<le> T'"
    by auto
  let ?A1 = "A \<squnion> \<A> e1" let ?A2 = "?A1 \<squnion> \<A> e2" let ?A3 = "?A2 \<squnion> \<A> e3"
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s1 = "compT E A ST e1"
  let ?\<tau>1 = "ty\<^sub>i' (T1#ST) E ?A1" let ?\<tau>s2 = "compT E ?A1 (T1#ST) e2"
  let ?\<tau>2 = "ty\<^sub>i' (T2#T1#ST) E ?A2" let ?\<tau>s3 = "compT E ?A2 (T2#T1#ST) e3"
  let ?\<tau>3 = "ty\<^sub>i' (T3#T2#T1#ST) E ?A3"
  let ?\<tau>' = "ty\<^sub>i' (Boolean#ST) E ?A3"
  from \<open>length ST + max_stack (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) \<le> mxs\<close>
  have "\<turnstile> [CAS F D], [] [::] [?\<tau>3,?\<tau>']" using wt1 wt2 wt3
    by(cases T1)(auto simp add: ty\<^sub>i'_def wt_defs nth_Cons split: nat.split intro: sees_field_idemp widen_trans[OF widen_array_object] dest: sees_field_decl_above)
  also from CompareAndSwap.hyps(3)[of T3] wt3 CompareAndSwap.prems wt1 wt2
  have "\<turnstile> compE2 e3, compxE2 e3 0 (size ST+2) [::] ?\<tau>2#?\<tau>s3@[?\<tau>3]"
    by(auto simp add: after_def)
  also from CompareAndSwap.hyps(2)[of T2] wt2 wt1 CompareAndSwap.prems
  have "\<turnstile> compE2 e2, compxE2 e2 0 (size ST+1) [::] ?\<tau>1#?\<tau>s2@[?\<tau>2]"
    by(auto simp add: after_def)
  also from wt1 CompareAndSwap have "\<turnstile> compE2 e1, compxE2 e1 0 (size ST) [::] ?\<tau>#?\<tau>s1@[?\<tau>1]" 
    by(auto simp add: after_def)
  also have "ty E (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) = T" using wt by(rule ty_def2)
  ultimately show ?case using wt1 wt2 wt3
    by(simp add: after_def hyperUn_assoc)
next
  case (InSynchronized i a exp) thus ?case by auto
qed

end

lemma states_compP [simp]: "states (compP f P) mxs mxl = states P mxs mxl"
by (simp add: JVM_states_unfold)

lemma [simp]: "app\<^sub>i (i, compP f P, pc, mpc, T, \<tau>) = app\<^sub>i (i, P, pc, mpc, T, \<tau>)"
proof -
  { fix ST LT
    have "app\<^sub>i (i, compP f P, pc, mpc, T, (ST, LT)) = app\<^sub>i (i, P, pc, mpc, T, (ST, LT))"
    proof(cases i)
      case (Invoke M n)
      have "\<And>C Ts D. (\<exists>T m. compP f P \<turnstile> C sees M: Ts\<rightarrow>T = m in D) \<longleftrightarrow> (\<exists>T m. P \<turnstile> C sees M: Ts\<rightarrow>T = m in D)"
        by(auto dest!: sees_method_compPD dest: sees_method_compP)
      with Invoke show ?thesis by clarsimp
    qed(simp_all) }
  thus ?thesis by(cases \<tau>) simp
qed

  
lemma [simp]: "is_relevant_entry (compP f P) i = is_relevant_entry P i"
  apply (rule ext)+
  apply (unfold is_relevant_entry_def)
  apply (cases i)
  apply auto
  done

lemma [simp]: "relevant_entries (compP f P) i pc xt = relevant_entries P i pc xt"
by (simp add: relevant_entries_def)

lemma [simp]: "app i (compP f P) mpc T pc mxl xt \<tau> = app i P mpc T pc mxl xt \<tau>"
  apply (simp add: app_def xcpt_app_def eff_def xcpt_eff_def norm_eff_def)
  apply (fastforce simp add: image_def)
  done

lemma [simp]: "app i P mpc T pc mxl xt \<tau> \<Longrightarrow> eff i (compP f P) pc xt \<tau> = eff i P pc xt \<tau>"
  apply (clarsimp simp add: eff_def norm_eff_def xcpt_eff_def app_def)
  apply (cases i)
  apply(auto)
  done

lemma [simp]: "widen (compP f P) = widen P"
  apply (rule ext)+
  apply (simp)
  done
  
lemma [simp]: "compP f P \<turnstile> \<tau> \<le>' \<tau>' = P \<turnstile> \<tau> \<le>' \<tau>'"
by (simp add: sup_state_opt_def sup_state_def sup_ty_opt_def)(*>*)

lemma [simp]: "compP f P,T,mpc,mxl,xt \<turnstile> i,pc :: \<tau>s = P,T,mpc,mxl,xt \<turnstile> i,pc :: \<tau>s"
by (simp add: wt_instr_def cong: conj_cong)

declare TC0.compT_sizes[simp]  TC1.ty_def2[OF TC1.intro, simp]

lemma compT_method:
  fixes e and A and C and Ts and mxl\<^sub>0
  defines [simp]: "E \<equiv> Class C # Ts"
      and [simp]: "A \<equiv> \<lfloor>{..size Ts}\<rfloor>"
      and [simp]: "A' \<equiv> A \<squnion> \<A> e"
      and [simp]: "mxs \<equiv> max_stack e"
      and [simp]: "mxl\<^sub>0 \<equiv> max_vars e"
      and [simp]: "mxl \<equiv> 1 + size Ts + mxl\<^sub>0"
  assumes wf_prog: "wf_prog p P"
  shows "\<lbrakk> P,E \<turnstile>1 e :: T; \<D> e A; \<B> e (size E); set E \<subseteq> types P; P \<turnstile> T \<le> T' \<rbrakk> \<Longrightarrow>
   wt_method (compP2 P) C Ts T' mxs mxl\<^sub>0 (compE2 e @ [Return]) (compxE2 e 0 0)
      (TC0.ty\<^sub>i' mxl [] E A # TC0.compTa P mxl E A [] e)"
using wf_prog
apply(simp add:wt_method_def TC0.compTa_def TC0.after_def compP2_def compMb2_def)
apply(rule conjI)
 apply(simp add:check_types_def TC0.OK_ty\<^sub>i'_in_statesI)
 apply(rule conjI)
  apply(frule WT1_is_type[OF wf_prog])
   apply simp
  apply(insert max_stack1[of e])
  apply(fastforce intro!: TC0.OK_ty\<^sub>i'_in_statesI)
 apply(erule (1) TC1.compT_states[OF TC1.intro])
    apply simp
   apply simp
  apply simp
 apply simp
apply(rule conjI)
 apply(fastforce simp add:wt_start_def TC0.ty\<^sub>i'_def TC0.ty\<^sub>l_def list_all2_conv_all_nth nth_Cons split:nat.split dest:less_antisym)
apply (frule (1) TC3.compT_wt_instrs[OF TC3.intro[OF TC1.intro], where ST = "[]" and mxs = "max_stack e" and mxl = "1 + size Ts + max_vars e"])
     apply simp
    apply simp
   apply simp
  apply simp
 apply simp
apply (clarsimp simp:TC2.wt_instrs_def TC0.after_def)
apply(rule conjI)
 apply (fastforce)
apply(clarsimp)
apply(drule (1) less_antisym)
apply(thin_tac "\<forall>x. P x" for P)
apply(clarsimp simp:TC2.wt_defs xcpt_app_pcs xcpt_eff_pcs TC0.ty\<^sub>i'_def)
done
(*>*)


definition compTP :: "'addr J1_prog \<Rightarrow> ty\<^sub>P"
where
  "compTP P C M  \<equiv>
  let (D,Ts,T,meth) = method P C M;
       e = the meth;
       E = Class C # Ts;
       A = \<lfloor>{..size Ts}\<rfloor>;
       mxl = 1 + size Ts + max_vars e
  in  (TC0.ty\<^sub>i' mxl [] E A # TC0.compTa P mxl E A [] e)"

theorem wt_compTP_compP2:
  "wf_J1_prog P \<Longrightarrow> wf_jvm_prog\<^bsub>compTP P\<^esub> (compP2 P)"
  apply (simp add: wf_jvm_prog_phi_def compP2_def compMb2_def)
  apply (rule wf_prog_compPI)
   prefer 2 apply assumption
  apply (clarsimp simp add: wf_mdecl_def)
  apply (simp add: compTP_def)
  apply (rule compT_method [simplified compP2_def compMb2_def, simplified])
       apply assumption+
    apply (drule (1) sees_wf_mdecl)
    apply (simp add: wf_mdecl_def)
   apply (fastforce intro: sees_method_is_class)
  apply assumption
  done


theorem wt_compP2:
  "wf_J1_prog P \<Longrightarrow> wf_jvm_prog (compP2 P)"
by(auto simp add: wf_jvm_prog_def intro: wt_compTP_compP2)

end
