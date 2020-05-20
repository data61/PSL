(*  Title:      JinjaThreads/Compiler/JJ1WellForm.thy
    Author:     Andreas Lochbihler

    Reminiscent of the Jinja theory Compiler/Correctness1
*)

section \<open>Preservation of well-formedness from source code to intermediate language\<close>

theory JJ1WellForm imports
  "../J/JWellForm"
  J1WellForm
  Compiler1
begin

text\<open>The compiler preserves well-formedness. Is less trivial than it
may appear. We start with two simple properties: preservation of
well-typedness\<close>

lemma assumes wf: "wf_prog wfmd P"
  shows compE1_pres_wt: "\<lbrakk> P,[Vs[\<mapsto>]Ts] \<turnstile> e :: U; size Ts = size Vs \<rbrakk> \<Longrightarrow> compP f P,Ts \<turnstile>1 compE1 Vs e :: U"
  and compEs1_pres_wt: "\<lbrakk> P,[Vs[\<mapsto>]Ts] \<turnstile> es [::] Us; size Ts = size Vs \<rbrakk> \<Longrightarrow> compP f P,Ts \<turnstile>1 compEs1 Vs es [::] Us"
proof(induct Vs e and Vs es arbitrary: Ts U and Ts Us rule: compE1_compEs1_induct)
  case Var thus ?case by(fastforce simp:map_upds_apply_eq_Some split:if_split_asm)
next
  case LAss thus ?case by(fastforce simp:map_upds_apply_eq_Some split:if_split_asm)
next
  case Call thus ?case
    by(fastforce dest: sees_method_compP[where f = f])
next
  case Block thus ?case by(fastforce simp:nth_append)
next
  case (Synchronized Vs V exp1 exp2 Ts U)
  note IH1 = \<open>\<And>Ts U. \<lbrakk>P,[Vs [\<mapsto>] Ts] \<turnstile> exp1 :: U;
    length Ts = length Vs\<rbrakk> \<Longrightarrow> compP f P,Ts \<turnstile>1 compE1 Vs exp1 :: U\<close>
  note IH2 = \<open>\<And>Ts U. \<lbrakk>P,[(Vs @ [fresh_var Vs]) [\<mapsto>] Ts] \<turnstile> exp2 :: U; length Ts = length (Vs @ [fresh_var Vs])\<rbrakk>
      \<Longrightarrow> compP f P,Ts \<turnstile>1 compE1 (Vs @ [fresh_var Vs]) exp2 :: U\<close>
  note length = \<open>length Ts = length Vs\<close>
  from \<open>P,[Vs [\<mapsto>] Ts] \<turnstile> sync\<^bsub>V\<^esub> (exp1) exp2 :: U\<close>
  obtain U1 where wt1: "P,[Vs [\<mapsto>] Ts] \<turnstile> exp1 :: U1"
    and wt2: "P,[Vs [\<mapsto>] Ts] \<turnstile> exp2 :: U"
    and U1: "is_refT U1" "U1 \<noteq> NT"
    by(auto)
  from IH1[of Ts U1] wt1 length
  have wt1': "compP f P,Ts \<turnstile>1 compE1 Vs exp1 :: U1" by simp
  from length fresh_var_fresh[of Vs] have "[Vs [\<mapsto>] Ts] \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] Ts @ [Class Object]]"
    by(auto simp add: map_le_def fun_upd_def)
  with wt2 have "P,[Vs@[fresh_var Vs] [\<mapsto>] Ts @ [Class Object]] \<turnstile> exp2 :: U"
    by(rule wt_env_mono)
  with length IH2[of "Ts @ [Class Object]" U]
  have "compP f P,Ts @ [Class Object] \<turnstile>1 compE1 (Vs @ [fresh_var Vs]) exp2 :: U" by simp
  with wt1' U1 show ?case by(auto)
next 
  case (TryCatch Vs exp1 C V exp2)
  note IH1 = \<open>\<And>Ts U. \<lbrakk>P,[Vs [\<mapsto>] Ts] \<turnstile> exp1 :: U; length Ts = length Vs\<rbrakk> \<Longrightarrow> compP f P,Ts \<turnstile>1 compE1 Vs exp1 :: U\<close>
  note IH2 = \<open>\<And>Ts U. \<lbrakk>P,[(Vs @ [V]) [\<mapsto>] Ts] \<turnstile> exp2 :: U; length Ts = length (Vs @ [V])\<rbrakk> \<Longrightarrow> compP f P,Ts \<turnstile>1 compE1 (Vs @ [V]) exp2 :: U\<close>
  note length = \<open>length Ts = length Vs\<close>
  with \<open>P,[Vs [\<mapsto>] Ts] \<turnstile> try exp1 catch(C V) exp2 :: U\<close>
  have wt1: "P,[Vs [\<mapsto>] Ts] \<turnstile> exp1 :: U" and wt2: "P,[(Vs@[V]) [\<mapsto>] (Ts@[Class C])] \<turnstile> exp2 :: U"
    and C: "P \<turnstile> C \<preceq>\<^sup>* Throwable" by(auto simp add: nth_append)
  from wf C have "is_class P C" by(rule is_class_sub_Throwable)
  with IH1[OF wt1 length] IH2[OF wt2] length show ?case by(auto)
qed(fastforce)+


text\<open>\noindent and the correct block numbering:\<close>

text\<open>The main complication is preservation of definite assignment
@{term"\<D>"}.\<close>

lemma fixes e :: "'addr expr" and es :: "'addr expr list"
  shows A_compE1_None[simp]: "\<A> e = None \<Longrightarrow> \<A> (compE1 Vs e) = None"
  and As_compEs1_None: "\<A>s es = None \<Longrightarrow> \<A>s (compEs1 Vs es) = None"
apply(induct Vs e and Vs es rule: compE1_compEs1_induct)
apply(auto simp:hyperset_defs)
done

lemma fixes e :: "'addr expr" and es :: "'addr expr list"
  shows A_compE1: "\<lbrakk> \<A> e = \<lfloor>A\<rfloor>; fv e \<subseteq> set Vs \<rbrakk> \<Longrightarrow> \<A> (compE1 Vs e) = \<lfloor>index Vs ` A\<rfloor>"
  and As_compEs1: "\<lbrakk> \<A>s es = \<lfloor>A\<rfloor>; fvs es \<subseteq> set Vs \<rbrakk> \<Longrightarrow> \<A>s (compEs1 Vs es) = \<lfloor>index Vs ` A\<rfloor>"
proof(induct Vs e and Vs es arbitrary: A and A rule: compE1_compEs1_induct)
  case (Block Vs V' T vo e)
  hence "fv e \<subseteq> set (Vs@[V'])" by fastforce
  moreover obtain B where "\<A> e = \<lfloor>B\<rfloor>"
    using Block.prems by(simp add: hyperset_defs)
  moreover from calculation have "B \<subseteq> set (Vs@[V'])" by(auto dest!:A_fv)
  ultimately show ?case using Block
    by(auto simp add: hyperset_defs image_index)
next
  case (Synchronized Vs V exp1 exp2 A)
  have IH1: "\<And>A. \<lbrakk>\<A> exp1 = \<lfloor>A\<rfloor>; fv exp1 \<subseteq> set Vs\<rbrakk> \<Longrightarrow> \<A> (compE1 Vs exp1) = \<lfloor>index Vs ` A\<rfloor>" by fact
  have IH2: "\<And>A. \<lbrakk>\<A> exp2 = \<lfloor>A\<rfloor>; fv exp2 \<subseteq> set (Vs @ [fresh_var Vs])\<rbrakk> \<Longrightarrow> \<A> (compE1 (Vs @ [fresh_var Vs]) exp2) = \<lfloor>index (Vs @ [fresh_var Vs]) ` A\<rfloor>" by fact
  from \<open>fv (sync\<^bsub>V\<^esub> (exp1) exp2) \<subseteq> set Vs\<close> 
  have fv1: "fv exp1 \<subseteq> set Vs"
    and fv2: "fv exp2 \<subseteq> set Vs" by auto
  from \<open>\<A> (sync\<^bsub>V\<^esub> (exp1) exp2) = \<lfloor>A\<rfloor>\<close> have A: "\<A> exp1 \<squnion> \<A> exp2 = \<lfloor>A\<rfloor>" by(simp)
  then obtain A1 A2 where A1: "\<A> exp1 = \<lfloor>A1\<rfloor>" and A2: "\<A> exp2 = \<lfloor>A2\<rfloor>" by(auto simp add: hyperset_defs)
  from A2 fv2 have "A2 \<subseteq> set Vs" by(auto dest: A_fv del: subsetI)
  with fresh_var_fresh[of Vs] have "(fresh_var Vs) \<notin> A2" by(auto)
  from fv2 have "fv exp2 \<subseteq> set (Vs @ [fresh_var Vs])" by auto
  with IH2[OF A2] have "\<A> (compE1 (Vs @ [fresh_var Vs]) exp2) = \<lfloor>index (Vs @ [fresh_var Vs]) ` A2\<rfloor>" by(auto)
  with IH1[OF A1 fv1] A[symmetric] \<open>A2 \<subseteq> set Vs\<close> \<open>(fresh_var Vs) \<notin> A2\<close> A1 A2 show ?case
    by(auto simp add: image_index)
next
  case (InSynchronized Vs V a exp A)
  have IH: "\<And>A. \<lbrakk>\<A> exp = \<lfloor>A\<rfloor>; fv exp \<subseteq> set (Vs @ [fresh_var Vs])\<rbrakk> \<Longrightarrow> \<A> (compE1 (Vs @ [fresh_var Vs]) exp) = \<lfloor>index (Vs @ [fresh_var Vs]) ` A\<rfloor>" by fact
  from \<open>\<A> (insync\<^bsub>V\<^esub> (a) exp) = \<lfloor>A\<rfloor>\<close> have A: "\<A> exp = \<lfloor>A\<rfloor>" by simp
  from \<open>fv (insync\<^bsub>V\<^esub> (a) exp) \<subseteq> set Vs\<close> have fv: "fv exp \<subseteq> set Vs" by simp
  from A fv have "A \<subseteq> set Vs" by(auto dest: A_fv del: subsetI)
  with fresh_var_fresh[of Vs] have "(fresh_var Vs) \<notin> A" by(auto)
  from fv IH[OF A] have " \<A> (compE1 (Vs @ [fresh_var Vs]) exp) = \<lfloor>index (Vs @ [fresh_var Vs]) ` A\<rfloor>" by simp
  with \<open>A \<subseteq> set Vs\<close> \<open>(fresh_var Vs) \<notin> A\<close> show ?case by(simp add: image_index)
next
  case (TryCatch Vs e1 C V' e2)
  hence fve2: "fv e2 \<subseteq> set (Vs@[V'])" by auto
  show ?case
  proof (cases "\<A> e1")
    assume A1: "\<A> e1 = None"
    then obtain A2 where A2: "\<A> e2 = \<lfloor>A2\<rfloor>" using TryCatch
      by(simp add:hyperset_defs)
    hence "A2 \<subseteq> set (Vs@[V'])" using TryCatch.prems A_fv[OF A2] by simp blast
    thus ?thesis using TryCatch fve2 A1 A2
      by(auto simp add:hyperset_defs image_index)
  next
    fix A1 assume A1: "\<A> e1 =  \<lfloor>A1\<rfloor>"
    show ?thesis
    proof (cases  "\<A> e2")
      assume A2: "\<A> e2 = None"
      then show ?case using TryCatch A1 by(simp add:hyperset_defs)
    next
      fix A2 assume A2: "\<A> e2 = \<lfloor>A2\<rfloor>"
      have "A1 \<subseteq> set Vs" using TryCatch.prems A_fv[OF A1] by simp blast
      moreover
      have "A2 \<subseteq> set (Vs@[V'])" using TryCatch.prems A_fv[OF A2] by simp blast
      ultimately show ?thesis using TryCatch A1 A2
        by(fastforce simp add: hyperset_defs image_index
          Diff_subset_conv inj_on_image_Int[OF inj_on_index])
    qed
  qed
next
  case (Cond Vs e e1 e2)
  { assume "\<A> e = None \<or> \<A> e1 = None \<or> \<A> e2 = None"
    hence ?case using Cond by(auto simp add:hyperset_defs image_Un)
  }
  moreover
  { fix A A1 A2
    assume "\<A> e = \<lfloor>A\<rfloor>" and A1: "\<A> e1 = \<lfloor>A1\<rfloor>" and A2: "\<A> e2 = \<lfloor>A2\<rfloor>"
    moreover
    have "A1 \<subseteq> set Vs" using Cond.prems A_fv[OF A1] by simp blast
    moreover
    have "A2 \<subseteq> set Vs" using Cond.prems A_fv[OF A2] by simp blast
    ultimately have ?case using Cond
      by(auto simp add:hyperset_defs image_Un
          inj_on_image_Int[OF inj_on_index])
  }
  ultimately show ?case by fastforce
qed (auto simp add:hyperset_defs)

lemma fixes e :: "('a, 'b, 'addr) exp" and es :: "('a, 'b, 'addr) exp list"
  shows D_None [iff]: "\<D> e None"
  and Ds_None [iff]: "\<D>s es None"
by(induct e and es rule: \<D>.induct \<D>s.induct)(simp_all)

declare Un_ac [simp]

lemma fixes e :: "'addr expr" and es :: "'addr expr list"
  shows D_index_compE1: "\<lbrakk> A \<subseteq> set Vs; fv e \<subseteq> set Vs \<rbrakk> \<Longrightarrow> \<D> e \<lfloor>A\<rfloor> \<Longrightarrow> \<D> (compE1 Vs e) \<lfloor>index Vs ` A\<rfloor>"
  and Ds_index_compEs1: "\<lbrakk> A \<subseteq> set Vs; fvs es \<subseteq> set Vs \<rbrakk> \<Longrightarrow> \<D>s es \<lfloor>A\<rfloor> \<Longrightarrow> \<D>s (compEs1 Vs es) \<lfloor>index Vs ` A\<rfloor>"
proof(induct e and es arbitrary: A Vs and A Vs rule: \<D>.induct \<D>s.induct)
  case (BinOp e1 bop e2)
  hence IH1: "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e1")
    case None thus ?thesis using BinOp by simp
  next
    case (Some A1)
    have indexA1: "\<A> (compE1 Vs e1) = \<lfloor>index Vs ` A1\<rfloor>"
      using A_compE1[OF Some] BinOp.prems  by auto
    have "A \<union> A1 \<subseteq> set Vs" using BinOp.prems A_fv[OF Some] by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` (A1 \<union> A)\<rfloor>" using BinOp Some by(auto)
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` A1 \<union> index Vs ` A\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH1 indexA1 by auto
  qed
next
  case (AAcc a i A Vs)
  have IH1: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv a \<subseteq> set Vs; \<D> a \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs a) \<lfloor>index Vs ` A\<rfloor>" by fact
  have IH2: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv i \<subseteq> set Vs; \<D> i \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs i) \<lfloor>index Vs ` A\<rfloor>" by fact
  from \<open>\<D> (a\<lfloor>i\<rceil>) \<lfloor>A\<rfloor>\<close> have D1: "\<D> a \<lfloor>A\<rfloor>" and D2: "\<D> i (\<lfloor>A\<rfloor> \<squnion> \<A> a)" by auto
  from \<open>fv (a\<lfloor>i\<rceil>) \<subseteq> set Vs\<close> have fv1: "fv a \<subseteq> set Vs" and fv2: "fv i \<subseteq> set Vs" by auto
  show ?case
  proof(cases "\<A> a")
    case None thus ?thesis using AAcc by simp
  next
    case (Some A1)
    with fv1 have "\<A> (compE1 Vs a) = \<lfloor>index Vs ` A1\<rfloor>" by-(rule A_compE1)
    moreover from A_fv[OF Some] fv1 \<open>A \<subseteq> set Vs\<close> have "A1 \<union> A \<subseteq> set Vs" by auto
    from IH2[OF this fv2] Some D2 have "\<D> (compE1 Vs i) \<lfloor>index Vs ` A1 \<union> index Vs ` A\<rfloor>"
      by(simp add: image_Un)
    ultimately show ?thesis using IH1[OF \<open>A \<subseteq> set Vs\<close> fv1 D1] by(simp)
  qed
next
  case (AAss a i e A Vs)
  have IH1: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv a \<subseteq> set Vs; \<D> a \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs a) \<lfloor>index Vs ` A\<rfloor>" by fact
  have IH2: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv i \<subseteq> set Vs; \<D> i \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs i) \<lfloor>index Vs ` A\<rfloor>" by fact
  have IH3: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv e \<subseteq> set Vs; \<D> e \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs e) \<lfloor>index Vs ` A\<rfloor>" by fact
  from \<open>\<D> (a\<lfloor>i\<rceil>:=e) \<lfloor>A\<rfloor>\<close> have D1: "\<D> a \<lfloor>A\<rfloor>" and D2: "\<D> i (\<lfloor>A\<rfloor> \<squnion> \<A> a)" 
    and D3: "\<D> e (\<lfloor>A\<rfloor> \<squnion> \<A> a \<squnion> \<A> i)" by auto
  from \<open>fv (a\<lfloor>i\<rceil> := e) \<subseteq> set Vs\<close>
  have fv1: "fv a \<subseteq> set Vs" and fv2: "fv i \<subseteq> set Vs" and fv3: "fv e \<subseteq> set Vs" by auto
  show ?case
  proof(cases "\<A> a")
    case None thus ?thesis using AAss by simp
  next
    case (Some A1)
    with fv1 have A1: "\<A> (compE1 Vs a) = \<lfloor>index Vs ` A1\<rfloor>" by-(rule A_compE1)
    from A_fv[OF Some] fv1 \<open>A \<subseteq> set Vs\<close> have "A1 \<union> A \<subseteq> set Vs" by auto
    from IH2[OF this fv2] Some D2 have D2': "\<D> (compE1 Vs i) \<lfloor>index Vs ` A1 \<union> index Vs ` A\<rfloor>"
      by(simp add: image_Un)
    show ?thesis
    proof(cases "\<A> i")
      case None thus ?thesis using AAss D2' Some A1 by simp
    next
      case (Some A2)
      with fv2 have A2: "\<A> (compE1 Vs i) = \<lfloor>index Vs ` A2\<rfloor>" by-(rule A_compE1)
      moreover from A_fv[OF Some] fv2 \<open>A1 \<union> A \<subseteq> set Vs\<close> have "A1 \<union> A \<union> A2 \<subseteq> set Vs" by auto
      from IH3[OF this fv3] Some \<open>\<A> a = \<lfloor>A1\<rfloor>\<close> D3
      have "\<D> (compE1 Vs e) \<lfloor>index Vs ` A1 \<union> index Vs ` A \<union> index Vs ` A2\<rfloor>"
        by(simp add: image_Un Un_commute Un_assoc)
      ultimately show ?thesis using IH1[OF \<open>A \<subseteq> set Vs\<close> fv1 D1] D2' A1 A2 by(simp)
    qed
  qed
next
  case (FAss e1 F D e2)
  hence IH1: "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e1")
    case None thus ?thesis using FAss by simp
  next
    case (Some A1)
    have indexA1: "\<A> (compE1 Vs e1) = \<lfloor>index Vs ` A1\<rfloor>"
      using A_compE1[OF Some] FAss.prems  by auto
    have "A \<union> A1 \<subseteq> set Vs" using FAss.prems A_fv[OF Some] by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` (A \<union> A1)\<rfloor>" using FAss Some by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` A \<union> index Vs ` A1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH1 indexA1 by auto
  qed
next
  case (CompareAndSwap e1 D F e2 e3 A Vs)
  have IH1: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv e1 \<subseteq> set Vs; \<D> e1 \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs e1) \<lfloor>index Vs ` A\<rfloor>" by fact
  have IH2: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv e2 \<subseteq> set Vs; \<D> e2 \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs e2) \<lfloor>index Vs ` A\<rfloor>" by fact
  have IH3: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv e3 \<subseteq> set Vs; \<D> e3 \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs e3) \<lfloor>index Vs ` A\<rfloor>" by fact
  from \<open>\<D> (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) \<lfloor>A\<rfloor>\<close> have D1: "\<D> e1 \<lfloor>A\<rfloor>" and D2: "\<D> e2 (\<lfloor>A\<rfloor> \<squnion> \<A> e1)" 
    and D3: "\<D> e3 (\<lfloor>A\<rfloor> \<squnion> \<A> e1 \<squnion> \<A> e2)" by auto
  from \<open>fv (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) \<subseteq> set Vs\<close>
  have fv1: "fv e1 \<subseteq> set Vs" and fv2: "fv e2 \<subseteq> set Vs" and fv3: "fv e3 \<subseteq> set Vs" by auto
  show ?case
  proof(cases "\<A> e1")
    case None thus ?thesis using CompareAndSwap by simp
  next
    case (Some A1)
    with fv1 have A1: "\<A> (compE1 Vs e1) = \<lfloor>index Vs ` A1\<rfloor>" by-(rule A_compE1)
    from A_fv[OF Some] fv1 \<open>A \<subseteq> set Vs\<close> have "A1 \<union> A \<subseteq> set Vs" by auto
    from IH2[OF this fv2] Some D2 have D2': "\<D> (compE1 Vs e2) \<lfloor>index Vs ` A1 \<union> index Vs ` A\<rfloor>"
      by(simp add: image_Un)
    show ?thesis
    proof(cases "\<A> e2")
      case None thus ?thesis using CompareAndSwap D2' Some A1 by simp
    next
      case (Some A2)
      with fv2 have A2: "\<A> (compE1 Vs e2) = \<lfloor>index Vs ` A2\<rfloor>" by-(rule A_compE1)
      moreover from A_fv[OF Some] fv2 \<open>A1 \<union> A \<subseteq> set Vs\<close> have "A1 \<union> A \<union> A2 \<subseteq> set Vs" by auto
      from IH3[OF this fv3] Some \<open>\<A> e1 = \<lfloor>A1\<rfloor>\<close> D3
      have "\<D> (compE1 Vs e3) \<lfloor>index Vs ` A1 \<union> index Vs ` A \<union> index Vs ` A2\<rfloor>"
        by(simp add: image_Un Un_commute Un_assoc)
      ultimately show ?thesis using IH1[OF \<open>A \<subseteq> set Vs\<close> fv1 D1] D2' A1 A2 by(simp)
    qed
  qed
next
  case (Call e1 M es)
  hence IH1: "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e1")
    case None thus ?thesis using Call by simp
  next
    case (Some A1)
    have indexA1: "\<A> (compE1 Vs e1) = \<lfloor>index Vs ` A1\<rfloor>"
      using A_compE1[OF Some] Call.prems  by auto
    have "A \<union> A1 \<subseteq> set Vs" using Call.prems A_fv[OF Some] by auto
    hence "\<D>s (compEs1 Vs es) \<lfloor>index Vs ` (A \<union> A1)\<rfloor>" using Call Some by auto
    hence "\<D>s (compEs1 Vs es) \<lfloor>index Vs ` A \<union> index Vs ` A1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH1 indexA1 by auto
  qed
next
  case (Synchronized V exp1 exp2 A Vs)
  have IH1: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv exp1 \<subseteq> set Vs; \<D> exp1 \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs exp1) \<lfloor>index Vs ` A\<rfloor>" by fact
  have IH2: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv exp2 \<subseteq> set Vs; \<D> exp2 \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs exp2) \<lfloor>index Vs ` A\<rfloor>" by fact
  from \<open>\<D> (sync\<^bsub>V\<^esub> (exp1) exp2) \<lfloor>A\<rfloor>\<close> have D1: "\<D> exp1 \<lfloor>A\<rfloor>" and D2: "\<D> exp2 (\<lfloor>A\<rfloor> \<squnion> \<A> exp1)" by auto
  from \<open>fv (sync\<^bsub>V\<^esub> (exp1) exp2) \<subseteq> set Vs\<close> have fv1: "fv exp1 \<subseteq> set Vs" and fv2: "fv exp2 \<subseteq> set Vs" by auto
  show ?case
  proof(cases "\<A> exp1")
    case None thus ?thesis using Synchronized by(simp)
  next
    case (Some A1)
    with fv1 have A1: "\<A> (compE1 Vs exp1) = \<lfloor>index Vs ` A1\<rfloor>" by-(rule A_compE1)
    from A_fv[OF Some] fv1 \<open>A \<subseteq> set Vs\<close> have "A \<union> A1 \<subseteq> set Vs" by auto
    hence "A \<union> A1 \<subseteq> set (Vs @ [fresh_var Vs])" by simp
    from IH2[OF this] fv2 Some D2
    have D2': "\<D> (compE1 (Vs @ [fresh_var Vs]) exp2) \<lfloor>index (Vs @ [fresh_var Vs]) ` (A \<union> A1)\<rfloor>"
      by(simp)
    moreover from fresh_var_fresh[of Vs] \<open>A \<union> A1 \<subseteq> set Vs\<close>
    have "(fresh_var Vs) \<notin> A \<union> A1" by auto
    with \<open>A \<union> A1 \<subseteq> set Vs\<close>
    have "index (Vs @ [fresh_var Vs]) ` (A \<union> A1) = index Vs ` A \<union> index Vs ` A1"
      by(simp add: image_index image_Un)
    ultimately show ?thesis using IH1[OF \<open>A \<subseteq> set Vs\<close> fv1 D1] D2' A1 by(simp)
  qed
next
  case (InSynchronized V a e A Vs)
  have IH: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv e \<subseteq> set Vs; \<D> e \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs e) \<lfloor>index Vs ` A\<rfloor>" by fact
  from IH[of A "Vs @ [fresh_var Vs]"] \<open>A \<subseteq> set Vs\<close> \<open>fv (insync\<^bsub>V\<^esub> (a) e) \<subseteq> set Vs\<close> \<open>\<D> (insync\<^bsub>V\<^esub> (a) e) \<lfloor>A\<rfloor>\<close>
  have "\<D> (compE1 (Vs @ [fresh_var Vs]) e) \<lfloor>index (Vs @ [fresh_var Vs]) ` A\<rfloor>" by(auto)
  moreover from fresh_var_fresh[of Vs] \<open>A \<subseteq> set Vs\<close> have "(fresh_var Vs) \<notin> A" by auto
  with \<open>A \<subseteq> set Vs\<close> have "index (Vs @ [fresh_var Vs]) ` A = index Vs ` A" by(simp add: image_index)
  ultimately show ?case by(simp)
next
  case (TryCatch e1 C V e2)
  have "\<lbrakk> A\<union>{V} \<subseteq> set(Vs@[V]); fv e2 \<subseteq> set(Vs@[V]); \<D> e2 \<lfloor>A\<union>{V}\<rfloor>\<rbrakk> \<Longrightarrow>
        \<D> (compE1 (Vs@[V]) e2) \<lfloor>index (Vs@[V]) ` (A\<union>{V})\<rfloor>" by fact
  hence "\<D> (compE1 (Vs@[V]) e2) \<lfloor>index (Vs@[V]) ` (A\<union>{V})\<rfloor>"
    using TryCatch.prems by(simp add:Diff_subset_conv)
  moreover have "index (Vs@[V]) ` A \<subseteq> index Vs ` A \<union> {size Vs}"
    using TryCatch.prems by(auto simp add: image_index split:if_split_asm)
  ultimately show ?case using TryCatch by(auto simp:hyperset_defs elim!:D_mono')
next
  case (Seq e1 e2)
  hence IH1: "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e1")
    case None thus ?thesis using Seq by simp
  next
    case (Some A1)
    have indexA1: "\<A> (compE1 Vs e1) = \<lfloor>index Vs ` A1\<rfloor>"
      using A_compE1[OF Some] Seq.prems  by auto
    have "A \<union> A1 \<subseteq> set Vs" using Seq.prems A_fv[OF Some] by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` (A \<union> A1)\<rfloor>" using Seq Some by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` A \<union> index Vs ` A1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH1 indexA1 by auto
  qed
next
  case (Cond e e1 e2)
  hence IH1: "\<D> (compE1 Vs e) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e")
    case None thus ?thesis using Cond by simp
  next
    case (Some B)
    have indexB: "\<A> (compE1 Vs e) = \<lfloor>index Vs ` B\<rfloor>"
      using A_compE1[OF Some] Cond.prems  by auto
    have "A \<union> B \<subseteq> set Vs" using Cond.prems A_fv[OF Some] by auto
    hence "\<D> (compE1 Vs e1) \<lfloor>index Vs ` (A \<union> B)\<rfloor>"
      and "\<D> (compE1 Vs e2) \<lfloor>index Vs ` (A \<union> B)\<rfloor>"
      using Cond Some by auto
    hence "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A \<union> index Vs ` B\<rfloor>"
      and "\<D> (compE1 Vs e2) \<lfloor>index Vs ` A \<union> index Vs ` B\<rfloor>"
      by(simp add: image_Un)+
    thus ?thesis using IH1 indexB by auto
  qed
next
  case (While e1 e2)
  hence IH1: "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e1")
    case None thus ?thesis using While by simp
  next
    case (Some A1)
    have indexA1: "\<A> (compE1 Vs e1) = \<lfloor>index Vs ` A1\<rfloor>"
      using A_compE1[OF Some] While.prems  by auto
    have "A \<union> A1 \<subseteq> set Vs" using While.prems A_fv[OF Some] by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` (A \<union> A1)\<rfloor>" using While Some by auto
    hence "\<D> (compE1 Vs e2) \<lfloor>index Vs ` A \<union> index Vs ` A1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH1 indexA1 by auto
  qed
next
  case (Block V T vo e A Vs)
  have IH: "\<And>A Vs. \<lbrakk>A \<subseteq> set Vs; fv e \<subseteq> set Vs; \<D> e \<lfloor>A\<rfloor>\<rbrakk> \<Longrightarrow> \<D> (compE1 Vs e) \<lfloor>index Vs ` A\<rfloor>" by fact
  from \<open>fv {V:T=vo; e} \<subseteq> set Vs\<close> have fv: "fv e \<subseteq> set (Vs @ [V])" by auto
  show ?case
  proof(cases vo)
    case None
    with \<open>\<D> {V:T=vo; e} \<lfloor>A\<rfloor>\<close> have D: "\<D> e \<lfloor>A - {V}\<rfloor>" by(auto)
    from \<open>A \<subseteq> set Vs\<close> have "A - {V} \<subseteq> set (Vs @ [V])" by auto
    from IH[OF this fv D] have "\<D> (compE1 (Vs @ [V]) e) \<lfloor>index (Vs @ [V]) ` (A - {V})\<rfloor>" .
    moreover from \<open>A \<subseteq> set Vs\<close> have size: "size Vs \<notin> index Vs ` A" by(auto simp add: image_def)
    hence "\<lfloor>index Vs ` (A - {V})\<rfloor> \<sqsubseteq> \<lfloor>index Vs ` A\<rfloor>" by(auto simp add: hyperset_defs)
    ultimately have "\<D> (compE1 (Vs @ [V]) e) \<lfloor>index Vs ` A\<rfloor>" using \<open>A - {V} \<subseteq> set (Vs @ [V])\<close>
      by(simp add: image_index)(erule D_mono', auto)
    thus ?thesis using None size by(simp)
  next
    case (Some v)
    with \<open>\<D> {V:T=vo; e} \<lfloor>A\<rfloor>\<close> have D: "\<D> e \<lfloor>insert V A\<rfloor>" by(auto)
    from \<open>A \<subseteq> set Vs\<close> have "insert V A \<subseteq> set (Vs @ [V])" by auto
    from IH[OF this fv D] have "\<D> (compE1 (Vs @ [V]) e) \<lfloor>index (Vs @ [V]) ` insert V A\<rfloor>" by simp
    moreover from \<open>A \<subseteq> set Vs\<close> have "index (Vs @ [V]) ` insert V A \<subseteq> insert (length Vs) (index Vs ` A)"
      by(auto simp add: image_index)
    ultimately show ?thesis using Some by(auto elim!: D_mono' simp add: hyperset_defs)
  qed
next
  case (Cons_exp e1 es)
  hence IH1: "\<D> (compE1 Vs e1) \<lfloor>index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e1")
    case None thus ?thesis using Cons_exp by simp
  next
    case (Some A1)
    have indexA1: "\<A> (compE1 Vs e1) = \<lfloor>index Vs ` A1\<rfloor>"
      using A_compE1[OF Some] Cons_exp.prems  by auto
    have "A \<union> A1 \<subseteq> set Vs" using Cons_exp.prems A_fv[OF Some] by auto
    hence "\<D>s (compEs1 Vs es) \<lfloor>index Vs ` (A \<union> A1)\<rfloor>" using Cons_exp Some by auto
    hence "\<D>s (compEs1 Vs es) \<lfloor>index Vs ` A \<union> index Vs ` A1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH1 indexA1 by auto
  qed
qed (simp_all add:hyperset_defs)

declare Un_ac [simp del]

lemma index_image_set: "distinct xs \<Longrightarrow> index xs ` set xs = {..<size xs}"
by(induct xs rule:rev_induct) (auto simp add: image_index)

lemma D_compE1:
  "\<lbrakk> \<D> e \<lfloor>set Vs\<rfloor>; fv e \<subseteq> set Vs; distinct Vs \<rbrakk> \<Longrightarrow> \<D> (compE1 Vs e) \<lfloor>{..<length Vs}\<rfloor>"
by(fastforce dest!: D_index_compE1[OF subset_refl] simp add:index_image_set)

lemma D_compE1':
  assumes "\<D> e \<lfloor>set(V#Vs)\<rfloor>" and "fv e \<subseteq> set(V#Vs)" and "distinct(V#Vs)"
  shows "\<D> (compE1 (V#Vs) e) \<lfloor>{..length Vs}\<rfloor>"
proof -
  have "{..size Vs} = {..<size(V#Vs)}" by auto
  thus ?thesis using assms by (simp only:)(rule D_compE1)
qed

lemma compP1_pres_wf: "wf_J_prog P \<Longrightarrow> wf_J1_prog (compP1 P)"
apply simp
apply(rule wf_prog_compPI)
 prefer 2 apply assumption
apply(case_tac m)
apply(simp add:wf_mdecl_def)
apply(clarify)
apply(frule WT_fv)
apply(fastforce intro!: compE1_pres_wt D_compE1' \<B> syncvars_compE1)
done

end
