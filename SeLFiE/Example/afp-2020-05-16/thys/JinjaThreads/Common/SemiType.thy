(*  Title:      JinjaThreads/Common/SemiType.thy
    Author:     Tobias Nipkow, Gerwin Klein, Andreas Lochbihler
*)

section \<open>The Jinja Type System as a Semilattice\<close>

theory SemiType
imports
  WellForm
  "../DFA/Semilattices"
begin

inductive_set
  widen1 :: "'a prog \<Rightarrow> (ty \<times> ty) set"
  and widen1_syntax :: "'a prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ <\<^sup>1 _" [71,71,71] 70)
  for P :: "'a prog"
where
  "P \<turnstile> C <\<^sup>1 D \<equiv> (C, D) \<in> widen1 P"

| widen1_Array_Object:
  "P \<turnstile> Array (Class Object) <\<^sup>1 Class Object"

| widen1_Array_Integer:
  "P \<turnstile> Array Integer <\<^sup>1 Class Object"

| widen1_Array_Boolean:
  "P \<turnstile> Array Boolean <\<^sup>1 Class Object"

| widen1_Array_Void:
  "P \<turnstile> Array Void <\<^sup>1 Class Object"

| widen1_Class: 
  "P \<turnstile> C \<prec>\<^sup>1 D \<Longrightarrow> P \<turnstile> Class C <\<^sup>1 Class D"

| widen1_Array_Array:
  "\<lbrakk> P \<turnstile> T <\<^sup>1 U; \<not> is_NT_Array T \<rbrakk> \<Longrightarrow> P \<turnstile> Array T <\<^sup>1 Array U"

abbreviation widen1_trancl :: "'a prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ <\<^sup>+ _" [71,71,71] 70) where
  "P \<turnstile> T <\<^sup>+ U \<equiv> (T, U) \<in> trancl (widen1 P)"

abbreviation widen1_rtrancl :: "'a prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ <\<^sup>* _" [71,71,71] 70) where
  "P \<turnstile> T <\<^sup>* U \<equiv> (T, U) \<in> rtrancl (widen1 P)"

inductive_simps widen1_simps1 [simp]:
  "P \<turnstile> Integer <\<^sup>1 T"
  "P \<turnstile> Boolean <\<^sup>1 T"
  "P \<turnstile> Void <\<^sup>1 T"
  "P \<turnstile> Class Object <\<^sup>1 T"
  "P \<turnstile> NT <\<^sup>1 U"

inductive_simps widen1_simps [simp]:
  "P \<turnstile> Array (Class Object) <\<^sup>1 T"
  "P \<turnstile> Array Integer <\<^sup>1 T"
  "P \<turnstile> Array Boolean <\<^sup>1 T"
  "P \<turnstile> Array Void <\<^sup>1 T"
  "P \<turnstile> Class C <\<^sup>1 T"
  "P \<turnstile> T <\<^sup>1 Array U"

lemma is_type_widen1: 
  assumes icO: "is_class P Object"
  shows "P \<turnstile> T <\<^sup>1 U \<Longrightarrow> is_type P T"
by(induct rule: widen1.induct)(auto intro: subcls_is_class icO split: ty.split dest: is_type_ground_type)

lemma widen1_NT_Array:
  assumes "is_NT_Array T"
  shows "\<not> P \<turnstile> T\<lfloor>\<rceil> <\<^sup>1 U"
proof
  assume "P \<turnstile> T\<lfloor>\<rceil> <\<^sup>1 U" thus False using assms
    by(induct "T\<lfloor>\<rceil>" U arbitrary: T) auto
qed

lemma widen1_is_type:
  assumes wfP: "wf_prog wfmd P"
  shows "(A, B) \<in> widen1 P \<Longrightarrow> is_type P B"
proof(induct rule: widen1.induct)
  case (widen1_Class C D)
  hence "is_class P C" "is_class P D"
    by(auto intro: subcls_is_class converse_subcls_is_class[OF wfP])
  thus ?case by simp
next
  case (widen1_Array_Array T U)
  thus ?case by(cases U)(auto elim: widen1.cases)
qed(insert wfP, auto)

lemma widen1_trancl_is_type:
  assumes wfP: "wf_prog wfmd P"
  shows "(A, B) \<in> (widen1 P)^+ \<Longrightarrow> is_type P B"
apply(induct rule: trancl_induct)
apply(auto intro: widen1_is_type[OF wfP])
done

lemma single_valued_widen1:
  assumes wf: "wf_prog wf_md P"
  shows "single_valued (widen1 P)"
proof(rule single_valuedI)
  fix x y z
  assume "P \<turnstile> x <\<^sup>1 y" "P \<turnstile> x <\<^sup>1 z"
  thus "y = z"
  proof(induct arbitrary: z rule: widen1.induct)
    case widen1_Class
    with single_valued_subcls1[OF wf] show ?case
      by(auto dest: single_valuedpD)
  next
    case (widen1_Array_Array T U z)
    from \<open>P \<turnstile> T\<lfloor>\<rceil> <\<^sup>1 z\<close> \<open>P \<turnstile> T <\<^sup>1 U\<close> \<open>\<not> is_NT_Array T\<close>
    obtain z' where z': "z = z'\<lfloor>\<rceil>" and Tz': "P \<turnstile> T <\<^sup>1 z'"
      by(auto elim: widen1.cases)
    with \<open>P \<turnstile> T <\<^sup>1 z' \<Longrightarrow> U = z'\<close> have "U = z'" by blast
    with z' show ?case by simp
  qed simp_all
qed

function inheritance_level :: "'a prog \<Rightarrow> cname \<Rightarrow> nat" where
  "inheritance_level P C =
   (if acyclicP (subcls1 P) \<and> is_class P C \<and> C \<noteq> Object
    then Suc (inheritance_level P (fst (the (class P C))))
    else 0)"
by(pat_completeness, auto)
termination
proof(relation "same_fst (\<lambda>P. acyclicP (subcls1 P)) (\<lambda>P. {(C, C'). (subcls1 P)\<inverse>\<inverse> C C'})")
  show "wf (same_fst (\<lambda>P. acyclicP (subcls1 P)) (\<lambda>P. {(C, C'). (subcls1 P)\<inverse>\<inverse> C C'}))"
    by(rule wf_same_fst)(rule acyclicP_wf_subcls1[unfolded wfP_def])
qed(auto simp add: is_class_def intro: subcls1I)

fun subtype_measure :: "'a prog \<Rightarrow> ty \<Rightarrow> nat" where
  "subtype_measure P (Class C) = inheritance_level P C"
| "subtype_measure P (Array T) = 1 + subtype_measure P T"
| "subtype_measure P T = 0"

lemma subtype_measure_measure:
  assumes acyclic: "acyclicP (subcls1 P)"
  and widen1: "P \<turnstile> x <\<^sup>1 y"
  shows "subtype_measure P y < subtype_measure P x"
using widen1
proof(induct rule: widen1.induct)
  case (widen1_Class C D)
  then obtain rest where "is_class P C" "C \<noteq> Object" "class P C = \<lfloor>(D, rest)\<rfloor>"
    by(auto elim!: subcls1.cases simp: is_class_def)
  thus ?case using acyclic by(simp)
qed(simp_all)

lemma wf_converse_widen1:
  assumes wfP: "wf_prog wfmc P"
  shows "wf ((widen1 P)^-1)"
proof(rule wf_subset)
  from wfP have "acyclicP (subcls1 P)" by(rule acyclic_subcls1)
  thus "(widen1 P)\<inverse> \<subseteq> measure (subtype_measure P)" 
    by(auto dest: subtype_measure_measure)
qed simp

fun super :: "'a prog \<Rightarrow> ty \<Rightarrow> ty"
where
  "super P (Array Integer) = Class Object"
| "super P (Array Boolean) = Class Object"
| "super P (Array Void) = Class Object"
| "super P (Array (Class C)) = (if C = Object then Class Object else Array (super P (Class C)))"
| "super P (Array (Array T)) = Array (super P (Array T))"
| "super P (Class C) = Class (fst (the (class P C)))"

lemma superI:
  "P \<turnstile> T <\<^sup>1 U \<Longrightarrow> super P T = U"
proof(induct rule: widen1.induct)
  case (widen1_Array_Array T U)
  thus ?case by(cases T) auto
qed(auto dest: subcls1D)

lemma Class_widen1_super:
  "P \<turnstile> Class C' <\<^sup>1 U' \<longleftrightarrow> is_class P C' \<and> C' \<noteq> Object \<and> U' = super P (Class C')"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs thus ?rhs
    by(auto intro: subcls_is_class simp add: superI simp del: super.simps)
next
  assume ?rhs thus ?lhs
    by(auto simp add: is_class_def intro: subcls1.intros)
qed

lemma super_widen1:
  assumes icO: "is_class P Object"
  shows "P \<turnstile> T <\<^sup>1 U \<longleftrightarrow> is_type P T \<and> (case T of Class C  \<Rightarrow> (C \<noteq> Object \<and> U = super P T) 
                                              | Array T' \<Rightarrow> U = super P T 
                                              | _        \<Rightarrow> False)"
proof(induct T arbitrary: U)
  case Class thus ?case using Class_widen1_super by(simp)
next
  case (Array T' U')
  note IH = this
  have "P \<turnstile> T'\<lfloor>\<rceil> <\<^sup>1 U' = (is_type P (T'\<lfloor>\<rceil>) \<and> U' = super P (T'\<lfloor>\<rceil>))"
  proof(rule iffI)
    assume wd: "P \<turnstile> T'\<lfloor>\<rceil> <\<^sup>1 U'"
    with icO have "is_type P (T'\<lfloor>\<rceil>)" by(rule is_type_widen1)
    moreover from wd have "super P (T'\<lfloor>\<rceil>) = U'" by(rule superI)
    ultimately show "is_type P (T'\<lfloor>\<rceil>) \<and> U' = super P (T'\<lfloor>\<rceil>)" by simp
  next
    assume "is_type P (T'\<lfloor>\<rceil>) \<and> U' = super P (T'\<lfloor>\<rceil>)"
    then obtain "is_type P (T'\<lfloor>\<rceil>)" and U': "U' = super P (T'\<lfloor>\<rceil>)" ..
    thus "P \<turnstile> T'\<lfloor>\<rceil> <\<^sup>1 U'"
    proof(cases T')
      case (Class D)
      thus ?thesis using U' icO \<open>is_type P (T'\<lfloor>\<rceil>)\<close>
        by(cases "D = Object")(auto simp add: is_class_def intro: subcls1.intros)
    next
      case Array thus ?thesis
        using IH \<open>is_type P (T'\<lfloor>\<rceil>)\<close> U' by(auto simp add: ty.split_asm)
    qed simp_all
  qed
  thus ?case by(simp)
qed(simp_all)

definition sup :: "'c prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty err" where
  "sup P T U \<equiv>
   if is_refT T \<and> is_refT U
   then OK (if U = NT then T
            else if T = NT then U
            else exec_lub (widen1 P) (super P) T U)
   else if (T = U) then OK T else Err"

lemma sup_def':
  "sup P = (\<lambda>T U.
   if is_refT T \<and> is_refT U
   then OK (if U = NT then T
            else if T = NT then U
            else exec_lub (widen1 P) (super P) T U)
   else if (T = U) then OK T else Err)"
  by (simp add: fun_eq_iff sup_def)

definition esl :: "'m prog \<Rightarrow> ty esl"
where
  "esl P = (types P, widen P, sup P)"

lemma order_widen [intro,simp]: 
  "wf_prog m P \<Longrightarrow> order (widen P)"
unfolding Semilat.order_def lesub_def
by (auto intro: widen_trans widen_antisym)

lemma subcls1_trancl_widen1_trancl:
  "(subcls1 P)^++ C D \<Longrightarrow> P \<turnstile> Class C <\<^sup>+ Class D"
by(induct rule: tranclp_induct[consumes 1, case_names base step])
  (auto intro: trancl_into_trancl)

lemma subcls_into_widen1_rtrancl:
  "P \<turnstile> C \<preceq>\<^sup>* D \<Longrightarrow> P \<turnstile> Class C <\<^sup>* Class D"
by(induct rule: rtranclp_induct)(auto intro: rtrancl_into_rtrancl)

lemma not_widen1_NT_Array:
  "P \<turnstile> U <\<^sup>1 T \<Longrightarrow> \<not> is_NT_Array T"
by(induct rule: widen1.induct)(auto)

lemma widen1_trancl_into_Array_widen1_trancl:
  "\<lbrakk> P \<turnstile> A <\<^sup>+ B; \<not> is_NT_Array A \<rbrakk> \<Longrightarrow> P \<turnstile> A\<lfloor>\<rceil> <\<^sup>+ B\<lfloor>\<rceil>"
by(induct rule: converse_trancl_induct)
  (auto intro: trancl_into_trancl2 widen1_Array_Array dest: not_widen1_NT_Array)

lemma widen1_rtrancl_into_Array_widen1_rtrancl:
  "\<lbrakk> P \<turnstile> A <\<^sup>* B; \<not> is_NT_Array A \<rbrakk> \<Longrightarrow> P \<turnstile> A\<lfloor>\<rceil> <\<^sup>* B\<lfloor>\<rceil>"
by(blast elim: rtranclE intro: trancl_into_rtrancl widen1_trancl_into_Array_widen1_trancl rtrancl_into_trancl1)

lemma Array_Object_widen1_trancl:
  assumes wf: "wf_prog wmdc P"
  and itA: "is_type P (A\<lfloor>\<rceil>)"
  shows "P \<turnstile> A\<lfloor>\<rceil> <\<^sup>+ Class Object"
using itA
proof(induction A)
  case (Class C)
  hence "is_class P C" by simp
  hence "P \<turnstile> C \<preceq>\<^sup>* Object" by(rule subcls_C_Object[OF _ wf])
  hence "P \<turnstile> Class C <\<^sup>* Class Object" by(rule subcls_into_widen1_rtrancl)
  hence "P \<turnstile> Class C\<lfloor>\<rceil> <\<^sup>* Class Object\<lfloor>\<rceil>"
    by(rule widen1_rtrancl_into_Array_widen1_rtrancl) simp
  thus ?case by(rule rtrancl_into_trancl1) simp
next
  case (Array A)
  from \<open>is_type P (A\<lfloor>\<rceil>\<lfloor>\<rceil>)\<close> have "is_type P (A\<lfloor>\<rceil>)" by(rule is_type_ArrayD)
  hence "P \<turnstile> A\<lfloor>\<rceil> <\<^sup>+ Class Object" by(rule Array.IH)
  moreover from \<open>is_type P (A\<lfloor>\<rceil>\<lfloor>\<rceil>)\<close> have "\<not> is_NT_Array (A\<lfloor>\<rceil>)" by auto
  ultimately have "P \<turnstile> A\<lfloor>\<rceil>\<lfloor>\<rceil> <\<^sup>+ Class Object\<lfloor>\<rceil>"
    by(rule widen1_trancl_into_Array_widen1_trancl)
  thus ?case by(rule trancl_into_trancl) simp
qed auto

lemma widen_into_widen1_trancl:
  assumes wf: "wf_prog wfmd P"
  shows "\<lbrakk> P \<turnstile> A \<le> B; A \<noteq> B; A \<noteq> NT; is_type P A \<rbrakk> \<Longrightarrow> P \<turnstile> A <\<^sup>+ B"
proof(induct rule: widen.induct)
  case (widen_subcls C D)
  from \<open>Class C \<noteq> Class D\<close> \<open>P \<turnstile> C \<preceq>\<^sup>* D\<close> have "(subcls1 P)\<^sup>+\<^sup>+ C D"
    by(auto elim: rtranclp.cases intro: rtranclp_into_tranclp1)
  thus ?case by(rule subcls1_trancl_widen1_trancl)
next
  case widen_array_object thus ?case by(auto intro: Array_Object_widen1_trancl[OF wf])
next
  case (widen_array_array A B)
  hence "P \<turnstile> A <\<^sup>+ B" by(cases A) auto
  with \<open>is_type P (A\<lfloor>\<rceil>)\<close> show ?case by(auto intro: widen1_trancl_into_Array_widen1_trancl)
qed(auto)

lemma wf_prog_impl_acc_widen:
  assumes wfP: "wf_prog wfmd P"
  shows "acc (types P) (widen P)"
proof -
  from wf_converse_widen1[OF wfP]
  have "wf (((widen1 P)^-1)^+)" by(rule wf_trancl)

  hence wfw1t: "\<And>M T. T \<in> M \<Longrightarrow> (\<exists>z\<in>M. \<forall>y. (y, z) \<in> ((widen1 P)\<inverse>)\<^sup>+ \<longrightarrow> y \<notin> M)"
    by(auto simp only: wf_eq_minimal)
  have "wf {(y, x). is_type P x \<and> is_type P y \<and> widen P x y \<and> x \<noteq> y}"
    unfolding wf_eq_minimal
  proof(intro strip)
    fix M and T :: ty
    assume TM: "T \<in> M"
    show "\<exists>z\<in>M. \<forall>y. (y, z) \<in> {(y, T). is_type P T \<and> is_type P y \<and> widen P T y \<and> T \<noteq> y} \<longrightarrow> y \<notin> M"
    proof(cases "(\<exists>C. Class C \<in> M \<and> is_class P C) \<or> (\<exists>U. U\<lfloor>\<rceil> \<in> M \<and> is_type P (U\<lfloor>\<rceil>))")
      case True
      have BNTthesis: "\<And>B. \<lbrakk> B \<in> (M \<inter> types P) - {NT} \<rbrakk> \<Longrightarrow> ?thesis"
      proof -
        fix B
        assume BM: "B \<in> M \<inter> types P - {NT}"
        from wfw1t[OF BM] obtain z
          where zM: "z \<in> M"
          and znnt: "z \<noteq> NT"
          and itz: "is_type P z"
          and y: "\<And>y. (y, z) \<in> ((widen1 P)\<inverse>)\<^sup>+ \<Longrightarrow> y \<notin> M \<inter> types P - {NT}" by blast
        show "?thesis B"
        proof(rule bexI[OF _ zM], rule allI, rule impI)
          fix y
          assume "(y, z) \<in> {(y, T). is_type P T \<and> is_type P y \<and> widen P T y \<and> T \<noteq> y}"
          hence Pzy: "P \<turnstile> z \<le> y" and zy: "z \<noteq> y" and "is_type P y" by auto
          hence "P \<turnstile> z <\<^sup>+ y" using znnt itz
            by -(rule widen_into_widen1_trancl[OF wfP])
          hence ynM: "y \<notin> M \<inter> types P - {NT}"
            by -(rule y, simp add: trancl_converse)
          thus "y \<notin> M" using Pzy znnt \<open>is_type P y\<close> by auto
        qed
      qed
      from True show ?thesis by(fastforce intro: BNTthesis)
    next
      case False
      
      hence not_is_class: "\<And>C. Class C \<in> M \<Longrightarrow> \<not> is_class P C"
        and not_is_array: "\<And>U. U\<lfloor>\<rceil> \<in> M \<Longrightarrow> \<not> is_type P (U\<lfloor>\<rceil>)" by simp_all

      show ?thesis
      proof(cases "\<exists>C. Class C \<in> M")
        case True
        then obtain C where "Class C \<in> M" ..
        with not_is_class[of C] show ?thesis
          by(blast dest: rtranclpD subcls_is_class Class_widen)
      next
        case False
        show ?thesis
        proof(cases "\<exists>T. Array T \<in> M")
          case True
          then obtain U where U: "Array U \<in> M" ..
          hence "\<not> is_type P (U\<lfloor>\<rceil>)" by(rule not_is_array)
          thus ?thesis using U by(auto simp del: is_type.simps)
        next
          case False
          with \<open>\<not> (\<exists>C. Class C \<in> M)\<close> TM
          have "\<forall>y. P \<turnstile> T \<le> y \<and> T \<noteq> y \<longrightarrow> y \<notin> M"
            by(cases T)(fastforce simp add: NT_widen)+
          thus ?thesis using TM by blast
        qed
      qed
    qed
  qed
  thus ?thesis by(simp add: Semilat.acc_def lesssub_def lesub_def)
qed

lemmas wf_widen_acc = wf_prog_impl_acc_widen
declare wf_widen_acc [intro, simp]

lemma acyclic_widen1:
  "wf_prog wfmc P \<Longrightarrow> acyclic (widen1 P)"
by(auto dest: wf_converse_widen1 wf_acyclic simp add: acyclic_converse)

lemma widen1_into_widen:
  "(A, B) \<in> widen1 P \<Longrightarrow> P \<turnstile> A \<le> B"
by(induct rule: widen1.induct)(auto intro: widen.intros)

lemma widen1_rtrancl_into_widen:
  "P \<turnstile> A <\<^sup>* B \<Longrightarrow> P \<turnstile> A \<le> B"
by(induct rule: rtrancl_induct)(auto dest!: widen1_into_widen elim: widen_trans)

lemma widen_eq_widen1_trancl:
  "\<lbrakk> wf_prog wf_md P; T \<noteq> NT; T \<noteq> U; is_type P T \<rbrakk> \<Longrightarrow> P \<turnstile> T \<le> U \<longleftrightarrow> P \<turnstile> T <\<^sup>+ U"
by(blast intro: widen_into_widen1_trancl widen1_rtrancl_into_widen trancl_into_rtrancl)

lemma sup_is_type:
  assumes wf: "wf_prog wf_md P"
  and itA: "is_type P A"
  and itB: "is_type P B"
  and sup: "sup P A B = OK T"
  shows "is_type P T"
proof -
  { assume ANT: "A \<noteq> NT"
      and BNT: "B \<noteq> NT"
      and AnB: "A \<noteq> B"
      and RTA: "is_refT A"
      and RTB: "is_refT B"
    with itA itB have AObject: "P \<turnstile> A \<le> Class Object"
      and BObject: "P \<turnstile> B \<le> Class Object"
      by(auto intro: is_refType_widen_Object[OF wf])
    have "is_type P (exec_lub (widen1 P) (super P) A B)"
    proof(cases "A = Class Object \<or> B = Class Object")
      case True
      hence "exec_lub (widen1 P) (super P) A B = Class Object"
      proof(rule disjE)
        assume A: "A = Class Object"
        moreover
        from BObject BNT itB have "P \<turnstile> B <\<^sup>* Class Object"
          by(cases "B = Class Object")(auto intro: trancl_into_rtrancl widen_into_widen1_trancl[OF wf])
        hence "is_ub ((widen1 P)\<^sup>*) (Class Object) B (Class Object)"
          by(auto intro: is_ubI)
        hence "is_lub ((widen1 P)\<^sup>*) (Class Object) B (Class Object)"
          by(auto simp add: is_lub_def dest: is_ubD)
        with acyclic_widen1[OF wf]
        have "exec_lub (widen1 P) (super P) (Class Object) B = Class Object"
          by(auto intro: exec_lub_conv superI)
        ultimately show "exec_lub (widen1 P) (super P) A B = Class Object" by simp
      next
        assume B: "B = Class Object"
        moreover
        from AObject ANT itA
        have "(A, Class Object) \<in> (widen1 P)\<^sup>*"
          by(cases "A = Class Object", auto intro: trancl_into_rtrancl widen_into_widen1_trancl[OF wf])
        hence "is_ub ((widen1 P)\<^sup>*) (Class Object) A (Class Object)"
          by(auto intro: is_ubI)
        hence "is_lub ((widen1 P)\<^sup>*) (Class Object) A (Class Object)"
          by(auto simp add: is_lub_def dest: is_ubD)
        with acyclic_widen1[OF wf]
        have "exec_lub (widen1 P) (super P) A (Class Object) = Class Object"
          by(auto intro: exec_lub_conv superI)
        ultimately show "exec_lub (widen1 P) (super P) A B = Class Object" by simp
      qed
      with wf show ?thesis by(simp)
    next
      case False
      hence AnObject: "A \<noteq> Class Object"
        and BnObject: "B \<noteq> Class Object" by auto
      from widen_into_widen1_trancl[OF wf AObject AnObject ANT itA]
      have "P \<turnstile> A <\<^sup>* Class Object" by(rule trancl_into_rtrancl)
      moreover from widen_into_widen1_trancl[OF wf BObject BnObject BNT itB]
      have "P \<turnstile> B <\<^sup>* Class Object" by(rule trancl_into_rtrancl)
      ultimately have "is_lub ((widen1 P)\<^sup>*) A B (exec_lub (widen1 P) (super P) A B)"
        by(rule is_lub_exec_lub[OF single_valued_widen1[OF wf] acyclic_widen1[OF wf]])(auto intro: superI)
      hence Aew1: "P \<turnstile> A <\<^sup>* exec_lub (widen1 P) (super P) A B"
        by(auto simp add: is_lub_def dest!: is_ubD)
      thus ?thesis
      proof(rule rtranclE)
        assume "A = exec_lub (widen1 P) (super P) A B"
        with itA show ?thesis by simp
      next
        fix A'
        assume "P \<turnstile> A' <\<^sup>1 exec_lub (widen1 P) (super P) A B"
        thus ?thesis by(rule widen1_is_type[OF wf])
      qed
    qed }
  with is_class_Object[OF wf] sup itA itB show ?thesis unfolding sup_def
    by(cases "A = B")(auto split: if_split_asm simp add: exec_lub_refl)
qed

lemma closed_err_types:
  assumes wfP: "wf_prog wf_mb P"
  shows "closed (err (types P)) (lift2 (sup P))"
proof -
  { fix A B
    assume it: "is_type P A" "is_type P B"
      and "A \<noteq> NT" "B \<noteq> NT" "A \<noteq> B"
      and "is_refT A" "is_refT B"
    hence "is_type P (exec_lub (widen1 P) (super P) A B)"
      using sup_is_type[OF wfP it] by(simp add: sup_def) }
  with is_class_Object[OF wfP] show ?thesis
    unfolding closed_def plussub_def lift2_def sup_def'
    by(auto split: err.split ty.splits)(auto simp add: exec_lub_refl)
qed

lemma widen_into_widen1_rtrancl:
  "\<lbrakk>wf_prog wfmd P; widen P A B; A \<noteq> NT; is_type P A \<rbrakk> \<Longrightarrow> (A, B) \<in> (widen1 P)\<^sup>*"
by(cases "A = B")(auto intro: trancl_into_rtrancl widen_into_widen1_trancl)


lemma sup_widen_greater:
  assumes wfP: "wf_prog wf_mb P"
  and it1: "is_type P t1"
  and it2: "is_type P t2"
  and sup: "sup P t1 t2 = OK s"
  shows "widen P t1 s \<and> widen P t2 s"
proof -
  { assume t1: "is_refT t1"
      and t2: "is_refT t2"
      and t1NT: "t1 \<noteq> NT"
      and t2NT: "t2 \<noteq> NT"
    with it1 it2 wfP have "P \<turnstile> t1 \<le> Class Object" "P \<turnstile> t2 \<le> Class Object"
      by(auto intro: is_refType_widen_Object)
    with t1NT t2NT it1 it2
    have "P \<turnstile> t1 <\<^sup>* Class Object" "P \<turnstile> t2 <\<^sup>* Class Object"
      by(auto intro: widen_into_widen1_rtrancl[OF wfP])
    with single_valued_widen1[OF wfP]
    obtain u where "is_lub ((widen1 P)^*) t1 t2 u" 
      by (blast dest: single_valued_has_lubs)
    hence "P \<turnstile> t1 \<le> exec_lub (widen1 P) (super P) t1 t2 \<and>
           P \<turnstile> t2 \<le> exec_lub (widen1 P) (super P) t1 t2"
      using acyclic_widen1[OF wfP] superI[of _ _ P]
      by(simp add: exec_lub_conv)(blast dest: is_lubD is_ubD intro: widen1_rtrancl_into_widen) }
  with it1 it2 sup show ?thesis
    by (cases s) (auto simp add: sup_def split: if_split_asm elim: refTE)
qed

lemma sup_widen_smallest:
  assumes wfP: "wf_prog wf_mb P"
  and itT: "is_type P T"
  and itU: "is_type P U"
  and TwV: "P \<turnstile> T \<le> V"
  and UwV: "P \<turnstile> U \<le> V"
  and sup: "sup P T U = OK W"
  shows "widen P W V"
proof -
  { assume rT: "is_refT T"
      and rU: "is_refT U"
      and UNT: "U \<noteq> NT"
      and TNT: "T \<noteq> NT"
      and W: "exec_lub (widen1 P) (super P) T U = W"
    from itU itT rT rU UNT TNT have "P \<turnstile> T \<le> Class Object" "P \<turnstile> U \<le> Class Object"
      by(auto intro:is_refType_widen_Object[OF wfP])
    with UNT TNT itT itU
    have "P \<turnstile> T <\<^sup>* Class Object" "P \<turnstile> U <\<^sup>* Class Object"
      by(auto intro: widen_into_widen1_rtrancl[OF wfP])
    with single_valued_widen1[OF wfP]
    obtain X where lub: "is_lub ((widen1 P)^* ) T U X"
      by (blast dest: single_valued_has_lubs)   
    with acyclic_widen1[OF wfP]
    have "exec_lub (widen1 P) (super P) T U = X"
      by (blast intro: superI exec_lub_conv)
    also from TwV TNT UwV UNT itT itU have "P \<turnstile> T <\<^sup>* V" "P \<turnstile> U <\<^sup>* V"
      by(auto intro: widen_into_widen1_rtrancl[OF wfP])
    with lub have "P \<turnstile> X <\<^sup>* V"
      by (clarsimp simp add: is_lub_def is_ub_def)
    finally have "P \<turnstile> exec_lub (widen1 P) (super P) T U \<le> V"
      by(rule widen1_rtrancl_into_widen)
    with W have "P \<turnstile> W \<le> V" by simp }
  with sup itT itU TwV UwV show ?thesis
    by(simp add: sup_def split: if_split_asm)
qed

lemma sup_exists:
  "\<lbrakk> widen P a c; widen P b c \<rbrakk> \<Longrightarrow> \<exists>T. sup P a b = OK T"
by(cases b a rule: ty.exhaust[case_product ty.exhaust])(auto simp add: sup_def)

lemma err_semilat_JType_esl:
  assumes wf_prog: "wf_prog wf_mb P"
  shows "err_semilat (esl P)"
proof -
  from wf_prog have "order (widen P)" ..
  moreover from wf_prog
  have "closed (err (types P)) (lift2 (sup P))"
    by (rule closed_err_types)
  moreover
  from wf_prog have
    "(\<forall>x\<in>err (types P). \<forall>y\<in>err (types P). x \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> x \<squnion>\<^bsub>lift2 (sup P)\<^esub> y) \<and> 
     (\<forall>x\<in>err (types P). \<forall>y\<in>err (types P). y \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> x \<squnion>\<^bsub>lift2 (sup P)\<^esub> y)"
    by(auto simp add: lesub_def plussub_def Err.le_def lift2_def sup_widen_greater split: err.split)
  moreover from wf_prog have
    "\<forall>x\<in>err (types P). \<forall>y\<in>err (types P). \<forall>z\<in>err (types P). 
    x \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> z \<and> y \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> z \<longrightarrow> x \<squnion>\<^bsub>lift2 (sup P)\<^esub> y \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> z"
    unfolding lift2_def plussub_def lesub_def Err.le_def
    by(auto intro: sup_widen_smallest dest:sup_exists simp add: split: err.split)
  ultimately show ?thesis by (simp add: esl_def semilat_def sl_def Err.sl_def)
qed

subsection \<open>Relation between @{term "sup P T U = OK V"} and @{term "P \<turnstile> lub(T, U) = V"}\<close>

lemma sup_is_lubI:
  assumes wf: "wf_prog wf_md P"
  and it: "is_type P T" "is_type P U"
  and sup: "sup P T U = OK V"
  shows "P \<turnstile> lub(T, U) = V"
proof 
  from sup_widen_greater[OF wf it sup]
  show "P \<turnstile> T \<le> V" "P \<turnstile> U \<le> V" by blast+
next
  fix T'
  assume "P \<turnstile> T \<le> T'" "P \<turnstile> U \<le> T'"
  thus "P \<turnstile> V \<le> T'" using sup by(rule sup_widen_smallest[OF wf it])
qed

lemma is_lub_subD:
  assumes wf: "wf_prog wf_md P"
  and it: "is_type P T" "is_type P U"
  and lub: "P \<turnstile> lub(T, U) = V"
  shows "sup P T U = OK V"
proof -
  from lub have "P \<turnstile> T \<le> V" "P \<turnstile> U \<le> V" by(blast dest: is_lub_upper)+
  from sup_exists[OF this] obtain W where "sup P T U = OK W" by blast
  moreover
  with wf it have "P \<turnstile> lub(T, U) = W" by(rule sup_is_lubI)
  with lub have "V = W" by(auto dest: is_lub_unique[OF wf])
  ultimately show ?thesis by simp
qed

lemma is_lub_is_type:
  "\<lbrakk> wf_prog wf_md P; is_type P T; is_type P U; P \<turnstile> lub(T, U) = V \<rbrakk> \<Longrightarrow> is_type P V"
by(frule (3) is_lub_subD)(erule (3) sup_is_type)

subsection \<open>Code generator setup\<close>

code_pred widen1p .
lemmas [code] = widen1_def

lemma eval_widen1p_i_i_o_conv:
  "Predicate.eval (widen1p_i_i_o P T) = (\<lambda>U. P \<turnstile> T <\<^sup>1 U)"
by(auto elim: widen1p_i_i_oE intro: widen1p_i_i_oI simp add: widen1_def fun_eq_iff)

lemma rtrancl_widen1_code [code_unfold]:
  "(widen1 P)^* = {(a, b). Predicate.holds (rtrancl_tab_FioB_i_i_i (widen1p_i_i_o P) [] a b)}"
by(auto simp add: fun_eq_iff Predicate.holds_eq widen1_def rtrancl_def rtranclp_eq_rtrancl_tab_nil eval_widen1p_i_i_o_conv intro!: rtrancl_tab_FioB_i_i_iI elim!: rtrancl_tab_FioB_i_i_iE)

declare exec_lub_def [code_unfold]

end

