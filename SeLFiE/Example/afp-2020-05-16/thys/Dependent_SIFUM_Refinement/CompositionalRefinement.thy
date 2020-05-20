(*
Title: Value-Dependent SIFUM Refinement
Authors: Toby Murray, Robert Sison
*)
theory CompositionalRefinement
imports Dependent_SIFUM_Type_Systems.Compositionality
begin


lemma inj_card_le: 
  "inj (f::'a \<Rightarrow> 'b) \<Longrightarrow> finite (UNIV::'b set) \<Longrightarrow> card (UNIV::'a set) \<le> card (UNIV::'b set)"
  by (blast intro: card_inj_on_le)

text \<open>
  We define a generic locale for capturing refinement between an abstract and a concrete
  program. We then define and prove sufficient, conditions that preserve local security
  from the abstract to the concrete program.

  Below we define a second locale that is more restrictive than this one. Specifically, this
  one allows the concrete program to have extra variables not present in the abstract one.
  These variables might be used, for instance, to implement a runtime stack that was implicit
  in the semantics of the abstract program; or as temporary storage for expression evaluation
  that may (appear to be) atomic in the abstract semantics.

  The simpler locale below forbids extra variables in the concrete program, making the
  necessary conditions for preservation of local security simpler.
\<close>
locale sifum_refinement = 
  abs: sifum_security dma\<^sub>A \<C>_vars\<^sub>A \<C>\<^sub>A eval\<^sub>A some_val +
  conc: sifum_security dma\<^sub>C \<C>_vars\<^sub>C \<C>\<^sub>C eval\<^sub>C some_val
  for dma\<^sub>A :: "('Var\<^sub>A,'Val) Mem \<Rightarrow> 'Var\<^sub>A \<Rightarrow> Sec"
  and dma\<^sub>C :: "('Var\<^sub>C,'Val) Mem \<Rightarrow> 'Var\<^sub>C \<Rightarrow> Sec"
  and \<C>_vars\<^sub>A :: "'Var\<^sub>A \<Rightarrow> 'Var\<^sub>A set"
  and \<C>_vars\<^sub>C :: "'Var\<^sub>C \<Rightarrow> 'Var\<^sub>C set"
  and \<C>\<^sub>A :: "'Var\<^sub>A set"
  and \<C>\<^sub>C :: "'Var\<^sub>C set"
  and eval\<^sub>A :: "('Com\<^sub>A, 'Var\<^sub>A, 'Val) LocalConf rel"
  and eval\<^sub>C :: "('Com\<^sub>C, 'Var\<^sub>C, 'Val) LocalConf rel"
  and some_val :: "'Val" +
  fixes var\<^sub>C_of :: "'Var\<^sub>A \<Rightarrow> 'Var\<^sub>C"
  assumes var\<^sub>C_of_inj: "inj var\<^sub>C_of" 
  assumes dma_consistent:
    "dma\<^sub>A (\<lambda>x\<^sub>A. mem\<^sub>C (var\<^sub>C_of x\<^sub>A)) x\<^sub>A = dma\<^sub>C mem\<^sub>C (var\<^sub>C_of x\<^sub>A)"
  assumes \<C>_vars_consistent:
    "(var\<^sub>C_of ` \<C>_vars\<^sub>A x\<^sub>A) = \<C>_vars\<^sub>C (var\<^sub>C_of x\<^sub>A)"
  (* we make the (reasonable IMHO) assumption that the only control variables
     are user-declared and so that the compiler won't introduce new ones. *)
  assumes control_vars_are_A_vars:
    "\<C>\<^sub>C = var\<^sub>C_of ` \<C>\<^sub>A"

section "General Compositional Refinement"

text \<open>
  The type of state relations between the abstract and compiled components.
  The job of a certifying compiler will be to exhibit one of these for each
  component it compiles. Below we'll define the conditions that such a
  relation needs to satisfy to give compositional refinement.
\<close>
type_synonym ('Com\<^sub>A, 'Var\<^sub>A, 'Val, 'Com\<^sub>C, 'Var\<^sub>C) state_relation = 
   "(('Com\<^sub>A, 'Var\<^sub>A, 'Val) LocalConf \<times> ('Com\<^sub>C, 'Var\<^sub>C, 'Val) LocalConf) set"

context sifum_refinement begin

abbreviation 
  conf_abv\<^sub>A :: "'Com\<^sub>A \<Rightarrow> 'Var\<^sub>A Mds \<Rightarrow> ('Var\<^sub>A, 'Val) Mem \<Rightarrow> (_,_,_) LocalConf"
  ("\<langle>_, _, _\<rangle>\<^sub>A" [0, 0, 0] 1000)
where
  "\<langle> c, mds, mem \<rangle>\<^sub>A \<equiv> ((c, mds), mem)"

abbreviation 
  conf_abv\<^sub>C :: "'Com\<^sub>C \<Rightarrow> 'Var\<^sub>C Mds \<Rightarrow> ('Var\<^sub>C, 'Val) Mem \<Rightarrow> (_,_,_) LocalConf"
  ("\<langle>_, _, _\<rangle>\<^sub>C" [0, 0, 0] 1000)
where
  "\<langle> c, mds, mem \<rangle>\<^sub>C \<equiv> ((c, mds), mem)"

abbreviation 
  eval_abv\<^sub>A :: "('Com\<^sub>A, 'Var\<^sub>A, 'Val) LocalConf \<Rightarrow> (_, _, _) LocalConf \<Rightarrow> bool"
  (infixl "\<leadsto>\<^sub>A" 70)
 where
  "x \<leadsto>\<^sub>A y \<equiv> (x, y) \<in> eval\<^sub>A"

abbreviation 
  eval_abv\<^sub>C :: "('Com\<^sub>C, 'Var\<^sub>C, 'Val) LocalConf \<Rightarrow> (_, _, _) LocalConf \<Rightarrow> bool"
  (infixl "\<leadsto>\<^sub>C" 70)
where
  "x \<leadsto>\<^sub>C y \<equiv> (x, y) \<in> eval\<^sub>C"

definition
  preserves_modes_mem :: "('Com\<^sub>A, 'Var\<^sub>A, 'Val, 'Com\<^sub>C, 'Var\<^sub>C) state_relation \<Rightarrow> bool"
where
  "preserves_modes_mem \<R> \<equiv> 
  (\<forall> c\<^sub>A mds\<^sub>A mem\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>C. (\<langle> c\<^sub>A, mds\<^sub>A, mem\<^sub>A \<rangle>\<^sub>A, \<langle> c\<^sub>C, mds\<^sub>C, mem\<^sub>C \<rangle>\<^sub>C) \<in> \<R> \<longrightarrow>
      (\<forall>x\<^sub>A. (mem\<^sub>A x\<^sub>A) = (mem\<^sub>C (var\<^sub>C_of x\<^sub>A))) \<and>
      (\<forall>m. var\<^sub>C_of ` mds\<^sub>A m = (range var\<^sub>C_of) \<inter> mds\<^sub>C m))"

definition
  mem\<^sub>A_of :: "('Var\<^sub>C, 'Val) Mem \<Rightarrow> ('Var\<^sub>A, 'Val) Mem"
where
  "mem\<^sub>A_of mem\<^sub>C \<equiv>  (\<lambda>x\<^sub>A. (mem\<^sub>C (var\<^sub>C_of x\<^sub>A)))"
  
definition
  mds\<^sub>A_of :: "'Var\<^sub>C Mds \<Rightarrow> 'Var\<^sub>A Mds"
where
  "mds\<^sub>A_of mds\<^sub>C \<equiv> (\<lambda> m. (inv var\<^sub>C_of) ` (range var\<^sub>C_of \<inter> mds\<^sub>C m))"

lemma low_mds_eq_from_conc_to_abs:
  "conc.low_mds_eq mds mem mem' \<Longrightarrow> abs.low_mds_eq (mds\<^sub>A_of mds) (mem\<^sub>A_of mem) (mem\<^sub>A_of mem')"
  apply(clarsimp simp: abs.low_mds_eq_def conc.low_mds_eq_def mem\<^sub>A_of_def mds\<^sub>A_of_def)
  using var\<^sub>C_of_inj 
  by (metis IntI control_vars_are_A_vars dma_consistent image_eqI inv_f_f rangeI)

definition
  var\<^sub>A_of :: "'Var\<^sub>C \<Rightarrow> 'Var\<^sub>A"
where
  "var\<^sub>A_of \<equiv> inv var\<^sub>C_of"

lemma preserves_modes_mem_mem\<^sub>A_simp:
  "(\<forall>x\<^sub>A. (mem\<^sub>A x\<^sub>A) = (mem\<^sub>C (var\<^sub>C_of x\<^sub>A))) \<Longrightarrow>
      mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C"
  unfolding mem\<^sub>A_of_def by blast


lemma preserves_modes_mem_mds\<^sub>A_simp:
  "(\<forall>m. var\<^sub>C_of ` mds\<^sub>A m = range (var\<^sub>C_of) \<inter> mds\<^sub>C m) \<Longrightarrow>
      mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C"
  unfolding mds\<^sub>A_of_def
  apply(rule ext)
  apply(drule_tac x=m in spec)
  apply(rule equalityI)
   apply clarsimp
   apply(rename_tac x\<^sub>A)
   apply(drule equalityD1)
   apply(drule_tac c="var\<^sub>C_of x\<^sub>A" in subsetD)
    apply blast
   unfolding image_def
   apply clarsimp
   apply(rule_tac x="var\<^sub>C_of x\<^sub>A" in bexI)
    apply(rule sym)
    apply(rule inv_f_f[OF var\<^sub>C_of_inj])
   apply(drule inj_onD[OF var\<^sub>C_of_inj])
   apply blast+
  apply clarsimp
  apply(rename_tac x\<^sub>A)
  apply(simp add: inv_f_f[OF var\<^sub>C_of_inj])
  apply(drule equalityD2)
  apply(drule_tac c="var\<^sub>C_of x\<^sub>A" in subsetD)
   apply blast
  apply clarsimp
  apply(drule inj_onD[OF var\<^sub>C_of_inj])
  apply blast+
  done

text \<open>
  This version might be more useful. Not sure yet.
\<close>
lemma preserves_modes_mem_def2:
  "preserves_modes_mem \<R> =
  (\<forall> c\<^sub>A mds\<^sub>A mem\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>C. (\<langle> c\<^sub>A, mds\<^sub>A, mem\<^sub>A \<rangle>\<^sub>A, \<langle> c\<^sub>C, mds\<^sub>C, mem\<^sub>C \<rangle>\<^sub>C) \<in> \<R> \<longrightarrow>
      mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C \<and>
      mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C)"
  unfolding preserves_modes_mem_def
  apply(rule iffI)
   apply(blast dest: preserves_modes_mem_mem\<^sub>A_simp preserves_modes_mem_mds\<^sub>A_simp)
  apply safe
     apply(elim allE impE, assumption, elim conjE)
     apply(simp add: mem\<^sub>A_of_def)
    apply blast
   apply clarsimp
   apply(rename_tac x\<^sub>A)
   apply(elim allE impE, assumption, elim conjE)
   apply clarsimp
   apply(clarsimp simp: mds\<^sub>A_of_def image_def)
   apply(simp add: inv_f_f[OF var\<^sub>C_of_inj])
  apply clarsimp
  apply(rename_tac x\<^sub>A)
  apply(rule imageI)
  apply(elim allE impE, assumption, elim conjE)
  apply(clarsimp simp: mds\<^sub>A_of_def)
  apply(subst image_def)
  apply clarify
  apply(rule_tac x="var\<^sub>C_of x\<^sub>A" in bexI)
   apply(simp add: inv_f_f[OF var\<^sub>C_of_inj])
  apply blast
  done

definition
  closed_others :: "('Com\<^sub>A, 'Var\<^sub>A, 'Val, 'Com\<^sub>C, 'Var\<^sub>C) state_relation \<Rightarrow> bool"
where
  "closed_others \<R> \<equiv> 
  (\<forall> c\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>C mem\<^sub>C'. (\<langle> c\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C \<rangle>\<^sub>A, \<langle> c\<^sub>C, mds\<^sub>C, mem\<^sub>C \<rangle>\<^sub>C) \<in> \<R> \<longrightarrow>
   (\<forall>x. mem\<^sub>C x \<noteq> mem\<^sub>C' x \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x) \<longrightarrow>
   (\<forall>x. dma\<^sub>C mem\<^sub>C x \<noteq> dma\<^sub>C mem\<^sub>C' x \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x) \<longrightarrow>
         (\<langle> c\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C' \<rangle>\<^sub>A, \<langle> c\<^sub>C, mds\<^sub>C, mem\<^sub>C' \<rangle>\<^sub>C) \<in> \<R>)"

definition
  stops\<^sub>C :: "('Com\<^sub>C, 'Var\<^sub>C, 'Val) LocalConf \<Rightarrow> bool"
where
  "stops\<^sub>C c \<equiv> \<forall>c'. \<not> (c \<leadsto>\<^sub>C c')"

lemmas neval_induct = abs.neval.induct[consumes 1, case_names Zero Suc]

(* FIXME: move to Security.thy or similar *)
lemma strong_low_bisim_neval':
  "abs.neval c\<^sub>1 n c\<^sub>n \<Longrightarrow> (c\<^sub>1,c\<^sub>1') \<in> \<R>\<^sub>A \<Longrightarrow> snd (fst c\<^sub>1) = snd (fst c\<^sub>1') \<Longrightarrow> abs.strong_low_bisim_mm \<R>\<^sub>A \<Longrightarrow>
  \<exists>c\<^sub>n'. abs.neval c\<^sub>1' n c\<^sub>n' \<and> (c\<^sub>n,c\<^sub>n') \<in> \<R>\<^sub>A \<and> snd (fst c\<^sub>n) = snd (fst (c\<^sub>n'))"
proof(induct  arbitrary: c\<^sub>1' rule: neval_induct)
  case (Zero c\<^sub>1 c\<^sub>n)
   hence "abs.neval c\<^sub>1' 0 c\<^sub>1' \<and> (c\<^sub>n, c\<^sub>1') \<in> \<R>\<^sub>A \<and> snd (fst c\<^sub>n) = snd (fst c\<^sub>1')"
     by(blast intro: abs.neval.intros(1))
   thus ?case by blast
next
  case (Suc lc\<^sub>0 lc\<^sub>1 n lc\<^sub>n lc\<^sub>0')
  obtain c\<^sub>0 mds\<^sub>0 mem\<^sub>0 
  where [simp]: "lc\<^sub>0 = \<langle>c\<^sub>0, mds\<^sub>0, mem\<^sub>0\<rangle>\<^sub>A" by (case_tac lc\<^sub>0, auto)
  obtain c\<^sub>1 mds\<^sub>1 mem\<^sub>1 
  where [simp]: "lc\<^sub>1 = \<langle>c\<^sub>1, mds\<^sub>1, mem\<^sub>1\<rangle>\<^sub>A" by (case_tac lc\<^sub>1, auto)
  from \<open>snd (fst lc\<^sub>0) = snd (fst lc\<^sub>0')\<close> obtain c\<^sub>0' mem\<^sub>0'
  where [simp]: "lc\<^sub>0' = \<langle>c\<^sub>0', mds\<^sub>0, mem\<^sub>0'\<rangle>\<^sub>A" by (case_tac lc\<^sub>0', auto)
  
  from \<open>(lc\<^sub>0, lc\<^sub>0') \<in> \<R>\<^sub>A\<close>[simplified] \<open>lc\<^sub>0 \<leadsto>\<^sub>A lc\<^sub>1\<close>[simplified] \<open>abs.strong_low_bisim_mm \<R>\<^sub>A\<close>
  obtain c\<^sub>1' mem\<^sub>1' where a: "\<langle>c\<^sub>0',mds\<^sub>0, mem\<^sub>0'\<rangle>\<^sub>A \<leadsto>\<^sub>A \<langle>c\<^sub>1',mds\<^sub>1, mem\<^sub>1'\<rangle>\<^sub>A" and 
          b: "(\<langle>c\<^sub>1,mds\<^sub>1,mem\<^sub>1\<rangle>\<^sub>A,\<langle>c\<^sub>1',mds\<^sub>1, mem\<^sub>1'\<rangle>\<^sub>A) \<in> \<R>\<^sub>A"
    unfolding abs.strong_low_bisim_mm_def
    by blast

  from this Suc.hyps Suc(6) obtain lc\<^sub>S' where "abs.neval \<langle>c\<^sub>1',mds\<^sub>1,mem\<^sub>1'\<rangle>\<^sub>A n lc\<^sub>S'" and "(lc\<^sub>n, lc\<^sub>S') \<in> \<R>\<^sub>A" and "snd (fst lc\<^sub>n) = snd (fst lc\<^sub>S')"
    by force
  with Suc this a b show ?case by(fastforce intro: abs.neval.intros(2))
qed

lemma strong_low_bisim_neval:
  "abs.neval \<langle>c\<^sub>1,mds\<^sub>1,mem\<^sub>1\<rangle>\<^sub>A n \<langle>c\<^sub>n,mds\<^sub>n,mem\<^sub>n\<rangle>\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>1,mds\<^sub>1,mem\<^sub>1\<rangle>\<^sub>A,\<langle>c\<^sub>1',mds\<^sub>1,mem\<^sub>1'\<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<Longrightarrow> abs.strong_low_bisim_mm \<R>\<^sub>A \<Longrightarrow>
  \<exists>c\<^sub>n' mem\<^sub>n'. abs.neval \<langle>c\<^sub>1',mds\<^sub>1,mem\<^sub>1'\<rangle>\<^sub>A n \<langle>c\<^sub>n',mds\<^sub>n,mem\<^sub>n'\<rangle>\<^sub>A \<and> (\<langle>c\<^sub>n,mds\<^sub>n,mem\<^sub>n\<rangle>\<^sub>A,\<langle>c\<^sub>n',mds\<^sub>n,mem\<^sub>n'\<rangle>\<^sub>A) \<in> \<R>\<^sub>A"
  by(drule strong_low_bisim_neval', simp+)

lemma in_\<R>_dma':
  assumes preserves: "preserves_modes_mem \<R>"
  assumes in_\<R>: "(\<langle>c\<^sub>A,mds\<^sub>A,mem\<^sub>A\<rangle>\<^sub>A,\<langle>c\<^sub>C,mds\<^sub>C,mem\<^sub>C\<rangle>\<^sub>C) \<in> \<R>"
  shows  "dma\<^sub>A mem\<^sub>A x\<^sub>A = dma\<^sub>C mem\<^sub>C (var\<^sub>C_of x\<^sub>A)"
proof -
  from assms have
    mds\<^sub>A_def: "mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C" and  
    mem\<^sub>A_def: "mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C"
    unfolding preserves_modes_mem_def2 by blast+
  
  have "dma\<^sub>A (mem\<^sub>A_of mem\<^sub>C) x\<^sub>A = dma\<^sub>C mem\<^sub>C (var\<^sub>C_of x\<^sub>A)"
    unfolding mem\<^sub>A_of_def
    by(rule dma_consistent)
  
  thus ?thesis
    by(simp add: mem\<^sub>A_def)
qed

lemma in_\<R>_dma:
  assumes preserves: "preserves_modes_mem \<R>"
  assumes in_\<R>: "(\<langle>c\<^sub>A,mds\<^sub>A,mem\<^sub>A\<rangle>\<^sub>A,\<langle>c\<^sub>C,mds\<^sub>C,mem\<^sub>C\<rangle>\<^sub>C) \<in> \<R>"
  shows  "dma\<^sub>A mem\<^sub>A = (dma\<^sub>C mem\<^sub>C \<circ> var\<^sub>C_of)"
  unfolding o_def
  using assms by(blast intro: in_\<R>_dma')


definition
  new_vars_private ::  "('Com\<^sub>A, 'Var\<^sub>A, 'Val, 'Com\<^sub>C, 'Var\<^sub>C) state_relation \<Rightarrow> bool"
where
  "new_vars_private \<R> \<equiv>
  (\<forall> c\<^sub>1\<^sub>A mds\<^sub>A mem\<^sub>1\<^sub>A c\<^sub>1\<^sub>C mds\<^sub>C mem\<^sub>1\<^sub>C. 
   (\<langle> c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C) \<in> \<R> \<longrightarrow>
    (\<forall> c\<^sub>1\<^sub>C' mds\<^sub>C' mem\<^sub>1\<^sub>C'. \<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C \<longrightarrow>
     (\<forall>v\<^sub>C. (mem\<^sub>1\<^sub>C' v\<^sub>C \<noteq> mem\<^sub>1\<^sub>C v\<^sub>C \<or> dma\<^sub>C mem\<^sub>1\<^sub>C' v\<^sub>C < dma\<^sub>C mem\<^sub>1\<^sub>C v\<^sub>C) \<and> v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite) \<and>
     (mds\<^sub>C AsmNoReadOrWrite - (range var\<^sub>C_of)) \<subseteq> (mds\<^sub>C' AsmNoReadOrWrite - (range var\<^sub>C_of))))"

lemma not_less_eq_is_greater_Sec:
  "(\<not> a \<le> (b::Sec)) = (a > b)"
  unfolding less_Sec_def less_eq_Sec_def using Sec.exhaust by blast

lemma doesnt_have_mode:
  "(x \<notin> mds\<^sub>A_of mds\<^sub>C m) = (var\<^sub>C_of x \<notin> mds\<^sub>C m)"
  apply(clarsimp simp: mds\<^sub>A_of_def image_def)
  apply(rule iffI)
   apply clarsimp
   apply(drule_tac x="var\<^sub>C_of x" in bspec)
    apply blast
   apply(simp add: inv_f_f[OF var\<^sub>C_of_inj])
  apply(clarify)
  apply(simp add: inv_f_f[OF var\<^sub>C_of_inj])
  done

lemma new_vars_private_does_the_thing:
  assumes nice: "new_vars_private \<R>"
  assumes in_\<R>\<^sub>1: "(\<langle> c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C) \<in> \<R>"
  assumes in_\<R>\<^sub>2: "(\<langle> c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C \<rangle>\<^sub>A, \<langle> c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C \<rangle>\<^sub>C) \<in> \<R>"
  assumes step\<^sub>1\<^sub>C: "\<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C"
  assumes step\<^sub>2\<^sub>C: "\<langle> c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C \<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle> c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C' \<rangle>\<^sub>C"
  assumes low_mds_eq\<^sub>C: "conc.low_mds_eq mds\<^sub>C mem\<^sub>1\<^sub>C mem\<^sub>2\<^sub>C"
  assumes low_mds_eq\<^sub>A': "abs.low_mds_eq (mds\<^sub>A_of mds\<^sub>C') (mem\<^sub>A_of mem\<^sub>1\<^sub>C') (mem\<^sub>A_of mem\<^sub>2\<^sub>C')" 
  shows "conc.low_mds_eq mds\<^sub>C' mem\<^sub>1\<^sub>C' mem\<^sub>2\<^sub>C'"
  unfolding conc.low_mds_eq_def
proof(clarify)
  let ?mem\<^sub>1\<^sub>A = "mem\<^sub>A_of mem\<^sub>1\<^sub>C"
  let ?mem\<^sub>2\<^sub>A = "mem\<^sub>A_of mem\<^sub>2\<^sub>C"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  let ?mem\<^sub>2\<^sub>A' = "mem\<^sub>A_of mem\<^sub>2\<^sub>C'"
  let ?mds\<^sub>A = "mds\<^sub>A_of mds\<^sub>C"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  fix x\<^sub>C
  assume is_Low\<^sub>C': "dma\<^sub>C mem\<^sub>1\<^sub>C' x\<^sub>C = Low"
  assume is_readable\<^sub>C': "x\<^sub>C \<in> \<C>\<^sub>C \<or> x\<^sub>C \<notin> mds\<^sub>C' AsmNoReadOrWrite"
  show "mem\<^sub>1\<^sub>C' x\<^sub>C = mem\<^sub>2\<^sub>C' x\<^sub>C"
  proof(cases "dma\<^sub>C mem\<^sub>1\<^sub>C' x\<^sub>C \<ge> dma\<^sub>C mem\<^sub>1\<^sub>C x\<^sub>C \<and> mem\<^sub>1\<^sub>C' x\<^sub>C = mem\<^sub>1\<^sub>C x\<^sub>C \<and> mem\<^sub>2\<^sub>C' x\<^sub>C = mem\<^sub>2\<^sub>C x\<^sub>C \<and> (x\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite \<longrightarrow> x\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite)")
    assume easy: "dma\<^sub>C mem\<^sub>1\<^sub>C' x\<^sub>C \<ge> dma\<^sub>C mem\<^sub>1\<^sub>C x\<^sub>C \<and> mem\<^sub>1\<^sub>C' x\<^sub>C = mem\<^sub>1\<^sub>C x\<^sub>C \<and> mem\<^sub>2\<^sub>C' x\<^sub>C = mem\<^sub>2\<^sub>C x\<^sub>C \<and> (x\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite \<longrightarrow> x\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite)"
    with is_Low\<^sub>C' have is_Low\<^sub>C: "dma\<^sub>C mem\<^sub>1\<^sub>C x\<^sub>C = Low" by (simp add: less_eq_Sec_def)
    from easy is_readable\<^sub>C' have is_readable\<^sub>C: "x\<^sub>C \<in> \<C>\<^sub>C \<or> x\<^sub>C \<notin> mds\<^sub>C AsmNoReadOrWrite" by blast
    from is_Low\<^sub>C is_readable\<^sub>C low_mds_eq\<^sub>C have "mem\<^sub>1\<^sub>C x\<^sub>C = mem\<^sub>2\<^sub>C x\<^sub>C"
      unfolding conc.low_mds_eq_def by blast
    with easy show ?thesis by metis
  next
    assume a: "\<not> (dma\<^sub>C mem\<^sub>1\<^sub>C x\<^sub>C \<le> dma\<^sub>C mem\<^sub>1\<^sub>C' x\<^sub>C \<and>
       mem\<^sub>1\<^sub>C' x\<^sub>C = mem\<^sub>1\<^sub>C x\<^sub>C \<and>
       mem\<^sub>2\<^sub>C' x\<^sub>C = mem\<^sub>2\<^sub>C x\<^sub>C \<and> (x\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite \<longrightarrow> x\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite))"
    hence a_disj: "(dma\<^sub>C mem\<^sub>1\<^sub>C x\<^sub>C > dma\<^sub>C mem\<^sub>1\<^sub>C' x\<^sub>C \<or>
       mem\<^sub>1\<^sub>C' x\<^sub>C \<noteq> mem\<^sub>1\<^sub>C x\<^sub>C \<or>
       mem\<^sub>2\<^sub>C' x\<^sub>C \<noteq> mem\<^sub>2\<^sub>C x\<^sub>C \<or> (x\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite \<and> x\<^sub>C \<notin> mds\<^sub>C' AsmNoReadOrWrite))"
       using not_less_eq_is_greater_Sec by blast
    show "mem\<^sub>1\<^sub>C' x\<^sub>C = mem\<^sub>2\<^sub>C' x\<^sub>C"
    proof(cases "x\<^sub>C \<in> range var\<^sub>C_of")
      assume C_only_var: "x\<^sub>C \<notin> range var\<^sub>C_of"
      with in_\<R>\<^sub>1 step\<^sub>1\<^sub>C nice
      have "(mem\<^sub>1\<^sub>C' x\<^sub>C \<noteq> mem\<^sub>1\<^sub>C x\<^sub>C \<or> dma\<^sub>C mem\<^sub>1\<^sub>C' x\<^sub>C < dma\<^sub>C mem\<^sub>1\<^sub>C x\<^sub>C) \<longrightarrow> x\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite"
        unfolding new_vars_private_def  by blast
      moreover from C_only_var in_\<R>\<^sub>2 step\<^sub>2\<^sub>C nice have "(mem\<^sub>2\<^sub>C' x\<^sub>C \<noteq> mem\<^sub>2\<^sub>C x\<^sub>C) \<longrightarrow> x\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite"
        unfolding new_vars_private_def by blast
      moreover from C_only_var in_\<R>\<^sub>1 step\<^sub>1\<^sub>C nice have "x\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite \<longrightarrow> x\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite" unfolding new_vars_private_def by blast
      moreover from C_only_var is_readable\<^sub>C' have "x\<^sub>C \<notin> mds\<^sub>C' AsmNoReadOrWrite"
        using control_vars_are_A_vars by blast
      ultimately have False using a_disj by blast
      thus ?thesis by blast
    next
      assume in_val\<^sub>C_of: "x\<^sub>C \<in> range var\<^sub>C_of"
      from this obtain x\<^sub>A where x\<^sub>C_def: "x\<^sub>C = var\<^sub>C_of x\<^sub>A" by blast
      from is_Low\<^sub>C' have is_Low\<^sub>A': "dma\<^sub>A ?mem\<^sub>1\<^sub>A' x\<^sub>A = Low"
        using dma_consistent unfolding mem\<^sub>A_of_def x\<^sub>C_def by force
      from is_readable\<^sub>C' have is_readable\<^sub>A': "x\<^sub>A \<in> \<C>\<^sub>A \<or> x\<^sub>A \<notin> ?mds\<^sub>A' AsmNoReadOrWrite"
        using control_vars_are_A_vars x\<^sub>C_def doesnt_have_mode[symmetric] var\<^sub>C_of_inj inj_image_mem_iff by fast
      with is_Low\<^sub>A' low_mds_eq\<^sub>A' have x\<^sub>A_eq': "?mem\<^sub>1\<^sub>A' x\<^sub>A = ?mem\<^sub>2\<^sub>A' x\<^sub>A" 
        unfolding abs.low_mds_eq_def by blast
      thus ?thesis by(simp add: mem\<^sub>A_of_def x\<^sub>C_def)
    qed
  qed
qed

  
text \<open>
  Perhaps surprisingly, we don't necessarily 
  care whether the refinement preserves
  termination or divergence behaviour from the source to the target program.
  It can do whatever it likes, so long as it transforms two source programs
  that are low bisimilar (i.e. perform the same low actions at the 
  same time), into two target ones that perform the same low actions at the
  same time.

  Having the concrete step correspond to zero abstract ones is like expanding
  abstract code out (think e.g. of side-effect free expression evaluation).
  Having the concrete step correspond to more than one abstract step is
  like optimising out abstract code. But importantly, the optimisation needs
  to look the same for abstract-bisimilar code.

  Additionally, we allow the instantiation of this theory to supply
  an arbitrary predicate that can be used to restrict our consideration to
  pairs of concrete steps that correspond to each other in terms of progress.
  This is particularly important for distinguishing between multiple concrete
  steps derived from the expansion of a single abstract step.
\<close>
definition
  secure_refinement :: "('Com\<^sub>A, 'Var\<^sub>A, 'Val) LocalConf rel \<Rightarrow> ('Com\<^sub>A, 'Var\<^sub>A, 'Val, 'Com\<^sub>C, 'Var\<^sub>C) state_relation \<Rightarrow> 
                          ('Com\<^sub>C, 'Var\<^sub>C, 'Val) LocalConf rel \<Rightarrow> bool"
where
  "secure_refinement \<R>\<^sub>A \<R> P \<equiv>
  closed_others \<R> \<and>
  preserves_modes_mem \<R> \<and>
  new_vars_private \<R> \<and>
  conc.closed_glob_consistent P \<and>
  (\<forall> c\<^sub>1\<^sub>A mds\<^sub>A mem\<^sub>1\<^sub>A c\<^sub>1\<^sub>C mds\<^sub>C mem\<^sub>1\<^sub>C. 
   (\<langle> c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C) \<in> \<R> \<longrightarrow>
    (\<forall> c\<^sub>1\<^sub>C' mds\<^sub>C' mem\<^sub>1\<^sub>C'. \<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C \<longrightarrow>
     (\<exists> n c\<^sub>1\<^sub>A' mds\<^sub>A' mem\<^sub>1\<^sub>A'. abs.neval \<langle> c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A \<rangle>\<^sub>A n \<langle> c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A' \<rangle>\<^sub>A \<and>
                   (\<langle> c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A' \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C) \<in> \<R> \<and>
       (\<forall>c\<^sub>2\<^sub>A mem\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'. 
         (\<langle> c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A \<rangle>\<^sub>A, \<langle> c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A \<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<and>
         (\<langle> c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A \<rangle>\<^sub>A, \<langle> c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C \<rangle>\<^sub>C) \<in> \<R> \<and>
         (\<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C, \<langle> c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C \<rangle>\<^sub>C) \<in> P \<and>
         abs.neval \<langle> c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A \<rangle>\<^sub>A n \<langle> c\<^sub>2\<^sub>A', mds\<^sub>A', mem\<^sub>2\<^sub>A' \<rangle>\<^sub>A  \<longrightarrow>
           (\<exists> c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'. \<langle> c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C \<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle> c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C' \<rangle>\<^sub>C \<and>
                   (\<langle> c\<^sub>2\<^sub>A', mds\<^sub>A', mem\<^sub>2\<^sub>A' \<rangle>\<^sub>A, \<langle> c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C' \<rangle>\<^sub>C) \<in> \<R> \<and>
                   (\<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C, \<langle> c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C' \<rangle>\<^sub>C) \<in> P)))))"

lemma preserves_modes_memD:
  "\<lbrakk>preserves_modes_mem \<R>; (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> \<R>\<rbrakk> \<Longrightarrow> mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C \<and> mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C"
  using preserves_modes_mem_def2 by blast

lemma secure_refinement_def2:
  "secure_refinement \<R>\<^sub>A \<R> P \<equiv>
  closed_others \<R> \<and>
  preserves_modes_mem \<R> \<and>
  new_vars_private \<R> \<and>
  conc.closed_glob_consistent P \<and>
  (\<forall> c\<^sub>1\<^sub>A c\<^sub>1\<^sub>C mds\<^sub>C mem\<^sub>1\<^sub>C. 
   (\<langle> c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C) \<in> \<R> \<longrightarrow>
    (\<forall> c\<^sub>1\<^sub>C' mds\<^sub>C' mem\<^sub>1\<^sub>C'. \<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C \<longrightarrow>
     (\<exists> n c\<^sub>1\<^sub>A'. abs.neval \<langle> c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C \<rangle>\<^sub>A n \<langle> c\<^sub>1\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of mem\<^sub>1\<^sub>C' \<rangle>\<^sub>A \<and>
                   (\<langle> c\<^sub>1\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of mem\<^sub>1\<^sub>C' \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C) \<in> \<R> \<and>
       (\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'. 
         (\<langle> c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C \<rangle>\<^sub>A, \<langle> c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C \<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<and>
         (\<langle> c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C \<rangle>\<^sub>A, \<langle> c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C \<rangle>\<^sub>C) \<in> \<R> \<and>
         (\<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C, \<langle> c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C \<rangle>\<^sub>C) \<in> P \<and>
         abs.neval \<langle> c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C \<rangle>\<^sub>A n \<langle> c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A' \<rangle>\<^sub>A  \<longrightarrow>
           (\<exists> c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'. \<langle> c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C \<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle> c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C' \<rangle>\<^sub>C \<and>
                   (\<langle> c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A' \<rangle>\<^sub>A, \<langle> c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C' \<rangle>\<^sub>C) \<in> \<R> \<and>
                   (\<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C, \<langle> c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C' \<rangle>\<^sub>C) \<in> P)))))"
  apply(rule eq_reflection)
  unfolding secure_refinement_def
  apply(rule conj_cong)
   apply(fastforce)
  apply(rule conj_cong)
   apply(fastforce)
  apply(rule conj_cong)
   apply(fastforce)
  apply(rule conj_cong, fastforce)
  apply(rule iffI)
   apply(intro allI conjI impI)
   apply((drule spec)+,erule (1) impE)
   apply((drule spec)+,erule (1) impE)
   using preserves_modes_memD apply metis
  apply(intro allI conjI impI)
  apply(frule (1) preserves_modes_memD, clarify)
  apply((drule spec)+,erule (1) impE)
  apply((drule spec)+,erule (1) impE)
  using preserves_modes_memD apply metis
  done

lemma extra_vars_are_not_control_vars:
  "x \<notin> range var\<^sub>C_of \<Longrightarrow> x \<notin> \<C>\<^sub>C"
  proof(erule contrapos_nn)
    assume "x \<in> \<C>\<^sub>C"
    from this obtain x\<^sub>A where "x = var\<^sub>C_of x\<^sub>A"
      using control_vars_are_A_vars by blast
    thus "x \<in> range var\<^sub>C_of" by blast
  qed

definition
  R\<^sub>C_of :: 
 "((('Com\<^sub>A \<times> (Mode \<Rightarrow> 'Var\<^sub>A set)) \<times> ('Var\<^sub>A \<Rightarrow> 'Val)) \<times>
    ('Com\<^sub>A \<times> (Mode \<Rightarrow> 'Var\<^sub>A set)) \<times> ('Var\<^sub>A \<Rightarrow> 'Val)) set \<Rightarrow> 
  ('Com\<^sub>A, 'Var\<^sub>A, 'Val, 'Com\<^sub>C, 'Var\<^sub>C) state_relation \<Rightarrow>
  ((('Com\<^sub>C \<times> (Mode \<Rightarrow> 'Var\<^sub>C set)) \<times> ('Var\<^sub>C \<Rightarrow> 'Val)) \<times>
    ('Com\<^sub>C \<times> (Mode \<Rightarrow> 'Var\<^sub>C set)) \<times> ('Var\<^sub>C \<Rightarrow> 'Val)) set \<Rightarrow>
  ((('Com\<^sub>C \<times> (Mode \<Rightarrow> 'Var\<^sub>C set)) \<times> ('Var\<^sub>C \<Rightarrow> 'Val)) \<times>
    ('Com\<^sub>C \<times> (Mode \<Rightarrow> 'Var\<^sub>C set)) \<times> ('Var\<^sub>C \<Rightarrow> 'Val)) set"
where
  "R\<^sub>C_of \<R>\<^sub>A \<R> P \<equiv> {(x,y). \<exists>x\<^sub>A y\<^sub>A. (x\<^sub>A,x) \<in> \<R> \<and> (y\<^sub>A,y) \<in> \<R> \<and> (x\<^sub>A,y\<^sub>A) \<in> \<R>\<^sub>A \<and>
     snd (fst x) = snd (fst y) \<comment> \<open>TODO: annoying to have to say\<close> \<and>
     conc.low_mds_eq (snd (fst x)) (snd x) (snd y) \<and>
     (x,y) \<in> P}"

lemma abs_low_mds_eq_dma\<^sub>C_eq:
  assumes "abs.low_mds_eq (mds\<^sub>A_of mds) (mem\<^sub>A_of mem\<^sub>1\<^sub>C)  (mem\<^sub>A_of mem\<^sub>2\<^sub>C)"
  shows "dma\<^sub>C mem\<^sub>1\<^sub>C = dma\<^sub>C mem\<^sub>2\<^sub>C"
  proof(rule conc.dma_\<C>, rule ballI)
    fix x\<^sub>C
    assume "x\<^sub>C \<in> \<C>\<^sub>C"
    from this obtain x\<^sub>A where "var\<^sub>C_of x\<^sub>A = x\<^sub>C" and "x\<^sub>A \<in> \<C>\<^sub>A" using control_vars_are_A_vars by blast
    from assms \<open>x\<^sub>A \<in> \<C>\<^sub>A\<close> have "(mem\<^sub>A_of mem\<^sub>1\<^sub>C) x\<^sub>A = (mem\<^sub>A_of mem\<^sub>2\<^sub>C) x\<^sub>A"
      unfolding abs.low_mds_eq_def
      using abs.\<C>_Low by blast
    thus "(mem\<^sub>1\<^sub>C x\<^sub>C) = (mem\<^sub>2\<^sub>C x\<^sub>C)"
      using \<open>var\<^sub>C_of x\<^sub>A = x\<^sub>C\<close> unfolding mem\<^sub>A_of_def by blast
  qed

lemma R\<^sub>C_ofD:
  assumes rr: "secure_refinement \<R>\<^sub>A \<R> P"
  assumes in_R: "(\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> R\<^sub>C_of \<R>\<^sub>A \<R> P"
  shows
   "(\<exists>c\<^sub>1\<^sub>A c\<^sub>2\<^sub>A.  (\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<and>
             (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<and>
             (\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> \<R>\<^sub>A) \<and>
    (mds\<^sub>C' = mds\<^sub>C) \<and>
    conc.low_mds_eq mds\<^sub>C mem\<^sub>1\<^sub>C mem\<^sub>2\<^sub>C \<and>
    (\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> P"
  proof -
  have \<R>_preserves_modes_mem: "preserves_modes_mem \<R>"
    using rr unfolding secure_refinement_def by blast

  from in_R obtain c\<^sub>1\<^sub>A mds\<^sub>1\<^sub>A mem\<^sub>1\<^sub>A c\<^sub>2\<^sub>A mds\<^sub>2\<^sub>A mem\<^sub>2\<^sub>A where
  in_\<R>\<^sub>1: "(\<langle>c\<^sub>1\<^sub>A, mds\<^sub>1\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> \<R>" and
  in_\<R>\<^sub>2: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>2\<^sub>A, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> \<R>" and
  in_\<R>\<^sub>A: "(\<langle>c\<^sub>1\<^sub>A, mds\<^sub>1\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>2\<^sub>A, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A) \<in> \<R>\<^sub>A" and
  pred_holds: "(\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> P" and
  mds_eq: "mds\<^sub>C = mds\<^sub>C'" and
  mds_eq: "conc.low_mds_eq mds\<^sub>C mem\<^sub>1\<^sub>C mem\<^sub>2\<^sub>C"
    unfolding R\<^sub>C_of_def by force+
  
  from this \<R>_preserves_modes_mem[simplified preserves_modes_mem_def2, rule_format, OF in_\<R>\<^sub>1] \<R>_preserves_modes_mem[simplified preserves_modes_mem_def2, rule_format, OF in_\<R>\<^sub>2]
    show ?thesis by blast
qed

lemma R\<^sub>C_ofI:
   "(\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<Longrightarrow>
    (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<Longrightarrow>
    (\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<Longrightarrow>
    conc.low_mds_eq mds\<^sub>C mem\<^sub>1\<^sub>C mem\<^sub>2\<^sub>C \<Longrightarrow>
    (\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> P \<Longrightarrow>
     (\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> R\<^sub>C_of \<R>\<^sub>A \<R> P"
  unfolding R\<^sub>C_of_def by fastforce

lemma R\<^sub>C_of_sym:
  assumes "sym \<R>\<^sub>A"
  assumes P_sym: "sym P"
  assumes rr: "secure_refinement \<R>\<^sub>A \<R> P"
  assumes mm: 
    "\<And>c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mds mem\<^sub>2. (\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>\<^sub>A, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<Longrightarrow>
    abs.low_mds_eq mds mem\<^sub>1 mem\<^sub>2"
  shows "sym (R\<^sub>C_of \<R>\<^sub>A \<R> P)"
proof(rule symI, clarify)
  fix c\<^sub>1\<^sub>C mds\<^sub>C mem\<^sub>1\<^sub>C  c\<^sub>2\<^sub>C mds\<^sub>C' mem\<^sub>2\<^sub>C
  assume in_R\<^sub>C_of: "(\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> R\<^sub>C_of \<R>\<^sub>A \<R> P"
  from in_R\<^sub>C_of obtain c\<^sub>1\<^sub>A c\<^sub>2\<^sub>A where
  junk:
  "(\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<and>
   (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<and>
   (\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<and>
    (mds\<^sub>C' = mds\<^sub>C) \<and> conc.low_mds_eq mds\<^sub>C mem\<^sub>1\<^sub>C mem\<^sub>2\<^sub>C \<and>
    (\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> P"
    using rr R\<^sub>C_ofD by fastforce+
  hence dma_eq: "dma\<^sub>C mem\<^sub>1\<^sub>C = dma\<^sub>C mem\<^sub>2\<^sub>C"
    using abs_low_mds_eq_dma\<^sub>C_eq[OF mm] by blast
  with junk have junk':
  "(\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<and>
   (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<and>
   (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<and>
    (mds\<^sub>C' = mds\<^sub>C) \<and>
   conc.low_mds_eq mds\<^sub>C' mem\<^sub>2\<^sub>C mem\<^sub>1\<^sub>C \<and>
   (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> P"
    using \<open>sym \<R>\<^sub>A\<close> P_sym unfolding sym_def using conc.low_mds_eq_sym by metis
   thus "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> R\<^sub>C_of \<R>\<^sub>A \<R> P"
   using R\<^sub>C_ofI by auto
qed

lemma R\<^sub>C_of_simp:
  assumes rr: "secure_refinement \<R>\<^sub>A \<R> P"
  shows "(\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> R\<^sub>C_of \<R>\<^sub>A \<R> P =
   ((\<exists>c\<^sub>1\<^sub>A c\<^sub>2\<^sub>A.  (\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<and>
             (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<and>
             (\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> \<R>\<^sub>A) \<and>
    conc.low_mds_eq mds\<^sub>C mem\<^sub>1\<^sub>C mem\<^sub>2\<^sub>C \<and>
    (\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> P)"
  using assms by(blast dest: R\<^sub>C_ofD intro: R\<^sub>C_ofI)

definition
  A\<^sub>A_of :: "('Var\<^sub>C,'Val) adaptation \<Rightarrow> ('Var\<^sub>A,'Val) adaptation"
where
  "A\<^sub>A_of A \<equiv> \<lambda>x\<^sub>A. case A (var\<^sub>C_of x\<^sub>A) of None \<Rightarrow> None |
                  Some (v,v') \<Rightarrow> Some (v,v')"

lemma var_writable\<^sub>A:
  "\<not> var_asm_not_written mds\<^sub>C (var\<^sub>C_of x) \<Longrightarrow> \<not> var_asm_not_written (mds\<^sub>A_of mds\<^sub>C) x"
  apply(simp add: var_asm_not_written_def mds\<^sub>A_of_def)
  apply(auto simp: inv_f_f[OF var\<^sub>C_of_inj])
  done

lemma A\<^sub>A_asm_mem:
  assumes A\<^sub>C_asm_mem: "\<forall>x. case A\<^sub>C x of None \<Rightarrow> True
           | Some (v, v') \<Rightarrow>
               mem\<^sub>1\<^sub>C x \<noteq> v \<or> mem\<^sub>2\<^sub>C x \<noteq> v' \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x"
  shows "case (A\<^sub>A_of A\<^sub>C) x of None \<Rightarrow> True
           | Some (v, v') \<Rightarrow>
               (mem\<^sub>A_of mem\<^sub>1\<^sub>C) x \<noteq> v \<or> (mem\<^sub>A_of mem\<^sub>2\<^sub>C) x \<noteq> v' \<longrightarrow> \<not> var_asm_not_written (mds\<^sub>A_of mds\<^sub>C) x"
  apply(split option.splits, simp, intro allI impI)
  proof -
    fix v v'
    assume A\<^sub>A_not_None: "A\<^sub>A_of A\<^sub>C x = Some (v, v')"
    assume A\<^sub>A_updates_x: "mem\<^sub>A_of mem\<^sub>1\<^sub>C x = v \<longrightarrow> mem\<^sub>A_of mem\<^sub>2\<^sub>C x \<noteq> v'"
    from A\<^sub>A_not_None have
      A\<^sub>C_not_None: "A\<^sub>C (var\<^sub>C_of x) = Some (v, v')"
      unfolding A\<^sub>A_of_def by (auto split: option.splits)

    from A\<^sub>A_updates_x  have
      A\<^sub>C_updates_x: "mem\<^sub>1\<^sub>C (var\<^sub>C_of x) \<noteq> v \<or> mem\<^sub>2\<^sub>C (var\<^sub>C_of x) \<noteq> v'"
      unfolding mem\<^sub>A_of_def by fastforce

    from A\<^sub>C_not_None A\<^sub>C_updates_x A\<^sub>C_asm_mem have
      "\<not> var_asm_not_written mds\<^sub>C (var\<^sub>C_of x)" by (auto split: option.splits)

    thus "\<not> var_asm_not_written (mds\<^sub>A_of mds\<^sub>C) x"
      by(rule var_writable\<^sub>A)
  qed

lemma dma\<^sub>A_adaptation_eq:
  "dma\<^sub>A ((mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>1 A\<^sub>A_of A\<^sub>C]) x\<^sub>A = dma\<^sub>C (mem\<^sub>1\<^sub>C [\<parallel>\<^sub>1 A\<^sub>C]) (var\<^sub>C_of x\<^sub>A)"
  apply(subst dma_consistent[folded mem\<^sub>A_of_def, symmetric])
  apply(rule_tac x=x\<^sub>A in fun_cong)
  apply(rule_tac f="dma\<^sub>A" in arg_cong)
  apply(rule ext)
  apply(clarsimp simp: apply_adaptation_def A\<^sub>A_of_def mem\<^sub>A_of_def split: option.splits)
  done

  
lemma A\<^sub>A_asm_dma:
  assumes A\<^sub>C_asm_dma: "\<forall>x. dma\<^sub>C (mem\<^sub>1\<^sub>C [\<parallel>\<^sub>1 A\<^sub>C]) x \<noteq> dma\<^sub>C mem\<^sub>1\<^sub>C x \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x"
  shows "dma\<^sub>A ((mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>1 (A\<^sub>A_of A\<^sub>C)]) x\<^sub>A \<noteq> dma\<^sub>A (mem\<^sub>A_of mem\<^sub>1\<^sub>C) x\<^sub>A \<longrightarrow> \<not> var_asm_not_written (mds\<^sub>A_of mds\<^sub>C) x\<^sub>A"
proof(intro impI)
  assume A\<^sub>A_updates_dma: "dma\<^sub>A ((mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>1 A\<^sub>A_of A\<^sub>C]) x\<^sub>A \<noteq> dma\<^sub>A (mem\<^sub>A_of mem\<^sub>1\<^sub>C) x\<^sub>A"
 
  with dma_consistent[folded mem\<^sub>A_of_def] dma\<^sub>A_adaptation_eq
  have "dma\<^sub>C (mem\<^sub>1\<^sub>C [\<parallel>\<^sub>1 A\<^sub>C]) (var\<^sub>C_of x\<^sub>A) \<noteq> dma\<^sub>C mem\<^sub>1\<^sub>C (var\<^sub>C_of x\<^sub>A)" by(metis)

  with A\<^sub>C_asm_dma have "\<not> var_asm_not_written mds\<^sub>C (var\<^sub>C_of x\<^sub>A)" by blast

  thus " \<not> var_asm_not_written (mds\<^sub>A_of mds\<^sub>C) x\<^sub>A" by (rule  var_writable\<^sub>A)
qed

lemma var\<^sub>C_of_in_\<C>\<^sub>C: 
  assumes "x\<^sub>A \<in> \<C>\<^sub>A"
  shows "var\<^sub>C_of x\<^sub>A \<in> \<C>\<^sub>C"
proof -
  from assms obtain y\<^sub>A where "x\<^sub>A \<in> \<C>_vars\<^sub>A y\<^sub>A"
  unfolding abs.\<C>_def by blast

  hence "var\<^sub>C_of x\<^sub>A \<in> \<C>_vars\<^sub>C (var\<^sub>C_of y\<^sub>A)"
    using \<C>_vars_consistent by blast

  thus ?thesis using conc.\<C>_def by blast
qed

lemma doesnt_have_mode\<^sub>C:
  "x \<notin> mds\<^sub>A_of mds\<^sub>C m \<Longrightarrow> var\<^sub>C_of x \<notin> mds\<^sub>C m"
  by(simp add: doesnt_have_mode)

lemma has_mode\<^sub>A: "var\<^sub>C_of x \<in> mds\<^sub>C m \<Longrightarrow> x \<in> mds\<^sub>A_of mds\<^sub>C m"
  using doesnt_have_mode\<^sub>C
  by fastforce

lemma A\<^sub>A_sec:
  assumes A\<^sub>C_sec: "\<forall>x. dma\<^sub>C (mem\<^sub>1\<^sub>C [\<parallel>\<^sub>1 A\<^sub>C]) x = Low \<and> (x \<notin> mds\<^sub>C AsmNoReadOrWrite \<or> x \<in> \<C>\<^sub>C) \<longrightarrow>
           mem\<^sub>1\<^sub>C [\<parallel>\<^sub>1 A\<^sub>C] x = mem\<^sub>2\<^sub>C [\<parallel>\<^sub>2 A\<^sub>C] x"
  shows "dma\<^sub>A ((mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>1 A\<^sub>A_of A\<^sub>C]) x = Low \<and> (x \<notin> mds\<^sub>A_of mds\<^sub>C AsmNoReadOrWrite \<or> x \<in> \<C>\<^sub>A) \<longrightarrow>
           (mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>1 A\<^sub>A_of A\<^sub>C] x = (mem\<^sub>A_of mem\<^sub>2\<^sub>C) [\<parallel>\<^sub>2 A\<^sub>A_of A\<^sub>C] x"
proof(clarify)
  assume x_is_Low: "dma\<^sub>A ((mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>1 A\<^sub>A_of A\<^sub>C]) x = Low"
  assume x_is_readable: "x \<notin> mds\<^sub>A_of mds\<^sub>C AsmNoReadOrWrite \<or> x \<in> \<C>\<^sub>A"
    
  from x_is_Low have x_is_Low\<^sub>C: "dma\<^sub>C (mem\<^sub>1\<^sub>C [\<parallel>\<^sub>1 A\<^sub>C]) (var\<^sub>C_of x) = Low"
    using dma\<^sub>A_adaptation_eq by simp
  from x_is_readable have "var\<^sub>C_of x \<notin> mds\<^sub>C AsmNoReadOrWrite \<or> var\<^sub>C_of x \<in> \<C>\<^sub>C"
    using doesnt_have_mode\<^sub>C  var\<^sub>C_of_in_\<C>\<^sub>C by blast
  with A\<^sub>C_sec x_is_Low\<^sub>C have "mem\<^sub>1\<^sub>C [\<parallel>\<^sub>1 A\<^sub>C] (var\<^sub>C_of x) = mem\<^sub>2\<^sub>C [\<parallel>\<^sub>2 A\<^sub>C] (var\<^sub>C_of x)"
    by blast
  thus "(mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>1 A\<^sub>A_of A\<^sub>C] x = (mem\<^sub>A_of mem\<^sub>2\<^sub>C) [\<parallel>\<^sub>2 A\<^sub>A_of A\<^sub>C] x"
    by(auto simp: mem\<^sub>A_of_def apply_adaptation_def A\<^sub>A_of_def split: option.splits)
qed

lemma apply_adaptation\<^sub>A:
  "(mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>1 A\<^sub>A_of A\<^sub>C] = mem\<^sub>A_of (mem\<^sub>1\<^sub>C [\<parallel>\<^sub>1 A\<^sub>C])"
  "(mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>2 A\<^sub>A_of A\<^sub>C] = mem\<^sub>A_of (mem\<^sub>1\<^sub>C [\<parallel>\<^sub>2 A\<^sub>C])"
  by(auto simp: mem\<^sub>A_of_def A\<^sub>A_of_def apply_adaptation_def split: option.splits)

 
lemma R\<^sub>C_of_closed_glob_consistent:
  assumes mm: 
    "\<And>c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mds mem\<^sub>2. (\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>\<^sub>A, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<Longrightarrow>
    abs.low_mds_eq mds mem\<^sub>1 mem\<^sub>2"
  assumes cgc: "abs.closed_glob_consistent \<R>\<^sub>A"
  assumes rr: "secure_refinement \<R>\<^sub>A \<R> P"
  shows "conc.closed_glob_consistent (R\<^sub>C_of \<R>\<^sub>A \<R> P)"
  unfolding conc.closed_glob_consistent_def
proof(clarify)
  fix c\<^sub>1\<^sub>C mds\<^sub>C mem\<^sub>1\<^sub>C c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C A\<^sub>C
  assume "(\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> R\<^sub>C_of \<R>\<^sub>A \<R> P"
  from this rr obtain c\<^sub>1\<^sub>A c\<^sub>2\<^sub>A where
       in_\<R>\<^sub>A:  "(\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> \<R>\<^sub>A" and
       in_\<R>\<^sub>1:  "(\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> \<R>" and
       in_\<R>\<^sub>2:  "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> \<R>"
         and
       mds_eq: "conc.low_mds_eq mds\<^sub>C mem\<^sub>1\<^sub>C mem\<^sub>2\<^sub>C"
         and
       P: "(\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> P"
      by (blast dest: R\<^sub>C_ofD)
  assume A\<^sub>C_asm_mem: "\<forall>x. case A\<^sub>C x of None \<Rightarrow> True
                                   | Some (v, v') \<Rightarrow>
                                      mem\<^sub>1\<^sub>C x \<noteq> v \<or> mem\<^sub>2\<^sub>C x \<noteq> v' \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x"
  hence A\<^sub>A_asm_mem: "\<forall>x. case (A\<^sub>A_of A\<^sub>C) x of None \<Rightarrow> True
                                           | Some (v, v') \<Rightarrow>
               (mem\<^sub>A_of mem\<^sub>1\<^sub>C) x \<noteq> v \<or> (mem\<^sub>A_of mem\<^sub>2\<^sub>C) x \<noteq> v' \<longrightarrow> \<not> var_asm_not_written (mds\<^sub>A_of mds\<^sub>C) x"
    by(metis A\<^sub>A_asm_mem)

  assume A\<^sub>C_asm_dma: "\<forall>x. dma\<^sub>C (mem\<^sub>1\<^sub>C [\<parallel>\<^sub>1 A\<^sub>C]) x \<noteq> dma\<^sub>C mem\<^sub>1\<^sub>C x \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x"
  hence A\<^sub>A_asm_dma: "\<forall>x\<^sub>A. dma\<^sub>A ((mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>1 (A\<^sub>A_of A\<^sub>C)]) x\<^sub>A \<noteq> dma\<^sub>A (mem\<^sub>A_of mem\<^sub>1\<^sub>C) x\<^sub>A \<longrightarrow> \<not> var_asm_not_written (mds\<^sub>A_of mds\<^sub>C) x\<^sub>A"
    by(metis A\<^sub>A_asm_dma)

  assume A\<^sub>C_sec: "\<forall>x. dma\<^sub>C (mem\<^sub>1\<^sub>C [\<parallel>\<^sub>1 A\<^sub>C]) x = Low \<and> (x \<notin> mds\<^sub>C AsmNoReadOrWrite \<or> x \<in> \<C>\<^sub>C) \<longrightarrow>
         mem\<^sub>1\<^sub>C [\<parallel>\<^sub>1 A\<^sub>C] x = mem\<^sub>2\<^sub>C [\<parallel>\<^sub>2 A\<^sub>C] x"
  hence A\<^sub>A_sec: "\<forall>x. dma\<^sub>A ((mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>1 A\<^sub>A_of A\<^sub>C]) x = Low \<and> (x \<notin> mds\<^sub>A_of mds\<^sub>C AsmNoReadOrWrite \<or> x \<in> \<C>\<^sub>A) \<longrightarrow>
         (mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>1 A\<^sub>A_of A\<^sub>C] x = (mem\<^sub>A_of mem\<^sub>2\<^sub>C) [\<parallel>\<^sub>2 A\<^sub>A_of A\<^sub>C] x"
    by(metis A\<^sub>A_sec)
    
  from rr have others: "closed_others \<R>"
    unfolding secure_refinement_def by blast
  from rr have P_cgc: "conc.closed_glob_consistent P"
    unfolding secure_refinement_def by blast
  let ?mem\<^sub>1\<^sub>C' = "(mem\<^sub>1\<^sub>C [\<parallel>\<^sub>1 A\<^sub>C])" and
      ?mem\<^sub>2\<^sub>C' = "(mem\<^sub>2\<^sub>C [\<parallel>\<^sub>2 A\<^sub>C])" and
      ?mem\<^sub>1\<^sub>A = "(mem\<^sub>A_of mem\<^sub>1\<^sub>C)" and
      ?mem\<^sub>2\<^sub>A = "(mem\<^sub>A_of mem\<^sub>2\<^sub>C)" and
      ?mem\<^sub>1\<^sub>A' = "(mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>1 A\<^sub>A_of A\<^sub>C]" and
      ?mem\<^sub>2\<^sub>A' = "(mem\<^sub>A_of mem\<^sub>2\<^sub>C) [\<parallel>\<^sub>2 A\<^sub>A_of A\<^sub>C]"

  have mem'_simps: 
    "?mem\<^sub>1\<^sub>A' = mem\<^sub>A_of ?mem\<^sub>1\<^sub>C'" 
    "?mem\<^sub>2\<^sub>A' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'" by(simp add: apply_adaptation\<^sub>A)+

  from cgc in_\<R>\<^sub>A A\<^sub>A_asm_mem A\<^sub>A_asm_dma A\<^sub>A_sec have
    in_\<R>\<^sub>A': "(\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, (mem\<^sub>A_of mem\<^sub>1\<^sub>C) [\<parallel>\<^sub>1 A\<^sub>A_of A\<^sub>C]\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, (mem\<^sub>A_of mem\<^sub>2\<^sub>C) [\<parallel>\<^sub>2 A\<^sub>A_of A\<^sub>C]\<rangle>\<^sub>A) \<in> \<R>\<^sub>A" unfolding abs.closed_glob_consistent_def by blast

  from A\<^sub>C_asm_mem A\<^sub>C_asm_dma have 
    A\<^sub>C_asm_mem\<^sub>1': "\<forall>x. mem\<^sub>1\<^sub>C x \<noteq> ?mem\<^sub>1\<^sub>C' x \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x" and
    A\<^sub>C_asm_dma\<^sub>1': "\<forall>x. dma\<^sub>C mem\<^sub>1\<^sub>C x \<noteq> dma\<^sub>C ?mem\<^sub>1\<^sub>C' x \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x"
    unfolding apply_adaptation_def by(force split: option.splits)+

  from A\<^sub>C_asm_mem have
    A\<^sub>C_asm_mem\<^sub>2': "\<forall>x. mem\<^sub>2\<^sub>C x \<noteq> ?mem\<^sub>2\<^sub>C' x \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x"
    unfolding apply_adaptation_def by(force split: option.splits)

  from in_\<R>\<^sub>1 A\<^sub>C_asm_mem\<^sub>1' A\<^sub>C_asm_dma\<^sub>1' others have
    in_\<R>\<^sub>1':  "(\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A_of mds\<^sub>C, ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, ?mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> \<R>"
    unfolding closed_others_def mem'_simps by blast

  from mm[OF in_\<R>\<^sub>A] have 
    dma\<^sub>C_eq: "dma\<^sub>C mem\<^sub>1\<^sub>C = dma\<^sub>C mem\<^sub>2\<^sub>C" by(rule abs_low_mds_eq_dma\<^sub>C_eq)
  have dma\<^sub>C_eq': "dma\<^sub>C ?mem\<^sub>1\<^sub>C' = dma\<^sub>C ?mem\<^sub>2\<^sub>C'"
    apply(rule abs_low_mds_eq_dma\<^sub>C_eq[OF mm])
    apply(simp add: mem'_simps[symmetric])
    by(rule in_\<R>\<^sub>A')
  from dma\<^sub>C_eq dma\<^sub>C_eq' A\<^sub>C_asm_dma\<^sub>1' have
    A\<^sub>C_asm_dma\<^sub>2': "\<forall>x. dma\<^sub>C mem\<^sub>2\<^sub>C x \<noteq> dma\<^sub>C ?mem\<^sub>2\<^sub>C' x \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x"
    by simp

  from in_\<R>\<^sub>2  A\<^sub>C_asm_mem\<^sub>2' A\<^sub>C_asm_dma\<^sub>2' others have
    in_\<R>\<^sub>2':  "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, ?mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> \<R>"
    unfolding closed_others_def mem'_simps by blast

  have mds_eq': "conc.low_mds_eq mds\<^sub>C ?mem\<^sub>1\<^sub>C' ?mem\<^sub>2\<^sub>C'" 
    using A\<^sub>C_sec unfolding conc.low_mds_eq_def by blast
   
 from P P_cgc A\<^sub>C_asm_mem A\<^sub>C_asm_dma A\<^sub>C_sec have P': "(\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, ?mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> P"
   unfolding conc.closed_glob_consistent_def by blast 
  from in_\<R>\<^sub>A' in_\<R>\<^sub>1' in_\<R>\<^sub>2' mem'_simps R\<^sub>C_ofI mds_eq' P' show
  "(\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, ?mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> R\<^sub>C_of \<R>\<^sub>A \<R> P"
    by(metis)
qed

lemma R\<^sub>C_of_local_preservation:
  assumes rr: "secure_refinement \<R>\<^sub>A \<R> P"
  assumes bisim: "abs.strong_low_bisim_mm \<R>\<^sub>A"
  assumes in_R\<^sub>C_of: "(\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> R\<^sub>C_of \<R>\<^sub>A \<R> P"
  assumes step\<^sub>1\<^sub>C: "\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C"
  shows "\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
          \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C \<and>
          (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> R\<^sub>C_of \<R>\<^sub>A \<R> P"
proof -
  from rr in_R\<^sub>C_of have
    P: "(\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> P"
      by(blast dest: R\<^sub>C_ofD)

  let ?mds\<^sub>A = "mds\<^sub>A_of mds\<^sub>C" and
      ?mem\<^sub>1\<^sub>A = "mem\<^sub>A_of mem\<^sub>1\<^sub>C" and
      ?mem\<^sub>2\<^sub>A = "mem\<^sub>A_of mem\<^sub>2\<^sub>C" and
      ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'" and
      ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"

  from rr in_R\<^sub>C_of obtain c\<^sub>1\<^sub>A c\<^sub>2\<^sub>A where
    in_\<R>\<^sub>1: "(\<langle>c\<^sub>1\<^sub>A, ?mds\<^sub>A, ?mem\<^sub>1\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> \<R>" and
    in_\<R>\<^sub>2: "(\<langle>c\<^sub>2\<^sub>A, ?mds\<^sub>A, ?mem\<^sub>2\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> \<R>" and
    in_\<R>\<^sub>A: "(\<langle>c\<^sub>1\<^sub>A, ?mds\<^sub>A, ?mem\<^sub>1\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, ?mds\<^sub>A, ?mem\<^sub>2\<^sub>A\<rangle>\<^sub>A) \<in> \<R>\<^sub>A" and
    low_mds_mds\<^sub>C: "conc.low_mds_eq mds\<^sub>C mem\<^sub>1\<^sub>C mem\<^sub>2\<^sub>C"
    by(blast dest: R\<^sub>C_ofD)+

  from rr in_\<R>\<^sub>1 in_\<R>\<^sub>A in_\<R>\<^sub>2 step\<^sub>1\<^sub>C obtain n c\<^sub>1\<^sub>A' where
     a: "(abs.neval \<langle> c\<^sub>1\<^sub>A, ?mds\<^sub>A, ?mem\<^sub>1\<^sub>A \<rangle>\<^sub>A n \<langle> c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A' \<rangle>\<^sub>A \<and>
         (\<langle> c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A' \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C) \<in> \<R> \<and>
       (\<forall>c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'. 
         (\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> P \<and>
         abs.neval \<langle> c\<^sub>2\<^sub>A, ?mds\<^sub>A, ?mem\<^sub>2\<^sub>A \<rangle>\<^sub>A n \<langle> c\<^sub>2\<^sub>A', ?mds\<^sub>A', mem\<^sub>2\<^sub>A' \<rangle>\<^sub>A  \<longrightarrow>
           (\<exists> c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'. \<langle> c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C \<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle> c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C' \<rangle>\<^sub>C \<and>
                   (\<langle> c\<^sub>2\<^sub>A', ?mds\<^sub>A', mem\<^sub>2\<^sub>A' \<rangle>\<^sub>A, \<langle> c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C' \<rangle>\<^sub>C) \<in> \<R> \<and>
                   (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> P)))"
  unfolding secure_refinement_def2
    by metis

  show ?thesis
  proof -
    from a have neval\<^sub>1\<^sub>A: "abs.neval \<langle>c\<^sub>1\<^sub>A, ?mds\<^sub>A, ?mem\<^sub>1\<^sub>A\<rangle>\<^sub>A n \<langle>c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
                in_\<R>\<^sub>1': "(\<langle>c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> \<R>"
           by blast+
    from  strong_low_bisim_neval[OF neval\<^sub>1\<^sub>A  in_\<R>\<^sub>A bisim] obtain c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A' where
      neval\<^sub>2\<^sub>A: "abs.neval \<langle>c\<^sub>2\<^sub>A, ?mds\<^sub>A, ?mem\<^sub>2\<^sub>A\<rangle>\<^sub>A n \<langle>c\<^sub>2\<^sub>A', ?mds\<^sub>A', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A" and
      in_\<R>\<^sub>A'_help: "(\<langle>c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A', ?mds\<^sub>A', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A) \<in> \<R>\<^sub>A"
      unfolding abs.strong_low_bisim_mm_def
      by blast

    from a in_\<R>\<^sub>A in_\<R>\<^sub>2 neval\<^sub>2\<^sub>A P obtain c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C' where
          step\<^sub>2\<^sub>C: "\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C" and
          in_\<R>\<^sub>2'_help: "(\<langle>c\<^sub>2\<^sub>A', ?mds\<^sub>A', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> \<R>" and
          P': "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> P"
      by blast

    let ?mem\<^sub>2\<^sub>A' = "mem\<^sub>A_of mem\<^sub>2\<^sub>C'"
    from in_\<R>\<^sub>2'_help rr preserves_modes_memD have "mem\<^sub>2\<^sub>A' = ?mem\<^sub>2\<^sub>A'" 
      unfolding secure_refinement_def by metis
    with in_\<R>\<^sub>2'_help in_\<R>\<^sub>A'_help have 
      in_\<R>\<^sub>2': "(\<langle>c\<^sub>2\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> \<R>" and
      in_\<R>\<^sub>A': "(\<langle>c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A) \<in> \<R>\<^sub>A"
      by simp+

    have "conc.low_mds_eq mds\<^sub>C' mem\<^sub>1\<^sub>C' mem\<^sub>2\<^sub>C'"
      apply(rule new_vars_private_does_the_thing[where \<R>=\<R>, OF _ in_\<R>\<^sub>1 in_\<R>\<^sub>2 step\<^sub>1\<^sub>C step\<^sub>2\<^sub>C low_mds_mds\<^sub>C])
       using rr apply(fastforce simp: secure_refinement_def)
      using in_\<R>\<^sub>A' bisim unfolding abs.strong_low_bisim_mm_def by blast

    with step\<^sub>2\<^sub>C in_\<R>\<^sub>1' in_\<R>\<^sub>2' in_\<R>\<^sub>A' in_\<R>\<^sub>2' P' show ?thesis
      by(blast intro: R\<^sub>C_ofI)
  qed
qed
  
text \<open>
  Security of the concrete system should follow straightforwardly from
  security of the abstract one, via the compositionality theorem, presuming
  that the compiler also preserves the sound use of modes.
\<close>
lemma R\<^sub>C_of_strong_low_bisim_mm:
  assumes abs: "abs.strong_low_bisim_mm \<R>\<^sub>A"
  assumes rr: "secure_refinement \<R>\<^sub>A \<R> P"
  assumes P_sym: "sym P"
  shows "conc.strong_low_bisim_mm (R\<^sub>C_of \<R>\<^sub>A \<R> P)"
  unfolding conc.strong_low_bisim_mm_def
  apply(intro conjI)
    apply(rule R\<^sub>C_of_sym)
    using abs rr P_sym unfolding abs.strong_low_bisim_mm_def apply blast+
   apply(rule R\<^sub>C_of_closed_glob_consistent)
    using abs unfolding abs.strong_low_bisim_mm_def apply blast+
   using rr apply blast
  apply safe
   apply(fastforce simp: R\<^sub>C_of_def)
  apply(rule R\<^sub>C_of_local_preservation)
     apply(rule rr)
    apply(rule abs)
   apply assumption+
  done

section "A Simpler Proof Principle for General Compositional Refinement"

text \<open>
  Here we make use of the fact that the source language we are working
  in is assumed deterministic. This allows us to invert the direction
  of refinement and thereby to derive a simpler condition for secure
  compositional refinement.
  
  The simpler condition rests on an ordinary definition of refinement,
  and has the user prove separately that the coupling invariant @{term P}
  is self-preserving. This allows proofs about coupling invariant properties
  to be disentangled from the proof of refinement itself.
\<close>
  
text \<open>
  Given a  bisimulation @{term \<R>\<^sub>A}, this definition captures the essence of the extra
  requirements on a refinement relation~@{term \<R>} needed to ensure that the refined program is
  also secure. These requirements are essentially that:
  \begin{enumerate}
    \item The enabledness of the compiled code depends only on Low abstract data;
    \item The length of the abstract program to which a single step of the concrete program
          corresponds depends only on Low abstract data;
    \item The coupling invariant is maintained.
  \end{enumerate}
  
  The second requirement we express via the parameter~@{term abs_steps} that, given an
  abstract and corresponding concrete configuration, yields the number of execution steps of
  the abstract configuration to which a single step of the concrete configuration corresponds.
  
  Note that a more specialised version of this definition, fixing the coupling
  invariant @{term P} to be the one that relates all configurations with
  identical programs and mode states, appeared in Murray et al., CSF 2016.
  Here we generalise the theory to support a wider class of coupling invariants.
\<close>
definition
  simpler_refinement_safe 
where
  "simpler_refinement_safe \<R>\<^sub>A \<R> P abs_steps \<equiv> 
  \<forall>c\<^sub>1\<^sub>A mds\<^sub>A mem\<^sub>1\<^sub>A c\<^sub>2\<^sub>A mem\<^sub>2\<^sub>A c\<^sub>1\<^sub>C mds\<^sub>C mem\<^sub>1\<^sub>C c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C. (\<langle>c\<^sub>1\<^sub>A,mds\<^sub>A,mem\<^sub>1\<^sub>A\<rangle>\<^sub>A,\<langle>c\<^sub>2\<^sub>A,mds\<^sub>A,mem\<^sub>2\<^sub>A\<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<and> 
      (\<langle>c\<^sub>1\<^sub>A,mds\<^sub>A,mem\<^sub>1\<^sub>A\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<and> (\<langle>c\<^sub>2\<^sub>A,mds\<^sub>A,mem\<^sub>2\<^sub>A\<rangle>\<^sub>A,\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<and>
       (\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> P  \<longrightarrow>
           (stops\<^sub>C \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C = stops\<^sub>C \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<and>
           (abs_steps \<langle>c\<^sub>1\<^sub>A,mds\<^sub>A,mem\<^sub>1\<^sub>A\<rangle>\<^sub>A \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C = abs_steps \<langle>c\<^sub>2\<^sub>A,mds\<^sub>A,mem\<^sub>2\<^sub>A\<rangle>\<^sub>A \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<and>
           (\<forall>mds\<^sub>1\<^sub>C' mds\<^sub>2\<^sub>C' mem\<^sub>1\<^sub>C' mem\<^sub>2\<^sub>C' c\<^sub>1\<^sub>C' c\<^sub>2\<^sub>C'. \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>1\<^sub>C', mds\<^sub>1\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C  \<and>
                                          \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>2\<^sub>C', mds\<^sub>2\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C \<longrightarrow>
                                          (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>1\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>2\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> P \<and>
                                          mds\<^sub>1\<^sub>C' = mds\<^sub>2\<^sub>C')"

definition
  secure_refinement_simpler
where
  "secure_refinement_simpler \<R>\<^sub>A \<R> P abs_steps \<equiv>
  closed_others \<R> \<and>
  preserves_modes_mem \<R> \<and>
  new_vars_private \<R> \<and>
  simpler_refinement_safe \<R>\<^sub>A \<R> P abs_steps \<and>
  conc.closed_glob_consistent P \<and>
  (\<forall> c\<^sub>1\<^sub>A mds\<^sub>A mem\<^sub>1\<^sub>A c\<^sub>1\<^sub>C mds\<^sub>C mem\<^sub>1\<^sub>C. 
   (\<langle> c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C) \<in> \<R> \<longrightarrow>
    (\<forall> c\<^sub>1\<^sub>C' mds\<^sub>C' mem\<^sub>1\<^sub>C'. \<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C \<longrightarrow>
     (\<exists> c\<^sub>1\<^sub>A' mds\<^sub>A' mem\<^sub>1\<^sub>A'. abs.neval \<langle> c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A \<rangle>\<^sub>A (abs_steps \<langle>c\<^sub>1\<^sub>A,mds\<^sub>A,mem\<^sub>1\<^sub>A\<rangle>\<^sub>A \<langle>c\<^sub>1\<^sub>C,mds\<^sub>C,mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<langle> c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A' \<rangle>\<^sub>A \<and>
                   (\<langle> c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A' \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C) \<in> \<R>)))"
    
lemma secure_refinement_simpler:
  assumes rrs: "secure_refinement_simpler \<R>\<^sub>A \<R> P abs_steps"
  shows "secure_refinement \<R>\<^sub>A \<R> P"
  unfolding secure_refinement_def
proof(safe)
  from rrs show "closed_others \<R>"
    unfolding secure_refinement_simpler_def by blast
next
  from rrs show "preserves_modes_mem \<R>"
    unfolding secure_refinement_simpler_def by blast
next
  from rrs show "new_vars_private \<R>"
    unfolding secure_refinement_simpler_def by blast
next
  fix c\<^sub>1\<^sub>A mds\<^sub>A mem\<^sub>1\<^sub>A c\<^sub>1\<^sub>C mds\<^sub>C mem\<^sub>1\<^sub>C c\<^sub>1\<^sub>C' mds\<^sub>C' mem\<^sub>1\<^sub>C'
  let ?n = "abs_steps \<langle>c\<^sub>1\<^sub>A,mds\<^sub>A,mem\<^sub>1\<^sub>A\<rangle>\<^sub>A \<langle>c\<^sub>1\<^sub>C,mds\<^sub>C,mem\<^sub>1\<^sub>C\<rangle>\<^sub>C"
  assume in_\<R>\<^sub>1: "(\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> \<R>"
     and eval\<^sub>1\<^sub>C: "\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C"
  with rrs obtain c\<^sub>1\<^sub>A' mds\<^sub>A' mem\<^sub>1\<^sub>A' where
    neval\<^sub>1: "abs.neval \<langle> c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A \<rangle>\<^sub>A ?n \<langle> c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A' \<rangle>\<^sub>A" and
    in_\<R>\<^sub>1': "(\<langle> c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A' \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C) \<in> \<R>"
    unfolding secure_refinement_simpler_def by metis
  have "(\<forall>c\<^sub>2\<^sub>A mem\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                (\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<and>
                (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<and>
                (\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C,\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> P \<and> abs.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A ?n \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                    \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C \<and>
                    (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> \<R> \<and> 
                    (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C,\<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> P))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A mem\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume 
    in_\<R>\<^sub>A: "(\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A) \<in> \<R>\<^sub>A" and 
    in_\<R>\<^sub>2: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> \<R>" and
    neval\<^sub>2: "abs.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A ?n \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A" and
    in_P: "(\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C,\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> P"
    have "\<forall>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'. \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C \<longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> \<R> \<and> (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> P"
    proof(clarify)
      fix c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'
      assume eval\<^sub>2\<^sub>C: "\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C"
      from in_\<R>\<^sub>2 eval\<^sub>2\<^sub>C in_P rrs obtain
      c\<^sub>2\<^sub>A'' mds\<^sub>A'' mem\<^sub>2\<^sub>A'' where 
      neval\<^sub>2': "abs.neval \<langle> c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A \<rangle>\<^sub>A (abs_steps \<langle>c\<^sub>2\<^sub>A,mds\<^sub>A,mem\<^sub>2\<^sub>A\<rangle>\<^sub>A \<langle>c\<^sub>2\<^sub>C,mds\<^sub>C,mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<langle> c\<^sub>2\<^sub>A'', mds\<^sub>A'', mem\<^sub>2\<^sub>A'' \<rangle>\<^sub>A" and
      in_\<R>\<^sub>2': "(\<langle> c\<^sub>2\<^sub>A'', mds\<^sub>A'', mem\<^sub>2\<^sub>A'' \<rangle>\<^sub>A, \<langle> c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C' \<rangle>\<^sub>C) \<in> \<R>"
        unfolding secure_refinement_simpler_def by blast
      let ?n' = "(abs_steps \<langle>c\<^sub>2\<^sub>A,mds\<^sub>A,mem\<^sub>2\<^sub>A\<rangle>\<^sub>A \<langle>c\<^sub>2\<^sub>C,mds\<^sub>C,mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)"
      from rrs have pe: "simpler_refinement_safe \<R>\<^sub>A \<R> P abs_steps"
        unfolding secure_refinement_simpler_def by blast
      with in_\<R>\<^sub>A in_\<R>\<^sub>1 in_\<R>\<^sub>2 in_P
      have "?n' = ?n"
        unfolding simpler_refinement_safe_def by fastforce
      with neval\<^sub>2 neval\<^sub>2' abs.neval_det 
      have [simp]: "c\<^sub>2\<^sub>A'' = c\<^sub>2\<^sub>A'"  and [simp]: "mds\<^sub>A'' = mds\<^sub>A'" and [simp]: "mem\<^sub>2\<^sub>A'' = mem\<^sub>2\<^sub>A'"
        by auto
      from in_\<R>\<^sub>2' have in_\<R>\<^sub>2': "(\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> \<R>" by simp
      from eval\<^sub>1\<^sub>C eval\<^sub>2\<^sub>C in_P have 
      in_P': "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C,\<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> P"
        using rrs unfolding secure_refinement_simpler_def
                            simpler_refinement_safe_def
        using in_\<R>\<^sub>A in_\<R>\<^sub>1 in_\<R>\<^sub>2 in_P by auto
      with in_\<R>\<^sub>2'
      show "(\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> \<R> \<and>
       (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> P" by blast
    qed
    moreover have "\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'. \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C"
    proof -
      from rrs have pe: "simpler_refinement_safe \<R>\<^sub>A \<R> P abs_steps"
        unfolding secure_refinement_simpler_def by blast
      with in_\<R>\<^sub>A in_\<R>\<^sub>1 in_\<R>\<^sub>2 in_P have "stops\<^sub>C  \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C = stops\<^sub>C  \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C"
        unfolding simpler_refinement_safe_def by blast
      moreover from eval\<^sub>1\<^sub>C have "\<not> stops\<^sub>C  \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C"
        unfolding stops\<^sub>C_def by blast
      ultimately have "\<not> stops\<^sub>C  \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C"
        by simp          
      from this obtain c\<^sub>2\<^sub>C' mds\<^sub>C'' mem\<^sub>2\<^sub>C'' where eval\<^sub>2\<^sub>C': "\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>2\<^sub>C',mds\<^sub>C'',mem\<^sub>2\<^sub>C''\<rangle>\<^sub>C"
        unfolding stops\<^sub>C_def by auto
      with pe eval\<^sub>1\<^sub>C in_\<R>\<^sub>A in_\<R>\<^sub>1 in_\<R>\<^sub>2 in_P have in_P': "(\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C',mds\<^sub>C'', mem\<^sub>2\<^sub>C''\<rangle>\<^sub>C) \<in> P"
                                             and [simp]: "mds\<^sub>C'' = mds\<^sub>C'"
        unfolding simpler_refinement_safe_def  by blast+
      from in_P' eval\<^sub>2\<^sub>C'
      show "\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'. \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C"
        by fastforce
      qed
    ultimately show 
    "\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
     \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C \<and> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> \<R> \<and> (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C,
           \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
          \<in> P"
      by blast
  qed
  with neval\<^sub>1 in_\<R>\<^sub>1 in_\<R>\<^sub>1' 
  show "\<exists>n c\<^sub>1\<^sub>A' mds\<^sub>A' mem\<^sub>1\<^sub>A'.
            abs.neval \<langle>c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A n \<langle>c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A \<and>
            (\<langle>c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> \<R> \<and>
            (\<forall>c\<^sub>2\<^sub>A mem\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                (\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<and>
                (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<and>
                (\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                \<in> P \<and>
                abs.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A n \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                    \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C \<and>
                    (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> \<R> \<and>
                    (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                    \<in> P))"
    by auto
next
  show "conc.closed_glob_consistent P"
    using rrs unfolding secure_refinement_simpler_def by blast
qed

section "Simple Bisimulations and Simple Refinement"

text \<open>
  We derive the theory of simple refinements from Murray et al. CSF 2016 from the above
  \emph{simpler} theory of secure refinement.
\<close>

definition
   bisim_simple
where
  "bisim_simple \<R>\<^sub>A \<equiv> \<forall>c\<^sub>1\<^sub>A mds mem\<^sub>1\<^sub>A c\<^sub>2\<^sub>A mem\<^sub>2\<^sub>A. (\<langle>c\<^sub>1\<^sub>A,mds,mem\<^sub>1\<^sub>A\<rangle>\<^sub>A,\<langle>c\<^sub>2\<^sub>A,mds,mem\<^sub>2\<^sub>A\<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<longrightarrow> 
                                              c\<^sub>1\<^sub>A = c\<^sub>2\<^sub>A"
definition
  simple_refinement_safe
where
  "simple_refinement_safe \<R>\<^sub>A \<R> abs_steps \<equiv> 
  \<forall>c\<^sub>A mds\<^sub>A mem\<^sub>1\<^sub>A mem\<^sub>2\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>1\<^sub>C mem\<^sub>2\<^sub>C. (\<langle>c\<^sub>A,mds\<^sub>A,mem\<^sub>1\<^sub>A\<rangle>\<^sub>A,\<langle>c\<^sub>A,mds\<^sub>A,mem\<^sub>2\<^sub>A\<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<and> 
      (\<langle>c\<^sub>A,mds\<^sub>A,mem\<^sub>1\<^sub>A\<rangle>\<^sub>A,\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<and> (\<langle>c\<^sub>A,mds\<^sub>A,mem\<^sub>2\<^sub>A\<rangle>\<^sub>A,\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<longrightarrow>
           (stops\<^sub>C \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C = stops\<^sub>C \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<and>
           (abs_steps \<langle>c\<^sub>A,mds\<^sub>A,mem\<^sub>1\<^sub>A\<rangle>\<^sub>A \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C = abs_steps \<langle>c\<^sub>A,mds\<^sub>A,mem\<^sub>2\<^sub>A\<rangle>\<^sub>A \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<and>
           (\<forall>mds\<^sub>1\<^sub>C' mds\<^sub>2\<^sub>C' mem\<^sub>1\<^sub>C' mem\<^sub>2\<^sub>C' c\<^sub>1\<^sub>C' c\<^sub>2\<^sub>C'. \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>1\<^sub>C', mds\<^sub>1\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C  \<and>
                                          \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>2\<^sub>C', mds\<^sub>2\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C \<longrightarrow>
                                          c\<^sub>1\<^sub>C' = c\<^sub>2\<^sub>C' \<and> mds\<^sub>1\<^sub>C' = mds\<^sub>2\<^sub>C')"

definition
  secure_refinement_simple
where
  "secure_refinement_simple \<R>\<^sub>A \<R> abs_steps \<equiv>
  closed_others \<R> \<and>
  preserves_modes_mem \<R> \<and>
  new_vars_private \<R> \<and>
  simple_refinement_safe \<R>\<^sub>A \<R> abs_steps \<and>
  bisim_simple \<R>\<^sub>A \<and>
  (\<forall> c\<^sub>1\<^sub>A mds\<^sub>A mem\<^sub>1\<^sub>A c\<^sub>1\<^sub>C mds\<^sub>C mem\<^sub>1\<^sub>C. 
   (\<langle> c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C) \<in> \<R> \<longrightarrow>
    (\<forall> c\<^sub>1\<^sub>C' mds\<^sub>C' mem\<^sub>1\<^sub>C'. \<langle> c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C \<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C \<longrightarrow>
     (\<exists> c\<^sub>1\<^sub>A' mds\<^sub>A' mem\<^sub>1\<^sub>A'. abs.neval \<langle> c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A \<rangle>\<^sub>A (abs_steps \<langle>c\<^sub>1\<^sub>A,mds\<^sub>A,mem\<^sub>1\<^sub>A\<rangle>\<^sub>A \<langle>c\<^sub>1\<^sub>C,mds\<^sub>C,mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<langle> c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A' \<rangle>\<^sub>A \<and>
                   (\<langle> c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A' \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C' \<rangle>\<^sub>C) \<in> \<R>)))"

definition
  \<I>simple
where
  "\<I>simple \<equiv> {(\<langle>c,mds,mem\<rangle>\<^sub>C,\<langle>c',mds',mem'\<rangle>\<^sub>C)| c mds mem c' mds' mem'. c = c'}"

lemma \<I>simple_closed_glob_consistent:
  "conc.closed_glob_consistent \<I>simple"
  by(auto simp: conc.closed_glob_consistent_def \<I>simple_def)
  
lemma secure_refinement_simple:
  assumes srs: "secure_refinement_simple \<R>\<^sub>A \<R> abs_steps"
  shows "secure_refinement_simpler \<R>\<^sub>A \<R> \<I>simple abs_steps"
unfolding secure_refinement_simpler_def
proof(safe | clarsimp)+
  from srs show "closed_others \<R>"
  unfolding secure_refinement_simple_def by blast
next
  from srs show "preserves_modes_mem \<R>"
  unfolding secure_refinement_simple_def by blast
next
  from srs show "new_vars_private \<R>"
  unfolding secure_refinement_simple_def by blast
next
  show "conc.closed_glob_consistent \<I>simple" by (rule \<I>simple_closed_glob_consistent)
next
  from srs have safe: "simple_refinement_safe \<R>\<^sub>A \<R> abs_steps"
  unfolding secure_refinement_simple_def by blast
  from srs have simple: "bisim_simple \<R>\<^sub>A"
  unfolding secure_refinement_simple_def by fastforce
  
  from safe simple show "simpler_refinement_safe \<R>\<^sub>A \<R> \<I>simple abs_steps"
  by(fastforce simp: simpler_refinement_safe_def \<I>simple_def simple_refinement_safe_def bisim_simple_def)
next
  fix c\<^sub>1\<^sub>A mds\<^sub>A mem\<^sub>1\<^sub>A c\<^sub>1\<^sub>C mds\<^sub>C mem\<^sub>1\<^sub>C c\<^sub>1\<^sub>C' mds\<^sub>C' mem\<^sub>1\<^sub>C'
  show " (\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<Longrightarrow>
       \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C \<Longrightarrow>
       \<exists>c\<^sub>1\<^sub>A' mds\<^sub>A' mem\<^sub>1\<^sub>A'.
          abs.neval \<langle>c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A (abs_steps \<langle>c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C)
           \<langle>c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A \<and>
          (\<langle>c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> \<R>"
    using srs unfolding secure_refinement_simple_def by blast
qed
  
section "Sound Mode Use Preservation"

text \<open>
  Prove that
  \begin{quote}
  acquiring a mode on the concrete version of an abstract
      variable~@{term x}, and then mapping the new concrete mode state to the
      corresponding abstract mode state,
  \end{quote}
   is equivalent to
   \begin{quote}
      first mapping the initial concrete mode
      state to its corresponding abstract mode state and then acquiring the mode
      on the abstract variable~@{term x}.
   \end{quote}

   This lemma essentially justifies why a concrete program doing
   @{term "Acq (var\<^sub>C_of x) SomeMode"}
   is a the right way to implement the abstract program doing
   @{term "Acq x SomeMode"}.
\<close>

(* FIXME: There might be better names for these *)
lemma mode_acquire_refinement_helper:
  "mds\<^sub>A_of (mds\<^sub>C(SomeMode := insert (var\<^sub>C_of x) (mds\<^sub>C SomeMode))) =
   (mds\<^sub>A_of mds\<^sub>C)(SomeMode := insert x (mds\<^sub>A_of mds\<^sub>C SomeMode))"
  apply(clarsimp simp: mds\<^sub>A_of_def)
  apply(rule ext)
  apply(force simp: image_def inv_f_f[OF var\<^sub>C_of_inj])
  done

lemma mode_release_refinement_helper:
  "mds\<^sub>A_of (mds\<^sub>C(SomeMode := {y \<in> mds\<^sub>C SomeMode. y \<noteq> (var\<^sub>C_of x)})) =
   (mds\<^sub>A_of mds\<^sub>C)(SomeMode := {y \<in> (mds\<^sub>A_of mds\<^sub>C SomeMode). y \<noteq> x})"
  apply(clarsimp simp: mds\<^sub>A_of_def)
  apply(rule ext)
  apply (force simp: image_def inv_f_f[OF var\<^sub>C_of_inj])
  done

definition
  preserves_locally_sound_mode_use :: "('Com\<^sub>A, 'Var\<^sub>A, 'Val, 'Com\<^sub>C, 'Var\<^sub>C) state_relation \<Rightarrow> bool"
where
  "preserves_locally_sound_mode_use \<R> \<equiv>
   \<forall>lc\<^sub>A lc\<^sub>C.
      (abs.locally_sound_mode_use lc\<^sub>A \<and> (lc\<^sub>A, lc\<^sub>C) \<in> \<R> \<longrightarrow>
      conc.locally_sound_mode_use lc\<^sub>C)"

lemma secure_refinement_loc_reach:
  assumes rr: "secure_refinement \<R>\<^sub>A \<R> P"
  assumes in_\<R>:  "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> \<R>"
  assumes loc_reach\<^sub>C: "\<langle>c\<^sub>C', mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C \<in> conc.loc_reach \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C"
  shows "\<exists>c\<^sub>A' mds\<^sub>A' mem\<^sub>A'.
      (\<langle>c\<^sub>A', mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>C', mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> \<R> \<and>
      \<langle>c\<^sub>A', mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A \<in> abs.loc_reach \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A"
using loc_reach\<^sub>C proof(induct rule: conc.loc_reach.induct)
  case (refl) show ?case
    using in_\<R> abs.loc_reach.refl by force
next
  case (step c\<^sub>C' mds\<^sub>C' mem\<^sub>C' c\<^sub>C'' mds\<^sub>C'' mem\<^sub>C'')
  from step(2) obtain c\<^sub>A' mds\<^sub>A' mem\<^sub>A' where 
    in_\<R>': "(\<langle>c\<^sub>A', mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>C', mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> \<R>" and 
    loc_reach\<^sub>A: "\<langle>c\<^sub>A', mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A \<in> abs.loc_reach \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A "
    by blast
  from rr in_\<R>' step(3)
  obtain n c\<^sub>A'' mds\<^sub>A'' mem\<^sub>A'' where 
    neval\<^sub>A: "abs.neval \<langle> c\<^sub>A', mds\<^sub>A', mem\<^sub>A' \<rangle>\<^sub>A n \<langle> c\<^sub>A'', mds\<^sub>A'', mem\<^sub>A'' \<rangle>\<^sub>A" and
    in_\<R>'': "(\<langle> c\<^sub>A'', mds\<^sub>A'', mem\<^sub>A'' \<rangle>\<^sub>A, \<langle> c\<^sub>C'', mds\<^sub>C'', mem\<^sub>C'' \<rangle>\<^sub>C) \<in> \<R>"
    unfolding secure_refinement_def by blast
  from neval\<^sub>A loc_reach\<^sub>A have "\<langle>c\<^sub>A'', mds\<^sub>A'', mem\<^sub>A''\<rangle>\<^sub>A \<in> abs.loc_reach \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A"
    using abs.neval_loc_reach
    by blast
  with in_\<R>'' show ?case by blast
next
  case (mem_diff c\<^sub>C' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C'')
  from mem_diff(2) obtain c\<^sub>A' mds\<^sub>A' mem\<^sub>A' where 
    in_\<R>': "(\<langle>c\<^sub>A', mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>C', mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> \<R>" and 
    loc_reach\<^sub>A: "\<langle>c\<^sub>A', mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A \<in> abs.loc_reach \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A "
    by blast
  from rr have mm: "preserves_modes_mem \<R>" and co: "closed_others \<R>"
    unfolding secure_refinement_def by blast+
  from preserves_modes_memD[OF mm in_\<R>'] have 
    mem\<^sub>A'_def: "mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C'" and mds\<^sub>A'_def: "mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C'"
    by simp+
  hence in_\<R>': "(\<langle>c\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C', mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> \<R>"
   and loc_reach\<^sub>A: "(\<langle>c\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A) \<in> abs.loc_reach \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A"
    using in_\<R>' loc_reach\<^sub>A by simp+
  with mem_diff(3) co
  have "(\<langle>c\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of mem\<^sub>C''\<rangle>\<^sub>A, \<langle>c\<^sub>C', mds\<^sub>C', mem\<^sub>C''\<rangle>\<^sub>C) \<in> \<R>"
    unfolding closed_others_def by blast
  moreover have "\<langle>c\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of mem\<^sub>C''\<rangle>\<^sub>A \<in> abs.loc_reach \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A"
    apply(rule abs.loc_reach.mem_diff)
     apply(rule loc_reach\<^sub>A)
    using mem_diff(3)
    using calculation in_\<R>' in_\<R>_dma' mem\<^sub>A_of_def mm var_writable\<^sub>A by fastforce 
  ultimately show ?case by blast
qed

definition preserves_local_guarantee_compliance ::
  "('Com\<^sub>A, 'Var\<^sub>A, 'Val, 'Com\<^sub>C, 'Var\<^sub>C) state_relation \<Rightarrow> bool"
where
  "preserves_local_guarantee_compliance \<R> \<equiv>
    \<forall>cm\<^sub>A mem\<^sub>A cm\<^sub>C mem\<^sub>C.
      abs.respects_own_guarantees cm\<^sub>A \<and>
      ((cm\<^sub>A, mem\<^sub>A), (cm\<^sub>C, mem\<^sub>C)) \<in> \<R> \<longrightarrow>
        conc.respects_own_guarantees cm\<^sub>C"

lemma preserves_local_guarantee_compliance_def2:
  "preserves_local_guarantee_compliance \<R> \<equiv>
    \<forall>c\<^sub>A mds\<^sub>A mem\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>C.
      abs.respects_own_guarantees (c\<^sub>A, mds\<^sub>A) \<and>
      (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<longrightarrow>
        conc.respects_own_guarantees (c\<^sub>C, mds\<^sub>C)"
  unfolding preserves_local_guarantee_compliance_def
  by simp

(* This lemma proves it is sufficient to require a refinement relation to preserve
   guarantee compliance to ensure that it also preserves locally sound mode use.
  TODO: Should preserves_guarantee_compliance become part of secure_refinement's requirements? *)
lemma locally_sound_mode_use_preservation:
  assumes rr: "secure_refinement \<R>\<^sub>A \<R> P"
  assumes preserves_guarantee_compliance: "preserves_local_guarantee_compliance \<R>"
  shows "preserves_locally_sound_mode_use \<R>"
  unfolding preserves_locally_sound_mode_use_def
proof(clarsimp)
  fix c\<^sub>A mds\<^sub>A mem\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>C
  assume locally_sound\<^sub>A: "abs.locally_sound_mode_use \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A" and
         in_\<R>: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> \<R>"
 
  show "conc.locally_sound_mode_use \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C"
    unfolding conc.locally_sound_mode_use_def2
    proof(clarsimp)
      fix c\<^sub>C' mds\<^sub>C' mem\<^sub>C'
      assume loc_reach\<^sub>C: "\<langle>c\<^sub>C', mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C \<in> conc.loc_reach \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C"

      from rr in_\<R> loc_reach\<^sub>C
      obtain c\<^sub>A' mds\<^sub>A' mem\<^sub>A' where
        in_\<R>': "(\<langle>c\<^sub>A', mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>C', mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> \<R>" and
        loc_reach\<^sub>A: "\<langle>c\<^sub>A', mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A \<in> abs.loc_reach \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A"
        using secure_refinement_loc_reach by blast

      from locally_sound\<^sub>A loc_reach\<^sub>A
      have respects_guarantees\<^sub>A': "abs.respects_own_guarantees (c\<^sub>A', mds\<^sub>A')"
        unfolding abs.locally_sound_mode_use_def2 by auto

      with preserves_guarantee_compliance in_\<R>'
      show "conc.respects_own_guarantees (c\<^sub>C', mds\<^sub>C')"
        unfolding preserves_local_guarantee_compliance_def by blast
    qed
qed

end

section "Refinement without changing the Memory Model"

text \<open>
  Here we define a locale which restricts the refinement to be between an abstract and
  concrete programs that share identical memory models: i,e. have the same set of variables.
  This allows us to derive simpler versions of the conditions that are likely to be easier
  to work with for initial experimentation.
\<close>
locale sifum_refinement_same_mem = 
  abs: sifum_security dma \<C>_vars \<C> eval\<^sub>A some_val +
  conc: sifum_security dma \<C>_vars \<C> eval\<^sub>C some_val
  for dma :: "('Var,'Val) Mem \<Rightarrow> 'Var \<Rightarrow> Sec"
  and \<C>_vars :: "'Var \<Rightarrow> 'Var set"
  and \<C> :: "'Var set"
  and eval\<^sub>A :: "('Com\<^sub>A, 'Var, 'Val) LocalConf rel"
  and eval\<^sub>C :: "('Com\<^sub>C, 'Var, 'Val) LocalConf rel"
  and some_val :: "'Val" 

sublocale sifum_refinement_same_mem \<subseteq> 
          gen_refine: sifum_refinement dma dma \<C>_vars \<C>_vars \<C> \<C> eval\<^sub>A eval\<^sub>C some_val id
  by(unfold_locales, simp_all)

context sifum_refinement_same_mem begin

lemma [simp]:
  "gen_refine.new_vars_private \<R>"
  unfolding gen_refine.new_vars_private_def
  by simp

definition
  preserves_modes_mem :: "('Com\<^sub>A, 'Var, 'Val, 'Com\<^sub>C, 'Var) state_relation \<Rightarrow> bool"
where
  "preserves_modes_mem \<R> \<equiv> 
  (\<forall> c\<^sub>A mds\<^sub>A mem\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>C. (\<langle> c\<^sub>A, mds\<^sub>A, mem\<^sub>A \<rangle>\<^sub>A, \<langle> c\<^sub>C, mds\<^sub>C, mem\<^sub>C \<rangle>\<^sub>C) \<in> \<R> \<longrightarrow>
      mem\<^sub>A = mem\<^sub>C \<and> mds\<^sub>A = mds\<^sub>C)"


definition
  closed_others :: "('Com\<^sub>A, 'Var, 'Val, 'Com\<^sub>C, 'Var) state_relation \<Rightarrow> bool"
where
  "closed_others \<R> \<equiv> 
  (\<forall> c\<^sub>A mds mem c\<^sub>C mem'. (\<langle> c\<^sub>A, mds, mem \<rangle>\<^sub>A, \<langle> c\<^sub>C, mds, mem \<rangle>\<^sub>C) \<in> \<R> \<longrightarrow>
   (\<forall>x. mem x \<noteq> mem' x \<longrightarrow> \<not> var_asm_not_written mds x) \<longrightarrow>
   (\<forall>x. dma mem x \<noteq> dma mem' x \<longrightarrow> \<not> var_asm_not_written mds x) \<longrightarrow>
         (\<langle> c\<^sub>A, mds, mem' \<rangle>\<^sub>A, \<langle> c\<^sub>C, mds, mem' \<rangle>\<^sub>C) \<in> \<R>)"

lemma [simp]:
  "gen_refine.mds\<^sub>A_of x = x"
  by(simp add: gen_refine.mds\<^sub>A_of_def)

lemma [simp]:
  "gen_refine.mem\<^sub>A_of x = x"
  by(simp add: gen_refine.mem\<^sub>A_of_def)

lemma [simp]:
  "preserves_modes_mem \<R> \<Longrightarrow>
  gen_refine.closed_others \<R> = closed_others \<R>"
  unfolding closed_others_def
            gen_refine.closed_others_def
            preserves_modes_mem_def
  by auto

lemma [simp]:
  "gen_refine.preserves_modes_mem \<R> = preserves_modes_mem \<R>"
  unfolding gen_refine.preserves_modes_mem_def2 preserves_modes_mem_def
  by simp

definition
  secure_refinement :: "('Com\<^sub>A, 'Var, 'Val) LocalConf rel \<Rightarrow> ('Com\<^sub>A, 'Var, 'Val, 'Com\<^sub>C, 'Var) state_relation \<Rightarrow> 
                          ('Com\<^sub>C, 'Var, 'Val) LocalConf rel \<Rightarrow> bool"
where
  "secure_refinement \<R>\<^sub>A \<R> P \<equiv>
  closed_others \<R> \<and>
  preserves_modes_mem \<R> \<and>
  conc.closed_glob_consistent P \<and>
  (\<forall> c\<^sub>1\<^sub>A mds mem\<^sub>1 c\<^sub>1\<^sub>C. 
   (\<langle> c\<^sub>1\<^sub>A, mds, mem\<^sub>1 \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C, mds, mem\<^sub>1 \<rangle>\<^sub>C) \<in> \<R> \<longrightarrow>
    (\<forall> c\<^sub>1\<^sub>C' mds' mem\<^sub>1'. \<langle> c\<^sub>1\<^sub>C, mds, mem\<^sub>1 \<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle> c\<^sub>1\<^sub>C', mds', mem\<^sub>1' \<rangle>\<^sub>C \<longrightarrow>
     (\<exists> n c\<^sub>1\<^sub>A'. abs.neval \<langle> c\<^sub>1\<^sub>A, mds, mem\<^sub>1 \<rangle>\<^sub>A n \<langle> c\<^sub>1\<^sub>A', mds', mem\<^sub>1' \<rangle>\<^sub>A \<and>
                   (\<langle> c\<^sub>1\<^sub>A', mds', mem\<^sub>1' \<rangle>\<^sub>A, \<langle> c\<^sub>1\<^sub>C', mds', mem\<^sub>1' \<rangle>\<^sub>C) \<in> \<R> \<and>
       (\<forall>c\<^sub>2\<^sub>A mem\<^sub>2 c\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2'. 
         (\<langle> c\<^sub>1\<^sub>A, mds, mem\<^sub>1 \<rangle>\<^sub>A, \<langle> c\<^sub>2\<^sub>A, mds, mem\<^sub>2 \<rangle>\<^sub>A) \<in> \<R>\<^sub>A \<and>
         (\<langle> c\<^sub>2\<^sub>A, mds, mem\<^sub>2 \<rangle>\<^sub>A, \<langle> c\<^sub>2\<^sub>C, mds, mem\<^sub>2 \<rangle>\<^sub>C) \<in> \<R> \<and>
         (\<langle>c\<^sub>1\<^sub>C, mds, mem\<^sub>1\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds, mem\<^sub>2\<rangle>\<^sub>C) \<in> P  \<and>
         abs.neval \<langle> c\<^sub>2\<^sub>A, mds, mem\<^sub>2 \<rangle>\<^sub>A n \<langle> c\<^sub>2\<^sub>A', mds', mem\<^sub>2' \<rangle>\<^sub>A  \<longrightarrow>
           (\<exists> c\<^sub>2\<^sub>C' . \<langle> c\<^sub>2\<^sub>C, mds, mem\<^sub>2 \<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle> c\<^sub>2\<^sub>C', mds', mem\<^sub>2' \<rangle>\<^sub>C \<and>
                   (\<langle> c\<^sub>2\<^sub>A', mds', mem\<^sub>2' \<rangle>\<^sub>A, \<langle> c\<^sub>2\<^sub>C', mds', mem\<^sub>2' \<rangle>\<^sub>C) \<in> \<R> \<and>
                   (\<langle>c\<^sub>1\<^sub>C', mds', mem\<^sub>1'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds', mem\<^sub>2'\<rangle>\<^sub>C) \<in> P )))))"

lemma preserves_modes_memD:
  "preserves_modes_mem \<R> \<Longrightarrow>
(\<langle> c\<^sub>A, mds\<^sub>A, mem\<^sub>A \<rangle>\<^sub>A, \<langle> c\<^sub>C, mds\<^sub>C, mem\<^sub>C \<rangle>\<^sub>C) \<in> \<R> \<Longrightarrow>
      mem\<^sub>A = mem\<^sub>C \<and> mds\<^sub>A = mds\<^sub>C"
  by(auto simp: preserves_modes_mem_def)

lemma [simp]:
  "gen_refine.secure_refinement \<R>\<^sub>A \<R> P = secure_refinement \<R>\<^sub>A \<R> P"
  unfolding gen_refine.secure_refinement_def secure_refinement_def
  apply safe
         apply fastforce
        apply fastforce
       defer
       apply fastforce
      apply fastforce
     apply fastforce
    defer
   apply ((drule spec)+, erule (1) impE)
   apply ((drule spec)+, erule (1) impE)
   apply (clarify)
   apply(rename_tac  n c\<^sub>1\<^sub>A' mds\<^sub>A' mem\<^sub>1\<^sub>A')
   apply(rule_tac x=n in exI)
   apply(rule_tac x=c\<^sub>1\<^sub>A' in exI)
   apply(fastforce dest: preserves_modes_memD)
  apply (frule (1) preserves_modes_memD)
  apply clarify
  apply ((drule spec)+, erule (1) impE)
  apply ((drule spec)+, erule (1) impE)
  apply clarify
  apply(blast dest: preserves_modes_memD)
  done
  
lemma R\<^sub>C_of_strong_low_bisim_mm:
  assumes abs: "abs.strong_low_bisim_mm \<R>\<^sub>A"
  assumes rr: "secure_refinement \<R>\<^sub>A \<R> P"
  assumes P_sym: "sym P"
  shows "conc.strong_low_bisim_mm (gen_refine.R\<^sub>C_of \<R>\<^sub>A \<R> P)"
  using abs rr gen_refine.R\<^sub>C_of_strong_low_bisim_mm[OF _ _ P_sym]
  by simp

end

context sifum_refinement begin
lemma use_secure_refinement_helper:
  "secure_refinement \<R>\<^sub>A \<R> P \<Longrightarrow>
   ((cm\<^sub>A,mem\<^sub>A),(cm\<^sub>C,mem\<^sub>C)) \<in> \<R> \<Longrightarrow> (cm\<^sub>C,mem\<^sub>C) \<leadsto>\<^sub>C (cm\<^sub>C',mem\<^sub>C') \<Longrightarrow>
   (\<exists>cm\<^sub>A' mem\<^sub>A' n. abs.neval (cm\<^sub>A,mem\<^sub>A) n (cm\<^sub>A',mem\<^sub>A') \<and>
                 ((cm\<^sub>A',mem\<^sub>A'), (cm\<^sub>C',mem\<^sub>C')) \<in> \<R>)"
  apply(case_tac cm\<^sub>A, case_tac cm\<^sub>C)
  apply clarsimp
  apply(clarsimp simp: secure_refinement_def)
  by (metis surjective_pairing)
  
lemma closed_othersD:
  "closed_others \<R> \<Longrightarrow>
   (\<langle>c\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> \<R> \<Longrightarrow>
   (\<And>x. mem\<^sub>C' x \<noteq> mem\<^sub>C x \<or> dma\<^sub>C mem\<^sub>C' x \<noteq> dma\<^sub>C mem\<^sub>C x \<Longrightarrow> \<not> var_asm_not_written mds\<^sub>C x) \<Longrightarrow>
   (\<langle>c\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> \<R>"
   unfolding closed_others_def
   by auto
end

record ('a, 'Val, 'Var\<^sub>C, 'Com\<^sub>C, 'Var\<^sub>A, 'Com\<^sub>A) componentwise_refinement =
  priv_mem :: "'Var\<^sub>C set" (* private variables *)
  \<R>\<^sub>A_rel :: "('Com\<^sub>A, 'Var\<^sub>A, 'Val) LocalConf rel" (* abstract bisimulation *)
  \<R>_rel :: "('Com\<^sub>A, 'Var\<^sub>A, 'Val, 'Com\<^sub>C, 'Var\<^sub>C) state_relation" (* refinement relation *)
  P_rel :: "('Com\<^sub>C, 'Var\<^sub>C, 'Val) LocalConf rel"

section "Whole System Refinement"

text \<open>
  A locale to capture componentwise refinement of an entire system.
\<close>
locale sifum_refinement_sys = 
  sifum_refinement dma\<^sub>A dma\<^sub>C \<C>_vars\<^sub>A \<C>_vars\<^sub>C \<C>\<^sub>A \<C>\<^sub>C eval\<^sub>A eval\<^sub>C some_val var\<^sub>C_of
  for dma\<^sub>A :: "('Var\<^sub>A,'Val) Mem \<Rightarrow> 'Var\<^sub>A \<Rightarrow> Sec"
  and dma\<^sub>C :: "('Var\<^sub>C,'Val) Mem \<Rightarrow> 'Var\<^sub>C \<Rightarrow> Sec"
  and \<C>_vars\<^sub>A :: "'Var\<^sub>A \<Rightarrow> 'Var\<^sub>A set"
  and \<C>_vars\<^sub>C :: "'Var\<^sub>C \<Rightarrow> 'Var\<^sub>C set"
  and \<C>\<^sub>A :: "'Var\<^sub>A set"
  and \<C>\<^sub>C :: "'Var\<^sub>C set"
  and eval\<^sub>A :: "('Com\<^sub>A, 'Var\<^sub>A, 'Val) LocalConf rel"
  and eval\<^sub>C :: "('Com\<^sub>C, 'Var\<^sub>C, 'Val) LocalConf rel"
  and some_val :: "'Val"
  and var\<^sub>C_of :: "'Var\<^sub>A \<Rightarrow> 'Var\<^sub>C" +
  fixes cms :: "('a::wellorder, 'Val, 'Var\<^sub>C, 'Com\<^sub>C, 'Var\<^sub>A, 'Com\<^sub>A) componentwise_refinement list" 
  fixes priv_mem\<^sub>C :: "'Var\<^sub>C set list"
  defines priv_mem\<^sub>C_def: "priv_mem\<^sub>C \<equiv> map priv_mem cms"
  assumes priv_mem_disjoint: "i < length cms \<Longrightarrow> j < length cms \<Longrightarrow> i \<noteq> j \<Longrightarrow> priv_mem\<^sub>C ! i \<inter> priv_mem\<^sub>C ! j = {}"
  assumes new_vars_priv: "- range var\<^sub>C_of = \<Union> (set priv_mem\<^sub>C)"
  assumes new_privs_preserved: "\<langle>c, mds, mem\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c', mds', mem'\<rangle>\<^sub>C \<Longrightarrow> x \<notin> range var\<^sub>C_of \<Longrightarrow>
                                 (x \<in> mds m) = (x \<in> mds' m)"
  assumes secure_refinements: 
    "i < length cms \<Longrightarrow> secure_refinement (\<R>\<^sub>A_rel (cms ! i)) (\<R>_rel (cms ! i)) (P_rel (cms ! i))"
  assumes local_guarantee_preservation:
    "i < length cms \<Longrightarrow> preserves_local_guarantee_compliance (\<R>_rel (cms ! i))"
  assumes bisims:
    "i < length cms \<Longrightarrow> abs.strong_low_bisim_mm (\<R>\<^sub>A_rel (cms ! i))"
  assumes Ps_sym:
    "\<And>a b. i < length cms \<Longrightarrow> sym (P_rel (cms ! i))"
  assumes Ps_refl_on_low_mds_eq:
    "i < length cms \<Longrightarrow> conc.low_mds_eq mds\<^sub>C mem\<^sub>C mem\<^sub>C' \<Longrightarrow> (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> (P_rel (cms ! i))" 

(* FIXME: move to a parent theory? *)
context sifum_security begin
lemma neval_modifies_helper:
  assumes nevaln: "neval lcn m lcn'"
  assumes lcn_def: "lcn = (cms ! n, mem)"
  assumes lcn'_def: "lcn' = (cmn', mem')"
  assumes len: "n < length cms"
  assumes modified: "mem x \<noteq> mem' x \<or> dma mem x \<noteq> dma mem' x"
  shows "\<exists>k cmn'' mem'' cmn''' mem'''. k < m \<and> neval (cms ! n,mem) k (cmn'',mem'') \<and>
                           (cmn'',mem'') \<leadsto> (cmn''', mem''') \<and>
                           (mem'' x \<noteq> mem''' x \<or> dma mem'' x \<noteq> dma mem''' x)"
using nevaln lcn_def lcn'_def modified len
proof(induct arbitrary: cms cmn' mem mem' rule: neval.induct)
  case (neval_0 lcn lcn')
    from neval_0 show ?case by simp
  next
  case (neval_S_n lcn lcn'' m lcn')
  obtain cmn'' mem'' where lcn''_def: "lcn'' = (cmn'', mem'')" by fastforce
  show ?case
  proof(cases "mem x \<noteq> mem'' x \<or> dma mem x \<noteq> dma mem'' x")    
    assume a: "mem x \<noteq> mem'' x \<or> dma mem x \<noteq> dma mem'' x"
    let ?k = "0::nat"
    let ?cmn'' = "cms ! n"
    let ?mem'' = "mem"
    have "?k < Suc m \<and>
    neval (cms ! n, mem) ?k (?cmn'', ?mem'') \<and>
    (?cmn'', ?mem'') \<leadsto> (cmn'', mem'') \<and> (?mem'' x \<noteq> mem'' x \<or>
    dma ?mem'' x \<noteq> dma mem'' x)"
      apply (rule conjI, simp add: neval.neval_0)+
      apply (simp only: a)
      by (simp add: neval_S_n(1)[simplified neval_S_n lcn''_def])
    thus ?case by blast
  next
    assume a: "\<not> (mem x \<noteq> mem'' x \<or> dma mem x \<noteq> dma mem'' x)"
    hence unchanged: "mem'' x = mem x \<and> dma mem'' x = dma mem x"
      by (blast intro: sym)
    define cms'' where "cms'' = cms[n := cmn'']"
    have len'': "n < length cms''"
      by(simp add: cms''_def neval_S_n)
    hence lcn''_def2: "lcn'' = (cms'' ! n, mem'')"
      by(simp add: lcn''_def cms''_def)
    from
    neval_S_n(3)[OF lcn''_def2 neval_S_n(5), simplified unchanged neval_S_n len'']
    obtain k cmn''' mem''' cmn'''' mem'''' where
      hyp:    "k < m \<and>
          neval (cms'' ! n, mem'') k (cmn''', mem''') \<and>
          (cmn''', mem''') \<leadsto> (cmn'''', mem'''') \<and>
          (mem''' x \<noteq> mem'''' x \<or> dma mem''' x \<noteq> dma mem'''' x)"
      by blast
    have "neval (cms ! n, mem) (Suc k) (cmn''', mem''')"           
      apply(rule neval.neval_S_n)  
       prefer 2
       using hyp apply fastforce 
      apply(simp add: cms''_def neval_S_n)
      by(rule neval_S_n(1)[simplified neval_S_n lcn''_def])
    moreover have "Suc k < Suc m" using hyp by auto
    ultimately show ?case using hyp by fastforce
  qed
qed

lemma neval_sched_Nil [simp]:
  "(cms, mem) \<rightarrow>\<^bsub>[]\<^esub> (cms, mem)"
  by simp
  
lemma reachable_mode_states_refl:
  "map snd cms \<in> reachable_mode_states (cms, mem)"
  apply(clarsimp simp: reachable_mode_states_def)
  using neval_sched_Nil by blast
  
lemma neval_reachable_mode_states:
  assumes neval: "neval lc n lc'"
  assumes lc_def: "lc = (cms ! k, mem)" 
  assumes len: "k < length cms"
  shows "map snd (cms[k := (fst lc')]) \<in> reachable_mode_states (cms, mem)"
using neval lc_def len proof(induct arbitrary: cms mem rule: neval.induct)
case (neval_0 x y)
  thus ?case
  apply simp
  apply(drule sym, simp add: len reachable_mode_states_refl)
  done
next
case (neval_S_n x y n z)
  define cms' where "cms' = cms[k := fst y]"
  define mem' where "mem' = snd y"
  have y_def: "y = (cms' ! k, mem')"
    by(simp add: cms'_def mem'_def neval_S_n)
  moreover have len': "k < length cms'"
    by(simp add: cms'_def neval_S_n)
  ultimately have hyp: "map snd (cms'[k := fst z]) \<in> reachable_mode_states (cms', mem')"
    using neval_S_n by metis
  have "map snd (cms'[k := fst z]) = map snd (cms[k := fst z])"
    unfolding cms'_def
    by simp
  moreover have "(cms, mem) \<leadsto>\<^bsub>k\<^esub> (cms', mem')"
    using meval_intro neval_S_n y_def cms'_def mem'_def len' by fastforce 
  ultimately show ?case
  using reachable_modes_subset subsetD hyp by fastforce
qed


lemma meval_sched_sound_mode_use:
  "sound_mode_use gc \<Longrightarrow> meval_sched sched gc gc' \<Longrightarrow> sound_mode_use gc'"
proof(induct rule: meval_sched.induct)
case (1 gc)
  thus ?case by simp
next
case (2 n ns gc gc')
  from 2(3) obtain gc'' where "meval_abv gc n gc''" and a: "meval_sched ns gc'' gc'" by force
  with 2(2) sound_modes_invariant have b: "sound_mode_use gc''" by (metis surjective_pairing)
  show ?case by (rule 2(1)[OF b a])
qed

lemma neval_meval:
  "neval lcn k lcn' \<Longrightarrow> n < length cms \<Longrightarrow> lcn = (cms ! n,mem) \<Longrightarrow> lcn' = (cmn', mem') \<Longrightarrow>
  meval_sched (replicate k n) (cms,mem) (cms[n := cmn'],mem')"
proof(induct arbitrary: cms mem cmn' mem' rule: neval.induct)
case (neval_0 lcn lcn')  
  thus ?case by fastforce
next
case (neval_S_n lcn lcn'' k lcn')
  define cms'' where [simp]: "cms'' = cms[n := fst lcn'']"
  define mem'' where [simp]: "mem'' = snd lcn''"
  have len'' [simp]: "n < length cms''" by(simp add: neval_S_n(4))
  have lcn''_def: "lcn'' = (cms'' ! n, mem'')" using len'' by simp
  have hyp: "(cms'', mem'') \<rightarrow>\<^bsub>replicate k n\<^esub> (cms''[n := cmn'], mem')"
    by (rule neval_S_n(3)[OF len'' lcn''_def neval_S_n(6)])
  have meval: "(cms, mem) \<leadsto>\<^bsub>n\<^esub> (cms'', mem'')"
    using cms''_def neval_S_n.hyps(1) neval_S_n.prems(1) neval_S_n.prems(2) by fastforce
  from hyp meval show ?case
    by fastforce
qed

lemma meval_sched_app:
  "meval_sched as gc gc' \<Longrightarrow> meval_sched bs gc' gc'' \<Longrightarrow> meval_sched (as@bs) gc gc''"
proof(induct as arbitrary: gc gc' bs)
case Nil thus ?case by simp
next
case (Cons a as)
  from Cons(2) 
  obtain gc''' where a: "meval_abv gc a gc'''" and as: "meval_sched as gc''' gc'" by force
  from Cons(1)[OF as Cons(3)] a
  have "gc \<rightarrow>\<^bsub>a # (as @ bs)\<^esub> gc''"
    by (metis meval_sched.simps)
  thus ?case by simp
qed

end

context sifum_refinement_sys begin

lemma conc_respects_priv:
  assumes xnin: "x\<^sub>C \<notin> range var\<^sub>C_of"
  assumes modified\<^sub>C: "mem\<^sub>C x\<^sub>C \<noteq> mem\<^sub>C' x\<^sub>C \<or> dma\<^sub>C mem\<^sub>C x\<^sub>C \<noteq> dma\<^sub>C mem\<^sub>C' x\<^sub>C"
  assumes eval\<^sub>C: "(cms\<^sub>C ! n, mem\<^sub>C) \<leadsto>\<^sub>C (cm\<^sub>Cn', mem\<^sub>C')"
  assumes in_\<R>n: "((cms\<^sub>A ! n, mem\<^sub>A), cms\<^sub>C ! n, mem\<^sub>C) \<in> \<R>n"
  assumes preserves: "preserves_local_guarantee_compliance \<R>n"
  assumes sound_mode_use\<^sub>A: "abs.sound_mode_use (cms\<^sub>A, mem\<^sub>A)"
  assumes nlen: "n < length cms"
  assumes len_eq: "length cms\<^sub>A = length cms"
  assumes len_eq': "length cms\<^sub>C = length cms"
  shows "x\<^sub>C \<notin> (snd (cms\<^sub>C ! n)) GuarNoWrite \<and> x\<^sub>C \<notin> (snd (cms\<^sub>C ! n)) GuarNoReadOrWrite"
proof -
  from sound_mode_use\<^sub>A have "abs.respects_own_guarantees (cms\<^sub>A ! n)"
    using nlen len_eq abs.locally_sound_respects_guarantees 
    unfolding abs.sound_mode_use_def list_all_length
    by fastforce
  with in_\<R>n have 1: "conc.respects_own_guarantees (cms\<^sub>C ! n)"
    using preserves
    unfolding preserves_local_guarantee_compliance_def
    by metis
  with eval\<^sub>C modified\<^sub>C have 2: "\<not> conc.doesnt_modify (fst (cms\<^sub>C ! n)) x\<^sub>C"
    unfolding conc.doesnt_modify_def
    by (metis surjective_pairing)
  then have "\<not> conc.doesnt_read_or_modify (fst (cms\<^sub>C ! n)) x\<^sub>C"
    using conc.doesnt_read_or_modify_doesnt_modify by metis
  with 1 2 show ?thesis
    unfolding conc.respects_own_guarantees_def 
    by metis
qed

lemma modified_variables_are_not_assumed_not_written:
  fixes cms\<^sub>A mem\<^sub>A cms\<^sub>C mem\<^sub>C cm\<^sub>Cn' mem\<^sub>C' \<R>n cm\<^sub>An' mem\<^sub>A' m\<^sub>A \<R>i
  assumes sound_mode_use\<^sub>A: "abs.sound_mode_use (cms\<^sub>A, mem\<^sub>A)"
  assumes pmmn: "preserves_modes_mem \<R>n"
  assumes in_\<R>n: "((cms\<^sub>A ! n, mem\<^sub>A), (cms\<^sub>C ! n, mem\<^sub>C)) \<in> \<R>n"
  assumes pmmi: "preserves_modes_mem \<R>i"
  assumes in_\<R>i: "((cms\<^sub>A ! i, mem\<^sub>A), (cms\<^sub>C ! i, mem\<^sub>C)) \<in> \<R>i"
  assumes nlen: "n < length cms"
  assumes len\<^sub>A: "length cms\<^sub>A = length cms"
  assumes len\<^sub>C: "length cms\<^sub>C = length cms"
  assumes priv_is_asm_priv: "\<And>i. i < length cms \<Longrightarrow> priv_mem\<^sub>C ! i \<subseteq> snd (cms\<^sub>C ! i) AsmNoReadOrWrite"
  assumes priv_is_guar_priv: "\<And>i j. i < length cms \<Longrightarrow> j < length cms \<Longrightarrow> i \<noteq> j \<Longrightarrow> priv_mem\<^sub>C ! i \<subseteq> snd (cms\<^sub>C ! j) GuarNoReadOrWrite"
  assumes new_asms_only_for_priv: "\<And>i. i < length cms \<Longrightarrow> 
                                           (snd (cms\<^sub>C ! i) AsmNoReadOrWrite \<union> snd (cms\<^sub>C ! i) AsmNoWrite) \<inter> (- range var\<^sub>C_of) \<subseteq> priv_mem\<^sub>C ! i"
  assumes eval\<^sub>Cn: "(cms\<^sub>C ! n,mem\<^sub>C) \<leadsto>\<^sub>C (cm\<^sub>Cn', mem\<^sub>C')"
  assumes neval\<^sub>An: "abs.neval (cms\<^sub>A ! n,mem\<^sub>A) m\<^sub>A (cm\<^sub>An', mem\<^sub>A')"
  assumes in_\<R>n': "((cm\<^sub>An', mem\<^sub>A'), (cm\<^sub>Cn', mem\<^sub>C')) \<in> \<R>n"
  assumes modified\<^sub>C: "mem\<^sub>C x\<^sub>C \<noteq> mem\<^sub>C' x\<^sub>C \<or> dma\<^sub>C mem\<^sub>C x\<^sub>C \<noteq> dma\<^sub>C mem\<^sub>C' x\<^sub>C"
  assumes neq: "i \<noteq> n"
  assumes ilen: "i < length cms"
  assumes preserves: "preserves_local_guarantee_compliance \<R>n"
  shows "\<not> var_asm_not_written (snd (cms\<^sub>C ! i)) x\<^sub>C"
proof(cases "x\<^sub>C \<in> range var\<^sub>C_of")
  assume "x\<^sub>C \<in> range var\<^sub>C_of"
  from this obtain x\<^sub>A where x\<^sub>C_def: "x\<^sub>C = var\<^sub>C_of x\<^sub>A" by blast
  obtain c\<^sub>An mds\<^sub>An where [simp]: "cms\<^sub>A ! n = (c\<^sub>An, mds\<^sub>An)" by fastforce
  obtain c\<^sub>Cn mds\<^sub>Cn where [simp]: "cms\<^sub>C ! n = (c\<^sub>Cn, mds\<^sub>Cn)" by fastforce
  obtain c\<^sub>Cn' mds\<^sub>Cn' where [simp]: "cm\<^sub>Cn' = (c\<^sub>Cn', mds\<^sub>Cn')" by fastforce
  obtain c\<^sub>An' mds\<^sub>An' where [simp]: "cm\<^sub>An' = (c\<^sub>An', mds\<^sub>An')" by fastforce

  from in_\<R>n pmmn have [simp]: "mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C" and [simp]: "mds\<^sub>An = mds\<^sub>A_of mds\<^sub>Cn"
    using preserves_modes_memD by auto
  from in_\<R>n' pmmn have [simp]: "mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C'" and [simp]: "mds\<^sub>An' = mds\<^sub>A_of mds\<^sub>Cn'"
    using preserves_modes_memD by auto
  
  from modified\<^sub>C dma_consistent have 
    modified\<^sub>A: "mem\<^sub>A x\<^sub>A \<noteq> mem\<^sub>A' x\<^sub>A \<or> dma\<^sub>A mem\<^sub>A x\<^sub>A \<noteq> dma\<^sub>A mem\<^sub>A' x\<^sub>A"
    by (simp add: mem\<^sub>A_of_def x\<^sub>C_def)
    
  from len\<^sub>A nlen have nlen\<^sub>A: "n < length cms\<^sub>A" by simp
  from len\<^sub>A ilen have ilen\<^sub>A: "i < length cms\<^sub>A" by simp

  from abs.neval_modifies_helper[OF neval\<^sub>An HOL.refl HOL.refl nlen\<^sub>A modified\<^sub>A]
  obtain k\<^sub>A cm\<^sub>An'' mem\<^sub>A'' cm\<^sub>An''' mem\<^sub>A''' 
  where "k\<^sub>A < m\<^sub>A" 
    and neval\<^sub>An'': "abs.neval (cms\<^sub>A ! n, mem\<^sub>A) k\<^sub>A (cm\<^sub>An'', mem\<^sub>A'')"
    and eval\<^sub>An'': "(cm\<^sub>An'', mem\<^sub>A'') \<leadsto>\<^sub>A (cm\<^sub>An''', mem\<^sub>A''')"
    and modified\<^sub>A'': "(mem\<^sub>A'' x\<^sub>A \<noteq> mem\<^sub>A''' x\<^sub>A \<or> dma\<^sub>A mem\<^sub>A'' x\<^sub>A \<noteq> dma\<^sub>A mem\<^sub>A''' x\<^sub>A)" by blast
  let ?c\<^sub>An'' = "fst cm\<^sub>An''"
  let ?mds\<^sub>An'' = "snd cm\<^sub>An''"
  from eval\<^sub>An'' modified\<^sub>A'' have modifies\<^sub>A'': "\<not> abs.doesnt_modify ?c\<^sub>An'' x\<^sub>A"
    unfolding abs.doesnt_modify_def
    by (metis surjective_pairing)
  have loc_reach\<^sub>A'': "(cm\<^sub>An'', mem\<^sub>A'') \<in> abs.loc_reach (cms\<^sub>A ! n, mem\<^sub>A)"
    apply(rule abs.neval_loc_reach)
     apply(rule neval\<^sub>An'')
    using abs.loc_reach.refl by simp
  have locally_sound_mode_use\<^sub>An: "abs.locally_sound_mode_use  (cms\<^sub>A ! n, mem\<^sub>A)"
    using sound_mode_use\<^sub>A nlen\<^sub>A
    unfolding abs.sound_mode_use_def
    using list_all_length by fastforce
  from modifies\<^sub>A'' loc_reach\<^sub>A'' locally_sound_mode_use\<^sub>An abs.doesnt_read_or_modify_doesnt_modify
  have no_guar\<^sub>An: "x\<^sub>A \<notin> ?mds\<^sub>An'' GuarNoReadOrWrite \<and> x\<^sub>A \<notin> ?mds\<^sub>An'' GuarNoWrite"
    unfolding abs.locally_sound_mode_use_def
    by (metis surjective_pairing)
  let ?mdss\<^sub>A'' = "map snd (cms\<^sub>A[n := fst (cm\<^sub>An'',mem\<^sub>A'')])"
  have "?mdss\<^sub>A'' \<in> abs.reachable_mode_states (cms\<^sub>A, mem\<^sub>A)"
    apply(rule abs.neval_reachable_mode_states)
      apply(rule neval\<^sub>An'')
     apply(rule HOL.refl)
    by(rule nlen\<^sub>A)
  hence compat: "abs.compatible_modes ?mdss\<^sub>A''"
    using sound_mode_use\<^sub>A
    by(simp add: abs.globally_sound_mode_use_def)
  have n: "?mdss\<^sub>A'' ! n = ?mds\<^sub>An''"
    by(simp add: nlen\<^sub>A)
  let ?mds\<^sub>Ai = "snd (cms\<^sub>A ! i)"
  have i: "?mdss\<^sub>A'' ! i = ?mds\<^sub>Ai"
    apply(simp add: ilen\<^sub>A)
    by(metis nth_list_update_neq neq)
  from nlen\<^sub>A have nlen\<^sub>A'': "n < length ?mdss\<^sub>A''" by simp
  from ilen\<^sub>A have ilen\<^sub>A'': "i < length ?mdss\<^sub>A''" by simp
  with compat n i nlen\<^sub>A'' ilen\<^sub>A'' no_guar\<^sub>An neq
  have no_asm\<^sub>Ai: "x\<^sub>A \<notin> ?mds\<^sub>Ai AsmNoWrite \<and> x\<^sub>A \<notin> ?mds\<^sub>Ai AsmNoReadOrWrite"
    unfolding abs.compatible_modes_def
    by metis

  obtain c\<^sub>Ai mds\<^sub>Ai where [simp]: "cms\<^sub>A ! i = (c\<^sub>Ai, mds\<^sub>Ai)" by fastforce
  obtain c\<^sub>Ci mds\<^sub>Ci where [simp]: "cms\<^sub>C ! i = (c\<^sub>Ci, mds\<^sub>Ci)" by fastforce

  from in_\<R>i pmmi have [simp]: "mds\<^sub>Ai = mds\<^sub>A_of mds\<^sub>Ci"
    using preserves_modes_memD by auto
  have [simp]: "?mds\<^sub>Ai = mds\<^sub>Ai" by simp
  from no_asm\<^sub>Ai have no_asm\<^sub>Ci: "x\<^sub>C \<notin> mds\<^sub>Ci AsmNoWrite \<and> x\<^sub>C \<notin> mds\<^sub>Ci AsmNoReadOrWrite"
    using x\<^sub>C_def mds\<^sub>A_of_def
    using doesnt_have_mode by auto
  thus ?thesis
    unfolding var_asm_not_written_def
    by simp
next
  let ?mds\<^sub>Cn = "snd (cms\<^sub>C ! n)"
  let ?mds\<^sub>Ci = "snd (cms\<^sub>C ! i)"

  assume new_var: "x\<^sub>C \<notin> range var\<^sub>C_of"
  from conc_respects_priv[OF new_var modified\<^sub>C eval\<^sub>Cn in_\<R>n preserves sound_mode_use\<^sub>A nlen len\<^sub>A len\<^sub>C] 
  have "x\<^sub>C \<notin> ?mds\<^sub>Cn GuarNoWrite \<and> x\<^sub>C \<notin> ?mds\<^sub>Cn GuarNoReadOrWrite" .
  with priv_is_guar_priv nlen ilen neq
  have "x\<^sub>C \<notin> priv_mem\<^sub>C ! i"
    by blast
  with new_var new_asms_only_for_priv ilen
  have "x\<^sub>C \<notin> ?mds\<^sub>Ci AsmNoReadOrWrite \<union> ?mds\<^sub>Ci AsmNoWrite"
    by blast
  thus ?thesis
    unfolding var_asm_not_written_def
    by simp
qed

definition
  priv_is_asm_priv :: "'Var\<^sub>C Mds list \<Rightarrow> bool"
where
  "priv_is_asm_priv mdss\<^sub>C \<equiv>  \<forall>i < length cms. priv_mem\<^sub>C ! i \<subseteq> (mdss\<^sub>C ! i) AsmNoReadOrWrite"

definition
  priv_is_guar_priv :: "'Var\<^sub>C Mds list \<Rightarrow> bool"
where
  "priv_is_guar_priv mdss\<^sub>C \<equiv> 
    \<forall>i < length cms. (\<forall>j < length cms. i \<noteq> j \<longrightarrow> priv_mem\<^sub>C ! i \<subseteq> (mdss\<^sub>C ! j) GuarNoReadOrWrite)"
 
definition
  new_asms_only_for_priv :: "'Var\<^sub>C Mds list \<Rightarrow> bool"
where
  "new_asms_only_for_priv mdss\<^sub>C \<equiv> 
    \<forall> i < length cms. 
      ((mdss\<^sub>C ! i) AsmNoReadOrWrite \<union> (mdss\<^sub>C ! i) AsmNoWrite) \<inter> (- range var\<^sub>C_of) \<subseteq> priv_mem\<^sub>C ! i"

definition
  new_asms_NoReadOrWrite_only :: "'Var\<^sub>C Mds list \<Rightarrow> bool"
where
  "new_asms_NoReadOrWrite_only mdss\<^sub>C \<equiv> 
    \<forall> i < length cms. 
      (mdss\<^sub>C ! i) AsmNoWrite \<inter> (- range var\<^sub>C_of) = {}"

definition
  modes_respect_priv :: "'Var\<^sub>C Mds list \<Rightarrow> bool"
where
  "modes_respect_priv mdss\<^sub>C  \<equiv> priv_is_asm_priv mdss\<^sub>C \<and> priv_is_guar_priv mdss\<^sub>C \<and>
                               new_asms_only_for_priv mdss\<^sub>C \<and>
                               new_asms_NoReadOrWrite_only mdss\<^sub>C"

definition
  ignores_old_vars :: "('Var\<^sub>C Mds list \<Rightarrow> bool) \<Rightarrow> bool"
where
  "ignores_old_vars P \<equiv> \<forall>mdss mdss'. length mdss = length mdss' \<and> length mdss' = length cms \<longrightarrow> 
    (map (\<lambda>x m. x m \<inter> (- range var\<^sub>C_of)) mdss) = (map (\<lambda>x m. x m \<inter> (- range var\<^sub>C_of)) mdss') \<longrightarrow> 
  P mdss = P mdss'"

lemma ignores_old_vars_conj:
  assumes Rdef: "(\<And>x. R x = (P x \<and> Q x))"
  assumes iP: "ignores_old_vars P" 
  assumes iQ: "ignores_old_vars Q" 
  shows "ignores_old_vars R"
  unfolding ignores_old_vars_def
  apply(simp add: Rdef)
  apply(intro impI allI)
  apply(rule conj_cong)
   apply(erule (1) iP[unfolded ignores_old_vars_def, rule_format])
  apply(erule (1) iQ[unfolded ignores_old_vars_def, rule_format])
  done

  
lemma nth_map_eq': 
  "length xs = length ys \<Longrightarrow> map f xs = map g ys \<Longrightarrow> i < length xs \<Longrightarrow> f (xs ! i) = g (ys ! i)"  
  apply(induct xs ys rule: list_induct2)
   apply simp
  apply(case_tac i)
   apply force
  by (metis length_map nth_map)

lemma nth_map_eq: 
  "map f xs = map g ys \<Longrightarrow> i < length xs \<Longrightarrow> f (xs ! i) = g (ys ! i)"
  apply(rule nth_map_eq')
    apply(erule map_eq_imp_length_eq)
   apply assumption+
  done

lemma nth_in_Union_over_set: 
  "i < length xs \<Longrightarrow> xs ! i \<subseteq> \<Union>(set xs)"
  by (simp add: Union_upper)

lemma priv_are_new_vars: 
  "x \<in> priv_mem\<^sub>C ! i \<Longrightarrow> i < length cms \<Longrightarrow> x \<notin> range var\<^sub>C_of"
  using new_vars_priv nth_in_Union_over_set subsetD
  using priv_mem\<^sub>C_def by fastforce
  
lemma priv_is_asm_priv_ignores_old_vars:
  "ignores_old_vars priv_is_asm_priv"
  apply(clarsimp simp: ignores_old_vars_def priv_is_asm_priv_def)
  apply(rule all_cong)
  apply(drule nth_map_eq)
   apply simp
  apply(blast dest: priv_are_new_vars fun_cong)
  done
  
lemma priv_is_guar_priv_ignores_old_vars:
  "ignores_old_vars priv_is_guar_priv"
  apply(clarsimp simp: ignores_old_vars_def priv_is_guar_priv_def)
  apply(rule all_cong)
  apply(rule all_cong)
  apply(rule imp_cong)
   apply(rule HOL.refl)
  apply(frule nth_map_eq)
   apply simp
  apply(drule_tac i=j in nth_map_eq)
   apply simp
  apply(blast dest: priv_are_new_vars fun_cong)
  done

lemma new_asms_only_for_priv_ignores_old_vars:
  "ignores_old_vars new_asms_only_for_priv"
  apply(clarsimp simp: ignores_old_vars_def new_asms_only_for_priv_def)
  apply(rule all_cong)
  apply(drule nth_map_eq)
   apply simp
  apply(blast dest: priv_are_new_vars fun_cong)
  done

lemma new_asms_NoReadOrWrite_only_ignores_old_vars:
  "ignores_old_vars new_asms_NoReadOrWrite_only"
  apply(clarsimp simp: ignores_old_vars_def new_asms_NoReadOrWrite_only_def)
  apply(rule all_cong)
  apply(drule nth_map_eq)
   apply simp
  apply(blast dest: priv_are_new_vars fun_cong)
  done
  
lemma modes_respect_priv_ignores_old_vars:
   "ignores_old_vars modes_respect_priv"
   apply(rule ignores_old_vars_conj)
     apply(subst modes_respect_priv_def)
     apply(rule HOL.refl)
    apply(rule priv_is_asm_priv_ignores_old_vars)
   apply(rule ignores_old_vars_conj)
    apply(rule HOL.refl)
   apply(rule priv_is_guar_priv_ignores_old_vars)
  apply(rule ignores_old_vars_conj)
    apply(rule HOL.refl)
   apply(rule new_asms_only_for_priv_ignores_old_vars)
  apply(rule new_asms_NoReadOrWrite_only_ignores_old_vars)
  done
  
lemma ignores_old_varsD:
  "ignores_old_vars P \<Longrightarrow> length mdss = length mdss' \<Longrightarrow> length mdss' = length cms \<Longrightarrow>
  (map (\<lambda>x m. x m \<inter> (- range var\<^sub>C_of)) mdss) = (map (\<lambda>x m. x m \<inter> (- range var\<^sub>C_of)) mdss') \<Longrightarrow> 
  P mdss = P mdss'"
  unfolding ignores_old_vars_def
  by force
  
lemma new_privs_preserved':
  "\<langle>c, mds, mem\<rangle>\<^sub>C \<leadsto>\<^sub>C \<langle>c', mds', mem'\<rangle>\<^sub>C \<Longrightarrow> (mds m \<inter> (- range var\<^sub>C_of)) = (mds' m \<inter> (- range var\<^sub>C_of))"
  using new_privs_preserved by blast

lemma map_nth_eq:
  "length xs = length ys \<Longrightarrow> (\<And>i. i < length xs \<Longrightarrow> f (xs ! i) = g (ys ! i)) \<Longrightarrow>
  map f xs = map g ys"
  apply(induct xs ys rule: list_induct2)
   apply simp
  apply force
  done
  
lemma ignores_old_vars_conc_meval:
  assumes ignores: "ignores_old_vars P"
  assumes meval:  "conc.meval_abv gc\<^sub>C n gc\<^sub>C'"
  assumes len_eq: "length (fst gc\<^sub>C) = length cms"
  shows "P (map snd (fst gc\<^sub>C)) = P (map snd (fst gc\<^sub>C'))"
proof -
  obtain cms\<^sub>C mem\<^sub>C where [simp]: "gc\<^sub>C = (cms\<^sub>C, mem\<^sub>C)" by fastforce
  obtain cms\<^sub>C' mem\<^sub>C' where [simp]: "gc\<^sub>C' = (cms\<^sub>C', mem\<^sub>C')" by fastforce
  from meval obtain cmn' mem\<^sub>C' where
    eval\<^sub>Cn: "(cms\<^sub>C ! n, mem\<^sub>C) \<leadsto>\<^sub>C (cmn', mem\<^sub>C')" and len: "n < length cms\<^sub>C" and cms\<^sub>C'_def: "cms\<^sub>C' = cms\<^sub>C[n := cmn']"
    using conc.meval.cases by fastforce
  have
    "P (map snd cms\<^sub>C) = P (map snd cms\<^sub>C')"
    apply(rule ignores_old_varsD[OF ignores])
      apply(simp add: cms\<^sub>C'_def)
     using len_eq apply (simp add: cms\<^sub>C'_def)
    apply(rule map_nth_eq)
     apply (simp add: cms\<^sub>C'_def)
    apply(case_tac "i = n")
     apply simp
     apply(rule ext)
     apply(simp add: cms\<^sub>C'_def)
     using eval\<^sub>Cn new_privs_preserved' apply(metis surjective_pairing)
    by (simp add: cms\<^sub>C'_def)
  thus ?thesis by simp
qed

lemma ignores_old_vars_conc_meval_sched:
  assumes ignores: "ignores_old_vars P"
  assumes meval_sched:  "conc.meval_sched sched gc\<^sub>C gc\<^sub>C'"
  assumes len_eq: "length (fst gc\<^sub>C) = length cms"
  shows "P (map snd (fst gc\<^sub>C)) = P (map snd (fst gc\<^sub>C'))"
using meval_sched len_eq proof(induct rule: conc.meval_sched.induct)
  case (1 gc gc')
  thus ?case by simp
next
  case (2 n ns gc gc')
  from 2(2) obtain gc'' where b: "conc.meval_abv gc n gc''" and a: "conc.meval_sched ns gc'' gc'" by force
  with 2 have "length (fst gc'') = length cms"
    using conc.meval.cases 
    by (metis length_list_update surjective_pairing)
  with 2 a b show ?case
  using ignores_old_vars_conc_meval ignores by metis 
qed

lemma meval_sched_modes_respect_priv:
  "conc.meval_sched sched gc\<^sub>C gc\<^sub>C' \<Longrightarrow>   length (fst gc\<^sub>C) = length cms \<Longrightarrow>
  modes_respect_priv (map snd (fst gc\<^sub>C)) \<Longrightarrow>
  modes_respect_priv (map snd (fst gc\<^sub>C'))"
  by(blast dest!: ignores_old_vars_conc_meval_sched[OF modes_respect_priv_ignores_old_vars])

lemma meval_modes_respect_priv:
  "conc.meval_abv gc\<^sub>C n gc\<^sub>C' \<Longrightarrow>   length (fst gc\<^sub>C) = length cms \<Longrightarrow>
  modes_respect_priv (map snd (fst gc\<^sub>C)) \<Longrightarrow>
  modes_respect_priv (map snd (fst gc\<^sub>C'))"
  by(blast dest!: ignores_old_vars_conc_meval[OF modes_respect_priv_ignores_old_vars])
  
(* I think this lemma would guarantee globally sound mode use for all of the
  var\<^sub>C_of variables. It should also hold for all of the non var\<^sub>C_of variables by
  the locale assumptions above *)
lemma traces_refinement:
  "\<And>gc\<^sub>C gc\<^sub>C' sched\<^sub>C gc\<^sub>A. conc.meval_sched sched\<^sub>C gc\<^sub>C gc\<^sub>C' \<Longrightarrow>
    length (fst gc\<^sub>A) = length cms \<Longrightarrow> length (fst gc\<^sub>C) = length cms  \<Longrightarrow>
    (\<And>i. i < length cms \<Longrightarrow> ((fst gc\<^sub>A ! i, snd gc\<^sub>A), (fst gc\<^sub>C ! i, snd gc\<^sub>C)) \<in> \<R>_rel (cms ! i)) \<Longrightarrow>
    abs.sound_mode_use gc\<^sub>A \<Longrightarrow> modes_respect_priv (map snd (fst gc\<^sub>C)) \<Longrightarrow>
   \<exists>sched\<^sub>A gc\<^sub>A'. abs.meval_sched sched\<^sub>A gc\<^sub>A gc\<^sub>A' \<and>
          (\<forall>i. i < length cms \<longrightarrow> ((fst gc\<^sub>A' ! i, snd gc\<^sub>A'), (fst gc\<^sub>C' ! i, snd gc\<^sub>C')) \<in> \<R>_rel (cms ! i)) \<and>
          abs.sound_mode_use gc\<^sub>A'"
proof -
  fix gc\<^sub>C gc\<^sub>C' sched\<^sub>C gc\<^sub>A
  assume meval\<^sub>C: "conc.meval_sched sched\<^sub>C gc\<^sub>C gc\<^sub>C'"
     and len_eq [simp]: "length (fst gc\<^sub>A) = length cms"
     and len_eq'[simp]: "length (fst gc\<^sub>C) = length cms"
     and in_\<R>: "(\<And>i. i < length cms \<Longrightarrow> ((fst gc\<^sub>A ! i, snd gc\<^sub>A), (fst gc\<^sub>C ! i, snd gc\<^sub>C)) \<in> \<R>_rel (cms ! i))"
     and sound_mode_use\<^sub>A: "abs.sound_mode_use gc\<^sub>A"
     and modes_respect_priv: "modes_respect_priv (map snd (fst gc\<^sub>C))"
  thus
    "\<exists>sched\<^sub>A gc\<^sub>A'. abs.meval_sched sched\<^sub>A gc\<^sub>A gc\<^sub>A' \<and>
          (\<forall>i. i < length cms \<longrightarrow> ((fst gc\<^sub>A' ! i, snd gc\<^sub>A'), (fst gc\<^sub>C' ! i, snd gc\<^sub>C')) \<in> \<R>_rel (cms ! i)) \<and>
          abs.sound_mode_use gc\<^sub>A'"
  proof(induct  arbitrary: gc\<^sub>A rule: conc.meval_sched.induct)
  case (1 cms\<^sub>C cms\<^sub>C')
    from 1(1) have cms\<^sub>C'_def [simp]: "cms\<^sub>C' = cms\<^sub>C" by simp
    with 1 have "abs.meval_sched [] gc\<^sub>A gc\<^sub>A \<and>
    (\<forall>i<length cms.
        ((fst gc\<^sub>A ! i, snd gc\<^sub>A), fst cms\<^sub>C' ! i, snd cms\<^sub>C') \<in> \<R>_rel (cms ! i)) \<and>
        abs.sound_mode_use gc\<^sub>A"
      by simp
    thus ?case by blast
  next
  case (2 n ns gc\<^sub>C gc\<^sub>c')
    obtain cms\<^sub>C mem\<^sub>C where gc\<^sub>C_def [simp]: "gc\<^sub>C = (cms\<^sub>C, mem\<^sub>C)" by force
    obtain cms\<^sub>A mem\<^sub>A where gc\<^sub>A_def [simp]: "gc\<^sub>A = (cms\<^sub>A, mem\<^sub>A)" by force
    from 2(2) gc\<^sub>C_def obtain cms\<^sub>C'' mem\<^sub>C'' where
      meval\<^sub>C: "((cms\<^sub>C,mem\<^sub>C), n, (cms\<^sub>C'',mem\<^sub>C'')) \<in> conc.meval" and 
      meval_sched\<^sub>C: "conc.meval_sched ns (cms\<^sub>C'',mem\<^sub>C'') gc\<^sub>c'" 
      by force
  
    let ?cm\<^sub>Cn = "cms\<^sub>C ! n"
    let ?cm\<^sub>An = "cms\<^sub>A ! n"
    let ?\<R>n = "\<R>_rel (cms ! n)"
    from meval\<^sub>C obtain cm\<^sub>Cn'' where
      eval\<^sub>Cn: "(?cm\<^sub>Cn, mem\<^sub>C) \<leadsto>\<^sub>C (cm\<^sub>Cn'', mem\<^sub>C'')" and
      len: "n < length cms\<^sub>C" and
      cms\<^sub>C''_def: "cms\<^sub>C'' = cms\<^sub>C [n := cm\<^sub>Cn'']" by (blast elim: conc.meval.cases)
    from len have len [simp]: "n < length cms" by (simp add: 2[simplified])
    from cms\<^sub>C''_def 2 have 
      len_cms\<^sub>C'' [simp]: "length cms\<^sub>C'' = length cms" by simp
    from 2 len have 
      in_\<R>n: "((?cm\<^sub>An,mem\<^sub>A), (?cm\<^sub>Cn,mem\<^sub>C)) \<in> ?\<R>n"
      by simp
    
    with eval\<^sub>Cn use_secure_refinement_helper[OF secure_refinements[OF len]]  
    obtain cm\<^sub>An'' mem\<^sub>A'' m\<^sub>A where
      neval\<^sub>An: "abs.neval (?cm\<^sub>An, mem\<^sub>A) m\<^sub>A (cm\<^sub>An'', mem\<^sub>A'')" and
      in_\<R>n'': "((cm\<^sub>An'',mem\<^sub>A''),(cm\<^sub>Cn'',mem\<^sub>C'')) \<in> ?\<R>n"
      by blast+
      
    define cms\<^sub>A'' where "cms\<^sub>A'' = cms\<^sub>A [n := cm\<^sub>An'']" 
    define gc\<^sub>A'' where [simp]: "gc\<^sub>A'' = (cms\<^sub>A'', mem\<^sub>A'')"
    have len_cms\<^sub>A'' [simp]: "length cms\<^sub>A'' = length cms" by(simp add: cms\<^sub>A''_def 2[simplified])
  
    have in_\<R>'': "(\<And>i. i < length cms \<Longrightarrow> ((cms\<^sub>A'' ! i, mem\<^sub>A''), cms\<^sub>C'' ! i, mem\<^sub>C'') \<in> \<R>_rel (cms ! i))"
    proof -
      fix i
      assume "i < length cms"
      show "?thesis i"
      proof(cases "i = n")
        assume "i = n"
        hence "cms\<^sub>A'' ! i = cm\<^sub>An''"
          using cms\<^sub>A''_def len_cms\<^sub>A'' len by simp
        moreover from \<open>i = n\<close> have "cms\<^sub>C'' ! i = cm\<^sub>Cn''"
          using cms\<^sub>C''_def len_cms\<^sub>C'' len by simp
        ultimately  show ?thesis 
          using in_\<R>n'' \<open>i = n\<close>
          by simp
      next
        obtain c\<^sub>Ai mds\<^sub>Ai where cms\<^sub>Ai_def [simp]: "(cms\<^sub>A ! i) = (c\<^sub>Ai, mds\<^sub>Ai)" by fastforce 
        obtain c\<^sub>Ci mds\<^sub>Ci where cms\<^sub>Ci_def [simp]: "(cms\<^sub>C ! i) = (c\<^sub>Ci, mds\<^sub>Ci)" by fastforce 
        hence mds\<^sub>Ci_def: "mds\<^sub>Ci = snd (cms\<^sub>C ! i)" by simp
        
        from 2(5) \<open>i < length cms\<close> have 
          in_\<R>i: "((cms\<^sub>A ! i,mem\<^sub>A), (cms\<^sub>C ! i,mem\<^sub>C)) \<in> \<R>_rel (cms ! i)"
          by force
          
        from in_\<R>n'' secure_refinements len preserves_modes_memD
        have mem\<^sub>A''_def [simp]: "mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C''"
          unfolding secure_refinement_def
          by (metis surjective_pairing)
          
        from in_\<R>i secure_refinements  \<open>i < length cms\<close> preserves_modes_memD
             cms\<^sub>Ai_def cms\<^sub>Ci_def
        have mem\<^sub>A_def [simp]: "mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C" and
             mds\<^sub>Ai_def [simp]: "mds\<^sub>Ai = mds\<^sub>A_of mds\<^sub>Ci"
          unfolding secure_refinement_def
          by metis+
          
        assume "i \<noteq> n"
        hence "cms\<^sub>A'' ! i = cms\<^sub>A ! i"
          using cms\<^sub>A''_def len_cms\<^sub>A'' len by simp
        moreover from \<open>i \<noteq> n\<close> have "cms\<^sub>C'' ! i = cms\<^sub>C ! i"
          using cms\<^sub>C''_def len_cms\<^sub>C'' len by simp
        ultimately  show ?thesis 
        
          using 2(5)[of i] \<open>i \<noteq> n\<close> \<open>i < length cms\<close>
          apply simp
          apply(rule closed_othersD)
            apply(rule secure_refinements[OF \<open>i < length cms\<close>, unfolded secure_refinement_def, THEN conjunct1])
           apply assumption
          apply(simp only: mds\<^sub>Ci_def)  
          apply(rule_tac \<R>n="\<R>_rel (cms ! n)"  and \<R>i="\<R>_rel (cms ! i)" in modified_variables_are_not_assumed_not_written)
                           apply(rule 2(6)[unfolded gc\<^sub>A_def])
                          using secure_refinements len secure_refinement_def apply blast
                         apply(rule in_\<R>n)
                        using secure_refinements secure_refinement_def apply blast
                       apply(rule in_\<R>i)
                      apply(rule len)
                      using 2 apply simp
                    using 2 apply simp
                   using 2(7) unfolding modes_respect_priv_def priv_is_asm_priv_def gc\<^sub>C_def 
                   using "2.prems"(3) apply auto[1]
                  using 2(7) unfolding modes_respect_priv_def priv_is_guar_priv_def gc\<^sub>C_def 
                  using "2.prems"(3) apply auto[1]
                 using 2(7) unfolding modes_respect_priv_def new_asms_only_for_priv_def gc\<^sub>C_def 
                 using "2.prems"(3) apply auto[1]
                apply(rule eval\<^sub>Cn)
               apply(rule neval\<^sub>An)
              apply(rule in_\<R>n'')
             apply fastforce
            apply assumption
           apply assumption
          apply(rule local_guarantee_preservation)
          by simp
      qed
    qed
  
    have meval_sched\<^sub>A: "abs.meval_sched (replicate m\<^sub>A n) gc\<^sub>A (cms\<^sub>A'', mem\<^sub>A'')"
      apply(simp add: cms\<^sub>A''_def)
      apply(rule abs.neval_meval[OF _ _ HOL.refl HOL.refl])
       apply(rule neval\<^sub>An)
      using "2.prems"(2) by auto
  
    have sound_mode_use\<^sub>A'': "abs.sound_mode_use (cms\<^sub>A'', mem\<^sub>A'')"
      apply(rule abs.meval_sched_sound_mode_use)
       apply(rule 2(6))
      by(rule meval_sched\<^sub>A)
   
    have respects'': "modes_respect_priv (map snd cms\<^sub>C'')"
      apply(rule meval_modes_respect_priv[where gc\<^sub>C'="(cms\<^sub>C'',mem\<^sub>C'')", simplified])
        apply(rule meval\<^sub>C)
       using "2.prems"(3) gc\<^sub>C_def apply blast
      using 2 by simp

    from respects'' 2(1)[OF meval_sched\<^sub>C, where gc\<^sub>A7 = gc\<^sub>A''] in_\<R>'' sound_mode_use\<^sub>A''
    obtain sched\<^sub>A gc\<^sub>A' 
    where  meval_sched\<^sub>A'': "abs.meval_sched sched\<^sub>A gc\<^sub>A'' gc\<^sub>A'" and
           in_\<R>': "(\<forall>i<length cms. ((fst gc\<^sub>A' ! i, snd gc\<^sub>A'), fst gc\<^sub>c' ! i, snd gc\<^sub>c') \<in> \<R>_rel (cms ! i))" and
           sound_mode_use\<^sub>A': "abs.sound_mode_use  gc\<^sub>A'" by fastforce
    define final_sched\<^sub>A where "final_sched\<^sub>A = (replicate m\<^sub>A n) @ sched\<^sub>A"
    have meval_final_sched\<^sub>A: "abs.meval_sched final_sched\<^sub>A gc\<^sub>A gc\<^sub>A'"
      using meval_sched\<^sub>A'' meval_sched\<^sub>A abs.meval_sched_app final_sched\<^sub>A_def gc\<^sub>A''_def by blast
    
    from meval_final_sched\<^sub>A in_\<R>' sound_mode_use\<^sub>A'
    show ?case by blast
  qed
qed

end

context sifum_security begin

definition
  restrict_modes :: "'Var Mds list \<Rightarrow> 'Var set \<Rightarrow> 'Var Mds list"
where
  "restrict_modes mdss X \<equiv> map (\<lambda>mds m. mds m \<inter> X) mdss"

lemma restrict_modes_length [simp]:
  "length (restrict_modes mdss X) = length mdss"
  by(auto simp: restrict_modes_def)
  
lemma compatible_modes_by_case_distinction:
  assumes compat_X: "compatible_modes (restrict_modes mdss X)"
  assumes compat_compX: "compatible_modes (restrict_modes mdss (-X ))"
  shows "compatible_modes mdss"
unfolding compatible_modes_def
proof(safe)
  fix i x j
  assume ilen: "i < length mdss"
  assume jlen: "j < length mdss"
  assume neq: "j \<noteq> i"
  assume asm: "x \<in> (mdss ! i) AsmNoReadOrWrite"
  show "x \<in> (mdss ! j) GuarNoReadOrWrite"
  proof(cases "x \<in> X")
    assume xin: "x \<in> X"
    let ?mdss\<^sub>X = "restrict_modes mdss X"
    from asm xin have "x \<in> (?mdss\<^sub>X ! i) AsmNoReadOrWrite"
      unfolding restrict_modes_def
      using ilen by auto
    
    with compat_X jlen ilen neq 
    have "x \<in> (?mdss\<^sub>X ! j) GuarNoReadOrWrite"
      unfolding compatible_modes_def
      by auto
    with xin jlen show ?thesis
      unfolding restrict_modes_def by auto
  next
    assume xnin: "x \<notin> X"
    let ?mdss\<^sub>X = "restrict_modes mdss (- X)"
    from asm xnin have "x \<in> (?mdss\<^sub>X ! i) AsmNoReadOrWrite"
      unfolding restrict_modes_def
      using ilen by auto
    
    with compat_compX jlen ilen neq 
    have "x \<in> (?mdss\<^sub>X ! j) GuarNoReadOrWrite"
      unfolding compatible_modes_def
      by auto
    with xnin jlen show ?thesis
      unfolding restrict_modes_def by auto
  qed
next
  fix i x j
  assume ilen: "i < length mdss"
  assume jlen: "j < length mdss"
  assume neq: "j \<noteq> i"
  assume asm: "x \<in> (mdss ! i) AsmNoWrite"
  show "x \<in> (mdss ! j) GuarNoWrite"
  proof(cases "x \<in> X")
    assume xin: "x \<in> X"
    let ?mdss\<^sub>X = "restrict_modes mdss X"
    from asm xin have "x \<in> (?mdss\<^sub>X ! i) AsmNoWrite"
      unfolding restrict_modes_def
      using ilen by auto
    
    with compat_X jlen ilen neq 
    have "x \<in> (?mdss\<^sub>X ! j) GuarNoWrite"
      unfolding compatible_modes_def
      by auto
    with xin jlen show ?thesis
      unfolding restrict_modes_def by auto
  next
    assume xnin: "x \<notin> X"
    let ?mdss\<^sub>X = "restrict_modes mdss (- X)"
    from asm xnin have "x \<in> (?mdss\<^sub>X ! i) AsmNoWrite"
      unfolding restrict_modes_def
      using ilen by auto
    
    with compat_compX jlen ilen neq 
    have "x \<in> (?mdss\<^sub>X ! j) GuarNoWrite"
      unfolding compatible_modes_def
      by auto
    with xnin jlen show ?thesis
      unfolding restrict_modes_def by auto
  qed
qed

lemma in_restrict_modesD:
  "i < length mdss \<Longrightarrow> x \<in> ((restrict_modes mdss X) ! i) m \<Longrightarrow> x \<in> X \<and> x \<in> (mdss ! i) m"
  by(auto simp: restrict_modes_def)

lemma in_restrict_modesI:
  "i < length mdss \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> (mdss ! i) m \<Longrightarrow> x \<in> ((restrict_modes mdss X) ! i) m "
  by(auto simp: restrict_modes_def)
  
lemma meval_sched_length:
  "meval_sched sched gc gc' \<Longrightarrow> length (fst gc') = length (fst gc)"
  apply(induct sched arbitrary: gc gc')
  by auto
  
  
end

context sifum_refinement_sys begin

lemma compatible_modes_old_vars:
  assumes compatible_modes\<^sub>A: "abs.compatible_modes (map snd cms\<^sub>A)" 
  assumes len\<^sub>A: "length cms\<^sub>A = length cms"
  assumes len\<^sub>C: "length cms\<^sub>C = length cms"
  assumes in_\<R>: "(\<forall>i<length cms. ((cms\<^sub>A ! i, mem\<^sub>A), cms\<^sub>C ! i, mem\<^sub>C) \<in> \<R>_rel (cms ! i))"
  shows "conc.compatible_modes (conc.restrict_modes (map snd cms\<^sub>C) (range var\<^sub>C_of))"
unfolding conc.compatible_modes_def
proof(clarsimp)
  fix i x
  assume i_len: "i < length cms\<^sub>C"
  let ?cms = "cms ! i" and
      ?c\<^sub>A = "fst (cms\<^sub>A ! i)" and ?mds\<^sub>A = "snd (cms\<^sub>A ! i)" and
      ?c\<^sub>C = "fst (cms\<^sub>C ! i)" and ?mds\<^sub>C = "snd (cms\<^sub>C ! i)"

  from in_\<R> i_len len\<^sub>C
  have in_\<R>_i: "((cms\<^sub>A ! i, mem\<^sub>A), cms\<^sub>C ! i, mem\<^sub>C) \<in> \<R>_rel ?cms" by simp

  from i_len have "i < length (map snd cms\<^sub>C)" by simp
  hence m_x_range: "\<And>m. x \<in> (conc.restrict_modes (map snd cms\<^sub>C) (range var\<^sub>C_of) ! i) m \<Longrightarrow> x \<in> range var\<^sub>C_of \<and> x \<in> (map snd cms\<^sub>C ! i) m"
    using conc.in_restrict_modesD i_len by blast+
  hence m_x\<^sub>C_i: "\<And>m. x \<in> (conc.restrict_modes (map snd cms\<^sub>C) (range var\<^sub>C_of) ! i) m \<Longrightarrow> x \<in> ?mds\<^sub>C m"
    by (simp add: i_len)

  from secure_refinements i_len len\<^sub>C
  have "secure_refinement (\<R>\<^sub>A_rel ?cms) (\<R>_rel ?cms) (P_rel ?cms)" by simp
  hence preserves_modes_mem_\<R>_i: "preserves_modes_mem (\<R>_rel ?cms)"
    unfolding secure_refinement_def by simp

  from in_\<R>_i have "(\<langle>?c\<^sub>A, ?mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>?c\<^sub>C, ?mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> \<R>_rel ?cms" by clarsimp
  with preserves_modes_mem_\<R>_i
  have "(\<forall>x\<^sub>A. mem\<^sub>A x\<^sub>A = mem\<^sub>C (var\<^sub>C_of x\<^sub>A)) \<and> (\<forall>m. var\<^sub>C_of ` ?mds\<^sub>A m = range var\<^sub>C_of \<inter> ?mds\<^sub>C m)"
    unfolding preserves_modes_mem_def by blast
  with m_x\<^sub>C_i have m_x\<^sub>A: "\<And>m. x \<in> (conc.restrict_modes (map snd cms\<^sub>C) (range var\<^sub>C_of) ! i) m \<Longrightarrow> var\<^sub>A_of x \<in> ?mds\<^sub>A m"
    unfolding var\<^sub>A_of_def using m_x_range inj_image_mem_iff var\<^sub>C_of_inj by fastforce

  show "(x \<in> (conc.restrict_modes (map snd cms\<^sub>C) (range var\<^sub>C_of) ! i) AsmNoReadOrWrite \<longrightarrow>
          (\<forall>j<length cms\<^sub>C. j \<noteq> i \<longrightarrow>
            x \<in> (conc.restrict_modes (map snd cms\<^sub>C) (range var\<^sub>C_of) ! j) GuarNoReadOrWrite)) \<and>
        (x \<in> (conc.restrict_modes (map snd cms\<^sub>C) (range var\<^sub>C_of) ! i) AsmNoWrite \<longrightarrow>
          (\<forall>j<length cms\<^sub>C. j \<noteq> i \<longrightarrow>
            x \<in> (conc.restrict_modes (map snd cms\<^sub>C) (range var\<^sub>C_of) ! j) GuarNoWrite))"
    proof(safe)
      fix j
      assume AsmNoRW_x\<^sub>C: "x \<in> (conc.restrict_modes (map snd cms\<^sub>C) (range var\<^sub>C_of) ! i) AsmNoReadOrWrite" and
        j_len: "j < length cms\<^sub>C" and
        j_not_i: "j \<noteq> i"
      let ?cms' = "cms ! j" and
          ?c\<^sub>A' = "fst (cms\<^sub>A ! j)" and ?mds\<^sub>A' = "snd (cms\<^sub>A ! j)" and
          ?c\<^sub>C' = "fst (cms\<^sub>C ! j)" and ?mds\<^sub>C' = "snd (cms\<^sub>C ! j)"

      from AsmNoRW_x\<^sub>C m_x_range
      have x_range: "x \<in> range var\<^sub>C_of" by simp

      from AsmNoRW_x\<^sub>C m_x\<^sub>A
      have "var\<^sub>A_of x \<in> ?mds\<^sub>A AsmNoReadOrWrite" by simp
      with compatible_modes\<^sub>A
      have GuarNoRW_x\<^sub>A: "var\<^sub>A_of x \<in> ?mds\<^sub>A' GuarNoReadOrWrite"
        unfolding abs.compatible_modes_def using i_len len\<^sub>A len\<^sub>C j_len j_not_i by clarsimp

      from in_\<R> j_len len\<^sub>C
      have in_\<R>_j: "((cms\<^sub>A ! j, mem\<^sub>A), cms\<^sub>C ! j, mem\<^sub>C) \<in> \<R>_rel ?cms'" by simp

      from j_len have j_len': "j < length (map snd cms\<^sub>C)" by simp

      from secure_refinements j_len len\<^sub>C
      have "secure_refinement (\<R>\<^sub>A_rel ?cms') (\<R>_rel ?cms') (P_rel ?cms')" by simp
      hence preserves_modes_mem_\<R>_j: "preserves_modes_mem (\<R>_rel ?cms')"
        unfolding secure_refinement_def by simp

      from in_\<R>_j have "(\<langle>?c\<^sub>A', ?mds\<^sub>A', mem\<^sub>A\<rangle>\<^sub>A, \<langle>?c\<^sub>C', ?mds\<^sub>C', mem\<^sub>C\<rangle>\<^sub>C) \<in> \<R>_rel ?cms'" by clarsimp
      with preserves_modes_mem_\<R>_j
      have "(\<forall>x\<^sub>A. mem\<^sub>A x\<^sub>A = mem\<^sub>C (var\<^sub>C_of x\<^sub>A)) \<and> (\<forall>m. var\<^sub>C_of ` ?mds\<^sub>A' m = range var\<^sub>C_of \<inter> ?mds\<^sub>C' m)"
        unfolding preserves_modes_mem_def by blast

      with GuarNoRW_x\<^sub>A j_len j_len' mds\<^sub>A_of_def x_range conc.in_restrict_modesI var\<^sub>C_of_inj
      show "x \<in> (conc.restrict_modes (map snd cms\<^sub>C) (range var\<^sub>C_of) ! j) GuarNoReadOrWrite"
        unfolding var\<^sub>A_of_def
        by (metis (no_types, lifting) doesnt_have_mode f_inv_into_f image_inv_f_f nth_map)
    next
      (* This argument is identical to that for AsmNoReadOrWrite *)
      fix j
      assume AsmNoWrite_x\<^sub>C: "x \<in> (conc.restrict_modes (map snd cms\<^sub>C) (range var\<^sub>C_of) ! i) AsmNoWrite" and
        j_len: "j < length cms\<^sub>C" and
        j_not_i: "j \<noteq> i"
      let ?cms' = "cms ! j" and
          ?c\<^sub>A' = "fst (cms\<^sub>A ! j)" and ?mds\<^sub>A' = "snd (cms\<^sub>A ! j)" and
          ?c\<^sub>C' = "fst (cms\<^sub>C ! j)" and ?mds\<^sub>C' = "snd (cms\<^sub>C ! j)"

      from AsmNoWrite_x\<^sub>C m_x_range
      have x_range: "x \<in> range var\<^sub>C_of" by simp

      from AsmNoWrite_x\<^sub>C m_x\<^sub>A
      have "var\<^sub>A_of x \<in> ?mds\<^sub>A AsmNoWrite" by simp
      with compatible_modes\<^sub>A
      have GuarNoWrite_x\<^sub>A: "var\<^sub>A_of x \<in> ?mds\<^sub>A' GuarNoWrite"
        unfolding abs.compatible_modes_def using i_len len\<^sub>A len\<^sub>C j_len j_not_i by clarsimp

      from in_\<R> j_len len\<^sub>C
      have in_\<R>_j: "((cms\<^sub>A ! j, mem\<^sub>A), cms\<^sub>C ! j, mem\<^sub>C) \<in> \<R>_rel ?cms'" by simp

      from j_len have j_len': "j < length (map snd cms\<^sub>C)" by simp

      from secure_refinements j_len len\<^sub>C
      have "secure_refinement (\<R>\<^sub>A_rel ?cms') (\<R>_rel ?cms') (P_rel ?cms')" by simp
      hence preserves_modes_mem_\<R>_j: "preserves_modes_mem (\<R>_rel ?cms')"
        unfolding secure_refinement_def by simp

      from in_\<R>_j have "(\<langle>?c\<^sub>A', ?mds\<^sub>A', mem\<^sub>A\<rangle>\<^sub>A, \<langle>?c\<^sub>C', ?mds\<^sub>C', mem\<^sub>C\<rangle>\<^sub>C) \<in> \<R>_rel ?cms'" by clarsimp
      with preserves_modes_mem_\<R>_j
      have "(\<forall>x\<^sub>A. mem\<^sub>A x\<^sub>A = mem\<^sub>C (var\<^sub>C_of x\<^sub>A)) \<and> (\<forall>m. var\<^sub>C_of ` ?mds\<^sub>A' m = range var\<^sub>C_of \<inter> ?mds\<^sub>C' m)"
        unfolding preserves_modes_mem_def by blast

      with GuarNoWrite_x\<^sub>A j_len j_len' mds\<^sub>A_of_def x_range conc.in_restrict_modesI var\<^sub>C_of_inj
      show "x \<in> (conc.restrict_modes (map snd cms\<^sub>C) (range var\<^sub>C_of) ! j) GuarNoWrite"
        unfolding var\<^sub>A_of_def
        by (metis (no_types, lifting) doesnt_have_mode f_inv_into_f image_inv_f_f nth_map)
    qed
qed

lemma compatible_modes_new_vars:
  "length mdss = length cms \<Longrightarrow> modes_respect_priv mdss \<Longrightarrow> conc.compatible_modes (conc.restrict_modes mdss (- range var\<^sub>C_of))"
unfolding conc.compatible_modes_def
proof(safe)
  let ?X = "- range var\<^sub>C_of"
  let ?mdss\<^sub>X = "conc.restrict_modes mdss ?X"
  assume respect: "modes_respect_priv mdss"
  assume len_eq: "length mdss = length cms"
  fix i x\<^sub>C j
  assume ilen: "i < length ?mdss\<^sub>X"
  assume jlen: "j < length ?mdss\<^sub>X"
  assume neq: "j \<noteq> i"
  assume asm\<^sub>X: "x\<^sub>C \<in> (?mdss\<^sub>X ! i) AsmNoWrite"
  from conc.in_restrict_modesD ilen asm\<^sub>X conc.restrict_modes_length have 
    xin: "x\<^sub>C \<in> ?X" and
    asm: "x\<^sub>C \<in> (mdss ! i) AsmNoWrite" by metis+
  from asm have "False"
    using respect xin ilen conc.restrict_modes_length len_eq
    unfolding modes_respect_priv_def new_asms_NoReadOrWrite_only_def
    by force
  thus "x\<^sub>C \<in> (?mdss\<^sub>X ! j) GuarNoWrite" by blast
next
  let ?X = "- range var\<^sub>C_of"
  let ?mdss\<^sub>X = "conc.restrict_modes mdss ?X"
  assume respect: "modes_respect_priv mdss"
  assume len_eq: "length mdss = length cms"
  fix i x\<^sub>C j
  assume ilen: "i < length ?mdss\<^sub>X"
  assume jlen: "j < length ?mdss\<^sub>X"
  assume neq: "j \<noteq> i"
  assume asm\<^sub>X: "x\<^sub>C \<in> (?mdss\<^sub>X ! i) AsmNoReadOrWrite"
  from conc.in_restrict_modesD ilen asm\<^sub>X conc.restrict_modes_length have 
    xin: "x\<^sub>C \<in> ?X" and
    asm: "x\<^sub>C \<in> (mdss ! i) AsmNoReadOrWrite" by metis+
  from respect asm xin ilen conc.restrict_modes_length len_eq have
    "x\<^sub>C \<in> priv_mem\<^sub>C ! i"
    unfolding modes_respect_priv_def new_asms_only_for_priv_def
    by force
  with respect ilen jlen neq conc.restrict_modes_length len_eq have
    "x\<^sub>C \<in> (mdss ! j) GuarNoReadOrWrite"
    unfolding modes_respect_priv_def priv_is_guar_priv_def
    by force
  with jlen xin conc.in_restrict_modesI show
    "x\<^sub>C \<in> (?mdss\<^sub>X ! j) GuarNoReadOrWrite" by force
qed

    
lemma sound_mode_use_preservation:
  "\<And>gc\<^sub>C gc\<^sub>A. 
    length (fst gc\<^sub>A) = length cms \<Longrightarrow> length (fst gc\<^sub>C) = length cms  \<Longrightarrow>
    (\<And>i. i < length cms \<Longrightarrow> ((fst gc\<^sub>A ! i, snd gc\<^sub>A), (fst gc\<^sub>C ! i, snd gc\<^sub>C)) \<in> \<R>_rel (cms ! i)) \<Longrightarrow>
    abs.sound_mode_use gc\<^sub>A \<Longrightarrow> modes_respect_priv (map snd (fst gc\<^sub>C)) \<Longrightarrow>
    conc.sound_mode_use gc\<^sub>C"
proof -
  fix gc\<^sub>C gc\<^sub>A
  assume len_eq [simp]: "length (fst gc\<^sub>A) = length cms"
     and len_eq'[simp]: "length (fst gc\<^sub>C) = length cms"
     and in_\<R>: "(\<And>i. i < length cms \<Longrightarrow> ((fst gc\<^sub>A ! i, snd gc\<^sub>A), (fst gc\<^sub>C ! i, snd gc\<^sub>C)) \<in> \<R>_rel (cms ! i))"
     and sound_mode_use\<^sub>A: "abs.sound_mode_use gc\<^sub>A"
     and modes_respect_priv: "modes_respect_priv (map snd (fst gc\<^sub>C))"
  have "conc.globally_sound_mode_use gc\<^sub>C"
  unfolding conc.globally_sound_mode_use_def
  proof(clarsimp)
    fix mdss\<^sub>C'
    assume in_reachable_modes: "mdss\<^sub>C' \<in> conc.reachable_mode_states gc\<^sub>C"
    from this obtain cms\<^sub>C' mem\<^sub>C' sched\<^sub>C where
      meval_sched\<^sub>C: "conc.meval_sched sched\<^sub>C gc\<^sub>C (cms\<^sub>C', mem\<^sub>C')" and
      mdss\<^sub>C'_def: "mdss\<^sub>C' = map snd cms\<^sub>C'"
      unfolding conc.reachable_mode_states_def by blast
    from traces_refinement[OF meval_sched\<^sub>C, OF len_eq len_eq' in_\<R> sound_mode_use\<^sub>A modes_respect_priv] 
    obtain sched\<^sub>A gc\<^sub>A' cms\<^sub>A' mem\<^sub>A' where gc\<^sub>A'_def [simp]: "gc\<^sub>A' = (cms\<^sub>A', mem\<^sub>A')"  and
      meval_sched\<^sub>A: "abs.meval_sched sched\<^sub>A gc\<^sub>A gc\<^sub>A'" and
      in_\<R>: "(\<forall>i<length cms.
              ((cms\<^sub>A' ! i, mem\<^sub>A'), cms\<^sub>C' ! i, mem\<^sub>C') \<in> \<R>_rel (cms ! i))"
      and sound_mode_use\<^sub>A': "abs.sound_mode_use gc\<^sub>A'"
        by fastforce
    let ?mdss\<^sub>A' = "map snd cms\<^sub>A'"
    have "?mdss\<^sub>A' \<in> abs.reachable_mode_states gc\<^sub>A"
      unfolding abs.reachable_mode_states_def
      using meval_sched\<^sub>A by fastforce
    hence compatible_modes\<^sub>A': "abs.compatible_modes ?mdss\<^sub>A'"
      using sound_mode_use\<^sub>A unfolding abs.sound_mode_use_def abs.globally_sound_mode_use_def
      by fastforce
    let ?X = "range var\<^sub>C_of"
    show "conc.compatible_modes mdss\<^sub>C'"
    proof(rule conc.compatible_modes_by_case_distinction[where X="?X"])
      show "conc.compatible_modes (conc.restrict_modes mdss\<^sub>C' ?X)"
        apply(simp add: mdss\<^sub>C'_def)
        apply(rule compatible_modes_old_vars[OF _ _ _ in_\<R>])
          apply(rule compatible_modes\<^sub>A')
         using len_eq abs.meval_sched_length[OF meval_sched\<^sub>A] gc\<^sub>A'_def apply simp
        using len_eq' conc.meval_sched_length[OF meval_sched\<^sub>C] by simp
    next
      show "conc.compatible_modes (conc.restrict_modes mdss\<^sub>C' (- ?X))"
        apply(rule compatible_modes_new_vars)
         using len_eq' conc.meval_sched_length[OF meval_sched\<^sub>C] mdss\<^sub>C'_def apply simp
        apply(simp add: mdss\<^sub>C'_def)
        apply(rule meval_sched_modes_respect_priv[OF meval_sched\<^sub>C, simplified])
        using modes_respect_priv by simp
    qed
  qed
  
  moreover have "list_all (\<lambda> cm. conc.locally_sound_mode_use (cm, (snd gc\<^sub>C))) (fst gc\<^sub>C)"
  unfolding list_all_length
  proof(clarify)
    fix i
    assume "i < length (fst gc\<^sub>C)"
    hence len: "i < length cms" by simp
    have preserves: "preserves_locally_sound_mode_use (\<R>_rel (cms ! i))"
      apply(rule locally_sound_mode_use_preservation)
       using secure_refinements len apply blast
      using local_guarantee_preservation len by blast
    have "abs.locally_sound_mode_use (fst gc\<^sub>A ! i, snd gc\<^sub>A)"
      using sound_mode_use\<^sub>A \<open>i < length cms\<close> len_eq
      unfolding abs.sound_mode_use_def list_all_length
      by (simp add: case_prod_unfold)
    
    from this in_\<R>[OF len] preserves[unfolded preserves_locally_sound_mode_use_def]
    show "conc.locally_sound_mode_use (fst gc\<^sub>C ! i, snd gc\<^sub>C)"
      by blast
  qed
      
  ultimately show "?thesis gc\<^sub>C gc\<^sub>A" unfolding conc.sound_mode_use_def 
  by (simp add: case_prod_unfold)
qed     
      
lemma refined_prog_secure:
  assumes len\<^sub>A [simp]: "length cms\<^sub>C = length cms"
  assumes len\<^sub>C [simp]: "length cms\<^sub>A = length cms"
  assumes in_\<R>: "(\<And>i mem\<^sub>C. i < length cms \<Longrightarrow>  ((cms\<^sub>A ! i,mem\<^sub>A_of mem\<^sub>C),(cms\<^sub>C ! i, mem\<^sub>C)) \<in> \<R>_rel (cms ! i))"
  assumes in_\<R>\<^sub>A: "(\<And>i mem\<^sub>C mem\<^sub>C'. \<lbrakk>i < length cms; conc.low_mds_eq (snd (cms\<^sub>C ! i)) mem\<^sub>C mem\<^sub>C'\<rbrakk>
       \<Longrightarrow> ((cms\<^sub>A ! i, mem\<^sub>A_of mem\<^sub>C), (cms\<^sub>A ! i, mem\<^sub>A_of mem\<^sub>C')) \<in> \<R>\<^sub>A_rel (cms ! i))"
  assumes sound_mode_use\<^sub>A: "(\<And> mem\<^sub>A.  abs.sound_mode_use (cms\<^sub>A, mem\<^sub>A))"
  assumes modes_respect_priv: "modes_respect_priv (map snd cms\<^sub>C)"
  shows "conc.prog_sifum_secure_cont cms\<^sub>C"
  apply(rule conc.sifum_compositionality_cont)
   apply(clarsimp simp: list_all_length)
   apply(clarsimp simp: conc.com_sifum_secure_def conc.low_indistinguishable_def)
   apply(rule conc.mm_equiv.intros)
    apply(rule R\<^sub>C_of_strong_low_bisim_mm)
      apply(fastforce intro: bisims)
     apply(fastforce intro: secure_refinements)
    apply(fastforce simp: Ps_sym)
   apply(clarsimp simp: R\<^sub>C_of_def)
   apply(rename_tac i c\<^sub>C mds\<^sub>C mem\<^sub>C mem\<^sub>C')
   apply(rule_tac x="fst (cms\<^sub>A ! i)" in exI)
   apply(rule_tac x="snd (cms\<^sub>A ! i)" in exI)
   apply(rule_tac x="mem\<^sub>A_of mem\<^sub>C" in exI)
   apply(rule conjI)
    using in_\<R> apply fastforce
   apply(rule_tac x="fst (cms\<^sub>A ! i)" in exI)
   apply(rule_tac x="snd (cms\<^sub>A ! i)" in exI)
   apply(rule_tac x="mem\<^sub>A_of mem\<^sub>C'" in exI)
   apply(rule conjI)
    using in_\<R> apply fastforce
   apply(fastforce simp: in_\<R>\<^sub>A Ps_refl_on_low_mds_eq)
  apply(clarify)
  apply(rename_tac mem\<^sub>C)
  apply(rule_tac gc\<^sub>A="(cms\<^sub>A,mem\<^sub>A_of mem\<^sub>C)" in sound_mode_use_preservation)
      apply simp
     apply simp
    using in_\<R> apply fastforce
   apply(rule sound_mode_use\<^sub>A)
  apply clarsimp
  by(rule modes_respect_priv)

lemma refined_prog_secure':
  assumes len\<^sub>A [simp]: "length cms\<^sub>C = length cms"
  assumes len\<^sub>C [simp]: "length cms\<^sub>A = length cms"
  assumes in_\<R>: "(\<And>i mem\<^sub>C. i < length cms \<Longrightarrow> ((cms\<^sub>A ! i,mem\<^sub>A_of mem\<^sub>C),(cms\<^sub>C ! i, mem\<^sub>C)) \<in> \<R>_rel (cms ! i))"
  assumes in_\<R>\<^sub>A: "(\<And>i mem\<^sub>A mem\<^sub>A'. \<lbrakk>i < length cms;  abs.low_mds_eq (snd (cms\<^sub>A ! i)) mem\<^sub>A mem\<^sub>A'\<rbrakk>
       \<Longrightarrow> ((cms\<^sub>A ! i, mem\<^sub>A), (cms\<^sub>A ! i, mem\<^sub>A')) \<in> \<R>\<^sub>A_rel (cms ! i))"
  assumes sound_mode_use\<^sub>A: "(\<And> mem\<^sub>A.  abs.sound_mode_use (cms\<^sub>A, mem\<^sub>A))"
  assumes modes_respect_priv: "modes_respect_priv (map snd cms\<^sub>C)"
  shows "conc.prog_sifum_secure_cont cms\<^sub>C"
  apply(rule refined_prog_secure)
       apply(rule len\<^sub>A)
      apply(rule len\<^sub>C)
     apply(blast intro: in_\<R>)
    apply(rule in_\<R>\<^sub>A)
     apply assumption
    apply(subgoal_tac "snd (cms\<^sub>A ! i) = mds\<^sub>A_of (snd (cms\<^sub>C ! i))")
     using low_mds_eq_from_conc_to_abs apply fastforce
    apply(rule_tac \<R>1="\<R>_rel (cms ! i)" and c\<^sub>A1="fst (cms\<^sub>A ! i)" and c\<^sub>C1="fst (cms\<^sub>C ! i)" in preserves_modes_memD[THEN conjunct2])
     using secure_refinements unfolding secure_refinement_def apply fast
    apply clarsimp
    using in_\<R> apply fastforce
   apply(blast intro: sound_mode_use\<^sub>A)
  by(rule modes_respect_priv)
    
end
  
context sifum_security begin

definition
  reachable_mems :: "('Com \<times> (Mode \<Rightarrow> 'Var set)) list \<Rightarrow> ('Var,'Val) Mem \<Rightarrow> ('Var,'Val) Mem set"
where
  "reachable_mems cms mem \<equiv> {mem'. \<exists>sched cms'. meval_sched sched (cms,mem) (cms',mem')}"

lemma reachable_mems_refl:
  "mem \<in> reachable_mems cms mem"
  apply(clarsimp simp: reachable_mems_def)
  apply(rule_tac x="[]" in exI)
  apply fastforce
  done
  
end

context sifum_refinement_sys begin

lemma reachable_mems_refinement:
  assumes sys_nonempty: "length cms > 0"
  assumes len\<^sub>A [simp]: "length cms\<^sub>C = length cms"
  assumes len\<^sub>C [simp]: "length cms\<^sub>A = length cms"
  assumes in_\<R>: "(\<And>i mem\<^sub>C. i < length cms \<Longrightarrow> ((cms\<^sub>A ! i,mem\<^sub>A_of mem\<^sub>C),(cms\<^sub>C ! i, mem\<^sub>C)) \<in> \<R>_rel (cms ! i))"
  assumes sound_mode_use\<^sub>A: "(\<And> mem\<^sub>A. abs.sound_mode_use (cms\<^sub>A, mem\<^sub>A))"
  assumes modes_respect_priv: "modes_respect_priv (map snd cms\<^sub>C)"
  assumes reachable\<^sub>C: "mem\<^sub>C' \<in> conc.reachable_mems cms\<^sub>C mem\<^sub>C"
  shows "mem\<^sub>A_of mem\<^sub>C' \<in> abs.reachable_mems cms\<^sub>A (mem\<^sub>A_of mem\<^sub>C)"
proof -
  from reachable\<^sub>C obtain sched\<^sub>C cms\<^sub>C' where
    meval_sched\<^sub>C: "conc.meval_sched sched\<^sub>C (cms\<^sub>C, mem\<^sub>C) (cms\<^sub>C', mem\<^sub>C')"
    by (fastforce simp: conc.reachable_mems_def)
  
  let ?mem\<^sub>A = "mem\<^sub>A_of mem\<^sub>C"
  
  have sound_mode_use\<^sub>A: "abs.sound_mode_use (cms\<^sub>A, ?mem\<^sub>A)"  
    by(rule sound_mode_use\<^sub>A)

  from traces_refinement[where gc\<^sub>A="(cms\<^sub>A,?mem\<^sub>A)", OF meval_sched\<^sub>C, OF _ _ _ sound_mode_use\<^sub>A]
       in_\<R>[of _ mem\<^sub>C]
       modes_respect_priv
  obtain sched\<^sub>A cms\<^sub>A' mem\<^sub>A' where
    meval_sched\<^sub>A: "abs.meval_sched sched\<^sub>A (cms\<^sub>A, ?mem\<^sub>A) (cms\<^sub>A', mem\<^sub>A')" and
    in_\<R>': "(\<forall>i<length cms.
               ((cms\<^sub>A' ! i, mem\<^sub>A'), cms\<^sub>C' ! i, mem\<^sub>C') \<in> \<R>_rel (cms ! i))"
    by fastforce
  hence reachable\<^sub>A: "mem\<^sub>A' \<in> abs.reachable_mems cms\<^sub>A ?mem\<^sub>A"
    by(fastforce simp: abs.reachable_mems_def)
  from sys_nonempty obtain i where ilen: "i < length cms" by blast
  let ?\<R>i = "\<R>_rel (cms ! i)"
  from ilen secure_refinements have "preserves_modes_mem ?\<R>i"
    unfolding secure_refinement_def by blast
  from ilen in_\<R>' preserves_modes_memD[OF this] have
    mem\<^sub>A'_def: "mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C'"
    by(metis surjective_pairing)
  with reachable\<^sub>A show ?thesis by simp
qed

end

end
