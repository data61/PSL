section \<open>Control Flow Graph\<close>
theory SM_Cfg
imports 
  SM_Syntax 
  "../Lib/LTS" 
  "../Lib/SOS_Misc_Add" 
begin
  text \<open>
    We define the control flow graph of SM, in the style of
    an structural operational semantics.
\<close>


  text \<open>
    The edges of the CFG are labeled with actions. These are
    assignments, tests, and skip.
    Assignment actions come in three versions: Assignment to local variables,
    assignment to global variables, and assignment to variables without
    specification of a scope. These will be mapped to local or global variables,
    depending on the scope.
\<close>
  datatype action = 
      AAssign exp ident exp | AAssign_local exp ident exp | AAssign_global exp ident exp
    | ATest exp | ASkip

  text \<open>
    Moreover, the semantics uses internal actions to handle break and continue
    statements. For well-formed programs, this type of actions will
    never be exposed
\<close>
  datatype brk_ctd = AIBreak | AIContinue

  text \<open>
    The control flow graph is a graph over commands, labeled with actions
\<close>
  inductive cfg :: "cmd \<Rightarrow> (action + brk_ctd) \<Rightarrow> cmd \<Rightarrow> bool" where
    Ass: "cfg (Assign c x e) (Inl (AAssign c x e)) Skip"
  | Assl: "cfg (Assign_local c x e) (Inl (AAssign_local c x e)) Skip"
  | Assg: "cfg (Assign_global c x e) (Inl (AAssign_global c x e)) Skip"
  | Test: "cfg (Test e) (Inl (ATest e)) Skip"

  | Seq1: "cfg (Seq Skip c2) (Inl ASkip) c2"
  | Seq2': "\<lbrakk> cfg c1 e Skip \<rbrakk> \<Longrightarrow> cfg (Seq c1 c2) e c2"
  | Seq2: "\<lbrakk> cfg c1 e c1'; c1'\<noteq>Skip \<rbrakk> \<Longrightarrow> cfg (Seq c1 c2) e (Seq c1' c2)"

  | Or1: "cfg c1 e c1' \<Longrightarrow> cfg (Or c1 c2) e c1'"
  | Or2: "cfg c2 e c2' \<Longrightarrow> cfg (Or c1 c2) e c2'"

  | Break: "cfg (Break) (Inr AIBreak) Invalid"
  | Continue: "cfg (Continue) (Inr AIContinue) Invalid"
  
  | Iterate1: "cfg (Iterate Skip c) (Inl ASkip) (Iterate c c)"
  | Iterate2': "\<lbrakk> cfg c (Inl e) Skip \<rbrakk> \<Longrightarrow> cfg (Iterate c cb) (Inl e) (Iterate cb cb)"
  | Iterate2: "\<lbrakk> cfg c (Inl e) c'; c'\<noteq>Skip \<rbrakk> \<Longrightarrow> cfg (Iterate c cb) (Inl e) (Iterate c' cb)"
  | IterateBrk: "\<lbrakk> cfg c (Inr AIBreak) _  \<rbrakk> \<Longrightarrow> cfg (Iterate c cb) (Inl ASkip) Skip"
  | IterateCtd: "\<lbrakk> cfg c (Inr AIContinue) _  \<rbrakk> \<Longrightarrow> cfg (Iterate c cb) (Inl ASkip) (Iterate cb cb)"

  inductive_cases Seq_cases: "cfg (Seq c1 c2) e c'"

section \<open>Reachable Nodes\<close>

interpretation cfg_lts: LTS cfg .

text \<open>Finite set of reachable CFG nodes\<close>

primrec reachable_term_order_aux :: "cmd \<Rightarrow> nat" where
  "reachable_term_order_aux (Assign c x e) = 0"
| "reachable_term_order_aux (Assign_local c x e) = 0"
| "reachable_term_order_aux (Assign_global c x e) = 0"
| "reachable_term_order_aux (Test e) = 0"
| "reachable_term_order_aux (Skip) = 0"
| "reachable_term_order_aux (Seq c1 c2) = reachable_term_order_aux c1 + reachable_term_order_aux c2"
| "reachable_term_order_aux (Or c1 c2) = reachable_term_order_aux c1 + reachable_term_order_aux c2"
| "reachable_term_order_aux (Break) = 0"
| "reachable_term_order_aux (Continue) = 0"
| "reachable_term_order_aux (Iterate c1 c2) = reachable_term_order_aux c1 + reachable_term_order_aux c2"
| "reachable_term_order_aux Invalid = 0"

function approx_reachable :: "cmd \<Rightarrow> cmd set" where
  "approx_reachable (Assign c x e) = {Assign c x e, Skip}"
| "approx_reachable (Assign_local c x e) = {Assign_local c x e, Skip}"
| "approx_reachable (Assign_global c x e) = {Assign_global c x e, Skip}"
| "approx_reachable (Test e) = {Test e, Skip}"
| "approx_reachable (Skip) = {Skip}"
| "approx_reachable (Seq c1 c2) = (approx_reachable c2) \<union> (do { c1\<leftarrow>approx_reachable c1; {Seq c1 c2} })"
| "approx_reachable (Or c1 c2) = insert (Or c1 c2) (approx_reachable c1 \<union> approx_reachable c2)"
| "approx_reachable (Break) = {Break,Invalid}"
| "approx_reachable (Continue) = {Continue,Invalid}"
| "approx_reachable (Iterate c1 c2) = insert Skip
    (do { c1\<leftarrow>approx_reachable c1; {Iterate c1 c2} })
  \<union> (do { c2'\<leftarrow>approx_reachable c2; {Iterate c2' c2} })"
| "approx_reachable Invalid = {Invalid}"
by pat_completeness auto

termination
  apply (relation "reachable_term_order_aux <*mlex*> measure size")
  apply (metis wf_measure wf_mlex)
  apply (auto simp: mlex_prod_def)
  done

lemma finite_approx_reachable[simp, intro!]: "finite (approx_reachable c)"
  by (induction c rule: approx_reachable.induct) auto

lemma approx_reachable_refl[simp]: "c\<in>approx_reachable c"
  by (induction c rule: approx_reachable.induct) auto

lemma approx_reachable_closed:
  assumes "c\<in>approx_reachable c0"
  assumes "cfg c a c'"
  shows "c'\<in>approx_reachable c0"
  using assms
  apply (induction c0 arbitrary: c c' rule: approx_reachable.induct)
  apply (auto elim: cfg.cases) [] 
  apply (auto elim: cfg.cases) [] 
  apply (auto elim: cfg.cases) [] 
  apply (auto elim: cfg.cases) [] 
  apply (auto elim: cfg.cases) []
  apply (auto elim: cfg.cases) []
  apply (auto, erule cfg.cases, simp_all, force+) []
  apply (auto elim: cfg.cases) [] 
  apply (auto elim: cfg.cases) [] 
  apply (auto elim: cfg.cases) []
  apply (auto elim: cfg.cases) [] 
  done

lemma approx_reachable_approx: "cfg_lts.reachable c c' \<Longrightarrow> c'\<in>approx_reachable c"
  unfolding cfg_lts.reachable_def
proof safe
  fix p
  assume "cfg_lts.path c p c'"
  thus "c'\<in>approx_reachable c"
    by (induction p arbitrary: c' rule: rev_induct)
       (auto intro: approx_reachable_closed)
qed

lemma finite_cfg_reachable: "finite (Collect (cfg_lts.reachable c))"
  apply (rule finite_subset[OF _ finite_approx_reachable])
  using approx_reachable_approx by auto

end

