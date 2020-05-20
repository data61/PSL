theory EgHighBranchRevC
imports Dependent_SIFUM_Type_Systems.Compositionality
        Dependent_SIFUM_Type_Systems.Language
        "HOL-Eisbach.Eisbach_Tools"
        "../CompositionalRefinement"
begin

text \<open>
  Theory for exploring refinement of a program that branches on a high variable.

  The purpose of this particular example is to demonstrate that in order to prove any branching
  on a High-classified variable remains safe when refined to a concrete implementation, it is
  necessary to ensure that the two concrete branches of execution take the same number of steps,
  possibly by skip-padding the one with less steps in it, and provide an appropriate coupling
  invariant to link the corresponding concrete steps of the two branches of the if-statement.
\<close>

type_synonym 'var addr = 'var
type_synonym val = nat
type_synonym 'var mem = "'var addr \<Rightarrow> val"

(* Arithmetic expression evaluation *)
datatype 'var aexp = Const "val" |
                     Load "'var addr" |
                     Add "'var aexp" "'var aexp" |
                     Sub "'var aexp" "'var aexp"

fun
  ev\<^sub>A :: "'var mem \<Rightarrow> 'var aexp \<Rightarrow> val"
where
  "ev\<^sub>A mem (Const v) = v" |
  "ev\<^sub>A mem (Load x) = mem x" |
  "ev\<^sub>A mem (Add x y) = ev\<^sub>A mem x + ev\<^sub>A mem y" |
  "ev\<^sub>A mem (Sub x y) = ev\<^sub>A mem x - ev\<^sub>A mem y"

(* Boolean expression evaluation *)
datatype 'var bexp = Eq "'var aexp" "'var aexp" |
                     Neq "'var aexp" "'var aexp" |
                     Lte "'var aexp" "'var aexp" |
                     Gt "'var aexp" "'var aexp"

fun
  ev\<^sub>B :: "'var mem \<Rightarrow> 'var bexp \<Rightarrow> bool"
where
  "ev\<^sub>B mem (Eq x y) = (ev\<^sub>A mem x = ev\<^sub>A mem y)" |
  "ev\<^sub>B mem (Neq x y) = (ev\<^sub>A mem x \<noteq> ev\<^sub>A mem y)" |
  "ev\<^sub>B mem (Lte x y) = (ev\<^sub>A mem x \<le> ev\<^sub>A mem y)" |
  "ev\<^sub>B mem (Gt x y) = (ev\<^sub>A mem x > ev\<^sub>A mem y)"

(* Function that gives the control variables of a given variable.
 * None for this example. *)
definition
  \<C>_vars :: "'var addr \<Rightarrow> 'var addr set"
where
  "\<C>_vars x \<equiv> {}"

(* NB: mds ~ "mode state"
 * mds\<^sub>s is the initial mode state *)
definition
  mds\<^sub>s :: "Mode \<Rightarrow> 'var set"
where
  "mds\<^sub>s \<equiv> \<lambda>m. case m of AsmNoReadOrWrite \<Rightarrow> {} | _ \<Rightarrow> {}"

primrec
  aexp_vars :: "'var aexp \<Rightarrow> 'var set"
where
  "aexp_vars (Const _) = {}" |
  "aexp_vars (Load v) = {v}" |
  "aexp_vars (Add x y) = aexp_vars x \<union> aexp_vars y" |
  "aexp_vars (Sub x y) = aexp_vars x \<union> aexp_vars y"

fun
  bexp_vars :: "'var bexp \<Rightarrow> 'var addr set"
where
  "bexp_vars (Neq x y) = aexp_vars x \<union> aexp_vars y" |
  "bexp_vars (Eq x y) = aexp_vars x \<union> aexp_vars y" |
  "bexp_vars (Lte x y) = aexp_vars x \<union> aexp_vars y" |
  "bexp_vars (Gt x y) = aexp_vars x \<union> aexp_vars y"

fun
  bexp_neg :: "'var bexp \<Rightarrow> 'var bexp"
where
  "bexp_neg (Neq x y) = (Eq x y)" |
  "bexp_neg (Eq x y) = (Neq x y)" |
  "bexp_neg (Lte x y) = (Gt x y)" |
  "bexp_neg (Gt x y) = (Lte x y)"

fun
  bexp_assign :: "'var addr \<Rightarrow> 'var aexp \<Rightarrow> 'var bexp"
where
  "bexp_assign x a = (Eq (Load x) a)"

datatype var = h_var | x_var | y_var | z_var

definition
  dma :: "var mem \<Rightarrow> var addr \<Rightarrow> Sec"
where
  "dma m x \<equiv> if x = h_var then High else Low"

type_synonym t_ev\<^sub>A = "var mem \<Rightarrow> var aexp \<Rightarrow> val"
type_synonym t_ev\<^sub>B = "var mem \<Rightarrow> var bexp \<Rightarrow> bool"
type_synonym t_aexp_vars = "var aexp \<Rightarrow> var set"
type_synonym t_bexp_vars = "var bexp \<Rightarrow> var addr set"

locale sifum_example =
  sifum_lang_no_dma "ev\<^sub>A::t_ev\<^sub>A" "ev\<^sub>B::t_ev\<^sub>B" "aexp_vars::t_aexp_vars" "bexp_vars::t_bexp_vars" +
  assumes eval_det: "(lc, lc') \<in> eval\<^sub>w \<Longrightarrow> (lc, lc'') \<in> eval\<^sub>w \<Longrightarrow> lc' = lc''"

definition
  \<C> :: "var addr set"
where
  "\<C> \<equiv> \<Union>x. \<C>_vars x"

sublocale sifum_example \<subseteq>  sifum_security dma \<C>_vars \<C> eval\<^sub>w undefined
  apply(unfold_locales)
       apply(blast intro: eval_det)
      apply(rule Var_finite)
     apply(auto simp: \<C>_vars_def dma_def \<C>_def split: if_splits)[3]
  apply(auto simp: \<C>_def)
  done

context sifum_example begin
(*
  y := 0; z := 0;
  x := y;
  if h then x := y
       else x := y + z

  Must have NoWrite z to prevent an agent getting something observable by spiking the value of z.
  Also take NoWrite y & h to simplify reasoning about reg values staying consistent with the mem.
 *)
definition
  prog_high_branch :: "(var addr, var aexp, var bexp) Stmt"
where
  "prog_high_branch \<equiv>
     ModeDecl Skip (Acq h_var AsmNoWrite) ;;
     ModeDecl Skip (Acq y_var AsmNoWrite) ;;
     ModeDecl Skip (Acq z_var AsmNoWrite) ;;
     Assign y_var (Const 0) ;;
     Assign z_var (Const 0) ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     )"
end

datatype var\<^sub>C = h_mem | x_mem | y_mem | z_mem | reg0 | reg1 | reg2 | reg3

definition
  dma\<^sub>C :: "var\<^sub>C mem \<Rightarrow> var\<^sub>C addr \<Rightarrow> Sec"
where
  "dma\<^sub>C m x \<equiv> if x = h_mem then High else Low"

type_synonym t_ev\<^sub>A\<^sub>C = "var\<^sub>C mem \<Rightarrow> var\<^sub>C aexp \<Rightarrow> val"
type_synonym t_ev\<^sub>B\<^sub>C = "var\<^sub>C mem \<Rightarrow> var\<^sub>C bexp \<Rightarrow> bool"
type_synonym t_aexp_vars\<^sub>C = "var\<^sub>C aexp \<Rightarrow> var\<^sub>C set"
type_synonym t_bexp_vars\<^sub>C = "var\<^sub>C bexp \<Rightarrow> var\<^sub>C addr set"

locale sifum_example\<^sub>C =
  sifum_lang_no_dma "ev\<^sub>A::t_ev\<^sub>A\<^sub>C" "ev\<^sub>B::t_ev\<^sub>B\<^sub>C" "aexp_vars::t_aexp_vars\<^sub>C" "bexp_vars::t_bexp_vars\<^sub>C" +
  assumes eval_det: "(lc, lc') \<in> eval\<^sub>w \<Longrightarrow> (lc, lc'') \<in> eval\<^sub>w \<Longrightarrow> lc' = lc''"

definition
  \<C>\<^sub>C :: "var\<^sub>C addr set"
where
  "\<C>\<^sub>C \<equiv> \<Union>x. \<C>_vars x"

sublocale sifum_example\<^sub>C \<subseteq>  sifum_security dma\<^sub>C \<C>_vars \<C>\<^sub>C eval\<^sub>w undefined
  apply(unfold_locales)
       apply(blast intro: eval_det)
      apply(rule Var_finite)
     apply(auto simp: \<C>_vars_def dma\<^sub>C_def \<C>_def split: if_splits)[3]
  apply(auto simp: \<C>\<^sub>C_def)
  done

context sifum_example\<^sub>C begin
(*
  y := 0; z := 0;
  x := y;
  if h
    then
      // "then"-branch: x := y
      NOP ;
      NOP ;
      LOAD r0 y ;
      STORE x r0 ;
    else
      // "else"-branch: x := y + z
      LOAD r1 y ;
      LOAD r2 z ;
      ADD r0 r1 r2 ;
      STORE x r0 ;
 *)
definition
  prog_high_branch\<^sub>C :: "(var\<^sub>C addr, var\<^sub>C aexp, var\<^sub>C bexp) Stmt"
where
  "prog_high_branch\<^sub>C \<equiv>
     ModeDecl Skip (Acq h_mem AsmNoWrite) ;;
     ModeDecl Skip (Acq y_mem AsmNoWrite) ;;
     ModeDecl Skip (Acq z_mem AsmNoWrite) ;;
     \<comment> \<open>Just set up the memory to match our assumptions\<close>
     Assign y_mem (Const 0) ;;
     Assign z_mem (Const 0) ;;
     Assign x_mem (Load y_mem) ;;
     \<comment> \<open>From this point onwards we model the if-statement using registers.\<close>
     \<comment> \<open>Note that we can just as well (re-)use reg0 instead of reg3 - verify with a search-replace.\<close>
     \<comment> \<open>Leaving it this way to make the reg usages easier to distinguish for the reader, though.\<close>
     Assign reg3 (Load h_mem) ;;
     If (Neq (Load reg3) (Const 0)) (
       Skip ;;
       Skip ;;
       Assign reg0 (Load y_mem) ;;
       Assign x_mem (Load reg0)
     ) (
       Assign reg1 (Load y_mem) ;;
       Assign reg2 (Load z_mem) ;;
       Assign reg0 (Add (Load reg1) (Load reg2)) ;;
       Assign x_mem (Load reg0)
     )"
end

context sifum_example begin
lemma \<C>_simp[simp]:
  "\<C> = {}"
  by(auto simp: \<C>_def \<C>_vars_def split: if_splits)

declare \<C>_vars_def [simp]

(* Manual proof of bisimulation because we can't use the type system *)
inductive inv :: "(((var addr, var aexp, var bexp) Stmt, var addr, val) LocalConf) \<Rightarrow> bool"
where
  inv\<^sub>1h: "\<lbrakk>c = prog_high_branch; mds AsmNoReadOrWrite = {}; mds AsmNoWrite = {}\<rbrakk> \<Longrightarrow> inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>1h': "\<lbrakk>c =
     Stop ;;
     ModeDecl Skip (Acq y_var AsmNoWrite) ;;
     ModeDecl Skip (Acq z_var AsmNoWrite) ;;
     Assign y_var (Const 0) ;;
     Assign z_var (Const 0) ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ); mds AsmNoWrite = {h_var}; mds AsmNoReadOrWrite = {}\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>1y: "\<lbrakk>c =
     ModeDecl Skip (Acq y_var AsmNoWrite) ;;
     ModeDecl Skip (Acq z_var AsmNoWrite) ;;
     Assign y_var (Const 0) ;;
     Assign z_var (Const 0) ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ); mds AsmNoWrite = {h_var}; mds AsmNoReadOrWrite = {}\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>1y': "\<lbrakk>c =
     Stop ;;
     ModeDecl Skip (Acq z_var AsmNoWrite) ;;
     Assign y_var (Const 0) ;;
     Assign z_var (Const 0) ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ); mds AsmNoWrite = {y_var, h_var}; mds AsmNoReadOrWrite = {}\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>1z: "\<lbrakk>c =
     ModeDecl Skip (Acq z_var AsmNoWrite) ;;
     Assign y_var (Const 0) ;;
     Assign z_var (Const 0) ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ); mds AsmNoWrite = {y_var, h_var}; mds AsmNoReadOrWrite = {}\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>1z': "\<lbrakk>c =
     Stop ;;
     Assign y_var (Const 0) ;;
     Assign z_var (Const 0) ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ); mds AsmNoWrite = {z_var, y_var, h_var}; mds AsmNoReadOrWrite = {}\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>2: "\<lbrakk>c =
     Assign y_var (Const 0) ;;
     Assign z_var (Const 0) ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ); mds AsmNoWrite = {z_var, y_var, h_var}; mds AsmNoReadOrWrite = {}\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>2': "\<lbrakk>c =
     Stop ;;
     Assign z_var (Const 0) ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ); mds AsmNoWrite = {z_var, y_var, h_var}; mds AsmNoReadOrWrite = {}\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>3: "\<lbrakk>c =
     Assign z_var (Const 0) ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ); mds AsmNoWrite = {z_var, y_var, h_var}; mds AsmNoReadOrWrite = {}\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>3': "\<lbrakk>c =
     Stop ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ); mds AsmNoWrite = {z_var, y_var, h_var}; mds AsmNoReadOrWrite = {}; mem z_var = 0\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>4: "\<lbrakk>c =
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ); mds AsmNoWrite = {z_var, y_var, h_var}; mds AsmNoReadOrWrite = {}; mem z_var = 0\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>4': "\<lbrakk>c =
     Stop ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ); mds AsmNoWrite = {z_var, y_var, h_var}; mds AsmNoReadOrWrite = {}; mem z_var = 0\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>5: "\<lbrakk>c =
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ); mds AsmNoWrite = {z_var, y_var, h_var}; mds AsmNoReadOrWrite = {}; mem z_var = 0\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>5_then: "\<lbrakk>c = Assign x_var (Load y_var);
     mds AsmNoWrite = {z_var, y_var, h_var}; mds AsmNoReadOrWrite = {}; mem z_var = 0\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>5_else: "\<lbrakk>c = Assign x_var (Add (Load y_var) (Load z_var));
     mds AsmNoWrite = {z_var, y_var, h_var}; mds AsmNoReadOrWrite = {}; mem z_var = 0\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>6: "\<lbrakk>c = Stop\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>"

definition z_locked_steps
where "z_locked_steps \<equiv> {
     Stop ;;
     Assign y_var (Const 0) ;;
     Assign z_var (Const 0) ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ),
     Assign y_var (Const 0) ;;
     Assign z_var (Const 0) ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ),
     Stop ;;
     Assign z_var (Const 0) ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     ),
     Assign z_var (Const 0) ;;
     Assign x_var (Load y_var) ;;
     If (Neq (Load h_var) (Const 0)) (
       Assign x_var (Load y_var)
     ) (
       Assign x_var (Add (Load y_var) (Load z_var))
     )}"

inductive_set rel_inv :: "(((var addr, var aexp, var bexp) Stmt, var addr, val) LocalConf) rel"
where
  rel_inv_if:
  "\<lbrakk>c = Assign x_var (Load y_var);
    c' = Assign x_var (Add (Load y_var) (Load z_var));
    z_var \<in> mds AsmNoWrite; mds AsmNoReadOrWrite = {}; mem z_var = mem' z_var\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv" |
  rel_inv_if':
  "\<lbrakk>c' = Assign x_var (Load y_var);
    c = Assign x_var (Add (Load y_var) (Load z_var));
    z_var \<in> mds AsmNoWrite; mds AsmNoReadOrWrite = {}; mem z_var = mem' z_var\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv" |
  rel_inv_start:
  "\<lbrakk>c = c'; z_var \<notin> mds AsmNoWrite; mds AsmNoReadOrWrite = {}\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv" |
  rel_inv_z_locked:
  "\<lbrakk>c \<in> z_locked_steps;
    c = c'; z_var \<in> mds AsmNoWrite; mds AsmNoReadOrWrite = {}\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv" |
  rel_inv_z_initted:
  "\<lbrakk>c \<notin> z_locked_steps;
    c = c'; mem z_var = mem' z_var; z_var \<in> mds AsmNoWrite; mds AsmNoReadOrWrite = {}\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv"

declare z_locked_steps_def[simp add]

(* the bisimulation is phrased as a conjunction of a global invariant and a
   relational invariant, defined above, plus the background requirement
   of low-equivalence modulo modes *)
inductive_set  R :: "(((var addr, var aexp, var bexp) Stmt, var addr, val) LocalConf) rel"
where
(* Having a c = c' requirement here is actually too restrictive *)
  "\<lbrakk>mds = mds'; low_mds_eq mds mem mem'; inv \<langle>c,mds,mem\<rangle>; inv \<langle>c',mds',mem'\<rangle>;
    (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv\<rbrakk> \<Longrightarrow>
 (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> R"

lemma rel_inv_sym:
  "low_mds_eq mds mem mem' \<Longrightarrow> (\<langle>c, mds, mem\<rangle>, \<langle>c, mds, mem'\<rangle>) \<in> rel_inv \<Longrightarrow>
    (\<langle>c, mds, mem'\<rangle>, \<langle>c, mds, mem\<rangle>) \<in> rel_inv"
  apply(auto elim!: rel_inv.cases intro: rel_inv.intros)
  done

lemma R_sym':
  "(\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> R \<Longrightarrow>
   (\<langle>c', mds', mem'\<rangle>, \<langle>c, mds, mem\<rangle>) \<in> R"
  apply(rule R.intros)
      apply(blast elim: R.cases dest: low_mds_eq_sym dest: rel_inv_sym)+
  apply(erule R.cases)
  apply(erule rel_inv.cases)
      apply clarsimp
      apply(rule rel_inv_if', simp+)
     apply(rule rel_inv_if, simp+)
    apply(rule rel_inv_start, simp+)
   apply(rule rel_inv_z_locked, simp+)
  apply(rule rel_inv_z_initted, simp+)
  done

lemma R_sym:
  "sym R"
  by(rule symI, clarify, erule R_sym')

lemma inv_closed_glob_consistent:
  "inv \<langle>c', mds', mem\<rangle> \<Longrightarrow>
       \<forall>x. case A x of None \<Rightarrow> True | Some (v, v') \<Rightarrow> mem x \<noteq> v \<longrightarrow> \<not> var_asm_not_written mds' x \<Longrightarrow>
       \<forall>x. dma mem [\<parallel>\<^sub>1 A] x \<noteq> dma mem x \<longrightarrow> \<not> var_asm_not_written mds' x  \<Longrightarrow>
       inv \<langle>c', mds', mem [\<parallel>\<^sub>1 A]\<rangle>"
  apply(erule inv.cases)
             using inv.intros apply (force, force, force, force, force, force, force, force, force)
        apply(rule inv\<^sub>3', clarsimp+)
        apply(erule_tac x=z_var in allE)
        apply(erule_tac x=z_var in allE)
        apply(cases "A z_var")
         apply(simp add:apply_adaptation_def)
        apply(clarsimp simp add:var_asm_not_written_def dma_def apply_adaptation_def)
       apply(rule inv\<^sub>4, clarsimp+)
       apply(erule_tac x=z_var in allE)
       apply(erule_tac x=z_var in allE)
       apply(cases "A z_var")
        apply(simp add:apply_adaptation_def)
       apply(clarsimp simp add:var_asm_not_written_def dma_def apply_adaptation_def)
      apply(rule inv\<^sub>4', clarsimp+)
      apply(erule_tac x=z_var in allE)
      apply(erule_tac x=z_var in allE)
      apply(cases "A z_var")
       apply(simp add:apply_adaptation_def)
      apply(clarsimp simp add:var_asm_not_written_def dma_def apply_adaptation_def)
     apply(rule inv\<^sub>5, clarsimp+)
     apply(erule_tac x=z_var in allE)
     apply(erule_tac x=z_var in allE)
     apply(cases "A z_var")
      apply(simp add:apply_adaptation_def)
     apply(clarsimp simp add:var_asm_not_written_def dma_def apply_adaptation_def)
    apply(rule inv\<^sub>5_then, clarsimp+)
    apply(erule_tac x=z_var in allE)
    apply(erule_tac x=z_var in allE)
    apply(cases "A z_var")
     apply(simp add:apply_adaptation_def)
    apply(clarsimp simp add:var_asm_not_written_def dma_def apply_adaptation_def)
   apply(rule inv\<^sub>5_else, clarsimp+)
   apply(erule_tac x=z_var in allE)
   apply(erule_tac x=z_var in allE)
   apply(cases "A z_var")
    apply(simp add:apply_adaptation_def)
   apply(clarsimp simp add:var_asm_not_written_def dma_def apply_adaptation_def)
  apply(rule inv\<^sub>6, clarsimp+)
  done

(* The "right-hand" side of inv_closed_glob_consistent *)
lemma inv_closed_glob_consistent_r:
  "inv \<langle>c', mds', mem\<rangle> \<Longrightarrow>
       \<forall>x. case A x of None \<Rightarrow> True | Some (v, v') \<Rightarrow> mem x \<noteq> v' \<longrightarrow> \<not> var_asm_not_written mds' x \<Longrightarrow>
       \<forall>x. dma mem [\<parallel>\<^sub>2 A] x \<noteq> dma mem x \<longrightarrow> \<not> var_asm_not_written mds' x  \<Longrightarrow>
       inv \<langle>c', mds', mem [\<parallel>\<^sub>2 A]\<rangle>"
  apply(erule inv.cases)
               using inv.intros apply (force, force, force, force, force, force, force, force, force)
        apply(rule inv\<^sub>3', clarsimp+)
        apply(erule_tac x=z_var in allE)
        apply(erule_tac x=z_var in allE)
        apply(cases "A z_var")
         apply(simp add:apply_adaptation_def)
        apply(clarsimp simp add:var_asm_not_written_def dma_def apply_adaptation_def)
       apply(rule inv\<^sub>4, clarsimp+)
       apply(erule_tac x=z_var in allE)
       apply(erule_tac x=z_var in allE)
       apply(cases "A z_var")
        apply(simp add:apply_adaptation_def)
       apply(clarsimp simp add:var_asm_not_written_def dma_def apply_adaptation_def)
      apply(rule inv\<^sub>4', clarsimp+)
      apply(erule_tac x=z_var in allE)
      apply(erule_tac x=z_var in allE)
      apply(cases "A z_var")
       apply(simp add:apply_adaptation_def)
      apply(clarsimp simp add:var_asm_not_written_def dma_def apply_adaptation_def)
     apply(rule inv\<^sub>5, clarsimp+)
     apply(erule_tac x=z_var in allE)
     apply(erule_tac x=z_var in allE)
     apply(cases "A z_var")
      apply(simp add:apply_adaptation_def)
     apply(clarsimp simp add:var_asm_not_written_def dma_def apply_adaptation_def)
    apply(rule inv\<^sub>5_then, clarsimp+)
    apply(erule_tac x=z_var in allE)
    apply(erule_tac x=z_var in allE)
    apply(cases "A z_var")
     apply(simp add:apply_adaptation_def)
    apply(clarsimp simp add:var_asm_not_written_def dma_def apply_adaptation_def)
   apply(rule inv\<^sub>5_else, clarsimp+)
   apply(erule_tac x=z_var in allE)
   apply(erule_tac x=z_var in allE)
   apply(cases "A z_var")
    apply(simp add:apply_adaptation_def)
   apply(clarsimp simp add:var_asm_not_written_def dma_def apply_adaptation_def)
  apply(rule inv\<^sub>6, clarsimp+)
  done

lemma rel_inv_closed_glob_consistent:
  "(\<langle>c, mds', mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv \<Longrightarrow>
       \<forall>x a b.
          A x = Some (a, b) \<longrightarrow>
          (mem x = a \<longrightarrow> mem' x \<noteq> b) \<longrightarrow> \<not> var_asm_not_written mds' x \<Longrightarrow>
       \<forall>x. dma mem [\<parallel>\<^sub>1 A] x \<noteq> dma mem x \<longrightarrow> \<not> var_asm_not_written mds' x \<Longrightarrow>
       \<forall>x. dma mem [\<parallel>\<^sub>1 A] x = Low \<and> (x \<in> mds' AsmNoReadOrWrite \<longrightarrow> x \<in> \<C>) \<longrightarrow>
           mem [\<parallel>\<^sub>1 A] x = mem' [\<parallel>\<^sub>2 A] x \<Longrightarrow>
       (\<langle>c, mds', mem [\<parallel>\<^sub>1 A]\<rangle>, \<langle>c', mds', mem' [\<parallel>\<^sub>2 A]\<rangle>) \<in> rel_inv"
  apply(safe elim!: rel_inv.cases)
  using rel_inv.intros dma_def by simp+

lemma R_closed_glob_consistent:
  "closed_glob_consistent R"
  unfolding closed_glob_consistent_def
  apply clarsimp
  apply(erule R.cases)
  apply clarsimp
  apply(rule R.intros)
      apply simp
     apply(fastforce simp: low_mds_eq_def)
    apply(rule inv_closed_glob_consistent)
      apply simp
     apply(fastforce split: option.splits)
    apply assumption
   apply(rule inv_closed_glob_consistent_r)
     apply simp
    apply(fastforce split: option.splits)
   apply(subgoal_tac "dma mem = dma mem' \<and> dma mem [\<parallel>\<^sub>1 A] = dma mem' [\<parallel>\<^sub>2 A]")
    apply simp
   apply(rule conjI)
    apply(rule low_mds_eq_dma)
    apply assumption
   apply(rule dma_\<C>)
   apply(simp add: \<C>_Low)
  apply(rule rel_inv_closed_glob_consistent)
  apply(simp_all)
  apply(fastforce split: option.splits)
  done

lemma R_low_mds_eq:
  "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> R \<Longrightarrow>
        low_mds_eq mds mem\<^sub>1 mem\<^sub>2"
  apply(blast elim: R.cases)
  done

inductive_cases rel_invE: "(\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv"

method seq_decl_inv_method uses inv_rule rel_inv_rule =
 (erule rel_invE, simp+,
   drule seq_elim, simp,
   clarsimp,
   drule upd_elim, drule skip_elim, simp,
   clarsimp,
   rule conjI,
    rule eval\<^sub>w.seq,
    rule decl_eval\<^sub>w', simp+,
   rule R.intros, simp+,
      fastforce simp: low_mds_eq_def,
     rule inv_rule, simp+,
    rule inv_rule, simp+,
   rule rel_inv_rule, simp+)

method seq_stop_inv_method uses inv_rule rel_inv_rule =
 (erule rel_invE, simp+,
   drule seq_stop_elim, clarsimp,
   (rule exI)+,
   intro conjI,
    rule seq_stop_eval\<^sub>w,
   rule R.intros, (simp|clarsimp simp: low_mds_eq_def dma_def ev\<^sub>A.simps)+,
     (rule inv_rule; simp|blast?),
    (rule inv_rule; simp|blast?),
   rule rel_inv_rule, simp+)

method assign_inv\<^sub>6_method =
 (rule_tac x=c\<^sub>1' in exI,
  rule_tac x="mem\<^sub>2(x_var := ev\<^sub>A mem\<^sub>2 (Load y_var))" in exI,
  erule rel_invE, simp+,
  (drule assign_elim, simp,
   rule conjI,
    clarsimp simp: ev\<^sub>A.simps,
    erule_tac x=z_var in allE,
    clarsimp,
    rule assign_eval\<^sub>w', simp+,
    clarsimp simp: ev\<^sub>A.simps,
   rule R.intros, simp+,
      unfold low_mds_eq_def dma_def, clarsimp simp: ev\<^sub>A.simps,
     (rule inv\<^sub>6, simp+)+,
   rule rel_inv_z_initted, simp+)+)

lemma R_inv:
  notes ev\<^sub>A.simps[simp del]
  shows  "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> R \<Longrightarrow>
       (\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>) \<in> eval\<^sub>w \<Longrightarrow>
       \<exists>c\<^sub>2' mem\<^sub>2'.
          (\<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>, \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>) \<in> eval\<^sub>w \<and>
          (\<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>, \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>) \<in> R"
  apply(erule R.cases)
  apply clarsimp
  apply(erule inv.cases)
                 apply(unfold prog_high_branch_def)
                 apply clarsimp
                 apply(rule_tac x=c\<^sub>1' in exI)
                 apply(rule_tac x=mem\<^sub>2 in exI)
                 apply(seq_decl_inv_method inv_rule:inv\<^sub>1h' rel_inv_rule:rel_inv_start)
                apply(seq_stop_inv_method inv_rule:inv\<^sub>1y rel_inv_rule:rel_inv_start)
               apply(rule_tac x=c\<^sub>1' in exI)
               apply(rule_tac x=mem\<^sub>2 in exI)
               apply(seq_decl_inv_method inv_rule:inv\<^sub>1y' rel_inv_rule:rel_inv_start)
              apply(seq_stop_inv_method inv_rule:inv\<^sub>1z rel_inv_rule:rel_inv_start)
             apply(rule_tac x=c\<^sub>1' in exI)
             apply(rule_tac x=mem\<^sub>2 in exI)
             apply(seq_decl_inv_method inv_rule:inv\<^sub>1z' rel_inv_rule:rel_inv_z_locked)
            apply(seq_stop_inv_method inv_rule:inv\<^sub>2 rel_inv_rule:rel_inv_z_locked)

           (* Assign ;; *)
           apply clarsimp
           apply(rule_tac x=c\<^sub>1' in exI)
           apply(rule_tac x="mem\<^sub>2(y_var := ev\<^sub>A mem\<^sub>2 (Const 0))" in exI)
           apply(erule rel_invE, simp+)
            apply(drule seq_elim, simp)
            apply clarsimp
            apply(drule assign_elim, simp)
            apply(rule conjI)
             apply(rule eval\<^sub>w.seq)
             apply(rule assign_eval\<^sub>w)
            apply(rule R.intros, simp+)
               apply(unfold low_mds_eq_def dma_def, clarsimp simp: ev\<^sub>A.simps)
              apply(rule inv\<^sub>2', fast+)+
            apply(rule rel_inv_z_locked, simp+)
          apply(seq_stop_inv_method inv_rule:inv\<^sub>3 rel_inv_rule:rel_inv_z_locked)

         (* Assign ;; *)
         apply clarsimp
         apply(rule_tac x=c\<^sub>1' in exI)
         apply(rule_tac x="mem\<^sub>2(z_var := ev\<^sub>A mem\<^sub>2 (Const 0))" in exI)
         apply(erule rel_invE, simp+)
          apply(drule seq_elim, simp)
          apply clarsimp
          apply(drule assign_elim, simp)
          apply(rule conjI)
           apply(rule eval\<^sub>w.seq)
           apply(rule assign_eval\<^sub>w)
          apply(rule R.intros, simp+)
             apply(unfold low_mds_eq_def dma_def, clarsimp simp: ev\<^sub>A.simps)
            apply(rule inv\<^sub>3', simp+)
            apply(simp add: ev\<^sub>A.simps)
           apply(rule inv\<^sub>3', simp+)
           apply(simp add: ev\<^sub>A.simps)
          apply(rule rel_inv_z_initted, simp+)
            apply(simp add: ev\<^sub>A.simps) (* do it separately so it doesn't mess everything else up *)
           apply simp+
        apply(seq_stop_inv_method inv_rule:inv\<^sub>4 rel_inv_rule:rel_inv_z_initted)

       (* Assign ;; *)
       apply clarsimp
       apply(rule_tac x=c\<^sub>1' in exI)
       apply(rule_tac x="mem\<^sub>2(x_var := ev\<^sub>A mem\<^sub>2 (Load y_var))" in exI)
       apply(erule rel_invE, simp+)
       apply(drule seq_elim, simp)
       apply clarsimp
       apply(drule assign_elim, simp)
       apply(rule conjI)
        apply(rule eval\<^sub>w.seq)
        apply(rule assign_eval\<^sub>w)
       apply(rule R.intros, simp+)
          apply(unfold low_mds_eq_def dma_def, clarsimp simp: ev\<^sub>A.simps)
         apply(rule inv\<^sub>4', simp+)+
       apply(rule rel_inv_z_initted, simp+)
      apply(seq_stop_inv_method inv_rule:inv\<^sub>5 rel_inv_rule:rel_inv_z_initted)

     (* (If (cond) Then Else) *)
     apply clarsimp
     apply(erule rel_invE, simp+)
     apply(rule_tac x="(if ev\<^sub>B mem\<^sub>2 (Neq (Load h_var) (Const 0))
                        then (x_var \<leftarrow> Load y_var)
                        else (x_var \<leftarrow> Add (Load y_var) (Load z_var)))" in exI)
     apply(rule_tac x="mem\<^sub>2" in exI)
     apply(rule conjI)
       apply(erule if_elim)
        apply clarify
        apply(rule if_eval\<^sub>w)
       apply clarify
       apply(rule if_eval\<^sub>w)
      apply(erule if_elim)
       apply(rule R.intros, simp+)
          apply(unfold low_mds_eq_def dma_def, clarsimp)
         apply(rule inv\<^sub>5_then, simp+)
        apply safe
         apply(rule inv\<^sub>5_then, simp+)
        apply(rule inv\<^sub>5_else, simp+)
       apply safe
        apply(rule rel_inv_z_initted, simp+)
       apply(rule rel_inv_if, simp, simp, simp, simp, simp)
 
     apply(rule R.intros, simp+)
        apply(unfold low_mds_eq_def dma_def, clarsimp)
       apply(rule inv\<^sub>5_else, simp+)
      apply safe
       apply(rule inv\<^sub>5_then, simp+)
      apply(rule inv\<^sub>5_else, simp+)
     apply safe
      apply(rule rel_inv_if', simp+)
     apply(rule rel_inv_z_initted, simp+)
 
    (* Assign - then | else *)
    apply assign_inv\<^sub>6_method
   apply assign_inv\<^sub>6_method
  using stop_no_eval by fastforce

lemma strong_low_bisim_mm_R:
  "strong_low_bisim_mm R"
  unfolding strong_low_bisim_mm_def
  proof(safe)
    show "sym R" by(rule R_sym)
  next
    show "closed_glob_consistent R" by(rule R_closed_glob_consistent)
  next
    fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2  mem\<^sub>2
    assume "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> R"
    thus "low_mds_eq mds mem\<^sub>1 mem\<^sub>2"
    by(rule R_low_mds_eq)
  next
    fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2  mem\<^sub>2 c\<^sub>1' mds' mem\<^sub>1'
    assume "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> R"
       and "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>) \<in> eval\<^sub>w"
    thus "\<exists>c\<^sub>2' mem\<^sub>2'.
          (\<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>, \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>) \<in> eval\<^sub>w \<and>
          (\<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>, \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>) \<in> R"
       by(rule R_inv)
  qed

lemma prog_high_branch_secure':
  "low_mds_eq mds\<^sub>s mem\<^sub>1 mem\<^sub>2 \<Longrightarrow>
       (\<langle>prog_high_branch, mds\<^sub>s, mem\<^sub>1\<rangle>, \<langle>prog_high_branch, mds\<^sub>s, mem\<^sub>2\<rangle>) \<in> R"
  apply(rule R.intros)
  apply simp_all
   apply(rule inv\<^sub>1h)
     apply (simp_all add: mds\<^sub>s_def)
   apply(rule inv\<^sub>1h)
     apply (simp_all add: mds\<^sub>s_def)
  unfolding prog_high_branch_def by(fastforce intro: rel_inv.intros)

lemma "com_sifum_secure (prog_high_branch, mds\<^sub>s)"
  unfolding com_sifum_secure_def low_indistinguishable_def
  apply clarify
  apply(rule mm_equiv_intro)
   apply(rule strong_low_bisim_mm_R)
  by (rule prog_high_branch_secure')

end

locale sifum_refinement_high_branch =
  A: sifum_example +
  C: sifum_example\<^sub>C

primrec var\<^sub>C_of :: "var \<Rightarrow> var\<^sub>C"
where
  "var\<^sub>C_of h_var = h_mem" |
  "var\<^sub>C_of x_var = x_mem" |
  "var\<^sub>C_of y_var = y_mem" |
  "var\<^sub>C_of z_var = z_mem"

sublocale sifum_refinement_high_branch \<subseteq>
  sifum_refinement dma dma\<^sub>C \<C>_vars \<C>_vars \<C> \<C>\<^sub>C A.eval\<^sub>w C.eval\<^sub>w undefined var\<^sub>C_of
  apply(unfold_locales)
     apply(rule inj_onI, simp)
     apply(case_tac x)
         apply(case_tac y, simp+)
        apply(case_tac y, simp+)
       apply(case_tac y, simp+)
      apply(case_tac y, simp+)
    apply(case_tac x\<^sub>A)
       apply(clarsimp simp:dma_def dma\<^sub>C_def)+
  done

context sifum_refinement_high_branch begin

(* Adapted these helpers from Eg1Eg2 *)
lemma conc_only_vars_not_visible_abs:
  "(\<forall>v\<^sub>C. v\<^sub>C \<in> range var\<^sub>C_of \<longrightarrow> mem\<^sub>C v\<^sub>C = mem\<^sub>C' v\<^sub>C) \<Longrightarrow> mem\<^sub>A_of mem\<^sub>C = mem\<^sub>A_of mem\<^sub>C'"
  by (simp add: mem\<^sub>A_of_def)

lemma conc_only_var_assign_not_visible_abs:
  "\<forall>v\<^sub>C e. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> mem\<^sub>A_of mem\<^sub>C = mem\<^sub>A_of (mem\<^sub>C(v\<^sub>C := e))"
  using conc_only_vars_not_visible_abs
  by simp

lemma reg_is_not_the_var\<^sub>C_of_anything:
  "reg \<in> {reg0, reg1, reg2, reg3} \<Longrightarrow> reg = var\<^sub>C_of x \<Longrightarrow> False"
  by (induct x, clarsimp+)

lemma reg_not_visible_abs:
  "reg \<in> {reg0, reg1, reg2, reg3} \<Longrightarrow> reg \<notin> range var\<^sub>C_of"
  using reg_is_not_the_var\<^sub>C_of_anything
  by blast

(* Helpers carried over from Eg1Eg2 *)
lemma assign_eval\<^sub>w_load\<^sub>A:
  shows "(\<langle>x \<leftarrow> Load y, mds, mem\<rangle>\<^sub>A, \<langle>Stop, mds, mem (x := mem y)\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
  by (metis A.assign_eval\<^sub>w ev\<^sub>A.simps(2))

lemma assign_eval\<^sub>w_load\<^sub>C:
  shows "(\<langle>x \<leftarrow> Load y, mds, mem\<rangle>\<^sub>C, \<langle>Stop, mds, mem (x := mem y)\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
  using C.unannotated[OF C.assign, where E="[]", simplified]
  apply(drule_tac x=x in meta_spec)
  apply(drule_tac x="Load y" in meta_spec)
  apply(drule_tac x=mds in meta_spec)
  apply(drule_tac x=mem in meta_spec)
  apply clarsimp
  done

lemma assign_eval\<^sub>w_const\<^sub>A:
  shows "(\<langle>x \<leftarrow> Const c, mds, mem\<rangle>, \<langle>Stop, mds, mem (x := c)\<rangle>) \<in> A.eval\<^sub>w"
  by (metis A.assign_eval\<^sub>w ev\<^sub>A.simps(1))

lemma assign_eval\<^sub>w_const\<^sub>C:
  shows "(\<langle>x \<leftarrow> Const c, mds, mem\<rangle>, \<langle>Stop, mds, mem (x := c)\<rangle>) \<in> C.eval\<^sub>w"
  using C.unannotated[OF C.assign, where E="[]", simplified]
  apply(drule_tac x=x in meta_spec)
  apply(drule_tac x="Const c" in meta_spec)
  apply(drule_tac x=mds in meta_spec)
  apply(drule_tac x=mem in meta_spec)
  apply clarsimp
  done

lemma mem_assign_refinement_helper_var:
  "mem\<^sub>A_of (mem\<^sub>C (var\<^sub>C_of x := mem\<^sub>C (var\<^sub>C_of y)))
       = (mem\<^sub>A_of mem\<^sub>C) (x := (mem\<^sub>A_of mem\<^sub>C) y)"
  apply(clarsimp simp: mem\<^sub>A_of_def)
  apply(rule ext, clarsimp)
  apply(cases x)
   apply(case_tac x\<^sub>A, clarsimp+)+
  done

lemma mem_assign_refinement_helper_const:
  "mem\<^sub>A_of (mem\<^sub>C (var\<^sub>C_of x := c))
       = (mem\<^sub>A_of mem\<^sub>C) (x := c)"
  apply(clarsimp simp: mem\<^sub>A_of_def)
  apply(rule ext, clarsimp)
  apply(cases x)
      apply(case_tac x\<^sub>A, clarsimp+)+
  done

lemma NoRW\<^sub>A_implies_NoRW\<^sub>C:
  "x \<in> mds\<^sub>A_of mds\<^sub>C AsmNoReadOrWrite \<Longrightarrow>
   var\<^sub>C_of x \<in> mds\<^sub>C AsmNoReadOrWrite"
  unfolding mds\<^sub>A_of_def
  apply clarsimp
  apply (simp only: var\<^sub>C_of_def)
  apply clarsimp
  apply (simp add: f_inv_into_f)
  done

lemma NoWrite\<^sub>A_implies_NoWrite\<^sub>C:
  "x \<in> mds\<^sub>A_of mds\<^sub>C AsmNoWrite \<Longrightarrow>
   var\<^sub>C_of x \<in> mds\<^sub>C AsmNoWrite"
  unfolding mds\<^sub>A_of_def
  apply clarsimp
  apply (simp only: var\<^sub>C_of_def)
  apply clarsimp
  apply (simp add: f_inv_into_f)
  done

lemma if_seq_eval\<^sub>w_helper\<^sub>A:
  "(\<langle>If B T E, mds, mem\<rangle>,
    \<langle>if ev\<^sub>B mem B then T else E, mds, mem\<rangle>\<^sub>A) \<in> A.eval\<^sub>w
    \<Longrightarrow>
   (\<langle>If B T E ;; TAIL, mds, mem\<rangle>,
    \<langle>if ev\<^sub>B mem B then T ;; TAIL else E ;; TAIL, mds, mem\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
  using A.eval\<^sub>w.seq
  by auto

lemma if_seq_eval\<^sub>w_helper\<^sub>C:
  "(\<langle>If B T E, mds, mem\<rangle>,
    \<langle>if ev\<^sub>B\<^sub>C mem B then T else E, mds, mem\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
    \<Longrightarrow>
   (\<langle>If B T E ;; TAIL, mds, mem\<rangle>,
    \<langle>if ev\<^sub>B\<^sub>C mem B then T ;; TAIL else E ;; TAIL, mds, mem\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
  using C.eval\<^sub>w.seq
  by auto

fun aexp\<^sub>C_of
where
  "aexp\<^sub>C_of (Const c) = (Const c)" |
  "aexp\<^sub>C_of (Load v) = (Load (var\<^sub>C_of v))" |
  "aexp\<^sub>C_of (Add x y) = Add (aexp\<^sub>C_of x) (aexp\<^sub>C_of y)" |
  "aexp\<^sub>C_of (Sub x y) = Sub (aexp\<^sub>C_of x) (aexp\<^sub>C_of y)"

lemma mem_assign_refinement_helper_aexp:
  "mem\<^sub>A_of (mem\<^sub>C (var\<^sub>C_of x := ev\<^sub>A mem\<^sub>C (aexp\<^sub>C_of a)))
       = (mem\<^sub>A_of mem\<^sub>C) (x := ev\<^sub>A (mem\<^sub>A_of mem\<^sub>C) a)"
  apply(clarsimp simp: mem\<^sub>A_of_def)
  apply(rule ext, clarsimp)
  apply(rename_tac x\<^sub>A)
  apply(cases x)
     apply(case_tac x\<^sub>A, induct rule:aexp\<^sub>C_of.induct, clarsimp+)
    apply(case_tac x\<^sub>A, induct rule:aexp\<^sub>C_of.induct, clarsimp+)
      apply(induct rule:aexp\<^sub>C_of.induct, clarsimp+)
   apply(case_tac x\<^sub>A, induct rule:aexp\<^sub>C_of.induct, clarsimp+)
    apply(induct rule:aexp\<^sub>C_of.induct, clarsimp+)
  apply(case_tac x\<^sub>A, induct rule:aexp\<^sub>C_of.induct, clarsimp+)
  apply(induct rule:aexp\<^sub>C_of.induct, clarsimp+)
  done

inductive_set rel_inv\<^sub>C :: "(((var\<^sub>C addr, var\<^sub>C aexp, var\<^sub>C bexp) Stmt, var\<^sub>C addr, val) LocalConf) rel"
where
  rel_inv\<^sub>C_1:
  "\<lbrakk>c =
     Skip ;;
     Skip ;;
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    c' =
     Assign reg1 (Load y_mem) ;;
     Assign reg2 (Load z_mem) ;;
     Assign reg0 (Add (Load reg1) (Load reg2)) ;;
     Assign x_mem (Load reg0)\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv\<^sub>C" |
  rel_inv\<^sub>C_1':
  "\<lbrakk>c' =
     Skip ;;
     Skip ;;
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    c =
     Assign reg1 (Load y_mem) ;;
     Assign reg2 (Load z_mem) ;;
     Assign reg0 (Add (Load reg1) (Load reg2)) ;;
     Assign x_mem (Load reg0)\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv\<^sub>C" |
  rel_inv\<^sub>C_2:
  "\<lbrakk>c =
     Stop ;;
     Skip ;;
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    c' =
     Stop ;;
     Assign reg2 (Load z_mem) ;;
     Assign reg0 (Add (Load reg1) (Load reg2)) ;;
     Assign x_mem (Load reg0)\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv\<^sub>C" |
  rel_inv\<^sub>C_2':
  "\<lbrakk>c' =
     Stop ;;
     Skip ;;
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    c =
     Stop ;;
     Assign reg2 (Load z_mem) ;;
     Assign reg0 (Add (Load reg1) (Load reg2)) ;;
     Assign x_mem (Load reg0)\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv\<^sub>C" |
  rel_inv\<^sub>C_3:
  "\<lbrakk>c =
     Skip ;;
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    c' =
     Assign reg2 (Load z_mem) ;;
     Assign reg0 (Add (Load reg1) (Load reg2)) ;;
     Assign x_mem (Load reg0)\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv\<^sub>C" |
  rel_inv\<^sub>C_3':
  "\<lbrakk>c' =
     Skip ;;
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    c =
     Assign reg2 (Load z_mem) ;;
     Assign reg0 (Add (Load reg1) (Load reg2)) ;;
     Assign x_mem (Load reg0)\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv\<^sub>C" |
  rel_inv\<^sub>C_4:
  "\<lbrakk>c =
     Stop ;;
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    c' =
     Stop ;;
     Assign reg0 (Add (Load reg1) (Load reg2)) ;;
     Assign x_mem (Load reg0)\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv\<^sub>C" |
  rel_inv\<^sub>C_4':
  "\<lbrakk>c' =
     Stop ;;
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    c =
     Stop ;;
     Assign reg0 (Add (Load reg1) (Load reg2)) ;;
     Assign x_mem (Load reg0)\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv\<^sub>C" |
  rel_inv\<^sub>C_5:
  "\<lbrakk>c =
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    c' =
     Assign reg0 (Add (Load reg1) (Load reg2)) ;;
     Assign x_mem (Load reg0)\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv\<^sub>C" |
  rel_inv\<^sub>C_5':
  "\<lbrakk>c' =
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    c =
     Assign reg0 (Add (Load reg1) (Load reg2)) ;;
     Assign x_mem (Load reg0)\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv\<^sub>C" |
  rel_inv\<^sub>C_default:
  "\<lbrakk>c = c'\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv\<^sub>C"

inductive_cases rel_inv\<^sub>CE: "(\<langle>c, mds, mem\<rangle>\<^sub>C, \<langle>c', mds', mem'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"

lemma rel_inv\<^sub>C_sym:
  "sym rel_inv\<^sub>C"
  unfolding sym_def
  apply(auto elim!: rel_inv\<^sub>C.cases intro: rel_inv\<^sub>C.intros)
  done

lemma rel_inv\<^sub>C_closed_glob_consistent:
  "C.closed_glob_consistent rel_inv\<^sub>C"
  unfolding C.closed_glob_consistent_def
  apply(safe elim!: rel_inv\<^sub>C.cases)
  using rel_inv\<^sub>C.intros by simp+

inductive_set RefRel_HighBranch :: "(
    (((var, var aexp, var bexp) Stmt \<times> (Mode \<Rightarrow> var set)) \<times> (var \<Rightarrow> val)) \<times>
     ((var\<^sub>C, var\<^sub>C aexp, var\<^sub>C bexp) Stmt \<times> (Mode \<Rightarrow> var\<^sub>C set)) \<times> (var\<^sub>C \<Rightarrow> val)
    ) set"
where
  acq_mode_rel: "\<lbrakk>c\<^sub>A = ModeDecl Skip (Acq x SomeMode) ;; c\<^sub>A_tail;
    c\<^sub>C = ModeDecl Skip (Acq (var\<^sub>C_of x) SomeMode) ;; c\<^sub>C_tail;
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A''\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>A_tail, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>Stop ;; c\<^sub>A_tail, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  assign_load_rel: "\<lbrakk>c\<^sub>A = (x \<leftarrow> aexp.Load y) ;; c\<^sub>A_tail;
    c\<^sub>C = ((var\<^sub>C_of x) \<leftarrow> aexp.Load (var\<^sub>C_of y)) ;; c\<^sub>C_tail;
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    x \<notin> mds\<^sub>A GuarNoReadOrWrite;
    x \<notin> mds\<^sub>A GuarNoWrite;
    y \<notin> mds\<^sub>A GuarNoReadOrWrite;
    x \<notin> \<C>;
    y \<notin> \<C>;
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A''\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>A_tail, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>Stop ;; c\<^sub>A_tail, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  assign_const_rel: "\<lbrakk>c\<^sub>A = (x \<leftarrow> Const z) ;; c\<^sub>A_tail;
    c\<^sub>C = ((var\<^sub>C_of x) \<leftarrow> Const z) ;; c\<^sub>C_tail;
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    x \<notin> mds\<^sub>A GuarNoReadOrWrite;
    x \<notin> mds\<^sub>A GuarNoWrite;
    x \<notin> \<C>;
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A''\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>A_tail, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>Stop ;; c\<^sub>A_tail, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_reg_load_rel: "\<lbrakk>
    c\<^sub>A = (If (Neq (Load x) (Const 0)) c\<^sub>A_then c\<^sub>A_else);
    c\<^sub>C = (reg3 \<leftarrow> (Load (var\<^sub>C_of x))) ;; ((If (Neq (Load reg3) (Const 0)) c\<^sub>C_then c\<^sub>C_else));
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    x \<in> mds\<^sub>A AsmNoWrite \<and> x \<notin> mds\<^sub>A AsmNoReadOrWrite;
    reg3 \<notin> mds\<^sub>C GuarNoReadOrWrite \<and> reg3 \<notin> mds\<^sub>C GuarNoWrite;
    x \<notin> mds\<^sub>A GuarNoReadOrWrite;
    \<forall>x'. x \<in> \<C>_vars x' \<longrightarrow> x' \<notin> mds\<^sub>A GuarNoReadOrWrite;
    (\<forall>mem\<^sub>A' mem\<^sub>C' mem\<^sub>A'' mem\<^sub>C''.
        (
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         \<comment> \<open>The change in \<open>mem\<^sub>C\<close> does not affect \<open>mem\<^sub>A\<close>\<close>
         mem\<^sub>A'' = mem\<^sub>A' \<and>
         \<comment> \<open>The concrete and abstract versions of the bool condition must become consistent\<close>
         ev\<^sub>B mem\<^sub>C' (Neq (Load reg3) (Const 0)) = ev\<^sub>B mem\<^sub>A' (Neq (Load x) (Const 0)) \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
          \<langle>Stop ;; (If (Neq (Load reg3) (Const 0)) c\<^sub>C_then c\<^sub>C_else), mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A''\<rangle>\<^sub>A,
          \<langle>Stop ;; (If (Neq (Load reg3) (Const 0)) c\<^sub>C_then c\<^sub>C_else), mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch)
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_reg_stop_rel: "\<lbrakk>
    c\<^sub>A = (If (Neq (Load x) (Const 0)) c\<^sub>A_then c\<^sub>A_else);
    c\<^sub>C = Stop ;; ((If (Neq (Load reg3) (Const 0)) c\<^sub>C_then c\<^sub>C_else));
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    x \<in> mds\<^sub>A AsmNoWrite \<and> x \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<comment> \<open>We will need to carry this through to the \<open>if_reg_rel\<close> case.\<close>
    ev\<^sub>B mem\<^sub>C (Neq (Load reg3) (Const 0)) = ev\<^sub>B mem\<^sub>A (Neq (Load x) (Const 0));
    (\<forall>mem\<^sub>A' mem\<^sub>C' mem\<^sub>A'' mem\<^sub>C''.
        (
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         \<comment> \<open>The change in \<open>mem\<^sub>C\<close> does not affect \<open>mem\<^sub>A\<close>\<close>
         mem\<^sub>A'' = mem\<^sub>A' \<and>
         \<comment> \<open>The concrete and abstract versions of the bool condition must remain consistent\<close>
         ev\<^sub>B mem\<^sub>C' (Neq (Load reg3) (Const 0)) = ev\<^sub>B mem\<^sub>A' (Neq (Load x) (Const 0)) \<and>
         ev\<^sub>B mem\<^sub>C'' (Neq (Load reg3) (Const 0)) = ev\<^sub>B mem\<^sub>A'' (Neq (Load x) (Const 0)) \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
          \<langle>(If (Neq (Load reg3) (Const 0)) c\<^sub>C_then c\<^sub>C_else), mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A''\<rangle>\<^sub>A,
          \<langle>(If (Neq (Load reg3) (Const 0)) c\<^sub>C_then c\<^sub>C_else), mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch)
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_reg_rel: "\<lbrakk>
    \<comment> \<open>Is a more generic version possible for an arbitrary \<open>b\<^sub>A\<close>?\<close>
    \<^cancel>\<open>c\<^sub>A = (If b\<^sub>A c\<^sub>A_then c\<^sub>A_else);\<close>
    \<^cancel>\<open>b\<^sub>A = Eq (Load x) (Const 0);\<close>  \<comment> \<open>\<open>ev\<^sub>B mem\<^sub>A b\<^sub>A\<close>\<close>
    c\<^sub>A = (If (Neq (Load x) (Const 0)) c\<^sub>A_then c\<^sub>A_else);
    c\<^sub>C = (If (Neq (Load reg3) (Const 0)) c\<^sub>C_then c\<^sub>C_else);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    x \<in> mds\<^sub>A AsmNoWrite \<and> x \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<comment> \<open>The concrete and abstract versions of the bool condition must have remained consistent\<close>
    ev\<^sub>B mem\<^sub>C (Neq (Load reg3) (Const 0)) = ev\<^sub>B mem\<^sub>A (Neq (Load x) (Const 0));
    \<comment> \<open>As for \<comment> \<open>if_reg_load_rel\<close>\<close>
    reg3 \<notin> mds\<^sub>C GuarNoReadOrWrite \<and> reg3 \<notin> mds\<^sub>C GuarNoWrite;
    x \<notin> mds\<^sub>A GuarNoReadOrWrite;
    \<forall>x'. x \<in> \<C>_vars x' \<longrightarrow> x' \<notin> mds\<^sub>A GuarNoReadOrWrite;
    \<comment> \<open>As we would expect, the two branches must be related by the coupling invariant.\<close>
    \<forall>mem\<^sub>C' mem\<^sub>C''. (\<langle>c\<^sub>C_then, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>C_else, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C;
    (\<forall>mem\<^sub>A' mem\<^sub>C' mem\<^sub>A'' mem\<^sub>C''.
       mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
       mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
       ev\<^sub>B mem\<^sub>C'' (Neq (Load reg3) (Const 0)) = ev\<^sub>B mem\<^sub>A'' (Neq (Load x) (Const 0)) \<and>
       ev\<^sub>B mem\<^sub>C' (Neq (Load reg3) (Const 0)) = ev\<^sub>B mem\<^sub>A' (Neq (Load x) (Const 0)) \<and>
       (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A''\<rangle>\<^sub>A,
        \<langle>(if (ev\<^sub>B mem\<^sub>A'' (Neq (Load x) (Const 0))) then c\<^sub>A_then else c\<^sub>A_else), mds\<^sub>A, mem\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w \<and>
       (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
        \<langle>(if (ev\<^sub>B mem\<^sub>C'' (Neq (Load reg3) (Const 0))) then c\<^sub>C_then else c\<^sub>C_else), mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
       \<longrightarrow>
       (\<langle>(if (ev\<^sub>B mem\<^sub>A'' (Neq (Load x) (Const 0))) then c\<^sub>A_then else c\<^sub>A_else), mds\<^sub>A, mem\<^sub>A'\<rangle>\<^sub>A,
        \<langle>(if (ev\<^sub>B mem\<^sub>C'' (Neq (Load reg3) (Const 0))) then c\<^sub>C_then else c\<^sub>C_else), mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch)
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

(*
  Assign x_var (Load y_var)
    - to -
  Skip ;;
  Skip ;;
  Assign reg0 (Load y_mem) ;;
  Assign x_mem (Load reg0);
*)
  if_then_rel_1: "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Load y_var);
    c\<^sub>C = Skip ;; c\<^sub>C_tail;
    c\<^sub>C_tail =
     Skip ;;
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_then_rel_1': "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Load y_var);
    c\<^sub>C = Stop ;; c\<^sub>C_tail;
    c\<^sub>C_tail =
     Skip ;;
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_then_rel_2: "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Load y_var);
    c\<^sub>C = Skip ;; c\<^sub>C_tail;
    c\<^sub>C_tail =
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_then_rel_2': "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Load y_var);
    c\<^sub>C = Stop ;; c\<^sub>C_tail;
    c\<^sub>C_tail =
     Assign reg0 (Load y_mem) ;;
     Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_then_rel_3: "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Load y_var);
    c\<^sub>C = Assign reg0 (Load y_mem) ;; c\<^sub>C_tail;
    c\<^sub>C_tail = Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    y_var \<in> mds\<^sub>A AsmNoWrite \<and> y_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         \<comment> \<open>The value of \<open>reg0\<close> and \<open>y_var\<close> must now become consistent\<close>
         ev\<^sub>A mem\<^sub>C' (Load reg0) = ev\<^sub>A mem\<^sub>A' (Load y_var) \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_then_rel_3': "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Load y_var);
    c\<^sub>C = Stop ;; c\<^sub>C_tail;
    c\<^sub>C_tail = Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    y_var \<in> mds\<^sub>A AsmNoWrite \<and> y_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<comment> \<open>The value of \<open>reg0\<close> and \<open>y_var\<close> at this point must be consistent\<close>
    ev\<^sub>A mem\<^sub>C (Load reg0) = ev\<^sub>A mem\<^sub>A (Load y_var);
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         \<comment> \<open>and must remain consistent\<close>
         ev\<^sub>A mem\<^sub>C' (Load reg0) = ev\<^sub>A mem\<^sub>A' (Load y_var) \<and>
         ev\<^sub>A mem\<^sub>C'' (Load reg0) = ev\<^sub>A mem\<^sub>A'' (Load y_var) \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_then_rel_4: "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Load y_var);
    c\<^sub>C = Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    y_var \<in> mds\<^sub>A AsmNoWrite \<and> y_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<comment> \<open>The value of \<open>reg0\<close> and \<open>y_var\<close> at this point must be consistent\<close>
    ev\<^sub>A mem\<^sub>C (Load reg0) = ev\<^sub>A mem\<^sub>A (Load y_var);
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A''\<rangle>\<^sub>A, \<langle>Stop, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>Stop, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>Stop, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

(*
  Assign x_var (Add (Load y_var) (Load z_var))
    - to -
  Assign reg1 (Load y_mem) ;;
  Assign reg2 (Load z_mem) ;;
  Assign reg0 (Add (Load reg1) (Load reg2)) ;;
  Assign x_mem (Load reg0)
*)
  if_else_rel_1: "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Add (Load y_var) (Load z_var));
    c\<^sub>C = (reg1 \<leftarrow> Load y_mem) ;; c\<^sub>C_tail;
    c\<^sub>C_tail =
      Assign reg2 (Load z_mem) ;;
      Assign reg0 (Add (Load reg1) (Load reg2)) ;;
      Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    y_var \<in> mds\<^sub>A AsmNoWrite \<and> y_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         \<comment> \<open>Now \<open>reg1\<close> takes on \<open>y_var\<close>\<close>
         ev\<^sub>A mem\<^sub>C' (Load reg1) = ev\<^sub>A mem\<^sub>A' (Load y_var) \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_else_rel_1': "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Add (Load y_var) (Load z_var));
    c\<^sub>C = Stop ;; c\<^sub>C_tail;
    c\<^sub>C_tail =
      Assign reg2 (Load z_mem) ;;
      Assign reg0 (Add (Load reg1) (Load reg2)) ;;
      Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    y_var \<in> mds\<^sub>A AsmNoWrite \<and> y_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<comment> \<open>At this point \<open>reg1\<close> contains \<open>y_var\<close>\<close>
    ev\<^sub>A mem\<^sub>C (Load reg1) = ev\<^sub>A mem\<^sub>A (Load y_var);
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         \<comment> \<open>maintain it\<close>
         ev\<^sub>A mem\<^sub>C' (Load reg1) = ev\<^sub>A mem\<^sub>A' (Load y_var) \<and>
         ev\<^sub>A mem\<^sub>C'' (Load reg1) = ev\<^sub>A mem\<^sub>A'' (Load y_var) \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_else_rel_2: "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Add (Load y_var) (Load z_var));
    c\<^sub>C = Assign reg2 (Load z_mem) ;; c\<^sub>C_tail;
    c\<^sub>C_tail =
      Assign reg0 (Add (Load reg1) (Load reg2)) ;;
      Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    y_var \<in> mds\<^sub>A AsmNoWrite \<and> y_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<comment> \<open>At this point \<open>reg1\<close> contains \<open>y_var\<close>\<close>
    ev\<^sub>A mem\<^sub>C (Load reg1) = ev\<^sub>A mem\<^sub>A (Load y_var);
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         \<comment> \<open>maintain it\<close>
         ev\<^sub>A mem\<^sub>C'' (Load reg1) = ev\<^sub>A mem\<^sub>A'' (Load y_var) \<and>
         ev\<^sub>A mem\<^sub>C' (Load reg1) = ev\<^sub>A mem\<^sub>A' (Load y_var) \<and>
         \<comment> \<open>Now \<open>reg2\<close> takes on \<open>z_var\<close>\<close>
         ev\<^sub>A mem\<^sub>C' (Load reg2) = ev\<^sub>A mem\<^sub>A' (Load z_var) \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_else_rel_2': "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Add (Load y_var) (Load z_var));
    c\<^sub>C = Stop ;; c\<^sub>C_tail;
    c\<^sub>C_tail =
      Assign reg0 (Add (Load reg1) (Load reg2)) ;;
      Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    y_var \<in> mds\<^sub>A AsmNoWrite \<and> y_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    z_var \<in> mds\<^sub>A AsmNoWrite \<and> z_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<comment> \<open>At this point \<open>reg1\<close> contains \<open>y_var\<close> and \<open>reg2\<close> contains z_var\<close>
    ev\<^sub>A mem\<^sub>C (Load reg1) = ev\<^sub>A mem\<^sub>A (Load y_var);
    ev\<^sub>A mem\<^sub>C (Load reg2) = ev\<^sub>A mem\<^sub>A (Load z_var);
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         \<comment> \<open>maintain it\<close>
         ev\<^sub>A mem\<^sub>C'' (Load reg1) = ev\<^sub>A mem\<^sub>A'' (Load y_var) \<and>
         ev\<^sub>A mem\<^sub>C'' (Load reg2) = ev\<^sub>A mem\<^sub>A'' (Load z_var) \<and>
         ev\<^sub>A mem\<^sub>C' (Load reg1) = ev\<^sub>A mem\<^sub>A' (Load y_var) \<and>
         ev\<^sub>A mem\<^sub>C' (Load reg2) = ev\<^sub>A mem\<^sub>A' (Load z_var) \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_else_rel_3: "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Add (Load y_var) (Load z_var));
    c\<^sub>C = Assign reg0 (Add (Load reg1) (Load reg2)) ;; c\<^sub>C_tail;
    c\<^sub>C_tail = Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    y_var \<in> mds\<^sub>A AsmNoWrite \<and> y_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    z_var \<in> mds\<^sub>A AsmNoWrite \<and> z_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<comment> \<open>At this point \<open>reg1\<close> contains \<open>y_var\<close> and \<open>reg2\<close> contains \<open>z_var\<close>\<close>
    ev\<^sub>A mem\<^sub>C (Load reg1) = ev\<^sub>A mem\<^sub>A (Load y_var);
    ev\<^sub>A mem\<^sub>C (Load reg2) = ev\<^sub>A mem\<^sub>A (Load z_var);
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         ev\<^sub>A mem\<^sub>C'' (Load reg1) = ev\<^sub>A mem\<^sub>A'' (Load y_var) \<and>
         ev\<^sub>A mem\<^sub>C'' (Load reg2) = ev\<^sub>A mem\<^sub>A'' (Load z_var) \<and>
         \<comment> \<open>Thus the value of \<open>reg0\<close> becomes consistent with \<open>y_var + z_var\<close>\<close>
         ev\<^sub>A mem\<^sub>C' (Load reg0) = ev\<^sub>A mem\<^sub>A' (Add (Load y_var) (Load z_var)) \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_else_rel_3': "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Add (Load y_var) (Load z_var));
    c\<^sub>C = Stop ;; c\<^sub>C_tail;
    c\<^sub>C_tail = Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    y_var \<in> mds\<^sub>A AsmNoWrite \<and> y_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    z_var \<in> mds\<^sub>A AsmNoWrite \<and> z_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<comment> \<open>The value of \<open>reg0\<close> and \<open>y_var + z_var\<close> at this point must be consistent\<close>
    ev\<^sub>A mem\<^sub>C (Load reg0) = ev\<^sub>A mem\<^sub>A (Add (Load y_var) (Load z_var));
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         \<comment> \<open>and must remain consistent\<close>
         ev\<^sub>A mem\<^sub>C' (Load reg0) = ev\<^sub>A mem\<^sub>A' (Add (Load y_var) (Load z_var)) \<and>
         ev\<^sub>A mem\<^sub>C'' (Load reg0) = ev\<^sub>A mem\<^sub>A'' (Add (Load y_var) (Load z_var)) \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  if_else_rel_4: "\<lbrakk>c\<^sub>A = (x_var \<leftarrow> Add (Load y_var) (Load z_var));
    c\<^sub>C = Assign x_mem (Load reg0);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    y_var \<in> mds\<^sub>A AsmNoWrite \<and> y_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    z_var \<in> mds\<^sub>A AsmNoWrite \<and> z_var \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<comment> \<open>The value of \<open>reg0\<close> and \<open>y_var + z_var\<close> at this point must be consistent\<close>
    ev\<^sub>A mem\<^sub>C (Load reg0) = ev\<^sub>A mem\<^sub>A (Add (Load y_var) (Load z_var));
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A''\<rangle>\<^sub>A, \<langle>Stop, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>Stop, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>Stop, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  stop_seq_rel: "\<lbrakk>c\<^sub>A = Stop ;; c\<^sub>A_tail;
    c\<^sub>C = Stop ;; c\<^sub>C_tail;
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<langle>c\<^sub>A_tail, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch\<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" |

  stop_rel:
    "(\<langle>Stop, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A, \<langle>Stop, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"

inductive_cases RefRelE: "(\<langle>c, mds, mem\<rangle>\<^sub>A, \<langle>c', mds', mem'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"

definition abs_steps' :: "(_,_,_) Stmt \<Rightarrow> (_,_,_) Stmt \<Rightarrow> nat" where
  "abs_steps' c\<^sub>A c\<^sub>C \<equiv>
    (if (\<exists>x m c\<^sub>A_tail. c\<^sub>A = ((Skip@[x +=\<^sub>m m]) ;; c\<^sub>A_tail)) \<and>
        (\<exists>x m c\<^sub>C_tail. c\<^sub>C = ((Skip@[var\<^sub>C_of x +=\<^sub>m m]) ;; c\<^sub>C_tail)) then (Suc 0)
     else if (\<exists> c\<^sub>A_tail c\<^sub>C_tail. c\<^sub>A = (Stop ;; c\<^sub>A_tail) \<and> c\<^sub>C = (Stop ;; c\<^sub>C_tail)) then (Suc 0)
     else if (\<exists> x then\<^sub>A else\<^sub>A then\<^sub>C else\<^sub>C.
        c\<^sub>A = (Stmt.If (Neq (Load x) (Const 0)) then\<^sub>A else\<^sub>A) \<and>
        (c\<^sub>C = ((reg3 \<leftarrow> Load (var\<^sub>C_of x)) ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C)) \<or>
         c\<^sub>C = (Stop ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C))
        then 0
     else if (c\<^sub>A = (x_var \<leftarrow> Load y_var) \<and>
        c\<^sub>C \<in> {Skip ;; Skip ;; Assign reg0 (Load y_mem) ;; Assign x_mem (Load reg0),
              Stop ;; Skip ;; Assign reg0 (Load y_mem) ;; Assign x_mem (Load reg0),
              Skip ;; Assign reg0 (Load y_mem) ;; Assign x_mem (Load reg0),
              Stop ;; Assign reg0 (Load y_mem) ;; Assign x_mem (Load reg0),
              Assign reg0 (Load y_mem) ;; Assign x_mem (Load reg0),
              Stop ;; Assign x_mem (Load reg0)})
        then 0
     else if (c\<^sub>A = (x_var \<leftarrow> Add (Load y_var) (Load z_var)) \<and>
        c\<^sub>C \<in> {(reg1 \<leftarrow> Load y_mem) ;; Assign reg2 (Load z_mem) ;;
                Assign reg0 (Add (Load reg1) (Load reg2)) ;; Assign x_mem (Load reg0),
              Stop ;; Assign reg2 (Load z_mem) ;;
                Assign reg0 (Add (Load reg1) (Load reg2)) ;; Assign x_mem (Load reg0),
              Assign reg2 (Load z_mem) ;;
                Assign reg0 (Add (Load reg1) (Load reg2)) ;; Assign x_mem (Load reg0),
              Stop ;;
                Assign reg0 (Add (Load reg1) (Load reg2)) ;; Assign x_mem (Load reg0),
              Assign reg0 (Add (Load reg1) (Load reg2)) ;; Assign x_mem (Load reg0),
              Stop ;; Assign x_mem (Load reg0)})
        then 0
     else (Suc 0))"

fun abs_steps
where
"abs_steps \<langle>c\<^sub>A, _, _\<rangle>\<^sub>A \<langle>c\<^sub>C, _, _\<rangle>\<^sub>C = abs_steps' c\<^sub>A c\<^sub>C"

lemma closed_others_RefRel_HighBranch:
  "closed_others RefRel_HighBranch"
unfolding closed_others_def
proof(clarify)
fix c\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>C mem\<^sub>C'
assume
  in_rel: "(\<langle>c\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A,
    \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
  vars: " \<forall>x. mem\<^sub>C x \<noteq> mem\<^sub>C' x \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x"
and  dmas: "\<forall>x. dma\<^sub>C mem\<^sub>C x \<noteq> dma\<^sub>C mem\<^sub>C' x \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x"
from in_rel vars dmas
show "(\<langle>c\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
  proof (induct rule: RefRel_HighBranch.induct)
  case (acq_mode_rel c\<^sub>A x SomeMode tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using acq_mode_rel
    by (simp add:RefRel_HighBranch.acq_mode_rel)
  next
  case (assign_load_rel c\<^sub>A x y tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using assign_load_rel
    by (simp add:RefRel_HighBranch.assign_load_rel)
  next
  case (assign_const_rel c\<^sub>A x z tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using assign_const_rel
    by (simp add:RefRel_HighBranch.assign_const_rel)
  next
  case (if_reg_load_rel c\<^sub>A x then\<^sub>A else\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_reg_load_rel
    by (simp add:RefRel_HighBranch.if_reg_load_rel)
  next
  case (if_reg_stop_rel c\<^sub>A x then\<^sub>A else\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_reg_stop_rel
    proof (clarsimp)
      from if_reg_stop_rel.hyps(3,5,6) if_reg_stop_rel.prems(1)
      have reg_untouched: "mem\<^sub>C reg3 = mem\<^sub>C' reg3" and
        x\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of x) = mem\<^sub>C' (var\<^sub>C_of x)" and
        x\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C x = mem\<^sub>A_of mem\<^sub>C' x"
        using reg_is_not_the_var\<^sub>C_of_anything mem\<^sub>A_of_def NoWrite\<^sub>A_implies_NoWrite\<^sub>C
        by (clarsimp simp:var_asm_not_written_def, blast)+
      with if_reg_stop_rel.hyps
      have conds_still_match: "(mem\<^sub>C' reg3 = 0) = (mem\<^sub>A_of mem\<^sub>C' x = 0)"
        by fastforce
      with if_reg_stop_rel RefRel_HighBranch.if_reg_stop_rel
      show "(\<langle>Stmt.If (Neq (Load x) (Const 0)) then\<^sub>A else\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A,
             \<langle>Stop ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C)
             \<in> RefRel_HighBranch"
        by auto
    qed
  next
  case (if_reg_rel c\<^sub>A x then\<^sub>A else\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_reg_rel(1-11)
    proof (clarsimp)
      from if_reg_rel.hyps(3,5,6) if_reg_rel.prems(1)
      have reg_untouched: "mem\<^sub>C reg3 = mem\<^sub>C' reg3" and
        x\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of x) = mem\<^sub>C' (var\<^sub>C_of x)" and
        x\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C x = mem\<^sub>A_of mem\<^sub>C' x"
        using reg_is_not_the_var\<^sub>C_of_anything mem\<^sub>A_of_def NoWrite\<^sub>A_implies_NoWrite\<^sub>C
        by (clarsimp simp:var_asm_not_written_def, blast)+
      with if_reg_rel.hyps
      have conds_still_match: "(mem\<^sub>C' reg3 = 0) = (mem\<^sub>A_of mem\<^sub>C' x = 0)"
        by auto
      show "(\<langle>Stmt.If (Neq (Load x) (Const 0)) then\<^sub>A else\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A,
             \<langle>Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C)
             \<in> RefRel_HighBranch"
        apply (rule RefRel_HighBranch.if_reg_rel, simp+)
            using if_reg_rel apply simp
           using if_reg_rel apply simp
          using conds_still_match apply simp
         using if_reg_rel apply blast+
        done
    qed
  next
  case (if_then_rel_1 c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_then_rel_1
    by (simp add:RefRel_HighBranch.if_then_rel_1)
  next
  case (if_then_rel_1' c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_then_rel_1'
    by (simp add:RefRel_HighBranch.if_then_rel_1')
  next
  case (if_then_rel_2 c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_then_rel_2
    by (simp add:RefRel_HighBranch.if_then_rel_2)
  next
  case (if_then_rel_2' c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_then_rel_2'
    by (simp add:RefRel_HighBranch.if_then_rel_2')
  next
  case (if_then_rel_3 c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_then_rel_3
    by (simp add:RefRel_HighBranch.if_then_rel_3)
  next
  case (if_then_rel_3' c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_then_rel_3'
    proof (clarsimp)
      from if_then_rel_3'.hyps(4,5,6,7) if_then_rel_3'.prems(1)
      have reg_untouched: "mem\<^sub>C reg0 = mem\<^sub>C' reg0" and
        y\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of y_var) = mem\<^sub>C' (var\<^sub>C_of y_var)" and
        y\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C y_var = mem\<^sub>A_of mem\<^sub>C' y_var"
        using reg_is_not_the_var\<^sub>C_of_anything mem\<^sub>A_of_def NoWrite\<^sub>A_implies_NoWrite\<^sub>C var_asm_not_written_def
        by fastforce+
      with if_then_rel_3'.hyps
      have conds_still_match: "mem\<^sub>C' reg0 = mem\<^sub>A_of mem\<^sub>C' y_var"
        by simp
      show "(\<langle>x_var \<leftarrow> Load y_var, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A,
             \<langle>Stop ;; (x_mem \<leftarrow> Load reg0), mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C)
             \<in> RefRel_HighBranch"
        using RefRel_HighBranch.if_then_rel_3' if_then_rel_3' conds_still_match by simp
    qed
  next
  case (if_then_rel_4 c\<^sub>A c\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_then_rel_4
    proof (clarsimp)
      from if_then_rel_4.hyps(3-7) if_then_rel_4.prems(1)
      have reg_untouched: "mem\<^sub>C reg0 = mem\<^sub>C' reg0" and
        y\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of y_var) = mem\<^sub>C' (var\<^sub>C_of y_var)" and
        y\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C y_var = mem\<^sub>A_of mem\<^sub>C' y_var"
        using reg_is_not_the_var\<^sub>C_of_anything mem\<^sub>A_of_def NoWrite\<^sub>A_implies_NoWrite\<^sub>C var_asm_not_written_def
        by (fast, metis+)
      with if_then_rel_4.hyps
      have conds_still_match: "mem\<^sub>C' reg0 = mem\<^sub>A_of mem\<^sub>C' y_var"
        by simp
      show "(\<langle>x_var \<leftarrow> Load y_var, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A,
             \<langle>x_mem \<leftarrow> Load reg0, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C)
             \<in> RefRel_HighBranch"
        using RefRel_HighBranch.if_then_rel_4 if_then_rel_4 conds_still_match by simp
    qed
  next
  case (if_else_rel_1 c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_else_rel_1
    by (simp add:RefRel_HighBranch.if_else_rel_1)
  next
  case (if_else_rel_1' c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_else_rel_1'
    proof (clarsimp)
      from if_else_rel_1'.hyps(4-7) if_else_rel_1'.prems(1)
      have reg_untouched: "mem\<^sub>C reg1 = mem\<^sub>C' reg1" and
        y\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of y_var) = mem\<^sub>C' (var\<^sub>C_of y_var)" and
        y\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C y_var = mem\<^sub>A_of mem\<^sub>C' y_var"
        using reg_is_not_the_var\<^sub>C_of_anything mem\<^sub>A_of_def NoWrite\<^sub>A_implies_NoWrite\<^sub>C var_asm_not_written_def
        by (metis (no_types) insertCI reg_not_visible_abs, metis+)
      with if_else_rel_1'.hyps
      have conds_still_match: "mem\<^sub>C' reg1 = mem\<^sub>A_of mem\<^sub>C' y_var"
        by simp
      show "(\<langle>x_var \<leftarrow> Add (Load y_var) (Load z_var), mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A,
             \<langle>Stop ;; (reg2 \<leftarrow> Load z_mem) ;; (reg0 \<leftarrow> Add (Load reg1) (Load reg2)) ;; (x_mem \<leftarrow> Load reg0), mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C)
             \<in> RefRel_HighBranch"
        using RefRel_HighBranch.if_else_rel_1' if_else_rel_1' conds_still_match by simp
    qed
  next
  case (if_else_rel_2 c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_else_rel_2
    proof (clarsimp)
      from if_else_rel_2.hyps(4-7) if_else_rel_2.prems(1)
      have reg_untouched: "mem\<^sub>C reg1 = mem\<^sub>C' reg1" and
        y\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of y_var) = mem\<^sub>C' (var\<^sub>C_of y_var)" and
        y\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C y_var = mem\<^sub>A_of mem\<^sub>C' y_var"
        using reg_is_not_the_var\<^sub>C_of_anything mem\<^sub>A_of_def NoWrite\<^sub>A_implies_NoWrite\<^sub>C var_asm_not_written_def
        by (metis (no_types) insertCI reg_not_visible_abs, metis+)
      with if_else_rel_2.hyps
      have conds_still_match: "mem\<^sub>C' reg1 = mem\<^sub>A_of mem\<^sub>C' y_var"
        by simp
      show "(\<langle>x_var \<leftarrow> Add (Load y_var) (Load z_var), mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A,
             \<langle>(reg2 \<leftarrow> Load z_mem) ;; (reg0 \<leftarrow> Add (Load reg1) (Load reg2)) ;; (x_mem \<leftarrow> Load reg0), mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C)
             \<in> RefRel_HighBranch"
        using RefRel_HighBranch.if_else_rel_2 if_else_rel_2 conds_still_match by simp
    qed
  next
  case (if_else_rel_2' c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_else_rel_2'
    proof (clarsimp)
      from if_else_rel_2'.hyps(4-8) if_else_rel_2'.prems(1)
      have regs_untouched: "mem\<^sub>C reg1 = mem\<^sub>C' reg1 \<and> mem\<^sub>C reg2 = mem\<^sub>C' reg2" and
        y\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of y_var) = mem\<^sub>C' (var\<^sub>C_of y_var)" and
        y\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C y_var = mem\<^sub>A_of mem\<^sub>C' y_var" and
        z\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of z_var) = mem\<^sub>C' (var\<^sub>C_of z_var)" and
        z\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C z_var = mem\<^sub>A_of mem\<^sub>C' z_var"
        using reg_is_not_the_var\<^sub>C_of_anything mem\<^sub>A_of_def NoWrite\<^sub>A_implies_NoWrite\<^sub>C var_asm_not_written_def
        by (metis (no_types) insertCI reg_not_visible_abs, metis+)
      with if_else_rel_2'.hyps(5,9,10)
      have conds_still_match: "mem\<^sub>C' reg1 = mem\<^sub>A_of mem\<^sub>C' y_var \<and> mem\<^sub>C' reg2 = mem\<^sub>A_of mem\<^sub>C' z_var"
        by simp
      show "(\<langle>x_var \<leftarrow> Add (Load y_var) (Load z_var), mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A,
             \<langle>Stop ;; (reg0 \<leftarrow> Add (Load reg1) (Load reg2)) ;; (x_mem \<leftarrow> Load reg0), mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C)
             \<in> RefRel_HighBranch"
        using RefRel_HighBranch.if_else_rel_2' if_else_rel_2' conds_still_match by simp
    qed
  next
  case (if_else_rel_3 c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_else_rel_3
    proof (clarsimp)
      from if_else_rel_3.hyps(4-8) if_else_rel_3.prems(1)
      have regs_untouched: "mem\<^sub>C reg1 = mem\<^sub>C' reg1 \<and> mem\<^sub>C reg2 = mem\<^sub>C' reg2" and
        y\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of y_var) = mem\<^sub>C' (var\<^sub>C_of y_var)" and
        y\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C y_var = mem\<^sub>A_of mem\<^sub>C' y_var" and
        z\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of z_var) = mem\<^sub>C' (var\<^sub>C_of z_var)" and
        z\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C z_var = mem\<^sub>A_of mem\<^sub>C' z_var"
        using reg_is_not_the_var\<^sub>C_of_anything mem\<^sub>A_of_def NoWrite\<^sub>A_implies_NoWrite\<^sub>C var_asm_not_written_def
        by (metis (no_types) insertCI reg_not_visible_abs, metis+)
      with if_else_rel_3.hyps(5,9,10)
      have conds_still_match: "mem\<^sub>C' reg1 = mem\<^sub>A_of mem\<^sub>C' y_var \<and> mem\<^sub>C' reg2 = mem\<^sub>A_of mem\<^sub>C' z_var"
        by simp
      show "(\<langle>x_var \<leftarrow> Add (Load y_var) (Load z_var), mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A,
             \<langle>(reg0 \<leftarrow> Add (Load reg1) (Load reg2)) ;; (x_mem \<leftarrow> Load reg0), mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C)
             \<in> RefRel_HighBranch"
        using RefRel_HighBranch.if_else_rel_3 if_else_rel_3 conds_still_match by simp
    qed
  next
  case (if_else_rel_3' c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_else_rel_3'
    proof (clarsimp)
      from if_else_rel_3'.hyps(4-8) if_else_rel_3'.prems(1)
      have reg_untouched: "mem\<^sub>C reg0 = mem\<^sub>C' reg0" and
        y\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of y_var) = mem\<^sub>C' (var\<^sub>C_of y_var)" and
        y\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C y_var = mem\<^sub>A_of mem\<^sub>C' y_var" and
        z\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of z_var) = mem\<^sub>C' (var\<^sub>C_of z_var)" and
        z\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C z_var = mem\<^sub>A_of mem\<^sub>C' z_var"
        using reg_is_not_the_var\<^sub>C_of_anything mem\<^sub>A_of_def NoWrite\<^sub>A_implies_NoWrite\<^sub>C var_asm_not_written_def
        by (metis (no_types) insertCI reg_not_visible_abs, metis+)
      with if_else_rel_3'.hyps(5,9)
      have conds_still_match:
        "ev\<^sub>A mem\<^sub>C' (Load reg0) = ev\<^sub>A (mem\<^sub>A_of mem\<^sub>C') (Add (Load y_var) (Load z_var))"
        by simp
      show "(\<langle>x_var \<leftarrow> Add (Load y_var) (Load z_var), mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A,
             \<langle>Stop ;; (x_mem \<leftarrow> Load reg0), mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C)
             \<in> RefRel_HighBranch"
        using RefRel_HighBranch.if_else_rel_3' if_else_rel_3' conds_still_match by simp
    qed
  next
  case (if_else_rel_4 c\<^sub>A c\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using if_else_rel_4
    proof (clarsimp)
      from if_else_rel_4.hyps(3-7) if_else_rel_4.prems(1)
      have reg_untouched: "mem\<^sub>C reg0 = mem\<^sub>C' reg0" and
        y\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of y_var) = mem\<^sub>C' (var\<^sub>C_of y_var)" and
        y\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C y_var = mem\<^sub>A_of mem\<^sub>C' y_var" and
        z\<^sub>C_untouched: "mem\<^sub>C (var\<^sub>C_of z_var) = mem\<^sub>C' (var\<^sub>C_of z_var)" and
        z\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C z_var = mem\<^sub>A_of mem\<^sub>C' z_var"
        using reg_is_not_the_var\<^sub>C_of_anything mem\<^sub>A_of_def NoWrite\<^sub>A_implies_NoWrite\<^sub>C var_asm_not_written_def
        by (metis (no_types) insertCI reg_not_visible_abs, metis+)
      with if_else_rel_4.hyps(4,8)
      have conds_still_match:
        "ev\<^sub>A mem\<^sub>C' (Load reg0) = ev\<^sub>A (mem\<^sub>A_of mem\<^sub>C') (Add (Load y_var) (Load z_var))"
        by simp
      show "(\<langle>x_var \<leftarrow> Add (Load y_var) (Load z_var), mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A,
             \<langle>(x_mem \<leftarrow> Load reg0), mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C)
             \<in> RefRel_HighBranch"
        using RefRel_HighBranch.if_else_rel_4 if_else_rel_4 conds_still_match by simp
    qed
  next
  case (stop_seq_rel c\<^sub>A tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using stop_seq_rel
    by (simp add:RefRel_HighBranch.stop_seq_rel)
  next
  case (stop_rel mds\<^sub>C mem\<^sub>C)
  show ?case by (simp add:RefRel_HighBranch.stop_rel)
  qed
qed

lemma preserves_modes_mem_RefRel_HighBranch:
  "preserves_modes_mem RefRel_HighBranch"
unfolding preserves_modes_mem_def2
proof(clarsimp)
  fix c\<^sub>A mds\<^sub>A mem\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>C
  assume in_rel: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
  thus "mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C \<and> mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C"
    by (cases rule:RefRel_HighBranch.cases, blast+)
qed

lemma new_vars_private_RefRel_HighBranch:
  "sifum_refinement.new_vars_private dma\<^sub>C C.eval\<^sub>w var\<^sub>C_of RefRel_HighBranch"
unfolding new_vars_private_def
(* Slightly more intuitive goals without simp converting \<or> to \<longrightarrow> *)
proof(clarify)
  fix c\<^sub>A mds\<^sub>A mem\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>C c\<^sub>C' mds\<^sub>C' mem\<^sub>C'
  assume in_rel: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
      does_eval: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>C', mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
  let "?diff_mem v\<^sub>C" = "mem\<^sub>C' v\<^sub>C \<noteq> mem\<^sub>C v\<^sub>C"
  let "?diff_dma v\<^sub>C" = "dma\<^sub>C mem\<^sub>C' v\<^sub>C < dma\<^sub>C mem\<^sub>C v\<^sub>C"
  let "?conc_only v\<^sub>C" = "v\<^sub>C \<notin> range var\<^sub>C_of"
  show "(\<forall>v\<^sub>C. (?diff_mem v\<^sub>C \<or> ?diff_dma v\<^sub>C) \<and> ?conc_only v\<^sub>C \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite) \<and>
         mds\<^sub>C AsmNoReadOrWrite - range var\<^sub>C_of \<subseteq> mds\<^sub>C' AsmNoReadOrWrite - range var\<^sub>C_of"
  using in_rel does_eval
  proof(cases rule:RefRel_HighBranch.cases)
  case (acq_mode_rel x SomeMode tail\<^sub>A tail\<^sub>C)
    moreover with does_eval
    have "mds\<^sub>C' = mds\<^sub>C (SomeMode := insert (var\<^sub>C_of x) (mds\<^sub>C SomeMode))"
      by (metis (mono_tags) C.seq_decl_elim C.update_modes.simps(1))
    ultimately show ?thesis
      by simp
  next
  case (assign_load_rel x y tail\<^sub>A tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis C.assign_elim C.seq_elim Stmt.distinct(13) set_eq_subset)
  next
  case (assign_const_rel x z tail\<^sub>A tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis C.assign_elim C.seq_elim Stmt.distinct(13) set_eq_subset)
  next
  case (if_reg_load_rel x then\<^sub>A else\<^sub>A then\<^sub>C else\<^sub>C)
    with does_eval
    show ?thesis
      by (metis C.assign_elim C.seq_elim Stmt.distinct(13) set_eq_subset)
  next
  case (if_reg_stop_rel x then\<^sub>A else\<^sub>A then\<^sub>C else\<^sub>C)
    with does_eval
    show ?thesis
      by (metis C.seq_stop_elim subset_refl)
  next
  case (if_reg_rel x then\<^sub>A else\<^sub>A then\<^sub>C else\<^sub>C)
    with does_eval
    have mds\<^sub>C_unchanged: "mds\<^sub>C = mds\<^sub>C'"
      by (metis C.if_elim C.seq_elim Stmt.distinct(39))
    moreover with if_reg_rel(5)
    have "\<forall>v\<^sub>C. (?diff_mem v\<^sub>C \<or> ?diff_dma v\<^sub>C) \<and> ?conc_only v\<^sub>C \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite"
      by simp
    moreover from mds\<^sub>C_unchanged
    have "mds\<^sub>C AsmNoReadOrWrite - range var\<^sub>C_of \<subseteq> mds\<^sub>C' AsmNoReadOrWrite - range var\<^sub>C_of"
      by clarify
    ultimately show ?thesis
      by simp
  next
  case (if_then_rel_1 tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis (no_types, hide_lams) C.eval\<^sub>w.seq C.eval_det C.seq_stop_elim C.seq_stop_eval\<^sub>w C.skip_eval\<^sub>w subsetI)
  next
  case (if_then_rel_1' tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis (no_types, hide_lams) C.seq_stop_elim subsetI)
  next
  case (if_then_rel_2 tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis (no_types, hide_lams) C.eval\<^sub>w.seq C.eval_det C.seq_stop_elim C.seq_stop_eval\<^sub>w C.skip_eval\<^sub>w subsetI)
  next
  case (if_then_rel_2' tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis (no_types, hide_lams) C.seq_stop_elim subsetI)
  next
  case (if_then_rel_3 tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis (full_types) C.seq_assign_elim subset_refl)
  next
  case (if_then_rel_3' tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis (no_types, hide_lams) C.seq_stop_elim subsetI)
  next
  case (if_then_rel_4)
    with does_eval
    show ?thesis
      by (metis C.assign_elim order_refl)
  next
  case (if_else_rel_1 tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis (full_types) C.seq_assign_elim subset_refl)
  next
  case (if_else_rel_1' tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis (no_types, hide_lams) C.seq_stop_elim subsetI)
  next
  case (if_else_rel_2 tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis (full_types) C.seq_assign_elim subset_refl)
  next
  case (if_else_rel_2' tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis (no_types, hide_lams) C.seq_stop_elim subsetI)
  next
  case (if_else_rel_3 tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis (full_types) C.seq_assign_elim subset_refl)
  next
  case (if_else_rel_3' tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis (no_types, hide_lams) C.seq_stop_elim subsetI)
  next
  case (if_else_rel_4)
    with does_eval
    show ?thesis
      by (metis C.assign_elim order_refl)
  next
  case (stop_seq_rel tail\<^sub>A tail\<^sub>C)
    with does_eval C.seq_stop_elim
    show ?thesis by blast
  next
  case (stop_rel)
    with does_eval C.stop_no_eval have False by simp
    thus ?thesis by simp
  qed
qed

inductive_cases inR_E:
"(\<langle>c, mds, mem\<rangle>\<^sub>A, \<langle>c', mds', mem'\<rangle>\<^sub>A) \<in> A.R"

lemma refrel_helper_Acq_Rel_ex1I:
"
  (\<langle>(Skip@[x +=\<^sub>m SomeMode]) ;; c\<^sub>A_tail, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
      \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
     \<in> RefRel_HighBranch
  \<Longrightarrow>
  \<exists>!c\<^sub>C_tail.
  c\<^sub>2\<^sub>C = (Skip@[var\<^sub>C_of x +=\<^sub>m SomeMode]) ;; c\<^sub>C_tail \<and>
        ((\<langle>(Skip@[var\<^sub>C_of x +=\<^sub>m SomeMode]) ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
          \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C(SomeMode := insert (var\<^sub>C_of x) (mds\<^sub>C SomeMode)), mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
          \<in> C.eval\<^sub>w)"
  apply(cases rule:RefRel_HighBranch.cases)
       apply simp
      apply clarsimp
      apply(erule_tac x="mem\<^sub>A_of mem\<^sub>2\<^sub>C" in allE)
      apply(erule_tac x="mds\<^sub>C(SomeMode := insert (var\<^sub>C_of x) (mds\<^sub>C SomeMode))" in allE)
      apply(erule_tac x="mem\<^sub>2\<^sub>C" in allE)
      apply(erule impE)
       apply(rule_tac x="mem\<^sub>2\<^sub>C" in exI)
       apply(rule conjI)
        apply(rule HOL.refl)
       apply(rule conjI)
        apply(rule A.eval\<^sub>w.seq)
        apply(rule A.decl_eval\<^sub>w', rule HOL.refl, clarsimp)
        apply(rule mode_acquire_refinement_helper)
       apply(rule C.eval\<^sub>w.seq)
       apply(rule C.decl_eval\<^sub>w', rule HOL.refl, clarsimp)
      apply(rule_tac a=c\<^sub>C_tail in ex1I)
       apply clarsimp
        apply(rule C.eval\<^sub>w.seq)
        apply(rule C.decl_eval\<^sub>w', rule HOL.refl, clarsimp)
       apply blast+
  done

lemma refrel_helper_Assign_Load_ex1I:
"
  (\<langle>(x \<leftarrow> Load y) ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
      \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
     \<in> RefRel_HighBranch
  \<Longrightarrow>
  \<exists>!tail\<^sub>C.
  c\<^sub>2\<^sub>C = (var\<^sub>C_of x \<leftarrow> Load (var\<^sub>C_of y)) ;; tail\<^sub>C \<and>
        ((\<langle>(var\<^sub>C_of x \<leftarrow> Load (var\<^sub>C_of y)) ;; tail\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
          \<langle>Stop ;; tail\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C((var\<^sub>C_of x) := mem\<^sub>2\<^sub>C (var\<^sub>C_of y))\<rangle>\<^sub>C)
          \<in> C.eval\<^sub>w)"
  apply(cases rule:RefRel_HighBranch.cases, simp+)
          apply clarsimp
          apply(erule_tac x="mem\<^sub>A_of mem\<^sub>2\<^sub>C" in allE)
          apply(erule_tac x="mds\<^sub>C" in allE)
          apply(erule_tac x="mem\<^sub>2\<^sub>C((var\<^sub>C_of x) := mem\<^sub>2\<^sub>C (var\<^sub>C_of y))" in allE)
          apply(erule impE)
           apply(rule_tac x="mem\<^sub>2\<^sub>C" in exI)
           apply(rule conjI)
            apply(rule HOL.refl)
           apply(rule conjI)
            apply(rule A.eval\<^sub>w.seq)
            apply(simp add: assign_eval\<^sub>w_load\<^sub>A mem_assign_refinement_helper_var)
           apply(rule C.eval\<^sub>w.seq)
           apply(simp add: assign_eval\<^sub>w_load\<^sub>C)
          apply(rule_tac a=c\<^sub>C_tail in ex1I)
           apply clarsimp
           apply(rule C.eval\<^sub>w.seq)
           apply(simp add:assign_eval\<^sub>w_load\<^sub>C)
          apply blast
         apply clarsimp
        apply(simp add: assign_eval\<^sub>w_load\<^sub>A mem_assign_refinement_helper_var)
       apply(simp add:assign_eval\<^sub>w_load\<^sub>C)
      apply(rule_tac a=c\<^sub>C_tail in ex1I)
       apply clarsimp
      apply(simp add:assign_eval\<^sub>w_load\<^sub>C)
     apply blast
    apply(rule ex1I, clarsimp+)
  done


lemma refrel_helper_Assign_Const_ex1I:
"
  (\<langle>(x \<leftarrow> Const z) ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
      \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
     \<in> RefRel_HighBranch
  \<Longrightarrow>
  \<exists>!tail\<^sub>C.
  c\<^sub>2\<^sub>C = (var\<^sub>C_of x \<leftarrow> Const z) ;; tail\<^sub>C \<and>
        ((\<langle>(var\<^sub>C_of x \<leftarrow> Const z) ;; tail\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
          \<langle>Stop ;; tail\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C((var\<^sub>C_of x) := z)\<rangle>\<^sub>C)
          \<in> C.eval\<^sub>w)"
  apply(cases rule:RefRel_HighBranch.cases, simp+)
          apply clarsimp
          apply(erule_tac x="mem\<^sub>A_of mem\<^sub>2\<^sub>C" in allE)
          apply(erule_tac x="mds\<^sub>C" in allE)
          apply(erule_tac x="mem\<^sub>2\<^sub>C((var\<^sub>C_of x) := z)" in allE)
          apply(erule impE)
           apply(rule_tac x="mem\<^sub>2\<^sub>C" in exI)
           apply(rule conjI)
            apply(rule HOL.refl)
           apply(rule conjI)
            apply(rule A.eval\<^sub>w.seq)
            apply(simp add: assign_eval\<^sub>w_const\<^sub>A mem_assign_refinement_helper_const)
           apply(rule C.eval\<^sub>w.seq)
           apply(simp add:assign_eval\<^sub>w_const\<^sub>C)
          apply(rule_tac a=c\<^sub>C_tail in ex1I)
           apply clarsimp
           apply(rule C.eval\<^sub>w.seq)
           apply(simp add:assign_eval\<^sub>w_const\<^sub>C)
          apply blast
         apply clarsimp
        apply(simp add: assign_eval\<^sub>w_load\<^sub>A mem_assign_refinement_helper_var)
       apply(simp add:assign_eval\<^sub>w_const\<^sub>C)
      apply(rule_tac a=c\<^sub>C_tail in ex1I)
       apply clarsimp
      apply(simp add:assign_eval\<^sub>w_const\<^sub>C)
     apply blast
    apply(rule ex1I, clarsimp+)
  done

(* Could possibly be useful if we have one that just does seq *)
lemma refrel_helper_Assign_Const:
"
  (\<langle>(x \<leftarrow> Const z), mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
      \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
     \<in> RefRel_HighBranch
  \<Longrightarrow>
  c\<^sub>2\<^sub>C = (var\<^sub>C_of x \<leftarrow> Const z) \<and>
        ((\<langle>(var\<^sub>C_of x \<leftarrow> Const z), mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
          \<langle>Stop, mds\<^sub>C, mem\<^sub>2\<^sub>C((var\<^sub>C_of x) := z)\<rangle>\<^sub>C)
          \<in> C.eval\<^sub>w)"
  by (cases rule:RefRel_HighBranch.cases, (simp add:assign_eval\<^sub>w_const\<^sub>C)+)

type_synonym t_Neq_C = "(var\<^sub>C aexp \<Rightarrow> var\<^sub>C aexp \<Rightarrow> var\<^sub>C bexp)"

lemma refrel_helper_If_Reg_Load_exI:
  "
  c\<^sub>C = (reg3 \<leftarrow> Load (var\<^sub>C_of x)) ;; Stmt.If ((Neq::t_Neq_C) (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C
  \<Longrightarrow>
  c\<^sub>2\<^sub>A = If (Neq (Load x) (Const 0)) then\<^sub>A else\<^sub>A
  \<Longrightarrow>
  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
    \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
   \<in> RefRel_HighBranch
  \<Longrightarrow>
  A.neval
     \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
     \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A
  \<Longrightarrow>
  \<comment> \<open>Distinguish between the different concrete cases\<close>
  \<comment> \<open>for which the abstract program remains the same.\<close>
  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C
  \<Longrightarrow>
  \<exists>then\<^sub>C' else\<^sub>C'.
  ((c\<^sub>2\<^sub>C = (reg3 \<leftarrow> Load (var\<^sub>C_of x)) ;; Stmt.If ((Neq::t_Neq_C) (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C')
 \<and>
   (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
    \<langle>Stop ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C(reg3 := mem\<^sub>2\<^sub>C (var\<^sub>C_of x))\<rangle>\<^sub>C)
     \<in> C.eval\<^sub>w
)"
  apply(cases rule:RefRel_HighBranch.cases, simp+)
       apply clarsimp
       apply(erule_tac x="mem\<^sub>2\<^sub>C(reg3 := mem\<^sub>2\<^sub>C (var\<^sub>C_of x))" in allE)
       apply(erule impE)
        apply(rule_tac x="mem\<^sub>2\<^sub>C" in exI)
        apply(rule conjI)
         apply(simp add: conc_only_var_assign_not_visible_abs reg_not_visible_abs)
        apply(rule conjI)
         apply clarsimp
         apply(simp add: mem\<^sub>A_of_def)
        apply(rule C.eval\<^sub>w.seq)
        apply(simp add:assign_eval\<^sub>w_load\<^sub>C)
       apply(rule C.eval\<^sub>w.seq)
       apply(simp add:assign_eval\<^sub>w_load\<^sub>C)
      apply(erule rel_inv\<^sub>CE, simp+)+
  done

lemma refrel_helper_If_Reg_Stop_exI:
  "
  c\<^sub>C = Stop ;; Stmt.If ((Neq::t_Neq_C) (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C
  \<Longrightarrow>
  c\<^sub>2\<^sub>A = If (Neq (Load x) (Const 0)) then\<^sub>A else\<^sub>A
  \<Longrightarrow>
  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
    \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
   \<in> RefRel_HighBranch
  \<Longrightarrow>
  A.neval
     \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
     \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A
  \<Longrightarrow>
  \<comment> \<open>Distinguish between concrete cases for which abstract program remains the same.\<close>
  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C
  \<Longrightarrow>
  \<exists>then\<^sub>C' else\<^sub>C'.
  ((c\<^sub>2\<^sub>C = Stop ;; Stmt.If ((Neq::t_Neq_C) (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C')
 \<and>
   (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
    \<langle>Stmt.If ((Neq::t_Neq_C) (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
     \<in> C.eval\<^sub>w
)"
  apply(cases rule:RefRel_HighBranch.cases, simp+)
      apply(erule rel_inv\<^sub>CE, simp+)+
     apply(rule C.seq_stop_eval\<^sub>w)+
    apply(erule rel_inv\<^sub>CE, simp+)+
  done

lemma refrel_helper_If_Reg_exI:
assumes
  conds_match: "ev\<^sub>B (sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C) (Neq (Load x) (Const 0)) =
    ev\<^sub>B mem\<^sub>2\<^sub>C ((Neq::t_Neq_C) (Load reg3) (Const 0))" and
  rest_assms: "c\<^sub>C = Stmt.If ((Neq::t_Neq_C) (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C \<and>
  \<comment> \<open>Distinguish between concrete cases for which abstract program remains the same.\<close>
  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
shows
"
  \<exists>then\<^sub>C' else\<^sub>C'.
  ((c\<^sub>2\<^sub>C = Stmt.If ((Neq::t_Neq_C) (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C')
 \<and>
   (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
    \<langle>if (ev\<^sub>B mem\<^sub>2\<^sub>C ((Neq::t_Neq_C) (Load reg3) (Const 0))) then (then\<^sub>C') else (else\<^sub>C'),
                  mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
     \<in> C.eval\<^sub>w
)"
  using rest_assms
  apply(clarsimp simp del:ev\<^sub>B.simps split del:if_splits)
  apply(erule rel_inv\<^sub>CE, (clarsimp simp del:ev\<^sub>B.simps split del:if_splits)+)
  apply(rule C.if_eval\<^sub>w)
  done

inductive_cases Skip_tail_RefRel_HighBranchE: "(\<langle>Skip ;; c\<^sub>A_tail, mds\<^sub>A, mem\<^sub>A\<rangle>, \<langle>Skip ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C\<rangle>) \<in> RefRel_HighBranch"
thm Skip_tail_RefRel_HighBranchE

inductive_cases Stop_tail_RefRel_HighBranchE: "(\<langle>Stop ;; c\<^sub>A_tail, mds\<^sub>A, mem\<^sub>A\<rangle>, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C\<rangle>) \<in> RefRel_HighBranch"
thm Stop_tail_RefRel_HighBranchE

inductive_cases Acq_Mode_RefRel_HighBranchE:
"(\<langle>(Skip@[x +=\<^sub>m SomeMode]) ;; c\<^sub>A_tail, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A,
  \<langle>(Skip@[var\<^sub>C_of x +=\<^sub>m SomeMode]) ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
thm Acq_Mode_RefRel_HighBranchE

inductive_cases Assign_Load_RefRel_HighBranchE:
"(\<langle>(x \<leftarrow> aexp.Load y) ;; c\<^sub>A_tail, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A,
  \<langle>((var\<^sub>C_of x) \<leftarrow> Load (var\<^sub>C_of y)) ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
thm Assign_Load_RefRel_HighBranchE

inductive_cases Assign_Const_RefRel_HighBranchE:
"(\<langle>(x \<leftarrow> Const z) ;; c\<^sub>A_tail, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A,
  \<langle>((var\<^sub>C_of x) \<leftarrow> Const z) ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
thm Assign_Const_RefRel_HighBranchE

inductive_cases If_Reg_Load_RefRel_HighBranchE:
"(\<langle>(If (Neq (Load x) (Const 0)) c\<^sub>A_then c\<^sub>A_else), mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A,
  \<langle>(reg3 \<leftarrow> Load (var\<^sub>C_of y)) ;; ((If (Neq (Load reg3) (Const 0)) c\<^sub>C_then c\<^sub>C_else)), mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
thm If_Reg_Load_RefRel_HighBranchE

inductive_cases If_Reg_Stop_RefRel_HighBranchE:
"(\<langle>(If (Neq (Load x) (Const 0)) c\<^sub>A_then c\<^sub>A_else), mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A,
  \<langle>Stop ;; ((If (Neq (Load reg3) (Const 0)) c\<^sub>C_then c\<^sub>C_else)), mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
thm If_Reg_Stop_RefRel_HighBranchE

inductive_cases If_Reg_RefRel_HighBranchE:
"(\<langle>(If (Neq (Load x) (Const 0)) c\<^sub>A_then c\<^sub>A_else), mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A,
  \<langle>((If (Neq (Load reg3) (Const 0)) c\<^sub>C_then c\<^sub>C_else)), mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
thm If_Reg_RefRel_HighBranchE

inductive_cases If_Then_RefRel_HighBranchE:
"(\<langle>(x_var \<leftarrow> Load y_var), mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C)
  \<in> RefRel_HighBranch"

inductive_cases If_Else_RefRel_HighBranchE:
"(\<langle>(x_var \<leftarrow> Add (Load y_var) (Load z_var)), mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C)
  \<in> RefRel_HighBranch"

inductive_cases inv\<^sub>5E:
"A.inv \<langle>Assign x_var (Load y_var), mds, mem\<rangle>"

inductive_cases inv\<^sub>6E:
"A.inv \<langle>Assign x_var (Add (Load y_var) (Load z_var)), mds, mem\<rangle>"

lemma induction_full_RefRel_HighBranch:
  notes neq0_conv[simp del] neq0_conv[symmetric, simp add]
  shows
  "\<lbrakk>(\<langle>c\<^sub>1\<^sub>A, sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A,
         \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C)
        \<in> RefRel_HighBranch;
        (\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B\<rbrakk>
       \<Longrightarrow> \<exists>n c\<^sub>1\<^sub>A'.
              A.neval
               \<langle>c\<^sub>1\<^sub>A, sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A n
               \<langle>c\<^sub>1\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of
                         mds\<^sub>C', sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>1\<^sub>C'\<rangle>\<^sub>A \<and>
              (\<langle>c\<^sub>1\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>1\<^sub>C'\<rangle>\<^sub>A,
               \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C)
              \<in> RefRel_HighBranch \<and>
              (\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>1\<^sub>A, sifum_refinement.mds\<^sub>A_of var\<^sub>C_of
                            mds\<^sub>C, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>1\<^sub>C\<rangle>\<^sub>A,
                   \<langle>c\<^sub>2\<^sub>A, sifum_refinement.mds\<^sub>A_of var\<^sub>C_of
                            mds\<^sub>C, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A)
                  \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, sifum_refinement.mds\<^sub>A_of var\<^sub>C_of
                            mds\<^sub>C, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
                   \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A
                   n \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A,
                       \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
proof(induct rule: RefRel_HighBranch.induct)
case (acq_mode_rel c\<^sub>A x m tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  let ?c\<^sub>1\<^sub>A' = "Stop ;; tail\<^sub>A"
  from acq_mode_rel(1,2)
  have abs_steps_acq: "(abs_steps' c\<^sub>A c\<^sub>C) = 1"
    by (simp add:abs_steps'_def)
  moreover from acq_mode_rel.prems acq_mode_rel(2)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (Stop ;; tail\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C(m := insert (var\<^sub>C_of x) (mds\<^sub>C m))" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    by (metis (mono_tags) C.seq_decl_elim C.update_modes.simps(1))+
  moreover from mds\<^sub>C'_def
  have mds\<^sub>A'_def: "?mds\<^sub>A' = A.update_modes (x +=\<^sub>m m) (mds\<^sub>A_of mds\<^sub>C)"
    unfolding A.update_modes.simps
    by(blast intro: mode_acquire_refinement_helper)
  moreover with mem\<^sub>1\<^sub>C'_def acq_mode_rel A.eval\<^sub>w.seq A.decl_eval\<^sub>w
  have eval\<^sub>A: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
    by presburger
  hence neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 1 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A"
    by clarsimp
  moreover from acq_mode_rel(5)
  have mds\<^sub>C'_concrete_vars_unwritable:
    "(\<forall>v\<^sub>C. v\<^sub>C \<notin> range var\<^sub>C_of \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite)"
    by(auto simp: mds\<^sub>C'_def)
  moreover with acq_mode_rel(6)[simplified] acq_mode_rel.hyps(4) neval\<^sub>A c\<^sub>1\<^sub>C'_def
  have in_Rel': "(\<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    by (metis A.neval_Suc_simp One_nat_def acq_mode_rel.prems)
  moreover have "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
           (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
           (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
           \<in> RefRel_HighBranch \<and>
           (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
           A.neval
            \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 1
            \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
           (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
               (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
               (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
               \<in> RefRel_HighBranch \<and>
               (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
    proof(clarsimp)
      fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
      assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
        in_RefRel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
           \<in> RefRel_HighBranch" and
        in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
        eval\<^sub>2\<^sub>A: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
         \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A)
        \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B"
      let ?c\<^sub>2\<^sub>C' = "Stop ;; tail\<^sub>C"
      from in_rel_inv\<^sub>C acq_mode_rel(2) rel_inv\<^sub>CE
      have "c\<^sub>2\<^sub>C = (Skip@[var\<^sub>C_of x +=\<^sub>m m]) ;; tail\<^sub>C" by blast
      hence eval_tail\<^sub>C: "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; tail\<^sub>C, mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B"
        by (simp del:fun_upd_apply add:C.eval\<^sub>w.seq C.decl_eval\<^sub>w' mds\<^sub>C'_def)
      from in_R acq_mode_rel(1)
      have c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = (Skip@[x +=\<^sub>m m]) ;; tail\<^sub>A" by (blast elim:inR_E A.rel_invE)
      with acq_mode_rel(1,3,4)
      have "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
            \<langle>Stop ;; tail\<^sub>A, sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
        by (simp del:fun_upd_apply add:A.eval\<^sub>w.seq A.decl_eval\<^sub>w' mds\<^sub>C'_def mode_acquire_refinement_helper)
      with eval\<^sub>2\<^sub>A acq_mode_rel(1,3,4)
      have c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = Stop ;; tail\<^sub>A" and
        mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
        using A.eval_det by blast+
      from acq_mode_rel(3) in_RefRel c\<^sub>2\<^sub>A_def refrel_helper_Acq_Rel_ex1I
      obtain tail\<^sub>C' where
        c\<^sub>2\<^sub>C_def: "c\<^sub>2\<^sub>C = (Skip@[var\<^sub>C_of x +=\<^sub>m m]) ;; tail\<^sub>C'" and
        eval\<^sub>2\<^sub>C': "(\<langle>(Skip@[var\<^sub>C_of x +=\<^sub>m m]) ;; tail\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
                   \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C(m := insert (var\<^sub>C_of x) (mds\<^sub>C m)), mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> C.eval\<^sub>w"
        by blast
      have eval_tail\<^sub>C': "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
        by(simp add: mds\<^sub>C'_def c\<^sub>2\<^sub>C_def eval\<^sub>2\<^sub>C')
      with eval_tail\<^sub>C C.eval_det have
        tails_eq: "tail\<^sub>C = tail\<^sub>C'" by blast
      moreover have "(\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
      proof -
        from Acq_Mode_RefRel_HighBranchE[OF in_RefRel[simplified c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_def acq_mode_rel(3)]]
        have "((\<langle>(Skip@[x +=\<^sub>m m]) ;; tail\<^sub>A, mds\<^sub>A_of  mds\<^sub>C,  mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
                \<langle>Stop ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A)
               \<in> A.eval\<^sub>w) \<longrightarrow>
              (\<langle>Stop ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
               \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
              \<in> RefRel_HighBranch"
        using eval\<^sub>2\<^sub>C' mds\<^sub>C'_concrete_vars_unwritable
          by (metis (mono_tags, lifting) mds\<^sub>C'_def)
        hence "(\<langle>Stop ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
                \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
               \<in> RefRel_HighBranch"
        using A.eval\<^sub>w.seq A.decl_eval\<^sub>w' mds\<^sub>C'_def A.update_modes.simps mode_acquire_refinement_helper
          by simp
        thus ?thesis
          by(simp add: c\<^sub>2\<^sub>C_def c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def)
      qed
      moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
        using c\<^sub>1\<^sub>C'_def tails_eq rel_inv\<^sub>C_default
        by simp
      moreover note eval_tail\<^sub>C
      ultimately show "\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
              (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
              (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
              \<in> RefRel_HighBranch \<and>
              (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
              by blast
    qed
  thus ?case using in_Rel' abs_steps_acq neval\<^sub>A by blast
next
case (assign_load_rel c\<^sub>A x y tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "Stop ;; tail\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from assign_load_rel(1) assign_load_rel(2)
  have abs_steps_load: "(abs_steps' c\<^sub>A c\<^sub>C) = 1"
    by (simp add:abs_steps'_def)
  from assign_load_rel.prems assign_load_rel(2)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (Stop ;; tail\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C((var\<^sub>C_of x) := mem\<^sub>C (var\<^sub>C_of y))"
    using C.seq_elim C.assign_elim assign_eval\<^sub>w_load\<^sub>C
    by (metis (no_types, lifting) Stmt.distinct(13))+
  from assign_load_rel(1,3,4) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have eval\<^sub>A: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A,\<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w" and
    neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 1 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A"
    using A.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>A mem_assign_refinement_helper_var abs_steps_load by simp+
  with assign_load_rel(11)[simplified] assign_load_rel.prems c\<^sub>1\<^sub>C'_def
  have in_Rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using assign_load_rel.hyps(4-5) mds\<^sub>C'_def by blast
  have
    "\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 1
                   \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
    proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           eval\<^sub>2\<^sub>A: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
    let ?mem\<^sub>2\<^sub>C' = "(mem\<^sub>2\<^sub>C((var\<^sub>C_of x) := mem\<^sub>2\<^sub>C (var\<^sub>C_of y)))"
    from in_rel_inv\<^sub>C assign_load_rel(2) reg_is_not_the_var\<^sub>C_of_anything
    have "c\<^sub>2\<^sub>C = (var\<^sub>C_of x \<leftarrow> Load (var\<^sub>C_of y)) ;; tail\<^sub>C"
      by (blast elim:rel_inv\<^sub>CE)
    hence eval_tail\<^sub>C: "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; tail\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B"
      by (simp del:fun_upd_apply add:C.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>C mds\<^sub>C'_def)
    from assign_load_rel(1) in_R inR_E
    have c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = (x \<leftarrow> aexp.Load y) ;; tail\<^sub>A"
      by (blast elim:inR_E A.rel_invE)
    hence c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = Stop ;; tail\<^sub>A"
      and mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'"
      using eval\<^sub>2\<^sub>A abs_steps_load A.assign_elim A.seq_elim mem_assign_refinement_helper_var
      by fastforce+
    from assign_load_rel(3) in_Rel c\<^sub>2\<^sub>A_def refrel_helper_Assign_Load_ex1I
    obtain tail\<^sub>C' where
      c\<^sub>2\<^sub>C_def: "c\<^sub>2\<^sub>C = (var\<^sub>C_of x \<leftarrow> Load (var\<^sub>C_of y)) ;; tail\<^sub>C'" and
      eval\<^sub>2\<^sub>C': "(\<langle>(var\<^sub>C_of x \<leftarrow> Load (var\<^sub>C_of y)) ;; tail\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
                 \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C((var\<^sub>C_of x) := mem\<^sub>2\<^sub>C (var\<^sub>C_of y))\<rangle>\<^sub>C)
                \<in> C.eval\<^sub>w"
      by blast
    have eval_tail\<^sub>C': "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
                  \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C((var\<^sub>C_of x) := mem\<^sub>2\<^sub>C (var\<^sub>C_of y))\<rangle>\<^sub>C)
                  \<in> C.eval\<^sub>w"
      by(simp add: mds\<^sub>C'_def c\<^sub>2\<^sub>C_def eval\<^sub>2\<^sub>C')
    with eval_tail\<^sub>C C.eval_det have
        tails_eq: "tail\<^sub>C = tail\<^sub>C'" by blast
    moreover have "(\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                    \<in> RefRel_HighBranch"
    proof -
      from Assign_Load_RefRel_HighBranchE[OF in_Rel[simplified c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_def assign_load_rel(3)]]
      have "((\<langle>(x \<leftarrow> aexp.Load y) ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
              \<langle>Stop ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>A)
             \<in> A.eval\<^sub>w) \<longrightarrow>
            (\<langle>Stop ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>A,
             \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
            \<in> RefRel_HighBranch"
      using eval\<^sub>2\<^sub>C'
        by (metis mds\<^sub>C'_def)
      hence "(\<langle>Stop ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>A,
              \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
             \<in> RefRel_HighBranch"
      using A.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>A mds\<^sub>C'_def A.update_modes.simps mem_assign_refinement_helper_var
        by simp
      thus ?thesis
        by(simp add: c\<^sub>2\<^sub>C_def c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def)
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def tails_eq rel_inv\<^sub>C_default
      by simp
    moreover note eval_tail\<^sub>C eval_tail\<^sub>C'
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                  (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w \<and>
                  (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      by blast
  qed
  thus ?case using in_Rel' abs_steps_load neval\<^sub>A by blast
next
case (assign_const_rel c\<^sub>A x z tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "Stop ;; tail\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from assign_const_rel(1,2)
  have abs_steps_const: "(abs_steps' c\<^sub>A c\<^sub>C) = 1"
    by (simp add:abs_steps'_def)
  from assign_const_rel.prems assign_const_rel(2)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = Stop ;; tail\<^sub>C" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C((var\<^sub>C_of x) := z)"
    using C.seq_elim C.assign_elim assign_eval\<^sub>w_const\<^sub>C
    by (metis (no_types, lifting) Stmt.distinct(13))+
  from assign_const_rel(1,3,4) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have eval\<^sub>A: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w" and
    neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 1 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A"
    using A.eval\<^sub>w.seq assign_eval\<^sub>w_const\<^sub>A mem_assign_refinement_helper_const abs_steps_const by simp+
  with assign_const_rel c\<^sub>1\<^sub>C'_def stop_rel mds\<^sub>C'_def
  have in_Rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch" by blast
  have
    "\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 1
                   \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
    proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           eval\<^sub>2\<^sub>A: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
    let ?mem\<^sub>2\<^sub>C' = "(mem\<^sub>2\<^sub>C((var\<^sub>C_of x) := z))"
    from in_rel_inv\<^sub>C assign_const_rel(2) rel_inv\<^sub>CE
    have "c\<^sub>2\<^sub>C = (var\<^sub>C_of x \<leftarrow> Const z) ;; tail\<^sub>C" by blast
    moreover hence eval_tail\<^sub>C: "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; tail\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B"
      by (simp del:fun_upd_apply add:C.eval\<^sub>w.seq assign_eval\<^sub>w_const\<^sub>C mds\<^sub>C'_def)
    moreover from assign_const_rel(1) in_R inR_E
    have c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = (x \<leftarrow> Const z) ;; tail\<^sub>A"
      by (blast elim:inR_E A.rel_invE)
    moreover hence c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = Stop ;; tail\<^sub>A"
      and mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'"
      using eval\<^sub>2\<^sub>A abs_steps_const A.assign_elim A.seq_elim mem_assign_refinement_helper_const
      by fastforce+
    moreover from assign_const_rel(3) in_Rel c\<^sub>2\<^sub>A_def refrel_helper_Assign_Const_ex1I
    obtain tail\<^sub>C' where c\<^sub>2\<^sub>C_def: "c\<^sub>2\<^sub>C = (var\<^sub>C_of x \<leftarrow> Const z) ;; tail\<^sub>C'" and
      eval\<^sub>2\<^sub>C': "(\<langle>(var\<^sub>C_of x \<leftarrow> Const z) ;; tail\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
                 \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C((var\<^sub>C_of x) := z)\<rangle>\<^sub>C)
                \<in> C.eval\<^sub>w"
      by blast
    have eval_tail\<^sub>C': "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
                  \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C((var\<^sub>C_of x) := z)\<rangle>\<^sub>C)
                  \<in> C.eval\<^sub>w"
      by(simp add: mds\<^sub>C'_def c\<^sub>2\<^sub>C_def eval\<^sub>2\<^sub>C')
    with eval_tail\<^sub>C C.eval_det have
        tails_eq: "tail\<^sub>C = tail\<^sub>C'" by blast
    moreover have "(\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                    \<in> RefRel_HighBranch"
    proof -
      from Assign_Const_RefRel_HighBranchE[OF in_Rel[simplified c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_def assign_const_rel(3)]]
      have "((\<langle>(x \<leftarrow> Const z) ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A,
              \<langle>Stop ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>A)
             \<in> A.eval\<^sub>w) \<longrightarrow>
            (\<langle>Stop ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>A,
             \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
            \<in> RefRel_HighBranch"
      using eval\<^sub>2\<^sub>C'
        by (metis mds\<^sub>C'_def)
      hence "(\<langle>Stop ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C', mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>A,
              \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
             \<in> RefRel_HighBranch"
      using A.eval\<^sub>w.seq assign_eval\<^sub>w_const\<^sub>A mds\<^sub>C'_def A.update_modes.simps mem_assign_refinement_helper_const
        by simp
      thus ?thesis
        by(simp add: c\<^sub>2\<^sub>C_def c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def)
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>Stop ;; tail\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def tails_eq rel_inv\<^sub>C_default
      by simp
    moreover note eval_tail\<^sub>C eval_tail\<^sub>C'
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                  (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w \<and>
                  (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      by blast
  qed
  thus ?case using in_Rel' abs_steps_const neval\<^sub>A by blast
next
case (if_reg_load_rel c\<^sub>A x then\<^sub>A else\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_reg_load_rel.hyps(1,2)
  have abs_steps_if_reg_load: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_reg_load_rel.prems if_reg_load_rel(2)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (Stop ;; If (Neq (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C(reg3 := mem\<^sub>C (var\<^sub>C_of x))"
    using C.seq_elim C.assign_elim C.skip_elim assign_eval\<^sub>w_load\<^sub>C
    by (metis (no_types, lifting) Stmt.distinct(13))+
  from if_reg_load_rel(1-4) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using reg_not_visible_abs conc_only_var_assign_not_visible_abs A.neval.intros(1) by simp+
  with if_reg_load_rel c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    apply clarsimp
    apply(erule_tac x=mem\<^sub>1\<^sub>C' in allE)
    apply(erule_tac impE)
     apply(rule_tac x=mem\<^sub>C in exI)
     apply(rule conjI)
      apply(clarsimp)
     apply(rule conjI)
      apply clarsimp
      apply (simp add: mem\<^sub>A_of_def)
     using if_reg_load_rel.prems mem\<^sub>A_of_def apply blast
    apply clarsimp
    done
  (* This might be usable for an Isar proof of rel', but not sure how best to approach that *)
  from reg_not_visible_abs conc_only_var_assign_not_visible_abs mem\<^sub>A_of_def mem\<^sub>1\<^sub>C'_def
  have mem\<^sub>1\<^sub>C'_conds_match: "(mem\<^sub>1\<^sub>C' reg3 = 0) = (mem\<^sub>A_of mem\<^sub>1\<^sub>C' x = 0)"
    by simp
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
    proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?mem\<^sub>2\<^sub>C' = "(mem\<^sub>2\<^sub>C(reg3 := mem\<^sub>2\<^sub>C (var\<^sub>C_of x)))"
    from in_rel_inv\<^sub>C if_reg_load_rel(2) rel_inv\<^sub>CE
    have "c\<^sub>2\<^sub>C = (reg3 \<leftarrow> Load (var\<^sub>C_of x)) ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C" by blast
    hence eval_tail\<^sub>C: "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B"
      by (simp del:fun_upd_apply add:C.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>C mds\<^sub>C'_def)
    from if_reg_load_rel(1) in_R
    have c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = If (Neq (Load x) (Const 0)) then\<^sub>A else\<^sub>A"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
    using neval\<^sub>2\<^sub>A abs_steps_if_reg_load A.neval_ZeroE
      by (clarsimp, blast)+
    from if_reg_load_rel.hyps(2,3) c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>A'_def in_Rel neval\<^sub>2\<^sub>A abs_steps_if_reg_load in_rel_inv\<^sub>C
         refrel_helper_If_Reg_Load_exI
    obtain then\<^sub>C' else\<^sub>C' where
      c\<^sub>2\<^sub>C_def: "(c\<^sub>2\<^sub>C = (reg3 \<leftarrow> Load (var\<^sub>C_of x)) ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C')" and
      eval_tail\<^sub>C': "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
                 \<langle>Stop ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C',
                      mds\<^sub>C, mem\<^sub>2\<^sub>C(reg3 := mem\<^sub>2\<^sub>C (var\<^sub>C_of x))\<rangle>\<^sub>C)
                \<in> C.eval\<^sub>w"
      by metis
    with eval_tail\<^sub>C C.eval_det have
      tails_eq: "else\<^sub>C = else\<^sub>C' \<and> then\<^sub>C = then\<^sub>C'" by blast
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_reg_load_rel(1-9)
    have "(\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A,
                    \<langle>Stop ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C',
                       mds\<^sub>C, mem\<^sub>2\<^sub>C(reg3 := mem\<^sub>2\<^sub>C (var\<^sub>C_of x))\<rangle>\<^sub>C)
                   \<in> RefRel_HighBranch"
    proof -
      from If_Reg_Load_RefRel_HighBranchE[OF in_Rel[simplified c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_def if_reg_load_rel(1-9)]]
      have "(\<exists>mem\<^sub>C''.
           sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>C'' = sifum_refinement.mem\<^sub>A_of var\<^sub>C_of ?mem\<^sub>2\<^sub>C' \<and>
           (?mem\<^sub>2\<^sub>C' reg3 = 0) = (sifum_refinement.mem\<^sub>A_of var\<^sub>C_of ?mem\<^sub>2\<^sub>C' x = 0) \<and>
           (\<langle>(reg3 \<leftarrow> Load (var\<^sub>C_of x)) ;;
             Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>Stop ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
           \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B) \<longrightarrow>
             (\<langle>Stmt.If (Neq (Load x) (Const 0)) then\<^sub>A else\<^sub>A,
              sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>A,
              \<langle>Stop ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
             \<in> RefRel_HighBranch"  
        by (metis neq0_conv)
      moreover have "(?mem\<^sub>2\<^sub>C' reg3 = 0) = (sifum_refinement.mem\<^sub>A_of var\<^sub>C_of ?mem\<^sub>2\<^sub>C' x = 0)"
         using conc_only_var_assign_not_visible_abs reg_not_visible_abs mem\<^sub>A_of_def if_reg_load_rel(1-9)
         by simp
      moreover obtain mem\<^sub>C'' where
        "sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>C'' = sifum_refinement.mem\<^sub>A_of var\<^sub>C_of ?mem\<^sub>2\<^sub>C'"
        by simp
      ultimately have "(\<langle>Stmt.If (Neq (Load x) (Const 0)) then\<^sub>A else\<^sub>A,
              sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>A,
             \<langle>Stop ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
            \<in> RefRel_HighBranch"
        using c\<^sub>2\<^sub>C_def eval_tail\<^sub>C' if_reg_load_rel(1-9) conc_only_var_assign_not_visible_abs reg_not_visible_abs
        by auto
      thus ?thesis
      using if_reg_load_rel(1-9) c\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def conc_only_var_assign_not_visible_abs mds\<^sub>C'_def mem\<^sub>2\<^sub>A'_def reg_not_visible_abs
        by simp
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>Stop ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default tails_eq
      by simp
    moreover note eval_tail\<^sub>C' eval_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_reg_load_rel.hyps(3) by blast
  qed
  thus ?case using rel' abs_steps_if_reg_load neval\<^sub>A by blast
next
case (if_reg_stop_rel c\<^sub>A x then\<^sub>A else\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_reg_stop_rel.hyps(1,2)
  have abs_steps_if_reg_stop: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_reg_stop_rel.prems if_reg_stop_rel(2)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (If (Neq (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    using C.seq_stop_elim by simp+
  from if_reg_stop_rel(1-4) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using reg_not_visible_abs conc_only_var_assign_not_visible_abs A.neval.intros(1) by simp+
  with if_reg_stop_rel c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have in_Rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch" by blast
  have
    "\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
    proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?mem\<^sub>2\<^sub>C' = "mem\<^sub>2\<^sub>C"
    from in_rel_inv\<^sub>C if_reg_stop_rel(2) rel_inv\<^sub>CE
    have "c\<^sub>2\<^sub>C = Stop ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C" by blast
    hence eval_tail\<^sub>C: "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B"
      by (simp del:fun_upd_apply add:C.seq_stop_eval\<^sub>w mds\<^sub>C'_def)
    from if_reg_stop_rel in_R inR_E
    have c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = If (Neq (Load x) (Const 0)) then\<^sub>A else\<^sub>A"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
    using neval\<^sub>2\<^sub>A abs_steps_if_reg_stop A.neval_ZeroE
      by (clarsimp, blast)+
    from if_reg_stop_rel.hyps(2,3,7) c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>A'_def in_Rel neval\<^sub>2\<^sub>A abs_steps_if_reg_stop in_rel_inv\<^sub>C
         refrel_helper_If_Reg_Stop_exI
    obtain then\<^sub>C' else\<^sub>C' where
      c\<^sub>2\<^sub>C_def: "(c\<^sub>2\<^sub>C = Stop ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C')" and
      eval_tail\<^sub>C': "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
                 \<langle>Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                \<in> C.eval\<^sub>w"
      by metis+
    with eval_tail\<^sub>C C.eval_det have
      tails_eq: "else\<^sub>C = else\<^sub>C' \<and> then\<^sub>C = then\<^sub>C'" by blast
    moreover have "(\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A,
                    \<langle>Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                   \<in> RefRel_HighBranch"
    proof -
      from If_Reg_Stop_RefRel_HighBranchE[OF in_Rel[simplified c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_def if_reg_stop_rel(3)]]
      have "(\<langle>Stop ;; Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
             \<langle>Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                \<in> C.eval\<^sub>w \<longrightarrow>
            (\<langle>Stmt.If (Neq (Load x) (Const 0)) then\<^sub>A else\<^sub>A, sifum_refinement.mds\<^sub>A_of var\<^sub>C_of
                       mds\<^sub>C, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>A,
             \<langle>Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
            \<in> RefRel_HighBranch"
      using eval_tail\<^sub>C' mds\<^sub>C'_def
        by metis
      hence "(\<langle>Stmt.If (Neq (Load x) (Const 0)) then\<^sub>A else\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>A,
             \<langle>Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
            \<in> RefRel_HighBranch"
      using c\<^sub>2\<^sub>C_def eval_tail\<^sub>C'
        by auto
      thus ?thesis
      using c\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def conc_only_var_assign_not_visible_abs mds\<^sub>C'_def mem\<^sub>2\<^sub>A'_def reg_not_visible_abs
        by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default tails_eq
      by simp
    moreover note eval_tail\<^sub>C' eval_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
              (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
              \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
              (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
              \<in> RefRel_HighBranch \<and>
              (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using mds\<^sub>C'_def if_reg_stop_rel.hyps(3) by blast
  qed
  thus ?case using in_Rel' abs_steps_if_reg_stop neval\<^sub>A by blast
next
case (if_reg_rel c\<^sub>A x then\<^sub>A else\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "if (ev\<^sub>B mem\<^sub>A (Neq (Load x) (Const 0))) then (then\<^sub>A) else (else\<^sub>A)"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_reg_rel(1) if_reg_rel(2)
  have abs_steps_if_reg: "(abs_steps' c\<^sub>A c\<^sub>C) = 1"
    by (simp add:abs_steps'_def)
  from if_reg_rel.prems if_reg_rel(2)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (if (ev\<^sub>B mem\<^sub>C (Neq (Load reg3) (Const 0))) then (then\<^sub>C) else (else\<^sub>C))" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    apply simp_all
    by (erule C.if_elim, clarsimp+)+
  from if_reg_rel(1,3,4) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have eval\<^sub>A: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
    using if_seq_eval\<^sub>w_helper\<^sub>A A.if_eval\<^sub>w by presburger
  hence neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 1 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A"
    using abs_steps_if_reg by simp
  from if_reg_rel(3,4,7,12) if_reg_rel.prems c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def eval\<^sub>A
  have in_Rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    by clarsimp
  have
    "\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 1
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
    proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           eval\<^sub>2\<^sub>A: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
    let ?mem\<^sub>2\<^sub>C' = "mem\<^sub>2\<^sub>C"
    from in_rel_inv\<^sub>C if_reg_rel(2) rel_inv\<^sub>CE
    have "c\<^sub>2\<^sub>C = Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C" by blast
    hence eval_tail\<^sub>C: "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
        \<langle>if (ev\<^sub>B mem\<^sub>2\<^sub>C (Neq (Load reg3) (Const 0)))
         then (then\<^sub>C) else (else\<^sub>C), mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B"
      by (blast intro:C.if_eval\<^sub>w if_seq_eval\<^sub>w_helper\<^sub>C)
    from if_reg_rel(1-10) in_R inR_E
    have c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = If (Neq (Load x) (Const 0)) then\<^sub>A else\<^sub>A"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = (if (ev\<^sub>B (mem\<^sub>A_of mem\<^sub>2\<^sub>C) (Neq (Load x) (Const 0)))
         then (then\<^sub>A) else (else\<^sub>A))" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
      using eval\<^sub>2\<^sub>A if_seq_eval\<^sub>w_helper\<^sub>A A.if_eval\<^sub>w if_reg_rel(1-4) A.eval_det
      by blast+
    from in_Rel c\<^sub>2\<^sub>A_def in_rel_inv\<^sub>C if_reg_rel(2)
    have mem\<^sub>2\<^sub>C_reg_mem\<^sub>A_x: "ev\<^sub>B (mem\<^sub>A_of mem\<^sub>2\<^sub>C) (Neq (Load x) (Const 0)) = ev\<^sub>B mem\<^sub>2\<^sub>C (Neq (Load reg3) (Const 0))"
      apply -
      apply(erule RefRelE, simp_all)
      by (erule rel_inv\<^sub>CE, simp+)
    with if_reg_rel.hyps(2,3,7) c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>A'_def in_Rel eval\<^sub>2\<^sub>A abs_steps_if_reg in_rel_inv\<^sub>C
         refrel_helper_If_Reg_exI
    obtain then\<^sub>C' else\<^sub>C' where
      c\<^sub>2\<^sub>C_def: "(c\<^sub>2\<^sub>C = Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C' else\<^sub>C')" and
      eval_tail\<^sub>C': "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
                 \<langle>if (ev\<^sub>B mem\<^sub>2\<^sub>C (Neq (Load reg3) (Const 0)))
                  then (then\<^sub>C') else (else\<^sub>C'), mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> C.eval\<^sub>w"
      by blast
    with eval_tail\<^sub>C C.eval_det have
      tails_eq: "else\<^sub>C = else\<^sub>C' \<and> then\<^sub>C = then\<^sub>C'"
      by (simp add: \<open>c\<^sub>2\<^sub>C = Stmt.If (Neq (Load reg3) (Const 0)) then\<^sub>C else\<^sub>C\<close>)
    let ?c\<^sub>2\<^sub>C' = "if (ev\<^sub>B mem\<^sub>2\<^sub>C (Neq (Load reg3) (Const 0))) then (then\<^sub>C') else (else\<^sub>C')"
    have "(\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>?c\<^sub>2\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      from in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_def if_reg_rel(3,7,9) eval_tail\<^sub>C mds\<^sub>C'_def c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
           eval\<^sub>2\<^sub>A abs_steps_if_reg
      have "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>?c\<^sub>2\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w \<longrightarrow>
            (\<langle>c\<^sub>2\<^sub>A', ?mds\<^sub>A', mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>A, \<langle>?c\<^sub>2\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        apply clarsimp
        apply(erule If_Reg_RefRel_HighBranchE)
        apply(erule_tac x=mem\<^sub>2\<^sub>C in allE)
        apply(erule_tac x=mem\<^sub>2\<^sub>C in allE)
        apply(clarsimp split del: if_split)
        by presburger
      hence "(\<langle>c\<^sub>2\<^sub>A', ?mds\<^sub>A', mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>A, \<langle>?c\<^sub>2\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
      using c\<^sub>2\<^sub>C_def eval_tail\<^sub>C' mds\<^sub>C'_def
        by auto
      thus ?thesis
      using c\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def conc_only_var_assign_not_visible_abs mds\<^sub>C'_def mem\<^sub>2\<^sub>A'_def reg_not_visible_abs
        by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>?c\<^sub>2\<^sub>C', mds\<^sub>C', ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
    proof -
      have "(\<langle>if ev\<^sub>B mem\<^sub>2\<^sub>C (Neq (Load reg3) (Const 0)) then then\<^sub>C' else else\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
             \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C)
             \<in> rel_inv\<^sub>C \<or>
            (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C,
             \<langle>if ev\<^sub>B mem\<^sub>2\<^sub>C (Neq (Load reg3) (Const 0)) then then\<^sub>C' else else\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
             \<in> rel_inv\<^sub>C"
        using c\<^sub>1\<^sub>C'_def if_reg_rel.hyps(11) mds\<^sub>C'_def rel_inv\<^sub>C.rel_inv\<^sub>C_default tails_eq by auto
      thus ?thesis
        by (meson rel_inv\<^sub>C_sym symE)
    qed
    moreover note eval_tail\<^sub>C' eval_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
              (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
              (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
              \<in> RefRel_HighBranch \<and>
              (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using mds\<^sub>C'_def by blast
  qed
  thus ?case using in_Rel' abs_steps_if_reg neval\<^sub>A by blast
next
case (if_then_rel_1 c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_then_rel_1.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_then_rel_1.prems if_then_rel_1(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (Stop ;; tail\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    using C.seq_elim C.skip_elim by blast+
  from if_then_rel_1(1-5) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using A.neval.intros(1) by auto
  with if_then_rel_1 c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    by blast
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?mem\<^sub>2\<^sub>C' = "mem\<^sub>2\<^sub>C(reg1 := mem\<^sub>2\<^sub>C y_mem)"
    let ?tail\<^sub>2\<^sub>C = "(reg2 \<leftarrow> Load z_mem) ;;
                (reg0 \<leftarrow> Add (Load reg1) (Load reg2)) ;; (x_mem \<leftarrow> Load reg0)"
    from in_rel_inv\<^sub>C if_then_rel_1(2-3)
    have "c\<^sub>2\<^sub>C = c\<^sub>C \<or>
          c\<^sub>2\<^sub>C = (reg1 \<leftarrow> Load y_mem) ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    moreover from in_R if_then_rel_1(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
      using neval\<^sub>2\<^sub>A abs_steps_this A.neval_ZeroE
      by (clarsimp, blast)+

    (* c\<^sub>2\<^sub>C is also in the 'then' branch *)
    moreover have eval_then_tail\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_then_rel_1(2,3) c\<^sub>1\<^sub>C'_def C.eval\<^sub>w.seq C.skip_eval\<^sub>w by blast
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_then_rel_1(1-6)
    have c\<^sub>2\<^sub>C_then_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: If_Then_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_then_rel_1(1-8) c\<^sub>1\<^sub>C'_def
    have "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
      by (clarsimp, meson C.eval\<^sub>w.seq C.skip_eval\<^sub>w)
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp

    (* c\<^sub>2\<^sub>C is in the other, 'else' branch *)
    moreover have eval_else_tail\<^sub>C: "(\<langle>(reg1 \<leftarrow> Load y_mem) ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp del:fun_upd_apply add:C.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>C mds\<^sub>C'_def)
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_then_rel_1(1-6)
    have c\<^sub>2\<^sub>C_else_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = (reg1 \<leftarrow> Load y_mem) ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: If_Else_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover have "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A"
      from in_else c\<^sub>2\<^sub>A_def have
        c\<^sub>2\<^sub>A_else_def: "c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
        by clarsimp
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_else_def if_then_rel_1.hyps(4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C' \<and>
           (\<langle>(reg1 \<leftarrow> Load y_mem) ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        apply clarsimp
        apply(erule If_Else_RefRel_HighBranchE)
        apply(erule_tac x="mem\<^sub>A_of mem\<^sub>C''" in allE)
        apply(erule_tac x="mds\<^sub>C" in allE)
        apply(erule_tac x="mem\<^sub>2\<^sub>C(reg1 := mem\<^sub>2\<^sub>C y_mem)" in allE)
        using conc_only_var_assign_not_visible_abs reg_not_visible_abs mem\<^sub>A_of_def by auto
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'"
        by simp
      ultimately show ?thesis
        using conc_only_var_assign_not_visible_abs eval_else_tail\<^sub>C reg_not_visible_abs by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_then_rel_1(3) rel_inv\<^sub>C_2 by simp

    moreover note eval_then_tail\<^sub>C eval_else_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_then_rel_1.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (if_else_rel_1 c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_else_rel_1.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_else_rel_1.prems if_else_rel_1(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (Stop ;; tail\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C(reg1 := mem\<^sub>C y_mem)"
    using C.seq_elim C.assign_elim assign_eval\<^sub>w_load\<^sub>C
    by (metis (no_types, lifting) Stmt.distinct(13))+
  from if_else_rel_1(1-5) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using A.neval.neval_0 conc_only_var_assign_not_visible_abs reg_not_visible_abs by simp+
  with if_else_rel_1 c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    apply clarsimp
    apply(erule_tac x=mem\<^sub>A in allE)
    apply(erule_tac x=mds\<^sub>C in allE)
    apply(erule_tac x=mem\<^sub>1\<^sub>C' in allE)
    apply(erule_tac impE)
     apply(rule_tac x=mem\<^sub>C in exI)
     apply(rule conjI)
      apply(clarsimp)
     apply(rule conjI)
      apply clarsimp
      apply (simp add: mem\<^sub>A_of_def)
     using if_else_rel_1.prems mem\<^sub>A_of_def apply blast
    apply clarsimp
    done
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?mem\<^sub>2\<^sub>C' = "mem\<^sub>2\<^sub>C(reg1 := mem\<^sub>2\<^sub>C y_mem)"
    let ?tail\<^sub>2\<^sub>C = "Skip ;;
                (reg0 \<leftarrow> Load y_mem) ;; (x_mem \<leftarrow> Load reg0)"
    from in_rel_inv\<^sub>C if_else_rel_1(2-3)
    have "c\<^sub>2\<^sub>C = c\<^sub>C \<or>
          c\<^sub>2\<^sub>C = Skip ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    moreover from in_R if_else_rel_1(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
      using neval\<^sub>2\<^sub>A abs_steps_this A.neval_ZeroE
      by (clarsimp, blast)+

    (* c\<^sub>2\<^sub>C is in the other, 'then' branch *)
    moreover have eval_then_tail\<^sub>C: "(\<langle>Skip ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_else_rel_1(2,3) c\<^sub>1\<^sub>C'_def C.eval\<^sub>w.seq C.skip_eval\<^sub>w by blast
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_else_rel_1(1-6)
    have c\<^sub>2\<^sub>C_then_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = Skip ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: If_Then_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover with c\<^sub>2\<^sub>A_def
    have c\<^sub>2\<^sub>A_then_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
      by clarsimp
    moreover have "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_then: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A"
      with in_then in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_then_def if_else_rel_1.hyps(4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C \<and>
           (\<langle>Skip ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        apply clarsimp
        apply(erule If_Then_RefRel_HighBranchE)
        apply(erule_tac x="mem\<^sub>A_of mem\<^sub>C''" in allE)
        apply(erule_tac x="mds\<^sub>C" in allE)
        apply(erule_tac x="mem\<^sub>2\<^sub>C" in allE)
        by auto
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
        by simp
      ultimately show ?thesis
        using eval_then_tail\<^sub>C by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_else_rel_1(2,3) rel_inv\<^sub>C_2' mem\<^sub>1\<^sub>C'_def mds\<^sub>C'_def by simp

    (* c\<^sub>2\<^sub>C is also in the 'else' branch *)
    moreover have eval_else_tail\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp del:fun_upd_apply add:C.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>C mds\<^sub>C'_def c\<^sub>1\<^sub>C'_def if_else_rel_1(2,3))
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_else_rel_1(1-6)
    have c\<^sub>2\<^sub>C_else_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: If_Else_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover have "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A = c\<^sub>A"
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_else_def if_else_rel_1.hyps(1-4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>1\<^sub>C'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C' \<and>
           (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        apply clarsimp
        apply(erule If_Else_RefRel_HighBranchE)
        apply(erule_tac x="mem\<^sub>A_of mem\<^sub>C''" in allE)
        apply(erule_tac x="mds\<^sub>C" in allE)
        apply(erule_tac x="?mem\<^sub>2\<^sub>C'" in allE)
        using conc_only_var_assign_not_visible_abs reg_not_visible_abs mem\<^sub>A_of_def by auto
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'"
        by simp
      ultimately show ?thesis
        using conc_only_var_assign_not_visible_abs eval_else_tail\<^sub>C reg_not_visible_abs by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp

    moreover note eval_then_tail\<^sub>C eval_else_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_else_rel_1.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (if_then_rel_1' c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_then_rel_1'.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_then_rel_1'.prems if_then_rel_1'(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = tail\<^sub>C" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    using C.seq_stop_elim by blast+
  from if_then_rel_1'(1-5) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using A.neval.intros(1) by auto
  with if_then_rel_1' c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    by blast
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?tail\<^sub>2\<^sub>C = "(reg2 \<leftarrow> Load z_mem) ;;
                (reg0 \<leftarrow> Add (Load reg1) (Load reg2)) ;; (x_mem \<leftarrow> Load reg0)"
    from in_rel_inv\<^sub>C if_then_rel_1'(2-3)
    have "c\<^sub>2\<^sub>C = c\<^sub>C \<or>
          c\<^sub>2\<^sub>C = Stop ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    moreover from in_R if_then_rel_1'(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
      using neval\<^sub>2\<^sub>A abs_steps_this A.neval_ZeroE
      by (clarsimp, blast)+

    (* c\<^sub>2\<^sub>C is also in the 'then' branch *)
    moreover have eval_then_tail\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_then_rel_1'(2,3) c\<^sub>1\<^sub>C'_def C.seq_stop_eval\<^sub>w by blast
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_then_rel_1'(1-6)
    have c\<^sub>2\<^sub>C_then_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: If_Then_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_then_rel_1'(1-8) c\<^sub>1\<^sub>C'_def
    have "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
      by (clarsimp, meson C.seq_stop_eval\<^sub>w)
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp

    (* c\<^sub>2\<^sub>C is in the other, 'else' branch *)
    moreover have eval_else_tail\<^sub>C: "(\<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp del:fun_upd_apply add:C.seq_stop_eval\<^sub>w mds\<^sub>C'_def)
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_then_rel_1'(1-6)
    have c\<^sub>2\<^sub>C_else_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = Stop ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: If_Else_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_then_rel_1'(1-8) c\<^sub>1\<^sub>C'_def
    have "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A"
      from in_else c\<^sub>2\<^sub>A_def have
        c\<^sub>2\<^sub>A_else_def: "c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
        by clarsimp
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_else_def if_then_rel_1'.hyps(4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C \<and>
           (\<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        apply clarsimp
        apply(erule If_Else_RefRel_HighBranchE)
        apply(erule_tac x="mem\<^sub>A_of mem\<^sub>C''" in allE)
        apply(erule_tac x="mds\<^sub>C" in allE)
        apply(erule_tac x="mem\<^sub>2\<^sub>C" in allE)
        using eval_else_tail\<^sub>C by blast+
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C" by simp
      ultimately show ?thesis using eval_else_tail\<^sub>C by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_then_rel_1'(3) rel_inv\<^sub>C_3 by simp

    moreover note eval_then_tail\<^sub>C eval_else_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_then_rel_1'.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (if_else_rel_1' c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_else_rel_1'.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_else_rel_1'.prems if_else_rel_1'(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = tail\<^sub>C" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    using C.seq_stop_elim by blast+
  from if_else_rel_1'(1-5) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using A.neval.neval_0 by simp+
  with if_else_rel_1' c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    by blast
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?tail\<^sub>2\<^sub>C = "Skip ;; (reg0 \<leftarrow> Load y_mem) ;; (x_mem \<leftarrow> Load reg0)"
    from in_rel_inv\<^sub>C if_else_rel_1'(2-3)
    have "c\<^sub>2\<^sub>C = c\<^sub>C \<or>
          c\<^sub>2\<^sub>C = Stop ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    moreover from in_R if_else_rel_1'(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
      using neval\<^sub>2\<^sub>A abs_steps_this A.neval_ZeroE
      by (clarsimp, blast)+

    (* c\<^sub>2\<^sub>C is in the other, 'then' branch *)
    moreover have eval_then_tail\<^sub>C: "(\<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_else_rel_1'(2,3) c\<^sub>1\<^sub>C'_def C.seq_stop_eval\<^sub>w by blast
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_else_rel_1'(1-6)
    have c\<^sub>2\<^sub>C_then_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = Stop ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: If_Then_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover with c\<^sub>2\<^sub>A_def
    have c\<^sub>2\<^sub>A_then_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
      by clarsimp
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_else_rel_1'(1-8) c\<^sub>1\<^sub>C'_def c\<^sub>2\<^sub>A_then_def
    have "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A"
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_then_def if_else_rel_1'.hyps(4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C \<and>
           (\<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        by (blast elim: If_Then_RefRel_HighBranchE)
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
        by simp
      ultimately show ?thesis
        using eval_then_tail\<^sub>C by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_else_rel_1'(2,3) rel_inv\<^sub>C_3' mem\<^sub>1\<^sub>C'_def mds\<^sub>C'_def by simp

    (* c\<^sub>2\<^sub>C is also in the 'else' branch *)
    moreover have eval_else_tail\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp del:fun_upd_apply add:C.seq_stop_eval\<^sub>w mds\<^sub>C'_def c\<^sub>1\<^sub>C'_def if_else_rel_1'(2,3))
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_else_rel_1'(1-6)
    have c\<^sub>2\<^sub>C_else_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: If_Else_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_else_rel_1'(1-8) c\<^sub>1\<^sub>C'_def
    have "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A = c\<^sub>A"
      from in_else c\<^sub>2\<^sub>A_def if_else_rel_1'(1) have
        c\<^sub>2\<^sub>A_else_def: "c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
        by clarsimp
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_else_def if_else_rel_1'.hyps(1-4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>1\<^sub>C'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C \<and>
           (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        apply clarsimp
        apply(erule If_Else_RefRel_HighBranchE)
        apply(erule_tac x="mem\<^sub>A_of mem\<^sub>C''" in allE)
        apply(erule_tac x="mds\<^sub>C" in allE)
        apply(erule_tac x="mem\<^sub>2\<^sub>C" in allE)
        using eval_else_tail\<^sub>C by blast+
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C" by simp
      ultimately show ?thesis using eval_else_tail\<^sub>C by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp

    moreover note eval_then_tail\<^sub>C eval_else_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_else_rel_1'.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (if_then_rel_2 c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_then_rel_2.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_then_rel_2.prems if_then_rel_2(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (Stop ;; tail\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    using C.seq_elim C.skip_elim by blast+
  from if_then_rel_2(1-5) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using A.neval.intros(1) by auto
  with if_then_rel_2 c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    by blast
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?mem\<^sub>2\<^sub>C' = "mem\<^sub>2\<^sub>C(reg2 := mem\<^sub>2\<^sub>C z_mem)"
    let ?tail\<^sub>2\<^sub>C = "(reg0 \<leftarrow> Add (Load reg1) (Load reg2)) ;; (x_mem \<leftarrow> Load reg0)"
    from in_rel_inv\<^sub>C if_then_rel_2(2-3)
    have "c\<^sub>2\<^sub>C = c\<^sub>C \<or> c\<^sub>2\<^sub>C = (reg2 \<leftarrow> Load z_mem) ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    moreover from in_R if_then_rel_2(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
      using neval\<^sub>2\<^sub>A abs_steps_this A.neval_ZeroE
      by (clarsimp, blast)+

    (* c\<^sub>2\<^sub>C is also in the 'then' branch *)
    moreover have eval_then_tail\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_then_rel_2(2,3) c\<^sub>1\<^sub>C'_def C.eval\<^sub>w.seq C.skip_eval\<^sub>w by blast
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_then_rel_2(1-6)
    have c\<^sub>2\<^sub>C_then_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: If_Then_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_then_rel_2(1-8) c\<^sub>1\<^sub>C'_def
    have "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
      by (clarsimp, meson C.eval\<^sub>w.seq C.skip_eval\<^sub>w)
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp

    (* c\<^sub>2\<^sub>C is in the other, 'else' branch *)
    moreover have eval_else_tail\<^sub>C: "(\<langle>(reg2 \<leftarrow> Load z_mem) ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp del:fun_upd_apply add:C.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>C mds\<^sub>C'_def)
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_then_rel_2(1-6)
    have c\<^sub>2\<^sub>C_else_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = (reg2 \<leftarrow> Load z_mem) ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: If_Else_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover have "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A"
      from in_else c\<^sub>2\<^sub>A_def have
        c\<^sub>2\<^sub>A_else_def: "c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
        by clarsimp
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_else_def if_then_rel_2.hyps(4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C' \<and>
           (\<langle>(reg2 \<leftarrow> Load z_mem) ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        apply clarsimp
        apply(erule If_Else_RefRel_HighBranchE, simp+)
        apply(erule_tac x="mem\<^sub>A_of mem\<^sub>C''" in allE)
        apply(erule_tac x="mds\<^sub>C" in allE)
        apply(erule_tac x="?mem\<^sub>2\<^sub>C'" in allE)
        using conc_only_var_assign_not_visible_abs reg_not_visible_abs mem\<^sub>A_of_def eval_else_tail\<^sub>C by auto
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'" by simp
      ultimately show ?thesis
        using conc_only_var_assign_not_visible_abs eval_else_tail\<^sub>C reg_not_visible_abs by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_then_rel_2(3) rel_inv\<^sub>C_4 by simp

    moreover note eval_then_tail\<^sub>C eval_else_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_then_rel_2.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (if_else_rel_2 c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_else_rel_2.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_else_rel_2.prems if_else_rel_2(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (Stop ;; tail\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C(reg2 := mem\<^sub>C z_mem)"
    using C.seq_elim C.assign_elim assign_eval\<^sub>w_load\<^sub>C
    by (metis (no_types, lifting) Stmt.distinct(13))+
  from if_else_rel_2(1-5) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using A.neval.neval_0 conc_only_var_assign_not_visible_abs reg_not_visible_abs by simp+
  with if_else_rel_2 c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    apply clarsimp
    apply(erule_tac x=mem\<^sub>A in allE)
    apply(erule_tac x=mds\<^sub>C in allE)
    apply(erule_tac x=mem\<^sub>1\<^sub>C' in allE)
    apply(erule_tac impE)
     apply(rule_tac x=mem\<^sub>C in exI)
     apply(rule conjI)
      apply(clarsimp)
     apply(rule conjI)
      apply clarsimp
      apply (simp add: mem\<^sub>A_of_def)
     using if_else_rel_2.prems mem\<^sub>A_of_def apply blast
    apply clarsimp
    done
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?mem\<^sub>2\<^sub>C' = "mem\<^sub>2\<^sub>C(reg2 := mem\<^sub>2\<^sub>C z_mem)"
    let ?tail\<^sub>2\<^sub>C = "(reg0 \<leftarrow> Load y_mem) ;; (x_mem \<leftarrow> Load reg0)"
    from in_rel_inv\<^sub>C if_else_rel_2(2-3)
    have "c\<^sub>2\<^sub>C = c\<^sub>C \<or>
          c\<^sub>2\<^sub>C = Skip ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    moreover from in_R if_else_rel_2(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
      using neval\<^sub>2\<^sub>A abs_steps_this A.neval_ZeroE
      by (clarsimp, blast)+

    (* c\<^sub>2\<^sub>C is in the other, 'then' branch *)
    moreover have eval_then_tail\<^sub>C: "(\<langle>Skip ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_else_rel_2(2,3) c\<^sub>1\<^sub>C'_def C.eval\<^sub>w.seq C.skip_eval\<^sub>w by blast
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_else_rel_2(1-6)
    have c\<^sub>2\<^sub>C_then_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = Skip ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: If_Then_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover with c\<^sub>2\<^sub>A_def
    have c\<^sub>2\<^sub>A_then_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
      by clarsimp
    moreover have "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A"
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_then_def if_else_rel_2.hyps(4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C \<and>
           (\<langle>Skip ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        apply clarsimp
        apply(erule If_Then_RefRel_HighBranchE, simp+)
        apply(erule_tac x="mem\<^sub>A_of mem\<^sub>C''" in allE)
        apply(erule_tac x="mds\<^sub>C" in allE)
        apply(erule_tac x="mem\<^sub>2\<^sub>C" in allE)
        by auto
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
        by simp
      ultimately show ?thesis
        using eval_then_tail\<^sub>C by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_else_rel_2(2,3) rel_inv\<^sub>C_4' mem\<^sub>1\<^sub>C'_def mds\<^sub>C'_def by simp

    (* c\<^sub>2\<^sub>C is also in the 'else' branch *)
    moreover have eval_else_tail\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp del:fun_upd_apply add:C.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>C mds\<^sub>C'_def c\<^sub>1\<^sub>C'_def if_else_rel_2(2,3))
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_else_rel_2(1-6)
    have c\<^sub>2\<^sub>C_else_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: If_Else_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover have "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A = c\<^sub>A"
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_else_def if_else_rel_2.hyps(1-4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>1\<^sub>C'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C' \<and>
           (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        apply clarsimp
        apply(erule If_Else_RefRel_HighBranchE, simp+)
        apply(erule_tac x="mem\<^sub>A_of mem\<^sub>C''" in allE)
        apply(erule_tac x="mds\<^sub>C" in allE)
        apply(erule_tac x="?mem\<^sub>2\<^sub>C'" in allE)
        using conc_only_var_assign_not_visible_abs reg_not_visible_abs mem\<^sub>A_of_def eval_else_tail\<^sub>C by auto
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'"
        by simp
      ultimately show ?thesis
        using conc_only_var_assign_not_visible_abs eval_else_tail\<^sub>C reg_not_visible_abs by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp

    moreover note eval_then_tail\<^sub>C eval_else_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_else_rel_2.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (if_then_rel_2' c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_then_rel_2'.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_then_rel_2'.prems if_then_rel_2'(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = tail\<^sub>C" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    using C.seq_stop_elim by blast+
  from if_then_rel_2'(1-5) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using A.neval.intros(1) by auto
  with if_then_rel_2' c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    by blast
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?tail\<^sub>2\<^sub>C = "(reg0 \<leftarrow> Add (Load reg1) (Load reg2)) ;; (x_mem \<leftarrow> Load reg0)"
    from in_rel_inv\<^sub>C if_then_rel_2'(2-3)
    have "c\<^sub>2\<^sub>C = c\<^sub>C \<or>
          c\<^sub>2\<^sub>C = Stop ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    moreover from in_R if_then_rel_2'(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
      using neval\<^sub>2\<^sub>A abs_steps_this A.neval_ZeroE
      by (clarsimp, blast)+

    (* c\<^sub>2\<^sub>C is also in the 'then' branch *)
    moreover have eval_then_tail\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_then_rel_2'(2,3) c\<^sub>1\<^sub>C'_def C.seq_stop_eval\<^sub>w by blast
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_then_rel_2'(1-6)
    have c\<^sub>2\<^sub>C_then_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: If_Then_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_then_rel_2'(1-8) c\<^sub>1\<^sub>C'_def
    have "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
      by (clarsimp, meson C.seq_stop_eval\<^sub>w)
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp

    (* c\<^sub>2\<^sub>C is in the other, 'else' branch *)
    moreover have eval_else_tail\<^sub>C: "(\<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp del:fun_upd_apply add:C.seq_stop_eval\<^sub>w mds\<^sub>C'_def)
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_then_rel_2'(1-6)
    have c\<^sub>2\<^sub>C_else_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = Stop ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: If_Else_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover have "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A"
      from in_else c\<^sub>2\<^sub>A_def have
        c\<^sub>2\<^sub>A_else_def: "c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
        by clarsimp
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_else_def if_then_rel_2'.hyps(4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C \<and>
           (\<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        using eval_else_tail\<^sub>C by (blast elim: If_Else_RefRel_HighBranchE)
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C" by simp
      ultimately show ?thesis using eval_else_tail\<^sub>C by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_then_rel_2'(3) rel_inv\<^sub>C_5 by simp

    moreover note eval_then_tail\<^sub>C eval_else_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_then_rel_2'.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (if_else_rel_2' c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_else_rel_2'.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_else_rel_2'.prems if_else_rel_2'(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = tail\<^sub>C" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    using C.seq_stop_elim by blast+
  from if_else_rel_2'(1-5) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using A.neval.neval_0 by simp+
  with if_else_rel_2' c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    by blast
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?tail\<^sub>2\<^sub>C = "(reg0 \<leftarrow> Load y_mem) ;; (x_mem \<leftarrow> Load reg0)"
    from in_rel_inv\<^sub>C if_else_rel_2'(2-3)
    have "c\<^sub>2\<^sub>C = c\<^sub>C \<or>
          c\<^sub>2\<^sub>C = Stop ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    moreover from in_R if_else_rel_2'(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
      using neval\<^sub>2\<^sub>A abs_steps_this A.neval_ZeroE
      by (clarsimp, blast)+

    (* c\<^sub>2\<^sub>C is in the other, 'then' branch *)
    moreover have eval_then_tail\<^sub>C: "(\<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_else_rel_2'(2,3) c\<^sub>1\<^sub>C'_def C.seq_stop_eval\<^sub>w by blast
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_else_rel_2'(1-6)
    have c\<^sub>2\<^sub>C_then_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = Stop ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: If_Then_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover with c\<^sub>2\<^sub>A_def
    have c\<^sub>2\<^sub>A_then_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
      by clarsimp
    moreover have "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A"
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_then_def if_else_rel_2'.hyps(4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C \<and>
           (\<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        by (blast elim: If_Then_RefRel_HighBranchE)
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
        by simp
      ultimately show ?thesis
        using eval_then_tail\<^sub>C by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_else_rel_2'(2,3) rel_inv\<^sub>C_5' mem\<^sub>1\<^sub>C'_def mds\<^sub>C'_def by simp

    (* c\<^sub>2\<^sub>C is also in the 'else' branch *)
    moreover have eval_else_tail\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp del:fun_upd_apply add:C.seq_stop_eval\<^sub>w mds\<^sub>C'_def c\<^sub>1\<^sub>C'_def if_else_rel_2'(2,3))
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_else_rel_2'(1-6)
    have c\<^sub>2\<^sub>C_else_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: If_Else_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover have "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A = c\<^sub>A"
      from in_else c\<^sub>2\<^sub>A_def if_else_rel_2'(1) have
        c\<^sub>2\<^sub>A_else_def: "c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
        by clarsimp
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_else_def if_else_rel_2'.hyps(1-4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>1\<^sub>C'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C \<and>
           (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        using eval_else_tail\<^sub>C by (blast elim: If_Else_RefRel_HighBranchE)
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C" by simp
      ultimately show ?thesis using eval_else_tail\<^sub>C by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp

    moreover note eval_then_tail\<^sub>C eval_else_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_else_rel_2'.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (if_then_rel_3 c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_then_rel_3.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_then_rel_3.prems if_then_rel_3(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (Stop ;; tail\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C(reg0 := mem\<^sub>C y_mem)"
    using C.seq_elim C.assign_elim assign_eval\<^sub>w_load\<^sub>C
    by (metis (no_types, lifting) Stmt.distinct(13))+
  from if_then_rel_3(1-5) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using A.neval.neval_0 conc_only_var_assign_not_visible_abs reg_not_visible_abs by simp+
  with if_then_rel_3 c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    apply clarsimp
    apply(erule_tac x=mem\<^sub>A in allE)
    apply(erule_tac x=mds\<^sub>C in allE)
    apply(erule_tac x=mem\<^sub>1\<^sub>C' in allE)
    apply(erule_tac impE)
     apply(rule_tac x=mem\<^sub>C in exI)
     apply(rule conjI)
      apply(clarsimp)
     apply(rule conjI)
      apply clarsimp
      apply (simp add: mem\<^sub>A_of_def)
     using if_then_rel_3.prems mem\<^sub>A_of_def apply blast
    apply clarsimp
    done
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?mem\<^sub>2\<^sub>C'_t = "mem\<^sub>2\<^sub>C(reg0 := mem\<^sub>2\<^sub>C y_mem)"
    let ?mem\<^sub>2\<^sub>C'_e = "mem\<^sub>2\<^sub>C(reg0 := ev\<^sub>A mem\<^sub>2\<^sub>C (Add (Load reg1) (Load reg2)))"
    let ?tail\<^sub>2\<^sub>C = "x_mem \<leftarrow> Load reg0"
    from in_rel_inv\<^sub>C if_then_rel_3(2-3)
    have "c\<^sub>2\<^sub>C = c\<^sub>C \<or> c\<^sub>2\<^sub>C = (reg0 \<leftarrow> Add (Load reg1) (Load reg2)) ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    moreover from in_R if_then_rel_3(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
      using neval\<^sub>2\<^sub>A abs_steps_this A.neval_ZeroE
      by (clarsimp, blast)+

    (* c\<^sub>2\<^sub>C is also in the 'then' branch *)
    moreover have eval_then_tail\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_t\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_then_rel_3(2,3) c\<^sub>1\<^sub>C'_def C.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>C by simp
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_then_rel_3(1-6)
    have c\<^sub>2\<^sub>C_then_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: If_Then_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover have "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_t\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_then: "c\<^sub>2\<^sub>A = c\<^sub>A"
      from in_then c\<^sub>2\<^sub>A_def if_then_rel_3(1) have
        c\<^sub>2\<^sub>A_then_def: "c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
        by clarsimp
      with in_then in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_then_def if_then_rel_3.hyps(2-4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'_t \<and>
           (\<langle>(reg0 \<leftarrow> Load y_mem) ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_t\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_t\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        apply clarsimp
        apply(erule If_Then_RefRel_HighBranchE, simp+)
        apply(erule_tac x="mem\<^sub>A_of mem\<^sub>C''" in allE)
        apply(erule_tac x="mds\<^sub>C" in allE)
        apply(erule_tac x="mem\<^sub>2\<^sub>C(reg0 := mem\<^sub>2\<^sub>C y_mem)" in allE)
        using conc_only_var_assign_not_visible_abs reg_not_visible_abs mem\<^sub>A_of_def by auto
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'_t" by simp
      moreover note c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def if_then_rel_3(1-3) c\<^sub>1\<^sub>C'_def
      ultimately show ?thesis
        using conc_only_var_assign_not_visible_abs eval_then_tail\<^sub>C reg_not_visible_abs by fast
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_t\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp

    (* c\<^sub>2\<^sub>C is in the other, 'else' branch *)
    moreover have eval_else_tail\<^sub>C: "(\<langle>(reg0 \<leftarrow> Add (Load reg1) (Load reg2)) ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_e\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using C.eval\<^sub>w.seq C.assign_eval\<^sub>w' ev\<^sub>A.simps mds\<^sub>C'_def by blast
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_then_rel_3(1-6)
    have c\<^sub>2\<^sub>C_else_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = (reg0 \<leftarrow> Add (Load reg1) (Load reg2)) ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: If_Else_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_then_rel_3(1-8) c\<^sub>1\<^sub>C'_def
    have "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_e\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A"
      from in_else c\<^sub>2\<^sub>A_def have
        c\<^sub>2\<^sub>A_else_def: "c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
        by clarsimp
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_else_def if_then_rel_3.hyps(4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'_e \<and>
           (\<langle>(reg0 \<leftarrow> Add (Load reg1) (Load reg2)) ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_e\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_e\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        apply clarsimp
        apply(erule If_Else_RefRel_HighBranchE, simp+)
        apply(erule_tac x="mem\<^sub>A_of mem\<^sub>C''" in allE)
        apply(erule_tac x="mds\<^sub>C" in allE)
        apply(erule_tac x="?mem\<^sub>2\<^sub>C'_e" in allE)
        using conc_only_var_assign_not_visible_abs reg_not_visible_abs eval_else_tail\<^sub>C mem\<^sub>A_of_def by auto
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'_e" by simp
      ultimately show ?thesis
        using conc_only_var_assign_not_visible_abs eval_else_tail\<^sub>C reg_not_visible_abs by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_e\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_then_rel_3(3) rel_inv\<^sub>C_default by clarsimp

    moreover note eval_then_tail\<^sub>C eval_else_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_then_rel_3.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (if_else_rel_3 c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_else_rel_3.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_else_rel_3.prems if_else_rel_3(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (Stop ;; tail\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C(reg0 := ev\<^sub>A mem\<^sub>C (Add (Load reg1) (Load reg2)))"
    using C.seq_elim C.assign_elim assign_eval\<^sub>w_load\<^sub>C
    by (metis (no_types, lifting) Stmt.distinct(13))+
  from if_else_rel_3(1-5) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using A.neval.neval_0 conc_only_var_assign_not_visible_abs reg_not_visible_abs by simp+
  with if_else_rel_3 c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    apply clarsimp
    apply(erule_tac x=mem\<^sub>A in allE)
    apply(erule_tac x=mds\<^sub>C in allE)
    apply(erule_tac x=mem\<^sub>1\<^sub>C' in allE)
    apply(erule_tac impE)
     apply(rule_tac x=mem\<^sub>C in exI)
     apply(rule conjI)
      apply(clarsimp)
     apply(rule conjI)
      apply clarsimp
      apply (simp add: mem\<^sub>A_of_def)
     using if_else_rel_3.prems mem\<^sub>A_of_def apply blast
    apply clarsimp
    done
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?mem\<^sub>2\<^sub>C'_t = "mem\<^sub>2\<^sub>C(reg0 := mem\<^sub>2\<^sub>C y_mem)"
    let ?mem\<^sub>2\<^sub>C'_e = "mem\<^sub>2\<^sub>C(reg0 := ev\<^sub>A mem\<^sub>2\<^sub>C (Add (Load reg1) (Load reg2)))"
    let ?tail\<^sub>2\<^sub>C = "x_mem \<leftarrow> Load reg0"
    from in_rel_inv\<^sub>C if_else_rel_3(2-3)
    have "c\<^sub>2\<^sub>C = c\<^sub>C \<or>
          c\<^sub>2\<^sub>C = (reg0 \<leftarrow> Load y_mem) ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    moreover from in_R if_else_rel_3(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
      using neval\<^sub>2\<^sub>A abs_steps_this A.neval_ZeroE
      by (clarsimp, blast)+

    (* c\<^sub>2\<^sub>C is in the other, 'then' branch *)
    moreover have eval_then_tail\<^sub>C: "(\<langle>(reg0 \<leftarrow> Load y_mem) ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_t\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_else_rel_3(2,3) C.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>C by simp
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_else_rel_3(1-6)
    have c\<^sub>2\<^sub>C_then_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = (reg0 \<leftarrow> Load y_mem) ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: If_Then_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover with c\<^sub>2\<^sub>A_def
    have c\<^sub>2\<^sub>A_then_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
      by clarsimp
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_else_rel_3(1-8) c\<^sub>1\<^sub>C'_def c\<^sub>2\<^sub>A_then_def
    have "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_t\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_then: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A"
      with c\<^sub>2\<^sub>A_then_def in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_then_def if_else_rel_3.hyps(4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'_t \<and>
           (\<langle>(reg0 \<leftarrow> Load y_mem) ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_t\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_t\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        apply clarsimp
        apply(erule If_Then_RefRel_HighBranchE, simp+)
        apply(erule_tac x="mem\<^sub>A_of mem\<^sub>C''" in allE)
        apply(erule_tac x="mds\<^sub>C" in allE)
        apply(erule_tac x="?mem\<^sub>2\<^sub>C'_t" in allE)
        using conc_only_var_assign_not_visible_abs reg_not_visible_abs mem\<^sub>A_of_def by auto
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'_t" by simp
      ultimately show ?thesis
        using conc_only_var_assign_not_visible_abs eval_then_tail\<^sub>C reg_not_visible_abs by fast
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_t\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_else_rel_3(2,3) rel_inv\<^sub>C_default mem\<^sub>1\<^sub>C'_def mds\<^sub>C'_def by simp

    (* c\<^sub>2\<^sub>C is also in the 'else' branch *)
    moreover have eval_else_tail\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_e\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using C.eval\<^sub>w.seq C.assign_eval\<^sub>w' ev\<^sub>A.simps mds\<^sub>C'_def c\<^sub>1\<^sub>C'_def if_else_rel_3(2,3) by blast
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_else_rel_3(1-6)
    have c\<^sub>2\<^sub>C_else_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: If_Else_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_else_rel_3(1-8) c\<^sub>1\<^sub>C'_def
    have "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_e\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A = c\<^sub>A"
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_else_def if_else_rel_3.hyps(1-4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>1\<^sub>C'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'_e \<and>
           (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_e\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_e\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        apply clarsimp
        apply(erule If_Else_RefRel_HighBranchE, simp+)
        apply(erule_tac x="mem\<^sub>A_of mem\<^sub>C''" in allE)
        apply(erule_tac x="mds\<^sub>C" in allE)
        apply(erule_tac x="?mem\<^sub>2\<^sub>C'_e" in allE)
        using conc_only_var_assign_not_visible_abs reg_not_visible_abs mem\<^sub>A_of_def eval_else_tail\<^sub>C by auto
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'_e"
        by simp
      ultimately show ?thesis
        using conc_only_var_assign_not_visible_abs eval_else_tail\<^sub>C reg_not_visible_abs by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'_e\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp

    moreover note eval_then_tail\<^sub>C eval_else_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_else_rel_3.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (if_then_rel_3' c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_then_rel_3'.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_then_rel_3'.prems if_then_rel_3'(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = tail\<^sub>C" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    using C.seq_stop_elim by blast+
  from if_then_rel_3'(1-5) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using A.neval.intros(1) by auto
  with if_then_rel_3' c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    by blast
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?tail\<^sub>2\<^sub>C = "x_mem \<leftarrow> Load reg0"
    from in_rel_inv\<^sub>C if_then_rel_3'(2-3)
    have "c\<^sub>2\<^sub>C = c\<^sub>C \<or>
          c\<^sub>2\<^sub>C = Stop ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    moreover from in_R if_then_rel_3'(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
      using neval\<^sub>2\<^sub>A abs_steps_this A.neval_ZeroE
      by (clarsimp, blast)+

    (* c\<^sub>2\<^sub>C is also in the 'then' branch *)
    moreover have eval_then_tail\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_then_rel_3'(2,3) c\<^sub>1\<^sub>C'_def C.seq_stop_eval\<^sub>w by blast
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_then_rel_3'(1-6)
    have c\<^sub>2\<^sub>C_then_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: If_Then_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_then_rel_3'(1-8) c\<^sub>1\<^sub>C'_def
    have "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_then: "c\<^sub>2\<^sub>A = c\<^sub>A"
      from in_then c\<^sub>2\<^sub>A_def if_then_rel_3'(1) have
        c\<^sub>2\<^sub>A_then_def: "c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
        by clarsimp
      with in_then in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_then_def if_then_rel_3'.hyps(2-4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>1\<^sub>C'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C \<and>
           (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        using eval_then_tail\<^sub>C by (blast elim: If_Then_RefRel_HighBranchE)
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C" by simp
      moreover note c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def if_then_rel_3'(1-3) c\<^sub>1\<^sub>C'_def
      ultimately show ?thesis using eval_then_tail\<^sub>C by fast
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp

    (* c\<^sub>2\<^sub>C is in the other, 'else' branch *)
    moreover have eval_else_tail\<^sub>C: "(\<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp del:fun_upd_apply add:C.seq_stop_eval\<^sub>w mds\<^sub>C'_def)
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_then_rel_3'(1-6)
    have c\<^sub>2\<^sub>C_else_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = Stop ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: If_Else_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_then_rel_3'(1-8) c\<^sub>1\<^sub>C'_def
    have "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A"
      from in_else c\<^sub>2\<^sub>A_def have
        c\<^sub>2\<^sub>A_else_def: "c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
        by clarsimp
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_else_def if_then_rel_3'.hyps(4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C \<and>
           (\<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        using eval_else_tail\<^sub>C by (blast elim: If_Else_RefRel_HighBranchE)
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C" by simp
      ultimately show ?thesis using eval_else_tail\<^sub>C by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_then_rel_3'(3) rel_inv\<^sub>C_default by simp

    moreover note eval_then_tail\<^sub>C eval_else_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_then_rel_3'.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (if_else_rel_3' c\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_else_rel_3'.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_else_rel_3'.prems if_else_rel_3'(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = tail\<^sub>C" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    using C.seq_stop_elim by blast+
  from if_else_rel_3'(1-5) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using A.neval.neval_0 by simp+
  with if_else_rel_3' c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    by blast
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           neval\<^sub>2\<^sub>A: "A.neval \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 0 \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A"
    let ?tail\<^sub>2\<^sub>C = "x_mem \<leftarrow> Load reg0"
    from in_rel_inv\<^sub>C if_else_rel_3'(2-3)
    have "c\<^sub>2\<^sub>C = c\<^sub>C \<or>
          c\<^sub>2\<^sub>C = Stop ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    moreover from in_R if_else_rel_3'(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
      by (blast elim: inR_E A.rel_invE)
    moreover hence
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = c\<^sub>2\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
      using neval\<^sub>2\<^sub>A abs_steps_this A.neval_ZeroE
      by (clarsimp, blast)+

    (* c\<^sub>2\<^sub>C is in the other, 'then' branch *)
    moreover have eval_then_tail\<^sub>C: "(\<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_else_rel_3'(2,3) c\<^sub>1\<^sub>C'_def C.seq_stop_eval\<^sub>w by blast
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_else_rel_3'(1-6)
    have c\<^sub>2\<^sub>C_then_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = Stop ;; ?tail\<^sub>2\<^sub>C"
      by (blast elim: If_Then_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover with c\<^sub>2\<^sub>A_def
    have c\<^sub>2\<^sub>A_then_def: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
      by clarsimp
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_else_rel_3'(1-8) c\<^sub>1\<^sub>C'_def c\<^sub>2\<^sub>A_then_def
    have "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A \<noteq> c\<^sub>A"
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_then_def if_else_rel_3'.hyps(4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C \<and>
           (\<langle>Stop ;; ?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        using eval_then_tail\<^sub>C by (blast elim: If_Then_RefRel_HighBranchE)
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
        by simp
      ultimately show ?thesis
        using eval_then_tail\<^sub>C by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>?tail\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_else_rel_3'(2,3) rel_inv\<^sub>C_default mem\<^sub>1\<^sub>C'_def mds\<^sub>C'_def by simp

    (* c\<^sub>2\<^sub>C is also in the 'else' branch *)
    moreover have eval_else_tail\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp del:fun_upd_apply add:C.seq_stop_eval\<^sub>w mds\<^sub>C'_def c\<^sub>1\<^sub>C'_def if_else_rel_3'(2,3))
    moreover from c\<^sub>2\<^sub>A_def in_Rel in_rel_inv\<^sub>C if_else_rel_3'(1-6)
    have c\<^sub>2\<^sub>C_else_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: If_Else_RefRel_HighBranchE rel_inv\<^sub>CE)
    moreover have "c\<^sub>2\<^sub>A = c\<^sub>A \<Longrightarrow> (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    proof -
      assume in_else: "c\<^sub>2\<^sub>A = c\<^sub>A"
      from in_else c\<^sub>2\<^sub>A_def if_else_rel_3'(1) have
        c\<^sub>2\<^sub>A_else_def: "c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
        by clarsimp
      with in_else in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_else_def if_else_rel_3'.hyps(1-4) c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>1\<^sub>C'_def
      have "(\<exists>mem\<^sub>C''.
           mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C \<and>
           (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
            \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w) \<longrightarrow>
             (\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
        using eval_else_tail\<^sub>C by (blast elim: If_Else_RefRel_HighBranchE)
      moreover obtain mem\<^sub>C'' where "mem\<^sub>A_of mem\<^sub>C'' = mem\<^sub>A_of mem\<^sub>2\<^sub>C" by simp
      ultimately show ?thesis using eval_else_tail\<^sub>C by auto
    qed
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp

    moreover note eval_then_tail\<^sub>C eval_else_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_else_rel_3'.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (if_then_rel_4 c\<^sub>A c\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "Stop"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_then_rel_4.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 1"
    by (simp add:abs_steps'_def)
  from if_then_rel_4.prems if_then_rel_4(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = Stop" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C(x_mem := mem\<^sub>C reg0)"
    using C.assign_elim assign_eval\<^sub>w_load\<^sub>C
    by metis+
  from if_then_rel_4(1-7) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have eval\<^sub>A: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A,\<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w" and
    neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 1 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A"
    using A.assign_eval\<^sub>w' ev\<^sub>A.simps(2) mem_assign_refinement_helper_const var\<^sub>C_of.simps(2) abs_steps_this
    by (metis, simp, metis)
  with if_then_rel_4 c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    by blast
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 1
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           eval\<^sub>2\<^sub>A: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
    let ?mem\<^sub>2\<^sub>C' = "mem\<^sub>2\<^sub>C(x_mem := mem\<^sub>2\<^sub>C reg0)"
    from in_rel_inv\<^sub>C if_then_rel_4(2-3)
    have c\<^sub>2\<^sub>C_def: "c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    from in_rel_inv\<^sub>C if_then_rel_4(1-4,6) in_R
    have z\<^sub>A: "mem\<^sub>A z_var = 0"
      using A.prog_high_branch_def inR_E inv\<^sub>5E
      by (metis if_then_rel_4.hyps(6))
    from in_rel_inv\<^sub>C if_then_rel_4(1-4) in_R
    have "mem\<^sub>A z_var = mem\<^sub>A_of mem\<^sub>2\<^sub>C z_var"
      using inR_E A.low_mds_eq_def dma_def emptyE inv\<^sub>5E var.distinct(5)
      by (metis (mono_tags, hide_lams))
    with z\<^sub>A have z\<^sub>2\<^sub>A: "mem\<^sub>A_of mem\<^sub>2\<^sub>C z_var = 0"
      by simp

    moreover from in_R if_then_rel_4(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Add (Load y_var) (Load z_var)"
      by (blast elim: inR_E A.rel_invE)

    from in_Rel c\<^sub>2\<^sub>C_def if_then_rel_4(1,2,3) in_rel_inv\<^sub>C c\<^sub>2\<^sub>A_def z\<^sub>2\<^sub>A
    have r0y: "mem\<^sub>2\<^sub>C reg0 = mem\<^sub>2\<^sub>C y_mem"
      apply clarsimp
      apply(case_tac "c\<^sub>A = c\<^sub>2\<^sub>A")
       apply clarsimp
       apply(erule If_Then_RefRel_HighBranchE, simp+)
       using mem\<^sub>A_of_def apply force
      apply clarsimp
      apply(erule If_Else_RefRel_HighBranchE, simp+)
      using mem\<^sub>A_of_def by force

    moreover from c\<^sub>2\<^sub>A_def have
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = Stop"
      using eval\<^sub>2\<^sub>A A.assign_elim if_then_rel_4(1)
      by (case_tac "c\<^sub>A = c\<^sub>2\<^sub>A", clarsimp+)

    moreover with c\<^sub>2\<^sub>A_def if_then_rel_4(1-7) have
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'"
      using eval\<^sub>2\<^sub>A c\<^sub>2\<^sub>A_def mds\<^sub>C'_def
      apply clarsimp
      apply(case_tac "c\<^sub>A = c\<^sub>2\<^sub>A")
       apply clarsimp
       apply(drule A.assign_elim)
       apply clarsimp
       using r0y apply clarsimp
       using mem\<^sub>A_of_def
       apply (metis mem_assign_refinement_helper_const var\<^sub>C_of.simps(2) var\<^sub>C_of.simps(3))
      apply clarsimp
      apply(drule A.assign_elim)
      apply clarsimp
      using r0y z\<^sub>2\<^sub>A apply clarsimp
      using mem\<^sub>A_of_def 
      apply (metis mem_assign_refinement_helper_const var\<^sub>C_of.simps(2) var\<^sub>C_of.simps(3))
      done

    moreover have eval_tail\<^sub>C: "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_then_rel_4(2,3) c\<^sub>2\<^sub>C_def c\<^sub>1\<^sub>C'_def C.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>C by simp
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_then_rel_4(1-8) c\<^sub>1\<^sub>C'_def
    have "(\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
      by (meson RefRel_HighBranch.stop_rel)
    (* c\<^sub>2\<^sub>C is also in the 'then' branch *)
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp
    (* c\<^sub>2\<^sub>C is in the other, 'else' branch *)
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>Stop, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_then_rel_4(3) rel_inv\<^sub>C_default by clarsimp
    moreover note eval_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_then_rel_4.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (if_else_rel_4 c\<^sub>A c\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "Stop"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_else_rel_4.hyps(1-3)
  have abs_steps_this: "(abs_steps' c\<^sub>A c\<^sub>C) = 1"
    by (simp add:abs_steps'_def)
  from if_else_rel_4.prems if_else_rel_4(2,3)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = Stop" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C(x_mem := mem\<^sub>C reg0)"
    using C.assign_elim assign_eval\<^sub>w_load\<^sub>C
    by metis+
  from if_else_rel_4(1-8) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have eval\<^sub>A: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A,\<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w" and
    neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 1 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A"
    using A.assign_eval\<^sub>w' ev\<^sub>A.simps(2) mem_assign_refinement_helper_const var\<^sub>C_of.simps(2) abs_steps_this
    by (metis, simp, metis)
  with if_else_rel_4 c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    by blast
  have
    "(\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 1
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C))"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           eval\<^sub>2\<^sub>A: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
    let ?mem\<^sub>2\<^sub>C' = "mem\<^sub>2\<^sub>C(x_mem := mem\<^sub>2\<^sub>C reg0)"
    from in_rel_inv\<^sub>C if_else_rel_4(2-3)
    have c\<^sub>2\<^sub>C_def: "c\<^sub>2\<^sub>C = c\<^sub>C"
      by (blast elim: rel_inv\<^sub>CE)
    from in_rel_inv\<^sub>C if_else_rel_4(1-4,6) in_R
    have z\<^sub>A: "mem\<^sub>A z_var = 0"
      using A.prog_high_branch_def inR_E inv\<^sub>6E
      by (metis if_else_rel_4.hyps(6))
    from in_rel_inv\<^sub>C if_else_rel_4(1-4) in_R
    have "mem\<^sub>A z_var = mem\<^sub>A_of mem\<^sub>2\<^sub>C z_var"
      using inR_E A.low_mds_eq_def dma_def emptyE inv\<^sub>6E var.distinct(5)
      by (metis (mono_tags, hide_lams))
    with z\<^sub>A have z\<^sub>2\<^sub>A: "mem\<^sub>A_of mem\<^sub>2\<^sub>C z_var = 0"
      by simp

    moreover from in_R if_else_rel_4(1) inR_E A.rel_invE have
      c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = c\<^sub>A \<or> c\<^sub>2\<^sub>A = x_var \<leftarrow> Load y_var"
      by (blast elim: inR_E A.rel_invE)

    from in_Rel c\<^sub>2\<^sub>C_def if_else_rel_4(1,2,3) in_rel_inv\<^sub>C c\<^sub>2\<^sub>A_def z\<^sub>2\<^sub>A
    have r0y: "mem\<^sub>2\<^sub>C reg0 = mem\<^sub>2\<^sub>C y_mem"
      apply clarsimp
      apply(case_tac "c\<^sub>A = c\<^sub>2\<^sub>A")
       apply clarsimp
       apply(erule If_Else_RefRel_HighBranchE, simp+)
       using mem\<^sub>A_of_def apply force
      apply clarsimp
      apply(erule If_Then_RefRel_HighBranchE, simp+)
      using mem\<^sub>A_of_def by force

    moreover from c\<^sub>2\<^sub>A_def have
      c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = Stop"
      using eval\<^sub>2\<^sub>A A.assign_elim if_else_rel_4(1)
      by (case_tac "c\<^sub>A = c\<^sub>2\<^sub>A", clarsimp+)

    moreover with c\<^sub>2\<^sub>A_def if_else_rel_4(1-7) have
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of ?mem\<^sub>2\<^sub>C'"
      using eval\<^sub>2\<^sub>A c\<^sub>2\<^sub>A_def mds\<^sub>C'_def
      apply clarsimp
      apply(case_tac "c\<^sub>A \<noteq> c\<^sub>2\<^sub>A")
       apply clarsimp
       apply(drule A.assign_elim)
       apply clarsimp
       using r0y apply clarsimp
       using mem\<^sub>A_of_def
       apply (metis mem_assign_refinement_helper_const var\<^sub>C_of.simps(2) var\<^sub>C_of.simps(3))
      apply clarsimp
      apply(drule A.assign_elim)
      apply clarsimp
      using r0y z\<^sub>2\<^sub>A apply clarsimp
      using mem\<^sub>A_of_def 
      apply (metis mem_assign_refinement_helper_const var\<^sub>C_of.simps(2) var\<^sub>C_of.simps(3))
      done

    moreover have eval_tail\<^sub>C: "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      using if_else_rel_4(2,3) c\<^sub>2\<^sub>C_def c\<^sub>1\<^sub>C'_def C.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>C by simp
    moreover from c\<^sub>2\<^sub>A'_def mem\<^sub>2\<^sub>A'_def c\<^sub>2\<^sub>A_def if_else_rel_4(1-8) c\<^sub>1\<^sub>C'_def
    have "(\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A, mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
      by (meson RefRel_HighBranch.stop_rel)
    (* c\<^sub>2\<^sub>C is also in the 'then' branch *)
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def rel_inv\<^sub>C_default by simp
    (* c\<^sub>2\<^sub>C is in the other, 'else' branch *)
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>Stop, mds\<^sub>C, ?mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def if_else_rel_4(3) rel_inv\<^sub>C_default by clarsimp
    moreover note eval_tail\<^sub>C c\<^sub>2\<^sub>A'_def
    ultimately show "(\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
      using mds\<^sub>C'_def if_else_rel_4.hyps(1-6) by blast
  qed
  thus ?case using rel' abs_steps_this neval\<^sub>A by blast
next
case (stop_seq_rel c\<^sub>A tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "tail\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from stop_seq_rel(1,2)
  have abs_steps_stop: "(abs_steps' c\<^sub>A c\<^sub>C) = 1"
    by (simp add:abs_steps'_def)
  from stop_seq_rel
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = tail\<^sub>C" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    using C.seq_stop_elim by auto
  hence neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 1 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    rel': "(\<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
    using stop_seq_rel A.seq_stop_eval\<^sub>w by auto
  have "\<forall>c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'.
                  (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R \<and>
                  (\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C)
                  \<in> RefRel_HighBranch \<and>
                  (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C \<and>
                  A.neval
                   \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, sifum_refinement.mem\<^sub>A_of var\<^sub>C_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A 1
                   \<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A \<longrightarrow>
                  (\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
                      (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
                      (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
                      \<in> RefRel_HighBranch \<and>
                      (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C)"
  proof(clarsimp)
    fix c\<^sub>2\<^sub>A c\<^sub>2\<^sub>C mem\<^sub>2\<^sub>C c\<^sub>2\<^sub>A' mem\<^sub>2\<^sub>A'
    assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A) \<in> A.R" and
           in_Rel: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch" and
           in_rel_inv\<^sub>C: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C" and
           eval\<^sub>2\<^sub>A: "(\<langle>c\<^sub>2\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>2\<^sub>C\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
    from in_rel_inv\<^sub>C stop_seq_rel(2) obtain tail\<^sub>C' where c\<^sub>2\<^sub>C_def:
      "c\<^sub>2\<^sub>C = Stop ;; tail\<^sub>C'"
      by (blast elim:rel_inv\<^sub>CE)
    hence eval_tail\<^sub>C': "(\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>tail\<^sub>C', mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (blast intro:C.seq_stop_eval\<^sub>w)
    moreover from stop_seq_rel(1) in_R inR_E
    have c\<^sub>2\<^sub>A_def: "c\<^sub>2\<^sub>A = Stop ;; tail\<^sub>A"
      by (blast elim: inR_E A.rel_invE)
    moreover from c\<^sub>2\<^sub>A_def
    have c\<^sub>2\<^sub>A'_def: "c\<^sub>2\<^sub>A' = tail\<^sub>A" and
      mem\<^sub>2\<^sub>A'_def: "mem\<^sub>2\<^sub>A' = mem\<^sub>A_of mem\<^sub>2\<^sub>C"
    using eval\<^sub>2\<^sub>A abs_steps_stop A.seq_stop_elim
      by simp+
    moreover with c\<^sub>2\<^sub>C_def have
      "(\<langle>c\<^sub>2\<^sub>A', mds\<^sub>A_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>tail\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
      using in_Rel c\<^sub>2\<^sub>A_def c\<^sub>2\<^sub>C_def mds\<^sub>C'_def Stop_tail_RefRel_HighBranchE C.seq_stop_eval\<^sub>w
      by blast
    moreover have "(\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>tail\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using c\<^sub>1\<^sub>C'_def in_rel_inv\<^sub>C stop_seq_rel(2) c\<^sub>2\<^sub>C_def
      by (blast elim:rel_inv\<^sub>CE intro:rel_inv\<^sub>C.intros)
    ultimately show "\<exists>c\<^sub>2\<^sub>C' mem\<^sub>2\<^sub>C'.
              (\<langle>c\<^sub>2\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<and>
              (\<langle>c\<^sub>2\<^sub>A', sifum_refinement.mds\<^sub>A_of var\<^sub>C_of mds\<^sub>C', mem\<^sub>2\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C)
              \<in> RefRel_HighBranch \<and>
              (\<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> rel_inv\<^sub>C"
      using mds\<^sub>C'_def by blast
  qed
  thus ?case using rel' abs_steps_stop neval\<^sub>A by blast
next
case stop_rel
  with C.stop_no_eval have False by simp
  thus ?case by simp
qed

lemma RefRel_HighBranch_secure_refinement:
  "secure_refinement A.R RefRel_HighBranch rel_inv\<^sub>C"
  apply(unfold secure_refinement_def2)
  apply(rule conjI)
   apply(rule closed_others_RefRel_HighBranch)
  apply(rule conjI)
   apply(rule preserves_modes_mem_RefRel_HighBranch)
  apply(rule conjI)
   apply(rule new_vars_private_RefRel_HighBranch)
  apply(rule conjI)
   apply(rule rel_inv\<^sub>C_closed_glob_consistent)
  apply clarsimp
  apply(rule induction_full_RefRel_HighBranch, simp+)
  done

lemma strong_low_bisim_mm_R\<^sub>C_of_R:
  "C.strong_low_bisim_mm (R\<^sub>C_of A.R RefRel_HighBranch rel_inv\<^sub>C)"
  apply(rule R\<^sub>C_of_strong_low_bisim_mm)
    apply(rule A.strong_low_bisim_mm_R)
   apply(rule RefRel_HighBranch_secure_refinement)
  apply(rule rel_inv\<^sub>C_sym)
  done

definition
  mds\<^sub>0 :: "Mode \<Rightarrow> var\<^sub>C set"
where
  "mds\<^sub>0 \<equiv> \<lambda>m. case m of AsmNoReadOrWrite \<Rightarrow> {reg0, reg1, reg2, reg3} |
                        AsmNoWrite \<Rightarrow> {} |
                        _ \<Rightarrow> {}"

lemma regs_the_only_concrete_only_vars:
  "v\<^sub>C \<notin> range var\<^sub>C_of \<Longrightarrow> v\<^sub>C \<in> {reg0, reg1, reg2, reg3}"
  by (case_tac v\<^sub>C, (clarsimp|metis rangeI var\<^sub>C_of.simps)+)

lemma prog_high_branch_RefRel:
  "(\<langle>A.prog_high_branch, mds\<^sub>A_of mds\<^sub>0, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A, \<langle>C.prog_high_branch\<^sub>C, mds\<^sub>0, mem\<^sub>C\<rangle>\<^sub>C) \<in> RefRel_HighBranch"
  unfolding A.prog_high_branch_def C.prog_high_branch\<^sub>C_def mds\<^sub>0_def
  using regs_the_only_concrete_only_vars doesnt_have_mode has_mode\<^sub>A NoRW\<^sub>A_implies_NoRW\<^sub>C
  apply clarsimp

  apply(rule acq_mode_rel, (simp|clarsimp)+)
  apply(drule C.seq_decl_elim, clarsimp)
  apply(rule stop_seq_rel, simp+)

  apply(rule acq_mode_rel, (simp|clarsimp)+)
  apply(drule C.seq_decl_elim, clarsimp)
  apply(rule stop_seq_rel, simp+)

  apply(rule acq_mode_rel, (simp|clarsimp)+)
  apply(drule C.seq_decl_elim, clarsimp)
  apply(rule stop_seq_rel, simp+)

  apply(rule assign_const_rel, (simp|clarsimp)+)
  apply(drule C.seq_assign_elim, clarsimp)
  apply(rule stop_seq_rel, simp+)
  
  apply(rule assign_const_rel, (simp|clarsimp)+)
  apply(drule C.seq_assign_elim, clarsimp)
  apply(rule stop_seq_rel, simp+)

  apply(rule assign_load_rel, (simp|clarsimp)+)
  apply(drule C.seq_assign_elim, clarsimp)
  apply(rule stop_seq_rel, simp+)

  apply(rule if_reg_load_rel, (simp|clarsimp)+)
  apply(drule C.seq_assign_elim, clarsimp)
  apply(rule if_reg_stop_rel, (simp|clarsimp)+)

  apply(drule C.seq_stop_elim, clarsimp)

  apply(rule if_reg_rel, (simp|clarsimp)+)
   apply(rule rel_inv\<^sub>C_1, clarsimp+)
  apply(rule conjI)

   (* Then *)
   apply clarsimp
   apply(rule if_then_rel_1, (simp|clarsimp)+)
   apply(drule C.if_elim, simp+)
   apply(drule C.seq_elim, simp+)
   apply(drule C.skip_elim, simp+)
   apply(rule if_then_rel_1', (simp|clarsimp)+)
   apply(drule C.seq_stop_elim, simp+)
   apply(rule if_then_rel_2, (simp|clarsimp)+)
   apply(drule C.seq_elim, simp+)
   apply(drule C.skip_elim, simp+)
   apply(rule if_then_rel_2', (simp|clarsimp)+)
   apply(drule C.seq_stop_elim, simp+)
   apply(rule if_then_rel_3, (simp|clarsimp)+)
   apply(drule C.seq_assign_elim, simp+)
   apply(rule if_then_rel_3', (simp|clarsimp)+)
   apply(drule C.seq_stop_elim, simp+)
   apply(rule if_then_rel_4, (simp|clarsimp)+)
   apply(drule C.assign_elim, simp+)
   apply(rule stop_rel)

  (* Else *)
  apply clarsimp
  apply(rule if_else_rel_1, (simp|clarsimp)+)
  apply(drule C.if_elim, simp+)
  apply(drule C.seq_assign_elim, simp+)
  apply(rule if_else_rel_1', (simp|clarsimp)+)
  apply(drule C.seq_stop_elim, simp+)
  apply(rule if_else_rel_2, (simp|clarsimp)+)
  apply(drule C.seq_assign_elim, simp+)
  apply(rule if_else_rel_2', (simp|clarsimp)+)
  apply(drule C.seq_stop_elim, simp+)
  apply(rule if_else_rel_3, (simp|clarsimp)+)
  apply(drule C.seq_assign_elim, simp+)
  apply(rule if_else_rel_3', (simp|clarsimp)+)
  apply(drule C.seq_stop_elim, simp+)
  apply(rule if_else_rel_4, (simp|clarsimp)+)
  apply(drule C.assign_elim, simp+)
  apply(rule stop_rel)
  done

lemma mds\<^sub>s_A_of_mds\<^sub>0:
  "mds\<^sub>s = mds\<^sub>A_of mds\<^sub>0"
  apply(rule preserves_modes_mem_mds\<^sub>A_simp)
  apply clarsimp
  apply(case_tac m)
     unfolding mds\<^sub>s_def mds\<^sub>0_def mds\<^sub>A_of_def
     apply(clarsimp simp: reg_not_visible_abs)+
  done

lemma A_of_mds\<^sub>0_is_mds\<^sub>s:
  "mds\<^sub>A_of mds\<^sub>0 = mds\<^sub>s"
  by (simp add: mds\<^sub>s_A_of_mds\<^sub>0)

lemma prog_high_branch\<^sub>C_in_R\<^sub>C_of_R:
  "C.low_mds_eq mds\<^sub>0 mem\<^sub>1 mem\<^sub>2 \<Longrightarrow>
       (\<langle>C.prog_high_branch\<^sub>C, mds\<^sub>0, mem\<^sub>1\<rangle>\<^sub>C, \<langle>C.prog_high_branch\<^sub>C, mds\<^sub>0, mem\<^sub>2\<rangle>\<^sub>C)
        \<in> (R\<^sub>C_of A.R RefRel_HighBranch rel_inv\<^sub>C)"
  apply(clarsimp simp: R\<^sub>C_of_def)
  apply(rule_tac x=A.prog_high_branch in exI)
  apply(rule_tac x="mds\<^sub>A_of mds\<^sub>0" in exI)
  apply(rule_tac x="mem\<^sub>A_of mem\<^sub>1" in exI)
  apply(rule conjI)
   apply(rule prog_high_branch_RefRel)
  apply(rule_tac x=A.prog_high_branch in exI)
  apply(rule_tac x="mds\<^sub>A_of mds\<^sub>0" in exI)
  apply(rule_tac x="mem\<^sub>A_of mem\<^sub>2" in exI)
  apply(rule conjI)
   apply(rule prog_high_branch_RefRel)
  apply(simp add: A_of_mds\<^sub>0_is_mds\<^sub>s)
  apply(rule conjI)
   apply(rule A.prog_high_branch_secure')
   apply(clarsimp simp: A.low_mds_eq_def)
   apply(case_tac x)
   unfolding C.low_mds_eq_def mem\<^sub>A_of_def dma_def dma\<^sub>C_def \<C>\<^sub>C_def mds\<^sub>0_def
   apply clarsimp+
  apply(rule rel_inv\<^sub>C_default, simp)
  done

lemma "C.com_sifum_secure (C.prog_high_branch\<^sub>C, mds\<^sub>0)"
  unfolding C.com_sifum_secure_def C.low_indistinguishable_def
  apply clarify
  apply(rule C.mm_equiv_intro)
   apply(rule strong_low_bisim_mm_R\<^sub>C_of_R)
  by (rule prog_high_branch\<^sub>C_in_R\<^sub>C_of_R)

end

end
