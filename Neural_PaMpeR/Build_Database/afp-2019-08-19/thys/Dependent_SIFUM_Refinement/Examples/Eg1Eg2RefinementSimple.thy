theory Eg1Eg2RefinementSimple
imports Eg1Eg2
begin

context sifum_refinement_eg1_eg2
begin

inductive_set RelS_Eg1Eg2 :: "(
    (((var, aexp, bexp) Stmt \<times> (Mode \<Rightarrow> var set)) \<times> (var \<Rightarrow> val)) \<times>
     ((var\<^sub>C, aexp\<^sub>C, bexp\<^sub>C) Stmt \<times> (Mode \<Rightarrow> var\<^sub>C set)) \<times> (var\<^sub>C \<Rightarrow> val)
    ) set"
where
  acq_mode_rel: "\<lbrakk>c\<^sub>A = ModeDecl Skip (Acq x SomeMode) ;; c\<^sub>A_tail;
    c\<^sub>C = ModeDecl Skip (Acq (Eg2_var\<^sub>C_of_Eg1 x) SomeMode) ;; c\<^sub>C_tail;
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range Eg2_var\<^sub>C_of_Eg1 \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A''\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>A_tail, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>Stop ;; c\<^sub>A_tail, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2" |

  rel_mode_rel: "\<lbrakk>c\<^sub>A = ModeDecl Skip (Rel x SomeMode);
    c\<^sub>C = ModeDecl Skip (Rel (Eg2_var\<^sub>C_of_Eg1 x) SomeMode);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range Eg2_var\<^sub>C_of_Eg1 \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    \<forall>mds\<^sub>A' mem\<^sub>A' mem\<^sub>A'' mds\<^sub>C' mem\<^sub>C' mem\<^sub>C''.
        (
         mds\<^sub>A' = mds\<^sub>A_of mds\<^sub>C' \<and>
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A''\<rangle>\<^sub>A, \<langle>Stop, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C, \<langle>Stop, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>Stop, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2" |

  assign_load_rel: "\<lbrakk>c\<^sub>A = (x \<leftarrow> aexp.Load y) ;; c\<^sub>A_tail;
    c\<^sub>C = ((Eg2_var\<^sub>C_of_Eg1 x) \<leftarrow> aexp\<^sub>C.Load (Eg2_var\<^sub>C_of_Eg1 y)) ;; c\<^sub>C_tail;
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range Eg2_var\<^sub>C_of_Eg1 \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    \<comment> \<open>With this requirement it is possible to establish \<open>x \<notin> mds\<^sub>A GuarNoReadOrWrite\<close>.\<close>
    \<^cancel>\<open>x \<noteq> y;\<close>
    \<comment> \<open>However since we've deemed it reasonable to require \<open>x \<notin> mds\<^sub>A GuarNoWrite\<close>,\<close>
    \<comment> \<open>it makes little sense not to just require \<open>x \<notin> mds\<^sub>A GuarNoReadOrWrite\<close> as well.\<close>
    x \<notin> mds\<^sub>A GuarNoReadOrWrite;
    \<comment> \<open>Without this requirement, we would have to prove preservation of \<open>doesnt_modify c x\<close>\<close>
    \<comment> \<open>because \<open>x \<in> mds\<^sub>A GuarNoWrite\<close> holds in the case where \<open>mem\<^sub>A x = mem\<^sub>A y\<close>.\<close>
    \<comment> \<open>It makes more sense just to assume a blanket ban on this guarantee for this instruction,\<close>
    \<comment> \<open>seeing as it is clearly a write operation to \<open>x\<close>.\<close>
    x \<notin> mds\<^sub>A GuarNoWrite;
    \<comment> \<open>This command loads from \<open>y\<close>, so it makes little sense to guarantee we're not reading it\<close>
    y \<notin> mds\<^sub>A GuarNoReadOrWrite;
    \<comment> \<open>Requirements for sound mode use preservation for variables other than \<open>x\<close> and \<open>y\<close>\<close>
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
         (\<langle>Stop ;; c\<^sub>A_tail, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2" |

  assign_const_rel: "\<lbrakk>c\<^sub>A = (x \<leftarrow> aexp.Const z) ;; c\<^sub>A_tail;
    c\<^sub>C = ((Eg2_var\<^sub>C_of_Eg1 x) \<leftarrow> aexp\<^sub>C.Const z) ;; c\<^sub>C_tail;
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range Eg2_var\<^sub>C_of_Eg1 \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
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
         (\<langle>Stop ;; c\<^sub>A_tail, mds\<^sub>A', mem\<^sub>A'\<rangle>\<^sub>A, \<langle>Stop ;; c\<^sub>C_tail, mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2" |

  if_reg_load_rel: "\<lbrakk>
    c\<^sub>A = (If (Eg1.Eq x 0) c\<^sub>A_then c\<^sub>A_else) ;; c\<^sub>A_tail;
    c\<^sub>C = (reg\<^sub>C \<leftarrow> (Load (Eg2_var\<^sub>C_of_Eg1 x))) ;; ((If (Eq reg\<^sub>C 0) c\<^sub>C_then c\<^sub>C_else) ;; c\<^sub>C_tail);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range Eg2_var\<^sub>C_of_Eg1 \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    reg\<^sub>C \<notin> mds\<^sub>C GuarNoReadOrWrite;
    reg\<^sub>C \<notin> mds\<^sub>C GuarNoWrite;
    x \<notin> mds\<^sub>A GuarNoReadOrWrite;
    \<comment> \<open>Nope: need to make this one versatile enough to allow \<open>c = control_var\<close> for our example\<close>
    \<^cancel>\<open>x \<notin> \<C>;\<close>
    \<forall>x'. x \<in> \<C>_vars x' \<longrightarrow> x' \<notin> mds\<^sub>A GuarNoReadOrWrite;
    (\<forall>mem\<^sub>A' mem\<^sub>C' mem\<^sub>A'' mem\<^sub>C''.
        (
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         \<comment> \<open>The change in \<open>mem\<^sub>C\<close> does not affect \<open>mem\<^sub>A\<close>\<close>
         mem\<^sub>A'' = mem\<^sub>A' \<and>
         \<comment> \<open>The concrete and abstract versions of the bool condition must become consistent\<close>
         ev\<^sub>B\<^sub>C mem\<^sub>C' (Eq reg\<^sub>C 0) = ev\<^sub>B mem\<^sub>A' (Eg1.Eq x 0) \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
          \<langle>Stop ;; (If (Eq reg\<^sub>C 0) c\<^sub>C_then c\<^sub>C_else) ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A''\<rangle>\<^sub>A,
          \<langle>Stop ;; (If (Eq reg\<^sub>C 0) c\<^sub>C_then c\<^sub>C_else) ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2)
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2" |

  if_reg_stop_rel: "\<lbrakk>
    c\<^sub>A = (If (Eg1.Eq x 0) c\<^sub>A_then c\<^sub>A_else) ;; c\<^sub>A_tail;
    c\<^sub>C = Stop ;; ((If (Eq reg\<^sub>C 0) c\<^sub>C_then c\<^sub>C_else) ;; c\<^sub>C_tail);
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range Eg2_var\<^sub>C_of_Eg1 \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    x \<in> mds\<^sub>A AsmNoWrite \<and> x \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<comment> \<open>Likely we will need to carry this through to the \<open>if_reg_rel\<close> case.\<close>
    ev\<^sub>B\<^sub>C mem\<^sub>C (Eq reg\<^sub>C 0) = ev\<^sub>B mem\<^sub>A (Eg1.Eq x 0);
    (\<forall>mem\<^sub>A' mem\<^sub>C' mem\<^sub>A'' mem\<^sub>C''.
        (
         mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
         mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
         \<comment> \<open>The change in \<open>mem\<^sub>C\<close> does not affect \<open>mem\<^sub>A\<close>\<close>
         mem\<^sub>A'' = mem\<^sub>A' \<and>
         \<comment> \<open>The concrete and abstract versions of the bool condition must remain consistent\<close>
         ev\<^sub>B\<^sub>C mem\<^sub>C' (Eq reg\<^sub>C 0) = ev\<^sub>B mem\<^sub>A' (Eg1.Eq x 0) \<and>
         ev\<^sub>B\<^sub>C mem\<^sub>C'' (Eq reg\<^sub>C 0) = ev\<^sub>B mem\<^sub>A'' (Eg1.Eq x 0) \<and>
         (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
          \<langle>(If (Eq reg\<^sub>C 0) c\<^sub>C_then c\<^sub>C_else) ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
        )
         \<longrightarrow>
         (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A''\<rangle>\<^sub>A,
          \<langle>(If (Eq reg\<^sub>C 0) c\<^sub>C_then c\<^sub>C_else) ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2)
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2" |

  if_reg_rel: "\<lbrakk>
\<comment> \<open>Is a more generic version possible for an arbitrary \<open>b\<^sub>A\<close>?\<close>
    \<^cancel>\<open>c\<^sub>A = (If b\<^sub>A c\<^sub>A_then c\<^sub>A_else) ;; c\<^sub>A_tail;\<close>
    \<^cancel>\<open>b\<^sub>A = Eg1.Eq x 0;\<close>  \<comment> \<open>\<open>ev\<^sub>B mem\<^sub>A b\<^sub>A\<close>\<close>
    c\<^sub>A = (If (Eg1.Eq x 0) c\<^sub>A_then c\<^sub>A_else) ;; c\<^sub>A_tail;
    c\<^sub>C = (If (Eq reg\<^sub>C 0) c\<^sub>C_then c\<^sub>C_else) ;; c\<^sub>C_tail;
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<forall>v\<^sub>C. v\<^sub>C \<notin> range Eg2_var\<^sub>C_of_Eg1 \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C AsmNoReadOrWrite);
    x \<in> mds\<^sub>A AsmNoWrite \<and> x \<notin> mds\<^sub>A AsmNoReadOrWrite;
    \<comment> \<open>The concrete and abstract versions of the bool condition must have remained consistent\<close>
    ev\<^sub>B\<^sub>C mem\<^sub>C (Eq reg\<^sub>C 0) = ev\<^sub>B mem\<^sub>A (Eg1.Eq x 0);
    \<comment> \<open>As for \<open>if_reg_load_rel\<close>\<close>
    reg\<^sub>C \<notin> mds\<^sub>C GuarNoReadOrWrite;
    reg\<^sub>C \<notin> mds\<^sub>C GuarNoWrite;
    x \<notin> mds\<^sub>A GuarNoReadOrWrite;
    \<forall>x'. x \<in> \<C>_vars x' \<longrightarrow> x' \<notin> mds\<^sub>A GuarNoReadOrWrite;
    (\<forall>mem\<^sub>A' mem\<^sub>C' mem\<^sub>A'' mem\<^sub>C''.
       mem\<^sub>A' = mem\<^sub>A_of mem\<^sub>C' \<and>
       mem\<^sub>A'' = mem\<^sub>A_of mem\<^sub>C'' \<and>
       ev\<^sub>B\<^sub>C mem\<^sub>C'' (Eq reg\<^sub>C 0) = ev\<^sub>B mem\<^sub>A'' (Eg1.Eq x 0) \<and>
       ev\<^sub>B\<^sub>C mem\<^sub>C' (Eq reg\<^sub>C 0) = ev\<^sub>B mem\<^sub>A' (Eg1.Eq x 0) \<and>
       (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A''\<rangle>\<^sub>A,
        \<langle>(if (ev\<^sub>B mem\<^sub>A'' (Eg1.Eq x 0)) then c\<^sub>A_then else c\<^sub>A_else) ;; c\<^sub>A_tail, mds\<^sub>A, mem\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w \<and>
       (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C''\<rangle>\<^sub>C,
        \<langle>(if (ev\<^sub>B\<^sub>C mem\<^sub>C'' (Eq reg\<^sub>C 0)) then c\<^sub>C_then else c\<^sub>C_else) ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w
       \<longrightarrow>
       (\<langle>(if (ev\<^sub>B mem\<^sub>A'' (Eg1.Eq x 0)) then c\<^sub>A_then else c\<^sub>A_else) ;; c\<^sub>A_tail, mds\<^sub>A, mem\<^sub>A'\<rangle>\<^sub>A,
        \<langle>(if (ev\<^sub>B\<^sub>C mem\<^sub>C'' (Eq reg\<^sub>C 0)) then c\<^sub>C_then else c\<^sub>C_else) ;; c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2);
    \<comment> \<open>Disallow branching on variables that can potentially be in the high domain\<close>
    x \<noteq> buffer \<and> x \<noteq> high_var
    \<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2" |

  stop_seq_rel: "\<lbrakk>c\<^sub>A = Stop ;; c\<^sub>A_tail;
    c\<^sub>C = Stop ;; c\<^sub>C_tail;
    mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C;
    mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C;
    (\<langle>c\<^sub>A_tail, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C_tail, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2\<rbrakk>
    \<Longrightarrow>
    (\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2" |

  stop_rel:
    "(\<langle>Stop, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A, \<langle>Stop, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"


definition abs_steps' :: "(_,_,_) Stmt \<Rightarrow> (_,_,_) Stmt \<Rightarrow> nat" where
  "abs_steps' c\<^sub>A c\<^sub>C \<equiv>
    (if (\<exists>x m c\<^sub>A_tail. c\<^sub>A = ((Skip@[x +=\<^sub>m m]) ;; c\<^sub>A_tail)) \<and>
        (\<exists>x m c\<^sub>C_tail. c\<^sub>C = ((Skip@[Eg2_var\<^sub>C_of_Eg1 x +=\<^sub>m m]) ;; c\<^sub>C_tail)) then (Suc 0)
     else if (\<exists> c\<^sub>A_tail c\<^sub>C_tail. c\<^sub>A = (Stop ;; c\<^sub>A_tail) \<and> c\<^sub>C = (Stop ;; c\<^sub>C_tail)) then (Suc 0)
     else if (\<exists> x then\<^sub>A else\<^sub>A tail\<^sub>A then\<^sub>C else\<^sub>C tail\<^sub>C.
        c\<^sub>A = (Stmt.If (bexp.Eq x 0) then\<^sub>A else\<^sub>A ;; tail\<^sub>A) \<and>
        (c\<^sub>C = ((reg\<^sub>C \<leftarrow> aexp\<^sub>C.Load (Eg2_var\<^sub>C_of_Eg1 x)) ;; Stmt.If (bexp\<^sub>C.Eq reg\<^sub>C 0) then\<^sub>C else\<^sub>C ;; tail\<^sub>C)) \<or>
         c\<^sub>C = (Stop ;; Stmt.If (bexp\<^sub>C.Eq reg\<^sub>C 0) then\<^sub>C else\<^sub>C ;; tail\<^sub>C))
        then 0
     else (Suc 0))"

fun abs_steps
where
"abs_steps \<langle>c\<^sub>A, _, _\<rangle>\<^sub>A \<langle>c\<^sub>C, _, _\<rangle>\<^sub>C = abs_steps' c\<^sub>A c\<^sub>C"

lemma closed_others_RelS_Eg1Eg2:
  "closed_others RelS_Eg1Eg2"
unfolding closed_others_def
proof(clarify)
fix c\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>C mem\<^sub>C'
assume
  in_rel: "(\<langle>c\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A,
    \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2" and
  vars: " \<forall>x. mem\<^sub>C x \<noteq> mem\<^sub>C' x \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x"
and  dmas: "\<forall>x. dma\<^sub>C mem\<^sub>C x \<noteq> dma\<^sub>C mem\<^sub>C' x \<longrightarrow> \<not> var_asm_not_written mds\<^sub>C x"
from in_rel vars dmas
show "(\<langle>c\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
  proof (induct rule: RelS_Eg1Eg2.induct)
  case (acq_mode_rel c\<^sub>A x SomeMode tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    using acq_mode_rel
    by (simp add:RelS_Eg1Eg2.acq_mode_rel)
  next
  case (rel_mode_rel c\<^sub>A x SomeMode c\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    using rel_mode_rel
    by (simp add:RelS_Eg1Eg2.rel_mode_rel)
  next
  case (assign_load_rel c\<^sub>A x y tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    using assign_load_rel
    by (simp add:RelS_Eg1Eg2.assign_load_rel)
  next
  case (assign_const_rel c\<^sub>A x z tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    using assign_const_rel
    by (simp add:RelS_Eg1Eg2.assign_const_rel)
  next
  case (if_reg_load_rel c\<^sub>A x then\<^sub>A else\<^sub>A tail\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    using if_reg_load_rel
    by (simp add:RelS_Eg1Eg2.if_reg_load_rel)
  next
  case (if_reg_stop_rel c\<^sub>A x then\<^sub>A else\<^sub>A tail\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    using if_reg_stop_rel
    proof (clarsimp)
      from if_reg_stop_rel.hyps(3,5,6) if_reg_stop_rel.prems(1)
      have reg\<^sub>C_untouched: "mem\<^sub>C reg\<^sub>C = mem\<^sub>C' reg\<^sub>C" and
        x\<^sub>C_untouched: "mem\<^sub>C (Eg2_var\<^sub>C_of_Eg1 x) = mem\<^sub>C' (Eg2_var\<^sub>C_of_Eg1 x)" and
        x\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C x = mem\<^sub>A_of mem\<^sub>C' x"
        using reg\<^sub>C_is_not_the_var\<^sub>C_of_anything mem\<^sub>A_of_def NoWrite\<^sub>A_implies_NoWrite\<^sub>C
        by (clarsimp simp:var_asm_not_written_def, blast)+
      with if_reg_stop_rel.hyps
      have conds_still_match: "(mem\<^sub>C' reg\<^sub>C = 0) = (mem\<^sub>A_of mem\<^sub>C' x = 0)"
        by simp
      with if_reg_stop_rel RelS_Eg1Eg2.if_reg_stop_rel
      show "(\<langle>Stmt.If (bexp.Eq x 0) then\<^sub>A else\<^sub>A ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A,
             \<langle>Stop ;; Stmt.If (bexp\<^sub>C.Eq reg\<^sub>C 0) then\<^sub>C else\<^sub>C ;; tail\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C)
             \<in> RelS_Eg1Eg2"
        by clarsimp
    qed
  next
  case (if_reg_rel c\<^sub>A x then\<^sub>A else\<^sub>A tail\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    using if_reg_rel
    proof (clarsimp)
      from if_reg_rel.hyps(3,5,6) if_reg_rel.prems(1)
      have reg\<^sub>C_untouched: "mem\<^sub>C reg\<^sub>C = mem\<^sub>C' reg\<^sub>C" and
        x\<^sub>C_untouched: "mem\<^sub>C (Eg2_var\<^sub>C_of_Eg1 x) = mem\<^sub>C' (Eg2_var\<^sub>C_of_Eg1 x)" and
        x\<^sub>A_untouched: "mem\<^sub>A_of mem\<^sub>C x = mem\<^sub>A_of mem\<^sub>C' x"
        using reg\<^sub>C_is_not_the_var\<^sub>C_of_anything mem\<^sub>A_of_def NoWrite\<^sub>A_implies_NoWrite\<^sub>C
        by (clarsimp simp:var_asm_not_written_def, blast)+
      with if_reg_rel.hyps
      have conds_still_match: "(mem\<^sub>C' reg\<^sub>C = 0) = (mem\<^sub>A_of mem\<^sub>C' x = 0)"
        by simp
      show "(\<langle>Stmt.If (bexp.Eq x 0) then\<^sub>A else\<^sub>A ;; tail\<^sub>A, mds\<^sub>A_of mds\<^sub>C, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A,
             \<langle>Stmt.If (bexp\<^sub>C.Eq reg\<^sub>C 0) then\<^sub>C else\<^sub>C ;; tail\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C)
             \<in> RelS_Eg1Eg2"
        apply (rule RelS_Eg1Eg2.if_reg_rel, simp+)
            using if_reg_rel apply simp
           using if_reg_rel apply simp
          using conds_still_match apply simp
         using if_reg_rel apply blast+
        done
    qed
  next
  case (stop_seq_rel c\<^sub>A tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  show "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A_of mem\<^sub>C'\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    using stop_seq_rel
    by (simp add:RelS_Eg1Eg2.stop_seq_rel)
  next
  case (stop_rel mds\<^sub>C mem\<^sub>C)
  show ?case by (simp add:RelS_Eg1Eg2.stop_rel)
  qed
qed

lemma preserves_modes_mem_RelS_Eg1Eg2:
  "preserves_modes_mem RelS_Eg1Eg2"
unfolding preserves_modes_mem_def2
proof(clarsimp)
  fix c\<^sub>A mds\<^sub>A mem\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>C
  assume in_rel: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
  thus "mem\<^sub>A = mem\<^sub>A_of mem\<^sub>C \<and> mds\<^sub>A = mds\<^sub>A_of mds\<^sub>C"
    by (cases rule:RelS_Eg1Eg2.cases, blast+)
qed

(* Just some exploration to see what's likely to be needed *)

lemma mem_twist_other: "z \<noteq> x \<Longrightarrow> z \<noteq> y \<Longrightarrow> mem (x := mem y, z := v) = mem (z := v, x := (mem (z := v)) y)"
  by (simp add: fun_upd_other fun_upd_twist)

lemma reg\<^sub>C_load_helper:
  "x\<^sub>C \<noteq> Eg2_var\<^sub>C_of_Eg1 x \<Longrightarrow>
   (\<langle>reg\<^sub>C \<leftarrow> aexp\<^sub>C.Load (Eg2_var\<^sub>C_of_Eg1 x), mds, mem(x\<^sub>C := v)\<rangle>\<^sub>C, \<langle>Stop, mds, mem
            (x\<^sub>C := v, reg\<^sub>C := mem (Eg2_var\<^sub>C_of_Eg1 x))\<rangle>\<^sub>C) =
   (\<langle>reg\<^sub>C \<leftarrow> aexp\<^sub>C.Load (Eg2_var\<^sub>C_of_Eg1 x), mds, mem(x\<^sub>C := v)\<rangle>\<^sub>C, \<langle>Stop, mds, mem
            (x\<^sub>C := v, reg\<^sub>C := (mem(x\<^sub>C := v)) (Eg2_var\<^sub>C_of_Eg1 x))\<rangle>\<^sub>C)"
  using fun_upd_other by simp

lemma preserves_local_guarantee_compliance_RelS_Eg1Eg2:
  "preserves_local_guarantee_compliance RelS_Eg1Eg2"
proof(clarsimp simp:preserves_local_guarantee_compliance_def2)
  fix c\<^sub>A mds\<^sub>A mem\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>C
  assume in_RelS: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2" and
    respects\<^sub>A: "A.respects_own_guarantees (c\<^sub>A, mds\<^sub>A)"
  thus "conc.respects_own_guarantees (c\<^sub>C, mds\<^sub>C)"
  unfolding conc.respects_own_guarantees_def conc.doesnt_read_or_modify_def conc.doesnt_read_or_modify_vars_def conc.doesnt_modify_def
  proof(induct rule:RelS_Eg1Eg2.induct)
    case (acq_mode_rel c\<^sub>A x m tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
      from acq_mode_rel.hyps(2-3)
      show ?case using C.decl_eval\<^sub>w' C.eval\<^sub>w.seq C.seq_decl_elim by fastforce+
    next
    case (rel_mode_rel c\<^sub>A x m c\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
      from rel_mode_rel.hyps(2-3)
      show ?case using C.decl_eval\<^sub>w' C.eval\<^sub>w.seq C.seq_decl_elim by fastforce+
    next
    case (assign_load_rel c\<^sub>A x y tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
      hence in_RelS: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
        by (simp add:RelS_Eg1Eg2.intros(3))

      from assign_load_rel.prems show ?case
      proof (clarify)
        assume respects\<^sub>A: "A.respects_own_guarantees (c\<^sub>A, mds\<^sub>A)"
        fix x\<^sub>C
        let ?case_x\<^sub>C = "(x\<^sub>C \<in> snd (c\<^sub>C, mds\<^sub>C) GuarNoReadOrWrite \<longrightarrow>
               (\<forall>mds mem c' mds' mem'.
                   (\<langle>fst (c\<^sub>C, mds\<^sub>C), mds, mem\<rangle>\<^sub>C, \<langle>c', mds', mem'\<rangle>\<^sub>C)
                   \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C \<longrightarrow>
                   (\<forall>x\<in>{x\<^sub>C} \<union> \<C>_vars\<^sub>C x\<^sub>C.
                       \<forall>v. (\<langle>fst (c\<^sub>C, mds\<^sub>C), mds, mem(x := v)\<rangle>\<^sub>C, \<langle>c', mds', mem'(x := v)\<rangle>\<^sub>C)
                           \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C))) \<and>
              (x\<^sub>C \<in> snd (c\<^sub>C, mds\<^sub>C) GuarNoWrite \<longrightarrow>
               (\<forall>mds mem c' mds' mem'.
                   (\<langle>fst (c\<^sub>C, mds\<^sub>C), mds, mem\<rangle>\<^sub>C, \<langle>c', mds', mem'\<rangle>\<^sub>C)
                   \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C \<longrightarrow>
                   mem x\<^sub>C = mem' x\<^sub>C \<and> dma\<^sub>C mem x\<^sub>C = dma\<^sub>C mem' x\<^sub>C))"

        (* For x\<^sub>C = x, we have to argue that the abstract version of x\<^sub>C must have the same
           guarantees as for x\<^sub>C, which yields contradictions in both cases. *)
        from assign_load_rel(3,6,7) preserves_modes_mem_RelS_Eg1Eg2 has_mode\<^sub>A
        have notGuarNoRW_x\<^sub>C: "x\<^sub>C = Eg2_var\<^sub>C_of_Eg1 x \<Longrightarrow> x\<^sub>C \<notin> mds\<^sub>C GuarNoReadOrWrite" and
             notGuarNoWrite_x\<^sub>C: "x\<^sub>C = Eg2_var\<^sub>C_of_Eg1 x \<Longrightarrow> x\<^sub>C \<notin> mds\<^sub>C GuarNoWrite" by clarsimp+

        (* For x\<^sub>C = y, waive doesnt_read_or_modify using \<not> GuarNoRW y from refinement relation,
           and the proof for doesnt_modify is straightforward *)
        from assign_load_rel(3,8) preserves_modes_mem_RelS_Eg1Eg2 has_mode\<^sub>A
        have "x\<^sub>C = Eg2_var\<^sub>C_of_Eg1 y \<Longrightarrow> x\<^sub>C \<notin> mds\<^sub>C GuarNoReadOrWrite" by clarsimp
        with assign_load_rel(2)
        have "\<lbrakk>x\<^sub>C = Eg2_var\<^sub>C_of_Eg1 y; Eg2_var\<^sub>C_of_Eg1 x \<notin> \<C>_vars\<^sub>C x\<^sub>C\<rbrakk> \<Longrightarrow> ?case_x\<^sub>C"
          apply clarsimp
          apply(drule C.seq_assign_elim, clarsimp)
          using \<C>_vars\<^sub>C_def dma\<^sub>C_def by auto

        (* For all other x\<^sub>C, the proof should be straightforward because c\<^sub>C does not touch x\<^sub>C,
           and we've required that x and y cannot potentially be the control var of x\<^sub>C *)
        moreover have "\<lbrakk>x\<^sub>C \<noteq> Eg2_var\<^sub>C_of_Eg1 x; x\<^sub>C \<noteq> Eg2_var\<^sub>C_of_Eg1 y;
               Eg2_var\<^sub>C_of_Eg1 x \<notin> \<C>_vars\<^sub>C x\<^sub>C; Eg2_var\<^sub>C_of_Eg1 y \<notin> \<C>_vars\<^sub>C x\<^sub>C\<rbrakk>
              \<Longrightarrow> ?case_x\<^sub>C"
          using assign_load_rel(2,6) apply safe
             apply(clarsimp, drule C.seq_assign_elim)
             apply(simp add: mem_twist_other C.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>C del:fun_upd_apply)
            apply(clarsimp, drule C.seq_assign_elim, clarsimp)
            apply(subgoal_tac "xa \<noteq> Eg2_var\<^sub>C_of_Eg1 x \<and> xa \<noteq> Eg2_var\<^sub>C_of_Eg1 y")
             apply(simp add: mem_twist_other C.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>C del:fun_upd_apply)
            apply blast
           apply(clarsimp, drule C.seq_assign_elim, clarsimp)
          apply(clarsimp, drule C.seq_assign_elim)
          using \<C>_vars\<^sub>C_def dma\<^sub>C_def by auto

        moreover have "Eg2_var\<^sub>C_of_Eg1 x \<notin> \<C>_vars\<^sub>C x\<^sub>C" and "Eg2_var\<^sub>C_of_Eg1 y \<notin> \<C>_vars\<^sub>C x\<^sub>C"
          using assign_load_rel(9-10) unfolding \<C>_vars\<^sub>C_def
          by (metis Eg2_var\<^sub>C_of_Eg1.simps(1) A.\<C>_simp empty_iff insert_iff inv_f_eq var\<^sub>C_of_inj)+
        moreover note notGuarNoRW_x\<^sub>C notGuarNoWrite_x\<^sub>C
        moreover have "x\<^sub>C \<notin> mds\<^sub>C GuarNoReadOrWrite \<Longrightarrow> x\<^sub>C \<notin> mds\<^sub>C GuarNoWrite \<Longrightarrow> ?case_x\<^sub>C" by auto
        ultimately show ?case_x\<^sub>C by fastforce
      qed
    next
    case (assign_const_rel c\<^sub>A x z tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
      from assign_const_rel.prems show ?case
      proof (clarify)
        assume respects\<^sub>A: "A.respects_own_guarantees (c\<^sub>A, mds\<^sub>A)"
        fix x\<^sub>C
        let ?case_x\<^sub>C = "(x\<^sub>C \<in> snd (c\<^sub>C, mds\<^sub>C) GuarNoReadOrWrite \<longrightarrow>
               (\<forall>mds mem c' mds' mem'.
                   (\<langle>fst (c\<^sub>C, mds\<^sub>C), mds, mem\<rangle>\<^sub>C, \<langle>c', mds', mem'\<rangle>\<^sub>C)
                   \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C \<longrightarrow>
                   (\<forall>x\<in>{x\<^sub>C} \<union> \<C>_vars\<^sub>C x\<^sub>C.
                       \<forall>v. (\<langle>fst (c\<^sub>C, mds\<^sub>C), mds, mem(x := v)\<rangle>\<^sub>C, \<langle>c', mds', mem'(x := v)\<rangle>\<^sub>C)
                           \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C))) \<and>
              (x\<^sub>C \<in> snd (c\<^sub>C, mds\<^sub>C) GuarNoWrite \<longrightarrow>
               (\<forall>mds mem c' mds' mem'.
                   (\<langle>fst (c\<^sub>C, mds\<^sub>C), mds, mem\<rangle>\<^sub>C, \<langle>c', mds', mem'\<rangle>\<^sub>C)
                   \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C \<longrightarrow>
                   mem x\<^sub>C = mem' x\<^sub>C \<and> dma\<^sub>C mem x\<^sub>C = dma\<^sub>C mem' x\<^sub>C))"
        from assign_const_rel(3,6,7) preserves_modes_mem_RelS_Eg1Eg2 has_mode\<^sub>A
        have notGuarNoRW_x\<^sub>C: "x\<^sub>C = Eg2_var\<^sub>C_of_Eg1 x \<Longrightarrow> x\<^sub>C \<notin> mds\<^sub>C GuarNoReadOrWrite" and
             notGuarNoWrite_x\<^sub>C: "x\<^sub>C = Eg2_var\<^sub>C_of_Eg1 x \<Longrightarrow> x\<^sub>C \<notin> mds\<^sub>C GuarNoWrite" by clarsimp+

        moreover have "\<lbrakk>x\<^sub>C \<noteq> Eg2_var\<^sub>C_of_Eg1 x; Eg2_var\<^sub>C_of_Eg1 x \<notin> \<C>_vars\<^sub>C x\<^sub>C\<rbrakk> \<Longrightarrow> ?case_x\<^sub>C"
          using assign_const_rel(2,8) apply safe
             apply(clarsimp, drule C.seq_assign_elim)
             apply(simp add: fun_upd_twist C.eval\<^sub>w.seq assign_eval\<^sub>w_const\<^sub>C)
            apply(clarsimp, drule C.seq_assign_elim, clarsimp)
            apply(subgoal_tac "xa \<noteq> Eg2_var\<^sub>C_of_Eg1 x")
             apply(simp add: fun_upd_twist C.eval\<^sub>w.seq assign_eval\<^sub>w_const\<^sub>C)
            apply blast
           apply(clarsimp, drule C.seq_assign_elim, clarsimp)
          apply(clarsimp, drule C.seq_assign_elim)
          using \<C>_vars\<^sub>C_def dma\<^sub>C_def by auto

        moreover have "Eg2_var\<^sub>C_of_Eg1 x \<notin> \<C>_vars\<^sub>C x\<^sub>C"
          using assign_const_rel(8) unfolding \<C>_vars\<^sub>C_def
          by (metis Eg2_var\<^sub>C_of_Eg1.simps(1) A.\<C>_simp empty_iff insert_iff inv_f_eq var\<^sub>C_of_inj)
        moreover note notGuarNoRW_x\<^sub>C notGuarNoWrite_x\<^sub>C
        moreover have "x\<^sub>C \<notin> mds\<^sub>C GuarNoReadOrWrite \<Longrightarrow> x\<^sub>C \<notin> mds\<^sub>C GuarNoWrite \<Longrightarrow> ?case_x\<^sub>C" by auto
        ultimately show ?case_x\<^sub>C by fastforce
      qed
    next
    case (if_reg_load_rel c\<^sub>A x then\<^sub>A else\<^sub>A tail\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
      from if_reg_load_rel.prems show ?case
      proof (clarify)
        assume respects\<^sub>A: "A.respects_own_guarantees (c\<^sub>A, mds\<^sub>A)"
        fix x\<^sub>C
        let ?case_x\<^sub>C = "(x\<^sub>C \<in> snd (c\<^sub>C, mds\<^sub>C) GuarNoReadOrWrite \<longrightarrow>
               (\<forall>mds mem c' mds' mem'.
                   (\<langle>fst (c\<^sub>C, mds\<^sub>C), mds, mem\<rangle>\<^sub>C, \<langle>c', mds', mem'\<rangle>\<^sub>C)
                   \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C \<longrightarrow>
                   (\<forall>x\<in>{x\<^sub>C} \<union> \<C>_vars\<^sub>C x\<^sub>C.
                       \<forall>v. (\<langle>fst (c\<^sub>C, mds\<^sub>C), mds, mem(x := v)\<rangle>\<^sub>C, \<langle>c', mds', mem'(x := v)\<rangle>\<^sub>C)
                           \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C))) \<and>
              (x\<^sub>C \<in> snd (c\<^sub>C, mds\<^sub>C) GuarNoWrite \<longrightarrow>
               (\<forall>mds mem c' mds' mem'.
                   (\<langle>fst (c\<^sub>C, mds\<^sub>C), mds, mem\<rangle>\<^sub>C, \<langle>c', mds', mem'\<rangle>\<^sub>C)
                   \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C \<longrightarrow>
                   mem x\<^sub>C = mem' x\<^sub>C \<and> dma\<^sub>C mem x\<^sub>C = dma\<^sub>C mem' x\<^sub>C))"
        (* For x\<^sub>C = x, waive doesnt_read_or_modify using \<not> GuarNoRW x from refinement relation
           (makes sense because it's being read), then doesnt_modify is straightforward *)
        from if_reg_load_rel(3,8) preserves_modes_mem_RelS_Eg1Eg2 has_mode\<^sub>A
        have "x\<^sub>C = Eg2_var\<^sub>C_of_Eg1 x \<Longrightarrow> x\<^sub>C \<notin> mds\<^sub>C GuarNoReadOrWrite" by clarsimp
        with if_reg_load_rel(2)
        have "x\<^sub>C = Eg2_var\<^sub>C_of_Eg1 x \<Longrightarrow> ?case_x\<^sub>C"
          apply clarsimp
          apply(drule C.seq_assign_elim, clarsimp)
          using \<C>_vars\<^sub>C_def dma\<^sub>C_def by auto

        moreover from if_reg_load_rel(2)
        have "\<lbrakk>x\<^sub>C \<noteq> reg\<^sub>C; x\<^sub>C \<noteq> Eg2_var\<^sub>C_of_Eg1 x; reg\<^sub>C \<notin> \<C>_vars\<^sub>C x\<^sub>C;
               Eg2_var\<^sub>C_of_Eg1 x \<in> \<C>_vars\<^sub>C x\<^sub>C \<Longrightarrow> x\<^sub>C \<notin> mds\<^sub>C GuarNoReadOrWrite\<rbrakk> \<Longrightarrow> ?case_x\<^sub>C"
          apply safe
             apply(clarsimp, drule C.seq_assign_elim)
             apply(simp add:fun_upd_twist del:fun_upd_apply)
             apply(rule C.eval\<^sub>w.seq, clarsimp)
             apply(simp add:reg\<^sub>C_load_helper del:fun_upd_apply)
             apply(rule assign_eval\<^sub>w_load\<^sub>C)
            apply(clarsimp, drule C.seq_assign_elim)
            apply(simp add:fun_upd_twist del:fun_upd_apply)
            apply(rule C.eval\<^sub>w.seq, clarsimp)
            apply(subgoal_tac "xa \<noteq> Eg2_var\<^sub>C_of_Eg1 x \<and> xa \<noteq> reg\<^sub>C")
             apply clarsimp
             apply(simp add:fun_upd_twist reg\<^sub>C_load_helper assign_eval\<^sub>w_load\<^sub>C del:fun_upd_apply)
            apply blast
           apply(clarsimp, drule C.seq_assign_elim, clarsimp)
          apply(clarsimp, drule C.seq_assign_elim)
          using \<C>_vars\<^sub>C_def dma\<^sub>C_def by auto
        moreover from if_reg_load_rel(3,9)
        have "Eg2_var\<^sub>C_of_Eg1 x \<in> \<C>_vars\<^sub>C x\<^sub>C \<Longrightarrow> x\<^sub>C \<notin> mds\<^sub>C GuarNoReadOrWrite"
          by (metis Eg2_var\<^sub>C_of_Eg1.simps(1-2) \<C>_vars\<^sub>C_def \<C>_vars_def empty_iff has_mode\<^sub>A insert_iff inv_f_f var\<^sub>C_of_inj)

        (* We waive cases where x\<^sub>C = reg\<^sub>C by requiring \<not> GuarNoRW reg\<^sub>C and \<not> GuarNoWrite reg\<^sub>C
           which makes sense if we consider concrete-only variables like reg\<^sub>C to be private.
           Furthermore we establish that reg\<^sub>C cannot be a control var.  *)
        moreover have "x\<^sub>C = reg\<^sub>C \<Longrightarrow> ?case_x\<^sub>C"
          using if_reg_load_rel(6-7) by clarsimp
        moreover have "reg\<^sub>C \<notin> \<C>_vars\<^sub>C x\<^sub>C"
          using reg\<^sub>C_is_not_the_var\<^sub>C_of_anything \<C>_vars\<^sub>C_def by clarsimp
        ultimately show ?case_x\<^sub>C by fastforce
      qed
    next
    case (if_reg_stop_rel c\<^sub>A x then\<^sub>A else\<^sub>A tail\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
      from if_reg_stop_rel(2) show ?case
        by (metis C.seq_stop_elim C.seq_stop_eval\<^sub>w fst_conv)
    next
    case (if_reg_rel c\<^sub>A x then\<^sub>A else\<^sub>A tail\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
      from if_reg_rel.prems show ?case
      proof (clarify)
        assume respects\<^sub>A: "A.respects_own_guarantees (c\<^sub>A, mds\<^sub>A)"
        fix x\<^sub>C
        let ?case_x\<^sub>C = "(x\<^sub>C \<in> snd (c\<^sub>C, mds\<^sub>C) GuarNoReadOrWrite \<longrightarrow>
               (\<forall>mds mem c' mds' mem'.
                   (\<langle>fst (c\<^sub>C, mds\<^sub>C), mds, mem\<rangle>\<^sub>C, \<langle>c', mds', mem'\<rangle>\<^sub>C)
                   \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C \<longrightarrow>
                   (\<forall>x\<in>{x\<^sub>C} \<union> \<C>_vars\<^sub>C x\<^sub>C.
                       \<forall>v. (\<langle>fst (c\<^sub>C, mds\<^sub>C), mds, mem(x := v)\<rangle>\<^sub>C, \<langle>c', mds', mem'(x := v)\<rangle>\<^sub>C)
                           \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C))) \<and>
              (x\<^sub>C \<in> snd (c\<^sub>C, mds\<^sub>C) GuarNoWrite \<longrightarrow>
               (\<forall>mds mem c' mds' mem'.
                   (\<langle>fst (c\<^sub>C, mds\<^sub>C), mds, mem\<rangle>\<^sub>C, \<langle>c', mds', mem'\<rangle>\<^sub>C)
                   \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C \<longrightarrow>
                   mem x\<^sub>C = mem' x\<^sub>C \<and> dma\<^sub>C mem x\<^sub>C = dma\<^sub>C mem' x\<^sub>C))"
        from if_reg_rel(3,10) preserves_modes_mem_RelS_Eg1Eg2 has_mode\<^sub>A
        have "x\<^sub>C = Eg2_var\<^sub>C_of_Eg1 x \<Longrightarrow> x\<^sub>C \<notin> mds\<^sub>C GuarNoReadOrWrite" by clarsimp
        with if_reg_rel(2)
        have "x\<^sub>C = Eg2_var\<^sub>C_of_Eg1 x \<Longrightarrow> ?case_x\<^sub>C"
          apply clarsimp
          apply(drule C.seq_elim, clarsimp)
          using \<C>_vars\<^sub>C_def dma\<^sub>C_def by auto
        moreover from if_reg_rel(2)
        have "\<lbrakk>x\<^sub>C \<noteq> reg\<^sub>C; x\<^sub>C \<noteq> Eg2_var\<^sub>C_of_Eg1 x; reg\<^sub>C \<notin> \<C>_vars\<^sub>C x\<^sub>C;
            Eg2_var\<^sub>C_of_Eg1 x \<in> \<C>_vars\<^sub>C x\<^sub>C \<Longrightarrow> x\<^sub>C \<notin> mds\<^sub>C GuarNoReadOrWrite\<rbrakk> \<Longrightarrow> ?case_x\<^sub>C"
          apply safe
             apply(subgoal_tac "(mem(x\<^sub>C := v)) reg\<^sub>C = mem reg\<^sub>C")
              apply clarsimp
              apply(drule C.seq_elim, clarsimp+)
              apply(erule C.if_elim, clarsimp)
               apply(simp add: if_true_eval\<^sub>w\<^sub>C if_false_eval\<^sub>w\<^sub>C)+
            apply(subgoal_tac "xa \<noteq> Eg2_var\<^sub>C_of_Eg1 x \<and> xa \<noteq> reg\<^sub>C")
             apply(drule C.seq_elim, clarsimp+)
             apply(erule C.if_elim, clarsimp)
              apply(simp add: if_true_eval\<^sub>w\<^sub>C if_false_eval\<^sub>w\<^sub>C)+
            apply blast
           apply clarsimp
           apply(drule C.seq_elim, clarsimp+)
           apply(erule C.if_elim, clarsimp+)
          apply(drule C.seq_elim, clarsimp+)
          apply(erule C.if_elim, clarsimp+)
          done
        moreover from if_reg_rel(3,11)
        have "Eg2_var\<^sub>C_of_Eg1 x \<in> \<C>_vars\<^sub>C x\<^sub>C \<Longrightarrow> x\<^sub>C \<notin> mds\<^sub>C GuarNoReadOrWrite"
          by (metis Eg2_var\<^sub>C_of_Eg1.simps(1-2) \<C>_vars\<^sub>C_def \<C>_vars_def empty_iff has_mode\<^sub>A insert_iff inv_f_f var\<^sub>C_of_inj)
        moreover have "x\<^sub>C = reg\<^sub>C \<Longrightarrow> ?case_x\<^sub>C"
          using if_reg_rel(8-9) by clarsimp
        moreover have "reg\<^sub>C \<notin> \<C>_vars\<^sub>C x\<^sub>C"
          using reg\<^sub>C_is_not_the_var\<^sub>C_of_anything \<C>_vars\<^sub>C_def by clarsimp
        ultimately show ?case_x\<^sub>C by fastforce
      qed
    next
    case (stop_seq_rel c\<^sub>A tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
      from stop_seq_rel(2)
      show ?case by (metis C.seq_stop_elim C.seq_stop_eval\<^sub>w fst_conv)
    next
    case stop_rel
      thus ?case by (simp add: C.stop_no_eval)
  qed
qed

definition mdss\<^sub>A_of :: "((var\<^sub>C Mds) list) \<Rightarrow> ((var Mds) list)"
where
  "mdss\<^sub>A_of mdss\<^sub>C = map mds\<^sub>A_of mdss\<^sub>C"

lemma new_vars_private_RelS_Eg1Eg2:
  "sifum_refinement.new_vars_private dma\<^sub>C C.eval\<^sub>w Eg2_var\<^sub>C_of_Eg1 RelS_Eg1Eg2"
unfolding new_vars_private_def
(* Slightly more intuitive goals without simp converting \<or> to \<longrightarrow> *)
proof(clarify)
  fix c\<^sub>A mds\<^sub>A mem\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>C c\<^sub>C' mds\<^sub>C' mem\<^sub>C'
  assume in_rel: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2" and
      does_eval: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>C', mds\<^sub>C', mem\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
  let "?diff_mem v\<^sub>C" = "mem\<^sub>C' v\<^sub>C \<noteq> mem\<^sub>C v\<^sub>C"
  let "?diff_dma v\<^sub>C" = "dma\<^sub>C mem\<^sub>C' v\<^sub>C < dma\<^sub>C mem\<^sub>C v\<^sub>C"
  let "?conc_only v\<^sub>C" = "v\<^sub>C \<notin> range Eg2_var\<^sub>C_of_Eg1"
  show "(\<forall>v\<^sub>C. (?diff_mem v\<^sub>C \<or> ?diff_dma v\<^sub>C) \<and> ?conc_only v\<^sub>C \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite) \<and>
         mds\<^sub>C AsmNoReadOrWrite - range Eg2_var\<^sub>C_of_Eg1
         \<subseteq> mds\<^sub>C' AsmNoReadOrWrite - range Eg2_var\<^sub>C_of_Eg1" (* not sure what to call this one *)
  using in_rel does_eval
  proof(cases rule:RelS_Eg1Eg2.cases)
  case (acq_mode_rel x SomeMode tail\<^sub>A tail\<^sub>C)
    moreover with does_eval
    have "mds\<^sub>C' = mds\<^sub>C (SomeMode := insert (Eg2_var\<^sub>C_of_Eg1 x) (mds\<^sub>C SomeMode))"
      by (metis (mono_tags) C.seq_decl_elim C.update_modes.simps(1))
    ultimately show ?thesis
      by simp
  next
  case (rel_mode_rel x SomeMode)
    moreover with does_eval
    have "mds\<^sub>C' = mds\<^sub>C (SomeMode := {y. y \<in> (mds\<^sub>C SomeMode) \<and> y \<noteq> (Eg2_var\<^sub>C_of_Eg1 x)})"
      by (metis (mono_tags) C.upd_elim C.skip_elim C.update_modes.simps(2))
    ultimately show ?thesis
      by auto
  next
  case (assign_load_rel x y tail\<^sub>A tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis C.assign_elim C.seq_elim Stmt.distinct(14) set_eq_subset)
  next
  case (assign_const_rel x z tail\<^sub>A tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis C.assign_elim C.seq_elim Stmt.distinct(14) set_eq_subset)
  next
  case (if_reg_load_rel x then\<^sub>A else\<^sub>A tail\<^sub>A then\<^sub>C else\<^sub>C tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis C.assign_elim C.seq_elim Stmt.distinct(14) set_eq_subset)
  next
  case (if_reg_stop_rel x then\<^sub>A else\<^sub>A tail\<^sub>A then\<^sub>C else\<^sub>C tail\<^sub>C)
    with does_eval
    show ?thesis
      by (metis C.seq_stop_elim subset_refl)
  next
  case (if_reg_rel x then\<^sub>A else\<^sub>A tail\<^sub>A then\<^sub>C else\<^sub>C tail\<^sub>C)
    with does_eval
    have mds\<^sub>C_unchanged: "mds\<^sub>C = mds\<^sub>C'"
      by (metis C.if_elim C.seq_elim Stmt.distinct(50))
    moreover with if_reg_rel(5)
    have "\<forall>v\<^sub>C. (?diff_mem v\<^sub>C \<or> ?diff_dma v\<^sub>C) \<and> ?conc_only v\<^sub>C \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite"
      by simp
    moreover from mds\<^sub>C_unchanged
    have "mds\<^sub>C AsmNoReadOrWrite - range Eg2_var\<^sub>C_of_Eg1 \<subseteq> mds\<^sub>C' AsmNoReadOrWrite - range Eg2_var\<^sub>C_of_Eg1"
      by clarify
    ultimately show ?thesis
      by simp
  next
  case (stop_seq_rel tail\<^sub>A tail\<^sub>C)
    with does_eval C.seq_stop_elim
    show ?thesis
      by blast
  next
  case (stop_rel)
    with does_eval C.stop_no_eval have False by simp
    thus ?thesis by simp
  qed
qed

lemma simple_refinement_safe_RelS_Eg1Eg2:
assumes R_low_mds_eq:
  "\<And>c mds mem mem'. (\<langle>c, mds, mem\<rangle>\<^sub>A, \<langle>c, mds, mem'\<rangle>\<^sub>A) \<in> Some_R \<Longrightarrow> A.low_mds_eq mds mem mem'"
shows
  "sifum_refinement.simple_refinement_safe C.eval\<^sub>w Some_R RelS_Eg1Eg2 abs_steps"
unfolding simple_refinement_safe_def
proof(clarsimp)
  fix c\<^sub>A mds\<^sub>A mem\<^sub>1\<^sub>A mem\<^sub>2\<^sub>A c\<^sub>C mds\<^sub>C mem\<^sub>1\<^sub>C mem\<^sub>2\<^sub>C
  assume in_R: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A) \<in> Some_R" and
       in_RelS_1: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2" and
       in_RelS_2: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>2\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
  show "stops\<^sub>C \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C = stops\<^sub>C \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C \<and>
       (\<forall>mds\<^sub>1\<^sub>C' mds\<^sub>2\<^sub>C' mem\<^sub>1\<^sub>C' mem\<^sub>2\<^sub>C' c\<^sub>1\<^sub>C' c\<^sub>2\<^sub>C'.
           (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>1\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w \<and>
           (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>2\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w  \<longrightarrow>
           c\<^sub>1\<^sub>C' = c\<^sub>2\<^sub>C' \<and> mds\<^sub>1\<^sub>C' = mds\<^sub>2\<^sub>C')"
  using in_RelS_1 in_RelS_2
  proof(cases rule:RelS_Eg1Eg2.cases)
  case (acq_mode_rel x m tail\<^sub>A tail\<^sub>C)
    let ?mds\<^sub>C' = "mds\<^sub>C(m := insert (Eg2_var\<^sub>C_of_Eg1 x) (mds\<^sub>C m))"
    from acq_mode_rel have
    eval_1: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; tail\<^sub>C, ?mds\<^sub>C', mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w" and
    eval_2: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; tail\<^sub>C, ?mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp add: C.decl_eval\<^sub>w' C.eval\<^sub>w.seq)+
    thus ?thesis unfolding stops\<^sub>C_def using C.eval_det by blast
  next
  case (rel_mode_rel x m)
    let ?mds\<^sub>C' = "mds\<^sub>C(m := {y. y \<in> (mds\<^sub>C m) \<and> y \<noteq> (Eg2_var\<^sub>C_of_Eg1 x)})"
    from rel_mode_rel have
    eval_1: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>Stop, ?mds\<^sub>C', mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w" and
    eval_2: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop, ?mds\<^sub>C', mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp add: C.decl_eval\<^sub>w')+
    thus ?thesis unfolding stops\<^sub>C_def using C.eval_det by blast
  next
  case (assign_load_rel x y tail\<^sub>A tail\<^sub>C)
    from assign_load_rel have
    eval_1: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; tail\<^sub>C, mds\<^sub>C,
               mem\<^sub>1\<^sub>C((Eg2_var\<^sub>C_of_Eg1 x) := mem\<^sub>1\<^sub>C (Eg2_var\<^sub>C_of_Eg1 y))\<rangle>\<^sub>C) \<in> C.eval\<^sub>w" and
    eval_2: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; tail\<^sub>C, mds\<^sub>C,
               mem\<^sub>2\<^sub>C((Eg2_var\<^sub>C_of_Eg1 x) := mem\<^sub>2\<^sub>C (Eg2_var\<^sub>C_of_Eg1 y))\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp add: assign_eval\<^sub>w_load\<^sub>C C.eval\<^sub>w.seq)+
    thus ?thesis unfolding stops\<^sub>C_def using C.eval_det by blast
  next
  case (assign_const_rel x z tail\<^sub>A tail\<^sub>C)
    from assign_const_rel have
    eval_1: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; tail\<^sub>C, mds\<^sub>C,
               mem\<^sub>1\<^sub>C((Eg2_var\<^sub>C_of_Eg1 x) := z)\<rangle>\<^sub>C) \<in> C.eval\<^sub>w" and
    eval_2: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; tail\<^sub>C, mds\<^sub>C,
               mem\<^sub>2\<^sub>C((Eg2_var\<^sub>C_of_Eg1 x) := z)\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp add: assign_eval\<^sub>w_const\<^sub>C C.eval\<^sub>w.seq)+
    thus ?thesis unfolding stops\<^sub>C_def using C.eval_det by blast
  next
  case (if_reg_load_rel x then\<^sub>A else\<^sub>A tail\<^sub>A then\<^sub>C else\<^sub>C tail\<^sub>C)
    from if_reg_load_rel have
    eval_1: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; Stmt.If (bexp\<^sub>C.Eq reg\<^sub>C 0) then\<^sub>C else\<^sub>C ;; tail\<^sub>C, mds\<^sub>C,
               mem\<^sub>1\<^sub>C(reg\<^sub>C := mem\<^sub>1\<^sub>C (Eg2_var\<^sub>C_of_Eg1 x))\<rangle>\<^sub>C) \<in> C.eval\<^sub>w" and
    eval_2: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>Stop ;; Stmt.If (bexp\<^sub>C.Eq reg\<^sub>C 0) then\<^sub>C else\<^sub>C ;; tail\<^sub>C, mds\<^sub>C,
               mem\<^sub>2\<^sub>C(reg\<^sub>C := mem\<^sub>2\<^sub>C (Eg2_var\<^sub>C_of_Eg1 x))\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp add: assign_eval\<^sub>w_load\<^sub>C C.eval\<^sub>w.seq)+
    thus ?thesis unfolding stops\<^sub>C_def using C.eval_det by blast
  next
  case (if_reg_stop_rel x then\<^sub>A else\<^sub>A tail\<^sub>A then\<^sub>C else\<^sub>C tail\<^sub>C)
    from if_reg_stop_rel have
    eval_1: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C,
              \<langle>Stmt.If (bexp\<^sub>C.Eq reg\<^sub>C 0) then\<^sub>C else\<^sub>C ;; tail\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w" and
    eval_2: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
              \<langle>Stmt.If (bexp\<^sub>C.Eq reg\<^sub>C 0) then\<^sub>C else\<^sub>C ;; tail\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp add: C.seq_stop_eval\<^sub>w)+
    thus ?thesis unfolding stops\<^sub>C_def using C.eval_det by blast
  next
  case (if_reg_rel x then\<^sub>A else\<^sub>A tail\<^sub>A then\<^sub>C else\<^sub>C tail\<^sub>C)
    from if_reg_rel have
    eval_1: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C,
              \<langle>(if ev\<^sub>B\<^sub>C mem\<^sub>1\<^sub>C (bexp\<^sub>C.Eq reg\<^sub>C 0) then then\<^sub>C else else\<^sub>C) ;; tail\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w" and
    eval_2: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C,
              \<langle>(if ev\<^sub>B\<^sub>C mem\<^sub>2\<^sub>C (bexp\<^sub>C.Eq reg\<^sub>C 0) then then\<^sub>C else else\<^sub>C) ;; tail\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp add: if_true_eval\<^sub>w\<^sub>C if_false_eval\<^sub>w\<^sub>C)+
    hence stops_eq: "stops\<^sub>C \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C = stops\<^sub>C \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C"
      unfolding stops\<^sub>C_def by blast
    (* Side-conditions ensure both programs take the same branch *)
    from in_R R_low_mds_eq
    have "A.low_mds_eq mds\<^sub>A mem\<^sub>1\<^sub>A mem\<^sub>2\<^sub>A" by clarsimp
    with if_reg_rel(6,13) dma_def
    have "ev\<^sub>B mem\<^sub>1\<^sub>A (bexp.Eq x 0) = ev\<^sub>B mem\<^sub>2\<^sub>A (bexp.Eq x 0)"
      by (simp add:A.low_mds_eq_def)
    with if_reg_rel(1,2,7) in_RelS_2
    have "ev\<^sub>B\<^sub>C mem\<^sub>1\<^sub>C (bexp\<^sub>C.Eq reg\<^sub>C 0) = ev\<^sub>B\<^sub>C mem\<^sub>2\<^sub>C (bexp\<^sub>C.Eq reg\<^sub>C 0)"
      apply clarsimp
      by (cases rule:RelS_Eg1Eg2.cases, simp+)
    with if_reg_rel(1,2) eval_1 eval_2 C.eval_det have
      "(\<forall>mds\<^sub>1\<^sub>C' mds\<^sub>2\<^sub>C' mem\<^sub>1\<^sub>C' mem\<^sub>2\<^sub>C' c\<^sub>1\<^sub>C' c\<^sub>2\<^sub>C'.
           (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>1\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C \<and>
           (\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>2\<^sub>C', mds\<^sub>2\<^sub>C', mem\<^sub>2\<^sub>C'\<rangle>\<^sub>C) \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C \<longrightarrow>
           c\<^sub>1\<^sub>C' = c\<^sub>2\<^sub>C' \<and> mds\<^sub>1\<^sub>C' = mds\<^sub>2\<^sub>C')"
      by (clarsimp, blast)
    thus ?thesis using stops_eq by simp
  next
  case (stop_seq_rel tail\<^sub>A tail\<^sub>C)
    from stop_seq_rel have
    eval_1: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>tail\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w" and
    eval_2: "(\<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C, \<langle>tail\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C) \<in> C.eval\<^sub>w"
      by (simp add: C.seq_stop_eval\<^sub>w)+
    thus ?thesis unfolding stops\<^sub>C_def using C.eval_det by blast
  next
  case stop_rel
    with C.stop_no_eval have
      stops_1: "stops\<^sub>C \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C" and
      stops_2: "stops\<^sub>C \<langle>c\<^sub>C, mds\<^sub>C, mem\<^sub>2\<^sub>C\<rangle>\<^sub>C"
      unfolding stops\<^sub>C_def by simp+
    thus ?thesis unfolding stops\<^sub>C_def by auto
  qed
qed

lemma induction_RelS_Eg1Eg2:
notes A.update_modes.simps[simp del]
shows
"(\<langle>c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2 \<Longrightarrow>
       (\<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> C.eval\<^sub>w \<Longrightarrow>
       \<exists>c\<^sub>1\<^sub>A' mds\<^sub>A' mem\<^sub>1\<^sub>A'.
          A.neval \<langle>c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A
           (abs_steps \<langle>c\<^sub>1\<^sub>A, mds\<^sub>A, mem\<^sub>1\<^sub>A\<rangle>\<^sub>A \<langle>c\<^sub>1\<^sub>C, mds\<^sub>C, mem\<^sub>1\<^sub>C\<rangle>\<^sub>C)
           \<langle>c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A \<and>
          (\<langle>c\<^sub>1\<^sub>A', mds\<^sub>A', mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
proof(induct rule: RelS_Eg1Eg2.induct)
case (acq_mode_rel c\<^sub>A x m tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  let ?c\<^sub>1\<^sub>A' = "Stop ;; tail\<^sub>A"
  from acq_mode_rel(1,2)
  have abs_steps_acq: "(abs_steps' c\<^sub>A c\<^sub>C) = 1"
    by (simp add:abs_steps'_def)
  moreover from acq_mode_rel.prems acq_mode_rel(2)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (Stop ;; tail\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C(m := insert (Eg2_var\<^sub>C_of_Eg1 x) (mds\<^sub>C m))" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    by (metis (mono_tags) C.seq_decl_elim C.update_modes.simps(1))+
  moreover from mds\<^sub>C'_def
  have mds\<^sub>A'_def: "?mds\<^sub>A' = A.update_modes (x +=\<^sub>m m) (mds\<^sub>A_of mds\<^sub>C)"
    unfolding A.update_modes.simps
    by(blast intro: mode_acquire_refinement_helper)
  moreover with mem\<^sub>1\<^sub>C'_def acq_mode_rel A.eval\<^sub>w.seq A.decl_eval\<^sub>w
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 1 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A"
    by clarsimp
  moreover from acq_mode_rel(5)
  have mds\<^sub>C'_concrete_vars_unwritable:
    "(\<forall>v\<^sub>C. v\<^sub>C \<notin> range Eg2_var\<^sub>C_of_Eg1 \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite)"
    by(auto simp: mds\<^sub>C'_def)
  moreover with acq_mode_rel(6)[simplified] acq_mode_rel.hyps(4) neval\<^sub>A c\<^sub>1\<^sub>C'_def
  have in_Rel': "(\<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    by (metis A.neval_Suc_simp One_nat_def acq_mode_rel.prems)
  ultimately show ?case
    by (metis (no_types, hide_lams) One_nat_def abs_steps.simps n_not_Suc_n)
next
case (rel_mode_rel c\<^sub>A x m c\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  let ?c\<^sub>1\<^sub>A' = "Stop"
  from rel_mode_rel(1,2)
  have abs_steps_acq: "(abs_steps' c\<^sub>A c\<^sub>C) = 1"
    by (simp add:abs_steps'_def)
  moreover from rel_mode_rel.prems rel_mode_rel(2)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = Stop" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C(m := {y. y \<in> (mds\<^sub>C m) \<and> y \<noteq> (Eg2_var\<^sub>C_of_Eg1 x)})" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    by (metis (mono_tags) C.upd_elim C.skip_elim C.update_modes.simps(2))+
  moreover from mds\<^sub>C'_def
  have mds\<^sub>A'_def: "?mds\<^sub>A' = A.update_modes (x -=\<^sub>m m) (mds\<^sub>A_of mds\<^sub>C)"
    unfolding A.update_modes.simps
    by(blast intro: mode_release_refinement_helper)
  moreover with mem\<^sub>1\<^sub>C'_def rel_mode_rel A.eval\<^sub>w.seq A.decl_eval\<^sub>w
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 1 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A"
    by clarsimp
  moreover from rel_mode_rel(5)
  have mds\<^sub>C'_concrete_vars_unwritable:
    "(\<forall>v\<^sub>C. v\<^sub>C \<notin> range Eg2_var\<^sub>C_of_Eg1 \<longrightarrow> v\<^sub>C \<in> mds\<^sub>C' AsmNoReadOrWrite)"
    by(auto simp: mds\<^sub>C'_def)
  moreover with rel_mode_rel(6)[simplified] rel_mode_rel.hyps(4) neval\<^sub>A c\<^sub>1\<^sub>C'_def
  have in_Rel': "(\<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    by (metis A.neval_Suc_simp One_nat_def rel_mode_rel.prems)
  ultimately show ?case
    by (metis (no_types, hide_lams) One_nat_def abs_steps.simps n_not_Suc_n)
next
case (assign_load_rel c\<^sub>A x y tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "Stop ;; tail\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from assign_load_rel(1,2)
  have abs_steps_load: "(abs_steps' c\<^sub>A c\<^sub>C) = 1"
    by (simp add:abs_steps'_def)
  from assign_load_rel.prems assign_load_rel(2)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (Stop ;; tail\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C((Eg2_var\<^sub>C_of_Eg1 x) := mem\<^sub>C (Eg2_var\<^sub>C_of_Eg1 y))"
    using C.seq_elim C.assign_elim C.skip_elim assign_eval\<^sub>w_load\<^sub>C
    by (metis (no_types, lifting) Stmt.distinct(14))+
  from assign_load_rel(1,3,4) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have eval\<^sub>A: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A,\<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w" and
    neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 1 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A"
    using A.eval\<^sub>w.seq assign_eval\<^sub>w_load\<^sub>A mem_assign_refinement_helper_var by simp+
  with assign_load_rel(11)[simplified] assign_load_rel.prems c\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    using assign_load_rel.hyps(4-5) mds\<^sub>C'_def by blast
  thus ?case using rel' abs_steps_load neval\<^sub>A by auto
next
case (assign_const_rel c\<^sub>A x z tail\<^sub>A c\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "Stop ;; tail\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from assign_const_rel(1,2)
  have abs_steps_const: "(abs_steps' c\<^sub>A c\<^sub>C) = 1"
    by (simp add:abs_steps'_def)
  from assign_const_rel.prems assign_const_rel(2)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (Stop ;; tail\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C((Eg2_var\<^sub>C_of_Eg1 x) := z)"
    using C.seq_elim C.assign_elim C.skip_elim assign_eval\<^sub>w_const\<^sub>C
    by (metis (no_types, lifting) Stmt.distinct(14))+
  from assign_const_rel(1,3,4) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have eval\<^sub>A: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A,\<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w" and
    neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 1 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A"
    using A.eval\<^sub>w.seq assign_eval\<^sub>w_const\<^sub>A mem_assign_refinement_helper_const by simp+
  with assign_const_rel(9)[simplified] assign_const_rel.prems c\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    using assign_const_rel.hyps(4) by blast
  thus ?case using rel' abs_steps_const neval\<^sub>A by auto
next
case (if_reg_load_rel c\<^sub>A x then\<^sub>A else\<^sub>A tail\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_reg_load_rel.hyps(1,2)
  have abs_steps_if_reg_load: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_reg_load_rel.prems if_reg_load_rel(2)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (Stop ;; If (Eq reg\<^sub>C 0) then\<^sub>C else\<^sub>C ;; tail\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C(reg\<^sub>C := mem\<^sub>C (Eg2_var\<^sub>C_of_Eg1 x))"
    using C.seq_elim C.assign_elim C.skip_elim assign_eval\<^sub>w_load\<^sub>C
    by (metis (no_types, lifting) Stmt.distinct(14))+
  from if_reg_load_rel(1-4) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using reg\<^sub>C_not_visible_abs conc_only_var_assign_not_visible_abs A.neval.intros(1) by simp+
  with if_reg_load_rel c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
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
  show ?case using rel' abs_steps_if_reg_load neval\<^sub>A by auto
next
case (if_reg_stop_rel c\<^sub>A x then\<^sub>A else\<^sub>A tail\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "c\<^sub>A"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_reg_stop_rel.hyps(1,2)
  have abs_steps_if_reg_stop: "(abs_steps' c\<^sub>A c\<^sub>C) = 0"
    by (simp add:abs_steps'_def)
  from if_reg_stop_rel.prems if_reg_stop_rel(2)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (If (Eq reg\<^sub>C 0) then\<^sub>C else\<^sub>C ;; tail\<^sub>C)" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    using C.seq_stop_elim by simp+
  from if_reg_stop_rel(1-4) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 0 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    mem\<^sub>A_unchanged: "?mem\<^sub>1\<^sub>A' = mem\<^sub>A"
    using reg\<^sub>C_not_visible_abs conc_only_var_assign_not_visible_abs A.neval.intros(1) by simp+
  with if_reg_stop_rel c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A,\<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2" by blast
  show ?case using rel' abs_steps_if_reg_stop neval\<^sub>A by auto
next
case (if_reg_rel c\<^sub>A x then\<^sub>A else\<^sub>A tail\<^sub>A c\<^sub>C then\<^sub>C else\<^sub>C tail\<^sub>C mds\<^sub>A mds\<^sub>C mem\<^sub>A mem\<^sub>C)
  let ?c\<^sub>1\<^sub>A' = "if (ev\<^sub>B mem\<^sub>A (bexp.Eq x 0)) then (then\<^sub>A ;; tail\<^sub>A) else (else\<^sub>A ;; tail\<^sub>A)"
  let ?mds\<^sub>A' = "mds\<^sub>A_of mds\<^sub>C'"
  let ?mem\<^sub>1\<^sub>A' = "mem\<^sub>A_of mem\<^sub>1\<^sub>C'"
  from if_reg_rel(1) if_reg_rel(2)
  have abs_steps_if_reg: "(abs_steps' c\<^sub>A c\<^sub>C) = Suc 0"
    by (simp add:abs_steps'_def)
  from if_reg_rel.prems if_reg_rel(2)
  have c\<^sub>1\<^sub>C'_def: "c\<^sub>1\<^sub>C' = (if (ev\<^sub>B\<^sub>C mem\<^sub>C (bexp\<^sub>C.Eq reg\<^sub>C 0)) then (then\<^sub>C ;; tail\<^sub>C) else (else\<^sub>C ;; tail\<^sub>C))" and
    mds\<^sub>C'_def: "mds\<^sub>C' = mds\<^sub>C" and
    mem\<^sub>1\<^sub>C'_def: "mem\<^sub>1\<^sub>C' = mem\<^sub>C"
    apply simp_all
    by (drule C.seq_elim, simp, erule exE, clarsimp, erule C.if_elim, clarsimp+)+
  from if_reg_rel(1,3,4) mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def
  have eval\<^sub>A: "(\<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A, \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A) \<in> A.eval\<^sub>w"
    using if_seq_eval\<^sub>w_helper\<^sub>A A.if_eval\<^sub>w by presburger
  hence neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A (abs_steps' c\<^sub>A c\<^sub>C) \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A"
    using abs_steps_if_reg by (simp only:A.neval_Suc_simp)
  from if_reg_rel(3,4,7,12) if_reg_rel.prems c\<^sub>1\<^sub>C'_def mds\<^sub>C'_def mem\<^sub>1\<^sub>C'_def eval\<^sub>A
  have rel': "(\<langle>?c\<^sub>1\<^sub>A',?mds\<^sub>A',?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C',mds\<^sub>C',mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    by (clarify, presburger)
  show ?case using rel' abs_steps_if_reg neval\<^sub>A by auto
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
  hence
    neval\<^sub>A: "A.neval \<langle>c\<^sub>A, mds\<^sub>A, mem\<^sub>A\<rangle>\<^sub>A 1 \<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A" and
    rel': "(\<langle>?c\<^sub>1\<^sub>A', ?mds\<^sub>A', ?mem\<^sub>1\<^sub>A'\<rangle>\<^sub>A, \<langle>c\<^sub>1\<^sub>C', mds\<^sub>C', mem\<^sub>1\<^sub>C'\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
    using stop_seq_rel A.seq_stop_eval\<^sub>w by auto
  thus ?case using abs_steps_stop by auto
next
case stop_rel
  with C.stop_no_eval have False by simp
  thus ?case by simp
qed

definition
  mds\<^sub>0 :: "Mode \<Rightarrow> var\<^sub>C set"
where
  "mds\<^sub>0 \<equiv> \<lambda>m. case m of AsmNoReadOrWrite \<Rightarrow> {reg\<^sub>C} | _ \<Rightarrow> {}"

lemma read_buffer_assign_temp_onwards_RelS:
  "(\<langle>(temp \<leftarrow> aexp.Const 0) ;; (Skip@[temp -=\<^sub>m AsmNoReadOrWrite]),
         mds\<^sub>A_of ((case_Mode {reg\<^sub>C} {} {} {}) (AsmNoWrite := {control_var\<^sub>C},
                  AsmNoReadOrWrite := {temp\<^sub>C, reg\<^sub>C})),
         mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A,
        \<langle>(temp\<^sub>C \<leftarrow> aexp\<^sub>C.Const 0) ;; (Skip@[temp\<^sub>C -=\<^sub>m AsmNoReadOrWrite]),
                  (case_Mode {reg\<^sub>C} {} {} {}) (AsmNoWrite := {control_var\<^sub>C},
                  AsmNoReadOrWrite := {temp\<^sub>C, reg\<^sub>C}),
                  mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
  (* Assign temp (Const 0) ;; *)
  apply(rule assign_const_rel, simp+)
   apply(clarsimp simp: reg\<^sub>C_the_only_concrete_only_var doesnt_have_mode)+
  apply(drule C.seq_assign_elim, clarsimp)
  apply(rule stop_seq_rel, simp+)
  (* ModeDecl Skip (Rel temp AsmNoReadOrWrite)" *)
  apply(rule rel_mode_rel, simp+)
   apply(clarsimp simp: reg\<^sub>C_the_only_concrete_only_var)+
  apply(rule stop_rel)
  done

lemma read_buffer_RelS:
  "(\<langle>A.read_buffer, mds\<^sub>A_of mds\<^sub>0, mem\<^sub>A_of mem\<^sub>C\<rangle>\<^sub>A, \<langle>C.read_buffer\<^sub>C, mds\<^sub>0, mem\<^sub>C\<rangle>\<^sub>C) \<in> RelS_Eg1Eg2"
  unfolding A.read_buffer_def C.read_buffer\<^sub>C_def mds\<^sub>0_def
  (* ModeDecl Skip (Acq buffer AsmNoWrite) ;; *)
  apply(rule acq_mode_rel, simp+)
   apply(clarsimp simp: reg\<^sub>C_the_only_concrete_only_var)+
  apply(drule C.seq_decl_elim, clarsimp)
  apply(rule stop_seq_rel, simp+)
  (* ModeDecl Skip (Acq temp AsmNoReadOrWrite) ;; *)
  apply(rule acq_mode_rel, simp+)
   apply(clarsimp simp: reg\<^sub>C_the_only_concrete_only_var)+
  apply(drule C.seq_decl_elim, clarsimp)
  apply(rule stop_seq_rel, simp+)
  (* Assign temp (Load buffer) ;; *)
  apply(rule assign_load_rel, simp+)
   apply(clarsimp simp: reg\<^sub>C_the_only_concrete_only_var doesnt_have_mode)+
  apply(drule C.seq_assign_elim, clarsimp)
  apply(rule stop_seq_rel, simp+)
  (* If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp)) ;; *)
  apply(rule if_reg_load_rel, simp+)
   apply(clarsimp simp: reg\<^sub>C_the_only_concrete_only_var doesnt_have_mode)+
  apply(drule C.seq_assign_elim, clarsimp)
  apply(rule if_reg_stop_rel, simp+)
     apply(clarsimp simp: reg\<^sub>C_the_only_concrete_only_var)
    using has_mode\<^sub>A NoRW\<^sub>A_implies_NoRW\<^sub>C apply fastforce
   apply(clarsimp simp: has_mode\<^sub>A)+
  apply(rule if_reg_rel, simp+)
     apply(clarsimp simp: reg\<^sub>C_the_only_concrete_only_var has_mode\<^sub>A doesnt_have_mode)+
   apply(rule conjI)
    (* (Assign low_var (Load temp)) ;; *)
    apply clarsimp
    apply(rule assign_load_rel, simp+)
     apply(clarsimp simp: reg\<^sub>C_the_only_concrete_only_var doesnt_have_mode)+
     apply(drule C.seq_assign_elim, clarsimp)
    apply(rule stop_seq_rel, simp+)
    apply(rule read_buffer_assign_temp_onwards_RelS)
   (* (Assign high_var (Load temp)) ;; *)
   apply clarsimp
   apply(rule assign_load_rel, simp+)
    apply(clarsimp simp: reg\<^sub>C_the_only_concrete_only_var doesnt_have_mode)+
    apply(drule C.seq_assign_elim, clarsimp)
   apply(rule stop_seq_rel, simp+)
   apply(rule read_buffer_assign_temp_onwards_RelS)
  apply simp
  done

lemma control_var_visible:
  "control_var\<^sub>C \<in> range Eg2_var\<^sub>C_of_Eg1"
  apply(unfold Eg2_var\<^sub>C_of_Eg1_def)
  apply(rule_tac x=control_var in range_eqI)
  apply clarsimp
  done

lemma mds\<^sub>s_A_of_mds\<^sub>0:
  "mds\<^sub>s = mds\<^sub>A_of mds\<^sub>0"
  apply(rule preserves_modes_mem_mds\<^sub>A_simp)
  apply clarsimp
  apply(case_tac m)
     unfolding mds\<^sub>s_def mds\<^sub>0_def mds\<^sub>A_of_def
     apply(clarsimp simp: reg\<^sub>C_not_visible_abs control_var_visible)+
  done

lemma A_of_mds\<^sub>0_is_mds\<^sub>s:
  "mds\<^sub>A_of mds\<^sub>0 = mds\<^sub>s"
  by (simp add: mds\<^sub>s_A_of_mds\<^sub>0)

(* using the bisimulation established by the type system *)

lemma RelS_Eg1Eg2_secure_refinement_simple_\<R>:
  "secure_refinement_simple (A.\<R> \<Gamma> \<S> P) RelS_Eg1Eg2 abs_steps"
  apply(unfold secure_refinement_simple_def)
  apply(rule conjI)
   apply(rule closed_others_RelS_Eg1Eg2)
  apply(rule conjI)
   apply(rule preserves_modes_mem_RelS_Eg1Eg2)
  apply(rule conjI)
   apply(rule new_vars_private_RelS_Eg1Eg2)
  apply(rule conjI)
   apply(rule simple_refinement_safe_RelS_Eg1Eg2)
   using A.\<R>_to_\<R>\<^sub>3 A.\<R>\<^sub>3_mem_eq apply fast
  apply(rule conjI)
   apply(rule bisim_simple_\<R>)
  apply safe
  apply(drule (1) induction_RelS_Eg1Eg2, clarify)
  done

lemma RelS_Eg1Eg2_secure_refinement_\<R>:
  "secure_refinement (A.\<R> \<Gamma> \<S> P) RelS_Eg1Eg2 \<I>simple"
  apply(rule secure_refinement_simpler)
  apply(rule secure_refinement_simple)
  apply(rule RelS_Eg1Eg2_secure_refinement_simple_\<R>)
  done

lemma strong_low_bisim_mm_R\<^sub>C_of_RelS_\<R>:
  "conc.strong_low_bisim_mm (R\<^sub>C_of (A.\<R> \<Gamma> \<S> P) RelS_Eg1Eg2 \<I>simple)"
  apply(rule R\<^sub>C_of_strong_low_bisim_mm)
    apply(rule A.\<R>_bisim)
   apply(rule RelS_Eg1Eg2_secure_refinement_\<R>)
  apply(simp add: sym_def \<I>simple_def)
  done

lemma read_buffer\<^sub>C_secure:
  "conc.low_mds_eq mds\<^sub>0 mem\<^sub>1 mem\<^sub>2 \<Longrightarrow> \<exists> \<Gamma>' \<S>' P'.
   (\<langle>C.read_buffer\<^sub>C, mds\<^sub>0, mem\<^sub>1\<rangle>\<^sub>C, \<langle>C.read_buffer\<^sub>C, mds\<^sub>0, mem\<^sub>2\<rangle>\<^sub>C) \<in> (R\<^sub>C_of (A.\<R> \<Gamma>' \<S>' P') RelS_Eg1Eg2 \<I>simple)"
  apply(insert A.read_buffer_typed[OF HOL.refl HOL.refl HOL.refl])
  apply clarsimp
  apply(rule_tac x=\<Gamma>' in exI)
  apply(rule_tac x=a in exI)
  apply(rule_tac x=b in exI)
  apply(rule_tac x=x in exI)
  apply(clarsimp simp: R\<^sub>C_of_def)
  apply(rule_tac x=A.read_buffer in exI)
  apply(rule_tac x="mds\<^sub>A_of mds\<^sub>0" in exI)
  apply(rule_tac x="mem\<^sub>A_of mem\<^sub>1" in exI)
  apply(rule conjI)
   apply(rule read_buffer_RelS)
  apply(rule_tac x=A.read_buffer in exI)
  apply(rule_tac x="mds\<^sub>A_of mds\<^sub>0" in exI)
  apply(rule_tac x="mem\<^sub>A_of mem\<^sub>2" in exI)
  apply(rule conjI)
   apply(rule read_buffer_RelS)
  apply(simp add: A_of_mds\<^sub>0_is_mds\<^sub>s \<I>simple_def)
  apply(drule low_mds_eq_from_conc_to_abs)
  apply(rule A.Typed_in_\<R>, simp)
      unfolding A.tyenv_wellformed_def apply safe
       unfolding A.mds_consistent_def apply clarsimp
      unfolding A.types_wellformed_def mds\<^sub>s_def apply simp
     unfolding A.types_stable_def apply simp
    apply clarsimp
    (* should be easy: low_mds_eq and low var \<longrightarrow> equal mem var *)
    unfolding A.low_mds_eq_def apply clarsimp
    apply(rename_tac v, erule_tac x=v in allE)
    apply clarsimp
    apply safe
     apply(clarsimp simp: mds\<^sub>A_of_def mds\<^sub>0_def)
     apply(rename_tac xb, case_tac xb, simp_all)
    apply(case_tac v, clarsimp)
       unfolding dma_def mds\<^sub>0_def mds\<^sub>A_of_def pred_def
       using reg\<^sub>C_not_visible_abs apply auto[4]
   using A.pred_def apply clarsimp
  using A.pred_def apply clarsimp
  done

lemma "conc.com_sifum_secure (C.read_buffer\<^sub>C, mds\<^sub>0)"
  unfolding conc.com_sifum_secure_def conc.low_indistinguishable_def
  apply clarify
  apply(drule_tac read_buffer\<^sub>C_secure)
  apply(erule exE)+
  apply(rule conc.mm_equiv_intro)
   apply(rule_tac \<Gamma>=\<Gamma>' and \<S>=\<S>' and P=P' in strong_low_bisim_mm_R\<^sub>C_of_RelS_\<R>)
  by simp

end

end
