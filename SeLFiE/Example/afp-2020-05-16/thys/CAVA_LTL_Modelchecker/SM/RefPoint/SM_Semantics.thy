section \<open>Semantics of SM\<close>
theory SM_Semantics
imports SM_State SM_Cfg Gen_Scheduler
begin

  section \<open>Evaluation of Expressions\<close>
  subsection \<open>Basic operations\<close>
  text \<open>Attention: Silently overflows, using 2's complement.
    This should match Java-semantics. In C, signed overflow is undefined!\<close>
  primrec eval_bin_op :: "bin_op \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
    "eval_bin_op bo_plus v1 v2 = v1+v2"
  | "eval_bin_op bo_minus v1 v2 = v1-v2"
  | "eval_bin_op bo_mul v1 v2 = v1*v2"
  | "eval_bin_op bo_div v1 v2 = v1 sdiv v2"
  | "eval_bin_op bo_mod v1 v2 = v1 smod v2"
  | "eval_bin_op bo_less v1 v2 = val_of_bool (v1 < v2)"
  | "eval_bin_op bo_less_eq v1 v2 = val_of_bool (v1 \<le> v2)"
  | "eval_bin_op bo_eq v1 v2 = val_of_bool (v1 = v2)"
  | "eval_bin_op bo_and v1 v2 = v1 AND v2"
  | "eval_bin_op bo_or v1 v2 = v1 OR v2"
  | "eval_bin_op bo_xor v1 v2 = v1 XOR v2"

  primrec eval_un_op :: "un_op \<Rightarrow> val \<Rightarrow> val" where
    "eval_un_op uo_minus v = -v"  \<comment> \<open>Attention: Silently overflows. @{term "-min_int = min_int"}!\<close>
  | "eval_un_op uo_not v = NOT v"
  
  subsection \<open>Expressions\<close>
  abbreviation exists_var :: "valuation \<Rightarrow> ident \<Rightarrow> bool" where
    "exists_var s x \<equiv> x \<in> dom s"

  abbreviation update_var :: "ident \<Rightarrow> val \<Rightarrow> valuation \<Rightarrow> valuation" where
    "update_var x v s \<equiv> s(x\<mapsto>v)"

  fun eval_exp :: "exp \<Rightarrow> focused_state \<rightharpoonup> val" where
    "eval_exp (e_var x) (ls,gs) = do {
      let lv = local_state.variables ls; let gv = global_state.variables gs;
      case lv x of
        Some v \<Rightarrow> Some v
      | None \<Rightarrow> (case gv x of
          Some v \<Rightarrow> Some v
        | None \<Rightarrow> None)
    }"
  | "eval_exp (e_localvar x) (ls,gs) = local_state.variables ls x"
  | "eval_exp (e_globalvar x) (ls,gs) = global_state.variables gs x"
  | "eval_exp (e_const n) fs = do {
      assert_option (n\<ge>min_signed \<and> n\<le>max_signed);
      Some (signed_of_int n)
    }"
  | "eval_exp (e_bin bop e1 e2) fs = do {
      v1\<leftarrow>eval_exp e1 fs;
      v2\<leftarrow>eval_exp e2 fs;
      Some (eval_bin_op bop v1 v2)
      }"
  | "eval_exp (e_un uop e) fs = do {
      v\<leftarrow>eval_exp e fs;
      Some (eval_un_op uop v)
      }"

  subsection \<open>Local Actions\<close>

  text \<open>Enabledness and effects of actions\<close>
  primrec la_en :: "focused_state \<Rightarrow> action \<rightharpoonup> bool" where
    "la_en fs (AAssign c _ _) = do { v \<leftarrow> eval_exp c fs; Some (bool_of_val v)}"
  | "la_en fs (AAssign_local c _ _) = do { v \<leftarrow> eval_exp c fs; Some (bool_of_val v)}"
  | "la_en fs (AAssign_global c _ _) = do { v \<leftarrow> eval_exp c fs; Some (bool_of_val v)}"
  | "la_en fs (ATest e) = do {
      v \<leftarrow> eval_exp e fs;
      Some (bool_of_val v)}"
  | "la_en _ (ASkip) = Some True"

  text \<open>Extension (for run, handshake): Let action have scheduler effect\<close>
  fun la_ex :: "focused_state \<Rightarrow> action \<rightharpoonup> focused_state" where
    "la_ex (ls,gs) (AAssign c x e) = do {
      u \<leftarrow> eval_exp c (ls,gs);
      assert_option (bool_of_val u);
      v \<leftarrow> eval_exp e (ls,gs);
      if exists_var (local_state.variables ls) x then do {
        let ls = local_state.variables_update (update_var x v) ls;
        Some (ls,gs)
      } else do {
        assert_option (exists_var (global_state.variables gs) x);
        let gs = global_state.variables_update (update_var x v) gs;
        Some (ls,gs)
      }
    }"
  | "la_ex (ls,gs) (AAssign_local c x e) = do {
      u \<leftarrow> eval_exp c (ls,gs);
      assert_option (bool_of_val u);
      v \<leftarrow> eval_exp e (ls,gs);
      assert_option (exists_var (local_state.variables ls) x);
      let ls = local_state.variables_update (update_var x v) ls;
      Some (ls,gs)
    }"
  | "la_ex (ls,gs) (AAssign_global c x e) = do {
      u \<leftarrow> eval_exp c (ls,gs);
      assert_option (bool_of_val u);
      v \<leftarrow> eval_exp e (ls,gs);
      assert_option (exists_var (global_state.variables gs) x);
      let gs = global_state.variables_update (update_var x v) gs;
      Some (ls,gs)
    }"
  | "la_ex fs (ATest e) = do {
      v \<leftarrow> eval_exp e fs;
      assert_option (bool_of_val v); 
      Some fs
    }"
  | "la_ex fs ASkip = Some fs"


  subsection "Scheduling"
  type_synonym local_config = "(cmd,local_state) local_config"
  type_synonym global_config = "(cmd,local_state,global_state) global_config"
  
  interpretation li: Gen_Scheduler cfg la_en la_ex .

  subsection \<open>Initial State\<close>
  definition init_valuation :: "var_decl list \<Rightarrow> valuation" where
    "init_valuation vd x \<equiv> if x \<in> set vd then Some 0 else None"

  lemma init_valuation_eq_Some[simp]: "init_valuation vd x = Some v \<longleftrightarrow> x\<in>set vd \<and> v=0"  
    unfolding init_valuation_def by auto

  lemma init_valuation_eq_None[simp]: "init_valuation vd x = None \<longleftrightarrow> x\<notin>set vd"  
    unfolding init_valuation_def by auto

  definition init_pc :: "proc_decl \<Rightarrow> local_config" where
    "init_pc pd \<equiv> \<lparr>
      local_config.command = proc_decl.body pd,
      local_config.state = \<lparr>
        local_state.variables = init_valuation (proc_decl.local_vars pd)
      \<rparr>
    \<rparr>"

  definition init_gc :: "program \<Rightarrow> global_config" where
    "init_gc prog \<equiv> \<lparr>
      global_config.processes = mset (map init_pc (program.processes prog)),
      global_config.state = \<lparr>
        global_state.variables = init_valuation (program.global_vars prog)
      \<rparr>
    \<rparr>"

  subsection "Semantics Reference Point"
  
  interpretation li: Gen_Scheduler_linit cfg la_en la_ex "{init_gc prog}" global_config.state
    for prog .
  
  abbreviation "ref_is_run \<equiv> li.sa.is_run"
  abbreviation "ref_accept \<equiv> li.sa.accept"

end

