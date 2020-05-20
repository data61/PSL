theory Mulog
imports "../CAVA_Impl"
begin

  fun join :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
    where "join [] a = []" | "join (x # xs) a = x # a # join xs a"
  fun join' :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
    where "join' (x # y # xs) a = x # a # join' (y # xs) a" | "join' xs a = xs"

  fun nat_to_string :: "nat \<Rightarrow> String.literal"
    where
      "nat_to_string 0 = STR ''0''" |
      "nat_to_string (Suc 0) = STR ''1''" |
      "nat_to_string (Suc (Suc 0)) = STR ''2''" |
      "nat_to_string (Suc (Suc (Suc 0))) = STR ''3''" |
      "nat_to_string (Suc (Suc (Suc (Suc n)))) = STR ''many''"
  definition int_to_string :: "int \<Rightarrow> String.literal"
    where "int_to_string i \<equiv> if i < 0
      then STR ''-'' + nat_to_string (nat (- i))
      else nat_to_string (nat i)"
  definition literal_concat :: "String.literal list \<Rightarrow> String.literal"
    where "literal_concat xs \<equiv> foldr (+) xs 0"

  definition get_assignments :: "valuation_impl \<Rightarrow> String.literal list"
    where "get_assignments v \<equiv> map
      (\<lambda> k. k + STR '' = '' + nat_to_string (nat_of_uint32 (the (Mapping.lookup v k))))
      (Mapping.ordered_keys v)"
  definition show_state :: "pid_global_config_impl \<Rightarrow> String.literal"
    where "show_state s \<equiv> let
      gvals = global_state_impl.variables (pid_global_config.state s);
      lvals = map (local_state_impl.variables \<circ> local_config.state) (pid_global_config.processes s)
      in literal_concat (join' (concat (map get_assignments (gvals # lvals))) (STR '', ''))"
  definition show_ce :: "pid_global_config_impl lasso \<Rightarrow> String.literal"
    where "show_ce ce \<equiv>
      STR ''reach'' +
      String.implode [lf] +
      literal_concat (join' (remdups_adj (map show_state (lasso_reach ce))) (String.implode [lf])) +
      String.implode [lf] +
      STR ''va'' +
      String.implode [lf] +
      show_state (lasso_va ce) +
      String.implode [lf] +
      STR ''cysfx'' +
      String.implode [lf] +
      literal_concat (join' (remdups_adj (map show_state (lasso_cysfx ce))) (String.implode [lf]))"

  type_synonym cmd = SM_Syntax.cmd

  notation cmd.Seq (infixr ";" 50)

  definition efalse :: "exp" where "efalse \<equiv> e_const 0"
  definition etrue :: "exp" where "etrue \<equiv> e_const 1"

  definition var :: "ident \<Rightarrow> exp"
    where "var v \<equiv> e_var v"
  definition assign :: "ident \<Rightarrow> exp \<Rightarrow> cmd"
    where "assign v e \<equiv> cmd.Assign etrue v e"
  definition assignc :: "exp \<Rightarrow> ident \<Rightarrow> exp \<Rightarrow> cmd"
    where "assignc c v e \<equiv> cmd.Assign c v e"
  definition wait :: "exp \<Rightarrow> cmd"
    where "wait c \<equiv> cmd.Test c"
  definition not :: "exp \<Rightarrow> exp"
    where "not e \<equiv> e_bin bo_eq e (e_const 0)"
  definition ifelse :: "exp \<Rightarrow> cmd \<Rightarrow> cmd \<Rightarrow> cmd"
    where "ifelse c c1 c2 \<equiv> cmd.Or (cmd.Test c; c1) (cmd.Test (not c); c2)"

  definition var_decl_to_promela :: "var_decl \<Rightarrow> String.literal"
    where "var_decl_to_promela var_decl \<equiv> STR ''int'' + STR '' '' + var_decl"
  fun bin_op_to_promela :: "bin_op \<Rightarrow> String.literal"
    where
      "bin_op_to_promela bo_plus = STR ''+''" |
      "bin_op_to_promela bo_minus = STR ''-''" |
      "bin_op_to_promela bo_mul = STR ''*''" |
      "bin_op_to_promela bo_div = STR ''/''" |
      "bin_op_to_promela bo_mod = STR ''%''" |
      "bin_op_to_promela bo_less = STR ''<''" |
      "bin_op_to_promela bo_less_eq = STR ''<=''" |
      "bin_op_to_promela bo_eq = STR ''==''" |
      "bin_op_to_promela bo_and = STR ''&''" |
      "bin_op_to_promela bo_or = STR ''|''" |
      "bin_op_to_promela bo_xor = STR ''^''"
  fun un_op_to_promela :: "un_op \<Rightarrow> String.literal"
    where
      "un_op_to_promela uo_minus = STR ''-''" |
      "un_op_to_promela uo_not = STR ''~''"
  fun exp_to_promela :: "exp \<Rightarrow> String.literal"
    where
      "exp_to_promela (e_var v) = v" |
      "exp_to_promela (e_localvar v) = v" |
      "exp_to_promela (e_globalvar v) = v" |
      "exp_to_promela (e_const i) = int_to_string i" |
      "exp_to_promela (e_bin bo e1 e2) = STR ''('' + exp_to_promela e1 + STR '' '' + bin_op_to_promela bo + STR '' '' + exp_to_promela e2 + STR '')''" |
      "exp_to_promela (e_un uo e) = STR ''('' + un_op_to_promela uo + STR '' '' + exp_to_promela e + STR '')''"
  fun cmd_to_promela :: "cmd \<Rightarrow> String.literal"
    where
      "cmd_to_promela (Assign c v e) = STR ''atomic { '' + exp_to_promela c + STR '' -> '' + v + STR '' = '' + exp_to_promela e + STR '' }''" |
      "cmd_to_promela (Assign_local c v e) = STR ''atomic { '' + exp_to_promela c + STR '' -> '' + v + STR '' = '' + exp_to_promela e + STR '' }''" |
      "cmd_to_promela (Assign_global c v e) = STR ''atomic { '' + exp_to_promela c + STR '' -> '' + v + STR '' = '' + exp_to_promela e + STR '' }''" |
      "cmd_to_promela (Test c) = exp_to_promela c" |
      "cmd_to_promela (Skip) = STR ''skip''" |
      "cmd_to_promela (Seq c1 c2) = cmd_to_promela c1 + STR ''; '' + cmd_to_promela c2" |
      "cmd_to_promela (Or c1 c2) = STR ''if'' + STR '' :: '' + cmd_to_promela c1 + STR '' :: '' + cmd_to_promela c2 + STR '' fi''" |
      "cmd_to_promela (Iterate c1 c2) = (
        if c1=c2 then
          STR ''do'' + STR '' :: '' + cmd_to_promela c1 + STR '' od''
        else
          Code.abort (STR ''General iterate not supported by promela translator'') (\<lambda>_. undefined)
        )"
  definition proc_decl_to_promela :: "proc_decl \<Rightarrow> String.literal"
    where "proc_decl_to_promela proc_decl \<equiv>
      STR ''proctype'' + STR '' '' + name proc_decl + STR ''()'' + STR '' '' + STR ''{ '' +
      literal_concat (join (map var_decl_to_promela (local_vars proc_decl)) (STR ''; '')) +
      cmd_to_promela (body proc_decl) + STR '' }''"
  definition run_process_to_promela :: "proc_decl \<Rightarrow> String.literal"
    where "run_process_to_promela proc_decl \<equiv> STR ''run'' + STR '' '' + name proc_decl + STR ''()''"
  definition program_to_promela :: "program \<Rightarrow> String.literal"
    where "program_to_promela program \<equiv>
      literal_concat (join (map var_decl_to_promela (global_vars program)) (STR ''; '')) +
      literal_concat (map proc_decl_to_promela (processes program)) +
      STR ''init { '' + literal_concat (join' (map run_process_to_promela (processes program)) (STR ''; '')) + STR '' }''"

  definition "lock_lock n \<equiv> n + STR ''l''"
  definition "lock_vars n \<equiv> [lock_lock n]"
  definition lock_initialize :: "ident \<Rightarrow> cmd"
    where "lock_initialize n \<equiv> assign (lock_lock n) efalse"
  definition lock_block :: "ident \<Rightarrow> cmd \<Rightarrow> cmd"
    where "lock_block n c \<equiv>
      assignc (not (var (lock_lock n))) (lock_lock n) etrue;
      c;
      assign (lock_lock n) efalse"

  definition "handshake_sender n \<equiv> n + STR ''s''"
  definition "handshake_receiver n \<equiv> n + STR ''r''"
  definition "handshake_message n \<equiv> n + STR ''m''"
  definition "handshake_sent n \<equiv> n + STR ''n''"
  definition "handshake_received n \<equiv> n + STR ''c''"
  definition "handshake_vars n \<equiv>
    concat (map lock_vars [handshake_sender n, handshake_receiver n]) @
    [handshake_message n, handshake_sent n, handshake_received n]"
  definition handshake_initialize :: "ident \<Rightarrow> cmd"
    where "handshake_initialize n \<equiv>
      lock_initialize (handshake_sender n);
      lock_initialize (handshake_receiver n);
      assign (handshake_message n) (e_const 0);
      assign (handshake_sent n) efalse;
      assign (handshake_received n) efalse"
  definition handshake_waiting :: "ident \<Rightarrow> exp"
    where "handshake_waiting n \<equiv> var (handshake_sent n)"
  definition handshake_send :: "ident \<Rightarrow> exp \<Rightarrow> cmd"
    where "handshake_send n m \<equiv>
      lock_block (handshake_sender n)
      (
        assign (handshake_message n) m;
        assign (handshake_sent n) etrue;
        wait (var (handshake_received n));
        assign (handshake_received n) efalse
      )"
  definition handshake_receive :: "ident \<Rightarrow> ident \<Rightarrow> cmd"
    where "handshake_receive n m \<equiv>
      lock_block (handshake_receiver n)
      (
        wait (var (handshake_sent n));
        assign (handshake_sent n) efalse;
        assign m (var (handshake_message n));
        assign (handshake_received n) etrue
      )"

  definition "mulog_processes \<equiv> [STR ''A'', STR ''B'']"
  definition "mulog_process_ids \<equiv> [1 ..< Suc (length mulog_processes)]"
  fun mulog_process_name :: "nat \<Rightarrow> ident"
    where
      "mulog_process_name 0 = STR ''unknown''" |
      "mulog_process_name (Suc i) = mulog_processes ! i"

  definition "mulog_handshake i \<equiv> mulog_process_name i + STR ''h''"
  definition "mulog_msg i \<equiv> mulog_process_name i + STR ''m''"
  definition "mulog_idle i \<equiv> mulog_process_name i + STR ''i''"
  definition "mulog_token i \<equiv> mulog_process_name i + STR ''t''"
  definition "mulog_requesting i \<equiv> mulog_process_name i + STR ''r''"
  definition "mulog_parent i \<equiv> mulog_process_name i + STR ''p''"
  definition "mulog_next i \<equiv> mulog_process_name i + STR ''n''"

  fun mulog_send_aux :: "nat \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> cmd"
    where
      "mulog_send_aux 0 proc msg = cmd.Skip" |
      "mulog_send_aux (Suc n) proc msg =
        ifelse (e_bin bo_eq proc (e_const (int (Suc n))))
        (handshake_send (mulog_handshake (Suc n)) msg)
        (mulog_send_aux n proc msg)"
  definition mulog_send :: "exp \<Rightarrow> exp \<Rightarrow> cmd"
    where "mulog_send \<equiv> mulog_send_aux (length mulog_processes)"

  definition "mulog_vars_global i \<equiv> handshake_vars (mulog_handshake i)"
  definition "mulog_vars_local i \<equiv> [mulog_msg i, mulog_idle i, mulog_token i, mulog_requesting i,
    mulog_parent i, mulog_next i]"
  definition mulog_initialize :: "nat \<Rightarrow> cmd"
    where "mulog_initialize i \<equiv>
      handshake_initialize (mulog_handshake i);
      assign (mulog_msg i) (e_const 0);
      assign (mulog_idle i) etrue;
      assign (mulog_parent i) (if i = 1 then e_const 0 else e_const 1);
      assign (mulog_next i) (e_const 0);
      assign (mulog_requesting i) efalse;
      assign (mulog_token i) (if i = 1 then etrue else efalse)"
  definition mulog_request_token :: "nat \<Rightarrow> cmd"
    where "mulog_request_token i \<equiv>
      assign (mulog_requesting i) etrue;
      ifelse (e_bin bo_eq (var (mulog_parent i)) (e_const 0))
      cmd.Skip
      (
        mulog_send (var (mulog_parent i)) (e_const (int i));
        assign (mulog_parent i) (e_const 0)
      )"
  definition mulog_release_token :: "nat \<Rightarrow> cmd"
    where "mulog_release_token i \<equiv>
      assign (mulog_requesting i) efalse;
      ifelse (e_bin bo_eq (var (mulog_next i)) (e_const 0))
      cmd.Skip
      (
        assign (mulog_token i) efalse;
        mulog_send (var (mulog_next i)) (e_const 0);
        assign (mulog_next i) (e_const 0)
      )"

  definition mulog_process_cmd :: "nat \<Rightarrow> cmd"
    where "mulog_process_cmd i \<equiv>
      mulog_initialize i;
      SM_Syntax.Loop
      (
        ifelse (handshake_waiting (mulog_handshake i))
        (
          handshake_receive (mulog_handshake i) (mulog_msg i);
          ifelse (e_bin bo_eq (var (mulog_msg i)) (e_const 0))
          (assign (mulog_token i) etrue)
          (
            ifelse (e_bin bo_eq (var (mulog_parent i)) (e_const 0))
            (
              ifelse (var (mulog_requesting i))
              (assign (mulog_next i) (var (mulog_msg i)))
              (
                assign (mulog_token i) efalse;
                mulog_send (var (mulog_msg i)) (e_const 0)
              )
            )
            (mulog_send (var (mulog_parent i)) (var (mulog_msg i)));
            assign (mulog_parent i) (var (mulog_msg i))
          )
        )
        (
          ifelse (var (mulog_idle i))
          (
            assign (mulog_idle i) efalse;
            mulog_request_token i
          )
          (
            ifelse (var (mulog_token i))
            (
              assign (STR ''x'') (e_bin bo_plus (var (STR ''x'')) (e_const 1));
              assign (STR ''x'') (e_bin bo_minus (var (STR ''x'')) (e_const 1));
              mulog_release_token i;
              assign (mulog_idle i) etrue
            )
            cmd.Skip
          )
        )
      )"
  definition mulog_process :: "nat \<Rightarrow> proc_decl"
    where "mulog_process i \<equiv>
    \<lparr>
      name = mulog_process_name i,
      body = mulog_process_cmd i,
      local_vars = mulog_vars_local i
    \<rparr>"
  definition mulog_program :: "program"
    where "mulog_program \<equiv>
    \<lparr>
      program.processes = map mulog_process mulog_process_ids,
      program.global_vars = STR ''x'' # List.maps mulog_vars_global mulog_process_ids
    \<rparr>"

  definition test1_process_send :: "int \<Rightarrow> proc_decl"
    where "test1_process_send i \<equiv>
    \<lparr>
      name = STR ''test1_process_send'',
      body = handshake_send (STR ''foo'') (e_const i),
      local_vars = []
    \<rparr>"
  definition test1_process_receive :: "proc_decl"
    where "test1_process_receive \<equiv>
    \<lparr>
      name = STR ''test1_process_receive'',
      body = SM_Syntax.Loop
      (
        handshake_receive (STR ''foo'') (STR ''temp'');
        assign (STR ''x'') (e_bin bo_plus (var (STR ''x'')) (var (STR ''temp'')))
      ),
      local_vars = [STR ''temp'']
    \<rparr>"
  definition test1_program :: "program"
    where "test1_program \<equiv>
    \<lparr>
      program.processes = [test1_process_send 1, test1_process_send 2, test1_process_receive],
      program.global_vars = STR ''x'' # handshake_vars (STR ''foo'')
    \<rparr>"

  definition test2_process :: "proc_decl"
    where "test2_process \<equiv>
    \<lparr>
      name = STR ''test2_process'',
      body = lock_block (STR ''foo'')
      (
        assign (STR ''x'') (e_bin bo_plus (var (STR ''x'')) (e_const 1));
        assign (STR ''x'') (e_bin bo_minus (var (STR ''x'')) (e_const 1))
      ),
      local_vars = []
    \<rparr>"
  definition test2_program :: "program"
    where "test2_program \<equiv>
    \<lparr>
      program.processes = [test2_process, test2_process],
      program.global_vars = STR ''x'' # lock_vars (STR ''foo'')
    \<rparr>"

  definition "mulog_property \<equiv> G\<^sub>c prop\<^sub>c(e_bin bo_less_eq (e_var (STR ''x'')) (e_const 1))"
  definition "test1_property \<equiv> F\<^sub>c prop\<^sub>c(e_bin bo_eq (e_var (STR ''x'')) (e_const 3))"
  definition "test2_property \<equiv> G\<^sub>c prop\<^sub>c(e_bin bo_less_eq (e_var (STR ''x'')) (e_const 1))"

  definition "test n \<equiv> cava_sm dflt_cfg mulog_program mulog_property"

  value [code] "cmd_to_promela (mulog_initialize 1)"
  (* value [code] "program_to_promela mulog_program *)

  export_code
    program_to_promela mulog_program
    test show_ce
    TY_ERR SAT UNSAT UNSAT_CE
    lasso_reach lasso_va lasso_cysfx
    nat_of_integer
    in SML
    module_name Mulog
    file "../code/examples/mulog/Mulog_Export.sml"

end
