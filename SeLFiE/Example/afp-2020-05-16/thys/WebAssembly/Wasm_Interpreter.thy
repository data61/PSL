section \<open>WebAssembly Interpreter\<close>

theory Wasm_Interpreter imports Wasm begin

datatype res_crash =
  CError
| CExhaustion

datatype res =
  RCrash res_crash
| RTrap
| RValue "v list"  

datatype res_step =
  RSCrash res_crash
| RSBreak nat "v list"
| RSReturn "v list"
| RSNormal "e list"

abbreviation crash_error where "crash_error \<equiv> RSCrash CError"

type_synonym depth = nat
type_synonym fuel = nat

type_synonym config_tuple = "s \<times> v list \<times> e list"

type_synonym config_one_tuple = " s \<times> v list \<times> v list \<times> e"

type_synonym res_tuple = "s \<times> v list \<times> res_step"

fun split_vals :: "b_e list \<Rightarrow> v list \<times> b_e list" where
  "split_vals ((C v)#es) = (let (vs', es') = split_vals es in (v#vs', es'))"
| "split_vals es = ([], es)"

fun split_vals_e :: "e list \<Rightarrow> v list \<times> e list" where
  "split_vals_e (($ C v)#es) = (let (vs', es') = split_vals_e es in (v#vs', es'))"
| "split_vals_e es = ([], es)"

fun split_n :: "v list \<Rightarrow> nat \<Rightarrow> v list \<times> v list" where
  "split_n [] n = ([], [])"
| "split_n es 0 = ([], es)"
| "split_n (e#es) (Suc n) = (let (es', es'') = split_n es n in (e#es', es''))"

lemma split_n_conv_take_drop: "split_n es n = (take n es, drop n es)"
  by (induction es n rule: split_n.induct, simp_all)

lemma split_n_length:
  assumes "split_n es n = (es1, es2)" "length es \<ge> n"
  shows "length es1 = n"
  using assms
  unfolding split_n_conv_take_drop
  by fastforce

lemma split_n_conv_app:
  assumes "split_n es n = (es1, es2)"
  shows "es = es1@es2"
  using assms
  unfolding split_n_conv_take_drop
  by auto

lemma app_conv_split_n:
  assumes "es = es1@es2"
  shows "split_n es (length es1) = (es1, es2)"
  using assms
  unfolding split_n_conv_take_drop
  by auto

lemma split_vals_const_list: "split_vals (map EConst vs) = (vs, [])"
  by (induction vs, simp_all)

lemma split_vals_e_const_list: "split_vals_e ($$* vs) = (vs, [])"
  by (induction vs, simp_all)

lemma split_vals_e_conv_app:
  assumes "split_vals_e xs = (as, bs)"
  shows "xs = ($$* as)@bs"
  using assms
proof (induction xs arbitrary: as rule: split_vals_e.induct)
  case (1 v es)
  obtain as' bs' where "split_vals_e es = (as', bs')"
    by (meson surj_pair)
  thus ?case
    using 1
    by fastforce
qed simp_all

abbreviation expect :: "'a option \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b" where
  "expect a f b \<equiv> (case a of
                     Some a' \<Rightarrow> f a'
                   | None \<Rightarrow> b)"

abbreviation vs_to_es :: " v list \<Rightarrow> e list"
  where "vs_to_es v \<equiv> $$* (rev v)"

definition e_is_trap :: "e \<Rightarrow> bool" where
  "e_is_trap e = (case e of Trap \<Rightarrow> True | _ \<Rightarrow> False)"

definition es_is_trap :: "e list \<Rightarrow> bool" where
  "es_is_trap es = (case es of [e] \<Rightarrow> e_is_trap e | _ \<Rightarrow> False)"

lemma[simp]: "e_is_trap e = (e = Trap)"
  using e_is_trap_def
  by (cases "e") auto

lemma[simp]: "es_is_trap es = (es = [Trap])"
proof (cases es)
  case Nil
  thus ?thesis
    using es_is_trap_def
    by auto
next
  case outer_Cons:(Cons a list)
  thus ?thesis
  proof (cases list)
    case Nil
    thus ?thesis
      using outer_Cons es_is_trap_def
      by auto
  next
    case (Cons a' list')
    thus ?thesis
      using es_is_trap_def outer_Cons
      by auto
  qed
qed

axiomatization 
  mem_grow_impl:: "mem \<Rightarrow> nat \<Rightarrow> mem option" where
  mem_grow_impl_correct:"(mem_grow_impl m n = Some m') \<Longrightarrow> (mem_grow m n = m')"

(*
definition mem_grow_impl:: "mem \<Rightarrow> nat \<Rightarrow> mem option" where
  "mem_grow_impl m n = Some (mem_grow m n)"

lemma mem_grow_impl_correct:
  "(mem_grow_impl m n = Some m') \<Longrightarrow> (mem_grow m n = m')"
  unfolding mem_grow_impl_def
*)
axiomatization 
  host_apply_impl:: "s \<Rightarrow> tf \<Rightarrow> host \<Rightarrow> v list \<Rightarrow> (s \<times> v list) option" where
  host_apply_impl_correct:"(host_apply_impl s tf h vs = Some m') \<Longrightarrow> (\<exists>hs. host_apply s tf h vs hs = Some m')"

function (sequential)                                                                               
    run_step :: "depth \<Rightarrow> nat \<Rightarrow> config_tuple \<Rightarrow> res_tuple"
and run_one_step :: "depth \<Rightarrow> nat \<Rightarrow> config_one_tuple \<Rightarrow> res_tuple" where
  "run_step d i (s,vs,es) = (let (ves, es') = split_vals_e es in
                             case es' of
                               [] \<Rightarrow> (s,vs, crash_error)
                             | e#es'' \<Rightarrow>
                               if e_is_trap e
                                 then
                                   if (es'' \<noteq> [] \<or> ves \<noteq> [])
                                     then
                                       (s, vs, RSNormal [Trap])
                                     else
                                       (s, vs, crash_error)
                                 else
                                   (let (s',vs',r) = run_one_step d i (s,vs,(rev ves),e) in
                                    case r of
                                      RSNormal res \<Rightarrow> (s', vs', RSNormal (res@es''))
                                  | _ \<Rightarrow> (s', vs', r)))"
| "run_one_step d i (s, vs, ves, e) =
     (case e of
    \<comment> \<open>\<open>B_E\<close>\<close>
      \<comment> \<open>\<open>UNOPS\<close>\<close>
        $(Unop_i T_i32 iop) \<Rightarrow>
         (case ves of
            (ConstInt32 c)#ves' \<Rightarrow>
              (s, vs, RSNormal (vs_to_es ((ConstInt32 (app_unop_i iop c))#ves')))
          | _ \<Rightarrow> (s, vs, crash_error))
      | $(Unop_i T_i64 iop) \<Rightarrow>
          (case ves of
             (ConstInt64 c)#ves' \<Rightarrow>
               (s, vs, RSNormal (vs_to_es ((ConstInt64 (app_unop_i iop c))#ves')))
           | _ \<Rightarrow> (s, vs, crash_error))
      | $(Unop_i _ iop) \<Rightarrow> (s, vs, crash_error)
      | $(Unop_f T_f32 fop) \<Rightarrow>
          (case ves of
             (ConstFloat32 c)#ves' \<Rightarrow>
               (s, vs, RSNormal (vs_to_es ((ConstFloat32 (app_unop_f fop c))#ves')))
           | _ \<Rightarrow> (s, vs, crash_error))
      | $(Unop_f T_f64 fop) \<Rightarrow>
          (case ves of
             (ConstFloat64 c)#ves' \<Rightarrow>
               (s, vs, RSNormal (vs_to_es ((ConstFloat64 (app_unop_f fop c))#ves')))
           | _ \<Rightarrow> (s, vs, crash_error))
      | $(Unop_f _ fop) \<Rightarrow> (s, vs, crash_error)
      \<comment> \<open>\<open>BINOPS\<close>\<close>
      | $(Binop_i T_i32 iop) \<Rightarrow>
          (case ves of
             (ConstInt32 c2)#(ConstInt32 c1)#ves' \<Rightarrow>
                expect (app_binop_i iop c1 c2) (\<lambda>c. (s, vs, RSNormal (vs_to_es ((ConstInt32 c)#ves')))) (s, vs, RSNormal ((vs_to_es ves')@[Trap]))
           | _ \<Rightarrow> (s, vs, crash_error))
      | $(Binop_i T_i64 iop) \<Rightarrow>
          (case ves of
             (ConstInt64 c2)#(ConstInt64 c1)#ves' \<Rightarrow>
                expect (app_binop_i iop c1 c2) (\<lambda>c. (s, vs, RSNormal (vs_to_es ((ConstInt64 c)#ves')))) (s, vs, RSNormal ((vs_to_es ves')@[Trap]))
           | _ \<Rightarrow> (s, vs, crash_error))
      | $(Binop_i _ iop) \<Rightarrow> (s, vs, crash_error)
      | $(Binop_f T_f32 fop) \<Rightarrow>
          (case ves of
             (ConstFloat32 c2)#(ConstFloat32 c1)#ves' \<Rightarrow>
                expect (app_binop_f fop c1 c2) (\<lambda>c. (s, vs, RSNormal (vs_to_es ((ConstFloat32 c)#ves')))) (s, vs, RSNormal ((vs_to_es ves')@[Trap]))
           | _ \<Rightarrow> (s, vs, crash_error))
      | $(Binop_f T_f64 fop) \<Rightarrow>
        (case ves of
           (ConstFloat64 c2)#(ConstFloat64 c1)#ves' \<Rightarrow>
              expect (app_binop_f fop c1 c2) (\<lambda>c. (s, vs, RSNormal (vs_to_es ((ConstFloat64 c)#ves')))) (s, vs, RSNormal ((vs_to_es ves')@[Trap]))
         | _ \<Rightarrow> (s, vs, crash_error))
      | $(Binop_f _ fop) \<Rightarrow> (s, vs, crash_error)
      \<comment> \<open>\<open>TESTOPS\<close>\<close>
      | $(Testop T_i32 testop) \<Rightarrow>
          (case ves of
             (ConstInt32 c)#ves' \<Rightarrow>
               (s, vs, RSNormal (vs_to_es ((ConstInt32 (wasm_bool (app_testop_i testop c)))#ves')))
           | _ \<Rightarrow> (s, vs, crash_error))
      | $(Testop T_i64 testop) \<Rightarrow>
          (case ves of
             (ConstInt64 c)#ves' \<Rightarrow>
               (s, vs, RSNormal (vs_to_es ((ConstInt32 (wasm_bool (app_testop_i testop c)))#ves')))
           | _ \<Rightarrow> (s, vs, crash_error))
      | $(Testop _ testop) \<Rightarrow> (s, vs, crash_error)
      \<comment> \<open>\<open>RELOPS\<close>\<close>
      | $(Relop_i T_i32 iop) \<Rightarrow>
          (case ves of
             (ConstInt32 c2)#(ConstInt32 c1)#ves' \<Rightarrow>
               (s, vs, RSNormal (vs_to_es ((ConstInt32 (wasm_bool (app_relop_i iop c1 c2)))#ves')))
           | _ \<Rightarrow> (s, vs, crash_error))
      | $(Relop_i T_i64 iop) \<Rightarrow>
          (case ves of
             (ConstInt64 c2)#(ConstInt64 c1)#ves' \<Rightarrow>
               (s, vs, RSNormal (vs_to_es ((ConstInt32 (wasm_bool (app_relop_i iop c1 c2)))#ves')))
           | _ \<Rightarrow> (s, vs, crash_error))
      | $(Relop_i _ iop) \<Rightarrow> (s, vs, crash_error)
      | $(Relop_f T_f32 fop) \<Rightarrow>
          (case ves of
             (ConstFloat32 c2)#(ConstFloat32 c1)#ves' \<Rightarrow>
               (s, vs, RSNormal (vs_to_es ((ConstInt32 (wasm_bool (app_relop_f fop c1 c2)))#ves')))
           | _ \<Rightarrow> (s, vs, crash_error))
      | $(Relop_f T_f64 fop) \<Rightarrow>
          (case ves of
             (ConstFloat64 c2)#(ConstFloat64 c1)#ves' \<Rightarrow>
               (s, vs, RSNormal (vs_to_es ((ConstInt32 (wasm_bool (app_relop_f fop c1 c2)))#ves')))
           | _ \<Rightarrow> (s, vs, crash_error))
      | $(Relop_f _ fop) \<Rightarrow> (s, vs, crash_error)
      \<comment> \<open>\<open>CONVERT\<close>\<close>
      | $(Cvtop t2 Convert t1 sx) \<Rightarrow>
          (case ves of
             v#ves' \<Rightarrow>
               (if (types_agree t1 v)
                  then
                    expect (cvt t2 sx v) (\<lambda>v'. (s, vs, RSNormal (vs_to_es (v'#ves')))) (s, vs, RSNormal ((vs_to_es ves')@[Trap]))
                  else
                    (s, vs, crash_error))
           | _ \<Rightarrow> (s, vs, crash_error))
      | $(Cvtop t2 Reinterpret t1 sx) \<Rightarrow>
          (case ves of
             v#ves' \<Rightarrow>
               (if (types_agree t1 v \<and> sx = None)
                  then
                    (s, vs, RSNormal (vs_to_es ((wasm_deserialise (bits v) t2)#ves')))
                  else
                    (s, vs, crash_error))
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>UNREACHABLE\<close>\<close>
      | $Unreachable \<Rightarrow>
          (s, vs, RSNormal ((vs_to_es ves)@[Trap]))
      \<comment> \<open>\<open>NOP\<close>\<close>
      | $Nop \<Rightarrow>
          (s, vs, RSNormal (vs_to_es ves))
      \<comment> \<open>\<open>DROP\<close>\<close>
      | $Drop \<Rightarrow>
          (case ves of
             v#ves' \<Rightarrow>
               (s, vs, RSNormal (vs_to_es ves'))
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>SELECT\<close>\<close>
      | $Select \<Rightarrow>
          (case ves of
             (ConstInt32 c)#v2#v1#ves' \<Rightarrow>
               (if int_eq c 0 then (s, vs, RSNormal (vs_to_es (v2#ves'))) else (s, vs, RSNormal (vs_to_es (v1#ves'))))
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>BLOCK\<close>\<close>
      | $(Block (t1s _> t2s) es) \<Rightarrow>
          (if length ves \<ge> length t1s
             then
               let (ves', ves'') = split_n ves (length t1s) in
               (s, vs, RSNormal ((vs_to_es ves'') @ [Label (length t2s) [] ((vs_to_es ves')@($* es))]))
             else
               (s, vs, crash_error))
      \<comment> \<open>\<open>LOOP\<close>\<close>
      | $(Loop (t1s _> t2s) es) \<Rightarrow>
          (if length ves \<ge> length t1s
             then
               let (ves', ves'') = split_n ves (length t1s) in
               (s, vs, RSNormal ((vs_to_es ves'') @ [Label (length t1s) [$(Loop (t1s _> t2s) es)] ((vs_to_es ves')@($* es))]))
             else
               (s, vs, crash_error))
      \<comment> \<open>\<open>IF\<close>\<close>
      | $(If tf es1 es2) \<Rightarrow>
          (case ves of
             (ConstInt32 c)#ves' \<Rightarrow>
                if int_eq c 0
                  then
                    (s, vs, RSNormal ((vs_to_es ves')@[$(Block tf es2)]))
                  else
                    (s, vs, RSNormal ((vs_to_es ves')@[$(Block tf es1)]))
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>BR\<close>\<close>
      | $Br j \<Rightarrow>
          (s, vs, RSBreak j ves)
      \<comment> \<open>\<open>BR_IF\<close>\<close>
      | $Br_if j \<Rightarrow>
          (case ves of
             (ConstInt32 c)#ves' \<Rightarrow>
                if int_eq c 0
                  then
                    (s, vs, RSNormal (vs_to_es ves'))
                  else
                    (s, vs, RSNormal ((vs_to_es ves') @ [$Br j]))
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>BR_TABLE\<close>\<close>
      | $Br_table js j \<Rightarrow>
          (case ves of
             (ConstInt32 c)#ves' \<Rightarrow>
             let k = nat_of_int c in
                if k < length js
                  then
                    (s, vs, RSNormal ((vs_to_es ves') @ [$Br (js!k)]))
                  else
                    (s, vs, RSNormal ((vs_to_es ves') @ [$Br j]))
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>CALL\<close>\<close>
      | $Call j \<Rightarrow>
          (s, vs, RSNormal ((vs_to_es ves) @ [Callcl (sfunc s i j)]))
      \<comment> \<open>\<open>CALL_INDIRECT\<close>\<close>
      | $Call_indirect j \<Rightarrow>
          (case ves of
             (ConstInt32 c)#ves' \<Rightarrow>
               (case (stab s i (nat_of_int c)) of
                  Some cl \<Rightarrow>
                    if (stypes s i j = cl_type cl)
                      then
                        (s, vs, RSNormal ((vs_to_es ves') @ [Callcl cl]))
                      else
                        (s, vs, RSNormal ((vs_to_es ves')@[Trap]))
                | _ \<Rightarrow> (s, vs, RSNormal ((vs_to_es ves')@[Trap])))
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>RETURN\<close>\<close>
      | $Return \<Rightarrow>
          (s, vs, RSReturn ves)
      \<comment> \<open>\<open>GET_LOCAL\<close>\<close>
      | $Get_local j \<Rightarrow>
          (if j < length vs
             then (s, vs, RSNormal (vs_to_es ((vs!j)#ves)))
             else (s, vs, crash_error))
      \<comment> \<open>\<open>SET_LOCAL\<close>\<close>
      | $Set_local j \<Rightarrow>
          (case ves of
             v#ves' \<Rightarrow>
               if j < length vs
                 then (s, vs[j := v], RSNormal (vs_to_es ves'))
                 else (s, vs, crash_error)
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>TEE_LOCAL\<close>\<close>
      | $Tee_local j \<Rightarrow>
          (case ves of
             v#ves' \<Rightarrow>
               (s, vs, RSNormal ((vs_to_es (v#ves)) @ [$(Set_local j)]))
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>GET_GLOBAL\<close>\<close>
      | $Get_global j \<Rightarrow>
          (s, vs, RSNormal (vs_to_es ((sglob_val s i j)#ves)))
      \<comment> \<open>\<open>SET_GLOBAL\<close>\<close>
      | $Set_global j \<Rightarrow>
          (case ves of
             v#ves' \<Rightarrow> ((supdate_glob s i j v), vs, RSNormal (vs_to_es ves'))
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>LOAD\<close>\<close>
      | $(Load t None a off) \<Rightarrow>
          (case ves of
             (ConstInt32 k)#ves' \<Rightarrow>
               expect (smem_ind s i)
                  (\<lambda>j.
                    expect (load ((mem s)!j) (nat_of_int k) off (t_length t))
                      (\<lambda>bs. (s, vs, RSNormal (vs_to_es ((wasm_deserialise bs t)#ves'))))
                      (s, vs, RSNormal ((vs_to_es ves')@[Trap])))
                  (s, vs, crash_error)
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>LOAD PACKED\<close>\<close>
      | $(Load t (Some (tp, sx)) a off) \<Rightarrow>
          (case ves of
             (ConstInt32 k)#ves' \<Rightarrow>
               expect (smem_ind s i)
                  (\<lambda>j.
                    expect (load_packed sx ((mem s)!j) (nat_of_int k) off (tp_length tp) (t_length t))
                      (\<lambda>bs. (s, vs, RSNormal (vs_to_es ((wasm_deserialise bs t)#ves'))))
                      (s, vs, RSNormal ((vs_to_es ves')@[Trap])))
                  (s, vs, crash_error)
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>STORE\<close>\<close>
      | $(Store t None a off) \<Rightarrow>
          (case ves of
             v#(ConstInt32 k)#ves' \<Rightarrow>
               (if (types_agree t v)
                 then
                   expect (smem_ind s i)
                      (\<lambda>j.
                         expect (store ((mem s)!j) (nat_of_int k) off (bits v) (t_length t))
                           (\<lambda>mem'. (s\<lparr>mem:= ((mem s)[j := mem'])\<rparr>, vs, RSNormal (vs_to_es ves')))
                           (s, vs, RSNormal ((vs_to_es ves')@[Trap])))
                      (s, vs, crash_error)
                 else
                   (s, vs, crash_error))
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>STORE_PACKED\<close>\<close>
      | $(Store t (Some tp) a off) \<Rightarrow>
          (case ves of
                  v#(ConstInt32 k)#ves' \<Rightarrow>
                    (if (types_agree t v)
                      then
                        expect (smem_ind s i)
                           (\<lambda>j.
                              expect (store_packed ((mem s)!j) (nat_of_int k) off (bits v) (tp_length tp))
                                (\<lambda>mem'. (s\<lparr>mem:= ((mem s)[j := mem'])\<rparr>, vs, RSNormal (vs_to_es ves')))
                                (s, vs, RSNormal ((vs_to_es ves')@[Trap])))
                           (s, vs, crash_error)
                      else
                        (s, vs, crash_error))
                | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>CURRENT_MEMORY\<close>\<close>
      | $Current_memory \<Rightarrow>
          expect (smem_ind s i)
            (\<lambda>j. (s, vs, RSNormal (vs_to_es ((ConstInt32 (int_of_nat (mem_size ((s.mem s)!j))))#ves))))
            (s, vs, crash_error)
      \<comment> \<open>\<open>GROW_MEMORY\<close>\<close>
      | $Grow_memory \<Rightarrow>
          (case ves of
             (ConstInt32 c)#ves' \<Rightarrow>
                expect (smem_ind s i)
                  (\<lambda>j.
                     let l = (mem_size ((s.mem s)!j)) in
                     (expect (mem_grow_impl ((mem s)!j) (nat_of_int c))
                        (\<lambda>mem'. (s\<lparr>mem:= ((mem s)[j := mem'])\<rparr>, vs, RSNormal (vs_to_es ((ConstInt32 (int_of_nat l))#ves'))))
                        (s, vs, RSNormal (vs_to_es ((ConstInt32 int32_minus_one)#ves')))))
                  (s, vs, crash_error)
           | _ \<Rightarrow> (s, vs, crash_error))
      \<comment> \<open>\<open>VAL\<close> - should not be executed\<close>
      | $C v \<Rightarrow> (s, vs, crash_error)
    \<comment> \<open>\<open>E\<close>\<close>
      \<comment> \<open>\<open>CALLCL\<close>\<close>
      | Callcl cl \<Rightarrow>
          (case cl of
             Func_native i' (t1s _> t2s) ts es \<Rightarrow>
               let n = length t1s in
               let m = length t2s in
               if length ves \<ge> n
                 then
                   let (ves', ves'') = split_n ves n in
                   let zs = n_zeros ts in
                     (s, vs, RSNormal ((vs_to_es ves'') @ ([Local m i' ((rev ves')@zs) [$(Block ([] _> t2s) es)]])))
                 else
                   (s, vs, crash_error)
           | Func_host (t1s _> t2s) f \<Rightarrow>
               let n = length t1s in
               let m = length t2s in
               if length ves \<ge> n
                 then
                   let (ves', ves'') = split_n ves n in
                   case host_apply_impl s (t1s _> t2s) f (rev ves') of
                     Some (s',rves) \<Rightarrow> 
                       if list_all2 types_agree t2s rves
                         then
                           (s', vs, RSNormal ((vs_to_es ves'') @ ($$* rves)))
                         else
                           (s', vs, crash_error)
                   | None \<Rightarrow> (s, vs, RSNormal ((vs_to_es ves'')@[Trap]))
                 else
                   (s, vs, crash_error))
      \<comment> \<open>\<open>LABEL\<close>\<close>
      | Label ln les es \<Rightarrow>
          if es_is_trap es
            then
              (s, vs, RSNormal ((vs_to_es ves)@[Trap]))
             else
               (if (const_list es)
                  then
                    (s, vs, RSNormal ((vs_to_es ves)@es))
                  else
                    let (s', vs', res) = run_step d i (s, vs, es) in
                    (case res of
                       RSBreak 0 bvs \<Rightarrow>
                         if (length bvs \<ge> ln)
                           then (s', vs', RSNormal ((vs_to_es ((take ln bvs)@ves))@les))
                           else (s', vs', crash_error)
                     | RSBreak (Suc n) bvs \<Rightarrow>
                         (s', vs', RSBreak n bvs)
                     | RSReturn rvs \<Rightarrow>
                         (s', vs', RSReturn rvs)
                     | RSNormal es' \<Rightarrow>
                         (s', vs', RSNormal ((vs_to_es ves)@[Label ln les es']))
                     | _ \<Rightarrow> (s', vs', crash_error)))
     \<comment> \<open>\<open>LOCAL\<close>\<close>
     | Local ln j vls es \<Rightarrow>
          if es_is_trap es
            then
              (s, vs, RSNormal ((vs_to_es ves)@[Trap]))
             else
               (if (const_list es)
                  then
                    if (length es = ln)
                      then (s, vs, RSNormal ((vs_to_es ves)@es))
                      else (s, vs, crash_error)
                  else
                    case d of
                      0 \<Rightarrow> (s, vs, crash_error)
                    | Suc d' \<Rightarrow>
                        let (s', vls', res) = run_step d' j (s, vls, es) in
                        (case res of
                           RSReturn rvs \<Rightarrow>
                             if (length rvs \<ge> ln)
                               then (s', vs, RSNormal (vs_to_es ((take ln rvs)@ves)))
                               else (s', vs, crash_error)
                         | RSNormal es' \<Rightarrow>
                             (s', vs, RSNormal ((vs_to_es ves)@[Local ln j vls' es']))
                         | _ \<Rightarrow> (s', vs, RSCrash CExhaustion)))
     \<comment> \<open>\<open>TRAP\<close> - should not be executed\<close>
     | Trap \<Rightarrow> (s, vs, crash_error))"
  by pat_completeness auto
termination
proof -
  {
    fix xs::"e list" and as b bs
    assume local_assms:"(as, b#bs) = split_vals_e xs"
    have "2*(size b) < 2*(size_list size xs) + 1"
      using local_assms[symmetric] split_vals_e_conv_app
            size_list_estimation'[of b xs "size b" size]
      unfolding size_list_def
      by fastforce
  }
  thus ?thesis
    by (relation "measure (case_sum
                               (\<lambda>p. 2 * (size_list size (snd (snd (snd (snd p))))) + 1)
                               (\<lambda>p. 2 * size (snd (snd (snd (snd (snd p)))))))") auto
qed

fun run_v :: "fuel \<Rightarrow> depth \<Rightarrow> nat \<Rightarrow> config_tuple \<Rightarrow> (s \<times> res)" where
  "run_v (Suc n) d i (s,vs,es) = (if (es_is_trap es)
                                    then (s, RTrap)
                                    else if (const_list es)
                                           then (s, RValue (fst (split_vals_e es)))
                                           else (let (s',vs',res) = (run_step d i (s,vs,es)) in
                                                 case res of
                                                   RSNormal es' \<Rightarrow> run_v n d i (s',vs',es')
                                                 | RSCrash error \<Rightarrow> (s, RCrash error)
                                                 | _ \<Rightarrow> (s, RCrash CError)))"
| "run_v 0 d i (s,vs,es) = (s, RCrash CExhaustion)"

end
