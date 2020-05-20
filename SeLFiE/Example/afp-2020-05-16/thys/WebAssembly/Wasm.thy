theory Wasm imports Wasm_Base_Defs begin

(* TYPING RELATION *)
inductive b_e_typing :: "[t_context, b_e list, tf] \<Rightarrow> bool" ("_ \<turnstile> _ : _" 60) where
  \<comment> \<open>\<open>num ops\<close>\<close>
  const:"\<C> \<turnstile> [C v]         : ([]    _> [(typeof v)])"
| unop_i:"is_int_t t   \<Longrightarrow> \<C> \<turnstile> [Unop_i t _]  : ([t]   _> [t])"
| unop_f:"is_float_t t \<Longrightarrow> \<C> \<turnstile> [Unop_f t _]  : ([t]   _> [t])"
| binop_i:"is_int_t t   \<Longrightarrow> \<C> \<turnstile> [Binop_i t iop] : ([t,t] _> [t])"
| binop_f:"is_float_t t \<Longrightarrow> \<C> \<turnstile> [Binop_f t _] : ([t,t] _> [t])"
| testop:"is_int_t t   \<Longrightarrow> \<C> \<turnstile> [Testop t _]  : ([t]   _> [T_i32])"
| relop_i:"is_int_t t   \<Longrightarrow> \<C> \<turnstile> [Relop_i t _] : ([t,t] _> [T_i32])"
| relop_f:"is_float_t t \<Longrightarrow> \<C> \<turnstile> [Relop_f t _] : ([t,t] _> [T_i32])"
  \<comment> \<open>\<open>convert\<close>\<close>
| convert:"\<lbrakk>(t1 \<noteq> t2); (sx = None) = ((is_float_t t1 \<and> is_float_t t2) \<or> (is_int_t t1 \<and> is_int_t t2 \<and> (t_length t1 < t_length t2)))\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Cvtop t1 Convert t2 sx] : ([t2] _> [t1])"
  \<comment> \<open>\<open>reinterpret\<close>\<close>
| reinterpret:"\<lbrakk>(t1 \<noteq> t2); t_length t1 = t_length t2\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Cvtop t1 Reinterpret t2 None] : ([t2] _> [t1])"
  \<comment> \<open>\<open>unreachable, nop, drop, select\<close>\<close>
| unreachable:"\<C> \<turnstile> [Unreachable] : (ts _> ts')"
| nop:"\<C> \<turnstile> [Nop] : ([] _> [])"
| drop:"\<C> \<turnstile> [Drop] : ([t] _> [])"
| select:"\<C> \<turnstile> [Select] : ([t,t,T_i32] _> [t])"
  \<comment> \<open>\<open>block\<close>\<close>
| block:"\<lbrakk>tf = (tn _> tm); \<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr> \<turnstile> es : (tn _> tm)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Block tf es] : (tn _> tm)"
  \<comment> \<open>\<open>loop\<close>\<close>
| loop:"\<lbrakk>tf = (tn _> tm); \<C>\<lparr>label := ([tn] @ (label \<C>))\<rparr> \<turnstile> es : (tn _> tm)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Loop tf es] : (tn _> tm)"
  \<comment> \<open>\<open>if then else\<close>\<close>
| if_wasm:"\<lbrakk>tf = (tn _> tm); \<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr> \<turnstile> es1 : (tn _> tm); \<C>\<lparr>label := ([tm] @ (label \<C>))\<rparr> \<turnstile> es2 : (tn _> tm)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [If tf es1 es2] : (tn @ [T_i32] _> tm)"
  \<comment> \<open>\<open>br\<close>\<close>
| br:"\<lbrakk>i < length(label \<C>); (label \<C>)!i = ts\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Br i] : (t1s @ ts _> t2s)"
  \<comment> \<open>\<open>br_if\<close>\<close>
| br_if:"\<lbrakk>i < length(label \<C>); (label \<C>)!i = ts\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Br_if i] : (ts @ [T_i32] _> ts)"
  \<comment> \<open>\<open>br_table\<close>\<close>
| br_table:"\<lbrakk>list_all (\<lambda>i. i < length(label \<C>) \<and> (label \<C>)!i = ts) (is@[i])\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Br_table is i] : (t1s @ ts @ [T_i32] _> t2s)"
  \<comment> \<open>\<open>return\<close>\<close>
| return:"\<lbrakk>(return \<C>) = Some ts\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Return] : (t1s @ ts _> t2s)"
  \<comment> \<open>\<open>call\<close>\<close>
| call:"\<lbrakk>i < length(func_t \<C>); (func_t \<C>)!i = tf\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Call i] : tf"
  \<comment> \<open>\<open>call_indirect\<close>\<close>
| call_indirect:"\<lbrakk>i < length(types_t \<C>); (types_t \<C>)!i = (t1s _> t2s); (table \<C>) \<noteq> None\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Call_indirect i] : (t1s @ [T_i32] _> t2s)"
  \<comment> \<open>\<open>get_local\<close>\<close>
| get_local:"\<lbrakk>i < length(local \<C>); (local \<C>)!i = t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Get_local i] : ([] _> [t])"
  \<comment> \<open>\<open>set_local\<close>\<close>
| set_local:"\<lbrakk>i < length(local \<C>); (local \<C>)!i = t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Set_local i] : ([t] _> [])"
  \<comment> \<open>\<open>tee_local\<close>\<close>
| tee_local:"\<lbrakk>i < length(local \<C>); (local \<C>)!i = t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Tee_local i] : ([t] _> [t])"
  \<comment> \<open>\<open>get_global\<close>\<close>
| get_global:"\<lbrakk>i < length(global \<C>); tg_t ((global \<C>)!i) = t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Get_global i] : ([] _> [t])"
  \<comment> \<open>\<open>set_global\<close>\<close>
| set_global:"\<lbrakk>i < length(global \<C>); tg_t ((global \<C>)!i) = t; is_mut ((global \<C>)!i)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Set_global i] : ([t] _> [])"
  \<comment> \<open>\<open>load\<close>\<close>
| load:"\<lbrakk>(memory \<C>) = Some n; load_store_t_bounds a (option_projl tp_sx) t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Load t tp_sx a off] : ([T_i32] _> [t])"
  \<comment> \<open>\<open>store\<close>\<close>
| store:"\<lbrakk>(memory \<C>) = Some n; load_store_t_bounds a tp t\<rbrakk> \<Longrightarrow> \<C> \<turnstile> [Store t tp a off] : ([T_i32,t] _> [])"
  \<comment> \<open>\<open>current_memory\<close>\<close>
| current_memory:"(memory \<C>) = Some n \<Longrightarrow> \<C> \<turnstile> [Current_memory] : ([] _> [T_i32])"
  \<comment> \<open>\<open>Grow_memory\<close>\<close>
| grow_memory:"(memory \<C>) = Some n \<Longrightarrow> \<C> \<turnstile> [Grow_memory] : ([T_i32] _> [T_i32])"
  \<comment> \<open>\<open>empty program\<close>\<close>
| empty:"\<C> \<turnstile> [] : ([] _> [])"
  \<comment> \<open>\<open>composition\<close>\<close>
| composition:"\<lbrakk>\<C> \<turnstile> es : (t1s _> t2s); \<C> \<turnstile> [e] : (t2s _> t3s)\<rbrakk> \<Longrightarrow> \<C> \<turnstile> es @ [e] : (t1s _> t3s)"
  \<comment> \<open>\<open>weakening\<close>\<close>
| weakening:"\<C> \<turnstile> es : (t1s _> t2s) \<Longrightarrow> \<C> \<turnstile> es : (ts @ t1s _> ts @ t2s)"

inductive cl_typing :: "[s_context, cl, tf] \<Rightarrow> bool" where
   "\<lbrakk>i < length (s_inst \<S>); ((s_inst \<S>)!i) = \<C>; tf = (t1s _> t2s); \<C>\<lparr>local := (local \<C>) @ t1s @ ts, label := ([t2s] @ (label \<C>)), return := Some t2s\<rparr> \<turnstile> es : ([] _> t2s)\<rbrakk> \<Longrightarrow> cl_typing \<S> (Func_native i tf ts es) (t1s _> t2s)"
|  "cl_typing \<S> (Func_host tf h) tf"

(* lifting the b_e_typing relation to the administrative operators *)
inductive e_typing :: "[s_context, t_context, e list, tf] \<Rightarrow> bool" ("_\<bullet>_ \<turnstile> _ : _" 60)
and       s_typing :: "[s_context, (t list) option, nat, v list, e list, t list] \<Rightarrow> bool" ("_\<bullet>_ \<tturnstile>'_ _ _;_ : _" 60) where
(* section: e_typing *)
  (* lifting *)
  "\<C> \<turnstile> b_es : tf \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> $*b_es : tf"
  (* composition *)
| "\<lbrakk>\<S>\<bullet>\<C> \<turnstile> es : (t1s _> t2s); \<S>\<bullet>\<C> \<turnstile> [e] : (t2s _> t3s)\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> es @ [e] : (t1s _> t3s)"
  (* weakening *)
| "\<S>\<bullet>\<C> \<turnstile> es : (t1s _> t2s) \<Longrightarrow>\<S>\<bullet>\<C> \<turnstile> es : (ts @ t1s _> ts @ t2s)"
  (* trap *)
| "\<S>\<bullet>\<C> \<turnstile> [Trap] : tf"
  (* local *)
| "\<lbrakk>\<S>\<bullet>Some ts \<tturnstile>_i vs;es : ts; length ts = n\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> [Local n i vs es] : ([] _> ts)"
  (* callcl *)
| "\<lbrakk>cl_typing \<S> cl tf\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C>  \<turnstile> [Callcl cl] : tf"
  (* label *)
| "\<lbrakk>\<S>\<bullet>\<C> \<turnstile> e0s : (ts _> t2s); \<S>\<bullet>\<C>\<lparr>label := ([ts] @ (label \<C>))\<rparr> \<turnstile> es : ([] _> t2s); length ts = n\<rbrakk> \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> [Label n e0s es] : ([] _> t2s)"
(* section: s_typing *)
| "\<lbrakk>i < (length (s_inst \<S>)); tvs = map typeof vs; \<C> =((s_inst \<S>)!i)\<lparr>local := (local ((s_inst \<S>)!i) @ tvs), return := rs\<rparr>; \<S>\<bullet>\<C> \<turnstile> es : ([] _> ts); (rs = Some ts) \<or> rs = None\<rbrakk> \<Longrightarrow> \<S>\<bullet>rs \<tturnstile>_i vs;es : ts"

definition "globi_agree gs n g = (n < length gs \<and> gs!n = g)"

definition "memi_agree sm j m = ((\<exists>j' m'. j = Some j' \<and> j' < length sm \<and>  m = Some m' \<and> sm!j' = m') \<or> j = None \<and> m = None)"

definition "funci_agree fs n f = (n < length fs \<and> fs!n = f)"

inductive inst_typing :: "[s_context, inst, t_context] \<Rightarrow> bool" where
  "\<lbrakk>list_all2 (funci_agree (s_funcs \<S>)) fs tfs; list_all2 (globi_agree (s_globs \<S>)) gs tgs; (i = Some i' \<and> i' < length (s_tab \<S>) \<and> (s_tab \<S>)!i' = (the n)) \<or> (i = None \<and> n = None); memi_agree (s_mem \<S>) j m\<rbrakk> \<Longrightarrow> inst_typing \<S> \<lparr>types = ts, funcs = fs, tab = i, mem = j, globs = gs\<rparr> \<lparr>types_t = ts, func_t = tfs, global = tgs, table = n, memory = m, local = [], label = [], return = None\<rparr>"

definition "glob_agree g tg = (tg_mut tg = g_mut g \<and> tg_t tg = typeof (g_val g))"

definition "tab_agree \<S> tcl = (case tcl of None \<Rightarrow> True | Some cl \<Rightarrow> \<exists>tf. cl_typing \<S> cl tf)"

definition "mem_agree bs m = (\<lambda> bs m. m \<le> mem_size bs) bs m"

inductive store_typing :: "[s, s_context] \<Rightarrow> bool" where
  "\<lbrakk>\<S> = \<lparr>s_inst = \<C>s, s_funcs = tfs, s_tab = ns, s_mem = ms, s_globs = tgs\<rparr>; list_all2 (inst_typing \<S>) insts \<C>s; list_all2 (cl_typing \<S>) fs tfs; list_all (tab_agree \<S>) (concat tclss); list_all2 (\<lambda> tcls n. n \<le> length tcls) tclss ns; list_all2 mem_agree bss ms; list_all2 glob_agree gs tgs\<rbrakk> \<Longrightarrow> store_typing \<lparr>s.inst = insts, s.funcs = fs, s.tab = tclss, s.mem = bss, s.globs = gs\<rparr> \<S>"

inductive config_typing :: "[nat, s, v list, e list, t list] \<Rightarrow> bool" ("\<turnstile>'_ _ _;_;_ : _" 60) where
  "\<lbrakk>store_typing s \<S>; \<S>\<bullet>None \<tturnstile>_i vs;es : ts\<rbrakk> \<Longrightarrow> \<turnstile>_i s;vs;es : ts"

(* REDUCTION RELATION *)

inductive reduce_simple :: "[e list, e list] \<Rightarrow> bool" ("\<lparr>_\<rparr> \<leadsto> \<lparr>_\<rparr>" 60) where
  \<comment> \<open>\<open>integer unary ops\<close>\<close>
  unop_i32:"\<lparr>[$C (ConstInt32 c), $(Unop_i T_i32 iop)]\<rparr> \<leadsto> \<lparr>[$C (ConstInt32 (app_unop_i iop c))]\<rparr>"
| unop_i64:"\<lparr>[$C (ConstInt64 c), $(Unop_i T_i64 iop)]\<rparr> \<leadsto> \<lparr>[$C (ConstInt64 (app_unop_i iop c))]\<rparr>"
  \<comment> \<open>\<open>float unary ops\<close>\<close>
| unop_f32:"\<lparr>[$C (ConstFloat32 c), $(Unop_f T_f32 fop)]\<rparr> \<leadsto> \<lparr>[$C (ConstFloat32 (app_unop_f fop c))]\<rparr>"
| unop_f64:"\<lparr>[$C (ConstFloat64 c), $(Unop_f T_f64 fop)]\<rparr> \<leadsto> \<lparr>[$C (ConstFloat64 (app_unop_f fop c))]\<rparr>"
  \<comment> \<open>\<open>int32 binary ops\<close>\<close>
| binop_i32_Some:"\<lbrakk>app_binop_i iop c1 c2 = (Some c)\<rbrakk> \<Longrightarrow> \<lparr>[$C (ConstInt32 c1), $C (ConstInt32 c2), $(Binop_i T_i32 iop)]\<rparr> \<leadsto> \<lparr>[$C (ConstInt32 c)]\<rparr>"
| binop_i32_None:"\<lbrakk>app_binop_i iop c1 c2 = None\<rbrakk> \<Longrightarrow> \<lparr>[$C (ConstInt32 c1), $C (ConstInt32 c2), $(Binop_i T_i32 iop)]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>int64 binary ops\<close>\<close>
| binop_i64_Some:"\<lbrakk>app_binop_i iop c1 c2 = (Some c)\<rbrakk> \<Longrightarrow> \<lparr>[$C (ConstInt64 c1), $C (ConstInt64 c2), $(Binop_i T_i64 iop)]\<rparr> \<leadsto> \<lparr>[$C (ConstInt64 c)]\<rparr>"
| binop_i64_None:"\<lbrakk>app_binop_i iop c1 c2 = None\<rbrakk> \<Longrightarrow> \<lparr>[$C (ConstInt64 c1), $C (ConstInt64 c2), $(Binop_i T_i64 iop)]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>float32 binary ops\<close>\<close>
| binop_f32_Some:"\<lbrakk>app_binop_f fop c1 c2 = (Some c)\<rbrakk> \<Longrightarrow> \<lparr>[$C (ConstFloat32 c1), $C (ConstFloat32 c2), $(Binop_f T_f32 fop)]\<rparr> \<leadsto> \<lparr>[$C (ConstFloat32 c)]\<rparr>"
| binop_f32_None:"\<lbrakk>app_binop_f fop c1 c2 = None\<rbrakk> \<Longrightarrow> \<lparr>[$C (ConstFloat32 c1), $C (ConstFloat32 c2), $(Binop_f T_f32 fop)]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>float64 binary ops\<close>\<close>
| binop_f64_Some:"\<lbrakk>app_binop_f fop c1 c2 = (Some c)\<rbrakk> \<Longrightarrow> \<lparr>[$C (ConstFloat64 c1), $C (ConstFloat64 c2), $(Binop_f T_f64 fop)]\<rparr> \<leadsto> \<lparr>[$C (ConstFloat64 c)]\<rparr>"
| binop_f64_None:"\<lbrakk>app_binop_f fop c1 c2 = None\<rbrakk> \<Longrightarrow> \<lparr>[$C (ConstFloat64 c1), $C (ConstFloat64 c2), $(Binop_f T_f64 fop)]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>testops\<close>\<close>
| testop_i32:"\<lparr>[$C (ConstInt32 c), $(Testop T_i32 testop)]\<rparr> \<leadsto> \<lparr>[$C ConstInt32 (wasm_bool (app_testop_i testop c))]\<rparr>"
| testop_i64:"\<lparr>[$C (ConstInt64 c), $(Testop T_i64 testop)]\<rparr> \<leadsto> \<lparr>[$C ConstInt32 (wasm_bool (app_testop_i testop c))]\<rparr>"
  \<comment> \<open>\<open>int relops\<close>\<close>
| relop_i32:"\<lparr>[$C (ConstInt32 c1), $C (ConstInt32 c2), $(Relop_i T_i32 iop)]\<rparr> \<leadsto> \<lparr>[$C (ConstInt32 (wasm_bool (app_relop_i iop c1 c2)))]\<rparr>"
| relop_i64:"\<lparr>[$C (ConstInt64 c1), $C (ConstInt64 c2), $(Relop_i T_i64 iop)]\<rparr> \<leadsto> \<lparr>[$C (ConstInt32 (wasm_bool (app_relop_i iop c1 c2)))]\<rparr>"
  \<comment> \<open>\<open>float relops\<close>\<close>
| relop_f32:"\<lparr>[$C (ConstFloat32 c1), $C (ConstFloat32 c2), $(Relop_f T_f32 fop)]\<rparr> \<leadsto> \<lparr>[$C (ConstInt32 (wasm_bool (app_relop_f fop c1 c2)))]\<rparr>"
| relop_f64:"\<lparr>[$C (ConstFloat64 c1), $C (ConstFloat64 c2), $(Relop_f T_f64 fop)]\<rparr> \<leadsto> \<lparr>[$C (ConstInt32 (wasm_bool (app_relop_f fop c1 c2)))]\<rparr>"
  \<comment> \<open>\<open>convert\<close>\<close>
| convert_Some:"\<lbrakk>types_agree t1 v; cvt t2 sx v = (Some v')\<rbrakk> \<Longrightarrow> \<lparr>[$(C v), $(Cvtop t2 Convert t1 sx)]\<rparr> \<leadsto> \<lparr>[$(C v')]\<rparr>"
| convert_None:"\<lbrakk>types_agree t1 v; cvt t2 sx v = None\<rbrakk> \<Longrightarrow> \<lparr>[$(C v), $(Cvtop t2 Convert t1 sx)]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>reinterpret\<close>\<close>
| reinterpret:"types_agree t1 v \<Longrightarrow> \<lparr>[$(C v), $(Cvtop t2 Reinterpret t1 None)]\<rparr> \<leadsto> \<lparr>[$(C (wasm_deserialise (bits v) t2))]\<rparr>"
  \<comment> \<open>\<open>unreachable\<close>\<close>
| unreachable:"\<lparr>[$ Unreachable]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>nop\<close>\<close>
| nop:"\<lparr>[$ Nop]\<rparr> \<leadsto> \<lparr>[]\<rparr>"
  \<comment> \<open>\<open>drop\<close>\<close>
| drop:"\<lparr>[$(C v), ($ Drop)]\<rparr> \<leadsto> \<lparr>[]\<rparr>"
  \<comment> \<open>\<open>select\<close>\<close>
| select_false:"int_eq n 0 \<Longrightarrow> \<lparr>[$(C v1), $(C v2), $C (ConstInt32 n), ($ Select)]\<rparr> \<leadsto> \<lparr>[$(C v2)]\<rparr>"
| select_true:"int_ne n 0 \<Longrightarrow> \<lparr>[$(C v1), $(C v2), $C (ConstInt32 n), ($ Select)]\<rparr> \<leadsto> \<lparr>[$(C v1)]\<rparr>"
  \<comment> \<open>\<open>block\<close>\<close>
| block:"\<lbrakk>const_list vs; length vs = n; length t1s = n; length t2s = m\<rbrakk> \<Longrightarrow> \<lparr>vs @ [$(Block (t1s _> t2s) es)]\<rparr> \<leadsto> \<lparr>[Label m [] (vs @ ($* es))]\<rparr>"
  \<comment> \<open>\<open>loop\<close>\<close>
| loop:"\<lbrakk>const_list vs; length vs = n; length t1s = n; length t2s = m\<rbrakk> \<Longrightarrow> \<lparr>vs @ [$(Loop (t1s _> t2s) es)]\<rparr> \<leadsto> \<lparr>[Label n [$(Loop (t1s _> t2s) es)] (vs @ ($* es))]\<rparr>"
  \<comment> \<open>\<open>if\<close>\<close>
| if_false:"int_eq n 0 \<Longrightarrow> \<lparr>[$C (ConstInt32 n), $(If tf e1s e2s)]\<rparr> \<leadsto> \<lparr>[$(Block tf e2s)]\<rparr>"
| if_true:"int_ne n 0 \<Longrightarrow> \<lparr>[$C (ConstInt32 n), $(If tf e1s e2s)]\<rparr> \<leadsto> \<lparr>[$(Block tf e1s)]\<rparr>"
  \<comment> \<open>\<open>label\<close>\<close>
| label_const:"const_list vs \<Longrightarrow> \<lparr>[Label n es vs]\<rparr> \<leadsto> \<lparr>vs\<rparr>"
| label_trap:"\<lparr>[Label n es [Trap]]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>br\<close>\<close>
| br:"\<lbrakk>const_list vs; length vs = n; Lfilled i lholed (vs @ [$(Br i)]) LI\<rbrakk> \<Longrightarrow> \<lparr>[Label n es LI]\<rparr> \<leadsto> \<lparr>vs @ es\<rparr>"
  \<comment> \<open>\<open>br_if\<close>\<close>
| br_if_false:"int_eq n 0 \<Longrightarrow> \<lparr>[$C (ConstInt32 n), $(Br_if i)]\<rparr> \<leadsto> \<lparr>[]\<rparr>"
| br_if_true:"int_ne n 0 \<Longrightarrow> \<lparr>[$C (ConstInt32 n), $(Br_if i)]\<rparr> \<leadsto> \<lparr>[$(Br i)]\<rparr>"
  \<comment> \<open>\<open>br_table\<close>\<close>
| br_table:"\<lbrakk>length is > (nat_of_int c)\<rbrakk> \<Longrightarrow> \<lparr>[$C (ConstInt32 c), $(Br_table is i)]\<rparr> \<leadsto> \<lparr>[$(Br (is!(nat_of_int c)))]\<rparr>"
| br_table_length:"\<lbrakk>length is \<le> (nat_of_int c)\<rbrakk> \<Longrightarrow> \<lparr>[$C (ConstInt32 c), $(Br_table is i)]\<rparr> \<leadsto> \<lparr>[$(Br i)]\<rparr>"
  \<comment> \<open>\<open>local\<close>\<close>
| local_const:"\<lbrakk>const_list es; length es = n\<rbrakk> \<Longrightarrow> \<lparr>[Local n i vs es]\<rparr> \<leadsto> \<lparr>es\<rparr>"
| local_trap:"\<lparr>[Local n i vs [Trap]]\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"
  \<comment> \<open>\<open>return\<close>\<close>
| return:"\<lbrakk>const_list vs; length vs = n; Lfilled j lholed (vs @ [$Return]) es\<rbrakk>  \<Longrightarrow> \<lparr>[Local n i vls es]\<rparr> \<leadsto> \<lparr>vs\<rparr>"
  \<comment> \<open>\<open>tee_local\<close>\<close>
| tee_local:"is_const v \<Longrightarrow> \<lparr>[v, $(Tee_local i)]\<rparr> \<leadsto> \<lparr>[v, v, $(Set_local i)]\<rparr>"
| trap:"\<lbrakk>es \<noteq> [Trap]; Lfilled 0 lholed [Trap] es\<rbrakk> \<Longrightarrow> \<lparr>es\<rparr> \<leadsto> \<lparr>[Trap]\<rparr>"

(* full reduction rule *)
inductive reduce :: "[s, v list, e list, nat, s, v list, e list] \<Rightarrow> bool" ("\<lparr>_;_;_\<rparr> \<leadsto>'_ _ \<lparr>_;_;_\<rparr>" 60) where
  \<comment> \<open>\<open>lifting basic reduction\<close>\<close>
  basic:"\<lparr>e\<rparr> \<leadsto> \<lparr>e'\<rparr> \<Longrightarrow> \<lparr>s;vs;e\<rparr> \<leadsto>_i \<lparr>s;vs;e'\<rparr>"
  \<comment> \<open>\<open>call\<close>\<close>
| call:"\<lparr>s;vs;[$(Call j)]\<rparr> \<leadsto>_i \<lparr>s;vs;[Callcl (sfunc s i j)]\<rparr>"
  \<comment> \<open>\<open>call_indirect\<close>\<close>
| call_indirect_Some:"\<lbrakk>stab s i (nat_of_int c) = Some cl; stypes s i j = tf; cl_type cl = tf\<rbrakk> \<Longrightarrow> \<lparr>s;vs;[$C (ConstInt32 c), $(Call_indirect j)]\<rparr> \<leadsto>_i \<lparr>s;vs;[Callcl cl]\<rparr>"
| call_indirect_None:"\<lbrakk>(stab s i (nat_of_int c) = Some cl \<and> stypes s i j \<noteq> cl_type cl) \<or> stab s i (nat_of_int c) = None\<rbrakk> \<Longrightarrow> \<lparr>s;vs;[$C (ConstInt32 c), $(Call_indirect j)]\<rparr> \<leadsto>_i \<lparr>s;vs;[Trap]\<rparr>"
  \<comment> \<open>\<open>call\<close>\<close>
| callcl_native:"\<lbrakk>cl = Func_native j (t1s _> t2s) ts es; ves = ($$* vcs); length vcs = n; length ts = k; length t1s = n; length t2s = m; (n_zeros ts = zs) \<rbrakk> \<Longrightarrow> \<lparr>s;vs;ves @ [Callcl cl]\<rparr> \<leadsto>_i \<lparr>s;vs;[Local m j (vcs@zs) [$(Block ([] _> t2s) es)]]\<rparr>"
| callcl_host_Some:"\<lbrakk>cl = Func_host (t1s _> t2s) f; ves = ($$* vcs); length vcs = n; length t1s = n; length t2s = m; host_apply s (t1s _> t2s) f vcs hs = Some (s', vcs')\<rbrakk> \<Longrightarrow> \<lparr>s;vs;ves @ [Callcl cl]\<rparr> \<leadsto>_i \<lparr>s';vs;($$* vcs')\<rparr>"
| callcl_host_None:"\<lbrakk>cl = Func_host (t1s _> t2s) f; ves = ($$* vcs); length vcs = n; length t1s = n; length t2s = m\<rbrakk> \<Longrightarrow> \<lparr>s;vs;ves @ [Callcl cl]\<rparr> \<leadsto>_i \<lparr>s;vs;[Trap]\<rparr>"
  \<comment> \<open>\<open>get_local\<close>\<close>
| get_local:"\<lbrakk>length vi = j\<rbrakk> \<Longrightarrow> \<lparr>s;(vi @ [v] @ vs);[$(Get_local j)]\<rparr> \<leadsto>_i \<lparr>s;(vi @ [v] @ vs);[$(C v)]\<rparr>"
  \<comment> \<open>\<open>set_local\<close>\<close>
| set_local:"\<lbrakk>length vi = j\<rbrakk> \<Longrightarrow> \<lparr>s;(vi @ [v] @ vs);[$(C v'), $(Set_local j)]\<rparr> \<leadsto>_i \<lparr>s;(vi @ [v'] @ vs);[]\<rparr>"
  \<comment> \<open>\<open>get_global\<close>\<close>
| get_global:"\<lparr>s;vs;[$(Get_global j)]\<rparr> \<leadsto>_i \<lparr>s;vs;[$ C(sglob_val s i j)]\<rparr>"
  \<comment> \<open>\<open>set_global\<close>\<close>
| set_global:"supdate_glob s i j v = s' \<Longrightarrow> \<lparr>s;vs;[$(C v), $(Set_global j)]\<rparr> \<leadsto>_i \<lparr>s';vs;[]\<rparr>"
  \<comment> \<open>\<open>load\<close>\<close>
| load_Some:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; load m (nat_of_int k) off (t_length t) = Some bs\<rbrakk> \<Longrightarrow> \<lparr>s;vs;[$C (ConstInt32 k), $(Load t None a off)]\<rparr> \<leadsto>_i \<lparr>s;vs;[$C (wasm_deserialise bs t)]\<rparr>"
| load_None:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; load m (nat_of_int k) off (t_length t) = None\<rbrakk> \<Longrightarrow> \<lparr>s;vs;[$C (ConstInt32 k), $(Load t None a off)]\<rparr> \<leadsto>_i \<lparr>s;vs;[Trap]\<rparr>"
  \<comment> \<open>\<open>load packed\<close>\<close>
| load_packed_Some:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; load_packed sx m (nat_of_int k) off (tp_length tp) (t_length t) = Some bs\<rbrakk> \<Longrightarrow> \<lparr>s;vs;[$C (ConstInt32 k), $(Load t (Some (tp, sx)) a off)]\<rparr> \<leadsto>_i \<lparr>s;vs;[$C (wasm_deserialise bs t)]\<rparr>"
| load_packed_None:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; load_packed sx m (nat_of_int k) off (tp_length tp) (t_length t) = None\<rbrakk> \<Longrightarrow> \<lparr>s;vs;[$C (ConstInt32 k), $(Load t (Some (tp, sx)) a off)]\<rparr> \<leadsto>_i \<lparr>s;vs;[Trap]\<rparr>"
  \<comment> \<open>\<open>store\<close>\<close>
| store_Some:"\<lbrakk>types_agree t v; smem_ind s i = Some j; ((mem s)!j) = m; store m (nat_of_int k) off (bits v) (t_length t) = Some mem'\<rbrakk> \<Longrightarrow> \<lparr>s;vs;[$C (ConstInt32 k), $C v, $(Store t None a off)]\<rparr> \<leadsto>_i \<lparr>s\<lparr>mem:= ((mem s)[j := mem'])\<rparr>;vs;[]\<rparr>"
| store_None:"\<lbrakk>types_agree t v; smem_ind s i = Some j; ((mem s)!j) = m; store m (nat_of_int k) off (bits v) (t_length t) = None\<rbrakk> \<Longrightarrow> \<lparr>s;vs;[$C (ConstInt32 k), $C v, $(Store t None a off)]\<rparr> \<leadsto>_i \<lparr>s;vs;[Trap]\<rparr>"
  \<comment> \<open>\<open>store packed\<close>\<close> (* take only (tp_length tp) lower order bytes *)
| store_packed_Some:"\<lbrakk>types_agree t v; smem_ind s i = Some j; ((mem s)!j) = m; store_packed m (nat_of_int k) off (bits v) (tp_length tp) = Some mem'\<rbrakk> \<Longrightarrow> \<lparr>s;vs;[$C (ConstInt32 k), $C v, $(Store t (Some tp) a off)]\<rparr> \<leadsto>_i \<lparr>s\<lparr>mem:= ((mem s)[j := mem'])\<rparr>;vs;[]\<rparr>"
| store_packed_None:"\<lbrakk>types_agree t v; smem_ind s i = Some j; ((mem s)!j) = m; store_packed m (nat_of_int k) off (bits v) (tp_length tp) = None\<rbrakk> \<Longrightarrow> \<lparr>s;vs;[$C (ConstInt32 k), $C v, $(Store t (Some tp) a off)]\<rparr> \<leadsto>_i \<lparr>s;vs;[Trap]\<rparr>"
  \<comment> \<open>\<open>current_memory\<close>\<close>
| current_memory:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; mem_size m = n\<rbrakk> \<Longrightarrow> \<lparr>s;vs;[ $(Current_memory)]\<rparr> \<leadsto>_i \<lparr>s;vs;[$C (ConstInt32 (int_of_nat n))]\<rparr>"
  \<comment> \<open>\<open>grow_memory\<close>\<close>
| grow_memory:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; mem_size m = n; mem_grow m (nat_of_int c) = mem'\<rbrakk> \<Longrightarrow> \<lparr>s;vs;[$C (ConstInt32 c), $(Grow_memory)]\<rparr> \<leadsto>_i \<lparr>s\<lparr>mem:= ((mem s)[j := mem'])\<rparr>;vs;[$C (ConstInt32 (int_of_nat n))]\<rparr>"
  \<comment> \<open>\<open>grow_memory fail\<close>\<close>
| grow_memory_fail:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; mem_size m = n\<rbrakk> \<Longrightarrow> \<lparr>s;vs;[$C (ConstInt32 c),$(Grow_memory)]\<rparr> \<leadsto>_i \<lparr>s;vs;[$C (ConstInt32 int32_minus_one)]\<rparr>"
  (* The bad ones. *)
  \<comment> \<open>\<open>inductive label reduction\<close>\<close>
| label:"\<lbrakk>\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>; Lfilled k lholed es les; Lfilled k lholed es' les'\<rbrakk> \<Longrightarrow> \<lparr>s;vs;les\<rparr> \<leadsto>_i \<lparr>s';vs';les'\<rparr>"
  \<comment> \<open>\<open>inductive local reduction\<close>\<close>
| local:"\<lbrakk>\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>\<rbrakk> \<Longrightarrow> \<lparr>s;v0s;[Local n i vs es]\<rparr> \<leadsto>_j \<lparr>s';v0s;[Local n i vs' es']\<rparr>"

end
