section \<open>Auxiliary Type System Properties\<close>

theory Wasm_Properties_Aux imports Wasm_Axioms begin

lemma typeof_i32:
  assumes "typeof v = T_i32"
  shows "\<exists>c. v = ConstInt32 c"
  using assms
  unfolding typeof_def
  by (cases v) auto

lemma typeof_i64:
  assumes "typeof v = T_i64"
  shows "\<exists>c. v = ConstInt64 c"
  using assms
  unfolding typeof_def
  by (cases v) auto

lemma typeof_f32:
  assumes "typeof v = T_f32"
  shows "\<exists>c. v = ConstFloat32 c"
  using assms
  unfolding typeof_def
  by (cases v) auto

lemma typeof_f64:
  assumes "typeof v = T_f64"
  shows "\<exists>c. v = ConstFloat64 c"
  using assms
  unfolding typeof_def
  by (cases v) auto

lemma exists_v_typeof: "\<exists>v v. typeof v = t"
proof (cases t)
  case T_i32
  fix v
  have "typeof (ConstInt32 v) = t"
    using T_i32
    unfolding typeof_def
    by simp
  thus ?thesis
    using T_i32
    by fastforce
next
  case T_i64
  fix v
  have "typeof (ConstInt64 v) = t"
    using T_i64
    unfolding typeof_def
    by simp
  thus ?thesis
    using T_i64
    by fastforce
next
  case T_f32
  fix v
  have "typeof (ConstFloat32 v) = t"
    using T_f32
    unfolding typeof_def
    by simp
  thus ?thesis
    using T_f32
    by fastforce
next
  case T_f64
  fix v
  have "typeof (ConstFloat64 v) = t"
    using T_f64
    unfolding typeof_def
    by simp
  thus ?thesis
    using T_f64
    by fastforce
qed

lemma lfilled_collapse1:
  assumes "Lfilled n lholed (vs@es) LI"
          "const_list vs"
          "length vs \<ge> l"
  shows "\<exists>lholed'. Lfilled n lholed' ((drop (length vs - l) vs)@es) LI"
  using assms(1)
proof (induction "vs@es" LI rule: Lfilled.induct)
  case (L0 vs' lholed es')
  obtain vs1 vs2 where "vs = vs1@vs2" "length vs2 = l"
    using assms(3)
    by (metis append_take_drop_id diff_diff_cancel length_drop)
  moreover
  hence "const_list (vs'@vs1)"
    using L0(1) assms(2)
    unfolding const_list_def
    by simp
  ultimately
  show ?case
    using Lfilled.intros(1)[of "vs'@vs1" _ es' "vs2@es"]
      by fastforce
next
  case (LN vs lholed n es' l es'' k lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed

lemma lfilled_collapse2:
  assumes "Lfilled n lholed (es@es') LI"
  shows "\<exists>lholed' vs'. Lfilled n lholed' es LI"
  using assms
proof (induction "es@es'" LI rule: Lfilled.induct)
  case (L0 vs lholed es')
  thus ?case
    using Lfilled.intros(1)
    by fastforce
next
  case (LN vs lholed n es' l es'' k lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed

lemma lfilled_collapse3:
  assumes "Lfilled k lholed [Label n les es] LI"
  shows "\<exists>lholed'. Lfilled (Suc k) lholed' es LI"
  using assms
proof (induction "[Label n les es]" LI rule: Lfilled.induct)
  case (L0 vs lholed es')
  have "Lfilled 0 (LBase [] []) es es"
    using Lfilled.intros(1)
    unfolding const_list_def
    by (metis append.left_neutral append_Nil2 list_all_simps(2))
  thus ?case
    using Lfilled.intros(2) L0
    by fastforce
next
  case (LN vs lholed n es' l es'' k lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed


lemma unlift_b_e: assumes "\<S>\<bullet>\<C> \<turnstile> $*b_es : tf" shows "\<C> \<turnstile> b_es : tf"
using assms proof (induction "\<S>" "\<C>" "($*b_es)" "tf" arbitrary: b_es)
  case (1 \<C> b_es tf \<S>)
  then show ?case
    using inj_basic map_injective
    by auto
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  obtain es' e' where "es' @ [e'] = b_es"
    using 2(5)
    by (simp add: snoc_eq_iff_butlast)
  then show ?case using 2
    using b_e_typing.composition
    by fastforce
next                            
  case (3 \<S> \<C> t1s t2s ts)
  then show ?case
    using b_e_typing.weakening
    by blast
qed auto

lemma store_typing_imp_inst_length_eq:
  assumes "store_typing s \<S>"
  shows "length (inst s) = length (s_inst \<S>)"
  using assms list_all2_lengthD
  unfolding store_typing.simps
  by fastforce

lemma store_typing_imp_func_length_eq:
  assumes "store_typing s \<S>"
  shows "length (funcs s) = length (s_funcs \<S>)"
  using assms list_all2_lengthD
  unfolding store_typing.simps
  by fastforce

lemma store_typing_imp_mem_length_eq:
  assumes "store_typing s \<S>"
  shows "length (s.mem s) = length (s_mem \<S>)"
  using assms list_all2_lengthD
  unfolding store_typing.simps
  by fastforce

lemma store_typing_imp_glob_length_eq:
  assumes "store_typing s \<S>"
  shows "length (globs s) = length (s_globs \<S>)"
  using assms list_all2_lengthD
  unfolding store_typing.simps
  by fastforce

lemma store_typing_imp_inst_typing:
  assumes "store_typing s \<S>"
          "i < length (inst s)"
  shows "inst_typing \<S> ((inst s)!i) ((s_inst \<S>)!i)"
  using assms
  unfolding list_all2_conv_all_nth store_typing.simps
  by fastforce

lemma stab_typed_some_imp_member:
  assumes "stab s i c = Some cl"
          "store_typing s \<S>"
          "i < length (inst s)"
  shows "Some cl \<in> set (concat (s.tab s))"
proof -
  obtain k' where k_def:"inst.tab ((inst s)!i) = Some k'"
                       "length ((s.tab s)!k') > c"
                       "((s.tab s)!k')!c = Some cl"
    using stab_unfold assms(1,3)
    by fastforce
  hence "Some cl \<in> set ((s.tab s)!k')"
    using nth_mem
    by fastforce
  moreover
  have "inst_typing \<S> ((inst s)!i) ((s_inst \<S>)!i)"
    using assms(2,3) store_typing_imp_inst_typing
    by blast
  hence "k' < length (s_tab \<S>)"
    using k_def(1)
    unfolding inst_typing.simps stypes_def
    by auto
  hence "k' < length (s.tab s)"
    using assms(2) list_all2_lengthD
    unfolding store_typing.simps
    by fastforce
  ultimately
  show ?thesis
    using k_def
    by auto
qed

lemma stab_typed_some_imp_cl_typed:
  assumes "stab s i c = Some cl"
          "store_typing s \<S>"
          "i < length (inst s)"
  shows "\<exists>tf. cl_typing \<S> cl tf"
proof -
  have "Some cl \<in> set (concat (s.tab s))"
    using assms stab_typed_some_imp_member
    by auto
  moreover
  have "list_all (tab_agree \<S>) (concat (s.tab s))"
    using assms(2)
    unfolding store_typing.simps
    by auto
  ultimately
  show ?thesis
    unfolding in_set_conv_nth list_all_length tab_agree_def
    by fastforce
qed

lemma b_e_type_empty1[dest]: assumes "\<C> \<turnstile> [] : (ts _> ts')" shows "ts = ts'"
  using assms
  by (induction "[]::(b_e list)" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, simp_all)

lemma b_e_type_empty: "(\<C> \<turnstile> [] : (ts _> ts')) = (ts = ts')"
proof (safe)
  assume "\<C> \<turnstile> [] : (ts _> ts')"
  thus "ts = ts'"
    by blast
next
  assume "ts = ts'"
  thus "\<C> \<turnstile> [] : (ts' _> ts')"
    using b_e_typing.empty b_e_typing.weakening
    by fastforce
qed

lemma b_e_type_value:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = C v"
  shows "ts' = ts @ [typeof v]"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_load:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Load t tp_sx a off"
  shows "\<exists>ts'' sec n. ts = ts''@[T_i32] \<and> ts' = ts''@[t] \<and> (memory \<C>) = Some n"
        "load_store_t_bounds a (option_projl tp_sx) t"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_store:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Store t tp a off"
    shows "ts = ts'@[T_i32, t]"
          "\<exists>sec n. (memory \<C>) = Some n"
          "load_store_t_bounds a tp t"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_current_memory:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Current_memory"
  shows "\<exists>sec n. ts' = ts @ [T_i32] \<and> (memory \<C>) = Some n"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_grow_memory:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Grow_memory"
  shows "\<exists>ts''. ts = ts''@[T_i32] \<and> ts = ts' \<and> (\<exists>n. (memory \<C>) = Some n)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct) auto

lemma b_e_type_nop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Nop"
  shows "ts = ts'"
  using assms
  by (induction "[e]"  "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

definition arity_2_result :: "b_e \<Rightarrow> t" where
  "arity_2_result op2 = (case op2 of
                           Binop_i t _ \<Rightarrow> t
                         | Binop_f t _ \<Rightarrow> t
                         | Relop_i t _ \<Rightarrow> T_i32
                         | Relop_f t _ \<Rightarrow> T_i32)"

lemma b_e_type_binop_relop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Binop_i t iop \<or> e = Binop_f t fop \<or> e = Relop_i t irop \<or> e = Relop_f t frop"
  shows "\<exists>ts''. ts = ts''@[t,t] \<and> ts' = ts''@[arity_2_result(e)]"
        "e = Binop_f t fop \<Longrightarrow> is_float_t t"
        "e = Relop_f t frop \<Longrightarrow> is_float_t t"
  using assms
  unfolding arity_2_result_def
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_testop_drop_cvt0:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Testop t testop \<or> e = Drop \<or> e = Cvtop t1 cvtop t2 sx"
  shows "ts \<noteq> []"
  using assms
  by (induction "[e]" "ts _> ts'" arbitrary: ts' rule: b_e_typing.induct, auto)

definition arity_1_result :: "b_e \<Rightarrow> t" where
  "arity_1_result op1 = (case op1 of
                           Unop_i t _ \<Rightarrow> t
                         | Unop_f t _ \<Rightarrow> t
                         | Testop t _ \<Rightarrow> T_i32
                         | Cvtop t1 Convert _ _ \<Rightarrow> t1
                         | Cvtop t1 Reinterpret _ _ \<Rightarrow> t1)"

lemma b_e_type_unop_testop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Unop_i t iop \<or> e = Unop_f t fop \<or> e = Testop t testop"
  shows "\<exists>ts''. ts = ts''@[t] \<and> ts' = ts''@[arity_1_result e]"
        "e = Unop_f t fop \<Longrightarrow> is_float_t t"
  using assms int_float_disjoint
  unfolding arity_1_result_def
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct) fastforce+

lemma b_e_type_cvtop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Cvtop t1 cvtop t sx"
  shows "\<exists>ts''. ts = ts''@[t] \<and> ts' = ts''@[arity_1_result e]"
        "cvtop = Convert \<Longrightarrow> (t1 \<noteq> t) \<and> (sx = None) = ((is_float_t t1 \<and> is_float_t t) \<or> (is_int_t t1 \<and> is_int_t t \<and> (t_length t1 < t_length t)))"
        "cvtop = Reinterpret \<Longrightarrow> (t1 \<noteq> t) \<and> t_length t1 = t_length t"
  using assms
  unfolding arity_1_result_def
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_drop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Drop"
  shows "\<exists>t. ts = ts'@[t]"
  using assms b_e_type_testop_drop_cvt0
by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_select:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Select"
  shows "\<exists>ts'' t. ts = ts''@[t,t,T_i32] \<and> ts' = ts''@[t]"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_call:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Call i"
  shows  "i < length (func_t \<C>)"
         "\<exists>ts'' tf1 tf2. ts = ts''@tf1 \<and> ts' = ts''@tf2 \<and> (func_t \<C>)!i = (tf1 _> tf2)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_call_indirect:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Call_indirect i"
  shows "i < length (types_t \<C>)"
        "\<exists>ts'' tf1 tf2. ts = ts''@tf1@[T_i32] \<and> ts' = ts''@tf2 \<and> (types_t \<C>)!i = (tf1 _> tf2)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_get_local:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Get_local i"
  shows "\<exists>t. ts' = ts@[t] \<and> (local \<C>)!i = t" "i < length(local \<C>)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_set_local:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Set_local i"
  shows "\<exists>t. ts = ts'@[t] \<and> (local \<C>)!i = t" "i < length(local \<C>)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_tee_local:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Tee_local i"
  shows "\<exists>ts'' t. ts = ts''@[t] \<and> ts' = ts''@[t] \<and> (local \<C>)!i = t" "i < length(local \<C>)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_get_global:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Get_global i"
  shows "\<exists>t. ts' = ts@[t] \<and> tg_t((global \<C>)!i) = t" "i < length(global \<C>)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_set_global:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Set_global i"
  shows "\<exists>t. ts = ts'@[t] \<and> (global \<C>)!i = \<lparr>tg_mut = T_mut, tg_t = t\<rparr> \<and> i < length(global \<C>)"
  using assms is_mut_def
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct) auto

lemma b_e_type_block:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Block tf es"
  shows "\<exists>ts'' tfn tfm. tf = (tfn _> tfm) \<and> (ts = ts''@tfn) \<and> (ts' = ts''@tfm) \<and>
                        (\<C>\<lparr>label :=  [tfm] @ label \<C>\<rparr> \<turnstile> es : tf)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_loop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Loop tf es"
  shows "\<exists>ts'' tfn tfm. tf = (tfn _> tfm) \<and> (ts = ts''@tfn) \<and> (ts' = ts''@tfm) \<and>
                        (\<C>\<lparr>label :=  [tfn] @ label \<C>\<rparr> \<turnstile> es : tf)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_if:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = If tf es1 es2"
  shows "\<exists>ts'' tfn tfm. tf = (tfn _> tfm) \<and> (ts = ts''@tfn @ [T_i32]) \<and> (ts' = ts''@tfm) \<and>
                        (\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> es1 : tf) \<and>
                        (\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> es2 : tf)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_br:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Br i"
        shows "i < length(label \<C>)"
              "\<exists>ts_c ts''. ts = ts_c @ ts'' \<and> (label \<C>)!i = ts''"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_br_if:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Br_if i"
        shows "i < length(label \<C>)"
              "\<exists>ts_c ts''. ts = ts_c @ ts'' @ [T_i32] \<and> ts' = ts_c @ ts'' \<and> (label \<C>)!i = ts''"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_br_table:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Br_table is i"
  shows "\<exists>ts_c ts''. list_all (\<lambda>i. i < length(label \<C>) \<and> (label \<C>)!i = ts'') (is@[i]) \<and> ts = ts_c @ ts''@[T_i32]"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, fastforce+)

lemma b_e_type_return:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Return"
        shows "\<exists>ts_c ts''. ts = ts_c @ ts'' \<and> (return \<C>) = Some ts''"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_comp:
  assumes "\<C> \<turnstile> es@[e] : (t1s _> t4s)"
  shows "\<exists>ts'. (\<C> \<turnstile> es : (t1s _> ts')) \<and> (\<C> \<turnstile> [e] : (ts' _> t4s))"
proof (cases es rule: List.rev_cases)
  case Nil
  then show ?thesis
    using assms b_e_typing.empty b_e_typing.weakening
    by fastforce
next
  case (snoc es' e')
  show ?thesis using assms snoc b_e_typing.weakening
    by (induction "es@[e]" "(t1s _> t4s)" arbitrary: t1s t4s, fastforce+)
qed

(* Two special cases - useful for inductions over reduce. *)
lemma b_e_type_comp2_unlift:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$e1, $e2] : (t1s _> t2s)"
  shows "\<exists>ts'. (\<C> \<turnstile> [e1] : (t1s _> ts')) \<and> (\<C> \<turnstile> [e2] : (ts' _> t2s))"
  using assms
        unlift_b_e[of \<S> \<C> "([e1, e2])" "(t1s _> t2s)"]
        b_e_type_comp[of \<C> "[e1]" e2 t1s t2s]
  by simp

lemma b_e_type_comp2_relift:
  assumes "\<C> \<turnstile> [e1] : (t1s _> ts')" "\<C> \<turnstile> [e2] : (ts' _> t2s)"
  shows "\<S>\<bullet>\<C> \<turnstile> [$e1, $e2] : (ts@t1s _> ts@t2s)"
  using assms
        b_e_typing.composition[OF assms]
        e_typing_s_typing.intros(1)[of \<C> "[e1, e2]" "(t1s _> t2s)"]
        e_typing_s_typing.intros(3)[of \<S> \<C> "([$e1,$e2])" t1s t2s ts]
  by simp

lemma b_e_type_value2:
  assumes "\<C> \<turnstile> [C v1, C v2] : (t1s _> t2s)"
  shows "t2s = t1s @ [typeof v1, typeof v2]"
proof -
  obtain ts' where ts'_def:"\<C> \<turnstile> [C v1] : (t1s _> ts')"
                           "\<C> \<turnstile> [C v2] : (ts' _> t2s)"
    using b_e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last_ConsL last_ConsR list.distinct(1))
  have "ts' = t1s @ [typeof v1]"
    using b_e_type_value ts'_def(1)
    by fastforce
  thus ?thesis
    using b_e_type_value ts'_def(2)
    by fastforce
qed

(* Lifting the previous results to all expressions. *)
lemma e_type_comp:
  assumes "\<S>\<bullet>\<C> \<turnstile> es@[e] : (t1s _> t3s)"
  shows "\<exists>ts'. (\<S>\<bullet>\<C> \<turnstile> es : (t1s _> ts')) \<and> (\<S>\<bullet>\<C> \<turnstile> [e] : (ts' _> t3s))"
proof (cases es rule: List.rev_cases)
  case Nil
  thus ?thesis
    using assms e_typing_s_typing.intros(1)
    by (metis append_Nil b_e_type_empty list.simps(8))
next
  case (snoc es' e')
  show ?thesis using assms snoc
  proof (induction "es@[e]" "(t1s _> t3s)" arbitrary: t1s t3s)
    case (1 \<C> b_es \<S>)
    obtain es'' e'' where b_e_defs:"($* (es'' @ [e''])) = ($* b_es)"
      using 1(1,2)
      by (metis Nil_is_map_conv append_is_Nil_conv not_Cons_self2 rev_exhaust)
    hence "($*es'') = es" "($e'') = e"
      using 1(2) inj_basic map_injective
      by auto
    moreover
    have "\<C> \<turnstile> (es'' @ [e'']) : (t1s _> t3s)" using 1(1)
      using inj_basic map_injective b_e_defs
      by blast
    then obtain t2s where "\<C> \<turnstile> es'' : (t1s _> t2s)" "\<C> \<turnstile> [e''] : (t2s _> t3s)"
      using b_e_type_comp
      by blast
    ultimately
    show ?case
      using e_typing_s_typing.intros(1)
      by fastforce
  next
    case (3 \<S> \<C> t1s t2s ts)
    thus ?case
      using e_typing_s_typing.intros(3)
      by fastforce
  qed auto
qed

lemma e_type_comp_conc:
  assumes "\<S>\<bullet>\<C> \<turnstile> es : (t1s _> t2s)"
          "\<S>\<bullet>\<C> \<turnstile> es' : (t2s _> t3s)"
  shows "\<S>\<bullet>\<C> \<turnstile> es@es' : (t1s _> t3s)"
  using assms(2)
proof (induction es' arbitrary: t3s rule: List.rev_induct)
  case Nil
  hence "t2s = t3s"
    using unlift_b_e[of _ _ "[]"] b_e_type_empty[of _ t2s t3s]
    by fastforce
  then show ?case
    using Nil assms(1) e_typing_s_typing.intros(2)
    by fastforce
next
  case (snoc x xs)
  then obtain ts' where "\<S>\<bullet>\<C> \<turnstile> xs : (t2s _> ts')" "\<S>\<bullet>\<C> \<turnstile> [x] : (ts' _> t3s)"
    using e_type_comp[of _ _ xs x]
    by fastforce
  then show ?case
    using snoc(1)[of ts'] e_typing_s_typing.intros(2)[of _ _ "es @ xs" t1s ts' x t3s]
    by simp
qed

(* This isn't needed here, but we unlift for convenience. *)
lemma b_e_type_comp_conc:
  assumes "\<C> \<turnstile> es : (t1s _> t2s)"
          "\<C> \<turnstile> es' : (t2s _> t3s)"
  shows "\<C> \<turnstile> es@es' : (t1s _> t3s)"
proof -
  fix \<S>
  have 1:"\<S>\<bullet>\<C> \<turnstile> $*es : (t1s _> t2s)"
    using e_typing_s_typing.intros(1)[OF assms(1)]
    by fastforce
  have 2:"\<S>\<bullet>\<C> \<turnstile> $*es' : (t2s _> t3s)"
    using e_typing_s_typing.intros(1)[OF assms(2)]
    by fastforce
  show ?thesis
    using e_type_comp_conc[OF 1 2]
    by (simp add:  unlift_b_e)
qed

lemma e_type_comp_conc1:
  assumes "\<S>\<bullet>\<C> \<turnstile> es@es' : (ts _> ts')"
  shows "\<exists>ts''. (\<S>\<bullet>\<C> \<turnstile> es : (ts _> ts'')) \<and> (\<S>\<bullet>\<C> \<turnstile> es' : (ts'' _> ts'))"
  using assms
proof (induction es' arbitrary: ts ts' rule: List.rev_induct)
  case Nil
  thus ?case
    using b_e_type_empty[of _ ts' ts'] e_typing_s_typing.intros(1)
    by fastforce
next
  case (snoc x xs)
  then show ?case
    using e_type_comp[of \<S> \<C> "es @ xs" x ts ts'] e_typing_s_typing.intros(2)[of \<S> \<C> xs _ _ x ts']
    by fastforce
qed

lemma e_type_comp_conc2:
  assumes "\<S>\<bullet>\<C> \<turnstile> es@es'@es'' : (t1s _> t2s)"
  shows "\<exists>ts' ts''. (\<S>\<bullet>\<C> \<turnstile> es : (t1s _> ts'))
                     \<and> (\<S>\<bullet>\<C> \<turnstile> es' : (ts' _> ts''))
                     \<and> (\<S>\<bullet>\<C> \<turnstile> es'' : (ts'' _> t2s))"
proof -
  obtain ts' where "\<S>\<bullet>\<C> \<turnstile> es : (t1s _> ts')" "\<S>\<bullet>\<C> \<turnstile> es'@es'' : (ts' _> t2s)"
    using assms(1) e_type_comp_conc1
    by fastforce
  moreover
  then obtain ts'' where "\<S>\<bullet>\<C> \<turnstile> es' : (ts' _> ts'')" "\<S>\<bullet>\<C> \<turnstile> es'' : (ts'' _> t2s)"
    using e_type_comp_conc1
    by fastforce
  ultimately
  show ?thesis
    by fastforce
qed

lemma b_e_type_value_list:
  assumes "(\<C> \<turnstile> es@[C v] : (ts _> ts'@[t]))"
  shows "(\<C> \<turnstile> es : (ts _> ts'))"
        "(typeof v = t)"
proof -
  obtain ts'' where "(\<C> \<turnstile> es : (ts _> ts''))" "(\<C> \<turnstile> [C v] : (ts'' _> ts' @ [t]))"
    using b_e_type_comp assms
    by blast
  thus "(\<C> \<turnstile> es : (ts _> ts'))" "(typeof v = t)"
    using b_e_type_value[of \<C> "C v" "ts''" "ts' @ [t]"]
    by auto
qed

lemma e_type_label:
  assumes "\<S>\<bullet>\<C> \<turnstile> [Label n es0 es] : (ts _> ts')"
  shows "\<exists>tls t2s. (ts' = (ts@t2s))
                \<and> length tls = n
                \<and> (\<S>\<bullet>\<C> \<turnstile> es0 : (tls _> t2s))
                \<and> (\<S>\<bullet>\<C>\<lparr>label := [tls] @ (label \<C>)\<rparr> \<turnstile> es : ([] _> t2s))"
  using assms
proof (induction "\<S>" "\<C>" "[Label n es0 es]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  then show ?case
    by (simp add: map_eq_Cons_conv)
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis append_self_conv2 b_e_type_empty last_snoc list.simps(8) unlift_b_e)
next
  case (3 \<S> \<C> t1s t2s ts)
  then show ?case
    by simp
next
  case (7 \<S> \<C> t2s)
  then show ?case
    by fastforce
qed

lemma e_type_callcl_native:
  assumes "\<S>\<bullet>\<C> \<turnstile> [Callcl cl] : (t1s' _> t2s')"
          "cl = Func_native i tf ts es"
  shows "\<exists>t1s t2s ts_c. (t1s' = ts_c @ t1s)
                         \<and> (t2s' = ts_c @ t2s)
                         \<and> tf = (t1s _> t2s)
                         \<and> i < length (s_inst \<S>)
                         \<and> (((s_inst \<S>)!i)\<lparr>local := (local ((s_inst \<S>)!i)) @ t1s @ ts, label := ([t2s] @ (label ((s_inst \<S>)!i))), return := Some t2s\<rparr>  \<turnstile> es : ([] _> t2s))"
  using assms
proof (induction "\<S>" "\<C>" "[Callcl cl]" "(t1s' _> t2s')" arbitrary: t1s' t2s')
  case (1 \<C> b_es \<S>)
  thus ?case
    by auto
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  have "\<C> \<turnstile> [] : (t1s _> t2s)"
    using 2(1,5) unlift_b_e
    by (metis Nil_is_map_conv append_Nil butlast_snoc)
  thus ?case
    using 2(4,5,6)
    by fastforce
next
  case (3 \<S> \<C> t1s t2s ts)
    thus ?case
    by fastforce
next
  case (6 \<S> \<C>)
  thus ?case
    unfolding cl_typing.simps
    by fastforce
qed

lemma e_type_callcl_host:
  assumes "\<S>\<bullet>\<C> \<turnstile> [Callcl cl] : (t1s' _> t2s')"
          "cl = Func_host tf f"
  shows "\<exists>t1s t2s ts_c. (t1s' = ts_c @ t1s)
                        \<and> (t2s' = ts_c @ t2s)
                        \<and> tf = (t1s _> t2s)"
  using assms
proof (induction "\<S>" "\<C>" "[Callcl cl]" "(t1s' _> t2s')" arbitrary: t1s' t2s')
  case (1 \<C> b_es \<S>)
  thus ?case
    by auto
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  have "\<C> \<turnstile> [] : (t1s _> t2s)"
    using 2(1,5) unlift_b_e
    by (metis Nil_is_map_conv append_Nil butlast_snoc)
  thus ?case
    using 2(4,5,6)
    by fastforce
next
  case (3 \<S> \<C> t1s t2s ts)
    thus ?case
    by fastforce
next
  case (6 \<S> \<C>)
  thus ?case
    unfolding cl_typing.simps
    by fastforce
qed

lemma e_type_callcl:
  assumes "\<S>\<bullet>\<C> \<turnstile> [Callcl cl] : (t1s' _> t2s')"
  shows "\<exists>t1s t2s ts_c. (t1s' = ts_c @ t1s)
                        \<and> (t2s' = ts_c @ t2s)
                        \<and> cl_type cl = (t1s _> t2s)"
proof (cases cl)
  case (Func_native x11 x12 x13 x14)
  thus ?thesis
    using e_type_callcl_native[OF assms]
    unfolding cl_type_def
    by (cases x12) fastforce
next
  case (Func_host x21 x22)
  thus ?thesis
    using e_type_callcl_host[OF assms]
    unfolding cl_type_def
    by fastforce
qed

lemma s_type_unfold:
  assumes "\<S>\<bullet>rs \<tturnstile>_i vs;es : ts"
  shows "i < length (s_inst \<S>)"
        "(rs = Some ts) \<or> rs = None"
        "(\<S>\<bullet>((s_inst \<S>)!i)\<lparr>local := (local ((s_inst \<S>)!i)) @ (map typeof vs), return := rs\<rparr> \<turnstile> es : ([] _> ts))"
  using assms
  by (induction vs es ts, auto)

lemma e_type_local:
  assumes "\<S>\<bullet>\<C> \<turnstile> [Local n i vs es] : (ts _> ts')"
  shows "\<exists>tls. i < length (s_inst \<S>)
               \<and> length tls = n
               \<and> (\<S>\<bullet>((s_inst \<S>)!i)\<lparr>local := (local ((s_inst \<S>)!i)) @ (map typeof vs), return := Some tls\<rparr> \<turnstile> es : ([] _> tls))
               \<and> ts' = ts @ tls"
  using assms
proof (induction "\<S>" "\<C>" "[Local n i vs es]" "(ts _> ts')" arbitrary: ts ts')
  case (2 \<S> \<C> es' t1s t2s e t3s)
  have "t1s = t2s"
    using 2 unlift_b_e
    by force
  thus ?case
    using 2
    by simp
qed (auto simp add: unlift_b_e s_typing.simps)

lemma e_type_local_shallow:
  assumes "\<S>\<bullet>\<C> \<turnstile> [Local n i vs es] : (ts _> ts')"
  shows "\<exists>tls. length tls = n \<and> ts' = ts@tls \<and> (\<S>\<bullet>(Some tls) \<tturnstile>_i vs;es : tls)"
  using assms
proof (induction "\<S>" "\<C>" "[Local n i vs es]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  thus ?case
  by (metis e.distinct(7) map_eq_Cons_D)
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  thus ?case
  by simp (metis append_Nil append_eq_append_conv e_type_comp_conc e_type_local)
qed simp_all

(* Some proofs treat (lists of) consts as an opaque (typed) arrangement. *)
lemma e_type_const_unwrap:
  assumes "is_const e"
  shows "\<exists>v. e = $C v"
  using assms
proof (cases e)
  case (Basic x1)
  then show ?thesis
    using assms
  proof (cases x1)
    case (EConst x23)
      thus ?thesis
        using Basic e_typing_s_typing.intros(1,3)
        by fastforce
  qed  (simp_all add: is_const_def)
qed (simp_all add: is_const_def)

lemma is_const_list1:
  assumes "ves = map (Basic \<circ> EConst) vs"
  shows "const_list ves"
  using assms
proof (induction vs arbitrary: ves)
  case Nil
  then show ?case
    unfolding const_list_def
    by simp
next
  case (Cons a vs)
  then obtain ves' where "ves' = map (Basic \<circ> EConst) vs"
    by blast
  moreover
  have "is_const ((Basic \<circ> EConst) a)"
    unfolding is_const_def
    by simp
  ultimately
  show ?case
    using Cons
    unfolding const_list_def
      (* WHYYYYYY *)
    by auto
qed

lemma is_const_list:
  assumes "ves = $$* vs"
  shows "const_list ves"
  using assms is_const_list1
  unfolding comp_def
  by auto

lemma const_list_cons_last:
  assumes "const_list (es@[e])"
  shows "const_list es"
        "is_const e"
  using assms list_all_append[of is_const es "[e]"]
  unfolding const_list_def
  by auto

lemma e_type_const1:
  assumes "is_const e"
  shows "\<exists>t. (\<S>\<bullet>\<C> \<turnstile> [e] : (ts _> ts@[t]))"
  using assms
proof (cases e)
  case (Basic x1)
  then show ?thesis
    using assms
  proof (cases x1)
    case (EConst x23)
      hence "\<C> \<turnstile> [x1] : ([] _> [typeof x23])"
        by (simp add: b_e_typing.intros(1))
      thus ?thesis
        using Basic e_typing_s_typing.intros(1,3)
        by (metis append_Nil2 to_e_list_1)
  qed  (simp_all add: is_const_def)
qed (simp_all add: is_const_def)

lemma e_type_const:
  assumes "is_const e"
          "\<S>\<bullet>\<C> \<turnstile> [e] : (ts _> ts')"
  shows  "\<exists>t. (ts' = ts@[t]) \<and> (\<S>\<bullet>\<C>' \<turnstile> [e] : ([] _> [t]))"
  using assms
proof (cases e)
  case (Basic x1)
  then show ?thesis
    using assms
  proof (cases x1)
    case (EConst x23)
      then have "ts' = ts @ [typeof x23]"
        by (metis (no_types) Basic assms(2) b_e_type_value list.simps(8,9) unlift_b_e)
      moreover
      have "\<S>\<bullet>\<C>' \<turnstile> [e] : ([] _> [typeof x23])"
        using Basic EConst b_e_typing.intros(1) e_typing_s_typing.intros(1)
        by fastforce
      ultimately
      show ?thesis
        by simp
  qed  (simp_all add: is_const_def)
qed (simp_all add: is_const_def)

lemma const_typeof:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C v] : ([] _> [t])"
  shows "typeof v = t"
  using assms
proof -
  have "\<C> \<turnstile> [C v] : ([] _> [t])"
    using unlift_b_e assms
    by fastforce
  thus ?thesis
    by (induction "[C v]" "([] _> [t])" rule: b_e_typing.induct, auto)
qed

lemma e_type_const_list:
  assumes "const_list vs"
          "\<S>\<bullet>\<C> \<turnstile> vs : (ts _> ts')"
  shows   "\<exists>tvs. ts' = ts @ tvs \<and> length vs = length tvs \<and> (\<S>\<bullet>\<C>' \<turnstile> vs : ([] _> tvs))"
  using assms
proof (induction vs arbitrary: ts ts' rule: List.rev_induct)
  case Nil
  have "\<S>\<bullet>\<C>' \<turnstile> [] : ([] _> [])"
    using b_e_type_empty[of \<C>' "[]" "[]"] e_typing_s_typing.intros(1)
    by fastforce
  thus ?case
    using Nil
    by (metis append_Nil2 b_e_type_empty list.map(1) list.size(3) unlift_b_e)
next
  case (snoc x xs)
  hence v_lists:"list_all is_const xs" "is_const x"
  unfolding const_list_def
  by simp_all
  obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> xs : (ts _> ts'')" "\<S>\<bullet>\<C> \<turnstile> [x] : (ts'' _> ts')"
    using snoc(3) e_type_comp
    by fastforce
  then obtain ts_b where ts_b_def:"ts'' = ts @ ts_b" "length xs = length ts_b" "\<S>\<bullet>\<C>' \<turnstile> xs : ([] _> ts_b)"
    using snoc(1) v_lists(1)
    unfolding const_list_def
    by fastforce
  then obtain t where t_def:"ts' = ts @ ts_b @ [t]" "\<S>\<bullet>\<C>' \<turnstile> [x] : ([] _> [t])"
    using e_type_const v_lists(2) ts''_def
    by fastforce
  moreover
  then have "length (ts_b@[t]) = length (xs@[x])"
    using ts_b_def(2)
    by simp
  moreover
  have "\<S>\<bullet>\<C>' \<turnstile> (xs@[x]) : ([] _> ts_b@[t])"
    using ts_b_def(3) t_def e_typing_s_typing.intros(2,3)
    by fastforce
  ultimately
  show ?case
    by simp
qed

lemma e_type_const_list_snoc:
  assumes "const_list vs"
          "\<S>\<bullet>\<C> \<turnstile> vs : ([] _> ts@[t])"
  shows "\<exists>vs1 v2. (\<S>\<bullet>\<C> \<turnstile> vs1 : ([] _> ts))
                   \<and> (\<S>\<bullet>\<C> \<turnstile> [v2] : (ts _> ts@[t]))
                   \<and> (vs = vs1@[v2])
                   \<and> const_list vs1
                   \<and> is_const v2"
  using assms
proof -
  obtain vs' v where vs_def:"vs = vs'@[v]"
    using e_type_const_list[OF assms(1,2)]
    by (metis append_Nil append_eq_append_conv list.size(3) snoc_eq_iff_butlast)
  hence consts_def:"const_list vs'" "is_const v"
    using assms(1)
    unfolding const_list_def
    by auto
  obtain ts' where ts'_def:"\<S>\<bullet>\<C> \<turnstile> vs' : ([] _> ts')" "\<S>\<bullet>\<C> \<turnstile> [v] : (ts' _> ts@[t])"
    using vs_def assms(2) e_type_comp[of \<S> \<C> vs' v "[]" "ts@[t]"]
    by fastforce
  obtain c where "v = $C c"
    using e_type_const_unwrap consts_def(2)
    by fastforce
  hence "ts' = ts"
    using ts'_def(2) unlift_b_e[of \<S> \<C> "[C c]"] b_e_type_value
    by fastforce
  thus ?thesis using ts'_def vs_def consts_def
    by simp
qed
    
lemma e_type_const_list_cons:
  assumes "const_list vs"
          "\<S>\<bullet>\<C> \<turnstile> vs : ([] _> (ts1@ts2))"
  shows "\<exists>vs1 vs2. (\<S>\<bullet>\<C> \<turnstile> vs1 : ([] _> ts1))
                   \<and> (\<S>\<bullet>\<C> \<turnstile> vs2 : (ts1 _> (ts1@ts2)))
                   \<and> vs = vs1@vs2
                   \<and> const_list vs1
                   \<and> const_list vs2"
  using assms
proof (induction "ts1@ts2" arbitrary: vs ts1 ts2 rule: List.rev_induct)
  case Nil
  thus ?case
    using e_type_const_list
    by fastforce
next
  case (snoc t ts)
  note snoc_outer = snoc
  show ?case
  proof (cases ts2 rule: List.rev_cases)
    case Nil
    have "\<S>\<bullet>\<C> \<turnstile> [] : (ts1 _> ts1 @ [])"
      using b_e_typing.empty b_e_typing.weakening e_typing_s_typing.intros(1)
      by fastforce
    then show ?thesis
      using snoc(3,4) Nil
      unfolding const_list_def
      by auto
  next
    case (snoc ts2' a)
    obtain vs1 v2 where vs1_def:"(\<S>\<bullet>\<C> \<turnstile> vs1 : ([] _> ts1 @ ts2'))"
                                "(\<S>\<bullet>\<C> \<turnstile> [v2] : (ts1 @ ts2' _> ts1 @ ts2' @[t]))"
                                "(vs = vs1@[v2])"
                                "const_list vs1"
                                "is_const v2"
                                "ts = ts1 @ ts2'"
      using e_type_const_list_snoc[OF snoc_outer(3), of \<S> \<C> "ts1@ts2'" t]
            snoc_outer(2,4) snoc
      by fastforce
    show ?thesis
      using snoc_outer(1)[OF vs1_def(6,4,1)] snoc_outer(2) vs1_def(3,5)
            e_typing_s_typing.intros(2)[OF _ vs1_def(2), of _ ts1]
            snoc
      unfolding const_list_def
      by fastforce
  qed
qed

lemma e_type_const_conv_vs:
  assumes "const_list ves"
  shows "\<exists>vs. ves = $$* vs"
  using assms
proof (induction ves)
  case Nil
  thus ?case
    by simp
next
  case (Cons a ves)
  thus ?case
  using e_type_const_unwrap
  unfolding const_list_def
  by (metis (no_types, lifting) list.pred_inject(2) list.simps(9)) 
qed

lemma types_exist_lfilled:
  assumes "Lfilled k lholed es lfilled"
          "\<S>\<bullet>\<C> \<turnstile> lfilled : (ts _> ts')"
  shows "\<exists>t1s t2s \<C>' arb_label. (\<S>\<bullet>\<C>\<lparr>label := arb_label@(label \<C>)\<rparr> \<turnstile> es : (t1s _> t2s))"
  using assms
proof (induction arbitrary: \<C> ts ts' rule: Lfilled.induct)
  case (L0 vs lholed es' es)
  hence "\<S>\<bullet>(\<C>\<lparr>label := label \<C>\<rparr>) \<turnstile> vs @ es @ es' : (ts _> ts')"
    by simp
  thus ?case
    using e_type_comp_conc2
    by (metis append_Nil)
next
  case (LN vs lholed n es' l es'' k es lfilledk)
  obtain ts'' ts''' where "\<S>\<bullet>\<C> \<turnstile> [Label n es' lfilledk]  : (ts'' _> ts''')"
    using e_type_comp_conc2[OF LN(5)]
    by fastforce
  then obtain t1s t2s ts where test:"\<S>\<bullet>\<C>\<lparr>label := [ts] @ (label \<C>)\<rparr> \<turnstile> lfilledk  : (t1s _> t2s)"
    using e_type_label
    by metis
  show ?case
    using LN(4)[OF test(1)]
    by simp (metis append.assoc append_Cons append_Nil)
qed

lemma types_exist_lfilled_weak:
  assumes "Lfilled k lholed es lfilled"
          "\<S>\<bullet>\<C> \<turnstile> lfilled : (ts _> ts')"
  shows "\<exists>t1s t2s \<C>' arb_label arb_return. (\<S>\<bullet>\<C>\<lparr>label := arb_label, return := arb_return\<rparr> \<turnstile> es : (t1s _> t2s))"
proof -
  have "\<exists>t1s t2s \<C>' arb_label. (\<S>\<bullet>\<C>\<lparr>label := arb_label, return := (return \<C>)\<rparr> \<turnstile> es : (t1s _> t2s))"
    using types_exist_lfilled[OF assms]
    by fastforce
  thus ?thesis
    by fastforce
qed

lemma store_typing_imp_func_agree:
  assumes "store_typing s \<S>"
          "i < length (s_inst \<S>)"
          "j < length (func_t ((s_inst \<S>)!i))"
  shows "(sfunc_ind s i j) < length (s_funcs \<S>)"
        "cl_typing \<S> (sfunc s i j) ((s_funcs \<S>)!(sfunc_ind s i j))"
        "((s_funcs \<S>)!(sfunc_ind s i j)) = (func_t ((s_inst \<S>)!i))!j"
proof -
  have funcs_agree:"list_all2 (cl_typing \<S>) (funcs s) (s_funcs \<S>)"
    using assms(1)
    unfolding store_typing.simps
    by auto
  have "list_all2 (funci_agree (s_funcs \<S>)) (inst.funcs ((inst s)!i)) (func_t ((s_inst \<S>)!i))"
    using assms(1,2) store_typing_imp_inst_length_eq store_typing_imp_inst_typing
    by (fastforce simp add: inst_typing.simps)
  hence "funci_agree (s_funcs \<S>) ((inst.funcs ((inst s)!i))!j) ((func_t ((s_inst \<S>)!i))!j)"
    using assms(3) list_all2_nthD2
    by blast
  thus "(sfunc_ind s i j) < length (s_funcs \<S>)"
       "((s_funcs \<S>)!(sfunc_ind s i j)) = (func_t ((s_inst \<S>)!i))!j"
    unfolding funci_agree_def sfunc_ind_def
    by auto
  thus "cl_typing \<S> (sfunc s i j) ((s_funcs \<S>)!(sfunc_ind s i j))"
    using funcs_agree list_all2_nthD2
    unfolding sfunc_def
    by fastforce
qed

lemma store_typing_imp_glob_agree:
  assumes "store_typing s \<S>"
          "i < length (s_inst \<S>)"
          "j < length (global ((s_inst \<S>)!i))"
  shows "(sglob_ind s i j) < length (s_globs \<S>)"
        "glob_agree (sglob s i j) ((s_globs \<S>)!(sglob_ind s i j))"
        "((s_globs \<S>)!(sglob_ind s i j)) = (global ((s_inst \<S>)!i))!j"
proof -
  have globs_agree:"list_all2 glob_agree (globs s) (s_globs \<S>)"
    using assms(1)
    unfolding store_typing.simps
    by auto
  have "list_all2 (globi_agree (s_globs \<S>)) (inst.globs ((inst s)!i)) (global ((s_inst \<S>)!i))"
    using assms(1,2) store_typing_imp_inst_length_eq store_typing_imp_inst_typing
    by (fastforce simp add: inst_typing.simps)
  hence "globi_agree (s_globs \<S>) ((inst.globs ((inst s)!i))!j) ((global ((s_inst \<S>)!i))!j)"
    using assms(3) list_all2_nthD2
    by blast
  thus "(sglob_ind s i j) < length (s_globs \<S>)"
       "((s_globs \<S>)!(sglob_ind s i j)) = (global ((s_inst \<S>)!i))!j"
    unfolding globi_agree_def sglob_ind_def
    by auto
  thus "glob_agree (sglob s i j) ((s_globs \<S>)!(sglob_ind s i j))"
    using globs_agree list_all2_nthD2
    unfolding sglob_def
    by fastforce
qed

lemma store_typing_imp_mem_agree_Some:
  assumes "store_typing s \<S>"
          "i < length (s_inst \<S>)"
          "smem_ind s i = Some j"
  shows "j < length (s_mem \<S>)"
        "mem_agree ((mem s)!j) ((s_mem \<S>)!j)"
        "\<exists>x. ((s_mem \<S>)!j) = x \<and> (memory ((s_inst \<S>)!i)) = Some x"
proof -
  have mems_agree:"list_all2 mem_agree (mem s) (s_mem \<S>)"
  using assms(1)
  unfolding store_typing.simps
  by auto
  hence "memi_agree (s_mem \<S>) ((inst.mem ((inst s)!i))) ((memory ((s_inst \<S>)!i)))"
    using assms(1,2) store_typing_imp_inst_length_eq store_typing_imp_inst_typing
    by (fastforce simp add: inst_typing.simps)
  thus "j < length (s_mem \<S>)"
       "\<exists>x. ((s_mem \<S>)!j) = x \<and> (memory ((s_inst \<S>)!i)) = Some x"
    using assms(3)
    unfolding memi_agree_def smem_ind_def
    by auto
  thus "mem_agree ((mem s)!j) ((s_mem \<S>)!j)"
    using mems_agree list_all2_nthD2
    unfolding sglob_def
    by fastforce
qed

lemma store_typing_imp_mem_agree_None:
  assumes "store_typing s \<S>"
          "i < length (s_inst \<S>)"
          "smem_ind s i = None"
  shows "(memory ((s_inst \<S>)!i)) = None"
proof -
  have mems_agree:"list_all2 mem_agree (mem s) (s_mem \<S>)"
  using assms(1)
  unfolding store_typing.simps
  by auto
  hence "memi_agree (s_mem \<S>) ((inst.mem ((inst s)!i))) ((memory ((s_inst \<S>)!i)))"
    using assms(1,2) store_typing_imp_inst_length_eq store_typing_imp_inst_typing
    by (fastforce simp add: inst_typing.simps)
  thus ?thesis
    using assms(3)
    unfolding memi_agree_def smem_ind_def
    by auto
qed

lemma store_mem_exists:
  assumes "i < length (s_inst \<S>)"
          "store_typing s \<S>"
  shows "Option.is_none (memory ((s_inst \<S>)!i)) = Option.is_none (inst.mem ((inst s)!i))"
proof -
  obtain j where j_def:"j = (inst.mem ((inst s)!i))"
    by blast
  obtain m where m_def:"m = (memory ((s_inst \<S>)!i))"
    by blast
  have inst_typ:"inst_typing \<S> ((inst s)!i) ((s_inst \<S>)!i)"
    using assms
    unfolding store_typing.simps list_all2_conv_all_nth
    by auto
  thus ?thesis
    unfolding inst_typing.simps memi_agree_def
    by auto
qed

lemma store_preserved_mem:
  assumes "store_typing s \<S>"
          "s' = s\<lparr>s.mem := (s.mem s)[i := mem']\<rparr>"
          "mem_size mem' \<ge> mem_size orig_mem"
          "((s.mem s)!i) = orig_mem"
  shows "store_typing s' \<S>"
proof -
  obtain insts fs clss bss gs where "s = \<lparr>inst = insts, funcs = fs, tab = clss, mem = bss, globs = gs\<rparr>"
    using s.cases
    by blast
  moreover
  obtain insts' fs' clss' bss' gs' where "s' = \<lparr>inst = insts', funcs = fs', tab = clss', mem = bss', globs = gs'\<rparr>"
    using s.cases
    by blast
  moreover
  obtain \<C>s tfs ns ms tgs where "\<S> = \<lparr>s_inst = \<C>s, s_funcs = tfs, s_tab = ns, s_mem = ms, s_globs = tgs\<rparr>"
    using s_context.cases
    by blast
  moreover
  note s_S_defs = calculation
  hence
  "insts = insts'"
  "fs = fs'"
  "clss = clss'"
  "gs = gs'"
    using assms(2)
    by simp_all
  hence
  "list_all2 (inst_typing \<S>) insts' \<C>s"
  "list_all2 (cl_typing \<S>) fs' tfs"
  "list_all (tab_agree \<S>) (concat clss')"
  "list_all2 (\<lambda>cls n. n \<le> length cls) clss' ns"
  "list_all2 glob_agree gs' tgs"
    using s_S_defs assms(1)
    unfolding store_typing.simps
    by auto
  moreover
  have "list_all2 (\<lambda> bs m. m \<le> mem_size bs) bss' ms"
  proof -
    have "length bss = length bss'"
      using assms(2)  s_S_defs
      by (simp)
    moreover
    (* Memory correct before execution. *)
    have initial_mem:"list_all2 (\<lambda> bs m. m \<le> mem_size bs) bss ms"
      using assms(1) s_S_defs
      unfolding store_typing.simps mem_agree_def
      by blast
    have "\<And>n. n < length bss \<Longrightarrow> (\<lambda> bs m. m \<le> mem_size bs) (bss'!n) (ms!n)"
    proof -
      fix n
      assume local_assms:"n < length bss"
      obtain \<C>_m where cmdef:"\<C>_m = \<C>s ! n"
        by blast
      hence "(\<lambda> bs m. m \<le> mem_size bs) (bss!n) (ms!n)"
        using initial_mem local_assms
        unfolding list_all2_conv_all_nth
        by simp
      thus "(\<lambda> bs m. m \<le> mem_size bs) (bss'!n) (ms!n)"
        using assms(2,3,4) s_S_defs local_assms
        by (cases "n=i", auto)
    qed
    ultimately
    show ?thesis
      by (metis initial_mem list_all2_all_nthI list_all2_lengthD)
  qed
  ultimately
  show ?thesis
    unfolding store_typing.simps mem_agree_def
    by simp
qed

lemma types_agree_imp_e_typing:
  assumes "types_agree t v"
  shows "\<S>\<bullet>\<C> \<turnstile> [$C v] : ([] _> [t])"
  using assms e_typing_s_typing.intros(1)[OF b_e_typing.intros(1)]
  unfolding types_agree_def
  by fastforce

lemma list_types_agree_imp_e_typing:
  assumes "list_all2 types_agree ts vs"
  shows "\<S>\<bullet>\<C> \<turnstile> $$* vs : ([] _> ts)"
  using assms
proof (induction rule: list_all2_induct)
  case Nil
  thus ?case
    using b_e_typing.empty e_typing_s_typing.intros(1)
    by fastforce
next
  case (Cons t ts v vs)
  hence "\<S>\<bullet>\<C> \<turnstile> [$C v] : ([] _> [t])"
    using types_agree_imp_e_typing
    by fastforce
  thus ?case
    using e_typing_s_typing.intros(3)[OF Cons(3), of "[t]"] e_type_comp_conc
    by fastforce
qed

lemma b_e_typing_imp_list_types_agree:
  assumes "\<C> \<turnstile> (map (\<lambda>v. C v) vs) : (ts' _> ts'@ts)"
  shows "list_all2 types_agree ts vs"
  using assms
proof (induction "(map (\<lambda>v. C v) vs)" "(ts' _> ts'@ts)" arbitrary: ts ts' vs rule: b_e_typing.induct)
  case (composition \<C> es t1s t2s e)
  obtain vs1 vs2 where es_e_def:"es = map EConst vs1" "[e] = map EConst vs2" "vs1@vs2=vs"  
    using composition(5)
    by (metis (no_types) last_map list.simps(8,9) map_butlast snoc_eq_iff_butlast)
  have "const_list ($*es)"
    using es_e_def(1) is_const_list1
    by auto
  then obtain tvs1 where "t2s = t1s@tvs1"
    using e_type_const_list e_typing_s_typing.intros(1)[OF composition(1)]
    by fastforce
  moreover
  have "const_list ($*[e])"
    using es_e_def(2) is_const_list1
    by auto
  then obtain tvs2 where "t1s @ ts = t2s @ tvs2"
    using e_type_const_list e_typing_s_typing.intros(1)[OF composition(3)]
    by fastforce
  ultimately
  show ?case
    using composition(2,4,5) es_e_def
    by (auto simp add: list_all2_appendI)
qed (auto simp add: types_agree_def)

lemma e_typing_imp_list_types_agree:
  assumes "\<S>\<bullet>\<C> \<turnstile> ($$* vs) : (ts' _> ts'@ts)"
  shows "list_all2 types_agree ts vs"
proof -
  have "($$* vs) = $* (map (\<lambda>v. C v) vs)"
    by simp
  thus ?thesis
    using assms unlift_b_e b_e_typing_imp_list_types_agree
    by (fastforce simp del: map_map)
qed

lemma store_extension_imp_store_typing:
  assumes "store_extension s s'"
          "store_typing s \<S>"
  shows "store_typing s' \<S>"
proof -
  obtain insts fs clss bss gs where "s = \<lparr>inst = insts, funcs = fs, tab = clss, mem = bss, globs = gs\<rparr>"
    using s.cases
    by blast
  moreover
  obtain insts' fs' clss' bss' gs' where "s' = \<lparr>inst = insts', funcs = fs', tab = clss', mem = bss', globs = gs'\<rparr>"
    using s.cases
    by blast
  moreover
  obtain \<C>s tfs ns ms tgs where "\<S> = \<lparr>s_inst = \<C>s, s_funcs = tfs, s_tab = ns, s_mem = ms, s_globs = tgs\<rparr>"
    using s_context.cases
    by blast
  moreover
  note s_S_defs = calculation
  hence
  "insts = insts'"
  "fs = fs'"
  "clss = clss'"
  "gs = gs'"
    using assms(1)
    unfolding store_extension.simps
    by simp_all
  hence
  "list_all2 (inst_typing \<S>) insts' \<C>s"
  "list_all2 (cl_typing \<S>) fs' tfs"
  "list_all (tab_agree \<S>) (concat clss')"
  "list_all2 (\<lambda>cls n. n \<le> length cls) clss' ns"
  "list_all2 glob_agree gs' tgs"
    using s_S_defs assms(2)
    unfolding store_typing.simps
    by auto
  moreover
  have "list_all2 (\<lambda> bs m. m \<le> mem_size bs) bss ms"
    using s_S_defs(1,3) assms(2)
    unfolding store_typing.simps mem_agree_def
    by simp
  hence "list_all2 mem_agree bss' ms"
    using assms(1) s_S_defs(1,2)
    unfolding store_extension.simps list_all2_conv_all_nth mem_agree_def
    by fastforce
  ultimately
  show ?thesis
    using store_typing.intros
    by fastforce
qed

lemma lfilled_deterministic:
  assumes "Lfilled k lfilled es les"
          "Lfilled k lfilled es les'"
  shows "les = les'"
  using assms
proof (induction arbitrary: les' rule: Lfilled.induct)
  case (L0 vs lholed es' es)
  thus ?case
    by (fastforce simp add: Lfilled.simps[of 0])
next
  case (LN vs lholed n es' l es'' k es lfilledk)
  thus ?case
    unfolding Lfilled.simps[of "(k + 1)"]
    by fastforce
qed
end