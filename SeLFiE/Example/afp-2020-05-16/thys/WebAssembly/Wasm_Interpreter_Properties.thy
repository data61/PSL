section \<open>Soundness of Interpreter\<close>

theory Wasm_Interpreter_Properties imports Wasm_Interpreter Wasm_Properties begin

lemma is_const_list_vs_to_es_list: "const_list ($$* vs)"
  using is_const_list
  by auto

lemma not_const_vs_to_es_list:
  assumes "~(is_const e)"
  shows "vs1 @ [e] @ vs2 \<noteq> $$* vs"
proof -
  fix vs
  {
    assume "vs1 @ [e] @ vs2 = $$* vs"
    hence "(\<forall>y\<in>set (vs1 @ [e] @ vs2). \<exists>x. y = $C x)"
      by simp
    hence False
      using assms
      unfolding is_const_def
      by fastforce
  }
  thus "vs1 @ [e] @ vs2 \<noteq> $$* vs"
    by fastforce
qed

lemma neq_label_nested:"[Label n les es] \<noteq> es"
proof -
  have "size_list size [Label n les es] > size_list size es"
    by simp
  thus ?thesis
    by fastforce
qed

lemma neq_local_nested:"[Local n i lvs es] \<noteq> es"
proof -
  have "size_list size [Local n i lvs es] > size_list size es"
    by simp
  thus ?thesis
    by fastforce
qed

lemma trap_not_value:"[Trap] \<noteq> $$*es"
  by fastforce

thm Lfilled.simps[of _ _ _ "[e]", simplified]

lemma lfilled_single:
  assumes "Lfilled k lholed es [e]"
          "\<And> a b c. e \<noteq> Label a b c"
  shows "(es = [e] \<and> lholed = LBase [] []) \<or> es = []"
  using assms
proof (cases rule: Lfilled.cases)
  case (L0 vs es')
  thus ?thesis
    by (metis Nil_is_append_conv append_self_conv2 butlast_append butlast_snoc)
next
  case (LN vs n es' l es'' k lfilledk)
  assume "(\<And>a b c. e \<noteq> Label a b c)"
  thus ?thesis
    using LN(2)
    unfolding Cons_eq_append_conv
    by fastforce
qed

lemma lfilled_eq:
  assumes "Lfilled j lholed es LI"
          "Lfilled j lholed es' LI"
  shows "es = es'"
  using assms
proof (induction arbitrary: es' rule: Lfilled.induct)
  case (L0 vs lholed es' es)
  thus ?case
    using Lfilled.simps[of 0, simplified]
    by auto
next
  case (LN vs lholed n les' l les'' k les lfilledk)
  thus ?case
    using Lfilled.simps[of "(k+1)" "LRec vs n les' l les''" es' "(vs @ [Label n les' lfilledk] @ les'')", simplified]
    by auto
qed

lemma lfilled_size:
  assumes "Lfilled j lholed es LI"
  shows "size_list size LI \<ge> size_list size es"
  using assms
  by (induction rule: Lfilled.induct) auto

thm Lfilled.simps[of _ _ es es, simplified]

lemma reduce_simple_not_eq:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  shows "es \<noteq> es'"
  using assms
proof (induction es' rule: reduce_simple.induct)
  case (label_const vs n es)
  thus ?case
    using neq_label_nested
    by auto
next
  case (br vs n i lholed LI es)
  have "size_list size [Label n es LI] > size_list size (vs @ es)"
    using lfilled_size[OF br(3)]
    by simp
  thus ?case
    by fastforce
next
  case (local_const es n i vs)
  thus ?case
    using neq_local_nested
    by auto
next
  case (return vs n j lholed es i vls)
  hence "size_list size [Local n i vls es] > size_list size vs"
        using lfilled_size[OF return(3)]
    by simp
  thus ?case
    by auto
qed auto
    
lemma reduce_not_eq:
  assumes "\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  shows "es \<noteq> es'"
  using assms
proof (induction es' rule: reduce.induct)
  case (basic e e' s vs i)
  thus ?case
    using reduce_simple_not_eq
    by simp
next
  case (callcl_host_Some cl t1s t2s f ves vcs n m s hs s' vcs' vs i)
  thus ?case
    by (cases vcs' rule:rev_cases) auto
next
  case (label s vs es i s' vs' es' k lholed les les')
  thus ?case
    using lfilled_eq
    by fastforce
qed auto

lemma reduce_simple_not_value:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  shows "es \<noteq> $$* vs"
  using assms
proof (induction rule: reduce_simple.induct)
  case (block vs n t1s t2s m es)
  have "\<not>(is_const ($Block (t1s _> t2s) es))"
    unfolding is_const_def
    by simp
  thus ?case
    using not_const_vs_to_es_list
    by (metis append.right_neutral)
next
  case (loop vs n t1s t2s m es)
  have "\<not>(is_const ($Loop (t1s _> t2s) es))"
    unfolding is_const_def
    by simp
  thus ?case
    using not_const_vs_to_es_list
    by (metis append.right_neutral)
next
  case (trap lholed es)
  show ?case
    using trap(2)
  proof (cases rule: Lfilled.cases)
    case L0
    have "\<not>(is_const Trap)"
      unfolding is_const_def
      by simp
    thus ?thesis
      using L0 not_const_vs_to_es_list
      by fastforce
  qed auto
qed auto

lemma reduce_not_value:
  assumes "\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  shows "es \<noteq> $$* ves"
  using assms
proof (induction es' arbitrary: ves rule: reduce.induct)
  case (basic e e' s vs i)
  thus ?case
    using reduce_simple_not_value
    by fastforce
next
  case (callcl_native cl i' j ts es s t1s t2s ves vcs n k m zs vs i)
  have "\<not>(is_const (Callcl cl))"
    unfolding is_const_def
    by simp
  thus ?case
    using not_const_vs_to_es_list
    by (metis append.right_neutral)
next
  case (callcl_host_Some cl t1s t2s f ves vcs n m s i s' vcs' vs)
  have "\<not>(is_const (Callcl cl))"
    unfolding is_const_def
    by simp
  thus ?case
    using not_const_vs_to_es_list
    by (metis append.right_neutral)
next
  case (callcl_host_None cl t1s t2s f ves vcs n m s vs i)
  have "\<not>(is_const (Callcl cl))"
    unfolding is_const_def
    by simp
  thus ?case
    using not_const_vs_to_es_list
    by (metis append.right_neutral)
next
  case (label s vs es i s' vs' es' k lholed les les')
  show ?case
    using label(2,4)
  proof (induction rule: Lfilled.induct)
    case (L0 lvs lholed les' les)
    {
      assume "lvs @ les @ les' = $$* ves"
      hence "(\<forall>y\<in>set (lvs @ les @ les'). \<exists>x. y = $C x)"
        by simp
      hence "(\<forall>y\<in>set les. \<exists>x. y = $C x)"
        by simp
      hence "\<exists>vs1. les = $$* vs1"
        unfolding ex_map_conv.
    }
    thus ?case
      using L0(3)
      by fastforce
  next
    case (LN lvs lholed ln les' l les'' k les lfilledk)
    have "\<not>(is_const (Label ln les' lfilledk))"
      unfolding is_const_def
      by simp
    thus ?case
      using not_const_vs_to_es_list
      by fastforce
  qed
qed auto

lemma reduce_simple_not_nil:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  shows "es \<noteq> []"
  using assms
proof (induction rule: reduce_simple.induct)
  case (trap es lholed)
  thus ?case
    using Lfilled.simps[of 0 lholed "[Trap]"]
    by auto
qed auto

lemma reduce_not_nil:
  assumes "\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  shows "es \<noteq> []"
  using assms
proof (induction rule: reduce.induct)
  case (basic e e' s vs i)
  thus ?case
    using reduce_simple_not_nil
    by simp
next
  case (label s vs es i s' vs' es' k lholed les les')
  show ?case
    using lfilled_size[OF label(2)] label(4)
    by (metis One_nat_def add_is_0 le_0_eq list.exhaust list.size(2) list.size_gen(1) zero_neq_one)
qed auto

lemma reduce_simple_not_trap:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  shows "es \<noteq> [Trap]"
  using assms
  by (induction rule: reduce_simple.induct) auto

lemma reduce_not_trap:
  assumes "\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  shows "es \<noteq> [Trap]"
  using assms
proof (induction rule: reduce.induct)
  case (basic e e' s vs i)
  thus ?case
    using reduce_simple_not_trap
    by simp
next
  case (label s vs es i s' vs' es' k lholed les les')
  {
    assume "les = [Trap]"
    hence "Lfilled k lholed es [Trap]"
      using label(2)
      by simp
    hence False
      using lfilled_single reduce_not_nil[OF label(1)] label(4)
      by fastforce
  }
  thus ?case
    by auto
qed auto

lemma reduce_simple_call: "\<not>\<lparr>[$Call j]\<rparr> \<leadsto> \<lparr>es'\<rparr>"
  using reduce_simple.simps[of "[$Call j]", simplified] lfilled_single
  by fastforce

lemma reduce_call:
  assumes "\<lparr>s;vs;[$Call j]\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
  shows "s = s'"
        "vs = vs'"
        "es' = [Callcl (sfunc s i j)]"
  using assms
proof (induction "[$Call j]:: e list" i s' vs' es' rule: reduce.induct)
  case (label s vs es i s' vs' es' k lholed les')
  have "es = [$Call j]"
       "lholed = LBase [] []"
    using reduce_not_nil[OF label(1)] lfilled_single[OF label(5)]
    by auto
  thus "s = s'"
       "vs = vs'"
       "les' = [Callcl (sfunc s i j)]"
    using label(2,3,4,6) Lfilled.simps[of k "LBase [] []" "[Callcl (sfunc s i j)]" les']
    by auto
qed (auto simp add: reduce_simple_call)

lemma run_one_step_basic_unreachable_result:
  assumes "run_one_step d i (s,vs,ves,$Unreachable) = (s', vs', res)"
  shows "\<exists>r. res = RSNormal r"
  using assms
  by auto

lemma run_one_step_basic_nop_result:
  assumes "run_one_step d i (s,vs,ves,$Nop) = (s', vs', res)"
  shows "\<exists>r. res = RSNormal r"
  using assms
  by auto

lemma run_one_step_basic_drop_result:
  assumes "run_one_step d i (s,vs,ves,$Drop) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases ves) auto

lemma run_one_step_basic_select_result:
  assumes "run_one_step d i (s,vs,ves,$Select) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
  proof (cases a; cases list)
    fix x1a aa listaa
    assume "a = ConstInt32 x1a" and "list = aa#listaa"
    thus ?thesis
      using assms Cons
      by (cases listaa; cases "int_eq x1a 0") auto
  qed auto
qed auto

lemma run_one_step_basic_block_result:
  assumes "run_one_step d i (s,vs,ves,$(Block x51 x52)) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof -
  obtain t1s t2s where "x51 = (t1s _> t2s)"
    using tf.exhaust
    by blast
  moreover obtain ves' ves'' where "split_n ves (length t1s) = (ves', ves'')"
    by (metis surj_pair)
  ultimately
    show ?thesis
    using assms 
    by (cases "length t1s \<le> length ves") auto
qed

lemma run_one_step_basic_loop_result:
  assumes "run_one_step d i (s,vs,ves,$(Loop x61 x62)) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof -
  obtain t1s t2s where "x61 = (t1s _> t2s)"
    using tf.exhaust
    by blast
  moreover obtain ves' ves'' where "split_n ves (length t1s) = (ves', ves'')"
    by (metis surj_pair)
  ultimately
    show ?thesis
    using assms 
    by (cases "length t1s \<le> length ves") auto
qed

lemma run_one_step_basic_if_result:
  assumes "run_one_step d i (s,vs,ves,$(If x71 x72 x73)) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
  proof (cases a)
    fix x1a
    assume "a = ConstInt32 x1a"
    thus ?thesis
      using assms Cons
      by (cases "int_eq x1a 0") auto
  qed auto
qed auto

lemma run_one_step_basic_br_result:
  assumes "run_one_step d i (s,vs,ves,$Br x8) = (s', vs', res)"
  shows "\<exists>r vrs. res = RSBreak r vrs"
  using assms
  by (cases ves) auto

lemma run_one_step_basic_br_if_result:
  assumes "run_one_step d i (s,vs,ves,$Br_if x9) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
  proof (cases a)
    case (ConstInt32 x1)
    thus ?thesis
      using assms Cons
      by (cases "int_eq x1 0") auto
  qed auto
qed auto

lemma run_one_step_basic_br_table_result:
  assumes "run_one_step d i (s,vs,ves,$Br_table js j) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
  proof (cases a)
    case (ConstInt32 x1)
    thus ?thesis
      using assms Cons
      by (cases "nat_of_int x1 < length js") auto
  qed auto
qed auto

lemma run_one_step_basic_return_result:
  assumes "run_one_step d i (s,vs,ves,$Return) = (s', vs', res)"
  shows "\<exists>vrs. res = RSReturn vrs"
  using assms
  by (cases ves) auto

lemma run_one_step_basic_call_result:
  assumes "run_one_step d i (s,vs,ves,$Call x12) = (s', vs', res)"
  shows "\<exists>r. res = RSNormal r"
  using assms
  by (cases ves) auto

lemma run_one_step_basic_call_indirect_result:
  assumes "run_one_step d i (s,vs,ves,$Call_indirect x13) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
  proof (cases a)
    case (ConstInt32 x1)
    thus ?thesis
      using Cons assms
    proof (cases "stab s i (nat_of_int x1)")
      case (Some cl)
      thus ?thesis
        using Cons assms ConstInt32
        by (cases cl; cases "stypes s i x13 = cl_type cl") auto
    qed auto
  qed auto
qed auto

lemma run_one_step_basic_get_local_result:
  assumes "run_one_step d i (s,vs,ves,$Get_local x14) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases "x14 < length vs") auto

lemma run_one_step_basic_set_local_result:
  assumes "run_one_step d i (s,vs,ves,$Set_local x15) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases ves; cases "x15 < length vs") auto

lemma run_one_step_basic_tee_local_result:
  assumes "run_one_step d i (s,vs,ves,$Tee_local x16) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases ves) auto

lemma run_one_step_basic_get_global_result:
  assumes "run_one_step d i (s,vs,ves,$Get_global x17) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by auto

lemma run_one_step_basic_set_global_result:
  assumes "run_one_step d i (s,vs,ves,$Set_global x18) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases ves) auto

lemma run_one_step_basic_load_result:
  assumes "run_one_step d i (s,vs,ves,$Load x191 x192 x193 x194) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
proof (cases x192)
  case None
  thus ?thesis
    using assms
  proof (cases ves)
    case (Cons a list)
    thus ?thesis
      using assms None
    proof (cases "smem_ind s i"; cases a)
      fix aa x1
      assume "smem_ind s i = Some aa" and "a = ConstInt32 x1" 
      thus ?thesis
        using assms None Cons
        by (cases "load (s.mem s ! aa) (nat_of_int x1) x194 (t_length x191)") auto
    qed auto
  qed auto
next
  case (Some a)
  thus ?thesis
    using assms
  proof (cases ves)
    case (Cons a' list)
    thus ?thesis
      using assms Some
    proof (cases "smem_ind s i"; cases a; cases a')
      fix aa x y x1
      assume "smem_ind s i = Some aa" and "a = (x, y)" and "a' = ConstInt32 x1"
      thus ?thesis
        using assms Some Cons
        by (cases "load_packed y (s.mem s ! aa) (nat_of_int x1) x194 (tp_length x) (t_length x191)") auto
    qed auto
  qed auto
qed

lemma run_one_step_basic_store_result:
  assumes "run_one_step d i (s,vs,ves,$Store x201 x202 x203 x204) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
proof (cases x202)
  case None
  thus ?thesis
    using assms
  proof (cases ves)
    case (Cons a list)
    note outer_Cons = Cons
    thus ?thesis
      using assms None
    proof (cases list)
      case (Cons a' list')
      thus ?thesis
        using assms None outer_Cons
      proof (cases a'; cases "types_agree x201 a"; cases "smem_ind s i")
        fix k aa
        assume "a' = ConstInt32 k" and "types_agree x201 a" and "smem_ind s i = Some aa"
        thus ?thesis
          using assms None outer_Cons Cons
          by (cases "store (s.mem s ! aa) (nat_of_int k) x204 (bits a) (t_length x201)") auto
      qed auto
    qed auto
  qed auto
next
  case (Some a'')
  thus ?thesis
    using assms
  proof (cases ves)
    case (Cons a list)
    note outer_Cons = Cons
    thus ?thesis
      using assms Some
    proof (cases list)
      case (Cons a' list')
      thus ?thesis
        using assms Some outer_Cons
      proof (cases a'; cases "types_agree x201 a"; cases "smem_ind s i")
        fix k aa
        assume "a' = ConstInt32 k" and "types_agree x201 a" and "smem_ind s i = Some aa"
        thus ?thesis
          using assms Some outer_Cons Cons
          by (cases "store_packed (s.mem s ! aa) (nat_of_int k) x204 (bits a) (tp_length a'')") auto
      qed auto
    qed auto
  qed auto
qed

lemma run_one_step_basic_current_memory_result:
  assumes "run_one_step d i (s,vs,ves,$Current_memory) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases "smem_ind s i") auto

lemma run_one_step_basic_grow_memory_result:
  assumes "run_one_step d i (s,vs,ves,$Grow_memory) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
  proof (cases a; cases "smem_ind s i")
    fix c a'
    assume "a = ConstInt32 c" and "smem_ind s i = Some a'"
    thus ?thesis
      using assms Cons
      by (cases "mem_grow_impl (s.mem s ! a') (nat_of_int c)") auto
  qed auto
qed auto

lemma run_one_step_basic_const_result:
  assumes "run_one_step d i (s,vs,ves,$EConst x23) = (s', vs', res)"
  shows "\<exists>e. res = RSCrash e"
  using assms
  by auto

lemma run_one_step_basic_unop_i_result:
  assumes "run_one_step d i (s,vs,ves,$Unop_i x241 x242) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
    by (cases x241; cases a) auto
qed (cases x241; auto)

lemma run_one_step_basic_unop_f_result:
  assumes "run_one_step d i (s,vs,ves,$Unop_f x251 x252) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
    by (cases x251; cases a) auto
qed (cases x251; auto)

lemma run_one_step_basic_binop_i_result:
  assumes "run_one_step d i (s,vs,ves,$Binop_i x261 x262) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  note outer_Cons = Cons
  thus ?thesis
    using assms
  proof (cases list)
    case (Cons a' list')
    thus ?thesis
      using assms outer_Cons
    proof (cases x261; cases a; cases a')
      fix x1 x2
      assume "x261 = T_i32" "a = ConstInt32 x1" and "a' = ConstInt32 x2"
      thus ?thesis
        using assms outer_Cons Cons
        by (cases "app_binop_i x262 x2 x1") auto
    next
      fix x1 x2
      assume "x261 = T_i64" "a = ConstInt64 x1" and "a' = ConstInt64 x2"
      thus ?thesis
        using assms outer_Cons Cons
        by (cases "app_binop_i x262 x2 x1") auto
    qed auto
  qed (cases x261; cases a; auto)
qed (cases x261; auto)

lemma run_one_step_basic_binop_f_result:
  assumes "run_one_step d i (s,vs,ves,$Binop_f x271 x272) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  note outer_Cons = Cons
  thus ?thesis
    using assms
  proof (cases list)
    case (Cons a' list')
    thus ?thesis
      using assms outer_Cons
    proof (cases x271; cases a; cases a')
      fix x1 x2
      assume "x271 = T_f32" "a = ConstFloat32 x1" and "a' = ConstFloat32 x2"
      thus ?thesis
        using assms outer_Cons Cons
        by (cases "app_binop_f x272 x2 x1") auto
    next
      fix x1 x2
      assume "x271 = T_f64" "a = ConstFloat64 x1" and "a' = ConstFloat64 x2"
      thus ?thesis
        using assms outer_Cons Cons
        by (cases "app_binop_f x272 x2 x1") auto
    qed auto
  qed (cases x271; cases a; auto)
qed (cases x271; auto)

lemma run_one_step_basic_testop_result:
  assumes "run_one_step d i (s,vs,ves,$Testop x281 x282) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  thus ?thesis
    using assms
    by (cases x281; cases a) auto
qed (cases x281; auto)

lemma run_one_step_basic_relop_i_result:
  assumes "run_one_step d i (s,vs,ves,$Relop_i x291 x292) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  note outer_Cons = Cons
  thus ?thesis
    using assms
  proof (cases list)
    case (Cons a' list')
    thus ?thesis
      using assms outer_Cons
    proof (cases x291; cases a; cases a')
      fix x1 x2
      assume "x291 = T_i32" "a = ConstInt32 x1" and "a' = ConstInt32 x2"
      thus ?thesis
        using assms outer_Cons Cons
        by (cases "app_relop_i x292 x2 x1") auto
    next
      fix x1 x2
      assume "x291 = T_i64" "a = ConstInt64 x1" and "a' = ConstInt64 x2"
      thus ?thesis
        using assms outer_Cons Cons
        by (cases "app_relop_i x292 x2 x1") auto
    qed auto
  qed (cases x291; cases a; auto)
qed (cases x291; auto)

lemma run_one_step_basic_relop_f_result:
  assumes "run_one_step d i (s,vs,ves,$Relop_f x301 x302) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves)
  case (Cons a list)
  note outer_Cons = Cons
  thus ?thesis
    using assms
  proof (cases list)
    case (Cons a' list')
    thus ?thesis
      using assms outer_Cons
    proof (cases x301; cases a; cases a')
      fix x1 x2
      assume "x301 = T_f32" "a = ConstFloat32 x1" and "a' = ConstFloat32 x2"
      thus ?thesis
        using assms outer_Cons Cons
        by (cases "app_relop_f x302 x2 x1") auto
    next
      fix x1 x2
      assume "x301 = T_f64" "a = ConstFloat64 x1" and "a' = ConstFloat64 x2"
      thus ?thesis
        using assms outer_Cons Cons
        by (cases "app_relop_f x302 x2 x1") auto
    qed auto
  qed (cases x301; cases a; auto)
qed (cases x301; auto)

lemma run_one_step_basic_cvtop_result:
  assumes "run_one_step d i (s,vs,ves,$Cvtop t2 x312 t1 sx) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases ves; cases x312)
  fix a ves'
  assume "ves = a#ves'" and "x312 = Convert" 
  thus ?thesis
    using assms
    by (cases "cvt t2 sx a"; cases "types_agree t1 a") auto
next
  fix a ves'
  assume "ves = a#ves'" and "x312 = Reinterpret" 
  thus ?thesis
    using assms
    by (cases sx; cases "types_agree t1 a") auto
qed auto

lemma run_one_step_trap_result:
  assumes "run_one_step d i (s,vs,ves,Trap) = (s', vs', res)"
  shows "\<exists>e. res = RSCrash e"
  using assms
  by auto

lemma run_one_step_callcl_result:
  assumes "run_one_step d i (s,vs,ves,Callcl cl) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
proof -
  obtain t1s t2s where cl_type_is:"cl_type cl = (t1s _> t2s)"
    using tf.exhaust
    by blast
  obtain ves' ves'' where split_n_is:"split_n ves (length t1s) = (ves', ves'')"
    by fastforce
  show ?thesis
  proof (cases cl)
    case (Func_native x11 x12 x13 x14)
    thus ?thesis
      using assms cl_type_is split_n_is
      unfolding cl_type_def
      by (cases "length t1s \<le> length ves") auto
  next
    case (Func_host x21 x22)
    show ?thesis
    proof (cases "host_apply_impl s (t1s _> t2s) x22 (rev ves')")
      case None
      thus ?thesis
        using assms cl_type_is split_n_is Func_host
        unfolding cl_type_def
        by (cases "length t1s \<le> length ves")  auto
    next
      case (Some a)
      thus ?thesis
      proof (cases a)
        case (Pair s' vcs')
        thus ?thesis
          using assms cl_type_is split_n_is Func_host Some
          unfolding cl_type_def
          by (cases "length t1s \<le> length ves"; cases "list_all2 types_agree t2s vcs'")  auto
      qed
    qed
  qed
qed

lemma run_one_step_label_result:
  assumes "run_one_step d i (s,vs,ves,Label x41 x42 x43) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>r rvs. res = RSBreak r rvs) \<or> (\<exists>rvs. res = RSReturn rvs) \<or> (\<exists>e. res = RSCrash e)"
  using assms
  by (cases res) auto

lemma run_one_step_local_result:
  assumes "run_one_step d i (s,vs,ves,Local x51 x52 x53 x54) = (s', vs', res)"
  shows "(\<exists>r. res = RSNormal r) \<or> (\<exists>e. res = RSCrash e)"
  using assms
proof (cases "x54 = [Trap]")
  case False
  note outer_False = False
  thus ?thesis
  proof (cases "const_list x54")
    case True
    thus ?thesis
      using assms outer_False
      by (cases "length x54 = x51") auto
  next
    case False
    thus ?thesis
      using assms outer_False
    proof (cases d)
      case (Suc d')
      obtain s' vs' res where rs_def:"run_step d' x52 (s, x53, x54) = (s', vs', res)"
      by (metis surj_pair)
      thus ?thesis
        using assms outer_False False Suc
      proof (cases res)
        case (RSReturn x3)
        thus ?thesis
          using assms outer_False False rs_def Suc
          by (cases "x51 \<le> length x3") auto
      qed auto
    qed auto
  qed
qed auto

lemma run_one_step_break:
  assumes "run_one_step d i (s,vs,ves,e) = (s', vs', RSBreak n res)"
  shows "(e = $Br n) \<or> (\<exists>n les es. e = Label n les es)"
proof (cases e)
  case (Basic x1)
  thus ?thesis
  proof (cases x1)
    case Unreachable
    thus ?thesis
      using run_one_step_basic_unreachable_result assms Basic
      by fastforce
  next
    case Nop
    thus ?thesis
      using assms Basic
      by fastforce
  next
    case Drop
    thus ?thesis
      using run_one_step_basic_drop_result assms Basic
      by fastforce
  next
    case Select
    thus ?thesis
      using run_one_step_basic_select_result assms Basic
      by fastforce
  next
    case (Block x51 x52)
    thus ?thesis
      using run_one_step_basic_block_result assms Basic
      by fastforce
  next
    case (Loop x61 x62)
    thus ?thesis
      using run_one_step_basic_loop_result assms Basic
      by fastforce
  next
    case (If x71 x72 x73)
    thus ?thesis
      using run_one_step_basic_if_result assms Basic
      by fastforce
  next
    case (Br x8)
    thus ?thesis
      using run_one_step_basic_br_result assms Basic
      by fastforce
  next
    case (Br_if x9)
    thus ?thesis
      using run_one_step_basic_br_if_result assms Basic
      by fastforce
  next
    case (Br_table x10)
    thus ?thesis
      using run_one_step_basic_br_table_result assms Basic
      by fastforce
  next
    case Return
    thus ?thesis
      using run_one_step_basic_return_result assms Basic
      by fastforce
  next
    case (Call x12)
    thus ?thesis
      using run_one_step_basic_call_result assms Basic
      by fastforce
  next
    case (Call_indirect x13)
    thus ?thesis
      using run_one_step_basic_call_indirect_result assms Basic
      by fastforce
  next
    case (Get_local x14)
    thus ?thesis
      using run_one_step_basic_get_local_result assms Basic
      by fastforce
  next
    case (Set_local x15)
    thus ?thesis
      using run_one_step_basic_set_local_result assms Basic
      by fastforce
  next
    case (Tee_local x16)
    thus ?thesis
      using run_one_step_basic_tee_local_result assms Basic
      by fastforce
  next
    case (Get_global x17)
    thus ?thesis
      using assms Basic
      by fastforce
  next
    case (Set_global x18)
    thus ?thesis
      using run_one_step_basic_set_global_result assms Basic
      by fastforce
  next
    case (Load x191 x192 x193 x194)
    thus ?thesis
      using run_one_step_basic_load_result assms Basic
      by fastforce
  next
    case (Store x201 x202 x203 x204)
    thus ?thesis
      using run_one_step_basic_store_result assms Basic
      by fastforce
  next
    case Current_memory
    thus ?thesis
      using run_one_step_basic_current_memory_result assms Basic
      by fastforce
  next
    case Grow_memory
    thus ?thesis
      using run_one_step_basic_grow_memory_result assms Basic
      by fastforce
  next
    case (EConst x23)
    thus ?thesis
      using assms Basic
      by fastforce
  next
    case (Unop_i x241 x242)
    thus ?thesis
      using run_one_step_basic_unop_i_result assms Basic
      by fastforce
  next
    case (Unop_f x251 x252)
    thus ?thesis
      using run_one_step_basic_unop_f_result assms Basic
      by fastforce
  next
    case (Binop_i x261 x262)
    thus ?thesis
      using run_one_step_basic_binop_i_result assms Basic
      by fastforce
  next
    case (Binop_f x271 x272)
    thus ?thesis
      using run_one_step_basic_binop_f_result assms Basic
      by fastforce
  next
    case (Testop x281 x282)
    thus ?thesis
      using run_one_step_basic_testop_result assms Basic
      by fastforce
  next
    case (Relop_i x291 x292)
    thus ?thesis
      using run_one_step_basic_relop_i_result assms Basic
      by fastforce
  next
    case (Relop_f x301 x302)
    thus ?thesis
      using run_one_step_basic_relop_f_result assms Basic
      by fastforce
  next
    case (Cvtop x311 x312 x313 x314)
    thus ?thesis
      using run_one_step_basic_cvtop_result assms Basic
      by fastforce
  qed
next
  case Trap
  thus ?thesis
    using assms
    by auto
next
  case (Callcl x3)
  thus ?thesis
    using assms run_one_step_callcl_result
    by fastforce
next
  case (Label x41 x42 x43)
  thus ?thesis
    by auto
next
  case (Local x51 x52 x53 x54)
  thus ?thesis
    using assms run_one_step_local_result
    by fastforce
qed

lemma run_one_step_return:
  assumes "run_one_step d i (s,vs,ves,e) = (s', vs', RSReturn res)"
  shows "(e = $Return) \<or> (\<exists>n les es. e = Label n les es)"
proof (cases e)
  case (Basic x1)
  thus ?thesis
  proof (cases x1)
    case Unreachable
    thus ?thesis
      using run_one_step_basic_unreachable_result assms Basic
      by fastforce
  next
    case Nop
    thus ?thesis
      using assms Basic
      by fastforce
  next
    case Drop
    thus ?thesis
      using run_one_step_basic_drop_result assms Basic
      by fastforce
  next
    case Select
    thus ?thesis
      using run_one_step_basic_select_result assms Basic
      by fastforce
  next
    case (Block x51 x52)
    thus ?thesis
      using run_one_step_basic_block_result assms Basic
      by fastforce
  next
    case (Loop x61 x62)
    thus ?thesis
      using run_one_step_basic_loop_result assms Basic
      by fastforce
  next
    case (If x71 x72 x73)
    thus ?thesis
      using run_one_step_basic_if_result assms Basic
      by fastforce
  next
    case (Br x8)
    thus ?thesis
      using run_one_step_basic_br_result assms Basic
      by fastforce
  next
    case (Br_if x9)
    thus ?thesis
      using run_one_step_basic_br_if_result assms Basic
      by fastforce
  next
    case (Br_table x10)
    thus ?thesis
      using run_one_step_basic_br_table_result assms Basic
      by fastforce
  next
    case Return
    thus ?thesis
      using run_one_step_basic_return_result assms Basic
      by fastforce
  next
    case (Call x12)
    thus ?thesis
      using run_one_step_basic_call_result assms Basic
      by fastforce
  next
    case (Call_indirect x13)
    thus ?thesis
      using run_one_step_basic_call_indirect_result assms Basic
      by fastforce
  next
    case (Get_local x14)
    thus ?thesis
      using run_one_step_basic_get_local_result assms Basic
      by fastforce
  next
    case (Set_local x15)
    thus ?thesis
      using run_one_step_basic_set_local_result assms Basic
      by fastforce
  next
    case (Tee_local x16)
    thus ?thesis
      using run_one_step_basic_tee_local_result assms Basic
      by fastforce
  next
    case (Get_global x17)
    thus ?thesis
      using assms Basic
      by fastforce
  next
    case (Set_global x18)
    thus ?thesis
      using run_one_step_basic_set_global_result assms Basic
      by fastforce
  next
    case (Load x191 x192 x193 x194)
    thus ?thesis
      using run_one_step_basic_load_result assms Basic
      by fastforce
  next
    case (Store x201 x202 x203 x204)
    thus ?thesis
      using run_one_step_basic_store_result assms Basic
      by fastforce
  next
    case Current_memory
    thus ?thesis
      using run_one_step_basic_current_memory_result assms Basic
      by fastforce
  next
    case Grow_memory
    thus ?thesis
      using run_one_step_basic_grow_memory_result assms Basic
      by fastforce
  next
    case (EConst x23)
    thus ?thesis
      using assms Basic
      by fastforce
  next
    case (Unop_i x241 x242)
    thus ?thesis
      using run_one_step_basic_unop_i_result assms Basic
      by fastforce
  next
    case (Unop_f x251 x252)
    thus ?thesis
      using run_one_step_basic_unop_f_result assms Basic
      by fastforce
  next
    case (Binop_i x261 x262)
    thus ?thesis
      using run_one_step_basic_binop_i_result assms Basic
      by fastforce
  next
    case (Binop_f x271 x272)
    thus ?thesis
      using run_one_step_basic_binop_f_result assms Basic
      by fastforce
  next
    case (Testop x281 x282)
    thus ?thesis
      using run_one_step_basic_testop_result assms Basic
      by fastforce
  next
    case (Relop_i x291 x292)
    thus ?thesis
      using run_one_step_basic_relop_i_result assms Basic
      by fastforce
  next
    case (Relop_f x301 x302)
    thus ?thesis
      using run_one_step_basic_relop_f_result assms Basic
      by fastforce
  next
    case (Cvtop x311 x312 x313 x314)
    thus ?thesis
      using run_one_step_basic_cvtop_result assms Basic
      by fastforce
  qed
next
  case Trap
  thus ?thesis
    using assms
    by auto
next
  case (Callcl x3)
  thus ?thesis
    using assms run_one_step_callcl_result
    by fastforce
next
  case (Label x41 x42 x43)
  thus ?thesis
    by auto
next
  case (Local x51 x52 x53 x54)
  thus ?thesis
    using assms run_one_step_local_result
    by fastforce
qed

lemma run_step_break_imp_not_trap_const_list:
  assumes "run_step d i (s, vs, es) = (s', vs', RSBreak n res)"
  shows "es \<noteq> [Trap]" "\<not>const_list es"
proof -
  {
    assume "es = [Trap]"
    hence False
      using assms
      by simp
  }
  thus "es \<noteq> [Trap]"
    by blast
  {
    assume "const_list es"
    then obtain vs where "split_vals_e es = (vs, [])"
      using split_vals_e_const_list e_type_const_conv_vs
      by fastforce
    hence False
      using assms
      by simp
  }
  thus "\<not>const_list es"
    by blast
qed

lemma run_step_return_imp_not_trap_const_list:
  assumes "run_step d i (s, vs, es) = (s', vs', RSReturn res)"
  shows "es \<noteq> [Trap]" "\<not>const_list es"
proof -
  {
    assume "es = [Trap]"
    hence False
      using assms
      by simp
  }
  thus "es \<noteq> [Trap]"
    by blast
  {
    assume "const_list es"
    then obtain vs where "split_vals_e es = (vs, [])"
      using split_vals_e_const_list e_type_const_conv_vs
      by fastforce
    hence False
      using assms
      by simp
  }
  thus "\<not>const_list es"
    by blast
qed

lemma run_one_step_label_break_imp_break:
  assumes "run_one_step d i (s, vs, ves, Label ln les es) = (s', vs', RSBreak n res)"
  shows "run_step d i (s, vs, es) = (s', vs', RSBreak (Suc n) res)"
  using assms
proof (cases "es = [Trap]"; cases "const_list es")
  assume local_assms:"es \<noteq> [Trap]" "\<not>const_list es"
  obtain s'' vs'' res'' where rs_def:"run_step d i (s, vs, es) = (s'', vs'', res'')"
    by (metis surj_pair)
  thus ?thesis
    using assms local_assms
  proof (cases res'')
    case (RSBreak x21 x22)
    thus ?thesis
      using assms local_assms rs_def
      by (cases x21; cases "ln \<le> length x22") auto
  qed auto
qed auto

lemma run_one_step_label_return_imp_return:
  assumes "run_one_step d i (s, vs, ves, Label n les es) = (s', vs', RSReturn res)"
  shows "run_step d i (s, vs, es) = (s', vs', RSReturn res)"
  using assms
proof (cases "es = [Trap]"; cases "const_list es")
  assume local_assms:"es \<noteq> [Trap]" "\<not>const_list es"
  obtain s'' vs'' res'' where rs_def:"run_step d i (s, vs, es) = (s'', vs'', res'')"
    by (metis surj_pair)
  thus ?thesis
    using assms local_assms
  proof (cases res'')
    case (RSBreak x21 x22)
    thus ?thesis
      using assms local_assms rs_def
      by (cases x21; cases "n \<le> length x22") auto
  qed auto
qed auto
thm run_step_run_one_step.induct

(* These definitions are needed because the automatic induction process hangs if they are unrolled *)
definition run_step_break_imp_lfilled_prop where
  "run_step_break_imp_lfilled_prop s' vs' n res =
     (\<lambda>d i (s,vs,es). (run_step d i (s,vs,es) = (s', vs', RSBreak n res)) \<longrightarrow>
       s = s' \<and> vs = vs' \<and>
       (\<exists>n' lfilled es_c. n' \<ge> n \<and> Lfilled_exact (n'-n) lfilled ((vs_to_es res) @ [$Br n'] @ es_c) es))"

definition run_one_step_break_imp_lfilled_prop where
  "run_one_step_break_imp_lfilled_prop s' vs' n res =
     (\<lambda>d i (s,vs,ves,e). run_one_step d i (s,vs,ves,e) = (s', vs', RSBreak n res) \<longrightarrow>
       s = s' \<and> vs = vs' \<and> ((res = ves \<and> e = $Br n) \<or> (\<exists>n' lfilled es_c es les' ln. n' > n \<and> Lfilled_exact (n'-(n+1)) lfilled ((vs_to_es res) @ [$Br n'] @ es_c) es \<and> e = Label ln les' es)))"

lemma run_step_break_imp_lfilled:
  assumes "run_step d i (s,vs,es) = (s', vs', RSBreak n res)"
  shows "s = s' \<and>
         vs = vs' \<and>
         (\<exists>n' lfilled es_c. n' \<ge> n \<and>
                            Lfilled_exact (n'-n) lfilled ((vs_to_es res) @ [$Br n'] @ es_c) es)"
proof -
  fix ves e
  have "(run_step_break_imp_lfilled_prop s' vs' n res) d i (s,vs,es)"
  and  "(run_one_step_break_imp_lfilled_prop s' vs' n res) d i (s,vs,ves,e)"
  proof (induction d i "(s,vs,es)" and d i "(s,vs,ves,e)"  arbitrary: n es and n ves e rule: run_step_run_one_step.induct)
    case (1 d i es)
    {
      assume local_assms:"run_step d i (s,vs,es) = (s', vs', RSBreak n res)"
      obtain ves es' where split_vals_es:"split_vals_e es = (ves, es')"
        by (metis surj_pair)
      then obtain a as where es'_def:"es' = a#as"
        using local_assms
        by (cases es') auto
      hence a_def:"a \<noteq> Trap"
        using local_assms split_vals_es
        by (cases "a = Trap"; cases "(as \<noteq> [] \<or> ves \<noteq> [])") simp_all
      obtain s'' vs'' res'' where "run_one_step d i (s,vs,(rev ves),a) = (s'', vs'', res'')"
        by (metis surj_pair)
      hence ros_def:"run_one_step d i (s,vs,(rev ves),a) = (s', vs', RSBreak n res)"
        using local_assms split_vals_es es'_def a_def
        by (cases "res''") (auto simp del: run_one_step.simps)
      hence "run_one_step_break_imp_lfilled_prop  s' vs' n res d i (s, vs, rev ves, a)"
        using 1 split_vals_es a_def es'_def
        by fastforce
      then obtain n' lfilled es_c les les' ln where
        "s = s'" "vs = vs'"
        "((res = (rev ves) \<and> a = $Br n) \<or>
           n' > n \<and> (Lfilled_exact (n'-(n+1)) lfilled ((vs_to_es res) @ [$Br n'] @ es_c) les \<and> a = Label ln les' les))"
        using ros_def
        unfolding run_one_step_break_imp_lfilled_prop_def
        by fastforce
      then consider
        (1) "s = s'" "vs = vs'" "res = (rev ves)" "a = $Br n"
      | (2) "s = s'" "vs = vs'" "n' > n" "Lfilled_exact (n'-(n+1)) lfilled ((vs_to_es res) @ [$Br n'] @ es_c) les" "a = Label ln les' les"
        by blast
      hence "s = s' \<and> vs = vs' \<and>
             (\<exists>n' lfilled es_c.  n' \<ge> n \<and> Lfilled_exact (n'-n) lfilled ((vs_to_es res) @ [$Br n'] @ es_c) es)"
      proof cases
        case 1
      thus ?thesis
        using es'_def split_vals_e_conv_app[OF split_vals_es] Lfilled_exact.intros(1) is_const_list[of _ ves]
        by fastforce
      next
        case 2
      have test:"const_list ($$* ves)"
        using is_const_list
        by auto
      have "(Suc (n' - Suc n)) = n' - n"
        using 2(3)
        by simp
      thus ?thesis
        using 2(1,2,3,5) Lfilled_exact.intros(2)[OF test _ 2(4), of _ ln les' as] es'_def split_vals_e_conv_app[OF split_vals_es]
        by (metis Suc_eq_plus1 append_Cons append_Nil less_imp_le_nat)
      qed
  }
  thus ?case
    unfolding run_step_break_imp_lfilled_prop_def
    by fastforce
  next
    case (2 d i ves e)
    {
    assume local_assms:"run_one_step d i (s,vs,ves,e) = (s', vs', RSBreak n res)"
    consider (a) "e = $Br n" | (b) "(\<exists>n les es. e = Label n les es)"
      using run_one_step_break[OF local_assms]
      by blast
    hence "s = s' \<and> vs = vs' \<and> ((res = ves \<and> e = $Br n) \<or> (\<exists>n' lfilled es_c es les' ln. n' > n \<and> Lfilled_exact (n'-(n+1)) lfilled ((vs_to_es res) @ [$Br n'] @ es_c) es \<and> e = Label ln les' es))"
    proof cases
      case a
      thus ?thesis
        using local_assms
        by simp
    next
      case b
      then obtain ln les es where e_def:"e = Label ln les es"
        by blast
      hence "run_one_step d i (s, vs, ves,  Label ln les es) = (s', vs', RSBreak n res)"
        using local_assms by simp
      hence rs_def:"run_step d i (s, vs, es) = (s', vs', RSBreak (Suc n) res)"
        using run_one_step_label_break_imp_break
        by fastforce
      hence "run_step_break_imp_lfilled_prop s' vs' (Suc n) res d i (s, vs, es)"
        using 2(1)[OF e_def _ run_step_break_imp_not_trap_const_list(2)]
        by fastforce
      thus ?thesis
        using e_def rs_def
        unfolding run_step_break_imp_lfilled_prop_def
        by fastforce
    qed
  }
  thus ?case
    unfolding run_one_step_break_imp_lfilled_prop_def
    by fastforce
  qed
  thus ?thesis
    using assms
    unfolding run_step_break_imp_lfilled_prop_def
    by fastforce
qed

lemma run_step_return_imp_lfilled:
  assumes "run_step d i (s,vs,es) = (s', vs', RSReturn res)"
  shows "s = s' \<and> vs = vs' \<and> (\<exists>n lfilled es_c. Lfilled_exact n lfilled ((vs_to_es res) @ [$Return] @ es_c) es)"
proof -
  fix ves e
  have "(run_step d i (s,vs,es) = (s', vs', RSReturn res)) \<Longrightarrow>
           s = s' \<and> vs = vs' \<and> (\<exists>n lfilled es_c. Lfilled_exact n lfilled ((vs_to_es res) @ [$Return] @ es_c) es)"
  and  "(run_one_step d i (s,vs,ves,e) = (s', vs', RSReturn res)) \<Longrightarrow>
          s = s' \<and> vs = vs' \<and>
          ((res = ves \<and> e = $Return) \<or>
           (\<exists>n lfilled ves es_c es n' les'. Lfilled_exact n lfilled ((vs_to_es res) @ [$Return] @ es_c) es \<and>
              e = Label n' les' es))"
  proof (induction d i "(s,vs,es)" and d i "(s,vs,ves,e)" arbitrary: s vs es s' vs' res and s vs ves e s' vs' res rule: run_step_run_one_step.induct)
    case (1 d i s vs es)
    obtain ves es' where split_vals_es:"split_vals_e es = (ves, es')"
      by (metis surj_pair)
    then obtain a as where es'_def:"es' = a#as"
      using 1(2)
      by (cases es') auto
    hence a_def:"\<not> e_is_trap a"
      using 1(2) split_vals_es
      by (cases "a = Trap"; cases "(as \<noteq> [] \<or> ves \<noteq> [])") simp_all
    obtain s'' vs'' res'' where "run_one_step d i (s,vs,(rev ves),a) = (s'', vs'', res'')"
      by (metis surj_pair)
    hence ros_def:"run_one_step d i (s,vs,(rev ves),a) = (s', vs', RSReturn res)"
      using 1(2) split_vals_es es'_def a_def
      by (cases "res''") (auto simp del: run_one_step.simps)
    obtain n lfilled les_c les n' les' where
      "s = s'" "vs = vs'"
      "(res = rev ves \<and> a = $Return) \<or> (Lfilled_exact n lfilled ((vs_to_es res) @ [$Return] @ les_c) les \<and> a = Label n' les' les)"
      using 1(1)[OF split_vals_es[symmetric] _ es'_def a_def ros_def]
      by fastforce
    then consider
      (1) "s = s'" "vs = vs'" "res = rev ves" "a = $Return"
    | (2) "s = s'" "vs = vs'" "(Lfilled_exact n lfilled ((vs_to_es res) @ [$Return] @ les_c) les)" "(a = Label n' les' les)"
      by blast
    thus ?case
    proof cases
      case 1
      thus ?thesis
        using es'_def split_vals_e_conv_app[OF split_vals_es] Lfilled_exact.intros(1) is_const_list[of _ ves]
        by fastforce
    next
      case 2
      have "const_list ($$* ves)"
        using is_const_list
        by fastforce
      thus ?thesis
        using 2 Lfilled_exact.intros(2) es'_def split_vals_e_conv_app[OF split_vals_es]
          by fastforce
    qed
  next
    case (2 d i s vs ves e s' vs')
    consider (a) "e = $Return" | (b) "(\<exists>n les es. e = Label n les es)"
      using run_one_step_return[OF 2(3)]
      by blast
    thus ?case
    proof cases
      case a
      thus ?thesis
        using 2(3)
        by simp
    next
      case b
      then obtain n les es where e_def:"e = Label n les es"
        by blast
      hence "run_one_step d i (s, vs, ves,  Label n les es) = (s', vs', RSReturn res)"
        using 2(3) by simp
      hence "run_step d i (s, vs, es) = (s', vs', RSReturn res)"
        using run_one_step_label_return_imp_return
        by fastforce
      thus ?thesis
        using 2(3) 2(1)[OF e_def _ run_step_return_imp_not_trap_const_list(2)] e_def
        by fastforce
    qed
  qed
  thus ?thesis
    using assms
    by blast
qed

lemma run_step_basic_unop_testop_sound:
  assumes "(run_one_step d i (s,vs,ves,$b_e) = (s', vs', RSNormal es'))"
          "b_e = Unop_i t iop \<or> b_e = Unop_f t fop \<or> b_e = Testop t testop"
  shows "\<lparr>s;vs;(vs_to_es ves)@[$b_e]\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
proof -
  consider (1) "b_e = Unop_i t iop" | (2) "b_e = Unop_f t fop" | (3) "b_e = Testop t testop"
    using assms(2)
    by blast
  note b_e_cases = this
  show ?thesis
    using assms(1)
  proof (cases ves)
    case (Cons a list)
    thus ?thesis
      using assms(1)
    proof (cases a; cases t)
      case (ConstInt32 x1)
      case T_i32
      thus ?thesis
        using assms(1) Cons ConstInt32
           is_const_list_vs_to_es_list[of "rev list"]
            progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(1)]]
            progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(13)]]
        by (cases rule: b_e_cases) auto
    next
      case (ConstInt64 x2)
      case T_i64
      thus ?thesis
        using assms(1) Cons ConstInt64
           is_const_list_vs_to_es_list[of "rev list"]
            progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(2)]]
            progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(14)]]
        by (cases rule: b_e_cases) auto
    next
      case (ConstFloat32 x3)
      case T_f32
      thus ?thesis
        using assms(1) Cons ConstFloat32
           is_const_list_vs_to_es_list[of "rev list"]
            progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(3)]]
        by (cases rule: b_e_cases) auto
    next
      case (ConstFloat64 x4)
      case T_f64
      thus ?thesis
        using assms(1) Cons ConstFloat64
           is_const_list_vs_to_es_list[of "rev list"]
            progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(4)]]
        by (cases rule: b_e_cases) auto
    qed (cases rule: b_e_cases; auto)+
  qed (cases rule: b_e_cases; cases t; auto)
qed

lemma run_step_basic_binop_relop_sound:
  assumes "(run_one_step d i (s,vs,ves,$b_e) = (s', vs', RSNormal es'))"
          "b_e = Binop_i t iop \<or> b_e = Binop_f t fop \<or> b_e = Relop_i t irop \<or> b_e = Relop_f t frop"
  shows "\<lparr>s;vs;(vs_to_es ves)@[$b_e]\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
proof -
  consider
    (1) "b_e = Binop_i t iop"
  | (2) "b_e = Binop_f t fop"
  | (3) "b_e = Relop_i t irop"
  | (4) "b_e = Relop_f t frop"
    using assms(2)
    by blast
  note b_e_cases = this
  show ?thesis
    using assms(1)
  proof (cases ves)
    case outer_Cons:(Cons v1 list)
    thus ?thesis
      using assms(1)
    proof (cases list)
      case (Cons v2 list')
      thus ?thesis
        using assms(1) outer_Cons
      proof (cases v1; cases v2; cases t)
        fix c1 c2
        assume "v1 = ConstInt32 c1" and "v2 = ConstInt32 c2" and "t = T_i32"
        thus ?thesis
          using assms(1) Cons outer_Cons
             is_const_list_vs_to_es_list[of "rev list'"]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(5)]]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(6)]]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(15)]]
          by (cases rule: b_e_cases; cases "app_binop_i iop c2 c1") auto
      next
        fix c1 c2
        assume "v1 = ConstInt64 c1" and "v2 = ConstInt64 c2" and "t = T_i64"
        thus ?thesis
          using assms(1) Cons outer_Cons
             is_const_list_vs_to_es_list[of "rev list'"]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(7)]]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(8)]]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(16)]]
          by (cases rule: b_e_cases; cases "app_binop_i iop c2 c1") auto
      next
        fix c1 c2
        assume "v1 = ConstFloat32 c1" and "v2 = ConstFloat32 c2" and "t = T_f32"
        thus ?thesis
          using assms(1) Cons outer_Cons
             is_const_list_vs_to_es_list[of "rev list'"]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(9)]]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(10)]]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(17)]]
          by (cases rule: b_e_cases; cases "app_binop_f fop c2 c1") auto
      next
        fix c1 c2
        assume "v1 = ConstFloat64 c1" and "v2 = ConstFloat64 c2" and "t = T_f64"
        thus ?thesis
          using assms(1) Cons outer_Cons
             is_const_list_vs_to_es_list[of "rev list'"]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(11)]]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(12)]]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(18)]]
          by (cases rule: b_e_cases; cases "app_binop_f fop c2 c1") auto
      qed (cases rule: b_e_cases; auto)+
    qed (cases rule: b_e_cases; cases t; cases v1; auto)
  qed (cases rule: b_e_cases; cases t; auto)
qed

lemma run_step_basic_sound:
  assumes "(run_one_step d i (s,vs,ves,$b_e) = (s', vs', RSNormal es'))"
  shows "\<lparr>s;vs;(vs_to_es ves)@[$b_e]\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
proof -
  show ?thesis
  proof (cases b_e)
    case Unreachable
    thus ?thesis
      using is_const_list_vs_to_es_list[of "rev ves"]
            progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(22)]]
            assms
      by fastforce
  next
    case Nop
    thus ?thesis
      using is_const_list_vs_to_es_list[of "rev ves"]
            progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(23)]]
            assms
      by fastforce
  next
    case Drop
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      hence "vs_to_es ves = vs_to_es list @ [$C a]"
        by fastforce
      thus ?thesis
        using is_const_list_vs_to_es_list[of "rev list"]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(24)]]
              Drop assms Cons
        by auto
    qed auto
  next
    case Select
    thus ?thesis
      using assms
    proof (cases ves)
      case outer_outer_cons:(Cons a list)
      thus ?thesis
        using Select assms
      proof (cases a; cases list)
        case (ConstInt32 x1a)
        case outer_cons:(Cons a' list')
        thus ?thesis
          using assms outer_outer_cons ConstInt32 Select
        proof (cases list')
          case (Cons a'' list'')
          hence "vs_to_es ves = vs_to_es list'' @ [$C a'', $C a', $C ConstInt32 x1a]"
            using outer_outer_cons outer_cons ConstInt32
            by fastforce
          thus ?thesis
            using is_const_list_vs_to_es_list[of "rev list''"]
                  progress_L0_left[OF reduce.intros(1)]
                  reduce_simple.intros(25,26)
                  assms outer_outer_cons outer_cons Cons ConstInt32 Select
            by (cases "int_eq x1a 0") auto
        qed auto
      qed auto
    qed auto
  next
    case (Block x51 x52)
    thus ?thesis
    proof (cases x51)
      case (Tf t1s t2s)
      thus ?thesis
        using Block assms
      proof (cases "length t1s \<le> length ves"; cases "split_n ves (length t1s)")
        case True
        case (Pair ves' ves'')
        hence "vs_to_es ves = vs_to_es ves'' @ vs_to_es ves'"
          using split_n_conv_app
          by fastforce
        moreover
        have "s = s'" "vs = vs'" "es' = vs_to_es ves'' @ [Label (length t2s) [] (vs_to_es ves' @ ($* x52))]"
          using Block assms Tf True Pair
          by auto
        moreover
        have "\<lparr>s;vs;(vs_to_es ves'')@(vs_to_es ves')@[$Block x51 x52]\<rparr> \<leadsto>_i \<lparr>s;vs;(vs_to_es ves'')@[Label (length t2s) [] (vs_to_es ves' @ ($* x52))]\<rparr>"
          using Tf reduce_simple.intros(27) split_n_length[OF Pair True] progress_L0_left[OF reduce.intros(1)]
                is_const_list_vs_to_es_list[of "rev ves'"] is_const_list_vs_to_es_list[of "rev ves''"]
          by fastforce
        ultimately
        show ?thesis
          using Block
          by auto
      qed auto
    qed
  next
    case (Loop x61 x62)
    thus ?thesis
    proof (cases x61)
      case (Tf t1s t2s)
      thus ?thesis
        using Loop assms
      proof (cases "length t1s \<le> length ves"; cases "split_n ves (length t1s)")
        case True
        case (Pair ves' ves'')
        hence "vs_to_es ves = vs_to_es ves'' @ vs_to_es ves'"
          using split_n_conv_app
          by fastforce
        moreover
        have "s = s'" "vs = vs'" "es' = vs_to_es ves'' @ [Label (length t1s) [$Loop x61 x62] (vs_to_es ves' @ ($* x62))]"
          using Loop assms Tf True Pair
          by auto
        moreover
        have "\<lparr>s;vs;(vs_to_es ves'')@(vs_to_es ves')@[$Loop x61 x62]\<rparr> \<leadsto>_i \<lparr>s;vs;(vs_to_es ves'')@[Label (length t1s) [$Loop x61 x62] (vs_to_es ves' @ ($* x62))]\<rparr>"
          using Tf reduce_simple.intros(28) split_n_length[OF Pair True] progress_L0_left[OF reduce.intros(1)]
                is_const_list_vs_to_es_list[of "rev ves'"] is_const_list_vs_to_es_list[of "rev ves''"]
          by fastforce
        ultimately
        show ?thesis
          using Loop
          by auto
      qed auto
    qed
  next
    case (If x71 x72 x73)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms If
      proof (cases a)
        case (ConstInt32 x1)
      hence "vs_to_es ves = vs_to_es list @ [$C ConstInt32 x1]"
        unfolding Cons
        by simp
      thus ?thesis
        using progress_L0_left[OF reduce.intros(1)]
              is_const_list_vs_to_es_list[of "rev list"]
              reduce_simple.intros(29,30)
              assms Cons If ConstInt32
        by (cases "int_eq x1 0") auto
      qed auto
    qed auto
  next
    case (Br x8)
    thus ?thesis
      using assms
      by auto
  next
    case (Br_if x9)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Br_if
      proof (cases a)
        case (ConstInt32 x1)
      hence "vs_to_es ves = vs_to_es list @ [$C ConstInt32 x1]"
        unfolding Cons
        by simp
      thus ?thesis
        using progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(34)]]
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(35)]]
              is_const_list_vs_to_es_list[of "rev list"]
              assms Cons Br_if ConstInt32
        by (cases "int_eq x1 0") auto
      qed auto
    qed auto
  next
    case (Br_table x10)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Br_table
      proof (cases a)
        case (ConstInt32 x1)
        thus ?thesis
          using progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(36)]]
                progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(37)]]
                is_const_list_vs_to_es_list[of "rev list"]
                assms Br_table Cons
          by (cases "(nat_of_int x1) < length x10") auto
      qed auto
    qed auto
  next
    case Return
    thus ?thesis
      using assms
      by simp
  next
    case (Call x12)
    thus ?thesis
      using assms progress_L0_left[OF reduce.intros(2)]
            is_const_list_vs_to_es_list[of "rev ves"]
      by auto
  next
    case (Call_indirect x13)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Call_indirect
      proof (cases a)
        case (ConstInt32 c)
        thus ?thesis
        proof (cases "stab s i (nat_of_int c)")
          case None
          thus ?thesis
            using assms Call_indirect Cons ConstInt32
                  progress_L0_left[OF reduce.intros(4)]
                  is_const_list_vs_to_es_list[of "rev list"]
            by auto
        next
          case (Some cl)
          thus ?thesis
          proof (cases "stypes s i x13 = cl_type cl")
            case True
            hence "\<lparr>s;vs;(vs_to_es list) @ [$C ConstInt32 c, $Call_indirect x13]\<rparr> \<leadsto>_ i \<lparr>s;vs;(vs_to_es list) @ [Callcl cl]\<rparr>"
              using progress_L0_left[OF reduce.intros(3)] True Some is_const_list_vs_to_es_list[of "rev list"]
              by fastforce
            thus ?thesis
              using assms Call_indirect Cons ConstInt32 Some True
              by auto
          next
            case False
            hence "\<lparr>s;vs;(vs_to_es list)@[$C ConstInt32 c, $Call_indirect x13]\<rparr> \<leadsto>_ i \<lparr>s;vs;(vs_to_es list)@[Trap]\<rparr>"
              using progress_L0_left[OF reduce.intros(4)] False Some is_const_list_vs_to_es_list[of "rev list"]
              by fastforce
            thus ?thesis
              using assms Call_indirect Cons ConstInt32 Some False
              by auto
          qed
        qed
      qed auto
    qed auto
  next
    case (Get_local j)
    thus ?thesis
      using assms
    proof (cases "j < length vs")
      case True
      then obtain vs1 v vs2 where "vs = vs1@[v]@vs2" "length vs1 = j"
        using id_take_nth_drop
        by fastforce
      thus ?thesis
        using assms Get_local True
              progress_L0_left[OF reduce.intros(8)]
              is_const_list_vs_to_es_list[of "rev ves"]
        by auto
    qed auto
  next
    case (Set_local j)
    thus ?thesis
      using assms      
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Set_local
      proof (cases "j < length vs")
        case True
        obtain vs1 v vs2 where vs_def:"vs = vs1@[v]@vs2" "length vs1 = j"
          using id_take_nth_drop True
          by fastforce
        thus ?thesis
          using assms Set_local True Cons
                progress_L0_left[OF reduce.intros(9)]
                is_const_list_vs_to_es_list[of "rev list"]
          by auto
      qed auto
    qed auto
  next
    case (Tee_local x16)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Tee_local
              progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(41)]]
                              is_const_list_vs_to_es_list[of "rev list"]
        by (auto simp add: is_const_def)
    qed auto
  next
    case (Get_global x17)
    thus ?thesis
      using assms
            progress_L0_left[OF reduce.intros(10)]
            is_const_list_vs_to_es_list[of "rev ves"]
      by (auto simp add: is_const_def)
  next
    case (Set_global x18)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Set_global
              progress_L0_left[OF reduce.intros(11)]
              is_const_list_vs_to_es_list[of "rev list"]
        by (auto simp add: is_const_def)
    qed auto
  next
    case (Load x191 x192 x193 x194)
    thus ?thesis
      using assms
    proof (cases x192; cases ves)
      case None
      case (Cons a list)
      thus ?thesis
        using Load assms None
      proof (cases a; cases "smem_ind s i")
        case (ConstInt32 x1)
        case (Some a)
        thus ?thesis
          using Load assms None Cons ConstInt32
              progress_L0_left[OF reduce.intros(12)]
              progress_L0_left[OF reduce.intros(13)]
              is_const_list_vs_to_es_list[of "rev list"]
          by (cases "load (s.mem s ! a) (nat_of_int x1) x194 (t_length x191)" )
             (auto simp add: is_const_def)
      qed auto
    next
      case outer_some:(Some tp_sx)
      case (Cons a list)
      thus ?thesis
        using Load assms outer_some
        proof (cases a; cases "smem_ind s i"; cases tp_sx)
          case (ConstInt32 x1)
          case (Pair tp sx)
          case (Some a)
          thus ?thesis
            using Load assms outer_some Cons ConstInt32 Pair
                  progress_L0_left[OF reduce.intros(14)]
                  progress_L0_left[OF reduce.intros(15)]
                  is_const_list_vs_to_es_list[of "rev list"]
            by (cases "load_packed sx (s.mem s ! a) (nat_of_int x1) x194 (tp_length tp) (t_length x191)")
               (auto simp add: is_const_def)
        qed auto
    qed auto
  next
    case (Store t tp a off)
    thus ?thesis
      using assms
    proof (cases ves)
      case outer_Cons:(Cons a list)
      thus ?thesis
        using Store assms
      proof (cases list)
        case (Cons a' list')
        thus ?thesis
          using Store outer_Cons assms
        proof (cases a')
          case (ConstInt32 x1)
          thus ?thesis
            using Store outer_Cons Cons assms
          proof (cases "(types_agree t a)"; cases "smem_ind s i")
            case True
            case outer_Some:(Some j)
            show ?thesis
            proof (cases tp)
              case None
              thus ?thesis
                using Store outer_Cons Cons assms True outer_Some ConstInt32
                      progress_L0_left[OF reduce.intros(16)]
                      progress_L0_left[OF reduce.intros(17)]
                      is_const_list_vs_to_es_list[of "rev list'"]
                by (cases "store (s.mem s ! j) (nat_of_int x1) off (bits a) (t_length t)")
                   auto
            next
              case (Some the_tp)
              thus ?thesis
                using Store outer_Cons Cons assms True outer_Some ConstInt32
                      progress_L0_left[OF reduce.intros(18)]
                      progress_L0_left[OF reduce.intros(19)]
                      is_const_list_vs_to_es_list[of "rev list'"]
                by (cases "store_packed (s.mem s ! j) (nat_of_int x1) off (bits a) (tp_length the_tp)")
                   auto
            qed
          qed (cases tp; auto)+
        qed (cases tp; auto)+
      qed (cases tp; auto)
    qed (cases tp; auto)
  next
    case Current_memory
    thus ?thesis
      using assms
    proof (cases "smem_ind s i")
      case (Some a)
      thus ?thesis
        using assms Current_memory 
              progress_L0_left[OF reduce.intros(20)]
              is_const_list_vs_to_es_list[of "rev ves"]
        by (auto simp add: is_const_def)
    qed auto
  next
    case Grow_memory
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Grow_memory
      proof (cases a; cases "smem_ind s i")
        case (ConstInt32 x1)
        case (Some j)
        thus ?thesis
          using assms Grow_memory Cons ConstInt32
                             progress_L0_left[OF reduce.intros(21)]
                             progress_L0_left[OF reduce.intros(22)]
              is_const_list_vs_to_es_list[of "rev list"] 
          by (cases "mem_grow_impl (s.mem s ! j) (nat_of_int x1)") (auto simp add: mem_grow_impl_correct is_const_def)
      qed auto
    qed auto
  next
    case (EConst x23)
    thus ?thesis
      using assms
      by auto
  next
    case (Unop_i x241 x242)
    thus ?thesis
      using run_step_basic_unop_testop_sound[OF assms]
      by fastforce
  next
    case (Unop_f x251 x252)
    thus ?thesis
      using run_step_basic_unop_testop_sound[OF assms]
      by fastforce
  next
    case (Binop_i x261 x262)
    thus ?thesis
      using run_step_basic_binop_relop_sound[OF assms]
      by fastforce
  next
    case (Binop_f x271 x272)
    thus ?thesis
      using run_step_basic_binop_relop_sound[OF assms]
      by fastforce
  next
    case (Testop x281 x282)
    thus ?thesis
      using run_step_basic_unop_testop_sound[OF assms]
      by fastforce
  next
    case (Relop_i x291 x292)
    thus ?thesis
      using run_step_basic_binop_relop_sound[OF assms]
      by fastforce
  next
    case (Relop_f x301 x302)
    thus ?thesis
      using run_step_basic_binop_relop_sound[OF assms]
      by fastforce
  next
    case (Cvtop t2 cvtop t1 sx)
    thus ?thesis
      using assms
    proof (cases ves)
      case (Cons a list)
      thus ?thesis
        using assms Cvtop
      proof (cases cvtop; cases "types_agree t1 a")
        case Convert
        case True
        thus ?thesis
          using Convert assms Cvtop Cons
                progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(19)]]
                progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(20)]]
                is_const_list_vs_to_es_list[of "rev list"]
          by (cases "(cvt t2 sx a)") auto
      next
        case Reinterpret
        case True
        thus ?thesis
          using Reinterpret assms Cvtop Cons
                progress_L0_left[OF reduce.intros(1)[OF reduce_simple.intros(21)]]
                is_const_list_vs_to_es_list[of "rev list"]
          by (cases sx) auto
      qed auto
    qed (cases cvtop; auto)
  qed
qed

theorem run_step_sound:
  assumes "run_step d i (s,vs,es) = (s', vs', RSNormal es')"
  shows "\<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
  using assms
proof -
  fix ves e
  have "(run_step d i (s,vs,es) = (s', vs', RSNormal es')) \<Longrightarrow>
           (\<lambda>i (s, vs, es). \<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>) i (s, vs, es)"
  and  "(run_one_step d i (s,vs,ves,e) = (s', vs', RSNormal es')) \<Longrightarrow>
          (\<lambda>i (s, vs, ves, e). \<lparr>s;vs;(vs_to_es ves)@[e]\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>) i (s, vs, ves, e)"
  proof (induction d i _ and d i _ arbitrary: s' vs' es' and s' vs' es' rule: run_step_run_one_step.induct)
    case (1 d i s vs es)
    obtain ves ses where ves_def:"split_vals_e es = (ves, ses)"
      by (metis surj_pair)
    thus ?case
    proof (cases ses)
      case Nil
      thus ?thesis
        using 1(2) ves_def
        by simp
    next
      case (Cons a list)
      thus ?thesis
      proof (cases "a = Trap")
        case True
        have c_ves:"const_list ($$* ves)"
          using is_const_list[of _ ves]
          by simp
        have "es' = [Trap] \<and> (list \<noteq> [] \<or> ves \<noteq> [])"
          using Cons 1(2) ves_def True
          by (cases "(list \<noteq> [] \<or> ves \<noteq> [])") auto
        thus ?thesis
          using Cons 1(2) ves_def split_vals_e_conv_app[OF ves_def] True progress_L0_trap[OF c_ves]
          by auto
      next
        case False
        obtain os ovs oes where ros_def:"run_one_step d i (s, vs, (rev ves), a) = (os, ovs, oes)"
          by (metis surj_pair)
        moreover
        then obtain roes where "oes = RSNormal roes"
          using 1(2) ves_def Cons False
          by (cases "oes") auto
        moreover
        hence "os = s'" "ovs = vs'" and es'_def:"es' = roes @ list"
          using 1(2) ves_def Cons ros_def False
          by (cases "roes = [Trap]", auto simp del: run_one_step.simps)+
        ultimately
        have ros_red:"\<lparr>s;vs;($$* ves) @ [a]\<rparr> \<leadsto>_ i \<lparr>s';vs';roes\<rparr>"
          using 1(1)[OF ves_def[symmetric] _ Cons] ros_def False
          by (simp del: run_one_step.simps)
        have "\<lparr>s;vs;($$* ves)@[a]@list\<rparr> \<leadsto>_ i \<lparr>s';vs';roes@list\<rparr>"
          using progress_L0[OF ros_red, of "[]" list]
          unfolding const_list_def
          by simp
        thus ?thesis
          using es'_def Cons split_vals_e_conv_app[OF ves_def]
          by simp
      qed
    qed
  next
    case (2 d i s vs ves e)
    show ?case
    proof (cases e)
      case (Basic x1)
      thus ?thesis
        using run_step_basic_sound 2(3)
        by simp
    next
      case Trap
      thus ?thesis
        using 2(3)
        by simp
    next
      case (Callcl cl)
      obtain t1s t2s where "cl_type cl = (t1s _> t2s)"
        using tf.exhaust[of _ thesis]
        by fastforce
      moreover
      obtain n where "length t1s = n"
        by blast
      moreover
      obtain m where "length t2s = m"
        by blast
      moreover
      note local_defs = calculation
      show ?thesis
      proof (cases "length ves \<ge> n")
        case outer_True:True
        obtain ves' ves'' where true_defs:"split_n ves n = (ves', ves'')"
          by (metis surj_pair)
        have ves'_length:"length (rev ves') = n"
          using split_n_length[OF true_defs outer_True] inj_basic_econst length_rev map_injective
          by blast
        show ?thesis
        proof (cases cl)
          case (Func_native i' tf fts fes)
          hence "s' = s" "vs' = vs" "es' = (vs_to_es ves'' @ [Local (length t2s) i' (rev ves' @ (n_zeros fts)) [$Block ([] _> t2s) fes]])"
            using 2(3) Callcl local_defs outer_True true_defs
            unfolding cl_type_def
            by auto
          moreover
          have "\<lparr>s;vs;(vs_to_es ves')@[Callcl cl]\<rparr> \<leadsto>_i \<lparr>s;vs;([Local (length t2s) i' (rev ves' @ (n_zeros fts)) [$Block ([] _> t2s) fes]])\<rparr>"
            using reduce.intros(5) local_defs(1,2) Func_native ves'_length
            unfolding cl_type_def
            by fastforce
          ultimately
          show ?thesis
            using Callcl progress_L0_left is_const_list[of _ "(rev ves'')"]
            unfolding split_n_conv_app[OF true_defs(1)]
            by auto
        next
          case (Func_host x21 x22)
          thus ?thesis
          proof (cases "host_apply_impl s (t1s _> t2s) x22 (rev ves')")
            case None
            hence "s = s'"
                  "vs = vs'"
                  "es' = vs_to_es ves'' @ [Trap] "
              using 2(3) Callcl local_defs outer_True true_defs Func_host
              unfolding cl_type_def
              by auto
            thus ?thesis
              using is_const_list[of _ "(rev ves'')"]
                    reduce.intros(7)[OF _ _ ves'_length local_defs(2)]
                    split_n_conv_app[OF true_defs]
                    progress_L0_left Callcl Func_host local_defs(1)
              unfolding cl_type_def
              by fastforce
          next
            case (Some a)
            show ?thesis
            proof (cases a)
            case (Pair rs rves)
              thus ?thesis
                using 2(3) Callcl local_defs outer_True true_defs Func_host Some
                unfolding cl_type_def
              proof (cases "list_all2 types_agree t2s rves")
                case True
                hence "rs = s'"
                      "vs = vs'"
                      "es' = vs_to_es ves'' @ ($$* rves) "
                  using 2(3) Callcl local_defs outer_True true_defs Func_host Pair Some      
                  unfolding cl_type_def
                  by auto
                thus ?thesis
                  using progress_L0_left reduce.intros(6)[OF _ _ ves'_length local_defs(2)] Pair
                        Callcl Func_host local_defs(1) True is_const_list[of _ "(rev ves'')"]
                        split_n_conv_app[OF true_defs] host_apply_impl_correct[OF Some]
                  unfolding cl_type_def
                  by fastforce
              qed auto
            qed
          qed
        qed
      next
        case False
        thus ?thesis
          using 2(3) Callcl local_defs
          unfolding cl_type_def
          by (cases cl) auto
      qed
    next
      case (Label ln les es)
      thus ?thesis
      proof (cases "es_is_trap es")
        case True
        thus ?thesis
          using 2(3) is_const_list_vs_to_es_list
                Label progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(32)]]
            by fastforce
      next
        case False
        note outer_outer_false = False
        show ?thesis
        proof (cases "(const_list es)")
          case True
          thus ?thesis
            using 2(3) outer_outer_false Label reduce.intros(1)[OF reduce_simple.intros(31)]
                  progress_L0[OF _ is_const_list_vs_to_es_list[of "rev ves"], where ?es_c="[]"]
            by fastforce
        next
          case False
          obtain s'' vs'' es'' where run_step_is:"run_step d i (s, vs, es) = (s'', vs'', es'')"
            by (metis surj_pair)
          show ?thesis
          proof (cases es'')
            case RSCrash
            thus ?thesis
              using outer_outer_false False run_step_is Label 2(3)
                by auto
          next
            case (RSBreak bn bvs)
            thus ?thesis
            proof (cases bn)
              case 0
              have run_step_is_break0:"run_step d i (s, vs, es) = (s'', vs'', RSBreak 0 bvs)"
                using run_step_is RSBreak 0
                by simp
              hence es'_def:"es' = ((vs_to_es ((take ln bvs)@ves))@les) \<and> s' = s'' \<and> vs' = vs'' \<and> ln \<le> length bvs"
                using outer_outer_false False run_step_is Label 2(3) RSBreak
                by (cases "ln \<le> length bvs") auto
              then obtain n lfilled es_c where local_eqs:"s=s'" "vs=vs'" "ln \<le> length bvs" "Lfilled_exact n lfilled ((vs_to_es bvs) @ [$Br n] @ es_c) es"
                using run_step_break_imp_lfilled[OF run_step_is_break0] RSBreak es'_def
                by fastforce
              then obtain lfilled' where lfilled_int:"Lfilled n lfilled' ((vs_to_es bvs) @ [$Br n]) es"
                using lfilled_collapse2[OF Lfilled_exact_imp_Lfilled]
                by fastforce
              obtain lfilled'' where "Lfilled n lfilled'' ((drop (length bvs - ln) (vs_to_es bvs)) @ [$Br n]) es"
                using lfilled_collapse1[OF lfilled_int] is_const_list_vs_to_es_list[of "rev bvs"] local_eqs(3)
                by fastforce
              hence "\<lparr>[Label ln les es]\<rparr> \<leadsto> \<lparr>(drop (length bvs - ln) (vs_to_es bvs))@les\<rparr>"
                using reduce_simple.intros(33) local_eqs(3) is_const_list_vs_to_es_list
                unfolding drop_map
                by fastforce
              hence 1:"\<lparr>s;vs;[Label ln les es]\<rparr> \<leadsto>_i \<lparr>s';vs';(drop (length bvs - ln) (vs_to_es bvs))@les\<rparr>"
                using reduce.intros(1) local_eqs(1,2)
                by fastforce
              have "\<lparr>s;vs;(vs_to_es ves)@[e]\<rparr> \<leadsto>_i \<lparr>s';vs';(vs_to_es ves)@(drop (length bvs - ln) (vs_to_es bvs))@les\<rparr>"
                using progress_L0[OF 1 is_const_list_vs_to_es_list[of "rev ves"], of "[]"] Label
                by fastforce
              thus ?thesis
                using es'_def
                unfolding drop_map rev_take[symmetric]
                by auto
            next
              case (Suc nat)
              thus ?thesis
                using outer_outer_false False run_step_is Label 2(3) RSBreak
                  by auto
            qed
          next
            case (RSReturn x3)
            thus ?thesis
              using outer_outer_false False run_step_is Label 2(3)
                by auto
          next
            case (RSNormal x4)
            hence "es' = (vs_to_es ves)@[Label ln les x4]" "s' = s''" "vs' = vs''"
              using outer_outer_false False run_step_is Label 2(3) run_step_is
              by auto   (* v* label_n {e* } Li end e* *)
            moreover
            have "Lfilled 1 (LRec (vs_to_es ves) ln les (LBase [] []) []) es ((vs_to_es ves)@[Label ln les es])"
              using Lfilled.intros(1)[of "[]" _ "[]" es]
                    Lfilled.intros(2)
                    is_const_list_vs_to_es_list[of "rev ves"]
              unfolding const_list_def
              by fastforce
            moreover
            have "Lfilled 1 (LRec (vs_to_es ves) ln les (LBase [] []) []) x4 ((vs_to_es ves)@[Label ln les x4])"
              using Lfilled.intros(1)[of "[]" _ "[]" x4]
                    Lfilled.intros(2)
                    is_const_list_vs_to_es_list[of "rev ves"]
              unfolding const_list_def
              by fastforce
            moreover
            have inner_reduce:"\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s'';vs'';x4\<rparr>"
              using 2(1)[OF Label outer_outer_false False] run_step_is RSNormal
              by auto
            ultimately
            show ?thesis
              using Label 2(3) outer_outer_false False run_step_is
                    reduce.intros(23)[OF inner_reduce]
              by fastforce
          qed
        qed
      qed
    next
      case (Local ln j vls es)
      thus ?thesis
      proof (cases "es_is_trap es")
        case True
        thus ?thesis
          using 2(3) is_const_list_vs_to_es_list
                Local progress_L0[OF reduce.intros(1)[OF reduce_simple.intros(39)]]
            by fastforce
      next
        case False
        note outer_outer_false = False
        show ?thesis
        proof (cases "(const_list es)")
          case True
          note outer_true = True
          thus ?thesis
          proof (cases "length es = ln")
            case True
            thus ?thesis
              using 2(3) Local outer_true outer_outer_false is_const_list_vs_to_es_list[of "rev ves"]
                  reduce.intros(1)[OF reduce_simple.intros(38)[OF outer_true True]]
                  progress_L0[where ?es_c="[]"]
                  by fastforce
          next
            case False
            thus ?thesis
              using 2(3) Local outer_outer_false outer_true is_const_list_vs_to_es_list[of "rev ves"]
              by auto
          qed
        next
          case False
          show ?thesis
          proof (cases d)
            case 0
            thus ?thesis
              using 2(3) Local outer_outer_false False is_const_list_vs_to_es_list[of "rev ves"]
              by auto
          next
            case (Suc d')
            obtain s'' vls' les' where run_step_is:"run_step d' j (s, vls, es) = (s'', vls', les')"
            by (metis surj_pair)
            show ?thesis
            proof (cases les')
              case RSCrash
              thus ?thesis
                using outer_outer_false False run_step_is Local 2(3) Suc
                  by auto
            next
              case (RSBreak x21 x22)
              thus ?thesis
                using outer_outer_false False run_step_is Local 2(3) Suc
                  by auto
            next
              case (RSReturn x3)
              hence es'_def:"es' = (vs_to_es ((take ln x3)@ves)) \<and> s' = s'' \<and> vs = vs' \<and> ln \<le> length x3"
                using outer_outer_false False run_step_is Local 2(3) Suc
                by (cases "ln \<le> length x3") auto
              then obtain n lfilled es_c where local_eqs:"s=s'" "vs=vs'" "ln \<le> length x3" "Lfilled_exact n lfilled ((vs_to_es x3) @ [$Return] @ es_c) es"
                using run_step_is run_step_return_imp_lfilled RSReturn
                by fastforce
              then obtain lfilled' where lfilled_int:"Lfilled n lfilled' ((vs_to_es x3) @ [$Return]) es"
                using lfilled_collapse2[OF Lfilled_exact_imp_Lfilled]
                by fastforce
              obtain lfilled'' where "Lfilled n lfilled'' ((drop (length x3 - ln) (vs_to_es x3)) @ [$Return]) es"
                using lfilled_collapse1[OF lfilled_int] is_const_list_vs_to_es_list[of "rev x3"] local_eqs(3)
                by fastforce
              hence "\<lparr>[Local ln j vls es]\<rparr> \<leadsto> \<lparr>(drop (length x3 - ln) (vs_to_es x3))\<rparr>"
                using reduce_simple.intros(40) local_eqs(3) is_const_list_vs_to_es_list
                unfolding drop_map
                by fastforce
              hence 1:"\<lparr>s;vs;[Local ln j vls es]\<rparr> \<leadsto>_i \<lparr>s';vs';(drop (length x3 - ln) (vs_to_es x3))\<rparr>"
                using reduce.intros(1) local_eqs(1,2)
                by fastforce
              have "\<lparr>s;vs;(vs_to_es ves)@[e]\<rparr> \<leadsto>_i \<lparr>s';vs';(vs_to_es ves)@(drop (length x3 - ln) (vs_to_es x3))\<rparr>"
                using progress_L0[OF 1 is_const_list_vs_to_es_list[of "rev ves"], of "[]"] Local
                by fastforce
              thus ?thesis
                using es'_def
                unfolding drop_map rev_take[symmetric]
                by auto
            next
              case (RSNormal x4)
              hence inner_reduce:"\<lparr>s;vls;es\<rparr> \<leadsto>_j \<lparr>s'';vls';x4\<rparr>"
                using 2(2)[OF Local outer_outer_false False] run_step_is Suc
                by auto
              thus ?thesis
                using Local 2(3) Local outer_outer_false False run_step_is Suc
                      reduce.intros(24)[OF inner_reduce] RSNormal
                      progress_L0_left is_const_list_vs_to_es_list[of "rev ves"]
                by (auto simp del: run_step.simps)
            qed
          qed
        qed
      qed
    qed
  qed
  thus ?thesis
    using assms
    by blast
qed

end